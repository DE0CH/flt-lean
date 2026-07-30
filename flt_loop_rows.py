"""Transition rules for the flt orchestrator loop -- the single source of
truth. Both the simulator and the real loop import this; neither
reimplements it, or the diagram and the machine drift apart.
"""

import random


def commit(s, msg):
    """Every state-changing tick is a commit in ~/.flt-loop.

    The state dir is a git repo, so `git log --oneline` IS the transition
    trace, and a repair agent can `git diff` its way back to the tick that
    broke things. Idle ticks are not committed -- a history of "nothing
    happened" would bury the history of what did.
    """
    s["git"].insert(0, msg)
    del s["git"][200:]


def unjustified(s):
    """Live jobs that have no business being alive in this state.

    Idling is only legitimate if we are waiting for something that is BOTH
    running and doing something the state actually calls for. `any job alive`
    is far too weak a test: it accepts a stale editor, a merger that claimed
    nothing, or a build of a snapshot we already have, and idles on them
    forever. Enumerating what a justified wait looks like means PANIC fires on
    the complement -- every configuration we did not explicitly expect.

    Returns a list of (name, reason), so a panic says WHICH job is wrong.
    """
    bad = []
    for n, j in s["jobs"].items():
        if not j["alive"]:
            # Every legitimate stopped record is consumed by a row above this
            # one. Surviving to idle means NO row claimed it -- so idle must
            # not paper over it just because some other job is healthy. This
            # is what makes "merger reported success but main never moved"
            # panic without needing a row that anticipates it.
            if j["started"]:
                bad.append((n, f"{j['kind']} stopped and no row consumed it"))
            continue
        k = j["kind"]
        if k == "merger":
            if s["main"] != s["rebaselined"]:
                bad.append((n, "merger alive but main already moved"))
            elif not s["inflight"]:
                bad.append((n, "merger alive with nothing claimed in .inflight"))
        elif k == "agent":
            w = j["worktree"]
            if w not in s["workers"]:
                bad.append((n, f"agent alive in unknown worktree {w}"))
            elif s["workers"].get(w) in ("awaiting_merge", "retired"):
                bad.append((n, f"agent alive in a {s['workers'][w]} worktree"))
        elif k != "medic":
            bad.append((n, f"unknown job kind {k}"))
    return bad


def idle_guard(s):
    live = [n for n, j in s["jobs"].items() if j["alive"]]
    if not live:
        # ...unless we are waiting on host capacity, which IS a legitimate
        # wait even with nothing running (a zero-capacity or fully drained
        # fleet). Without this it would read as an illegal state and panic.
        if any(unspawned(j) for j in s["jobs"].values()) and pick_host(s) is None:
            return (True, "")
        return (False, "nothing is alive, so nothing will change")
    bad = unjustified(s)
    if bad:
        return (False, "; ".join(f"{n}: {why}" for n, why in bad))
    return (True, "")


def anything_alive(s):
    return any(j["alive"] for j in s["jobs"].values())


def tok():
    return "%08x" % random.getrandbits(32)


def wstate(s, w):
    """Worker state: explicit if recorded, else derived from the job records."""
    st = s["workers"].get(w)
    if st in ("awaiting_merge", "retired"):
        return st
    return "claimed" if w in s["jobs"] else "free"


def jobs_of(s, kind):
    return {n: j for n, j in s["jobs"].items() if j["kind"] == kind}


def finished(j):
    return j["started"] and not j["alive"] and j["sentinel"] is not None


def died(j):
    return j["started"] and not j["alive"] and j["sentinel"] is None


# Installed by the runtime. Must launch the job DETACHED -- its own session,
# reparented away, never a child of the loop -- and return (host, pid,
# session). The loop must be killable at any instant without touching what it
# started, which is only true if it was never the parent.
SPAWN = None


def host_load(s):
    """Live jobs per host -- the distributor's view of the fleet."""
    load = {h: 0 for h in s.get("hosts", {})}
    for j in s["jobs"].values():
        if j["alive"] and j.get("host") in load:
            load[j["host"]] += 1
    return load


def pick_host(s):
    """Least-loaded host with room, ties broken by name so it is deterministic.

    Balancing on the RATIO rather than the count is what keeps a small machine
    from being handed the same absolute load as a large one; comparing raw
    counts silently overcommits the smallest host in the pool first.
    """
    load = host_load(s)
    room = [(load[h] / max(cap, 1), h)
            for h, cap in sorted(s.get("hosts", {}).items()) if load[h] < cap]
    return min(room)[1] if room else None


def unspawned(j):
    return (not j["started"]) and (not j["alive"])


def note(s, txt):
    s["log"].insert(0, txt)
    del s["log"][40:]


# --------------------------------------------------------------------------
# Each row: (id, label, guard, action). `guard(s)` -> (matched, reason).
# `reason` explains the FIRST failing conjunct, which is what makes a
# non-firing row informative rather than just dark.


def r1_guard(s):
    return (s["stop"], "no STOP file")


def r1_action(s):
    # Halts the LOOP and nothing else -- deliberately no killing, no draining,
    # no cleanup. Every job is spawned detached and is owned by its record
    # rather than by process lineage, so the loop is free to stop at any tick
    # and the fleet carries on. A stop that tore down its jobs would make
    # stopping a destructive act, and then it could never be used casually --
    # which is the only way it is any use at all.
    note(s, "1  STOP -> loop exits; running jobs are left alone")
    s["halted"] = True


def rmedic_done_guard(s):
    j = s["jobs"].get("medic")
    if not j:
        return (False, "no medic record")
    if not finished(j):
        return (False, "medic is not started ∧ ¬alive ∧ sentinel")
    return (True, "")


def rmedic_done_action(s):
    j = s["jobs"].pop("medic")
    v = j["sentinel"]
    verdict = "GO" if v.get("go") else "NO-GO"
    why = v.get("why", "")
    # Both verdicts email. A GO is not "nothing happened" -- it means the loop
    # silently reached an illegal state and something rewrote it, which is
    # exactly the thing a human should see even when the repair worked.
    s["email"].append(f"medic verdict {verdict}: {why}")
    commit(s, f"medic {verdict}: {why}")
    if v.get("go"):
        note(s, f"2  medic verdict GO: {why} -- emailed, resuming")
    else:
        s["stop"] = True
        note(s, f"2  medic verdict NO-GO: {why} -- emailed, STOP written")


def rmedic_wait_guard(s):
    return ("medic" in s["jobs"],
            "no medic in flight (normal operation)")


def rmedic_wait_action(s):
    j = s["jobs"]["medic"]
    if unspawned(j):
        j["started"] = True
        j["alive"] = True
        note(s, "3  SAFE MODE: medic spawned; all normal rows suspended")
    else:
        note(s, "3  SAFE MODE: waiting on medic")


def r2_guard(s):
    hits = [n for n, j in jobs_of(s, "agent").items() if finished(j)]
    return (bool(hits), "no agent is started ∧ ¬alive ∧ sentinel")


def r2_action(s):
    for n, j in list(jobs_of(s, "agent").items()):
        if not finished(j):
            continue
        for leaf in j["sentinel"].get("opened", []):
            s["queue2"].append(leaf)
        s["batch"].append(j["worktree"])
        s["workers"][j["worktree"]] = "awaiting_merge"   # set BEFORE deleting the record
        s["ancestor"][j["worktree"]] = False
        del s["jobs"][n]
        note(s, f"2  integrated {n}: batched, opened {j['sentinel'].get('opened', [])}"
                f" -> queue2; worker awaiting_merge")


def r3_guard(s):
    hits = [w for w in s["workers"]
            if wstate(s, w) == "awaiting_merge" and s["ancestor"].get(w)]
    return (bool(hits), "no awaiting_merge worker whose branch is an ancestor of main")


def r3_action(s):
    for w in list(s["workers"]):
        if wstate(s, w) == "awaiting_merge" and s["ancestor"].get(w):
            s["workers"][w] = None
            note(s, f"3  {w} branch landed -> free")


def r4_guard(s):
    hits = [n for n, j in jobs_of(s, "agent").items() if died(j)]
    return (bool(hits), "no agent is started ∧ ¬alive ∧ ¬sentinel")


def r4_action(s):
    for n, j in jobs_of(s, "agent").items():
        if died(j):
            j["alive"] = True
            j["retries"] += 1
            note(s, f"4  resumed {n} from transcript (resumes={j['retries']})")


def r5_guard(s):
    if any(unspawned(j) for j in s["jobs"].values()) and pick_host(s) is None:
        return (False, "every host is at capacity -- nowhere to spawn")
    hits = [n for n, j in s["jobs"].items() if unspawned(j)]
    return (bool(hits), "every job record already has a live process or a .started marker")


def r5_action(s):
    for n, j in s["jobs"].items():
        if unspawned(j):
            j["started"] = True
            j["alive"] = True
            # Identity is recorded BY the spawn, not by the record that
            # preceded it -- the record exists precisely while there is no
            # process yet. `session` is the Claude transcript id, which is
            # what row 6 resumes from: a died agent is continued from its
            # transcript, never restarted from nothing, so losing this field
            # would silently convert every resume into a redo.
            j["host"] = j.get("host") or pick_host(s)
            host, pid, sess = SPAWN(s, n, j)
            j["host"], j["pid"], j["session"] = host, pid, sess
            # Name what was spawned: row 7 is the ONE spawner for every kind,
            # so a bare "SPAWN" in the transition log is unreadable -- two
            # consecutive firings look like a double-spawn when they are a
            # lakebuild and an editor.
            note(s, f"5  spawned {j['kind']} '{n}' (token {j['token']})")
            s["spawned"] = f"{j['kind']} '{n}'"


def r6_guard(s):
    # DIED, i.e. no sentinel. A merger that exits WITH a sentinel but without
    # moving main is not handled here and deliberately has no row of its own:
    # a merge worker's whole purpose is to move main, so reporting success
    # without doing it is an illegal state. It reaches PANIC by falling out of
    # the idle guard, which is where unanticipated configurations belong.
    m = s["jobs"].get("merger")
    if not m:
        return (False, "no merger record")
    if not died(m):
        return (False, "merger is not started ∧ ¬alive ∧ ¬sentinel")
    if s["main"] != s["rebaselined"]:
        return (False, "main moved -- it released, so REBASELINE handles it")
    return (True, "")


def r6_action(s):
    if s["inflight"]:
        s["batch"] = s["inflight"] + s["batch"]
        s["inflight"] = None
    del s["jobs"]["merger"]
    note(s, "6  merger died without releasing: .inflight restored to batch, record dropped")


def r7_guard(s):
    """The merger delivered. Adopt its results.

    The merger is now the ONE producer of everything derived from main: it
    merges the batch, moves main, builds the clean .lake, and rewrites the
    queue (remainder of queue1 ahead of queue2, audited against the main it
    just produced). Folding those into the agent that already has the tree
    checked out removes a build job, an editor job, and the five rows that
    sequenced them -- and removes the window where main has moved but the
    snapshot and the audit still describe the previous release.

    So this guard demands the FULL delivery. A merger that moved main without
    also leaving a current snapshot and a current audit has broken its
    contract; the guard fails, its stopped record is consumed by nobody, and
    idle rejects it into PANIC. That is the intended path -- a partial
    delivery is not a case to handle, it is a violation to report.
    """
    if s["main"] == s["rebaselined"]:
        return (False, "main == rebaselined -- nothing new to adopt")
    m = s["jobs"].get("merger")
    if m and m["alive"]:
        return (False, "a merger is still alive")
    if not (s["snapshot"] and s["snapshot"]["sha"] == s["main"]):
        return (False, f"merger moved main to {s['main']} but left no snapshot for it")
    if s["queue1"]["audited"] != s["main"]:
        return (False, f"merger moved main to {s['main']} but left queue1 unaudited")
    return (True, "")


def r7_action(s):
    s["rebaselined"] = s["main"]
    s["jobs"].pop("merger", None)
    note(s, f"7  ADOPTED release {s['main']}: snapshot current, "
            f"queue1 AUDITED with {len(s['queue1']['tasks'])} task(s)")


def r11_guard(s):
    if "merger" in s["jobs"]:
        return (False, "a merger record already exists")
    stale = (not s["snapshot"] or s["snapshot"]["sha"] != s["main"]
             or s["queue1"]["audited"] != s["main"])
    if not s["batch"] and not stale:
        return (False, "nothing to merge and nothing derived from main is stale")
    return (True, "")


def r11_action(s):
    # An empty batch is allowed: main can move without us (a tooling commit),
    # and then the snapshot and the audit describe a main that no longer
    # exists. The merger is what refreshes them, so it must be startable with
    # nothing to merge -- otherwise that state is a silent deadlock in which
    # dispatch is blocked forever on a snapshot nobody will ever rebuild.
    s["inflight"] = list(s["batch"])
    s["batch"] = []
    s["jobs"]["merger"] = {
        "kind": "merger", "worktree": "flt-staging", "payload": s["inflight"],
        "token": tok(), "retries": 0, "started": False, "alive": False,
        "sentinel": None,
    }
    note(s, "11 merger record created; claimed %d branch(es)%s"
            % (len(s["inflight"]),
               "" if s["inflight"] else " (refresh only -- nothing to merge)"))


def r15_guard(s):
    if s["queue1"]["audited"] != s["main"]:
        return (False, "queue1 is not AUDITED at main")
    if not s["queue1"]["tasks"]:
        return (False, "queue1 is empty")
    if not s["snapshot"]:
        return (False, "no snapshot for agents to copy .lake from")
    if s["snapshot"]["sha"] != s["main"]:
        # Existence is not enough. After a rebaseline the PREVIOUS release's
        # snapshot is still on disk while the new one builds, and dispatching
        # against it seeds every agent with a .lake for the wrong main -- the
        # inconsistent-olean failure this project already knows well, where
        # loading does not typecheck and the mismatch surfaces later as a
        # bogus kernel error in an unrelated file. Row 13 already required
        # snapshot == main before starting a merger; dispatch was the row that
        # only checked non-None.
        return (False, f"snapshot is {s['snapshot']['sha']}, main is {s['main']}")
    free = [w for w in s["workers"]
            if wstate(s, w) == "free" and s["healthy"].get(w)]
    if not free:
        return (False, "no free ∧ healthy worker")
    return (True, "")


def r15_action(s):
    free = sorted(w for w in s["workers"]
                  if wstate(s, w) == "free" and s["healthy"].get(w))
    n = 0
    for w in free:
        if not s["queue1"]["tasks"]:
            break
        task = s["queue1"]["tasks"].pop(0)
        s["jobs"][w] = {
            "kind": "agent", "worktree": w, "payload": task, "token": tok(),
            "retries": 0, "started": False, "alive": False, "sentinel": None,
        }
        n += 1
    note(s, f"15 dispatched {n} agent record(s); spawn happens in row 5")


def panic(s, reason="no row matched"):
    """The state cannot be explained. Commit it, report it, hand it to a medic.

    Three things, in this order. The commit first, because everything after it
    is a side effect and the record of WHAT WENT WRONG must exist before any
    attempt to change it.

    Reached two ways. INFERRED: no row matched, so the loop cannot account for
    what it is looking at. REPORTED: a job came back saying its preconditions
    were broken. Both mean the same thing -- the machinery is not in a state
    the loop knows how to drive -- and both take the same path.
    """
    commit(s, "PANIC: " + reason)
    s["email"].append("PANIC: " + reason)
    s["jobs"]["medic"] = {
        "kind": "medic", "worktree": "flt-loop-state", "payload": "diagnose",
        "token": tok(), "retries": 0, "started": False, "alive": False,
        "sentinel": None,
    }
    note(s, "PANIC: committed, emailed, medic record created -> SAFE MODE")


def reported_panic_guard(s):
    """A job came back saying the LOOP's preconditions are broken.

    Every job is asked to return one binary field. It is emphatically NOT a
    verdict on the work: a proof that does not go through, a leaf that turns
    out to be false, a merge that has to decline a branch -- those are ordinary
    outcomes and the loop wants them reported as results, not as alarms. It
    means the job could not operate at all: the .lake it was told to copy is
    not there, the worktree is on a branch nobody claimed, the snapshot
    directory is torn.

    That distinction is the whole value of the field. The loop cannot tell the
    two apart from outside -- a failed proof and a missing .lake both look like
    "agent finished, leaf still open" -- and treating every failure as a panic
    would make panic meaningless within an hour, since failed proofs are the
    normal case here.

    Checked ABOVE the rows that consume sentinels, so a panicking job is never
    quietly integrated first.
    """
    hits = [(n, j) for n, j in s["jobs"].items()
            if finished(j) and j["sentinel"].get("panic")]
    if not hits:
        return (False, "no job reported panic")
    n, j = hits[0]
    return (True, "%s: %s" % (n, j["sentinel"].get("why", "no reason given")))


def reported_panic_action(s):
    n, j = next((n, j) for n, j in s["jobs"].items()
                if finished(j) and j["sentinel"].get("panic"))
    why = j["sentinel"].get("why", "no reason given")
    # The record is kept, not consumed: the medic needs to see what came back.
    panic(s, "%s (%s) reported PANIC: %s" % (n, j["kind"], why))


ROWS = [
    (1, "STOP exists", r1_guard, r1_action),
    (2, "medic finished -> apply GO / NO-GO verdict", rmedic_done_guard, rmedic_done_action),
    (3, "medic in flight -> SAFE MODE (all rows below suspended)", rmedic_wait_guard, rmedic_wait_action),
    (4, "a job REPORTED panic -> email + medic", reported_panic_guard, reported_panic_action),
    (5, "agent finished -> integrate, awaiting_merge", r2_guard, r2_action),
    (6, "awaiting_merge ∧ ancestor(main) -> free", r3_guard, r3_action),
    (7, "agent died -> resume from transcript", r4_guard, r4_action),
    (8, "record ∧ ¬started ∧ no process -> SPAWN", r5_guard, r5_action),
    (9, "merger died without releasing -> restore .inflight", r6_guard, r6_action),
    (10, "merger delivered main+snapshot+audit -> ADOPT", r7_guard, r7_action),
    (11, "batch ∨ derived-from-main is stale -> create merger record", r11_guard, r11_action),
    (12, "dispatch: pop queue1 -> agent records", r15_guard, r15_action),
    (13, "idle -- every live job is justified", idle_guard, lambda s: None),
    (14, "ILLEGAL STATE -> email + medic", lambda s: (True, ""), panic),
]


def evaluate(s):
    """Evaluate every row; return the rows plus which one fires."""
    out, firing = [], None
    for rid, label, guard, _ in ROWS:
        ok, why = guard(s)
        if ok and firing is None:
            firing = rid
        out.append({"id": rid, "label": label, "matched": ok, "why": why,
                    "fires": ok and firing == rid})
    return out, firing


def step(s):
    rows, firing = evaluate(s)
    for rid, label, _, action in ROWS:
        if rid == firing:
            action(s)
            # Idle commits nothing: a history of "nothing happened" would bury
            # the history of what did. PANIC commits itself, first.
            # idle/done/panic never emit a generic commit: panic writes its
            # own first, and the medic verdict rows write theirs.
            if rid not in (2, 18, 19):
                commit(s, f"row {rid}: {label}")
            break
    return firing


# --------------------------------------------------------------------------
# server
# --------------------------------------------------------------------------

def mutate(s, job, what):
    """Inject the things the loop cannot cause itself -- the outside world."""
    if what == "release":
        n = "r%d" % (int(s["main"][1:]) + 1)
        s["main"] = n
        # Releasing is WHAT MAKES those branches ancestors of main -- so read
        # .inflight, the merger's own record of what it claimed, and mark
        # exactly those. Leaving `ancestor` a hand-flipped knob made the one
        # causal link the loop depends on invisible: row 5 frees a worker only
        # when its branch has landed, and nothing was ever landing it, so
        # every awaiting_merge worker sat there across releases that had in
        # fact merged it. Branches NOT in .inflight stay awaiting_merge,
        # which is correct -- this merger did not carry them.
        merged = [w for w in (s["inflight"] or []) if w in s["ancestor"]]
        for w in merged:
            s["ancestor"][w] = True
        m = s["jobs"].get("merger")
        if m:
            m["alive"] = False
            m["sentinel"] = {"released": n, "merged": merged}
        s["inflight"] = None
        note(s, f"~  merger released {n}; main moved; landed {merged or 'nothing'}")
    elif what == "merger_noop":
        # ILLEGAL by construction: a merge worker exists to move main, so
        # reporting success without moving it is not an outcome the table
        # anticipates. Kept as an injection precisely so the fall-through to
        # PANIC can be exercised.
        m = s["jobs"].get("merger")
        if m:
            m["alive"] = False
            m["sentinel"] = {"ok": True}
            note(s, "~  merger reported success but did NOT move main (illegal)")
    elif what == "merger_die":
        m = s["jobs"].get("merger")
        if m:
            m["alive"] = False
            note(s, "~  merger process died without a sentinel")
    elif what == "build_fail":
        b = s["jobs"].get("lakebuild")
        if b:
            b["alive"] = False
            b["sentinel"] = {"rc": 1, "sha": b["payload"]}
            note(s, "~  lake build exited nonzero")
    elif what == "leaf":
        for n, j in s["jobs"].items():
            if j["kind"] == "agent" and j["alive"]:
                j["alive"] = False
                j["sentinel"] = {"opened": [j["payload"] + "·a", j["payload"] + "·b"]}
                note(s, f"~  {n} finished, opening {j['payload']}'")
                break
    elif what == "corrupt":
        s["inflight"] = ["flt-lean-9"]
        s["jobs"].pop("merger", None)
        note(s, "~  .inflight orphaned (merger record vanished)")
    elif what == "job_panic":
        for n, j in s["jobs"].items():
            if j["alive"] and j["kind"] in ("agent", "merger"):
                j["alive"] = False
                j["sentinel"] = {"panic": True,
                                 "why": "no .lake at the snapshot path; cannot build"}
                note(s, f"~  {n} returned PANIC (environment, not mathematics)")
                break
    elif what == "medic_go":
        j = s["jobs"].get("medic")
        if j:
            j["alive"] = False
            j["sentinel"] = {"go": True, "why": "state repaired from git history"}
    elif what == "medic_nogo":
        j = s["jobs"].get("medic")
        if j:
            j["alive"] = False
            j["sentinel"] = {"go": False, "why": "unrecoverable: queue2 contents lost"}
    elif what == "stop":
        s["stop"] = True
        note(s, "~  STOP file written")
    elif job and what == "finish":
        j = s["jobs"][job]
        # Finishing must do what that job actually DOES in the world, or the
        # simulator teaches the wrong lesson. A merge worker's product is a
        # moved main -- that is an external fact it performs itself, not an
        # effect the loop applies on consuming a sentinel (which is how the
        # editor's audit and the lakebuild's snapshot work, in their rows).
        if j["kind"] == "merger":
            return mutate(s, None, "release")
        j["alive"] = False
        if j["kind"] == "lakebuild":
            j["sentinel"] = {"rc": 0, "sha": j["payload"]}
        elif j["kind"] == "agent":
            # Real workers close their target and cut it into smaller leaves.
            # Two successors is the honest default and it is what makes the
            # queue dynamics realistic instead of monotonically draining.
            j["sentinel"] = {"opened": [j["payload"] + "·a", j["payload"] + "·b"]}
        else:
            j["sentinel"] = {"ok": True}
        note(s, f"~  {job} wrote its sentinel")
    elif job and what == "die":
        s["jobs"][job]["alive"] = False
        note(s, f"~  {job} died with no sentinel")

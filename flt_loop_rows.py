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
        elif k == "lakebuild":
            if s["snapshot"] and s["snapshot"]["sha"] == s["main"]:
                bad.append((n, "lakebuild alive but the snapshot is already current"))
        elif k == "editor":
            if s["queue1"]["audited"] == s["main"]:
                bad.append((n, "editor alive but queue1 is already audited at main"))
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
    note(s, "1  STOP -> exit")
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
    hits = [n for n, j in s["jobs"].items() if unspawned(j)]
    return (bool(hits), "every job record already has a live process or a .started marker")


def r5_action(s):
    for n, j in s["jobs"].items():
        if unspawned(j):
            j["started"] = True
            j["alive"] = True
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
    # Rebaseline is not "a release happened" -- it is "the queue we dispatch
    # from is no longer the right one". Exhaustion qualifies: without this,
    # queue1 empty + queue2 non-empty + batch empty is a permanent deadlock,
    # which is exactly the state reached when agents finish without commits.
    exhausted = (not s["queue1"]["tasks"]) and bool(s["queue2"])
    if s["main"] == s["rebaselined"] and not exhausted:
        return (False, "main == rebaselined and queue1 still has work")
    m = s["jobs"].get("merger")
    if m and m["alive"]:
        return (False, "a merger is still alive")
    return (True, "")


def r7_action(s):
    s["queue2"] = s["queue1"]["tasks"] + s["queue2"]
    s["queue1"] = {"audited": None, "tasks": s["queue2"]}
    s["queue2"] = []
    s["rebaselined"] = s["main"]
    s["jobs"].pop("merger", None)
    if s["jobs"].pop("editor", None):
        note(s, "7  ... stale editor stopped (its audit predates this release)")
    note(s, f"7  REBASELINE at {s['main']}: queues swapped, queue1 AUDITED:none")


def r8_guard(s):
    if s["snapshot"] and s["snapshot"]["sha"] == s["main"]:
        return (False, "snapshot already reflects main")
    if "lakebuild" in s["jobs"]:
        return (False, "a lakebuild record already exists")
    return (True, "")


def r8_action(s):
    s["jobs"]["lakebuild"] = {
        "kind": "lakebuild", "worktree": "flt-main-build", "payload": s["main"],
        "token": tok(), "retries": 0, "started": False, "alive": False,
        "sentinel": None,
    }
    note(s, f"8  lakebuild record created for {s['main']}")


def r9_guard(s):
    b = s["jobs"].get("lakebuild")
    if not b:
        return (False, "no lakebuild record")
    if not finished(b):
        return (False, "lakebuild is not started ∧ ¬alive ∧ sentinel")
    return (True, "")


def r9_action(s):
    b = s["jobs"]["lakebuild"]
    ok = b["sentinel"].get("rc") == 0 and b["sentinel"].get("sha") == b["payload"]
    if ok:
        s["snapshot"] = {"sha": b["payload"]}
        note(s, f"9  snapshot verified and published at {b['payload']}")
    else:
        note(s, f"9  snapshot FAILED verification (rc={b['sentinel'].get('rc')}) -- retrying")
    del s["jobs"]["lakebuild"]


def r10_guard(s):
    b = s["jobs"].get("lakebuild")
    if not b:
        return (False, "no lakebuild record")
    if not died(b):
        return (False, "lakebuild is not started ∧ ¬alive ∧ ¬sentinel")
    return (True, "")


def r10_action(s):
    del s["jobs"]["lakebuild"]
    note(s, "10 lakebuild died -- record dropped, row 8 will restart it")


def r11_guard(s):
    if not (s["snapshot"] and s["snapshot"]["sha"] == s["main"]):
        return (False, "snapshot does not reflect main yet")
    if "merger" in s["jobs"]:
        return (False, "a merger record already exists")
    if not s["batch"]:
        return (False, "batch is empty -- nothing to merge")
    return (True, "")


def r11_action(s):
    s["inflight"] = list(s["batch"])
    s["batch"] = []
    s["jobs"]["merger"] = {
        "kind": "merger", "worktree": "flt-staging", "payload": s["inflight"],
        "token": tok(), "retries": 0, "started": False, "alive": False,
        "sentinel": None,
    }
    note(s, f"11 merger record created; claimed {len(s['inflight'])} branch(es)")


def r12_guard(s):
    if s["queue1"]["audited"] == s["main"]:
        return (False, "queue1 is already AUDITED at main")
    if "editor" in s["jobs"]:
        return (False, "an editor record already exists")
    return (True, "")


def r12_action(s):
    s["jobs"]["editor"] = {
        "kind": "editor", "worktree": "flt-lean", "payload": "queue1",
        "token": tok(), "retries": 0, "started": False, "alive": False,
        "sentinel": None,
    }
    note(s, "12 queue editor record created")


def r13_guard(s):
    e = s["jobs"].get("editor")
    if not e:
        return (False, "no editor record")
    if not finished(e):
        return (False, "editor is not started ∧ ¬alive ∧ sentinel")
    return (True, "")


def r13_action(s):
    s["queue1"]["audited"] = s["main"]
    del s["jobs"]["editor"]
    note(s, f"13 editor finished; queue1 AUDITED:{s['main']}")


def r14_guard(s):
    e = s["jobs"].get("editor")
    if not e:
        return (False, "no editor record")
    if not died(e):
        return (False, "editor is not started ∧ ¬alive ∧ ¬sentinel")
    return (True, "")


def r14_action(s):
    e = s["jobs"]["editor"]
    e["alive"] = True
    e["retries"] += 1
    note(s, f"14 editor resumed (retries={e['retries']})")


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


ROWS = [
    (1, "STOP exists", r1_guard, r1_action),
    (2, "medic finished -> apply GO / NO-GO verdict",
     rmedic_done_guard, rmedic_done_action),
    (3, "medic in flight -> SAFE MODE (all rows below suspended)",
     rmedic_wait_guard, rmedic_wait_action),
    (4, "agent finished -> integrate, awaiting_merge", r2_guard, r2_action),
    (5, "awaiting_merge ∧ ancestor(main) -> free", r3_guard, r3_action),
    (6, "agent died -> resume from transcript", r4_guard, r4_action),
    (7, "record ∧ ¬started ∧ no process -> SPAWN", r5_guard, r5_action),
    (8, "merger died without releasing -> restore .inflight", r6_guard, r6_action),
    (9, "main ≠ rebaselined ∨ queue1 exhausted -> REBASELINE", r7_guard, r7_action),
    (10, "snapshot ≠ main -> create lakebuild record", r8_guard, r8_action),
    (11, "lakebuild finished -> verify + publish snapshot", r9_guard, r9_action),
    (12, "lakebuild died -> drop record", r10_guard, r10_action),
    (13, "snapshot == main ∧ batch -> create merger record", r11_guard, r11_action),
    (14, "queue1.AUDITED ≠ main -> create editor record", r12_guard, r12_action),
    (15, "editor finished -> queue1 AUDITED := main", r13_guard, r13_action),
    (16, "editor died -> resume", r14_guard, r14_action),
    (17, "dispatch: pop queue1 -> agent records", r15_guard, r15_action),
    (18, "idle -- every live job is justified",
     idle_guard, lambda s: None),
    # There is deliberately NO "done" row. Reaching "no jobs, no queues, no
    # batch" in a tree with hundreds of open sorries means the state was eaten,
    # not that the work finished -- and treating it as a clean exit would
    # silently swallow exactly the corruption the catch-all exists to catch.
    # Even genuine completion is better served by panicking: it emails a human,
    # which is what you want for an event that momentous.
    (19, "PANIC -- illegal state, no row matches",
     lambda s: (True, ""), lambda s: panic(s)),
]


def panic(s):
    """No row matched and nothing is running: the state cannot be explained.

    Three things, in this order. The commit first, because everything after it
    is a side effect and the record of WHAT WENT WRONG must exist before any
    attempt to change it.
    """
    commit(s, "PANIC: no row matched")
    s["email"].append("PANIC: loop reached a state no transition matches")
    s["jobs"]["medic"] = {
        "kind": "medic", "worktree": "flt-loop-state", "payload": "diagnose",
        "token": tok(), "retries": 0, "started": False, "alive": False,
        "sentinel": None,
    }
    note(s, "18 PANIC: committed, emailed, medic record created -> SAFE MODE")


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
        m = s["jobs"].get("merger")
        if m:
            m["alive"] = False
            m["sentinel"] = {"released": n}
        s["inflight"] = None
        note(s, f"~  merger released {n}; main moved")
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

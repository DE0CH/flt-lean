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
            # A LIVE merger is justified for as long as it runs. Two earlier
            # tests lived here and both were wrong, in the same way -- they
            # inferred what a merger had done from a fact that is not about it.
            #
            #   `main != rebaselined` read ANY movement of main as "this merger
            #   already released". But main moves without a release: a tooling
            #   commit is explicitly sanctioned (CLAUDE.md), and the loop's own
            #   source commit is one. After the first such commit the condition
            #   is permanently true, so every merger created afterwards to
            #   refresh the stale snapshot was condemned on its first tick --
            #   which is exactly the panic that produced this comment. It also
            #   cannot be repaired by tightening it to "delivered everything and
            #   still alive": ALIVE_CACHE means that is naturally true for up to
            #   20 seconds at the end of EVERY successful release. Whether this
            #   merger released is now recorded where it belongs, in the record
            #   (`base`), and rows 9/10 consume it when it stops.
            #
            #   `not s["inflight"]` condemned the refresh-only merger that
            #   r11_action deliberately creates with an empty claim -- `[]` is
            #   falsy. None and [] are DIFFERENT facts here and load()/save()
            #   keep them apart on purpose: None is "no merger claimed
            #   anything", [] is "claimed nothing, refresh only".
            if s["inflight"] is None:
                bad.append((n, "merger alive but .inflight records no claim"))
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
    if s.get("quota_block"):
        return (True, "")      # idling on quota is a legitimate wait
    live = [n for n, j in s["jobs"].items() if j["alive"]]
    if not live:
        # ...unless we are waiting on host capacity, which IS a legitimate
        # wait even with nothing running (a zero-capacity or fully drained
        # fleet). Without this it would read as an illegal state and panic.
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


def host_of(s, worktree):
    return s.get("worker_host", {}).get(worktree)


# Deyao, 2026-07-30: 150 concurrent workers, a RAM veto, and placement by CPU
# utilisation. These are three DIFFERENT limits and each catches something the
# others cannot: the cap bounds total concurrency, the veto refuses a machine
# that would swap, and utilisation decides which of the acceptable machines
# gets the next job.
MAX_WORKERS = 150
SPAWNS_PER_TICK = 5      # a herd of 47 at once is what this prevents
MIN_AVAIL_GB = 120.0     # below this a host is vetoed outright
MAX_UTIL = 0.90          # 1.0 == loadavg equal to core count


def host_load(s):
    """Busy worktrees per host -- the distributor's view of the fleet.

    Counted by WORKTREE, not by job, because a worktree is what a job occupies
    and a worktree cannot move: its .lake is machine-local, so the host is a
    property of the worktree rather than a choice made when a job starts. The
    earlier version chose a host at spawn time, which is only meaningful if a
    job could run anywhere -- it cannot, and the real fleet has recorded a
    fixed worktree->host map all along.
    """
    load = {h: 0 for h in s.get("hosts", {})}
    for w in s["workers"]:
        h = host_of(s, w)
        if h in load and wstate(s, w) == "claimed":
            load[h] += 1
    return load


def busy_count(s):
    return sum(1 for w in s["workers"] if wstate(s, w) == "claimed")


def pick_worker(s):
    """A free, healthy worktree on an acceptable host. None if none qualifies.

    Placement is by MEASURED CPU utilisation, not by a static capacity, because
    these are shared machines: other people's jobs run on them, and a fixed
    per-host slot count cannot see that. One host was carrying a load of 420
    from another user's work while holding none of ours -- a static cap would
    have kept feeding it.

    The RAM veto is separate and absolute. A host low on memory is not "less
    preferred", it is unusable: Lean elaboration that starts swapping does not
    slow down gracefully, it takes the machine down with it.
    """
    if busy_count(s) >= MAX_WORKERS:
        return None
    load = host_load(s)
    cands = []
    for w in sorted(s["workers"]):
        if wstate(s, w) != "free" or not s["healthy"].get(w):
            continue
        h = host_of(s, w)
        m = s.get("hosts", {}).get(h)
        if not m:
            continue
        if m.get("avail_gb", 0) < MIN_AVAIL_GB:
            continue
        # Our own queued jobs are not visible in a loadavg sampled seconds ago,
        # so count what we have already placed this tick against the host.
        proj = m.get("util", 1.0) + load.get(h, 0) / max(m.get("ncpu", 1), 1)
        if proj > MAX_UTIL:
            continue
        cands.append((round(proj, 3), h, w))
    return min(cands)[2] if cands else None


# Kinds that occupy a worktree and build Lean, and so are subject to the
# distributor. The medic is NOT one: it edits state files on the loop's own
# host and needs no build slot.
#
# Exempting it is not a convenience. A panic happens when things are wedged,
# which is exactly when the fleet is most likely to be full -- and SAFE MODE
# suspends every row below the medic, so no agent will ever finish and free a
# slot. Subjecting the medic to capacity is therefore a guaranteed permanent
# deadlock: the one job that can unstick the loop queues behind the jobs that
# cannot proceed until it does.
# The medic runs here, always, whatever the fleet is doing.
MEDIC_HOST = "mystique"


def spawnable(s, j):
    if not unspawned(j):
        return False
    # The API is refusing work. Spawning now burns an attempt and achieves
    # nothing, so the loop waits instead -- the wait is the correct action,
    # not a degraded one.
    if s.get("quota_block"):
        return False
    # SAFE MODE, enforced at the spawner rather than by row order. SPAWN has
    # to sit ABOVE the SAFE MODE row -- otherwise the row that engages safe
    # mode blocks the only thing that can start the medic -- and this is what
    # stops that from also letting ordinary work start during a panic.
    return not ("medic" in s["jobs"] and j["kind"] != "medic")


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
        # GO means the state on disk is normal again, so the panic reports
        # that produced this medic are part of what it repaired -- they are
        # cleared, and their jobs go back to being ordinary completions for
        # the normal rows to consume.
        #
        # Leaving them set would make GO meaningless: the reported-panic row
        # would match the same sentinel on the very next tick, spawn another
        # medic, and the loop would alternate between panicking and being told
        # it is fine, forever, without a single operational row running in
        # between. A verdict the machine cannot act on is not a verdict.
        cleared = [n for n, k in s["jobs"].items()
                   if k["sentinel"] and k["sentinel"].get("panic")]
        for n in cleared:
            s["jobs"][n]["sentinel"]["panic"] = False
        note(s, f"2  medic verdict GO: {why} -- emailed, resuming"
                + (f" (cleared panic on {', '.join(cleared)})" if cleared else ""))
    else:
        s["stop"] = True
        note(s, f"2  medic verdict NO-GO: {why} -- emailed, STOP written")


def rmedic_dead_guard(s):
    """The medic died without a verdict. Nothing below can rescue this.

    Every other job's death has a recovery: an agent is respawned as a takeover,
    a merger's claim is restored to the batch. The medic has none, because the
    medic IS the recovery -- and SAFE MODE suspends every row beneath it. So a
    medic that stops without writing a sentinel wedges the loop permanently and
    silently, which is the worst outcome the table can produce.

    Escalate to the human instead of respawning: the medic is the loop's own
    self-repair, and self-repair that died is exactly the point at which
    guessing again is worse than stopping and saying so. Nothing is torn down
    -- STOP halts the loop only; the fleet keeps running (see r1_action).
    """
    j = s["jobs"].get("medic")
    if not j:
        return (False, "no medic record")
    if not died(j):
        return (False, "medic is not started ∧ ¬alive ∧ ¬sentinel")
    return (True, "")


def rmedic_dead_action(s):
    # Two strikes. An unreachable host reports NO tokens rather than raising
    # (live_tokens swallows it deliberately, to avoid calling a whole host's
    # jobs dead on one bad ssh), so a single observation of "not alive" can be
    # a network blip. Requiring a second firing costs one tick and spans a
    # fresh sweep, since the liveness cache is shorter than two ticks.
    j = s["jobs"]["medic"]
    if j["retries"] < 1:
        j["retries"] += 1
        note(s, "2a medic not observed alive; one more tick before escalating")
        commit(s, "medic not observed alive (strike 1 of 2)")
        return
    why = s["jobs"]["medic"]["payload"]
    s["email"].append("medic died without a verdict; the panic it was sent to "
                      "repair is UNREPAIRED: " + str(why))
    commit(s, "medic died without a verdict -> STOP")
    s["stop"] = True
    note(s, "2a medic died without a verdict -> emailed, STOP written")


def rmedic_wait_guard(s):
    """SAFE MODE engages on the medic RECORD, before it has even started.

    An earlier version engaged on the medic running, and spawned it by hand
    from this row to get around the ordering -- a second spawner in a design
    whose whole point is that there is exactly one, which skipped the host,
    the pid, the session and the prompt.
    """
    # Engages on the RECORD, so nothing operational runs in the gap between a
    # panic being reported and the medic actually starting. That gap was real:
    # the panicking agent was integrated by the row below on the very next
    # tick, which is exactly what checking panic above the consumers was
    # supposed to prevent. SPAWN sits above this row and spawnable() refuses
    # every non-medic kind while a medic exists, so the medic can still start.
    if "medic" not in s["jobs"]:
        return (False, "no medic in flight (normal operation)")
    return (True, "")


def rmedic_wait_action(s):
    note(s, "3  SAFE MODE: waiting on medic; all normal rows suspended")


def r2_guard(s):
    hits = [n for n, j in jobs_of(s, "agent").items() if finished(j)]
    return (bool(hits), "no agent is started ∧ ¬alive ∧ sentinel")


def r2_action(s):
    """Integrate a finished agent, and RELAY what it addressed to someone.

    An agent's sentinel is not a report -- nothing reads reports. It carries at
    most three things, each addressed to a specific reader, and each is
    delivered here or it is lost:

      queue     -> queue2, the accumulator the next release audits and dispatches
      to_merger -> the merger inbox, pasted into the next merge worker's prompt
      to_medic  -> a panic (row 5 sees it above every consumer)

    Anything else an agent writes goes nowhere, which is the point: a message
    with no addressee has no delivery.
    """
    for n, j in list(jobs_of(s, "agent").items()):
        if not finished(j):
            continue
        sen = j["sentinel"]
        # `opened` is the older spelling of the same thing; accept both so an
        # agent running an older prompt is still integrated rather than dropped.
        for task in (sen.get("queue") or []) + (sen.get("opened") or []):
            if task and task not in s["queue2"]:
                s["queue2"].append(task)
        for msg in (sen.get("to_merger") or []):
            if msg:
                s["merger_inbox"].append("from %s: %s" % (n, msg))
        s["batch"].append(j["worktree"])
        s["workers"][j["worktree"]] = "awaiting_merge"   # set BEFORE deleting the record
        s["ancestor"][j["worktree"]] = False
        del s["jobs"][n]
        note(s, "2  integrated %s: batched; %d task(s) -> queue2, %d note(s) -> merger"
                % (n, len(sen.get("queue") or []) + len(sen.get("opened") or []),
                   len(sen.get("to_merger") or [])))


def landed(s):
    """Everything a landed branch entitles us to discharge.

    LANDING IS ONE EVENT WITH TWO CONSEQUENCES, and this row used to take only
    the first. A branch that becomes an ancestor of main frees its worker AND
    settles its place in the merge queue -- there is nothing left to merge, so
    a queue entry for it is a claim on work that no longer exists.

    Taking only the worker half produced the 2026-07-31 panic. The merge worker
    publishes main WHILE it is still running, and a medic had (correctly, on
    the evidence available to it) restored branches that turned out to be
    already merged into `merger` but not yet published. When main moved, this
    row freed 31 workers and left all 31 branches sitting in the batch -- and
    from that instant they were invisible to their own repair, because
    s["ancestor"] was computed for awaiting_merge workers only, so a freed
    worker's landed branch read back as un-merged. Permanently queued, and
    correctly reported by the orphan invariant as a state the loop could not
    progress out of.

    Note this is a FOLD, not the assignment-that-deletes-work that has now
    caused three separate leaks: the claim is discharged only where ancestry --
    the fleet's one receipt, which a decline produces as surely as a merge --
    says it has been honoured.
    """
    free = [w for w in s["workers"]
            if wstate(s, w) == "awaiting_merge" and s["ancestor"].get(w)]
    done = [b for b in (list(s["batch"]) + list(s["inflight"] or []))
            if s["ancestor"].get(b)]
    return free, done


def r3_guard(s):
    free, done = landed(s)
    return (bool(free or done),
            "no landed branch to discharge: no awaiting_merge worker and no "
            "queued branch is an ancestor of main")


def r3_action(s):
    free, done = landed(s)
    for w in free:
        s["workers"][w] = None
        note(s, f"3  {w} branch landed -> free")
    if done:
        drop = set(done)
        s["batch"] = [b for b in s["batch"] if b not in drop]
        if s["inflight"] is not None:
            s["inflight"] = [b for b in s["inflight"] if b not in drop]
        note(s, "3  %d queued branch(es) already in main -> dropped from the "
                "merge queue: %s%s" % (len(done), ", ".join(sorted(drop)[:6]),
                                       " ..." if len(drop) > 6 else ""))


def r4_guard(s):
    hits = [n for n, j in jobs_of(s, "agent").items() if died(j)]
    return (bool(hits), "no agent is started ∧ ¬alive ∧ ¬sentinel")


def r4_action(s):
    """A died agent RESUMES its own conversation. It does not start over.

    The loop chose the agent's session id when it spawned it, so the transcript
    is addressable: row 3 re-launches with `--resume <session>` instead of a
    fresh prompt, and the agent comes back knowing its task, what it had tried
    and what had failed. Starting a stranger in the worktree instead throws all
    of that away and makes it re-derive the situation from `git diff`.

    A NEW token is minted even though the session is kept: the token names the
    PROCESS (it is what the liveness sweep matches in argv[0]), the session
    names the CONVERSATION. Reusing the token would let a stale `.started`
    marker, or a straggler still exiting, be mistaken for the replacement.

    Takeover -- a fresh agent told to read `git status` -- is the fallback for
    a record with no session, which now means only the ones inherited from
    before the loop existed.
    """
    for n, j in jobs_of(s, "agent").items():
        if died(j):
            j["started"] = False
            j["alive"] = False
            j["token"] = tok()
            j["retries"] += 1
            if j.get("session"):
                j["resume"] = True
                note(s, f"4  {n} died -> resuming its session "
                        f"(attempt {j['retries']})")
            else:
                j["takeover"] = True
                note(s, f"4  {n} died, no session -> fresh takeover "
                        f"(attempt {j['retries']})")


def r5_guard(s):
    if any(spawnable(s, j) for j in s["jobs"].values()):
        return (True, "")
    if any(unspawned(j) for j in s["jobs"].values()):
        return (False, "every host is at capacity -- nowhere to spawn")
    return (False, "every job record already has a live process or a .started marker")


def r5_action(s):
    # A pending medic is spawned ALONE. Everything else is operational work,
    # and a panic is the one moment where starting more of it is wrong: the
    # state is already unexplained.
    pending_medic = [n for n, j in s["jobs"].items()
                     if j["kind"] == "medic" and unspawned(j)]
    # Rate-limited. 47 agents were waiting to start at once after the fleet was
    # rebuilt, and starting them in a single tick would put a thundering herd
    # on machines shared with other users -- with the loadavg the placement
    # reads lagging a minute behind the damage.
    budget = SPAWNS_PER_TICK
    for n, j in s["jobs"].items():
        if pending_medic and n not in pending_medic:
            continue
        if budget <= 0:
            break
        if spawnable(s, j):
            budget -= 1
            j["started"] = True
            j["alive"] = True
            # Identity is recorded BY the spawn, not by the record that
            # preceded it -- the record exists precisely while there is no
            # process yet. `session` is the Claude transcript id, which is
            # what row 6 resumes from: a died agent is continued from its
            # transcript, never restarted from nothing, so losing this field
            # would silently convert every resume into a redo.
            # Placement was decided when the record was created; spawning
            # only executes it. Choosing here would let the decision drift
            # from the worktree the record already names.
            j["host"] = (j.get("host") or host_of(s, j["worktree"])
                         or (MEDIC_HOST if j["kind"] == "medic" else None))
            # `session` used to be recorded here for a transcript resume that
            # does not exist and cannot: the loop is a Python process, not a
            # Claude session, and the ids it can obtain are not resumable. It
            # was written on every record and read by nothing, which made the
            # capability look real. Dropped; what preserves a dead agent's work
            # is its WORKTREE, and the takeover prompt tells its replacement to
            # read it.
            host, pid, sess = SPAWN(s, n, j)
            j["host"], j["pid"] = host, pid
            if sess:
                j["session"] = sess
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
    # NO comparison against a main sha, of any kind. "main moved" is not
    # evidence that THIS merger released -- main moves for reasons the loop
    # does not cause, and every sha-proxy tried here failed the same way:
    # against `rebaselined` a single tooling commit disabled this row forever;
    # against a `base` stamped at creation it survived exactly until the next
    # tooling commit, which the medic writing this line then made itself while
    # repairing the first version.
    #
    # The contract is what settles it. A merger delivers by moving main AND
    # leaving a current snapshot AND a current audit AND reporting -- so one
    # that died with no sentinel did not deliver, whatever main is doing. The
    # single exception is a full delivery on disk that it was killed before
    # reporting; that is precisely r7_guard, so ask it rather than approximate
    # it, and let ADOPT take it.
    if r7_guard(s)[0]:
        return (False, "the full delivery is on disk -- ADOPT handles it")
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
    # `snapshot_current` / `audit_current`, NOT sha equality. A tooling commit
    # moves main without touching a single Lean input, so raw equality made
    # every one of them retroactively unadopt the release that was already
    # delivered -- and then this row stopped matching, nobody consumed the
    # finished merger, and the loop panicked. Twice, on two different medics'
    # own repair commits. See lean_equiv() for what "current" now means.
    if not s["snapshot_current"]:
        snap = s["snapshot"]["sha"] if s["snapshot"] else "none"
        return (False, f"main is {s['main']} but the snapshot is {snap}")
    if not s["audit_current"]:
        return (False, f"main is {s['main']} but queue1 is audited at "
                       f"{s['queue1']['audited'] or 'none'}")
    return (True, "")


def r7_action(s):
    s["rebaselined"] = s["main"]
    # Only a merger's claim is discharged here. This row also fires with NO
    # merger record -- main moving by a tooling commit is a re-baseline with no
    # release behind it -- and in that case .inflight belongs to somebody else.
    # Clearing it unconditionally would drop an outstanding claim on the floor,
    # which is fault 3 all over again by a different door.
    if s["jobs"].pop("merger", None) is None:
        note(s, f"7  re-baselined to {s['main']} with no release behind it "
                f"(main moved without changing any Lean input)")
        return
    # A DELIVERY IS NOT A RECEIPT FOR THE WHOLE CLAIM. Adopting used to
    # discharge .inflight wholesale, on the strength of the release being
    # complete -- and a release is complete when main moved and the snapshot
    # and audit are current, which says NOTHING about how much of the payload
    # got merged. So a merger that merged 18 of its 55 branches and then died
    # (r6_guard defers to r7_guard: "the full delivery is on disk, ADOPT takes
    # it") had the other 37 dropped in this one assignment, exactly as fault 3
    # dropped 46 in r11_action's. Their worktrees stayed awaiting_merge for
    # ever after, because a worker is freed only by its branch BECOMING an
    # ancestor of main and nothing was left to merge it. 78 worktrees -- one
    # full day of the fleet's output -- were lost this way before the anomaly
    # block was written and saw the two numbers fail to add up.
    #
    # The receipt is ANCESTRY, and every outcome the merger is allowed already
    # produces it: a merge makes the branch an ancestor, and so does a DECLINE,
    # which this fleet records as an explicit empty merge commit (CLAUDE.md,
    # class 7: `git checkout HEAD -- <files>`, so the diff against the first
    # parent is empty on purpose). A claimed branch that is neither is one the
    # merger never dealt with, so it goes back to the batch and the next merger
    # gets it. Partial delivery is now self-correcting rather than a leak.
    #
    # ANCESTRY ALONE decides, and it has to be ancestry of the BRANCH rather
    # than the state of its worker. This test was once `wstate(...) ==
    # "awaiting_merge" and not ancestor`, because row 7 sits ABOVE this one and
    # may already have freed the branches that DID land, while s["ancestor"]
    # was computed for awaiting_merge workers only -- so a freed worker read
    # back as "not an ancestor" and the worker-state test was the only thing
    # stopping every just-freed branch from being re-batched. load() now asks
    # about the queued branches themselves, which answers the question
    # directly. The worker-state proxy has to go with it: a branch whose worker
    # was freed WITHOUT landing (a medic repairing state, a worktree
    # re-dispatched under it) still carries unmerged work, and the proxy would
    # have silently dropped it -- fault 3 one more time, by one more door.
    claim = list(s["inflight"] or [])
    unmerged = [b for b in claim if not s["ancestor"].get(b)]
    # Discharged only after the unmerged remainder has been taken out of it.
    # Leaving it set would make ".inflight non-empty with no merger record"
    # ambiguous between "a claim was dropped on the floor" and "a claim was
    # honoured" -- and r11_action recovers the first, so it must be able to
    # tell them apart. Row 9 already clears it on the failure path; this is the
    # success path saying the same thing.
    s["inflight"] = None
    if unmerged:
        s["batch"] = unmerged + [b for b in s["batch"] if b not in unmerged]
    note(s, f"7  ADOPTED release {s['main']}: snapshot current, "
            f"queue1 AUDITED with {len(s['queue1']['tasks'])} task(s)"
            + (f"; {len(unmerged)} claimed branch(es) never landed -> batch"
               if unmerged else ""))


def r11_guard(s):
    if "merger" in s["jobs"]:
        return (False, "a merger record already exists")
    # Stale means "a build of main would differ from what we have", not "main
    # moved". Under raw sha equality a tooling commit ordered a full 4.6 GB
    # rebuild of a tree whose Lean sources had not changed by one byte.
    stale = not s["snapshot_current"] or not s["audit_current"]
    if not s["batch"] and not stale:
        return (False, "nothing to merge and nothing derived from main is stale")
    return (True, "")


def r11_action(s):
    # An empty batch is allowed: main can move without us (a tooling commit),
    # and then the snapshot and the audit describe a main that no longer
    # exists. The merger is what refreshes them, so it must be startable with
    # nothing to merge -- otherwise that state is a silent deadlock in which
    # dispatch is blocked forever on a snapshot nobody will ever rebuild.
    #
    # FOLDED, never overwritten. This line used to read
    # `s["inflight"] = list(s["batch"])`, which DESTROYS an outstanding claim,
    # and it destroyed a real one: the bootstrap handed the loop the stopped
    # fleet's 46-branch merge batch in .inflight with no merger record to own
    # it, this row fired eleven minutes later because the snapshot was stale,
    # and all 46 were gone in one assignment. 37 of them were still unmerged
    # 2 hours later -- every one ahead of main with real work on it, their
    # worktrees pinned in awaiting_merge forever, since a branch is only freed
    # by BECOMING an ancestor of main and nothing was ever going to merge it.
    # Nothing panicked, because no guard asks about an unowned claim: the loop
    # cannot distinguish work it dropped from work that was never there.
    #
    # A non-empty .inflight with no merger record is precisely that dropped
    # claim -- r7_action discharges the claim it delivers and row 9 restores
    # the claim it fails to, so the only way to reach this row with one
    # outstanding is that its owner vanished without either. It is work to be
    # merged, this is the row that creates the merger, so it joins the claim.
    # (The simulator has always had a `corrupt: orphan .inflight` injection for
    # exactly this state. It exercised the path; nobody checked that clobbering
    # was the wrong answer to it.)
    orphaned = list(s["inflight"] or [])
    claim = orphaned + [b for b in s["batch"] if b not in orphaned]
    s["inflight"] = claim
    s["batch"] = []
    # Drain the inbox onto the record: delivered exactly once, to the merger
    # that actually carries these branches. Leaving it in place would repeat
    # every note to every future merger forever.
    inbox, s["merger_inbox"] = list(s["merger_inbox"]), []
    s["jobs"]["merger"] = {
        "kind": "merger", "worktree": "flt-staging", "payload": s["inflight"],
        "inbox": inbox,
        "token": tok(), "retries": 0, "started": False, "alive": False,
        "sentinel": None,
    }
    note(s, "11 merger record created; claimed %d branch(es)%s%s"
            % (len(claim),
               "" if claim else " (refresh only -- nothing to merge)",
               " [recovered %d orphaned by a vanished merger]" % len(orphaned)
               if orphaned else ""))


def r15_guard(s):
    if not s["audit_current"]:
        return (False, "queue1 is not AUDITED at main")
    if not s["queue1"]["tasks"]:
        return (False, "queue1 is empty")
    if not s["snapshot"]:
        return (False, "no snapshot for agents to copy .lake from")
    if not s["snapshot_current"]:
        # Existence is not enough. After a rebaseline the PREVIOUS release's
        # snapshot is still on disk while the new one builds, and dispatching
        # against it seeds every agent with a .lake for the wrong main -- the
        # inconsistent-olean failure this project already knows well, where
        # loading does not typecheck and the mismatch surfaces later as a
        # bogus kernel error in an unrelated file. Row 13 already required
        # snapshot == main before starting a merger; dispatch was the row that
        # only checked non-None.
        return (False, f"snapshot is {s['snapshot']['sha']}, main is {s['main']}")
    if pick_worker(s) is None:
        return (False, "no free ∧ healthy worktree on a host with spare capacity")
    return (True, "")


def r15_action(s):
    # Re-picked each time round: claiming a worktree changes its host's load,
    # so allocating the whole free list up front would pile a run of tasks
    # onto one machine before the balance was recomputed.
    n, placed = 0, []
    while s["queue1"]["tasks"]:
        w = pick_worker(s)
        if w is None:
            break
        task = s["queue1"]["tasks"].pop(0)
        s["jobs"][w] = {
            "kind": "agent", "worktree": w, "payload": task,
            "host": host_of(s, w),
            "token": tok(), "retries": 0, "started": False, "alive": False,
            "sentinel": None,
        }
        placed.append("%s->%s" % (task.splitlines()[0][:40] if task else "?", w))
        n += 1
    note(s, "15 dispatched %d agent record(s): %s" % (n, ", ".join(placed)))


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
        # The reason IS the payload. A medic told only "something is wrong"
        # has to re-derive the diagnosis from the git history, and the one
        # thing the loop knows and it does not is which guard failed and on
        # what -- that is the whole content of the panic. Emailing the reason
        # while handing the repair agent a bare "diagnose" would put the
        # useful half in the place nobody acts on.
        # `flt-loop-state` was a path that does not exist, so the spawn's
        # `cd || cd REPO` fallback quietly put the medic in the repo while its
        # prompt told it to work somewhere else. The repo IS the medic's
        # worktree: the loop source lives there and the state dir is its own
        # git repo, addressed absolutely.
        "kind": "medic", "worktree": "flt-lean", "payload": reason,
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
    # Self-disabling: once a medic exists the panic is being handled, and the
    # report must stop matching. Without this the row fires every tick and
    # rebuilds the medic record from scratch each time -- so the medic is
    # perpetually one tick old, never survives long enough for SPAWN (which
    # sits below this row) to start it, and the loop reports the same panic
    # forever while doing nothing about it.
    if "medic" in s["jobs"]:
        return (False, "a medic is already handling a panic")
    hits = [(n, j) for n, j in s["jobs"].items()
            if finished(j) and (j["sentinel"].get("to_medic")
                                or j["sentinel"].get("panic"))]
    if not hits:
        return (False, "no job reported panic")
    n, j = hits[0]
    return (True, "%s: %s" % (n, j["sentinel"].get("to_medic")
                              or j["sentinel"].get("why") or "no reason given"))


def reported_panic_action(s):
    n, j = next((n, j) for n, j in s["jobs"].items()
                if finished(j) and (j["sentinel"].get("to_medic")
                                    or j["sentinel"].get("panic")))
    why = (j["sentinel"].get("to_medic")
           or j["sentinel"].get("why") or "no reason given")
    # The record is kept, not consumed: the medic needs to see what came back.
    panic(s, "%s (%s) reported PANIC: %s" % (n, j["kind"], why))


def inferred_panic(s):
    """The catch-all. Say what could not be explained, not merely that it was.

    The idle guard already computed the answer: it is the list of jobs it
    refused to justify. Passing that through means the medic gets "merger
    stopped and no row consumed it" rather than "no row matched", which is the
    difference between a diagnosis and a notification.
    """
    bad = unjustified(s)
    if bad:
        why = "unjustified jobs -- " + "; ".join(f"{n}: {w}" for n, w in bad)
    elif not any(j["alive"] for j in s["jobs"].values()):
        why = ("nothing is running and no row matched: queue1=%d queue2=%d "
               "batch=%d jobs=%d" % (len(s["queue1"]["tasks"]), len(s["queue2"]),
                                     len(s["batch"]), len(s["jobs"])))
    else:
        why = "no row matched"
    panic(s, why)


# Installed by the runtime: send one probe, and consume a job's refusal
# evidence. Both are EFFECTS, so they belong to row actions rather than to
# observation -- the loop learns it is refused by reading state, and decides
# what to do about it in the table like everything else.
PROBE = None            # () -> None, sends a probe
CONSUME_REFUSAL = None  # (name, job) -> None, moves the log aside


def now(s):
    return s.get("now") or __import__("time").time()


def refused_jobs(s):
    return {n: j for n, j in s["jobs"].items() if j.get("refused")}


def r_refused_guard(s):
    """The API refused a job. Stop spawning until it serves us again.

    This is the whole of "out of credit" as far as the machine is concerned:
    an observation about a job, and a transition. It used to be imperative code
    inside load(), which meant the one condition that halts the entire fleet
    was the one condition not expressible in the transition table -- invisible
    to --dry-run, to the medic, and to anyone reading the rows.
    """
    if s.get("quota_block"):
        return (False, "already blocked")
    hits = refused_jobs(s)
    if not hits:
        return (False, "no job reported an API refusal")
    n = sorted(hits)[0]
    return (True, "%s was refused: %s" % (n, hits[n]["refused"].strip().splitlines()[0][:70]))


def r_refused_action(s):
    hits = refused_jobs(s)
    n = sorted(hits)[0]
    s["quota_block"] = {"since": int(now(s)),
                        "why": hits[n]["refused"].strip().splitlines()[0][:200]}
    for m, j in hits.items():
        # A refusal is not a death: the record goes back to unspawned so it is
        # retried once the door opens, and its evidence is consumed so the same
        # line cannot re-arm the block for ever.
        j["started"], j["alive"], j["refused"] = False, False, ""
        if CONSUME_REFUSAL:
            CONSUME_REFUSAL(m, j)
    note(s, "quota: refused -- spawning halted, %d record(s) returned to the queue"
            % len(hits))
    s["email"].append("flt-loop: quota exhausted, idling -- %s" % s["quota_block"]["why"])


def r_unblock_guard(s):
    if not s.get("quota_block"):
        return (False, "not blocked")
    if not s["probe"]["served"]:
        return (False, "no probe has come back served")
    return (True, "")


def r_unblock_action(s):
    s["quota_block"] = None
    s["probe"] = dict(s["probe"], served=False)
    note(s, "quota: a probe was served -- spawning resumes")
    s["email"].append("flt-loop: quota available again, resuming")


def r_probe_guard(s):
    """Blocked and no answer yet -- ask again. Every tick, no timer.

    A refused call costs nothing: the API rejects it immediately and it
    consumes no quota, so there is nothing to ration and no reason to wait
    between attempts. Probing on every cycle also removes two things that only
    existed to approximate this one: the staleness interval, and the special
    case that forced an immediate probe when the rotator swapped credentials.
    Both were answering "has the answer changed yet?" indirectly. Asking every
    tick answers it directly, and the block lifts the tick after the door
    opens rather than up to five minutes later.

    It stops on its own: a served probe fires row 19, which clears the block,
    and this guard needs the block.
    """
    if not s.get("quota_block"):
        return (False, "not blocked")
    if s["probe"]["served"]:
        return (False, "a served probe is waiting to be consumed")
    return (True, "")


def r_probe_action(s):
    if PROBE:
        PROBE()
    note(s, "quota: probed with the credential now on disk")


def anomalies(s):
    """Invariants that must hold of the state. Every violation is a bug.

    EXPECT THIS TO GROW. It is the standing home for "this should never be
    true", added to as bugs are found, so that each one is caught by the
    machine the next time instead of by a human noticing two numbers do not
    add up. Everything here must be genuinely always-true: a false positive
    panics a healthy fleet, which is worse than the bug it was guarding.

    Returns a list of one-line descriptions, empty when the state is sound.
    """
    out = []
    aw = {w for w, st in s["workers"].items() if st == "awaiting_merge"}
    batch, infl = set(s["batch"]), set(s["inflight"] or [])
    queued = batch | infl

    # A worker is awaiting_merge for exactly as long as its branch is waiting
    # to be merged, so the two sets are the same set seen from either end. They
    # are written by different rows (6 batches, 11 claims, 7 frees), which is
    # precisely why they can drift apart without anyone noticing.
    #
    # Found 2026-07-30 with 97 awaiting_merge against 19 queued branches: when
    # a merge worker DECLINES a branch, the branch leaves .inflight but nothing
    # frees its worker, so the worker is stranded and the pool silently shrinks.
    # A worker whose branch has ALREADY LANDED is not stranded -- row 7 frees
    # it on the next tick. That window is opened by every release, so counting
    # it as a fault would panic on the loop's own normal operation.
    lost = sorted(w for w in (aw - queued) if not s["ancestor"].get(w))
    if lost:
        out.append("%d worker(s) awaiting_merge with no branch in batch or "
                   "inflight -- stranded, pool shrinking: %s%s"
                   % (len(lost), ", ".join(lost[:6]),
                      " ..." if len(lost) > 6 else ""))
    # Mirror of the exemption above, and for the mirror-image reason: between a
    # branch landing and row 7 dropping it from the queue there is one tick in
    # which it is queued behind a worker row 7 has already freed. That window
    # is opened by every release, so counting it as a fault would panic on the
    # loop's own normal operation -- which is exactly what it did on
    # 2026-07-31, when nothing dropped landed branches from the queue at all
    # and the window never closed. A queued branch that is NOT in main and has
    # no worker waiting on it is still a real fault: nobody is holding that
    # worktree, so it can be re-dispatched under the branch.
    orphan = sorted(w for w in (queued - aw) if not s["ancestor"].get(w))
    if orphan:
        out.append("%d branch(es) queued to merge whose worker is not "
                   "awaiting_merge: %s%s"
                   % (len(orphan), ", ".join(orphan[:6]),
                      " ..." if len(orphan) > 6 else ""))

    both = sorted(batch & infl)
    if both:
        out.append("branch(es) in BOTH batch and inflight, so a merge worker "
                   "and the queue disagree about who owns them: %s"
                   % ", ".join(both[:6]))

    if len(s["batch"]) != len(batch):
        out.append("batch contains duplicate entries -- a branch would be "
                   "merged twice")
    if s["inflight"] and len(s["inflight"]) != len(infl):
        out.append("inflight contains duplicate entries")

    # A worktree cannot be running a job and waiting to be merged at once.
    for n, j in s["jobs"].items():
        if j["kind"] == "agent" and s["workers"].get(j["worktree"]) == "awaiting_merge":
            out.append("worktree %s has a live agent record AND is "
                       "awaiting_merge" % j["worktree"])
    return out


def anomaly_guard(s):
    """Fires only when nothing else can make progress.

    Deliberately the LAST row before idle. Half the states that look wrong for
    an instant are ones the very next row repairs -- a release leaves workers
    awaiting_merge until row 7 frees them, an agent finishes before row 6
    batches it. Checking above those rows would report the loop's own normal
    operation as a fault. Sitting here means every row that could act has
    declined, so what remains is a state the loop cannot progress out of, which
    is what an anomaly actually is.
    """
    # Self-disabling in the same way the reported-panic row is: once a medic
    # exists the violation is being handled, and re-firing would rebuild the
    # medic record every tick and never let it start.
    if "medic" in s["jobs"]:
        return (False, "a medic is already handling something")
    bad = anomalies(s)
    if not bad:
        return (False, "no invariant violated")
    return (True, bad[0][:110])


def anomaly_action(s):
    bad = anomalies(s)
    panic(s, "INVARIANT VIOLATED (%d): %s" % (len(bad), " | ".join(bad[:4])))


ROWS = [
    (1, "STOP exists", r1_guard, r1_action),
    (2, "medic finished -> apply GO / NO-GO verdict", rmedic_done_guard, rmedic_done_action),
    # Id 16, not 3: ids are stable names that IDLE/PANIC/QUIET refer to by
    # number, so a new row is appended to the numbering and inserted in the
    # ORDER. Renumbering would silently repoint those constants at other rows.
    (16, "medic died without a verdict -> escalate + STOP",
     rmedic_dead_guard, rmedic_dead_action),
    (18, "API refused a job -> halt spawning", r_refused_guard, r_refused_action),
    (19, "quota blocked ∧ probe served -> resume", r_unblock_guard, r_unblock_action),
    (20, "quota blocked ∧ no answer yet -> probe again", r_probe_guard, r_probe_action),
    (3, "record ∧ ¬started ∧ no process -> SPAWN", r5_guard, r5_action),
    (4, "medic in flight -> SAFE MODE (all rows below suspended)",
     rmedic_wait_guard, rmedic_wait_action),
    (5, "a job REPORTED panic -> notify + medic", reported_panic_guard, reported_panic_action),
    (6, "agent finished -> integrate, awaiting_merge", r2_guard, r2_action),
    (7, "branch landed -> free its worker, drop it from the merge queue",
     r3_guard, r3_action),
    (8, "agent died -> resume its session", r4_guard, r4_action),
    (9, "merger died without releasing -> restore .inflight", r6_guard, r6_action),
    (10, "merger delivered main+snapshot+audit -> ADOPT", r7_guard, r7_action),
    (11, "batch ∨ derived-from-main is stale -> create merger record", r11_guard, r11_action),
    (12, "dispatch: pop queue1 -> agent records", r15_guard, r15_action),
    (17, "INVARIANT VIOLATED -> notify + medic", anomaly_guard, anomaly_action),
    (13, "idle -- every live job is justified", idle_guard, lambda s: None),
    (14, "ILLEGAL STATE -> notify + medic", lambda s: (True, ""), inferred_panic),
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

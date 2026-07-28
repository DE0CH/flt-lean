#!/usr/bin/env python3
"""PreToolUse hook on the Agent tool (Deyao, 2026-07-23): allocates a
worktree from the fixed 13-worktree pool, fed by a FIFO task queue.

TASK QUEUE (Deyao, 2026-07-23): ~/.flt-task-queue is a plain text file
in the home folder — tasks (full agent prompts, normally containing
{{FLT_WORKTREE}}) separated by lines consisting exactly of the
delimiter `=== TASK ===`. The orchestrator pushes/edits/reorders BY
HAND-EDITING THE FILE. Dispatch of the queue head uses the special
prompt sentinel {{FLT_QUEUE_POP}}: this hook intercepts it, pops the
top task, allocates a free worktree, substitutes the worktree path for
{{FLT_WORKTREE}} inside the queued prompt, and replaces the Agent
call's prompt with the result.

Rules enforced here:
- A direct {{FLT_WORKTREE}} dispatch that cannot run immediately
  (queue nonempty -- FIFO order -- or no free worktree) is AUTO-QUEUED:
  the hook itself appends the prompt to ~/.flt-task-queue and denies
  the call with a message saying the task has been queued and that
  {{FLT_QUEUE_POP}} pops the head once there is capacity.
- Non-fleet spawn (no placeholder) while the queue is nonempty -> DENY,
  reminding the orchestrator to dispatch queued items first.
- Sentinel + empty queue -> DENY (nothing to pop).
- A queue pop with no free worktree leaves the queue untouched.

POOL STATES (Deyao, 2026-07-25). Exactly one of:

- `free` — idle and allocatable. The ONLY state `allocate_worktree` selects.
- `claimed` — an agent is working in it.
- `reclaiming` — claimed, but retire this slot when its task finishes. How
  the fleet drains from 62 workers to ~30 without interrupting anyone.
- `suspended <agent-id>` — the worktree is DIRTY and its state matches a
  recorded transcript: an agent was stopped mid-task and is meant to be
  resumed from the middle. The third field is that transcript id, and it is
  the whole point of the state — without it the in-progress work is
  unrecoverable. Never allocate, never clean, never mark a clean worktree
  this way.
- `retired` — the worktree is CLEAN, its last agent exited cleanly, and
  there is nothing to resume. Held out of service only for capacity
  reasons, so it can be promoted straight back to `free` the moment
  capacity allows.

The `suspended`/`retired` split matters because the two look identical in a
worker count but are opposite in kind: `suspended` means "work is parked
here, resume it", `retired` means "nothing here, reuse me freely".

None of these need code in this hook to be safe: `allocate_worktree`
selects only `free`, and the pool rewrite preserves every other status
verbatim. The rules that give them meaning live in the integration step —
`post-merge-reminder.py` maps `claimed → free` and `reclaiming → retired`
on merge — and in the RAM watchdog, which is what creates
`suspended <agent-id>` when it has to stop a live agent under memory
pressure.

The drain exists because the user slice is CPU-quota-capped at 24 cores
(cpu.max 2400000/100000), throttled in ~76% of periods, so workers past the
quota lengthen every verification instead of adding throughput.

Worktree allocation: find a `free` entry in ~/.flt-worktree-pool, check
it is git-clean and its branch is an ancestor of MAIN, fast-forward it
to main (--ff-only), mark it `claimed`. A worktree marked free but
dirty/diverged is NOT a normal condition and is NOT auto-corrected —
hard crash (traceback, exit 2, tool call blocked): something beyond
allocation went wrong.

RELEASE MODEL (Deyao, 2026-07-26). `main` is the only branch anything
is dispatched from, and ONLY THE MERGER MOVES IT, only to a sha it has
built green. The orchestrator never merges. When an agent finishes, its
worktree name goes into ~/.flt-merge-batch (`flt-cycle.py done`) and
sits there; the merger claims the batch, merges it, resolves conflicts,
drives the build green, and moves main. That is a RELEASE. The
orchestrator then runs `flt-cycle.py release`, which fast-forwards idle
worktrees to main and seeds their `.lake` from the merger's own build,
and only then dispatches queued work.

The merger is self-paced: the moment it finishes a batch it claims the
next one. Nothing schedules it.

Freeing a worktree, batching it, and pushing to the task queue are the
orchestrator editing text files or running `flt-cycle.py`, the single
entry point. No merging on that side.

CONCURRENCY (fixed 2026-07-25). Everything below runs under ONE
exclusive flock on the pool file, held for the whole dispatch decision:
queue read, pop, queue write, and worktree allocation. Do not narrow it
back. Consequence for `.claude/settings.json`: this hook's `timeout`
must stay GENEROUS (currently 300s). Each run does three git operations
in a worktree (~8s under fleet load) while holding the lock, and a wave
of N simultaneous spawns serializes them — with a 30s timeout, the
spawns past ~3rd were KILLED, and a killed PreToolUse hook is
non-blocking, so the Agent launched with the ORIGINAL prompt: agents
whose prompt was the literal {{FLT_QUEUE_POP}} sentinel, holding no
worktree and no task. Both failure modes were observed together in one
04:52Z wave of seven: four agents got the SAME task (lost-update pops)
and three were sentinel zombies.
"""

import datetime
import fcntl
import json
import os
import re
import subprocess
import sys
import time
import traceback

POOL_FILE = "/home/chend/.flt-worktree-pool"
QUEUE_FILE = "/home/chend/.flt-task-queue"
# In-flight registry (Deyao, 2026-07-25). The queue records work NOT yet
# started; the pool records which worktrees are busy but not WHAT they are
# doing. Neither answers "is this leaf already being worked on?", so the
# orchestrator's post-merge queue review could only catch duplicates still
# sitting in the queue — never ones already dispatched. That hole produced
# four independent proofs of `span_vertNumerator` and two agents redirected
# off already-proven leaves. This file closes it: one JSON object per line,
# appended here at dispatch, removed by the orchestrator at integration.
INFLIGHT_FILE = "/home/chend/.flt-inflight.jsonl"
PLACEHOLDER = "{{FLT_WORKTREE}}"
SENTINEL = "{{FLT_QUEUE_POP}}"

# The STAGING worker (Deyao, 2026-07-25) is a third kind of dispatch and must
# bypass both of the mechanisms above.
#
# It lives in a FIXED worktree outside the 110-slot pool, so it must not consume
# an allocation -- and it must not be denied when the queue is non-empty, which
# is exactly when it is most needed: a backlog means main has not been promoted
# in a while, and the whole point of this worker is to verify staging and promote
# it. Making it queue behind ordinary leaf tasks would deadlock the thing that
# unblocks them.
#
# Its worktree tracks `merger`, its own branch, so the source cannot move under
# it mid-batch. (`staging` and `staging-worker` were deleted on 2026-07-26.)
STAGING_PLACEHOLDER = "{{FLT_STAGING}}"
STAGING_WORKTREE = "/home/chend/flt-staging"
DELIMITER = "=== TASK ==="
BASE_PREFIX = "#base:"
HOME = "/home/chend"
# Second pool batch (Deyao, 2026-07-24): the home volume filled up (a
# worktree costs ~5.4G, 4.6G of it mathlib oleans), so flt-lean-14..26
# live on the local scratch disk. A pool entry is resolved by looking
# for the worktree in each root in order, so the original 13 keep
# resolving under $HOME exactly as before.
ROOTS = [HOME, "/scratch/chend-flt"]


def git(args, cwd):
    return subprocess.run(
        ["git", "-C", cwd] + args, capture_output=True, text=True, check=False
    )


TARGET_RE = re.compile(r"\*\*`([^`]+)`\*\*")


MERGE_CLAIM = os.path.join(HOME, ".flt-merge-batch.inflight")


def staging_owner():
    """Evidence that a merge worker already holds the staging worktree.

    Two mergers share one .lake and corrupt each other's build, so this errs
    toward DENYING: a stale claim blocking a dispatch is recoverable by
    deleting one file, whereas two concurrent mergers is not.

    The claim file is what `flt-cycle.py claim` creates when a merger takes a
    batch, so it is the fleet's existing signal. A /proc cwd scan is NOT used:
    the merger drives builds with `ssh host 'cd ~/flt-staging && ...'`, so its
    local cwd is elsewhere and the scan reports "free" while it is working —
    verified 2026-07-27.
    """
    if os.path.exists(MERGE_CLAIM):
        try:
            n = sum(1 for line in open(MERGE_CLAIM) if line.strip())
        except OSError:
            n = "?"
        return f"{MERGE_CLAIM} exists ({n} branches claimed)"
    return None


def record_inflight(worktree_path, prompt, kind, payload):
    """Append one in-flight record. Called INSIDE the pool flock, so
    concurrent dispatches serialise here exactly as they do for the queue.

    `targets` is the useful field: the leaf names the task names in bold,
    which is what makes a duplicate detectable at a glance. The full prompt
    is kept too, so an agent that dies is re-dispatchable from this file
    alone without digging through transcripts.

    NOTE on the agent transcript id: it is NOT available here. The harness
    mints it after the PreToolUse hook returns, so a dispatch-time hook
    cannot know it. What we can record is the ORCHESTRATOR's session_id and
    the tool_use_id of the spawning call, which is enough to correlate with
    a task notification after the fact. Recovering the agent id itself stays
    the orchestrator's job (and is rarely needed — each agent's own
    transcript already knows its worktree)."""
    try:
        rec = {
            "worktree": os.path.basename(worktree_path),
            "worktree_path": worktree_path,
            "kind": kind,  # "queue-pop" | "direct"
            "dispatched_at": datetime.datetime.now().isoformat(timespec="seconds"),
            "targets": TARGET_RE.findall(prompt)[:8],
            "session_id": payload.get("session_id"),
            "tool_use_id": payload.get("tool_use_id"),
            "prompt": prompt,
        }
        with open(INFLIGHT_FILE, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(rec) + "\n")
    except Exception:
        # Never let bookkeeping block a dispatch: a missing record costs the
        # orchestrator a duplicate-check, a failed dispatch costs a worker.
        traceback.print_exc(file=sys.stderr)


def emit(obj):
    print(json.dumps(obj))
    sys.exit(0)


def deny(reason):
    emit({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        }
    })


def read_queue():
    """Returns the list of task texts (whitespace-only segments dropped)."""
    try:
        raw = open(QUEUE_FILE, encoding="utf-8").read()
    except FileNotFoundError:
        return []
    tasks = []
    current = []
    for line in raw.splitlines():
        if line.strip() == DELIMITER:
            if "".join(current).strip():
                tasks.append("\n".join(current).strip("\n"))
            current = []
        else:
            current.append(line)
    if "".join(current).strip():
        tasks.append("\n".join(current).strip("\n"))
    return tasks


def write_queue(tasks):
    with open(QUEUE_FILE, "w", encoding="utf-8") as fh:
        for i, t in enumerate(tasks):
            if i:
                fh.write(f"\n{DELIMITER}\n")
            fh.write(t + "\n")


def split_base(task):
    """Strip a leading `#base: <sha>` line if present and IGNORE it.

    Pinning was tried and REVERTED (Deyao, 2026-07-25): resetting a
    worktree backwards onto an older commit makes its `.lake` disagree
    with its sources, so the report server rebuilds the import cone from
    source on the agent's first diagnostics call — minutes to hours of
    re-elaboration per dispatch, which costs far more than the stale
    line numbers it was protecting. Worktrees now always advance to main;
    a task whose line references have drifted is cheap for its agent to
    re-locate by name. The header is still tolerated so queue entries
    written while pinning was live remain dispatchable."""
    lines = task.split("\n")
    if lines and lines[0].startswith(BASE_PREFIX):
        return "\n".join(lines[1:]).lstrip("\n")
    return task


HOST_DIR = "/home/chend/.flt-worker-host"
CORES_FILE = "/home/chend/.flt-worker-cores"
# Live capacity measurement (Deyao, 2026-07-25). Static core weights were wrong in
# a way that matters: these are SHARED departmental machines, and two of them were
# already carrying load ~100 from other tenants when seven were added to the pool.
# Weighting by a machine's size ignores how much of it is actually ours right now.
CAPACITY_FILE = "/home/chend/.flt-worker-capacity"
CAPACITY_TTL = 120          # seconds; a measurement older than this is re-taken
RAM_PER_WORKER_G = 10       # sharp, margin already included (Deyao)
# Our self-imposed ceiling on any one machine. These are SHARED departmental
# boxes; taking a whole idle host because it happens to be idle is how you become
# the reason someone else's job crawls. 25% is ours, the rest is theirs.
OUR_SHARE = 0.25
# Fleet-wide ceiling on concurrent workers, read LIVE from this file at every
# dispatch so it can be retuned without a restart or a code edit. The pool is
# provisioned capacity (188 slots); this is how much of it we choose to run.
LIMIT_FILE = "/home/chend/.flt-worker-limit"
DEFAULT_LIMIT = 100


def _worker_limit():
    """The concurrency ceiling. Comments and blanks ignored; first integer wins.
    An unreadable or malformed file falls back to DEFAULT_LIMIT rather than
    failing open -- an accidental unbounded fleet is the worse error."""
    try:
        with open(LIMIT_FILE, encoding="utf-8") as fh:
            for line in fh:
                line = line.split("#", 1)[0].strip()
                if line.isdigit():
                    return int(line)
    except OSError:
        pass
    return DEFAULT_LIMIT


def capacity_note():
    """One line telling the orchestrator how much MORE it can dispatch right now.

    Exists because the orchestrator does not reliably compute this. On
    2026-07-28 it dispatched in waves of 16 for hours -- correct while the
    per-host quota allowed only ~16 -- and kept the same wave size after 118
    worktrees were freed, leaving ~170 idle. The wave size was being copied
    from the shape of its own previous dispatches, not derived from state:
    refusals had been acting as the stop signal, and when they stopped
    arriving nothing counted up to the ceiling.

    So the fix is to put the number in front of it at the moment of dispatch,
    where it cannot be pattern-matched away. Never let this raise -- a
    bookkeeping nicety must not cost a worker.
    """
    try:
        ready = claimed = 0
        with open(POOL_FILE, encoding="utf-8") as fh:
            for line in fh:
                parts = line.split()
                if len(parts) < 2:
                    continue
                if parts[1] == "ready":
                    ready += 1
                elif parts[1] in ("claimed", "reclaiming"):
                    claimed += 1
        limit = _worker_limit()
        headroom = max(0, limit - claimed)
        spare = min(ready, headroom)
        if spare <= 0:
            return (f"CAPACITY: 0 more workers dispatchable right now "
                    f"({claimed} claimed against a ceiling of {limit}, "
                    f"{ready} ready). Free or promote worktrees before retrying.")
        return (f"CAPACITY: you have ~{spare} more workers you can dispatch RIGHT NOW "
                f"({claimed}/{limit} claimed, {ready} ready). Please use them -- "
                f"dispatch until this hook REFUSES rather than stopping at a "
                f"round number; refusals are free and are the only reliable "
                f"stop signal. If `ready` is the binding number, promote `free` "
                f"entries in {POOL_FILE} within each host's quota.")
    except Exception:
        return None


def _with_capacity(obj):
    """Attach the capacity note to an allow decision, if one can be computed."""
    note = capacity_note()
    if note:
        obj["hookSpecificOutput"]["permissionDecisionReason"] = note
    return obj


def _host_of(name):
    """Which machine serves this worktree, or None if unrouted."""
    try:
        with open(os.path.join(HOST_DIR, name), encoding="utf-8") as fh:
            return fh.read().strip() or None
    except OSError:
        return None


def _measure(hosts):
    """host -> {free_cpu, free_ram_g}, measured in PARALLEL over ssh.

    free_cpu is `nproc - loadavg1`, i.e. logical cores not currently being asked
    for -- by anyone, including other tenants. free_ram_g is MemAvailable.
    An unreachable host is simply absent from the result and is never allocated:
    we cannot verify it has room, so we do not guess."""
    procs, out = {}, {}
    for h in hosts:
        procs[h] = subprocess.Popen(
            ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=8", h,
             "nproc; cut -d' ' -f1 /proc/loadavg; "
             "awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo"],
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    for h, pr in procs.items():
        try:
            stdout, _ = pr.communicate(timeout=25)
            n, load, ram = stdout.split()
            out[h] = {"free_cpu": max(0.0, int(n) - float(load)),
                      "total_cpu": int(n),
                      "free_ram_g": int(ram)}
        except Exception:
            try:
                pr.kill()
            except Exception:
                pass
    return out


def _capacity(hosts):
    """Cached {host: {free_cpu, free_ram_g}}. Re-measured when stale.

    Cached rather than measured per dispatch because this runs while holding the
    pool flock, and a wave of simultaneous spawns serialises on it."""
    now = time.time()
    try:
        with open(CAPACITY_FILE, encoding="utf-8") as fh:
            blob = json.load(fh)
        cached = blob.get("hosts") or {}
        # Fresh AND covering every host we were asked about. The coverage test
        # is not pedantry (Deyao, 2026-07-26): a host absent from `cap` is
        # treated by `rank` as unreachable and VETOED outright, so a cache
        # populated from one call's host set silently excluded every machine not
        # in it for the whole TTL -- and since a vetoed host is never allocated,
        # it stays absent from later host sets too. `vanisher` and
        # `nightcrawler` were missing from the live cache for exactly this
        # reason. Missing measurements must force a re-measure, never a veto.
        if (now - blob.get("ts", 0) < CAPACITY_TTL
                and cached and all(h in cached for h in hosts)):
            return cached
    except (OSError, ValueError):
        pass
    hosts_cap = _measure(hosts)
    try:
        with open(CAPACITY_FILE, "w", encoding="utf-8") as fh:
            json.dump({"ts": now, "hosts": hosts_cap}, fh)
    except OSError:
        pass
    return hosts_cap


def _spend(host):
    """Charge one worker against the cached capacity, so a burst of dispatches
    between measurements does not all pile onto the same host."""
    try:
        with open(CAPACITY_FILE, encoding="utf-8") as fh:
            blob = json.load(fh)
        h = blob.get("hosts", {}).get(host)
        if h:
            h["free_cpu"] = max(0.0, h["free_cpu"] - 1)
            h["free_ram_g"] = max(0, h["free_ram_g"] - RAM_PER_WORKER_G)
            with open(CAPACITY_FILE, "w", encoding="utf-8") as fh:
                json.dump(blob, fh)
    except (OSError, ValueError):
        pass


def pick_free(entries, candidate_state="ready"):
    """Choose which worktree to hand out: the one on the machine with the
    most FREE CPU right now, subject to a hard RAM veto (Deyao, 2026-07-25).

    `candidate_state` is what makes LAZY SEEDING work (Deyao, 2026-07-26).
    Dispatch draws from `ready` -- advanced to the release AND holding `.lake`
    artifacts copied from the build that verified it. `flt-release.py` calls
    this same function with `candidate_state="free"` to decide WHICH worktrees
    are worth seeding, so the expensive copy lands only where work will
    actually run, and the choice of where to seed is made by exactly the
    capacity logic documented below rather than by a second, drifting copy of
    it. A `free` worktree is at the release but its artifacts are stale, so
    handing one out would hand out a from-source rebuild.

    Two rules, and the difference between them is the point:

    * **CPU is proportional, under a ceiling.** Rank hosts by
      `min(nproc - loadavg, 25% of nproc)`: logical cores nobody is currently
      asking for, but never crediting a host with more than a quarter of itself.
      These are SHARED departmental boxes, and taking a whole idle machine because
      it happens to be idle is how you become the reason someone else's job crawls.
      Charging one core per dispatch (`_spend`) makes a burst of allocations spread
      across hosts rather than all landing on whichever host measured best.
    * **That quarter is also a hard cap on our footprint.** A host already holding
      `25% x nproc` of our workers is skipped no matter how much CPU frees up.
    * **A fleet-wide ceiling** from `~/.flt-worker-limit` caps concurrent workers
      regardless of how much capacity exists. Checked first, because it is free
      and it short-circuits the ssh probe entirely.
    * **RAM is a VETO, not a weight.** A lean worker needs 10G (margin already
      included). A host with less than that free is skipped outright, however idle
      its CPUs are -- an OOM kills the elaboration outright, whereas CPU contention
      only makes it slower. Asymmetric consequences, asymmetric rule.

    Why measured rather than static: these are SHARED departmental machines. When
    seven were added to the pool, two of them were already carrying load ~100 from
    other tenants, and shadowcat had 1133G of RAM against a table that said 2048.
    A static weight describes how big a machine is; only a measurement describes
    how much of it is available to us.

    An unreachable host is excluded -- we cannot verify it has room, so we do not
    guess. If every host is vetoed the caller sees an exhausted pool and queues the
    task, which is the correct outcome: there is nowhere to put the work yet.

    Falls back to pool order if no measurement can be obtained at all; allocation
    must never fail because a probe did."""
    free = [n for n, status, _ in entries if status == candidate_state]
    if not free:
        return None

    # Global ceiling first: cheapest check, and it short-circuits the ssh probe.
    limit = _worker_limit()
    in_use = sum(1 for _, status, _ in entries if status == "claimed")
    if in_use >= limit:
        return None                           # at the ceiling: caller queues

    hosts = {h for h in (_host_of(n) for n in free) if h}
    if not hosts:
        return free[0]
    cap = _capacity(sorted(hosts))
    if not cap:
        return free[0]

    # OUR footprint on each host: the states that are RUNNING AN AGENT and so
    # actually consume CPU. `claimed` and `reclaiming` both do (a `reclaiming`
    # slot retires later but is elaborating right now).
    #
    # `ready` is deliberately EXCLUDED, reversing a 2026-07-28 rule that counted
    # it. Counting `ready` is self-defeating: a dispatch converts `ready` ->
    # `claimed`, which is quota-NEUTRAL, so a ready worktree was consuming the
    # very slot needed to claim it. Observed the same day: cyclops held 23
    # `ready` and 1 `claimed` against a quota of 24 and could dispatch NOTHING;
    # fleet-wide, 125 ready worktrees were permanently undispatchable until the
    # unrelated `claimed` count happened to fall. That is the opposite of the
    # intent -- the rule was added to stop machines sitting idle and instead
    # guaranteed it.
    #
    # `ready` costs disk (a seeded `.lake`) and no CPU. The quota is a CPU
    # share, so only running work belongs in it. `batched` is excluded for the
    # same reason: the agent has finished and nothing is elaborating.
    ours = {}
    for name, status, _ in entries:
        if status in ("claimed", "reclaiming"):
            h = _host_of(name)
            if h:
                ours[h] = ours.get(h, 0) + 1

    def rank(name):
        """Our REMAINING QUOTA on this host: `(25% - our usage) x cores`.

        (Deyao, 2026-07-26 — this replaces `min(free_cpu, quarter)`, which was
        broken in a way that idled seven machines.)

        The old weight ranked a host holding 23 of our workers exactly equal to
        one holding none, because `quarter` is a constant per host and
        `free_cpu` sat far above it almost everywhere. So every host with any
        headroom tied at exactly `quarter`; `max()` is stable on ties, so the
        first in pool order won EVERY dispatch. `_spend` was supposed to break
        that up, but it charges `free_cpu`, and while `free_cpu > quarter` the
        `min` clamps it away — charging a core changed the weight by nothing.
        The result was a few machines saturated and seven at zero utilisation.

        Ranking by REMAINING QUOTA fixes it structurally rather than by
        tie-breaking: placing a worker on a host lowers that host's weight by
        exactly one, so the next pick naturally goes elsewhere, and allocation
        self-levels toward equal fractions of each machine's quarter.

        `free_cpu` stays as a CAP, not the weight: we never want to pile onto a
        machine other tenants are already hammering, even if our own quota there
        is untouched. These are shared departmental boxes.
        """
        h = _host_of(name)
        c = cap.get(h) if h else None
        if not c or c["free_ram_g"] < RAM_PER_WORKER_G:
            return None                       # unreachable, unrouted, or RAM veto
        quarter = OUR_SHARE * c.get("total_cpu", 0)
        headroom = quarter - ours.get(h, 0)
        if headroom <= 0:
            return None                       # our share of this machine is spent
        return min(c["free_cpu"], headroom)

    viable = [(rank(n), n) for n in free]
    viable = [(r, n) for r, n in viable if r is not None]
    if not viable:
        return None                           # every host vetoed: queue instead
    # max() is stable on ties, so equal weight keeps the original pool order.
    best = max(viable, key=lambda rn: rn[0])[1]
    _spend(_host_of(best))
    return best


def allocate_worktree(pool_fh):
    """Under the caller's pool-file lock: find a free worktree, verify
    clean+ancestor, fast-forward it to main, mark claimed. Returns its
    path, or None if the pool is exhausted. Hard-raises on unexpected
    state."""
    # `<name> <status> [extra...]` — a SUSPENDED entry (Deyao, 2026-07-24)
    # carries the stopped agent's transcript id as a third field so its work
    # can be picked up later; it is never allocated, which is also how a
    # reduced worker count is enforced under memory pressure. Trailing
    # fields are preserved verbatim on rewrite.
    entries = []
    for line in pool_fh.read().splitlines():
        if not line.strip():
            continue
        parts = line.split()
        entries.append((parts[0], parts[1], parts[2:]))
    free_name = pick_free(entries)
    if free_name is None:
        return None
    worktree_path = next(
        (p for p in (f"{root}/{free_name}" for root in ROOTS)
         if os.path.isdir(p)), None)
    if worktree_path is None:
        raise RuntimeError(
            f"pool entry {free_name} resolves to no worktree directory "
            f"under any of {ROOTS}")

    status_out = git(["status", "--porcelain"], worktree_path)
    if status_out.returncode != 0:
        raise RuntimeError(
            f"git status failed in {worktree_path}: {status_out.stderr}")
    if status_out.stdout.strip():
        raise RuntimeError(
            f"worktree {free_name} is marked free in {POOL_FILE} but has "
            f"uncommitted changes:\n{status_out.stdout}")

    # Ancestor of MAIN (Deyao, 2026-07-26, RELEASE MODEL -- reverses the staging
    # rule below it). `main` is now the only branch anything is dispatched from,
    # and it moves only when the merger has built a batch green. So a finished
    # branch becomes an ancestor of main exactly when its work has been released.
    anc = git(["merge-base", "--is-ancestor", free_name, "main"], worktree_path)
    if anc.returncode != 0:
        raise RuntimeError(
            f"worktree {free_name}'s branch is marked free in {POOL_FILE} "
            "but is NOT an ancestor of main (diverged/unreleased commits) "
            "-- its work has not been through the merger yet; either it was "
            "never added to ~/.flt-merge-batch, or the merger has not cut a "
            "release containing it")

    # Advance to MAIN, the release (Deyao, 2026-07-26). This reverses the
    # staging rule, which had workers advance to a branch that accumulated
    # unbuilt work continuously.
    #
    # The phantom-dispatch worry that motivated the staging rule -- a worker
    # sent at a leaf that exists only on an unmerged branch, landing on a tree
    # where the declaration is absent -- is now handled by ORDERING instead of
    # by branch choice: work is queued when its leaf is not yet released, and
    # dispatched only after a release contains it. The queue, not the branch
    # pointer, is what absorbs the lag.
    #
    # What this buys is worth the wait: every worker starts from a tree that is
    # KNOWN TO COMPILE, with `.lake` artifacts seeded from the very build that
    # verified it (flt-release.py). Under the staging rule a worker could start
    # from a red it did not cause and could not see, and its `.lake` never
    # matched its source -- the inconsistent-olean trap that manufactures
    # phantom kernel errors and cost several agents a full cycle each.
    #
    # Always advance, never backwards (see split_base: pinning was reverted
    # because a backwards move invalidates `.lake` and forces a from-source
    # rebuild of the import cone on the agent's first query).
    ff = git(["merge", "--ff-only", "main"], worktree_path)
    if ff.returncode != 0:
        raise RuntimeError(
            f"ff-only advance of {free_name} to main failed: {ff.stderr}")

    new_lines = [
        " ".join([n, "claimed" if n == free_name else status] + extra)
        for n, status, extra in entries
    ]
    pool_fh.seek(0)
    pool_fh.write("\n".join(new_lines) + "\n")
    pool_fh.truncate()
    return worktree_path


def main():
    payload = json.load(sys.stdin)
    tool_input = payload.get("tool_input", {})
    prompt = tool_input.get("prompt", "")

    is_pop = SENTINEL in prompt
    is_direct = PLACEHOLDER in prompt

    # The staging worker is resolved BEFORE the pool lock is taken: it allocates
    # nothing, pops nothing, and is never queued, so it has no business
    # contending for the pool file. Substitute and allow.
    if STAGING_PLACEHOLDER in prompt:
        if not os.path.isdir(STAGING_WORKTREE):
            deny(f"{STAGING_PLACEHOLDER} was used but {STAGING_WORKTREE} does "
                 "not exist — create the staging worktree first "
                 "(`git worktree add /home/chend/flt-staging staging-worker`, "
                 "then symlink .lake into /scratch on its assigned host).")
        # NEVER TWO MERGERS. This check must live here, on the DIRECT path, not
        # only in the queue-pop branch: a direct dispatch resolves before the
        # pool lock and would otherwise skip the guard entirely. That is exactly
        # how two workers ended up in staging on 2026-07-27 — the orchestrator
        # wrongly concluded none was running and dispatched a second, which
        # merged a 23k-line relocation whose staged resolution was then swept
        # into the other worker's commit. They share one .lake; two builds in it
        # produce kernel errors that look like real defects.
        busy = staging_owner()
        if busy is not None:
            deny(f"a merge worker already holds {STAGING_WORKTREE} ({busy}) — "
                 f"NEVER run two. If you believe it is dead, confirm with "
                 f"`git reflog merger | head` (are the top entries recent?) and "
                 f"a live-process check, then delete {MERGE_CLAIM} to release "
                 f"the claim. Do not dispatch past this message.")
        tool_input["prompt"] = prompt.replace(
            STAGING_PLACEHOLDER, STAGING_WORKTREE)
        # Recorded in the inflight registry like any other dispatch, so the
        # ownership scan can see that staging has a live owner -- but with its
        # own kind, so it is never mistaken for a pool worktree to be freed.
        record_inflight(
            STAGING_WORKTREE, tool_input["prompt"], "staging", payload)
        emit(_with_capacity({
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "allow",
                "updatedInput": tool_input,
            }
        }))

    # ONE lock covering the WHOLE dispatch decision (fixed 2026-07-25 after
    # a wave handed FOUR agents the identical task). The queue used to be
    # read here, outside any lock, and written back inside the pool lock —
    # so concurrent {{FLT_QUEUE_POP}} spawns each read the same head, each
    # popped it, and each wrote back its own stale list: the pops were lost
    # updates. The pool file's flock is the fleet's existing mutual-exclusion
    # primitive, so widen it to cover the queue too — queue read, pop, and
    # write are now serialized with worktree allocation against every other
    # concurrently spawning agent.
    with open(POOL_FILE, "r+") as pool_fh:
        fcntl.flock(pool_fh, fcntl.LOCK_EX)
        queue = read_queue()

        def auto_queue(reason):
            # THE MERGE WORKER IS NEVER QUEUED. It allocates no pool worktree,
            # nothing in the fleet can progress past a full merge batch, and a
            # queued merger is a stalled fleet. It is resolved before this lock
            # is ever taken; reaching here means something upstream mangled the
            # placeholder, which is a defect, not a capacity problem.
            if STAGING_PLACEHOLDER in prompt:
                deny(f"refusing to queue a {STAGING_PLACEHOLDER} task — the "
                     f"merge worker is dispatched IMMEDIATELY and never waits "
                     f"in {QUEUE_FILE}. Spawn it directly with "
                     f"{STAGING_PLACEHOLDER} in the prompt.")
            queue.append(prompt)
            write_queue(queue)
            deny(f"{reason} — this task has been QUEUED (position "
                 f"{len(queue)} in {QUEUE_FILE}). Dispatch the queue head "
                 f"with an Agent spawn whose prompt is {SENTINEL} once there "
                 f"is capacity; hand-edit the file to reprioritize or drop.")

        if is_direct and not is_pop and queue:
            auto_queue(f"the task queue already has {len(queue)} pending "
                       f"item(s) (FIFO order)")

        if not is_pop and not is_direct and queue:
            deny(f"the task queue ({QUEUE_FILE}) has {len(queue)} pending "
                 f"item(s) — dispatch them first, in FIFO order, by spawning "
                 f"an agent whose prompt is the sentinel {SENTINEL} (the hook "
                 f"substitutes the queue head). To reprioritize or drop "
                 f"tasks, hand-edit the queue file.")

        if is_pop:
            if not queue:
                deny(f"the task queue ({QUEUE_FILE}) is empty — nothing to "
                     f"pop; dispatch directly with {PLACEHOLDER} in the "
                     f"prompt.")
            # THE MERGE WORKER NEVER WAITS IN LINE. If a staging task is
            # anywhere in the queue, it jumps FIFO and dispatches immediately:
            # it consumes NO pool worktree, and nothing else in the fleet can
            # make progress past a full merge batch anyway, so queueing it
            # behind ordinary work is always wrong.
            #
            # This is also the bug of 2026-07-27: the pre-lock staging check
            # fires only on the SPAWNED prompt, and a pop's prompt is just the
            # sentinel, so a QUEUED staging task was popped into an ordinary
            # pool worktree with {{FLT_STAGING}} never substituted. The merge
            # worker task was silently consumed, the agent got a numbered
            # worktree and a different task, and ~105 branches sat unmerged
            # for 25 minutes while the pool looked healthy.
            staging_idx = next(
                (i for i, t in enumerate(queue)
                 if STAGING_PLACEHOLDER in split_base(t)), None)
            if staging_idx is not None:
                task_body = split_base(queue[staging_idx])
                if not os.path.isdir(STAGING_WORKTREE):
                    deny(f"a queued task uses {STAGING_PLACEHOLDER} but "
                         f"{STAGING_WORKTREE} does not exist — it stays in "
                         f"{QUEUE_FILE}; create the staging worktree first.")
                busy = staging_owner()
                if busy is not None:
                    deny(f"a merge worker is already live in "
                         f"{STAGING_WORKTREE} ({busy}) — NEVER run two: "
                         f"they share one .lake and corrupt each other's "
                         f"build. The task stays in {QUEUE_FILE}; retry once "
                         f"that worker reports.")
                queue.pop(staging_idx)
                write_queue(queue)
                tool_input["prompt"] = task_body.replace(
                    STAGING_PLACEHOLDER, STAGING_WORKTREE)
                record_inflight(
                    STAGING_WORKTREE, tool_input["prompt"], "staging", payload)
                emit({
                    "hookSpecificOutput": {
                        "hookEventName": "PreToolUse",
                        "permissionDecision": "allow",
                        "updatedInput": tool_input,
                    }
                })

            task_body = split_base(queue[0])
            worktree_path = allocate_worktree(pool_fh)
            if worktree_path is None:
                deny("no free worktree available — the queued task stays in "
                     f"{QUEUE_FILE}; retry the {SENTINEL} dispatch after "
                     "freeing a worktree (merge + hand-edit the pool file).")
            queue.pop(0)
            write_queue(queue)
            tool_input["prompt"] = task_body.replace(
                PLACEHOLDER, worktree_path)
            record_inflight(
                worktree_path, tool_input["prompt"], "queue-pop", payload)
            emit(_with_capacity({
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "allow",
                    "updatedInput": tool_input,
                }
            }))

        if not is_direct:
            sys.exit(0)  # non-fleet agent, queue empty: pass through

        worktree_path = allocate_worktree(pool_fh)
        if worktree_path is None:
            auto_queue("no free worktree available")
        tool_input["prompt"] = tool_input["prompt"].replace(
            PLACEHOLDER, worktree_path)
        record_inflight(
            worktree_path, tool_input["prompt"], "direct", payload)
        emit(_with_capacity({
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "allow",
                "updatedInput": tool_input,
            }
        }))


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception:
        traceback.print_exc(file=sys.stderr)
        print(
            "\nworktree-pool-hook: HARD CRASH -- pool state is unexpected; "
            "this needs orchestrator attention, not an automatic retry.",
            file=sys.stderr,
        )
        sys.exit(2)

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

Worktree allocation is unchanged: find a `free` entry in
~/.flt-worktree-pool, check it is git-clean and its branch is an
ancestor of main, fast-forward it to main (--ff-only), mark it
`claimed`. A worktree marked free but dirty/diverged is NOT a normal
condition and is NOT auto-corrected — hard crash (traceback, exit 2,
tool call blocked): something beyond allocation went wrong.

Freeing a worktree after its work is merged, and pushing to the task
queue, are both the orchestrator hand-editing the respective text
file. No scripts on that side.

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


def _host_of(name):
    """Which machine serves this worktree, or None if unrouted."""
    try:
        with open(os.path.join(HOST_DIR, name), encoding="utf-8") as fh:
            return fh.read().strip() or None
    except OSError:
        return None


def _cores():
    """host -> core count, from CORES_FILE (`<host> <n>` per line).

    Missing or malformed file means every host weighs 1, which degrades to
    even-by-count balancing. Allocation must never fail over this."""
    out = {}
    try:
        with open(CORES_FILE, encoding="utf-8") as fh:
            for line in fh:
                parts = line.split()
                if len(parts) >= 2 and parts[1].isdigit() and int(parts[1]) > 0:
                    out[parts[0]] = int(parts[1])
    except OSError:
        pass
    return out


def pick_free(entries):
    """Choose which free worktree to hand out: the one on the machine that is
    least loaded RELATIVE TO ITS CORE COUNT (Deyao, 2026-07-25).

    Why not just take the first free entry, as this did before: the pool is
    ordered by worktree number and the numbers are grouped by machine, so
    first-fit drains one machine before touching the next. Measured mid-run on
    2026-07-25: dazzler held 28 claimed slots and gambit 8, on identical 96-core
    machines, while nightcrawler and nocturne (128 cores each) sat at 27. One
    machine was oversubscribed ~3.5x relative to another with the same capacity.

    That matters because elaboration is single-threaded — one core per file — so
    a machine's useful parallelism IS its core count. Piling workers past it
    lengthens every verification on that host without adding throughput, while
    cores idle elsewhere.

    Ranks hosts by claimed/cores ascending, so the emptiest-per-core machine is
    served first; ties break by pool order, keeping allocation deterministic.
    Free worktrees whose host is unknown (no routing-table entry) sort last —
    they are still allocatable, just not preferred, since we cannot say what
    they would cost."""
    free = [n for n, status, _ in entries if status == "free"]
    if not free:
        return None

    cores = _cores()
    # A host present in the routing table but absent from CORES_FILE (a machine
    # added without re-measuring) must not be starved: weighting it 1 would make
    # its ratio ~100x everyone else's after a single claim, so it would never be
    # picked again. Assume it looks like the machines we HAVE measured.
    default_cores = round(sum(cores.values()) / len(cores)) if cores else 1

    claimed = {}
    for name, status, _ in entries:
        if status == "claimed":
            h = _host_of(name)
            if h:
                claimed[h] = claimed.get(h, 0) + 1

    def load(name):
        h = _host_of(name)
        if h is None:
            return (1, 0.0)          # unrouted: allocatable, but last resort
        return (0, claimed.get(h, 0) / cores.get(h, default_cores))

    # min() is stable, so equal load keeps the original pool order.
    return min(free, key=load)


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

    anc = git(["merge-base", "--is-ancestor", free_name, "main"], worktree_path)
    if anc.returncode != 0:
        raise RuntimeError(
            f"worktree {free_name}'s branch is marked free in {POOL_FILE} "
            "but is NOT an ancestor of main (diverged/unmerged commits) "
            "-- integration was likely skipped for this branch")

    # Always advance to main, never backwards (see split_base: pinning was
    # reverted because a backwards move invalidates `.lake` and forces a
    # from-source rebuild of the import cone on the agent's first query).
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
            emit({
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "allow",
                    "updatedInput": tool_input,
                }
            })

        if not is_direct:
            sys.exit(0)  # non-fleet agent, queue empty: pass through

        worktree_path = allocate_worktree(pool_fh)
        if worktree_path is None:
            auto_queue("no free worktree available")
        tool_input["prompt"] = tool_input["prompt"].replace(
            PLACEHOLDER, worktree_path)
        record_inflight(
            worktree_path, tool_input["prompt"], "direct", payload)
        emit({
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "allow",
                "updatedInput": tool_input,
            }
        })


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

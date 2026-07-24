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

Worktree allocation is unchanged: find a `free` entry in
~/.flt-worktree-pool, check it is git-clean and its branch is an
ancestor of main, fast-forward it to main (--ff-only), mark it
`claimed`. A worktree marked free but dirty/diverged is NOT a normal
condition and is NOT auto-corrected — hard crash (traceback, exit 2,
tool call blocked): something beyond allocation went wrong.

Freeing a worktree after its work is merged, and pushing to the task
queue, are both the orchestrator hand-editing the respective text
file. No scripts on that side.
"""

import fcntl
import json
import os
import subprocess
import sys
import traceback

POOL_FILE = "/home/chend/.flt-worktree-pool"
QUEUE_FILE = "/home/chend/.flt-task-queue"
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
    """A queued task may pin the commit it was WRITTEN AGAINST with a
    leading `#base: <sha>` line (Deyao, 2026-07-24). Task prompts cite
    exact declaration line numbers, so advancing the worktree to a much
    newer main invalidates them; the hook advances to the pinned commit
    instead. Returns (base_or_None, prompt_without_the_header)."""
    lines = task.split("\n")
    if not lines or not lines[0].startswith(BASE_PREFIX):
        raise RuntimeError(
            f"queued task has no leading `{BASE_PREFIX} <sha>` line. Every "
            "task must pin the commit it was written against; an unpinned "
            "task would be dispatched against an arbitrary tree. Fix the "
            f"queue entry by hand.\nTask head: {task[:200]!r}")
    return lines[0][len(BASE_PREFIX):].strip(), "\n".join(lines[1:]).lstrip("\n")


def allocate_worktree(pool_fh, target="main"):
    """Under the caller's pool-file lock: find a free worktree, verify
    clean+ancestor, move it EXACTLY onto `target` (the task's pinned base
    commit) in either direction, mark claimed. Returns its path, or None
    if the pool is exhausted. Hard-raises on unexpected state."""
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
    free_name = next((n for n, status, _ in entries if status == "free"), None)
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

    rev = git(["rev-parse", "--verify", f"{target}^{{commit}}"], worktree_path)
    if rev.returncode != 0:
        raise RuntimeError(
            f"task pins base {target}, which does not resolve in "
            f"{worktree_path}: {rev.stderr}")
    # A free worktree must be strictly BEHIND the pin: it was last advanced
    # to some main, its work was merged, and the pin is a commit of main.
    # A branch that already contains the pin means the pool/queue state is
    # not what it should be -- crash and let the orchestrator investigate
    # rather than silently dispatching against the wrong tree.
    # Move the branch EXACTLY onto the pin, forwards or backwards (Deyao,
    # 2026-07-24). Backwards is routine, not an error: pins age relative to
    # main while a task waits in the queue, so a worktree freed after a
    # newer-pinned task will be ahead of an older-pinned one. Resetting
    # loses nothing -- the branch is verified above to be an ancestor of
    # main, so its commits are already in main. `.lake` is content-hash
    # traced, so a backwards move is seen as "these files changed" and only
    # the differing modules re-elaborate.
    head_sha = git(["rev-parse", "HEAD"], worktree_path).stdout.strip()
    if head_sha != rev.stdout.strip():
        reset = git(["reset", "--hard", target], worktree_path)
        if reset.returncode != 0:
            raise RuntimeError(
                f"resetting {free_name} onto its pinned base {target} "
                f"failed: {reset.stderr}")

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

    queue = read_queue()

    def auto_queue(reason):
        # Stamp the commit this task was written against, so the eventual
        # pop advances the worktree to THAT tree, not to a newer main.
        head = git(["rev-parse", "main"], HOME + "/flt-lean")
        stamped = prompt
        if head.returncode == 0 and not prompt.startswith(BASE_PREFIX):
            stamped = f"{BASE_PREFIX} {head.stdout.strip()}\n{prompt}"
        queue.append(stamped)
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
             f"substitutes the queue head). To reprioritize or drop tasks, "
             f"hand-edit the queue file.")

    if is_pop:
        if not queue:
            deny(f"the task queue ({QUEUE_FILE}) is empty — nothing to pop; "
                 f"dispatch directly with {PLACEHOLDER} in the prompt.")
        base, task_body = split_base(queue[0])
        with open(POOL_FILE, "r+") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            worktree_path = allocate_worktree(f, base or "main")
            if worktree_path is None:
                deny("no free worktree available — the queued task stays in "
                     f"{QUEUE_FILE}; retry the {SENTINEL} dispatch after "
                     "freeing a worktree (merge + hand-edit the pool file).")
            queue.pop(0)
            write_queue(queue)
        tool_input["prompt"] = task_body.replace(PLACEHOLDER, worktree_path)
        emit({
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "allow",
                "updatedInput": tool_input,
            }
        })

    if not is_direct:
        sys.exit(0)  # non-fleet agent, queue empty: pass through unchanged

    with open(POOL_FILE, "r+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        worktree_path = allocate_worktree(f)
        if worktree_path is None:
            auto_queue("no free worktree available")
    tool_input["prompt"] = tool_input["prompt"].replace(
        PLACEHOLDER, worktree_path)
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

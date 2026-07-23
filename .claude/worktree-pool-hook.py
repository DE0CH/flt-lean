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
- Queue nonempty + spawn prompt is NOT the sentinel -> DENY, reminding
  the orchestrator to dispatch queued items first (FIFO order).
- Sentinel + empty queue -> DENY (nothing to pop).
- No free worktree -> DENY; for a direct {{FLT_WORKTREE}} dispatch the
  message says to append the task to ~/.flt-task-queue instead.
  A queue pop with no free worktree leaves the queue untouched.

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
import subprocess
import sys
import traceback

POOL_FILE = "/home/chend/.flt-worktree-pool"
QUEUE_FILE = "/home/chend/.flt-task-queue"
PLACEHOLDER = "{{FLT_WORKTREE}}"
SENTINEL = "{{FLT_QUEUE_POP}}"
DELIMITER = "=== TASK ==="
HOME = "/home/chend"


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


def allocate_worktree(pool_fh):
    """Under the caller's pool-file lock: find a free worktree, verify
    clean+ancestor, ff to main, mark claimed. Returns its path, or None
    if the pool is exhausted. Hard-raises on unexpected state."""
    entries = [line.split() for line in pool_fh.read().splitlines() if line.strip()]
    free_name = next((n for n, status in entries if status == "free"), None)
    if free_name is None:
        return None
    worktree_path = f"{HOME}/{free_name}"

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

    ff = git(["merge", "--ff-only", "main"], worktree_path)
    if ff.returncode != 0:
        raise RuntimeError(
            f"ff-only advance of {free_name} to main failed: {ff.stderr}")

    new_lines = [
        f"{n} claimed" if n == free_name else f"{n} {status}"
        for n, status in entries
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

    if not is_pop and queue:
        deny(f"the task queue ({QUEUE_FILE}) has {len(queue)} pending "
             f"item(s) — dispatch them first, in FIFO order, by spawning "
             f"an agent whose prompt is the sentinel {SENTINEL} (the hook "
             f"substitutes the queue head). To reprioritize or drop tasks, "
             f"hand-edit the queue file.")

    if is_pop:
        if not queue:
            deny(f"the task queue ({QUEUE_FILE}) is empty — nothing to pop; "
                 f"dispatch directly with {PLACEHOLDER} in the prompt.")
        with open(POOL_FILE, "r+") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            worktree_path = allocate_worktree(f)
            if worktree_path is None:
                deny("no free worktree available — the queued task stays in "
                     f"{QUEUE_FILE}; retry the {SENTINEL} dispatch after "
                     "freeing a worktree (merge + hand-edit the pool file).")
            task = queue.pop(0)
            write_queue(queue)
        tool_input["prompt"] = task.replace(PLACEHOLDER, worktree_path)
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
            deny("no free worktree available — PUSH THIS TASK TO THE QUEUE "
                 f"instead: append the full prompt to {QUEUE_FILE} (tasks "
                 f"separated by a line `{DELIMITER}`), then dispatch it "
                 f"later with the {SENTINEL} sentinel once a worktree "
                 "frees up.")
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

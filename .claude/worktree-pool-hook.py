#!/usr/bin/env python3
"""PreToolUse hook on the Agent tool (Deyao, 2026-07-23): allocates a
worktree from the fixed 13-worktree pool for math dispatches.

Only acts when the Agent prompt contains the literal placeholder
{{FLT_WORKTREE}} (so Explore/research/other agents pass through
unchanged). When present: find a `free` entry in ~/.flt-worktree-pool,
verify it is clean and its branch is an ancestor of main, fast-forward
it to main, mark it `claimed`, and substitute the real worktree path
for the placeholder in the prompt.

No free worktree is a normal, expected condition -> deny with a plain
reason, tool call blocked, no crash.

An allocated worktree that is dirty or not an ancestor of main is NOT
a normal condition -- it means something beyond allocation has gone
wrong and needs attention, not an automatic fallback to a different
worktree. This hard-crashes: full traceback + message to stderr, exit
2 (blocks the tool call).

Freeing a worktree after its work is merged into main has no reliable
hook trigger (there is no event for "the orchestrator finished
merging into main" -- git merge is just a Bash call among many). The
orchestrator hand-edits ~/.flt-worktree-pool back to `free` as part of
the integration step; no script for that side.
"""

import fcntl
import json
import subprocess
import sys
import traceback

POOL_FILE = "/home/chend/.flt-worktree-pool"
PLACEHOLDER = "{{FLT_WORKTREE}}"
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


def allow_unchanged():
    sys.exit(0)


def allow_with_worktree(tool_input, worktree_path):
    tool_input["prompt"] = tool_input["prompt"].replace(PLACEHOLDER, worktree_path)
    emit({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "allow",
            "updatedInput": tool_input,
        }
    })


def main():
    payload = json.load(sys.stdin)
    tool_input = payload.get("tool_input", {})
    prompt = tool_input.get("prompt", "")

    if PLACEHOLDER not in prompt:
        allow_unchanged()

    with open(POOL_FILE, "r+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        entries = [line.split() for line in f.read().splitlines() if line.strip()]

        free_name = next((n for n, status in entries if status == "free"), None)
        if free_name is None:
            deny("no free worktree available")

        worktree_path = f"{HOME}/{free_name}"

        # -- hard-crash guard: allocated worktree must be clean and an
        # ancestor of main. No fallback, no silent re-pick.
        status_out = git(["status", "--porcelain"], worktree_path)
        if status_out.returncode != 0:
            raise RuntimeError(
                f"git status failed in {worktree_path}: {status_out.stderr}"
            )
        if status_out.stdout.strip():
            raise RuntimeError(
                f"worktree {free_name} is marked free in {POOL_FILE} but has "
                f"uncommitted changes:\n{status_out.stdout}"
            )

        anc = git(["merge-base", "--is-ancestor", free_name, "main"], worktree_path)
        if anc.returncode != 0:
            raise RuntimeError(
                f"worktree {free_name}'s branch is marked free in {POOL_FILE} "
                "but is NOT an ancestor of main (diverged/unmerged commits) "
                "-- integration was likely skipped for this branch"
            )

        ff = git(["merge", "--ff-only", "main"], worktree_path)
        if ff.returncode != 0:
            raise RuntimeError(
                f"ff-only advance of {free_name} to main failed: {ff.stderr}"
            )

        new_lines = [
            f"{n} claimed" if n == free_name else f"{n} {status}"
            for n, status in entries
        ]
        f.seek(0)
        f.write("\n".join(new_lines) + "\n")
        f.truncate()

    allow_with_worktree(tool_input, worktree_path)


if __name__ == "__main__":
    try:
        main()
    except Exception:
        traceback.print_exc(file=sys.stderr)
        print(
            "\nworktree-pool-hook: HARD CRASH -- pool state is unexpected; "
            "this needs orchestrator attention, not an automatic retry.",
            file=sys.stderr,
        )
        sys.exit(2)

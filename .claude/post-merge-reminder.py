#!/usr/bin/env python3
"""PostToolUse hook on Bash (Deyao, 2026-07-23): after any Bash call
whose command mentions `git merge`, inject a reminder prompt about the
integration-time checks. Deliberately matches WIDELY (any `git merge`
anywhere in the command) and lets the model distinguish what actually
happened and which actions apply -- the hook does no cwd/branch
detection of its own.

GRACEFUL (harness-called, Deyao's caller policy): any failure exits
silently; never blocks anything.
"""

import json
import sys


PROMPT = (
    "It looks like this command ran `git merge`. If this was an "
    "INTEGRATION merge (an agent/work branch merged into main): this is "
    "the moment the integration checks run -- (1) run `python3 "
    "free-floating.py` at the repo root (the floating check pays its "
    "cone rebuild now, at integration cadence) and resolve or assign any "
    "floating declarations top-down; (2) mark the agent's worktree back "
    "to `free` in ~/.flt-worktree-pool; (3) keep progress-entries.json / "
    "PROGRESS.md current for what the merge changed. If this was NOT an "
    "integration into main (e.g. a --ff-only worktree advance, or some "
    "unrelated merge), ignore this reminder."
)


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name") != "Bash":
        return 0
    command = (payload.get("tool_input") or {}).get("command", "")
    if "git merge" not in command:
        return 0
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": PROMPT,
        }
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())

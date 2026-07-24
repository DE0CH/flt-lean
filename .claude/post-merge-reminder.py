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
    "the moment the integration checks run -- (1) mark the agent's "
    "worktree back to `free` in ~/.flt-worktree-pool; (2) if the "
    "just-finished agent was the BOOKKEEPING agent (the combined "
    "free-floating check + progress-entries.json/PROGRESS.md "
    "regeneration cycle), remember to dispatch/queue a NEW bookkeeping "
    "task -- appended to the END of ~/.flt-task-queue like every other "
    "task; (3) REVIEW THE QUEUE against what this merge just changed "
    "(Deyao, 2026-07-24): the merged report is new information, so walk "
    "~/.flt-task-queue and UPDATE any task whose target moved, was "
    "renamed, was restated, or whose recorded line numbers/plan are now "
    "stale, and DELETE any task the merge made obsolete (target already "
    "proven, leaf withdrawn, decomposition superseded). Each queued task "
    "carries a leading `#base: <sha>` line pinning the commit it was "
    "written against -- the pop hook advances the worktree to THAT commit "
    "instead of main, so line references stay valid. **If you edit a "
    "task, you must also advance its `#base:` to the current main "
    "commit** (`git rev-parse main`), since the edit is written against "
    "the new tree. Leave untouched tasks pinned where they are. If this "
    "was NOT an integration into main (e.g. a --ff-only worktree advance, "
    "or some unrelated merge), ignore this reminder."
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

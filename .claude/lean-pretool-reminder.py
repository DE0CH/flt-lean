#!/usr/bin/env python3
"""PreToolUse hook (Deyao, 2026-07-22): before every lean-lsp MCP call,
remind Claude of the no-floating discipline at the have/sorry level.

Non-blocking: the tool call always proceeds (permissionDecision
"allow"); the reminder reaches Claude via additionalContext.
"""

import json
import sys

REMINDER = (
    "Before calling Lean, please check that sorry is only used in place "
    "of a proof (never a proposition) and that every have/let is "
    "comsumed. You may not define a have that is not used anywhere."
)


def main() -> int:
    try:
        json.load(sys.stdin)  # hook input is unused; consume it anyway
    except Exception:
        pass
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "allow",
            "additionalContext": REMINDER,
        }
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())

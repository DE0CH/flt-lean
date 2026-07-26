#!/usr/bin/env python3
"""PostToolUse hook on Bash: if the orchestrator ran `git merge`, tell it not to.

Under the RELEASE MODEL (Deyao, 2026-07-26) the orchestrator does not merge at
all. This hook used to carry a long integration checklist -- merge into staging,
free the worktree, review the queue, promote, push. Every one of those steps
moved to the merger or to `flt-cycle.py`. What is left is a GUARD: an
orchestrator running `git merge` is doing the merger's job by hand, which is
precisely the drift this model exists to eliminate.

GRACEFUL (harness-called, Deyao's caller policy): any failure exits silently,
never blocks anything.
"""

import json
import re
import sys

BATCH = "/home/chend/.flt-merge-batch"

PROMPT = (
    "RELEASE MODEL: the orchestrator does not merge.\n\n"
    "If that was a work branch, undo it (`git merge --abort`, or reset back to "
    "the release) and instead run\n"
    "    python3 flt-cycle.py done <worktree>\n"
    "which records it in the merge batch. The MERGER claims the batch, resolves "
    "conflicts, drives the build green, and moves `main` to the sha it built. "
    "That is the only path by which anything reaches `main`, and it is the one "
    "invariant the whole fleet rests on.\n\n"
    "Your two jobs are: run `flt-cycle.py`, and hand-edit ~/.flt-task-queue -- "
    "adding tasks when an agent finishes, correcting them when a release lands. "
    "Nothing else.\n\n"
    "If NO merger is currently running, start one now: spawn an agent whose "
    "prompt contains the {{FLT_STAGING}} sentinel. A stalled merger is the one "
    "condition that halts the entire fleet, because nothing else can produce a "
    "release."
)


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return
    cmd = (payload.get("tool_input") or {}).get("command") or ""
    if not re.search(r"\bgit\s+(-C\s+\S+\s+)?merge\b", cmd):
        return
    # `merge-base` is a query, not a merge; `--ff-only` is how flt-cycle.py
    # hands out a release and how the merger starts a cycle. Both legitimate.
    if "merge-base" in cmd or "--ff-only" in cmd:
        return

    try:
        n = sum(1 for ln in open(BATCH) if ln.strip())
        depth = f"\n\nMerge batch currently holds {n} worktree(s)."
    except OSError:
        depth = ""

    print(PROMPT + depth, file=sys.stderr)


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass
    sys.exit(0)

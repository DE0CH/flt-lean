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
    "the moment the integration checks run -- (1) CHECK THE WORKTREE'S "
    "CURRENT POOL STATE FIRST, because where it goes next depends on it "
    "(Deyao, 2026-07-25). If it reads `claimed`, mark it `free`. If it reads "
    "`reclaiming` -- meaning 'claimed, but retire this slot when its task "
    "finishes' -- mark it `retired`, NOT `free` and NOT `suspended`: its "
    "agent exited cleanly and you just merged its work, so the worktree is "
    "clean and there is NO transcript state to resume; `retired` is exactly "
    "that case, and such a slot can be promoted straight back to `free` the "
    "moment capacity allows. Reserve `suspended <agent-id>` for the opposite "
    "situation -- a worktree left DIRTY by an agent stopped mid-task, whose "
    "recorded transcript id is what lets the work be resumed from the "
    "middle; never mark a clean, cleanly-exited worktree `suspended`, since "
    "that implies work worth resuming when there is none. `reclaiming` "
    "exists to drain the fleet from 62 workers to ~30, because the user "
    "slice is CPU-quota-capped at 24 cores (cpu.max 2400000/100000) and is "
    "throttled in ~76% of scheduling periods, so workers past that quota "
    "lengthen every verification instead of adding throughput. In every "
    "case REMOVE ITS LINE "
    "FROM ~/.flt-inflight.jsonl (Deyao, 2026-07-25): the dispatch hook "
    "appends one JSON record per dispatch (worktree, kind, dispatched_at, "
    "the bold `targets` the task named, and the full prompt); that file is "
    "the registry of what is being worked on RIGHT NOW, and it is only "
    "trustworthy if you delete the finished worktree's record here. Deleting "
    "it is also the moment to re-read the remaining records, because -- "
    "see (3) -- the merge you just made may have proven a leaf some OTHER "
    "agent is still working on; (2) if the "
    "just-finished agent was the BOOKKEEPING agent (the combined "
    "free-floating check + progress-entries.json/PROGRESS.md "
    "regeneration cycle), remember to dispatch/queue a NEW bookkeeping "
    "task -- appended to the END of ~/.flt-task-queue like every other "
    "task; (3) REVIEW THE QUEUE against what this merge just changed "
    "(Deyao, 2026-07-24): the merged report is new information, so walk "
    "~/.flt-task-queue and UPDATE any task whose target moved, was "
    "renamed, was restated, or whose recorded line numbers/plan are now "
    "stale, and DELETE any task the merge made obsolete (target already "
    "proven, leaf withdrawn, decomposition superseded). Worktrees always "
    "fast-forward to main at dispatch (pinning was reverted 2026-07-25 -- "
    "it forced from-source rebuilds), so a task whose recorded line "
    "numbers have drifted should be fixed by naming the target, not by "
    "pinning: agents locate leaves by name anyway; (4) CHECK "
    "FOR STARVATION (Deyao, 2026-07-24): if ~/.flt-task-queue is NON-EMPTY "
    "while ~/.flt-worktree-pool still has `free` slots, the fleet is "
    "finishing work faster than the orchestrator can merge and re-dispatch "
    "-- fill every free slot now, and EMAIL Deyao that integration is the "
    "bottleneck (reuse claude_refill.send_email with a [flt-fleet] subject "
    "and latch=None). Suspended slots do not count as free. If this "
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

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
    "fast-forward to STAGING at dispatch (pinning was reverted 2026-07-25 -- "
    "it forced from-source rebuilds), so a task whose recorded line "
    "numbers have drifted should be fixed by naming the target, not by "
    "pinning: agents locate leaves by name anyway; "
    "(3b) **DISPATCH THE NEW SORRIES THIS MERGE JUST INTRODUCED** (Deyao, "
    "2026-07-25). Almost every completion adds leaves: an agent proves its "
    "target over a finer cut and leaves 1-5 new ones behind. Those are "
    "UNOWNED the instant they land, and the loop invariant is that every "
    "sorry has an owner at all times. So right now: scan the merged file(s) "
    "for DIRECT sorries (comment-stripped, attributed by walking BACKWARDS "
    "to the nearest declaration header -- forwards mis-attributes), diff "
    "that against the agent's reported leaf list, and for each new one "
    "EITHER spawn an agent with `{{FLT_WORKTREE}}` in the prompt OR append a "
    "task to ~/.flt-task-queue (separated by a line reading exactly "
    "`=== TASK ===`). Queue it rather than dropping it when the pool is "
    "full -- the hook auto-queues a denied dispatch anyway. Resolve "
    "ownership with `python3 flt-owner.py <leaf-name>`, NEVER by grepping "
    "whole prompts: task prompts deliberately name sibling leaves under "
    "'do not touch these', so a whole-prompt grep reports phantom owners "
    "and an unowned leaf looks covered. That exact false positive left 67 "
    "of 92 sorries unowned on 2026-07-25 while the orchestrator believed "
    "the frontier was saturated; (4) CHECK "
    "FOR STARVATION (Deyao, 2026-07-24): if ~/.flt-task-queue is NON-EMPTY "
    "while ~/.flt-worktree-pool still has `free` slots, the fleet is "
    "finishing work faster than the orchestrator can merge and re-dispatch "
    "-- fill every free slot now, and EMAIL Deyao that integration is the "
    "bottleneck (reuse claude_refill.send_email with a [flt-fleet] subject "
    "and latch=None). Suspended slots do not count as free; (4b) **MERGES GO "
    "TO `staging`, NOT `main`** (Deyao, 2026-07-25). Two branches that diverge "
    "and rejoin: `staging` ACCUMULATES -- you merge worker branches into it and "
    "NEVER build, since a full cone build costs hours and would make integration "
    "the bottleneck -- while `main` POINTS AT THE LAST GREEN BUILD and NOTHING "
    "BUT THE STAGING WORKER EVER MOVES IT, only ever to a sha it has actually "
    "built. So resolve conflicts here with your best effort and let the compiler "
    "catch downstream what only a compiler can. When the worker has promoted "
    "(`git rev-list --count staging..main` non-zero), run `python3 flt-promote.py` "
    "to merge main BACK into staging: agents fast-forward to staging, so without "
    "it all ~90 of them keep inheriting a red that has already been repaired. "
    "Workers fast-forward to `staging` at dispatch, NOT main -- a leaf a "
    "completion just created exists only on staging, so dispatching against main "
    "would send an agent to a tree where its target does not exist; (5) **`git push`** "
    "(Deyao, 2026-07-24, re-issued 2026-07-25 after the orchestrator drifted "
    "off it again). Push at the END OF EVERY INTEGRATION WAVE -- not once a "
    "session, not when convenient. An unpushed merge exists on exactly one "
    "disk: the branch refs live in this repo's object store, `/scratch` is "
    "machine-local and NOT backed up, and every worktree fast-forwards from "
    "staging at dispatch, so unpushed work is both unreplicated AND invisible to "
    "the next agent allocated. A failing gate is never a reason to hold a "
    "push -- fix forward, push anyway; the sorry gate is EXPECTED to fail "
    "during development. If this "
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

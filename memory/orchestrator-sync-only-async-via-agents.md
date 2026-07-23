---
name: orchestrator-sync-only-async-via-agents
description: "Deyao 2026-07-23 — the orchestrator runs everything SYNCHRONOUSLY; background/async commands are banned (they were a source of bugs). The only permitted async is dispatching a task queue to a subagent, which itself runs its commands synchronously."
metadata:
  node_type: memory
  type: feedback
---

Deyao (2026-07-23): "i want you to run things synchronously. async had
been a source of bugs. remember that. the only way to run async is to
dispatch a task queue to an agent, and the agent runs commands
synchronously. for example, you can dispatch the floating check + sorry
count + regenerate progress.md to a subagent, and then merge its branch
into main later." Followed immediately by: "examine your background
commands and cancel all of them."

**Why:** Background Bash tasks from the driver session caused real bugs
this session: queued census clients each captured stale source text at
queue-entry time (a committed PROGRESS.md reflecting three-merges-old
state), lock-queue starvation timed out checks that then needed
reruns, and concurrent background jobs raced each other on shared
files (progress-entries.json interleaving risk). A subagent running
its queue synchronously has none of these: one worker, one worktree,
one ordered sequence, results integrated atomically via a git merge.

**How to apply:** Never pass run_in_background to Bash. Long-running
work the driver shouldn't block on goes to a SUBAGENT (whose prompt is
the task queue, run strictly in order); integrate its branch when its
completion notification arrives. The standing example: the
integration-bookkeeping bundle (floating check + sorry count +
PROGRESS.md regeneration) is dispatched as one subagent working in a
pool worktree, and the orchestrator merges its branch into main later.
This NARROWS the RESPONSIVENESS clause in [[flt-orchestrator-role]]:
"slow work runs as a background task or inside an agent" becomes
"slow work runs inside an agent" — background tasks are no longer an
option.

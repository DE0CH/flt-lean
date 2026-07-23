---
name: subagent-dispatch-suspended-until-told
description: "Deyao 2026-07-23 — subagent dispatch is fully suspended, blanket, not scoped by task type, until Deyao explicitly says to use subagents again"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-23T05:04:18.682Z
---

Deyao (2026-07-23): stopped 6 subagents dispatched for a keep-list audit
task and said "do not launch subagents. did you forget." When I first
recorded this as "the math-proving dispatch authorization doesn't cover
other task types," Deyao corrected that too: "no that's not the reason,
i stopped you from using subagents and said until i tell you to use
subagents again."

**Why:** This is a blanket pause, not a task-type distinction. It does
not matter whether the task is the math-proving loop, an audit, a
mechanical sweep, or anything else — no subagent dispatch of any kind
until Deyao explicitly re-authorizes it. Deyao, immediately after: "no i
don't want to use fleet, fleet is buggy from experience" — the
[[flt-fleet-13-worktree-protocol]] mechanism itself is under active
distrust right now (this session's own incident — killed agents left
worktrees dirty, needing manual cleanup — is fresh evidence for that),
not just paused for pacing reasons.

**How to apply:** Do not dispatch subagents for ANY task right now,
regardless of whether it superficially resembles the math-proving fleet
loop [[flt-fleet-13-worktree-protocol]] was written for. Wait for an
explicit "use subagents again" (or equivalent) from Deyao before
dispatching anything. Related: [[flt-orchestrator-role]] (the dispatch
gate there needs the same correction — its "LIFTED" note is not a
standing green light independent of this pause).

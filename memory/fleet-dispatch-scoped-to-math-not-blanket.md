---
name: fleet-dispatch-scoped-to-math-not-blanket
description: "Deyao 2026-07-23 — the 13-worktree fleet dispatch protocol authorizes subagent dispatch for the MATH-PROVING loop specifically; it is not blanket permission to dispatch subagents for other tasks (audits, investigations, etc.) just because they reuse the same {{FLT_WORKTREE}} pool mechanism"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-23T05:00:43.248Z
---

Deyao (2026-07-23): after I dispatched 6 subagents (using the sanctioned
`{{FLT_WORKTREE}}` pool-hook mechanism) to audit `free-floating-keep.json`
entries via delete-and-recompile testing, Deyao stopped all 6 and said:
"do not launch subagents. did you forget."

**Why:** [[flt-fleet-13-worktree-protocol]] lifted the dispatch-suspension
gate for a SPECIFIC purpose — the math-proving loop over the 13-worktree
pool. Using the same mechanism (the placeholder, the pool file) for a
DIFFERENT kind of task (investigation/verification work, not proving a
sorry) is not covered by that authorization, even though it reuses the
same plumbing. The standing default — ask before dispatching — still
applies to anything outside the specific math-loop use case.

**How to apply:** Before dispatching any subagent, ask: is this the
math-proving fleet loop specifically (claim a worktree, prove/decompose
a sorry, merge, free the worktree)? If yes, dispatch is live per the
protocol. If it's anything else — audits, investigations, mechanical
sweeps, verification tasks — check first, even if the task would
naturally reuse the same worktree/pool infrastructure. Related:
[[flt-orchestrator-role]], [[why-question-is-not-consent]].

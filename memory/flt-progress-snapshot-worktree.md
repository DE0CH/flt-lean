---
name: flt-progress-snapshot-worktree
description: "Deyao 2026-07-22 — regenerate PROGRESS.md from a consistent COMMITTED state via a secondary git worktree, regularly (on agent completions/milestones), since the live worktree never settles under a fleet"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e68e4f89-102e-4f9f-8119-8fd03437ed31
  modified: 2026-07-22T16:37:21.415Z
---

Deyao (2026-07-22): "the whole thing is git tracked, meaning that you can find a consistent state and then generate progress.md and deliver the update to me in a timely manner … because you have a fleet all working, it's almost impossible to find a state where the whole repo is in a clean state, so you need to do that regularly when something changes (e.g. agent finishes work, reaches a milestone)."

**Why:** With parallel agents the live worktree is permanently mid-edit; the daemon/generator correctly refuse degraded states, so tree updates would starve. Committed states ARE consistent by construction (only verified work is committed).

**How to apply:** Maintain a secondary git worktree of the repo pinned to origin/main (or HEAD), with its own .lake build state (seeded by copying the main repo's caches once). On each integration point (agent completion, milestone commit): advance the snapshot worktree to the latest commit, incremental `lake build` there, run progress-tree.py there, bring the regenerated PROGRESS.md back into main as a commit. The snapshot pipeline lives in snapshot-progress.sh (see repo). Related: [[flt-progress-md-is-generated]], [[flt-orchestrator-role]].

---
name: flt-worktree-seed-artifacts
description: "Deyao 2026-07-22 — when fanning out agent worktrees, seed them with build artifacts from a CONSISTENT state so agents never build from fresh"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T17:38:23.326Z
---

Deyao (2026-07-22): "when you fan out, copy the build artifacts too so that the agents don't need to build them from fresh. of course when you copy, you need to make sure the state is consistent."

**Why:** Worktree isolation without seeded artifacts makes every agent recompile the deep import chains (observed: gpp/serre/tate each rebuilding the WeilPairing spine in their sandboxes — hours of duplicated compute). Seeding from an inconsistent source (mid-build, or artifacts behind the checked-out commit) silently poisons agents with stale/missing oleans instead.

**How to apply:** The requirement is the INVARIANT, not a procedure: the artifacts an agent starts from must be consistent with the sources its worktree checks out — verified, not assumed. Deyao (same day, correcting an over-specific version of this note): you do NOT need to wait for builds to finish (dependency analysis can show a running build touches nothing in the copied cone), worktrees need NOT share one commit (each needs artifacts consistent with ITS commit), and hardlink-vs-copy is an implementation detail, not part of the rule. Analyze per-module: an olean is usable iff it matches the module source at the target commit and its import closure's oleans do too; copy any set satisfying that, whenever it satisfies it. Related: [[flt-orchestrator-role]], [[flt-progress-snapshot-worktree]].

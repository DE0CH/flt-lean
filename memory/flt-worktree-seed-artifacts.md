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

**How to apply:** Fan-out procedure: (1) ensure the seed source is CONSISTENT — no build running in it, oleans fresh w.r.t. the commit the worktrees will check out (materialize first if needed; the daemon's self-materialization or the snapshot worktree provide this); (2) create each worktree at that exact commit; (3) seed: hardlink the read-only dependency artifacts (`cp -al .lake/packages`), real-copy the project build dir (`cp -a .lake/build` — agents rewrite their own module oleans); (4) only then dispatch. Prefer seeding all worktrees from the same settled source so the fleet starts from one identical compiled state. Related: [[flt-orchestrator-role]], [[flt-progress-snapshot-worktree]].

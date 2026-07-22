---
name: flt-worktree-seed-artifacts
description: "Deyao 2026-07-22 — when fanning out agent worktrees, seed them with build artifacts from a CONSISTENT state so agents never build from fresh"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T18:06:17.232Z
---

Deyao (2026-07-22): "when you fan out, copy the build artifacts too so that the agents don't need to build them from fresh. of course when you copy, you need to make sure the state is consistent."

**Why:** Worktree isolation without seeded artifacts makes every agent recompile the deep import chains (observed: gpp/serre/tate each rebuilding the WeilPairing spine in their sandboxes — hours of duplicated compute). Seeding from a mid-build or behind-the-commit source is often fine too (Deyao, same day): the new build invalidates and rebuilds whatever mismatches (content hashing) — the cost of an imperfect seed is incremental rebuild time, not correctness.

**How to apply:** Seeding is a PERFORMANCE optimization, not a correctness requirement — the compiler is built to start from an older or incomplete artifact set and reconcile incrementally (content hashing rebuilds exactly what is stale or missing; that is expected operation, not an error). Deyao (2026-07-22, correcting two over-strict versions of this note): different commits are fine; no need to wait for running builds; analyze what is worth copying WITH ACTUAL CODE (a script comparing module sources/hashes and import cones — not eyeballed assumptions); an imperfect seed just means a bit more incremental rebuild in the worktree. NEVER use hardlinks (Deyao, same day: 'do not use hardlink at all, it is just a source of bugs') — the filesystem is copy-on-write, so plain copies are already cheap and carry no shared-inode mutation hazard.

**THE ONE HARD CONSTRAINT (Deyao, same day): the seed must never be a broken state the new compiler CANNOT pick up.** "Older/incomplete" is recoverable because lake's freshness metadata correctly reports it as stale; unrecoverable states are the ones whose metadata LIES so the build system never knows to rebuild. Examples:
- a torn/partially-written `.olean` copied together with its intact `.trace` — lake trusts the trace, treats the corrupt olean as fresh, and `importModules` crashes or misbehaves instead of rebuilding;
- an `.olean`/`.trace` pair whose trace matches the sources but whose olean content is from a different edit (metadata/content mix from two moments of a mid-write copy) — silently wrong environment, never rebuilt;
- artifacts from a different toolchain version — olean format mismatch that source-hash traces do not detect;
- out-of-sync sibling outputs (`.olean` vs `.ilean`/`.c`/setup json from different builds of the module).
The analysis script must therefore copy each module's artifact+metadata SET atomically-consistently (or drop the module from the seed — dropping is always safe, it just rebuilds); when in doubt about a file pair's coherence, exclude it. Net effect: fan-outs can seed cheaply at ANY moment, maximizing parallel start-up speed, with per-module coherence as the only invariant. Related: [[flt-orchestrator-role]], [[flt-progress-snapshot-worktree]].

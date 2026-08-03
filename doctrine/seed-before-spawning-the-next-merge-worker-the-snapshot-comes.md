## SEED BEFORE SPAWNING THE NEXT MERGE WORKER — the snapshot comes from the staging `.lake`

(2026-07-29, orchestrator error.) `flt-cycle.py release` seeds worktree artifacts by rsyncing
`MERGER_LAKE = /scratch/chend-flt/flt-staging/.lake/build` — **the merge worker's own build
directory**, hardcoded, with no option to point it elsewhere. So the sequence is not negotiable:

    merger reports green  ->  flt-cycle.py release   (snapshot + seed)
                          ->  dispatch the queue
                          ->  THEN spawn the next merge worker

I spawned release 19's worker first and then ran the seeding. Phase 1 (advance every worktree,
cheap) completed; phase 2 aborted on the built-in **torn-snapshot guard** — `.trace` files with no
matching `.olean`, for `ModThree` and `MazurTorsion`, because the next worker was mid-build in that
very directory. The guard is right and saved a fleet-wide seeding of a half-written olean set; it
also leaves the pool with everything `free` and **nothing `ready`**, i.e. dispatch blocked until the
next release.

There is no recovery that does not wait: `~/.flt-release-lake/build` holds only the *previous*
snapshot (days stale by then), and the release-18 artifacts are gone because the worker overwrote
them starting release 19. Hand-copying from a live worktree is precisely what the guard exists to
prevent. **The cost of getting the order wrong is one full release cycle of idle seeding capacity.**

Corollary worth stating separately: `release` is two phases with very different costs, and only
phase 2 needs the staging worktree quiet. If the order is ever wrong again, phase 1 has still run —
so every worktree IS advanced to the release, and the only thing missing is artifacts. Agents own
their own `.lake` and can rebuild; the loss is throughput, not correctness.


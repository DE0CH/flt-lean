---
name: flt-merger-red-verify-against-release-farm
description: When your target leaf exists only on a RED merger, base on merger anyway and verify in a scratch against a symlink farm of the release oleans
metadata:
  type: project
---

2026-07-31, `flt-lean-189`. The release-window check found the target
(`tsum_rpow_neg_natCard_quotient_isNarrowRayEquivMod_le_tsum_add_ray_class`)
only on `merger` — and `merger` does not build: release 27 was unpublished
because `merger`'s `X0.lean` has **103 errors**, and `X0` is in `ModThree`'s
import cone, so `lake build` on a merger-based branch never reaches the target
module.

**Why:** you must still base on `merger` (the leaf, its neighbours and the
parent that consumes it are merger-only; landing on `main` is a rival cut and a
duplicate declaration). But then the only *consistent* olean set you have is the
release one — your own `.lake` becomes a mix of main-seeded and merger-built
artifacts the moment a partial build runs.

**How to apply:** `cp -rs ~/.flt-release-lake/build/lib/lean /tmp/relean-N/lib/`,
put it FIRST on `LEAN_PATH` (harvest with `lake env printenv`, then call bare
`lean` — `lake env lean` resets it), and compile a scratch that `public import`s
the target module and **restates the target verbatim**. Measured: **12 s per
round**. Soundness condition: every name your proof uses must exist unchanged at
the release sha — check with `git diff --stat main merger -- <their files>`.

For the real file, build the farm from your own `.lake` and drop the release copy
of only the broken module over it; copy every sibling artifact
(`olean.server` too, or Lean stops with `failed to open file … .olean.server`).
Do not substitute modules whose merger olean built fine.

Related: [[flt-green-base-is-release-lake-sha]], [[flt-see-the-merge-before-the-merger]].

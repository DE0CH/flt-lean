---
name: flt-pairwise-unit-ratios-are-not-a-cocycle
description: "\"∀ i j, ∃ u unit, f i = u * f j\" on overlaps is strictly weaker than Cartier data — the triple identity needs f k to be cancellable, so a local-equations cut owes integrality or an explicit cocycle clause"
metadata: 
  node_type: memory
  type: project
  originSessionId: 29cb3fe7-f236-4bc9-887f-9ad78994eb0c
  modified: 2026-08-01T17:53:51.467Z
---

(2026-08-01, `flt-lean-289`, caught while writing the cut rather than after.) A
"local equations" leaf of the shape

    ∀ i j, ∃ u, IsUnit u ∧ (f i)|_{V i ⊓ V j} = u * (f j)|_{V i ⊓ V j}

looks like effective-Cartier-divisor data and is not. It constrains PAIRS; every
construction of `𝒪(D)` — gluing or subobject — needs `u i j * u j k = u i k` on the
triple overlap, and that follows from `u i j * u j k * f k = u i k * f k` only after
cancelling `f k`.

**Why:** ship the weak form and the sheaf-theoretic consumer is unprovable by the
recorded route, while looking fine to every scan.

**How to apply:** buy the cancellation. Either `[AlgebraicGeometry.IsIntegral X]` plus a
clause forcing `f i ≠ 0` — on an integral scheme "every member of the cover MEETS the
dense open `U`" is free and does it, via `map_injective_of_isIntegral` — or an explicit
triple-overlap clause in the data. Prefer the first when the call site has integrality;
the second is the honest general statement and is more for the geometric half to produce.

Rider: the meets-`U` clause makes `hUne` LOAD-BEARING FOR TRUTH in the geometric half,
though it was decoration in the parent (`U = ⊥` there is discharged by `L = 𝒪`, `s = 0`).
**A hypothesis's degenerate-case audit does not survive the cut that moves it** — re-run
it on each side. Related: [[flt-decomposition-drops-a-hypothesis]].

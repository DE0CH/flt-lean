---
name: flt-cup-product-universe-collapse
description: The categorical cup product forces its three coefficient modules into one universe; with k and V independent, ULift all three
metadata:
  type: project
---

`ContinuousCohomology.cup` (vendored 2026-07-31 into
`Fermat/FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/CupProduct.lean`)
lands in `A ⟶ TopModuleCat.linHom B C`, and a category has morphisms only between
objects of its own universe — so the three coefficient modules must share one universe.
The reference project also tied them to the GROUP's universe (`{M1 M2 M3 : Type v}` with
`{G : Type v}`); that half is removable by writing `Type (max v w)` and the port does so.
The other half is not.

**Why:** `HardlyRamified/Deformation.lean` has `k : Type u` and `V : Type v` independent,
so `AdZero k V : Type v` and the dualising module `k(1)` on carrier `k : Type u` cannot be
paired. `max u v = v` is not derivable, and the `Type v` copies of `k` one can build
(`span {1} ⊆ End k V`, `End k V ⧸ ad⁰`) carry the wrong Galois action or need `V ≠ 0`.

**How to apply:** `ULift` all three into `Type (max u v)` — `ad⁰`, `ad⁰(1)` by `ULift.{u}`,
`k(1)` by `ULift.{v}` — using `contRepULift` in `Deformation.lean`, which is free because
every carrier there is discrete. Give any definition whose carrier mentions `v` but not `V`
an explicit `(V : Type v)` universe-marker argument, or use sites elaborate ambiguously.
See [[flt-two-leaves-may-be-one]] for the neighbouring habit of checking statements before
building machinery.

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

**EXTENDED 2026-08-02 (`flt-lean-248`): the `ULift` does not stay local to the pairing —
it FORKS THE COHOMOLOGY.** `TopRep k G` has morphisms only within one module universe and
`ContinuousCohomology.map` inherits that (`{X : TopRep k G} {Y : TopRep k H}`,
`f : res φ X ⟶ Y`). So once the local coefficients are lifted into `Type (max u v)`, every
GLOBAL object localised into them must be lifted too, and anything already stated in
`Type v` — `Sha1Twist`, `Sha2`, `adZeroTwistRestricted` — sits in a cohomology theory
nothing can map into or out of. Build the new development entirely in the lifted world;
state the crossing ONCE as a named leaf and as a CARDINALITY comparison (an inclusion is
not stateable, the ambients differ); and check which sibling already owes the same
crossing — `poitouTateExactness_of_localTateDuality` owed exactly this one.

Take the invariants OF THE LIFTED module (`unramTopRep (adZeroTopRepU ρbar) S`), never the
lift of the invariants: then the bridge to the local objects is the plain inclusion of
invariants and its equivariance is `rfl`, because `unramRep` is a `QuotientGroup.lift` of a
`LinearMap.restrict` and computes on `QuotientGroup.mk'`.

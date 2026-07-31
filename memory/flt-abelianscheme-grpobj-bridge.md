---
name: flt-abelianscheme-grpobj-bridge
description: AbelianSchemeStruct now bridges to mathlib's GrpObj (Over.mk f) — build group schemes in mathlib's language and convert, don't re-derive smoothness/commutativity
metadata:
  type: project
---

`Fermat/FLT/Modularity/AbelianSchemeGrpObj.lean` (added 2026-07-31) connects this
development's functor-of-points `AbelianSchemeStruct f` to mathlib's
`GrpObj (Over.mk f)`.  The usable entry point is

    AbelianSchemeStruct.ofGrpObjOfGeometricallyIntegral
      (f : G ⟶ Spec (CommRingCat.of K)) [GrpObj (Over.mk f)] [IsProper f]
      [GeometricallyIntegral f] : AbelianSchemeStruct f

**Why:** `Mathlib/AlgebraicGeometry/Group/` proves `smooth_of_grpObj` (a
geometrically reduced, locally-of-finite-type group scheme over a field is
smooth) and `isCommMonObj_of_isProper_of_geometricallyIntegral` (stacks 0BFD).
Both are stated for `GrpObj`, so before the bridge existed neither was reachable
from any leaf phrased in `AbelianSchemeStruct`, and agents were costing
"smoothness of a reduced group scheme over a perfect field" as missing theory.
It is not missing.  Geometric connectedness likewise comes free from geometric
irreducibility (`geometricallyConnected_of_geometricallyIrreducible`, also in that
module — the pin has no such instance).

**How to apply:** when a leaf asks you to PRODUCE an abelian scheme, produce a
group object plus `IsProper` and `GeometricallyIntegral` and convert; do not
prove smoothness or commutativity by hand.  `Over S` already has global
`CartesianMonoidalCategory` and `BraidedCategory` instances
(`Mathlib/AlgebraicGeometry/Pullbacks.lean`), so `GrpObj (Over.mk f)` needs no
setup.  `grpAdd`/`grpZero`/`grpNeg` are the induced operations on `RelPoint`
and are `ofGrpObj`'s fields on the nose, so a compatibility clause stated with
`grpAdd` matches `abB.add` by `rfl` — that is how
`exists_abelianSubscheme_closure_of_divisibleGaloisSubmodule_finiteBase` is
proven over `exists_grpObj_closure_of_divisibleGaloisSubmodule_finiteBase`.
The converse direction (`AbelianSchemeStruct → CommGrpObj`) was written, verified
and then dropped as free-floating; the recipe is in the module docstring.
See [[flt-inventory-audits-understate-what-exists]] and
[[audit-searched-production-not-invariant]].

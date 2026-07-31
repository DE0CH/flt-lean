---
name: grpobj-via-ofrepresentableby
description: Build a GrpObj/MonObj in a cartesian monoidal category with ofRepresentableBy (a presheaf of groups), never by writing mul/one/inv as morphisms out of fibre products
metadata:
  type: reference
---

`CategoryTheory.GrpObj.ofRepresentableBy` (`Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean`)
turns a **representable presheaf of groups** into a group object in any cartesian monoidal
category. `MonObj`, `IsCommMonObj` and `CommGrpObj` have the same constructor in sibling files.

**Why:** the alternative supplies `mul : X ⊗ X ⟶ X`, `one : 𝟙_ ⟶ X`, `inv : X ⟶ X` and checks
five diagrams, each an equation of morphisms out of an iterated fibre product, in
`CartesianMonoidalCategory`'s associator/unitor vocabulary. Via `ofRepresentableBy` every axiom
is an equation between **elements of a type** and no pullback ever appears.

**How to apply:** for `Over S` with `S : Scheme`, the monoidal structure IS `Limits.pullback` —
`tensorObj_left`, `lift_left`, `fst_left`, `snd_left`, `toUnit_left` are all `rfl`, and
`AlgebraicGeometry/Pullbacks.lean:705` registers the instance globally. Give
`G : (Over S)ᵒᵖ ⥤ GrpCat` from the relative-point group and
`(G ⋙ forget _).RepresentableBy (Over.mk f)` whose `homEquiv` is `h ↦ ⟨h.left, h.w⟩` /
`Over.homMk` (both inverse laws are `rfl`). Naturality obligations are exactly two — `map_mul`
and `map_one` — because a group hom is a `MonoidHom`; inversion needs nothing. `GrpObj` is DATA,
so return `Nonempty (GrpObj …)` and `obtain` it at the consumer.

Done in `Fermat.nonempty_grpObj_of_relPointGroup` (`X0.lean`, 2026-07-31), which fed
`AlgebraicGeometry.smooth_of_grpObj` (Cartier) and closed
`smooth_schemeTheoreticImage_of_isAdditiveOn`. The recon had priced the `GrpObj` as the bulk of
that leaf and prescribed a refactor of a neighbouring proof to export three
`IsClosedImmersion.lift`s; none of it was needed. `Fermat.nonempty_grpObj_of_yoneda`
(`GroupScheme/AffineGroupHopf.lean`) was already the same trick on the affine/Hopf side and sat
unconnected to the leaf for three days.

General form: a functor-of-points presentation and a morphisms-and-diagrams presentation are
Yoneda-equivalent and mathlib carries the bridge — pick the side the data is already on. See
[[flt-absence-audit-names-one-module]] and [[flt-missing-machinery-may-be-downstream]] for the
companion trap that hit the same leaf's other half.

---
name: mathlib-has-ega-8-8-not-the-localization-colimit
description: "Mathlib's AffineTransitionLimit.lean already has all of EGA IV 8.8 for schemes; what the pin lacked was the ring-level presentation of Localization M as the filtered colimit of the Localization.Away m, now PROVEN in X0.lean as awaySpecIsLimit"
metadata:
  type: project
---

Any leaf whose docstring says "this is EGA IV 8.8/8.14, pure spreading out" should be
priced against `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`, which is far
stronger than the one-line "pin available" notes suggest. It contains, for a cofiltered
diagram of qcqs schemes with affine transition maps over a base `S`:

* `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` — a morphism
  `lim Dᵢ ⟶ X` factors through some `Dⱼ ⟶ X` when `X ⟶ S` is locally of finite
  presentation (the SURJECTIVITY half, and the one people actually need);
* `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` and
  `…_hom_hom_…` — the injectivity half;
* `exists_map_preimage_eq_map_preimage`, `exists_preimage_eq`,
  `isBasis_preimage_isAffineOpen`, `Scheme.exists_isAffine_of_isLimit` — for descending
  conditions on ranges and opens.

**What was NOT there (searched 2026-07-31, whole of `RingTheory/Localization/`): any
`IsColimit`, and any statement relating `Localization.Away` to `Localization.AtPrime` as
a colimit.** So the entire cost of "spreading out over `Spec R_p`" was supplying the
presentation, not the descent theorem. That is now `Fermat.awaySpecIsLimit` in
`Fermat/FLT/ModularCurve/X0.lean` (section `AwayLimit`), for an arbitrary submonoid
`M ≤ A`:

    Spec (Localization M) = lim_{m ∈ M} Spec (Localization.Away m)

cofiltered over `M` under REVERSE divisibility (`m ⟶ n` iff `n ∣ m`), with affine
transition maps and affine stages, together with the packaged corollary
`exists_hom_away_of_localization`. `Spec` is a right adjoint, so the scheme statement is
`isLimitOfPreserves` applied to the ring-level `awayIsLimit`, and the ring-level proof is
just `IsLocalization.lift` + `IsLocalization.ringHom_ext` — the index `1 ∈ M` supplies
the single map `A ⟶ s.pt` that every leg restricts to, and there is no filteredness
argument in it at all.

Two things that make it apply for free in this development: `AbelianSchemeStruct` carries
`smooth` as a FIELD and mathlib has `Smooth f → LocallyOfFinitePresentation f` as an
instance, so `d.f` is finitely presented over ANY (non-noetherian) base; and each stage is
affine, hence compact and quasi-separated.

Companion technique, for descending a UNIT rather than an element: over `R_p` do not run a
second colimit argument — write the element as `numerator / s^k`, observe its image is a
unit, and use `IsLocalization.AtPrime.isUnit_to_map_iff` to conclude `numerator ∉ p`. That
is `exists_weierstrassCurve_away_of_atPrime`, and locality replaces filteredness outright.

See [[lean-op-category-defeq-needs-exact-not-rw]] for the Lean-engineering traps in
building the diagram.

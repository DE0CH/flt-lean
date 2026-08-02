---
name: flt-generic-fibre-plus-flatness-beats-regularity
description: Over a DVR/domain base, properties of the total space come from the GENERIC FIBRE plus flatness — not from regularity of the total space, which is the expensive route an audit will name.
metadata:
  type: project
---

(2026-08-02, `isIntegral_of_smoothProperCurve` in `ModularCurve/X0.lean`, PROVEN.)
A leaf asserting a property of a scheme `𝒳` smooth and proper over `ℤ_(ℓ)` will
almost always be audited conjunct-by-conjunct, and each conjunct priced by ITS OWN
classical proof. Those proofs run through **regularity of `𝒳`**, hence through
"smooth over a regular base is regular", which really is absent from this pin
(`grep -rln "IsRegularRing\|IsRegularLocalRing" Mathlib/` returns exactly two files,
both under `RingTheory/RegularLocalRing/`, and neither mentions `Smooth`).

**The cheap route is the GENERIC FIBRE, and it covers both halves:**

* *reduced*: `𝒳` is flat over the domain `R`, so `A ↪ Frac R ⊗_R A` on every affine
  open, and the target is smooth over the FIELD `Frac R`. That is
  `AlgebraicGeometry.isReduced_of_smooth_over_domain`, already PROVEN in
  `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`;
* *irreducible*: the generic fibre is a smooth geometrically connected curve over a
  FIELD, hence integral
  (`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`,
  `CurveExtension.lean`, which needs no properness); it is an OPEN subscheme
  because `Spec ℚ ⟶ Spec R` is an open immersion; and it is DENSE because a flat map
  is generalizing (`Flat.generalizingMap`) and the generic point of `Spec R` lies in
  that open. A space with a dense preirreducible subset is preirreducible
  (`IsPreirreducible.closure`).

**Nothing about `𝒳` over the DVR is ever shown regular, and no connectedness of `𝒳`
is needed either** — the audit's route wanted both.

So: when a leaf's conclusion is a property of the total space of a family over a
domain, ask whether the property **descends from the generic fibre along flatness**
before pricing anything about the total space. Reduced, irreducible, integral and
"has a dense open with property P" all do; regular and normal do not.

See [[flt-absence-audit-greps-consumer-vocabulary]] for the other half of why this
leaf stood: the audit greps mathlib, and the missing theorem was in `Fermat/`.

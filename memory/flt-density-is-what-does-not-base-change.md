---
name: flt-density-is-what-does-not-base-change
description: In "∃ dense open + property" predicates, every clause base-changes EXCEPT density; repair it downstream with irreducibility + nonemptiness, not with a density hypothesis
metadata:
  type: project
---

`HasDoubleCoverOfAffineLine` / `HasNoFibreAffineLine` (X0.lean) both have the shape
"∃ `U`, an open immersion `ι : U ⟶ X` that is DOMINANT, plus a finite `φ : U ⟶ 𝔸(Unit; S)`
over `S`, plus a fibre-size clause". Transporting one along a base change `S' ⟶ S`:

- `IsOpenImmersion ι` — base-changes (`MorphismProperty.IsStableUnderBaseChange`);
- `IsFinite φ` — base-changes, once you know `𝔸(n; S') = 𝔸(n; S) ×_S S'`, which is
  exactly **`AlgebraicGeometry.AffineSpace.isPullback_map`**. That lemma is the key to
  base-changing *anything* stated with the relative affine line;
- the fibre-size clause — transports, because a `K`-point of `V ×_T T'` is pinned by its
  two projections (`IsPullback.hom_ext` twice);
- **`IsDominant ι` — does NOT base-change.** A dense open of the total space can miss a
  whole fibre. In the intended application it does exactly that: the open lives inside
  the GENERIC fibre and meets the special fibre in ∅.

So density must be *re-derived* downstairs. The cheap true version: over an IRREDUCIBLE
target a nonempty open is dense (`IsOpen.dense` needs only `PreirreducibleSpace`). For a
smooth proper geometrically connected model over `ℤ_(ℓ)` the special fibre is integral —
proven as `isIntegral_pullbackSpecial_of_isReductionBase`, over
`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` (CurveExtension.lean),
whose base must be a FIELD, so it applies to the fibre and never to the model.

**Why this pays**: it lets a leaf ask for `Nonempty U` instead of `IsDominant ι`. Every
construction of such an open exhibits a point on the way (the generic point of the special
fibre), so the weakened ask is free, and the density argument stops being the prover's
problem. That cut is what `exists_finite_toAffineLine_specialFibre_of_model` is.

**Why:** the density clause is the only one that is a statement about the *whole* of the
source rather than about the morphism, and base change does not preserve "whole".

**How to apply:** when transporting an "∃ dense open …" predicate along any pullback,
budget for density separately and look for irreducibility of the target; and when CUTTING
such a predicate into a leaf, weaken `IsDominant` to `Nonempty` and prove the upgrade in
the assembly. See also [[flt-cleaner-statement-harder-proof]].

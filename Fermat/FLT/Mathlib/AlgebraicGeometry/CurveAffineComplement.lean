/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveExtension

/-!
# The complement of a closed point of a smooth proper curve is affine

Classically (Hartshorne IV.1, Stacks `0BXB`) a nonempty effective divisor on a smooth
proper geometrically connected curve over a field is **ample**, so the complement of its
support is affine.  Specialised to a single closed point this is the statement that makes
the *affine chart* of a pointed curve exist — and it is the scheme-theoretic half of
"an elliptic scheme has a Weierstrass model", the other half being Riemann–Roch.

## What is here

* `IsClosedImmersion.of_section` and `isClosed_range_of_section` — a section of a
  separated morphism is a closed immersion, so its range is closed.  PROVEN.
* `range_eq_singleton_of_spec_field` — the range of a `K`-point of a scheme is a
  singleton, `K` a field.  PROVEN.  (`Spec K` is a one-point space.)
* `isClosed_singleton_of_section` — the two combined: the image of a section of a
  separated morphism from the spectrum of a field is a closed point.  PROVEN.
* `isAffineOpen_compl_singleton_of_isSmoothProperCurve` — **the sorry leaf**, and it is
  the whole content: ampleness / the Serre criterion.
* `exists_isOpenImmersion_range_eq_compl_of_section` — the packaged existential a consumer
  actually wants: a ring `R` and an open immersion `Spec R ⟶ X` onto the complement of the
  image of a `K`-point.  PROVEN over the leaf.

## Why the leaf is not further decomposable here

The only cut available is "the complement is open" plus "the complement is affine", and
everything except the second is proven in this file.  The second needs ampleness of
divisors, which **the pin does not have**: verified 2026-07-28 by
`grep -rl 'Ample' Mathlib/AlgebraicGeometry/`, which returns only files where the word
occurs inside `example`/`sample`.  There is no `IsAmple`, no `VeryAmple`, no Serre
criterion for affineness and no coherent-sheaf cohomology anywhere under
`Mathlib/AlgebraicGeometry/`, and `~/cs/FLT` has none either.

The classical route, for whoever picks the leaf up: `[z]` has positive degree on the
integral projective curve `X`, hence is ample, hence `X ∖ {z}` is affine.  A route that
avoids ampleness and stays closer to what this project already owns: Riemann–Roch supplies
a nonconstant `x` regular away from `z`; `x` extends to a morphism `X ⟶ ℙ¹` by the
valuative criterion (`exists_unique_extension_of_isSmoothProperCurve`, PROVEN in
`CurveExtension.lean`); that morphism is proper and quasi-finite, hence finite by Zariski's
main theorem (`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`); and the preimage of
the affine `𝔸¹` under a finite — hence affine — morphism is affine.  That route pays for
Riemann–Roch, which the sibling leaf needs anyway.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-! ### Sections of a separated morphism -/

/-- **A section of a separated morphism is a closed immersion** (PROVEN).

`s ≫ f = 𝟙` is an isomorphism, hence a closed immersion, and `IsClosedImmersion` cancels
on the right against a separated morphism (`IsClosedImmersion.of_comp`). -/
theorem IsClosedImmersion.of_section {X Y : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ X}
    [IsSeparated f] (hs : s ≫ f = 𝟙 Y) : IsClosedImmersion s := by
  have h : IsClosedImmersion (s ≫ f) := by
    rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s f

/-- **The range of a section of a separated morphism is closed** (PROVEN). -/
theorem isClosed_range_of_section {X Y : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ X}
    [IsSeparated f] (hs : s ≫ f = 𝟙 Y) : IsClosed (Set.range s.base) := by
  haveI := IsClosedImmersion.of_section hs
  exact s.isClosedEmbedding.isClosed_range

/-- **The range of a `K`-point of a scheme is a single point**, `K` a field (PROVEN):
`Spec K` is a one-point space, so the range of any `Spec K ⟶ X` is the singleton on the
image of the unique point. -/
theorem range_eq_singleton_of_spec_field {K : Type u} [Field K] {X : Scheme.{u}}
    (s : Spec (CommRingCat.of K) ⟶ X) :
    ∃ z : X, Set.range s.base = {z} := by
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ⟨s.base (IsLocalRing.closedPoint K), ?_⟩
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact congrArg _ (Subsingleton.elim w _)
  · rintro rfl
    exact ⟨_, rfl⟩

/-- **The image of a `K`-point that is a section of a separated morphism is a closed
point** (PROVEN, from the two lemmas above). -/
theorem isClosed_singleton_of_section {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of K)} {s : Spec (CommRingCat.of K) ⟶ X} [IsSeparated f]
    (hs : s ≫ f = 𝟙 _) {z : X} (hz : Set.range s.base = {z}) :
    IsClosed ({z} : Set X) :=
  hz ▸ isClosed_range_of_section hs

/-! ### The affineness leaf -/

/-- **The complement of a closed point of a smooth proper geometrically connected curve
over a field is affine** (sorry leaf, cut 2026-07-28).

TRUE and classical: `[z]` is a nonempty effective divisor on the integral projective curve
`X`, hence ample, hence the complement of its support is affine (Hartshorne IV.1, or the
Serre criterion applied to `O(n·[z])`).

**`hconn` IS LOAD-BEARING and the statement is FALSE without it.**  Take `X` the disjoint
union of two copies of a smooth proper curve and `z` a closed point of the first.  `X` is
still smooth of relative dimension one and still proper, `{z}` is still closed, and the
complement still contains the whole second copy — which is proper and positive-dimensional,
hence not affine, and an open subscheme with a proper positive-dimensional *component*
cannot be affine (its global sections would have to separate the points of that component,
but they are constant on it by properness).  Connectedness is exactly what forbids that.

**`SmoothOfRelativeDimension 1` IS LOAD-BEARING and the statement is FALSE without it.**
At relative dimension two the complement of a point on an abelian surface has the same
global sections as the surface (`K`, by properness), so it is not affine — not even
quasi-affine.  This is the same hypothesis, and the same counterexample, that separates
the curve case from the abelian-surface case in `exists_affineComplement_zeroSection`.

**`hz` IS LOAD-BEARING for a trivial reason**: `{z}ᶜ` has to be open before it can be an
affine *open*, and a scheme is only `T0`, so a point need not be closed.  In every intended
application `z` is the image of a rational point, and `isClosed_singleton_of_section`
supplies `hz`.

**`IsProper` is used by the intended ROUTE, not by the truth of the statement**: a smooth
connected curve that is *not* proper is already affine-by-compactification, since then the
compactification has a second missing point.  Do not drop it without a proof — the route
below goes through the projective model.

NOT VACUOUS: for `E` an elliptic curve over `ℚ`, `proj E` with `z` the point at infinity
satisfies every hypothesis, and the conclusion holds there with the affine chart
`Spec ℚ[E]` — see `exists_affineChart_projInfty` in
`Fermat/FLT/ModularCurve/EllipticScheme.lean`, which is PROVEN.  So the hypothesis set is
inhabited and the conclusion is not satisfiable only by junk.

WHAT WOULD REFUTE THE "MISSING FROM THE PIN" DIAGNOSIS: any declaration under
`Mathlib/AlgebraicGeometry/` concluding `IsAffineOpen` (or `IsAffine`) for an open
subscheme from a condition on its complement, or any ampleness of divisors.  Searched
2026-07-28 over `Fermat/`, `.lake/packages/mathlib` and `~/cs/FLT`: absent from all
three. -/
theorem isAffineOpen_compl_singleton_of_isSmoothProperCurve
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X)) :
    IsAffineOpen (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) :=
  sorry

/-- **The complement of the image of a `K`-point of a smooth proper geometrically connected
curve is the range of an open immersion from an affine scheme** (PROVEN over the leaf
above).

This is the shape a consumer wants: it hands back a bare commutative ring together with an
open immersion of its spectrum onto the complement, which is exactly
`exists_affineComplement_zeroSection`'s conclusion. -/
theorem exists_isOpenImmersion_range_eq_compl_of_section
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ strX = 𝟙 _) :
    ∃ (R : Type u) (_ : CommRing R) (ι : Spec (CommRingCat.of R) ⟶ X),
      IsOpenImmersion ι ∧ Set.range ι.base = (Set.range s.base)ᶜ := by
  obtain ⟨z, hzr⟩ := range_eq_singleton_of_spec_field s
  have hz : IsClosed ({z} : Set X) := isClosed_singleton_of_section hs hzr
  have hU : IsAffineOpen (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) :=
    isAffineOpen_compl_singleton_of_isSmoothProperCurve strX hconn hz
  refine ⟨Γ(X, (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)), inferInstance,
    hU.fromSpec, inferInstance, ?_⟩
  rw [hU.range_fromSpec, hzr]
  rfl

end AlgebraicGeometry

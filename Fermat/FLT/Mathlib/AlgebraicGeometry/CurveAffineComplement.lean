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
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
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
* `injective_of_surjective_coordinateRing` — a surjection from a Weierstrass coordinate
  ring onto a domain that is not a field is injective.  PROVEN, no sorry.  This is the
  algebraic half of "the affine chart IS a Weierstrass coordinate ring"; it means the
  geometric side has to construct only a SURJECTION, never an isomorphism.

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

universe u v

open CategoryTheory TopologicalSpace
open scoped Polynomial

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

/-! ### Recognising a Weierstrass coordinate ring from a surjection

The affine chart of a pointed genus-one curve is a Weierstrass coordinate ring.  That
statement splits cleanly in two, and only the FIRST half is Riemann–Roch:

1. the chart's ring is *generated by two elements satisfying a Weierstrass relation* —
   equivalently, some `E.toAffine.CoordinateRing` maps ONTO it.  This is where `L(2[O])`,
   `L(3[O])` and the seven-monomials-in-a-six-dimensional-space count live.
2. any such surjection is automatically INJECTIVE.  This half is pure commutative algebra
   and is proven below, so a prover at the chart need only produce the surjection.
-/

/-- **A surjection from a Weierstrass coordinate ring onto a domain that is not a field is
injective** (PROVEN 2026-07-28) — so such a surjection is automatically a ring
isomorphism.

This is the algebraic half of "the affine chart of a pointed genus-one curve is a
Weierstrass coordinate ring": it removes the need for the geometric side to prove anything
about the KERNEL of the map it constructs.

The proof is Krull dimension in elementary form.  `C := E.toAffine.CoordinateRing` is a
free `k[X]`-module of rank two (`WeierstrassCurve.Affine.CoordinateRing.basis`), hence
integral over `k[X]`, hence `R` — a quotient of `C` — is integral over `k[X]` too.  Now
suppose the kernel contains some `a ≠ 0`.  The constant coefficient `c` of the minimal
polynomial of `a` over `k[X]` is nonzero (otherwise `divX` of it would be a monic
annihilator of strictly smaller degree, `C` being a domain and `a ≠ 0`), and
`c = -(a · …)` lies in the kernel.  So the kernel `P` of `k[X] → R` is a NONZERO prime;
`k[X]` is a PID, so `P` is maximal and `k[X]/P` is a field; and `R` is a domain integral
over a field, hence itself a field (`isField_of_isIntegral_of_isField'`) — contradicting
`hR`.

**`hR` IS LOAD-BEARING and the statement is FALSE without it**: `φ` may be the quotient
by any maximal ideal, e.g. `E.toAffine.CoordinateRing → k` evaluating at a `k`-rational
point of `E`.  That is a surjection onto a domain and is very far from injective.  What
`hR` says geometrically is that the target is a CURVE and not a point.

**`IsDomain R` IS LOAD-BEARING** in the same way — without it `φ` could be the quotient by
any ideal at all — and it is free in the intended application, where `Spec R` is an open
subscheme of an integral scheme.

NOT VACUOUS: for `E` elliptic over `ℚ`, the identity of `E.toAffine.CoordinateRing`
satisfies every hypothesis (the coordinate ring is a domain and is not a field, being a
one-dimensional domain), and the conclusion holds. -/
theorem injective_of_surjective_coordinateRing {k : Type u} [Field k]
    (E : WeierstrassCurve k) {R : Type v} [CommRing R] [IsDomain R] (hR : ¬ IsField R)
    (φ : E.toAffine.CoordinateRing →+* R) (hφ : Function.Surjective φ) :
    Function.Injective φ := by
  classical
  haveI hfin : Module.Finite k[X] E.toAffine.CoordinateRing :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine)
  haveI : Algebra.IsIntegral k[X] E.toAffine.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  letI : Algebra E.toAffine.CoordinateRing R := φ.toAlgebra
  letI : Algebra k[X] R := (φ.comp (algebraMap k[X] E.toAffine.CoordinateRing)).toAlgebra
  haveI : IsScalarTower k[X] E.toAffine.CoordinateRing R :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral k[X] R := by
    refine ⟨fun r => ?_⟩
    obtain ⟨x, rfl⟩ := hφ r
    exact (Algebra.IsIntegral.isIntegral (R := k[X]) x).map
      (IsScalarTower.toAlgHom k[X] E.toAffine.CoordinateRing R)
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hane
  have hint : IsIntegral k[X] a := Algebra.IsIntegral.isIntegral a
  have hmon : (minpoly k[X] a).Monic := minpoly.monic hint
  have hae : (Polynomial.aeval a) (minpoly k[X] a) = 0 := minpoly.aeval _ _
  -- the constant coefficient of the minimal polynomial is nonzero
  have hc : (minpoly k[X] a).coeff 0 ≠ 0 := by
    intro h0
    have hpx : Polynomial.X * (minpoly k[X] a).divX = minpoly k[X] a := by
      have h := Polynomial.X_mul_divX_add (minpoly k[X] a)
      rw [h0, map_zero, add_zero] at h
      exact h
    have hlead : (minpoly k[X] a).divX.leadingCoeff = 1 := by
      have h : (minpoly k[X] a).leadingCoeff = (minpoly k[X] a).divX.leadingCoeff := by
        conv_lhs => rw [← hpx]
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X, one_mul]
      rw [← h]; exact hmon
    have hmon' : (minpoly k[X] a).divX.Monic := hlead
    have hae' : (Polynomial.aeval a) (minpoly k[X] a).divX = 0 := by
      have hz : a * (Polynomial.aeval a) (minpoly k[X] a).divX = 0 := by
        conv_rhs => rw [← hae, ← hpx]
        simp
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hane
      · exact h
    exact absurd (minpoly.min k[X] a hmon' hae')
      (not_le.mpr (Polynomial.degree_divX_lt hmon.ne_zero))
  -- and it lies in the kernel of `k[X] → R`
  have hkey : algebraMap k[X] E.toAffine.CoordinateRing ((minpoly k[X] a).coeff 0)
      = -(a * (Polynomial.aeval a) (minpoly k[X] a).divX) := by
    have h := congrArg (Polynomial.aeval a) (Polynomial.X_mul_divX_add (minpoly k[X] a))
    rw [hae] at h
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    linear_combination h
  have hker : (algebraMap k[X] R) ((minpoly k[X] a).coeff 0) = 0 := by
    show φ (algebraMap k[X] E.toAffine.CoordinateRing ((minpoly k[X] a).coeff 0)) = 0
    rw [hkey, map_neg, map_mul, ha, zero_mul, neg_zero]
  -- so that kernel is a nonzero prime of a PID, hence maximal
  set P : Ideal k[X] := RingHom.ker (algebraMap k[X] R) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hPne : P ≠ ⊥ := by
    intro h
    have hmem : (minpoly k[X] a).coeff 0 ∈ P := RingHom.mem_ker.mpr hker
    rw [h, Ideal.mem_bot] at hmem
    exact hc hmem
  haveI : P.IsMaximal := _root_.IsPrime.to_maximal_ideal hPne
  letI : Field (k[X] ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (k[X] ⧸ P) R :=
    (Ideal.Quotient.lift P (algebraMap k[X] R) (fun _ hx => hx)).toAlgebra
  haveI : IsScalarTower k[X] (k[X] ⧸ P) R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral (k[X] ⧸ P) R := Algebra.IsIntegral.tower_top (R := k[X])
  exact hR (isField_of_isIntegral_of_isField' (R := k[X] ⧸ P) (Field.toIsField _))

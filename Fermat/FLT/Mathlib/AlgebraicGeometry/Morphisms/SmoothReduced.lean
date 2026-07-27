/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Unramified.Field

/-!
# Smooth morphisms are geometrically reduced

A smooth morphism of schemes is geometrically reduced: every base change of it
to a field has reduced total space.  This is the scheme-theoretic packaging of
the single classical fact

    a scheme smooth over a field is reduced

and it is absent from the mathlib pin *as a statement* — but, as the docstring
of `Algebra.IsStandardSmooth.isReduced_of_field` records, every ingredient of
its proof is present, and this file is now **sorry-free**.

## Main results

* `Algebra.IsStandardSmooth.isReduced_of_field` — a *standard* smooth algebra
  over a field is reduced.  This is the mathematical content.
* `Algebra.Smooth.isReduced_of_isField` — a smooth algebra over a field is
  reduced (from the previous item, since smooth is standard smooth on a
  standard open cover).
* `RingHom.Smooth.isReduced_of_isField` — the `RingHom` restatement.
* `AlgebraicGeometry.isReduced_of_smooth_over_field` — a scheme smooth over a
  field is reduced (proven from the leaf by an affine cover).
* `AlgebraicGeometry.GeometricallyReduced.of_smooth` — `Smooth f →
  GeometricallyReduced f` (proven from the previous item, since `Smooth` is
  stable under base change).

## Why this file exists

`GeometricallyReduced` is the hypothesis mathlib's
`AlgebraicGeometry/Geometrically/Reduced.lean` asks for in

    instance [GeometricallyReduced g] [Flat g] [IsReduced X]
      [IsLocallyNoetherian X] : IsReduced (pullback f g)

which is how reducedness of an iterated fibre product is obtained.  Mathlib
defines the class and proves it stable under base change, but **nothing in
mathlib ever instantiates it** except from itself; in particular there is no
route from smoothness.  Supplying that route once, in this generality, is
strictly less work than any parochial substitute, and it is immediately
reusable: all the base-change instances downstream of `GeometricallyReduced`
come for free.
-/

@[expose] public section

universe u v

open CategoryTheory Limits

/-- **A standard smooth algebra over a field is reduced.**

PROVEN.  This is the whole mathematical content of
`AlgebraicGeometry.GeometricallyReduced.of_smooth`, and it is *not* obtained
through regular local rings — see the audit below for why that route is a dead
end at this pin and what replaces it.

## THE PROOF

Write `P := K[X₁, …, Xₙ]` for the polynomial ring in `n = ` the relative
dimension, and `M := P⁰` for its non-zero-divisors.

1. `RingHom.IsStandardSmooth.exists_etale_mvPolynomial` factors `K → T` as
   `K → P → T` with `P → T` **étale**.  This is the Jacobian criterion,
   already done in mathlib: a submersive presentation with `c` relations
   among `n + c` variables is a submersive presentation of relative dimension
   `0` over the polynomial ring on the `n` variables *not* hit by
   `P.map`, and `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`
   converts that to étaleness.
2. Étale ⟹ smooth ⟹ `Module.Flat P T` (`Algebra.Smooth.flat`), and `P` is a
   domain, so every `t ∈ M` acts injectively on `T`
   (`Module.Flat.isSMulRegular_of_nonZeroDivisors`).
3. Pass to the generic fibre `Tₘ := M⁻¹T`.  By
   `Algebra.FormallyEtale.localization_map` it is formally étale over
   `Frac P = M⁻¹P`, and essentially of finite type over it, so
   `Algebra.FormallyUnramified.isReduced_of_field` gives `IsReduced Tₘ`.
   (Concretely `Tₘ` is a finite product of finite separable extensions of
   `Frac P`, by `Algebra.FormallyEtale.iff_exists_algEquiv_prod`.)
4. A nilpotent `x : T` dies in the reduced ring `Tₘ`, so `t * x = 0` for some
   `t ∈ M`; by step 2, `x = 0`.

## AUDIT CORRECTION (2026-07-27)

An earlier version of this docstring recorded the leaf as needing *new
commutative algebra*: "smooth ⟹ regular ⟹ domain", with both halves absent.
The **absence claims about regular local rings are all still true** —
`grep -rln 'IsRegularLocalRing\|IsRegularRing' Mathlib/` returns exactly
`RingTheory/RegularLocalRing/{Defs,Polynomial}.lean`, which contain no
`IsRegularLocalRing → IsDomain` and no link to smoothness; and
`grep -rn 'IsReduced\|IsRegularLocalRing\|IsRegularRing\|IsDomain'
Mathlib/RingTheory/Smooth/ Mathlib/RingTheory/Etale/` is indeed empty.

The audit was nevertheless **wrong about the conclusion**, and in an
instructive way: it searched the two directories where the *statement* would
live and inferred that the *route* was unavailable.  The decisive lemma is in
neither of them.  It is
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`, in
`Mathlib/RingTheory/RingHom/StandardSmooth.lean`, and it makes the regular
local ring theory unnecessary: reducedness is inherited from the *generic
fibre*, which is étale over a field and therefore a product of separable field
extensions, rather than from regularity of the local rings.

Two of the audit's other observations survive unchanged and are worth keeping:

* `AlgebraicGeometry/Group/Smooth.lean`'s
  `smooth_of_grpObj [GeometricallyReduced f] : Smooth f` (Cartier) is the
  **converse**; a name-based search hits it and cannot run it backwards.
* A lifting-property proof really does fail: applying formal smoothness to
  `B = A`, `J = nilradical` produces only an endomorphism `σ ≡ id (mod N)`,
  which is no contradiction with `N ≠ 0`.  The content is genuinely the
  Jacobian criterion — mathlib just already has it. -/
theorem Algebra.IsStandardSmooth.isReduced_of_field (K : Type u) (T : Type v) [Field K]
    [CommRing T] [Algebra K T] [Algebra.IsStandardSmooth K T] : IsReduced T := by
  obtain ⟨n, g, _, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (RingHom.isStandardSmooth_algebraMap.mpr ‹Algebra.IsStandardSmooth K T›)
  algebraize [g]
  haveI : IsDomain (MvPolynomial (Fin n) K) := inferInstance
  haveI : Module.Flat (MvPolynomial (Fin n) K) T := inferInstance
  haveI : IsLocalization (Submonoid.map (algebraMap (MvPolynomial (Fin n) K) T)
      (nonZeroDivisors (MvPolynomial (Fin n) K)))
      (Localization (Algebra.algebraMapSubmonoid T
        (nonZeroDivisors (MvPolynomial (Fin n) K)))) :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid T
      (nonZeroDivisors (MvPolynomial (Fin n) K))) _)
  haveI : Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin n) K))
      (Localization (Algebra.algebraMapSubmonoid T
        (nonZeroDivisors (MvPolynomial (Fin n) K)))) :=
    Algebra.FormallyEtale.localization_map (R := MvPolynomial (Fin n) K) (S := T)
      (nonZeroDivisors (MvPolynomial (Fin n) K))
  haveI : Algebra.EssFiniteType (FractionRing (MvPolynomial (Fin n) K))
      (Localization (Algebra.algebraMapSubmonoid T
        (nonZeroDivisors (MvPolynomial (Fin n) K)))) :=
    Algebra.EssFiniteType.of_comp (MvPolynomial (Fin n) K) _ _
  haveI : IsReduced (Localization (Algebra.algebraMapSubmonoid T
      (nonZeroDivisors (MvPolynomial (Fin n) K)))) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing (MvPolynomial (Fin n) K)) _
  refine ⟨fun x hx => ?_⟩
  have h0 : algebraMap T (Localization (Algebra.algebraMapSubmonoid T
      (nonZeroDivisors (MvPolynomial (Fin n) K)))) x = 0 := (hx.map _).eq_zero
  rw [IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid T
    (nonZeroDivisors (MvPolynomial (Fin n) K)))] at h0
  obtain ⟨⟨y, t, ht, hty⟩, hmx⟩ := h0
  refine Module.Flat.isSMulRegular_of_nonZeroDivisors (M := T) ht ?_
  simpa [Algebra.smul_def, hty] using hmx

/-- **A smooth algebra over a field is reduced.**

PROVEN from `Algebra.IsStandardSmooth.isReduced_of_field` by the standard
open cover on which a smooth algebra is standard smooth.

Concretely: let `x` be nilpotent and nonzero.  Its annihilator is a proper
ideal, so it lies in a maximal ideal `m`; `Algebra.smoothLocus_eq_univ` says
`S` is smooth at `m`, so `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`
supplies `f ∉ m` with `S_f` standard smooth, hence reduced.  Then `x` dies in
`S_f`, i.e. `fᵏ * x = 0` for some `k`, i.e. `fᵏ` annihilates `x`, so
`fᵏ ∈ m` and `f ∈ m` — contradiction. -/
theorem Algebra.Smooth.isReduced_of_isField {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (hR : IsField R) [Algebra.Smooth R S] : IsReduced S := by
  letI : Field R := hR.toField
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  have hne : (Submodule.span S {x}).annihilator ≠ ⊤ := by
    intro h
    refine hx0 ?_
    have h1 : (1 : S) ∈ (Submodule.span S {x}).annihilator := h ▸ Submodule.mem_top
    simpa using (Submodule.mem_annihilator_span_singleton x (1 : S)).mp h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI : m.IsPrime := hm.isPrime
  haveI : Algebra.IsSmoothAt R m :=
    Set.eq_univ_iff_forall.mp (Algebra.smoothLocus_eq_univ (R := R) (A := S)) ⟨m, ‹_›⟩
  obtain ⟨f, hf, hfs⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R m
  haveI : IsReduced (Localization.Away f) := Algebra.IsStandardSmooth.isReduced_of_field R _
  have h0 : algebraMap S (Localization.Away f) x = 0 := (hx.map _).eq_zero
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at h0
  obtain ⟨⟨y, k, hk⟩, hmx⟩ := h0
  refine hf (hm.isPrime.mem_of_pow_mem k (hle ?_))
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, show f ^ k = y from hk]
  exact hmx

/-- **A smooth ring homomorphism out of a field has reduced target** — the
`RingHom` restatement of `Algebra.Smooth.isReduced_of_isField`, which is the
shape the scheme-theoretic `HasRingHomProperty` API produces. -/
theorem RingHom.Smooth.isReduced_of_isField {R S : Type u} [CommRing R] [CommRing S]
    {φ : R →+* S} (hR : IsField R) (hφ : φ.Smooth) : IsReduced S := by
  letI := φ.toAlgebra
  haveI : Algebra.Smooth R S := hφ
  exact Algebra.Smooth.isReduced_of_isField hR

namespace AlgebraicGeometry

/-- **A scheme smooth over a field is reduced.**

PROVEN from `RingHom.Smooth.isReduced_of_isField` by an affine cover: each
`X.affineCover.X i` is affine, the composite `X.affineCover.f i ≫ f` is smooth
(open immersions are smooth of relative dimension `0`), and
`HasRingHomProperty.appTop` turns that into `RingHom.Smooth` of the map
`Γ(Spec K, ⊤) ⟶ Γ(X.affineCover.X i, ⊤)`.  The source of that map is a field by
transport along `Scheme.ΓSpecIso`, so the leaf applies and gives the ring-level
reducedness, whence `isReduced_of_isAffine_isReduced` and
`IsReduced.of_openCover`. -/
theorem isReduced_of_smooth_over_field {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] : IsReduced X := by
  haveI hK : _root_.IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  haveI : ∀ i, IsReduced (X.affineCover.X i) := by
    intro i
    haveI : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      RingHom.Smooth.isReduced_of_isField hK
        (HasRingHomProperty.appTop (@Smooth) (X.affineCover.f i ≫ f) inferInstance)
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ X.affineCover

/-- **Smooth morphisms are geometrically reduced.**

PROVEN from `isReduced_of_smooth_over_field`: `geometrically IsReduced f` asks,
for every field `K`, every `y : Spec K ⟶ Y` and every pullback square over
`(f, y)`, that the total space be reduced — and the second leg of such a square
is a base change of `f`, hence smooth, hence has reduced source.

This is not registered as an `instance`: mathlib already carries the converse
`AlgebraicGeometry.smooth_of_grpObj [GeometricallyReduced f] : Smooth f` for
group schemes, and keeping both directions out of instance search avoids any
risk of a loop. -/
theorem GeometricallyReduced.of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f where
  geometrically_isReduced := by
    intro K _ y Z fst snd h
    haveI : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
    exact isReduced_of_smooth_over_field snd

end AlgebraicGeometry

/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup
import Fermat.FLT.EllipticCurve.TorsionCard
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!

Let E be an elliptic curve over the field of fractions k
of a DVR, with good reduction. Let n be a positive
integer which is nonzero in k.
Then the Galois representation on the n-torsion points
over k^sep is unramified.

This is the easy direction of the criterion of Néron–Ogg–Shafarevich;
see for example [Silverman, *The Arithmetic of Elliptic Curves*, VII.7.1]
or [Serre–Tate, *Good reduction of abelian varieties*, Theorem 1
for the general abelian variety case].

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points

-- let R be a discrete valuation ring with field of fractions k
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]

-- Let E/k be an elliptic curve with good reduction over R. Note that mathlib's
-- `HasGoodReduction` asks that the given Weierstrass equation for E is a minimal
-- integral equation whose discriminant has valuation 1; this loses no generality
-- because every elliptic curve over k is isomorphic to one given by a minimal
-- equation (`WeierstrassCurve.exists_isMinimal`).
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]

-- Let n be a natural which is nonzero in k
variable (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]

-- Let ksep be a separable closure of k (`DecidableEq` is needed for the group law on points)
variable (ksep : Type*) [Field ksep] [Algebra k ksep] [IsSepClosure k ksep] [DecidableEq ksep]

-- Let 𝒪 be a valuation subring of ksep. This is arbitrary here; the hypothesis
-- that it lies above R is `h𝒪` in the theorem below.
variable (𝒪 : ValuationSubring ksep)

set_option backward.isDefEq.respectTransparency false in
open Polynomial in
/-- **Roots of unit-leading-coefficient polynomials are integral**
(PROVEN 2026-07-17, step (i) of the Néron–Ogg–Shafarevich easy
direction): if all coefficients of `f` lie in a valuation subring and
the inverse of the leading coefficient does too, then every root lies
in the subring — otherwise the leading term of `f(x) = 0` strictly
dominates the others. -/
theorem ValuationSubring.mem_of_root_of_inv_leadingCoeff_mem
    {K : Type*} [Field K] (A : ValuationSubring K) {f : Polynomial K}
    (hfne : f ≠ 0) (hcoeff : ∀ i, f.coeff i ∈ A)
    (hlc : (f.leadingCoeff)⁻¹ ∈ A)
    {x : K} (hroot : f.eval x = 0) : x ∈ A := by
  by_contra hx
  rw [← A.valuation_le_one_iff, not_le] at hx
  set d := f.natDegree with hd
  have hd1 : 1 ≤ d := by
    by_contra hd0
    have hdz : f.natDegree = 0 := by omega
    have hfC := Polynomial.eq_C_of_natDegree_eq_zero hdz
    rw [hfC, Polynomial.eval_C] at hroot
    exact hfne (by rw [hfC, hroot, Polynomial.C_0])
  have hlcne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hfne
  -- the valuation of the leading coefficient is 1
  have h1 : A.valuation f.leadingCoeff ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (hcoeff _)
  have h2 : A.valuation (f.leadingCoeff)⁻¹ ≤ 1 :=
    (A.valuation_le_one_iff _).mpr hlc
  have hab : A.valuation f.leadingCoeff *
      A.valuation (f.leadingCoeff)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hlcne, map_one]
  have hb1 : (1 : A.ValueGroup) ≤ A.valuation (f.leadingCoeff)⁻¹ := by
    calc (1 : A.ValueGroup) =
        A.valuation f.leadingCoeff * A.valuation (f.leadingCoeff)⁻¹ :=
          hab.symm
      _ ≤ 1 * A.valuation (f.leadingCoeff)⁻¹ := mul_le_mul_left h1 _
      _ = A.valuation (f.leadingCoeff)⁻¹ := one_mul _
  have hvlc : A.valuation f.leadingCoeff = 1 := by
    have hinv1 : A.valuation (f.leadingCoeff)⁻¹ = 1 :=
      le_antisymm h2 hb1
    rw [hinv1, mul_one] at hab
    exact hab
  -- split off the leading term
  have hsplit : f.coeff d * x ^ d =
      -(∑ i ∈ Finset.range d, f.coeff i * x ^ i) := by
    have hev := hroot
    rw [Polynomial.eval_eq_sum_range, ← hd, Finset.sum_range_succ]
      at hev
    linear_combination hev
  -- valuations
  have hL : A.valuation (f.coeff d * x ^ d) = A.valuation x ^ d := by
    rw [map_mul, map_pow, show f.coeff d = f.leadingCoeff from rfl,
      hvlc, one_mul]
  have hR : A.valuation (∑ i ∈ Finset.range d, f.coeff i * x ^ i) ≤
      A.valuation x ^ (d - 1) := by
    refine Valuation.map_sum_le _ (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc A.valuation (f.coeff i) * A.valuation x ^ i ≤
        1 * A.valuation x ^ i :=
          mul_le_mul_left ((A.valuation_le_one_iff _).mpr (hcoeff i)) _
      _ = A.valuation x ^ i := one_mul _
      _ ≤ A.valuation x ^ (d - 1) :=
          pow_le_pow_right₀ (le_of_lt hx) (by omega)
  have hcombined : A.valuation x ^ d ≤ A.valuation x ^ (d - 1) := by
    rw [← hL, hsplit, Valuation.map_neg]
    exact hR
  have hstrict : A.valuation x ^ (d - 1) < A.valuation x ^ d :=
    pow_lt_pow_right₀ hx (by omega)
  exact absurd hcombined (not_le.mpr hstrict)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsSepClosure k ksep] in
open Polynomial WeierstrassCurve WeierstrassCurve.Affine in
/-- **Torsion abscissas are integral** (PROVEN 2026-07-17, the
Cassels division-polynomial argument): at good reduction with `n`
invertible in the residue field, the `x`-coordinate of every
`n`-torsion point lies in any valuation subring of `kˢᵉᵖ` above `R` —
it is a root of `ΨSqₙ`, whose coefficients are integral (the minimal
model) and whose leading coefficient `n²` is a unit. -/
theorem WeierstrassCurve.torsion_abscissa_mem
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    {x y : ksep} (h : (E⁄ksep).toAffine.Nonsingular x y)
    (htor : (n : ℤ) • (Affine.Point.some x y h : (E⁄ksep).Point) = 0) :
    x ∈ 𝒪 := by
  classical
  haveI : (E⁄ksep).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k ksep)).IsElliptic)
  haveI : DecidableEq k := Classical.decEq k
  -- `n` is a unit of `R`, hence nonzero in `ksep`
  have hnR : IsUnit (n : R) := by
    by_contra hu
    have hmem : (n : R) ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hu
    apply NeZero.ne ((n : IsLocalRing.ResidueField R))
    have h1 : IsLocalRing.residue R ((n : R)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [← map_natCast (IsLocalRing.residue R) n]
    exact h1
  have hnk : (n : k) ≠ 0 := by
    intro h0
    have h1 : algebraMap R k ((n : R)) = algebraMap R k 0 := by
      rw [map_natCast, map_zero]
      exact h0
    exact hnR.ne_zero ((IsFractionRing.injective R k) h1)
  have hnksep : (n : ksep) ≠ 0 := by
    intro h0
    apply hnk
    have h1 : algebraMap k ksep ((n : k)) = algebraMap k ksep 0 := by
      rw [map_natCast, map_zero]
      exact h0
    exact (algebraMap k ksep).injective h1
  have hnZ : ((n : ℕ) : ℤ) ≠ 0 := by
    have := NeZero.ne ((n : IsLocalRing.ResidueField R))
    intro h0
    apply this
    have : n = 0 := by exact_mod_cast h0
    rw [this]
    exact Nat.cast_zero
  -- the dictionary: the abscissa is a root of `ΨSqₙ`
  have hΨ0 : ((E⁄ksep).ΨSq (n : ℤ)).eval x = 0 := by
    have hd := (TorsionCard.smul_some_eq_zero_iff
      (E.map (algebraMap k ksep)) hnZ h).mp ?_
    · exact hd
    · exact htor
  -- integral coefficients: the curve comes from `R`
  haveI : E.IsIntegral R := inferInstance
  obtain ⟨Eint, hEint⟩ := (inferInstance : E.IsIntegral R).integral
  have hcoeffmem : ∀ i, ((E⁄ksep).ΨSq (n : ℤ)).coeff i ∈ 𝒪 := by
    intro i
    have hmap : (E⁄ksep).ΨSq (n : ℤ) =
        ((Eint.ΨSq (n : ℤ)).map (algebraMap R k)).map
          (algebraMap k ksep) := by
      rw [show (E⁄ksep) = ((Eint⁄k)⁄ksep) from by rw [hEint]]
      show ((Eint⁄k).map (algebraMap k ksep)).ΨSq (n : ℤ) = _
      rw [WeierstrassCurve.map_ΨSq]
      congr 1
      show ((Eint.map (algebraMap R k)).ΨSq (n : ℤ)) = _
      rw [WeierstrassCurve.map_ΨSq]
    rw [hmap, Polynomial.coeff_map, Polynomial.coeff_map]
    have hmem : algebraMap R k ((Eint.ΨSq (n : ℤ)).coeff i) ∈
        (algebraMap R k).range := ⟨_, rfl⟩
    rw [← h𝒪] at hmem
    exact hmem
  -- the leading coefficient is `n²`, a unit
  have hne : (E⁄ksep).ΨSq (n : ℤ) ≠ 0 := by
    intro h0
    have hc := congrArg (fun q => Polynomial.coeff q
      (((n : ℤ)).natAbs ^ 2 - 1)) h0
    simp only [Polynomial.coeff_zero] at hc
    rw [WeierstrassCurve.coeff_ΨSq] at hc
    apply hnksep
    have : ((n : ksep)) ^ 2 = 0 := by exact_mod_cast hc
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hdeg : ((E⁄ksep).ΨSq (n : ℤ)).natDegree =
      ((n : ℤ)).natAbs ^ 2 - 1 :=
    WeierstrassCurve.natDegree_ΨSq (W := (E⁄ksep))
      (by exact_mod_cast hnksep)
  have hlcinv : (((E⁄ksep).ΨSq (n : ℤ)).leadingCoeff)⁻¹ ∈ 𝒪 := by
    have hlc : ((E⁄ksep).ΨSq (n : ℤ)).leadingCoeff = ((n : ksep)) ^ 2 := by
      rw [Polynomial.leadingCoeff, hdeg, WeierstrassCurve.coeff_ΨSq]
      push_cast
      ring
    rw [hlc]
    -- `(n²)⁻¹` is the image of the `R`-inverse
    obtain ⟨u, hu⟩ := hnR
    have hprod : ((n : ksep)) ^ 2 *
        algebraMap k ksep (algebraMap R k
          (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R))) = 1 := by
      rw [show ((n : ksep)) = algebraMap k ksep (algebraMap R k ((n : R)))
        from by rw [map_natCast, map_natCast]]
      rw [← map_pow, ← map_pow, ← map_mul, ← map_mul]
      rw [show ((n : R)) ^ 2 * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) =
        ((u * u⁻¹ : Rˣ) : R) * ((u * u⁻¹ : Rˣ) : R) from by
          rw [← hu]
          push_cast
          ring]
      simp
    rw [inv_eq_of_mul_eq_one_right hprod]
    have hmem : algebraMap R k
        (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) ∈
        (algebraMap R k).range := ⟨_, rfl⟩
    rw [← h𝒪] at hmem
    exact hmem
  exact 𝒪.mem_of_root_of_inv_leadingCoeff_mem hne hcoeffmem hlcinv hΨ0

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsSepClosure k ksep] in
open Polynomial WeierstrassCurve WeierstrassCurve.Affine in
/-- **Torsion ordinates are integral**: the ordinate satisfies the
monic `y`-quadratic whose coefficients are integral once the abscissa
is. -/
theorem WeierstrassCurve.torsion_ordinate_mem
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    {x y : ksep} (h : (E⁄ksep).toAffine.Nonsingular x y)
    (htor : (n : ℤ) • (Affine.Point.some x y h : (E⁄ksep).Point) = 0) :
    y ∈ 𝒪 := by
  classical
  have hx := WeierstrassCurve.torsion_abscissa_mem R k E n ksep 𝒪 h𝒪 h htor
  haveI : E.IsIntegral R := inferInstance
  obtain ⟨Eint, hEint⟩ := (inferInstance : E.IsIntegral R).integral
  have hamem : ∀ z : R, algebraMap k ksep (algebraMap R k z) ∈ 𝒪 := by
    intro z
    have hmem : algebraMap R k z ∈ (algebraMap R k).range := ⟨_, rfl⟩
    rw [← h𝒪] at hmem
    exact hmem
  have ha1 : (E⁄ksep).a₁ ∈ 𝒪 := by
    rw [show (E⁄ksep) = ((Eint⁄k)⁄ksep) from by rw [hEint]]
    exact hamem _
  have ha2 : (E⁄ksep).a₂ ∈ 𝒪 := by
    rw [show (E⁄ksep) = ((Eint⁄k)⁄ksep) from by rw [hEint]]
    exact hamem _
  have ha3 : (E⁄ksep).a₃ ∈ 𝒪 := by
    rw [show (E⁄ksep) = ((Eint⁄k)⁄ksep) from by rw [hEint]]
    exact hamem _
  have ha4 : (E⁄ksep).a₄ ∈ 𝒪 := by
    rw [show (E⁄ksep) = ((Eint⁄k)⁄ksep) from by rw [hEint]]
    exact hamem _
  have ha6 : (E⁄ksep).a₆ ∈ 𝒪 := by
    rw [show (E⁄ksep) = ((Eint⁄k)⁄ksep) from by rw [hEint]]
    exact hamem _
  set f : Polynomial ksep := Polynomial.X ^ 2 +
    Polynomial.C ((E⁄ksep).a₁ * x + (E⁄ksep).a₃) * Polynomial.X -
    Polynomial.C (x ^ 3 + (E⁄ksep).a₂ * x ^ 2 + (E⁄ksep).a₄ * x +
      (E⁄ksep).a₆) with hfdef
  have hd2 : f.natDegree = 2 := by
    rw [hfdef]
    compute_degree!
  have hfne : f ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd2
    exact two_ne_zero hd2.symm
  have hroot : f.eval y = 0 := by
    have heq := (Affine.equation_iff _ _).mp h.1
    rw [hfdef]
    simp only [Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    linear_combination heq
  have hcoeff : ∀ i, f.coeff i ∈ 𝒪 := by
    intro i
    rw [hfdef]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    match i with
    | 0 =>
      norm_num
      exact add_mem (neg_mem ha6) (add_mem (neg_mem (mul_mem ha4 hx))
        (add_mem (neg_mem (mul_mem ha2 (pow_mem hx 2)))
          (neg_mem (pow_mem hx 3))))
    | 1 =>
      norm_num
      exact add_mem (mul_mem ha1 hx) ha3
    | 2 =>
      norm_num
    | (j + 3) =>
      norm_num
      exact zero_mem _
  have hlc : (f.leadingCoeff)⁻¹ ∈ 𝒪 := by
    have h1 : f.leadingCoeff = 1 := by
      rw [Polynomial.leadingCoeff, hd2, hfdef]
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    rw [h1, inv_one]
    exact one_mem _
  exact 𝒪.mem_of_root_of_inv_leadingCoeff_mem hfne hcoeff hlc hroot

set_option backward.isDefEq.respectTransparency false in
open Polynomial in
/-- **Distinct roots keep distinct residues under a separable
reduction** (NOS step (iii) core): if `f₀` over a valuation subring
has two distinct roots and its residue polynomial is separable, the
roots have distinct residues — otherwise the residue polynomial
acquires a square factor `(X − ξ)²`. -/
theorem ValuationSubring.residue_ne_of_roots_ne
    {K : Type*} [Field K] (A : ValuationSubring K)
    (f₀ : Polynomial A) {x₁ x₂ : A}
    (hr₁ : f₀.eval x₁ = 0) (hr₂ : f₀.eval x₂ = 0) (hne : x₁ ≠ x₂)
    (hsep : (f₀.map (IsLocalRing.residue A)).Separable) :
    IsLocalRing.residue A x₁ ≠ IsLocalRing.residue A x₂ := by
  intro hcong
  have h1 : (Polynomial.X - Polynomial.C x₁) ∣ f₀ :=
    Polynomial.dvd_iff_isRoot.mpr hr₁
  obtain ⟨g, hg⟩ := h1
  have hg2 : g.eval x₂ = 0 := by
    have hev := hr₂
    rw [hg, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hev
    rcases mul_eq_zero.mp hev with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) (fun hc => hne hc.symm)
    · exact h0
  obtain ⟨h, hh⟩ := Polynomial.dvd_iff_isRoot.mpr hg2
  have hmap := congrArg (Polynomial.map (IsLocalRing.residue A)) hg
  rw [hh] at hmap
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at hmap
  rw [← hcong] at hmap
  have hsq := hsep.squarefree
  have hdvd : (Polynomial.X -
      Polynomial.C (IsLocalRing.residue A x₁)) *
      (Polynomial.X - Polynomial.C (IsLocalRing.residue A x₁)) ∣
      f₀.map (IsLocalRing.residue A) := by
    rw [hmap]
    exact ⟨h.map _, by ring⟩
  exact Polynomial.not_isUnit_X_sub_C _ (hsq _ hdvd)

set_option warn.sorry false in
/-- (Sorry node; vendored from the FLT project.) If `E` is an elliptic curve
over `k` (given by a minimal Weierstrass equation)
with good reduction over `R`, and if `𝒪` is a valuation subring of `kˢᵉᵖ` lying above `R`,
then the inertia subgroup of `Gal(kˢᵉᵖ/k)` at `𝒪` acts trivially on the `n`-torsion
of `E(kˢᵉᵖ)`. In other words, the Galois representation on the `n`-torsion points
is unramified. -/
theorem WeierstrassCurve.torsion_unramified_of_good_reduction
    -- Assume 𝒪 lies above R, i.e. 𝒪 ∩ k = R
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    -- Then every element of the inertia subgroup at 𝒪 fixes every n-torsion point of E(ksep)
    ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P :=
  sorry

/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup
import Fermat.FLT.EllipticCurve.TorsionCardSep
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

set_option backward.isDefEq.respectTransparency false in
open Polynomial in
/-- **Inertia fixes `A`-integral roots of base-field polynomials with
separable reduction** (the master root-fixing lemma, subsuming the
`X^p − 1` and `X^p − c` cases): let `f` be a polynomial over the
valuation subring `A` whose coefficients come from the base field `k₀`
and whose residue reduction is separable. If `x ∈ A` is a root of `f`,
then every inertia element fixes `x`: the `σ`-image is again a root
(the coefficients are `σ`-fixed), it has the same residue (inertia
fixes residues), and distinct roots have distinct residues under a
separable reduction (`residue_ne_of_roots_ne`). -/
theorem ValuationSubring.inertia_fixes_root_of_separable_residue
    {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    (A : ValuationSubring K)
    (σ : A.decompositionSubgroup k₀) (hσ : σ ∈ A.inertiaSubgroup k₀)
    (f : Polynomial A)
    (hcoeff : ∀ i, ((f.coeff i : A) : K) ∈ Set.range (algebraMap k₀ K))
    (hsep : (f.map (IsLocalRing.residue A)).Separable)
    {x : K} (hxA : x ∈ A)
    (hroot : f.eval (⟨x, hxA⟩ : A) = 0) :
    (σ : K ≃ₐ[k₀] K) x = x := by
  classical
  -- σ fixes every coefficient of `f`
  have hσc : ∀ i, (σ : K ≃ₐ[k₀] K) ((f.coeff i : A) : K) =
      ((f.coeff i : A) : K) := by
    intro i
    obtain ⟨r, hr⟩ := hcoeff i
    rw [← hr]
    exact (σ : K ≃ₐ[k₀] K).commutes r
  -- the `σ`-image of the root lies in `A`
  have hcoe : ((σ • (⟨x, hxA⟩ : A) : A) : K) = (σ : K ≃ₐ[k₀] K) x := rfl
  have hσxA : (σ : K ≃ₐ[k₀] K) x ∈ A := hcoe ▸ (σ • (⟨x, hxA⟩ : A)).2
  -- the `K`-level polynomial and its two roots
  set F : Polynomial K := f.map A.subtype with hF
  have hFx : F.eval x = 0 := by
    have h1 : F.eval ((⟨x, hxA⟩ : A) : K) = A.subtype (f.eval ⟨x, hxA⟩) := by
      rw [hF, Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply A.subtype ⟨x, hxA⟩
    rw [show x = ((⟨x, hxA⟩ : A) : K) from rfl, h1, hroot, map_zero]
  -- `σ` fixes `F` coefficientwise
  have hFσ : F.map ((σ : K ≃ₐ[k₀] K) : K →+* K) = F := by
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_map, hF, Polynomial.coeff_map]
    exact hσc i
  have hFσx : F.eval ((σ : K ≃ₐ[k₀] K) x) = 0 := by
    have h1 : (F.map ((σ : K ≃ₐ[k₀] K) : K →+* K)).eval
        (((σ : K ≃ₐ[k₀] K) : K →+* K) x) =
        ((σ : K ≃ₐ[k₀] K) : K →+* K) (F.eval x) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply ((σ : K ≃ₐ[k₀] K) : K →+* K) x
    rw [hFσ] at h1
    rw [show ((σ : K ≃ₐ[k₀] K) x) = ((σ : K ≃ₐ[k₀] K) : K →+* K) x from rfl,
      h1, hFx, map_zero]
  have hroot' : f.eval (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) = 0 := by
    apply Subtype.ext
    have h1 : F.eval ((⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) : K) =
        A.subtype (f.eval ⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩) := by
      rw [hF, Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply A.subtype ⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩
    show ((f.eval (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) : A) : K) = ((0 : A) : K)
    rw [show ((f.eval (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) : A) : K) =
      A.subtype (f.eval ⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩) from rfl, ← h1]
    exact hFσx
  -- inertia fixes residues
  have hres : ∀ z : A, IsLocalRing.residue A (σ • z) =
      IsLocalRing.residue A z := by
    intro z
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := MonoidHom.mem_ker.mp hσ
    calc (σ : A.decompositionSubgroup k₀) • IsLocalRing.residue A z
        = (MulSemiringAction.toRingAut (A.decompositionSubgroup k₀)
            (IsLocalRing.ResidueField A) σ)
            (IsLocalRing.residue A z) := rfl
      _ = IsLocalRing.residue A z := by rw [h1]; rfl
  -- conclude by root separation
  by_contra hne
  have hnesub : (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) ≠ ⟨x, hxA⟩ :=
    fun hc => hne (congrArg Subtype.val hc)
  have hresne := A.residue_ne_of_roots_ne _ hroot' hroot hnesub hsep
  apply hresne
  have h9 : (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) = σ • (⟨x, hxA⟩ : A) :=
    Subtype.ext hcoe.symm
  rw [h9]
  exact hres _

set_option backward.isDefEq.respectTransparency false in
/-- **Inertia fixes the `p`-th roots of residually-nonzero constants**
(generalizing the roots-of-unity case below): if `p` is nonzero in the
residue field of `A`, `c` is an element of `A` with nonzero residue
fixed by `σ`, and `x^p = c`, then every inertia element fixes `x`. The
polynomial `X^p − c` reduces separably (derivative `p·X^{p−1}`, prime
to it as `c̄ ≠ 0`), the roots are integral, inertia fixes residues, and
distinct roots would have distinct residues. -/
theorem ValuationSubring.inertia_fixes_of_pow_eq
    {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p ≠ 0)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (σ : A.decompositionSubgroup k₀) (hσ : σ ∈ A.inertiaSubgroup k₀)
    {c : K} (hcA : c ∈ A)
    (hcres : IsLocalRing.residue A (⟨c, hcA⟩ : A) ≠ 0)
    (hσc : (σ : K ≃ₐ[k₀] K) c = c)
    {x : K} (hx : x ^ p = c) :
    (σ : K ≃ₐ[k₀] K) x = x := by
  classical
  -- membership of the roots in `A`
  have hmemA : ∀ {w : K}, w ^ p = c → w ∈ A := by
    intro w hw
    rw [← A.valuation_le_one_iff]
    by_contra hgt
    rw [not_le] at hgt
    have h1 : (1 : A.ValueGroup) < A.valuation w ^ p :=
      one_lt_pow₀ hgt hp
    rw [← map_pow, hw] at h1
    exact absurd (lt_of_lt_of_le h1
      ((A.valuation_le_one_iff c).mpr hcA)) (lt_irrefl _)
  have hxA : x ∈ A := hmemA hx
  have hσxpow : ((σ : K ≃ₐ[k₀] K) x) ^ p = c := by
    rw [← map_pow, hx, hσc]
  have hσxA : (σ : K ≃ₐ[k₀] K) x ∈ A := hmemA hσxpow
  -- inertia fixes residues
  have hres : ∀ z : A, IsLocalRing.residue A (σ • z) =
      IsLocalRing.residue A z := by
    intro z
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := MonoidHom.mem_ker.mp hσ
    calc (σ : A.decompositionSubgroup k₀) • IsLocalRing.residue A z
        = (MulSemiringAction.toRingAut (A.decompositionSubgroup k₀)
            (IsLocalRing.ResidueField A) σ)
            (IsLocalRing.residue A z) := rfl
      _ = IsLocalRing.residue A z := by rw [h1]; rfl
  have hcoe : ((σ • (⟨x, hxA⟩ : A) : A) : K) =
      (σ : K ≃ₐ[k₀] K) x := rfl
  by_contra hne
  have hr₁ : (Polynomial.X ^ p - Polynomial.C (⟨c, hcA⟩ : A) :
      Polynomial A).eval (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    apply Subtype.ext
    show ((σ : K ≃ₐ[k₀] K) x) ^ p - c = (0 : K)
    rw [hσxpow, sub_self]
  have hr₂ : (Polynomial.X ^ p - Polynomial.C (⟨c, hcA⟩ : A) :
      Polynomial A).eval (⟨x, hxA⟩ : A) = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    apply Subtype.ext
    show x ^ p - c = (0 : K)
    rw [hx, sub_self]
  have hsep : ((Polynomial.X ^ p - Polynomial.C (⟨c, hcA⟩ : A) :
      Polynomial A).map (IsLocalRing.residue A)).Separable := by
    have hmap : (Polynomial.X ^ p - Polynomial.C (⟨c, hcA⟩ : A) :
        Polynomial A).map (IsLocalRing.residue A) =
        Polynomial.X ^ p - Polynomial.C
          (IsLocalRing.residue A (⟨c, hcA⟩ : A)) := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C]
    rw [hmap]
    exact Polynomial.separable_X_pow_sub_C _ hchar hcres
  have hnesub : (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) ≠ ⟨x, hxA⟩ :=
    fun hc => hne (congrArg Subtype.val hc)
  have hresne := A.residue_ne_of_roots_ne _ hr₁ hr₂ hnesub hsep
  apply hresne
  have h9 : (⟨(σ : K ≃ₐ[k₀] K) x, hσxA⟩ : A) = σ • (⟨x, hxA⟩ : A) :=
    Subtype.ext hcoe.symm
  rw [h9]
  exact hres _

set_option backward.isDefEq.respectTransparency false in
/-- **Inertia fixes the roots of unity of order prime to the residue
characteristic** (PROVEN — step (b) of the Tate-multiplicative
derivation): if `p` is nonzero in the residue field of the valuation
subring `A`, every element of the inertia subgroup fixes every `p`-th
root of unity. The root is `A`-integral (its valuation is `1`), the
polynomial `X^p − 1` reduces separably
(`Polynomial.X_pow_sub_one_separable_iff`), inertia fixes residues, and
distinct roots would have distinct residues
(`residue_ne_of_roots_ne`). -/
theorem ValuationSubring.inertia_fixes_of_pow_eq_one
    {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p ≠ 0)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (σ : A.decompositionSubgroup k₀) (hσ : σ ∈ A.inertiaSubgroup k₀)
    {ζ : K} (hζ : ζ ^ p = 1) :
    (σ : K ≃ₐ[k₀] K) ζ = ζ := by
  classical
  -- membership of the roots in `A`
  have hmemA : ∀ {w : K}, w ^ p = 1 → w ∈ A := by
    intro w hw
    rw [← A.valuation_le_one_iff]
    by_contra hgt
    rw [not_le] at hgt
    have h1 : (1 : A.ValueGroup) < A.valuation w ^ p :=
      one_lt_pow₀ hgt hp
    rw [← map_pow, hw, map_one] at h1
    exact absurd h1 (lt_irrefl _)
  have hζA : ζ ∈ A := hmemA hζ
  have hσζpow : ((σ : K ≃ₐ[k₀] K) ζ) ^ p = 1 := by
    rw [← map_pow, hζ, map_one]
  have hσζA : (σ : K ≃ₐ[k₀] K) ζ ∈ A := hmemA hσζpow
  -- inertia fixes residues
  have hres : ∀ z : A, IsLocalRing.residue A (σ • z) =
      IsLocalRing.residue A z := by
    intro z
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := MonoidHom.mem_ker.mp hσ
    calc (σ : A.decompositionSubgroup k₀) • IsLocalRing.residue A z
        = (MulSemiringAction.toRingAut (A.decompositionSubgroup k₀)
            (IsLocalRing.ResidueField A) σ)
            (IsLocalRing.residue A z) := rfl
      _ = IsLocalRing.residue A z := by rw [h1]; rfl
  have hcoe : ((σ • (⟨ζ, hζA⟩ : A) : A) : K) =
      (σ : K ≃ₐ[k₀] K) ζ := rfl
  -- the two roots of `X^p − 1` in `A`
  by_contra hne
  have hr₁ : (Polynomial.X ^ p - 1 : Polynomial A).eval
      (⟨(σ : K ≃ₐ[k₀] K) ζ, hσζA⟩ : A) = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    apply Subtype.ext
    show ((σ : K ≃ₐ[k₀] K) ζ) ^ p - 1 = (0 : K)
    rw [hσζpow, sub_self]
  have hr₂ : (Polynomial.X ^ p - 1 : Polynomial A).eval
      (⟨ζ, hζA⟩ : A) = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    apply Subtype.ext
    show ζ ^ p - 1 = (0 : K)
    rw [hζ, sub_self]
  have hsep : ((Polynomial.X ^ p - 1 : Polynomial A).map
      (IsLocalRing.residue A)).Separable := by
    have hmap : (Polynomial.X ^ p - 1 : Polynomial A).map
        (IsLocalRing.residue A) =
        Polynomial.X ^ p - 1 := by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_one]
    rw [hmap]
    exact Polynomial.X_pow_sub_one_separable_iff.mpr hchar
  have hnesub : (⟨(σ : K ≃ₐ[k₀] K) ζ, hσζA⟩ : A) ≠ ⟨ζ, hζA⟩ :=
    fun hc => hne (congrArg Subtype.val hc)
  have hresne := A.residue_ne_of_roots_ne _ hr₁ hr₂ hnesub hsep
  apply hresne
  have h9 : (⟨(σ : K ≃ₐ[k₀] K) ζ, hσζA⟩ : A) = σ • (⟨ζ, hζA⟩ : A) :=
    Subtype.ext hcoe.symm
  rw [h9]
  exact hres _

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R k]
  [IsSepClosure k ksep] [DecidableEq ksep] in
/-- The structural homomorphism `R → 𝒪` induced by `h𝒪`. -/
noncomputable def WeierstrassCurve.RtoO
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    R →+* 𝒪 where
  toFun r := ⟨algebraMap k ksep (algebraMap R k r), by
    have hmem : algebraMap R k r ∈ (algebraMap R k).range := ⟨r, rfl⟩
    rw [← h𝒪] at hmem
    exact hmem⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R k]
  [IsSepClosure k ksep] [DecidableEq ksep] in
lemma WeierstrassCurve.RtoO_coe
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (r : R) : ((WeierstrassCurve.RtoO R k ksep 𝒪 h𝒪 r : 𝒪) : ksep) =
      algebraMap k ksep (algebraMap R k r) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsSepClosure k ksep]
  [DecidableEq ksep] in
/-- `R → 𝒪` is a local homomorphism: a unit inverse in `𝒪` descends
to `R = 𝒪 ∩ k`. -/
instance WeierstrassCurve.isLocalHom_RtoO
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    IsLocalHom (WeierstrassCurve.RtoO R k ksep 𝒪 h𝒪) := by
  constructor
  intro r hu
  have hrne : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  have hkne : algebraMap R k r ≠ 0 := fun h0 =>
    hrne (IsFractionRing.injective R k (by rw [h0, map_zero]))
  obtain ⟨u, hu'⟩ := hu
  have hval : ((WeierstrassCurve.RtoO R k ksep 𝒪 h𝒪 r : 𝒪) : ksep) *
      algebraMap k ksep ((algebraMap R k r)⁻¹) = 1 := by
    rw [WeierstrassCurve.RtoO_coe, ← map_mul, mul_inv_cancel₀ hkne,
      map_one]
  have hw : ((WeierstrassCurve.RtoO R k ksep 𝒪 h𝒪 r : 𝒪) : ksep) *
      (((u⁻¹ : 𝒪ˣ) : 𝒪) : ksep) = 1 := by
    rw [← hu']
    have h2 : ((u : 𝒪) * ((u⁻¹ : 𝒪ˣ) : 𝒪)) = 1 := by
      exact_mod_cast u.mul_inv
    exact_mod_cast congrArg (fun z : 𝒪 => (z : ksep)) h2
  have hane : ((WeierstrassCurve.RtoO R k ksep 𝒪 h𝒪 r : 𝒪) : ksep) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hval
    exact one_ne_zero hval.symm
  have heq : algebraMap k ksep ((algebraMap R k r)⁻¹) =
      (((u⁻¹ : 𝒪ˣ) : 𝒪) : ksep) :=
    mul_left_cancel₀ hane (hval.trans hw.symm)
  have hinv𝒪 : algebraMap k ksep ((algebraMap R k r)⁻¹) ∈ 𝒪 := by
    rw [heq]
    exact ((u⁻¹ : 𝒪ˣ) : 𝒪).2
  have hmem : (algebraMap R k r)⁻¹ ∈
      (𝒪.comap (algebraMap k ksep)).toSubring := hinv𝒪
  rw [h𝒪] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hrs : r * s = 1 := by
    refine IsFractionRing.injective R k ?_
    rw [map_mul, map_one, hs, mul_inv_cancel₀ hkne]
  exact ⟨⟨r, s, hrs, by rw [mul_comm]; exact hrs⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsSepClosure k ksep] in
open Polynomial WeierstrassCurve WeierstrassCurve.Affine in
/-- **Distinct torsion abscissas have distinct residues** (NOS step
(iii), `x`-level): for an odd prime `p` invertible in the residue
field, via the residue curve's separability of `preΨ'ₚ`. -/
theorem WeierstrassCurve.torsion_abscissa_residue_ne
    (hp : n.Prime) (hodd : Odd n)
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    {x₁ y₁ x₂ y₂ : ksep}
    (h₁ : (E⁄ksep).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E⁄ksep).toAffine.Nonsingular x₂ y₂)
    (ht₁ : (n : ℤ) • (Affine.Point.some x₁ y₁ h₁ : (E⁄ksep).Point) = 0)
    (ht₂ : (n : ℤ) • (Affine.Point.some x₂ y₂ h₂ : (E⁄ksep).Point) = 0)
    (hne : x₁ ≠ x₂) (hm₁ : x₁ ∈ 𝒪) (hm₂ : x₂ ∈ 𝒪) :
    IsLocalRing.residue 𝒪 ⟨x₁, hm₁⟩ ≠
      IsLocalRing.residue 𝒪 ⟨x₂, hm₂⟩ := by
  classical
  haveI : (E⁄ksep).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k ksep)).IsElliptic)
  haveI : DecidableEq k := Classical.decEq k
  have hnR : IsUnit (n : R) := by
    by_contra hu
    have hmem : (n : R) ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hu
    apply NeZero.ne ((n : IsLocalRing.ResidueField R))
    have h1 : IsLocalRing.residue R ((n : R)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [← map_natCast (IsLocalRing.residue R) n]
    exact h1
  have hnZ : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply NeZero.ne ((n : IsLocalRing.ResidueField R))
    have : n = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]
  have hroot : ∀ {x y : ksep} (h : (E⁄ksep).toAffine.Nonsingular x y),
      (n : ℤ) • (Affine.Point.some x y h : (E⁄ksep).Point) = 0 →
      ((E⁄ksep).preΨ' n).eval x = 0 := by
    intro x y h ht
    have hΨ := (TorsionCard.smul_some_eq_zero_iff
      (E.map (algebraMap k ksep)) hnZ h).mp ht
    rw [WeierstrassCurve.ΨSq_ofNat,
      if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one,
      Polynomial.eval_pow] at hΨ
    exact pow_eq_zero_iff two_ne_zero |>.mp hΨ
  set φ := WeierstrassCurve.RtoO R k ksep 𝒪 h𝒪 with hφdef
  set f₀ : Polynomial 𝒪 :=
    ((WeierstrassCurve.integralModel R E).preΨ' n).map φ with hf₀def
  have hcomp : (𝒪.subtype).comp φ =
      (algebraMap k ksep).comp (algebraMap R k) := by
    ext r
    exact WeierstrassCurve.RtoO_coe R k ksep 𝒪 h𝒪 r
  have hf₀K : f₀.map 𝒪.subtype = (E⁄ksep).preΨ' n := by
    rw [hf₀def, Polynomial.map_map, hcomp]
    have hEE : ((WeierstrassCurve.integralModel R E)⁄k) = E :=
      WeierstrassCurve.baseChange_integralModel_eq R E
    rw [show (E⁄ksep) = (((WeierstrassCurve.integralModel R E)⁄k)⁄ksep)
      from by rw [hEE]]
    show _ = (((WeierstrassCurve.integralModel R E).map
      (algebraMap R k)).map (algebraMap k ksep)).preΨ' n
    rw [WeierstrassCurve.map_preΨ', WeierstrassCurve.map_preΨ',
      Polynomial.map_map]
  have hrO : ∀ {x y : ksep} (h : (E⁄ksep).toAffine.Nonsingular x y)
      (_ : (n : ℤ) • (Affine.Point.some x y h : (E⁄ksep).Point) = 0)
      (hm : x ∈ 𝒪), f₀.eval ⟨x, hm⟩ = 0 := by
    intro x y h ht hm
    apply Subtype.ext
    calc (𝒪.subtype) (f₀.eval ⟨x, hm⟩)
        = (f₀.map 𝒪.subtype).eval (𝒪.subtype ⟨x, hm⟩) :=
          (Polynomial.eval_map_apply _ _).symm
      _ = ((E⁄ksep).preΨ' n).eval x := by rw [hf₀K]; rfl
      _ = 0 := hroot h ht
  set ψ := IsLocalRing.ResidueField.map φ with hψdef
  set Ered := (E.reduction R).map ψ with hEreddef
  haveI hredell : (E.reduction R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp
      inferInstance
  haveI : Ered.IsElliptic := inferInstanceAs
    (((E.reduction R).map ψ).IsElliptic)
  have hf₀res : f₀.map (IsLocalRing.residue 𝒪) = Ered.preΨ' n := by
    rw [hf₀def, Polynomial.map_map]
    rw [show (IsLocalRing.residue 𝒪).comp φ =
        ψ.comp (IsLocalRing.residue R) from by
      ext r
      exact (IsLocalRing.ResidueField.map_residue φ r).symm]
    rw [hEreddef, WeierstrassCurve.map_preΨ',
      show (E.reduction R).preΨ' n =
        ((WeierstrassCurve.integralModel R E).preΨ' n).map
          (IsLocalRing.residue R) from by
        rw [WeierstrassCurve.reduction, WeierstrassCurve.map_preΨ'],
      Polynomial.map_map]
  have hnκ : ((n : ℕ) : IsLocalRing.ResidueField 𝒪) ≠ 0 := by
    have hunit : IsUnit (IsLocalRing.residue 𝒪 (φ ((n : R)))) :=
      (hnR.map φ).map (IsLocalRing.residue 𝒪)
    have hcast : IsLocalRing.residue 𝒪 (φ ((n : R))) =
        ((n : ℕ) : IsLocalRing.ResidueField 𝒪) := by
      rw [map_natCast, map_natCast]
    rw [hcast] at hunit
    exact hunit.ne_zero
  have hsepred : (f₀.map (IsLocalRing.residue 𝒪)).Separable := by
    rw [hf₀res]
    haveI : DecidableEq (IsLocalRing.ResidueField 𝒪) := Classical.decEq _
    have hsep' := TorsionCard.separable_preΨ' Ered hp hodd hnκ
    rwa [show ((Ered⁄(IsLocalRing.ResidueField 𝒪))).preΨ' n =
        Ered.preΨ' n from by
      show ((Ered.map (algebraMap _ _)).preΨ' n) = _
      rw [WeierstrassCurve.map_preΨ', Algebra.algebraMap_self,
        Polynomial.map_id]] at hsep'
  exact 𝒪.residue_ne_of_roots_ne f₀ (hrO h₁ ht₁ hm₁) (hrO h₂ ht₂ hm₂)
    (fun hc => hne (congrArg Subtype.val hc)) hsepred

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
omit [IsSepClosure k ksep] in
open Polynomial WeierstrassCurve WeierstrassCurve.Affine in
/-- **Congruent torsion ordinates above one abscissa coincide** (NOS
step (iii), `y`-level): two points above `x` differ by
`ψ₂ = 2y + a₁x + a₃`, whose square is `Ψ₂Sq(x)` on the curve; the
residue of `Ψ₂Sq(x)` is nonzero by the residue curve's
`Ψ₂Sq`/`preΨ'ₚ` Bézout identity at the abscissa residue, so
congruent ordinates are equal. -/
theorem WeierstrassCurve.torsion_ordinate_eq_of_residue_eq
    (hp : n.Prime) (hodd : Odd n)
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    {x y₁ y₂ : ksep}
    (h₁ : (E⁄ksep).toAffine.Nonsingular x y₁)
    (h₂ : (E⁄ksep).toAffine.Nonsingular x y₂)
    (ht₁ : (n : ℤ) • (Affine.Point.some x y₁ h₁ : (E⁄ksep).Point) = 0)
    (hm : x ∈ 𝒪) (hm₁ : y₁ ∈ 𝒪) (hm₂ : y₂ ∈ 𝒪)
    (hcong : IsLocalRing.residue 𝒪 ⟨y₁, hm₁⟩ =
      IsLocalRing.residue 𝒪 ⟨y₂, hm₂⟩) : y₁ = y₂ := by
  classical
  haveI : (E⁄ksep).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k ksep)).IsElliptic)
  haveI : DecidableEq k := Classical.decEq k
  by_contra hne
  have heq₁ := (Affine.equation_iff _ _).mp h₁.1
  have heq₂ := (Affine.equation_iff _ _).mp h₂.1
  have hfac : (y₁ - y₂) *
      (y₁ + y₂ + (E⁄ksep).a₁ * x + (E⁄ksep).a₃) = 0 := by
    linear_combination heq₁ - heq₂
  have hsum : y₁ + y₂ + (E⁄ksep).a₁ * x + (E⁄ksep).a₃ = 0 := by
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · exact h0
  have hdiff : y₁ - y₂ = 2 * y₁ + (E⁄ksep).a₁ * x + (E⁄ksep).a₃ := by
    linear_combination -hsum
  have hb2 : (2 * y₁ + (E⁄ksep).a₁ * x + (E⁄ksep).a₃) ^ 2 =
      ((E⁄ksep).Ψ₂Sq).eval x := by
    have h := congrArg (Polynomial.evalEvalRingHom x y₁)
      ((E⁄ksep).ψ₂_sq)
    simp only [map_add, map_mul, map_pow, map_ofNat,
      Polynomial.coe_evalEvalRingHom, Polynomial.evalEval_C] at h
    rw [show (E⁄ksep).toAffine.polynomial.evalEval x y₁ = 0 from
      h₁.1] at h
    rw [show ((E⁄ksep).ψ₂).evalEval x y₁ =
        2 * y₁ + (E⁄ksep).a₁ * x + (E⁄ksep).a₃ from by
      rw [WeierstrassCurve.ψ₂, Affine.evalEval_polynomialY]] at h
    rw [h]
    ring
  have hdm : y₁ - y₂ ∈ 𝒪 := sub_mem hm₁ hm₂
  have hdres : IsLocalRing.residue 𝒪 ⟨y₁ - y₂, hdm⟩ = 0 := by
    have hsub : (⟨y₁ - y₂, hdm⟩ : 𝒪) = ⟨y₁, hm₁⟩ - ⟨y₂, hm₂⟩ :=
      Subtype.ext (by simp)
    rw [hsub, map_sub, hcong, sub_self]
  have hnR : IsUnit (n : R) := by
    by_contra hu
    have hmem : (n : R) ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hu
    apply NeZero.ne ((n : IsLocalRing.ResidueField R))
    have h1 : IsLocalRing.residue R ((n : R)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [← map_natCast (IsLocalRing.residue R) n]
    exact h1
  have hnZ : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply NeZero.ne ((n : IsLocalRing.ResidueField R))
    have : n = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]
  set φ := WeierstrassCurve.RtoO R k ksep 𝒪 h𝒪 with hφdef
  have hcomp : (𝒪.subtype).comp φ =
      (algebraMap k ksep).comp (algebraMap R k) := by
    ext r
    exact WeierstrassCurve.RtoO_coe R k ksep 𝒪 h𝒪 r
  have hEE : ((WeierstrassCurve.integralModel R E)⁄k) = E :=
    WeierstrassCurve.baseChange_integralModel_eq R E
  set ψr := IsLocalRing.ResidueField.map φ with hψdef
  set Ered := (E.reduction R).map ψr with hEreddef
  haveI hredell : (E.reduction R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp
      inferInstance
  haveI : Ered.IsElliptic := inferInstanceAs
    (((E.reduction R).map ψr).IsElliptic)
  have hresidue_comp : (IsLocalRing.residue 𝒪).comp φ =
      ψr.comp (IsLocalRing.residue R) := by
    ext r
    exact (IsLocalRing.ResidueField.map_residue φ r).symm
  -- the two-face principle for integral-model polynomials
  have hface : ∀ (q : Polynomial R) (v : 𝒪)
      (hmem : (q.map ((algebraMap k ksep).comp
        (algebraMap R k))).eval (v : ksep) ∈ 𝒪),
      IsLocalRing.residue 𝒪 ⟨_, hmem⟩ =
        (q.map (ψr.comp (IsLocalRing.residue R))).eval
          (IsLocalRing.residue 𝒪 v) := by
    intro q v hmem
    have hcoe : (((q.map φ).eval v : 𝒪) : ksep) =
        (q.map ((algebraMap k ksep).comp
          (algebraMap R k))).eval (v : ksep) := by
      have h1 := Polynomial.eval_map_apply (p := q.map φ) 𝒪.subtype v
      rw [Polynomial.map_map, hcomp] at h1
      exact h1.symm
    have hc : (⟨_, hmem⟩ : 𝒪) = (q.map φ).eval v :=
      Subtype.ext hcoe.symm
    rw [hc, ← Polynomial.eval_map_apply (IsLocalRing.residue 𝒪),
      Polynomial.map_map, hresidue_comp]
  -- the reduction identifications
  have hqΨ : ((WeierstrassCurve.integralModel R E).Ψ₂Sq).map
      ((algebraMap k ksep).comp (algebraMap R k)) =
      (E⁄ksep).Ψ₂Sq := by
    rw [← Polynomial.map_map, ← WeierstrassCurve.map_Ψ₂Sq,
      ← WeierstrassCurve.map_Ψ₂Sq]
    rw [show ((WeierstrassCurve.integralModel R E).map
      (algebraMap R k)) = E from hEE]
    rfl
  have hqpre : ((WeierstrassCurve.integralModel R E).preΨ' n).map
      ((algebraMap k ksep).comp (algebraMap R k)) =
      (E⁄ksep).preΨ' n := by
    rw [← Polynomial.map_map, ← WeierstrassCurve.map_preΨ',
      ← WeierstrassCurve.map_preΨ']
    rw [show ((WeierstrassCurve.integralModel R E).map
      (algebraMap R k)) = E from hEE]
    rfl
  have hqΨred : ((WeierstrassCurve.integralModel R E).Ψ₂Sq).map
      (ψr.comp (IsLocalRing.residue R)) = Ered.Ψ₂Sq := by
    rw [← Polynomial.map_map, hEreddef, WeierstrassCurve.map_Ψ₂Sq,
      show (E.reduction R).Ψ₂Sq =
        ((WeierstrassCurve.integralModel R E).Ψ₂Sq).map
          (IsLocalRing.residue R) from by
        rw [WeierstrassCurve.reduction, WeierstrassCurve.map_Ψ₂Sq]]
  have hqprered : ((WeierstrassCurve.integralModel R E).preΨ' n).map
      (ψr.comp (IsLocalRing.residue R)) = Ered.preΨ' n := by
    rw [← Polynomial.map_map, hEreddef, WeierstrassCurve.map_preΨ',
      show (E.reduction R).preΨ' n =
        ((WeierstrassCurve.integralModel R E).preΨ' n).map
          (IsLocalRing.residue R) from by
        rw [WeierstrassCurve.reduction, WeierstrassCurve.map_preΨ']]
  -- residue of `Ψ₂Sq(x)` is zero
  have hΨmem : (((WeierstrassCurve.integralModel R E).Ψ₂Sq).map
      ((algebraMap k ksep).comp (algebraMap R k))).eval
        ((⟨x, hm⟩ : 𝒪) : ksep) ∈ 𝒪 := by
    rw [hqΨ, ← hb2, ← hdiff]
    exact pow_mem hdm 2
  have hΨres0 : (Ered.Ψ₂Sq).eval
      (IsLocalRing.residue 𝒪 ⟨x, hm⟩) = 0 := by
    rw [← hqΨred, ← hface _ ⟨x, hm⟩ hΨmem]
    have hsq : (⟨_, hΨmem⟩ : 𝒪) = (⟨y₁ - y₂, hdm⟩ : 𝒪) ^ 2 :=
      Subtype.ext (by
        push_cast
        rw [hqΨ, ← hb2, ← hdiff])
    rw [hsq, map_pow, hdres, zero_pow two_ne_zero]
  -- residue of `preΨ'ₚ(x)` is zero
  have hrootK : ((E⁄ksep).preΨ' n).eval x = 0 := by
    have hΨ := (TorsionCard.smul_some_eq_zero_iff
      (E.map (algebraMap k ksep)) hnZ h₁).mp ht₁
    rw [WeierstrassCurve.ΨSq_ofNat,
      if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one,
      Polynomial.eval_pow] at hΨ
    exact pow_eq_zero_iff two_ne_zero |>.mp hΨ
  have hpremem : (((WeierstrassCurve.integralModel R E).preΨ' n).map
      ((algebraMap k ksep).comp (algebraMap R k))).eval
        ((⟨x, hm⟩ : 𝒪) : ksep) ∈ 𝒪 := by
    rw [hqpre, hrootK]
    exact zero_mem _
  have hpre0 : (Ered.preΨ' n).eval
      (IsLocalRing.residue 𝒪 ⟨x, hm⟩) = 0 := by
    rw [← hqprered, ← hface _ ⟨x, hm⟩ hpremem]
    have hz : (⟨_, hpremem⟩ : 𝒪) = 0 :=
      Subtype.ext (by push_cast; rw [hqpre, hrootK])
    rw [hz, map_zero]
  -- the residue-curve Bézout identity gives `1 = 0`
  have hnκ : ((n : ℕ) : IsLocalRing.ResidueField 𝒪) ≠ 0 := by
    have hunit : IsUnit (IsLocalRing.residue 𝒪 (φ ((n : R)))) :=
      (hnR.map φ).map (IsLocalRing.residue 𝒪)
    have hcast : IsLocalRing.residue 𝒪 (φ ((n : R))) =
        ((n : ℕ) : IsLocalRing.ResidueField 𝒪) := by
      rw [map_natCast, map_natCast]
    rw [hcast] at hunit
    exact hunit.ne_zero
  haveI : DecidableEq (IsLocalRing.ResidueField 𝒪) := Classical.decEq _
  obtain ⟨F, G, hFG⟩ := TorsionCard.isCoprime_Ψ₂Sq_preΨ' Ered hp hodd hnκ
  have hid : ((Ered⁄(IsLocalRing.ResidueField 𝒪))) = Ered := by
    show Ered.map (algebraMap _ _) = Ered
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hid] at hFG
  have hev := congrArg (Polynomial.eval
    (IsLocalRing.residue 𝒪 ⟨x, hm⟩)) hFG
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_one, hΨres0, hpre0, mul_zero, mul_zero,
    add_zero] at hev
  exact zero_ne_one hev

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsSepClosure k ksep] in
open Polynomial WeierstrassCurve WeierstrassCurve.Affine in
/-- **The Néron–Ogg–Shafarevich criterion, easy direction** (PROVEN
2026-07-17 for odd primes, which is what the tree consumes): if `E`
has good reduction over `R` and the odd prime `n` is invertible in
the residue field, the inertia subgroup at any valuation subring `𝒪`
of `kˢᵉᵖ` above `R` acts trivially on the `n`-torsion: torsion
coordinates are integral, inertia fixes their residues, and the
mod-`𝔪` injectivity through the residue curve's separability forces
fixed points. -/
theorem WeierstrassCurve.torsion_unramified_of_good_reduction
    (hp : n.Prime) (hodd : Odd n)
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup k,
      ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P := by
  classical
  haveI : (E⁄ksep).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k ksep)).IsElliptic)
  intro σ hσ P hP
  have hres : ∀ z : 𝒪, IsLocalRing.residue 𝒪 (σ • z) =
      IsLocalRing.residue 𝒪 z := by
    intro z
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := MonoidHom.mem_ker.mp hσ
    calc (σ : 𝒪.decompositionSubgroup k) • IsLocalRing.residue 𝒪 z
        = (MulSemiringAction.toRingAut (𝒪.decompositionSubgroup k)
            (IsLocalRing.ResidueField 𝒪) σ)
            (IsLocalRing.residue 𝒪 z) := rfl
      _ = IsLocalRing.residue 𝒪 z := by rw [h1]; rfl
  have hcoe : ∀ z : 𝒪, ((σ • z : 𝒪) : ksep) =
      ((σ : ksep ≃ₐ[k] ksep)).toAlgHom (z : ksep) := fun z => rfl
  have hPtor : (n : ℤ) • P = 0 := hP
  cases P with
  | zero => rfl
  | @some x y h =>
    have htor : (n : ℤ) •
        (Affine.Point.some x y h : (E⁄ksep).Point) = 0 := hPtor
    have hxm := WeierstrassCurve.torsion_abscissa_mem R k E n ksep 𝒪
      h𝒪 h htor
    have hym := WeierstrassCurve.torsion_ordinate_mem R k E n ksep 𝒪
      h𝒪 h htor
    set σf := ((σ : ksep ≃ₐ[k] ksep)).toAlgHom with hσfdef
    rw [Affine.Point.map_some]
    have hns' : (E⁄ksep).toAffine.Nonsingular (σf x) (σf y) :=
      (WeierstrassCurve.Affine.baseChange_nonsingular (W := E)
        σf.injective x y).mpr (show (E⁄ksep).Nonsingular x y from h)
    -- the image is torsion
    have h1 : Affine.Point.map σf (Affine.Point.some x y h) =
        (Affine.Point.some (σf x) (σf y) hns' : (E⁄ksep).Point) :=
      Affine.Point.map_some _ h
    have hmaptor : (n : ℤ) • (Affine.Point.some (σf x) (σf y) hns' :
        (E⁄ksep).Point) = 0 := by
      rw [← h1, ← map_zsmul, htor, map_zero]
    -- memberships of the image coordinates
    have hσxm : σf x ∈ 𝒪 := by
      have := hcoe ⟨x, hxm⟩
      rw [← this]
      exact Subtype.mem _
    have hσym : σf y ∈ 𝒪 := by
      have := hcoe ⟨y, hym⟩
      rw [← this]
      exact Subtype.mem _
    -- inertia gives congruent residues
    have hrx : IsLocalRing.residue 𝒪 ⟨σf x, hσxm⟩ =
        IsLocalRing.residue 𝒪 ⟨x, hxm⟩ := by
      have h1 := hres ⟨x, hxm⟩
      rwa [show (σ • (⟨x, hxm⟩ : 𝒪)) = ⟨σf x, hσxm⟩ from
        Subtype.ext (hcoe ⟨x, hxm⟩)] at h1
    have hry : IsLocalRing.residue 𝒪 ⟨σf y, hσym⟩ =
        IsLocalRing.residue 𝒪 ⟨y, hym⟩ := by
      have h1 := hres ⟨y, hym⟩
      rwa [show (σ • (⟨y, hym⟩ : 𝒪)) = ⟨σf y, hσym⟩ from
        Subtype.ext (hcoe ⟨y, hym⟩)] at h1
    -- the abscissae agree
    have hxeq : σf x = x := by
      by_contra hne
      exact WeierstrassCurve.torsion_abscissa_residue_ne R k E n ksep 𝒪
        hp hodd h𝒪 hns' h hmaptor htor hne hσxm hxm hrx
    -- transport the image point to the common abscissa
    have hns'' : (E⁄ksep).toAffine.Nonsingular x (σf y) :=
      hxeq ▸ hns'
    have hmaptor' : (n : ℤ) • (Affine.Point.some x (σf y) hns'' :
        (E⁄ksep).Point) = 0 := by
      have := hmaptor
      have hpt : (Affine.Point.some (σf x) (σf y) hns' :
          (E⁄ksep).Point) = Affine.Point.some x (σf y) hns'' := by
        congr 1
      rwa [hpt] at this
    -- the ordinates agree
    have hyeq : σf y = y :=
      WeierstrassCurve.torsion_ordinate_eq_of_residue_eq R k E n ksep 𝒪
        hp hodd h𝒪 hns'' h hmaptor' hxm hσym hym hry
    -- conclude by congruence
    congr 1


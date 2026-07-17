/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup

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

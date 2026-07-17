/-
PhiPsiCoprime.lean — own work for the Fermat project.

The direct coprimality of the division polynomials `Φₙ` and `ΨSqₙ`
over a field with `Δ ≠ 0`, replacing the resultant-formula node. A
common root over the algebraic closure lifts to a curve point whose
`ψ`-values form a normalised EDS with `w₁ = 1`; `ΨSq`-vanishing gives
`wₙ = 0`, `Φ`-vanishing gives `wₙ₊₁ wₙ₋₁ = 0` (through the definition
`Φₙ = X ΨSqₙ − preΨₙ₊₁ preΨₙ₋₁ ⬝ parity` and the on-curve identity
`Ψ₂Sq(x₀) = ψ₂(P)²`), so the rank of apparition divides two
consecutive integers — impossible — unless the rank has adjacent
zeros, which forces the degenerate seeds `(ψ₂, ψ₃) = (0,0)` or
`(ψ₃, ψ₄) = (0,0)`, excluded by the small Bézout certificates
`F ⬝ Ψ₂Sq + G ⬝ Ψ₃ = −Δ²` and `F ⬝ Ψ₃ + G ⬝ preΨ₄ = Δ⁴`.
-/
module

public import Fermat.FLT.Mathlib.NumberTheory.EDSRank
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Points
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

namespace PhiPsiCoprime

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticDivisibilitySequence
open scoped Polynomial.Bivariate

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

set_option warn.sorry false in
/-- **The `(2,3)` Bézout certificate** (sorry node, sympy-extracted
cofactors pending): `F ⬝ Ψ₂Sq + G ⬝ Ψ₃ = −Δ²`, so `Ψ₂Sq` and `Ψ₃`
cannot vanish together when `Δ ≠ 0`. -/
theorem psi23_not_both_zero (hΔ : W.Δ ≠ 0) (x₀ : K)
    (h2 : (W.Ψ₂Sq).eval x₀ = 0) (h3 : (W.Ψ₃).eval x₀ = 0) : False :=
  sorry

set_option warn.sorry false in
/-- **The `(3,4)` Bézout certificate** (sorry node, sympy-extracted
cofactors pending): `F ⬝ Ψ₃ + G ⬝ preΨ₄ = Δ⁴`, so `Ψ₃` and `preΨ₄`
cannot vanish together when `Δ ≠ 0`. -/
theorem psi34_not_both_zero (hΔ : W.Δ ≠ 0) (x₀ : K)
    (h3 : (W.Ψ₃).eval x₀ = 0) (h4 : (W.preΨ₄).eval x₀ = 0) : False :=
  sorry

variable {W}

set_option backward.isDefEq.respectTransparency false in
/-- The `ψ`-values at a point are the normalised EDS of the seed
values. -/
lemma evalEval_ψ_normEDS (x y : K) (n : ℤ) :
    (W.ψ n).evalEval x y =
      normEDS ((W.ψ₂).evalEval x y) ((W.Ψ₃).eval x)
        ((W.preΨ₄).eval x) n := by
  have h := map_normEDS (Polynomial.evalEvalRingHom x y) W.ψ₂
    (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) n
  calc (W.ψ n).evalEval x y
      = (Polynomial.evalEvalRingHom x y)
          (normEDS W.ψ₂ (Polynomial.C W.Ψ₃)
            (Polynomial.C W.preΨ₄) n) := rfl
    _ = normEDS ((Polynomial.evalEvalRingHom x y) W.ψ₂)
          ((Polynomial.evalEvalRingHom x y) (Polynomial.C W.Ψ₃))
          ((Polynomial.evalEvalRingHom x y) (Polynomial.C W.preΨ₄))
          n := h
    _ = _ := by
        simp only [Polynomial.coe_evalEvalRingHom,
          Polynomial.evalEval_C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **No common root over an algebraically closed field**: the heart
of the coprimality. -/
theorem no_common_root [IsAlgClosed K] (hΔ : W.Δ ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) (x₀ : K) (hΦ : (W.Φ (n : ℤ)).eval x₀ = 0)
    (hΨ : (W.ΨSq (n : ℤ)).eval x₀ = 0) : False := by
  classical
  -- the point above `x₀`
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
    (p := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x₀ + W.a₃) *
      Polynomial.X - Polynomial.C
        (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
    (by
      have hd2 : (Polynomial.X ^ 2 +
          Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X -
          Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) :
          Polynomial K).natDegree = 2 := by
        compute_degree!
      intro hdeg
      have hne : (Polynomial.X ^ 2 +
          Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X -
          Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) :
          Polynomial K) ≠ 0 := by
        intro h0
        rw [h0, Polynomial.natDegree_zero] at hd2
        exact two_ne_zero hd2.symm
      rw [Polynomial.degree_eq_natDegree hne, hd2] at hdeg
      norm_num at hdeg)
  have heq : W.toAffine.Equation x₀ y₀ := by
    rw [Affine.equation_iff]
    have := hy₀
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X] at this
    linear_combination this
  have hns : W.toAffine.Nonsingular x₀ y₀ :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq
  -- the seed values and the value sequence
  set b := (W.ψ₂).evalEval x₀ y₀ with hbdef
  set c := (W.Ψ₃).eval x₀ with hcdef
  set d := (W.preΨ₄).eval x₀ with hddef
  have hw : ∀ m : ℤ, (W.ψ m).evalEval x₀ y₀ = normEDS b c d m :=
    fun m => evalEval_ψ_normEDS x₀ y₀ m
  -- the on-curve square identity `b² = Ψ₂Sq(x₀)`
  have hb2 : b ^ 2 = (W.Ψ₂Sq).eval x₀ := by
    have h := congrArg (Polynomial.evalEvalRingHom x₀ y₀) W.ψ₂_sq
    simp only [map_add, map_mul, map_pow, map_ofNat,
      Polynomial.coe_evalEvalRingHom, Polynomial.evalEval_C] at h
    rw [show W.toAffine.polynomial.evalEval x₀ y₀ = 0 from heq] at h
    rw [hbdef]
    rw [h]
    ring
  -- `wₙ = 0`
  have hwn : normEDS b c d (n : ℤ) = 0 := by
    have hsq : ((W.ψ (n : ℤ)).evalEval x₀ y₀) ^ 2 =
        ((W.ΨSq (n : ℤ))).eval x₀ := by
      rw [← WeierstrassCurve.evalEval_Ψ_sq _ heq,
        WeierstrassCurve.evalEval_ψ _ heq]
    rw [← hw]
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [hsq, hΨ])
  -- `wₙ₊₁ ⬝ wₙ₋₁ = 0` from the `Φ`-definition
  have hprod : normEDS b c d ((n : ℤ) + 1) *
      normEDS b c d ((n : ℤ) - 1) = 0 := by
    have hΦeq : W.Φ (n : ℤ) = Polynomial.X * W.ΨSq (n : ℤ) -
        W.preΨ ((n : ℤ) + 1) * W.preΨ ((n : ℤ) - 1) *
          (if Even (n : ℤ) then 1 else W.Ψ₂Sq) := rfl
    have hbridge : ∀ m : ℤ, (W.ψ m).evalEval x₀ y₀ =
        (W.preΨ m).eval x₀ * (if Even m then b else 1) := by
      intro m
      rw [WeierstrassCurve.evalEval_ψ _ heq]
      rw [show W.Ψ m = Polynomial.C (W.preΨ m) *
        (if Even m then W.ψ₂ else 1) from by
          rw [WeierstrassCurve.Ψ]]
      rcases Int.even_or_odd m with hm | hm
      · rw [if_pos hm, if_pos hm]
        simp [Polynomial.evalEval_C, hbdef]
      · rw [if_neg (Int.not_even_iff_odd.mpr hm),
          if_neg (Int.not_even_iff_odd.mpr hm)]
        simp [Polynomial.evalEval_C]
    have h1 := hbridge ((n : ℤ) + 1)
    have h2 := hbridge ((n : ℤ) - 1)
    rw [hw] at h1 h2
    rcases Nat.even_or_odd n with hpar | hpar
    · -- even `n`: neighbours odd, parity factor `1`
      have hev : Even ((n : ℤ)) := by exact_mod_cast hpar
      have hne1 : ¬ Even ((n : ℤ) + 1) := by
        rw [Int.even_add_one, not_not]
        exact hev
      have hne2 : ¬ Even ((n : ℤ) - 1) := by
        intro hcon
        exact hne1 (by
          rcases hcon with ⟨t, ht⟩
          exact ⟨t + 1, by omega⟩)
      rw [if_pos hev, mul_one] at hΦeq
      have hΦv := congrArg (Polynomial.eval x₀) hΦeq
      rw [hΦ] at hΦv
      simp only [Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X] at hΦv
      rw [hΨ, mul_zero, zero_sub, eq_comm, neg_eq_zero] at hΦv
      rw [if_neg hne1, mul_one] at h1
      rw [if_neg hne2, mul_one] at h2
      rw [h1, h2]
      exact hΦv
    · -- odd `n`: neighbours even, parity factor `Ψ₂Sq(x₀) = b²`
      have hodd' : ¬ Even ((n : ℤ)) := by
        exact_mod_cast Nat.not_even_iff_odd.mpr hpar
      have he1 : Even ((n : ℤ) + 1) := by
        rw [Int.even_add_one]
        exact hodd'
      have he2 : Even ((n : ℤ) - 1) := by
        rcases he1 with ⟨t, ht⟩
        exact ⟨t - 1, by omega⟩
      rw [if_neg hodd'] at hΦeq
      have hΦv := congrArg (Polynomial.eval x₀) hΦeq
      rw [hΦ] at hΦv
      simp only [Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X] at hΦv
      rw [hΨ, mul_zero, zero_sub, eq_comm, neg_eq_zero] at hΦv
      rw [if_pos he1] at h1
      rw [if_pos he2] at h2
      rw [h1, h2]
      calc (W.preΨ ((n : ℤ) + 1)).eval x₀ * b *
            ((W.preΨ ((n : ℤ) - 1)).eval x₀ * b) =
          (W.preΨ ((n : ℤ) + 1)).eval x₀ *
            (W.preΨ ((n : ℤ) - 1)).eval x₀ * b ^ 2 := by ring
        _ = 0 := by rw [hb2, hΦv]
  -- the rank of apparition
  have hex : ∃ r : ℕ, 2 ≤ r ∧ normEDS b c d r = 0 := ⟨n, hn, hwn⟩
  classical
  set r := Nat.find hex with hrdef
  obtain ⟨hr2, hr0⟩ := Nat.find_spec hex
  have hrank : EDSRank.IsRank b c d r := by
    refine ⟨hr2, hr0, ?_⟩
    intro k hk1 hkr
    rcases eq_or_lt_of_le hk1 with h1 | h2
    · rw [← h1]
      simp [normEDS_one]
    · intro h0
      exact Nat.find_min hex hkr ⟨h2, h0⟩
  by_cases hadj : normEDS b c d ((r : ℤ) + 1) = 0
  · -- adjacent zeros: degenerate seeds, excluded by the certificates
    rcases hrank.degenerate_of_adjacent hadj with ⟨hb, hc⟩ | ⟨hc, hd, -⟩
    · exact psi23_not_both_zero W hΔ x₀
        (by rw [← hb2, hb, zero_pow two_ne_zero]) (hcdef ▸ hc)
    · exact psi34_not_both_zero W hΔ x₀ (hcdef ▸ hc) (hddef ▸ hd)
  · -- the rank divides two consecutive integers
    have hdvdn := hrank.dvd_of_eq_zero hadj n (by omega) hwn
    rcases mul_eq_zero.mp hprod with h1 | h1
    · have hdvd1 := hrank.dvd_of_eq_zero hadj (n + 1) (by omega)
        (by rwa [show (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 by omega])
      have hone : (r : ℤ) ∣ 1 := by
        have ha : (r : ℤ) ∣ ((n : ℤ) + 1) := by
          exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd1
        have hb' : (r : ℤ) ∣ (n : ℤ) :=
          Int.natCast_dvd_natCast.mpr hdvdn
        have := dvd_sub ha hb'
        rwa [show ((n : ℤ) + 1) - (n : ℤ) = 1 by ring] at this
      have hone' : r ∣ 1 := by exact_mod_cast hone
      have := Nat.le_of_dvd one_pos hone'
      omega
    · have hdvd1 := hrank.dvd_of_eq_zero hadj (n - 1) (by omega)
        (by rwa [show (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 by omega])
      have hone : (r : ℤ) ∣ 1 := by
        have ha : (r : ℤ) ∣ ((n : ℤ) - 1) := by
          have := Int.natCast_dvd_natCast.mpr hdvd1
          rwa [show (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 by omega] at this
        have hb' : (r : ℤ) ∣ (n : ℤ) :=
          Int.natCast_dvd_natCast.mpr hdvdn
        have := dvd_sub hb' ha
        rwa [show ((n : ℤ)) - ((n : ℤ) - 1) = 1 by ring] at this
      have hone' : r ∣ 1 := by exact_mod_cast hone
      have := Nat.le_of_dvd one_pos hone'
      omega

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Coprimality of `Φₙ` and `ΨSqₙ` over any field with `Δ ≠ 0`**:
the direct replacement for the resultant-formula route. -/
theorem isCoprime_Φ_ΨSq_field {k : Type*} [Field k]
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    IsCoprime (W.Φ n) (W.ΨSq n) := by
  classical
  -- reduce to `n = |n|` by the parity of the division polynomials
  have hΦabs : W.Φ n = W.Φ ((n.natAbs : ℕ) : ℤ) := by
    rcases Int.natAbs_eq n with h | h
    · conv_lhs => rw [h]
    · conv_lhs => rw [h, WeierstrassCurve.Φ_neg]
  have hΨabs : W.ΨSq n = W.ΨSq ((n.natAbs : ℕ) : ℤ) := by
    rcases Int.natAbs_eq n with h | h
    · conv_lhs => rw [h]
    · conv_lhs => rw [h, WeierstrassCurve.ΨSq_neg]
  rw [hΦabs, hΨabs]
  set m : ℕ := n.natAbs with hmdef
  have hm1 : 1 ≤ m := by
    have := Int.natAbs_pos.mpr hn
    omega
  set nn : ℤ := ((m : ℕ) : ℤ) with hnndef
  have hpos : 0 < nn := by omega
  rcases eq_or_lt_of_le (by omega : (1 : ℤ) ≤ nn) with h1 | h2
  · -- `n = 1`: `ΨSq 1 = 1`
    rw [← h1, show W.ΨSq 1 = 1 from by
      rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
        WeierstrassCurve.ΨSq_ofNat]
      simp]
    exact isCoprime_one_right
  -- `n ≥ 2`: no common root over the algebraic closure
  by_contra hcop
  set g := EuclideanDomain.gcd (W.Φ nn) (W.ΨSq nn) with hgdef
  have hΦne : W.Φ nn ≠ 0 := by
    intro h0
    have hc := congrArg (fun q => Polynomial.coeff q (nn.natAbs ^ 2)) h0
    simp only [Polynomial.coeff_zero] at hc
    rw [WeierstrassCurve.coeff_Φ] at hc
    exact one_ne_zero hc
  have hgne : g ≠ 0 := fun h0 =>
    hΦne ((EuclideanDomain.gcd_eq_zero_iff.mp h0).1)
  have hgunit : ¬IsUnit g := fun h =>
    hcop (EuclideanDomain.gcd_isUnit_iff.mp h)
  -- a root of `g` in the algebraic closure
  set Kb := AlgebraicClosure k
  set φ : k →+* Kb := algebraMap k Kb
  have hgmapne : g.map φ ≠ 0 := Polynomial.map_ne_zero hgne
  have hdeg : (g.map φ).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro h0
    exact hgunit (Polynomial.isUnit_iff_degree_eq_zero.mpr h0)
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root (p := g.map φ) hdeg
  -- transfer the common vanishing
  have hΦ0 : ((W.map φ).Φ nn).eval x₀ = 0 := by
    rw [WeierstrassCurve.map_Φ]
    obtain ⟨q, hq⟩ := EuclideanDomain.gcd_dvd_left (W.Φ nn) (W.ΨSq nn)
    rw [hq, Polynomial.map_mul, Polynomial.eval_mul,
      show (g.map φ).eval x₀ = 0 from hx₀, zero_mul]
  have hΨ0 : ((W.map φ).ΨSq nn).eval x₀ = 0 := by
    rw [WeierstrassCurve.map_ΨSq]
    obtain ⟨q, hq⟩ := EuclideanDomain.gcd_dvd_right (W.Φ nn) (W.ΨSq nn)
    rw [hq, Polynomial.map_mul, Polynomial.eval_mul,
      show (g.map φ).eval x₀ = 0 from hx₀, zero_mul]
  have hΔK : (W.map φ).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    intro h0
    exact hΔ ((map_eq_zero φ).mp h0)
  -- specialize the closed-field result at `n.toNat`
  have hn2 : 2 ≤ nn.toNat := by omega
  refine no_common_root hΔK hn2 x₀ ?_ ?_
  · rwa [show ((nn.toNat : ℕ) : ℤ) = nn by omega]
  · rwa [show ((nn.toNat : ℕ) : ℤ) = nn by omega]

end PhiPsiCoprime

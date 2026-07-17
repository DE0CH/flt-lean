/-
WronskianInduction.lean — own work for the Fermat project.

The invariant-differential induction at the tautological point: for
every `n ≥ 1`, the coordinates `(xₙ, yₙ)` of `n • (tautX, tautY)`
satisfy `DK xₙ = n ⬝ ψ₂(nP)` and `DK yₙ = −n ⬝ F_X(nP)` — i.e.
`[n]*ω = n ⬝ ω` for the invariant differential. Base case `n = 1` is
`DK_tautX`/`DK_tautY` (true by construction of the Hamiltonian
derivation), `n = 2` is the differentiated duplication law, and the
step is the differentiated addition law along the chord.
-/
module

public import Fermat.FLT.EllipticCurve.WronskianStep
public import Fermat.FLT.EllipticCurve.TautMultiplication
import Fermat.FLT.EllipticCurve.TorsionCard
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Points

@[expose] public section

namespace PsiSumCompanion

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

set_option backward.isDefEq.respectTransparency false in
lemma bc_a₁ : (WK⁄Kuniv).a₁ = coeffHom (MvPolynomial.X 0) := rfl
set_option backward.isDefEq.respectTransparency false in
lemma bc_a₂ : (WK⁄Kuniv).a₂ = coeffHom (MvPolynomial.X 1) := rfl
set_option backward.isDefEq.respectTransparency false in
lemma bc_a₃ : (WK⁄Kuniv).a₃ = coeffHom (MvPolynomial.X 2) := rfl
set_option backward.isDefEq.respectTransparency false in
lemma bc_a₄ : (WK⁄Kuniv).a₄ = coeffHom (MvPolynomial.X 3) := rfl
set_option backward.isDefEq.respectTransparency false in
lemma bc_a₆ : (WK⁄Kuniv).a₆ = coeffHom (MvPolynomial.X 4) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma DK_bc_a₁ : DK (WK⁄Kuniv).a₁ = 0 := by
  rw [bc_a₁]; exact DK_coeffHom _
set_option backward.isDefEq.respectTransparency false in
lemma DK_bc_a₂ : DK (WK⁄Kuniv).a₂ = 0 := by
  rw [bc_a₂]; exact DK_coeffHom _
set_option backward.isDefEq.respectTransparency false in
lemma DK_bc_a₃ : DK (WK⁄Kuniv).a₃ = 0 := by
  rw [bc_a₃]; exact DK_coeffHom _
set_option backward.isDefEq.respectTransparency false in
lemma DK_bc_a₄ : DK (WK⁄Kuniv).a₄ = 0 := by
  rw [bc_a₄]; exact DK_coeffHom _

set_option backward.isDefEq.respectTransparency false in
/-- The curve equation at a nonsingular point, in explicit form. -/
lemma equation_explicit {x y : Kuniv}
    (h : (WK⁄Kuniv).toAffine.Nonsingular x y) :
    y ^ 2 + (WK⁄Kuniv).a₁ * x * y + (WK⁄Kuniv).a₃ * y =
      x ^ 3 + (WK⁄Kuniv).a₂ * x ^ 2 + (WK⁄Kuniv).a₄ * x +
        (WK⁄Kuniv).a₆ :=
  (Affine.equation_iff x y).mp h.1

set_option backward.isDefEq.respectTransparency false in
/-- `ψ₂ ≠ 0` at the tautological point: the base point is not
`2`-torsion. -/
lemma taut_s_ne_zero :
    2 * tautY + (WK⁄Kuniv).a₁ * tautX + (WK⁄Kuniv).a₃ ≠ 0 := by
  have h := taut_psi_ne_zero' two_ne_zero
  rwa [show ((2 : ℤ) : ℤ) = 2 from rfl, WeierstrassCurve.ψ_two,
    WeierstrassCurve.ψ₂, Affine.evalEval_polynomialY] at h

set_option backward.isDefEq.respectTransparency false in
/-- The base case of the invariant-differential values, phrased with
the curve coefficients. -/
lemma DK_taut_base :
    DK tautX = 2 * tautY + (WK⁄Kuniv).a₁ * tautX + (WK⁄Kuniv).a₃ ∧
    DK tautY = -((WK⁄Kuniv).a₁ * tautY -
      (3 * tautX ^ 2 + 2 * (WK⁄Kuniv).a₂ * tautX + (WK⁄Kuniv).a₄)) := by
  constructor
  · rw [bc_a₁, bc_a₃]
    exact DK_tautX
  · rw [bc_a₁, bc_a₂, bc_a₄]
    exact DK_tautY

set_option backward.isDefEq.respectTransparency false in
lemma taut_negY_ne :
    tautY ≠ (WK⁄Kuniv).toAffine.negY tautX tautY := by
  intro hc
  apply taut_s_ne_zero
  rw [Affine.negY] at hc
  linear_combination hc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The invariant-differential induction at the tautological
point**: `[n]*ω = n ⬝ ω`, expressed through the values of the
invariant derivation at the coordinates of `n • taut`. -/
theorem DK_smul_taut : ∀ (n : ℕ), 1 ≤ n → ∀ (xn yn : Kuniv)
    (hns : (WK⁄Kuniv).toAffine.Nonsingular xn yn),
    ((n : ℤ) • (Affine.Point.some tautX tautY tautNS' :
      (WK⁄Kuniv).Point) = Affine.Point.some xn yn hns) →
    DK xn = (n : Kuniv) *
      (2 * yn + (WK⁄Kuniv).a₁ * xn + (WK⁄Kuniv).a₃) ∧
    DK yn = -((n : Kuniv) * ((WK⁄Kuniv).a₁ * yn -
      (3 * xn ^ 2 + 2 * (WK⁄Kuniv).a₂ * xn + (WK⁄Kuniv).a₄))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro hn xn yn hns hsm
  rcases eq_or_lt_of_le hn with h1 | h2
  · -- base case n = 1
    subst h1
    rw [Nat.cast_one, one_smul] at hsm
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj hsm
    subst hx; subst hy
    rw [Nat.cast_one, one_mul, one_mul]
    exact DK_taut_base
  rcases eq_or_lt_of_le (by omega : 2 ≤ n) with h2' | h3
  · -- base case n = 2 : the tangent (doubling) case
    subst h2'
    have hsm2 : (2 : ℤ) • (Affine.Point.some tautX tautY tautNS' :
        (WK⁄Kuniv).Point) =
        Affine.Point.some tautX tautY tautNS' +
          Affine.Point.some tautX tautY tautNS' := by
      rw [show (2 : ℤ) = 1 + 1 from rfl, add_zsmul, one_zsmul]
    have hxy : ¬(tautX = tautX ∧ tautY =
        (WK⁄Kuniv).toAffine.negY tautX tautY) :=
      fun h => taut_negY_ne h.2
    rw [Affine.Point.add_some hxy] at hsm2
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hsm2] at hsm
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj hsm.symm
    set ℓ := (WK⁄Kuniv).toAffine.slope tautX tautX tautY tautY with hℓdef
    have hden : tautY - (WK⁄Kuniv).toAffine.negY tautX tautY =
        2 * tautY + (WK⁄Kuniv).a₁ * tautX + (WK⁄Kuniv).a₃ := by
      rw [Affine.negY]
      ring
    have hℓ : ℓ = (3 * tautX ^ 2 + 2 * (WK⁄Kuniv).a₂ * tautX +
        (WK⁄Kuniv).a₄ - (WK⁄Kuniv).a₁ * tautY) /
        (2 * tautY + (WK⁄Kuniv).a₁ * tautX + (WK⁄Kuniv).a₃) := by
      rw [hℓdef, Affine.slope_of_Y_ne rfl taut_negY_ne, hden]
    have hx3 : xn = ℓ ^ 2 + (WK⁄Kuniv).a₁ * ℓ - (WK⁄Kuniv).a₂ -
        2 * tautX := by
      rw [hx]
      simp only [Affine.addX]
      ring
    have hy3 : yn = -(ℓ * (xn - tautX) + tautY) -
        (WK⁄Kuniv).a₁ * xn - (WK⁄Kuniv).a₃ := by
      rw [hy, hx]
      simp only [Affine.addY, Affine.negY, Affine.negAddY]
    have hstep := DK_doubling_step (WK⁄Kuniv).a₁ (WK⁄Kuniv).a₂
      (WK⁄Kuniv).a₃ (WK⁄Kuniv).a₄ (WK⁄Kuniv).a₆ tautX tautY ℓ xn yn
      DK_bc_a₁ DK_bc_a₂ DK_bc_a₃ DK_bc_a₄
      (equation_explicit tautNS') taut_s_ne_zero hℓ
      DK_taut_base.1 DK_taut_base.2 hx3 hy3
    rw [show ((2 : ℕ) : Kuniv) = 2 from by norm_num]
    exact hstep
  · -- step n ≥ 3 : the chord case through (n−1) • taut
    have hn1 : (1 : ℕ) ≤ n - 1 := by omega
    have hn1z : ((n : ℤ) - 1) ≠ 0 := by omega
    obtain ⟨xk, yk, hk, hsmk, -⟩ := taut_smul_formula hn1z
    have hIH := IH (n - 1) (by omega) hn1 xk yk hk
      (by rwa [show (((n - 1 : ℕ) : ℤ)) = (n : ℤ) - 1 from by omega])
    -- the chord condition
    have hxk : xk ≠ tautX := by
      intro hc
      subst hc
      rcases Affine.Y_eq_of_X_eq hk.1 tautNS'.1 rfl with hy | hy
      · -- (n−1) • T = T, so (n−2) • T = 0
        subst hy
        have hzero : ((n : ℤ) - 2) •
            (Affine.Point.some tautX tautY tautNS' :
              (WK⁄Kuniv).Point) = 0 := by
          have : ((n : ℤ) - 2) = ((n : ℤ) - 1) - 1 := by ring
          rw [this, sub_zsmul, one_zsmul, hsmk]
          exact add_neg_cancel _
        exact taut_ΨSq_ne_zero (by omega : ((n : ℤ) - 2) ≠ 0)
          ((TorsionCard.smul_some_eq_zero_iff WK (by omega) tautNS').mp
            hzero)
      · -- (n−1) • T = −T, so n • T = 0
        subst hy
        have hzero : (n : ℤ) •
            (Affine.Point.some tautX tautY tautNS' :
              (WK⁄Kuniv).Point) = 0 := by
          have : (n : ℤ) = ((n : ℤ) - 1) + 1 := by ring
          rw [this, add_zsmul, one_zsmul, hsmk,
            ← Affine.Point.neg_some tautNS', neg_add_cancel]
        exact taut_ΨSq_ne_zero (by omega : (n : ℤ) ≠ 0)
          ((TorsionCard.smul_some_eq_zero_iff WK (by omega)
            tautNS').mp hzero)
    -- the sum decomposition
    have hxy : ¬(xk = tautX ∧ yk =
        (WK⁄Kuniv).toAffine.negY tautX tautY) := fun h => hxk h.1
    have hsum : (n : ℤ) • (Affine.Point.some tautX tautY tautNS' :
        (WK⁄Kuniv).Point) =
        Affine.Point.some xk yk hk +
          Affine.Point.some tautX tautY tautNS' := by
      have : (n : ℤ) = ((n : ℤ) - 1) + 1 := by ring
      rw [this, add_zsmul, one_zsmul, hsmk]
    rw [Affine.Point.add_some hxy] at hsum
    rw [hsum] at hsm
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj hsm.symm
    set ℓ := (WK⁄Kuniv).toAffine.slope xk tautX yk tautY with hℓdef
    have hℓ : ℓ = (yk - tautY) / (xk - tautX) := by
      rw [hℓdef, Affine.slope_of_X_ne hxk]
    have hx3 : xn = ℓ ^ 2 + (WK⁄Kuniv).a₁ * ℓ - (WK⁄Kuniv).a₂ -
        xk - tautX := by
      rw [hx]
      simp only [Affine.addX]
    have hy3 : yn = -(ℓ * (xn - xk) + yk) -
        (WK⁄Kuniv).a₁ * xn - (WK⁄Kuniv).a₃ := by
      rw [hy, hx]
      simp only [Affine.addY, Affine.negY, Affine.negAddY]
    have hstep := DK_addition_step (WK⁄Kuniv).a₁ (WK⁄Kuniv).a₂
      (WK⁄Kuniv).a₃ (WK⁄Kuniv).a₄ (WK⁄Kuniv).a₆ tautX tautY xk yk
      (((n - 1 : ℕ) : Kuniv)) ℓ xn yn
      DK_bc_a₁ DK_bc_a₂ DK_bc_a₃
      (equation_explicit tautNS') (equation_explicit hk) hxk hℓ
      DK_taut_base.1 DK_taut_base.2 hIH.1 hIH.2 hx3 hy3
    have hcast : ((n - 1 : ℕ) : Kuniv) + 1 = (n : Kuniv) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    rw [← hcast]
    exact hstep

end PsiSumCompanion

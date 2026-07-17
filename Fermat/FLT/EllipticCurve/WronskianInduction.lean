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

/-! ## The Wronskian identity

Differentiating the multiplication `x`-formula `xₙ ⬝ ΨSqₙ = Φₙ` with
the invariant derivation and cancelling `DK(x) = ψ₂ ≠ 0` yields
`Φₙ′ΨSqₙ − ΦₙΨSqₙ′ = n ⬝ preΨ₂ₙ`. -/

set_option backward.isDefEq.respectTransparency false in
/-- `DK(x)` is the image of the class of `F_Y`. -/
lemma DK_tautX_repr : DK tautX = algebraMap Buniv Kuniv
    (CoordinateRing.mk Wuniv Wuniv.toAffine.polynomialY) := by
  have hrepr : tautX = algebraMap Buniv Kuniv
      (CoordinateRing.mk Wuniv (Polynomial.C Polynomial.X)) := rfl
  rw [hrepr, DK_algebraMap, DB_mk]
  rw [show Dham (Polynomial.C Polynomial.X) =
      Wuniv.toAffine.polynomialY by
    rw [Dham_C]
    simp]

set_option backward.isDefEq.respectTransparency false in
/-- **The chain rule at the tautological point**: `DK` of a `y`-free
value is the derivative value times `DK(x)`. -/
lemma DK_eval_taut (P : (MvPolynomial (Fin 5) ℤ)[X]) :
    DK ((P.map coeffHom).eval tautX) =
      ((Polynomial.derivative P).map coeffHom).eval tautX * DK tautX := by
  rw [taut_eval_C_mk, DK_algebraMap, DB_mk, Dham_C, map_mul, map_mul,
    taut_eval_C_mk, DK_tautX_repr]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The Wronskian identity at the tautological point**:
`Φₙ′ ⬝ ΨSqₙ − Φₙ ⬝ ΨSqₙ′ = n ⬝ preΨ₂ₙ` as values at `tautX`. -/
theorem wronskian_taut {n : ℕ} (hn : 1 ≤ n) :
    ((Polynomial.derivative (Wuniv.Φ (n : ℤ))).map coeffHom).eval tautX *
        ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX -
      ((Wuniv.Φ (n : ℤ)).map coeffHom).eval tautX *
        ((Polynomial.derivative (Wuniv.ΨSq (n : ℤ))).map coeffHom).eval
          tautX =
      (n : Kuniv) *
        ((Wuniv.preΨ (2 * (n : ℤ))).map coeffHom).eval tautX := by
  have hnz : ((n : ℤ)) ≠ 0 := by omega
  have hs : (((WK⁄Kuniv).ψ 2).evalEval tautX tautY : Kuniv) ≠ 0 :=
    taut_psi_ne_zero' two_ne_zero
  have hpsin := taut_psi_ne_zero' hnz
  obtain ⟨x', y', h', hsm, hxf, htr⟩ :=
    (TorsionCard.zsmul_some_aux_strong WK tautNS' hs (n : ℤ)
      (by omega)).2 hpsin
  have hDK := (DK_smul_taut n hn x' y' h' hsm).1
  -- the bridges to univariate values
  have hbridgeSq : (((WK⁄Kuniv).ψ (n : ℤ)).evalEval tautX tautY) ^ 2 =
      ((WK⁄Kuniv).ΨSq (n : ℤ)).eval tautX := by
    rw [← WeierstrassCurve.evalEval_Ψ_sq _ tautNS'.1,
      WeierstrassCurve.evalEval_ψ _ tautNS'.1]
  have hxf' : x' * ((WK⁄Kuniv).ΨSq (n : ℤ)).eval tautX =
      ((WK⁄Kuniv).Φ (n : ℤ)).eval tautX := by
    rw [← hbridgeSq, ← WeierstrassCurve.evalEval_φ _ tautNS'.1]
    exact hxf
  -- the tracking in univariate form
  have h2n : Even (2 * (n : ℤ)) := even_two_mul _
  have htr' : (2 * y' + (WK⁄Kuniv).a₁ * x' + (WK⁄Kuniv).a₃) *
      ((WK⁄Kuniv).ΨSq (n : ℤ)).eval tautX ^ 2 =
      ((WK⁄Kuniv).preΨ (2 * (n : ℤ))).eval tautX * DK tautX := by
    have he := TorsionCard.evalEval_ψ_of_even WK h2n tautNS'.1
    have hψ2 : (((WK⁄Kuniv).ψ 2).evalEval tautX tautY : Kuniv) =
        DK tautX := by
      rw [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂,
        Affine.evalEval_polynomialY, DK_taut_base.1]
    rw [← hψ2, ← he, ← hbridgeSq]
    linear_combination htr
  -- differentiate the x-formula
  have hxfm : x' * ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX =
      ((Wuniv.Φ (n : ℤ)).map coeffHom).eval tautX := by
    have h0 : ((WK⁄Kuniv).ΨSq (n : ℤ)).eval tautX =
        ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX ∧
        ((WK⁄Kuniv).Φ (n : ℤ)).eval tautX =
          ((Wuniv.Φ (n : ℤ)).map coeffHom).eval tautX := by
      constructor
      · have h1 : ((WK.ΨSq (n : ℤ)).eval tautX : Kuniv) =
            ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX := by
          have h2 : WK.ΨSq (n : ℤ) =
              (Wuniv.ΨSq (n : ℤ)).map coeffHom := by
            rw [show WK = Wuniv.map coeffHom from rfl,
              WeierstrassCurve.map_ΨSq]
          rw [h2]
        exact (WK_baseChange_self ▸ h1 : _)
      · have h1 : ((WK.Φ (n : ℤ)).eval tautX : Kuniv) =
            ((Wuniv.Φ (n : ℤ)).map coeffHom).eval tautX := by
          have h2 : WK.Φ (n : ℤ) =
              (Wuniv.Φ (n : ℤ)).map coeffHom := by
            rw [show WK = Wuniv.map coeffHom from rfl,
              WeierstrassCurve.map_Φ]
          rw [h2]
        exact (WK_baseChange_self ▸ h1 : _)
    rw [← h0.1, ← h0.2]
    exact hxf'
  have hpre : ((WK⁄Kuniv).preΨ (2 * (n : ℤ))).eval tautX =
      ((Wuniv.preΨ (2 * (n : ℤ))).map coeffHom).eval tautX := by
    have h1 : ((WK.preΨ (2 * (n : ℤ))).eval tautX : Kuniv) =
        ((Wuniv.preΨ (2 * (n : ℤ))).map coeffHom).eval tautX := by
      have h2 : WK.preΨ (2 * (n : ℤ)) =
          (Wuniv.preΨ (2 * (n : ℤ))).map coeffHom := by
        rw [show WK = Wuniv.map coeffHom from rfl,
          WeierstrassCurve.map_preΨ]
      rw [h2]
    exact (WK_baseChange_self ▸ h1 : _)
  have hSm : ((WK⁄Kuniv).ΨSq (n : ℤ)).eval tautX =
      ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX := by
    have h1 : ((WK.ΨSq (n : ℤ)).eval tautX : Kuniv) =
        ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX := by
      have h2 : WK.ΨSq (n : ℤ) = (Wuniv.ΨSq (n : ℤ)).map coeffHom := by
        rw [show WK = Wuniv.map coeffHom from rfl,
          WeierstrassCurve.map_ΨSq]
      rw [h2]
    exact (WK_baseChange_self ▸ h1 : _)
  -- differentiate
  have hdiff := congrArg DK hxfm
  have hmul := DK_mul x' (((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX)
  rw [DK_eval_taut] at hdiff hmul
  -- assemble; cancel DK tautX
  have hD : DK tautX ≠ 0 := by
    rw [DK_taut_base.1]
    exact taut_s_ne_zero
  have htr'' : (2 * y' + (WK⁄Kuniv).a₁ * x' + (WK⁄Kuniv).a₃) *
      (((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX) ^ 2 =
      ((Wuniv.preΨ (2 * (n : ℤ))).map coeffHom).eval tautX *
        DK tautX := by
    rw [← hSm, ← hpre]
    exact htr'
  have key : (((Polynomial.derivative (Wuniv.Φ (n : ℤ))).map
        coeffHom).eval tautX *
        ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX -
      ((Wuniv.Φ (n : ℤ)).map coeffHom).eval tautX *
        ((Polynomial.derivative (Wuniv.ΨSq (n : ℤ))).map
          coeffHom).eval tautX -
      (n : Kuniv) *
        ((Wuniv.preΨ (2 * (n : ℤ))).map coeffHom).eval tautX) *
      DK tautX = 0 := by
    linear_combination
      (-(((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX)) * hdiff +
      ((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX * hmul +
      (((Polynomial.derivative (Wuniv.ΨSq (n : ℤ))).map
        coeffHom).eval tautX * DK tautX) * hxfm +
      (n : Kuniv) * htr'' +
      (((Wuniv.ΨSq (n : ℤ)).map coeffHom).eval tautX) ^ 2 * hDK
  rcases mul_eq_zero.mp key with h0 | h0
  · linear_combination h0
  · exact absurd h0 hD

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The universal Wronskian identity**: in `ℤ[A₁,…,A₅][X]`,
`Φₙ′ ⬝ ΨSqₙ − Φₙ ⬝ ΨSqₙ′ = n ⬝ preΨ₂ₙ`. -/
theorem univ_wronskian {n : ℕ} (hn : 1 ≤ n) :
    Polynomial.derivative (Wuniv.Φ (n : ℤ)) * Wuniv.ΨSq (n : ℤ) -
      Wuniv.Φ (n : ℤ) * Polynomial.derivative (Wuniv.ΨSq (n : ℤ)) =
      (n : (MvPolynomial (Fin 5) ℤ)[X]) * Wuniv.preΨ (2 * (n : ℤ)) := by
  apply taut_C_injective
  have h := wronskian_taut hn
  simp only [taut_eval_C_mk] at h
  simp only [map_mul, map_sub, map_natCast]
  linear_combination h

set_option backward.isDefEq.respectTransparency false in
/-- **The Wronskian identity over any commutative ring**:
`Φₙ′ ⬝ ΨSqₙ − Φₙ ⬝ ΨSqₙ′ = n ⬝ preΨ₂ₙ`. -/
theorem wronskian {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) :
    Polynomial.derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
      W.Φ (n : ℤ) * Polynomial.derivative (W.ΨSq (n : ℤ)) =
      (n : R[X]) * W.preΨ (2 * (n : ℤ)) := by
  set σ : MvPolynomial (Fin 5) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hmap : Wuniv.map σ = W := by
    simp only [Wuniv, WeierstrassCurve.map, MvPolynomial.eval₂Hom_X', σ]
    rfl
  have h := congrArg (Polynomial.map σ) (univ_wronskian hn)
  simp only [Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_natCast, ← Polynomial.derivative_map,
    ← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_ΨSq,
    ← WeierstrassCurve.map_preΨ, hmap] at h
  exact h

end PsiSumCompanion

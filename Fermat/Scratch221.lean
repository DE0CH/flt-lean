module

public import Fermat.FLT.EllipticCurve.DifferentialCharacter

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

namespace Scratch221

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- Explicit evaluation of `Φ 2`. -/
theorem eval_Φ_two (x : F) :
    (W.Φ ((2 : ℕ) : ℤ)).eval x = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  have h : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
  rw [h, WeierstrassCurve.Φ_two]
  simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_X]

theorem eval_ΨSq_two (x : F) :
    (W.ΨSq ((2 : ℕ) : ℤ)).eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  have h : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
  rw [h, WeierstrassCurve.ΨSq_two, WeierstrassCurve.Ψ₂Sq]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]

theorem eval_derivative_Φ_two (x : F) :
    (derivative (W.Φ ((2 : ℕ) : ℤ))).eval x = 4 * x ^ 3 - 2 * W.b₄ * x - 2 * W.b₆ := by
  have h : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
  rw [h, WeierstrassCurve.Φ_two]
  simp only [derivative_sub, derivative_mul, derivative_C, derivative_X_pow,
    derivative_X, zero_mul, zero_add, mul_one, eval_sub, eval_mul, eval_pow,
    eval_C, eval_X, eval_zero, Nat.cast_ofNat]
  push_cast
  ring

theorem eval_derivative_ΨSq_two (x : F) :
    (derivative (W.ΨSq ((2 : ℕ) : ℤ))).eval x = 12 * x ^ 2 + 2 * W.b₂ * x + 2 * W.b₄ := by
  have h : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
  rw [h, WeierstrassCurve.ΨSq_two, WeierstrassCurve.Ψ₂Sq]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow,
    derivative_X, zero_mul, zero_add, mul_one, eval_add, eval_mul, eval_pow,
    eval_C, eval_X, eval_zero, Nat.cast_ofNat]
  push_cast
  ring

/-- **The duplication differential identity, as a statement about a field.**

`ψ₂([2]P) · ΨSq₂(x)² = 2⁻¹·(Wronskian)·ψ₂(P)` with all denominators cleared:
with `L` the tangent slope, `Bx = ΨSq₂(x)`, `Ax = Φ₂(x)` and `dA, dB` their
derivatives evaluated at `x`, the identity is

  `2·Bx²·ψ₂(2P) = (dA·Bx − Ax·dB)·ψ₂(P)`,

which is exactly the reduced differential certificate for `λ([2]) = 2`. -/
theorem diffChar_two_core (a₁ a₂ a₃ a₄ a₆ x y L Bx Ax dA dB : F)
    (hEq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hLd : L * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hBx : Bx = 4 * x ^ 3 + (a₁ ^ 2 + 4 * a₂) * x ^ 2
      + 2 * (2 * a₄ + a₁ * a₃) * x + (a₃ ^ 2 + 4 * a₆))
    (hAx : Ax = x ^ 4 - (2 * a₄ + a₁ * a₃) * x ^ 2 - 2 * (a₃ ^ 2 + 4 * a₆) * x
      - (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2))
    (hdA : dA = 4 * x ^ 3 - 2 * (2 * a₄ + a₁ * a₃) * x - 2 * (a₃ ^ 2 + 4 * a₆))
    (hdB : dB = 12 * x ^ 2 + 2 * (a₁ ^ 2 + 4 * a₂) * x + 2 * (2 * a₄ + a₁ * a₃)) :
    2 * Bx ^ 2
        * (2 * (-(L * ((L ^ 2 + a₁ * L - a₂ - x - x) - x) + y)
              - a₁ * (L ^ 2 + a₁ * L - a₂ - x - x) - a₃)
            + a₁ * (L ^ 2 + a₁ * L - a₂ - x - x) + a₃)
      = (dA * Bx - Ax * dB) * (2 * y + a₁ * x + a₃) := by
  -- `ψ₂² = Bx`, from the curve equation with cofactor `4`.
  have hψsq : (2 * y + a₁ * x + a₃) ^ 2 = Bx := by
    rw [hBx]; linear_combination 4 * hEq
  -- `x([2]P)·Bx = Ax`: the duplication `x`-formula.
  have hAX : (L ^ 2 + a₁ * L - a₂ - x - x) * Bx = Ax := by
    rw [hAx, hBx]
    linear_combination
      (L * (2 * y + a₁ * x + a₃) + (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
          + a₁ * (2 * y + a₁ * x + a₃)) * hLd
        + (-a₁ ^ 2 - 4 * (a₂ + 2 * x) - 4 * (L ^ 2 + a₁ * L - a₂ - x - x)) * hEq
  -- Eliminate the slope.
  have hkey : 2 * Bx ^ 2
        * (2 * (-(L * ((L ^ 2 + a₁ * L - a₂ - x - x) - x) + y)
              - a₁ * (L ^ 2 + a₁ * L - a₂ - x - x) - a₃)
            + a₁ * (L ^ 2 + a₁ * L - a₂ - x - x) + a₃)
      = -2 * (2 * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) * (2 * y + a₁ * x + a₃)
            + a₁ * Bx) * (Ax - x * Bx)
        - 2 * Bx ^ 2 * (2 * y + a₁ * x + a₃) := by
    linear_combination (-2 * Bx * (2 * L + a₁)) * hAX
      + (4 * L * (Ax - x * Bx)) * hψsq
      + (-4 * (Ax - x * Bx) * (2 * y + a₁ * x + a₃)) * hLd
  rw [hkey, hBx, hAx, hdA, hdB]
  linear_combination
    (8 * a₁ * ((x ^ 4 - (2 * a₄ + a₁ * a₃) * x ^ 2 - 2 * (a₃ ^ 2 + 4 * a₆) * x
        - (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2))
      - x * (4 * x ^ 3 + (a₁ ^ 2 + 4 * a₂) * x ^ 2
        + 2 * (2 * a₄ + a₁ * a₃) * x + (a₃ ^ 2 + 4 * a₆)))) * hEq

/-- `[2] ≠ 0`: the `2`-torsion is finite and `x` is surjective onto the (infinite)
algebraically closed base field. -/
theorem mulByHom_two_ne_zero [IsAlgClosed F] [W.IsElliptic] :
    mulByHom W 2 ≠ (0 : W.Point →+ W.Point) := by
  classical
  have hfin : (veluPointX '' {P : W.Point | (2 : ℕ) • P = 0}).Finite :=
    (finite_nsmulKer (W := W) two_ne_zero).image _
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  obtain ⟨P, hP0, hPx⟩ := exists_point_veluPointX_eq (W := W) t
  intro hc
  exact ht ⟨P, by simpa [mulByHom_apply] using DFunLike.congr_fun hc P, hPx⟩

theorem isDiffChar_mulByHom_two' [IsAlgClosed F] [W.IsElliptic] :
    IsDiffChar (mulByHom W 2) (2 : F) := by
  classical
  obtain ⟨Cw, Dw, Ew, hEw, hyw⟩ := exists_y_witness_two (W := W)
  have hBne : W.ΨSq ((2 : ℕ) : ℤ) ≠ 0 := ΨSq_ne_zero' W (by norm_num)
  have hxw : ∀ P : W.Point, mulByHom W 2 P ≠ 0 →
      veluPointX (mulByHom W 2 P) * (W.ΨSq ((2 : ℕ) : ℤ)).eval (veluPointX P)
        = (W.Φ ((2 : ℕ) : ℤ)).eval (veluPointX P) := fun P hP =>
    veluPointX_nsmul (n := 2) (by norm_num) P hP
  have hguard : mulByHom W 2 = (0 : W.Point →+ W.Point) → (2 : F) = 0 :=
    fun hc => absurd hc (mulByHom_two_ne_zero (W := W))
  refine ⟨hguard,
    W.Φ ((2 : ℕ) : ℤ), W.ΨSq ((2 : ℕ) : ℤ), Cw, Dw, Ew, hBne, hEw,
    fun P hP => ⟨hxw P hP, hyw P hP⟩, ?_⟩
  refine isDiffCharCert_of_cofinite_ne_zero
    (S := veluPointX '' {P : W.Point | (2 : ℕ) • P = 0})
    ((finite_nsmulKer (W := W) two_ne_zero).image _) ?_
  intro Q hQ0 hQS
  have h2Q : mulByHom W 2 Q ≠ 0 := fun hc => hQS ⟨Q, by simpa [mulByHom_apply] using hc, rfl⟩
  refine isDiffCharCert_of_reduced (hxw Q h2Q) (hyw Q h2Q) ?_
  cases Q with
  | zero => exact absurd rfl hQ0
  | some xq yq hns =>
    have hEq : yq ^ 2 + W.a₁ * xq * yq + W.a₃ * yq
        = xq ^ 3 + W.a₂ * xq ^ 2 + W.a₄ * xq + W.a₆ := (Affine.equation_iff ..).1 hns.1
    have hy2 : yq ≠ -yq - W.a₁ * xq - W.a₃ := by
      intro hc
      refine h2Q ?_
      simp only [mulByHom_apply, two_nsmul]
      exact Affine.Point.add_self_of_Y_eq (by simpa [Affine.negY] using hc)
    have hd : (2 * yq + W.a₁ * xq + W.a₃) ≠ 0 := fun hc => hy2 (by linear_combination hc)
    have hy2' : yq ≠ W.negY xq yq := by simpa [Affine.negY] using hy2
    have hLd : W.slope xq xq yq yq * (2 * yq + W.a₁ * xq + W.a₃)
        = 3 * xq ^ 2 + 2 * W.a₂ * xq + W.a₄ - W.a₁ * yq := by
      rw [Affine.slope_of_Y_ne' hy2,
        show yq - (-yq - W.a₁ * xq - W.a₃) = 2 * yq + W.a₁ * xq + W.a₃ from by ring]
      exact div_mul_cancel₀ _ hd
    have hX2 : veluPointX (mulByHom W 2 (Affine.Point.some xq yq hns : W.Point))
        = W.addX xq xq (W.slope xq xq yq yq) := by
      simp only [mulByHom_apply, two_nsmul]
      rw [Affine.Point.add_self_of_Y_ne hy2', veluPointX_some]
    have hY2 : veluPointY (mulByHom W 2 (Affine.Point.some xq yq hns : W.Point))
        = W.addY xq xq yq (W.slope xq xq yq yq) := by
      simp only [mulByHom_apply, two_nsmul]
      rw [Affine.Point.add_self_of_Y_ne hy2', veluPointY_some]
    have hcore := diffChar_two_core W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ xq yq
      (W.slope xq xq yq yq)
      ((W.ΨSq ((2 : ℕ) : ℤ)).eval xq) ((W.Φ ((2 : ℕ) : ℤ)).eval xq)
      ((derivative (W.Φ ((2 : ℕ) : ℤ))).eval xq)
      ((derivative (W.ΨSq ((2 : ℕ) : ℤ))).eval xq)
      hEq hLd
      (by rw [eval_ΨSq_two, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆])
      (by rw [eval_Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈])
      (by rw [eval_derivative_Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆])
      (by rw [eval_derivative_ΨSq_two, WeierstrassCurve.b₂, WeierstrassCurve.b₄])
    rw [hX2, hY2]
    simp only [veluPointX_some, veluPointY_some, Affine.addY, Affine.negAddY,
      Affine.addX, Affine.negY]
    linear_combination (Ew.eval xq) * hcore

end Scratch221

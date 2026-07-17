/-
UniversalCurve.lean — own work for the Fermat project.

The universal Weierstrass curve (generic `a`-coefficients over
`MvPolynomial (Fin 5) ℤ`), and the nonvanishing of its division
polynomials in the coordinate ring — the witness used to cancel
`normEDS`-factors over the generic EDS coefficient ring `ℤ[b, c, d]`.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

namespace PsiSumCompanion

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

/-- The universal Weierstrass curve, with generic `a`-coefficients. -/
noncomputable def Wuniv : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
    MvPolynomial.X 3, MvPolynomial.X 4⟩

set_option backward.isDefEq.respectTransparency false in
/-- Nonzero integers stay nonzero in `ℤ[A₁, …, A₅]` (by evaluation). -/
theorem intCast_mvPoly_ne_zero {k : ℤ} (hk : k ≠ 0) :
    ((k : ℤ) : MvPolynomial (Fin 5) ℤ) ≠ 0 := by
  intro hc
  have h := congrArg (MvPolynomial.eval fun _ => (0 : ℤ)) hc
  rw [map_intCast, map_zero, Int.cast_id] at h
  exact hk h

set_option backward.isDefEq.respectTransparency false in
/-- **`mk (Ψ k) ≠ 0` over the universal curve** for `k ≠ 0`: `Ψ k` has
`{1, Y}`-basis coordinates built from `preΨ k ≠ 0` (degree theory)
with an extra unit `2` in the even case. -/
theorem mk_Ψ_univ_ne_zero {k : ℤ} (hk : k ≠ 0) :
    CoordinateRing.mk Wuniv (Wuniv.Ψ k) ≠ 0 := by
  have hpre : Wuniv.preΨ k ≠ 0 := fun hc =>
    Wuniv.coeff_preΨ_ne_zero (intCast_mvPoly_ne_zero hk)
      (by rw [hc, Polynomial.coeff_zero])
  rw [WeierstrassCurve.Ψ]
  by_cases he : Even k
  · rw [if_pos he]
    intro hzero
    have hrepr : Polynomial.C (Wuniv.preΨ k) * Wuniv.ψ₂ =
        Polynomial.C (Wuniv.preΨ k * (Polynomial.C Wuniv.a₁ *
            Polynomial.X + Polynomial.C Wuniv.a₃)) +
          Polynomial.C (2 * Wuniv.preΨ k) * Polynomial.X := by
      rw [WeierstrassCurve.ψ₂, Affine.polynomialY]
      C_simp
      ring1
    rw [hrepr] at hzero
    have hsmul : (Wuniv.preΨ k * (Polynomial.C Wuniv.a₁ * Polynomial.X +
        Polynomial.C Wuniv.a₃)) •
          (1 : Wuniv.toAffine.CoordinateRing) +
        (2 * Wuniv.preΨ k) • CoordinateRing.mk Wuniv Polynomial.X = 0 := by
      rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, ← map_mul,
        ← map_add]
      exact hzero
    have h2 := (CoordinateRing.smul_basis_eq_zero hsmul).2
    rcases mul_eq_zero.mp h2 with hc | hc
    · have h := congrArg (fun p => Polynomial.coeff p 0) hc
      simp only [Polynomial.coeff_ofNat_zero, Polynomial.coeff_zero] at h
      have h' := congrArg (MvPolynomial.eval fun _ => (0 : ℤ)) h
      norm_num [map_ofNat] at h'
    · exact hpre hc
  · rw [if_neg he, mul_one]
    intro hzero
    have hsmul : (Wuniv.preΨ k) •
        (1 : Wuniv.toAffine.CoordinateRing) +
        (0 : (MvPolynomial (Fin 5) ℤ)[X]) •
          CoordinateRing.mk Wuniv Polynomial.X = 0 := by
      simp only [CoordinateRing.smul, mul_one, map_zero, zero_mul,
        add_zero]
      exact hzero
    exact hpre (CoordinateRing.smul_basis_eq_zero hsmul).1

end PsiSumCompanion

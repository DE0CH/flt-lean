/-
PsiSumCompanion.lean — own work for the Fermat project (not vendored).

The on-curve **sum-companion of the even recurrence** for division
polynomials, derived from the universal EDS identity
`EllipticDivisibilitySequence.normEDS_sum_companion`:

`ψₙ₋₁²ψₙ₊₂ + ψₙ₋₂ψₙ₊₁² = ψₙ₋₁ψₙψₙ₊₁(6x² + b₂x + b₄) − ψₙ³ Ψ₂Sq(x)`

at any point of any Weierstrass curve. Pipeline:

1. `anchor`: the `R[X]`-identity `Ψ₃(6X² + b₂X + b₄) = preΨ₄ + Ψ₂Sq²`
   (pure `ring` in the `a`-coefficients).
2. `psi_mul_sumDiff`: for ANY `W`, in `R[X][Y]`,
   `ψ₂ ⬝ CΨ₃ ⬝ sumDiff = 4 ⬝ W.polynomial ⬝ (explicit cofactor)` —
   from the universal identity instantiated at
   `ψ = normEDS ψ₂ (C Ψ₃) (C preΨ₄)` (definitional), the anchor, and
   `ψ₂² = C Ψ₂Sq + 4 ⬝ polynomial`. Hence
   `mk W (ψ₂ ⬝ CΨ₃) ⬝ mk W sumDiff = 0` in the coordinate ring.
3. Over the UNIVERSAL curve (generic `a`-coefficients in
   `MvPolynomial (Fin 5) ℤ`) the coordinate ring is a domain and
   `mk (ψ₂ ⬝ CΨ₃) ≠ 0` (its `Y`-coordinate in the `{1, Y}`-basis is
   `2Ψ₃ ≠ 0`), so `mk sumDiff = 0` there.
4. Functoriality (`CoordinateRing.map`) specialises to any `W/R`:
   `mk W sumDiff = 0`, i.e. `W.polynomial ∣ sumDiff`; evaluating at a
   point of the curve gives the value-level identity.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Fermat.FLT.EllipticCurve.UniversalCurve
public import Fermat.FLT.Mathlib.NumberTheory.EDSStange
import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

namespace PsiSumCompanion

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
  EllipticDivisibilitySequence

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

set_option backward.isDefEq.respectTransparency false in
/-- **The anchor identity** (PROVEN): `Ψ₃(6X² + b₂X + b₄) = preΨ₄ + Ψ₂Sq²`
in `R[X]` — the `n = 2` instance of the sum-companion, witnessing that
`(6x² + b₂x + b₄)` is the EDS-intrinsic quantity `(ψ₄/ψ₂ + ψ₂⁴)/ψ₃`. -/
theorem anchor : W.Ψ₃ * (C 6 * X ^ 2 + C W.b₂ * X + C W.b₄) =
    W.preΨ₄ + W.Ψ₂Sq ^ 2 := by
  rw [Ψ₃, preΨ₄, Ψ₂Sq, b₂, b₄, b₆, b₈]
  C_simp
  ring1

/-- The sum-companion difference in `R[X][Y]`: the on-curve identity
asserts precisely that this maps to `0` in the coordinate ring. -/
noncomputable def sumDiff (n : ℤ) : R[X][Y] :=
  (W.ψ (n - 1) ^ 2 * W.ψ (n + 2) + W.ψ (n - 2) * W.ψ (n + 1) ^ 2) -
    (W.ψ (n - 1) * W.ψ n * W.ψ (n + 1) *
      C (C 6 * X ^ 2 + C W.b₂ * X + C W.b₄) -
     W.ψ n ^ 3 * C W.Ψ₂Sq)

set_option backward.isDefEq.respectTransparency false in
/-- **The multiplied sum-companion** (PROVEN modulo the universal EDS
node): in `R[X][Y]`, `ψ₂ ⬝ CΨ₃ ⬝ sumDiff n` is an explicit multiple of
the curve polynomial. -/
theorem psi₂_mul_sumDiff (n : ℤ) :
    W.ψ₂ * C W.Ψ₃ * sumDiff W n =
      4 * W.toAffine.polynomial * W.ψ₂ *
        (W.ψ (n - 1) * W.ψ n * W.ψ (n + 1) * (W.ψ₂ ^ 2 + C W.Ψ₂Sq) -
          W.ψ n ^ 3 * C W.Ψ₃) := by
  have hstar := normEDS_sum_companion W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
  have hanchor : (C (W.Ψ₃ * (C 6 * X ^ 2 + C W.b₂ * X + C W.b₄)) :
      R[X][Y]) = C (W.preΨ₄ + W.Ψ₂Sq ^ 2) := by rw [anchor W]
  have hψsq := W.ψ₂_sq
  rw [sumDiff]
  simp only [WeierstrassCurve.ψ]
  simp only [C_add, C_mul, C_pow] at hanchor ⊢
  linear_combination hstar -
    (normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) (n - 1) *
      normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
      normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) (n + 1) * W.ψ₂) * hanchor +
    (W.ψ₂ * (normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) (n - 1) *
        normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
        normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) (n + 1) *
        (W.ψ₂ ^ 2 + C W.Ψ₂Sq) -
      normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n ^ 3 * C W.Ψ₃)) * hψsq

set_option backward.isDefEq.respectTransparency false in
/-- In the coordinate ring, `mk (ψ₂ ⬝ CΨ₃) ⬝ mk (sumDiff n) = 0`. -/
theorem mk_psi₂_mul_mk_sumDiff (n : ℤ) :
    CoordinateRing.mk W (W.ψ₂ * C W.Ψ₃) *
      CoordinateRing.mk W (sumDiff W n) = 0 := by
  rw [← map_mul, psi₂_mul_sumDiff]
  simp only [map_mul, AdjoinRoot.mk_self, mul_zero, zero_mul]

/-! ## The universal curve (see `UniversalCurve.lean` for `Wuniv`) -/

set_option backward.isDefEq.respectTransparency false in
/-- Over the universal curve, `mk (ψ₂ ⬝ CΨ₃) ≠ 0`: its coordinates in
the `{1, Y}`-basis are `(Ψ₃(a₁X + a₃), 2Ψ₃)`, and `2Ψ₃ ≠ 0` since the
`X⁴`-coefficient of `Ψ₃` is `3`. -/
theorem mk_psi₂_mul_C_ne_zero :
    CoordinateRing.mk Wuniv (Wuniv.ψ₂ * C Wuniv.Ψ₃) ≠ 0 := by
  intro hzero
  have hrepr : Wuniv.ψ₂ * C Wuniv.Ψ₃ =
      C (Wuniv.Ψ₃ * (C Wuniv.a₁ * X + C Wuniv.a₃)) +
        C (2 * Wuniv.Ψ₃) * Y := by
    rw [WeierstrassCurve.ψ₂, Affine.polynomialY]
    C_simp
    ring1
  rw [hrepr] at hzero
  have hsmul : (Wuniv.Ψ₃ * (C Wuniv.a₁ * X + C Wuniv.a₃)) •
      (1 : Wuniv.toAffine.CoordinateRing) +
      (2 * Wuniv.Ψ₃) • CoordinateRing.mk Wuniv Y = 0 := by
    rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, ← map_mul,
      ← map_add]
    exact hzero
  have h2 := (CoordinateRing.smul_basis_eq_zero hsmul).2
  have h3 : (2 * Wuniv.Ψ₃).coeff 4 = 6 := by
    rw [coeff_ofNat_mul, coeff_Ψ₃]
    norm_num
  rw [h2, Polynomial.coeff_zero] at h3
  have h4 := congrArg (MvPolynomial.eval fun _ => (0 : ℤ)) h3
  norm_num [map_ofNat] at h4

set_option backward.isDefEq.respectTransparency false in
/-- Over the universal curve, `mk (sumDiff n) = 0` — the domain
cancellation. -/
theorem mk_sumDiff_univ (n : ℤ) :
    CoordinateRing.mk Wuniv (sumDiff Wuniv n) = 0 := by
  rcases mul_eq_zero.mp (mk_psi₂_mul_mk_sumDiff Wuniv n) with h | h
  · exact absurd h mk_psi₂_mul_C_ne_zero
  · exact h

/-! ## Specialisation to an arbitrary curve -/

set_option backward.isDefEq.respectTransparency false in
/-- `sumDiff` is compatible with base change. -/
theorem map_sumDiff {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (sumDiff W n).map (mapRingHom f) = sumDiff (W.map f) n := by
  simp only [sumDiff, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, map_ψ, Polynomial.map_C,
    map_Ψ₂Sq, map_b₂, map_b₄, Polynomial.coe_mapRingHom, map_ofNat,
    Polynomial.map_ofNat, Polynomial.map_X]

set_option backward.isDefEq.respectTransparency false in
/-- **The sum-companion holds in every coordinate ring**: the curve
polynomial divides `sumDiff n` for every Weierstrass curve, by
specialising the universal case. -/
theorem mk_sumDiff (n : ℤ) : CoordinateRing.mk W (sumDiff W n) = 0 := by
  let σ : MvPolynomial (Fin 5) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hmap : Wuniv.map σ = W := by
    simp only [Wuniv, WeierstrassCurve.map, MvPolynomial.eval₂Hom_X', σ]
    rfl
  have hzero := congrArg (CoordinateRing.map Wuniv σ) (mk_sumDiff_univ n)
  rw [CoordinateRing.map_mk, map_zero, map_sumDiff] at hzero
  rw [← hmap]
  exact hzero

set_option backward.isDefEq.respectTransparency false in
/-- **The value-level sum-companion**: at any point of the curve,
`ψₙ₋₁²ψₙ₊₂ + ψₙ₋₂ψₙ₊₁² = ψₙ₋₁ψₙψₙ₊₁(6x² + b₂x + b₄) − ψₙ³ Ψ₂Sq(x)`. -/
theorem evalEval_ψ_sum (n : ℤ) {x y : R}
    (h : W.toAffine.Equation x y) :
    (W.ψ (n - 1)).evalEval x y ^ 2 * (W.ψ (n + 2)).evalEval x y +
      (W.ψ (n - 2)).evalEval x y * (W.ψ (n + 1)).evalEval x y ^ 2 =
    (W.ψ (n - 1)).evalEval x y * (W.ψ n).evalEval x y *
      (W.ψ (n + 1)).evalEval x y * (6 * x ^ 2 + W.b₂ * x + W.b₄) -
    (W.ψ n).evalEval x y ^ 3 * W.Ψ₂Sq.eval x := by
  obtain ⟨g, hg⟩ := AdjoinRoot.mk_eq_zero.mp (mk_sumDiff W n)
  have hz := congrArg (Polynomial.evalEval x y) hg
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  rw [sumDiff] at hz
  simp only [Polynomial.evalEval_mul, Polynomial.evalEval_add,
    Polynomial.evalEval_sub, Polynomial.evalEval_pow,
    Polynomial.evalEval_C, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    h0, zero_mul] at hz
  linear_combination hz

end PsiSumCompanion

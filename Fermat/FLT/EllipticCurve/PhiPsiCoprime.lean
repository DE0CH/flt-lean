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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **The `(2,3)` Bézout certificate** (PROVEN, sympy-extracted
Sylvester-adjugate cofactors): `F ⬝ Ψ₂Sq + G ⬝ Ψ₃ = −Δ²` modulo the
`b`-invariant relation, so `Ψ₂Sq` and `Ψ₃` cannot vanish together
when `Δ ≠ 0`. -/
theorem psi23_not_both_zero (hΔ : W.Δ ≠ 0) (x₀ : K)
    (h2 : (W.Ψ₂Sq).eval x₀ = 0) (h3 : (W.Ψ₃).eval x₀ = 0) : False := by
  set B2 : Polynomial K := Polynomial.C W.b₂ with hB2
  set B4 : Polynomial K := Polynomial.C W.b₄ with hB4
  set B6 : Polynomial K := Polynomial.C W.b₆ with hB6
  set B8 : Polynomial K := Polynomial.C W.b₈ with hB8
  have hrelC : B2 * B6 - B4 ^ 2 = 4 * B8 := by
    rw [hB2, hB4, hB6, hB8, ← Polynomial.C_mul, ← Polynomial.C_pow,
      ← Polynomial.C_sub, ← W.b_relation,
      show ((4 : Polynomial K)) = Polynomial.C (4 : K) from
        (map_ofNat _ 4).symm, ← Polynomial.C_mul]
  have hcert : (-729*B6^3 - 972*Polynomial.X^3*B6^2 - 216*Polynomial.X*B4^4 - 216*Polynomial.X^3*B4^3 - 192*Polynomial.X*B8^2 - 108*B6*B4^3 - 16*B2*B8^2 - 4*B2^3*B6^2 + Polynomial.X*B8*B2^4 + B4*B8*B2^3 - B8*Polynomial.X^2*B2^3 - 1134*Polynomial.X*B4*B6^2 - 351*B2*Polynomial.X^2*B6^2 - 72*B2*Polynomial.X^2*B4^3 - 36*B2*B8*B4^2 - 12*B8*Polynomial.X^3*B2^2 - 7*B6*B8*B2^2 - 6*B6*Polynomial.X^3*B2^3 - 3*Polynomial.X*B2^2*B6^2 - 2*B6*Polynomial.X^2*B2^4 + 2*Polynomial.X^2*B2^3*B4^2 + 3*B6*B2^2*B4^2 + 6*Polynomial.X*B2^2*B4^3 + 6*Polynomial.X^3*B2^2*B4^2 + 108*B6*Polynomial.X^2*B4^2 + 162*B2*B4*B6^2 + 288*B4*B8*Polynomial.X^3 + 432*Polynomial.X*B8*B4^2 + 432*B4*B6*B8 + 432*B6*B8*Polynomial.X^2 - 50*Polynomial.X*B4*B8*B2^2 - 7*Polynomial.X*B4*B6*B2^3 + 81*B4*B6*Polynomial.X^2*B2^2 + 168*Polynomial.X*B2*B6*B8 + 252*B2*B4*B6*Polynomial.X^3 + 288*Polynomial.X*B2*B6*B4^2) * W.Ψ₂Sq +
      (144*B4^4 + 256*B8^2 + B2^2*B6^2 - B8*B2^4 - 384*B8*B4^2 - 4*B2^2*B4^3 + 288*Polynomial.X^2*B4^3 + 864*B4*B6^2 + 1296*Polynomial.X^2*B6^2 - 576*Polynomial.X*B6*B8 - 384*B4*B8*Polynomial.X^2 - 204*B2*B6*B4^2 - 176*B2*B6*B8 - 144*Polynomial.X*B6*B4^2 - 8*Polynomial.X^2*B2^2*B4^2 - 2*Polynomial.X*B2^3*B4^2 + 2*Polynomial.X*B6*B2^4 + 5*B4*B6*B2^3 + 8*B6*Polynomial.X^2*B2^3 + 16*B8*Polynomial.X^2*B2^2 + 48*B4*B8*B2^2 + 72*Polynomial.X*B2*B4^3 + 360*Polynomial.X*B2*B6^2 - 336*B2*B4*B6*Polynomial.X^2 - 80*Polynomial.X*B4*B6*B2^2 + 32*Polynomial.X*B2*B4*B8) * W.Ψ₃ = -(Polynomial.C (W.Δ ^ 2)) := by
    rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
      show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 +
        9 * W.b₂ * W.b₄ * W.b₆ from rfl]
    simp only [map_ofNat, Polynomial.C_neg, Polynomial.C_add,
      Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, ← hB2,
      ← hB4, ← hB6, ← hB8]
    linear_combination (-(64*B4^4 + 64*B8^2 - 112*B8*B4^2 + 4*B2^2*B6^2 + 324*B4*B6^2 - 80*B2*B6*B4^2 - 32*B2*B6*B8 + 12*B4*B8*B2^2)) * hrelC
  have hev := congrArg (Polynomial.eval x₀) hcert
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_neg, Polynomial.eval_C] at hev
  rw [h2, h3, mul_zero, mul_zero, add_zero] at hev
  exact hΔ (pow_eq_zero_iff two_ne_zero |>.mp
    (by linear_combination hev))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 40000000 in
/-- **The `(3,4)` Bézout certificate** (PROVEN, sympy-extracted
Sylvester-cofactor column): `F ⬝ Ψ₃ + G ⬝ preΨ₄ = Δ⁴` modulo the
`b`-invariant relation, so `Ψ₃` and `preΨ₄` cannot vanish together
when `Δ ≠ 0`. -/
theorem psi34_not_both_zero (hΔ : W.Δ ≠ 0) (x₀ : K)
    (h3 : (W.Ψ₃).eval x₀ = 0) (h4 : (W.preΨ₄).eval x₀ = 0) : False := by
  set B2 : Polynomial K := Polynomial.C W.b₂ with hB2
  set B4 : Polynomial K := Polynomial.C W.b₄ with hB4
  set B6 : Polynomial K := Polynomial.C W.b₆ with hB6
  set B8 : Polynomial K := Polynomial.C W.b₈ with hB8
  have hrelC : B2 * B6 - B4 ^ 2 = 4 * B8 := by
    rw [hB2, hB4, hB6, hB8, ← Polynomial.C_mul, ← Polynomial.C_pow,
      ← Polynomial.C_sub, ← W.b_relation,
      show ((4 : Polynomial K)) = Polynomial.C (4 : K) from
        (map_ofNat _ 4).symm, ← Polynomial.C_mul]
  set Fc : Polynomial K := (614656*B8^5 + B2^8*B8^3 - 592704*B4^2*B8^4 - 400464*B6^4*B8^2 - 308367*B4*B6^6 - 20412*B4^6*B8^2 - 1632*B2^4*B8^4 + 7*B2^5*B6^5 + 1944*B2^2*B6^6 + 2187*B4^7*B6^2 + 6561*B4^4*B6^4 + 131712*Polynomial.X^4*B8^4 + 190512*B4^4*B8^3 + 314928*Polynomial.X^5*B6^5 + 1614006*Polynomial.X^2*B6^6 + Polynomial.X^2*B2^6*B6^4 + Polynomial.X^4*B2^8*B8^2 - B2^5*B4^3*B6^3 - 2558304*Polynomial.X^2*B6^2*B8^3 - 1843968*Polynomial.X*B6*B8^4 - 666360*B4^3*B6^2*B8^2 - 639744*B2*B6*B8^4 - 508032*B6*Polynomial.X^5*B8^3 - 317520*Polynomial.X^2*B4^3*B8^3 - 127008*Polynomial.X^4*B4^2*B8^3 - 91854*Polynomial.X^3*B4^4*B6^3 - 52488*B8*Polynomial.X^4*B6^4 - 45927*Polynomial.X*B2*B6^6 - 39944*B2^2*B4^3*B8^3 - 38880*Polynomial.X^3*B6^3*B8^2 - 34992*Polynomial.X^5*B4^3*B6^3 - 28431*Polynomial.X^2*B4^3*B6^4 - 10935*B6*Polynomial.X^3*B4^7 - 10935*B8*Polynomial.X^2*B4^7 - 10935*Polynomial.X^2*B4^6*B6^2 - 7432*B2^3*B6^3*B8^2 - 6075*Polynomial.X^3*B2^2*B6^5 - 5600*Polynomial.X^2*B2^2*B8^4 - 5346*B2*B4^5*B6^3 - 5264*Polynomial.X*B2^3*B8^4 - 4374*B6*Polynomial.X^5*B4^6 - 4374*B8*Polynomial.X^4*B4^6 - 1422*B4*B2^3*B6^5 - 1152*Polynomial.X^5*B2^3*B8^3 - 808*Polynomial.X^4*B2^4*B8^3 - 165*Polynomial.X*B2^4*B6^5 - 111*B4*B2^6*B8^3 - 92*Polynomial.X^3*B2^5*B8^3 - 78*B2^4*B4^4*B8^2 - 54*B2^2*B4^6*B6^2 - 27*B2^6*B6^2*B8^2 - 22*Polynomial.X^3*B2^5*B6^4 - 18*B2^4*B4^2*B6^4 + 2*Polynomial.X^5*B2^7*B8^2 + 9*Polynomial.X*B2^7*B8^3 + 10*Polynomial.X^2*B2^6*B8^3 + 162*B2^3*B4^4*B6^3 + 519*Polynomial.X^4*B2^4*B6^4 + 693*B8*B2^4*B6^4 + 864*B6*B2^5*B8^3 + 1107*B2^2*B4^3*B6^4 + 1134*Polynomial.X^5*B2^3*B6^4 + 3663*B2^2*B4^5*B8^2 + 3760*B2^4*B4^2*B8^3 + 4374*Polynomial.X^4*B4^5*B6^2 + 6075*Polynomial.X^2*B2^3*B6^5 + 10935*Polynomial.X*B4^5*B6^3 + 40824*Polynomial.X^4*B4^4*B8^2 + 45684*B2*B4^2*B6^5 + 46899*B8*B4^5*B6^2 + 53312*B2*Polynomial.X^3*B8^4 + 56862*Polynomial.X^4*B4^2*B6^4 + 88816*B4*B2^2*B8^4 + 102060*Polynomial.X^2*B4^5*B8^2 + 144342*B2*Polynomial.X^4*B6^5 + 148716*Polynomial.X*B4^2*B6^5 + 179888*B2^2*B6^2*B8^3 + 188568*B2*B8*B6^5 + 329280*B4*Polynomial.X^2*B8^4 + 734832*B4*Polynomial.X^3*B6^5 + 983664*B8*B4^2*B6^4 + 1259712*Polynomial.X*B8*B6^5 + 1553328*B4*B6^2*B8^3 + B8*Polynomial.X^3*B2^7*B6^2 + Polynomial.X^4*B2^6*B4^2*B6^2 - B4*Polynomial.X^3*B2^6*B6^3 - 4639356*B4*B8*Polynomial.X^2*B6^4 - 3251664*Polynomial.X*B4*B6^3*B8^2 - 2118960*B8*Polynomial.X^3*B4^2*B6^3 - 1213632*B4*B6*Polynomial.X^3*B8^3 - 886464*B4*B8*Polynomial.X^5*B6^3 - 756648*B2*B4*B6^3*B8^2 - 375192*Polynomial.X*B8*B4^3*B6^3 - 356238*B8*Polynomial.X^2*B4^4*B6^2 - 327264*B2*B6*Polynomial.X^4*B8^3 - 270459*B2*B4*Polynomial.X^2*B6^5 - 211410*B2*B8*B4^3*B6^3 - 157248*Polynomial.X*B2*B4^3*B8^3 - 89424*B8*Polynomial.X^4*B4^3*B6^2 - 75816*B8*Polynomial.X^2*B2^2*B6^4 - 71604*B2*Polynomial.X^3*B4^4*B8^2 - 71352*Polynomial.X*B2^2*B6^3*B8^2 - 64395*B2*Polynomial.X^3*B4^2*B6^4 - 57348*B6*B8*Polynomial.X^3*B4^5 - 43432*B4*B6*B2^3*B8^3 - 40824*B2*B4*Polynomial.X^5*B6^4 - 36288*B2*Polynomial.X^5*B4^3*B8^2 - 30224*B6*Polynomial.X^3*B2^2*B8^3 - 29160*Polynomial.X*B6*B8*B4^6 - 28188*Polynomial.X*B2*B4^3*B6^4 - 28188*B2*Polynomial.X^4*B4^3*B6^3 - 26406*B4*B8*B2^2*B6^4 - 25272*B6*B8*Polynomial.X^5*B4^4 - 22656*Polynomial.X^4*B2^2*B4^3*B8^2 - 18792*B4*Polynomial.X^4*B2^2*B6^4 - 17496*B8*Polynomial.X^5*B2^2*B6^3 - 14034*B6*B2^3*B4^3*B8^2 - 11694*Polynomial.X^2*B2^2*B4^4*B8^2 - 9423*Polynomial.X^3*B2^2*B4^3*B6^3 - 9072*Polynomial.X*B6*B4^4*B8^2 - 8502*B8*Polynomial.X^4*B2^3*B6^3 - 5103*B2*B6*B8*B4^6 - 2992*B6*Polynomial.X^2*B2^3*B8^3 - 2290*B4*B2^4*B6^2*B8^2 - 2187*B2*B6*Polynomial.X^4*B4^6 - 1674*Polynomial.X^5*B2^2*B4^2*B6^3 - 1084*B4*Polynomial.X^2*B2^4*B8^3 - 972*B2*B8*Polynomial.X^3*B6^4 - 880*Polynomial.X*B4*B2^5*B8^3 - 864*Polynomial.X^3*B2^3*B4^4*B6^2 - 756*Polynomial.X^2*B2^3*B4^3*B6^3 - 705*Polynomial.X*B2^3*B4^4*B8^2 - 513*Polynomial.X^4*B2^3*B4^2*B6^3 - 456*B8*B2^4*B4^3*B6^2 - 415*Polynomial.X^3*B2^5*B4^2*B8^2 - 324*Polynomial.X^5*B2^3*B4^3*B6^2 - 316*B8*Polynomial.X^2*B2^5*B6^3 - 306*B8*Polynomial.X^3*B2^3*B4^5 - 274*Polynomial.X*B2^5*B6^2*B8^2 - 270*Polynomial.X*B2^2*B4^4*B6^3 - 200*B4*Polynomial.X^5*B2^5*B8^2 - 162*Polynomial.X^4*B2^4*B4^3*B6^2 - 144*B8*Polynomial.X^5*B2^3*B4^4 - 102*B4*Polynomial.X^4*B2^6*B8^2 - 84*B4*Polynomial.X^2*B2^4*B6^4 - 72*B8*Polynomial.X^4*B2^4*B4^4 - 72*B8*Polynomial.X^5*B2^5*B6^2 - 34*B8*Polynomial.X^4*B2^6*B6^2 - 5*Polynomial.X*B4*B2^5*B6^4 - 4*Polynomial.X^2*B2^6*B4^2*B8^2 - 3*B4*B6*B2^7*B8^2 + 2*Polynomial.X*B2^5*B4^3*B8^2 + 2*Polynomial.X^5*B2^5*B4^2*B6^2 + 3*B8*B2^6*B4^2*B6^2 + 4*B4*Polynomial.X^3*B2^7*B8^2 + 5*Polynomial.X^2*B2^5*B4^2*B6^3 + 5*Polynomial.X^3*B2^5*B4^3*B6^2 + 7*Polynomial.X*B8*B2^6*B6^3 + 7*B6*Polynomial.X^3*B2^6*B8^2 + 10*B6*Polynomial.X^2*B2^7*B8^2 + 16*B4*Polynomial.X^4*B2^5*B6^3 + 25*B4*B8*B2^5*B6^3 + 36*B4*Polynomial.X^5*B2^4*B6^3 + 54*B6*Polynomial.X^4*B2^3*B4^5 + 108*B6*Polynomial.X^5*B2^2*B4^5 + 126*B6*B8*B2^3*B4^5 + 189*Polynomial.X^2*B2^2*B4^2*B6^4 + 223*B8*Polynomial.X^3*B2^4*B6^3 + 252*Polynomial.X^3*B2^4*B4^2*B6^3 + 270*B6*Polynomial.X^3*B2^2*B4^6 + 270*B8*Polynomial.X^2*B2^2*B4^6 + 270*Polynomial.X^2*B2^2*B4^5*B6^2 + 385*Polynomial.X^2*B2^4*B4^3*B8^2 + 424*B6*B2^5*B4^2*B8^2 + 734*B6*Polynomial.X^4*B2^5*B8^2 + 846*Polynomial.X*B2^3*B4^2*B6^4 + 1092*Polynomial.X^3*B2^3*B6^2*B8^2 + 1440*B6*Polynomial.X^5*B2^4*B8^2 + 2400*B4*Polynomial.X^3*B2^3*B8^3 + 2511*B8*B2^3*B4^2*B6^3 + 3024*B8*Polynomial.X^4*B2^2*B4^5 + 3062*Polynomial.X^4*B2^4*B4^2*B8^2 + 3357*B4*Polynomial.X^3*B2^3*B6^4 + 5238*Polynomial.X^4*B2^2*B4^4*B6^2 + 5720*Polynomial.X*B6*B2^4*B8^3 + 5792*Polynomial.X^5*B2^3*B4^2*B8^2 + 5832*B2*B8*Polynomial.X^5*B4^5 + 5994*Polynomial.X*B4*B2^2*B6^5 + 6114*Polynomial.X*B8*B2^3*B6^4 + 7260*Polynomial.X^2*B2^4*B6^2*B8^2 + 10692*B2*Polynomial.X^5*B4^4*B6^2 + 12176*Polynomial.X^3*B2^3*B4^3*B8^2 + 12393*B2*B8*Polynomial.X^3*B4^6 + 13410*B8*B2^2*B4^4*B6^2 + 24543*B2*Polynomial.X^2*B4^4*B6^3 + 25048*Polynomial.X*B2^3*B4^2*B8^3 + 25272*Polynomial.X*B2*B4^5*B8^2 + 28917*B2*Polynomial.X^3*B4^5*B6^2 + 35568*Polynomial.X^2*B2^2*B4^2*B8^3 + 41216*B4*Polynomial.X^4*B2^2*B8^3 + 48600*B2*B6*B4^4*B8^2 + 56448*B2*B4*Polynomial.X^5*B8^3 + 85680*B2*Polynomial.X^3*B4^2*B8^3 + 103824*B2*B6*B4^2*B8^3 + 149832*Polynomial.X^4*B2^2*B6^2*B8^2 + 200916*B2^2*B4^2*B6^2*B8^2 + 235872*B4*Polynomial.X^4*B6^2*B8^2 + 244608*Polynomial.X*B2*B4*B8^4 + 284256*B6*Polynomial.X^5*B4^2*B8^2 + 295488*B2*Polynomial.X^5*B6^2*B8^2 + 674352*B6*Polynomial.X^3*B4^3*B8^2 + 903168*Polynomial.X*B6*B4^2*B8^3 + 1082928*Polynomial.X*B2*B6^2*B8^3 + 1469664*B2*Polynomial.X^2*B6^3*B8^2 + 2036448*Polynomial.X^2*B4^2*B6^2*B8^2 - 444528*B2*B4*B8*Polynomial.X^4*B6^3 - 390492*B4*Polynomial.X^2*B2^2*B6^2*B8^2 - 285184*Polynomial.X*B4*B6*B2^2*B8^3 - 220104*B2*B6*Polynomial.X^2*B4^3*B8^2 - 180648*B6*Polynomial.X^3*B2^2*B4^2*B8^2 - 170424*Polynomial.X*B2*B4*B8*B6^4 - 88896*Polynomial.X*B6*B2^2*B4^3*B8^2 - 87183*B8*Polynomial.X^2*B2^2*B4^3*B6^2 - 74304*B4*B6*Polynomial.X^5*B2^2*B8^2 - 50220*B4*B8*Polynomial.X^3*B2^2*B6^3 - 40401*B6*B8*Polynomial.X^3*B2^2*B4^4 - 37632*B4*B6*Polynomial.X^4*B2^3*B8^2 - 18144*B6*B8*Polynomial.X^5*B2^2*B4^3 - 9384*B6*B8*Polynomial.X^4*B2^3*B4^3 - 5541*B4*B8*Polynomial.X^2*B2^3*B6^3 - 4872*Polynomial.X*B4*B2^3*B6^2*B8^2 - 2430*B2*B6*B8*Polynomial.X^4*B4^4 - 2112*Polynomial.X*B8*B2^3*B4^3*B6^2 - 1572*B6*B8*Polynomial.X^2*B2^3*B4^4 - 1047*B4*B6*Polynomial.X^2*B2^5*B8^2 - 648*B4*B8*Polynomial.X^5*B2^3*B6^2 - 468*B4*B8*Polynomial.X^4*B2^4*B6^2 - 258*Polynomial.X*B4*B8*B2^4*B6^3 - 256*B4*B8*Polynomial.X^3*B2^5*B6^2 - 25*Polynomial.X*B4*B6*B2^6*B8^2 - 17*B4*B8*Polynomial.X^2*B2^6*B6^2 - 9*B6*B8*Polynomial.X^3*B2^6*B4^2 - 4*B4*B6*B8*Polynomial.X^5*B2^6 - 2*B4*B6*B8*Polynomial.X^4*B2^7 + 5*B6*B8*Polynomial.X^2*B2^5*B4^3 + 12*Polynomial.X*B8*B2^5*B4^2*B6^2 + 300*B6*B8*Polynomial.X^4*B2^5*B4^2 + 596*B6*B8*Polynomial.X^5*B2^4*B4^2 + 702*Polynomial.X*B8*B2^2*B4^2*B6^3 + 720*Polynomial.X*B6*B8*B2^2*B4^5 + 729*B8*Polynomial.X^3*B2^3*B4^2*B6^2 + 1334*B6*B8*Polynomial.X^3*B2^4*B4^3 + 2840*B8*Polynomial.X^2*B2^4*B4^2*B6^2 + 3098*Polynomial.X*B6*B2^4*B4^2*B8^2 + 3176*B4*B6*Polynomial.X^3*B2^4*B8^2 + 31940*B6*Polynomial.X^2*B2^3*B4^2*B8^2 + 57591*B2*B6*B8*Polynomial.X^2*B4^5 + 71523*Polynomial.X*B2*B8*B4^4*B6^2 + 117450*B8*Polynomial.X^4*B2^2*B4^2*B6^2 + 127344*B2*B4*B6*Polynomial.X^2*B8^3 + 133920*B2*B6*Polynomial.X^4*B4^2*B8^2 + 227232*B2*B8*Polynomial.X^5*B4^2*B6^2 + 511272*B2*B8*Polynomial.X^3*B4^3*B6^2 + 808272*B2*B4*Polynomial.X^3*B6^2*B8^2 + 959256*Polynomial.X*B2*B4^2*B6^2*B8^2 + 1193076*B2*B8*Polynomial.X^2*B4^2*B6^3) with hFc
  set Gc : Polynomial K := (-531441*B6^6 - B2^6*B6^4 - 472392*Polynomial.X^3*B6^5 - 197568*B4*B8^4 - 197568*Polynomial.X^2*B8^4 - 61236*B4^5*B8^2 - 39366*B4^3*B6^4 - 2187*B2^3*B6^5 - 9*B2^6*B8^3 + 5264*B2^2*B8^4 + 6561*B8*B4^7 + 190512*B4^3*B8^3 + 789264*B6^2*B8^3 - Polynomial.X^2*B2^8*B8^2 - 818424*B4^2*B6^2*B8^2 - 441288*B2*B6^3*B8^2 - 393660*Polynomial.X*B4*B6^5 - 137781*B2*Polynomial.X^2*B6^5 - 85293*Polynomial.X^2*B4^2*B6^4 - 61236*Polynomial.X^2*B4^4*B8^2 - 47040*Polynomial.X*B2*B8^4 - 22104*B2^2*B4^2*B8^3 - 6561*Polynomial.X^2*B4^5*B6^2 - 4374*B2^2*B4^2*B6^4 - 2238*B2^4*B6^2*B8^2 - 1701*Polynomial.X^3*B2^3*B6^4 - 824*B6*B2^3*B8^3 - 495*Polynomial.X^2*B2^4*B6^4 - 216*B2^4*B4^3*B8^2 - 162*B8*B2^2*B4^6 - 54*B2^3*B4^3*B6^3 - 3*B6*B2^7*B8^2 - 3*Polynomial.X^3*B2^7*B8^2 + 2*B2^6*B4^2*B8^2 + 21*Polynomial.X*B2^5*B6^4 + 67*B8*B2^5*B6^3 + 80*Polynomial.X*B2^5*B8^3 + 162*B4*B2^4*B6^4 + 800*B4*B2^4*B8^3 + 924*Polynomial.X^2*B2^4*B8^3 + 1728*Polynomial.X^3*B2^3*B8^3 + 2187*B2*B4^4*B6^3 + 5832*Polynomial.X*B2^2*B6^5 + 6561*Polynomial.X*B6*B4^7 + 6561*B6*Polynomial.X^3*B4^6 + 6561*B8*Polynomial.X^2*B4^6 + 7065*B2^2*B4^4*B8^2 + 15066*B8*B2^2*B6^4 + 52488*Polynomial.X^3*B4^3*B6^3 + 58320*Polynomial.X*B6^3*B8^2 + 59049*Polynomial.X*B4^4*B6^3 + 78732*B8*Polynomial.X^2*B6^4 + 118098*B2*B4*B6^5 + 181521*B8*B4^4*B6^2 + 190512*Polynomial.X^2*B4^2*B8^3 + 762048*B6*Polynomial.X^3*B8^3 + 1522152*B4*B8*B6^4 + Polynomial.X*B4*B2^6*B6^3 - Polynomial.X*B8*B2^7*B6^2 - Polynomial.X^2*B2^6*B4^2*B6^2 - 443232*B2*Polynomial.X^3*B6^2*B8^2 - 426384*B6*Polynomial.X^3*B4^2*B8^2 - 404838*B2*B8*B4^2*B6^3 - 371952*Polynomial.X*B6*B4^3*B8^2 - 353808*B4*Polynomial.X^2*B6^2*B8^2 - 150876*Polynomial.X^2*B2^2*B6^2*B8^2 - 84672*B2*B4*Polynomial.X^3*B8^3 - 47712*B4*Polynomial.X^2*B2^2*B8^3 - 33264*Polynomial.X*B2*B4^2*B8^3 - 26973*B2*B6*B8*B4^5 - 18225*Polynomial.X*B2*B4^5*B6^2 - 16038*B2*Polynomial.X^3*B4^4*B6^2 - 11934*B6*B2^3*B4^2*B8^2 - 11664*Polynomial.X*B2*B8*B6^4 - 8748*B2*B8*Polynomial.X^3*B4^5 - 8688*Polynomial.X^3*B2^3*B4^2*B8^2 - 6561*Polynomial.X*B2*B8*B4^6 - 6360*Polynomial.X*B2^3*B4^3*B8^2 - 5184*Polynomial.X^2*B2^2*B4^4*B6^2 - 3145*Polynomial.X^2*B2^4*B4^2*B8^2 - 3078*B8*Polynomial.X^2*B2^2*B4^5 - 3024*B2*B4*B6*B8^3 - 2944*Polynomial.X*B4*B2^3*B8^3 - 2160*B6*Polynomial.X^3*B2^4*B8^2 - 2079*Polynomial.X*B4*B2^3*B6^4 - 1116*Polynomial.X*B2^3*B6^2*B8^2 - 900*B8*B2^4*B4^2*B6^2 - 741*B6*Polynomial.X^2*B2^5*B8^2 - 273*Polynomial.X*B8*B2^4*B6^3 - 216*Polynomial.X*B2^4*B4^2*B6^3 - 162*Polynomial.X*B6*B2^2*B4^6 - 162*B6*Polynomial.X^3*B2^2*B4^5 - 54*B4*Polynomial.X^3*B2^4*B6^3 - 54*B6*Polynomial.X^2*B2^3*B4^5 - 15*B4*Polynomial.X^2*B2^5*B6^3 - 7*Polynomial.X*B6*B2^6*B8^2 - 3*Polynomial.X*B2^5*B4^3*B6^2 - 3*B6*B8*B2^5*B4^3 - 3*Polynomial.X^3*B2^5*B4^2*B6^2 - 2*Polynomial.X*B4*B2^7*B8^2 + 5*B4*B8*B2^6*B6^2 + 33*B8*Polynomial.X^2*B2^6*B6^2 + 72*B8*Polynomial.X^2*B2^4*B4^4 + 103*B4*Polynomial.X^2*B2^6*B8^2 + 108*B8*Polynomial.X^3*B2^5*B6^2 + 162*Polynomial.X*B8*B2^3*B4^5 + 162*Polynomial.X^2*B2^4*B4^3*B6^2 + 214*Polynomial.X*B2^5*B4^2*B8^2 + 216*B8*Polynomial.X^3*B2^3*B4^4 + 300*B4*Polynomial.X^3*B2^5*B8^2 + 351*Polynomial.X^2*B2^3*B4^2*B6^3 + 356*B4*B6*B2^5*B8^2 + 486*Polynomial.X^3*B2^3*B4^3*B6^2 + 540*Polynomial.X*B2^3*B4^4*B6^2 + 756*B6*B8*B2^3*B4^4 + 2187*B2*B6*Polynomial.X^2*B4^6 + 2511*Polynomial.X^3*B2^2*B4^2*B6^3 + 3519*B4*B8*B2^3*B6^3 + 7695*Polynomial.X*B2^2*B4^3*B6^3 + 8379*B8*Polynomial.X^2*B2^3*B6^3 + 17982*B4*Polynomial.X^2*B2^2*B6^4 + 18954*Polynomial.X*B2*B4^2*B6^4 + 24912*Polynomial.X^2*B2^2*B4^3*B8^2 + 26244*B8*Polynomial.X^3*B2^2*B6^3 + 27024*Polynomial.X*B6*B2^2*B8^3 + 27513*B8*B2^2*B4^3*B6^2 + 29160*Polynomial.X*B6*B8*B4^5 + 33534*B2*Polynomial.X^2*B4^3*B6^3 + 35964*Polynomial.X*B2*B4^4*B8^2 + 37908*B6*B8*Polynomial.X^3*B4^4 + 54432*B2*Polynomial.X^3*B4^3*B8^2 + 61236*B2*B4*Polynomial.X^3*B6^4 + 84888*B2*B6*B4^3*B8^2 + 132516*B4*B2^2*B6^2*B8^2 + 134136*B8*Polynomial.X^2*B4^3*B6^2 + 363888*B2*B6*Polynomial.X^2*B8^3 + 677376*Polynomial.X*B4*B6*B8^3 + 1183896*Polynomial.X*B8*B4^2*B6^3 + 1329696*B4*B8*Polynomial.X^3*B6^3 - 488592*Polynomial.X*B2*B4*B6^2*B8^2 - 340848*B2*B8*Polynomial.X^3*B4^2*B6^2 - 277992*Polynomial.X*B2*B8*B4^3*B6^2 - 129816*B2*B6*Polynomial.X^2*B4^2*B8^2 - 119367*B8*Polynomial.X^2*B2^2*B4^2*B6^2 - 2673*B2*B6*B8*Polynomial.X^2*B4^4 - 1644*Polynomial.X*B4*B6*B2^4*B8^2 - 1593*Polynomial.X*B8*B2^3*B4^2*B6^2 - 894*B6*B8*Polynomial.X^3*B2^4*B4^2 - 738*Polynomial.X*B6*B8*B2^4*B4^3 - 301*B6*B8*Polynomial.X^2*B2^5*B4^2 + 2*B4*B6*B8*Polynomial.X^2*B2^7 + 5*Polynomial.X*B6*B8*B2^6*B4^2 + 6*B4*B6*B8*Polynomial.X^3*B2^6 + 186*Polynomial.X*B4*B8*B2^5*B6^2 + 540*B4*B8*Polynomial.X^2*B2^4*B6^2 + 972*B4*B8*Polynomial.X^3*B2^3*B6^2 + 9540*B6*B8*Polynomial.X^2*B2^3*B4^3 + 22329*Polynomial.X*B6*B8*B2^2*B4^4 + 27216*B6*B8*Polynomial.X^3*B2^2*B4^3 + 35640*Polynomial.X*B4*B8*B2^2*B6^3 + 37872*B4*B6*Polynomial.X^2*B2^3*B8^2 + 101736*Polynomial.X*B6*B2^2*B4^2*B8^2 + 111456*B4*B6*Polynomial.X^3*B2^2*B8^2 + 445176*B2*B4*B8*Polynomial.X^2*B6^3) with hGc
  have hcert : Fc * W.Ψ₃ + Gc * W.preΨ₄ = Polynomial.C (W.Δ ^ 4) := by
    rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 +
        9 * W.b₂ * W.b₄ * W.b₆ from rfl, hFc, hGc]
    simp only [map_ofNat, Polynomial.C_neg, Polynomial.C_add,
      Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, ← hB2,
      ← hB4, ← hB6, ← hB8]
    linear_combination ((-4096*B4^10 + 153664*B8^5 - B2^5*B6^5 - 590490*B4*B6^6 - 297432*B6^4*B8^2 - 279936*B4^4*B6^4 - 235984*B4^2*B8^4 - 58975*B4^6*B8^2 - 55296*B4^7*B6^2 - 2187*B2^2*B6^6 - 408*B2^4*B8^4 + 16384*B8*B4^8 + 154252*B4^4*B8^3 - B2^4*B4^2*B6^4 - 577584*B4^3*B6^2*B8^2 - 121520*B2*B6*B8^4 - 78624*B2^2*B4^3*B6^4 - 21392*B2^2*B4^3*B8^3 - 16768*B2^2*B4^6*B6^2 - 2048*B8*B2^2*B4^7 - 384*B2^4*B4^4*B8^2 - 30*B4*B2^6*B8^3 - 3*B2^6*B6^2*B8^2 + 56*B8*B2^4*B6^4 + 114*B6*B2^5*B8^3 + 162*B4*B2^3*B6^5 + 1242*B2^4*B4^2*B8^3 + 1667*B2^3*B6^3*B8^2 + 6560*B2^3*B4^4*B6^3 + 8030*B2^2*B4^5*B8^2 + 13276*B2^2*B6^2*B8^3 + 14336*B2*B6*B4^8 + 23520*B4*B2^2*B8^4 + 83106*B2*B8*B6^5 + 131328*B2*B4^5*B6^3 + 216810*B8*B4^5*B6^2 + 347733*B2*B4^2*B6^5 + 635040*B4*B6^2*B8^3 + 905418*B8*B4^2*B6^4 - 284688*B2*B8*B4^3*B6^3 - 139968*B2*B4*B6^3*B8^2 - 70956*B4*B8*B2^2*B6^4 - 40960*B2*B6*B8*B4^6 - 10544*B6*B2^3*B4^3*B8^2 - 5184*B4*B6*B2^3*B8^3 - 3416*B2*B6*B4^2*B8^3 - 2912*B8*B2^4*B4^3*B6^2 - 2628*B4*B2^4*B6^2*B8^2 + 6*B4*B8*B2^5*B6^3 + 477*B6*B2^5*B4^2*B8^2 + 4864*B6*B8*B2^3*B4^5 + 5484*B8*B2^2*B4^4*B6^2 + 25252*B8*B2^3*B4^2*B6^3 + 72789*B2*B6*B4^4*B8^2 + 84711*B2^2*B4^2*B6^2*B8^2 : Polynomial K)) * hrelC
  have hev := congrArg (Polynomial.eval x₀) hcert
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C] at hev
  rw [h3, h4, mul_zero, mul_zero, add_zero] at hev
  exact hΔ (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0) |>.mp
    (by linear_combination -hev))

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

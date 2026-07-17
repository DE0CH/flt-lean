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
set_option maxHeartbeats 8000000 in
/-- **The `(3,4)` Bézout certificate** (PROVEN, sympy-extracted
Sylvester-cofactor column, `X`-collected form): the combination
`F ⬝ Ψ₃ + G ⬝ preΨ₄` equals the constant raw resultant, which is `Δ⁴`
by the `b`-invariant relation; so `Ψ₃` and `preΨ₄` cannot vanish
together when `Δ ≠ 0`. -/
theorem psi34_not_both_zero (hΔ : W.Δ ≠ 0) (x₀ : K)
    (h3 : (W.Ψ₃).eval x₀ = 0) (h4 : (W.preΨ₄).eval x₀ = 0) : False := by
  have hcert : (Polynomial.C (614656*W.b₈^5 + W.b₂^8*W.b₈^3 - 592704*W.b₄^2*W.b₈^4 - 400464*W.b₆^4*W.b₈^2 - 308367*W.b₄*W.b₆^6 - 20412*W.b₄^6*W.b₈^2 - 1632*W.b₂^4*W.b₈^4 + 7*W.b₂^5*W.b₆^5 + 1944*W.b₂^2*W.b₆^6 + 2187*W.b₄^7*W.b₆^2 + 6561*W.b₄^4*W.b₆^4 + 190512*W.b₄^4*W.b₈^3 - W.b₂^5*W.b₄^3*W.b₆^3 - 666360*W.b₄^3*W.b₆^2*W.b₈^2 - 639744*W.b₂*W.b₆*W.b₈^4 - 39944*W.b₂^2*W.b₄^3*W.b₈^3 - 7432*W.b₂^3*W.b₆^3*W.b₈^2 - 5346*W.b₂*W.b₄^5*W.b₆^3 - 1422*W.b₄*W.b₂^3*W.b₆^5 - 111*W.b₄*W.b₂^6*W.b₈^3 - 78*W.b₂^4*W.b₄^4*W.b₈^2 - 54*W.b₂^2*W.b₄^6*W.b₆^2 - 27*W.b₂^6*W.b₆^2*W.b₈^2 - 18*W.b₂^4*W.b₄^2*W.b₆^4 + 162*W.b₂^3*W.b₄^4*W.b₆^3 + 693*W.b₈*W.b₂^4*W.b₆^4 + 864*W.b₆*W.b₂^5*W.b₈^3 + 1107*W.b₂^2*W.b₄^3*W.b₆^4 + 3663*W.b₂^2*W.b₄^5*W.b₈^2 + 3760*W.b₂^4*W.b₄^2*W.b₈^3 + 45684*W.b₂*W.b₄^2*W.b₆^5 + 46899*W.b₈*W.b₄^5*W.b₆^2 + 88816*W.b₄*W.b₂^2*W.b₈^4 + 179888*W.b₂^2*W.b₆^2*W.b₈^3 + 188568*W.b₂*W.b₈*W.b₆^5 + 983664*W.b₈*W.b₄^2*W.b₆^4 + 1553328*W.b₄*W.b₆^2*W.b₈^3 - 756648*W.b₂*W.b₄*W.b₆^3*W.b₈^2 - 211410*W.b₂*W.b₈*W.b₄^3*W.b₆^3 - 43432*W.b₄*W.b₆*W.b₂^3*W.b₈^3 - 26406*W.b₄*W.b₈*W.b₂^2*W.b₆^4 - 14034*W.b₆*W.b₂^3*W.b₄^3*W.b₈^2 - 5103*W.b₂*W.b₆*W.b₈*W.b₄^6 - 2290*W.b₄*W.b₂^4*W.b₆^2*W.b₈^2 - 456*W.b₈*W.b₂^4*W.b₄^3*W.b₆^2 - 3*W.b₄*W.b₆*W.b₂^7*W.b₈^2 + 3*W.b₈*W.b₂^6*W.b₄^2*W.b₆^2 + 25*W.b₄*W.b₈*W.b₂^5*W.b₆^3 + 126*W.b₆*W.b₈*W.b₂^3*W.b₄^5 + 424*W.b₆*W.b₂^5*W.b₄^2*W.b₈^2 + 2511*W.b₈*W.b₂^3*W.b₄^2*W.b₆^3 + 13410*W.b₈*W.b₂^2*W.b₄^4*W.b₆^2 + 48600*W.b₂*W.b₆*W.b₄^4*W.b₈^2 + 103824*W.b₂*W.b₆*W.b₄^2*W.b₈^3 + 200916*W.b₂^2*W.b₄^2*W.b₆^2*W.b₈^2 : K) * Polynomial.X ^ 0 +
      Polynomial.C (-1843968*W.b₆*W.b₈^4 - 45927*W.b₂*W.b₆^6 - 5264*W.b₂^3*W.b₈^4 - 165*W.b₂^4*W.b₆^5 + 9*W.b₂^7*W.b₈^3 + 10935*W.b₄^5*W.b₆^3 + 148716*W.b₄^2*W.b₆^5 + 1259712*W.b₈*W.b₆^5 - 3251664*W.b₄*W.b₆^3*W.b₈^2 - 375192*W.b₈*W.b₄^3*W.b₆^3 - 157248*W.b₂*W.b₄^3*W.b₈^3 - 71352*W.b₂^2*W.b₆^3*W.b₈^2 - 29160*W.b₆*W.b₈*W.b₄^6 - 28188*W.b₂*W.b₄^3*W.b₆^4 - 9072*W.b₆*W.b₄^4*W.b₈^2 - 880*W.b₄*W.b₂^5*W.b₈^3 - 705*W.b₂^3*W.b₄^4*W.b₈^2 - 274*W.b₂^5*W.b₆^2*W.b₈^2 - 270*W.b₂^2*W.b₄^4*W.b₆^3 - 5*W.b₄*W.b₂^5*W.b₆^4 + 2*W.b₂^5*W.b₄^3*W.b₈^2 + 7*W.b₈*W.b₂^6*W.b₆^3 + 846*W.b₂^3*W.b₄^2*W.b₆^4 + 5720*W.b₆*W.b₂^4*W.b₈^3 + 5994*W.b₄*W.b₂^2*W.b₆^5 + 6114*W.b₈*W.b₂^3*W.b₆^4 + 25048*W.b₂^3*W.b₄^2*W.b₈^3 + 25272*W.b₂*W.b₄^5*W.b₈^2 + 244608*W.b₂*W.b₄*W.b₈^4 + 903168*W.b₆*W.b₄^2*W.b₈^3 + 1082928*W.b₂*W.b₆^2*W.b₈^3 - 285184*W.b₄*W.b₆*W.b₂^2*W.b₈^3 - 170424*W.b₂*W.b₄*W.b₈*W.b₆^4 - 88896*W.b₆*W.b₂^2*W.b₄^3*W.b₈^2 - 4872*W.b₄*W.b₂^3*W.b₆^2*W.b₈^2 - 2112*W.b₈*W.b₂^3*W.b₄^3*W.b₆^2 - 258*W.b₄*W.b₈*W.b₂^4*W.b₆^3 - 25*W.b₄*W.b₆*W.b₂^6*W.b₈^2 + 12*W.b₈*W.b₂^5*W.b₄^2*W.b₆^2 + 702*W.b₈*W.b₂^2*W.b₄^2*W.b₆^3 + 720*W.b₆*W.b₈*W.b₂^2*W.b₄^5 + 3098*W.b₆*W.b₂^4*W.b₄^2*W.b₈^2 + 71523*W.b₂*W.b₈*W.b₄^4*W.b₆^2 + 959256*W.b₂*W.b₄^2*W.b₆^2*W.b₈^2 : K) * Polynomial.X ^ 1 +
      Polynomial.C (1614006*W.b₆^6 + W.b₂^6*W.b₆^4 - 2558304*W.b₆^2*W.b₈^3 - 317520*W.b₄^3*W.b₈^3 - 28431*W.b₄^3*W.b₆^4 - 10935*W.b₈*W.b₄^7 - 10935*W.b₄^6*W.b₆^2 - 5600*W.b₂^2*W.b₈^4 + 10*W.b₂^6*W.b₈^3 + 6075*W.b₂^3*W.b₆^5 + 102060*W.b₄^5*W.b₈^2 + 329280*W.b₄*W.b₈^4 - 4639356*W.b₄*W.b₈*W.b₆^4 - 356238*W.b₈*W.b₄^4*W.b₆^2 - 270459*W.b₂*W.b₄*W.b₆^5 - 75816*W.b₈*W.b₂^2*W.b₆^4 - 11694*W.b₂^2*W.b₄^4*W.b₈^2 - 2992*W.b₆*W.b₂^3*W.b₈^3 - 1084*W.b₄*W.b₂^4*W.b₈^3 - 756*W.b₂^3*W.b₄^3*W.b₆^3 - 316*W.b₈*W.b₂^5*W.b₆^3 - 84*W.b₄*W.b₂^4*W.b₆^4 - 4*W.b₂^6*W.b₄^2*W.b₈^2 + 5*W.b₂^5*W.b₄^2*W.b₆^3 + 10*W.b₆*W.b₂^7*W.b₈^2 + 189*W.b₂^2*W.b₄^2*W.b₆^4 + 270*W.b₈*W.b₂^2*W.b₄^6 + 270*W.b₂^2*W.b₄^5*W.b₆^2 + 385*W.b₂^4*W.b₄^3*W.b₈^2 + 7260*W.b₂^4*W.b₆^2*W.b₈^2 + 24543*W.b₂*W.b₄^4*W.b₆^3 + 35568*W.b₂^2*W.b₄^2*W.b₈^3 + 1469664*W.b₂*W.b₆^3*W.b₈^2 + 2036448*W.b₄^2*W.b₆^2*W.b₈^2 - 390492*W.b₄*W.b₂^2*W.b₆^2*W.b₈^2 - 220104*W.b₂*W.b₆*W.b₄^3*W.b₈^2 - 87183*W.b₈*W.b₂^2*W.b₄^3*W.b₆^2 - 5541*W.b₄*W.b₈*W.b₂^3*W.b₆^3 - 1572*W.b₆*W.b₈*W.b₂^3*W.b₄^4 - 1047*W.b₄*W.b₆*W.b₂^5*W.b₈^2 - 17*W.b₄*W.b₈*W.b₂^6*W.b₆^2 + 5*W.b₆*W.b₈*W.b₂^5*W.b₄^3 + 2840*W.b₈*W.b₂^4*W.b₄^2*W.b₆^2 + 31940*W.b₆*W.b₂^3*W.b₄^2*W.b₈^2 + 57591*W.b₂*W.b₆*W.b₈*W.b₄^5 + 127344*W.b₂*W.b₄*W.b₆*W.b₈^3 + 1193076*W.b₂*W.b₈*W.b₄^2*W.b₆^3 : K) * Polynomial.X ^ 2 +
      Polynomial.C (-91854*W.b₄^4*W.b₆^3 - 38880*W.b₆^3*W.b₈^2 - 10935*W.b₆*W.b₄^7 - 6075*W.b₂^2*W.b₆^5 - 92*W.b₂^5*W.b₈^3 - 22*W.b₂^5*W.b₆^4 + 53312*W.b₂*W.b₈^4 + 734832*W.b₄*W.b₆^5 + W.b₈*W.b₂^7*W.b₆^2 - W.b₄*W.b₂^6*W.b₆^3 - 2118960*W.b₈*W.b₄^2*W.b₆^3 - 1213632*W.b₄*W.b₆*W.b₈^3 - 71604*W.b₂*W.b₄^4*W.b₈^2 - 64395*W.b₂*W.b₄^2*W.b₆^4 - 57348*W.b₆*W.b₈*W.b₄^5 - 30224*W.b₆*W.b₂^2*W.b₈^3 - 9423*W.b₂^2*W.b₄^3*W.b₆^3 - 972*W.b₂*W.b₈*W.b₆^4 - 864*W.b₂^3*W.b₄^4*W.b₆^2 - 415*W.b₂^5*W.b₄^2*W.b₈^2 - 306*W.b₈*W.b₂^3*W.b₄^5 + 4*W.b₄*W.b₂^7*W.b₈^2 + 5*W.b₂^5*W.b₄^3*W.b₆^2 + 7*W.b₆*W.b₂^6*W.b₈^2 + 223*W.b₈*W.b₂^4*W.b₆^3 + 252*W.b₂^4*W.b₄^2*W.b₆^3 + 270*W.b₆*W.b₂^2*W.b₄^6 + 1092*W.b₂^3*W.b₆^2*W.b₈^2 + 2400*W.b₄*W.b₂^3*W.b₈^3 + 3357*W.b₄*W.b₂^3*W.b₆^4 + 12176*W.b₂^3*W.b₄^3*W.b₈^2 + 12393*W.b₂*W.b₈*W.b₄^6 + 28917*W.b₂*W.b₄^5*W.b₆^2 + 85680*W.b₂*W.b₄^2*W.b₈^3 + 674352*W.b₆*W.b₄^3*W.b₈^2 - 180648*W.b₆*W.b₂^2*W.b₄^2*W.b₈^2 - 50220*W.b₄*W.b₈*W.b₂^2*W.b₆^3 - 40401*W.b₆*W.b₈*W.b₂^2*W.b₄^4 - 256*W.b₄*W.b₈*W.b₂^5*W.b₆^2 - 9*W.b₆*W.b₈*W.b₂^6*W.b₄^2 + 729*W.b₈*W.b₂^3*W.b₄^2*W.b₆^2 + 1334*W.b₆*W.b₈*W.b₂^4*W.b₄^3 + 3176*W.b₄*W.b₆*W.b₂^4*W.b₈^2 + 511272*W.b₂*W.b₈*W.b₄^3*W.b₆^2 + 808272*W.b₂*W.b₄*W.b₆^2*W.b₈^2 : K) * Polynomial.X ^ 3 +
      Polynomial.C (131712*W.b₈^4 + W.b₂^8*W.b₈^2 - 127008*W.b₄^2*W.b₈^3 - 52488*W.b₈*W.b₆^4 - 4374*W.b₈*W.b₄^6 - 808*W.b₂^4*W.b₈^3 + 519*W.b₂^4*W.b₆^4 + 4374*W.b₄^5*W.b₆^2 + 40824*W.b₄^4*W.b₈^2 + 56862*W.b₄^2*W.b₆^4 + 144342*W.b₂*W.b₆^5 + W.b₂^6*W.b₄^2*W.b₆^2 - 327264*W.b₂*W.b₆*W.b₈^3 - 89424*W.b₈*W.b₄^3*W.b₆^2 - 28188*W.b₂*W.b₄^3*W.b₆^3 - 22656*W.b₂^2*W.b₄^3*W.b₈^2 - 18792*W.b₄*W.b₂^2*W.b₆^4 - 8502*W.b₈*W.b₂^3*W.b₆^3 - 2187*W.b₂*W.b₆*W.b₄^6 - 513*W.b₂^3*W.b₄^2*W.b₆^3 - 162*W.b₂^4*W.b₄^3*W.b₆^2 - 102*W.b₄*W.b₂^6*W.b₈^2 - 72*W.b₈*W.b₂^4*W.b₄^4 - 34*W.b₈*W.b₂^6*W.b₆^2 + 16*W.b₄*W.b₂^5*W.b₆^3 + 54*W.b₆*W.b₂^3*W.b₄^5 + 734*W.b₆*W.b₂^5*W.b₈^2 + 3024*W.b₈*W.b₂^2*W.b₄^5 + 3062*W.b₂^4*W.b₄^2*W.b₈^2 + 5238*W.b₂^2*W.b₄^4*W.b₆^2 + 41216*W.b₄*W.b₂^2*W.b₈^3 + 149832*W.b₂^2*W.b₆^2*W.b₈^2 + 235872*W.b₄*W.b₆^2*W.b₈^2 - 444528*W.b₂*W.b₄*W.b₈*W.b₆^3 - 37632*W.b₄*W.b₆*W.b₂^3*W.b₈^2 - 9384*W.b₆*W.b₈*W.b₂^3*W.b₄^3 - 2430*W.b₂*W.b₆*W.b₈*W.b₄^4 - 468*W.b₄*W.b₈*W.b₂^4*W.b₆^2 - 2*W.b₄*W.b₆*W.b₈*W.b₂^7 + 300*W.b₆*W.b₈*W.b₂^5*W.b₄^2 + 117450*W.b₈*W.b₂^2*W.b₄^2*W.b₆^2 + 133920*W.b₂*W.b₆*W.b₄^2*W.b₈^2 : K) * Polynomial.X ^ 4 +
      Polynomial.C (314928*W.b₆^5 - 508032*W.b₆*W.b₈^3 - 34992*W.b₄^3*W.b₆^3 - 4374*W.b₆*W.b₄^6 - 1152*W.b₂^3*W.b₈^3 + 2*W.b₂^7*W.b₈^2 + 1134*W.b₂^3*W.b₆^4 - 886464*W.b₄*W.b₈*W.b₆^3 - 40824*W.b₂*W.b₄*W.b₆^4 - 36288*W.b₂*W.b₄^3*W.b₈^2 - 25272*W.b₆*W.b₈*W.b₄^4 - 17496*W.b₈*W.b₂^2*W.b₆^3 - 1674*W.b₂^2*W.b₄^2*W.b₆^3 - 324*W.b₂^3*W.b₄^3*W.b₆^2 - 200*W.b₄*W.b₂^5*W.b₈^2 - 144*W.b₈*W.b₂^3*W.b₄^4 - 72*W.b₈*W.b₂^5*W.b₆^2 + 2*W.b₂^5*W.b₄^2*W.b₆^2 + 36*W.b₄*W.b₂^4*W.b₆^3 + 108*W.b₆*W.b₂^2*W.b₄^5 + 1440*W.b₆*W.b₂^4*W.b₈^2 + 5792*W.b₂^3*W.b₄^2*W.b₈^2 + 5832*W.b₂*W.b₈*W.b₄^5 + 10692*W.b₂*W.b₄^4*W.b₆^2 + 56448*W.b₂*W.b₄*W.b₈^3 + 284256*W.b₆*W.b₄^2*W.b₈^2 + 295488*W.b₂*W.b₆^2*W.b₈^2 - 74304*W.b₄*W.b₆*W.b₂^2*W.b₈^2 - 18144*W.b₆*W.b₈*W.b₂^2*W.b₄^3 - 648*W.b₄*W.b₈*W.b₂^3*W.b₆^2 - 4*W.b₄*W.b₆*W.b₈*W.b₂^6 + 596*W.b₆*W.b₈*W.b₂^4*W.b₄^2 + 227232*W.b₂*W.b₈*W.b₄^2*W.b₆^2 : K) * Polynomial.X ^ 5) * W.Ψ₃ +
      (Polynomial.C (-531441*W.b₆^6 - W.b₂^6*W.b₆^4 - 197568*W.b₄*W.b₈^4 - 61236*W.b₄^5*W.b₈^2 - 39366*W.b₄^3*W.b₆^4 - 2187*W.b₂^3*W.b₆^5 - 9*W.b₂^6*W.b₈^3 + 5264*W.b₂^2*W.b₈^4 + 6561*W.b₈*W.b₄^7 + 190512*W.b₄^3*W.b₈^3 + 789264*W.b₆^2*W.b₈^3 - 818424*W.b₄^2*W.b₆^2*W.b₈^2 - 441288*W.b₂*W.b₆^3*W.b₈^2 - 22104*W.b₂^2*W.b₄^2*W.b₈^3 - 4374*W.b₂^2*W.b₄^2*W.b₆^4 - 2238*W.b₂^4*W.b₆^2*W.b₈^2 - 824*W.b₆*W.b₂^3*W.b₈^3 - 216*W.b₂^4*W.b₄^3*W.b₈^2 - 162*W.b₈*W.b₂^2*W.b₄^6 - 54*W.b₂^3*W.b₄^3*W.b₆^3 - 3*W.b₆*W.b₂^7*W.b₈^2 + 2*W.b₂^6*W.b₄^2*W.b₈^2 + 67*W.b₈*W.b₂^5*W.b₆^3 + 162*W.b₄*W.b₂^4*W.b₆^4 + 800*W.b₄*W.b₂^4*W.b₈^3 + 2187*W.b₂*W.b₄^4*W.b₆^3 + 7065*W.b₂^2*W.b₄^4*W.b₈^2 + 15066*W.b₈*W.b₂^2*W.b₆^4 + 118098*W.b₂*W.b₄*W.b₆^5 + 181521*W.b₈*W.b₄^4*W.b₆^2 + 1522152*W.b₄*W.b₈*W.b₆^4 - 404838*W.b₂*W.b₈*W.b₄^2*W.b₆^3 - 26973*W.b₂*W.b₆*W.b₈*W.b₄^5 - 11934*W.b₆*W.b₂^3*W.b₄^2*W.b₈^2 - 3024*W.b₂*W.b₄*W.b₆*W.b₈^3 - 900*W.b₈*W.b₂^4*W.b₄^2*W.b₆^2 - 3*W.b₆*W.b₈*W.b₂^5*W.b₄^3 + 5*W.b₄*W.b₈*W.b₂^6*W.b₆^2 + 356*W.b₄*W.b₆*W.b₂^5*W.b₈^2 + 756*W.b₆*W.b₈*W.b₂^3*W.b₄^4 + 3519*W.b₄*W.b₈*W.b₂^3*W.b₆^3 + 27513*W.b₈*W.b₂^2*W.b₄^3*W.b₆^2 + 84888*W.b₂*W.b₆*W.b₄^3*W.b₈^2 + 132516*W.b₄*W.b₂^2*W.b₆^2*W.b₈^2 : K) * Polynomial.X ^ 0 +
      Polynomial.C (-393660*W.b₄*W.b₆^5 - 47040*W.b₂*W.b₈^4 + 21*W.b₂^5*W.b₆^4 + 80*W.b₂^5*W.b₈^3 + 5832*W.b₂^2*W.b₆^5 + 6561*W.b₆*W.b₄^7 + 58320*W.b₆^3*W.b₈^2 + 59049*W.b₄^4*W.b₆^3 + W.b₄*W.b₂^6*W.b₆^3 - W.b₈*W.b₂^7*W.b₆^2 - 371952*W.b₆*W.b₄^3*W.b₈^2 - 33264*W.b₂*W.b₄^2*W.b₈^3 - 18225*W.b₂*W.b₄^5*W.b₆^2 - 11664*W.b₂*W.b₈*W.b₆^4 - 6561*W.b₂*W.b₈*W.b₄^6 - 6360*W.b₂^3*W.b₄^3*W.b₈^2 - 2944*W.b₄*W.b₂^3*W.b₈^3 - 2079*W.b₄*W.b₂^3*W.b₆^4 - 1116*W.b₂^3*W.b₆^2*W.b₈^2 - 273*W.b₈*W.b₂^4*W.b₆^3 - 216*W.b₂^4*W.b₄^2*W.b₆^3 - 162*W.b₆*W.b₂^2*W.b₄^6 - 7*W.b₆*W.b₂^6*W.b₈^2 - 3*W.b₂^5*W.b₄^3*W.b₆^2 - 2*W.b₄*W.b₂^7*W.b₈^2 + 162*W.b₈*W.b₂^3*W.b₄^5 + 214*W.b₂^5*W.b₄^2*W.b₈^2 + 540*W.b₂^3*W.b₄^4*W.b₆^2 + 7695*W.b₂^2*W.b₄^3*W.b₆^3 + 18954*W.b₂*W.b₄^2*W.b₆^4 + 27024*W.b₆*W.b₂^2*W.b₈^3 + 29160*W.b₆*W.b₈*W.b₄^5 + 35964*W.b₂*W.b₄^4*W.b₈^2 + 677376*W.b₄*W.b₆*W.b₈^3 + 1183896*W.b₈*W.b₄^2*W.b₆^3 - 488592*W.b₂*W.b₄*W.b₆^2*W.b₈^2 - 277992*W.b₂*W.b₈*W.b₄^3*W.b₆^2 - 1644*W.b₄*W.b₆*W.b₂^4*W.b₈^2 - 1593*W.b₈*W.b₂^3*W.b₄^2*W.b₆^2 - 738*W.b₆*W.b₈*W.b₂^4*W.b₄^3 + 5*W.b₆*W.b₈*W.b₂^6*W.b₄^2 + 186*W.b₄*W.b₈*W.b₂^5*W.b₆^2 + 22329*W.b₆*W.b₈*W.b₂^2*W.b₄^4 + 35640*W.b₄*W.b₈*W.b₂^2*W.b₆^3 + 101736*W.b₆*W.b₂^2*W.b₄^2*W.b₈^2 : K) * Polynomial.X ^ 1 +
      Polynomial.C (-197568*W.b₈^4 - W.b₂^8*W.b₈^2 - 137781*W.b₂*W.b₆^5 - 85293*W.b₄^2*W.b₆^4 - 61236*W.b₄^4*W.b₈^2 - 6561*W.b₄^5*W.b₆^2 - 495*W.b₂^4*W.b₆^4 + 924*W.b₂^4*W.b₈^3 + 6561*W.b₈*W.b₄^6 + 78732*W.b₈*W.b₆^4 + 190512*W.b₄^2*W.b₈^3 - W.b₂^6*W.b₄^2*W.b₆^2 - 353808*W.b₄*W.b₆^2*W.b₈^2 - 150876*W.b₂^2*W.b₆^2*W.b₈^2 - 47712*W.b₄*W.b₂^2*W.b₈^3 - 5184*W.b₂^2*W.b₄^4*W.b₆^2 - 3145*W.b₂^4*W.b₄^2*W.b₈^2 - 3078*W.b₈*W.b₂^2*W.b₄^5 - 741*W.b₆*W.b₂^5*W.b₈^2 - 54*W.b₆*W.b₂^3*W.b₄^5 - 15*W.b₄*W.b₂^5*W.b₆^3 + 33*W.b₈*W.b₂^6*W.b₆^2 + 72*W.b₈*W.b₂^4*W.b₄^4 + 103*W.b₄*W.b₂^6*W.b₈^2 + 162*W.b₂^4*W.b₄^3*W.b₆^2 + 351*W.b₂^3*W.b₄^2*W.b₆^3 + 2187*W.b₂*W.b₆*W.b₄^6 + 8379*W.b₈*W.b₂^3*W.b₆^3 + 17982*W.b₄*W.b₂^2*W.b₆^4 + 24912*W.b₂^2*W.b₄^3*W.b₈^2 + 33534*W.b₂*W.b₄^3*W.b₆^3 + 134136*W.b₈*W.b₄^3*W.b₆^2 + 363888*W.b₂*W.b₆*W.b₈^3 - 129816*W.b₂*W.b₆*W.b₄^2*W.b₈^2 - 119367*W.b₈*W.b₂^2*W.b₄^2*W.b₆^2 - 2673*W.b₂*W.b₆*W.b₈*W.b₄^4 - 301*W.b₆*W.b₈*W.b₂^5*W.b₄^2 + 2*W.b₄*W.b₆*W.b₈*W.b₂^7 + 540*W.b₄*W.b₈*W.b₂^4*W.b₆^2 + 9540*W.b₆*W.b₈*W.b₂^3*W.b₄^3 + 37872*W.b₄*W.b₆*W.b₂^3*W.b₈^2 + 445176*W.b₂*W.b₄*W.b₈*W.b₆^3 : K) * Polynomial.X ^ 2 +
      Polynomial.C (-472392*W.b₆^5 - 1701*W.b₂^3*W.b₆^4 - 3*W.b₂^7*W.b₈^2 + 1728*W.b₂^3*W.b₈^3 + 6561*W.b₆*W.b₄^6 + 52488*W.b₄^3*W.b₆^3 + 762048*W.b₆*W.b₈^3 - 443232*W.b₂*W.b₆^2*W.b₈^2 - 426384*W.b₆*W.b₄^2*W.b₈^2 - 84672*W.b₂*W.b₄*W.b₈^3 - 16038*W.b₂*W.b₄^4*W.b₆^2 - 8748*W.b₂*W.b₈*W.b₄^5 - 8688*W.b₂^3*W.b₄^2*W.b₈^2 - 2160*W.b₆*W.b₂^4*W.b₈^2 - 162*W.b₆*W.b₂^2*W.b₄^5 - 54*W.b₄*W.b₂^4*W.b₆^3 - 3*W.b₂^5*W.b₄^2*W.b₆^2 + 108*W.b₈*W.b₂^5*W.b₆^2 + 216*W.b₈*W.b₂^3*W.b₄^4 + 300*W.b₄*W.b₂^5*W.b₈^2 + 486*W.b₂^3*W.b₄^3*W.b₆^2 + 2511*W.b₂^2*W.b₄^2*W.b₆^3 + 26244*W.b₈*W.b₂^2*W.b₆^3 + 37908*W.b₆*W.b₈*W.b₄^4 + 54432*W.b₂*W.b₄^3*W.b₈^2 + 61236*W.b₂*W.b₄*W.b₆^4 + 1329696*W.b₄*W.b₈*W.b₆^3 - 340848*W.b₂*W.b₈*W.b₄^2*W.b₆^2 - 894*W.b₆*W.b₈*W.b₂^4*W.b₄^2 + 6*W.b₄*W.b₆*W.b₈*W.b₂^6 + 972*W.b₄*W.b₈*W.b₂^3*W.b₆^2 + 27216*W.b₆*W.b₈*W.b₂^2*W.b₄^3 + 111456*W.b₄*W.b₆*W.b₂^2*W.b₈^2 : K) * Polynomial.X ^ 3) * W.preΨ₄ = Polynomial.C (531441*W.b₆^8 + 614656*W.b₈^6 + W.b₂^6*W.b₆^6 + W.b₂^8*W.b₈^4 - 1189728*W.b₆^4*W.b₈^3 - 790272*W.b₄^2*W.b₈^5 - 81648*W.b₄^6*W.b₈^3 - 1632*W.b₂^4*W.b₈^5 + 2187*W.b₂^3*W.b₆^7 + 6561*W.b₄^8*W.b₈^2 + 39366*W.b₄^3*W.b₆^6 + 381024*W.b₄^4*W.b₈^4 - 2361960*W.b₄*W.b₈*W.b₆^6 - 1675296*W.b₄^3*W.b₆^2*W.b₈^3 - 639744*W.b₂*W.b₆*W.b₈^5 - 214326*W.b₈*W.b₄^4*W.b₆^4 - 118098*W.b₂*W.b₄*W.b₆^7 - 62048*W.b₂^2*W.b₄^3*W.b₈^4 - 13122*W.b₈*W.b₂^2*W.b₆^6 - 6608*W.b₂^3*W.b₆^3*W.b₈^3 - 4374*W.b₈*W.b₄^7*W.b₆^2 - 2187*W.b₂*W.b₄^4*W.b₆^5 - 294*W.b₂^4*W.b₄^4*W.b₈^3 - 162*W.b₄*W.b₂^4*W.b₆^6 - 162*W.b₂^2*W.b₄^7*W.b₈^2 - 120*W.b₄*W.b₂^6*W.b₈^4 - 60*W.b₈*W.b₂^5*W.b₆^5 - 18*W.b₂^6*W.b₆^2*W.b₈^3 + 2*W.b₂^6*W.b₄^3*W.b₈^3 + 3*W.b₂^7*W.b₆^3*W.b₈^2 + 54*W.b₂^3*W.b₄^3*W.b₆^5 + 864*W.b₆*W.b₂^5*W.b₈^4 + 2931*W.b₂^4*W.b₆^4*W.b₈^2 + 4374*W.b₂^2*W.b₄^2*W.b₆^6 + 4560*W.b₂^4*W.b₄^2*W.b₈^4 + 10728*W.b₂^2*W.b₄^5*W.b₈^3 + 94080*W.b₄*W.b₂^2*W.b₈^5 + 174624*W.b₂^2*W.b₆^2*W.b₈^4 + 289656*W.b₄^5*W.b₆^2*W.b₈^2 + 629856*W.b₂*W.b₆^5*W.b₈^2 + 2540160*W.b₄*W.b₆^2*W.b₈^4 + 3324240*W.b₄^2*W.b₆^4*W.b₈^2 - 1194912*W.b₂*W.b₄*W.b₆^3*W.b₈^3 - 701136*W.b₂*W.b₄^3*W.b₆^3*W.b₈^2 - 143856*W.b₄*W.b₂^2*W.b₆^4*W.b₈^2 - 44256*W.b₄*W.b₆*W.b₂^3*W.b₈^4 - 32076*W.b₂*W.b₆*W.b₄^6*W.b₈^2 - 30780*W.b₈*W.b₂^2*W.b₄^3*W.b₆^4 - 25968*W.b₆*W.b₂^3*W.b₄^3*W.b₈^3 - 7128*W.b₄*W.b₈*W.b₂^3*W.b₆^5 - 5328*W.b₄*W.b₂^4*W.b₆^2*W.b₈^3 - 1140*W.b₂^4*W.b₄^3*W.b₆^2*W.b₈^2 - 648*W.b₈*W.b₂^3*W.b₄^4*W.b₆^3 - 264*W.b₄*W.b₂^5*W.b₆^3*W.b₈^2 - 6*W.b₄*W.b₆*W.b₂^7*W.b₈^3 - 6*W.b₄*W.b₈*W.b₂^6*W.b₆^4 - 3*W.b₆*W.b₂^5*W.b₄^4*W.b₈^2 + 2*W.b₈*W.b₂^5*W.b₄^3*W.b₆^3 + 6*W.b₂^6*W.b₄^2*W.b₆^2*W.b₈^2 + 108*W.b₈*W.b₂^2*W.b₄^6*W.b₆^2 + 780*W.b₆*W.b₂^5*W.b₄^2*W.b₈^3 + 882*W.b₆*W.b₂^3*W.b₄^5*W.b₈^2 + 1044*W.b₈*W.b₂^4*W.b₄^2*W.b₆^4 + 17964*W.b₂^3*W.b₄^2*W.b₆^3*W.b₈^2 + 23814*W.b₂*W.b₈*W.b₄^5*W.b₆^3 + 33858*W.b₂^2*W.b₄^4*W.b₆^2*W.b₈^2 + 100800*W.b₂*W.b₆*W.b₄^2*W.b₈^4 + 133488*W.b₂*W.b₆*W.b₄^4*W.b₈^3 + 355536*W.b₂^2*W.b₄^2*W.b₆^2*W.b₈^3 + 568620*W.b₂*W.b₈*W.b₄^2*W.b₆^5 : K) := by
    rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄]
    simp only [map_ofNat, Polynomial.C_neg, Polynomial.C_add,
      Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow]
    ring
  have hDval : (531441*W.b₆^8 + 614656*W.b₈^6 + W.b₂^6*W.b₆^6 + W.b₂^8*W.b₈^4 - 1189728*W.b₆^4*W.b₈^3 - 790272*W.b₄^2*W.b₈^5 - 81648*W.b₄^6*W.b₈^3 - 1632*W.b₂^4*W.b₈^5 + 2187*W.b₂^3*W.b₆^7 + 6561*W.b₄^8*W.b₈^2 + 39366*W.b₄^3*W.b₆^6 + 381024*W.b₄^4*W.b₈^4 - 2361960*W.b₄*W.b₈*W.b₆^6 - 1675296*W.b₄^3*W.b₆^2*W.b₈^3 - 639744*W.b₂*W.b₆*W.b₈^5 - 214326*W.b₈*W.b₄^4*W.b₆^4 - 118098*W.b₂*W.b₄*W.b₆^7 - 62048*W.b₂^2*W.b₄^3*W.b₈^4 - 13122*W.b₈*W.b₂^2*W.b₆^6 - 6608*W.b₂^3*W.b₆^3*W.b₈^3 - 4374*W.b₈*W.b₄^7*W.b₆^2 - 2187*W.b₂*W.b₄^4*W.b₆^5 - 294*W.b₂^4*W.b₄^4*W.b₈^3 - 162*W.b₄*W.b₂^4*W.b₆^6 - 162*W.b₂^2*W.b₄^7*W.b₈^2 - 120*W.b₄*W.b₂^6*W.b₈^4 - 60*W.b₈*W.b₂^5*W.b₆^5 - 18*W.b₂^6*W.b₆^2*W.b₈^3 + 2*W.b₂^6*W.b₄^3*W.b₈^3 + 3*W.b₂^7*W.b₆^3*W.b₈^2 + 54*W.b₂^3*W.b₄^3*W.b₆^5 + 864*W.b₆*W.b₂^5*W.b₈^4 + 2931*W.b₂^4*W.b₆^4*W.b₈^2 + 4374*W.b₂^2*W.b₄^2*W.b₆^6 + 4560*W.b₂^4*W.b₄^2*W.b₈^4 + 10728*W.b₂^2*W.b₄^5*W.b₈^3 + 94080*W.b₄*W.b₂^2*W.b₈^5 + 174624*W.b₂^2*W.b₆^2*W.b₈^4 + 289656*W.b₄^5*W.b₆^2*W.b₈^2 + 629856*W.b₂*W.b₆^5*W.b₈^2 + 2540160*W.b₄*W.b₆^2*W.b₈^4 + 3324240*W.b₄^2*W.b₆^4*W.b₈^2 - 1194912*W.b₂*W.b₄*W.b₆^3*W.b₈^3 - 701136*W.b₂*W.b₄^3*W.b₆^3*W.b₈^2 - 143856*W.b₄*W.b₂^2*W.b₆^4*W.b₈^2 - 44256*W.b₄*W.b₆*W.b₂^3*W.b₈^4 - 32076*W.b₂*W.b₆*W.b₄^6*W.b₈^2 - 30780*W.b₈*W.b₂^2*W.b₄^3*W.b₆^4 - 25968*W.b₆*W.b₂^3*W.b₄^3*W.b₈^3 - 7128*W.b₄*W.b₈*W.b₂^3*W.b₆^5 - 5328*W.b₄*W.b₂^4*W.b₆^2*W.b₈^3 - 1140*W.b₂^4*W.b₄^3*W.b₆^2*W.b₈^2 - 648*W.b₈*W.b₂^3*W.b₄^4*W.b₆^3 - 264*W.b₄*W.b₂^5*W.b₆^3*W.b₈^2 - 6*W.b₄*W.b₆*W.b₂^7*W.b₈^3 - 6*W.b₄*W.b₈*W.b₂^6*W.b₆^4 - 3*W.b₆*W.b₂^5*W.b₄^4*W.b₈^2 + 2*W.b₈*W.b₂^5*W.b₄^3*W.b₆^3 + 6*W.b₂^6*W.b₄^2*W.b₆^2*W.b₈^2 + 108*W.b₈*W.b₂^2*W.b₄^6*W.b₆^2 + 780*W.b₆*W.b₂^5*W.b₄^2*W.b₈^3 + 882*W.b₆*W.b₂^3*W.b₄^5*W.b₈^2 + 1044*W.b₈*W.b₂^4*W.b₄^2*W.b₆^4 + 17964*W.b₂^3*W.b₄^2*W.b₆^3*W.b₈^2 + 23814*W.b₂*W.b₈*W.b₄^5*W.b₆^3 + 33858*W.b₂^2*W.b₄^4*W.b₆^2*W.b₈^2 + 100800*W.b₂*W.b₆*W.b₄^2*W.b₈^4 + 133488*W.b₂*W.b₆*W.b₄^4*W.b₈^3 + 355536*W.b₂^2*W.b₄^2*W.b₆^2*W.b₈^3 + 568620*W.b₂*W.b₈*W.b₄^2*W.b₆^5 : K) = W.Δ ^ 4 := by
    have hrel := W.b_relation
    rw [show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 +
      9 * W.b₂ * W.b₄ * W.b₆ from rfl]
    linear_combination (-4096*W.b₄^10 + 153664*W.b₈^5 - W.b₂^5*W.b₆^5 - 590490*W.b₄*W.b₆^6 - 297432*W.b₆^4*W.b₈^2 - 279936*W.b₄^4*W.b₆^4 - 235984*W.b₄^2*W.b₈^4 - 58975*W.b₄^6*W.b₈^2 - 55296*W.b₄^7*W.b₆^2 - 2187*W.b₂^2*W.b₆^6 - 408*W.b₂^4*W.b₈^4 + 16384*W.b₈*W.b₄^8 + 154252*W.b₄^4*W.b₈^3 - W.b₂^4*W.b₄^2*W.b₆^4 - 577584*W.b₄^3*W.b₆^2*W.b₈^2 - 121520*W.b₂*W.b₆*W.b₈^4 - 78624*W.b₂^2*W.b₄^3*W.b₆^4 - 21392*W.b₂^2*W.b₄^3*W.b₈^3 - 16768*W.b₂^2*W.b₄^6*W.b₆^2 - 2048*W.b₈*W.b₂^2*W.b₄^7 - 384*W.b₂^4*W.b₄^4*W.b₈^2 - 30*W.b₄*W.b₂^6*W.b₈^3 - 3*W.b₂^6*W.b₆^2*W.b₈^2 + 56*W.b₈*W.b₂^4*W.b₆^4 + 114*W.b₆*W.b₂^5*W.b₈^3 + 162*W.b₄*W.b₂^3*W.b₆^5 + 1242*W.b₂^4*W.b₄^2*W.b₈^3 + 1667*W.b₂^3*W.b₆^3*W.b₈^2 + 6560*W.b₂^3*W.b₄^4*W.b₆^3 + 8030*W.b₂^2*W.b₄^5*W.b₈^2 + 13276*W.b₂^2*W.b₆^2*W.b₈^3 + 14336*W.b₂*W.b₆*W.b₄^8 + 23520*W.b₄*W.b₂^2*W.b₈^4 + 83106*W.b₂*W.b₈*W.b₆^5 + 131328*W.b₂*W.b₄^5*W.b₆^3 + 216810*W.b₈*W.b₄^5*W.b₆^2 + 347733*W.b₂*W.b₄^2*W.b₆^5 + 635040*W.b₄*W.b₆^2*W.b₈^3 + 905418*W.b₈*W.b₄^2*W.b₆^4 - 284688*W.b₂*W.b₈*W.b₄^3*W.b₆^3 - 139968*W.b₂*W.b₄*W.b₆^3*W.b₈^2 - 70956*W.b₄*W.b₈*W.b₂^2*W.b₆^4 - 40960*W.b₂*W.b₆*W.b₈*W.b₄^6 - 10544*W.b₆*W.b₂^3*W.b₄^3*W.b₈^2 - 5184*W.b₄*W.b₆*W.b₂^3*W.b₈^3 - 3416*W.b₂*W.b₆*W.b₄^2*W.b₈^3 - 2912*W.b₈*W.b₂^4*W.b₄^3*W.b₆^2 - 2628*W.b₄*W.b₂^4*W.b₆^2*W.b₈^2 + 6*W.b₄*W.b₈*W.b₂^5*W.b₆^3 + 477*W.b₆*W.b₂^5*W.b₄^2*W.b₈^2 + 4864*W.b₆*W.b₈*W.b₂^3*W.b₄^5 + 5484*W.b₈*W.b₂^2*W.b₄^4*W.b₆^2 + 25252*W.b₈*W.b₂^3*W.b₄^2*W.b₆^3 + 72789*W.b₂*W.b₆*W.b₄^4*W.b₈^2 + 84711*W.b₂^2*W.b₄^2*W.b₆^2*W.b₈^2 : K) * hrel
  have hev := congrArg (Polynomial.eval x₀) hcert
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C] at hev
  rw [h3, h4, mul_zero, mul_zero, add_zero] at hev
  rw [hDval] at hev
  exact hΔ (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0) |>.mp hev.symm)

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

/-
TorsionCard.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `WeierstrassCurve.n_torsion_card`
(`#E(k̄)[n] = n²` for `(n : k) ≠ 0`, `Torsion.lean`) into two faithful
arithmetic nodes, plus the PROVEN derivation:

* `TorsionCard.smul_surjective` (sorry node): **divisibility of the
  points group** — over a separably closed field, multiplication by
  `n` with `(n : k) ≠ 0` is surjective on the points of an elliptic
  curve. (The multiplication-by-`n` map is a finite separable isogeny of
  degree `n²`; over a separably closed field a separable isogeny is
  surjective on points.)

* `TorsionCard.prime_torsion_card` (sorry node): **the prime-level
  count** — for a prime `p` with `(p : k) ≠ 0`, the `p`-torsion of an
  elliptic curve over a separably closed field has exactly `p²`
  elements.

* `TorsionCard.card_torsionBy` (PROVEN): the general count by strong
  induction peeling off a minimal prime factor: multiplication by
  `p := n.minFac` restricts to a surjection `E[n] → E[n/p]`
  (divisibility node) whose kernel is `E[p]` (prime-level node), so
  `#E[n] = p² ⬝ (n/p)²` by Lagrange and the first isomorphism theorem.
  No CRT is needed.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.IsSepClosed
-- the division polynomials `Φ`, `ΨSq`, `preΨ'` appearing in the
-- point-level nodes below
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
-- `WeierstrassCurve.isCoprime_Φ_ΨSq` (Bézout from the resultant node),
-- used to rule out common roots of `Φ n` and `ΨSq n` in the proofs
import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat
-- the evaluation bridges `evalEval_ψ`, `evalEval_Ψ_sq`, `evalEval_φ`
-- between bivariate and univariate division polynomials on the curve
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Points
-- the sum-companion of the even recurrence, from the universal EDS
-- identity `normEDS_sum_companion`
import Fermat.FLT.EllipticCurve.PsiSumCompanion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
-- `Set.ncard` bridging between `Nat.card` of the torsion submodule and
-- `Finset.card` of the explicit point finset
import Mathlib.Data.Set.Card

@[expose] public section

namespace TorsionCard

open WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]
  [DecidableEq k]

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] in
/-- **The `n = 1` case of the multiplication formula** (PROVEN
2026-07-17, the first base case of the Washington Thm 3.6 induction):
`ψ₁ = 1 ≠ 0`, `1 • P = P`, `x ⬝ 1² = φ₁(x,y) = x`, and the
`y`-tracking reduces to `ψ₂(x,y) = 2y + a₁x + a₃`, which is its
definition (`ψ₂ = polynomialY`). -/
theorem zsmul_some_aux_one {x y : k} (h : (E⁄k).toAffine.Nonsingular x y) :
    ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
      (1 : ℤ) • (Affine.Point.some x y h : (E⁄k).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((E⁄k).ψ 1).evalEval x y ^ 2 = ((E⁄k).φ 1).evalEval x y ∧
      (2 * y' + (E⁄k).a₁ * x' + (E⁄k).a₃) * ((E⁄k).ψ 1).evalEval x y ^ 4 =
        ((E⁄k).ψ (2 * 1)).evalEval x y := by
  refine ⟨x, y, h, one_smul _ _, ?_, ?_⟩
  · rw [WeierstrassCurve.ψ_one, WeierstrassCurve.φ_one]
    simp [Polynomial.evalEval_C]
  · rw [WeierstrassCurve.ψ_one, show (2 : ℤ) * 1 = 2 from rfl,
      WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂]
    simp only [Polynomial.evalEval_one, one_pow, mul_one]
    rw [show ((E⁄k).toAffine.polynomialY).evalEval x y =
        2 * y + ((E⁄k).a₁ * x + (E⁄k).a₃) from by
      rw [Affine.polynomialY]
      simp [Polynomial.evalEval_add, Polynomial.evalEval_C, Polynomial.evalEval_X]]
    ring

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The `φ`-difference identity on the curve** (PROVEN 2026-07-17):
`φₙ(x,y) = x ⬝ ψₙ(x,y)² - ψₙ₊₁(x,y) ⬝ ψₙ₋₁(x,y)` — the value-level
form of the definition `Φ n = X ⬝ ΨSq n - preΨ (n+1) ⬝ preΨ (n-1) ⬝
(1 or Ψ₂Sq)`, with the parity factor absorbed into the `ψ`s via
`ψ₂² = Ψ₂Sq` on the curve. Equivalently `x - x([n]P) =
ψₙ₊₁ψₙ₋₁/ψₙ²`, the form of the multiplication formula the induction
steps consume. -/
theorem evalEval_φ_eq (n : ℤ) {x y : k} (h : (E⁄k).toAffine.Equation x y) :
    ((E⁄k).φ n).evalEval x y =
      x * ((E⁄k).ψ n).evalEval x y ^ 2 -
        ((E⁄k).ψ (n + 1)).evalEval x y * ((E⁄k).ψ (n - 1)).evalEval x y := by
  rw [WeierstrassCurve.evalEval_φ n h, WeierstrassCurve.evalEval_ψ n h,
    WeierstrassCurve.evalEval_ψ (n + 1) h, WeierstrassCurve.evalEval_ψ (n - 1) h,
    WeierstrassCurve.evalEval_Ψ_sq n h, WeierstrassCurve.Φ]
  have hψ₂ := WeierstrassCurve.evalEval_ψ₂_sq (W := (E⁄k)) h
  rcases Int.even_or_odd n with hev | hodd
  · have h1 : ¬ Even (n + 1) := by
      rw [Int.even_add_one]
      exact fun h' => h' hev
    have h2 : ¬ Even (n - 1) := by
      rw [Int.even_sub_one]
      exact fun h' => h' hev
    rw [show (E⁄k).Ψ (n + 1) = Polynomial.C ((E⁄k).preΨ (n + 1)) * 1 from by
        rw [WeierstrassCurve.Ψ, if_neg h1],
      show (E⁄k).Ψ (n - 1) = Polynomial.C ((E⁄k).preΨ (n - 1)) * 1 from by
        rw [WeierstrassCurve.Ψ, if_neg h2],
      if_pos hev]
    simp only [mul_one, Polynomial.evalEval_C, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_X]
  · have h1 : Even (n + 1) := by
      rw [Int.even_add_one]
      exact fun h' => (Int.not_even_iff_odd.mpr hodd) h'
    have h2 : Even (n - 1) := by
      rw [Int.even_sub_one]
      exact fun h' => (Int.not_even_iff_odd.mpr hodd) h'
    rw [show (E⁄k).Ψ (n + 1) = Polynomial.C ((E⁄k).preΨ (n + 1)) * (E⁄k).ψ₂ from by
        rw [WeierstrassCurve.Ψ, if_pos h1],
      show (E⁄k).Ψ (n - 1) = Polynomial.C ((E⁄k).preΨ (n - 1)) * (E⁄k).ψ₂ from by
        rw [WeierstrassCurve.Ψ, if_pos h2],
      if_neg (Int.not_even_iff_odd.mpr hodd)]
    simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    linear_combination (((E⁄k).preΨ (n + 1)).eval x *
      ((E⁄k).preΨ (n - 1)).eval x) * hψ₂

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- The value of `ψ₂` at any point of the plane: `2y + a₁x + a₃`
(no curve equation needed — `ψ₂` is the `Y`-derivative polynomial). -/
theorem evalEval_ψ_two (x y : k) :
    ((E⁄k).ψ 2).evalEval x y = 2 * y + (E⁄k).a₁ * x + (E⁄k).a₃ := by
  rw [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂, Affine.polynomialY]
  simp only [Polynomial.evalEval_add, Polynomial.evalEval_C,
    Polynomial.evalEval_X, Polynomial.evalEval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  ring

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The even `ψ`-recurrence on the curve** (PROVEN 2026-07-17):
`ψ₂ₘ ⬝ ψ₂ = ψₘ₋₁² ψₘ ψₘ₊₂ - ψₘ₋₂ ψₘ ψₘ₊₁²` at a point of the curve
(the value-level instance of `Ψ_even`). -/
theorem evalEval_ψ_even (m : ℤ) {x y : k}
    (h : (E⁄k).toAffine.Equation x y) :
    ((E⁄k).ψ (2 * m)).evalEval x y * ((E⁄k).ψ 2).evalEval x y =
      ((E⁄k).ψ (m - 1)).evalEval x y ^ 2 * ((E⁄k).ψ m).evalEval x y *
        ((E⁄k).ψ (m + 2)).evalEval x y -
      ((E⁄k).ψ (m - 2)).evalEval x y * ((E⁄k).ψ m).evalEval x y *
        ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 := by
  have hkey := congrArg (Polynomial.evalEval x y)
    (WeierstrassCurve.Ψ_even (W := (E⁄k)) m)
  simp only [Polynomial.evalEval_mul, Polynomial.evalEval_sub,
    Polynomial.evalEval_pow] at hkey
  rw [WeierstrassCurve.evalEval_ψ (2 * m) h, WeierstrassCurve.ψ_two,
    WeierstrassCurve.evalEval_ψ (m - 1) h, WeierstrassCurve.evalEval_ψ m h,
    WeierstrassCurve.evalEval_ψ (m + 2) h, WeierstrassCurve.evalEval_ψ (m - 2) h,
    WeierstrassCurve.evalEval_ψ (m + 1) h]
  exact hkey

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The odd `ψ`-recurrence on the curve** (PROVEN 2026-07-17):
`ψ₂ₘ₊₁ = ψₘ₊₂ ψₘ³ - ψₘ₋₁ ψₘ₊₁³` at a point of the curve — the
correction term of `Ψ_odd` carries the curve polynomial as a factor
and dies on points. -/
theorem evalEval_ψ_odd (m : ℤ) {x y : k}
    (h : (E⁄k).toAffine.Equation x y) :
    ((E⁄k).ψ (2 * m + 1)).evalEval x y =
      ((E⁄k).ψ (m + 2)).evalEval x y * ((E⁄k).ψ m).evalEval x y ^ 3 -
        ((E⁄k).ψ (m - 1)).evalEval x y * ((E⁄k).ψ (m + 1)).evalEval x y ^ 3 := by
  have h0 : ((E⁄k).toAffine.polynomial).evalEval x y = 0 := h
  have hkey := congrArg (Polynomial.evalEval x y)
    (WeierstrassCurve.Ψ_odd (W := (E⁄k)) m)
  simp only [Polynomial.evalEval_mul, Polynomial.evalEval_sub,
    Polynomial.evalEval_add, Polynomial.evalEval_pow] at hkey
  rw [h0, zero_mul, zero_mul, add_zero] at hkey
  rw [WeierstrassCurve.evalEval_ψ (2 * m + 1) h,
    WeierstrassCurve.evalEval_ψ (m + 2) h, WeierstrassCurve.evalEval_ψ m h,
    WeierstrassCurve.evalEval_ψ (m - 1) h, WeierstrassCurve.evalEval_ψ (m + 1) h]
  exact hkey

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8000 in
omit [E.IsElliptic] in
/-- **The duplication formula** (PROVEN 2026-07-17, the `n = 2` seed of
the Washington Thm 3.6 induction, characteristic-free): if
`ψ₂(x,y) ≠ 0` then `2 • P` is affine with `x' ⬝ ψ₂² = φ₂(x,y)` and
`(2y' + a₁x' + a₃) ⬝ ψ₂⁴ = ψ₄(x,y)`. The point is the tangent-line
addition `P + P`; after clearing the slope denominator `ψ₂(x,y)`, both
coordinate identities are polynomial consequences of the curve
equation. -/
theorem zsmul_some_aux_two {x y : k}
    (h : (E⁄k).toAffine.Nonsingular x y)
    (hψ : ((E⁄k).ψ 2).evalEval x y ≠ 0) :
    ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
      (2 : ℤ) • (Affine.Point.some x y h : (E⁄k).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((E⁄k).ψ 2).evalEval x y ^ 2 = ((E⁄k).φ 2).evalEval x y ∧
      (2 * y' + (E⁄k).a₁ * x' + (E⁄k).a₃) * ((E⁄k).ψ 2).evalEval x y ^ 4 =
        ((E⁄k).ψ (2 * 2)).evalEval x y := by
  classical
  have hψ₂v := evalEval_ψ_two E x y
  have hyne : y ≠ (E⁄k).toAffine.negY x y := by
    intro hy
    apply hψ
    rw [hψ₂v, Affine.negY] at *
    linear_combination hy
  have hxy : ¬(x = x ∧ y = (E⁄k).toAffine.negY x y) := fun hc => hyne hc.2
  -- the slope, cleared of its denominator
  have hden : y - (E⁄k).toAffine.negY x y = ((E⁄k).ψ 2).evalEval x y := by
    rw [hψ₂v, Affine.negY]
    ring
  have hslope : (E⁄k).toAffine.slope x x y y =
      (3 * x ^ 2 + 2 * (E⁄k).a₂ * x + (E⁄k).a₄ - (E⁄k).a₁ * y) /
        ((E⁄k).ψ 2).evalEval x y := by
    rw [Affine.slope, if_pos rfl, if_neg hyne, hden]
  -- the equation of the point
  have heq := (Affine.equation_iff _ _).mp h.1
  -- the addition
  have hψ₂ψ2 : ((E⁄k).ψ₂).evalEval x y = ((E⁄k).ψ 2).evalEval x y := by
    rw [WeierstrassCurve.ψ_two]
  have hφ2 : ((E⁄k).φ 2).evalEval x y =
      x * ((E⁄k).ψ 2).evalEval x y ^ 2 - ((E⁄k).Ψ₃).eval x := by
    rw [WeierstrassCurve.φ_two]
    simp only [Polynomial.evalEval_sub, Polynomial.evalEval_mul,
      Polynomial.evalEval_pow, Polynomial.evalEval_C, Polynomial.eval_X]
    rw [hψ₂ψ2]
  have hψ4 : ((E⁄k).ψ (2 * 2)).evalEval x y =
      ((E⁄k).preΨ₄).eval x * ((E⁄k).ψ 2).evalEval x y := by
    rw [show (2 * 2 : ℤ) = 4 from rfl, WeierstrassCurve.ψ_four]
    simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C]
    rw [hψ₂ψ2]
  -- the multiplied slope equation, avoiding all division
  rw [hψ₂v] at hψ
  have hT : (E⁄k).toAffine.slope x x y y * (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) =
      3 * x ^ 2 + 2 * (E⁄k).a₂ * x + (E⁄k).a₄ - (E⁄k).a₁ * y := by
    rw [hslope, hψ₂v, div_mul_cancel₀ _ hψ]
  refine ⟨_, _, Affine.nonsingular_add h h hxy,
    by rw [two_smul ℤ]; exact Affine.Point.add_some hxy, ?_, ?_⟩
  · -- the `x`-coordinate identity
    rw [Affine.addX, hφ2, hψ₂v, WeierstrassCurve.Ψ₃,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
    linear_combination ((E⁄k).toAffine.slope x x y y *
        (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) +
      (3 * x ^ 2 + 2 * (E⁄k).a₂ * x + (E⁄k).a₄ - (E⁄k).a₁ * y) +
      (E⁄k).a₁ * (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃)) * hT +
      (-((E⁄k).a₁ ^ 2) - 4 * (E⁄k).a₂ - 12 * x) * heq
  · -- the `y`-coordinate identity
    rw [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, hψ4,
      hψ₂v, WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
    linear_combination
      (-2 * (((E⁄k).toAffine.slope x x y y * (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃)) ^ 2 +
          ((E⁄k).toAffine.slope x x y y * (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃)) *
            (3 * x ^ 2 + 2 * (E⁄k).a₂ * x + (E⁄k).a₄ - (E⁄k).a₁ * y) +
          (3 * x ^ 2 + 2 * (E⁄k).a₂ * x + (E⁄k).a₄ - (E⁄k).a₁ * y) ^ 2) *
          (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) -
        3 * (E⁄k).a₁ * ((E⁄k).toAffine.slope x x y y *
            (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) +
          (3 * x ^ 2 + 2 * (E⁄k).a₂ * x + (E⁄k).a₄ - (E⁄k).a₁ * y)) *
          (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) ^ 2 +
        (2 * (E⁄k).a₂ + 6 * x - (E⁄k).a₁ ^ 2) *
          (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) ^ 3) * hT +
      ((2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) *
        ((E⁄k).a₁ ^ 4 * x + (E⁄k).a₁ ^ 3 * (E⁄k).a₃ +
          8 * (E⁄k).a₁ ^ 2 * (E⁄k).a₂ * x + 2 * (E⁄k).a₁ ^ 2 * (E⁄k).a₄ +
          10 * (E⁄k).a₁ ^ 2 * x ^ 2 + 4 * (E⁄k).a₁ * (E⁄k).a₂ * (E⁄k).a₃ -
          4 * (E⁄k).a₁ * (E⁄k).a₃ * x - 16 * (E⁄k).a₁ * x * y +
          16 * (E⁄k).a₂ ^ 2 * x + 8 * (E⁄k).a₂ * (E⁄k).a₄ +
          56 * (E⁄k).a₂ * x ^ 2 - 8 * (E⁄k).a₃ ^ 2 - 16 * (E⁄k).a₃ * y +
          8 * (E⁄k).a₄ * x - 16 * (E⁄k).a₆ + 56 * x ^ 3 - 16 * y ^ 2)) * heq

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] in
/-- **The secant addition formula in multiplied form** (PROVEN
2026-07-17): for two affine points with distinct `x`-coordinates,
`P₁ + P₂` is affine, its `x`-coordinate satisfies the multiplied
secant identity, and its `ψ₂`-value satisfies the degree-one tracking
identity. Characteristic-free and division-free; no curve equation is
needed (both identities are `λ`-elimination telescopes). -/
theorem add_some_coords {x₁ y₁ x₂ y₂ : k}
    (h₁ : (E⁄k).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E⁄k).toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    ∃ (x₃ y₃ : k) (h₃ : (E⁄k).toAffine.Nonsingular x₃ y₃),
      (Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) + Affine.Point.some x₂ y₂ h₂ =
        Affine.Point.some x₃ y₃ h₃ ∧
      x₃ * (x₁ - x₂) ^ 2 = (y₁ - y₂) ^ 2 + (E⁄k).a₁ * (y₁ - y₂) * (x₁ - x₂) -
        ((E⁄k).a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 ∧
      (2 * y₃ + (E⁄k).a₁ * x₃ + (E⁄k).a₃) * (x₁ - x₂) =
        -(2 * (y₁ - y₂)) * (x₃ - x₁) -
          (2 * y₁ + (E⁄k).a₁ * x₃ + (E⁄k).a₃) * (x₁ - x₂) := by
  classical
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (E⁄k).toAffine.negY x₂ y₂) := fun hc => hx hc.1
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hslope : (E⁄k).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
    rw [Affine.slope, if_neg hx]
  have hS : (E⁄k).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hslope, div_mul_cancel₀ _ hd]
  refine ⟨_, _, Affine.nonsingular_add h₁ h₂ hxy,
    Affine.Point.add_some hxy, ?_, ?_⟩
  · rw [Affine.addX]
    linear_combination ((E⁄k).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) +
      (y₁ - y₂) + (E⁄k).a₁ * (x₁ - x₂)) * hS
  · rw [Affine.addY, Affine.negY, Affine.negAddY]
    linear_combination (-2 : k) * ((E⁄k).toAffine.addX x₁ x₂
      ((E⁄k).toAffine.slope x₁ x₂ y₁ y₂) - x₁) * hS

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] in
/-- **The `x`-collision dichotomy** (PROVEN 2026-07-17): two affine
points share an `x`-coordinate exactly when they are equal or
opposite. Used by the induction's addition step to split off the
`(2m+1) • P = 0` branch. -/
theorem eq_or_add_eq_zero_of_X_eq {x₁ y₁ x₂ y₂ : k}
    (h₁ : (E⁄k).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E⁄k).toAffine.Nonsingular x₂ y₂) (hx : x₁ = x₂) :
    (Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) = Affine.Point.some x₂ y₂ h₂ ∨
      (Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) + Affine.Point.some x₂ y₂ h₂ = 0 := by
  rcases Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx with hy | hy
  · left
    subst hx
    subst hy
    rfl
  · right
    exact Affine.Point.add_of_Y_eq hx hy

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] in
/-- **The smul-level collision consequence** (PROVEN 2026-07-17): if
`m • P` and `(m+1) • P` are affine with the same `x`-coordinate, then
`(2m+1) • P = 0` (they cannot be equal, since their difference is the
affine point `P`). -/
theorem smul_collision {m : ℤ} {x y xm ym xm1 ym1 : k}
    (h : (E⁄k).toAffine.Nonsingular x y)
    (hm : (E⁄k).toAffine.Nonsingular xm ym)
    (hm1 : (E⁄k).toAffine.Nonsingular xm1 ym1)
    (heqm : m • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some xm ym hm)
    (heqm1 : (m + 1) • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some xm1 ym1 hm1)
    (hxx : xm1 = xm) :
    (2 * m + 1) • (Affine.Point.some x y h : (E⁄k).Point) = 0 := by
  rcases eq_or_add_eq_zero_of_X_eq E hm1 hm hxx with heq | hadd
  · -- equal points would make `P` zero
    exfalso
    have hP : (Affine.Point.some x y h : (E⁄k).Point) = 0 := by
      have hsub : ((m + 1) - m) • (Affine.Point.some x y h : (E⁄k).Point) =
          (m + 1) • (Affine.Point.some x y h : (E⁄k).Point) -
            m • (Affine.Point.some x y h : (E⁄k).Point) := sub_smul _ _ _
      rw [show (m + 1) - m = 1 from by ring, one_smul, heqm, heqm1, heq,
        sub_self] at hsub
      exact hsub
    exact nomatch hP.trans
      (show (0 : (E⁄k).Point) = Affine.Point.zero from rfl)
  · -- opposite points give the vanishing
    have : (2 * m + 1) • (Affine.Point.some x y h : (E⁄k).Point) =
        ((m + 1) + m) • (Affine.Point.some x y h : (E⁄k).Point) := by
      congr 1
      ring
    rw [this, add_smul, heqm, heqm1]
    exact hadd

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The gap-1 `x`-difference identity** (PROVEN 2026-07-17): from the
multiplication formulas at `m` and `m+1`, the difference of the
`x`-coordinates is `x([m+1]P) - x([m]P) = -ψ₂ₘ₊₁/(ψₘψₘ₊₁)²` in
multiplied form — by the `φ`-difference identity and the odd
recurrence, with no further input. -/
theorem x_sub_gap_one {m : ℤ} {x y xm xm1 : k}
    (h : (E⁄k).toAffine.Equation x y)
    (hm : xm * ((E⁄k).ψ m).evalEval x y ^ 2 = ((E⁄k).φ m).evalEval x y)
    (hm1 : xm1 * ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 =
      ((E⁄k).φ (m + 1)).evalEval x y) :
    (xm1 - xm) * (((E⁄k).ψ m).evalEval x y * ((E⁄k).ψ (m + 1)).evalEval x y) ^ 2 =
      -((E⁄k).ψ (2 * m + 1)).evalEval x y := by
  have hφm := evalEval_φ_eq E m h
  have hφm1 := evalEval_φ_eq E (m + 1) h
  have hodd := evalEval_ψ_odd E m h
  rw [show m + 1 + 1 = m + 2 from by ring] at hφm1
  rw [show m + 1 - 1 = m from by ring] at hφm1
  linear_combination ((E⁄k).ψ m).evalEval x y ^ 2 * hm1 -
    ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 * hm +
    ((E⁄k).ψ m).evalEval x y ^ 2 * hφm1 -
    ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 * hφm + hodd

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The gap-2 `x`-difference identity** (PROVEN 2026-07-17): from the
multiplication formulas at `m-1` and `m+1`, the difference of the
`x`-coordinates is `x([m-1]P) - x([m+1]P) = ψ₂ₘψ₂/(ψₘ₋₁ψₘ₊₁)²` in
multiplied form — by the `φ`-difference identity and the even
recurrence. -/
theorem x_sub_gap_two {m : ℤ} {x y xm1 xp1 : k}
    (h : (E⁄k).toAffine.Equation x y)
    (hm1 : xm1 * ((E⁄k).ψ (m - 1)).evalEval x y ^ 2 =
      ((E⁄k).φ (m - 1)).evalEval x y)
    (hp1 : xp1 * ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 =
      ((E⁄k).φ (m + 1)).evalEval x y) :
    (xm1 - xp1) *
        (((E⁄k).ψ (m - 1)).evalEval x y * ((E⁄k).ψ (m + 1)).evalEval x y) ^ 2 =
      ((E⁄k).ψ (2 * m)).evalEval x y * ((E⁄k).ψ 2).evalEval x y := by
  have hφm1 := evalEval_φ_eq E (m - 1) h
  have hφp1 := evalEval_φ_eq E (m + 1) h
  have heven := evalEval_ψ_even E m h
  rw [show m - 1 + 1 = m from by ring] at hφm1
  rw [show m - 1 - 1 = m - 2 from by ring] at hφm1
  rw [show m + 1 + 1 = m + 2 from by ring] at hφp1
  rw [show m + 1 - 1 = m from by ring] at hφp1
  linear_combination ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 * hm1 -
    ((E⁄k).ψ (m - 1)).evalEval x y ^ 2 * hp1 +
    ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 * hφm1 -
    ((E⁄k).ψ (m - 1)).evalEval x y ^ 2 * hφp1 - heven

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The universal two-point cross identity** (PROVEN 2026-07-17):
for any two points of the curve, with `X₃` the multiplied
`x`-coordinate expression of `Q₁ - Q₂` (the secant through `Q₁` and
`-Q₂`), the product of the `ψ₂`-values satisfies
`2t₁t₂(x₁-x₂)² = (b₂+4x₁+4x₂)(x₁-x₂)⁴ + 4X₃ - (Ψ₂Sq(x₁)+Ψ₂Sq(x₂))(x₁-x₂)²`.
Every cross-tracking relation of the multiplication-formula induction
is an instance of this single identity (pairs `(n,n+1)` with
difference `P`, `(m-1,m+1)` with difference `2P`, `(1,m)` with
difference `(m-1)P`), so the induction package needs only the
`x`-formula and the `ψ₂`-tracking. Certificate: cofactors `-4, -4` on
the two curve equations. -/
theorem two_point_cross_identity {x₁ y₁ x₂ y₂ : k}
    (h₁ : (E⁄k).toAffine.Equation x₁ y₁)
    (h₂ : (E⁄k).toAffine.Equation x₂ y₂) :
    2 * ((2 * y₁ + (E⁄k).a₁ * x₁ + (E⁄k).a₃) *
        (2 * y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃)) * (x₁ - x₂) ^ 2 =
      ((E⁄k).b₂ + 4 * x₁ + 4 * x₂) * (x₁ - x₂) ^ 4 +
        4 * (((y₁ + y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃) ^ 2 +
          (E⁄k).a₁ * (y₁ + y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃) * (x₁ - x₂) -
          ((E⁄k).a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) * (x₁ - x₂) ^ 2) -
        (((E⁄k).Ψ₂Sq).eval x₁ + ((E⁄k).Ψ₂Sq).eval x₂) * (x₁ - x₂) ^ 2 := by
  have heq₁ := (Affine.equation_iff x₁ y₁).mp h₁
  have heq₂ := (Affine.equation_iff x₂ y₂).mp h₂
  rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  linear_combination (-4 : k) * (x₁ - x₂) ^ 2 * heq₁ +
    (-4 : k) * (x₁ - x₂) ^ 2 * heq₂

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8000 in
omit [E.IsElliptic] in
/-- **The generic odd induction step** (PROVEN 2026-07-17): given
affine IH data at `m` and `m+1` (points, `x`-formulas, trackings) with
distinct `x`-coordinates, `(2m+1) • P` is affine and satisfies the
`x`-formula. The core `(x - x₃)·dx² = t₁t₂` is a PURE RING consequence
of the two secant identities (the sum `(m+1)P + mP` and the difference
`(m+1)P + (-mP) = P`); the conversion to division polynomials uses the
`φ`-difference identity, the gap-1 identity, and the trackings. -/
theorem zsmul_odd_step_x {m : ℤ}
    {x y xm ym xm1 ym1 : k}
    (h : (E⁄k).toAffine.Nonsingular x y)
    (hm : (E⁄k).toAffine.Nonsingular xm ym)
    (hm1 : (E⁄k).toAffine.Nonsingular xm1 ym1)
    (heqm : m • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some xm ym hm)
    (heqm1 : (m + 1) • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some xm1 ym1 hm1)
    (hxm : xm * ((E⁄k).ψ m).evalEval x y ^ 2 = ((E⁄k).φ m).evalEval x y)
    (hxm1 : xm1 * ((E⁄k).ψ (m + 1)).evalEval x y ^ 2 =
      ((E⁄k).φ (m + 1)).evalEval x y)
    (htm : (2 * ym + (E⁄k).a₁ * xm + (E⁄k).a₃) *
      ((E⁄k).ψ m).evalEval x y ^ 4 = ((E⁄k).ψ (2 * m)).evalEval x y)
    (htm1 : (2 * ym1 + (E⁄k).a₁ * xm1 + (E⁄k).a₃) *
      ((E⁄k).ψ (m + 1)).evalEval x y ^ 4 =
      ((E⁄k).ψ (2 * (m + 1))).evalEval x y)
    (hne : xm1 ≠ xm) :
    ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
      (2 * m + 1) • (Affine.Point.some x y h : (E⁄k).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((E⁄k).ψ (2 * m + 1)).evalEval x y ^ 2 =
        ((E⁄k).φ (2 * m + 1)).evalEval x y := by
  classical
  -- the sum `(m+1)P + mP`
  obtain ⟨x₃, y₃, h₃, hadd, hX₃, -⟩ := add_some_coords E hm1 hm hne
  have hsum : (2 * m + 1) • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some x₃ y₃ h₃ := by
    rw [show 2 * m + 1 = (m + 1) + m from by ring, add_smul, heqm, heqm1, hadd]
  -- the difference `(m+1)P + (-mP) = P`
  have hmneg : (E⁄k).toAffine.Nonsingular xm ((E⁄k).toAffine.negY xm ym) :=
    (Affine.nonsingular_neg ..).mpr hm
  obtain ⟨x₄, y₄, h₄, hadd₄, hX₄, -⟩ := add_some_coords E hm1 hmneg hne
  have hdiff : (Affine.Point.some x₄ y₄ h₄ : (E⁄k).Point) =
      Affine.Point.some x y h := by
    rw [← hadd₄, ← Affine.Point.neg_some (h := hm)]
    have hsub : (Affine.Point.some xm1 ym1 hm1 : (E⁄k).Point) -
        Affine.Point.some xm ym hm = Affine.Point.some x y h := by
      rw [← heqm, ← heqm1, ← sub_smul,
        show (m + 1) - m = 1 from by ring, one_smul]
    rw [← hsub, sub_eq_add_neg]
  have hx₄ : x₄ = x := by injection hdiff
  -- the ring core: `(x - x₃)·dx² = t₁t₂`
  have hcore : (x - x₃) * (xm1 - xm) ^ 2 =
      (2 * ym1 + (E⁄k).a₁ * xm1 + (E⁄k).a₃) *
        (2 * ym + (E⁄k).a₁ * xm + (E⁄k).a₃) := by
    have hX₄' := hX₄
    rw [hx₄, Affine.negY] at hX₄'
    linear_combination hX₄' - hX₃
  -- assemble: `φ`-difference at `2m+1`, gap-1, trackings
  have hφ := evalEval_φ_eq E (2 * m + 1) h.1
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring,
    show 2 * m + 1 - 1 = 2 * m from by ring] at hφ
  have hgap := x_sub_gap_one E h.1 hxm hxm1
  have hprod := congr(($htm1) * ($htm))
  refine ⟨x₃, y₃, h₃, hsum, ?_⟩
  linear_combination -hφ + (x₃ - x) *
      (((E⁄k).ψ (2 * m + 1)).evalEval x y -
        (xm1 - xm) * (((E⁄k).ψ m).evalEval x y *
          ((E⁄k).ψ (m + 1)).evalEval x y) ^ 2) * hgap -
    (((E⁄k).ψ m).evalEval x y * ((E⁄k).ψ (m + 1)).evalEval x y) ^ 4 * hcore -
    hprod

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The membership identity** (PROVEN 2026-07-17): on the curve,
`Ψ₂Sq (x) = (2y + a₁x + a₃)²` — the square of the `ψ₂`-value. This is
the `linear_combination` input the induction certificates call the
"membership" of a point; it comes free from the point's `Equation`
with cofactor `-4`. -/
theorem eval_Ψ₂Sq_eq_sq {x y : k} (h : (E⁄k).toAffine.Equation x y) :
    ((E⁄k).Ψ₂Sq).eval x = (2 * y + ((E⁄k).a₁ * x + (E⁄k).a₃)) ^ 2 := by
  have heq := (Affine.equation_iff x y).mp h
  rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  linear_combination (-4 : k) * heq

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8000 in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The two-point trace identity** (PROVEN 2026-07-17): for two curve
points with `x₁ ≠ x₂` and `x₃`, `t₃` given by the multiplied secant
`x`- and `ψ₂`-expressions of `Q₁ + Q₂` (the conclusions of
`add_some_coords`), the `ψ₂`-value `s = 2y₂ + a₁x₂ + a₃` satisfies
`s(t₃ + s) = (x₂-x₃)(6x₂² + b₂x₂ + b₄) - 2(x₂-x₁)(x₂-x₃)²`.
This pins the SIGN of the `ψ₂`-tracking of a sum from the `y`-addition
formula; it is the pure two-point residue of the multiplication
formula's tracking output (which then follows from the sum-companion
recurrence `evalEval_ψ_sum` with no window widening). Certificate:
clear `(x₁-x₂)⁵`, eliminate `t₃` by the `ψ₂`-secant and `x₃` by the
`x`-secant, then reduce by the two curve equations. -/
theorem two_point_trace_identity {x₁ y₁ x₂ y₂ x₃ t₃ : k}
    (h₁ : (E⁄k).toAffine.Equation x₁ y₁)
    (h₂ : (E⁄k).toAffine.Equation x₂ y₂)
    (hX₃ : x₃ * (x₁ - x₂) ^ 2 = (y₁ - y₂) ^ 2 +
      (E⁄k).a₁ * (y₁ - y₂) * (x₁ - x₂) -
      ((E⁄k).a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2)
    (hY₃ : t₃ * (x₁ - x₂) =
      -(2 * (y₁ - y₂)) * (x₃ - x₁) -
        (2 * y₁ + (E⁄k).a₁ * x₃ + (E⁄k).a₃) * (x₁ - x₂))
    (hne : x₁ ≠ x₂) :
    (2 * y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃) *
        (t₃ + (2 * y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃)) =
      (x₂ - x₃) * (6 * x₂ ^ 2 + (E⁄k).b₂ * x₂ + (E⁄k).b₄) -
        2 * (x₂ - x₁) * (x₂ - x₃) ^ 2 := by
  have heq₁ := (Affine.equation_iff x₁ y₁).mp h₁
  have heq₂ := (Affine.equation_iff x₂ y₂).mp h₂
  have hkey : ((2 * y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃) *
        (t₃ + (2 * y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃))) * (x₁ - x₂) ^ 5 =
      ((x₂ - x₃) * (6 * x₂ ^ 2 + (E⁄k).b₂ * x₂ + (E⁄k).b₄) -
        2 * (x₂ - x₁) * (x₂ - x₃) ^ 2) * (x₁ - x₂) ^ 5 := by
    rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    linear_combination ((2 * y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃) *
        (x₁ - x₂) ^ 4) * hY₃ +
      (-2*(E⁄k).a₁*x₁^3*y₁ + 4*(E⁄k).a₁*x₁^2*x₂*y₁
        + 2*(E⁄k).a₁*x₁^2*x₂*y₂ - 2*(E⁄k).a₁*x₁*x₂^2*y₁
        - 4*(E⁄k).a₁*x₁*x₂^2*y₂ + 2*(E⁄k).a₁*x₂^3*y₂ + 2*(E⁄k).a₂*x₁^4
        - 4*(E⁄k).a₂*x₁^3*x₂ + 4*(E⁄k).a₂*x₁*x₂^3 - 2*(E⁄k).a₂*x₂^4
        - 2*(E⁄k).a₃*x₁^2*y₁ + 2*(E⁄k).a₃*x₁^2*y₂ + 4*(E⁄k).a₃*x₁*x₂*y₁
        - 4*(E⁄k).a₃*x₁*x₂*y₂ - 2*(E⁄k).a₃*x₂^2*y₁ + 2*(E⁄k).a₃*x₂^2*y₂
        + 2*(E⁄k).a₄*x₁^3 - 6*(E⁄k).a₄*x₁^2*x₂ + 6*(E⁄k).a₄*x₁*x₂^2
        - 2*(E⁄k).a₄*x₂^3 + 2*x₁^5 - 2*x₁^4*x₂ - 2*x₁^4*x₃ - 6*x₁^3*x₂^2
        + 8*x₁^3*x₂*x₃ + 10*x₁^2*x₂^3 - 12*x₁^2*x₂^2*x₃ - 2*x₁^2*y₁^2
        + 2*x₁^2*y₂^2 - 4*x₁*x₂^4 + 8*x₁*x₂^3*x₃ + 4*x₁*x₂*y₁^2
        - 4*x₁*x₂*y₂^2 - 2*x₂^4*x₃ - 2*x₂^2*y₁^2 + 2*x₂^2*y₂^2) * hX₃ +
      (-2*(E⁄k).a₁*x₁^3*y₁ + 2*(E⁄k).a₁*x₁^3*y₂ + 6*(E⁄k).a₁*x₁^2*x₂*y₁
        - 4*(E⁄k).a₁*x₁^2*x₂*y₂ - 6*(E⁄k).a₁*x₁*x₂^2*y₁
        + 2*(E⁄k).a₁*x₁*x₂^2*y₂ + 2*(E⁄k).a₁*x₂^3*y₁ + 2*(E⁄k).a₂*x₁^4
        - 8*(E⁄k).a₂*x₁^3*x₂ + 10*(E⁄k).a₂*x₁^2*x₂^2 - 4*(E⁄k).a₂*x₁*x₂^3
        + 2*(E⁄k).a₃*x₁^2*y₂ - 4*(E⁄k).a₃*x₁*x₂*y₂ + 2*(E⁄k).a₃*x₂^2*y₂
        - 2*(E⁄k).a₄*x₁^2*x₂ + 4*(E⁄k).a₄*x₁*x₂^2 - 2*(E⁄k).a₄*x₂^3
        - 2*(E⁄k).a₆*x₁^2 + 4*(E⁄k).a₆*x₁*x₂ - 2*(E⁄k).a₆*x₂^2 + 2*x₁^5
        - 4*x₁^4*x₂ - 4*x₁^3*x₂^2 + 14*x₁^2*x₂^3 - 2*x₁^2*y₁^2
        + 4*x₁^2*y₁*y₂ - 10*x₁*x₂^4 + 4*x₁*x₂*y₁^2 - 8*x₁*x₂*y₁*y₂
        + 2*x₂^5 - 2*x₂^2*y₁^2 + 4*x₂^2*y₁*y₂) * heq₁ +
      (-2*(E⁄k).a₁*x₁^3*y₂ - 2*(E⁄k).a₁*x₁^2*x₂*y₁
        + 6*(E⁄k).a₁*x₁^2*x₂*y₂ + 4*(E⁄k).a₁*x₁*x₂^2*y₁
        - 6*(E⁄k).a₁*x₁*x₂^2*y₂ - 2*(E⁄k).a₁*x₂^3*y₁ + 2*(E⁄k).a₁*x₂^3*y₂
        + 4*(E⁄k).a₂*x₁^3*x₂ - 10*(E⁄k).a₂*x₁^2*x₂^2 + 8*(E⁄k).a₂*x₁*x₂^3
        - 2*(E⁄k).a₂*x₂^4 - 2*(E⁄k).a₃*x₁^2*y₁ + 4*(E⁄k).a₃*x₁*x₂*y₁
        - 2*(E⁄k).a₃*x₂^2*y₁ + 2*(E⁄k).a₄*x₁^3 - 4*(E⁄k).a₄*x₁^2*x₂
        + 2*(E⁄k).a₄*x₁*x₂^2 + 2*(E⁄k).a₆*x₁^2 - 4*(E⁄k).a₆*x₁*x₂
        + 2*(E⁄k).a₆*x₂^2 + 6*x₁^3*x₂^2 - 16*x₁^2*x₂^3 - 4*x₁^2*y₁*y₂
        + 2*x₁^2*y₂^2 + 14*x₁*x₂^4 + 8*x₁*x₂*y₁*y₂ - 4*x₁*x₂*y₂^2 - 4*x₂^5
        - 4*x₂^2*y₁*y₂ + 2*x₂^2*y₂^2) * heq₂
  exact mul_right_cancel₀ (pow_ne_zero 5 (sub_ne_zero.mpr hne)) hkey

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The sum-companion of the even recurrence** (DERIVED 2026-07-17
from the universal EDS identity via `PsiSumCompanion`): on the curve,
`ψₙ₋₁²ψₙ₊₂ + ψₙ₋₂ψₙ₊₁² = ψₙ₋₁ψₙψₙ₊₁(6x² + b₂x + b₄) - ψₙ³ Ψ₂Sq(x)`.
This is the additive counterpart of `evalEval_ψ_even` (which gives the
DIFFERENCE `ψₙ₋₁²ψₙψₙ₊₂ - ψₙ₋₂ψₙψₙ₊₁² = ψ₂ₙψ₂`): together they
resolve `ψₙ₋₁²ψₙ₊₂` and `ψₙ₋₂ψₙ₊₁²` individually. Classically it is
the trace form of the addition formulas (`x(Q+P) + x(Q-P)`). It rests
on the sharp universal node
`EllipticDivisibilitySequence.normEDS_sum_companion`, transported to
the curve by the anchor identity `Ψ₃(6X²+b₂X+b₄) = preΨ₄ + Ψ₂Sq²`,
the coordinate-ring membership `ψ₂² ≡ Ψ₂Sq`, cancellation of the
non-zero-divisor `ψ₂Ψ₃` over the universal curve, and base change.
It is the final identity input for the multiplication-formula
induction's tracking output. -/
theorem evalEval_ψ_sum (n : ℤ) {x y : k}
    (h : (E⁄k).toAffine.Equation x y) :
    ((E⁄k).ψ (n - 1)).evalEval x y ^ 2 * ((E⁄k).ψ (n + 2)).evalEval x y +
      ((E⁄k).ψ (n - 2)).evalEval x y * ((E⁄k).ψ (n + 1)).evalEval x y ^ 2 =
    ((E⁄k).ψ (n - 1)).evalEval x y * ((E⁄k).ψ n).evalEval x y *
      ((E⁄k).ψ (n + 1)).evalEval x y *
      (6 * x ^ 2 + (E⁄k).b₂ * x + (E⁄k).b₄) -
    ((E⁄k).ψ n).evalEval x y ^ 3 * ((E⁄k).Ψ₂Sq).eval x :=
  PsiSumCompanion.evalEval_ψ_sum (E⁄k) n h

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8000 in
omit [E.IsElliptic] in
/-- **The consecutive induction step** (PROVEN 2026-07-17,
parity-free — supersedes separate odd/even steps): given affine IH
data at `n-1` (point, `x`-formula, tracking) and `n-2` (point,
`x`-formula), with `x([n-1]P) ≠ x(P)`, `ψₙ₋₂(x,y) ≠ 0`,
`ψₙ₋₁(x,y) ≠ 0` and `ψ₂(x,y) ≠ 0`, the point `n•P = [n-1]P + P` is
affine and satisfies the `x`-formula AND the `ψ₂`-tracking formula
(the full IH package for the next step). The `x`-core
`(x₂ - x₃)dx² = t₁s` is a pure ring identity from the sum/difference
secants; the conversion is `φ`-difference at `n, n-1, n-2` + the even
recurrence at `n-1` + the tracking, cancelling `ψₙ₋₂²`. The tracking
output combines `two_point_trace_identity` (which pins the sign from
the `y`-addition formula), the sum-companion recurrence
`evalEval_ψ_sum` and the even recurrence at `n`, cancelling
`ψ₂ψₙ₋₁²`. -/
theorem zsmul_consec_step {n : ℤ} {x y x₁ y₁ x₂ y₂ : k}
    (h : (E⁄k).toAffine.Nonsingular x y)
    (h₁ : (E⁄k).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E⁄k).toAffine.Nonsingular x₂ y₂)
    (heq₁ : (n - 1) • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some x₁ y₁ h₁)
    (heq₂ : (n - 2) • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some x₂ y₂ h₂)
    (hx₁ : x₁ * ((E⁄k).ψ (n - 1)).evalEval x y ^ 2 =
      ((E⁄k).φ (n - 1)).evalEval x y)
    (hx₂ : x₂ * ((E⁄k).ψ (n - 2)).evalEval x y ^ 2 =
      ((E⁄k).φ (n - 2)).evalEval x y)
    (ht₁ : (2 * y₁ + (E⁄k).a₁ * x₁ + (E⁄k).a₃) *
      ((E⁄k).ψ (n - 1)).evalEval x y ^ 4 =
      ((E⁄k).ψ (2 * (n - 1))).evalEval x y)
    (hψ₂ : ((E⁄k).ψ (n - 2)).evalEval x y ≠ 0)
    (hψ₁ : ((E⁄k).ψ (n - 1)).evalEval x y ≠ 0)
    (hs : ((E⁄k).ψ 2).evalEval x y ≠ 0)
    (hne : x₁ ≠ x) :
    ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
      n • (Affine.Point.some x y h : (E⁄k).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((E⁄k).ψ n).evalEval x y ^ 2 = ((E⁄k).φ n).evalEval x y ∧
      (2 * y' + (E⁄k).a₁ * x' + (E⁄k).a₃) * ((E⁄k).ψ n).evalEval x y ^ 4 =
        ((E⁄k).ψ (2 * n)).evalEval x y := by
  classical
  -- the sum `[n-1]P + P`
  obtain ⟨x₃, y₃, h₃, hadd, hX₃, hY₃⟩ := add_some_coords E h₁ h hne
  have hsum : n • (Affine.Point.some x y h : (E⁄k).Point) =
      Affine.Point.some x₃ y₃ h₃ := by
    rw [show n = (n - 1) + 1 from by ring, add_smul, one_smul, heq₁, hadd]
  -- the difference `[n-1]P + (-P) = [n-2]P`
  have hneg : (E⁄k).toAffine.Nonsingular x ((E⁄k).toAffine.negY x y) :=
    (Affine.nonsingular_neg ..).mpr h
  obtain ⟨x₄, y₄, h₄, hadd₄, hX₄, -⟩ := add_some_coords E h₁ hneg hne
  have hdiff : (Affine.Point.some x₄ y₄ h₄ : (E⁄k).Point) =
      Affine.Point.some x₂ y₂ h₂ := by
    rw [← hadd₄, ← Affine.Point.neg_some (h := h)]
    have hsub : (Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) -
        Affine.Point.some x y h = Affine.Point.some x₂ y₂ h₂ := by
      have hss : ((n - 1) - 1) • (Affine.Point.some x y h : (E⁄k).Point) =
          (n - 1) • (Affine.Point.some x y h : (E⁄k).Point) -
            (1 : ℤ) • (Affine.Point.some x y h : (E⁄k).Point) :=
        sub_smul _ _ _
      rw [one_smul, heq₁, show n - 1 - 1 = n - 2 from by ring, heq₂] at hss
      exact hss.symm
    rw [← hsub, sub_eq_add_neg]
  have hx₄ : x₄ = x₂ := by injection hdiff
  -- the ring core: `(x₂ - x₃)·dx² = t₁·s`
  have hcore : (x₂ - x₃) * (x₁ - x) ^ 2 =
      (2 * y₁ + (E⁄k).a₁ * x₁ + (E⁄k).a₃) *
        (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) := by
    have hX₄' := hX₄
    rw [hx₄, Affine.negY] at hX₄'
    linear_combination hX₄' - hX₃
  -- gap-1 at `n-1`: `(x - x₁)ψₙ₋₁² = ψₙψₙ₋₂`
  have hφ₁ := evalEval_φ_eq E (n - 1) h.1
  rw [show n - 1 + 1 = n from by ring, show n - 1 - 1 = n - 2 from by ring] at hφ₁
  have hgap : (x - x₁) * ((E⁄k).ψ (n - 1)).evalEval x y ^ 2 =
      ((E⁄k).ψ n).evalEval x y * ((E⁄k).ψ (n - 2)).evalEval x y := by
    linear_combination -hφ₁ - hx₁
  -- `φ`-differences at `n` and `n-2`, even recurrence at `n-1`
  have hφn := evalEval_φ_eq E n h.1
  have hφn2 := evalEval_φ_eq E (n - 2) h.1
  rw [show n - 2 + 1 = n - 1 from by ring,
    show n - 2 - 1 = n - 3 from by ring] at hφn2
  have heven := evalEval_ψ_even E (n - 1) h.1
  rw [show n - 1 - 1 = n - 2 from by ring, show n - 1 + 2 = n + 1 from by ring,
    show n - 1 - 2 = n - 3 from by ring, show n - 1 + 1 = n from by ring] at heven
  have hψ₂v := evalEval_ψ_two E x y
  -- assemble, then cancel `ψₙ₋₂²`
  have h1 : (x₂ - x₃) *
      (((E⁄k).ψ n).evalEval x y * ((E⁄k).ψ (n - 2)).evalEval x y) ^ 2 =
      (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) *
        ((E⁄k).ψ (2 * (n - 1))).evalEval x y := by
    linear_combination ((E⁄k).ψ (n - 1)).evalEval x y ^ 4 * hcore +
      (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) * ht₁ +
      (x₃ - x₂) * ((x - x₁) * ((E⁄k).ψ (n - 1)).evalEval x y ^ 2 +
        ((E⁄k).ψ n).evalEval x y * ((E⁄k).ψ (n - 2)).evalEval x y) * hgap
  have h2 : ((E⁄k).φ n).evalEval x y * ((E⁄k).ψ (n - 2)).evalEval x y ^ 2 =
      ((E⁄k).φ (n - 2)).evalEval x y * ((E⁄k).ψ n).evalEval x y ^ 2 -
        (2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) *
          ((E⁄k).ψ (2 * (n - 1))).evalEval x y := by
    linear_combination ((E⁄k).ψ (n - 2)).evalEval x y ^ 2 * hφn -
      ((E⁄k).ψ n).evalEval x y ^ 2 * hφn2 + heven -
      ((E⁄k).ψ (2 * (n - 1))).evalEval x y * hψ₂v
  have hmain : (x₃ * ((E⁄k).ψ n).evalEval x y ^ 2 - ((E⁄k).φ n).evalEval x y) *
      ((E⁄k).ψ (n - 2)).evalEval x y ^ 2 = 0 := by
    linear_combination -h1 - h2 + ((E⁄k).ψ n).evalEval x y ^ 2 * hx₂
  have hxf : x₃ * ((E⁄k).ψ n).evalEval x y ^ 2 = ((E⁄k).φ n).evalEval x y := by
    rcases mul_eq_zero.mp hmain with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h0) hψ₂
  -- the tracking output `t₃ψₙ⁴ = ψ₂ₙ`: gap-1 at `n`, even recurrence
  -- at `n`, the sum-companion recurrence, the trace identity; then
  -- cancel `ψ₂ψₙ₋₁²`
  have hgapn : (x - x₃) * ((E⁄k).ψ n).evalEval x y ^ 2 =
      ((E⁄k).ψ (n + 1)).evalEval x y * ((E⁄k).ψ (n - 1)).evalEval x y := by
    linear_combination -hφn - hxf
  have hevenn := evalEval_ψ_even E n h.1
  have hstar := evalEval_ψ_sum E n h.1
  have hP2 := eval_Ψ₂Sq_eq_sq E h.1
  have hT4 := two_point_trace_identity E h₁.1 h.1 hX₃ hY₃ hne
  rw [evalEval_ψ_two] at hs
  have hfinal : ((2 * y₃ + (E⁄k).a₁ * x₃ + (E⁄k).a₃) *
        ((E⁄k).ψ n).evalEval x y ^ 4 - ((E⁄k).ψ (2 * n)).evalEval x y) *
      ((2 * y + (E⁄k).a₁ * x + (E⁄k).a₃) *
        ((E⁄k).ψ (n - 1)).evalEval x y ^ 2) = 0 := by
    linear_combination
      (-(((E⁄k).ψ (n - 1)).evalEval x y ^ 2)) * hevenn +
      (((E⁄k).ψ (n - 1)).evalEval x y ^ 2 *
        ((E⁄k).ψ (2 * n)).evalEval x y) * hψ₂v +
      (-(((E⁄k).ψ n).evalEval x y *
        ((E⁄k).ψ (n - 1)).evalEval x y ^ 2)) * hstar +
      (((E⁄k).ψ n).evalEval x y ^ 4 *
        ((E⁄k).ψ (n - 1)).evalEval x y ^ 2) * hP2 +
      (((E⁄k).ψ (n - 1)).evalEval x y ^ 2 * ((E⁄k).ψ n).evalEval x y ^ 2 *
          (6 * x ^ 2 + (E⁄k).b₂ * x + (E⁄k).b₄) -
        2 * ((E⁄k).ψ n).evalEval x y * ((E⁄k).ψ (n - 2)).evalEval x y *
          (((E⁄k).ψ (n - 1)).evalEval x y * ((E⁄k).ψ (n + 1)).evalEval x y +
            (x - x₃) * ((E⁄k).ψ n).evalEval x y ^ 2)) * hgapn +
      (-(2 * ((E⁄k).ψ n).evalEval x y ^ 4 * (x - x₃) ^ 2)) * hgap +
      (((E⁄k).ψ n).evalEval x y ^ 4 *
        ((E⁄k).ψ (n - 1)).evalEval x y ^ 2) * hT4
  refine ⟨x₃, y₃, h₃, hsum, hxf, ?_⟩
  rcases mul_eq_zero.mp hfinal with h0 | h0
  · exact sub_eq_zero.mp h0
  · rcases mul_eq_zero.mp h0 with h0' | h0'
    · exact absurd h0' hs
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h0') hψ₁
set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [DecidableEq k] in
/-- **The symmetric addition identity** (PROVEN 2026-07-17): for two
curve points, the sum of the `x`-coordinates of `Q₁ + Q₂` and
`Q₁ - Q₂` satisfies
`(x₁-x₂)²(2x₂ - x₃ - x₄) = 2x₂³ - 6x₁x₂² - b₂x₁x₂ - b₄(x₁+x₂) - b₆`
(certificate: cofactors `-2, -2` on the two curve equations), where
`x₃, x₄` are given by the sum/difference secant expressions. -/
theorem sum_diff_X_identity {x₁ y₁ x₂ y₂ x₃ x₄ : k}
    (h₁ : (E⁄k).toAffine.Equation x₁ y₁)
    (h₂ : (E⁄k).toAffine.Equation x₂ y₂)
    (hX₃ : x₃ * (x₁ - x₂) ^ 2 = (y₁ - y₂) ^ 2 +
      (E⁄k).a₁ * (y₁ - y₂) * (x₁ - x₂) -
      ((E⁄k).a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2)
    (hX₄ : x₄ * (x₁ - x₂) ^ 2 = (y₁ + y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃) ^ 2 +
      (E⁄k).a₁ * (y₁ + y₂ + (E⁄k).a₁ * x₂ + (E⁄k).a₃) * (x₁ - x₂) -
      ((E⁄k).a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) :
    (x₁ - x₂) ^ 2 * (2 * x₂ - x₃ - x₄) =
      2 * x₂ ^ 3 - 6 * x₁ * x₂ ^ 2 - (E⁄k).b₂ * x₁ * x₂ -
        (E⁄k).b₄ * (x₁ + x₂) - (E⁄k).b₆ := by
  have heq₁ := (Affine.equation_iff x₁ y₁).mp h₁
  have heq₂ := (Affine.equation_iff x₂ y₂).mp h₂
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (-(1 : k)) * hX₃ + (-(1 : k)) * hX₄ +
    (-2 : k) * heq₁ + (-2 : k) * heq₂

set_option warn.sorry false in
/-- (Sorry node — **the multiplication-by-`n` formula**, Washington
*Elliptic curves* Theorem 3.6.) For `n > 0` and an affine point
`P = (x, y)`: (a) if `ψₙ(x, y) = 0` then `n • P = 0`; (b) if
`ψₙ(x, y) ≠ 0` then `n • P` is affine with `x' ⬝ ψₙ² = φₙ(x, y)`.
To be proven by strong induction: steps `[2m+1]P = [m+1]P + [m]P` and
`[2m]P = [m+1]P + [m-1]P` via `add_some_coords`, secant denominators
from `x_sub_gap_one`/`x_sub_gap_two`, collision branches via
`smul_collision`, `y`-data pinned by `two_point_cross_identity` (whose
`(1, j)`-instances solve for the `ψ₂`-values `2yⱼ + a₁xⱼ + a₃` in
closed form — no tracking component is carried), certificates with
unit cofactors (see `scripts/division_polynomial_certificates.py`),
base cases `zsmul_some_aux_one`/`zsmul_some_aux_two`, and the
2-torsion branch (`ψ₂(x,y) = 0`) seeded by `Res(Ψ₂Sq, Ψ₃) = -Δ²`. -/
theorem zsmul_some_aux (n : ℤ) (hn : 0 < n) {x y : k}
    (h : (E⁄k).toAffine.Nonsingular x y) :
    (((E⁄k).ψ n).evalEval x y = 0 →
      n • (Affine.Point.some x y h : (E⁄k).Point) = 0) ∧
    (((E⁄k).ψ n).evalEval x y ≠ 0 →
      ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
        n • (Affine.Point.some x y h : (E⁄k).Point) =
          Affine.Point.some x' y' h' ∧
        x' * ((E⁄k).ψ n).evalEval x y ^ 2 = ((E⁄k).φ n).evalEval x y) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **The division-polynomial torsion dictionary** (DERIVED 2026-07-17
from the multiplication formula `zsmul_some_aux`): an affine point
`P = (x, y)` satisfies `n • P = 0` precisely when its `x`-coordinate
is a root of the division polynomial `ΨSq n`. The bivariate/univariate
translation is `ψₙ(x,y)² = ΨSqₙ(x)` on the curve (`evalEval_Ψ_sq`),
and negative `n` reduces to positive `n` by `ΨSq_neg` and
`neg_smul`. -/
theorem smul_some_eq_zero_iff {n : ℤ} (hn : n ≠ 0)
    {x y : k} (h : (E⁄k).toAffine.Nonsingular x y) :
    (n • (Affine.Point.some x y h : (E⁄k).Point) = 0) ↔
      ((E⁄k).ΨSq n).eval x = 0 := by
  classical
  -- the bivariate/univariate translation on the curve
  have hbridge : ∀ m : ℤ, ((E⁄k).ψ m).evalEval x y = 0 ↔
      ((E⁄k).ΨSq m).eval x = 0 := by
    intro m
    rw [← WeierstrassCurve.evalEval_Ψ_sq m h.1, ← WeierstrassCurve.evalEval_ψ m h.1,
      pow_eq_zero_iff two_ne_zero]
  -- reduce to positive `n`
  rcases hn.lt_or_gt with hneg | hpos
  · have hpos' : 0 < -n := by omega
    have := zsmul_some_aux E (-n) hpos' h
    rw [show (n • (Affine.Point.some x y h : (E⁄k).Point) = 0) ↔
        ((-n) • (Affine.Point.some x y h : (E⁄k).Point) = 0) from by
      rw [neg_smul, neg_eq_zero],
      show ((E⁄k).ΨSq n).eval x = ((E⁄k).ΨSq (-n)).eval x from by
        rw [WeierstrassCurve.ΨSq_neg]]
    constructor
    · intro h0
      by_contra hΨ
      obtain ⟨x', y', h', heq, -⟩ := this.2 fun hz => hΨ ((hbridge _).mp hz)
      rw [h0] at heq
      exact nomatch heq.symm.trans
        (show (0 : (E⁄k).Point) = Affine.Point.zero from rfl)
    · intro hΨ
      exact this.1 ((hbridge _).mpr hΨ)
  · have := zsmul_some_aux E n hpos h
    constructor
    · intro h0
      by_contra hΨ
      obtain ⟨x', y', h', heq, -⟩ := this.2 fun hz => hΨ ((hbridge _).mp hz)
      rw [h0] at heq
      exact nomatch heq.symm.trans
        (show (0 : (E⁄k).Point) = Affine.Point.zero from rfl)
    · intro hΨ
      exact this.1 ((hbridge _).mpr hΨ)

set_option backward.isDefEq.respectTransparency false in
/-- **The multiplication-by-`n` `x`-coordinate formula** (DERIVED
2026-07-17 from `zsmul_some_aux`): if `P = (x, y)` is an affine point
with `ΨSq n` not vanishing at `x`, then `n • P` is an affine point
whose `x`-coordinate `x'` satisfies `x' ⬝ ΨSq n (x) = Φ n (x)` — the
classical `x([n]P) = Φₙ(x)/ψₙ²(x)`, in multiplied-out form. Negative
`n` reduces to positive `n` (`x(-Q) = x(Q)` and the division
polynomials are even/odd appropriately). -/
theorem exists_smul_some_eq {n : ℤ} (hn : n ≠ 0)
    {x y : k} (h : (E⁄k).toAffine.Nonsingular x y)
    (hΨ : ((E⁄k).ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
      n • (Affine.Point.some x y h : (E⁄k).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((E⁄k).ΨSq n).eval x = ((E⁄k).Φ n).eval x := by
  classical
  have hbridgeSq : ∀ m : ℤ, ((E⁄k).ψ m).evalEval x y ^ 2 =
      ((E⁄k).ΨSq m).eval x := by
    intro m
    rw [← WeierstrassCurve.evalEval_Ψ_sq m h.1, WeierstrassCurve.evalEval_ψ m h.1]
  have hbridgeφ : ((E⁄k).φ n).evalEval x y = ((E⁄k).Φ n).eval x :=
    WeierstrassCurve.evalEval_φ n h.1
  rcases hn.lt_or_gt with hneg | hpos
  · -- negative `n`: apply the formula at `-n` and negate the point
    have hpos' : 0 < -n := by omega
    have hΨ' : ((E⁄k).ψ (-n)).evalEval x y ≠ 0 := by
      intro hz
      apply hΨ
      rw [← WeierstrassCurve.ΨSq_neg, ← hbridgeSq, hz]
      ring
    obtain ⟨x', y', h', heq, hx'⟩ := (zsmul_some_aux E (-n) hpos' h).2 hΨ'
    refine ⟨x', (E⁄k).toAffine.negY x' y',
      (Affine.nonsingular_neg ..).mpr h', ?_, ?_⟩
    · have : n • (Affine.Point.some x y h : (E⁄k).Point) =
          -((-n) • (Affine.Point.some x y h : (E⁄k).Point)) := by
        rw [← neg_smul, neg_neg]
      rw [this, heq, Affine.Point.neg_some]
    · have hΨeq : ((E⁄k).ΨSq n).eval x = ((E⁄k).ΨSq (-n)).eval x := by
        rw [WeierstrassCurve.ΨSq_neg]
      have hΦeq : ((E⁄k).Φ n).eval x = ((E⁄k).Φ (-n)).eval x := by
        rw [WeierstrassCurve.Φ_neg]
      rw [hΨeq, hΦeq, ← hbridgeSq,
        ← WeierstrassCurve.evalEval_φ (-n) h.1]
      exact hx'
  · obtain ⟨x', y', h', heq, hx'⟩ := (zsmul_some_aux E n hpos h).2
      (fun hz => hΨ (by rw [← hbridgeSq, hz]; ring))
    exact ⟨x', y', h', heq, by rw [← hbridgeSq, ← hbridgeφ]; exact hx'⟩

set_option warn.sorry false in
/-- **Rational points in the multiplication fibres** (sorry node): over
a separably closed field, every fibre of the `x`-coordinate of the
multiplication-by-`n` map contains a rational point — there is a
nonsingular point `(x₀, y₀)` of the curve with `Φ n (x₀) = ξ ⬝ ΨSq n
(x₀)`. This is where separability of the multiplication-by-`n` isogeny
enters (`[n]` is étale for `(n : k) ≠ 0`, so its fibres, cut out by
`Φ n - ξ ⬝ ΨSq n` on the `x`-line, acquire points over a separably
closed field). -/
theorem exists_point_x_smul [IsSepClosed k] {n : ℤ} (hn : n ≠ 0)
    (hnk : (n : k) ≠ 0) (ξ : k) :
    ∃ (x₀ y₀ : k) (h : (E⁄k).toAffine.Nonsingular x₀ y₀),
      ((E⁄k).Φ n).eval x₀ = ξ * ((E⁄k).ΨSq n).eval x₀ :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Divisibility of the points group** (DERIVED 2026-07-17 from the
three division-polynomial nodes above): over a separably closed field,
multiplication by `n` with `(n : k) ≠ 0` is surjective on the points of
an elliptic curve. Given a target affine point `(ξ, η)`, the fibre node
provides a curve point `(x₀, y₀)` with `Φ n (x₀) = ξ ⬝ ΨSq n (x₀)`;
`ΨSq n (x₀) ≠ 0` by the Bézout identity `isCoprime_Φ_ΨSq` (a common
root would contradict `F ⬝ Φ + G ⬝ ΨSq = 1`), so the formula node
computes `n • (x₀, y₀)` as an affine point with `x`-coordinate `ξ`;
its `y`-coordinate is `η` or `negY ξ η`, and in the latter case
negating the preimage fixes it. -/
theorem smul_surjective [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Function.Surjective (fun P : (E⁄k).Point => (n : ℤ) • P) := by
  classical
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  have hnZ : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn0
  have hnk : (((n : ℤ) : ℤ) : k) ≠ 0 := by exact_mod_cast hn
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  -- points with equal coordinates are equal
  have hpoint : ∀ {x₁ y₁ x₂ y₂ : k} (h₁ : (E⁄k).toAffine.Nonsingular x₁ y₁)
      (h₂ : (E⁄k).toAffine.Nonsingular x₂ y₂), x₁ = x₂ → y₁ = y₂ →
      (Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) = Affine.Point.some x₂ y₂ h₂ := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hx hy
    subst hx
    subst hy
    rfl
  intro P₀
  cases P₀ with
  | zero => exact ⟨0, smul_zero _⟩
  | some ξ η h₀ =>
    obtain ⟨x₀, y₀, hns, hrel⟩ := exists_point_x_smul E hnZ (by exact_mod_cast hn) ξ
    -- `ΨSq n (x₀) ≠ 0` by coprimality
    have hΨ : ((E⁄k).ΨSq (n : ℤ)).eval x₀ ≠ 0 := by
      intro h0
      obtain ⟨F, G, hFG⟩ := WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k) hnZ
        (WeierstrassCurve.isUnit_Δ _)
      have hev := congrArg (Polynomial.eval x₀) hFG
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_one, hrel, h0] at hev
      simp at hev
    obtain ⟨x', y', h', hsmul, hx'⟩ :=
      exists_smul_some_eq E hnZ hns hΨ
    -- the `x`-coordinate of `n • (x₀, y₀)` is `ξ`
    have hx : x' = ξ := by
      rw [hrel] at hx'
      exact mul_right_cancel₀ hΨ hx'
    -- the `y`-coordinate is `η` or its negation
    rcases Affine.Y_eq_of_X_eq h'.1 h₀.1 hx with hy | hy
    · exact ⟨Affine.Point.some x₀ y₀ hns, hsmul.trans (hpoint h' h₀ hx hy)⟩
    · refine ⟨-(Affine.Point.some x₀ y₀ hns), ?_⟩
      show (n : ℤ) • (-(Affine.Point.some x₀ y₀ hns) : (E⁄k).Point) = _
      rw [smul_neg, hsmul, Affine.Point.neg_some]
      exact hpoint _ h₀ hx (by rw [hy, hx, Affine.negY_negY])

set_option warn.sorry false in
/-- **Separability of the division polynomial** (sorry node): for an
odd prime `p` invertible in `k`, the reduced `p`-division polynomial
`preΨ' p` (whose square is `ΨSq p`) is separable — its roots, the
`x`-coordinates of the nonzero `p`-torsion, are simple. Classically
via the discriminant companion of the resultant identity
(`disc(ψₚ) = ± pᵃ Δᵇ`). -/
theorem separable_preΨ' {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : k) ≠ 0) :
    ((E⁄k).preΨ' p).Separable :=
  sorry

-- (The coprimality of `Ψ₂Sq` and `preΨ' p` — classically the strong
-- divisibility `gcd(ψ₂, ψₚ) = ψ₁ = 1` — is DERIVED from the torsion
-- dictionary further below, after the `y`-fibre quadratic machinery.)

/-! ### The `y`-fibre above a fixed `x`-coordinate

For a fixed `x₀ : k`, the points of the curve with `x`-coordinate `x₀`
are cut out by the monic quadratic `yQuad x₀` in the `y`-variable. Its
key algebraic property is the characteristic-free Bézout identity
`(yQuad')² - 4 ⬝ yQuad = C (Ψ₂Sq x₀)`, which makes it separable
whenever `Ψ₂Sq (x₀) ≠ 0`. -/

/-- The monic quadratic cutting out the `y`-coordinates of the curve
points above `x₀`. -/
noncomputable def yQuad (x₀ : k) : Polynomial k :=
  Polynomial.X ^ 2 + Polynomial.C ((E⁄k).a₁ * x₀ + (E⁄k).a₃) * Polynomial.X -
    Polynomial.C (x₀ ^ 3 + (E⁄k).a₂ * x₀ ^ 2 + (E⁄k).a₄ * x₀ + (E⁄k).a₆)

omit [E.IsElliptic] [DecidableEq k] in
theorem yQuad_natDegree (x₀ : k) : (yQuad E x₀).natDegree = 2 := by
  rw [yQuad]
  compute_degree!

omit [E.IsElliptic] [DecidableEq k] in
theorem yQuad_ne_zero (x₀ : k) : yQuad E x₀ ≠ 0 := by
  intro h0
  have := yQuad_natDegree E x₀
  rw [h0] at this
  simp at this

omit [E.IsElliptic] [DecidableEq k] in
theorem eval_yQuad_eq_zero_iff_equation (x₀ y : k) :
    (yQuad E x₀).eval y = 0 ↔ (E⁄k).toAffine.Equation x₀ y := by
  rw [Affine.equation_iff, yQuad]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

omit [E.IsElliptic] [DecidableEq k] in
/-- The derivative of the `y`-fibre quadratic, evaluated. -/
theorem derivative_yQuad_eval (x₀ y : k) :
    (Polynomial.derivative (yQuad E x₀)).eval y =
      2 * y + ((E⁄k).a₁ * x₀ + (E⁄k).a₃) := by
  rw [yQuad]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_X_pow, Nat.cast_ofNat]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero, Polynomial.eval_one]
  ring

omit [E.IsElliptic] [DecidableEq k] in
/-- The characteristic-free discriminant identity for the `y`-fibre
quadratic: `(∂yQuad)² - 4 ⬝ yQuad` is the constant `Ψ₂Sq (x₀)`. -/
theorem derivative_yQuad_sq_sub (x₀ : k) :
    (Polynomial.derivative (yQuad E x₀)) ^ 2 - 4 * yQuad E x₀ =
      Polynomial.C (((E⁄k).Ψ₂Sq).eval x₀) := by
  have hval : ((E⁄k).Ψ₂Sq).eval x₀ =
      ((E⁄k).a₁ * x₀ + (E⁄k).a₃) ^ 2 +
        4 * (x₀ ^ 3 + (E⁄k).a₂ * x₀ ^ 2 + (E⁄k).a₄ * x₀ + (E⁄k).a₆) := by
    rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hder : Polynomial.derivative (yQuad E x₀) =
      Polynomial.C 2 * Polynomial.X +
        Polynomial.C ((E⁄k).a₁ * x₀ + (E⁄k).a₃) := by
    rw [yQuad]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_C,
      Polynomial.derivative_X, Polynomial.derivative_X_pow,
      Nat.cast_ofNat]
    ring
  rw [hder, hval, yQuad]
  simp only [map_ofNat, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]
  ring

omit [E.IsElliptic] [DecidableEq k] in
/-- The `y`-fibre quadratic is separable whenever `Ψ₂Sq (x₀) ≠ 0`
(uniformly in the characteristic, by the Bézout identity
`(1/D) ⬝ ∂Q ⬝ ∂Q + (-4/D) ⬝ Q = 1` from `derivative_yQuad_sq_sub`). -/
theorem yQuad_separable {x₀ : k} (hx₀ : ((E⁄k).Ψ₂Sq).eval x₀ ≠ 0) :
    (yQuad E x₀).Separable := by
  refine ⟨Polynomial.C (-4 / ((E⁄k).Ψ₂Sq).eval x₀),
    Polynomial.C (1 / ((E⁄k).Ψ₂Sq).eval x₀) *
      Polynomial.derivative (yQuad E x₀), ?_⟩
  have hkey := derivative_yQuad_sq_sub E x₀
  have hD : (1 / ((E⁄k).Ψ₂Sq).eval x₀) * (((E⁄k).Ψ₂Sq).eval x₀) = 1 :=
    one_div_mul_cancel hx₀
  calc Polynomial.C (-4 / ((E⁄k).Ψ₂Sq).eval x₀) * yQuad E x₀ +
        Polynomial.C (1 / ((E⁄k).Ψ₂Sq).eval x₀) *
          Polynomial.derivative (yQuad E x₀) * Polynomial.derivative (yQuad E x₀)
      = Polynomial.C (1 / ((E⁄k).Ψ₂Sq).eval x₀) *
          ((Polynomial.derivative (yQuad E x₀)) ^ 2 - 4 * yQuad E x₀) := by
        rw [neg_div, Polynomial.C_neg, div_eq_mul_one_div, mul_comm (4 : k),
          Polynomial.C_mul]
        simp only [map_ofNat]
        ring
    _ = 1 := by
        rw [hkey, ← Polynomial.C_mul, hD, Polynomial.C_1]

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] in
/-- **The `n = 2` case of the torsion dictionary** (PROVEN 2026-07-17,
the base case of the Washington Thm 3.6 induction): `2 • (x, y) = 0`
iff `Ψ₂Sq (x) = 0`. On the curve the discriminant identity specialises
to `Ψ₂Sq (x) = (2y + a₁x + a₃)²`, and `2 • P = 0` iff `P = -P` iff
`y` is `negY`-fixed iff `2y + a₁x + a₃ = 0`. -/
theorem two_smul_some_eq_zero_iff {x y : k}
    (h : (E⁄k).toAffine.Nonsingular x y) :
    ((2 : ℤ) • (Affine.Point.some x y h : (E⁄k).Point) = 0) ↔
      ((E⁄k).Ψ₂Sq).eval x = 0 := by
  classical
  have hΨval := eval_Ψ₂Sq_eq_sq E h.1
  constructor
  · intro h2
    rw [two_smul ℤ (Affine.Point.some x y h), add_eq_zero_iff_eq_neg,
      Affine.Point.neg_some] at h2
    have hy : y = (E⁄k).toAffine.negY x y := by
      have := h2
      injection this with h1 h2'
    rw [hΨval]
    have : 2 * y + ((E⁄k).a₁ * x + (E⁄k).a₃) = 0 := by
      rw [Affine.negY] at hy
      linear_combination hy
    rw [this]
    ring
  · intro hΨ
    rw [hΨval] at hΨ
    have h2y : 2 * y + ((E⁄k).a₁ * x + (E⁄k).a₃) = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp hΨ
    have hnegY : (E⁄k).toAffine.negY x y = y := by
      rw [Affine.negY]
      linear_combination -h2y
    rw [two_smul ℤ (Affine.Point.some x y h), add_eq_zero_iff_eq_neg,
      Affine.Point.neg_some]
    have : ∀ (y' : k) (h' : (E⁄k).toAffine.Nonsingular x y'), y = y' →
        (Affine.Point.some x y h : (E⁄k).Point) = Affine.Point.some x y' h' := by
      intro y' h' hy
      subst hy
      rfl
    exact this _ _ hnegY.symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`2`-torsion and `p`-torsion have disjoint `x`-coordinates**
(DERIVED 2026-07-17 from the torsion dictionary): for an odd prime `p`
invertible in `k`, the two-torsion polynomial `Ψ₂Sq` and the reduced
`p`-division polynomial `preΨ' p` are coprime — classically
`gcd(ψ₂, ψₚ) = ψ_{gcd(2,p)} = ψ₁ = 1`. A common root `α` over the
algebraic closure would carry a curve point `(α, y₀)` (any root `y₀`
of the `y`-fibre quadratic) that is `2`-torsion (by the discriminant
identity `(∂Q)² - 4Q = C (Ψ₂Sq α) = 0`, the derivative vanishes at
`y₀`, so `y₀` is `negY`-fixed) and `p`-torsion (by the dictionary),
hence trivial as `gcd(2, p) = 1` — contradicting that it is affine. -/
theorem isCoprime_Ψ₂Sq_preΨ' {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : k) ≠ 0) :
    IsCoprime ((E⁄k).Ψ₂Sq) ((E⁄k).preΨ' p) := by
  classical
  by_contra hnc
  rw [← EuclideanDomain.gcd_isUnit_iff] at hnc
  -- the would-be common divisor has a root over the algebraic closure
  have hpre0 : (E⁄k).preΨ' p ≠ 0 := by
    intro h0
    refine WeierstrassCurve.coeff_preΨ'_ne_zero (W := (E⁄k)) hpk ?_
    rw [h0, Polynomial.coeff_zero]
  have hg0 : EuclideanDomain.gcd ((E⁄k).Ψ₂Sq) ((E⁄k).preΨ' p) ≠ 0 := by
    intro h0
    exact hpre0 (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  have hgdeg : (EuclideanDomain.gcd ((E⁄k).Ψ₂Sq) ((E⁄k).preΨ' p)).degree ≠ 0 := by
    intro h0
    exact hnc (Polynomial.isUnit_iff_degree_eq_zero.mpr h0)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    ((EuclideanDomain.gcd ((E⁄k).Ψ₂Sq) ((E⁄k).preΨ' p)).map
      (algebraMap k (AlgebraicClosure k)))
    (by rwa [Polynomial.degree_map])
  have hα' := Polynomial.root_gcd_iff_root_left_right
    (ϕ := algebraMap k (AlgebraicClosure k)) (α := α) |>.mp
    (by rwa [Polynomial.eval₂_eq_eval_map])
  -- transfer the two vanishing statements to the base-changed curve
  haveI : (E.baseChange (AlgebraicClosure k)).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k (AlgebraicClosure k))).IsElliptic)
  have hmapself : ∀ (F : Type u) [inst : Field F] (q : Polynomial F),
      q.map (algebraMap F F) = q := by
    intro F _ q
    rw [show algebraMap F F = RingHom.id F from rfl, Polynomial.map_id]
  have hΨ₂α : (((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).Ψ₂Sq).eval α
      = 0 := by
    show ((((E.baseChange (AlgebraicClosure k)).map
      (algebraMap (AlgebraicClosure k) (AlgebraicClosure k))).Ψ₂Sq)).eval α = 0
    rw [WeierstrassCurve.map_Ψ₂Sq, hmapself]
    show (((E.map (algebraMap k (AlgebraicClosure k))).Ψ₂Sq)).eval α = 0
    rw [WeierstrassCurve.map_Ψ₂Sq]
    have h1 := hα'.1
    rw [Polynomial.eval₂_eq_eval_map,
      show (E⁄k).Ψ₂Sq = E.Ψ₂Sq from by
        show (E.map (algebraMap k k)).Ψ₂Sq = E.Ψ₂Sq
        rw [WeierstrassCurve.map_Ψ₂Sq, hmapself]] at h1
    exact h1
  have hpreα : (((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).preΨ' p).eval α
      = 0 := by
    show ((((E.baseChange (AlgebraicClosure k)).map
      (algebraMap (AlgebraicClosure k) (AlgebraicClosure k))).preΨ' p)).eval α = 0
    rw [WeierstrassCurve.map_preΨ', hmapself]
    show (((E.map (algebraMap k (AlgebraicClosure k))).preΨ' p)).eval α = 0
    rw [WeierstrassCurve.map_preΨ']
    have h1 := hα'.2
    rw [Polynomial.eval₂_eq_eval_map,
      show (E⁄k).preΨ' p = E.preΨ' p from by
        show (E.map (algebraMap k k)).preΨ' p = E.preΨ' p
        rw [WeierstrassCurve.map_preΨ', hmapself]] at h1
    exact h1
  -- a curve point above `α`
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
    (yQuad (E.baseChange (AlgebraicClosure k)) α)
    (by
      intro h0
      have := yQuad_natDegree (E.baseChange (AlgebraicClosure k)) α
      rw [Polynomial.degree_eq_natDegree
        (yQuad_ne_zero (E.baseChange (AlgebraicClosure k)) α), this] at h0
      exact two_ne_zero (by exact_mod_cast h0))
  have hy₀' : (yQuad (E.baseChange (AlgebraicClosure k)) α).eval y₀ = 0 := hy₀
  have heq : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).toAffine.Equation
      α y₀ := (eval_yQuad_eq_zero_iff_equation _ α y₀).mp hy₀'
  have hns : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).toAffine.Nonsingular
      α y₀ := by
    haveI : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).IsElliptic :=
      inferInstanceAs (((E.baseChange (AlgebraicClosure k)).map
        (algebraMap (AlgebraicClosure k) (AlgebraicClosure k))).IsElliptic)
    exact Affine.equation_iff_nonsingular.mp heq
  -- the point is `negY`-fixed: the derivative of the `y`-quadratic
  -- vanishes at `y₀`
  have h2y : 2 * y₀ + ((E.baseChange (AlgebraicClosure k)).a₁ * α +
      (E.baseChange (AlgebraicClosure k)).a₃) = 0 := by
    have hkey := congrArg (Polynomial.eval y₀)
      (derivative_yQuad_sq_sub (E.baseChange (AlgebraicClosure k)) α)
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, hΨ₂α, hy₀', mul_zero, sub_zero,
      derivative_yQuad_eval] at hkey
    exact pow_eq_zero_iff two_ne_zero |>.mp hkey
  have hnegY : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).toAffine.negY
      α y₀ = y₀ := by
    rw [Affine.negY]
    show -y₀ - ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).a₁ * α -
      ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).a₃ = y₀
    have ha₁ : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).a₁ =
        (E.baseChange (AlgebraicClosure k)).a₁ := rfl
    have ha₃ : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).a₃ =
        (E.baseChange (AlgebraicClosure k)).a₃ := rfl
    rw [ha₁, ha₃]
    linear_combination -h2y
  -- the point is `2`-torsion …
  have h2P : (2 : ℤ) • (Affine.Point.some α y₀ hns :
      ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).Point) = 0 := by
    rw [two_smul ℤ (Affine.Point.some α y₀ hns), add_eq_zero_iff_eq_neg,
      Affine.Point.neg_some]
    have : ∀ (y' : AlgebraicClosure k)
        (h' : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).toAffine.Nonsingular
          α y'), y₀ = y' →
        (Affine.Point.some α y₀ hns :
          ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).Point) =
          Affine.Point.some α y' h' := by
      intro y' h' hy
      subst hy
      rfl
    exact this _ _ hnegY.symm
  -- … and `p`-torsion, by the dictionary
  have hpP : ((p : ℕ) : ℤ) • (Affine.Point.some α y₀ hns :
      ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).Point) = 0 := by
    rw [smul_some_eq_zero_iff (E.baseChange (AlgebraicClosure k))
      (Int.natCast_ne_zero.mpr hp.ne_zero) hns]
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (Nat.not_even_iff_odd.mpr hodd),
      mul_one, Polynomial.eval_pow, pow_eq_zero_iff two_ne_zero]
    exact hpreα
  -- `gcd(2, p) = 1` kills the point, contradiction
  obtain ⟨m, hm⟩ := hodd
  have hP0 : (Affine.Point.some α y₀ hns :
      ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).Point) = 0 := by
    have h1 : (1 : ℤ) = ((p : ℕ) : ℤ) - 2 * m := by
      have : (p : ℤ) = 2 * m + 1 := by exact_mod_cast hm
      omega
    calc (Affine.Point.some α y₀ hns :
        ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).Point)
        = (1 : ℤ) • Affine.Point.some α y₀ hns := (one_smul _ _).symm
      _ = (((p : ℕ) : ℤ) - 2 * m) • Affine.Point.some α y₀ hns := by rw [← h1]
      _ = ((p : ℕ) : ℤ) • Affine.Point.some α y₀ hns -
          (m : ℤ) • ((2 : ℤ) • Affine.Point.some α y₀ hns) := by
          rw [sub_smul, smul_smul]
          norm_num [mul_comm]
      _ = 0 := by rw [hpP, h2P]; simp
  exact nomatch hP0.trans
    (show (0 : ((E.baseChange (AlgebraicClosure k))⁄(AlgebraicClosure k)).Point)
      = Affine.Point.zero from rfl)

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq k] in
/-- **Separability of the two-torsion polynomial** (PROVEN
2026-07-17): for `(2 : k) ≠ 0` the two-torsion cubic `Ψ₂Sq` is
separable — its discriminant is `16 Δ`, nonzero on an elliptic curve
(`twoTorsionPolynomial_discr_ne_zero_of_isElliptic`), so its roots
over the algebraic closure are distinct
(`Cubic.discr_ne_zero_iff_roots_nodup`) and separability descends
(`Polynomial.separable_map`). -/
theorem separable_Ψ₂Sq (h2 : (2 : k) ≠ 0) :
    ((E⁄k).Ψ₂Sq).Separable := by
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  have h4 : ((E⁄k).twoTorsionPolynomial).a ≠ 0 := by
    show (4 : k) ≠ 0
    intro h
    apply h2
    have h22 : (4 : k) = 2 * 2 := by norm_num
    rcases mul_eq_zero.mp (h22 ▸ h) with h' | h' <;> exact h'
  have hne : (E⁄k).twoTorsionPolynomial.toPoly.map
      (algebraMap k (AlgebraicClosure k)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap k (AlgebraicClosure k)).injective]
    intro h0
    exact h4 (by rw [show ((E⁄k).twoTorsionPolynomial).a =
      (E⁄k).twoTorsionPolynomial.toPoly.coeff 3 from
        Cubic.coeff_eq_a.symm, h0, Polynomial.coeff_zero])
  have hsplits : ((E⁄k).twoTorsionPolynomial.toPoly.map
      (algebraMap k (AlgebraicClosure k))).Splits :=
    IsAlgClosed.splits _
  have hnodup := (Cubic.discr_ne_zero_iff_roots_nodup
      (φ := algebraMap k (AlgebraicClosure k)) h4 hsplits).mp
    ((E⁄k).twoTorsionPolynomial_discr_ne_zero_of_isElliptic
      (isUnit_iff_ne_zero.mpr h2))
  rw [Cubic.map_roots] at hnodup
  rw [WeierstrassCurve.Ψ₂Sq_eq,
    ← Polynomial.separable_map (algebraMap k (AlgebraicClosure k)),
    ← Polynomial.nodup_roots_iff_of_splits hne hsplits]
  exact hnodup

/-- The points of the curve lying above a fixed `x`-coordinate, as a
finset (the image of the roots of the `y`-fibre quadratic). -/
noncomputable def pointsAt (x₀ : k) : Finset ((E⁄k).Point) :=
  ((yQuad E x₀).roots.toFinset).attach.image fun y =>
    Affine.Point.some x₀ y.1 <| by
      haveI : (E⁄k).IsElliptic :=
        inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
      exact (E⁄k).toAffine.equation_iff_nonsingular.mp
        ((eval_yQuad_eq_zero_iff_equation E x₀ y.1).mp
          (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp y.2)).2)

theorem mem_pointsAt_iff {x₀ : k} {P : (E⁄k).Point} :
    P ∈ pointsAt E x₀ ↔ ∃ (y : k) (h : (E⁄k).toAffine.Nonsingular x₀ y),
      P = Affine.Point.some x₀ y h := by
  constructor
  · intro hP
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨y.1, _, rfl⟩
  · rintro ⟨y, h, rfl⟩
    refine Finset.mem_image.mpr ⟨⟨y, ?_⟩, Finset.mem_attach _ _, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (yQuad_ne_zero E x₀),
      Polynomial.IsRoot, eval_yQuad_eq_zero_iff_equation]
    exact h.1

theorem pointsAt_card (x₀ : k) :
    (pointsAt E x₀).card = (yQuad E x₀).roots.toFinset.card := by
  rw [pointsAt, Finset.card_image_of_injective _ ?_, Finset.card_attach]
  intro y₁ y₂ hy
  simp only [Affine.Point.some.injEq] at hy
  exact Subtype.ext hy.2

theorem zero_notMem_pointsAt (x₀ : k) : (0 : (E⁄k).Point) ∉ pointsAt E x₀ := by
  intro h0
  obtain ⟨y, h, hP⟩ := (mem_pointsAt_iff E).mp h0
  rw [show (0 : (E⁄k).Point) = Affine.Point.zero from rfl] at hP
  exact nomatch hP

set_option backward.isDefEq.respectTransparency false in
/-- **The prime-level count** (DERIVED 2026-07-17 from the dictionary
node and the three division-polynomial separability/coprimality
nodes): for a prime `p` with `(p : k) ≠ 0`, the `p`-torsion of an
elliptic curve over a separably closed field has exactly `p²`
elements. The nonzero `p`-torsion is fibred over the roots of the
relevant division polynomial (`preΨ' p` for odd `p`, with two points
per root since the `y`-fibre quadratic is separable there by the
coprimality node; `Ψ₂Sq` for `p = 2`, with one point per root since
the quadratic is then a square), and the separability nodes count the
roots: `2 ⬝ (p² - 1)/2` resp. `1 ⬝ 3` of them. -/
theorem prime_torsion_card [IsSepClosed k] {p : ℕ} (hp : p.Prime)
    (hchar : (p : k) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (E⁄k).Point p) = p ^ 2 := by
  classical
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  have hpZ : ((p : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hpkZ : (((p : ℕ) : ℤ) : k) ≠ 0 := by exact_mod_cast hchar
  -- the counting skeleton, shared between `p = 2` and odd `p`:
  -- a separable polynomial `g` whose roots are the torsion
  -- `x`-coordinates, and a uniform `y`-fibre count `m`
  have key : ∀ (g : Polynomial k) (m : ℕ), g.Separable →
      (∀ x₀ y (h : (E⁄k).toAffine.Nonsingular x₀ y),
        ((p : ℤ) • (Affine.Point.some x₀ y h : (E⁄k).Point) = 0 ↔
          g.eval x₀ = 0)) →
      (∀ x₀, g.eval x₀ = 0 → (yQuad E x₀).roots.toFinset.card = m) →
      Nat.card (Submodule.torsionBy ℤ (E⁄k).Point p) =
        1 + m * g.natDegree := by
    intro g m hgsep hdict hfib
    have hg0 : g ≠ 0 := hgsep.ne_zero
    -- the root finset of `g`
    have hgroots : g.roots.toFinset.card = g.natDegree := by
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hgsep)]
      exact (IsSepClosed.splits_of_separable g hgsep).natDegree_eq_card_roots.symm
    -- the finset of nonzero `p`-torsion points
    set F : Finset ((E⁄k).Point) := g.roots.toFinset.biUnion (pointsAt E)
      with hF
    have hdisj : ∀ x₁ ∈ g.roots.toFinset, ∀ x₂ ∈ g.roots.toFinset, x₁ ≠ x₂ →
        Disjoint (pointsAt E x₁) (pointsAt E x₂) := by
      intro x₁ hx₁ x₂ hx₂ hne
      refine Finset.disjoint_left.mpr fun P hP₁ hP₂ => ?_
      obtain ⟨y₁, h₁, rfl⟩ := (mem_pointsAt_iff E).mp hP₁
      obtain ⟨y₂, h₂, hP⟩ := (mem_pointsAt_iff E).mp hP₂
      simp only [Affine.Point.some.injEq] at hP
      exact hne hP.1
    have hFcard : F.card = m * g.natDegree := by
      rw [hF, Finset.card_biUnion hdisj,
        Finset.sum_congr rfl fun x₀ hx₀ => (pointsAt_card E x₀).trans
          (hfib x₀ (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx₀)).2),
        Finset.sum_const, smul_eq_mul, hgroots, mul_comm]
    -- the torsion submodule is `{0} ∪ F` as a set
    have hset : (Submodule.torsionBy ℤ (E⁄k).Point p : Set ((E⁄k).Point)) =
        ↑(insert (0 : (E⁄k).Point) F) := by
      ext P
      simp only [SetLike.mem_coe, Submodule.mem_torsionBy_iff,
        Finset.coe_insert, Set.mem_insert_iff]
      constructor
      · intro hP
        cases P with
        | zero => exact Or.inl rfl
        | some x y h =>
          refine Or.inr (Finset.mem_biUnion.mpr ⟨x, ?_,
            (mem_pointsAt_iff E).mpr ⟨y, h, rfl⟩⟩)
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
          exact (hdict x y h).mp hP
      · rintro (rfl | hP)
        · exact smul_zero _
        · obtain ⟨x₀, hx₀, hPx⟩ := Finset.mem_biUnion.mp hP
          obtain ⟨y, h, rfl⟩ := (mem_pointsAt_iff E).mp hPx
          exact (hdict x₀ y h).mpr
            (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx₀)).2
    -- count
    calc Nat.card (Submodule.torsionBy ℤ (E⁄k).Point p)
        = Set.ncard (Submodule.torsionBy ℤ (E⁄k).Point p :
            Set ((E⁄k).Point)) := (Nat.card_coe_set_eq _)
      _ = (insert (0 : (E⁄k).Point) F).card := by
          rw [hset, Set.ncard_coe_finset]
      _ = 1 + m * g.natDegree := by
          rw [Finset.card_insert_of_notMem, hFcard, add_comm]
          intro h0
          obtain ⟨x₀, -, hPx⟩ := Finset.mem_biUnion.mp h0
          exact zero_notMem_pointsAt E x₀ hPx
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- `p = 2`: one point per root of the two-torsion cubic
    have h2 : (2 : k) ≠ 0 := by exact_mod_cast hchar
    have hdeg : ((E⁄k).Ψ₂Sq).natDegree = 3 := by
      have h4 : (4 : k) ≠ 0 := by
        intro h
        exact h2 (by
          have : (4 : k) = 2 * 2 := by norm_num
          rcases mul_eq_zero.mp (this ▸ h) with h' | h' <;> exact h')
      rw [WeierstrassCurve.Ψ₂Sq]
      compute_degree!
    rw [key ((E⁄k).Ψ₂Sq) 1 (separable_Ψ₂Sq E h2) ?_ ?_, hdeg]
    · norm_num
    · -- the dictionary at `2` is `ΨSq 2 = Ψ₂Sq`
      intro x₀ y h
      have := smul_some_eq_zero_iff E (by norm_num : (2 : ℤ) ≠ 0) h
      rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl, this, WeierstrassCurve.ΨSq_two]
    · -- one `y` above each two-torsion `x`-coordinate
      intro x₀ hx₀
      have hval : ((E⁄k).a₁ * x₀ + (E⁄k).a₃) ^ 2 +
          4 * (x₀ ^ 3 + (E⁄k).a₂ * x₀ ^ 2 + (E⁄k).a₄ * x₀ + (E⁄k).a₆) = 0 := by
        have hv : ((E⁄k).Ψ₂Sq).eval x₀ =
            ((E⁄k).a₁ * x₀ + (E⁄k).a₃) ^ 2 +
              4 * (x₀ ^ 3 + (E⁄k).a₂ * x₀ ^ 2 + (E⁄k).a₄ * x₀ + (E⁄k).a₆) := by
          rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
            WeierstrassCurve.b₆]
          simp only [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
          ring
        rw [← hv, hx₀]
      -- the unique `y`-root is `-(c/2)`
      have hroot : ∀ y : k, (yQuad E x₀).eval y = 0 ↔
          y = -(((E⁄k).a₁ * x₀ + (E⁄k).a₃) / 2) := by
        intro y
        rw [yQuad]
        simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        constructor
        · intro hy
          have hsq : (y + ((E⁄k).a₁ * x₀ + (E⁄k).a₃) / 2) ^ 2 = 0 := by
            field_simp
            linear_combination (4 : k) * hy + hval
          have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
          exact eq_neg_of_add_eq_zero_left this
        · rintro rfl
          field_simp
          linear_combination -hval
      rw [show (yQuad E x₀).roots.toFinset =
          {-(((E⁄k).a₁ * x₀ + (E⁄k).a₃) / 2)} from ?_, Finset.card_singleton]
      ext y
      rw [Multiset.mem_toFinset, Finset.mem_singleton,
        Polynomial.mem_roots (yQuad_ne_zero E x₀), Polynomial.IsRoot, hroot]
  · -- odd `p`: two points per root of `preΨ' p`
    have hnoteven : ¬ Even p := Nat.not_even_iff_odd.mpr hodd
    have hdeg : ((E⁄k).preΨ' p).natDegree = (p ^ 2 - 1) / 2 := by
      rw [WeierstrassCurve.natDegree_preΨ' (W := (E⁄k)) hchar, if_neg hnoteven]
    -- `ΨSq p` vanishing is `preΨ' p` vanishing (odd `p`)
    have hΨodd : ∀ x₀ : k, ((E⁄k).ΨSq ((p : ℕ) : ℤ)).eval x₀ = 0 ↔
        ((E⁄k).preΨ' p).eval x₀ = 0 := by
      intro x₀
      rw [WeierstrassCurve.ΨSq_ofNat, if_neg hnoteven, mul_one,
        Polynomial.eval_pow, pow_eq_zero_iff two_ne_zero]
    rw [key ((E⁄k).preΨ' p) 2 (separable_preΨ' E hp hodd hchar) ?_ ?_, hdeg]
    · -- `1 + 2 ⬝ (p² - 1)/2 = p²`
      obtain ⟨t, ht⟩ := hodd.pow (n := 2)
      omega
    · -- the dictionary
      intro x₀ y h
      rw [smul_some_eq_zero_iff E hpZ h, hΨodd]
    · -- two `y`s above each root of `preΨ' p`
      intro x₀ hx₀
      have hΨ₂ : ((E⁄k).Ψ₂Sq).eval x₀ ≠ 0 := by
        intro h0
        obtain ⟨F, G, hFG⟩ := isCoprime_Ψ₂Sq_preΨ' E hp hodd hchar
        have hev := congrArg (Polynomial.eval x₀) hFG
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
          Polynomial.eval_one, h0, hx₀] at hev
        simp at hev
      have hsep := yQuad_separable E hΨ₂
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
        ← (IsSepClosed.splits_of_separable _ hsep).natDegree_eq_card_roots,
        yQuad_natDegree]

/-- **The torsion count** (PROVEN from the nodes above):
`#E(k̄)[n] = n²` for `(n : k) ≠ 0`, by strong induction peeling off the
minimal prime factor. -/
theorem card_torsionBy [IsSepClosed k] :
    ∀ n : ℕ, (n : k) ≠ 0 →
      Nat.card (Submodule.torsionBy ℤ (E⁄k).Point n) = n ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rcases eq_or_ne n 1 with rfl | hn1
    · -- `E[1]` is trivial
      have hbot : Submodule.torsionBy ℤ (E⁄k).Point ((1 : ℕ) : ℤ) = ⊥ := by
        rw [Nat.cast_one]
        exact Submodule.torsionBy_one
      rw [hbot]
      simp
    · -- peel off the minimal prime factor
      have hp : n.minFac.Prime := Nat.minFac_prime hn1
      obtain ⟨m, hm⟩ := n.minFac_dvd
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hm
        exact hn0 hm
      have hmn : m < n := by
        have h2 := hp.two_le
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        rw [hm]
        nlinarith
      have hpk : (n.minFac : k) ≠ 0 := by
        intro h
        apply hn
        rw [hm, Nat.cast_mul, h, zero_mul]
      have hmk : (m : k) ≠ 0 := by
        intro h
        apply hn
        rw [hm, Nat.cast_mul, h, mul_zero]
      have hcast : ((m : ℤ)) * ((n.minFac : ℤ)) = ((n : ℤ)) := by
        exact_mod_cast (by rw [mul_comm]; exact hm.symm : m * n.minFac = n)
      -- multiplication by the prime, restricted to the torsion tower
      have hwd : ∀ P : Submodule.torsionBy ℤ (E⁄k).Point n,
          ((n.minFac : ℤ) • (P : (E⁄k).Point)) ∈
            Submodule.torsionBy ℤ (E⁄k).Point m := by
        intro P
        have hP := (Submodule.mem_torsionBy_iff _ _).mp P.2
        rw [Submodule.mem_torsionBy_iff, smul_smul, hcast]
        exact hP
      set f : Submodule.torsionBy ℤ (E⁄k).Point n →+
          Submodule.torsionBy ℤ (E⁄k).Point m :=
        { toFun := fun P => ⟨(n.minFac : ℤ) • (P : (E⁄k).Point), hwd P⟩
          map_zero' := by
            apply Subtype.ext
            show (n.minFac : ℤ) •
              ((0 : Submodule.torsionBy ℤ (E⁄k).Point n) : (E⁄k).Point) = 0
            rw [ZeroMemClass.coe_zero, smul_zero]
          map_add' := fun P Q => by
            apply Subtype.ext
            show (n.minFac : ℤ) • ((P + Q :
              Submodule.torsionBy ℤ (E⁄k).Point n) : (E⁄k).Point) = _
            rw [Submodule.coe_add, smul_add]
            rfl } with hf
      have hfsurj : Function.Surjective f := by
        rintro ⟨Q, hQ⟩
        obtain ⟨P, hP⟩ := smul_surjective E hpk Q
        have hP' : (n.minFac : ℤ) • P = Q := hP
        have hPn : P ∈ Submodule.torsionBy ℤ (E⁄k).Point n := by
          rw [Submodule.mem_torsionBy_iff, ← hcast, ← smul_smul, hP']
          exact (Submodule.mem_torsionBy_iff _ _).mp hQ
        exact ⟨⟨P, hPn⟩, Subtype.ext hP'⟩
      -- the kernel is the `p`-torsion
      have hple : Submodule.torsionBy ℤ (E⁄k).Point (n.minFac) ≤
          Submodule.torsionBy ℤ (E⁄k).Point n :=
        Submodule.torsionBy_le_torsionBy_of_dvd _ _
          (Int.natCast_dvd_natCast.mpr n.minFac_dvd)
      have hkerEquiv : Submodule.torsionBy ℤ (E⁄k).Point (n.minFac) ≃
          f.ker := by
        refine ⟨fun P => ⟨⟨P.1, hple P.2⟩, ?_⟩, fun x => ⟨x.1.1, ?_⟩,
          fun P => ?_, fun x => ?_⟩
        · rw [AddMonoidHom.mem_ker]
          ext
          exact (Submodule.mem_torsionBy_iff _ _).mp P.2
        · have hx := AddMonoidHom.mem_ker.mp x.2
          rw [Submodule.mem_torsionBy_iff]
          exact congrArg Subtype.val hx
        · rfl
        · rfl
      have hker : Nat.card f.ker = n.minFac ^ 2 := by
        rw [← Nat.card_congr hkerEquiv]
        exact prime_torsion_card E hp hpk
      -- Lagrange plus the first isomorphism theorem
      have hlag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (f.ker)
      have hquot : Nat.card
          ((Submodule.torsionBy ℤ (E⁄k).Point n) ⧸ f.ker) =
          Nat.card (Submodule.torsionBy ℤ (E⁄k).Point m) :=
        Nat.card_congr
          (QuotientAddGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv
      calc Nat.card (Submodule.torsionBy ℤ (E⁄k).Point n)
          = Nat.card ((Submodule.torsionBy ℤ (E⁄k).Point n) ⧸ f.ker) *
            Nat.card f.ker := hlag
      _ = Nat.card (Submodule.torsionBy ℤ (E⁄k).Point m) *
            n.minFac ^ 2 := by rw [hquot, hker]
      _ = m ^ 2 * n.minFac ^ 2 := by rw [ih m hmn hmk]
      _ = (n.minFac * m) ^ 2 := by ring
      _ = n ^ 2 := by rw [← hm]

end TorsionCard

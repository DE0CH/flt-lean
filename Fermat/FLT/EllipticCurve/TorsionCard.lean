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

set_option warn.sorry false in
/-- **The division-polynomial torsion dictionary** (sorry node): an
affine point `P = (x, y)` satisfies `n • P = 0` precisely when its
`x`-coordinate is a root of the division polynomial `ΨSq n`
(classically: the roots of `ψₙ` are exactly the `x`-coordinates of the
nonzero `n`-torsion points; Washington, *Elliptic curves*, Lemma
combined with the recursion of Theorem 3.6). -/
theorem smul_some_eq_zero_iff {n : ℤ} (hn : n ≠ 0) (hnk : (n : k) ≠ 0)
    {x y : k} (h : (E⁄k).toAffine.Nonsingular x y) :
    (n • (Affine.Point.some x y h : (E⁄k).Point) = 0) ↔
      ((E⁄k).ΨSq n).eval x = 0 :=
  sorry

set_option warn.sorry false in
/-- **The multiplication-by-`n` `x`-coordinate formula** (sorry node):
if `P = (x, y)` is an affine point with `ΨSq n` not vanishing at `x`
(so `n • P ≠ 0` by the dictionary above), then `n • P` is an affine
point whose `x`-coordinate `x'` satisfies `x' ⬝ ΨSq n (x) = Φ n (x)` —
the classical `x([n]P) = Φₙ(x)/ψₙ²(x)` (Washington, *Elliptic curves*,
Theorem 3.6), stated in multiplied-out form to avoid division. -/
theorem exists_smul_some_eq {n : ℤ} (hn : n ≠ 0) (hnk : (n : k) ≠ 0)
    {x y : k} (h : (E⁄k).toAffine.Nonsingular x y)
    (hΨ : ((E⁄k).ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
      n • (Affine.Point.some x y h : (E⁄k).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((E⁄k).ΨSq n).eval x = ((E⁄k).Φ n).eval x :=
  sorry

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
      exists_smul_some_eq E hnZ (by exact_mod_cast hn) hns hΨ
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
  -- on the curve, `Ψ₂Sq (x) = (2y + a₁x + a₃)²`
  have hyQ : (yQuad E x).eval y = 0 :=
    (eval_yQuad_eq_zero_iff_equation E x y).mpr h.1
  have hΨval : ((E⁄k).Ψ₂Sq).eval x =
      (2 * y + ((E⁄k).a₁ * x + (E⁄k).a₃)) ^ 2 := by
    have hkey := congrArg (Polynomial.eval y) (derivative_yQuad_sq_sub E x)
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, hyQ, mul_zero, sub_zero, derivative_yQuad_eval] at hkey
    exact hkey.symm
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
      (Int.natCast_ne_zero.mpr hp.ne_zero) ?_ hns]
    · rw [WeierstrassCurve.ΨSq_ofNat, if_neg (Nat.not_even_iff_odd.mpr hodd),
        mul_one, Polynomial.eval_pow, pow_eq_zero_iff two_ne_zero]
      exact hpreα
    · rw [show (((p : ℕ) : ℤ) : AlgebraicClosure k) = algebraMap k (AlgebraicClosure k) (p : k)
        by push_cast; rfl]
      exact fun h0 => hpk ((map_eq_zero _).mp h0)
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
      have := smul_some_eq_zero_iff E (by norm_num : (2 : ℤ) ≠ 0)
        (by exact_mod_cast h2) h
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
      rw [smul_some_eq_zero_iff E hpZ hpkZ h, hΨodd]
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

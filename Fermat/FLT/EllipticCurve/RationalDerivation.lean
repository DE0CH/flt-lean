/-
RationalDerivation.lean — own work for the Fermat project (not vendored).

**`d/dX` on `F(X)`, and the chord formula differentiated.**  Cut 2026-07-30 out of
`Fermat/FLT/EllipticCurve/DifferentialCharacter.lean`, whose leaf
`isDiffCharCert_add_of_ne` (the chord branch of the additivity of the differential
character `λ`) named exactly these two things as **THE MISSING MACHINERY**:

> this project has no derivation on the coordinate ring of a general `W/F` (only
> `PsiSumCompanion.DK` for the UNIVERSAL curve, in `InvariantDerivation.lean`).
> Two routes: build the rank-2 model `p(x) + q(x)y` … or eliminate `y` first —
> `x₃` is `y`-free because `x(−Q) = x(Q)`, so every quantity above can be pushed
> into `F(x)` and `D` becomes `ψ₂·d/dx` with ordinary `Polynomial.derivative`.

This module takes the SECOND route, which needs no coordinate ring at all.

## What is here

* `wr A B = A′B − AB′`, the Wronskian numerator, with the three identities that
  make it a calculus: `wr_smul` (it is `2`-homogeneous, so `A/B ↦ wr A B / B²` is
  well defined), `wr_add` and `wr_mul` (the sum and product rules with
  denominators cleared).
* `rderiv : F(X) → F(X)`, `d/dX` on rational functions, defined through
  `RatFunc.liftOn'` — `rderiv (A/B) = wr A B / B²` for EVERY representation
  `A/B`, not only the reduced one, which is what `wr_smul` buys.  It is a
  derivation: `rderiv_add`, `rderiv_mul`, `rderiv_sub`, `rderiv_div`, and it
  extends `Polynomial.derivative` (`rderiv_algebraMap`).
* `chordDeriv_core`, the differentiated chord formula, as PURE FIELD ALGEBRA over
  an arbitrary derivation `D` of an arbitrary field.  This is the mathematical
  content of `isDiffCharCert_add_of_ne`.

## `chordDeriv_core`, and why it is stated `y`-free

Write `Qᵢ = (xᵢ, yᵢ)` for the two image points of `P` under two maps, and put
`yᵢ = γᵢ·y + δᵢ` — every rational map's `y`-coordinate is affine in `y`, with
`γᵢ, δᵢ` functions of `x` alone.  Then `xᵢ`, `γᵢ`, `δᵢ` all live in `F(x)` and

* `D xᵢ = cᵢ·γᵢ` is `φᵢ*ω′ = cᵢ·ω` (this is the hypothesis, in the shape
  `DifferentialCharacter.lean`'s reduced certificate delivers it);
* `2δᵢ = γᵢ·(a₁x + a₃) − a₁′xᵢ − a₃′` is `diffChar_yWitness_onePart`, the
  `1`-part of the `y`-witness, which is automatic from `φᵢ` being a homomorphism;
* `γᵢ²f + δᵢ² + a₁′xᵢδᵢ + a₃′δᵢ = xᵢ³ + a₂′xᵢ² + a₄′xᵢ + a₆′` is the equation of
  the TARGET curve at `Qᵢ`, with `y` eliminated by `y² = f − (a₁x + a₃)y`;
* `x₃·(x₂ − x₁)² = (γ₂ − γ₁)²f + (δ₂ − δ₁)² + a₁′(δ₂ − δ₁)(x₂ − x₁)
  − (a₂′ + x₁ + x₂)(x₂ − x₁)²` is the chord formula
  `x₃ = λ² + a₁′λ − a₂′ − x₁ − x₂`, `λ = (y₂ − y₁)/(x₂ − x₁)`, with `y`
  eliminated the same way — legitimately, because the `y`-coefficient of `λ²`
  is killed by the `1`-part identity above;
* `γ₃(x₂ − x₁) = −(γ₂ − γ₁)(x₃ − x₁) − γ₁(x₂ − x₁)` is the `y`-part of
  `y₃ = −(λ(x₃ − x₁) + y₁) − a₁′x₃ − a₃′`.

The conclusion is `D x₃ = (c + d)·γ₃`.  No `y`, no points, no polynomials — and
no hypothesis on the characteristic: every certificate below has integer
coefficients.

The proof is the classical translation-invariance computation of Silverman *AEC*
III.5.1 in coordinates.  Its two halves, isolated as `hI1`/`hI2` inside, are

  `γ₁(2Γf + pΔ) − e·R₁ = (x₁ − x₃)e²`,  `e·R₂ − γ₂(2Γf + pΔ) = (x₂ − x₃)e²`

with `Rᵢ = 3xᵢ² + 2a₂′xᵢ + a₄′ − a₁′δᵢ`, `e = x₂ − x₁`; they say `Dλ = x₁ − x₃`
and `Dλ = x₂ − x₃` in the two slots, and each is a `linear_combination` over the
two target-curve equations and the two `1`-part identities.  `γ₁, γ₂ ≠ 0` is
load-bearing: it is what lets `D` of the curve equation be divided down to
`2f·Dγᵢ + γᵢ·Df + p·Dδᵢ = cᵢRᵢ`, and it is the statement that the maps do not
land in the `2`-torsion.
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

namespace RationalDerivation

open Polynomial

variable {F : Type*} [Field F]

local notation "ι" => algebraMap F[X] (RatFunc F)

/-- **The Wronskian numerator** of a pair of polynomials: `wr A B = A′B − AB′`, so
that `(A/B)′ = wr A B / B²`. -/
noncomputable def wr (A B : F[X]) : F[X] := derivative A * B - A * derivative B

/-- **`wr` is `2`-homogeneous**, which is exactly what makes `A/B ↦ wr A B / B²`
independent of the representation of the fraction. -/
theorem wr_smul (a A B : F[X]) : wr (a * A) (a * B) = a ^ 2 * wr A B := by
  simp only [wr, derivative_mul]; ring

/-- **The sum rule**, denominators cleared: `A/B + C/E = (AE + CB)/(BE)`. -/
theorem wr_add (A B C E : F[X]) :
    wr (A * E + C * B) (B * E) = E ^ 2 * wr A B + B ^ 2 * wr C E := by
  simp only [wr, derivative_mul, derivative_add]; ring

/-- **The product rule**, denominators cleared: `(A/B)·(C/E) = (AC)/(BE)`. -/
theorem wr_mul (A B C E : F[X]) :
    wr (A * C) (B * E) = C * E * wr A B + A * B * wr C E := by
  simp only [wr, derivative_mul]; ring

/-- **`d/dX` on rational functions.**  Well defined by `wr_smul`. -/
noncomputable def rderiv (x : RatFunc F) : RatFunc F :=
  x.liftOn' (fun p q => ι (wr p q) / (ι q) ^ 2) <| by
    intro p q a hq ha
    rw [wr_smul, map_mul, map_mul, map_pow, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero ha))]

@[simp]
theorem rderiv_div (p q : F[X]) : rderiv (ι p / ι q) = ι (wr p q) / (ι q) ^ 2 := by
  rw [rderiv, RatFunc.liftOn'_div]
  intro r
  simp [wr]

/-- `rderiv` extends `Polynomial.derivative`. -/
theorem rderiv_algebraMap (p : F[X]) : rderiv (ι p) = ι (derivative p) := by
  have h := rderiv_div p (1 : F[X])
  simp only [map_one, div_one, one_pow] at h
  rw [h, wr]
  simp

theorem rderiv_add (x y : RatFunc F) : rderiv (x + y) = rderiv x + rderiv y := by
  induction x using RatFunc.induction_on with | f p q hq => ?_
  induction y using RatFunc.induction_on with | f r s hs => ?_
  have hq' : ι q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hs' : ι s ≠ 0 := RatFunc.algebraMap_ne_zero hs
  have hsum : ι p / ι q + ι r / ι s = ι (p * s + r * q) / ι (q * s) := by
    rw [map_add, map_mul, map_mul, map_mul]
    field_simp
  rw [hsum, rderiv_div, rderiv_div, rderiv_div, wr_add]
  simp only [map_add, map_mul, map_pow]
  field_simp

theorem rderiv_mul (x y : RatFunc F) : rderiv (x * y) = x * rderiv y + y * rderiv x := by
  induction x using RatFunc.induction_on with | f p q hq => ?_
  induction y using RatFunc.induction_on with | f r s hs => ?_
  have hq' : ι q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hs' : ι s ≠ 0 := RatFunc.algebraMap_ne_zero hs
  have hprod : ι p / ι q * (ι r / ι s) = ι (p * r) / ι (q * s) := by
    rw [map_mul, map_mul]; field_simp
  rw [hprod, rderiv_div, rderiv_div, rderiv_div, wr_mul]
  simp only [map_add, map_mul]
  field_simp
  ring

theorem rderiv_sub (x y : RatFunc F) : rderiv (x - y) = rderiv x - rderiv y := by
  have h : rderiv ((x - y) + y) = rderiv (x - y) + rderiv y := rderiv_add _ _
  rw [sub_add_cancel] at h
  rw [h]; ring

/-! ### The chord formula, differentiated

Pure field algebra over an arbitrary derivation; see the module docstring for the
dictionary between the variables here and the geometry. -/

/-- **THE CHORD FORMULA DIFFERENTIATED** (Silverman *AEC* III.5.1 in coordinates).
`x₁, x₂` are the `x`-coordinates of the two image points, `g₁, g₂` their
`y`-multipliers and `q₁, q₂` their `y`-constants; `x₃, g₃` the same data for the
chord sum.  Given `D xᵢ = cᵢ·gᵢ` for the two summands, the sum satisfies
`D x₃ = (c + d)·g₃`.

No characteristic hypothesis: all certificates have integer coefficients. -/
theorem chordDeriv_core {K : Type*} [Field K] (D : K → K)
    (hadd : ∀ u v : K, D (u + v) = D u + D v)
    (hmul : ∀ u v : K, D (u * v) = u * D v + v * D u)
    {al1 al2 al3 al4 al6 c d f p x1 x2 g1 g2 q1 q2 x3 g3 : K}
    (hDal1 : D al1 = 0) (hDal2 : D al2 = 0) (hDal3 : D al3 = 0)
    (hDal4 : D al4 = 0) (hDal6 : D al6 = 0)
    (hg1 : g1 ≠ 0) (hg2 : g2 ≠ 0) (he : x2 - x1 ≠ 0)
    (hx1 : D x1 = c * g1) (hx2 : D x2 = d * g2)
    (hO1 : 2 * q1 = g1 * p - al1 * x1 - al3)
    (hO2 : 2 * q2 = g2 * p - al1 * x2 - al3)
    (hC1 : g1 ^ 2 * f + q1 ^ 2 + al1 * x1 * q1 + al3 * q1
        = x1 ^ 3 + al2 * x1 ^ 2 + al4 * x1 + al6)
    (hC2 : g2 ^ 2 * f + q2 ^ 2 + al1 * x2 * q2 + al3 * q2
        = x2 ^ 3 + al2 * x2 ^ 2 + al4 * x2 + al6)
    (hx3 : x3 * (x2 - x1) ^ 2
        = (g2 - g1) ^ 2 * f + (q2 - q1) ^ 2 + al1 * (q2 - q1) * (x2 - x1)
          - (al2 + x1 + x2) * (x2 - x1) ^ 2)
    (hg3 : g3 * (x2 - x1) = -((g2 - g1) * (x3 - x1)) - g1 * (x2 - x1)) :
    D x3 = (c + d) * g3 := by
  -- the derivation calculus
  have hD0 : D 0 = 0 := by have h := hmul 0 0; simpa using h
  have hDneg : ∀ u : K, D (-u) = -D u := by
    intro u
    have h := hadd u (-u)
    rw [add_neg_cancel, hD0] at h
    linear_combination -h
  have hDsub : ∀ u v : K, D (u - v) = D u - D v := by
    intro u v
    rw [sub_eq_add_neg, hadd, hDneg, ← sub_eq_add_neg]
  have hDsq : ∀ u : K, D (u ^ 2) = 2 * u * D u := by
    intro u; rw [pow_two, hmul]; ring
  have hDcube : ∀ u : K, D (u ^ 3) = 3 * u ^ 2 * D u := by
    intro u
    rw [show u ^ 3 = u ^ 2 * u from by ring, hmul, hDsq]; ring
  -- the two halves of translation invariance: `Dλ = x₁ − x₃` and `Dλ = x₂ − x₃`
  have hI1 : (x2 - x1) * (3 * x1 ^ 2 + 2 * al2 * x1 + al4 - al1 * q1)
      = g1 * (2 * (g2 - g1) * f + p * (q2 - q1)) - (x1 - x3) * (x2 - x1) ^ 2 := by
    linear_combination hC1 - hC2 + (q2 - q1) * hO1 - hx3
  have hI2 : (x2 - x1) * (3 * x2 ^ 2 + 2 * al2 * x2 + al4 - al1 * q2)
      = g2 * (2 * (g2 - g1) * f + p * (q2 - q1)) + (x2 - x3) * (x2 - x1) ^ 2 := by
    linear_combination hC1 - hC2 + (q2 - q1) * hO2 + hx3
  -- the target curve's equation at each image point, differentiated and divided by `gᵢ`
  have hD1 : 2 * f * D g1 + g1 * D f + p * D q1
      = c * (3 * x1 ^ 2 + 2 * al2 * x1 + al4 - al1 * q1) := by
    have h := congrArg D hC1
    simp only [hadd, hmul, hDsq, hDcube, hDal1, hDal2, hDal3, hDal4, hDal6, hx1,
      mul_zero, add_zero] at h
    have hkey : g1 * (2 * f * D g1 + g1 * D f + p * D q1
        - c * (3 * x1 ^ 2 + 2 * al2 * x1 + al4 - al1 * q1)) = 0 := by
      linear_combination h - D q1 * hO1
    rcases mul_eq_zero.mp hkey with h0 | h0
    · exact absurd h0 hg1
    · linear_combination h0
  have hD2 : 2 * f * D g2 + g2 * D f + p * D q2
      = d * (3 * x2 ^ 2 + 2 * al2 * x2 + al4 - al1 * q2) := by
    have h := congrArg D hC2
    simp only [hadd, hmul, hDsq, hDcube, hDal1, hDal2, hDal3, hDal4, hDal6, hx2,
      mul_zero, add_zero] at h
    have hkey : g2 * (2 * f * D g2 + g2 * D f + p * D q2
        - d * (3 * x2 ^ 2 + 2 * al2 * x2 + al4 - al1 * q2)) = 0 := by
      linear_combination h - D q2 * hO2
    rcases mul_eq_zero.mp hkey with h0 | h0
    · exact absurd h0 hg2
    · linear_combination h0
  -- differentiate the chord formula and assemble
  have hDX3 := congrArg D hx3
  simp only [hadd, hDsub, hmul, hDsq, hDal1, hDal2, hx1, hx2, mul_zero, add_zero,
    zero_add] at hDX3
  have hkey : D x3 * (x2 - x1) ^ 3
      = (x2 - x1) ^ 2 * ((g2 - g1) * (c * (x1 - x3) + d * (x2 - x3))
          - (x2 - x1) * (c * g1 + d * g2)) := by
    linear_combination (x2 - x1) * hDX3
      + (g2 - g1) * (x2 - x1) * hD2 - (g2 - g1) * (x2 - x1) * hD1
      + (g2 - g1) * d * hI2 - (g2 - g1) * c * hI1
      + ((x2 - x1) * (D q2 - D q1) - (d * g2 - c * g1) * (q2 - q1)) * hO2
      - ((x2 - x1) * (D q2 - D q1) - (d * g2 - c * g1) * (q2 - q1)) * hO1
      - 2 * (d * g2 - c * g1) * hx3
  have hcube : (x2 - x1) ^ 3 ≠ 0 := pow_ne_zero 3 he
  have hfin : D x3 * (x2 - x1) ^ 3 = ((c + d) * g3) * (x2 - x1) ^ 3 := by
    rw [hkey]
    linear_combination (-(c + d) * (x2 - x1) ^ 2) * hg3
  exact mul_right_cancel₀ hcube hfin

end RationalDerivation

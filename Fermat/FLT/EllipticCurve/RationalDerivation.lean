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

/-! ### The chord branch as a polynomial identity

`polyForm_add` is `chordDeriv_core` instantiated at `RatFunc F`, with every quantity a
fraction of polynomials.  It is the whole bridge between the field computation above and
the polynomial world its consumer lives in, and it mentions nothing elliptic: the ten
constants `a₁ … a₆` (source) and `al1 … al6` (target) are arbitrary field elements. -/

/-- **THE CHORD BRANCH, AS A POLYNOMIAL IDENTITY.**  Given, for two maps with witnesses
`(Aᵢ, Bᵢ, Cᵢ, Dᵢ, Eᵢ)`,

* `(Aᵢ′Bᵢ − AᵢBᵢ′)·Eᵢ = cᵢ·Cᵢ·Bᵢ²`  (the differential certificate, `diffChar_polyForm`),
* `2DᵢBᵢ + a₁′AᵢEᵢ + a₃′BᵢEᵢ = CᵢBᵢ(a₁X + a₃)`  (`diffChar_yWitness_onePart`),
* the target curve's equation at the image point, `y`-free (`diffChar_curveEq`),

together with the chord formula for the sum's witnesses `(A, B, Cp, ·, E)` — `hx3` for the
`x`-coordinate and `hg3` for the `y`-multiplier, both pure group-law bookkeeping — the sum
satisfies `(A′B − AB′)·E = (c + d)·Cp·B²`.

`Cᵢ ≠ 0` is `diffChar_yMultiplier_ne_zero` and `A₂B₁ − A₁B₂ ≠ 0` says the two maps have
different `x`-coordinate functions.  Everything is proven by moving to `RatFunc F`, where
`xᵢ = Aᵢ/Bᵢ`, `γᵢ = Cᵢ/Eᵢ`, `δᵢ = Dᵢ/Eᵢ`, `x₃ = A/B`, `γ₃ = Cp/E`, applying
`chordDeriv_core` with `D = rderiv`, and clearing denominators back. -/
theorem polyForm_add {a1 a2 a3 a4 a6 al1 al2 al3 al4 al6 c d : F}
    {A₁ B₁ C₁ D₁ E₁ A₂ B₂ C₂ D₂ E₂ A B Cp E : F[X]}
    (hB₁ : B₁ ≠ 0) (hE₁ : E₁ ≠ 0) (hB₂ : B₂ ≠ 0) (hE₂ : E₂ ≠ 0)
    (hB : B ≠ 0) (hE : E ≠ 0) (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0)
    (hG : A₂ * B₁ - A₁ * B₂ ≠ 0)
    (hp1 : (derivative A₁ * B₁ - A₁ * derivative B₁) * E₁ = C c * C₁ * B₁ ^ 2)
    (hp2 : (derivative A₂ * B₂ - A₂ * derivative B₂) * E₂ = C d * C₂ * B₂ ^ 2)
    (ho1 : C 2 * D₁ * B₁ + C al1 * A₁ * E₁ + C al3 * B₁ * E₁
      = C₁ * B₁ * (C a1 * X + C a3))
    (ho2 : C 2 * D₂ * B₂ + C al1 * A₂ * E₂ + C al3 * B₂ * E₂
      = C₂ * B₂ * (C a1 * X + C a3))
    (hq1 : C₁ ^ 2 * (X ^ 3 + C a2 * X ^ 2 + C a4 * X + C a6) * B₁ ^ 3 + D₁ ^ 2 * B₁ ^ 3
        + C al1 * A₁ * D₁ * E₁ * B₁ ^ 2 + C al3 * D₁ * E₁ * B₁ ^ 3
      = E₁ ^ 2 * (A₁ ^ 3 + C al2 * A₁ ^ 2 * B₁ + C al4 * A₁ * B₁ ^ 2 + C al6 * B₁ ^ 3))
    (hq2 : C₂ ^ 2 * (X ^ 3 + C a2 * X ^ 2 + C a4 * X + C a6) * B₂ ^ 3 + D₂ ^ 2 * B₂ ^ 3
        + C al1 * A₂ * D₂ * E₂ * B₂ ^ 2 + C al3 * D₂ * E₂ * B₂ ^ 3
      = E₂ ^ 2 * (A₂ ^ 3 + C al2 * A₂ ^ 2 * B₂ + C al4 * A₂ * B₂ ^ 2 + C al6 * B₂ ^ 3))
    (hx3 : A * ((E₁ * E₂) ^ 2 * (A₂ * B₁ - A₁ * B₂) ^ 2 * (B₁ * B₂))
      = B * ((B₁ * B₂) ^ 3 * ((C₂ * E₁ - C₁ * E₂) ^ 2
              * (X ^ 3 + C a2 * X ^ 2 + C a4 * X + C a6) + (D₂ * E₁ - D₁ * E₂) ^ 2)
          + C al1 * (D₂ * E₁ - D₁ * E₂) * (A₂ * B₁ - A₁ * B₂) * (B₁ * B₂) ^ 2 * (E₁ * E₂)
          - (C al2 * (B₁ * B₂) + (A₁ * B₂ + A₂ * B₁))
            * (A₂ * B₁ - A₁ * B₂) ^ 2 * (E₁ * E₂) ^ 2))
    (hg3 : Cp * (A₂ * B₁ - A₁ * B₂) * (E₁ * E₂) * B
        + C₁ * (A₂ * B₁ - A₁ * B₂) * E * E₂ * B
        + (C₂ * E₁ - C₁ * E₂) * (A * B₁ - A₁ * B) * E * B₂ = 0) :
    (derivative A * B - A * derivative B) * E = C (c + d) * Cp * B ^ 2 := by
  have iB₁ : (ι B₁) ≠ 0 := RatFunc.algebraMap_ne_zero hB₁
  have iE₁ : (ι E₁) ≠ 0 := RatFunc.algebraMap_ne_zero hE₁
  have iB₂ : (ι B₂) ≠ 0 := RatFunc.algebraMap_ne_zero hB₂
  have iE₂ : (ι E₂) ≠ 0 := RatFunc.algebraMap_ne_zero hE₂
  have iB : (ι B) ≠ 0 := RatFunc.algebraMap_ne_zero hB
  have iE : (ι E) ≠ 0 := RatFunc.algebraMap_ne_zero hE
  have iC₁ : (ι C₁) ≠ 0 := RatFunc.algebraMap_ne_zero hC₁
  have iC₂ : (ι C₂) ≠ 0 := RatFunc.algebraMap_ne_zero hC₂
  have iG : (ι (A₂ * B₁ - A₁ * B₂)) ≠ 0 := RatFunc.algebraMap_ne_zero hG
  -- the derivative of a constant vanishes
  have hDC : ∀ a : F, rderiv (ι (C a)) = 0 := by
    intro a; rw [rderiv_algebraMap, derivative_C, map_zero]
  have hne : ι A₂ / ι B₂ - ι A₁ / ι B₁ ≠ 0 := by
    have h : ι A₂ / ι B₂ - ι A₁ / ι B₁ = ι (A₂ * B₁ - A₁ * B₂) / (ι B₂ * ι B₁) := by
      rw [map_sub, map_mul, map_mul]; field_simp
    rw [h]
    exact div_ne_zero iG (mul_ne_zero iB₂ iB₁)
  have key := RationalDerivation.chordDeriv_core (K := RatFunc F) rderiv rderiv_add rderiv_mul
    (al1 := ι (C al1)) (al2 := ι (C al2)) (al3 := ι (C al3)) (al4 := ι (C al4))
    (al6 := ι (C al6)) (c := ι (C c)) (d := ι (C d))
    (f := ι X ^ 3 + ι (C a2) * ι X ^ 2 + ι (C a4) * ι X + ι (C a6))
    (p := ι (C a1) * ι X + ι (C a3))
    (x1 := ι A₁ / ι B₁) (x2 := ι A₂ / ι B₂) (g1 := ι C₁ / ι E₁) (g2 := ι C₂ / ι E₂)
    (q1 := ι D₁ / ι E₁) (q2 := ι D₂ / ι E₂) (x3 := ι A / ι B) (g3 := ι Cp / ι E)
    (hDC al1) (hDC al2) (hDC al3) (hDC al4) (hDC al6)
    (div_ne_zero iC₁ iE₁) (div_ne_zero iC₂ iE₂) hne
    ?hx1 ?hx2 ?hO1 ?hO2 ?hC1 ?hC2 ?hx3 ?hg3
  · -- the conclusion, cleared
    rw [rderiv_div] at key
    simp only [wr, map_mul, map_sub] at key
    have hfin : ι ((derivative A * B - A * derivative B) * E) = ι (C (c + d) * Cp * B ^ 2) := by
      simp only [map_mul, map_sub, map_pow, map_add]
      field_simp at key
      linear_combination key
    exact RatFunc.algebraMap_injective F hfin
  case hx1 =>
    rw [rderiv_div]
    have h := congrArg (algebraMap F[X] (RatFunc F)) hp1
    simp only [wr, map_mul, map_sub, map_pow] at h ⊢
    field_simp
    linear_combination h
  case hx2 =>
    rw [rderiv_div]
    have h := congrArg (algebraMap F[X] (RatFunc F)) hp2
    simp only [wr, map_mul, map_sub, map_pow] at h ⊢
    field_simp
    linear_combination h
  case hO1 =>
    have h := congrArg (algebraMap F[X] (RatFunc F)) ho1
    simp only [map_mul, map_add, map_ofNat] at h ⊢
    field_simp
    linear_combination h
  case hO2 =>
    have h := congrArg (algebraMap F[X] (RatFunc F)) ho2
    simp only [map_mul, map_add, map_ofNat] at h ⊢
    field_simp
    linear_combination h
  case hC1 =>
    have h := congrArg (algebraMap F[X] (RatFunc F)) hq1
    simp only [map_mul, map_pow, map_add] at h ⊢
    field_simp
    linear_combination h
  case hC2 =>
    have h := congrArg (algebraMap F[X] (RatFunc F)) hq2
    simp only [map_mul, map_pow, map_add] at h ⊢
    field_simp
    linear_combination h
  case hx3 =>
    have h := congrArg (algebraMap F[X] (RatFunc F)) hx3
    simp only [map_mul, map_sub, map_pow, map_add] at h ⊢
    field_simp
    linear_combination h
  case hg3 =>
    have h := congrArg (algebraMap F[X] (RatFunc F)) hg3
    simp only [map_mul, map_sub, map_add, map_zero] at h ⊢
    field_simp
    linear_combination h

end RationalDerivation

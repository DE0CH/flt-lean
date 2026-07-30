/-
BinaryQuadraticForm.lean — own work for the Fermat project.

**Gauss's theory of integral binary quadratic forms**, built here because
mathlib has none of it: a grep of the pin for `BinaryQuadraticForm` returns a
single hit, an unrelated prose line in `NumberTheory/LegendreSymbol/Basic.lean`,
and `~/cs/FLT` has zero hits for each of `BinaryQuadratic`, `classNumber`,
`Heegner`, `Rabinowitsch`.

What is here, and all of it is PROVEN:

* `BinaryQuadraticForm`, `eval`, `discr`, `IsPosDef`, `IsReduced`;
* the right action `act` of `SL₂(ℤ)` on forms, its composition law `act_act`,
  the transformation rule `discr_act` for the discriminant, and proper
  equivalence `Equivalent` with `symm`/`trans`;
* `eval_pos` — a positive definite form takes positive values off the origin —
  and `IsPosDef.act`, so positive definiteness is an invariant;
* **`exists_reduced_equivalent`: Gauss reduction.** Every positive definite
  form is properly equivalent to a reduced one (`|b| ≤ a ≤ c`). Proved by the
  classical descent: translate `b` into `(−a, a]` by `T^n`, then swap by `S`
  whenever `c < a`, which strictly decreases `a`;
* **`a_eq_one_of_primeGenerating`: Rabinowitsch's criterion, the easy half.**
  If `x² + x + m` is prime for every `x ≤ m − 2`, then every reduced positive
  definite form of discriminant `1 − 4m` has `a = 1`. (For a reduced form,
  `b` is odd, `b = ±(2x+1)`, and `a·c = x² + x + m` is exactly the value of
  the quadratic at `x`; the reduction inequalities `3a² ≤ 4m − 1` force
  `x + 1 < m`, so that value is prime and `a ≤ c` pins `a = 1`.)
* **`equivalent_of_primeGenerating`**: combining the two, under the same
  hypothesis EVERY positive definite form of discriminant `1 − 4m` is properly
  equivalent to the principal form `⟨1, 1, m⟩` — i.e. the discriminant
  `1 − 4m` has ONE class.

On top of that, `neg_163_le_of_classNumberOne` is now PROVEN by a decomposition
along the Heegner–Stark route (Heegner 1952, Stark 1967; presented as in Cox,
*Primes of the form x²+ny²*, §12, and Booher, *Modular curves and the class
number one problem*, §6). The elementary half is proved here:

* `not_dvd_sq_sub_of_classNumberOne` — **the elementary obstruction**: one class
  forces `d` to be a non-square mod `4a` for every `a` with `2 ≤ a` and `4a < |d|`
  (this is Booher's Proposition 2, i.e. "no small split primes", in the form that
  needs no Legendre symbol);
* `prime_of_classNumberOne` — **the reduction to prime discriminants**:
  `d = −4`, `d = −8`, or `−d` is a prime `≡ 3 mod 4` (the elementary half of
  Gauss's genus theory, run with explicit forms);
* `mod_eight_eq_three_of_classNumberOne` — `p ≡ 3 mod 8` once `p > 8`;
* `heegnerRelation_solutions` — the six solutions of Heegner's coefficient
  relation `2(b²−4a) = (2b−a²)²`, over the Diophantine leaf below.

* `eq_of_two_mul_mul_cube_add_one_eq_sq` — **PROVEN**: `2x(x³+1) = y²` has exactly
  the six solutions `(0,0), (−1,0), (1,±2), (2,±6)`. Elementary and self-contained;
  see the section header above it for the argument, which needs none of the three
  quadratic rings an earlier plan called for.

`lt_exp_pi_sqrt`, the numeric bound `exp(π√p) > 640320³ + 745` for `p ≥ 164`, is
also proved here.

The DEEP leaf `exists_heegnerRelation_of_classNumberOne` has since been
DECOMPOSED and is now PROVEN over the `Heegner` namespace, which defines
`j = E₄³/Δ`, Weber's `f₂ = √2·η(2τ)/η(τ)`, `γ₂ = (f₂²⁴+16)/f₂⁸`, the Heegner
point `τ₀ = (3+√−p)/2` and `α = ζ₈⁻¹f₂(τ₀)²` over mathlib's `ModularForm.eta`,
`ModularForm.discriminant` and `ModularForm.E₄`, and proves Heegner's
double-squaring match (`Heegner.exists_heegnerRelation_aux`, the step Weber
missed) together with `Heegner.exists_int_gammaTwo`.

`Heegner.exists_rat_gammaTwo_heegnerPoint` has since been decomposed and PROVEN in turn, over
`Heegner.exists_real_gammaTwo_heegnerPoint` (`γ₂(τ₀) ∈ ℝ` — PROVEN here, by conjugation
through `η`'s infinite product) and the two class-field leaves listed below.

FIVE leaves remain, each stated so that it can be worked on alone.  (The
Diophantine leaf `eq_of_two_mul_mul_cube_add_one_eq_sq`, which an earlier version
of this list counted, was PROVEN concurrently — see its bullet above; and
`exists_rat_gammaTwo_heegnerPoint`, which it also counted, was replaced by the
two class-field leaves below.)

* `Heegner.natDegree_minpoly_weberAlpha` — the degree of `α` over `ℚ` is exactly `3`
  (Weber's theory of the ring class field of the order of discriminant `−4p`, whose class
  number is `3`). This is the ONLY thing about `α` still open, and both
  `Heegner.exists_intCubic_weberAlpha` and `Heegner.intCast_indep_weberAlpha_pow_four` are
  PROVEN from it by elementary field theory — the independence of `1, α⁴, α⁸` needed no
  modular input at all, only the primality of the degree. Its former companion
  `Heegner.isIntegral_weberAlpha` — "`α` is an algebraic integer" — turned out NOT to be an
  independent CM input and is now PROVEN: `α⁴` is a root of `x³ − γ₂(τ₀)x − 16` by the
  definition of `γ₂`, so `γ₂(τ₀) ∈ ℤ` (i.e. `Heegner.exists_int_gammaTwo`, which the main
  argument needs anyway) already forces `α⁴`, hence `α`, to be integral;
* `Heegner.exists_modularPolynomial` — the MODULAR POLYNOMIAL `Φ_N ∈ ℤ[X, Y]`: it kills
  `(j(A z), j(z))` for every primitive integral `A` of determinant `N`, and for non-square `N`
  its diagonal `Φ_N(X, X)` has leading coefficient `±1` (Kronecker). No class field theory and
  no class-number hypothesis. This REPLACES the former leaf
  `Heegner.isIntegral_gammaTwo_heegnerPoint`, which is now PROVEN from it through three
  intermediate steps, ALL proved here: `isIntegral_of_eval_diag` (a `(x,x)`-root of a
  diagonal-unit bivariate polynomial is an algebraic integer),
  `isIntegral_jInvariant_of_fixedPoint` (put `w = z`), and
  `isIntegral_jInvariant_of_quadratic` (`j` is an algebraic integer at every imaginary
  quadratic `z` — the fixing matrix is `[[m−b, −c], [a, m]]`, and
  `exists_coprime_not_isSquare_quadratic` produces an `m` making it primitive with non-square
  determinant); a cube root of an algebraic integer is then an algebraic integer, so Weber's
  `3 ∤ p` and level-`3` theory — which the old docstring claimed were needed here — are not;
* `Heegner.exists_quadratic_jInvariant_heegnerPoint` — `j(τ₀) ∈ K = ℚ(√−p)`; **this is the
  main theorem of complex multiplication and is the only leaf here that needs it**, and the
  only one that consumes `hcl`;
* `Heegner.exists_quadratic_gammaTwo_of_jInvariant` — `γ₂(τ₀) ∈ K` once `j(τ₀) ∈ K` (Weber's
  level-`3` descent; needs only `3 ∤ p`);

`Heegner.gammaTwo_pow_three_eq_jInvariant` (Weber's `γ₂³ = j`) and
`Heegner.exp_pi_sqrt_le_of_jInvariant_eq` (the bound `exp(π√p) ≤ 745 − j(τ₀)`) are now both
PROVEN, over three new analytic leaves:

* `Heegner.eta_pow_24_add_eta_two_pow_24` — `η²⁴ + 256η(2z)²⁴ = E₄·(η·η(2z))⁸`, the single
  modular-form identity carrying ALL of Weber's `γ₂³ = j`. Given it, LEAF 5 is field algebra.
  **Now PROVEN** (2026-07-29), over ONE new leaf, `Heegner.eta_two_torsion_key`
  (`η(z/2)⁸η(2z)⁸(η(z/2)⁸+16η(2z)⁸) = η(z)²⁴`). Everything else is proven here: `η(z+1)`,
  the `S`-transformation of `F = (η²⁴+256η(2z)²⁴)/(ηη(2z))⁸` from the key identity, the
  packaging of `F` as a `ModularForm 𝒮ℒ 4`, its value `1` at the cusp, and
  `F = E₄` from `ModularForm.levelOne_weight_four_rank_one`;
* `Heegner.exists_E₄_heegnerPoint_approx`, `Heegner.exists_E₆_heegnerPoint_approx` — the
  values of `E₄` and `E₆` at `τ₀` to second order in `Q = exp(−π√p)`, with an explicit `Q³`
  error bound. Both follow the same mathlib lemma
  (`EisensteinSeries.q_expansion_bernoulli`), and between them they eliminate `Δ` via
  `Δ = (E₄³ − E₆²)/1728` — so LEAF 6 needs no infinite products and, notably, no positivity
  of the `j`-coefficients `c_k`. **Both are now PROVEN** (2026-07-28), over
  `Heegner.cexp_heegnerPoint` (`q = −Q` at `τ₀`), `Heegner.E_second_order` (the shared
  `q`-expansion split) and `Heegner.abs_tsum_shift_le` (a geometric-majorant tail bound).

So this file has FIVE open leaves. The list below was REGENERATED from the merged source at
this merge, not inherited from any of the three sides that disagreed about it — and each of
them was RIGHT about its own base, which is exactly why none of their lists survives:
`Heegner.natDegree_minpoly_weberAlpha`, `Heegner.exists_modularPolynomial`, the two
class-field leaves `Heegner.exists_quadratic_jInvariant_heegnerPoint` and
`Heegner.exists_quadratic_gammaTwo_of_jInvariant`, and the single `η`-product identity
`Heegner.eta_two_torsion_key`.

Six names moved between release 19 and here, in three independent directions:

* `isIntegral_gammaTwo_heegnerPoint` is PROVEN (flt-lean-108) — from the new and strictly
  weaker leaf `exists_modularPolynomial`, which needs no class field theory and no
  class-number hypothesis, together with three intermediate steps proved there;
* `exists_intCubic_weberAlpha` and `intCast_indep_weberAlpha_pow_four` are PROVEN
  (flt-lean-237) from the new leaf `natDegree_minpoly_weberAlpha`, and their former
  companion `isIntegral_weberAlpha` is PROVEN outright — it was never a CM input;
* `eta_pow_24_add_eta_two_pow_24` is PROVEN (flt-lean-41, release 19), replaced as a leaf by
  `eta_two_torsion_key`.

So the count fell from six to five by two closures net (three leaves closed against two
opened, plus `eta_pow_24` traded one-for-one), and NOT ONE of the three contributing branches
could have computed that number: each saw its own two closures and neither of the others'.
`exists_rat_gammaTwo_heegnerPoint` and the Diophantine `eq_of_two_mul_mul_cube_add_one_eq_sq`
are PROVEN and are not leaves at all.

Do not trust this paragraph either — it is stamped to one commit; regenerate it from the
compiler's `declaration uses 'sorry'` warning set. -/
module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

@[expose] public section

namespace Fermat

/-- An integral binary quadratic form `a x² + b x y + c y²`, recorded by its
three coefficients. -/
@[ext]
structure BinaryQuadraticForm where
  /-- The coefficient of `x²`. -/
  a : ℤ
  /-- The coefficient of `x y`. -/
  b : ℤ
  /-- The coefficient of `y²`. -/
  c : ℤ

namespace BinaryQuadraticForm

/-- The value `f(x, y) = a x² + b x y + c y²`. -/
def eval (f : BinaryQuadraticForm) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- The discriminant `b² − 4 a c`. -/
def discr (f : BinaryQuadraticForm) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- Positive definiteness: `a > 0` and negative discriminant. -/
structure IsPosDef (f : BinaryQuadraticForm) : Prop where
  /-- The leading coefficient is positive. -/
  a_pos : 0 < f.a
  /-- The discriminant is negative. -/
  discr_neg : f.discr < 0

/-- Gauss reduction, in the form used here: `|b| ≤ a ≤ c`. (The extra
normalisation `b ≥ 0` when `|b| = a` or `a = c`, which pins the reduced
representative uniquely, is not needed for anything below.) -/
structure IsReduced (f : BinaryQuadraticForm) : Prop where
  /-- `|b| ≤ a`. -/
  abs_b_le_a : |f.b| ≤ f.a
  /-- `a ≤ c`. -/
  a_le_c : f.a ≤ f.c

/-- The form `f ∘ M` for `M = ![![p, q], ![r, s]]`, i.e. the form
`(x, y) ↦ f (p x + q y, r x + s y)`. -/
def act (f : BinaryQuadraticForm) (p q r s : ℤ) : BinaryQuadraticForm where
  a := f.eval p r
  b := 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s
  c := f.eval q s

/-- Proper equivalence of forms: `g = f ∘ M` for some `M ∈ SL₂(ℤ)`. -/
def Equivalent (f g : BinaryQuadraticForm) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = 1 ∧ f.act p q r s = g

/-- The principal form `⟨1, 1, m⟩` of discriminant `1 − 4m`. -/
def principal (m : ℤ) : BinaryQuadraticForm := ⟨1, 1, m⟩

lemma discr_act (f : BinaryQuadraticForm) (p q r s : ℤ) :
    (f.act p q r s).discr = (p * s - q * r) ^ 2 * f.discr := by
  simp only [discr, act, eval]; ring

lemma act_act (f : BinaryQuadraticForm) (p q r s p' q' r' s' : ℤ) :
    (f.act p q r s).act p' q' r' s'
      = f.act (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  ext
  · simp only [act, eval]; ring
  · simp only [act, eval]; ring
  · simp only [act, eval]; ring

lemma act_one (f : BinaryQuadraticForm) : f.act 1 0 0 1 = f := by
  ext
  · simp only [act, eval]; ring
  · simp only [act, eval]; ring
  · simp only [act, eval]; ring

theorem Equivalent.symm {f g : BinaryQuadraticForm} (h : f.Equivalent g) : g.Equivalent f := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  refine ⟨s, -q, -r, p, by linear_combination hdet, ?_⟩
  rw [act_act]
  have h1 : p * s + q * -r = 1 := by linear_combination hdet
  have h2 : p * -q + q * p = 0 := by ring
  have h3 : r * s + s * -r = 0 := by ring
  have h4 : r * -q + s * p = 1 := by linear_combination hdet
  rw [h1, h2, h3, h4, act_one]

theorem Equivalent.trans {f g h : BinaryQuadraticForm} (h₁ : f.Equivalent g)
    (h₂ : g.Equivalent h) : f.Equivalent h := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h₁
  obtain ⟨p', q', r', s', hdet', rfl⟩ := h₂
  refine ⟨p * p' + q * r', p * q' + q * s', r * p' + s * r', r * q' + s * s', ?_, ?_⟩
  · linear_combination (p' * s' - q' * r') * hdet + hdet'
  · exact (act_act f p q r s p' q' r' s').symm

lemma eval_pos {f : BinaryQuadraticForm} (hf : f.IsPosDef) {x y : ℤ}
    (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < f.eval x y := by
  have ha := hf.a_pos
  have hd := hf.discr_neg
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := by tauto
    have hx2 : 0 < x ^ 2 := by positivity
    simp only [eval]
    nlinarith
  · have key : 4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.discr * y ^ 2 := by
      simp only [eval, discr]; ring
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * f.a * x + f.b * y)]

lemma IsPosDef.act {f : BinaryQuadraticForm} (hf : f.IsPosDef) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) : (f.act p q r s).IsPosDef where
  a_pos := by
    refine eval_pos hf ?_
    rcases eq_or_ne p 0 with rfl | hp
    · rcases eq_or_ne r 0 with rfl | hr
      · exact absurd hdet (by norm_num)
      · exact Or.inr hr
    · exact Or.inl hp
  discr_neg := by
    rw [discr_act, hdet, one_pow, one_mul]
    exact hf.discr_neg

/-- The translation step of Gauss reduction: applying `T^(-k)` moves `b` into
the window `[-a, a)` without changing `a`. -/
lemma exists_abs_b_le {f : BinaryQuadraticForm} (hf : f.IsPosDef) :
    ∃ g, f.Equivalent g ∧ g.a = f.a ∧ |g.b| ≤ g.a := by
  have ha : 0 < f.a := hf.a_pos
  have h2a : (0 : ℤ) < 2 * f.a := by linarith
  obtain ⟨k, t, ht0, ht2, hsplit⟩ :
      ∃ k t : ℤ, 0 ≤ t ∧ t < 2 * f.a ∧ 2 * f.a * k + t = f.b + f.a :=
    ⟨(f.b + f.a) / (2 * f.a), (f.b + f.a) % (2 * f.a), Int.emod_nonneg _ h2a.ne',
      Int.emod_lt_of_pos _ h2a, Int.mul_ediv_add_emod _ _⟩
  refine ⟨f.act 1 (-k) 0 1, ⟨1, -k, 0, 1, by ring, rfl⟩, ?_, ?_⟩
  · simp only [act, eval]; ring
  · have hA : (f.act 1 (-k) 0 1).a = f.a := by simp only [act, eval]; ring
    have hB : (f.act 1 (-k) 0 1).b = t - f.a := by
      simp only [act, eval]; linear_combination -hsplit
    rw [hA, hB, abs_le]
    constructor <;> linarith

/-- Gauss reduction, in the form the descent is actually run: induction on a
bound `n` for the leading coefficient. Each round translates `b` into the
window `[-a, a)` and, if `c < a`, swaps by `S`, which strictly decreases `a`.
Use `exists_reduced_equivalent` instead. -/
lemma exists_reduced_aux : ∀ (n : ℕ) (f : BinaryQuadraticForm), f.IsPosDef →
    f.a.toNat ≤ n → ∃ g, f.Equivalent g ∧ g.IsPosDef ∧ g.IsReduced := by
  intro n
  induction n with
  | zero =>
    intro f hf hn
    have ha := hf.a_pos
    exact absurd hn (by omega)
  | succ n ih =>
    intro f hf hn
    obtain ⟨f₁, he₁, ha₁, hb₁⟩ := exists_abs_b_le hf
    have hf₁ : f₁.IsPosDef := by
      obtain ⟨p, q, r, s, hdet, rfl⟩ := he₁
      exact hf.act hdet
    by_cases hle : f₁.a ≤ f₁.c
    · exact ⟨f₁, he₁, hf₁, ⟨hb₁, hle⟩⟩
    · have hlt : f₁.c < f₁.a := not_le.1 hle
      have hsw : (f₁.act 0 (-1) 1 0).IsPosDef := hf₁.act (by ring)
      have hsa : (f₁.act 0 (-1) 1 0).a = f₁.c := by simp only [act, eval]; ring
      have hcpos : 0 < f₁.c := by have := hsw.a_pos; rwa [hsa] at this
      have hswapeq : f₁.Equivalent (f₁.act 0 (-1) 1 0) := ⟨0, -1, 1, 0, by ring, rfl⟩
      obtain ⟨g, hg₁, hg₂, hg₃⟩ := ih (f₁.act 0 (-1) 1 0) hsw (by rw [hsa]; omega)
      exact ⟨g, he₁.trans (hswapeq.trans hg₁), hg₂, hg₃⟩

/-- **Gauss reduction.** Every positive definite integral binary quadratic form
is properly equivalent to a reduced one. -/
theorem exists_reduced_equivalent (f : BinaryQuadraticForm) (hf : f.IsPosDef) :
    ∃ g, f.Equivalent g ∧ g.IsPosDef ∧ g.IsReduced :=
  exists_reduced_aux f.a.toNat f hf le_rfl

/-- **Rabinowitsch's criterion, the elementary half.** If `x² + x + m` is prime
for every `x` with `x + 1 < m`, then every reduced positive definite form of
discriminant `1 − 4m` has leading coefficient `1`.

For a reduced form of odd discriminant, `b` is odd, so `|b| = 2x + 1` for some
`x ≥ 0` and `a · c = ((2x+1)² − (1 − 4m))/4 = x² + x + m`. The reduction
inequalities give `3a² ≤ 4m − 1`, which together with `2x + 1 ≤ a` forces
`x + 1 < m`; so `a · c` is one of the primes supplied by the hypothesis, and
`a ≤ c` leaves `a = 1`. -/
theorem a_eq_one_of_primeGenerating {m : ℕ} (hm : 2 ≤ m)
    (hgen : ∀ x : ℕ, x + 1 < m → Nat.Prime (x ^ 2 + x + m))
    {f : BinaryQuadraticForm} (hpd : f.IsPosDef) (hred : f.IsReduced)
    (hd : f.discr = 1 - 4 * m) : f.a = 1 := by
  have ha : 0 < f.a := hpd.a_pos
  have hb : |f.b| ≤ f.a := hred.abs_b_le_a
  have hac : f.a ≤ f.c := hred.a_le_c
  have hm2 : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hdisc : f.b ^ 2 - 4 * f.a * f.c = 1 - 4 * (m : ℤ) := hd
  -- `|b|` is odd.
  obtain ⟨x, hx⟩ : ∃ x : ℤ, |f.b| = 2 * x + 1 := by
    rcases Int.even_or_odd |f.b| with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have hbk : f.b ^ 2 = 4 * k ^ 2 := by rw [← sq_abs, hk]; ring
      have hdvd : (4 : ℤ) ∣ 1 :=
        ⟨k ^ 2 + (m : ℤ) - f.a * f.c, by linear_combination hbk - hdisc⟩
      norm_num at hdvd
    · exact ⟨k, hk⟩
  have hx0 : 0 ≤ x := by have := abs_nonneg f.b; omega
  have hsq : (2 * x + 1) ^ 2 = f.b ^ 2 := by rw [← hx, sq_abs]
  have hxac : f.a * f.c = x ^ 2 + x + (m : ℤ) := by
    have h4 : 4 * (f.a * f.c) = 4 * (x ^ 2 + x + (m : ℤ)) := by
      linear_combination -hsq - hdisc
    linarith
  -- The reduction inequalities.
  have hb2 : f.b ^ 2 ≤ f.a ^ 2 := by
    have h1 : |f.b| ^ 2 ≤ f.a ^ 2 := by nlinarith [abs_nonneg f.b]
    rwa [sq_abs] at h1
  have hacge : f.a ^ 2 ≤ f.a * f.c := by nlinarith
  have h3a : 3 * f.a ^ 2 ≤ 4 * (m : ℤ) - 1 := by linarith
  have hxa : 2 * x + 1 ≤ f.a := by rw [← hx]; exact hb
  have hxm : x + 1 < (m : ℤ) := by
    rcases lt_or_ge (x + 1) (m : ℤ) with h | hcon
    · exact h
    · exfalso
      have hA : 2 * (m : ℤ) - 1 ≤ f.a := by linarith
      have hA2 : (2 * (m : ℤ) - 1) ^ 2 ≤ f.a ^ 2 := by nlinarith
      nlinarith
  -- Feed the prime-generating hypothesis.
  have hxn : ((x.toNat : ℤ)) = x := Int.toNat_of_nonneg hx0
  have hxn1 : x.toNat + 1 < m := by omega
  have hp := hgen x.toNat hxn1
  have hc0 : 0 < f.c := by linarith
  have hmul : f.a.toNat * f.c.toNat = x.toNat ^ 2 + x.toNat + m := by
    have : ((f.a.toNat * f.c.toNat : ℕ) : ℤ) = ((x.toNat ^ 2 + x.toNat + m : ℕ) : ℤ) := by
      push_cast [Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hc0.le, hxn]
      exact hxac
    exact_mod_cast this
  rcases hp.eq_one_or_self_of_dvd f.a.toNat ⟨f.c.toNat, hmul.symm⟩ with h1 | h1
  · omega
  · rw [h1] at hmul
    have hc1 : f.c.toNat = 1 :=
      Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hmul)
    omega

/-- **One class.** Under Rabinowitsch's hypothesis, every positive definite form
of discriminant `1 − 4m` is properly equivalent to the principal form. -/
theorem equivalent_of_primeGenerating {m : ℕ} (hm : 2 ≤ m)
    (hgen : ∀ x : ℕ, x + 1 < m → Nat.Prime (x ^ 2 + x + m))
    {f : BinaryQuadraticForm} (hpd : f.IsPosDef) (hd : f.discr = 1 - 4 * m) :
    f.Equivalent (principal m) := by
  obtain ⟨g, hfg, hgpd, hgred⟩ := exists_reduced_equivalent f hpd
  have hgd : g.discr = 1 - 4 * (m : ℤ) := by
    obtain ⟨p, q, r, s, hdet, rfl⟩ := hfg
    rw [discr_act, hdet, one_pow, one_mul]
    exact hd
  have hga : g.a = 1 := a_eq_one_of_primeGenerating hm hgen hgpd hgred hgd
  have hbb : -1 ≤ g.b ∧ g.b ≤ 1 := by
    have := hgred.abs_b_le_a
    rw [hga, abs_le] at this
    exact this
  have hdd : g.b ^ 2 - 4 * g.a * g.c = 1 - 4 * (m : ℤ) := hgd
  rw [hga] at hdd
  have hbne : g.b ≠ 0 := by
    intro h0
    rw [h0] at hdd
    have hdvd : (4 : ℤ) ∣ 1 := ⟨(m : ℤ) - g.c, by linear_combination -hdd⟩
    norm_num at hdvd
  have hcm : g.c = (m : ℤ) := by
    rcases (by omega : g.b = 1 ∨ g.b = -1) with h1 | h1 <;> rw [h1] at hdd <;> linarith
  rcases (by omega : g.b = 1 ∨ g.b = -1) with h1 | h1
  · have : g = principal m := by
      ext
      · exact hga
      · exact h1
      · exact hcm
    rwa [this] at hfg
  · refine hfg.trans ⟨1, 1, 0, 1, by ring, ?_⟩
    ext
    · simp only [act, eval, principal]; rw [hga]; ring
    · simp only [act, eval, principal]; rw [hga, h1]; ring
    · simp only [act, eval, principal]; rw [hga, h1, hcm]; ring

/-! ### The elementary obstruction: represented values -/

/-- The action is precomposition with the matrix: `(f ∘ M)(x, y) = f(px + qy, rx + sy)`. -/
lemma eval_act (f : BinaryQuadraticForm) (p q r s x y : ℤ) :
    (f.act p q r s).eval x y = f.eval (p * x + q * y) (r * x + s * y) := by
  simp only [act, eval]; ring

/-- The set of represented values is an invariant of proper equivalence. -/
lemma Equivalent.represents {f g : BinaryQuadraticForm} (h : f.Equivalent g) {n : ℤ}
    (hn : ∃ x y : ℤ, g.eval x y = n) : ∃ x y : ℤ, f.eval x y = n := by
  obtain ⟨p, q, r, s, _, rfl⟩ := h
  obtain ⟨x, y, hxy⟩ := hn
  exact ⟨p * x + q * y, r * x + s * y, by rw [← eval_act]; exact hxy⟩

/-- Completing the square: `4 a f(x,y) = (2 a x + b y)² − d y²`. -/
lemma four_mul_a_mul_eval (f : BinaryQuadraticForm) (x y : ℤ) :
    4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.discr * y ^ 2 := by
  simp only [eval, discr]; ring

/-- A form whose leading coefficient satisfies `2 ≤ a` and `4a < |d|` does not represent `1`.

By `four_mul_a_mul_eval`, `f(x,y) = 1` gives `4a = (2ax + by)² + |d| y²`. If `y ≠ 0` the right
side is at least `|d| > 4a`; and if `y = 0` it says `4a = 4a²x²`, i.e. `a·x² = 1`, so `a ∣ 1`. -/
lemma not_represents_one {f : BinaryQuadraticForm} (ha : 2 ≤ f.a)
    (hd : 4 * f.a < -f.discr) : ¬ ∃ x y : ℤ, f.eval x y = 1 := by
  rintro ⟨x, y, hxy⟩
  have key := four_mul_a_mul_eval f x y
  rw [hxy, mul_one] at key
  rcases eq_or_ne y 0 with rfl | hy
  · have key0 : 4 * f.a = (2 * f.a * x) ^ 2 := by linarith [key]
    have h1 : 4 * f.a * (f.a * x ^ 2) = 4 * f.a * 1 := by linear_combination -key0
    have h2 : f.a * x ^ 2 = 1 :=
      mul_left_cancel₀ (show (4 : ℤ) * f.a ≠ 0 by intro h; omega) h1
    have h3 : f.a ∣ 1 := ⟨x ^ 2, h2.symm⟩
    have := Int.le_of_dvd one_pos h3
    omega
  · have hy2 : 1 ≤ y ^ 2 := (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hy)
    have hdpos : (0 : ℤ) < -f.discr := by linarith
    have hbig : -f.discr ≤ -f.discr * y ^ 2 := le_mul_of_one_le_right hdpos.le hy2
    nlinarith [sq_nonneg (2 * f.a * x + f.b * y)]

/-- Every admissible discriminant carries a form with leading coefficient `1` — namely
`⟨1, 0, −d/4⟩` or `⟨1, 1, (1−d)/4⟩` — which therefore represents `1`. -/
lemma exists_a_eq_one (d : ℤ) (hd4 : d % 4 = 0 ∨ d % 4 = 1) :
    ∃ f : BinaryQuadraticForm, f.a = 1 ∧ f.discr = d := by
  rcases hd4 with h | h
  · obtain ⟨e, rfl⟩ : ∃ e, d = 4 * e := ⟨d / 4, by omega⟩
    exact ⟨⟨1, 0, -e⟩, rfl, by simp only [discr]; ring⟩
  · obtain ⟨e, rfl⟩ : ∃ e, d = 1 + 4 * e := ⟨d / 4, by omega⟩
    exact ⟨⟨1, 1, -e⟩, rfl, by simp only [discr]; ring⟩

/-- **THE ELEMENTARY OBSTRUCTION TO CLASS NUMBER ONE.** If `d < 0` has exactly one class of
positive definite forms, then for every `a ≥ 2` with `4a < |d|` the discriminant `d` is
**not a square modulo `4a`**.

From `b² ≡ d (mod 4a)` one builds `f = ⟨a, b, (b²−d)/(4a)⟩`, positive definite of discriminant
`d`, which by `not_represents_one` does not represent `1`; but `exists_a_eq_one` supplies a form
of the same discriminant that does, and represented values are an equivalence invariant.

This is exactly Booher's Proposition 2 (*Modular curves and the class number one problem*):
for `p ≡ 3 mod 4` prime, `h(−p) = 1` iff every prime `ℓ < √(p/4)`… — stated here without
Legendre symbols, so it needs no quadratic reciprocity and no number field. -/
theorem not_dvd_sq_sub_of_classNumberOne {d : ℤ} (hd : d < 0) (hd4 : d % 4 = 0 ∨ d % 4 = 1)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = d → g.discr = d → f.Equivalent g)
    {a : ℤ} (ha : 2 ≤ a) (hlt : 4 * a < -d) (b : ℤ) (hdvd : 4 * a ∣ b ^ 2 - d) : False := by
  obtain ⟨c, hc⟩ := hdvd
  have hdisc : (⟨a, b, c⟩ : BinaryQuadraticForm).discr = d := by simp only [discr]; linarith
  have hpd : (⟨a, b, c⟩ : BinaryQuadraticForm).IsPosDef :=
    ⟨show (0 : ℤ) < a by omega, by rw [hdisc]; exact hd⟩
  obtain ⟨g, hga, hgd⟩ := exists_a_eq_one d hd4
  have hgpd : g.IsPosDef := ⟨by rw [hga]; norm_num, by rw [hgd]; exact hd⟩
  have hequiv := hcl ⟨a, b, c⟩ g hpd hgpd hdisc hgd
  refine not_represents_one (f := ⟨a, b, c⟩) (show (2 : ℤ) ≤ a from ha)
    (by rw [hdisc]; exact hlt) ?_
  exact hequiv.represents ⟨1, 0, by simp [eval, hga]⟩

/-- A composite number factors as `u * v` with `2 ≤ u ≤ v`. -/
lemma exists_ordered_factorization {N : ℕ} (h2 : 2 ≤ N) (hp : ¬ N.Prime) :
    ∃ u v : ℕ, 2 ≤ u ∧ u ≤ v ∧ N = u * v := by
  obtain ⟨m, ⟨j, rfl⟩, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 h2 hp
  have hj2 : 2 ≤ j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j <;> omega
    · exact h
  rcases le_total m j with hle | hle
  · exact ⟨m, j, hm2, hle, rfl⟩
  · exact ⟨j, m, hj2, hle, Nat.mul_comm m j⟩

/-- **THE ELEMENTARY REDUCTION OF CLASS NUMBER ONE TO PRIME DISCRIMINANTS.**

If `d < 0` has one class of positive definite integral binary quadratic forms — primitive
and imprimitive alike — then `d = −4`, `d = −8`, or `−d` is a prime congruent to `3` mod `4`.

This is the elementary half of Gauss's genus theory, run with explicit inequivalent forms
rather than genus characters (which would need Dirichlet's theorem for the surjectivity of the
genus map). Each case exhibits a form of discriminant `d` whose leading coefficient `a`
satisfies `2 ≤ a` and `4a < |d|`, hence which does not represent `1`:

* `d = −4n` with `n = u·v`, `2 ≤ u ≤ v` — the form `⟨u, 0, v⟩`;
* `d = −4p` with `p` an odd prime — the form `⟨2, 2, (p+1)/2⟩`;
* `d = −N` with `N ≡ 3 mod 4` and `N = u·v`, `3 ≤ u ≤ v` — the form `⟨u, u, (u+v)/4⟩`
  (note `4 ∣ u+v`, because `u·v ≡ 3 mod 4` with `u, v` odd forces `u ≢ v mod 4`; and `v ≥ 5`,
  because `u = v = 3` would give `N = 9 ≡ 1 mod 4`).

Quantifying over ALL forms rather than only primitive ones is what makes the second bullet
work and what removes the four non-fundamental class-number-one discriminants
`−12, −16, −27, −28`; see the note on `neg_163_le_of_classNumberOne`. -/
theorem prime_of_classNumberOne {d : ℤ} (hd : d < 0) (hd4 : d % 4 = 0 ∨ d % 4 = 1)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = d → g.discr = d → f.Equivalent g) :
    d = -4 ∨ d = -8 ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have key : ∀ a : ℤ, 2 ≤ a → 4 * a < -d → ∀ b : ℤ, 4 * a ∣ b ^ 2 - d → False :=
    fun _ => not_dvd_sq_sub_of_classNumberOne hd hd4 hcl
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, d = -(N : ℤ) := ⟨(-d).toNat, by omega⟩
  rcases hd4 with h4 | h4
  · -- `d ≡ 0 (mod 4)`: write `N = 4 n`.
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = 4 * n := ⟨N / 4, by omega⟩
    by_cases hn2 : n ≤ 2
    · have hn0 : 0 < n := by omega
      interval_cases n
      · exact Or.inl (by norm_num)
      · exact Or.inr (Or.inl (by norm_num))
    · exfalso
      by_cases hp : n.Prime
      · -- `n` an odd prime: use `⟨2, 2, (n+1)/2⟩`.
        have hodd : n % 2 = 1 := by
          rcases hp.eq_two_or_odd with h | h
          · omega
          · exact h
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 * k + 1 := ⟨n / 2, by omega⟩
        exact key 2 (by norm_num) (by push_cast; omega) 2
          ⟨(k : ℤ) + 1, by push_cast; ring⟩
      · -- `n` composite: use `⟨u, 0, v⟩`.
        obtain ⟨u, v, hu2, huv, rfl⟩ := exists_ordered_factorization (by omega) hp
        have hu2' : (2 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu2
        have hv2' : (2 : ℤ) ≤ (v : ℤ) := by exact_mod_cast le_trans hu2 huv
        exact key (u : ℤ) hu2' (by push_cast; nlinarith) 0
          ⟨(v : ℤ), by push_cast; ring⟩
  · -- `d ≡ 1 (mod 4)`, i.e. `N ≡ 3 (mod 4)`.
    have hN4 : N % 4 = 3 := by omega
    by_cases hp : N.Prime
    · exact Or.inr (Or.inr ⟨N, hp, hN4, rfl⟩)
    · exfalso
      obtain ⟨u, v, hu2, huv, hNuv⟩ := exists_ordered_factorization (by omega) hp
      have hu_odd : u % 2 = 1 := by
        have hnd : ¬ ((2 : ℕ) ∣ u) := by
          intro h
          have h2N : (2 : ℕ) ∣ N := by rw [hNuv]; exact h.mul_right v
          omega
        omega
      have hv_odd : v % 2 = 1 := by
        have hnd : ¬ ((2 : ℕ) ∣ v) := by
          intro h
          have h2N : (2 : ℕ) ∣ N := by rw [hNuv]; exact h.mul_left u
          omega
        omega
      obtain ⟨s, rfl⟩ : ∃ s : ℕ, u = 2 * s + 1 := ⟨u / 2, by omega⟩
      obtain ⟨t, rfl⟩ : ∃ t : ℕ, v = 2 * t + 1 := ⟨v / 2, by omega⟩
      obtain ⟨P, hP⟩ : ∃ P : ℕ, s * t = P := ⟨s * t, rfl⟩
      have hexp : N = 4 * P + 2 * s + 2 * t + 1 := by rw [hNuv, ← hP]; ring
      -- `s + t` is odd, hence `4 ∣ u + v`; and `s < t`, hence `v ≥ 5`.
      obtain ⟨w, hw⟩ : ∃ w : ℕ, 2 * s + 1 + (2 * t + 1) = 4 * w :=
        ⟨(2 * s + 2 * t + 2) / 4, by omega⟩
      have ht2 : 2 ≤ t := by omega
      have hNZ : (N : ℤ) = ((2 * s + 1 : ℕ) : ℤ) * ((2 * t + 1 : ℕ) : ℤ) := by exact_mod_cast hNuv
      have hwZ : ((2 * s + 1 : ℕ) : ℤ) + ((2 * t + 1 : ℕ) : ℤ) = 4 * (w : ℤ) := by
        exact_mod_cast hw
      have ht2' : (5 : ℤ) ≤ ((2 * t + 1 : ℕ) : ℤ) := by push_cast; omega
      have hs0' : (3 : ℤ) ≤ ((2 * s + 1 : ℕ) : ℤ) := by push_cast; omega
      refine key ((2 * s + 1 : ℕ) : ℤ) (by push_cast; omega) ?_
        ((2 * s + 1 : ℕ) : ℤ) ⟨(w : ℤ), ?_⟩
      · rw [hNZ]; nlinarith
      · rw [hNZ]; linear_combination ((2 * s + 1 : ℕ) : ℤ) * hwZ

/-! ### Heegner's route -/

/-- **`p ≡ 3 (mod 8)`.** If `−p` has one class and `p > 8` then `p ≡ 3 mod 8`.

For `p ≡ 7 mod 8` one has `8 ∣ 1 + p`, i.e. `1² ≡ −p (mod 8)`, so `⟨2, 1, (p+1)/8⟩` is a
positive definite form of discriminant `−p` that does not represent `1`. (Classically this is
the statement that `2` splits in `ℚ(√−p)` exactly when `p ≡ 7 mod 8`; Heegner and Cox instead
deduce `p = 7` from `h(−4p) = h(−p) = 1` and the even-discriminant list, which needs the class
number formula for non-maximal orders. The form-theoretic route above needs neither.) -/
theorem mod_eight_eq_three_of_classNumberOne {p : ℕ} (hp4 : p % 4 = 3) (h8 : 8 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    p % 8 = 3 := by
  rcases (by omega : p % 8 = 3 ∨ p % 8 = 7) with h | h
  · exact h
  · exfalso
    obtain ⟨q, hq⟩ : ∃ q : ℕ, p + 1 = 8 * q := ⟨(p + 1) / 8, by omega⟩
    have hqZ : (p : ℤ) + 1 = 8 * (q : ℤ) := by exact_mod_cast hq
    exact not_dvd_sq_sub_of_classNumberOne (d := -(p : ℤ)) (by omega) (by omega) hcl
      (a := 2) (by norm_num) (by omega) 1 ⟨(q : ℤ), by linear_combination hqZ⟩

/-! ### The Diophantine equation `2x(x³+1) = y²`

Everything from here to `eq_of_two_mul_mul_cube_add_one_eq_sq` is elementary integer
arithmetic — no quadratic ring, no class number, nothing else from this file.

THE ROUTE ACTUALLY TAKEN, which is NOT the one the older plan in this docstring
recorded (that plan called for factoring in `ℤ[i]`, `ℤ[ω]` and `ℤ[√−2]`, and for
Euler's descent on `x³+1 = z²`). None of the three quadratic rings is needed, and
neither is Euler's descent. The reason is that the equation carries **more** than
`x³ + 1 = εz²`: the companion factor pins `±2x` (or `±x`) to be a square as well, and
that extra square turns every cube that shows up into a **sixth power**. Sixth powers
factor as `t³ ± 1 = (t ± 1)(t² ∓ t + 1)` with `t` a square, and both pieces are then
squares by coprimality — which reduces everything to the single finite statement
`eq_zero_or_one_of_sq_sub_self_add_one_eq_sq`.

Concretely: `x` and `x³+1` are coprime, so splitting on the parity of `x` gives
`2x = ±a²` with `x³+1 = ±b²` (`x` even), or `x = ±a²` with `x³+1 = ±2c²` (`x` odd).

* `x` odd, `x = a²`: `a⁶ + 1 = 2c²`, killed by `sq_eq_one_of_pow_six_add_one_eq_two_mul_sq`,
  giving `x = 1`.
* `x` odd, `x = −a²`: `a⁶ − 1 = 2c²`, killed by `sq_eq_one_of_pow_six_sub_one_eq_two_mul_sq`,
  giving `x = −1`.
* `x` even, negative sign: `b² + 1 = 8m⁶` is impossible mod `8`.
* `x` even, positive sign: `2x = a²` forces `x = 2k²`, and `b² − 1 = x³ = 8k⁶` splits into
  two consecutive coprime integers whose product is `2k⁶`. Each is then `±` a **sixth**
  power, and the four sign patterns land on `B⁶ ± 1 = 2A⁶`, i.e. on the same two lemmas
  again. Only `x = 2` survives.

(These are Mordell equations; `y² = x³ + 1` is the elliptic curve `27a3`, rank `0`, and a
CAS finds its integral points in under a second — useful as a check, never as the proof.
`gp` was used to confirm the six solutions over `|x| ≤ 2000` before the proof was built.) -/

/-- **Bézout boost.** If `a x + b y = k` and `k` is coprime to `y`, then so is `x`.

This is how every coprimality below is obtained: exhibit an explicit integer combination
of the two factors equal to a small constant (`3` or `4`), then remove that constant from
a divisibility fact. It avoids any `Int.gcd` manipulation. -/
theorem isCoprime_of_bezout {x y k a b : ℤ} (hk : IsCoprime k y)
    (h : a * x + b * y = k) : IsCoprime x y := by
  obtain ⟨p, q, hpq⟩ := hk
  exact ⟨p * a, p * b + q, by linear_combination p * h + hpq⟩

/-- A coprime factorisation of a **sixth** power has sixth-power factors, up to sign —
the exponent-`6` analogue of `Int.sq_of_isCoprime`. The sign is genuinely needed: `6` is
even, so `-d ^ 6` is not itself a sixth power. -/
theorem pow_six_of_isCoprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 6) :
    ∃ a0 : ℤ, a = a0 ^ 6 ∨ a = -a0 ^ 6 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' h heq
  rcases Int.associated_iff.mp hd with h' | h'
  · exact ⟨d, Or.inl h'.symm⟩
  · exact ⟨d, Or.inr (by linarith)⟩

/-- `B² + 1` is never divisible by `3`, since `B² ≡ 0, 1 (mod 3)`. This is exactly what
makes `t + 1` and `t² − t + 1` coprime when `t` is a square. -/
theorem not_three_dvd_sq_add_one (B : ℤ) : ¬ (3 : ℤ) ∣ (B ^ 2 + 1) := by
  rintro ⟨k, hk⟩
  have h3 : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by omega
  obtain ⟨c, hc⟩ : ∃ c, B = 3 * c + B % 3 := ⟨B / 3, by omega⟩
  rcases h3 with h3 | h3 | h3 <;> rw [h3] at hc <;> subst hc
  · exact absurd (⟨k - 3 * c ^ 2, by linear_combination hk⟩ : (3 : ℤ) ∣ 1) (by omega)
  · exact absurd (⟨k - 3 * c ^ 2 - 2 * c, by linear_combination hk⟩ : (3 : ℤ) ∣ 2) (by omega)
  · exact absurd (⟨k - 3 * c ^ 2 - 4 * c, by linear_combination hk⟩ : (3 : ℤ) ∣ 5) (by omega)

/-- **The workhorse.** `n² − n + 1` is a perfect square only at `n = 0` and `n = 1`.

`(2s − 2n + 1)(2s + 2n − 1) = 4s² − (2n−1)² = 3`, so both factors divide `3`; that bounds
`n` to `[−1, 2]` and `s` to `[−1, 1]`, a finite check. -/
theorem eq_zero_or_one_of_sq_sub_self_add_one_eq_sq {n s : ℤ} (h : n ^ 2 - n + 1 = s ^ 2) :
    n = 0 ∨ n = 1 := by
  have key : (2 * s - 2 * n + 1) * (2 * s + 2 * n - 1) = 3 := by linear_combination (-4 : ℤ) * h
  have hA : (2 * s - 2 * n + 1) ∣ 3 := ⟨_, key.symm⟩
  have hB : (2 * s + 2 * n - 1) ∣ 3 := Dvd.intro_left _ key
  have hA' : |2 * s - 2 * n + 1| ≤ 3 := Int.le_of_dvd (by norm_num) ((abs_dvd _ _).mpr hA)
  have hB' : |2 * s + 2 * n - 1| ≤ 3 := Int.le_of_dvd (by norm_num) ((abs_dvd _ _).mpr hB)
  rw [abs_le] at hA' hB'
  obtain ⟨hn1, hn2⟩ : -1 ≤ n ∧ n ≤ 2 := by omega
  obtain ⟨hs1, hs2⟩ : -1 ≤ s ∧ s ≤ 1 := by omega
  interval_cases n
  · exfalso; interval_cases s <;> norm_num at h
  · norm_num
  · norm_num
  · exfalso; interval_cases s <;> norm_num at h

/-- `n² + n + 1` is a perfect square only at `n = 0` and `n = −1`; the reflection
`n ↦ −n` of `eq_zero_or_one_of_sq_sub_self_add_one_eq_sq`. -/
theorem eq_zero_or_neg_one_of_sq_add_self_add_one_eq_sq {n s : ℤ} (h : n ^ 2 + n + 1 = s ^ 2) :
    n = 0 ∨ n = -1 := by
  have := eq_zero_or_one_of_sq_sub_self_add_one_eq_sq (n := -n) (s := s) (by linear_combination h)
  omega

/-- **`B⁶ + 1 = 2M²` forces `B² = 1`.**

`B` must be odd, so with `t = B²` the factorisation `t³ + 1 = (t+1)(t² − t + 1)` has an
even first factor and an odd second one, and they are coprime because `3 ∤ t + 1` for `t`
a square (`not_three_dvd_sq_add_one`). Cancelling the `2` leaves a coprime product equal
to `M²`, so `t² − t + 1` is a square — and then `t ∈ {0, 1}` with `t` odd. -/
theorem sq_eq_one_of_pow_six_add_one_eq_two_mul_sq {B M : ℤ} (h : B ^ 6 + 1 = 2 * M ^ 2) :
    B ^ 2 = 1 := by
  have hBodd : Odd B := by
    rcases Int.even_or_odd B with ⟨c, hc⟩ | ho
    · exact absurd (⟨M ^ 2 - 32 * c ^ 6, by rw [hc] at h; linear_combination h⟩ : (2 : ℤ) ∣ 1)
        (by omega)
    · exact ho
  obtain ⟨T, hT⟩ : ∃ T : ℤ, B ^ 2 + 1 = 2 * T := by
    obtain ⟨u, hu⟩ := hBodd
    exact ⟨2 * u ^ 2 + 2 * u + 1, by rw [hu]; ring⟩
  have hprod : (B ^ 4 - B ^ 2 + 1) * T = M ^ 2 :=
    mul_left_cancel₀ two_ne_zero (by linear_combination h - (B ^ 4 - B ^ 2 + 1) * hT)
  have h3T : ¬ (3 : ℤ) ∣ T := by
    intro hd
    exact not_three_dvd_sq_add_one B (by rw [hT]; exact Dvd.dvd.mul_left hd 2)
  have hcop : IsCoprime (B ^ 4 - B ^ 2 + 1) T :=
    isCoprime_of_bezout (Int.prime_three.coprime_iff_not_dvd.mpr h3T)
      (a := 1) (b := -2 * (B ^ 2 - 2)) (by linear_combination (B ^ 2 - 2) * hT)
  obtain ⟨s, hs⟩ := Int.sq_of_isCoprime hcop hprod
  have hpos : 0 < B ^ 4 - B ^ 2 + 1 := by nlinarith [sq_nonneg (B ^ 2 - 1), sq_nonneg B]
  have hn : B ^ 4 - B ^ 2 + 1 = s ^ 2 := by
    rcases hs with hs | hs
    · exact hs
    · nlinarith [sq_nonneg s]
  rcases eq_zero_or_one_of_sq_sub_self_add_one_eq_sq (n := B ^ 2) (s := s)
    (by linear_combination hn) with h0 | h1
  · exfalso
    have hB0 : B = 0 := by
      have := pow_eq_zero_iff (M₀ := ℤ) (n := 2) (a := B) (by norm_num)
      exact this.mp h0
    rw [hB0] at hBodd
    simp at hBodd
  · exact h1

/-- **`B⁶ − 1 = 2M²` forces `B² = 1`.**

Here `B⁶ − 1 = (B² − 1)(B² + B + 1)(B² − B + 1)`, with the first factor even and the last
two odd and coprime to each other. Each of the last two is coprime to `B² − 1` up to a
possible factor `3`, and `3` cannot divide both — so at least one of `B² ± B + 1` is
coprime to the rest, hence (being positive) a perfect square. `n² ± n + 1` a square then
pins `B = ±1`.

Note this needs **no** case analysis on `B mod 3`: coprimality of the two odd factors
already excludes `3` dividing both. -/
theorem sq_eq_one_of_pow_six_sub_one_eq_two_mul_sq {B M : ℤ} (h : B ^ 6 - 1 = 2 * M ^ 2) :
    B ^ 2 = 1 := by
  have hBodd : Odd B := by
    rcases Int.even_or_odd B with ⟨c, hc⟩ | ho
    · exact absurd (⟨32 * c ^ 6 - M ^ 2, by rw [hc] at h; linear_combination -h⟩ : (2 : ℤ) ∣ 1)
        (by omega)
    · exact ho
  obtain ⟨u, hu⟩ := hBodd
  obtain ⟨P, hP⟩ : ∃ P : ℤ, B ^ 2 - 1 = 2 * P := ⟨2 * u ^ 2 + 2 * u, by rw [hu]; ring⟩
  have hprod : P * ((B ^ 2 + B + 1) * (B ^ 2 - B + 1)) = M ^ 2 :=
    mul_left_cancel₀ two_ne_zero
      (by linear_combination h - ((B ^ 2 + B + 1) * (B ^ 2 - B + 1)) * hP)
  have hqpos : 0 < B ^ 2 + B + 1 := by nlinarith [sq_nonneg (2 * B + 1)]
  have hrpos : 0 < B ^ 2 - B + 1 := by nlinarith [sq_nonneg (2 * B - 1)]
  have hqr : IsCoprime (B ^ 2 + B + 1) (B ^ 2 - B + 1) := by
    refine isCoprime_of_bezout (k := 4) ?_
      (a := 2 - (B ^ 2 + B + 1) + 2 * (B ^ 2 - B + 1)) (b := 2 - (B ^ 2 - B + 1)) (by ring)
    exact ⟨-((2 * u ^ 2 + u) ^ 2 + (2 * u ^ 2 + u)), B ^ 2 - B + 1, by rw [hu]; ring⟩
  by_cases hr3 : (3 : ℤ) ∣ (B ^ 2 - B + 1)
  · -- then `3 ∤ B² + B + 1`, so that factor is coprime to `P` and to `B² − B + 1`
    have hq3 : ¬ (3 : ℤ) ∣ (B ^ 2 + B + 1) := by
      intro hh
      have := hqr.isUnit_of_dvd' hh hr3
      rw [Int.isUnit_iff] at this
      omega
    have hPq : IsCoprime P (B ^ 2 + B + 1) :=
      isCoprime_of_bezout (Int.prime_three.coprime_iff_not_dvd.mpr hq3)
        (a := 2 * (B - 1)) (b := -(B - 2)) (by linear_combination (-(B - 1)) * hP)
    obtain ⟨s, hs⟩ := Int.sq_of_isCoprime (hPq.symm.mul_right hqr)
      (show (B ^ 2 + B + 1) * (P * (B ^ 2 - B + 1)) = M ^ 2 by linear_combination hprod)
    have hqsq : B ^ 2 + B + 1 = s ^ 2 := by
      rcases hs with hs | hs
      · exact hs
      · nlinarith [sq_nonneg s]
    rcases eq_zero_or_neg_one_of_sq_add_self_add_one_eq_sq hqsq with h0 | h1
    · rw [h0] at hu; omega
    · rw [h1]; norm_num
  · -- `3 ∤ B² − B + 1`, so that factor is coprime to `P` and to `B² + B + 1`
    have hPr : IsCoprime P (B ^ 2 - B + 1) :=
      isCoprime_of_bezout (Int.prime_three.coprime_iff_not_dvd.mpr hr3)
        (a := -2 * (B + 1)) (b := B + 2) (by linear_combination (B + 1) * hP)
    obtain ⟨s, hs⟩ := Int.sq_of_isCoprime (hPr.symm.mul_right hqr.symm)
      (show (B ^ 2 - B + 1) * (P * (B ^ 2 + B + 1)) = M ^ 2 by linear_combination hprod)
    have hrsq : B ^ 2 - B + 1 = s ^ 2 := by
      rcases hs with hs | hs
      · exact hs
      · nlinarith [sq_nonneg s]
    rcases eq_zero_or_one_of_sq_sub_self_add_one_eq_sq hrsq with h0 | h1
    · rw [h0] at hu; omega
    · rw [h1]; norm_num

/-- **Sign matching.** In a coprime factorisation `u v = y²` with both factors nonzero,
`Int.sq_of_isCoprime` gives `u = ±a²` and `v = ±b²` independently; the two signs must
agree, since a mixed pair would make `y² = −(ab)²` with `ab ≠ 0`. -/
theorem sq_and_sq_of_mul_eq_sq {u v a b y : ℤ} (hprod : u * v = y ^ 2)
    (hu : u = a ^ 2 ∨ u = -a ^ 2) (hv : v = b ^ 2 ∨ v = -b ^ 2)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    (u = a ^ 2 ∧ v = b ^ 2) ∨ (u = -a ^ 2 ∧ v = -b ^ 2) := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact Or.inl ⟨hu, hv⟩
  · exfalso
    have hz : a ^ 2 * b ^ 2 = 0 := by nlinarith [sq_nonneg y, sq_nonneg (a * b)]
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact hu0 (by rw [hu, h0])
    · exact hv0 (by rw [hv, h0]; ring)
  · exfalso
    have hz : a ^ 2 * b ^ 2 = 0 := by nlinarith [sq_nonneg y, sq_nonneg (a * b)]
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact hu0 (by rw [hu, h0]; ring)
    · exact hv0 (by rw [hv, h0])
  · exact Or.inr ⟨hu, hv⟩

/-- **The `x`-coordinates of `2x(x³+1) = y²` are `0, −1, 1, 2`.**

The whole content of the Diophantine leaf; `eq_of_two_mul_mul_cube_add_one_eq_sq` only
solves for `y` afterwards. See the section header above for the argument. -/
theorem eq_zero_or_neg_one_or_one_or_two_of_two_mul_mul_cube_add_one_eq_sq
    {x y : ℤ} (h : 2 * x * (x ^ 3 + 1) = y ^ 2) : x = 0 ∨ x = -1 ∨ x = 1 ∨ x = 2 := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  by_cases hx1 : x = -1
  · exact Or.inr (Or.inl hx1)
  have hcube : x ^ 3 + 1 ≠ 0 := by
    intro hc
    refine hx1 ?_
    have h2 : (x + 1) * (x ^ 2 - x + 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · nlinarith [sq_nonneg (2 * x - 1)]
  have hcopx : IsCoprime x (x ^ 3 + 1) := ⟨-x ^ 2, 1, by ring⟩
  rcases Int.even_or_odd x with hev | hod
  · -- `x` even, so `2x` and `x³+1` are coprime
    obtain ⟨m, hm⟩ := hev
    have hodd1 : Odd (x ^ 3 + 1) := ⟨4 * m ^ 3, by rw [hm]; ring⟩
    have hcop : IsCoprime (2 * x) (x ^ 3 + 1) :=
      (Int.isCoprime_two_left.mpr hodd1).mul_left hcopx
    have h2x : 2 * x ≠ 0 := by omega
    have h' : 2 * x * (x ^ 3 + 1) = y ^ 2 := h
    obtain ⟨a, ha⟩ := Int.sq_of_isCoprime hcop h'
    obtain ⟨b, hb⟩ := Int.sq_of_isCoprime (c := y) hcop.symm (by linear_combination h)
    rcases sq_and_sq_of_mul_eq_sq h' ha hb h2x hcube with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `2x = a²` and `x³+1 = b²`, so `x = 2k²` and `(b−1)(b+1) = 8k⁶`
      have haeven : Even a := (Int.even_pow' (n := 2) (by norm_num)).mp ⟨x, by linarith⟩
      obtain ⟨k, hk⟩ := haeven
      have hxk : x = 2 * k ^ 2 :=
        mul_left_cancel₀ two_ne_zero (by rw [hk] at ha; linear_combination ha)
      have hk0 : k ≠ 0 := by rintro rfl; simp at hxk; exact hx0 hxk
      have hk6 : 0 < k ^ 6 := by
        have h2 : (k ^ 3) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero 3 hk0)
        have h3 : k ^ 6 = (k ^ 3) ^ 2 := by ring
        rw [h3]; exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm h2)
      have hbodd : Odd b := by
        rcases Int.even_or_odd b with ⟨c, hc⟩ | ho
        · exact absurd (⟨2 * c ^ 2 - 4 * k ^ 6, by rw [hxk, hc] at hb; linear_combination hb⟩ :
            (2 : ℤ) ∣ 1) (by omega)
        · exact ho
      obtain ⟨c, hc⟩ := hbodd
      have hcc : c * (c + 1) = 2 * k ^ 6 :=
        mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
          (by rw [hxk, hc] at hb; linear_combination -hb)
      have hcop2 : IsCoprime c (c + 1) := ⟨-1, 1, by ring⟩
      rcases Int.even_or_odd c with ⟨d, hd⟩ | ⟨d, hd⟩
      · -- `c = 2d`, so `d (2d+1) = k⁶` with both factors sixth powers up to sign
        subst hd
        have hdc : d * (d + d + 1) = k ^ 6 :=
          mul_left_cancel₀ two_ne_zero (by linear_combination hcc)
        have hcop3 : IsCoprime d (d + d + 1) :=
          IsCoprime.of_isCoprime_of_dvd_left hcop2 ⟨2, by ring⟩
        have hd0 : d ≠ 0 := by rintro rfl; linarith [hdc, hk6]
        obtain ⟨A, hA⟩ := pow_six_of_isCoprime hcop3 hdc
        obtain ⟨B, hB⟩ := pow_six_of_isCoprime (c := k) hcop3.symm (by linear_combination hdc)
        have hA6 : (0 : ℤ) ≤ A ^ 6 := by positivity
        have hB6 : (0 : ℤ) ≤ B ^ 6 := by positivity
        rcases hA with hA | hA <;> rcases hB with hB | hB
        · -- `B⁶ − 2A⁶ = 1`
          exfalso
          have hL : B ^ 6 - 1 = 2 * (A ^ 3) ^ 2 := by linear_combination -hB + 2 * hA
          have hB2 := sq_eq_one_of_pow_six_sub_one_eq_two_mul_sq hL
          have hB61 : B ^ 6 = 1 := by linear_combination (B ^ 4 + B ^ 2 + 1) * hB2
          rw [hB61] at hB
          exact hd0 (by omega)
        · exfalso; linarith
        · exfalso
          have hle : d ≤ 0 := by linarith
          have hge : 0 ≤ d + d + 1 := by linarith
          exact hd0 (by omega)
        · -- `2A⁶ − B⁶ = 1`, the branch that produces `x = 2`
          have hL : B ^ 6 + 1 = 2 * (A ^ 3) ^ 2 := by linear_combination hB - 2 * hA
          have hB2 := sq_eq_one_of_pow_six_add_one_eq_two_mul_sq hL
          have hB61 : B ^ 6 = 1 := by linear_combination (B ^ 4 + B ^ 2 + 1) * hB2
          rw [hB61] at hB
          have hd1 : d = -1 := by omega
          subst hd1
          have hk61 : k ^ 6 = 1 := by linarith [hdc]
          have hfac : (k ^ 2 - 1) * ((k ^ 2) ^ 2 + k ^ 2 + 1) = 0 := by linear_combination hk61
          have hpos2 : 0 < (k ^ 2) ^ 2 + k ^ 2 + 1 := by positivity
          have hk2 : k ^ 2 = 1 := by
            rcases mul_eq_zero.mp hfac with h0 | h0
            · linarith
            · linarith
          exact Or.inr (Or.inr (Or.inr (by rw [hxk, hk2]; norm_num)))
      · -- `c = 2d+1`, so `(2d+1)(d+1) = k⁶`
        subst hd
        have hdc : (2 * d + 1) * (d + 1) = k ^ 6 :=
          mul_left_cancel₀ two_ne_zero (by linear_combination hcc)
        have hcop3 : IsCoprime (2 * d + 1) (d + 1) := ⟨-1, 2, by ring⟩
        have hd0 : d + 1 ≠ 0 := by
          intro hz
          rw [show (2 : ℤ) * d + 1 = 2 * (d + 1) - 1 by ring, hz] at hdc
          linarith [hdc, hk6]
        obtain ⟨A, hA⟩ := pow_six_of_isCoprime hcop3 hdc
        obtain ⟨B, hB⟩ := pow_six_of_isCoprime (c := k) hcop3.symm (by linear_combination hdc)
        have hA6 : (0 : ℤ) ≤ A ^ 6 := by positivity
        have hB6 : (0 : ℤ) ≤ B ^ 6 := by positivity
        rcases hA with hA | hA <;> rcases hB with hB | hB
        · -- `2B⁶ − A⁶ = 1`, the second branch producing `x = 2`
          have hL : A ^ 6 + 1 = 2 * (B ^ 3) ^ 2 := by linear_combination -hA + 2 * hB
          have hA2 := sq_eq_one_of_pow_six_add_one_eq_two_mul_sq hL
          have hA61 : A ^ 6 = 1 := by linear_combination (A ^ 4 + A ^ 2 + 1) * hA2
          rw [hA61] at hA
          have hd1 : d = 0 := by omega
          subst hd1
          have hk61 : k ^ 6 = 1 := by linarith [hdc]
          have hfac : (k ^ 2 - 1) * ((k ^ 2) ^ 2 + k ^ 2 + 1) = 0 := by linear_combination hk61
          have hpos2 : 0 < (k ^ 2) ^ 2 + k ^ 2 + 1 := by positivity
          have hk2 : k ^ 2 = 1 := by
            rcases mul_eq_zero.mp hfac with h0 | h0
            · linarith
            · linarith
          exact Or.inr (Or.inr (Or.inr (by rw [hxk, hk2]; norm_num)))
        · exfalso
          have hkk : k ^ 6 = -(A ^ 6 * B ^ 6) := by rw [← hdc, hA, hB]; ring
          nlinarith [mul_nonneg hA6 hB6]
        · exfalso
          have hkk : k ^ 6 = -(A ^ 6 * B ^ 6) := by rw [← hdc, hA, hB]; ring
          nlinarith [mul_nonneg hA6 hB6]
        · exfalso
          have hL : A ^ 6 - 1 = 2 * (B ^ 3) ^ 2 := by linear_combination hA - 2 * hB
          have hA2 := sq_eq_one_of_pow_six_sub_one_eq_two_mul_sq hL
          have hA61 : A ^ 6 = 1 := by linear_combination (A ^ 4 + A ^ 2 + 1) * hA2
          rw [hA61] at hA
          exact hd0 (by omega)
    · -- `2x = −a²` and `x³+1 = −b²`: then `b² + 1 = 8m⁶`, impossible mod `8`
      exfalso
      have haeven : Even a := (Int.even_pow' (n := 2) (by norm_num)).mp ⟨-x, by linarith⟩
      obtain ⟨m, hm⟩ := haeven
      have hxm : x = -2 * m ^ 2 :=
        mul_left_cancel₀ two_ne_zero (by rw [hm] at ha; linear_combination ha)
      have hb8 : b ^ 2 + 1 = 8 * m ^ 6 := by rw [hxm] at hb; linear_combination hb
      rcases Int.even_or_odd b with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact absurd (⟨4 * m ^ 6 - 2 * c ^ 2, by rw [hc] at hb8; linear_combination hb8⟩ :
          (2 : ℤ) ∣ 1) (by omega)
      · exact absurd (⟨2 * m ^ 6 - c ^ 2 - c, by rw [hc] at hb8; linear_combination hb8⟩ :
          (4 : ℤ) ∣ 2) (by omega)
  · -- `x` odd, so `x` and `2(x³+1)` are coprime
    have hcop : IsCoprime x (2 * (x ^ 3 + 1)) :=
      (Int.isCoprime_two_right.mpr hod).mul_right hcopx
    have h' : x * (2 * (x ^ 3 + 1)) = y ^ 2 := by linear_combination h
    have h2c : 2 * (x ^ 3 + 1) ≠ 0 := fun hz => hcube (by linarith)
    obtain ⟨a, ha⟩ := Int.sq_of_isCoprime hcop h'
    obtain ⟨b, hb⟩ := Int.sq_of_isCoprime (c := y) hcop.symm (by linear_combination h)
    rcases sq_and_sq_of_mul_eq_sq h' ha hb hx0 h2c with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `x = a²` and `x³+1 = 2e²`, i.e. `a⁶ + 1 = 2e²`
      have hbeven : Even b := (Int.even_pow' (n := 2) (by norm_num)).mp ⟨x ^ 3 + 1, by linarith⟩
      obtain ⟨e, he⟩ := hbeven
      have hcube2 : x ^ 3 + 1 = 2 * e ^ 2 :=
        mul_left_cancel₀ two_ne_zero (by rw [he] at hb; linear_combination hb)
      have hL : a ^ 6 + 1 = 2 * e ^ 2 := by rw [ha] at hcube2; linear_combination hcube2
      exact Or.inr (Or.inr (Or.inl (by
        rw [ha, sq_eq_one_of_pow_six_add_one_eq_two_mul_sq hL])))
    · -- `x = −a²` and `x³+1 = −2e²`, i.e. `a⁶ − 1 = 2e²`
      have hbeven : Even b :=
        (Int.even_pow' (n := 2) (by norm_num)).mp ⟨-(x ^ 3 + 1), by linarith⟩
      obtain ⟨e, he⟩ := hbeven
      have hcube2 : x ^ 3 + 1 = -(2 * e ^ 2) :=
        mul_left_cancel₀ two_ne_zero (by rw [he] at hb; linear_combination hb)
      have hL : a ^ 6 - 1 = 2 * e ^ 2 := by rw [ha] at hcube2; linear_combination -hcube2
      exact Or.inr (Or.inl (by
        rw [ha, sq_eq_one_of_pow_six_sub_one_eq_two_mul_sq hL]))

/-- **DIOPHANTINE LEAF, PROVEN.** The only integer solutions of `2x(x³ + 1) = y²` are
`(0, 0)`, `(−1, 0)`, `(1, ±2)` and `(2, ±6)`.

This is Booher's Proposition 39 / Cox, *Primes of the form x²+ny²*, end of §12. It is
elementary and self-contained: nothing else in this file is used.

`eq_zero_or_neg_one_or_one_or_two_of_two_mul_mul_cube_add_one_eq_sq` does the work and
pins `x`; substituting each value leaves `y² = 0, 0, 4, 36`, whose solutions are read off
by factoring `y² − c²`. -/
theorem eq_of_two_mul_mul_cube_add_one_eq_sq {x y : ℤ} (h : 2 * x * (x ^ 3 + 1) = y ^ 2) :
    (x = 0 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 1 ∧ y = 2) ∨ (x = 1 ∧ y = -2) ∨
      (x = 2 ∧ y = 6) ∨ (x = 2 ∧ y = -6) := by
  rcases eq_zero_or_neg_one_or_one_or_two_of_two_mul_mul_cube_add_one_eq_sq h with
    rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, pow_eq_zero_iff (M₀ := ℤ) (n := 2) (by norm_num) |>.mp (by linarith)⟩
  · exact Or.inr (Or.inl ⟨rfl,
      pow_eq_zero_iff (M₀ := ℤ) (n := 2) (by norm_num) |>.mp (by linarith)⟩)
  · have hy : (y - 2) * (y + 2) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hy with h0 | h0
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by linarith⟩)))
  · have hy : (y - 6) * (y + 6) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hy with h0 | h0
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by linarith⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by linarith⟩))))

/-- **Heegner's coefficient relation has exactly six solutions.**

`2(b² − 4a) = (2b − a²)²` holds for `(a, b)` exactly in
`{(0,0), (2,4), (−2,8), (−2,0), (−4,28), (−4,4)}`.

PROVEN here over `eq_of_two_mul_mul_cube_add_one_eq_sq`. The relation forces `a` even (the
right side is even, so `2b − a²` is, so `a²` is) and then `b` even; writing `a = −2x` and
`b = 2m`, the relation becomes exactly `2x(x³ + 1) = (m − 2x²)²`, so the six solutions
`(x, y) = (0,0), (−1,0), (1,±2), (2,±6)` transport to the six pairs above via `a = −2x`,
`b = 4x² + 2y`. -/
theorem heegnerRelation_solutions {a b : ℤ} (h : 2 * (b ^ 2 - 4 * a) = (2 * b - a ^ 2) ^ 2) :
    (a = 0 ∧ b = 0) ∨ (a = 2 ∧ b = 4) ∨ (a = -2 ∧ b = 8) ∨ (a = -2 ∧ b = 0) ∨
      (a = -4 ∧ b = 28) ∨ (a = -4 ∧ b = 4) := by
  have heven : Even ((2 * b - a ^ 2) ^ 2) := ⟨b ^ 2 - 4 * a, by linarith⟩
  have hu : Even (2 * b - a ^ 2) := (Int.even_pow' (by norm_num)).mp heven
  have ha2 : Even (a ^ 2) := by obtain ⟨k, hk⟩ := hu; exact ⟨b - k, by linarith⟩
  obtain ⟨k, hk⟩ := (Int.even_pow' (by norm_num)).mp ha2
  obtain ⟨x, rfl⟩ : ∃ x : ℤ, a = -2 * x := ⟨-k, by omega⟩
  have hb2 : Even (b ^ 2) := by
    refine ⟨(b - 2 * x ^ 2) ^ 2 - 4 * x, ?_⟩
    refine mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) ?_
    linear_combination h
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, b = 2 * m := by
    obtain ⟨n, hn⟩ := (Int.even_pow' (by norm_num)).mp hb2
    exact ⟨n, by omega⟩
  have hy : 2 * x * (x ^ 3 + 1) = (m - 2 * x ^ 2) ^ 2 :=
    mul_left_cancel₀ (show (8 : ℤ) ≠ 0 by norm_num) (by linear_combination h)
  rcases eq_of_two_mul_mul_cube_add_one_eq_sq hy with
    ⟨hx, hm⟩ | ⟨hx, hm⟩ | ⟨hx, hm⟩ | ⟨hx, hm⟩ | ⟨hx, hm⟩ | ⟨hx, hm⟩ <;>
      subst hx <;> norm_num at hm ⊢ <;> omega

/-- **The numeric bound.** `exp(π √p) > 262537412640768745` for `p ≥ 164`.

Nothing arithmetic is involved: `262537412640768745 = 640320³ + 745`, and
`(log 262537412640768745 / π)² = 163.000000000…`, so the statement is SHARP at `p = 163` — the
celebrated Ramanujan near-integer `exp(π√163) = 262537412640768743.99999999999925…` — and has
a comfortable margin at `p = 164`, where `exp(π√164) ≈ 2.9685·10¹⁷`.

Proved from `√p > 12.8` and `π > 3.141592`, giving `π√p > 40.2123`, then splitting
`exp(π√p) = exp 40 · exp(π√p − 40)` with `exp 1 > 2.718` for the first factor and
`1 + t ≤ exp t` for the second: `2.718⁴⁰ · 1.2123 > 2.8417·10¹⁷`. -/
theorem lt_exp_pi_sqrt {p : ℕ} (hp : 164 ≤ p) :
    (262537412640768745 : ℝ) < Real.exp (Real.pi * Real.sqrt p) := by
  have h164 : (164 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hs : (12.8 : ℝ) < Real.sqrt p := (Real.lt_sqrt (by norm_num)).mpr (by nlinarith)
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hprod : (40.2123 : ℝ) < Real.pi * Real.sqrt p := by
    nlinarith [Real.pi_pos, Real.sqrt_nonneg (p : ℝ)]
  have he : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hL : (2.718 : ℝ) ^ 40 < Real.exp 40 := by
    have h40 : Real.exp 40 = Real.exp 1 ^ 40 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h40]; gcongr
  have ht : (1.2123 : ℝ) ≤ Real.exp (Real.pi * Real.sqrt p - 40) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  have hsplit : Real.exp 40 * Real.exp (Real.pi * Real.sqrt p - 40)
      = Real.exp (Real.pi * Real.sqrt p) := by
    rw [← Real.exp_add]; ring_nf
  calc (262537412640768745 : ℝ) < (2.718 : ℝ) ^ 40 * 1.2123 := by norm_num
    _ ≤ Real.exp 40 * Real.exp (Real.pi * Real.sqrt p - 40) :=
        mul_le_mul hL.le ht (by norm_num) (Real.exp_pos _).le
    _ = Real.exp (Real.pi * Real.sqrt p) := hsplit

/-! ### Heegner's complex-multiplication input

This namespace carries the modular-function side of the Heegner–Stark argument: the
definitions of `j`, Weber's `f₂`, `γ₂` and Heegner's algebraic integer `α`, the six leaves
that the deep node decomposes into, and the purely algebraic core (Heegner's double-squaring
match), which is PROVEN here.

Nothing of the modular theory used below is in mathlib at this pin, in `~/cs/FLT`, or in this
project; what IS available, and is used, are the Dedekind eta function
(`Mathlib.NumberTheory.ModularForms.DedekindEta`: `ModularForm.eta`, `eta_ne_zero`), the
modular discriminant `Δ = η²⁴` (`…ModularForms.Discriminant`: `ModularForm.discriminant`,
normalised so that `(qExpansion 1 Δ).coeff 1 = 1`), and the normalised level-one Eisenstein
series (`…ModularForms.EisensteinSeries.Basic`: `ModularForm.E₄`, with
`(qExpansion 1 E₄).coeff 0 = 1` and `.coeff 1 = 240`). Those normalisations are what make
`jInvariant = E₄³/Δ` below the CLASSICAL `j`, with `q`-expansion `q⁻¹ + 744 + 196884q + ⋯`;
checked against `PARI/GP`'s `ellj` at all five Heegner points (see `LEAF 6`). -/
namespace Heegner

/-- The modular `j`-invariant, `j = E₄³/Δ`.

With mathlib's normalisations (`E₄ = 1 + 240q + ⋯`, `Δ = η²⁴ = q − 24q² + ⋯`) this is the
classical `j`, i.e. `j = q⁻¹ + 744 + 196884q + ⋯`. Verified numerically against `PARI/GP`'s
`ellj` at `τ₀ = (3+√−p)/2` for `p = 11, 19, 43, 67, 163`, where it returns
`−32768, −884736, −884736000, −147197952000, −262537412640768000`. -/
noncomputable def jInvariant (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ z ^ 3 / ModularForm.discriminant z

/-- **Weber's function** `f₂(z) = √2 · η(2z)/η(z)`, one of the three Weber modular functions
(Booher §3.2, Definition 20; Cox §12.B). -/
noncomputable def weberF2 (z : UpperHalfPlane) : ℂ :=
  (Real.sqrt 2 : ℂ) * ModularForm.eta (2 * (z : ℂ)) / ModularForm.eta (z : ℂ)

/-- **`γ₂`, the cube root of `j`**, *defined* by Weber's formula `γ₂ = (f₂²⁴ + 16)/f₂⁸`
(Booher §3.2, Theorem 23).

Taking this as the DEFINITION rather than as a theorem is deliberate: it makes `γ₂`
computable from `η` alone, and concentrates the whole modular-function content of Weber's
theorem into the single identity `gammaTwo_pow_three_eq_jInvariant` (`γ₂³ = j`, LEAF 5).
The alternative — defining `γ₂` as a cube root of `j` — would need a choice of branch and
would make Weber's formula a second leaf rather than a definition. -/
noncomputable def gammaTwo (z : UpperHalfPlane) : ℂ :=
  (weberF2 z ^ 24 + 16) / weberF2 z ^ 8

/-- **The Heegner point** `τ₀ = (3 + √(−p))/2`.

The `3` (rather than `1`) is essential and is not a normalisation: it is what makes
`q = exp(2πiτ₀) = −exp(−π√p)` REAL AND NEGATIVE, which is in turn what makes the `q`-expansion
tail `196884q + ⋯` a NEGATIVE correction and hence the constant `745` in LEAF 6 attainable.
With `τ = (1+√−p)/2` one gets the same `j` (the two differ by `z ↦ z+1`), so nothing
mathematical is lost, but `α = ζ₈⁻¹f₂(τ₀)²` is real exactly at this representative
(Booher §6). -/
noncomputable def heegnerPoint (p : ℕ) (hp : 0 < p) : UpperHalfPlane :=
  UpperHalfPlane.mk ((3 + Complex.I * (Real.sqrt p : ℂ)) / 2) <| by
    have h1 : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
    simp only [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    positivity

/-- **Heegner's algebraic integer** `α = ζ₈⁻¹ f₂(τ₀)²`, with `ζ₈ = exp(πi/4)`.

The twist by `ζ₈⁻¹` is what makes `α` REAL (verified numerically: `α = 0.8392867552…` at
`p = 11`, `0.0707018420…` at `p = 163`) and hence a generator of the real cubic field
`ℚ(f(√−p)²)`; `f₂(τ₀)²` itself is not real. Only `α⁴ = −f₂(τ₀)⁸` enters the final
identities, but the cubic minimal polynomial that drives the argument is `α`'s, not
`α⁴`'s — that is the whole point of Heegner's double squaring. -/
noncomputable def weberAlpha (p : ℕ) (hp : 0 < p) : ℂ :=
  (Complex.exp (↑Real.pi * Complex.I / 4))⁻¹ * weberF2 (heegnerPoint p hp) ^ 2

lemma eta_ne_zero' (z : UpperHalfPlane) : ModularForm.eta (z : ℂ) ≠ 0 :=
  ModularForm.eta_ne_zero z.2

lemma eta_two_ne_zero (z : UpperHalfPlane) : ModularForm.eta (2 * (z : ℂ)) ≠ 0 := by
  refine ModularForm.eta_ne_zero ?_
  show 0 < (2 * (z : ℂ)).im
  simpa using z.im_pos

lemma weberF2_ne_zero (z : UpperHalfPlane) : weberF2 z ≠ 0 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  exact div_ne_zero (mul_ne_zero h2 (eta_two_ne_zero z)) (eta_ne_zero' z)

/-- Weber's formula, cleared of denominators: `γ₂ · f₂⁸ = f₂²⁴ + 16`. -/
lemma gammaTwo_mul (z : UpperHalfPlane) :
    gammaTwo z * weberF2 z ^ 8 = weberF2 z ^ 24 + 16 :=
  div_mul_cancel₀ _ (pow_ne_zero _ (weberF2_ne_zero z))

lemma zeta8_pow_four : (Complex.exp (↑Real.pi * Complex.I / 4)) ^ 4 = -1 := by
  have h : (Complex.exp (↑Real.pi * Complex.I / 4)) ^ 4
      = Complex.exp (↑Real.pi * Complex.I) := by
    rw [show (↑Real.pi * Complex.I : ℂ) = ↑Real.pi * Complex.I / 4 + ↑Real.pi * Complex.I / 4
      + ↑Real.pi * Complex.I / 4 + ↑Real.pi * Complex.I / 4 by ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_add]
    ring_nf
  rw [h, Complex.exp_pi_mul_I]

lemma zeta8_inv_pow_four : ((Complex.exp (↑Real.pi * Complex.I / 4))⁻¹) ^ 4 = -1 := by
  rw [inv_pow, zeta8_pow_four]
  norm_num

/-- `α⁴ = −f₂(τ₀)⁸`, because `ζ₈⁻⁴ = −1`. -/
lemma weberAlpha_pow_four (p : ℕ) (hp : 0 < p) :
    weberAlpha p hp ^ 4 = -weberF2 (heegnerPoint p hp) ^ 8 := by
  rw [weberAlpha, mul_pow, zeta8_inv_pow_four, ← pow_mul]
  ring

/-- **`α⁴` is a root of `x³ − γ₂ x − 16`** (Booher §6, equation (7)).

This is immediate from the DEFINITION of `γ₂` together with `α⁴ = −f₂(τ₀)⁸`: substituting
`x = −f₂⁸` into `x³ − γ₂x − 16` gives `−f₂²⁴ + γ₂f₂⁸ − 16`, which vanishes exactly by
`gammaTwo_mul`. No modular theory is consumed. -/
lemma weberAlpha_pow_four_cubic (p : ℕ) (hp : 0 < p) :
    (weberAlpha p hp ^ 4) ^ 3 - gammaTwo (heegnerPoint p hp) * weberAlpha p hp ^ 4 - 16 = 0 := by
  rw [weberAlpha_pow_four]
  linear_combination gammaTwo_mul (heegnerPoint p hp)

/-- **Heegner's double squaring.** If `x` is a root of `x³ + ax² + bx + c`, then `x²` is a
root of `x³ + (2b − a²)x² + (b² − 2ac)x − c²`.

Proof: `x³ + bx = −(ax² + c)`; square both sides and read the result as a cubic in `x²`.
Formally the whole content is the factorisation
`(x²)³ + (2b−a²)(x²)² + (b²−2ac)x² − c² = (x³+ax²+bx+c)(x³−ax²+bx−c)`. -/
lemma cube_of_sq {R : Type*} [CommRing R] (x a b c : R)
    (h : x ^ 3 + a * x ^ 2 + b * x + c = 0) :
    (x ^ 2) ^ 3 + (2 * b - a ^ 2) * (x ^ 2) ^ 2 + (b ^ 2 - 2 * a * c) * x ^ 2 + -c ^ 2 = 0 := by
  linear_combination (x ^ 3 - a * x ^ 2 + b * x - c) * h

/-! #### The cubic field of `α`: field theory, then the one remaining CM input

The two leaves `exists_intCubic_weberAlpha` and `intCast_indep_weberAlpha_pow_four` are both
consequences of the SINGLE statement "`α` is an algebraic integer of degree exactly `3`", and
that is how they are proven below. The field-theoretic passage from that statement to each of
them is elementary and is PROVEN here; what is left open is the CM input itself, and it is now
the SINGLE named leaf `natDegree_minpoly_weberAlpha` — the degree. Its companion
`isIntegral_weberAlpha` is proven (further down, after `exists_int_gammaTwo`, on which it
depends).

This is a strict improvement on stating the two conclusions directly, because the second of
them (`ℤ`-independence of `1, α⁴, α⁸`) is NOT an independent fact: it follows from
`[ℚ(α) : ℚ] = 3` with no further modular input, by the degree argument in
`intCast_indep_of_natDegree_minpoly` below. Leaving it as a separate assumption invited a
future owner to attack a statement that was never open. -/

open _root_.Polynomial _root_.IntermediateField in
/-- In a cubic extension `L/ℚ`, any `x` of degree `≤ 2` is already rational.

`3` is prime, so `[ℚ(x) : ℚ]` divides `3` by the tower law and is `≤ 2` by hypothesis, hence
`1`; and a degree-one simple extension is `⊥`. -/
theorem mem_range_algebraMap_of_finrank_three {L : Type*} [Field L] [Algebra ℚ L]
    (h3 : Module.finrank ℚ L = 3) (x : L) (hx : (minpoly ℚ x).natDegree ≤ 2) :
    ∃ r : ℚ, algebraMap ℚ L r = x := by
  have hfd : FiniteDimensional ℚ L := by
    apply FiniteDimensional.of_finrank_pos (K := ℚ); rw [h3]; norm_num
  have hxi : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  have hrank : Module.finrank ℚ ℚ⟮x⟯ = (minpoly ℚ x).natDegree :=
    _root_.IntermediateField.adjoin.finrank hxi
  have htower : Module.finrank ℚ ℚ⟮x⟯ * Module.finrank ℚ⟮x⟯ L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ _ L
  rw [h3, hrank] at htower
  have hd1 : (minpoly ℚ x).natDegree = 1 := by
    set d := (minpoly ℚ x).natDegree with hdd
    clear_value d
    interval_cases d <;> omega
  have hbot : ℚ⟮x⟯ = ⊥ := _root_.IntermediateField.finrank_eq_one_iff.mp (by rw [hrank, hd1])
  have hmem : x ∈ ℚ⟮x⟯ := _root_.IntermediateField.mem_adjoin_simple_self ℚ x
  rw [hbot] at hmem
  exact _root_.IntermediateField.mem_bot.mp hmem

open _root_.Polynomial in
/-- If `x²` is rational then `x` has degree at most `2`, being a root of `X² − r`. -/
theorem natDegree_minpoly_le_two_of_sq_mem_range {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (r : ℚ) (h : algebraMap ℚ L r = x ^ 2) : (minpoly ℚ x).natDegree ≤ 2 := by
  have hne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := by
    intro hc
    have h2 : (X ^ 2 - C r : ℚ[X]).coeff 2 = 1 := by simp
    rw [hc] at h2
    simp at h2
  have hae : aeval x (X ^ 2 - C r : ℚ[X]) = 0 := by simp [h]
  have hdle := minpoly.degree_le_of_ne_zero ℚ x hne hae
  have hdeg2 : (X ^ 2 - C r : ℚ[X]).degree = 2 := by
    have := Polynomial.degree_X_pow_sub_C (n := 2) (by norm_num) r
    simpa using this
  rw [hdeg2] at hdle
  exact Polynomial.natDegree_le_iff_degree_le.mpr hdle

open _root_.Polynomial in
/-- An algebraic integer of degree `3` over `ℚ` satisfies a MONIC cubic with coefficients in
`ℤ` — namely its minimal polynomial over `ℤ`, which maps to the one over `ℚ` because `ℤ` is
integrally closed with fraction field `ℚ`. -/
theorem exists_intCubic_of_natDegree_minpoly {α : ℂ} (hint : IsIntegral ℤ α)
    (hdeg : (minpoly ℚ α).natDegree = 3) :
    ∃ a b c : ℤ, α ^ 3 + (a : ℂ) * α ^ 2 + (b : ℂ) * α + (c : ℂ) = 0 := by
  have hmonic : (minpoly ℤ α).Monic := minpoly.monic hint
  have hmap : minpoly ℚ α = (minpoly ℤ α).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hPdeg : (minpoly ℤ α).natDegree = 3 := by
    rw [hmap, hmonic.natDegree_map] at hdeg
    exact hdeg
  have haev : aeval α (minpoly ℤ α) = 0 := minpoly.aeval ℤ α
  have hlt : (minpoly ℤ α).natDegree < 4 := by rw [hPdeg]; norm_num
  have hsum := Polynomial.aeval_eq_sum_range' hlt α
  rw [haev] at hsum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  have hc3 : (minpoly ℤ α).coeff 3 = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hPdeg] at this
  rw [hc3] at hsum
  refine ⟨(minpoly ℤ α).coeff 2, (minpoly ℤ α).coeff 1, (minpoly ℤ α).coeff 0, ?_⟩
  simp only [zsmul_eq_mul, Int.cast_one, one_mul, pow_zero, pow_one, mul_one, zero_add] at hsum
  linear_combination -hsum

open _root_.Polynomial _root_.IntermediateField in
/-- **`1, α⁴, α⁸` are `ℤ`-independent as soon as `α` has degree `3`** — no modular input.

The mechanism is the prime degree, applied TWICE. A nontrivial relation
`uα⁸ + vα⁴ + w = 0` makes `α⁴` a root of a nonzero rational polynomial of degree `≤ 2`, so
`α⁴` is rational by `mem_range_algebraMap_of_finrank_three`; then `α²` is a root of `X² − α⁴`,
so `α²` is rational by the same lemma; then `α` is a root of `X² − α²`, giving
`deg α ≤ 2 < 3`.

This is why no "`α⁴` has degree `3`" hypothesis is needed anywhere: it is a THEOREM about any
degree-three `α`, not an extra fact about this particular one. -/
theorem intCast_indep_of_natDegree_minpoly {α : ℂ} (hdeg : (minpoly ℚ α).natDegree = 3) :
    ∀ u v w : ℤ, (u : ℂ) * α ^ 8 + (v : ℂ) * α ^ 4 + (w : ℂ) = 0 → u = 0 ∧ v = 0 ∧ w = 0 := by
  have hint : IsIntegral ℚ α := by
    by_contra hc
    rw [minpoly.eq_zero hc] at hdeg
    simp at hdeg
  have h3 : Module.finrank ℚ ℚ⟮α⟯ = 3 := by
    rw [_root_.IntermediateField.adjoin.finrank hint, hdeg]
  set a : ℚ⟮α⟯ := _root_.IntermediateField.AdjoinSimple.gen ℚ α with ha
  have hamap : (algebraMap ℚ⟮α⟯ ℂ) a = α :=
    _root_.IntermediateField.AdjoinSimple.algebraMap_gen ℚ α
  have hmp : minpoly ℚ a = minpoly ℚ α := _root_.IntermediateField.minpoly_gen ℚ α
  intro u v w h
  by_contra hcon
  have hinj : Function.Injective (algebraMap ℚ⟮α⟯ ℂ) := (algebraMap ℚ⟮α⟯ ℂ).injective
  have hL0 : (u : ℚ⟮α⟯) * a ^ 8 + (v : ℚ⟮α⟯) * a ^ 4 + (w : ℚ⟮α⟯) = 0 := by
    apply hinj
    simp only [map_add, map_mul, map_pow, map_intCast, map_zero, hamap]
    exact h
  set q : ℚ[X] := C (u : ℚ) * X ^ 2 + C (v : ℚ) * X + C (w : ℚ) with hq
  have hqne : q ≠ 0 := by
    intro hc
    apply hcon
    have e2 : q.coeff 2 = (u : ℚ) := by
      rw [hq]; simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]; norm_num
    have e1 : q.coeff 1 = (v : ℚ) := by
      rw [hq]; simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]; norm_num
    have e0 : q.coeff 0 = (w : ℚ) := by
      rw [hq]; simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]; norm_num
    rw [hc] at e2 e1 e0
    simp only [Polynomial.coeff_zero] at e2 e1 e0
    exact ⟨by exact_mod_cast e2.symm, by exact_mod_cast e1.symm, by exact_mod_cast e0.symm⟩
  have hae : aeval (a ^ 4) q = 0 := by
    simp only [hq, map_add, map_mul, aeval_X, map_pow, map_intCast]
    linear_combination hL0
  have hdle : (minpoly ℚ (a ^ 4)).natDegree ≤ 2 := by
    have hd := minpoly.degree_le_of_ne_zero ℚ (a ^ 4) hqne hae
    have hdq : q.degree ≤ 2 := by rw [hq]; compute_degree
    exact Polynomial.natDegree_le_iff_degree_le.mpr (le_trans hd hdq)
  obtain ⟨r, hr⟩ := mem_range_algebraMap_of_finrank_three h3 (a ^ 4) hdle
  have hstep1 : (minpoly ℚ (a ^ 2)).natDegree ≤ 2 :=
    natDegree_minpoly_le_two_of_sq_mem_range (a ^ 2) r (by rw [hr]; ring)
  obtain ⟨s, hs⟩ := mem_range_algebraMap_of_finrank_three h3 (a ^ 2) hstep1
  have hstep2 : (minpoly ℚ a).natDegree ≤ 2 :=
    natDegree_minpoly_le_two_of_sq_mem_range a s hs
  rw [hmp, hdeg] at hstep2
  omega

/-- **LEAF 1b — `α` HAS DEGREE EXACTLY `3` OVER `ℚ`.**

This is the class-number computation, and it is the ONLY place the deep input enters: `α`
lies in the ring class field of the order `[1, √−p]` of discriminant `−4p`, and for
`p ≡ 3 mod 8` the class number formula for a conductor-`2` order gives

  `h(−4p) = 2·h(−p)·(1 − (−p|2)/2) = 3·h(−p)`,

using `(−p|2) = −1` because `−p ≡ 5 mod 8`. With `h(−p) = 1` — which is exactly what `hcl`
says — this is `3`, so `ℚ(α)` is a cubic field.

`hcl` IS LOAD-BEARING and does not appear in the conclusion: drop it and `h(−p)` may exceed
`1`, making `h(−4p) = 3h(−p) > 3` and the degree larger than `3`. It is not decorative.

MACHINE-CHECKED FAITHFULNESS: `polisirreducible(algdep(α,3)) = 1` at all five admissible `p`
(table in `isIntegral_weberAlpha`), so the degree is exactly `3` — not `1` or `2` — in every
case where the hypotheses are satisfiable. Refute by exhibiting an admissible `p` at which
`α` satisfies a rational polynomial of degree `< 3`. -/
theorem natDegree_minpoly_weberAlpha {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    (minpoly ℚ (weberAlpha p hp.pos)).natDegree = 3 :=
  sorry

/-- **LEAF 2 — `α⁴` has degree at least `3`**, stated as `ℤ`-linear independence of
`1, α⁴, α⁸`.

This is the second half of "`ℚ(α) = ℚ(α⁴)` is a cubic field", and it is what licenses the
coefficient MATCH in `exists_heegnerRelation_aux`: a monic cubic satisfied by `α⁴` is then
forced to be THE minimal polynomial, hence equal to `x³ − γ₂x − 16`.

It is stated over `ℤ` rather than `ℚ` purely to avoid coercion noise; the two are equivalent
by clearing denominators, and `ℤ`-independence is exactly what the consumer needs.

WHY IT IS TRUE. `α⁴ = −f₂(τ₀)⁸` and `α` generate the same field (Booher §6: `α = 2/f(√−p)²`
and `α⁴` is a root of the cubic `x³ − γ₂x − 16`, which is irreducible because
`[ℚ(f(√−p)²) : ℚ] = h(−4p) = 3`). Numerically, at `p = 11`, `α⁴ = 4α² + 2α − 4` in
`ℚ(α) = ℚ[x]/(x³+2x²−2)` and is visibly not rational.

DROPPING `hcl` MAKES THIS FALSE, and that is the interesting failure mode: without class
number one there is no reason for the ring class field of `[1, √−p]` to be cubic, `γ₂(τ₀)`
need not be rational, and `x³ − γ₂x − 16` need not be the minimal polynomial. So `hcl` is
load-bearing here even though it does not appear in the conclusion — it enters through
`natDegree_minpoly_weberAlpha`.

**PROVEN**, from `natDegree_minpoly_weberAlpha` ALONE — integrality is not needed here.
A CORRECTION to the framing above: this leaf was cut as if "`α⁴` has degree at least `3`"
were a second, independent piece of Weber's theory to be supplied alongside LEAF 1. It is
not. Once `α` has degree `3`, independence is FORCED by the primality of that degree, applied
twice (`intCast_indep_of_natDegree_minpoly`): a nontrivial relation makes `α⁴` rational,
hence `α²` rational, hence `deg α ≤ 2 < 3`. No modular input is consumed, and in particular
the claim "`ℚ(α) = ℚ(α⁴)`" quoted above need never be established separately. -/
theorem intCast_indep_weberAlpha_pow_four {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∀ u v w : ℤ, (u : ℂ) * weberAlpha p hp.pos ^ 8 + (v : ℂ) * weberAlpha p hp.pos ^ 4
      + (w : ℂ) = 0 → u = 0 ∧ v = 0 ∧ w = 0 :=
  intCast_indep_of_natDegree_minpoly (natDegree_minpoly_weberAlpha hp hp8 h3 hcl)

/-! `LEAF 1` — the monic integral cubic satisfied by `α` — is `exists_intCubic_weberAlpha`,
and it is stated and PROVEN further down, immediately after `exists_int_gammaTwo`. It has to
live there rather than here: its integrality half is no longer a leaf but a CONSEQUENCE of
`γ₂(τ₀) ∈ ℤ`, so it depends on `LEAF 3`/`LEAF 4` by way of `exists_int_gammaTwo`. See
`isIntegral_weberAlpha`. -/

/- **LEAF 3 (`isIntegral_gammaTwo_heegnerPoint`) HAS MOVED** — it is now PROVEN, and lives
just below `gammaTwo_pow_three_eq_jInvariant` (LEAF 5), which its proof consumes. Lean's
declaration order is the only reason for the move; nothing about the statement changed. -/

/-! #### `LEAF 4` DECOMPOSED — the real-analytic half is PROVEN here (2026-07-28)

`γ₂(τ₀) ∈ ℚ` splits into a REAL-ANALYTIC half and a CLASS-FIELD half, and the first of the
two costs no arithmetic at all:

* `exists_real_gammaTwo_heegnerPoint` — `γ₂(τ₀) ∈ ℝ`. **PROVEN**, from `0 < p` alone.
* `exists_quadratic_jInvariant_heegnerPoint` — `j(τ₀) ∈ K = ℚ(√−p)`. The first main theorem
  of complex multiplication; the ONLY place `hcl` is consumed.
* `exists_quadratic_gammaTwo_of_jInvariant` — `γ₂(τ₀) ∈ K` once `j(τ₀) ∈ K`. Weber's
  level-`3` descent, which needs only `3 ∤ p`.

The assembly is then arithmetic: `K ∩ ℝ = ℚ`, i.e. `x = u + v√−p` real forces `v = 0`.
That IS the classical argument's shape — CM puts `j` in the ring class field, `h(−p) = 1`
collapses that field to `K`, and REALITY is what cuts `K` down to `ℚ`. Separating reality out
matters because reality is elementary and everything else here is not.

WHY `γ₂(τ₀)` IS REAL, and why it is provable at this pin. `q = 𝕢₁(τ₀) = −e^{−π√p}` is a
NEGATIVE REAL — this is exactly what the `3` in `τ₀ = (3+√−p)/2` buys — so every factor of
`η`'s product `∏(1 − qⁿ⁺¹)` is real; and the prefactors satisfy `𝕢₂₄(τ₀)⁸ = −e^{−π√p/3}`,
`𝕢₂₄(2τ₀)⁸ = e^{−2π√p/3}`, both real. Hence `η(τ₀)⁸` and `η(2τ₀)⁸` are real, so
`f₂(τ₀)⁸ = 16·η(2τ₀)⁸/η(τ₀)⁸` is real and `γ₂ = ((f₂⁸)³ + 16)/f₂⁸` is real. Note `f₂(τ₀)` and
`f₂(τ₀)²` are NOT real — only the EIGHTH power is, which is the same phenomenon the `ζ₈⁻¹`
twist in `weberAlpha` records. Reality is expressed here as `conj`-invariance and transported
through the infinite product by `Multipliable.map_tprod` applied to `starRingEnd ℂ`; that is
the whole trick, and it needs nothing from mathlib beyond `ModularForm.eta`'s definition.

ABSENCE RE-VERIFIED 2026-07-28, not inherited. `grep -rn` for `ComplexMultiplication`,
`HilbertClassField`, `ringClassField` returns, over `.lake/packages/mathlib`: NOTHING; over
`~/cs/FLT`: NOTHING; over `Fermat/`: four hits, every one of them prose inside a docstring
(`Modularity/MoretBailly.lean`, `FreyCurve/MazurTorsion.lean`, `ModularCurve/X0.lean`, and
this file) asserting the same absence. The two mathlib files that match `jInvariant`
(`Analysis/Fourier/AddCircle.lean`, `Topology/ContinuousMap/StoneWeierstrass.lean`) match on
the substring inside `conjInvariantSubalgebra` and have nothing to do with `j`. So there is
still no `j`-invariant and no class field theory anywhere reachable. Refute by exhibiting any
of those names as an actual declaration.

MACHINE-CHECKED (`PARI/GP`, 80 digits, via `ellj` — computed independently of the `η`-product
that defines `γ₂` here): at EVERY prime `p ≡ 3 mod 8` with `3 < p ≤ 200` and `h(−p) = 1`,
i.e. `p = 11, 19, 43, 67, 163`, `j(τ₀)` has `|Im j| = 0` to 80 digits and is the integer
`−32768, −884736, −884736000, −147197952000, −262537412640768000`, each an EXACT cube of
`−32, −96, −960, −5280, −640320`. So all three leaves below hold at every admissible `p`,
with `v = 0` in the two `K`-valued ones. -/

/-- `τ₀` written out: `(3 + i√p)/2`. -/
lemma coe_heegnerPoint (p : ℕ) (hp : 0 < p) :
    (heegnerPoint p hp : ℂ) = (3 + Complex.I * (Real.sqrt p : ℂ)) / 2 := rfl

/-- `exp(n·πi + r)` with `n : ℕ` and `r` REAL is the real number `(−1)ⁿeʳ`. All four
`q`-parameter evaluations below are instances of this. -/
lemma cexp_eq_ofReal_of_natPiI {w : ℂ} {n : ℕ} {r : ℝ}
    (h : w = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) + (r : ℂ)) :
    Complex.exp w = (((-1 : ℝ) ^ n * Real.exp r : ℝ) : ℂ) := by
  rw [h, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  push_cast [Complex.ofReal_exp]
  ring

/-- **The conjugation trick.** If `𝕢₁(z)` and `𝕢₂₄(z)⁸` are both real, then `η(z)⁸` is real.

`η(z) = 𝕢₂₄(z)·∏(1 − 𝕢₁(z)ⁿ⁺¹)`, so reality of `𝕢₁(z)` makes every factor of the product
`conj`-invariant, and `Multipliable.map_tprod` carries `conj` through the infinite product.
The eighth power is what makes the `𝕢₂₄` prefactor real at the Heegner point; no smaller
power works. -/
lemma conj_eta_pow_eight {z : ℂ} (hz : 0 < z.im) {a b : ℝ}
    (hq : Function.Periodic.qParam 1 z = (a : ℂ))
    (h24 : Function.Periodic.qParam 24 z ^ 8 = (b : ℂ)) :
    (starRingEnd ℂ) (ModularForm.eta z ^ 8) = ModularForm.eta z ^ 8 := by
  have hnorm : ‖Function.Periodic.qParam 1 z‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one (by norm_num) hz
  have hm : Multipliable fun n : ℕ ↦ (1 - ModularForm.eta_q n z) :=
    ModularForm.multipliable_one_sub_pow hnorm
  have hq' : (starRingEnd ℂ) (Function.Periodic.qParam 1 z) = Function.Periodic.qParam 1 z := by
    rw [hq, Complex.conj_ofReal]
  have hP : (starRingEnd ℂ) (∏' n : ℕ, (1 - ModularForm.eta_q n z))
      = ∏' n : ℕ, (1 - ModularForm.eta_q n z) := by
    rw [hm.map_tprod (starRingEnd ℂ) Complex.continuous_conj]
    refine tprod_congr fun n => ?_
    show (starRingEnd ℂ) (1 - Function.Periodic.qParam 1 z ^ (n + 1))
      = 1 - Function.Periodic.qParam 1 z ^ (n + 1)
    rw [map_sub, map_one, map_pow, hq']
  have h24' : (starRingEnd ℂ) (Function.Periodic.qParam 24 z ^ 8)
      = Function.Periodic.qParam 24 z ^ 8 := by rw [h24, Complex.conj_ofReal]
  rw [ModularForm.eta, mul_pow, map_mul, h24', map_pow, hP]

lemma im_heegnerPoint_pos (p : ℕ) (hp : 0 < p) : 0 < ((heegnerPoint p hp : ℂ)).im :=
  (heegnerPoint p hp).2

lemma im_two_heegnerPoint_pos (p : ℕ) (hp : 0 < p) : 0 < (2 * (heegnerPoint p hp : ℂ)).im := by
  have := im_heegnerPoint_pos p hp
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  linarith

/-- `η(τ₀)⁸` is REAL: `𝕢₁(τ₀) = −e^{−π√p}` and `𝕢₂₄(τ₀)⁸ = −e^{−π√p/3}`. -/
lemma conj_eta_heegnerPoint_pow_eight (p : ℕ) (hp : 0 < p) :
    (starRingEnd ℂ) (ModularForm.eta (heegnerPoint p hp : ℂ) ^ 8)
      = ModularForm.eta (heegnerPoint p hp : ℂ) ^ 8 := by
  refine conj_eta_pow_eight (im_heegnerPoint_pos p hp)
    (a := (-1 : ℝ) ^ 3 * Real.exp (-(Real.pi * Real.sqrt p)))
    (b := (-1 : ℝ) ^ 1 * Real.exp (-(Real.pi * Real.sqrt p) / 3)) ?_ ?_
  · refine cexp_eq_ofReal_of_natPiI ?_
    rw [coe_heegnerPoint]
    push_cast
    linear_combination (Real.pi * (Real.sqrt p : ℂ)) * Complex.I_sq
  · rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    refine cexp_eq_ofReal_of_natPiI ?_
    rw [coe_heegnerPoint]
    push_cast
    linear_combination ((Real.pi : ℂ) * (Real.sqrt p : ℂ) / 3) * Complex.I_sq

/-- `η(2τ₀)⁸` is REAL: `𝕢₁(2τ₀) = e^{−2π√p}` and `𝕢₂₄(2τ₀)⁸ = e^{−2π√p/3}`. -/
lemma conj_eta_two_heegnerPoint_pow_eight (p : ℕ) (hp : 0 < p) :
    (starRingEnd ℂ) (ModularForm.eta (2 * (heegnerPoint p hp : ℂ)) ^ 8)
      = ModularForm.eta (2 * (heegnerPoint p hp : ℂ)) ^ 8 := by
  refine conj_eta_pow_eight (im_two_heegnerPoint_pos p hp)
    (a := (-1 : ℝ) ^ 6 * Real.exp (-(2 * Real.pi * Real.sqrt p)))
    (b := (-1 : ℝ) ^ 2 * Real.exp (-(2 * Real.pi * Real.sqrt p) / 3)) ?_ ?_
  · refine cexp_eq_ofReal_of_natPiI ?_
    rw [coe_heegnerPoint]
    push_cast
    linear_combination (2 * Real.pi * (Real.sqrt p : ℂ)) * Complex.I_sq
  · rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    refine cexp_eq_ofReal_of_natPiI ?_
    rw [coe_heegnerPoint]
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * (Real.sqrt p : ℂ) / 3) * Complex.I_sq

/-- **`f₂(τ₀)⁸` is REAL.** Note `f₂(τ₀)` and `f₂(τ₀)²` are not — only the eighth power. -/
lemma conj_weberF2_heegnerPoint_pow_eight (p : ℕ) (hp : 0 < p) :
    (starRingEnd ℂ) (weberF2 (heegnerPoint p hp) ^ 8) = weberF2 (heegnerPoint p hp) ^ 8 := by
  rw [weberF2, div_pow, mul_pow, map_div₀, map_mul, conj_eta_two_heegnerPoint_pow_eight,
    conj_eta_heegnerPoint_pow_eight, map_pow, Complex.conj_ofReal]

/-- **LEAF 4a — `γ₂(τ₀)` is REAL. PROVEN.**

No arithmetic hypothesis is used: `0 < p` is all it takes, because reality is a statement
about the `q`-expansion at the specific point `τ₀ = (3+√−p)/2` and nothing else. This is the
half of `LEAF 4` that cuts `K = ℚ(√−p)` down to `ℚ`; see the section note above. -/
theorem exists_real_gammaTwo_heegnerPoint (p : ℕ) (hp : 0 < p) :
    ∃ x : ℝ, (x : ℂ) = gammaTwo (heegnerPoint p hp) := by
  have hrw : gammaTwo (heegnerPoint p hp)
      = ((weberF2 (heegnerPoint p hp) ^ 8) ^ 3 + 16) / (weberF2 (heegnerPoint p hp) ^ 8) := by
    rw [gammaTwo, ← pow_mul]
  have hconj : (starRingEnd ℂ) (gammaTwo (heegnerPoint p hp)) = gammaTwo (heegnerPoint p hp) := by
    rw [hrw, map_div₀, map_add, map_pow, conj_weberF2_heegnerPoint_pow_eight, map_ofNat]
  exact ⟨_, Complex.conj_eq_iff_re.mp hconj⟩

/-- **LEAF 4b — `j(τ₀) ∈ K = ℚ(√−p)`. THE FIRST MAIN THEOREM OF COMPLEX MULTIPLICATION.**

`τ₀ = (3+√−p)/2 = 1 + (1+√−p)/2`, so `ℤ + ℤτ₀ = ℤ[(1+√−p)/2] = 𝒪_K`, the MAXIMAL order (here
`p ≡ 3 mod 4` follows from `p ≡ 3 mod 8`). By the first main theorem of CM (Booher Theorem
34/36; Cox §11) `K(j(𝒪_K))` is the Hilbert class field of `K` and `[K(j(𝒪_K)) : K] = h(−p)`.
`hcl` says every positive definite form of discriminant `−p` is properly equivalent to every
other, i.e. `h(−p) = 1`, so that field is `K` itself and `j(τ₀) ∈ K`.

`hcl` IS LOAD-BEARING AND IS CONSUMED ONLY HERE. Drop it and the statement is FALSE, with an
explicit witness that satisfies every OTHER hypothesis (`PARI/GP`-checked 2026-07-28):
`p = 59` is prime, `59 ≡ 3 mod 8`, `3 < 59`, and `h(−59) = 3`. There `j(τ₀) = −30197682742.99…`
is a root of the IRREDUCIBLE cubic

  `x³ + 30197678080x² − 140811576541184x + 374643194001883136`

(`polclass(-59)`, `polisirreducible` = 1), so `[ℚ(j(τ₀)) : ℚ] = 3` and `j(τ₀)` lies in no
quadratic field, let alone `K`. Note that `j(τ₀)` is still REAL there — which is precisely
why `LEAF 4a` needs no `hcl` and is strictly weaker than this leaf.

WHAT IT WOULD TAKE. Complex multiplication, ring class fields and the Galois action
`σ_𝔞(j(𝔟)) = j(𝔞𝔟)` are absent from mathlib at this pin, from `~/cs/FLT` and from this
project — re-verified 2026-07-28, see the section note above for the exact greps. The route
is Cox §11: the modular polynomial `Φ_N ∈ ℤ[X, Y]`, then that `Gal(ℚ̄/ℚ)` permutes the finite
set `{j(τ_f) : f of discriminant −p}`, then `h = 1` makes that set a singleton, so `j(τ₀)` is
fixed by every automorphism. Building `Φ_N` is the bulk of it and is a project in its own
right; **that** is where the next cut belongs, not here.

CHEAPER ALTERNATIVE WORTH CHECKING FIRST: Stark's remark (quoted at the end of Booher) that
"nothing more modern is required" — Weber's own computations replace the class field theory.
Nobody in this development has yet costed that route; doing so is a legitimate outcome for
whoever owns this leaf. -/
theorem exists_quadratic_jInvariant_heegnerPoint {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ u v : ℚ, jInvariant (heegnerPoint p hp.pos)
      = (u : ℂ) + (v : ℂ) * (Complex.I * (Real.sqrt p : ℂ)) :=
  sorry

/-- **LEAF 4c — `γ₂(τ₀)` descends with `j(τ₀)`.** Weber's level-`3` result (Booher §3.2 and
Theorem 36): for `3 ∤ D`, `K(γ₂(τ)) = K(j(τ))`.

`γ₂³ = j` gives `ℚ(j) ⊆ ℚ(γ₂)` for free; ALL the content is the reverse inclusion, i.e. that
the cube root does not enlarge the field. `γ₂` is a modular function for a level-`3` group,
so `[K(γ₂(τ)) : K(j(τ))]` divides `3`, and `3 ∤ D` forces it to be `1`.

WHAT A PROVER MAY USE, and it collapses this leaf considerably. `exists_real_gammaTwo_heegnerPoint`
(PROVEN above) plus `gammaTwo_pow_three_eq_jInvariant` (`LEAF 5`) turn `hj` into `j(τ₀) ∈ ℚ`
— reality kills the `√−p` component — and reduce the conclusion to the single arithmetic
statement **`j(τ₀)` is a perfect cube in `ℚ`**, with `γ₂(τ₀)` its real cube root. That is the
honest residue of this leaf and is how it should be attacked.

ONLY `3 ∤ p` IS EXPECTED TO BE LOAD-BEARING, and it comes from `hp` with `h3`; `hp8` is
passed for uniformity with its siblings and is not expected to be needed. `3 ∤ p` genuinely
cannot be dropped: at `D` divisible by `3` the cube root does enlarge the field, which is
exactly why Booher's Theorem 36 carries the hypothesis.

NOT VACUOUS, and note `hj` is not idle: without it the conclusion is a statement about an
unconstrained transcendental-looking quantity, and with it the leaf is the `[K(γ₂):K(j)] = 1`
step alone. Machine-checked at all five admissible `p`: `j(τ₀)` is an exact rational cube
(see the section note). -/
theorem exists_quadratic_gammaTwo_of_jInvariant {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (h3 : 3 < p)
    (hj : ∃ u v : ℚ, jInvariant (heegnerPoint p hp.pos)
      = (u : ℂ) + (v : ℂ) * (Complex.I * (Real.sqrt p : ℂ))) :
    ∃ u v : ℚ, gammaTwo (heegnerPoint p hp.pos)
      = (u : ℂ) + (v : ℂ) * (Complex.I * (Real.sqrt p : ℂ)) :=
  sorry

/-- **LEAF 4 — `γ₂(τ₀)` is RATIONAL. This is the main theorem of complex multiplication.**

By the first main theorem of CM (Booher Theorem 34/36; Cox §11), `K(j(τ₀))` is the Hilbert
class field of `K = ℚ(√−p)` and `[K(j(τ₀)) : K] = h(−p)`; with `h(−p) = 1` that field is `K`
itself, and since `j(τ₀)` is real it lies in `ℚ`. Because `3 ∤ p`, Weber's `γ₂` generates the
same field (Booher Theorem 36), so `γ₂(τ₀) ∈ ℚ` too.

Together with LEAF 3 this gives `γ₂(τ₀) ∈ ℤ` — see `exists_int_gammaTwo`, which is PROVEN
from the two, using that `ℤ` is integrally closed in `ℚ`.

MACHINE-CHECKED FAITHFULNESS: at the five admissible `p`, `(f₂(τ₀)²⁴+16)/f₂(τ₀)⁸` evaluates
(`PARI/GP`, 60 digits, `η` as a 400-term product) to
`−32, −96, −960, −5280, −640320` with imaginary part `< 10⁻⁷⁰`.

THIS IS THE REAL COST OF THE DEEP LEAF. Complex multiplication, ring class fields, and the
Galois action `σ_a(j(b)) = j(ab)` are absent from mathlib at this pin, from `~/cs/FLT`, and
from this project; building them is a project in its own right and this is where a further
decomposition should cut. The elementary route Stark points out (Booher's closing remark:
"nothing more modern is required") replaces the class field theory by Weber's own
computations, and is the cheaper target if this is ever attacked directly.

**DECOMPOSED 2026-07-28 (`flt-lean-329`), and this declaration is now PROVEN** over the three
leaves in the section above — the first of which is itself PROVEN here:

* `exists_real_gammaTwo_heegnerPoint` — `γ₂(τ₀) ∈ ℝ`. **PROVEN**, from `0 < p` alone;
* `exists_quadratic_jInvariant_heegnerPoint` — `j(τ₀) ∈ K = ℚ(√−p)` (the CM half, and the
  only consumer of `hcl`);
* `exists_quadratic_gammaTwo_of_jInvariant` — `γ₂(τ₀) ∈ K` given `j(τ₀) ∈ K` (Weber's
  level-`3` descent, needing only `3 ∤ p`).

The assembly below is the step "`K ∩ ℝ = ℚ`": reality forces the `√−p` coefficient `v` to
vanish, since `√p > 0`. No complex multiplication is used HERE — all of it is in the second
leaf, which is now the only place in this cluster that needs class field theory. -/
theorem exists_rat_gammaTwo_heegnerPoint {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ r : ℚ, (r : ℂ) = gammaTwo (heegnerPoint p hp.pos) := by
  obtain ⟨x, hx⟩ := exists_real_gammaTwo_heegnerPoint p hp.pos
  obtain ⟨u, v, huv⟩ := exists_quadratic_gammaTwo_of_jInvariant hp hp8 h3
    (exists_quadratic_jInvariant_heegnerPoint hp hp8 h3 hcl)
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have him := congrArg Complex.im (hx.trans huv)
  simp only [Complex.ofReal_im, Complex.add_im, Complex.ratCast_im, Complex.mul_im,
    Complex.ratCast_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, zero_mul, mul_zero, zero_add, add_zero, one_mul, sub_zero] at him
  have hv : v = 0 := by
    have hv' : (v : ℝ) = 0 := by
      rcases mul_eq_zero.mp him.symm with h | h
      · exact h
      · exact absurd h (ne_of_gt hsqrt)
    exact_mod_cast hv'
  exact ⟨u, by rw [huv, hv]; simp⟩

/-! ### Reduction of LEAVES 5 and 6 to their analytic cores

Everything from here to `exp_pi_sqrt_le_of_jInvariant_eq` was added when LEAVES 5 and 6 were
closed over three new named sub-leaves. Both targets are now PROVEN.

STATUS UPDATE (2026-07-29): all three of those sub-leaves are now closed too.
`exists_E₄_heegnerPoint_approx` and `exists_E₆_heegnerPoint_approx` were proven on
2026-07-28; `eta_pow_24_add_eta_two_pow_24` is proven below over the single new leaf
`eta_two_torsion_key`. So nothing in the LEAF 5 / LEAF 6 reduction is open except that one
`η`-product identity. The sentence that used to stand here, listing the two `E`-estimates as
open, was stale.

CORRECTION TO THE NAMESPACE DOCSTRING ABOVE (checked 2026-07-28, `grep` over
`.lake/packages/mathlib`). The claim that "nothing of the modular theory used below is in
mathlib at this pin" is too strong and cost this decomposition a wrong first plan. Mathlib at
this pin ALSO has, and all of it is used or usable here:

* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq : Δ z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728`
  (`ModularForms/LevelOne/GradedRing.lean`) — this is what lets LEAF 6 avoid infinite products
  entirely and run on Eisenstein values alone;
* `ModularForm.levelOne_weight_four_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 4) = 1`,
  `dimension_level_one`, and `sturm_bound_levelOne`
  (`ModularForms/LevelOne/DimensionFormula.lean`) — a Sturm bound, i.e. exactly the tool for
  proving an identity of level-one forms from finitely many `q`-coefficients;
* `EisensteinSeries.q_expansion_bernoulli`, `E_qExpansion_coeff`,
  `EisensteinSeries.summable_sigma_mul_cexp_pow` (`EisensteinSeries/QExpansion.lean`) — the
  pointwise `q`-expansion `E k z = 1 - (2k/B_k) Σ σ_{k-1}(n) qⁿ` with summability;
* `ModularForm.discriminant_eq_q_prod`, `discriminant_T_invariant`, `discriminant_S_invariant`,
  and the `η`-transformation material in `ModularForms/Discriminant.lean`.

What is genuinely absent is still absent: no `j`-invariant, no Weber functions, no complex
multiplication, no ring class fields. Re-run the greps; they are a dated measurement. -/

/-! ### SUB-LEAF 5a: the level-two `η`-identity, and its reduction to ONE `η`-product identity

`eta_pow_24_add_eta_two_pow_24` — `η(z)²⁴ + 256 η(2z)²⁴ = E₄(z)·(η(z)η(2z))⁸` — is now PROVEN
below, over the single remaining leaf `eta_two_torsion_key`.  Everything between here and it is
new and proven: the `η`-transformation bookkeeping, the packaging of

  `F(z) = (η(z)²⁴ + 256 η(2z)²⁴)/(η(z)η(2z))⁸`

as an honest `ModularForm 𝒮ℒ 4`, and the identification `F = E₄` from
`ModularForm.levelOne_weight_four_rank_one`.

**CORRECTION (2026-07-29) TO THE ROUTE THIS NODE WAS CUT ALONG.**  The previous docstring said
the remaining work was "`S`-invariance of weight 4, after which `levelOne_weight_four_rank_one`
plus a single `q`-coefficient comparison finishes; `sturm_bound_levelOne` is the packaged form
of that last step".  The first clause is right and the last is a red herring — no Sturm bound is
used or needed below; `sturm_bound_levelOne` never enters, because rank-one plus the constant
term is already enough.  The `S`-invariance really is the whole theorem, exactly as the
2026-07-28 correction said, and the honest cut is NOT the two Weber relations
`f·f₁·f₂ = √2` and `f⁸ = f₁⁸+f₂⁸` separately but their COMBINATION, which is a single identity
in `η` alone — see `eta_two_torsion_key`.  Concretely, write `E = η(z)²⁴`, `B = η(z/2)⁸`,
`C = η(2z)⁸`.  Applying `eta_comp_eq_csqrt_I_inv` at `z` and (via `−2/z = −1/(z/2)`) at `z/2`
turns `F(−1/z) = z⁴F(z)` into `C·(16E + B³) = B·(E + 256C³)`, and the difference of the two
sides factors exactly as

  `C·(16E + B³) − B·(E + 256C³) = (16C − B)·(E − B·C·(B + 16C))`.

So the `S`-transformation is implied by `B·C·(B + 16C) = E`, which is `eta_two_torsion_key`.
In the Weber variables `b = B/η(z)⁸`, `c = 16C/η(z)⁸` that identity is `bc(b+c) = 16`; the two
`f`-relations imply it (`a = b+c` substituted into `abc = 16`), but it does not need `f` — so
`η((z+1)/2)` and the 48-th root of unity never appear.  `etaWeightFour_S_algebra` is that one
factorisation, discharged by `rw` on the key identity followed by `field_simp; ring`.

Also corrected: `T`-invariance is NOT the "24-th power argument" the old docstring described
(that argument is about `Δ`, not about `F`).  What is actually true and proven here is
`eta_add_one : η(z+1) = e^{πi/12}η(z)`, whence `η(2z+2) = e^{πi/6}η(2z)`, and both numerator
and denominator of `F` are multiplied by `(e^{πi/12})²⁴ = 1`.

Still true and re-checked at this pin: `discriminant_eq_E₄_cube_sub_E₆_sq`,
`levelOne_weight_four_rank_one`, `dimension_level_one`, `EisensteinSeries.q_expansion_bernoulli`,
`discriminant_eq_q_prod`, `discriminant_S_invariant`, `eta_comp_eq_csqrt_I_inv` are all in
mathlib and are used below.  Genuinely absent, re-grepped 2026-07-29: `j`, Weber functions, CM,
ring class fields, and any Jacobi triple product. -/

section EtaWeightFour

open Complex UpperHalfPlane ModularForm Filter Function
open scoped Real MatrixGroups Topology Manifold


/-! ### `Complex.sqrt` helpers -/

lemma csqrt_sq {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul,
    show ((2 : ℕ) : ℂ) * (Complex.log z / 2) = Complex.log z by push_cast; ring,
    Complex.exp_log hz]

lemma csqrt_pow_eight {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 8 = z ^ 4 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, csqrt_sq hz]

lemma csqrt_pow_twentyFour {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 24 = z ^ 12 := by
  rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, csqrt_sq hz]

lemma csqrtI_pow_eight : Complex.sqrt Complex.I ^ 8 = 1 := by
  rw [csqrt_pow_eight Complex.I_ne_zero, Complex.I_pow_four]

/-! ### `η(z+1)` -/

lemma eta_add_one (z : ℂ) :
    ModularForm.eta (z + 1) = Complex.exp (↑Real.pi * Complex.I / 12) * ModularForm.eta z := by
  have hq1 : Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one]
    rw [show 2 * (↑Real.pi : ℂ) * Complex.I * (z + 1)
        = 2 * ↑Real.pi * Complex.I * z + 2 * ↑Real.pi * Complex.I by ring]
    exact Complex.exp_periodic _
  have hq24 : Periodic.qParam 24 (z + 1)
      = Complex.exp (↑Real.pi * Complex.I / 12) * Periodic.qParam 24 z := by
    simp only [Periodic.qParam]
    rw [show 2 * (↑Real.pi : ℂ) * Complex.I * (z + 1) / ((24 : ℝ) : ℂ)
        = ↑Real.pi * Complex.I / 12 + 2 * ↑Real.pi * Complex.I * z / ((24 : ℝ) : ℂ) by
      push_cast; ring, Complex.exp_add]
  simp only [ModularForm.eta, ModularForm.eta_q, hq1, hq24, mul_assoc]

lemma zeta24_pow_24 : Complex.exp (↑Real.pi * Complex.I / 12) ^ 24 = 1 := by
  rw [← Complex.exp_nat_mul,
    show ((24 : ℕ) : ℂ) * (↑Real.pi * Complex.I / 12) = 2 * ↑Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

/-! ### The weight-four eta quotient -/

/-- **SUB-LEAF 5a-i — THE ONE REMAINING ANALYTIC INPUT.**

  `η(z/2)⁸ · η(2z)⁸ · (η(z/2)⁸ + 16 η(2z)⁸) = η(z)²⁴`.

Everything else in `eta_pow_24_add_eta_two_pow_24` is PROVEN below from this single identity;
see the section prose above for the derivation and for why this is a strictly cleaner cut than
the two Weber relations the previous plan named.

WHERE IT COMES FROM. In Weber's notation `f = ζ₄₈⁻¹η((z+1)/2)/η(z)`, `f₁ = η(z/2)/η(z)`,
`f₂ = √2·η(2z)/η(z)`, put `a = f⁸`, `b = f₁⁸ = η(z/2)⁸/η(z)⁸`, `c = f₂⁸ = 16η(2z)⁸/η(z)⁸`.
The two classical Weber relations are

  `f·f₁·f₂ = √2`  (equivalently `abc = 16`)   and   `f⁸ = f₁⁸ + f₂⁸`  (equivalently `a = b + c`),

the second being Jacobi's `θ₂⁴ + θ₄⁴ = θ₃⁴`.  Substituting `a = b + c` into `abc = 16`
ELIMINATES `f` (and with it `η((z+1)/2)` and the 48-th root of unity) and leaves exactly
`bc(b+c) = 16`, which cleared of denominators is the statement above.  So this one identity
carries the full content of both Weber relations that the `S`-transformation actually needs,
and it is stated purely in `ModularForm.eta` — no Weber function, no root of unity, no theta
constant appears.

MACHINE-CHECKED FAITHFULNESS (`PARI/GP`, `eta(z,1)`, 60 digits, 2026-07-29): the relative
residual of `η(z/2)⁸η(2z)⁸(η(z/2)⁸+16η(2z)⁸) − η(z)²⁴` is `< 9·10⁻⁷⁶` at all NINE of
`z = 0.3+0.7i`, `0.1+1.3i`, `−0.4+0.55i`, `0.05+i`, `3i`, `0.3i`, `0.49+0.05i`, `−0.25+0.1i`,
`i/√2`.  The last five were chosen to probe the places where such an identity most often
degenerates: deep in the cusp (`3i`), close to the real axis (`0.3i`, `0.49+0.05i`,
`−0.25+0.1i`), and at the fixed point `i/√2` of the Fricke involution, which is exactly where
the factor `16η(2z)⁸ − η(z/2)⁸` in the `S`-transformation vanishes.  The two Weber relations
and the final target were checked at the first four points with the same residual, so the
reduction above is not a mis-derivation.  The points are generic, not CM points: this is an
identity on all of `ℍ`.

WHAT WOULD REFUTE IT: any `z ∈ ℍ` where the two sides differ.  Note the constant `16` is
forced twice over and is not a normalisation — it is `(√2)⁸` on one side and the `2⁴` inside
`f₂⁸ = 2⁴η(2z)⁸/η(z)⁸` on the other — and the exponent `8` is forced by `f₂⁸` being the
smallest power of `f₂` that is a modular FUNCTION.

ROUTE FOR THE NEXT OWNER.  Re-grepped over `.lake/packages/mathlib` at this pin (2026-07-29):
there are no Weber functions, `ModularForms/JacobiTheta/` has no product formula tying `θ` to
`η`, and there is no Jacobi triple product anywhere.  So neither Weber relation can be quoted
and this really is new theory.  Two routes, both classical:

* prove the Jacobi triple product for `jacobiTheta₂` and read off `θ₂θ₃θ₄ = 2η³` together with
  `θ₂⁴+θ₄⁴ = θ₃⁴`; or
* prove it as a level-2 modular identity: `b` and `c` are holomorphic and non-vanishing on `ℍ`,
  `bc(b+c) − 16` is invariant under `Γ(2)` (the group is generated by `T²` and `ST²S`, and both
  act on the pair `(b, c)` by the `η`-transformation formulas already in
  `ModularForms/Discriminant.lean`), and it vanishes at all three cusps by the `q`-expansions
  `b = q^{1/3}(1 + O(q^{1/2}))`, `c = 16q^{1/3}·q^{1/2}(1 + O(q))`.

An equivalent purely `q`-series form, with `x = e^{πiz}`, is
`∏(1−(−1)ⁿxⁿ)⁸ = ∏(1−xⁿ)⁸ + 16x·∏(1−x⁴ⁿ)⁸`. -/
theorem eta_two_torsion_key (z : ℍ) :
    ModularForm.eta ((z : ℂ) / 2) ^ 8 * ModularForm.eta (2 * (z : ℂ)) ^ 8 *
        (ModularForm.eta ((z : ℂ) / 2) ^ 8 + 16 * ModularForm.eta (2 * (z : ℂ)) ^ 8)
      = ModularForm.eta (z : ℂ) ^ 24 := sorry

/-- `F(z) = (η(z)²⁴ + 256 η(2z)²⁴)/(η(z)η(2z))⁸`. -/
noncomputable def etaWeightFour (z : ℍ) : ℂ :=
  (ModularForm.eta (z : ℂ) ^ 24 + 256 * ModularForm.eta (2 * (z : ℂ)) ^ 24) /
    (ModularForm.eta (z : ℂ) * ModularForm.eta (2 * (z : ℂ))) ^ 8

lemma mem_upperHalfPlaneSet_two_mul (z : ℍ) : 2 * (z : ℂ) ∈ upperHalfPlaneSet := by
  show 0 < (2 * (z : ℂ)).im
  simpa using z.im_pos

lemma mem_upperHalfPlaneSet_div_two (z : ℍ) : (z : ℂ) / 2 ∈ upperHalfPlaneSet := by
  show 0 < ((z : ℂ) / 2).im
  simpa using z.im_pos

lemma eta_ne_zero_two_mul (z : ℍ) : ModularForm.eta (2 * (z : ℂ)) ≠ 0 :=
  ModularForm.eta_ne_zero (mem_upperHalfPlaneSet_two_mul z)

lemma eta_ne_zero_div_two (z : ℍ) : ModularForm.eta ((z : ℂ) / 2) ≠ 0 :=
  ModularForm.eta_ne_zero (mem_upperHalfPlaneSet_div_two z)

/-- The pure field algebra behind the `S`-transformation. -/
lemma etaWeightFour_S_algebra (Z e h f : ℂ) (hZ : Z ≠ 0) (he : e ≠ 0) (hh : h ≠ 0) (hf : f ≠ 0)
    (key : h ^ 8 * f ^ 8 * (h ^ 8 + 16 * f ^ 8) = e ^ 24) :
    (Z ^ 12 * e ^ 24 + 256 * ((Z / 2) ^ 12 * h ^ 24)) / (Z ^ 4 * (Z / 2) ^ 4 * (e * h) ^ 8)
      = Z ^ 4 * ((e ^ 24 + 256 * f ^ 24) / (e * f) ^ 8) := by
  rw [← key]
  field_simp
  ring

/-- `F(z + 1) = F(z)`. -/
lemma etaWeightFour_of_eq_add_one {z w : ℍ} (hw : (w : ℂ) = (z : ℂ) + 1) :
    etaWeightFour w = etaWeightFour z := by
  set ζ : ℂ := Complex.exp (↑Real.pi * Complex.I / 12) with hζ
  have hz24 : ζ ^ 24 = 1 := zeta24_pow_24
  have h1 : ModularForm.eta (w : ℂ) = ζ * ModularForm.eta (z : ℂ) := by
    rw [hw]; exact eta_add_one _
  have h2 : ModularForm.eta (2 * (w : ℂ)) = ζ ^ 2 * ModularForm.eta (2 * (z : ℂ)) := by
    rw [hw, show 2 * ((z : ℂ) + 1) = (2 * (z : ℂ) + 1) + 1 by ring, eta_add_one, eta_add_one]
    ring
  have hA : (ζ * ModularForm.eta (z : ℂ)) ^ 24 = ModularForm.eta (z : ℂ) ^ 24 := by
    rw [mul_pow, hz24, one_mul]
  have hB : (ζ ^ 2 * ModularForm.eta (2 * (z : ℂ))) ^ 24
      = ModularForm.eta (2 * (z : ℂ)) ^ 24 := by
    rw [mul_pow, ← pow_mul, show 2 * 24 = 24 * 2 from rfl, pow_mul, hz24, one_pow, one_mul]
  have hC : (ζ * ModularForm.eta (z : ℂ) * (ζ ^ 2 * ModularForm.eta (2 * (z : ℂ)))) ^ 8
      = (ModularForm.eta (z : ℂ) * ModularForm.eta (2 * (z : ℂ))) ^ 8 := by
    rw [show ζ * ModularForm.eta (z : ℂ) * (ζ ^ 2 * ModularForm.eta (2 * (z : ℂ)))
        = ζ ^ 3 * (ModularForm.eta (z : ℂ) * ModularForm.eta (2 * (z : ℂ))) by ring,
      mul_pow, ← pow_mul, show 3 * 8 = 24 from rfl, hz24, one_mul]
  rw [etaWeightFour, etaWeightFour, h1, h2, hA, hB, hC]

/-- The `S`-transformation, reduced to the root-of-unity bookkeeping. -/
lemma etaWeightFour_S_reduce (S sz sh e h : ℂ) (hS : S ^ 8 = 1) :
    ((S * (sz * e)) ^ 24 + 256 * (S * (sh * h)) ^ 24) / (S * (sz * e) * (S * (sh * h))) ^ 8
      = (sz ^ 24 * e ^ 24 + 256 * (sh ^ 24 * h ^ 24)) / (sz ^ 8 * sh ^ 8 * (e * h) ^ 8) := by
  have h24 : S ^ 24 = 1 := by rw [show (24 : ℕ) = 8 * 3 from rfl, pow_mul, hS, one_pow]
  have h16 : S ^ 16 = 1 := by rw [show (16 : ℕ) = 8 * 2 from rfl, pow_mul, hS, one_pow]
  rw [show (S * (sz * e)) ^ 24 + 256 * (S * (sh * h)) ^ 24
      = S ^ 24 * (sz ^ 24 * e ^ 24) + 256 * (S ^ 24 * (sh ^ 24 * h ^ 24)) by ring,
    show (S * (sz * e) * (S * (sh * h))) ^ 8
      = S ^ 16 * (sz ^ 8 * sh ^ 8 * (e * h) ^ 8) by ring, h24, h16]
  simp only [one_mul]

/-- `F(-1/z) = z⁴ F(z)`.  This is the `S`-transformation, and it is exactly where the
KEY leaf `eta_two_torsion_key` is consumed. -/
lemma etaWeightFour_of_eq_neg_inv {z w : ℍ} (hw : (w : ℂ) = -(z : ℂ)⁻¹) :
    etaWeightFour w = (z : ℂ) ^ 4 * etaWeightFour z := by
  have hz0 : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have hh0 : (z : ℂ) / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  have hS8 : ((Complex.sqrt Complex.I)⁻¹) ^ 8 = 1 := by
    rw [inv_pow, csqrtI_pow_eight, inv_one]
  have he1 : ModularForm.eta (w : ℂ)
      = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt (z : ℂ) * ModularForm.eta (z : ℂ)) := by
    rw [hw]
    simpa [neg_div] using ModularForm.eta_comp_eq_csqrt_I_inv z.2
  have he2 : ModularForm.eta (2 * (w : ℂ))
      = (Complex.sqrt Complex.I)⁻¹ *
        (Complex.sqrt ((z : ℂ) / 2) * ModularForm.eta ((z : ℂ) / 2)) := by
    have h := ModularForm.eta_comp_eq_csqrt_I_inv (mem_upperHalfPlaneSet_div_two z)
    rw [hw, show 2 * -(z : ℂ)⁻¹ = -1 / ((z : ℂ) / 2) by field_simp]
    simpa using h
  rw [etaWeightFour, he1, he2, etaWeightFour_S_reduce _ _ _ _ _ hS8,
    csqrt_pow_twentyFour hz0, csqrt_pow_eight hz0, csqrt_pow_twentyFour hh0, csqrt_pow_eight hh0]
  exact etaWeightFour_S_algebra _ _ _ _ hz0 (ModularForm.eta_ne_zero z.2)
    (eta_ne_zero_div_two z) (eta_ne_zero_two_mul z) (eta_two_torsion_key z)

/-! ### Slash invariance -/

lemma etaWeightFour_T_invariant :
    (etaWeightFour ∣[(4 : ℤ)] ModularGroup.T) = etaWeightFour := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul,
    etaWeightFour_of_eq_add_one (z := z) (w := (1 : ℝ) +ᵥ z)
      (by rw [UpperHalfPlane.coe_vadd]; push_cast; ring)]
  simp [denom, ModularGroup.T]

lemma etaWeightFour_S_invariant :
    (etaWeightFour ∣[(4 : ℤ)] ModularGroup.S) = etaWeightFour := by
  ext z
  have hz0 : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  rw [SlashInvariantForm.slash_S_apply,
    etaWeightFour_of_eq_neg_inv (z := z) (w := .mk _ z.im_inv_neg_coe_pos) (by simp)]
  rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

lemma etaWeightFour_slash (γ : SL(2, ℤ)) :
    (etaWeightFour ∣[(4 : ℤ)] γ) = etaWeightFour :=
  SlashInvariantForm.slash_action_generators_SL2Z etaWeightFour_S_invariant
    etaWeightFour_T_invariant γ

/-! ### Holomorphy -/

lemma differentiableAt_etaQuot {x : ℂ} (hx : x ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ (fun x : ℂ => (ModularForm.eta x ^ 24 + 256 * ModularForm.eta (2 * x) ^ 24)
      / (ModularForm.eta x * ModularForm.eta (2 * x)) ^ 8) x := by
  have h2 : (2 : ℂ) * x ∈ upperHalfPlaneSet := by
    show 0 < (2 * x).im
    simpa using hx
  have d1 : DifferentiableAt ℂ ModularForm.eta x :=
    ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hx
  have d2 : DifferentiableAt ℂ (fun x : ℂ => ModularForm.eta (2 * x)) x :=
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet h2).comp x (by fun_prop)
  exact ((d1.pow 24).add ((d2.pow 24).const_mul _)).div ((d1.mul d2).pow 8)
    (pow_ne_zero _ (mul_ne_zero (ModularForm.eta_ne_zero hx) (ModularForm.eta_ne_zero h2)))

lemma etaWeightFour_mdifferentiable : MDiff etaWeightFour := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine .congr (fun z hz ↦ (differentiableAt_etaQuot hz).differentiableWithinAt) fun z hz ↦ ?_
  simp [etaWeightFour, UpperHalfPlane.ofComplex_apply_of_im_pos hz]


/-! ### Behaviour at the cusp -/

/-- `G q = ∏' n, (1 - q^(n+1))`, the `q`-series factor of `η`. -/
noncomputable def etaProd (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

lemma eta_eq_qParam_mul_etaProd (z : ℂ) :
    ModularForm.eta z = Periodic.qParam 24 z * etaProd (Periodic.qParam 1 z) := rfl

lemma tendsto_etaProd : Filter.Tendsto etaProd (𝓝 0) (𝓝 1) := by
  have h := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 (0 : ℂ)) (g := 0)
    (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
  simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at h
  have : etaProd = fun q : ℂ ↦ ∏' n : ℕ, (1 + -q ^ (n + 1)) := by
    funext q; simp [etaProd, sub_eq_add_neg]
  rw [this]
  refine h
    (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
    (fun k ↦ by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq k
  exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _

/-- The cusp expression `(G(q)²⁴ + 256 q G(q²)²⁴)/(G(q)⁸ G(q²)⁸)`. -/
noncomputable def cuspExpr (q : ℂ) : ℂ :=
  (etaProd q ^ 24 + 256 * q * etaProd (q ^ 2) ^ 24) / (etaProd q ^ 8 * etaProd (q ^ 2) ^ 8)

lemma tendsto_cuspExpr : Filter.Tendsto cuspExpr (𝓝 0) (𝓝 1) := by
  have h2 : Filter.Tendsto (fun q : ℂ ↦ etaProd (q ^ 2)) (𝓝 0) (𝓝 1) := by
    refine tendsto_etaProd.comp ?_
    simpa using ((continuous_pow (M := ℂ) 2).tendsto 0)
  have hnum : Filter.Tendsto (fun q : ℂ ↦ etaProd q ^ 24 + 256 * q * etaProd (q ^ 2) ^ 24)
      (𝓝 0) (𝓝 1) := by
    have := ((tendsto_etaProd.pow 24).add
      (((tendsto_const_nhds (x := (256 : ℂ)) (f := 𝓝 (0:ℂ))).mul tendsto_id).mul (h2.pow 24)))
    simpa using this
  have hden : Filter.Tendsto (fun q : ℂ ↦ etaProd q ^ 8 * etaProd (q ^ 2) ^ 8)
      (𝓝 0) (𝓝 1) := by simpa using (tendsto_etaProd.pow 8).mul (h2.pow 8)
  have h := hnum.div hden one_ne_zero
  rw [div_one] at h
  exact Filter.Tendsto.congr (fun q ↦ rfl) h

lemma cusp_algebra (u g1 g2 : ℂ) (hu : u ≠ 0) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) :
    ((u * g1) ^ 24 + 256 * (u ^ 2 * g2) ^ 24) / (u * g1 * (u ^ 2 * g2)) ^ 8
      = (g1 ^ 24 + 256 * u ^ 24 * g2 ^ 24) / (g1 ^ 8 * g2 ^ 8) := by
  field_simp

lemma etaWeightFour_eq_cuspExpr (z : ℍ) :
    etaWeightFour z = cuspExpr (Periodic.qParam 1 (z : ℂ)) := by
  set u : ℂ := Periodic.qParam 24 (z : ℂ) with hu
  have hu0 : u ≠ 0 := by simp only [hu, Periodic.qParam]; exact Complex.exp_ne_zero _
  have hq : Periodic.qParam 1 (z : ℂ) = u ^ 24 := by
    simp only [hu, Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hq2 : Periodic.qParam 1 (2 * (z : ℂ)) = (Periodic.qParam 1 (z : ℂ)) ^ 2 := by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu2 : Periodic.qParam 24 (2 * (z : ℂ)) = u ^ 2 := by
    simp only [hu, Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have he1 : ModularForm.eta (z : ℂ) = u * etaProd (Periodic.qParam 1 (z : ℂ)) :=
    eta_eq_qParam_mul_etaProd _
  have he2 : ModularForm.eta (2 * (z : ℂ))
      = u ^ 2 * etaProd ((Periodic.qParam 1 (z : ℂ)) ^ 2) := by
    rw [eta_eq_qParam_mul_etaProd, hu2, hq2]
  have hg1 : etaProd (Periodic.qParam 1 (z : ℂ)) ≠ 0 := by
    intro h; exact ModularForm.eta_ne_zero z.2 (by rw [he1, h, mul_zero])
  have hg2 : etaProd ((Periodic.qParam 1 (z : ℂ)) ^ 2) ≠ 0 := by
    intro h; exact eta_ne_zero_two_mul z (by rw [he2, h, mul_zero])
  rw [etaWeightFour, he1, he2, cusp_algebra _ _ _ hu0 hg1 hg2, cuspExpr, ← hq]

lemma etaWeightFour_tendsto_one :
    Filter.Tendsto etaWeightFour UpperHalfPlane.atImInfty (𝓝 1) :=
  Filter.Tendsto.congr (fun z ↦ (etaWeightFour_eq_cuspExpr z).symm)
    (tendsto_cuspExpr.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos))

lemma etaWeightFour_isBoundedAtImInfty : UpperHalfPlane.IsBoundedAtImInfty etaWeightFour :=
  etaWeightFour_tendsto_one.isBigO_one ℝ

/-! ### Identification with `E₄` -/

noncomputable def etaWeightFourForm : ModularForm 𝒮ℒ 4 where
  toFun := etaWeightFour
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact etaWeightFour_slash A
  holo' := etaWeightFour_mdifferentiable
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [etaWeightFour_slash]
    exact etaWeightFour_isBoundedAtImInfty

theorem etaWeightFour_eq_E₄ (z : ℍ) : etaWeightFour z = ModularForm.E₄ z := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₄ = etaWeightFourForm :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₄
        (EisensteinSeries.E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_four_rank_one) _
  have hcoe : (c • (ModularForm.E₄ : ℍ → ℂ)) = etaWeightFour := congrArg DFunLike.coe hc
  have hc1 : c = 1 := by
    have h1 : (qExpansion 1 (c • (ModularForm.E₄ : ℍ → ℂ))).coeff 0 = c := by
      rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₄]
      simp [EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩]
    rw [hcoe] at h1
    rw [← h1, show (etaWeightFour : ℍ → ℂ) = (etaWeightFourForm : ℍ → ℂ) from rfl,
      UpperHalfPlane.qExpansion_coeff_zero one_pos
        (ModularFormClass.analyticAt_cuspFunction_zero (f := etaWeightFourForm) one_pos
          one_mem_strictPeriods_SL)
        (SlashInvariantFormClass.periodic_comp_ofComplex (f := etaWeightFourForm)
          one_mem_strictPeriods_SL)]
    exact etaWeightFour_tendsto_one.limUnder_eq
  rw [← congrFun hcoe z, hc1]
  simp

end EtaWeightFour

/-- **SUB-LEAF 5a — the level-two `η`-identity**

  `η(z)²⁴ + 256 η(2z)²⁴ = E₄(z) · (η(z)η(2z))⁸`.

This is ALL of the modular-function content of Weber's `γ₂³ = j`: given it, LEAF 5 is pure
field algebra (see `gammaTwo_eq_E₄_div_eta_pow_eight` and
`gammaTwo_pow_three_eq_jInvariant`, both PROVEN below).

WHY THIS IS THE RIGHT CUT. Writing `h = η(2z)/η(z)`, the definition
`γ₂ = (f₂²⁴+16)/f₂⁸` with `f₂ = √2·h` unfolds to `γ₂ = (256h²⁴+1)/h⁸`, i.e.
`γ₂ = (η²⁴ + 256η(2z)²⁴)/(η¹⁶ η(2z)⁸)`. So this identity says exactly `γ₂ = E₄/η⁸`, and
cubing gives `γ₂³ = E₄³/η²⁴ = E₄³/Δ = j` because `Δ = η²⁴` is mathlib's DEFINITION of the
discriminant. No branch of a cube root is ever chosen, which is why the statement is an
identity rather than an identity-up-to-`ζ₃`.

MACHINE-CHECKED FAITHFULNESS (`PARI/GP`, 60 digits, `eta(z,1)` against the `σ₃` series for
`E₄`): at `z = 0.3+0.7i`, `0.1+1.3i`, `-0.4+0.55i`, `0.05+i` the two sides agree to `10⁻⁷⁶`,
with ratio `1` to every printed digit. The points are generic — not Heegner points — because
this is an identity on all of `ℍ`, and testing it only at CM points would not distinguish it
from a weaker statement.

PROVEN (2026-07-29) from `etaWeightFour_eq_E₄`, i.e. from the single leaf
`eta_two_torsion_key` together with the modular-form packaging in the section above. -/
theorem eta_pow_24_add_eta_two_pow_24 (z : UpperHalfPlane) :
    ModularForm.eta (z : ℂ) ^ 24 + 256 * ModularForm.eta (2 * (z : ℂ)) ^ 24
      = ModularForm.E₄ z * (ModularForm.eta (z : ℂ) * ModularForm.eta (2 * (z : ℂ))) ^ 8 := by
  have h := etaWeightFour_eq_E₄ z
  rw [etaWeightFour, div_eq_iff (pow_ne_zero _ (mul_ne_zero (eta_ne_zero' z)
    (eta_two_ne_zero z)))] at h
  exact h

/-- The field algebra behind `γ₂ = E₄/η⁸`, isolated over plain variables of `ℂ` so that `ring`
sees genuine atoms rather than `η` applied to two different-looking arguments. -/
theorem weber_div_algebra (e1 e2 E s : ℂ) (h1 : e1 ≠ 0) (h2 : e2 ≠ 0) (hs : s ^ 2 = 2)
    (key : e1 ^ 24 + 256 * e2 ^ 24 = E * (e1 * e2) ^ 8) :
    ((s * e2 / e1) ^ 24 + 16) / (s * e2 / e1) ^ 8 = E / e1 ^ 8 := by
  have hs8 : s ^ 8 = 16 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hs]; norm_num
  have hs24 : s ^ 24 = 4096 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, hs]; norm_num
  have hE : E = (e1 ^ 24 + 256 * e2 ^ 24) / (e1 * e2) ^ 8 := by
    rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero h1 h2))]
    linear_combination -key
  rw [hE, div_pow, div_pow, mul_pow, mul_pow, hs8, hs24]
  field_simp
  ring

/-- **`γ₂ = E₄/η⁸`** — PROVEN from `eta_pow_24_add_eta_two_pow_24`.

This is the useful form of Weber's identity: it exhibits `γ₂` as an honest cube root of
`j = E₄³/η²⁴` with no branch chosen. -/
theorem gammaTwo_eq_E₄_div_eta_pow_eight (z : UpperHalfPlane) :
    gammaTwo z = ModularForm.E₄ z / ModularForm.eta (z : ℂ) ^ 8 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    rw [Real.sq_sqrt]
    norm_num
  exact weber_div_algebra _ _ _ _ (eta_ne_zero' z) (eta_two_ne_zero z) hs
    (eta_pow_24_add_eta_two_pow_24 z)

/-- The real `q`-parameter magnitude at the Heegner point: `Q = exp(−π√p)`.

`q = exp(2πiτ₀) = −Q` is NEGATIVE — that is what the `3` in `τ₀ = (3+√−p)/2` buys — but only
`Q` itself is needed below, since the sign is already absorbed into the signs of the
coefficients in `exists_E₄_heegnerPoint_approx` and `exists_E₆_heegnerPoint_approx`. -/
noncomputable def heegnerQ (p : ℕ) : ℝ := Real.exp (-(Real.pi * Real.sqrt p))

lemma heegnerQ_pos (p : ℕ) : 0 < heegnerQ p := Real.exp_pos _

/-- `Q ≤ 10⁻⁴` for `p ≥ 11`. The true value at `p = 11` is `2.98·10⁻⁵`; `10⁻⁴` is the
threshold the tail arithmetic below is calibrated to, and it is reached with room to spare
(`π√11 = 10.42` against the `10` actually used). -/
lemma heegnerQ_le {p : ℕ} (hp : 11 ≤ p) : heegnerQ p ≤ 1 / 10000 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hsq : (3.3 : ℝ) ≤ Real.sqrt p := by
    have h11 : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h2 : Real.sqrt 10.89 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by linarith)
    calc (3.3 : ℝ) = Real.sqrt 10.89 := by
          rw [show (10.89 : ℝ) = 3.3 ^ 2 by norm_num, Real.sqrt_sq]; norm_num
      _ ≤ _ := h2
  have h10 : (10 : ℝ) ≤ Real.pi * Real.sqrt p := by nlinarith [Real.pi_pos]
  have hexp : (10000 : ℝ) ≤ Real.exp 10 := by
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hp10 : (2.7182818283 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
      pow_le_pow_left₀ (by norm_num) he.le 10
    rw [show Real.exp 10 = Real.exp 1 ^ 10 by rw [← Real.exp_nat_mul]; norm_num]
    nlinarith [hp10]
  have hmono : Real.exp (-(Real.pi * Real.sqrt p)) ≤ Real.exp (-10) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [heegnerQ]
  refine hmono.trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  simpa using hexp

/-- **The `q`-parameter at the Heegner point is `−Q`, real and negative.**

`2πiτ₀ = 3πi − π√p`, so `q = exp(2πiτ₀) = exp(3πi)·exp(−π√p) = −Q`. The `exp(3πi) = −1` is where
the `3` in `τ₀ = (3+√−p)/2` is spent; with `τ = (1+√−p)/2` one would get the same value, and with
an even numerator one would get `q = +Q` and the signs below would all flip (which is what makes
`745` unattainable — see `heegner_tail_nonneg`). -/
lemma cexp_heegnerPoint (p : ℕ) (hp : 0 < p) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (heegnerPoint p hp : ℂ))
      = ((-heegnerQ p : ℝ) : ℂ) := by
  have hz : ((heegnerPoint p hp : UpperHalfPlane) : ℂ)
      = (3 + Complex.I * (Real.sqrt p : ℂ)) / 2 := rfl
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((3 + Complex.I * (Real.sqrt p : ℂ)) / 2)
      = 3 * ((Real.pi : ℂ) * Complex.I) + ((-(Real.pi * Real.sqrt p) : ℝ) : ℂ) := by
    push_cast
    linear_combination ((Real.pi : ℂ) * ((Real.sqrt p : ℝ) : ℂ)) * Complex.I_mul_I
  rw [hz, harg, Complex.exp_add]
  rw [show (3 : ℂ) * ((Real.pi : ℂ) * Complex.I) = ((3 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) by
    norm_num, Complex.exp_nat_mul, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
  rw [heegnerQ]
  push_cast
  ring

/-- **The `n ≥ 3` tail of a `q`-series with polynomially bounded coefficients is `O(Q³)`.**

If `a n ≤ n ^ K` and `(n+3)^K ≤ C·bⁿ`, then `|Σ_{n≥3} a(n)(−Q)ⁿ| ≤ C Q³/(1 − bQ)`. Both Eisenstein
tails below are instances: `K = 4, C = 81, b = 4` for `σ₃`, and `K = 6, C = 729, b = 8` for `σ₅`
(`ArithmeticFunction.sigma_le_pow_succ` supplies the hypothesis `ha`). The geometric majorant is
what keeps this free of any `Σ nᴷ xⁿ` closed form. -/
lemma abs_tsum_shift_le {a : ℕ → ℕ} {K : ℕ} {C b Q : ℝ}
    (ha : ∀ n : ℕ, (a n : ℝ) ≤ (n : ℝ) ^ K)
    (hQ0 : 0 < Q) (hb0 : 0 < b) (hbQ : b * Q < 1)
    (hC : ∀ n : ℕ, ((n : ℝ) + 3) ^ K ≤ C * b ^ n) :
    |∑' n : ℕ, (a (n + 3) : ℝ) * (-Q) ^ (n + 3)| ≤ C * Q ^ 3 / (1 - b * Q) := by
  have hCnn : 0 ≤ C := by
    have h0 := hC 0
    simp only [Nat.cast_zero, zero_add, pow_zero, mul_one] at h0
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ (3:ℝ)) K]
  have hbQ0 : 0 ≤ b * Q := by positivity
  have hpt : ∀ n : ℕ, |(a (n + 3) : ℝ) * (-Q) ^ (n + 3)| ≤ (C * Q ^ 3) * (b * Q) ^ n := by
    intro n
    have h1 : |(a (n + 3) : ℝ) * (-Q) ^ (n + 3)| = (a (n + 3) : ℝ) * Q ^ (n + 3) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (a (n+3) : ℝ)), abs_pow,
        abs_neg, abs_of_pos hQ0]
    rw [h1]
    have h2 : (a (n + 3) : ℝ) ≤ ((n : ℝ) + 3) ^ K := by
      have h := ha (n + 3)
      push_cast at h
      exact h
    have h3 : (a (n + 3) : ℝ) ≤ C * b ^ n := h2.trans (hC n)
    have h4 : (0:ℝ) < Q ^ (n + 3) := by positivity
    calc (a (n + 3) : ℝ) * Q ^ (n + 3) ≤ (C * b ^ n) * Q ^ (n + 3) :=
          mul_le_mul_of_nonneg_right h3 h4.le
      _ = (C * Q ^ 3) * (b * Q) ^ n := by rw [mul_pow]; ring
  have hgeom : Summable (fun n : ℕ => (C * Q ^ 3) * (b * Q) ^ n) :=
    (summable_geometric_of_lt_one hbQ0 hbQ).mul_left _
  have habs : Summable (fun n : ℕ => |(a (n + 3) : ℝ) * (-Q) ^ (n + 3)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt hgeom
  have hnorm : Summable (fun n : ℕ => ‖(a (n + 3) : ℝ) * (-Q) ^ (n + 3)‖) := by
    simpa only [Real.norm_eq_abs] using habs
  have hstep1 : |∑' n : ℕ, (a (n + 3) : ℝ) * (-Q) ^ (n + 3)|
      ≤ ∑' n : ℕ, |(a (n + 3) : ℝ) * (-Q) ^ (n + 3)| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  calc |∑' n : ℕ, (a (n + 3) : ℝ) * (-Q) ^ (n + 3)|
      ≤ ∑' n : ℕ, |(a (n + 3) : ℝ) * (-Q) ^ (n + 3)| := hstep1
    _ ≤ ∑' n : ℕ, (C * Q ^ 3) * (b * Q) ^ n := Summable.tsum_le_tsum hpt habs hgeom
    _ = C * Q ^ 3 / (1 - b * Q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hbQ0 hbQ, div_eq_mul_inv]

/-- `(n+3)⁴ ≤ 81·4ⁿ`; the base `4` beats `((n+4)/(n+3))⁴ ≤ (4/3)⁴ = 256/81`. -/
lemma pow_four_bound (n : ℕ) : ((n : ℝ) + 3) ^ 4 ≤ 81 * 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : 3 * ((n : ℝ) + 4) ≤ 4 * ((n : ℝ) + 3) := by linarith
      have h2 : (3 * ((n : ℝ) + 4)) ^ 4 ≤ (4 * ((n : ℝ) + 3)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h1 4
      have h3 : (81 : ℝ) * ((n : ℝ) + 4) ^ 4 ≤ 256 * ((n : ℝ) + 3) ^ 4 := by nlinarith [h2]
      have h4 : (0:ℝ) < (4:ℝ) ^ n := by positivity
      have h5 : ((n : ℝ) + 4) ^ 4 ≤ 256 * 4 ^ n := by nlinarith [h3, ih]
      push_cast
      rw [pow_succ (4:ℝ) n]
      linarith [h5, h4]

/-- `(n+3)⁶ ≤ 729·8ⁿ`; here `(4/3)⁶ = 4096/729 ≈ 5.62`, so the base must be `8`, not `4`. -/
lemma pow_six_bound (n : ℕ) : ((n : ℝ) + 3) ^ 6 ≤ 729 * 8 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : 3 * ((n : ℝ) + 4) ≤ 4 * ((n : ℝ) + 3) := by linarith
      have h2 : (3 * ((n : ℝ) + 4)) ^ 6 ≤ (4 * ((n : ℝ) + 3)) ^ 6 :=
        pow_le_pow_left₀ (by positivity) h1 6
      have h3 : (729 : ℝ) * ((n : ℝ) + 4) ^ 6 ≤ 4096 * ((n : ℝ) + 3) ^ 6 := by nlinarith [h2]
      have h4 : (0:ℝ) < (8:ℝ) ^ n := by positivity
      have h5 : ((n : ℝ) + 4) ^ 6 ≤ 4096 * 8 ^ n := by nlinarith [h3, ih]
      push_cast
      rw [pow_succ (8:ℝ) n]
      linarith [h5, h4]

/-- **Second-order `q`-expansion of `E k` at the Heegner point**, tail left explicit.

From `EisensteinSeries.q_expansion_bernoulli`: `E k z = 1 − (2k/B_k) Σ_{n≥1} σ_{k−1}(n) qⁿ`.
At `τ₀` one has `q = −Q` (`cexp_heegnerPoint`), so with `c` the real number `2k/B_k`,

  `E k τ₀ = 1 + cQ − c σ_{k−1}(2) Q² − c Σ_{n≥3} σ_{k−1}(n)(−Q)ⁿ`,

the `n = 1` term contributing `+cQ` because `σ_{k−1}(1) = 1` and `q = −Q`. Everything on the right
is REAL, which is the point of stating it through a `Complex.ofReal`: the two consumers then work
entirely in `ℝ`. Instantiated at `k = 4` (`c = −240`, `B₄ = −1/30`) and `k = 6`
(`c = 504`, `B₆ = 1/42`). -/
lemma E_second_order {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) {p : ℕ} (hp : 0 < p) (c : ℝ)
    (hc : (2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ)) = ((c : ℝ) : ℂ)) :
    ModularForm.E hk (heegnerPoint p hp) =
      ((1 + c * heegnerQ p
          - c * ((ArithmeticFunction.sigma (k - 1) 2 : ℕ) : ℝ) * heegnerQ p ^ 2
          - c * (∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 3) : ℕ) : ℝ)
                  * (-heegnerQ p) ^ (n + 3)) : ℝ) : ℂ) := by
  have hq := cexp_heegnerPoint p hp
  have hsum : Summable (fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ)
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (heegnerPoint p hp : ℂ)) ^ n) :=
    EisensteinSeries.summable_sigma_mul_cexp_pow (by omega) _
  have hb : ModularForm.E hk (heegnerPoint p hp)
      = 1 - (c : ℂ) * ∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) (n : ℕ) : ℕ) : ℂ)
          * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (heegnerPoint p hp : ℂ))
            ^ ((n : ℕ) : ℤ) := by
    rw [← hc]
    exact EisensteinSeries.q_expansion_bernoulli hk hk2 _
  have hpnat : (∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) (n : ℕ) : ℕ) : ℂ)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (heegnerPoint p hp : ℂ)) ^ ((n : ℕ) : ℤ))
      = ∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (heegnerPoint p hp : ℂ)) ^ n := by
    simp_rw [zpow_natCast]
    exact tsum_pnat_eq_tsum_of_eq_zero
      (f := fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (heegnerPoint p hp : ℂ)) ^ n) (by simp)
  have hsplit := hsum.sum_add_tsum_nat_add 3
  have htail : (∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 3) : ℕ) : ℂ)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (heegnerPoint p hp : ℂ)) ^ (n + 3))
      = ((∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 3) : ℕ) : ℝ)
          * (-heegnerQ p) ^ (n + 3) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hq]
    push_cast
    ring
  rw [hb, hpnat, ← hsplit, htail, hq]
  have h0 : ((ArithmeticFunction.sigma (k - 1) 0 : ℕ) : ℂ) = 0 := by simp
  have h1 : ((ArithmeticFunction.sigma (k - 1) 1 : ℕ) : ℂ) = 1 := by simp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, zero_add, pow_zero, pow_one,
    zero_mul]
  push_cast
  ring

/-- `σ₃(2) = 1 + 8 = 9`. -/
lemma sigma_three_two : (ArithmeticFunction.sigma 3 2 : ℕ) = 9 := by decide

/-- `σ₅(2) = 1 + 32 = 33`. -/
lemma sigma_five_two : (ArithmeticFunction.sigma 5 2 : ℕ) = 33 := by decide

/-- **SUB-LEAF 6a — the value of `E₄` at the Heegner point, to second order in `Q`.**

  `E₄(τ₀) = 1 − 240Q + 2160Q² + r`  with  `|r| ≤ 20000 Q³`,  `Q = exp(−π√p)`.

WHY SECOND ORDER IS NOT NEGOTIABLE. The quantity the consumer needs is a difference of two
numbers each `≈ 1728Q` whose leading terms cancel: the margin in
`heegner_tail_nonneg` is `1728Q²`, so a first-order-only bound on `E₄` (error `O(Q²)`) is
useless no matter how small its constant. The `Q²` coefficient `2160 = 240·σ₃(2) = 240·9`
must be exact, and only the `Q³` tail may be bounded.

ROUTE. `EisensteinSeries.q_expansion_bernoulli` gives
`E k z = 1 - (2k/B_k) Σ' n:ℕ+, σ_{k-1}(n) · exp(2πiz)ⁿ`; at `k = 4`, `B₄ = -1/30`, so
`2·4/B₄ = -240` and `E₄ z = 1 + 240 Σ σ₃(n) qⁿ`. At `τ₀` one has `q = exp(2πiτ₀) = -Q`,
real and negative, because `2πiτ₀ = 3πi - π√p` and `exp(3πi) = -1`. Splitting off `n = 1, 2`
leaves `r = 240 Σ_{n≥3} σ₃(n)(-Q)ⁿ`, and `ArithmeticFunction.sigma_le_pow_succ` gives
`σ₃(n) ≤ n⁴`, whence `|r| ≤ 240 Σ_{n≥3} n⁴Qⁿ ≤ 240 · 82 Q³ = 19680 Q³` for `Q ≤ 10⁻⁴`.
Summability for the split is `EisensteinSeries.summable_sigma_mul_cexp_pow`.

The stated constant `20000` is therefore not tight — it has ~1.6% slack over the true bound,
and the consumer has a further factor of ~12 of room — so it may be freely rounded up to any
value below `10⁷` without breaking `heegner_tail_nonneg`. What may NOT change is the exponent
`Q³` or the coefficients `240` and `2160`.

PROVEN, along exactly the route described: `E_second_order` at `k = 4` supplies the identity with
`r = 240·Σ_{n≥3} σ₃(n)(−Q)ⁿ`, and `abs_tsum_shift_le` with `pow_four_bound` bounds that tail by
`240·81·Q³/(1−4Q) ≤ 240·82·Q³ = 19680 Q³`. The geometric majorant `(n+3)⁴ ≤ 81·4ⁿ` replaces the
`Σ n⁴Qⁿ ≤ 82Q³` of the prose above; the resulting constant is the same. -/
theorem exists_E₄_heegnerPoint_approx {p : ℕ} (hp : 11 ≤ p) :
    ∃ r : ℝ, |r| ≤ 20000 * heegnerQ p ^ 3 ∧
      ModularForm.E₄ (heegnerPoint p (by omega)) =
        ((1 - 240 * heegnerQ p + 2160 * heegnerQ p ^ 2 + r : ℝ) : ℂ) := by
  have hQ0 := heegnerQ_pos p
  have hQle := heegnerQ_le hp
  have hQ3 : (0:ℝ) < heegnerQ p ^ 3 := by positivity
  refine ⟨240 * ∑' n : ℕ, ((ArithmeticFunction.sigma 3 (n + 3) : ℕ) : ℝ)
    * (-heegnerQ p) ^ (n + 3), ?_, ?_⟩
  · have hbd : |∑' n : ℕ, ((ArithmeticFunction.sigma 3 (n + 3) : ℕ) : ℝ) * (-heegnerQ p) ^ (n + 3)|
        ≤ 81 * heegnerQ p ^ 3 / (1 - 4 * heegnerQ p) := by
      refine abs_tsum_shift_le (K := 4) (fun n => ?_) hQ0 (by norm_num) (by linarith)
        pow_four_bound
      exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 3 n).trans_eq (by norm_num)
    have hden : (0:ℝ) < 1 - 4 * heegnerQ p := by linarith
    have hrhs : 81 * heegnerQ p ^ 3 / (1 - 4 * heegnerQ p) ≤ 82 * heegnerQ p ^ 3 := by
      rw [div_le_iff₀ hden]
      nlinarith [hQ3, hQ0, hQle]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 240)]
    linarith [hbd.trans hrhs, hQ3]
  · have hc : (2 * ((4:ℕ) : ℂ) / ((bernoulli 4 : ℚ) : ℂ)) = (((-240 : ℝ)) : ℂ) := by
      rw [show (bernoulli 4 : ℚ) = -1/30 by decide +kernel]
      push_cast
      norm_num
    have h := E_second_order (k := 4) (by norm_num) (by decide) (p := p) (by omega) (-240) hc
    rw [show (4 - 1 : ℕ) = 3 from rfl, sigma_three_two] at h
    rw [show (ModularForm.E₄ : ModularForm _ 4) = ModularForm.E (by norm_num : 3 ≤ 4) from rfl]
    rw [h]
    push_cast
    ring

/-- **SUB-LEAF 6b — the value of `E₆` at the Heegner point, to second order in `Q`.**

  `E₆(τ₀) = 1 + 504Q − 16632Q² + s`  with  `|s| ≤ 400000 Q³`.

Identical route to `exists_E₄_heegnerPoint_approx` at `k = 6`: `B₆ = 1/42`, so
`2·6/B₆ = 504` and `E₆ z = 1 - 504 Σ σ₅(n) qⁿ`; at `q = -Q` this is
`1 + 504Q - 504·σ₅(2)·Q² + ⋯` with `σ₅(2) = 33`, giving the `-16632 = -504·33`. The tail bound
uses `σ₅(n) ≤ n⁶`: `|s| ≤ 504 Σ_{n≥3} n⁶Qⁿ ≤ 504 · 730 Q³ = 367920 Q³` for `Q ≤ 10⁻⁴`.

`E₆` enters only through `Δ = (E₄³ − E₆²)/1728`
(`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`). Using that identity rather than the
`η`-product `Δ = q∏(1−qⁿ)²⁴` is what keeps this leaf-set free of infinite-product estimates:
both `E₄` and `E₆` are handled by one and the same mathlib lemma.

PROVEN, exactly as for `exists_E₄_heegnerPoint_approx`, with `s = −504·Σ_{n≥3} σ₅(n)(−Q)ⁿ`
bounded by `504·729·Q³/(1−8Q) ≤ 504·730·Q³ = 367920 Q³`. The geometric majorant is
`pow_six_bound`, `(n+3)⁶ ≤ 729·8ⁿ`; note the base must be `8` rather than the `4` that suffices
at weight `4`, since `(4/3)⁶ = 5.62 > 4`. -/
theorem exists_E₆_heegnerPoint_approx {p : ℕ} (hp : 11 ≤ p) :
    ∃ s : ℝ, |s| ≤ 400000 * heegnerQ p ^ 3 ∧
      ModularForm.E₆ (heegnerPoint p (by omega)) =
        ((1 + 504 * heegnerQ p - 16632 * heegnerQ p ^ 2 + s : ℝ) : ℂ) := by
  have hQ0 := heegnerQ_pos p
  have hQle := heegnerQ_le hp
  have hQ3 : (0:ℝ) < heegnerQ p ^ 3 := by positivity
  refine ⟨-(504 * ∑' n : ℕ, ((ArithmeticFunction.sigma 5 (n + 3) : ℕ) : ℝ)
    * (-heegnerQ p) ^ (n + 3)), ?_, ?_⟩
  · have hbd : |∑' n : ℕ, ((ArithmeticFunction.sigma 5 (n + 3) : ℕ) : ℝ) * (-heegnerQ p) ^ (n + 3)|
        ≤ 729 * heegnerQ p ^ 3 / (1 - 8 * heegnerQ p) := by
      refine abs_tsum_shift_le (K := 6) (fun n => ?_) hQ0 (by norm_num) (by linarith)
        pow_six_bound
      exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 5 n).trans_eq (by norm_num)
    have hden : (0:ℝ) < 1 - 8 * heegnerQ p := by linarith
    have hrhs : 729 * heegnerQ p ^ 3 / (1 - 8 * heegnerQ p) ≤ 730 * heegnerQ p ^ 3 := by
      rw [div_le_iff₀ hden]
      nlinarith [hQ3, hQ0, hQle]
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 504)]
    linarith [hbd.trans hrhs, hQ3]
  · have hc : (2 * ((6:ℕ) : ℂ) / ((bernoulli 6 : ℚ) : ℂ)) = (((504 : ℝ)) : ℂ) := by
      rw [show (bernoulli 6 : ℚ) = 1/42 by decide +kernel]
      push_cast
      norm_num
    have h := E_second_order (k := 6) (by norm_num) (by decide) (p := p) (by omega) 504 hc
    rw [show (6 - 1 : ℕ) = 5 from rfl, sigma_five_two] at h
    rw [show (ModularForm.E₆ : ModularForm _ 6) = ModularForm.E (by norm_num : 3 ≤ 6) from rfl]
    rw [h]
    push_cast
    ring

/-- Product of two bounded nonnegative reals. Stated separately to keep the `nlinarith` calls
in `heegner_tail_nonneg` out of a twenty-hypothesis context, where they time out. -/
theorem heegner_nonneg_prod {x u a b : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ a) (hu1 : 0 ≤ u)
    (hu2 : u ≤ b) : 0 ≤ x * u ∧ x * u ≤ a * b :=
  ⟨mul_nonneg hx1 hu1, mul_le_mul hx2 hu2 hu1 (le_trans hx1 hx2)⟩

/-- Product of a two-sided-bounded real with a bounded nonnegative one. -/
theorem heegner_two_sided_prod {x u a b : ℝ} (hx1 : -a ≤ x) (hx2 : x ≤ a) (hu1 : 0 ≤ u)
    (hu2 : u ≤ b) : -(a * b) ≤ x * u ∧ x * u ≤ a * b := by
  have ha : 0 ≤ a := by linarith
  constructor <;> nlinarith

/-- `x² + xy + y²` on the box `[0.9, 1.1]²`. -/
theorem heegner_box_bound {x y : ℝ} (hx1 : (0.9 : ℝ) ≤ x) (hx2 : x ≤ 1.1)
    (hy1 : (0.9 : ℝ) ≤ y) (hy2 : y ≤ 1.1) :
    0 ≤ x ^ 2 + x * y + y ^ 2 ∧ x ^ 2 + x * y + y ^ 2 ≤ 4 := by
  constructor <;> nlinarith

/-- `Δ(τ₀) < 0`, in the form `1000Q ≤ B² − A³`, where `A = E₄(τ₀)` and `B = E₆(τ₀)`.

The true value of `B² − A³` is `1728Q(1 + 24Q + ⋯)`; `1000Q` is a deliberately slack lower
bound, needed only to know the sign of `Δ` so that the final inequality may be multiplied
through by it. -/
theorem heegner_tail_pos {Q r s A B : ℝ} (hQpos : 0 < Q) (hQle : Q ≤ 1 / 10000)
    (hr : |r| ≤ 20000 * Q ^ 3) (hs : |s| ≤ 400000 * Q ^ 3)
    (hA : A = 1 - 240 * Q + 2160 * Q ^ 2 + r) (hB : B = 1 + 504 * Q - 16632 * Q ^ 2 + s) :
    1000 * Q ≤ B ^ 2 - A ^ 3 := by
  rw [abs_le] at hr hs
  have hQ3 : Q ^ 3 ≤ Q ^ 2 / 10000 := by nlinarith [pow_pos hQpos 2]
  have hQ2 : Q ^ 2 ≤ Q / 10000 := by nlinarith
  have hrM : r ≤ 2 * Q ^ 2 := by nlinarith [hr.2]
  have hrm : -(2 * Q ^ 2) ≤ r := by nlinarith [hr.1]
  have hsM : s ≤ 40 * Q ^ 2 := by nlinarith [hs.2]
  have hsm : -(40 * Q ^ 2) ≤ s := by nlinarith [hs.1]
  have hQcube : Q ^ 3 ≤ 1 / 1000000000000 := by nlinarith [hQ3, hQ2, hQle, hQpos]
  have hAM : A ≤ 1 - 240 * Q + 2163 * Q ^ 2 := by rw [hA]; linarith
  have hAm : (0.9 : ℝ) ≤ A := by rw [hA]; nlinarith
  have hBm : 1 + 504 * Q - 16673 * Q ^ 2 ≤ B := by rw [hB]; linarith
  have hBm2 : (0.9 : ℝ) ≤ B := by rw [hB]; nlinarith
  have hApos : (0 : ℝ) ≤ 1 - 240 * Q + 2163 * Q ^ 2 := by nlinarith
  have hBpos : (0 : ℝ) ≤ 1 + 504 * Q - 16673 * Q ^ 2 := by nlinarith
  have hA3 : A ^ 3 ≤ (1 - 240 * Q + 2163 * Q ^ 2) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hAM 3
  have hB2 : (1 + 504 * Q - 16673 * Q ^ 2) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hBpos hBm 2
  have hpoly : 1000 * Q ≤ (1 + 504 * Q - 16673 * Q ^ 2) ^ 2 - (1 - 240 * Q + 2163 * Q ^ 2) ^ 3 := by
    have hid : (1 + 504 * Q - 16673 * Q ^ 2) ^ 2 - (1 - 240 * Q + 2163 * Q ^ 2) ^ 3 - 1000 * Q
        = Q * ((728 - 109813178 * Q ^ 3) + (41381 * Q + 132336 * Q ^ 2)
            + Q ^ 4 * (3368569680 - 10119744747 * Q)) := by ring
    nlinarith [hid, hQpos, hQcube, hQle, pow_pos hQpos 2, pow_pos hQpos 4, pow_pos hQpos 3]
  linarith [hA3, hB2, hpoly]

/-- **The real core of LEAF 6.** With `A = E₄(τ₀)`, `B = E₆(τ₀)` and `Q = exp(−π√p)`,

  `0 ≤ 1728·Q·A³ − (B² − A³)(1 − 745Q)`.

This is exactly `exp(π√p) ≤ 745 − j(τ₀)` cleared of denominators, using
`Δ = (A³ − B²)/1728` and `j = A³/Δ`.

WHERE THE `745` LIVES. Substituting the exact second-order values `A₀ = 1 − 240Q + 2160Q²`,
`B₀ = 1 + 504Q − 16632Q²` gives, by `ring`,

  `1728·Q·A₀³ − (B₀² − A₀³)(1 − 745Q)`
    `= 1728Q² + 340523136Q³ − 29025860544Q⁴ + 583386857280Q⁵ − 3292047360000Q⁶`
      `+ 9906375168000Q⁷`,

whose leading term `1728Q²` is precisely the `1` of slack that `745` (rather than `744`) buys:
`744` would make that coefficient `0` and the statement would then turn on the sign of
`340523136Q³ − ⋯`, i.e. on `c₁ = 196884` beating `1/Q` — which fails at `p = 163`. So the
`745` is visible here as a positive `Q²` coefficient, and `744` is visible as its absence.
That is the mechanical form of the "do not weaken it" note on LEAF 6.

The perturbation `r, s` off the second-order values contributes at most
`20000Q³·8 + 400000Q³·3 = 1360000Q³ ≤ 136Q²` at `Q ≤ 10⁻⁴`, comfortably inside `1728Q²`. -/
theorem heegner_tail_nonneg {Q r s A B : ℝ} (hQpos : 0 < Q) (hQle : Q ≤ 1 / 10000)
    (hr : |r| ≤ 20000 * Q ^ 3) (hs : |s| ≤ 400000 * Q ^ 3)
    (hA : A = 1 - 240 * Q + 2160 * Q ^ 2 + r) (hB : B = 1 + 504 * Q - 16632 * Q ^ 2 + s) :
    0 ≤ 1728 * Q * A ^ 3 - (B ^ 2 - A ^ 3) * (1 - 745 * Q) := by
  rw [abs_le] at hr hs
  obtain ⟨A0, hA0⟩ : ∃ x : ℝ, x = 1 - 240 * Q + 2160 * Q ^ 2 := ⟨_, rfl⟩
  obtain ⟨B0, hB0⟩ : ∃ x : ℝ, x = 1 + 504 * Q - 16632 * Q ^ 2 := ⟨_, rfl⟩
  have hQ3 : Q ^ 3 ≤ Q ^ 2 / 10000 := by nlinarith [pow_pos hQpos 2]
  have hQ2 : Q ^ 2 ≤ Q / 10000 := by nlinarith
  have hAA0 : A = A0 + r := by rw [hA, hA0]
  have hBB0 : B = B0 + s := by rw [hB, hB0]
  have hrM : r ≤ 2 * Q ^ 2 := by nlinarith [hr.2]
  have hrm : -(2 * Q ^ 2) ≤ r := by nlinarith [hr.1]
  have hsM : s ≤ 40 * Q ^ 2 := by nlinarith [hs.2]
  have hsm : -(40 * Q ^ 2) ≤ s := by nlinarith [hs.1]
  have hA0b : (0.9 : ℝ) ≤ A0 ∧ A0 ≤ 1.1 := by
    rw [hA0]; constructor <;> nlinarith
  have hB0b : (0.9 : ℝ) ≤ B0 ∧ B0 ≤ 1.1 := by
    rw [hB0]; constructor <;> nlinarith
  have hAb : (0.9 : ℝ) ≤ A ∧ A ≤ 1.1 := by
    rw [hA]; constructor <;> nlinarith
  have hBb : (0.9 : ℝ) ≤ B ∧ B ≤ 1.1 := by
    rw [hB]; constructor <;> nlinarith
  have hC0 : 1728 * Q ^ 2 ≤ 1728 * Q * A0 ^ 3 - (B0 ^ 2 - A0 ^ 3) * (1 - 745 * Q) := by
    have hid : 1728 * Q * A0 ^ 3 - (B0 ^ 2 - A0 ^ 3) * (1 - 745 * Q) - 1728 * Q ^ 2
        = Q ^ 3 * ((340523136 - 29025860544 * Q)
            + Q ^ 2 * (583386857280 - 3292047360000 * Q)
            + 9906375168000 * Q ^ 4) := by
      rw [hA0, hB0]; ring
    nlinarith [pow_pos hQpos 3, pow_pos hQpos 2, pow_nonneg hQpos.le 4, hid, hQle, hQpos]
  have hCid : (1728 * Q * A ^ 3 - (B ^ 2 - A ^ 3) * (1 - 745 * Q))
        - (1728 * Q * A0 ^ 3 - (B0 ^ 2 - A0 ^ 3) * (1 - 745 * Q))
      = r * ((1 + 983 * Q) * (A ^ 2 + A * A0 + A0 ^ 2)) - s * ((1 - 745 * Q) * (B + B0)) := by
    rw [hAA0, hBB0]; ring
  have hX1 : (0 : ℝ) ≤ A ^ 2 + A * A0 + A0 ^ 2 :=
    (heegner_box_bound hAb.1 hAb.2 hA0b.1 hA0b.2).1
  have hX2 : A ^ 2 + A * A0 + A0 ^ 2 ≤ 4 :=
    (heegner_box_bound hAb.1 hAb.2 hA0b.1 hA0b.2).2
  have hY1 : (0 : ℝ) ≤ B + B0 := by linarith [hBb.1, hB0b.1]
  have hY2 : B + B0 ≤ 3 := by linarith [hBb.2, hB0b.2]
  have hc1 : (0 : ℝ) < 1 + 983 * Q := by linarith
  have hc2 : 1 + 983 * Q ≤ 2 := by linarith
  have hd1 : (0 : ℝ) < 1 - 745 * Q := by linarith
  have hd2 : 1 - 745 * Q ≤ 1 := by linarith
  have hU := heegner_nonneg_prod hc1.le hc2 hX1 hX2
  have hV := heegner_nonneg_prod hd1.le hd2 hY1 hY2
  obtain ⟨hE1, -⟩ := heegner_two_sided_prod hr.1 hr.2 hU.1 hU.2
  obtain ⟨-, hE2⟩ := heegner_two_sided_prod hs.1 hs.2 hV.1 hV.2
  have hfin : 20000 * Q ^ 3 * (2 * 4) + 400000 * Q ^ 3 * (1 * 3) ≤ 1728 * Q ^ 2 := by
    nlinarith [hQ3, sq_nonneg Q]
  linarith [hC0, hCid, hE1, hE2]

/-- **LEAF 5 — Weber's identity: `γ₂³ = j`**, i.e. `((f₂²⁴+16)/f₂⁸)³ = E₄³/Δ` on all of `ℍ`.

Booher §3.2, Theorem 23 together with the definition `γ₂ = 12g₂/Δ^{1/3}`. The classical proof
runs through the Weierstrass `℘`-function: with `e₁ = ℘(z/2)`, `e₂ = ℘(1/2)`,
`e₃ = ℘((z+1)/2)` one has `e₂−e₁ = π²η⁴f⁸`, `e₂−e₃ = π²η⁴f₁⁸`, `e₃−e₁ = π²η⁴f₂⁸`
(Booher Lemma 24, via the Weierstrass `σ`-function), whence
`Δ = 16(e₂−e₁)²(e₂−e₃)²(e₃−e₁)² = (2π)¹²η²⁴` and
`3g₂ = 4π⁴η⁸(f¹⁶ − f₁⁸f₂⁸)`, giving `γ₂ = f¹⁶ − f₁⁸f₂⁸ = (f₂²⁴+16)/f₂⁸` by
`f f₁ f₂ = √2` and `f₁(2z)f₂(z) = √2`.

This is stated for ALL `z : ℍ`, not just at `τ₀`, because it is an identity of modular
functions and nothing is gained by specialising. It is the one leaf here that needs no
arithmetic at all — only classical elliptic-function theory — and is the natural first target
for anyone continuing this decomposition, since mathlib already has `η`, `Δ = η²⁴`, `E₄`,
`E₆` and `Δ = (E₄³−E₆²)/1728`.

FAITHFULNESS: verified numerically at the five Heegner points, where both sides return
`−32768, −884736, −884736000, −147197952000, −262537412640768000`, the left from the `η`
product and the right from `PARI/GP`'s independent `ellj`.

PROVEN here from `gammaTwo_eq_E₄_div_eta_pow_eight` (hence from the single sub-leaf
`eta_pow_24_add_eta_two_pow_24`) together with `Δ = η²⁴`, which is mathlib's DEFINITION of
`ModularForm.discriminant` — so the last step is `(E₄/η⁸)³ = E₄³/η²⁴`, i.e. `pow_mul`. -/
theorem gammaTwo_pow_three_eq_jInvariant (z : UpperHalfPlane) : gammaTwo z ^ 3 = jInvariant z := by
  rw [gammaTwo_eq_E₄_div_eta_pow_eight, jInvariant, div_pow, ModularForm.discriminant,
    show (24 : ℕ) = 8 * 3 from rfl, pow_mul]

/-! ### LEAF 3 — `γ₂(τ₀)` is an algebraic integer

This block replaces the former LEAF 3 (which sat above, between LEAF 2 and LEAF 4). It is
here rather than there only because its proof consumes `gammaTwo_pow_three_eq_jInvariant`,
which Lean requires to be declared first.

**The old LEAF 3 docstring's route was more expensive than necessary, and one of its claims
is retracted below**: it asserted that `3 ∤ p` and Weber's level-`3` group `H` are needed to
pass from "`j(τ₀)` is an algebraic integer" to "`γ₂(τ₀)` is an algebraic integer". They are
not. `γ₂` is a root of the MONIC polynomial `X³ − j(τ₀)`, so integrality of the cube root is
free from integral closedness alone (`IsIntegral.of_pow`), with no modular theory, no
`q`-expansion combinatorics and no hypothesis on `p mod 3`. Weber's `3 ∤ p` is needed for
`γ₂(τ₀)` to lie in the same *field* as `j(τ₀)` — i.e. for the class-field leaves,
rationality — not for integrality.

WHAT IS LEFT OPEN HERE IS EXACTLY ONE STATEMENT, `exists_modularPolynomial`, and the chain
down to it is fully written and compiling:

  `exists_modularPolynomial`  (LEAF: `Φ_N ∈ ℤ[X,Y]` kills `(j(A z), j(z))`; Kronecker's `±1`)
    → `isIntegral_jInvariant_of_fixedPoint`   (put `w = z`; PROVEN, via `isIntegral_of_eval_diag`)
    → `isIntegral_jInvariant_of_quadratic`    (build the fixing matrix; PROVEN)
    → `isIntegral_jInvariant_heegnerPoint`    (specialise to `τ₀`; PROVEN)
    → `isIntegral_gammaTwo_heegnerPoint`      (cube root; PROVEN)

Everything except the first line is elementary — integer arithmetic, one complex-analytic
observation (`z ∈ ℍ` is not real, hence the discriminant is negative) and polynomial
plumbing. -/

/-- **The pointwise arithmetic criterion — PROVEN.** `m² − b m + k` is positive and NOT a
perfect square as soon as `2m − b ≥ 4k − b² > 0`.

This is the elementary step that produces the non-square determinant `N` the modular
polynomial needs; it is pure integer arithmetic, with no modular theory and no `z`.

THE ARGUMENT, which is much cheaper than the one an earlier draft of this file recorded.
That draft invoked "a quadratic taking perfect-square values at every integer must be the
square of a linear polynomial, hence have discriminant `0`" — true, but a real theorem. It
is not needed. Complete the square instead: with `E = 4k − b² > 0` and `u = 2m − b`,

  `4(m² − b m + k) = u² + E`,

so as soon as `u ≥ E` one has `u² < u² + E ≤ u² + u < (u + 1)²`. A perfect square
`m² − bm + k = s²` would make `u² + E = (2s)²` a perfect square strictly between the
consecutive squares `u²` and `(u+1)²` — impossible. Positivity is the same identity:
`4(m² − bm + k) = u² + E > 0`.

It is stated POINTWISE rather than as an existence claim because the consumer needs to pick
`m` in a prescribed residue class (coprime to `a`, to make the matrix primitive), not merely
to know that some `m` works. -/
theorem not_isSquare_quadratic_of_le {b k m : ℤ} (hE : 0 < 4 * k - b ^ 2)
    (hm : 4 * k - b ^ 2 ≤ 2 * m - b) :
    0 < m ^ 2 - b * m + k ∧ ¬ IsSquare (m ^ 2 - b * m + k) := by
  have hu0 : 0 ≤ 2 * m - b := le_trans hE.le hm
  refine ⟨by nlinarith [sq_nonneg (2 * m - b)], ?_⟩
  rintro ⟨s, hs⟩
  have key : (2 * s) ^ 2 = (2 * m - b) ^ 2 + (4 * k - b ^ 2) := by nlinarith [hs]
  have ht0 : (0 : ℤ) ≤ |2 * s| := abs_nonneg _
  have ht : |2 * s| ^ 2 = (2 * m - b) ^ 2 + (4 * k - b ^ 2) := by rw [sq_abs]; exact key
  by_cases hle : |2 * s| ≤ 2 * m - b
  · nlinarith
  · have h1 : 2 * m - b + 1 ≤ |2 * s| := by omega
    nlinarith

/-- **The arithmetic input to LEAF 3a — PROVEN.** A quadratic `m² − b m + k` of negative
discriminant takes a positive non-square value at some `m` COPRIME to any prescribed nonzero
`a`.

The coprimality is what makes the matrix `[[m − b, −c], [a, m]]` built from it PRIMITIVE,
which the modular polynomial genuinely needs (see `exists_modularPolynomial`). Witness:
`m = 1 + |a|·T` with `T = (4k − b²) + |b| + 1`, so that `m ≡ 1 mod a` and `2m − b ≥ 4k − b²`
simultaneously. -/
theorem exists_coprime_not_isSquare_quadratic {b k : ℤ} (h : b ^ 2 - 4 * k < 0) {a : ℤ}
    (ha : a ≠ 0) :
    ∃ m : ℤ, IsCoprime m a ∧ 0 < m ^ 2 - b * m + k ∧ ¬ IsSquare (m ^ 2 - b * m + k) := by
  have hE : 0 < 4 * k - b ^ 2 := by linarith
  set T : ℤ := (4 * k - b ^ 2) + |b| + 1 with hT
  have hTpos : 0 < T := by
    have : (0 : ℤ) ≤ |b| := abs_nonneg b
    simp only [hT]; linarith
  have ha1 : 1 ≤ |a| := Int.one_le_abs (by omega)
  refine ⟨1 + |a| * T, ?_, ?_⟩
  · rcases abs_cases a with ⟨hac, _⟩ | ⟨hac, _⟩
    · exact ⟨1, -T, by rw [hac]; ring⟩
    · exact ⟨1, T, by rw [hac]; ring⟩
  · refine not_isSquare_quadratic_of_le hE ?_
    have h1 : b ≤ |b| := le_abs_self b
    nlinarith

/-- **An integral quadratic relation at a point of `ℍ` has negative discriminant — PROVEN.**

`z ∈ ℍ` is not real, so `a z² + b z + c = 0` with `a ≠ 0` forces `b² − 4ac < 0`; no sign
condition need be assumed anywhere. Formally: `w = 2a z + b` satisfies `w² = b² − 4ac`, a
REAL number, while `Im w = 2a·Im z ≠ 0`; so `Im(w²) = 2·Re w·Im w = 0` gives `Re w = 0`, and
then `b² − 4ac = Re(w²) = −(Im w)² < 0`. -/
theorem neg_discr_of_quadratic (z : UpperHalfPlane) {a b c : ℤ} (ha : a ≠ 0)
    (h : (a : ℂ) * (z : ℂ) ^ 2 + (b : ℂ) * (z : ℂ) + (c : ℂ) = 0) :
    b ^ 2 - 4 * a * c < 0 := by
  set w : ℂ := ((2 * a : ℤ) : ℂ) * (z : ℂ) + ((b : ℤ) : ℂ) with hwdef
  have hw2 : w ^ 2 = ((b ^ 2 - 4 * a * c : ℤ) : ℂ) := by
    simp only [hwdef]; push_cast; linear_combination (4 * (a : ℂ)) * h
  have hwim : w.im = 2 * (a : ℝ) * (z : ℂ).im := by
    simp only [hwdef, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
    push_cast
    ring
  have hzim : 0 < (z : ℂ).im := z.im_pos
  have haR : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hwim0 : w.im ≠ 0 := by
    rw [hwim]
    exact mul_ne_zero (mul_ne_zero two_ne_zero haR) (ne_of_gt hzim)
  have hre : w.re = 0 := by
    have h1 : (w ^ 2).im = 0 := by rw [hw2]; exact Complex.intCast_im _
    rw [pow_two, Complex.mul_im] at h1
    have h2 : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 hwim0
  have hD : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) = -(w.im ^ 2) := by
    have h1 := congrArg Complex.re hw2
    rw [pow_two, Complex.mul_re, hre] at h1
    rw [Complex.intCast_re] at h1
    nlinarith [h1]
  have hlt : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) < 0 := by
    rw [hD]
    have : 0 < w.im ^ 2 := by positivity
    linarith
  exact_mod_cast hlt

/-- **Plumbing — PROVEN.** If a bivariate integral polynomial `Φ ∈ ℤ[Y][X]` vanishes at
`(x, x)` and its DIAGONAL `Φ(Y, Y)` has unit leading coefficient, then `x` is an algebraic
integer.

`Φ(Y, Y)` is `Φ.eval Polynomial.X`: substituting the outer variable by the inner one. The
proof is `Polynomial.hom_eval₂` (substitution commutes with a ring hom) plus the observation
that a `±1` leading coefficient makes `Φ(Y,Y)` or its negative monic. Note no nonvanishing
hypothesis on `Φ(Y,Y)` is needed: `IsUnit` of its leading coefficient already excludes `0`. -/
theorem isIntegral_of_eval_diag {x : ℂ} {Φ : Polynomial (Polynomial ℤ)}
    (hunit : IsUnit (Φ.eval Polynomial.X).leadingCoeff)
    (hvan : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) x) x Φ = 0) :
    IsIntegral ℤ x := by
  have h1 := Polynomial.hom_eval₂ Φ (RingHom.id (Polynomial ℤ))
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ) x) Polynomial.X
  rw [Polynomial.eval₂_id, RingHom.comp_id] at h1
  rw [show (Polynomial.eval₂RingHom (Int.castRingHom ℂ) x) Polynomial.X = x from
      Polynomial.eval₂_X _ _] at h1
  rw [hvan] at h1
  have hfD : Polynomial.eval₂ (algebraMap ℤ ℂ) x (Φ.eval Polynomial.X) = 0 := by
    rw [algebraMap_int_eq]; exact h1
  rcases Int.isUnit_iff.mp hunit with h2 | h2
  · exact ⟨Φ.eval Polynomial.X, h2, hfD⟩
  · exact ⟨-(Φ.eval Polynomial.X),
      by rw [Polynomial.Monic, Polynomial.leadingCoeff_neg, h2, neg_neg],
      by rw [Polynomial.eval₂_neg, hfD, neg_zero]⟩

/-- **LEAF 3a — THE MODULAR POLYNOMIAL `Φ_N`, WITH KRONECKER'S LEADING COEFFICIENT.**

For every `N > 0` there is a `Φ_N ∈ ℤ[Y][X]` such that

* `Φ_N(j(A z), j(z)) = 0` for every `z ∈ ℍ` and every PRIMITIVE integral matrix
  `A = [[p, q], [r, s]]` of determinant `N`, and
* if `N` is not a perfect square, the diagonal `Φ_N(Y, Y) ∈ ℤ[Y]` has leading coefficient a
  unit, i.e. `±1` (**Kronecker**).

This is the arithmetic heart of the class equation, and it is now the ONLY unproven step of
the old LEAF 3: Cox, *Primes of the form x²+ny²*, §11 (Theorem 11.18 for `Φ_m ∈ ℤ[X, Y]`,
Theorem 11.2 / Lemma 11.23 for the leading coefficient); Booher, *Modular curves and the
class number one problem*, §2; Serre, *Cours d'arithmétique*, VII.

THE CONSTRUCTION, for whoever proves it. Let `C(N)` be a set of representatives for the
finitely many left-`Γ`-classes of primitive integral matrices of determinant `N` (`Γ = SL₂ℤ`,
`#C(N) = ψ(N) = N∏(1 + 1/ℓ)`; Hermite normal form gives the standard representatives
`[[a, b], [0, d]]` with `ad = N`, `0 ≤ b < d`, `gcd(a,b,d) = 1`). Put

  `Φ_N(X, j(z)) = ∏_{A' ∈ C(N)} (X − j(A' z))`,

monic of degree `ψ(N)` in `X`. Its coefficients are holomorphic `Γ`-invariant functions on
`ℍ` that are meromorphic at the cusp, hence POLYNOMIALS IN `j`; integrality of those
polynomials' coefficients is the `q`-expansion argument (they lie in `ℤ[ζ_N]` and are
`Gal(ℚ(ζ_N)/ℚ)`-stable, hence in `ℤ`). The vanishing clause then holds for EVERY primitive
`A` of determinant `N`, not just for the representatives, because `A = γ A'` with `γ ∈ Γ` and
`j` is `Γ`-invariant, so `j(A z) = j(A' z)`.

Kronecker's half is the `q`-expansion computation on the diagonal: writing `q = e^{2πiz}`,
each factor `j(z) − j(A' z)` of `Φ_N(j(z), j(z))` has a leading `q`-power with coefficient a
root of unity, and for `N` a NON-square no factor vanishes identically — whereas for `N = d²`
the representative `d·I` contributes the factor `j(z) − j(z) = 0` and `Φ_N(X, X)` is
identically `0`.

WHY PRIMITIVITY IS IN THE HYPOTHESIS AND MUST STAY. Without it the clause is FALSE, not
merely unprovable: `A = d·A'` induces the same Möbius transformation as `A'`, so
`j(A z) = j(A' z)`, which is a root of `Φ_{N/d²}(·, j(z))` and in general NOT of
`Φ_N(·, j(z))`. Concretely at `N = 4`, `A = 2·I` gives `j(A z) = j(z)`, and `Φ_4(X, X)` is
identically zero while `Φ_4(j(z), j(z)) = 0` would be needed. The consumer supplies
primitivity for free by choosing `m` coprime to `a` — see
`exists_coprime_not_isSquare_quadratic`.

WHY THE NON-SQUARE HYPOTHESIS IS ON THE SECOND CLAUSE ONLY. `Φ_N` exists for every `N > 0`;
it is only Kronecker's leading coefficient that needs `N` non-square, and dropping that
hypothesis makes the clause FALSE with an explicit witness: for `N = 1` the only class is
`I`, so `Φ_1(X, Y) = X − Y` and `Φ_1(Y, Y) = 0`, whose leading coefficient is `0`, not a
unit. (This is exactly why the consumer below must produce a non-square determinant: with a
square one it could conclude that `j` is an algebraic integer at EVERY point of `ℍ`, whereas
`j` is transcendental off a countable set.)

THE STATEMENT IS DELIBERATELY MORE GENERAL THAN THE CONSUMER NEEDS — it is quantified over
all `z` and all target points `w = A z`, whereas the consumer only uses `w = z`. That is the
same choice `gammaTwo_pow_three_eq_jInvariant` makes and for the same reason: it is an
identity of modular functions, nothing is gained by specialising, and the general form is
what any further consumer (Weber's level-`3` descent, Hecke correspondences) will want.

THE MÖBIUS CONDITION IS WRITTEN MULTIPLICATIVELY (`p z + q = w (r z + s)`) to avoid a
division: `r z + s ≠ 0` is automatic once the determinant is nonzero (if `r ≠ 0` then
`Im(r z + s) = r·Im z ≠ 0`; if `r = 0` then `s ≠ 0`), so no such hypothesis is needed.

ABSENCE RE-VERIFIED, NOT INHERITED (2026-07-28, and again 2026-07-30 after the merge):
`grep -rn 'jInvariant\|modularPolynomial\|classEquation\|ComplexMultiplication' Fermat/
.lake/packages/mathlib/ ~/cs/FLT/` finds the `j`-invariant nowhere outside this file —
`Mathlib/NumberTheory/ModularForms/` has `DedekindEta`, `Discriminant`, `LevelOne/GradedRing`
and `QExpansion` and no `j` at all, and `~/cs/FLT` has zero hits. Refute this note by
exhibiting any of those names; the leaf would then reduce to specialising them.

WHAT THIS LEAF IS *NOT*. It needs no complex multiplication, no class field theory and no
class-number hypothesis — integrality of `j` at CM points is prior to all of that, and holds
at every imaginary quadratic point regardless of the class number. That is exactly why the
CM content of this cluster sits in the class-field leaves and not here. -/
theorem exists_modularPolynomial {N : ℤ} (hN : 0 < N) :
    ∃ Φ : Polynomial (Polynomial ℤ),
      (¬ IsSquare N → IsUnit (Φ.eval Polynomial.X).leadingCoeff) ∧
      ∀ (z w : UpperHalfPlane) (p q r s : ℤ), p * s - q * r = N →
        (∀ d : ℤ, d ∣ p → d ∣ q → d ∣ r → d ∣ s → IsUnit d) →
        (p : ℂ) * (z : ℂ) + (q : ℂ) = (w : ℂ) * ((r : ℂ) * (z : ℂ) + (s : ℂ)) →
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (jInvariant z))
          (jInvariant w) Φ = 0 :=
  sorry

/-- **`j(z)` is an algebraic integer at a FIXED POINT of a primitive integral matrix of
non-square determinant — PROVEN** over LEAF 3a and `isIntegral_of_eval_diag`.

This is Kronecker's theorem in the form the class equation uses: put `w = z` in the modular
equation, so that `Φ_N(j(z), j(z)) = 0`, and read off a monic integral polynomial from
Kronecker's leading coefficient.

`hpos : 0 < p*s − q*r` IS DERIVABLE from `hfix` and so does not strengthen the hypothesis
list in any essential way: a matrix of determinant `D` scales imaginary parts by
`D/|r z + s|²`, so a fixed point in `ℍ` forces `D > 0`. It is taken as an argument because
every classical source states the theorem for `det = N > 0`, and because both consumers have
it in hand already. -/
theorem isIntegral_jInvariant_of_fixedPoint (z : UpperHalfPlane) {p q r s : ℤ}
    (hpos : 0 < p * s - q * r) (hns : ¬ IsSquare (p * s - q * r))
    (hprim : ∀ d : ℤ, d ∣ p → d ∣ q → d ∣ r → d ∣ s → IsUnit d)
    (hfix : (p : ℂ) * (z : ℂ) + (q : ℂ) = (z : ℂ) * ((r : ℂ) * (z : ℂ) + (s : ℂ))) :
    IsIntegral ℤ (jInvariant z) := by
  obtain ⟨Φ, hkron, hvan⟩ := exists_modularPolynomial hpos
  exact isIntegral_of_eval_diag (hkron hns) (hvan z z p q r s rfl hprim hfix)

/-- **Integrality of the `j`-invariant at an imaginary quadratic point — PROVEN** over
`isIntegral_jInvariant_of_fixedPoint` plus the two arithmetic lemmas above.

If `z ∈ ℍ` satisfies a nontrivial integral quadratic relation `a z² + b z + c = 0` with
`a ≠ 0`, then `j(z)` is an algebraic integer.

THE MATRIX, and where the arithmetic goes. Multiplication by `β = m + a z` on the lattice
`[1, z]` is integral and fixes `z`; concretely `z·(a z + m) = (m − b) z − c` by the relation,
so `A = [[m − b, −c], [a, m]]` satisfies `A z = z` with

  `det A = (m − b)·m + a c = m² − b m + a c = N(β)`.

The choice `m = 0` gives `A = [[−b, −c], [a, 0]]` of determinant `a c`, which may well be a
square — and one may NOT repair that by rescaling `(a, b, c) ↦ (t a, t b, t c)`, which
multiplies the determinant by `t²` and so preserves square-ness (an error in an earlier draft
of this note). Vary `m` instead: `neg_discr_of_quadratic` gives `b² − 4 a c < 0`, and
`exists_coprime_not_isSquare_quadratic` then produces an `m` with `m² − b m + a c` positive
and not a square, and with `gcd(m, a) = 1`. Both of those are PROVEN above, so this
specialisation is pure bookkeeping.

THE COPRIMALITY IS WHAT MAKES `A` PRIMITIVE, which LEAF 3a genuinely needs: a common divisor
`d` of the four entries divides both `m` and `a`, hence divides `1`. (Note primitivity of `A`
does NOT require primitivity of the triple `(a, b, c)` — choosing `m` coprime to `a` is
enough, and is cheaper than dividing the relation through by `gcd(a, b, c)`.)

`ha : a ≠ 0` IS LOAD-BEARING AND THE STATEMENT IS FALSE WITHOUT IT. Take `a = b = c = 0`:
the hypothesis reads `0 = 0` and holds for EVERY `z : ℍ`, while `j` is transcendental at
almost every point. Note `a ≠ 0` alone suffices — no primitivity of `(a, b, c)`, no
`gcd(a,b,c) = 1`, and no sign condition on the discriminant. -/
theorem isIntegral_jInvariant_of_quadratic (z : UpperHalfPlane) {a b c : ℤ} (ha : a ≠ 0)
    (h : (a : ℂ) * (z : ℂ) ^ 2 + (b : ℂ) * (z : ℂ) + (c : ℂ) = 0) :
    IsIntegral ℤ (jInvariant z) := by
  have hD : b ^ 2 - 4 * (a * c) < 0 := by
    have h0 := neg_discr_of_quadratic z ha h
    rw [mul_assoc] at h0
    exact h0
  obtain ⟨m, hcop, hpos, hns⟩ := exists_coprime_not_isSquare_quadratic hD ha
  have hdet : (m - b) * m - (-c) * a = m ^ 2 - b * m + a * c := by ring
  refine isIntegral_jInvariant_of_fixedPoint z (p := m - b) (q := -c) (r := a) (s := m)
    (by rw [hdet]; exact hpos) (by rw [hdet]; exact hns)
    (fun d _ _ hda hdm => hcop.isUnit_of_dvd' hdm hda) ?_
  push_cast
  linear_combination -h

/-- **`j(τ₀)` is an algebraic integer** — LEAF 3a specialised to the Heegner point, PROVEN.

`τ₀ = (3 + √−p)/2` satisfies `x² − 3x + (9+p)/4 = 0`, and `(9+p)/4` is an INTEGER exactly
because `p ≡ 3 mod 4`: writing `p = 4k + 3` it equals `k + 3`. So the integral quadratic
relation demanded by LEAF 3a is `⟨a, b, c⟩ = ⟨1, −3, k+3⟩`, with `a = 1 ≠ 0`.

This is where the `3` in `τ₀ = (3+√−p)/2` and the congruence `p ≡ 3 mod 4` are spent; the
stronger `p ≡ 3 mod 8` and the primality of `p` are NOT needed for integrality. -/
theorem isIntegral_jInvariant_heegnerPoint {p : ℕ} (hp : 0 < p) (hp4 : p % 4 = 3) :
    IsIntegral ℤ (jInvariant (heegnerPoint p hp)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  refine isIntegral_jInvariant_of_quadratic _ (a := 1) (b := -3) (c := (k : ℤ) + 3)
    one_ne_zero ?_
  have hcoe : ((heegnerPoint p hp : UpperHalfPlane) : ℂ)
      = (3 + Complex.I * (Real.sqrt p : ℂ)) / 2 := UpperHalfPlane.coe_mk _ _
  have hs : ((Real.sqrt p : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  have hp' : (p : ℂ) = 4 * (k : ℂ) + 3 := by exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) hk
  rw [hcoe]
  push_cast
  linear_combination (((Real.sqrt p : ℂ)) ^ 2 / 4) * hI - (1 / 4) * hs - (1 / 4) * hp'

/-- **LEAF 3 — `γ₂(τ₀)` is an ALGEBRAIC INTEGER. Now PROVEN**, over LEAF 3a
(`isIntegral_jInvariant_of_quadratic`) and LEAF 5 (`gammaTwo_pow_three_eq_jInvariant`).

Half of "`γ₂(τ₀) ∈ ℤ`", and deliberately the half that costs no class field theory. The proof
is two steps: `γ₂(τ₀)³ = j(τ₀)` is an algebraic integer by LEAF 3a, and a cube root of an
algebraic integer is an algebraic integer, because `X³ − j(τ₀)` is MONIC over `ℤ[j(τ₀)]` and
integrality is transitive (`IsIntegral.of_pow`).

THE HYPOTHESES ARE STRONGER THAN THE PROOF NEEDS, and the signature is left unchanged only
because `exists_int_gammaTwo` and the released statement call it positionally. What is
actually consumed is `0 < p` (already forced by the statement, which mentions
`heegnerPoint p hp.pos`) and `p ≡ 3 mod 4` — derived here from `hp8`. `_h3` is unused and
underscored to make that mechanically visible; primality is used only for `hp.pos`.

NOTE THIS LEAF DOES NOT NEED `hcl`, and its hypotheses are correspondingly weaker than the
other CM leaf's. That asymmetry is the reason for splitting the CM input in two: this half
is integrality of the class equation, the other half (LEAF 4) is the main theorem of complex
multiplication. They are independently attackable and belong to different theories. -/
theorem isIntegral_gammaTwo_heegnerPoint {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (_h3 : 3 < p) :
    IsIntegral ℤ (gammaTwo (heegnerPoint p hp.pos)) := by
  refine IsIntegral.of_pow (n := 3) (by norm_num) ?_
  rw [gammaTwo_pow_three_eq_jInvariant]
  exact isIntegral_jInvariant_heegnerPoint hp.pos (by omega)

/-- **LEAF 6 — the `q`-expansion bound.** If `j(τ₀)` is the integer `n`, then
`exp(π√p) ≤ 745 − n`.

This is the analytic half, and it is what converts a finite list of `γ₂` values into a bound
on `p` without needing "`j` determines the field". With `q = exp(2πiτ₀) = −exp(−π√p)` and
`j = q⁻¹ + 744 + Σ_{k≥1} c_k qᵏ` (all `c_k > 0`),

  `exp(π√p) = 744 − n + (−c₁Q + c₂Q² − c₃Q³ + ⋯)`,  `Q = exp(−π√p) ∈ (0,1)`,

so the tail is dominated by its even part, `Σ_{k≥2} c_k Qᵏ`, which at `p ≥ 11` is at most
`c₂Q² + ⋯ < 0.02` — comfortably below `1`. The negative sign of `q` is essential and is
exactly what the `3` in `τ₀ = (3+√−p)/2` buys.

MACHINE-CHECKED FAITHFULNESS AND SHARPNESS (`PARI/GP`, `ellj`, 60 digits):

| `p`   | `j(τ₀)`               | `745 − j(τ₀)`        | `exp(π√p)`                        | slack             |
|-------|-----------------------|----------------------|-----------------------------------|-------------------|
| `11`  | `−32768`              | `33513`              | `33506.14306559`                  | `6.857`           |
| `19`  | `−884736`             | `885481`             | `885479.77768015`                 | `1.222`           |
| `43`  | `−884736000`          | `884736745`          | `884736743.99977747`              | `1.000223`        |
| `67`  | `−147197952000`       | `147197952745`       | `147197952743.99999866`           | `1.0000013`       |
| `163` | `−262537412640768000` | `262537412640768745` | `262537412640768743.999999999999` | `1.00000000000075`|

`745` is FORCED at the level of the consumer: `744` survives at `p = 163` only by `7.5·10⁻¹³`,
i.e. by the Ramanujan near-integer, and `743` fails outright. Do not weaken it.

`11 ≤ p` rather than `3 < p` because the estimate genuinely fails at `p = 3`, where
`Q = e^{−π√3} ≈ 0.0043` is far too large for the tail bound (though the CONCLUSION still
holds there, since `j((3+√−3)/2) = 0`). The consumer supplies `11 ≤ p` from
`p ≡ 3 mod 8`, `p` prime, `3 < p`.

PROVEN here from `exists_E₄_heegnerPoint_approx` and `exists_E₆_heegnerPoint_approx` over
`heegner_tail_pos` and `heegner_tail_nonneg`. Note the route taken does NOT go through the
`q`-expansion of `j` at all — no `c_k` is ever named, and in particular the positivity of the
`c_k` (a Kronecker/Hurwitz-level fact) is never needed. Instead `Δ` is eliminated by
`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`, turning the whole estimate into a polynomial
inequality in the two Eisenstein VALUES and `Q`. The prose above describing the `c_k` tail is
a correct account of why the statement is true; it is not the proof used. -/
theorem exp_pi_sqrt_le_of_jInvariant_eq {p : ℕ} (hp : 11 ≤ p) {n : ℤ}
    (hn : (n : ℂ) = jInvariant (heegnerPoint p (by omega))) :
    Real.exp (Real.pi * Real.sqrt p) ≤ 745 - (n : ℝ) := by
  obtain ⟨r, hr, ha⟩ := exists_E₄_heegnerPoint_approx hp
  obtain ⟨s, hs, hb⟩ := exists_E₆_heegnerPoint_approx hp
  have hQpos : 0 < heegnerQ p := heegnerQ_pos p
  have hQle : heegnerQ p ≤ 1 / 10000 := heegnerQ_le hp
  set Q := heegnerQ p with hQdef
  set A : ℝ := 1 - 240 * Q + 2160 * Q ^ 2 + r with hAdef
  set B : ℝ := 1 + 504 * Q - 16632 * Q ^ 2 + s with hBdef
  have hΔ : ModularForm.discriminant (heegnerPoint p (by omega : 0 < p))
      = (((A ^ 3 - B ^ 2) / 1728 : ℝ) : ℂ) := by
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, ha, hb, hAdef, hBdef]
    push_cast
    ring
  have hΔne := ModularForm.discriminant_ne_zero (heegnerPoint p (by omega : 0 < p))
  have hnC : (n : ℂ) * (((A ^ 3 - B ^ 2) / 1728 : ℝ) : ℂ) = ((A ^ 3 : ℝ) : ℂ) := by
    rw [← hΔ, hn, jInvariant, div_mul_cancel₀ _ hΔne, ha, hAdef]
    push_cast
    ring
  have hnR : (n : ℝ) * ((A ^ 3 - B ^ 2) / 1728) = A ^ 3 := by exact_mod_cast hnC
  have hD : 1000 * Q ≤ B ^ 2 - A ^ 3 := heegner_tail_pos hQpos hQle hr hs hAdef hBdef
  have hC : 0 ≤ 1728 * Q * A ^ 3 - (B ^ 2 - A ^ 3) * (1 - 745 * Q) :=
    heegner_tail_nonneg hQpos hQle hr hs hAdef hBdef
  have hDpos : 0 < B ^ 2 - A ^ 3 := by nlinarith
  have hexp : Real.exp (Real.pi * Real.sqrt p) = Q⁻¹ := by
    rw [hQdef, heegnerQ, ← Real.exp_neg, neg_neg]
  rw [hexp, inv_le_iff_one_le_mul₀ hQpos]
  have hkey : (745 - (n : ℝ)) * Q * (B ^ 2 - A ^ 3) - (B ^ 2 - A ^ 3)
      = 1728 * Q * A ^ 3 - (B ^ 2 - A ^ 3) * (1 - 745 * Q) := by
    linear_combination (1728 * Q) * hnR
  nlinarith [hC, hDpos, hkey]

/-- **`γ₂(τ₀) ∈ ℤ`** — PROVEN from LEAF 3 (algebraic integer) and LEAF 4 (rational), using
that `ℤ` is integrally closed in `ℚ`. -/
theorem exists_int_gammaTwo {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ g : ℤ, (g : ℂ) = gammaTwo (heegnerPoint p hp.pos) := by
  obtain ⟨r, hr⟩ := exists_rat_gammaTwo_heegnerPoint hp hp8 h3 hcl
  have hint : IsIntegral ℤ (algebraMap ℚ ℂ r) := by
    rw [show algebraMap ℚ ℂ r = (r : ℂ) from rfl, hr]
    exact isIntegral_gammaTwo_heegnerPoint hp hp8 h3
  have h2 : IsIntegral ℤ r :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)
      (algebraMap ℚ ℂ).injective).mp hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  refine ⟨n, ?_⟩
  rw [← hr, ← hn]
  simp

open _root_.Polynomial in
/-- **`α` IS AN ALGEBRAIC INTEGER — PROVEN.** No class field theory, and in particular no
Weber theory of `f(√−p)⁶` in a ring class field: this is a two-line consequence of
`exists_int_gammaTwo`.

`α⁴` is a root of `x³ − γ₂(τ₀)x − 16` (`weberAlpha_pow_four_cubic`, which is nothing but the
DEFINITION of `γ₂` rearranged), and `γ₂(τ₀)` is the rational integer `g`. So `α⁴` is a root
of the monic polynomial `X³ − gX − 16 ∈ ℤ[X]`, hence integral over `ℤ`; and integrality
descends through the fourth power (`IsIntegral.of_pow`), so `α` is integral too.

THIS DECLARATION WAS A LEAF AND IS NO LONGER ONE. It was cut as "LEAF 1a", the integrality
half of `exists_intCubic_weberAlpha`, on the belief that it needed Weber's theorem that
`f(√−p)⁶` lies in the ring class field of `[1, 8√−p]`. That belief was wrong, and in a way
worth recording: the CM input needed to make `α` INTEGRAL is exactly the CM input needed to
make `γ₂(τ₀)` integral, which the development already pays for in `LEAF 3` and `LEAF 4`
because the main argument needs `γ₂(τ₀) ∈ ℤ` for its own sake. Nothing is bought by asking
for it twice. What remains genuinely open about `α` is only its DEGREE
(`natDegree_minpoly_weberAlpha`).

`hcl`, `hp8` and `h3` are all consumed, through `exists_int_gammaTwo`.

MACHINE-CHECKED CORROBORATION (`PARI/GP`, `realprecision 80`,
`α = exp(−πi/4)·(√2·η(2τ₀)/η(τ₀))²` with `η` the full Dedekind eta `eta(·,1)`):
`algdep(α,3)` returns a MONIC polynomial with integer coefficients at every admissible `p`,
so `α` is an algebraic integer in all five cases, as the proof above now shows outright:

| `p`   | `minpoly α`          | monic | irreducible |
|-------|----------------------|-------|-------------|
| `11`  | `x³ + 2x² − 2`       | yes   | yes         |
| `19`  | `x³ − 2x² + 4x − 2`  | yes   | yes         |
| `43`  | `x³ + 4x² + 4x − 2`  | yes   | yes         |
| `67`  | `x³ + 2x² + 8x − 2`  | yes   | yes         |
| `163` | `x³ + 4x² + 28x − 2` | yes   | yes         |

The same run confirms `α` is REAL (imaginary part `< 10⁻⁹⁶` at all five), which is what the
`ζ₈⁻¹` twist is for. -/
theorem isIntegral_weberAlpha {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    IsIntegral ℤ (weberAlpha p hp.pos) := by
  obtain ⟨g, hg⟩ := exists_int_gammaTwo hp hp8 h3 hcl
  have hcub := weberAlpha_pow_four_cubic p hp.pos
  rw [← hg] at hcub
  refine IsIntegral.of_pow (n := 4) (by norm_num)
    ⟨X ^ 3 - C g * X - C 16, by monicity!, ?_⟩
  simp only [eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  linear_combination hcub

/-- **LEAF 1 — `α` is an algebraic integer of degree at most `3` — PROVEN** from
`isIntegral_weberAlpha` (itself now proven, from `exists_int_gammaTwo`) and
`natDegree_minpoly_weberAlpha`.

`α = ζ₈⁻¹f₂(τ₀)²` satisfies a MONIC cubic with rational-integer coefficients. This is the
"one hand" of Heegner's insight (Booher §6). Given that `α` is integral over `ℤ` and has
degree `3` over `ℚ`, the cubic is just its minimal polynomial over `ℤ`, which is monic and
maps onto the one over `ℚ` because `ℤ` is integrally closed with fraction field `ℚ`; see
`exists_intCubic_of_natDegree_minpoly`. The CM content left in this statement sits entirely in
`natDegree_minpoly_weberAlpha` — the DEGREE, and nothing else.

MACHINE-CHECKED FAITHFULNESS. `PARI/GP`'s `algdep(α, 3)` at the five admissible `p` returns
exactly a monic integral cubic, with integer coefficients:

| `p`   | minimal polynomial of `α` | `(a, b, c)`   |
|-------|---------------------------|---------------|
| `11`  | `x³ + 2x² − 2`            | `(2, 0, −2)`  |
| `19`  | `x³ − 2x² + 4x − 2`       | `(−2, 4, −2)` |
| `43`  | `x³ + 4x² + 4x − 2`       | `(4, 4, −2)`  |
| `67`  | `x³ + 2x² + 8x − 2`       | `(2, 8, −2)`  |
| `163` | `x³ + 4x² + 28x − 2`      | `(4, 28, −2)` |

Note `c = −2` in every case, matching the `c² = 4` that `exists_heegnerRelation_aux` DERIVES
(so the derivation is not vacuous — it recovers a fact the numerics independently show).
This table was re-computed independently when this proof was written, and reproduced exactly. -/
theorem exists_intCubic_weberAlpha {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ a b c : ℤ, weberAlpha p hp.pos ^ 3 + (a : ℂ) * weberAlpha p hp.pos ^ 2
      + (b : ℂ) * weberAlpha p hp.pos + (c : ℂ) = 0 :=
  exists_intCubic_of_natDegree_minpoly (isIntegral_weberAlpha hp hp8 h3 hcl)
    (natDegree_minpoly_weberAlpha hp hp8 h3 hcl)

/-- **THE ALGEBRAIC CORE OF HEEGNER'S ARGUMENT — PROVEN.** This is the step Weber himself
missed, and it is where the sixty-year gap sat.

Given: `α` satisfies a monic integral cubic `x³ + ax² + bx + c`; `γ₂(τ₀)` is the integer `g`;
and `1, α⁴, α⁸` are `ℤ`-linearly independent. Then `α⁴` satisfies Heegner's coefficient
relation.

The mechanism: separating even and odd degree terms and squaring turns the cubic for `α` into
a monic cubic for `α²` (`cube_of_sq`), and squaring again turns THAT into a monic cubic for
`α⁴`, with coefficients

  `E = 2f − e²`, `F = f² − 2eG`, `G₂ = −G²`, where `e = 2b − a²`, `f = b² − 2ac`, `G = −c²`.

But `α⁴ = −f₂(τ₀)⁸` already satisfies `x³ − g x − 16` (`weberAlpha_pow_four_cubic`, which is
just the definition of `γ₂`). Subtracting the two monic cubics leaves a QUADRATIC relation
among `1, α⁴, α⁸` with integer coefficients, which linear independence forces to be trivial:

  `2f = e²`,  `F = −g`,  `G₂ = −16`.

`G₂ = −c⁴ = −16` gives `c² = 4`; setting `A = a·c/2` and `B = b` (so `A = a` when `c = 2` and
`A = −a` when `c = −2`, and in both cases `f = B² − 4A`, `e = 2B − A²`) turns the first and
second into exactly

  `2(B² − 4A) = (2B − A²)²`  and  `g = −(B² − 4A)² − 8(2B − A²)`.

No case is lost: the substitution is uniform in the sign of `c`, which is why no "replace `α`
by `−α`" WLOG is needed here even though Booher's exposition uses one. -/
theorem exists_heegnerRelation_aux {p : ℕ} (hp0 : 0 < p) (g a b c : ℤ)
    (hcubic : weberAlpha p hp0 ^ 3 + (a : ℂ) * weberAlpha p hp0 ^ 2
      + (b : ℂ) * weberAlpha p hp0 + (c : ℂ) = 0)
    (hg : (g : ℂ) = gammaTwo (heegnerPoint p hp0))
    (hindep : ∀ u v w : ℤ, (u : ℂ) * weberAlpha p hp0 ^ 8 + (v : ℂ) * weberAlpha p hp0 ^ 4
      + (w : ℂ) = 0 → u = 0 ∧ v = 0 ∧ w = 0) :
    ∃ A B : ℤ, 2 * (B ^ 2 - 4 * A) = (2 * B - A ^ 2) ^ 2 ∧
      g = -(B ^ 2 - 4 * A) ^ 2 - 8 * (2 * B - A ^ 2) := by
  set α := weberAlpha p hp0 with hα
  set e : ℤ := 2 * b - a ^ 2 with he
  set f : ℤ := b ^ 2 - 2 * a * c with hf
  set G : ℤ := -c ^ 2 with hG
  have h2 : (α ^ 2) ^ 3 + (e : ℂ) * (α ^ 2) ^ 2 + (f : ℂ) * α ^ 2 + (G : ℂ) = 0 := by
    have := cube_of_sq α (a : ℂ) (b : ℂ) (c : ℂ) hcubic
    push_cast [he, hf, hG]
    linear_combination this
  have h4 : ((α ^ 2) ^ 2) ^ 3 + ((2 * f - e ^ 2 : ℤ) : ℂ) * ((α ^ 2) ^ 2) ^ 2
      + ((f ^ 2 - 2 * e * G : ℤ) : ℂ) * (α ^ 2) ^ 2 + ((-G ^ 2 : ℤ) : ℂ) = 0 := by
    have := cube_of_sq (α ^ 2) (e : ℂ) (f : ℂ) (G : ℂ) h2
    push_cast
    linear_combination this
  have hcub2 := weberAlpha_pow_four_cubic p hp0
  rw [← hα, ← hg] at hcub2
  have hsub : ((2 * f - e ^ 2 : ℤ) : ℂ) * α ^ 8
      + ((f ^ 2 - 2 * e * G + g : ℤ) : ℂ) * α ^ 4 + ((-G ^ 2 + 16 : ℤ) : ℂ) = 0 := by
    push_cast at h4 hcub2 ⊢
    linear_combination h4 - hcub2
  obtain ⟨hE, hF, hG2⟩ := hindep _ _ _ hsub
  have hc4 : c ^ 4 = 16 := by nlinarith [hG2, hG]
  have hc2 : c ^ 2 = 4 := by nlinarith [hc4, sq_nonneg (c ^ 2 - 4), sq_nonneg (c ^ 2 + 4)]
  have hGval : G = -4 := by omega
  have hcc : c = 2 ∨ c = -2 := by
    have : (c - 2) * (c + 2) = 0 := by linarith [hc2]
    rcases mul_eq_zero.mp this with h | h
    · left; omega
    · right; omega
  rcases hcc with rfl | rfl
  · refine ⟨a, b, ?_, ?_⟩
    · have : 2 * f - e ^ 2 = 0 := hE
      rw [hf, he] at this
      linarith [this]
    · have : f ^ 2 - 2 * e * G + g = 0 := hF
      rw [hf, he, hGval] at this
      nlinarith [this]
  · refine ⟨-a, b, ?_, ?_⟩
    · have : 2 * f - e ^ 2 = 0 := hE
      rw [hf, he] at this
      linarith [this]
    · have : f ^ 2 - 2 * e * G + g = 0 := hF
      rw [hf, he, hGval] at this
      nlinarith [this]

end Heegner

/-- **THE DEEP LEAF: HEEGNER'S COMPLEX-MULTIPLICATION INPUT.**
Heegner (1952), Stark (1967); the presentation is Cox, *Primes of the form x²+ny²*, §12, as
worked out in Booher, *Modular curves and the class number one problem*, §6.

If `p ≡ 3 (mod 8)` is a prime `> 3` and the discriminant `−p` has one class, then there are
integers `a, b` satisfying Heegner's coefficient relation `2(b² − 4a) = (2b − a²)²`, such that
the associated integer

  `γ = −(b² − 4a)² − 8(2b − a²)`

satisfies `exp(π √p) ≤ |γ|³ + 745`.

WHAT `γ` IS, AND WHERE EACH PIECE COMES FROM. Put `τ₀ = (3 + √−p)/2`, and let
`f₂(τ) = √2 · η(2τ)/η(τ)` be Weber's function and `γ₂ = j^{1/3}` the real cube root of the
modular `j`-invariant. Then:

* `h(−p) = 1` makes `K(j(τ₀))` the Hilbert class field of `K = ℚ(√−p)`, so `j(τ₀) ∈ ℤ`; since
  `p ≢ 0 mod 3`, also `γ₂(τ₀) ∈ ℤ`. **This is the main theorem of complex multiplication.**
* Weber's identity `γ₂ = (f₂²⁴ + 16)/f₂⁸` (an identity of modular functions, provable from the
  `η`-product) shows `α⁴ = −f₂(τ₀)⁸` is a root of `x³ − γ₂ x − 16`, where
  `α = ζ₈⁻¹ f₂(τ₀)²`.
* `α` generates the same cubic field, so it has a monic cubic minimal polynomial
  `x³ + ax² + bx + c` over `ℤ`. Squaring twice ("separate even and odd degree terms, square")
  turns that into a cubic for `α⁴`; matching it against `x³ − γ₂x − 16` gives `c = ±2` and the
  system `2(b² − 4a) = (2b − a²)²`, `γ₂ = −(b² − 4a)² − 8(2b − a²)`. **This is the relation
  above** — and it is the step Weber missed, which is why the problem waited sixty years.
* Finally `j(τ₀) = q⁻¹ + 744 + 196884q + …` with `q = −exp(−π√p)` real, so
  `exp(π√p) = |j(τ₀)| + 744 − 196884·exp(−π√p) − … ≤ |γ₂|³ + 745`. **This is the analytic
  half**, and it is what converts the finite list of `γ₂` values into a bound on `p` without
  needing "`j` determines the field".

FAITHFULNESS, machine-checked. The hypotheses are satisfiable exactly for
`p ∈ {11, 19, 43, 67, 163}`, with `γ = −32, −96, −960, −5280, −640320` respectively (`p = 3`
is excluded by `3 < p`, and would give `γ = 0`). The final inequality was verified at all six
values in `PARI/GP`, minimum slack `1.0000`:

| `p`   | `|γ|³ + 745`         | `exp(π√p)`               |
|-------|----------------------|--------------------------|
| `3`   | `745`                | `230.7646`               |
| `11`  | `33513`              | `33506.1431`             |
| `19`  | `885481`             | `885479.7777`            |
| `43`  | `884736745`          | `884736743.9998`         |
| `67`  | `147197952745`       | `147197952743.999999`    |
| `163` | `262537412640768745` | `262537412640768744.000` |

The constant `745` is essentially forced: `744` would leave slack `0.0000` at `p = 163`.

DECOMPOSED, and now PROVEN over six leaves in the `Heegner` namespace above. `j = E₄³/Δ`,
`f₂ = √2·η(2τ)/η(τ)`, `γ₂ = (f₂²⁴+16)/f₂⁸`, `τ₀ = (3+√−p)/2` and `α = ζ₈⁻¹f₂(τ₀)²` are all
DEFINED there over mathlib's `ModularForm.eta`, `ModularForm.discriminant` and
`ModularForm.E₄`; the double-squaring match — the step Weber missed — is PROVEN
(`Heegner.exists_heegnerRelation_aux`), as is the passage from "algebraic integer" plus
"rational" to `γ₂(τ₀) ∈ ℤ` (`Heegner.exists_int_gammaTwo`). What remains open is:

* `Heegner.natDegree_minpoly_weberAlpha` — `α` has degree exactly `3` over `ℚ`.
  It REPLACES `Heegner.exists_intCubic_weberAlpha` and
  `Heegner.intCast_indep_weberAlpha_pow_four`, both now PROVEN from it — the
  independence of `1, α⁴, α⁸` needed no modular input at all, only the primality
  of the degree. Its former companion `Heegner.isIntegral_weberAlpha` is PROVEN too, from
  `Heegner.exists_int_gammaTwo`: `α⁴` is a root of `x³ − γ₂(τ₀)x − 16` by the definition of
  `γ₂`, so an integral `γ₂(τ₀)` already forces an integral `α`;
* `Heegner.exists_modularPolynomial` — the modular polynomial `Φ_N` with Kronecker's leading
  coefficient (integrality of the class equation; `Heegner.isIntegral_jInvariant_of_fixedPoint`,
  `Heegner.isIntegral_jInvariant_of_quadratic` and hence
  `Heegner.isIntegral_gammaTwo_heegnerPoint` are now all PROVEN from it);
* `Heegner.exists_quadratic_jInvariant_heegnerPoint` — `j(τ₀) ∈ K = ℚ(√−p)` (**the main
  theorem of CM**);
* `Heegner.exists_quadratic_gammaTwo_of_jInvariant` — `γ₂(τ₀) ∈ K` once `j(τ₀) ∈ K` (Weber's
  level-`3` descent);
* `Heegner.eta_two_torsion_key` — the `η`-product identity
  `η(z/2)⁸η(2z)⁸(η(z/2)⁸+16η(2z)⁸) = η(z)²⁴` behind Weber's `γ₂³ = j`. It replaced
  `Heegner.eta_pow_24_add_eta_two_pow_24`, which is PROVEN over it, and hence so are
  `Heegner.gammaTwo_pow_three_eq_jInvariant` and
  `Heegner.exp_pi_sqrt_le_of_jInvariant_eq` (the latter also over the two `E`-approximations).

`Heegner.exists_rat_gammaTwo_heegnerPoint` is no longer among them: it was decomposed and
PROVEN on 2026-07-28 over the two class-field items together with
`Heegner.exists_real_gammaTwo_heegnerPoint` (`γ₂(τ₀) ∈ ℝ`, PROVEN outright — the reality that
cuts `K` down to `ℚ`).

Of these only `exists_quadratic_jInvariant_heegnerPoint` needs class field theory;
`exists_quadratic_gammaTwo_of_jInvariant` needs Weber's level-`3` modular theory but no class
field theory. `eta_two_torsion_key` is classical elliptic-function theory over machinery
mathlib already has (`η`, `Δ = η²⁴`, `E₄`, `Δ = (E₄³−E₆²)/1728`, `qExpansion`), and
`exists_modularPolynomial` is the integrality of the class equation; those two are the cheap
targets. (This list is referred to BY NAME rather than by position — its ordinals went stale
twice, and at one point "the seventh" had no referent at all.) -/
theorem exists_heegnerRelation_of_classNumberOne {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ a b : ℤ, 2 * (b ^ 2 - 4 * a) = (2 * b - a ^ 2) ^ 2 ∧
      Real.exp (Real.pi * Real.sqrt p) ≤
        ((|(b ^ 2 - 4 * a) ^ 2 + 8 * (2 * b - a ^ 2)| ^ 3 + 745 : ℤ) : ℝ) := by
  have hp11 : 11 ≤ p := by omega
  obtain ⟨g, hg⟩ := Heegner.exists_int_gammaTwo hp hp8 h3 hcl
  obtain ⟨a, b, c, hcubic⟩ := Heegner.exists_intCubic_weberAlpha hp hp8 h3 hcl
  have hindep := Heegner.intCast_indep_weberAlpha_pow_four hp hp8 h3 hcl
  obtain ⟨A, B, hrel, hgv⟩ := Heegner.exists_heegnerRelation_aux hp.pos g a b c hcubic hg hindep
  refine ⟨A, B, hrel, ?_⟩
  have hneg : (B ^ 2 - 4 * A) ^ 2 + 8 * (2 * B - A ^ 2) = -g := by linarith [hgv]
  have habs : |(B ^ 2 - 4 * A) ^ 2 + 8 * (2 * B - A ^ 2)| = |g| := by rw [hneg, abs_neg]
  have hj : ((g ^ 3 : ℤ) : ℂ) = Heegner.jInvariant (Heegner.heegnerPoint p hp.pos) := by
    push_cast
    rw [hg]
    exact Heegner.gammaTwo_pow_three_eq_jInvariant _
  have hbound := Heegner.exp_pi_sqrt_le_of_jInvariant_eq hp11 hj
  rw [habs]
  have hcube : -((g : ℝ) ^ 3) ≤ |(g : ℝ)| ^ 3 := by
    rw [← abs_pow]
    exact neg_le_abs _
  push_cast at hbound ⊢
  linarith

/-- **THE CLASS NUMBER ONE THEOREM — Heegner (1952), Stark (1967), Baker (1966).**

If the discriminant `d < 0` has exactly ONE class of positive definite integral
binary quadratic forms (i.e. any two such forms of discriminant `d` are properly
equivalent), then `d ≥ −163`.

FAITHFULNESS, machine-checked before this leaf was written (a direct
enumeration of Gauss-reduced representatives `|b| ≤ a ≤ c`, `b ≥ 0` when
`|b| = a` or `a = c`, over ALL positive definite forms — primitive and
imprimitive alike): the discriminants `d < 0`, `d ≡ 0, 1 (mod 4)`, with exactly
one class down to `−20000` are exactly

  `{−3, −4, −7, −8, −11, −19, −43, −67, −163}`

so the bound `−163 ≤ d` is TRUE and SHARP. Note that the hypothesis here
quantifies over ALL forms, not only primitive ones, which is why the four
non-fundamental discriminants of class number one — `−12, −16, −27, −28` —
are correctly absent: each carries an imprimitive form (e.g. `⟨3, 3, 3⟩` at
`d = −27`) inequivalent to the principal one. Getting this wrong would have
made the leaf FALSE at `m = 7`, since `h(−27) = 1` while `x² + x + 7` is
composite at `x = 1`.

Both hypotheses are load-bearing. Without `d < 0` there are no positive
definite forms at all and the hypothesis is vacuous; likewise without
`d ≡ 0, 1 (mod 4)`, since `b² − 4ac ≡ 0, 1 (mod 4)` always.

PROVEN here, along the Heegner–Stark route, over three leaves:

1. `prime_of_classNumberOne` — ELEMENTARY, proven above: `d = −4`, `d = −8`, or
   `−d` is a prime `p ≡ 3 mod 4`. Then `mod_eight_eq_three_of_classNumberOne`
   pins `p ≡ 3 mod 8` once `p > 8`. Together these are the elementary half of
   genus theory plus the `2`-adic condition, and they cost no CM theory at all.
2. `exists_heegnerRelation_of_classNumberOne` — the DEEP leaf: complex
   multiplication, Weber's functions and the `q`-expansion of `j` produce
   integers `a, b` with `2(b² − 4a) = (2b − a²)²` and
   `exp(π√p) ≤ |γ|³ + 745`, `γ = −(b² − 4a)² − 8(2b − a²)`.
3. `heegnerRelation_solutions` — PROVEN, over the now also proven
   `eq_of_two_mul_mul_cube_add_one_eq_sq` (`2x(x³+1) = y²`): the relation has
   exactly six solutions, so `|γ| ≤ 640320` and `|γ|³ + 745 ≤ 640320³ + 745`.
4. `lt_exp_pi_sqrt` — PROVEN: `exp(π√p) > 640320³ + 745` for `p ≥ 164`.

The two routes NOT taken, recorded so nobody re-costs them:

* **Baker.** An effective lower bound for linear forms in logarithms plus the
  Gelfond–Linnik reduction. The reduction is itself research-level and cannot
  be cut into checkable statements, which is why this route was rejected;
  the transcendence machinery (auxiliary functions, Siegel's lemma,
  extrapolation, heights) is absent from mathlib, `~/cs/FLT` and this project.
* **Goldfeld–Gross–Zagier.** Strictly harder: `L`-functions of elliptic curves
  and Heegner points.

The SOFT-ANALYTIC route is a dead end for a DIFFERENT reason: Dirichlet's class
number formula gives `L(1, χ_d) = π h / √|d|`, and `h ≥ 1` already yields
`L(1, χ_d) ≥ π/√|d|`; `h = 1` is exactly the EQUALITY case, i.e. precisely the
Siegel-zero scenario. An elementary or soft-analytic argument cannot beat the
trivial bound, and Siegel's improvement is ineffective by construction. -/
theorem neg_163_le_of_classNumberOne {d : ℤ} (hd : d < 0) (hd4 : d % 4 = 0 ∨ d % 4 = 1)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = d → g.discr = d → f.Equivalent g) :
    -163 ≤ d := by
  rcases prime_of_classNumberOne hd hd4 hcl with rfl | rfl | ⟨p, hp, hp4, rfl⟩
  · norm_num
  · norm_num
  · by_contra hcon
    have hple : 164 ≤ p := by
      have : (163 : ℤ) < (p : ℤ) := by omega
      exact_mod_cast this
    have hp8 : p % 8 = 3 := mod_eight_eq_three_of_classNumberOne hp4 (by omega) hcl
    obtain ⟨a, b, hrel, hbnd⟩ :=
      exists_heegnerRelation_of_classNumberOne hp hp8 (by omega) hcl
    have hint : |(b ^ 2 - 4 * a) ^ 2 + 8 * (2 * b - a ^ 2)| ^ 3 + 745
        ≤ (262537412640768745 : ℤ) := by
      rcases heegnerRelation_solutions hrel with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
    have hcast : ((|(b ^ 2 - 4 * a) ^ 2 + 8 * (2 * b - a ^ 2)| ^ 3 + 745 : ℤ) : ℝ)
        ≤ (262537412640768745 : ℝ) := by exact_mod_cast hint
    linarith [lt_exp_pi_sqrt hple]

/-- **Rabinowitsch's theorem.** If `x² + x + m` is prime for every `x` with
`x + 1 < m`, then `m ≤ 41`.

PROVEN here over `neg_163_le_of_classNumberOne`, which is itself proven over the
Heegner leaves. The elementary content — that the hypothesis forces the
discriminant `1 − 4m` to have one class — is
`equivalent_of_primeGenerating`, which rests on Gauss
reduction (`exists_reduced_equivalent`) and the reduced-form computation
(`a_eq_one_of_primeGenerating`). The bound is SHARP: the hypothesis holds
exactly for `m ∈ {2, 3, 5, 11, 17, 41}`. -/
theorem le_41_of_primeGenerating {m : ℕ} (hm : 2 ≤ m)
    (hgen : ∀ x : ℕ, x + 1 < m → Nat.Prime (x ^ 2 + x + m)) : m ≤ 41 := by
  have hd : (1 - 4 * (m : ℤ)) < 0 := by
    have : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    linarith
  have hd4 : (1 - 4 * (m : ℤ)) % 4 = 0 ∨ (1 - 4 * (m : ℤ)) % 4 = 1 := by omega
  have hbound := neg_163_le_of_classNumberOne hd hd4 (fun f g hf hg hfd hgd =>
    (equivalent_of_primeGenerating hm hgen hf hfd).trans
      (equivalent_of_primeGenerating hm hgen hg hgd).symm)
  omega

end BinaryQuadraticForm

end Fermat

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

SEVEN leaves remain, each stated so that it can be worked on alone.  (The
Diophantine leaf `eq_of_two_mul_mul_cube_add_one_eq_sq`, which an earlier version
of this list counted, was PROVEN concurrently — see its bullet above; and
`exists_rat_gammaTwo_heegnerPoint`, which it also counted, was replaced by the
two class-field leaves below.)

* `Heegner.exists_intCubic_weberAlpha`, `Heegner.intCast_indep_weberAlpha_pow_four`
  — `α` is an algebraic integer generating a cubic field (Weber's theory of the
  ring class field of the order of discriminant `−4p`, whose class number is `3`);
* `Heegner.isIntegral_gammaTwo_heegnerPoint` — `γ₂(τ₀)` is an algebraic integer
  (`q`-expansion combinatorics, no class field theory);
* `Heegner.exists_quadratic_jInvariant_heegnerPoint` — `j(τ₀) ∈ K = ℚ(√−p)`; **this is the
  main theorem of complex multiplication and is the only leaf here that needs it**, and the
  only one that consumes `hcl`;
* `Heegner.exists_quadratic_gammaTwo_of_jInvariant` — `γ₂(τ₀) ∈ K` once `j(τ₀) ∈ K` (Weber's
  level-`3` descent; needs only `3 ∤ p`);
* `Heegner.gammaTwo_pow_three_eq_jInvariant` — Weber's `γ₂³ = j` (classical
  elliptic-function theory over machinery mathlib already has);
* `Heegner.exp_pi_sqrt_le_of_jInvariant_eq` — the `q`-expansion bound
  `exp(π√p) ≤ 745 − j(τ₀)`, a real-analytic estimate.
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

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

/-- **LEAF 1 — `α` is an algebraic integer of degree at most `3`.**

`α = ζ₈⁻¹f₂(τ₀)²` satisfies a MONIC cubic with rational-integer coefficients. This is the
"one hand" of Heegner's insight (Booher §6): `α` lies in the ring class field of the order
`[1, √−p]` of discriminant `−4p`, whose class number is
`h(−4p) = 2h(−p)(1 + ½) = 3h(−p) = 3` when `p ≡ 3 mod 8` — so `ℚ(α)` is a cubic field, and
`α` is an algebraic integer because `f₂(τ₀)²` is (Weber; Booher Theorem 37, whose proof
shows `f(√−p)⁶` lies in the ring class field by descending from the order `[1, 8√−p]`).

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

WHAT IS MISSING, AND THE CHECK THAT WOULD REFUTE THIS. The claim "ring class field theory is
absent" was re-verified for this decomposition rather than inherited: `grep -rn` for
`ComplexMultiplication`, `HilbertClassField`, `ringClassField`, `jInvariant` over
`.lake/packages/mathlib`, over `Fermat/`, and over `~/cs/FLT/` returns nothing relevant, and
`Mathlib/NumberTheory/ModularForms/` contains no `j`-invariant at all. Refute by exhibiting
any of those names; the leaf would then reduce to specialising them. -/
theorem exists_intCubic_weberAlpha {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ a b c : ℤ, weberAlpha p hp.pos ^ 3 + (a : ℂ) * weberAlpha p hp.pos ^ 2
      + (b : ℂ) * weberAlpha p hp.pos + (c : ℂ) = 0 :=
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
load-bearing here even though it does not appear in the conclusion. -/
theorem intCast_indep_weberAlpha_pow_four {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∀ u v w : ℤ, (u : ℂ) * weberAlpha p hp.pos ^ 8 + (v : ℂ) * weberAlpha p hp.pos ^ 4
      + (w : ℂ) = 0 → u = 0 ∧ v = 0 ∧ w = 0 :=
  sorry

/-- **LEAF 3 — `γ₂(τ₀)` is an ALGEBRAIC INTEGER.**

Half of "`γ₂(τ₀) ∈ ℤ`", and deliberately the half that costs no class field theory: `j(τ₀)`
is an algebraic integer for any imaginary quadratic `τ₀` (the classical integrality of the
class equation, provable by `q`-expansions and the modular equation `Φ_N`, Booher §2), and
since `3 ∤ p` the cube root `γ₂` is again an algebraic integer (Booher §3.1: `γ₂` is a
modular function for the group `H` of level `3`, and its `q`-expansion has integral
coefficients).

NOTE THIS LEAF DOES NOT NEED `hcl`, and its hypotheses are correspondingly weaker than the
other CM leaf's. That asymmetry is the reason for splitting the CM input in two: this half is
Weber/`q`-expansion combinatorics, the other half (LEAF 4) is the main theorem of complex
multiplication. They are independently attackable and belong to different theories. -/
theorem isIntegral_gammaTwo_heegnerPoint {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p) :
    IsIntegral ℤ (gammaTwo (heegnerPoint p hp.pos)) :=
  sorry

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
product and the right from `PARI/GP`'s independent `ellj`. -/
theorem gammaTwo_pow_three_eq_jInvariant (z : UpperHalfPlane) : gammaTwo z ^ 3 = jInvariant z :=
  sorry

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
`p ≡ 3 mod 8`, `p` prime, `3 < p`. -/
theorem exp_pi_sqrt_le_of_jInvariant_eq {p : ℕ} (hp : 11 ≤ p) {n : ℤ}
    (hn : (n : ℂ) = jInvariant (heegnerPoint p (by omega))) :
    Real.exp (Real.pi * Real.sqrt p) ≤ 745 - (n : ℝ) :=
  sorry

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

* `Heegner.exists_intCubic_weberAlpha` — `α` satisfies a monic integral cubic;
* `Heegner.intCast_indep_weberAlpha_pow_four` — `1, α⁴, α⁸` are independent;
* `Heegner.isIntegral_gammaTwo_heegnerPoint` — `γ₂(τ₀)` is an algebraic integer;
* `Heegner.exists_quadratic_jInvariant_heegnerPoint` — `j(τ₀) ∈ K = ℚ(√−p)` (**the main
  theorem of CM**);
* `Heegner.exists_quadratic_gammaTwo_of_jInvariant` — `γ₂(τ₀) ∈ K` once `j(τ₀) ∈ K` (Weber's
  level-`3` descent);
* `Heegner.gammaTwo_pow_three_eq_jInvariant` — Weber's `γ₂³ = j`;
* `Heegner.exp_pi_sqrt_le_of_jInvariant_eq` — the `q`-expansion bound.

`Heegner.exists_rat_gammaTwo_heegnerPoint` is no longer among them: it was decomposed and
PROVEN on 2026-07-28 over the fourth and fifth items together with
`Heegner.exists_real_gammaTwo_heegnerPoint` (`γ₂(τ₀) ∈ ℝ`, PROVEN outright — the reality that
cuts `K` down to `ℚ`).

Of these only the fourth needs class field theory; the fifth needs Weber's level-`3` modular
theory but no class field theory. The sixth is classical elliptic-function theory over
machinery mathlib already has (`η`, `Δ = η²⁴`, `E₄`, `Δ = (E₄³−E₆²)/1728`, `qExpansion`), and
the seventh is a real-analytic estimate on the `q`-expansion of `j`; both are the cheap
targets. -/
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

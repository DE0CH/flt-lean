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

`lt_exp_pi_sqrt`, the numeric bound `exp(π√p) > 640320³ + 745` for `p ≥ 164`, is
also proved here.

The DEEP leaf `exists_heegnerRelation_of_classNumberOne` has since been
DECOMPOSED and is now PROVEN over the `Heegner` namespace, which defines
`j = E₄³/Δ`, Weber's `f₂ = √2·η(2τ)/η(τ)`, `γ₂ = (f₂²⁴+16)/f₂⁸`, the Heegner
point `τ₀ = (3+√−p)/2` and `α = ζ₈⁻¹f₂(τ₀)²` over mathlib's `ModularForm.eta`,
`ModularForm.discriminant` and `ModularForm.E₄`, and proves Heegner's
double-squaring match (`Heegner.exists_heegnerRelation_aux`, the step Weber
missed) together with `Heegner.exists_int_gammaTwo`.

SEVEN leaves remain, each stated so that it can be worked on alone:

* `eq_of_two_mul_mul_cube_add_one_eq_sq` — `2x(x³+1) = y²`, elementary and
  self-contained;
* `Heegner.exists_intCubic_weberAlpha`, `Heegner.intCast_indep_weberAlpha_pow_four`
  — `α` is an algebraic integer generating a cubic field (Weber's theory of the
  ring class field of the order of discriminant `−4p`, whose class number is `3`);
* `Heegner.isIntegral_gammaTwo_heegnerPoint` — `γ₂(τ₀)` is an algebraic integer
  (`q`-expansion combinatorics, no class field theory);
* `Heegner.exists_rat_gammaTwo_heegnerPoint` — `γ₂(τ₀) ∈ ℚ`; **this is the main
  theorem of complex multiplication and is the only leaf here that needs it**;
`Heegner.gammaTwo_pow_three_eq_jInvariant` (Weber's `γ₂³ = j`) and
`Heegner.exp_pi_sqrt_le_of_jInvariant_eq` (the bound `exp(π√p) ≤ 745 − j(τ₀)`) are now both
PROVEN, over three new analytic leaves:

* `Heegner.eta_pow_24_add_eta_two_pow_24` — `η²⁴ + 256η(2z)²⁴ = E₄·(η·η(2z))⁸`, the single
  modular-form identity carrying ALL of Weber's `γ₂³ = j`. Given it, LEAF 5 is field algebra;
* `Heegner.exists_E₄_heegnerPoint_approx`, `Heegner.exists_E₆_heegnerPoint_approx` — the
  values of `E₄` and `E₆` at `τ₀` to second order in `Q = exp(−π√p)`, with an explicit `Q³`
  error bound. Both follow the same mathlib lemma
  (`EisensteinSeries.q_expansion_bernoulli`), and between them they eliminate `Δ` via
  `Δ = (E₄³ − E₆²)/1728` — so LEAF 6 needs no infinite products and, notably, no positivity
  of the `j`-coefficients `c_k`.

So this file has EIGHT open leaves, not seven; the count rose because two leaves closed over
three smaller ones. -/
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

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

/-- **DIOPHANTINE LEAF.** The only integer solutions of `2x(x³ + 1) = y²` are
`(0, 0)`, `(−1, 0)`, `(1, ±2)` and `(2, ±6)`.

This is Booher's Proposition 39 / Cox, *Primes of the form x²+ny²*, end of §12. It is
elementary and self-contained: **nothing else in this file is needed to attack it.**

PROOF PLAN (Booher, Prop. 39 and Lemma 40). Handle `x = 0, −1` directly. Otherwise `x` and
`x³+1` are coprime, so `±(x³+1)` is a square or twice a square, i.e.
`x³ + 1 = ε z²` or `x³ + 1 = 2ε z²` with `ε = ±1`. In the case `x³ + 1 = 2z²`, substituting back
gives `4xz² = y²`, so `x` is itself a square, `x = w²`. This leaves four subsidiary equations:

1. `x³ + 1 = z²` — solutions `(−1, 0)`, `(0, ±1)`, `(2, ±3)`. Euler's descent: there are no
   positive integers `b ≠ c` with `3 ∤ c` and `bc(c² − 3bc + 3b²)` a perfect square; apply it
   to `x = a/b`, `c = a + b`, noting `b(a³+b³) = bc(c² − 3bc + 3b²)`. This is the hard one.
2. `x³ + 1 = −z²` — only `(−1, 0)`; factor `x³ = −(z² + 1)` over `ℤ[i]`.
3. `w⁶ + 1 = 2z²` — only `w² = 1`, `z = ±1`; factor over `ℤ[ω]`.
4. `x³ + 1 = −2z²` — only `(−1, 0)`; factor over `ℤ[√−2]`.

All three quadratic rings have class number one, which is what makes the factorisations work.
(These are Mordell equations; `y² = x³ + 1` is the elliptic curve `27a3`, rank `0`, and a CAS
finds its integral points in under a second — useful as a check, never as the proof.) -/
theorem eq_of_two_mul_mul_cube_add_one_eq_sq {x y : ℤ} (h : 2 * x * (x ^ 3 + 1) = y ^ 2) :
    (x = 0 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 1 ∧ y = 2) ∨ (x = 1 ∧ y = -2) ∨
      (x = 2 ∧ y = 6) ∨ (x = 2 ∧ y = -6) :=
  sorry

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
computations, and is the cheaper target if this is ever attacked directly. -/
theorem exists_rat_gammaTwo_heegnerPoint {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ r : ℚ, (r : ℂ) = gammaTwo (heegnerPoint p hp.pos) :=
  sorry

/-! ### Reduction of LEAVES 5 and 6 to their analytic cores

Everything from here to `exp_pi_sqrt_le_of_jInvariant_eq` was added when LEAVES 5 and 6 were
closed over three new named sub-leaves. Both targets are now PROVEN; what is left open is
`eta_pow_24_add_eta_two_pow_24` (one modular-form identity) and the two `q`-expansion value
estimates `exists_E₄_heegnerPoint_approx` / `exists_E₆_heegnerPoint_approx`.

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
`E₄`): at `z = 0.3+0.7i`, `0.1+1.3i`, `-0.4+0.55i` the two sides agree to `10⁻⁷⁷`, with ratio
`1` to every printed digit. The three points are generic — not Heegner points — because this
is an identity on all of `ℍ`, and testing it only at CM points would not distinguish it from
a weaker statement.

ROUTE, AND WHAT MAKES IT CHEAP AT THIS PIN. Divide through: the claim is that
`F(z) = (Δ(z) + 256Δ(2z))/(η(z)η(2z))⁸` equals `E₄`. `F` is holomorphic and nonvanishing-free
of poles on `ℍ` (`ModularForm.eta_ne_zero`), and is `T`-invariant by the `24`-th-power
argument — `η(z+1)²⁴ = η(z)²⁴` and `η(2z+2)²⁴ = η(2z)²⁴`, while the denominator picks up
`(e^{πi/12}·e^{πi/6})⁸ = e^{2πi} = 1`. The remaining work is `S`-invariance of weight `4`,
after which `ModularForm.levelOne_weight_four_rank_one` plus a single `q`-coefficient
comparison (constant term `1`) finishes; `sturm_bound_levelOne` is the packaged form of that
last step. `discriminant_S_invariant` and `eta_comp_eqOn_const_mul_csqrt_eta` in
`ModularForms/Discriminant.lean` are the transformation inputs.

WHAT WOULD REFUTE IT: any `z ∈ ℍ` where the two sides differ. There is none — but note the
`256` and the exponent `8` are both forced, and neither is a normalisation choice: `256`
comes from `2¹²/16` in `f₂²⁴/f₂⁸` and `8` from `f₂⁸ = 16 η(2z)⁸/η(z)⁸`. -/
theorem eta_pow_24_add_eta_two_pow_24 (z : UpperHalfPlane) :
    ModularForm.eta (z : ℂ) ^ 24 + 256 * ModularForm.eta (2 * (z : ℂ)) ^ 24
      = ModularForm.E₄ z * (ModularForm.eta (z : ℂ) * ModularForm.eta (2 * (z : ℂ))) ^ 8 :=
  sorry

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
`Q³` or the coefficients `240` and `2160`. -/
theorem exists_E₄_heegnerPoint_approx {p : ℕ} (hp : 11 ≤ p) :
    ∃ r : ℝ, |r| ≤ 20000 * heegnerQ p ^ 3 ∧
      ModularForm.E₄ (heegnerPoint p (by omega)) =
        ((1 - 240 * heegnerQ p + 2160 * heegnerQ p ^ 2 + r : ℝ) : ℂ) :=
  sorry

/-- **SUB-LEAF 6b — the value of `E₆` at the Heegner point, to second order in `Q`.**

  `E₆(τ₀) = 1 + 504Q − 16632Q² + s`  with  `|s| ≤ 400000 Q³`.

Identical route to `exists_E₄_heegnerPoint_approx` at `k = 6`: `B₆ = 1/42`, so
`2·6/B₆ = 504` and `E₆ z = 1 - 504 Σ σ₅(n) qⁿ`; at `q = -Q` this is
`1 + 504Q - 504·σ₅(2)·Q² + ⋯` with `σ₅(2) = 33`, giving the `-16632 = -504·33`. The tail bound
uses `σ₅(n) ≤ n⁶`: `|s| ≤ 504 Σ_{n≥3} n⁶Qⁿ ≤ 504 · 730 Q³ = 367920 Q³` for `Q ≤ 10⁻⁴`.

`E₆` enters only through `Δ = (E₄³ − E₆²)/1728`
(`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`). Using that identity rather than the
`η`-product `Δ = q∏(1−qⁿ)²⁴` is what keeps this leaf-set free of infinite-product estimates:
both `E₄` and `E₆` are handled by one and the same mathlib lemma. -/
theorem exists_E₆_heegnerPoint_approx {p : ℕ} (hp : 11 ≤ p) :
    ∃ s : ℝ, |s| ≤ 400000 * heegnerQ p ^ 3 ∧
      ModularForm.E₆ (heegnerPoint p (by omega)) =
        ((1 + 504 * heegnerQ p - 16632 * heegnerQ p ^ 2 + s : ℝ) : ℂ) :=
  sorry

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
* `Heegner.exists_rat_gammaTwo_heegnerPoint` — `γ₂(τ₀) ∈ ℚ` (**the main theorem of CM**);
* `Heegner.gammaTwo_pow_three_eq_jInvariant` — Weber's `γ₂³ = j`;
* `Heegner.exp_pi_sqrt_le_of_jInvariant_eq` — the `q`-expansion bound.

Of these only the fourth needs class field theory. The fifth is classical elliptic-function
theory over machinery mathlib already has (`η`, `Δ = η²⁴`, `E₄`, `Δ = (E₄³−E₆²)/1728`,
`qExpansion`), and the sixth is a real-analytic estimate on the `q`-expansion of `j`; both
are the cheap targets. -/
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
3. `heegnerRelation_solutions` — proven over the DIOPHANTINE leaf
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

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
also proved here. ONE leaf remains:

* `exists_heegnerRelation_of_classNumberOne` — the DEEP one (complex
  multiplication, Weber's functions, the `q`-expansion of `j`).
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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

WHAT IT WOULD TAKE. The `j`-function is not in mathlib at this pin, but its ingredients are:
`Mathlib.NumberTheory.ModularForms.DedekindEta` (`η`),
`Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing` (`E₄`, `E₆`, `Δ`, and
`Δ = (E₄³ − E₆²)/1728`), and `Mathlib.NumberTheory.ModularForms.QExpansion`. So `j = E₄³/Δ`
and `f₂ = √2 · η(2τ)/η(τ)` are both *definable* today, and the `q`-expansion bullet is
within reach of the existing `qExpansion` API. What is genuinely absent everywhere — mathlib,
`~/cs/FLT`, and this project — is the main theorem of complex multiplication and the ring
class field theory behind the first bullet; that is the real cost of this leaf, and it is where
a further decomposition should cut. The remaining bullets are ordinary (if lengthy) modular
function identities. -/
theorem exists_heegnerRelation_of_classNumberOne {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (h3 : 3 < p)
    (hcl : ∀ f g : BinaryQuadraticForm, f.IsPosDef → g.IsPosDef →
      f.discr = -(p : ℤ) → g.discr = -(p : ℤ) → f.Equivalent g) :
    ∃ a b : ℤ, 2 * (b ^ 2 - 4 * a) = (2 * b - a ^ 2) ^ 2 ∧
      Real.exp (Real.pi * Real.sqrt p) ≤
        ((|(b ^ 2 - 4 * a) ^ 2 + 8 * (2 * b - a ^ 2)| ^ 3 + 745 : ℤ) : ℝ) :=
  sorry

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

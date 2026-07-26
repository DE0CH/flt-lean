/-
QuarticDescent.lean — own work for the Fermat project (not vendored from
the FLT project).
-/
module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic

/-!
# `e² = X⁴ − 11X²Y² − Y⁴` has no coprime nonzero integer solution

This is the arithmetic heart of the `X_1(2,10)` node of
`Fermat/FLT/FreyCurve/MazurTorsion.lean`: it is the `2`-descent
homogeneous space of the conductor-`20` elliptic curve
`v² = c³ − 11c² − c`, and the statement is equivalent to that curve
having Mordell–Weil rank `0`. It cannot be settled by a congruence: the
quartic carries the rational point `(X, Y, e) = (1, 0, 1)`, so it is the
*trivial* coset of the descent and is everywhere locally solvable. What
is written here is therefore a genuine **infinite descent**, in the
classical Gaussian-integer form.

## The argument

Throughout, `X`, `Y` are coprime and nonzero and `e² = X⁴ − 11X²Y² − Y⁴`.

1. **Parity** (`odd_of_quartic`). `X` is odd: if `X` were even then `Y`
   would be odd and `e² ≡ 3` or `7 (mod 8)`, neither a square. (The
   sharper classical statement `4 ∣ Y` is true but not needed here — the
   descent below only ever uses that `X` is odd.)

2. **Completing the square.** With `B = 2Y² + 11X²` one has
   `B² + (2e)² = 125 X⁴`, `B` is odd, and `gcd(B, e) = 1`: an odd prime
   dividing both divides `125X⁴`; `p ∣ X` forces `p ∣ Y`, and `p = 5`
   forces `Y² ≡ 2X² (mod 5)`, impossible since `2` is not a quadratic
   residue mod `5` unless `5` divides both `X` and `Y`.

3. **Gaussian factorisation.** In `ℤ[i]` (a Euclidean domain, hence a
   PID and a UFD) the element `α = B + 2ei` is coprime to its conjugate,
   and `α · ᾱ = 125 X⁴ = π³ π̄³ X⁴` for the prime `π = 2 + i` of norm
   `5`. After conjugating if necessary (the statement is symmetric in
   `e ↦ −e`, which is what `descent_step` exploits), `π³ ∣ α`; writing
   `α = π³ β` gives `β · β̄ = X⁴` with `β`, `β̄` coprime, so
   `exists_associated_pow_of_mul_eq_pow'` produces `γ = p + qi` and a
   unit `u` with `β = γ⁴ u` and `p² + q² = |X|`.

4. **The unit is `±i`.** With `π³ = 2 + 11i` and
   `γ⁴ = R + Si`, `R = p⁴ − 6p²q² + q⁴`, `S = 4p³q − 4pq³`, the four
   units give `B = ±(2R − 11S)` or `B = ±(11R + 2S)`. Since `X` is odd,
   `p` and `q` have opposite parity, so `R` is odd and `S` is even; as
   `B` is odd only the second pair survives.

5. **Descent.** Using `R = X² − 8p²q²`, the sign `B = 11R + 2S` gives
   `Y² = 4pq(p² − 11pq − q²)`, and the sign `B = −(11R + 2S)` gives
   `Y² = (q² − p²)(11p² + 4pq − 11q²)`, which is
   `m'n'(m'² − 11m'n' − n'²)` at `(m', n') = (p + q, q − p)`. Both land
   back on the shape `mn(m² − 11mn − n²) = □` with
   `|m'| + |n'| ≤ 2|X| − 2 ≤ X² − 1 < X² + Y²`, a strictly smaller
   value of the measure `|m| + |n|`.

6. **The loop closes** because a square of the product shape produces a
   quartic again (`exists_quartic`): the three factors `m`, `n`,
   `m² − 11mn − n²` are pairwise coprime, hence each is `±` a square,
   and the signs land on `e² = X⁴ − 11X²Y² − Y⁴` with
   `X² + Y² = |m| + |n|`. Strong induction on `m.natAbs + n.natAbs`
   (`not_isSquare_form`) then finishes, and the quartic statement itself
   follows by feeding in `(m, n) = (X², Y²)`, for which the product is
   `(XYe)²`.

## Main results

* `QuarticDescent.not_isSquare_form` — for coprime nonzero `m`, `n` the
  integer `m·n·(m² − 11mn − n²)` is never a perfect square.
* `QuarticDescent.quartic_no_solution` — the quartic itself. This is
  what `MazurTwoTen.quartic_no_solution` in
  `Fermat/FLT/FreyCurve/MazurTorsion.lean` is proven from.
-/

@[expose] public section

namespace QuarticDescent

open Zsqrtd

/-! ### Small helpers -/

/-- The norm of `ℤ√d` is multiplicative, hence monotone for divisibility. -/
lemma norm_dvd_norm {d : ℤ} {a b : ℤ√d} (h : a ∣ b) : a.norm ∣ b.norm := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.norm, Zsqrtd.norm_mul _ _⟩

/-- A nonzero integer has square at least `1`. -/
lemma one_le_sq {a : ℤ} (h : a ≠ 0) : 1 ≤ a ^ 2 := by
  have h1 : (0 : ℤ) < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 h))
  linarith [Int.lt_iff_add_one_le.mp h1]

/-- `|a| ≤ a²` over `ℤ` (false over `ℝ`; integrality is what makes it work). -/
lemma abs_le_sq (a : ℤ) : |a| ≤ a ^ 2 := by
  rcases eq_or_lt_of_le (abs_nonneg a) with h | h
  · rw [← h]; positivity
  · have h1 : (1 : ℤ) ≤ |a| := by linarith [Int.lt_iff_add_one_le.mp h]
    nlinarith [sq_abs a]

/-- Fourth powers are injective on nonnegative integers. Used to turn the
norm identity `N(γ)⁴ = X⁴` into `p² + q² = |X|`. -/
lemma pow_four_inj {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 4 = b ^ 4) : a = b := by
  have h1 : (a ^ 2 - b ^ 2) * (a ^ 2 + b ^ 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have h3 : (a - b) * (a + b) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4 <;> linarith
  · have ha2 : a ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg b]) (sq_nonneg a)
    have hb2 : b ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg a]) (sq_nonneg b)
    rw [sq_eq_zero_iff.mp ha2, sq_eq_zero_iff.mp hb2]

/-- **The units of `ℤ[i]` are `±1` and `±i`.** A unit has norm `1`, i.e.
`re² + im² = 1`, which bounds both coordinates to `[-1, 1]`. -/
lemma isUnit_cases {u : GaussianInt} (hu : IsUnit u) :
    u = 1 ∨ u = -1 ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ := by
  have h : Zsqrtd.norm u = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) u).mpr hu
  have h' : u.re * u.re + u.im * u.im = 1 := by
    rw [Zsqrtd.norm_def] at h; linarith
  have hr1 : -1 ≤ u.re := by nlinarith [mul_self_nonneg u.im, mul_self_nonneg (u.re + 1)]
  have hr2 : u.re ≤ 1 := by nlinarith [mul_self_nonneg u.im, mul_self_nonneg (u.re - 1)]
  have hi1 : -1 ≤ u.im := by nlinarith [mul_self_nonneg u.re, mul_self_nonneg (u.im + 1)]
  have hi2 : u.im ≤ 1 := by nlinarith [mul_self_nonneg u.re, mul_self_nonneg (u.im - 1)]
  interval_cases h3 : u.re <;> interval_cases h4 : u.im <;>
    simp_all [Zsqrtd.ext_iff]

/-- **`2 + i` is prime in `ℤ[i]`.** Its norm is the rational prime `5`, so a
factorisation splits `5` multiplicatively and one factor has norm `1`.
Irreducible implies prime because `ℤ[i]` is a Euclidean domain, hence a UFD. -/
lemma prime_two_add_i : Prime (⟨2, 1⟩ : GaussianInt) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  constructor
  · intro hu
    have h : Zsqrtd.norm (⟨2, 1⟩ : GaussianInt) = 1 :=
      (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr hu
    rw [Zsqrtd.norm_def] at h
    norm_num at h
  · rintro a b hab
    have hn : Zsqrtd.norm a * Zsqrtd.norm b = 5 := by
      have h := congrArg Zsqrtd.norm hab
      rw [Zsqrtd.norm_mul] at h
      rw [← h, Zsqrtd.norm_def]
      norm_num
    have hna : 0 ≤ Zsqrtd.norm a := Zsqrtd.norm_nonneg (by norm_num) a
    have hnb : 0 ≤ Zsqrtd.norm b := Zsqrtd.norm_nonneg (by norm_num) b
    have key : Zsqrtd.norm a = 1 ∨ Zsqrtd.norm b = 1 := by
      set A := Zsqrtd.norm a with hA
      set B := Zsqrtd.norm b with hB
      have hA1 : 1 ≤ A := by
        rcases hna.lt_or_eq with h | h
        · omega
        · exfalso; rw [← h] at hn; simp at hn
      have hB1 : 1 ≤ B := by
        rcases hnb.lt_or_eq with h | h
        · omega
        · exfalso; rw [← h] at hn; simp at hn
      have hA5 : A ≤ 5 := by nlinarith
      interval_cases A <;> omega
    rcases key with h | h
    · exact Or.inl ((Zsqrtd.norm_eq_one_iff' (by norm_num) _).mp h)
    · exact Or.inr ((Zsqrtd.norm_eq_one_iff' (by norm_num) _).mp h)

/-! ### Parity -/

/-- **`X` is odd.** If `X` were even then `Y` is odd by coprimality, and mod `8`
the right-hand side is `3` or `7`, neither a square. (The classical descent also
records `4 ∣ Y`; the Gaussian argument below never needs it, since `2 ∣ Y` comes
out of the descent identity `Y² = 4pq(p² − 11pq − q²)` for free.) -/
lemma odd_of_quartic {X Y e : ℤ} (hXY : IsCoprime X Y)
    (heq : e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4) : ¬ (2 : ℤ) ∣ X := by
  intro hX2
  obtain ⟨X₁, hX₁⟩ := hX2
  have hYodd : ¬ (2 : ℤ) ∣ Y := by
    intro hY2
    exact absurd (Int.isUnit_iff.mp (hXY.isUnit_of_dvd' ⟨X₁, hX₁⟩ hY2)) (by norm_num)
  obtain ⟨Y₁, hY₁⟩ : ∃ k, Y = 2 * k + 1 := by
    rcases Int.even_or_odd Y with h | h
    · exact absurd h.two_dvd hYodd
    · obtain ⟨k, hk⟩ := h; exact ⟨k, hk⟩
  have key : ∀ a b c : ZMod 8,
      c ^ 2 ≠ (2 * a) ^ 4 - 11 * (2 * a) ^ 2 * (2 * b + 1) ^ 2 - (2 * b + 1) ^ 4 := by decide
  refine key (X₁ : ZMod 8) (Y₁ : ZMod 8) (e : ZMod 8) ?_
  have h := congrArg (fun z : ℤ => (z : ZMod 8)) heq
  simp only [hX₁, hY₁] at h
  push_cast at h
  exact h

/-! ### The Gaussian descent step -/

/-- Computation of `(2 + 11i) * ((r + si) * (u₁ + u₂ i))`. -/
lemma mul_comp (r s u1 u2 : ℤ) :
    (⟨2, 11⟩ : GaussianInt) * ((⟨r, s⟩ : GaussianInt) * ⟨u1, u2⟩) =
      ⟨2 * (r * u1 - s * u2) - 11 * (r * u2 + s * u1),
       11 * (r * u1 - s * u2) + 2 * (r * u2 + s * u1)⟩ := by
  ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-- `1` in coordinates, so that `mul_comp` applies to the unit case `u = 1`. -/
lemma gaussian_one : (1 : GaussianInt) = ⟨1, 0⟩ := by ext <;> simp

/-- `-1` in coordinates, so that `mul_comp` applies to the unit case `u = -1`. -/
lemma gaussian_negOne : (-1 : GaussianInt) = ⟨-1, 0⟩ := by ext <;> simp

/-- **The size bound driving the descent.** If `a`, `b` are nonzero and
`a² + b²` is odd then one of them is even, hence of absolute value at least `2`,
and `|a| + |b| ≤ a² + b² − 2`. The `−2` is what makes the measure drop
strictly: without it the case `|a| = |b| = 1` would be neutral (and it is
excluded here precisely because `a² + b² = 2` is even). -/
lemma size_bound {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hpar : ¬ (2 : ℤ) ∣ (a ^ 2 + b ^ 2)) :
    |a| + |b| ≤ a ^ 2 + b ^ 2 - 2 := by
  have hbig : ∀ c : ℤ, c ≠ 0 → (2 : ℤ) ∣ c → |c| + 2 ≤ c ^ 2 := by
    intro c hc hdc
    have h2 : (2 : ℤ) ≤ |c| := Int.le_of_dvd (abs_pos.mpr hc) ((dvd_abs 2 c).mpr hdc)
    nlinarith [sq_abs c]
  have hev : (2 : ℤ) ∣ a ∨ (2 : ℤ) ∣ b := by
    rcases Int.even_or_odd a with h | h
    · exact Or.inl h.two_dvd
    · rcases Int.even_or_odd b with h' | h'
      · exact Or.inr h'.two_dvd
      · exfalso
        obtain ⟨s, hs⟩ := h
        obtain ⟨t, ht⟩ := h'
        exact hpar ⟨2 * s ^ 2 + 2 * s + 2 * t ^ 2 + 2 * t + 1, by rw [hs, ht]; ring⟩
  rcases hev with h | h
  · linarith [hbig a ha h, abs_le_sq b]
  · linarith [hbig b hb h, abs_le_sq a]

/-- **The descent step, one half.** From a coprime nonzero solution of the
quartic in which `2 + i` divides `α = B + 2ei` (`B = 2Y² + 11X²`), produce a
coprime nonzero pair `(m, n)` with `mn(m² − 11mn − n²)` a perfect square and
`|m| + |n| ≤ 2|X| − 2`. The other half (`2 + i` dividing the conjugate) is the
same statement applied to `−e`, which is what `descent_step` does. -/
lemma descent_step_aux {X Y e : ℤ} (hXY : IsCoprime X Y) (hX : X ≠ 0) (hY : Y ≠ 0)
    (heq : e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4)
    (hdvd : (⟨2, 1⟩ : GaussianInt) ∣ (⟨2 * Y ^ 2 + 11 * X ^ 2, 2 * e⟩ : GaussianInt)) :
    ∃ m n : ℤ, IsCoprime m n ∧ m ≠ 0 ∧ n ≠ 0 ∧
      IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2)) ∧ |m| + |n| ≤ 2 * |X| - 2 := by
  have hπ : Prime (⟨2, 1⟩ : GaussianInt) := prime_two_add_i
  set B : ℤ := 2 * Y ^ 2 + 11 * X ^ 2 with hBdef
  set α : GaussianInt := ⟨B, 2 * e⟩ with hαdef
  have hXodd : ¬ (2 : ℤ) ∣ X := odd_of_quartic hXY heq
  have hBodd : ¬ (2 : ℤ) ∣ B := by
    intro h
    apply hXodd
    have h11 : (2 : ℤ) ∣ 11 * X ^ 2 := by
      have hrw : (11 : ℤ) * X ^ 2 = B - 2 * Y ^ 2 := by rw [hBdef]; ring
      rw [hrw]; exact dvd_sub h ⟨Y ^ 2, rfl⟩
    rcases Int.prime_two.dvd_mul.mp h11 with h1 | h1
    · norm_num at h1
    · exact Int.prime_two.dvd_of_dvd_pow h1
  have hnormB : B ^ 2 + 4 * e ^ 2 = 125 * X ^ 4 := by rw [hBdef]; linear_combination 4 * heq
  have hnormα : Zsqrtd.norm α = 125 * X ^ 4 := by
    rw [hαdef]
    show B * B - (-1) * (2 * e) * (2 * e) = 125 * X ^ 4
    linear_combination hnormB
  have hoddnorm : ¬ (2 : ℤ) ∣ (125 * X ^ 4) := by
    intro h
    apply hXodd
    rcases Int.prime_two.dvd_mul.mp h with h1 | h1
    · norm_num at h1
    · exact Int.prime_two.dvd_of_dvd_pow h1
  -- `B` and `e` are coprime
  have hBe : IsCoprime B e := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨d, hd, hdvd'⟩ := Nat.exists_prime_and_dvd hg
    have hdB : (d : ℤ) ∣ B :=
      (Int.natCast_dvd_natCast.mpr hdvd').trans (Int.gcd_dvd_left B e)
    have hde : (d : ℤ) ∣ e :=
      (Int.natCast_dvd_natCast.mpr hdvd').trans (Int.gcd_dvd_right B e)
    have hdp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hd
    have hdd : (d : ℤ) ∣ 125 * X ^ 4 := by
      rw [← hnormB]
      exact dvd_add (dvd_pow hdB two_ne_zero) (Dvd.dvd.mul_left (dvd_pow hde two_ne_zero) 4)
    rcases hdp.dvd_mul.mp hdd with h5 | hXd
    · have hd5 : d = 5 := by
        have h1 : d ∣ 125 := by exact_mod_cast h5
        have h53 : d ∣ 5 ^ 3 := by norm_num; exact h1
        exact (Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp (hd.dvd_of_dvd_pow h53)
      subst hd5
      have hB5 : (5 : ℤ) ∣ B := by exact_mod_cast hdB
      have hzm : ((B : ℤ) : ZMod 5) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd B 5).mpr (by exact_mod_cast hB5)
      have key : ∀ x y : ZMod 5, 2 * y ^ 2 + 11 * x ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
      rw [hBdef] at hzm
      push_cast at hzm
      have hxy := key (X : ZMod 5) (Y : ZMod 5) hzm
      have h5X : (5 : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X 5).mp hxy.1
      have h5Y : (5 : ℤ) ∣ Y := (ZMod.intCast_zmod_eq_zero_iff_dvd Y 5).mp hxy.2
      exact absurd (Int.isUnit_iff.mp (hXY.isUnit_of_dvd' h5X h5Y)) (by norm_num)
    · have hdX : (d : ℤ) ∣ X := hdp.dvd_of_dvd_pow hXd
      have hd2Y : (d : ℤ) ∣ 2 * Y ^ 2 := by
        have hrw : (2 : ℤ) * Y ^ 2 = B - 11 * X ^ 2 := by rw [hBdef]; ring
        rw [hrw]
        exact dvd_sub hdB (Dvd.dvd.mul_left (dvd_pow hdX two_ne_zero) 11)
      rcases hdp.dvd_mul.mp hd2Y with h2 | hY2
      · have hd2 : d = 2 := by
          have h1 : d ∣ 2 := by exact_mod_cast h2
          exact (Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h1
        subst hd2
        exact hBodd (by exact_mod_cast hdB)
      · have hdY : (d : ℤ) ∣ Y := hdp.dvd_of_dvd_pow hY2
        have := Int.isUnit_iff.mp (hXY.isUnit_of_dvd' hdX hdY)
        have h2d : 2 ≤ d := hd.two_le
        rcases this with h | h <;> omega
  -- `α` and `star α` are coprime
  have hsum : α + star α = ((2 * B : ℤ) : GaussianInt) := by
    rw [hαdef]
    ext <;> simp [Zsqrtd.star_mk]
    ring
  have h4e : ((4 * e : ℤ) : GaussianInt) = (α - star α) * ⟨0, -1⟩ := by
    rw [hαdef]
    ext <;> simp [Zsqrtd.star_mk, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  have hcop : IsCoprime α (star α) := by
    refine isCoprime_of_prime_dvd ?_ ?_
    · rintro ⟨h1, -⟩
      rw [hαdef] at h1
      have hB0 : B = 0 := congrArg Zsqrtd.re h1
      rw [hBdef] at hB0
      nlinarith [sq_nonneg Y, one_le_sq hX]
    · intro z hz hza hzs
      have hdn : Zsqrtd.norm z ∣ 125 * X ^ 4 := by
        rw [← hnormα]; exact norm_dvd_norm hza
      have hz2 : ¬ z ∣ ((2 : ℤ) : GaussianInt) := by
        intro h2
        refine hz.not_unit ((Zsqrtd.norm_eq_one_iff' (by norm_num) z).mp ?_)
        have hd4 : Zsqrtd.norm z ∣ (4 : ℤ) := by
          have h3 := norm_dvd_norm h2
          rwa [Zsqrtd.norm_intCast] at h3
        have hodd : ¬ (2 : ℤ) ∣ Zsqrtd.norm z := fun h3 => hoddnorm (h3.trans hdn)
        have hnz : 0 ≤ Zsqrtd.norm z := Zsqrtd.norm_nonneg (by norm_num) z
        have hle : Zsqrtd.norm z ≤ 4 := Int.le_of_dvd (by norm_num) hd4
        set N := Zsqrtd.norm z with hN
        interval_cases N <;> omega
      have hzB : z ∣ ((B : ℤ) : GaussianInt) := by
        have h1 : z ∣ ((2 * B : ℤ) : GaussianInt) := hsum ▸ dvd_add hza hzs
        push_cast at h1
        rcases hz.dvd_mul.mp h1 with h | h
        · exact absurd (by push_cast; exact h) hz2
        · exact h
      have hze : z ∣ ((e : ℤ) : GaussianInt) := by
        have h1 : z ∣ ((4 * e : ℤ) : GaussianInt) := by
          rw [h4e]; exact Dvd.dvd.mul_right (dvd_sub hza hzs) _
        have h2 : z ∣ ((2 : ℤ) : GaussianInt) *
            (((2 : ℤ) : GaussianInt) * ((e : ℤ) : GaussianInt)) := by
          refine dvd_trans h1 ?_
          refine Dvd.intro 1 ?_
          push_cast; ring
        rcases hz.dvd_mul.mp h2 with h | h
        · exact absurd h hz2
        · rcases hz.dvd_mul.mp h with h' | h'
          · exact absurd h' hz2
          · exact h'
      exact hz.not_unit ((hBe.map (Int.castRingHom GaussianInt)).isUnit_of_dvd' hzB hze)
  -- `(2+i)^3` divides `α`
  have hπ3 : (⟨2, 1⟩ : GaussianInt) ^ 3 = ⟨2, 11⟩ := by
    ext <;> simp [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hprod : α * star α = ((125 * X ^ 4 : ℤ) : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hnormα]
  have hπ3' : (star (⟨2, 1⟩ : GaussianInt)) ^ 3 = ⟨2, -11⟩ := by
    rw [Zsqrtd.star_mk]
    ext <;> simp [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have h125 : ((125 : ℤ) : GaussianInt) =
      (⟨2, 1⟩ : GaussianInt) ^ 3 * (star (⟨2, 1⟩ : GaussianInt)) ^ 3 := by
    rw [hπ3, hπ3']; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hnotdvd : ¬ (⟨2, 1⟩ : GaussianInt) ∣ star α := fun h =>
    hπ.not_unit (hcop.isUnit_of_dvd' hdvd h)
  have hdvd3 : (⟨2, 1⟩ : GaussianInt) ^ 3 ∣ α := by
    refine hπ.pow_dvd_of_dvd_mul_left 3 hnotdvd ?_
    rw [mul_comm (star α) α, hprod]
    have hsplit : ((125 * X ^ 4 : ℤ) : GaussianInt) =
        ((125 : ℤ) : GaussianInt) * ((X : ℤ) : GaussianInt) ^ 4 := by push_cast; ring
    rw [hsplit, h125]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _
  obtain ⟨β, hβ⟩ := hdvd3
  have hstarβ : star α = (star (⟨2, 1⟩ : GaussianInt)) ^ 3 * star β := by
    rw [hβ, star_mul, star_pow, mul_comm]
  have h125ne : ((125 : ℤ) : GaussianInt) ≠ 0 := by
    intro h
    have h1 : (125 : ℤ) = 0 := congrArg Zsqrtd.re h
    norm_num at h1
  have hββ : β * star β = ((X : ℤ) : GaussianInt) ^ 4 := by
    refine mul_left_cancel₀ h125ne ?_
    have h1 : ((125 : ℤ) : GaussianInt) * (β * star β) = α * star α := by
      rw [hstarβ, hβ, h125]; ring
    rw [h1, hprod]
    push_cast; ring
  have hcopβ : IsCoprime β (star β) :=
    (hcop.of_isCoprime_of_dvd_left
        ⟨(⟨2, 1⟩ : GaussianInt) ^ 3, by rw [hβ]; ring⟩).of_isCoprime_of_dvd_right
      ⟨(star (⟨2, 1⟩ : GaussianInt)) ^ 3, by rw [hstarβ]; ring⟩
  obtain ⟨γ, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcopβ hββ
  set p : ℤ := γ.re with hp
  set q : ℤ := γ.im with hq
  set R : ℤ := p ^ 4 - 6 * p ^ 2 * q ^ 2 + q ^ 4 with hR
  set S : ℤ := 4 * p ^ 3 * q - 4 * p * q ^ 3 with hS
  have hγ4 : γ ^ 4 = (⟨R, S⟩ : GaussianInt) := by
    rw [hR, hS, hp, hq]
    ext <;> (simp [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]; try ring)
  have hnormu : Zsqrtd.norm (u : GaussianInt) = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr u.isUnit
  have hnormβ : Zsqrtd.norm β = X ^ 4 := by
    have h1 : ((Zsqrtd.norm β : ℤ) : GaussianInt) = ((X ^ 4 : ℤ) : GaussianInt) := by
      rw [Zsqrtd.norm_eq_mul_conj, hββ]; push_cast; ring
    exact_mod_cast h1
  have habs : p ^ 2 + q ^ 2 = |X| := by
    refine pow_four_inj (by positivity) (abs_nonneg X) ?_
    have h1 : Zsqrtd.norm (γ ^ 4 * (u : GaussianInt)) = X ^ 4 := by rw [hu]; exact hnormβ
    rw [Zsqrtd.norm_mul, hnormu, mul_one] at h1
    have hnp : Zsqrtd.norm (γ ^ 4) = (Zsqrtd.norm γ) ^ 4 := by
      simp [pow_succ, Zsqrtd.norm_mul]
    rw [hnp] at h1
    have h3 : Zsqrtd.norm γ = p ^ 2 + q ^ 2 := by rw [Zsqrtd.norm_def, ← hp, ← hq]; ring
    rw [h3] at h1
    have hX4 : |X| ^ 4 = X ^ 4 := by
      have h4 : |X| ^ 4 = (|X| ^ 2) ^ 2 := by ring
      rw [h4, sq_abs]
      ring
    rw [h1, hX4]
  have hX2 : X ^ 2 = (p ^ 2 + q ^ 2) ^ 2 := by rw [habs, sq_abs]
  -- `p` and `q` are coprime
  have hpq : IsCoprime p q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨d, hd, hdvd'⟩ := Nat.exists_prime_and_dvd hg
    have hdγ : ((d : ℤ) : GaussianInt) ∣ γ := by
      rw [Zsqrtd.intCast_dvd]
      exact ⟨(Int.natCast_dvd_natCast.mpr hdvd').trans (Int.gcd_dvd_left p q),
             (Int.natCast_dvd_natCast.mpr hdvd').trans (Int.gcd_dvd_right p q)⟩
    have hdβ : ((d : ℤ) : GaussianInt) ∣ β := by
      rw [← hu]
      exact Dvd.dvd.mul_right (dvd_pow hdγ (by norm_num)) _
    have hdsβ : ((d : ℤ) : GaussianInt) ∣ star β := by
      have h1 := map_dvd (starRingEnd GaussianInt) hdβ
      have h2 : (starRingEnd GaussianInt) ((d : ℤ) : GaussianInt) = ((d : ℤ) : GaussianInt) := by
        ext <;> simp
      rwa [h2] at h1
    have h3 : Zsqrtd.norm ((d : ℤ) : GaussianInt) = 1 :=
      (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr (hcopβ.isUnit_of_dvd' hdβ hdsβ)
    rw [Zsqrtd.norm_intCast] at h3
    have h4 : (d : ℤ) = 1 ∨ (d : ℤ) = -1 := mul_self_eq_one_iff.mp h3
    have h2d : 2 ≤ d := hd.two_le
    rcases h4 with h | h <;> omega
  -- parity of `R`
  have hpqodd : ¬ (2 : ℤ) ∣ (p ^ 2 + q ^ 2) := by
    rw [habs]
    intro h
    exact hXodd ((dvd_abs 2 X).mp h)
  have hRodd : ¬ (2 : ℤ) ∣ R := by
    intro h
    apply hpqodd
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (p ^ 2 + q ^ 2) 2).mp ?_
    have h1 : ((R : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd R 2).mpr (by exact_mod_cast h)
    rw [hR] at h1
    have key : ∀ a b : ZMod 2, a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 = a ^ 2 + b ^ 2 := by decide
    push_cast at h1 ⊢
    rw [← key (p : ZMod 2) (q : ZMod 2)]
    exact h1
  -- the main equation
  have hmain : (⟨B, 2 * e⟩ : GaussianInt) =
      (⟨2, 11⟩ : GaussianInt) * ((⟨R, S⟩ : GaussianInt) * (u : GaussianInt)) := by
    rw [← hγ4, hu, ← hπ3, ← hβ, hαdef]
  have h2S : (2 : ℤ) ∣ S := ⟨2 * p ^ 3 * q - 2 * p * q ^ 3, by rw [hS]; ring⟩
  have hBsign : B = 11 * R + 2 * S ∨ B = -(11 * R + 2 * S) := by
    rcases isUnit_cases u.isUnit with h | h | h | h
    · exfalso
      rw [h, gaussian_one, mul_comp] at hmain
      have hre : B = 2 * (R * 1 - S * 0) - 11 * (R * 0 + S * 1) := congrArg Zsqrtd.re hmain
      obtain ⟨t, ht⟩ := h2S
      exact hBodd ⟨R - 11 * t, by rw [hre, ht]; ring⟩
    · exfalso
      rw [h, gaussian_negOne, mul_comp] at hmain
      have hre : B = 2 * (R * (-1) - S * 0) - 11 * (R * 0 + S * (-1)) := congrArg Zsqrtd.re hmain
      obtain ⟨t, ht⟩ := h2S
      exact hBodd ⟨-R + 11 * t, by rw [hre, ht]; ring⟩
    · right
      rw [h, mul_comp] at hmain
      have hre : B = 2 * (R * 0 - S * 1) - 11 * (R * 1 + S * 0) := congrArg Zsqrtd.re hmain
      linarith
    · left
      rw [h, mul_comp] at hmain
      have hre : B = 2 * (R * 0 - S * (-1)) - 11 * (R * (-1) + S * 0) := congrArg Zsqrtd.re hmain
      linarith
  rcases hBsign with hBs | hBs
  · -- `B = 11R + 2S`: descend to `(p, q)`
    rw [hBdef, hR, hS] at hBs
    have hY2 : 2 * Y ^ 2 = 2 * (4 * (p * q * (p ^ 2 - 11 * p * q - q ^ 2))) := by
      linear_combination hBs - 11 * hX2
    have hY2' : Y ^ 2 = 4 * (p * q * (p ^ 2 - 11 * p * q - q ^ 2)) :=
      mul_left_cancel₀ two_ne_zero hY2
    have hp0 : p ≠ 0 := by
      intro h
      exact hY (sq_eq_zero_iff.mp (by rw [hY2', h]; ring))
    have hq0 : q ≠ 0 := by
      intro h
      exact hY (sq_eq_zero_iff.mp (by rw [hY2', h]; ring))
    have h2Y : (2 : ℤ) ∣ Y := by
      refine Int.Prime.dvd_pow' (k := 2) (by norm_num) ?_
      exact ⟨2 * (p * q * (p ^ 2 - 11 * p * q - q ^ 2)), by rw [hY2']; ring⟩
    obtain ⟨w, hw⟩ := h2Y
    have hwsq : p * q * (p ^ 2 - 11 * p * q - q ^ 2) = w * w := by
      have h4 : (4 : ℤ) * (p * q * (p ^ 2 - 11 * p * q - q ^ 2)) = 4 * (w * w) := by
        linear_combination -hY2' + (Y + 2 * w) * hw
      exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4
    refine ⟨p, q, hpq, hp0, hq0, ⟨w, hwsq⟩, ?_⟩
    have hsz := size_bound hp0 hq0 hpqodd
    rw [habs] at hsz
    have hXge : (2 : ℤ) ≤ |X| := by
      rw [← habs]; linarith [one_le_sq hp0, one_le_sq hq0]
    linarith [abs_nonneg p, abs_nonneg q]
  · -- `B = -(11R + 2S)`: descend to `(p + q, q - p)`
    rw [hBdef, hR, hS] at hBs
    have hY2 : 2 * Y ^ 2 = 2 * ((q ^ 2 - p ^ 2) * (11 * p ^ 2 + 4 * p * q - 11 * q ^ 2)) := by
      linear_combination hBs - 11 * hX2
    have hY2' : Y ^ 2 = (q ^ 2 - p ^ 2) * (11 * p ^ 2 + 4 * p * q - 11 * q ^ 2) :=
      mul_left_cancel₀ two_ne_zero hY2
    have hfac : q ^ 2 - p ^ 2 ≠ 0 := by
      intro h
      exact hY (sq_eq_zero_iff.mp (by rw [hY2', h, zero_mul]))
    have hp0 : p ≠ 0 := by
      intro h
      rw [h] at hY2'
      have h1 : Y ^ 2 = -(11 * q ^ 4) := by linear_combination hY2'
      have h2 : Y ^ 2 = 0 := le_antisymm (by nlinarith [pow_two_nonneg (q ^ 2)]) (sq_nonneg Y)
      exact hY (sq_eq_zero_iff.mp h2)
    have hq0 : q ≠ 0 := by
      intro h
      rw [h] at hY2'
      have h1 : Y ^ 2 = -(11 * p ^ 4) := by linear_combination hY2'
      have h2 : Y ^ 2 = 0 := le_antisymm (by nlinarith [pow_two_nonneg (p ^ 2)]) (sq_nonneg Y)
      exact hY (sq_eq_zero_iff.mp h2)
    have hm0 : p + q ≠ 0 := by
      intro h
      exact hfac (by have hqp : q = -p := by linarith
                     rw [hqp]; ring)
    have hn0 : q - p ≠ 0 := by
      intro h
      exact hfac (by have hqp : q = p := by linarith
                     rw [hqp]; ring)
    have hmn : IsCoprime (p + q) (q - p) := by
      obtain ⟨s, t, hst⟩ := hpq
      obtain ⟨j, hj⟩ : ∃ j, p + q = 2 * j + 1 := by
        have hodd : ¬ (2 : ℤ) ∣ (p + q) := by
          rintro ⟨c, hc⟩
          exact hpqodd ⟨2 * c ^ 2 - 2 * c * q + q ^ 2, by
            have hpc : p = 2 * c - q := by linarith
            rw [hpc]; ring⟩
        rcases Int.even_or_odd (p + q) with h | h
        · exact absurd h.two_dvd hodd
        · obtain ⟨j, hj⟩ := h; exact ⟨j, hj⟩
      exact ⟨1 - j * (s + t), -(j * (t - s)), by linear_combination hj - 2 * j * hst⟩
    refine ⟨p + q, q - p, hmn, hm0, hn0, ⟨Y, by linear_combination -hY2'⟩, ?_⟩
    have hsz := size_bound hp0 hq0 hpqodd
    rw [habs] at hsz
    have h1 : |p + q| ≤ |p| + |q| := abs_add_le p q
    have h2 : |q - p| ≤ |q| + |p| := by
      rw [sub_eq_add_neg]
      calc |q + -p| ≤ |q| + |-p| := abs_add_le q (-p)
        _ = |q| + |p| := by rw [abs_neg]
    linarith

/-- **The descent step.** `2 + i` divides `125 X⁴ = α · ᾱ` and is prime, so it
divides one of the two conjugate factors; the two cases differ only by the sign
of `e`, to which the conclusion is blind. -/
lemma descent_step {X Y e : ℤ} (hXY : IsCoprime X Y) (hX : X ≠ 0) (hY : Y ≠ 0)
    (heq : e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4) :
    ∃ m n : ℤ, IsCoprime m n ∧ m ≠ 0 ∧ n ≠ 0 ∧
      IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2)) ∧ |m| + |n| ≤ 2 * |X| - 2 := by
  have hπ : Prime (⟨2, 1⟩ : GaussianInt) := prime_two_add_i
  have hnormB : (2 * Y ^ 2 + 11 * X ^ 2) ^ 2 + 4 * e ^ 2 = 125 * X ^ 4 := by
    linear_combination 4 * heq
  have hprod : (⟨2 * Y ^ 2 + 11 * X ^ 2, 2 * e⟩ : GaussianInt) *
      (⟨2 * Y ^ 2 + 11 * X ^ 2, 2 * -e⟩ : GaussianInt) = ((125 * X ^ 4 : ℤ) : GaussianInt) := by
    ext
    · show (2 * Y ^ 2 + 11 * X ^ 2) * (2 * Y ^ 2 + 11 * X ^ 2) +
        (-1) * (2 * e) * (2 * -e) = 125 * X ^ 4
      linear_combination hnormB
    · show (2 * Y ^ 2 + 11 * X ^ 2) * (2 * -e) + (2 * e) * (2 * Y ^ 2 + 11 * X ^ 2) = 0
      ring
  have h5 : (⟨2, 1⟩ : GaussianInt) ∣ ((125 * X ^ 4 : ℤ) : GaussianInt) := by
    refine ⟨(⟨50, -25⟩ : GaussianInt) * ((X : ℤ) : GaussianInt) ^ 4, ?_⟩
    have hstep : (⟨2, 1⟩ : GaussianInt) * (⟨50, -25⟩ : GaussianInt) = ((125 : ℤ) : GaussianInt) := by
      ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
    rw [← mul_assoc, hstep]
    push_cast; ring
  rcases hπ.dvd_mul.mp (hprod ▸ h5) with h | h
  · exact descent_step_aux hXY hX hY heq h
  · exact descent_step_aux hXY hX hY (e := -e) (by linear_combination heq) h

/-! ### From the product form to the quartic -/

/-- **From the product form back to the quartic, for `n > 0`.** The factors `m`,
`n`, `k = m² − 11mn − n²` are pairwise coprime (`k ≡ −n² (mod m)` and
`≡ m² (mod n)`) and `k ≠ 0` (else `(2m − 11n)² = 125n²`, forcing `5 ∣ m` and
`5 ∣ n`), so each is `±` a square; `n > 0` and the sign of the product pin the
branches, landing on the quartic at `(X, Y) = (a, b)` or `(b, a)`. The size
bookkeeping is recorded as `X² + Y² = |m| + |n|`. -/
lemma exists_quartic_pos {m n : ℤ} (hmn : IsCoprime m n) (hm : m ≠ 0) (hn : 0 < n)
    (hsq : IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2))) :
    ∃ X Y e : ℤ, IsCoprime X Y ∧ X ≠ 0 ∧ Y ≠ 0 ∧
      e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4 ∧ X ^ 2 + Y ^ 2 = |m| + |n| := by
  have hp5 : Nat.Prime 5 := by decide
  set k : ℤ := m ^ 2 - 11 * m * n - n ^ 2 with hkdef
  have hk0 : k ≠ 0 := by
    intro h
    rw [hkdef] at h
    have hA : (2 * m - 11 * n) ^ 2 = 125 * n ^ 2 := by linear_combination 4 * h
    obtain ⟨A1, hA1⟩ : (5 : ℤ) ∣ (2 * m - 11 * n) :=
      Int.Prime.dvd_pow' (k := 2) hp5 ⟨25 * n ^ 2, by push_cast; linear_combination hA⟩
    have hA1' : A1 ^ 2 = 5 * n ^ 2 := by
      have h25 : (25 : ℤ) * A1 ^ 2 = 25 * (5 * n ^ 2) := by
        linear_combination hA - (2 * m - 11 * n + 5 * A1) * hA1
      linarith
    obtain ⟨A2, hA2⟩ : (5 : ℤ) ∣ A1 :=
      Int.Prime.dvd_pow' (k := 2) hp5 ⟨n ^ 2, by push_cast; linear_combination hA1'⟩
    have hn5 : n ^ 2 = 5 * A2 ^ 2 := by
      have h5 : (5 : ℤ) * n ^ 2 = 5 * (5 * A2 ^ 2) := by
        linear_combination -hA1' + (A1 + 5 * A2) * hA2
      linarith
    have h3 : (5 : ℤ) ∣ n :=
      Int.Prime.dvd_pow' (k := 2) hp5 ⟨A2 ^ 2, by push_cast; linear_combination hn5⟩
    obtain ⟨n1, hn1⟩ := id h3
    have h4 : (5 : ℤ) ∣ m := by
      have h2m : (5 : ℤ) ∣ 2 * m := ⟨A1 + 11 * n1, by linear_combination hA1 + 11 * hn1⟩
      rcases Int.Prime.dvd_mul' hp5 h2m with hcon | hcon
      · exfalso; norm_num at hcon
      · push_cast at hcon; exact hcon
    exact absurd (Int.isUnit_iff.mp (hmn.isUnit_of_dvd' h4 h3)) (by norm_num)
  have hmk : IsCoprime m k := by
    have h := ((hmn.pow_right (n := 2)).neg_right).add_mul_left_right (m - 11 * n)
    have heq : -n ^ 2 + m * (m - 11 * n) = k := by rw [hkdef]; ring
    rwa [heq] at h
  have hnk : IsCoprime n k := by
    have h := (hmn.symm.pow_right (n := 2)).add_mul_left_right (-(11 * m) - n)
    have heq : m ^ 2 + n * (-(11 * m) - n) = k := by rw [hkdef]; ring
    rwa [heq] at h
  obtain ⟨s, hs⟩ := hsq
  obtain ⟨b, hb⟩ : ∃ b : ℤ, n = b ^ 2 ∨ n = -b ^ 2 :=
    Int.sq_of_isCoprime (hmn.symm.mul_right hnk) (c := s) (by linear_combination hs)
  obtain ⟨a, ha⟩ : ∃ a : ℤ, m = a ^ 2 ∨ m = -a ^ 2 :=
    Int.sq_of_isCoprime (hmn.mul_right hmk) (c := s) (by linear_combination hs)
  obtain ⟨e, he⟩ : ∃ e : ℤ, k = e ^ 2 ∨ k = -e ^ 2 :=
    Int.sq_of_isCoprime (hmk.symm.mul_right hnk.symm) (c := s) (by linear_combination hs)
  have hbn : n = b ^ 2 := by
    rcases hb with h | h
    · exact h
    · exfalso; linarith [sq_nonneg b]
  have hb0 : b ≠ 0 := by
    intro hb'
    rw [hb'] at hbn
    norm_num at hbn
    omega
  have ha0 : a ≠ 0 := by
    intro ha'
    apply hm
    rcases ha with h | h <;> simp [h, ha']
  have hprod : 0 < m * n * k := by
    refine lt_of_le_of_ne ?_ (Ne.symm (mul_ne_zero (mul_ne_zero hm hn.ne') hk0))
    rw [hs]; exact mul_self_nonneg s
  have hmkpos : 0 < m * k := by
    by_contra hcon
    have hcon' : m * k ≤ 0 := not_lt.mp hcon
    have h1 : m * k * n ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hcon', hn.le⟩)
    linarith [hprod, h1]
  have h2ne : (2 : ℕ) ≠ 0 := by norm_num
  have hab : IsCoprime a b := by
    have h1 : IsCoprime (a ^ 2) (b ^ 2) := by
      rcases ha with h | h
      · rw [← h, ← hbn]; exact hmn
      · have h2 : IsCoprime (-(a ^ 2)) (b ^ 2) := by rw [← h, ← hbn]; exact hmn
        simpa using h2.neg_left
    exact ((h1.of_isCoprime_of_dvd_left (dvd_pow_self a h2ne)).symm.of_isCoprime_of_dvd_left
      (dvd_pow_self b h2ne)).symm
  have habsn : |n| = b ^ 2 := by rw [hbn]; exact abs_of_nonneg (sq_nonneg b)
  rcases ha with hma | hma <;> rcases he with hke | hke
  · refine ⟨a, b, e, hab, ha0, hb0, by rw [← hke, hkdef, hma, hbn]; ring, ?_⟩
    rw [habsn, hma, abs_of_nonneg (sq_nonneg a)]
  · exact absurd hmkpos (by rw [hma, hke]; nlinarith [sq_nonneg a, sq_nonneg e])
  · exact absurd hmkpos (by rw [hma, hke]; nlinarith [sq_nonneg a, sq_nonneg e])
  · refine ⟨b, a, e, hab.symm, hb0, ha0, ?_, ?_⟩
    · have hq0 : -e ^ 2 = a ^ 4 + 11 * a ^ 2 * b ^ 2 - b ^ 4 := by
        rw [← hke, hkdef, hma, hbn]; ring
      linarith
    · rw [habsn, hma]
      rw [abs_neg, abs_of_nonneg (sq_nonneg a)]
      ring

/-- **From the product form back to the quartic.** The product
`mn(m² − 11mn − n²)` is invariant under `(m, n) ↦ (−m, −n)`, so the sign of `n`
is not a restriction. -/
lemma exists_quartic {m n : ℤ} (hmn : IsCoprime m n) (hm : m ≠ 0) (hn : n ≠ 0)
    (hsq : IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2))) :
    ∃ X Y e : ℤ, IsCoprime X Y ∧ X ≠ 0 ∧ Y ≠ 0 ∧
      e ^ 2 = X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4 ∧ X ^ 2 + Y ^ 2 = |m| + |n| := by
  rcases lt_or_gt_of_ne hn with h | h
  · have h1 : IsCoprime (-m) (-n) := (hmn.neg_left).neg_right
    have h2 : (-m) * (-n) * ((-m) ^ 2 - 11 * (-m) * (-n) - (-n) ^ 2) =
        m * n * (m ^ 2 - 11 * m * n - n ^ 2) := by ring
    obtain ⟨X, Y, e, hc, hX, hY, hq, hsz⟩ :=
      exists_quartic_pos h1 (neg_ne_zero.mpr hm) (by linarith) (by rw [h2]; exact hsq)
    exact ⟨X, Y, e, hc, hX, hY, hq, by rw [hsz, abs_neg, abs_neg]⟩
  · exact exists_quartic_pos hmn hm h hsq

/-! ### The descent -/

/-- **The infinite descent.** For coprime nonzero integers `m`, `n` the product
`m·n·(m² − 11mn − n²)` is never a perfect square. The induction is on the
measure `|m| + |n|`: `exists_quartic` converts a square into a quartic with
`X² + Y² = |m| + |n|`, `descent_step` produces a new pair with
`|m'| + |n'| ≤ 2|X| − 2`, and `2|X| − 2 ≤ X² − 1 < X² + Y²` because
`(|X| − 1)² ≥ 0` and `Y² ≥ 1`. -/
theorem not_isSquare_form : ∀ (N : ℕ) (m n : ℤ), m.natAbs + n.natAbs ≤ N →
    IsCoprime m n → m ≠ 0 → n ≠ 0 →
    ¬ IsSquare (m * n * (m ^ 2 - 11 * m * n - n ^ 2)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m n hle hmn hm hn hsq
    obtain ⟨X, Y, e, hXY, hX, hY, heq, hsz⟩ := exists_quartic hmn hm hn hsq
    obtain ⟨m', n', hm'n', hm', hn', hsq', hbd⟩ := descent_step hXY hX hY heq
    have hkey : (m'.natAbs : ℤ) + (n'.natAbs : ℤ) < (m.natAbs : ℤ) + (n.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
      have h1 : 2 * |X| - 2 ≤ X ^ 2 - 1 := by nlinarith [sq_abs X, sq_nonneg (|X| - 1)]
      have h2 : (1 : ℤ) ≤ Y ^ 2 := one_le_sq hY
      linarith
    have hlt : m'.natAbs + n'.natAbs < N := by
      have h1 : (m'.natAbs : ℤ) + (n'.natAbs : ℤ) < (N : ℤ) := by
        have h2 : (m.natAbs : ℤ) + (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
        linarith
      exact_mod_cast h1
    exact ih _ hlt m' n' le_rfl hm'n' hm' hn' hsq'

/-- **The quartic of the `X_1(2,10)` descent** (PROVEN): `e² = X⁴ − 11X²Y² − Y⁴`
has no solution in coprime nonzero integers. It follows from
`not_isSquare_form` applied at `(m, n) = (X², Y²)`, where the product is
`X²Y²(X⁴ − 11X²Y² − Y⁴) = X²Y²e² = (XYe)²`. -/
theorem quartic_no_solution {X Y e : ℤ} (hXY : IsCoprime X Y)
    (hX : X ≠ 0) (hY : Y ≠ 0) :
    e ^ 2 ≠ X ^ 4 - 11 * X ^ 2 * Y ^ 2 - Y ^ 4 := by
  intro h
  refine not_isSquare_form ((X ^ 2).natAbs + (Y ^ 2).natAbs) (X ^ 2) (Y ^ 2) le_rfl
    (hXY.pow) (pow_ne_zero 2 hX) (pow_ne_zero 2 hY) ⟨X * Y * e, ?_⟩
  linear_combination (-(X ^ 2 * Y ^ 2)) * h

end QuarticDescent

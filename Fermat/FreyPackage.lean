/-
Adapted from the FLT project, `FLT/FreyCurve/FreyPackage.lean`
(https://github.com/ImperialCollegeLondon/FLT), Copyright (c) 2025 Kevin
Buzzard, released under the Apache 2.0 license.
Authors of the original: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone.
Adapted for this project: module-system syntax removed, casts adjusted to the
pinned mathlib (v4.32.0-rc1).
-/
import Mathlib

/-!
# Frey packages

A *Frey package* is a bundle of data consisting of nonzero pairwise coprime
integers `a`, `b`, `c` and a prime `p ≥ 5` such that `a ≡ 3 [ZMOD 4]`,
`b` is even, and `a ^ p + b ^ p = c ^ p`.

The main result of this file is that a counterexample to Fermat's Last
Theorem for a prime exponent `p ≥ 5` yields a Frey package
(`FreyPackage.of_not_FermatLastTheoremFor_p_ge_5`), and hence that if there
are no Frey packages then Fermat's Last Theorem holds for all primes `p ≥ 5`
(`FreyPackage.fermatLastTheoremFor_p_ge_5`).

The point of the normalization is that all results of Section 4.1 of Serre's
1987 Duke paper apply to the Frey curve `Y² = X(X - aᵖ)(X + bᵖ)` of a Frey
package.
-/

/-- A *Frey Package* is a 4-tuple `(a, b, c, p)` of integers satisfying
`a ^ p + b ^ p = c ^ p` together with nonvanishing, coprimality, and
congruence conditions guaranteeing that the results in Section 4.1 of Serre's
1987 Duke paper apply to the corresponding Frey curve
`Y² = X(X - aᵖ)(X + bᵖ)`. -/
structure FreyPackage where
  /-- The integer `a` in the Frey package. -/
  a : ℤ
  /-- The integer `b` in the Frey package. -/
  b : ℤ
  /-- The integer `c` in the Frey package. -/
  c : ℤ
  /-- The integer `a` is nonzero. -/
  ha0 : a ≠ 0
  /-- The integer `b` is nonzero. -/
  hb0 : b ≠ 0
  /-- The integer `c` is nonzero. -/
  hc0 : c ≠ 0
  /-- The prime number `p` in the Frey package. -/
  p : ℕ
  /-- The natural number `p` is prime. -/
  pp : Nat.Prime p
  /-- The prime `p` is at least `5`. -/
  hp5 : 5 ≤ p
  /-- The Fermat equation `a ^ p + b ^ p = c ^ p` holds. -/
  hFLT : a ^ p + b ^ p = c ^ p
  /-- The integers `a` and `b` are coprime. Together with `hFLT` this is
  equivalent to `a`, `b` and `c` being pairwise coprime. -/
  hgcdab : gcd a b = 1
  /-- The integer `a` is congruent to `3` modulo `4`. -/
  ha4 : (a : ZMod 4) = 3
  /-- The integer `b` is even, i.e. congruent to `0` modulo `2`. -/
  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

lemma hppos (P : FreyPackage) : 0 < P.p := lt_of_lt_of_le (by omega) P.hp5

lemma hp0 (P : FreyPackage) : P.p ≠ 0 := P.hppos.ne'

lemma hp_odd (P : FreyPackage) : Odd P.p := Nat.Prime.odd_of_ne_two P.pp <|
  have := P.hp5; by linarith

lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p) (h : a ^ p + b ^ p = c ^ p) :
    gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

lemma hgcdac (P : FreyPackage) : gcd P.a P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos P.hFLT, P.hgcdab]

lemma hgcdbc (P : FreyPackage) : gcd P.b P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos, gcd_comm, P.hgcdab]
  rw [add_comm]
  exact P.hFLT

/-- Given a counterexample `a ^ p + b ^ p = c ^ p` to Fermat's Last Theorem
with `p ≥ 5` and prime, there exists a Frey package. -/
lemma of_not_FermatLastTheoremFor_p_ge_5
    {p : ℕ} (pp : p.Prime) (hp5 : 5 ≤ p) (H : ¬ FermatLastTheoremFor p) :
    Nonempty FreyPackage := by
  have p_odd := pp.odd_of_ne_two (by omega)
  -- first get the counterexample
  unfold FermatLastTheoremFor FermatLastTheoremWith at H
  push Not at H
  obtain ⟨a, b, c, ha, hb, hc, hflt⟩ := H
  -- This is natural numbers. Now turn it into a counterexample for integers.
  let A : ℤ := a
  let B : ℤ := b
  let C : ℤ := c
  have hA : A ≠ 0 := Int.ofNat_ne_zero.mpr ha
  have hB : B ≠ 0 := Int.ofNat_ne_zero.mpr hb
  have hC : C ≠ 0 := Int.ofNat_ne_zero.mpr hc
  have H : A ^ p + B ^ p = C ^ p := by
    show (a : ℤ) ^ p + (b : ℤ) ^ p = (c : ℤ) ^ p
    exact_mod_cast hflt
  -- First, show that we can make a,b coprime by dividing through by gcd a b
  have ⟨a, b, c, a0, b0, c0, ab, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ a ^ p + b ^ p = c ^ p := by
    obtain ⟨d, a', b', d0, cop, a_eq, b_eq⟩ :=
      Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left B hA)
    simp only [a_eq, mul_pow, b_eq] at H
    rw [← add_mul, mul_comm] at H
    obtain ⟨c', hCdc⟩ := (Int.pow_dvd_pow_iff pp.ne_zero).1 ⟨_, H.symm⟩
    rw [hCdc] at H hC
    rw [mul_pow] at H
    have a0' := left_ne_zero_of_mul (a_eq ▸ hA)
    have b0' := left_ne_zero_of_mul (b_eq ▸ hB)
    have c0' := right_ne_zero_of_mul hC
    exact ⟨a', b', c', a0', b0', c0', cop, mul_left_cancel₀ (pow_ne_zero _ (mod_cast d0.ne')) H⟩
  -- Then show that WLOG we can take b to be even,
  -- because at least one of a,b,c is even and we can permute if needed
  have ⟨a, b, c, a0, b0, c0, ab, eb, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ Even b ∧
        a ^ p + b ^ p = c ^ p := by
    if eb : Even b then
      exact ⟨a, b, c, a0, b0, c0, ab, eb, H⟩
    else if ea : Even a then
      exact ⟨b, a, c, b0, a0, c0, Int.gcd_comm a b ▸ ab, ea, by rwa [add_comm]⟩
    else
      refine ⟨a, -c, -b, a0, neg_ne_zero.2 c0, neg_ne_zero.2 b0, ?_, even_neg.2 ?_, ?_⟩
      · refine Int.gcd_neg.trans (.trans (.symm ?_) ab)
        exact Nat.cast_inj.1 (gcdab_eq_gcdac pp.pos H)
      · refine ((Int.even_pow (n := p)).1 (H.symm ▸ Int.even_add.2 (iff_of_false ?_ ?_))).1
        · exact fun h => ea (Int.even_pow.1 h).1
        · exact fun h => eb (Int.even_pow.1 h).1
      · simp [p_odd.neg_pow, ← H]
  -- We can ensure additionally that a ≡ 3 [ZMOD 4] by negating everything if necessary
  have ⟨a, b, c, ha0, hb0, hc0, ab, ha3, eb, hFLT⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧
        a ≡ 3 [ZMOD 4] ∧ Even b ∧ a ^ p + b ^ p = c ^ p := by
    -- Since b is even, a cannot also be even
    have a_odd' : ∀ {i}, a ≡ i [ZMOD 4] → ¬2 ∣ i := fun ai ei => by
      have ea := (dvd_sub_right ei).1 (.trans (by decide) (Int.modEq_iff_dvd.1 ai))
      simpa +decide [gcd, ab] using dvd_gcd ea (even_iff_two_dvd.1 eb)
    mod_cases a_mod : a % 4
    · cases a_odd' a_mod (by decide)
    · exact ⟨-a, -b, -c, neg_ne_zero.2 a0, neg_ne_zero.2 b0, neg_ne_zero.2 c0,
        by rwa [Int.neg_gcd, Int.gcd_neg], a_mod.neg, eb.neg,
        by simp [p_odd.neg_pow, ← H, add_comm]⟩
    · cases a_odd' a_mod (by decide)
    · exact ⟨a, b, c, a0, b0, c0, ab, a_mod, eb, H⟩
  -- Build the Frey package from the assumptions
  exact ⟨{
    a, b, c, ha0, hb0, hc0, p, pp, hp5, hFLT
    hgcdab := by simp [gcd, ab]
    ha4 := (ZMod.intCast_eq_intCast_iff ..).2 ha3
    hb2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).2 (even_iff_two_dvd.1 eb)
  }⟩

/-- If there is no Frey package, then Fermat's Last Theorem is true for all
primes `p ≥ 5`. -/
lemma fermatLastTheoremFor_p_ge_5 (h : IsEmpty FreyPackage) :
    ∀ p ≥ 5, p.Prime → FermatLastTheoremFor p := by
  -- assume for a contradiction that we have a counterexample a^p+b^p=c^p
  intro p hp5 hpp
  by_contra hcon
  -- by the previous result, we can make a Frey package `f`
  obtain ⟨f⟩ := of_not_FermatLastTheoremFor_p_ge_5 hpp hp5 hcon
  -- This contradicts our assumption.
  exact IsEmpty.false f

end FreyPackage

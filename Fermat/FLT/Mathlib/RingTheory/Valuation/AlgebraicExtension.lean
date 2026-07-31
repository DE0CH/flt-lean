/-
Own work for the Fermat project (not vendored).
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# `ℚ`-valued extension of a discrete valuation to an algebraic extension

Let `A` be a Dedekind domain with fraction field `K`, let `q` be a height-one
prime of `A`, and let `L / K` be an **algebraic** field extension (typically
`L = AlgebraicClosure K`).  This file constructs an additive valuation

  `w : L → WithTop ℚ`

extending the `q`-adic valuation of `A`, normalised so that `w` takes the value
`N` exactly on `q^N \ q^{N+1}` inside `A`.

## Why `WithTop ℚ` and not `WithTop ℤ`

The value group of *any* extension of `v_q` to a full algebraic closure is
divisible (`w (x^{1/n}) = w x / n`), so no `ℤ`-valued function can be
multiplicative on all of `L`.  Rational values are exactly what is available,
and they are enough: the extension is integral-valued at every point of `A`.

## Construction

`ValuationSubring` + Chevalley's extension theorem
(`LocalSubring.exists_le_valuationSubring`) gives a valuation subring `S` of `L`
**dominating** the local ring of `q` in `K`.  Write `Γ` for the value group of
`S` and `γ := v_S π` for the value of a uniformiser `π` of `q`; domination is
exactly what forces `γ < 1`.

Because `L / K` is algebraic, for every `x ≠ 0` there are `n > 0` and `m : ℤ`
with `v_S x ^ n = γ ^ m` — this is the only nontrivial input, and it comes from
the minimal polynomial of `x` together with the fact that in
`∑ i, a i * x ^ i = 0` the *maximum* of the `v_S (a i * x ^ i)` cannot be
attained only once (`Valuation.map_sum_eq_of_lt`).  The rational number `m / n`
is then well defined and is the value of `w` at `x`.

## Main results

* `FLT.exists_admPair` — the commensurability statement just described.
* `FLT.ratVal` — the resulting `WithTop ℚ`-valued function.
* `FLT.exists_ratValuation_of_heightOneSpectrum` — the packaged existence
  statement used by `Fermat/FLT/Modularity/Interface.lean`.
-/

@[expose] public section

namespace FLT

open Polynomial Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- `AdmPair S π x m n` says that the pair `(m, n)`, with `n > 0`, *computes*
the value of `x ≠ 0` against the uniformiser `π`: `v_S x ^ n = v_S π ^ m`.
The rational number `m / n` is then the additive value of `x` normalised so
that `π` has value `1`. -/
def AdmPair (S : ValuationSubring L) (π : L) (x : L) (m : ℤ) (n : ℕ) : Prop :=
  0 < n ∧ x ≠ 0 ∧ S.valuation x ^ n = S.valuation π ^ m

/-- Two admissible pairs for the same `x` determine the same rational number.
This is where `v_S π ≠ 1` (i.e. `π` is a genuine non-unit) is used: without it
`γ ^ k = 1` for every `k` and nothing is pinned down. -/
theorem admPair_unique {S : ValuationSubring L} {π x : L}
    (hγ0 : 0 < S.valuation π) (hγ1 : S.valuation π < 1)
    {m m' : ℤ} {n n' : ℕ} (h : AdmPair S π x m n) (h' : AdmPair S π x m' n') :
    m * n' = m' * n := by
  obtain ⟨hn, hx, hv⟩ := h
  obtain ⟨hn', _, hv'⟩ := h'
  have key : S.valuation π ^ (m * (n' : ℤ)) = S.valuation π ^ (m' * (n : ℤ)) := by
    rw [zpow_mul, zpow_mul, ← hv, ← hv', ← zpow_natCast (S.valuation x) n,
      ← zpow_natCast (S.valuation x) n', ← zpow_mul, ← zpow_mul, mul_comm]
  exact (zpow_right_injective₀ hγ0 (ne_of_lt hγ1)) key

/-- **Commensurability.**  For an algebraic extension `L / K`, every nonzero
`x : L` admits an admissible pair, provided every nonzero value of `K` is a
power of `γ = v_S π`.

The proof is the classical one: write down the minimal polynomial
`∑ i ∈ support, a i * x ^ i = 0`.  If no admissible pair existed, the values
`v_S (a i * x ^ i)` would be pairwise distinct, so the maximum would be attained
exactly once and `Valuation.map_sum_eq_of_lt` would give the sum a nonzero
value — but the sum is `0`. -/
theorem exists_admPair [Algebra.IsAlgebraic K L] {S : ValuationSubring L} {π : L}
    (hγ0 : 0 < S.valuation π) (_hγ1 : S.valuation π < 1)
    (hK : ∀ k : K, k ≠ 0 → ∃ m : ℤ, S.valuation (algebraMap K L k) = S.valuation π ^ m)
    {x : L} (hx : x ≠ 0) :
    ∃ (m : ℤ) (n : ℕ), AdmPair S π x m n := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon` in usable form: no positive power of `v_S x` is a power of `γ`.
  have hcon' : ∀ (n : ℕ), 0 < n → ∀ m : ℤ, S.valuation x ^ n ≠ S.valuation π ^ m := by
    intro n hn m hm
    exact hcon m n ⟨hn, hx, hm⟩
  set f : K[X] := minpoly K x with hf
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfne : f ≠ 0 := minpoly.ne_zero hxint
  have hsum : ∑ i ∈ f.support, algebraMap K L (f.coeff i) * x ^ i = 0 := by
    have := minpoly.aeval K x
    rwa [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at this
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hfne
  -- pairwise distinct values
  have hdistinct : ∀ i ∈ f.support, ∀ j ∈ f.support, i ≠ j →
      S.valuation (algebraMap K L (f.coeff i) * x ^ i)
        ≠ S.valuation (algebraMap K L (f.coeff j) * x ^ j) := by
    have main : ∀ i ∈ f.support, ∀ j ∈ f.support, j < i →
        S.valuation (algebraMap K L (f.coeff i) * x ^ i)
          ≠ S.valuation (algebraMap K L (f.coeff j) * x ^ j) := by
      intro i hi j hj hji heq
      obtain ⟨a, ha⟩ := hK (f.coeff i) (Polynomial.mem_support_iff.mp hi)
      obtain ⟨b, hb⟩ := hK (f.coeff j) (Polynomial.mem_support_iff.mp hj)
      rw [map_mul, map_mul, map_pow, map_pow, ha, hb] at heq
      have hvx : S.valuation x ≠ 0 := by
        simpa using (Valuation.ne_zero_iff S.valuation).mpr hx
      have hγne : S.valuation π ≠ 0 := ne_of_gt hγ0
      -- cancel `v x ^ j` to get `γ ^ a * v x ^ (i - j) = γ ^ b`
      have hsplit : S.valuation x ^ (i - j) * S.valuation x ^ j = S.valuation x ^ i := by
        rw [← pow_add]
        congr 1
        omega
      have hcancel : S.valuation π ^ a * S.valuation x ^ (i - j) = S.valuation π ^ b := by
        refine mul_right_cancel₀ (pow_ne_zero j hvx) ?_
        calc S.valuation π ^ a * S.valuation x ^ (i - j) * S.valuation x ^ j
            = S.valuation π ^ a * (S.valuation x ^ (i - j) * S.valuation x ^ j) :=
              mul_assoc _ _ _
          _ = S.valuation π ^ a * S.valuation x ^ i := by rw [hsplit]
          _ = S.valuation π ^ b * S.valuation x ^ j := heq
      have hstep : S.valuation x ^ (i - j) = S.valuation π ^ (b - a) := by
        rw [zpow_sub₀ hγne, eq_div_iff (zpow_ne_zero a hγne), mul_comm]
        exact hcancel
      exact hcon' (i - j) (by omega) (b - a) hstep
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact fun e => main j hj i hi h e.symm
    · exact main i hi j hj h
  -- the maximum is attained exactly once
  obtain ⟨j, hjmem, hjmax⟩ :=
    Finset.exists_max_image f.support
      (fun i => S.valuation (algebraMap K L (f.coeff i) * x ^ i)) hne
  have hlt : ∀ i ∈ f.support \ {j},
      S.valuation (algebraMap K L (f.coeff i) * x ^ i)
        < S.valuation (algebraMap K L (f.coeff j) * x ^ j) := by
    intro i hi
    have hi' : i ∈ f.support := (Finset.mem_sdiff.mp hi).1
    have hij : i ≠ j := by simpa using (Finset.mem_sdiff.mp hi).2
    exact lt_of_le_of_ne (hjmax i hi') (hdistinct i hi' j hjmem hij)
  have hzero := Valuation.map_sum_eq_of_lt S.valuation hjmem hlt
  rw [hsum, Valuation.map_zero] at hzero
  have hcj : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hjmem
  have hnz : S.valuation (algebraMap K L (f.coeff j) * x ^ j) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]
    exact mul_ne_zero (by simpa using hcj) (pow_ne_zero _ hx)
  exact hnz hzero.symm

open Classical in
/-- The `WithTop ℚ`-valued additive valuation attached to a valuation subring
`S` of `L` and a uniformiser `π`: the value of `x ≠ 0` is `m / n` for any
admissible pair `(m, n)`, and `⊤` at `0`. -/
noncomputable def ratVal (S : ValuationSubring L) (π : L) (x : L) : WithTop ℚ :=
  if h : ∃ mn : ℤ × ℕ, AdmPair S π x mn.1 mn.2 then
    ((h.choose.1 : ℚ) / (h.choose.2 : ℚ) : ℚ)
  else ⊤

theorem ratVal_eq_of_admPair {S : ValuationSubring L} {π : L}
    (hγ0 : 0 < S.valuation π) (hγ1 : S.valuation π < 1)
    {x : L} {m : ℤ} {n : ℕ} (h : AdmPair S π x m n) :
    ratVal S π x = ((m : ℚ) / (n : ℚ) : ℚ) := by
  classical
  have hex : ∃ mn : ℤ × ℕ, AdmPair S π x mn.1 mn.2 := ⟨(m, n), h⟩
  rw [ratVal, dif_pos hex]
  have hch := hex.choose_spec
  have huniq := admPair_unique hγ0 hγ1 hch h
  have hn : (0 : ℚ) < (n : ℚ) := by exact_mod_cast h.1
  have hn' : (0 : ℚ) < ((hex.choose.2 : ℕ) : ℚ) := by exact_mod_cast hch.1
  have hq : ((hex.choose.1 : ℚ) / (hex.choose.2 : ℚ)) = ((m : ℚ) / (n : ℚ)) := by
    rw [div_eq_div_iff (ne_of_gt hn') (ne_of_gt hn)]
    exact_mod_cast huniq
  rw [hq]

theorem ratVal_zero (S : ValuationSubring L) (π : L) : ratVal S π 0 = ⊤ := by
  classical
  rw [ratVal, dif_neg]
  rintro ⟨mn, -, h, -⟩
  exact h rfl

theorem ratVal_ne_top {S : ValuationSubring L} {π : L} {x : L}
    (h : ∃ (m : ℤ) (n : ℕ), AdmPair S π x m n) : ratVal S π x ≠ ⊤ := by
  classical
  obtain ⟨m, n, hmn⟩ := h
  rw [ratVal, dif_pos ⟨(m, n), hmn⟩]
  exact WithTop.coe_ne_top

/-- Raising an admissible identity `v_S x ^ n = γ ^ m` to the `n'`-th power. -/
theorem valuation_pow_mul_eq {S : ValuationSubring L} {π x : L} {m : ℤ} {n : ℕ}
    (hv : S.valuation x ^ n = S.valuation π ^ m) (n' : ℕ) :
    S.valuation x ^ (n * n') = S.valuation π ^ (m * (n' : ℤ)) := by
  rw [pow_mul, hv, ← zpow_natCast (S.valuation π ^ m) n', ← zpow_mul]

/-- `ratVal` is *antitone* against the multiplicative valuation of `S`: a bigger
`v_S` means a smaller additive value. -/
theorem ratVal_le_ratVal_iff {S : ValuationSubring L} {π : L}
    (hγ0 : 0 < S.valuation π) (hγ1 : S.valuation π < 1)
    {x y : L} (hx : ∃ (m : ℤ) (n : ℕ), AdmPair S π x m n)
    (hy : ∃ (m : ℤ) (n : ℕ), AdmPair S π y m n) :
    ratVal S π x ≤ ratVal S π y ↔ S.valuation y ≤ S.valuation x := by
  obtain ⟨m, n, hmn⟩ := hx
  obtain ⟨m', n', hmn'⟩ := hy
  obtain ⟨hn, hxne, hv⟩ := hmn
  obtain ⟨hn', hyne, hv'⟩ := hmn'
  rw [ratVal_eq_of_admPair hγ0 hγ1 ⟨hn, hxne, hv⟩, ratVal_eq_of_admPair hγ0 hγ1 ⟨hn', hyne, hv'⟩]
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hnQ' : (0 : ℚ) < (n' : ℚ) := by exact_mod_cast hn'
  have hnn : n * n' ≠ 0 := by positivity
  have step1 : (((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ) ≤ (((m' : ℚ) / (n' : ℚ) : ℚ) : WithTop ℚ)
      ↔ m * (n' : ℤ) ≤ m' * (n : ℤ) := by
    rw [WithTop.coe_le_coe, div_le_div_iff₀ hnQ hnQ']
    exact_mod_cast Iff.rfl
  rw [step1]
  have hxp : S.valuation x ^ (n * n') = S.valuation π ^ (m * (n' : ℤ)) :=
    valuation_pow_mul_eq hv n'
  have hyp : S.valuation y ^ (n * n') = S.valuation π ^ (m' * (n : ℤ)) := by
    rw [Nat.mul_comm]; exact valuation_pow_mul_eq hv' n
  constructor
  · intro h
    refine le_of_pow_le_pow_left₀ hnn zero_le ?_
    rw [hxp, hyp]
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hγ0 hγ1).mpr h
  · intro h
    have hpow : S.valuation y ^ (n * n') ≤ S.valuation x ^ (n * n') :=
      pow_le_pow_left₀ zero_le h _
    rw [hxp, hyp] at hpow
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hγ0 hγ1).mp hpow

/-- Comparison of `ratVal` with an *integer*: this is the clause the consumers use. -/
theorem intCast_le_ratVal_iff {S : ValuationSubring L} {π : L}
    (hγ0 : 0 < S.valuation π) (hγ1 : S.valuation π < 1)
    {x : L} (hx : ∃ (m : ℤ) (n : ℕ), AdmPair S π x m n) (N : ℤ) :
    (((N : ℚ) : ℚ) : WithTop ℚ) ≤ ratVal S π x ↔ S.valuation x ≤ S.valuation π ^ N := by
  obtain ⟨m, n, hmn⟩ := hx
  obtain ⟨hn, hxne, hv⟩ := hmn
  rw [ratVal_eq_of_admPair hγ0 hγ1 ⟨hn, hxne, hv⟩, WithTop.coe_le_coe]
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnQ]
  have hcast : ((N : ℚ) * (n : ℚ) ≤ (m : ℚ)) ↔ N * (n : ℤ) ≤ m := by exact_mod_cast Iff.rfl
  rw [hcast]
  have hxp : S.valuation x ^ n = S.valuation π ^ m := hv
  constructor
  · intro h
    refine le_of_pow_le_pow_left₀ hn.ne' zero_le ?_
    rw [hxp, ← zpow_natCast (S.valuation π ^ N) n, ← zpow_mul]
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hγ0 hγ1).mpr h
  · intro h
    have h2 : S.valuation x ^ n ≤ (S.valuation π ^ N) ^ n := pow_le_pow_left₀ zero_le h _
    rw [hxp, ← zpow_natCast (S.valuation π ^ N) n, ← zpow_mul] at h2
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hγ0 hγ1).mp h2

/-- **The valuation axioms and the comparison clause, packaged.**  `S` is a
valuation subring of `L` and `π` a non-unit of `S` coming from `K` whose powers
exhaust the values of `K`; `L / K` algebraic then makes `ratVal S π` an additive
valuation with values in `WithTop ℚ`. -/
theorem exists_ratValuation_of_valuationSubring [Algebra.IsAlgebraic K L]
    (S : ValuationSubring L) (π : L)
    (hγ0 : 0 < S.valuation π) (hγ1 : S.valuation π < 1)
    (hK : ∀ k : K, k ≠ 0 → ∃ m : ℤ, S.valuation (algebraMap K L k) = S.valuation π ^ m) :
    ∃ w : L → WithTop ℚ,
      w 0 = ⊤ ∧ w 1 = 0 ∧
      (∀ x y : L, w (x * y) = w x + w y) ∧
      (∀ x y : L, min (w x) (w y) ≤ w (x + y)) ∧
      (∀ (x : L) (N : ℤ),
        (((N : ℚ) : ℚ) : WithTop ℚ) ≤ w x ↔ S.valuation x ≤ S.valuation π ^ N) := by
  classical
  have hadm : ∀ x : L, x ≠ 0 → ∃ (m : ℤ) (n : ℕ), AdmPair S π x m n :=
    fun x hx => exists_admPair hγ0 hγ1 hK hx
  refine ⟨ratVal S π, ratVal_zero S π, ?_, ?_, ?_, ?_⟩
  · -- `w 1 = 0`
    have h1 : AdmPair S π (1 : L) 0 1 := ⟨Nat.one_pos, one_ne_zero, by simp⟩
    rw [ratVal_eq_of_admPair hγ0 hγ1 h1]
    norm_num
  · -- multiplicativity
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · simp [ratVal_zero]
    rcases eq_or_ne y 0 with rfl | hy
    · simp [ratVal_zero]
    obtain ⟨m, n, hn, -, hv⟩ := hadm x hx
    obtain ⟨m', n', hn', -, hv'⟩ := hadm y hy
    have hxp : S.valuation x ^ (n * n') = S.valuation π ^ (m * (n' : ℤ)) :=
      valuation_pow_mul_eq hv n'
    have hyp : S.valuation y ^ (n * n') = S.valuation π ^ (m' * (n : ℤ)) := by
      rw [Nat.mul_comm]; exact valuation_pow_mul_eq hv' n
    have hxy : AdmPair S π (x * y) (m * (n' : ℤ) + m' * (n : ℤ)) (n * n') := by
      refine ⟨by positivity, mul_ne_zero hx hy, ?_⟩
      rw [map_mul, mul_pow, zpow_add₀ (ne_of_gt hγ0), hxp, hyp]
    rw [ratVal_eq_of_admPair hγ0 hγ1 hxy, ratVal_eq_of_admPair hγ0 hγ1 ⟨hn, hx, hv⟩,
      ratVal_eq_of_admPair hγ0 hγ1 ⟨hn', hy, hv'⟩, ← WithTop.coe_add]
    congr 1
    have hnQ : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hnQ' : ((n' : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hn'.ne'
    push_cast
    field_simp
  · -- ultrametric
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · simp [ratVal_zero]
    rcases eq_or_ne y 0 with rfl | hy
    · simp [ratVal_zero]
    rcases eq_or_ne (x + y) 0 with hxy | hxy
    · rw [hxy, ratVal_zero]; exact le_top
    have hle := S.valuation.map_add x y
    rcases le_total (S.valuation x) (S.valuation y) with h | h
    · -- `v y` is the max, so `ratVal y ≤ ratVal (x+y)` and `ratVal y ≤ ratVal x`
      have h1 : S.valuation (x + y) ≤ S.valuation y := le_trans hle (by simp [max_eq_right h])
      have h2 : ratVal S π y ≤ ratVal S π (x + y) :=
        (ratVal_le_ratVal_iff hγ0 hγ1 (hadm y hy) (hadm _ hxy)).mpr h1
      exact le_trans (min_le_right _ _) h2
    · have h1 : S.valuation (x + y) ≤ S.valuation x := le_trans hle (by simp [max_eq_left h])
      have h2 : ratVal S π x ≤ ratVal S π (x + y) :=
        (ratVal_le_ratVal_iff hγ0 hγ1 (hadm x hx) (hadm _ hxy)).mpr h1
      exact le_trans (min_le_left _ _) h2
  · -- the integer comparison clause
    intro x N
    rcases eq_or_ne x 0 with rfl | hx
    · simp [ratVal_zero, le_top]
    exact intCast_le_ratVal_iff hγ0 hγ1 (hadm x hx) N

section DedekindDomain

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {FK : Type*} [Field FK] [Algebra A FK] [IsFractionRing A FK]

/-- **The `ℚ`-valued extension of a `q`-adic valuation to an algebraic extension
of the fraction field.**

`w` is an additive valuation on `L` whose restriction to `A` is the `q`-adic
order function: `w z ≥ N` exactly when `z ∈ q ^ N`.  In particular `w` takes the
value `N` on `q^N \ q^{N+1}`, so it is normalised at a uniformiser of `q` — not
at the residue characteristic. -/
theorem exists_ratValuation_of_heightOneSpectrum (q : HeightOneSpectrum A)
    (L : Type*) [Field L] [Algebra FK L] [Algebra.IsAlgebraic FK L] :
    ∃ w : L → WithTop ℚ,
      w 0 = ⊤ ∧ w 1 = 0 ∧
      (∀ x y : L, w (x * y) = w x + w y) ∧
      (∀ x y : L, min (w x) (w y) ≤ w (x + y)) ∧
      (∀ (z : A) (N : ℕ), z ∈ q.asIdeal ^ N ↔
        (((N : ℚ) : ℚ) : WithTop ℚ) ≤ w (algebraMap FK L (algebraMap A FK z))) := by
  classical
  obtain ⟨π, hπ⟩ := q.valuation_exists_uniformizer FK
  set vq := q.valuation FK with hvq
  set R : ValuationSubring FK := vq.valuationSubring with hR
  have hexp_le : ∀ c : ℤ, c ≤ 0 →
      WithZero.exp c ≤ (1 : WithZero (Multiplicative ℤ)) := by
    intro c hc
    simpa using WithZero.exp_le_exp.mpr hc
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hπ
    exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) hπ.symm
  have hπL0 : algebraMap FK L π ≠ 0 := by
    simpa using (algebraMap FK L).injective.ne hπ0
  -- Chevalley: dominate the image of `R` by a valuation subring of `L`.
  obtain ⟨S, hS⟩ :=
    (LocalSubring.map (algebraMap FK L) R.toLocalSubring).exists_le_valuationSubring
  obtain ⟨hSle, hSloc⟩ := hS
  have hmapmem : ∀ k : FK, k ∈ R →
      algebraMap FK L k ∈ (LocalSubring.map (algebraMap FK L) R.toLocalSubring).toSubring := by
    intro k hk
    exact Subring.mem_map.mpr ⟨k, hk, rfl⟩
  have hRS : ∀ k : FK, k ∈ R → algebraMap FK L k ∈ S := fun k hk => hSle (hmapmem k hk)
  have hπR : π ∈ R := by
    rw [hR, Valuation.mem_valuationSubring_iff, hπ]
    exact hexp_le _ (by norm_num)
  have hπmem : algebraMap FK L π ∈ S := hRS π hπR
  -- `π` stays a non-unit in `S`: this is exactly what domination buys.
  have hπnotunit : ¬ IsUnit ((⟨algebraMap FK L π, hπmem⟩ : S)) := by
    intro hu
    have hu' : IsUnit ((⟨algebraMap FK L π, hmapmem π hπR⟩ :
        (LocalSubring.map (algebraMap FK L) R.toLocalSubring).toSubring)) :=
      hSloc.1 _ hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu'
    have hy' : (algebraMap FK L π) * (y : L) = 1 := congrArg Subtype.val hy
    obtain ⟨r, hrR, hr⟩ := Subring.mem_map.mp y.2
    have hπr : π * r = 1 := by
      refine (algebraMap FK L).injective ?_
      rw [map_mul, hr, map_one]
      exact hy'
    have hinv : π⁻¹ ∈ R := by
      rw [inv_eq_of_mul_eq_one_right hπr]
      exact hrR
    rw [hR, Valuation.mem_valuationSubring_iff, map_inv₀, hπ] at hinv
    rw [← WithZero.exp_neg, neg_neg] at hinv
    have hle : WithZero.exp (1 : ℤ) ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero]; exact hinv
    exact absurd (WithZero.exp_le_exp.mp hle) (by norm_num)
  have hγ1 : S.valuation (algebraMap FK L π) < 1 :=
    lt_of_le_of_ne (S.valuation_le_one ⟨_, hπmem⟩)
      (fun h => hπnotunit ((S.valuation_eq_one_iff ⟨_, hπmem⟩).mpr h))
  have hγ0 : 0 < S.valuation (algebraMap FK L π) :=
    lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr hπL0))
  -- the exact value of `S.valuation` on `FK`
  have hKexact : ∀ k : FK, k ≠ 0 →
      S.valuation (algebraMap FK L k)
        = S.valuation (algebraMap FK L π) ^ (-(WithZero.log (vq k))) := by
    intro k hk
    set c : ℤ := WithZero.log (vq k) with hc
    have hvk : vq k = WithZero.exp c := (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hk)).symm
    have hune : k * π ^ c ≠ 0 := mul_ne_zero hk (zpow_ne_zero _ hπ0)
    have hvu : vq (k * π ^ c) = 1 := by
      rw [map_mul, map_zpow₀, hπ, hvk, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one,
        ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    have huR : (k * π ^ c) ∈ R := by
      rw [hR, Valuation.mem_valuationSubring_iff, hvu]
    have huinvR : (k * π ^ c)⁻¹ ∈ R := by
      rw [hR, Valuation.mem_valuationSubring_iff, map_inv₀, hvu, inv_one]
    have hSu : S.valuation (algebraMap FK L (k * π ^ c)) = 1 := by
      refine (S.valuation_eq_one_iff ⟨algebraMap FK L (k * π ^ c), hRS _ huR⟩).mp ?_
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap FK L (k * π ^ c)⁻¹, hRS _ huinvR⟩, ?_⟩
      refine Subtype.ext ?_
      show algebraMap FK L (k * π ^ c) * algebraMap FK L (k * π ^ c)⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hune, map_one]
    have hsplit : algebraMap FK L k
        = algebraMap FK L (k * π ^ c) * (algebraMap FK L π) ^ (-c) := by
      rw [map_mul, map_zpow₀, mul_assoc, ← zpow_add₀ hπL0, add_neg_cancel, zpow_zero, mul_one]
    rw [hsplit, map_mul, hSu, one_mul, map_zpow₀]
  have hK : ∀ k : FK, k ≠ 0 →
      ∃ m : ℤ, S.valuation (algebraMap FK L k) = S.valuation (algebraMap FK L π) ^ m :=
    fun k hk => ⟨_, hKexact k hk⟩
  obtain ⟨w, hw0, hw1, hwmul, hwadd, hwcmp⟩ :=
    exists_ratValuation_of_valuationSubring S (algebraMap FK L π) hγ0 hγ1 hK
  refine ⟨w, hw0, hw1, hwmul, hwadd, ?_⟩
  intro z N
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hw0]
  have hzK : algebraMap A FK z ≠ 0 := fun h =>
    hz (IsFractionRing.injective A FK (by rw [h, map_zero]))
  have hcast : ((((N : ℕ) : ℚ) : ℚ) : WithTop ℚ) = ((((N : ℕ) : ℤ) : ℚ) : WithTop ℚ) := by
    norm_cast
  rw [hcast, hwcmp _ ((N : ℕ) : ℤ), hKexact _ hzK]
  rw [zpow_le_zpow_iff_right_of_lt_one₀ hγ0 hγ1]
  -- reduce to the `q`-adic comparison on `A`
  have hvz : vq (algebraMap A FK z) = q.intValuation z := q.valuation_of_algebraMap z
  have hlog : WithZero.exp (WithZero.log (vq (algebraMap A FK z))) = q.intValuation z := by
    rw [WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hzK), hvz]
  rw [← q.intValuation_le_pow_iff_mem z N, ← hlog]
  rw [WithZero.exp_le_exp]
  omega

end DedekindDomain

end FLT

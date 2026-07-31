/-
NumberField/Density.lean — own work for the Fermat project (not vendored
from the FLT project).
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The density input of Chebotarev: an extension in which almost every prime has residue degree one is trivial

This file carries `NumberField.finrank_eq_one_of_forall_inertiaDeg_eq_one`, the single
analytic input of `NumberField.closure_frobAt_eq_top` (Chebotarev) in
`Fermat/FLT/NumberField/ArtinSymbol.lean`:

> for a finite extension `F/k` of number fields and a FINITE set `S` of ideals of `𝓞 k`,
> if every maximal ideal `q` of `𝓞 F` whose contraction avoids `S` has `f(q | 𝓞 k) = 1`,
> then `finrank k F = 1`.

Only the residue degrees are constrained, never the ramification indices; that is
deliberate and makes the statement STRONGER than "splits completely", which is the form
the consumer needs.

## THE PIN HAS THE DEDEKIND ZETA FUNCTION AND THE CLASS NUMBER FORMULA

The docstring this leaf was cut with (2026-07-31) recorded that "mathlib at this pin has
Dirichlet's theorem on primes in arithmetic progressions (the case `k = ℚ`, `N`
cyclotomic) and NOTHING over a general number field … this must be BUILT, not cited".
**That is false, and it was the single most expensive fact about this leaf.** The pin has

* `NumberField.dedekindZeta K s = LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s`
  (`Mathlib/NumberTheory/NumberField/DedekindZeta.lean`, Xavier Roblot), and
* `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, the **Dirichlet class number
  formula**: `(s - 1) * ζ_K(s) → ρ_K` as `s → 1⁺` along the reals, with
  `NumberField.dedekindZeta_residue_pos : 0 < ρ_K`,

resting on `NumberField.Ideal.tendsto_norm_le_div_atTop₀` (the ideal-counting theorem via
`ZLattice.covolume`). So the *deep* analytic content — the simple pole of `ζ_K` at `s = 1`
with a nonzero residue, for an ARBITRARY number field — is already available. What is NOT
available is the elementary bookkeeping that connects `ζ_K` to the primes: mathlib has the
Euler product only for multiplicative functions on `ℕ`, and the multiplicativity of
`n ↦ #{I : absNorm I = n}` is not in the pin.

That relocates the whole difficulty. It is no longer "build the analytic half of class
field theory"; it is "regroup a Dirichlet series over ideals and exhibit an injection".
The three residual leaves below are exactly that, and none of them mentions a Frobenius, a
Galois group, a residue degree or anything else from this development.

## The proof, and where it is cut

Write `n = finrank k F` and suppose `n ≥ 2`. Outside the finite set
`S ∪ ramifiedBelow k F` every maximal `𝔭` of `𝓞 k` is unramified in `F` and has all its
residue degrees `1`, so the fundamental identity `∑ e·f = n` forces exactly `n ≥ 2` primes
above it, each of absolute norm `N 𝔭` (`exists_two_primesOver`, PROVEN below). Choosing two
of them for each such `𝔭` gives an injection

  `(𝔞, 𝔟) ↦ ∏_𝔭 q₁(𝔭) ^ v_𝔭(𝔞) · ∏_𝔭 q₂(𝔭) ^ v_𝔭(𝔟)`

from PAIRS of ideals of `𝓞 k` avoiding `S ∪ ramifiedBelow k F` into ideals of `𝓞 F`, which
multiplies absolute norms. Hence `ζ_F(s) ≥ (ζ_k^{avoiding}(s))²`, and removing the finitely
many bad Euler factors costs only a constant, so `ζ_F(s) ≥ c · ζ_k(s)²` for `s > 1` with
`c > 0`. Now `ζ_k(s) ≥ ρ_k / (2(s-1))` near `1` by the class number formula, so
`(s-1)·ζ_F(s) ≥ c ρ_k² / (4 (s-1)) → ∞`, contradicting `(s-1)·ζ_F(s) → ρ_F < ∞`. That
endgame is `exists_mul_sq_dedekindZeta_re_le` + `finrank_eq_one_of_forall_inertiaDeg_eq_one`,
both PROVEN below.

The cut therefore leaves exactly three open statements, and each is a standard fact about
Dirichlet series over ideals, stated with mathlib vocabulary only:

* `NumberField.dedekindZeta_re_eq_zetaAvoiding_empty` — the REGROUPING. `ζ_K(s)` really is
  the sum of `(N I)^{-s}` over the nonzero ideals. This is `LSeries` unfolded and the
  fibres of `absNorm` collected; it is where `Nat.card {I // absNorm I = n}` is paid for.
* `NumberField.sq_zetaAvoiding_le_zetaAvoiding_empty` — the INJECTION above.
* `NumberField.exists_zetaAvoiding_empty_le` — the finitely many removed Euler factors cost
  at most `∏_{𝔭 ∈ T} (1 - N𝔭^{-s})^{-1} ≤ 2^{#T}`.

## Falsity audit

The statement is TRUE. The finiteness of `S` is load-bearing: with `S` unrestricted the
hypothesis is vacuous and `F` may be anything. With `S` finite the hypothesis still speaks
about infinitely many primes. The three residual leaves were each checked for truth at
`s > 1`, where every series in sight converges absolutely:

* the regrouping is an equality of two absolutely convergent sums over the same index set
  (`absNorm I = 0 ↔ I = ⊥`, and `LSeries.term` is `0` at `n = 0`);
* the injection is injective because `q₁ 𝔭 ≠ q₂ 𝔭'` for all `𝔭, 𝔭'` — for `𝔭 ≠ 𝔭'` the
  contractions differ, for `𝔭 = 𝔭'` the two choices are distinct — and it multiplies norms
  because `absNorm` is multiplicative and `absNorm (qᵢ 𝔭) = absNorm 𝔭`;
* the Euler-factor bound uses only `2 ≤ N 𝔭` for maximal `𝔭`, so each removed factor is at
  most `(1 - 2⁻¹)⁻¹ = 2`.

Note `zetaAvoiding` ignores non-maximal members of `T` on purpose: `¬ 𝔡 ∣ I` for a
composite `𝔡` is not an Euler condition and the factorisation bound above would not be
available for it. The consumer only ever supplies maximal ideals that matter.

## The check that would refute the main statement

A nontrivial finite extension `F/k` of number fields and a finite set `S` of ideals of
`𝓞 k` such that every maximal ideal of `𝓞 F` contracting outside `S` has residue degree `1`
over `𝓞 k`.
-/

@[expose] public section

open scoped NumberField

open Filter Topology

namespace NumberField

variable (k F : Type*) [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]

/-! ### The finitely many ramified primes -/

/-- **The primes of `𝓞 k` that ramify in `F`**: those carrying a prime of `𝓞 F` at which
`𝓞 F / 𝓞 k` is not unramified.

Stated with `Q.IsPrime` rather than `Q.IsMaximal` so that it matches the shape of
`Algebra.IsUnramifiedAt`; the zero ideal is harmless, being unramified in characteristic
zero (`Algebra.isUnramifiedAt_bot`).

Hoisted here from `Fermat/FLT/NumberField/ArtinSymbol.lean` on 2026-07-31, unchanged, so
that the density theorem below can use it; `ArtinSymbol.lean` still consumes it under the
same name and signature. -/
def ramifiedBelow : Set (Ideal (𝓞 k)) :=
  {𝔭 | ∃ (Q : Ideal (𝓞 F)) (_ : Q.IsPrime),
    Q.under (𝓞 k) = 𝔭 ∧ ¬ Algebra.IsUnramifiedAt (𝓞 k) Q}

/-- **ONLY FINITELY MANY PRIMES OF `𝓞 k` RAMIFY IN `F`** (PROVEN 2026-07-31).

A prime `Q` of `𝓞 F` is ramified exactly when it divides the different ideal `𝔡_{F/k}`
(`dvd_differentIdeal_iff`), the different is nonzero (`differentIdeal_ne_bot`), and a
nonzero ideal of a Dedekind domain has only finitely many prime divisors
(`Ideal.finite_factors`). The set below is the image of that finite set under
`Ideal.under`.

The only friction is that both mathlib lemmas are stated with the hypothesis
`Algebra.IsSeparable (FractionRing (𝓞 k)) (FractionRing (𝓞 F))`, and there is no
`Algebra (FractionRing (𝓞 k)) (FractionRing (𝓞 F))` instance to state it against. It is
built here with `FractionRing.liftAlgebra`, whose scalar tower plus
`isAlgebraic_of_isFractionRing` gives algebraicity, hence separability in characteristic
zero. -/
theorem finite_ramifiedBelow : (ramifiedBelow k F).Finite := by
  classical
  letI : Algebra (FractionRing (𝓞 k)) (FractionRing (𝓞 F)) :=
    FractionRing.liftAlgebra (𝓞 k) (FractionRing (𝓞 F))
  haveI : IsScalarTower (𝓞 k) (FractionRing (𝓞 k)) (FractionRing (𝓞 F)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (FractionRing (𝓞 k)) (FractionRing (𝓞 F)) :=
    isAlgebraic_of_isFractionRing (𝓞 k) (𝓞 F) (FractionRing (𝓞 k)) (FractionRing (𝓞 F))
  haveI : Algebra.IsIntegral (FractionRing (𝓞 k)) (FractionRing (𝓞 F)) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : Algebra.IsSeparable (FractionRing (𝓞 k)) (FractionRing (𝓞 F)) := inferInstance
  have hne : differentIdeal (𝓞 k) (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have hfin : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) |
      v.asIdeal ∣ differentIdeal (𝓞 k) (𝓞 F)}.Finite := Ideal.finite_factors hne
  refine Set.Finite.subset (hfin.image (fun v => v.asIdeal.under (𝓞 k))) ?_
  rintro 𝔭 ⟨Q, hQp, rfl, hQr⟩
  haveI := hQp
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    exact hQr Algebra.isUnramifiedAt_bot
  exact ⟨⟨Q, hQp, hQne⟩, dvd_differentIdeal_iff.mpr hQr, rfl⟩

/-! ### The algebraic reduction: two primes of norm `N 𝔭` above almost every `𝔭` -/

variable {k F}

/-- **TWO DISTINCT PRIMES OF THE SAME ABSOLUTE NORM ABOVE EVERY GOOD `𝔭`** (PROVEN
2026-07-31).

If `[F : k] ≥ 2` and `𝔭` is a maximal ideal of `𝓞 k` that is neither in the exceptional set
`S` nor ramified in `F`, then `𝔭` has at least two distinct primes above it, each of
absolute norm `N 𝔭`.

**Proof.** The fundamental identity `Ideal.sum_ramification_inertia` reads
`∑_{Q | 𝔭} e(Q|𝔭) · f(Q|𝔭) = [F : k]`. Every `Q` over `𝔭` is maximal
(`Ideal.IsMaximal.of_liesOver_isMaximal`), contracts to `𝔭`, has `f = 1` by hypothesis and
`e = 1` because `𝔭 ∉ ramifiedBelow k F` (`Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`,
transported along `Ideal.ramificationIdx'_eq_ramificationIdx`). So the sum counts the primes
over `𝔭`, and there are `[F : k] ≥ 2` of them. Their absolute norms are `N 𝔭` by
`Ideal.absNorm_pow_inertiaDeg` with `f = 1`.

This is the ONLY place where the hypothesis on residue degrees is used; everything
downstream sees only the two-primes conclusion. -/
theorem exists_two_primesOver
    (S : Set (Ideal (𝓞 k)))
    (h : ∀ q : Ideal (𝓞 F), q.IsMaximal → q.under (𝓞 k) ∉ S → q.inertiaDeg (𝓞 k) = 1)
    (hn : 2 ≤ Module.finrank k F)
    (𝔭 : Ideal (𝓞 k)) (h𝔭 : 𝔭.IsMaximal) (hS : 𝔭 ∉ S) (hR : 𝔭 ∉ ramifiedBelow k F) :
    ∃ q₁ q₂ : Ideal (𝓞 F), q₁ ≠ q₂ ∧ q₁.IsMaximal ∧ q₂.IsMaximal ∧
      q₁.under (𝓞 k) = 𝔭 ∧ q₂.under (𝓞 k) = 𝔭 ∧
      Ideal.absNorm q₁ = Ideal.absNorm 𝔭 ∧ Ideal.absNorm q₂ = Ideal.absNorm 𝔭 := by
  haveI := h𝔭
  have hp0 : 𝔭 ≠ ⊥ := NeZero.ne 𝔭
  have hsum := Ideal.sum_ramification_inertia (𝓞 F) k F hp0
  have hmem : ∀ Q ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F),
      Q.IsMaximal ∧ Q.under (𝓞 k) = 𝔭 ∧ Ideal.absNorm Q = Ideal.absNorm 𝔭 ∧
        Ideal.ramificationIdx' 𝔭 Q * Ideal.inertiaDeg' 𝔭 Q = 1 := by
    intro Q hQ
    obtain ⟨hQp, hQo⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := Q)).mp hQ
    haveI := hQp
    haveI := hQo
    have hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q 𝔭
    have hunder : Q.under (𝓞 k) = 𝔭 := (Ideal.LiesOver.over (p := 𝔭) (P := Q)).symm
    have hf : Q.inertiaDeg (𝓞 k) = 1 := h Q hQmax (by rw [hunder]; exact hS)
    have hunr : Algebra.IsUnramifiedAt (𝓞 k) Q := by
      by_contra hcon
      exact hR ⟨Q, hQp, hunder, hcon⟩
    haveI := hunr
    have he : Ideal.ramificationIdx' 𝔭 Q = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 Q hp0]
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    have hnorm : Ideal.absNorm Q = Ideal.absNorm 𝔭 := by
      have habs := Ideal.absNorm_pow_inertiaDeg (R := 𝓞 k) (S := 𝓞 F) 𝔭 Q
      rw [hf, pow_one] at habs
      exact habs.symm
    refine ⟨hQmax, hunder, hnorm, ?_⟩
    rw [he, Ideal.inertiaDeg'_eq_inertiaDeg, hf, mul_one]
  have hcard : (IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F)).card = Module.finrank k F := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun Q hQ => ((hmem Q hQ).2.2.2).symm
  have h2 : 1 < (IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F)).card := by omega
  obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ := Finset.one_lt_card.mp h2
  exact ⟨q₁, q₂, hne, (hmem q₁ hq₁).1, (hmem q₂ hq₂).1, (hmem q₁ hq₁).2.1, (hmem q₂ hq₂).2.1,
    (hmem q₁ hq₁).2.2.1, (hmem q₂ hq₂).2.2.1⟩

/-! ### The Dirichlet series over ideals, and the three analytic leaves -/

variable (k F)

/-- **The real Dirichlet series of the nonzero ideals of `𝓞 K` that avoid `T`**:
`∑_{I ≠ ⊥, no maximal member of T divides I} (N I) ^ (-s)`.

`zetaAvoiding K ∅ s` is the full sum, i.e. the Dedekind zeta function of `K` at a real
`s > 1` (`dedekindZeta_re_eq_zetaAvoiding_empty`); a nonempty `T` removes the Euler factors
at the maximal ideals of `T`.

Only the MAXIMAL members of `T` are used. A composite `𝔡 ∈ T` would impose `¬ 𝔡 ∣ I`, which
is not an Euler condition, and `exists_zetaAvoiding_empty_le` would be false for it. -/
noncomputable def zetaAvoiding (K : Type*) [Field K] [NumberField K]
    (T : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ ∀ 𝔭 ∈ T, 𝔭.IsMaximal → ¬ 𝔭 ∣ I},
    (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)

theorem zetaAvoiding_nonneg (K : Type*) [Field K] [NumberField K]
    (T : Set (Ideal (𝓞 K))) (s : ℝ) : 0 ≤ zetaAvoiding K T s :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

open Asymptotics Finset in
/-- **THE PARTIAL SUMS OF THE IDEAL-COUNTING FUNCTION ARE `~ ρ_K · x`** (PROVEN 2026-07-31).

`(∑_{m ≤ n} #{I : N I = m}) / n → ρ_K`. This is mathlib's ideal-counting theorem
`NumberField.Ideal.tendsto_norm_le_div_atTop₀` with the counting function rewritten from
"norm at most `n`" to "the fibres of the norm summed", exactly as the proof of
`tendsto_sub_one_mul_dedekindZeta_nhdsGT` does it internally; it is lifted out here
because all three leaves below need it and mathlib does not export it. -/
theorem tendsto_sum_card_absNorm_eq_div (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun n : ℕ ↦ (∑ m ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← _root_.Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ _root_.Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

open Asymptotics in
/-- **THE DIRICHLET SERIES OF `ζ_K` CONVERGES ABSOLUTELY AT EVERY REAL `s > 1`** (PROVEN
2026-07-31).

`LSeriesSummable_of_sum_norm_bigO_and_nonneg` applied to the previous lemma with `r = 1`.
This is the convergence hypothesis every one of the three leaves below silently needs, and
it is the reason each of them is stated with `1 < s`. -/
theorem lseriesSummable_dedekindZeta (K : Type*) [Field K] [NumberField K] {s : ℝ}
    (hs : 1 < s) :
    LSeriesSummable
      (fun n ↦ ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (fun _ ↦ Nat.cast_nonneg _)
    zero_le_one (by simpa using hs)
  have hlim := tendsto_sum_card_absNorm_eq_div K
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (r := 1) (by simpa using hlim)

/-- **LEAF 1 — THE REGROUPING: `ζ_K(s)` is the sum of `(N I)^{-s}` over the nonzero ideals**
(OPEN, cut 2026-07-31).

`dedekindZeta K` is `LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n})`, i.e.
the coefficients are already the fibres of `Ideal.absNorm`. So this is the statement that
summing over `ℕ` with multiplicities is the same as summing over the ideals themselves.

**What it needs.** `LSeries.term` vanishes at `n = 0` and `Ideal.absNorm I = 0 ↔ I = ⊥`
(`Ideal.absNorm_eq_zero_iff`), so both sides are indexed by the nonzero ideals; the fibres
of `absNorm` are finite (`NumberField.Ideal.finite_setOf_absNorm_eq`, used by
`tendsto_sub_one_mul_dedekindZeta_nhdsGT` in mathlib) and the regrouping is
`tsum_sigma`/`Summable.tsum_fiberwise` for the map `I ↦ absNorm I`. The value is real
because every coefficient is a natural number, which is why `.re` loses nothing.

**Convergence is already available**: `lseriesSummable_dedekindZeta` above, PROVEN, is
`LSeriesSummable` of these coefficients at every real `s > 1`. Combined with
`summable_norm_iff` it gives absolute convergence of the `ℕ`-indexed side; the ideal-indexed
side then follows from `summable_sigma_of_nonneg` along
`Equiv.sigmaFiberEquiv (fun I ↦ Ideal.absNorm I)`, whose fibres are finite by
`Ideal.finite_setOf_absNorm_eq`. Do not re-derive the counting estimate — it is
`tendsto_sum_card_absNorm_eq_div`, also PROVEN above. -/
theorem dedekindZeta_re_eq_zetaAvoiding_empty (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    (dedekindZeta K s).re = zetaAvoiding K ∅ s :=
  sorry

/-- **LEAF 2 — THE INJECTION: two primes above almost every `𝔭` square the zeta function**
(OPEN, cut 2026-07-31).

Given, for every maximal `𝔭` of `𝓞 k` outside `T`, two DISTINCT primes `q₁ 𝔭 ≠ q₂ 𝔭` of
`𝓞 F` above `𝔭` of absolute norm `N 𝔭`, the assignment

  `(𝔞, 𝔟) ↦ ∏_𝔭 (q₁ 𝔭) ^ v_𝔭 𝔞 · ∏_𝔭 (q₂ 𝔭) ^ v_𝔭 𝔟`

is an injection from PAIRS of nonzero `T`-avoiding ideals of `𝓞 k` into the nonzero ideals
of `𝓞 F`, and it multiplies absolute norms. Summing `(N ·)^{-s}` over the image is therefore
at most the full sum over `𝓞 F`, while the sum over the source factors as a square.

**What it needs.** A choice function `𝔭 ↦ (q₁ 𝔭, q₂ 𝔭)` on the maximal ideals outside `T`
(`Classical.choice` on the hypothesis); the multiplicative extension of it to ideals, which
is `∏ᶠ` over `IsDedekindDomain.HeightOneSpectrum` with exponents
`IsDedekindDomain.HeightOneSpectrum.count`/`Ideal.factorization` — mathlib's
`FractionalIdeal.finprod_heightOneSpectrum_factorization'` is the statement that the ideal
monoid really is free on the height-one primes, and it is what makes both the
well-definedness and the injectivity mechanical; `Ideal.absNorm` is a `MonoidHom`, which
gives the norm identity from `absNorm (qᵢ 𝔭) = absNorm 𝔭`; and
`Summable.mul_of_nonneg`/`tsum_mul_tsum_of_summable_norm` to turn the sum over pairs into a
square.

**Why the primes must be distinct.** If `q₁ 𝔭 = q₂ 𝔭` the map is not injective — this is
exactly the point where "`𝔭` splits into at least two" is used, and it is why the
consumer must rule out ramification and not merely control residue degrees. -/
theorem sq_zetaAvoiding_le_zetaAvoiding_empty
    (T : Set (Ideal (𝓞 k)))
    (h : ∀ 𝔭 : Ideal (𝓞 k), 𝔭.IsMaximal → 𝔭 ∉ T →
      ∃ q₁ q₂ : Ideal (𝓞 F), q₁ ≠ q₂ ∧ q₁.IsMaximal ∧ q₂.IsMaximal ∧
        q₁.under (𝓞 k) = 𝔭 ∧ q₂.under (𝓞 k) = 𝔭 ∧
        Ideal.absNorm q₁ = Ideal.absNorm 𝔭 ∧ Ideal.absNorm q₂ = Ideal.absNorm 𝔭)
    (s : ℝ) (hs : 1 < s) :
    (zetaAvoiding k T s) ^ 2 ≤ zetaAvoiding F ∅ s :=
  sorry

/-- **LEAF 3 — REMOVING FINITELY MANY EULER FACTORS COSTS A CONSTANT** (OPEN, cut
2026-07-31).

Every nonzero ideal `𝔞` of `𝓞 K` factors uniquely as `𝔟 · 𝔠` with `𝔟` supported on the
maximal ideals of `T` and `𝔠` avoiding them, so

  `ζ_K(s) = (∑_{𝔟 T-supported} (N 𝔟)^{-s}) · zetaAvoiding K T s`,

and the first factor is `∏_{𝔭 ∈ T maximal} (1 - (N 𝔭)^{-s})⁻¹ ≤ 2 ^ #T` for `s > 1`,
because `2 ≤ N 𝔭` for a maximal `𝔭`. The constant is uniform in `s`, which is what the
endgame needs — it takes `s → 1⁺`.

**What it needs.** The `T`-part/`T`-free factorisation of an ideal (again
`Ideal.factorization` over `HeightOneSpectrum`, or `UniqueFactorizationMonoid`
`Finsupp` support splitting), and the geometric series for each of the finitely many
removed factors. Nothing analytic beyond `Summable.mul_of_nonneg`.

Only the maximal members of `T` are removed, by the definition of `zetaAvoiding`; a
composite member imposes a non-Euler condition and this bound would fail for it. -/
theorem exists_zetaAvoiding_empty_le (T : Set (Ideal (𝓞 k))) (hT : T.Finite) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → zetaAvoiding k ∅ s ≤ C * zetaAvoiding k T s :=
  sorry

/-! ### The endgame -/

/-- **THE CLASS NUMBER FORMULA, REAL-VALUED** (PROVEN 2026-07-31).

`(s - 1) · ζ_K(s) → ρ_K` as `s → 1⁺` along the reals, with `ρ_K = dedekindZeta_residue K`
positive. This is mathlib's `tendsto_sub_one_mul_dedekindZeta_nhdsGT` with `Complex.re`
applied; the coefficients of `ζ_K` are natural numbers, so nothing is lost. -/
theorem tendsto_sub_one_mul_dedekindZeta_re (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K s).re) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  simp only [Function.comp_def, Complex.ofReal_re] at h
  refine h.congr fun s => ?_
  rw [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]

/-- **`ζ_F` DOMINATES `ζ_k²` WHEN ALMOST EVERY PRIME OF `k` HAS TWO PRIMES OF `F` OF THE
SAME NORM ABOVE IT** (PROVEN 2026-07-31 over the three leaves above).

Pure assembly: leaf 3 gives `ζ_k(s) ≤ C · Z(s)` where `Z = zetaAvoiding k T`, leaf 2 gives
`Z(s)² ≤ ζ_F(s)`, and `Z ≥ 0`, so `C⁻² · ζ_k(s)² ≤ Z(s)² ≤ ζ_F(s)`. Leaf 1 is what lets the
last two be compared at all. -/
theorem exists_mul_sq_dedekindZeta_re_le
    (T : Set (Ideal (𝓞 k))) (hT : T.Finite)
    (h : ∀ 𝔭 : Ideal (𝓞 k), 𝔭.IsMaximal → 𝔭 ∉ T →
      ∃ q₁ q₂ : Ideal (𝓞 F), q₁ ≠ q₂ ∧ q₁.IsMaximal ∧ q₂.IsMaximal ∧
        q₁.under (𝓞 k) = 𝔭 ∧ q₂.under (𝓞 k) = 𝔭 ∧
        Ideal.absNorm q₁ = Ideal.absNorm 𝔭 ∧ Ideal.absNorm q₂ = Ideal.absNorm 𝔭) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 1 < s →
      c * ((dedekindZeta k s).re) ^ 2 ≤ (dedekindZeta F s).re := by
  obtain ⟨C, hC, hCle⟩ := exists_zetaAvoiding_empty_le k T hT
  refine ⟨(C ^ 2)⁻¹, by positivity, fun s hs => ?_⟩
  have hZ : 0 ≤ zetaAvoiding k T s := zetaAvoiding_nonneg k T s
  have hzk : (dedekindZeta k s).re = zetaAvoiding k ∅ s :=
    dedekindZeta_re_eq_zetaAvoiding_empty k s hs
  have hzF : (dedekindZeta F s).re = zetaAvoiding F ∅ s :=
    dedekindZeta_re_eq_zetaAvoiding_empty F s hs
  have h1 : zetaAvoiding k ∅ s ≤ C * zetaAvoiding k T s := hCle s hs
  have h2 : (zetaAvoiding k T s) ^ 2 ≤ zetaAvoiding F ∅ s :=
    sq_zetaAvoiding_le_zetaAvoiding_empty k F T h s hs
  have h0 : 0 ≤ zetaAvoiding k ∅ s := zetaAvoiding_nonneg k ∅ s
  rw [hzk, hzF]
  have hsq : (zetaAvoiding k ∅ s) ^ 2 ≤ (C * zetaAvoiding k T s) ^ 2 := by
    have := mul_nonneg hC.le hZ
    nlinarith
  have : (C ^ 2)⁻¹ * (zetaAvoiding k ∅ s) ^ 2 ≤ (C ^ 2)⁻¹ * (C * zetaAvoiding k T s) ^ 2 := by
    have hCinv : (0:ℝ) < (C ^ 2)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hsq hCinv.le
  have heq : (C ^ 2)⁻¹ * (C * zetaAvoiding k T s) ^ 2 = (zetaAvoiding k T s) ^ 2 := by
    field_simp
  linarith [this, heq ▸ h2]

/-- **THE DENSITY INPUT OF CHEBOTAREV: a finite extension of number fields in which all but
finitely many primes of the base have residue degree one is trivial** (PROVEN 2026-07-31
over the three Dirichlet-series leaves above).

Only the residue degrees are constrained, not the ramification indices: the hypothesis is
`f(q | 𝔭) = 1` for every maximal `q` of `𝓞 F` whose contraction avoids the finite set `S`.
That is weaker than "splits completely" and makes the statement STRONGER, which is what
`NumberField.closure_frobAt_eq_top` needs (it controls `f` and never touches `e`).

**Proof.** Suppose `n = finrank k F ≥ 2`. Outside the finite set `S ∪ ramifiedBelow k F`,
`exists_two_primesOver` gives two distinct primes of `𝓞 F` of absolute norm `N 𝔭` above
every maximal `𝔭`, so `exists_mul_sq_dedekindZeta_re_le` gives `c > 0` with
`c · ζ_k(s)² ≤ ζ_F(s)` for every real `s > 1`. The class number formula makes
`(s-1) ζ_k(s) → ρ_k > 0`, hence `ζ_k(s) > ρ_k / (2(s-1))` near `1`, hence
`(s-1) ζ_F(s) ≥ c ρ_k² / (4(s-1))`, which is unbounded as `s → 1⁺` — against
`(s-1) ζ_F(s) → ρ_F`. So `n = 1`.

**The finiteness hypothesis is load-bearing.** Without it the statement is false for a
trivial reason: take `S` to be everything, and the hypothesis becomes vacuous while `F` may
be any extension. With `S` finite the hypothesis still speaks about infinitely many primes,
since `𝓞 k` has infinitely many maximal ideals.

**The check that would refute it**: a nontrivial finite extension `F/k` of number fields and
a finite set `S` of primes of `𝓞 k` such that every maximal ideal of `𝓞 F` contracting
outside `S` has residue degree `1` over `𝓞 k`. -/
theorem finrank_eq_one_of_forall_inertiaDeg_eq_one
    (S : Set (Ideal (𝓞 k))) (hS : S.Finite)
    (h : ∀ q : Ideal (𝓞 F), q.IsMaximal → q.under (𝓞 k) ∉ S → q.inertiaDeg (𝓞 k) = 1) :
    Module.finrank k F = 1 := by
  by_contra hne
  have hpos : 0 < Module.finrank k F := Module.finrank_pos
  have hn : 2 ≤ Module.finrank k F := by omega
  obtain ⟨c, hc, hle⟩ := exists_mul_sq_dedekindZeta_re_le k F (S ∪ ramifiedBelow k F)
    (hS.union (finite_ramifiedBelow k F))
    (fun 𝔭 h𝔭 hnot => exists_two_primesOver S h hn 𝔭 h𝔭 (fun hx => hnot (Or.inl hx))
      (fun hx => hnot (Or.inr hx)))
  set ρk := dedekindZeta_residue k with hρkdef
  set ρF := dedekindZeta_residue F with hρFdef
  have hρk : 0 < ρk := dedekindZeta_residue_pos k
  have hρF : 0 < ρF := dedekindZeta_residue_pos F
  have hA : ∀ᶠ s : ℝ in 𝓝[>] 1, ρk / 2 < (s - 1) * (dedekindZeta k s).re :=
    (tendsto_sub_one_mul_dedekindZeta_re k).eventually_const_lt (by linarith)
  have hB : ∀ᶠ s : ℝ in 𝓝[>] 1, (s - 1) * (dedekindZeta F s).re < ρF + 1 :=
    (tendsto_sub_one_mul_dedekindZeta_re F).eventually_lt_const (by linarith)
  set ε : ℝ := c * ρk ^ 2 / (4 * (ρF + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝 (1:ℝ)) (𝓝 (1 - 1)) :=
      (continuous_sub_right (1:ℝ)).tendsto 1
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hC : ∀ᶠ s : ℝ in 𝓝[>] 1, s - 1 < ε := hsub.eventually_lt_const hε
  obtain ⟨s, hsA, hsB, hsC, hs1⟩ := (hA.and (hB.and (hC.and self_mem_nhdsWithin))).exists
  have hs1' : (1:ℝ) < s := hs1
  have hu : (0:ℝ) < s - 1 := by linarith
  have hsev := hle s hs1'
  set A := (dedekindZeta k s).re with hAdef
  set B := (dedekindZeta F s).re with hBdef
  have hA0 : 0 < A := by nlinarith
  have hsq : ρk ^ 2 / 4 < ((s - 1) * A) ^ 2 := by nlinarith
  have h3 : (s - 1) ^ 2 * (c * A ^ 2) ≤ (s - 1) ^ 2 * B := by nlinarith
  have h4 : c * ρk ^ 2 / 4 < (s - 1) ^ 2 * B := by nlinarith
  have h6 : (s - 1) * ((s - 1) * B) < (s - 1) * (ρF + 1) := by nlinarith
  have h7 : c * ρk ^ 2 / 4 < (s - 1) * (ρF + 1) := by nlinarith
  have h8 : ε * (ρF + 1) = c * ρk ^ 2 / 4 := by
    rw [hεdef]; field_simp
  nlinarith

end NumberField

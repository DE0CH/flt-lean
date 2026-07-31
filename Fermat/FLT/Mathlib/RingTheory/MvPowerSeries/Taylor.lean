/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.Mathlib.RingTheory.MvPowerSeries.AdicEval
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The first-order Taylor estimate for a multivariate power series

Fontaine's step 4 (*Il n'y a pas de variété abélienne sur ℤ*, Invent. Math. 81
(1985), pp. 521–522) needs the following estimate.  Let `O` be `I`-adically
complete, let `f` be a power series over `R` whose every partial derivative is
`3` times another series, `∂f/∂X_j = 3 gⱼ`, and let `w` be a tuple from `I` and
`μ` a tuple from `I ^ t`.  Then

`f(w + μ) − f(w) − 3 · Σⱼ gⱼ(w) · μⱼ  ∈  I ^ (t + e + 1)`

as soon as `3 ∈ I ^ e` and `e < 2t`.

## Why the threshold `e < 2t` and not `t > e`

A plain monomial expansion gives a remainder only in `I ^ (2t)`, and
`I ^ (2t) ⊆ I ^ (t + e + 1)` would need `t > e`, which is strictly stronger than
`e < 2t`.  The estimate closes because the **quadratic** coefficients of the
translated series carry their own factor of `3`: differentiating twice,
`∂²f/∂X_j∂X_k = 3 · ∂g_j/∂X_k`, so the degree-`2` part of `f(w + Y)` lies in
`3 · (Y)²` up to a factor of `2`, and the cubic-and-higher part is already in
`I ^ (3t) ⊆ I ^ (t + e + 1)`.

**No Hasse derivatives and no divided powers are needed**, and neither is the
invertibility of `2`.  The factor `2` that appears when `j = k` is removed by the
identity `x = 3x − 2x`: both `3x` and `2x` are shown to lie in the target ideal
separately, the first because `3 ∈ I ^ e` and the second because
`2 · coeff (2·e_j) = ∂²f/∂X_j²` is divisible by `3`.  That is the whole trick, and
it is why this file has no characteristic hypothesis.

## Main definitions

* `MvPolynomial.translate` — the `R`-algebra map `MvPolynomial σ R →ₐ[R]
  MvPolynomial σ O` sending `X_j ↦ C (w j) + X_j`.  Its coefficients are the
  (divided) derivatives of `p` at `w`, which is how the Taylor expansion is
  extracted here without ever writing a Hasse derivative.

## Main results

* `MvPolynomial.eval_sub_linear_mem` — the abstract sum split: if every
  coefficient of total degree `≥ 2` contributes to an ideal `T` after being
  multiplied by the corresponding monomial in `μ`, then `eval μ` differs from its
  own linearisation by an element of `T`.
* `MvPowerSeries.adicEvalOfMem_taylor_mem` — the estimate above.
-/

@[expose] public section

namespace MvPolynomial

section Translate

variable {σ : Type*} {R : Type*} [CommRing R] {O : Type*} [CommRing O] [Algebra R O]

/-- **TRANSLATION OF THE VARIABLES BY A TUPLE `w`**: the `R`-algebra map
`MvPolynomial σ R →ₐ[R] MvPolynomial σ O` sending `X_j` to `C (w j) + X_j`.

This is the carrier of the Taylor expansion of `p` at `w`: the coefficient of
`X^d` in `translate w p` is the `d`-th divided derivative of `p` at `w`, but it is
available here as a plain coefficient, with no division and no divided-power
structure. -/
noncomputable def translate (w : σ → O) : MvPolynomial σ R →ₐ[R] MvPolynomial σ O :=
  aeval fun k => C (w k) + X k

@[simp]
theorem translate_X (w : σ → O) (k : σ) :
    translate (R := R) w (X k) = C (w k) + X k := by
  simp [translate]

/-- Evaluating a translate at `v` is evaluating the original at `w + v`. -/
theorem eval_translate (w v : σ → O) (p : MvPolynomial σ R) :
    eval v (translate (R := R) w p) = aeval (w + v) p := by
  have key : ((aeval v : MvPolynomial σ O →ₐ[O] O).restrictScalars R).comp
      (translate (R := R) w) = aeval (w + v) := by
    refine algHom_ext fun k => ?_
    simp
  have := AlgHom.congr_fun key p
  simpa [coe_aeval_eq_eval] using this

/-- The constant coefficient of a translate is the value at `w`. -/
theorem constantCoeff_translate (w : σ → O) (p : MvPolynomial σ R) :
    constantCoeff (translate (R := R) w p) = aeval w p := by
  have h := eval_translate (R := R) w 0 p
  rw [add_zero] at h
  rw [← h]
  exact (RingHom.congr_fun eval_zero _).symm

/-- **TRANSLATION COMMUTES WITH THE PARTIAL DERIVATIVES.**  This is the chain rule
for a translation, and it is what turns "every `∂f/∂X_j` is divisible by `3`" into
"every coefficient of `translate w f` of total degree `≥ 1` is divisible by `3`,
up to a factor coming from the exponent". -/
theorem pderiv_translate (w : σ → O) (j : σ) (p : MvPolynomial σ R) :
    pderiv j (translate (R := R) w p) = translate (R := R) w (pderiv j p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h1 : translate (R := R) w (C a) = C (algebraMap R O a) := by
        simp [translate]
      simp [h1]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      have h1 : translate (R := R) w (p * X k) =
          translate (R := R) w p * (C (w k) + X k) := by
        rw [map_mul, translate_X]
      have h2 : translate (R := R) w (pderiv j (p * X k)) =
          translate (R := R) w (pderiv j p) * (C (w k) + X k) +
            translate (R := R) w p * translate (R := R) w (pderiv j (X k)) := by
        rw [pderiv_mul, map_add, map_mul, map_mul, translate_X]
      have h3 : (pderiv j) (X k : MvPolynomial σ O) =
          translate (R := R) w (pderiv j (X k : MvPolynomial σ R)) := by
        rcases eq_or_ne j k with rfl | hjk
        · rw [pderiv_X_self, pderiv_X_self, map_one]
        · rw [pderiv_X_of_ne hjk.symm, pderiv_X_of_ne hjk.symm, map_zero]
      rw [h1, pderiv_mul, hp, h2, map_add, pderiv_C, zero_add, h3]

end Translate

section SumSplit

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {O : Type*} [CommRing O]

omit [Fintype σ] in
/-- A multidegree of total degree at most `1` is either `0` or a single variable. -/
theorem eq_zero_or_eq_single_of_degree_le_one {d : σ →₀ ℕ} (hd : d.degree ≤ 1) :
    d = 0 ∨ ∃ j, d = Finsupp.single j 1 := by
  classical
  rcases eq_or_ne d 0 with rfl | hne
  · exact Or.inl rfl
  refine Or.inr ?_
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  refine ⟨j, ?_⟩
  have hdj1 : d j ≤ 1 := le_trans (Finset.single_le_sum (f := fun i => d i)
    (fun _ _ => Nat.zero_le _) hj) hd
  have hdjpos : 0 < d j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
  have hdj : d j = 1 := le_antisymm hdj1 hdjpos
  have hsupp : ∀ k, k ≠ j → d k = 0 := by
    intro k hk
    by_contra hkne
    have hkmem : k ∈ d.support := Finsupp.mem_support_iff.mpr hkne
    have hsub : ({j, k} : Finset σ) ⊆ d.support := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hj
      · exact hkmem
    have hpair : d j + d k ≤ d.degree :=
      calc d j + d k = ∑ i ∈ ({j, k} : Finset σ), d i := by
            rw [Finset.sum_pair (Ne.symm hk)]
        _ ≤ d.degree := Finset.sum_le_sum_of_subset hsub
    have : 0 < d k := Nat.pos_of_ne_zero hkne
    omega
  refine Finsupp.ext fun k => ?_
  rcases eq_or_ne k j with rfl | hk
  · simp [hdj]
  · simp [hsupp k hk, hk]

/-- **THE SUM SPLIT**: `eval μ f` agrees with its own linearisation
`coeff 0 f + Σⱼ coeff (single j 1) f · μⱼ` modulo any ideal `T` that already
receives every degree-`≥ 2` contribution.

This is the only combinatorial content of the Taylor estimate: the degree-`0` and
degree-`1` parts of the coefficient sum are read off exactly, and everything else
is deferred to the hypothesis. -/
theorem eval_sub_linear_mem (T : Ideal O) (f : MvPolynomial σ O) (μ : σ → O)
    (hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree →
      coeff d f * ∏ i ∈ d.support, μ i ^ d i ∈ T) :
    eval μ f - coeff 0 f - ∑ j, coeff (Finsupp.single j 1) f * μ j ∈ T := by
  classical
  set term : (σ →₀ ℕ) → O := fun d => coeff d f * ∏ i ∈ d.support, μ i ^ d i with hterm
  set U : Finset (σ →₀ ℕ) :=
    insert 0 (Finset.univ.image fun j : σ => Finsupp.single j 1) with hU
  have hsmall : ∑ d ∈ U, term d = coeff 0 f + ∑ j, coeff (Finsupp.single j 1) f * μ j := by
    have h0 : (0 : σ →₀ ℕ) ∉ Finset.univ.image fun j : σ => Finsupp.single j 1 := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro j hj
      exact one_ne_zero (Finsupp.single_eq_zero.mp hj)
    rw [hU, Finset.sum_insert h0]
    congr 1
    · simp [hterm]
    · rw [Finset.sum_image (fun a _ b _ hab => by
        have := congrArg (fun g => (g : σ →₀ ℕ) a) hab
        simpa [Finsupp.single_apply, eq_comm] using this)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hterm]
  have hsub : f.support.filter (fun d => d.degree ≤ 1) ⊆ U := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rcases eq_zero_or_eq_single_of_degree_le_one hd.2 with rfl | ⟨j, rfl⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hzero : ∀ d ∈ U, d ∉ f.support.filter (fun d => d.degree ≤ 1) → term d = 0 := by
    intro d hd hnot
    have hdle : d.degree ≤ 1 := by
      rw [hU, Finset.mem_insert] at hd
      rcases hd with rfl | hd
      · simp
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
        simp
    have : d ∉ f.support := by
      intro hmem
      exact hnot (Finset.mem_filter.mpr ⟨hmem, hdle⟩)
    simp [hterm, MvPolynomial.notMem_support_iff.mp this]
  have hsplit : eval μ f =
      (∑ d ∈ f.support.filter (fun d => d.degree ≤ 1), term d) +
      ∑ d ∈ f.support.filter (fun d => ¬ d.degree ≤ 1), term d := by
    rw [eval_eq]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hrest : ∑ d ∈ f.support.filter (fun d => ¬ d.degree ≤ 1), term d ∈ T := by
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [Finset.mem_filter] at hd
    exact hbig d (by omega)
  rw [hsplit, Finset.sum_subset hsub hzero, hsmall]
  convert hrest using 1
  ring

end SumSplit

end MvPolynomial

namespace MvPowerSeries

section Truncation

variable {σ : Type*} [Finite σ] {R : Type*} [CommRing R]

/-- **THE DERIVATIVE OF A TRUNCATION IS THE TRUNCATION OF THE DERIVATIVE**, one
degree lower.  This is what carries the divisibility hypothesis
`∂f/∂X_j = 3 gⱼ` from the power series to the polynomial the estimate is actually
run on. -/
theorem pderiv_truncTotal (n : ℕ) (j : σ) (f : MvPowerSeries σ R) :
    MvPolynomial.pderiv j (truncTotal (n + 1) f) = truncTotal n (pderiv j f) := by
  classical
  ext d
  rw [MvPolynomial.coeff_pderiv, coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite,
    coeff_pderiv]
  have hdeg : (d + Finsupp.single j 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  rw [hdeg]
  by_cases hd : d.degree < n
  · rw [if_pos (by omega), if_pos hd, nsmul_eq_mul, mul_comm]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg hd, zero_mul]

end Truncation

section Taylor

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommRing R]
  {O : Type*} [CommRing O] [Algebra R O]

omit [Fintype σ] [DecidableEq σ] in
/-- A monomial in a tuple drawn from `I ^ t` lies in `I ^ (t · |d|)`. -/
theorem prod_pow_mem_pow (I : Ideal O) (t : ℕ) {μ : σ → O} (hμ : ∀ i, μ i ∈ I ^ t)
    (d : σ →₀ ℕ) : ∏ i ∈ d.support, μ i ^ d i ∈ I ^ (t * d.degree) := by
  classical
  have h1 : ∏ i ∈ d.support, μ i ^ d i ∈ ∏ i ∈ d.support, I ^ (t * d i) := by
    refine Ideal.prod_mem_prod fun i _ => ?_
    rw [pow_mul]
    exact Ideal.pow_mem_pow (hμ i) (d i)
  have h2 : (∏ i ∈ d.support, I ^ (t * d i)) = I ^ (t * d.degree) := by
    rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply, ← Finset.mul_sum]
  rwa [h2] at h1

/-- **FONTAINE'S FIRST-ORDER TAYLOR ESTIMATE** (Fontaine, *Il n'y a pas de variété
abélienne sur ℤ*, Invent. Math. 81 (1985), step 4 of Prop. 1.7, pp. 521–522).

If every partial derivative of `f` is `3` times another power series, then along a
perturbation `μ` drawn from `I ^ t` the series is linear to order `t + e + 1`,
where `3 ∈ I ^ e` and `e < 2t`.

The threshold is sharp for this argument: see the module docstring for why a plain
monomial expansion (which would need `t > e`) is not enough, and why no Hasse
derivative and no invertibility of `2` is needed all the same. -/
theorem adicEvalOfMem_taylor_mem (I : Ideal O) [IsAdicComplete I O]
    (f : MvPowerSeries σ R) (g : σ → MvPowerSeries σ R)
    (hfg : ∀ j, pderiv j f = 3 * g j)
    (e t n : ℕ) (he : (3 : O) ∈ I ^ e) (ht : e < 2 * t) (htn : t + e = n)
    (w μ : σ → O) (hw : ∀ i, w i ∈ I) (hμ : ∀ i, μ i ∈ I ^ t) :
    adicEvalOfMem I (w + μ) f - adicEvalOfMem I w f -
      3 * ∑ j, adicEvalOfMem I w (g j) * μ j ∈ I ^ (n + 1) := by
  classical
  -- `t ≥ 1`, hence `n ≥ 1`.
  have ht1 : 1 ≤ t := by omega
  have hn1 : 1 ≤ n := by omega
  have hμ1 : ∀ i, μ i ∈ I := fun i => by
    have h := Ideal.pow_le_pow_right (I := I) ht1 (hμ i)
    rwa [pow_one] at h
  have hwμ : ∀ i, (w + μ) i ∈ I := fun i => I.add_mem (hw i) (hμ1 i)
  set p : MvPolynomial σ R := truncTotal (n + 1) f with hp
  set F : MvPolynomial σ O := MvPolynomial.translate w p with hF
  -- Reduction to the truncation.
  have hA1 : adicEvalOfMem I (w + μ) f - MvPolynomial.aeval (w + μ) p ∈ I ^ (n + 1) := by
    rw [adicEvalOfMem_eq I hwμ]
    exact adicEval_sub_mem_pow I (w + μ) hwμ (n + 1) f
  have hA2 : adicEvalOfMem I w f - MvPolynomial.aeval w p ∈ I ^ (n + 1) := by
    rw [adicEvalOfMem_eq I hw]
    exact adicEval_sub_mem_pow I w hw (n + 1) f
  -- The two evaluations of the translate.
  have hev : MvPolynomial.eval μ F = MvPolynomial.aeval (w + μ) p :=
    MvPolynomial.eval_translate w μ p
  have hc0 : MvPolynomial.coeff 0 F = MvPolynomial.aeval w p := by
    rw [← MvPolynomial.constantCoeff_eq]
    exact MvPolynomial.constantCoeff_translate w p
  -- The derivative of the translate, and the divisibility it carries.
  have hpd : ∀ j, MvPolynomial.pderiv j F =
      MvPolynomial.translate w ((3 : R) • truncTotal n (g j)) := by
    intro j
    have h3 : (3 : MvPowerSeries σ R) * g j = (3 : R) • g j := by
      rw [Algebra.smul_def, map_ofNat]
    rw [hF, MvPolynomial.pderiv_translate, hp, pderiv_truncTotal, hfg j]
    congr 1
    rw [h3, map_smul]
  have hpd3 : ∀ (j : σ) (m : σ →₀ ℕ),
      MvPolynomial.coeff m (MvPolynomial.pderiv j F) =
        3 * MvPolynomial.coeff m (MvPolynomial.translate w (truncTotal n (g j))) := by
    intro j m
    rw [hpd j, map_smul, MvPolynomial.coeff_smul, Algebra.smul_def, map_ofNat]
  -- The linear coefficient is `3 · gⱼ(w)` up to `I ^ (e + n)`.
  have hlin : ∀ j : σ, MvPolynomial.coeff (Finsupp.single j 1) F * μ j -
      3 * adicEvalOfMem I w (g j) * μ j ∈ I ^ (n + 1) := by
    intro j
    have hcoe : MvPolynomial.coeff (Finsupp.single j 1) F =
        3 * MvPolynomial.aeval w (truncTotal n (g j)) := by
      have h := hpd3 j 0
      rw [MvPolynomial.coeff_pderiv, zero_add, Finsupp.coe_zero, Pi.zero_apply,
        Nat.cast_zero, zero_add, mul_one] at h
      rw [h, ← MvPolynomial.constantCoeff_eq, MvPolynomial.constantCoeff_translate]
    have hgap : adicEvalOfMem I w (g j) - MvPolynomial.aeval w (truncTotal n (g j)) ∈ I ^ n := by
      rw [adicEvalOfMem_eq I hw]
      exact adicEval_sub_mem_pow I w hw n (g j)
    have h3 : 3 * (MvPolynomial.aeval w (truncTotal n (g j)) - adicEvalOfMem I w (g j)) *
        μ j ∈ I ^ (e + n + t) := by
      have h1 : (3 : O) * (MvPolynomial.aeval w (truncTotal n (g j)) -
          adicEvalOfMem I w (g j)) ∈ I ^ e * I ^ n :=
        Ideal.mul_mem_mul he (by simpa using neg_mem hgap)
      rw [← pow_add] at h1
      have := Ideal.mul_mem_mul h1 (hμ j)
      rwa [← pow_add] at this
    have hle : n + 1 ≤ e + n + t := by omega
    refine Ideal.pow_le_pow_right hle ?_
    rw [hcoe]
    convert h3 using 1
    ring
  -- The degree-`≥ 2` part.
  have hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree →
      MvPolynomial.coeff d F * ∏ i ∈ d.support, μ i ^ d i ∈ I ^ (n + 1) := by
    intro d hd
    have hprod := prod_pow_mem_pow I t hμ d
    rcases lt_or_ge d.degree 3 with hlt | hge
    · -- total degree exactly `2`: the coefficient carries a factor of `3`.
      have hdeg2 : d.degree = 2 := by omega
      obtain ⟨j, hj⟩ : ∃ j, j ∈ d.support := by
        refine Finsupp.support_nonempty_iff.mpr ?_
        intro h0
        rw [h0] at hdeg2
        simp at hdeg2
      have hdjpos : 0 < d j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
      have hdjle : d j ≤ 2 := by
        have : d j ≤ d.degree := Finset.single_le_sum (f := fun i => d i)
          (fun _ _ => Nat.zero_le _) hj
        omega
      -- `d j • coeff d F` is divisible by `3`.
      set m : σ →₀ ℕ := d - Finsupp.single j 1 with hm
      have hmd : m + Finsupp.single j 1 = d := by
        rw [hm]
        refine Finsupp.ext fun k => ?_
        rcases eq_or_ne k j with rfl | hk
        · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [hk]
      have hmj : m j + 1 = d j := by
        rw [hm]
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      have hdj3 : MvPolynomial.coeff d F * (d j : O) ∈ I ^ e := by
        have h := hpd3 j m
        rw [MvPolynomial.coeff_pderiv, hmd] at h
        have hcast : ((m j : O) + 1) = (d j : O) := by
          rw [← hmj]; push_cast; ring
        rw [hcast] at h
        rw [h]
        exact Ideal.mul_mem_right _ _ he
      have hprod2 : ∏ i ∈ d.support, μ i ^ d i ∈ I ^ (2 * t) := by
        have := hprod
        rw [hdeg2, mul_comm t 2] at this
        exact this
      have hle : n + 1 ≤ e + 2 * t := by omega
      -- `(d j) · X ∈ I ^ (n+1)` and `3 · X ∈ I ^ (n+1)`; `d j ∈ {1, 2}` finishes.
      have hX1 : (d j : O) * (MvPolynomial.coeff d F * ∏ i ∈ d.support, μ i ^ d i) ∈
          I ^ (n + 1) := by
        refine Ideal.pow_le_pow_right hle ?_
        have := Ideal.mul_mem_mul hdj3 hprod2
        rw [← pow_add] at this
        convert this using 1
        ring
      have hX3 : (3 : O) * (MvPolynomial.coeff d F * ∏ i ∈ d.support, μ i ^ d i) ∈
          I ^ (n + 1) := by
        refine Ideal.pow_le_pow_right hle ?_
        have := Ideal.mul_mem_mul he (Ideal.mul_mem_left _ (MvPolynomial.coeff d F) hprod2)
        rw [← pow_add] at this
        convert this using 1
      have hdj12 : d j = 1 ∨ d j = 2 := by omega
      rcases hdj12 with hdjv | hdjv
      · rw [hdjv] at hX1
        simpa using hX1
      · rw [hdjv] at hX1
        have hrw : MvPolynomial.coeff d F * ∏ i ∈ d.support, μ i ^ d i =
            (3 : O) * (MvPolynomial.coeff d F * ∏ i ∈ d.support, μ i ^ d i) -
            (((2 : ℕ) : O)) * (MvPolynomial.coeff d F * ∏ i ∈ d.support, μ i ^ d i) := by
          push_cast
          ring
        rw [hrw]
        exact Ideal.sub_mem _ hX3 hX1
    · -- total degree `≥ 3`: the monomial in `μ` alone is small enough.
      have hle : n + 1 ≤ t * d.degree := by
        calc n + 1 = t + e + 1 := by omega
          _ ≤ t + 2 * t := by omega
          _ = t * 3 := by ring
          _ ≤ t * d.degree := Nat.mul_le_mul_left t hge
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle hprod)
  -- Assemble.
  have hsplit := MvPolynomial.eval_sub_linear_mem (I ^ (n + 1)) F μ hbig
  have hlinsum : ∑ j, MvPolynomial.coeff (Finsupp.single j 1) F * μ j -
      3 * ∑ j, adicEvalOfMem I w (g j) * μ j ∈ I ^ (n + 1) := by
    have : ∑ j, MvPolynomial.coeff (Finsupp.single j 1) F * μ j -
        3 * ∑ j, adicEvalOfMem I w (g j) * μ j =
        ∑ j, (MvPolynomial.coeff (Finsupp.single j 1) F * μ j -
          3 * adicEvalOfMem I w (g j) * μ j) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact Submodule.sum_mem _ fun j _ => hlin j
  have hgoal : adicEvalOfMem I (w + μ) f - adicEvalOfMem I w f -
      3 * ∑ j, adicEvalOfMem I w (g j) * μ j =
      (adicEvalOfMem I (w + μ) f - MvPolynomial.aeval (w + μ) p) -
      (adicEvalOfMem I w f - MvPolynomial.aeval w p) +
      (MvPolynomial.eval μ F - MvPolynomial.coeff 0 F -
        ∑ j, MvPolynomial.coeff (Finsupp.single j 1) F * μ j) +
      (∑ j, MvPolynomial.coeff (Finsupp.single j 1) F * μ j -
        3 * ∑ j, adicEvalOfMem I w (g j) * μ j) := by
    rw [hev, hc0]
    ring
  rw [hgoal]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.sub_mem _ hA1 hA2) hsplit) hlinsum

end Taylor

end MvPowerSeries

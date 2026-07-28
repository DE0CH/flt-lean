/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Evaluating a multivariate power series in an adically complete ring

Fontaine's proof that a finite flat group scheme over `𝒪_K` is rigid along the
`𝔪`-adic filtration (*Il n'y a pas de variété abélienne sur ℤ*, Invent. Math. 81
(1985), Prop. 1.7) presents the affine algebra as `𝒪_K[[X₁,…,X_h]]/(P₁,…,P_h)` and
then substitutes tuples from the maximal ideal of a complete discrete valuation
ring into the `P_i`.  This file supplies exactly that substitution, and it does so
**without any topology**: `MvPowerSeries σ R` maps to `MvPolynomial σ R ⧸ (X)^n`
by total truncation (`MvPowerSeries.truncTotalAlgHom`), `MvPolynomial.aeval w`
carries `(X)^n` into `I^n` as soon as every `w i` lies in `I`, and a compatible
family of maps into the `O ⧸ I^n` assembles into a map into `O` itself by
`IsAdicComplete.liftAlgHom`.  So the construction is a composite of three pieces
of mathlib and needs neither `MvPowerSeries.HasEval` nor a uniform structure on
`O` — which matters here, because the ring being substituted into is
`IntegralClosure 𝒪₃ᵥ E`, on which the development carries `IsAdicComplete` but no
topology.

## Main definitions

* `MvPowerSeries.pderiv` — the formal partial derivative of a multivariate power
  series, defined coefficientwise.  (The pin has derivatives for `Polynomial`,
  `MvPolynomial` and `PowerSeries`, but nothing for `MvPowerSeries`.)
* `MvPowerSeries.adicEval` — evaluation `MvPowerSeries σ R →ₐ[R] O` at a tuple
  `w : σ → O` all of whose entries lie in an ideal `I` for which `O` is
  `I`-adically complete.

## Main results

* `MvPowerSeries.mk_adicEval` — the defining property: modulo `I ^ n` the value of
  `adicEval` is the value of the degree-`< n` truncation.
* `MvPowerSeries.adicEval_X`, `MvPowerSeries.adicEval_coe` — the substitution does
  what it should on variables and on polynomials.
* `MvPowerSeries.adicEval_mem_pow` — a power series whose coefficients vanish below
  total degree `k` evaluates into `I ^ k`.  This is the estimate that makes the
  construction useful: it turns "congruent modulo a power of the variable ideal"
  into "congruent modulo a power of `I`".
-/

@[expose] public section

/-- Two elements of an `I`-adically complete ring that agree modulo every power of
`I` are equal. -/
theorem IsAdicComplete.eq_of_sub_mem_pow {O : Type*} [CommRing O] (I : Ideal O)
    [IsAdicComplete I O] {a b : O} (h : ∀ n, a - b ∈ I ^ n) : a = b :=
  sub_eq_zero.mp
    (IsHausdorff.haus (IsAdicComplete.toIsHausdorff : IsHausdorff I O) (a - b)
      fun n => SModEq.sub_mem.mpr (by simpa using h n))

/-- Monotonicity of ideal powers in the ideal. -/
theorem Ideal.pow_le_pow_left' {O : Type*} [CommRing O] {J K : Ideal O} (h : J ≤ K) :
    ∀ n : ℕ, J ^ n ≤ K ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact Ideal.mul_mono (Ideal.pow_le_pow_left' h n) h

namespace MvPowerSeries

section Pderiv

variable {σ : Type*} {R : Type*} [CommRing R]

/-- The formal partial derivative of a multivariate power series with respect to the
variable `j`, defined coefficientwise by `∂(X^n)/∂X_j = n_j · X^(n - e_j)`.

This is a definition only; it is here because Fontaine's argument needs to *state*
that the Jacobian matrix of a power-series presentation is `3` times an invertible
matrix, and this mathlib pin has `Polynomial.derivative`, `MvPolynomial.pderiv` and
`PowerSeries.derivative` but nothing for `MvPowerSeries`. -/
noncomputable def pderiv (j : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun n => (n j + 1) • coeff (n + Finsupp.single j 1) f

@[simp]
theorem coeff_pderiv (j : σ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (pderiv j f) = (n j + 1) • coeff (n + Finsupp.single j 1) f := by
  simp [pderiv, coeff_apply]

end Pderiv

section AdicEval

variable {σ : Type*} [Finite σ] {R : Type*} [CommRing R]
  {O : Type*} [CommRing O] [Algebra R O]

omit [Finite σ] in
/-- `MvPolynomial.aeval w` carries the `k`-th power of the ideal of variables into
`I ^ k`, as soon as every `w i` lies in `I`. -/
theorem aeval_mem_pow_of_mem_pow_idealOfVars {I : Ideal O} {w : σ → O}
    (hw : ∀ i, w i ∈ I) (k : ℕ) {a : MvPolynomial σ R}
    (ha : a ∈ (MvPolynomial.idealOfVars σ R) ^ k) :
    MvPolynomial.aeval w a ∈ I ^ k := by
  have h0 : Ideal.map ((MvPolynomial.aeval w : MvPolynomial σ R →ₐ[R] O) :
      MvPolynomial σ R →+* O) (MvPolynomial.idealOfVars σ R) ≤ I := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨i, rfl⟩ := hz
    simpa using hw i
  have h1 : Ideal.map ((MvPolynomial.aeval w : MvPolynomial σ R →ₐ[R] O) :
      MvPolynomial σ R →+* O) ((MvPolynomial.idealOfVars σ R) ^ k) ≤ I ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_le_pow_left' h0 k
  exact h1 (Ideal.mem_map_of_mem _ ha)

variable (I : Ideal O) (w : σ → O) (hw : ∀ i, w i ∈ I)

/-- Evaluation of a multivariate power series at `w` modulo `I ^ n`: only the
degree-`< n` part of the series contributes, so this is an honest finite sum. -/
noncomputable def adicEvalAux (n : ℕ) : MvPowerSeries σ R →ₐ[R] O ⧸ I ^ n :=
  (Ideal.Quotient.liftₐ ((MvPolynomial.idealOfVars σ R) ^ n)
      ((Ideal.Quotient.mkₐ R (I ^ n)).comp (MvPolynomial.aeval w))
      (fun a ha => by
        have h := aeval_mem_pow_of_mem_pow_idealOfVars (R := R) hw n ha
        show Ideal.Quotient.mk (I ^ n) (MvPolynomial.aeval w a) = 0
        rwa [Ideal.Quotient.eq_zero_iff_mem])).comp
    ((truncTotalAlgHom σ R n).restrictScalars R)

theorem adicEvalAux_apply (n : ℕ) (p : MvPowerSeries σ R) :
    adicEvalAux I w hw n p =
      Ideal.Quotient.mk (I ^ n) (MvPolynomial.aeval w (truncTotal n p)) := rfl

theorem adicEvalAux_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) hle)).comp
        (adicEvalAux I w hw n) = adicEvalAux I w hw m := by
  refine AlgHom.ext fun p => ?_
  have hsub : truncTotal n p - truncTotal m p ∈ (MvPolynomial.idealOfVars σ R) ^ m :=
    truncTotal_sub_truncTotal_mem_pow_idealOfVars hle (le_refl m) p
  have hmem : MvPolynomial.aeval w (truncTotal n p) -
      MvPolynomial.aeval w (truncTotal m p) ∈ I ^ m := by
    have := aeval_mem_pow_of_mem_pow_idealOfVars (R := R) hw m hsub
    simpa using this
  simp only [AlgHom.comp_apply, adicEvalAux_apply]
  rw [show (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := I) hle))
      (Ideal.Quotient.mk (I ^ n) (MvPolynomial.aeval w (truncTotal n p))) =
      Ideal.Quotient.mk (I ^ m) (MvPolynomial.aeval w (truncTotal n p)) from rfl,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hmem

variable [IsAdicComplete I O]

/-- **Evaluation of a multivariate power series at a tuple drawn from an ideal of an
adically complete ring.**  If `O` is `I`-adically complete and every `w i` lies in
`I`, then `f ↦ f(w)` is a well-defined `R`-algebra map `MvPowerSeries σ R →ₐ[R] O`.

No topology on `O` is used: the map is assembled by `IsAdicComplete.liftAlgHom`
from the truncated evaluations `adicEvalAux`. -/
noncomputable def adicEval : MvPowerSeries σ R →ₐ[R] O :=
  IsAdicComplete.liftAlgHom I (adicEvalAux I w hw) (adicEvalAux_compat I w hw)

@[simp]
theorem mk_adicEval (n : ℕ) (p : MvPowerSeries σ R) :
    Ideal.Quotient.mk (I ^ n) (adicEval I w hw p) =
      Ideal.Quotient.mk (I ^ n) (MvPolynomial.aeval w (truncTotal n p)) := by
  rw [adicEval, IsAdicComplete.mk_liftAlgHom I (adicEvalAux I w hw)
    (adicEvalAux_compat I w hw) n p, adicEvalAux_apply]

theorem adicEval_sub_mem_pow (n : ℕ) (p : MvPowerSeries σ R) :
    adicEval I w hw p - MvPolynomial.aeval w (truncTotal n p) ∈ I ^ n := by
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact mk_adicEval I w hw n p

@[simp]
theorem adicEval_coe (p : MvPolynomial σ R) :
    adicEval I w hw (p : MvPowerSeries σ R) = MvPolynomial.aeval w p := by
  refine IsAdicComplete.eq_of_sub_mem_pow I fun n => ?_
  set N := max n (p.totalDegree + 1) with hN
  have hlt : p.totalDegree < N := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)
  have h1 := adicEval_sub_mem_pow I w hw N (p : MvPowerSeries σ R)
  have h2 : truncTotal N (p : MvPowerSeries σ R) = p :=
    (truncTotal_coe_eq_self_iff (n := N) p hpos.ne').mpr hlt
  rw [h2] at h1
  exact Ideal.pow_le_pow_right (le_max_left _ _) h1

@[simp]
theorem adicEval_X (i : σ) : adicEval I w hw (X i : MvPowerSeries σ R) = w i := by
  have hX : ((MvPolynomial.X i : MvPolynomial σ R) : MvPowerSeries σ R) = X i := by simp
  rw [← hX, adicEval_coe]
  simp

/-- The estimate that makes `adicEval` useful: a power series all of whose
coefficients below total degree `k` vanish evaluates into `I ^ k`. -/
theorem adicEval_mem_pow (k : ℕ) (p : MvPowerSeries σ R)
    (hp : ∀ d : σ →₀ ℕ, d.degree < k → coeff d p = 0) :
    adicEval I w hw p ∈ I ^ k := by
  have htr : truncTotal k p = 0 := by
    ext d
    rw [MvPolynomial.coeff_zero, coeff_truncTotal_eq_ite]
    split
    · rename_i hd
      exact hp d hd
    · rfl
  have h1 := adicEval_sub_mem_pow I w hw k p
  rwa [htr, map_zero, sub_zero] at h1

end AdicEval

section AdicEvalOfMem

variable {σ : Type*} [Finite σ] {R : Type*} [CommRing R]
  {O : Type*} [CommRing O] [Algebra R O] (I : Ideal O) [IsAdicComplete I O]

open Classical in
/-- The **total** form of `adicEval`: evaluation at an arbitrary tuple `w`, which
falls back to evaluation at `0` when some `w i` fails to lie in `I`.

`adicEval` takes the membership hypothesis `hw : ∀ i, w i ∈ I` as an argument, so
it cannot be used to build a function of `w` alone.  Consumers that need such a
function — Fontaine's "equation function" `F` and "normalised Jacobian" `p`, whose
statements quantify over all `w` — use this instead, together with
`adicEvalOfMem_eq` to recover `adicEval` wherever the hypothesis is available. -/
noncomputable def adicEvalOfMem (w : σ → O) : MvPowerSeries σ R →ₐ[R] O :=
  if hw : ∀ i, w i ∈ I then adicEval I w hw else adicEval I 0 (fun _ => I.zero_mem)

theorem adicEvalOfMem_eq {w : σ → O} (hw : ∀ i, w i ∈ I) :
    (adicEvalOfMem I w : MvPowerSeries σ R →ₐ[R] O) = adicEval I w hw := by
  rw [adicEvalOfMem, dif_pos hw]

@[simp]
theorem adicEvalOfMem_X {w : σ → O} (hw : ∀ i, w i ∈ I) (i : σ) :
    adicEvalOfMem I w (X i : MvPowerSeries σ R) = w i := by
  rw [adicEvalOfMem_eq I hw, adicEval_X]

theorem adicEvalOfMem_mem_pow {w : σ → O} (hw : ∀ i, w i ∈ I) (k : ℕ)
    (p : MvPowerSeries σ R) (hp : ∀ d : σ →₀ ℕ, d.degree < k → coeff d p = 0) :
    adicEvalOfMem I w p ∈ I ^ k := by
  rw [adicEvalOfMem_eq I hw]
  exact adicEval_mem_pow I w hw k p hp

end AdicEvalOfMem

end MvPowerSeries

/-
Copyright (c) 2026 The Fermat project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.MvPowerSeries.VarsIdeal
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalRing.Module

/-!
# The Jacobian of a power-series presentation, and Fontaine's step 3

Fontaine's Prop. 1.7 (*Il n'y a pas de variété abélienne sur ℤ*, Invent. Math. 81
(1985)) presents a finite flat local algebra `B` over a complete discrete valuation
ring `𝒪` as `𝒪[[X₁,…,X_h]] ⧸ (P₁,…,P_h)` and then has to know that the Jacobian
matrix `(∂Pᵢ/∂Xⱼ)` dies modulo `p`.  That is the content of
`MvPowerSeries.alpha_pderiv_mem_span_of_flat` below, and it is the one place in the
argument where the *flatness* of `Ω[B⁄𝒪] ⊗ B/pB` over `B/pB` is spent.

## The argument

Write `V := σ → B`, `x j := α (X j)` and `d` for the universal derivation of `B`
over `𝒪`.  Everything rests on the

**CHAIN RULE** `d (α f) = ∑ⱼ α(∂f/∂Xⱼ) · d(xⱼ)`   (`kaehlerD_eq_jacToKaehler`)

which holds for *power* series, with no continuity or convergence hypothesis
anywhere: `α` is an arbitrary `𝒪`-algebra map.  What replaces convergence is that
`α` carries the ideal of variables into an ideal `I` of `B` with `Iⁿ · Ω = 0`, so
the tail of `f` beyond total degree `n + 1` and the tails of its derivatives are
both invisible.  For a *surjective* `α` onto a local ring one may take
`I = 𝔪_B` (`algHom_X_mem_maximalIdeal`).

The chain rule says two things at once.  The map `φ : V → Ω`, `eⱼ ↦ d(xⱼ)`
(`jacToKaehler`) is ONTO, and the rows of the Jacobian lie in its KERNEL.  The
reverse inclusion `ker φ ⊆ ⟨Jacobian rows⟩` is the derivation
`jacDerivation : B → V ⧸ ⟨rows⟩` sending `α f` to `(α(∂f/∂Xⱼ))ⱼ`, which is well
defined precisely because the Jacobian row of an element of `ker α` is a
combination of the rows of `P` (`jacRow_mem_jacSpan`).

So `Ω ≅ V ⧸ K` with `K = ⟨Jacobian rows⟩ ⊆ 𝔪·V` by minimality of the
presentation.  Reducing mod `p` and using that `Ω` is flat — hence, over the local
ring `B/pB`, free, hence projective — the surjection `V/pV ↠ B/pB ⊗ Ω` splits, so
`K/pV` is a direct summand of `V/pV` contained in `𝔪·(V/pV)`; Nakayama kills it.
Therefore `K ⊆ p·V`, which is the conclusion.

## Main results

* `MvPowerSeries.pderiv_X`, `pderiv_neg`, `pderiv_sub` — the missing scraps of the
  `MvPowerSeries.pderiv` API.
* `MvPowerSeries.kaehlerD_eq_jacToKaehler` — the chain rule.
* `MvPowerSeries.alpha_pderiv_mem_span_of_flat` — Fontaine's step 3 entry point.
-/

@[expose] public section

open scoped TensorProduct

namespace MvPowerSeries

variable {σ : Type*} {R : Type*} [CommRing R]

theorem add_single_eq_single_iff [DecidableEq σ] (i j : σ) (n : σ →₀ ℕ) :
    n + Finsupp.single j 1 = Finsupp.single i 1 ↔ (n = 0 ∧ i = j) := by
  constructor
  · intro h
    have hj := congrArg (fun t : σ →₀ ℕ => t j) h
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply] at hj
    have hij : i = j := by
      by_contra hne
      rw [if_neg hne] at hj
      omega
    refine ⟨?_, hij⟩
    subst hij
    rw [if_pos rfl] at hj
    have hn0 : n i = 0 := by omega
    ext k
    have hk := congrArg (fun t : σ →₀ ℕ => t k) h
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hk ⊢
    by_cases hki : i = k
    · subst hki; simpa using hn0
    · rw [if_neg hki] at hk; omega
  · rintro ⟨rfl, rfl⟩
    simp

/-- `∂Xᵢ/∂Xⱼ = δᵢⱼ`. -/
@[simp]
theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv j (X i : MvPowerSeries σ R) = if i = j then 1 else 0 := by
  ext n
  rw [coeff_pderiv, coeff_X]
  simp only [add_single_eq_single_iff]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg (by simp [hn]), if_neg hn]; simp
  · rw [if_neg hij, if_neg (by simp [hij]), map_zero]
    simp

@[simp]
theorem pderiv_neg (j : σ) (f : MvPowerSeries σ R) : pderiv j (-f) = -pderiv j f := by
  ext n; simp [coeff_pderiv]

theorem pderiv_sub (j : σ) (f g : MvPowerSeries σ R) :
    pderiv j (f - g) = pderiv j f - pderiv j g := by
  rw [sub_eq_add_neg, pderiv_add, pderiv_neg, ← sub_eq_add_neg]

section Jacobian

variable {σ : Type*} {𝒪 : Type*} [CommRing 𝒪] {B : Type*} [CommRing B] [Algebra 𝒪 B]

/-- The row of the Jacobian at `f`: the images under `α` of the partial derivatives. -/
noncomputable def jacRow (α : MvPowerSeries σ 𝒪 →ₐ[𝒪] B) (f : MvPowerSeries σ 𝒪) : σ → B :=
  fun j => α (pderiv j f)

variable (α : MvPowerSeries σ 𝒪 →ₐ[𝒪] B)

@[simp] theorem jacRow_apply (f : MvPowerSeries σ 𝒪) (j : σ) :
    jacRow α f j = α (pderiv j f) := rfl

theorem jacRow_add (f g : MvPowerSeries σ 𝒪) :
    jacRow α (f + g) = jacRow α f + jacRow α g := by
  funext j; simp [jacRow, pderiv_add]

theorem jacRow_mul (f g : MvPowerSeries σ 𝒪) :
    jacRow α (f * g) = α f • jacRow α g + α g • jacRow α f := by
  funext j; simp only [jacRow_apply, pderiv_mul, map_add, map_mul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, jacRow_apply]
  ring

theorem jacRow_algebraMap (c : 𝒪) :
    jacRow α (algebraMap 𝒪 (MvPowerSeries σ 𝒪) c) = 0 := by
  funext j
  simp [jacRow, show algebraMap 𝒪 (MvPowerSeries σ 𝒪) c = C c from rfl]

theorem jacRow_zero : jacRow α 0 = 0 := by funext j; simp [jacRow]

theorem jacRow_X [DecidableEq σ] (i : σ) : jacRow α (X i) = Pi.single i 1 := by
  funext j
  simp only [jacRow_apply, pderiv_X, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (fun hc => h hc.symm), map_zero]

variable {ι : Type*} (P : ι → MvPowerSeries σ 𝒪)

/-- The `B`-submodule of `σ → B` spanned by the rows of the Jacobian of `P`. -/
noncomputable def jacSpan : Submodule B (σ → B) :=
  Submodule.span B (Set.range fun i => jacRow α (P i))

/-- **THE JACOBIAN SPAN ABSORBS EVERY ELEMENT OF THE KERNEL.**  If `ker α` is
generated by the `P i` then the Jacobian row of any element of `ker α` lies in the
span of the rows of `P`: by Leibniz, `∂(a·f) = a ∂f + f ∂a`, and the second term
dies because `α f = 0`. -/
theorem jacRow_mem_jacSpan (hker : RingHom.ker α = Ideal.span (Set.range P))
    {f : MvPowerSeries σ 𝒪} (hf : f ∈ RingHom.ker α) :
    jacRow α f ∈ jacSpan α P := by
  rw [hker] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [jacRow_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [jacRow_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      have hx0 : α x = 0 := by
        have : x ∈ RingHom.ker α := by rw [hker]; exact hx
        simpa [RingHom.mem_ker] using this
      rw [smul_eq_mul, jacRow_mul, hx0, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ ih

theorem jacRow_sub (f g : MvPowerSeries σ 𝒪) :
    jacRow α (f - g) = jacRow α f - jacRow α g := by
  funext j; simp [jacRow, pderiv_sub]

variable (hsurj : Function.Surjective α)
  (hker : RingHom.ker α = Ideal.span (Set.range P))

omit hsurj in
include hker in
theorem jacRow_congr {f g : MvPowerSeries σ 𝒪} (h : α f = α g) :
    (Submodule.Quotient.mk (jacRow α f) : (σ → B) ⧸ jacSpan α P) =
      Submodule.Quotient.mk (jacRow α g) := by
  rw [Submodule.Quotient.eq, ← jacRow_sub]
  exact jacRow_mem_jacSpan α P hker (by simp [RingHom.mem_ker, map_sub, h])

/-- The `𝒪`-linear map `B → (σ → B) ⧸ jacSpan` sending `α f` to the Jacobian row of
`f`.  Well defined because the Jacobian row of an element of `ker α` lies in the
span of the rows of `P`. -/
noncomputable def jacLinearMap : B →ₗ[𝒪] ((σ → B) ⧸ jacSpan α P) where
  toFun := fun b => Submodule.Quotient.mk (jacRow α (Function.surjInv hsurj b))
  map_add' := by
    intro b c
    obtain ⟨f, rfl⟩ := hsurj b
    obtain ⟨g, rfl⟩ := hsurj c
    rw [jacRow_congr α P hker (Function.surjInv_eq hsurj (α f)),
      jacRow_congr α P hker (Function.surjInv_eq hsurj (α g)),
      jacRow_congr α P hker (by rw [Function.surjInv_eq hsurj, map_add] :
        α (Function.surjInv hsurj (α f + α g)) = α (f + g)),
      jacRow_add, Submodule.Quotient.mk_add]
  map_smul' := by
    intro c b
    obtain ⟨f, rfl⟩ := hsurj b
    rw [jacRow_congr α P hker (Function.surjInv_eq hsurj (α f)),
      jacRow_congr α P hker (by
        rw [Function.surjInv_eq hsurj, Algebra.smul_def, map_mul, AlgHom.commutes,
          ← Algebra.smul_def] :
        α (Function.surjInv hsurj (c • α f)) = α (algebraMap 𝒪 (MvPowerSeries σ 𝒪) c * f))]
    simp only [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    rw [jacRow_mul, jacRow_algebraMap, smul_zero, add_zero, AlgHom.commutes]
    congr 1
    exact algebraMap_smul B c (jacRow α f)

include hsurj hker in
@[simp] theorem jacLinearMap_apply (f : MvPowerSeries σ 𝒪) :
    jacLinearMap α P hsurj hker (α f) = Submodule.Quotient.mk (jacRow α f) :=
  jacRow_congr α P hker (Function.surjInv_eq hsurj (α f))

/-- The `𝒪`-derivation `B → (σ → B) ⧸ jacSpan` sending `α f` to the Jacobian row of
`f`. -/
noncomputable def jacDerivation : Derivation 𝒪 B ((σ → B) ⧸ jacSpan α P) where
  toLinearMap := jacLinearMap α P hsurj hker
  map_one_eq_zero' := by
    rw [show (1 : B) = α 1 from (map_one α).symm, jacLinearMap_apply,
      show (1 : MvPowerSeries σ 𝒪) = algebraMap 𝒪 _ 1 by simp, jacRow_algebraMap]
    rfl
  leibniz' := by
    intro b c
    obtain ⟨f, rfl⟩ := hsurj b
    obtain ⟨g, rfl⟩ := hsurj c
    rw [← map_mul α f g, jacLinearMap_apply, jacLinearMap_apply, jacLinearMap_apply,
      jacRow_mul, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_smul]

include hsurj hker in
@[simp] theorem jacDerivation_apply (f : MvPowerSeries σ 𝒪) :
    jacDerivation α P hsurj hker (α f) = Submodule.Quotient.mk (jacRow α f) :=
  jacLinearMap_apply α P hsurj hker f

section Fin

variable [Fintype σ] [DecidableEq σ]

/-- The map `(σ → B) → Ω[B⁄𝒪]` sending the `j`-th basis vector to `d(α Xⱼ)`. -/
noncomputable def jacToKaehler : (σ → B) →ₗ[B] Ω[B⁄𝒪] :=
  ∑ j : σ, (LinearMap.proj j : (σ → B) →ₗ[B] B).smulRight
    (KaehlerDifferential.D 𝒪 B (α (X j)))

omit [DecidableEq σ] in
theorem jacToKaehler_apply (v : σ → B) :
    jacToKaehler α v = ∑ j : σ, v j • KaehlerDifferential.D 𝒪 B (α (X j)) := by
  simp [jacToKaehler]

include hsurj hker in
/-- `ψ ∘ φ` is the quotient map: the derivation built out of the Jacobian rows is a
one-sided inverse of `v ↦ ∑ vⱼ d(α Xⱼ)`. -/
theorem jacDerivation_liftKaehlerDifferential_comp_jacToKaehler (v : σ → B) :
    (jacDerivation α P hsurj hker).liftKaehlerDifferential (jacToKaehler α v) =
      Submodule.Quotient.mk v := by
  rw [jacToKaehler_apply, map_sum]
  have hone : ∀ j : σ, (jacDerivation α P hsurj hker).liftKaehlerDifferential
      (KaehlerDifferential.D 𝒪 B (α (X j))) =
      Submodule.Quotient.mk (Pi.single j (1 : B)) := by
    intro j
    rw [Derivation.liftKaehlerDifferential_comp_D, jacDerivation_apply, jacRow_X]
  calc ∑ j : σ, (jacDerivation α P hsurj hker).liftKaehlerDifferential
        (v j • KaehlerDifferential.D 𝒪 B (α (X j)))
      = ∑ j : σ, (Submodule.Quotient.mk (Pi.single j (v j)) :
          (σ → B) ⧸ jacSpan α P) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hone j, ← Submodule.Quotient.mk_smul]
        congr 1
        funext k
        by_cases hk : j = k
        · subst hk; simp
        · simp [hk]
    _ = Submodule.Quotient.mk v := by
        conv_rhs => rw [← Finset.univ_sum_single v]
        exact (map_sum (jacSpan α P).mkQ (fun j => Pi.single j (v j)) Finset.univ).symm

omit [DecidableEq σ] in
theorem jacToKaehler_single (i : σ) [DecidableEq σ] :
    jacToKaehler α (Pi.single i (1 : B)) = KaehlerDifferential.D 𝒪 B (α (X i)) := by
  rw [jacToKaehler_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, Ne.symm hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

omit hsurj hker in
/-- **THE CHAIN RULE, POLYNOMIAL CASE.** -/
theorem kaehlerD_coe_eq (q : MvPolynomial σ 𝒪) :
    KaehlerDifferential.D 𝒪 B (α (q : MvPowerSeries σ 𝒪)) =
      jacToKaehler α (jacRow α (q : MvPowerSeries σ 𝒪)) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.coe_C,
        show (MvPowerSeries.C a : MvPowerSeries σ 𝒪) = algebraMap 𝒪 (MvPowerSeries σ 𝒪) a from rfl,
        jacRow_algebraMap, map_zero, AlgHom.commutes]
      exact (KaehlerDifferential.D 𝒪 B).map_algebraMap a
  | add p q hp hq =>
      rw [MvPolynomial.coe_add, map_add, map_add, jacRow_add, map_add, hp, hq]
  | mul_X p i hp =>
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, Derivation.leibniz,
        jacRow_mul, map_add, map_smul, map_smul, jacRow_X, jacToKaehler_single, hp]

/-- The tail of `f` beyond total degree `n` lies in the `n`-th power of the ideal of
variables, and so does the tail of each of its partial derivatives one degree lower. -/
theorem pderiv_tail_mem_varsIdeal_pow [Fintype σ] [LinearOrder σ] (n : ℕ)
    (f : MvPowerSeries σ 𝒪) (j : σ) :
    pderiv j (f - ((truncTotal (n + 1) f : MvPolynomial σ 𝒪) : MvPowerSeries σ 𝒪)) ∈
      (varsIdeal σ 𝒪) ^ n := by
  refine mem_varsIdeal_pow n _ fun d hd => ?_
  rw [coeff_pderiv, map_sub, MvPolynomial.coeff_coe,
    coeff_truncTotal _ (by rw [Finsupp.degree_add, Finsupp.degree_single]; omega), sub_self,
    smul_zero]

omit hsurj hker in
/-- **`d(𝔞^{k+1}) ⊆ 𝔞^k · Ω`** — the Leibniz rule, by induction on `k`. -/
theorem kaehlerD_pow_mem_smul_top (I : Ideal B) (k : ℕ) (b : B) (hb : b ∈ I ^ (k + 1)) :
    KaehlerDifferential.D 𝒪 B b ∈ (I ^ k) • (⊤ : Submodule B (Ω[B⁄𝒪])) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
      rw [pow_succ] at hb
      refine Submodule.mul_induction_on hb ?_ ?_
      · intro x hx y hy
        rw [Derivation.leibniz]
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.smul_mem_smul hx Submodule.mem_top
        · have h1 : KaehlerDifferential.D 𝒪 B x ∈ (I ^ k) • (⊤ : Submodule B (Ω[B⁄𝒪])) :=
            ih x hx
          have h2 : y • KaehlerDifferential.D 𝒪 B x ∈ I • ((I ^ k) • (⊤ : Submodule B _)) :=
            Submodule.smul_mem_smul hy h1
          rwa [← mul_smul, ← pow_succ'] at h2
      · intro x y ihx ihy
        rw [map_add]; exact Submodule.add_mem _ ihx ihy

variable (I : Ideal B) (n : ℕ)

omit hsurj hker in
/-- **THE CHAIN RULE FOR POWER SERIES.**  `d(α f) = ∑ⱼ α(∂f/∂Xⱼ) · d(α Xⱼ)`.

There is no convergence hypothesis: the tail of `f` beyond total degree `n + 1` maps
into `I ^ (n + 1)`, and `I ^ n` already annihilates `Ω`, so both the tail of `f` and
the tails of its derivatives are invisible. -/
theorem kaehlerD_eq_jacToKaehler [Fintype σ] [LinearOrder σ]
    (hX : ∀ i, α (X i) ∈ I) (hIn : (I ^ n) • (⊤ : Submodule B (Ω[B⁄𝒪])) = ⊥)
    (f : MvPowerSeries σ 𝒪) :
    KaehlerDifferential.D 𝒪 B (α f) = jacToKaehler α (jacRow α f) := by
  classical
  set q : MvPolynomial σ 𝒪 := truncTotal (n + 1) f with hq
  set g : MvPowerSeries σ 𝒪 := f - (q : MvPowerSeries σ 𝒪) with hg
  have hgmem : g ∈ (varsIdeal σ 𝒪) ^ (n + 1) := by
    refine mem_varsIdeal_pow (n + 1) _ fun d hd => ?_
    rw [hg, map_sub, MvPolynomial.coeff_coe, hq, coeff_truncTotal _ hd, sub_self]
  have hαg : α g ∈ I ^ (n + 1) := map_mem_pow_of_mem_varsIdeal_pow α I hX (n + 1) hgmem
  -- the tail contributes nothing to the left-hand side
  have hleft : KaehlerDifferential.D 𝒪 B (α g) = 0 := by
    have := kaehlerD_pow_mem_smul_top (𝒪 := 𝒪) I n (α g) hαg
    rwa [hIn, Submodule.mem_bot] at this
  -- nor to the right-hand side
  have hright : jacToKaehler α (jacRow α g) = 0 := by
    rw [jacToKaehler_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : pderiv j g ∈ (varsIdeal σ 𝒪) ^ n := pderiv_tail_mem_varsIdeal_pow n f j
    have h2 : α (pderiv j g) ∈ I ^ n := map_mem_pow_of_mem_varsIdeal_pow α I hX n h1
    have h4 : α (pderiv j g) • (KaehlerDifferential.D 𝒪 B (α (X j)))
        ∈ (I ^ n) • (⊤ : Submodule B (Ω[B⁄𝒪])) := Submodule.smul_mem_smul h2 Submodule.mem_top
    rwa [hIn, Submodule.mem_bot] at h4
  have hfq : f = (q : MvPowerSeries σ 𝒪) + g := by rw [hg]; ring
  rw [hfq, map_add, map_add, jacRow_add, map_add, hleft, hright, add_zero, add_zero,
    kaehlerD_coe_eq α q]

end Fin

end Jacobian

section Main

variable {σ : Type*} [Fintype σ] [LinearOrder σ]
variable {𝒪 : Type*} [CommRing 𝒪] {B : Type*} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]

/-- A surjective algebra map out of a power series ring carries the variables into the
maximal ideal: `1 - f·Xᵢ` is a unit for every `f`, so `α Xᵢ` lies in the Jacobson
radical, which for a local ring is the maximal ideal. -/
theorem algHom_X_mem_maximalIdeal (α : MvPowerSeries σ 𝒪 →ₐ[𝒪] B)
    (hsurj : Function.Surjective α) (i : σ) :
    α (X i) ∈ IsLocalRing.maximalIdeal B := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  obtain ⟨g, hg⟩ := hsurj (-(↑u⁻¹ : B))
  have hunit : IsUnit ((X i : MvPowerSeries σ 𝒪) * g + 1) := by
    rw [isUnit_iff_constantCoeff]
    simpa using isUnit_one
  have h2 := hunit.map α
  rw [map_add, map_mul, map_one, hg, ← hu] at h2
  rw [mul_neg, Units.mul_inv, neg_add_cancel] at h2
  exact zero_ne_one (isUnit_zero_iff.mp h2)

/-- A vector all of whose entries lie in `I` lies in `I · (σ → B)`. -/
theorem mem_ideal_smul_top_of_forall {C : Type*} [CommRing C] (I : Ideal C)
    (v : σ → C) (hv : ∀ j, v j ∈ I) : v ∈ I • (⊤ : Submodule C (σ → C)) := by
  classical
  have hv' : v = ∑ j : σ, v j • Pi.single j (1 : C) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun j _ => ?_
    funext k
    by_cases hk : j = k
    · subst hk; simp
    · simp [hk]
  rw [hv']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hv j) Submodule.mem_top

end Main

end MvPowerSeries

namespace MvPowerSeries

section MainThm

variable {σ : Type*} [Fintype σ] [LinearOrder σ]
variable {𝒪 : Type*} [CommRing 𝒪] {B : Type*} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]

open scoped TensorProduct

/-- **THE JACOBIAN OF A MINIMAL POWER-SERIES PRESENTATION DIES MODULO `p`.** -/
theorem alpha_pderiv_mem_span_of_flat
    (α : MvPowerSeries σ 𝒪 →ₐ[𝒪] B) (hsurj : Function.Surjective α)
    {ι : Type*} (P : ι → MvPowerSeries σ 𝒪)
    (hker : RingHom.ker α = Ideal.span (Set.range P))
    (p : B) (hpm : p ∈ IsLocalRing.maximalIdeal B)
    (hΩ : ∀ ω : Ω[B⁄𝒪], p • ω = 0)
    (n : ℕ) (hnil : IsLocalRing.maximalIdeal B ^ n ≤ Ideal.span {p})
    (hmin : ∀ i j, α (pderiv j (P i)) ∈ IsLocalRing.maximalIdeal B)
    (hflat : Module.Flat (B ⧸ Ideal.span {p}) ((B ⧸ Ideal.span {p}) ⊗[B] Ω[B⁄𝒪]))
    (i : ι) (j : σ) :
    α (pderiv j (P i)) ∈ Ideal.span {p} := by
  classical
  set 𝔪 : Ideal B := IsLocalRing.maximalIdeal B with h𝔪
  set Ip : Ideal B := Ideal.span {p} with hIp
  have hX : ∀ i, α (X i) ∈ 𝔪 := algHom_X_mem_maximalIdeal α hsurj
  -- `(p)` annihilates `Ω`
  have hpspan : Ip • (⊤ : Submodule B (Ω[B⁄𝒪])) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr fun r hr ω _ => ?_) bot_le
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [Submodule.mem_bot, mul_smul, hΩ ω, smul_zero]
  have hIn : (𝔪 ^ n) • (⊤ : Submodule B (Ω[B⁄𝒪])) = ⊥ :=
    le_antisymm ((Submodule.smul_mono_left hnil).trans hpspan.le) bot_le
  -- the chain rule
  have hchain : ∀ f, KaehlerDifferential.D 𝒪 B (α f) = jacToKaehler α (jacRow α f) :=
    kaehlerD_eq_jacToKaehler α 𝔪 n hX hIn
  -- `v ↦ ∑ vⱼ d(α Xⱼ)` is onto
  have hφsurj : Function.Surjective (jacToKaehler α) := by
    rw [← LinearMap.range_eq_top]
    refine top_le_iff.mp ?_
    rw [← KaehlerDifferential.span_range_derivation]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    obtain ⟨f, rfl⟩ := hsurj b
    exact ⟨jacRow α f, (hchain f).symm⟩
  -- its kernel is inside the Jacobian span
  have hkerle : LinearMap.ker (jacToKaehler α) ≤ jacSpan α P := by
    intro v hv
    have := jacDerivation_liftKaehlerDifferential_comp_jacToKaehler α P hsurj hker v
    rw [LinearMap.mem_ker.mp hv, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero _).mp this.symm
  -- and the Jacobian span has all entries in `𝔪`
  have hentries : ∀ v ∈ jacSpan α P, ∀ k, v k ∈ 𝔪 := by
    intro v hv
    refine Submodule.span_induction (p := fun w _ => ∀ k, w k ∈ 𝔪) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i', rfl⟩ k; exact hmin i' k
    · intro k; simp
    · intro x y _ _ ihx ihy k; exact Ideal.add_mem _ (ihx k) (ihy k)
    · intro a x _ ih k; exact Ideal.mul_mem_left _ _ (ih k)
  -- the rows of `P` are in the kernel
  have hPker : ∀ i', jacRow α (P i') ∈ LinearMap.ker (jacToKaehler α) := by
    intro i'
    have hαP : α (P i') = 0 := by
      have : P i' ∈ RingHom.ker α := by rw [hker]; exact Ideal.subset_span ⟨i', rfl⟩
      simpa [RingHom.mem_ker] using this
    rw [LinearMap.mem_ker, ← hchain, hαP, map_zero]
  -- pass to `B̄ = B ⧸ (p)`
  have hIptop : Ip ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpm))
  haveI : Nontrivial (B ⧸ Ip) := Ideal.Quotient.nontrivial_iff.mpr hIptop
  haveI : IsLocalRing (B ⧸ Ip) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Ip) Ideal.Quotient.mk_surjective
  set mk : B →+* B ⧸ Ip := Ideal.Quotient.mk Ip with hmk
  set 𝔪q : Ideal (B ⧸ Ip) := IsLocalRing.maximalIdeal (B ⧸ Ip) with h𝔪q
  have hmkm : ∀ x ∈ 𝔪, mk x ∈ 𝔪q := by
    intro x hx
    rw [h𝔪q, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ Ip)
    have h1 : mk (x * y) = 1 := by
      rw [map_mul, ← hu, hy]; exact u.mul_inv
    have h2 : x * y - 1 ∈ Ip := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
    have h3 : (1 : B) ∈ 𝔪 := by
      have := Ideal.sub_mem 𝔪 (Ideal.mul_mem_right y 𝔪 hx)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpm) h2)
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
  set φ' : (σ → B ⧸ Ip) →ₗ[B ⧸ Ip] ((B ⧸ Ip) ⊗[B] Ω[B⁄𝒪]) :=
    ∑ k : σ, (LinearMap.proj k : (σ → B ⧸ Ip) →ₗ[B ⧸ Ip] (B ⧸ Ip)).smulRight
      ((1 : B ⧸ Ip) ⊗ₜ[B] KaehlerDifferential.D 𝒪 B (α (X k))) with hφ'
  have hφ'apply : ∀ w : σ → B ⧸ Ip, φ' w =
      ∑ k : σ, w k • ((1 : B ⧸ Ip) ⊗ₜ[B] KaehlerDifferential.D 𝒪 B (α (X k))) := by
    intro w; simp [hφ']
  have hπ : ∀ v : σ → B, φ' (fun k => mk (v k)) =
      (1 : B ⧸ Ip) ⊗ₜ[B] (jacToKaehler α v) := by
    intro v
    rw [hφ'apply, jacToKaehler_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul]
    congr 1
    show mk (v k) = v k • (1 : B ⧸ Ip)
    rw [Algebra.smul_def, mul_one, hmk, Ideal.Quotient.algebraMap_eq]
  have hsmul1 : ∀ b : B, b • (1 : B ⧸ Ip) = mk b := by
    intro b; rw [Algebra.smul_def, mul_one, hmk, Ideal.Quotient.algebraMap_eq]
  -- `φ'` is onto
  have hφ'surj : Function.Surjective φ' := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul b ω =>
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
        obtain ⟨v, rfl⟩ := hφsurj ω
        refine ⟨fun k => mk (c * v k), ?_⟩
        rw [hπ (fun k => c * v k),
          show jacToKaehler α (fun k => c * v k) = c • jacToKaehler α v from
            (map_smul (jacToKaehler α) c v), ← TensorProduct.smul_tmul, hsmul1]
    | add x y hx hy =>
        obtain ⟨w, rfl⟩ := hx
        obtain ⟨w', rfl⟩ := hy
        exact ⟨w + w', map_add _ _ _⟩
  -- and its kernel has all entries in the maximal ideal
  have hkerφ' : ∀ w ∈ LinearMap.ker φ', ∀ k, w k ∈ 𝔪q := by
    intro w hw k
    choose v hv using fun k => Ideal.Quotient.mk_surjective (I := Ip) (w k)
    have hw' : w = fun k => mk (v k) := by funext k; exact (hv k).symm
    rw [hw', LinearMap.mem_ker, hπ] at hw
    have hz : jacToKaehler α v = 0 := by
      have he := TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := Ω[B⁄𝒪]) Ip
        (jacToKaehler α v)
      rw [hw, map_zero] at he
      have h5 := (Submodule.Quotient.mk_eq_zero _).mp he.symm
      rwa [hpspan, Submodule.mem_bot] at h5
    rw [hw']
    exact hmkm _ (hentries v (hkerle hz) k)
  -- Nakayama
  haveI : Module.Finite (B ⧸ Ip) ((B ⧸ Ip) ⊗[B] Ω[B⁄𝒪]) := Module.Finite.of_surjective φ' hφ'surj
  haveI := hflat
  haveI : Module.Free (B ⧸ Ip) ((B ⧸ Ip) ⊗[B] Ω[B⁄𝒪]) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ' LinearMap.id
    hφ'surj
  have hs' : ∀ x, φ' (s x) = x := fun x => LinearMap.ext_iff.mp hs x
  set r : (σ → B ⧸ Ip) →ₗ[B ⧸ Ip] (σ → B ⧸ Ip) := LinearMap.id - s.comp φ' with hr
  have hrk : ∀ w, φ' (r w) = 0 := by
    intro w
    simp only [hr, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply, map_sub,
      hs' (φ' w), sub_self]
  have hrid : ∀ w ∈ LinearMap.ker φ', r w = w := by
    intro w hw
    simp only [hr, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hw, map_zero, sub_zero]
  have hNrange : LinearMap.ker φ' = Submodule.map r ⊤ := by
    refine le_antisymm (fun w hw => ⟨w, Submodule.mem_top, hrid w hw⟩) ?_
    rintro _ ⟨w, -, rfl⟩
    exact hrk w
  have hNfg : (LinearMap.ker φ').FG := by
    rw [hNrange]
    exact Submodule.FG.map r (Module.Finite.fg_top)
  have hNle : LinearMap.ker φ' ≤ 𝔪q • LinearMap.ker φ' := by
    intro w hw
    have h6 : w ∈ 𝔪q • (⊤ : Submodule (B ⧸ Ip) (σ → B ⧸ Ip)) :=
      mem_ideal_smul_top_of_forall 𝔪q w (hkerφ' w hw)
    have h7 : r w ∈ Submodule.map r (𝔪q • (⊤ : Submodule (B ⧸ Ip) (σ → B ⧸ Ip))) :=
      ⟨w, h6, rfl⟩
    rw [Submodule.map_smul'', ← hNrange] at h7
    rwa [hrid w hw] at h7
  have hNbot : LinearMap.ker φ' = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔪q _ hNfg hNle
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
  -- conclude
  have hrowker : (fun k => mk (jacRow α (P i) k)) ∈ LinearMap.ker φ' := by
    rw [LinearMap.mem_ker, hπ, LinearMap.mem_ker.mp (hPker i), TensorProduct.tmul_zero]
  rw [hNbot, Submodule.mem_bot] at hrowker
  have hfin := congrFun hrowker j
  rw [hmk] at hfin
  simpa [Ideal.Quotient.eq_zero_iff_mem] using hfin

end MainThm

end MvPowerSeries

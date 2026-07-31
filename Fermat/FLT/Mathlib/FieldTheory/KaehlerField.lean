/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The derivation criterion for `p`-th powers in a finitely generated extension

Let `k` be a **perfect** field of characteristic `p` and let `K / k` be a finitely generated
field extension.  This file proves the classical criterion

  `KaehlerDifferential.D k K x = 0  ↔  ∃ y : K, y ^ p = x`,

i.e. the kernel of `d : K → Ω[K⁄k]` is exactly `K ^ p`.

## Main results

* `FLT.exists_kaehlerBasis_of_isTranscendenceBasis`: if `t : ι → K` is a *separating*
  transcendence basis (so that `K` is separable over `k(t)`) then `Ω[K⁄k]` is free over `K`
  on `{ d tᵢ }`.
* `FLT.exists_partialDerivation_of_isTranscendenceBasis`: the dual family of partial
  derivations `∂ᵢ` with `∂ᵢ tⱼ = δᵢⱼ`.
* `FLT.D_eq_zero_iff_exists_pow`: the headline criterion.
* `FLT.D_algebraMap_eq_zero_iff_exists_pow`: the same criterion for an element of an
  integrally closed subring `R` with `Frac R = K` — the `p`-th root is then in `R`.  This is
  the step from a function field down to a local ring (a stalk of a smooth variety).

## Implementation notes

The freeness statement is obtained by *composing formal étaleness*: writing `A = k[tᵢ]` for the
polynomial algebra on a separating transcendence basis, `A → K` factors as a localisation
`A → k(t)` followed by a separable algebraic extension `k(t) → K`, both of which are formally
étale, so `K ⊗[A] Ω[A⁄k] ≃ Ω[K⁄k]` by
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, and `Ω[A⁄k]` is free on the `d tᵢ` by
`KaehlerDifferential.mvPolynomialBasis`.

The kernel computation then never needs a `p`-basis of `K` over `K ^ p`: the partial derivations
`∂ᵢ` *by themselves* force the tower

  `K ^ p ⊆ K ^ p (t₁) ⊆ ⋯ ⊆ K ^ p (t₁,…,t_d) = K`

to have all its steps of degree exactly `p`, because `∂ⱼ` kills `K ^ p (t₁,…,t_{j-1})` while
`∂ⱼ tⱼ = 1`, so that `tⱼ` cannot already lie in that field.  Peeling one step is
`FLT.mem_of_derivation_step`; iterating it is `FLT.mem_of_forall_derivation_eq_zero`.  The
identification `K ^ p (t) = K` is `FLT.sup_pthPowers_adjoin_eq_top`: that field is at once
separable (it contains `k(t)`) and purely inseparable (it contains every `p`-th power) in `K`.
-/

@[expose] public section

open Polynomial

namespace FLT

/-- The characteristic descends along a ring homomorphism out of a division ring. -/
theorem charP_of_ringHom {R A : Type*} [DivisionRing R] [Semiring A] [Nontrivial A]
    (f : R →+* A) (p : ℕ) [CharP A p] : CharP R p :=
  ⟨fun n => by
    rw [← map_eq_zero_iff f f.injective, map_natCast, CharP.cast_eq_zero_iff A p n]⟩

section Derivation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A derivation kills `p`-th powers in characteristic `p`. -/
theorem derivation_map_pow_char {R A M : Type*} [CommRing R] [CommRing A] [AddCommGroup M]
    [Algebra R A] [Module A M] [Module R M] (p : ℕ) [CharP A p] (D : Derivation R A M) (a : A) :
    D (a ^ p) = 0 := by
  rw [D.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero, zero_smul]

/-- The kernel of a `k`-derivation of `K`, as a subfield. -/
def derivationKerSubfield (D : Derivation k K K) : Subfield K where
  carrier := {x : K | D x = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [D.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  zero_mem' := map_zero D
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_neg, ha, neg_zero]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rcases eq_or_ne a 0 with rfl | h
    · simp
    · have h1 : D (a * a⁻¹) = 0 := by rw [mul_inv_cancel₀ h]; exact D.map_one_eq_zero
      rw [D.leibniz, ha, smul_zero, add_zero, smul_eq_mul, mul_eq_zero] at h1
      exact h1.resolve_left h

/-- The kernel of a `k`-derivation of `K`, as an intermediate field of `K / k`. -/
def derivationKer (D : Derivation k K K) : IntermediateField k K :=
  (derivationKerSubfield D).toIntermediateField fun x => D.map_algebraMap x

@[simp]
theorem mem_derivationKer {D : Derivation k K K} {x : K} : x ∈ derivationKer D ↔ D x = 0 :=
  Iff.rfl

/-- A `k`-derivation of `K` that vanishes on an intermediate field `M` is an `M`-derivation. -/
def derivationOver (M : IntermediateField k K) (D : Derivation k K K)
    (hDM : ∀ y ∈ M, D y = 0) : Derivation M K K where
  toLinearMap :=
    { toFun := D
      map_add' := map_add D
      map_smul' := by
        intro m x
        show D ((m : K) * x) = (m : K) * D x
        rw [D.leibniz, hDM m m.2, smul_zero, add_zero, smul_eq_mul] }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

@[simp]
theorem derivationOver_apply (M : IntermediateField k K) (D : Derivation k K K)
    (hDM : ∀ y ∈ M, D y = 0) (x : K) : derivationOver M D hDM x = D x := rfl

end Derivation

section PthPowers

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- The subfield of `p`-th powers of `K`. -/
def pthPowersSubfield (p : ℕ) [ExpChar K p] : Subfield K where
  carrier := Set.range (frobenius K p)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, map_neg _ _⟩
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, by simp [frobenius_def]⟩

/-- The subfield `K ^ p` of `p`-th powers, as an intermediate field of `K / k`.  This uses that
`k` is perfect, so that `k = k ^ p ⊆ K ^ p`. -/
def pthPowers (p : ℕ) [ExpChar K p] [ExpChar k p] [PerfectField k] : IntermediateField k K :=
  (pthPowersSubfield K p).toIntermediateField fun x => by
    obtain ⟨y, hy⟩ := surjective_frobenius k p x
    exact ⟨algebraMap k K y, by simp [frobenius_def, ← hy, map_pow]⟩

variable {k K}

@[simp]
theorem mem_pthPowers {p : ℕ} [ExpChar K p] [ExpChar k p] [PerfectField k] {x : K} :
    x ∈ pthPowers k K p ↔ ∃ y : K, y ^ p = x := by
  show x ∈ Set.range (frobenius K p) ↔ _
  simp [frobenius_def]

theorem coe_pthPowers (p : ℕ) [ExpChar K p] [ExpChar k p] [PerfectField k] :
    (pthPowers k K p : Set K) = Set.range (frobenius K p) := rfl

end PthPowers

section Descent

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **One step of the descent.**  Let `M` be an intermediate field of `K / k` and `a : K` with
`a ^ p ∈ M`.  If `D` is a `k`-derivation of `K` vanishing on `M` with `D a = 1`, then any
element of `M(a)` killed by `D` already lies in `M`.

The hypothesis `D a = 1` is exactly what forces `[M(a) : M] = p`; no `p`-basis input is
needed. -/
theorem mem_of_derivation_step {p : ℕ} (hp : p.Prime) [CharP K p]
    (M : IntermediateField k K) {a : K} (ha : a ^ p ∈ M)
    (D : Derivation k K K) (hDM : ∀ y ∈ M, D y = 0) (hDa : D a = 1)
    {x : K} (hx : x ∈ M ⊔ IntermediateField.adjoin k {a}) (hDx : D x = 0) : x ∈ M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : ExpChar K p := .prime hp
  haveI : CharP M p := charP_of_ringHom (algebraMap M K) p
  -- `a ∉ M`, since `D` kills `M` but `D a = 1 ≠ 0`.
  have haM : a ∉ M := fun h => one_ne_zero (α := K) (hDa ▸ hDM a h)
  set b : M := ⟨a ^ p, ha⟩ with hb
  -- `X ^ p - C b` is irreducible over `M`: `b` is not a `p`-th power there.
  have hnpow : ∀ c : M, c ^ p ≠ b := by
    intro c hc
    apply haM
    have hcp : ((c : K)) ^ p = a ^ p := by
      have := congrArg (fun z : M => (z : K)) hc
      simpa [hb] using this
    have hz : ((c : K) - a) ^ p = 0 := by rw [sub_pow_char, hcp, sub_self]
    have hca : (c : K) = a := sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp hz)
    exact hca ▸ c.2
  have hirr : Irreducible (X ^ p - C b) := X_pow_sub_C_irreducible_of_prime hp hnpow
  have hmonic : (X ^ p - C b : M[X]).Monic := monic_X_pow_sub_C _ hp.ne_zero
  have haeval : (aeval a) (X ^ p - C b : M[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hb]
    simp
  have hmin : (X ^ p - C b : M[X]) = minpoly M a :=
    minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  have hint : IsIntegral M a := ⟨X ^ p - C b, hmonic, haeval⟩
  have hdeg : (minpoly M a).natDegree = p := by
    rw [← hmin, natDegree_X_pow_sub_C]
  -- rewrite the membership as `x = aeval a f`
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.mem_restrictScalars,
    ← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx
  obtain ⟨f, rfl⟩ := hx
  -- reduce `f` modulo the minimal polynomial
  have hgm : (minpoly M a).Monic := minpoly.monic hint
  have hfe : (aeval a) (f %ₘ minpoly M a) = (aeval a) f := by
    conv_rhs => rw [← modByMonic_add_div f (minpoly M a)]
    simp [minpoly.aeval]
  have hf'deg : (f %ₘ minpoly M a).natDegree < p := by
    have h1 : (f %ₘ minpoly M a).degree < (minpoly M a).degree := degree_modByMonic_lt f hgm
    rcases eq_or_ne (f %ₘ minpoly M a) 0 with hz | hz
    · simp [hz, hp.pos]
    · have := natDegree_lt_natDegree hz h1
      omega
  -- differentiate
  have hD' : (aeval a) (derivative (f %ₘ minpoly M a)) = 0 := by
    have h2 := (derivationOver M D hDM).map_aeval (f %ₘ minpoly M a) a
    rw [derivationOver_apply, derivationOver_apply, hfe, hDx, hDa, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hderiv : derivative (f %ₘ minpoly M a) = 0 := by
    by_contra hne
    have hdvd : minpoly M a ∣ derivative (f %ₘ minpoly M a) := minpoly.dvd M a hD'
    have h1 : (minpoly M a).natDegree ≤ (derivative (f %ₘ minpoly M a)).natDegree :=
      natDegree_le_of_dvd hdvd hne
    have h2 : (derivative (f %ₘ minpoly M a)).natDegree ≤ (f %ₘ minpoly M a).natDegree - 1 :=
      natDegree_derivative_le _
    omega
  -- a polynomial with zero derivative and degree `< p` is constant
  have hconst : (f %ₘ minpoly M a) = C ((f %ₘ minpoly M a).coeff 0) := by
    refine Polynomial.ext fun n => ?_
    rcases n with _ | m
    · simp
    · rw [coeff_C]
      simp only [Nat.succ_ne_zero, if_false]
      have hd := congrArg (fun q : M[X] => q.coeff m) hderiv
      simp only [coeff_derivative, coeff_zero] at hd
      rcases mul_eq_zero.mp hd with h | h
      · exact h
      · have hcast : ((m + 1 : ℕ) : M) = 0 := by push_cast; exact h
        have hdvd : p ∣ (m + 1) := (CharP.cast_eq_zero_iff M p (m + 1)).mp hcast
        have hle : p ≤ m + 1 := Nat.le_of_dvd (Nat.succ_pos m) hdvd
        exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hf'deg hle)
  rw [← hfe, hconst, aeval_C]
  exact ((f %ₘ minpoly M a).coeff 0).2

/-- The intermediate field generated by `M` together with a list of elements. -/
def chainField (M : IntermediateField k K) (l : List K) : IntermediateField k K :=
  M ⊔ IntermediateField.adjoin k {x : K | x ∈ l}

theorem le_chainField (M : IntermediateField k K) (l : List K) : M ≤ chainField M l := le_sup_left

theorem chainField_nil (M : IntermediateField k K) : chainField M [] = M := by
  have : {x : K | x ∈ ([] : List K)} = (∅ : Set K) := by ext y; simp
  rw [chainField, this, IntermediateField.adjoin_empty, sup_bot_eq]

theorem chainField_cons (M : IntermediateField k K) (a : K) (l : List K) :
    chainField M (a :: l) = chainField M l ⊔ IntermediateField.adjoin k {a} := by
  have hset : {x : K | x ∈ a :: l} = {a} ∪ {x : K | x ∈ l} := by ext y; simp
  rw [chainField, chainField, hset, IntermediateField.adjoin_union,
    sup_comm (IntermediateField.adjoin k {a}), ← sup_assoc]

/-- **The descent.**  If `M` contains every `p`-th power and the elements of `l` carry a dual
family of derivations vanishing on `M`, then an element of `M(l)` killed by all of them lies
in `M`. -/
theorem mem_of_forall_derivation_eq_zero [DecidableEq K] {p : ℕ} (hp : p.Prime) [CharP K p]
    (M : IntermediateField k K) (hM : ∀ y : K, y ^ p ∈ M) (part : K → Derivation k K K) :
    ∀ l : List K, l.Nodup →
      (∀ a ∈ l, ∀ y ∈ M, part a y = 0) →
      (∀ a ∈ l, ∀ b ∈ l, part a b = if b = a then 1 else 0) →
      ∀ x ∈ chainField M l, (∀ a ∈ l, part a x = 0) → x ∈ M := by
  intro l
  induction l with
  | nil => intro _ _ _ x hx _; rwa [chainField_nil] at hx
  | cons a l ih =>
    intro hnd hM0 hdual x hx hzero
    have haNotMem : a ∉ l := (List.nodup_cons.mp hnd).1
    have hndl : l.Nodup := (List.nodup_cons.mp hnd).2
    have hvan : ∀ y ∈ chainField M l, part a y = 0 := by
      intro y hy
      have hle : chainField M l ≤ derivationKer (part a) := by
        refine sup_le (fun z hz => hM0 a (by simp) z hz) ?_
        rw [IntermediateField.adjoin_le_iff]
        rintro z hz
        have hzl : z ∈ l := hz
        have hzz := hdual a (by simp) z (List.mem_cons_of_mem a hzl)
        have hzne : z ≠ a := by rintro rfl; exact haNotMem hzl
        simpa [hzne] using hzz
      exact hle hy
    have haa : part a a = 1 := by simpa using hdual a (by simp) a (by simp)
    rw [chainField_cons] at hx
    have hxM : x ∈ chainField M l :=
      mem_of_derivation_step hp (chainField M l) (le_chainField M l (hM a)) (part a) hvan haa hx
        (hzero a (by simp))
    exact ih hndl (fun b hb => hM0 b (by simp [hb])) (fun b hb c hc => hdual b (by simp [hb]) c
      (by simp [hc])) x hxM (fun b hb => hzero b (by simp [hb]))

end Descent

section SupTop

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- If `K` is separable over `k(s)` then `K ^ p · k(s) = K`: that intermediate field is
separable and purely inseparable in `K` at the same time. -/
theorem sup_pthPowers_adjoin_eq_top (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    [CharP k p] [PerfectField k] (s : Set K)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k s) K] :
    pthPowers k K p ⊔ IntermediateField.adjoin k s = ⊤ := by
  haveI : ExpChar K p := .prime hp.out
  haveI : ExpChar k p := .prime hp.out
  set F := IntermediateField.adjoin k s with hF
  set N : IntermediateField F K := IntermediateField.adjoin F (Set.range (frobenius K p)) with hN
  haveI : Algebra.IsSeparable N K := Algebra.isSeparable_tower_top_of_isSeparable ↥F ↥N K
  haveI : CharP N p := charP_of_ringHom (algebraMap N K) p
  haveI : ExpChar N p := .prime hp.out
  haveI : IsPurelyInseparable N K := by
    rw [isPurelyInseparable_iff_pow_mem N p]
    intro x
    refine ⟨1, ⟨x ^ p, ?_⟩, ?_⟩
    · exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
    · simp
  have hsurj := IsPurelyInseparable.surjective_algebraMap_of_isSeparable N K
  have hNtop : N = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy⟩ := hsurj x
    exact hy ▸ y.2
  have hres : IntermediateField.restrictScalars k N = ⊤ := by
    rw [hNtop]; ext y; simp
  rw [IntermediateField.restrictScalars_adjoin_eq_sup] at hres
  have hcoe : IntermediateField.adjoin k (Set.range (frobenius K p)) = pthPowers k K p := by
    rw [← coe_pthPowers (k := k) p]
    exact IntermediateField.adjoin_self k _
  rw [hcoe, sup_comm] at hres
  exact hres

end SupTop

section Freeness

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

open TensorProduct

/-- **Freeness of the module of differentials.**  If `t : ι → K` is a transcendence basis over
which `K` is separable, then `Ω[K⁄k]` is free on `{ d tᵢ }`. -/
theorem exists_kaehlerBasis_of_isTranscendenceBasis {ι : Type*} (t : ι → K)
    (ht : IsTranscendenceBasis k t)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k (Set.range t)) K] :
    ∃ b : Module.Basis ι K (Ω[K⁄k]), ∀ i, b i = KaehlerDifferential.D k K (t i) := by
  classical
  have hinj : Function.Injective (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] K) :=
    algebraicIndependent_iff_injective_aeval.1 ht.1
  letI : Algebra (MvPolynomial ι k) K := (MvPolynomial.aeval t).toAlgebra
  have halgK : (algebraMap (MvPolynomial ι k) K) =
      (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] K).toRingHom := rfl
  haveI : IsScalarTower k (MvPolynomial ι k) K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [halgK]; simp [MvPolynomial.algebraMap_eq]
  set E := IntermediateField.adjoin k (Set.range t) with hE
  have htE : ∀ i, t i ∈ E := fun i => IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  letI : Algebra (MvPolynomial ι k) E :=
    (MvPolynomial.aeval (fun i => (⟨t i, htE i⟩ : E))).toAlgebra
  have halgE : (algebraMap (MvPolynomial ι k) E) =
      (MvPolynomial.aeval (fun i => (⟨t i, htE i⟩ : E)) :
        MvPolynomial ι k →ₐ[k] E).toRingHom := rfl
  have hcompRing : (algebraMap E K).comp (algebraMap (MvPolynomial ι k) E) =
      algebraMap (MvPolynomial ι k) K := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, halgE, halgK]
      simp [IntermediateField.algebraMap_apply]
    · intro i
      rw [RingHom.comp_apply, halgE, halgK]
      simp
  have hcomp : ∀ a, algebraMap E K (algebraMap (MvPolynomial ι k) E a) =
      algebraMap (MvPolynomial ι k) K a := fun a => RingHom.congr_fun hcompRing a
  haveI : IsScalarTower (MvPolynomial ι k) E K :=
    IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  haveI : IsFractionRing (MvPolynomial ι k) E := by
    refine IsFractionRing.of_algEquiv (K := FractionRing (MvPolynomial ι k))
      (AlgEquiv.ofRingEquiv (f := ht.1.aevalEquivField.toRingEquiv) ?_)
    intro a
    apply Subtype.ext
    rw [show ((ht.1.aevalEquivField.toRingEquiv (algebraMap _ _ a) : E) : K) =
          ((ht.1.aevalEquivField (algebraMap _ _ a) : E) : K) from rfl,
      AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    have := hcomp a
    rw [halgK] at this
    simpa [IntermediateField.algebraMap_apply] using this.symm
  haveI : Algebra.FormallyEtale (MvPolynomial ι k) E :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial ι k))
  haveI : Algebra.FormallyEtale (↥E) K := Algebra.FormallyEtale.of_isSeparable (↥E) K
  haveI : Algebra.FormallyEtale (MvPolynomial ι k) K :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) (↥E) K
  refine ⟨((KaehlerDifferential.mvPolynomialBasis k ι).baseChange K).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) K), fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  congr 1
  rw [halgK]
  simp

/-- The dual family of partial derivations attached to a separating transcendence basis. -/
theorem exists_partialDerivation_of_isTranscendenceBasis {ι : Type*} [DecidableEq ι]
    (t : ι → K) (ht : IsTranscendenceBasis k t)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k (Set.range t)) K] :
    ∃ part : ι → Derivation k K K,
      (∀ i j, part i (t j) = if j = i then 1 else 0) ∧
      (∀ i, ∀ x : K, KaehlerDifferential.D k K x = 0 → part i x = 0) := by
  obtain ⟨b, hb⟩ := exists_kaehlerBasis_of_isTranscendenceBasis t ht
  refine ⟨fun i => (b.coord i).compDer (KaehlerDifferential.D k K), fun i j => ?_, ?_⟩
  · show b.coord i (KaehlerDifferential.D k K (t j)) = _
    rw [← hb j, Module.Basis.coord_apply, b.repr_self]
    simp [Finsupp.single_apply]
  · intro i x hx
    show b.coord i (KaehlerDifferential.D k K x) = 0
    rw [hx, map_zero]

end Freeness

section Main

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- **The derivation criterion.**  For a finitely generated extension `K / k` with `k` perfect
of characteristic `p`, the kernel of `d : K → Ω[K⁄k]` is exactly `K ^ p`. -/
theorem D_eq_zero_iff_exists_pow (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    [PerfectField k] [Algebra.EssFiniteType k K] (x : K) :
    KaehlerDifferential.D k K x = 0 ↔ ∃ y : K, y ^ p = x := by
  classical
  haveI : CharP k p := charP_of_ringHom (algebraMap k K) p
  haveI : ExpChar K p := .prime hp.out
  haveI : ExpChar k p := .prime hp.out
  constructor
  · intro hx
    obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
    have hrange : Set.range (Subtype.val : {y // y ∈ s} → K) = (s : Set K) := Subtype.range_coe
    haveI : Algebra.IsSeparable
        ↥(IntermediateField.adjoin k (Set.range (Subtype.val : {y // y ∈ s} → K))) K := by
      rw [hrange]; exact hsep
    obtain ⟨part, hdual, hker⟩ :=
      exists_partialDerivation_of_isTranscendenceBasis (Subtype.val : {y // y ∈ s} → K) hs
    have hMpow : ∀ y : K, y ^ p ∈ pthPowers k K p := fun y => mem_pthPowers.2 ⟨y, rfl⟩
    let part' : K → Derivation k K K := fun a => if h : a ∈ s then part ⟨a, h⟩ else 0
    have hzeroM : ∀ a ∈ s.toList, ∀ y ∈ pthPowers k K p, part' a y = 0 := by
      intro a _ y hy
      obtain ⟨z, rfl⟩ := mem_pthPowers.1 hy
      simp only [part']
      split
      · exact derivation_map_pow_char p _ z
      · rfl
    have hdual' : ∀ a ∈ s.toList, ∀ b ∈ s.toList, part' a b = if b = a then 1 else 0 := by
      intro a ha b hb
      rw [Finset.mem_toList] at ha hb
      simp only [part', dif_pos ha]
      have := hdual ⟨a, ha⟩ ⟨b, hb⟩
      simpa [Subtype.ext_iff] using this
    have hzerox : ∀ a ∈ s.toList, part' a x = 0 := by
      intro a _
      simp only [part']
      split
      · exact hker _ x hx
      · rfl
    have hmem : x ∈ chainField (pthPowers k K p) s.toList := by
      have hlist : {y : K | y ∈ s.toList} = (s : Set K) := by ext y; simp
      have htop : chainField (pthPowers k K p) s.toList = ⊤ := by
        rw [chainField, hlist]
        exact sup_pthPowers_adjoin_eq_top p (s : Set K)
      rw [htop]; trivial
    exact mem_pthPowers.1 (mem_of_forall_derivation_eq_zero hp.out (pthPowers k K p) hMpow part'
      s.toList s.nodup_toList hzeroM hdual' x hmem hzerox)
  · rintro ⟨y, rfl⟩
    exact derivation_map_pow_char p _ y

end Main

section Normal

variable {k R K : Type*} [Field k] [CommRing R] [IsIntegrallyClosed R] [Field K]
variable [Algebra R K] [IsFractionRing R K] [Algebra k K]

/-- **The criterion descends to an integrally closed subring.**  If `R` is a normal domain with
fraction field `K`, and `K / k` is finitely generated over a perfect field `k` of characteristic
`p`, then an element of `R` killed by `d : K → Ω[K⁄k]` is a `p`-th power **in `R`**, not merely
in `K`: its `p`-th root is integral over `R` (it is a root of the monic `X ^ p - x`) and lies in
`K`, so normality puts it in `R`.

This is the step from the function field to a local ring; the intended consumer is a stalk
`𝒪_{X, x}` of a smooth — hence normal — variety. -/
theorem D_algebraMap_eq_zero_iff_exists_pow (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    [PerfectField k] [Algebra.EssFiniteType k K] (x : R) :
    KaehlerDifferential.D k K (algebraMap R K x) = 0 ↔ ∃ z : R, z ^ p = x := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (D_eq_zero_iff_exists_pow k K p _).1 hx
    obtain ⟨z, hz⟩ :=
      IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K) hp.out.pos
        (hy ▸ isIntegral_algebraMap)
    refine ⟨z, hinj ?_⟩
    rw [map_pow, hz, hy]
  · rintro ⟨z, rfl⟩
    rw [map_pow]
    exact derivation_map_pow_char p _ _

end Normal

end FLT

end

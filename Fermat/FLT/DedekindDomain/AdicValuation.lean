/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.Topology.Path
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Fermat.FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Fermat.FLT.Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!

# Adic Completions

If `A` is a valued ring with field of fractions `K` there are two different
complete rings containing `A` one might define, the first is
`𝒪_v = {x ∈ K_v | v x ≤ 1}` (defined in Lean as `adicCompletionIntegers K v`)
and the second is the `v-adic` completion of `A`. In the case when `A` is a
Dedekind domain these definitions give isomorphic topological `A`-algebras.
This file makes some progress towards this.

## Main theorems/defs

* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_integers` : The closure of
    `A` in `K_v` is `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField` : The canonical
  isomorphism `A ⧸ v ≅ 𝓞ᵥ / v`.
* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_prodIntegers` : If `s` is
    a set of primes of `A`, then the closure of `A` in `∏_{v ∈ s} K_v` is `∏_{v ∈ s} 𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.denseRange_of_prodAlgebraMap` : If `s` is a finite set
    of primes of `A`, then `K` is dense in `∏_{v ∈ s} K_v`.
* We show (as an unnamed instance) `IsDiscreteValuationRing (𝒪[v.adicCompletion K])`
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped WithZero
lemma exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  lift x to Multiplicative ℤ using hx
  norm_cast at hx'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos hx')
  use k
  rw [← hk, Int.neg_neg]
  rfl


end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

lemma ne_zero_of_some_le_intValuation {a : A} {m : Multiplicative ℤ} (h : m ≤ v.intValuation a)
    : a ≠ 0 := by
  rintro rfl
  simp at h

lemma emultiplicity_eq_of_valuation_eq_ofAdd {a : A} {k : ℕ}
    (hv : v.intValuation a = (Multiplicative.ofAdd (-(k : ℤ)))) :
    emultiplicity v.asIdeal (Ideal.span {a}) = k := by
  classical
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ (le_of_eq hv.symm)
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  simp only [intValuation_if_neg _ hnz, WithZero.exp, ofAdd_neg, WithZero.coe_inv, inv_inj,
    WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq, Nat.cast_inj] at hv
  rw [← hv, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb,
    Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot, normalize_eq]

/-- Given `a, b ∈ A` and `v b ≤ v a` we can find `y in A` such that `y` is close to `a / b` by
    the valuation v. -/
lemma exists_adicValued_mul_sub_le {a b : A} {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    (hle : γ ≤ v.intValuation a)
    (hle' : v.intValuation b ≤ v.intValuation a) :
    ∃ y, v.intValuation (y * a - b) ≤ γ := by
  -- Find `n` such that `γ = Multiplicative.ofAdd (-(n : ℤ))`
  have hγ' : γ ≤ 1 := by
    apply hle.trans
    apply intValuation_le_one
  obtain ⟨n, hn⟩ := exists_ofAdd_natCast_of_le_one hγ hγ'
  rw [← hn, ← WithZero.exp] at hle ⊢
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ hle
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  -- Rewrite the statements to involve multiplicity rather than valuations
  rw [intValuation_eq_coe_neg_multiplicity _ hnz, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le] at hle
  have hm : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n :=
    le_of_eq_of_le
      (emultiplicity_eq_of_valuation_eq_ofAdd v <| intValuation_eq_coe_neg_multiplicity v hnz)
      (ENat.coe_le_coe.mpr hle)
  have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
    rwa [← intValuation_le_pow_iff_mem, ← intValuation_eq_coe_neg_multiplicity _ hnz]
  -- Now make use of
  -- `v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) = v.asIdeal ^ n ⊔ Ideal.span {a}`
  -- (this is where we need `IsDedekindDomain A`)
  rw [← Ideal.irreducible_pow_sup_of_ge hnb (irreducible v) n hm] at hb
  -- Extract y by writing b as a general term of the sum of the two ideals.
  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  use y
  -- And again prove the result about valuations by turning into one about ideals.
  rwa [hy, ← hxz, sub_add_cancel_right, intValuation_le_pow_iff_mem, neg_mem_iff]

open MonoidWithZeroHom in
lemma exists_adicValued_sub_lt_of_adicValued_le_one {x : (WithVal (v.valuation K))}
    (γ : ((WithZero (Multiplicative ℤ)))ˣ) (hx : Valued.v x ≤ 1) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  -- Write `x = n / d`
  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  dsimp only at hnd
  -- Show `v n ≤ v d`
  have hnd' := congr_arg Valued.v hnd
  simp only [map_mul] at hnd'
  have hge : Valued.v ((algebraMap A (WithVal (v.valuation K))) d) ≥
      Valued.v ((algebraMap A (WithVal (v.valuation K))) n) :=
    calc Valued.v ((algebraMap A (WithVal (v.valuation K))) d)
          ≥ (valuation K v) x.ofVal *
            (valuation K v) ((algebraMap A (WithVal (v.valuation K))) d).ofVal :=
                mul_le_of_le_one_left' hx
        _ = Valued.v ((algebraMap A (WithVal (v.valuation K))) n) := hnd'
  simp only [ge_iff_le, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hge
  simp only [valuation_of_algebraMap] at hge
  have hdz : (algebraMap A (WithVal (v.valuation K)) d) ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ (fun _ ↦ id) hd
  -- Find a suitable `γ` for the bound in `exists_adicValued_mul_sub_le`
  have hv : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hdz
  let hu : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) * γ.val ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hv, γ.ne_zero⟩
  obtain ⟨γ', hγ, hγu, hγv⟩ := WithZero.exists_ne_zero_and_lt_and_lt hu hv
  simp only [WithVal.algebraMap_right_apply, WithVal.valued_toVal, valuation_of_algebraMap] at hγv
  -- Now can apply `exists_adicValued_mul_sub_le` to get the approximation of `x`.
  obtain ⟨a, hval⟩ := exists_adicValued_mul_sub_le v hγ hγv.le hge
  use a
  rw [← eq_div_iff_mul_eq hdz] at hnd
  rw [← adicCompletion.valued_toCompletion]
  change Valued.v ((↑((WithVal.equiv (valuation K v)).symm ((algebraMap A K) a)) :
    (v.valuation K).Completion) - ↑x) < ↑γ
  rw [← UniformSpace.Completion.coe_sub, Valued.valuedCompletion_apply, hnd, sub_div' hdz, map_div₀]
  rw [← Valuation.pos_iff Valued.v, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hdz
  simp only [WithVal.algebraMap_right_apply, WithVal.equiv_symm_apply,
    ← WithVal.toVal_mul, ← WithVal.toVal_sub, WithVal.valued_toVal, ← map_mul, ← map_sub] at hγu ⊢
  rw [div_lt_iff₀' hdz, valuation_of_algebraMap]
  exact lt_of_le_of_lt hval hγu

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

-- could go in mathlib
instance : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open Valuation.IsRankOneDiscrete in
/-- The closure of `A` in `K_v` is `𝒪_v`. -/
theorem closureAlgebraMapIntegers_eq_integers :
    closure (algebraMap A (v.adicCompletion K)).range =
    SetLike.coe (v.adicCompletionIntegers K) := by
  apply subset_antisymm
  -- We know `closure A ⊆ 𝒪_v` because `𝒪_v` is closed and `A ⊆ 𝒪_v`
  · apply closure_minimal _ (Valued.isClosed_valuationSubring _)
    rintro b ⟨a, rfl⟩
    exact coe_mem_adicCompletionIntegers v a
  -- Show `𝒪_v ⊆ closure A` from `𝒪_v ⊆ closure O_[K]` and `closure O_[K] ⊆ closure A`
  · let f := fun (k : WithVal (v.valuation K)) => (k : v.adicCompletion K)
    suffices h : closure (f '' (f ⁻¹' (adicCompletionIntegers K v))) ⊆
        closure (algebraMap A (adicCompletion K v)).range by
      apply Set.Subset.trans _ h
      -- `f = ofCompletion ∘ (↑·)` has dense range: `ofCompletion` is a surjective homeomorphism
      -- and the completion coercion is dense.
      exact DenseRange.subset_closure_image_preimage_of_isOpen
        ((adicCompletion.ofCompletion_surjective K v).denseRange.comp
          UniformSpace.Completion.denseRange_coe (adicCompletion.continuous_ofCompletion K v))
        (Valued.isOpen_valuationSubring _)
    -- Unfold the topological definitions until we get the result from the previous lemma
    apply closure_minimal _ isClosed_closure
    rintro k ⟨x, hx, rfl⟩
    unfold f at hx
    rw [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers,
        adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply] at hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    let γ' := Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv γ
    obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicValued_le_one K v γ' hx
    use algebraMap A K a
    constructor
    · use a
      rfl
    · apply hγ
      simp only [sub_zero, WithVal.equiv_symm_apply, Set.mem_setOf_eq]
      rwa [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (valuedAdicCompletion_surjective K v)]


open Valuation.IsRankOneDiscrete in
/-- An element of `𝒪_v` can be approximated by an element of `A`. -/
theorem exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  have h := closureAlgebraMapIntegers_eq_integers K v
  rw [Set.ext_iff] at h
  specialize h x
  simp_rw [RingHom.coe_range, Subtype.coe_prop, iff_true, mem_closure_iff_nhds] at h
  specialize h { y | Valued.v (y  - (x : v.adicCompletion K)) < γ.val }
  have hn : {y | Valued.v (y - (x : v.adicCompletion K)) < γ.val} ∈ nhds x.val := by
    rw [Valued.mem_nhds]
    use (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt vK)).symm γ
    have hsurj := (valuedAdicCompletion_surjective K v)
    obtain ⟨z, hz⟩ := hsurj γ
    simp [← hz, ← valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj,
      (valueGroup₀_equiv_withZeroMulInt_strictMono (.ofClass vK)).lt_iff_lt,
      -valueGroup₀_equiv_withZeroMulInt_apply]
  obtain ⟨z, ⟨hz, a, ha⟩⟩ := h hn
  use a
  rw [algebraMap_adicCompletion, Function.comp_apply] at ha
  rwa [ha]

/-- The maximal ideal of the integers of the completion of `v`. -/
noncomputable abbrev completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)

lemma mem_completionIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ completionIdeal K v ↔ Valued.v x.val < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

lemma algebraMap_completionIntegers (x : A) :
    (algebraMap A (v.adicCompletionIntegers K) x) = (algebraMap A (v.adicCompletion K) x) :=
  rfl

instance : (v.completionIdeal K).LiesOver v.asIdeal where
  over := by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]

open IsLocalRing in
/-- The canonical ring homomorphism from A / v to 𝓞ᵥ / v, where 𝓞ᵥ is the integers of the
completion Kᵥ of the field of fractions of A. -/
noncomputable def ResidueFieldToCompletionResidueField :
    A ⧸ v.asIdeal →+* ResidueField (v.adicCompletionIntegers K) :=
  Ideal.quotientMap _ (algebraMap _ _) <| le_of_eq Ideal.LiesOver.over

-- shortcut instances for next def: needed after mathlib #34045
noncomputable instance : CommSemiring ↥(adicCompletionIntegers K v) := inferInstance
noncomputable instance : Field (adicCompletion K v) := inferInstance

set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
/-- The canonical isomorphism from A / v to 𝓞ᵥ / v, where 𝓞ᵥ is the integers of the
completion Kᵥ of the field of fractions K of A. -/
noncomputable def ResidueFieldEquivCompletionResidueField :
    A ⧸ v.asIdeal ≃+* ResidueField (v.adicCompletionIntegers K) := by
  apply RingEquiv.ofBijective (ResidueFieldToCompletionResidueField K v)
    ⟨Ideal.quotientMap_injective' <| ge_of_eq Ideal.LiesOver.over, ?_⟩
  intro z
  obtain ⟨x, hx⟩ :=
    Submodule.Quotient.mk_surjective (p := maximalIdeal ↥(adicCompletionIntegers K v)) z
  rw [← hx, Ideal.Quotient.mk_eq_mk]
  suffices ∃ a : A, (ResidueFieldToCompletionResidueField K v) a = Ideal.Quotient.mk _ x by
    obtain ⟨a, ha⟩ := this
    refine ⟨a, ha⟩
  change ∃ a, Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K)) _ = _
  simp_rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_maximalIdeal, mem_nonunits_iff]
  -- TODO - figure out why this can't be 'simp_rw/simp'
  conv =>
    pattern ¬(IsUnit _)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact exists_adicValued_sub_lt_of_adicCompletionInteger K v x 1




lemma adicCompletion.eq_mul_nonZeroDivisor_inv_adicCompletionIntegers (v : HeightOneSpectrum A)
    (x : v.adicCompletion K) :
    ∃a ∈ nonZeroDivisors A, ∃b ∈ v.adicCompletionIntegers K, x = (algebraMap A K a)⁻¹ • b := by
  obtain ⟨a, hz, ha⟩ :=
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  use a, hz, (algebraMap A K a) • x
  constructor
  · rwa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_comm]
  · rw [smul_smul, inv_mul_cancel₀, one_smul]
    exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) hz

lemma adicCompletion.eq_mul_pi_adicCompletionIntegers {ι : Type*} [Finite ι]
    (valuation : ι → HeightOneSpectrum A) (x : (i : ι) → (valuation i).adicCompletion K) :
      ∃k : K, ∃y ∈ Set.pi Set.univ (fun (i : ι) ↦ ((valuation i).adicCompletionIntegers K).carrier),
      x = k • y := by
  classical
  let := Fintype.ofFinite ι
  choose f hf using fun (i : ι) =>
    eq_mul_nonZeroDivisor_inv_adicCompletionIntegers K (valuation i) (x i)
  use (algebraMap A K (∏ i : ι, f i))⁻¹, (algebraMap A K (∏ i : ι, f i)) • x
  have hz : ∀ (i : ι), (algebraMap A K) (f i) ≠ 0 := fun i =>
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) (hf i).left
  constructor
  · rintro i -
    obtain ⟨b, hb, hx⟩ := (hf i).right
    beta_reduce
    rw [Pi.smul_apply, algebraMap_smul, Subsemiring.coe_carrier_toSubmonoid,
        Subring.coe_toSubsemiring, SetLike.mem_coe, ValuationSubring.mem_toSubring, hx,
        ← Finset.prod_erase_mul _ f (Finset.mem_univ i), mul_smul,
        ← IsScalarTower.smul_assoc (f i), Algebra.smul_def (f i), mul_inv_cancel₀ (hz i), one_smul,
        Algebra.smul_def]
    apply mul_mem (coe_mem_adicCompletionIntegers _ _) hb
  · rw [smul_smul, inv_mul_cancel₀, one_smul]
    simp [Finset.prod_ne_zero_iff, hz]


namespace adicCompletion

-- (invisible-instance support: `exists_uniformizer` feeds the DVR instance
-- cluster below, which is consumed by typeclass synthesis in cone modules
-- (e.g. `NumberField/Completion/Finite.lean`) — do not delete as free-floating.)
-- IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
open scoped algebraMap in
theorem exists_uniformizer (v : HeightOneSpectrum A) :
    ∃ π : v.adicCompletionIntegers K, Valued.v π.1 = Multiplicative.ofAdd (- 1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  use π
  rw [← WithZero.exp, ← hπ, ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]


variable {K} in
theorem uniformizer_ne_zero {v : HeightOneSpectrum A}
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    π ≠ 0 := by
  contrapose! hπ
  simp [hπ]

-- shortcut instance for next theorem: needed after mathlib #34045
noncomputable instance : Ring (adicCompletion K v) := inferInstance

set_option backward.isDefEq.respectTransparency false in
variable {K} in
open scoped Multiplicative in
theorem uniformizer_not_isUnit {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬IsUnit (π : v.adicCompletionIntegers K) := by
  rw [ValuationSubring.isUnit_iff_valued_eq_one, ← WithZero.coe_one, ← ofAdd_zero, hπ]
  apply ne_of_lt
  rw [WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
  omega

theorem eq_pow_uniformizer_mul_unit {x : v.adicCompletionIntegers K} (hx : x ≠ 0)
    {π : v.adicCompletionIntegers K} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers K)ˣ), x = π ^ n * u := by
  have hx' : Valued.v x.1 ≠ 0 := by simp [hx]
  let m := - Multiplicative.toAdd (WithZero.unzero hx')
  have hm₀ : 0 ≤ m := by
    simp_rw [m, Right.nonneg_neg_iff, ← toAdd_one, Multiplicative.toAdd_le]
    rw [← WithZero.coe_le_coe]; exact (WithZero.coe_unzero _).symm ▸ x.2
  have hpow : Valued.v (π ^ (-m) * x.val) = 1 := by
    rw [Valued.v.map_mul, map_zpow₀, hπ, ofAdd_neg, WithZero.coe_inv,
      inv_zpow', neg_neg, ← WithZero.coe_zpow, ← Int.ofAdd_mul, one_mul, ofAdd_neg, ofAdd_toAdd,
      WithZero.coe_inv, WithZero.coe_unzero, inv_mul_cancel₀ hx']
  let a : v.adicCompletionIntegers K := ⟨π ^ (-m) * x.val, le_of_eq hpow⟩
  refine ⟨m.toNat, (ValuationSubring.isUnit_of_valued_eq_one a hpow).unit, Subtype.ext ?_⟩
  simp only [zpow_neg, IsUnit.unit_spec, MulMemClass.coe_mul, SubmonoidClass.coe_pow, a,
    ← zpow_natCast, m.toNat_of_nonneg hm₀, ← mul_assoc]
  rw [mul_inv_cancel₀ (zpow_ne_zero _ <| (by simp [uniformizer_ne_zero hπ])), one_mul]

open scoped algebraMap in
theorem maximalIdeal_eq_span_uniformizer {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {(π : v.adicCompletionIntegers K)} := by
  refine (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.span_singleton_ne_top (uniformizer_not_isUnit v hπ)) (fun x hx => ?_)
  by_cases hx₀ : x = 0
  · simp only [hx₀, Ideal.zero_mem]
  · obtain ⟨n, ⟨u, hu⟩⟩ := eq_pow_uniformizer_mul_unit K v hx₀ hπ
    have hn : ¬(IsUnit x) := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx h)
    replace hn : n ≠ 0 := fun h => by {rw [hu, h, pow_zero, one_mul] at hn; exact hn u.isUnit}
    simpa [Ideal.mem_span_singleton, hu, IsUnit.dvd_mul_right, Units.isUnit] using dvd_pow_self π hn







-- (invisible instances: consumed by typeclass synthesis then inlined —
-- `IsDiscreteValuationRing 𝒪ᵥ` is required by cone declarations in
-- `NumberField/Completion/Finite.lean`; do not delete as free-floating.)
instance : Ring.DimensionLEOne (v.adicCompletionIntegers K) where
  maximalOfPrime {𝔭} h𝔭_ne_bot h𝔭_prime := by
    let ⟨x, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭_ne_bot
    let ⟨π, hπ⟩ := exists_uniformizer K v
    obtain ⟨n, ⟨u, rfl⟩⟩ := eq_pow_uniformizer_mul_unit K v hx.2 hπ
    simp only [Units.isUnit, Ideal.mul_unit_mem_iff_mem, ne_eq, mul_eq_zero, pow_eq_zero_iff',
      Units.ne_zero, or_false, not_and, Decidable.not_not] at hx
    by_cases hn : n = 0
    · simp only [hn, pow_zero, ← 𝔭.eq_top_iff_one, implies_true, and_true] at hx
      exact h𝔭_prime.ne_top hx |>.elim
    · rw [h𝔭_prime.pow_mem_iff_mem n (by omega), ← 𝔭.span_singleton_le_iff_mem,
        ← maximalIdeal_eq_span_uniformizer K v hπ] at hx
      exact IsLocalRing.maximalIdeal_le h𝔭_prime.ne_top hx.1

open scoped algebraMap in
instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  apply IsPrincipalIdealRing.of_prime
  intro P hP
  by_cases hP_bot : P = ⊥
  · exact hP_bot ▸ bot_isPrincipal
  · let ⟨π, hπ⟩ := exists_uniformizer K v
    use π
    rw [IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_bot)]
    exact maximalIdeal_eq_span_uniformizer K v hπ

instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    let ⟨π, hπ⟩ := exists_uniformizer K v
    rw [maximalIdeal_eq_span_uniformizer K v hπ]
    intro h
    simp only [Ideal.span_singleton_eq_bot] at h
    exact uniformizer_ne_zero hπ h

open scoped Valued in
instance : IsDiscreteValuationRing (𝒪[v.adicCompletion K]) :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))

end adicCompletion



end IsDedekindDomain.HeightOneSpectrum

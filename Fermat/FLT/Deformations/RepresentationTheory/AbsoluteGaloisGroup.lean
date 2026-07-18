/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.Frobenius
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Fermat.FLT.Deformations.RepresentationTheory.IntegralClosure
public import Fermat.FLT.Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import Fermat.FLT.NumberField.Completion.Finite
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Functoriality of the absolute Galois group

For a field extension `K → L`, we define the induced map between absolute
Galois groups `Γ L → Γ K` and prove its continuity, together with finite-index
results for fixing subgroups.
-/

@[expose] public section

variable {K L : Type*} [Field K] [Field L]
variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

open NumberField

variable [NumberField K]

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

set_option backward.isDefEq.respectTransparency false in
/-- Given a field extension, this is a map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.mapAux (f : K →+* L) : Γ L →* Γ K where
  toFun σ :=
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    ((σ.restrictScalars K).toAlgHom.comp
      (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ)).restrictNormal' (Kᵃˡᵍ)
  map_one' := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans (by simp)
  map_mul' σ₁ σ₂ := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (AlgebraicClosure.map f).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans ?_
    refine ((AlgHom.restrictNormal_commutes _ _ _).trans ?_).symm
    simpa [absoluteGaloisGroup] using! AlgHom.restrictNormal_commutes _ _ _

/-- Given a field extension, this is a continuous map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.map (f : K →+* L) : Γ L →ₜ* Γ K where
  __ := Field.absoluteGaloisGroup.mapAux f
  continuous_toFun := by
    classical
    letI := f.toAlgebra
    let F : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ := IsAlgClosed.lift
    letI := F.toRingHom.toAlgebra
    apply continuous_of_continuousAt_one (Field.absoluteGaloisGroup.mapAux f)
    rw [ContinuousAt, map_one]
    refine ((galGroupBasis L (Lᵃˡᵍ)).nhds_one_hasBasis.tendsto_iff
      (galGroupBasis K (Kᵃˡᵍ)).nhds_one_hasBasis).mpr ?_
    rintro _ ⟨_, ⟨K', hK', rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨.adjoin _ (K'.map F), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
    · have : FiniteDimensional _ _ := hK'
      obtain ⟨s, hs⟩ := K'.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType K K'))
      obtain rfl := IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
      simp only [IntermediateField.adjoin_map, IntermediateField.adjoin_adjoin_right,
        ← Finset.coe_image]
      refine IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
    · exact F.injective ((AlgHom.restrictNormal_commutes _ _ _).trans
        (hσ ⟨F x, IntermediateField.subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩))

set_option allowUnsafeReducibility true in
attribute [reducible] Field.absoluteGaloisGroup -- lol WTF is going on here

set_option backward.isDefEq.respectTransparency false in
lemma Field.absoluteGaloisGroup.lift_map (f : K →+* L) (σ : Γ L) (x : Kᵃˡᵍ) :
    AlgebraicClosure.map f (map f σ x) = σ (AlgebraicClosure.map f x) := by
  letI := f.toAlgebra
  letI := (AlgebraicClosure.map f).toAlgebra
  exact AlgHom.restrictNormal_commutes _ _ _


attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubringVendored IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring
  Valued.toIsUniformAddGroup

attribute [local instance] Valued.toNormedField in
lemma isIntegral_of_spectralNorm_le_one
    {K L Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Field K] [Field L]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne] [Algebra K L] [Algebra.IsAlgebraic K L]
    {x : L} (hx : spectralNorm K L x ≤ 1) : IsIntegral (Valued.v : Valuation K Γ₀).integer x := by
  have : minpoly K x ∈ Polynomial.lifts (Valued.v : Valuation K Γ₀).integer.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    have := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at this
    split_ifs at this with h
    · conv_rhs at this => rw [← Real.one_rpow (1 / (↑(minpoly K x).natDegree - ↑i) : ℝ)]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at this
      simpa [Valuation.mem_integer_iff] using this
    obtain h | h := (le_of_not_gt h).eq_or_lt
    · simp [← h, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, one_mem]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt h, zero_mem]
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic this
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K,
    Subring.algebraMap_def, hP, minpoly.aeval]

lemma spectralNorm_inv
    {K L : Type*} [NontriviallyNormedField K] [Field L] [Algebra K L] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra.IsAlgebraic K L] (x : L) :
    spectralNorm K L (x⁻¹) = (spectralNorm K L x)⁻¹ := by
  by_cases H : x = 0
  · simp [H, spectralNorm_zero]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← spectralAlgNorm_def, ← spectralAlgNorm_def, ← spectralAlgNorm_mul (K := K) x x⁻¹,
    mul_inv_cancel₀ H, spectralAlgNorm_one]

noncomputable instance : NontriviallyNormedField Kᵥ := Valued.toNontriviallyNormedField _ _

instance valuationRing_integralClosure
    {L : Type*} [Field L] [Algebra Kᵥ L] [Algebra.IsAlgebraic Kᵥ L] :
    ValuationRing (IntegralClosure 𝒪ᵥ L) := by
  refine ValuationSubring.instValuationRingSubtypeMem ⟨(integralClosure 𝒪ᵥ L).toSubring, ?_⟩
  intro x
  obtain hx | hx := le_total (spectralNorm Kᵥ L x) 1
  · exact .inl (isIntegral_of_spectralNorm_le_one hx)
  · have := inv_le_one_of_one_le₀ hx
    rw [← spectralNorm_inv] at this
    exact .inr (isIntegral_of_spectralNorm_le_one this)

/-- The local inertia subgroup of a number field at a prime, defined as a subgroup
of the local galois group. -/
noncomputable
def localInertiaGroup : Subgroup (Γ Kᵥ) :=
  (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).toAddSubgroup.inertia (Γ Kᵥ)

/-- The integral closure of `𝒪ᵥ` in the algebraic closure of `Kᵥ`, as a
valuation subring: the spectral-norm dichotomy shows every element or
its inverse is integral. (The subring is the one whose maximal ideal
defines `localInertiaGroup`; packaging it as a `ValuationSubring` lets
the decomposition/inertia machinery of
`Mathlib.RingTheory.Valuation.RamificationGroup` apply.) -/
noncomputable
def localValuationSubring : ValuationSubring (Kᵥᵃˡᵍ) :=
  ⟨(integralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)).toSubring, by
    intro x
    obtain hx | hx := le_total (spectralNorm Kᵥ (Kᵥᵃˡᵍ) x) 1
    · exact .inl (isIntegral_of_spectralNorm_le_one hx)
    · have := inv_le_one_of_one_le₀ hx
      rw [← spectralNorm_inv] at this
      exact .inr (isIntegral_of_spectralNorm_le_one this)⟩

open scoped Pointwise in
/-- Every `Kᵥ`-automorphism stabilizes the local valuation subring:
integrality over `𝒪ᵥ` is preserved by automorphisms fixing `Kᵥ`. -/
theorem mem_decompositionSubgroup_localValuationSubring
    (σ : (Kᵥᵃˡᵍ) ≃ₐ[Kᵥ] (Kᵥᵃˡᵍ)) :
    σ ∈ (localValuationSubring v).decompositionSubgroup Kᵥ := by
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact IsIntegral.map
      (σ.toAlgHom.restrictScalars 𝒪ᵥ) (hx : IsIntegral 𝒪ᵥ x)
  · intro x hx
    refine ⟨σ⁻¹ x, ?_, ?_⟩
    · exact IsIntegral.map
        ((σ⁻¹ : (Kᵥᵃˡᵍ) ≃ₐ[Kᵥ] (Kᵥᵃˡᵍ)).toAlgHom.restrictScalars 𝒪ᵥ)
        (hx : IsIntegral 𝒪ᵥ x)
    · show σ (σ⁻¹ x) = x
      exact σ.apply_symm_apply x

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The two spellings of local inertia agree** (PROVEN): an element of
`localInertiaGroup v` (trivial action mod the maximal ideal of the
integral closure) lies in the `ValuationSubring.inertiaSubgroup` of the
local valuation subring (trivial action on its residue field). The two
conditions are the same congruence, read through `Ideal.Quotient.eq`
and the residue-compatibility of the decomposition action. -/
theorem mem_inertiaSubgroup_localValuationSubring
    (σ : (Kᵥᵃˡᵍ) ≃ₐ[Kᵥ] (Kᵥᵃˡᵍ)) (hσ : σ ∈ localInertiaGroup v) :
    (⟨σ, mem_decompositionSubgroup_localValuationSubring v σ⟩ :
      (localValuationSubring v).decompositionSubgroup Kᵥ) ∈
      (localValuationSubring v).inertiaSubgroup Kᵥ := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := localValuationSubring v) z
  have h1 : (MulSemiringAction.toRingAut
      ((localValuationSubring v).decompositionSubgroup Kᵥ)
      (IsLocalRing.ResidueField (localValuationSubring v))
      (⟨σ, mem_decompositionSubgroup_localValuationSubring v σ⟩))
      (IsLocalRing.residue _ a) =
      IsLocalRing.residue _
        ((⟨σ, mem_decompositionSubgroup_localValuationSubring v σ⟩ :
          (localValuationSubring v).decompositionSubgroup Kᵥ) • a) := rfl
  rw [h1]
  show IsLocalRing.residue _ _ = IsLocalRing.residue _ a
  exact Ideal.Quotient.eq.mpr (hσ ⟨(a : (Kᵥᵃˡᵍ)), a.2⟩)


instance : CharZero Kᵥ :=
  ((algebraMap K Kᵥ).charZero_iff (algebraMap K Kᵥ).injective).mp inferInstance

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩

instance : Finite (IsLocalRing.ResidueField 𝒪ᵥ) := inferInstance

instance finite_adicCompletionIntegers_quotient
    {I : Ideal 𝒪ᵥ} [I.IsPrime] [NeZero I] : Finite (𝒪ᵥ ⧸ I) := by
  obtain rfl := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime 𝒪ᵥ).mp
      inferInstance).2.unique ⟨NeZero.ne _, ‹I.IsPrime›⟩ ⟨IsDiscreteValuationRing.not_a_field 𝒪ᵥ,
      inferInstanceAs (𝔪 _).IsPrime⟩
  exact inferInstanceAs <| Finite (IsLocalRing.ResidueField _)

instance neZero_maximalIdeal_integralClosure :
    NeZero (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) := by
  have : 𝒪ᵥ ≠ ⊤ := by
    refine fun h ↦ IsDiscreteValuationRing.not_isField 𝒪ᵥ (h ▸ ?_)
    exact (Subring.topEquiv (R := Kᵥ)).isField (Semifield.toIsField Kᵥ)
  exact ⟨(Ideal.bot_lt_of_maximal (𝔪 _)
    (not_isField_integralClosure (L := Kᵥᵃˡᵍ) _ this)).ne'⟩

/-- An arbitrary choice of an (arithmetic) frobenious element of a local galois group. -/
noncomputable
def Field.AbsoluteGaloisGroup.adicArithFrob : Γ Kᵥ :=
  arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))

local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

lemma Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob :
    IsArithFrobAt 𝒪ᵥ Frobᵥ (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) :=
  .arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))

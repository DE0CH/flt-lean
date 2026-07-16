/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Deyao Chen
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- `Ideal.ramificationIdxIn` and `card_inertia_eq_ramificationIdxIn`,
-- used to state and prove the finite-level `|I| = e` theorem.
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# The fixed field of the local inertia group is unramified

This file states the LOCAL half of the embedding-prime transport family:
if a finite subextension `M/Kᵥ` of `Kᵥᵃˡᵍ` is fixed pointwise by the
local inertia group `localInertiaGroup v ≤ Γ Kᵥ`, then `M/Kᵥ` is
unramified, in the concrete integral form: the maximal ideal of `𝒪ᵥ`
generates the maximal ideal of the integral closure `𝒪_M` of `𝒪ᵥ` in
`M` (i.e. `e(M/Kᵥ) = 1`).

Classically this is the statement that the fixed field of the inertia
group of `Kᵥᵃˡᵍ/Kᵥ` is the maximal unramified extension `Kᵥᵘⁿʳ`
(Neukirch, *Algebraic Number Theory*, II.9.11 / II.7.5 applied through
finite levels). The planned proof route (see PROGRESS.md): pass to the
Galois closure `N` of `M/Kᵥ`, use `|I(N/Kᵥ)| = e(N/Kᵥ)` at the finite
level (`Ideal.card_inertia_eq_ramificationIdxIn`, applicable because
the integral closure at every finite level is LOCAL — a valuation ring
via the vendored spectral-norm argument — with finite residue field),
tower multiplicativity of `e`, and a compactness lifting of finite-level
inertia elements to `localInertiaGroup v` (finite-level inertia
surjectivity along towers is a counting argument from the same two
ingredients; no henselian lifting is required).

The GLOBAL half (transporting this statement to the trivial-inertia
prime `Q₀` of a number field `L` fixed by the image of the local
inertia) is derived in `Fermat.FLT.FreyCurve.MazurTorsion`.
-/

@[expose] public section

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

/-- The type synonym `IntegralClosure R A` is an integral closure of `R`
in `A` in the `IsIntegralClosure` sense (delta-transparent restatement of
mathlib's instance for the `integralClosure` subalgebra). -/
instance isIntegralClosure_integralClosure {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] :
    IsIntegralClosure (IntegralClosure R A) R A := by
  delta IntegralClosure
  infer_instance

/-- The action of `G` on the integral closure distributes over the
scalar multiplication of the integral closure on the ambient field
(both are multiplication in `K`, and `G` acts by ring maps). -/
instance smulDistribClass_integralClosure
    {G R K : Type*} [CommRing R] [Field K] [Algebra R K] [Monoid G]
    [MulSemiringAction G K] [SMulCommClass G R K] :
    SMulDistribClass G (IntegralClosure R K) K where
  smul_distrib_smul g b s := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    rfl

/-- A valuation subring, its field, and an intermediate field of an
extension form a scalar tower (the algebra map out of the subring is
DEFINED as the composite). Deliberately restricted to intermediate-field
subtypes: a fully general `IsScalarTower O K L` instance would enable
`IntermediateField.algebra'` as a SECOND route to `Algebra O ↥M`,
making elaborations of `IntegralClosure O ↥M` ambiguous. -/
instance instIsScalarTowerValuationSubringIntermediateField
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (O : ValuationSubring K) (M : IntermediateField K E) :
    IsScalarTower O K M :=
  IsScalarTower.of_algebraMap_eq' rfl

section FiniteLevel

variable (N : IntermediateField
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
  [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]

/-- The maximal ideal of the integral closure at a finite level lies over
the maximal ideal of `𝒪ᵥ` (the pullback of a maximal ideal along an
integral extension of a local ring is the unique maximal ideal). -/
instance liesOver_maximalIdeal_integralClosure :
    (𝔪 (IntegralClosure 𝒪ᵥ N)).LiesOver (𝔪 𝒪ᵥ) := by
  constructor
  have hmax : ((𝔪 (IntegralClosure 𝒪ᵥ N)).comap
      (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ N))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (𝔪 (IntegralClosure 𝒪ᵥ N))
  exact (hmax.eq_of_le (IsLocalRing.maximalIdeal.isMaximal 𝒪ᵥ).ne_top
    (IsLocalRing.le_maximalIdeal hmax.ne_top)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Finite-level `|I| = e`** (Hilbert; PROVEN 2026-07-16 —
instance-assembly around mathlib's
`card_inertia_eq_ramificationIdxIn`): for a finite Galois subextension
`N/Kᵥ` of `Kᵥᵃˡᵍ`, the inertia subgroup of the maximal ideal of
`𝒪_N = IntegralClosure 𝒪ᵥ N` inside `Gal(N/Kᵥ)` has cardinality the
ramification index of `𝔪ᵥ` in `𝒪_N`. The assembly: `𝒪_N` is a
fraction ring of `N` (integral closure in a finite separable
extension), the Galois action restricts with invariants `𝒪ᵥ`
(`IsGaloisGroup.of_isFractionRing`), `𝒪_N` is finite free over the
DVR `𝒪ᵥ` (hence flat), and the residue field of `𝔪ᵥ` is finite hence
perfect. The `respectTransparency` option is REQUIRED: without it the
`Module.Free` synthesis fails on non-reducibly-unifiable instance
arguments across `IntegralClosure` elaboration sites. -/
theorem card_inertia_finite_level [IsGalois Kᵥ N] :
    Nat.card ((𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[Kᵥ] N)) =
      Ideal.ramificationIdxIn (𝔪 𝒪ᵥ) (IntegralClosure 𝒪ᵥ N) := by
  haveI : IsFractionRing (IntegralClosure 𝒪ᵥ N) N :=
    IsIntegralClosure.isFractionRing_of_finite_extension 𝒪ᵥ Kᵥ N
      (IntegralClosure 𝒪ᵥ N)
  haveI : IsGaloisGroup (N ≃ₐ[Kᵥ] N) 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) :=
    IsGaloisGroup.of_isFractionRing (N ≃ₐ[Kᵥ] N) 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) Kᵥ N
  haveI : Module.Finite 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) :=
    IsIntegralClosure.finite 𝒪ᵥ Kᵥ N (IntegralClosure 𝒪ᵥ N)
  haveI : Module.Free 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) :=
    Module.free_of_finite_type_torsion_free'
  -- the residue field of `𝔪ᵥ` is finite (surjective image of `κ(𝒪ᵥ)`),
  -- hence perfect
  haveI : Finite (𝒪ᵥ ⧸ (𝔪 𝒪ᵥ)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField 𝒪ᵥ))
  have hsurj : Function.Surjective
      (algebraMap (𝒪ᵥ ⧸ (𝔪 𝒪ᵥ)) ((𝔪 𝒪ᵥ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
        (IsLocalRing.maximalIdeal.isMaximal _))
  haveI : Finite ((𝔪 𝒪ᵥ).ResidueField) := Finite.of_surjective _ hsurj
  exact Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[Kᵥ] N)
    (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ N))

/-- The tower `𝒪ᵥ ⊆ ↥N ⊆ Kᵥᵃˡᵍ` (middle term an intermediate-field
subtype; the ambient-middle shape `𝒪ᵥ ⊆ Kᵥ ⊆ Kᵥᵃˡᵍ` is deliberately
NOT declared — see the previous instance's docstring). -/
instance instIsScalarTowerValuationSubringIntermediateFieldAmbient
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (O : ValuationSubring K) (M : IntermediateField K E) :
    IsScalarTower O M E :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [show (algebraMap O E) = (algebraMap K E).comp (algebraMap O K) from rfl,
      IsScalarTower.algebraMap_eq K M E, RingHom.comp_assoc]
    rfl)

/-- The inclusion of the integral closure of `𝒪ᵥ` in a subextension `N`
into the integral closure in the full algebraic closure. -/
noncomputable def integralClosureInclusion :
    IntegralClosure 𝒪ᵥ N →+* IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ) :=
  RingHom.codRestrict
    ((algebraMap N (Kᵥᵃˡᵍ)).comp
      (algebraMap (IntegralClosure 𝒪ᵥ N) N))
    (integralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))
    (fun x => (Algebra.IsIntegral.isIntegral (R := 𝒪ᵥ) x).map
      ((IsScalarTower.toAlgHom 𝒪ᵥ N (Kᵥᵃˡᵍ)).comp
        (IsScalarTower.toAlgHom 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) N)))

omit [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N] in
/-- **Restriction maps the local inertia group into the finite-level
inertia**: if `σ ∈ Γ Kᵥ` lies in `localInertiaGroup v`, then its
restriction to a finite Galois subextension `N` lies in the inertia
subgroup of `𝔪_N` in `Gal(N/Kᵥ)`. The two ingredients: the
compatibility `ι(σ|_N • x) = σ • ι(x)` (from
`AlgEquiv.restrictNormal_commutes`), and `ι⁻¹(𝔪_big) ≤ 𝔪_N` — which is
FREE from locality of `𝒪_N` (the pullback is a proper ideal of a local
ring; no integrality or henselian input needed). -/
theorem restrictNormalHom_mem_inertia_of_mem_localInertiaGroup
    [IsGalois Kᵥ N] (σ : Γ Kᵥ) (hσ : σ ∈ localInertiaGroup v) :
    AlgEquiv.restrictNormalHom N σ ∈
      (𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[Kᵥ] N) := by
  rw [AddSubgroup.mem_inertia]
  intro x
  -- the inclusion carries the difference into `𝔪` of the big integral
  -- closure
  have hcomm : integralClosureInclusion v N ((AlgEquiv.restrictNormalHom N σ) • x - x) =
      σ • (integralClosureInclusion v N x) - integralClosureInclusion v N x := by
    rw [map_sub]
    congr 1
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes σ N (algebraMap (IntegralClosure 𝒪ᵥ N) N x)
  have hbig : integralClosureInclusion v N ((AlgEquiv.restrictNormalHom N σ) • x - x) ∈
      (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).toAddSubgroup := by
    rw [hcomm]
    exact hσ (integralClosureInclusion v N x)
  -- pull back along the inclusion: the pullback of the maximal ideal is
  -- a proper ideal of the local ring `𝒪_N`, hence contained in `𝔪_N`
  have hproper : (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).comap
      (integralClosureInclusion v N) ≠ ⊤ := by
    intro htop
    have h1 : (1 : IntegralClosure 𝒪ᵥ N) ∈ (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).comap
        (integralClosureInclusion v N) := htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hle := IsLocalRing.le_maximalIdeal hproper
  rw [Submodule.mem_toAddSubgroup] at hbig ⊢
  exact hle (Ideal.mem_comap.mpr hbig)

end FiniteLevel

set_option warn.sorry false in
/-- **The fixed field of the local inertia group is unramified** (the
local half of the embedding-prime transport; Neukirch II.9.11): if a
finite subextension `M/Kᵥ` of `Kᵥᵃˡᵍ` is fixed pointwise by
`localInertiaGroup v`, then the maximal ideal of `𝒪ᵥ` generates the
maximal ideal of the integral closure of `𝒪ᵥ` in `M` — that is,
`e(M/Kᵥ) = 1`. -/
theorem maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup
    (M : IntermediateField Kᵥ (Kᵥᵃˡᵍ)) [FiniteDimensional Kᵥ M]
    (hM : M ≤ IntermediateField.fixedField (localInertiaGroup v)) :
    (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ M)) =
      𝔪 (IntegralClosure 𝒪ᵥ M) :=
  sorry

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
-- `Ring.HasFiniteQuotients` and `Submodule.finite_quotient_smul`, for
-- residue finiteness over intermediate bases.
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Index
-- `ramificationIdx'_algebra_tower'` and
-- `ramificationIdx'_ne_zero_of_liesOver`, for the counting step.
import Mathlib.NumberTheory.RamificationInertia.Ramification

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

/-- A valuation subring, its field, and any algebra over the field form
a scalar tower. This general form enables `IntermediateField.algebra'`
as a second route to `Algebra O ↥M` (divergent `IntegralClosure`
elaborations); consumers hitting the resulting synthesis failures apply
`set_option backward.isDefEq.respectTransparency false in`. -/
instance instIsScalarTowerValuationSubring {K L : Type*} [Field K] [Semiring L]
    (O : ValuationSubring K) [Algebra K L] :
    IsScalarTower O K L :=
  IsScalarTower.of_algebraMap_eq' rfl

section FiniteLevel

variable (N : Type*) [Field N]
  [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]
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

/-- The completed integer ring is a PROPER valuation subring of `Kᵥ`
(otherwise it would be a field, contradicting `𝔪ᵥ ≠ ⊥` from its DVR
structure). -/
theorem adicCompletionIntegers_ne_top :
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) ≠ ⊤ := by
  intro h
  have hfield : IsField 𝒪ᵥ :=
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := mul_comm
      mul_inv_cancel := by
        intro a ha
        have ha0 : (a : Kᵥ) ≠ 0 := fun h0 => ha (Subtype.ext h0)
        refine ⟨⟨(a : Kᵥ)⁻¹, (SetLike.ext_iff.mp h ((a : Kᵥ)⁻¹)).mpr trivial⟩, ?_⟩
        exact Subtype.ext (mul_inv_cancel₀ ha0) }
  exact IsDiscreteValuationRing.not_a_field 𝒪ᵥ
    ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield)

/-- The integral closure of `𝒪ᵥ` in a finite extension of `Kᵥ`
is a discrete valuation ring: it is a valuation ring (spectral-norm
argument), Noetherian (finite separable extension of the Noetherian
integrally closed `𝒪ᵥ`), hence a PID (Bézout + Noetherian), local, and
not a field (`not_isField_integralClosure`, since `𝒪ᵥ` is proper). -/
instance isDiscreteValuationRing_integralClosure :
    IsDiscreteValuationRing (IntegralClosure 𝒪ᵥ N) := by
  haveI : IsNoetherianRing (IntegralClosure 𝒪ᵥ N) :=
    IsIntegralClosure.isNoetherianRing 𝒪ᵥ Kᵥ N (IntegralClosure 𝒪ᵥ N)
  have hnf : ¬ IsField (IntegralClosure 𝒪ᵥ N) :=
    not_isField_integralClosure 𝒪ᵥ (adicCompletionIntegers_ne_top v)
  refine { not_a_field' := ?_ }
  intro hbot
  exact hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot)

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
      Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ N)) := by
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
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[Kᵥ] N)
      (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ N)),
    Ideal.ramificationIdxIn_eq_ramificationIdx (𝔪 𝒪ᵥ)
      (𝔪 (IntegralClosure 𝒪ᵥ N)) (N ≃ₐ[Kᵥ] N),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔪 𝒪ᵥ)
      (𝔪 (IntegralClosure 𝒪ᵥ N)) (IsDiscreteValuationRing.not_a_field 𝒪ᵥ)]

end FiniteLevel

section FiniteLevelSubextension

variable (N : IntermediateField
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
  [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]

/-- The completed integer ring has finite quotients: every nonzero
ideal is a power `𝔪ᵥⁿ` (DVR ideal classification), and `𝒪ᵥ ⧸ 𝔪ᵥⁿ` is
finite by induction on `n` (`Submodule.finite_quotient_smul` against
the finite residue field). -/
theorem hasFiniteQuotients_adicCompletionIntegers :
    Ring.HasFiniteQuotients
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) := by
  constructor
  intro I hI
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪ᵥ
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hirr
  rw [hn, ← Ideal.span_singleton_pow, ← hirr.maximalIdeal_eq]
  clear hn hI
  induction n with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      haveI : Subsingleton (𝒪ᵥ ⧸ (⊤ : Ideal 𝒪ᵥ)) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      infer_instance
  | succ k ih =>
      haveI : Finite (𝒪ᵥ ⧸ (𝔪 𝒪ᵥ)) :=
        inferInstanceAs (Finite (IsLocalRing.ResidueField 𝒪ᵥ))
      haveI := ih
      have hfin := Submodule.finite_quotient_smul (I := 𝔪 𝒪ᵥ)
        (N := ((𝔪 𝒪ᵥ) ^ k : Ideal 𝒪ᵥ))
        (IsNoetherian.noetherian _)
      rw [smul_eq_mul, ← pow_succ'] at hfin
      exact hfin

/-- The tower `𝒪ᵥ ⊆ ↥M ⊆ E` for an intermediate field `M` of `E/Kᵥ`. -/
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

end FiniteLevelSubextension

section FiniteLevel

variable (N : Type*) [Field N]
  [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]
  [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]

set_option backward.isDefEq.respectTransparency false in
/-- **`e = 1` gives the ideal equality**: if the ramification index of
`𝔪ᵥ` at `𝔪_N` is `1`, then `𝔪ᵥ` generates `𝔪_N`. In the DVR `𝒪_N`
the mapped ideal is a nonzero power `(ϖⁿ)` of the uniformizer; it is
contained in `𝔪_N = (ϖ)` (so `n ≥ 1`) and not contained in `𝔪_N²`
(`ramificationIdx'_ne_one_iff`, so `n < 2`); hence `n = 1`. -/
theorem maximalIdeal_map_eq_of_ramificationIdx_eq_one
    (he : Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ N)) = 1) :
    (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ N)) =
      𝔪 (IntegralClosure 𝒪ᵥ N) := by
  -- the mapped ideal is nonzero: a nonzero element of `𝔪ᵥ` has nonzero
  -- image (the algebra map is injective)
  have hne0 : (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ N)) ≠ ⊥ := by
    obtain ⟨x, hxmem, hx0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field 𝒪ᵥ)
    intro hbot
    have himg : algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) x ∈
        (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ N)) :=
      Ideal.mem_map_of_mem _ hxmem
    rw [hbot, Ideal.mem_bot] at himg
    exact hx0 ((injective_iff_map_eq_zero _).mp
      (FaithfulSMul.algebraMap_injective 𝒪ᵥ (IntegralClosure 𝒪ᵥ N)) x himg)
  -- the mapped ideal sits inside `𝔪_N` (the proven `LiesOver`)
  have hle1 : (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ N)) ≤
      𝔪 (IntegralClosure 𝒪ᵥ N) :=
    Ideal.map_le_iff_le_comap.mpr
      (le_of_eq (liesOver_maximalIdeal_integralClosure v N).over)
  -- but not inside `𝔪_N²`, since `e = 1`
  have hnotsq : ¬ (𝔪 𝒪ᵥ).map (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ N)) ≤
      (𝔪 (IntegralClosure 𝒪ᵥ N)) ^ 2 := fun hsq =>
    ((Ideal.ramificationIdx'_ne_one_iff hle1).mpr hsq) he
  -- classify the mapped ideal as a power of the uniformizer
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible
    (IntegralClosure 𝒪ᵥ N)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne0 hirr
  have hmax : 𝔪 (IntegralClosure 𝒪ᵥ N) = Ideal.span {ϖ} := hirr.maximalIdeal_eq
  -- `n ≥ 1`: otherwise the mapped ideal is everything, forcing `𝔪_N = ⊤`
  have hn1 : 1 ≤ n := by
    by_contra hn0
    have h0 : n = 0 := by omega
    rw [h0, pow_zero, Ideal.span_singleton_one] at hn
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (top_le_iff.mp (hn ▸ hle1))
  -- `n < 2`: otherwise the mapped ideal sits inside `𝔪_N²`
  have hn2 : n < 2 := by
    by_contra hge
    refine hnotsq ?_
    rw [hn, hmax, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right (by omega)
  have hn_eq : n = 1 := by omega
  rw [hn, hn_eq, pow_one, hmax]

section Transport

variable {N₂ : Type*} [Field N₂]
  [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N₂]
  [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N₂]

set_option backward.isDefEq.respectTransparency false in
/-- **Transport of the inertia condition along a `Kᵥ`-isomorphism**: if
`j : N ≃ₐ[Kᵥ] N₂`, then conjugating an inertia element of `𝔪_N` by `j`
(`AlgEquiv.autCongr`) gives an inertia element of `𝔪_{N₂}`. The induced
map on integral closures carries `𝔪` into `𝔪` because a ring map with a
two-sided inverse reflects units. -/
theorem autCongr_mem_inertia
    (j : N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N₂)
    (σ : N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N)
    (hσ : σ ∈ (𝔪 (IntegralClosure 𝒪ᵥ N)).inertia
      (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N)) :
    AlgEquiv.autCongr j σ ∈ (𝔪 (IntegralClosure 𝒪ᵥ N₂)).inertia
      (N₂ ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N₂) := by
  -- the forward and backward ring maps between the integral closures
  let f₁ : IntegralClosure 𝒪ᵥ N →+* IntegralClosure 𝒪ᵥ N₂ :=
    RingHom.codRestrict
      ((j : N →+* N₂).comp (algebraMap (IntegralClosure 𝒪ᵥ N) N))
      (integralClosure 𝒪ᵥ N₂)
      (fun x => (Algebra.IsIntegral.isIntegral (R := 𝒪ᵥ) x).map
        ((j.toAlgHom.restrictScalars 𝒪ᵥ).comp
          (IsScalarTower.toAlgHom 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) N)))
  let f₂ : IntegralClosure 𝒪ᵥ N₂ →+* IntegralClosure 𝒪ᵥ N :=
    RingHom.codRestrict
      ((j.symm : N₂ →+* N).comp (algebraMap (IntegralClosure 𝒪ᵥ N₂) N₂))
      (integralClosure 𝒪ᵥ N)
      (fun x => (Algebra.IsIntegral.isIntegral (R := 𝒪ᵥ) x).map
        ((j.symm.toAlgHom.restrictScalars 𝒪ᵥ).comp
          (IsScalarTower.toAlgHom 𝒪ᵥ (IntegralClosure 𝒪ᵥ N₂) N₂)))
  have hf21 : ∀ y : IntegralClosure 𝒪ᵥ N₂, f₁ (f₂ y) = y := fun y =>
    Subtype.ext (j.apply_symm_apply _)
  have hf12 : ∀ y : IntegralClosure 𝒪ᵥ N, f₂ (f₁ y) = y := fun y =>
    Subtype.ext (j.symm_apply_apply _)
  -- `f₁` carries the maximal ideal into the maximal ideal
  have hmax : ∀ m ∈ 𝔪 (IntegralClosure 𝒪ᵥ N), f₁ m ∈ 𝔪 (IntegralClosure 𝒪ᵥ N₂) := by
    intro m hm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm (by simpa [hf12] using hu.map f₂)
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  have hσ' := AddSubgroup.mem_inertia.mp hσ (f₂ x)
  have hpush := hmax _ hσ'
  rw [map_sub] at hpush
  have h1 : f₁ (σ • f₂ x) = (AlgEquiv.autCongr j σ) • x := by
    apply Subtype.ext
    show j (σ (j.symm x.1)) = _
    rfl
  rw [Submodule.mem_toAddSubgroup]
  rw [h1, hf21] at hpush
  exact hpush

end Transport

section IntermediateBase

variable (M' : IntermediateField
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N)

/-- The composite `𝒪_{M'} → ↥M' → N` as an algebra structure (the
canonical way `N` is an algebra over the integral closure of `𝒪ᵥ` in an
intermediate field). -/
noncomputable instance algebraIntegralClosureIntermediateAmbient :
    Algebra (IntegralClosure 𝒪ᵥ M') N :=
  ((algebraMap M' N).comp
    (algebraMap (IntegralClosure 𝒪ᵥ M') M')).toAlgebra

instance : IsScalarTower (IntegralClosure 𝒪ᵥ M') M' N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- `𝒪_N` is an algebra over `𝒪_{M'}` (elements of the smaller integral
closure are integral over `𝒪ᵥ`, hence land in the bigger one). -/
noncomputable instance algebraIntegralClosureOfIntermediate :
    Algebra (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) :=
  (RingHom.codRestrict
    (algebraMap (IntegralClosure 𝒪ᵥ M') N)
    (integralClosure 𝒪ᵥ N)
    (fun x => (Algebra.IsIntegral.isIntegral (R := 𝒪ᵥ) x).map
      ((IsScalarTower.toAlgHom 𝒪ᵥ M' N).comp
        (IsScalarTower.toAlgHom 𝒪ᵥ (IntegralClosure 𝒪ᵥ M') M')))).toAlgebra

instance : IsScalarTower (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) N :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower 𝒪ᵥ (IntegralClosure 𝒪ᵥ M') N :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq 𝒪ᵥ M' N,
      IsScalarTower.algebraMap_eq 𝒪ᵥ (IntegralClosure 𝒪ᵥ M') M',
      ← RingHom.comp_assoc]
    rfl)

instance : IsScalarTower 𝒪ᵥ (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    apply Subtype.ext
    show algebraMap 𝒪ᵥ N x = algebraMap (IntegralClosure 𝒪ᵥ M') N
      (algebraMap 𝒪ᵥ (IntegralClosure 𝒪ᵥ M') x)
    rw [← IsScalarTower.algebraMap_apply 𝒪ᵥ (IntegralClosure 𝒪ᵥ M') N])

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **`|I| = e` over the intermediate base**: for a finite Galois
`N/Kᵥ` and an intermediate field `M'`, the inertia subgroup of `𝔪_N`
inside `Gal(N/M')` has cardinality the ramification index of `𝔪_{M'}`
in `𝒪_N`. Same assembly as `card_inertia_finite_level`, with base ring
`𝒪_{M'}` (a DVR by the generalized instance) and the intermediate-base
algebra layer above. -/
theorem card_inertia_intermediate [IsGalois Kᵥ N] :
    Nat.card ((𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[M'] N)) =
      Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
        (𝔪 (IntegralClosure 𝒪ᵥ N)) := by
  -- the Galois action of `Gal(N/M')` commutes with `Kᵥ`-scalars (they
  -- factor through `M'`-scalars)
  haveI hscc : SMulCommClass (N ≃ₐ[M'] N)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N := by
    constructor
    intro g k x
    show g (k • x) = k • g x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [IsScalarTower.algebraMap_apply
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) M' N]
    exact g.commutes _
  -- fraction-ring structure on both integral closures
  haveI : IsFractionRing (IntegralClosure 𝒪ᵥ M') M' :=
    IsIntegralClosure.isFractionRing_of_finite_extension 𝒪ᵥ Kᵥ M'
      (IntegralClosure 𝒪ᵥ M')
  haveI : IsFractionRing (IntegralClosure 𝒪ᵥ N) N :=
    IsIntegralClosure.isFractionRing_of_finite_extension 𝒪ᵥ Kᵥ N
      (IntegralClosure 𝒪ᵥ N)
  -- `𝒪_N` is integral over `𝒪_{M'}`
  haveI : Algebra.IsIntegral (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) :=
    Algebra.IsIntegral.tower_top (R := 𝒪ᵥ)
  -- the Galois group of `N/M'` with invariants `𝒪_{M'}`
  haveI : IsGaloisGroup (N ≃ₐ[M'] N) (IntegralClosure 𝒪ᵥ M')
      (IntegralClosure 𝒪ᵥ N) :=
    IsGaloisGroup.of_isFractionRing (N ≃ₐ[M'] N) (IntegralClosure 𝒪ᵥ M')
      (IntegralClosure 𝒪ᵥ N) M' N
  -- finite free over the DVR `𝒪_{M'}`
  haveI : Module.Finite 𝒪ᵥ (IntegralClosure 𝒪ᵥ N) :=
    IsIntegralClosure.finite 𝒪ᵥ Kᵥ N (IntegralClosure 𝒪ᵥ N)
  haveI : Module.Finite (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) :=
    Module.Finite.of_restrictScalars_finite 𝒪ᵥ (IntegralClosure 𝒪ᵥ M')
      (IntegralClosure 𝒪ᵥ N)
  haveI : FaithfulSMul (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 := congrArg (algebraMap (IntegralClosure 𝒪ᵥ N) N) hab
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    have h2 : Function.Injective
        (algebraMap (IntegralClosure 𝒪ᵥ M') N) := by
      rw [IsScalarTower.algebraMap_eq (IntegralClosure 𝒪ᵥ M') M' N]
      exact (algebraMap M' N).injective.comp
        (IsFractionRing.injective (IntegralClosure 𝒪ᵥ M') M')
    exact h2 h1
  haveI : Module.Free (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) :=
    Module.free_of_finite_type_torsion_free'
  -- `𝔪_N` lies over `𝔪_{M'}`
  haveI hlies : (𝔪 (IntegralClosure 𝒪ᵥ N)).LiesOver
      (𝔪 (IntegralClosure 𝒪ᵥ M')) := by
    constructor
    have hmax : ((𝔪 (IntegralClosure 𝒪ᵥ N)).comap
        (algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (𝔪 (IntegralClosure 𝒪ᵥ N))
    exact (hmax.eq_of_le
      (IsLocalRing.maximalIdeal.isMaximal (IntegralClosure 𝒪ᵥ M')).ne_top
      (IsLocalRing.le_maximalIdeal hmax.ne_top)).symm
  -- the residue field of `𝔪_{M'}` is finite hence perfect
  haveI : Module.Finite 𝒪ᵥ (IntegralClosure 𝒪ᵥ M') :=
    IsIntegralClosure.finite 𝒪ᵥ Kᵥ M' (IntegralClosure 𝒪ᵥ M')
  haveI := hasFiniteQuotients_adicCompletionIntegers v
  haveI : Ring.HasFiniteQuotients (IntegralClosure 𝒪ᵥ M') :=
    Ring.HasFiniteQuotients.of_module_finite 𝒪ᵥ (IntegralClosure 𝒪ᵥ M')
  haveI : Finite ((IntegralClosure 𝒪ᵥ M') ⧸ (𝔪 (IntegralClosure 𝒪ᵥ M'))) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (IsDiscreteValuationRing.not_a_field _)
  have hsurj : Function.Surjective
      (algebraMap ((IntegralClosure 𝒪ᵥ M') ⧸ (𝔪 (IntegralClosure 𝒪ᵥ M')))
        ((𝔪 (IntegralClosure 𝒪ᵥ M')).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
        (IsLocalRing.maximalIdeal.isMaximal _))
  haveI : Finite ((𝔪 (IntegralClosure 𝒪ᵥ M')).ResidueField) :=
    Finite.of_surjective _ hsurj
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[M'] N)
      (𝔪 (IntegralClosure 𝒪ᵥ M')) (𝔪 (IntegralClosure 𝒪ᵥ N)),
    Ideal.ramificationIdxIn_eq_ramificationIdx (𝔪 (IntegralClosure 𝒪ᵥ M'))
      (𝔪 (IntegralClosure 𝒪ᵥ N)) (N ≃ₐ[M'] N),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔪 (IntegralClosure 𝒪ᵥ M'))
      (𝔪 (IntegralClosure 𝒪ᵥ N))
      (IsDiscreteValuationRing.not_a_field (IntegralClosure 𝒪ᵥ M'))]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **Restriction into the intermediate-level inertia**: an inertia
element of `𝔪_N` in `Gal(N/Kᵥ)` restricts to an inertia element of
`𝔪_{M'}` in `Gal(M'/Kᵥ)` (for normal `M'`). Same two ingredients as
the `Γ`-level restriction lemma: `restrictNormal_commutes` and the
locality of `𝒪_{M'}`. -/
theorem restrictNormalHom_mem_inertia_intermediate [Normal
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) M']
    (σ : N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N)
    (hσ : σ ∈ (𝔪 (IntegralClosure 𝒪ᵥ N)).inertia
      (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N)) :
    AlgEquiv.restrictNormalHom M' σ ∈
      (𝔪 (IntegralClosure 𝒪ᵥ M')).inertia
        (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M') := by
  rw [AddSubgroup.mem_inertia]
  intro x
  rw [AddSubgroup.mem_inertia] at hσ
  have hcomm : algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N)
      ((AlgEquiv.restrictNormalHom M' σ) • x - x) =
      σ • (algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) x) -
        algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) x := by
    rw [map_sub]
    congr 1
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes σ M'
      (algebraMap (IntegralClosure 𝒪ᵥ M') M' x)
  have hbig := hσ (algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) x)
  rw [← hcomm] at hbig
  have hproper : (𝔪 (IntegralClosure 𝒪ᵥ N)).comap
      (algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N)) ≠ ⊤ := by
    intro htop
    have h1 : (1 : IntegralClosure 𝒪ᵥ M') ∈ (𝔪 (IntegralClosure 𝒪ᵥ N)).comap
        (algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N)) :=
      htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  rw [Submodule.mem_toAddSubgroup] at hbig ⊢
  exact IsLocalRing.le_maximalIdeal hproper (Ideal.mem_comap.mpr hbig)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **Finite-level inertia surjectivity**: for normal `M' ⊆ N` over
`Kᵥ`, the restriction `Gal(N/Kᵥ) → Gal(M'/Kᵥ)` maps the inertia of
`𝔪_N` ONTO the inertia of `𝔪_{M'}`. Counting: with
`f := restriction ∘ inclusion` on `A := I(𝔪_N/Gal(N/Kᵥ))`,
`|A| = |ker f|·|range f|` (first isomorphism theorem); `ker f`
biject with `I(𝔪_N/Gal(N/M'))` (kernel of restriction is the fixing
subgroup, and the upgrade preserves the inertia condition), which has
cardinality `e(N/M')`; `|A| = e(N/Kᵥ) = e(M'/Kᵥ)·e(N/M')` (tower), so
`|range f| = e(M'/Kᵥ) = |I(𝔪_{M'})|`, and `range f ≤ I(𝔪_{M'})` by
the restriction-into lemma — hence equality. No henselian input. -/
theorem restrictNormalHom_inertia_surjective [IsGalois
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]
    [Normal (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) M']
    (τ : M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M')
    (hτ : τ ∈ (𝔪 (IntegralClosure 𝒪ᵥ M')).inertia
      (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M')) :
    ∃ σ : N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N,
      σ ∈ (𝔪 (IntegralClosure 𝒪ᵥ N)).inertia
        (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N) ∧
      AlgEquiv.restrictNormalHom M' σ = τ := by
  classical
  -- the restricted homomorphism on the inertia subgroup
  set A : Subgroup (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N) :=
    (𝔪 (IntegralClosure 𝒪ᵥ N)).inertia
      (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N) with hA
  set f : A →* (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M') :=
    (AlgEquiv.restrictNormalHom M').comp A.subtype with hf
  -- the range of `f` sits inside the target inertia
  have hrange : f.range ≤ (𝔪 (IntegralClosure 𝒪ᵥ M')).inertia
      (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M') := by
    rintro _ ⟨σ, rfl⟩
    exact restrictNormalHom_mem_inertia_intermediate v N M' σ.1 σ.2
  -- the kernel of `f` bijects with the inertia over `M'`
  have hker : Nat.card f.ker =
      Nat.card ((𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[M'] N)) := by
    refine Nat.le_antisymm ?_ ?_
    · -- forward injection: a kernel element fixes `M'`, upgrade it
      refine Nat.card_le_card_of_injective (fun σ =>
        ⟨IntermediateField.fixingSubgroupEquiv M'
          ⟨σ.1.1, (IntermediateField.restrictNormalHom_ker M') ▸ σ.2⟩, ?_⟩) ?_
      · refine AddSubgroup.mem_inertia.mpr fun x => ?_
        have hσ := AddSubgroup.mem_inertia.mp σ.1.2
        have h2 : (IntermediateField.fixingSubgroupEquiv M'
            ⟨σ.1.1, (IntermediateField.restrictNormalHom_ker M') ▸ σ.2⟩ :
            N ≃ₐ[M'] N) • x = σ.1.1 • x := by
          apply Subtype.ext
          rfl
        rw [h2]
        exact hσ x
      · intro a b hab
        have h3 := (IntermediateField.fixingSubgroupEquiv M').injective
          (Subtype.ext_iff.mp hab)
        exact Subtype.ext (Subtype.ext (congrArg
          (fun (x : M'.fixingSubgroup) =>
            (x : N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N)) h3))
    · -- backward injection: an inertia element over `M'` is in the kernel
      refine Nat.card_le_card_of_injective (fun ρ =>
        ⟨⟨((IntermediateField.fixingSubgroupEquiv M').symm ρ.1 :
          M'.fixingSubgroup).1, ?_⟩, ?_⟩) ?_
      · refine AddSubgroup.mem_inertia.mpr fun x => ?_
        have hρ := AddSubgroup.mem_inertia.mp ρ.2
        have h2 : (((IntermediateField.fixingSubgroupEquiv M').symm ρ.1 :
            M'.fixingSubgroup).1) • x = ρ.1 • x := by
          apply Subtype.ext
          show (((IntermediateField.fixingSubgroupEquiv M').symm ρ.1 :
            M'.fixingSubgroup).1) x.1 = (ρ.1 : N ≃ₐ[M'] N) x.1
          have h3 := (IntermediateField.fixingSubgroupEquiv M').apply_symm_apply ρ.1
          exact congrFun (congrArg (fun (g : N ≃ₐ[M'] N) => (g : N → N)) h3) x.1
        rw [h2]
        exact hρ x
      · show AlgEquiv.restrictNormalHom M' _ = 1
        rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker M']
        exact ((IntermediateField.fixingSubgroupEquiv M').symm ρ.1).2
      · intro a b hab
        have h3 : ((IntermediateField.fixingSubgroupEquiv M').symm a.1 :
            M'.fixingSubgroup) = (IntermediateField.fixingSubgroupEquiv M').symm b.1 :=
          Subtype.ext (congrArg (fun (x : ↥f.ker) =>
            ((x : A) : N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N))
            hab)
        exact Subtype.ext
          ((IntermediateField.fixingSubgroupEquiv M').symm.injective h3)
  -- first isomorphism: `|A| = |ker f| · |range f|`
  have hiso : Nat.card A = Nat.card f.ker * Nat.card f.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  -- the three ramification counts
  have hcA : Nat.card A = Ideal.ramificationIdx' (𝔪 𝒪ᵥ)
      (𝔪 (IntegralClosure 𝒪ᵥ N)) := card_inertia_finite_level v N
  haveI : Algebra.IsSeparable
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) M' :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) M' N
  haveI : IsGalois (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) M' :=
    { }
  have hcM : Nat.card ((𝔪 (IntegralClosure 𝒪ᵥ M')).inertia
      (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M')) =
      Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) :=
    card_inertia_finite_level v M'
  have hcJ := card_inertia_intermediate v N M'
  -- tower and positivity (as in the counting step)
  haveI hlies : (𝔪 (IntegralClosure 𝒪ᵥ N)).LiesOver
      (𝔪 (IntegralClosure 𝒪ᵥ M')) := by
    constructor
    haveI : Algebra.IsIntegral (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) :=
      Algebra.IsIntegral.tower_top (R := 𝒪ᵥ)
    have hmax : ((𝔪 (IntegralClosure 𝒪ᵥ N)).comap
        (algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (𝔪 (IntegralClosure 𝒪ᵥ N))
    exact (hmax.eq_of_le
      (IsLocalRing.maximalIdeal.isMaximal (IntegralClosure 𝒪ᵥ M')).ne_top
      (IsLocalRing.le_maximalIdeal hmax.ne_top)).symm
  haveI : FaithfulSMul (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 := congrArg (algebraMap (IntegralClosure 𝒪ᵥ N) N) hab
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    haveI : IsFractionRing (IntegralClosure 𝒪ᵥ M') M' :=
      IsIntegralClosure.isFractionRing_of_finite_extension 𝒪ᵥ Kᵥ M'
        (IntegralClosure 𝒪ᵥ M')
    have h2 : Function.Injective
        (algebraMap (IntegralClosure 𝒪ᵥ M') N) := by
      rw [IsScalarTower.algebraMap_eq (IntegralClosure 𝒪ᵥ M') M' N]
      exact (algebraMap M' N).injective.comp
        (IsFractionRing.injective (IntegralClosure 𝒪ᵥ M') M')
    exact h2 h1
  have htower := Ideal.ramificationIdx'_algebra_tower'
    (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) (𝔪 (IntegralClosure 𝒪ᵥ N))
  have hne2 : Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
      (𝔪 (IntegralClosure 𝒪ᵥ N)) ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _
      (IsDiscreteValuationRing.not_a_field (IntegralClosure 𝒪ᵥ M'))
  -- conclude `|range f| = |I(𝔪_{M'})|`, hence equality of subgroups
  have hcard_range : Nat.card f.range =
      Nat.card ((𝔪 (IntegralClosure 𝒪ᵥ M')).inertia
        (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M')) := by
    have h4 : Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
        (𝔪 (IntegralClosure 𝒪ᵥ N)) * Nat.card f.range =
        Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
          (𝔪 (IntegralClosure 𝒪ᵥ N)) *
          Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) :=
      calc Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
            (𝔪 (IntegralClosure 𝒪ᵥ N)) * Nat.card f.range
          = Nat.card f.ker * Nat.card f.range := by rw [hker, hcJ]
        _ = Nat.card A := hiso.symm
        _ = Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ N)) := hcA
        _ = Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) *
            Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
              (𝔪 (IntegralClosure 𝒪ᵥ N)) := htower
        _ = Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
              (𝔪 (IntegralClosure 𝒪ᵥ N)) *
            Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) :=
          mul_comm _ _
    rw [hcM]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne2) h4
  have heq : f.range = (𝔪 (IntegralClosure 𝒪ᵥ M')).inertia
      (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M') := by
    haveI : Finite ((𝔪 (IntegralClosure 𝒪ᵥ M')).inertia
        (M' ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] M')) :=
      Subtype.finite
    exact Subgroup.eq_of_le_of_card_ge hrange (le_of_eq hcard_range.symm)
  obtain ⟨σ, hσ⟩ := heq ▸ hτ
  exact ⟨σ.1, σ.2, hσ⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **The counting step**: if the inertia subgroup of `𝔪_N` in
`Gal(N/Kᵥ)` fixes the intermediate field `M'` pointwise, then `M'/Kᵥ`
is unramified (`e(𝔪ᵥ at 𝔪_{M'}) = 1`). Proof:
`e(N/Kᵥ) = |I(𝔪_N/Gal(N/Kᵥ))| ≤ |I(𝔪_N/Gal(N/M'))| = e(N/M')` — the
middle step upgrades inertia elements through `fixingSubgroupEquiv` —
while `e(N/Kᵥ) = e(M'/Kᵥ) · e(N/M')` by tower multiplicativity; since
`e(N/M') ≠ 0`, this forces `e(M'/Kᵥ) ≤ 1`, and `e ≠ 0` always. -/
theorem ramificationIdx_eq_one_of_inertia_le_fixingSubgroup [IsGalois Kᵥ N]
    (hfix : ((𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[Kᵥ] N) : Set (N ≃ₐ[Kᵥ] N)) ⊆
      (M'.fixingSubgroup : Set (N ≃ₐ[Kᵥ] N))) :
    Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) = 1 := by
  -- the two counted inertia groups
  have hc1 := card_inertia_finite_level v N
  have hc2 := card_inertia_intermediate v N M'
  -- upgrade: an inertia element over `Kᵥ` fixing `M'` is an inertia
  -- element over `M'` (same underlying map)
  have hinj : Nat.card ((𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[Kᵥ] N)) ≤
      Nat.card ((𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[M'] N)) := by
    have hmem : ∀ σ : ((𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[Kᵥ] N)),
        (IntermediateField.fixingSubgroupEquiv M' ⟨σ.1, hfix σ.2⟩ :
          N ≃ₐ[M'] N) ∈ (𝔪 (IntegralClosure 𝒪ᵥ N)).inertia (N ≃ₐ[M'] N) := by
      intro σ
      rw [AddSubgroup.mem_inertia]
      intro x
      have hσ := σ.2
      rw [AddSubgroup.mem_inertia] at hσ
      have h1 := hσ x
      -- the two actions have the same underlying function
      have h2 : (IntermediateField.fixingSubgroupEquiv M' ⟨σ.1, hfix σ.2⟩ :
          N ≃ₐ[M'] N) • x = σ.1 • x := by
        apply Subtype.ext
        rfl
      rwa [h2]
    refine Nat.card_le_card_of_injective
      (fun σ => ⟨IntermediateField.fixingSubgroupEquiv M' ⟨σ.1, hfix σ.2⟩, hmem σ⟩) ?_
    intro a b hab
    have h3 : (⟨a.1, hfix a.2⟩ : M'.fixingSubgroup) = ⟨b.1, hfix b.2⟩ :=
      (IntermediateField.fixingSubgroupEquiv M').injective (Subtype.ext_iff.mp hab)
    exact Subtype.ext (congrArg
      (fun (x : M'.fixingSubgroup) => (x : N ≃ₐ[Kᵥ] N)) h3)
  -- tower multiplicativity
  haveI hlies : (𝔪 (IntegralClosure 𝒪ᵥ N)).LiesOver
      (𝔪 (IntegralClosure 𝒪ᵥ M')) := by
    constructor
    haveI : Algebra.IsIntegral (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) :=
      Algebra.IsIntegral.tower_top (R := 𝒪ᵥ)
    have hmax : ((𝔪 (IntegralClosure 𝒪ᵥ N)).comap
        (algebraMap (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (𝔪 (IntegralClosure 𝒪ᵥ N))
    exact (hmax.eq_of_le
      (IsLocalRing.maximalIdeal.isMaximal (IntegralClosure 𝒪ᵥ M')).ne_top
      (IsLocalRing.le_maximalIdeal hmax.ne_top)).symm
  haveI : FaithfulSMul (IntegralClosure 𝒪ᵥ M') (IntegralClosure 𝒪ᵥ N) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 := congrArg (algebraMap (IntegralClosure 𝒪ᵥ N) N) hab
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    haveI : IsFractionRing (IntegralClosure 𝒪ᵥ M') M' :=
      IsIntegralClosure.isFractionRing_of_finite_extension 𝒪ᵥ Kᵥ M'
        (IntegralClosure 𝒪ᵥ M')
    have h2 : Function.Injective
        (algebraMap (IntegralClosure 𝒪ᵥ M') N) := by
      rw [IsScalarTower.algebraMap_eq (IntegralClosure 𝒪ᵥ M') M' N]
      exact (algebraMap M' N).injective.comp
        (IsFractionRing.injective (IntegralClosure 𝒪ᵥ M') M')
    exact h2 h1
  have htower := Ideal.ramificationIdx'_algebra_tower'
    (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) (𝔪 (IntegralClosure 𝒪ᵥ N))
  -- positivity of the upper ramification index
  have hne2 : Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
      (𝔪 (IntegralClosure 𝒪ᵥ N)) ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _
      (IsDiscreteValuationRing.not_a_field (IntegralClosure 𝒪ᵥ M'))
  have hne1 : Ideal.ramificationIdx' (𝔪 𝒪ᵥ)
      (𝔪 (IntegralClosure 𝒪ᵥ M')) ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _
      (IsDiscreteValuationRing.not_a_field 𝒪ᵥ)
  -- combine: `e₁ · e₂ = e ≤ e₂` with `e₂ ≠ 0` forces `e₁ = 1`
  rw [hc1, hc2, htower] at hinj
  have hle : Ideal.ramificationIdx' (𝔪 𝒪ᵥ) (𝔪 (IntegralClosure 𝒪ᵥ M')) *
      Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
        (𝔪 (IntegralClosure 𝒪ᵥ N)) ≤
      1 * Ideal.ramificationIdx' (𝔪 (IntegralClosure 𝒪ᵥ M'))
        (𝔪 (IntegralClosure 𝒪ᵥ N)) := by
    rw [one_mul]
    exact hinj
  have hle1 := Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero hne2)
  omega

end IntermediateBase

end FiniteLevel

section FiniteLevelSubextension

variable (N : IntermediateField
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
  [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]

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

end FiniteLevelSubextension

section Reify

variable (N N' : IntermediateField
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))

/-- `N` reified as an intermediate field of `↥N'` (the pullback of `N`
along the inclusion of `N'`). -/
noncomputable def reifySubextension : IntermediateField
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N' :=
  IntermediateField.comap N'.val N

/-- The canonical `Kᵥ`-isomorphism between the reification of `N`
inside `↥N'` and `N` itself. -/
noncomputable def reifyEquiv (h : N ≤ N') :
    ↥(reifySubextension v N N') ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v]
      ↥N :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨(x.1 : AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
    ⟨fun _ _ hab => Subtype.ext (Subtype.ext (congrArg
      (fun (y : ↥N) => (y : AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) hab)),
     fun y => ⟨⟨⟨(y : AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)), h y.2⟩, y.2⟩,
      rfl⟩⟩

theorem normal_reifySubextension (h : N ≤ N') [IsGalois
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N] :
    Normal (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      ↥(reifySubextension v N N') :=
  Normal.of_algEquiv (reifyEquiv v N N' h).symm

end Reify

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

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

/-- The integral closure of `𝒪ᵥ` in a finite subextension of `Kᵥᵃˡᵍ`
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
      Ideal.ramificationIdxIn (𝔪 (IntegralClosure 𝒪ᵥ M'))
        (IntegralClosure 𝒪ᵥ N) := by
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
  exact Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[M'] N)
    (𝔪 (IntegralClosure 𝒪ᵥ M')) (𝔪 (IntegralClosure 𝒪ᵥ N))

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

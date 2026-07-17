/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Deyao Chen
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, used to state the
-- shared flat transport at a rational prime
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- `WithConv` and its convolution monoid, the group structure on the
-- points of the vendored DVR-package
public import Mathlib.RingTheory.HopfAlgebra.Convolution
-- the Hopf-algebra instance on `𝒪ᵥ ⊗[R] H` (base change), used by the
-- flat-prolongation transport core
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
-- `localizationToAdicCompletionIntegers` (the arc `ℤ_(q) → 𝒪ᵥ`), used
-- in the proof of the rational-prime instantiation
import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField

/-!
# Transport layers for flat prolongations

This file hosts the transport machinery turning the vendored
finite-flat-prolongation leaf (`torsion_flat_of_good_reduction`, stated
over an abstract DVR) into the `GaloisRep.HasFlatProlongationAt`
package at a place of `ℚ` (which lives over the COMPLETED integers
`𝒪ᵥ`). This file starts with the degenerate case: a representation on
a subsingleton module has a flat prolongation everywhere (witnessed by
the trivial Hopf algebra `𝒪ᵥ` itself), which discharges the `I = ⊤`
case of the open-ideal quantifier in `GaloisRep.IsFlatAt`.
-/

@[expose] public section

open NumberField TensorProduct

universe uKf

variable {K : Type uKf} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {M : Type*} [AddCommGroup M] [Module A M]

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- Every element of `Kᵥᵃˡᵍ` that is integral (= algebraic) over `K`
lies in the image of the chosen embedding `ι : Kᵃˡᵍ → Kᵥᵃˡᵍ`: its
minimal polynomial over `K` splits already over `Kᵃˡᵍ`, and the roots
of the pushed-forward polynomial are exactly the `ι`-images of the
roots upstairs. This is the factorization input for the flat-transport
points comparison (finite `K`-algebra maps into `Kᵥᵃˡᵍ` land in
`ι(Kᵃˡᵍ)`). -/
theorem mem_range_algebraicClosureMap_of_isIntegral
    (z : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    (hz : IsIntegral K z) :
    z ∈ Set.range (AlgebraicClosure.map
      (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) := by
  classical
  have hμ0 : minpoly K z ≠ 0 := minpoly.ne_zero hz
  -- the minimal polynomial splits over `Kᵃˡᵍ`
  have hsplit : ((minpoly K z).map
      (algebraMap K (AlgebraicClosure K))).Splits :=
    IsAlgClosed.splits ((minpoly K z).map (algebraMap K (AlgebraicClosure K)))
  -- push the polynomial to `Kᵥᵃˡᵍ` through `ι`
  have hfactor : (minpoly K z).map (algebraMap K
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) =
      ((minpoly K z).map (algebraMap K (AlgebraicClosure K))).map
        (AlgebraicClosure.map
          (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) := by
    rw [Polynomial.map_map]
    congr 1
    refine RingHom.ext fun x => ?_
    exact (AlgebraicClosure.map_algebraMap
      (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) x).symm
  -- `z` is a root of the pushed polynomial
  have hroot : z ∈ ((minpoly K z).map (algebraMap K
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))).roots := by
    rw [Polynomial.mem_roots
      (Polynomial.map_ne_zero_iff (algebraMap K _).injective |>.mpr hμ0)]
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval K z
  -- the roots downstairs are the `ι`-images of the roots upstairs
  rw [hfactor, Polynomial.Splits.roots_map hsplit, Multiset.mem_map] at hroot
  obtain ⟨r, _, hr⟩ := hroot
  exact ⟨r, hr⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The chosen embedding of algebraic closures, packaged as a
`K`-algebra homomorphism. -/
noncomputable def algebraicClosureMapAlgHom :
    AlgebraicClosure K →ₐ[K]
      AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
  { toRingHom := AlgebraicClosure.map
      (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    commutes' := fun x => by
      show AlgebraicClosure.map
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        (algebraMap K (AlgebraicClosure K) x) = _
      rw [AlgebraicClosure.map_algebraMap
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) x]
      exact (IsScalarTower.algebraMap_apply K
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) x).symm }

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Layer C of the flat-transport points comparison**: for a finite
`K`-algebra `B`, postcomposition with the embedding `ι` is a bijection
between the `Kᵃˡᵍ`-points and the `Kᵥᵃˡᵍ`-points of `B` (every map to
`Kᵥᵃˡᵍ` has algebraic image, hence factors through `ι(Kᵃˡᵍ)`). -/
noncomputable def algHomEquivOfFinite (B : Type*) [CommRing B] [Algebra K B]
    [Module.Finite K B] :
    (B →ₐ[K] AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) ≃
    (B →ₐ[K] AlgebraicClosure K) where
  toFun φ := (AlgEquiv.ofInjective (algebraicClosureMapAlgHom v)
      (algebraicClosureMapAlgHom v).toRingHom.injective).symm.toAlgHom.comp
    (φ.codRestrict (algebraicClosureMapAlgHom v).range (fun b => by
      obtain ⟨r, hr⟩ := mem_range_algebraicClosureMap_of_isIntegral v (φ b)
        ((Algebra.IsIntegral.isIntegral (R := K) b).map φ)
      exact ⟨r, hr⟩))
  invFun ψ := (algebraicClosureMapAlgHom v).comp ψ
  left_inv φ := by
    refine AlgHom.ext fun b => ?_
    have h1 := congrArg Subtype.val
      ((AlgEquiv.ofInjective (algebraicClosureMapAlgHom v) (algebraicClosureMapAlgHom v).toRingHom.injective).apply_symm_apply
        (φ.codRestrict (algebraicClosureMapAlgHom v).range (fun b => by
          obtain ⟨r, hr⟩ := mem_range_algebraicClosureMap_of_isIntegral v (φ b)
            ((Algebra.IsIntegral.isIntegral (R := K) b).map φ)
          exact ⟨r, hr⟩) b))
    exact h1
  right_inv ψ := by
    refine AlgHom.ext fun b => ?_
    apply (AlgEquiv.ofInjective (algebraicClosureMapAlgHom v) (algebraicClosureMapAlgHom v).toRingHom.injective).injective
    refine ((AlgEquiv.ofInjective (algebraicClosureMapAlgHom v)
      (algebraicClosureMapAlgHom v).toRingHom.injective).apply_symm_apply _).trans ?_
    apply Subtype.ext
    rfl

section AlgHomEquivConv

open WithConv

section PlainAlgebra

variable {B : Type*} [CommRing B] [Algebra K B] [Module.Finite K B]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The inverse of `algHomEquivOfFinite` is postcomposition with the
embedding `ι = algebraicClosureMapAlgHom`. -/
theorem algHomEquivOfFinite_symm_apply (ψ : B →ₐ[K] (AlgebraicClosure K)) :
    (algHomEquivOfFinite v B).symm ψ = (algebraicClosureMapAlgHom v).comp ψ :=
  rfl

end PlainAlgebra

variable {B : Type*} [CommRing B] [Bialgebra K B] [Module.Finite K B]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- `algHomEquivOfFinite` preserves the convolution unit. -/
theorem algHomEquivOfFinite_convOne :
    algHomEquivOfFinite v B
      ((1 : WithConv (B →ₐ[K] (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))).ofConv) =
      (1 : WithConv (B →ₐ[K] (AlgebraicClosure K))).ofConv := by
  apply (algHomEquivOfFinite v B).symm.injective
  rw [Equiv.symm_apply_apply, algHomEquivOfFinite_symm_apply]
  refine AlgHom.ext fun b => ?_
  rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply,
    AlgHom.commutes]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- `algHomEquivOfFinite` preserves the convolution product
(postcomposition with the algebra hom `ι` distributes over
convolution, `AlgHom.comp_convMul_distrib`). -/
theorem algHomEquivOfFinite_convMul
    (ψ₁ ψ₂ : WithConv (B →ₐ[K] (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))) :
    algHomEquivOfFinite v B ((ψ₁ * ψ₂).ofConv) =
      (toConv (algHomEquivOfFinite v B ψ₁.ofConv) *
        toConv (algHomEquivOfFinite v B ψ₂.ofConv)).ofConv := by
  apply (algHomEquivOfFinite v B).symm.injective
  rw [Equiv.symm_apply_apply, algHomEquivOfFinite_symm_apply,
    AlgHom.comp_convMul_distrib,
    ← algHomEquivOfFinite_symm_apply v (algHomEquivOfFinite v B ψ₁.ofConv),
    ← algHomEquivOfFinite_symm_apply v (algHomEquivOfFinite v B ψ₂.ofConv),
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- `algHomEquivOfFinite` intertwines postcomposition with a local
Galois element `σ : Γ Kᵥ` and postcomposition with its restriction
`map σ : Γ K` (through `Field.absoluteGaloisGroup.lift_map`). -/
theorem algHomEquivOfFinite_comp
    (σ : Γ(IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    (ψ : B →ₐ[K] (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) :
    algHomEquivOfFinite v B ((σ.toAlgHom.restrictScalars K).comp ψ) =
      (Field.absoluteGaloisGroup.map (algebraMap K
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) σ).toAlgHom.comp
        (algHomEquivOfFinite v B ψ) := by
  apply (algHomEquivOfFinite v B).symm.injective
  rw [Equiv.symm_apply_apply, algHomEquivOfFinite_symm_apply]
  have h2 : (algebraicClosureMapAlgHom v).comp (algHomEquivOfFinite v B ψ) = ψ := by
    rw [← algHomEquivOfFinite_symm_apply, Equiv.symm_apply_apply]
  refine AlgHom.ext fun b => ?_
  refine Eq.symm ?_
  calc ((algebraicClosureMapAlgHom v).comp
        ((Field.absoluteGaloisGroup.map (algebraMap K
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) σ).toAlgHom.comp
          (algHomEquivOfFinite v B ψ))) b
      = σ (AlgebraicClosure.map (algebraMap K
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
          ((algHomEquivOfFinite v B ψ) b)) :=
        Field.absoluteGaloisGroup.lift_map _ σ _
    _ = σ (ψ b) := congrArg σ congr($(h2) b)
    _ = ((σ.toAlgHom.restrictScalars K).comp ψ) b := rfl

end AlgHomEquivConv

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- Transport of `GaloisRep.HasFlatProlongationAt` along an equivariant
additive equivalence of the underlying spaces. The flat-prolongation
package mentions the representation space only through its additive
group and its `Γ Kᵥ`-action, so any additive identification commuting
with the two (global) Galois actions carries the package across. -/
theorem GaloisRep.HasFlatProlongationAt.of_addEquiv
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {A' : Type*} [CommRing A'] [TopologicalSpace A']
    {M' : Type*} [AddCommGroup M'] [Module A' M']
    {ρ : GaloisRep K A M} {ρ' : GaloisRep K A' M'}
    (h : ρ.HasFlatProlongationAt w)
    (e : M ≃+ M')
    (he : ∀ (σ : Γ K) (x : M), e (ρ σ x) = ρ' σ (e x)) :
    ρ'.HasFlatProlongationAt w := by
  obtain ⟨G, hCR, hHopf, hFlat, hFin, hEt, f, hbij⟩ := h
  letI := hCR
  letI := hHopf
  letI := hFlat
  letI := hFin
  refine ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, hEt,
    { toFun := fun x => e (f x)
      map_smul' := fun σ x => by
        show e (f (σ • x)) = (ρ'.toLocal w) σ (e (f x))
        rw [map_smul f σ x]
        show e ((ρ.toLocal w) σ (f x)) = (ρ'.toLocal w) σ (e (f x))
        exact he _ _
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun a b => by rw [map_add, map_add] },
    e.bijective.comp hbij⟩

section LiftEquivConv

open WithConv

variable {R S H₀ B₀ : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing H₀] [Bialgebra R H₀]
variable [CommRing B₀] [Algebra R B₀] [Algebra S B₀] [IsScalarTower R S B₀]

/-- The unit of the convolution monoid is preserved by the tensor-hom
adjunction `AlgHom.liftEquiv` (inverse direction): restricting the
counit-unit of `S ⊗[R] H₀` along `includeRight` gives the counit-unit
of `H₀`. -/
theorem liftEquiv_symm_convOne :
    (AlgHom.liftEquiv R S H₀ B₀).symm
      ((1 : WithConv (S ⊗[R] H₀ →ₐ[S] B₀)).ofConv) =
      (1 : WithConv (H₀ →ₐ[R] B₀)).ofConv := by
  refine AlgHom.ext fun a => ?_
  rw [AlgHom.liftEquiv_symm_apply]
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  rw [congr($(Bialgebra.TensorProduct.counit_eq_algHom_toLinearMap R S S H₀)
    (1 ⊗ₜ[R] a))]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The convolution product is preserved by the tensor-hom adjunction
`AlgHom.liftEquiv` (inverse direction, mixed base rings `R ⊆ S`): the
comultiplication of the base-changed bialgebra `S ⊗[R] H₀` restricts
along `includeRight` to the comultiplication of `H₀`. -/
theorem liftEquiv_symm_convMul (f g : WithConv (S ⊗[R] H₀ →ₐ[S] B₀)) :
    (AlgHom.liftEquiv R S H₀ B₀).symm ((f * g).ofConv) =
      (toConv ((AlgHom.liftEquiv R S H₀ B₀).symm f.ofConv) *
        toConv ((AlgHom.liftEquiv R S H₀ B₀).symm g.ofConv)).ofConv := by
  refine AlgHom.ext fun a => ?_
  rw [AlgHom.liftEquiv_symm_apply, AlgHom.convMul_apply, AlgHom.convMul_apply]
  -- compute `comul (1 ⊗ₜ a)` on the base-changed bialgebra
  have hcomul : (Coalgebra.comul (R := S) (A := S ⊗[R] H₀)) (1 ⊗ₜ[R] a) =
      (Algebra.TensorProduct.tensorTensorTensorComm R S R S S S H₀ H₀).toAlgHom
        ((1 : S ⊗[S] S) ⊗ₜ[R] (Coalgebra.comul (R := R) a)) := by
    rw [congr($(Bialgebra.TensorProduct.comul_eq_algHom_toLinearMap R S S H₀)
      (1 ⊗ₜ[R] a))]
    simp [Algebra.TensorProduct.one_def]
  rw [hcomul]
  induction Coalgebra.comul (R := R) a with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.one_def]
    simp [AlgHom.liftEquiv_symm_apply]

/-- The tensor-hom adjunction commutes with postcomposition (inverse
direction): both sides precompose with `includeRight`. -/
theorem liftEquiv_symm_comp (h : B₀ →ₐ[S] B₀) (f : S ⊗[R] H₀ →ₐ[S] B₀) :
    (AlgHom.liftEquiv R S H₀ B₀).symm (h.comp f) =
      (h.restrictScalars R).comp ((AlgHom.liftEquiv R S H₀ B₀).symm f) :=
  rfl

/-- Forward direction of `liftEquiv_symm_convOne`, by injectivity of
the inverse. -/
theorem liftEquiv_convOne :
    AlgHom.liftEquiv R S H₀ B₀ ((1 : WithConv (H₀ →ₐ[R] B₀)).ofConv) =
      (1 : WithConv (S ⊗[R] H₀ →ₐ[S] B₀)).ofConv := by
  apply (AlgHom.liftEquiv R S H₀ B₀).symm.injective
  rw [Equiv.symm_apply_apply, liftEquiv_symm_convOne]

/-- Forward direction of `liftEquiv_symm_convMul`, by injectivity of
the inverse. -/
theorem liftEquiv_convMul (χ₁ χ₂ : WithConv (H₀ →ₐ[R] B₀)) :
    AlgHom.liftEquiv R S H₀ B₀ ((χ₁ * χ₂).ofConv) =
      (toConv (AlgHom.liftEquiv R S H₀ B₀ χ₁.ofConv) *
        toConv (AlgHom.liftEquiv R S H₀ B₀ χ₂.ofConv)).ofConv := by
  apply (AlgHom.liftEquiv R S H₀ B₀).symm.injective
  rw [Equiv.symm_apply_apply, liftEquiv_symm_convMul]
  simp

/-- Forward direction of `liftEquiv_symm_comp`, by injectivity of the
inverse. -/
theorem liftEquiv_comp (h : B₀ →ₐ[S] B₀) (χ : H₀ →ₐ[R] B₀) :
    AlgHom.liftEquiv R S H₀ B₀ ((h.restrictScalars R).comp χ) =
      h.comp (AlgHom.liftEquiv R S H₀ B₀ χ) := by
  apply (AlgHom.liftEquiv R S H₀ B₀).symm.injective
  rw [Equiv.symm_apply_apply, liftEquiv_symm_comp, Equiv.symm_apply_apply]

end LiftEquivConv

section VendoredConvBridge

open WithConv

universe uv

variable {K₀ L₀ : Type uv} [Field K₀] [Field L₀] [Algebra K₀ L₀]
variable {A₀ : Type*} [CommRing A₀] [Bialgebra K₀ A₀]

/-- The vendored bare-hom convolution monoid on `A₀ →ₐ[K₀] L₀` (the
instance in `Deformations/RepresentationTheory/Etale.lean`, used by
`GaloisRep.HasFlatProlongationAt`) has the SAME unit as mathlib's
`WithConv` convolution monoid. -/
theorem vendored_one_eq_convOne :
    (1 : A₀ →ₐ[K₀] L₀) = (1 : WithConv (A₀ →ₐ[K₀] L₀)).ofConv :=
  rfl

/-- The vendored bare-hom convolution monoid on `A₀ →ₐ[K₀] L₀` has the
SAME multiplication as mathlib's `WithConv` convolution monoid: both
are `lift φ ψ ∘ comul`. -/
theorem vendored_mul_eq_convMul (φ ψ : A₀ →ₐ[K₀] L₀) :
    φ * ψ = (toConv φ * toConv ψ).ofConv := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.convMul_apply]
  rfl

end VendoredConvBridge

section DVRPackageCore

open WithConv

variable (R : Type uKf) [CommRing R]
  [Algebra R K]
  [Algebra R (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)]
  [Algebra R (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)]
  [IsScalarTower R (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)]
  [IsScalarTower R K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)]
variable (H : Type uKf) [CommRing H] [HopfAlgebra R H] [Module.Finite R H]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The four-layer points comparison** for the flat-prolongation
transport: the `Kᵥᵃˡᵍ`-points of the generic fibre of the base-changed
Hopf algebra `𝒪ᵥ ⊗[R] H` are the `Kᵃˡᵍ`-points of `K ⊗[R] H`
(`AlgHom.liftEquiv` three times, then `algHomEquivOfFinite`). -/
noncomputable def dvrPointsEquiv :
    ((Kᵥ ⊗[𝒪ᵥ] (𝒪ᵥ ⊗[R] H)) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)) ≃ ((K ⊗[R] H) →ₐ[K] (Kᵃˡᵍ)) :=
  (AlgHom.liftEquiv 𝒪ᵥ Kᵥ (𝒪ᵥ ⊗[R] H) (Kᵥᵃˡᵍ)).symm.trans
    ((AlgHom.liftEquiv R 𝒪ᵥ H (Kᵥᵃˡᵍ)).symm.trans
      ((AlgHom.liftEquiv R K H (Kᵥᵃˡᵍ)).trans
        (algHomEquivOfFinite v (K ⊗[R] H))))

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- The points comparison sends the convolution unit (of the vendored
bare-hom monoid) to the convolution unit. -/
theorem dvrPointsEquiv_one :
    dvrPointsEquiv v R H (1 : (Kᵥ ⊗[𝒪ᵥ] (𝒪ᵥ ⊗[R] H)) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)) =
      (1 : WithConv ((K ⊗[R] H) →ₐ[K] (Kᵃˡᵍ))).ofConv := by
  show algHomEquivOfFinite v (K ⊗[R] H)
    ((AlgHom.liftEquiv R K H (Kᵥᵃˡᵍ))
      ((AlgHom.liftEquiv R 𝒪ᵥ H (Kᵥᵃˡᵍ)).symm
        ((AlgHom.liftEquiv 𝒪ᵥ Kᵥ (𝒪ᵥ ⊗[R] H) (Kᵥᵃˡᵍ)).symm 1))) = _
  rw [vendored_one_eq_convOne, liftEquiv_symm_convOne, liftEquiv_symm_convOne,
    liftEquiv_convOne, algHomEquivOfFinite_convOne]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- The points comparison sends the convolution product (of the
vendored bare-hom monoid) to the convolution product. -/
theorem dvrPointsEquiv_mul (φ ψ : (Kᵥ ⊗[𝒪ᵥ] (𝒪ᵥ ⊗[R] H)) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)) :
    dvrPointsEquiv v R H (φ * ψ) =
      (toConv (dvrPointsEquiv v R H φ) * toConv (dvrPointsEquiv v R H ψ)).ofConv := by
  show algHomEquivOfFinite v (K ⊗[R] H)
    ((AlgHom.liftEquiv R K H (Kᵥᵃˡᵍ))
      ((AlgHom.liftEquiv R 𝒪ᵥ H (Kᵥᵃˡᵍ)).symm
        ((AlgHom.liftEquiv 𝒪ᵥ Kᵥ (𝒪ᵥ ⊗[R] H) (Kᵥᵃˡᵍ)).symm (φ * ψ)))) = _
  rw [vendored_mul_eq_convMul, liftEquiv_symm_convMul, liftEquiv_symm_convMul,
    liftEquiv_convMul, algHomEquivOfFinite_convMul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- The points comparison intertwines the postcomposition action of
`Γ Kᵥ` with the postcomposition action of its restriction in `Γ K`. -/
theorem dvrPointsEquiv_smul
    (σ : Γ(IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    (φ : (Kᵥ ⊗[𝒪ᵥ] (𝒪ᵥ ⊗[R] H)) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)) :
    dvrPointsEquiv v R H (σ • φ) =
      (Field.absoluteGaloisGroup.map (algebraMap K
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) σ).toAlgHom.comp
        (dvrPointsEquiv v R H φ) := by
  have h₀ : σ • φ = (σ.toAlgHom : (Kᵥᵃˡᵍ) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)).comp φ :=
    AlgHom.ext fun _ => rfl
  show algHomEquivOfFinite v (K ⊗[R] H)
    ((AlgHom.liftEquiv R K H (Kᵥᵃˡᵍ))
      ((AlgHom.liftEquiv R 𝒪ᵥ H (Kᵥᵃˡᵍ)).symm
        ((AlgHom.liftEquiv 𝒪ᵥ Kᵥ (𝒪ᵥ ⊗[R] H) (Kᵥᵃˡᵍ)).symm (σ • φ)))) = _
  rw [h₀, liftEquiv_symm_comp, liftEquiv_symm_comp]
  have hrs : ((σ.toAlgHom.restrictScalars 𝒪ᵥ).restrictScalars R :
      (Kᵥᵃˡᵍ) →ₐ[R] (Kᵥᵃˡᵍ)) =
      ((σ.toAlgHom.restrictScalars K).restrictScalars R) := rfl
  rw [hrs, liftEquiv_comp, algHomEquivOfFinite_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The core of the shared flat-prolongation transport**, over a
general number field `K` and abstract coefficient ring `R` mapping
compatibly into `K` and `𝒪ᵥ`: a Galois representation whose space is
presented, `Γ K`-equivariantly, as the `Kᵃˡᵍ`-points of the generic
fibre of a finite flat Hopf algebra `H` over `R` has a flat
prolongation at `v`, witnessed by the base change `𝒪ᵥ ⊗[R] H`. -/
theorem GaloisRep.hasFlatProlongationAt_of_hopf_package
    (ρ : GaloisRep K A M)
    [Module.Flat R H]
    [Algebra.Etale K (K ⊗[R] H)]
    (f : Additive (WithConv ((K ⊗[R] H) →ₐ[K] (Kᵃˡᵍ))) ≃+ M)
    (hf : ∀ (σ : (Kᵃˡᵍ) ≃ₐ[K] (Kᵃˡᵍ)) (φ : (K ⊗[R] H) →ₐ[K] (Kᵃˡᵍ)),
      f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
        ρ σ (f (Additive.ofMul (WithConv.toConv φ)))) :
    ρ.HasFlatProlongationAt v := by
  classical
  refine ⟨𝒪ᵥ ⊗[R] H,
    (inferInstance : CommRing (𝒪ᵥ ⊗[R] H)),
    (inferInstance : HopfAlgebra 𝒪ᵥ (𝒪ᵥ ⊗[R] H)),
    (inferInstance : Module.Flat 𝒪ᵥ (𝒪ᵥ ⊗[R] H)),
    (inferInstance : Module.Finite 𝒪ᵥ (𝒪ᵥ ⊗[R] H)),
    Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R K Kᵥ Kᵥ H).trans
      (Algebra.TensorProduct.cancelBaseChange R 𝒪ᵥ Kᵥ Kᵥ H).symm),
    { toFun := fun Φ =>
        f (Additive.ofMul (WithConv.toConv (dvrPointsEquiv v R H Φ.toMul)))
      map_smul' := fun σ Φ => by
        show f (Additive.ofMul (WithConv.toConv
            (dvrPointsEquiv v R H (Additive.toMul (σ • Φ))))) =
          ((ρ.toLocal v) σ) (f (Additive.ofMul (WithConv.toConv
            (dvrPointsEquiv v R H Φ.toMul))))
        have hΦ : Additive.toMul (σ • Φ) = σ • Φ.toMul := rfl
        rw [hΦ, dvrPointsEquiv_smul]
        exact hf (Field.absoluteGaloisGroup.map (algebraMap K
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) σ) _
      map_zero' := by
        show f (Additive.ofMul (WithConv.toConv
            (dvrPointsEquiv v R H (Additive.toMul 0)))) = 0
        have h0 : Additive.toMul
            (0 : Additive ((Kᵥ ⊗[𝒪ᵥ] (𝒪ᵥ ⊗[R] H)) →ₐ[Kᵥ] (Kᵥᵃˡᵍ))) = 1 := rfl
        rw [h0, dvrPointsEquiv_one, WithConv.toConv_ofConv]
        exact map_zero f
      map_add' := fun Φ Ψ => by
        show f (Additive.ofMul (WithConv.toConv
            (dvrPointsEquiv v R H (Additive.toMul (Φ + Ψ))))) = _
        have hΦΨ : Additive.toMul (Φ + Ψ) = Φ.toMul * Ψ.toMul := rfl
        rw [hΦΨ, dvrPointsEquiv_mul, WithConv.toConv_ofConv]
        exact map_add f _ _ }, ?_⟩
  -- bijectivity
  exact f.bijective.comp (Additive.ofMul.bijective.comp
    (WithConv.toConv_bijective.comp
      ((dvrPointsEquiv v R H).bijective.comp Additive.toMul.bijective)))

end DVRPackageCore

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The shared flat-prolongation transport, core** (DERIVED
2026-07-17 from `hasFlatProlongationAt_of_hopf_package`): a Galois
representation of `ℚ` whose space is presented, equivariantly, as the
`ℚ̄`-points of the generic fibre of a finite flat Hopf algebra over the
localization `ℤ_(q)` has a flat prolongation at `q`. The instantiation
equips `𝒪ᵥ` and `Kᵥ` with their `ℤ_(q)`-algebra structures through the
proven arc `ℤ_(q) → ℚ → Kᵥ` (`localizationToAdicCompletionIntegers`),
under which the scalar towers hold definitionally. -/
theorem GaloisRep.hasFlatProlongationAt_of_dvr_package
    {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {M : Type} [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    (ρ : GaloisRep ℚ A M)
    {q : ℕ} (hq : q.Prime)
    [Algebra (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ]
    [IsScalarTower (NumberField.RingOfIntegers ℚ)
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ]
    (H : Type) [CommRing H]
    [HopfAlgebra
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H]
    [Module.Finite
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H]
    [Module.Flat
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H]
    [Algebra.Etale ℚ
      (ℚ ⊗[Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)]
    (f : Additive (WithConv
      ((ℚ ⊗[Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
        →ₐ[ℚ] AlgebraicClosure ℚ)) ≃+ M)
    (hf : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (φ : (ℚ ⊗[Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H) →ₐ[ℚ] AlgebraicClosure ℚ),
      f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
        ρ σ (f (Additive.ofMul (WithConv.toConv φ)))) :
    ρ.HasFlatProlongationAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  letI : Algebra (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    (localizationToAdicCompletionIntegers hq.toHeightOneSpectrumRingOfIntegersRat).toAlgebra
  letI : Algebra (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)).comp
      (localizationToAdicCompletionIntegers
        hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- NOTE: the middle `Algebra ℚ Kᵥ` instance must be pinned to the
  -- canonical `instAlgebraAdicCompletion` (the one baked into the core
  -- theorem's statement); unpinned search at `ℚ` returns
  -- `DivisionRing.toRatAlgebra` instead
  haveI := @IsScalarTower.of_algebraMap_eq
    (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    _ _ _ _
    (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    _
    fun x => by
      -- the left side is the value of the codomain-restricted arc
      -- `ℤ_(q) → ℚ → Kᵥ`; the two `ℚ`-algebra structures on `Kᵥ`
      -- (the one baked into `localizationToAdicCompletionIntegers` and
      -- the ambient one) agree since ring homs out of `ℚ` are unique
      show ((localizationToAdicCompletionIntegers
        hq.toHeightOneSpectrumRingOfIntegersRat) x :
          IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) = _
      unfold localizationToAdicCompletionIntegers
      rw [RingHom.codRestrict_apply, RingHom.comp_apply]
  exact ρ.hasFlatProlongationAt_of_hopf_package
    (v := hq.toHeightOneSpectrumRingOfIntegersRat)
    (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H f hf

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- A Galois representation on a SUBSINGLETON module has a flat
prolongation at every place: the trivial Hopf algebra `𝒪ᵥ` works. Its
generic fibre `Kᵥ ⊗ 𝒪ᵥ ≅ Kᵥ` has a unique `Kᵥ`-point, and the target
space is a single point as well. -/
theorem GaloisRep.hasFlatProlongationAt_of_subsingleton
    (ρ : GaloisRep K A M) [Subsingleton M] :
    ρ.HasFlatProlongationAt v := by
  classical
  -- the source of the comparison map is a singleton
  haveI hsub : Subsingleton ((Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)) := by
    constructor
    intro φ ψ
    have h1 : ∀ (χ : (Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)),
        χ = (χ.comp (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm.toAlgHom).comp
          (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).toAlgHom := by
      intro χ
      refine AlgHom.ext fun x => ?_
      simp
    rw [h1 φ, h1 ψ, Subsingleton.elim
      (φ.comp (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm.toAlgHom)
      (ψ.comp (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm.toAlgHom)]
  haveI hne : Nonempty ((Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ) →ₐ[Kᵥ] (Kᵥᵃˡᵍ)) :=
    ⟨(IsScalarTower.toAlgHom Kᵥ Kᵥ (Kᵥᵃˡᵍ)).comp
      (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).toAlgHom⟩
  -- the target space is a single point
  haveI hsubM : Subsingleton (ρ.toLocal v).Space :=
    inferInstanceAs (Subsingleton M)
  -- assemble the package
  refine ⟨𝒪ᵥ, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
    { toFun := fun _ => 0
      map_smul' := fun _ _ => (smul_zero _).symm
      map_zero' := rfl
      map_add' := fun _ _ => (add_zero (0 : (ρ.toLocal v).Space)).symm }, ?_, ?_⟩
  · -- the generic fibre is étale (isomorphic to `Kᵥ`)
    exact Algebra.Etale.of_equiv (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm
  · -- injectivity between the two singletons
    intro a b _
    exact Subsingleton.elim a b
  · -- surjectivity
    intro y
    exact ⟨Additive.ofMul hne.some, Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The shared flat-prolongation transport** (DERIVED from
`hasFlatProlongationAt_of_dvr_package` + the two-ideal case split): a
mod-`p` Galois representation of `ℚ` over a FIELD `A` whose space is
presented, equivariantly, as the `ℚ̄`-points of the generic fibre of a
finite flat Hopf algebra over `ℤ_(q)` is flat at `q` in the
`GaloisRep.IsFlatAt` sense. The open-ideal quantifier runs over the
two ideals of `A`: at `⊤` the base-changed space is a module over the
zero ring, hence a singleton, and `hasFlatProlongationAt_of_subsingleton`
applies; at `⊥` the base change along `A ⧸ ⊥ ≅ A` is carried by
`HasFlatProlongationAt.of_addEquiv` across the equivariant additive
identification `M ≃+ (A ⧸ ⊥) ⊗[A] M`, `x ↦ (⋯) ⊗ₜ x`. -/
theorem GaloisRep.isFlatAt_of_dvr_package
    {A : Type} [Field A] [TopologicalSpace A] [IsTopologicalRing A]
    {M : Type} [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    (ρ : GaloisRep ℚ A M)
    {q : ℕ} (hq : q.Prime)
    [Algebra (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ]
    [IsScalarTower (NumberField.RingOfIntegers ℚ)
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ]
    (H : Type) [CommRing H]
    [HopfAlgebra
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H]
    [Module.Finite
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H]
    [Module.Flat
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H]
    [Algebra.Etale ℚ
      (ℚ ⊗[Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)]
    (f : Additive (WithConv
      ((ℚ ⊗[Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
        →ₐ[ℚ] AlgebraicClosure ℚ)) ≃+ M)
    (hf : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (φ : (ℚ ⊗[Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H) →ₐ[ℚ] AlgebraicClosure ℚ),
      f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
        ρ σ (f (Additive.ofMul (WithConv.toConv φ)))) :
    ρ.IsFlatAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  constructor
  intro I hI
  rcases I.eq_bot_or_top with rfl | rfl
  · -- `I = ⊥`: transport the core package along `M ≃+ (A ⧸ ⊥) ⊗[A] M`
    have hbase : ρ.HasFlatProlongationAt hq.toHeightOneSpectrumRingOfIntegersRat :=
      ρ.hasFlatProlongationAt_of_dvr_package hq H f hf
    -- the equivariant additive identification
    let e₁ : ((A ⧸ (⊥ : Ideal A)) ⊗[A] M) ≃ₗ[A] M :=
      (TensorProduct.congr (AlgEquiv.quotientBot A A).toLinearEquiv
        (LinearEquiv.refl A M)).trans (TensorProduct.lid A M)
    refine hbase.of_addEquiv e₁.symm.toAddEquiv ?_
    intro σ x
    show e₁.symm (ρ σ x) = (ρ.baseChange (A ⧸ (⊥ : Ideal A))) σ (e₁.symm x)
    have hx : ∀ y : M, e₁.symm y =
        ((AlgEquiv.quotientBot A A).toLinearEquiv.symm 1) ⊗ₜ[A] y := by
      intro y
      simp [e₁, TensorProduct.congr_symm_tmul]
    rw [hx, hx, GaloisRep.baseChange_tmul]
  · -- `I = ⊤`: the base-changed space is a module over the zero ring
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    haveI : Subsingleton ((A ⧸ (⊤ : Ideal A)) ⊗[A] M) :=
      Module.subsingleton (A ⧸ (⊤ : Ideal A)) _
    exact GaloisRep.hasFlatProlongationAt_of_subsingleton
      hq.toHeightOneSpectrumRingOfIntegersRat (ρ.baseChange (A ⧸ (⊤ : Ideal A)))

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

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {M : Type*} [AddCommGroup M] [Module A M]

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

set_option warn.sorry false in
/-- (Sorry node — **the shared flat-prolongation transport**.) A mod-`p`
Galois representation of `ℚ` whose space is presented, equivariantly,
as the `ℚ̄`-points of the generic fibre of a finite flat Hopf algebra
over the localization `ℤ_(q)` is flat at `q` in the
`GaloisRep.IsFlatAt` sense. This is the local-global/base-change
transport common to BOTH flat glue nodes: pass to
`G := 𝒪ᵥ ⊗[ℤ_(q)] H` (Hopf/flat/finite by base change — instance
availability scratch-verified), identify the generic fibre through
`Algebra.TensorProduct.cancelBaseChange` and the `Kᵥ`-points with the
`ℚ̄`-points through the tensor-hom adjunction and the factorization of
finite `ℚ`-algebra maps through `ι(ℚ̄) ⊆ Kᵥᵃˡᵍ`, transporting the
convolution structures (the vendored bare-hom `Monoid` instance vs
mathlib's `WithConv`) and the Galois equivariance through `lift_map`;
the open-ideal quantifier of `IsFlatAt` is handled by the two ideals
of the field `A` (`⊤` via `hasFlatProlongationAt_of_subsingleton`
below, `⊥` via the package itself). See PROGRESS.md (flat-transport
design) for the verified ingredient list. -/
theorem GaloisRep.isFlatAt_of_dvr_package
    {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A]
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
    ρ.IsFlatAt hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

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

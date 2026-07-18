/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import Fermat.FLT.Mathlib.GroupTheory.Index
public import Fermat.FLT.Mathlib.Topology.Algebra.Group.Basic
public import Fermat.FLT.Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix

/-!
# Miscellaneous lemmas for the Deformations folder

A collection of small auxiliary lemmas used in the deformation-theory
files: existence of open maximal ideals in linearly topologized rings,
continuous group-homomorphism / matrix-coefficient lifts, etc.
-/

@[expose] public section




/-- Coerce a `ContinuousAlgHom` to `ContinuousMonoidHom`. -/
def ContinuousAlgHom.toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) : A →ₜ* B :=
  ⟨f.1.toMonoidHom, f.2⟩










open Topology in










open IsLocalRing in

/-- Given a field extension, this is an arbitrarily chosen map between their `AlgebraicClosure`s. -/
noncomputable
def AlgebraicClosure.map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  letI := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom

lemma AlgebraicClosure.map_algebraMap {K L : Type*} [Field K] [Field L] (f : K →+* L) (x) :
    map f (algebraMap K _ x) = algebraMap _ _ (f x) :=
    letI := f.toAlgebra
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).commutes _

lemma IntermediateField.adjoin_adjoin_right
    {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] (s : Set E) : adjoin L (adjoin K s : Set E) = adjoin L s := by
  apply le_antisymm
  · exact adjoin_le_iff.mpr (adjoin_le_iff (T := (adjoin L s).restrictScalars K).mpr
      (subset_adjoin _ _))
  · exact adjoin.mono _ _ _ (subset_adjoin _ _)

nonrec
lemma IsModuleTopology.continuous_det {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace (Module.End A M)] [IsModuleTopology A (Module.End A M)] :
    Continuous (LinearMap.det : Module.End A M →* A) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s A M)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : IsModuleTopology A (Matrix s s A) := IsModuleTopology.instPi
    have : ContinuousAdd (Module.End A M) := IsModuleTopology.toContinuousAdd A _
    letI e : Module.End A M ≃A[A] Matrix s s A :=
    { __ := algEquivMatrix b,
      continuous_toFun := continuous_of_linearMap (algEquivMatrix b).toLinearMap,
      continuous_invFun := continuous_of_linearMap (algEquivMatrix b).symm.toLinearMap }
    rw [e.symm.isQuotientMap.continuous_iff]
    convert! continuous_id.matrix_det (R := A) (n := s)
    ext M
    exact LinearMap.det_toLin b M
  rw [LinearMap.det, dif_neg H]
  exact continuous_of_const fun x ↦ congrFun rfl





/-- We can upgrade an `AlgEquiv` between algebras with the module topology
into a `ContinuousAlgEquiv`. -/
def ContinuousAlgEquiv.ofIsModuleTopology {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace R] [IsModuleTopology R A] [IsModuleTopology R B] (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd R B
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd R A
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap




open NumberField in
instance {G K : Type*} [Field K] [Monoid G] [MulSemiringAction G K] :
    MulSemiringAction G (𝓞 K) where
  smul σ x := ⟨σ • x, x.2.map (MulSemiringAction.toAlgHom ℤ K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

lemma Subring.algebraMap_def {R : Type*} [CommRing R] (S : Subring R) :
    algebraMap S R = S.subtype := rfl

instance {K A : Type*} [Field K] [CommRing A] [Algebra K A] (R : ValuationSubring K)
    [FaithfulSMul K A] : FaithfulSMul R A :=
  Subsemiring.instFaithfulSMulSubtypeMem R


-- VENDORING CHANGE: named explicitly (the original is anonymous and is
-- referred to elsewhere by its auto-generated name
-- `instAlgebraSubtypeMemValuationSubring_fLT`, which depends on the FLT
-- package's module root and so changes under vendoring).
instance instAlgebraSubtypeMemValuationSubringVendored
    {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] :
    Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' _ _ := by simp [← Algebra.smul_def]; rfl



instance {G K L : Type*} [Field K] [Field L] [Algebra K L] [Monoid G] [MulSemiringAction G L]
    [SMulCommClass G K L]
    (E : IntermediateField K L) [Normal K E] : MulSemiringAction G E where
  smul σ x := ⟨σ • x, by
    convert ((MulSemiringAction.toAlgHom K L σ).restrictNormal E x).2
    exact ((MulSemiringAction.toAlgHom K L σ).restrictNormal_commutes E x).symm⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

-- (invisible-instance floater: consumed by typeclass synthesis then inlined —
-- do not delete as free-floating; the term cone cannot see instance use.)
instance IntermediateField.smulCommClass_of_normal
    {K L G : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] [Normal K E] :
    SMulCommClass G K E where
  smul_comm g k e := Subtype.ext <| smul_comm g k e.1

instance ValuationSubring.smulCommClass
    (K L G : Type*) [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L]
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] :
    SMulCommClass G O L where
  smul_comm g o l := smul_comm g o.1 l

noncomputable
instance Additive.instDistrbMulAction
    {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    DistribMulAction G (Additive M) where
  smul g m := .ofMul (g • m.toMul)
  one_smul m := one_smul _ m.toMul
  mul_smul g h m := mul_smul g h m.toMul
  smul_zero g := smul_one (N := M) g
  smul_add g m n := MulDistribMulAction.smul_mul g m.toMul n.toMul

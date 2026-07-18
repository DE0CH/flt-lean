/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Fermat.FLT.Deformations.RepresentationTheory.Etale
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, used to state the
-- cyclotomic-at-Frobenius leaf below in THIS module's elaboration context
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Galois representations

The type `GaloisRep K A M` of `A`-linear continuous representations of the
absolute Galois group of a field `K` on an `A`-module `M`, together with the
basic API (kernel, etc.).
-/

@[expose] public section

open NumberField

universe uK

variable {K : Type uK} {L : Type*} [Field K] [Field L]
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {B : Type*} [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

variable (K A M) in
/-- `GaloisRep K A M` are the `A`-linear galois reps of a field `K` on the `A`-module `M`. -/
def GaloisRep :=
  letI := moduleTopology A (Module.End A M)
  Γ K →ₜ* Module.End A M

noncomputable instance : FunLike (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instFunLike

instance : MonoidHomClass (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instMonoidHomClass

omit [NumberField K] in
@[ext]
lemma GaloisRep.ext {ρ ρ' : GaloisRep K A M} (H : ∀ σ, ρ σ = ρ' σ) : ρ = ρ' :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.ext H

/-- The kernel of a galois rep. -/
noncomputable nonrec
abbrev GaloisRep.ker (ρ : GaloisRep K A M) : Subgroup (Γ K) :=
  letI := moduleTopology A (Module.End A M)
  ρ.ker

/-- A field extension induces a map between galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
def GaloisRep.map (ρ : GaloisRep K A M) (f : K →+* L) : GaloisRep L A M :=
  letI := moduleTopology A (Module.End A M)
  ρ.comp (Field.absoluteGaloisGroup.map f)

-- remark: `.toMonoidHom` added in bump to v4.30.0-rc1

variable (K A n) in
/-- A framed galois rep is a galois rep with a distinguished basis.
We implement it by via a galois rep on `Aⁿ`. -/
abbrev FramedGaloisRep := GaloisRep K A (n → A)


/-- We can conjugate a galois rep by a linear isomorphism on the space. -/
noncomputable
def GaloisRep.conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) : GaloisRep K A N :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  let e' : Module.End A M ≃A[A] Module.End A N :=
    .ofIsModuleTopology <| LinearEquiv.conjAlgEquiv A e
  e'.toContinuousAlgHom.toContinuousMonoidHom.comp ρ

omit [NumberField K] in
lemma GaloisRep.conj_apply (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) :
    ρ.conj e σ = e.conj (ρ σ) := rfl







-- **TODO** this should be frame_unframe maybe?


variable [IsTopologicalRing A]







/-- The determinant of a galois rep. -/
noncomputable
def GaloisRep.det (ρ : GaloisRep K A M) : Γ K →ₜ* A :=
  letI := moduleTopology A (Module.End A M)
  .comp ⟨LinearMap.det, IsModuleTopology.continuous_det⟩ ρ

open TensorProduct in
variable (B) in
/-- Make a `A`-linear galois rep on `M` into a `B`-linear rep on `B ⊗ M`. -/
noncomputable
def GaloisRep.baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) : GaloisRep K B (B ⊗[A] M) :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology B (Module.End B (B ⊗[A] M))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite B (Module.End B (B ⊗[A] M))⟩
  letI := IsModuleTopology.toContinuousAdd B (Module.End B (B ⊗[A] M))
  let F : Module.End A M →+* Module.End B (B ⊗[A] M) := Module.End.baseChangeHom A B M
  have : Continuous F := by
    have : IsTopologicalSemiring (Module.End B (B ⊗[A] M)) := ⟨⟩
    have : Continuous (algebraMap A (Module.End B (B ⊗[A] M))) := by
      rw [IsScalarTower.algebraMap_eq A B, RingHom.coe_comp]
      exact (continuous_algebraMap _ _).comp (continuous_algebraMap _ _)
    exact IsModuleTopology.continuous_of_ringHom (R := A) F (by simpa [F])
  .comp ⟨F, this⟩ ρ

omit [IsTopologicalRing A] [NumberField K] in
open TensorProduct in
@[simp]
lemma GaloisRep.baseChange_tmul [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (σ : Γ K) (r : B) (x : M) :
    ρ.baseChange B σ (r ⊗ₜ x) = r ⊗ₜ (ρ σ x) := rfl

omit [IsTopologicalRing A] [NumberField K] in
lemma GaloisRep.ker_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) :
    ρ.ker ≤ (ρ.baseChange B).ker := by
  intro _; simp +contextual [baseChange]




omit [NumberField K] in
variable (B) in






/-- Given a (global) galois rep, this is the local galois rep at a finite prime `v`.
Note: this fixes an arbitrary embedding `Kᵃˡᵍ → Kᵥᵃˡᵍ`, or equivalently,
an arbitrary choice of valuation on `Kᵃˡᵍ` extending `v`. -/
noncomputable
abbrev GaloisRep.toLocal (ρ : GaloisRep K A M) (v : Ω K) : GaloisRep (v.adicCompletion K) A M :=
  ρ.map (algebraMap _ _)

omit [IsTopologicalRing A] in
/-- `toLocal` evaluates by precomposition with the induced map of absolute
Galois groups (an exposed `rfl`-lemma: downstream modules cannot unfold the
definition through the module-system export). -/
lemma GaloisRep.toLocal_apply (ρ : GaloisRep K A M) (v : Ω K)
    (σ : Γ (v.adicCompletion K)) :
    ρ.toLocal v σ =
      ρ (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) σ) :=
  rfl

universe v u
variable {R : Type u} [CommRing R]

/-- The class of galois reps unramified at `v`. -/
class GaloisRep.IsUnramifiedAt (ρ : GaloisRep K A M) (v : Ω K) : Prop where
  localInertiaGroup_le :
    letI := moduleTopology A (Module.End A M)
    localInertiaGroup v ≤ (ρ.toLocal v).ker


instance [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] :
    (ρ.baseChange B).IsUnramifiedAt v :=
  ⟨(GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans
    (((ρ.toLocal v).ker_baseChange (B := B)))⟩

variable [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]

/-- The characteristic polynomial of the frobenious conjugacy class at `v` under `ρ`. -/
noncomputable
def GaloisRep.charFrob (ρ : GaloisRep K A M) : Polynomial A := (ρ.toLocal v Frobᵥ).charpoly

-- shortcut instance for next theorem: needed after mathlib #34045
noncomputable instance : CommRing Kᵥ := inferInstance


section Flat

set_option linter.unusedVariables false in
/-- The underlying space of a galois rep. This is a type class synonym that allows `G` to act
on it via `ρ`. -/
@[nolint unusedArguments]
def GaloisRep.Space (ρ : GaloisRep K A M) : Type _ := M

instance (ρ : GaloisRep K A M) : AddCommGroup ρ.Space := inferInstanceAs (AddCommGroup M)

-- dirty hack
set_option backward.isDefEq.respectTransparency false in
noncomputable instance (ρ : GaloisRep K A M) : DistribMulAction (Γ K) ρ.Space where
  smul g v := ρ g v
  one_smul b := by unfold HSMul.hSMul; simp [instHSMul]
  mul_smul := by unfold HSMul.hSMul; simp [instHSMul]
  smul_zero := by unfold HSMul.hSMul; simp [instHSMul]
  smul_add := by unfold HSMul.hSMul; simp [instHSMul]

open TensorProduct in
/-- A galois rep `ρ : Γ K → Aut_A(M)` has a flat prolongation at `v` if `M` (when viewed as a
`Γ Kᵥ`) module is isomorphic to the geometric points of a finite etale hopf algebra over `Kᵥ`, and
there exists an finite flat hopf algebra over `𝒪ᵥ` whose generic fiber is isomorphic to it.
In particular this requires `M` (and by extension `A`) to have finite cardinality.

Note that the `Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G)` condition is redundant because `Kᵥ` has char 0
and all finite flat group schemes over `Kᵥ` are etale.
But this would be hard to prove in general, while in the applications they would come from
finite groups so it would be easy to show that they are etale. If this turns out to not be the case,
we can remove this condition and state the aforementioned result as a sorry.
-/
def GaloisRep.HasFlatProlongationAt (ρ : GaloisRep K A M) : Prop :=
  ∃ (G : Type uK) (_ : CommRing G) (_ : HopfAlgebra 𝒪ᵥ G)
    (_ : Module.Flat 𝒪ᵥ G) (_ : Module.Finite 𝒪ᵥ G) (_ : Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G))
    (f : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ) →+[Γ Kᵥ] (ρ.toLocal v).Space),
    Function.Bijective f

omit [IsTopologicalRing A] [Module.Free A M] [Module.Finite A M] in
/-- `HasFlatProlongationAt` transports along a `Γ Kᵥ`-equivariant additive
isomorphism of underlying spaces: the Hopf-algebra witness is reused verbatim
and the geometric-points identification is composed with the isomorphism. -/
lemma GaloisRep.HasFlatProlongationAt.of_equiv {A' : Type*} [CommRing A']
    [TopologicalSpace A'] {M' : Type*} [AddCommGroup M'] [Module A' M']
    {ρ₁ : GaloisRep K A M} {ρ₂ : GaloisRep K A' M'}
    (h : ρ₁.HasFlatProlongationAt v)
    (e : (ρ₁.toLocal v).Space ≃+ (ρ₂.toLocal v).Space)
    (he : ∀ (g : Γ Kᵥ) (x : (ρ₁.toLocal v).Space), e (g • x) = g • e x) :
    ρ₂.HasFlatProlongationAt v := by
  obtain ⟨G, i1, i2, i3, i4, i5, f, hbij⟩ := h
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  exact ⟨G, i1, i2, i3, i4, i5,
    { toFun := fun x => e (f x)
      map_smul' := fun g x => by
        show e (f (g • x)) = g • e (f x)
        rw [map_smul f g x, he]
      map_zero' := by simp
      map_add' := fun a b => by simp },
    e.bijective.comp hbij⟩

set_option warn.sorry false in
/-- **The 3-adic cyclotomic character at an arithmetic Frobenius** (sorry
node): for a prime `p ∉ {2, 3}`, the cyclotomic character of `Γ ℚ`
evaluated at (the global image of) an arithmetic Frobenius at `p` is `p` —
Frobenius raises `3`-power roots of unity to the `p`-th power. Stated in
THIS module so that the Frobenius-image element elaborates identically to
`GaloisRep.toLocal_apply`'s right-hand side (the module-system's opaque
exports make cross-module respellings non-defeq). Stated after applying
`algebraMap ℤ₃ → R`, matching the determinant condition of
`IsHardlyRamified`. -/
theorem cyclotomicCharacter_adicArithFrob {R : Type*} [CommRing R]
    [Algebra ℤ_[3] R]
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    algebraMap ℤ_[3] R
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            hp.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv)) =
      (p : R) :=
  sorry

/-- A galois rep `ρ : Γ K → Aut_A(M)` is flat at `v` if `A/I ⊗ M` has a flat prolongation at `v`
for all open ideals `I`. -/
class GaloisRep.IsFlatAt [IsLocalRing A] (ρ : GaloisRep K A M) : Prop where
  cond : ∀ (I : Ideal A), IsOpen (I : Set A) →
    (ρ.baseChange (A ⧸ I)).HasFlatProlongationAt v

end Flat

/-- A Galois representation is a representation (note that we
are forgetting topological information here). -/
def GaloisRep.toRepresentation (ρ : GaloisRep K A M) : Representation A (Γ K) M :=
  letI := moduleTopology A (Module.End A M) -- ?!
  ρ.toMonoidHom

/-- Irreducibility of a Galois representation over a field. -/
def GaloisRep.IsIrreducible {k : Type*} [Field k] [TopologicalSpace k] [Module k M]
    (ρ : GaloisRep K k M) : Prop := ρ.toRepresentation.IsIrreducible

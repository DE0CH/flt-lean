/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Deyao Chen
-/
module

-- `GaloisRep.HasFlatProlongationAt`, the convolution bridges
-- (`vendored_one_eq_convOne`, `vendored_mul_eq_convMul`) and the
-- `AlgHom.liftEquiv` convolution glue (`liftEquiv_*`)
public import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
-- the Gelfand-duality / étale-Grothendieck machinery this cut runs
-- inside: `exists_finiteQuotient_galoisModule_etale_package`,
-- `exists_algHom_of_algHom_map`, `eq_zero_of_forall_algHom_eq_zero`,
-- `antipodeAlgHom_comp_bialgHom`, `exists_flat_hopf_form_of_hopf_order`
public import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat

/-!
# Raynaud closure, on the representation-free point-group carrier

MOVED HERE 2026-07-26 from `Modularity/Interface.lean` — this file is
the LOWEST home for the content, not a new copy of it. The duplication
audit on `hasFlatProlongationAt_of_pi_surjection`
(`GaloisRepresentation/HardlyRamified/Deformation.lean`) recorded that
the Raynaud-closure cut existed only ABOVE that leaf, in
`Modularity/Interface.lean`, which imports
`Modularity/KhareWintenberger.lean`, which imports `Deformation.lean`;
so the leaf could not consume it and a THIRD copy was being sorried in
`KhareWintenberger.lean`. The declarations below are the Interface ones
VERBATIM, in the same namespace (`GaloisRepresentation.Modularity`) and
under the same names, so every existing consumer keeps working through
the import; `Interface.lean` now hosts only the parts of the cut that
are not needed downstream (the Hopf-order trio, the two étale–Galois
embedding leaves and `IsFlatPointsGroupAt.of_injective`).

Contents: the carrier `IsFlatPointsGroupAt v X` ("`X` is,
`Γ Kᵥ`-equivariantly, the geometric-point group of the generic fibre of
a finite flat `𝒪ᵥ`-Hopf algebra with étale generic fibre"), its exact
repackaging of `GaloisRep.HasFlatProlongationAt`, and the closure
properties that a QUOTIENT argument needs: transport along equivariant
additive isomorphisms, the trivial package, binary and finite products
(Hopf tensor product), and closure under equivariant surjections
(schematic closure over the DVR).

The neutral-home nomination in `KhareWintenberger.lean`'s own audit was
`Deformations/RepresentationTheory/FlatProlongation.lean`; this file is
its sibling rather than that file itself, because the cut needs the
elliptic-curve/Hopf module `KnownIn1980s/EllipticCurves/Flat.lean` in
its import cone and `FlatProlongation.lean` is consumed by modules that
should not pay for it.

References: Raynaud, *Schémas en groupes de type `(p,…,p)`*, Bull. SMF
102 (1974), §3; Tate, *Finite flat group schemes*, in
Cornell–Silverman–Stevens.
-/

@[expose] public section

open IsDedekindDomain
open scoped TensorProduct

universe u v

namespace GaloisRepresentation.Modularity

/-! ##### Convolution glue for points of a tensor product of Hopf orders

The product half of the Raynaud cut needs one general fact: the
`Ω`-points of a tensor product of two Hopf algebras are the PAIRS of
points, compatibly with the convolution group law. The lemmas of this
section establish that in two steps — first over the base ring
(`tensorPoints_convOne` / `tensorPoints_convMul` / `tensorPoints_comp`,
the multiplicativity of `Algebra.TensorProduct.lift` for the
convolution products of the tensor bialgebra), then transported through
the base-change adjunction `AlgHom.liftEquiv` to the generic fibres
(`basePointsTensorEquiv` and its `_one` / `_mul` / `_smul` laws), reusing
the base-change convolution lemmas of `FlatProlongation.lean`. -/

section TensorPointsGlue

open WithConv

variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
variable {A B : Type*} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

/-- **Convolution unit of a tensor product of points** (PROVEN): the
pair `(1, 1)` of counit-units lifts to the counit-unit of the tensor
bialgebra `A ⊗[R] B`, because its counit is the product of the two
counits. -/
theorem tensorPoints_convOne :
    Algebra.TensorProduct.lift ((1 : WithConv (A →ₐ[R] C)).ofConv)
        ((1 : WithConv (B →ₐ[R] C)).ofConv) (fun _ _ => Commute.all _ _) =
      (1 : WithConv (A ⊗[R] B →ₐ[R] C)).ofConv := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp [AlgHom.convOne_apply, mul_comm]

/-- **Convolution product of a tensor product of points** (PROVEN):
`Algebra.TensorProduct.lift` is multiplicative for the convolution
products, because the comultiplication of the tensor bialgebra is the
componentwise one composed with the middle-four exchange — so both
sides evaluate on `a ⊗ₜ b` to the same sum over
`comul a ⊗ comul b`. -/
theorem tensorPoints_convMul (f₁ g₁ : WithConv (A →ₐ[R] C))
    (f₂ g₂ : WithConv (B →ₐ[R] C)) :
    Algebra.TensorProduct.lift ((f₁ * g₁).ofConv) ((f₂ * g₂).ofConv)
        (fun _ _ => Commute.all _ _) =
      (toConv (Algebra.TensorProduct.lift f₁.ofConv f₂.ofConv (fun _ _ => Commute.all _ _)) *
        toConv (Algebra.TensorProduct.lift g₁.ofConv g₂.ofConv
          (fun _ _ => Commute.all _ _))).ofConv := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.convMul_apply, AlgHom.convMul_apply,
      AlgHom.convMul_apply, TensorProduct.comul_tmul]
    induction Coalgebra.comul (R := R) a with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, add_mul, hx, hy]
    | tmul a₁ a₂ =>
      induction Coalgebra.comul (R := R) b with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, mul_add, hx, hy]
      | tmul b₁ b₂ =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.lift_tmul]
        ring

/-- **Postcomposition through the tensor pairing** (PROVEN): the pairing
`Algebra.TensorProduct.lift` commutes with postcomposition by an algebra
map, which is what makes the points identification Galois-equivariant. -/
theorem tensorPoints_comp {D : Type*} [CommRing D] [Algebra R D] (h : C →ₐ[R] D)
    (ψ₁ : A →ₐ[R] C) (ψ₂ : B →ₐ[R] C) :
    Algebra.TensorProduct.lift (h.comp ψ₁) (h.comp ψ₂) (fun _ _ => Commute.all _ _) =
      h.comp (Algebra.TensorProduct.lift ψ₁ ψ₂ (fun _ _ => Commute.all _ _)) := by
  refine AlgHom.ext fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

/-- **Points of a tensor product are pairs of points** (PROVEN): for a
COMMUTATIVE target there is no commutation side condition, so
`Algebra.TensorProduct.lift` and restriction along the two inclusions
are mutually inverse. -/
noncomputable def algHomTensorProdEquiv :
    ((A ⊗[R] B) →ₐ[R] C) ≃ ((A →ₐ[R] C) × (B →ₐ[R] C)) where
  toFun Φ := (Φ.comp Algebra.TensorProduct.includeLeft,
    Φ.comp (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)))
  invFun p := Algebra.TensorProduct.lift p.1 p.2 (fun _ _ => Commute.all _ _)
  left_inv Φ := by ext x <;> simp
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> refine AlgHom.ext fun x => ?_ <;> simp

end TensorPointsGlue

section BasePointsGlue

open WithConv

variable {R : Type*} [CommRing R]
variable {S L : Type u} [Field S] [Field L] [Algebra S L] [Algebra R S] [Algebra R L]
  [IsScalarTower R S L]
variable {A B : Type u} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

/-- **The generic-fibre points of a tensor product of Hopf orders**
(PROVEN): pairs of `L`-points of the base changes `S ⊗[R] A`,
`S ⊗[R] B` are the `L`-points of the base change of `A ⊗[R] B`. Built
from the base-change adjunction `AlgHom.liftEquiv` on each side and
`algHomTensorProdEquiv` over the base ring. -/
noncomputable def basePointsTensorEquiv :
    ((S ⊗[R] A →ₐ[S] L) × (S ⊗[R] B →ₐ[S] L)) ≃ (S ⊗[R] (A ⊗[R] B) →ₐ[S] L) :=
  ((AlgHom.liftEquiv R S A L).symm.prodCongr (AlgHom.liftEquiv R S B L).symm).trans
    (algHomTensorProdEquiv.symm.trans (AlgHom.liftEquiv R S (A ⊗[R] B) L))

/-- The defining formula of `basePointsTensorEquiv`. -/
theorem basePointsTensorEquiv_apply (p : (S ⊗[R] A →ₐ[S] L) × (S ⊗[R] B →ₐ[S] L)) :
    basePointsTensorEquiv p = AlgHom.liftEquiv R S (A ⊗[R] B) L
      (Algebra.TensorProduct.lift ((AlgHom.liftEquiv R S A L).symm p.1)
        ((AlgHom.liftEquiv R S B L).symm p.2) (fun _ _ => Commute.all _ _)) := rfl

set_option maxSynthPendingDepth 4 in
/-- `basePointsTensorEquiv` sends the pair of convolution units to the
convolution unit (of the bare-hom monoid used by the flat-prolongation
package). -/
theorem basePointsTensorEquiv_one :
    basePointsTensorEquiv ((1 : S ⊗[R] A →ₐ[S] L), (1 : S ⊗[R] B →ₐ[S] L)) = 1 := by
  rw [basePointsTensorEquiv_apply, vendored_one_eq_convOne (A₀ := S ⊗[R] A),
    vendored_one_eq_convOne (A₀ := S ⊗[R] B),
    liftEquiv_symm_convOne, liftEquiv_symm_convOne, tensorPoints_convOne, liftEquiv_convOne,
    vendored_one_eq_convOne]

set_option maxSynthPendingDepth 4 in
/-- `basePointsTensorEquiv` is multiplicative for the componentwise
convolution product. -/
theorem basePointsTensorEquiv_mul (p q : (S ⊗[R] A →ₐ[S] L) × (S ⊗[R] B →ₐ[S] L)) :
    basePointsTensorEquiv (p.1 * q.1, p.2 * q.2) =
      basePointsTensorEquiv p * basePointsTensorEquiv q := by
  rw [basePointsTensorEquiv_apply, basePointsTensorEquiv_apply, basePointsTensorEquiv_apply,
    vendored_mul_eq_convMul p.1 q.1, vendored_mul_eq_convMul p.2 q.2,
    liftEquiv_symm_convMul, liftEquiv_symm_convMul, tensorPoints_convMul, liftEquiv_convMul,
    vendored_mul_eq_convMul]

set_option maxSynthPendingDepth 4 in
/-- `basePointsTensorEquiv` is equivariant for the postcomposition
action of `Gal(L/S)` on points. -/
theorem basePointsTensorEquiv_smul (σ : L ≃ₐ[S] L)
    (p : (S ⊗[R] A →ₐ[S] L) × (S ⊗[R] B →ₐ[S] L)) :
    basePointsTensorEquiv (σ • p.1, σ • p.2) = σ • basePointsTensorEquiv p := by
  have h1 : ∀ (φ : S ⊗[R] A →ₐ[S] L), σ • φ = (σ.toAlgHom).comp φ :=
    fun _ => AlgHom.ext fun _ => rfl
  have h2 : ∀ (φ : S ⊗[R] B →ₐ[S] L), σ • φ = (σ.toAlgHom).comp φ :=
    fun _ => AlgHom.ext fun _ => rfl
  have h3 : ∀ (φ : S ⊗[R] (A ⊗[R] B) →ₐ[S] L), σ • φ = (σ.toAlgHom).comp φ :=
    fun _ => AlgHom.ext fun _ => rfl
  rw [basePointsTensorEquiv_apply, basePointsTensorEquiv_apply, h1, h2, h3,
    liftEquiv_symm_comp, liftEquiv_symm_comp, tensorPoints_comp, liftEquiv_comp]

end BasePointsGlue

section RaynaudClosure

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "Kᵥ" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝒪ᵥ" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Γᵥ" =>
  Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ v)
local notation "Ωᵥ" =>
  AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)

set_option backward.isDefEq.respectTransparency false in
/-- **The flat point-group carrier at `v`**: the additive group `X`
with its `Γ Kᵥ`-action is, equivariantly, the geometric-point group
of the generic fibre of some finite flat `𝒪ᵥ`-Hopf algebra with
étale generic fibre. This is exactly the existential package of
`GaloisRep.HasFlatProlongationAt` with the representation space
replaced by an abstract `Γ Kᵥ`-module (the equivariant bijection is
carried as an `AddMonoidHom` plus an explicit equivariance clause so
the carrier needs no `DistribMulActionHom` instances on abstract
`X`); `hasFlatProlongationAt_iff_isFlatPointsGroupAt` is the exact
repackaging. Raynaud's closure properties of finite flat group
schemes over the DVR `𝒪ᵥ` become closure properties of this
predicate (`prod`, `of_injective` below). -/
def IsFlatPointsGroupAt (X : Type*) [AddCommGroup X]
    [DistribMulAction Γᵥ X] : Prop :=
  ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra 𝒪ᵥ G)
    (_ : Module.Flat 𝒪ᵥ G) (_ : Module.Finite 𝒪ᵥ G)
    (_ : Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G))
    (f : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Ωᵥ) →+ X),
    Function.Bijective f ∧
      ∀ (g : Γᵥ) (y : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Ωᵥ)),
        f (g • y) = g • f y

variable {v}

set_option backward.isDefEq.respectTransparency false in
/-- **The exact repackaging** (PROVEN): a Galois representation has a
flat prolongation at `v` iff its local space is a flat point-group at
`v`. The two sides differ only in how the equivariant bijection is
carried (`DistribMulActionHom` versus `AddMonoidHom` + equivariance
clause). -/
theorem GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] (ρ : GaloisRep ℚ A M) :
    ρ.HasFlatProlongationAt v ↔ IsFlatPointsGroupAt v (ρ.toLocal v).Space := by
  constructor
  · rintro ⟨G, i1, i2, i3, i4, i5, f, hbij⟩
    exact ⟨G, i1, i2, i3, i4, i5,
      { toFun := f
        map_zero' := f.map_zero
        map_add' := f.map_add }, hbij, fun g y => f.map_smul g y⟩
  · rintro ⟨G, i1, i2, i3, i4, i5, f, hbij, hequiv⟩
    exact ⟨G, i1, i2, i3, i4, i5,
      { toFun := f
        map_smul' := hequiv
        map_zero' := f.map_zero
        map_add' := f.map_add }, hbij⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Transport** (PROVEN): the flat point-group property moves along
a `Γ Kᵥ`-equivariant additive isomorphism — the Hopf witness is
reused verbatim and the point identification is composed with the
isomorphism. -/
theorem IsFlatPointsGroupAt.of_addEquiv {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y]
    [DistribMulAction Γᵥ X] [DistribMulAction Γᵥ Y]
    (h : IsFlatPointsGroupAt v X) (e : X ≃+ Y)
    (he : ∀ (g : Γᵥ) (x : X), e (g • x) = g • e x) :
    IsFlatPointsGroupAt v Y := by
  obtain ⟨G, i1, i2, i3, i4, i5, f, hbij, hequiv⟩ := h
  exact ⟨G, i1, i2, i3, i4, i5, e.toAddMonoidHom.comp f,
    e.bijective.comp hbij, fun g y => by
      show e (f (g • y)) = g • e (f y)
      rw [hequiv, he]⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The trivial package** (PROVEN — the abstract form of
`GaloisRep.hasFlatProlongationAt_of_subsingleton`, by the same
argument): a subsingleton is a flat point-group at every `v`,
witnessed by the trivial Hopf algebra `𝒪ᵥ` itself, whose generic
fibre `Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ ≅ Kᵥ` is étale with a unique `Kᵥᵃˡᵍ`-point. -/
theorem IsFlatPointsGroupAt.of_subsingleton {X : Type*}
    [AddCommGroup X] [DistribMulAction Γᵥ X] [Subsingleton X] :
    IsFlatPointsGroupAt v X := by
  classical
  haveI hsub : Subsingleton ((Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ) →ₐ[Kᵥ] Ωᵥ) := by
    constructor
    intro φ ψ
    have h1 : ∀ (χ : (Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ) →ₐ[Kᵥ] Ωᵥ),
        χ = (χ.comp (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm.toAlgHom).comp
          (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).toAlgHom := by
      intro χ
      refine AlgHom.ext fun x => ?_
      simp
    rw [h1 φ, h1 ψ, Subsingleton.elim
      (φ.comp (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm.toAlgHom)
      (ψ.comp (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm.toAlgHom)]
  have hne : Nonempty ((Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ) →ₐ[Kᵥ] Ωᵥ) :=
    ⟨(IsScalarTower.toAlgHom Kᵥ Kᵥ Ωᵥ).comp
      (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).toAlgHom⟩
  exact ⟨𝒪ᵥ, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.Etale.of_equiv (Algebra.TensorProduct.rid 𝒪ᵥ Kᵥ Kᵥ).symm,
    { toFun := fun _ => (0 : X)
      map_zero' := rfl
      map_add' := fun _ _ => (add_zero (0 : X)).symm },
    ⟨fun a b _ => Subsingleton.elim a b,
      fun _ => ⟨Additive.ofMul hne.some, Subsingleton.elim _ _⟩⟩,
    fun g _ => (smul_zero g).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
set_option maxSynthPendingDepth 4 in
/-- **Product closure** (PROVEN 2026-07-25 — the products half of
Raynaud closure: finite flat group schemes over the DVR `𝒪ᵥ` are
closed under finite products): the binary product of two flat
point-groups at `v` is a flat point-group at `v`. The witness is the
tensor product `G₁ ⊗[𝒪ᵥ] G₂` of the two witness Hopf algebras —
* Hopf structure: the `HopfAlgebra 𝒪ᵥ (G₁ ⊗[𝒪ᵥ] G₂)` instance of
  `Mathlib.RingTheory.HopfAlgebra.TensorProduct`; flatness and
  module-finiteness of the tensor product are mathlib instances.
* Generic fibre: `(Kᵥ ⊗[𝒪ᵥ] G₁) ⊗[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G₂) ≃ₐ[Kᵥ]
  Kᵥ ⊗[𝒪ᵥ] (G₁ ⊗[𝒪ᵥ] G₂)` (`Algebra.TensorProduct.cancelBaseChange`
  then `Algebra.TensorProduct.assoc`); étaleness of the left side is
  base change (`Algebra.Etale.baseChange`, `Kᵥ → Kᵥ ⊗[𝒪ᵥ] G₁`) plus
  composition (`Algebra.Etale.comp`), and it is transported through
  the isomorphism by `Algebra.Etale.of_equiv`.
* Points: `basePointsTensorEquiv` identifies the `Kᵥᵃˡᵍ`-points of
  the generic fibre with PAIRS of points (no commutation side
  condition in the commutative target), and
  `basePointsTensorEquiv_one` / `_mul` / `_smul` make that
  identification an equivariant isomorphism of convolution groups.
  Composing with `f₁ × f₂` lands in `X × Y`.
Unconditionally TRUE; no hypothesis package. -/
theorem IsFlatPointsGroupAt.prod {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y]
    [DistribMulAction Γᵥ X] [DistribMulAction Γᵥ Y]
    (hX : IsFlatPointsGroupAt v X) (hY : IsFlatPointsGroupAt v Y) :
    IsFlatPointsGroupAt v (X × Y) := by
  classical
  obtain ⟨G₁, cr₁, hopf₁, flat₁, fin₁, et₁, f₁, hbij₁, heq₁⟩ := hX
  obtain ⟨G₂, cr₂, hopf₂, flat₂, fin₂, et₂, f₂, hbij₂, heq₂⟩ := hY
  letI := cr₁; letI := hopf₁; letI := flat₁; letI := fin₁; letI := et₁
  letI := cr₂; letI := hopf₂; letI := flat₂; letI := fin₂; letI := et₂
  -- the generic fibre of the tensor witness is étale: base change then composition
  haveI hEt : Algebra.Etale Kᵥ ((Kᵥ ⊗[𝒪ᵥ] G₁) ⊗[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G₂)) :=
    Algebra.Etale.comp Kᵥ (Kᵥ ⊗[𝒪ᵥ] G₁) ((Kᵥ ⊗[𝒪ᵥ] G₁) ⊗[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G₂))
  -- the points of the tensor witness are pairs of points, equivariantly and
  -- compatibly with the convolution group law
  obtain ⟨e, hesmul⟩ :
      ∃ e : (Additive (Kᵥ ⊗[𝒪ᵥ] G₁ →ₐ[Kᵥ] Ωᵥ) × Additive (Kᵥ ⊗[𝒪ᵥ] G₂ →ₐ[Kᵥ] Ωᵥ)) ≃+
          Additive (Kᵥ ⊗[𝒪ᵥ] (G₁ ⊗[𝒪ᵥ] G₂) →ₐ[Kᵥ] Ωᵥ),
        ∀ (g : Γᵥ) (p : Additive (Kᵥ ⊗[𝒪ᵥ] G₁ →ₐ[Kᵥ] Ωᵥ) ×
            Additive (Kᵥ ⊗[𝒪ᵥ] G₂ →ₐ[Kᵥ] Ωᵥ)),
          e (g • p) = g • e p := by
    refine ⟨{ toFun := fun p =>
                Additive.ofMul (basePointsTensorEquiv (p.1.toMul, p.2.toMul))
              invFun := fun Φ =>
                (Additive.ofMul (basePointsTensorEquiv.symm Φ.toMul).1,
                  Additive.ofMul (basePointsTensorEquiv.symm Φ.toMul).2)
              left_inv := fun p => by
                show (Additive.ofMul (basePointsTensorEquiv.symm
                      (basePointsTensorEquiv (p.1.toMul, p.2.toMul))).1,
                    Additive.ofMul (basePointsTensorEquiv.symm
                      (basePointsTensorEquiv (p.1.toMul, p.2.toMul))).2) = p
                rw [Equiv.symm_apply_apply]
                exact rfl
              right_inv := fun Φ => by
                show Additive.ofMul (basePointsTensorEquiv
                    ((basePointsTensorEquiv.symm Φ.toMul).1,
                      (basePointsTensorEquiv.symm Φ.toMul).2)) = Φ
                rw [Prod.mk.eta, Equiv.apply_symm_apply]
                exact rfl
              map_add' := fun p q => ?_ }, fun g p => ?_⟩
    · show Additive.ofMul (basePointsTensorEquiv
        (Additive.toMul (p.1 + q.1), Additive.toMul (p.2 + q.2))) = _
      show Additive.ofMul (basePointsTensorEquiv
        (p.1.toMul * q.1.toMul, p.2.toMul * q.2.toMul)) = _
      rw [basePointsTensorEquiv_mul (p := (p.1.toMul, p.2.toMul))
        (q := (q.1.toMul, q.2.toMul))]
      rfl
    · show Additive.ofMul (basePointsTensorEquiv
        (Additive.toMul (g • p.1), Additive.toMul (g • p.2))) = _
      show Additive.ofMul (basePointsTensorEquiv
        (g • p.1.toMul, g • p.2.toMul)) = _
      rw [basePointsTensorEquiv_smul (p := (p.1.toMul, p.2.toMul))]
      rfl
  refine ⟨G₁ ⊗[𝒪ᵥ] G₂, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.Etale.of_equiv
      ((Algebra.TensorProduct.cancelBaseChange 𝒪ᵥ Kᵥ Kᵥ (Kᵥ ⊗[𝒪ᵥ] G₁) G₂).trans
        (Algebra.TensorProduct.assoc 𝒪ᵥ 𝒪ᵥ Kᵥ Kᵥ G₁ G₂)),
    { toFun := fun Φ => (f₁ (e.symm Φ).1, f₂ (e.symm Φ).2)
      map_zero' := by simp
      map_add' := fun Φ Ψ => by simp [map_add e.symm] }, ?_, ?_⟩
  · -- bijectivity: the pair identification and both point identifications are bijective
    exact (hbij₁.prodMap hbij₂).comp e.symm.bijective
  · -- equivariance: `e.symm` is equivariant by `hesmul`, and so is `f₁ × f₂`
    intro g Φ
    have hsymm : e.symm (g • Φ) = g • e.symm Φ := by
      apply e.injective
      rw [e.apply_symm_apply, hesmul, e.apply_symm_apply]
    show ((f₁ (e.symm (g • Φ)).1, f₂ (e.symm (g • Φ)).2) : X × Y) =
      g • ((f₁ (e.symm Φ).1, f₂ (e.symm Φ).2) : X × Y)
    rw [hsymm]
    exact Prod.ext (heq₁ g (e.symm Φ).1) (heq₂ g (e.symm Φ).2)

set_option backward.isDefEq.respectTransparency false in
/-- **Finite products** (PROVEN glue): a finite product of flat
point-groups at `v` is a flat point-group at `v`, by `Fin`-recursion
from the trivial package (`of_subsingleton`, base case) and binary
products (`prod`), transported along the equivariant additive
identification `(∀ i : Fin (m+1), X i) ≃+ X 0 × ∀ i : Fin m, X i.succ`
(`Fin.cons`). -/
theorem IsFlatPointsGroupAt.pi {n : ℕ} {X : Fin n → Type*}
    [instG : ∀ i, AddCommGroup (X i)]
    [instD : ∀ i, DistribMulAction Γᵥ (X i)]
    (h : ∀ i, IsFlatPointsGroupAt v (X i)) :
    IsFlatPointsGroupAt v (∀ i, X i) := by
  induction n generalizing instG instD with
  | zero =>
    haveI : Subsingleton (∀ i : Fin 0, X i) :=
      ⟨fun a b => funext fun i => i.elim0⟩
    exact IsFlatPointsGroupAt.of_subsingleton
  | succ m ih =>
    have htail : IsFlatPointsGroupAt v (∀ i : Fin m, X i.succ) :=
      ih fun i => h i.succ
    have hprod : IsFlatPointsGroupAt v (X 0 × ∀ i : Fin m, X i.succ) :=
      (h 0).prod htail
    refine hprod.of_addEquiv
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun q => (q 0, fun i => q i.succ)
        left_inv := fun p => by
          refine Prod.ext ?_ ?_
          · simp
          · funext i
            simp
        right_inv := fun q => by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_add' := fun p q => by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
      fun g p => ?_
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The étale sub-bialgebra of a point-group quotient** (PROVEN
2026-07-25 — step (β) of the Raynaud quotient-closure cut, split off
the same day from `IsFlatPointsGroupAt.of_surjective`): a
`Γ Kᵥ`-equivariant quotient `Y` of the `Kᵥᵃˡᵍ`-point group of a finite
étale `Kᵥ`-Hopf algebra `Q` is the point group of a
`Kᵥ`-sub-bialgebra `H ↪ Q`, again finite étale — the pullback of
functions along the point surjection. This is Grothendieck's Galois
correspondence for étale algebras carrying a group structure, i.e. the
CONVERSE direction of the Gelfand-duality machinery of
`KnownIn1980s/EllipticCurves/Flat.lean` (which builds the algebra from
the group); the proof runs entirely inside that PROVEN machinery, in
five steps:
* *finiteness*: `Q` is module-finite over `Kᵥ`, so its `Kᵥᵃˡᵍ`-points
  are finite (`Finite.algHom`) and `Y` is finite through the surjection
  `p`;
* *the finite Galois quotient*: a `Kᵥ`-basis `b` of `Q` is enough to
  pin a point, so two automorphisms of `Kᵥᵃˡᵍ` agreeing on the FINITE
  set `{φ (b i)}` act equally on every point of `Q` — by `Kᵥ`-linearity
  of `σ ∘ φ` — hence, `p` being an equivariant surjection, equally on
  `Y`. The normal closure `L` of `Kᵥ({φ (b i)})` is therefore a finite
  Galois subextension through which the `Γ Kᵥ`-action on `Y` factors,
  the factored action `ρ` being built from `AlgEquiv.liftNormal` (which
  is multiplicative because lifts of equal restrictions act equally);
* *the algebra*: `exists_finiteQuotient_galoisModule_etale_package`
  applied to `(Y, L, ρ)` — `Small.{0} Kᵥ` is `small_self` and `Ωᵥ` is a
  separable closure in characteristic zero — yields a finite étale
  `Kᵥ`-Hopf algebra `H` with `points(H) ≃+ Y` equivariantly, its
  `WithConv` convolution monoid identified with the vendored bare-hom
  one by `vendored_mul_eq_convMul`;
* *the embedding*: `exists_algHom_of_algHom_map` (the Gelfand transform
  onto equivariant functions — injective by separation, surjective by
  Speiser independence) applied to the ÉTALE algebra `Q` and the
  equivariant point map `t := e⁻¹ ∘ p` produces `ι : H →ₐ[Kᵥ] Q` with
  `φ ∘ ι = t φ`. It is injective because `p` is surjective, so every
  point of `H` is some `t φ` and the points of the finite étale `H`
  separate it (`eq_zero_of_forall_algHom_eq_zero`);
* *the bialgebra upgrade*: points separate the finite étale
  `Q ⊗[Kᵥ] Q` and every point of it is the `TensorProduct.lift` of its
  two restrictions, so testing `comul ∘ ι` against `(ι ⊗ ι) ∘ comul`
  at such a point is exactly the multiplicativity of `t` (which holds
  because `p` and `e` are additive), and testing the counits is
  `t 1 = 1`; `BialgHom.ofAlgHom` assembles `ι : H →ₐc[Kᵥ] Q`, and its
  induced map on points is `p` — the last clause below.
Unconditionally TRUE; no hypothesis package (for `p` bijective one may
take `H = Q` and `ι = id`). -/
theorem exists_etale_subBialgebra_of_points_surjective
    {Q : Type} [CommRing Q] [HopfAlgebra Kᵥ Q] [Module.Finite Kᵥ Q]
    [Algebra.Etale Kᵥ Q]
    {Y : Type*} [AddCommGroup Y] [DistribMulAction Γᵥ Y]
    (p : Additive (Q →ₐ[Kᵥ] Ωᵥ) →+ Y)
    (hp : Function.Surjective p)
    (hpe : ∀ (g : Γᵥ) (x : Additive (Q →ₐ[Kᵥ] Ωᵥ)), p (g • x) = g • p x) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra Kᵥ H) (_ : Module.Finite Kᵥ H)
      (_ : Algebra.Etale Kᵥ H) (ι : H →ₐc[Kᵥ] Q)
      (_ : Function.Injective (ι : H →ₐ[Kᵥ] Q))
      (e : Additive (H →ₐ[Kᵥ] Ωᵥ) ≃+ Y),
      ∀ φ : Q →ₐ[Kᵥ] Ωᵥ,
        e (Additive.ofMul (φ.comp (ι : H →ₐ[Kᵥ] Q))) = p (Additive.ofMul φ) := by
  classical
  -- ### instances: `Ωᵥ` is a separable closure of `Kᵥ`, and the points are finite
  haveI : CharZero (HeightOneSpectrum.adicCompletion ℚ v) :=
    charZero_of_injective_algebraMap
      ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)).injective)
  haveI hsepcl : IsSepClosure Kᵥ Ωᵥ := ⟨inferInstance, inferInstance⟩
  haveI hQpts : Finite (Q →ₐ[Kᵥ] Ωᵥ) := Finite.algHom Kᵥ Q Ωᵥ
  haveI hYfin : Finite Y := Finite.of_surjective p hp
  -- the Galois action on points is postcomposition
  have hsm : ∀ (g : Γᵥ) (φ : Q →ₐ[Kᵥ] Ωᵥ),
      g • φ = ((g : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ).toAlgHom).comp φ := fun _ _ => AlgHom.ext fun _ => rfl
  -- ### (1) a finite Galois subextension through which the action on `Y` factors
  set b := Module.finBasis Kᵥ Q
  set Sset : Set Ωᵥ :=
    Set.range (fun x : (Q →ₐ[Kᵥ] Ωᵥ) × Fin (Module.finrank Kᵥ Q) => x.1 (b x.2))
  haveI hSfin : Finite ↥Sset := (Set.finite_range _).to_subtype
  set L₀ : IntermediateField Kᵥ Ωᵥ := IntermediateField.adjoin Kᵥ Sset
  haveI : FiniteDimensional Kᵥ ↥L₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsSeparable.isSeparable Kᵥ x).isIntegral
  set L : IntermediateField Kᵥ Ωᵥ := IntermediateField.normalClosure Kᵥ ↥L₀ Ωᵥ
  haveI : Algebra.IsSeparable Kᵥ ↥L :=
    Algebra.isSeparable_tower_bot_of_isSeparable Kᵥ ↥L Ωᵥ
  haveI hGalL : IsGalois Kᵥ ↥L := ⟨⟩
  have hsub : Sset ⊆ (L : Set Ωᵥ) := fun z hz =>
    IntermediateField.le_normalClosure L₀ (IntermediateField.subset_adjoin Kᵥ Sset hz)
  -- automorphisms agreeing on `L` act equally on every point of `Q`
  have keyL : ∀ (σ τ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ), (∀ l ∈ L, σ l = τ l) →
      ∀ φ : Q →ₐ[Kᵥ] Ωᵥ, σ.toAlgHom.comp φ = τ.toAlgHom.comp φ := by
    intro σ τ hστ φ
    refine AlgHom.ext fun x => ?_
    have h2 : (σ.toAlgHom.comp φ).toLinearMap = (τ.toAlgHom.comp φ).toLinearMap :=
      b.ext fun i => hστ _ (hsub ⟨(φ, i), rfl⟩)
    exact LinearMap.congr_fun h2 x
  -- hence equally on `Y`, which is a quotient of the points of `Q`
  have hYact : ∀ σ τ : Γᵥ,
      (∀ l ∈ L, (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) l = (τ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) l) →
      ∀ y : Y, σ • y = τ • y := by
    intro σ τ hστ y
    obtain ⟨x, hx⟩ := hp y
    rw [← hx, ← hpe σ x, ← hpe τ x]
    refine congrArg p ?_
    have h1 : (σ • x : Additive (Q →ₐ[Kᵥ] Ωᵥ)) =
        Additive.ofMul (σ • Additive.toMul x) := rfl
    have h2 : (τ • x : Additive (Q →ₐ[Kᵥ] Ωᵥ)) =
        Additive.ofMul (τ • Additive.toMul x) := rfl
    rw [h1, h2, hsm σ, hsm τ]
    exact congrArg Additive.ofMul (keyL _ _ hστ _)
  -- the `Γ Kᵥ`-action as additive endomorphisms
  set act : Γᵥ → AddMonoid.End Y := fun g =>
    { toFun := fun y => g • y
      map_zero' := smul_zero g
      map_add' := fun y₁ y₂ => smul_add g y₁ y₂ }
  -- the action of `Gal(L/Kᵥ)` on `Y` through `AlgEquiv.liftNormal`
  set ρ : (↥L ≃ₐ[Kᵥ] ↥L) →* AddMonoid.End Y :=
    { toFun := fun σ' => act (AlgEquiv.liftNormal σ' Ωᵥ)
      map_one' := by
        refine AddMonoidHom.ext fun y => ?_
        have hfix : ∀ l ∈ L, (AlgEquiv.liftNormal (1 : ↥L ≃ₐ[Kᵥ] ↥L) Ωᵥ) l
            = (1 : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) l := by
          intro l hl
          have hc := AlgEquiv.liftNormal_commutes (1 : ↥L ≃ₐ[Kᵥ] ↥L) Ωᵥ ⟨l, hl⟩
          simpa using hc
        show (AlgEquiv.liftNormal (1 : ↥L ≃ₐ[Kᵥ] ↥L) Ωᵥ) • y = y
        rw [hYact _ (1 : Γᵥ) hfix y, one_smul]
      map_mul' := by
        intro σ' τ'
        refine AddMonoidHom.ext fun y => ?_
        have hfix : ∀ l ∈ L, (AlgEquiv.liftNormal (σ' * τ') Ωᵥ) l
            = ((AlgEquiv.liftNormal σ' Ωᵥ) * (AlgEquiv.liftNormal τ' Ωᵥ) :
              Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) l := by
          intro l hl
          have hc := AlgEquiv.liftNormal_commutes (σ' * τ') Ωᵥ ⟨l, hl⟩
          have hcτ := AlgEquiv.liftNormal_commutes τ' Ωᵥ ⟨l, hl⟩
          have hcσ := AlgEquiv.liftNormal_commutes σ' Ωᵥ (τ' ⟨l, hl⟩)
          simp only [IntermediateField.algebraMap_apply] at hc hcτ hcσ
          show (AlgEquiv.liftNormal (σ' * τ') Ωᵥ) l
            = (AlgEquiv.liftNormal σ' Ωᵥ) ((AlgEquiv.liftNormal τ' Ωᵥ) l)
          rw [hc, hcτ, hcσ]
          rfl
        show (AlgEquiv.liftNormal (σ' * τ') Ωᵥ) • y =
          (AlgEquiv.liftNormal σ' Ωᵥ) • ((AlgEquiv.liftNormal τ' Ωᵥ) • y)
        rw [hYact _ _ hfix y, mul_smul] }
  -- the restriction of a global automorphism acts on `Y` as the automorphism itself
  have hρσ : ∀ (σ : Γᵥ) (y : Y),
      ρ (AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) ↥L
        (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ)) y = σ • y := by
    intro σ y
    show (AlgEquiv.liftNormal (AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) ↥L
      (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ)) Ωᵥ) • y = σ • y
    refine hYact _ _ (fun l hl => ?_) y
    have hc := AlgEquiv.liftNormal_commutes
      (AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) ↥L (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ)) Ωᵥ ⟨l, hl⟩
    have hr := AlgEquiv.restrictNormalHom_apply (F := Kᵥ) (K₁ := Ωᵥ) L
      (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) ⟨l, hl⟩
    simp only [IntermediateField.algebraMap_apply] at hc
    rw [hc, hr]
  -- ### (2) the finite étale Hopf algebra with point group `Y`
  obtain ⟨H, hCR, hHopf, hFin, hEt, f, hf⟩ :
      ∃ (HK : Type) (_ : CommRing HK) (_ : HopfAlgebra Kᵥ HK)
        (_ : Module.Finite Kᵥ HK) (_ : Algebra.Etale Kᵥ HK)
        (f : Additive (WithConv (HK →ₐ[Kᵥ] Ωᵥ)) ≃+ Y),
        ∀ (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) (φ : HK →ₐ[Kᵥ] Ωᵥ),
          f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
            ρ (AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) ↥L σ)
              (f (Additive.ofMul (WithConv.toConv φ))) :=
    exists_finiteQuotient_galoisModule_etale_package Kᵥ Ωᵥ Y L ρ
  letI := hCR
  letI := hHopf
  letI := hFin
  letI := hEt
  -- the bare-hom convolution monoid on the points of `H` is mathlib's `WithConv` one
  set w : Additive (H →ₐ[Kᵥ] Ωᵥ) ≃+ Additive (WithConv (H →ₐ[Kᵥ] Ωᵥ)) :=
    { toFun := fun u => Additive.ofMul (WithConv.toConv (Additive.toMul u))
      invFun := fun u => Additive.ofMul (WithConv.ofConv (Additive.toMul u))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun u₁ u₂ => congrArg Additive.ofMul (by
        show WithConv.toConv (Additive.toMul u₁ * Additive.toMul u₂) =
          WithConv.toConv (Additive.toMul u₁) * WithConv.toConv (Additive.toMul u₂)
        rw [vendored_mul_eq_convMul, WithConv.toConv_ofConv]) }
  set e : Additive (H →ₐ[Kᵥ] Ωᵥ) ≃+ Y := w.trans f
  have heapply : ∀ φ : H →ₐ[Kᵥ] Ωᵥ,
      e (Additive.ofMul φ) = f (Additive.ofMul (WithConv.toConv φ)) := fun _ => rfl
  have hee : ∀ (g : Γᵥ) (u : Additive (H →ₐ[Kᵥ] Ωᵥ)), e (g • u) = g • e u := by
    intro g u
    have h1 : (g • u : Additive (H →ₐ[Kᵥ] Ωᵥ)) =
        Additive.ofMul (((g : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ).toAlgHom).comp (Additive.toMul u)) := by
      show Additive.ofMul (g • Additive.toMul u) = _
      exact congrArg Additive.ofMul (AlgHom.ext fun _ => rfl)
    have h3 : e u = f (Additive.ofMul (WithConv.toConv (Additive.toMul u))) := rfl
    rw [h1, heapply, hf (g : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) (Additive.toMul u), hρσ g, h3]
  have heesymm : ∀ (g : Γᵥ) (y : Y), e.symm (g • y) = g • e.symm y := by
    intro g y
    apply e.injective
    rw [e.apply_symm_apply, hee, e.apply_symm_apply]
  -- ### (3) the induced map of point sets and the algebra homomorphism `H → Q`
  set t : (Q →ₐ[Kᵥ] Ωᵥ) → (H →ₐ[Kᵥ] Ωᵥ) :=
    fun φ => Additive.toMul (e.symm (p (Additive.ofMul φ)))
  have hte : ∀ (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) (φ : Q →ₐ[Kᵥ] Ωᵥ),
      t (σ.toAlgHom.comp φ) = σ.toAlgHom.comp (t φ) := by
    intro σ φ
    have h1 : (Additive.ofMul (σ.toAlgHom.comp φ) : Additive (Q →ₐ[Kᵥ] Ωᵥ)) =
        (σ : Γᵥ) • Additive.ofMul φ := by
      refine congrArg Additive.ofMul ?_
      exact (AlgHom.ext fun _ => rfl : ((σ : Γᵥ) • φ) = σ.toAlgHom.comp φ).symm
    show Additive.toMul (e.symm (p (Additive.ofMul (σ.toAlgHom.comp φ)))) = _
    rw [h1, hpe, heesymm]
    exact AlgHom.ext fun _ => rfl
  obtain ⟨ι₀, hι₀⟩ := exists_algHom_of_algHom_map Kᵥ Ωᵥ Q H t hte
  have hcompι : ∀ φ : Q →ₐ[Kᵥ] Ωᵥ, φ.comp ι₀ = t φ := fun φ =>
    AlgHom.ext fun x => hι₀ φ x
  -- every point of `H` is a restriction, because `p` is surjective
  have htsurj : ∀ ψ : H →ₐ[Kᵥ] Ωᵥ, ∃ φ : Q →ₐ[Kᵥ] Ωᵥ, t φ = ψ := by
    intro ψ
    obtain ⟨x, hx⟩ := hp (e (Additive.ofMul ψ))
    refine ⟨Additive.toMul x, ?_⟩
    show Additive.toMul (e.symm (p (Additive.ofMul (Additive.toMul x)))) = ψ
    rw [show (Additive.ofMul (Additive.toMul x) : Additive (Q →ₐ[Kᵥ] Ωᵥ)) = x from rfl,
      hx, e.symm_apply_apply]
    rfl
  have hι₀inj : Function.Injective ι₀ := by
    intro x₁ x₂ hx
    have hzero : x₁ - x₂ = 0 := by
      refine eq_zero_of_forall_algHom_eq_zero Kᵥ Ωᵥ H _ fun ψ => ?_
      obtain ⟨φ, hφ⟩ := htsurj ψ
      rw [map_sub, sub_eq_zero, ← hφ]
      show t φ x₁ = t φ x₂
      rw [← hι₀ φ x₁, ← hι₀ φ x₂, hx]
    exact sub_eq_zero.mp hzero
  -- ### (4) the bialgebra upgrade: `ι₀` respects counit and comultiplication
  have ht1 : t 1 = 1 := by
    show Additive.toMul (e.symm (p (Additive.ofMul (1 : Q →ₐ[Kᵥ] Ωᵥ)))) = 1
    rw [show (Additive.ofMul (1 : Q →ₐ[Kᵥ] Ωᵥ)) = (0 : Additive (Q →ₐ[Kᵥ] Ωᵥ)) from rfl,
      map_zero, map_zero]
    rfl
  have htmul : ∀ φ ψ : Q →ₐ[Kᵥ] Ωᵥ, t (φ * ψ) = t φ * t ψ := by
    intro φ ψ
    show Additive.toMul (e.symm (p (Additive.ofMul (φ * ψ)))) = _
    rw [show (Additive.ofMul (φ * ψ) : Additive (Q →ₐ[Kᵥ] Ωᵥ)) =
      Additive.ofMul φ + Additive.ofMul ψ from rfl, map_add, map_add]
    rfl
  have hcounit : (Bialgebra.counitAlgHom Kᵥ Q).comp ι₀ = Bialgebra.counitAlgHom Kᵥ H := by
    refine AlgHom.ext fun x => ?_
    refine (algebraMap Kᵥ Ωᵥ).injective ?_
    have h1 : (1 : Q →ₐ[Kᵥ] Ωᵥ) (ι₀ x) =
        algebraMap Kᵥ Ωᵥ (Bialgebra.counitAlgHom Kᵥ Q (ι₀ x)) := rfl
    have h2 : (1 : H →ₐ[Kᵥ] Ωᵥ) x =
        algebraMap Kᵥ Ωᵥ (Bialgebra.counitAlgHom Kᵥ H x) := rfl
    rw [AlgHom.comp_apply, ← h1, ← h2, hι₀ 1 x, ht1]
  haveI hEt2 : Algebra.Etale Kᵥ (Q ⊗[Kᵥ] Q) := Algebra.Etale.comp Kᵥ Q (Q ⊗[Kᵥ] Q)
  have hcomul : (Algebra.TensorProduct.map ι₀ ι₀).comp (Bialgebra.comulAlgHom Kᵥ H) =
      (Bialgebra.comulAlgHom Kᵥ Q).comp ι₀ := by
    refine AlgHom.ext fun a => ?_
    have hsep := eq_zero_of_forall_algHom_eq_zero Kᵥ Ωᵥ (Q ⊗[Kᵥ] Q)
      ((Algebra.TensorProduct.map ι₀ ι₀).comp (Bialgebra.comulAlgHom Kᵥ H) a -
        (Bialgebra.comulAlgHom Kᵥ Q).comp ι₀ a)
    rw [sub_eq_zero] at hsep
    apply hsep
    intro χ
    rw [map_sub, sub_eq_zero]
    set φ := χ.comp Algebra.TensorProduct.includeLeft with hφ
    set ψ := χ.comp (Algebra.TensorProduct.includeRight : Q →ₐ[Kᵥ] Q ⊗[Kᵥ] Q) with hψ
    have hχ : χ = Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _ := by
      refine Algebra.TensorProduct.ext ?_ ?_
      · exact AlgHom.ext fun c => by simp [hφ]
      · exact AlgHom.ext fun c => by simp [hψ]
    have hleft : χ ((Algebra.TensorProduct.map ι₀ ι₀)
        (Bialgebra.comulAlgHom Kᵥ H a)) = ((t φ) * (t ψ)) a := by
      rw [hχ]
      have hlift : (Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _).comp
          (Algebra.TensorProduct.map ι₀ ι₀) =
          Algebra.TensorProduct.lift (φ.comp ι₀) (ψ.comp ι₀)
            (fun _ _ => Commute.all _ _) := by
        refine Algebra.TensorProduct.ext ?_ ?_
        · exact AlgHom.ext fun c => by simp
        · exact AlgHom.ext fun c => by simp
      rw [← AlgHom.comp_apply, hlift, hcompι, hcompι]
      rfl
    have hright : χ ((Bialgebra.comulAlgHom Kᵥ Q) (ι₀ a)) = (φ * ψ) (ι₀ a) := by
      rw [hχ]; rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hleft, hright,
      show (φ * ψ) (ι₀ a) = ((φ * ψ).comp ι₀) a from rfl, hcompι, htmul]
  -- ### (5) assembly
  refine ⟨H, hCR, hHopf, hFin, hEt, BialgHom.ofAlgHom ι₀ hcounit hcomul, ?_, e, ?_⟩
  · exact hι₀inj
  · intro φ
    show e (Additive.ofMul (φ.comp ι₀)) = p (Additive.ofMul φ)
    rw [hcompι φ]
    show e (Additive.ofMul (Additive.toMul (e.symm (p (Additive.ofMul φ))))) = _
    rw [show ∀ z : Additive (H →ₐ[Kᵥ] Ωᵥ),
      (Additive.ofMul (Additive.toMul z) : Additive (H →ₐ[Kᵥ] Ωᵥ)) = z from fun _ => rfl]
    exact e.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Hopf orders in sub-bialgebras of a generic fibre** (PROVEN
2026-07-25 — step (γ), the schematic-closure/saturation half of the
Raynaud quotient-closure cut, split off from
`IsFlatPointsGroupAt.of_surjective`; Raynaud, *Schémas en groupes de
type `(p, …, p)`*, Bull. SMF 102 (1974); Tate, *Finite flat group
schemes*, in Cornell–Silverman–Stevens): a `Kᵥ`-sub-bialgebra `H` of
the generic fibre `Q := Kᵥ ⊗[𝒪ᵥ] G` of a finite flat `𝒪ᵥ`-Hopf algebra
`G` carries a finite flat `𝒪ᵥ`-Hopf order — the intersection
`H ∩ G` formed inside `Q` — whose generic fibre is `H` as a
`Kᵥ`-bialgebra. This is the DUAL, and the easier half, of the schematic
closure `IsFlatPointsGroupAt.of_injective` needs: it takes a
SUB-algebra of the witness where that node must quotient it.

The proof needs NO sub-bialgebra API (the pin has none) and builds NO
`HopfAlgebra` structure by hand: the whole point is that the vendored
`exists_flat_hopf_form_of_hopf_order` of
`KnownIn1980s/EllipticCurves/Flat.lean` already turns a *Hopf ORDER* —
a finitely generated `𝒪ᵥ`-subalgebra spanning the generic fibre and
closed under counit, antipode and comultiplication — into a finite flat
Hopf `𝒪ᵥ`-algebra together with the bialgebra equivalence of generic
fibres. So all that is proven here is that the intersection
`H₀ := ι ⁻¹' (1 ⊗ G)`, a `Subalgebra 𝒪ᵥ H` by `Subalgebra.comap`, IS
such an order. Its five clauses:
* *denominators* (used twice): every `q ∈ Q` has `c • q ∈ 1 ⊗ G` for
  some `c ∈ 𝒪ᵥ⁰` — a tensor induction, the pure-tensor case being
  `IsLocalization.exists_integer_multiple` for `Kᵥ = Frac 𝒪ᵥ`.
* *spanning*: for `x ∈ H`, `ι (c • x) = c • ι x ∈ 1 ⊗ G` gives
  `c • x ∈ H₀`, and `c` is invertible in `Kᵥ`
  (`IsLocalization.map_units`), so `x ∈ span Kᵥ H₀`.
* *the saturation retraction* — the technical core. Put
  `A := {g : G | 1 ⊗ g ∈ ι(H)}`, a `Submodule 𝒪ᵥ G`. Then `G ⧸ A` is
  torsion-free (`c • g ∈ A` forces `1 ⊗ g ∈ ι(H)`, dividing by the unit
  `c` inside the `Kᵥ`-subspace `ι(H)`) and module-finite, hence FREE
  over the DVR `𝒪ᵥ` (`Module.free_of_finite_type_torsion_free'`), hence
  projective: the quotient map `G → G ⧸ A` splits
  (`LinearMap.exists_rightInverse_of_surjective`), so `A` is a direct
  summand and `ret := id − sec ∘ mkQ : G →ₗ[𝒪ᵥ] G` retracts `G` onto
  `A`. Composing with the (Kᵥ-linear, hence 𝒪ᵥ-linear) left inverse
  `π` of the injection `ι` gives `s := π ∘ (1 ⊗ ·) ∘ ret : G →ₗ[𝒪ᵥ] H`
  with `ι (s g) = 1 ⊗ ret g`; its base change
  `ρ := s.liftBaseChange Kᵥ : Q →ₗ[Kᵥ] H` satisfies `ρ (1 ⊗ G) ⊆ H₀`
  and `ρ ∘ ι = id` (checked on `H₀`, extended by the spanning clause).
* *finite generation*: `H₀` is exactly `range s` (`⊆` because
  `ι (s g) = 1 ⊗ ret g`, `⊇` because for `x ∈ H₀` the `g` with
  `1 ⊗ g = ι x` lies in `A`, so `s g = x`), the image of the
  module-finite `G`.
* *counit* and *antipode*: transport along the bialgebra homomorphism
  `ι` (`BialgHomClass.counitAlgHom_comp`,
  `antipodeAlgHom_comp_bialgHom`) and then read off the base-change
  structure formulas at `1 ⊗ g` (`TensorProduct.counit_tmul`; the
  antipode of the base change is definitionally `1 ⊗ antipode`).
* *comultiplication* — the saturation step proper. `comul` of `ι x` is
  in the `𝒪ᵥ`-span of the pure tensors of `1 ⊗ G`
  (`TensorProduct.comul_tmul`, as in `exists_hopfOrder_baseChange`),
  and `ρ ⊗ ρ` maps that span into the `𝒪ᵥ`-span of the pure tensors of
  `H₀` while fixing `comul x` — because `(ρ ⊗ ρ) ∘ (ι ⊗ ι) = id`. This
  is the Lean incarnation of "`H₀ ⊗ H₀` is the intersection of
  `H ⊗[Kᵥ] H` with the image of `G ⊗[𝒪ᵥ] G`": saturation is what makes
  the retraction `ρ` exist integrally.
EXISTENCE of the order needs no `e < p − 1` bound — Raynaud's bound
enters only for uniqueness/full-faithfulness statements.
Unconditionally TRUE; no hypothesis package. -/
theorem exists_hopfOrder_of_subBialgebra
    {G : Type} [CommRing G] [HopfAlgebra 𝒪ᵥ G] [Module.Flat 𝒪ᵥ G]
    [Module.Finite 𝒪ᵥ G]
    {H : Type} [CommRing H] [HopfAlgebra Kᵥ H] [Module.Finite Kᵥ H]
    (ι : H →ₐc[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G))
    (hι : Function.Injective (ι : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G))) :
    ∃ (G' : Type) (_ : CommRing G') (_ : HopfAlgebra 𝒪ᵥ G') (_ : Module.Flat 𝒪ᵥ G')
      (_ : Module.Finite 𝒪ᵥ G'), Nonempty ((Kᵥ ⊗[𝒪ᵥ] G') ≃ₐc[Kᵥ] H) := by
  classical
  -- `H` becomes an `𝒪ᵥ`-algebra through `Kᵥ`
  letI : Algebra 𝒪ᵥ H := ((algebraMap Kᵥ H).comp (algebraMap 𝒪ᵥ Kᵥ)).toAlgebra
  haveI : IsScalarTower 𝒪ᵥ Kᵥ H := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set ιA : H →ₐ[Kᵥ] Kᵥ ⊗[𝒪ᵥ] G := (ι : H →ₐ[Kᵥ] Kᵥ ⊗[𝒪ᵥ] G)
  -- the canonical integral model `1 ⊗ G` inside the generic fibre
  obtain ⟨G₀, hmemG₀, hG₀mem⟩ : ∃ G₀ : Subalgebra 𝒪ᵥ (Kᵥ ⊗[𝒪ᵥ] G),
      (∀ g : G, ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g) ∈ G₀) ∧
      (∀ q ∈ G₀, ∃ g : G, ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g) = q) :=
    ⟨(Algebra.TensorProduct.includeRight : G →ₐ[𝒪ᵥ] Kᵥ ⊗[𝒪ᵥ] G).range,
      fun g => ⟨g, rfl⟩, fun _ hq => hq⟩
  -- the Hopf order candidate: the intersection `H ∩ G` formed inside the generic fibre
  obtain ⟨H₀, hmemH₀⟩ : ∃ H₀ : Subalgebra 𝒪ᵥ H, ∀ x : H, x ∈ H₀ ↔ ιA x ∈ G₀ :=
    ⟨G₀.comap (ιA.restrictScalars 𝒪ᵥ), fun _ => Iff.rfl⟩
  have hιsmul : ∀ (c : 𝒪ᵥ) (x : H), ιA (c • x) = c • ιA x := by
    intro c x
    rw [← IsScalarTower.algebraMap_smul Kᵥ c x, ← IsScalarTower.algebraMap_smul Kᵥ c (ιA x),
      map_smul]
  -- ### the three base-change structure formulas at `1 ⊗ g`
  have hcounitG : ∀ g : G,
      Bialgebra.counitAlgHom Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g) ∈
        (algebraMap 𝒪ᵥ Kᵥ).range := by
    intro g
    refine ⟨Coalgebra.counit (R := 𝒪ᵥ) g, ?_⟩
    show algebraMap 𝒪ᵥ Kᵥ (Coalgebra.counit (R := 𝒪ᵥ) g) =
      Coalgebra.counit (R := Kᵥ) ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g)
    rw [TensorProduct.counit_tmul]
    simp [Algebra.smul_def]
  have hantipodeG : ∀ g : G, HopfAlgebra.antipode Kᵥ ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g) =
      (1 : Kᵥ) ⊗ₜ[𝒪ᵥ] (HopfAlgebra.antipode 𝒪ᵥ g) := fun _ => rfl
  have hcomulG : ∀ g : G, Bialgebra.comulAlgHom Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g) ∈
      Submodule.span 𝒪ᵥ {z : (Kᵥ ⊗[𝒪ᵥ] G) ⊗[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G) |
        ∃ a ∈ G₀, ∃ b ∈ G₀, a ⊗ₜ[Kᵥ] b = z} := by
    intro g
    show Coalgebra.comul (R := Kᵥ) ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g) ∈ _
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    generalize Coalgebra.comul (R := 𝒪ᵥ) g = t
    induction t with
    | zero => simp
    | tmul a b =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
        exact Submodule.subset_span ⟨_, hmemG₀ a, _, hmemG₀ b, rfl⟩
    | add p q hp hq =>
        rw [TensorProduct.tmul_add, map_add]
        exact Submodule.add_mem _ hp hq
  -- ### denominators: every element of the generic fibre has an integral multiple
  have hden : ∀ q : Kᵥ ⊗[𝒪ᵥ] G, ∃ c ∈ nonZeroDivisors 𝒪ᵥ, c • q ∈ G₀ := by
    intro q
    induction q with
    | zero => exact ⟨1, one_mem _, by rw [one_smul]; exact zero_mem G₀⟩
    | tmul k g =>
        obtain ⟨⟨c, hc⟩, c', hc'⟩ :=
          IsLocalization.exists_integer_multiple (nonZeroDivisors 𝒪ᵥ) k
        refine ⟨c, hc, ?_⟩
        have hc'' : algebraMap 𝒪ᵥ Kᵥ c' = c • k := hc'
        have h1 : c • (k ⊗ₜ[𝒪ᵥ] g) = c' • ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g) := by
          rw [TensorProduct.smul_tmul' c k g, TensorProduct.smul_tmul' c' (1 : Kᵥ) g,
            ← hc'', Algebra.smul_def, mul_one]
        rw [h1]
        exact G₀.smul_mem (hmemG₀ g) c'
    | add p q hp hq =>
        obtain ⟨c₁, hc₁, h₁⟩ := hp
        obtain ⟨c₂, hc₂, h₂⟩ := hq
        refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, ?_⟩
        have h1 : (c₁ * c₂) • (p + q) = c₂ • (c₁ • p) + c₁ • (c₂ • q) := by
          simp only [smul_add, smul_smul]
          rw [mul_comm c₂ c₁]
        rw [h1]
        exact add_mem (G₀.smul_mem h₁ c₂) (G₀.smul_mem h₂ c₁)
  -- ### the saturated preimage lattice inside `G`
  obtain ⟨A, hmemA⟩ : ∃ A : Submodule 𝒪ᵥ G,
      ∀ g : G, g ∈ A ↔ ∃ x : H, ιA x = (1 : Kᵥ) ⊗ₜ[𝒪ᵥ] g :=
    ⟨Submodule.comap
      ((Algebra.TensorProduct.includeRight : G →ₐ[𝒪ᵥ] Kᵥ ⊗[𝒪ᵥ] G).toLinearMap)
      (Submodule.restrictScalars 𝒪ᵥ (LinearMap.range ιA.toLinearMap)), fun _ => Iff.rfl⟩
  haveI : Module.Finite 𝒪ᵥ (G ⧸ A) :=
    Module.Finite.of_surjective A.mkQ (Submodule.mkQ_surjective A)
  haveI : Module.IsTorsionFree 𝒪ᵥ (G ⧸ A) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective A x
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective A y
    have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
    have hrK : algebraMap 𝒪ᵥ Kᵥ r ≠ 0 := fun h0 =>
      hr0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective 𝒪ᵥ Kᵥ) r h0)
    have hsub : r • (a - b) ∈ A := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul, map_sub, smul_sub,
        sub_eq_zero]
      exact hxy
    have hab : a - b ∈ A := by
      obtain ⟨w, hw⟩ := (hmemA _).mp hsub
      refine (hmemA _).mpr ⟨(algebraMap 𝒪ᵥ Kᵥ r)⁻¹ • w, ?_⟩
      rw [map_smul, hw, TensorProduct.tmul_smul,
        ← IsScalarTower.algebraMap_smul Kᵥ r ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] (a - b)), inv_smul_smul₀ hrK]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hab
  -- the retraction of `G` onto the saturated lattice `A` (its cokernel is free)
  obtain ⟨ret, hretmem, hretid⟩ : ∃ ret : G →ₗ[𝒪ᵥ] G,
      (∀ g : G, ret g ∈ A) ∧ (∀ g ∈ A, ret g = g) := by
    obtain ⟨sec, hsec⟩ :=
      A.mkQ.exists_rightInverse_of_surjective (by rw [Submodule.range_mkQ])
    refine ⟨LinearMap.id - sec ∘ₗ A.mkQ, fun g => ?_, fun g hg => ?_⟩
    · have h0 : A.mkQ (g - sec (A.mkQ g)) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact (LinearMap.congr_fun hsec (A.mkQ g)).symm
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      exact h0
    · have h0 : A.mkQ g = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hg
      show g - sec (A.mkQ g) = g
      rw [h0, map_zero, sub_zero]
  -- ### the integral retraction `G → H₀` and its base change `ρ`
  obtain ⟨π, hπ⟩ := ιA.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hι)
  have hπι : ∀ x : H, π (ιA x) = x := fun x => LinearMap.congr_fun hπ x
  obtain ⟨s, hsapp⟩ : ∃ s : G →ₗ[𝒪ᵥ] H, ∀ g : G, s g = π ((1 : Kᵥ) ⊗ₜ[𝒪ᵥ] (ret g)) :=
    ⟨(π.restrictScalars 𝒪ᵥ) ∘ₗ
      ((Algebra.TensorProduct.includeRight : G →ₐ[𝒪ᵥ] Kᵥ ⊗[𝒪ᵥ] G).toLinearMap ∘ₗ ret),
      fun _ => rfl⟩
  have hsιA : ∀ g : G, ιA (s g) = (1 : Kᵥ) ⊗ₜ[𝒪ᵥ] (ret g) := by
    intro g
    obtain ⟨x, hx⟩ := (hmemA _).mp (hretmem g)
    rw [hsapp, ← hx, hπι]
  have hsmem : ∀ g : G, s g ∈ H₀ := by
    intro g
    rw [hmemH₀, hsιA]
    exact hmemG₀ _
  have hsH₀ : ∀ x ∈ H₀, ∃ g : G, s g = x := by
    intro x hx
    obtain ⟨g, hg⟩ := hG₀mem _ ((hmemH₀ x).mp hx)
    refine ⟨g, hι ?_⟩
    rw [hsιA, hretid g ((hmemA g).mpr ⟨x, hg.symm⟩)]
    exact hg
  obtain ⟨ρ, hρtmul⟩ : ∃ ρ : (Kᵥ ⊗[𝒪ᵥ] G) →ₗ[Kᵥ] H,
      ∀ (k : Kᵥ) (g : G), ρ (k ⊗ₜ[𝒪ᵥ] g) = k • s g :=
    ⟨s.liftBaseChange Kᵥ, fun _ _ => rfl⟩
  have hρG₀ : ∀ q ∈ G₀, ρ q ∈ H₀ := by
    intro q hq
    obtain ⟨g, hg⟩ := hG₀mem q hq
    rw [← hg, hρtmul, one_smul]
    exact hsmem g
  -- ### clause 2: the order spans the sub-bialgebra over `Kᵥ`
  have hspan : Submodule.span Kᵥ (H₀ : Set H) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨c, hc, hcq⟩ := hden (ιA x)
    have hcx : c • x ∈ H₀ := by
      rw [hmemH₀, hιsmul]
      exact hcq
    obtain ⟨u, hu⟩ := IsLocalization.map_units Kᵥ (⟨c, hc⟩ : nonZeroDivisors 𝒪ᵥ)
    have hx : x = (↑u⁻¹ : Kᵥ) • (c • x) := by
      rw [← IsScalarTower.algebraMap_smul Kᵥ c x]
      show x = (↑u⁻¹ : Kᵥ) • ((algebraMap 𝒪ᵥ Kᵥ c) • x)
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcx)
  -- ### clause 1: finite generation
  have hH₀range : (Subalgebra.toSubmodule H₀ : Submodule 𝒪ᵥ H) = LinearMap.range s := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨g, hg⟩ := hsH₀ x hx
      exact ⟨g, hg⟩
    · rintro x ⟨g, rfl⟩
      exact hsmem g
  have hfg : (Subalgebra.toSubmodule H₀).FG := by
    rw [hH₀range, LinearMap.range_eq_map]
    exact (Module.finite_def.mp inferInstance).map s
  -- ### clause 3: counit integrality
  have hcounit : ∀ x ∈ H₀, Bialgebra.counitAlgHom Kᵥ H x ∈ (algebraMap 𝒪ᵥ Kᵥ).range := by
    intro x hx
    obtain ⟨g, hg⟩ := hG₀mem _ ((hmemH₀ x).mp hx)
    have hcc : Bialgebra.counitAlgHom Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) (ιA x) =
        Bialgebra.counitAlgHom Kᵥ H x :=
      AlgHom.congr_fun (BialgHomClass.counitAlgHom_comp ι) x
    rw [← hcc, ← hg]
    exact hcounitG g
  -- ### clause 4: antipode stability
  have hantipode : ∀ x ∈ H₀, HopfAlgebra.antipode Kᵥ x ∈ H₀ := by
    intro x hx
    obtain ⟨g, hg⟩ := hG₀mem _ ((hmemH₀ x).mp hx)
    have hap : HopfAlgebra.antipode Kᵥ (ιA x) = ιA (HopfAlgebra.antipode Kᵥ x) :=
      AlgHom.congr_fun (antipodeAlgHom_comp_bialgHom ι) x
    rw [hmemH₀, ← hap, ← hg, hantipodeG g]
    exact hmemG₀ _
  -- ### clause 5: comultiplication closure — the saturation step
  have hsret : ∀ g : G, s (ret g) = s g := by
    intro g
    refine hι ?_
    rw [hsιA, hsιA, hretid _ (hretmem g)]
  have hρι : ∀ x : H, ρ (ιA x) = x := by
    have hext : (ρ ∘ₗ ιA.toLinearMap) = LinearMap.id (R := Kᵥ) (M := H) := by
      refine LinearMap.ext_on hspan ?_
      intro x hx
      obtain ⟨g, hg⟩ := hsH₀ x hx
      show ρ (ιA x) = x
      rw [← hg, hsιA, hρtmul, one_smul, hsret]
    intro x
    exact LinearMap.congr_fun hext x
  have hmapid : ∀ t : H ⊗[Kᵥ] H,
      TensorProduct.map ρ ρ (Algebra.TensorProduct.map ιA ιA t) = t := by
    intro t
    induction t with
    | zero => simp
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, hρι, hρι]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  have hcomul : ∀ x ∈ H₀, Bialgebra.comulAlgHom Kᵥ H x ∈
      Submodule.span 𝒪ᵥ {z : H ⊗[Kᵥ] H | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[Kᵥ] b = z} := by
    intro x hx
    obtain ⟨g, hg⟩ := hG₀mem _ ((hmemH₀ x).mp hx)
    have hcm : Bialgebra.comulAlgHom Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) (ιA x) =
        Algebra.TensorProduct.map ιA ιA (Bialgebra.comulAlgHom Kᵥ H x) :=
      (AlgHom.congr_fun (BialgHomClass.map_comp_comulAlgHom ι) x).symm
    have hmem0 : Bialgebra.comulAlgHom Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) (ιA x) ∈
        Submodule.span 𝒪ᵥ {z : (Kᵥ ⊗[𝒪ᵥ] G) ⊗[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G) |
          ∃ a ∈ G₀, ∃ b ∈ G₀, a ⊗ₜ[Kᵥ] b = z} := by
      rw [← hg]
      exact hcomulG g
    obtain ⟨F, hFapp⟩ : ∃ F : ((Kᵥ ⊗[𝒪ᵥ] G) ⊗[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G)) →ₗ[𝒪ᵥ] (H ⊗[Kᵥ] H),
        ∀ z, F z = TensorProduct.map ρ ρ z :=
      ⟨(TensorProduct.map ρ ρ).restrictScalars 𝒪ᵥ, fun _ => rfl⟩
    have h2 := Submodule.mem_map_of_mem (f := F) hmem0
    rw [Submodule.map_span] at h2
    have h3 : F (Bialgebra.comulAlgHom Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) (ιA x)) =
        Bialgebra.comulAlgHom Kᵥ H x := by
      rw [hFapp, hcm]
      exact hmapid _
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨z, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨ρ a, hρG₀ a ha, ρ b, hρG₀ b hb, by rw [hFapp, TensorProduct.map_tmul]⟩
  -- ### assemble: the Hopf order is a finite flat Hopf form
  obtain ⟨G', iCR, iHopf, iFin, iFlat, hequiv⟩ :=
    exists_flat_hopf_form_of_hopf_order 𝒪ᵥ Kᵥ H H₀ hfg hspan hcounit hantipode hcomul
  exact ⟨G', iCR, iHopf, iFlat, iFin, hequiv⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Quotient closure** (DECOMPOSED 2026-07-25 into the two leaves
`exists_etale_subBialgebra_of_points_surjective` (β, since PROVEN) and
`exists_hopfOrder_of_subBialgebra` (γ, still open) above, with the
assembly below PROVEN — the quotients half of Raynaud closure, added
2026-07-24 for
the E2b′ lattice-flatness transfer: the quotient of a finite flat group
scheme over the DVR `𝒪ᵥ` by a flat closed subgroup scheme is finite
flat — Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974); Tate, *Finite flat group schemes*, in
Cornell–Silverman–Stevens): a `Γ Kᵥ`-equivariant quotient of a flat
point-group at `v` is a flat point-group at `v`. The classical argument
is dual to `of_injective`, taking SUB-algebras of the witness where
that node quotients it, so the schematic-closure step is the easier
one; it runs in four steps, of which (α) is vacuous here and (δ) is the
proven glue below:
* (α) *finiteness* — folded into leaf (β), which needs it internally:
  the ambient point group of `Q := Kᵥ ⊗[𝒪ᵥ] G` is finite, hence so is
  `Y` through the surjection `π`.
* (β) *étale–Galois* — `exists_etale_subBialgebra_of_points_surjective`
  (PROVEN 2026-07-25): `Y` is the point group of a finite étale
  `Kᵥ`-Hopf algebra `H` embedded in `Q` by an injective `Kᵥ`-bialgebra
  map `ι`, the pullback of functions along the point surjection.
* (γ) *schematic closure over the DVR* — the leaf
  `exists_hopfOrder_of_subBialgebra`: `G' := H ∩ G` is a finite flat
  `𝒪ᵥ`-Hopf order with `Kᵥ ⊗[𝒪ᵥ] G' ≃ₐc[Kᵥ] H`.
* (δ) *conclusion* — PROVEN below: étaleness of the generic fibre
  transports along the underlying algebra equivalence
  (`Algebra.Etale.of_equiv`); precomposition with the bialgebra
  equivalence is an isomorphism of convolution point groups
  (`AlgHom.convMul_comp_bialgHom_distrib`, through the local
  `hbridge` identifying the bare-hom convolution monoid baked into
  `IsFlatPointsGroupAt` with mathlib's `WithConv` one — both are
  `lift φ ψ ∘ comul`) and is `Γ Kᵥ`-equivariant by
  associativity of composition; and the identification `e` supplied by
  (β) is equivariant because it is compatible with the equivariant
  surjection `π ∘ f`, which forces restriction of points along `ι` to be
  surjective.
Unconditionally TRUE; no hypothesis package (for `π` bijective this
is already `of_addEquiv`). CONSUMERS: the E2b′ lattice-flatness glue
`isFlatAt_lattice_of_generic_iso` (reduction of arbitrary open-ideal
levels to the cofinal `p`-power subtower); available to any future
finite-flat quotient need (e.g. E1b's closure half). -/
theorem IsFlatPointsGroupAt.of_surjective {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y]
    [DistribMulAction Γᵥ X] [DistribMulAction Γᵥ Y]
    (hX : IsFlatPointsGroupAt v X) (π : X →+ Y)
    (hπ : Function.Surjective π)
    (hπe : ∀ (g : Γᵥ) (x : X), π (g • x) = g • π x) :
    IsFlatPointsGroupAt v Y := by
  classical
  obtain ⟨G, iCR, iHopf, iFlat, iFin, iEt, f, hfbij, hfe⟩ := hX
  letI := iCR
  letI := iHopf
  letI := iFlat
  letI := iFin
  letI := iEt
  -- the composed equivariant surjection onto `Y` from the points of the
  -- generic fibre `Q := Kᵥ ⊗[𝒪ᵥ] G`
  have hpsurj : Function.Surjective (π.comp f) := hπ.comp hfbij.2
  have hpe : ∀ (g : Γᵥ) (x : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Ωᵥ)),
      (π.comp f) (g • x) = g • (π.comp f) x := by
    intro g x
    show π (f (g • x)) = g • π (f x)
    rw [hfe, hπe]
  -- (β): the étale sub-bialgebra `H ↪ Q` with point group `Y`
  obtain ⟨H, jCR, jHopf, jFin, jEt, ι, hιinj, e, he⟩ :=
    exists_etale_subBialgebra_of_points_surjective (Q := Kᵥ ⊗[𝒪ᵥ] G) (π.comp f)
      hpsurj hpe
  letI := jCR
  letI := jHopf
  letI := jFin
  letI := jEt
  -- postcomposition by a Galois element commutes with precomposition
  have hsmulcomp : ∀ {B C : Type} [CommRing B] [Algebra Kᵥ B] [CommRing C]
      [Algebra Kᵥ C] (g : Γᵥ) (χ : B →ₐ[Kᵥ] C) (ψ : C →ₐ[Kᵥ] Ωᵥ),
      (g • ψ).comp χ = g • (ψ.comp χ) := fun g χ ψ => AlgHom.ext fun _ => rfl
  -- the identification of the points of `H` with `Y` is equivariant:
  -- restriction of points along `ι` is surjective because `π ∘ f` is
  have hee : ∀ (g : Γᵥ) (u : Additive (H →ₐ[Kᵥ] Ωᵥ)), e (g • u) = g • e u := by
    intro g u
    obtain ⟨w, hw⟩ := hpsurj (e u)
    have hφ : Additive.ofMul
        ((Additive.toMul w).comp (ι : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G))) = u :=
      e.injective (by rw [he]; exact hw)
    rw [← hφ]
    have h1 : g • Additive.ofMul
        ((Additive.toMul w).comp (ι : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G))) =
        Additive.ofMul ((g • Additive.toMul w).comp
          (ι : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G))) :=
      congrArg Additive.ofMul (hsmulcomp g _ _).symm
    rw [h1, he, he]
    exact hpe g w
  -- (γ): the finite flat Hopf order `G'` with generic fibre `H`
  obtain ⟨G', kCR, kHopf, kFlat, kFin, ⟨ε⟩⟩ :=
    exists_hopfOrder_of_subBialgebra (G := G) (H := H) ι hιinj
  letI := kCR
  letI := kHopf
  letI := kFlat
  letI := kFin
  -- (δ): precomposition with the form equivalence identifies the points
  let ι' : H →ₐc[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G') := ε.symm.toBialgHom
  let ι'' : (Kᵥ ⊗[𝒪ᵥ] G') →ₐc[Kᵥ] H := ε.toBialgHom
  let Φ : ((Kᵥ ⊗[𝒪ᵥ] G') →ₐ[Kᵥ] Ωᵥ) ≃ (H →ₐ[Kᵥ] Ωᵥ) :=
    { toFun := fun ψ => ψ.comp (ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G'))
      invFun := fun φ => φ.comp (ι'' : (Kᵥ ⊗[𝒪ᵥ] G') →ₐ[Kᵥ] H)
      left_inv := fun ψ => AlgHom.ext fun x => by
        show ψ ((ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G'))
          ((ι'' : (Kᵥ ⊗[𝒪ᵥ] G') →ₐ[Kᵥ] H) x)) = ψ x
        congr 1
        exact ε.symm_apply_apply x
      right_inv := fun φ => AlgHom.ext fun x => by
        show φ ((ι'' : (Kᵥ ⊗[𝒪ᵥ] G') →ₐ[Kᵥ] H)
          ((ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G')) x)) = φ x
        congr 1
        exact ε.apply_symm_apply x }
  -- the bare-hom convolution monoid on `B →ₐ[Kᵥ] Ωᵥ` (the one baked into
  -- `IsFlatPointsGroupAt`) has the same product as mathlib's `WithConv`:
  -- both are `lift φ ψ ∘ comul`
  have hbridge : ∀ {B : Type} [CommRing B] [Bialgebra Kᵥ B] (φ ψ : B →ₐ[Kᵥ] Ωᵥ),
      φ * ψ = (WithConv.toConv φ * WithConv.toConv ψ).ofConv :=
    fun {_} _ _ φ ψ => AlgHom.ext fun x => by
      rw [AlgHom.convMul_apply]
      rfl
  have hΦmul : ∀ ψ₁ ψ₂ : (Kᵥ ⊗[𝒪ᵥ] G') →ₐ[Kᵥ] Ωᵥ, Φ (ψ₁ * ψ₂) = Φ ψ₁ * Φ ψ₂ := by
    intro ψ₁ ψ₂
    show (ψ₁ * ψ₂).comp (ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G')) =
      (ψ₁.comp (ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G'))) *
        (ψ₂.comp (ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G')))
    have d := AlgHom.convMul_comp_bialgHom_distrib
      (WithConv.toConv ψ₁) (WithConv.toConv ψ₂) ι'
    rw [hbridge ψ₁ ψ₂,
      hbridge (ψ₁.comp (ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G')))
        (ψ₂.comp (ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G')))]
    exact d
  let g₀ : Additive ((Kᵥ ⊗[𝒪ᵥ] G') →ₐ[Kᵥ] Ωᵥ) ≃+ Additive (H →ₐ[Kᵥ] Ωᵥ) :=
    { toFun := fun x => Additive.ofMul (Φ (Additive.toMul x))
      invFun := fun y => Additive.ofMul (Φ.symm (Additive.toMul y))
      left_inv := fun x => congrArg Additive.ofMul (Φ.symm_apply_apply _)
      right_inv := fun y => congrArg Additive.ofMul (Φ.apply_symm_apply _)
      map_add' := fun x y => congrArg Additive.ofMul (hΦmul _ _) }
  refine ⟨G', kCR, kHopf, kFlat, kFin,
    Algebra.Etale.of_equiv ε.toAlgEquiv.symm,
    (g₀.trans e).toAddMonoidHom, (g₀.trans e).bijective, ?_⟩
  intro g y
  show e (g₀ (g • y)) = g • e (g₀ y)
  have hg : g₀ (g • y) = g • g₀ y :=
    congrArg Additive.ofMul
      (hsmulcomp g (ι' : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] G')) (Additive.toMul y))
  rw [hg]
  exact hee g (g₀ y)

end RaynaudClosure

end GaloisRepresentation.Modularity

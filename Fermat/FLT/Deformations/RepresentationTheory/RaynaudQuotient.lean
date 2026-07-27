/-
Deformations/RepresentationTheory/RaynaudQuotient.lean — own work for the
Fermat project (not vendored from the FLT project).

# The `IsFlatPointsGroupAt` (Raynaud closure) development, in a NEUTRAL HOME

This module exists to resolve the import-reachability problem recorded in
the HOME AUDIT of `hasFlatProlongationAt_of_surjective`
(`Modularity/KhareWintenberger.lean`, 2026-07-25).

The whole Raynaud closure development for the flat point-group carrier —
closure of finite flat group schemes over the DVR `𝒪ᵥ` under finite
PRODUCTS, under Galois-stable SUBOBJECTS of the generic fibre, and under
equivariant QUOTIENTS, read on `ℚ̄ᵥ`-points — was PROVEN on 2026-07-24/25
in `Modularity/Interface.lean` as `IsFlatPointsGroupAt.prod`,
`.of_injective`, `.pi` and `.of_surjective`, the last over the two bricks

* `exists_etale_subBialgebra_of_points_surjective` (the étale–Galois half),
* `exists_hopfOrder_of_subBialgebra`               (the schematic closure
  over the DVR),

all of them sorry-free there.  But `Interface.lean` IMPORTS
`Modularity/KhareWintenberger.lean`, which in turn sits above
`GaloisRepresentation/HardlyRamified/Deformation.lean`, so those proofs are
import-unreachable from the three leaves that want them: consuming them
would be a literal import cycle, which the pillar-β circularity guard
forbids.  The three leaves are

* `hasFlatProlongationAt_of_surjective`     (`Modularity/KhareWintenberger.lean`),
* `hasFlatProlongationAt_of_prod_injection` (`…/HardlyRamified/Deformation.lean`),
* `hasFlatProlongationAt_of_pi_surjection`  (`…/HardlyRamified/Deformation.lean`),

each of which becomes a two-or-three line assembly over the declarations
below.  Only the first is discharged here (this module's own task); the
other two are left to their owners, who now merely have to import this
module.

The HOME AUDIT names the fix — put the brick in a module BELOW both — and
names the two costs that stopped the original author from performing it:
`Interface.lean`'s copy is separately owned (so it must not be deleted out
from under its owner), and `FlatProlongation.lean` sits under the 30k-line
`ModThree.lean` cone (so editing it forces a full-cone rebuild in every
worktree of the fleet).  This module dodges both: it is a NEW sibling of
`FlatProlongation.lean`, imported only by `KhareWintenberger.lean`, so
nothing under `ModThree.lean` is disturbed and `Interface.lean` is not
touched at all.

## Duplication is deliberate and TEMPORARY — read before deduplicating

Everything below is, at the time of writing, character-for-character the
corresponding declarations of `Interface.lean` — its `TensorPointsGlue`
and `BasePointsGlue` sections (Interface lines 5375–5531 of the commit
this was taken from) and the `RaynaudClosure` chain (Interface lines
5592–6490, plus the two bricks and `of_surjective` further down) —
re-homed here inside `namespace RaynaudQuotient` so that the two copies
cannot clash when `Interface.lean` (transitively) imports this file.  No
mathematics was rewritten and no third copy of any argument exists: the
verbatim-ness is checkable mechanically and is meant to be checked.

That is the FIRST half of the unification the HOME AUDIT prescribes.  The
SECOND half — deleting `Interface.lean`'s copies of

* the `TensorPointsGlue` section (`tensorPoints_convOne`,
  `tensorPoints_convMul`, `tensorPoints_comp`, `algHomTensorProdEquiv`),
* the `BasePointsGlue` section (`basePointsTensorEquiv` and its
  `_apply` / `_one` / `_mul` / `_smul` laws),
* `IsFlatPointsGroupAt` and
  `GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt`,
* `IsFlatPointsGroupAt.of_addEquiv`, `.of_subsingleton`, `.prod`,
  `.of_injective`, `.pi`, `.of_surjective`,
* the Hopf-order helpers `algHom_convOne_comp_bialgHom`,
  `algHom_convMul_comp_bialgHom`, `exists_hopfOrder_baseChange`,
  `exists_hopfOrder_map_of_surjective_bialgHom`,
  `isFlatPointsGroupAt_of_hopfOrder`,
  `exists_etaleHopfAlgebra_of_points_embedding`,
  `exists_surjective_bialgHom_of_points_injection`,
* the two quotient bricks `exists_etale_subBialgebra_of_points_surjective`
  and `exists_hopfOrder_of_subBialgebra`

and replacing them by `export RaynaudQuotient (...)` — is a pure DELETION
in `Interface.lean`, to be performed by that file's owner.  It was
deliberately not done here, because `Interface.lean` has concurrent owners
and this module's task was to make the content reachable, not to edit
someone else's region.  Whoever performs it should delete, not move: the
declarations here are the survivors.

Nothing else of `Interface.lean` was touched.  In particular its
prolongation-level consumers of this chain (`isFlatAt_lattice_of_generic_iso`
and friends) stay where they are and keep resolving against its own copies
until the deletion happens.

## FREE-FLOATING WINDOW — do not sweep this module yet

Only `GaloisRep.HasFlatProlongationAt.of_surjective` at the foot of this
file is consumed as of the commit that introduces it, by
`hasFlatProlongationAt_of_surjective` in `Modularity/KhareWintenberger.lean`.
Its own chain — `hasFlatProlongationAt_iff_isFlatPointsGroupAt`,
`exists_etale_subBialgebra_of_points_surjective`,
`exists_hopfOrder_of_subBialgebra` — therefore lies in the cone of the root
theorem, but the PRODUCT and SUBOBJECT halves (`IsFlatPointsGroupAt.prod`,
`.of_injective`, `.pi`, `.of_addEquiv`, `.of_subsingleton`, the Hopf-order
helpers, and both glue sections) do NOT, until the two leaves

* `hasFlatProlongationAt_of_prod_injection`
  (`…/HardlyRamified/Deformation.lean`) and
* `hasFlatProlongationAt_of_pi_surjection` (same file)

are discharged over them — which is a two-or-three line assembly each, and
is exactly why they were re-homed here (that file cannot import
`Modularity/*`; this module is below it and outside its import cone, so it
can).  Both are owned.  So this module is EXPECTED to report floaters in
the interval between this commit and those two, and the correct response is
to wait for them, not to delete: deleting would only force a fourth copy of
Raynaud's closure theorem to be written somewhere else.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Topology.Algebra.IntermediateField
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
-- the `HopfAlgebra R (A ⊗[R] B)` instance, which is the witness of the
-- PRODUCT half of the Raynaud closure (`IsFlatPointsGroupAt.prod`)
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Basic
import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat

namespace RaynaudQuotient

open IsDedekindDomain
open scoped TensorProduct

universe u

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

/-! ##### Schematic closure over the DVR (PROVEN 2026-07-25)

The commutative-algebra half of Raynaud's subobject closure: Hopf
ORDERS (finitely generated `𝒪ᵥ`-subalgebras spanning the generic
fibre and stable under counit, antipode and comultiplication, in the
exact vocabulary of the PROVEN
`exists_flat_hopf_form_of_hopf_order` of
`KnownIn1980s/EllipticCurves/Flat.lean`) exist canonically in the
generic fibre of a finite flat Hopf algebra
(`exists_hopfOrder_baseChange`), push forward along a SURJECTIVE
bialgebra homomorphism (`exists_hopfOrder_map_of_surjective_bialgHom`
— the surjective analogue of the vendored
`exists_hopf_order_map_of_bialgEquiv`), and turn back into a flat
point-group package (`isFlatPointsGroupAt_of_hopfOrder`). No
`e < p − 1` bound is needed anywhere: Raynaud's bound enters only for
uniqueness/full-faithfulness, never for existence. -/

set_option maxHeartbeats 1000000 in
/-- **The convolution unit is preserved by precomposition with a
bialgebra homomorphism** (PROVEN): the unit of the vendored bare-hom
convolution monoid on `C →ₐ[K₁] L₁` (`Deformations/RepresentationTheory/
Etale.lean`, the monoid used by `GaloisRep.HasFlatProlongationAt` and
hence by `IsFlatPointsGroupAt`) is `Algebra.ofId ∘ counit`, and a
bialgebra homomorphism intertwines the counits. -/
theorem algHom_convOne_comp_bialgHom {K₁ L₁ : Type u} [Field K₁] [Field L₁]
    [Algebra K₁ L₁] {B C : Type*} [CommRing B] [Bialgebra K₁ B] [CommRing C]
    [Bialgebra K₁ C] (Φ : B →ₐc[K₁] C) :
    (1 : C →ₐ[K₁] L₁).comp (Φ : B →ₐ[K₁] C) = 1 := by
  have hAA : AlgHomClass.toAlgHom Φ = (Φ : B →ₐ[K₁] C) := rfl
  have hc : (Bialgebra.counitAlgHom K₁ C).comp (Φ : B →ₐ[K₁] C) =
      Bialgebra.counitAlgHom K₁ B := by
    rw [← hAA]; exact BialgHomClass.counitAlgHom_comp Φ
  have h1 : (1 : C →ₐ[K₁] L₁) =
      (Algebra.ofId K₁ L₁).comp (Bialgebra.counitAlgHom K₁ C) := rfl
  have h2 : (1 : B →ₐ[K₁] L₁) =
      (Algebra.ofId K₁ L₁).comp (Bialgebra.counitAlgHom K₁ B) := rfl
  rw [h1, h2, AlgHom.comp_assoc, hc]

set_option maxHeartbeats 1000000 in
/-- **The convolution product is preserved by precomposition with a
bialgebra homomorphism** (PROVEN): the vendored bare-hom convolution
agrees with mathlib's `WithConv` convolution
(`vendored_mul_eq_convMul`), for which this is
`AlgHom.convMul_comp_bialgHom_distrib`. Together with
`algHom_convOne_comp_bialgHom` this makes precomposition with a
bialgebra homomorphism an additive map of the point groups. -/
theorem algHom_convMul_comp_bialgHom {K₁ L₁ : Type u} [Field K₁] [Field L₁]
    [Algebra K₁ L₁] {B C : Type*} [CommRing B] [Bialgebra K₁ B] [CommRing C]
    [Bialgebra K₁ C] (Φ : B →ₐc[K₁] C) (φ ψ : C →ₐ[K₁] L₁) :
    (φ * ψ).comp (Φ : B →ₐ[K₁] C) =
      (φ.comp (Φ : B →ₐ[K₁] C)) * (ψ.comp (Φ : B →ₐ[K₁] C)) := by
  rw [vendored_mul_eq_convMul φ ψ, vendored_mul_eq_convMul]
  exact AlgHom.convMul_comp_bialgHom_distrib
    (WithConv.toConv φ) (WithConv.toConv ψ) Φ

set_option maxHeartbeats 1000000 in
/-- **The canonical Hopf order in a base-changed Hopf algebra**
(PROVEN, curve-free and place-free): for a module-finite Hopf
`R`-algebra `G` and any `R`-algebra `S`, the image `1 ⊗ G` of `G` in
`S ⊗[R] G` is a Hopf ORDER — finitely generated over `R`, spanning
`S ⊗[R] G` over `S`, with counit landing in the image of `R`, stable
under the antipode, and with comultiplication in the `R`-span of its
pure tensors — in the exact vocabulary consumed by
`exists_flat_hopf_form_of_hopf_order`. All five clauses are the
base-change structure formulas `TensorProduct.counit_tmul`,
`TensorProduct.comul_tmul` and the definitional antipode of the base
change, evaluated at `1 ⊗ₜ g`. -/
theorem exists_hopfOrder_baseChange
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (G : Type*) [CommRing G] [HopfAlgebra R G] [Module.Finite R G] :
    ∃ G₀ : Subalgebra R (S ⊗[R] G),
      (Subalgebra.toSubmodule G₀).FG ∧
      Submodule.span S (G₀ : Set (S ⊗[R] G)) = ⊤ ∧
      (∀ x ∈ G₀, Bialgebra.counitAlgHom S (S ⊗[R] G) x ∈ (algebraMap R S).range) ∧
      (∀ x ∈ G₀, HopfAlgebra.antipode S x ∈ G₀) ∧
      (∀ x ∈ G₀, Bialgebra.comulAlgHom S (S ⊗[R] G) x ∈
        Submodule.span R {z : (S ⊗[R] G) ⊗[S] (S ⊗[R] G) |
          ∃ a ∈ G₀, ∃ b ∈ G₀, a ⊗ₜ[S] b = z}) := by
  classical
  set G₀ : Subalgebra R (S ⊗[R] G) :=
    (⊤ : Subalgebra R G).map (Algebra.TensorProduct.includeRight : G →ₐ[R] S ⊗[R] G)
    with hG₀
  have hmem : ∀ g : G, ((1 : S) ⊗ₜ[R] g) ∈ G₀ :=
    fun g => Subalgebra.mem_map.mpr ⟨g, Algebra.mem_top, rfl⟩
  have htop : (Subalgebra.toSubmodule (⊤ : Subalgebra R G)) = ⊤ := by ext x; simp
  refine ⟨G₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hG₀, Subalgebra.map_toSubmodule, htop]
    exact (Module.finite_def.mp inferInstance).map _
  · rw [eq_top_iff]
    rintro x -
    induction x with
    | zero => exact Submodule.zero_mem _
    | tmul s g =>
        have hs : s ⊗ₜ[R] g = s • ((1 : S) ⊗ₜ[R] g) := by
          rw [TensorProduct.smul_tmul']; simp
        rw [hs]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem g))
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  · rintro x hx
    obtain ⟨g, -, rfl⟩ := Subalgebra.mem_map.mp hx
    refine ⟨Coalgebra.counit (R := R) g, ?_⟩
    show algebraMap R S (Coalgebra.counit (R := R) g) =
      Coalgebra.counit (R := S) ((1 : S) ⊗ₜ[R] g)
    rw [TensorProduct.counit_tmul]
    simp [Algebra.smul_def]
  · rintro x hx
    obtain ⟨g, -, rfl⟩ := Subalgebra.mem_map.mp hx
    show HopfAlgebra.antipode (R := S) ((1 : S) ⊗ₜ[R] g) ∈ G₀
    show (1 : S) ⊗ₜ[R] (HopfAlgebra.antipode (R := R) g) ∈ G₀
    exact hmem _
  · rintro x hx
    obtain ⟨g, -, rfl⟩ := Subalgebra.mem_map.mp hx
    show Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] g) ∈ _
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    generalize Coalgebra.comul (R := R) g = t
    induction t with
    | zero => simp
    | tmul a b =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
        exact Submodule.subset_span ⟨_, hmem a, _, hmem b, rfl⟩
    | add p q hp hq =>
        rw [TensorProduct.tmul_add, map_add]
        exact Submodule.add_mem _ hp hq

set_option maxHeartbeats 1000000 in
/-- **Hopf orders push forward along surjective bialgebra
homomorphisms** (PROVEN, curve-free and place-free — the SURJECTIVE
analogue of the vendored `exists_hopf_order_map_of_bialgEquiv`, by
the same pointwise structure-map compatibilities; surjectivity is
used only for the spanning clause, where the equivalence proof used
`Φ.toAlgEquiv.surjective`): the image of a Hopf-closed `R₀`-order
under a surjective `K₀`-bialgebra homomorphism of commutative Hopf
`K₀`-algebras (both towers over `R₀`) is again a Hopf-closed order.
This is the schematic-closure step of Raynaud's subobject theorem:
the generic-fibre quotient is `H`, and the order is the image of the
integral model — module-finiteness, counit integrality, antipode
stability and comultiplication closure transport pointwise, the
antipode one by `antipodeAlgHom_comp_bialgHom`. -/
theorem exists_hopfOrder_map_of_surjective_bialgHom
    {R₀ : Type*} [CommRing R₀] {K₀ : Type*} [Field K₀] [Algebra R₀ K₀]
    (HK₁ : Type*) [CommRing HK₁] [HopfAlgebra K₀ HK₁]
    [Algebra R₀ HK₁] [IsScalarTower R₀ K₀ HK₁]
    (HK₂ : Type*) [CommRing HK₂] [HopfAlgebra K₀ HK₂]
    [Algebra R₀ HK₂] [IsScalarTower R₀ K₀ HK₂]
    (Φ : HK₁ →ₐc[K₀] HK₂) (hΦ : Function.Surjective (Φ : HK₁ →ₐ[K₀] HK₂))
    (H₀ : Subalgebra R₀ HK₁)
    (hfg : (Subalgebra.toSubmodule H₀).FG)
    (hspan : Submodule.span K₀ (H₀ : Set HK₁) = ⊤)
    (hcounit : ∀ x ∈ H₀, Bialgebra.counitAlgHom K₀ HK₁ x ∈ (algebraMap R₀ K₀).range)
    (hantipode : ∀ x ∈ H₀, HopfAlgebra.antipode K₀ x ∈ H₀)
    (hcomul : ∀ x ∈ H₀, Bialgebra.comulAlgHom K₀ HK₁ x ∈
      Submodule.span R₀ {z : HK₁ ⊗[K₀] HK₁ | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[K₀] b = z}) :
    ∃ H₀' : Subalgebra R₀ HK₂,
      (Subalgebra.toSubmodule H₀').FG ∧
      Submodule.span K₀ (H₀' : Set HK₂) = ⊤ ∧
      (∀ x ∈ H₀', Bialgebra.counitAlgHom K₀ HK₂ x ∈ (algebraMap R₀ K₀).range) ∧
      (∀ x ∈ H₀', HopfAlgebra.antipode K₀ x ∈ H₀') ∧
      (∀ x ∈ H₀', Bialgebra.comulAlgHom K₀ HK₂ x ∈
        Submodule.span R₀ {z : HK₂ ⊗[K₀] HK₂ |
          ∃ a ∈ H₀', ∃ b ∈ H₀', a ⊗ₜ[K₀] b = z}) := by
  classical
  set ΦA : HK₁ →ₐ[K₀] HK₂ := (Φ : HK₁ →ₐ[K₀] HK₂) with hΦA
  set ψ : HK₁ →ₐ[R₀] HK₂ := ΦA.restrictScalars R₀ with hψ
  have hcounit_pt : ∀ x : HK₁, Bialgebra.counitAlgHom K₀ HK₂ (ΦA x) =
      Bialgebra.counitAlgHom K₀ HK₁ x := fun x =>
    AlgHom.congr_fun (BialgHomClass.counitAlgHom_comp Φ) x
  have hantipode_pt : ∀ x : HK₁, HopfAlgebra.antipode K₀ (ΦA x) =
      ΦA (HopfAlgebra.antipode K₀ x) := fun x =>
    AlgHom.congr_fun (antipodeAlgHom_comp_bialgHom Φ) x
  have hcomul_pt : ∀ x : HK₁, Bialgebra.comulAlgHom K₀ HK₂ (ΦA x) =
      Algebra.TensorProduct.map ΦA ΦA (Bialgebra.comulAlgHom K₀ HK₁ x) := fun x =>
    (AlgHom.congr_fun (BialgHomClass.map_comp_comulAlgHom Φ) x).symm
  refine ⟨H₀.map ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subalgebra.map_toSubmodule]
    exact hfg.map ψ.toLinearMap
  · have hcoe : (↑(H₀.map ψ) : Set HK₂) = ⇑ΦA.toLinearMap '' (H₀ : Set HK₁) := by
      rw [Subalgebra.coe_map]; rfl
    rw [hcoe, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact hΦ
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    show Bialgebra.counitAlgHom K₀ HK₂ (ΦA x) ∈ _
    rw [hcounit_pt]
    exact hcounit x hx
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    show HopfAlgebra.antipode K₀ (ΦA x) ∈ _
    rw [hantipode_pt]
    exact Subalgebra.mem_map.mpr ⟨HopfAlgebra.antipode K₀ x, hantipode x hx, rfl⟩
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    show Bialgebra.comulAlgHom K₀ HK₂ (ΦA x) ∈ _
    rw [hcomul_pt]
    set T : HK₁ ⊗[K₀] HK₁ →ₗ[R₀] HK₂ ⊗[K₀] HK₂ :=
      ((Algebra.TensorProduct.map ΦA ΦA).toLinearMap).restrictScalars R₀ with hT
    have hmem : T (Bialgebra.comulAlgHom K₀ HK₁ x) ∈
        Submodule.map T (Submodule.span R₀
          {z : HK₁ ⊗[K₀] HK₁ | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[K₀] b = z}) :=
      Submodule.mem_map_of_mem (hcomul x hx)
    rw [Submodule.map_span] at hmem
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨z, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨ΦA a, Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩,
      ΦA b, Subalgebra.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **A Hopf order with the right points is a flat point-group
package** (PROVEN): if a finite étale `Kᵥ`-Hopf algebra `H` carries a
Hopf `𝒪ᵥ`-order `H₀` and its `Kᵥᵃˡᵍ`-points are, `Γ Kᵥ`-equivariantly,
the group `X`, then `X` is a flat point-group at `v`. Proof: the
vendored `exists_flat_hopf_form_of_hopf_order` turns the order into a
finite flat Hopf `𝒪ᵥ`-algebra `H'` with a bialgebra equivalence
`Kᵥ ⊗[𝒪ᵥ] H' ≃ₐc H`, whose generic fibre is therefore étale
(`Algebra.Etale.of_equiv`); precomposition with the inverse
equivalence identifies the points of `Kᵥ ⊗[𝒪ᵥ] H'` with those of `H`
— bijectively (an inverse is precomposition with the equivalence
itself) and ADDITIVELY, since a bialgebra homomorphism preserves the
convolution unit and product (`algHom_convOne_comp_bialgHom`,
`algHom_convMul_comp_bialgHom`) — and `Γ Kᵥ`-equivariantly, because
the Galois action is postcomposition, which commutes with
precomposition. -/
theorem isFlatPointsGroupAt_of_hopfOrder {X : Type*} [AddCommGroup X]
    [DistribMulAction Γᵥ X]
    (H : Type) [CommRing H] [HopfAlgebra Kᵥ H] [Module.Finite Kᵥ H]
    [Algebra.Etale Kᵥ H] [Algebra 𝒪ᵥ H] [IsScalarTower 𝒪ᵥ Kᵥ H]
    (H₀ : Subalgebra 𝒪ᵥ H)
    (hfg : (Subalgebra.toSubmodule H₀).FG)
    (hspan : Submodule.span Kᵥ (H₀ : Set H) = ⊤)
    (hcounit : ∀ x ∈ H₀, Bialgebra.counitAlgHom Kᵥ H x ∈ (algebraMap 𝒪ᵥ Kᵥ).range)
    (hantipode : ∀ x ∈ H₀, HopfAlgebra.antipode Kᵥ x ∈ H₀)
    (hcomul : ∀ x ∈ H₀, Bialgebra.comulAlgHom Kᵥ H x ∈
      Submodule.span 𝒪ᵥ {z : H ⊗[Kᵥ] H | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[Kᵥ] b = z})
    (e : Additive (H →ₐ[Kᵥ] Ωᵥ) →+ X) (hbij : Function.Bijective e)
    (hee : ∀ (g : Γᵥ) (y : Additive (H →ₐ[Kᵥ] Ωᵥ)), e (g • y) = g • e y) :
    IsFlatPointsGroupAt v X := by
  classical
  obtain ⟨H', iCR, iHopf, iFin, iFlat, ⟨Φ⟩⟩ :=
    exists_flat_hopf_form_of_hopf_order 𝒪ᵥ Kᵥ H H₀ hfg hspan hcounit hantipode hcomul
  letI := iCR
  letI := iHopf
  set Ψ : H →ₐc[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] H') := Φ.symm.toBialgHom with hΨ
  set ΨA : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] H') := (Ψ : H →ₐ[Kᵥ] (Kᵥ ⊗[𝒪ᵥ] H')) with hΨA
  have hmn : ∀ ψ : (Kᵥ ⊗[𝒪ᵥ] H') →ₐ[Kᵥ] Ωᵥ,
      (ψ.comp ΨA).comp (Φ.toAlgEquiv.toAlgHom) = ψ := fun ψ =>
    AlgHom.ext fun x => by
      show ψ (ΨA (Φ.toAlgEquiv.toAlgHom x)) = ψ x
      have hx : ΨA (Φ.toAlgEquiv.toAlgHom x) = x := by
        show Φ.symm (Φ x) = x
        simp
      rw [hx]
  have hnm : ∀ φ : H →ₐ[Kᵥ] Ωᵥ,
      (φ.comp (Φ.toAlgEquiv.toAlgHom)).comp ΨA = φ := fun φ =>
    AlgHom.ext fun x => by
      show φ (Φ.toAlgEquiv.toAlgHom (ΨA x)) = φ x
      have hx : Φ.toAlgEquiv.toAlgHom (ΨA x) = x := by
        show Φ (Φ.symm x) = x
        simp
      rw [hx]
  refine ⟨H', iCR, iHopf, iFlat, iFin, Algebra.Etale.of_equiv Φ.toAlgEquiv.symm,
    { toFun := fun ψ => e (Additive.ofMul ((Additive.toMul ψ).comp ΨA))
      map_zero' := by
        show e (Additive.ofMul ((1 : (Kᵥ ⊗[𝒪ᵥ] H') →ₐ[Kᵥ] Ωᵥ).comp ΨA)) = 0
        rw [hΨA, algHom_convOne_comp_bialgHom Ψ]
        exact map_zero e
      map_add' := fun ψ χ => by
        show e (Additive.ofMul (((Additive.toMul ψ) * (Additive.toMul χ)).comp ΨA)) = _
        rw [hΨA, algHom_convMul_comp_bialgHom Ψ]
        exact map_add e _ _ }, ?_, ?_⟩
  · refine hbij.comp (Additive.ofMul.bijective.comp ?_)
    exact Function.bijective_iff_has_inverse.mpr
      ⟨fun φ => φ.comp (Φ.toAlgEquiv.toAlgHom), hmn, hnm⟩
  · intro g y
    show e (Additive.ofMul ((Additive.toMul (g • y)).comp ΨA)) = _
    have h1 : (Additive.toMul (g • y)).comp ΨA =
        Additive.toMul (g • (Additive.ofMul ((Additive.toMul y).comp ΨA))) :=
      AlgHom.ext fun _ => rfl
    rw [h1]
    exact hee g _

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Étale–Galois, existence half** (PROVEN 2026-07-25 — step (β1) of
the subobject closure, opened the same day by the decomposition of
`IsFlatPointsGroupAt.of_injective`): a `Γ Kᵥ`-module `Y` that embeds
`Γ Kᵥ`-equivariantly into the `Kᵥᵃˡᵍ`-points of a finite étale
`Kᵥ`-Hopf algebra `Q` is ITSELF the point group of a finite étale
`Kᵥ`-Hopf algebra. This is Grothendieck's anti-equivalence between
finite étale `Kᵥ`-algebras and finite discrete `Γ Kᵥ`-sets, with the
group structure carried along. The proof runs entirely inside the
PROVEN Gelfand-duality machinery of
`KnownIn1980s/EllipticCurves/Flat.lean`:
* `Y` is FINITE: `Q` is module-finite over `Kᵥ`, so it has finitely
  many `Kᵥᵃˡᵍ`-points (`Finite.algHom` is an instance on the pin) and
  `j` is injective.
* the action of `Γ Kᵥ` on `Y` factors through a FINITE Galois
  quotient `Gal(L/Kᵥ)`. Concretely: a `Kᵥ`-basis `b` of `Q` is finite,
  so the values `φ (b i)` over the finitely many points `φ` form a
  FINITE subset `T` of `Kᵥᵃˡᵍ`; `L₀ := Kᵥ(T)` is finite over `Kᵥ`
  (`IntermediateField.finiteDimensional_adjoin`, every element being
  integral) and contains the whole image of every point, since points
  are `Kᵥ`-linear in `b`; its normal closure `L` in `Kᵥᵃˡᵍ` is finite
  (`normalClosure.is_finiteDimensional`) and Galois (normal, and
  separable in characteristic zero). Two absolute automorphisms with
  the same restriction to `L` therefore act identically on the points
  of `Q` (`AlgEquiv.restrictNormalHom_apply`), hence — `j` being
  equivariant and injective — identically on `Y`. The descended
  `ρ : Gal(L/Kᵥ) →* AddMonoid.End Y` is built from the canonical lift
  `AlgEquiv.liftNormal`, whose `restrictNormalHom` is the identity
  (`AlgEquiv.restrict_liftNormal`), so `map_one`/`map_mul` are
  instances of that same "agree on `L` ⇒ agree on `Y`" lemma.
* `exists_finiteQuotient_galoisModule_etale_package` (`Small.{0} Kᵥ`
  holds, `Ωᵥ` is a separable closure in characteristic zero) then
  produces exactly `H`, `Module.Finite`, `Algebra.Etale` and an
  equivariant additive bijection of its points with `Y`; the
  `WithConv` wrapper of that statement is the same monoid as the
  vendored bare-hom one by `vendored_mul_eq_convMul` /
  `vendored_one_eq_convOne`, which is how the `≃+` it returns becomes
  the bare-hom `AddMonoidHom` demanded here.
Unconditionally TRUE; no hypothesis package. -/
theorem exists_etaleHopfAlgebra_of_points_embedding
    (Q : Type) [CommRing Q] [HopfAlgebra Kᵥ Q] [Module.Finite Kᵥ Q]
    [Algebra.Etale Kᵥ Q]
    {Y : Type*} [AddCommGroup Y] [DistribMulAction Γᵥ Y]
    (j : Y →+ Additive (Q →ₐ[Kᵥ] Ωᵥ)) (hj : Function.Injective j)
    (hje : ∀ (g : Γᵥ) (y : Y), j (g • y) = g • j y) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra Kᵥ H) (_ : Module.Finite Kᵥ H)
      (_ : Algebra.Etale Kᵥ H) (e : Additive (H →ₐ[Kᵥ] Ωᵥ) →+ Y),
      Function.Bijective e ∧
        ∀ (g : Γᵥ) (y : Additive (H →ₐ[Kᵥ] Ωᵥ)), e (g • y) = g • e y := by
  classical
  haveI : Finite Y := Finite.of_injective j hj
  -- a finite `Kᵥ`-basis of `Q`, and the finite set of all the values taken by
  -- all the (finitely many) points of `Q` on that basis
  set n := Module.finrank Kᵥ Q
  set b := Module.finBasis Kᵥ Q
  set T : Set Ωᵥ := Set.range (fun p : (Q →ₐ[Kᵥ] Ωᵥ) × Fin n => p.1 (b p.2))
  haveI : Finite T := Set.Finite.to_subtype (Set.finite_range _)
  -- the finite subextension over which every point of `Q` is defined, and its
  -- normal (hence Galois, characteristic zero) closure
  set L₀ : IntermediateField Kᵥ Ωᵥ := IntermediateField.adjoin Kᵥ T
  haveI : FiniteDimensional Kᵥ L₀ :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsIntegral.isIntegral (R := Kᵥ) x))
  set L : IntermediateField Kᵥ Ωᵥ := IntermediateField.normalClosure Kᵥ L₀ Ωᵥ
  -- every point of `Q` takes values in `L`
  have hbT : ∀ (φ : Q →ₐ[Kᵥ] Ωᵥ) (i : Fin n), φ (b i) ∈ L₀ :=
    fun φ i => IntermediateField.subset_adjoin Kᵥ T ⟨(φ, i), rfl⟩
  have hL₀L : L₀ ≤ L := IntermediateField.le_normalClosure L₀
  have hval : ∀ (φ : Q →ₐ[Kᵥ] Ωᵥ) (x : Q), φ x ∈ L := by
    intro φ x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem (fun i _ => ?_)
    rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    exact mul_mem (L.algebraMap_mem _) (hL₀L (hbT φ i))
  -- two absolute automorphisms agreeing on `L` act the same on the points of `Q`
  have hagreepts : ∀ (σ τ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ),
      AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L σ =
        AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L τ →
      ∀ φ : Q →ₐ[Kᵥ] Ωᵥ, σ.toAlgHom.comp φ = τ.toAlgHom.comp φ := by
    intro σ τ h φ
    refine AlgHom.ext fun x => ?_
    have h1 := AlgEquiv.restrictNormalHom_apply (F := Kᵥ) (K₁ := Ωᵥ) L σ ⟨φ x, hval φ x⟩
    have h2 := AlgEquiv.restrictNormalHom_apply (F := Kᵥ) (K₁ := Ωᵥ) L τ ⟨φ x, hval φ x⟩
    show σ (φ x) = τ (φ x)
    rw [← h1, ← h2, h]
  -- hence the same on `Y`, by injectivity of the embedding
  have hagree : ∀ (σ τ : Γᵥ),
      AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L σ =
        AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L τ →
      ∀ z : Y, σ • z = τ • z := by
    intro σ τ h z
    apply hj
    rw [hje, hje]
    exact congrArg Additive.ofMul (hagreepts σ τ h (Additive.toMul (j z)))
  -- the canonical lift of an automorphism of `L` to `Kᵥᵃˡᵍ`
  set lft : (L ≃ₐ[Kᵥ] L) → Γᵥ := fun s => (AlgEquiv.liftNormal s Ωᵥ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ)
  have hlftr : ∀ s : L ≃ₐ[Kᵥ] L,
      AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L (lft s) = s :=
    fun s => AlgEquiv.restrict_liftNormal (E := Ωᵥ) s
  -- the descended action of the finite Galois quotient `Gal(L/Kᵥ)` on `Y`
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (L ≃ₐ[Kᵥ] L) →* AddMonoid.End Y, ∀ s z, ρ s z = lft s • z := by
    refine ⟨{ toFun := fun s => DistribMulAction.toAddMonoidEnd Γᵥ Y (lft s)
              map_one' := ?_, map_mul' := ?_ }, fun _ _ => rfl⟩
    · refine DFunLike.ext _ _ fun z => ?_
      have h1 : AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L (lft 1) =
          AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L (1 : Γᵥ) := by
        rw [hlftr, map_one]
      show lft 1 • z = z
      rw [hagree _ _ h1, one_smul]
    · intro s t
      rw [← map_mul]
      refine DFunLike.ext _ _ fun z => ?_
      have h1 : AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L (lft (s * t)) =
          AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L (lft s * lft t) := by
        rw [hlftr, map_mul, hlftr, hlftr]
      exact hagree _ _ h1 z
  -- Grothendieck's construction: `Y` is the point group of a finite étale Hopf algebra
  obtain ⟨HK, iCR, iHopf, iFin, iEt, f, hf⟩ :
      ∃ (HK : Type) (_ : CommRing HK) (_ : HopfAlgebra Kᵥ HK)
        (_ : Module.Finite Kᵥ HK) (_ : Algebra.Etale Kᵥ HK)
        (f : Additive (WithConv (HK →ₐ[Kᵥ] Ωᵥ)) ≃+ Y),
        ∀ (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) (φ : HK →ₐ[Kᵥ] Ωᵥ),
          f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
            ρ (AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L σ)
              (f (Additive.ofMul (WithConv.toConv φ))) :=
    exists_finiteQuotient_galoisModule_etale_package Kᵥ Ωᵥ Y L ρ
  letI := iCR
  letI := iHopf
  letI := iFin
  letI := iEt
  -- transport across the vendored/`WithConv` convolution bridge
  obtain ⟨e, he⟩ : ∃ e : Additive (HK →ₐ[Kᵥ] Ωᵥ) →+ Y,
      ∀ y, e y = f (Additive.ofMul (WithConv.toConv (Additive.toMul y))) := by
    refine ⟨{ toFun := fun y => f (Additive.ofMul (WithConv.toConv (Additive.toMul y)))
              map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩
    · show f (Additive.ofMul (1 : WithConv (HK →ₐ[Kᵥ] Ωᵥ))) = 0
      rw [ofMul_one, map_zero]
    · intro y₁ y₂
      show f (Additive.ofMul (WithConv.toConv
        (Additive.toMul y₁ * Additive.toMul y₂))) = _
      rw [vendored_mul_eq_convMul, WithConv.toConv_ofConv, ofMul_mul, map_add]
  refine ⟨HK, iCR, iHopf, iFin, iEt, e, ?_, ?_⟩
  · have hfe : ⇑e = fun y : Additive (HK →ₐ[Kᵥ] Ωᵥ) =>
        f (Additive.ofMul (WithConv.toConv (Additive.toMul y))) := funext he
    rw [hfe]
    exact f.bijective.comp (Additive.ofMul.bijective.comp
      (WithConv.toConv_bijective.comp Additive.toMul.bijective))
  · intro g y
    have h1 := hf (g : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) (Additive.toMul y)
    have h2 : AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L
        (lft (AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L g)) =
        AlgEquiv.restrictNormalHom (F := Kᵥ) (K₁ := Ωᵥ) L g := hlftr _
    rw [he, he]
    show f (Additive.ofMul (WithConv.toConv
      ((g : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ).toAlgHom.comp (Additive.toMul y)))) = _
    rw [h1, hρ]
    exact hagree _ _ h2 _

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Étale–Galois, full-faithfulness half** (PROVEN 2026-07-25 — step
(β2) of the subobject closure, added 2026-07-25 by the decomposition of
`IsFlatPointsGroupAt.of_injective`): an INJECTIVE, `Γ Kᵥ`-equivariant
homomorphism `t` of convolution point groups from a finite étale
`Kᵥ`-Hopf algebra `H` into the points of a finite étale `Kᵥ`-Hopf
algebra `Q` is induced by a SURJECTIVE `Kᵥ`-bialgebra homomorphism
`π : Q → H` (restriction of functions along an inclusion of point
groups). Intended proof, entirely inside the PROVEN machinery of
`KnownIn1980s/EllipticCurves/Flat.lean`:
* the ALGEBRA map: `exists_algHom_of_algHom_map` applied with the
  étale algebra `H` and the plain `Kᵥ`-algebra `Q` and the
  equivariant `t` gives `π : Q →ₐ[Kᵥ] H` with `φ (π q) = t φ q` for
  every point `φ` of `H`, i.e. `φ.comp π = t φ`.
* SURJECTIVITY: the range of `π` is a `Kᵥ`-subalgebra of `H`
  separating the points of `H` — two points agreeing on the range
  have `t φ = t ψ`, hence `φ = ψ` by injectivity of `t` — so it is
  `⊤` by `subalgebra_eq_top_of_algHom_separating`.
* the BIALGEBRA upgrade: points separate the finite étale `H ⊗[Kᵥ] H`
  (`eq_zero_of_forall_algHom_eq_zero`, base change plus
  `Algebra.Etale.comp`), and every point of `H ⊗[Kᵥ] H` is the
  `Algebra.TensorProduct.lift` of its two restrictions (the target
  `Kᵥᵃˡᵍ` is commutative); testing `comul ∘ π` against
  `(π ⊗ π) ∘ comul` at such a point is, after unfolding
  `AlgHom.convMul_apply`, exactly `htmul`, and testing the counits is
  `htone` — the same argument as the PROVEN
  `exists_bialgEquiv_of_algEquiv_conv`, whose `AlgEquiv` hypothesis is
  never used for these two checks. (CONFIRMED 2026-07-25 while proving
  this: that lemma's comultiplication and counit tests go through
  verbatim for a bare `AlgHom`; the equivalence is used there only to
  transport `hmul` into the `hmul'` shape, which here is supplied
  directly by `htmul` through `φ.comp π = t φ`.) The antipode needs no
  check (`→ₐc` preserves it automatically,
  `antipodeAlgHom_comp_bialgHom`).
The bridge between the bare-hom convolution monoid on
`H →ₐ[Kᵥ] Ωᵥ` (in which `htone`/`htmul` are stated) and mathlib's
`WithConv` monoid (in which `AlgHom.convMul_apply` computes) is
`vendored_one_eq_convOne` / `vendored_mul_eq_convMul`, both `rfl`.
`Ωᵥ` is a separable closure of the characteristic-zero field `Kᵥ`
(`IsSepClosure Kᵥ Ωᵥ` from `IsAlgClosed` plus `Algebra.IsSeparable`),
which is what lets the three `Flat.lean` ingredients apply.
Unconditionally TRUE; no hypothesis package. -/
theorem exists_surjective_bialgHom_of_points_injection
    (Q : Type) [CommRing Q] [HopfAlgebra Kᵥ Q] [Module.Finite Kᵥ Q]
    [Algebra.Etale Kᵥ Q]
    (H : Type) [CommRing H] [HopfAlgebra Kᵥ H] [Module.Finite Kᵥ H]
    [Algebra.Etale Kᵥ H]
    (t : (H →ₐ[Kᵥ] Ωᵥ) → (Q →ₐ[Kᵥ] Ωᵥ))
    (htinj : Function.Injective t)
    (htone : t 1 = 1)
    (htmul : ∀ φ ψ : H →ₐ[Kᵥ] Ωᵥ, t (φ * ψ) = t φ * t ψ)
    (hteq : ∀ (g : Γᵥ) (φ : H →ₐ[Kᵥ] Ωᵥ), t (g • φ) = g • t φ) :
    ∃ π : Q →ₐc[Kᵥ] H, Function.Surjective (π : Q →ₐ[Kᵥ] H) ∧
      ∀ φ : H →ₐ[Kᵥ] Ωᵥ, φ.comp (π : Q →ₐ[Kᵥ] H) = t φ := by
  classical
  -- in characteristic zero the algebraic closure is a separable closure
  haveI hsepcl : IsSepClosure Kᵥ Ωᵥ := ⟨inferInstance, inferInstance⟩
  -- (1) the underlying ALGEBRA map, from Grothendieck full faithfulness:
  -- the equivariance clause in composition form
  have hteq' : ∀ (σ : Ωᵥ ≃ₐ[Kᵥ] Ωᵥ) (φ : H →ₐ[Kᵥ] Ωᵥ),
      t (σ.toAlgHom.comp φ) = σ.toAlgHom.comp (t φ) := by
    intro σ φ
    have h1 : σ.toAlgHom.comp φ = σ • φ := AlgHom.ext fun _ => rfl
    have h2 : σ.toAlgHom.comp (t φ) = σ • t φ := AlgHom.ext fun _ => rfl
    rw [h1, h2]
    exact hteq σ φ
  obtain ⟨π₀, hπ₀⟩ := exists_algHom_of_algHom_map Kᵥ Ωᵥ H Q t hteq'
  have hcomp : ∀ φ : H →ₐ[Kᵥ] Ωᵥ, φ.comp π₀ = t φ :=
    fun φ => AlgHom.ext fun q => hπ₀ φ q
  -- (2) SURJECTIVITY: the range of `π₀` separates the points of `H`,
  -- because two points agreeing on it have the same image under `t`
  have hrange : π₀.range = ⊤ := by
    refine subalgebra_eq_top_of_algHom_separating Kᵥ Ωᵥ H π₀.range ?_
    intro φ ψ hsepφψ
    refine htinj ?_
    rw [← hcomp φ, ← hcomp ψ]
    exact AlgHom.ext fun q => hsepφψ (π₀ q) ⟨q, rfl⟩
  have hsurj : Function.Surjective π₀ := by
    intro x
    have hx : x ∈ π₀.range := by rw [hrange]; trivial
    exact hx
  -- (3) the BIALGEBRA upgrade, counit half: `t 1 = 1` says
  -- `algebraMap ∘ counit_H ∘ π₀ = algebraMap ∘ counit_Q`
  have hcounit : (Bialgebra.counitAlgHom Kᵥ H).comp π₀ =
      Bialgebra.counitAlgHom Kᵥ Q := by
    refine AlgHom.ext fun q => ?_
    have h1 : (1 : H →ₐ[Kᵥ] Ωᵥ).comp π₀ = (1 : Q →ₐ[Kᵥ] Ωᵥ) := by
      rw [hcomp 1, htone]
    have h2 := AlgHom.congr_fun h1 q
    have h3 : (1 : H →ₐ[Kᵥ] Ωᵥ) (π₀ q) =
        algebraMap Kᵥ Ωᵥ (Coalgebra.counit (π₀ q)) := rfl
    have h4 : (1 : Q →ₐ[Kᵥ] Ωᵥ) q = algebraMap Kᵥ Ωᵥ (Coalgebra.counit q) := rfl
    rw [AlgHom.comp_apply] at h2
    rw [h3, h4] at h2
    exact (algebraMap Kᵥ Ωᵥ).injective h2
  -- (4) the BIALGEBRA upgrade, comultiplication half: test against every
  -- point of the finite étale `H ⊗[Kᵥ] H`
  haveI hEt2 : Algebra.Etale Kᵥ (H ⊗[Kᵥ] H) :=
    Algebra.Etale.comp Kᵥ H (H ⊗[Kᵥ] H)
  have hmul' : ∀ φ ψ : H →ₐ[Kᵥ] Ωᵥ,
      (WithConv.toConv (φ.comp π₀) * WithConv.toConv (ψ.comp π₀)).ofConv =
        ((WithConv.toConv φ * WithConv.toConv ψ).ofConv).comp π₀ := by
    intro φ ψ
    rw [← vendored_mul_eq_convMul, ← vendored_mul_eq_convMul, hcomp φ, hcomp ψ,
      hcomp (φ * ψ)]
    exact (htmul φ ψ).symm
  have hcomul : (Algebra.TensorProduct.map π₀ π₀).comp
      (Bialgebra.comulAlgHom Kᵥ Q) =
      (Bialgebra.comulAlgHom Kᵥ H).comp π₀ := by
    refine AlgHom.ext fun a => ?_
    have hsep2 := eq_zero_of_forall_algHom_eq_zero Kᵥ Ωᵥ (H ⊗[Kᵥ] H)
      ((Algebra.TensorProduct.map π₀ π₀).comp (Bialgebra.comulAlgHom Kᵥ Q) a -
        (Bialgebra.comulAlgHom Kᵥ H).comp π₀ a)
    rw [sub_eq_zero] at hsep2
    apply hsep2
    intro χ
    rw [map_sub, sub_eq_zero]
    -- decompose the point `χ` of `H ⊗[Kᵥ] H` into its two restrictions
    set φ := χ.comp Algebra.TensorProduct.includeLeft with hφ
    set ψ := χ.comp (Algebra.TensorProduct.includeRight :
      H →ₐ[Kᵥ] H ⊗[Kᵥ] H) with hψ
    have hχ : χ = Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _ := by
      apply Algebra.TensorProduct.ext
      · apply AlgHom.ext
        intro b
        simp [hφ]
      · apply AlgHom.ext
        intro b
        simp [hψ]
    -- the left side is the convolution of the transported points
    have hleft : χ ((Algebra.TensorProduct.map π₀ π₀).comp
        (Bialgebra.comulAlgHom Kᵥ Q) a) =
        ((WithConv.toConv (φ.comp π₀) * WithConv.toConv (ψ.comp π₀)).ofConv) a := by
      rw [hχ]
      have hlift : (Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _).comp
          (Algebra.TensorProduct.map π₀ π₀) =
          Algebra.TensorProduct.lift (φ.comp π₀) (ψ.comp π₀)
            (fun _ _ => Commute.all _ _) := by
        apply Algebra.TensorProduct.ext
        · apply AlgHom.ext
          intro b
          simp
        · apply AlgHom.ext
          intro b
          simp
      rw [AlgHom.comp_apply, ← AlgHom.comp_apply (Algebra.TensorProduct.lift φ ψ _),
        hlift]
      rw [AlgHom.convMul_apply]
      rfl
    -- the right side is the convolution of the original points, at `π₀ a`
    have hright : χ ((Bialgebra.comulAlgHom Kᵥ H).comp π₀ a) =
        (((WithConv.toConv φ * WithConv.toConv ψ).ofConv).comp π₀) a := by
      rw [hχ, AlgHom.comp_apply]
      rw [show (Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _)
          ((Bialgebra.comulAlgHom Kᵥ H) (π₀ a)) =
          ((WithConv.toConv φ * WithConv.toConv ψ).ofConv) (π₀ a) from
        (AlgHom.convMul_apply _ _ _).symm]
      rfl
    rw [hleft, hright, hmul' φ ψ]
  exact ⟨BialgHom.ofAlgHom π₀ hcounit hcomul, hsurj, hcomp⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Subobject closure** (DECOMPOSED 2026-07-25 — the subobjects half
of Raynaud closure: a Galois-stable subgroup of the generic-fibre
points of a finite flat group scheme over the DVR `𝒪ᵥ` is the
generic-fibre point group of a finite flat group scheme, by schematic
closure): a `Γ Kᵥ`-equivariantly embedded subgroup of a flat
point-group at `v` is a flat point-group at `v`. The assembly below is
PROVEN over the four steps of the classical argument; of the two
étale–Galois leaves the existence half is now PROVEN too, so only the
full-faithfulness half remains sorried:
* (α) *transport*: the witness `f` of `hX` identifies `X`
  equivariantly with the `Kᵥᵃˡᵍ`-points of the generic fibre
  `Q := Kᵥ ⊗[𝒪ᵥ] G`, so `j` becomes an equivariant injection
  `j' : Y ↪ points(Q)` (PROVEN here);
* (β) *étale–Galois*: `Y` is the point group of a finite étale
  `Kᵥ`-Hopf algebra `H` (`exists_etaleHopfAlgebra_of_points_embedding`,
  PROVEN), and the induced inclusion of point groups comes from a
  SURJECTIVE bialgebra homomorphism `π : Q → H`
  (`exists_surjective_bialgHom_of_points_injection`, PROVEN 2026-07-25)
  — the two halves of Grothendieck's anti-equivalence. The convolution
  homomorphism property of the induced `t` is PROVEN here from
  additivity of `j'` and `e`;
* (γ) *schematic closure over the DVR*: the canonical Hopf order
  `1 ⊗ G ⊆ Q` (`exists_hopfOrder_baseChange`) pushes forward along the
  surjection `π` to a Hopf order in `H`
  (`exists_hopfOrder_map_of_surjective_bialgHom`) — PROVEN. EXISTENCE
  of this closure needs no `e < p − 1` bound; Raynaud's bound enters
  only for uniqueness/full-faithfulness statements;
* (δ) *conclusion*: a Hopf order in a finite étale `Kᵥ`-Hopf algebra
  whose points are `Y` is a flat point-group package
  (`isFlatPointsGroupAt_of_hopfOrder`, PROVEN, over the vendored
  `exists_flat_hopf_form_of_hopf_order`).
Unconditionally TRUE; no hypothesis package (for `Y` a subsingleton
this is already `IsFlatPointsGroupAt.of_subsingleton`). -/
theorem IsFlatPointsGroupAt.of_injective {X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y]
    [DistribMulAction Γᵥ X] [DistribMulAction Γᵥ Y]
    (hX : IsFlatPointsGroupAt v X) (j : Y →+ X)
    (hj : Function.Injective j)
    (hje : ∀ (g : Γᵥ) (y : Y), j (g • y) = g • j y) :
    IsFlatPointsGroupAt v Y := by
  classical
  obtain ⟨G, iCR, iHopf, iFlat, iFin, iEt, f, hfbij, hfeq⟩ := hX
  letI := iCR; letI := iHopf; letI := iFlat; letI := iFin; letI := iEt
  -- (α) the equivariant identification of `X` with the points of the generic fibre
  set fe : Additive ((Kᵥ ⊗[𝒪ᵥ] G) →ₐ[Kᵥ] Ωᵥ) ≃+ X :=
    AddEquiv.ofBijective f hfbij with hfedef
  have hfesymm : ∀ (g : Γᵥ) (x : X), fe.symm (g • x) = g • fe.symm x := by
    intro g x
    apply fe.injective
    rw [fe.apply_symm_apply]
    show g • x = f (g • fe.symm x)
    rw [hfeq]
    show g • x = g • fe (fe.symm x)
    rw [fe.apply_symm_apply]
  set j' : Y →+ Additive ((Kᵥ ⊗[𝒪ᵥ] G) →ₐ[Kᵥ] Ωᵥ) :=
    fe.symm.toAddMonoidHom.comp j with hj'def
  have hj'inj : Function.Injective j' := fe.symm.injective.comp hj
  have hj'eq : ∀ (g : Γᵥ) (y : Y), j' (g • y) = g • j' y := by
    intro g y
    show fe.symm (j (g • y)) = g • fe.symm (j y)
    rw [hje, hfesymm]
  -- (β) the étale–Galois package of the subgroup, and the induced surjection
  obtain ⟨H, hCR, hHopf, hFin, hEt, e, hebij, heeq⟩ :=
    exists_etaleHopfAlgebra_of_points_embedding (Kᵥ ⊗[𝒪ᵥ] G) j' hj'inj hj'eq
  letI := hCR; letI := hHopf; letI := hFin; letI := hEt
  set t : (H →ₐ[Kᵥ] Ωᵥ) → ((Kᵥ ⊗[𝒪ᵥ] G) →ₐ[Kᵥ] Ωᵥ) :=
    fun φ => Additive.toMul (j' (e (Additive.ofMul φ))) with htdef
  have htinj : Function.Injective t := fun φ ψ hφψ => by
    have h1 : j' (e (Additive.ofMul φ)) = j' (e (Additive.ofMul ψ)) :=
      Additive.toMul.injective hφψ
    exact Additive.ofMul.injective (hebij.1 (hj'inj h1))
  have htone : t 1 = 1 := by
    show Additive.toMul (j' (e (Additive.ofMul (1 : H →ₐ[Kᵥ] Ωᵥ)))) = 1
    have h0 : Additive.ofMul (1 : H →ₐ[Kᵥ] Ωᵥ) = 0 := rfl
    rw [h0, map_zero, map_zero]
    rfl
  have htmul : ∀ φ ψ : H →ₐ[Kᵥ] Ωᵥ, t (φ * ψ) = t φ * t ψ := by
    intro φ ψ
    show Additive.toMul (j' (e (Additive.ofMul (φ * ψ)))) = _
    have h1 : Additive.ofMul (φ * ψ) =
        Additive.ofMul φ + Additive.ofMul ψ := rfl
    rw [h1, map_add, map_add]
    rfl
  have hteq : ∀ (g : Γᵥ) (φ : H →ₐ[Kᵥ] Ωᵥ), t (g • φ) = g • t φ := by
    intro g φ
    show Additive.toMul (j' (e (Additive.ofMul (g • φ)))) = _
    have h1 : Additive.ofMul (g • φ) =
        g • (Additive.ofMul φ : Additive (H →ₐ[Kᵥ] Ωᵥ)) := rfl
    rw [h1, heeq, hj'eq]
    rfl
  obtain ⟨π, hπsurj, -⟩ :=
    exists_surjective_bialgHom_of_points_injection (Kᵥ ⊗[𝒪ᵥ] G) H t htinj htone
      htmul hteq
  -- (γ) schematic closure: push the canonical Hopf order forward along `π`
  obtain ⟨G₀, hfg, hspan, hcounit, hantipode, hcomul⟩ :=
    exists_hopfOrder_baseChange 𝒪ᵥ Kᵥ G
  obtain ⟨H₀, hfg', hspan', hcounit', hantipode', hcomul'⟩ :=
    exists_hopfOrder_map_of_surjective_bialgHom (Kᵥ ⊗[𝒪ᵥ] G) H π hπsurj G₀
      hfg hspan hcounit hantipode hcomul
  -- (δ) conclude
  exact isFlatPointsGroupAt_of_hopfOrder H H₀ hfg' hspan' hcounit' hantipode'
    hcomul' e hebij heeq

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

end RaynaudQuotient

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud quotient closure, in prolongation form** (PROVEN): a
`G_ℚ`-equivariant QUOTIENT of a Galois representation which has a flat
prolongation at `v` again has a flat prolongation at `v`.

Scheme-theoretically this is the closure of finite flat group schemes over
the DVR `𝒪ᵥ` under quotients by flat closed subgroup schemes (Raynaud,
*Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102 (1974), §1–3;
Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens ch. V),
read on `ℚ̄ᵥ`-points — the form the project's prolongation package takes.

The equivariance hypothesis is stated for the GLOBAL action, as in
`GaloisRep.HasFlatProlongationAt.of_addEquiv`; it implies the local one
because `toLocal` is precomposition with `G_ℚᵥ → G_ℚ` — which is why the
`show` below can discharge it by `he` alone.

Proof: repackage both sides through
`RaynaudQuotient.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt`
and apply the carrier-level quotient closure
`RaynaudQuotient.IsFlatPointsGroupAt.of_surjective`, whose two halves are
the étale–Galois brick
`RaynaudQuotient.exists_etale_subBialgebra_of_points_surjective` and the
schematic-closure brick
`RaynaudQuotient.exists_hopfOrder_of_subBialgebra` above.

Unconditionally TRUE — permanent library material carrying no hypothesis
package (for `e` bijective this is already
`GaloisRep.HasFlatProlongationAt.of_addEquiv`, and for a subsingleton
target `GaloisRep.hasFlatProlongationAt_of_subsingleton`). -/
theorem GaloisRep.HasFlatProlongationAt.of_surjective
    {v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    {A₁ : Type*} [CommRing A₁] [TopologicalSpace A₁]
    {M₁ : Type*} [AddCommGroup M₁] [Module A₁ M₁]
    {A₂ : Type*} [CommRing A₂] [TopologicalSpace A₂]
    {M₂ : Type*} [AddCommGroup M₂] [Module A₂ M₂]
    {ρ₁ : GaloisRep ℚ A₁ M₁} {ρ₂ : GaloisRep ℚ A₂ M₂}
    (h : ρ₁.HasFlatProlongationAt v)
    (e : M₁ →+ M₂) (hsurj : Function.Surjective e)
    (he : ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : M₁), e (ρ₁ σ x) = ρ₂ σ (e x)) :
    ρ₂.HasFlatProlongationAt v := by
  refine (RaynaudQuotient.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt
    (v := v) ρ₂).mpr ?_
  refine RaynaudQuotient.IsFlatPointsGroupAt.of_surjective
    ((RaynaudQuotient.GaloisRep.hasFlatProlongationAt_iff_isFlatPointsGroupAt
      (v := v) ρ₁).mp h) e hsurj ?_
  intro g x
  show e ((ρ₁.toLocal v) g x) = (ρ₂.toLocal v) g (e x)
  exact he _ _

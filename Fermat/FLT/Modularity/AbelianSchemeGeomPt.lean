/-
Modularity/AbelianSchemeGeomPt.lean — own work for the Fermat project (not
vendored from the FLT project).
-/
module

-- `AbelianSchemeStruct`, `GeomFibrePt`, `galSMul`, `specGal`, `specAlgClos`.
public import Fermat.FLT.Modularity.AbelianScheme
-- `Scheme.residueField`, `Scheme.descResidueField`, `Scheme.stalkClosedPointTo`,
-- `Scheme.SpecToEquivOfField`, `Scheme.residueFieldCongr`,
-- `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`.
public import Mathlib.AlgebraicGeometry.ResidueField
-- `LocallyOfFiniteType.stalkMap` — the one geometric input, supplied by
-- `ab.proper`.
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
-- `RingHom.EssFiniteType.ext` and `RingHom.EssFiniteType.finset`.
public import Mathlib.RingTheory.EssentialFiniteness
-- `AlgebraicClosure`, and `Algebra.IsIntegral` for it.
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- `IntermediateField.adjoin`, `IntermediateField.finiteDimensional_adjoin`,
-- `IntermediateField.subset_adjoin`.
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
-- `mem_fixingSubgroup_iff`.
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
-- `attribute [reducible] Field.absoluteGaloisGroup`.  NOT optional and NOT
-- cosmetic: without it, instance and coercion search do not unfold
-- `Field.absoluteGaloisGroup F` to `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`
-- (unification does, which is why the STATEMENT elaborates), and the proof
-- below fails with `Function expected at σ` and
-- `failed to synthesize MulAction (Field.absoluteGaloisGroup F) …`.  This
-- module was already in the cone of both `TateModule.lean` (through
-- `Deformations/RepresentationTheory/GaloisRep.lean`) and
-- `Fermat/FLT/ModularCurve/X0.lean`, so the import adds nothing to either.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# A geometric point of an abelian scheme is defined over a finite extension

One theorem, `exists_fixingSubgroup_le_stabilizer_geomFibrePt`, hoisted out of
`Fermat/FLT/Modularity/TateModule.lean` on 2026-07-28.

**WHY THIS MODULE EXISTS: it is an IMPORT-CONE cut, not a mathematical one.**
The statement is about an arbitrary morphism `Spec F̄ ⟶ A` over a base point,
and `ab` enters only through `ab.proper`; nothing about Tate modules, level
structures, adic completions or compatible systems is involved.  It was written
in `TateModule.lean` because that is where its first consumer lived.

Its second consumer is the weak Mordell–Weil chain of
`Fermat/FLT/ModularCurve/X0.lean`, which needs it to see that the `p`-torsion
field `ℚ(A[p])` is finite over `ℚ`.  `X0.lean` cannot import `TateModule.lean`
cheaply: that module's cone carries `GaloisRepresentation/Chebotarev.lean`
(13 500 lines) and `TateModule.lean` itself (16 000 lines), and putting either
UPSTREAM of `X0.lean` — which is upstream of `MazurTorsion`, `ModThree` and the
whole Frey-curve tower — lengthens the build's critical path by both of them.
This module's project cone is `Modularity/AbelianScheme.lean` and nothing else,
already inside `X0.lean`'s cone, so the import costs one small module.

`TateModule.lean` `public import`s this file, so its own downstream consumers
(`exists_isOpen_stabilizer_geomFibrePt` and the rest) see the same name in the
same namespace, unqualified and unchanged.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Fermat

/-- **A geometric point of the fibre is defined over a finite extension
of `F`** (PROVEN 2026-07-26 — scheme theory; EGA IV 8.8, Stacks
01ZC/01ZM).

For every `y : Spec F̄ ⟶ A` lying over `Spec F̄ ⟶ Spec F --x--> S` there
is a finite subextension `E/F` inside `F̄` such that every `σ ∈ Γ_F`
fixing `E` pointwise fixes `y`.

HOW IT IS PROVEN, in the residue-field form, which avoids both affine
opens and the limit formalism. A morphism `Spec K ⟶ X` out of the
spectrum of a field is the same thing as a point `p` of `X` together
with a field map `ψ : κ(p) ⟶ K` (`Scheme.SpecToEquivOfField`,
`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`), and
under that description precomposition with `Spec σ` is postcomposition
of `ψ` with `σ`. So the goal becomes `σ ∘ ψ = ψ`.

Since `A.residue p : 𝒪_{A,p} ↠ κ(p)` is an epimorphism it is enough to
prove `σ ∘ Ψ = Ψ` for `Ψ := A.residue p ≫ ψ`, and now
`LocallyOfFiniteType.stalkMap` — this is the ONLY geometric input, and
it comes from `ab.proper`, which extends `LocallyOfFiniteType` — says
that `f.stalkMap p : 𝒪_{S,f p} ⟶ 𝒪_{A,p}` is ESSENTIALLY OF FINITE
TYPE. Two ring maps out of an essentially-of-finite-type extension that
agree on the base and on the finitely many essential generators are
equal (`RingHom.EssFiniteType.ext`). Taking
`E := F(Ψ g₁, …, Ψ gₙ)` for `gᵢ` those generators, each `Ψ gᵢ` is
algebraic over `F` because `F̄/F` is, so `E/F` is finite; and any `σ`
fixing `E` fixes the generators by construction and fixes the base
because the composite `𝒪_{S,f p} ⟶ 𝒪_{A,p} ⟶ F̄` factors through `F` —
that last point is exactly the hypothesis `y.2`, read through the same
residue-field description of `Spec F̄ ⟶ Spec F --x--> S`.

The group structure plays NO role: this is a statement about an
arbitrary morphism `Spec F̄ ⟶ A` over `x`, and `ab` enters only through
`ab.proper`. It is deliberately stated for a single point, because that
is the form in which spreading out is true — the uniform version over an
infinite set of points is FALSE, and it is finiteness of `A[J]`
(`finite_torsion_of_ne_bot`) that repairs it. -/
theorem exists_fixingSubgroup_le_stabilizer_geomFibrePt
    {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (y : GeomFibrePt f x) :
    ∃ (E : IntermediateField F (AlgebraicClosure F)) (_ : FiniteDimensional F E),
      ∀ σ : Field.absoluteGaloisGroup F,
        σ ∈ E.fixingSubgroup → ab.galSMul x σ y = y := by
  classical
  haveI : IsProper f := ab.proper
  -- The point of `A` underlying the geometric point, and the induced map on residue fields.
  set p : A := y.1 (IsLocalRing.closedPoint (AlgebraicClosure F))
  set ψ : A.residueField p ⟶ CommRingCat.of (AlgebraicClosure F) :=
    Scheme.descResidueField (Scheme.stalkClosedPointTo y.1)
  have hy1 : Spec.map ψ ≫ A.fromSpecResidueField p = y.1 :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ A y.1
  -- The same data for the base point `x`, whose residue field lands in `F` itself.
  set q : S := x (IsLocalRing.closedPoint F)
  set χ : S.residueField q ⟶ CommRingCat.of F :=
    Scheme.descResidueField (Scheme.stalkClosedPointTo x)
  have hx1 : Spec.map χ ≫ S.fromSpecResidueField q = x :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ S x
  set ι : CommRingCat.of F ⟶ CommRingCat.of (AlgebraicClosure F) :=
    CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) with hιdef
  -- `θ` is the residue-field datum of the composite `Spec F̄ ⟶ A ⟶ S`.
  set θ : S.residueField (f p) ⟶ CommRingCat.of (AlgebraicClosure F) :=
    f.residueFieldMap p ≫ ψ with hθdef
  have hkey : Spec.map θ ≫ S.fromSpecResidueField (f p)
      = Spec.map (χ ≫ ι) ≫ S.fromSpecResidueField q := by
    have h1 : Spec.map θ ≫ S.fromSpecResidueField (f p) = y.1 ≫ f := by
      rw [hθdef, Spec.map_comp, Category.assoc,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, hy1]
    have h2 : Spec.map (χ ≫ ι) ≫ S.fromSpecResidueField q = specAlgClos F ≫ x := by
      rw [Spec.map_comp, Category.assoc, hx1, specAlgClos, hιdef]
    rw [h1, h2, y.2]
  -- Hence `θ` factors through `F`.
  have hsig : (⟨f p, θ⟩ : Σ z : S, S.residueField z ⟶ CommRingCat.of (AlgebraicClosure F))
      = ⟨q, χ ≫ ι⟩ :=
    (Scheme.SpecToEquivOfField (AlgebraicClosure F) S).symm.injective hkey
  obtain ⟨e, hθ⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hsig
  replace hθ : θ = (S.residueFieldCongr e).hom ≫ (χ ≫ ι) := hθ
  have hθrange : ∀ z, ∃ w : F, θ.hom z = algebraMap F (AlgebraicClosure F) w := by
    intro z
    refine ⟨χ.hom ((S.residueFieldCongr e).hom.hom z), ?_⟩
    rw [hθ]
    rfl
  -- `f` is locally of finite type, so the stalk map is essentially of finite type.
  have hst : (f.stalkMap p).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f p
  set Ψ : A.presheaf.stalk p ⟶ CommRingCat.of (AlgebraicClosure F) :=
    A.residue p ≫ ψ with hΨdef
  have hcomp : f.stalkMap p ≫ Ψ = S.residue (f p) ≫ θ := by
    rw [hΨdef, hθdef, ← Category.assoc, ← Scheme.residue_residueFieldMap, Category.assoc]
  -- The finitely many essential generators, pushed into `F̄`.
  set gens : Finset (AlgebraicClosure F) := hst.finset.image (fun z => Ψ.hom z)
  refine ⟨IntermediateField.adjoin F (gens : Set (AlgebraicClosure F)),
    IntermediateField.finiteDimensional_adjoin
      (fun z _ => Algebra.IsIntegral.isIntegral (R := F) z), ?_⟩
  intro σ hσ
  have hfix : ∀ z ∈ gens, (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) z = z := by
    intro z hz
    exact (mem_fixingSubgroup_iff _).mp hσ z
      (IntermediateField.subset_adjoin F (gens : Set (AlgebraicClosure F)) hz)
  set σr : CommRingCat.of (AlgebraicClosure F) ⟶ CommRingCat.of (AlgebraicClosure F) :=
    CommRingCat.ofHom
      ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom)
  have hΨσ : Ψ ≫ σr = Ψ := by
    refine CommRingCat.hom_ext (RingHom.EssFiniteType.ext hst ?_ ?_)
    · refine RingHom.ext fun z => ?_
      have hz : Ψ.hom ((f.stalkMap p).hom z) = θ.hom ((S.residue (f p)).hom z) :=
        congrArg
          (fun t : S.presheaf.stalk (f p) ⟶ CommRingCat.of (AlgebraicClosure F) => t.hom z) hcomp
      obtain ⟨w, hw⟩ := hθrange ((S.residue (f p)).hom z)
      show (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (Ψ.hom ((f.stalkMap p).hom z))
        = Ψ.hom ((f.stalkMap p).hom z)
      rw [hz, hw]
      exact (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).commutes w
    · intro z hz
      exact hfix _ (Finset.mem_image_of_mem _ hz)
  have hψσ : ψ ≫ σr = ψ := by
    rw [← cancel_epi (A.residue p), ← Category.assoc]
    exact hΨσ
  refine Subtype.ext ?_
  show specGal σ ≫ y.1 = y.1
  calc specGal σ ≫ y.1
      = Spec.map σr ≫ Spec.map ψ ≫ A.fromSpecResidueField p := by rw [hy1]; rfl
    _ = Spec.map (ψ ≫ σr) ≫ A.fromSpecResidueField p := by rw [Spec.map_comp]; simp
    _ = y.1 := by rw [hψσ, hy1]

end Fermat

/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# A concrete cocycles-modulo-coboundaries model for continuous group cohomology

Our mathlib pin computes `continuousCohomology n X` as the homology of the homogeneous
cochain complex `TopRep.homogeneousCochains X`, but offers no way to get *at* a class:
`continuousCohomology n X` is a `TopModuleCat` produced by the categorical homology
functor, and there is no statement identifying it with `Z^n / B^n`. Without such an
identification one cannot construct a cohomology class from an explicit cocycle, which is
what every obstruction-theoretic argument needs.

This file supplies that identification, `ContinuousCohomology.cohomologyIsoQuot`:

  `continuousCohomology j X ≅ TopModuleCat.coker (bdryKer X j)`

where `bdryKer X j` is the `(j-1)`-st differential corestricted to the kernel of the
`j`-th one, so its cokernel is literally "`j`-cocycles modulo `j`-coboundaries", carrying
the quotient topology.

## Provenance and pin-drift audit

Vendored from the reference project `~/cs/FLT`, files
`FLT/Mathlib/Algebra/Category/ModuleCat/Topology/Homology.lean` and
`FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean`
(author Edison Xie), whose mathlib pin `81a5d2` differs from ours `a3364fa`.
Audited against our pin declaration by declaration on 2026-07-27; the outcome was that
**the drift is entirely in our favour**. Specifically:

* `TopModuleCat`, `TopRep`, `TopRep.resolutionX`, `TopRep.homogeneousCochains`,
  `continuousCohomology`, `TopModuleCat.ker`/`coker`/`kerι`/`cokerπ`/`isLimitKer`/
  `isColimitCoker`/`comp_cokerπ`/`cokerπ_surjective`, and the
  `CategoryWithHomology (TopModuleCat R)` instance are all **upstream in our pin already**
  (`Mathlib/Algebra/Category/ModuleCat/Topology/{Basic,Homology}.lean`,
  `Mathlib/RepresentationTheory/{Continuous/TopRep,Homological/ContCohomology/Basic}.lean`).
  In `~/cs/FLT` four of these are still carried as private shims
  (`FLT.Mathlib.Algebra.Category.ModuleCat.Topology.{Basic,Homology}`,
  `FLT.Mathlib.RepresentationTheory.Continuous.{Basic,TopRep}`); vendoring those would have
  duplicated upstream material, so they are **deliberately not vendored**.
* What is genuinely absent from our pin, and is therefore what this file carries, is exactly:
  `TopModuleCat.cokerDesc`, `cokerπ_eq_zero_iff`, `cokerCongr`;
  `HomologicalComplex.cyclesIsoKer`, `homologyIsoCoker`; `CochainComplex.prev_nat`; and
  `ContinuousCohomology.{bdryKer, cohomologyIsoQuot}`.
* The cup-product development (`FLT/Mathlib/.../ContCohomology/CupProduct.lean`, 582 lines)
  and the `linHom`/`iHom`/`cokerDescBilinear` internal-hom machinery it rests on are **not**
  vendored: nothing in this development needs a cup product, and that half of the reference
  file drags in `SemialgHom` (`FLT.Mathlib.Algebra.Algebra.{Hom,Pi}`, 346 lines) for reasons
  unrelated to cohomology. If a cup product is ever needed, that is the place to look, and
  the audit above says the `TopModuleCat` base it needs is already upstream here.
* No lemma required a proof change. The reference file's `resolutionXCast` lemmas use the
  `lia` tactic, which our toolchain (`v4.32.0-rc1` against their `v4.32.0`) may not carry;
  they are not needed for `cohomologyIsoQuot` and are not vendored, so the question does
  not arise.

Material destined for `Mathlib.Algebra.Category.ModuleCat.Topology.Homology` and
`Mathlib.RepresentationTheory.Homological.ContCohomology.Basic`.
-/

@[expose] public section

universe u v w

namespace TopModuleCat

open CategoryTheory Limits

variable {k : Type u} [CommRing k] [TopologicalSpace k]

section Coker

variable {M N N' P : TopModuleCat.{v} k}

/-- The universal property of the concrete quotient `TopModuleCat.coker`: a morphism killing
the range descends to the quotient. -/
noncomputable def cokerDesc (φ : M ⟶ N) (ψ : N ⟶ P) (w : φ ≫ ψ = 0) : coker φ ⟶ P :=
  (isColimitCoker φ).desc (CokernelCofork.ofπ ψ w)

@[reassoc (attr := simp)]
lemma cokerπ_cokerDesc (φ : M ⟶ N) (ψ : N ⟶ P) (w : φ ≫ ψ = 0) :
    cokerπ φ ≫ cokerDesc φ ψ w = ψ :=
  (isColimitCoker φ).fac (CokernelCofork.ofπ ψ w) WalkingParallelPair.one

@[simp]
lemma cokerDesc_apply (φ : M ⟶ N) (ψ : N ⟶ P) (w : φ ≫ ψ = 0) (y : ↥N) :
    cokerDesc φ ψ w (cokerπ φ y) = ψ y :=
  congr($(cokerπ_cokerDesc φ ψ w) y)

/-- A class in the concrete cokernel vanishes exactly when a representative lies in the
range — the handle that turns "the cohomology class is zero" into "the cocycle is a
coboundary". -/
lemma cokerπ_eq_zero_iff (φ : M ⟶ N) (y : ↥N) :
    cokerπ φ y = 0 ↔ y ∈ φ.hom.range :=
  Submodule.Quotient.mk_eq_zero _

/-- Cokernels of morphisms identified under an isomorphism of the targets are isomorphic. -/
noncomputable def cokerCongr {φ : M ⟶ N} {ψ : M ⟶ N'} (e : N ≅ N') (w : φ ≫ e.hom = ψ) :
    coker φ ≅ coker ψ where
  hom := cokerDesc φ (e.hom ≫ cokerπ ψ) (by rw [← Category.assoc, w, comp_cokerπ])
  inv := cokerDesc ψ (e.inv ≫ cokerπ φ) (by rw [← w]; simp)
  hom_inv_id := by rw [← cancel_epi (cokerπ φ)]; simp
  inv_hom_id := by rw [← cancel_epi (cokerπ ψ)]; simp

@[reassoc (attr := simp)]
lemma cokerπ_cokerCongr_hom {φ : M ⟶ N} {ψ : M ⟶ N'} (e : N ≅ N') (w : φ ≫ e.hom = ψ) :
    cokerπ φ ≫ (cokerCongr e w).hom = e.hom ≫ cokerπ ψ :=
  cokerπ_cokerDesc _ _ _

end Coker

end TopModuleCat

/-- The predecessor function of the cochain complex shape on `ℕ` is truncated subtraction. -/
lemma CochainComplex.prev_nat (j : ℕ) : (ComplexShape.up ℕ).prev j = j - 1 := by
  cases j <;> simp

namespace HomologicalComplex

open CategoryTheory Limits

variable {k : Type u} [CommRing k] [TopologicalSpace k]
variable {ι : Type w} {c : ComplexShape ι} (K : HomologicalComplex (TopModuleCat.{v} k) c)

/-- The cycles of a complex of topological modules, identified with the kernel of the
differential carrying the subspace topology. -/
noncomputable def cyclesIsoKer (i j : ι) (hij : c.next i = j) :
    K.cycles i ≅ TopModuleCat.ker (K.d i j) :=
  KernelFork.mapIsoOfIsLimit (K.cyclesIsKernel i j hij) (TopModuleCat.isLimitKer _) (Iso.refl _)

@[reassoc (attr := simp)]
lemma cyclesIsoKer_hom_kerι (i j : ι) (hij : c.next i = j) :
    (K.cyclesIsoKer i j hij).hom ≫ TopModuleCat.kerι (K.d i j) = K.iCycles i :=
  KernelFork.mapOfIsLimit_ι _ (TopModuleCat.isLimitKer (K.d i j)) (𝟙 _)

@[simp]
lemma cyclesIsoKer_hom_apply_coe (i j : ι) (hij : c.next i = j)
    (z : ↥(K.cycles i)) :
    ((K.cyclesIsoKer i j hij).hom z).1 = K.iCycles i z :=
  congr($(K.cyclesIsoKer_hom_kerι i j hij) z)

/-- The homology of a complex of topological modules, identified with the quotient of the
cycles by the boundaries, carrying the quotient topology. -/
noncomputable def homologyIsoCoker (i j : ι) (hij : c.prev j = i) :
    K.homology j ≅ TopModuleCat.coker (K.toCycles i j) :=
  CokernelCofork.mapIsoOfIsColimit (K.homologyIsCokernel i j hij)
    (TopModuleCat.isColimitCoker _) (Iso.refl _)

end HomologicalComplex

namespace ContinuousCohomology

open CategoryTheory TopRep

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Applying two consecutive differentials of the homogeneous cochain complex gives zero. -/
lemma _root_.TopRep.homogeneousCochains.d_comp_d_apply (X : TopRep k G) (i j l : ℕ)
    (σ : (homogeneousCochains X).X i) :
    (homogeneousCochains X).d j l ((homogeneousCochains X).d i j σ) = 0 := by
  simpa using congr($((homogeneousCochains X).d_comp_d i j l) σ)

/-- The coboundary map into the kernel model: the differential corestricted to the cocycles of
the next degree. In degree `0` the junk value `d 0 0 = 0` makes its range `⊥`, matching the
convention of `HomologicalComplex.homologyIsCokernel`. -/
noncomputable def bdryKer (X : TopRep k G) (j : ℕ) :
    (homogeneousCochains X).X (j - 1) ⟶
      TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)) :=
  TopModuleCat.ofHom
    (((homogeneousCochains X).d (j - 1) j).hom.codRestrict _
      fun y ↦ LinearMap.mem_ker.2 (homogeneousCochains.d_comp_d_apply X (j - 1) j (j + 1) y))

lemma bdryKer_apply_coe (X : TopRep k G) (j : ℕ) (y : ↥((homogeneousCochains X).X (j - 1))) :
    (bdryKer X j y).1 = (homogeneousCochains X).d (j - 1) j y := rfl

/-- Under the identification of the cycles with the kernel model, `toCycles` becomes the
corestricted differential `bdryKer`. -/
lemma toCycles_comp_cyclesIsoKer_hom (X : TopRep k G) (j : ℕ) :
    (homogeneousCochains X).toCycles (j - 1) j ≫
      ((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).hom = bdryKer X j := by
  refine ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext ?_
  rw [ConcreteCategory.comp_apply, (homogeneousCochains X).cyclesIsoKer_hom_apply_coe,
    bdryKer_apply_coe]
  exact congr($((homogeneousCochains X).toCycles_i (i := j - 1) (j := j)) y)

/-- **Continuous cohomology as cocycles modulo coboundaries.** `continuousCohomology j X` is
identified with the quotient of the kernel model of the `j`-cocycles by the image of the
`(j-1)`-st differential, carrying the quotient topology.

This is the handle that lets an explicit cocycle be turned into a cohomology class, and — via
`TopModuleCat.cokerπ_eq_zero_iff` — lets the vanishing of that class be read as the cocycle
being a coboundary. -/
noncomputable def cohomologyIsoQuot (X : TopRep k G) (j : ℕ) :
    continuousCohomology j X ≅ TopModuleCat.coker (bdryKer X j) :=
  (homogeneousCochains X).homologyIsoCoker (j - 1) j (CochainComplex.prev_nat j) ≪≫
    TopModuleCat.cokerCongr ((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp))
      (toCycles_comp_cyclesIsoKer_hom X j)

/-- **The cohomology class of a continuous `j`-cocycle**, as a `k`-linear map from the kernel
model of the cocycles to `continuousCohomology j X`.

This is the arrow every obstruction-theoretic argument needs: it turns an explicitly written
cocycle into a class, and `cocycleClass_eq_zero_iff` below turns the vanishing of that class
back into the cocycle being a coboundary. -/
noncomputable def cocycleClass (X : TopRep k G) (j : ℕ) :
    ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1))) →ₗ[k]
      ↥(continuousCohomology j X) :=
  (TopModuleCat.cokerπ (bdryKer X j) ≫ (cohomologyIsoQuot X j).inv).hom.toLinearMap

lemma cocycleClass_apply (X : TopRep k G) (j : ℕ)
    (c : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)))) :
    cocycleClass X j c = (cohomologyIsoQuot X j).inv (TopModuleCat.cokerπ (bdryKer X j) c) :=
  ConcreteCategory.comp_apply _ _ c

/-- **A cocycle has vanishing class exactly when it is a coboundary.** -/
lemma cocycleClass_eq_zero_iff (X : TopRep k G) (j : ℕ)
    (c : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)))) :
    cocycleClass X j c = 0 ↔ c ∈ (bdryKer X j).hom.range := by
  rw [← TopModuleCat.cokerπ_eq_zero_iff, cocycleClass_apply]
  refine ⟨fun hc => ?_, fun hc => by rw [hc, map_zero]⟩
  have h1 : (cohomologyIsoQuot X j).hom
      ((cohomologyIsoQuot X j).inv (TopModuleCat.cokerπ (bdryKer X j) c)) =
      TopModuleCat.cokerπ (bdryKer X j) c :=
    congr($((cohomologyIsoQuot X j).inv_hom_id) (TopModuleCat.cokerπ (bdryKer X j) c))
  rw [← h1, hc, map_zero]

end ContinuousCohomology

/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.DirectSum.Basic

/-!
# The induced grading on a quotient by a homogeneous ideal

If `𝒜 : ι → Submodule R A` makes `A` a graded algebra and `I : Ideal A` is
homogeneous for `𝒜`, then `A ⧸ I` is graded by the images of the `𝒜 i`.

This is the standard "quotient of a graded ring by a homogeneous ideal is
graded" statement (Stacks Project, tag 00JL; Bourbaki, *Algèbre* II §11).  It
is what lets a projective model be formed as `Proj` of a quotient of a
polynomial ring, and it is absent from `Mathlib/RingTheory/GradedAlgebra/`
at this pin: `Ideal.IsHomogeneous` and `HomogeneousIdeal` exist, the induced
grading on `A ⧸ I` does not.

## Main definitions

* `HomogeneousIdeal.quotientGrading` — the family `i ↦ (𝒜 i).map (mk I)` of
  `R`-submodules of `A ⧸ I`.
* `HomogeneousIdeal.instGradedAlgebraQuotientGrading` — the `GradedAlgebra`
  (equivalently `GradedRing`) instance on that family.

## Implementation notes

The grading is stated for a *bundled* `HomogeneousIdeal 𝒜` rather than for a
bare `I : Ideal A` together with `hI : I.IsHomogeneous 𝒜`, because the
`GradedAlgebra` structure has to be an `instance`: instance resolution cannot
discharge an unbundled homogeneity hypothesis.  An unbundled ideal is used by
writing `(⟨I, hI⟩ : HomogeneousIdeal 𝒜)`.

The `DirectSum.Decomposition` field is built from the decomposition of `A`
itself: `DirectSum.decompose 𝒜` followed by the degreewise map
`DirectSum.map`.  Homogeneity of `I` is exactly what makes that composite kill
`I`, so it descends to `A ⧸ I`.
-/

@[expose] public section

open DirectSum

namespace HomogeneousIdeal

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

/-- The grading induced on `A ⧸ I` by a grading of `A` and a homogeneous ideal
`I`: the degree-`i` piece is the image of `𝒜 i` under the quotient map. -/
def quotientGrading (i : ι) : Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

variable {𝒜 I}

theorem mem_quotientGrading {i : ι} {x : A ⧸ I.toIdeal} :
    x ∈ quotientGrading 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I.toIdeal a = x :=
  Submodule.mem_map

theorem mk_mem_quotientGrading {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk I.toIdeal a ∈ quotientGrading 𝒜 I i :=
  mem_quotientGrading.mpr ⟨a, ha, rfl⟩

variable (𝒜 I)

instance instSetLikeGradedMonoidQuotientGrading :
    SetLike.GradedMonoid (quotientGrading 𝒜 I) where
  one_mem := by
    simpa using mk_mem_quotientGrading (I := I) (SetLike.one_mem_graded 𝒜)
  mul_mem := by
    rintro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := mem_quotientGrading.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_quotientGrading.mp hy
    simpa using mk_mem_quotientGrading (I := I) (SetLike.mul_mem_graded ha hb)

/-- The quotient map, restricted to the degree-`i` pieces. -/
def gradingHom (i : ι) : 𝒜 i →+ quotientGrading 𝒜 I i where
  toFun a := ⟨Ideal.Quotient.mk I.toIdeal (a : A), mk_mem_quotientGrading a.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp]
theorem coe_gradingHom (i : ι) (a : 𝒜 i) :
    (gradingHom 𝒜 I i a : A ⧸ I.toIdeal) = Ideal.Quotient.mk I.toIdeal (a : A) :=
  rfl

/-- The degreewise quotient map `⨁ 𝒜 i → ⨁ (𝒜 i ↠ A ⧸ I)`. -/
def directSumMap : (⨁ i, 𝒜 i) →+ ⨁ i, quotientGrading 𝒜 I i :=
  DirectSum.map (gradingHom 𝒜 I)

theorem coeAddMonoidHom_comp_directSumMap :
    (DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I)).comp (directSumMap 𝒜 I)
      = (Ideal.Quotient.mk I.toIdeal : A →+* A ⧸ I.toIdeal).toAddMonoidHom.comp
          (DirectSum.coeAddMonoidHom 𝒜) := by
  refine DirectSum.addHom_ext fun i y => ?_
  simp [directSumMap, DirectSum.coeAddMonoidHom_of]

theorem coe_directSumMap (z : ⨁ i, 𝒜 i) :
    DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I) (directSumMap 𝒜 I z)
      = Ideal.Quotient.mk I.toIdeal (DirectSum.coeAddMonoidHom 𝒜 z) :=
  DFunLike.congr_fun (coeAddMonoidHom_comp_directSumMap 𝒜 I) z

/-- The decomposition of `A`, pushed degreewise into `A ⧸ I`. -/
def decomposeAux : A →+ ⨁ i, quotientGrading 𝒜 I i :=
  (directSumMap 𝒜 I).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

theorem decomposeAux_apply (a : A) :
    decomposeAux 𝒜 I a = directSumMap 𝒜 I (DirectSum.decompose 𝒜 a) := rfl

/-- Homogeneity of `I` is exactly what makes `decomposeAux` kill `I`. -/
theorem decomposeAux_eq_zero_of_mem {a : A} (ha : a ∈ I.toIdeal) :
    decomposeAux 𝒜 I a = 0 := by
  rw [decomposeAux_apply, DirectSum.ext_iff]
  intro j
  rw [directSumMap, DirectSum.map_apply, DirectSum.zero_apply]
  ext
  simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr (I.is_homogeneous' j ha)

/-- The decomposition map of `A ⧸ I`. -/
def quotientDecompose : (A ⧸ I.toIdeal) →+ ⨁ i, quotientGrading 𝒜 I i where
  toFun x := Quotient.liftOn' x (decomposeAux 𝒜 I) (by
    intro a b hab
    have hmem : a - b ∈ I.toIdeal := (Submodule.quotientRel_def _).mp hab
    have h0 : decomposeAux 𝒜 I (a - b) = 0 := decomposeAux_eq_zero_of_mem 𝒜 I hmem
    rw [map_sub, sub_eq_zero] at h0
    exact h0)
  map_zero' := map_zero _
  map_add' := by rintro ⟨a⟩ ⟨b⟩; exact map_add (decomposeAux 𝒜 I) a b

theorem quotientDecompose_mk (a : A) :
    quotientDecompose 𝒜 I (Ideal.Quotient.mk I.toIdeal a) = decomposeAux 𝒜 I a := rfl

theorem coeAddMonoidHom_comp_quotientDecompose :
    (DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I)).comp (quotientDecompose 𝒜 I)
      = AddMonoidHom.id _ := by
  ext x
  induction x using Quotient.inductionOn' with
  | h a =>
    show DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I) (decomposeAux 𝒜 I a) = _
    rw [decomposeAux_apply, coe_directSumMap]
    exact congrArg (Ideal.Quotient.mk I.toIdeal)
      (DirectSum.Decomposition.left_inv (ℳ := 𝒜) a)

theorem quotientDecompose_comp_coeAddMonoidHom :
    (quotientDecompose 𝒜 I).comp (DirectSum.coeAddMonoidHom (quotientGrading 𝒜 I))
      = AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext fun i y => ?_
  obtain ⟨a, ha, hay⟩ := mem_quotientGrading.mp y.2
  rw [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
    AddMonoidHom.id_apply, ← hay, quotientDecompose_mk, decomposeAux_apply,
    DirectSum.decompose_of_mem 𝒜 ha, directSumMap, DirectSum.map_of]
  exact congrArg _ (Subtype.ext (by simpa using hay))

instance instDecompositionQuotientGrading :
    DirectSum.Decomposition (quotientGrading 𝒜 I) :=
  DirectSum.Decomposition.ofAddHom (quotientGrading 𝒜 I) (quotientDecompose 𝒜 I)
    (coeAddMonoidHom_comp_quotientDecompose 𝒜 I)
    (quotientDecompose_comp_coeAddMonoidHom 𝒜 I)

/-- **The quotient of a graded algebra by a homogeneous ideal is graded.**

For `𝒜 : ι → Submodule R A` with `[GradedAlgebra 𝒜]` and a homogeneous ideal
`I`, the quotient `A ⧸ I` is graded by the images `(𝒜 i).map (mk I)`.  Since
`GradedAlgebra` is an abbreviation for `GradedRing`, this is simultaneously the
`GradedRing` instance, which is the form `AlgebraicGeometry.Proj` consumes. -/
instance instGradedAlgebraQuotientGrading : GradedAlgebra (quotientGrading 𝒜 I) where

end HomogeneousIdeal

end

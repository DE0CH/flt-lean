/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Fermat.FLT.Mathlib.RingTheory.GradedAlgebra.Quotient

/-!
# The projective Weierstrass model as a scheme

`Proj` of the homogeneous coordinate ring
`R[X, Y, Z] ⧸ (Y²Z + a₁XYZ + a₃YZ² - X³ - a₂X²Z - a₄XZ² - a₆Z³)`.

This is item 2 of the routable specification in the docstring of
`exists_ellipticScheme_of_weierstrass` (`Fermat/FLT/ModularCurve/X0.lean`),
and it is the first consumer of
`HomogeneousIdeal.quotientGrading` — without a `GradedRing` structure on the
quotient of a graded ring by a homogeneous ideal, the scheme `A` of that node
cannot even be *formed*.

## Main definitions

* `WeierstrassCurve.Projective.isHomogeneous_polynomial` — the projective
  Weierstrass polynomial is homogeneous of degree `3`.
* `WeierstrassCurve.Projective.polynomialHomogeneousIdeal` — the ideal it
  generates, as a bundled `HomogeneousIdeal`.
* `WeierstrassCurve.Projective.projGrading` — the induced grading on the
  homogeneous coordinate ring.
* `WeierstrassCurve.Projective.proj` — the projective model as a `Scheme`.
* `WeierstrassCurve.Projective.projToSpec` — its structure morphism to
  `Spec R`.

## Implementation notes

`MvPolynomial.gradedAlgebra` is deliberately *not* a global instance in
mathlib (a different weight function gives a different grading), so it is
introduced here with `attribute [local instance]`.  Consequently the *types*
of the declarations below mention a locally supplied instance, and a consumer
in another file must reintroduce the same local instance.  That is the same
convention mathlib itself uses for `homogeneousSubmodule`.

Nothing here asserts smoothness, properness or the group law: those are items
3, 5, 6 and 7 of the specification, and they are separate.  This file only
does what item 2 says — it *forms the scheme*.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open _root_.MvPolynomial

namespace WeierstrassCurve.Projective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The projective Weierstrass polynomial
`Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)` is homogeneous of
degree `3`. -/
theorem isHomogeneous_polynomial : (polynomial W).IsHomogeneous 3 := by
  have hX : (X (0 : Fin 3) : MvPolynomial (Fin 3) R).IsHomogeneous 1 :=
    isHomogeneous_X _ _
  have hY : (X (1 : Fin 3) : MvPolynomial (Fin 3) R).IsHomogeneous 1 :=
    isHomogeneous_X _ _
  have hZ : (X (2 : Fin 3) : MvPolynomial (Fin 3) R).IsHomogeneous 1 :=
    isHomogeneous_X _ _
  have hX2 : ((X (0 : Fin 3) : MvPolynomial (Fin 3) R) ^ 2).IsHomogeneous 2 :=
    isHomogeneous_X_pow _ _
  have hY2 : ((X (1 : Fin 3) : MvPolynomial (Fin 3) R) ^ 2).IsHomogeneous 2 :=
    isHomogeneous_X_pow _ _
  have hZ2 : ((X (2 : Fin 3) : MvPolynomial (Fin 3) R) ^ 2).IsHomogeneous 2 :=
    isHomogeneous_X_pow _ _
  have hX3 : ((X (0 : Fin 3) : MvPolynomial (Fin 3) R) ^ 3).IsHomogeneous 3 :=
    isHomogeneous_X_pow _ _
  have hZ3 : ((X (2 : Fin 3) : MvPolynomial (Fin 3) R) ^ 3).IsHomogeneous 3 :=
    isHomogeneous_X_pow _ _
  rw [polynomial]
  refine IsHomogeneous.sub (IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_)
    (IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_) ?_)
  · simpa using hY2.mul hZ
  · simpa using ((hX.C_mul W.a₁).mul hY).mul hZ
  · simpa using (hY.C_mul W.a₃).mul hZ2
  · exact hX3
  · simpa using (hX2.C_mul W.a₂).mul hZ
  · simpa using (hX.C_mul W.a₄).mul hZ2
  · exact hZ3.C_mul W.a₆

/-- The ideal cut out by the projective Weierstrass equation, as a bundled
homogeneous ideal of `R[X, Y, Z]`. -/
noncomputable def polynomialHomogeneousIdeal :
    HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) where
  toSubmodule := Ideal.span {polynomial W}
  is_homogeneous' := by
    refine Ideal.homogeneous_span _ _ fun p hp => ?_
    rw [Set.mem_singleton_iff] at hp
    exact ⟨3, hp ▸ isHomogeneous_polynomial W⟩

/-- The homogeneous coordinate ring of the projective Weierstrass model,
graded by the images of the spaces of homogeneous polynomials.

This is where `HomogeneousIdeal.quotientGrading` is used. -/
noncomputable abbrev projGrading : ℕ →
    Submodule R (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :=
  HomogeneousIdeal.quotientGrading (homogeneousSubmodule (Fin 3) R)
    (polynomialHomogeneousIdeal W)

/-- **The projective Weierstrass model of `W` as a scheme**, namely `Proj` of
the homogeneous coordinate ring `R[X, Y, Z] ⧸ (W)`. -/
noncomputable def proj : Scheme.{u} :=
  AlgebraicGeometry.Proj (projGrading W)

/-- The structure morphism of the projective Weierstrass model over its
base, `proj W ⟶ Spec R`.

It is `Proj.toSpecZero` followed by `Spec` of the map from `R` into the
degree-zero part of the coordinate ring. -/
noncomputable def projToSpec : proj W ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projGrading W) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (projGrading W 0)))

/-! ### Inversion: the Weierstrass involution as an automorphism of the model

`[X : Y : Z] ↦ [X : −Y − a₁X − a₃Z : Z]` is the one piece of the
chord–tangent group law that is a morphism **outright**, with no gluing:
the substitution `Y ↦ −Y − a₁X − a₃Z` is a *degree-preserving ring
automorphism* of `R[X, Y, Z]` that fixes the Weierstrass polynomial on the
nose, hence descends to a graded automorphism of the homogeneous
coordinate ring, and `Proj` is a functor of the graded ring
(`AlgebraicGeometry.Proj.map`).

The fixed-polynomial computation is the classical identity behind
`W.negY`: writing `Y' = −Y − a₁X − a₃Z`,

`Y'²Z + a₁XY'Z + a₃Y'Z² = Y²Z + a₁XYZ + a₃YZ²`,

and the remaining terms of `W` involve no `Y` at all.

Note that no compatibility with the structure morphism has to be proved
separately for the base `ℚ`: see `Fermat.subsingleton_hom_spec_rat` in
`Fermat/FLT/ModularCurve/EllipticScheme.lean`. -/

/-- The images of `X`, `Y`, `Z` under the Weierstrass involution
`[X : Y : Z] ↦ [X : −Y − a₁X − a₃Z : Z]`. -/
noncomputable def negVars : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X (0 : Fin 3),
    -X (1 : Fin 3) - C W.a₁ * X (0 : Fin 3) - C W.a₃ * X (2 : Fin 3),
    X (2 : Fin 3)]

@[simp] theorem negVars_zero : negVars W 0 = X (0 : Fin 3) := rfl

@[simp] theorem negVars_one :
    negVars W 1 = -X (1 : Fin 3) - C W.a₁ * X (0 : Fin 3) - C W.a₃ * X (2 : Fin 3) := rfl

@[simp] theorem negVars_two : negVars W 2 = X (2 : Fin 3) := rfl

/-- Each coordinate of the Weierstrass involution is a linear form, i.e.
homogeneous of degree `1`.  This is what makes the involution *graded*. -/
theorem negVars_isHomogeneous (i : Fin 3) : (negVars W i).IsHomogeneous 1 := by
  fin_cases i
  · exact isHomogeneous_X _ _
  · exact (((isHomogeneous_X _ _).neg).sub ((isHomogeneous_X _ _).C_mul _)).sub
      ((isHomogeneous_X _ _).C_mul _)
  · exact isHomogeneous_X _ _

/-- **The Weierstrass involution** `Y ↦ −Y − a₁X − a₃Z` of `R[X, Y, Z]`. -/
noncomputable def negAlgHom : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval (negVars W)

@[simp] theorem negAlgHom_X (i : Fin 3) : negAlgHom W (X i) = negVars W i := by
  simp [negAlgHom]

/-- The Weierstrass involution preserves each degree. -/
theorem isHomogeneous_negAlgHom {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (negAlgHom W p).IsHomogeneous n := by
  simpa only [one_mul, negAlgHom] using hp.aeval (negVars W) (negVars_isHomogeneous W)

/-- **The Weierstrass involution is an involution.** -/
theorem negAlgHom_comp_negAlgHom :
    (negAlgHom W).comp (negAlgHom W) = AlgHom.id R (MvPolynomial (Fin 3) R) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> (simp [negAlgHom, negVars]; ring)

@[simp] theorem negAlgHom_negAlgHom (p : MvPolynomial (Fin 3) R) :
    negAlgHom W (negAlgHom W p) = p := by
  simpa using DFunLike.congr_fun (negAlgHom_comp_negAlgHom W) p

/-- **The Weierstrass involution fixes the Weierstrass polynomial.**  This
is the identity that makes the involution descend to the homogeneous
coordinate ring. -/
@[simp] theorem negAlgHom_polynomial : negAlgHom W (polynomial W) = polynomial W := by
  rw [polynomial]
  simp only [map_add, map_sub, map_mul, map_pow, negAlgHom, aeval_C, aeval_X, negVars_zero,
    negVars_one, negVars_two, MvPolynomial.algebraMap_eq]
  ring

theorem negAlgHom_mem_polynomialHomogeneousIdeal {p : MvPolynomial (Fin 3) R}
    (hp : p ∈ (polynomialHomogeneousIdeal W).toIdeal) :
    negAlgHom W p ∈ (polynomialHomogeneousIdeal W).toIdeal := by
  have h : (polynomialHomogeneousIdeal W).toIdeal = Ideal.span {polynomial W} := rfl
  rw [h, Ideal.mem_span_singleton] at hp ⊢
  obtain ⟨c, rfl⟩ := hp
  exact ⟨negAlgHom W c, by rw [map_mul, negAlgHom_polynomial]⟩

/-- The Weierstrass involution, descended to the homogeneous coordinate
ring `R[X, Y, Z] ⧸ (W)`. -/
noncomputable def negQuot :
    (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) →+*
      (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (negAlgHom W).toRingHom)
    fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2 (negAlgHom_mem_polynomialHomogeneousIdeal W ha)

@[simp] theorem negQuot_mk (p : MvPolynomial (Fin 3) R) :
    negQuot W (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (negAlgHom W p) := rfl

@[simp] theorem negQuot_negQuot (a : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :
    negQuot W (negQuot W a) = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [negQuot_mk, negQuot_mk, negAlgHom_negAlgHom]

/-- **The Weierstrass involution as a GRADED ring automorphism** of the
homogeneous coordinate ring.  This is the input `Proj.map` consumes. -/
noncomputable def negGradedHom : projGrading W →+*ᵍ projGrading W where
  __ := negQuot W
  map_mem := by
    intro i x hx
    obtain ⟨a, ha, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp hx
    exact HomogeneousIdeal.mem_quotientGrading.mpr
      ⟨negAlgHom W a, isHomogeneous_negAlgHom W ha, rfl⟩

@[simp] theorem negGradedHom_apply
    (a : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :
    negGradedHom W a = negQuot W a := rfl

theorem negGradedHom_comp_negGradedHom :
    (negGradedHom W).comp (negGradedHom W) = GradedRingHom.id (projGrading W) := by
  ext a
  simp

/-- The involution sends the irrelevant ideal onto itself, which is the
hypothesis `Proj.map` needs. -/
theorem irrelevant_le_map_negGradedHom :
    HomogeneousIdeal.irrelevant (projGrading W) ≤
      (HomogeneousIdeal.irrelevant (projGrading W)).map (negGradedHom W) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  have h1 : negGradedHom W a ∈ HomogeneousIdeal.irrelevant (projGrading W) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi ((negGradedHom W).map_mem ha)
  have h2 := Ideal.mem_map_of_mem (negGradedHom W) h1
  rw [show (negGradedHom W) (negGradedHom W a) = a from negQuot_negQuot W a] at h2
  exact h2

/-- **Inversion on the projective Weierstrass model**,
`[X : Y : Z] ↦ [X : −Y − a₁X − a₃Z : Z]`, as a morphism of schemes.

This is one of the three pieces of data of a `ProjGroupLaw`
(`Fermat/FLT/ModularCurve/EllipticScheme.lean`) and, unlike the group law
`m`, it needs no gluing: it is `Proj` applied to a graded automorphism of
the homogeneous coordinate ring. -/
noncomputable def projNeg : proj W ⟶ proj W :=
  Proj.map (negGradedHom W) (irrelevant_le_map_negGradedHom W)

/-- **Inversion is an involution of the projective model.** -/
@[simp] theorem projNeg_comp_projNeg : projNeg W ≫ projNeg W = 𝟙 (proj W) := by
  show Proj.map (negGradedHom W) _ ≫ Proj.map (negGradedHom W) _ =
    𝟙 (Proj (projGrading W))
  rw [← Proj.map_comp]
  simp only [negGradedHom_comp_negGradedHom]
  exact Proj.map_id

end WeierstrassCurve.Projective

end

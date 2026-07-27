/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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

end WeierstrassCurve.Projective

end

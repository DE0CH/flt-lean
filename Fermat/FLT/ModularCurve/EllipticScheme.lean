/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveModel
public import Fermat.FLT.EllipticCurve.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The projective Weierstrass model as an elliptic scheme over `Spec ℚ`

This module assembles `Fermat.exists_ellipticScheme_of_weierstrass`
(`Fermat/FLT/ModularCurve/X0.lean`) out of the pieces that had to land
first, and it exists as a SEPARATE module for one specific reason, given
under "Why this is not in `X0.lean`" below.

## Main definitions and results

* `Fermat.ProjGroupLaw` — morphism-level group-law data on the projective
  Weierstrass model, in exactly the shape
  `AbelianSchemeStruct.ofMorphisms` consumes.
* `Fermat.ProjGroupLaw.toAbelianSchemeStruct` — the bridge to
  `AbelianSchemeStruct` (PROVEN, formal).
* `Fermat.exists_ellipticScheme_of_projModel` — the assembled statement,
  which `X0.lean` transports verbatim onto
  `exists_ellipticScheme_of_weierstrass`.

`isProper_projToSpec` is PROVEN, and so now is `smoothOfRelativeDimension_projToSpec`
apart from three leaves that are all missing pieces of MATHLIB rather than of
this development.  `locally_isStandardSmooth_awayCoord` — the last direct sorry of
item 7a — is now PROVEN from them, and they are, in the "Dehomogenisation"
section: `exists_projChartRingEquiv` (the dehomogenisation isomorphism
`(ℚ[X, Y, Z] ⧸ (W))_{(xᵢ)}` in degree `0` ≃ `ℚ[u, v] ⧸ (wᵢ)`),
`projChart_jacobian_span_eq_top` (the chart Jacobian criterion, where `hjac` and
hence `Δ` is consumed), and
`isStandardSmoothOfRelativeDimension_projChartAway` (a plane curve is standard
smooth of relative dimension `1` where a partial derivative is invertible).
The remaining open leaves of the file are those three plus
`nonempty_projGroupLaw`, `exists_projGeomFibreAddEquiv`, and the interior of
`geometricallyConnected_projToSpec`, which still carries three named sorried
steps `hbc`/`hne`/`hpre`.  Each declaration carries its own docstring saying what
is missing and where the classical argument is.

## Why this is not in `X0.lean`

**A global token collision, and it is not a stylistic choice.**
`ProjectiveModel` reaches
`Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean` and through
it `Mathlib/Tactic/Ring/NamePolyVars.lean`, which declares the command
syntax `name_poly_vars … " over " …`.  **Lean's token table is global**: an
atom reserved by any transitively imported module becomes a keyword,
whether or not the notation is ever opened.  So the bare identifier `over`
stops parsing in every module that transitively imports `ProjectiveModel`.

That is not hypothetical.  `X0.lean` declares
`IsCompactificationY0.over`, and `X0.lean` is `public import`ed by
`MazurTorsion.lean`, whose own dependent cone includes `ModThree.lean`,
`HermiteMinkowski.lean`, `Mazur.lean`, `InertiaCardTransport.lean` and
`CompletionInvariance.lean` — and `ModThree.lean` uses mathlib's
`Ideal.LiesOver.over`.  A `public import` of `ProjectiveModel` into
`X0.lean` therefore breaks files several modules downstream, with the error
reported at their `over` occurrence rather than at the import.

Keeping the `ProjectiveModel` dependency HERE, and having `X0.lean` take a
NON-public `import` of this module, confines the reserved token to
`X0.lean` itself (where the single affected field is written `«over»`,
which preserves the declaration name exactly) instead of propagating it
through the whole `MazurTorsion` cone.

The statement of `exists_ellipticScheme_of_projModel` is existential over
the scheme, so it mentions neither `proj` nor `projToSpec`; that is what
makes a proof-body-only use in `X0.lean`, and hence the non-public import,
sufficient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped WeierstrassCurve.Affine

namespace Fermat

section EllipticScheme

open _root_.WeierstrassCurve.Projective

/-  `MvPolynomial.gradedAlgebra` is deliberately not a global instance in mathlib (a
different weight function gives a different grading), so — exactly as in
`ProjectiveModel.lean`, and by the same convention mathlib uses for
`homogeneousSubmodule` — it has to be reintroduced locally in any file that mentions
`projGrading` as a graded ring rather than merely mentioning `proj`/`projToSpec`,
whose *types* carry no instance. -/
attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Morphism-level group-law data on the projective Weierstrass model
of `E`**, in exactly the shape `AbelianSchemeStruct.ofMorphisms`
consumes: a group law on the fibre square, a unit section over the base,
an inversion, each compatible with the structure morphism, and the four
group axioms as EQUATIONS OF MORPHISMS.

This is why the node is writable at all.  `AbelianSchemeStruct.add` is an
operation on `RelPoint f g` for an ARBITRARY test scheme `T`, and there
is no functor-of-points description of `Hom(T, Proj 𝒜)` at this pin —
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean` gives only
functoriality `Proj ℬ ⟶ Proj 𝒜` in the graded ring.  So `add` cannot be
written by hand on `T`-points.  Equations of morphisms can be, and
`ofMorphisms` derives the `T`-point presentation from them.

This structure carries no ellipticity hypothesis: it is data plus
equations, and it is satisfiable only for a genuine elliptic curve, which
is recorded in `nonempty_projGroupLaw` where the hypothesis belongs.  It
is deliberately NOT an interface to build against — `AbelianSchemeStruct`
is that interface, and `toAbelianSchemeStruct` is the one-line bridge. -/
structure ProjGroupLaw (E : WeierstrassCurve ℚ) where
  /-- the group law `A ×_ℚ A ⟶ A` -/
  m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E
  /-- the unit section `Spec ℚ ⟶ A`, i.e. the point at infinity -/
  e : Spec (CommRingCat.of ℚ) ⟶ proj E
  /-- inversion `A ⟶ A` -/
  i : proj E ⟶ proj E
  /-- the group law lies over the base -/
  hm : m ≫ projToSpec E =
    Limits.pullback.fst (projToSpec E) (projToSpec E) ≫ projToSpec E
  /-- the unit really is a section -/
  he : e ≫ projToSpec E = 𝟙 (Spec (CommRingCat.of ℚ))
  /-- inversion lies over the base -/
  hi : i ≫ projToSpec E = projToSpec E
  /-- associativity, on the threefold fibre product -/
  hassoc : AbelianSchemeStruct.triAddLeft (projToSpec E) m hm =
    AbelianSchemeStruct.triAddRight (projToSpec E) m hm
  /-- commutativity, as invariance under the swap of the two factors -/
  hcomm : Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
    (Limits.pullback.fst (projToSpec E) (projToSpec E))
    Limits.pullback.condition.symm ≫ m = m
  /-- the unit law -/
  hunit : Limits.pullback.lift (projToSpec E ≫ e) (𝟙 (proj E))
    (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 (proj E)
  /-- the inverse law -/
  hinv : Limits.pullback.lift i (𝟙 (proj E)) (by rw [hi, Category.id_comp]) ≫ m =
    projToSpec E ≫ e

/-- **The chord–tangent law on the projective Weierstrass model, as
morphisms of schemes** (sorry node — items 5+6 of the routable
specification in `exists_ellipticScheme_of_weierstrass`'s docstring).

TRUE and classical.  The addition FORMULAS are already at this pin over
an arbitrary `[CommRing R]` —
`WeierstrassCurve.Projective.addXYZ`/`addX`/`addY`/`addZ` in
`EllipticCurve/Projective/Formula.lean` — so nothing has to be invented;
what is missing is the *gluing*.  The formulas degenerate on the locus
where the naive chart fails, so `m` is obtained from the standard
three-chart cover of `A ×_ℚ A` together with agreement on the overlaps.
`e` is the point at infinity `[0 : 1 : 0]`, a section over `Spec ℚ`
because that point is rational; `i` is `[X : −Y − a₁X − a₃Z : Z]`, which
is a morphism outright.

`hassoc` (item 6) is the one axiom that is not a chart computation: as an
equation of morphisms out of `A ×_ℚ A ×_ℚ A` it is classically the
rigidity lemma, or the theorem of the cube, or — since `A ×_ℚ A ×_ℚ A` is
reduced and its generic fibre dense, `ℚ` having characteristic zero — a
reduction to equality of the two composites on `ℚ̄`-points, where it is
associativity of the classical group law of `E(ℚ̄)`.  That last route is
the cheapest here, and it is why ellipticity rather than mere smoothness
is hypothesised: `Δ ≠ 0` is what makes the generic fibre a smooth curve
and the reducedness argument valid.

`hcomm`, `hunit` and `hinv` are chart identities in the same formulas,
and are the easy half. -/
theorem nonempty_projGroupLaw (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Nonempty (ProjGroupLaw E) :=
  sorry

/-- **The projective Weierstrass model is proper over `Spec ℚ`** (PROVEN).

`projToSpec` is `Proj.toSpecZero` FOLLOWED by
`Spec.map (algebraMap ℚ (projGrading E 0))`, and properness is not stable under
postcomposition in general, so the proof is in two halves.

*The first factor.*  Mathlib has `IsProper (Proj.toSpecZero 𝒜)` under
`[Algebra.FiniteType (𝒜 0) A]`.  That hypothesis is obtained here by descending
`Algebra.FiniteType ℚ (ℚ[X, Y, Z] ⧸ (W))` — itself a quotient of a polynomial ring
in finitely many variables — along the tower `ℚ → projGrading E 0 → ℚ[X, Y, Z] ⧸ (W)`
with `Algebra.FiniteType.of_restrictScalars_finiteType`.

*The second factor* is an ISOMORPHISM: the degree-zero part of the homogeneous
coordinate ring of the Weierstrass cubic is `ℚ` itself.  Surjectivity is
`MvPolynomial.homogeneousSubmodule_zero` (`homogeneousSubmodule σ R 0 = 1`), which
says every degree-`0` homogeneous polynomial is a constant.  Injectivity is the
observation that the ideal `(W)` meets the constants trivially, and the cheap proof
of that is NOT a degree count but the ring hom `MvPolynomial.constantCoeff`: it kills
`W` (a homogeneous polynomial of degree `3 ≠ 0` has no constant term), so it kills
every multiple of `W`, while it sends `C c` to `c`.

Two implementation notes worth keeping, both of which cost a verification cycle:

* The `IsScalarTower ℚ ↥(projGrading E 0) (ℚ[X, Y, Z] ⧸ (W))` that
  `of_restrictScalars_finiteType` consumes must be produced with `R`/`S`/`A` PINNED BY
  NAME.  Elaborating the statement instead picks the `Submodule.smul` and
  `Submodule.Quotient.instSMul'` scalar actions, whereas every `FiniteType` lemma is
  stated over `Algebra.toSMul`; the two are a diamond, and `apply` fails to unify.
* Both bridging identities — `↑(algebraMap ℚ ↥(𝒜 0) c) = algebraMap ℚ A c` and
  `algebraMap ↥(𝒜 0) A x = ↑x` — are `rfl`
  (`SetLike.GradeZero.coe_algebraMap`, `SetLike.GradeZero.algebraMap_apply`), which is
  what makes the two `Subtype.val` crossings free.

**FORMAL-CONTENT NOTE.** `[E.IsElliptic]` is NOT used: properness holds for the
projective model of an arbitrary Weierstrass equation over `ℚ`, singular or not, since
`Proj` of a finite-type graded ring is always proper over its degree-zero part.  The
discriminant enters only at `smoothOfRelativeDimension_projToSpec`.  The hypothesis is
retained because the signature is consumed by `ProjGroupLaw.toAbelianSchemeStruct` and
is fixed by the cut, not because this leaf needs it. -/
theorem isProper_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    IsProper (projToSpec E) := by
  -- The projective Weierstrass polynomial has vanishing constant term: it is
  -- homogeneous of degree `3`, and `3 ≠ 0`.
  have hc : MvPolynomial.constantCoeff (polynomial E) = 0 :=
    (isHomogeneous_polynomial E).coeff_eq_zero (d := 0) (by simp)
  -- Hence `ℚ → ℚ[X, Y, Z] ⧸ (W)` is injective: a constant in `(W)` is `b * W`, and
  -- `constantCoeff` sends that to `0`.
  have hinj : Function.Injective (algebraMap ℚ
      (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal)) := by
    intro c c' h
    have h' : (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal
          (MvPolynomial.C c)) = Ideal.Quotient.mk _ (MvPolynomial.C c') := h
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← MvPolynomial.C_sub] at h'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h'
    have hcc := congrArg MvPolynomial.constantCoeff hb
    rw [map_mul, hc, mul_zero, MvPolynomial.constantCoeff_C] at hcc
    exact sub_eq_zero.mp hcc.symm
  -- The degree-zero part of the homogeneous coordinate ring is exactly `ℚ`.
  have hbij : Function.Bijective (algebraMap ℚ (projGrading E 0)) := by
    refine ⟨fun c c' h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp hx
    rw [MvPolynomial.homogeneousSubmodule_zero] at hp
    obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hp
    exact ⟨c, rfl⟩
  -- `R`/`S`/`A` pinned by name: see the implementation note above.
  haveI := IsScalarTower.of_algebraMap_eq (R := ℚ) (S := (projGrading E 0))
    (A := MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) fun _ => rfl
  haveI : Algebra.FiniteType ℚ
      (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ _) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType (projGrading E 0)
      (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℚ _ _
  haveI : IsIso (CommRingCat.ofHom (algebraMap ℚ (projGrading E 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  show IsProper (Proj.toSpecZero (projGrading E) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (projGrading E 0))))
  infer_instance

/-! ### The Jacobian criterion for a Weierstrass equation

The three lemmas below are the ring-theoretic heart of item 7a, and they hold over an
ARBITRARY commutative ring — nothing here is special to `ℚ`.

The point is `Δ_mem_jacobianSpan`: the discriminant lies in the ideal generated by the
Weierstrass polynomial and its two partial derivatives, evaluated at any pair of ring
elements.  Granted that, `IsElliptic` (which says `Δ` is a UNIT) upgrades "the Jacobian
ideal contains `Δ`" to "the Jacobian ideal is everything" at any point OF the curve, which
is exactly the hypothesis the Jacobian criterion for smoothness consumes.

The certificate is found by a route that keeps the cofactors small.  Written directly, the
identity `Δ = A·W + B·W_X + C·W_Y` in `ℚ[a₁,…,a₆][X, Y]` has cofactors of forty-odd terms
(confirmed by a Gröbner `lift`).  But mathlib's own variable change `(X, Y) ↦ (X + x, Y + y)`
— i.e. `VariableChange.mk 1 x 0 y` — carries the curve to one whose `a₃`, `a₄`, `a₆` ARE
(up to sign) the three quantities `W_Y`, `W_X`, `W` evaluated at `(x, y)`, while fixing `Δ`.
So it suffices to certify `Δ ∈ (a₃, a₄, a₆)` in `ℤ[a₁,…,a₆]`, where the cofactors are tiny
and `ring` closes the identity outright.  That is `Δ_eq_coeffCombination`.

A numerical check worth recording: over `ℚ[a₁,…,a₆][u, v]` the Jacobian ideal of each of the
three standard charts does NOT contain `1`, so `Δ` is genuinely carrying the content here —
the statement is not vacuously true. -/

/-- **`Δ` lies in the ideal `(a₃, a₄, a₆)`**, with explicit cofactors.

Read off from `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` by expanding each of `b₈`, `b₄³`, `b₆²`
and `b₂b₄b₆` along `a₃`, `a₄`, `a₆`; `ring` verifies the result. -/
theorem Δ_eq_coeffCombination {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.Δ =
      (-W.b₂ ^ 2 * (W.a₂ * W.a₃ - W.a₁ * W.a₄) - 8 * W.b₄ ^ 2 * W.a₁ - 27 * W.b₆ * W.a₃
        + 9 * W.b₂ * W.b₄ * W.a₃) * W.a₃
      + (W.b₂ ^ 2 * W.a₄ - 16 * W.b₄ ^ 2) * W.a₄
      + (-W.b₂ ^ 3 - 108 * W.b₆ + 36 * W.b₂ * W.b₄) * W.a₆ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    WeierstrassCurve.Δ]
  ring

/-- Translating the curve by `(x, y)` sends `a₃` to `W_Y(x, y)`. -/
theorem variableChangeShift_a₃ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).a₃
      = Polynomial.evalEval x y W.toAffine.polynomialY := by
  rw [WeierstrassCurve.variableChange_a₃, WeierstrassCurve.Affine.evalEval_polynomialY]
  simp
  ring

/-- Translating the curve by `(x, y)` sends `a₄` to `-W_X(x, y)`. -/
theorem variableChangeShift_a₄ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).a₄
      = -Polynomial.evalEval x y W.toAffine.polynomialX := by
  rw [WeierstrassCurve.variableChange_a₄, WeierstrassCurve.Affine.evalEval_polynomialX]
  simp
  ring

/-- Translating the curve by `(x, y)` sends `a₆` to `-W(x, y)`. -/
theorem variableChangeShift_a₆ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).a₆
      = -Polynomial.evalEval x y W.toAffine.polynomial := by
  rw [WeierstrassCurve.variableChange_a₆, WeierstrassCurve.Affine.evalEval_polynomial]
  simp
  ring

/-- Translating the curve by `(x, y)` fixes the discriminant (the scaling unit is `1`). -/
theorem variableChangeShift_Δ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).Δ = W.Δ := by
  rw [WeierstrassCurve.variableChange_Δ]
  simp

/-- **The discriminant lies in the Jacobian ideal of the affine Weierstrass equation**,
at every pair of ring elements. -/
theorem Δ_mem_jacobianSpan {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    W.Δ ∈ Ideal.span {Polynomial.evalEval x y W.toAffine.polynomial,
      Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY} := by
  have h := Δ_eq_coeffCombination ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W)
  rw [variableChangeShift_Δ, variableChangeShift_a₃, variableChangeShift_a₄,
    variableChangeShift_a₆] at h
  rw [h]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_))
    (Ideal.mul_mem_left _ _ ?_)
  · exact Ideal.subset_span (by simp)
  · exact neg_mem (Ideal.subset_span (by simp))
  · exact neg_mem (Ideal.subset_span (by simp))

/-- **On an elliptic curve, the two partial derivatives generate the unit ideal at every
point of the curve.**  This is the Jacobian criterion in the form the chart argument needs,
and it is the ONLY place `E.IsElliptic` is consumed in item 7a. -/
theorem jacobianSpan_eq_top {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (x y : R) (h : W.toAffine.Equation x y) :
    Ideal.span {Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hmem := Δ_mem_jacobianSpan W x y
  rw [show Polynomial.evalEval x y W.toAffine.polynomial = 0 from h] at hmem
  have hsub : Ideal.span {(0 : R), Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY}
      ≤ Ideal.span {Polynomial.evalEval x y W.toAffine.polynomialX,
        Polynomial.evalEval x y W.toAffine.polynomialY} := by
    rw [Ideal.span_le]
    rintro z (rfl | hz)
    · exact Ideal.zero_mem _
    · exact Ideal.subset_span hz
  obtain ⟨u, hu⟩ := W.isUnit_Δ
  have hu' : (u : R) ∈ Ideal.span {Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY} := hu ▸ hsub hmem
  simpa using Ideal.mul_mem_left _ (↑u⁻¹) hu'

/-! ### Descending smoothness along a standard affine chart of `Proj` -/

/-- **The chart composite `Spec (A_g)₀ ⟶ Proj 𝒜 ⟶ Spec ℚ` is `Spec.map` of a ring map out
of `ℚ`** — so the chart obligation is purely RING-THEORETIC.

This is `Proj.awayι_toSpecZero` (in its `reassoc` form) followed by collapsing the two
`Spec.map`s.  The `show` is doing real work: `projToSpec` has source `proj E`, which is
`Proj (projGrading E)` only up to unfolding a `def`, and `rw`'s motive check runs at
`instances` transparency and rejects it.  `show` is checked at default transparency. -/
theorem awayι_projToSpec_eq_specMap (E : WeierstrassCurve ℚ)
    (g : MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal)
    (hg : g ∈ projGrading E 1) :
    Proj.awayι (projGrading E) g hg Nat.one_pos ≫ projToSpec E
      = Spec.map (CommRingCat.ofHom
          ((HomogeneousLocalization.fromZeroRingHom (projGrading E)
            (Submonoid.powers g)).comp (algebraMap ℚ (projGrading E 0)))) := by
  show Proj.awayι (projGrading E) g hg Nat.one_pos ≫
      (Proj.toSpecZero (projGrading E) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (projGrading E 0)))) = _
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- `SmoothOfRelativeDimension n` of a `Spec.map` is exactly the associated ring-hom
property, by `HasRingHomProperty.Spec_iff`. -/
theorem smoothOfRelativeDimension_specMap_of_locally {A : Type} [CommRing A] (φ : ℚ →+* A)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) φ) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom φ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact h

/-! ### Dehomogenisation: the standard affine chart of `Proj` of a polynomial quotient

This is the MISSING MATHLIB PIECE of item 7a, and nothing below is elliptic-curve
mathematics: it is the identification of the degree-zero part of an away-localisation of a
graded polynomial quotient with a concrete polynomial quotient.  Mathlib has
`HomogeneousLocalization.Away` and `Proj.awayι` but no such identification — a grep for
`dehomogeni` over the pin returns NOTHING, and neither `~/cs/FLT` nor this project has one.

The three declarations below cut the residual leaf into three independent pieces, each
stated exactly as `locally_isStandardSmooth_awayCoord` consumes it and each carrying its own
proof plan.  The assembly is written and PROVEN. -/

/-- The two affine coordinates on the standard chart `D₊(Xᵢ)` of `Proj ℚ[X, Y, Z]`, namely
the two homogeneous coordinates OTHER than `Xᵢ` — the chart coordinates being the ratios
`Xⱼ / Xᵢ` for `j ≠ i`. -/
abbrev ProjChartVar (i : Fin 3) : Type := {j : Fin 3 // j ≠ i}

/-- **Dehomogenisation at the `i`-th coordinate**: substitute `Xᵢ ↦ 1` and send each other
variable `Xⱼ` to the corresponding affine chart coordinate.

For a polynomial `p` homogeneous of degree `d` this is the numerator of `p / Xᵢ^d` written
in the chart coordinates, which is exactly what the chart identification needs. -/
noncomputable def dehomogenizeAt (R : Type) [CommRing R] (i : Fin 3) :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (ProjChartVar i) R :=
  MvPolynomial.aeval fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

/-- The dehomogenisation of the projective Weierstrass polynomial at the `i`-th chart.

For `i = 2` (the chart `Z ≠ 0`) this is literally the affine Weierstrass polynomial
`y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆`.  For `i = 0` and `i = 1` it is a different plane
cubic — the charts at `X ≠ 0` and `Y ≠ 0` — and in particular the chart `i = 1` is the one
containing the point at infinity `[0 : 1 : 0]`. -/
noncomputable def projChartPolynomial {R : Type} [CommRing R] (E : WeierstrassCurve R)
    (i : Fin 3) : MvPolynomial (ProjChartVar i) R :=
  dehomogenizeAt R i (polynomial E)

/-- The coordinate ring of the standard chart `D₊(Xᵢ)` of the projective Weierstrass model:
a plane curve in the two chart coordinates. -/
abbrev ProjChartRing {R : Type} [CommRing R] (E : WeierstrassCurve R) (i : Fin 3) : Type :=
  MvPolynomial (ProjChartVar i) R ⧸ Ideal.span {projChartPolynomial E i}

/-- The image of the `i`-th homogeneous coordinate in the homogeneous coordinate ring. -/
noncomputable abbrev projCoord {R : Type} [CommRing R] (E : WeierstrassCurve R) (i : Fin 3) :
    MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal E).toIdeal :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- **LEAF A — THE DEHOMOGENISATION ISOMORPHISM** (sorry node; a missing piece of MATHLIB,
not of this development).

  `(ℚ[X, Y, Z] ⧸ (W))_{(Xᵢ)}` in degree `0`  ≃  `ℚ[u, v] ⧸ (wᵢ)`,

compatibly with the two structure maps out of `ℚ`.  It is stated as a `RingEquiv` together
with the commuting triangle rather than as an `AlgEquiv` deliberately: the source carries an
`Algebra (projGrading E 0)` instance and the target an `Algebra ℚ` one, and forcing them
into a common `Algebra ℚ` structure invites exactly the "two defeq but never syntactically
equal instances" trap this development has been bitten by repeatedly.  The commuting
triangle is what the consumer actually needs, and it is instance-free.

## Proof plan

*Surjectivity is already in mathlib.*  `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`
says that if the graded ring is generated over its degree-zero part by homogeneous `vₗ` of
degrees `dvₗ`, then `𝒜_(f)` for `f` of degree `d` is generated as a `𝒜₀`-algebra by the
elements `(∏ vₗ^aₗ) / f^a` with `∑ aₗ dvₗ = a d` and `aₗ ≤ d`.  Here `d = 1` (that is what
`hcoord` supplies), the `vₗ` are the three coordinates `x₀, x₁, x₂` of degree `1`, so the
constraint `aₗ ≤ 1` forces each generator to be a product of a SUBSET of the coordinates
divided by `xᵢ^{card}` — i.e. a product of the three ratios `xⱼ / xᵢ`, one of which is `1`.
So the chart ring is generated over `ℚ` by the two ratios, which is exactly surjectivity of
the map `ℚ[u, v] → (B_{xᵢ})₀` sending `u, v` to the two ratios.

*The kernel is the one genuinely new argument.*  Let `q ∈ ℚ[u, v]` of degree `n` and let
`Q := Xᵢ^n · q(Xⱼ/Xᵢ, Xₖ/Xᵢ)` be its homogenisation, so the image of `q` is `Q̄ / xᵢ^n`.
That vanishes iff `Xᵢ^m · Q ∈ (W)` in `ℚ[X, Y, Z]` for some `m`.  Now `ℚ[X, Y, Z]` is a UFD,
`Xᵢ` is prime, and `Xᵢ ∤ W` for each of the three `i` — `W` contains the monomial `-X³` (so
`Y ∤ W` and `Z ∤ W`) and the monomial `Y²Z` (so `X ∤ W`).  Hence no prime factor of `W` is
associate to `Xᵢ`, and `W ∣ Xᵢ^m Q` forces `W ∣ Q`.  Dehomogenising, `wᵢ ∣ q`.  The reverse
inclusion is immediate since `W` maps to `0`.

Note this argument does NOT need `W` irreducible, only `Xᵢ ∤ W`, which is a monomial check.
The relevant mathlib entry points are `UniqueFactorizationMonoid` and
`MvPolynomial.prime_X` / `MvPolynomial.isDomain`.

This is the piece that ought to be upstreamed: stated for an arbitrary homogeneous ideal of
`R[X₀ .. Xₙ]` it is the standard affine chart of `Proj` of a projective scheme over `R`, and
its absence is what has kept every `Proj`-level smoothness argument out of reach. -/
theorem exists_projChartRingEquiv (E : WeierstrassCurve ℚ) (i : Fin 3)
    (hcoord : projCoord E i ∈ projGrading E 1) :
    ∃ e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) ≃+* ProjChartRing E i,
      (e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) →+* ProjChartRing E i).comp
          ((HomogeneousLocalization.fromZeroRingHom (projGrading E)
            (Submonoid.powers (projCoord E i))).comp (algebraMap ℚ (projGrading E 0)))
        = algebraMap ℚ (ProjChartRing E i) :=
  sorry

/-- **LEAF B — THE CHART JACOBIAN CRITERION** (sorry node): on each of the three charts the
two partial derivatives of the dehomogenised Weierstrass cubic generate the UNIT ideal of
the chart ring.  This is what makes the chart ring locally a hypersurface with an invertible
partial, and it is where `hjac` — hence `Δ` — is consumed.

## NOT VACUOUS, and true on all three charts

Checked with a Gröbner basis over `ℚ(a₁, …, a₆)`: for each of the three charts the ideal
generated by `wᵢ` and its two partials is `(1)`.  So the statement holds for all `i`, not
merely for the affine chart, and `Δ` is genuinely doing the work (over `ℚ[a₁, …, a₆]` the
ideal is proper — that is the content of `Δ_mem_jacobianSpan`).

## Proof plan — the same two ingredients on every chart, then three easy cases

*Ingredient 1 — dehomogenisation commutes with `∂`.*  For `j ≠ i`,
`pderiv j (dehomogenizeAt R i p) = dehomogenizeAt R i (pderiv j p)`, by
`MvPolynomial.induction_on`; the substitution `Xᵢ ↦ 1` is a constant in the `j`-th variable.
So the two chart partials are the dehomogenisations `pⱼ := dehom(W_{Xⱼ})`, `j ≠ i`, and
these are the dehomogenisations of mathlib's `polynomialX`, `polynomialY`, `polynomialZ`.

*Ingredient 2 — Euler.*  `WeierstrassCurve.Projective.polynomial_relation` is Euler's
theorem `3W = X·W_X + Y·W_Y + Z·W_Z`.  Dehomogenising at `i` and using `wᵢ = 0` in the chart
ring gives `pᵢ = -∑_{j ≠ i} uⱼ pⱼ`.  Hence in the chart ring
`span {pⱼ : j ≠ i} = span {p₀, p₁, p₂}`, and it suffices to show the LATTER is `⊤`.

*Chart `i = 2` (`Z ≠ 0`).*  `w₂` IS the affine Weierstrass polynomial, so `hjac` applies
directly at `S := ProjChartRing E 2` with `x, y` the images of the two chart coordinates:
the affine `Equation` holds because the chart ring is the quotient by `w₂`.

*Chart `i = 0` (`X ≠ 0`).*  Here `z := Z/X` is already a UNIT of the chart ring: `w₀ = 0`
reads `z · (v² + a₁v + a₃vz - a₂ - a₄z - a₆z²) = 1`.  So `x := 1/z` and `y := v/z` are
honest elements satisfying the affine equation, `hjac` applies at `S := ProjChartRing E 0`,
and the affine partials are `W_X(x,y) = x²·p₀` and `W_Y(x,y) = x²·p₁` (both partials are
homogeneous of degree `2`, and `x = X/Z` is a unit), so `span {p₀, p₁} = ⊤`.

*Chart `i = 1` (`Y ≠ 0`).*  This is the only chart containing the point at infinity, `z` is
NOT a unit there, and the argument needs one extra step.  Modulo `z` the chart relation
`w₁` becomes `-u³`, and `p₂ = dehom(W_Z) = 1 + a₁u + 2a₃z - a₂u² - 2a₄uz - 3a₆z²` has
constant term `1`, so `p₂` is a unit modulo `(z, u³)`: hence `span {p₂, z} = ⊤`.  On the
localisation away from `z` the previous argument applies verbatim (`x = u/z`, `y = 1/z`),
giving `zᵐ ∈ span {p₀, p₁}` for some `m`.  Since `span {p₂, z} = ⊤` implies
`span {p₂, zᵐ} = ⊤` (`IsCoprime.pow_right`), the two together give `1 ∈ span {p₀, p₁, p₂}`.

An explicit `Δᴺ = A·w₁ + B·p₀ + C·p₂` certificate from a Gröbner `lift` would also close
chart `i = 1` outright and is the fallback if the localisation bookkeeping proves painful;
the cofactors are large, which is why the structural argument is given first. -/
theorem projChart_jacobian_span_eq_top (E : WeierstrassCurve ℚ) [E.IsElliptic] (i : Fin 3)
    (hjac : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (x y : S),
      (E.map (algebraMap ℚ S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialY} = ⊤) :
    Ideal.span (Set.range fun j : ProjChartVar i =>
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
          (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i)) = ⊤ :=
  sorry

/-- **LEAF C — A PLANE CURVE IS STANDARD SMOOTH OF RELATIVE DIMENSION `1` WHERE A PARTIAL
DERIVATIVE IS INVERTIBLE** (sorry node; also a missing piece of MATHLIB rather than of this
development).

## Proof plan

`Algebra.PreSubmersivePresentation.naive` (`Mathlib/RingTheory/Extension/Presentation/
Submersive.lean`) builds a pre-submersive presentation of `R[Xₛ] ⧸ (vᵣ)` from an INJECTIVE
assignment `a : relations → variables`, with `jacobiMatrix_naive` computing the Jacobian
matrix as `(vⱼ).pderiv (a i)`.  So the whole of the construction is:

* variables `σ := ProjChartVar i ⊕ Unit`, i.e. `(u, v, t)` — three of them;
* relations `ι := Fin 2`, namely `wᵢ` and `t · ∂wᵢ/∂uⱼ - 1`;
* the assignment `a` sends the first relation to `uⱼ` and the second to `t`, which is
  injective;
* the Jacobian matrix is then LOWER TRIANGULAR,
  `[[∂wᵢ/∂uⱼ, 0], [t · ∂²wᵢ/∂uⱼ², ∂wᵢ/∂uⱼ]]`, with determinant `(∂wᵢ/∂uⱼ)²`, a unit in the
  quotient because the second relation says `t` inverts it;
* `dimension = card σ - card ι = 3 - 2 = 1`, using
  `Fintype.card (ProjChartVar i) = 2`.

The one piece of plumbing is the identification of the presented ring with `T`:

  `ℚ[u, v, t] ⧸ (wᵢ, t·∂wᵢ/∂uⱼ - 1)`  ≃  `(ℚ[u, v] ⧸ (wᵢ))_{∂wᵢ/∂uⱼ}`,

obtained from `MvPolynomial.optionEquivLeft` (or `sumAlgEquiv`) to split off `t`, then
`Ideal.polynomialQuotientEquivQuotientPolynomial` to push the quotient by `wᵢ` inside, then
`Localization.awayEquivAdjoin` — which is precisely
`Localization.Away r ≃ₐ[R] AdjoinRoot (C r * X - 1)` — to recognise the remaining quotient.
Finally `SubmersivePresentation.ofAlgEquiv` transports the presentation onto `T`, and
`IsLocalization.algEquiv` moves between `T` and `Localization.Away`. -/
theorem isStandardSmoothOfRelativeDimension_projChartAway (E : WeierstrassCurve ℚ) (i : Fin 3)
    (j : ProjChartVar i) (T : Type) [CommRing T] [Algebra (ProjChartRing E i) T]
    [IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
      (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i) T] :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((algebraMap (ProjChartRing E i) T).comp (algebraMap ℚ (ProjChartRing E i))) :=
  sorry

/-- **THE RESIDUAL LEAF OF ITEM 7a** — the degree-zero part of the localisation of the
homogeneous coordinate ring at a coordinate is locally standard smooth of relative
dimension `1` over `ℚ`.

Everything else in `smoothOfRelativeDimension_projToSpec` is now proven: the reduction to
the three coordinate charts, the identification of each chart composite with a `Spec.map`
(`awayι_projToSpec_eq_specMap`), the passage to the ring-hom property
(`smoothOfRelativeDimension_specMap_of_locally`), and the Jacobian criterion itself
(`jacobianSpan_eq_top`, supplied here as `hjac` and therefore genuinely consumed).

## THIS IS NOW PROVEN, from three named sub-leaves

The recipe below is written out and compiles; what remain are the three declarations in the
"Dehomogenisation" section above, each of which is a missing piece of MATHLIB rather than
any further elliptic-curve mathematics:

* `exists_projChartRingEquiv` (LEAF A) — the **dehomogenisation isomorphism**
  `(ℚ[X, Y, Z] ⧸ (W))_{(xᵢ)}` in degree `0` ≃ `ℚ[u, v] ⧸ (wᵢ)`, with the commuting triangle
  over `ℚ`.  Mathlib has `HomogeneousLocalization.Away` and `Proj.awayι` but NO
  identification of the degree-zero away-part with a concrete polynomial quotient — a grep
  for `dehomogeni` over the pin returns nothing, and neither does one over `~/cs/FLT`.
* `projChart_jacobian_span_eq_top` (LEAF B) — the two chart partials generate the unit
  ideal.  This is where `hjac`, and hence `Δ`, is consumed.
* `isStandardSmoothOfRelativeDimension_projChartAway` (LEAF C) — on each of the two
  localisations the `2 × 2` Jacobian of the relations `(wᵢ, t·∂wᵢ/∂u - 1)` in the generators
  `(u, v, t)` is triangular with determinant `(∂wᵢ/∂u)²`, a unit there, so the presentation
  is submersive of dimension `3 - 2 = 1`.

Each carries its own proof plan; see their docstrings.  A Gröbner computation confirms the
Jacobian ideal of each of the three charts is the unit ideal over `ℚ(a₁, …, a₆)` and is
PROPER over `ℚ[a₁, …, a₆]`, so no chart is exceptional and none of this is vacuous. -/
theorem locally_isStandardSmooth_awayCoord (E : WeierstrassCurve ℚ) [E.IsElliptic] (i : Fin 3)
    (hcoord : (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.X i))
      ∈ projGrading E 1)
    (hjac : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (x y : S),
      (E.map (algebraMap ℚ S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialY} = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      ((HomogeneousLocalization.fromZeroRingHom (projGrading E)
        (Submonoid.powers (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal
          (MvPolynomial.X i)))).comp (algebraMap ℚ (projGrading E 0))) := by
  classical
  obtain ⟨e, he⟩ := exists_projChartRingEquiv E i hcoord
  /- The chart ring is locally standard smooth of relative dimension `1`: the two partial
  derivatives generate the unit ideal (LEAF B, where `hjac` and hence `Δ` is consumed), and
  on each of the two localisations the curve is a hypersurface with an invertible partial
  (LEAF C). -/
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (ProjChartRing E i)) :=
    RingHom.locally_of_exists RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      (fun j : ProjChartVar i =>
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
          (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i))
      (projChart_jacobian_span_eq_top E i hjac)
      (fun j => Localization.Away
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
          (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i))
      (fun j => isStandardSmoothOfRelativeDimension_projChartAway E i j _)
  -- transport back along the dehomogenisation isomorphism (LEAF A)
  have htrans := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ e.symm hloc
  rw [← he, ← RingHom.comp_assoc] at htrans
  have hid : e.symm.toRingHom.comp
      (e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) →+* ProjChartRing E i)
      = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  rwa [hid, RingHom.id_comp] at htrans

/-- **The projective Weierstrass model is smooth of relative dimension
`1` over `Spec ℚ`** (sorry node — item 7a).

CORRECTION to the item-7 note in `exists_ellipticScheme_of_weierstrass`'s
docstring, and a sharpening rather than a restatement: the Jacobian
criterion is NOT absent from this pin.  `Mathlib/RingTheory/Smooth/Local.lean`
states it for LOCAL ALGEBRAS and `Smooth/StandardSmoothOfFree.lean` carries
`isUnit_jacobian_of_cotangentRestrict_bijective`.  What is missing is a
`Proj`-level formulation, so the task here is to DESCEND the local
criterion along the standard affine cover of `Proj` — `Proj.awayι` and
`Proj.affineOpenCover` — not to build a criterion from nothing.

On each affine chart the partial derivatives of the Weierstrass
polynomial generate the unit ideal exactly when `Δ` is invertible, which
is `E.IsElliptic`.  This is where ellipticity is genuinely used, and it
is the only place the discriminant enters.

## What is PROVEN here and what remains

The **reduction to the three coordinate charts is now proven**, and it is the whole
of the glue: `SmoothOfRelativeDimension n` has a `HasRingHomProperty`, hence is
Zariski-local at the SOURCE, so `IsZariskiLocalAtSource.of_openCover` reduces the
claim to the charts of any affine open cover.  The cover used is
`Proj.affineOpenCoverOfIrrelevantLESpan` at the three images `x₀, x₁, x₂` of the
coordinates — i.e. `D₊(X)`, `D₊(Y)`, `D₊(Z)` — rather than mathlib's default
`Proj.affineOpenCover`, whose index set is ALL homogeneous elements of positive
degree and which would therefore leave a strictly harder residual obligation.

Both side conditions of that cover are discharged:

* the degree condition `xᵢ ∈ projGrading E 1`, from
  `HomogeneousIdeal.mk_mem_quotientGrading` and `MvPolynomial.isHomogeneous_X`;
* the covering condition `(projGrading E)₊ ≤ span {x₀, x₁, x₂}`, via
  `HomogeneousIdeal.toIdeal_irrelevant_le` (which reduces it to homogeneous elements
  of positive degree) and `MvPolynomial.mem_ideal_span_X_image` (a polynomial lies in
  the ideal generated by the variables iff every monomial of its support involves
  one) — a homogeneous polynomial of degree `i > 0` has no constant monomial, so it
  qualifies.

**`hchart` is now proven too, modulo ONE named leaf.**  The chart obligation has been
reduced all the way to a ring-hom property, and the Jacobian criterion — the part that
actually uses `Δ` — is PROVEN:

* `awayι_projToSpec_eq_specMap` — by `Proj.awayι_toSpecZero`, the chart composite
  `Spec ((A_{xᵢ})₀) ⟶ Proj 𝒜 ⟶ Spec ℚ` IS `Spec.map` of the ring map `ℚ → (A_{xᵢ})₀`,
  so the residual obligation is purely RING-THEORETIC;
* `smoothOfRelativeDimension_specMap_of_locally` — for such a `Spec.map`,
  `SmoothOfRelativeDimension 1` is exactly `Locally (IsStandardSmoothOfRelativeDimension 1)`
  of that ring map, by `HasRingHomProperty.Spec_iff`;
* `jacobianSpan_eq_top` — **where `Δ` enters, and PROVEN over an ARBITRARY commutative
  ring**: at any point of the curve the two partial derivatives generate the unit ideal.
  It is handed to the leaf as the hypothesis `hjac`, so the discriminant is genuinely
  consumed rather than merely available.

The single remaining leaf is `locally_isStandardSmooth_awayCoord`, and what it needs is a
piece of MATHLIB infrastructure rather than any further elliptic-curve mathematics: the
dehomogenisation isomorphism between the degree-zero part of `(ℚ[X, Y, Z] ⧸ (W))_{xᵢ}` and
`ℚ[u, v] ⧸ (wᵢ)`.  Its own docstring states precisely what is missing and how the
remaining pieces fit.  Concretely, for `i = 2` the target ring is
`ℚ[x, y] ⧸ (y² + a₁xy + a₃y − x³ − a₂x² − a₄x − a₆)`. -/
theorem smoothOfRelativeDimension_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    SmoothOfRelativeDimension 1 (projToSpec E) := by
  classical
  -- the images of the three coordinates in the homogeneous coordinate ring
  set f : Fin 3 → (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) :=
    fun i => Ideal.Quotient.mk _ (MvPolynomial.X i)
  have f_deg : ∀ i, f i ∈ projGrading E 1 := fun i =>
    HomogeneousIdeal.mk_mem_quotientGrading
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℚ i))
  -- the three basic opens `D₊(xᵢ)` really do cover `Proj`
  have hf : (HomogeneousIdeal.irrelevant (projGrading E)).toIdeal
      ≤ Ideal.span (Set.range f) := by
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro i hi z hz
    obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp hz
    have hp' : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3))) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra hcon
      push Not at hcon
      have hm0 : m = 0 := by
        ext j; exact hcon j (Set.mem_univ j)
      have hdeg := ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
        (MvPolynomial.mem_support_iff.mp hm)
      rw [hm0] at hdeg
      simp at hdeg
      omega
    have hle : Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3)))
        ≤ Ideal.comap (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal)
          (Ideal.span (Set.range f)) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, -, rfl⟩
      exact Ideal.subset_span ⟨j, rfl⟩
    exact hle hp'
  /- **The Jacobian criterion**, PROVEN: at any point of any base change of `E`, the two
  partial derivatives generate the unit ideal.  This is where `E.IsElliptic` is consumed,
  and it is the mathematical input to the chart obligation below. -/
  have hjac : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (x y : S),
      (E.map (algebraMap ℚ S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialY} = ⊤ :=
    fun S _ _ x y h => jacobianSpan_eq_top _ x y h
  /- **The residual leaf**, now reduced to a purely ring-theoretic statement: each chart
  composite is `Spec.map` of a ring map out of `ℚ`, so smoothness of relative dimension `1`
  is the corresponding ring-hom property of that map. -/
  have hchart : ∀ i : Fin 3, SmoothOfRelativeDimension 1
      (Proj.awayι (projGrading E) (f i) (f_deg i) Nat.one_pos ≫ projToSpec E) := by
    intro i
    rw [awayι_projToSpec_eq_specMap E (f i) (f_deg i)]
    exact smoothOfRelativeDimension_specMap_of_locally _
      (locally_isStandardSmooth_awayCoord E i (f_deg i) hjac)
  exact IsZariskiLocalAtSource.of_openCover
    (Proj.affineOpenCoverOfIrrelevantLESpan (projGrading E) f (m := fun _ => 1) f_deg
      (fun _ => Nat.one_pos) hf).openCover hchart

/-- **The projective Weierstrass model is geometrically connected over
`Spec ℚ`** (sorry node — item 7b).

The base change to `ℚ̄` is `Proj` of `ℚ̄[X, Y, Z] ⧸ (W)`, and `W` is an
irreducible cubic there — a reducible plane cubic is singular at an
intersection point of two components, contradicting
`smoothOfRelativeDimension_projToSpec` — so the coordinate ring is a
domain, and `Proj` of a graded domain is irreducible, hence connected.
Nonemptiness, which `GeometricallyConnected` demands through
`ConnectedSpace`, is the point at infinity.

## What is PROVEN here and what remains

The **reduction to a single base change is now proven**.  `GeometricallyConnected` is
by definition `geometrically (ConnectedSpace ·)`, i.e. a condition on `X ×_ℚ Spec K`
for EVERY field `K` with a map `Spec K ⟶ Spec ℚ`; since the base is affine and
`(ConnectedSpace ·)` is closed under isomorphism,
`geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` turns that into: for
every field `K` with `[Algebra ℚ K]`, the pullback along
`Spec.map (algebraMap ℚ K)` is connected.

Note this is genuinely a statement about ALL field extensions `K/ℚ`, not only about
`ℚ̄` — the docstring above is right that `ℚ̄` is where the geometry happens, but the
quantifier is not eliminable at this stage, so the remaining leaves are stated over a
general `K`.  That costs nothing: the cubic is irreducible over every extension of a
field over which it is smooth, so the same argument serves.

**Three sorries remain**, and the assembly consumes exactly these:

* `hbc` — the base change of the projective model is the projective model of the
  base-changed curve, `Proj (ℚ[X,Y,Z]⧸(W)) ×_ℚ Spec K ≅ Proj (K[X,Y,Z]⧸(W_K))`.  This
  is `Proj` commuting with base change of the graded ring, plus
  `WeierstrassCurve.baseChange` commuting with `polynomial`.  It carries no
  ellipticity.
* `hne` — nonemptiness, which is the point at infinity `[0 : 1 : 0]`.
* `hpre` — preconnectedness, which is the real content: `W_K` is an irreducible cubic
  (a reducible plane cubic is singular at an intersection of two components,
  contradicting `smoothOfRelativeDimension_projToSpec` after base change), so the
  coordinate ring is a domain and `Proj` of a graded domain is irreducible.

Splitting `ConnectedSpace` into `Nonempty` and `PreconnectedSpace` is deliberate: the
two halves have nothing to do with each other, and bundling them would have forced a
successor to redo the trivial half. -/
theorem geometricallyConnected_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    GeometricallyConnected (projToSpec E) := by
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  /- The base change of the projective model along `ℚ → K` is the projective model of
  the base-changed Weierstrass curve. -/
  have hbc : Limits.pullback (projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ≅ proj (E.baseChange K) := sorry
  /- Nonemptiness: the point at infinity `[0 : 1 : 0]` is a `K`-rational point. -/
  haveI hne : Nonempty (proj (E.baseChange K)) := sorry
  /- Preconnectedness: `W_K` is an irreducible cubic, so `K[X, Y, Z] ⧸ (W_K)` is a
  graded domain and its `Proj` is irreducible. -/
  haveI hpre : PreconnectedSpace (proj (E.baseChange K)) := sorry
  have hconn : ConnectedSpace (proj (E.baseChange K)) := ⟨hne⟩
  exact ObjectProperty.prop_of_iso (fun X : Scheme.{0} => ConnectedSpace X) hbc.symm hconn

/-- **The abelian-scheme structure on the projective Weierstrass model**
(PROVEN) — the morphism-level bridge, applied.

Everything here is formal: `ofMorphisms` turns the data of `ProjGroupLaw`
into the functor-of-points presentation the moduli argument consumes, and
its two naturality fields cost the caller nothing.  `Smooth` is obtained
from `SmoothOfRelativeDimension 1` by `SmoothOfRelativeDimension.smooth`,
so smoothness is asserted once rather than twice. -/
noncomputable def ProjGroupLaw.toAbelianSchemeStruct {E : WeierstrassCurve ℚ}
    [E.IsElliptic] (gl : ProjGroupLaw E) : AbelianSchemeStruct (projToSpec E) :=
  haveI := smoothOfRelativeDimension_projToSpec E
  AbelianSchemeStruct.ofMorphisms (projToSpec E) gl.m gl.e gl.i gl.hm gl.he gl.hi
    gl.hassoc gl.hcomm gl.hunit gl.hinv (isProper_projToSpec E)
    (SmoothOfRelativeDimension.smooth 1 (projToSpec E))
    (geometricallyConnected_projToSpec E)

end EllipticScheme

/-- **The geometric fibre of the projective Weierstrass model IS `E(ℚ̄)`,
equivariantly** (sorry node — item 8).

This is the conjunct that pins the scheme as *this* curve rather than
some elliptic curve: without it the node would be satisfiable by any
elliptic curve over `ℚ` whatsoever, and the bridge in `X0.lean` would
then manufacture a `Γ₀(N)`-datum out of the wrong curve.

Two halves, and only the first is missing.  The FIELD-level half is
already at this pin: `WeierstrassCurve.Projective.toAffineAddEquiv` gives
`W.Point ≃+ W.toAffine.Point` over a field.  What has to be supplied is
the identification of `Spec ℚ̄`-points of `proj E` with the projective
points `(E⁄ℚ̄).Point` — that a morphism `Spec ℚ̄ ⟶ Proj 𝒜` over `Spec ℚ` is
a homogeneous prime together with a `ℚ̄`-valued homogeneous coordinate.
For a `Proj` over a FIELD that is the classical description, and it does
NOT require the general `Hom(T, Proj 𝒜)` that is missing at this pin —
which is precisely why item 8 is a leaf rather than another instance of
the structural obstruction.

Galois equivariance is then automatic: `galSMul` is precomposition with
`Spec σ` (`AbelianSchemeStruct.galSMul_def`), and under the coordinate
description that is the coordinatewise action of `σ` on `[x : y : z]`,
which is `WeierstrassCurve.Affine.Point.map`.

Additivity is where the group law re-enters: the `≃+` must intertwine
`gl.m` with the chord–tangent law on `(E⁄ℚ̄).Point`, which on `ℚ̄`-points
is the defining property of the addition formulas.  So this leaf consumes
`ProjGroupLaw`'s DATA — hence the `gl` argument — but nothing of its
axioms beyond what `toAbelianSchemeStruct` already packages.

It is stated OUTSIDE the `open WeierstrassCurve.Projective` section
above: that namespace carries its own scoped `⁄` notation for
`baseChange`, which would make `E⁄(AlgebraicClosure ℚ)` ambiguous against
the `WeierstrassCurve.Affine` one this file opens at the top.  Hence the
qualified `projToSpec`. -/
theorem exists_projGeomFibreAddEquiv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (gl : ProjGroupLaw E) :
    letI := gl.toAbelianSchemeStruct.addCommGroup
      (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
    ∃ eqv : (E⁄(AlgebraicClosure ℚ)).Point ≃+
        GeomFibrePt (_root_.WeierstrassCurve.Projective.projToSpec E)
          (𝟙 (Spec (CommRingCat.of ℚ))),
      ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
        eqv (WeierstrassCurve.Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
          = gl.toAbelianSchemeStruct.galSMul (𝟙 (Spec (CommRingCat.of ℚ))) σ (eqv x) :=
  sorry

/-- **The projective Weierstrass model of `E/ℚ` as an elliptic scheme
over `Spec ℚ`** (PROVEN from the five leaves above).

This is `Fermat.exists_ellipticScheme_of_weierstrass` verbatim, stated
here so that `X0.lean` can consume it in a PROOF BODY and therefore take
only a non-public `import` of this module — see the module docstring for
why that matters.  The statement is existential over the scheme, so it
mentions neither `proj` nor `projToSpec`, which is what makes that
possible. -/
theorem exists_ellipticScheme_of_projModel (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of ℚ)) (ab : AbelianSchemeStruct f),
      SmoothOfRelativeDimension 1 f ∧
        (letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
         ∃ e : (E⁄(AlgebraicClosure ℚ)).Point ≃+
             GeomFibrePt f (𝟙 (Spec (CommRingCat.of ℚ))),
           ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
             e (WeierstrassCurve.Affine.Point.map
                 (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
               = ab.galSMul (𝟙 (Spec (CommRingCat.of ℚ))) σ (e x)) := by
  obtain ⟨gl⟩ := nonempty_projGroupLaw E
  exact ⟨_root_.WeierstrassCurve.Projective.proj E,
    _root_.WeierstrassCurve.Projective.projToSpec E, gl.toAbelianSchemeStruct,
    smoothOfRelativeDimension_projToSpec E, exists_projGeomFibreAddEquiv E gl⟩

end Fermat

end

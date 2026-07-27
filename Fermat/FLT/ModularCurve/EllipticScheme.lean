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
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
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

The open leaves are `nonempty_projGroupLaw`, `isProper_projToSpec`,
`smoothOfRelativeDimension_projToSpec`,
`geometricallyConnected_projToSpec` and
`exists_projGeomFibreAddEquiv`; each carries its own docstring saying what
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

/-- **The projective Weierstrass model is proper over `Spec ℚ`** (sorry
node).

Mathlib already has `IsProper (Proj.toSpecZero 𝒜)` under
`[Algebra.FiniteType (𝒜 0) A]` (`ProjectiveSpectrum/Proper.lean:368`), and
the homogeneous coordinate ring `ℚ[X, Y, Z] ⧸ (W)` is visibly of finite
type over its degree-zero part.  What is NOT immediate is that this
transfers to `projToSpec`, which is `Proj.toSpecZero` FOLLOWED by
`Spec.map (algebraMap ℚ (projGrading E 0))`: properness is not stable
under postcomposition in general.  The missing input is that the second
map is an isomorphism, i.e. that the degree-zero part of the homogeneous
coordinate ring of the Weierstrass cubic is `ℚ` itself — provable at the
ring level, because the degree-`0` component of `ℚ[X, Y, Z]` is `ℚ` and
the homogeneous ideal `(W)` is generated in degree `3`, so it meets
degree `0` trivially. -/
theorem isProper_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    IsProper (projToSpec E) :=
  sorry

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
is the only place the discriminant enters. -/
theorem smoothOfRelativeDimension_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    SmoothOfRelativeDimension 1 (projToSpec E) :=
  sorry

/-- **The projective Weierstrass model is geometrically connected over
`Spec ℚ`** (sorry node — item 7b).

The base change to `ℚ̄` is `Proj` of `ℚ̄[X, Y, Z] ⧸ (W)`, and `W` is an
irreducible cubic there — a reducible plane cubic is singular at an
intersection point of two components, contradicting
`smoothOfRelativeDimension_projToSpec` — so the coordinate ring is a
domain, and `Proj` of a graded domain is irreducible, hence connected.
Nonemptiness, which `GeometricallyConnected` demands through
`ConnectedSpace`, is the point at infinity. -/
theorem geometricallyConnected_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    GeometricallyConnected (projToSpec E) :=
  sorry

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

/-! ### The affine chart, and the COORDINATE pinning of the model

The conjunct `exists_ellipticScheme_of_projModel` remembers about `E` is
a Galois-equivariant `≃+` on geometric points, and — as the docstring of
`Fermat.IsJMapOn.classify_jm` records — that relation is **not** known to
determine `E.j`.  `Fermat.IsWeierstrassModel` (`X0.lean`) is the stronger,
coordinate-level pinning that does determine it, and this subsection is
what supplies it: the projective model minus its point at infinity is
literally `Spec` of mathlib's affine coordinate ring.

**Why the statements below spell out `Spec (CommRingCat.of E.toAffine.`
`CoordinateRing)` instead of using `Fermat.weierstrassAffine`.**  That
abbreviation, and `IsWeierstrassModel` itself, live in `X0.lean`, which
*imports this module* — so naming them here would be circular.  They are
definitionally these terms, so `X0.lean` consumes the conclusion below by
`exact`, with no transport lemma and no duplication of content; only the
spelling is duplicated.  Moving them into a shared module was rejected
because `IsWeierstrassModel` occurs in the SIGNATURE of
`Fermat.IsJSection.jt_model`, which would force `X0.lean` to take a
`public import` of whatever module held it — and if that module were this
one, the reserved atom `over` would propagate through the whole
`MazurTorsion` cone, which is exactly what the module docstring above
explains this file exists to prevent. -/

/-- **The affine chart `Z ≠ 0` of the projective Weierstrass model is
`Spec` of the affine coordinate ring, and its complement is the unit
section** (sorry node — the coordinate half of item 8).

TRUE and classical, and it is the *definition* of the projective closure
read backwards: `Proj (R[X,Y,Z]/(F))` is covered by the three basic opens
`D₊(X)`, `D₊(Y)`, `D₊(Z)`, the last of which is
`Spec ((R[X,Y,Z]/(F))_(Z))`, the degree-zero part of the localization at
`Z`.  Substituting `x = X/Z`, `y = Y/Z` identifies that ring with
`R[x,y]/(y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆)`, which is mathlib's
`WeierstrassCurve.Affine.CoordinateRing`.  The complement of `D₊(Z)` is
`V₊(Z)`, which for the Weierstrass cubic is the single point `[0 : 1 : 0]`
— substituting `Z = 0` into `F` leaves `-X³`, so `X = 0` too — and that
point is the unit `gl.e` of the group law.

WHAT IT NEEDS, as three separately checkable pieces:

* `Proj.awayIso` / the basic-open cover of `Proj` at this pin — the
  identification of `D₊(Z) ⊆ Proj 𝒜` with `Spec (𝒜_(Z))`, and that its
  inclusion is an open immersion over `Spec 𝒜₀`.
* The RING isomorphism `(R[X,Y,Z]/(F))_(Z) ≅ R[x,y]/(f)` — pure
  commutative algebra, the dehomogenisation map, and the only place where
  the shape of the Weierstrass polynomial is used.
* `V₊(Z) = {[0 : 1 : 0]}` as a set, and that this point is the range of
  `gl.e`.  The second half is the only place `gl` is consumed, and it is
  what makes the statement about the group law rather than about the bare
  scheme: `IsWeierstrassModel` pins the removed point to BE the origin,
  which is what lets `WeierstrassCurve.variableChange_j` be applied
  without a translation argument downstream.

THE CHECK THAT WOULD REFUTE THE "MISSING" HALF: a declaration in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` giving `D₊(f) ≅ Spec` of
the degree-zero localization together with the open immersion into
`Proj`, and one identifying the degree-zero part of a localization of a
graded quotient ring.

NOT VACUOUS: `IsOpenImmersion` alone would be satisfiable by the empty
scheme were the coordinate ring trivial, but `range_eq` forces the range
to be the *whole* complement of a point of an irreducible curve, so the
chart is genuinely dense. -/
theorem exists_affineChart_projModel (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (gl : ProjGroupLaw E) :
    ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶
        _root_.WeierstrassCurve.Projective.proj E,
      IsOpenImmersion ι ∧
        ι ≫ _root_.WeierstrassCurve.Projective.projToSpec E =
          Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)) ∧
        Set.range ι.base =
          (Set.range (gl.toAbelianSchemeStruct.zero
            (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ :=
  sorry

/-- **The projective Weierstrass model as an elliptic scheme, remembering
the COORDINATES as well as the geometric fibre** (PROVEN from the six
leaves above).

This is `exists_ellipticScheme_of_projModel` with one extra conjunct: the
affine Weierstrass curve of `E` sits inside the total space as the
complement of the zero section.  That conjunct is `Fermat.`
`IsWeierstrassModel` with its two definitions unfolded — see the
subsection docstring for why it is spelled out rather than named — and it
is what `Fermat.exists_weierstrassModel_gamma0Datum` in `X0.lean`
consumes to pin `d.ab` to `E` by coordinates rather than by the
Galois-equivariant `≃+`.

The equivariant conjunct is KEPT even though the model conjunct is
strictly more informative about which curve this is: the assembly in
`X0.lean` transports the ORDER and the STABILITY of the generator `g`
along that `≃+` in order to feed
`exists_cyclicSubgroupOfOrder_of_galoisStable`, and the coordinate
pinning says nothing about geometric points. So both are load-bearing,
for different halves of the datum. -/
theorem exists_ellipticScheme_isWeierstrassModel_of_projModel
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of ℚ)) (ab : AbelianSchemeStruct f),
      SmoothOfRelativeDimension 1 f ∧
        (∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ A,
          IsOpenImmersion ι ∧
            ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)) ∧
            Set.range ι.base =
              (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ) ∧
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
    smoothOfRelativeDimension_projToSpec E, exists_affineChart_projModel E gl,
    exists_projGeomFibreAddEquiv E gl⟩

end Fermat

end

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

The open leaves are `exists_projAdd`, `isProper_projToSpec`,
`smoothOfRelativeDimension_projToSpec`,
`geometricallyConnected_projToSpec` and
`exists_projGroupLaw_geomFibreAddEquiv`; each carries its own docstring
saying what is missing and where the classical argument is.

**Item 8 was restated on 2026-07-27** and its leaf is now
`exists_projGroupLaw_geomFibreAddEquiv`, which binds the group law
EXISTENTIALLY.  `exists_projGeomFibreAddEquiv` survives under its own name
as a PROVEN consequence, stated about the concrete `projGroupLaw E`.  The
old form quantified over an ARBITRARY `ProjGroupLaw`, which pins nothing
about `m`, and was therefore provable only through the rigidity theorem;
the audit is on `exists_projGroupLaw_geomFibreAddEquiv`.  That leaf also
subsumes `exists_projAdd`, and the two cuts should eventually be merged
— see the "Relation to `exists_projAdd`" section of its docstring.

`nonempty_projGroupLaw` is PROVEN: two of the three data fields of a
`ProjGroupLaw` are constructed outright in `ProjectiveModel.lean`
(`projNeg`, the Weierstrass involution through `Proj.map`; `projInfty`,
the point at infinity through `Proj.fromOfGlobalSections`), and all three
"lies over the base" fields are free over this base
(`hom_ext_spec_rat`).  What remains is `exists_projAdd`: the group law
`m` itself, together with the four group axioms.

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

/-- **Any two morphisms of schemes to `Spec ℚ` are equal** (PROVEN).

`Hom_Sch(X, Spec R) ≃ Hom_Ring(R, Γ(X, ⊤))` (the `Γ ⊣ Spec` adjunction,
here through `AlgebraicGeometry.ext_to_Spec`), and `ℚ →+* A` is a
subsingleton (`Rat.subsingleton_ringHom`: `ℤ → ℚ` is a ring epimorphism, so
a ring map out of `ℚ` is forced — `n ↦ n · 1` and `1/n ↦ (n · 1)⁻¹`).

**Consequence for this file, and it removes three obligations.**  Every
"lies over the base" field of `ProjGroupLaw` — `hm`, `he`, `hi` — is an
equation between two morphisms whose TARGET is `Spec ℚ`, so all three hold
automatically and carry no geometric content whatsoever.  Over a general
base they are real conditions; over `Spec ℚ` they are not, because a
scheme admits at most one morphism to `Spec ℚ` and hence every morphism
between `ℚ`-schemes is automatically a `ℚ`-morphism.  This is what lets
`nonempty_projGroupLaw` below be reduced to the group axioms alone.

`X0.lean` records the same fact downstream as `subsingleton_hom_specQ`;
the two are deliberately differently named, because `X0.lean` imports this
module and a shared name would be a duplicate declaration there.  They
should be merged at integration, keeping this one (it is upstream). -/
theorem hom_ext_spec_rat {X : Scheme.{0}} (f g : X ⟶ Spec (CommRingCat.of ℚ)) : f = g := by
  apply AlgebraicGeometry.ext_to_Spec
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

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

/-- **The chord–tangent addition on the projective Weierstrass model**
(sorry node — what is left of items 5+6 once the inversion `i`, the unit
section `e` and the three structure-morphism compatibilities have been
discharged; see `nonempty_projGroupLaw` for the assembly).

TRUE and classical.  The addition FORMULAS are already at this pin over
an arbitrary `[CommRing R]` —
`WeierstrassCurve.Projective.addXYZ`/`addX`/`addY`/`addZ` in
`EllipticCurve/Projective/Formula.lean` — so nothing has to be invented;
what is missing is the *gluing*.  The formulas degenerate on the locus
where the naive chart fails, so `m` is obtained from the standard
three-chart cover of `A ×_ℚ A` together with agreement on the overlaps.
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
and are the easy half.

## What this leaf does NOT have to do any more, and why

Five obligations were removed from the original single leaf, and the
statement below is the residue.  **This is a strengthening, not a
weakening**: `hunit` and `hinv` are now demanded against the specific,
named `projInfty E` and `projNeg E` rather than against an existentially
quantified `e` and `i`, so a witness for this leaf is strictly harder to
produce than a witness for the old one, and the old statement follows from
it (see `nonempty_projGroupLaw`).

* `i` is now **constructed**, as
  `WeierstrassCurve.Projective.projNeg E` — the substitution
  `Y ↦ −Y − a₁X − a₃Z` is a degree-preserving ring automorphism of
  `ℚ[X, Y, Z]` fixing the Weierstrass polynomial on the nose, so it
  descends to a graded automorphism of the homogeneous coordinate ring and
  `Proj` is a functor of that (`AlgebraicGeometry.Proj.map`).  No gluing,
  no charts.  It is an involution: `projNeg_comp_projNeg`.
* `e` is now **constructed**, as
  `WeierstrassCurve.Projective.projInfty E` — the point at infinity
  `[0 : 1 : 0]`, obtained from `Proj.fromOfGlobalSections`, whose
  hypothesis is exactly that the chosen coordinates have no common zero.
  Again no gluing.
* `hm`, `he`, `hi` are **free over this base** (`hom_ext_spec_rat`): each
  is an equation between morphisms whose target is `Spec ℚ`, and a scheme
  has at most one morphism to `Spec ℚ`.

## ROUTE AUDIT (2026-07-27), stating the checks that would refute it

The `m`-half is gated on scheme-theoretic infrastructure that is genuinely
absent, and the axis searched was *how to write a morphism into a `Proj`*:

1. There is no functor-of-points description of `Hom(T, Proj 𝒜)` at this
   pin — `ProjectiveSpectrum/Functor.lean` gives only functoriality
   `Proj ℬ ⟶ Proj 𝒜` in the graded ring, which is exactly the route that
   *did* work for `projNeg` and does **not** work for `m` (the group law
   is not induced by a graded ring map, since its source is a product).
   *Refuting check*: grep `ProjectiveSpectrum/` for a `Proj`-valued
   universal property, or for `Scheme.OpenCover.glueMorphisms` applied to
   a `Proj` target.
2. So `m` has to be glued out of an open cover of `A ×_ℚ A`, and each
   piece is an affine morphism written from the `addXYZ` formulas.
   *Refuting check*: find a chart on which the naive formula is defined
   everywhere — there is none, which is precisely why `addXYZ` has
   branches.
3. `hassoc` additionally needs the density statement "two morphisms out
   of a reduced finite-type `ℚ`-scheme into `proj E` agreeing on
   `ℚ̄`-points are equal".  *Refuting check*: grep mathlib for a scheme
   morphism ext lemma over closed points of a Jacobson base.

The axis NOT searched: a rigidity/theorem-of-the-cube route that would
derive `hassoc` from `hcomm`, `hunit`, `hinv` and properness without
touching points.  That would be a genuinely different cut and it is where
the next owner should start if the gluing proves too expensive. -/
theorem exists_projAdd (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E,
      AbelianSchemeStruct.triAddLeft (projToSpec E) m (hom_ext_spec_rat _ _) =
            AbelianSchemeStruct.triAddRight (projToSpec E) m (hom_ext_spec_rat _ _) ∧
          Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
              (Limits.pullback.fst (projToSpec E) (projToSpec E))
              Limits.pullback.condition.symm ≫ m = m ∧
        Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E) ∧
          Limits.pullback.lift (projNeg E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E :=
  sorry

/-- **The chord–tangent law on the projective Weierstrass model, as
morphisms of schemes** (PROVEN from `exists_projAdd`) — items 5+6 of
the routable specification in `exists_ellipticScheme_of_weierstrass`'s
docstring.

The three data fields are supplied as follows.  `m` comes from
`exists_projAdd`, which is where all the remaining gluing work lives.
`e` and `i` are CONSTRUCTED rather than assumed: `projInfty E`, the point
at infinity `[0 : 1 : 0]` via `Proj.fromOfGlobalSections`, and
`projNeg E`, `Proj` of the graded automorphism `Y ↦ −Y − a₁X − a₃Z` of
the homogeneous coordinate ring.  The three compatibility fields `hm`,
`he`, `hi` are `hom_ext_spec_rat`, i.e. free over the base `Spec ℚ`. -/
theorem nonempty_projGroupLaw (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Nonempty (ProjGroupLaw E) := by
  obtain ⟨m, hassoc, hcomm, hunit, hinv⟩ := exists_projAdd E
  exact ⟨{ m := m
           e := projInfty E
           i := projNeg E
           hm := hom_ext_spec_rat _ _
           he := hom_ext_spec_rat _ _
           hi := hom_ext_spec_rat _ _
           hassoc := hassoc
           hcomm := hcomm
           hunit := hunit
           hinv := hinv }⟩

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

/-! ### Compatibility of the morphism-level law with the `RelPoint` presentation

**This is the reusable payoff of stating the group law as morphisms.**
Every existing consumer in `X0.lean` and the moduli argument downstream is
written against `RelPoint`, not against `m`, `e`, `i`; so a producer that
hands over a `ProjGroupLaw` needs to know what the resulting `+`, `0` and
`-` on `RelPoint (projToSpec E) g` actually *are*.

All four lemmas below are definitional — `ofMorphisms` sets its `add`,
`zero` and `neg` fields to `addOfMor`, `zeroOfMor` and `negOfMor`, whose
values are `relPair x y ≫ m`, `g ≫ e` and `x.1 ≫ i` — but they are worth
stating, because after `toAbelianSchemeStruct` the underlying morphisms are
buried three definitions deep and no consumer should have to unfold
`ofMorphisms` by hand to reach them.  With these in place a `T`-point
computation on the projective model is a computation with `gl.m`, `gl.e`
and `gl.i` in the category of schemes, which is the only form in which the
chord–tangent formulas can be applied. -/

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] (gl : ProjGroupLaw E)
  {T : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of ℚ)}

/-- **Addition of relative points on the projective model is `gl.m` applied
to the paired point** (PROVEN, definitional). -/
@[simp] theorem ProjGroupLaw.toAbelianSchemeStruct_add_val
    (x y : RelPoint (projToSpec E) g) :
    (gl.toAbelianSchemeStruct.add x y).1 =
      AbelianSchemeStruct.relPair x y ≫ gl.m := rfl

/-- **The zero relative point on the projective model is the base point
composed with the unit section `gl.e`** (PROVEN, definitional). -/
@[simp] theorem ProjGroupLaw.toAbelianSchemeStruct_zero_val :
    (gl.toAbelianSchemeStruct.zero g).1 = g ≫ gl.e := rfl

/-- **Negation of relative points on the projective model is postcomposition
with `gl.i`** (PROVEN, definitional). -/
@[simp] theorem ProjGroupLaw.toAbelianSchemeStruct_neg_val
    (x : RelPoint (projToSpec E) g) :
    (gl.toAbelianSchemeStruct.neg x).1 = x.1 ≫ gl.i := rfl

/-- **The `AddCommGroup` structure on relative points, computed from the
morphisms** (PROVEN, definitional).

This is the form a consumer actually meets: `X0.lean` and the moduli
argument use the `+` coming from
`AbelianSchemeStruct.addCommGroup`, not the bare `add` field. -/
theorem ProjGroupLaw.addCommGroup_add_val (x y : RelPoint (projToSpec E) g) :
    letI := gl.toAbelianSchemeStruct.addCommGroup g
    (x + y).1 = AbelianSchemeStruct.relPair x y ≫ gl.m := rfl

/-- **The zero of the `AddCommGroup` on relative points is the unit
section** (PROVEN, definitional). -/
theorem ProjGroupLaw.addCommGroup_zero_val :
    letI := gl.toAbelianSchemeStruct.addCommGroup g
    (0 : RelPoint (projToSpec E) g).1 = g ≫ gl.e := rfl

/-- **Negation in the `AddCommGroup` on relative points is postcomposition
with `gl.i`** (PROVEN, definitional). -/
theorem ProjGroupLaw.addCommGroup_neg_val (x : RelPoint (projToSpec E) g) :
    letI := gl.toAbelianSchemeStruct.addCommGroup g
    (-x).1 = x.1 ≫ gl.i := rfl

end EllipticScheme

/-- **The projective Weierstrass model carries a group law whose geometric
fibre IS `E(ℚ̄)`, equivariantly** (sorry node — item 8, RESTATED
2026-07-27; see the FALSITY-OF-CUT AUDIT below for what it replaces).

This is the conjunct that pins the scheme as *this* curve rather than
some elliptic curve: without it the node would be satisfiable by any
elliptic curve over `ℚ` whatsoever, and the bridge in `X0.lean` would
then manufacture a `Γ₀(N)`-datum out of the wrong curve.

## FALSITY-OF-CUT AUDIT (2026-07-27) — why the `gl` is now BOUND HERE

The previous statement of item 8 was

    theorem exists_projGeomFibreAddEquiv (E) [E.IsElliptic]
        (gl : ProjGroupLaw E) : … the same conclusion …

i.e. it quantified over an **arbitrary** `gl : ProjGroupLaw E`, and its
docstring justified the additivity clause by saying that intertwining
`gl.m` with the chord–tangent law "on `ℚ̄`-points is the defining property
of the addition formulas".  **That justification does not hold**, and this
is a cut-level defect rather than a hard sub-problem:

* `ProjGroupLaw` (above) pins **nothing** about `m` beyond the four
  abelian-group axioms `hassoc`/`hcomm`/`hunit`/`hinv`.  `m`, `e` and `i`
  are free data.  So there is **no chord–tangent formula anywhere in the
  hypotheses to intertwine with** — the phrase "the defining property of
  the addition formulas" refers to something the statement never assumed.
* Proving the old statement for an arbitrary `gl` is therefore exactly the
  **rigidity theorem**: a group-scheme structure on a genus-`1` curve is
  determined by its identity section, so any second group law satisfies
  `x ⊕ y = x + y - e`.  That is in neither mathlib nor `~/cs/FLT`, and it
  is far heavier than the fibre comparison item 8 was cut as.

**The old statement was TRUE, not false** — `e` is `ℚ`-rational, so
translation by `-e` is a Galois-equivariant group isomorphism and the
equivalence exists for every `gl`.  It was true and *hard*, which is the
worst shape for a leaf: nothing about it announces that a major absent
theorem sits inside it.  So it is restated, not refuted.

**The repair**: bind `gl` **existentially** here.  A witness now
constructs `m` and the coordinate identification *together*, which is how
the classical argument actually goes and which needs no rigidity: `m` is
glued from `WeierstrassCurve.Projective.addXYZ`, the identification is the
coordinate description of `Spec ℚ̄`-points, and additivity is then a direct
computation with those same formulas rather than a comparison of two
unrelated group laws.  `projGroupLaw` below names the witness, and
`exists_projGeomFibreAddEquiv` — item 8 under its original name — is
PROVEN from this leaf and states the conclusion about that concrete
group law.

## What a witness has to supply

The FIELD-level half is already at this pin:
`WeierstrassCurve.Projective.toAffineAddEquiv` gives
`W.Point ≃+ W.toAffine.Point` over a field.  What has to be supplied is
the identification of `Spec ℚ̄`-points of `proj E` with the projective
points `(E⁄ℚ̄).Point` — that a morphism `Spec ℚ̄ ⟶ Proj 𝒜` over `Spec ℚ` is
a homogeneous prime together with a `ℚ̄`-valued homogeneous coordinate.
For a `Proj` over a FIELD that is the classical description, and it does
NOT require the general `Hom(T, Proj 𝒜)` that is missing at this pin —
which is precisely why item 8 is a leaf rather than another instance of
the structural obstruction.

Galois equivariance is then automatic: `galSMul` is precomposition with
`Spec σ` (`AbelianSchemeStruct.galSMul_def`, which is `rfl` and in
particular does **not** depend on the `AbelianSchemeStruct`), and under
the coordinate description that is the coordinatewise action of `σ` on
`[x : y : z]`, which is `WeierstrassCurve.Affine.Point.map`.

## Relation to `exists_projAdd`, and the `_gl₀` argument

This leaf **subsumes `exists_projAdd`**: a witness supplies `m` together
with `hassoc`, and `hassoc` is the expensive half of that leaf (the
`ProjGroupLaw` axioms transport along the identification from the group
axioms of `E(ℚ̄)`, which is the density route `exists_projAdd`'s own
docstring names as cheapest).  The intended end state is therefore that
`exists_projAdd` gains a chord–tangent clause and **this** leaf is proven
from it, at which point the two cuts become one.

Until that reconciliation, `_gl₀` is a deliberate **CONE ANCHOR** and
nothing else: it is underscore-prefixed because the intended proof does
not use it, and it exists so that `nonempty_projGroupLaw` — and through
it `exists_projAdd`, live work at the time of writing — stays inside the
used-constant cone of the root theorem instead of becoming free-floating
the moment this restatement lands.  It costs consumers nothing
(`nonempty_projGroupLaw` discharges it) and weakens the leaf only by a
hypothesis that is itself available.  **Delete the argument** once
`exists_projAdd` is reconciled as above.

It is stated OUTSIDE the `open WeierstrassCurve.Projective` section
above: that namespace carries its own scoped `⁄` notation for
`baseChange`, which would make `E⁄(AlgebraicClosure ℚ)` ambiguous against
the `WeierstrassCurve.Affine` one this file opens at the top.  Hence the
qualified `projToSpec`. -/
theorem exists_projGroupLaw_geomFibreAddEquiv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (_gl₀ : ProjGroupLaw E) :
    ∃ gl : ProjGroupLaw E,
      (letI := gl.toAbelianSchemeStruct.addCommGroup
        (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
       ∃ eqv : (E⁄(AlgebraicClosure ℚ)).Point ≃+
           GeomFibrePt (_root_.WeierstrassCurve.Projective.projToSpec E)
             (𝟙 (Spec (CommRingCat.of ℚ))),
         ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
           eqv (WeierstrassCurve.Affine.Point.map
               (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
             = gl.toAbelianSchemeStruct.galSMul
                 (𝟙 (Spec (CommRingCat.of ℚ))) σ (eqv x)) :=
  sorry

/-- **The chord–tangent group law on the projective Weierstrass model, as
a NAMED morphism-level datum** (PROVEN — a definition).

This is the concrete group law that item 8 is stated about.  It exists
because a statement of item 8 over an *arbitrary* `ProjGroupLaw` is
provable only through the rigidity theorem — see the audit on
`exists_projGroupLaw_geomFibreAddEquiv`.

`Classical.choose` is the right constructor here and not a dodge: the
witness is pinned by the accompanying specification
`exists_projGeomFibreAddEquiv` below, which is a *theorem* about
`projGroupLaw E` and not a second `sorry`, so every consumer meets the
chord–tangent content rather than an opaque choice.  Consumers should use
`exists_projGeomFibreAddEquiv`; the underlying `Exists.choose` is not
intended to be unfolded. -/
noncomputable def projGroupLaw (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ProjGroupLaw E :=
  (exists_projGroupLaw_geomFibreAddEquiv E (nonempty_projGroupLaw E).some).choose

/-- **The geometric fibre of the projective Weierstrass model IS `E(ℚ̄)`,
equivariantly** — item 8, now PROVEN, and stated about the CONCRETE group
law `projGroupLaw E`.

The statement is the original one with the universally quantified
`gl : ProjGroupLaw E` replaced by `projGroupLaw E`; that replacement is
the whole content of the 2026-07-27 repair, and the reason for it is the
FALSITY-OF-CUT AUDIT on `exists_projGroupLaw_geomFibreAddEquiv`.  It is
the defining specification of `projGroupLaw`, so it is the form every
consumer should quote. -/
theorem exists_projGeomFibreAddEquiv (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    letI := (projGroupLaw E).toAbelianSchemeStruct.addCommGroup
      (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
    ∃ eqv : (E⁄(AlgebraicClosure ℚ)).Point ≃+
        GeomFibrePt (_root_.WeierstrassCurve.Projective.projToSpec E)
          (𝟙 (Spec (CommRingCat.of ℚ))),
      ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
        eqv (WeierstrassCurve.Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
          = (projGroupLaw E).toAbelianSchemeStruct.galSMul
              (𝟙 (Spec (CommRingCat.of ℚ))) σ (eqv x) :=
  (exists_projGroupLaw_geomFibreAddEquiv E (nonempty_projGroupLaw E).some).choose_spec

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
               = ab.galSMul (𝟙 (Spec (CommRingCat.of ℚ))) σ (e x)) :=
  ⟨_root_.WeierstrassCurve.Projective.proj E,
    _root_.WeierstrassCurve.Projective.projToSpec E,
    (projGroupLaw E).toAbelianSchemeStruct,
    smoothOfRelativeDimension_projToSpec E, exists_projGeomFibreAddEquiv E⟩

end Fermat

end

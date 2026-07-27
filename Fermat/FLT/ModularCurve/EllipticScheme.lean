/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveModel
public import Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced
public import Fermat.FLT.EllipticCurve.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.Prime.Lemmas
public import Mathlib.RingTheory.Prime
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveAddition
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.ResidueField

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

`isProper_projToSpec` is PROVEN, and so is
`smoothOfRelativeDimension_projToSpec` apart from ONE named leaf: its `hchart`
step is now fully reduced, and the Jacobian criterion it rests on
(`jacobianSpan_eq_top`, over an arbitrary commutative ring) is proven here.

`projMul_assoc` is PROVEN too, by the density route: mathlib's
`ext_of_fromSpecResidueField_eq` reduces it to associativity at residue fields,
and `exists_projPtAddEquiv_algClosed` — the ALGEBRAIC
`K`-point dictionary (an abelian-group structure on `K`-points with `projInfty`
as zero and `projNeg` as negation, 2-divisible, and with every scheme morphism
acting affinely) — is **PROVEN as of 2026-07-27** over
`ProjCoords.specPointEquiv`, the dictionary as DATA (see the section "THE
`Spec K`-POINT DICTIONARY, AS DATA").  What is left of it is its four clauses,
as four named leaves: `specPointEquiv_comp_projInfty_eq_zero`,
`specPointEquiv_comp_projNeg`, `exists_add_self_affinePoint_of_isAlgClosed`
and `exists_addMonoidHom_specPointEquiv_projMulPt`.
`projMul_assoc_pt_algClosed` was the leaf here until 2026-07-27
and is now PROVEN from the dictionary together with the pure group-theoretic
`commLoop_eq_add_of_addHom`; the old Milne I.2.5 / rigidity plan was CIRCULAR
(it needs the group law on the target as a morphism) and the route taken
replaces it by Silverman *AEC* III.4.7, which needs only the SET-level group
`E(K)` that mathlib already has.  `projMul_assoc_pt` — the same statement over
an arbitrary field — is PROVEN by descent along `Spec K̄ ⟶ Spec K`.
`geometricallyReduced_projToSpec` is PROVEN as well: the general
`Smooth → GeometricallyReduced` gap it named was a MATHLIB gap and not
elliptic-curve mathematics, and it has been filled in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`, which is
**sorry-free as of 2026-07-27**: its former leaf
`Algebra.Smooth.isReduced_of_isField` (*a smooth algebra over a field is
reduced*) is PROVEN.  **That relocation forced a
reordering**: `geometricallyReduced_projToSpec`, `isReduced_triProd_proj`,
`projMul_assoc`, `exists_projAdd` and `nonempty_projGroupLaw` now sit AFTER
`smoothOfRelativeDimension_projToSpec`, since the first of them consumes it;
their text is otherwise unchanged.

`exists_affineChart_projModel` is PROVEN as of 2026-07-27 as well, over
`exists_affineChart_projInfty` and `exists_translation_toZero`, and its cut
carries a correction worth reading at the leaf: the old plan's third bullet —
"the complement of `D₊(Z)` is the range of `gl.e`" — is false as an
identification of POINTS, because `ProjGroupLaw` pins nothing about its unit
section and every translate of the chord–tangent law is again a
`ProjGroupLaw`.  The statement is still true, by translation, which is exactly
the shape of the FALSITY-OF-CUT AUDIT on
`exists_projGroupLaw_geomFibreAddEquiv`.  Its two residual leaves are the
GROUP-LAW-FREE halves of the chart: a commutative-algebra one
(`ProjChartRing E 2 ≃+* E.toAffine.CoordinateRing`) and a topological one
(`V₊(Z̄)` is the image of `projInfty`).

The open leaves of this FILE are therefore THIRTEEN, and this list was
REGENERATED at integration (2026-07-27) from the merged source rather than taken
from any side of the merges — several branches each carried a list that was
correct on its own branch and wrong once the others landed:

* **`exists_projMul` is PROVEN as of 2026-07-27** and is no longer a leaf.  It
  was decomposed over a new interface, `ProjCoords` — three sections of
  `Γ(X, ⊤)` satisfying the Weierstrass equation and generating the unit ideal,
  i.e. a TRIVIALISED `Proj`-coordinate datum — together with
  `ProjCoords.toHom`, the morphism `X ⟶ proj E` it determines through
  `Proj.fromOfGlobalSections`.  Of its five successor leaves, two are now
  CLOSED and one has been cut in two (2026-07-27):
  `ProjCoords.toHom_eq_of_addXYZ_not_span` is **PROVEN** over the new ring-level
  `ProjCoords.exists_units_smul_of_addXYZ_not_span`;
  `WeierstrassCurve.Projective.equation_addXYZ` is PROVEN in
  `Fermat/FLT/Mathlib/.../ProjectiveAddition.lean`;
  `ProjCoords.toHom_smul` is **PROVEN as a reduction** to
  `ProjCoords.toBasicOpenOfGlobalSections_eq_of_gradedSmul` (the chart identity,
  the only genuinely new MATHLIB work left) and
  `ProjCoords.ringHom_smul_apply_of_mem_projGrading` (a `MvPolynomial`
  computation), the gluing half having been discharged by
  `ProjCoords.openCover_eq_of_gradedSmul` and
  `ProjCoords.fromOfGlobalSections_eq_of_gradedSmul`;
  `ProjCoords.exists_of_specField` and `exists_projMulOfCoords` (the gluing)
  remain open.  **The `[Field K]` binder on the `K`-point leaves was REFUTED and
  replaced by `(hK : IsField ↥K)` on 2026-07-27** — see the FALSITY AUDIT on
  `ProjCoords.exists_of_specField`.  `hcomm` is now PROVEN rather than assumed, from antisymmetry of the
  chord–tangent forms plus a residue-field density argument; `hunit` and `hinv`
  stayed with the constructor because — correcting this file's earlier prose —
  they are NOT chart identities of the standard law, which degenerates exactly
  where each of them is asserted;
* **`exists_projPtAddEquiv_algClosed` is PROVEN as of 2026-07-27** — the
  algebraic `K`-point dictionary (`projMul_assoc_pt_algClosed` was this
  leaf until 2026-07-27 and is now PROVEN from it, `projMul_assoc_pt` was a
  second one and is PROVEN by descent, and `geometricallyReduced_projToSpec`
  was a third and is PROVEN outright).  Its four clauses are now four named
  leaves — `specPointEquiv_comp_projInfty_eq_zero`,
  `specPointEquiv_comp_projNeg`, `exists_add_self_affinePoint_of_isAlgClosed`,
  `exists_addMonoidHom_specPointEquiv_projMulPt` — and the bijection itself is
  the `def` `ProjCoords.specPointEquiv`;
* **`exists_projMul_geomFibreEquivVal` is PROVEN as of 2026-07-27** — item 8,
  see below; what remains of it is `specPointEquiv_symm_add_eq_projMulPt` (the
  chord–tangent identity, whose residue is the DIAGONAL only — `hlaw` gives the
  rest verbatim) and `specPointEquiv_symm_map_galois` (Galois equivariance).
  This was the third
  statement of item 8's leaf in one day and the chain is worth recording, since
  each step strictly shrank what a witness has to produce:
  `exists_projGroupLaw_geomFibreAddEquiv` (an `≃+` for an arbitrary
  `ProjGroupLaw` — refuted as a CUT, it needed rigidity) →
  `exists_projGroupLaw_geomFibreEquivVal` (a bare `≃` plus the raw morphism
  identity, `gl` existentially bound) → this leaf.  Both earlier forms are now
  PROVEN from it.  **RECONCILED AT INTEGRATION, 2026-07-27**: as written on its
  branch this leaf existentially bound its own `m`, which would have made the
  tree assert the existence of the multiplication TWICE — once here and once in
  `exists_projMul`, which is PROVEN over `ProjCoords`.  It now TAKES `m` and its
  `ProjCoords` law as hypotheses and asserts only the geometric-fibre
  identification, so there is exactly one construction of `m` in the tree and
  this leaf carries only the content that is genuinely new.  It and
  `exists_projPtAddEquiv_algClosed` above shared their whole implementation, and
  that implementation is now WRITTEN, once, as `ProjCoords.specPointEquiv` —
  `ProjCoords.exists_of_specField` (surjectivity) +
  `ProjCoords.exists_units_smul_of_toHom_eq` (injectivity, NEW: the exact
  converse of `ProjCoords.toHom_smul`, and the one ingredient the earlier plan
  named only as a "refuting check" rather than stating) + mathlib's
  `Projective.Point.toAffineAddEquiv`.  **No third dictionary should be
  written**;
* `isIso_projBaseChangeHom` — all that is left of `hbc`, base change for `Proj`;
* `exists_coordinateRingEquiv_projChartRing` and `compl_basicOpen_projCoord_two`
  — the two halves of `exists_affineChart_projModel` described above;
* the Weierstrass-comparison cluster further down, which belongs to a different
  node and is listed here only so that this count matches the compiler's:
  `exists_affineComplement_zeroSection`,
  `exists_weierstrassRingEquiv_of_affineComplement`,
  `isElliptic_of_isOpenImmersion_coordinateRing`, `relPointPost_add` and
  `exists_isIso_of_affineChart`.  Both
  `exists_weierstrassModel_of_ellipticScheme` and
  `exists_geomFibreAddEquiv_of_weierstrassModel` were leaves here until
  2026-07-27 and are now PROVEN — the first from the affineness /
  Riemann–Roch / discriminant thirds (the first three of those five), the
  second from the last two plus `hom_specRat_eq_of_range_eq`.

`isIso_projBaseChangeHom` — base change for `Proj`, the last of `hbc` — was on
this list until 2026-07-27 and is now PROVEN.

The whole "Dehomogenisation" section is now PROVEN — `exists_projChartRingEquiv`,
`projChart_jacobian_span_eq_top` and
`isStandardSmoothOfRelativeDimension_projChartAway` — and with it
`locally_isStandardSmooth_awayCoord`, the last direct sorry of item 7a.
`prime_projPolynomial` is PROVEN too, and so is `isIso_projBaseChangeHom`, so
`geometricallyConnected_projToSpec` has NO leaf left.  Each declaration carries its own
docstring saying what is missing and where the classical argument is.

**Item 8 was restated on 2026-07-27** and its leaf is now
`exists_projGroupLaw_geomFibreEquivVal`, which binds the group law
EXISTENTIALLY and states the chord–tangent clause in a `hassoc`-FREE form
(a bare `≃` plus the raw morphism identity
`(eqv (x + y)).1 = relPair (eqv x) (eqv y) ≫ gl.m`).  The `≃+` form,
`exists_projGroupLaw_geomFibreAddEquiv`, is PROVEN from it through
`ProjGroupLaw.geomFibreAddEquivOfVal`.
`exists_projGeomFibreAddEquiv` survives under its own name
as a PROVEN consequence, stated about the concrete `projGroupLaw E`.  The
old form quantified over an ARBITRARY `ProjGroupLaw`, which pins nothing
about `m`, and was therefore provable only through the rigidity theorem;
the audit is on `exists_projGroupLaw_geomFibreAddEquiv`.  That leaf also
subsumes `exists_projAdd`.

**The two cuts are now fully merged on the DOWNSTREAM side** (2026-07-27).  The
`hassoc`-entanglement is gone from every remaining OPEN statement, and
`exists_projGroupLaw_geomFibreEquivVal` has itself become plumbing: it is
PROVEN from `exists_projMul` (which CONSTRUCTS `m` and its `ProjCoords` law),
`exists_projMul_geomFibreEquivVal` (which supplies the chord–tangent clause for
that same `m`, taking it as a hypothesis) and `projMul_assoc` (which supplies
`hassoc` for it).  **The reconciliation is DONE (2026-07-27, at integration):**
as branched, `exists_projMul_geomFibreEquivVal` bound its own `m`, so the tree
would have asserted the existence of the multiplication TWICE; it now takes `m`
and `hlaw` as hypotheses and asserts only the identification.  See its own
docstring for why `hlaw` is load-bearing and why `_gl₀` still stays.

`geometricallyConnected_projToSpec` itself has **no direct sorry** any more.  Of its
three former steps `hbc`/`hne`/`hpre`:

* `hne` is **PROVEN** as `nonempty_proj`, over an arbitrary base field.  The point at
  infinity `[0 : 1 : 0]` is the homogeneous prime `(X̄, Z̄)`; the missing mathlib piece
  was primality of the span of a SUBSET of the variables, which is supplied here by
  `span_X_Z_eq_ker_killXZ` exhibiting `(X, Z)` as a kernel.
* `hpre` is **PROVEN OUTRIGHT** as `preconnectedSpace_proj`, over an arbitrary base
  field, with no remaining leaf.  Two statements absent from mathlib were needed and
  are proven here: that `Proj` of a graded domain is irreducible
  (`irreducibleSpace_projectiveSpectrum`), and that the projective Weierstrass cubic
  is prime (`prime_projPolynomial`).  The latter avoids the graded machinery entirely
  by reading `W` as a MONIC cubic in the single variable `X` over `K[Y, Z]`; see its
  docstring.
* `hbc` is **PROVEN OUTRIGHT** as `nonempty_projPullbackIso`.  Base change for `Proj`
  exists nowhere at this pin, so the whole thing had to be built here:
  `projBaseChangeGradedHom` (the graded hom), `irrelevant_le_map_projBaseChangeGradedHom`
  (the hypothesis `Proj.map` demands), `projBaseChangeHom` (the pullback lift — free here,
  because the commuting square lands in `Spec ℚ` and `hom_ext_spec_rat` applies), and then
  `isIso_projBaseChangeHom`.  Two pieces of missing MATHLIB infrastructure came out of it
  and are stated over arbitrary graded rings: `isPullback_awayι_map` (**the standard chart
  square of `Proj.map` is CARTESIAN**) and `awayDehomEquiv` (**`(A_s)₀ ≅ A ⧸ (s - 1)` for
  `s` of degree one**), the latter being what makes the ring residue elementary — after
  dehomogenising, base change of a chart is base change of a quotient of a polynomial ring
  (`isPushout_quotientMk`), with no graded base-change theory needed at all.

`nonempty_projGroupLaw` has no `sorry` of its own — but it is **REDUCED, NOT
CLOSED**: its proof runs through `exists_projAdd` and so through the still-open
`exists_projMul` and `projMul_assoc`, and it is therefore transitively sorried.
Do not read it as a finished result.  Two of the three data fields of a
`ProjGroupLaw` are constructed outright in `ProjectiveModel.lean`
(`projNeg`, the Weierstrass involution through `Proj.map`; `projInfty`,
the point at infinity through `Proj.fromOfGlobalSections`), and all three
"lies over the base" fields are free over this base
(`hom_ext_spec_rat`).  `exists_projAdd` — the group law `m` itself
together with the four group axioms — is in turn PROVEN from two leaves
that need disjoint machinery and can be owned separately:
`exists_projMul` (the gluing, plus the three axioms that are chart
identities in the same polynomial forms) and `projMul_assoc`
(associativity, the one axiom that is not a chart identity).

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

/-! ### Homogeneous coordinates for a morphism into `proj E`

This section is the interface item 2 of `exists_projMul`'s plan asks for —
"on each piece, the morphism into `proj E`" — packaged once so that the
gluing, the axioms and the `K`-point arguments all speak the same language.

A morphism `X ⟶ Proj 𝒜` is *not* the same thing as a triple of sections of
`X`: it is a line bundle on `X` together with three generating sections.
What `AlgebraicGeometry.Proj.fromOfGlobalSections` handles is the
TRIVIALISED case, where the line bundle is `𝒪_X` and the three sections are
honest elements of `Γ(X, ⊤)`, and that is exactly `ProjCoords` below.  Two
consequences shape everything that follows:

* a cover is unavoidable, because the bundle is only locally trivial;
* on an overlap the two trivialisations differ by a UNIT, which is why
  `ProjCoords.toHom_smul` is the load-bearing missing lemma.

`projInfty` (`ProjectiveModel.lean`) is the same construction done by hand
for the single datum `![0, 1, 0]`; it could be rewritten over this
interface, but is deliberately left alone here so that this cut touches no
other owner's declaration. -/

/-- **Spans are invariant under rescaling by a unit** (PROVEN, formal). -/
theorem span_range_smul_unit {R : Type*} [CommRing R] (u : Rˣ) (v : Fin 3 → R) :
    Ideal.span (Set.range ((u : R) • v)) = Ideal.span (Set.range v) := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have hv : v i = (↑u⁻¹ : R) * ((u : R) • v) i := by
      simp [Pi.smul_apply, smul_eq_mul, ← mul_assoc]
    rw [SetLike.mem_coe, hv]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

section Antisymmetry

variable {R : Type*} [CommRing R] (W' : WeierstrassCurve R)

/-! **The three chord–tangent forms are ANTISYMMETRIC** (PROVEN, `ring`).

`add? Q P = - add? P Q` for `? ∈ {X, Y, Z}`, and this needs NO curve
equation — it is a plain polynomial identity over any commutative ring.  A
projective triple and its negative are the same point, so this is the whole
content of `hcomm`, and it is why commutativity is the one group axiom that
comes for free from the standard law alone (see
`projMulCoords_comm`).  The docstring of `exists_projMul` previously
described the mechanism as "visibly symmetric … up to the sign that `negY`
absorbs"; the truth is simpler and is recorded here as four `ring` calls. -/

/-- The `Z`-coordinate of the chord–tangent law is antisymmetric. -/
theorem projAddZ_comm (P Q : Fin 3 → R) : addZ W' Q P = -addZ W' P Q := by
  simp only [addZ]; ring

/-- The `X`-coordinate of the chord–tangent law is antisymmetric. -/
theorem projAddX_comm (P Q : Fin 3 → R) : addX W' Q P = -addX W' P Q := by
  simp only [addX]; ring

/-- The `Y`-coordinate of `-(P + Q)` is antisymmetric. -/
theorem projNegAddY_comm (P Q : Fin 3 → R) : negAddY W' Q P = -negAddY W' P Q := by
  simp only [negAddY]; ring

/-- The `Y`-coordinate of the chord–tangent law is antisymmetric. -/
theorem projAddY_comm (P Q : Fin 3 → R) : addY W' Q P = -addY W' P Q := by
  simp only [addY, negY, addX, negAddY, addZ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The chord–tangent triple is antisymmetric**, i.e. swapping the two
arguments rescales it by the unit `-1` (PROVEN). -/
theorem projAddXYZ_comm (P Q : Fin 3 → R) :
    addXYZ W' Q P = (-1 : R) • addXYZ W' P Q := by
  rw [addXYZ, addXYZ, projAddX_comm, projAddY_comm, projAddZ_comm, smul_fin3]
  simp

end Antisymmetry

/-! **`equation_addXYZ` — the chord–tangent triple again satisfies the
Weierstrass equation — is PROVEN**, over an arbitrary commutative ring, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveAddition.lean`.

It was a leaf of this cut for a few hours.  It is a single
`linear_combination` against the two curve equations with cofactors of 130 and
186 monomials, computed by `Singular` and — the point that makes the statement
true over an arbitrary ring — carrying no denominators in the `aᵢ`.  It lives
in its own module because its `ring1` takes about four and a half minutes and
this file is edited concurrently by several owners; see that module's
docstring for the regeneration recipe. -/

/-- **Homogeneous coordinates for a morphism into the projective
Weierstrass model** — three sections of `Γ(X, ⊤)` satisfying the
Weierstrass equation and generating the unit ideal.

The `base` field is the structure map `ℚ →+* Γ(X, ⊤)`.  Carrying it
explicitly rather than as an `Algebra ℚ Γ(X, ⊤)` instance costs nothing:
`ℚ →+* A` is a subsingleton (`Rat.subsingleton_ringHom`, the same fact that
makes `hom_ext_spec_rat` work), so any two `ProjCoords` on the same `X`
have equal bases (`ProjCoords.base_eq`) and the structure is extensional in
`coord` alone (`ProjCoords.ext`).  The alternative — an instance argument —
is not available, because a general scheme carries no `ℚ`-algebra structure
on its global sections. -/
structure ProjCoords (E : WeierstrassCurve ℚ) (X : Scheme.{0}) where
  /-- the structure map of the base -/
  base : ℚ →+* Γ(X, ⊤)
  /-- the three homogeneous coordinates -/
  coord : Fin 3 → Γ(X, ⊤)
  /-- they satisfy the Weierstrass equation -/
  equation : Equation (E.map base) coord
  /-- they have no common zero -/
  span_coord : Ideal.span (Set.range coord) = ⊤

namespace ProjCoords

variable {E : WeierstrassCurve ℚ} {X : Scheme.{0}}

/-- **The base map is unique** (PROVEN): `ℚ →+* A` is a subsingleton. -/
theorem base_eq (c d : ProjCoords E X) : c.base = d.base := Subsingleton.elim _ _

/-- **A coordinate datum is determined by its coordinates** (PROVEN). -/
@[ext] theorem ext {c d : ProjCoords E X} (h : c.coord = d.coord) : c = d := by
  cases c; cases d
  simp only [mk.injEq]
  exact ⟨Subsingleton.elim _ _, h⟩

/-- **The coordinates kill the Weierstrass polynomial** (PROVEN). -/
theorem eval₂Hom_polynomial (c : ProjCoords E X) :
    MvPolynomial.eval₂Hom c.base c.coord (polynomial E) = 0 := by
  have h : MvPolynomial.eval c.coord (polynomial (E.map c.base)) = 0 := c.equation
  rw [WeierstrassCurve.Projective.map_polynomial, MvPolynomial.eval_map] at h
  simpa using h

/-- **The ring map out of the homogeneous coordinate ring** determined by a
coordinate datum (PROVEN) — `X ↦ x`, `Y ↦ y`, `Z ↦ z`, which descends
through `(W)` precisely because the coordinates satisfy the equation. -/
noncomputable def ringHom (c : ProjCoords E X) :
    (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) →+* Γ(X, ⊤) :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom c.base c.coord) (by
    intro a ha
    have h : (polynomialHomogeneousIdeal E).toIdeal = Ideal.span {polynomial E} := rfl
    rw [h, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, c.eval₂Hom_polynomial, zero_mul])

@[simp] theorem ringHom_mk (c : ProjCoords E X) (p : MvPolynomial (Fin 3) ℚ) :
    c.ringHom (Ideal.Quotient.mk _ p) = MvPolynomial.eval₂ c.base c.coord p := rfl

/-- **The irrelevant ideal maps onto the unit ideal** (PROVEN) — the
hypothesis `Proj.fromOfGlobalSections` consumes, and the reason
`span_coord` is the right non-degeneracy condition. -/
theorem map_irrelevant_eq_top (c : ProjCoords E X) :
    (HomogeneousIdeal.irrelevant (projGrading E)).toIdeal.map c.ringHom = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← c.span_coord, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hmem : (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.X i)) ∈
      (HomogeneousIdeal.irrelevant (projGrading E)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
      (HomogeneousIdeal.mk_mem_quotientGrading
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)))
  have h := Ideal.mem_map_of_mem c.ringHom hmem
  simpa using h

/-- **The morphism into the projective model determined by a coordinate
datum** (PROVEN) — item 2 of `exists_projMul`'s plan, done once and for
all. -/
noncomputable def toHom (c : ProjCoords E X) : X ⟶ proj E :=
  Proj.fromOfGlobalSections (𝒜 := projGrading E) c.ringHom c.map_irrelevant_eq_top

/-- **Rescaling the coordinates by a unit** (PROVEN) — the change of
trivialisation that relates two charts on their overlap. -/
noncomputable def smul (u : (Γ(X, ⊤))ˣ) (c : ProjCoords E X) : ProjCoords E X where
  base := c.base
  coord := (u : Γ(X, ⊤)) • c.coord
  equation := (WeierstrassCurve.Projective.equation_smul (W' := E.map c.base) c.coord
    u.isUnit).mpr c.equation
  span_coord := (span_range_smul_unit u c.coord).trans c.span_coord

@[simp] theorem smul_coord (u : (Γ(X, ⊤))ˣ) (c : ProjCoords E X) :
    (smul u c).coord = (u : Γ(X, ⊤)) • c.coord := rfl

section GradedSmul

/-! ### The `fromOfGlobalSections` congruence, cut into three (2026-07-27)

`ProjCoords.toHom_smul` was a single opaque leaf described as "the one piece of
genuinely new MATHLIB work".  It is now a REDUCTION: the scheme-theoretic half
below is PROVEN, and what is left is two much smaller statements, one of them a
plain computation in `MvPolynomial`.

The general shape is stated for an arbitrary graded ring, because nothing in the
scheme-theoretic half is special to the Weierstrass ring; `g` is the rescaled map
`f_u`, characterised by `g a = u ^ n * f a` on `𝒜 n`, and no sum over graded
pieces is needed because that characterisation is all the proof uses. -/

/-- **Rescaling by a unit does not move the basic opens of the
`fromOfGlobalSections` cover** (PROVEN, and the whole reason the two covers
coincide on the nose). -/
theorem basicOpen_eq_of_gradedSmul {σ : Type*} {A : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{0}}
    (u : (Γ(X, ⊤))ˣ) (f g : A →+* Γ(X, ⊤))
    (h : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → g a = (u : Γ(X, ⊤)) ^ n * f a)
    {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    X.basicOpen (g a) = X.basicOpen (f a) := by
  rw [h n a ha, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((u.isUnit).pow n),
    top_inf_eq]

/-- **The two `fromOfGlobalSections` covers are EQUAL**, not merely isomorphic
(PROVEN) — the index type is the same and the opens agree by
`basicOpen_eq_of_gradedSmul`, so the two `Scheme.OpenCover` structures differ
only in proof fields. -/
theorem openCover_eq_of_gradedSmul {σ : Type*} {A : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{0}}
    (u : (Γ(X, ⊤))ˣ) (f g : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    (h : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → g a = (u : Γ(X, ⊤)) ^ n * f a) :
    Proj.openCoverOfMapIrrelevantEqTop 𝒜 g hg = Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf := by
  have key : (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ X.basicOpen (g ir.2.1)) =
      (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ X.basicOpen (f ir.2.1)) :=
    funext fun ir ↦ basicOpen_eq_of_gradedSmul 𝒜 u f g h ir.2.2.2
  unfold Proj.openCoverOfMapIrrelevantEqTop
  congr 1

/-- **The chart-level half of the congruence** (sorry node — this is where ALL
the remaining content of `ProjCoords.toHom_smul` now sits, and it is the piece
that lives in `HomogeneousLocalization` rather than in scheme theory).

`Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hn ht` is, after composing with
`Proj.basicOpenIsoSpec`, the map determined by the ring homomorphism

    Away 𝒜 t →+* Localization.Away (f t),   mk (a, t ^ k) ↦ f a / (f t) ^ k

(`IsLocalization.map` composed with `algebraMap (Away 𝒜 t) (Localization.Away t)`
in mathlib's definition).  For `g` the same formula reads, on `a ∈ 𝒜 (k * n)`,

    g a / (g t) ^ k = u ^ (k * n) * f a / (u ^ n * f t) ^ k = f a / (f t) ^ k,

so the two ring maps are literally equal once `Localization.Away (g t)` is
identified with `Localization.Away (f t)` — which is legitimate because
`g t = u ^ n * f t` and `u ^ n` is a unit, so the two `Submonoid.powers` invert
the same elements.  **That is the whole mathematical content**: `Away` is the
degree-`0` part and the rescaling is by `u` to the power of the degree, so it
cancels between numerator and denominator.

The `Scheme.isoOfEq` on the left is `basicOpen_eq_of_gradedSmul`: the two charts
have equal — but not syntactically equal — domains.

*What is NOT missing.*  The gluing is already done: `openCover_eq_of_gradedSmul`
shows the two covers are equal, and `fromOfGlobalSections_eq_of_gradedSmul` below
derives the full congruence from this leaf by `Scheme.Cover.hom_ext` plus
`Scheme.Cover.ι_glueMorphisms`, with no further scheme theory.  So an owner of
this leaf never has to touch `glueMorphisms`. -/
theorem toBasicOpenOfGlobalSections_eq_of_gradedSmul {σ : Type*} {A : Type} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{0}}
    (u : (Γ(X, ⊤))ˣ) (f g : A →+* Γ(X, ⊤))
    (h : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → g a = (u : Γ(X, ⊤)) ^ n * f a)
    {n : ℕ} {t : A} (hn : 0 < n) (ht : t ∈ 𝒜 n) :
    Proj.toBasicOpenOfGlobalSections 𝒜 g rfl hn ht ≫ (Proj.basicOpen 𝒜 t).ι =
      (X.isoOfEq (basicOpen_eq_of_gradedSmul 𝒜 u f g h ht)).hom ≫
        Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hn ht ≫ (Proj.basicOpen 𝒜 t).ι :=
  sorry

/-- **The missing mathlib congruence for `Proj.fromOfGlobalSections`** (PROVEN
from `openCover_eq_of_gradedSmul` and
`toBasicOpenOfGlobalSections_eq_of_gradedSmul`).

This is the statement `ProjCoords.toHom_smul` needs, and — modulo the one chart
leaf above — it is done.  Note that no hypothesis says `g` is *built* from `f` by
rescaling; only the degreewise identity `g a = u ^ n * f a` is used, which is
exactly what `ProjCoords.smul` provides. -/
theorem fromOfGlobalSections_eq_of_gradedSmul {σ : Type*} {A : Type} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{0}}
    (u : (Γ(X, ⊤))ˣ) (f g : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    (h : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → g a = (u : Γ(X, ⊤)) ^ n * f a) :
    Proj.fromOfGlobalSections 𝒜 g hg = Proj.fromOfGlobalSections 𝒜 f hf := by
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 g hg).hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, t, hn, ht⟩ := i
  have hopen : X.basicOpen (g t) = X.basicOpen (f t) :=
    basicOpen_eq_of_gradedSmul 𝒜 u f g h ht
  have hfeq : (Proj.openCoverOfMapIrrelevantEqTop 𝒜 g hg).f ⟨n, t, hn, ht⟩ =
      (X.isoOfEq hopen).hom ≫ (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf).f ⟨n, t, hn, ht⟩ := by
    simp [Proj.openCoverOfMapIrrelevantEqTop]
  have hL : (Proj.openCoverOfMapIrrelevantEqTop 𝒜 g hg).f ⟨n, t, hn, ht⟩ ≫
        Proj.fromOfGlobalSections 𝒜 g hg =
      Proj.toBasicOpenOfGlobalSections 𝒜 g rfl hn ht ≫ (Proj.basicOpen 𝒜 t).ι :=
    (Proj.openCoverOfMapIrrelevantEqTop 𝒜 g hg).ι_glueMorphisms _ _ ⟨n, t, hn, ht⟩
  have hR : (Proj.openCoverOfMapIrrelevantEqTop 𝒜 g hg).f ⟨n, t, hn, ht⟩ ≫
        Proj.fromOfGlobalSections 𝒜 f hf =
      (X.isoOfEq hopen).hom ≫
        Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hn ht ≫ (Proj.basicOpen 𝒜 t).ι := by
    rw [hfeq]
    exact (Category.assoc _ _ _).trans (congrArg ((X.isoOfEq hopen).hom ≫ ·)
      ((Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨n, t, hn, ht⟩))
  rw [hL, hR]
  exact toBasicOpenOfGlobalSections_eq_of_gradedSmul 𝒜 u f g h hn ht

end GradedSmul

/-- **The rescaled coordinate ring map is `u ^ n` times the original in degree
`n`** (sorry node — the arithmetic half of `ProjCoords.toHom_smul`).

`ProjCoords.ringHom` is `Ideal.Quotient.lift` of `MvPolynomial.eval₂Hom base coord`,
so on the class of a polynomial `p` this says

    eval₂ base (u • coord) p = u ^ n * eval₂ base coord p   for `p` homogeneous of degree `n`,

which is a monomial-by-monomial computation: a monomial of total degree `n`
picks up exactly `u ^ n`.  The one step that is not literally that computation
is passing from `a ∈ projGrading E n` — membership in the quotient grading — to
a homogeneous representative of degree `n`, i.e. surjectivity of
`HomogeneousIdeal.quotientGrading` onto its graded pieces; `Ideal.Quotient.mk`
is surjective and the quotient grading is defined as the image, so this is
`HomogeneousIdeal.mk_mem_quotientGrading` read backwards.

This is deliberately stated in the exact form
`fromOfGlobalSections_eq_of_gradedSmul` consumes. -/
theorem ringHom_smul_apply_of_mem_projGrading (u : (Γ(X, ⊤))ˣ) (c : ProjCoords E X)
    (n : ℕ) (a : MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal)
    (ha : a ∈ projGrading E n) :
    (smul u c).ringHom a = (u : Γ(X, ⊤)) ^ n * c.ringHom a :=
  sorry

/-- **Rescaling the coordinates by a unit does not change the morphism**
(**PROVEN 2026-07-27** from `fromOfGlobalSections_eq_of_gradedSmul` and
`ringHom_smul_apply_of_mem_projGrading` — it is a REDUCTION, not a result: the
two leaves above still carry the content, and this declaration has no `sorry`
of its own).

The general statement is: for `u : Γ(X, ⊤)ˣ` and `f : A →+* Γ(X, ⊤)` with
`A` graded, the rescaled map `f_u : a ↦ ∑ n, u ^ n * f aₙ` satisfies
`fromOfGlobalSections 𝒜 f_u hf' = fromOfGlobalSections 𝒜 f hf`.  Here `A`
is generated in degree `1` by the three coordinates, so `f_u` is just
`aᵢ ↦ u * f aᵢ`, which is what `ProjCoords.smul` computes — no sum over
graded pieces is needed and the statement is a plain equation between two
morphisms of schemes.

**Still absent from the pin**, re-checked 2026-07-27:
`ProjectiveSpectrum/Basic.lean` has no congruence lemma for
`fromOfGlobalSections` in its `f` argument at all — only
`_preimage_basicOpen`, `_morphismRestrict`, `_resLE` and `_toSpecZero`.

*Route.* `fromOfGlobalSections` is built by `glueMorphisms` over the cover
`X.basicOpen (f r)` indexed by homogeneous `r` of positive degree.
Rescaling by `u` sends `X.basicOpen (f r)` to `X.basicOpen (u ^ n * f r)`,
which is the SAME open (`u` is a unit), so the two covers agree on the
nose; on each piece the induced map into `Away 𝒜 r` differs by the
automorphism of the localisation given by `u`, which is the identity on
degree-`0` elements — and `Away` is exactly the degree-`0` part.  So the
two morphisms agree piecewise, and `Scheme.Cover.hom_ext` finishes.  The
work is entirely in `HomogeneousLocalization`, not in scheme theory.

*Why it is load-bearing*: it is used three times below — for the unit
`-1` in `projMulCoords_comm`, for the transition between the two
Bosma–Lenstra laws on their overlap (where the unit is `add2Z / addZ`),
and for the identification of a degenerate sum with the point at
infinity. -/
theorem toHom_smul (u : (Γ(X, ⊤))ˣ) (c : ProjCoords E X) : (smul u c).toHom = c.toHom :=
  fromOfGlobalSections_eq_of_gradedSmul (projGrading E) u c.ringHom (smul u c).ringHom
    c.map_irrelevant_eq_top (smul u c).map_irrelevant_eq_top
    (ringHom_smul_apply_of_mem_projGrading u c)

/-- **The chord–tangent sum of two coordinate data**, where it is
non-degenerate (PROVEN from `equation_addXYZ`). -/
noncomputable def add (c d : ProjCoords E X)
    (h : Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤) :
    ProjCoords E X where
  base := c.base
  coord := addXYZ (E.map c.base) c.coord d.coord
  equation := equation_addXYZ c.equation (by rw [c.base_eq d]; exact d.equation)
  span_coord := h

@[simp] theorem add_coord (c d : ProjCoords E X) (h) :
    (c.add d h).coord = addXYZ (E.map c.base) c.coord d.coord := rfl

/-- **Every point of the projective model over a FIELD admits coordinates**
(sorry node).

TRUE and standard, and the restriction to `Spec K` is what makes it true:
a morphism `T ⟶ Proj 𝒜` is a line bundle on `T` plus generating sections,
and over `Spec K` every line bundle is trivial (`Pic (Spec K) = 0`, since
`K` is local — indeed a field — so every finitely generated projective
module of rank `1` is free).  Hence the tautological `𝒪(1)` pulls back to
`𝒪_{Spec K}` and its three coordinate sections become elements of
`Γ(Spec K, ⊤)`.

*Concretely*, without any Picard-group machinery: `a : Spec K ⟶ Proj 𝒜`
has image a single point, which lies in some basic open `D₊(r)` with `r`
one of `X̄`, `Ȳ`, `Z̄` (the three generate the irrelevant ideal, so they
cannot all vanish at it).  Factor `a` through
`D₊(r) ≅ Spec (Away 𝒜 r)`, giving a ring map `Away 𝒜 r →+* K`, and take
`coord i := (image of Xᵢ/r)` scaled by any lift; the coordinate `r/r = 1`
is a unit, so `span_coord` holds.  Mathlib supplies the factorisation as
`Proj.awayι` together with `Proj.opensRange_awayι` and
`Proj.basicOpenIsoSpec`.

*What it is used for*: it is the bridge from the residue-field ext lemma
`ext_of_fromSpecResidueField_eq` to the polynomial identities.  Without it
no `K`-point argument in this cluster can start.

## FALSITY AUDIT (2026-07-27): the hypothesis is `IsField ↥K`, NOT `[Field K]`

This leaf, `toHom_eq_of_addXYZ_not_span` and `projMulCoords_comm` were all
stated with `(K : CommRingCat.{0}) [Field K]`, and that binder is **false-shaped**
— not merely awkward.  `[Field K]` elaborates to `Field ↥K`, an arbitrary field
structure ON THE CARRIER TYPE, and `Field` extends `CommRing`, so it supplies a
SECOND ring structure unrelated to `K.str`.  Everything the statement is about —
`Spec K`, `Γ(Spec K, ⊤)`, `ProjCoords E (Spec K)` — is built from `K.str`, so the
hypothesis constrains nothing about the ring whose spectrum is being taken.

This was verified, not guessed.  The transport

    (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField _)

fails with *"synthesized type class instance is not definitionally equal"*,
`Field.toSemifield.toDivisionSemiring.toSemiring` against
`CommRing.toCommSemiring.toSemiring`, exactly because the two ring structures on
`↥K` are different terms.  With `(hK : IsField ↥K)` the same line elaborates, and
it also elaborates at the one instantiation site, `Scheme.residueField x`, where
the `Field` instance genuinely IS `K.str` — so the repair costs the consumers a
`Field.toIsField _` and nothing else.

Under the old binder the statement is not just unprovable but FALSE.  Take
`K := CommRingCat.of ℚ[X]` with a junk `Field ℚ[X]` transported along a bijection
`ℚ[X] ≃ ℚ` (`Equiv.field`; both types are denumerable): every hypothesis holds,
`Spec K = 𝔸¹_ℚ`, and `c := ![0,1,0]`, `d := ![x₀,y₀,t]` have
`addXYZ c d = t • d` (`addXYZ_of_Z_eq_zero_left`), whose span is `(t) ≠ ⊤`, while
`c.toHom ≠ d.toHom`.  The earlier note claiming the binder is false-shaped "only
when a proof needs `AlgebraicClosure K` or `algebraMap K _`" is too narrow: it is
false-shaped whenever the proof needs the field structure to BE `K.str`, which
"a proper ideal of a field is zero" does. -/
theorem exists_of_specField (E : WeierstrassCurve ℚ) (K : CommRingCat.{0})
    (hK : _root_.IsField ↥K) (a : Spec K ⟶ proj E) :
    ∃ c : ProjCoords E (Spec K), c.toHom = a :=
  sorry

/-- **Over a FIELD the chord–tangent triple degenerates exactly on the
diagonal** (PROVEN) — the ring-level content of
`ProjCoords.toHom_eq_of_addXYZ_not_span`, stated over an arbitrary
commutative ring that happens to be a field so that it can be instantiated
at `Γ(Spec K, ⊤)` without transporting the ambient `CommRing` structure.

`IsField` is taken as a HYPOTHESIS rather than as an instance on purpose:
`Γ(Spec K, ⊤)` is a field only through `Scheme.ΓSpecIso`, and installing a
`Field` instance obtained by transport would create a second `CommRing`
path on the same type, which is exactly the "instances that print
identically" trap.  Everything below is therefore phrased with the
`[NoZeroDivisors]`-general forms of mathlib's addition lemmas.

The conclusion is the strongest possible one: not merely that the two
points agree, but that the two coordinate triples differ by a UNIT, which
is what `ProjCoords.toHom_smul` consumes. -/
theorem exists_units_smul_of_addXYZ_not_span {R : Type*} [CommRing R] (hR : IsField R)
    (W' : WeierstrassCurve R) {P Q : Fin 3 → R}
    (hP : Equation W' P) (hQ : Equation W' Q)
    (hPs : Ideal.span (Set.range P) = ⊤) (hQs : Ideal.span (Set.range Q) = ⊤)
    (h : Ideal.span (Set.range (addXYZ W' P Q)) ≠ ⊤) :
    ∃ u : Rˣ, (u : R) • P = Q := by
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  have hunit : ∀ a : R, a ≠ 0 → IsUnit a := fun a ha =>
    isUnit_iff_exists_inv.mpr (hR.mul_inv_cancel ha)
  haveI : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · obtain ⟨a', ha'⟩ := hR.mul_inv_cancel ha
      refine Or.inr ?_
      calc b = a' * (a * b) := by rw [← mul_assoc, mul_comm a' a, ha', one_mul]
        _ = 0 := by rw [hab, mul_zero]
  -- a triple with a nonzero entry spans the unit ideal
  have hspan_top : ∀ (v : Fin 3 → R) (i : Fin 3), v i ≠ 0 →
      Ideal.span (Set.range v) = ⊤ := fun v i hvi =>
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (hunit _ hvi)
  -- a spanning triple whose outer entries vanish has a nonzero middle entry
  have hmid : ∀ (v : Fin 3 → R), Ideal.span (Set.range v) = ⊤ →
      v 0 = 0 → v 2 = 0 → v 1 ≠ 0 := by
    intro v hv h0 h2 h1
    have hle : Ideal.span (Set.range v) ≤ ⊥ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [h0, h1, h2]
    rw [hv] at hle
    exact one_ne_zero (Ideal.mem_bot.mp (hle Submodule.mem_top))
  -- the hypothesis says all three chord–tangent forms vanish
  have hzero : ∀ i, addXYZ W' P Q i = 0 := fun i => by
    by_contra hi
    exact h (hspan_top _ i hi)
  have hY : addY W' P Q = 0 := by have := hzero 1; rwa [addXYZ_Y] at this
  have hZ : addZ W' P Q = 0 := by have := hzero 2; rwa [addXYZ_Z] at this
  -- packaging: a cross-multiplication identity produces the rescaling unit
  have hmk : ∀ p q : R, p ≠ 0 → q ≠ 0 → (∀ i, q * P i = p * Q i) →
      ∃ u : Rˣ, (u : R) • P = Q := by
    intro p q hp hq hpq
    obtain ⟨up, hup⟩ := hunit p hp
    obtain ⟨uq, huq⟩ := hunit q hq
    refine ⟨uq * up⁻¹, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul]
    refine mul_left_cancel₀ hp ?_
    calc p * ((uq : R) * (up⁻¹ : Rˣ) * P i)
        = ((up : R) * (up⁻¹ : Rˣ)) * ((uq : R) * P i) := by rw [← hup]; ring
      _ = (uq : R) * P i := by rw [Units.mul_inv, one_mul]
      _ = q * P i := by rw [huq]
      _ = p * Q i := hpq i
  by_cases hPz : P 2 = 0
  · -- `P` is at infinity, and `addZ = 0` forces `Q` to be there too
    have hPx : P 0 = 0 := X_eq_zero_of_Z_eq_zero hP hPz
    have hPy : P 1 ≠ 0 := hmid P hPs hPx hPz
    have hQz : Q 2 = 0 := by
      have h0 : P 1 ^ 2 * Q 2 * Q 2 = 0 := by
        rw [← addZ_of_Z_eq_zero_left hP hPz]; exact hZ
      rcases mul_eq_zero.mp h0 with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h'') hPy
        · exact h''
      · exact h'
    have hQx : Q 0 = 0 := X_eq_zero_of_Z_eq_zero hQ hQz
    have hQy : Q 1 ≠ 0 := hmid Q hQs hQx hQz
    refine hmk (P 1) (Q 1) hPy hQy ?_
    intro i
    fin_cases i
    · show Q 1 * P 0 = P 1 * Q 0
      rw [hPx, hQx, mul_zero, mul_zero]
    · show Q 1 * P 1 = P 1 * Q 1
      ring
    · show Q 1 * P 2 = P 1 * Q 2
      rw [hPz, hQz, mul_zero, mul_zero]
  · by_cases hQz : Q 2 = 0
    · -- impossible: `Q` at infinity and `P` not
      exfalso
      have hQx : Q 0 = 0 := X_eq_zero_of_Z_eq_zero hQ hQz
      have hQy : Q 1 ≠ 0 := hmid Q hQs hQx hQz
      have h0 : -(Q 1 ^ 2 * P 2) * P 2 = 0 := by
        rw [← addZ_of_Z_eq_zero_right hQ hQz]; exact hZ
      rw [neg_mul, neg_eq_zero] at h0
      rcases mul_eq_zero.mp h0 with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact hQy (pow_eq_zero_iff two_ne_zero |>.mp h'')
        · exact hPz h''
      · exact hPz h'
    · -- both affine: `addZ = 0` forces equal `x`, then `addY = 0` forces equal `y`
      have hx : P 0 * Q 2 - Q 0 * P 2 = 0 := by
        refine pow_eq_zero_iff three_ne_zero |>.mp ?_
        rw [← addZ_eq' hP hQ, hZ, zero_mul]
      have hy : P 1 * Q 2 - Q 1 * P 2 = 0 := by
        refine pow_eq_zero_iff three_ne_zero |>.mp ?_
        have h1 : -(P 1 * Q 2 - Q 1 * P 2) ^ 3 * (P 2 * Q 2) ^ 2 = 0 := by
          rw [← addY_of_X_eq' hP hQ hPz hQz (sub_eq_zero.mp hx), hY, zero_mul]
        have hne : (P 2 * Q 2) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hPz hQz)
        rcases mul_eq_zero.mp h1 with h' | h'
        · exact neg_eq_zero.mp h'
        · exact absurd h' hne
      refine hmk (P 2) (Q 2) hPz hQz ?_
      intro i
      fin_cases i
      · show Q 2 * P 0 = P 2 * Q 0
        linear_combination hx
      · show Q 2 * P 1 = P 2 * Q 1
        linear_combination hy
      · show Q 2 * P 2 = P 2 * Q 2
        ring

/-- **Over a field the standard addition law degenerates exactly on the
DIAGONAL** (**PROVEN 2026-07-27** from
`ProjCoords.exists_units_smul_of_addXYZ_not_span` and
`ProjCoords.toHom_smul`) — the Lean form of the 2026-07-27 correction
recorded in `exists_projMul`'s docstring.

Over a field, `Ideal.span (Set.range v) ≠ ⊤` says precisely that all three
of `addX`, `addY`, `addZ` vanish, and the claim is that this forces the two
points to be EQUAL — not merely to have the same `x`-coordinate.  All the
inputs are in mathlib and the case analysis is short:

* `P z ≠ 0`, `Q z ≠ 0`: `addZ_eq'` gives
  `addZ · (P z * Q z) = (P x * Q z - Q x * P z) ^ 3`, so `addZ = 0` forces
  `x(P) = x(Q)`; then `addY_of_X_eq'` gives
  `addY · (P z Q z) ^ 3 = -(P y Q z - Q y P z) ^ 3 (P z Q z) ^ 2`, so
  `addY = 0` forces `y(P) = y(Q)`.  Hence `Q z • P = P z • Q` and the two
  data differ by the unit `Q z / P z`.
* `P z = 0`: then `P x = 0` (`X_eq_zero_of_Z_eq_zero`) and `P y` is a unit
  by `span_coord`, so `addZ_of_Z_eq_zero_left` reads
  `addZ = P y ^ 2 * Q z ^ 2`, forcing `Q z = 0`; both points are then
  `[0 : * : 0]`.
* `Q z = 0` symmetrically.

Conclude with `ProjCoords.toHom_smul`, which turns "the coordinates differ
by a unit" into "the morphisms are equal".

**This statement is the corrected one.**  A previous version of
`exists_projMul`'s docstring asserted that the standard law vanishes on the
whole locus `x(P) = x(Q)`; mathlib's `negAddY_of_X_eq'` refutes that — on
the antidiagonal `addY` is a unit and `[0 : addY : 0]` is the point at
infinity, the correct value of `P + Q`.

**The `[Field K]` binder was replaced by `(hK : IsField ↥K)` on 2026-07-27**; see
the FALSITY AUDIT on `ProjCoords.exists_of_specField` for why the old one made
this statement false rather than merely unprovable. -/
theorem toHom_eq_of_addXYZ_not_span {K : CommRingCat.{0}} (hK : _root_.IsField ↥K)
    (c d : ProjCoords E (Spec K))
    (h : ¬ Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤) :
    c.toHom = d.toHom := by
  have hR : _root_.IsField Γ(Spec K, ⊤) :=
    (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv.isField hK
  have hQ : Equation (E.map c.base) d.coord := by rw [c.base_eq d]; exact d.equation
  obtain ⟨u, hu⟩ := exists_units_smul_of_addXYZ_not_span hR (E.map c.base) c.equation hQ
    c.span_coord d.span_coord h
  have hd : smul u c = d := ProjCoords.ext (by rw [smul_coord]; exact hu)
  rw [← toHom_smul u c, hd]

/-- **The exact CONVERSE of `ProjCoords.toHom_smul`: over a field, two coordinate data
inducing the same morphism differ by a unit** (sorry node, introduced 2026-07-27 as the
one missing ingredient of the `Spec K`-point dictionary).

`toHom_smul` says rescaling does not change the morphism; this says nothing else does.
Together they make `c ↦ c.toHom` induce a BIJECTION from coordinate data modulo rescaling
onto `Spec K ⟶ proj E`, which is what `ProjCoords.specPointEquiv` below is built from —
`exists_of_specField` supplies surjectivity, this supplies injectivity, and without it the
`right_inv` field of the equivalence cannot be discharged.

**This is precisely the "refuting check" named in the route recorded at
`exists_projMul_geomFibreEquivVal`** ("exhibit … a pair of `ProjCoords` over `Spec ℚ̄`
with the same `toHom` that are not related by `ProjCoords.smul`").  That the route
*names* the check but no leaf *stated* it is why the plan looked complete while the
`Equiv` could not be assembled.

## Why it is TRUE

A morphism `a : Spec K ⟶ Proj 𝒜` from the spectrum of a FIELD has a single point in its
image; that point lies in some basic open `D₊(r)`, `r ∈ {X̄, Ȳ, Z̄}`, and `a` factors
through `D₊(r) ≅ Spec (Away 𝒜 r)`.  A `ProjCoords` datum `c` with `c.toHom = a` has
`c.coord r` a unit (otherwise the image would miss `D₊(r)`), and the induced ring map
`Away 𝒜 r →+* K` sends `Xᵢ/r ↦ c.coord i / c.coord r`.  So `a` determines every RATIO
`c.coord i / c.coord r`, and two data with the same ratios differ by the unit
`d.coord r / c.coord r`.  The field hypothesis enters twice: to know some coordinate is
a unit (`span_coord = ⊤` plus "a proper ideal of a field is zero"), and to divide.

*Contrast with the general case*: over a general `X` the statement is FALSE as
literally stated — two trivialisations of a line bundle differ by a unit only LOCALLY,
so the correct general form quantifies over a cover.  Over `Spec K` the bundle is
trivial (`Pic (Spec K) = 0`, the same fact `exists_of_specField` rests on) and one
global unit suffices.

The binder is `(hK : IsField ↥K')` rather than `[Field K']` for the reason given in the
FALSITY AUDIT on `exists_of_specField`: `[Field K']` would elaborate to a SECOND ring
structure on the carrier, unrelated to `K'.str`, and the statement would be false. -/
theorem exists_units_smul_of_toHom_eq {K' : CommRingCat.{0}} (_hK : _root_.IsField ↥K')
    (c d : ProjCoords E (Spec K')) (_h : c.toHom = d.toHom) :
    ∃ u : (Γ(Spec K', ⊤))ˣ, smul u c = d :=
  sorry

end ProjCoords

/-- **The chord–tangent multiplication morphism, characterised on
coordinate data, together with the unit and inverse laws** (sorry node —
this is where the GLUING now lives, and it is all that is left of the
construction half of `exists_projMul`).

Relative to the old single leaf, `hcomm` has been REMOVED: it is proven
below (`projMulCoords_comm`, then `exists_projMul`) from the
antisymmetry of the chord–tangent forms plus `ProjCoords.toHom_smul`, with
no charts and no second addition law.  What remains here is the
construction of `m` together with the characterisation that pins it, plus
the two axioms that genuinely need the second law.

## Why `hunit` and `hinv` are NOT free, correcting the previous docstring

The docstring of `exists_projMul` used to list all three of `hcomm`,
`hunit`, `hinv` as "cheap … chart identities in the same polynomial forms".
That is right for `hcomm` and WRONG for the other two, and the reason is
the same corrected computation that identified the diagonal as the
exceptional set:

* `hunit` reads `m(O, P) = P`.  From the standard law,
  `addXYZ ![0,1,0] Q = Q z • Q` (`addXYZ_of_Z_eq_zero_left`), which is a
  legitimate rescaling of `Q` — **but only where `Q z` is a unit**.  At
  `Q = O` the triple vanishes identically, so the standard law says nothing
  there, and `m(O, O) = O` is not obtainable from it.
* `hinv` reads `m(-P, P) = O`.  The standard law degenerates exactly where
  `negOf P ≈ P`, i.e. at the `2`-torsion, where again it says nothing.

Both gaps are covered by the second Bosma–Lenstra law, which is
non-degenerate on the whole diagonal — so the constructor of `m`, who has
both laws in hand, does get them; a consumer holding only the standard law
does not.  (The alternative is a density argument restricting to the
complements of those two proper closed subsets, which needs irreducibility
of `proj E` — available here as `irreducibleSpace_projectiveSpectrum` and
`prime_projPolynomial` — plus a nonemptiness statement for a basic open of
`Proj`.  Either route is legitimate; the second law is the shorter one.)

## What the characterisation buys, and why it is stated at every `X`

The first conjunct says: whenever a test scheme `X` carries coordinate data
for two points and the standard law is non-degenerate on it, `m` composed
with the corresponding `X`-point of `A ×_ℚ A` is given by the chord–tangent
triple.  Quantifying over all `X` (rather than only over fields) costs the
constructor nothing — it is exactly what `glueMorphisms` produces — and it
is what makes the leaf strong enough to be consumed both by the
residue-field argument below and, later, by the `ℚ̄`-point dictionary that
`exists_projGroupLaw_geomFibreEquivVal` needs. -/
theorem exists_projMulOfCoords (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E,
      (∀ (X : Scheme.{0}) (c d : ProjCoords E X)
          (h : Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤),
          Limits.pullback.lift c.toHom d.toHom (hom_ext_spec_rat _ _) ≫ m = (c.add d h).toHom) ∧
        Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E) ∧
          Limits.pullback.lift (projNeg E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E :=
  sorry

/-- **Any morphism into the fibre square is the lift of its two
components** (PROVEN, formal). -/
theorem comp_eq_lift_comp (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E) {T : Scheme.{0}}
    (s : T ⟶ Limits.pullback (projToSpec E) (projToSpec E)) :
    s ≫ m = Limits.pullback.lift (s ≫ Limits.pullback.fst (projToSpec E) (projToSpec E))
      (s ≫ Limits.pullback.snd (projToSpec E) (projToSpec E)) (hom_ext_spec_rat _ _) ≫ m := by
  congr 1
  apply Limits.pullback.hom_ext
  · rw [Limits.pullback.lift_fst]
  · rw [Limits.pullback.lift_snd]

/-- **Reading the swap-precomposed multiplication at a `T`-point**
(PROVEN, formal). -/
theorem comp_swap_eq_lift_comp (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E) {T : Scheme.{0}}
    (s : T ⟶ Limits.pullback (projToSpec E) (projToSpec E)) :
    s ≫ (Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
        (Limits.pullback.fst (projToSpec E) (projToSpec E))
        Limits.pullback.condition.symm ≫ m) =
      Limits.pullback.lift (s ≫ Limits.pullback.snd (projToSpec E) (projToSpec E))
        (s ≫ Limits.pullback.fst (projToSpec E) (projToSpec E)) (hom_ext_spec_rat _ _) ≫ m := by
  rw [← Category.assoc]
  congr 1
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]
  · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd]

/-- **Commutativity of the induced operation on `K`-points, `K` a field**
(PROVEN from `exists_projMulOfCoords`, `ProjCoords.exists_of_specField`,
`ProjCoords.toHom_smul` and `ProjCoords.toHom_eq_of_addXYZ_not_span`).

Both cases of the argument are short, and neither needs the second
addition law:

* where the standard law is non-degenerate, the two sums are
  `addXYZ P Q` and `addXYZ Q P`, which differ by the unit `-1`
  (`projAddXYZ_comm`), so `ProjCoords.toHom_smul` identifies them;
* where it degenerates, the two points are EQUAL
  (`ProjCoords.toHom_eq_of_addXYZ_not_span`) and commutativity is
  trivial.

This is the precise sense in which `hcomm` — alone among the three axioms
of the old leaf — is genuinely cheap.

**The `[Field K]` binder was replaced by `(hK : IsField ↥K)` on 2026-07-27**, in
step with the two `ProjCoords` leaves this consumes; see the FALSITY AUDIT on
`ProjCoords.exists_of_specField`.  The one caller, `exists_projMul`, supplies
`Field.toIsField _` at `Scheme.residueField x`, where the `Field` instance really
is the `CommRingCat` structure. -/
theorem projMulCoords_comm (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hlaw : ∀ (X : Scheme.{0}) (c d : ProjCoords E X)
      (h : Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤),
      Limits.pullback.lift c.toHom d.toHom (hom_ext_spec_rat _ _) ≫ m = (c.add d h).toHom)
    (K : CommRingCat.{0}) (hK : _root_.IsField ↥K) (a b : Spec K ⟶ proj E) :
    Limits.pullback.lift b a (hom_ext_spec_rat _ _) ≫ m =
      Limits.pullback.lift a b (hom_ext_spec_rat _ _) ≫ m := by
  obtain ⟨c, rfl⟩ := ProjCoords.exists_of_specField E K hK a
  obtain ⟨d, rfl⟩ := ProjCoords.exists_of_specField E K hK b
  by_cases h : Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤
  · have hcomm : addXYZ (E.map d.base) d.coord c.coord =
        ((-1 : (Γ(Spec K, ⊤))ˣ) : Γ(Spec K, ⊤)) • addXYZ (E.map c.base) c.coord d.coord := by
      rw [d.base_eq c, projAddXYZ_comm]
      simp
    have h' : Ideal.span (Set.range (addXYZ (E.map d.base) d.coord c.coord)) = ⊤ := by
      rw [hcomm, span_range_smul_unit]
      exact h
    rw [hlaw _ d c h', hlaw _ c d h]
    have hEq : ProjCoords.smul (-1 : (Γ(Spec K, ⊤))ˣ) (c.add d h) = d.add c h' :=
      ProjCoords.ext (by simp [hcomm])
    rw [← hEq, ProjCoords.toHom_smul]
  · rw [ProjCoords.toHom_eq_of_addXYZ_not_span hK c d h]

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

/-- **The operation `m` induces on `T`-points** (PROVEN, definitional).

A pair of `T`-points `P, Q : T ⟶ proj E` automatically lies over the same
base point (`hom_ext_spec_rat`, the base being `Spec ℚ`), so it lifts to a
`T`-point of `A ×_ℚ A` and may be fed to `m`.  This is the operation whose
associativity is the whole content of `projMul_assoc`, and stating it
separately is what lets that content be written as a plain algebraic
identity rather than as an equation between two composites out of a
threefold fibre product. -/
noncomputable def projMulPt (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    {T : Scheme.{0}} (P Q : T ⟶ proj E) : T ⟶ proj E :=
  Limits.pullback.lift P Q (hom_ext_spec_rat _ _) ≫ m

/-- **Naturality of `pullback.lift` into `A ×_ℚ A` in the source**
(PROVEN, formal).

Over the base `Spec ℚ` the pullback condition is automatic, so the two
`lift`s below differ only in a proof argument and precomposition may be
pushed inside.  This is the one piece of glue the residue-field reduction
needs, and it is stated separately because it is used three times.

*Implementation note*: the `rw` uses `Category.assoc` in the FORWARD
direction.  `Limits.pullback.hom_ext` leaves its goals LEFT-associated —
`(s ≫ lift P Q h) ≫ fst` — and neither `simp` nor `rw [← Category.assoc]`
makes progress on that shape; `rw [Category.assoc]` followed by
`lift_fst` does.  This cost a verification cycle, so it is recorded. -/
theorem comp_lift_proj (E : WeierstrassCurve ℚ)
    {T T' : Scheme.{0}} (s : T' ⟶ T) (P Q : T ⟶ proj E) (h h') :
    s ≫ Limits.pullback.lift (f := projToSpec E) (g := projToSpec E) P Q h =
      Limits.pullback.lift (s ≫ P) (s ≫ Q) h' := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]
  · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd]

/-- **`triAddLeft` read at a `T`-point is `(P · Q) · R`** (PROVEN, formal). -/
theorem comp_triAddLeft_proj (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    {T : Scheme.{0}} (s : T ⟶ AbelianSchemeStruct.triProd (projToSpec E)) :
    s ≫ AbelianSchemeStruct.triAddLeft (projToSpec E) m (hom_ext_spec_rat _ _) =
      projMulPt E m
        (projMulPt E m (s ≫ AbelianSchemeStruct.triFst (projToSpec E))
          (s ≫ AbelianSchemeStruct.triSnd (projToSpec E)))
        (s ≫ AbelianSchemeStruct.triThd (projToSpec E)) := by
  rw [AbelianSchemeStruct.triAddLeft, ← Category.assoc,
    comp_lift_proj E s _ _ _ (hom_ext_spec_rat _ _), projMulPt, projMulPt, ← Category.assoc,
    comp_lift_proj E s _ _ _ (hom_ext_spec_rat _ _)]

/-- **`triAddRight` read at a `T`-point is `P · (Q · R)`** (PROVEN, formal). -/
theorem comp_triAddRight_proj (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    {T : Scheme.{0}} (s : T ⟶ AbelianSchemeStruct.triProd (projToSpec E)) :
    s ≫ AbelianSchemeStruct.triAddRight (projToSpec E) m (hom_ext_spec_rat _ _) =
      projMulPt E m (s ≫ AbelianSchemeStruct.triFst (projToSpec E))
        (projMulPt E m (s ≫ AbelianSchemeStruct.triSnd (projToSpec E))
          (s ≫ AbelianSchemeStruct.triThd (projToSpec E))) := by
  rw [AbelianSchemeStruct.triAddRight, ← Category.assoc,
    comp_lift_proj E s _ _ _ (hom_ext_spec_rat _ _), projMulPt, projMulPt, ← Category.assoc,
    comp_lift_proj E s _ _ _ (hom_ext_spec_rat _ _)]

/-- **`Spec` of a field extension is an epimorphism of schemes** (PROVEN,
formal).

*Docstring repair, 2026-07-27*: this header previously read "Associativity
of the operation `m` induces on `K`-points, `K` a field (sorry node …)",
which belongs to `projMul_assoc_pt` below and had been left attached to
this lemma by an earlier edit.  It is a stale `(sorry node)` LABEL of
exactly the kind that generates phantom dispatches — this declaration is
proven and always was.

If `φ : K ⟶ L` is a homomorphism of FIELDS then `Spec φ` may be cancelled
on the left: two morphisms `Spec K ⟶ X` that agree after restriction to
`Spec L` are equal.  This is what lets a statement about `K`-points be
reduced to the same statement about `K̄`-points, which is how
`projMul_assoc_pt` reaches `projMul_assoc_pt_algClosed` below.

The proof is `AlgebraicGeometry.Scheme.SpecToEquivOfField`
(`Mathlib/AlgebraicGeometry/ResidueField.lean`), which identifies
`Spec K ⟶ X` with a point `x : X` together with an embedding
`κ(x) ⟶ K`.  Under that identification precomposition with `Spec φ` is
POSTcomposition with `φ` on the embedding, and `φ` is a monomorphism
because a ring homomorphism out of a field is injective.  So the whole
content is `cancel_mono`.

*Implementation note*, and it is the reason this file now imports
`Mathlib.AlgebraicGeometry.ResidueField` explicitly: `SpecToEquivOfField`
is stated for a bare `K : Type` carrying `[Field K]`, so the `CommRingCat`
it produces is `CommRingCat.of K` built from `Field.toCommRing`.  See the
INSTANCE-COHERENCE note on `projMul_assoc_pt` for why that phrasing is
forced. -/
theorem hom_ext_of_specMap_field {X : Scheme.{0}} {K L : Type} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) (f g : Spec (CommRingCat.of K) ⟶ X)
    (h : Spec.map φ ≫ f = Spec.map φ ≫ g) : f = g := by
  obtain ⟨⟨x, α⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective f
  obtain ⟨⟨y, β⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 : (⟨x, α ≫ φ⟩ : Σ z : X.carrier, X.residueField z ⟶ CommRingCat.of L)
      = ⟨y, β ≫ φ⟩ := by
    apply (X.SpecToEquivOfField L).symm.injective
    simpa only [Scheme.SpecToEquivOfField_symm_apply] using h
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp h2
  haveI : Mono φ := ConcreteCategory.mono_of_injective _ φ.hom.injective
  have hαβ : α = (X.residueFieldCongr e).hom ≫ β := by
    rw [← cancel_mono φ, Category.assoc]
    exact he
  have hfin : (⟨x, α⟩ : Σ z : X.carrier, X.residueField z ⟶ CommRingCat.of K) = ⟨y, β⟩ :=
    Scheme.SpecToEquivOfField_eq_iff.mpr ⟨e, hαβ⟩
  exact congrArg (X.SpecToEquivOfField K).symm hfin

/-- **The operation `m` induces on points is natural in the test scheme**
(PROVEN, formal).

`projMulPt` is `pullback.lift P Q _ ≫ m`, so precomposing with
`s : T' ⟶ T` is `comp_lift_proj` and nothing else.  This is what makes the
descent to an algebraic closure in `projMul_assoc_pt` a rewrite rather
than an argument. -/
theorem comp_projMulPt (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    {T T' : Scheme.{0}} (s : T' ⟶ T) (P Q : T ⟶ proj E) :
    s ≫ projMulPt E m P Q = projMulPt E m (s ≫ P) (s ≫ Q) := by
  rw [projMulPt, projMulPt, ← Category.assoc,
    comp_lift_proj E s _ _ _ (hom_ext_spec_rat _ _)]

/-- **`hcomm` read at points: the induced operation is commutative**
(PROVEN, formal).

`hcomm` says `m` is invariant under the swap of `A ×_ℚ A`; composing
`pullback.lift P Q` with that swap is `pullback.lift Q P`, which
`pullback.hom_ext` settles componentwise. -/
theorem projMulPt_comm (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hcomm : Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
      (Limits.pullback.fst (projToSpec E) (projToSpec E))
      Limits.pullback.condition.symm ≫ m = m)
    {T : Scheme.{0}} (P Q : T ⟶ proj E) :
    projMulPt E m P Q = projMulPt E m Q P := by
  have key : Limits.pullback.lift P Q (hom_ext_spec_rat _ _) ≫
      Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
        (Limits.pullback.fst (projToSpec E) (projToSpec E))
        Limits.pullback.condition.symm
      = Limits.pullback.lift Q P (hom_ext_spec_rat _ _) := by
    apply Limits.pullback.hom_ext <;>
      simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_snd]
  rw [projMulPt, projMulPt]
  conv_lhs => rw [← hcomm]
  rw [← Category.assoc, key]

/-- **`hunit` read at points: the unit is `projInfty E`** (PROVEN, formal).

The unit `T`-point is `P ≫ projToSpec E ≫ projInfty E`; it does not
actually depend on `P`, because `hom_ext_spec_rat` makes every
`P ≫ projToSpec E` the same morphism `T ⟶ Spec ℚ`.  Writing it this way
keeps the statement self-contained — a bare `T ⟶ Spec ℚ` need not exist
for an arbitrary `T`, but it does as soon as `T` carries one point of
`proj E`. -/
theorem projMulPt_unit_left (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hunit : Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E))
    {T : Scheme.{0}} (P : T ⟶ proj E) :
    projMulPt E m (P ≫ projToSpec E ≫ projInfty E) P = P := by
  have h := congrArg (fun t => P ≫ t) hunit
  simp only [← Category.assoc, comp_lift_proj E P _ _ _ (hom_ext_spec_rat _ _)] at h
  rw [projMulPt]
  simpa using h

/-- **`hinv` read at points: `projNeg E` is a two-sided inverse**
(PROVEN, formal).  Two-sided because `projMulPt_comm` is available. -/
theorem projMulPt_neg_left (E : WeierstrassCurve ℚ)
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hinv : Limits.pullback.lift (projNeg E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E)
    {T : Scheme.{0}} (P : T ⟶ proj E) :
    projMulPt E m (P ≫ projNeg E) P = P ≫ projToSpec E ≫ projInfty E := by
  have h := congrArg (fun t => P ≫ t) hinv
  simp only [← Category.assoc, comp_lift_proj E P _ _ _ (hom_ext_spec_rat _ _)] at h
  rw [projMulPt]
  simpa using h

/-- **A commutative loop operation on a 2-divisible abelian group that is
AFFINE in each variable IS the group addition** (PROVEN — pure group
theory, no geometry, no `sorry` anywhere in its cone).

This is the combinatorial half of `projMul_assoc_pt_algClosed`, isolated
here so that the geometric half can be one clean interface
(`exists_projPtAddEquiv_algClosed` below).  `F` is the operation
transported to an abelian group `G`; `halg` is the ALGEBRAICITY input —
for each fixed `y` the map `x ↦ F x y` is a group homomorphism plus a
constant.  For a morphism of a smooth projective genus-`1` curve to
itself that is Silverman *AEC* III.4.7 ("every morphism is a translation
composed with an isogeny"); a CONSTANT morphism is covered too, as the
zero homomorphism plus a constant, so `halg` needs no non-degeneracy
hypothesis and the interface below needs no case split.

## Why the three loop identities alone are NOT enough, and what closes the gap

`hsymm`/`hzero`/`hneg` say exactly that `F` is a commutative loop with
two-sided unit and inverses, and the smallest non-associative commutative
loop has order `5` — so those three are consistent with
non-associativity, which is the refutation recorded at
`projMul_assoc_pt_algClosed`.  `halg` plus `hdiv` is what breaks it, and
the argument is short enough to record in full:

* write `F x y = α y x + y` with `α y : G →+ G` (the constant is pinned to
  `y` by `hzero`, evaluating `halg` at `x = 0`);
* `B x y := α y x - x` is additive in `x` (a difference of two additive
  maps) and SYMMETRIC — `hsymm` rearranged is exactly
  `α y x - x = α x y - y` — hence additive in `y` as well: `B` is a
  symmetric biadditive form;
* `hneg` gives `α x (-x) + x = 0`, i.e. `α x x = x`, i.e. `B` vanishes on
  the diagonal;
* expanding `B (x + y) (x + y) = 0` biadditively therefore leaves
  `B x y + B y x = 0`, i.e. `2 • B x y = 0`;
* `hdiv` kills that residue: `B x y = B (z + z) y = 2 • B z y = 0`.

So `α y = id` for every `y`, and `F x y = x + y`.

**`hdiv` is not decorative.** Without it `B` may be a nonzero symmetric
biadditive form with values in `G[2]`, and `G[2] ≅ (ℤ/2)²` for an
elliptic curve, so the conclusion genuinely fails for a non-divisible
`G`.  Divisibility is the ONE place algebraic closedness of the base
field enters this half of the argument: `E(K̄)` is a divisible group. -/
theorem commLoop_eq_add_of_addHom {G : Type*} [AddCommGroup G] (F : G → G → G)
    (hsymm : ∀ x y, F x y = F y x)
    (hzero : ∀ y, F 0 y = y)
    (hneg : ∀ x, F (-x) x = 0)
    (hdiv : ∀ x : G, ∃ z, x = z + z)
    (halg : ∀ y : G, ∃ (α : G →+ G) (c : G), ∀ x, F x y = α x + c) :
    ∀ x y, F x y = x + y := by
  choose α c hαc using halg
  -- The constant is `y` itself, by `hzero` at `x = 0`.
  have hc : ∀ y, c y = y := by
    intro y
    have h := hαc y 0
    rw [hzero, map_zero, zero_add] at h
    exact h.symm
  have hF : ∀ x y, F x y = α y x + y := by
    intro x y; rw [hαc y x, hc y]
  -- `B` is symmetric, biadditive, and vanishes on the diagonal.
  set B : G → G → G := fun x y => α y x - x with hB
  have hBsymm : ∀ x y, B x y = B y x := by
    intro x y
    have h := hsymm x y
    rw [hF x y, hF y x] at h
    simp only [hB]
    linear_combination (norm := abel) h
  have hBadd : ∀ x x' y, B (x + x') y = B x y + B x' y := by
    intro x x' y
    simp only [hB, map_add]
    abel
  have hBself : ∀ x, B x x = 0 := by
    intro x
    have h := hneg x
    rw [hF (-x) x, map_neg] at h
    simp only [hB]
    linear_combination (norm := abel) -h
  -- Expanding `B (x + y) (x + y) = 0` leaves `2 • B x y = 0`.
  have htwo : ∀ x y, B x y + B x y = 0 := by
    intro x y
    have h := hBself (x + y)
    rw [hBadd x y (x + y), hBsymm x (x + y), hBsymm y (x + y), hBadd x y x, hBadd x y y,
      hBself x, hBself y] at h
    rw [hBsymm x y] at h ⊢
    linear_combination (norm := abel) h
  -- Divisibility kills it.
  have hBzero : ∀ x y, B x y = 0 := by
    intro x y
    obtain ⟨z, rfl⟩ := hdiv x
    rw [hBadd z z y]
    exact htwo z y
  intro x y
  have hxy := hBzero x y
  simp only [hB, sub_eq_zero] at hxy
  rw [hF x y, hxy]

/-! ## THE `Spec K`-POINT DICTIONARY, AS DATA

(Written 2026-07-27, and it is the shared implementation the "ONE DICTIONARY, THREE
LEAVES" note at `exists_projMul_geomFibreEquivVal` prescribes.)

Both `exists_projPtAddEquiv_algClosed` (immediately below) and
`exists_projMul_geomFibreEquivVal` (item 8) assert the existence of a bijection between
the `K`-points of `proj E` and `E(K)`, each carrying its own extra content.  Neither
implies the other and their STATEMENTS cannot be merged — each has to *name* the
bijection to state its extra content, and an existential closes over it; quantifying the
extra content over every bijection satisfying the shared clauses is outright FALSE.

What they share is the IMPLEMENTATION, and a shared implementation has to be DATA.  This
section is that data: `ProjCoords.specPointEquiv` is a `def`, not an `∃`, so both leaves
can name it, and no third `∃ e : … ≃ …` leaf is created.

The construction is exactly the one the route note prescribes —
`ProjCoords.exists_of_specField` (surjectivity) + `ProjCoords.toHom_smul` and its new
converse `ProjCoords.exists_units_smul_of_toHom_eq` (injectivity) + mathlib's
`WeierstrassCurve.Projective.Point.toAffineAddEquiv`.  Everything in this section is
PROVEN; the two `ProjCoords`-level statements it consumes are the leaves named above.

*Import note*: this section is why `Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point`
is imported.  `Projective/Basic` (which the file already had, through
`ProjectiveAddition`) has `Equation`/`Nonsingular` but neither `Projective.Point` nor
`toAffineAddEquiv`. -/

namespace ProjCoords

variable {E : WeierstrassCurve ℚ} {K : Type} [Field K]

/-- `Γ(Spec K, ⊤) ≃+* K` — the transport used throughout this section.  It is the same
ring equivalence `ProjCoords.toHom_eq_of_addXYZ_not_span` uses to see `Γ(Spec K, ⊤)` as a
field, packaged as a `def` so that `simp` cannot unfold it into `Scheme.ΓSpecIso`. -/
noncomputable def gammaSpecEquiv (K : Type) [Field K] :
    Γ(Spec (CommRingCat.of K), ⊤) ≃+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv

/-- **The `K`-valued coordinate triple** of a coordinate datum over `Spec K` (PROVEN,
definitional).  `ProjCoords.coord` lands in `Γ(Spec K, ⊤)`; this is the same triple read
in `K` itself, which is where mathlib's projective-point API lives. -/
noncomputable def coordField (c : ProjCoords E (Spec (CommRingCat.of K))) : Fin 3 → K :=
  fun i => gammaSpecEquiv K (c.coord i)

theorem coordField_def (c : ProjCoords E (Spec (CommRingCat.of K))) :
    coordField c = (gammaSpecEquiv K).toRingHom ∘ c.coord := rfl

/-- **The `K`-triple satisfies the Weierstrass equation of `E` over `K`** (PROVEN).
`f` is unconstrained because `ℚ →+* K` is a subsingleton, so it is necessarily
`gammaSpecEquiv ∘ c.base`. -/
theorem equation_coordField (f : ℚ →+* K) (c : ProjCoords E (Spec (CommRingCat.of K))) :
    Equation (E.map f) (coordField c) := by
  have hb : f = ((gammaSpecEquiv K).toRingHom.comp c.base) := Subsingleton.elim _ _
  rw [hb, ← WeierstrassCurve.map_map, coordField_def]
  exact WeierstrassCurve.Projective.Equation.map _ c.equation

/-- **The `K`-triple is not identically zero** (PROVEN) — this is `span_coord = ⊤` read
in `K`. -/
theorem exists_coordField_ne_zero (c : ProjCoords E (Spec (CommRingCat.of K))) :
    ∃ i, coordField c i ≠ 0 := by
  by_contra h
  push_neg at h
  have hc : ∀ i, c.coord i = 0 := by
    intro i
    have := h i
    simpa [coordField] using (gammaSpecEquiv K).map_eq_zero_iff.mp this
  have h1 : Ideal.span (Set.range c.coord) ≤ (⊥ : Ideal Γ(Spec (CommRingCat.of K), ⊤)) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    simp [hc i]
  rw [c.span_coord] at h1
  have h2 : (1 : Γ(Spec (CommRingCat.of K), ⊤)) = 0 := Ideal.mem_bot.mp (h1 trivial)
  haveI : Nontrivial Γ(Spec (CommRingCat.of K), ⊤) := (gammaSpecEquiv K).toEquiv.nontrivial
  exact one_ne_zero h2

/-- **A coordinate datum reconstructed from a `K`-triple** (PROVEN) — the inverse of
`coordField`, and the reason this section needs no separate surjectivity leaf. -/
noncomputable def ofTriple (f : ℚ →+* K) {v : Fin 3 → K}
    (hv : Equation (E.map f) v) (hne : ∃ i, v i ≠ 0) :
    ProjCoords E (Spec (CommRingCat.of K)) where
  base := (gammaSpecEquiv K).symm.toRingHom.comp f
  coord := fun i => (gammaSpecEquiv K).symm (v i)
  equation :=
    WeierstrassCurve.Projective.Equation.map (W' := E.map f) (gammaSpecEquiv K).symm.toRingHom hv
  span_coord := by
    obtain ⟨i, hi⟩ := hne
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self i)) ?_
    exact IsUnit.map (gammaSpecEquiv K).symm.toRingHom hi.isUnit

@[simp] theorem coordField_ofTriple (f : ℚ →+* K) {v : Fin 3 → K}
    (hv : Equation (E.map f) v) (hne : ∃ i, v i ≠ 0) :
    coordField (E := E) (ofTriple f hv hne) = v := by
  funext i
  simp [coordField, ofTriple]

theorem coordField_injective (c d : ProjCoords E (Spec (CommRingCat.of K)))
    (h : coordField c = coordField d) : c = d := by
  refine ProjCoords.ext ?_
  funext i
  have := congrFun h i
  simpa [coordField] using (gammaSpecEquiv K).injective this

theorem coordField_smul (u : (Γ(Spec (CommRingCat.of K), ⊤))ˣ)
    (c : ProjCoords E (Spec (CommRingCat.of K))) :
    coordField (ProjCoords.smul u c) =
      (gammaSpecEquiv K (u : Γ(Spec (CommRingCat.of K), ⊤))) • coordField c := by
  funext i
  simp [coordField, ProjCoords.smul]

/-- **Nonsingularity is AUTOMATIC on an elliptic curve** (PROVEN): a `K`-triple that
satisfies the Weierstrass equation and is not identically zero is nonsingular.

This is what lets the whole dictionary be phrased with `ProjCoords` — whose
non-degeneracy condition is `span_coord = ⊤`, i.e. "not all zero" — while mathlib's
projective-point API is phrased with `Nonsingular`.  Both cases are short: at `Z = 0` the
equation forces `X = 0`, so `Y ≠ 0` and the `Y`-partial is `Y² ≠ 0`; at `Z ≠ 0` it is
mathlib's `Affine.equation_iff_nonsingular`, which is exactly `Δ ≠ 0`. -/
theorem nonsingular_of_equation_of_ne_zero [E.IsElliptic] (f : ℚ →+* K) {v : Fin 3 → K}
    (hv : Equation (E.map f) v) (hne : ∃ i, v i ≠ 0) : Nonsingular (E.map f) v := by
  by_cases hz : v (2 : Fin 3) = 0
  · have hx : v (0 : Fin 3) = 0 := X_eq_zero_of_Z_eq_zero hv hz
    have hy : v (1 : Fin 3) ≠ 0 := by
      obtain ⟨i, hi⟩ := hne
      fin_cases i
      · exact absurd hx hi
      · exact hi
      · exact absurd hz hi
    rw [nonsingular_of_Z_eq_zero hz]
    refine ⟨hv, Or.inr ?_⟩
    simp only [hx, mul_zero, zero_mul, add_zero]
    simpa using pow_ne_zero 2 hy
  · rw [nonsingular_of_Z_ne_zero hz]
    exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((equation_of_Z_ne_zero hz).mp hv)

/-- The converse direction: a nonsingular triple is not identically zero (PROVEN — all
three partials vanish at the origin). -/
theorem exists_ne_zero_of_nonsingular {W : WeierstrassCurve K} {v : Fin 3 → K}
    (hv : Nonsingular W v) : ∃ i, v i ≠ 0 := by
  by_contra h
  push_neg at h
  rw [nonsingular_iff] at hv
  simp [h 0, h 1, h 2] at hv

/-- **The affine `K`-point of a coordinate datum** (PROVEN) — mathlib's total
`Projective.Point.toAffine` applied to `coordField`.  Totality is deliberate: it makes
this a plain function, with no side condition to carry through the equivalence below. -/
noncomputable def affinePoint (f : ℚ →+* K) (c : ProjCoords E (Spec (CommRingCat.of K))) :
    (E.map f).toAffine.Point :=
  WeierstrassCurve.Projective.Point.toAffine (E.map f) (coordField c)

/-- **Every affine `K`-point comes from a coordinate datum** (PROVEN, from
`toAffineAddEquiv.right_inv`). -/
theorem exists_affinePoint_eq [E.IsElliptic] (f : ℚ →+* K) (P : (E.map f).toAffine.Point) :
    ∃ c : ProjCoords E (Spec (CommRingCat.of K)), affinePoint f c = P := by
  classical
  set Q : WeierstrassCurve.Projective.Point (E.map f) :=
    WeierstrassCurve.Projective.Point.fromAffine P with hQ
  obtain ⟨v, hv⟩ := Quotient.exists_rep Q.point
  have hns : NonsingularLift (E.map f) ⟦v⟧ := hv ▸ Q.nonsingular
  have hnsv : Nonsingular (E.map f) v := (nonsingularLift_iff v).mp hns
  refine ⟨ofTriple f hnsv.left (exists_ne_zero_of_nonsingular hnsv), ?_⟩
  have hQeq : (⟨hns⟩ : WeierstrassCurve.Projective.Point (E.map f)) = Q :=
    WeierstrassCurve.Projective.Point.ext hv
  calc affinePoint f (ofTriple f hnsv.left (exists_ne_zero_of_nonsingular hnsv))
      = WeierstrassCurve.Projective.Point.toAffine (E.map f) v := by
        rw [affinePoint, coordField_ofTriple]
    _ = WeierstrassCurve.Projective.Point.toAffineLift
          (⟨hns⟩ : WeierstrassCurve.Projective.Point (E.map f)) := rfl
    _ = WeierstrassCurve.Projective.Point.toAffineLift Q := by rw [hQeq]
    _ = P := (WeierstrassCurve.Projective.Point.toAffineAddEquiv (E.map f)).right_inv P

/-- **Two coordinate data with the same affine point induce the same morphism** (PROVEN,
from `toAffineAddEquiv.left_inv` and `ProjCoords.toHom_smul`) — the direction of the
dictionary that needs NO new leaf, because mathlib's equivalence already says a
nonsingular triple is determined by its affine point up to a unit. -/
theorem toHom_eq_of_affinePoint_eq [E.IsElliptic] (f : ℚ →+* K)
    (c d : ProjCoords E (Spec (CommRingCat.of K))) (h : affinePoint f c = affinePoint f d) :
    c.toHom = d.toHom := by
  classical
  have hc := nonsingular_of_equation_of_ne_zero f (equation_coordField f c)
    (exists_coordField_ne_zero c)
  have hd := nonsingular_of_equation_of_ne_zero f (equation_coordField f d)
    (exists_coordField_ne_zero d)
  have hcl : NonsingularLift (E.map f) ⟦coordField c⟧ := (nonsingularLift_iff _).mpr hc
  have hdl : NonsingularLift (E.map f) ⟦coordField d⟧ := (nonsingularLift_iff _).mpr hd
  have hpt : (⟨hcl⟩ : WeierstrassCurve.Projective.Point (E.map f)) = ⟨hdl⟩ := by
    apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv (E.map f)).injective
    exact h
  have heq : (⟦coordField c⟧ : PointClass K) = ⟦coordField d⟧ := congrArg (·.point) hpt
  obtain ⟨u, hu⟩ := Quotient.exact heq
  set u' : (Γ(Spec (CommRingCat.of K), ⊤))ˣ :=
    Units.map (gammaSpecEquiv K).symm.toRingHom.toMonoidHom u with hu'
  have hsm : ProjCoords.smul u' d = c := by
    refine coordField_injective _ _ ?_
    rw [coordField_smul]
    have : gammaSpecEquiv K (u' : Γ(Spec (CommRingCat.of K), ⊤)) = (u : K) := by
      simp [hu']
    rw [this]
    exact hu
  rw [← hsm, ProjCoords.toHom_smul]

/-- The converse of the previous lemma (PROVEN from
`ProjCoords.exists_units_smul_of_toHom_eq` and `toAffine_smul`). -/
theorem affinePoint_eq_of_toHom_eq (f : ℚ →+* K)
    (c d : ProjCoords E (Spec (CommRingCat.of K))) (h : c.toHom = d.toHom) :
    affinePoint f c = affinePoint f d := by
  obtain ⟨u, hu⟩ :=
    exists_units_smul_of_toHom_eq (K' := CommRingCat.of K) (Field.toIsField K) c d h
  rw [affinePoint, affinePoint, ← hu, coordField_smul]
  exact (WeierstrassCurve.Projective.Point.toAffine_smul (W := E.map f) (coordField c)
    (u.isUnit.map (gammaSpecEquiv K).toRingHom)).symm

/-- **THE DICTIONARY** (PROVEN): the `K`-points of the projective Weierstrass model ARE
the affine points of `E` over `K`, for every field `K` admitting a `ℚ`-algebra structure.

This is the shared implementation of `exists_projPtAddEquiv_algClosed` and
`exists_projMul_geomFibreEquivVal`.  It is a `def` — the dictionary as DATA — precisely so
that the extra content each of those leaves carries can be stated ABOUT it; an
existentially bound bijection could not be named, and quantifying over all bijections
satisfying the shared clauses is false.

Surjectivity is `ProjCoords.exists_of_specField` plus `exists_affinePoint_eq`;
injectivity is `toHom_eq_of_affinePoint_eq`; the `right_inv` field is where
`ProjCoords.exists_units_smul_of_toHom_eq` is consumed, through
`affinePoint_eq_of_toHom_eq`.

There is no characteristic guard here and none is needed: `f : ℚ →+* K` is a HYPOTHESIS,
so `char K = p > 0` simply cannot occur.  A consumer that has only `Nonempty (Spec K ⟶ proj E)`
manufactures `f` from any such point, which is what `exists_projPtAddEquiv_algClosed` does. -/
noncomputable def specPointEquiv [E.IsElliptic] (f : ℚ →+* K) :
    (Spec (CommRingCat.of K) ⟶ proj E) ≃ (E.map f).toAffine.Point := by
  classical
  refine Equiv.ofBijective (fun a => affinePoint f
    (Classical.choose (ProjCoords.exists_of_specField E (CommRingCat.of K)
      (Field.toIsField K) a))) ⟨?_, ?_⟩
  · intro a b hab
    have ha := Classical.choose_spec
      (ProjCoords.exists_of_specField E (CommRingCat.of K) (Field.toIsField K) a)
    have hb := Classical.choose_spec
      (ProjCoords.exists_of_specField E (CommRingCat.of K) (Field.toIsField K) b)
    rw [← ha, ← hb]
    exact toHom_eq_of_affinePoint_eq f _ _ hab
  · intro P
    obtain ⟨c, hc⟩ := exists_affinePoint_eq f P
    refine ⟨c.toHom, ?_⟩
    have h := Classical.choose_spec
      (ProjCoords.exists_of_specField E (CommRingCat.of K) (Field.toIsField K) c.toHom)
    rw [← hc]
    exact affinePoint_eq_of_toHom_eq f _ _ h

/-- **The dictionary read on a coordinate datum** (PROVEN) — the computation rule that
makes `specPointEquiv` usable, since its definition goes through `Equiv.ofBijective` and
a choice. -/
theorem specPointEquiv_toHom [E.IsElliptic] (f : ℚ →+* K)
    (c : ProjCoords E (Spec (CommRingCat.of K))) :
    specPointEquiv f c.toHom = affinePoint f c := by
  classical
  have h := Classical.choose_spec
    (ProjCoords.exists_of_specField E (CommRingCat.of K) (Field.toIsField K) c.toHom)
  exact affinePoint_eq_of_toHom_eq f _ _ h

theorem specPointEquiv_symm_affinePoint [E.IsElliptic] (f : ℚ →+* K)
    (c : ProjCoords E (Spec (CommRingCat.of K))) :
    (specPointEquiv f).symm (affinePoint f c) = c.toHom := by
  rw [← specPointEquiv_toHom f c, Equiv.symm_apply_apply]

end ProjCoords

/-! ## The four clauses of `exists_projPtAddEquiv_algClosed`, as separate leaves

With the dictionary constructed, what is left of that leaf is exactly its four clauses,
each stated ABOUT `ProjCoords.specPointEquiv` (which is legitimate because it is a `def`).
Two of them — the unit section and the negation — are ONE missing piece of mathlib, and it
is worth naming it so that a successor factors it out rather than proving it twice:

> **Missing congruence.** `AlgebraicGeometry.Proj.fromOfGlobalSections` has NO
> functoriality lemma at this pin (`ProjectiveSpectrum/Basic.lean` has only
> `_preimage_basicOpen`, `_morphismRestrict`, `_resLE`, `_toSpecZero`).  What is wanted is
> `g ≫ Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 (Γ(g) ∘ f) _`
> (naturality in the source scheme) and
> `Proj.fromOfGlobalSections 𝒜 f hf ≫ Proj.map φ hφ = Proj.fromOfGlobalSections 𝒜 (f ∘ φ) _`
> (compatibility with `Proj.map`).  Both are cover-wise arguments of exactly the shape of
> `ProjCoords.fromOfGlobalSections_eq_of_gradedSmul` above, which is already PROVEN modulo
> its own chart leaf, so the pattern to copy is in this file.

From the first: `projInfty` is `fromOfGlobalSections` at `![0, 1, 0]`, so the unit-section
clause is `toAffine_zero`; and the Galois clause of `exists_projMul_geomFibreEquivVal` is
the same lemma at `g = specGal σ`, where `Γ(Spec σ) = σ`.  From the second: `projNeg` is
`Proj.map` of the graded involution `Y ↦ -Y - a₁X - a₃Z`, which is mathlib's
`Projective.neg` on coordinates, so the negation clause is `toAffine_neg`.

The other two clauses are genuine mathematics and are unrelated to each other. -/

/-- **The unit section is the zero of `E(K)`** (sorry node, introduced 2026-07-27 as
clause 1 of `exists_projPtAddEquiv_algClosed`).

`P ≫ projToSpec E` is THE structure morphism `Spec K ⟶ Spec ℚ` (`hom_ext_spec_rat`: there
is only one), so the left-hand side is the base change of `projInfty E`, the point
`[0 : 1 : 0]`.  Route: `projInfty` is by definition
`Proj.fromOfGlobalSections` of the coordinates `![0, 1, 0]`, so by the naturality lemma
named above it is `ProjCoords.toHom` of the datum with `coordField = ![0, 1, 0]`; then
`ProjCoords.specPointEquiv_toHom` and mathlib's `toAffine_zero` finish. -/
theorem specPointEquiv_comp_projInfty_eq_zero {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {K : Type} [Field K] (f : ℚ →+* K) (_P : Spec (CommRingCat.of K) ⟶ proj E) :
    ProjCoords.specPointEquiv f (_P ≫ projToSpec E ≫ projInfty E) = 0 :=
  sorry

/-- **`projNeg` is negation on `E(K)`** (sorry node, introduced 2026-07-27 as clause 2 of
`exists_projPtAddEquiv_algClosed`).

`projNeg E` is `Proj.map` of the graded involution `Y ↦ -Y - a₁X - a₃Z`, which on
coordinates is mathlib's `WeierstrassCurve.Projective.neg`.  Route: the `Proj.map`
congruence named above turns `c.toHom ≫ projNeg E` into `ProjCoords.toHom` of the datum
with `coordField = neg (coordField c)`, and then mathlib's `toAffine_neg` (which needs
`Nonsingular`, supplied by `ProjCoords.nonsingular_of_equation_of_ne_zero`) is exactly the
conclusion. -/
theorem specPointEquiv_comp_projNeg {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {K : Type} [Field K] (f : ℚ →+* K) (_P : Spec (CommRingCat.of K) ⟶ proj E) :
    ProjCoords.specPointEquiv f (_P ≫ projNeg E) = -ProjCoords.specPointEquiv f _P :=
  sorry

/-- **`E(K)` is 2-divisible for `K` algebraically closed** (sorry node, introduced
2026-07-27 as clause 3 of `exists_projPtAddEquiv_algClosed`).

This is the ONE place algebraic closedness enters that leaf, and
`commLoop_eq_add_of_addHom` shows it cannot be dropped: without it the residue `B` of the
loop argument may be a nonzero symmetric biadditive form with values in `E[2] ≅ (ℤ/2)²`.

Standard proof: given `x ∈ E(K)`, halving `x` amounts to finding a point `z` with
`2z = x`; the `x`-coordinates of the halves are the roots of a degree-4 polynomial over
`K` (the `2`-division polynomial of the translate), which has a root because `K` is
algebraically closed, and the corresponding `y` is then a root of the quadratic
`Y² + a₁XY + a₃Y = X³ + …`, again solvable.  Nothing here involves the scheme `proj E` —
it is a statement about mathlib's `WeierstrassCurve.Affine.Point` alone, which is why it
is stated that way. -/
theorem exists_add_self_affinePoint_of_isAlgClosed {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K] (f : ℚ →+* K)
    (x : (E.map f).toAffine.Point) : ∃ z : (E.map f).toAffine.Point, x = z + z :=
  sorry

/-- **ALGEBRAICITY: every scheme morphism acts affinely on `K`-points** (sorry node,
introduced 2026-07-27 as clause 4 of `exists_projPtAddEquiv_algClosed`, and it is
Silverman *AEC* III.4.7).

This is the clause that distinguishes the dictionary from a bare bijection: the loop
counterexample of order `5` transported along an arbitrary bijection satisfies every other
clause and violates this one.  It quantifies over EVERY morphism of schemes
`n : A ×_ℚ A ⟶ A`, with no hypothesis on `n` at all.

*Why it is true, and why it needs no non-degeneracy case.* `P ↦ projMulPt E n P Q` is
induced by an honest `K`-morphism: base-change `n` along `Spec K ⟶ Spec ℚ` and precompose
with `(id, Q)`, giving `A_K ⟶ A_K` where `A_K = proj E ×_ℚ Spec K` is a smooth projective
geometrically integral genus-`1` curve over `K` with the rational point `projInfty`.
Silverman *AEC* III.4.7 says every NON-constant morphism of such a curve to itself is a
translation composed with an isogeny, i.e. `x ↦ α x + c` with `α` a group homomorphism; a
CONSTANT morphism is `x ↦ 0 + c`, also of that shape.

*Why the rigidity/Milne route is NOT available here* (and this is recorded so it is not
re-attempted): forming `h(v,w) - f(v) - g(w)` needs the group law on the TARGET as a
morphism, i.e. the `GrpObj` this whole cluster is constructing, and everything in
`Mathlib/AlgebraicGeometry/Group/Abelian.lean` assumes `[GrpObj G]`.  III.4.7 needs only
the SET-level group `E(K)`, which mathlib already has, so it breaks the circle. -/
theorem exists_addMonoidHom_specPointEquiv_projMulPt {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {K : Type} [Field K] [DecidableEq K] (f : ℚ →+* K)
    (_n : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (_Q : Spec (CommRingCat.of K) ⟶ proj E) :
    ∃ (α : (E.map f).toAffine.Point →+ (E.map f).toAffine.Point) (c : (E.map f).toAffine.Point),
      ∀ P : Spec (CommRingCat.of K) ⟶ proj E,
        ProjCoords.specPointEquiv f (projMulPt E _n P _Q) =
          α (ProjCoords.specPointEquiv f P) + c :=
  sorry

/-- **The `K`-points of the projective Weierstrass model carry an abelian
group structure with `projInfty` as zero and `projNeg` as negation, which
is divisible and on which EVERY scheme morphism acts affinely** (**PROVEN
2026-07-27** over `ProjCoords.specPointEquiv` and the four clause leaves
immediately above; it was the geometric content that
`projMul_assoc_pt_algClosed`
now rests on, and it is the classical half: a point dictionary plus
Silverman *AEC* III.4.7).

Read clause by clause, for `K` algebraically closed and admitting at
least one `K`-point of `proj E` (see the CHARACTERISTIC GUARD below):

* `e` is a bijection from `K`-points of the projective Weierstrass model
  to an abelian group `G` — concretely `G = (E⁄K).Point`, mathlib's
  `WeierstrassCurve.Affine.Point`, whose `AddCommGroup` instance is
  proven in mathlib from the ideal class group of the coordinate ring and
  therefore does **not** depend on anything this cluster is constructing.
  That is what makes this cut NON-CIRCULAR, and it is the reason the
  rigidity route recorded below cannot be used instead;
* `e` sends the unit section `P ≫ projToSpec E ≫ projInfty E` (the point
  `[0 : 1 : 0]`) to `0`, and postcomposition with `projNeg E` (the
  substitution `Y ↦ -Y - a₁X - a₃Z`) to negation — both are the standard
  Weierstrass identifications;
* `G` is **2-divisible**.  For `K` algebraically closed `[2] : E(K) → E(K)`
  is surjective, since the `2`-division polynomial has a root in `K`.
  This is the only clause where `IsAlgClosed K` is genuinely used, and
  `commLoop_eq_add_of_addHom` shows it cannot be dropped;
* the last clause is **ALGEBRAICITY**, and it is what distinguishes this
  interface from the bare dictionary that the audit on
  `projMul_assoc_pt_algClosed` correctly refutes.  It quantifies over
  EVERY morphism of schemes `n : A ×_ℚ A ⟶ A`, saying that the induced map
  `P ↦ n(P, Q)` on `K`-points is a group homomorphism plus a constant.
  A bijection alone satisfies nothing of the sort — the loop
  counterexample transported along an arbitrary bijection violates it —
  so this clause is exactly the "the dictionary has to carry
  algebraicity" requirement, discharged.

## WHY THE LAST CLAUSE IS TRUE (and why it needs no non-degeneracy case)

`P ↦ projMulPt E n P Q` is induced by an honest `K`-morphism: base-change
`n` along `Spec K ⟶ Spec ℚ` and precompose with `(id, Q)`, giving
`A_K ⟶ A_K` where `A_K = proj E ×_ℚ Spec K` is a smooth projective
geometrically integral genus-`1` curve over `K` with the rational point
`projInfty`.  Silverman *AEC* III.4.7 says every NON-constant morphism of
such a curve to itself is a translation composed with an isogeny, i.e.
`x ↦ α x + c` with `α` a group homomorphism; a CONSTANT morphism is
`x ↦ 0 + c`, also of that shape.  So the clause holds for every `n`, with
no hypothesis on `n` at all.

## CHARACTERISTIC GUARD — `hne` is a FAITHFULNESS fix, not a convenience

Without `hne` the statement is **FALSE**.  `proj E` lives over `Spec ℚ`,
so a morphism `Spec K ⟶ proj E` yields `Spec K ⟶ Spec (CommRingCat.of ℚ)`
and hence a ring map `ℚ → K`; when `char K = p > 0` there is none, so the
`K`-point set is EMPTY, while every `AddCommGroup` is inhabited by `0` —
no equivalence can exist.  `hne` makes the char-`p` instances vacuous and
costs the consumer nothing: `projMul_assoc_pt_algClosed` is handed three
`K`-points and supplies `hne` from one of them.

## COORDINATE WITH `exists_projMul_geomFibreEquivVal` — DISCHARGED 2026-07-27

The pairing note that used to sit here is now HISTORY: the shared
implementation it prescribed exists, as `ProjCoords.specPointEquiv`
above, and BOTH leaves are proven over it.  The conclusion it reached is
still the reason the code is shaped this way, so it is worth keeping in
one sentence: the two statements cannot be merged (each has to *name* the
bijection to state its own extra content, and quantifying that content
over every bijection satisfying the shared clauses is FALSE), so the
sharing has to happen at the level of DATA — a `def`, not an `∃`.

What survives of this leaf are its four clauses, and they are now four
named leaves immediately above:
`specPointEquiv_comp_projInfty_eq_zero`, `specPointEquiv_comp_projNeg`,
`exists_add_self_affinePoint_of_isAlgClosed` and
`exists_addMonoidHom_specPointEquiv_projMulPt`.  The first two are one
missing mathlib congruence for `Proj.fromOfGlobalSections` (see the
section header above, which names it); the last two are the genuinely
separate obligations — 2-divisibility of `E(K̄)`, and Silverman *AEC*
III.4.7.

`G` is instantiated at `(E.map f).toAffine.Point`, with `f : ℚ →+* K`
manufactured from `hne` exactly as the CHARACTERISTIC GUARD note above
says it can be: a `K`-point yields a coordinate datum, whose `base` is a
ring map `ℚ → Γ(Spec K, ⊤)`, hence a ring map `ℚ → K`.

## WHAT THIS CUT REPLACES

The previous plan recorded at `projMul_assoc_pt_algClosed` was Milne
I.2.5 / rigidity, and it is CIRCULAR: forming `h(v,w) - f(v) - g(w)`
needs the group law on the target as a MORPHISM, which is the `GrpObj`
this cluster is constructing, and every result in mathlib's
`AlgebraicGeometry/Group/Abelian.lean` assumes `[GrpObj G]`.  The route
taken here needs only the group law on `K`-POINTS as a SET-level group,
which mathlib already has, so it breaks the circle. -/
theorem exists_projPtAddEquiv_algClosed (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (K : Type) [Field K] [IsAlgClosed K]
    (hne : Nonempty (Spec (CommRingCat.of K) ⟶ proj E)) :
    ∃ (G : Type) (_ : AddCommGroup G)
      (e : (Spec (CommRingCat.of K) ⟶ proj E) ≃ G),
      (∀ P : Spec (CommRingCat.of K) ⟶ proj E,
          e (P ≫ projToSpec E ≫ projInfty E) = 0) ∧
        (∀ P : Spec (CommRingCat.of K) ⟶ proj E, e (P ≫ projNeg E) = -e P) ∧
          (∀ x : G, ∃ z : G, x = z + z) ∧
            ∀ (n : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
              (Q : Spec (CommRingCat.of K) ⟶ proj E),
              ∃ (α : G →+ G) (c : G), ∀ P : Spec (CommRingCat.of K) ⟶ proj E,
                e (projMulPt E n P Q) = α (e P) + c := by
  letI : DecidableEq K := Classical.decEq K
  obtain ⟨a⟩ := hne
  obtain ⟨c₀, -⟩ := ProjCoords.exists_of_specField E (CommRingCat.of K) (Field.toIsField K) a
  refine ⟨(E.map ((ProjCoords.gammaSpecEquiv K).toRingHom.comp c₀.base)).toAffine.Point,
    inferInstance,
    ProjCoords.specPointEquiv ((ProjCoords.gammaSpecEquiv K).toRingHom.comp c₀.base),
    ?_, ?_, ?_, ?_⟩
  · exact fun P => specPointEquiv_comp_projInfty_eq_zero _ P
  · exact fun P => specPointEquiv_comp_projNeg _ P
  · exact fun x => exists_add_self_affinePoint_of_isAlgClosed (E := E) (K := K) _ x
  · exact fun n Q => exists_addMonoidHom_specPointEquiv_projMulPt (E := E) (K := K) _ n Q

/-- **Associativity of the operation `m` induces on `K`-points, `K` an
ALGEBRAICALLY CLOSED field** (PROVEN 2026-07-27 from
`exists_projPtAddEquiv_algClosed` and `commLoop_eq_add_of_addHom`; it was
the one leaf `projMul_assoc` rested on, and the residue now sits in the
DICTIONARY leaf rather than here).

The restriction to `Spec` of a FIELD is essential rather than cosmetic:
the same statement for an arbitrary test scheme `T` is `projMul_assoc`
itself (take `T` to be the threefold product and the three projections),
so nothing would have been gained.  What a field buys is that
`proj E ×_ℚ Spec K` is a smooth projective genus-`1` curve over `K` with
the rational point `projInfty E`, i.e. an honest elliptic curve, where
mathlib's `WeierstrassCurve.Affine.Point` supplies a real `AddCommGroup`.
Algebraic closedness on top of that is FREE — see `projMul_assoc_pt` —
and it is what every classical statement of the rigidity argument assumes.

## THE THREE POINT-LEVEL HYPOTHESES ARE NOT A ROUTE ON THEIR OWN

`hcommPt`/`hunitPt`/`hinvPt` are DERIVED from `hcomm`/`hunit`/`hinv` by
`projMulPt_comm`, `projMulPt_unit_left` and `projMulPt_neg_left` above,
and are passed in only so that the assembly does not have to redo the
`pullback.lift` gymnastics.  **They are not sufficient on their own**, and
that warning stands unchanged: together they say exactly that
`projMulPt E m` is a commutative LOOP with two-sided unit and inverses on
the set of `K`-points, and a commutative loop need not be associative —
the smallest non-associative commutative loop has order `5`, so the
set-level statement is false already for a five-element carrier.
*Refuting check for anyone tempted to close this from
`hcommPt`/`hunitPt`/`hinvPt` alone*: those three mention `m` only through
`projMulPt E m`, i.e. only through its values on `K`-points, so any proof
from them alone would prove the false set-level statement.

The proof below therefore does **not** use them alone: it uses them
together with `exists_projPtAddEquiv_algClosed`, whose last clause
quantifies over EVERY morphism of schemes and is exactly the algebraicity
input that a set-level hypothesis cannot supply.

**FORMAL-CONTENT NOTE — `_hcomm`/`_hunit`/`_hinv` are UNUSED**, and are
underscored so that this is mechanically visible rather than merely
asserted.  This is *not* vacuity: the algebraicity the proof needs comes
from the dictionary leaf, which quantifies over all morphisms `n` and so
covers `m` whatever `m` is, while the three properties of `m` that the
argument does consume are already supplied in point-level form by
`hcommPt`/`hunitPt`/`hinvPt`.  Those three are in turn DERIVED from the
scheme-level ones by `projMulPt_comm`, `projMulPt_unit_left` and
`projMulPt_neg_left`, so no hypothesis has been silently dropped from the
node — the caller `projMul_assoc_pt` still has to produce all six.  The
scheme-level triple is retained in the signature because it is fixed by
the cut and every caller has it; an owner who wanted a minimal statement
could delete it, at the cost of touching `projMul_assoc_pt`.

## THE PROOF, IN FIVE LINES OF MATHEMATICS

Transport `projMulPt E m` along the dictionary `e` of
`exists_projPtAddEquiv_algClosed` to an operation `F` on the abelian
group `G`.  The three loop identities become `hsymm`, `F 0 y = y` and
`F (-x) x = 0` (the unit and negation clauses of `e` are what turn
`hunitPt`/`hinvPt` into those); the algebraicity clause instantiated at
`n := m` becomes "`x ↦ F x y` is a group homomorphism plus a constant";
and `G` is 2-divisible.  `commLoop_eq_add_of_addHom` then gives
`F x y = x + y` outright, so `e (projMulPt E m P Q) = e P + e Q` and
associativity is `add_assoc` pulled back through the injectivity of `e`.

The combinatorial step is the one that was missing from every earlier
plan and it is worth stating separately: from `F x y = α y x + y` the
form `B x y := α y x - x` is symmetric and biadditive with `B x x = 0`,
hence `2 • B = 0`, hence `B = 0` by divisibility.  See
`commLoop_eq_add_of_addHom`.

## WHY THE OLD PLAN (MILNE I.2.5 / RIGIDITY) WAS NOT TAKEN — it is CIRCULAR

Recorded because the rigidity machinery really is in the pin and the next
reader will find it and be tempted.  Milne, *Abelian Varieties* I.2.5
("every morphism `E × E → E` of complete varieties into an abelian
variety is `(P, Q) ↦ φ(P) + ψ(Q) + c`") forms the DIFFERENCE
`h(v, w) − f(v) − g(w)`, so it needs the group law on the TARGET as a
morphism — i.e. exactly the `GrpObj` this cluster is constructing.
Mathlib's `WeierstrassCurve.Affine.Point` addition is set-level only, so
it does not supply it, and every result in
`Mathlib/AlgebraicGeometry/Group/Abelian.lean` (`@[stacks 0BFD]`, a
complete worked rigidity argument at this pin, together with
`subsingleton_image_closure_of_finite_of_isPreirreducible` in
`Mathlib/Topology/JacobsonSpace.lean`, `ext_of_apply_eq` /
`ext_of_apply_closedPoint_eq` in
`Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean`, and
`exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage` in
`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`) ASSUMES `[GrpObj G]`.
So rigidity can only compare an arbitrary `m` with an ALREADY-ASSOCIATIVE
reference law; it cannot bootstrap associativity out of unitality.

The route actually taken sidesteps this because it never needs a group
law on the target as a morphism — only Silverman *AEC* III.4.7, which is
a statement about morphisms of curves and the SET-level group `E(K)`.
That is the whole reason the cut is non-circular.

## THE CUT-LEVEL OBSERVATION ABOUT `exists_projMul` STILL STANDS

`projMul_assoc`'s only consumer is `exists_projAdd`, which applies it to
`exists_projMul`'s witness and to nothing else, so the universal
quantification over `m` buys the tree nothing; and
`exists_projGroupLaw_geomFibreAddEquiv`'s docstring asks for the same
repair — give `exists_projMul` a `hassoc`-free chord–tangent clause
pinning its witness in coordinates.  That repair is no longer needed
HERE (this leaf is proven for an arbitrary `m`), but it remains the thing
that would let `exists_projPtAddEquiv_algClosed` and the `geomFibre`
dictionary be discharged from explicit polynomials.  Reported, not made.

## A DICTIONARY ALONE IS STILL NOT A SAFE CUT — and this one is not one

"Given a bijection `(Spec K ⟶ proj E) ≃ E(K)` carrying `projInfty` to `0`
and `projNeg` to negation, `m` corresponds to `+`" is **FALSE** for an
arbitrary such bijection, by the loop counterexample above transported
along it.  `exists_projPtAddEquiv_algClosed` is not that statement: it
adds 2-divisibility and, crucially, a clause quantified over every
SCHEME MORPHISM `n`, which is where algebraicity — naturality in `K`,
equivalently being a morphism, by Yoneda — enters.  Dropping either of
those two clauses makes it satisfiable by junk and the proof below
unsound. -/
theorem projMul_assoc_pt_algClosed (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (_hcomm : Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
      (Limits.pullback.fst (projToSpec E) (projToSpec E))
      Limits.pullback.condition.symm ≫ m = m)
    (_hunit : Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E))
    (_hinv : Limits.pullback.lift (projNeg E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E)
    (K : Type) [Field K] [IsAlgClosed K]
    (hcommPt : ∀ P Q : Spec (CommRingCat.of K) ⟶ proj E,
      projMulPt E m P Q = projMulPt E m Q P)
    (hunitPt : ∀ P : Spec (CommRingCat.of K) ⟶ proj E,
      projMulPt E m (P ≫ projToSpec E ≫ projInfty E) P = P)
    (hinvPt : ∀ P : Spec (CommRingCat.of K) ⟶ proj E,
      projMulPt E m (P ≫ projNeg E) P = P ≫ projToSpec E ≫ projInfty E)
    (P Q R : Spec (CommRingCat.of K) ⟶ proj E) :
    projMulPt E m (projMulPt E m P Q) R = projMulPt E m P (projMulPt E m Q R) := by
  -- The dictionary.  `⟨P⟩` discharges the characteristic guard: we are handed a
  -- `K`-point, so `K` really is a `ℚ`-algebra and the point set really is nonempty.
  obtain ⟨G, _, e, hO, hN, hdiv, halg⟩ := exists_projPtAddEquiv_algClosed E K ⟨P⟩
  -- Transport `projMulPt E m` to `G` and check the four hypotheses of
  -- `commLoop_eq_add_of_addHom` one by one.
  have hsymm : ∀ x y : G, e (projMulPt E m (e.symm x) (e.symm y))
      = e (projMulPt E m (e.symm y) (e.symm x)) := fun x y => by rw [hcommPt]
  have hzero : ∀ y : G, e (projMulPt E m (e.symm 0) (e.symm y)) = y := by
    intro y
    have h0 : e.symm (0 : G) = (e.symm y) ≫ projToSpec E ≫ projInfty E :=
      e.symm_apply_eq.mpr (hO (e.symm y)).symm
    rw [h0, hunitPt, Equiv.apply_symm_apply]
  have hnegPt : ∀ x : G, e (projMulPt E m (e.symm (-x)) (e.symm x)) = 0 := by
    intro x
    have h0 : e.symm (-x) = (e.symm x) ≫ projNeg E := by
      refine e.symm_apply_eq.mpr ?_
      rw [hN (e.symm x), Equiv.apply_symm_apply]
    rw [h0, hinvPt, hO]
  have halg' : ∀ y : G, ∃ (α : G →+ G) (c : G),
      ∀ x : G, e (projMulPt E m (e.symm x) (e.symm y)) = α x + c := by
    intro y
    obtain ⟨α, c, hα⟩ := halg m (e.symm y)
    exact ⟨α, c, fun x => by rw [hα (e.symm x), Equiv.apply_symm_apply]⟩
  have key := commLoop_eq_add_of_addHom (fun x y => e (projMulPt E m (e.symm x) (e.symm y)))
    hsymm hzero hnegPt hdiv halg'
  -- `m` IS the group law on `K`-points; associativity is `add_assoc`.
  have key' : ∀ A B : Spec (CommRingCat.of K) ⟶ proj E,
      e (projMulPt E m A B) = e A + e B := by
    intro A B
    simpa only [Equiv.symm_apply_apply] using key (e A) (e B)
  exact e.injective (by rw [key', key', key', key', add_assoc])

/-- **Associativity of the operation `m` induces on `K`-points, `K` any
field** (PROVEN from `projMul_assoc_pt_algClosed` — the descent to an
algebraic closure, which is the half of this leaf that needed no new
theory).

Given `P Q R : Spec K ⟶ proj E`, base-change them along
`Spec K̄ ⟶ Spec K`.  `comp_projMulPt` turns each `ι ≫ projMulPt …` into
`projMulPt` of the base-changed points, so the two bracketings agree after
restriction to `K̄` by `projMul_assoc_pt_algClosed`; and
`hom_ext_of_specMap_field` cancels `ι`, because `Spec` of a field
extension is an epimorphism of schemes.  The three point-level loop
identities the algebraically-closed leaf asks for are supplied here from
`projMulPt_comm`, `projMulPt_unit_left` and `projMulPt_neg_left`.

## INSTANCE-COHERENCE REPAIR (2026-07-27): why `K` is a `Type`, not a `CommRingCat`

This statement previously read `(K : CommRingCat.{0}) [Field K]`.  That
phrasing is **formally defective and makes the field hypothesis
unusable**, and the defect is invisible until one tries to use it:

* `K.str : CommRing ↥K` is the ring structure `Spec K` is built from,
  while `[Field ↥K]` is an unrelated instance, and nothing ties
  `Field.toCommRing` to `K.str`.  For an abstract `K` they are not
  definitionally equal.
* Consequently `AlgebraicClosure ↥K`, `algebraMap ↥K _` and
  `Scheme.SpecToEquivOfField ↥K` all elaborate against
  `Field.toCommRing`, and none of them typechecks against `Spec K`.  The
  observed error is the familiar one —
  `Field.toSemifield.toCommSemiring` versus `CommRing.toCommSemiring` on
  terms that pretty-print identically.
* So the old statement quantified over pairs of a ring and an *incoherent*
  field structure on its carrier.  It was still TRUE (it is implied by
  `projMul_assoc`, which holds at every test scheme), but strictly harder
  than intended and impossible to attack by the intended argument.

The repair is mathlib's own idiom, the one `SpecToEquivOfField`,
`ext_of_apply_eq` and `Group/Abelian.lean` all use: quantify over
`(K : Type) [Field K]` and write `Spec (CommRingCat.of K)`.  **No
consumer changes**: `projMul_assoc_residueField` below still discharges it
with `_`s, because `CommRingCat.of ↥(X.residueField x)` is `rfl`-equal to
`X.residueField x`. -/
theorem projMul_assoc_pt (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hcomm : Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
      (Limits.pullback.fst (projToSpec E) (projToSpec E))
      Limits.pullback.condition.symm ≫ m = m)
    (hunit : Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E))
    (hinv : Limits.pullback.lift (projNeg E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E)
    (K : Type) [Field K] (P Q R : Spec (CommRingCat.of K) ⟶ proj E) :
    projMulPt E m (projMulPt E m P Q) R = projMulPt E m P (projMulPt E m Q R) := by
  refine hom_ext_of_specMap_field (L := AlgebraicClosure K)
    (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) _ _ ?_
  rw [comp_projMulPt, comp_projMulPt, comp_projMulPt, comp_projMulPt]
  exact projMul_assoc_pt_algClosed E m hcomm hunit hinv (AlgebraicClosure K)
    (projMulPt_comm E m hcomm) (projMulPt_unit_left E m hunit)
    (projMulPt_neg_left E m hinv) _ _ _

/-- **Associativity at the residue field of every point of the threefold
product** (PROVEN from `projMul_assoc_pt`).

This is the `H` hypothesis of `ext_of_fromSpecResidueField_eq`, read at
`S = Set.univ`.  The residue field of a point of a `ℚ`-scheme is a field,
so `projMul_assoc_pt` applies verbatim; the only work is
`comp_triAddLeft_proj`/`comp_triAddRight_proj`, which say that the two
composites are the two bracketings of the induced operation on the three
projections. -/
theorem projMul_assoc_residueField (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hcomm : Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
      (Limits.pullback.fst (projToSpec E) (projToSpec E))
      Limits.pullback.condition.symm ≫ m = m)
    (hunit : Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E))
    (hinv : Limits.pullback.lift (projNeg E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E)
    (x : AbelianSchemeStruct.triProd (projToSpec E)) :
    (AbelianSchemeStruct.triProd (projToSpec E)).fromSpecResidueField x ≫
        AbelianSchemeStruct.triAddLeft (projToSpec E) m (hom_ext_spec_rat _ _) =
      (AbelianSchemeStruct.triProd (projToSpec E)).fromSpecResidueField x ≫
        AbelianSchemeStruct.triAddRight (projToSpec E) m (hom_ext_spec_rat _ _) := by
  rw [comp_triAddLeft_proj, comp_triAddRight_proj]
  exact projMul_assoc_pt E m hcomm hunit hinv _ _ _ _

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
proof plan.  The assembly is written and PROVEN, and so now are two of the three pieces:
only `projChart_jacobian_span_eq_top` is still open.

The identification itself (`exists_projChartRingEquiv`) is built here out of the material
between `eval₂_dehomogenizeAt` and `projChartHom_ker`, and that material is written to be
upstreamable: the only place the Weierstrass equation enters is `not_X_dvd_polynomial`,
everything else being generic "dehomogenise a homogeneous polynomial and divide by `Xᵢ^n`". -/

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

open _root_.MvPolynomial in
/-- Evaluating a dehomogenisation is evaluating the original polynomial with `Xᵢ ↦ 1`. -/
theorem eval₂_dehomogenizeAt {S : Type} [CommRing S] (c : ℚ →+* S) (i : Fin 3)
    (g : Fin 3 → S) (p : MvPolynomial (Fin 3) ℚ) :
    MvPolynomial.eval₂ c (fun j : ProjChartVar i => g j.1) (dehomogenizeAt ℚ i p)
      = MvPolynomial.eval₂ c (fun j => if j = i then 1 else g j) p := by
  classical
  have key : (MvPolynomial.eval₂Hom c (fun j : ProjChartVar i => g j.1)).comp
      ((dehomogenizeAt ℚ i).toRingHom)
      = MvPolynomial.eval₂Hom c (fun j => if j = i then 1 else g j) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [dehomogenizeAt]
    · intro j
      by_cases h : j = i <;> simp [dehomogenizeAt, h]
  exact congrArg (fun φ : MvPolynomial (Fin 3) ℚ →+* S => φ p) key

open _root_.MvPolynomial in
/-- **The core dehomogenisation identity** (PROVEN).  If `t i` is invertible with inverse `s`,
then evaluating the dehomogenisation of a degree-`n` homogeneous `p` at the ratios `t j / t i`
gives `p(t) / t i ^ n`.

The proof is the one-line monomial computation made uniform: after reducing to a monomial `d`
with `∑ⱼ dⱼ = n`, the two products over `Fin 3` are compared factorwise, the factor at `j = i`
being `1 ^ dᵢ · t i ^ dᵢ` and the factor at `j ≠ i` being `(s · t j) ^ dⱼ · t i ^ dⱼ = t j ^ dⱼ`.
No case split on `i` is needed. -/
theorem eval₂_dehomogenizeAt_mul_pow {S : Type} [CommRing S] (c : ℚ →+* S) (i : Fin 3)
    (t : Fin 3 → S) (s : S) (hs : s * t i = 1) {n : ℕ} {p : MvPolynomial (Fin 3) ℚ}
    (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂ c (fun j : ProjChartVar i => s * t j.1) (dehomogenizeAt ℚ i p) * t i ^ n
      = MvPolynomial.eval₂ c t p := by
  classical
  rw [eval₂_dehomogenizeAt c i (fun j => s * t j)]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [← MvPolynomial.coe_eval₂Hom, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : ∑ j : Fin 3, d j = n := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (fun j => pow_zero _),
      Finsupp.prod_fintype _ _ (fun j => pow_zero _)]
  rw [mul_assoc, ← hdn, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h : j = i
  · subst h; simp
  · simp only [h, if_false, ← mul_pow]
    congr 1
    rw [mul_right_comm, hs, one_mul]

/-! #### Homogenisation, the section of `dehomogenizeAt` -/

/-- The inclusion `ℚ[uⱼ : j ≠ i] → ℚ[X₀, X₁, X₂]` sending each chart variable to the
corresponding homogeneous coordinate. -/
noncomputable def inclChartVar (i : Fin 3) :
    MvPolynomial (ProjChartVar i) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ :=
  MvPolynomial.aeval fun j => MvPolynomial.X j.1

theorem dehomogenizeAt_inclChartVar (i : Fin 3) (q : MvPolynomial (ProjChartVar i) ℚ) :
    dehomogenizeAt ℚ i (inclChartVar i q) = q := by
  have key : (dehomogenizeAt ℚ i).comp (inclChartVar i) = AlgHom.id ℚ _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [dehomogenizeAt, inclChartVar, dif_neg j.2]
  exact congrArg (fun φ : MvPolynomial (ProjChartVar i) ℚ →ₐ[ℚ] _ => φ q) key

/-- **Homogenisation at the `i`-th coordinate.**  The homogeneous component of degree `d` of
`q` (viewed in the big polynomial ring) is multiplied by `Xᵢ^(n - d)`, where `n` is the total
degree.  This is a section of `dehomogenizeAt` landing in a single degree, and it is the only
thing the kernel computation needs: the *value* of `n` is irrelevant. -/
noncomputable def homogenizeAt (i : Fin 3) (q : MvPolynomial (ProjChartVar i) ℚ) :
    MvPolynomial (Fin 3) ℚ :=
  ∑ d ∈ Finset.range ((inclChartVar i q).totalDegree + 1),
    MvPolynomial.X i ^ ((inclChartVar i q).totalDegree - d) *
      MvPolynomial.homogeneousComponent d (inclChartVar i q)

theorem isHomogeneous_homogenizeAt (i : Fin 3) (q : MvPolynomial (ProjChartVar i) ℚ) :
    (homogenizeAt i q).IsHomogeneous (inclChartVar i q).totalDegree := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd => ?_
  have hdle : d ≤ (inclChartVar i q).totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have h := (MvPolynomial.isHomogeneous_X_pow (R := ℚ) i
      ((inclChartVar i q).totalDegree - d)).mul
    (MvPolynomial.homogeneousComponent_isHomogeneous d (inclChartVar i q))
  rwa [Nat.sub_add_cancel hdle] at h

theorem dehomogenizeAt_homogenizeAt (i : Fin 3) (q : MvPolynomial (ProjChartVar i) ℚ) :
    dehomogenizeAt ℚ i (homogenizeAt i q) = q := by
  have hXi : dehomogenizeAt ℚ i (MvPolynomial.X i) = 1 := by simp [dehomogenizeAt]
  rw [homogenizeAt, map_sum]
  simp only [map_mul, map_pow, hXi, one_pow, one_mul]
  rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  exact dehomogenizeAt_inclChartVar i q

/-! #### The chart homomorphism `ℚ[u, v] → (B_{xᵢ})₀` -/

section ChartHom

variable (E : WeierstrassCurve ℚ) (i : Fin 3) (hcoord : projCoord E i ∈ projGrading E 1)

/-- The chart ratio `xⱼ / xᵢ`, an element of the degree-zero away-localisation. -/
noncomputable def projChartRatio (j : ProjChartVar i) :
    HomogeneousLocalization.Away (projGrading E) (projCoord E i) :=
  HomogeneousLocalization.Away.mk (projGrading E) hcoord 1
    (Ideal.Quotient.mk _ (MvPolynomial.X j.1))
    (by
      simpa using HomogeneousIdeal.mk_mem_quotientGrading (I := polynomialHomogeneousIdeal E)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℚ j.1)))

/-- The base map `ℚ → (B_{xᵢ})₀`, exactly the composite appearing in the commuting triangle of
`exists_projChartRingEquiv`. -/
noncomputable def projChartBase :
    ℚ →+* HomogeneousLocalization.Away (projGrading E) (projCoord E i) :=
  (HomogeneousLocalization.fromZeroRingHom (projGrading E)
    (Submonoid.powers (projCoord E i))).comp (algebraMap ℚ (projGrading E 0))

/-- **The chart homomorphism** `ℚ[u, v] → (B_{xᵢ})₀`, sending `uⱼ ↦ xⱼ / xᵢ`. -/
noncomputable def projChartHom :
    MvPolynomial (ProjChartVar i) ℚ →+*
      HomogeneousLocalization.Away (projGrading E) (projCoord E i) :=
  MvPolynomial.eval₂Hom (projChartBase E i) (projChartRatio E i hcoord)

/-- **The chart homomorphism computes dehomogenisations** (PROVEN): a homogeneous `p` of
degree `n` dehomogenises to a polynomial whose image is the fraction `p̄ / xᵢ^n`.

This is the whole content of the identification.  It is proved by transporting both sides into
the ordinary localisation `B_{xᵢ}` along `HomogeneousLocalization.val` — which is available as
a ring hom, being `algebraMap (HomogeneousLocalization 𝒜 x) (Localization x)` — and then
applying `eval₂_dehomogenizeAt_mul_pow` with `t j = xⱼ/1` and `s = 1/xᵢ`, cancelling the unit
`xᵢ^n`. -/
theorem projChartHom_dehomogenizeAt {n : ℕ} {p : MvPolynomial (Fin 3) ℚ}
    (hp : p.IsHomogeneous n) (hmem : Ideal.Quotient.mk _ p ∈ projGrading E (n • 1)) :
    projChartHom E i hcoord (dehomogenizeAt ℚ i p)
      = HomogeneousLocalization.Away.mk (projGrading E) hcoord n
        (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal p) hmem := by
  classical
  set B := MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal with hB
  set f : B := projCoord E i with hf
  set L := Localization (Submonoid.powers f) with hL
  set V := algebraMap (HomogeneousLocalization.Away (projGrading E) f) L with hV
  set t : Fin 3 → L := fun j => algebraMap B L (Ideal.Quotient.mk _ (MvPolynomial.X j)) with ht
  set s : L := Localization.mk 1 ⟨f, ⟨1, pow_one f⟩⟩ with hs'
  set c : ℚ →+* L := V.comp (projChartBase E i) with hc
  have hti : t i = algebraMap B L f := rfl
  have htj : ∀ j : Fin 3, t j = Localization.mk
      (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.X j)) 1 := fun j => by
    rw [ht]; exact (Localization.mk_one_eq_algebraMap _).symm
  -- `s` inverts `t i`
  have hs : s * t i = 1 := by
    rw [hs', hti, Localization.mk_eq_mk']
    exact (IsLocalization.mk'_spec L 1 (⟨f, ⟨1, pow_one f⟩⟩ : Submonoid.powers f)).trans (map_one _)
  -- the ratios are `s * t j`
  have hratio : ∀ j : ProjChartVar i, V (projChartRatio E i hcoord j) = s * t j.1 := fun j => by
    rw [hs', htj]
    show Localization.mk _ ⟨f ^ 1, _⟩ = Localization.mk 1 ⟨f, _⟩ * Localization.mk _ 1
    rw [Localization.mk_mul, one_mul, mul_one]
    congr 1
    exact Subtype.ext (pow_one f)
  -- `V ∘ projChartHom` is `eval₂` into the localisation
  have hcomp : V.comp (projChartHom E i hcoord)
      = MvPolynomial.eval₂Hom c (fun j : ProjChartVar i => s * t j.1) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [projChartHom, hc]
    · intro j; simp [projChartHom, hratio j]
  -- `eval₂ c t` is the quotient map followed by localisation
  have hct : MvPolynomial.eval₂Hom c t
      = (algebraMap B L).comp (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hcr : ((algebraMap ℚ (projGrading E 0) r : B)) =
          Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.C r) := by
        rw [SetLike.GradeZero.coe_algebraMap,
          IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 3) ℚ) B r,
          Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
      simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, hc]
      show Localization.mk ((algebraMap ℚ (projGrading E 0) r : B))
            (1 : ↥(Submonoid.powers f))
          = algebraMap B L
            (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.C r))
      rw [hcr, Localization.mk_one_eq_algebraMap]
    · intro j; simp [ht]
  -- assemble
  have hcore := eval₂_dehomogenizeAt_mul_pow c i t s hs hp
  have h1 : V (projChartHom E i hcoord (dehomogenizeAt ℚ i p))
      = MvPolynomial.eval₂ c (fun j : ProjChartVar i => s * t j.1) (dehomogenizeAt ℚ i p) :=
    RingHom.congr_fun hcomp _
  have h2 : MvPolynomial.eval₂ c t p
      = algebraMap B L (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal p) :=
    RingHom.congr_fun hct p
  have hVeq : V (projChartHom E i hcoord (dehomogenizeAt ℚ i p)) * t i ^ n
      = algebraMap B L (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal p) := by
    rw [h1, hcore, h2]
  have hunit : IsUnit (t i ^ n) := by
    rw [hti]
    exact (IsLocalization.map_units L (⟨f, ⟨1, pow_one f⟩⟩ : Submonoid.powers f)).pow n
  apply HomogeneousLocalization.val_injective
  apply hunit.mul_left_cancel
  have hlhs : (projChartHom E i hcoord (dehomogenizeAt ℚ i p)).val
      = V (projChartHom E i hcoord (dehomogenizeAt ℚ i p)) := rfl
  rw [hlhs, mul_comm (t i ^ n) (V _), hVeq, HomogeneousLocalization.Away.val_mk, hti, ← map_pow,
    Localization.mk_eq_mk', mul_comm]
  exact (IsLocalization.mk'_spec L _ _).symm

/-- **The chart homomorphism is surjective.**  This is the half that was already in mathlib:
`HomogeneousLocalization.Away.mk_surjective` says every element of `(B_{xᵢ})₀` is `a / xᵢ^m`
with `a` of degree `m`, and `projChartHom_dehomogenizeAt` exhibits `dehomogenizeAt ℚ i p` as a
preimage. -/
theorem projChartHom_surjective : Function.Surjective (projChartHom E i hcoord) := by
  intro z
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (projGrading E) hcoord z
  obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp ha
  have hp' : p.IsHomogeneous m := by
    have h := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hp
    simpa using h
  exact ⟨dehomogenizeAt ℚ i p, projChartHom_dehomogenizeAt E i hcoord hp' _⟩

end ChartHom

/-! #### `Xᵢ ∤ W`, and the kernel -/

/-- **`Xᵢ` does not divide the projective Weierstrass polynomial**, for any of the three
coordinates.  This — *not* irreducibility of `W` — is the only input the kernel computation
needs beyond primality of `Xᵢ`.

It is checked by evaluation.  If `Xᵢ ∣ W` then `eval P W = 0` for every `P` with `P i = 0`;
for `i = 1, 2` the point `(1, 0, 0)` gives `-1 = 0`, and for `i = 0` the three points
`(0, 0, 1)`, `(0, 1, 1)`, `(0, -1, 1)` give `-a₆ = 0`, `1 + a₃ - a₆ = 0` and
`1 - a₃ - a₆ = 0`, whose sum of the last two forces `a₆ = 1` against the first. -/
theorem not_X_dvd_polynomial (E : WeierstrassCurve ℚ) (i : Fin 3) :
    ¬ (MvPolynomial.X i ∣ polynomial E) := by
  rintro ⟨S, hS⟩
  have hev : ∀ P : Fin 3 → ℚ, P i = 0 → MvPolynomial.eval P (polynomial E) = 0 := by
    intro P hP
    rw [hS, map_mul, MvPolynomial.eval_X, hP, zero_mul]
  fin_cases i
  · have h0 := hev ![0, 0, 1] rfl
    have h1 := hev ![0, 1, 1] rfl
    have h2 := hev ![0, -1, 1] rfl
    simp only [eval_polynomial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
    norm_num at h0 h1 h2
    linarith
  · have h := hev ![1, 0, 0] rfl
    simp only [eval_polynomial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    norm_num at h
  · have h := hev ![1, 0, 0] rfl
    simp only [eval_polynomial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    norm_num at h

/-- `W ∣ Xᵢ^k · P → W ∣ P`.  This is the UFD half of the kernel argument, and mathlib's
`MvPolynomial.dvd_X_mul_iff` packages it so that a bare induction on `k` suffices: at each step
the alternative disjunct says `Xᵢ ∣ W`, refuted by `not_X_dvd_polynomial`. -/
theorem polynomial_dvd_of_dvd_X_pow_mul (E : WeierstrassCurve ℚ) (i : Fin 3) :
    ∀ (k : ℕ) (P : MvPolynomial (Fin 3) ℚ),
      polynomial E ∣ MvPolynomial.X i ^ k * P → polynomial E ∣ P := by
  intro k
  induction k with
  | zero => intro P h; simpa using h
  | succ k ih =>
    intro P h
    rw [pow_succ', mul_assoc] at h
    rcases MvPolynomial.dvd_X_mul_iff.mp h with h' | ⟨h'', -⟩
    · exact ih P h'
    · exact absurd h'' (not_X_dvd_polynomial E i)

section Kernel

variable (E : WeierstrassCurve ℚ) (i : Fin 3) (hcoord : projCoord E i ∈ projGrading E 1)

/-- **The kernel of the chart homomorphism is the dehomogenised Weierstrass ideal** (PROVEN).

`⊇` is immediate since `W ↦ 0`.  For `⊆`: a `q` in the kernel homogenises to some `Q` of a
single degree `n` with `dehom Q = q`; the vanishing of `Q̄ / xᵢ^n` in the localisation says
`xᵢ^k · Q̄ = 0` in `B`, i.e. `W ∣ Xᵢ^k · Q`, whence `W ∣ Q` by
`polynomial_dvd_of_dvd_X_pow_mul`, and dehomogenising the factorisation gives `wᵢ ∣ q`. -/
theorem projChartHom_ker :
    RingHom.ker (projChartHom E i hcoord) = Ideal.span {projChartPolynomial E i} := by
  have hW0 : Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (polynomial E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  apply le_antisymm
  · intro q hq
    rw [RingHom.mem_ker] at hq
    have hQhom : (homogenizeAt i q).IsHomogeneous (inclChartVar i q).totalDegree :=
      isHomogeneous_homogenizeAt i q
    have hmem : Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (homogenizeAt i q)
        ∈ projGrading E ((inclChartVar i q).totalDegree • 1) := by
      simpa using HomogeneousIdeal.mk_mem_quotientGrading (I := polynomialHomogeneousIdeal E)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hQhom)
    have h0 : HomogeneousLocalization.Away.mk (projGrading E) hcoord
        (inclChartVar i q).totalDegree
        (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (homogenizeAt i q)) hmem = 0 := by
      rw [← projChartHom_dehomogenizeAt E i hcoord hQhom hmem, dehomogenizeAt_homogenizeAt, hq]
    have hval := congrArg HomogeneousLocalization.val h0
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨⟨-, k, rfl⟩, hk⟩ := hval
    have hdvd : polynomial E ∣ MvPolynomial.X i ^ k * homogenizeAt i q := by
      rw [← Ideal.mem_span_singleton]
      show _ ∈ (polynomialHomogeneousIdeal E).toIdeal
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
      exact hk
    obtain ⟨T, hT⟩ := polynomial_dvd_of_dvd_X_pow_mul E i k _ hdvd
    rw [Ideal.mem_span_singleton]
    refine ⟨dehomogenizeAt ℚ i T, ?_⟩
    rw [← dehomogenizeAt_homogenizeAt i q, hT, map_mul]
    rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    have hhom : (polynomial E).IsHomogeneous 3 := isHomogeneous_polynomial E
    have hmem : Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (polynomial E)
        ∈ projGrading E (3 • 1) := by
      simpa using HomogeneousIdeal.mk_mem_quotientGrading (I := polynomialHomogeneousIdeal E)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hhom)
    show projChartHom E i hcoord (dehomogenizeAt ℚ i (polynomial E)) = 0
    rw [projChartHom_dehomogenizeAt E i hcoord hhom hmem]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, hW0,
      Localization.mk_zero]

end Kernel

/-- **LEAF A — THE DEHOMOGENISATION ISOMORPHISM** (PROVEN; it was a missing piece of MATHLIB,
not of this development, and it is written above in a form fit to be upstreamed).

  `(ℚ[X, Y, Z] ⧸ (W))_{(Xᵢ)}` in degree `0`  ≃  `ℚ[u, v] ⧸ (wᵢ)`,

compatibly with the two structure maps out of `ℚ`.  It is stated as a `RingEquiv` together
with the commuting triangle rather than as an `AlgEquiv` deliberately: the source carries an
`Algebra (projGrading E 0)` instance and the target an `Algebra ℚ` one, and forcing them
into a common `Algebra ℚ` structure invites exactly the "two defeq but never syntactically
equal instances" trap this development has been bitten by repeatedly.  The commuting
triangle is what the consumer actually needs, and it is instance-free.

## How it is proved

Everything is routed through the single ring hom `projChartHom E i hcoord : ℚ[u, v] → (B_{xᵢ})₀`
sending `uⱼ ↦ xⱼ / xᵢ`, of which this is the first isomorphism theorem:
`projChartHom_surjective` and `projChartHom_ker`, glued by
`RingHom.quotientKerEquivOfSurjective` and `Ideal.quotEquivOfEq`.

*Surjectivity was already in mathlib*, and more cheaply than the original plan supposed.  The
plan called for `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` at `d = 1`, which does
force every algebra generator to be a product of a SUBSET of the coordinates over `xᵢ^card`.
But `HomogeneousLocalization.Away.mk_surjective` is stronger and immediate: every element of
`(B_{xᵢ})₀` is literally `ā / xᵢ^m` with `a` homogeneous of degree `m`, and
`projChartHom_dehomogenizeAt` says `dehomogenizeAt ℚ i a` is a preimage.  So no generation
argument is needed at all.

*The kernel is the one genuinely new argument.*  Given `q` in the kernel, `homogenizeAt i q`
is a homogeneous `Q` of a single degree with `dehom Q = q` (built from the homogeneous
components of `q`, each pushed up by a power of `Xᵢ` — the degree itself is never needed).
Its image `Q̄ / xᵢ^n` vanishes iff `Xᵢ^k · Q ∈ (W)` for some `k`.  Now `ℚ[X, Y, Z]` is a UFD,
`Xᵢ` is prime, and `Xᵢ ∤ W` for each of the three `i` — `W` contains the monomial `Y²Z` (so
`X ∤ W`) and the monomial `-X³` (so `Y ∤ W` and `Z ∤ W`).  Hence `W ∣ Xᵢ^k Q` forces `W ∣ Q`
(`polynomial_dvd_of_dvd_X_pow_mul`, an induction on `k` off `MvPolynomial.dvd_X_mul_iff`).
Dehomogenising, `wᵢ ∣ q`.  The reverse inclusion is immediate since `W` maps to `0`.

Note this argument does NOT need `W` irreducible, only `Xᵢ ∤ W`, which is a numerical check
(`not_X_dvd_polynomial`, done by evaluation at three rational points).

This is the piece that ought to be upstreamed: stated for an arbitrary homogeneous ideal of
`R[X₀ .. Xₙ]` it is the standard affine chart of `Proj` of a projective scheme over `R`, and
its absence is what had kept every `Proj`-level smoothness argument out of reach.  The one
genuinely elliptic-curve-specific input is `not_X_dvd_polynomial`; everything else above is
stated for the Weierstrass ideal only because that is the ideal at hand. -/
theorem exists_projChartRingEquiv (E : WeierstrassCurve ℚ) (i : Fin 3)
    (hcoord : projCoord E i ∈ projGrading E 1) :
    ∃ e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) ≃+* ProjChartRing E i,
      (e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) →+* ProjChartRing E i).comp
          ((HomogeneousLocalization.fromZeroRingHom (projGrading E)
            (Submonoid.powers (projCoord E i))).comp (algebraMap ℚ (projGrading E 0)))
        = algebraMap ℚ (ProjChartRing E i) := by
  have hsurj := projChartHom_surjective E i hcoord
  have hker := projChartHom_ker E i hcoord
  refine ⟨(RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hker), ?_⟩
  refine RingHom.ext fun r => ?_
  show Ideal.quotEquivOfEq hker ((RingHom.quotientKerEquivOfSurjective hsurj).symm
      (projChartBase E i r)) = algebraMap ℚ (ProjChartRing E i) r
  have h1 : projChartBase E i r = projChartHom E i hcoord (MvPolynomial.C r) :=
    (MvPolynomial.eval₂Hom_C _ _ r).symm
  rw [h1, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk,
    IsScalarTower.algebraMap_apply ℚ (MvPolynomial (ProjChartVar i) ℚ) (ProjChartRing E i) r,
    Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]

/-! #### The two ingredients of the chart Jacobian criterion

Both are stated for an arbitrary base ring and are pure `MvPolynomial` bookkeeping; only
`false_of_eval_pderiv_projPolynomial_eq_zero` below is elliptic-curve mathematics. -/

/-- Dehomogenisation sends `Xₙ` to `1` when `n = i`, and to the `n`-th chart coordinate
otherwise. -/
theorem dehomogenizeAt_X {R : Type} [CommRing R] (i n : Fin 3) :
    dehomogenizeAt R i (MvPolynomial.X n)
      = if h : n = i then 1 else MvPolynomial.X ⟨n, h⟩ := by
  simp [dehomogenizeAt]

/-- `pderiv_dehomogenizeAt` on a single variable — the base case of the induction. -/
theorem pderiv_dehomogenizeAt_X {R : Type} [CommRing R] (i : Fin 3) (j : ProjChartVar i)
    (n : Fin 3) :
    MvPolynomial.pderiv j (dehomogenizeAt R i (MvPolynomial.X n))
      = dehomogenizeAt R i (MvPolynomial.pderiv (j : Fin 3) (MvPolynomial.X n)) := by
  classical
  rw [dehomogenizeAt_X]
  rcases eq_or_ne n i with rfl | h
  · rw [dif_pos rfl, MvPolynomial.pderiv_one,
      MvPolynomial.pderiv_X_of_ne (Ne.symm j.2), map_zero]
  · rw [dif_neg h]
    rcases eq_or_ne n (j : Fin 3) with h2 | h2
    · have hj : (⟨n, h⟩ : ProjChartVar i) = j := Subtype.ext h2
      rw [hj, MvPolynomial.pderiv_X_self, h2, MvPolynomial.pderiv_X_self, map_one]
    · rw [MvPolynomial.pderiv_X_of_ne (fun hc => h2 (congrArg Subtype.val hc)),
        MvPolynomial.pderiv_X_of_ne h2, map_zero]

/-- **INGREDIENT 1 — dehomogenisation commutes with the chart partials.**

For a chart variable `j ≠ i` the substitution `Xᵢ ↦ 1` is a constant in the `j`-th variable,
so `∂/∂uⱼ` may be taken before or after dehomogenising.  Consequently the two partials of
the chart equation `wᵢ` are the dehomogenisations of two of mathlib's `polynomialX`,
`polynomialY`, `polynomialZ`. -/
theorem pderiv_dehomogenizeAt {R : Type} [CommRing R] (i : Fin 3) (j : ProjChartVar i)
    (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.pderiv j (dehomogenizeAt R i p)
      = dehomogenizeAt R i (MvPolynomial.pderiv (j : Fin 3) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n h =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, map_mul, h,
      pderiv_dehomogenizeAt_X]

/-- Evaluating a base-changed polynomial at the image of the chart point `(…, 1, …)` is
`φ` applied to its dehomogenisation.  This is the bridge between the `MvPolynomial (Fin 3)`
world, where Euler's relation lives, and the chart ring. -/
theorem eval_map_eq_dehomogenizeAt {k : Type} [CommRing k] [Algebra ℚ k] (i : Fin 3)
    (φ : MvPolynomial (ProjChartVar i) ℚ →ₐ[ℚ] k) (p : MvPolynomial (Fin 3) ℚ) :
    MvPolynomial.eval (fun n => φ (if h : n = i then 1 else MvPolynomial.X ⟨n, h⟩))
        (MvPolynomial.map (algebraMap ℚ k) p)
      = φ (dehomogenizeAt ℚ i p) := by
  rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, dehomogenizeAt,
    MvPolynomial.comp_aeval_apply]

/-- **INGREDIENT 2 — EULER.**  Euler's homogeneous function theorem
`3W = X·W_X + Y·W_Y + Z·W_Z` (`WeierstrassCurve.Projective.polynomial_relation`) says the
three partials are not independent along the curve.  So at a point `P` of the curve whose
`i`-th coordinate is `1`, the vanishing of the two partials `∂/∂Xⱼ`, `j ≠ i`, forces the
vanishing of the third — which is why the chart's own two partials already control all
three. -/
theorem eval_pderiv_projPolynomial_eq_zero (E : WeierstrassCurve ℚ) (k : Type) [Field k]
    [Algebra ℚ k] (i : Fin 3) (P : Fin 3 → k) (hPi : P i = 1)
    (hW : MvPolynomial.eval P (polynomial (E.map (algebraMap ℚ k))) = 0)
    (hj : ∀ n : Fin 3, n ≠ i →
      MvPolynomial.eval P (MvPolynomial.pderiv n (polynomial (E.map (algebraMap ℚ k)))) = 0)
    (n : Fin 3) :
    MvPolynomial.eval P (MvPolynomial.pderiv n (polynomial (E.map (algebraMap ℚ k)))) = 0 := by
  have hE := WeierstrassCurve.Projective.polynomial_relation (W' := E.map (algebraMap ℚ k)) P
  rw [hW, mul_zero] at hE
  have eX : polynomialX (E.map (algebraMap ℚ k))
      = MvPolynomial.pderiv (0 : Fin 3) (polynomial (E.map (algebraMap ℚ k))) := rfl
  have eY : polynomialY (E.map (algebraMap ℚ k))
      = MvPolynomial.pderiv (1 : Fin 3) (polynomial (E.map (algebraMap ℚ k))) := rfl
  have eZ : polynomialZ (E.map (algebraMap ℚ k))
      = MvPolynomial.pderiv (2 : Fin 3) (polynomial (E.map (algebraMap ℚ k))) := rfl
  rw [eX, eY, eZ] at hE
  by_cases h : n = i
  · subst h
    have hsum : ∑ b : Fin 3,
        P b * MvPolynomial.eval P (MvPolynomial.pderiv b (polynomial (E.map (algebraMap ℚ k))))
        = 0 := by
      rw [Fin.sum_univ_three]
      linear_combination -hE
    rw [Finset.sum_eq_single_of_mem n (Finset.mem_univ n)
      (fun b _ hb => by rw [hj b hb, mul_zero]), hPi, one_mul] at hsum
    exact hsum
  · exact hj n h

/-- **THE GEOMETRIC CORE — over a FIELD there is no singular point.**

`hjac` (the affine Jacobian criterion, where `Δ` is consumed) forbids a point of the
projective Weierstrass curve at which all three homogeneous partials vanish and some
coordinate equals `1`.  The proof is a two-case check on whether the point is at infinity,
and **neither case mentions a chart** — that is what makes
`projChart_jacobian_span_eq_top` uniform in `i`.

* `P z ≠ 0`: the point is affine, `hjac` applies at `S := k`, and the two affine partials
  are `eval P W_X / P z ^ 2` and `eval P W_Y / P z ^ 2`, both zero — so `span {0, 0} = ⊤`
  in a field, absurd.
* `P z = 0`: the projective equation degenerates to `P x ^ 3 = 0`, so `P x = 0`, and then
  `eval P W_Z = P y ^ 2`, forcing `P y = 0`.  Every coordinate vanishes, contradicting
  `P i = 1`.  (The constant term of `W_Z` is what does the work here; this is the point at
  infinity, and it is not a separate chart argument.) -/
theorem false_of_eval_pderiv_projPolynomial_eq_zero (E : WeierstrassCurve ℚ) (k : Type)
    [Field k] [Algebra ℚ k]
    (hjac : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (x y : S),
      (E.map (algebraMap ℚ S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialY} = ⊤)
    (i : Fin 3) (P : Fin 3 → k) (hPi : P i = 1)
    (hW : MvPolynomial.eval P (polynomial (E.map (algebraMap ℚ k))) = 0)
    (hq : ∀ n : Fin 3,
      MvPolynomial.eval P (MvPolynomial.pderiv n (polynomial (E.map (algebraMap ℚ k)))) = 0) :
    False := by
  by_cases hPz : P 2 = 0
  · -- the point lies on the line at infinity, and is then forced to be `(0 : 0 : 0)`
    have hx : P 0 = 0 := by
      have h3 := (WeierstrassCurve.Projective.equation_of_Z_eq_zero
        (W' := E.map (algebraMap ℚ k)) hPz).1 hW
      by_contra hc
      exact pow_ne_zero 3 hc h3
    have hy : P 1 = 0 := by
      have h2 := hq 2
      rw [show MvPolynomial.pderiv (2 : Fin 3) (polynomial (E.map (algebraMap ℚ k)))
        = polynomialZ (E.map (algebraMap ℚ k)) from rfl,
        WeierstrassCurve.Projective.eval_polynomialZ, hx, hPz] at h2
      have hsq : P 1 ^ 2 = 0 := by linear_combination h2
      by_contra hc
      exact pow_ne_zero 2 hc hsq
    have hall : ∀ n : Fin 3, P n = 0 := by intro n; fin_cases n <;> assumption
    exact one_ne_zero (hPi.symm.trans (hall i))
  · -- an honest affine point of the curve over the field `k`
    have heq : (E.map (algebraMap ℚ k)).toAffine.Equation (P 0 / P 2) (P 1 / P 2) :=
      (WeierstrassCurve.Projective.equation_of_Z_ne_zero (W := E.map (algebraMap ℚ k)) hPz).1 hW
    have hX0 : Polynomial.evalEval (P 0 / P 2) (P 1 / P 2)
        (E.map (algebraMap ℚ k)).toAffine.polynomialX = 0 := by
      rw [← WeierstrassCurve.Projective.eval_polynomialX_of_Z_ne_zero
        (W := E.map (algebraMap ℚ k)) hPz,
        show polynomialX (E.map (algebraMap ℚ k))
          = MvPolynomial.pderiv (0 : Fin 3) (polynomial (E.map (algebraMap ℚ k))) from rfl,
        hq 0, zero_div]
    have hY0 : Polynomial.evalEval (P 0 / P 2) (P 1 / P 2)
        (E.map (algebraMap ℚ k)).toAffine.polynomialY = 0 := by
      rw [← WeierstrassCurve.Projective.eval_polynomialY_of_Z_ne_zero
        (W := E.map (algebraMap ℚ k)) hPz,
        show polynomialY (E.map (algebraMap ℚ k))
          = MvPolynomial.pderiv (1 : Fin 3) (polynomial (E.map (algebraMap ℚ k))) from rfl,
        hq 1, zero_div]
    have hspan := hjac k (P 0 / P 2) (P 1 / P 2) heq
    rw [hX0, hY0, Ideal.eq_top_iff_one] at hspan
    simp at hspan

/-- **THE CHART JACOBIAN CRITERION** (PROVEN): on each of the three charts the two partial
derivatives of the dehomogenised Weierstrass cubic generate the UNIT ideal of the chart
ring.  This is what makes the chart ring locally a hypersurface with an invertible partial,
and it is where `hjac` — hence `Δ` — is consumed.

## NOT VACUOUS, and true on all three charts

Checked with a Gröbner basis over `ℚ(a₁, …, a₆)`: for each of the three charts the ideal
generated by `wᵢ` and its two partials is `(1)`.  So the statement holds for all `i`, not
merely for the affine chart, and `Δ` is genuinely doing the work (over `ℚ[a₁, …, a₆]` the
ideal is proper — that is the content of `Δ_mem_jacobianSpan`).

## The proof, and why it is UNIFORM in `i`

The plan recorded with this leaf while it was open had three cases: `hjac` applied directly
on the affine chart `i = 2`; a unit `Z/X` on the chart `i = 0`; and, for the chart `i = 1`
containing the point at infinity, a coprimality step `span {p₂, z} = ⊤` combined with
`IsCoprime.pow_right` over the localisation away from `z`.  A Gröbner cofactor certificate
was offered as the fallback for that last chart.

**None of that is needed, and there is no case split on `i` below.**  The move that removes
it is to apply `hjac` not over the chart ring itself but over a RESIDUE FIELD of it.
Suppose the span were proper.  Pull it back: the ideal
`J := (wᵢ, ∂wᵢ/∂u, ∂wᵢ/∂v)` of `ℚ[u, v]` is then proper too, since its image in
`ℚ[u, v] ⧸ (wᵢ)` is exactly the span in question.  So `J ⊆ M` for some maximal `M`, and
`k := ℚ[u, v] ⧸ M` is a FIELD.  Let `P : Fin 3 → k` be the image of the chart point, so
`P i = 1` and `P j = ūⱼ` for `j ≠ i`.  Then

* `eval P W = 0`, because `W` dehomogenises to `wᵢ ∈ J ⊆ M` (`eval_map_eq_dehomogenizeAt`);
* `eval P W_{Xⱼ} = 0` for `j ≠ i`, because dehomogenisation commutes with those partials
  (`pderiv_dehomogenizeAt`) and `∂wᵢ/∂uⱼ ∈ J ⊆ M`;
* `eval P W_{Xᵢ} = 0` as well, by Euler's relation together with `P i = 1`
  (`eval_pderiv_projPolynomial_eq_zero`).

So `P` is a singular point of the projective Weierstrass curve over a FIELD, which
`false_of_eval_pderiv_projPolynomial_eq_zero` rules out in two chart-free cases.

The point at infinity is not a special case here: it is the `P z = 0` case there, and what
disposes of it is the constant term of `W_Z` — precisely the fact the original plan had
identified as operative for the chart `i = 1`.  Passing to a residue field is what lets that
one observation serve all three charts at once, and it is why no localisation, no
`IsCoprime.pow_right`, and no Gröbner cofactor certificate appear in the proof. -/
theorem projChart_jacobian_span_eq_top (E : WeierstrassCurve ℚ) [E.IsElliptic] (i : Fin 3)
    (hjac : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (x y : S),
      (E.map (algebraMap ℚ S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap ℚ S)).toAffine.polynomialY} = ⊤) :
    Ideal.span (Set.range fun j : ProjChartVar i =>
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
          (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i)) = ⊤ := by
  classical
  by_contra hne
  -- the Jacobian ideal PULLED BACK to the polynomial ring is proper
  have hJ : Ideal.span (insert (projChartPolynomial E i)
      (Set.range fun j : ProjChartVar i =>
        MvPolynomial.pderiv j (projChartPolynomial E i))) ≠ ⊤ := by
    intro htop
    refine hne ((Ideal.eq_top_iff_one _).2 ?_)
    have hmap : Ideal.map (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}))
        (Ideal.span (insert (projChartPolynomial E i)
          (Set.range fun j : ProjChartVar i =>
            MvPolynomial.pderiv j (projChartPolynomial E i))))
        ≤ Ideal.span (Set.range fun j : ProjChartVar i =>
            (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
              (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i)) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro x ⟨y, hy, rfl⟩
      rcases hy with rfl | ⟨j, rfl⟩
      · simp only [SetLike.mem_coe]
        rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
        exact Ideal.zero_mem _
      · exact Ideal.subset_span ⟨j, rfl⟩
    refine hmap ?_
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}))]
    exact Ideal.mem_map_of_mem _ (htop ▸ Submodule.mem_top)
  obtain ⟨M, hM, hMle⟩ := Ideal.exists_le_maximal _ hJ
  haveI : M.IsMaximal := hM
  letI : Field (MvPolynomial (ProjChartVar i) ℚ ⧸ M) := Ideal.Quotient.field M
  refine false_of_eval_pderiv_projPolynomial_eq_zero E (MvPolynomial (ProjChartVar i) ℚ ⧸ M)
    hjac i (fun n => Ideal.Quotient.mkₐ ℚ M (if h : n = i then 1 else MvPolynomial.X ⟨n, h⟩))
    (by simp) ?_ ?_
  · rw [WeierstrassCurve.Projective.map_polynomial,
      eval_map_eq_dehomogenizeAt i (Ideal.Quotient.mkₐ ℚ M)]
    show (Ideal.Quotient.mkₐ ℚ M) (projChartPolynomial E i) = 0
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hMle (Ideal.subset_span (Set.mem_insert _ _)))
  · refine eval_pderiv_projPolynomial_eq_zero E _ i _ (by simp) ?_ ?_
    · rw [WeierstrassCurve.Projective.map_polynomial,
        eval_map_eq_dehomogenizeAt i (Ideal.Quotient.mkₐ ℚ M)]
      show (Ideal.Quotient.mkₐ ℚ M) (projChartPolynomial E i) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (hMle (Ideal.subset_span (Set.mem_insert _ _)))
    · intro n hn
      rw [WeierstrassCurve.Projective.map_polynomial, MvPolynomial.pderiv_map,
        eval_map_eq_dehomogenizeAt i (Ideal.Quotient.mkₐ ℚ M),
        ← pderiv_dehomogenizeAt i (⟨n, hn⟩ : ProjChartVar i)]
      show (Ideal.Quotient.mkₐ ℚ M)
        (MvPolynomial.pderiv (⟨n, hn⟩ : ProjChartVar i) (projChartPolynomial E i)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (hMle (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨⟨n, hn⟩, rfl⟩)))

/-- **A PLANE CURVE IS STANDARD SMOOTH OF RELATIVE DIMENSION `1` WHERE A PARTIAL DERIVATIVE
IS INVERTIBLE** (PROVEN; it was LEAF C of the residual item-7a leaf, and it is a piece of
MATHLIB rather than of this development).

## The construction

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
The one piece of plumbing is the identification of the presented ring with `T`,

  `ℚ[u, v, t] ⧸ (wᵢ, t·∂wᵢ/∂uⱼ - 1)`  ≃  `(ℚ[u, v] ⧸ (wᵢ))_{∂wᵢ/∂uⱼ}`.

It is built here by hand as a pair of mutually inverse maps rather than by chaining
mathlib's quotient/localisation equivalences: `Ideal.Quotient.liftₐ` in one direction and
`IsLocalization.lift` in the other, compared on generators with `MvPolynomial.ringHom_ext`
and `IsLocalization.ringHom_ext`.  That turned out to be markedly shorter than assembling
`MvPolynomial.optionEquivLeft`, `Ideal.polynomialQuotientEquivQuotientPolynomial` and
`Localization.awayEquivAdjoin`, and it avoids the `Algebra ℚ (MvPolynomial V ℚ ⧸ I)` SMul
diamond — `Submodule.Quotient.instSMul'` versus `Algebra.toSMul` — which defeats
`IsScalarTower.of_algebraMap_eq` on the nose and is why the maps below are compared as
RING homs wherever the chart ring is involved.

Then `SubmersivePresentation.ofAlgEquiv` transports the presentation onto `T`, and the
dimension count is `Nat.card (Option (ProjChartVar i)) - Nat.card (Fin 2) = 3 - 2 = 1`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`. -/
theorem isStandardSmoothOfRelativeDimension_projChartAway (E : WeierstrassCurve ℚ) (i : Fin 3)
    (j : ProjChartVar i) (T : Type) [CommRing T] [Algebra (ProjChartRing E i) T]
    [IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
      (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i) T] :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((algebraMap (ProjChartRing E i) T).comp (algebraMap ℚ (ProjChartRing E i))) := by
  classical
  algebraize [(algebraMap (ProjChartRing E i) T).comp (algebraMap ℚ (ProjChartRing E i))]
  -- the two relations of the presentation, in the variables `(u, v, t)`
  set v : Fin 2 → MvPolynomial (Option (ProjChartVar i)) ℚ :=
    ![MvPolynomial.rename Option.some (projChartPolynomial E i),
      MvPolynomial.X none * MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i)) - 1] with hv
  set P := MvPolynomial (Option (ProjChartVar i)) ℚ ⧸ (Ideal.span <| Set.range v) with hP
  -- `t` inverts `∂w/∂u` in `P`
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i)))) := by
    have key : Ideal.Quotient.mk (Ideal.span <| Set.range v)
        (MvPolynomial.rename Option.some
          (MvPolynomial.pderiv j (projChartPolynomial E i)))
        * Ideal.Quotient.mk _ (MvPolynomial.X none) = 1 := by
      rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (Ideal.span <| Set.range v)),
        ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨1, by simp [hv, mul_comm]⟩
    exact ⟨⟨_, _, key, by rw [mul_comm]; exact key⟩, rfl⟩
  set dbar : ProjChartRing E i := Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
    (MvPolynomial.pderiv j (projChartPolynomial E i)) with hdbar
  -- the ring map `C → P`
  have hkillw : ∀ a ∈ Ideal.span {projChartPolynomial E i},
      (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        (MvPolynomial.rename Option.some a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hz : (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        (MvPolynomial.rename Option.some (projChartPolynomial E i)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨0, by simp [hv]⟩
    rw [map_mul, map_mul, hz, mul_zero]
  set CtoP : ProjChartRing E i →ₐ[ℚ] P :=
    Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℚ (Ideal.span <| Set.range v)).comp
      (MvPolynomial.rename Option.some)) hkillw with hCtoP
  have hCtoP_mk : ∀ p, CtoP (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk (Ideal.span <| Set.range v) (MvPolynomial.rename Option.some p) :=
    fun p => rfl
  -- the ring map `P → T`
  set g : Option (ProjChartVar i) → T := fun o => match o with
    | none => IsLocalization.mk' T (1 : ProjChartRing E i) ⟨dbar, Submonoid.mem_powers _⟩
    | some x => algebraMap (ProjChartRing E i) T
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}) (MvPolynomial.X x)) with hg
  have hrename : ∀ p : MvPolynomial (ProjChartVar i) ℚ,
      MvPolynomial.aeval g (MvPolynomial.rename Option.some p)
        = algebraMap (ProjChartRing E i) T
          (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}) p) := by
    have : ((MvPolynomial.aeval g : MvPolynomial (Option (ProjChartVar i)) ℚ →ₐ[ℚ] T) :
          MvPolynomial (Option (ProjChartVar i)) ℚ →+* T).comp
          ((MvPolynomial.rename Option.some :
            MvPolynomial (ProjChartVar i) ℚ →ₐ[ℚ] MvPolynomial (Option (ProjChartVar i)) ℚ) :
            MvPolynomial (ProjChartVar i) ℚ →+* _)
        = (algebraMap (ProjChartRing E i) T).comp
          (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun n => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom,
          MvPolynomial.rename_C, MvPolynomial.aeval_C]
        exact IsScalarTower.algebraMap_apply ℚ (ProjChartRing E i) T r
      · simp [hg]
    exact fun p => congrArg (fun f : MvPolynomial (ProjChartVar i) ℚ →+* T => f p) this
  have hginv : g none * algebraMap (ProjChartRing E i) T dbar = 1 := by
    show IsLocalization.mk' T (1 : ProjChartRing E i) ⟨dbar, Submonoid.mem_powers _⟩
      * algebraMap (ProjChartRing E i) T dbar = 1
    rw [IsLocalization.mk'_spec, map_one]
  have hkillv : ∀ a ∈ Ideal.span (Set.range v), MvPolynomial.aeval g a = 0 := by
    intro a ha
    refine Submodule.span_induction ?_ (by simp) (by intro x y _ _ hx hy; simp [hx, hy])
      (by intro c x _ hx; simp [hx]) ha
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · show MvPolynomial.aeval g
        (MvPolynomial.rename Option.some (projChartPolynomial E i)) = 0
      rw [hrename, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self _), map_zero]
    · show MvPolynomial.aeval g (MvPolynomial.X none * MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i)) - 1) = 0
      rw [map_sub, map_mul, MvPolynomial.aeval_X, hrename, map_one, ← hdbar, hginv, sub_self]
  set PtoT : P →ₐ[ℚ] T := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval g) hkillv with hPtoT
  have hPtoT_mk : ∀ q, PtoT (Ideal.Quotient.mk (Ideal.span <| Set.range v) q)
      = MvPolynomial.aeval g q := fun q => rfl
  -- the ring map `T → P`
  have hCtoP_dbar : CtoP dbar = Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i))) := rfl
  have hunits : ∀ y : Submonoid.powers dbar, IsUnit ((CtoP : ProjChartRing E i →+* P) y) := by
    rintro ⟨_, n, rfl⟩
    rw [show ((CtoP : ProjChartRing E i →+* P) (dbar ^ n)) = (CtoP dbar) ^ n from map_pow _ _ _,
      hCtoP_dbar]
    exact hunit.pow n
  set TtoP : T →+* P := IsLocalization.lift hunits with hTtoP
  have hTtoP_alg : ∀ c, TtoP (algebraMap (ProjChartRing E i) T c) = CtoP c :=
    fun c => IsLocalization.lift_eq hunits c
  have hcomp : ∀ c : ProjChartRing E i, PtoT (CtoP c) = algebraMap (ProjChartRing E i) T c := by
    intro c
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hCtoP_mk, hPtoT_mk, hrename]
  -- the two composites are the identity
  have hTP : ∀ x : T, PtoT (TtoP x) = x := by
    have := IsLocalization.ringHom_ext (M := Submonoid.powers dbar) (S := T)
      (j := (PtoT : P →+* T).comp TtoP) (k := RingHom.id T)
      (RingHom.ext fun c => by
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
          AlgHom.coe_toRingHom]
        rw [hTtoP_alg, hcomp])
    exact fun x => congrArg (fun f : T →+* T => f x) this
  have hPT : ∀ x : P, TtoP (PtoT x) = x := by
    have : (TtoP.comp (PtoT : P →+* T)).comp
        (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        = (RingHom.id P).comp (Ideal.Quotient.mk (Ideal.span <| Set.range v)) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun n => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
            AlgHom.coe_toRingHom]
        rw [hPtoT_mk]
        simp only [MvPolynomial.aeval_C]
        rw [IsScalarTower.algebraMap_apply ℚ (ProjChartRing E i) T r, hTtoP_alg]
        exact (CtoP.commutes r).trans (by rfl)
      · cases n with
        | none =>
          simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
            AlgHom.coe_toRingHom]
          rw [hPtoT_mk]
          simp only [MvPolynomial.aeval_X]
          show TtoP (IsLocalization.mk' T (1 : ProjChartRing E i)
            ⟨dbar, Submonoid.mem_powers _⟩) = _
          rw [IsLocalization.lift_mk'_spec]
          rw [map_one]
          change (1 : P) = CtoP dbar *
            Ideal.Quotient.mk (Ideal.span <| Set.range v) (MvPolynomial.X none)
          rw [hCtoP_dbar, ← map_mul, eq_comm, ← sub_eq_zero,
            ← map_one (Ideal.Quotient.mk (Ideal.span <| Set.range v)), ← map_sub,
            Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span ⟨1, by simp [hv, mul_comm]⟩
        | some x =>
          simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
            AlgHom.coe_toRingHom]
          rw [hPtoT_mk]
          simp only [MvPolynomial.aeval_X]
          show TtoP (algebraMap (ProjChartRing E i) T
            (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}) (MvPolynomial.X x))) = _
          rw [hTtoP_alg, hCtoP_mk, MvPolynomial.rename_X]
    intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun f : MvPolynomial (Option (ProjChartVar i)) ℚ →+* P => f q) this
  -- the isomorphism `P ≃ₐ[ℚ] T`
  set eA : P ≃ₐ[ℚ] T := AlgEquiv.ofRingEquiv
    (f := { (PtoT : P →+* T) with invFun := TtoP, left_inv := hPT, right_inv := hTP })
    (fun x => PtoT.commutes x) with heA
  -- `∂/∂t` kills everything pulled back from the chart variables
  have hpd0 : ∀ p : MvPolynomial (ProjChartVar i) ℚ,
      MvPolynomial.pderiv (none : Option (ProjChartVar i))
        (MvPolynomial.rename Option.some p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp => simp [hp]
  have ha : Function.Injective (![some j, none] : Fin 2 → Option (ProjChartVar i)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hdet : (Algebra.PreSubmersivePresentation.naive (R := ℚ) (v := v)
      ![some j, none] ha).jacobiMatrix.det
      = (MvPolynomial.rename Option.some
          (MvPolynomial.pderiv j (projChartPolynomial E i))) ^ 2 := by
    rw [Matrix.det_fin_two, Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    simp only [hv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      map_sub, map_one, MvPolynomial.pderiv_X, Derivation.leibniz,
      MvPolynomial.pderiv_rename (Option.some_injective (ProjChartVar i)), hpd0]
    simp [sq]
  refine (Algebra.SubmersivePresentation.ofAlgEquiv
    ⟨Algebra.PreSubmersivePresentation.naive (R := ℚ) (v := v) ![some j, none] ha, ?_⟩
    eA).isStandardSmoothOfRelativeDimension ?_
  · rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hdet, map_pow]
    refine IsUnit.pow 2 ?_
    show IsUnit (Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i))))
    exact hunit
  · show Nat.card (Option (ProjChartVar i)) - Nat.card (Fin 2) = 1
    simp

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
* `isStandardSmoothOfRelativeDimension_projChartAway` (**PROVEN**) — on each of the two
  localisations the `2 × 2` Jacobian of the relations `(wᵢ, t·∂wᵢ/∂u - 1)` in the generators
  `(u, v, t)` is triangular with determinant `(∂wᵢ/∂u)²`, a unit there, so the presentation
  is submersive of dimension `3 - 2 = 1`.

Leaves A and B each carry their own proof plan; see their docstrings.  A Gröbner computation confirms the
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

/-- **The projective Weierstrass model is geometrically reduced over `ℚ`**
(PROVEN, from `smoothOfRelativeDimension_projToSpec` through the general
bridge `AlgebraicGeometry.GeometricallyReduced.of_smooth`).

TRUE and standard: `projToSpec E` is smooth (`smoothOfRelativeDimension_projToSpec`),
`SmoothOfRelativeDimension` is stable under base change, and a smooth scheme over
a field is regular, hence reduced.  Every fibre `proj E ×_ℚ Spec K` is therefore
reduced, which is the definition of `GeometricallyReduced`.

## WHY THIS IS A SEPARATE LEAF: THE GAP IS IN MATHLIB, NOT HERE

The statement that is actually missing is not about elliptic curves at all.
It is

    Smooth f → GeometricallyReduced f

(equivalently, its fibrewise content: *a scheme smooth over a field is
reduced*), and **it is absent from the pin**.  Verified by grep on
2026-07-27, and the negative results are recorded so the next owner does
not repeat them:

* `AlgebraicGeometry/Morphisms/Smooth.lean` mentions `IsReduced` exactly
  once, in the hypotheses of `Scheme.Hom.dense_smoothLocus_of_perfectField`
  — never in a conclusion.
* `RingTheory/Nilpotent/GeometricallyReduced.lean` defines
  `IsGeometricallyReduced` and, outside its own file, **nothing in mathlib
  ever instantiates it**.
* `IsRegularLocalRing` is nowhere connected to smoothness or formal
  smoothness: `grep -rn IsRegularLocalRing RingTheory/ | grep -i
  'smooth\|etale\|formally'` is empty.  `RingTheory/Smooth/Local.lean`
  contains only the three `FormallySmooth.iff_injective_*` cotangent
  criteria, and `RingTheory/Smooth/StandardSmooth.lean` proves nothing
  about domains, reducedness or regularity.
* There is no perfect-field shortcut either — `PerfectField` does not
  occur in `RingTheory/Nilpotent/GeometricallyReduced.lean` or in any
  `AlgebraicGeometry/Geometrically/*.lean`, so the char-`0` identification
  of "reduced" with "geometrically reduced" is also unavailable and cannot
  be used to route around this.

## ROUTE TAKEN (2026-07-27): route 1, and it is now WRITTEN

Route 1 below was taken.  `Smooth f → GeometricallyReduced f` is now a
general theorem of this development,
`AlgebraicGeometry.GeometricallyReduced.of_smooth` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`, and
this declaration is a two-line consequence of it.  **There is no residual
gap: that file is sorry-free as of 2026-07-27.**  Its former leaf
`Algebra.Smooth.isReduced_of_isField` (*a smooth algebra over a field is
reduced*) is PROVEN, over the standard-open reduction to
`Algebra.IsStandardSmooth.isReduced_of_field`; everything
scheme-theoretic — the base change, the affine cover, and the passage from
`Γ` back to the scheme — was already proven there.

The recorded absence audit above is **superseded and partly refuted** by the
one in that file's docstring: the regular-local-ring absences it lists are
real, but they do not block the route, because mathlib's
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`
(`Mathlib/RingTheory/RingHom/StandardSmooth.lean`, in neither directory the
audit searched) factors a standard smooth map through a polynomial ring
étale-ly, and reducedness then descends from the generic fibre.  Note route 1
pays for itself immediately: all of
`GeometricallyReduced`'s base-change instances now apply to *any* smooth
morphism in this development.

**Why this declaration sits here, after the smoothness proof, rather than
next to the rest of the group-law material**: Lean's declaration order.
Its proof consumes `smoothOfRelativeDimension_projToSpec`, so it — and
with it `isReduced_triProd_proj`, `projMul_assoc`, `exists_projAdd` and
`nonempty_projGroupLaw`, which consume it in turn — had to move below the
chart/smoothness block.  The text of those five declarations is otherwise
unchanged.

*The parochial route, NOT taken*, recorded so it is not re-surveyed: show
   directly that `K[X, Y, Z] ⧸ (W)` is a domain for every field `K ⊇ ℚ`, i.e. that the Weierstrass cubic is
   irreducible — a cubic that factors has a linear factor, so the curve
   contains a line and is singular, contradicting `Δ ≠ 0`.  This needs, in
   addition, that `Proj` commutes with the base change `ℚ → K`, and that
   `Proj` of a graded domain is reduced; **neither is in the pin either**
   (there is no `IsReduced`/`IsIntegral` result anywhere in
   `AlgebraicGeometry/ProjectiveSpectrum/`).  So route 1 was both more
   general and strictly less work.  (The `Proj`-base-change half of it is
   in any case what `isIso_projBaseChangeHom` is about, and that leaf is
   still open.) -/
theorem geometricallyReduced_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    GeometricallyReduced (projToSpec E) :=
  haveI := smoothOfRelativeDimension_projToSpec E
  haveI : AlgebraicGeometry.Smooth (projToSpec E) :=
    SmoothOfRelativeDimension.smooth 1 (projToSpec E)
  _root_.AlgebraicGeometry.GeometricallyReduced.of_smooth (projToSpec E)

/-- **The threefold fibre product `A ×_ℚ A ×_ℚ A` is reduced** (PROVEN
from `geometricallyReduced_projToSpec` and `isProper_projToSpec`).

This is the `[IsReduced X]` side condition of
`ext_of_fromSpecResidueField_eq`, and it is the reason the density route
needs no hand-rolled irreducible-component argument: mathlib's

    instance [GeometricallyReduced g] [Flat g] [IsReduced X]
      [IsLocallyNoetherian X] : IsReduced (pullback f g)

(`AlgebraicGeometry/Geometrically/Reduced.lean`) applies twice, once to
build `A ×_ℚ A` from `A` and once to build `A ×_ℚ A ×_ℚ A` from that.  The
four inputs it wants are supplied as follows, and all but the first are
free:

* `GeometricallyReduced (projToSpec E)` — PROVEN, see above;
* `Flat (projToSpec E)` — **free, and this is worth knowing**: mathlib has
  `instance (priority := low) [Subsingleton Y] [IsIntegral Y] : Flat f`
  (`AlgebraicGeometry/Morphisms/Flat.lean`), and `Spec ℚ` is a one-point
  integral scheme, so `infer_instance` discharges it.  An earlier version
  of this proof routed flatness through smoothness instead; that made this
  declaration depend on the still-open `locally_isStandardSmooth_awayCoord`
  for no reason at all.  Over a field, EVERY morphism is flat;
* `IsLocallyNoetherian` of `proj E` and of `A ×_ℚ A` —
  `LocallyOfFiniteType.isLocallyNoetherian` applied to the structure
  morphisms, `LocallyOfFiniteType` coming from `IsProper`;
* `IsReduced (proj E)` — `isReduced_of_flat_of_isLocallyNoetherian`, i.e.
  the same geometric reducedness descended along the reduced noetherian
  base `Spec ℚ`. -/
theorem isReduced_triProd_proj (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    IsReduced (AbelianSchemeStruct.triProd (projToSpec E)) := by
  haveI := isProper_projToSpec E
  haveI := geometricallyReduced_projToSpec E
  haveI : IsLocallyNoetherian (proj E) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpec E)
  haveI : IsReduced (proj E) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (projToSpec E)
  haveI : IsLocallyNoetherian (Limits.pullback (projToSpec E) (projToSpec E)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Limits.pullback.fst (projToSpec E) (projToSpec E) ≫ projToSpec E)
  haveI : IsReduced (Limits.pullback (projToSpec E) (projToSpec E)) := inferInstance
  exact inferInstance

/-- **The chord–tangent multiplication morphism, with the three axioms
that are chart identities** (**PROVEN as of 2026-07-27** from
`exists_projMulOfCoords` and the four small leaves of the `ProjCoords`
section above — the CONSTRUCTION half of the old `exists_projAdd`, which
is proven from this together with `projMul_assoc`).

## STATUS: this declaration has NO `sorry` of its own any more

It is a REDUCTION, not a result: it is proven from four open leaves, of
which one (`exists_projMulOfCoords`) still carries the gluing.  Do not read
it as finished.  The four are, with the machinery they need:

| leaf | what it is |
|---|---|
| `ProjCoords.toHom_smul` | the missing MATHLIB congruence for `fromOfGlobalSections` |
| `ProjCoords.exists_of_specField` | `Pic (Spec K) = 0`, i.e. `K`-points have coordinates |
| `ProjCoords.toHom_eq_of_addXYZ_not_span` | the exceptional set is the DIAGONAL |
| `exists_projMulOfCoords` | the gluing, plus `hunit` and `hinv` |

A fifth, `WeierstrassCurve.Projective.equation_addXYZ` (the polynomial
certificate `W(add…) ∈ (W(P), W(Q))` over an arbitrary commutative ring), was
also cut out and is now PROVEN, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveAddition.lean`.

## THE STATEMENT NOW PUBLISHES A CHART DESCRIPTION OF `m`

(Cut-level call by the orchestrator, 2026-07-27, and it is the first
conjunct.)  The old existential said only `∃ m, hcomm ∧ hunit ∧ hinv`,
which pins NOTHING about the witness — so no consumer could compute with
it, and in particular `projMul_assoc` could not be specialised to it and
the chart-wise `linear_combination` route to associativity stayed
unavailable to the whole tree.  The first conjunct fixes that: it says
that on any test scheme carrying coordinate data for the two arguments,
`m` is given by the chord–tangent triple wherever that triple is
non-degenerate.  That is exactly the certificate a chart-wise
associativity proof needs, and it is also what a `ℚ̄`-point dictionary
would consume.

*Not propagated further on purpose*: `exists_projAdd` and
`ProjGroupLaw` still do not carry the clause, because `ProjGroupLaw` is a
structure owned by the item-5/6 cut and adding a field to it is a
cut-level change on someone else's declaration.  `exists_projAdd`
currently discards the clause with `-`.

## WHAT IS TRUE, AND THE CORRECTION TO THE PREVIOUS VERSION OF THIS TEXT

TRUE and classical.  The previous version of this paragraph said that
`hcomm`, `hunit` and `hinv` "are demanded here because each is an
identity between the *same* polynomial forms that define `m` on a chart,
so whoever writes the charts gets them essentially for free".  **That is
right for `hcomm` and wrong for the other two**, and the distinction is a
consequence of the same corrected computation that identified the
diagonal as the exceptional set:

* `hcomm` really is free from the STANDARD law alone: the three forms are
  antisymmetric (`projAddXYZ_comm`, a `ring` identity), so the two sums
  differ by the unit `-1`; and where the standard law degenerates the two
  points are equal, so commutativity is trivial.  It is therefore proven
  here, not assumed — see `projMulCoords_comm`.
* `hunit` and `hinv` are NOT free from the standard law.
  `addXYZ ![0,1,0] Q = Q z • Q` is a rescaling of `Q` only where `Q z` is
  a unit, and at `Q = O` the standard triple vanishes identically; and
  `addXYZ (negOf P) P` vanishes identically at the `2`-torsion.  Both
  gaps are covered by the SECOND Bosma–Lenstra law, which is
  non-degenerate on the diagonal — so they stay with the constructor, in
  `exists_projMulOfCoords`, where both laws are in scope.

`hassoc` is not a chart identity at all and is split off into
`projMul_assoc`.

## The formulas: both laws are now explicit

(The heading here used to read "the one that does not [exist]".  As of
2026-07-27 the second law is constructed and CAS-verified; what remains
missing is scheme-theoretic, not polynomial.)

`WeierstrassCurve.Projective.addX`/`addY`/`addZ`
(`EllipticCurve/Projective/Formula.lean`) are honest polynomial forms
over an arbitrary `[CommRing R]`, bihomogeneous of bidegree `(2, 2)`:
`addX_smul`/`addY_smul`/`addZ_smul` all read
`add? (u • P) (v • Q) = (u * v) ^ 2 * add? P Q`.  Instantiating
`P = ![X 0, X 1, X 2]`, `Q = ![X 3, X 4, X 5]` in
`MvPolynomial (Fin 6) ℚ` turns them into genuine bihomogeneous
polynomials, which is the form the gluing needs.

### CORRECTION (2026-07-27): the exceptional locus is the DIAGONAL ONLY

A previous version of this docstring said the triple "vanishes identically
on the bidegree-`(1,1)` locus `x(P) = x(Q)` — which contains both the
diagonal and the antidiagonal".  **That is FALSE, and mathlib's own
`negAddY_of_X_eq'` refutes it in one line**:

`negAddY P Q * (P z * Q z) ^ 2 = (P y * Q z - Q y * P z) ^ 3 * (P z * Q z)`.

So on `x(P) = x(Q)` we do get `addX = addZ = 0` (`addX_of_X_eq`,
`addZ_of_X_eq`), but `addY = -negAddY` is a UNIT there whenever
`y(P) ≠ y(Q)` — and the triple `[0 : addY : 0]` is exactly the point at
infinity `[0 : 1 : 0]`, which is the CORRECT value of `P + Q` on the
antidiagonal.  The standard law is perfectly good there.

**The true exceptional set of the standard law is the diagonal `Δ` alone**:
all three of `addX`, `addY`, `addZ` vanish at `(P, Q)` iff
`x(P) = x(Q)` and `y(P) = y(Q)`, i.e. iff `P = Q`.  This matters: it is
what makes a SECOND law suffice, and it tells the next owner what the
second law actually has to achieve (be nonzero on `Δ`), rather than
sending them to cover a locus that is not exceptional at all.

### Bosma–Lenstra: the laws are indexed by LINES in `P²`

W. Bosma and H. W. Lenstra, *Complete systems of two addition laws for
elliptic curves*, J. Number Theory **53** (1995) 229–240.  Their
structure theorem is the thing that makes the second law explicit rather
than mysterious:

> For a Weierstrass model `C ⊂ P²`, the addition laws of bidegree
> `(2, 2)` form a 3-dimensional space in bijection with the lines
> `ℓ = {aX + bY + cZ = 0}` of `P²`, and a pair `(P, Q)` is exceptional
> for the law of `ℓ` **iff `P - Q` lies on `ℓ`**.

The standard law is the law of `ℓ = {Z = 0}`: `P - Q ∈ {Z = 0}` iff
`P - Q = O` (the line at infinity meets `C` only at the inflection `O`,
with multiplicity 3) iff `P = Q` — which is exactly the corrected
computation above.  Two laws therefore form a complete system as soon as
their lines meet `C` in disjoint sets, and **any line missing
`O = [0 : 1 : 0]` will do**.  Take `ℓ₂ = {Y = 0}`, i.e. the tuple
`(a, b, c) = (0, 1, 0)`: then `O ∉ ℓ₂` since `O` has `Y = 1`, so no pair
is exceptional for both.  Both laws are defined over `ℤ`, so no field
extension and no Galois descent is needed.

### The second law, explicitly (CAS-computed and CAS-verified, 2026-07-27)

Write `negOf Q := ![Q x, W.negY Q, Q z]` (linear in `Q`, so composing with
it preserves bidegree) and

  `sub? P Q := add? P (negOf Q)`  for `? ∈ {X, Y, Z}`,

a bidegree-`(2,2)` representative of `P - Q`.  Then:

* **`subZ ≡ addZ` modulo `(W(P), W(Q))`** — verified in Magma.  Both
  satisfy `· * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3` (`negY` does not
  change `x` or `z`), and `R/(W(P), W(Q))` is a domain.
* Consequently the Bosma–Lenstra `(0,1,0)` law is `L₁ · subY / subZ`, and
  **its `Z`-coordinate is simply `subY`** — no new polynomial is needed
  for it:

      add2Z P Q := W.addY P (negOf Q)

* `add2X` and `add2Y` are the UNIQUE bidegree-`(2,2)` forms with

      add2X P Q * addZ P Q ≡ addX P Q * add2Z P Q   mod (W(P), W(Q))
      add2Y P Q * addZ P Q ≡ addY P Q * add2Z P Q   mod (W(P), W(Q))

  Uniqueness is free and worth knowing, because it means the next owner
  can *recompute* rather than trust a transcription: `R/(W(P), W(Q))` is
  a domain and `addZ ≠ 0` in it, so the identities pin `add2X`, `add2Y`
  modulo the ideal; and the ideal has NO nonzero element of bidegree
  `(2,2)` (its generators have bidegree `(3,0)` and `(0,3)`, so a
  cofactor would need a negative degree), so they are pinned on the nose.

These identities also *are* the statement that the two laws agree where
both are defined — the two triples are proportional — which is what the
overlap condition of the gluing needs.

**How to regenerate the polynomials** (about 5 minutes of Magma; `magma`
is at `/opt/bin/magma`).  Work in
`R = Q(a1..a6)[Px,Py,Pz,Qx,Qy,Qz]`, `I = (W(P), W(Q))`; note `{W(P), W(Q)}`
is already a Gröbner basis (coprime leading terms).  Expand a generic
bidegree-`(2,2)` form `F` over the 36 monomials
`{Px²,PxPy,PxPz,Py²,PyPz,Pz²} × {Qx²,…,Qz²}`, reduce
`F * addZ - addX * subY` modulo `I`, equate coefficients, and solve the
linear system.  It is consistent and has a unique solution; `add2X` comes
out with 27 monomials and `add2Y` with 18, with coefficients polynomial in
`a₁, a₂, a₃, a₄, a₆`.  *Two traps that cost a cycle each*: Magma's
`[ f(i,j) : i in I, j in J ]` varies the LEFT index fastest while
`Matrix(K,r,c,seq)` fills row-major, so build the matrix from an explicit
list of rows; and sanity-check the solver by first solving
`F * addZ = addX * subZ`, which must return `F = addX`.

*Do not copy the formulas out of Bosma–Lenstra's printed tables*: the
`X` and `Y` coordinates of their `(0,1,0)` law are **misprinted** in the
paper.  (Reported independently in M. Parada Seguí, *Elliptic curves:
various models and their addition laws*, MSc thesis, Radboud Univ.,
§1.2.2, which had to recompute them for the same reason.)

*`dblXYZ` is still not the second law and the next owner must not reach
for it*: `dblXYZ_smul` reads `dblXYZ (u • P) = u ^ 4 • dblXYZ P`, i.e. it
is a single-variable form of degree `4` along the diagonal, not a
bihomogeneous law on a neighbourhood of it, so it does not define a
morphism on any open subset of `A ×_ℚ A`.  *Refuting check*: look for a
`Fin 3 → R → Fin 3 → R → R` in `Formula.lean` whose `smul` lemma has the
shape `(u * v) ^ n` other than the `add?` family — there is none.

## What the gluing needs, in the order it is needed

1. An open cover of `A ×_ℚ A` by the non-degeneracy loci of the two
   laws.  That the two loci COVER is a Nullstellensatz statement: the
   ideal generated by the six forms contains a power of the irrelevant
   ideal modulo `(W(P), W(Q))`.  This is exactly the class the CAS
   doctrine is for — get the cofactor certificate out of `Singular` or
   `Magma` and verify the concrete witness in Lean with
   `linear_combination`.

   *The Bosma–Lenstra theorem above says this certificate EXISTS*, and
   says exactly why: a common zero would be a pair `(P, Q)` exceptional
   for both laws, hence with `P - Q` on both `{Z = 0}` and `{Y = 0}`,
   hence `P - Q = O` and `Y(O) = 0` — but `O = [0 : 1 : 0]`.  So this is
   a certificate hunt with a guaranteed answer, not an open question.
   As a smoke test before spending the search: the restrictions of the
   second law to the diagonal are visibly nonzero, e.g. for
   `a₁ = a₂ = a₃ = 0` one gets
   `add2Z P P = -8 * P y ^ 3 * P z` and
   `add2Y P P = -(P y ^ 4) - 3a₄ P x P y ^ 2 P z - 18a₆ P y ^ 2 P z ^ 2
   + 9a₄² P x ^ 2 P z ^ 2 + 27a₄a₆ P x P z ^ 3 + (a₄³ + 27a₆²) P z ^ 4`,
   the second of which is a unit exactly where the first is not (at
   2-torsion, where `P y = 0`).
2. On each piece, the morphism into `proj E`.  The only `Proj`-valued
   construction at this pin is
   `AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf`, which wants a
   ring map `f : A →+* Γ(X, ⊤)` with the image of the irrelevant ideal
   generating — i.e. it wants the tautological bundle TRIVIALISED on `X`.
   That is fine chart by chart (it is why it worked for `projInfty`), and
   it is the reason a cover is unavoidable.
3. **The genuinely missing mathlib lemma, and it is the load-bearing
   one**: `fromOfGlobalSections` is invariant under rescaling the
   coordinates by a unit.  Precisely — for `u : Γ(X, ⊤)ˣ` let
   `f_u : A →+* Γ(X, ⊤)` be `a ↦ ∑ n, u ^ n * f aₙ` (a ring hom, because
   `A` is graded), then
   `fromOfGlobalSections 𝒜 f_u hf' = fromOfGlobalSections 𝒜 f hf`.
   Without it the two charts cannot be shown to agree on their overlap,
   where the two addition laws differ by exactly such a unit.
   *Refuting check*: grep `ProjectiveSpectrum/Basic.lean` for any
   congruence lemma for `fromOfGlobalSections` in its `f` argument —
   there is none; the file has only `_preimage_basicOpen`,
   `_morphismRestrict`, `_resLE` and `_toSpecZero`.  (Re-checked
   2026-07-27 against the current pin: still absent.  This item is the
   one piece of the leaf that is genuinely new MATHLIB work.)

   The unit is now explicit, which is worth having when stating it: on
   the overlap the identities above give
   `(add2X, add2Y, add2Z) = (add2Z / addZ) • (addX, addY, addZ)`, so
   `u = add2Z / addZ`, invertible exactly where both laws are
   non-degenerate.
4. Then `Scheme.OpenCover.glueMorphisms` assembles `m`, and `hcomm`,
   `hunit`, `hinv` are checked chart-wise against the same forms.  All
   three are cheap, and the polynomial facts behind them have been
   checked (Magma, 2026-07-27) — the next owner should not re-derive
   them:

   * `hcomm`: **all three forms are ANTISYMMETRIC**,
     `add? Q P = - add? P Q` (this is a `ring` identity — no curve
     equation needed).  A projective triple and its negative are the same
     point, so commutativity is immediate.  The previous wording here
     ("visibly symmetric … up to the sign that `negY` absorbs") was
     vaguer than the truth and pointed at the wrong mechanism.
   * `hunit`: `(addX, addY, addZ) (P, O) = -P z • (P x, P y, P z)` on the
     nose, where `O = ![0, 1, 0]` — again a `ring` identity, and visibly
     `∝ P`.  It degenerates only at `P z = 0`, i.e. at `P = O`, i.e. at
     the single pair `(O, O)`, which lies on `Δ` and so is covered by the
     second law.
   * `hinv`: modulo `W(P)`, `addX (P, negOf P) = addZ (P, negOf P) = 0`,
     so the value is `[0 : addY (P, negOf P) : 0] = O` as required.  And
     `addY (P, negOf P)` is **literally the polynomial `add2Z P P`**
     (immediately from `add2Z P Q = addY P (negOf Q)`) — the same
     quantity whose non-vanishing makes the second law work on `Δ`.  So
     `hinv` and the diagonal non-degeneracy of law 2 are one fact, not
     two, and proving either gives the other.

## What this leaf does NOT have to do any more, and why

Five obligations were removed from the original single leaf, and the
statement below is the residue.  **This is a strengthening, not a
weakening**: `hunit` and `hinv` are demanded against the specific, named
`projInfty E` and `projNeg E` rather than against an existentially
quantified `e` and `i`, so a witness for this leaf is strictly harder to
produce than a witness for the old one, and the old statement follows
from it (see `nonempty_projGroupLaw`).

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
* `hassoc` is **no longer here at all** — see `projMul_assoc`. -/
theorem exists_projMul (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E,
      (∀ (X : Scheme.{0}) (c d : ProjCoords E X)
            (h : Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤),
            Limits.pullback.lift c.toHom d.toHom (hom_ext_spec_rat _ _) ≫ m =
              (c.add d h).toHom) ∧
        Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
              (Limits.pullback.fst (projToSpec E) (projToSpec E))
              Limits.pullback.condition.symm ≫ m = m ∧
        Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E) ∧
          Limits.pullback.lift (projNeg E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E := by
  obtain ⟨m, hlaw, hunit, hinv⟩ := exists_projMulOfCoords E
  refine ⟨m, hlaw, ?_, hunit, hinv⟩
  haveI := isProper_projToSpec E
  haveI := geometricallyReduced_projToSpec E
  haveI : IsLocallyNoetherian (proj E) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpec E)
  haveI : IsReduced (proj E) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (projToSpec E)
  haveI : IsLocallyNoetherian (Limits.pullback (projToSpec E) (projToSpec E)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Limits.pullback.fst (projToSpec E) (projToSpec E) ≫ projToSpec E)
  haveI : IsReduced (Limits.pullback (projToSpec E) (projToSpec E)) := inferInstance
  refine ext_of_fromSpecResidueField_eq _ _ (projToSpec E) Set.univ dense_univ ?_
    (hom_ext_spec_rat _ _)
  intro x _
  rw [comp_swap_eq_lift_comp, comp_eq_lift_comp E m
    ((Limits.pullback (projToSpec E) (projToSpec E)).fromSpecResidueField x)]
  exact projMulCoords_comm E m hlaw
    ((Limits.pullback (projToSpec E) (projToSpec E)).residueField x) (Field.toIsField _) _ _


/-- **`m` IS THE CHORD-TANGENT MULTIPLICATION**, as a named predicate: the first conjunct of
`exists_projMul` above, pulled out so that a downstream statement can take it as a
hypothesis without restating it.

Written as an `abbrev` on purpose — it must unfold definitionally, so that the witness
`exists_projMul` hands back is accepted where an `IsProjMulLaw E m` is expected, with no
bridging lemma.

**Why it exists at all** (integration, 2026-07-27).  `exists_projMul_geomFibreEquivVal`
needs exactly this clause to pin its `m`, and restating the clause inline in that
declaration's signature — five thousand lines further down — sent the elaborator into a
`whnf` timeout, while the identical text elaborates here in milliseconds.  Naming it once,
at the point where it is already being elaborated, is both cheaper and the honest statement
of what the downstream leaf assumes. -/
abbrev IsProjMulLaw (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E) : Prop :=
  ∀ (X : Scheme.{0}) (c d : ProjCoords E X)
      (h : Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤),
    Limits.pullback.lift c.toHom d.toHom (hom_ext_spec_rat _ _) ≫ m = (c.add d h).toHom

/-- **Associativity of any commutative unital multiplication with
`projNeg`-inverses on the projective Weierstrass model** (PROVEN from
`geometricallyReduced_projToSpec` and `projMul_assoc_pt`, whose own
residue is now `exists_projPtAddEquiv_algClosed` — the ABSTRACT half of
the old `exists_projAdd`).

## FAITHFULNESS AUDIT: why this is TRUE for an arbitrary such `m`

The hypotheses do not obviously pin `m` down, so the first question is
whether the statement is false.  It is not, and the reason is Milne,
*Abelian Varieties* I, Corollary 2.5: for complete varieties `V`, `W`
with rational points and `A` an abelian variety, every morphism
`h : V × W → A` with `h(v₀, w₀) = 0` is uniquely `f ∘ p + g ∘ q`.
Applied to `V = W = A = E` over `ℚ̄` this says every morphism
`E × E → E` has the form `(P, Q) ↦ φ(P) + ψ(Q) + c`.  The unit law
`m(O, Q) = Q` forces `ψ = id` and `φ(O) + c = 0`; the unit law in the
other argument — which follows here from `hcomm` — forces `φ = id` and
`c = 0`.  So `m` *is* the classical group law on `ℚ̄`-points, hence
associative.  `E` really is an abelian variety, so the appeal is sound.

**But that argument is not available inside the formalization**, because
it presupposes the group structure this node is constructing.  It settles
faithfulness only; it is not a proof route.

## ROUTE AUDIT (2026-07-27), correcting the previous one

The previous audit named "a rigidity / theorem-of-the-cube route
deriving `hassoc` from the other three axioms plus properness, without
touching points at all" as the promising unsearched axis.  **That axis was
searched and it does not close as stated.**  Milne I.2.1 (Rigidity) says:
if `V` is complete and `f : V × W → U` is constant on `V × {w₀}` and on
`{v₀} × W`, then `f` is constant.  Every corollary that turns this into a
statement about a multiplication — I.2.2 (a morphism is a homomorphism up
to translation), I.2.4 (commutativity), I.2.5 above — forms the
*difference* of two morphisms and therefore **presupposes the group law
on the target**.  To prove `hassoc` one would apply rigidity to
`φ(x, y, z) = m(m(x, y), z) − m(x, m(y, z))`, and that subtraction is
precisely what is not yet available.  So rigidity does not bootstrap
associativity out of unitality; something else must pin `m` first.
*Refuting check*: find a statement of the rigidity lemma, or of the
theorem of the cube, whose target is a bare proper variety rather than a
group object — Milne I.2, Mumford *AV* §II.4 and Debarre's notes all
require the group.

That leaves two routes, and the next owner should pick one deliberately:

* **The density route.**  `A ×_ℚ A ×_ℚ A` is reduced and of finite type
  over `ℚ` (characteristic `0`, and `Δ ≠ 0` makes the fibre a smooth
  curve), so it suffices to prove the two composites agree on
  `ℚ̄`-points, where the statement is `add_assoc` in mathlib's
  `WeierstrassCurve.Affine.Point` — already an `AddCommGroup`.  The
  missing input is a scheme-morphism ext lemma: *two morphisms from a
  reduced finite-type `ℚ`-scheme into `proj E` that agree on `ℚ̄`-points
  are equal*.  *Refuting check*: grep mathlib for a morphism ext lemma
  over closed points of a Jacobson base.  This route needs the
  `ℚ̄`-point description of `m`, which is the business of the sibling
  leaf `exists_projGeomFibreAddEquiv` — so the two are naturally worked
  together, and a prompt sending an owner here should say so.
* **Chart-wise associativity.**  Verify the identity directly between the
  bihomogeneous forms on the triple product cover.  This needs no new
  theory at all, only a large `linear_combination` certificate modulo
  `(W(P), W(Q), W(R))` obtainable from `Singular`/`Magma`, and it is
  independent of the density statement.  It is the brute-force route and
  it is probably the cheaper one.

Note that this leaf is stated for an ARBITRARY `m` satisfying the three
chart axioms rather than for the witness produced by `exists_projMul`.
That is deliberate: it keeps the two halves independently dispatchable.
An owner who finds the abstract form intractable may legitimately propose
folding this back into `exists_projMul`, where the charts are in scope —
that is a cut-level change and should be reported, not made silently.

## ROUTE AUDIT (2026-07-27, second correction): the CHART-WISE route does NOT
## apply to this leaf, and the audit above is wrong about that

The audit above offers "chart-wise associativity … a large
`linear_combination` certificate modulo `(W(P), W(Q), W(R))`" as the
cheap brute-force alternative, and calls it "probably the cheaper one".
**It is not available here at all.**  `m` is universally quantified: it
is an arbitrary morphism satisfying `hcomm`/`hunit`/`hinv`, and it comes
with NO charts and NO polynomial forms.  There is nothing for a CAS to
certify, because there are no polynomials in the hypotheses.  The
chart-wise route is a route for `exists_projMul`'s specific witness, and
it becomes available for this statement only under the cut-level change
that folds the two halves back together.  *Refuting check*: read the
binders of the statement below and look for any occurrence of `addX` /
`addY` / `addZ`, or of any hypothesis that constrains `m` on a chart —
there is none.

So **exactly one route survives for the leaf as stated: density**, and
this docstring's job is now to say how far it has been taken.

## WHAT IS DONE HERE, AND WHAT IS LEFT (2026-07-27)

The density route is no longer a plan; the assembly below is WRITTEN and
compiles, and `projMul_assoc` is PROVEN from two named sub-leaves.  The
ext lemma the previous audit listed as "the missing input" — *two
morphisms from a reduced finite-type `ℚ`-scheme into `proj E` that agree
on `ℚ̄`-points are equal* — **is already in mathlib**, as
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq`
(`Mathlib/AlgebraicGeometry/Morphisms/Separated.lean`):

    lemma ext_of_fromSpecResidueField_eq (f g : X ⟶ Y) (i : Y ⟶ Z)
      [IsSeparated i] [IsReduced X] (S : Set X) (hS' : Dense S)
      (H : ∀ x ∈ S, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g)
      (H' : f ≫ i = g ≫ i) : f = g

That is a strictly better instrument than the one the audit asked for:
it wants agreement at RESIDUE FIELDS of a dense set of points, which
subsumes closed points and needs no Jacobson-base argument, and `S` may
be taken to be `Set.univ`.  Its three side conditions all discharge here:

* `IsSeparated (projToSpec E)` — free, since `IsProper` *extends*
  `IsSeparated` and `isProper_projToSpec` is PROVEN above;
* `H'` — free, by `hom_ext_spec_rat`, the target being `Spec ℚ`;
* `IsReduced` of the threefold product — `isReduced_triProd_proj` below.

What is left is therefore exactly ONE thing (2026-07-27, updated the same
day): `exists_projPtAddEquiv_algClosed`, the ALGEBRAIC `K`-point
dictionary.  `projMul_assoc_pt` and `projMul_assoc_pt_algClosed` — the
"genuine Milne content", stated as plain associativity of the operation
`m` induces on `K`-points — are now both PROVEN from it, the second by
`commLoop_eq_add_of_addHom` and the first by descent.  The other item
this list used to name, `geometricallyReduced_projToSpec`, is PROVEN — it
was a general `Smooth → GeometricallyReduced` gap in mathlib, and it has
been filled in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`. -/
theorem projMul_assoc (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hcomm : Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
      (Limits.pullback.fst (projToSpec E) (projToSpec E))
      Limits.pullback.condition.symm ≫ m = m)
    (hunit : Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E))
    (hinv : Limits.pullback.lift (projNeg E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E) :
    AbelianSchemeStruct.triAddLeft (projToSpec E) m (hom_ext_spec_rat _ _) =
      AbelianSchemeStruct.triAddRight (projToSpec E) m (hom_ext_spec_rat _ _) := by
  haveI := isProper_projToSpec E
  haveI := isReduced_triProd_proj E
  exact ext_of_fromSpecResidueField_eq _ _ (projToSpec E) Set.univ dense_univ
    (fun x _ => projMul_assoc_residueField E m hcomm hunit hinv x) (hom_ext_spec_rat _ _)

/-- **The chord–tangent addition on the projective Weierstrass model**
(PROVEN from `exists_projMul` and `projMul_assoc`) — what is left of
items 5+6 once the inversion `i`, the unit section `e` and the three
structure-morphism compatibilities have been discharged; see
`nonempty_projGroupLaw` for the assembly.

The cut is between the two halves that need completely different
machinery, and it is why they are separate leaves: `exists_projMul` is
scheme-theoretic gluing (an open cover of `A ×_ℚ A`, the two
Bosma–Lenstra addition laws, and a missing congruence lemma for
`Proj.fromOfGlobalSections`), while `projMul_assoc` is the one axiom that
is not a chart identity and needs either a density statement about
`ℚ̄`-points or a large polynomial certificate.  Nothing is lost or
weakened by the split: the conjunction of the two is exactly this
statement. -/
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
              (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E := by
  obtain ⟨m, -, hcomm, hunit, hinv⟩ := exists_projMul E
  exact ⟨m, projMul_assoc E m hcomm hunit hinv, hcomm, hunit, hinv⟩

/-- **The chord–tangent law on the projective Weierstrass model, as
morphisms of schemes** (REDUCED to `exists_projAdd`, not closed) — items 5+6
of the routable specification in `exists_ellipticScheme_of_weierstrass`'s
docstring.

**This declaration carries no `sorry` of its own but is transitively
sorried**, because `exists_projAdd` is proven from `projMul_assoc` (itself
now reduced to `exists_projPtAddEquiv_algClosed` alone,
`geometricallyReduced_projToSpec` and both `projMul_assoc_pt*` leaves
having been closed) and from the still-open `exists_projMul`.  It is a reduction, not a result; the
remaining work is on those leaves.

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

section GeometricConnectedness

open _root_.MvPolynomial

/-! ### The ideal `(X, Z)` of `K[X, Y, Z]`, and the point at infinity

Everything in this block is what `geometricallyConnected_projToSpec` consumes for its
`hne` step, and it is fully proven.  The point at infinity `[0 : 1 : 0]` is the
homogeneous prime `(X̄, Z̄)` of the coordinate ring, and the one thing that has to be
established about it is that `(X, Z)` is prime in `K[X, Y, Z]` — for which mathlib has no
lemma, since it has nothing about the span of a *subset* of the variables (only
`MvPolynomial.X_prime`, for a single variable, and `MvPolynomial.mem_ideal_span_X_image`,
a support criterion that says nothing about primality).

The route taken here avoids computing anything: `(X, Z)` is exhibited as the KERNEL of the
retraction `killXZ` that sets `X` and `Z` to zero, and the kernel of a ring hom into a
domain is prime for free (`RingHom.ker_isPrime`).  The only real work is the kernel
computation `span_X_Z_eq_ker_killXZ`, and mathlib's `modMonomial` division API does it:
subtracting off the multiples of `X` and then of `Z` leaves a remainder supported on pure
`Y`-monomials, on which `killXZ` is the identity. -/

variable {K : Type u} [CommRing K]

/-- **Setting `X` and `Z` to zero**: the retraction of `K[X, Y, Z]` onto `K[Y]`, realised
inside `K[X, Y, Z]` itself so that the codomain is visibly a domain. -/
noncomputable def killXZ (K : Type u) [CommRing K] :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![0, X 1, 0]

@[simp] theorem killXZ_X0 : killXZ K (X 0) = 0 := by simp [killXZ]
@[simp] theorem killXZ_X1 : killXZ K (X 1) = X 1 := by simp [killXZ]
@[simp] theorem killXZ_X2 : killXZ K (X 2) = 0 := by simp [killXZ]

/-- On a monomial involving neither `X` nor `Z`, `killXZ` is the identity. -/
theorem killXZ_monomial_of {m : Fin 3 →₀ ℕ} (h0 : m 0 = 0) (h2 : m 2 = 0) (c : K) :
    killXZ K (monomial m c) = monomial m c := by
  have hm : m = Finsupp.single 1 (m 1) := by
    ext i; fin_cases i <;> simp [h0, h2]
  rw [hm, killXZ, aeval_monomial, Finsupp.prod_single_index (by simp)]
  simp [algebraMap_eq, C_mul_X_pow_eq_monomial]

/-- **The ideal `(X, Z)` is exactly the kernel of `killXZ`.**

The inclusion `⊆` is immediate.  For `⊇`, divide `p` by `X` and then the remainder by `Z`
(`MvPolynomial.modMonomial_add_divMonomial_single`): what is left is supported on
monomials with no `X` and no `Z`, hence is fixed by `killXZ`, hence is `0` when `p` is. -/
theorem span_X_Z_eq_ker_killXZ :
    (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K))
      = RingHom.ker (killXZ K) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f (rfl | rfl) <;> simp [SetLike.mem_coe, RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have hcoeff : ∀ m : Fin 3 →₀ ℕ, m 0 ≠ 0 ∨ m 2 ≠ 0 → coeff m
        ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
          (Finsupp.single (2 : Fin 3) 1)) = 0 := by
      intro m hm
      rcases hm with h | h
      · by_cases h2 : Finsupp.single (2 : Fin 3) 1 ≤ m
        · exact coeff_modMonomial_of_le _ h2
        · rw [coeff_modMonomial_of_not_le _ h2]
          exact coeff_modMonomial_of_le _
            (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr h)
      · exact coeff_modMonomial_of_le _
          (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr h)
    have hys : killXZ K ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
        (Finsupp.single (2 : Fin 3) 1))
        = (p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
          (Finsupp.single (2 : Fin 3) 1) := by
      set s : MvPolynomial (Fin 3) K :=
        (p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial (Finsupp.single (2 : Fin 3) 1)
      calc killXZ K s = killXZ K (∑ m ∈ s.support, monomial m (coeff m s)) := by
            rw [← MvPolynomial.as_sum]
        _ = ∑ m ∈ s.support, killXZ K (monomial m (coeff m s)) := by rw [map_sum]
        _ = ∑ m ∈ s.support, monomial m (coeff m s) := by
            refine Finset.sum_congr rfl fun m hm => ?_
            refine killXZ_monomial_of ?_ ?_ _
            · by_contra h; exact (mem_support_iff.mp hm) (hcoeff m (Or.inl h))
            · by_contra h; exact (mem_support_iff.mp hm) (hcoeff m (Or.inr h))
        _ = s := (MvPolynomial.as_sum s).symm
    have h1 := modMonomial_add_divMonomial_single p (0 : Fin 3)
    have h2 := modMonomial_add_divMonomial_single
      (p.modMonomial (Finsupp.single (0 : Fin 3) 1)) (2 : Fin 3)
    have hp0 : (p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
        (Finsupp.single (2 : Fin 3) 1) = 0 := by
      have hpp : killXZ K p = killXZ K ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
          (Finsupp.single (2 : Fin 3) 1)) := by
        conv_lhs => rw [← h1, ← h2]
        simp
      rw [hys, hp] at hpp
      exact hpp.symm
    have hpeq : p = X 2 * ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).divMonomial
          (Finsupp.single (2 : Fin 3) 1)) + X 0 * (p.divMonomial (Finsupp.single (0 : Fin 3) 1)) := by
      conv_lhs => rw [← h1, ← h2]
      rw [hp0, zero_add]
    rw [hpeq]
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- `(X, Z)` is a prime ideal of `K[X, Y, Z]` — the kernel of a map to a domain. -/
theorem isPrime_span_X_Z [IsDomain K] :
    (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)).IsPrime := by
  rw [span_X_Z_eq_ker_killXZ]; exact RingHom.ker_isPrime _

/-- `Y ∉ (X, Z)`: this is what makes the point at infinity a point of `Proj` rather than a
point of the irrelevant locus. -/
theorem X1_notMem_span_X_Z [Nontrivial K] :
    (X 1 : MvPolynomial (Fin 3) K) ∉ (Ideal.span {X (0 : Fin 3), X 2}) := by
  rw [span_X_Z_eq_ker_killXZ, RingHom.mem_ker, killXZ_X1]
  exact X_ne_zero 1

/-- **The projective Weierstrass cubic lies in `(X, Z)`**: every one of its seven terms is
divisible by `X` or by `Z`.  This is exactly the statement that `[0 : 1 : 0]` is on the
curve, and it is what lets `(X̄, Z̄)` be formed in the quotient. -/
theorem projPolynomial_mem_span_X_Z (W : WeierstrassCurve K) :
    polynomial W ∈ (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)) := by
  have h : polynomial W
      = X 0 * (C W.a₁ * X 1 * X 2 - X 0 ^ 2 - C W.a₂ * X 0 * X 2 - C W.a₄ * X 2 ^ 2)
        + X 2 * (X 1 ^ 2 + C W.a₃ * X 1 * X 2 - C W.a₆ * X 2 ^ 2) := by
    rw [WeierstrassCurve.Projective.polynomial]; ring
  rw [h]
  exact Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

section PointAtInfinity

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- The homogeneous ideal `(X̄, Z̄)` of the homogeneous coordinate ring `K[X, Y, Z] ⧸ (W)`. -/
noncomputable def infIdeal :
    Ideal (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal W).toIdeal) :=
  Ideal.map (Ideal.Quotient.mk _) (Ideal.span {X (0 : Fin 3), X 2})

theorem ker_le_span_X_Z :
    RingHom.ker (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal)
      ≤ (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)) := by
  rw [Ideal.mk_ker]
  exact Ideal.span_le.mpr (by simpa using projPolynomial_mem_span_X_Z W)

theorem infIdeal_eq_span :
    infIdeal W = Ideal.span {Ideal.Quotient.mk _ (X (0 : Fin 3)),
      Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal (X 2)} := by
  rw [infIdeal, Ideal.map_span, Set.image_pair]

theorem isPrime_infIdeal : (infIdeal W).IsPrime := by
  haveI : (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    isPrime_span_X_Z
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (ker_le_span_X_Z W)

theorem isHomogeneous_infIdeal : (infIdeal W).IsHomogeneous (projGrading W) := by
  rw [infIdeal_eq_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro x (rfl | rfl)
  · exact ⟨1, HomogeneousIdeal.mk_mem_quotientGrading
      (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _))⟩
  · exact ⟨1, HomogeneousIdeal.mk_mem_quotientGrading
      (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _))⟩

/-- `Ȳ` is not in `(X̄, Z̄)`, so `(X̄, Z̄)` does not contain the irrelevant ideal. -/
theorem mk_X1_notMem_infIdeal :
    Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal (X 1) ∉ infIdeal W := by
  intro h
  have hc : (X 1 : MvPolynomial (Fin 3) K) ∈ Ideal.comap
      (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal) (infIdeal W) := h
  rw [infIdeal, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr (ker_le_span_X_Z W)] at hc
  exact X1_notMem_span_X_Z hc

/-- **The point at infinity `[0 : 1 : 0]`**, as a point of the projective spectrum of the
homogeneous coordinate ring: the homogeneous prime `(X̄, Z̄)`, which is prime because
`K[X, Y, Z] ⧸ (W, X, Z) = K[X, Y, Z] ⧸ (X, Z) ≅ K[Y]`, using that `W ∈ (X, Z)`. -/
noncomputable def pointAtInfinity : ProjectiveSpectrum (projGrading W) where
  asHomogeneousIdeal := ⟨infIdeal W, isHomogeneous_infIdeal W⟩
  isPrime := isPrime_infIdeal W
  not_irrelevant_le := by
    intro h
    refine mk_X1_notMem_infIdeal W (h ?_)
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
      (HomogeneousIdeal.mk_mem_quotientGrading
        (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _)))

/-- **The projective Weierstrass model is nonempty** (PROVEN) — this is the `hne` step of
`geometricallyConnected_projToSpec`, over an arbitrary base field. -/
theorem nonempty_proj : Nonempty (proj W) := ⟨pointAtInfinity W⟩

end PointAtInfinity

/-! ### `Proj` of a graded domain is irreducible -/

section GradedDomain

variable {A : Type*} {σ' : Type*} [CommRing A] [SetLike σ' A] [AddSubmonoidClass σ' A]

/-- **`Proj` of a graded domain is an irreducible space**, provided it is nonempty.

This is the projective analogue of `PrimeSpectrum.irreducibleSpace`, and it is absent from
mathlib at this pin — `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` contains no
irreducibility or connectedness statement at all.

The proof is the same one line of ideas as the affine case: in a domain the zero ideal is
prime, and it is homogeneous, so it is a POINT of `ProjectiveSpectrum 𝒜` as soon as the
space is nonempty (nonemptiness is what rules out the irrelevant ideal being `⊥`).  It is
then a generic point, because `vanishingIdeal {0} = 0` and `zeroLocus 0` is everything.  A
space with a dense point is irreducible, and an irreducible space is preconnected. -/
theorem irreducibleSpace_projectiveSpectrum (𝒜 : ℕ → σ') [GradedRing 𝒜] [IsDomain A]
    (x₀ : ProjectiveSpectrum 𝒜) : IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
  have hbot : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ (⊥ : HomogeneousIdeal 𝒜) := fun h =>
    x₀.not_irrelevant_le (h.trans bot_le)
  have hprime : (⊥ : HomogeneousIdeal 𝒜).toIdeal.IsPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot
  let z : ProjectiveSpectrum 𝒜 := ⟨⊥, hprime, hbot⟩
  have hdense : closure ({z} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    simp only [z]
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense]
  exact isIrreducible_singleton.closure

end GradedDomain

/-! ### The two remaining leaves of `geometricallyConnected_projToSpec` -/

section Leaves

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- **A monic cubic over a domain with no root in the ring is irreducible.**

`Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` already holds over an
arbitrary `[CommRing R] [IsDomain R]` — it is NOT a field-only statement — so no Gauss
lemma, no fraction field and no integral-closedness argument is needed here.  This wrapper
just packages it with the degree computation. -/
theorem irreducible_monicCubic_of_no_root {A : Type*} [CommRing A] [IsDomain A]
    (c₂ c₁ c₀ : A) (h : ∀ r : A, r ^ 3 + c₂ * r ^ 2 + c₁ * r + c₀ ≠ 0) :
    Irreducible (Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2
      + Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀) := by
  set p : Polynomial A := Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2
      + Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀ with hp
  have hmonic : p.Monic := by rw [hp]; monicity!
  have hdeg : p.natDegree = 3 := by rw [hp]; compute_degree!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot.def] at hr
  exact h r (by simpa [hp] using hr)

/-- **`Z` is prime in `K[Y, Z]`.**  Mathlib has `Polynomial.prime_X` but no `MvPolynomial`
analogue; transporting along `finSuccEquiv` supplies it for the variable of index `0`, and
`renameEquiv` along `Equiv.swap 0 1` moves it to the variable of index `1`. -/
theorem prime_X_one_fin_two : Prime (X (1 : Fin 2) : MvPolynomial (Fin 2) K) := by
  have hswap : (X (1 : Fin 2) : MvPolynomial (Fin 2) K)
      = MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1) (X 0) := by
    simp
  rw [hswap, MulEquiv.prime_iff]
  refine (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 1)).mp ?_
  rw [MvPolynomial.finSuccEquiv_X_zero]
  exact Polynomial.prime_X

/-- **`Z ∤ Y` in `K[Y, Z]`** — seen by evaluating at `(Y, Z) = (1, 0)`. -/
theorem X_one_not_dvd_X_zero_fin_two :
    ¬ ((X (1 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 0) := by
  rintro ⟨c, hc⟩
  have h := congrArg (MvPolynomial.aeval (S₁ := K) ![(1 : K), 0]) hc
  simp at h

/-- **The projective Weierstrass cubic, read as a cubic in `X` over `K[Y, Z]`.**

`MvPolynomial.finSuccEquiv` splits off the variable of index `0`, which for
`WeierstrassCurve.Projective.polynomial` is exactly `X`; the cubic is then MONIC up to the
global sign, with leading coefficient `-1`.  That is the whole point of choosing this
splitting: no Gauss lemma and no primitivity argument is needed for a monic polynomial. -/
theorem finSuccEquiv_projPolynomial :
    MvPolynomial.finSuccEquiv K 2 (polynomial W)
      = -(Polynomial.X ^ 3
          + Polynomial.C (C W.a₂ * X 1) * Polynomial.X ^ 2
          + Polynomial.C (C W.a₄ * X 1 ^ 2 - C W.a₁ * X 0 * X 1) * Polynomial.X
          + Polynomial.C (C W.a₆ * X 1 ^ 3 - X 0 ^ 2 * X 1
              - C W.a₃ * X 0 * X 1 ^ 2)) := by
  have e0 : (MvPolynomial.finSuccEquiv K 2) (X 0 : MvPolynomial (Fin 3) K) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have e1 : (MvPolynomial.finSuccEquiv K 2) (X 1 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 0) := by
    rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl]
    exact MvPolynomial.finSuccEquiv_X_succ
  have e2 : (MvPolynomial.finSuccEquiv K 2) (X 2 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 1) := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl]
    exact MvPolynomial.finSuccEquiv_X_succ
  have eC : ∀ a : K, (MvPolynomial.finSuccEquiv K 2) (C a) = Polynomial.C (C a) := by
    intro a; simp [MvPolynomial.finSuccEquiv_apply]
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow, e0, e1, e2, eC]
  ring

/-- **The projective Weierstrass cubic is prime in `K[X, Y, Z]`** (PROVEN).

This is all that was left of the `hpre` step: given it, the homogeneous coordinate ring is a
domain and `irreducibleSpace_projectiveSpectrum` finishes the job.  It carries NO
ellipticity hypothesis, and should not: the Weierstrass cubic is irreducible over EVERY
field, singular ones included.

## The route actually taken, and why it is short

An earlier docstring here recorded this leaf as needing two pieces of missing mathlib —
homogenisation of a bivariate polynomial into a trivariate one, and the fact that a factor
of a homogeneous element of a graded domain is homogeneous — and proposed to descend from
mathlib's AFFINE `WeierstrassCurve.Affine.irreducible_polynomial` by dehomogenising at
`Z = 1`.  **Neither piece is needed, and neither is the affine statement.**  The graded
machinery only ever enters if one insists on factoring a HOMOGENEOUS polynomial as such;
reading `W` as an ordinary cubic in ONE distinguished variable avoids all of it:

1. `MvPolynomial.finSuccEquiv K 2` presents `K[X, Y, Z]` as `(K[Y, Z])[X]`, and under it
   `W` becomes `-q` with `q` MONIC of degree `3` (`finSuccEquiv_projPolynomial`).  The
   index-`0` variable of `WeierstrassCurve.Projective.polynomial` is `X`, and `W` contains
   `-X ^ 3`, so this splitting — and only this one — makes the leading coefficient a unit.
2. Monic + degree `3` reduces irreducibility to the absence of a ROOT in `K[Y, Z]`, by
   `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`, which holds over any
   `[IsDomain A]` and not merely over a field.  So there is no Gauss lemma, no fraction
   field, and no integral-closedness step anywhere in this proof.
3. There is no root: if `q(r) = 0` then reducing mod `Z` gives `r ³ ≡ 0`, so `Z ∣ r` since
   `Z` is prime (`prime_X_one_fin_two`); writing `r = Z s` and cancelling one `Z` leaves
   `Y ² = Z · (…)`, so `Z ∣ Y ²`, so `Z ∣ Y` — and `Z ∤ Y`
   (`X_one_not_dvd_X_zero_fin_two`).
4. `MvPolynomial (Fin 3) K` is a UFD, so irreducible gives prime. -/
theorem prime_projPolynomial : Prime (polynomial W) := by
  refine (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2)).mp ?_
  rw [finSuccEquiv_projPolynomial W]
  refine Prime.neg ?_
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  refine irreducible_monicCubic_of_no_root _ _ _ ?_
  intro r hr
  have hz : Prime (X (1 : Fin 2) : MvPolynomial (Fin 2) K) := prime_X_one_fin_two
  have h1 : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) ∣ r ^ 3 := by
    refine ⟨-(C W.a₂ * r ^ 2 + (C W.a₄ * X 1 - C W.a₁ * X 0) * r
      + (C W.a₆ * X 1 ^ 2 - X 0 ^ 2 - C W.a₃ * X 0 * X 1)), ?_⟩
    linear_combination hr
  obtain ⟨s, rfl⟩ := hz.dvd_of_dvd_pow h1
  have hA : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) *
      (X 1 ^ 2 * s ^ 3 + C W.a₂ * X 1 ^ 2 * s ^ 2 + C W.a₄ * X 1 ^ 2 * s
        - C W.a₁ * X 0 * X 1 * s + C W.a₆ * X 1 ^ 2 - X 0 ^ 2 - C W.a₃ * X 0 * X 1)
      = X 1 * 0 := by
    linear_combination hr
  have hA0 := mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := K) (1 : Fin 2)) hA
  have h2 : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 0 ^ 2 :=
    ⟨X 1 * s ^ 3 + C W.a₂ * X 1 * s ^ 2 + C W.a₄ * X 1 * s - C W.a₁ * X 0 * s
      + C W.a₆ * X 1 - C W.a₃ * X 0, by linear_combination -hA0⟩
  exact X_one_not_dvd_X_zero_fin_two (hz.dvd_of_dvd_pow h2)

/-- The homogeneous coordinate ring of the projective model is a domain (PROVEN) — the
content of `hpre`, modulo the general `Proj`-of-a-graded-domain statement. -/
theorem isDomain_projCoordinateRing :
    IsDomain (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal W).toIdeal) := by
  haveI : ((polynomialHomogeneousIdeal W).toIdeal).IsPrime := by
    show (Ideal.span {polynomial W}).IsPrime
    rw [Ideal.span_singleton_prime (prime_projPolynomial W).ne_zero]
    exact prime_projPolynomial W
  exact Ideal.Quotient.isDomain _

/-- **The projective Weierstrass model is preconnected** (PROVEN) — the `hpre` step of
`geometricallyConnected_projToSpec`, over an arbitrary base field, with no remaining
leaf.  `prime_projPolynomial`, which was the last one, is proven above. -/
theorem preconnectedSpace_proj : PreconnectedSpace (proj W) := by
  haveI := isDomain_projCoordinateRing W
  haveI := irreducibleSpace_projectiveSpectrum (projGrading W) (pointAtInfinity W)
  show PreconnectedSpace (ProjectiveSpectrum (projGrading W))
  infer_instance

end Leaves

/-! ### `hbc`: base change for `Proj`

**Everything in this block is PROVEN.**  The block replaces what used to be a single opaque
leaf `nonempty_projPullbackIso` by: the graded base-change hom, the irrelevant-ideal
hypothesis `Proj.map` demands, the assembled comparison morphism, and — in part 2 below —
the proof that that morphism is an isomorphism.

**There is no base change for `Proj` at this pin, in any form.**  A search over
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` for `Proj` together with `pullback`,
`baseChange`, `IsPullback` or `TensorProduct` returns nothing; so does the same search over
`~/cs/FLT`.  The only functoriality that exists is contravariant in the graded ring,
`AlgebraicGeometry.Proj.map` (`ProjectiveSpectrum/Functor.lean:144`).  One correction to the
earlier route note here: `Proj.pullbackAwayιIso` (`ProjectiveSpectrum/Basic.lean:256`) is
NOT the glue for this — it compares two charts of ONE `Proj`, not two `Proj`s over
different bases, and nothing in that file crosses a base change. -/

section BaseChange

variable (E : WeierstrassCurve ℚ) (K : Type) [Field K] [Algebra ℚ K]

/-- Base change of the projective Weierstrass polynomial, `W_K = map (algebraMap ℚ K) W`. -/
theorem polynomial_baseChange :
    polynomial (E.baseChange K) = MvPolynomial.map (algebraMap ℚ K) (polynomial E) :=
  WeierstrassCurve.Projective.map_polynomial (W' := E) (f := algebraMap ℚ K)

/-- Base change carries the ideal `(W)` into `(W_K)`, so it descends to the quotients. -/
theorem map_mem_polynomialHomogeneousIdeal_baseChange
    {a : MvPolynomial (Fin 3) ℚ} (ha : a ∈ (polynomialHomogeneousIdeal E).toIdeal) :
    MvPolynomial.map (algebraMap ℚ K) a
      ∈ (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal := by
  have h : (polynomialHomogeneousIdeal E).toIdeal = Ideal.span {polynomial E} := rfl
  have h' : (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal
      = Ideal.span {polynomial (E.baseChange K)} := rfl
  rw [h, Ideal.mem_span_singleton] at ha
  rw [h', Ideal.mem_span_singleton]
  obtain ⟨c, rfl⟩ := ha
  exact ⟨MvPolynomial.map (algebraMap ℚ K) c, by
    rw [map_mul, polynomial_baseChange, mul_comm]⟩

/-- **Base change on the homogeneous coordinate rings**, `ℚ[X, Y, Z] ⧸ (W) → K[X, Y, Z] ⧸ (W_K)`. -/
noncomputable def projBaseChangeQuot :
    (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) →+*
      (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap ℚ K)))
    fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2
      (map_mem_polynomialHomogeneousIdeal_baseChange E K ha)

@[simp] theorem projBaseChangeQuot_mk (p : MvPolynomial (Fin 3) ℚ) :
    projBaseChangeQuot E K (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℚ K) p) := rfl

/-- **Base change as a GRADED ring hom** of homogeneous coordinate rings — the input
`Proj.map` consumes.  Degrees are preserved because `MvPolynomial.map` preserves
homogeneity (`MvPolynomial.IsHomogeneous.map`). -/
noncomputable def projBaseChangeGradedHom :
    projGrading E →+*ᵍ projGrading (E.baseChange K) where
  __ := projBaseChangeQuot E K
  map_mem := by
    intro i x hx
    obtain ⟨a, ha, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp hx
    exact HomogeneousIdeal.mem_quotientGrading.mpr
      ⟨MvPolynomial.map (algebraMap ℚ K) a,
        mem_homogeneousSubmodule _ _ |>.mpr
          ((mem_homogeneousSubmodule _ _ |>.mp ha).map _), rfl⟩

@[simp] theorem projBaseChangeGradedHom_apply
    (a : MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) :
    projBaseChangeGradedHom E K a = projBaseChangeQuot E K a := rfl

/-- **The hypothesis `Proj.map` demands**: the irrelevant ideal downstairs is contained in
the ideal generated by the image of the irrelevant ideal upstairs.

A positive-degree homogeneous polynomial over `K` has every monomial of positive total
degree, hence lies in the ideal of the variables (`MvPolynomial.mem_pow_idealOfVars_iff'`
at exponent `1`), and each variable is the image of the corresponding variable over `ℚ`. -/
theorem irrelevant_le_map_projBaseChangeGradedHom :
    HomogeneousIdeal.irrelevant (projGrading (E.baseChange K)) ≤
      (HomogeneousIdeal.irrelevant (projGrading E)).map (projBaseChangeGradedHom E K) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp ha
  have hp' : p.IsHomogeneous i := mem_homogeneousSubmodule _ _ |>.mp hp
  have hspan : p ∈ MvPolynomial.idealOfVars (Fin 3) K := by
    rw [show MvPolynomial.idealOfVars (Fin 3) K = MvPolynomial.idealOfVars (Fin 3) K ^ 1 from
      (pow_one _).symm, MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    exact hp'.coeff_eq_zero (by omega)
  have hle : MvPolynomial.idealOfVars (Fin 3) K ≤
      Ideal.comap (Ideal.Quotient.mk (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal)
        ((HomogeneousIdeal.irrelevant (projGrading E)).map
          (projBaseChangeGradedHom E K)).toIdeal := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hXmem : (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (X j))
        ∈ HomogeneousIdeal.irrelevant (projGrading E) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
        (HomogeneousIdeal.mk_mem_quotientGrading
          (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _)))
    have h2 := Ideal.mem_map_of_mem (projBaseChangeGradedHom E K) hXmem
    simpa using h2
  exact hle hspan

/-- **The base-change morphism of projective models** `proj (E_K) ⟶ proj E`, namely `Proj`
applied to the graded base-change hom. -/
noncomputable def projBaseChangeMap : proj (E.baseChange K) ⟶ proj E :=
  Proj.map (projBaseChangeGradedHom E K) (irrelevant_le_map_projBaseChangeGradedHom E K)

/-- **The canonical comparison morphism** from the projective model of the base-changed
curve to the base change of the projective model.

The commuting square this needs is FREE over this base: both composites are morphisms into
`Spec ℚ`, and `hom_ext_spec_rat` says any two such are equal.  Over a general base it would
be a real obligation. -/
noncomputable def projBaseChangeHom :
    proj (E.baseChange K) ⟶ Limits.pullback (projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) :=
  Limits.pullback.lift (projBaseChangeMap E K) (projToSpec (E.baseChange K))
    (hom_ext_spec_rat _ _)

/-! #### `hbc`, part 2: the comparison morphism is an isomorphism

Everything from here to `isIso_projBaseChangeHom` is the proof that `projBaseChangeHom` is an
isomorphism, and it is fully PROVEN.  The argument has two halves, and each is a piece of
mathlib infrastructure that did not exist at this pin:

* **Geometric half.**  `Proj.map` is *cartesian on the standard charts*
  (`isPullback_awayι_map`): `Proj.map_preimage_basicOpen` says `D₊(φ s)` is exactly the
  preimage of `D₊(s)` ON THE NOSE, and `Proj.awayι_comp_map` gives the commuting square, so
  `IsOpenImmersion.isPullback` applies verbatim.  Feeding those charts to
  `Scheme.isPullback_of_openCover` reduces the whole base-change square to one AFFINE square
  per chart, and `Proj.awayι_toSpecZero` turns each chart's structure morphism into a
  `Spec.map` — so the affine square is `Spec` of a ring square, and
  `isPullback_SpecMap_of_isPushout` closes it from a pushout of rings.
* **Ring half.**  The residual ring statement is `Away 𝒜 s ⊗_ℚ K ≅ Away ℬ (φ s)`.  It is
  proven by DEHOMOGENISING: for `s` of degree ONE there is a canonical isomorphism
  `(A_s)₀ ≅ A ⧸ (s - 1)` (`awayDehomEquiv`), natural in the graded ring
  (`awayToDehom_comp_awayMap`), and on the right-hand side base change is elementary —
  a quotient of a polynomial ring, handled by `isPushout_quotientMk` (quotients commute with
  base change) pasted onto mathlib's `Algebra.IsPushout R S (MvPolynomial σ R)
  (MvPolynomial σ S)`.  No graded base-change theory is needed anywhere.

The degree-one hypothesis is not a restriction here: the cover used is `D₊(x₀), D₊(x₁),
D₊(x₂)`, and the coordinates are homogeneous of degree one. -/

/-- Transport of `IsPullback` along an isomorphism of the apex. -/
theorem isPullback_of_isoApex {C : Type*} [Category C] {P P' X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Limits.HasPullback f g] (e : P' ≅ P) :
    IsPullback (e.hom ≫ fst) (e.hom ≫ snd) f g :=
  IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, h.w]⟩ (e ≪≫ h.isoPullback)
    (by simp) (by simp)

/-- The structure map `R → (A_t)₀` of a standard chart of `proj W`. -/
noncomputable def awayBaseHom {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (t : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :
    R →+* HomogeneousLocalization.Away (projGrading W) t :=
  (HomogeneousLocalization.fromZeroRingHom (projGrading W) (Submonoid.powers t)).comp
    (algebraMap R (projGrading W 0))

/-- **The chart composite `Spec (A_t)₀ ⟶ proj W ⟶ Spec R` is `Spec.map` of `awayBaseHom`**,
over an arbitrary base ring and for an arbitrary homogeneous `t` of positive degree.  This is
the base-free version of `awayι_projToSpec_eq_specMap`, needed because the base-change square
has `proj E` over `ℚ` on one side and `proj (E_K)` over `K` on the other. -/
theorem awayι_projToSpec_eq_specMap' {R : Type} [CommRing R] (W : WeierstrassCurve R) {m : ℕ}
    (t : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal)
    (ht : t ∈ projGrading W m) (hm : 0 < m) :
    Proj.awayι (projGrading W) t ht hm ≫ projToSpec W
      = Spec.map (CommRingCat.ofHom (awayBaseHom W t)) := by
  show Proj.awayι (projGrading W) t ht hm ≫
      (Proj.toSpecZero (projGrading W) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (projGrading W 0)))) = _
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- **The standard chart square of `Proj.map` is CARTESIAN** — a general statement about
`Proj` that mathlib does not have.

`Proj.map_preimage_basicOpen` gives `map f ⁻¹ᵁ D₊(s) = D₊(f s)` on the nose, so the ranges of
the two chart immersions match, and `Proj.awayι_comp_map` is the commuting square;
`IsOpenImmersion.isPullback` then says a commuting square of open immersions with matching
preimage IS a pullback. -/
theorem isPullback_awayι_map {A B σ τ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
    [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) (hfs : f s ∈ ℬ i) :
    IsPullback (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s)))
      (Proj.awayι ℬ (f s) hfs hi) (Proj.awayι 𝒜 s hs hi) (Proj.map f hf) :=
  IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map f hf hi s hs)
    (by rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen])

/-- The three homogeneous coordinates have degree one. -/
theorem projCoord_mem_grading {R : Type} [CommRing R] (W : WeierstrassCurve R) (i : Fin 3) :
    projCoord W i ∈ projGrading W 1 :=
  HomogeneousIdeal.mk_mem_quotientGrading
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R i))

/-- The three coordinates span the irrelevant ideal, so `D₊(x₀), D₊(x₁), D₊(x₂)` cover
`proj W`.  This is the covering condition of `smoothOfRelativeDimension_projToSpec`, extracted
as a named lemma over an arbitrary base ring. -/
theorem irrelevant_le_span_projCoord {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (projGrading W)).toIdeal
      ≤ Ideal.span (Set.range (projCoord W)) := by
  classical
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
      ≤ Ideal.comap (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal)
        (Ideal.span (Set.range (projCoord W))) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, -, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hle hp'

/-! #### Dehomogenisation at a degree-one element: `(A_s)₀ ≅ A ⧸ (s - 1)`

This is the standard "set `s = 1`" isomorphism for a graded ring `A` and `s ∈ 𝒜 1`, and it is
absent from mathlib in every form.  It is what converts the graded base-change question into an
ungraded one.

Both maps are constructed explicitly and the two round trips are checked on generators, so no
graded induction on the degree is needed anywhere:

* `awayToDehom` is `IsLocalization.lift` of `A ↠ A ⧸ (s - 1)` (which inverts `s`, since `s ↦ 1`),
  restricted to the degree-zero part;
* `dehomToAway` is `DirectSum.toSemiring` applied to `a ↦ a / s^d` on each graded piece — this
  IS a ring hom because `1 / s^0 = 1` and `(ab) / s^{i+j} = (a/s^i)(b/s^j)`. -/

section Dehom

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {s : A} (hs : s ∈ 𝒜 1)

/-- `s` becomes `1` in `A ⧸ (s - 1)`. -/
theorem mk_self_dehom : Ideal.Quotient.mk (Ideal.span {s - 1}) s = 1 := by
  have h : Ideal.Quotient.mk (Ideal.span {s - 1}) (s - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

/-- Every power of `s` is a unit in `A ⧸ (s - 1)` — indeed it is `1`. -/
theorem isUnit_mk_dehom (y : Submonoid.powers s) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {s - 1}) y) := by
  obtain ⟨n, hn⟩ := y.2
  rw [show ((y : A)) = s ^ n from hn.symm, map_pow, mk_self_dehom, one_pow]
  exact isUnit_one

/-- **Dehomogenisation**, `(A_s)₀ → A ⧸ (s - 1)`: the fraction `a / sⁿ` goes to `a`. -/
noncomputable def awayToDehom :
    HomogeneousLocalization.Away 𝒜 s →+* A ⧸ Ideal.span {s - 1} :=
  (IsLocalization.lift (M := Submonoid.powers s) (S := Localization.Away s)
      (g := Ideal.Quotient.mk (Ideal.span {s - 1})) (isUnit_mk_dehom (s := s))).comp
    (algebraMap (HomogeneousLocalization.Away 𝒜 s) (Localization.Away s))

@[simp] theorem awayToDehom_apply (x : HomogeneousLocalization.Away 𝒜 s) {n : ℕ} {a : A}
    (hx : x.val = Localization.mk a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) :
    awayToDehom 𝒜 x = Ideal.Quotient.mk _ a := by
  show IsLocalization.lift (isUnit_mk_dehom (s := s)) x.val = _
  rw [hx, Localization.mk_eq_mk', IsLocalization.lift_mk'_spec]
  rw [map_pow, mk_self_dehom, one_pow, one_mul]

/-- The degree-zero fraction `a / sⁱ` attached to a homogeneous `a` of degree `i`. -/
noncomputable def homFrac (i : ℕ) (a : 𝒜 i) : HomogeneousLocalization.Away 𝒜 s :=
  HomogeneousLocalization.mk
    ⟨i, a, ⟨s ^ i, by simpa using SetLike.pow_mem_graded i hs⟩, ⟨i, rfl⟩⟩

@[simp] theorem val_homFrac (i : ℕ) (a : 𝒜 i) :
    (homFrac 𝒜 hs i a).val = Localization.mk (a : A) (⟨s ^ i, i, rfl⟩ : Submonoid.powers s) :=
  rfl

/-- `a ↦ a / sⁱ` is additive on the degree-`i` part. -/
noncomputable def homFracHom (i : ℕ) : 𝒜 i →+ HomogeneousLocalization.Away 𝒜 s where
  toFun a := homFrac 𝒜 hs i a
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [val_homFrac, HomogeneousLocalization.val_zero]
    simp [Localization.mk_zero]
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, val_homFrac, val_homFrac, val_homFrac,
      Localization.add_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [AddMemClass.coe_add, Submonoid.coe_mul]; ring⟩

theorem homFracHom_apply (i : ℕ) (a : 𝒜 i) : homFracHom 𝒜 hs i a = homFrac 𝒜 hs i a := rfl

/-- **The dehomogenisation section** `A → (A_s)₀`, `a ↦ Σ_d a_d / s^d`.

`DirectSum.toSemiring` builds it as a RING hom out of the degreewise maps, the two side
conditions being `1 / s^0 = 1` and `(a b) / s^{i+j} = (a / s^i) (b / s^j)`. -/
noncomputable def dehomToAway : A →+* HomogeneousLocalization.Away 𝒜 s :=
  (DirectSum.toSemiring (homFracHom 𝒜 hs)
    (by
      apply HomogeneousLocalization.val_injective
      rw [homFracHom_apply, val_homFrac, HomogeneousLocalization.val_one,
        ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp⟩)
    (by
      intro i j ai aj
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_mul, homFracHom_apply, homFracHom_apply, homFracHom_apply,
        val_homFrac, val_homFrac, val_homFrac, Localization.mk_mul]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp only [SetLike.coe_gMul, Submonoid.coe_mul, pow_add]; try ring⟩)).comp
    (DirectSum.decomposeRingEquiv 𝒜).toRingHom

theorem dehomToAway_of_mem {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    dehomToAway 𝒜 hs a = homFrac 𝒜 hs i ⟨a, ha⟩ := by
  unfold dehomToAway
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    show (DirectSum.decomposeRingEquiv 𝒜) a = DirectSum.decompose 𝒜 a from rfl,
    DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toSemiring_of]
  rfl

theorem dehomToAway_self : dehomToAway 𝒜 hs s = 1 := by
  rw [dehomToAway_of_mem 𝒜 hs hs]
  apply HomogeneousLocalization.val_injective
  rw [val_homFrac, HomogeneousLocalization.val_one, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem awayToDehom_dehomToAway (a : A) :
    awayToDehom 𝒜 (dehomToAway 𝒜 hs a) = Ideal.Quotient.mk _ a := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dehomToAway_of_mem 𝒜 hs (DirectSum.decompose 𝒜 a i).2]
  exact awayToDehom_apply 𝒜 _ (val_homFrac 𝒜 hs i _)

/-- The dehomogenisation section kills `s - 1`, so it descends to the quotient. -/
noncomputable def dehomQuotToAway :
    A ⧸ Ideal.span {s - 1} →+* HomogeneousLocalization.Away 𝒜 s :=
  Ideal.Quotient.lift _ (dehomToAway 𝒜 hs) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_sub, dehomToAway_self, map_one, sub_self, mul_zero])

@[simp] theorem dehomQuotToAway_mk (a : A) :
    dehomQuotToAway 𝒜 hs (Ideal.Quotient.mk _ a) = dehomToAway 𝒜 hs a := rfl

/-- **The dehomogenisation isomorphism** `(A_s)₀ ≅ A ⧸ (s - 1)` for `s` homogeneous of degree
one.  Absent from mathlib; it is the whole reason the base-change residue is elementary. -/
noncomputable def awayDehomEquiv :
    HomogeneousLocalization.Away 𝒜 s ≃+* A ⧸ Ideal.span {s - 1} :=
  RingEquiv.ofRingHom (awayToDehom 𝒜) (dehomQuotToAway 𝒜 hs)
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, RingHom.id_apply, dehomQuotToAway_mk]
      exact awayToDehom_dehomToAway 𝒜 hs a))
    (RingHom.ext fun x => by
      obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs x
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [awayToDehom_apply 𝒜 _ (HomogeneousLocalization.Away.val_mk 𝒜 n hs a ha),
        dehomQuotToAway_mk, dehomToAway_of_mem 𝒜 hs ha]
      apply HomogeneousLocalization.val_injective
      rw [val_homFrac, HomogeneousLocalization.Away.val_mk]
      simp)

@[simp] theorem awayDehomEquiv_apply (x : HomogeneousLocalization.Away 𝒜 s) :
    awayDehomEquiv 𝒜 hs x = awayToDehom 𝒜 x := rfl

end Dehom

section DehomMap

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The map on dehomogenisations induced by a graded ring hom. -/
noncomputable def dehomMap (φ : 𝒜 →+*ᵍ ℬ) (s : A) :
    A ⧸ Ideal.span {s - 1} →+* B ⧸ Ideal.span {φ s - 1} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (φ : A →+* B)) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    show Ideal.Quotient.mk _ (φ (c * (s - 1))) = 0
    rw [map_mul, map_sub, map_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
@[simp] theorem dehomMap_mk (φ : 𝒜 →+*ᵍ ℬ) (s a : A) :
    dehomMap φ s (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) := rfl

/-- **Naturality of dehomogenisation** in the graded ring: `(A_s)₀ ≅ A ⧸ (s - 1)` intertwines
`HomogeneousLocalization.Away.map` with `dehomMap`. -/
theorem awayToDehom_comp_awayMap (φ : 𝒜 →+*ᵍ ℬ) {s : A} (hs : s ∈ 𝒜 1) :
    (awayToDehom ℬ).comp (HomogeneousLocalization.Away.map φ s)
      = (dehomMap φ s).comp (awayToDehom 𝒜) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs x
  rw [RingHom.comp_apply, RingHom.comp_apply,
    HomogeneousLocalization.Away.map_mk φ s hs n a ha,
    awayToDehom_apply 𝒜 _ (HomogeneousLocalization.Away.val_mk 𝒜 n hs a ha),
    awayToDehom_apply ℬ _ (HomogeneousLocalization.Away.val_mk ℬ n (φ.map_mem hs) (φ a)
      (φ.map_mem ha)),
    dehomMap_mk]
  rfl

end DehomMap

/-- The chart base map `R → (A_t)₀`, dehomogenised, is the structure map of `A ⧸ (t - 1)`. -/
theorem awayToDehom_comp_awayBaseHom {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (t : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :
    (awayToDehom (projGrading W)).comp (awayBaseHom W t)
      = (Ideal.Quotient.mk (Ideal.span {t - 1})).comp
        (algebraMap R (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal)) :=
  RingHom.ext fun r =>
    awayToDehom_apply (projGrading W) _ (n := 0)
      (a := algebraMap R (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) r)
      (by simp [awayBaseHom, HomogeneousLocalization.fromZeroRingHom])

/-! #### Quotients commute with base change -/

/-- **Pushing out a quotient map along any ring map gives the quotient by the extended ideal**:
`B ⊗_A (A ⧸ I) = B ⧸ I·B`.  Proved directly from the universal property, since a ring map out
of `B ⧸ I·B` is a ring map out of `B` killing `I·B`. -/
theorem isPushout_quotientMk {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (Ideal.Quotient.lift I ((Ideal.Quotient.mk (I.map f)).comp f)
        (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem f ha))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))) := by
  refine IsPushout.of_isColimit' ⟨CommRingCat.hom_ext (RingHom.ext fun _ => rfl)⟩
    (Limits.PushoutCocone.isColimitAux' _ fun c => ?_)
  have hcw : ∀ a : A, c.inl.hom (Ideal.Quotient.mk I a) = c.inr.hom (f a) := fun a =>
    congrArg (fun g : CommRingCat.of A ⟶ c.pt => g.hom a) c.condition
  have hker : I.map f ≤ RingHom.ker c.inr.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker, ← hcw a,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift (I.map f) c.inr.hom fun b hb => hker hb),
    ?_, rfl, ?_⟩
  · exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => (hcw a).symm))
  · intro m _ hr
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_))
    exact congrArg (fun g : CommRingCat.of B ⟶ c.pt => g.hom b) hr

/-- Variant of `isPushout_quotientMk` with the downstairs ideal and the induced map supplied by
the caller — which is what makes it usable against concrete maps such as `projBaseChangeQuot`
and `dehomMap` without any transport along `Ideal.quotEquivOfEq`. -/
theorem isPushout_quotientMk' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) (J : Ideal B) (hJ : J = I.map f) (g : A ⧸ I →+* B ⧸ J)
    (hg : g.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom g) (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  subst hJ
  have hgeq : g = Ideal.Quotient.lift I ((Ideal.Quotient.mk (I.map f)).comp f)
      (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem f ha)) :=
    Ideal.Quotient.ringHom_ext (by rw [hg]; rfl)
  rw [hgeq]
  exact isPushout_quotientMk f I

section MvPoly

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **Base change of the polynomial ring** is a pushout of rings — mathlib's
`Algebra.IsPushout R (MvPolynomial σ R) S (MvPolynomial σ S)`, transported into `CommRingCat`. -/
theorem isPushout_mvPolyBaseChange :
    IsPushout (CommRingCat.ofHom (algebraMap ℚ (MvPolynomial (Fin 3) ℚ)))
      (CommRingCat.ofHom (algebraMap ℚ K))
      (CommRingCat.ofHom (MvPolynomial.map (algebraMap ℚ K)))
      (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K))) :=
  CommRingCat.isPushout_of_isPushout ℚ (MvPolynomial (Fin 3) ℚ) K (MvPolynomial (Fin 3) K)

end MvPoly

theorem ofHom_algebraMap_projQuot {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 3) R)) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal)
      = CommRingCat.ofHom (algebraMap R
          (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal)) := by
  ext r
  rfl

/-- **The homogeneous coordinate ring base-changes**: `K[X, Y, Z] ⧸ (W_K)` is
`(ℚ[X, Y, Z] ⧸ (W)) ⊗_ℚ K`. -/
theorem isPushout_projQuotBaseChange :
    IsPushout
      (CommRingCat.ofHom (algebraMap ℚ
        (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal)))
      (CommRingCat.ofHom (algebraMap ℚ K))
      (CommRingCat.ofHom (projBaseChangeQuot E K))
      (CommRingCat.ofHom (algebraMap K
        (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal))) := by
  have hq := isPushout_quotientMk' (MvPolynomial.map (algebraMap ℚ K))
    (polynomialHomogeneousIdeal E).toIdeal
    (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal
    (by
      show Ideal.span {polynomial (E.baseChange K)}
        = Ideal.map (MvPolynomial.map (algebraMap ℚ K)) (Ideal.span {polynomial E})
      rw [Ideal.map_span, Set.image_singleton, polynomial_baseChange])
    (projBaseChangeQuot E K) rfl
  have h := (isPushout_mvPolyBaseChange K).paste_horiz hq
  rwa [ofHom_algebraMap_projQuot, ofHom_algebraMap_projQuot] at h

/-- **The dehomogenised chart base-changes** — the ring residue of `hbc`, in the form the
dehomogenisation isomorphism delivers it.  Quotients commute with base change, so this is the
coordinate-ring pushout pasted with one more quotient. -/
theorem isPushout_dehomBaseChange
    (s : MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal) :
    IsPushout
      (CommRingCat.ofHom ((Ideal.Quotient.mk (Ideal.span {s - 1})).comp
        (algebraMap ℚ (MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal))))
      (CommRingCat.ofHom (algebraMap ℚ K))
      (CommRingCat.ofHom (dehomMap (projBaseChangeGradedHom E K) s))
      (CommRingCat.ofHom ((Ideal.Quotient.mk
        (Ideal.span {projBaseChangeGradedHom E K s - 1})).comp
        (algebraMap K (MvPolynomial (Fin 3) K ⧸
          (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal)))) := by
  have hq := isPushout_quotientMk' (projBaseChangeQuot E K) (Ideal.span {s - 1})
    (Ideal.span {projBaseChangeGradedHom E K s - 1})
    (by rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]; rfl)
    (dehomMap (projBaseChangeGradedHom E K) s) rfl
  have h := (isPushout_projQuotBaseChange E K).paste_horiz hq
  rwa [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at h

/-- **THE RING RESIDUE OF `hbc`, PROVEN**: `Away 𝒜 s ⊗_ℚ K ≅ Away ℬ (φ s)` for `s` of degree
one, stated as a pushout square of rings.  Transported from `isPushout_dehomBaseChange` along
the dehomogenisation isomorphism, whose naturality is `awayToDehom_comp_awayMap`. -/
theorem isPushout_awayBaseChange
    (s : MvPolynomial (Fin 3) ℚ ⧸ (polynomialHomogeneousIdeal E).toIdeal)
    (hs : s ∈ projGrading E 1) :
    IsPushout (CommRingCat.ofHom (awayBaseHom E s))
      (CommRingCat.ofHom (algebraMap ℚ K))
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map (projBaseChangeGradedHom E K) s))
      (CommRingCat.ofHom
        (awayBaseHom (E.baseChange K) (projBaseChangeGradedHom E K s))) := by
  refine (isPushout_dehomBaseChange E K s).of_iso' (Iso.refl _)
    (awayDehomEquiv (projGrading E) hs).toCommRingCatIso (Iso.refl _)
    (awayDehomEquiv (projGrading (E.baseChange K))
      ((projBaseChangeGradedHom E K).map_mem hs)).toCommRingCatIso ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
    exact (congrArg CommRingCat.ofHom (awayToDehom_comp_awayBaseHom E s)).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  · exact (congrArg CommRingCat.ofHom (awayToDehom_comp_awayMap _ hs)).symm
  · rw [Iso.refl_hom, Category.id_comp]
    exact (congrArg CommRingCat.ofHom
      (awayToDehom_comp_awayBaseHom (E.baseChange K) (projBaseChangeGradedHom E K s))).symm

/-- **The base-change square of projective models is CARTESIAN.**

`Scheme.isPullback_of_openCover` reduces this to the three standard charts `D₊(x₀), D₊(x₁),
D₊(x₂)` of `proj E`.  Over each chart, `isPullback_awayι_map` identifies the pullback of
`projBaseChangeMap` with `Spec` of `HomogeneousLocalization.Away.map`, and
`awayι_projToSpec_eq_specMap'` turns the two structure morphisms into `Spec.map`s — so the
chart obligation is `Spec` of the ring pushout `isPushout_awayBaseChange`. -/
theorem isPullback_projBaseChangeMap :
    IsPullback (projBaseChangeMap E K) (projToSpec (E.baseChange K)) (projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _
    (Proj.affineOpenCoverOfIrrelevantLESpan (projGrading E) (projCoord E) (m := fun _ => 1)
      (projCoord_mem_grading E) (fun _ => Nat.one_pos)
      (irrelevant_le_span_projCoord E)).openCover fun i => ?_
  have hfs : projBaseChangeGradedHom E K (projCoord E i) ∈ projGrading (E.baseChange K) 1 :=
    (projBaseChangeGradedHom E K).map_mem (projCoord_mem_grading E i)
  -- the chart square of `Proj.map` is cartesian
  have C : IsPullback
      (Proj.awayι (projGrading (E.baseChange K))
        (projBaseChangeGradedHom E K (projCoord E i)) hfs Nat.one_pos)
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (projBaseChangeGradedHom E K) (projCoord E i))))
      (projBaseChangeMap E K)
      (Proj.awayι (projGrading E) (projCoord E i) (projCoord_mem_grading E i) Nat.one_pos) :=
    (isPullback_awayι_map (projBaseChangeGradedHom E K)
      (irrelevant_le_map_projBaseChangeGradedHom E K) Nat.one_pos (projCoord E i)
      (projCoord_mem_grading E i) hfs).flip
  -- the chart square over the base is cartesian, by the ring pushout
  have H : IsPullback
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (projBaseChangeGradedHom E K) (projCoord E i))))
      (Proj.awayι (projGrading (E.baseChange K))
        (projBaseChangeGradedHom E K (projCoord E i)) hfs Nat.one_pos
        ≫ projToSpec (E.baseChange K))
      (Proj.awayι (projGrading E) (projCoord E i) (projCoord_mem_grading E i) Nat.one_pos
        ≫ projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) := by
    rw [awayι_projToSpec_eq_specMap' E _ _ Nat.one_pos,
      awayι_projToSpec_eq_specMap' (E.baseChange K) _ _ Nat.one_pos]
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (isPushout_awayBaseChange E K (projCoord E i) (projCoord_mem_grading E i))
  have key := isPullback_of_isoApex H C.isoPullback.symm
  rw [Iso.symm_hom, ← Category.assoc, C.isoPullback_inv_fst, C.isoPullback_inv_snd] at key
  exact key


/-- **The comparison morphism is an isomorphism** (PROVEN) — the last step of `hbc`, and with
it `geometricallyConnected_projToSpec` has no leaf left in this cluster.

`isPullback_projBaseChangeMap` says the square
`proj (E_K) → proj E` over `Spec K → Spec ℚ` is CARTESIAN, and `projBaseChangeHom` is exactly
the canonical map to the pullback of that square, so it is `IsPullback.isoPullback`.

Historical note, since the earlier version of this docstring sent a successor the wrong way:
`Proj.pullbackAwayιIso` looks relevant and is NOT (it compares two charts of ONE `Proj`), and
`pullbackSpecIso` is not needed either — the affine chart obligation is discharged by
`isPullback_SpecMap_of_isPushout` from a pushout of rings, which is strictly less work than
building the tensor-product comparison by hand. -/
theorem isIso_projBaseChangeHom : IsIso (projBaseChangeHom E K) := by
  have h := isPullback_projBaseChangeMap E K
  have he : projBaseChangeHom E K = h.isoPullback.hom := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [IsPullback.isoPullback_hom_fst]; exact Limits.pullback.lift_fst _ _ _
    · rw [IsPullback.isoPullback_hom_snd]; exact Limits.pullback.lift_snd _ _ _
  rw [he]
  infer_instance

/-- **`Proj` commutes with base change of the base field** — the `hbc` step of
`geometricallyConnected_projToSpec`.  Reduced to `isIso_projBaseChangeHom`; everything else
is proven above. -/
theorem nonempty_projPullbackIso :
    Nonempty (Limits.pullback (projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ≅ proj (E.baseChange K)) :=
  ⟨letI := isIso_projBaseChangeHom E K; (asIso (projBaseChangeHom E K)).symm⟩

end BaseChange

end GeometricConnectedness

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

**This theorem now has no direct sorry.**  The three steps stand as follows:

* `hbc` — the base change of the projective model is the projective model of the
  base-changed curve, `Proj (ℚ[X,Y,Z]⧸(W)) ×_ℚ Spec K ≅ Proj (K[X,Y,Z]⧸(W_K))`.  This
  is `Proj` commuting with base change of the graded ring.  It carries no ellipticity,
  and it is the ONE remaining leaf here: `nonempty_projPullbackIso`.
* `hne` — nonemptiness, the point at infinity `[0 : 1 : 0]`.  **PROVEN**, as
  `nonempty_proj`.
* `hpre` — preconnectedness.  **PROVEN** as `preconnectedSpace_proj`, modulo the single
  leaf `prime_projPolynomial` (irreducibility of the homogeneous cubic).  Note the
  argument used here is NOT the one this docstring originally proposed: it does not go
  through singularity of a reducible plane cubic and does not use
  `smoothOfRelativeDimension_projToSpec` at all.  The Weierstrass cubic is irreducible
  over EVERY field, singular ones included — mathlib's affine
  `WeierstrassCurve.Affine.irreducible_polynomial` needs only `[IsDomain R]` — so
  invoking smoothness would have been both circular-looking and unnecessary.

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
  obtain ⟨hbc⟩ := nonempty_projPullbackIso E K
  /- Nonemptiness: the point at infinity `[0 : 1 : 0]` is a `K`-rational point.  PROVEN,
  as `nonempty_proj`. -/
  haveI hne : Nonempty (proj (E.baseChange K)) := nonempty_proj _
  /- Preconnectedness: `W_K` is an irreducible cubic, so `K[X, Y, Z] ⧸ (W_K)` is a
  graded domain and its `Proj` is irreducible.  Proven as `preconnectedSpace_proj`,
  modulo the single leaf `prime_projPolynomial`. -/
  haveI hpre : PreconnectedSpace (proj (E.baseChange K)) := preconnectedSpace_proj _
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

/-- **An additive equivalence onto the geometric fibre, assembled from a
BARE equivalence plus the raw morphism identity** (PROVEN — one
`Subtype.ext`, and the whole content is that
`ProjGroupLaw.addCommGroup_add_val` is `rfl`).

This is the `hassoc`-free/`hassoc`-ful bridge, and it exists because the
two live cuts of the group law meet exactly here.  A producer that GLUES
`m` (see `exists_projMul`) can say what addition on `E(ℚ̄)` becomes only
as an identity between MORPHISMS,

    (eqv (x + y)).1 = AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ m

because `AbelianSchemeStruct.relPair` needs nothing but the structure
morphism and `m` is a bare morphism — no `AbelianSchemeStruct`, and in
particular no associativity, is involved.  A CONSUMER, on the other hand,
wants an `≃+`, whose `AddCommGroup` on `GeomFibrePt` comes from
`AbelianSchemeStruct.addCommGroup` and therefore reads the `add_assoc`
field, which `ProjGroupLaw.toAbelianSchemeStruct` feeds from `gl.hassoc`.

So the `≃+` is not expressible until `hassoc` is in hand, while the
identity is expressible before it.  This lemma is the exact point at
which the second is upgraded to the first, and it costs one
`Subtype.ext`. -/
noncomputable def ProjGroupLaw.geomFibreAddEquivOfVal {E : WeierstrassCurve ℚ}
    [E.IsElliptic] (gl : ProjGroupLaw E) {G : Type} [AddCommGroup G]
    (eqv : G ≃ GeomFibrePt (_root_.WeierstrassCurve.Projective.projToSpec E)
      (𝟙 (Spec (CommRingCat.of ℚ))))
    (hadd : ∀ x y : G,
      (eqv (x + y)).1 = AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ gl.m) :
    letI := gl.toAbelianSchemeStruct.addCommGroup
      (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
    G ≃+ GeomFibrePt (_root_.WeierstrassCurve.Projective.projToSpec E)
      (𝟙 (Spec (CommRingCat.of ℚ))) :=
  letI := gl.toAbelianSchemeStruct.addCommGroup
    (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
  { eqv with
    map_add' := fun x y => Subtype.ext (by
      show (eqv (x + y)).1 = (eqv x + eqv y).1
      rw [hadd x y]
      exact (gl.addCommGroup_add_val (eqv x) (eqv y)).symm) }

open _root_.WeierstrassCurve.Projective (proj projToSpec projInfty projNeg) in
/-- **ADDITIVITY: under the dictionary, `m` IS the addition of `E(K)`** (sorry node,
introduced 2026-07-27 as the first clause of `exists_projMul_geomFibreEquivVal`).

This is the whole geometric content of that clause, stated against the DATA
`ProjCoords.specPointEquiv` rather than against an existentially bound bijection — which
is exactly what the "ONE DICTIONARY" analysis says is required, and what makes the
statement true rather than false for a badly chosen bijection.

**`hlaw` is load-bearing**: for an arbitrary morphism `m` the conclusion is false.

## Route, and where the residue really is

Read at a pair of coordinate data `c, d` over `Spec K`:

* **off the diagonal** the conclusion is `hlaw` verbatim.  `hlaw` says
  `pullback.lift c.toHom d.toHom _ ≫ m = (c.add d h).toHom` whenever
  `addXYZ (E.map c.base) c.coord d.coord` spans the unit ideal, and `c.add d h` has
  `coordField = addXYZ (coordField c) (coordField d)`, whose affine point is
  `affinePoint c + affinePoint d` by mathlib's `Projective.Point.toAffine_add`.  So this
  half is a rewrite, not mathematics;
* **on the diagonal** `hlaw` says NOTHING.  Over a field the chord–tangent triple
  degenerates exactly where `d = u • c` (`ProjCoords.exists_units_smul_of_addXYZ_not_span`),
  i.e. exactly at `x = y`, and there the standard law gives the zero triple.  So the
  doubling `m(x, x)` is not pinned by `hlaw` pointwise and has to be obtained by DENSITY:
  `proj E ×_ℚ proj E` is integral (`geometricallyConnected_projToSpec` +
  `geometricallyReduced_projToSpec` give integrality of `proj E`, and the diagonal is a
  proper closed subset), `proj E` is separated, so two morphisms agreeing on a dense open
  agree.  `ext_of_fromSpecResidueField_eq` — the same tool `exists_projMul` uses to get
  `hcomm` — is the mechanism, run over the complement of the diagonal rather than over
  `Set.univ`.

**So an owner of this leaf should expect the work to be entirely on the diagonal**, and
should not re-derive the off-diagonal half. -/
theorem specPointEquiv_symm_add_eq_projMulPt {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {K : Type} [Field K] [DecidableEq K] (f : ℚ →+* K)
    (_m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E) (_hlaw : IsProjMulLaw E _m)
    (x y : (E.map f).toAffine.Point) :
    (ProjCoords.specPointEquiv f).symm (x + y) =
      projMulPt E _m ((ProjCoords.specPointEquiv f).symm x)
        ((ProjCoords.specPointEquiv f).symm y) :=
  sorry

open _root_.WeierstrassCurve.Projective (proj projToSpec projInfty projNeg) in
/-- **GALOIS EQUIVARIANCE of the dictionary** (sorry node, introduced 2026-07-27 as the
second clause of `exists_projMul_geomFibreEquivVal`).

`RelPoint.pre (specGal σ)` is precomposition with `Spec σ`
(`AbelianSchemeStruct.galSMul_def` is `rfl`, and in particular this clause does not
mention any `AbelianSchemeStruct`), so the statement is exactly: the dictionary intertwines
`WeierstrassCurve.Affine.Point.map σ` with precomposition by `Spec σ`.

*Route.*  Precomposing `c.toHom` with `Spec σ` is the coordinate datum whose coordinates
are `σ` applied to `c`'s — that is `Γ(Spec σ) = σ` under `Scheme.ΓSpecIso` — and applying
`σ` to a projective triple is `WeierstrassCurve.Affine.Point.map σ` under
`Projective.Point.toAffine`.  The only missing ingredient is the SAME `Proj` congruence
that `specPointEquiv_comp_projInfty_eq_zero` needs, namely naturality of
`Proj.fromOfGlobalSections` in the source scheme; see the section header before
`specPointEquiv_comp_projInfty_eq_zero` above, where it is stated. **Proving it once
discharges three of this file's leaves**, so factor it out rather than proving this
directly. -/
theorem specPointEquiv_symm_map_galois (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point) :
    (ProjCoords.specPointEquiv (E := E) (algebraMap ℚ (AlgebraicClosure ℚ))).symm
        (WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
      = specGal σ ≫
          (ProjCoords.specPointEquiv (E := E) (algebraMap ℚ (AlgebraicClosure ℚ))).symm x :=
  sorry

open _root_.WeierstrassCurve.Projective (proj projToSpec projInfty projNeg) in
/-- **The chord–tangent multiplication `m`, its three chart axioms, AND the
identification of the geometric fibre with `E(ℚ̄)`, produced together**
(**PROVEN 2026-07-27** over `ProjCoords.specPointEquiv` and the two clause
leaves immediately above; it was `exists_projMul` strengthened by the `hassoc`-free
chord–tangent clause, and it is the whole remaining content of item 8).

## Why this leaf exists, and what it replaced

`exists_projGroupLaw_geomFibreEquivVal` below used to carry this content
directly, and had to produce a whole `ProjGroupLaw` — associativity
included — in order to state it.  That was wasteful: `hassoc` is already
reduced, for an ARBITRARY `m` carrying `hcomm`/`hunit`/`hinv`, by
`projMul_assoc` (whose own residue is `projMul_assoc_pt`, the Milne
content).  Splitting the associativity off is therefore free, and it is
what the RESOLVING ROUTE recorded in
`exists_projGroupLaw_geomFibreAddEquiv`'s docstring prescribes: state the
chord–tangent clause in `hassoc`-free form, alongside the construction of
`m`, and let the consumer assemble the `ProjGroupLaw`.

**The `gl` stays existentially bound downstream because `m` is bound
here.**  That is what keeps the FALSITY-OF-CUT AUDIT on
`exists_projGroupLaw_geomFibreAddEquiv` discharged: a witness constructs
`m` and the coordinate identification *together*, so no rigidity theorem
is needed.  Stating the clause for an arbitrary `m` — or for an arbitrary
`ProjGroupLaw` — is exactly the shape that audit refutes.  Do not weaken
this leaf by moving `m` into the binders.

## Why it is a SIBLING of `exists_projMul` rather than an amendment to it

The route the audit prescribes is to put this clause ON `exists_projMul`.
That was not done, and deliberately: `exists_projMul` is under
construction (branch `flt-lean-76`, which restates it over a new
`ProjCoords` interface), and appending a conjunct to its existential
invalidates the witness being built.  So the strengthening is written
here instead, where it is inert.

**The two are not independent, and should be reconciled at integration.**
This leaf implies `exists_projMul` verbatim (drop the last conjunct), so
when the `ProjCoords` route lands, `exists_projMul` should NOT be proven
twice: prove THIS leaf from it, and delete nothing.

## The route to a witness, in the `ProjCoords` vocabulary

On branch `flt-lean-76` `exists_projMul` acquires a first conjunct

    ∀ (X : Scheme.{0}) (c d : ProjCoords E X)
        (h : Ideal.span (Set.range (addXYZ (E.map c.base) c.coord d.coord)) = ⊤),
      Limits.pullback.lift c.toHom d.toHom (hom_ext_spec_rat _ _) ≫ m = (c.add d h).toHom

— the chart-wise chord–tangent identity, for the glued `m`.  Together with
`ProjCoords.exists_of_specField` (every `Spec K`-point of `proj E` has
homogeneous coordinates, because `Pic (Spec K) = 0`) and
`ProjCoords.toHom_smul` (rescaling coordinates by a unit does not change
the morphism), that conjunct is exactly what this leaf needs:

* `eqv` is `ProjCoords E (Spec ℚ̄) ⧸ (rescaling) → GeomFibrePt`, i.e.
  `c ↦ c.toHom`, transported along mathlib's
  `WeierstrassCurve.Projective.Point.toAffineAddEquiv`
  (`W.Point ≃+ W.toAffine.Point` over a field), which is what identifies
  the coordinate classes with `(E⁄ℚ̄).Point`;
* the additivity clause is the `hlaw` conjunct read at `X = Spec ℚ̄`,
  together with `ProjCoords.toHom_eq_of_addXYZ_not_span` for the
  degenerate (diagonal) pairs where `addXYZ` fails to generate;
* Galois equivariance is then formal: `RelPoint.pre (specGal σ)` is
  precomposition with `Spec σ`, and precomposing `c.toHom` with `Spec σ`
  is `(σ • c).toHom` — the coordinatewise action of `σ` on `[x : y : z]`,
  which under `toAffineAddEquiv` is `WeierstrassCurve.Affine.Point.map`.

*Refuting check for that route*: exhibit a `Spec ℚ̄`-point of `proj E`
admitting no `ProjCoords` datum, or a pair of `ProjCoords` over `Spec ℚ̄`
with the same `toHom` that are not related by `ProjCoords.smul`.

**Nothing here needs `hassoc`**, which is the point: `AbelianSchemeStruct.relPair`
is built from the structure morphism alone and `m` is a bare morphism, so
the clause is expressible with no `AbelianSchemeStruct` anywhere.

## ONE DICTIONARY, THREE LEAVES — DISCHARGED 2026-07-27, and the dictionary
## is `ProjCoords.specPointEquiv`

(The analysis below was recorded after checking all three leaves against each
other, because the obvious reading — "these are two statements of one theorem,
merge them" — is wrong in a way that matters.  It has since been ACTED ON: the
shared implementation exists and both leaves are proven over it.  It is kept
because it is the reason the code has the shape it has.)

Three leaves in this file were the coordinate description of `Spec K ⟶ Proj 𝒜`:

* THIS one, at `K = AlgebraicClosure ℚ`, carrying **Galois equivariance** and
  the **chord–tangent identity against the `m` it constructs**;
* `exists_projPtAddEquiv_algClosed` above, for a general algebraically closed
  `K`, carrying **2-divisibility** and **algebraicity** (every scheme morphism
  acts affinely on `K`-points — Silverman *AEC* III.4.7);
* `ProjCoords.exists_of_specField`, the bare statement that every `Spec K`-point
  of `proj E` HAS homogeneous coordinates, true because `Pic (Spec K) = 0`.

**Neither of the first two implies the other, and merging their STATEMENTS is
not possible.**  Each has to *name* the bijection in order to state its own
extra content, so a common leaf would have to hand the bijection over as
data — and a leaf cannot, an existential closes over it.  Worse, quantifying
the extra content over *every* bijection satisfying the shared clauses is
**FALSE**: the shared clauses (`0 ↦ 0`, `neg ↦ neg`, Galois) do not pin the
bijection up to group automorphism, and this leaf's additivity clause fails
for a badly chosen one.  That is the same trap as the FALSITY-OF-CUT AUDIT,
one level down.

**What they DO share is the implementation, and it is now WRITTEN as
`ProjCoords.specPointEquiv`** — the dictionary as DATA rather than as an
existential, which is exactly what a shared implementation has to be.  It is

    ProjCoords.exists_of_specField            (surjectivity: every point has coordinates)
  + ProjCoords.exists_units_smul_of_toHom_eq  (injectivity: NEW, the converse of …)
  + ProjCoords.toHom_smul                     (… rescaling does not move the morphism)
  + WeierstrassCurve.Projective.Point.toAffineAddEquiv  (mathlib, `W.Point ≃+ W.toAffine.Point`)

**The injectivity half was NOT in the plan and is what blocked assembly.**  The
route recorded above names it only as a "refuting check"; without it stated as a
lemma the `right_inv` field of the `Equiv` cannot be discharged, so the plan read
as complete while the construction was impossible.  It is now
`ProjCoords.exists_units_smul_of_toHom_eq`, and it is the ONE leaf of the
dictionary itself.

Both leaves are now consumers, and what is left of each is exactly its own extra
content, cut into named leaves.  **Do not build a second dictionary.**

## CHARACTERISTIC GUARD — why this leaf does not need one

`exists_projPtAddEquiv_algClosed` carries an explicit
`hne : Nonempty (Spec K ⟶ proj E)` and is FALSE without it: `proj E` lies over
`Spec ℚ`, so a `K`-point forces a ring map `ℚ → K`, and at `char K = p > 0`
there is none — the point set is empty while every `AddCommGroup` contains `0`.
**This leaf is immune**, and it is worth saying why rather than leaving it to
be rediscovered: its `K` is literally `AlgebraicClosure ℚ`, which carries
`Algebra ℚ _`, so `GeomFibrePt (projToSpec E) (𝟙 _)` is inhabited by
`specAlgClos ℚ ≫ projInfty E` and the guard is discharged by the type.

Likewise the soundness clause that the loop counterexample forces — *quantify
over scheme MORPHISMS, not over bare bijections* — is satisfied here by
construction: `m` is a morphism `A ×_ℚ A ⟶ A`, taken as a HYPOTHESIS together
with the `ProjCoords` law `hlaw` that pins it to the chord–tangent
construction, so the additivity clause never speaks about a set-level
operation.

**`hlaw` IS LOAD-BEARING AND MUST NOT BE DROPPED.**  Without it `m` is an
arbitrary morphism and the additivity clause is false for almost all of them.
Its role is exactly to say "this `m` is the one `exists_projMul` builds"; the
statement is phrased this way, rather than re-binding `m` existentially, so
that the tree constructs the multiplication ONCE — a second existential here
would have been a second, independent assertion that the group law exists
(reconciled at integration, 2026-07-27). -/
theorem exists_projMul_geomFibreEquivVal (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hlaw : IsProjMulLaw E m) :
    ∃ eqv : (E⁄(AlgebraicClosure ℚ)).Point ≃
        GeomFibrePt (projToSpec E) (𝟙 (Spec (CommRingCat.of ℚ))),
      (∀ x y : (E⁄(AlgebraicClosure ℚ)).Point,
          (eqv (x + y)).1 = AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ m) ∧
        ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
          eqv (WeierstrassCurve.Affine.Point.map
              (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
            = RelPoint.pre (specGal σ)
                (specGal_comp_base (𝟙 (Spec (CommRingCat.of ℚ))) σ) (eqv x) := by
  classical
  refine ⟨(ProjCoords.specPointEquiv (E := E) (algebraMap ℚ (AlgebraicClosure ℚ))).symm.trans
    { toFun := fun y => ⟨y, hom_ext_spec_rat _ _⟩
      invFun := fun y => y.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }, ?_, ?_⟩
  · intro x y
    exact specPointEquiv_symm_add_eq_projMulPt _ m hlaw x y
  · intro σ x
    exact Subtype.ext (specPointEquiv_symm_map_galois E σ x)

/-- **The projective Weierstrass model carries a group law whose geometric
fibre IS `E(ℚ̄)`, equivariantly — the `hassoc`-FREE form** (PROVEN
2026-07-27 from `exists_projMul_geomFibreEquivVal` and `projMul_assoc`;
it was the last open leaf of item 8 until then, and the geometric content
has moved to that leaf).

This is `exists_projGroupLaw_geomFibreAddEquiv` with the two pieces of
`AbelianSchemeStruct` structure stripped out of the CONCLUSION:

* the `≃+` is a bare `≃` together with the raw morphism identity
  `(eqv (x + y)).1 = AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ gl.m`
  — `relPair` needs only the structure morphism, so no `AddCommGroup`,
  and hence no `hassoc`, appears;
* `gl.toAbelianSchemeStruct.galSMul` is replaced by what it is *by
  definition* (`AbelianSchemeStruct.galSMul_def` is `rfl`), namely
  `RelPoint.pre (specGal σ) _` — again free of the structure.

The `gl : ProjGroupLaw E` is still EXISTENTIALLY bound, which is what
keeps the FALSITY-OF-CUT AUDIT below discharged: it is bound because a
statement over an arbitrary `ProjGroupLaw` needs the rigidity theorem.

## Why this shape, and how it became plumbing

`exists_projAdd` was decomposed (branch `flt-lean-141`) into
`exists_projMul` — which CONSTRUCTS `m` by gluing the chord–tangent forms
— and `projMul_assoc`, which supplies `hassoc` for an ARBITRARY `m`.  The
chord–tangent clause needs the concrete glued `m` (only `exists_projMul`
has it) *and*, in `≃+` form, `hassoc` (only available after
`projMul_assoc`).  Stated in the `hassoc`-free form above it needs only
the first — which is what makes the assembly below possible.

**The assembly (2026-07-27, RECONCILED AT INTEGRATION).**  `exists_projMul`
supplies `m` together with its `ProjCoords` law `hlaw` and
`hcomm`/`hunit`/`hinv`; `exists_projMul_geomFibreEquivVal E m hlaw` then
supplies the chord–tangent clause for that same `m`;
`projMul_assoc E m hcomm hunit hinv` supplies `hassoc`; and
`projInfty E` / `projNeg E` / `hom_ext_spec_rat` supply the remaining six
fields of `ProjGroupLaw`.  So this declaration carries no mathematical
content: the geometry lives one level up, and the associativity lives in
`projMul_assoc_pt`.

Note the assembly does NOT go through `nonempty_projGroupLaw`, and could
not: that produces an ARBITRARY `ProjGroupLaw`, and the chord–tangent
clause holds only for the glued `m` (this is the FALSITY-OF-CUT AUDIT on
the next declaration).  What pins `m` is `hlaw`, which is exactly why the
leaf above takes it as a HYPOTHESIS rather than re-asserting the existence
of `m`: as originally branched it bound its own `m`, and the tree would
then have asserted the existence of the multiplication twice.

## `_gl₀` STILL STAYS — and what changed about the anchor chain

`_gl₀` is the same CONE ANCHOR as on the next declaration and is unused
for the same reason; see there.  **Re-checked after this assembly landed
(2026-07-27):** `projMul_assoc` and `exists_projMul` now BOTH reach the
root cone through real dependency edges — this proof applies both — so
neither depends on the anchor any more.  `nonempty_projGroupLaw` and
`exists_projAdd` still reach it ONLY through `_gl₀`, so deleting the
argument today would still make those two free-floating.  The anchor comes
out when they acquire a real consumer. -/
theorem exists_projGroupLaw_geomFibreEquivVal (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (_gl₀ : ProjGroupLaw E) :
    ∃ gl : ProjGroupLaw E,
      ∃ eqv : (E⁄(AlgebraicClosure ℚ)).Point ≃
          GeomFibrePt (_root_.WeierstrassCurve.Projective.projToSpec E)
            (𝟙 (Spec (CommRingCat.of ℚ))),
        (∀ x y : (E⁄(AlgebraicClosure ℚ)).Point,
            (eqv (x + y)).1 = AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ gl.m) ∧
          ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
            eqv (WeierstrassCurve.Affine.Point.map
                (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
              = RelPoint.pre (specGal σ)
                  (specGal_comp_base (𝟙 (Spec (CommRingCat.of ℚ))) σ) (eqv x) := by
  obtain ⟨m, hlaw, hcomm, hunit, hinv⟩ := exists_projMul E
  obtain ⟨eqv, hadd, hgal⟩ := exists_projMul_geomFibreEquivVal E m hlaw
  exact ⟨{ m := m
           e := _root_.WeierstrassCurve.Projective.projInfty E
           i := _root_.WeierstrassCurve.Projective.projNeg E
           hm := hom_ext_spec_rat _ _
           he := hom_ext_spec_rat _ _
           hi := hom_ext_spec_rat _ _
           hassoc := projMul_assoc E m hcomm hunit hinv
           hcomm := hcomm
           hunit := hunit
           hinv := hinv }, eqv, hadd, hgal⟩

/-- **The projective Weierstrass model carries a group law whose geometric
fibre IS `E(ℚ̄)`, equivariantly** (PROVEN from
`exists_projGroupLaw_geomFibreEquivVal`; item 8, RESTATED 2026-07-27 —
see the FALSITY-OF-CUT AUDIT below for what it replaces).

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

### RECONCILIATION, 2026-07-27 — the obstruction is REMOVED downstream; `_gl₀` still STAYS

The two cuts were merged into one tree on this date and the end state above
was attempted directly.  **It does not compose as prescribed**, for a
structural reason that is worth recording because it is not visible from
either cut alone; the resolution is recorded after it, and the DOWNSTREAM
half of it has landed — this declaration is now PROVEN, and the open leaf is
`exists_projGroupLaw_geomFibreEquivVal` above, which is `hassoc`-free.

Meanwhile `exists_projAdd` was itself decomposed (branch `flt-lean-141`) into
`exists_projMul` — the gluing, which CONSTRUCTS `m` from
`WeierstrassCurve.Projective.addXYZ` and yields `hcomm`/`hunit`/`hinv` — and
`projMul_assoc`, which supplies `hassoc` for an ARBITRARY `m` carrying those
three axioms.  `exists_projAdd` is now PROVEN from the two.  So for
`exists_projAdd` to *gain* a chord–tangent clause, one of those two leaves
must supply it, and neither can:

* **`exists_projMul` cannot STATE the clause.**  The clause's `≃+` is an
  additive equivalence onto `GeomFibrePt`, whose `AddCommGroup` comes from
  `AbelianSchemeStruct.addCommGroup`, which reads the `add_assoc` field —
  and `ProjGroupLaw.toAbelianSchemeStruct` feeds that field from `gl.hassoc`.
  `exists_projMul` deliberately does not have `hassoc`.  So the clause is not
  even expressible there in `≃+` form.
* **`projMul_assoc` cannot PROVE the clause.**  It quantifies over an
  arbitrary `m`, and an arbitrary `m` is exactly what the FALSITY-OF-CUT
  AUDIT above shows requires the rigidity theorem.  Putting the clause there
  reintroduces the very trap this leaf was restated to escape.

So the clause needs BOTH the concrete glued `m` (only in `exists_projMul`)
and `hassoc` (only after `projMul_assoc`), and 141's cut runs transverse to
exactly that pairing.  The two cuts are individually correct and jointly
non-composing; that is why this reconciliation is a cut-level decision rather
than a merge, and it was left to the owners rather than made unilaterally.

### THE RESOLVING ROUTE — half of it has LANDED

State the clause in a `hassoc`-FREE form, replacing the `≃+` by a bare
equivalence plus the raw morphism identity

    ∃ eqv : (E⁄(AlgebraicClosure ℚ)).Point ≃ GeomFibrePt (projToSpec E) (𝟙 _),
      (∀ x y, (eqv (x + y)).1 = AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ m) ∧ …

`relPair` needs only the structure morphism, and `m` is the bare morphism, so
this is expressible without any `AbelianSchemeStruct`.  The `≃+` then
assembles from the bare `≃` plus that identity once `hassoc` is in hand,
because `ProjGroupLaw.addCommGroup_add_val` is `rfl`.

**What landed (2026-07-27).**  The assembly is now a proven lemma,
`ProjGroupLaw.geomFibreAddEquivOfVal` above, and the open leaf of item 8 is
`exists_projGroupLaw_geomFibreEquivVal` — the `hassoc`-free statement, with
`gl` still existentially bound so the FALSITY-OF-CUT AUDIT stays discharged.
THIS declaration is PROVEN from those two, in three lines.  So the
`hassoc`-entanglement is gone from every remaining OPEN statement in item 8,
which was the whole obstruction.

**What landed next (2026-07-27, same day).**  The clause was put on a SIBLING
of `exists_projMul` rather than on `exists_projMul` itself —
`exists_projMul_geomFibreEquivVal`, stated just above
`exists_projGroupLaw_geomFibreEquivVal` — for exactly the reason recorded in
the paragraph below: `exists_projMul` had a live owner mid-construction and
appending a conjunct to its existential would have invalidated the witness
being built.  With `m` and the identification bound by ONE existential,
`projMul_assoc` supplies `hassoc` for that same `m` and
`exists_projGroupLaw_geomFibreEquivVal` became a three-line assembly.  So item
8's geometric content now sits in `exists_projMul_geomFibreEquivVal`, and both
statements below it are PROVEN.

**What has NOT landed, and the exact signature for whoever takes it.**  The
last step — putting the clause on `exists_projMul` proper, whence
`exists_projMul_geomFibreEquivVal` is proven from it rather than being a
second, independent assertion that `m` exists.  **Do not prove
`exists_projMul` twice**: reconcile.  The signature below is compiler-checked
in situ (it elaborates inside the `open _root_.WeierstrassCurve.Projective`
section, with `sorry`):

    theorem exists_projMul (E : WeierstrassCurve ℚ) [E.IsElliptic] :
        ∃ m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E,
          <hcomm> ∧ <hunit> ∧ <hinv> ∧
            ∃ eqv : (WeierstrassCurve.Affine.baseChange E (AlgebraicClosure ℚ)).Point ≃
                GeomFibrePt (projToSpec E) (𝟙 (Spec (CommRingCat.of ℚ))),
              (∀ x y, (eqv (x + y)).1 =
                  AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ m) ∧
                ∀ (σ : Field.absoluteGaloisGroup ℚ) (x),
                  eqv (WeierstrassCurve.Affine.Point.map
                      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
                    = RelPoint.pre (specGal σ)
                        (specGal_comp_base (𝟙 (Spec (CommRingCat.of ℚ))) σ) (eqv x)

**Note the `baseChange` spelt out.**  Writing `(E⁄(AlgebraicClosure ℚ)).Point`
there does NOT compile: `exists_projMul` lives inside the
`open _root_.WeierstrassCurve.Projective` section, and `⁄` is then ambiguous
between `WeierstrassCurve.Projective.baseChange` and
`WeierstrassCurve.Affine.baseChange` (checked: four `Ambiguous term` errors).
The Affine one is meant, and must be written out.  This is the one respect in
which the route as originally prescribed is wrong.

*Refuting check for the obstruction as originally stated*: find an
`AddCommGroup` on `GeomFibrePt` that does not route through
`AbelianSchemeStruct.addCommGroup`, or a `toAbelianSchemeStruct` that does not
consume `gl.hassoc`.

**Consequence for `_gl₀`: it must NOT be deleted yet.**  Checked directly —
the only term-level consumers of `nonempty_projGroupLaw` in the whole tree are
`projGroupLaw` and `exists_projGeomFibreAddEquiv` below, and BOTH reach it
solely by passing it as this `_gl₀`; and the only consumer of
`exists_projAdd` is `nonempty_projGroupLaw`.  Deleting the argument today
therefore detaches `nonempty_projGroupLaw`, `exists_projAdd`, `exists_projMul`
and `projMul_assoc` from the root cone all at once, making four declarations —
two of them live, owned work — free-floating.  **Re-checked twice on
2026-07-27, after each half landed; still true, with ONE change.**
`projMul_assoc` now reaches the cone by a REAL edge —
`exists_projGroupLaw_geomFibreEquivVal`'s proof applies it — so the anchor
carries three declarations rather than four.  `nonempty_projGroupLaw`,
`exists_projAdd` and `exists_projMul` still reach the cone only through
`_gl₀`, which this declaration passes straight through to
`exists_projGroupLaw_geomFibreEquivVal`.  The remaining edge appears when
`exists_projMul` itself carries the chord–tangent clause and
`exists_projMul_geomFibreEquivVal` consumes it; the anchor comes out at that
commit, not at this one.

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
                 (𝟙 (Spec (CommRingCat.of ℚ))) σ (eqv x)) := by
  obtain ⟨gl, eqv, hadd, hgal⟩ := exists_projGroupLaw_geomFibreEquivVal E _gl₀
  exact ⟨gl, gl.geomFibreAddEquivOfVal eqv hadd, hgal⟩

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

section AffineChart

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- **Translation carrying a prescribed section to the zero section**
(PROVEN, and stated for an arbitrary abelian scheme).

If `p : S ⟶ A` is a section of `f : A ⟶ S` then `x ↦ x ⊖ p` is an
automorphism of `A` over `S` sending `p` to the zero section of `ab`.

This is what removes the RIGIDITY problem from `exists_affineChart_projModel`
below, and it is worth stating separately for exactly the reason the
FALSITY-OF-CUT AUDIT on `exists_projGroupLaw_geomFibreAddEquiv` gives:
`ProjGroupLaw` pins **nothing** about its unit section `e`, so a leaf
asserting that the complement of the standard chart `D₊(Z)` *is* the range
of `gl`'s zero section quantifies over group laws whose unit is an
arbitrary rational point — every translate of the chord–tangent law is
again a `ProjGroupLaw`.  The statement is nevertheless TRUE, and this lemma
is the reason: it is true because `A` has an automorphism over `S` carrying
`[0 : 1 : 0]` to `gl.e`, not because the two points coincide.

The proof is Yoneda and nothing else — no geometry.  Everything happens
inside the abelian group `RelPoint f f`, whose tautological element
`⟨𝟙 A, _⟩` represents the identity morphism: writing `c` for the constant
point `⊖p` pulled back along `f`, the two morphisms are represented by
`𝟙 + c` and `𝟙 + (⊖c)`, and `RelPoint.pre` (precomposition) is additive by
`ab.pre_add`, sends the tautological element to its argument, and fixes
anything pulled back along `f`.  Those three facts turn "the two composites
are the identity" into `(𝟙 + c) + (⊖c) = 𝟙`, and `p ≫ τ = 0` into
`p ⊖ p = 0`. -/
theorem exists_translation_toZero {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    (p : S ⟶ A) (hp : p ≫ f = 𝟙 S) :
    ∃ τ : A ⟶ A, IsIso τ ∧ τ ≫ f = f ∧ p ≫ τ = (ab.zero (𝟙 S)).1 := by
  set P : RelPoint f (𝟙 S) := ⟨p, hp⟩ with hPdef
  set c : RelPoint f f := RelPoint.pre f (Category.comp_id f) (ab.neg P) with hcdef
  set c' : RelPoint f f := RelPoint.pre f (Category.comp_id f) (ab.neg (ab.neg P)) with hc'def
  set slf : RelPoint f f := ⟨𝟙 A, Category.id_comp f⟩ with hslfdef
  set τ : RelPoint f f := ab.add slf c with hτdef
  set τ' : RelPoint f f := ab.add slf c' with hτ'def
  -- `c` and `c'` are inverse to each other
  have hcc' : ab.add c c' = ab.zero f := by
    rw [hcdef, hc'def, ← ab.pre_add f (Category.comp_id f), ab.add_comm,
      ab.neg_add (ab.neg P), ab.pre_zero]
  have hc'c : ab.add c' c = ab.zero f := by rw [ab.add_comm]; exact hcc'
  -- precomposition by a point over `f` fixes anything pulled back along `f`
  have hpre_pull : ∀ (y : RelPoint f f) (z : RelPoint f (𝟙 S)),
      RelPoint.pre y.1 y.2 (RelPoint.pre f (Category.comp_id f) z)
        = RelPoint.pre f (Category.comp_id f) z := by
    intro y z
    refine Subtype.ext ?_
    show y.1 ≫ f ≫ z.1 = f ≫ z.1
    rw [← Category.assoc, y.2]
  have hpre_slf : ∀ y : RelPoint f f, RelPoint.pre y.1 y.2 slf = y := fun y =>
    Subtype.ext (Category.comp_id y.1)
  have hττ' : τ.1 ≫ τ'.1 = 𝟙 A := by
    have : RelPoint.pre τ.1 τ.2 τ' = slf := by
      rw [hτ'def, ab.pre_add, hpre_slf, hc'def, hpre_pull, ← hc'def, hτdef, ab.add_assoc,
        hcc', ab.add_comm, ab.zero_add]
    exact congrArg Subtype.val this
  have hτ'τ : τ'.1 ≫ τ.1 = 𝟙 A := by
    have : RelPoint.pre τ'.1 τ'.2 τ = slf := by
      rw [hτdef, ab.pre_add, hpre_slf, hcdef, hpre_pull, ← hcdef, hτ'def, ab.add_assoc,
        hc'c, ab.add_comm, ab.zero_add]
    exact congrArg Subtype.val this
  refine ⟨τ.1, ⟨τ'.1, hττ', hτ'τ⟩, τ.2, ?_⟩
  have hkey : RelPoint.pre p hp τ = ab.zero (𝟙 S) := by
    have h1 : RelPoint.pre p hp slf = P := Subtype.ext (Category.comp_id p)
    have h2 : RelPoint.pre p hp c = ab.neg P := by
      refine Subtype.ext ?_
      show p ≫ f ≫ (ab.neg P).1 = (ab.neg P).1
      rw [← Category.assoc, hp, Category.id_comp]
    rw [hτdef, ab.pre_add, h1, h2, ab.add_comm]
    exact ab.neg_add P
  exact congrArg Subtype.val hkey

/-- **Any two endomorphisms of `Spec ℚ` agree** (PROVEN).

`Spec` is fully faithful and `ℚ` has a unique ring endomorphism
(`Rat.subsingleton_ringHom`).  This is the declaration the docstring of
`WeierstrassCurve.Projective.projInfty` refers to as
`Fermat.subsingleton_hom_spec_rat` — that name never existed; this is it. -/
theorem subsingleton_hom_specRat (φ ψ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ℚ)) :
    φ = ψ := by
  apply (Spec.homEquiv (R := CommRingCat.of ℚ) (S := CommRingCat.of ℚ)).injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **The point at infinity is a section of the structure morphism**
(PROVEN, and free: over `ℚ` there is nothing to check). -/
theorem projInfty_projToSpec (E : WeierstrassCurve ℚ) :
    _root_.WeierstrassCurve.Projective.projInfty E ≫
        _root_.WeierstrassCurve.Projective.projToSpec E = 𝟙 (Spec (CommRingCat.of ℚ)) :=
  subsingleton_hom_specRat _ _

/-- Each homogeneous coordinate has degree `1` in the homogeneous
coordinate ring (PROVEN; the same one-liner as in
`smoothOfRelativeDimension_projToSpec`, named here because three
declarations below need it). -/
theorem mem_projGrading_projCoord (E : WeierstrassCurve ℚ) (i : Fin 3) :
    projCoord E i ∈ _root_.WeierstrassCurve.Projective.projGrading E 1 :=
  HomogeneousIdeal.mk_mem_quotientGrading
    (MvPolynomial.mem_homogeneousSubmodule _ _ |>.mpr (MvPolynomial.isHomogeneous_X _ _))

/-- **The chart ring at `Z ≠ 0` IS mathlib's affine coordinate ring**
(sorry node — pure commutative algebra, no scheme theory).

`ProjChartRing E 2` is `ℚ[u, v] ⧸ (dehom₂ W)` in the two chart variables
`ProjChartVar 2 = {0, 1}`, and `dehomogenizeAt ℚ 2` substitutes `Z ↦ 1`,
so `projChartPolynomial E 2` is *literally*
`v² + a₁uv + a₃v − u³ − a₂u² − a₄u − a₆` — the affine Weierstrass
polynomial.  Mathlib's `WeierstrassCurve.Affine.CoordinateRing` is
`AdjoinRoot W.polynomial` with `W.polynomial : ℚ[X][Y]`, so all that is
missing is the bookkeeping isomorphism

  `MvPolynomial (ProjChartVar 2) ℚ ≃ₐ[ℚ] ℚ[X][Y]`,  `u ↦ X`, `v ↦ Y`,

carrying `projChartPolynomial E 2` to `E.toAffine.polynomial`, and then
`Ideal.quotientEquiv` / `AdjoinRoot.quotEquiv`-style transport of the
quotient.  `MvPolynomial.finSuccEquiv`, `MvPolynomial.pUnitAlgEquiv` and
`MvPolynomial.renameEquiv` are the relevant mathlib entry points, together
with `AdjoinRoot` being `Polynomial ℚ[X] ⧸ span {polynomial}` by
definition.

THE CHECK THAT WOULD REFUTE "OPEN": a declaration anywhere in the tree
relating `Fermat.ProjChartRing` (or `Fermat.projChartPolynomial`) to
`WeierstrassCurve.Affine.CoordinateRing` or to
`WeierstrassCurve.Affine.polynomial`.  There is none.

NOT VACUOUS: the commuting triangle over `ℚ` is what the consumer needs —
without it the isomorphism could be any ring isomorphism whatsoever and
the chart would not be a chart *over the base*.

**A second consumer is waiting for this.**  `exists_projChartRingEquiv`
(LEAF A of item 7a) identifies `(ℚ[X, Y, Z] ⧸ (W))_{(xᵢ)}` with
`ProjChartRing E i`; composing the two is exactly what
`exists_affineChart_projInfty` does below, so anybody proving that leaf is
one composition away from this one at `i = 2`. -/
theorem exists_coordinateRingEquiv_projChartRing (E : WeierstrassCurve ℚ) :
    ∃ e : ProjChartRing E 2 ≃+* E.toAffine.CoordinateRing,
      (e : ProjChartRing E 2 →+* E.toAffine.CoordinateRing).comp
          (algebraMap ℚ (ProjChartRing E 2)) = algebraMap ℚ E.toAffine.CoordinateRing :=
  sorry

/-- **The complement of the standard chart `D₊(Z)` is the point at
infinity** (sorry node — the topological half, no group law and no
coordinate ring).

TRUE: modulo `Z̄` the homogeneous coordinate ring becomes
`ℚ[X, Y] ⧸ (X³)` — substituting `Z = 0` into the Weierstrass cubic leaves
`−X³` — so `X̄` is nilpotent modulo `(Z̄)` and every prime containing `Z̄`
contains `X̄`.  A relevant homogeneous prime containing `(X̄, Z̄)` therefore
corresponds to a homogeneous prime of `ℚ[Y]` not containing `(Y)`, i.e. to
`(0)`; so `V₊(Z̄) = {(X̄, Z̄)}`, a single point.  And `projInfty` is
`Proj.fromOfGlobalSections` at the coordinates `(0, 1, 0)`, whose image is
that prime.

**Half of this is already PROVEN in this file and should be reused, not
redone**: `Fermat.pointAtInfinity` is the prime `(X̄, Z̄)` as a point of
`ProjectiveSpectrum (projGrading W)`, with `isPrime_infIdeal`,
`isHomogeneous_infIdeal`, `mk_X1_notMem_infIdeal` and
`projPolynomial_mem_span_X_Z` all discharged there over an arbitrary base
FIELD.  So the two remaining halves are

* `(↑(Proj.basicOpen 𝒜 Z̄))ᶜ = {pointAtInfinity E}`, and
* `Set.range (projInfty E).base = {pointAtInfinity E}`,

and it was stated as a single equation only because the two singletons
elaborate in different (defeq but not syntactically equal) ambient types,
`↥(Proj (projGrading E))` and `↥(proj E)`.

`Proj.mem_basicOpen` (`x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal`) is
the entry point for the first half; `Proj.fromOfGlobalSections` and
`ProjectiveSpectrum.mem_basicOpen` for the second.

NOT VACUOUS: a wrong answer here is not a weaker statement but a false
one — the equation pins a specific point of an irreducible curve. -/
theorem compl_basicOpen_projCoord_two (E : WeierstrassCurve ℚ) :
    (↑(Proj.basicOpen (_root_.WeierstrassCurve.Projective.projGrading E)
        (projCoord E 2)) : Set ↥(Proj (_root_.WeierstrassCurve.Projective.projGrading E)))ᶜ
      = Set.range (_root_.WeierstrassCurve.Projective.projInfty E).base :=
  sorry

/-- **The affine chart `Z ≠ 0`, pinned at the POINT AT INFINITY**
(PROVEN from `exists_projChartRingEquiv`, `exists_coordinateRingEquiv_`
`projChartRing` and `compl_basicOpen_projCoord_two`).

This is `exists_affineChart_projModel` with the group law removed: the
removed point is the concrete `projInfty E` rather than the unit of an
arbitrary `ProjGroupLaw`, so nothing about rigidity or translation enters
here.  The chart is `Proj.awayι` at the homogeneous coordinate `Z̄`,
transported along the dehomogenisation isomorphism; the structure-map
clause is `awayι_projToSpec_eq_specMap` composed with the two commuting
triangles, and the range clause is `Proj.opensRange_awayι`.

The internal `aux` restates the goal with `Proj (projGrading E)` in place
of `proj E`: the two are equal by `rfl`, but `proj` is a semireducible
`def`, so instance search does not see through it and neither
`IsOpenImmersion (Proj.awayι …)` nor the `rw` of
`awayι_projToSpec_eq_specMap` fires at the unfolded spelling. -/
theorem exists_affineChart_projInfty (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶
        _root_.WeierstrassCurve.Projective.proj E,
      IsOpenImmersion ι ∧
        ι ≫ _root_.WeierstrassCurve.Projective.projToSpec E =
          Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)) ∧
        Set.range ι.base =
          (Set.range (_root_.WeierstrassCurve.Projective.projInfty E).base)ᶜ := by
  classical
  obtain ⟨e₀, he₀⟩ := exists_projChartRingEquiv E 2 (mem_projGrading_projCoord E 2)
  obtain ⟨e₁, he₁⟩ := exists_coordinateRingEquiv_projChartRing E
  set e : HomogeneousLocalization.Away (_root_.WeierstrassCurve.Projective.projGrading E)
      (projCoord E 2) ≃+* E.toAffine.CoordinateRing := e₀.trans e₁ with he
  have aux : ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶
      Proj (_root_.WeierstrassCurve.Projective.projGrading E),
      IsOpenImmersion ι ∧
        ι ≫ _root_.WeierstrassCurve.Projective.projToSpec E =
          Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)) ∧
        Set.range ι.base =
          (Set.range (_root_.WeierstrassCurve.Projective.projInfty E).base)ᶜ := by
    refine ⟨Spec.map e.toCommRingCatIso.hom ≫
      Proj.awayι (_root_.WeierstrassCurve.Projective.projGrading E) (projCoord E 2)
        (mem_projGrading_projCoord E 2) Nat.one_pos, inferInstance, ?_, ?_⟩
    · rw [Category.assoc, awayι_projToSpec_eq_specMap E _ (mem_projGrading_projCoord E 2),
        ← Spec.map_comp]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      have h0 := congrArg (fun g : ℚ →+* ProjChartRing E 2 => e₁ (g x)) he₀
      have h1 := congrArg (fun g : ℚ →+* E.toAffine.CoordinateRing => g x) he₁
      simpa [he] using h0.trans h1
    · rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
        Proj.opensRange_awayι, ← compl_basicOpen_projCoord_two E]
      exact (compl_compl _).symm
  exact aux

/-- **The affine chart `Z ≠ 0` of the projective Weierstrass model is
`Spec` of the affine coordinate ring, and its complement is the unit
section** (PROVEN 2026-07-27 from `exists_affineChart_projInfty` and
`exists_translation_toZero`; formerly a sorry node).

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

## THE CUT (2026-07-27), and the DEFECT it repairs

The third bullet of the previous plan — "`V₊(Z) = {[0 : 1 : 0]}`, and
this point is the range of `gl.e`" — is **FALSE as an identification of
points**, for exactly the reason recorded in the FALSITY-OF-CUT AUDIT on
`exists_projGroupLaw_geomFibreAddEquiv`: `ProjGroupLaw` pins nothing about
its unit `e`, so if `E(ℚ) ≠ {∞}` then translating the chord–tangent law by
a rational point `P` gives another `ProjGroupLaw` whose unit section is
`P`, and the complement of `D₊(Z)` is then not the range of `gl.e`.

The statement itself is nevertheless TRUE — the same shape as that audit's
verdict, and repaired the same way rather than refuted.  It is true because
`proj E` has an automorphism over `ℚ` carrying `[0 : 1 : 0]` to `gl.e`,
namely translation by `⊖[0 : 1 : 0]` in `gl`'s own group law, and the
chart may be composed with it.  So the leaf splits into

* `exists_translation_toZero` (PROVEN above) — the translation, for an
  arbitrary abelian scheme, by Yoneda inside `RelPoint f f`;
* `exists_affineChart_projInfty` (PROVEN above) — the same statement with
  `gl` deleted and the removed point taken to be `projInfty E`;

and the two genuinely open pieces are the sub-leaves of the latter,
`exists_coordinateRingEquiv_projChartRing` (commutative algebra) and
`compl_basicOpen_projCoord_two` (topology of `Proj`).  Neither mentions a
group law, which is the point of the cut: no `ProjGroupLaw` survives into
either.

The first bullet of the old plan is RETIRED as already available: the
basic-open cover of `Proj` **is** at this pin, as `Proj.awayι`,
`Proj.opensRange_awayι` and the `IsOpenImmersion` instance beside them.

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
            (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ := by
  classical
  obtain ⟨ι₀, hopen₀, hstr₀, hrange₀⟩ := exists_affineChart_projInfty E
  obtain ⟨τ, hτiso, hτf, hτp⟩ := exists_translation_toZero gl.toAbelianSchemeStruct
    (_root_.WeierstrassCurve.Projective.projInfty E) (projInfty_projToSpec E)
  refine ⟨ι₀ ≫ τ, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hτf]; exact hstr₀
  · have hbij : Function.Bijective (τ.base : _root_.WeierstrassCurve.Projective.proj E →
        _root_.WeierstrassCurve.Projective.proj E) := (Scheme.homeoOfIso (asIso τ)).bijective
    rw [← hτp]
    show Set.range ((ι₀ ≫ τ).base) = (Set.range
      ((_root_.WeierstrassCurve.Projective.projInfty E ≫ τ).base))ᶜ
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [hrange₀, Set.image_compl_eq hbij]

end AffineChart

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
  -- The group law must be the CONCRETE `projGroupLaw E`, not an arbitrary one
  -- from `nonempty_projGroupLaw`: `exists_projGeomFibreAddEquiv` was restated on
  -- 2026-07-27 to be about `projGroupLaw E` specifically (the old form quantified
  -- over an arbitrary `ProjGroupLaw`, which pins nothing about `m` — see
  -- `exists_projGroupLaw_geomFibreAddEquiv`), so it no longer takes a `gl`.
  exact ⟨_root_.WeierstrassCurve.Projective.proj E,
    _root_.WeierstrassCurve.Projective.projToSpec E,
    (projGroupLaw E).toAbelianSchemeStruct,
    smoothOfRelativeDimension_projToSpec E,
    exists_affineChart_projModel E (projGroupLaw E),
    exists_projGeomFibreAddEquiv E⟩

/-! ### The REVERSE bridge: an elliptic scheme over `Spec ℚ` HAS a Weierstrass model

Everything above runs from a `WeierstrassCurve ℚ` to a scheme.  The three
declarations below run the other way, and they exist because two leaves of
`Fermat/FLT/ModularCurve/X0.lean` — `exists_weierstrass_jm_of_gamma0Datum`
and, through it, `exists_weierstrass_jm_of_relPointY0` — start from a
`Gamma0Datum p SpecQ`, i.e. from a bare `AbelianSchemeStruct` of relative
dimension one, and have to produce the curve.  `X0.lean`'s own docstring at
`exists_weierstrass_jm_of_gamma0Datum` records the gap in as many words:
"the tree has only the FORWARD bridge `exists_ellipticScheme_of_weierstrass`
… there is no declaration anywhere in `Fermat/` producing a
`WeierstrassCurve ℚ` from an `AbelianSchemeStruct`".  This subsection is
that declaration.

**Why it lives HERE and not in `X0.lean`.**  Same reason as everything else
in this module: the intended proof is projective-model geometry, and the
`Proj` machinery reaches the reserved atom `over` (see the module docstring).
The STATEMENTS below are written so that none of them mentions `proj` or
`projToSpec` — the model conjunct is spelled out as an open immersion of
`Spec ℚ[E]`, exactly as in `exists_ellipticScheme_isWeierstrassModel_of_projModel`
above — so `X0.lean` consumes them in a PROOF BODY under its existing
non-public `import`, and nothing has to become `public`.

**Why the conjunct is spelled out rather than named.**  It is
`Fermat.IsWeierstrassModel ab E` with its two abbreviations
(`weierstrassAffine`, `weierstrassAffineStr`) unfolded.  That relation lives
in `X0.lean`, which imports this module, so naming it here would be
circular; it is definitionally this term, so `X0.lean` consumes the
conclusion by `exact` with no transport lemma.  This is the same device, and
the same spelling, as the forward theorem above.

**The cut, and the two ingredients.**  `A` is a proper, smooth,
geometrically connected curve over `ℚ` — properness, smoothness and
geometric connectedness are fields of `AbelianSchemeStruct`, and
`SmoothOfRelativeDimension 1` is what makes it a curve rather than an
abelian variety of higher dimension — carrying the rational point
`ab.zero (𝟙 (Spec ℚ))`.  So:

* `exists_weierstrassModel_of_ellipticScheme` is **Riemann–Roch**: the
  linear system `|3·[O]|` embeds `A` in `ℙ²` as a Weierstrass cubic, and the
  complement of `O` is `Spec ℚ[E]`.  (PROVEN 2026-07-27 from three leaves —
  affineness of the complement, Riemann–Roch proper, and `Δ ≠ 0`; see the
  subsection heading immediately before it.)
* `exists_geomFibreAddEquiv_of_weierstrassModel` is **rigidity**: a group
  law on a genus-one curve is determined by its identity section, so the
  functor-of-points law `ab` and the chord–tangent law on `E` — which have
  the SAME identity, because the model conjunct's `range_eq` forces the
  removed point to be the range of `ab.zero` — agree on `ℚ̄`-points.  Galois
  equivariance is then automatic, exactly as in the forward direction:
  `galSMul` is precomposition with `Spec σ` (`galSMul_def`, which is `rfl`),
  and under the coordinate description that is the coordinatewise action of
  `σ`, i.e. `WeierstrassCurve.Affine.Point.map`.

The two are separated because the difficulties are unrelated and neither is
available at this pin: the first is a linear-systems argument, the second is
the rigidity theorem that `exists_projGroupLaw_geomFibreAddEquiv`'s audit
already names as absent from mathlib and from `~/cs/FLT`.  Splitting them
means a prover at either one need not carry the other.

**The second is itself now DECOMPOSED and PROVEN** (2026-07-27), along the
axis its own audit named as untried — prove the identification for the
concrete projective model and TRANSPORT it — leaving
`exists_isIso_of_affineChart` (curve geometry: two charts glue) and
`relPointPost_add` (rigidity proper, for arbitrary abelian schemes over
`Spec ℚ`).  See the "Transport along an isomorphism of models" subsection
below. -/

/-! #### The three leaves of `exists_weierstrassModel_of_ellipticScheme`

(Cut 2026-07-27.  The node was a single `sorry` before; it is PROVEN below
from the three declarations of this subsection.)

The classical proof (Silverman *AEC* III.3.1, Hartshorne IV.1) runs
`A` ⟶ `A ∖ O` ⟶ `Γ(A ∖ O)` ⟶ Weierstrass equation, and the cut follows
that chain exactly, so that no two leaves share a difficulty:

1. `exists_affineComplement_zeroSection` — **the complement of the zero
   section is AFFINE**.  Pure scheme theory: the zero section of a proper
   morphism is a closed immersion, so its complement is an open subscheme,
   and on a curve the complement of a nonempty closed subset of the
   (irreducible, proper) total space is affine.  No linear system and no
   Weierstrass equation occurs.
2. `exists_weierstrassRingEquiv_of_affineComplement` — **that affine ring
   IS a Weierstrass coordinate ring**.  This is Riemann–Roch itself, and
   it is where all of the mathematical content sits: `L(2[O])` and
   `L(3[O])` supply `x` and `y`, the seven monomials of `L(6[O])` are
   dependent in a `6`-dimensional space, and the resulting relation is a
   Weierstrass cubic after scaling.  Nothing about `Proj`, open immersions
   or discriminants occurs — it is a statement about one commutative ring.
3. `isElliptic_of_isOpenImmersion_coordinateRing` — **`Δ ≠ 0`**.  A
   Weierstrass curve whose affine chart is an open subscheme of a smooth
   `A` is smooth, and a singular Weierstrass curve has a *rational*
   singular point in its affine chart, so `Δ` is a unit.  Pure
   commutative algebra about one `WeierstrassCurve ℚ`.

**Two conjuncts of the goal never reach a leaf.**  The structure-morphism
conjunct is free by `hom_ext_spec_rat` (any two morphisms to `Spec ℚ`
agree), and the transport of the range condition along the ring
isomorphism of leaf 2 is `Scheme.Hom.opensRange_comp_of_isIso`.  That is
why leaf 1 does not have to carry a `ℚ`-algebra structure on its ring and
leaf 2 produces a bare `≃+*` rather than a `≃ₐ[ℚ]`: over `ℚ` the two
notions coincide, because `ℚ` is initial in `CommRing`.
-/

/-- **The complement of the zero section of an elliptic scheme over
`Spec ℚ` is affine** (sorry leaf, introduced 2026-07-27 as leaf 1 of
`exists_weierstrassModel_of_ellipticScheme`).

TRUE and classical.  `ab.proper` makes `f` separated, so the section
`ab.zero (𝟙 (Spec ℚ))` is a *closed* immersion and its range — a single
point, since `Spec ℚ` has one point — is closed; the complement is
therefore an open subscheme of `A`.  That open subscheme is affine
because `A` is a proper, geometrically connected, smooth curve over `ℚ`:
a nonempty effective divisor on such a curve is ample, so the complement
of its support is affine (Hartshorne IV.1, or the Serre criterion applied
to `O(n·[O])`).

**`_hdim` IS LOAD-BEARING** and must NOT be dropped; it is
underscore-prefixed only because the body is `sorry`.  It is what makes
`A` a *curve*.  For an abelian surface the statement is FALSE: the
complement of a point on an abelian surface has the same global sections
as the surface itself (`ℚ`, by properness), so it is not affine — indeed
not even quasi-affine.  Relative dimension one is exactly the hypothesis
that separates the true case from the false one.

**Why `ab` and not merely "proper smooth geometrically connected"**: the
statement has to *name the removed point*, and the only point available
in a bare `AbelianSchemeStruct` is the zero section.  Every field of `ab`
except the two naturality fields is used: `proper` for closedness and for
ampleness, `smooth` and `connected` for the curve being a smooth
geometrically integral curve, and `zero` for the point.

NOT VACUOUS: `exists_ellipticScheme_isWeierstrassModel_of_projModel`
above produces, for every elliptic `E`, an `(A, f, ab)` satisfying every
hypothesis, and its chart witnesses the conclusion with
`R = E.toAffine.CoordinateRing`.  Nor is the conclusion satisfiable by
junk: `IsOpenImmersion` alone would be discharged by the empty scheme,
but the range clause pins the range to the *whole* complement of a point.

WHAT WOULD REFUTE THE "MISSING" DIAGNOSIS: any declaration in
`Mathlib/AlgebraicGeometry/` deducing affineness of an open subscheme
from ampleness of the complementary divisor, or an `IsAffine` instance
for the complement of a section of a proper curve.  Searched 2026-07-27
over `Fermat/`, `.lake/packages/mathlib` and `~/cs/FLT`: the pin has
`Mathlib/AlgebraicGeometry/QuasiAffine.lean` and
`Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`, but no ampleness
of divisors, no `Serre criterion`, and no genus. -/
theorem exists_affineComplement_zeroSection {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (_hdim : SmoothOfRelativeDimension 1 f) :
    ∃ (R : Type) (_ : CommRing R) (ι : Spec (CommRingCat.of R) ⟶ A),
      IsOpenImmersion ι ∧
        Set.range ι.base =
          (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ :=
  sorry

/-- **The affine complement of the zero section is a Weierstrass
coordinate ring** (sorry leaf, introduced 2026-07-27 as leaf 2 of
`exists_weierstrassModel_of_ellipticScheme`).  **This leaf IS
Riemann–Roch**; the other two carry none of it.

TRUE — Silverman *AEC* III.3.1.  `A` is a smooth proper geometrically
connected curve over `ℚ` carrying a group-scheme structure, hence has
trivial tangent bundle, hence arithmetic genus one; `O` is the rational
point `ab.zero (𝟙 (Spec ℚ))`.  Riemann–Roch on a genus-one curve gives
`dim L(n[O]) = n` for `n ≥ 1`, so there are `x ∈ L(2[O]) ∖ L([O])` and
`y ∈ L(3[O]) ∖ L(2[O])`; the seven elements
`1, x, y, x², xy, y², x³` lie in the six-dimensional `L(6[O])` and so
satisfy a linear relation, in which `y²` and `x³` occur with nonzero
coefficients (they are the only two of pole order exactly six).  Scaling
`x, y` makes those coefficients `1` and `−1`, and the relation becomes
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.  Finally `ℚ[x, y]` exhausts
`R = Γ(A ∖ O)` because `⋃ₙ L(n[O]) = R` and `L(n[O])` is spanned by the
monomials `xⁱyʲ` of pole order `≤ n`, and the kernel of
`ℚ[X, Y] ↠ R` is exactly the Weierstrass ideal because both quotients are
one-dimensional domains and the Weierstrass ideal is prime.  That
quotient is mathlib's `WeierstrassCurve.Affine.CoordinateRing`, which is
`AdjoinRoot E.toAffine.polynomial`.

**Genus one is a STEP OF THE PROOF, not a missing hypothesis.**  An
auditor looking for where the genus enters should look at `ab`: a smooth
proper geometrically connected curve carrying a group law has trivial
canonical bundle, hence genus one.  There is no genus in the pin to state
it with, and none is needed.

**`_hopen` and `_hrange` ARE LOAD-BEARING**, and the leaf is FALSE
without them; they are underscore-prefixed only because the body is
`sorry`.  Dropped, `R` would be an arbitrary commutative ring — take
`R = ℚ`, which admits no ring isomorphism to any
`E.toAffine.CoordinateRing` (the latter is never a field: it is a
one-dimensional domain).  `_hrange` in particular is what forces the
removed point to be a *single rational* point, which is what makes the
linear systems `L(n[O])` available; without it `ι` could be a chart
missing a divisor of higher degree and the pole-order filtration would
have the wrong dimensions.

**`_hdim` IS LOAD-BEARING** for the same reason as in leaf 1: without it
`A` is an abelian scheme of arbitrary relative dimension.

NOT VACUOUS: instantiate at the `(A, f, ab, ι)` produced by
`exists_ellipticScheme_isWeierstrassModel_of_projModel` and
`exists_affineChart_projModel`, where the conclusion holds with the
identity isomorphism.

WHAT WOULD REFUTE THE "MISSING" DIAGNOSIS: a Riemann–Roch theorem, a
genus, or a theory of divisors/linear systems on a relative curve, in
`Fermat/`, `.lake/packages/mathlib` or `~/cs/FLT`.  Searched 2026-07-27:
`Mathlib/AlgebraicGeometry/` contains no `RiemannRoch`, no `genus` and no
`arithmeticGenus`; its only divisor-adjacent files are
`AlgebraicCycle/Basic.lean` and `OrderOfVanishing.lean`, neither of which
computes a cohomology dimension.  So this leaf is a genuine theory
build — see the module docstring's note that a theory build is authorized
at this node. -/
theorem exists_weierstrassRingEquiv_of_affineComplement {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (_hdim : SmoothOfRelativeDimension 1 f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ A)
    (_hopen : IsOpenImmersion ι)
    (_hrange : Set.range ι.base =
      (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ) :
    ∃ E : WeierstrassCurve ℚ, Nonempty (R ≃+* E.toAffine.CoordinateRing) :=
  sorry

/-- **A Weierstrass curve whose affine chart is an open subscheme of a
smooth relative curve is elliptic** (sorry leaf, introduced 2026-07-27 as
leaf 3 of `exists_weierstrassModel_of_ellipticScheme`).

TRUE, and it is pure commutative algebra once the hypotheses are
unwound.  `ι` is an open immersion, hence smooth of relative dimension
`0`, so `ι ≫ f` is smooth of relative dimension `1`; and `ι ≫ f` IS
`Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing))`,
by `hom_ext_spec_rat` and nothing else.  So the first move of the proof
is to reduce to: *`E.toAffine.CoordinateRing` is a smooth `ℚ`-algebra
implies `IsUnit E.Δ`*.

For that, argue contrapositively: if `Δ = 0` then the affine Weierstrass
curve is singular, and — this is the part worth stating, because it is
what makes the argument work over `ℚ` rather than only over `ℚ̄` — its
singular point is *rational* (Silverman *AEC* III.1.4: solving the two
partial derivatives for a Weierstrass equation gives coordinates in the
base field, in char `0` by completing the square and the cube).  A
rational singular point of the affine chart is a `ℚ`-point at which the
Jacobian criterion fails, contradicting smoothness.  Note the singular
point of a singular Weierstrass curve always lies in the *affine* chart —
`[0 : 1 : 0]` is nonsingular for every Weierstrass equation — so nothing
is lost by working with the coordinate ring.

`jacobianSpan_eq_top` above is this implication in the other direction
(`IsElliptic → Jacobian span is everything`); its proof is a good model,
and `Δ_mem_jacobianSpan` — `Δ` lies in the Jacobian ideal — is very
likely the reusable half, since a failure of smoothness at a rational
point is exactly a maximal ideal containing the Jacobian ideal.

**`ab` IS DELIBERATELY ABSENT.**  This leaf needs no group law: relative
dimension one and the open immersion are the whole input.  Keeping `ab`
out makes it attackable by someone who knows nothing about abelian
schemes, which is the point of separating it from leaf 2.

**`_hdim` and `_hopen` ARE LOAD-BEARING** and the leaf is FALSE without
either; they are underscore-prefixed only because the body is `sorry`.
Drop `_hopen` and `ι` may be a constant morphism into a smooth `A` from
the chart of a nodal cubic (`Δ = 0`), so the conclusion fails.  Drop
`_hdim` and `f` need not be smooth at all, so nothing constrains `E`.

NOT VACUOUS: `exists_affineChart_projInfty` supplies, for every elliptic
`E`, an `(A, f, ι)` satisfying every hypothesis. -/
theorem isElliptic_of_isOpenImmersion_coordinateRing {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of ℚ)} (_hdim : SmoothOfRelativeDimension 1 f)
    (E : WeierstrassCurve ℚ)
    (ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ A)
    (_hopen : IsOpenImmersion ι) :
    E.IsElliptic :=
  sorry

/-- **An elliptic scheme over `Spec ℚ` has a Weierstrass model** (PROVEN
2026-07-27 from the three leaves above; a single `sorry` node before
that): the coordinate half of the reverse bridge.

TRUE, and it is Riemann–Roch.  `ab` makes `f` proper, smooth and
geometrically connected (three of its fields), `hdim` makes the fibre a
curve, and `ab.zero (𝟙 (Spec ℚ))` is a rational point on it.  A smooth
proper geometrically connected curve over a field with a rational point `O`
and arithmetic genus one is a Weierstrass cubic: the complete linear system
`|3·[O]|` is very ample of degree three and embeds it in `ℙ²` with image
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³`, `O ↦ [0 : 1 : 0]`.
Removing `O` leaves the affine chart `Z ≠ 0`, which is
`Spec ℚ[X, Y]/(Y² + a₁XY + a₃Y − X³ − a₂X² − a₄X − a₆)` — mathlib's
`WeierstrassCurve.Affine.CoordinateRing` — and the embedding is a morphism
over `Spec ℚ`, which is the middle conjunct.  `E.IsElliptic` follows because
a singular Weierstrass curve has a singular affine chart, and an open
subscheme of the smooth `A` is smooth.

**`hdim` IS LOAD-BEARING** and must NOT be dropped.  Without it `A` is an
abelian scheme of arbitrary relative dimension, and an abelian surface has
no Weierstrass model at all — the statement would be false, not merely
unprovable.  It is consumed by leaves 1, 2 and 3 alike.

**Genus one is not a hypothesis and does not need to be**: a smooth proper
geometrically connected curve carrying a group-scheme structure has trivial
tangent bundle, hence genus one.  That is a step of leaf 2, not a missing
pin — an auditor looking for the genus should look there.

NOT VACUOUS: `exists_ellipticScheme_isWeierstrassModel_of_projModel` above
produces, for every elliptic `E`, an `(A, f, ab)` satisfying every
hypothesis, so the hypothesis set is inhabited by the whole of `X_0`'s
supply of elliptic schemes.  Nor is it satisfiable by junk: `range_eq` pins
the range of `ι` to the complement of the zero section, so `ι` cannot be a
chart of some unrelated curve.

**How the assembly works**, since none of it is Riemann–Roch: leaf 1 gives
a bare commutative ring `R` and an open immersion `Spec R ↪ A` onto the
complement of the zero section; leaf 2 replaces `R` by
`E.toAffine.CoordinateRing`, and `Spec` of that ring isomorphism is an
isomorphism of schemes, so composing it with `ι` keeps the range
(`Scheme.Hom.opensRange_comp_of_isIso`) and keeps the open immersion.
Leaf 3 is then applied to the *composite*, which is exactly the chart whose
smoothness forces `Δ ≠ 0`.  The structure-morphism conjunct is free by
`hom_ext_spec_rat`: any two morphisms to `Spec ℚ` agree, which is why no
leaf has to carry a `ℚ`-algebra structure. -/
theorem exists_weierstrassModel_of_ellipticScheme {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f) :
    ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic),
      ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ A,
        IsOpenImmersion ι ∧
          ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)) ∧
          Set.range ι.base =
            (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ := by
  classical
  obtain ⟨R, _, ι, hopen, hrange⟩ := exists_affineComplement_zeroSection ab hdim
  obtain ⟨E, ⟨e⟩⟩ := exists_weierstrassRingEquiv_of_affineComplement ab hdim R ι hopen hrange
  have hE : E.IsElliptic :=
    isElliptic_of_isOpenImmersion_coordinateRing hdim E
      (Spec.map e.toCommRingCatIso.hom ≫ ι) inferInstance
  refine ⟨E, hE, Spec.map e.toCommRingCatIso.hom ≫ ι, inferInstance,
    hom_ext_spec_rat _ _, ?_⟩
  rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.coe_opensRange]
  exact hrange

/-! #### Transport along an isomorphism of models

`exists_geomFibreAddEquiv_of_weierstrassModel` below is PROVEN from the
material in this subsection, along the route its own audit named as the one
never tried: prove the identification for the CONCRETE projective model —
where it is `exists_projGeomFibreAddEquiv`, already available — and
transport it along an isomorphism `proj E ≅ A`.

**The transport is formal; only two things are not.**  Postcomposition with
a morphism over the base is a map of relative points (`relPointPost`), it
commutes with `RelPoint.pre` by associativity alone (`relPointPost_pre`),
and `galSMul` IS `RelPoint.pre` (`AbelianSchemeStruct.galSMul_def` is
`rfl`) — so Galois equivariance costs one lemma with a one-line proof, and
this is the same observation that discharged the generator's Galois
stability in `X0.lean`.  What is genuinely open is

* `exists_isIso_of_affineChart` — that the two charts glue to an
  isomorphism of the proper models, and
* `relPointPost_add` — that an isomorphism carrying zero to zero is a
  homomorphism, i.e. the RIGIDITY theorem.

The third input, `hom_specRat_eq_of_range_eq`, is PROVEN here: it is what
turns "the isomorphism matches the two charts" into "it matches the two
zero SECTIONS", which is the hypothesis rigidity consumes. -/

section Transport

universe u

/-- **Postcomposition of a relative point with a morphism over the base**
(PROVEN — a definition).

If `u : A ⟶ B` satisfies `u ≫ fB = fA` then `x ↦ x ≫ u` carries
`T`-points of `A` over `g` to `T`-points of `B` over `g`.  This is the map
along which the whole reverse bridge is transported. -/
def relPointPost {A B S : Scheme.{u}} {fA : A ⟶ S} {fB : B ⟶ S} (u : A ⟶ B)
    (hu : u ≫ fB = fA) {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint fA g) : RelPoint fB g :=
  ⟨x.1 ≫ u, by rw [Category.assoc, hu, x.2]⟩

/-- The underlying morphism of `relPointPost` (PROVEN, definitional). -/
@[simp] theorem relPointPost_val {A B S : Scheme.{u}} {fA : A ⟶ S} {fB : B ⟶ S} (u : A ⟶ B)
    (hu : u ≫ fB = fA) {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint fA g) :
    (relPointPost u hu x).1 = x.1 ≫ u := rfl

/-- **Postcomposition commutes with precomposition** (PROVEN — associativity
of composition and nothing else).

This is the entire content of the Galois-equivariance half of the reverse
bridge: `AbelianSchemeStruct.galSMul` is `RelPoint.pre (specGal σ)` by
definition, so a transported equivalence is automatically equivariant. -/
theorem relPointPost_pre {A B S : Scheme.{u}} {fA : A ⟶ S} {fB : B ⟶ S} (u : A ⟶ B)
    (hu : u ≫ fB = fA) {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (x : RelPoint fA g) :
    relPointPost u hu (RelPoint.pre h hg x) = RelPoint.pre h hg (relPointPost u hu x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- **Postcomposition with an ISOMORPHISM over the base is a bijection of
relative points** (PROVEN — the inverse is postcomposition with `inv u`). -/
noncomputable def relPointPostEquiv {A B S : Scheme.{u}} {fA : A ⟶ S} {fB : B ⟶ S} (u : A ⟶ B)
    [IsIso u] (hu : u ≫ fB = fA) {T : Scheme.{u}} {g : T ⟶ S} :
    RelPoint fA g ≃ RelPoint fB g where
  toFun := relPointPost u hu
  invFun := relPointPost (inv u) (by rw [← hu, IsIso.inv_hom_id_assoc])
  left_inv _ := Subtype.ext (by simp [relPointPost])
  right_inv _ := Subtype.ext (by simp [relPointPost])

/-- **A field has at most one ring homomorphism to `ℚ`** (PROVEN).

`ℚ` is the prime field of characteristic zero, so a ring map `φ : k → ℚ`
out of a field is injective, forces `CharZero k`, and is inverse to
`algebraMap ℚ k`: `φ ∘ algebraMap ℚ k` is a ring endomorphism of `ℚ`,
hence the identity (`Subsingleton (ℚ →+* ℚ)`), and injectivity of `φ`
upgrades that to `algebraMap ℚ k ∘ φ = id`.  Two such `φ`, `ψ` are then
both the inverse of the same map, hence equal.

Note that no hypothesis relating `φ` to `ψ` is needed — existence of ONE
such map already pins `k ≅ ℚ`. -/
theorem subsingleton_ringHom_rat {k : Type*} [Field k] : Subsingleton (k →+* ℚ) := by
  refine ⟨fun φ ψ => ?_⟩
  haveI : CharZero k := RingHom.charZero φ
  have hψ : ψ.comp (algebraMap ℚ k) = RingHom.id ℚ := Subsingleton.elim _ _
  have hφ : φ.comp (algebraMap ℚ k) = RingHom.id ℚ := Subsingleton.elim _ _
  refine RingHom.ext fun a => ?_
  have hround : algebraMap ℚ k (φ a) = a :=
    φ.injective (congrArg (fun g : ℚ →+* ℚ => g (φ a)) hφ)
  calc φ a = ψ (algebraMap ℚ k (φ a)) :=
        (congrArg (fun g : ℚ →+* ℚ => g (φ a)) hψ).symm
    _ = ψ a := by rw [hround]

/-- **A `ℚ`-point of a scheme is determined by its image point** (PROVEN).

Two morphisms `Spec ℚ ⟶ A` with the same set-theoretic range are equal.
By `Scheme.SpecToEquivOfField` such a morphism is a pair (a point `x` of
`A`, a ring map `κ(x) ⟶ ℚ`); `Spec ℚ` is a one-point space, so equal
ranges give equal points, and `subsingleton_ringHom_rat` gives equal ring
maps for free — `κ(x)` is a field, so it admits at most one map to `ℚ`.

**No section hypothesis is needed**, which is worth noticing: the naive
statement of this lemma carries `s ≫ f = 𝟙` and `t ≫ f = 𝟙` and proves
`κ(x) ≅ ℚ` from them, but the isomorphism is already forced by the mere
existence of `κ(x) ⟶ ℚ`.

NOT VACUOUS, and it is the load-bearing step of the transport: the
extension lemma below matches the two affine CHARTS, and what rigidity
consumes is that the two ZERO SECTIONS match.  The range chase in
`exists_geomFibreAddEquiv_of_weierstrassModel` turns the first into an
equality of ranges of the removed points, and this lemma is what upgrades
that to an equality of morphisms. -/
theorem hom_specRat_eq_of_range_eq {A : Scheme.{0}}
    (s t : Spec (CommRingCat.of ℚ) ⟶ A)
    (h : Set.range s.base = Set.range t.base) : s = t := by
  have hpt : s.base (IsLocalRing.closedPoint ℚ) = t.base (IsLocalRing.closedPoint ℚ) := by
    obtain ⟨y, hy⟩ : s.base (IsLocalRing.closedPoint ℚ) ∈ Set.range t.base := by
      rw [← h]; exact Set.mem_range_self _
    rw [← hy, Subsingleton.elim y (IsLocalRing.closedPoint ℚ)]
  apply (Scheme.SpecToEquivOfField ℚ A).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  exact ⟨hpt, CommRingCat.hom_ext (@Subsingleton.elim _ subsingleton_ringHom_rat _ _)⟩

/-- **RIGIDITY: a morphism of abelian schemes over `Spec ℚ` carrying zero
to zero is a homomorphism** (sorry node, introduced 2026-07-27).

TRUE — this is Mumford, *Abelian Varieties* §4, Cor. 1 (the corollary of
the rigidity lemma), and it is the ONLY genuinely deep input of the
reverse bridge that is not curve geometry.  `abA` and `abB` make `fA` and
`fB` proper, smooth and geometrically connected, `hu` makes `u` a morphism
over the base and `hzero` makes it carry the zero section to the zero
section; the conclusion is additivity of the induced map on `T`-points for
EVERY test scheme `T`, which by Yoneda is exactly "u is a homomorphism of
group schemes".

**Only the zero section over the base itself is hypothesised**, and that
is not a weakening: `AbelianSchemeStruct.pre_zero` gives
`(ab.zero g).1 = g ≫ (ab.zero (𝟙 S)).1` for every base point `g`, so
`hzero` at `𝟙 (Spec ℚ)` already determines the zero section everywhere.

## WHAT IS AVAILABLE AT THIS PIN — the previous verdict was too pessimistic

The audit on `exists_projGroupLaw_geomFibreAddEquiv` records "the rigidity
theorem is in neither mathlib nor `~/cs/FLT`".  That is true of the theorem
and FALSE of the argument, which matters more.  `Mathlib/AlgebraicGeometry/`
`Group/Abelian.lean` (Andrew Yang, Christian Merten) proves
`isCommMonObj_of_isProper_of_geometricallyIntegral` — *a proper
geometrically integral group scheme over a field is commutative*, Stacks
tag `0BFD` — and its proof IS the rigidity argument, run on the commutator
map `γ : (x, y) ↦ xyx⁻¹y⁻¹` instead of on the defect map.  The reusable
pieces it exercises, all at our pin, are

* `subsingleton_image_closure_of_finite_of_isPreirreducible` — the step
  "the image of an irreducible fibre is finite, hence a point";
* `exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage` —
  Zariski's main theorem in the form the argument needs;
* `ext_of_apply_eq`, `ext_of_apply_closedPoint_eq`, `pointEquivClosedPoint`
  and `pointOfClosedPoint` — the reduction to closed points.

So the shape of the intended proof is: apply the same template to
`δ : (x, y) ↦ u(x + y) - u(x) - u(y) : A ×_S A ⟶ B`, which by `hzero` is
zero on `{0} × A` and on `A × {0}`, and conclude `δ = 0`.

**The one real obstruction is presentational, not mathematical**: mathlib
states this for `GrpObj (G : Over (Spec K))` in a cartesian monoidal
category, while `AbelianSchemeStruct` is the functor-of-points
presentation.  `AbelianSchemeStruct.ofMorphisms` above already goes one way
between morphism-level and point-level data, so the bridge to build is
`AbelianSchemeStruct f → GrpObj (Over.mk f)`; that, and adding
`public import Mathlib.AlgebraicGeometry.Group.Abelian`, is what a prover
at this leaf should cost.

WHAT WOULD REFUTE THE "OPEN" DIAGNOSIS: a declaration anywhere stating
that a base-point-preserving morphism of abelian schemes (or of proper
geometrically integral group schemes) is a group homomorphism.  Searched
2026-07-27 over `Fermat/`, `.lake/packages/mathlib` and `~/cs/FLT`: the
`0BFD` proof above is the closest, and it concludes commutativity of ONE
group scheme, not functoriality between two.

NOT VACUOUS: dropping `hzero` makes the statement FALSE — translation by a
nonzero rational point of `A` is an isomorphism over `Spec ℚ` and is not
additive — and it is exactly `hzero` that the range chase in the consumer
works to establish. -/
theorem relPointPost_add {A B : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of ℚ)}
    {fB : B ⟶ Spec (CommRingCat.of ℚ)} (abA : AbelianSchemeStruct fA)
    (abB : AbelianSchemeStruct fB) (u : A ⟶ B) (hu : u ≫ fB = fA)
    (hzero : (abA.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1 ≫ u
      = (abB.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1)
    {T : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of ℚ)} (x y : RelPoint fA g) :
    relPointPost u hu (abA.add x y)
      = abB.add (relPointPost u hu x) (relPointPost u hu y) :=
  sorry

/-- **Two Weierstrass charts of the same affine curve glue to an
isomorphism of the proper models** (sorry node, introduced 2026-07-27).

TRUE, and it is the classical fact that a smooth proper curve is
determined by any dense open of it.  `ι₀` and `ι` are open immersions of
the SAME affine scheme `Spec ℚ[E]` into `proj E` and into `A`, both over
`Spec ℚ`, and each range is the complement of the range of a section — a
single rational point.  So `ι₀` and `ι` identify dense opens of two proper
smooth geometrically connected `ℚ`-curves (`proj E` by
`smoothOfRelativeDimension_projToSpec`, `isProper_projToSpec` and
`geometricallyConnected_projToSpec`; `A` by three fields of `ab`), and the
resulting birational map extends.

**The intended proof, and it is two applications of one criterion.**  The
local ring of `proj E` at the removed point is a DVR — the curve is
regular of dimension one — so `ValuativeCriterion.Existence` for the proper
`f : A ⟶ Spec ℚ` extends `ι₀⁻¹ ≫ ι` across that point to `u : proj E ⟶ A`;
symmetrically the inverse extends to `v : A ⟶ proj E`; and `u ≫ v` and
`v ≫ u` agree with the identity on a dense open of a reduced separated
scheme, hence are the identity.  The pin's entry points are
`AlgebraicGeometry.ValuativeCriterion`, `IsProper.eq_valuativeCriterion`
and `IsSeparated.valuativeCriterion` in
`Mathlib/AlgebraicGeometry/ValuativeCriterion.lean`, together with
`Mathlib/AlgebraicGeometry/Birational/` and
`Mathlib/AlgebraicGeometry/RationalMap.lean`.

**`ab` IS LOAD-BEARING** even though it appears only inside `_hrange`: it
is what makes `A` proper and separated, and without properness there is no
extension and without separatedness no uniqueness.  A prover must not
weaken it to a bare scheme.

**Both range hypotheses are LOAD-BEARING.**  Without them `ι₀` and `ι`
would be arbitrary open immersions — possibly of a proper subset of the
complement of a point — and the extension would not exist.  It is the two
`ᶜ`s that make the complements single points, which is what puts the
extension problem at a DVR.

WHAT WOULD REFUTE THE "OPEN" DIAGNOSIS: a declaration anywhere producing
an isomorphism of proper schemes from an isomorphism of dense opens, or
identifying a smooth proper curve with the proper model of its function
field.  Searched 2026-07-27 over `Fermat/`, `.lake/packages/mathlib` and
`~/cs/FLT`: mathlib has the valuative criterion and a birational-geometry
subtree but no proper-model theorem for curves.

NOT VACUOUS: the conclusion pins `u` to restrict to the given
identification of charts (`ι₀ ≫ u = ι`), so it cannot be discharged by
some unrelated automorphism of the model. -/
theorem exists_isIso_of_affineChart (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (ι₀ : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶
      _root_.WeierstrassCurve.Projective.proj E)
    (ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ A)
    (_h₀ : IsOpenImmersion ι₀) (_h₁ : IsOpenImmersion ι)
    (_hstr₀ : ι₀ ≫ _root_.WeierstrassCurve.Projective.projToSpec E =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)))
    (_hstr : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)))
    (_hrange₀ : Set.range ι₀.base = (Set.range ((projGroupLaw E).toAbelianSchemeStruct.zero
      (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ)
    (_hrange : Set.range ι.base =
      (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ) :
    ∃ u : _root_.WeierstrassCurve.Projective.proj E ⟶ A,
      IsIso u ∧ u ≫ f = _root_.WeierstrassCurve.Projective.projToSpec E ∧ ι₀ ≫ u = ι :=
  sorry

end Transport

/-- **A Weierstrass model of an elliptic scheme identifies the geometric
fibre with `E(ℚ̄)`, Galois-equivariantly** (PROVEN 2026-07-27 from
`exists_isIso_of_affineChart`, `relPointPost_add` and
`hom_specRat_eq_of_range_eq`; formerly a sorry node): the rigidity half of
the reverse bridge.

TRUE, and it is the **rigidity theorem** — a group law on a genus-one curve
is determined by its identity section.  The model hypothesis gives an open
immersion `Spec ℚ[E] ↪ A` over `Spec ℚ` whose range is the complement of the
zero section.  Over `ℚ̄` that is a bijection of `ℚ̄`-points off `O`, and the
single missing point on each side is the origin, so it extends to a
bijection `E(ℚ̄) ≃ A(ℚ̄)` matching the two identities.  Rigidity then makes it
a group isomorphism: both the chord–tangent law and `ab`'s functor-of-points
law are group laws on the same genus-one curve with the same identity, hence
equal.  Galois equivariance is free — `galSMul` is precomposition with
`Spec σ` (`AbelianSchemeStruct.galSMul_def`, which is `rfl`), and under the
coordinate description of `ℚ̄`-points that is the coordinatewise action of
`σ`, which is `WeierstrassCurve.Affine.Point.map`.

**`hmodel` IS LOAD-BEARING and the leaf is FALSE without it.**  Dropped, the
statement would assert a Galois-equivariant `≃+` between `E(ℚ̄)` and the
geometric fibre of an *arbitrary* elliptic scheme for an *arbitrary* `E` —
take `A` the projective model of a curve of rank `0` and `E` one of rank
`1` and there is no such isomorphism at all.  (It is no longer
underscore-prefixed: the proof below consumes all three of its conjuncts.)

**The `range_eq` conjunct of `hmodel` is the load-bearing part of it**, and
an auditor should check that a weakening does not quietly drop it: it is
what forces the point removed by the chart to BE the identity of `ab`, and
that is the hypothesis rigidity consumes.  With only "some open immersion"
the two group laws would differ by a translation and the conclusion would be
false as stated (it would hold only after composing with one).

## THE CUT (2026-07-27) — the untried axis, taken

The previous verdict here was IRREDUCIBLE, on the grounds that the rigidity
theorem is in neither mathlib nor `~/cs/FLT`, and it named its own escape:
the axis it ranged over was *theorems about morphisms of abelian schemes*,
and it did NOT cover proving the leaf for the CONCRETE projective model
first and transporting along the chart isomorphism.  That is the route
taken here, and it decomposes the leaf into three:

* `exists_isIso_of_affineChart` — the two affine charts glue to an
  isomorphism `proj E ≅ A` over `Spec ℚ` (valuative criterion at the one
  removed point; OPEN);
* `hom_specRat_eq_of_range_eq` — a `ℚ`-point is determined by its image, so
  matching charts force matching zero SECTIONS (PROVEN here);
* `relPointPost_add` — rigidity: a base-point-preserving morphism of
  abelian schemes is a homomorphism (OPEN, but see its docstring: mathlib's
  `0BFD` proof is the same argument and is reusable).

The Galois clause survives the cut for free, for the structural reason the
consumer in `X0.lean` already exploits: `galSMul` IS precomposition, so it
commutes with the postcomposition the transport is made of
(`relPointPost_pre`, whose proof is `Category.assoc`).

Note what the cut BUYS beyond decomposition: the rigidity obligation is now
stated for arbitrary abelian schemes over `Spec ℚ`, with no elliptic curve,
no `Proj` and no chart in sight, so it can be attacked — and reused —
independently of everything else in this module. -/
theorem exists_geomFibreAddEquiv_of_weierstrassModel (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (hmodel : ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ A,
      IsOpenImmersion ι ∧
        ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)) ∧
        Set.range ι.base =
          (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ) :
    letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
    ∃ e : (E⁄(AlgebraicClosure ℚ)).Point ≃+
        GeomFibrePt f (𝟙 (Spec (CommRingCat.of ℚ))),
      ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
        e (WeierstrassCurve.Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
          = ab.galSMul (𝟙 (Spec (CommRingCat.of ℚ))) σ (e x) := by
  classical
  obtain ⟨ι, hopen, hstr, hrange⟩ := hmodel
  obtain ⟨ι₀, hopen₀, hstr₀, hrange₀⟩ := exists_affineChart_projModel E (projGroupLaw E)
  obtain ⟨u, huiso, huf, huι⟩ :=
    exists_isIso_of_affineChart E ab ι₀ ι hopen₀ hopen hstr₀ hstr hrange₀ hrange
  haveI := huiso
  -- `u` is a homeomorphism, so it carries the complement of the projective model's
  -- zero section onto the complement of `ab`'s — hence one removed point onto the other.
  have hbij : Function.Bijective
      (u.base : _root_.WeierstrassCurve.Projective.proj E → A) :=
    (Scheme.homeoOfIso (asIso u)).bijective
  have hzrange : Set.range ((((projGroupLaw E).toAbelianSchemeStruct.zero
        (𝟙 (Spec (CommRingCat.of ℚ)))).1 ≫ u).base)
      = Set.range ((ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base) := by
    have h1 : Set.range ((ι₀ ≫ u).base) = Set.range ι.base := by rw [huι]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at h1 ⊢
    rw [hrange₀, hrange, Set.image_compl_eq hbij] at h1
    exact compl_injective h1
  have hzsec : (((projGroupLaw E).toAbelianSchemeStruct.zero
      (𝟙 (Spec (CommRingCat.of ℚ)))).1 ≫ u) = (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1 :=
    hom_specRat_eq_of_range_eq _ _ hzrange
  letI := (projGroupLaw E).toAbelianSchemeStruct.addCommGroup
    (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 (Spec (CommRingCat.of ℚ)))
  obtain ⟨e₀, he₀⟩ := exists_projGeomFibreAddEquiv E
  refine ⟨e₀.trans { relPointPostEquiv u huf with
      map_add' := fun x y =>
        relPointPost_add (projGroupLaw E).toAbelianSchemeStruct ab u huf hzsec x y }, ?_⟩
  intro σ x
  show relPointPost u huf (e₀ (WeierstrassCurve.Affine.Point.map
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x))
    = ab.galSMul (𝟙 (Spec (CommRingCat.of ℚ))) σ (relPointPost u huf (e₀ x))
  rw [he₀ σ x]
  exact relPointPost_pre u huf (specGal σ)
    (specGal_comp_base (𝟙 (Spec (CommRingCat.of ℚ))) σ) (e₀ x)

/-- **THE REVERSE WEIERSTRASS BRIDGE: every elliptic scheme over `Spec ℚ` is
the Weierstrass model of a curve, compatibly on geometric points** (PROVEN
2026-07-27 from the two declarations above — `exists_weierstrassModel_of_`
`ellipticScheme`, still a leaf, and `exists_geomFibreAddEquiv_of_`
`weierstrassModel`, itself now proven from the transport subsection).

This is the exact converse of
`exists_ellipticScheme_isWeierstrassModel_of_projModel`: there the curve is
given and the scheme produced, here the scheme is given and the curve
produced, and the two conjuncts are the same two conjuncts.  It is the
declaration `X0.lean` was missing.

**How `X0.lean` consumes it.**  Given `d : Gamma0Datum N SpecQ`, apply this
to `d.ab` and `d.relativeDimensionOne`.  The first conjunct is
`Fermat.IsWeierstrassModel d.ab E` with `weierstrassAffine` and
`weierstrassAffineStr` unfolded, so it is accepted by `exact` wherever that
relation is asked for — in particular by `IsJSection.jt_model`, and by the
`jm_classify` field that `exists_weierstrass_jm_of_gamma0Datum`'s docstring
proposes for `IsJMapOn`.  The second conjunct transports the level structure:
`d.cyc.geom_cyclic` supplies a generator of the geometric fibre subgroup, and
`e.symm` carries it to a point of `E(ℚ̄)` of the same order whose
`zmultiples` is Galois-stable, because `RelPoint.LiesIn` is preserved by
precomposition and `galSMul` IS precomposition.

**Neither conjunct mentions `proj` or `projToSpec`**, which is what keeps
`X0.lean`'s `import Fermat.FLT.ModularCurve.EllipticScheme` non-public — see
the subsection docstring, and the module docstring for why that matters. -/
theorem exists_weierstrassModel_geomFibreAddEquiv_of_ellipticScheme {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f) :
    ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic),
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
  obtain ⟨E, hE, hmodel⟩ := exists_weierstrassModel_of_ellipticScheme ab hdim
  haveI := hE
  exact ⟨E, hE, hmodel, exists_geomFibreAddEquiv_of_weierstrassModel E ab hmodel⟩

end Fermat

end

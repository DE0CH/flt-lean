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

`isProper_projToSpec` is PROVEN, and so is
`smoothOfRelativeDimension_projToSpec` apart from ONE named leaf: its `hchart`
step is now fully reduced, and the Jacobian criterion it rests on
(`jacobianSpan_eq_top`, over an arbitrary commutative ring) is proven here.

`projMul_assoc` is PROVEN too, by the density route: mathlib's
`ext_of_fromSpecResidueField_eq` reduces it to associativity at residue fields,
and the two things left are `geometricallyReduced_projToSpec` (a general
`Smooth → GeometricallyReduced` gap in MATHLIB, not elliptic-curve mathematics)
and `projMul_assoc_pt` (associativity of the induced operation on `K`-points,
which is where the Milne I.2.5 content sits).

The open leaves are therefore SIX, and this list is READ OFF the compiler's
`declaration uses 'sorry'` set for this file at the 2026-07-27 release, not
inherited from any side of a merge — several earlier versions of this paragraph
named leaves that had already been closed on a sibling branch:

* `exists_projMul` — the half of the old `exists_projAdd` where all the
  remaining gluing work for the group law lives (`exists_projAdd` itself is
  PROVEN from it and from `projMul_assoc`, see below);
* `geometricallyReduced_projToSpec` and `projMul_assoc_pt` — the two leaves
  `projMul_assoc` now rests on;
* `exists_projGroupLaw_geomFibreAddEquiv` — item 8, see below;
* `isIso_projBaseChangeHom` — all that is left of `hbc`, base change for `Proj`;
* `exists_affineChart_projModel`.

The whole "Dehomogenisation" section is now PROVEN — `exists_projChartRingEquiv`,
`projChart_jacobian_span_eq_top` and
`isStandardSmoothOfRelativeDimension_projChartAway` — and with it
`locally_isStandardSmooth_awayCoord`, the last direct sorry of item 7a.
`prime_projPolynomial` is PROVEN too, so `geometricallyConnected_projToSpec`
now consumes only `isIso_projBaseChangeHom`.  Each declaration carries its own
docstring saying what is missing and where the classical argument is.
**Item 8 was restated on 2026-07-27** and its leaf is now
`exists_projGroupLaw_geomFibreAddEquiv`, which binds the group law
EXISTENTIALLY.  `exists_projGeomFibreAddEquiv` survives under its own name
as a PROVEN consequence, stated about the concrete `projGroupLaw E`.  The
old form quantified over an ARBITRARY `ProjGroupLaw`, which pins nothing
about `m`, and was therefore provable only through the rigidity theorem;
the audit is on `exists_projGroupLaw_geomFibreAddEquiv`.  That leaf also
subsumes `exists_projAdd`.

**The two cuts are NOT yet merged** (reconciliation attempted 2026-07-27; see
the "Relation to `exists_projAdd`" section of that leaf's docstring for the
obstruction that was found and why `_gl₀` therefore stays).

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
* `hbc` is the only remaining leaf of this cluster, and it is now CUT.
  `nonempty_projPullbackIso` is proven from a single geometric leaf,
  `isIso_projBaseChangeHom`.  Base change for `Proj` exists nowhere at this pin, so the
  comparison morphism had to be built: `projBaseChangeGradedHom` (the graded hom),
  `irrelevant_le_map_projBaseChangeGradedHom` (the hypothesis `Proj.map` demands) and
  `projBaseChangeHom` (the pullback lift — free here, because the commuting square lands
  in `Spec ℚ` and `hom_ext_spec_rat` applies) are all PROVEN.  What is left is that that
  morphism is an isomorphism, whose residue is one ring statement:
  `Away 𝒜 s ⊗_ℚ K ≅ Away ℬ (φ s)`.  See its docstring for the checked route.

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

/-- **The chord–tangent multiplication morphism, with the three axioms
that are chart identities** (sorry node — the CONSTRUCTION half of the
old `exists_projAdd`, which is now proven from this together with
`projMul_assoc`).

TRUE and classical.  This leaf owns the gluing and nothing else:
`hcomm`, `hunit` and `hinv` are demanded here because each is an
identity between the *same* polynomial forms that define `m` on a chart,
so whoever writes the charts gets them essentially for free, while
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
      Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
              (Limits.pullback.fst (projToSpec E) (projToSpec E))
              Limits.pullback.condition.symm ≫ m = m ∧
        Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E) ∧
          Limits.pullback.lift (projNeg E) (𝟙 (proj E))
              (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E :=
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

/-- **The projective Weierstrass model is geometrically reduced over `ℚ`**
(sorry node — a small, general, mathlib-shaped gap).

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

## TWO ROUTES

1. *The general one, and the one worth writing*: prove `Smooth f →
   GeometricallyReduced f` in `Fermat/FLT/Mathlib/`.  Base change reduces
   it to: a scheme smooth over a field `K` is reduced.  This is a genuine
   piece of mathlib-facing infrastructure and would be reusable
   immediately — `GeometricallyReduced` already carries the base-change
   instances (`AlgebraicGeometry/Geometrically/Reduced.lean`) that make
   everything downstream of it automatic.
2. *The parochial one*: show directly that `K[X, Y, Z] ⧸ (W)` is a domain
   for every field `K ⊇ ℚ`, i.e. that the Weierstrass cubic is irreducible
   — a cubic that factors has a linear factor, so the curve contains a
   line and is singular, contradicting `Δ ≠ 0`.  This needs, in addition,
   that `Proj` commutes with the base change `ℚ → K`, and that `Proj` of a
   graded domain is reduced; **neither is in the pin either** (there is no
   `IsReduced`/`IsIntegral` result anywhere in
   `AlgebraicGeometry/ProjectiveSpectrum/`).  So route 1 is both more
   general and strictly less work. -/
theorem geometricallyReduced_projToSpec (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    GeometricallyReduced (projToSpec E) :=
  sorry

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

* `GeometricallyReduced (projToSpec E)` — the one open leaf;
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

/-- **Associativity of the operation `m` induces on `K`-points, `K` a
field** (sorry node — this is where ALL the remaining mathematical content
of `projMul_assoc` now sits).

This is the density route's payload, and the restriction to `Spec` of a
FIELD is essential rather than cosmetic: the same statement for an
arbitrary test scheme `T` is `projMul_assoc` itself (take `T` to be the
threefold product and the three projections), so nothing would have been
gained.  What a field buys is that `proj E ×_ℚ Spec K` is a smooth
projective genus-`1` curve over `K` with the rational point
`projInfty E`, i.e. an honest elliptic curve, where mathlib's
`WeierstrassCurve.Affine.Point` supplies a real `AddCommGroup`.

## WHAT IT NEEDS: MILNE I.2.5, AND IT IS UNAVOIDABLE

Over `K̄` the hypotheses say that `projMulPt E m` is a commutative loop
operation with unit `projInfty E` and inverse `projNeg E`.  **A
commutative loop with two-sided unit and inverses need not be
associative** — that is not a gap in the write-up, it is why this leaf is
hard: the conclusion is false for a general SET-level such operation, and
it holds here only because `m` is a MORPHISM OF VARIETIES.

The input that converts algebraicity into associativity is Milne,
*Abelian Varieties* I.2.5: every morphism `E × E → E` of complete
varieties into an abelian variety is `(P, Q) ↦ φ(P) + ψ(Q) + c`.  `hunit`
then forces `ψ = id` and `φ(O) + c = 0`, and `hcomm` forces `φ = id` and
`c = 0`, so `m` *is* the classical group law and associativity is
`add_assoc`.  Note this is the same argument recorded above as settling
FAITHFULNESS; the point of the present cut is that at a field it is no
longer circular — the group law on the target is mathlib's group law on
`E(K̄)`, which exists independently of the scheme-level `m` this cluster
is constructing.

Equivalently, and possibly cheaper in Lean, one may run the argument
through Silverman *AEC* III.4.7 (every morphism of elliptic curves is a
translation composed with an isogeny — proved via `Pic⁰` and Abel–Jacobi)
applied to `P ↦ projMulPt E m P Q` for fixed `Q`, and then pin the
resulting isogeny to `id` by connectedness of the family in `Q`, using
`projMulPt E m P (projInfty E) = P`.  Neither `Pic⁰` for curves nor the
rigidity lemma is in the pin or in `~/cs/FLT`, so either way this leaf
carries a real theory-building obligation and should be dispatched as
such, not as a proof exercise.

## COORDINATE WITH `exists_projGeomFibreAddEquiv`

That sibling leaf (`:583`, its own owner) is the `K̄`-point dictionary
between `RelPoint (projToSpec E)` and `WeierstrassCurve.Affine.Point`,
and it is exactly the interface this leaf wants for its last step.  It is
currently existentially stated, so it cannot be consumed as an API; an
owner taking this leaf should coordinate rather than build a second
dictionary. -/
theorem projMul_assoc_pt (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : Limits.pullback (projToSpec E) (projToSpec E) ⟶ proj E)
    (hcomm : Limits.pullback.lift (Limits.pullback.snd (projToSpec E) (projToSpec E))
      (Limits.pullback.fst (projToSpec E) (projToSpec E))
      Limits.pullback.condition.symm ≫ m = m)
    (hunit : Limits.pullback.lift (projToSpec E ≫ projInfty E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = 𝟙 (proj E))
    (hinv : Limits.pullback.lift (projNeg E) (𝟙 (proj E))
      (hom_ext_spec_rat _ _) ≫ m = projToSpec E ≫ projInfty E)
    (K : CommRingCat.{0}) [Field K] (P Q R : Spec K ⟶ proj E) :
    projMulPt E m (projMulPt E m P Q) R = projMulPt E m P (projMulPt E m Q R) :=
  sorry

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

/-- **Associativity of any commutative unital multiplication with
`projNeg`-inverses on the projective Weierstrass model** (PROVEN from
`geometricallyReduced_projToSpec` and `projMul_assoc_pt` — the ABSTRACT
half of the old `exists_projAdd`).

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

What is left is therefore exactly two things, and they are disjoint:

1. `geometricallyReduced_projToSpec` — a small, general, mathlib-shaped
   gap (see its docstring);
2. `projMul_assoc_pt` — the genuine Milne content, now stated as plain
   associativity of the operation `m` induces on `K`-points. -/
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
  obtain ⟨m, hcomm, hunit, hinv⟩ := exists_projMul E
  exact ⟨m, projMul_assoc E m hcomm hunit hinv, hcomm, hunit, hinv⟩

/-- **The chord–tangent law on the projective Weierstrass model, as
morphisms of schemes** (REDUCED to `exists_projAdd`, not closed) — items 5+6
of the routable specification in `exists_ellipticScheme_of_weierstrass`'s
docstring.

**This declaration carries no `sorry` of its own but is transitively
sorried**, because `exists_projAdd` is proven from `projMul_assoc` (itself
now reduced to `geometricallyReduced_projToSpec` and `projMul_assoc_pt`) and
from the still-open `exists_projMul`.  It is a reduction, not a result; the
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

Everything in this block except `isIso_projBaseChangeHom` is PROVEN.  The block replaces
what used to be a single opaque leaf `nonempty_projPullbackIso` by: the graded base-change
hom, the irrelevant-ideal hypothesis `Proj.map` demands, the assembled comparison morphism,
and the reduction of the leaf to that morphism being an isomorphism.

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

/-- **The comparison morphism is an isomorphism** (sorry leaf) — all that is left of the
`hbc` step of `geometricallyConnected_projToSpec`.

This is the whole geometric content of base change for `Proj`, and it is the ONLY thing
still missing: the graded hom, the irrelevant-ideal hypothesis and the pullback lift above
are all proven, so a successor gets a concrete morphism and has only to show it is an
isomorphism.  It carries no ellipticity: it is pure base change of a graded quotient of a
polynomial ring, true for every Weierstrass curve over every field extension.

## The route, with every named ingredient checked to exist at this pin

Being an isomorphism is local on the target, so work on the standard affine cover.

1. `Proj.affineOpenCoverOfIrrelevantLESpan (projGrading E) f` — already used in this file by
   `smoothOfRelativeDimension_projToSpec`, with `f = X̄, Ȳ, Z̄` — covers `proj E` by the
   charts `D₊(s) ≅ Spec (Away (projGrading E) s)`.  Pulling that cover back along
   `Limits.pullback.fst` covers the pullback, and `Proj.map_preimage_basicOpen`
   (`ProjectiveSpectrum/Functor.lean`) says `projBaseChangeMap ⁻¹ᵁ D₊(s) = D₊(φ s)`
   ON THE NOSE, so the same three elements cover the source compatibly.
2. On the chart over `D₊(s)` the statement becomes the RING statement
   `Away (projGrading E) s ⊗[ℚ] K ≅ Away (projGrading (E_K)) (φ s)`: the degree-zero part
   of a homogeneous localisation commutes with base change.  The comparison map already
   exists — `HomogeneousLocalization.Away.map (g : 𝒜 →+*ᵍ ℬ) (s) : Away 𝒜 s →+* Away ℬ (g s)`
   (`RingTheory/GradedAlgebra/HomogeneousLocalization.lean:724`) — and
   `AlgebraicGeometry.pullbackSpecIso` (`AlgebraicGeometry/Pullbacks.lean:719`) turns the
   scheme-level pullback of affines into `Spec` of a tensor product.  The compatibility of
   `Away.map` with the chart embeddings is `Proj.awayToSection_comp_appLE` and the
   `Spec.map (Away.map …) ≫ awayι` identity at `Functor.lean:188`.
3. So the mathematical residue is exactly: **`Away 𝒜 s ⊗_ℚ K → Away ℬ (φ s)` is bijective**,
   for `𝒜 = projGrading E`, `ℬ = projGrading (E_K)`, `s ∈ {X̄, Ȳ, Z̄}`.  This is elementary
   — degree-zero fractions `a / s ^ n` with `a` homogeneous of degree `n · deg s`, and both
   the numerator space and the relation module base-change freely because `ℚ → K` is flat
   (indeed free) — but it is not in mathlib in any form, so it is a genuine small theory
   build.  `MorphismProperty.isomorphisms Scheme` is the property to feed to the
   affine/local machinery (`HasAffineProperty.iff_of_isAffine` is used this way in
   `ValuativeCriterion.lean:292`).

**What NOT to reuse**: `Proj.pullbackAwayιIso` looks relevant and is not — it compares two
charts of one `Proj`. -/
theorem isIso_projBaseChangeHom : IsIso (projBaseChangeHom E K) := sorry

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

### RECONCILIATION ATTEMPTED 2026-07-27 — BLOCKED, and `_gl₀` therefore STAYS

The two cuts were merged into one tree on this date and the end state above
was attempted.  **It does not compose**, for a structural reason that is
worth recording because it is not visible from either cut alone.

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

**The route that would work**, for whoever takes it: state the clause in a
`hassoc`-FREE form on `exists_projMul`, replacing the `≃+` by a bare
equivalence plus the raw morphism identity

    ∃ eqv : (E⁄(AlgebraicClosure ℚ)).Point ≃ GeomFibrePt (projToSpec E) (𝟙 _),
      (∀ x y, (eqv (x + y)).1 = AbelianSchemeStruct.relPair (eqv x) (eqv y) ≫ m) ∧ …

`relPair` needs only the structure morphism, and `m` is the bare morphism, so
this is expressible without any `AbelianSchemeStruct`.  `exists_projAdd` can
then bundle it, and THIS leaf follows: `toAbelianSchemeStruct_add_val` is
`rfl`, so the `≃+` assembles from the bare `≃` plus that identity once
`hassoc` is in hand.  *Refuting check for the obstruction as stated*: find an
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
two of them live, owned work — free-floating.  The anchor comes out at the
same commit that lands the clause, not before.

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
  complement of `O` is `Spec ℚ[E]`.
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
means a prover at either one need not carry the other. -/

/-- **An elliptic scheme over `Spec ℚ` has a Weierstrass model** (sorry
node, introduced 2026-07-27): the coordinate half of the reverse bridge.

TRUE, and it is Riemann–Roch.  `ab` makes `f` proper, smooth and
geometrically connected (three of its fields), `_hdim` makes the fibre a
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

**`_hdim` IS LOAD-BEARING**; it is underscore-prefixed only because the body
is `sorry`, and it must NOT be dropped.  Without it `A` is an abelian scheme
of arbitrary relative dimension, and an abelian surface has no Weierstrass
model at all — the statement would be false, not merely unprovable.

**Genus one is not a hypothesis and does not need to be**: a smooth proper
geometrically connected curve carrying a group-scheme structure has trivial
tangent bundle, hence genus one.  That is a step of the intended proof, not
a missing pin — an auditor looking for the genus should look there.

NOT VACUOUS: `exists_ellipticScheme_isWeierstrassModel_of_projModel` above
produces, for every elliptic `E`, an `(A, f, ab)` satisfying every
hypothesis, so the hypothesis set is inhabited by the whole of `X_0`'s
supply of elliptic schemes.  Nor is it satisfiable by junk: `range_eq` pins
the range of `ι` to the complement of the zero section, so `ι` cannot be a
chart of some unrelated curve.

WHAT WOULD REFUTE THE "MISSING" DIAGNOSIS: a declaration in
`Mathlib/AlgebraicGeometry/` attaching a Weierstrass equation to a
genus-one curve with a rational point, or any `EllipticCurve`-valued
construction out of a smooth proper relative curve.  Searched 2026-07-27
over `Fermat/`, `.lake/packages/mathlib` and `~/cs/FLT`: mathlib's
elliptic-curve files all START from a `WeierstrassCurve`, and no file in
any of the three mentions an elliptic scheme's Weierstrass presentation. -/
theorem exists_weierstrassModel_of_ellipticScheme {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (_hdim : SmoothOfRelativeDimension 1 f) :
    ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic),
      ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ A,
        IsOpenImmersion ι ∧
          ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ E.toAffine.CoordinateRing)) ∧
          Set.range ι.base =
            (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of ℚ)))).1.base)ᶜ :=
  sorry

/-- **A Weierstrass model of an elliptic scheme identifies the geometric
fibre with `E(ℚ̄)`, Galois-equivariantly** (sorry node, introduced
2026-07-27): the rigidity half of the reverse bridge.

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

**`_hmodel` IS LOAD-BEARING and the leaf is FALSE without it.**  It is
underscore-prefixed only because the body is `sorry`.  Dropped, the
statement would assert a Galois-equivariant `≃+` between `E(ℚ̄)` and the
geometric fibre of an *arbitrary* elliptic scheme for an *arbitrary* `E` —
take `A` the projective model of a curve of rank `0` and `E` one of rank
`1` and there is no such isomorphism at all.

**The `range_eq` conjunct of `_hmodel` is the load-bearing part of it**, and
an auditor should check that a weakening does not quietly drop it: it is
what forces the point removed by the chart to BE the identity of `ab`, and
that is the hypothesis rigidity consumes.  With only "some open immersion"
the two group laws would differ by a translation and the conclusion would be
false as stated (it would hold only after composing with one).

IRREDUCIBLE at this pin in the sense that matters: the rigidity theorem is
in neither mathlib nor `~/cs/FLT` — the same verdict recorded at
`exists_projGroupLaw_geomFibreAddEquiv` above, which is why that leaf was
restated to bind its group law existentially rather than prove rigidity.
**The axis that verdict ranges over**: theorems about morphisms of abelian
schemes.  It does NOT cover the possibility of proving this leaf for the
CONCRETE projective model first and transporting along the chart
isomorphism, which is where an attack should start. -/
theorem exists_geomFibreAddEquiv_of_weierstrassModel (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℚ)} (ab : AbelianSchemeStruct f)
    (_hmodel : ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ A,
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
          = ab.galSMul (𝟙 (Spec (CommRingCat.of ℚ))) σ (e x) :=
  sorry

/-- **THE REVERSE WEIERSTRASS BRIDGE: every elliptic scheme over `Spec ℚ` is
the Weierstrass model of a curve, compatibly on geometric points** (PROVEN
2026-07-27 from the two leaves above).

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

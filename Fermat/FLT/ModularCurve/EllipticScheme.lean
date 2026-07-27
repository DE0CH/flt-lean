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

The open leaves are `exists_projMul`, `projMul_assoc`,
`isProper_projToSpec`,
`smoothOfRelativeDimension_projToSpec`,
`geometricallyConnected_projToSpec` and
`exists_projGeomFibreAddEquiv`; each carries its own docstring saying what
is missing and where the classical argument is.

`nonempty_projGroupLaw` is PROVEN: two of the three data fields of a
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

## The formulas that exist, and the one that does not

`WeierstrassCurve.Projective.addX`/`addY`/`addZ`
(`EllipticCurve/Projective/Formula.lean`) are honest polynomial forms
over an arbitrary `[CommRing R]`, bihomogeneous of bidegree `(2, 2)`:
`addX_smul`/`addY_smul`/`addZ_smul` all read
`add? (u • P) (v • Q) = (u * v) ^ 2 * add? P Q`.  Instantiating
`P = ![X 0, X 1, X 2]`, `Q = ![X 3, X 4, X 5]` in
`MvPolynomial (Fin 6) ℚ` turns them into genuine bihomogeneous
polynomials, which is the form the gluing needs.

**But this is only ONE addition law, and it is very degenerate.**
`addZ_eq'` reads `addZ P Q * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3`
and `addX_eq'` carries the same factor, so the whole triple vanishes
identically on the bidegree-`(1, 1)` locus `x(P) = x(Q)` — which contains
both the diagonal and the antidiagonal (`addXYZ_self P = ![0, 0, 0]`).
By **Bosma–Lenstra** a complete addition law of bidegree `(2, 2)` on a
Weierstrass curve does not exist and exactly TWO are needed to cover
`E × E`; the second one is **absent from this pin and must be written**.

*`dblXYZ` is not the second law and the next owner must not reach for
it*: `dblXYZ_smul` reads `dblXYZ (u • P) = u ^ 4 • dblXYZ P`, i.e. it is
a single-variable form of degree `4` along the diagonal, not a
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
   `_morphismRestrict`, `_resLE` and `_toSpecZero`.
4. Then `Scheme.OpenCover.glueMorphisms` assembles `m`, and `hcomm`,
   `hunit`, `hinv` are checked chart-wise against the same forms
   (`addX`/`addY`/`addZ` are visibly symmetric under swapping `P` and
   `Q` up to the sign that `negY` absorbs).

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

/-- **Associativity of any commutative unital multiplication with
`projNeg`-inverses on the projective Weierstrass model** (sorry node —
the ABSTRACT half of the old `exists_projAdd`).

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
that is a cut-level change and should be reported, not made silently. -/
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
      AbelianSchemeStruct.triAddRight (projToSpec E) m (hom_ext_spec_rat _ _) :=
  sorry

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

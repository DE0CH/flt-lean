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
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.RingHom.StandardSmooth
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

`isProper_projToSpec` and `nonempty_projGroupLaw` are both PROVEN, and so is
`smoothOfRelativeDimension_projToSpec` apart from ONE named leaf: its `hchart`
step is now fully reduced, and the Jacobian criterion it rests on
(`jacobianSpan_eq_top`, over an arbitrary commutative ring) is proven here.

The open leaves are therefore `exists_projAdd` — where all the remaining gluing
work for the group law now lives — `exists_projGeomFibreAddEquiv`,
`locally_isStandardSmooth_awayCoord` (all that is left of item 7a — and what it
wants is a missing piece of MATHLIB, the dehomogenisation isomorphism for a chart
of `Proj` of a polynomial quotient), and the two leaves that
`geometricallyConnected_projToSpec` now consumes.  Each declaration carries its own
docstring saying what is missing and where the classical argument is.

`geometricallyConnected_projToSpec` itself has **no direct sorry** any more.  Of its
three former steps `hbc`/`hne`/`hpre`:

* `hne` is **PROVEN** as `nonempty_proj`, over an arbitrary base field.  The point at
  infinity `[0 : 1 : 0]` is the homogeneous prime `(X̄, Z̄)`; the missing mathlib piece
  was primality of the span of a SUBSET of the variables, which is supplied here by
  `span_X_Z_eq_ker_killXZ` exhibiting `(X, Z)` as a kernel.
* `hpre` is **PROVEN** as `preconnectedSpace_proj` modulo the single leaf
  `prime_projPolynomial`.  The general statement that `Proj` of a graded domain is
  irreducible — also absent from mathlib — is proven here as
  `irreducibleSpace_projectiveSpectrum`.
* `hbc` remains open as `nonempty_projPullbackIso`; it is base change for `Proj`,
  which exists nowhere at this pin, and its docstring records the intended route.

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

/-- **THE RESIDUAL LEAF OF ITEM 7a** — the degree-zero part of the localisation of the
homogeneous coordinate ring at a coordinate is locally standard smooth of relative
dimension `1` over `ℚ`.

Everything else in `smoothOfRelativeDimension_projToSpec` is now proven: the reduction to
the three coordinate charts, the identification of each chart composite with a `Spec.map`
(`awayι_projToSpec_eq_specMap`), the passage to the ring-hom property
(`smoothOfRelativeDimension_specMap_of_locally`), and the Jacobian criterion itself
(`jacobianSpan_eq_top`, supplied here as `hjac` and therefore genuinely consumed).

## What is missing, precisely

ONE thing, and it is missing from mathlib rather than from this development: the
**dehomogenisation isomorphism for a chart of `Proj` of a quotient of a polynomial ring**,

  `(ℚ[X, Y, Z] ⧸ (W))_{(xᵢ)}` in degree `0`  ≃ₐ[ℚ]  `ℚ[u, v] ⧸ (wᵢ)`,

where `wᵢ` is the dehomogenisation of `W` at the `i`-th coordinate.  Mathlib has
`HomogeneousLocalization.Away` and `Proj.awayι` but NO identification of the degree-zero
away-part with a concrete polynomial quotient — a grep for `dehomogeni`, and for
`MvPolynomial` in the `HomogeneousLocalization` files, returns nothing.  Building it is the
whole of the remaining work.

Given that isomorphism the rest is mechanical, and is why `hjac` is the right hypothesis to
carry: transport along it with
`Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv`, then apply
`RingHom.locally_of_exists` to the two-element family `{∂wᵢ/∂u, ∂wᵢ/∂v}`, which spans the
unit ideal by `hjac` — that is exactly what `hjac` says, at the chart ring, for the point
`(u, v)` given by the images of the two coordinates, which lies on the curve because the
chart ring is the quotient by `wᵢ`.  On each of the two localisations the `2 × 2` Jacobian
of the relations `(wᵢ, t·∂wᵢ/∂u - 1)` in the generators `(u, v, t)` is triangular with
determinant `(∂wᵢ/∂u)²`, a unit there, so the presentation is submersive of dimension
`3 - 2 = 1`.

The three charts differ only in which dehomogenisation `wᵢ` appears; a Gröbner computation
confirms `Δ` lies in the Jacobian ideal for all three, so no chart is exceptional. -/
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
          (MvPolynomial.X i)))).comp (algebraMap ℚ (projGrading E 0))) := sorry

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

/-- **The projective Weierstrass cubic is prime in `K[X, Y, Z]`** (sorry leaf).

This is all that is left of the `hpre` step: given it, the homogeneous coordinate ring is a
domain and `irreducibleSpace_projectiveSpectrum` finishes the job.  It carries NO
ellipticity hypothesis, and should not: mathlib's affine
`WeierstrassCurve.Affine.irreducible_polynomial` holds over any `[IsDomain R]`, singular
Weierstrass equations included.

## Why this is not already available, and the route

Mathlib has the AFFINE statement, `WeierstrassCurve.Affine.irreducible_polynomial
[IsDomain R] : Irreducible W.polynomial`, for `W.polynomial : R[X][Y]`.  What is missing is
the bridge to the HOMOGENEOUS trivariate polynomial:

* `Mathlib/Algebra/Polynomial/Homogenize.lean` homogenises univariate `R[X]` into
  `MvPolynomial (Fin 2) R` only.  It does not cover bivariate → trivariate, and it contains
  **zero** irreducibility lemmas.
* There is no lemma anywhere that a factor of a homogeneous element of a graded domain is
  itself homogeneous, which is the other half of the classical argument.

The classical argument, for the successor: suppose `W = f * g` in `K[X, Y, Z]`.  Both
factors are homogeneous (the missing graded-domain lemma), say of degrees `d` and `3 - d`.
Dehomogenise at `Z = 1`: the affine cubic is irreducible, so one dehomogenised factor is a
nonzero constant, say `f(X, Y, 1) = c`.  A homogeneous `f` of degree `d` with constant
dehomogenisation is `c * Z ^ d`; but `Z ∤ W`, since `W` contains the term `-X ^ 3`.  Hence
`d = 0` and `f` is a unit.  So `W` is irreducible, and `K[X, Y, Z]` is a UFD, so `W` is
prime. -/
theorem prime_projPolynomial : Prime (polynomial W) := sorry

/-- The homogeneous coordinate ring of the projective model is a domain — the content of
`hpre`, modulo the general `Proj`-of-a-graded-domain statement. -/
theorem isDomain_projCoordinateRing :
    IsDomain (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal W).toIdeal) := by
  haveI : ((polynomialHomogeneousIdeal W).toIdeal).IsPrime := by
    show (Ideal.span {polynomial W}).IsPrime
    rw [Ideal.span_singleton_prime (prime_projPolynomial W).ne_zero]
    exact prime_projPolynomial W
  exact Ideal.Quotient.isDomain _

/-- **The projective Weierstrass model is preconnected** — the `hpre` step of
`geometricallyConnected_projToSpec`, over an arbitrary base field.  Everything here is
proven except `prime_projPolynomial`. -/
theorem preconnectedSpace_proj : PreconnectedSpace (proj W) := by
  haveI := isDomain_projCoordinateRing W
  haveI := irreducibleSpace_projectiveSpectrum (projGrading W) (pointAtInfinity W)
  show PreconnectedSpace (ProjectiveSpectrum (projGrading W))
  infer_instance

end Leaves

/-- **`Proj` commutes with base change of the base field** (sorry leaf) — the `hbc` step of
`geometricallyConnected_projToSpec`.

## Why there is nothing to reuse

There is **no base change for `Proj` at this pin, in any form**.  A search over
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` for `Proj` together with `pullback`,
`baseChange`, `IsPullback` or `TensorProduct` returns nothing; so does the same search over
`~/cs/FLT`.  The only functoriality that exists is contravariant in the graded ring,
`AlgebraicGeometry.Proj.map` (`ProjectiveSpectrum/Functor.lean:144`), and there is no
functor-of-points description of `Proj` to fall back on.  Building this IS the task.

## The route, and the two pieces it needs

`Proj.map` has signature `map (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) : Proj ℬ ⟶ Proj 𝒜`,
where `𝒜 →+*ᵍ ℬ` is `GradedRingHom` from
`Mathlib/RingTheory/GradedAlgebra/Homogeneous/Maps.lean`.  So the successor should:

1. **Build the graded ring hom.**  `MvPolynomial.map (algebraMap ℚ K)` sends `(W)` into
   `(W_K)` — that is exactly `WeierstrassCurve.Projective.baseChange_polynomial`, i.e.
   `(W⁄K).polynomial = MvPolynomial.map f W.polynomial`, which is already in mathlib
   (`EllipticCurve/Projective/Basic.lean:536`) — so it descends to the quotients, and it
   preserves `projGrading` degrees because it preserves `homogeneousSubmodule`.  The
   hypothesis `hf` holds because the target's irrelevant ideal is generated by `X̄, Ȳ, Z̄`,
   all of which are images.  This yields a canonical morphism
   `proj (W.baseChange K) ⟶ proj W`, and with `projToSpec (W.baseChange K)` a canonical
   morphism `proj (W.baseChange K) ⟶ pullback (projToSpec W) (Spec.map (algebraMap ℚ K))`.

2. **Prove that morphism is an isomorphism.**  This is the real content and it is local on
   the standard affine cover `Proj.affineOpenCoverOfIrrelevantLESpan` (already used, in
   this file, by `smoothOfRelativeDimension_projToSpec`): on the chart `D₊(f)` it becomes
   the ring statement `(A_(f)) ⊗_ℚ K ≅ (A_K)_(f_K)`, i.e. that the degree-zero part of a
   homogeneous localisation commutes with base change.  `Proj.pullbackAwayιIso`
   (`ProjectiveSpectrum/Basic.lean:256`) is the mathlib lemma that says the charts of `Proj`
   pull back to the charts, and is the intended glue.

Note this statement carries no ellipticity: it is pure base change of a graded quotient of
a polynomial ring, true for every Weierstrass curve over every field extension. -/
theorem nonempty_projPullbackIso (E : WeierstrassCurve ℚ) (K : Type) [Field K] [Algebra ℚ K] :
    Nonempty (Limits.pullback (projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ≅ proj (E.baseChange K)) := sorry

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

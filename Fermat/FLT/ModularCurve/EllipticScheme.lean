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

`isProper_projToSpec` and `nonempty_projGroupLaw` are both PROVEN, and so now is
`smoothOfRelativeDimension_projToSpec` apart from ONE leaf.
`locally_isStandardSmooth_awayCoord` — the last direct sorry of item 7a — is PROVEN
from the three declarations of the "Dehomogenisation" section, and two of those three
are now proven as well:

* `exists_projChartRingEquiv` (the dehomogenisation isomorphism
  `(ℚ[X, Y, Z] ⧸ (W))_{(xᵢ)}` in degree `0` ≃ `ℚ[u, v] ⧸ (wᵢ)`) is **PROVEN**, as the
  first isomorphism theorem for the chart map `projChartHom : ℚ[u, v] → (B_{xᵢ})₀`,
  `uⱼ ↦ xⱼ/xᵢ`.  Surjectivity is `HomogeneousLocalization.Away.mk_surjective` composed
  with `projChartHom_dehomogenizeAt`; the kernel is `projChartHom_ker`, whose only
  arithmetic input is `not_X_dvd_polynomial` (`Xᵢ ∤ W`, checked by evaluation), NOT
  irreducibility of `W`.
* `isStandardSmoothOfRelativeDimension_projChartAway` (a plane curve is standard smooth
  of relative dimension `1` where a partial derivative is invertible) is PROVEN.
* `projChart_jacobian_span_eq_top` (the chart Jacobian criterion, where `hjac` and hence
  `Δ` is consumed) is the one that remains.

The remaining open leaves of the file are therefore that one plus
`exists_projAdd` — where all the remaining gluing work for the group law now
lives — `exists_projGeomFibreAddEquiv`, and the interior of
`geometricallyConnected_projToSpec`, which still carries three named sorried
steps `hbc`/`hne`/`hpre`.  Each declaration carries its own docstring saying what
is missing and where the classical argument is.

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

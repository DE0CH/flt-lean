/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Two morphisms agreeing at a dense set of `K`-points are equal

Mathlib carries the engine for this in `Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean`
(a 2026 file), but only in the shape `AlgebraicGeometry.ext_of_apply_eq`, whose BASE must
be algebraically closed.  Over `Spec ℚ` — which is the base of every modular curve in this
development — that shape costs a base change to `Spec ℚ̄` and a descent back.

`AlgebraicGeometry.ext_of_fromSpecResidueField_eq` is stated over an ARBITRARY base and
costs neither, but it asks for agreement after `X.fromSpecResidueField x` rather than after
a `K`-point.  This file is the bridge: `ext_of_dense_fieldPoints` drives the arbitrary-base
lemma from the `K`-points a development actually has, and
`ext_of_dense_open_algClosPoints` packages the whole argument for the situation this project
meets — a scheme with a dense open subscheme whose `K`-points are understood.

## Main results

* `isDominant_specMap_residueField` — `Spec` of a field extension is dominant.
* `fromSpecResidueField_comp_eq_of_fieldPoint` — a `K`-point sees as much as its
  residue-field point.
* `ext_of_dense_fieldPoints` — two morphisms agreeing at a dense set of `K`-points, over an
  ARBITRARY base, are equal.
* `exists_algClosPoint_of_isClosed_singleton` — a scheme locally of finite type over a field
  `F` has a `K`-point over every CLOSED point, for any algebraically closed `K ⊇ F`.
* `ext_of_dense_open_algClosPoints` — the assembly: two morphisms out of a reduced
  irreducible `X` agreeing on the `K`-points of a nonempty open subscheme are equal.

The first three were verified green on 2026-07-31 by `flt-lean-296` and parked at the
repository root as `HANDOFF-flt-lean-296-dense-field-points.lean`; they are moved here, with
the last two added, by the commit that gives them their first consumer
(`ModularCurve/X0.lean`'s `eq_of_forall_comp_classify_of_isX0Compactification`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **`Spec` of a field extension is DOMINANT** (PROVEN).

Both spectra are single points, so the range is nonempty in a subsingleton space.  This is
the one instance `ext_of_isDominant_of_isSeparated` needs below and which typeclass search
does not find: there is no `IsDominant (Spec.map φ)` instance for a map of fields at this
pin. -/
theorem isDominant_specMap_residueField {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (φ : X.residueField x ⟶ CommRingCat.of K) : IsDominant (Spec.map φ) := by
  haveI : Subsingleton (Spec (X.residueField x)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (X.residueField x)))
  haveI : Nonempty (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K))
  rw [isDominant_iff, DenseRange]
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun y => ?_)
  exact subset_closure ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

/-- **A `K`-POINT SEES AS MUCH AS ITS RESIDUE-FIELD POINT** (PROVEN) — if two morphisms into
a separated `Y` agree after a `K`-point `p`, they agree after `X.fromSpecResidueField` at the
image of `p`.

This is the bridge that makes `ext_of_fromSpecResidueField_eq` — which is stated over an
ARBITRARY base — usable from `K`-points, and so removes the base change to an algebraic
closure that `ext_of_apply_eq` would otherwise force.

`Scheme.SpecToEquivOfField` factors `p` as `Spec.map φ ≫ fromSpecResidueField x` (**on the
nose — that direction of the equivalence is `rfl`**), and `Spec.map φ` is dominant by the
lemma above, so `ext_of_isDominant_of_isSeparated` cancels it.  Note `Spec κ(x)` is reduced
for free, so no hypothesis on `X` is used here; `IsReduced X` is needed only by the caller
below. -/
theorem fromSpecResidueField_comp_eq_of_fieldPoint {X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (i : Y ⟶ Z) [IsSeparated i] (hfg : f ≫ i = g ≫ i)
    {K : Type u} [Field K] (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = p ≫ g) :
    X.fromSpecResidueField ((Scheme.SpecToEquivOfField K X p).1) ≫ f
      = X.fromSpecResidueField ((Scheme.SpecToEquivOfField K X p).1) ≫ g := by
  have hp' : p = Spec.map (Scheme.SpecToEquivOfField K X p).2
      ≫ X.fromSpecResidueField (Scheme.SpecToEquivOfField K X p).1 := by
    conv_lhs => rw [← (Scheme.SpecToEquivOfField K X).symm_apply_apply p]
    rfl
  haveI := isDominant_specMap_residueField (Scheme.SpecToEquivOfField K X p).2
  refine ext_of_isDominant_of_isSeparated i ?_ (Spec.map (Scheme.SpecToEquivOfField K X p).2) ?_
  · rw [Category.assoc, Category.assoc, hfg]
  · rw [← Category.assoc, ← Category.assoc, ← hp']; exact hp

/-- **TWO MORPHISMS AGREEING AT A DENSE SET OF `K`-POINTS ARE EQUAL** (PROVEN), over an
ARBITRARY base and with no hypothesis that the base be algebraically closed — `K` itself need
not even be algebraically closed.

`X` reduced and `i` separated are exactly the hypotheses of
`ext_of_fromSpecResidueField_eq`, which this drives.  The caller owes, at each point of the
dense set, a `K`-point lying over it; for a finite-type scheme over a field with `K` an
algebraic closure of that field, that is `exists_algClosPoint_of_isClosed_singleton` below. -/
theorem ext_of_dense_fieldPoints {X Y Z : Scheme.{u}} {f g : X ⟶ Y} (i : Y ⟶ Z)
    [IsSeparated i] [IsReduced X] {K : Type u} [Field K]
    (S : Set X) (hS : Dense S)
    (H : ∀ x ∈ S, ∃ p : Spec (CommRingCat.of K) ⟶ X,
      (Scheme.SpecToEquivOfField K X p).1 = x ∧ p ≫ f = p ≫ g)
    (hfg : f ≫ i = g ≫ i) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g i S hS ?_ hfg
  intro x hx
  obtain ⟨p, hpx, hp⟩ := H x hx
  subst hpx
  exact fromSpecResidueField_comp_eq_of_fieldPoint i hfg p hp

/-- **A CLOSED POINT OF A FINITE-TYPE SCHEME OVER A FIELD CARRIES A `K`-POINT, FOR ANY
ALGEBRAICALLY CLOSED `K ⊇ F`** (PROVEN), and the `K`-point lies over `Spec F` through the
structure map of `K` as an `F`-algebra.

This is Zariski's lemma in scheme clothing.  `{y}` closed makes `Y.fromSpecResidueField y` a
closed immersion, so the composite `Spec κ(y) ⟶ Y ⟶ Spec F` is locally of finite type into a
JACOBSON scheme, hence FINITE
(`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`, `@[stacks 01TB]`) — which is where
Zariski's lemma is spent, inside mathlib.  So `κ(y)` is integral, hence algebraic, over `F`
and `IsAlgClosed.lift` embeds it in `K`.

**The `F`-ALGEBRA STRUCTURE ON `κ(y)` MUST COME FROM THE STRUCTURE MORPHISM AND FROM NOTHING
ELSE**, or the `IsScalarTower` that `IsAlgClosed.lift` needs does not synthesize.  It is
taken here as `Spec.preimage (Y.fromSpecResidueField y ≫ str)`, i.e. through the full
faithfulness of `Spec`, which is exactly the map the conclusion's compatibility clause is
about. -/
theorem exists_algClosPoint_of_isClosed_singleton
    {F K : Type u} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    {Y : Scheme.{u}} (str : Y ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType str]
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    ∃ q : Spec (CommRingCat.of K) ⟶ Y,
      (Scheme.SpecToEquivOfField K Y q).1 = y ∧
        q ≫ str = Spec.map (CommRingCat.ofHom (algebraMap F K)) := by
  haveI : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  haveI : IsFinite (Y.fromSpecResidueField y ≫ str) :=
    (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
      (f := Y.fromSpecResidueField y ≫ str)).mpr inferInstance
  -- `Spec` is fully faithful, so the composite is `Spec.map` of a ring map `φ : F ⟶ κ(y)`.
  set φ : CommRingCat.of F ⟶ Y.residueField y :=
    Spec.preimage (Y.fromSpecResidueField y ≫ str) with hφ
  have hφmap : Spec.map φ = Y.fromSpecResidueField y ≫ str := Spec.map_preimage _
  -- `κ(y)` is INTEGRAL over `F` through `φ`, hence algebraic …
  haveI : IsIntegralHom (Spec.map φ) := by rw [hφmap]; infer_instance
  have hint : φ.hom.IsIntegral := by rw [← IsIntegralHom.SpecMap_iff]; infer_instance
  letI : Algebra F (Y.residueField y) := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral F (Y.residueField y) := ⟨hint⟩
  haveI : Algebra.IsAlgebraic F (Y.residueField y) := inferInstance
  -- … and so embeds in the algebraically closed `K` over `F`.
  let ψ : Y.residueField y →ₐ[F] K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.fromSpecResidueField y, ?_, ?_⟩
  · simp only [Scheme.SpecToEquivOfField_apply_fst, Scheme.Hom.comp_base, TopCat.comp_app]
    exact Scheme.fromSpecResidueField_apply _ _
  · rw [Category.assoc, ← hφmap, ← Spec.map_comp]
    congr 1
    ext a
    exact ψ.commutes a

/-- **TWO MORPHISMS AGREEING ON THE `K`-POINTS OF A NONEMPTY OPEN SUBSCHEME ARE EQUAL**
(PROVEN) — the assembly, and the form a consumer wants.

`X` is reduced and pre-irreducible over the field `F` and locally of finite type over it;
`jY : Y ⟶ X` is an open immersion with `Y` nonempty; `jstr` is separated.  Then two
morphisms `u, v : X ⟶ J` over `Spec F` are equal as soon as they agree after every
`K`-point of `Y` over `Spec F`, for `K` any algebraically closed extension of `F`.

THE ARGUMENT, and both halves are cheap once the mathlib names are known.  `Y` is locally of
finite type over `F`, so it is a JACOBSON space and its CLOSED points are dense in it
(`Topology.closure_closedPoints`); `X` is irreducible and `Set.range jY.base` is a nonempty
OPEN, hence dense (`IsOpen.dense`); and continuity carries a dense subset of `Y` onto a set
whose closure contains `Set.range jY.base`, hence onto a dense subset of `X`.  At each such
point `exists_algClosPoint_of_isClosed_singleton` produces the `K`-point, and
`ext_of_dense_fieldPoints` finishes.

**`Nonempty Y` IS LOAD-BEARING and the statement is FALSE without it**: with `Y = ∅` the
hypothesis `H` is vacuous while `u` and `v` are arbitrary, and `X = 𝔸¹_F`, `J = 𝔸¹_F`,
`u = 𝟙`, `v` the zero section refutes the conclusion.  It is what makes the image of `Y`
a NONEMPTY open, which is what makes it dense. -/
theorem ext_of_dense_open_algClosPoints
    {F K : Type u} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    {X Y J : Scheme.{u}} {strX : X ⟶ Spec (CommRingCat.of F)}
    {strY : Y ⟶ Spec (CommRingCat.of F)} {jY : Y ⟶ X} [IsOpenImmersion jY]
    (hcomm : jY ≫ strX = strY) [LocallyOfFiniteType strX]
    [IsReduced X] [PreirreducibleSpace X] [Nonempty Y]
    {jstr : J ⟶ Spec (CommRingCat.of F)} [IsSeparated jstr]
    {u v : X ⟶ J} (huv : u ≫ jstr = v ≫ jstr)
    (H : ∀ q : Spec (CommRingCat.of K) ⟶ Y,
      q ≫ strY = Spec.map (CommRingCat.ofHom (algebraMap F K)) →
        q ≫ jY ≫ u = q ≫ jY ≫ v) :
    u = v := by
  haveI : LocallyOfFiniteType strY := by rw [← hcomm]; infer_instance
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace strY
  -- the image of `Y` is a NONEMPTY OPEN of the irreducible `X`, hence dense
  have hopen : IsOpen (Set.range jY.base) := jY.isOpenEmbedding.isOpen_range
  have hne : (Set.range jY.base).Nonempty := Set.range_nonempty _
  have hdY : Dense (Set.range jY.base) := hopen.dense hne
  -- the closed points of `Y` are dense in `Y`, so their image is dense in `X`
  have hcl : Dense (closedPoints Y) := dense_iff_closure_eq.mpr closure_closedPoints
  have hdense : Dense (jY.base '' closedPoints Y) := by
    have hsub : Set.range jY.base ⊆ closure (jY.base '' closedPoints Y) := by
      rintro _ ⟨y, rfl⟩
      exact image_closure_subset_closure_image jY.base.hom.continuous
        (Set.mem_image_of_mem _ (hcl y))
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
    rw [← hdY.closure_eq]
    exact closure_minimal hsub isClosed_closure
  refine ext_of_dense_fieldPoints (K := K) jstr _ hdense ?_ huv
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨q, hq1, hq2⟩ := exists_algClosPoint_of_isClosed_singleton (K := K) strY hy
  refine ⟨q ≫ jY, ?_, ?_⟩
  · simp only [Scheme.SpecToEquivOfField_apply_fst, Scheme.Hom.comp_base, TopCat.comp_app]
    rw [show (TopCat.Hom.hom q.base) (IsLocalRing.closedPoint K)
        = (Scheme.SpecToEquivOfField K Y q).1 from rfl, hq1]
  · rw [Category.assoc, Category.assoc]; exact H q hq2

end AlgebraicGeometry

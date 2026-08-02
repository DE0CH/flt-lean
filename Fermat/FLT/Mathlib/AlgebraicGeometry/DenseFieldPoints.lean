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
`exists_algClosPoint_of_isClosed_singleton` supplies those `K`-points at every closed point
of a finite-type scheme over a field — which is all a consumer over `Spec ℚ` has to know.

## Main results

* `isDominant_specMap_residueField` — `Spec` of a field extension is dominant.
* `fromSpecResidueField_comp_eq_of_fieldPoint` — a `K`-point sees as much as its
  residue-field point.
* `ext_of_dense_fieldPoints` — two morphisms agreeing at a dense set of `K`-points, over an
  ARBITRARY base, are equal.
* `exists_algClosPoint_of_isClosed_singleton` — a scheme locally of finite type over a field
  `F` has a `K`-point over every CLOSED point, for any algebraically closed `K ⊇ F`.
The first three were verified green on 2026-07-31 by `flt-lean-296` and parked at the
repository root as `HANDOFF-flt-lean-296-dense-field-points.lean`; they are moved here, with
the fourth added, by the commit that gives them their first consumer —
`ModularCurve/X0.lean`'s `eq_of_algClosPoint_comp_eq`, whose statement is unchanged and
whose ~30-line bespoke body this module replaces.  `X1.lean`'s `Γ₁` twin owes the same
statement and can now reuse these rather than re-derive them.
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

/-!
### The dense-open packaging is NOT here, and that is deliberate

An assembly `ext_of_dense_open_algClosPoints` — *two morphisms out of a reduced irreducible
`X` agreeing on the `K`-points of a NONEMPTY OPEN subscheme are equal* — was written and
verified green alongside the four lemmas above on 2026-08-02, and then removed, because
under the arrangement `X0.lean` actually took (`eq_of_algClosPoint_comp_eq`, which quantifies
over the `K`-points of ALL of `X`) it has no consumer, and free-floating declarations are
forbidden here.

It is the right shape for the level-free density statement that
`Fermat.HeckeCommute.eq_of_forall_algClosPoint_comp_eq` is queued to be — the one that
quantifies over the `ℚ̄`-points of the OPEN part `Y` only, so that `X0.lean` and `X1.lean`
can share it — and whoever takes that task should paste it back rather than re-derive it:

    git show 69db1300:Fermat/FLT/Mathlib/AlgebraicGeometry/DenseFieldPoints.lean

Its proof is `IsOpen.dense` for the image of `Y` in the irreducible `X`,
`Topology.closure_closedPoints` for the closed points of the Jacobson space `Y`,
`image_closure_subset_closure_image` to move the second inside the first, and then
`exists_algClosPoint_of_isClosed_singleton` and `ext_of_dense_fieldPoints` above.
`Nonempty Y` is load-bearing there: with `Y = ∅` the hypothesis is vacuous and the
conclusion false.
-/

end AlgebraicGeometry

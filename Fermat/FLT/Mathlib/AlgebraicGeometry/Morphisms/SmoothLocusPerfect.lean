/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Smooth.Field

/-!
# The smooth locus at a point with a perfect residue stalk

Small pieces of infrastructure about `Scheme.Hom.smoothLocus` that
`Mathlib` does not have at this pin, extracted while cutting
`flat_of_surjective_of_isAdditiveOn` in `Fermat/FLT/ModularCurve/X0.lean`.

The second block (`mem_smoothLocus_comp`, `mem_smoothLocus_of_comp_of_flat`,
`le_preimage_smoothLocus_of_sq`) was added 2026-07-31 and is the POINTWISE
two-out-of-three calculus for `smoothLocus`: `smoothLocus` is closed under
composition, and it is *reflected* by a flat first factor.  The second of those
is the single open leaf; the third is the packaged form the consumer wants and
is proven over the first two.

The point of the file is that mathlib's generic-smoothness statements

    Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
    Scheme.Hom.dense_smoothLocus_of_perfectField

are available **only for a morphism `f : X ⟶ Spec K` to the spectrum of a
field**, whereas the consumer needs them for a morphism `u : A ⟶ B` between
two schemes of positive dimension.  What actually makes mathlib's proof work
is not the shape of the target but the fact that the relevant stalk of the
target is a perfect field, and `mem_smoothLocus_of_isField_stalk` below is
that proof stated over an arbitrary target.

Together with the two instances

    Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean : `[Smooth f] : Flat f`
    Mathlib/RingTheory/Smooth/Fiber.lean : `Algebra.Smooth.of_formallySmooth_fiber`

this replaces the "Cohen-Macaulay rings + the local flatness criterion"
route that the consumer's docstring used to name as the only way in; see that
docstring for the correction.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **A morphism between two schemes locally of finite type over a locally
Noetherian base is locally of finite presentation.**

Over a Noetherian base, finite type and finite presentation agree
(`LocallyOfFinitePresentation.iff_locallyOfFiniteType`), and finite type is
right-cancellable (`locallyOfFiniteType_of_comp`).  Mathlib has both halves and
not the combination; the combination is what a morphism of `S`-schemes needs
before `Scheme.Hom.smoothLocus` is even well-formed, since that definition
takes `[LocallyOfFinitePresentation f]` as an instance argument. -/
theorem locallyOfFinitePresentation_of_comp_of_isLocallyNoetherian
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType g] [LocallyOfFiniteType (f ≫ g)] :
    LocallyOfFinitePresentation f := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  infer_instance

/-- **A morphism is smooth at a point whose source and target stalks are fields
of characteristic zero.**

This is the general-target form of mathlib's
`Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`, whose statement is
restricted to `f : X ⟶ Spec (.of K)`.  The mechanism is identical and is
entirely about the stalk map: `Algebra.FormallySmooth.of_perfectField`
(`Mathlib/RingTheory/Smooth/Field.lean`) makes any essentially-finite-type
algebra over a perfect field formally smooth, `LocallyOfFiniteType.stalkMap`
supplies `Algebra.EssFiniteType` for the stalk map, and membership in
`smoothLocus` is *by definition* formal smoothness of that stalk map.

**Characteristic zero, not perfectness, is the hypothesis** only because
`PerfectField.ofCharZero` is the instance a `ℚ`-scheme can actually discharge;
in characteristic `p` the statement is false for an inseparable extension, e.g.
`𝔽_p(t) ⟶ 𝔽_p(t^{1/p})`, which is a finite extension of fields that is not
formally smooth. -/
theorem mem_smoothLocus_of_isField_stalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X)
    (hX : IsField (X.presheaf.stalk x)) (hY : IsField (Y.presheaf.stalk (f x)))
    [CharZero (Y.presheaf.stalk (f x))] :
    x ∈ f.smoothLocus := by
  have := LocallyOfFiniteType.stalkMap f x
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap x).hom]
  letI : Field (X.presheaf.stalk x) := hX.toField
  letI : Field (Y.presheaf.stalk (f x)) := hY.toField
  haveI : PerfectField (Y.presheaf.stalk (f x)) := PerfectField.ofCharZero
  exact Algebra.FormallySmooth.of_perfectField

/-- **GENERIC SMOOTHNESS IN CHARACTERISTIC ZERO, for a dominant morphism of
integral schemes**: the smooth locus of such a morphism is nonempty, because
the generic point lies in it.

For integral `X` and `Y` the stalks at the generic points are the function
fields, so the stalk map of `f` at `genericPoint X` is an extension of fields;
in characteristic zero every such extension is separable, hence formally
smooth.  The hypothesis `hf` — that `f` carries the generic point to the
generic point — is exactly dominance, and it is load-bearing: a closed
immersion of a point into a curve has integral source and target and an empty
smooth locus. -/
theorem nonempty_smoothLocus_of_genericPoint_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [IsIntegral X] [IsIntegral Y]
    [CharZero Y.functionField] (hf : f (genericPoint X) = genericPoint Y) :
    (f.smoothLocus : Set X).Nonempty := by
  refine ⟨genericPoint X, ?_⟩
  have hX : IsField (X.presheaf.stalk (genericPoint X)) := Field.toIsField X.functionField
  have hY : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [hf]; exact Field.toIsField Y.functionField
  haveI : CharZero (Y.presheaf.stalk (f (genericPoint X))) := by rw [hf]; infer_instance
  exact mem_smoothLocus_of_isField_stalk f _ hX hY

/-! ## The pointwise two-out-of-three calculus for `smoothLocus`

`Scheme.Hom.smoothLocus` is *by definition* `{x | (f.stalkMap x).hom.FormallySmooth}`,
so it inherits, pointwise, whatever two-out-of-three properties
`RingHom.FormallySmooth` has.  Mathlib exposes none of these at the scheme level:
it has only `Scheme.Hom.preimage_smoothLocus_eq`, which is the special case of
`mem_smoothLocus_of_comp_of_flat` below in which the first factor is an OPEN
IMMERSION, proven by cancelling an *isomorphism* of stalks.  Replacing that
isomorphism by a faithfully flat local homomorphism is the whole of the residual
leaf.
-/

/-- **SMOOTHNESS AT A POINT COMPOSES** — if `f` is smooth at `x` and `g` is
smooth at `f x`, then `f ≫ g` is smooth at `x`.

This is `RingHom.FormallySmooth.comp` read through `Scheme.Hom.stalkMap_comp`,
and it is the direction of the two-out-of-three that costs nothing.  Mathlib has
the ring-level statement and not the `smoothLocus` one. -/
theorem mem_smoothLocus_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] {x : X}
    (hx : x ∈ f.smoothLocus) (hgx : f x ∈ g.smoothLocus) :
    x ∈ (f ≫ g).smoothLocus := by
  show ((f ≫ g).stalkMap x).hom.FormallySmooth
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.comp hgx hx

/-- **SMOOTHNESS AT A POINT DESCENDS ALONG A FLAT FIRST FACTOR** (sorry leaf,
cut 2026-07-31 out of `smoothLocus_pairSquareMap_le` in
`Fermat/FLT/ModularCurve/X0.lean`, which is now PROVEN over it) — if `p` is flat
and `p ≫ g` is smooth at `x`, then `g` is smooth at `p x`.

**Why the statement is VOUCHED**, i.e. why writing `sorry` here is a promise that
can be kept rather than a hypothesis about the world.  Unfolding both sides,
with `R := 𝒪_{Z, g (p x)}`, `S := 𝒪_{Y, p x}`, `T := 𝒪_{X, x}` and
`Scheme.Hom.stalkMap_comp`, the statement is exactly

    R ⟶ S ⟶ T local, S ⟶ T faithfully flat, R ⟶ T formally smooth
      ⟹ R ⟶ S formally smooth.

`S ⟶ T` really is FAITHFULLY flat and not merely flat: `Flat p` gives flatness of
the stalk map, the stalk map of any morphism of schemes is a local homomorphism of
local rings, and `Module.FaithfullyFlat.of_flat_of_isLocalHom`
(`Mathlib/RingTheory/Flat/FaithfullyFlat/Algebra.lean`) upgrades flat + local to
faithfully flat.  Globally the statement is Stacks `02VL` (smoothness is fppf
local on the source) read at one point, equivalently EGA IV 17.7.7; nothing about
it is open mathematics.

**WHAT IS ACTUALLY MISSING, checked against the pin on 2026-07-31 rather than
assumed.**  The obstruction is *descent of formal smoothness*, and both of the
two routes into it are absent:

* `Mathlib/RingTheory/Etale/Descent.lean` records the BASE-CHANGE form,
  `Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`, as
  an open `proof_wanted`, noting that a proof needs Raynaud–Gruson descent of
  projectivity (Stacks `058B`).  Its finite-presentation *corollaries* —
  `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat` and
  `RingHom.Smooth.codescendsAlong_faithfullyFlat` — ARE proven, and at the scheme
  level `Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean` turns them
  into `DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`.  None of
  these applies here: they descend along a base change of the TARGET, and what is
  needed is descent along the SOURCE, which is a different statement.
* Going through `Algebra.IsSmoothAt.of_formallySmooth_fiber`
  (`Mathlib/RingTheory/Smooth/Fiber.lean`) splits the goal into *flatness of
  `R ⟶ S`*, which does descend by an elementary argument, and *formal smoothness
  of the fibre `𝓀[R] ⊗[R] S` over the field `𝓀[R]`*, which does not: the only
  formal-smoothness-over-a-field statement in the PIN is
  `Algebra.FormallySmooth.of_perfectField`, and it is about a field EXTENSION
  (`Mathlib/RingTheory/Smooth/Field.lean`), whereas that fibre is a local ring.

**THE CHEAPEST ROUTE IS THE SECOND ONE, BECAUSE THIS PROJECT ALREADY HAS THE
PIECE MATHLIB IS MISSING** (found 2026-07-31 and NOT recorded on the old leaf, so
do not re-derive the pessimistic reading above).
`Fermat/FLT/Modularity/MoretBailly.lean` proves
`formallySmooth_of_isRegularLocalRing_of_essFiniteType_of_perfectField` — a
REGULAR local ring essentially of finite type over a PERFECT field is formally
smooth over it — together with its converse
`isRegularLocalRing_stalk_of_smooth_over_field`.  Both fibres here are local
(`𝓀[R] ⊗[R] S = S / 𝓂[R]S`, and likewise for `T`) and essentially of finite type
over `𝓀[R]`, and `S/𝓂[R]S ⟶ T/𝓂[R]T` is faithfully flat local as a base change of
`S ⟶ T`.  So when `𝓀[R]` is perfect — which it is in every consumer here, since
everything is over `ℚ` — the fibre step collapses to exactly one classical
statement:

> `A ⟶ B` a flat local homomorphism of Noetherian local rings with `B` regular
> ⟹ `A` regular.  (Matsumura, *Commutative Ring Theory*, Thm 23.7; Stacks `00OJ`.)

`grep -rn IsRegularLocalRing .lake/packages/mathlib/Mathlib` returns only
`RegularLocalRing/{Defs,Polynomial}.lean` at this pin, so that descent is absent
— but it is a bounded, self-contained, well-documented theorem, and it is a far
smaller target than Raynaud–Gruson.  **That is the route to take.**

A worker taking it may find it cheaper to add a `PerfectField` (or `CharZero`)
hypothesis on the relevant residue field of `Z` rather than prove the leaf in the
generality stated.  That is legitimate and costs two consumer edits:
`smoothLocus_pairSquareMap_le` and `smoothLocus_pairSquareMap` in `X0.lean` are
stated over an arbitrary base `S` while their only consumer,
`smoothLocus_eq_top_of_nonempty_of_isAdditiveOn`, has `S = SpecQ`, so the
hypothesis is available there and nowhere else has to change.  Keep the general
statement if the general proof is in reach; specialise if it is not.

Either way, build the theory in this file or beside it, not inside `X0.lean`.

**`Flat p` IS LOAD-BEARING and the statement is FALSE without it.**  Let `C` be
the cuspidal cubic over a field `k`, `p : Spec k ⟶ C` the closed immersion of the
cusp and `g : C ⟶ Spec k` the structure morphism.  Then `p ≫ g = 𝟙 (Spec k)` is
smooth, so the hypothesis holds at the unique point of `Spec k`, while `g` is not
smooth at the cusp — `C` is singular there.  The closed immersion `p` is locally
of finite presentation and is exactly not flat, so no weakening of the flatness
hypothesis to a finiteness one survives. -/
theorem mem_smoothLocus_of_comp_of_flat {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    [Flat p] [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation g] {x : X}
    (hx : x ∈ (p ≫ g).smoothLocus) :
    p x ∈ g.smoothLocus :=
  sorry

/-- **THE SMOOTH LOCUS OF THE TOP OF A COMMUTING SQUARE IS CARRIED INTO THE SMOOTH
LOCUS OF ITS BOTTOM** (PROVEN 2026-07-31 over the two lemmas above) — given

    f ≫ pB = pA ≫ u

with `pB` SMOOTH and `pA` FLAT, every point at which `f` is smooth maps under
`pA` to a point at which `u` is smooth.

This is the packaged form the homogeneity argument of `X0.lean` consumes: applied
to the two projections of `A ×_S A ⟶ B ×_S B` it is
`smoothLocus_pairSquareMap_le`.  The proof is two steps and no geometry:
`mem_smoothLocus_comp` pushes `z` into `smoothLocus (f ≫ pB)` because `pB` is
smooth everywhere, the square rewrites that to `smoothLocus (pA ≫ u)`, and
`mem_smoothLocus_of_comp_of_flat` cancels the flat `pA`.

Note that SURJECTIVITY of `pA` is not needed: the conclusion is about the single
point `pA z`, which the hypothesis already exhibits a preimage of.  That is what
makes this pointwise form cheaper than the global Stacks `02VL`. -/
theorem le_preimage_smoothLocus_of_sq {P Q A B : Scheme.{u}} {f : P ⟶ Q} {pA : P ⟶ A}
    {pB : Q ⟶ B} {u : A ⟶ B} (h : f ≫ pB = pA ≫ u)
    [LocallyOfFinitePresentation f] [Smooth pB] [Flat pA]
    [LocallyOfFinitePresentation pA] [LocallyOfFinitePresentation u] :
    f.smoothLocus ≤ pA ⁻¹ᵁ u.smoothLocus := by
  intro z hz
  have h1 : z ∈ (f ≫ pB).smoothLocus :=
    mem_smoothLocus_comp f pB hz (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)
  have h2 : z ∈ (pA ≫ u).smoothLocus := by
    show ((pA ≫ u).stalkMap z).hom.FormallySmooth
    rw [← h]
    exact h1
  exact mem_smoothLocus_of_comp_of_flat pA u h2

end AlgebraicGeometry

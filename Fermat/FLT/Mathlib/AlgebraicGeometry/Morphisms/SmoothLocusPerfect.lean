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

Three small pieces of infrastructure about `Scheme.Hom.smoothLocus` that
`Mathlib` does not have at this pin, extracted while cutting
`flat_of_surjective_of_isAdditiveOn` in `Fermat/FLT/ModularCurve/X0.lean`.

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

end AlgebraicGeometry

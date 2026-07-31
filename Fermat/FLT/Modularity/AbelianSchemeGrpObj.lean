/-
Modularity/AbelianSchemeGrpObj.lean — own work for the Fermat project (not
vendored from the FLT project).

# The bridge from mathlib's `GrpObj (Over S)` to `AbelianSchemeStruct`

`Modularity/AbelianScheme.lean` defines an abelian scheme by its FUNCTOR OF
POINTS: `AbelianSchemeStruct f` is a commutative group structure on
`RelPoint f g` for every base point `g`, natural in the test object, together
with properness, smoothness and geometric connectedness.  Its docstring
explains why: at the time it was written the pin carried no notion of an
abelian variety at all, and the functor-of-points form needs no chosen
pullbacks and no monoidal structure on `Over S`.

The pin has since grown `Mathlib/AlgebraicGeometry/Group/`, and it carries two
theorems this development cannot otherwise reach (found 2026-07-31):

* `AlgebraicGeometry.smooth_of_grpObj` (`Group/Smooth.lean`) — a locally-of-
  finite-type group scheme over a field whose structure morphism is
  `GeometricallyReduced` is `Smooth`.  That is "a reduced group scheme of
  finite type over a perfect field is smooth", already proven and already
  reduced to the algebraically closed case internally.
* `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`
  (`Group/Abelian.lean`, stacks 0BFD) — a proper geometrically integral group
  scheme over a field is commutative.

Both are stated for mathlib's `GrpObj (Over.mk f)`, i.e. the group-object
structure on the over-category with its Cartesian monoidal structure
(`AlgebraicGeometry.Pullbacks.lean` supplies the global
`CartesianMonoidalCategory (Over S)` and `BraidedCategory (Over S)`
instances), NOT for `AbelianSchemeStruct`.  So they are useless here until the
two structures are related, and relating them is what this module does.

## What is here

The load-bearing direction is `GrpObj → AbelianSchemeStruct`, because that is
the direction a PRODUCER needs: a construction that hands back a group scheme
in mathlib's language (a subgroup scheme, a kernel, a base change) can be
turned into the structure this development consumes.

* `mkHomEquivRelPoint` — the identification `(Over.mk g ⟶ Over.mk f) ≃
  RelPoint f g`, which is what the whole bridge rests on.  It is stated with
  the base point as a bare `g` rather than as `(Over.mk g).hom`, deliberately:
  `simp` does not see through the `Over.mk` projection, and with the projection
  form even `Equiv.apply_symm_apply` fails to fire.
* `grpAdd`, `grpZero`, `grpNeg` — the group law induced on relative points by
  a `GrpObj (Over.mk f)`.  These are separated out from `ofGrpObj` so that a
  consumer can state a compatibility ("the group law of the subscheme is the
  restriction of the ambient one") WITHOUT first having to build the whole
  `AbelianSchemeStruct`; `ofGrpObj`'s `add`/`zero`/`neg` fields are these three
  on the nose, so such a statement is `rfl`-usable.
* `AbelianSchemeStruct.ofGrpObj` — the bridge proper.
* `AbelianSchemeStruct.ofGrpObjOfGeometricallyIntegral` — the payoff: a
  proper, geometrically integral group scheme over a field IS an abelian
  variety in this development's sense.  Smoothness and commutativity are the
  two mathlib theorems above; geometric connectedness comes from geometric
  irreducibility through
  `AlgebraicGeometry.geometricallyConnected_of_geometricallyIrreducible`, which
  the PIN does not state (it has no `GeometricallyIrreducible →
  GeometricallyConnected` instance, only the `IrreducibleSpace →
  ConnectedSpace` one on the underlying spaces) but which this TREE already
  proved on 2026-07-27, in
  `Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean`.

## What is deliberately NOT here

The converse direction, `AbelianSchemeStruct → CommGrpObj (Over.mk f)`, is a
short construction through `CategoryTheory.CommGrpObj.ofRepresentableBy`: the
functor of points is a presheaf of commutative groups on `Over S`, and
`Over.mk f` represents it by `mkHomEquivRelPoint`.  It was written and verified
while this module was being built, and then dropped, because nothing in the
tree consumes it yet and free-floating code is not allowed here.  The recipe,
so it does not have to be rediscovered: give `RelPoint f g` a `CommGroup`
instance through a type synonym (a bare `RelPoint` must not carry one — there
may be several `ab`), assemble `pointPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat` with
`map φ := RelPoint.pre φ.unop.left (Over.w φ.unop)` (`map_id` and `map_comp`
are `Subtype.ext (Category.id_comp _)` and `Subtype.ext (Category.assoc _ _ _)`
after `ext`), and feed a `Functor.RepresentableBy` whose `homEquiv` is the
`Y.hom`-indexed variant of `mkHomEquivRelPoint` (`(Y ⟶ Over.mk f) ≃
RelPoint f Y.hom`, same four fields) to `CommGrpObj.ofRepresentableBy`; its
`homEquiv_comp` is `rfl`.  The result must be marked `@[implicit_reducible]`,
being a definition of class type.
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Group.Abelian
-- `AlgebraicGeometry.geometricallyConnected_of_geometricallyIrreducible`, PROVEN
-- 2026-07-27.  The pin has `GeometricallyIntegral → GeometricallyIrreducible`
-- and `IrreducibleSpace → ConnectedSpace` but nothing joining them, and this
-- file already supplies the join; it was rediscovered and re-proved here on
-- 2026-07-31 before a duplicate-name scan found the original, so import rather
-- than restate.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.SmoothConnectedCriteria

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Fermat

universe u

variable {A S : Scheme.{u}} {f : A ⟶ S}

/-! ### Relative points as morphisms in `Over S` -/

/-- **Morphisms `Over.mk g ⟶ Over.mk f` in `Over S` are exactly the relative
points of `f` over `g`.**

The base point is written as a bare `g : T ⟶ S` rather than as `Y.hom` for a
general `Y : Over S`.  That is not cosmetic: with the general form the type of
the equivalence mentions `(Over.mk g).hom`, `simp` will not unfold the
`Over.mk` projection, and every rewrite by `Equiv.apply_symm_apply` in the
group-law transport below silently fails to fire. -/
def mkHomEquivRelPoint (f : A ⟶ S) {T : Scheme.{u}} (g : T ⟶ S) :
    (Over.mk g ⟶ Over.mk f) ≃ RelPoint f g where
  toFun φ := ⟨φ.left, Over.w φ⟩
  invFun x := Over.homMk x.1 x.2
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := rfl

@[simp] theorem mkHomEquivRelPoint_apply_val {T : Scheme.{u}} (g : T ⟶ S)
    (φ : Over.mk g ⟶ Over.mk f) : (mkHomEquivRelPoint f g φ).1 = φ.left := rfl

@[simp] theorem mkHomEquivRelPoint_symm_apply_left {T : Scheme.{u}} (g : T ⟶ S)
    (x : RelPoint f g) : ((mkHomEquivRelPoint f g).symm x).left = x.1 := rfl

/-- **`RelPoint.pre` is precomposition in `Over S`.**  This is the one
naturality fact the transport of the group law needs, and it is what turns the
`pre_add` / `pre_zero` fields of `AbelianSchemeStruct` into
`MonObj.comp_mul` / `MonObj.comp_one`. -/
theorem mkHomEquivRelPoint_symm_pre {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S}
    {g' : T' ⟶ S} (hg : h ≫ g = g') (x : RelPoint f g) :
    (mkHomEquivRelPoint f g').symm (RelPoint.pre h hg x)
      = (Over.homMk h hg : Over.mk g' ⟶ Over.mk g) ≫
          (mkHomEquivRelPoint f g).symm x :=
  Over.OverMorphism.ext rfl

/-! ### The group law on relative points induced by a `GrpObj`

These three definitions are the `add`, `zero` and `neg` fields of
`AbelianSchemeStruct.ofGrpObj` below, on the nose.  They are given names of
their own so that a producer can state "the group law of `B` is the
restriction of the group law of `A`" as an equation of relative points before
`ofGrpObj`'s side conditions (properness, smoothness, connectedness) are
available — the statement then matches `ofGrpObj`'s field by `rfl`. -/

section GrpObj

open scoped CategoryTheory.MonObj

variable (f) in
/-- The addition of relative points induced by a group-object structure on
`Over.mk f`. -/
noncomputable def grpAdd [GrpObj (Over.mk f)] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : RelPoint f g) : RelPoint f g :=
  mkHomEquivRelPoint f g ((mkHomEquivRelPoint f g).symm x * (mkHomEquivRelPoint f g).symm y)

variable (f) in
/-- The zero relative point induced by a group-object structure on
`Over.mk f`. -/
noncomputable def grpZero [GrpObj (Over.mk f)] {T : Scheme.{u}} (g : T ⟶ S) :
    RelPoint f g :=
  mkHomEquivRelPoint f g 1

variable (f) in
/-- The negation of relative points induced by a group-object structure on
`Over.mk f`. -/
noncomputable def grpNeg [GrpObj (Over.mk f)] {T : Scheme.{u}} {g : T ⟶ S}
    (x : RelPoint f g) : RelPoint f g :=
  mkHomEquivRelPoint f g ((mkHomEquivRelPoint f g).symm x)⁻¹

theorem grpAdd_def [GrpObj (Over.mk f)] {T : Scheme.{u}} {g : T ⟶ S} (x y : RelPoint f g) :
    grpAdd f x y =
      mkHomEquivRelPoint f g
        ((mkHomEquivRelPoint f g).symm x * (mkHomEquivRelPoint f g).symm y) := rfl

theorem grpZero_def [GrpObj (Over.mk f)] {T : Scheme.{u}} (g : T ⟶ S) :
    grpZero f g = mkHomEquivRelPoint f g 1 := rfl

theorem grpNeg_def [GrpObj (Over.mk f)] {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint f g) :
    grpNeg f x = mkHomEquivRelPoint f g ((mkHomEquivRelPoint f g).symm x)⁻¹ := rfl

/-- **A proper, smooth, geometrically connected commutative group object of
`Over S` is an abelian scheme** in the functor-of-points sense of
`AbelianSchemeStruct`.

The three geometric fields are taken as explicit arguments rather than as
instances because `AbelianSchemeStruct` stores them as data; the group fields
are the transport of the group structure on `Over.mk g ⟶ Over.mk f` along
`mkHomEquivRelPoint`, and the two naturality fields are
`MonObj.comp_mul` / `MonObj.comp_one` read through
`mkHomEquivRelPoint_symm_pre`. -/
noncomputable def AbelianSchemeStruct.ofGrpObj (f : A ⟶ S) [GrpObj (Over.mk f)]
    [IsCommMonObj (Over.mk f)] (hp : IsProper f) (hs : Smooth f)
    (hc : GeometricallyConnected f) : AbelianSchemeStruct f where
  add := grpAdd f
  zero := grpZero f
  neg := grpNeg f
  add_assoc x y z := by simp [grpAdd_def, mul_assoc]
  add_comm := by
    intro T g x y
    haveI := (isCommMonObj_iff_isMulCommutative (Over.mk f)).1 inferInstance (Over.mk g)
    simp [grpAdd_def, mul_comm]
  zero_add := by
    intro T g x
    simp [grpAdd_def, grpZero_def]
  neg_add x := by simp [grpAdd_def, grpNeg_def, grpZero_def]
  pre_add := by
    intro T' T h g g' hg x y
    apply (mkHomEquivRelPoint f g').symm.injective
    simp [grpAdd_def, mkHomEquivRelPoint_symm_pre, MonObj.comp_mul]
  pre_zero := by
    intro T' T h g g' hg
    apply (mkHomEquivRelPoint f g').symm.injective
    simp [grpZero_def, mkHomEquivRelPoint_symm_pre]
  proper := hp
  smooth := hs
  connected := hc

end GrpObj

/-! ### Geometric integrality feeds the bridge -/

/-- **A proper, geometrically integral group scheme over a field is an abelian
variety**, in this development's `AbelianSchemeStruct` sense.

This is the whole point of the module.  Nothing here is proved by hand:
smoothness is `AlgebraicGeometry.smooth_of_grpObj` (which needs
`LocallyOfFiniteType`, supplied by `IsProper`, and `GeometricallyReduced`,
supplied by `GeometricallyIntegral`), commutativity is
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, and
geometric connectedness is geometric irreducibility.  A producer therefore
only has to exhibit the group-object structure and the two geometric
properties `IsProper` and `GeometricallyIntegral`. -/
noncomputable def AbelianSchemeStruct.ofGrpObjOfGeometricallyIntegral
    {K : Type u} [Field K] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of K))
    [GrpObj (Over.mk f)] [IsProper f] [GeometricallyIntegral f] :
    AbelianSchemeStruct f :=
  haveI : IsProper (Over.mk f).hom := ‹IsProper f›
  haveI : GeometricallyIntegral (Over.mk f).hom := ‹GeometricallyIntegral f›
  haveI := isCommMonObj_of_isProper_of_geometricallyIntegral (Over.mk f)
  AbelianSchemeStruct.ofGrpObj f ‹IsProper f› (smooth_of_grpObj f)
    (geometricallyConnected_of_geometricallyIrreducible f)

end Fermat

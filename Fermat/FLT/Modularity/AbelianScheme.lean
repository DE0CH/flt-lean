/-
Modularity/AbelianScheme.lean — own work for the Fermat project (not
vendored from the FLT project).

# Abelian schemes through their functor of points

This module supplies the **first missing piece** of the classical
discharge of `exists_twistedHilbertBlumenthalModuli_of_five_le`
(`Modularity/KhareWintenberger.lean`): the pin carries no notion of an
abelian variety or an abelian scheme at all — a survey of
`.lake/packages/mathlib` on 2026-07-25 found **no** `AbelianVariety`,
`AbelianScheme`, `TateModule`, `HilbertModular`, `Blumenthal` or
`ShimuraVariety` declaration anywhere, and `~/cs/FLT` has none either —
so the Hilbert–Blumenthal moduli input of Taylor 2002 §2 cannot even be
*stated* against the existing library. What follows is the minimum
needed to state it.

## Design: Yoneda, not pullbacks

A commutative group scheme over `S` is, by Yoneda, exactly a lift of the
functor of points `T ↦ Hom_S(T, A)` from sets to abelian groups. We take
that as the DEFINITION (`AbelianSchemeStruct`), rather than writing the
multiplication as a morphism `A ×_S A ⟶ A`, for three reasons:

* it needs no chosen pullbacks and no monoidal structure on `Over S`,
  so it is available immediately at this pin;
* it is *equivalent* to the usual definition (Yoneda is fully faithful,
  and `Hom_S(T, A ×_S A) ≅ Hom_S(T, A) × Hom_S(T, A)` is the universal
  property of the fibre product), so nothing is weakened;
* the object the moduli argument actually consumes — the group of
  geometric points of a fibre, with its Galois action — is then
  literally a special case, with *no* fibre products to form: the fibre
  of `f : A ⟶ X` at an `F`-point `x : Spec F ⟶ X`, evaluated on
  `Spec F̄`, is just the relative point set over `Spec F̄ ⟶ Spec F ⟶ X`.

The Galois action drops out of the same formulation: `Γ_F` acts on
`Spec F̄` over `Spec F`, hence on relative points by precomposition, and
the naturality axiom of the group structure says exactly that this
action is by additive automorphisms. That is the `DistribMulAction`
built below (`AbelianSchemeStruct.geomFibreAction`), and it is what lets
the two twisted level structures of the Hilbert–Blumenthal moduli
problem be written down as conditions on a Galois module.

## Everything is bundled, deliberately

Each mathematical fact proven here is placed inside the *definition* it
justifies rather than exported as a standalone lemma:

* the group axioms of `AbelianSchemeStruct` are consumed by
  `AbelianSchemeStruct.addCommGroup`;
* the two naturality axioms, and the action laws for `specGal`, are
  consumed by `AbelianSchemeStruct.geomFibreAction`, which *is* the
  statement that `Γ_F` acts on the geometric points of a fibre by
  additive automorphisms;
* the ring-action axioms of `Mult` are consumed by `Mult.module`, which
  *is* the statement that the geometric points form an `R`-module;
* naturality of the multiplication is consumed by `Mult.torsion`, whose
  value carries the proof that the `I`-torsion is Galois-stable;
* the facts about the Galois action on roots of unity are consumed by
  `galRootAction`, and the axioms of `DualStruct` / `PolarizationStruct`
  by the `PolarizationStruct.pairing` lemmas, which *are* the classical
  properties of the `𝒪_D`-Weil pairing (see the section docstring there).

This is not decoration: a declaration in this project must lie in the
transitive used-constant cone of the root theorem, and only the
definitions reachable from `IsTwistedHilbertBlumenthalModuli` in
`Modularity/KhareWintenberger.lean` are. Bundling puts the proofs where
the cone can see them, and simultaneously makes the moduli statement
speak about a genuine `Γ_F`-module and a genuine `𝒪_D`-submodule rather
than about a hand-rolled list of equations.

## Producing one: `AbelianSchemeStruct.ofMorphisms`

The Yoneda presentation is what the moduli argument consumes, but it is
not what a producer can hand over — see the section "Building an
`AbelianSchemeStruct` from MORPHISMS" below.  `ofMorphisms` takes the
group law as equations of morphisms (`m : A ×_S A ⟶ A`, `e : S ⟶ A`,
`i : A ⟶ A`) and derives the whole functor-of-points structure, with the
two naturality fields coming out for free.  It is the interface through
which every producer of an abelian scheme in this development is meant to
go.

Everything in this module is PROVEN; it contains no `sorry`.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Fermat

/-! ### Relative points -/

/-- **The `T`-points of `f : A ⟶ S` over a fixed structure morphism
`g : T ⟶ S`**: the value at `(T, g)` of the functor of points of `A` as
an object of `Over S`. -/
abbrev RelPoint {A S : Scheme.{u}} (f : A ⟶ S) {T : Scheme.{u}} (g : T ⟶ S) : Type u :=
  {x : T ⟶ A // x ≫ f = g}

namespace RelPoint

variable {A S : Scheme.{u}} {f : A ⟶ S}

/-- **Precomposition of a relative point along `h : T' ⟶ T`**, together
with an identification `h ≫ g = g'` of the resulting base point. Taking
`g' = h ≫ g` and `hg = rfl` recovers plain functoriality; the extra
identification is what lets the Galois action below be an action on one
fixed type rather than a family of transports. -/
def pre {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (x : RelPoint f g) : RelPoint f g' :=
  ⟨h ≫ x.1, by rw [Category.assoc, x.2, hg]⟩

end RelPoint

/-! ### Abelian schemes -/

/-- **An abelian scheme over `S`, presented by its functor of points.**

The data is a commutative group structure on the relative point set
`RelPoint f g` for every base point `g : T ⟶ S`, natural in `T` — by
Yoneda this is exactly a commutative group-scheme structure on `f` — and
the geometric conditions that `f` be proper, smooth and with
geometrically connected fibres. Those four together are the classical
definition of an abelian scheme (a proper smooth group scheme with
geometrically connected fibres); commutativity is automatic for such an
`f`, and is recorded here rather than derived.

Naturality is stated in the "identified base" form
(`RelPoint.pre h hg`) so that it can be applied directly to the Galois
action on geometric points, where the base point is preserved
propositionally rather than syntactically. -/
structure AbelianSchemeStruct {A S : Scheme.{u}} (f : A ⟶ S) where
  /-- addition of relative points -/
  add : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint f g → RelPoint f g
  /-- the zero section, read as a relative point -/
  zero : ∀ {T : Scheme.{u}} (g : T ⟶ S), RelPoint f g
  /-- inversion of relative points -/
  neg : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint f g
  add_assoc : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x y z : RelPoint f g),
    add (add x y) z = add x (add y z)
  add_comm : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x y : RelPoint f g), add x y = add y x
  zero_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint f g), add (zero g) x = x
  neg_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint f g), add (neg x) x = zero g
  /-- naturality of addition -/
  pre_add : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (x y : RelPoint f g),
    RelPoint.pre h hg (add x y) = add (RelPoint.pre h hg x) (RelPoint.pre h hg y)
  /-- naturality of the zero section -/
  pre_zero : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g'), RelPoint.pre h hg (zero g) = zero g'
  /-- an abelian scheme is proper over its base -/
  proper : IsProper f
  /-- an abelian scheme is smooth over its base -/
  smooth : Smooth f
  /-- the fibres of an abelian scheme are geometrically connected -/
  connected : GeometricallyConnected f

namespace AbelianSchemeStruct

variable {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)

/-- **The abelian group of relative points**: the group axioms of
`AbelianSchemeStruct`, read as an `AddCommGroup` instance on the value
of the functor of points at one base point. -/
@[reducible] def addCommGroup {T : Scheme.{u}} (g : T ⟶ S) :
    AddCommGroup (RelPoint f g) :=
  letI : Add (RelPoint f g) := ⟨ab.add⟩
  letI : Zero (RelPoint f g) := ⟨ab.zero g⟩
  letI : Neg (RelPoint f g) := ⟨ab.neg⟩
  letI grp : AddGroup (RelPoint f g) :=
    AddGroup.ofLeftAxioms ab.add_assoc ab.zero_add ab.neg_add
  { grp with add_comm := ab.add_comm }

end AbelianSchemeStruct

/-! ### Building an `AbelianSchemeStruct` from MORPHISMS

The functor-of-points presentation above is what the moduli argument
consumes, but it is *not* what a producer can hand over: `ab.add` is an
operation on `RelPoint f g` for an ARBITRARY test scheme `T`, and for a
scheme built as a `Proj` there is no functor-of-points description of
`Hom(T, Proj 𝒜)` at this pin — `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/
Functor.lean` supplies only functoriality `Proj ℬ ⟶ Proj 𝒜` in the graded
ring.  So `add` cannot be written down by hand on `T`-points, and every
attempt to do so degenerates into a chain of existentials.

`ofMorphisms` closes that gap in the only direction that is writable: it
takes the group law as EQUATIONS OF MORPHISMS — a multiplication
`m : A ×_S A ⟶ A`, a unit section `e : S ⟶ A`, an inversion `i : A ⟶ A`,
compatible with `f`, with associativity, commutativity, the unit law and
the inverse law stated as equalities of morphisms out of `A ×_S A` and
`A ×_S A ×_S A` — and produces the functor-of-points structure.

Nothing is weakened by going through morphisms: by Yoneda the two
presentations are equivalent, and the converse direction is carried out
in `Fermat/FLT/ModularCurve/X0.lean` (`addHom`, `negHom`,
`add_eq_addHom`, `neg_eq_negHom`), which recovers `m` and `i` from an
`AbelianSchemeStruct`.

**The two naturality fields are FREE.**  `pre_add` and `pre_zero` are the
only fields of `AbelianSchemeStruct` that quantify over a change of test
object, and they are exactly the compatibility of `pullback.lift` with
precomposition (`comp_relPair` below) and the associativity of
composition.  A producer therefore never has to think about naturality at
all — which is the whole reason this bridge exists. -/

namespace AbelianSchemeStruct

open _root_.CategoryTheory.Limits

variable {A S : Scheme.{u}}

/-- **Two relative points over the same base point, paired into a
`T`-point of the fibre square `A ×_S A`.**  This is the universal
property of the pullback read on points, and it is the only construction
the whole bridge below rests on. -/
noncomputable def relPair {f : A ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    (x y : RelPoint f g) : T ⟶ pullback f f :=
  pullback.lift x.1 y.1 (by rw [x.2, y.2])

@[simp] theorem relPair_fst {f : A ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    (x y : RelPoint f g) : relPair x y ≫ pullback.fst f f = x.1 :=
  pullback.lift_fst _ _ _

@[simp] theorem relPair_snd {f : A ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    (x y : RelPoint f g) : relPair x y ≫ pullback.snd f f = y.1 :=
  pullback.lift_snd _ _ _

/-- **`relPair` is natural in the test object.**  This one equation is
what makes the `pre_add` field of `ofMorphisms` automatic. -/
theorem comp_relPair {f : A ⟶ S} {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S}
    {g' : T' ⟶ S} (hg : h ≫ g = g') (x y : RelPoint f g) :
    h ≫ relPair x y = relPair (RelPoint.pre h hg x) (RelPoint.pre h hg y) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, relPair_fst, relPair_fst]
    rfl
  · rw [Category.assoc, relPair_snd, relPair_snd]
    rfl

/-! #### The operations induced on relative points -/

/-- **Addition of relative points induced by a morphism
`m : A ×_S A ⟶ A`**: pair the two points and compose. -/
noncomputable def addOfMor (f : A ⟶ S) (m : pullback f f ⟶ A)
    (hm : m ≫ f = pullback.fst f f ≫ f) {T : Scheme.{u}} {g : T ⟶ S}
    (x y : RelPoint f g) : RelPoint f g :=
  ⟨relPair x y ≫ m, by rw [Category.assoc, hm, ← Category.assoc, relPair_fst, x.2]⟩

@[simp] theorem addOfMor_val (f : A ⟶ S) (m : pullback f f ⟶ A)
    (hm : m ≫ f = pullback.fst f f ≫ f) {T : Scheme.{u}} {g : T ⟶ S}
    (x y : RelPoint f g) : (addOfMor f m hm x y).1 = relPair x y ≫ m := rfl

/-- **The zero relative point induced by a unit section `e : S ⟶ A`**:
the base point composed with `e`. -/
noncomputable def zeroOfMor (f : A ⟶ S) (e : S ⟶ A) (he : e ≫ f = 𝟙 S)
    {T : Scheme.{u}} (g : T ⟶ S) : RelPoint f g :=
  ⟨g ≫ e, by rw [Category.assoc, he, Category.comp_id]⟩

@[simp] theorem zeroOfMor_val (f : A ⟶ S) (e : S ⟶ A) (he : e ≫ f = 𝟙 S)
    {T : Scheme.{u}} (g : T ⟶ S) : (zeroOfMor f e he g).1 = g ≫ e := rfl

/-- **Negation of relative points induced by a morphism `i : A ⟶ A`.** -/
noncomputable def negOfMor (f : A ⟶ S) (i : A ⟶ A) (hi : i ≫ f = f)
    {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint f g) : RelPoint f g :=
  ⟨x.1 ≫ i, by rw [Category.assoc, hi, x.2]⟩

@[simp] theorem negOfMor_val (f : A ⟶ S) (i : A ⟶ A) (hi : i ≫ f = f)
    {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint f g) :
    (negOfMor f i hi x).1 = x.1 ≫ i := rfl

/-! #### The triple fibre product, where associativity lives

Associativity is the one group axiom that cannot be stated on `A ×_S A`:
it is an equation between two morphisms `A ×_S A ×_S A ⟶ A`.  The triple
product is formed as `(A ×_S A) ×_S A` over the structure morphism
`pullback.fst f f ≫ f` of the square; `triFst`, `triSnd`, `triThd` are its
three projections to `A`. -/

/-- **The threefold fibre product `A ×_S A ×_S A`**, formed as
`(A ×_S A) ×_S A`. -/
noncomputable abbrev triProd (f : A ⟶ S) : Scheme.{u} :=
  pullback (pullback.fst f f ≫ f) f

/-- The first projection of `triProd f`. -/
noncomputable def triFst (f : A ⟶ S) : triProd f ⟶ A :=
  pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f

/-- The second projection of `triProd f`. -/
noncomputable def triSnd (f : A ⟶ S) : triProd f ⟶ A :=
  pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f

/-- The third projection of `triProd f`. -/
noncomputable def triThd (f : A ⟶ S) : triProd f ⟶ A :=
  pullback.snd (pullback.fst f f ≫ f) f

/-- All three projections of `triProd f` lie over the same base point:
first versus third. -/
theorem triFst_comp (f : A ⟶ S) : triFst f ≫ f = triThd f ≫ f := by
  rw [triFst, triThd, Category.assoc]
  exact pullback.condition

/-- All three projections of `triProd f` lie over the same base point:
second versus third. -/
theorem triSnd_comp (f : A ⟶ S) : triSnd f ≫ f = triThd f ≫ f := by
  rw [triSnd, triThd, Category.assoc, ← pullback.condition (f := f) (g := f)]
  exact pullback.condition

/-- All three projections of `triProd f` lie over the same base point:
first versus second. -/
theorem triFst_comp_snd (f : A ⟶ S) : triFst f ≫ f = triSnd f ≫ f :=
  (triFst_comp f).trans (triSnd_comp f).symm

/-- **`(x + y) + z` as a morphism `A ×_S A ×_S A ⟶ A`.** -/
noncomputable def triAddLeft (f : A ⟶ S) (m : pullback f f ⟶ A)
    (hm : m ≫ f = pullback.fst f f ≫ f) : triProd f ⟶ A :=
  pullback.lift
      (pullback.lift (triFst f) (triSnd f) (triFst_comp_snd f) ≫ m) (triThd f)
      (by rw [Category.assoc, hm, ← Category.assoc, pullback.lift_fst]
          exact triFst_comp f) ≫
    m

/-- **`x + (y + z)` as a morphism `A ×_S A ×_S A ⟶ A`.** -/
noncomputable def triAddRight (f : A ⟶ S) (m : pullback f f ⟶ A)
    (hm : m ≫ f = pullback.fst f f ≫ f) : triProd f ⟶ A :=
  pullback.lift (triFst f)
      (pullback.lift (triSnd f) (triThd f) (triSnd_comp f) ≫ m)
      (by rw [Category.assoc, hm, ← Category.assoc, pullback.lift_fst]
          exact triFst_comp_snd f) ≫
    m

/-! #### The bridge -/

/-- **An `AbelianSchemeStruct` from morphism-level group-law data**
(PROVEN).

The data is the classical one: a multiplication `m : A ×_S A ⟶ A`, a unit
section `e : S ⟶ A` and an inversion `i : A ⟶ A`, each compatible with the
structure morphism `f` (`hm`, `he`, `hi`), together with the four group
axioms as EQUATIONS OF MORPHISMS:

* `hassoc` — `triAddLeft = triAddRight` on `A ×_S A ×_S A`;
* `hcomm` — `m` is invariant under the swap of the two factors;
* `hunit` — `m ∘ (e ∘ f, id) = id` on `A`;
* `hinv` — `m ∘ (i, id) = e ∘ f` on `A`.

Everything the functor-of-points presentation demands is then derived.
In particular the two NATURALITY fields, `pre_add` and `pre_zero`, cost
the caller nothing: they are `comp_relPair` and the associativity of
composition, because `add` is by construction a composite with the fixed
morphism `m`.  That is precisely why the morphism-level route is writable
where the point-level one is not.

Faithfulness note: this is a genuine bridge, not a weakening.  The
hypotheses are strictly stronger than the conclusion's group axioms
(Yoneda embeds `A ×_S A ⟶ A` into the natural transformations, and the
functor of points of `A ×_S A ×_S A` is the triple product of that of
`A`), so a consumer of the resulting `AbelianSchemeStruct` gets exactly
the structure it would have got from a hand-built one. -/
noncomputable def ofMorphisms (f : A ⟶ S) (m : pullback f f ⟶ A) (e : S ⟶ A)
    (i : A ⟶ A)
    (hm : m ≫ f = pullback.fst f f ≫ f)
    (he : e ≫ f = 𝟙 S)
    (hi : i ≫ f = f)
    (hassoc : triAddLeft f m hm = triAddRight f m hm)
    (hcomm : pullback.lift (pullback.snd f f) (pullback.fst f f)
      pullback.condition.symm ≫ m = m)
    (hunit : pullback.lift (f ≫ e) (𝟙 A)
      (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A)
    (hinv : pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp]) ≫ m = f ≫ e)
    (hproper : IsProper f) (hsmooth : Smooth f)
    (hconn : GeometricallyConnected f) :
    AbelianSchemeStruct f where
  add := addOfMor f m hm
  zero := zeroOfMor f e he
  neg := negOfMor f i hi
  add_assoc x y z := by
    apply Subtype.ext
    simp only [addOfMor_val]
    have hw : relPair x y ≫ pullback.fst f f ≫ f = z.1 ≫ f := by
      rw [← Category.assoc, relPair_fst, x.2, z.2]
    set w : _ ⟶ triProd f := pullback.lift (relPair x y) z.1 hw with hwdef
    have hw1 : w ≫ triFst f = x.1 := by
      rw [triFst, ← Category.assoc, hwdef, pullback.lift_fst, relPair_fst]
    have hw2 : w ≫ triSnd f = y.1 := by
      rw [triSnd, ← Category.assoc, hwdef, pullback.lift_fst, relPair_snd]
    have hw3 : w ≫ triThd f = z.1 := by
      rw [triThd, hwdef, pullback.lift_snd]
    have hL : w ≫ triAddLeft f m hm
        = relPair (addOfMor f m hm x y) z ≫ m := by
      rw [triAddLeft, ← Category.assoc]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, relPair_fst, addOfMor_val,
          ← Category.assoc]
        congr 1
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, pullback.lift_fst, relPair_fst]; exact hw1
        · rw [Category.assoc, pullback.lift_snd, relPair_snd]; exact hw2
      · rw [Category.assoc, pullback.lift_snd, relPair_snd]; exact hw3
    have hR : w ≫ triAddRight f m hm
        = relPair x (addOfMor f m hm y z) ≫ m := by
      rw [triAddRight, ← Category.assoc]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, relPair_fst]; exact hw1
      · rw [Category.assoc, pullback.lift_snd, relPair_snd, addOfMor_val,
          ← Category.assoc]
        congr 1
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, pullback.lift_fst, relPair_fst]; exact hw2
        · rw [Category.assoc, pullback.lift_snd, relPair_snd]; exact hw3
    rw [← hL, ← hR, hassoc]
  add_comm x y := by
    apply Subtype.ext
    simp only [addOfMor_val]
    have hswap : relPair x y ≫ pullback.lift (pullback.snd f f)
        (pullback.fst f f) pullback.condition.symm = relPair y x := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, relPair_snd, relPair_fst]
      · rw [Category.assoc, pullback.lift_snd, relPair_fst, relPair_snd]
    rw [← hswap, Category.assoc, hcomm]
  zero_add x := by
    apply Subtype.ext
    simp only [addOfMor_val]
    have hz : x.1 ≫ pullback.lift (f ≫ e) (𝟙 A)
        (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
        = relPair (zeroOfMor f e he _) x := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, relPair_fst, zeroOfMor_val,
          ← Category.assoc, x.2]
      · rw [Category.assoc, pullback.lift_snd, relPair_snd, Category.comp_id]
    rw [← hz, Category.assoc, hunit, Category.comp_id]
  neg_add x := by
    apply Subtype.ext
    simp only [addOfMor_val, zeroOfMor_val]
    have hn : x.1 ≫ pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp])
        = relPair (negOfMor f i hi x) x := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, relPair_fst, negOfMor_val]
      · rw [Category.assoc, pullback.lift_snd, relPair_snd, Category.comp_id]
    rw [← hn, Category.assoc, hinv, ← Category.assoc, x.2]
  pre_add := by
    intro T' T h g g' hg x y
    apply Subtype.ext
    show h ≫ relPair x y ≫ m
        = relPair (RelPoint.pre h hg x) (RelPoint.pre h hg y) ≫ m
    rw [← Category.assoc, comp_relPair h hg x y]
  pre_zero := by
    intro T' T h g g' hg
    apply Subtype.ext
    show h ≫ g ≫ e = g' ≫ e
    rw [← Category.assoc, hg]
  proper := hproper
  smooth := hsmooth
  connected := hconn

end AbelianSchemeStruct

/-! ### Geometric points of a fibre, and the Galois action on them -/

/-- **`Spec` of an algebraic closure, over `Spec` of the field.** -/
noncomputable def specAlgClos (F : Type u) [Field F] :
    Spec (CommRingCat.of (AlgebraicClosure F)) ⟶ Spec (CommRingCat.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))

/-- **The automorphism of `Spec F̄` induced by an element of `Γ_F`.**
`Field.absoluteGaloisGroup F` is by definition
`AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, so `σ` is in particular a
ring endomorphism of `F̄` fixing `F`. -/
noncomputable def specGal {F : Type u} [Field F] (σ : Field.absoluteGaloisGroup F) :
    Spec (CommRingCat.of (AlgebraicClosure F)) ⟶
      Spec (CommRingCat.of (AlgebraicClosure F)) :=
  Spec.map (CommRingCat.ofHom
    ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom))

/-- `specGal` is the identity at the identity of `Γ_F`. -/
@[simp] theorem specGal_one (F : Type u) [Field F] :
    specGal (1 : Field.absoluteGaloisGroup F) = 𝟙 _ := by
  rw [specGal, ← Spec.map_id]
  congr 1

/-- `specGal` turns multiplication in `Γ_F` into composition — note the
order: `Spec` is contravariant and the group law of
`AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F` is
`(σ * τ) x = σ (τ x)`, and the two reversals cancel. -/
theorem specGal_mul {F : Type u} [Field F] (σ τ : Field.absoluteGaloisGroup F) :
    specGal (σ * τ) = specGal σ ≫ specGal τ := by
  rw [specGal, specGal, specGal, ← Spec.map_comp]
  congr 1

/-- `Spec F̄ ⟶ Spec F` is invariant under the Galois action: this is the
statement that `σ` fixes `F` pointwise. -/
theorem specGal_comp_specAlgClos {F : Type u} [Field F]
    (σ : Field.absoluteGaloisGroup F) :
    specGal σ ≫ specAlgClos F = specAlgClos F := by
  rw [specGal, specAlgClos, ← Spec.map_comp]
  congr 1
  ext y
  exact (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).commutes y

/-- The base point of a geometric fibre is Galois-invariant. -/
theorem specGal_comp_base {F : Type u} [Field F] {S : Scheme.{u}}
    (x : Spec (CommRingCat.of F) ⟶ S) (σ : Field.absoluteGaloisGroup F) :
    specGal σ ≫ (specAlgClos F ≫ x) = specAlgClos F ≫ x := by
  rw [← Category.assoc, specGal_comp_specAlgClos]

/-- **The geometric points of the fibre of `f : A ⟶ S` at an `F`-point
`x : Spec F ⟶ S`**: the `Spec F̄`-points of `A` lying over `x`. No fibre
product is formed — the functor-of-points description of the fibre is
this relative point set, by the universal property of the pullback. -/
abbrev GeomFibrePt {A S : Scheme.{u}} (f : A ⟶ S) {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S) : Type u :=
  RelPoint f (specAlgClos F ≫ x)

namespace AbelianSchemeStruct

variable {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
variable {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)

/-- **The geometric points of a fibre form a `Γ_F`-module.**

`σ · y` is `y` precomposed with `Spec σ`; under the identification of
`F̄`-points of an affine `A` with `F`-algebra maps `𝒪(A) → F̄` this is the
usual action `φ ↦ σ ∘ φ`. That it is an ACTION is `specGal_one` and
`specGal_mul`; that it is by ADDITIVE automorphisms is exactly the
naturality of the group structure (`pre_zero`, `pre_add`) read at the
Galois automorphisms of `Spec F̄`.

This bundling is the point of the module: the twisted level structures
of the Hilbert–Blumenthal moduli problem are conditions on a
`Γ_F`-module, and this definition is what makes that phrase mean
something. -/
@[reducible] noncomputable def geomFibreAction :
    letI := ab.addCommGroup (specAlgClos F ≫ x)
    DistribMulAction (Field.absoluteGaloisGroup F) (GeomFibrePt f x) :=
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  { smul := fun σ y => RelPoint.pre (specGal σ) (specGal_comp_base x σ) y
    one_smul := fun y => by
      apply Subtype.ext
      show specGal (1 : Field.absoluteGaloisGroup F) ≫ y.1 = y.1
      rw [specGal_one, Category.id_comp]
    mul_smul := fun σ τ y => by
      apply Subtype.ext
      show specGal (σ * τ) ≫ y.1 = specGal σ ≫ specGal τ ≫ y.1
      rw [specGal_mul, Category.assoc]
    smul_zero := fun σ => ab.pre_zero (specGal σ) (specGal_comp_base x σ)
    smul_add := fun σ y z => ab.pre_add (specGal σ) (specGal_comp_base x σ) y z }

/-- **The Galois action on the geometric points of a fibre**, as a plain
function — the underlying scalar multiplication of `geomFibreAction`.
Level-structure conditions are written with this rather than with `•`
so that they can be stated without carrying the `AddCommGroup` instance
around. -/
noncomputable def galSMul (σ : Field.absoluteGaloisGroup F) (y : GeomFibrePt f x) :
    GeomFibrePt f x :=
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  letI := ab.geomFibreAction x
  σ • y

/-- `galSMul` is precomposition with `Spec σ`, by definition. -/
theorem galSMul_def (σ : Field.absoluteGaloisGroup F) (y : GeomFibrePt f x) :
    ab.galSMul x σ y = RelPoint.pre (specGal σ) (specGal_comp_base x σ) y := rfl

end AbelianSchemeStruct

/-! ### Multiplications: the real-multiplication datum -/

/-- **A multiplication of an abelian scheme by a commutative ring `R`**:
a ring action of `R` on the functor of points by group endomorphisms,
natural in the test object. For `R = 𝒪_D` with `D` totally real of degree
equal to the relative dimension this is exactly the *real
multiplication* datum of a Hilbert–Blumenthal abelian scheme; by Yoneda
it is the same thing as a ring homomorphism `R → End_S(A)`.

Naturality (`pre_act`) is what makes the induced action on the geometric
points of a fibre commute with the Galois action, which is what lets the
`λ`-torsion of a fibre be a Galois submodule and hence carry a level
structure; it is consumed by `Mult.torsion` below. -/
structure Mult {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    (R : Type*) [CommRing R] where
  /-- the endomorphism of the functor of points attached to `a : R` -/
  act : ∀ {T : Scheme.{u}} {g : T ⟶ S}, R → RelPoint f g → RelPoint f g
  /-- `a ↦ act a` is additive -/
  act_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (a b : R) (y : RelPoint f g),
    act (a + b) y = ab.add (act a y) (act b y)
  /-- `a ↦ act a` is multiplicative -/
  act_mul : ∀ {T : Scheme.{u}} {g : T ⟶ S} (a b : R) (y : RelPoint f g),
    act (a * b) y = act a (act b y)
  /-- `a ↦ act a` sends `1` to the identity -/
  act_one : ∀ {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g), act (1 : R) y = y
  /-- each `act a` is a group endomorphism -/
  act_addPt : ∀ {T : Scheme.{u}} {g : T ⟶ S} (a : R) (y z : RelPoint f g),
    act a (ab.add y z) = ab.add (act a y) (act a z)
  /-- naturality in the test object -/
  pre_act : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (a : R) (y : RelPoint f g),
    RelPoint.pre h hg (act a y) = act a (RelPoint.pre h hg y)

namespace Mult

variable {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
variable {R : Type u} [CommRing R] (m : Mult ab R)

/-- **The relative points of a scheme with multiplication by `R` form an
`R`-module.** `zero_smul` and `smul_zero` are not axioms of `Mult`: an
additive map kills zero, so both follow from `act_add` and `act_addPt`
by cancellation. -/
@[reducible] def module {T : Scheme.{u}} (g : T ⟶ S) :
    letI := ab.addCommGroup g
    Module R (RelPoint f g) :=
  letI := ab.addCommGroup g
  { smul := m.act
    one_smul := m.act_one
    mul_smul := m.act_mul
    smul_zero := fun a => by
      have h := m.act_addPt a (ab.zero g) (ab.zero g)
      have hz : ab.add (ab.zero g) (ab.zero g) = ab.zero g := ab.zero_add _
      rw [hz] at h
      show m.act a (0 : RelPoint f g) = 0
      exact add_right_cancel (b := m.act a (0 : RelPoint f g))
        (h.symm.trans (zero_add _).symm)
    smul_add := fun a y z => m.act_addPt a y z
    add_smul := fun a b y => m.act_add a b y
    zero_smul := fun y => by
      have h := m.act_add (0 : R) (0 : R) y
      rw [zero_add] at h
      show m.act (0 : R) y = 0
      exact add_right_cancel (b := m.act (0 : R) y)
        (h.symm.trans (zero_add _).symm) }

/-- **The multiplication commutes with the Galois action** on the
geometric points of a fibre: naturality read at the Galois automorphisms
of `Spec F̄`. -/
theorem galSMul_act {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (σ : Field.absoluteGaloisGroup F) (a : R) (y : GeomFibrePt f x) :
    ab.galSMul x σ (m.act a y) = m.act a (ab.galSMul x σ y) :=
  m.pre_act (specGal σ) (specGal_comp_base x σ) a y

/-- **The `I`-torsion of a geometric fibre, as a Galois-stable set**, for
an ideal `I ≤ R`: the geometric points killed by every element of `I`,
i.e. `Submodule.torsionBySet` for the `R`-module structure of
`Mult.module`, packaged with the proof that the Galois action preserves
it (which is naturality of the multiplication, `pre_act`).

For `I = λ` a maximal ideal of `𝒪_D` over `ℓ` this is `A[λ]`, the Galois
module carrying the `ℓ`-adic level structure of the Hilbert–Blumenthal
moduli problem — and it is a Galois module precisely because of the
second component of this value. -/
noncomputable def torsion {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R) :
    {s : Set (GeomFibrePt f x) //
      ∀ (σ : Field.absoluteGaloisGroup F) (y : GeomFibrePt f x),
        y ∈ s → ab.galSMul x σ y ∈ s} :=
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  letI := m.module (specAlgClos F ≫ x)
  ⟨↑(Submodule.torsionBySet R (GeomFibrePt f x) (I : Set R)), by
    intro σ y hy
    have hy' : ∀ a : (I : Set R), (a : R) • y = 0 :=
      (Submodule.mem_torsionBySet_iff _ _).mp hy
    refine SetLike.mem_coe.mpr ((Submodule.mem_torsionBySet_iff _ _).mpr ?_)
    intro a
    show m.act (a : R) (ab.galSMul x σ y) = 0
    rw [← m.galSMul_act x σ (a : R) y]
    have hzero : m.act (a : R) y = 0 := hy' a
    rw [hzero]
    exact (ab.geomFibreAction x).smul_zero σ⟩

end Mult

/-! ### The Galois action on roots of unity

The Weil pairing below takes values in the roots of unity of `F̄`, and the
whole arithmetic content of the pairing is that `Γ_F` acts on that target
through the CYCLOTOMIC CHARACTER and on nothing else. So the target needs
its Galois action before the pairing can be stated. -/

/-- **The action of `σ ∈ Γ_F` on the `n`-th roots of unity of `F̄`.**
`rootsOfUnity n M` is a subgroup of `Mˣ`, and `σ` is a ring automorphism
of `F̄`, so it acts on units; it preserves the subgroup because it is
multiplicative, which is the proof carried in the second component. -/
noncomputable def galRoot {F : Type u} [Field F] {n : ℕ}
    (σ : Field.absoluteGaloisGroup F) (ζ : rootsOfUnity n (AlgebraicClosure F)) :
    rootsOfUnity n (AlgebraicClosure F) :=
  ⟨Units.map ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom.toMonoidHom)
      (ζ : (AlgebraicClosure F)ˣ), by
    rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity n _).mp ζ.2, map_one]⟩

/-- `galRoot` is trivial at the identity of `Γ_F`. -/
@[simp] theorem galRoot_one {F : Type u} [Field F] {n : ℕ}
    (ζ : rootsOfUnity n (AlgebraicClosure F)) :
    galRoot (1 : Field.absoluteGaloisGroup F) ζ = ζ := by
  apply Subtype.ext; apply Units.ext; rfl

/-- `galRoot` turns multiplication in `Γ_F` into composition. Unlike
`specGal_mul` there is no reversal here: this is an action on ELEMENTS of
`F̄`, not on `Spec F̄`, so the contravariance of `Spec` does not intervene. -/
theorem galRoot_mul {F : Type u} [Field F] {n : ℕ}
    (σ τ : Field.absoluteGaloisGroup F) (ζ : rootsOfUnity n (AlgebraicClosure F)) :
    galRoot (σ * τ) ζ = galRoot σ (galRoot τ ζ) := by
  apply Subtype.ext; apply Units.ext; rfl

/-- Each `galRoot σ` is multiplicative. -/
theorem galRoot_mul_apply {F : Type u} [Field F] {n : ℕ}
    (σ : Field.absoluteGaloisGroup F) (ζ ξ : rootsOfUnity n (AlgebraicClosure F)) :
    galRoot σ (ζ * ξ) = galRoot σ ζ * galRoot σ ξ := by
  apply Subtype.ext; apply Units.ext
  exact map_mul _ _ _

/-- Each `galRoot σ` fixes `1`. -/
@[simp] theorem galRoot_one_elt {F : Type u} [Field F] {n : ℕ}
    (σ : Field.absoluteGaloisGroup F) :
    galRoot σ (1 : rootsOfUnity n (AlgebraicClosure F)) = 1 := by
  apply Subtype.ext; apply Units.ext
  exact map_one _

/-- **`Γ_F` acts on `μ_n(F̄)` by group automorphisms.** As elsewhere in
this module the facts just proven are consumed by the definition they
justify, rather than left as loose lemmas. -/
@[reducible] noncomputable def galRootAction (F : Type u) [Field F] (n : ℕ) :
    MulDistribMulAction (Field.absoluteGaloisGroup F) (rootsOfUnity n (AlgebraicClosure F)) where
  smul := galRoot
  one_smul := galRoot_one
  mul_smul := galRoot_mul
  smul_mul := galRoot_mul_apply
  smul_one := galRoot_one_elt

/-! ### The dual abelian scheme, polarizations and the `𝒪_D`-Weil pairing

WHY THIS SECTION EXISTS (2026-07-26). Two independent notes in this
development recorded the same absence and named the same repair:

* `Modularity/TateModule.lean` (at `det_eq_cyclotomicCharacter_of_tateFrame`)
  — "there is no dual abelian scheme, no polarization, no Cartier duality
  and no Weil pairing over a general base … `AbelianSchemeStruct` carries
  only `add`/`zero`/`neg` together with `proper`/`smooth`/`connected` — no
  line bundles, so *polarization* is not even stateable yet";
* the ATOMICITY AUDIT of
  `exists_twistedHilbertBlumenthalModuliTwist_of_datum`
  (`Modularity/KhareWintenberger.lean`) — "the prerequisite that would
  unlock it is nameable: a POLARIZATION and `𝒪_D`-WEIL PAIRING datum on
  `Fermat.AbelianSchemeStruct` / `Fermat.Mult` (an extension of
  `Modularity/AbelianScheme.lean`)".

This section is that extension.

DESIGN: THE PAIRING LIVES ON TORSION, NOT ON LINE BUNDLES. Constructing
`A^∨ = Pic⁰_{A/S}` as a scheme is Grothendieck's representability theorem
for the Picard functor, which is far out of reach at this pin — and it is
NOT what the consumers need. What they consume is the pairing on the
`I`-torsion of a geometric fibre together with its `Γ_F`-equivariance. So
the dual is presented here the way `AbelianSchemeStruct` itself is
presented: as a BUNDLED DATUM — a second abelian scheme over the same
base, carrying the transposed multiplication and a Weil pairing with its
axioms — rather than constructed. That is the same modelling decision the
rest of this module already makes, and it keeps the interface honest:
nothing here claims that a dual EXISTS, only what it means to have one.

Consequently `DualStruct` and `PolarizationStruct` are hypotheses, and
everything proven from them (the whole `PolarizationStruct` namespace) is
a genuine consequence of those hypotheses.

WHY THE PAIRING TAKES RAW POINTS. The `I`-torsion is `Mult.torsion`, a
`Set` carrying a Galois-stability proof; this module deliberately
registers no global `AddCommGroup`/`Module` instances on relative points
(they are `letI`-bound inside the definitions that need them, so that the
cone stays clean). Rather than reintroduce that plumbing at every
axiom, `weil` is a function on ALL geometric points whose axioms are
asserted only for torsion arguments; its value off the torsion is
unconstrained and no consumer may rely on it.

NON-VACUITY. The content of this layer is carried by TWO nondegeneracy
axioms, one in each structure, and NEITHER implies the other.

* `DualStruct.weil_nondegenerate` is the content of `DualStruct`:
  without it, `weil ≡ 1` would satisfy every other axiom of that
  structure.
* `PolarizationStruct.weil_hom_nondegenerate` is the content of
  `PolarizationStruct`, and it was MISSING until 2026-07-27. Without it
  the entire structure was satisfied by the CONSTANT ZERO MAP over EVERY
  datum — field by field, see the refutation test in its docstring — so
  `PolarizationStruct` added nothing whatever over `DualStruct`, and its
  induced `pairing` was permitted to be identically `1`. Every theorem
  that "used" it was using nothing.

  Its FIRST form overshot in the other direction and had to be repaired
  again the same day: quantified over all ideals, it forced `hom` to be an
  isomorphism, i.e. a PRINCIPAL `𝒪_D`-polarization, which a
  Hilbert–Blumenthal abelian variety need not admit — so
  `∃ d, Nonempty (PolarizationStruct d)` was FALSE whenever `h⁺(D) > 1`.
  `PolarizationStruct` is now indexed by a SET `𝒩` of levels and asserts
  nondegeneracy only there. See its docstring for the argument in both
  directions and for why the set, rather than a single ideal, is the right
  index.

`weil_nondegenerate` does NOT rescue that: it is nondegeneracy of the
canonical `A × A^∨` pairing, and says nothing about the composite
`A[I] × A[I] ⟶ μ_n` obtained by pushing the second variable through a
degenerate `hom`. Nondegeneracy of the INDUCED pairing is what the
level-structure condition of the Hilbert–Blumenthal moduli problem needs
— the condition that cuts the split moduli space down to ONE geometric
component instead of one per pairing value.

MISSING AXIOM, DELIBERATELY NOT ADDED HERE: COMPATIBILITY ALONG THE
`I`-ADIC TOWER. `DualStruct.weil` quantifies its ideal and its integer
INSIDE the field, so `weil x (I ^ k) (q ^ k)` is available at every level
with all five axioms — the whole `I ^ k` tower already exists, and any
note claiming that this layer "is level one" is wrong about the levels.
What is genuinely absent is any axiom relating CONSECUTIVE levels along
the transition map `· π`, for `π` a uniformiser of `I`: something of the
shape

    weil x (I ^ (k+1)) (q ^ (k+1)) _ (m.act π y) (d.dualMult.act π z)
      = weil x (I ^ k) (q ^ k) _ y' z'

identifying the level-`k+1` pairing of `π`-multiples with the level-`k`
pairing. That compatibility is what makes the pairings pass to the
inverse limit and so gives a pairing on the TATE MODULE `T_I A`, which is
what `det_eq_cyclotomicCharacter_of_tateFrame`
(`Modularity/TateModule.lean`) ultimately consumes. The axiom belongs on
`DualStruct`; adding it is a `DualStruct` restructuring and was out of
scope for the 2026-07-27 `PolarizationStruct` repair. It is recorded here
so that the next owner of `DualStruct` does not have to rediscover it.

WHAT CANNOT BE SAID IN THIS VOCABULARY AT ALL. `DualStruct.weil` is
`μ_n(F̄)`-valued, so pinning a pairing VALUE (`⟨α e₀, α e₁⟩ = ζ`) is NOT
a ℚ-rational condition: the target has no ℚ-structure and `Γ_F` moves `ζ`
through the cyclotomic character. Consequently a CANONICAL normalized
level module cannot be written here — only a BUNDLED one, carrying its
normalization as data. Do not design against the belief that a
normalization is expressible; that belief is what "the vocabulary is
unblocked" means, and it is true only in the bundled sense.

CONE STATUS (corrected 2026-07-27; the previous version of this
paragraph said none of these declarations were in the cone, which is now
half wrong). `DualStruct`, `PolarizationStruct`,
`PolarizationStruct.pairing` and `galRoot` ARE in the used-constant cone
of `fermat_last_theorem` as of commit `3a3e74cc`, which cut
`exists_twistedHilbertBlumenthalModuliTwist_of_datum`
(`Modularity/KhareWintenberger.lean`) into leaves that take them as
hypotheses and in existentials. What is NOT in the cone is the PROVEN
material of this section — `DualStruct.weil_zero_right`, and
`PolarizationStruct.pairing_def`, `pairing_add_left`, `pairing_add_right`,
`pairing_self`, `galSMul_hom`, `pairing_gal`, `pairing_act`,
`pairing_nondegenerate`, `exists_pairing_ne_one` and
`torsion_eq_zero_of_hom_eq_zero` — which is consumed only by proofs that
are still `sorry` (the two leaves of that cut,
`exists_realAbelianSchemeWithRealMultiplication`, and
`det_eq_cyclotomicCharacter_of_tateFrame`). That material must NOT be
swept as free-floating before its consumers are proven. -/

/-- **A dual abelian scheme, presented together with its Weil pairing.**

The data is a second abelian scheme `dualMap : dualScheme ⟶ S` over the
same base, carrying the transposed `R`-multiplication, together with the
canonical pairing

  `A[I] × A^∨[I] ⟶ μ_n(F̄)`

on the `I`-torsion of each geometric fibre, for every `n` killed by `I`.
The axioms are bi-additivity, `Γ_F`-equivariance, `R`-adjointness and
nondegeneracy — the classical properties of the Weil pairing.

`weil_act` is the statement that the Rosati involution attached to the
pairing restricts to the IDENTITY on `R`. For `R = 𝒪_D` with `D` totally
real that is automatic classically (the Rosati involution is positive, and
a totally real field admits no nontrivial positive involution), and it is
what makes the induced pairing `𝒪_D`-bilinear rather than merely
`ℤ`-bilinear. -/
structure DualStruct {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    {R : Type u} [CommRing R] (m : Mult ab R) where
  /-- the underlying scheme of the dual -/
  dualScheme : Scheme.{u}
  /-- the structure morphism of the dual -/
  dualMap : dualScheme ⟶ S
  /-- the dual is itself an abelian scheme over `S` -/
  dualAb : AbelianSchemeStruct dualMap
  /-- the transposed multiplication -/
  dualMult : Mult dualAb R
  /-- the Weil pairing on `I`-torsion of a geometric fibre -/
  weil : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
      (I : Ideal R) (n : ℕ), (n : R) ∈ I →
      GeomFibrePt f x → GeomFibrePt dualMap x → rootsOfUnity n (AlgebraicClosure F)
  /-- additivity in the first variable -/
  weil_add_left : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
      (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I)
      (y y' : GeomFibrePt f x) (z : GeomFibrePt dualMap x),
      y ∈ (m.torsion x I).1 → y' ∈ (m.torsion x I).1 → z ∈ (dualMult.torsion x I).1 →
      weil x I n hn (ab.add y y') z = weil x I n hn y z * weil x I n hn y' z
  /-- additivity in the second variable -/
  weil_add_right : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
      (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I)
      (y : GeomFibrePt f x) (z z' : GeomFibrePt dualMap x),
      y ∈ (m.torsion x I).1 → z ∈ (dualMult.torsion x I).1 → z' ∈ (dualMult.torsion x I).1 →
      weil x I n hn y (dualAb.add z z') = weil x I n hn y z * weil x I n hn y z'
  /-- `Γ_F`-equivariance: the Galois group acts on the target through its
  action on roots of unity, i.e. through the cyclotomic character -/
  weil_gal : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
      (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I) (σ : Field.absoluteGaloisGroup F)
      (y : GeomFibrePt f x) (z : GeomFibrePt dualMap x),
      y ∈ (m.torsion x I).1 → z ∈ (dualMult.torsion x I).1 →
      weil x I n hn (ab.galSMul x σ y) (dualAb.galSMul x σ z)
        = galRoot σ (weil x I n hn y z)
  /-- `R`-adjointness: the Rosati involution is trivial on `R` -/
  weil_act : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
      (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I) (a : R)
      (y : GeomFibrePt f x) (z : GeomFibrePt dualMap x),
      y ∈ (m.torsion x I).1 → z ∈ (dualMult.torsion x I).1 →
      weil x I n hn (m.act a y) z = weil x I n hn y (dualMult.act a z)
  /-- nondegeneracy in the first variable — the axiom that carries the
  content, and without which `weil ≡ 1` would satisfy all the others -/
  weil_nondegenerate : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
      (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I) (y : GeomFibrePt f x),
      y ∈ (m.torsion x I).1 →
      (∀ z : GeomFibrePt dualMap x, z ∈ (dualMult.torsion x I).1 →
        weil x I n hn y z = 1) →
      y = ab.zero (specAlgClos F ≫ x)

namespace DualStruct

variable {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
variable {R : Type u} [CommRing R] {m : Mult ab R} (d : DualStruct ab m)
variable {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
variable (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I)

/-- **The canonical pairing is trivial against the zero section of the
dual.** Additivity in the second variable at `z = z' = 0` gives
`w = w * w` in the group `μ_n(F̄)`, whence `w = 1`; the zero section is
`I`-torsion because `Mult.torsion` is a `Submodule`.

This is the load-bearing half of the zero-map refutation test recorded on
`PolarizationStruct`: it is exactly why the constant zero map used to
satisfy that structure's `weil_self` axiom for free. -/
theorem weil_zero_right (y : GeomFibrePt f x) (hy : y ∈ (m.torsion x I).1) :
    d.weil x I n hn y (d.dualAb.zero (specAlgClos F ≫ x)) = 1 := by
  have hz : d.dualAb.zero (specAlgClos F ≫ x) ∈ (d.dualMult.torsion x I).1 := by
    letI := d.dualAb.addCommGroup (specAlgClos F ≫ x)
    letI := d.dualMult.module (specAlgClos F ≫ x)
    exact (Submodule.torsionBySet R (GeomFibrePt d.dualMap x) (I : Set R)).zero_mem
  have h := d.weil_add_right x I n hn y (d.dualAb.zero (specAlgClos F ≫ x))
    (d.dualAb.zero (specAlgClos F ≫ x)) hy hz hz
  rw [d.dualAb.zero_add] at h
  exact left_eq_mul.mp h

end DualStruct

/-- **A polarization**: an `R`-linear symmetric isogeny `A ⟶ A^∨`.

By Yoneda a homomorphism of abelian schemes is exactly a natural additive
transformation of functors of points, which is what `hom`, `hom_add` and
`pre_hom` say; `hom_act` says it commutes with the real multiplication,
which is the `𝒪_D`-LINEARITY of the polarization; and `weil_self` says
the induced pairing is alternating, which is the symmetry of the
polarization read through the Weil pairing.

Classically such a polarization exists on any abelian variety over a
field (every abelian variety is projective, and the `𝒪_D`-average of a
polarization is `𝒪_D`-linear because `D` is totally real). Existence is
NOT asserted here — this is the datum, not a construction.

**CONTENT, AND THE STANDING REFUTATION TEST (repaired 2026-07-27).**

Before that date this structure carried NO CONTENT AT ALL: it was
satisfied by the CONSTANT ZERO MAP `hom := fun _ => d.dualAb.zero g`
over every datum whatsoever, field by field —

* `hom_add` by `zero_add`;
* `pre_hom` by `pre_zero`;
* `hom_act` by the `act a 0 = 0` derivation inside `Mult.module`;
* `hom_torsion` because `Mult.torsion` is a `Submodule`, so contains `0`;
* `weil_self` by `DualStruct.weil_zero_right` — `weil_add_right` at
  `z = z' = 0` gives `w = w * w` in a group.

So `PolarizationStruct` added nothing over `DualStruct` and its induced
`pairing` was permitted to be identically `1`.

`weil_hom_nondegenerate` is the repair, and **the refutation test is a
THEOREM, not prose**: `PolarizationStruct.torsion_eq_zero_of_hom_eq_zero`
proves that a `PolarizationStruct` whose `hom` is the zero map forces
EVERY `I`-torsion point of EVERY geometric fibre to vanish. The zero map
therefore no longer satisfies this structure over any datum possessing a
nonzero torsion point — i.e. over any datum the moduli problem cares
about. The one surviving case is the honest one, where `A[I]` really is
trivial (e.g. `I = R`, since `1 ∈ R` kills every point) and a
nondegenerate alternating pairing on `A[I]` is vacuously available.
**Anyone who weakens this structure must re-run that theorem**; a
structure whose only proof of content is prose drifts back.

**WHAT IS DELIBERATELY NOT ASSERTED**: that `hom` is SURJECTIVE on
geometric `I`-torsion, i.e. the full isogeny property. What the consumers
need is that the INDUCED pairing on `A[I]` is nondegenerate, which is
what `weil_hom_nondegenerate` says. Surjectivity of `A[I] → A^∨[I]` is a
strictly further claim — over an algebraically closed field it follows
from injectivity only via `#A[I] = #A^∨[I]`, which nothing in this
development audits — so it is not asserted here rather than asserted on
faith.

**THE LEVEL SET `𝒩`, AND WHY IT IS A PARAMETER (faithfulness repair,
2026-07-27, same day as the repair above).** In its first form
`weil_hom_nondegenerate` quantified over ALL ideals of `R`. That is
OVER-STRENGTH and it made this structure nearly uninhabitable, for the
reason recorded on `exists_tateWeilPairing_of_mult`
(`Modularity/TateModule.lean`): by nondegeneracy of the canonical
`A[I] × A^∨[I]` pairing, the axiom AT `I` says exactly
`ker hom ∩ A[I] = 0`; imposing it at EVERY `I` says `ker hom` has no
torsion geometric point at all, and in characteristic zero `ker hom` is
finite étale, so `hom` is forced to be an ISOMORPHISM. A
`PolarizationStruct` was therefore a PRINCIPAL `𝒪_D`-polarization —
and a Hilbert–Blumenthal abelian variety NEED NOT ADMIT ONE. The
`𝒪_D`-polarizations of an HBAV are classified by a polarization module
`𝔠`, an invertible `𝒪_D`-module, and a principal one exists exactly when
`𝔠` is trivial in `Cl⁺(D)`. So `∃ d, Nonempty (PolarizationStruct d)` in
the old form was a FALSE statement for every `D` with `h⁺(D) > 1`.

The repair makes the axiom LOCAL, and the correct locality is a SET of
levels rather than a single one, because the consumers need one and the
same polarization to be nondegenerate at the two level ideals `λ` and
`𝔭` (see `IsSplitLevelStructure` / `HasSplitHilbertBlumenthalModuli` in
`Modularity/KhareWintenberger.lean`, where `pol₀` is used at both).
Indexing by a single ideal would have forced those consumers to carry two
unrelated polarizations, which is a DIFFERENT and non-classical moduli
problem.

WHY `PolarizationStruct d 𝒩` IS INHABITED FOR FINITE `𝒩`, so that this
is a genuine weakening and not merely a smaller one: `𝔠` is invertible,
so for a finite set `𝒩` of maximal ideals one may choose `c ∈ 𝔠` with
`c 𝒪_{D,I} = 𝔠_I` for every `I ∈ 𝒩`; the polarization `λ_c` then has
degree prime to every `I ∈ 𝒩`, i.e. `ker λ_c ∩ A[I] = 0` there. This is
the global shadow of the local statement `exists_tateWeilPairing_of_mult`
already relies on — `∧²_{𝒪_D} T_I A ≅ 𝔡_D⁻¹ 𝔠 (1)` is free of rank one
over the LOCAL ring `𝒪_{D,I}` whatever the class of `𝔠`.

`𝒩 = ∅` is legal and contentless, exactly as `𝒩 = ⊤` is legal and
over-strong; that is deliberate. The set is a PARAMETER rather than a
field so that the choice is visible in every consumer's TYPE and cannot
drift silently — a consumer that wants content must name its levels.

**POSITIVITY GAP — THIS STRUCTURE IS NOT A POLARIZATION, AND THE
PARAGRAPH ABOVE CONFLATES `Cl` WITH `Cl⁺` (audit 2026-07-27, PARI/GP
confirmed).** Two corrections, and the second is load-bearing for
`Modularity/KhareWintenberger.lean`'s split moduli leaves.

*(1) There is no positivity anywhere in this structure.* Classically a
polarization is `φ_L` for an AMPLE `L`; what is written here is `hom`
additive, natural, `R`-linear, carrying torsion to torsion, with the
induced pairing ALTERNATING (`weil_self`) and nondegenerate at `𝒩`. By
Mumford (*Abelian Varieties* §23) "symmetric with `e^λ` alternating" is
exactly "`λ = φ_L` for SOME line bundle `L`" — ampleness of `L` is the
part that is missing, and it is the part no torsion-level, Weil-pairing
or kernel condition can supply. Concretely `hom` and `-hom` satisfy
every field of this structure simultaneously, and exactly one of a
symmetric isomorphism / its negative is a polarization. **So this is a
symmetric homomorphism `A ⟶ A^∨`, not a polarization**; the name is
historical and is kept only because every consumer already spells it.

*(2) Consequently the old all-ideals form pinned the WIDE class, not the
NARROW one.* The paragraph above says `PolarizationStruct` in its first
form forced a PRINCIPAL `𝒪_D`-polarization, hence `𝔠` trivial in
`Cl⁺(D)`. That is wrong. Nondegeneracy at every `I` forces
`ker hom = 0`, i.e. `hom` is a symmetric `𝒪_D`-linear ISOMORPHISM
`A ≃ A^∨`; such an isomorphism is `λ_c` for a GENERATOR `c` of
`𝔠 = Hom^{sym}_{𝒪_D}(A, A^∨)`, so it exists exactly when `𝔠` is trivial
in the WIDE class group `Cl(D)` — with no constraint on its sign, hence
none on its class in `Cl⁺(D)`.

The two differ, and the discriminating witness is small: `D = ℚ(√3)` has
`h(D) = 1` but `h⁺(D) = 2`, because the fundamental unit `2 + √3` has
norm `+1`, so every unit is totally positive or totally negative and no
element of mixed signature generates `𝒪_D`. `(√3)` therefore represents
the nontrivial class of `Cl⁺(D) ≅ ℤ/2` while being trivial in
`Cl(D) = 1`. (PARI/GP `bnfinit`/`bnrinit` at the infinite modulus, 2026-07-27:
`√3, √6, √7, √11, √14, √19, √21, √22, √23` all have `h = 1`, `h⁺ = 2`,
`N(fu) = +1`; `√15` has `h = 2`, `Cl⁺ ≅ (ℤ/2)²`; `√2, √5, √13, √17, √29`
have `h⁺ = h = 1` because `N(fu) = -1`.)

So an HBAV whose polarization module lies in the NONTRIVIAL narrow class
of `ℚ(√3)` carries a `PolarizationStruct d 𝒩` for EVERY `𝒩`, including
`𝒩 = ⊤` — the pre-repair form. Whatever the `𝒩` repair fixed, it did not
create, and reverting it would not remove, the falsity recorded on
`GaloisRepresentation.Modularity.HasSplitHilbertBlumenthalModuli`. The
component of a Hilbert–Blumenthal moduli space is indexed by the narrow
class, and **nothing expressible over this vocabulary sees it**; closing
that gap needs an ampleness (or Rosati-positivity) notion on
`AbelianSchemeStruct`, which is a cut-level piece of new machinery and
has no owner. -/
structure PolarizationStruct {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {R : Type u} [CommRing R] {m : Mult ab R} (d : DualStruct ab m)
    (𝒩 : Set (Ideal R)) where
  /-- the polarization on relative points -/
  hom : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint d.dualMap g
  /-- the polarization is additive -/
  hom_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (y y' : RelPoint f g),
    hom (ab.add y y') = d.dualAb.add (hom y) (hom y')
  /-- naturality in the test object -/
  pre_hom : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (y : RelPoint f g),
    RelPoint.pre h hg (hom y) = hom (RelPoint.pre h hg y)
  /-- the polarization is `R`-linear -/
  hom_act : ∀ {T : Scheme.{u}} {g : T ⟶ S} (a : R) (y : RelPoint f g),
    hom (m.act a y) = d.dualMult.act a (hom y)
  /-- the polarization carries `I`-torsion to `I`-torsion -/
  hom_torsion : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R) (y : GeomFibrePt f x),
    y ∈ (m.torsion x I).1 → hom y ∈ (d.dualMult.torsion x I).1
  /-- the induced pairing is alternating -/
  weil_self : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I) (y : GeomFibrePt f x),
    y ∈ (m.torsion x I).1 → d.weil x I n hn y (hom y) = 1
  /-- **the induced pairing `A[I] × A[I] ⟶ μ_n` is NONDEGENERATE AT EVERY
  LEVEL `I ∈ 𝒩`** — the axiom that carries the content of this structure,
  and without which (for nonempty `𝒩`) the constant ZERO MAP satisfies
  every other field over every datum (see the refutation test in the
  structure docstring).

  Classically the clause at `I` holds exactly when `ker hom ∩ A[I] = 0`,
  i.e. when the degree of the polarization is prime to `I` — part of the
  Hilbert–Blumenthal moduli datum, and consistent with `weil_self`, since
  the `λ`-Weil pairing on `A[I]` is alternating and nondegenerate under
  exactly that hypothesis. Note this is NOT implied by
  `DualStruct.weil_nondegenerate`, which is about the canonical
  `A × A^∨` pairing and is blind to a degenerate `hom`.

  **THE `I ∈ 𝒩` GUARD IS LOAD-BEARING, NOT BOOKKEEPING.** Dropping it —
  i.e. quantifying over all ideals — forces `ker hom = 0`, hence a
  PRINCIPAL polarization, which not every HBAV admits. See the structure
  docstring for the full argument and for why `PolarizationStruct d 𝒩` is
  nevertheless inhabited whenever `𝒩` is finite. -/
  weil_hom_nondegenerate : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R), I ∈ 𝒩 → ∀ (n : ℕ) (hn : (n : R) ∈ I) (y : GeomFibrePt f x),
    y ∈ (m.torsion x I).1 →
    (∀ z : GeomFibrePt f x, z ∈ (m.torsion x I).1 →
      d.weil x I n hn y (hom z) = 1) →
    y = ab.zero (specAlgClos F ≫ x)

namespace PolarizationStruct

variable {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
variable {R : Type u} [CommRing R] {m : Mult ab R} {d : DualStruct ab m}
variable {𝒩 : Set (Ideal R)}
variable (p : PolarizationStruct d 𝒩)
variable {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
variable (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I)

/-- **The `𝒪_D`-Weil pairing attached to a polarization**: the pairing
`A[I] × A[I] ⟶ μ_n` obtained from the canonical pairing on `A × A^∨` by
composing the second variable with the polarization.

This is the object named in both absence notes, and the six lemmas below
are its classical properties, each PROVEN from the axioms of
`DualStruct` and `PolarizationStruct` rather than assumed. -/
noncomputable def pairing (y z : GeomFibrePt f x) :
    rootsOfUnity n (AlgebraicClosure F) :=
  d.weil x I n hn y (p.hom z)

/-- The pairing is the canonical one composed with the polarization. -/
theorem pairing_def (y z : GeomFibrePt f x) :
    p.pairing x I n hn y z = d.weil x I n hn y (p.hom z) := rfl

/-- The pairing is multiplicative in the first variable. -/
theorem pairing_add_left (y y' z : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1) (hy' : y' ∈ (m.torsion x I).1)
    (hz : z ∈ (m.torsion x I).1) :
    p.pairing x I n hn (ab.add y y') z
      = p.pairing x I n hn y z * p.pairing x I n hn y' z :=
  d.weil_add_left x I n hn y y' (p.hom z) hy hy' (p.hom_torsion x I z hz)

/-- The pairing is multiplicative in the second variable. -/
theorem pairing_add_right (y z z' : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1) (hz : z ∈ (m.torsion x I).1)
    (hz' : z' ∈ (m.torsion x I).1) :
    p.pairing x I n hn y (ab.add z z')
      = p.pairing x I n hn y z * p.pairing x I n hn y z' := by
  rw [pairing_def, p.hom_add]
  exact d.weil_add_right x I n hn y (p.hom z) (p.hom z') hy
    (p.hom_torsion x I z hz) (p.hom_torsion x I z' hz')

/-- **The pairing is alternating.** -/
theorem pairing_self (y : GeomFibrePt f x) (hy : y ∈ (m.torsion x I).1) :
    p.pairing x I n hn y y = 1 :=
  p.weil_self x I n hn y hy

/-- **The polarization commutes with the Galois action**: naturality read
at the Galois automorphisms of `Spec F̄`, exactly as `Mult.galSMul_act`
reads naturality of the multiplication. -/
theorem galSMul_hom (σ : Field.absoluteGaloisGroup F) (y : GeomFibrePt f x) :
    d.dualAb.galSMul x σ (p.hom y) = p.hom (ab.galSMul x σ y) :=
  p.pre_hom (specGal σ) (specGal_comp_base x σ) y

/-- **The pairing is `Γ_F`-equivariant**, the Galois group acting on the
target through its action on roots of unity — i.e. through the cyclotomic
character alone. This is the input to the classical identification
`∧²_O T_I A ≅ O(1)`, and hence to
`det_eq_cyclotomicCharacter_of_tateFrame`. -/
theorem pairing_gal (σ : Field.absoluteGaloisGroup F) (y z : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1) (hz : z ∈ (m.torsion x I).1) :
    p.pairing x I n hn (ab.galSMul x σ y) (ab.galSMul x σ z)
      = galRoot σ (p.pairing x I n hn y z) := by
  rw [pairing_def, pairing_def, ← p.galSMul_hom x σ z]
  exact d.weil_gal x I n hn σ y (p.hom z) hy (p.hom_torsion x I z hz)

/-- **The pairing is `R`-bilinear**: a scalar may be moved across it.
This combines the `R`-linearity of the polarization (`hom_act`) with the
`R`-adjointness of the canonical pairing (`weil_act`), and it is the
sense in which this is the `𝒪_D`-Weil pairing rather than merely the
`ℤ`-valued one. -/
theorem pairing_act (a : R) (y z : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1) (hz : z ∈ (m.torsion x I).1) :
    p.pairing x I n hn (m.act a y) z = p.pairing x I n hn y (m.act a z) := by
  rw [pairing_def, pairing_def, p.hom_act]
  exact d.weil_act x I n hn a y (p.hom z) hy (p.hom_torsion x I z hz)

/-- **The pairing is NONDEGENERATE AT A LEVEL `I ∈ 𝒩`**:
`weil_hom_nondegenerate` read through `pairing`. This is the axiom that
gives `PolarizationStruct` its content — see the refutation test in the
structure's docstring — and it is what the classical arguments mean when
they call the polarized Weil pairing *perfect*.

`hI` is not decoration: at a level outside `𝒩` the pairing may be
genuinely degenerate, because a polarization whose module is nonprincipal
has nontrivial kernel somewhere. Demanding this at every `I` is exactly
the over-strength that made the structure uninhabitable. -/
theorem pairing_nondegenerate (hI : I ∈ 𝒩) (y : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1)
    (h : ∀ z : GeomFibrePt f x, z ∈ (m.torsion x I).1 →
      p.pairing x I n hn y z = 1) :
    y = ab.zero (specAlgClos F ≫ x) :=
  p.weil_hom_nondegenerate x I hI n hn y hy h

/-- **The pairing is NON-TRIVIAL on every nonzero torsion point**: the
contrapositive of `pairing_nondegenerate`, and the form the level
structure of the Hilbert–Blumenthal moduli problem consumes. In
particular `pairing` is not identically `1` as soon as `A[I] ≠ 0`, which
is precisely what the pre-repair `PolarizationStruct` failed to
guarantee. -/
theorem exists_pairing_ne_one (hI : I ∈ 𝒩) (y : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1)
    (hy0 : y ≠ ab.zero (specAlgClos F ≫ x)) :
    ∃ z : GeomFibrePt f x, z ∈ (m.torsion x I).1 ∧ p.pairing x I n hn y z ≠ 1 := by
  by_contra hcon
  refine hy0 (p.pairing_nondegenerate x I n hn hI y hy ?_)
  intro z hz
  by_contra hne
  exact hcon ⟨z, hz, hne⟩

include hn in
/-- **THE STANDING REFUTATION TEST: the constant zero map is not a
polarization.**

Until 2026-07-27 `PolarizationStruct` was satisfied by
`hom := fun _ => d.dualAb.zero g` over EVERY datum, so it carried no
content at all and its `pairing` could be identically `1`. This theorem
is the mechanical check that the repair took: if `hom` is the zero map,
then every `I`-torsion point of every geometric fibre is zero, for every
LEVEL `I ∈ 𝒩`. So the zero map satisfies the repaired structure only over
data with no `𝒩`-torsion whatsoever — never over a datum the moduli
problem cares about, provided `𝒩` names the levels that problem uses.

This survived the SECOND repair of the same day, which restricted
`weil_hom_nondegenerate` from all ideals to `𝒩`: the only change is the
hypothesis `hI`, which every consumer already has, since a consumer that
cares about level `I` is one that put `I` into `𝒩`. What the guard does
cost is content at `𝒩 = ∅`, where this theorem is vacuous and the zero
map is again a `PolarizationStruct` — which is honest, because at `𝒩 = ∅`
nothing is being asserted.

Re-run this theorem after any weakening of `PolarizationStruct`; a
structure whose only proof of content is prose will drift back. -/
theorem torsion_eq_zero_of_hom_eq_zero (hI : I ∈ 𝒩)
    (hhom : ∀ {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g),
      p.hom y = d.dualAb.zero g)
    (y : GeomFibrePt f x) (hy : y ∈ (m.torsion x I).1) :
    y = ab.zero (specAlgClos F ≫ x) := by
  refine p.weil_hom_nondegenerate x I hI n hn y hy ?_
  intro z _
  rw [hhom z]
  exact d.weil_zero_right x I n hn y hy

end PolarizationStruct

end Fermat

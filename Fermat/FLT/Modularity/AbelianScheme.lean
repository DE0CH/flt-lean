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
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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

/-- **Multiplication by `0` kills every relative point.** This is
`zero_smul` of `Mult.module`, restated in the raw `act` vocabulary so
that it can be used without introducing the `letI`-bound module instance
at the call site. It is what makes `PolarizationStruct.lam_zero` — and
hence the positivity refutation test `PolarizationStruct.posElt_ne_zero`
— available. -/
theorem act_zero {T : Scheme.{u}} (g : T ⟶ S) (y : RelPoint f g) :
    m.act (0 : R) y = ab.zero g := by
  letI := ab.addCommGroup g
  letI := m.module g
  exact zero_smul R y

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
  structure.  Since 2026-07-30 it is GATED on `(n : F) ≠ 0` — see the
  LEVEL GATE paragraph of the `DualStruct` docstring for the witness that
  made the ungated form UNINHABITABLE in positive characteristic.  The
  gate does not cost the non-vacuity: at any level invertible in `F` the
  axiom still rules out `weil ≡ 1`, and every fibre of characteristic
  zero has such levels at every `I ≠ ⊤`.
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

* THIRD REPAIR, SAME DAY — **POSITIVITY**, and it is a different kind of
  content from the two above. The `𝒩`-repair released the structure onto
  every polarization class, and that made
  `HasSplitHilbertBlumenthalModuli` (`Modularity/MoretBailly.lean`)
  FALSE, since its fineness clause then ranged over all classes while
  `GeometricallyIrreducible` allows one component. `PolarizationStruct`
  now also carries the POLARIZATION MODULE `𝔞` with a positivity cone
  `𝔞pos`, an isomorphism `𝔞 ≅ Hom^sym_R(A, A^∨)` (`lam`, `lam_injective`,
  `lam_surjective` — the new `SymHomStruct` exists only to let that be
  said), and the datum that `hom` is `λ_a` for a POSITIVE `a`. Wide class
  comes from the isomorphism, narrow class from positivity; the moduli
  statement is then indexed by `(𝔞, 𝔞⁺) ∈ Cl⁺(D)` and is true again.
  `PolarizationStruct.posElt_ne_zero` is the mechanical test that the
  positivity datum is not junk, and the structure's docstring records the
  refutation (`D = ℚ(√3)`, `h = 1`, `h⁺ = 2`) together with three repairs
  that do NOT work.

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
material of this section — `DualStruct.weil_zero_right`, `Mult.act_zero`,
and `PolarizationStruct.pairing_def`, `pairing_add_left`,
`pairing_add_right`, `pairing_self`, `galSMul_hom`, `pairing_gal`,
`pairing_act`, `pairing_nondegenerate`, `exists_pairing_ne_one`,
`torsion_eq_zero_of_hom_eq_zero`, `lam_zero` and `posElt_ne_zero` —
which is consumed only by proofs that
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
`ℤ`-bilinear.

**THE LEVEL GATE ON `weil_nondegenerate`, AND WHY IT IS NOT OPTIONAL**
(repair carried out 2026-07-30, prescribed by the falsity audit on
`exists_dualPolarization_of_mult` in `Modularity/TateModule.lean`).

`weil_nondegenerate` now carries `(hnF : (n : F) ≠ 0)`.  Without it the
structure is UNINHABITED as soon as `S` has a point of positive residue
characteristic whose fibre has nonzero torsion at that characteristic, so
every leaf of the shape `∃ d : DualStruct ab m, …` over such a base was
FALSE — not hard, impossible.  The mechanism has nothing to do with
duality:

* `weil x' I n hn` lands in `rootsOfUnity n (AlgebraicClosure F')`, and
  the binders of the axioms range over EVERY field `F'` and EVERY point
  `x' : Spec F' ⟶ S`, not just the point a consumer cares about;
* in characteristic `p` the group `rootsOfUnity p (AlgebraicClosure F')`
  is TRIVIAL (`z ^ p = 1 ↔ (z - 1) ^ p = 0 ↔ z = 1`), so at `I = (p)`,
  `n = p` — legal, since `(p : R) ∈ (p)` — the pairing is CONSTANTLY `1`;
* the hypothesis of the ungated axiom therefore held vacuously for every
  `p`-torsion point, and its conclusion said `A'[p](F̄') = 0`.

WITNESS, verified numerically (PARI/GP, 2026-07-30): `S = Spec ℤ[1/11]`,
`A` the smooth proper model of `X₀(11)` (conductor `11`, hence good
reduction at every `p ≠ 11`), `D = ℚ` so `R ≅ ℤ` and the relative
dimension is `1`.  At the point `(5)` the fibre is `11a1 / 𝔽_5`, with
`a_5 = 1`, `#E(𝔽_5) = 5` and `5 ∤ a_5`, i.e. ORDINARY, so
`E[5](𝔽̄_5) ≅ ℤ/5 ≠ 0` — which the ungated axiom forbade.

WHY THE GATE COSTS NOTHING.  Every level with `(n : R) ∈ I` at which the
axiom was contradictory has `n` divisible by the residue characteristic,
hence `(n : F) = 0`; conversely when `(n : F) ≠ 0` the group `A[I] ⊆ A[n]`
is étale of order prime to the characteristic and the canonical pairing on
it really is perfect.  In characteristic zero the gate is vacuous, so no
existing consumer over a number field changes — the only use of the axiom
in the tree, `DualStruct.baseChangeOfIsPullback`, threads the SAME `F` and
so passes it through verbatim.

`weil` itself is deliberately NOT gated: a pairing landing in a trivial
group is harmless, it is only the nondegeneracy CLAIM about it that was
false.

**HOW `weil` MUST BE READ — A SEPARATE CONSTRAINT THAT THE GATE DOES NOT
SUBSUME** (found 2026-07-29, re-checked against the gate 2026-07-30, and
BINDING on anyone who constructs a `DualStruct`).

Under the naive reading of `weil x I n hn` as "the `n`-Weil pairing `e_n`
RESTRICTED to `A[I] × Â[I]`" the structure is uninhabitable even in
CHARACTERISTIC ZERO, so the level gate does not rescue it.  Witness:
`R = ℤ`, `I = (2)`, `n = 4` — legal, since `(4 : ℤ) ∈ (2)`, and
`(4 : F) ≠ 0` in characteristic zero, so the gated axiom is still
asserted.  Every `y ∈ A[2]` is `2y'` and every `ẑ ∈ Â[2]` is `2ẑ'` with
`y', ẑ'` of order dividing `4`, so
`e_4(y, ẑ) = e_4(2y', 2ẑ') = e_4(y', ẑ')^4 = 1`; the restriction is
identically `1` while `A[2] ≠ 0`.

The reading that DOES work, and the one every construction must build:
`weil x I n hn` is the CANONICAL PERFECT pairing `A[I] × Â[I] ⟶ μ_e`,
where `e` is the exponent of `A[I]` (which divides `n`, because
`(n : R) ∈ I` forces `A[I] ⊆ A[n]`), composed with `μ_e ↪ μ_n`.  At the
levels the development actually uses — `I = (q^N)`, `n = q^N`, where the
exponent IS `q^N` — the two readings agree and `weil` is the classical
`e_{q^N}`, which is why nothing downstream depends on the distinction. -/
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
  content, and without which `weil ≡ 1` would satisfy all the others.

  **GATED ON `(n : F) ≠ 0` (2026-07-30).**  Ungated, this field made
  `DualStruct` UNINHABITED over any base with a fibre of positive residue
  characteristic `p` and positive `p`-rank: `rootsOfUnity p (AlgebraicClosure F)`
  is TRIVIAL in characteristic `p` (`z ^ p = 1 ↔ (z - 1) ^ p = 0 ↔ z = 1`), so at
  `I = (p)`, `n = p` — legal, since `(p : R) ∈ (p)` — the pairing is constantly
  `1`, the hypothesis holds for every `p`-torsion point, and the axiom concluded
  `A[p](F̄) = 0`.  An ORDINARY elliptic curve refutes that; the witness written
  out on `exists_dualPolarization_of_mult` (`Modularity/TateModule.lean`) is
  `X₀(11)` over `Spec ℤ[1/11]` read at the fibre `𝔽_5`.

  The gate is FREE in characteristic zero for every `n ≠ 0`, so no consumer over
  a number field changes, and it removes exactly the levels at which the axiom is
  contradictory.  `weil` itself needs no change — a pairing landing in a trivial
  group is harmless; it is only the nondegeneracy CLAIM about it that was false. -/
  weil_nondegenerate : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
      (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I) (_hnF : (n : F) ≠ 0) (y : GeomFibrePt f x),
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

/-- **A symmetric `R`-linear homomorphism `A ⟶ A^∨`** — the underlying
datum of a polarization with its POSITIVITY and its nondegeneracy
forgotten.

By Yoneda this is a natural additive `R`-equivariant transformation of
functors of points `A ⟶ A^∨` whose induced pairing on `I`-torsion is
alternating; "alternating" is the classical reading of SYMMETRY of a
homomorphism to the dual. Classically these form an invertible
`R`-module `Hom^sym_R(A, A^∨)`, and it is exactly that module which
`PolarizationStruct.lam` identifies with its parameter `𝔞`.

WHY THIS TYPE EXISTS AT ALL. It is introduced ONLY so that
`PolarizationStruct.lam_surjective` can be written. Without a type of
symmetric homomorphisms there is no way to say that `𝔞` EXHAUSTS them —
and without that, `𝔞` is pinned by nothing: one could always take
`𝔞 = R` and `λ_a := hom ∘ act a`, so the parameter would carry no
information and could not index anything. See the POSITIVITY section of
`PolarizationStruct`'s docstring, where that is the second of three
refuted repairs. -/
structure SymHomStruct {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {R : Type u} [CommRing R] {m : Mult ab R} (d : DualStruct ab m) where
  /-- the homomorphism, on relative points -/
  hom : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint d.dualMap g
  /-- it is additive -/
  hom_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (y y' : RelPoint f g),
    hom (ab.add y y') = d.dualAb.add (hom y) (hom y')
  /-- naturality in the test object -/
  pre_hom : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (y : RelPoint f g),
    RelPoint.pre h hg (hom y) = hom (RelPoint.pre h hg y)
  /-- it is `R`-linear -/
  hom_act : ∀ {T : Scheme.{u}} {g : T ⟶ S} (a : R) (y : RelPoint f g),
    hom (m.act a y) = d.dualMult.act a (hom y)
  /-- it carries `I`-torsion to `I`-torsion -/
  hom_torsion : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R) (y : GeomFibrePt f x),
    y ∈ (m.torsion x I).1 → hom y ∈ (d.dualMult.torsion x I).1
  /-- SYMMETRY, read through the Weil pairing: the induced pairing on
  `I`-torsion is alternating -/
  weil_self : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I) (y : GeomFibrePt f x),
    y ∈ (m.torsion x I).1 → d.weil x I n hn y (hom y) = 1

/-- **A polarization**: an `R`-linear symmetric isogeny `A ⟶ A^∨`,
together with its POLARIZATION MODULE `𝔞` and the POSITIVITY of the
element of that module which it is.

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

**POSITIVITY, AND THE POLARIZATION MODULE `(𝔞, 𝔞⁺)` (third repair of
this structure, 2026-07-27; it is what makes
`HasSplitHilbertBlumenthalModuli` TRUE again).**

The `𝒩`-repair above had a consequence its own note recorded as a
*contingency* and which duly FIRED. Once nondegeneracy is asserted only
at `𝒩`, a `PolarizationStruct` no longer forces `ker hom = 0`, so
HBAVs with a NONPRINCIPAL polarization module became admissible — and
the split Hilbert–Blumenthal moduli statement in
`Modularity/MoretBailly.lean`, which asserts `GeometricallyIrreducible`
of a space whose fineness clause then quantified over every polarization
class, became FALSE. The refutation is explicit: at `D = ℚ(√3)`
(PARI/GP: `h = 1`, `h⁺ = 2`, fundamental unit `2 + √3` of norm `+1`) a
`Γ_F`-equivariant `𝒪_D`-linear bijection on geometric points restricts
to torsion, gives `T_ℓB ≅ T_ℓA` for every `ℓ`, and by Faltings forces an
`𝒪_D`-linear isogeny — under which the narrow class moves only by
SQUARES. `Cl⁺(ℚ(√3)) ≅ ℤ/2` has no nontrivial squares, so nothing over
the principal component is comparable to a nonprincipal-class object.

THE CUT-LEVEL CALL, and why the alternative is not merely less elegant
but UNAVAILABLE. One could instead demand `h⁺(D) = 1` upstream. But `D`
is produced by `exists_totallyRealCoefficientDatum_of_residueField`,
which must hit a PRESCRIBED residue field `𝔽_{ℓ^r}`, and the
Khare–Wintenberger route quantifies over ALL `ℓ`; so the hypothesis
would read *"for every `ℓ` and every `r` there is a totally real `D`
with a degree-`r` prime above `ℓ` and `h⁺(D) = 1"`, whose real-quadratic
special case is Gauss's class-number-one problem — OPEN. Trading a false
leaf for an open problem is not progress. Indexing by `(𝔞, 𝔞⁺)` is what
the literature does: Rapoport, *Compactifications de l'espace de modules
de Hilbert–Blumenthal* (Compositio 36, 1978), §1, and Deligne–Pappas,
*Singularités des espaces de modules de Hilbert*, fix the polarization
module TOGETHER WITH ITS POSITIVITY CONE, and that cone is precisely
what indexes the components. Goren's *Lectures on Hilbert Modular
Varieties and Modular Forms* is the readable survey of the `Cl⁺`
indexing.

**THREE REPAIRS THAT DO NOT WORK, each refuted; do not re-propose them.**

1. *Reverting the `𝒩` guard.* It fixes nothing, because this structure
   carries no positivity: `hom` and `−hom` satisfy every field alike.
   So `ker hom = 0` yields only a symmetric `R`-linear ISOMORPHISM
   `A ≃ A^∨`, which exists exactly when the polarization module is
   trivial in the WIDE class group `Cl(D)`. `ℚ(√3)` has `h = 1` and
   `h⁺ = 2`, so its nontrivial-narrow-class HBAVs carry a
   `PolarizationStruct d 𝒩` for EVERY `𝒩`, `⊤` included. The earlier
   defusal conflated `Cl⁺` with `Cl`, and the `𝒩` guard is innocent.
2. *Carrying `𝔞` as data, with a module isomorphism
   `𝔞 ≃ Hom^sym_R(A, A^∨)` and nothing else.* That also sees only
   `Cl(D)` — which is TRIVIAL for the witness — so it does not separate
   the two components of `ℚ(√3)`. Necessary, not sufficient.
3. *A `Prop`-valued positivity field*, e.g. `isPol h := ∃ a ∈ 𝔞⁺,
   h = λ_a`. Junk-satisfiable: it constrains nothing, because `λ` and
   `𝔞⁺` are then free. **Positivity must be DATA.**

**WHAT IS ACTUALLY ADDED, AND WHY IT IS NOT JUNK-SATISFIABLE.** Two
parameters, `𝔞 : Ideal R` and `𝔞pos : Set R` (the positivity cone —
`Set R` rather than a totally-positive predicate because this structure
is stated over an arbitrary `CommRing R`; the moduli consumer
instantiates it with the totally positive elements of `𝒪_D`), and four
pieces of data:

* `lam : 𝔞 → SymHomStruct d`, additive and `R`-linear in the module
  variable (`lam_add`, `lam_smul`);
* `lam_injective` and **`lam_surjective`** — so `lam` is an isomorphism
  of `R`-modules `𝔞 ≅ Hom^sym_R(A, A^∨)`. This is the clause that pins
  the WIDE class `[𝔞] ∈ Cl(D)`, and it is why repair 2's shape is
  necessary here;
* `posElt : 𝔞` with `posElt_pos : (posElt : R) ∈ 𝔞pos` and
  `hom_eq_lam : hom = lam posElt` — the polarization corresponds to a
  POSITIVE element of the module. This is the clause that upgrades the
  pin from `Cl` to `Cl⁺`: two identifications `𝔞 ≅ Hom^sym` differ by
  multiplication by some `u ∈ D^×` with `u𝔞 = 𝔞`, and requiring both
  to carry the SAME `hom` to a positive element forces `u` totally
  positive. That is exactly the definition of the narrow class.

So `(𝔞, 𝔞pos)` is not decoration: `PolarizationStruct d 𝒩 𝔞 𝔞pos` is
INHABITED precisely when `[𝔞]` is the narrow class of the polarization
module of `(ab, m, d)`, and UNINHABITED for every other narrow class.
That is what lets a moduli statement index its component by `𝔞` and be
true. The junk instance that killed repair 2 — `𝔞 := R`,
`λ_a := hom ∘ act a` — fails `lam_surjective` over any datum whose
polarization module is nonprincipal, which is the whole point.

WHY POSITIVITY HAD TO ENTER AS DATA RATHER THAN BE DERIVED. The
classical definition is Mumford's: `hom = φ_L` for a RELATIVELY AMPLE
line bundle `L` on `A/S`. That is still unavailable, but NOT for the
reason recorded here before 2026-07-28. The previous version of this
paragraph said "there is NO ampleness of any kind for line bundles on
schemes at this pin, no relative Picard functor" — **both halves of that
are now false, and were already false when written into this file**:

* ampleness exists as `Fermat.IsAmpleSheaf`
  (`Modularity/AmpleSheaf.lean`), a nonvanishing-locus definition on
  `Scheme.Modules`, with a recorded non-vacuity witness;
* a relative Picard functor exists as `Fermat.IsRelPicZeroOf`
  (`ModularCurve/RelativePicard.lean`), together with `RelPicEquiv` and
  the existence leaf `Fermat.exists_relPicZero`.

Both of those modules import THIS one, so they cannot be used here; but
"the pin has nothing" is the wrong diagnosis to leave behind, because it
sends the next owner off to build a theory that this project already has.
What genuinely remains missing is only the third item: **no
identification of `d.dualScheme` with `Pic⁰`**, i.e. no bridge between
`DualStruct` and `IsRelPicZeroOf` — so `φ_L` still cannot be written
here, and writing that bridge is the concrete next step for anyone who
wants to derive positivity rather than assume it.
(`Mathlib.RingTheory.PicardGroup` is the Picard group of a commutative
RING and is unrelated.) But the deeper reason is not
the pin: **positivity is invisible to torsion.** `λ` and `−λ` have the
same kernel and induce the same pairing up to inversion, so NO axiom
phrased in the torsion/Galois vocabulary of this module can distinguish
them. Positivity therefore MUST arrive as a datum, and the honest form
of that datum is "which element of the polarization module this is,
inside a cone supplied by the consumer" — which is precisely the
Rapoport/Deligne–Pappas formulation. The surrogate is deliberate and
its choice is recorded here rather than hidden.

`𝔞pos` is unconstrained at this level of generality, and that is
correct: a positivity cone is a piece of the ARITHMETIC of `R`, not of
the geometry of `A`, and pretending otherwise would put a fake axiom on
a structure that cannot check it. What makes the moduli statement true
is that the consumer instantiates `𝔞pos` with a genuine cone and holds
it FIXED across the universal family and the fineness clause. -/
structure PolarizationStruct {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {R : Type u} [CommRing R] {m : Mult ab R} (d : DualStruct ab m)
    (𝒩 : Set (Ideal R)) (𝔞 : Ideal R) (𝔞pos : Set R) where
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
  nevertheless inhabited whenever `𝒩` is finite.

  **AND IT IS GATED ON `(n : F) ≠ 0` FOR THE SAME REASON
  `DualStruct.weil_nondegenerate` IS** (repair of 2026-07-30, applied to
  both axioms in one commit). The `I ∈ 𝒩` guard does NOT cover this: `𝒩`
  is a parameter, so it may perfectly well contain an ideal above the
  residue characteristic of some point of `S`, and there the pairing lands
  in a trivial group and this axiom concludes `A[I](F̄) = 0`. The witness
  is the one on `DualStruct.weil_nondegenerate`, with `𝒩 = {(5)}` added:
  `S = Spec ℤ[1/11]`, `A` the smooth proper model of `X₀(11)`, `R = ℤ`,
  the point `Spec 𝔽_5 ⟶ S` whose fibre `11a1` is ordinary, `I = (5)`,
  `n = 5`. `PolarizationStruct d {(5)} 𝔞 𝔞pos` is UNINHABITABLE over that
  base without the gate.

  The cost is stated honestly on `torsion_eq_zero_of_hom_eq_zero`, which is
  this structure's mechanical content test: at a level divisible by the
  residue characteristic the structure no longer excludes the zero map. It
  cannot, and nothing is lost — at such a level `d.weil` maps into a
  trivial group, so the induced pairing carries no information there
  whatever `hom` is, and the "content" the ungated axiom had was the
  content of a false statement. -/
  weil_hom_nondegenerate : ∀ {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R), I ∈ 𝒩 → ∀ (n : ℕ) (hn : (n : R) ∈ I) (y : GeomFibrePt f x),
    (n : F) ≠ 0 →
    y ∈ (m.torsion x I).1 →
    (∀ z : GeomFibrePt f x, z ∈ (m.torsion x I).1 →
      d.weil x I n hn y (hom z) = 1) →
    y = ab.zero (specAlgClos F ≫ x)
  /-- **THE POLARIZATION MODULE, REALIZED**: a symmetric `R`-linear
  homomorphism `λ_a : A ⟶ A^∨` for each `a` in `𝔞`. Together with
  `lam_injective` and `lam_surjective` this is an isomorphism of
  `R`-modules `𝔞 ≅ Hom^sym_R(A, A^∨)` — Rapoport's polarization module,
  presented as an identification rather than constructed. -/
  lam : ↥𝔞 → SymHomStruct d
  /-- `λ` is additive in the module variable -/
  lam_add : ∀ (a b : ↥𝔞) {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g),
    (lam (a + b)).hom y = d.dualAb.add ((lam a).hom y) ((lam b).hom y)
  /-- `λ` is `R`-linear in the module variable -/
  lam_smul : ∀ (c : R) (a : ↥𝔞) {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g),
    (lam (c • a)).hom y = d.dualMult.act c ((lam a).hom y)
  /-- `λ` is INJECTIVE -/
  lam_injective : ∀ a : ↥𝔞,
    (∀ {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g),
      (lam a).hom y = d.dualAb.zero g) → a = 0
  /-- **`λ` is SURJECTIVE onto ALL symmetric `R`-linear homomorphisms** —
  the clause that PINS the wide class `[𝔞] ∈ Cl(R)`. Without it `𝔞` may
  always be taken principal (`λ_a := hom ∘ act a`) and the parameter
  carries no information at all; see refuted repair 2 in the structure
  docstring. -/
  lam_surjective : ∀ s : SymHomStruct d, ∃ a : ↥𝔞,
    ∀ {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g), (lam a).hom y = s.hom y
  /-- **POSITIVITY, AS DATA (i)**: the element of the polarization module
  that `hom` IS. -/
  posElt : ↥𝔞
  /-- **POSITIVITY, AS DATA (ii)**: that element lies in the positivity
  cone. This is what upgrades the pin from the wide class `Cl(R)` to the
  NARROW class `Cl⁺(R)`: it rigidifies `lam` up to multiplication by
  positive units, which is exactly the equivalence defining `Cl⁺`. -/
  posElt_pos : (posElt : R) ∈ 𝔞pos
  /-- **POSITIVITY, AS DATA (iii)**: `hom = λ_{posElt}`. -/
  hom_eq_lam : ∀ {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g),
    hom y = (lam posElt).hom y

namespace PolarizationStruct

variable {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
variable {R : Type u} [CommRing R] {m : Mult ab R} {d : DualStruct ab m}
variable {𝒩 : Set (Ideal R)} {𝔞 : Ideal R} {𝔞pos : Set R}
variable (p : PolarizationStruct d 𝒩 𝔞 𝔞pos)
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
the over-strength that made the structure uninhabitable.

`hnF` is not decoration either, and it is a DIFFERENT restriction from
`hI`: in characteristic `p` the pairing lands in the trivial group
`μ_{p^k}(F̄)`, so it is constantly `1` and nondegeneracy is contradictory
at every level `I` with `p ∣ n`, `𝒩` or no `𝒩`. See the axiom's docstring
for the witness. In characteristic zero it says only `n ≠ 0`. -/
theorem pairing_nondegenerate (hI : I ∈ 𝒩) (hnF : (n : F) ≠ 0)
    (y : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1)
    (h : ∀ z : GeomFibrePt f x, z ∈ (m.torsion x I).1 →
      p.pairing x I n hn y z = 1) :
    y = ab.zero (specAlgClos F ≫ x) :=
  p.weil_hom_nondegenerate x I hI n hn y hnF hy h

/-- **The pairing is NON-TRIVIAL on every nonzero torsion point**: the
contrapositive of `pairing_nondegenerate`, and the form the level
structure of the Hilbert–Blumenthal moduli problem consumes. In
particular `pairing` is not identically `1` as soon as `A[I] ≠ 0`, which
is precisely what the pre-repair `PolarizationStruct` failed to
guarantee. -/
theorem exists_pairing_ne_one (hI : I ∈ 𝒩) (hnF : (n : F) ≠ 0)
    (y : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1)
    (hy0 : y ≠ ab.zero (specAlgClos F ≫ x)) :
    ∃ z : GeomFibrePt f x, z ∈ (m.torsion x I).1 ∧ p.pairing x I n hn y z ≠ 1 := by
  by_contra hcon
  refine hy0 (p.pairing_nondegenerate x I n hn hI hnF y hy ?_)
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
structure whose only proof of content is prose will drift back.

**RE-RUN OF 2026-07-30, AFTER THE THIRD WEAKENING — the characteristic
gate `(n : F) ≠ 0` on `weil_hom_nondegenerate`.** The test still passes,
with `hnF` threaded through and nothing else changed, so the repair of
2026-07-27 survives. What the gate costs is stated exactly: the zero map
is again a `PolarizationStruct` over a datum whose `𝒩`-torsion lives ONLY
at levels `n` divisible by the residue characteristic. That is honest and
unavoidable — at such a level `d.weil` maps into a trivial group, so the
induced pairing is identically `1` for EVERY `hom`, degenerate or not, and
no axiom about it can distinguish the zero map from a genuine
polarization. The ungated axiom did distinguish them there, and that is
precisely why it was false. So the content lost is the content of a false
statement, and the honest reading of this test is now: the zero map is
excluded over any datum with a nonzero `I`-torsion point at a level prime
to the characteristic — which is every datum the moduli problem cares
about, since it cares about levels `λ`, `𝔭` prime to the characteristics
in play. -/
theorem torsion_eq_zero_of_hom_eq_zero (hI : I ∈ 𝒩) (hnF : (n : F) ≠ 0)
    (hhom : ∀ {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g),
      p.hom y = d.dualAb.zero g)
    (y : GeomFibrePt f x) (hy : y ∈ (m.torsion x I).1) :
    y = ab.zero (specAlgClos F ≫ x) := by
  refine p.weil_hom_nondegenerate x I hI n hn y hnF hy ?_
  intro z _
  rw [hhom z]
  exact d.weil_zero_right x I n hn y hy

/-- **`λ` kills the zero of the polarization module**, by `R`-linearity
in the module variable at the scalar `0`. Glue for the positivity
refutation test below. -/
theorem lam_zero {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g) :
    (p.lam 0).hom y = d.dualAb.zero g := by
  have h := p.lam_smul (0 : R) (0 : ↥𝔞) y
  rw [smul_zero] at h
  rw [h, d.dualMult.act_zero]

include hn in
/-- **THE STANDING REFUTATION TEST FOR POSITIVITY: the polarization is a
NONZERO element of its module.**

The positivity datum `(posElt, posElt_pos, hom_eq_lam)` would be junk if
`posElt` could be `0` — a zero module element lies in whatever cone one
hands over as `𝔞pos` if that cone happens to contain `0`, and `λ_0` is
the constant zero map, which is precisely the degenerate configuration
`torsion_eq_zero_of_hom_eq_zero` was written to exclude one level down.
This theorem shows the two tests interlock: over any datum with a
nonzero `𝒩`-torsion point, `posElt ≠ 0`, so the polarization really is a
nonzero — and, by `posElt_pos`, positive — element of `𝔞`.

Together with `lam_surjective` this is what makes `[𝔞] ∈ Cl⁺(R)` an
INVARIANT of `(ab, m, d, p)` rather than a free parameter, which is the
whole purpose of the third repair. Re-run it after any weakening of the
positivity fields.

Re-run 2026-07-30 after the characteristic gate: it passes, with `hnF`
threaded. The witness point `y` must now be torsion at a level PRIME TO
THE CHARACTERISTIC, which is where the classical argument takes it
anyway. -/
theorem posElt_ne_zero (hI : I ∈ 𝒩) (hnF : (n : F) ≠ 0) (y : GeomFibrePt f x)
    (hy : y ∈ (m.torsion x I).1) (hy0 : y ≠ ab.zero (specAlgClos F ≫ x)) :
    p.posElt ≠ 0 := by
  intro h0
  refine hy0 (p.torsion_eq_zero_of_hom_eq_zero x I n hn hI hnF ?_ y hy)
  intro T g z
  rw [p.hom_eq_lam, h0, p.lam_zero]

end PolarizationStruct

/-! ### Base change

Everything above is stated over a FIXED base `S`. The moduli arguments that
consume it are not: a Hilbert–Blumenthal family is produced over one base and
then restricted along `q : S' ⟶ S` — to a fibre, to a geometric point, to an
étale neighbourhood, to a completion — and every one of those steps needs the
whole vocabulary carried across. This section does that carrying.

## The map, and the trap

The map is

  `RelPoint f' g  ≃  RelPoint f g₀`   whenever `g ≫ q = g₀`,

for `f' : A' ⟶ S'` a base change of `f : A ⟶ S` along `q : S' ⟶ S`
(`RelPoint.baseChangeEquiv`, from `RelPoint.ofBaseChange` and
`RelPoint.toBaseChange`). Its content is the universal property of the
pullback square, nothing else: a `T`-point of `A'` over `g` is a `T`-point of
`A` over `g ≫ q`, because `A' = A ×_S S'`.

**It is NOT `RelPoint.pre`.** `pre` moves the TEST object `T`, along
`h : T' ⟶ T`, keeping `f : A ⟶ S` fixed; this moves the BASE `S`, keeping the
test object fixed. The two compose but neither is a case of the other, and
because both have the shape "precompose and re-identify the base point", the
wrong one typechecks in several places here and silently means something else.
`RelPoint.ofBaseChange_pre` is the interchange law between them, and it is the
only place the two should ever meet.

The square is taken as an arbitrary `IsPullback p f' f q` rather than as the
chosen `pullback f q`. That is deliberate: a producer normally HAS a concrete
`A'` (a fibre, an open subscheme, a completion) together with a proof that the
square is cartesian, and forcing it through `Limits.pullback` would cost an
isomorphism transport at every use. `IsPullback.of_hasPullback f q` recovers
the chosen-pullback case in one term.

Note `AbelianSchemeIsogeny.lean` already carries the chosen-pullback special
case of the FIRST of these (`RelPoint.baseChangeDown`/`baseChangeUp` and
`AbelianSchemeStruct.baseChange`), written for the fibrewise reduction of
`[n]`. It lives DOWNSTREAM of this file, so it is invisible to
`Modularity/KhareWintenberger.lean`, which imports this module and not that
one; and it transports only `AbelianSchemeStruct`. The two developments agree
— `AbelianSchemeStruct.baseChange g` is `baseChangeOfIsPullback` at
`IsPullback.of_hasPullback f g` — and re-basing the downstream one on this
should be done by whoever next owns that file rather than here, since its
`baseChange_add` / `baseChange_zero` are `rfl`-lemmas about the current
definition.

## What transports, and what does NOT

`AbelianSchemeStruct`, `Mult`, `DualStruct` and `SymHomStruct` transport
UNCONDITIONALLY. The group law, the ring action, the Weil pairing and its four
axioms, the torsion submodules and the Galois action all move across the
bijection; the three geometric conditions move by mathlib's
`IsStableUnderBaseChange` instances for `IsProper`, `Smooth` and
`GeometricallyConnected`.

`PolarizationStruct` does NOT, and this is a mathematical fact about
polarizations rather than a gap in the proof. Thirteen of its fifteen fields
transport; the two that do not are exactly the ones that say `𝔞` IS the
polarization module:

* `lam_surjective` — that `λ : 𝔞 → Hom^sym_R(A, A^∨)` is ONTO. The group of
  symmetric homomorphisms GROWS under base change: already for `R = ℤ` it is
  the Néron–Severi group, and `NS` of a product of two elliptic curves that are
  isogenous only after a field extension jumps at that extension. A `𝔞` that
  exhausted `Hom^sym` over `S` need not exhaust it over `S'`.
* `lam_injective` — that `λ` is one-to-one. Take `S' = ∅` (with `q` the unique
  morphism, and `A' = ∅`, which satisfies every field of
  `AbelianSchemeStruct` vacuously). Every `RelPoint f' g` is then a singleton,
  so every `λ_a` is "zero", and `lam_injective` forces `𝔞 = 0`. So for any
  datum with `𝔞 ≠ 0` the source structure is inhabited and the base-changed
  one is not.

`PolarizationStruct.baseChangeOfIsPullback` therefore takes those two clauses
as HYPOTHESES, `hinj` and `hsurj`, stated verbatim as the fields they become.
That is the honest shape: a caller who has a reason for descent supplies it,
and everything else is free. Writing them as an unconditional sorried leaf
would be writing a FALSE leaf.

**THE TWO CLAUSES ARE NOT SYMMETRIC UNDER fppf** (correction, 2026-07-28 — an
earlier version of this paragraph offered "`q` faithfully flat and
quasi-compact, so that `Hom` is an fppf sheaf" as a reason discharging BOTH,
and that is wrong for the second one). The fppf sheaf condition on `Hom` is an
EQUALIZER

    Hom_S(A, A^∨)  ↪  Hom_{S'}(A', A'^∨)  ⇉  Hom_{S''}(A'', A''^∨),

`S'' = S' ×_S S'`. Its two halves say different things:

* SEPARATEDNESS — the first map is INJECTIVE — is unconditional in `s` and is
  exactly what `lam_injective` needs. It is PROVEN below as
  `SymHomStruct.hom_eq_of_baseChange_hom_eq`, and it discharges `hinj`
  (`PolarizationStruct.lam_injective_baseChange`), so
  `PolarizationStruct.baseChangeOfFppf` asks only for `hsurj`.
* EFFECTIVITY — an `s` over `S'` comes from `S` — holds only for those `s`
  that satisfy the COCYCLE CONDITION, i.e. whose two pullbacks to `S''` agree.
  `lam_surjective` quantifies over ALL `s : SymHomStruct d'`, so it needs
  every such `s` to be a descent datum, which is false.

**FALSITY AUDIT of the fppf claim for `lam_surjective`.** The witness is the
one already recorded above, and the point is that it IS an fppf base change.
Let `K/ℚ` be real quadratic, `E/K` an elliptic curve without CM, and
`A = Res_{K/ℚ} E` over `S = Spec ℚ`, with `R = 𝒪_K` acting. `A` is a simple
abelian surface and `Hom^sym_{𝒪_K}(A, A^∨)` has rank `1`, so it can be
`𝔞`. Take `q = Spec K ⟶ Spec ℚ`. That `q` is finite étale, hence **flat**,
**surjective** and **quasi-compact** — an fppf (indeed fpqc) covering, and
mathlib's `EffectiveEpi` instance applies to it verbatim. But
`A ×_ℚ K ≅ E × E^σ` and `Hom^sym_{𝒪_K}` there has rank `2`: the extra class
is the graph of the identification, which is defined over `K` and not over
`ℚ`. So `lam` cannot be onto over `S'` for ANY `𝔞` that worked over `S`,
while `q` satisfies every fppf hypothesis. Néron–Severi jumping at a field
extension is precisely a failure of effectivity for an fppf `q`, not a
failure of the fppf hypothesis.

Consequence for consumers: `hsurj` must come from something OTHER than
flatness of `q` — a cocycle condition checked by hand, a normalization pinned
across the family, or a moduli-theoretic reason why no new symmetric
homomorphisms appear.

## Cone status

Like the `DualStruct`/`PolarizationStruct` material above, the declarations in
this section are consumed only by proofs that are still `sorry` — they are the
transport layer the Hilbert–Blumenthal moduli leaves need in order to be cut
at all. They must NOT be swept as free-floating before those consumers are
proven. Everything here is PROVEN; there is no `sorry` in this section.
-/

section BaseChange

open _root_.CategoryTheory.Limits

namespace RelPoint

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}

/-- **A relative point of a base change, read as a relative point of the
original.** -/
def ofBaseChange (hp : IsPullback p f' f q) {T : Scheme.{u}} {g : T ⟶ S'} {g₀ : T ⟶ S}
    (hg : g ≫ q = g₀) (x : RelPoint f' g) : RelPoint f g₀ :=
  ⟨x.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, x.2, hg]⟩

/-- **A relative point of the original over a base point factoring through
`q`, read as a relative point of the base change.** -/
noncomputable def toBaseChange (hp : IsPullback p f' f q) {T : Scheme.{u}} {g : T ⟶ S'}
    {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (y : RelPoint f g₀) : RelPoint f' g :=
  ⟨hp.lift y.1 g (y.2.trans hg.symm), hp.lift_snd _ _ _⟩

@[simp] theorem ofBaseChange_val (hp : IsPullback p f' f q) {T : Scheme.{u}} {g : T ⟶ S'}
    {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (x : RelPoint f' g) :
    (ofBaseChange hp hg x).1 = x.1 ≫ p := rfl

@[simp] theorem ofBaseChange_toBaseChange (hp : IsPullback p f' f q) {T : Scheme.{u}}
    {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (y : RelPoint f g₀) :
    ofBaseChange hp hg (toBaseChange hp hg y) = y :=
  Subtype.ext (hp.lift_fst _ _ _)

@[simp] theorem toBaseChange_ofBaseChange (hp : IsPullback p f' f q) {T : Scheme.{u}}
    {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (x : RelPoint f' g) :
    toBaseChange hp hg (ofBaseChange hp hg x) = x := by
  refine Subtype.ext (hp.hom_ext ?_ ?_)
  · exact hp.lift_fst _ _ _
  · exact (hp.lift_snd _ _ _).trans x.2.symm

theorem ofBaseChange_injective (hp : IsPullback p f' f q) {T : Scheme.{u}}
    {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) :
    Function.Injective (ofBaseChange hp hg) :=
  Function.LeftInverse.injective (toBaseChange_ofBaseChange hp hg)

/-- **The base-change bijection on relative points.** -/
noncomputable def baseChangeEquiv (hp : IsPullback p f' f q) {T : Scheme.{u}}
    {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) : RelPoint f' g ≃ RelPoint f g₀ where
  toFun := ofBaseChange hp hg
  invFun := toBaseChange hp hg
  left_inv := toBaseChange_ofBaseChange hp hg
  right_inv := ofBaseChange_toBaseChange hp hg

@[simp] theorem baseChangeEquiv_apply (hp : IsPullback p f' f q) {T : Scheme.{u}}
    {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (x : RelPoint f' g) :
    baseChangeEquiv hp hg x = ofBaseChange hp hg x := rfl

@[simp] theorem baseChangeEquiv_symm_apply (hp : IsPullback p f' f q) {T : Scheme.{u}}
    {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (y : RelPoint f g₀) :
    (baseChangeEquiv hp hg).symm y = toBaseChange hp hg y := rfl

/-- The composite identification of base points used by `ofBaseChange_pre`. -/
theorem comp_base_of {T' T : Scheme.{u}} {h : T' ⟶ T} {g : T ⟶ S'} {g' : T' ⟶ S'}
    (hg : h ≫ g = g') {g₀ : T ⟶ S} {g₀' : T' ⟶ S} (hq : g ≫ q = g₀) (hq' : g' ≫ q = g₀') :
    h ≫ g₀ = g₀' := by
  rw [← hq, ← Category.assoc, hg, hq']

/-- **`ofBaseChange` is natural.** -/
theorem ofBaseChange_pre (hp : IsPullback p f' f q) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S'} {g' : T' ⟶ S'} (hg : h ≫ g = g') {g₀ : T ⟶ S} {g₀' : T' ⟶ S}
    (hq : g ≫ q = g₀) (hq' : g' ≫ q = g₀') (hh : h ≫ g₀ = g₀') (x : RelPoint f' g) :
    ofBaseChange hp hq' (RelPoint.pre h hg x) =
      RelPoint.pre h hh (ofBaseChange hp hq x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- `ofBaseChange_pre` at the tautological identification of base points. -/
theorem ofBaseChange_pre_rfl (hp : IsPullback p f' f q) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S'} {g' : T' ⟶ S'} (hg : h ≫ g = g') (x : RelPoint f' g) :
    ofBaseChange hp (rfl : g' ≫ q = g' ≫ q) (RelPoint.pre h hg x) =
      RelPoint.pre h (comp_base_of hg rfl rfl) (ofBaseChange hp rfl x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- **The base-change map on the geometric points of a fibre.** -/
noncomputable abbrev ofBaseChangeGeom (hp : IsPullback p f' f q) {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S') (y : GeomFibrePt f' x) : GeomFibrePt f (x ≫ q) :=
  ofBaseChange hp (Category.assoc _ _ _) y

/-- **The base-change map on the geometric points of a fibre, backwards.** -/
noncomputable abbrev toBaseChangeGeom (hp : IsPullback p f' f q) {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S') (y : GeomFibrePt f (x ≫ q)) : GeomFibrePt f' x :=
  toBaseChange hp (Category.assoc _ _ _) y

theorem ofBaseChangeGeom_injective (hp : IsPullback p f' f q) {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S') :
    Function.Injective (ofBaseChangeGeom hp x) :=
  ofBaseChange_injective hp _

@[simp] theorem ofBaseChangeGeom_toBaseChangeGeom (hp : IsPullback p f' f q) {F : Type u}
    [Field F] (x : Spec (CommRingCat.of F) ⟶ S') (y : GeomFibrePt f (x ≫ q)) :
    ofBaseChangeGeom hp x (toBaseChangeGeom hp x y) = y :=
  ofBaseChange_toBaseChange hp _ y

section Map

variable {D D' : Scheme.{u}} {e : D ⟶ S} {e' : D' ⟶ S'} {pd : D' ⟶ D}

/-- **Base change of a natural transformation of functors of points.** -/
noncomputable def baseChangeMap (hp : IsPullback p f' f q) (hpd : IsPullback pd e' e q)
    (H : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint e g)
    {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g) : RelPoint e' g :=
  toBaseChange hpd rfl (H (ofBaseChange hp rfl y))

@[simp] theorem ofBaseChange_baseChangeMap (hp : IsPullback p f' f q)
    (hpd : IsPullback pd e' e q)
    (H : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint e g)
    {T : Scheme.{u}} {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (y : RelPoint f' g) :
    ofBaseChange hpd hg (baseChangeMap hp hpd H y) = H (ofBaseChange hp hg y) := by
  subst hg
  exact ofBaseChange_toBaseChange _ _ _

/-- **`baseChangeMap` inherits naturality from the map it transports.** -/
theorem pre_baseChangeMap (hp : IsPullback p f' f q) (hpd : IsPullback pd e' e q)
    (H : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint e g)
    (Hpre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g')
      (y : RelPoint f g), RelPoint.pre h hg (H y) = H (RelPoint.pre h hg y))
    {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S'} {g' : T' ⟶ S'} (hg : h ≫ g = g')
    (y : RelPoint f' g) :
    RelPoint.pre h hg (baseChangeMap hp hpd H y) =
      baseChangeMap hp hpd H (RelPoint.pre h hg y) := by
  apply ofBaseChange_injective hpd (rfl : g' ≫ q = g' ≫ q)
  rw [ofBaseChange_pre_rfl, ofBaseChange_baseChangeMap, ofBaseChange_baseChangeMap,
    ofBaseChange_pre_rfl, Hpre]

end Map

end RelPoint

namespace AbelianSchemeStruct

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}

/-- **Base change of an abelian scheme structure along an arbitrary
pullback square.** -/
noncomputable def baseChangeOfIsPullback (ab : AbelianSchemeStruct f)
    (hp : IsPullback p f' f q) : AbelianSchemeStruct f' where
  add := fun {_} {_} x y =>
    RelPoint.toBaseChange hp rfl
      (ab.add (RelPoint.ofBaseChange hp rfl x) (RelPoint.ofBaseChange hp rfl y))
  zero := fun {_} g => RelPoint.toBaseChange hp (rfl : g ≫ q = g ≫ q) (ab.zero (g ≫ q))
  neg := fun {_} {_} x =>
    RelPoint.toBaseChange hp rfl (ab.neg (RelPoint.ofBaseChange hp rfl x))
  add_assoc := by
    intro T g x y z
    rw [RelPoint.ofBaseChange_toBaseChange, RelPoint.ofBaseChange_toBaseChange, ab.add_assoc]
  add_comm := by
    intro T g x y
    rw [ab.add_comm]
  zero_add := by
    intro T g x
    rw [RelPoint.ofBaseChange_toBaseChange, ab.zero_add, RelPoint.toBaseChange_ofBaseChange]
  neg_add := by
    intro T g x
    rw [RelPoint.ofBaseChange_toBaseChange, ab.neg_add]
  pre_add := by
    intro T' T h g g' hg x y
    apply RelPoint.ofBaseChange_injective hp (rfl : g' ≫ q = g' ≫ q)
    simp only [RelPoint.ofBaseChange_pre_rfl, RelPoint.ofBaseChange_toBaseChange]
    exact ab.pre_add h _ _ _
  pre_zero := by
    intro T' T h g g' hg
    apply RelPoint.ofBaseChange_injective hp (rfl : g' ≫ q = g' ≫ q)
    simp only [RelPoint.ofBaseChange_pre_rfl, RelPoint.ofBaseChange_toBaseChange]
    exact ab.pre_zero h _
  proper := MorphismProperty.IsStableUnderBaseChange.of_isPullback hp ab.proper
  smooth := MorphismProperty.IsStableUnderBaseChange.of_isPullback hp ab.smooth
  connected := MorphismProperty.IsStableUnderBaseChange.of_isPullback hp ab.connected

@[simp] theorem ofBaseChange_add (ab : AbelianSchemeStruct f) (hp : IsPullback p f' f q)
    {T : Scheme.{u}} {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀)
    (x y : RelPoint f' g) :
    RelPoint.ofBaseChange hp hg ((ab.baseChangeOfIsPullback hp).add x y) =
      ab.add (RelPoint.ofBaseChange hp hg x) (RelPoint.ofBaseChange hp hg y) := by
  subst hg
  exact RelPoint.ofBaseChange_toBaseChange _ _ _

@[simp] theorem ofBaseChange_zero (ab : AbelianSchemeStruct f) (hp : IsPullback p f' f q)
    {T : Scheme.{u}} {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) :
    RelPoint.ofBaseChange hp hg ((ab.baseChangeOfIsPullback hp).zero g) = ab.zero g₀ := by
  subst hg
  exact RelPoint.ofBaseChange_toBaseChange _ _ _

@[simp] theorem ofBaseChange_neg (ab : AbelianSchemeStruct f) (hp : IsPullback p f' f q)
    {T : Scheme.{u}} {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (x : RelPoint f' g) :
    RelPoint.ofBaseChange hp hg ((ab.baseChangeOfIsPullback hp).neg x) =
      ab.neg (RelPoint.ofBaseChange hp hg x) := by
  subst hg
  exact RelPoint.ofBaseChange_toBaseChange _ _ _

@[simp] theorem ofBaseChangeGeom_add (ab : AbelianSchemeStruct f) (hp : IsPullback p f' f q)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S') (y y' : GeomFibrePt f' x) :
    RelPoint.ofBaseChangeGeom hp x ((ab.baseChangeOfIsPullback hp).add y y') =
      ab.add (RelPoint.ofBaseChangeGeom hp x y) (RelPoint.ofBaseChangeGeom hp x y') :=
  ofBaseChange_add ab hp _ y y'

@[simp] theorem ofBaseChangeGeom_zero (ab : AbelianSchemeStruct f) (hp : IsPullback p f' f q)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S') :
    RelPoint.ofBaseChangeGeom hp x
        ((ab.baseChangeOfIsPullback hp).zero (specAlgClos F ≫ x)) =
      ab.zero (specAlgClos F ≫ (x ≫ q)) :=
  ofBaseChange_zero ab hp _

@[simp] theorem ofBaseChangeGeom_galSMul (ab : AbelianSchemeStruct f)
    (hp : IsPullback p f' f q) {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S')
    (σ : Field.absoluteGaloisGroup F) (y : GeomFibrePt f' x) :
    RelPoint.ofBaseChangeGeom hp x ((ab.baseChangeOfIsPullback hp).galSMul x σ y) =
      ab.galSMul (x ≫ q) σ (RelPoint.ofBaseChangeGeom hp x y) := by
  rw [AbelianSchemeStruct.galSMul_def, AbelianSchemeStruct.galSMul_def]
  exact RelPoint.ofBaseChange_pre hp (specGal σ) (specGal_comp_base x σ) _ _ _ y

end AbelianSchemeStruct

namespace Mult

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}
variable {ab : AbelianSchemeStruct f} {R : Type u} [CommRing R]

/-- **Base change of a multiplication.** -/
noncomputable def baseChangeOfIsPullback (m : Mult ab R) (hp : IsPullback p f' f q) :
    Mult (ab.baseChangeOfIsPullback hp) R where
  act := fun {_} {_} a x =>
    RelPoint.toBaseChange hp rfl (m.act a (RelPoint.ofBaseChange hp rfl x))
  act_add := by
    intro T g a b y
    apply RelPoint.ofBaseChange_injective hp (rfl : g ≫ q = g ≫ q)
    simp only [AbelianSchemeStruct.ofBaseChange_add, RelPoint.ofBaseChange_toBaseChange]
    exact m.act_add a b _
  act_mul := by
    intro T g a b y
    apply RelPoint.ofBaseChange_injective hp (rfl : g ≫ q = g ≫ q)
    simp only [RelPoint.ofBaseChange_toBaseChange]
    exact m.act_mul a b _
  act_one := by
    intro T g y
    simp only [m.act_one, RelPoint.toBaseChange_ofBaseChange]
  act_addPt := by
    intro T g a y z
    apply RelPoint.ofBaseChange_injective hp (rfl : g ≫ q = g ≫ q)
    simp only [AbelianSchemeStruct.ofBaseChange_add, RelPoint.ofBaseChange_toBaseChange]
    exact m.act_addPt a _ _
  pre_act := by
    intro T' T h g g' hg a y
    apply RelPoint.ofBaseChange_injective hp (rfl : g' ≫ q = g' ≫ q)
    simp only [RelPoint.ofBaseChange_pre_rfl, RelPoint.ofBaseChange_toBaseChange]
    exact m.pre_act h _ a _

@[simp] theorem ofBaseChange_act (m : Mult ab R) (hp : IsPullback p f' f q)
    {T : Scheme.{u}} {g : T ⟶ S'} {g₀ : T ⟶ S} (hg : g ≫ q = g₀) (a : R)
    (x : RelPoint f' g) :
    RelPoint.ofBaseChange hp hg ((m.baseChangeOfIsPullback hp).act a x) =
      m.act a (RelPoint.ofBaseChange hp hg x) := by
  subst hg
  exact RelPoint.ofBaseChange_toBaseChange _ _ _

@[simp] theorem ofBaseChangeGeom_act (m : Mult ab R) (hp : IsPullback p f' f q)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S') (a : R)
    (y : GeomFibrePt f' x) :
    RelPoint.ofBaseChangeGeom hp x ((m.baseChangeOfIsPullback hp).act a y) =
      m.act a (RelPoint.ofBaseChangeGeom hp x y) :=
  ofBaseChange_act m hp _ a y

/-- **Membership in the `I`-torsion, unbundled**: a geometric point of the
fibre lies in `A[I]` exactly when every element of `I` kills it. This is
`Submodule.mem_torsionBySet_iff` read through the `R`-module structure
`Mult.module` of `Mult.torsion`.

`Modularity/TateModule.lean` carries the same statement as a top-level
`Fermat.mem_torsion_iff`, specialised to `R = 𝒪_D`; it predates this one and
is used ~20 times there. The two do not collide (this one is
`Fermat.Mult.mem_torsion_iff`), but the specialised one is redundant once
this is available and should be retired by whoever next owns that file. -/
theorem mem_torsion_iff (m : Mult ab R) {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S) (I : Ideal R) (y : GeomFibrePt f x) :
    y ∈ (m.torsion x I).1 ↔ ∀ a ∈ I, m.act a y = ab.zero (specAlgClos F ≫ x) := by
  letI := ab.addCommGroup (specAlgClos F ≫ x)
  letI := m.module (specAlgClos F ≫ x)
  constructor
  · intro hy a ha
    exact (Submodule.mem_torsionBySet_iff _ _).mp hy ⟨a, ha⟩
  · intro hy
    exact SetLike.mem_coe.mpr ((Submodule.mem_torsionBySet_iff _ _).mpr
      (fun a => hy (a : R) a.2))

/-- **The base-change bijection carries `I`-torsion to `I`-torsion, both
ways.** -/
theorem mem_torsion_baseChange_iff (m : Mult ab R) (hp : IsPullback p f' f q)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S') (I : Ideal R)
    (y : GeomFibrePt f' x) :
    y ∈ ((m.baseChangeOfIsPullback hp).torsion x I).1 ↔
      RelPoint.ofBaseChangeGeom hp x y ∈ (m.torsion (x ≫ q) I).1 := by
  rw [mem_torsion_iff, mem_torsion_iff]
  constructor
  · intro hy a ha
    rw [← ofBaseChangeGeom_act m hp x a y, hy a ha]
    exact AbelianSchemeStruct.ofBaseChangeGeom_zero ab hp x
  · intro hy a ha
    apply RelPoint.ofBaseChangeGeom_injective hp x
    rw [ofBaseChangeGeom_act m hp x a y, hy a ha,
      AbelianSchemeStruct.ofBaseChangeGeom_zero ab hp x]

end Mult

namespace DualStruct

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}
variable {ab : AbelianSchemeStruct f} {R : Type u} [CommRing R] {m : Mult ab R}

/-- **Base change of a dual pair with its Weil pairing.** -/
noncomputable def baseChangeOfIsPullback (d : DualStruct ab m) (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) :
    DualStruct (ab.baseChangeOfIsPullback hp) (m.baseChangeOfIsPullback hp) where
  dualScheme := D'
  dualMap := dm'
  dualAb := d.dualAb.baseChangeOfIsPullback hpd
  dualMult := d.dualMult.baseChangeOfIsPullback hpd
  weil := fun {_} _ x I n hn y z =>
    d.weil (x ≫ q) I n hn (RelPoint.ofBaseChangeGeom hp x y)
      (RelPoint.ofBaseChangeGeom hpd x z)
  weil_add_left := by
    intro F _ x I n hn y y' z hy hy' hz
    rw [AbelianSchemeStruct.ofBaseChangeGeom_add]
    exact d.weil_add_left (x ≫ q) I n hn _ _ _
      ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)
      ((Mult.mem_torsion_baseChange_iff m hp x I y').mp hy')
      ((Mult.mem_torsion_baseChange_iff d.dualMult hpd x I z).mp hz)
  weil_add_right := by
    intro F _ x I n hn y z z' hy hz hz'
    rw [AbelianSchemeStruct.ofBaseChangeGeom_add]
    exact d.weil_add_right (x ≫ q) I n hn _ _ _
      ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)
      ((Mult.mem_torsion_baseChange_iff d.dualMult hpd x I z).mp hz)
      ((Mult.mem_torsion_baseChange_iff d.dualMult hpd x I z').mp hz')
  weil_gal := by
    intro F _ x I n hn σ y z hy hz
    rw [AbelianSchemeStruct.ofBaseChangeGeom_galSMul,
      AbelianSchemeStruct.ofBaseChangeGeom_galSMul]
    exact d.weil_gal (x ≫ q) I n hn σ _ _
      ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)
      ((Mult.mem_torsion_baseChange_iff d.dualMult hpd x I z).mp hz)
  weil_act := by
    intro F _ x I n hn a y z hy hz
    rw [Mult.ofBaseChangeGeom_act, Mult.ofBaseChangeGeom_act]
    exact d.weil_act (x ≫ q) I n hn a _ _
      ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)
      ((Mult.mem_torsion_baseChange_iff d.dualMult hpd x I z).mp hz)
  weil_nondegenerate := by
    intro F _ x I n hn hnF y hy hz
    apply RelPoint.ofBaseChangeGeom_injective hp x
    rw [AbelianSchemeStruct.ofBaseChangeGeom_zero]
    refine d.weil_nondegenerate (x ≫ q) I n hn hnF _
      ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy) ?_
    intro z hzt
    have hzt' : RelPoint.toBaseChangeGeom hpd x z ∈
        ((d.dualMult.baseChangeOfIsPullback hpd).torsion x I).1 := by
      rw [Mult.mem_torsion_baseChange_iff, RelPoint.ofBaseChangeGeom_toBaseChangeGeom]
      exact hzt
    have := hz (RelPoint.toBaseChangeGeom hpd x z) hzt'
    rwa [RelPoint.ofBaseChangeGeom_toBaseChangeGeom] at this

@[simp] theorem baseChangeOfIsPullback_dualAb (d : DualStruct ab m) (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) :
    (d.baseChangeOfIsPullback hp hpd).dualAb = d.dualAb.baseChangeOfIsPullback hpd := rfl

@[simp] theorem baseChangeOfIsPullback_dualMult (d : DualStruct ab m) (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) :
    (d.baseChangeOfIsPullback hp hpd).dualMult = d.dualMult.baseChangeOfIsPullback hpd := rfl

@[simp] theorem baseChangeOfIsPullback_weil (d : DualStruct ab m) (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) {F : Type u} [Field F]
    (x : Spec (CommRingCat.of F) ⟶ S') (I : Ideal R) (n : ℕ) (hn : (n : R) ∈ I)
    (y : GeomFibrePt f' x) (z : GeomFibrePt dm' x) :
    (d.baseChangeOfIsPullback hp hpd).weil x I n hn y z =
      d.weil (x ≫ q) I n hn (RelPoint.ofBaseChangeGeom hp x y)
        (RelPoint.ofBaseChangeGeom hpd x z) := rfl

end DualStruct

namespace SymHomStruct

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}
variable {ab : AbelianSchemeStruct f} {R : Type u} [CommRing R] {m : Mult ab R}
variable {d : DualStruct ab m}

/-- **Base change of a symmetric `R`-linear homomorphism `A ⟶ A^∨`.** -/
noncomputable def baseChangeOfIsPullback (s : SymHomStruct d) (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) :
    SymHomStruct (d.baseChangeOfIsPullback hp hpd) where
  hom := fun {_} {_} y => RelPoint.baseChangeMap hp hpd (fun {_} {_} => s.hom) y
  hom_add := by
    intro T g y y'
    apply RelPoint.ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
    simp only [DualStruct.baseChangeOfIsPullback_dualAb, RelPoint.ofBaseChange_baseChangeMap,
      AbelianSchemeStruct.ofBaseChange_add]
    exact s.hom_add _ _
  pre_hom := by
    intro T' T h g g' hg y
    exact RelPoint.pre_baseChangeMap hp hpd (fun {_} {_} => s.hom)
      (@SymHomStruct.pre_hom _ _ _ _ _ _ _ _ s) h hg y
  hom_act := by
    intro T g a y
    apply RelPoint.ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
    simp only [DualStruct.baseChangeOfIsPullback_dualMult, RelPoint.ofBaseChange_baseChangeMap,
      Mult.ofBaseChange_act]
    exact s.hom_act a _
  hom_torsion := by
    intro F _ x I y hy
    refine (Mult.mem_torsion_baseChange_iff d.dualMult hpd x I _).mpr ?_
    simp only [RelPoint.ofBaseChange_baseChangeMap]
    exact s.hom_torsion (x ≫ q) I _ ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)
  weil_self := by
    intro F _ x I n hn y hy
    simp only [DualStruct.baseChangeOfIsPullback_weil, RelPoint.ofBaseChangeGeom,
      RelPoint.ofBaseChange_baseChangeMap]
    exact s.weil_self (x ≫ q) I n hn _ ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)

@[simp] theorem ofBaseChange_hom (s : SymHomStruct d) (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) {T : Scheme.{u}} {g : T ⟶ S'} {g₀ : T ⟶ S}
    (hg : g ≫ q = g₀) (y : RelPoint f' g) :
    RelPoint.ofBaseChange hpd hg ((s.baseChangeOfIsPullback hp hpd).hom y) =
      s.hom (RelPoint.ofBaseChange hp hg y) :=
  RelPoint.ofBaseChange_baseChangeMap hp hpd _ hg y

end SymHomStruct

namespace PolarizationStruct

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}
variable {ab : AbelianSchemeStruct f} {R : Type u} [CommRing R] {m : Mult ab R}
variable {d : DualStruct ab m} {𝒩 : Set (Ideal R)} {𝔞 : Ideal R} {𝔞pos : Set R}

/-- **Base change of a polarization, given the two descent clauses.** -/
noncomputable def baseChangeOfIsPullback (pol : PolarizationStruct d 𝒩 𝔞 𝔞pos)
    (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q)
    (hinj : ∀ a : ↥𝔞, (∀ {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g),
        ((pol.lam a).baseChangeOfIsPullback hp hpd).hom y =
          (d.baseChangeOfIsPullback hp hpd).dualAb.zero g) → a = 0)
    (hsurj : ∀ s : SymHomStruct (d.baseChangeOfIsPullback hp hpd), ∃ a : ↥𝔞,
        ∀ {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g),
          ((pol.lam a).baseChangeOfIsPullback hp hpd).hom y = s.hom y) :
    PolarizationStruct (d.baseChangeOfIsPullback hp hpd) 𝒩 𝔞 𝔞pos where
  hom := fun {_} {_} y => RelPoint.baseChangeMap hp hpd (fun {_} {_} => pol.hom) y
  hom_add := by
    intro T g y y'
    apply RelPoint.ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
    simp only [DualStruct.baseChangeOfIsPullback_dualAb, RelPoint.ofBaseChange_baseChangeMap,
      AbelianSchemeStruct.ofBaseChange_add]
    exact pol.hom_add _ _
  pre_hom := by
    intro T' T h g g' hg y
    exact RelPoint.pre_baseChangeMap hp hpd (fun {_} {_} => pol.hom)
      (@PolarizationStruct.pre_hom _ _ _ _ _ _ _ _ _ _ _ pol) h hg y
  hom_act := by
    intro T g a y
    apply RelPoint.ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
    simp only [DualStruct.baseChangeOfIsPullback_dualMult, RelPoint.ofBaseChange_baseChangeMap,
      Mult.ofBaseChange_act]
    exact pol.hom_act a _
  hom_torsion := by
    intro F _ x I y hy
    refine (Mult.mem_torsion_baseChange_iff d.dualMult hpd x I _).mpr ?_
    simp only [RelPoint.ofBaseChange_baseChangeMap]
    exact pol.hom_torsion (x ≫ q) I _ ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)
  weil_self := by
    intro F _ x I n hn y hy
    simp only [DualStruct.baseChangeOfIsPullback_weil, RelPoint.ofBaseChangeGeom,
      RelPoint.ofBaseChange_baseChangeMap]
    exact pol.weil_self (x ≫ q) I n hn _ ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy)
  weil_hom_nondegenerate := by
    -- as for `DualStruct.weil_nondegenerate`: the point moves from `x` to
    -- `x ≫ q`, its residue field `F` does not, so `hnF` passes through.
    intro F _ x I hI n hn y hnF hy hz
    apply RelPoint.ofBaseChangeGeom_injective hp x
    rw [AbelianSchemeStruct.ofBaseChangeGeom_zero]
    refine pol.weil_hom_nondegenerate (x ≫ q) I hI n hn _ hnF
      ((Mult.mem_torsion_baseChange_iff m hp x I y).mp hy) ?_
    intro z hzt
    have hzt' : RelPoint.toBaseChangeGeom hp x z ∈
        ((m.baseChangeOfIsPullback hp).torsion x I).1 := by
      rw [Mult.mem_torsion_baseChange_iff, RelPoint.ofBaseChangeGeom_toBaseChangeGeom]
      exact hzt
    have h := hz (RelPoint.toBaseChangeGeom hp x z) hzt'
    simp only [DualStruct.baseChangeOfIsPullback_weil, RelPoint.ofBaseChangeGeom,
      RelPoint.ofBaseChange_baseChangeMap, RelPoint.ofBaseChange_toBaseChange] at h
    exact h
  lam := fun a => (pol.lam a).baseChangeOfIsPullback hp hpd
  lam_add := by
    intro a b T g y
    apply RelPoint.ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
    simp only [DualStruct.baseChangeOfIsPullback_dualAb, SymHomStruct.ofBaseChange_hom,
      AbelianSchemeStruct.ofBaseChange_add]
    exact pol.lam_add a b _
  lam_smul := by
    intro c a T g y
    apply RelPoint.ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
    simp only [DualStruct.baseChangeOfIsPullback_dualMult, SymHomStruct.ofBaseChange_hom,
      Mult.ofBaseChange_act]
    exact pol.lam_smul c a _
  lam_injective := hinj
  lam_surjective := hsurj
  posElt := pol.posElt
  posElt_pos := pol.posElt_pos
  hom_eq_lam := by
    intro T g y
    apply RelPoint.ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
    simp only [SymHomStruct.ofBaseChange_hom, RelPoint.ofBaseChange_baseChangeMap]
    exact pol.hom_eq_lam _

end PolarizationStruct

/-!
### fppf descent for symmetric homomorphisms

The two clauses that `PolarizationStruct.baseChangeOfIsPullback` cannot
transport are `lam_injective` and `lam_surjective`. This section proves the
half of fppf descent that discharges the FIRST of them, and records — with a
counterexample, in the section docstring above — that no amount of flatness
discharges the second.

**What is proven.** `Hom` is a sheaf for the fpqc topology, and the
separatedness half of the sheaf condition is that a homomorphism is determined
by its base change along a covering. Concretely, `q : S' ⟶ S` faithfully flat
and quasi-compact is a UNIVERSAL EPIMORPHISM: mathlib's
`AlgebraicGeometry.Scheme` instance makes any surjective, quasi-compact, flat
morphism an `EffectiveEpi`, and `Flat`, `Surjective` and `QuasiCompact` are
each stable under base change, so every projection `T ×_S S' ⟶ T` is an
epimorphism too. Two natural transformations of functors of points over `S`
whose base changes to `S'` agree therefore agree already over `S`: evaluate at
a relative point `y` over `g : T ⟶ S`, pull `y` back to `T ×_S S'`, and cancel
the epimorphism. That is `RelPoint.eq_of_baseChangeMap_eq`, and
`SymHomStruct.hom_eq_of_baseChange_hom_eq` is its specialization to symmetric
homomorphisms.

**Why the hypothesis is `Flat` + `Surjective` + `QuasiCompact` rather than
`LocallyOfFinitePresentation`.** Both are available: mathlib carries an
`EffectiveEpi` instance for each. The fpqc form is used here because it is the
weaker of the two on the flat side and because `QuasiCompact` is what the rest
of this development already carries. A caller holding an fppf covering in the
finite-presentation form supplies `RelPoint.eq_of_baseChangeMap_eq`'s explicit
`hq` argument directly — that is exactly why `hq` is an ordinary hypothesis
there and instances appear only in the wrappers below.

**What is NOT proven, and is FALSE.** That `lam_surjective` descends. See the
FALSITY AUDIT in the section docstring above: `Res_{K/ℚ} E` base changed along
the finite étale `Spec K ⟶ Spec ℚ` has `Hom^sym_{𝒪_K}` of rank `2` where the
source has rank `1`. Effectivity of fppf descent is conditional on the cocycle
condition, and `lam_surjective` quantifies over symmetric homomorphisms that
need not satisfy it. `PolarizationStruct.baseChangeOfFppf` therefore still
takes `hsurj` as a hypothesis, and only `hinj` has been discharged.

Everything in this section is PROVEN; it contains no `sorry`.
-/

namespace RelPoint

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}

/-- **A faithfully flat quasi-compact morphism is a UNIVERSAL epimorphism.**

`Flat`, `Surjective` and `QuasiCompact` are each stable under base change, and
mathlib makes a morphism with all three an `EffectiveEpi`, hence an `Epi`. So
every base change `t` of such a `q` — in particular every projection
`T ×_S S' ⟶ T` — may be cancelled on the left. This is the only input the
descent theorems below take from the geometry of `q`. -/
theorem epi_of_isPullback_of_flat [Flat q] [Surjective q] [QuasiCompact q]
    {T T' : Scheme.{u}} {t : T' ⟶ T} {g : T ⟶ S} {g' : T' ⟶ S'} (ht : IsPullback t g' g q) :
    Epi t := by
  haveI : Flat t := MorphismProperty.IsStableUnderBaseChange.of_isPullback ht.flip ‹Flat q›
  haveI : Surjective t :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ht.flip ‹Surjective q›
  haveI : QuasiCompact t :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ht.flip ‹QuasiCompact q›
  infer_instance

/-- **Relative points are separated by an epimorphic change of test object**:
if two `T`-points of `e` become equal after precomposition with an
epimorphism `t : T' ⟶ T`, they were equal. A `RelPoint` is a subtype of
morphisms, so this is `cancel_epi` plus `Subtype.ext`. -/
theorem eq_of_pre_eq_of_epi {D T T' : Scheme.{u}} {e : D ⟶ S} {g : T ⟶ S} {t : T' ⟶ T} [Epi t]
    {u v : RelPoint e g}
    (h : RelPoint.pre t (rfl : t ≫ g = t ≫ g) u = RelPoint.pre t rfl v) : u = v := by
  have h' : t ≫ u.1 = t ≫ v.1 := congrArg Subtype.val h
  exact Subtype.ext ((cancel_epi t).mp h')

/-- **fppf DESCENT FOR HOMOMORPHISMS, SEPARATEDNESS HALF.**

A natural transformation of functors of points over `S` is determined by its
base change along `q`, as soon as `q` is a universal epimorphism (`hq`; supply
`epi_of_isPullback_of_flat` when `q` is faithfully flat and quasi-compact).

This is the separatedness half of the statement that `Hom` is an fppf sheaf,
and it is the reusable form: `H` and `K` are arbitrary transformations with
their naturality, so the theorem applies to homomorphisms of abelian schemes,
to the zero section, and to anything else `RelPoint.baseChangeMap` transports.
The EFFECTIVITY half — that a transformation over `S'` DESCENDS — is a strictly
further statement, true only under the cocycle condition, and is deliberately
not asserted here; see the FALSITY AUDIT in the section docstring.

The proof is the standard one. Given `y` over `g : T ⟶ S`, form `T ×_S S'`;
its first projection `t` is a base change of `q`, hence an epimorphism, and its
second projection makes `RelPoint.pre t rfl y` come from a relative point of
`f'`. The hypothesis at that point, read back through
`RelPoint.ofBaseChange_baseChangeMap`, gives `H (pre t rfl y) = K (pre t rfl y)`;
naturality moves `pre t rfl` outside, and `t` cancels. -/
theorem eq_of_baseChangeMap_eq {D D' : Scheme.{u}} {e : D ⟶ S} {e' : D' ⟶ S'} {pd : D' ⟶ D}
    (hp : IsPullback p f' f q) (hpd : IsPullback pd e' e q)
    (hq : ∀ {T T' : Scheme.{u}} {t : T' ⟶ T} {g : T ⟶ S} {g' : T' ⟶ S'},
      IsPullback t g' g q → Epi t)
    (H K : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint e g)
    (Hpre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g')
      (y : RelPoint f g), RelPoint.pre h hg (H y) = H (RelPoint.pre h hg y))
    (Kpre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g')
      (y : RelPoint f g), RelPoint.pre h hg (K y) = K (RelPoint.pre h hg y))
    (hHK : ∀ {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g),
      baseChangeMap hp hpd (fun {_} {_} => H) y = baseChangeMap hp hpd (fun {_} {_} => K) y)
    {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g) : H y = K y := by
  have ht : IsPullback (pullback.fst g q) (pullback.snd g q) g q := IsPullback.of_hasPullback g q
  have hg : pullback.snd g q ≫ q = pullback.fst g q ≫ g := ht.w.symm
  haveI : Epi (pullback.fst g q) := hq ht
  refine eq_of_pre_eq_of_epi (t := pullback.fst g q) ?_
  rw [Hpre, Kpre]
  have h1 := hHK (toBaseChange hp hg
    (RelPoint.pre (pullback.fst g q) (rfl : pullback.fst g q ≫ g = pullback.fst g q ≫ g) y))
  have h2 := congrArg (ofBaseChange hpd hg) h1
  rwa [ofBaseChange_baseChangeMap, ofBaseChange_baseChangeMap, ofBaseChange_toBaseChange] at h2

/-- **The base change of the constant zero transformation is the zero
section of the base-changed abelian scheme.** This is what lets
`eq_of_baseChangeMap_eq` be applied against "`λ_a` is zero after base change",
whose right-hand side is written with the base-changed `zero` rather than as a
transported transformation. -/
theorem baseChangeMap_zero {D D' : Scheme.{u}} {e : D ⟶ S} {e' : D' ⟶ S'} {pd : D' ⟶ D}
    (hp : IsPullback p f' f q) (hpd : IsPullback pd e' e q) (ab₂ : AbelianSchemeStruct e)
    {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g) :
    baseChangeMap hp hpd (fun {_} {g₀} (_ : RelPoint f g₀) => ab₂.zero g₀) y =
      (ab₂.baseChangeOfIsPullback hpd).zero g := by
  apply ofBaseChange_injective hpd (rfl : g ≫ q = g ≫ q)
  rw [ofBaseChange_baseChangeMap, AbelianSchemeStruct.ofBaseChange_zero]

end RelPoint

namespace SymHomStruct

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}
variable {ab : AbelianSchemeStruct f} {R : Type u} [CommRing R] {m : Mult ab R}
variable {d : DualStruct ab m}

/-- **fppf DESCENT FOR SYMMETRIC HOMOMORPHISMS.**

Two symmetric `R`-linear homomorphisms `A ⟶ A^∨` whose base changes along a
faithfully flat quasi-compact `q` agree, agree. Equivalently:
`SymHomStruct.baseChangeOfIsPullback` is injective on the underlying
homomorphism, which is the separatedness half of the fppf sheaf condition for
`Hom^sym_R(A, A^∨)`.

`SymHomStruct` bundles proofs (`hom_add`, `weil_self`, …) along with the map,
so the conclusion is stated on `hom` rather than as `s = s₂`: two structures
with equal `hom` fields carry propositionally equal but not syntactically
identical proof fields, and every consumer here compares `hom`s.

Note that the EFFECTIVITY half fails: `Hom^sym` genuinely grows under fppf
base change (`Res_{K/ℚ} E` along `Spec K ⟶ Spec ℚ`), so there is no companion
surjectivity statement to be had. -/
theorem hom_eq_of_baseChange_hom_eq (s s₂ : SymHomStruct d) (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) [Flat q] [Surjective q] [QuasiCompact q]
    (h : ∀ {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g),
      (s.baseChangeOfIsPullback hp hpd).hom y = (s₂.baseChangeOfIsPullback hp hpd).hom y)
    {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g) : s.hom y = s₂.hom y :=
  RelPoint.eq_of_baseChangeMap_eq hp hpd (fun ht => RelPoint.epi_of_isPullback_of_flat ht)
    (fun {_} {_} => s.hom) (fun {_} {_} => s₂.hom)
    (@SymHomStruct.pre_hom _ _ _ _ _ _ _ _ s) (@SymHomStruct.pre_hom _ _ _ _ _ _ _ _ s₂)
    (fun y => h y) y

end SymHomStruct

namespace PolarizationStruct

variable {A S A' S' : Scheme.{u}} {f : A ⟶ S} {f' : A' ⟶ S'} {p : A' ⟶ A} {q : S' ⟶ S}
variable {ab : AbelianSchemeStruct f} {R : Type u} [CommRing R] {m : Mult ab R}
variable {d : DualStruct ab m} {𝒩 : Set (Ideal R)} {𝔞 : Ideal R} {𝔞pos : Set R}

/-- **`lam_injective` DESCENDS along a faithfully flat quasi-compact `q`** —
the first of the two clauses that `baseChangeOfIsPullback` takes as a
hypothesis, discharged.

This is `SymHomStruct.hom_eq_of_baseChange_hom_eq` against the constant zero
transformation rather than against a second `SymHomStruct`: `λ_a` being zero
after base change forces `λ_a` to be zero, and `pol.lam_injective` then gives
`a = 0`. The zero transformation is natural by `AbelianSchemeStruct.pre_zero`,
and `RelPoint.baseChangeMap_zero` identifies its base change with the zero
section of the base-changed dual. -/
theorem lam_injective_baseChange (pol : PolarizationStruct d 𝒩 𝔞 𝔞pos)
    (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) [Flat q] [Surjective q] [QuasiCompact q]
    (a : ↥𝔞)
    (h : ∀ {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g),
      ((pol.lam a).baseChangeOfIsPullback hp hpd).hom y =
        (d.baseChangeOfIsPullback hp hpd).dualAb.zero g) : a = 0 := by
  refine pol.lam_injective a ?_
  intro T g y
  refine RelPoint.eq_of_baseChangeMap_eq hp hpd
      (fun ht => RelPoint.epi_of_isPullback_of_flat ht) (fun {_} {_} => (pol.lam a).hom)
      (fun {_} {g₀} (_ : RelPoint f g₀) => d.dualAb.zero g₀) ?_ ?_ ?_ y
  · intro T' T h' g' g'' hg y
    exact (pol.lam a).pre_hom h' hg y
  · intro T' T h' g' g'' hg y
    exact d.dualAb.pre_zero h' hg
  · intro T g y
    rw [RelPoint.baseChangeMap_zero hp hpd d.dualAb]
    exact h y

/-- **Base change of a polarization along a faithfully flat quasi-compact
`q`** — `baseChangeOfIsPullback` with `hinj` discharged by fppf descent.

Only `hsurj` remains, and it remains BY NECESSITY rather than by omission:
`Hom^sym_R(A, A^∨)` grows under fppf base change, so no flatness hypothesis can
supply it. The witness is `A = Res_{K/ℚ} E` over `Spec ℚ` with `R = 𝒪_K`, base
changed along the finite étale — hence flat, surjective and quasi-compact —
morphism `Spec K ⟶ Spec ℚ`: rank `1` becomes rank `2`. See the FALSITY AUDIT
in this section's docstring.

A caller must therefore still have a reason of its own for `hsurj` — a cocycle
condition verified by hand, or a moduli-theoretic reason why the base change
acquires no new symmetric homomorphisms. -/
noncomputable def baseChangeOfFppf (pol : PolarizationStruct d 𝒩 𝔞 𝔞pos)
    (hp : IsPullback p f' f q)
    {D' : Scheme.{u}} {dm' : D' ⟶ S'} {pd : D' ⟶ d.dualScheme}
    (hpd : IsPullback pd dm' d.dualMap q) [Flat q] [Surjective q] [QuasiCompact q]
    (hsurj : ∀ s : SymHomStruct (d.baseChangeOfIsPullback hp hpd), ∃ a : ↥𝔞,
        ∀ {T : Scheme.{u}} {g : T ⟶ S'} (y : RelPoint f' g),
          ((pol.lam a).baseChangeOfIsPullback hp hpd).hom y = s.hom y) :
    PolarizationStruct (d.baseChangeOfIsPullback hp hpd) 𝒩 𝔞 𝔞pos :=
  pol.baseChangeOfIsPullback hp hpd
    (fun a h => pol.lam_injective_baseChange hp hpd a (fun y => h y)) hsurj

end PolarizationStruct

end BaseChange

end Fermat

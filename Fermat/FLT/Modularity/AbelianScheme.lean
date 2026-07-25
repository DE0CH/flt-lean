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
  value carries the proof that the `I`-torsion is Galois-stable.

This is not decoration: a declaration in this project must lie in the
transitive used-constant cone of the root theorem, and only the
definitions reachable from `IsTwistedHilbertBlumenthalModuli` in
`Modularity/KhareWintenberger.lean` are. Bundling puts the proofs where
the cone can see them, and simultaneously makes the moduli statement
speak about a genuine `Γ_F`-module and a genuine `𝒪_D`-submodule rather
than about a hand-rolled list of equations.

Everything in this module is PROVEN; it contains no `sorry`.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Module.Torsion.Basic

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

end Fermat

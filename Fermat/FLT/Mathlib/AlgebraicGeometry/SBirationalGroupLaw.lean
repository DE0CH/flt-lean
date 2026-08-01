/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# `S`-dense open subschemes and `S`-birational group laws

This file is the DEFINITIONAL LAYER that the middle leaf of the Néron-model
decomposition in `Fermat/FLT/ModularCurve/X0.lean` is stated over —
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §2.5 (`S`-rational maps) and §5.1
(birational group laws).  Nothing in this file is specific to Néron models, to
modular curves or to a base of arithmetic origin: everything is stated for an
arbitrary morphism of schemes `f : X ⟶ S`.

## Why a RELATIVE notion, and why mathlib's `PartialMap` is not it

Mathlib has `AlgebraicGeometry.Scheme.PartialMap` and
`AlgebraicGeometry.Scheme.RationalMap` (`X ⤏ Y`), built on ABSOLUTE density
(`Dense (U : Set X)`).  BLR open §2.5 by explaining why that notion is unusable
over a base:

> when working over a base scheme `S`, this notion does not behave well with
> respect to a base change `S' → S`.

Their replacement is `S`-density — density in every FIBRE — which is stable
under base change by construction.  So `IsSDense` below is not a variant of
mathlib's `Dense` for convenience; it is a different (strictly stronger)
condition, and the whole of BLR Chapters 4–6 is stated in terms of it.

## The topological reading of `IsSDense`, and why it is BLR's condition

BLR: *an open subscheme `U` of a smooth `S`-scheme `X` is called `S`-dense if,
for each `s ∈ S`, the fibre `U_s = U ×_S Spec k(s)` is Zariski-dense in the
fibre `X_s`.*

`IsSDense f A` is written here as a condition on the UNDERLYING TOPOLOGY:
every point of the set-theoretic fibre `f.base ⁻¹' {s}` lies in the closure of
`A ∩ f.base ⁻¹' {s}`.  Two remarks make this exactly BLR's condition and not a
weakening of it:

* the closure taken in `X` and intersected back with the fibre IS the closure
  taken in the fibre's subspace topology, so the displayed inclusion says
  precisely that `A ∩ f⁻¹(s)` is dense in `f⁻¹(s)`;
* the canonical morphism `X ×_S Spec κ(s) ⟶ X` is a homeomorphism onto
  `f.base ⁻¹' {s}`, so density in the scheme-theoretic fibre and density in the
  set-theoretic fibre are the same statement.

Working topologically is what keeps this file free of fibre products over
residue fields; the price is that the reader has to be told the second remark,
which is why it is written down here.

The definition is stated for an arbitrary SET rather than for an `X.Opens`.
That is a harmless generalisation — BLR only ever use it for opens, and so does
every consumer here — and it is what lets the range of an open immersion be
asserted `S`-dense without carrying an `IsOpenImmersion` instance inside the
type of a structure field.

## Main definitions

* `AlgebraicGeometry.IsSDense` — BLR §2.5's `S`-density.
* `AlgebraicGeometry.sqStr` — the structure morphism of `X ×_S X`.
* `AlgebraicGeometry.leftTransl`, `AlgebraicGeometry.rightTransl` — the
  universal translations `(x, y) ↦ (x, xy)` and `(x, y) ↦ (xy, y)` of BLR
  5.1/1(a), as honest morphisms defined on the domain of the law.
* `AlgebraicGeometry.SBirationalGroupLaw` — BLR 5.1/1.

## There is no `IsSDense` CALCULUS here, and that is the free-floating rule

`S`-density is monotone, stable under finite intersection, and transitive (an
`S`-dense subset of an `S`-dense OPEN is `S`-dense) — the first is two lines and
the other two are BLR §2.5's opening remarks.  None of the three is stated,
because none of them has a consumer yet: this project forbids declarations
outside the used-constant cone of the root theorem, and a helper lemma with no
call site is exactly that.  They are named here so that whoever first needs one
knows it is a two-line proof rather than a gap.  The transitivity statement is
the one the shrinking argument below appeals to informally.

## What is deliberately NOT built here

There is no `S`-rational map, no equivalence class of partial maps and no
domain of definition.  A group law needs exactly ONE partial morphism, and
carrying it as the pair (`domain`, `mul`) rather than as a class is what makes
every clause below a statement about honest morphisms.  The one place where the
class structure is genuinely needed is Weil's extension theorem (BLR 4.4/1,
*an `S`-rational map from a smooth `S`-scheme to a smooth separated `S`-group
scheme over a normal noetherian base, defined in codimension `≤ 1`, is defined
everywhere*), which is consumed only INSIDE the two leaves in `X0.lean` and
never appears in any statement.  Building the class layer is the natural next
cut and is recorded as such on those leaves.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **`A` is `S`-DENSE in `f : X ⟶ S`** — BLR §2.5: `A` meets every fibre of `f`
in a dense subset of that fibre.

The closure is taken in `X`; since the points quantified over lie in the fibre,
that is the same as the closure in the fibre's subspace topology.  See the
module docstring for why this is BLR's condition on the nose and not a
weakening of it. -/
def IsSDense {X S : Scheme.{u}} (f : X ⟶ S) (A : Set X) : Prop :=
  ∀ s : S, f.base ⁻¹' {s} ⊆ closure (A ∩ f.base ⁻¹' {s})

/-- **The structure morphism of `X ×_S X`.**  Written through the FIRST
projection; `sqStr_snd` records that the second projection gives the same
morphism, which is the pullback condition. -/
noncomputable def sqStr {X S : Scheme.{u}} (f : X ⟶ S) : Limits.pullback f f ⟶ S :=
  Limits.pullback.fst f f ≫ f

theorem sqStr_snd {X S : Scheme.{u}} (f : X ⟶ S) :
    Limits.pullback.snd f f ≫ f = sqStr f := Limits.pullback.condition.symm

/-- **The universal LEFT translation `(x, y) ↦ (x, m x y)`** of BLR 5.1/1(a),
as a morphism defined on the domain of `m`. -/
noncomputable def leftTransl {X S : Scheme.{u}} (f : X ⟶ S)
    (U : (Limits.pullback f f).Opens) (m : (U : Scheme.{u}) ⟶ X)
    (hm : m ≫ f = U.ι ≫ sqStr f) : (U : Scheme.{u}) ⟶ Limits.pullback f f :=
  Limits.pullback.lift (U.ι ≫ Limits.pullback.fst f f) m
    (by rw [Category.assoc, ← sqStr, hm])

/-- **The universal RIGHT translation `(x, y) ↦ (m x y, y)`** of BLR 5.1/1(a),
as a morphism defined on the domain of `m`. -/
noncomputable def rightTransl {X S : Scheme.{u}} (f : X ⟶ S)
    (U : (Limits.pullback f f).Opens) (m : (U : Scheme.{u}) ⟶ X)
    (hm : m ≫ f = U.ι ≫ sqStr f) : (U : Scheme.{u}) ⟶ Limits.pullback f f :=
  Limits.pullback.lift m (U.ι ≫ Limits.pullback.snd f f)
    (by rw [Category.assoc, sqStr_snd, hm])

/-- **AN `S`-BIRATIONAL GROUP LAW on `f : X ⟶ S`** — Bosch–Lütkebohmert–Raynaud,
*Néron Models*, 5.1/1.

The data is a partial multiplication: an `S`-dense open `domain ⊆ X ×_S X` and
an `S`-morphism `mul : domain ⟶ X`.  The three conditions are BLR's: the two
universal translations are open immersions with `S`-dense image, and `mul` is
associative wherever both associates are defined.

## THIS IS BLR 5.1/1 UP TO THE CHOICE OF REPRESENTATIVE, AND THAT IS DELIBERATE

BLR ask that `Φ` and `Ψ` be `S`-BIRATIONAL, i.e. that each be represented by
SOME `S`-morphism from SOME `S`-dense open which is an isomorphism onto an
`S`-dense open of `X ×_S X`.  The fields below ask instead that `Φ` and `Ψ` be
open immersions with `S`-dense range ON `domain` ITSELF.  The two are
interchangeable, and the translation between them is one paragraph:

* *this ⟹ BLR*: immediate, `domain` is itself an `S`-dense open;
* *BLR ⟹ this*: BLR's own remark immediately after Definition 1 says it is
  enough for `Φ` and `Ψ` to be open immersions on an `S`-dense open `V` of
  `X ×_S X`.  Take `V` to be the intersection of the two such opens — finite
  intersections of `S`-dense opens are `S`-dense (BLR §2.5) — and replace
  `(domain, mul)` by `(V, mul|_V)`.  The ranges stay `S`-dense because an
  `S`-dense open of an `S`-dense open is `S`-dense (fibrewise: a dense subset
  of a dense OPEN is dense), and `mul_assoc` survives because it is a statement
  about test points that land in the domain, so shrinking the domain only
  removes test points.

Carrying the shrunk representative is what removes an existential from every
one of the five clauses below, and neither consumer can tell the difference:
the leaf that PRODUCES a law may always shrink, and the leaf that CONSUMES one
only ever needs BLR's form.

## `mul_assoc` IS BLR's "(xy)z = x(yz) WHENEVER BOTH SIDES ARE DEFINED"

Stated on test schemes rather than on a triple fibre product.  Read
`a = (x, y)`, `b = (y, z)`, `c = (xy, z)`, `d = (x, yz)`: the five hypotheses
say that `a` and `b` overlap in `y`, that `c` really is `(xy, z)` and that `d`
really is `(x, yz)`, and the conclusion is that the two triple products agree.
A test point of `domain` is exactly a pair of points of `X` over a common base
point which lands in `domain`, so this quantifies over precisely the situations
in which both sides are defined — and it does so without constructing
`X ×_S X ×_S X` or naming an `S`-dense open of it. -/
structure SBirationalGroupLaw {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- the `S`-dense open of `X ×_S X` on which the law is defined -/
  domain : (Limits.pullback f f).Opens
  /-- BLR §2.5: the domain is `S`-dense -/
  isSDense_domain : IsSDense (sqStr f) (domain : Set _)
  /-- the partial multiplication -/
  mul : (domain : Scheme.{u}) ⟶ X
  /-- the multiplication is a morphism over `S` -/
  mul_over : mul ≫ f = domain.ι ≫ sqStr f
  /-- BLR 5.1/1(a) for `Φ : (x, y) ↦ (x, xy)` -/
  left_isOpenImmersion : IsOpenImmersion (leftTransl f domain mul mul_over)
  /-- BLR 5.1/1(a): the image of `Φ` is `S`-dense -/
  left_isSDense : IsSDense (sqStr f) (Set.range (leftTransl f domain mul mul_over).base)
  /-- BLR 5.1/1(a) for `Ψ : (x, y) ↦ (xy, y)` -/
  right_isOpenImmersion : IsOpenImmersion (rightTransl f domain mul mul_over)
  /-- BLR 5.1/1(a): the image of `Ψ` is `S`-dense -/
  right_isSDense : IsSDense (sqStr f) (Set.range (rightTransl f domain mul mul_over).base)
  /-- BLR 5.1/1(b): associativity, wherever both sides are defined -/
  mul_assoc : ∀ {T : Scheme.{u}} (a b c d : T ⟶ (domain : Scheme.{u})),
    a ≫ domain.ι ≫ Limits.pullback.snd f f = b ≫ domain.ι ≫ Limits.pullback.fst f f →
    c ≫ domain.ι ≫ Limits.pullback.fst f f = a ≫ mul →
    c ≫ domain.ι ≫ Limits.pullback.snd f f = b ≫ domain.ι ≫ Limits.pullback.snd f f →
    d ≫ domain.ι ≫ Limits.pullback.fst f f = a ≫ domain.ι ≫ Limits.pullback.fst f f →
    d ≫ domain.ι ≫ Limits.pullback.snd f f = b ≫ mul →
    c ≫ mul = d ≫ mul

end AlgebraicGeometry

/-
ModularCurve/X0.lean — own work for the Fermat project (not vendored from
the FLT project).

# `Y_0(N)` as a coarse moduli space over `ℚ`

This module supplies the **missing modular-curve layer** behind Kenku's
half of the Mazur–Kenku isogeny classification, i.e. behind the twelve
level nodes of `FreyCurve/MazurTorsion.lean`
(`WeierstrassCurve.not_cyclicIsogeny_prod_two_primes`,
`…_twenty`, `…_twentyFour`, `…_twentyEight`, `…_thirty`, `…_thirtySix`,
`…_fortyTwo`, `…_fortyFive`, `…_fifty`, `…_fiftyFour`, `…_sixtyThree`,
`…_seventyFive`).

## Why this layer has to exist at all

Every one of those twelve statements is, mathematically, the assertion

> the modular curve `Y_0(N)` has no `ℚ`-rational point,

for a level `N` of genus `≥ 1` (`20, 24, 36` have genus `1`; `28, 50`
genus `2`; `30, 45` genus `3`; `54` genus `4`; `42, 63, 75` genus `5`;
and already `X_0(22)` has genus `2`).  A survey of the pin on 2026-07-26
found **no modular curves anywhere**: `grep ModularCurve` over the whole
of `.lake/packages/mathlib` returns nothing,
`Mathlib/NumberTheory/ModularForms/` contains modular *forms* rather than
curves or Jacobians, and `~/cs/FLT` takes the strictly weaker Mazur
torsion bound as a bare `axiom` (`FLT/Assumptions/Mazur.lean`).  So the
twelve statements could not even be *phrased* as what they are; they were
phrased instead as statements about a Galois-stable cyclic subgroup of an
elliptic curve over `ℚ`, which is the moduli *input*, not the modular
curve.

What this module does is exactly that rephrasing, and nothing more: it
writes down the `Γ₀(N)`-moduli problem and its coarse moduli space, and
restates the twelve levels as `Y_0(N)(ℚ) = ∅`.  The mathematical content
of the twelve nodes is untouched — it is *relocated* onto an object where
the Kenku/Ogg arguments (Mordell–Weil ranks of `J_0(N)`, Chabauty) can
one day be run.

## Design: Yoneda, following `Modularity/AbelianScheme.lean`

The elliptic scheme is `Fermat.AbelianSchemeStruct` from
`Modularity/AbelianScheme.lean` — a commutative group structure on the
functor of points, plus properness, smoothness and geometrically
connected fibres — together with `SmoothOfRelativeDimension 1`, which is
what cuts abelian schemes down to elliptic curves.  Presenting the group
law through the functor of points rather than as a morphism
`E ×_T E ⟶ E` means no chosen pullbacks and no monoidal structure on
`Over T` are needed, which is the only reason this is writable at this
pin at all.

Three consequences shape everything below.

* **The level structure is a closed subgroup scheme, not a subfunctor.**
  A `Γ₀(N)`-structure is a finite closed subscheme `C ⊆ E`, and
  membership of a relative point in it is *factoring through the closed
  immersion* (`RelPoint.LiesIn`).  Taking a bare subfunctor of the
  functor of points instead would be strictly weaker — an arbitrary
  subfunctor need not be representable, the moduli problem would then be
  larger than the true one, and its coarse space larger than `Y_0(N)`,
  which is precisely the way a level statement could silently become
  false.  Representability is bought here by carrying `C` as an actual
  scheme.

* **Base change is stated relationally, never constructed**
  (`IsBaseChangeOf`).  The moduli "functor" is only a functor up to
  isomorphism, so instead of forming pullbacks and transporting the
  group structure — expensive, and unnecessary — the naturality axiom
  quantifies over cartesian squares.  Note that this *also* delivers
  isomorphism-invariance for free: an isomorphic datum over the same base
  is a base change along the identity, so a natural transformation out of
  the moduli problem is automatically constant on isomorphism classes,
  which is what makes "initial among such" the coarse space of the
  moduli *stack* rather than of some rigidified variant.

* **`Y_0(N)`, not `X_0(N)`.**  The affine coarse space suffices, so no
  compactification, no cusps and no genus theory are needed here: the
  statement "`X_0(N)(ℚ)` consists only of cusps" is literally
  "`Y_0(N)(ℚ) = ∅`".  This is a deliberate scope cut — it removes an
  entire missing theory (the smooth compactification of a coarse moduli
  space, and the rationality of its cusps) from the critical path without
  weakening any statement.

## FAITHFULNESS AUDIT

There are exactly three claim-shapes here, and each is true.  Shapes 1
and 3 are single sorry nodes; shape 2 is now a proven bridge over two
sorried inputs:

1. `exists_coarseModuliY0 N` — the `Γ₀(N)`-moduli problem over `ℚ` admits
   a coarse moduli space.  TRUE: this is the classical existence
   statement for `Y_0(N)` (Deligne–Rapoport, Katz–Mazur; or classically
   via the `j`-line and the modular polynomial).  It is now PROVEN from a
   split of the level: `exists_coarseModuliY0_of_pos` (`N ≥ 1`) carries
   the citation — Katz–Mazur Theorem 6.6.1 and (8.1.1) — and
   `exists_coarseModuliY0_zero` disposes of `N = 0`, which lies outside
   their theorem, from the elementary leaf
   `isEmpty_of_gamma0Datum_zero`.

   The audit at `exists_coarseModuliY0_of_pos` used to record one place
   where this module's level structure was *weaker* than Katz–Mazur's,
   and hence one place where the moduli problem here was strictly larger
   than `[Γ₀(N)]` and the citation did not literally apply.  **That is
   repaired as of 2026-07-26**: `CyclicSubgroupOfOrder` now carries a
   `flat` field, so the level structure is finite *locally free* in
   Katz–Mazur's sense (6.7.1) and the two moduli problems agree over
   `(Ell/ℚ)`.  See the docstring of `CyclicSubgroupOfOrder` for the
   `Spec ℚ[ε]` counterexample that the field excludes.

2. The bridge from the Weierstrass phrasing to the moduli problem.  This
   was one node, `nonempty_gamma0Datum_of_stable`; it is now PROVEN
   (2026-07-26) from the two independent missing theories it had folded
   together, which are the sorry nodes in its place:

   * `exists_ellipticScheme_of_weierstrass` — the projective Weierstrass
     model of `E` as an elliptic scheme over `Spec ℚ`, together with the
     `Γ_ℚ`-equivariant additive identification of its geometric fibre
     with `E(ℚ̄)`.  TRUE: the smooth plane cubic with the chord–tangent
     law.  The larger of the two.
   * `exists_cyclicSubgroupOfOrder_of_galoisStable` — a Galois-stable
     cyclic subgroup of the geometric points of *any* abelian scheme
     over `Spec ℚ` is cut out by a closed cyclic subgroup scheme.  TRUE:
     in characteristic `0` this is Galois descent for finite étale
     schemes, i.e. the reduced induced structure on a finite
     `Γ_ℚ`-stable set of closed points.

3. `Y0HasNoRationalPoint N` at the twelve levels.  TRUE: the levels `N`
   with `Y_0(N)(ℚ) ≠ ∅` are exactly `{1, …, 19, 21, 25, 27, 37, 43, 67,
   163}` (Mazur 1978, Kenku 1979–1982), and none of `20, 24, 28, 30, 36,
   42, 45, 50, 54, 63, 75` — nor any product of two distinct primes
   outside `{6, 10, 14, 15, 21}` — lies in that list.

**Why the interface must pin `Y` down, and does.** A weaker interface —
say, a smooth projective curve over `ℚ` with a bijection on `ℚ̄`-points
— would be satisfied by `ℙ¹` for a cheap reason, and then
`Y0HasNoRationalPoint 20` would be FALSE rather than open, which is worse
than leaving the node untouched.  What rules that out is the *universal
property*: `IsCoarseModuliY0` asks for initiality among all `ℚ`-schemes
receiving a natural transformation from the moduli problem, and an
initial object is unique up to unique isomorphism.  So any `Y` satisfying
this interface is `ℚ`-isomorphic to the genuine `Y_0(N)`, and (3) is a
statement about the genuine `Y_0(N)`.

## What is NOT here, and is the next decomposition

This module deliberately stops at the coarse moduli space.  It does not
build, and the twelve level nodes still need:

* `J_0(N)` and its Mordell–Weil group (`Y_0(N)(ℚ) = ∅` is proved by
  bounding `J_0(N)(ℚ)`);
* the Hecke algebra and the Eisenstein / winding quotient, which is what
  supplies the rank-`0` input;
* for the higher-genus levels, Chabauty–Coleman.

Those are three independent subtrees, none of which exists at this pin.
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
-- `AlgebraicGeometry.Flat`: the flatness half of "finite locally free", which
-- is what makes `CyclicSubgroupOfOrder` the Katz–Mazur moduli problem
-- `[Γ₀(N)]` rather than a strictly larger one.  See the `flat` field of
-- `CyclicSubgroupOfOrder` and the faithfulness audit of
-- `exists_coarseModuliY0_of_pos`.
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
-- The group law on `(E⁄K).Point` needs `DecidableEq K`, and the classical
-- instance for `AlgebraicClosure ℚ` — the one every torsion statement in
-- this development is phrased against — lives here.
public import Fermat.FLT.EllipticCurve.Torsion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
-- `emptyIsInitial`, `isInitialOfIsEmpty`: the empty scheme as the initial
-- object, which is the coarse moduli space of the (empty) `Γ₀(0)`-problem
-- in `exists_coarseModuliY0_zero`.
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped WeierstrassCurve.Affine

namespace Fermat

/-! ### Relative points and a closed subscheme -/

/-- **A relative point lies in a subscheme `ι : C ⟶ E`** when it factors
through `ι`.

For `ι` a closed immersion this is the functor-of-points description of
the closed subscheme `C ⊆ E`: it is a *subfunctor* of the functor of
points of `E` by construction (precomposition preserves factoring), so no
naturality axiom is needed for it anywhere below. -/
def RelPoint.LiesIn {E T C : Scheme.{u}} {f : E ⟶ T} (ι : C ⟶ E)
    {T' : Scheme.{u}} {g : T' ⟶ T} (x : RelPoint f g) : Prop :=
  ∃ y : T' ⟶ C, y ≫ ι = x.1

/-- **Transport of a relative point along a morphism lying over the
base.** If `map : E' ⟶ E` fits in a commuting square over `h : T' ⟶ T`
then a `T''`-point of `E'` over `g : T'' ⟶ T'` becomes a `T''`-point of
`E` over `g ≫ h`.

When the square is *cartesian* this map is the canonical identification
of the points of the base change with the points of `E` over the shifted
base point; it is used below only through cartesian squares, but nothing
in its definition needs that. -/
def RelPoint.along {E' T' E T : Scheme.{u}} {f' : E' ⟶ T'} {f : E ⟶ T}
    {h : T' ⟶ T} (map : E' ⟶ E) (hw : f' ≫ h = map ≫ f)
    {T'' : Scheme.{u}} {g : T'' ⟶ T'} (x : RelPoint f' g) :
    RelPoint f (g ≫ h) :=
  ⟨x.1 ≫ map, by rw [Category.assoc, ← hw, ← Category.assoc, x.2]⟩

/-! ### Cyclic subgroup schemes of order `N` -/

/-- **A cyclic subgroup scheme of order `N` of an abelian scheme.**

The data is a closed subscheme `ι : C ⟶ E`, **finite and flat** over the
base, whose relative points form a subgroup of the relative points of `E`
at every base point, and whose geometric fibres are cyclic of order
exactly `N`.

Four remarks on the axioms.

* Closedness and finiteness are what make this a subgroup *scheme*
  rather than a subfunctor; see the module docstring for why that
  distinction is load-bearing for faithfulness.
* **`flat` is not decoration; it is what makes this the Katz–Mazur
  moduli problem.**  Katz–Mazur **(6.7.1)** (p. 167) define a *cyclic
  group of order `N`* to be a "finite locally free commutative
  `S`-group-scheme, of rank `N`, and cyclic", and `IsFinite` together
  with `Flat` is exactly finite locally free (a finitely presented flat
  module is projective, and finite projective over a commutative ring is
  locally free).  Dropping flatness — as this structure did until
  2026-07-26 — makes the moduli problem STRICTLY LARGER than `[Γ₀(N)]`,
  so that the coarse-space existence theorem cited at
  `exists_coarseModuliY0_of_pos` does not apply to it.  The gap is real
  rather than notional, and here is the witness that was recorded when
  it was found:

  > Over `T = Spec ℚ[ε]` take `E = E₀ ×_ℚ ℚ[ε]` and a rational point `P`
  > of exact order `2` on `E₀`.  Then `C = Spec(ℚ[ε] × ℚ)` — the zero
  > section together with the *non-flat* thickening `ℚ[ε] ↠ ℚ` of the
  > `P`-component of `E[2]` — is closed in `E`, finite over `T`,
  > contains the zero section, and is closed under the group law
  > (`P + P = 0`), and its unique geometric fibre is `ℤ/2`.  Without
  > `flat` that is a `CyclicSubgroupOfOrder` of order `2` which is not a
  > Katz–Mazur `[Γ₀(2)]`-structure.  With `flat` it is excluded, because
  > `ℚ[ε] × ℚ` is not a flat `ℚ[ε]`-module.

  Note that the witness is *non-reduced over the base*, which is why the
  omission was invisible at every base this development actually
  evaluates the moduli problem at — and why it had to be repaired in the
  interface rather than worked around at a leaf.
* The subgroup conditions are stated at *every* base point `g : T' ⟶ T`,
  which is the functor-of-points way of saying that the group law of `E`
  restricts to `C`; no naturality is required because `LiesIn` is a
  subfunctor automatically.
* `geom_cyclic` is the level-structure condition proper.  Over an
  algebraically closed field the relative points at a geometric point are
  the geometric points of that fibre, and the condition says they meet
  `C` in a cyclic group of order `N`.  In residue characteristic `0` —
  the only case used here — this is equivalent to `C` being finite étale
  with cyclic geometric fibres, so nothing is lost by phrasing it
  pointwise.

**Why `geom_cyclic` and not a `rank = N` field.**  Katz–Mazur pin the
*rank* of the finite locally free group scheme; this structure pins the
*cardinality of the geometric fibres*.  Over a base in which `N` is
invertible — in particular over any `ℚ`-scheme, which is the only case
the modular-curve layer evaluates — a finite flat group scheme is étale
(Cartier's theorem; Waterhouse, *Introduction to Affine Group Schemes*,
Thm. 11.4, or Tate, *Finite flat group schemes*, §3.7 in
Cornell–Silverman–Stevens), so its rank equals the number of points of
any geometric fibre and the two conditions agree.  Carrying the fibre
condition rather than the rank keeps the level structure statable
without `Scheme.Hom.finrank`, and is the form the descent leaf
`exists_cyclicSubgroupOfOrder_of_galoisStable` naturally produces. -/
structure CyclicSubgroupOfOrder {E T : Scheme.{u}} {f : E ⟶ T}
    (ab : AbelianSchemeStruct f) (N : ℕ) where
  /-- the underlying scheme of the subgroup -/
  C : Scheme.{u}
  /-- the inclusion into the ambient abelian scheme -/
  ι : C ⟶ E
  /-- the inclusion is a closed immersion -/
  isClosedImmersion : IsClosedImmersion ι
  /-- the subgroup scheme is finite over the base -/
  isFinite : IsFinite (ι ≫ f)
  /-- the subgroup scheme is flat over the base; together with `isFinite`
  this is Katz–Mazur's "finite locally free" -/
  flat : AlgebraicGeometry.Flat (ι ≫ f)
  /-- the zero section lies in `C` -/
  zero_liesIn : ∀ {T' : Scheme.{u}} (g : T' ⟶ T),
    RelPoint.LiesIn ι (ab.zero g)
  /-- `C` is closed under the group law -/
  add_liesIn : ∀ {T' : Scheme.{u}} {g : T' ⟶ T} {x y : RelPoint f g},
    RelPoint.LiesIn ι x → RelPoint.LiesIn ι y → RelPoint.LiesIn ι (ab.add x y)
  /-- `C` is closed under inversion -/
  neg_liesIn : ∀ {T' : Scheme.{u}} {g : T' ⟶ T} {x : RelPoint f g},
    RelPoint.LiesIn ι x → RelPoint.LiesIn ι (ab.neg x)
  /-- every geometric fibre of `C` is cyclic of order exactly `N` -/
  geom_cyclic : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (t : Spec (CommRingCat.of K) ⟶ T),
      letI := ab.addCommGroup t
      ∃ y : RelPoint f t, RelPoint.LiesIn ι y ∧ addOrderOf y = N ∧
        ∀ x : RelPoint f t, RelPoint.LiesIn ι x ↔ x ∈ AddSubgroup.zmultiples y

/-! ### The `Γ₀(N)`-moduli problem -/

/-- **A `Γ₀(N)`-structure over a scheme `T`**: an elliptic scheme over
`T` together with a cyclic subgroup scheme of order `N`.

"Elliptic scheme" is spelled out as *abelian scheme of relative dimension
one*: `AbelianSchemeStruct f` already carries properness, smoothness,
geometrically connected fibres, a zero section and a commutative group
law on the functor of points, and `SmoothOfRelativeDimension 1 f` is what
makes the fibres curves rather than abelian varieties of arbitrary
dimension.

This is the moduli problem `[Γ₀(N)]` of Katz–Mazur; its coarse space over
`ℚ` is `Y_0(N)`. -/
structure Gamma0Datum (N : ℕ) (T : Scheme.{u}) where
  /-- the total space of the elliptic scheme -/
  E : Scheme.{u}
  /-- the structure morphism of the elliptic scheme -/
  f : E ⟶ T
  /-- the abelian-scheme structure on `f` -/
  ab : AbelianSchemeStruct f
  /-- relative dimension one: the fibres are curves -/
  relativeDimensionOne : SmoothOfRelativeDimension 1 f
  /-- the `Γ₀(N)`-level structure -/
  cyc : CyclicSubgroupOfOrder ab N

/-- **`d'` is a base change of `d` along `h : T' ⟶ T`.**

Rather than construct pullbacks and transport structure along them, the
base-change relation is *stated*: a morphism `map` on total spaces making
a cartesian square, compatible with the group law and with the level
structure.  `RelPoint.along map isPullback.w` is the induced map on
relative points, and cartesianness is what makes it a bijection onto the
points over the shifted base point — a fact this development never needs
and therefore never proves.

Taking `h = 𝟙` recovers *isomorphism* of `Γ₀(N)`-data over a fixed base,
which is why a natural transformation out of the moduli problem (in the
sense of `IsCoarseModuliY0.classify_natural` below) is automatically
constant on isomorphism classes. -/
structure IsBaseChangeOf {N : ℕ} {T' T : Scheme.{u}} (h : T' ⟶ T)
    (d' : Gamma0Datum N T') (d : Gamma0Datum N T) where
  /-- the morphism on total spaces -/
  map : d'.E ⟶ d.E
  /-- the square over `h` is cartesian -/
  isPullback : IsPullback d'.f map h d.f
  /-- the zero section is preserved -/
  map_zero : ∀ {T'' : Scheme.{u}} (g : T'' ⟶ T'),
    RelPoint.along map isPullback.w (d'.ab.zero g) = d.ab.zero (g ≫ h)
  /-- the group law is preserved -/
  map_add : ∀ {T'' : Scheme.{u}} {g : T'' ⟶ T'} (x y : RelPoint d'.f g),
    RelPoint.along map isPullback.w (d'.ab.add x y)
      = d.ab.add (RelPoint.along map isPullback.w x)
          (RelPoint.along map isPullback.w y)
  /-- the level structure is the pullback of the level structure -/
  liesIn_iff : ∀ {T'' : Scheme.{u}} {g : T'' ⟶ T'} (x : RelPoint d'.f g),
    RelPoint.LiesIn d'.cyc.ι x
      ↔ RelPoint.LiesIn d.cyc.ι (RelPoint.along map isPullback.w x)

/-! ### The coarse moduli space -/

/-- **`str : Y ⟶ S` is a coarse moduli space for the `Γ₀(N)`-moduli
problem.**

The data is a classifying map sending a `Γ₀(N)`-structure over an
`S`-scheme `T` to a `T`-point of `Y`, natural in cartesian squares, which
is *initial* among all such.  This is Mumford's definition of a
categorical quotient / coarse moduli space, with the bijectivity on
geometric points — the second half of the usual definition — deliberately
omitted: initiality already determines `(Y, classify)` up to unique
isomorphism, which is all that faithfulness of the level statements
requires, and stating the geometric bijection would additionally require
a theory of isomorphisms of `Γ₀(N)`-data that nothing here consumes.

Over `S = Spec ℚ` the unique such `Y` is the modular curve `Y_0(N)`. -/
structure IsCoarseModuliY0 (N : ℕ) {Y S : Scheme.{u}} (str : Y ⟶ S) where
  /-- the classifying map of the moduli problem -/
  classify : ∀ {T : Scheme.{u}} (g : T ⟶ S), Gamma0Datum N T → RelPoint str g
  /-- the classifying map is natural: a base change of data is sent to the
  precomposed point -/
  classify_natural : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S}
    {g' : T' ⟶ S} (hg : h ≫ g = g') {d' : Gamma0Datum N T'}
    {d : Gamma0Datum N T}, IsBaseChangeOf h d' d →
    classify g' d' = RelPoint.pre h hg (classify g d)
  /-- `(Y, classify)` is initial among `S`-schemes receiving a natural
  transformation from the moduli problem -/
  universal : ∀ {Y' : Scheme.{u}} (str' : Y' ⟶ S)
    (c : ∀ {T : Scheme.{u}} (g : T ⟶ S), Gamma0Datum N T → RelPoint str' g),
    (∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
      (hg : h ≫ g = g') {d' : Gamma0Datum N T'} {d : Gamma0Datum N T},
      IsBaseChangeOf h d' d → c g' d' = RelPoint.pre h hg (c g d)) →
    ∃! u : Y ⟶ Y', u ≫ str' = str ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (d : Gamma0Datum N T),
        (c g d).1 = (classify g d).1 ≫ u

/-- **`Spec ℚ`**, the base of every modular curve considered here. -/
noncomputable abbrev SpecQ : Scheme.{0} := Spec (CommRingCat.of ℚ)

/-- **`Y_0(N)` has no rational point.**

Stated over every coarse moduli space of the `Γ₀(N)`-problem rather than
over a chosen one, so that no choice has to be made before
`exists_coarseModuliY0` is available; by initiality all of them are
canonically `ℚ`-isomorphic, so this is a statement about the genuine
`Y_0(N)`.

`RelPoint str (𝟙 SpecQ)` is by definition the set of sections of
`str : Y ⟶ Spec ℚ`, i.e. `Y(ℚ)`. -/
def Y0HasNoRationalPoint (N : ℕ) : Prop :=
  ∀ (Y : Scheme.{0}) (str : Y ⟶ SpecQ),
    IsCoarseModuliY0 N str → IsEmpty (RelPoint str (𝟙 SpecQ))

/-! ### The existence of `Y_0(N)`, and the bridge from Weierstrass curves -/

/-- **The `Γ₀(0)`-moduli problem is supported on the empty scheme** (sorry
leaf).

TRUE, and *elementary* — no modular-curve theory enters.  Suppose
`d : Gamma0Datum 0 T` and `T` had a point `x`.  Embedding the residue field
`κ(x)` into an algebraic closure `K` gives a geometric point
`t : Spec K ⟶ T`, and `d.cyc.geom_cyclic K t` then supplies a relative point
`y` with `addOrderOf y = 0` — that is, of *infinite* order — such that the
points of `d.cyc.C` above `t` are exactly `AddSubgroup.zmultiples y`.  But
`d.cyc.isFinite` makes `d.cyc.ι ≫ d.f` a finite morphism, so the fibre of
`d.cyc.C` over `t` is `Spec` of a finite-dimensional `K`-algebra and has only
finitely many `K`-points, whereas `AddSubgroup.zmultiples y ≃ ℤ` is infinite.
Contradiction, so `T` has no point at all.

WHY THIS IS A SEPARATE LEAF.  `[Γ₀(N)]` is a moduli problem only for
`N ≥ 1`, so `N = 0` is *outside* the Katz–Mazur theorem cited at
`exists_coarseModuliY0_of_pos` below.  Splitting it off is what makes that
citation honest: the cited theorem really does prove the `N ≥ 1` half, and
this degenerate half — the only part of `exists_coarseModuliY0` reachable at
this pin — is separated out rather than silently folded into the citation.

REACHABLE.  Formalising the argument needs exactly three things, all
present: stability of `IsFinite` under base change
(`AlgebraicGeometry.IsFinite` is an `IsStableUnderBaseChange` morphism
property), affineness of a scheme finite over a field, and the finiteness of
the set of `K`-algebra maps out of an Artinian `K`-algebra. -/
theorem isEmpty_of_gamma0Datum_zero {T : Scheme.{0}} (d : Gamma0Datum 0 T) :
    IsEmpty T :=
  sorry

/-- **Existence of the coarse moduli space, degenerate level `N = 0`**
(PROVEN, from `isEmpty_of_gamma0Datum_zero`).

VACUITY AUDIT — read this before consuming it.  By
`isEmpty_of_gamma0Datum_zero` the `Γ₀(0)`-problem has no object over any
nonempty base, so the empty scheme `∅ ⟶ Spec ℚ` is a coarse moduli space
for it, for the cheapest possible reason: every base carrying a datum is
*initial*, so all three clauses of `IsCoarseModuliY0` are equalities of
morphisms out of an initial object.  This carries **no** arithmetic
whatsoever, and in particular `Y0HasNoRationalPoint 0` is NOT thereby a
statement about a modular curve.  It is recorded only so that
`exists_coarseModuliY0` can be stated for every `N` while the citation
below is restricted, correctly, to `N ≥ 1`. -/
theorem exists_coarseModuliY0_zero :
    ∃ (Y : Scheme.{0}) (str : Y ⟶ SpecQ), Nonempty (IsCoarseModuliY0 0 str) := by
  classical
  refine ⟨(∅ : Scheme.{0}), emptyIsInitial.to SpecQ, ⟨?_⟩⟩
  -- Every base carrying a `Γ₀(0)`-datum is an initial scheme.
  have hinit : ∀ {T : Scheme.{0}}, Gamma0Datum 0 T → Limits.IsInitial T := by
    intro T d
    have : IsEmpty T := isEmpty_of_gamma0Datum_zero d
    exact isInitialOfIsEmpty
  exact
    { classify := fun {_T} _g d => ⟨(hinit d).to _, (hinit d).hom_ext _ _⟩
      classify_natural := fun {_T' _T} _h {_g _g'} _hg {d'} {_d} _hbc =>
        Subtype.ext ((hinit d').hom_ext _ _)
      universal := fun {Y'} _str' _c _hc =>
        ⟨emptyIsInitial.to Y',
          ⟨emptyIsInitial.hom_ext _ _, fun {_T} _g d => (hinit d).hom_ext _ _⟩,
          fun _u _hu => emptyIsInitial.hom_ext _ _⟩ }

/-- **Existence of the coarse moduli space `Y_0(N)` for `N ≥ 1`** (sorry
node — a CITATION, not a gap in the argument).

## What is cited

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics
Studies 108, Princeton, 1985:

* **Theorem 6.6.1** (p. 166): *the moduli problem `[Γ₀(N)]` is relatively
  representable over `(Ell)`; it is finite and flat over `(Ell)` of degree
  `(N²/φ(N))·∏_{p ∣ N}(1 − p⁻²)`, and is regular and two-dimensional.*
* **(8.1.1)** (p. 224), the construction of the coarse moduli scheme:
  *let `R` be a ring and `𝒫` a relatively representable moduli problem on
  `(Ell/R)` which is affine over `(Ell/R)`.*  Locally on `R` pick `n ≥ 3`
  invertible and a representable `𝒮` finite étale galois over `(Ell/R)`
  with group `G` — e.g. `𝒮 = [Γ(n)]`, `G = GL₂(ℤ/nℤ)` — and set
  `M(𝒫) = 𝔐(𝒫, 𝒮)/G`.  Katz–Mazur note that this "exists because
  `𝔐(𝒫, 𝒮)` is itself affine", and is independent of the choice of `𝒮`,
  so the local constructions patch.
* **(8.1.3)** (pp. 224–225): the canonical `G`-equivariant *classifying map*
  `S → M(𝒫)` attached to `E/S` with a level `𝒫`-structure, again
  independent of the auxiliary `n`.  This is `classify`, and its
  construction by descent along `S_n → S` is what makes it natural in `S`,
  i.e. `classify_natural`.
* **Lemma 8.1.3.1** (p. 225): for `k` algebraically closed, `M(𝒫)(k)` is
  the set of `k`-isomorphism classes of elliptic curves with `𝒫`-structure.

The **initiality** clause is not part of Katz–Mazur's *definition* — they
define `M(𝒫)` by the quotient construction rather than by a universal
property — but it follows from it: `𝔐(𝒫, [Γ(n)])` is affine, so the
quotient of (8.1.1) is `Spec` of the ring of invariants, and that is a
categorical quotient in the category of all schemes (Katz–Mazur Chapter 7,
*Quotients by finite groups*, and its Appendix *Base change for rings of
invariants*; Mumford, *Geometric Invariant Theory*, Ch. 0 §2).  Initiality
of `(Y, classify)` in `IsCoarseModuliY0` is exactly that categorical-quotient
property transported along (8.1.3).

Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*, in
*Modular Functions of One Variable II*, Lecture Notes in Math. 349 (1973),
143–316, is the companion reference and treats the same problem over
`ℤ[1/N]` (no theorem number is quoted here because it was not checked
against the text).

## Why the hypotheses match

* *Base ring.*  `R = ℚ`.  (8.1.1) needs some `n ≥ 3` invertible in `R` only
  locally; over a field of characteristic `0` every `n` is invertible, so
  the construction is global and no patching is needed.  `SpecQ` is
  `Spec ℚ`, so `Y ⟶ SpecQ` is exactly an `R`-scheme.
* *The moduli problem.*  `Gamma0Datum N T` is `[Γ₀(N)]` on `(Ell/ℚ)`:
  `ab` together with `relativeDimensionOne` is an elliptic curve `E/T`, and
  `cyc` is the cyclic subgroup of order `N`.  Theorem 6.6.1 supplies both
  hypotheses (8.1.1) asks for — relative representability, and finiteness
  over `(Ell)`, which gives affineness over `(Ell)`.
* *`N ≥ 1`.*  `[Γ₀(N)]` is defined only for `N ≥ 1`; the level `N = 0` is
  handled separately and degenerately by `exists_coarseModuliY0_zero`.

## FAITHFULNESS AUDIT: the one mismatch, and its REPAIR (2026-07-26)

Katz–Mazur **(6.7.1)** (p. 167) define a *cyclic group of order `N`* to be
a "finite locally free commutative `S`-group-scheme, of rank `N`, and
cyclic".

Until 2026-07-26 `CyclicSubgroupOfOrder` asked only for a closed subgroup
scheme **finite** over the base with **geometric fibres** cyclic of order
`N` — it did **not** ask for flatness.  That made the moduli problem here
strictly *larger* than `[Γ₀(N)]`, so the theorem cited above did not
literally apply to it, and the gap was real rather than notional: over
`T = Spec ℚ[ε]` the non-flat thickening `C = Spec(ℚ[ε] × ℚ)` of a
`2`-torsion component satisfied every axiom and is not a KM
`[Γ₀(2)]`-structure.  The counterexample is written out in full in the
docstring of `CyclicSubgroupOfOrder`, where it now serves as the
justification for the axiom rather than as an open defect.

**The repair was made in the interface**, which is where it belonged: the
field `CyclicSubgroupOfOrder.flat` requires `AlgebraicGeometry.Flat
(ι ≫ f)`, so the level structure is finite *and* flat over the base,
i.e. finite locally free.  A flatification retraction — the route a
successor would otherwise have had to supply — is no longer needed, and
the earlier plan to build one (`C ⊆ C^♭ ⊆ E[N]`, open and closed in the
`N`-torsion, formed compatibly with base change) is retired rather than
merely deferred.

**What remains, and why it is not a mismatch.**  KM pin the *rank*;
`geom_cyclic` pins the *number of points of each geometric fibre*.  Over
a `ℚ`-scheme — and every base at which `IsCoarseModuliY0 N (str : Y ⟶
SpecQ)` evaluates the problem is a `ℚ`-scheme, since a datum comes with
a structure map `g : T ⟶ SpecQ` — a finite flat group scheme is étale by
Cartier's theorem, so rank and geometric-fibre cardinality coincide, and
"cyclic" in KM's fppf-local sense coincides with cyclicity of the
geometric fibres.  So over `(Ell/ℚ)` the two moduli problems are the
same, and the citation applies to this one on the nose.

The step in that paragraph — Cartier's theorem — is a *statement about
the citation's hypotheses*, not a hidden lemma of the formalisation:
nothing below consumes it, and it is recorded so that a successor
closing this node knows precisely which classical fact reconciles the
two phrasings.

## Why it is IRREDUCIBLE at this pin

Surveyed 2026-07-26: `Mathlib` has no modular curve, no modular polynomial,
no moduli stack, no coarse-space existence theorem, no geometric invariant
theory and no quotient of a scheme by a finite group; `~/cs/FLT` takes the
weaker Mazur torsion bound as a bare `axiom`.  Every route to this
statement — Katz–Mazur (8.1.1) via `[Γ(n)]`-rigidification and quotients,
Deligne–Rapoport via stacks, or the classical construction of `Y_0(N)` as
the normalisation of `Φ_N(X, Y) = 0` in `𝔸¹ × 𝔸¹` with classifying map
`(E, C) ↦ (j(E), j(E/C))` — needs a theory that does not exist here. -/
theorem exists_coarseModuliY0_of_pos (N : ℕ) (hN : 0 < N) :
    ∃ (Y : Scheme.{0}) (str : Y ⟶ SpecQ), Nonempty (IsCoarseModuliY0 N str) :=
  sorry

/-! ### The two missing theories behind the bridge

`nonempty_gamma0Datum_of_stable` was originally left as a single sorry
node folding together two *independent* missing theories.  It is now
DERIVED (2026-07-26) from the two leaves of this subsection, which are
exactly those two theories, cut apart:

* `exists_ellipticScheme_of_weierstrass` — the geometry: the projective
  Weierstrass model of `E/ℚ` as an elliptic scheme over `Spec ℚ`;
* `exists_cyclicSubgroupOfOrder_of_galoisStable` — the arithmetic:
  Galois descent turning a Galois-stable finite subgroup of the geometric
  points into a closed subgroup scheme over `ℚ`.

The cut is at the *geometric fibre*: leaf (a) hands over an equivariant
additive identification of `E(ℚ̄)` with the geometric points of the
elliptic scheme, and leaf (b) consumes nothing about `E` at all — it is
stated for an arbitrary abelian scheme over `Spec ℚ`.  So neither leaf
mentions the other's subject matter, and the assembly below is pure
transport along that identification. -/

/-- **The projective Weierstrass model of `E/ℚ` as an elliptic scheme
over `Spec ℚ`** (sorry node — theory (a) of the bridge).

TRUE, and classical: a Weierstrass equation with invertible discriminant
over `ℚ` cuts out a smooth projective plane curve `A ⊆ ℙ²_ℚ` of relative
dimension `1` with a rational point at infinity, the chord–tangent law
makes its functor of points a commutative group functor, and properness,
smoothness and geometric connectedness of the fibre are the standard
facts about a smooth plane cubic.  The last conjunct says that the
resulting group of geometric points is `E(ℚ̄)` with its usual group law
and its usual Galois action — i.e. that the scheme really is *this*
curve and not merely some elliptic scheme.

**Why the equivariant identification is part of the statement, and not a
separate leaf.**  Without it the leaf would be satisfiable by any
elliptic curve over `ℚ` whatsoever, and the bridge below would then
manufacture a `Γ₀(N)`-datum out of the wrong curve — the level structure
transported from `E` would have nothing to attach to.  Pinning the
geometric fibre as a `Γ_ℚ`-module is exactly what rules that out, and it
is also precisely what the descent leaf needs as input, so the two fit
without an intermediate interface.

IRREDUCIBLE at this mathlib pin: `Mathlib` has `WeierstrassCurve`,
`IsElliptic`, `WeierstrassCurve.Projective` and the group law on
`(E⁄K).Point` for a field `K`, but the elliptic curve as a *group
scheme* — the functor of points of the projective model, with the group
law as a natural transformation — does not exist anywhere in
`Mathlib`, and `~/cs/FLT` has no abelian schemes either (surveyed
2026-07-26).  This is the larger of the two theories. -/
theorem exists_ellipticScheme_of_weierstrass (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ (A : Scheme.{0}) (f : A ⟶ SpecQ) (ab : AbelianSchemeStruct f),
      SmoothOfRelativeDimension 1 f ∧
        (letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
         ∃ e : (E⁄(AlgebraicClosure ℚ)).Point ≃+ GeomFibrePt f (𝟙 SpecQ),
           ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
             e (WeierstrassCurve.Affine.Point.map
                 (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
               = ab.galSMul (𝟙 SpecQ) σ (e x)) :=
  sorry

/-- **Galois descent: a Galois-stable cyclic subgroup of the geometric
points of an abelian scheme over `ℚ` is cut out by a closed cyclic
subgroup scheme** (sorry node — theory (b) of the bridge).

TRUE, and this is the whole content of Galois descent for finite étale
schemes in characteristic `0`.  The argument: `⟨y⟩ ⊆ A(ℚ̄)` is a finite
`Γ_ℚ`-stable set, so its image in the topological space of `A` is a
finite set of closed points, stable under `Γ_ℚ`; give it the *reduced*
induced closed subscheme structure `C`.  Reduced and finite type over a
field of characteristic `0` is finite étale, `C(ℚ̄) = ⟨y⟩` because each
`Γ_ℚ`-orbit contributes one closed point whose residue field is the
field of definition of that orbit, and `C` is a subgroup scheme because
`C ×_ℚ C` is again reduced, so the two morphisms
`C ×_ℚ C ⇉ A` given by `ι ∘ pr₁ + ι ∘ pr₂` and its factorisation agree
once they agree on geometric points, `A` being separated.

Note the hypothesis is stated on the **generator only**: `galSMul σ` is
additive (it is the scalar action of `geomFibreAction`), so stability of
`y` up to `zmultiples` already gives stability of the whole subgroup.
That is the weakest honest form, and it is what the bridge below can
supply from the elementary hypothesis of the twelve level nodes.

`geom_cyclic` in the conclusion quantifies over *every* algebraically
closed `K` and every `K`-point of the base, not only over `ℚ̄`.  That is
not an extra assumption smuggled in: `ℚ` is initial among rings, so such
a base point is unique, and the algebraic closure of `ℚ` inside `K` is a
copy of `ℚ̄`, over which `C` is already split — so `C(K)` is again
`⟨y⟩`, with the same order `N`.

**PIN SURVEY, 2026-07-26 — do not repeat it, and note it is more
favourable than "nothing exists".**  What is PRESENT:

* `CommAlgCat.FiniteEtale R` (`Mathlib/RingTheory/Etale/Finite.lean`,
  new): the category of finite étale `R`-algebras, with the fiber
  functor `FiniteEtale.fiber R Ω : S ↦ (S →ₐ[R] Ω)`, base change, and
  `FiniteEtale.equivOfIsSepClosed` — but the equivalence is proven ONLY
  over a separably closed base, which is the split case and carries no
  descent.
* `Mathlib/CategoryTheory/Galois/`: Galois categories in the abstract,
  including `EssSurj` and `Prorepresentability`.
* `AlgebraicGeometry.ext_of_isDominant_of_isSeparated`
  (`Morphisms/Separated.lean`): two morphisms out of a reduced scheme
  into a separated one agree as soon as they agree on a dominant
  subscheme.  This is exactly the rigidity step the subgroup axioms
  need, and it means `add_liesIn`/`neg_liesIn` at an ARBITRARY base
  `T'` should reduce to the geometric-point statement rather than
  needing a separate argument.
* `Scheme.IdealSheafData.subscheme` / `subschemeι`
  (`AlgebraicGeometry/IdealSheaf/Subscheme.lean`): closed subschemes cut
  out by an ideal sheaf, with the closed-immersion API.

What is ABSENT, and is the actual content of this leaf:

* no `PreGaloisCategory` instance anywhere except `Action FintypeCat G`,
  so `FiniteEtale k` is NOT known to be a Galois category and the
  correspondence with finite continuous `Γ_k`-sets — the descent
  direction, over a NON-closed base — does not exist;
* no construction of the reduced induced closed subscheme structure on a
  closed subset of a scheme (`grep` over `AlgebraicGeometry/` finds no
  `reducedSubscheme` of any spelling).

So the honest cut for a successor is: build the reduced induced
structure, or go through `CommAlgCat.FiniteEtale` on affines and glue.
The algebra-side scaffolding is fresher than the module docstring's
"no modular curves anywhere" survey would suggest.

**NOTE ON THE `flat` FIELD** (added to `CyclicSubgroupOfOrder`
2026-07-26, when the level structure was corrected to Katz–Mazur's
"finite locally free").  This leaf now owes a proof of
`AlgebraicGeometry.Flat (ι ≫ f)` as well, and that costs it **nothing**:
the base here is `SpecQ = Spec ℚ`, a field, over which every module is
flat.  So the extra field is discharged by flatness of `C` as a
`ℚ`-scheme, whichever construction of `C` a successor chooses, and no
part of the descent argument above has to change.  The strengthening of
the interface is paid for entirely by the *general-base* consumers, not
here. -/
theorem exists_cyclicSubgroupOfOrder_of_galoisStable {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y) :
    Nonempty (CyclicSubgroupOfOrder ab N) :=
  sorry

/-- **Existence of the coarse moduli space `Y_0(N)`** (PROVEN, as the split
of the level into the cited case `N ≥ 1` and the degenerate case `N = 0`).

See `exists_coarseModuliY0_of_pos` for the citation (Katz–Mazur Theorem
6.6.1 and (8.1.1)) and for the faithfulness audit, and
`exists_coarseModuliY0_zero` for the degenerate level. -/
theorem exists_coarseModuliY0 (N : ℕ) :
    ∃ (Y : Scheme.{0}) (str : Y ⟶ SpecQ), Nonempty (IsCoarseModuliY0 N str) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact exists_coarseModuliY0_zero
  · exact exists_coarseModuliY0_of_pos N hN

/-- **A Galois-stable cyclic subgroup of order `N` of `E(ℚ̄)` is a
`Γ₀(N)`-structure over `Spec ℚ`** (PROVEN 2026-07-26 from the two leaves
above; formerly itself a sorry node).

This is the bridge between the elementary phrasing used in
`FreyCurve/MazurTorsion.lean` — a Weierstrass curve over `ℚ` and a point
of order `N` over `ℚ̄` generating a Galois-stable subgroup — and the
moduli problem.  All of its mathematical content now sits in
`exists_ellipticScheme_of_weierstrass` (the elliptic curve as a group
scheme) and `exists_cyclicSubgroupOfOrder_of_galoisStable` (Galois
descent for the level structure); what is left here, and proven, is the
transport of the order and of the stability hypothesis along the
equivariant identification of `E(ℚ̄)` with the geometric fibre.

`hstable` is verbatim the stability hypothesis carried by the twelve
level nodes, so no reformulation happens at the boundary. -/
theorem nonempty_gamma0Datum_of_stable (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    Nonempty (Gamma0Datum N SpecQ) := by
  obtain ⟨A, f, ab, hdim, e, he⟩ := exists_ellipticScheme_of_weierstrass E
  -- The `AddCommGroup` structure on the geometric fibre.  This binding is
  -- load-bearing, not decoration: the `letI`s inside the two `have`
  -- statements below scope over those statements only, so without this the
  -- ambient `AddMonoid`/`AddMonoidHomClass` instances needed by their
  -- proofs (`AddEquiv.addOrderOf_eq`, `map_zsmul`) fail to synthesize.
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  -- The order of the generator transports along the additive equivalence.
  have hord : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
      addOrderOf (e g) = N := by
    rw [AddEquiv.addOrderOf_eq]
    exact hg
  -- So does its Galois stability: `galSMul σ (e g) = e (σ • g)`, and `σ • g`
  -- is an integer multiple of `g` by hypothesis, hence `galSMul σ (e g)` is
  -- the same integer multiple of `e g`.
  have hst : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        ab.galSMul (𝟙 SpecQ) σ (e g) ∈ AddSubgroup.zmultiples (e g) := by
    intro σ
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (hstable σ g (AddSubgroup.mem_zmultiples g))
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
    rw [← he σ g, ← hk, map_zsmul]
  obtain ⟨cyc⟩ := exists_cyclicSubgroupOfOrder_of_galoisStable ab N (e g) hord hst
  exact ⟨{ E := A, f := f, ab := ab, relativeDimensionOne := hdim, cyc := cyc }⟩

/-- **The consumption rule of this module.**

If `Y_0(N)` has no rational point but some elliptic curve over `ℚ` has a
Galois-stable cyclic subgroup of order `N`, then the classifying map
produces a rational point of `Y_0(N)` — a contradiction.  This is the one
place where the three sorried inputs above meet, and it is what the
twelve level nodes of `FreyCurve/MazurTorsion.lean` call. -/
theorem false_of_stable_of_y0HasNoRationalPoint {N : ℕ}
    (hY : Y0HasNoRationalPoint N) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False := by
  obtain ⟨Y, str, ⟨M⟩⟩ := exists_coarseModuliY0 N
  obtain ⟨d⟩ := nonempty_gamma0Datum_of_stable E g hg hstable
  exact (hY Y str M).elim (M.classify (𝟙 SpecQ) d)

/-! ### The twelve levels of Kenku's non-prime-power determination

Each statement below is the level `N` of the Mazur–Kenku classification,
restated as a claim about the rational points of the modular curve
`Y_0(N)`.  The levels `N` for which `Y_0(N)(ℚ) ≠ ∅` are exactly

`1, …, 19, 21, 25, 27, 37, 43, 67, 163`

(Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47
(1977); *Rational isogenies of prime degree*, Invent. Math. 44 (1978);
Kenku's series, Math. Proc. Cambridge Philos. Soc. 85 (1979) and 87
(1980), J. London Math. Soc. (2) 22 (1980) and 23 (1981), J. Number
Theory 15 (1982)), and none of the levels below is in that list.

All of them are IRREDUCIBLE at this mathlib pin for the same reason: each
is a determination of the rational points of a curve of genus `≥ 1`, and
neither `J_0(N)`, nor its Mordell–Weil group, nor Chabauty–Coleman exists
in this development.  See the module docstring for the three subtrees
that are needed. -/

/-- **`Y_0(pq)(ℚ) = ∅` for `pq` a product of two distinct primes outside
`{6, 10, 14, 15, 21}`** (sorry node — the uniform, squarefree part of
Kenku's determination).

Those five products are exactly the semiprimes in the Mazur–Kenku list.
The statement is uniform but its content is finite: by Mazur's prime
node both `p` and `q` lie in `{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67,
163}`, so `61` of the `66` unordered pairs need excluding — among them
`X_0(35)` and `X_0(39)` (Kenku 1979), `X_0(65)` and `X_0(91)` (Kenku
1980).  Already `X_0(22)` has genus `2`. -/
theorem y0HasNoRationalPoint_prod_two_primes {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q)
    (hmem : p * q ∉ ({6, 10, 14, 15, 21} : Finset ℕ)) :
    Y0HasNoRationalPoint (p * q) :=
  sorry

/-! #### Reconnaissance for the eleven named levels (2026-07-26)

The arithmetic data deciding the route for each of the eleven levels
below was computed with Magma and is recorded here so that no later
owner has to recompute it.  Two facts hold **uniformly** across all
eleven, and together they fix the shape of every proof:

* **`rank J_0(N)(ℚ) = 0` for all eleven.**  Decomposing the cuspidal
  subspace of `S_2(Γ_0(N))` into newform factors and evaluating
  `L(A, 1)` on each, *every* factor at *every* one of the eleven levels
  has `L(A, 1) ≠ 0`; so `J_0(N)` has analytic rank `0`, and hence
  Mordell–Weil rank `0` by Kolyvagin–Logachev.  **No level below needs
  Chabauty–Coleman.**  (This corrects the guess recorded in the `N = 28`
  docstring before this pass, which called it "a Jacobian/Chabauty
  computation".)
* Consequently `J_0(N)(ℚ)` is finite, reduction `J_0(N)(ℚ) → J_0(N)(𝔽_ℓ)`
  is injective for every odd prime `ℓ ∤ N` of good reduction, and — using
  a rational cusp as base point for Abel–Jacobi — `X_0(N)(ℚ)` injects
  into `X_0(N)(𝔽_ℓ)`.  So `#X_0(N)(ℚ) ≤ #X_0(N)(𝔽_ℓ)`.

The counts come from Eichler–Shimura,
`#X_0(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`.  Writing `c(N)` for the
number of **`ℚ`-rational** cusps — the divisors `d ∣ N` with
`φ(gcd(d, N/d)) = 1` — the table is:

| `N` | genus | cusps | `c(N)` | best `ℓ` | `#X_0(N)(𝔽_ℓ)` | route |
|-----|-------|-------|--------|----------|------------------|-------|
| 20  | 1 | 6  | 6 | 3  | 6 | closes |
| 24  | 1 | 8  | 8 | 5  | 8 | closes |
| 28  | 2 | 6  | 6 | 5  | 6 | closes |
| 30  | 3 | 8  | 8 | 17 | 8 | closes |
| 36  | 1 | 12 | 6 | 5  | 6 | closes |
| 42  | 5 | 8  | 8 | 11 | 8 | closes |
| 45  | 3 | 8  | 4 | 7  | 8 | sieve |
| 50  | 2 | 12 | 4 | 3  | 4 | closes |
| 54  | 4 | 12 | 4 | 5  | 6 | sieve |
| 63  | 5 | 8  | 4 | 5  | 8 | sieve |
| 75  | 5 | 12 | 4 | 7  | 8 | sieve |

**Seven levels — `20, 24, 28, 30, 36, 42, 50` — close on a single
prime**: at the `ℓ` listed, `#X_0(N)(𝔽_ℓ) = c(N)`, and the `c(N)`
rational cusps already realise that many rational points, so
`X_0(N)(ℚ)` consists exactly of the rational cusps and `Y_0(N)(ℚ) = ∅`.

**Four levels — `45, 54, 63, 75` — do not.**  For these the single-prime
bound is strictly weaker than `c(N)`: no prime `ℓ < 100` with `ℓ ∤ N`
attains `#X_0(N)(𝔽_ℓ) = c(N)`, the minima over `3 ≤ ℓ < 60` being `8`
at `ℓ = 7` (`N = 45`), `6` at `ℓ = 5` (`N = 54`), `8` at `ℓ = 5`
(`N = 63`) and `8` at `ℓ = 7` (`N = 75`), against `c(N) = 4` in each
case.  They need a **multi-prime Mordell–Weil sieve**: the image of
`X_0(N)(ℚ)` in the finite group `J_0(N)(ℚ)` must be simultaneously
compatible with `X_0(N)(𝔽_ℓ) → J_0(N)(𝔽_ℓ)` for several `ℓ` at once.
The `gcd` of `#J_0(N)(𝔽_ℓ)` over `3 ≤ ℓ < 60`, which bounds
`#J_0(N)(ℚ)`, is `512`, `243`, `6144` and `2560` respectively — so the
sieve has a genuinely finite search space, but one prime is not enough.

**All eleven remain IRREDUCIBLE here for the same reason**, and it is
not the arithmetic above: nothing in this development yet has `X_0(N)`
as a scheme, its cusps, `J_0(N)`, Mordell–Weil, or reduction mod `ℓ`.
The arithmetic is settled; the *interface* is what is missing.  See the
sibling node `y0HasNoRationalPoint_prod_two_primes`, which owns that
shared layer. -/

/-- **`Y_0(20)(ℚ) = ∅`** (sorry node; `X_0(20)` has genus `1`).  Ogg,
*Rational points on certain elliptic modular curves*, Proc. Sympos. Pure
Math. 24 (1973): `X_0(20)` is an elliptic curve of Mordell–Weil rank `0`
over `ℚ` whose six rational points are its six cusps.

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(20)(ℚ) = 0`,
all six cusps are rational, and `#X_0(20)(𝔽_3) = 6`; so the six cusps
exhaust `X_0(20)(ℚ)`.  (`ℓ = 7` also gives `6`.) -/
theorem y0HasNoRationalPoint_twenty : Y0HasNoRationalPoint 20 :=
  sorry

/-- **`Y_0(24)(ℚ) = ∅`** (sorry node; `X_0(24)` has genus `1`; Ogg
1973).

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(24)(ℚ) = 0`,
all eight cusps are rational, and `#X_0(24)(𝔽_5) = 8`; so the eight
cusps exhaust `X_0(24)(ℚ)`.  (`ℓ = 7` and `ℓ = 11` also give `8`.) -/
theorem y0HasNoRationalPoint_twentyFour : Y0HasNoRationalPoint 24 :=
  sorry

/-- **`Y_0(28)(ℚ) = ∅`** (sorry node; `X_0(28)` has genus `2`; Ogg,
*Hyperelliptic modular curves*, Bull. Soc. Math. France 102 (1974)).

ROUTE (rank-`0` reduction, closes on one prime).  **This level does NOT
need Chabauty–Coleman**, contrary to what this docstring asserted before
2026-07-26: `J_0(28)` has analytic rank `0` (its single newform factor
has `L(A, 1) ≠ 0`), hence Mordell–Weil rank `0`.  All six cusps are
rational and `#X_0(28)(𝔽_5) = 6`, so the six cusps exhaust
`X_0(28)(ℚ)`.  (`ℓ = 17` also gives `6`.) -/
theorem y0HasNoRationalPoint_twentyEight : Y0HasNoRationalPoint 28 :=
  sorry

/-- **`Y_0(30)(ℚ) = ∅`** (sorry node; `X_0(30)` has genus `3`).  This is
the minimal level with three distinct prime factors.

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(30)(ℚ) = 0`
(both newform factors have `L(A, 1) ≠ 0`), all eight cusps are rational,
and `#X_0(30)(𝔽_17) = 8`; so the eight cusps exhaust `X_0(30)(ℚ)`.
Note the small primes are *not* good enough here — `ℓ = 7, 11, 13` give
`12, 20, 16` — so `ℓ = 17` is the witness to use. -/
theorem y0HasNoRationalPoint_thirty : Y0HasNoRationalPoint 30 :=
  sorry

/-- **`Y_0(36)(ℚ) = ∅`** (sorry node; `X_0(36)` has genus `1`; Ogg
1973).

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(36)(ℚ) = 0`.
`X_0(36)` has `12` cusps but only `6` rational ones (the divisors
`d ∈ {1, 2, 4, 9, 18, 36}`; the pairs over `d = 3, 6, 12` are conjugate
over `ℚ(ζ_3)`), and `#X_0(36)(𝔽_5) = 6`; so the six rational cusps
exhaust `X_0(36)(ℚ)`. -/
theorem y0HasNoRationalPoint_thirtySix : Y0HasNoRationalPoint 36 :=
  sorry

/-- **`Y_0(42)(ℚ) = ∅`** (sorry node; `X_0(42)` has genus `5`).  The
second minimal level with three distinct prime factors.

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(42)(ℚ) = 0`
(all three newform factors have `L(A, 1) ≠ 0`), all eight cusps are
rational, and `#X_0(42)(𝔽_11) = 8`; so the eight cusps exhaust
`X_0(42)(ℚ)`.  Despite the genus being `5`, this is the cheapest kind of
argument — no Chabauty–Coleman is involved. -/
theorem y0HasNoRationalPoint_fortyTwo : Y0HasNoRationalPoint 42 :=
  sorry

/-- **`Y_0(45)(ℚ) = ∅`** (sorry node; `X_0(45)` has genus `3`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(45)(ℚ) = 0` (both newform factors have `L(A, 1) ≠ 0`), so
`X_0(45)(ℚ)` is finite and injects into `X_0(45)(𝔽_ℓ)` for every odd
`ℓ ∤ 45`.  But `X_0(45)` has `8` cusps of which only `4` are rational,
and **no** prime `ℓ < 100` attains `#X_0(45)(𝔽_ℓ) = 4`: the minimum over
`3 ≤ ℓ < 60` is `8`, at `ℓ = 7`.  So a single reduction leaves a factor
of `2` unaccounted for, and the four rational points must be pinned by
intersecting the images of `X_0(45)(𝔽_ℓ) → J_0(45)(𝔽_ℓ)` over several
`ℓ` simultaneously.  `#J_0(45)(ℚ)` divides `512`. -/
theorem y0HasNoRationalPoint_fortyFive : Y0HasNoRationalPoint 45 :=
  sorry

/-- **`Y_0(50)(ℚ) = ∅`** (sorry node; `X_0(50)` has genus `2`; Ogg
1974).

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(50)(ℚ) = 0`
(both newform factors have `L(A, 1) ≠ 0`).  `X_0(50)` has `12` cusps but
only `4` rational ones, and `#X_0(50)(𝔽_3) = 4`; so the four rational
cusps exhaust `X_0(50)(ℚ)`.  This is the tightest of the seven
single-prime levels — the count matches `c(N)` exactly at the smallest
available prime. -/
theorem y0HasNoRationalPoint_fifty : Y0HasNoRationalPoint 50 :=
  sorry

/-- **`Y_0(54)(ℚ) = ∅`** (sorry node; `X_0(54)` has genus `4`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(54)(ℚ) = 0` (all three newform factors have `L(A, 1) ≠ 0`).
`X_0(54)` has `12` cusps of which `4` are rational, and no prime
`ℓ < 100` attains `#X_0(54)(𝔽_ℓ) = 4`: the minimum over `3 ≤ ℓ < 60` is
`6`, at `ℓ = 5`.  This is the *closest* of the four sieve levels — the
single-prime bound overshoots by only `2` — so it is the natural one to
attempt first.  `#J_0(54)(ℚ)` divides `243`. -/
theorem y0HasNoRationalPoint_fiftyFour : Y0HasNoRationalPoint 54 :=
  sorry

/-- **`Y_0(63)(ℚ) = ∅`** (sorry node; `X_0(63)` has genus `5`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(63)(ℚ) = 0` (all three newform factors have `L(A, 1) ≠ 0`).
`X_0(63)` has `8` cusps of which `4` are rational, and no prime
`ℓ < 100` attains `#X_0(63)(𝔽_ℓ) = 4`: the minimum over `3 ≤ ℓ < 60` is
`8`, at `ℓ = 5`.  `#J_0(63)(ℚ)` divides `6144`. -/
theorem y0HasNoRationalPoint_sixtyThree : Y0HasNoRationalPoint 63 :=
  sorry

/-- **`Y_0(75)(ℚ) = ∅`** (sorry node; `X_0(75)` has genus `5`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(75)(ℚ) = 0` (all four newform factors have `L(A, 1) ≠ 0`).
`X_0(75)` has `12` cusps of which `4` are rational, and no prime
`ℓ < 100` attains `#X_0(75)(𝔽_ℓ) = 4`: the minimum over `3 ≤ ℓ < 60` is
`8`, at `ℓ = 7`.  `#J_0(75)(ℚ)` divides `2560`. -/
theorem y0HasNoRationalPoint_seventyFive : Y0HasNoRationalPoint 75 :=
  sorry

end Fermat

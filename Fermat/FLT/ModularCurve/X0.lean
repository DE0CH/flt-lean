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

* **`Y_0(N)`, not `X_0(N)`, in the STATEMENTS.**  The level statements
  are about the affine coarse space: "`X_0(N)(ℚ)` consists only of
  cusps" is literally "`Y_0(N)(ℚ) = ∅`", and phrasing them affinely
  keeps the cusps out of the *interface* consumed by
  `FreyCurve/MazurTorsion.lean`.

  It does NOT keep them out of the *proofs*, and an earlier version of
  this docstring claimed otherwise.  Rank `0` bounds `#X_0(N)(ℚ)`; only
  the count of rational cusps turns that bound into emptiness of
  `Y_0(N)(ℚ)`.  So the compactification is on the critical path after
  all, and it is built below (`IsX0Compactification`, `IsJacobianOf`,
  `card_le_of_rankZeroJacobian`) — used by the seven single-prime
  levels, and stated so that the four sieve levels can reuse it.

## FAITHFULNESS AUDIT

There are four claim-shapes here, and each is true.  Shapes 1 and 2 are
now proven, each over strictly fewer sorried inputs than the node it
replaced; shape 3 is now proven at seven of its eleven named levels over
shape 4, and shape 4 is the compactification layer:

1. `exists_coarseModuliY0 N` — the `Γ₀(N)`-moduli problem over `ℚ` admits
   a coarse moduli space.  TRUE: this is the classical existence
   statement for `Y_0(N)` (Deligne–Rapoport, Katz–Mazur; or classically
   via the `j`-line and the modular polynomial).  It is now PROVEN from a
   split of the level: `exists_coarseModuliY0_of_pos` (`N ≥ 1`) carries
   the citation — Katz–Mazur Theorem 6.6.1 and (8.1.1) — and
   `exists_coarseModuliY0_zero` disposes of `N = 0`, which lies outside
   their theorem, from `isEmpty_of_gamma0Datum_zero` — itself PROVEN
   2026-07-26, so the `N = 0` half of this shape is now sorry-free
   outright and the citation at `_of_pos` is the only remaining input.

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

4. The compactification layer: `X_0(N) ⊇ Y_0(N)` with its finite cusp
   locus, `J_0(N)` by its Albanese universal property, the rank-`0`
   input, the Eichler–Shimura counts, and the reduction bound.  TRUE —
   each of its five leaves carries its own justification, and each is a
   named classical theorem rather than a repackaging of its consumer.
   The one hypothesis worth flagging is positivity of the genus, carried
   inside `HasRankZeroJacobian`: without it the reduction bound is FALSE
   at `N = 1`, where `X_0(1) = ℙ¹` has a trivial Jacobian and infinitely
   many rational points.

*Amended 2026-07-26.*  Shape 3 no longer covers the semiprime family
directly: `y0HasNoRationalPoint_prod_two_primes` is now PROVEN, and its
content sits in the two nodes `y0HasNoRationalPoint_prime` (Mazur 1978,
the only UNIFORM input in the module) and
`y0HasNoRationalPoint_semiprime_of_mazurPrimes` (Kenku, `61` explicit
levels).  Two further sorried shapes were introduced by that
decomposition, both about the degeneracy map `Y_0(N) ⟶ Y_0(M)` for
`M ∣ N`, and both TRUE:

4. `CyclicSubgroupOfOrder.ofDvd` — the sub-level structure `C[M] ⊆ C`,
   i.e. the `M`-torsion of `C`, the kernel of `[M]`.

5. `liesIn_ofDvd_iff` — that kernel commutes with base change.

*Amended again 2026-07-26.*  Shapes 4 and 5 are both now PROVEN, over a
single geometric leaf that replaces them:

6. `exists_torsionSubscheme` — for a cyclic subgroup scheme `C` of order
   `N` and ANY `M`, the `M`-torsion subfunctor of `C` is cut out by a
   closed subscheme of `E`, finite over the base.  TRUE: `C` is a finite
   flat commutative group scheme, `C[M]` is the fibre product of `[M]`
   with the zero section, and closed immersions are stable under base
   change and closed under composition.

   Everything else in shapes 4 and 5 is now proven from it: the subgroup
   axioms and the cyclic-of-order-`M` condition in
   `CyclicSubgroupOfOrder.ofTorsion` (the arithmetic input being
   `nsmul_eq_zero_iff_mem_zmultiples_div`: in `ℤ/N` with `M ∣ N` the
   `M`-torsion is the subgroup generated by `N / M`, of order exactly
   `M`), and base-change compatibility in `liesIn_ofDvd_iff` (from
   additivity and — for the converse direction — injectivity of
   `RelPoint.along`, which is where cartesianness of the square is used).

   Note the earlier statement of shape 4 described `C[M]` as the kernel
   of `[N / M]`.  That was a slip: in `ℤ/N` that kernel has order `N / M`,
   not `M`.  The object the degeneracy map needs is the unique subgroup
   of ORDER `M`, i.e. the kernel of `[M]`, generated by `N / M`.  The
   definition now says so.

*Amended a third time 2026-07-26: the compactification exists.*  Shape 3
no longer covers the two uniform statements either.  `Y_0(N)` is affine
and every route to `Y_0(N)(ℚ) = ∅` runs through the PROPER model, so
`y0HasNoRationalPoint_prime` and
`y0HasNoRationalPoint_semiprime_of_mazurPrimes` are now proven from
statements about `X_0(N)`, over the interface `IsCompactificationY0`:

7. `exists_compactificationY0` — the coarse space `Y_0(N)` is a smooth
   affine curve over `ℚ` and has a smooth proper compactification.  TRUE
   (Deligne–Rapoport III.1 / Katz–Mazur 8.2 for normality, plus the
   proper normal model of a function field).

8. `cuspidal_x0_prime` — Mazur 1978, Theorem 1: every rational point of
   `X_0(p)` is a cusp, for `p ∉ mazurIsogenyPrimes`.

9. `cuspidal_x0_semiprime_of_mazurPrimes` — Kenku's determination on the
   `61` residual semiprime levels, likewise on `X_0(pq)`.

Both 8 and 9 are quantified over EVERY model of the interface, so a
degenerate `X` cannot discharge them; and the passage from "cuspidal on
`X`" to "empty on `Y`" is no longer an informal remark but the proven
`y0HasNoRationalPoint_of_cuspidal`, resting on the equally proven
`y0HasNoRationalPoint_of_isEmpty` (one coarse space suffices, by
initiality).

The remaining missing subtree for 8 and 9 is `J_0(N)`: the Jacobian as an
abelian variety over `ℚ`, Abel–Jacobi from a rational cusp, and reduction
at a good prime.  With the interface in place the rank-`0` criterion can
now be STATED honestly — its conclusion is `∀ x : X(ℚ), hX.IsCusp x` and
the cusp count enters as a count of `X(𝔽_ℓ)` — which it could not be
while the module stopped at `Y_0(N)`.

The lemma they support, `y0HasNoRationalPoint_of_dvd`, is checked
against the ground truth by observing that the Mazur–Kenku list is
DIVISOR-CLOSED; see its docstring.

*Amended a fourth time 2026-07-26: the sieve layer.*  Shape 4's
compactification layer now carries a SIXTH leaf:

10. `exists_x0Sieve` — the Mordell–Weil sieve that the four levels
    `45, 54, 63, 75` need.  The ordinary counting bound
    `card_le_of_rankZeroJacobian` is never sharp at those four levels
    (no odd `ℓ ∤ N` attains `#X_0(N)(𝔽_ℓ) = 4`), so the bound must count
    FEWER than all of `X_0(N)(𝔽_ℓ)`: only those `𝔽_ℓ`-points whose
    Abel–Jacobi class lies in the image of `J_0(N)(ℚ)`.  TRUE, and a
    named classical technique rather than a repackaging of its consumer.
    The one hypothesis worth flagging is positivity of the genus, carried
    inside `HasRankZeroJacobian`: without it the reduction bound is FALSE
    at `N = 1`, where `X_0(1) = ℙ¹` has a trivial Jacobian and infinitely
    many rational points.

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

The compactification layer (`IsX0Compactification`, `IsJacobianOf`,
`HasRankZeroJacobian`, `card_le_of_rankZeroJacobian`) is now written as
an INTERFACE, and all eleven levels are proven over it — seven on a
single counting prime, four on the sieve `exists_x0Sieve`.
What the interface's six leaves still need, and none of it exists at
this pin:

* the smooth compactification of a coarse moduli space, and the cusps
  of `X_0(N)` with their field of definition
  (`exists_x0Compactification`, `exists_rationalCusps`);
* `J_0(N)` as an actual abelian scheme, its Mordell–Weil group, and the
  reduction map with its formal-group kernel
  (`card_le_of_rankZeroJacobian`);
* `S_2(Γ_0(N))`, the Hecke algebra, `L`-functions of modular abelian
  varieties and Kolyvagin–Logachev, which supply the rank-`0` input
  (`hasRankZeroJacobian_of_kenkuLevel`), and Eichler–Shimura, which
  supplies the point counts (`exists_x0Compactification_mod_prime`).

* the Abel–Jacobi image of `X_0(N)(𝔽_ℓ)` inside `J_0(N)(𝔽_ℓ)` as a
  computable finite object, which is what the multi-prime sieve leaf
  `exists_x0Sieve` asks for at the four levels `45, 54, 63, 75`.

Chabauty–Coleman is **not** on this list: the 2026-07-26 reconnaissance
found `rank J_0(N)(ℚ) = 0` at all eleven named levels, so none of them
needs it.  The four levels `45, 54, 63, 75` are proven over the
multi-prime Mordell–Weil sieve instead, which was — as predicted — a
strengthening of `card_le_of_rankZeroJacobian` rather than a new theory.
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
-- The finiteness of the `K`-points of a finite scheme over a geometric
-- point, which is what makes `isEmpty_of_gamma0Datum_zero` reachable:
-- `LocallyQuasiFinite` and `IsLocallyArtinian.of_locallyQuasiFinite`,
-- `IsArtinianScheme.finite`, and `pointEquivClosedPoint`.
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
-- `Scheme.residueField` / `Scheme.fromSpecResidueField`, used to produce a
-- geometric point above an arbitrary point of the base.
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
-- `ZMod ℓ` is the base ring of the reduction `X_0(N)_{𝔽_ℓ}`; see `SpecF`.
public import Mathlib.Data.ZMod.Basic

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

/-! ### The degenerate level `N = 0`

**The `Γ₀(0)`-moduli problem is supported on the empty scheme** — PROVEN
2026-07-26; this subsection was a single sorry leaf until then, and the
argument recorded here by its finder is the one that was carried out.

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
the set of `K`-algebra maps out of an Artinian `K`-algebra.

PROVEN 2026-07-26, along exactly those lines, from the two helper lemmas
`finite_sections_of_isFinite` and `infinite_zmultiples_of_addOrderOf_eq_zero`
below. -/

/-- **The sections of a finite morphism over a fixed geometric point are
finite in number.**

For `g : C ⟶ T` finite and `t : Spec K ⟶ T` a geometric point (`K`
algebraically closed), the `K`-points of `C` lying over `t` form a finite
set.

The proof is the classical one, and every step is mathlib API: `IsFinite`
is stable under base change, so `C ×_T Spec K` is finite over `Spec K`; a
quasi-finite quasi-compact scheme over an artinian one is artinian
(`IsLocallyArtinian.of_locallyQuasiFinite`), and an artinian scheme has a
finite underlying space (`IsArtinianScheme.finite`); and
`AlgebraicGeometry.pointEquivClosedPoint` identifies the sections of a
morphism of locally finite type to `Spec K` with the closed points of its
source.  A `K`-point of `C` over `t` induces such a section by the
universal property of the pullback, injectively. -/
theorem finite_sections_of_isFinite {C T : Scheme.{u}} (g : C ⟶ T) [IsFinite g]
    {K : Type u} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T) :
    Finite {w : Spec (CommRingCat.of K) ⟶ C // w ≫ g = t} := by
  classical
  let P : Scheme.{u} := Limits.pullback g t
  let π : P ⟶ Spec (CommRingCat.of K) := Limits.pullback.snd g t
  -- `IsFinite` is stable under base change, so the fibre is finite over `Spec K`.
  haveI : IsFinite π := inferInstanceAs (IsFinite (Limits.pullback.snd g t))
  -- A quasi-finite, quasi-compact scheme over an artinian one is artinian,
  -- hence has a finite underlying space.
  haveI : IsLocallyArtinian P := IsLocallyArtinian.of_locallyQuasiFinite π
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace π
  haveI : IsArtinianScheme P := ⟨⟩
  haveI : Finite P := IsArtinianScheme.finite
  -- A section of `π` is determined by the closed point of `P` it hits, and a
  -- `K`-point of `C` over `t` induces such a section.
  refine Finite.of_injective
    (fun w => (pointEquivClosedPoint π)
      ⟨Limits.pullback.lift w.1 (𝟙 _) (by rw [Category.id_comp]; exact w.2),
        Limits.pullback.lift_snd _ _ _⟩) ?_
  intro w₁ w₂ h
  have h2 := congrArg Subtype.val ((pointEquivClosedPoint π).injective h)
  refine Subtype.ext ?_
  have h3 := congrArg (· ≫ Limits.pullback.fst g t) h2
  simp only [Limits.pullback.lift_fst] at h3
  exact h3

/-- **An element of infinite additive order generates an infinite
subgroup.** `Nat.card` of `zmultiples y` is `addOrderOf y`, and a `Nat.card`
of `0` on a nonempty type means infinite. -/
theorem infinite_zmultiples_of_addOrderOf_eq_zero {G : Type u} [AddCommGroup G]
    (y : G) (h : addOrderOf y = 0) : Infinite (AddSubgroup.zmultiples y) := by
  have hc := Nat.card_zmultiples y
  rw [h] at hc
  exact (Nat.card_eq_zero.mp hc).resolve_left (not_isEmpty_iff.mpr ⟨0⟩)

/-- **The `Γ₀(0)`-moduli problem is supported on the empty scheme**
(PROVEN 2026-07-26; formerly a sorry leaf).

`[Γ₀(N)]` is a moduli problem only for `N ≥ 1`, so this degenerate level
lies outside the Katz–Mazur theorem cited at
`exists_coarseModuliY0_of_pos`; separating it off is what makes that
citation honest.  See the section comment above for the full argument and
for why the split exists. -/
theorem isEmpty_of_gamma0Datum_zero {T : Scheme.{0}} (d : Gamma0Datum 0 T) :
    IsEmpty T := by
  classical
  by_contra hne
  rw [not_isEmpty_iff] at hne
  obtain ⟨x⟩ := hne
  -- A geometric point of `T` above `x`: the algebraic closure of the residue
  -- field at `x`.
  let K := AlgebraicClosure (T.residueField x)
  let t : Spec (CommRingCat.of K) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) K)) ≫
      T.fromSpecResidueField x
  -- `geom_cyclic` states its conclusion under `ab.addCommGroup t`; bring that
  -- instance into the context so `addOrderOf` and `zmultiples` elaborate here.
  letI := d.ab.addCommGroup t
  obtain ⟨y, -, hyord, hyall⟩ := d.cyc.geom_cyclic K t
  -- The level structure has infinite order at this geometric point …
  haveI : Infinite (AddSubgroup.zmultiples y) :=
    infinite_zmultiples_of_addOrderOf_eq_zero y hyord
  -- … yet every element of `⟨y⟩` gives a distinct `K`-point of `d.cyc.C`
  -- over `t`, and those are finite in number because `d.cyc.ι ≫ d.f` is
  -- a finite morphism.
  haveI := d.cyc.isFinite
  haveI : Finite {w : Spec (CommRingCat.of K) ⟶ d.cyc.C //
      w ≫ (d.cyc.ι ≫ d.f) = t} := finite_sections_of_isFinite _ t
  have hex : ∀ z : AddSubgroup.zmultiples y,
      ∃ w : Spec (CommRingCat.of K) ⟶ d.cyc.C, w ≫ d.cyc.ι = (z.1 : _ ⟶ d.E) :=
    fun z => (hyall z.1).mpr z.2
  choose w hw using hex
  have hspec : ∀ z : AddSubgroup.zmultiples y, w z ≫ (d.cyc.ι ≫ d.f) = t := by
    intro z
    rw [← Category.assoc, hw z]
    exact z.1.2
  haveI : Finite (AddSubgroup.zmultiples y) := by
    refine Finite.of_injective (fun z => (⟨w z, hspec z⟩ :
      {w : Spec (CommRingCat.of K) ⟶ d.cyc.C // w ≫ (d.cyc.ι ≫ d.f) = t})) ?_
    intro z₁ z₂ hz
    have h1 : w z₁ = w z₂ := congrArg Subtype.val hz
    refine Subtype.ext (Subtype.ext ?_)
    rw [← hw z₁, ← hw z₂, h1]
  exact not_finite (AddSubgroup.zmultiples y)

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

**FALSITY AUDIT, 2026-07-26 — the hypothesis `hN : N ≠ 0` is NOT
decoration, and was ADDED on this date because the statement without it is
FALSE.**

At `N = 0` the conclusion is *unsatisfiable*, and the refutation is already
written down in this file: it is verbatim the argument of
`isEmpty_of_gamma0Datum_zero` above.  `geom_cyclic` at `N = 0` demands a
relative point `y` with `addOrderOf y = 0` — of INFINITE order — such that
the points lying in `C` are exactly `AddSubgroup.zmultiples y ≃ ℤ`.  But
`isFinite` makes `ι ≫ f` finite, so `C` is `Spec` of a finite-dimensional
`ℚ`-algebra and `{x | RelPoint.LiesIn ι x}` injects into
`Hom(Spec K, C)` — a finite set, since `ι` is a closed immersion and hence
a monomorphism.  A finite set cannot be `zmultiples` of an infinite-order
element.  The base `Spec ℚ` is nonempty, so the geometric point needed to
run this is available (it is `specAlgClos ℚ ≫ 𝟙 SpecQ`, the very one the
hypotheses are stated at) and the argument is not vacuous.

Meanwhile the HYPOTHESES at `N = 0` are satisfiable: any elliptic curve
over `ℚ` of positive Mordell–Weil rank has a rational point `y` of infinite
order, `⟨y⟩` is fixed pointwise by `Γ_ℚ`, and `addOrderOf y = 0`.  So the
`N = 0` instance is a genuine false statement, not a vacuous one, and no
prover could ever have discharged it.

The defect propagated: `nonempty_gamma0Datum_of_stable` and
`false_of_stable_of_y0HasNoRationalPoint` below are PROVEN from this leaf
and were therefore false as stated too — the first would have produced a
`Gamma0Datum 0 SpecQ`, which `isEmpty_of_gamma0Datum_zero` forbids over the
nonempty base `Spec ℚ`.  Both now carry `hN` as well.  Nothing downstream
is weakened: all twelve level nodes of `FreyCurve/MazurTorsion.lean` call
in at a concrete `N ≥ 20`, and the one infinite family at `N = p q` with
`p`, `q` prime.

TRUE for `N ≥ 1`, and this is the whole content of Galois descent for
finite étale schemes in characteristic `0`.  The argument: `⟨y⟩ ⊆ A(ℚ̄)` is a finite
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
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
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
level nodes, so no reformulation happens at the boundary.

`hN : N ≠ 0` was ADDED 2026-07-26: without it this statement is FALSE, for
the reason set out in the FALSITY AUDIT of
`exists_cyclicSubgroupOfOrder_of_galoisStable` above — at `N = 0` it would
produce a `Gamma0Datum 0 SpecQ`, which `isEmpty_of_gamma0Datum_zero`
forbids over the nonempty base `Spec ℚ`, while its own hypotheses are met
by any rational point of infinite order on a positive-rank curve. -/
theorem nonempty_gamma0Datum_of_stable (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} (hN : N ≠ 0) (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = N)
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
  obtain ⟨cyc⟩ := exists_cyclicSubgroupOfOrder_of_galoisStable ab N hN (e g) hord hst
  exact ⟨{ E := A, f := f, ab := ab, relativeDimensionOne := hdim, cyc := cyc }⟩

/-- **The consumption rule of this module.**

If `Y_0(N)` has no rational point but some elliptic curve over `ℚ` has a
Galois-stable cyclic subgroup of order `N`, then the classifying map
produces a rational point of `Y_0(N)` — a contradiction.  This is the one
place where the three sorried inputs above meet, and it is what the
twelve level nodes of `FreyCurve/MazurTorsion.lean` call.

`hN : N ≠ 0` was ADDED 2026-07-26, as the last link of the propagation
described in the FALSITY AUDIT of
`exists_cyclicSubgroupOfOrder_of_galoisStable`: at `N = 0` this statement
too is FALSE, since a rational point of infinite order on a positive-rank
curve satisfies `hg` and `hstable` while `Y0HasNoRationalPoint 0` holds
vacuously (the coarse space of the degenerate level is the empty scheme).
It is supplied at every call site by `norm_num`, all twelve level nodes
having a concrete `N ≥ 20`. -/
theorem false_of_stable_of_y0HasNoRationalPoint {N : ℕ}
    (hY : Y0HasNoRationalPoint N) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g)
    (hN : N ≠ 0) :
    False := by
  obtain ⟨Y, str, ⟨M⟩⟩ := exists_coarseModuliY0 N
  obtain ⟨d⟩ := nonempty_gamma0Datum_of_stable E hN g hg hstable
  exact (hY Y str M).elim (M.classify (𝟙 SpecQ) d)

/-! ### Functoriality in the level, and the descent along divisors

The twelve level nodes below are twelve *separate* determinations of the
rational points of a curve of genus `≥ 1`, and nothing about that is
uniform.  What IS uniform, and is built here, is the degeneracy map

`Y_0(N) ⟶ Y_0(M)` for `M ∣ N`, `(E, C) ↦ (E, C[M])`,

together with its consequence `y0HasNoRationalPoint_of_dvd`.  That single
lemma is what turns the one *infinite* family among the twelve —
`y0HasNoRationalPoint_prod_two_primes`, quantified over all pairs of
distinct primes — into a finite list of levels, by letting Mazur's prime
theorem be applied to a prime divisor of the level rather than to the
level itself.  It is stated here, once, rather than reproved inside each
level node.

**Why it is stated over the coarse space and not over data.**  A rational
point of `Y_0(N)` need not come from a `Γ₀(N)`-datum over `ℚ` — that is
exactly what "coarse" costs — so the map on points cannot be defined
pointwise.  It is obtained instead from the *universal property* of
`Y_0(N)`: `d ↦ classify_M (d.ofDvd)` is a natural transformation from the
`Γ₀(N)`-moduli problem to `Y_0(M)`, and initiality produces the morphism
`u : Y_0(N) ⟶ Y_0(M)` over `ℚ` through which every rational point is
pushed.  This is the only place in the module where `universal` is used,
and it is why that field was stated. -/

/-! #### The cyclic group theory behind `C[M]`

Three elementary facts about a cyclic group of order `N`, isolated here
so that `CyclicSubgroupOfOrder.ofTorsion` below is pure bookkeeping.  In
`ℤ/N` with `M ∣ N` the unique subgroup of order `M` is generated by
`N / M` and is exactly the `M`-torsion; that is the content of the second
lemma, and it is what makes `C[M]` a `Γ₀(M)`-structure. -/

/-- **The generator of the `M`-torsion of a cyclic group of order `N`**:
`(N / M) • y` has order exactly `M` when `y` has order `N` and `M ∣ N`. -/
theorem addOrderOf_nsmul_div_of_dvd {G : Type*} [AddCommGroup G] {M N : ℕ}
    (hN : N ≠ 0) (hMN : M ∣ N) (y : G) (hy : addOrderOf y = N) :
    addOrderOf ((N / M) • y) = M := by
  have hM : M ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hMN)
  have hMd : M * (N / M) = N := Nat.mul_div_cancel' hMN
  have hd : N / M ≠ 0 := by rintro h; rw [h, mul_zero] at hMd; exact hN hMd.symm
  rw [addOrderOf_nsmul' _ hd, hy, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hMN),
    Nat.div_div_self hMN hN]

/-- **The `M`-torsion of a cyclic group of order `N` is the subgroup
generated by `N / M`**, for `M ∣ N`.  This is the group-theoretic heart
of the degeneracy map: it identifies the *condition* `M • x = 0`, which
is what a torsion subscheme cuts out, with *membership in a cyclic
subgroup of order `M`*, which is what a `Γ₀(M)`-structure demands. -/
theorem nsmul_eq_zero_iff_mem_zmultiples_div {G : Type*} [AddCommGroup G] {M N : ℕ}
    (hN : N ≠ 0) (hMN : M ∣ N) (y : G) (hy : addOrderOf y = N)
    {x : G} (hx : x ∈ AddSubgroup.zmultiples y) :
    M • x = 0 ↔ x ∈ AddSubgroup.zmultiples ((N / M) • y) := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  have hM : M ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hMN)
  have hMd : M * (N / M) = N := Nat.mul_div_cancel' hMN
  have hzero : M • ((N / M) • y) = 0 := by
    rw [smul_smul, hMd, ← hy, addOrderOf_nsmul_eq_zero]
  constructor
  · intro h
    rw [← natCast_zsmul (k • y) M, smul_smul, ← addOrderOf_dvd_iff_zsmul_eq_zero, hy] at h
    have hdk : ((N / M : ℕ) : ℤ) ∣ k := by
      have hNc : ((N : ℕ) : ℤ) = (M : ℤ) * ((N / M : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hMd.symm
      rw [hNc] at h
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hM : (M : ℤ) ≠ 0)).mp h
    obtain ⟨j, rfl⟩ := hdk
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨j, by rw [← natCast_zsmul y (N / M), smul_smul, mul_comm]⟩
  · intro h
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp h
    rw [← hj, smul_comm, hzero, smul_zero]

/-- **The `M`-torsion sits inside the ambient cyclic group.** -/
theorem mem_zmultiples_of_mem_nsmul_div {G : Type*} [AddCommGroup G] {M N : ℕ} {y x : G}
    (h : x ∈ AddSubgroup.zmultiples ((N / M) • y)) : x ∈ AddSubgroup.zmultiples y := by
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  exact AddSubgroup.mem_zmultiples_iff.mpr
    ⟨j * ((N / M : ℕ) : ℤ), by rw [← natCast_zsmul y (N / M), smul_smul]⟩

/-- **The `M`-torsion of a cyclic subgroup scheme is again cut out by a
closed subscheme, finite over the base** (sorry node).

TRUE: `C` is finite flat over `T` with cyclic geometric fibres, hence a
finite flat commutative group scheme, so multiplication by `M` is an
endomorphism of `C` over `T` and `C[M]` is the fibre product of
`[M] : C ⟶ C` with the zero section `T ⟶ C`.  The zero section of a
scheme finite — hence separated — over `T` is a closed immersion, closed
immersions are stable under base change, and closed immersions compose;
so `C[M] ⟶ C ⟶ E` is a closed immersion and `C[M] ⟶ T` is finite.  On
relative points, membership of `C[M]` is membership of `C` together with
`M • x = 0`, which is what the characterisation below records.

This holds for EVERY `M`, with no divisibility hypothesis and no
constraint relating `M` to `N`: for `M = 0` the condition `0 • x = 0` is
vacuous and `C` itself works, and in general `C[M] = C[gcd (M, N)]`.
Keeping the leaf free of hypotheses it does not need is deliberate — the
arithmetic that `M ∣ N` buys is entirely group-theoretic and is
discharged in `CyclicSubgroupOfOrder.ofTorsion` below, so this node
carries only the geometry.

IRREDUCIBLE at this mathlib pin for the same reason as
`nonempty_gamma0Datum_of_stable`: the functor-of-points presentation used
here carries the group law on `RelPoint` rather than as a morphism
`E ×_T E ⟶ E`, so `[M] : C ⟶ C` is not available as a morphism of
schemes and the fibre product cannot be formed.  Supplying it needs the
group law as a morphism, which is the same missing theory.

**FLATNESS IS PART OF THIS LEAF** (added at integration, 2026-07-26, and
it is not decoration).  `CyclicSubgroupOfOrder` acquired a `flat` field —
that field is what makes the structure Katz–Mazur's finite *locally free*
`[Γ₀(N)]` rather than a strictly larger moduli problem; see the field's
own docstring for the `Spec ℚ[ε]` counterexample.  This leaf and
`CyclicSubgroupOfOrder.ofDvd` were written independently, against the
structure BEFORE and AFTER that field existed, so they merged cleanly and
then could not build: `ofTorsion` had no flatness to put in the field.
Carrying it here is the right place — `C[M]` is a torsion subscheme of an
already-flat `C`, so whatever construction discharges this leaf produces
flatness along with finiteness, and no separate argument is needed.  It
is threaded through `ofTorsion`'s `hflat` argument to `ofDvd`. -/
theorem exists_torsionSubscheme {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (M : ℕ) :
    ∃ (C' : Scheme.{u}) (ι' : C' ⟶ E), IsClosedImmersion ι' ∧ IsFinite (ι' ≫ f) ∧
      AlgebraicGeometry.Flat (ι' ≫ f) ∧
      ∀ (T' : Scheme.{u}) (g : T' ⟶ T) (x : RelPoint f g),
        letI := ab.addCommGroup g
        RelPoint.LiesIn ι' x ↔ (RelPoint.LiesIn c.ι x ∧ M • x = 0) :=
  sorry

/-- **A torsion subscheme of a cyclic subgroup scheme of order `N` is a
cyclic subgroup scheme of order `M`, for `M ∣ N`** (PROVEN).

This is everything about `C[M]` that is not the representability handled
by `exists_torsionSubscheme`: the subgroup axioms, which follow from
`smul_zero` / `smul_add` / `smul_neg` because `M • (-)` is additive, and
the level condition `geom_cyclic`, which is
`nsmul_eq_zero_iff_mem_zmultiples_div` applied fibre by fibre with
generator `(N / M) • y`.

`hN` excludes `N = 0`.  It is not cosmetic: `N = 0` asks the geometric
fibres of a scheme FINITE over the base to be infinite cyclic, so
`CyclicSubgroupOfOrder ab 0` is in fact vacuous — but vacuous for a
reason (finiteness of `ι ≫ f`) that this development does not have the
machinery to exploit, and without `hN` the statement would read as the
false claim that an infinite cyclic group has a subgroup of order `M`. -/
noncomputable def CyclicSubgroupOfOrder.ofTorsion {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    (c : CyclicSubgroupOfOrder ab N)
    {C' : Scheme.{u}} (ι' : C' ⟶ E) (hcl : IsClosedImmersion ι')
    (hfin : IsFinite (ι' ≫ f)) (hflat : AlgebraicGeometry.Flat (ι' ≫ f))
    (hmem : ∀ (T' : Scheme.{u}) (g : T' ⟶ T) (x : RelPoint f g),
      letI := ab.addCommGroup g
      RelPoint.LiesIn ι' x ↔ (RelPoint.LiesIn c.ι x ∧ M • x = 0)) :
    CyclicSubgroupOfOrder ab M where
  C := C'
  ι := ι'
  isClosedImmersion := hcl
  isFinite := hfin
  flat := hflat
  zero_liesIn g := by
    letI := ab.addCommGroup g
    refine (hmem _ g _).mpr ⟨c.zero_liesIn g, ?_⟩
    show M • (0 : RelPoint f g) = 0
    exact smul_zero M
  add_liesIn hx hy := by
    rename_i T' g x y
    letI := ab.addCommGroup g
    obtain ⟨hx1, hx2⟩ := (hmem _ g x).mp hx
    obtain ⟨hy1, hy2⟩ := (hmem _ g y).mp hy
    refine (hmem _ g _).mpr ⟨c.add_liesIn hx1 hy1, ?_⟩
    show M • (x + y) = 0
    rw [smul_add, hx2, hy2, add_zero]
  neg_liesIn hx := by
    rename_i T' g x
    letI := ab.addCommGroup g
    obtain ⟨hx1, hx2⟩ := (hmem _ g x).mp hx
    refine (hmem _ g _).mpr ⟨c.neg_liesIn hx1, ?_⟩
    show M • (-x) = 0
    rw [smul_neg, hx2, neg_zero]
  geom_cyclic := by
    intro K _ _ t
    letI := ab.addCommGroup t
    obtain ⟨y, hyC, hyord, hyall⟩ := c.geom_cyclic K t
    refine ⟨(N / M) • y, ?_, addOrderOf_nsmul_div_of_dvd hN hMN y hyord, ?_⟩
    · refine (hmem _ t _).mpr ⟨(hyall _).mpr (AddSubgroup.mem_zmultiples_iff.mpr
        ⟨((N / M : ℕ) : ℤ), natCast_zsmul y (N / M)⟩), ?_⟩
      rw [smul_smul, Nat.mul_div_cancel' hMN, ← hyord, addOrderOf_nsmul_eq_zero]
    · intro x
      rw [hmem _ t x, hyall x]
      constructor
      · rintro ⟨h1, h2⟩
        exact (nsmul_eq_zero_iff_mem_zmultiples_div hN hMN y hyord h1).mp h2
      · intro h
        have h1 : x ∈ AddSubgroup.zmultiples y := mem_zmultiples_of_mem_nsmul_div h
        exact ⟨h1, (nsmul_eq_zero_iff_mem_zmultiples_div hN hMN y hyord h1).mpr h⟩

/-- **The sub-level structure `C[M] ⊆ C` of a cyclic subgroup scheme of
order `N`, for `M ∣ N`** (PROVEN 2026-07-26 over `exists_torsionSubscheme`).

`C[M]` is the `M`-torsion of `C` — NOT, as an earlier version of this
docstring said, the kernel of `[N / M]`: in `ℤ/N` the kernel of `N / M`
has order `N / M`, whereas the sub-level structure wanted by the
degeneracy map `Y_0(N) ⟶ Y_0(M)` is the unique subgroup of order `M`,
which is the kernel of `[M]` and is generated by `N / M`.

The construction is `exists_torsionSubscheme` (the geometry: the torsion
subfunctor is a closed subscheme, finite over the base) fed to
`CyclicSubgroupOfOrder.ofTorsion` (the arithmetic: that subscheme is
cyclic of order exactly `M`). -/
noncomputable def CyclicSubgroupOfOrder.ofDvd {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    (c : CyclicSubgroupOfOrder ab N) : CyclicSubgroupOfOrder ab M :=
  CyclicSubgroupOfOrder.ofTorsion hN hMN c (exists_torsionSubscheme c M).choose_spec.choose
    (exists_torsionSubscheme c M).choose_spec.choose_spec.1
    (exists_torsionSubscheme c M).choose_spec.choose_spec.2.1
    (exists_torsionSubscheme c M).choose_spec.choose_spec.2.2.1
    (exists_torsionSubscheme c M).choose_spec.choose_spec.2.2.2

/-- **Membership in `C[M]`, on relative points** (PROVEN): a relative
point lies in `C[M]` exactly when it lies in `C` and is killed by `M`.

This is the *only* interface to `CyclicSubgroupOfOrder.ofDvd` that
anything downstream should use; the underlying scheme is obtained by
choice from `exists_torsionSubscheme` and is not otherwise pinned. -/
theorem CyclicSubgroupOfOrder.liesIn_ofDvd_iff_mem {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    (c : CyclicSubgroupOfOrder ab N) (T' : Scheme.{u}) (g : T' ⟶ T) (x : RelPoint f g) :
    letI := ab.addCommGroup g
    RelPoint.LiesIn (c.ofDvd hN hMN).ι x ↔ (RelPoint.LiesIn c.ι x ∧ M • x = 0) :=
  (exists_torsionSubscheme c M).choose_spec.choose_spec.2.2.2 T' g x

/-- **The degeneracy map on `Γ₀`-data, `(E, C) ↦ (E, C[M])` for `M ∣ N`.**

The elliptic scheme is untouched — same total space, same structure
morphism, same abelian-scheme structure, same relative dimension — and
only the level structure is cut down by `CyclicSubgroupOfOrder.ofDvd`.
Writing it this way is what makes `IsBaseChangeOf.ofDvd` below carry the
*same* `map` and the *same* cartesian square, so that the only thing left
to check there is the level-structure axiom. -/
noncomputable def Gamma0Datum.ofDvd {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    {T : Scheme.{u}} (d : Gamma0Datum N T) : Gamma0Datum M T where
  E := d.E
  f := d.f
  ab := d.ab
  relativeDimensionOne := d.relativeDimensionOne
  cyc := d.cyc.ofDvd hN hMN

/-! #### The map on relative points induced by a cartesian square

`RelPoint.along hb.map hb.isPullback.w` is additive by two of the axioms
of `IsBaseChangeOf`, and INJECTIVE because the square is cartesian — a
`T''`-point of `E'` is determined by its two projections.  Injectivity is
what makes the torsion condition `M • x = 0` descend in *both*
directions, which is exactly what `liesIn_ofDvd_iff` needs. -/

/-- **An additive map commutes with `nsmul`.**  Stated for bare functions
with the two homomorphism equations as hypotheses, rather than for an
`AddMonoidHom`, because `RelPoint.along` is not packaged as one and the
group structures here come from `AbelianSchemeStruct.addCommGroup` rather
than from instance synthesis. -/
theorem map_nsmul_of_map_add {A B : Type*} [AddMonoid A] [AddMonoid B]
    (F : A → B) (h0 : F 0 = 0) (hadd : ∀ x y, F (x + y) = F x + F y) :
    ∀ (n : ℕ) (x : A), F (n • x) = n • F x
  | 0, x => by simpa using h0
  | n + 1, x => by
      rw [succ_nsmul, hadd, map_nsmul_of_map_add F h0 hadd n x, succ_nsmul]

/-- **`RelPoint.along` preserves the zero section**, restated in the
group structures of `AbelianSchemeStruct.addCommGroup`. -/
theorem along_zero {N : ℕ} {T' T : Scheme.{u}} {h : T' ⟶ T} {d' : Gamma0Datum N T'}
    {d : Gamma0Datum N T} (hb : IsBaseChangeOf h d' d) {T'' : Scheme.{u}} (g : T'' ⟶ T') :
    letI := d'.ab.addCommGroup g
    letI := d.ab.addCommGroup (g ≫ h)
    RelPoint.along hb.map hb.isPullback.w (0 : RelPoint d'.f g) = 0 :=
  hb.map_zero g

/-- **`RelPoint.along` is additive**, restated in the group structures of
`AbelianSchemeStruct.addCommGroup`. -/
theorem along_add {N : ℕ} {T' T : Scheme.{u}} {h : T' ⟶ T} {d' : Gamma0Datum N T'}
    {d : Gamma0Datum N T} (hb : IsBaseChangeOf h d' d) {T'' : Scheme.{u}} {g : T'' ⟶ T'}
    (x y : RelPoint d'.f g) :
    letI := d'.ab.addCommGroup g
    letI := d.ab.addCommGroup (g ≫ h)
    RelPoint.along hb.map hb.isPullback.w (x + y)
      = RelPoint.along hb.map hb.isPullback.w x + RelPoint.along hb.map hb.isPullback.w y :=
  hb.map_add x y

/-- **`RelPoint.along` commutes with multiplication by a natural
number.** -/
theorem along_nsmul {N : ℕ} {T' T : Scheme.{u}} {h : T' ⟶ T} {d' : Gamma0Datum N T'}
    {d : Gamma0Datum N T} (hb : IsBaseChangeOf h d' d) {T'' : Scheme.{u}} {g : T'' ⟶ T'}
    (n : ℕ) (x : RelPoint d'.f g) :
    letI := d'.ab.addCommGroup g
    letI := d.ab.addCommGroup (g ≫ h)
    RelPoint.along hb.map hb.isPullback.w (n • x)
      = n • RelPoint.along hb.map hb.isPullback.w x :=
  letI := d'.ab.addCommGroup g
  letI := d.ab.addCommGroup (g ≫ h)
  map_nsmul_of_map_add _ (along_zero hb g) (fun a b => along_add hb a b) n x

/-- **`RelPoint.along` is injective along a cartesian square.**  A
`T''`-point of the pullback `E'` is determined by its projections to `T'`
and to `E`; the projection to `T'` is the fixed base point `g`, so the
projection to `E` — which is exactly `RelPoint.along` — determines it. -/
theorem along_inj {N : ℕ} {T' T : Scheme.{u}} {h : T' ⟶ T} {d' : Gamma0Datum N T'}
    {d : Gamma0Datum N T} (hb : IsBaseChangeOf h d' d) {T'' : Scheme.{u}} {g : T'' ⟶ T'}
    {a b : RelPoint d'.f g}
    (hab : RelPoint.along hb.map hb.isPullback.w a
        = RelPoint.along hb.map hb.isPullback.w b) : a = b :=
  Subtype.ext (hb.isPullback.hom_ext (by rw [a.2, b.2]) (congrArg Subtype.val hab))

/-- **The degeneracy map is compatible with base change, on the level
structure** (PROVEN 2026-07-26).

`C'[M]` is the `M`-torsion of `C'`, `C'` is the pullback of `C` as a
subgroup scheme of `E'` by `hb.liesIn_iff`, and the torsion CONDITION
`M • x = 0` transfers across `RelPoint.along` in both directions: forward
because `along` is additive (`along_nsmul`, `along_zero`), backward
because it is injective (`along_inj`, which is where cartesianness of the
square is used and the only place in this module where it is).

This is the *only* axiom of `IsBaseChangeOf` that the degeneracy map does
not inherit verbatim from `hb`, because the other four mention only data
that `Gamma0Datum.ofDvd` copies unchanged. -/
theorem liesIn_ofDvd_iff {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    {T' T : Scheme.{u}} {h : T' ⟶ T} {d' : Gamma0Datum N T'}
    {d : Gamma0Datum N T} (hb : IsBaseChangeOf h d' d)
    {T'' : Scheme.{u}} {g : T'' ⟶ T'} (x : RelPoint d'.f g) :
    RelPoint.LiesIn (d'.ofDvd hN hMN).cyc.ι x ↔
      RelPoint.LiesIn (d.ofDvd hN hMN).cyc.ι
        (RelPoint.along hb.map hb.isPullback.w x) := by
  show RelPoint.LiesIn (d'.cyc.ofDvd hN hMN).ι x ↔
    RelPoint.LiesIn (d.cyc.ofDvd hN hMN).ι (RelPoint.along hb.map hb.isPullback.w x)
  rw [CyclicSubgroupOfOrder.liesIn_ofDvd_iff_mem hN hMN d'.cyc _ g x,
    CyclicSubgroupOfOrder.liesIn_ofDvd_iff_mem hN hMN d.cyc _ (g ≫ h) _]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hb.liesIn_iff x).mp h1, by rw [← along_nsmul hb M x, h2, along_zero hb g]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(hb.liesIn_iff x).mpr h1, along_inj hb ?_⟩
    rw [along_nsmul hb M x, h2, along_zero hb g]

/-- **A base change of `Γ₀(N)`-data induces a base change of the
degenerated `Γ₀(M)`-data.**

Four of the five axioms are `hb`'s own, because `Gamma0Datum.ofDvd`
changes nothing they mention; the fifth is `liesIn_ofDvd_iff`. -/
noncomputable def IsBaseChangeOf.ofDvd {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    {T' T : Scheme.{u}} {h : T' ⟶ T} {d' : Gamma0Datum N T'}
    {d : Gamma0Datum N T} (hb : IsBaseChangeOf h d' d) :
    IsBaseChangeOf h (d'.ofDvd hN hMN) (d.ofDvd hN hMN) where
  map := hb.map
  isPullback := hb.isPullback
  map_zero := hb.map_zero
  map_add := hb.map_add
  liesIn_iff x := liesIn_ofDvd_iff hN hMN hb x

/-- **Descent along divisors of the level: if `Y_0(M)(ℚ) = ∅` and
`M ∣ N` then `Y_0(N)(ℚ) = ∅`** (PROVEN).

This is the uniform half of every composite level statement.  The proof
is the universal property and nothing else: `d ↦ classify_M (d.ofDvd)` is
a natural transformation from the `Γ₀(N)`-moduli problem to a coarse
space of the `Γ₀(M)`-problem, so initiality of `Y_0(N)` yields a
`ℚ`-morphism `u : Y_0(N) ⟶ Y_0(M)`, and composing a rational point of
`Y_0(N)` with `u` gives one of `Y_0(M)`.

**Sanity check against the ground truth.**  The contrapositive says the
set of levels with a rational point is closed under divisors, and the
Mazur–Kenku list `{1, …, 19, 21, 25, 27, 37, 43, 67, 163}` is indeed
divisor-closed: `27 ↦ 9, 3`; `25 ↦ 5`; `21 ↦ 3, 7`; `18 ↦ 9, 6, 3, 2`;
`16 ↦ 8, 4, 2`; `12 ↦ 6, 4, 3, 2`, and every proper divisor of a level
`≤ 19` is `≤ 19`.  The four large primes `37, 43, 67, 163` have no proper
divisor but `1`.  So this lemma is consistent with the classification,
which is the check that matters — a level statement that contradicted it
would be false rather than open. -/
theorem y0HasNoRationalPoint_of_dvd {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    (hM : Y0HasNoRationalPoint M) : Y0HasNoRationalPoint N := by
  intro Y str hcoarse
  obtain ⟨Y', str', ⟨cM⟩⟩ := exists_coarseModuliY0 M
  obtain ⟨u, ⟨hu, -⟩, -⟩ :=
    hcoarse.universal str' (fun g d => cM.classify g (d.ofDvd hN hMN))
      (by intro _ _ h _ _ hg _ _ hb; exact cM.classify_natural h hg (hb.ofDvd hN hMN))
  refine ⟨fun x => (hM Y' str' cM).elim ⟨x.1 ≫ u, ?_⟩⟩
  rw [Category.assoc, hu, x.2]

/-! ### One coarse space suffices, and the smooth compactification

`Y0HasNoRationalPoint N` quantifies over EVERY coarse moduli space of the
`Γ₀(N)`-problem, which is the right statement but the wrong thing to work
with: a level computation is carried out on one model.  The first lemma
below closes that gap once and for all — emptiness at a single coarse
space propagates to all of them, by the same initiality argument as
`y0HasNoRationalPoint_of_dvd` with `M = N`.

The rest of this section is the **compactification interface**, which the
module docstring names as the next decomposition and which is built here.
Its purpose is to move the two remaining uniform statements — Mazur's
prime theorem and Kenku's semiprime range — off the affine `Y_0(N)` and
onto `X_0(N)`, which is where their proofs live and where the only known
routes (rank `0` plus reduction, and Chabauty–Coleman) can even be
phrased.  See the docstring of `y0HasNoRationalPoint_semiprime_of_mazurPrimes`
for why they CANNOT be phrased against `Y_0(N)` alone. -/

/-- **Emptiness at one coarse space propagates to all of them** (PROVEN).

Any two coarse spaces of the `Γ₀(N)`-problem are canonically
`ℚ`-isomorphic by initiality, so it is enough to exhibit ONE with no
rational point.  The proof does not even need the isomorphism: initiality
of `str'` against the natural transformation `classify` of `str` gives a
`ℚ`-morphism `u : Y' ⟶ Y` along which a rational point of `Y'` pushes to
one of `Y`.

This is what lets every level computation below be performed on a single
chosen model. -/
theorem y0HasNoRationalPoint_of_isEmpty {N : ℕ} {Y : Scheme.{0}} {str : Y ⟶ SpecQ}
    (hc : IsCoarseModuliY0 N str) (he : IsEmpty (RelPoint str (𝟙 SpecQ))) :
    Y0HasNoRationalPoint N := by
  intro Y' str' hc'
  obtain ⟨u, ⟨hu, -⟩, -⟩ := hc'.universal str (fun g d => hc.classify g d)
    (by intro _ _ h _ _ hg _ _ hb; exact hc.classify_natural h hg hb)
  exact ⟨fun x => he.elim ⟨x.1 ≫ u, by rw [Category.assoc, hu, x.2]⟩⟩

/-- **`str_X : X ⟶ Spec ℚ` is the smooth compactification of the coarse
space `str_Y : Y ⟶ Spec ℚ`.**

`Y_0(N)` is a smooth affine curve over `ℚ`; `X_0(N)` is the unique smooth
proper curve containing it as a dense open subscheme, and the finite
complement is the set of cusps.  The interface records exactly that: an
open immersion `j` over `ℚ` with dense image into a proper smooth `X`.

**Why these four conditions and no fewer.**  A smooth curve has a smooth
compactification that is unique up to unique isomorphism *given the
curve*, so `IsOpenImmersion j`, `IsDominant j`, `IsProper strX` and
`Smooth strX` together pin `X` down as tightly as `IsCoarseModuliY0` pins
`Y` — and `Y` is already pinned by initiality.  Dropping density would
allow `X = Y ⊔ (anything proper)`; dropping properness would allow
`X = Y` with no cusps at all.  Neither would make any statement below
FALSE — the leaves are quantified over all models of the interface, so a
degenerate model only makes them harder — but both would make the
interface useless to the layer it exists to enable, since `J_0(N)` and
reduction at a good prime are statements about the proper model.

**Why there is no cusp DATA here.**  Cuspidality is a property, not a
choice: a rational point of `X` is a cusp exactly when it does not come
from a rational point of `Y` (`IsCompactificationY0.IsCusp`).  For an
open immersion that is the honest scheme-theoretic condition, and
carrying a `Finset` of cusps instead would be an invitation to state a
count as a hypothesis — which is precisely the smuggling that
`y0HasNoRationalPoint_semiprime_of_mazurPrimes`'s docstring warns
against. -/
structure IsCompactificationY0 {Y X : Scheme.{0}} (strY : Y ⟶ SpecQ) (strX : X ⟶ SpecQ) where
  /-- the inclusion of the affine coarse space -/
  j : Y ⟶ X
  /-- the inclusion is a morphism over `ℚ` -/
  over : j ≫ strX = strY
  /-- `Y` is an open subscheme of `X` -/
  isOpenImmersion : IsOpenImmersion j
  /-- `Y` is DENSE in `X`: `X` is a compactification of `Y`, not of
  something smaller -/
  isDominant : IsDominant j
  /-- `X` is proper over `ℚ` -/
  proper : IsProper strX
  /-- `X` is smooth over `ℚ` -/
  smooth : Smooth strX

/-- **A rational point of `X_0(N)` is a cusp when it does not come from a
rational point of `Y_0(N)`.**

For an open immersion this is the scheme-theoretic condition: a
`ℚ`-point of `X` whose image lies in the open subscheme `Y` factors
through `Y`, so the points that do not factor are exactly the ones
supported on the closed complement.

The condition `y ≫ strY = 𝟙` is not imposed and is not missing: it
follows from `y ≫ j = x.1` and `IsCompactificationY0.over`. -/
def IsCompactificationY0.IsCusp {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (hX : IsCompactificationY0 strY strX) (x : RelPoint strX (𝟙 SpecQ)) : Prop :=
  ¬ ∃ y : SpecQ ⟶ Y, y ≫ hX.j = x.1

/-- **`X_0(N)(ℚ)` cuspidal implies `Y_0(N)(ℚ) = ∅`** (PROVEN).

This is the bridge the module was missing, and it is the step that the
sentence "`X_0(N)(ℚ)` consists only of cusps is literally `Y_0(N)(ℚ) = ∅`"
in the module docstring was asserting informally.  It is now a proof: a
rational point of `Y` maps to a rational point of `X` that visibly comes
from `Y`, hence is not a cusp; so if every rational point of `X` is a
cusp then `Y` has none, and `y0HasNoRationalPoint_of_isEmpty` carries
that from this one model to every coarse space. -/
theorem y0HasNoRationalPoint_of_cuspidal {N : ℕ} {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ}
    {strX : X ⟶ SpecQ} (hc : IsCoarseModuliY0 N strY)
    (hX : IsCompactificationY0 strY strX)
    (hall : ∀ x : RelPoint strX (𝟙 SpecQ), hX.IsCusp x) : Y0HasNoRationalPoint N := by
  refine y0HasNoRationalPoint_of_isEmpty hc ⟨fun y => ?_⟩
  exact hall ⟨y.1 ≫ hX.j, by rw [Category.assoc, hX.over, y.2]⟩ ⟨y.1, rfl⟩

/-- **Existence of the smooth compactification `X_0(N)`** (sorry node).

TRUE, and classical, in two independent halves:

* the coarse space `Y_0(N)` is a smooth affine curve over `ℚ` — normality
  of a coarse moduli space of a smooth DM stack of dimension one, plus
  "normal curve = smooth curve" (Deligne–Rapoport III.1, Katz–Mazur 8.2);
* a smooth curve over a field has a smooth compactification, unique up to
  unique isomorphism — the standard function-field construction, the
  proper normal model of the function field of `Y`.

For `N = 0` the moduli problem is supported on the empty base (a scheme
finite over its base cannot have infinite cyclic geometric fibres), so
`Y_0(0)` is the empty scheme and `X = Y = ∅` satisfies every condition
vacuously; the statement is therefore uniform in `N`.

IRREDUCIBLE at this mathlib pin: neither the normality of coarse spaces
nor the smooth compactification of a curve exists here, and both are
genuinely separate theories from anything else in this module. -/
theorem exists_compactificationY0 {N : ℕ} {Y : Scheme.{0}} {strY : Y ⟶ SpecQ}
    (_hc : IsCoarseModuliY0 N strY) :
    ∃ (X : Scheme.{0}) (strX : X ⟶ SpecQ), Nonempty (IsCompactificationY0 strY strX) :=
  sorry

/-! ### The prime levels, and the finite residue of the semiprime family -/

/-- **The twelve primes admitting a rational cyclic isogeny of that
degree**, `{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`.

These are exactly the primes in the Mazur–Kenku list
`{1, …, 19, 21, 25, 27, 37, 43, 67, 163}`.  The elliptic-curve-side
statement carrying the same list is
`WeierstrassCurve.prime_mem_cyclicIsogenyDegrees` in
`FreyCurve/MazurTorsion.lean`, which is downstream of this module and so
cannot be used here. -/
def mazurIsogenyPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}

/-- **Mazur 1978, Theorem 1** (sorry node): for every prime
`p ∉ mazurIsogenyPrimes`, every rational point of `X_0(p)` is a cusp.

TRUE — Mazur, *Rational isogenies of prime degree*, Invent. Math. 44
(1978), Theorem 1: `X_0(p)(ℚ)` consists of the two cusps `0` and `∞` for
every prime `p ∉ {2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`.

**This is the statement in the shape Mazur proves it**, which is the
point of routing `y0HasNoRationalPoint_prime` through it.  The argument
is: the Eisenstein quotient `J̃` of `J_0(p)` has Mordell–Weil rank `0`
(Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47
(1977)); `x ↦ [x − ∞]` embeds `X_0(p)(ℚ)` in `J̃(ℚ)`, which is therefore
finite; and a specialisation argument at `3` forces the image to be
cuspidal for `p ≥ 23`, `p ∉ {37, 43, 67, 163}`.  Every object in that
sentence — `J_0(p)`, the Hecke algebra, the Eisenstein ideal, the
Mordell–Weil theorem, reduction of an abelian variety — is a subtree that
does not exist at this pin, and none of it can be *stated* against the
affine `Y_0(p)`.

Quantified over every model of `IsCompactificationY0`, so it is at least
as strong as the `Y_0(p)` statement it replaces and cannot be discharged
by a degenerate choice of `X`.

Note the conclusion is genuinely stronger than the elliptic-curve
statement `WeierstrassCurve.prime_mem_cyclicIsogenyDegrees` in
`FreyCurve/MazurTorsion.lean` (which is downstream of this module and so
unusable here): it rules out rational points of a COARSE space, which
need not be represented by a pair `(E, C)` defined over `ℚ`. -/
theorem cuspidal_x0_prime {p : ℕ} (_hp : p.Prime) (_hmem : p ∉ mazurIsogenyPrimes)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (_hc : IsCoarseModuliY0 p strY) (hX : IsCompactificationY0 strY strX)
    (x : RelPoint strX (𝟙 SpecQ)) : hX.IsCusp x :=
  sorry

/-- **Mazur's rational isogenies of prime degree, on the modular curve**
(sorry node): `Y_0(p)(ℚ) = ∅` for every prime `p` outside
`mazurIsogenyPrimes`.

TRUE — this is Mazur, *Rational isogenies of prime degree*, Invent. Math.
44 (1978), Theorem 1, in its modular-curve form: `X_0(p)(ℚ)` consists of
the two cusps for every prime `p ∉ {2, 3, 5, 7, 11, 13, 17, 19, 37, 43,
67, 163}`.

**This is the statement that makes the semiprime family finite**, via
`y0HasNoRationalPoint_of_dvd` applied to `p ∣ p * q`; it is the only
uniform input available, since every other tool here is a per-level
computation.

Relation to what is already in the tree.  The elliptic-curve phrasing,
`WeierstrassCurve.prime_mem_cyclicIsogenyDegrees`, is PROVEN in
`FreyCurve/MazurTorsion.lean` from the single leaf
`WeierstrassCurve.not_isogenyCharacter_of_prime_ge_twentyThree`.  That
module *imports* this one, so the implication cannot be used in this
direction, and in any case the modular-curve statement is genuinely
STRONGER: it rules out rational points of the coarse moduli space, which
need not be represented by a pair `(E, C)` defined over `ℚ`.  The two
should be reconciled once the layer below exists — the honest route is to
prove this node and *derive* the elliptic-curve one from it through
`false_of_stable_of_y0HasNoRationalPoint`, which is exactly the shape
`MazurTorsion.lean` already uses for the twelve composite levels.

IRREDUCIBLE at this pin: Mazur's argument is the Eisenstein ideal in the
Hecke algebra acting on `J_0(p)`, none of which exists here.  See the
module docstring for the three missing subtrees.

PROVEN 2026-07-26 over the compactification interface: the content is now
`cuspidal_x0_prime`, which is Mazur's Theorem 1 in the form he states and
proves it — a statement about `X_0(p)`, not about `Y_0(p)`. -/
theorem y0HasNoRationalPoint_prime {p : ℕ} (hp : p.Prime)
    (hmem : p ∉ mazurIsogenyPrimes) : Y0HasNoRationalPoint p := by
  obtain ⟨Y, strY, ⟨hc⟩⟩ := exists_coarseModuliY0 p
  obtain ⟨X, strX, ⟨hX⟩⟩ := exists_compactificationY0 hc
  exact y0HasNoRationalPoint_of_cuspidal hc hX (cuspidal_x0_prime hp hmem hc hX)

/-- **Kenku's semiprime determination, on `X_0(pq)`** (sorry node): for
distinct primes `p, q` both in `mazurIsogenyPrimes` with
`p * q ∉ {6, 10, 14, 15, 21}`, every rational point of `X_0(pq)` is a
cusp.

TRUE, and FINITE: `61` explicit levels, the smallest `2 · 11 = 22` and
the largest `67 · 163 = 10921`.  Sources: Kenku, Math. Proc. Cambridge
Philos. Soc. **85** (1979) 21–23 (`X_0(35)`, `X_0(39)`); ibid. **87**
(1980) 15–20 (`X_0(65)`, `X_0(91)`); J. London Math. Soc. (2) **22**
(1980) 249–256; ibid. **23** (1981) 415–427; J. Number Theory **15**
(1982) 199–202.

This is `y0HasNoRationalPoint_semiprime_of_mazurPrimes` moved onto the
compactification, which is where its two available routes live; see that
node's docstring for why neither can be stated against the affine
`Y_0(pq)`.  Every one of the `61` levels has genus `≥ 2`, so none is an
elliptic-curve rank computation. -/
theorem cuspidal_x0_semiprime_of_mazurPrimes {p q : ℕ} (_hp : p.Prime)
    (_hq : q.Prime) (_hpq : p ≠ q) (_hpm : p ∈ mazurIsogenyPrimes)
    (_hqm : q ∈ mazurIsogenyPrimes)
    (_hmem : p * q ∉ ({6, 10, 14, 15, 21} : Finset ℕ))
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (_hc : IsCoarseModuliY0 (p * q) strY) (hX : IsCompactificationY0 strY strX)
    (x : RelPoint strX (𝟙 SpecQ)) : hX.IsCusp x :=
  sorry

/-- **Kenku's semiprime determination, on the residual finite range**
(sorry node): `Y_0(pq)(ℚ) = ∅` for distinct primes `p, q` BOTH in
`mazurIsogenyPrimes` with `p * q ∉ {6, 10, 14, 15, 21}`.

TRUE: the semiprimes in the Mazur–Kenku list are exactly `6, 10, 14, 15,
21`, so every other product of two distinct primes is absent from it.

**This node is finite, and that is the whole point of the decomposition
above.**  `mazurIsogenyPrimes` has `12` elements, so there are `66`
unordered pairs; five of them give the excluded products; `61` remain,
the smallest being `2 · 11 = 22` and the largest `67 · 163 = 10921`.
Sources: Kenku, Math. Proc. Cambridge Philos. Soc. **85** (1979) 21–23
(`X_0(35)`, `X_0(39)`); ibid. **87** (1980) 15–20 (`X_0(65)`, `X_0(91)`);
J. London Math. Soc. (2) **22** (1980) 249–256; ibid. **23** (1981)
415–427; J. Number Theory **15** (1982) 199–202.

**WHAT THIS NODE STILL NEEDS, and why it is a subtree rather than a
leaf.**  Every one of the `61` pairs has `X_0(pq)` of genus `≥ 2` —
already `X_0(22)` has genus `2`, and no semiprime level has genus `1`
(the genus-`1` levels are `11, 14, 15, 17, 19, 20, 21, 24, 27, 32, 36,
49`, of which only `14, 15, 21` are semiprimes and all three are
excluded).  So none of them is an elliptic-curve rank computation, and
each is settled by one of:

* **rank `0` plus reduction** — `J_0(pq)(ℚ)` finite, Abel–Jacobi
  `X_0(pq) ↪ J_0(pq)` at a rational cusp, injectivity of reduction at a
  good prime `ℓ`, and then `#X_0(pq)(ℚ) ≤ #X_0(pq)(𝔽_ℓ) = #cusps`;
* **Chabauty–Coleman** for the pairs where the rank is positive but
  below the genus.

Neither is stated as a leaf here, deliberately.  Both are statements
about `X_0(pq)` — the SMOOTH COMPACTIFICATION, its cusps, its Jacobian,
and an integral model to reduce along — and this module stops at the
affine coarse space `Y_0(N)` precisely to keep that out of the critical
path.  Writing either criterion against `Y_0(N)` alone would have to
smuggle the point count into a hypothesis, since rank `0` by itself gives
FINITENESS of `X_0(N)(ℚ)` and never emptiness of `Y_0(N)(ℚ)`; the step
from finite to empty *is* the cusp count.  A criterion whose hypothesis
is equivalent to its conclusion would be a false economy, so the honest
next decomposition is the compactification interface first
(`X_0(N) ⊇ Y_0(N)` proper smooth, with its rational cusps), then
`J_0(N)` as an abelian scheme, and only then the two criteria.

**The first of those three steps is DONE (2026-07-26).**
`IsCompactificationY0` above is the compactification interface, and this
node is now proven from `cuspidal_x0_semiprime_of_mazurPrimes`, which is
the same assertion about `X_0(pq)`.  What remains for a later owner is
step two — `J_0(N)` as an abelian variety over `ℚ`, with Abel–Jacobi from
a rational cusp and reduction at a good prime — and only then step three,
the rank-`0` criterion.  Note that with the interface in place the
rank-`0` criterion CAN now be stated honestly: its conclusion is
`∀ x : X(ℚ), hX.IsCusp x`, and the cusp count enters as a count of
`X(𝔽_ℓ)`, not as a hypothesis about `X(ℚ)`. -/
theorem y0HasNoRationalPoint_semiprime_of_mazurPrimes {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hpm : p ∈ mazurIsogenyPrimes)
    (hqm : q ∈ mazurIsogenyPrimes)
    (hmem : p * q ∉ ({6, 10, 14, 15, 21} : Finset ℕ)) :
    Y0HasNoRationalPoint (p * q) := by
  obtain ⟨Y, strY, ⟨hc⟩⟩ := exists_coarseModuliY0 (p * q)
  obtain ⟨X, strX, ⟨hX⟩⟩ := exists_compactificationY0 hc
  exact y0HasNoRationalPoint_of_cuspidal hc hX
    (cuspidal_x0_semiprime_of_mazurPrimes hp hq hpq hpm hqm hmem hc hX)

/-! ### The compactification `X_0(N)`, its cusps, and `J_0(N)`

`Y_0(N)(ℚ) = ∅` cannot be proved on the affine curve alone.  The
classical route bounds the rational points of the **compactification**:
`rank J_0(N)(ℚ) = 0` makes `J_0(N)(ℚ)` finite, hence `X_0(N)(ℚ)` injects
into `X_0(N)(𝔽_ℓ)` for a good odd prime `ℓ`; and `Y_0(N)(ℚ) = ∅` follows
only when that count is already exhausted by points known to be rational
— the **cusps**, which live in `X_0(N) ∖ Y_0(N)`.  So the step from
*finite* to *empty* IS the cusp count, and any criterion phrased over
`Y_0(N)` alone would have to assume it as a hypothesis equivalent to its
own conclusion.

This subsection therefore builds, in the order that observation forces:

1. `IsX0Compactification` — `Y_0(N) ⊆ X_0(N)` as an open subscheme of a
   smooth proper curve with finite complement;
2. `IsJacobianOf` and `HasRankZeroJacobian` — `J_0(N)` by its Albanese
   universal property, and the two arithmetic inputs;
3. `card_le_of_rankZeroJacobian` — the reduction bound;
4. `y0HasNoRationalPoint_of_witnessPrime` — the assembly, PROVEN, and
   what the seven single-prime levels below call.

The arithmetic that feeds it is the Magma reconnaissance recorded in the
`#### Reconnaissance` block below. -/

/-- **`Spec 𝔽_ℓ`**, the base over which a modular curve is reduced.

`ℓ` is not asked to be prime here — primality is a hypothesis where it
matters, in `card_le_of_rankZeroJacobian`. -/
noncomputable abbrev SpecF (ℓ : ℕ) : Scheme.{0} := Spec (CommRingCat.of (ZMod ℓ))

/-- **A section of `Y` pushed into `X`.**  If `j : Y ⟶ X` is a morphism
over `S`, a section of `strY` composed with `j` is a section of `strX`.
For `S = Spec ℚ` and `j` the open immersion `Y_0(N) ⊆ X_0(N)` this is
the inclusion `Y_0(N)(ℚ) → X_0(N)(ℚ)`. -/
def sectionAlong {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S} (j : Y ⟶ X)
    (hj : j ≫ strX = strY) (y : RelPoint strY (𝟙 S)) : RelPoint strX (𝟙 S) :=
  ⟨y.1 ≫ j, by rw [Category.assoc, hj, y.2]⟩

/-- **The number of `ℚ`-rational cusps of `X_0(N)`.**

The cusps of `X_0(N)` are indexed by pairs `(d, a)` with `d ∣ N` and
`a ∈ (ℤ/gcd(d, N/d))ˣ`, and `Γ_ℚ` permutes the `φ(gcd(d, N/d))` cusps
above a given `d` transitively, through the cyclotomic character of
`ℚ(ζ_{gcd(d, N/d)})`.  So the cusps above `d` are rational exactly when
`φ(gcd(d, N/d)) = 1`, and this is the number of such divisors.

The TOTAL number of cusps is `∑_{d ∣ N} φ(gcd(d, N/d))`, which is
strictly larger at two of the seven levels below — `12` against `6` at
`N = 36`, and `12` against `4` at `N = 50`.  Counting against the total
rather than against the rational count would make the level statements
unprovable there, and is the trap this definition exists to avoid.

Values consumed below, each by `decide`:
`20 ↦ 6`, `24 ↦ 8`, `28 ↦ 6`, `30 ↦ 8`, `36 ↦ 6`, `42 ↦ 8`, `50 ↦ 4`. -/
def numRationalCusps (N : ℕ) : ℕ :=
  (N.divisors.filter fun d => Nat.totient (Nat.gcd d (N / d)) = 1).card

/-- **`strX : X ⟶ S` is the smooth compactification of the coarse moduli
space `strY : Y ⟶ S`, with `j : Y ⟶ X` the open immersion.**

`X` is proper and smooth of relative dimension `1` over `S`,
geometrically connected, and contains `Y` as an open subscheme with
FINITE complement — that complement is the cusp locus.

This pins `X` as the genuine `X_0(N)`: `Y` is pinned up to unique
isomorphism by the initiality clause carried in the `coarse` field, a
nonempty open of a connected curve is dense, and a smooth proper curve
containing a given smooth curve as a dense open is its unique smooth
compactification.  Dropping `finite_compl` would break exactly that —
`X` could then be any curve receiving `Y`, with the cusp count
meaningless.

The base `S` is general on purpose: the same structure over `Spec 𝔽_ℓ`
with `ℓ ∤ N` is the good reduction `X_0(N)_{𝔽_ℓ}`, and
`card_le_of_rankZeroJacobian` relates the two. -/
structure IsX0Compactification (N : ℕ) {X Y S : Scheme.{0}} (strX : X ⟶ S)
    (strY : Y ⟶ S) (j : Y ⟶ X) where
  /-- `j` is a morphism over the base -/
  comm : j ≫ strX = strY
  /-- `Y` is a coarse moduli space for the `Γ₀(N)`-problem -/
  coarse : IsCoarseModuliY0 N strY
  /-- `Y` is an open subscheme of `X` -/
  isOpen : IsOpenImmersion j
  /-- `X` is proper over the base -/
  isProper : IsProper strX
  /-- `X` is a smooth curve over the base -/
  smooth : SmoothOfRelativeDimension 1 strX
  /-- `X` is geometrically connected -/
  connected : GeometricallyConnected strX
  /-- the complement of `Y` in `X` — the cusp locus — is finite -/
  finite_compl : (Set.range j.base)ᶜ.Finite

/-- **`ab` is the Jacobian of the curve `strX`, based at `o`.**

Stated by the Albanese universal property, in the same
functor-of-points style as `IsCoarseModuliY0`: the Abel–Jacobi map
`x ↦ [x] − [o]` is a natural transformation from the points of `X` to
the points of an abelian scheme sending `o` to `0`, and it is INITIAL
among all such.  For a smooth proper geometrically connected curve the
Albanese variety with a base point is exactly the Jacobian, so this
determines `(J, aj)` up to unique isomorphism — which is what makes
`HasRankZeroJacobian` a statement about `J_0(N)` rather than about some
arbitrary abelian scheme that happens to receive `X(ℚ)`.

Note what is deliberately NOT a field here: injectivity of `aj` on
points.  It holds exactly when the genus is positive — for genus `0` the
Jacobian is trivial — so it is an independent condition, and it is
carried explicitly by `HasRankZeroJacobian` instead. -/
structure IsJacobianOf {X J S : Scheme.{0}} (strX : X ⟶ S) {jstr : J ⟶ S}
    (ab : AbelianSchemeStruct jstr) (o : RelPoint strX (𝟙 S)) where
  /-- the Abel–Jacobi map `x ↦ [x] − [o]` on relative points -/
  aj : ∀ {T : Scheme.{0}} (g : T ⟶ S), RelPoint strX g → RelPoint jstr g
  /-- the Abel–Jacobi map is natural -/
  aj_pre : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (x : RelPoint strX g),
    aj g' (RelPoint.pre h hg x) = RelPoint.pre h hg (aj g x)
  /-- the base point is sent to the origin -/
  aj_base : aj (𝟙 S) o = ab.zero (𝟙 S)
  /-- `(J, aj)` is initial among abelian schemes under `X` -/
  universal : ∀ {A : Scheme.{0}} {astr : A ⟶ S} (ab' : AbelianSchemeStruct astr)
    (c : ∀ {T : Scheme.{0}} (g : T ⟶ S), RelPoint strX g → RelPoint astr g),
    (∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
      (hg : h ≫ g = g') (x : RelPoint strX g),
      c g' (RelPoint.pre h hg x) = RelPoint.pre h hg (c g x)) →
    c (𝟙 S) o = ab'.zero (𝟙 S) →
    ∃! u : J ⟶ A, u ≫ astr = jstr ∧
      ∀ {T : Scheme.{0}} (g : T ⟶ S) (x : RelPoint strX g),
        (c g x).1 = (aj g x).1 ≫ u

/-- **`rank J_0(N)(ℚ) = 0`, together with `genus X_0(N) ≥ 1`.**

The two arithmetic inputs of the reduction argument, packaged as one
existential over the Jacobian because both are statements about it:

* `J(ℚ)` is FINITE — for an abelian variety over a number field the
  Mordell–Weil group is finitely generated, so finiteness is exactly
  rank `0`;
* the Abel–Jacobi map is INJECTIVE on rational points, which is
  positivity of the genus.

The second is not decoration.  Without it the reduction criterion below
is FALSE: at `N = 1` the curve `X_0(1) = ℙ¹` has trivial Jacobian, hence
finite `J(ℚ)`, and infinitely many rational points.

Both hold at all eleven Kenku levels — see
`hasRankZeroJacobian_of_kenkuLevel`. -/
def HasRankZeroJacobian {X : Scheme.{0}} (strX : X ⟶ SpecQ) : Prop :=
  ∃ (J : Scheme.{0}) (jstr : J ⟶ SpecQ) (ab : AbelianSchemeStruct jstr)
    (o : RelPoint strX (𝟙 SpecQ)) (jac : IsJacobianOf strX ab o),
    Finite (RelPoint jstr (𝟙 SpecQ)) ∧ Function.Injective (jac.aj (𝟙 SpecQ))

/-- **The eleven levels of Kenku's non-prime-power determination**, i.e.
the eleven named level nodes below.  All eleven have
`rank J_0(N)(ℚ) = 0`; seven of them additionally have a single witness
prime (`x0WitnessTable`), and the remaining four — `45, 54, 63, 75` —
need a multi-prime Mordell–Weil sieve. -/
def kenkuLevels : List ℕ := [20, 24, 28, 30, 36, 42, 45, 50, 54, 63, 75]

/-- **The witness table `(N, ℓ, #X_0(N)(𝔽_ℓ))` for the seven levels that
close on a single prime.**

Computed with Magma from Eichler–Shimura,
`#X_0(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`; see the
`#### Reconnaissance` block below for the full table with genus and
cusp data.  In every row the count EQUALS `numRationalCusps N`, which is
precisely why these seven close on one prime.

Two entries are traps for anyone regenerating this table.  `N = 30`
needs `ℓ = 17`: the small primes `7, 11, 13` give `12, 20, 16`, all
strictly larger than `8`.  And `N = 36`, `N = 50` must be counted
against their RATIONAL cusps (`6` and `4`), not against their `12`
cusps. -/
def x0WitnessTable : List (ℕ × ℕ × ℕ) :=
  [(20, 3, 6), (24, 5, 8), (28, 5, 6), (30, 17, 8), (36, 5, 6), (42, 11, 8), (50, 3, 4)]

/-- **Existence of the compactified coarse moduli space `X_0(N)` over
`ℚ`** (sorry node).

TRUE and classical: `Y_0(N)` is a smooth affine curve over `ℚ` and every
smooth curve over a field has a unique smooth projective
compactification; for `Y_0(N)` it is the modular curve `X_0(N)` of
Deligne–Rapoport, obtained directly as the coarse space of the moduli
problem of GENERALISED elliptic curves with `Γ₀(N)`-structure, the added
points being the cusps.

This leaf SUBSUMES `exists_coarseModuliY0` — its `coarse` field is
exactly that statement — so a successor closing that node has closed
half of this one; what remains is the compactification proper.

IRREDUCIBLE at this pin for the same reason as `exists_coarseModuliY0`:
neither modular curves nor a smooth-compactification theorem for curves
exists anywhere in `Mathlib`. -/
theorem exists_x0Compactification (N : ℕ) (hN : 0 < N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecQ) (strY : Y ⟶ SpecQ) (j : Y ⟶ X),
      Nonempty (IsX0Compactification N strX strY j) :=
  sorry

/-- **`X_0(N)` has `numRationalCusps N` rational cusps, and no cusp is
the image of a rational point of `Y_0(N)`** (sorry node).

TRUE and classical; see `numRationalCusps` for the divisor count and the
Galois action on the cusps.  The second conjunct is immediate from the
definition of a cusp — it lies in `X ∖ Y` — but it is exactly what the
emptiness argument consumes, so it is stated rather than left implicit.

Quantified over every compactification rather than over a chosen one:
`IsX0Compactification` pins `(X, Y, j)` up to isomorphism so the
statement is invariant, and `exists_x0Compactification` supplies an
instance so it is not vacuous.

IRREDUCIBLE at this pin: the cusps of `X_0(N)` do not exist here in any
form. -/
theorem exists_rationalCusps (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {j : Y ⟶ X} (h : IsX0Compactification N strX strY j) :
    ∃ s : Finset (RelPoint strX (𝟙 SpecQ)), s.card = numRationalCusps N ∧
      ∀ p ∈ s, ∀ y : RelPoint strY (𝟙 SpecQ), sectionAlong j h.comm y ≠ p :=
  sorry

/-- **`rank J_0(N)(ℚ) = 0` and `genus X_0(N) ≥ 1` at the eleven Kenku
levels** (sorry node).

TRUE, by the reconnaissance recorded below: decomposing the cuspidal
subspace `S_2(Γ_0(N))` into newform factors and evaluating `L(A, 1)` on
each, EVERY factor at EVERY one of the eleven levels has `L(A, 1) ≠ 0`;
so `J_0(N)` has analytic rank `0`, hence Mordell–Weil rank `0` by
Kolyvagin–Logachev, hence finite `J_0(N)(ℚ)`.  Positivity of the genus
is classical and holds at all eleven — the genus values, in the order of
`kenkuLevels`, are `1, 1, 2, 3, 1, 5, 3, 2, 4, 5, 5`.

IRREDUCIBLE at this pin, and the deepest of the six leaves here: it
needs `S_2(Γ_0(N))`, the Hecke algebra, `L`-functions of modular abelian
varieties and Gross–Zagier/Kolyvagin. -/
theorem hasRankZeroJacobian_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) : HasRankZeroJacobian strX :=
  sorry

/-- **The reduction `X_0(N)_{𝔽_ℓ}` and its Eichler–Shimura point count,
at the seven witness primes** (sorry node).

TRUE: for `ℓ ∤ N` the modular curve has good reduction at `ℓ` and its
special fibre is the coarse space of the same `Γ₀(N)`-problem over
`𝔽_ℓ`; being proper over a finite field it has finitely many rational
points; and Eichler–Shimura evaluates the count as
`ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`.  The seven rows of `x0WitnessTable` are
that formula computed with Magma.

IRREDUCIBLE at this pin: neither the integral model of `X_0(N)`, nor its
reduction, nor the Hecke operators exist here. -/
theorem exists_x0Compactification_mod_prime (N ℓ m : ℕ)
    (h : (N, ℓ, m) ∈ x0WitnessTable) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecF ℓ) (strY : Y ⟶ SpecF ℓ) (j : Y ⟶ X),
      Nonempty (IsX0Compactification N strX strY j) ∧
        Finite (RelPoint strX (𝟙 (SpecF ℓ))) ∧
        Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) = m :=
  sorry

/-- **The rank-`0` reduction bound, `#X_0(N)(ℚ) ≤ #X_0(N)(𝔽_ℓ)`** (sorry
node — this is the criterion).

TRUE, and classical.  `hJ` makes `J_0(N)(ℚ)` finite, hence torsion; for
`ℓ` an odd prime of good reduction the reduction map on torsion
`J_0(N)(ℚ) → J_0(N)(𝔽_ℓ)` is INJECTIVE, its kernel being the points of a
formal group over `ℤ_ℓ`, which is torsion-free for `ℓ` odd; Abel–Jacobi
based at a rational point embeds `X_0(N)(ℚ)` into `J_0(N)(ℚ)` and
commutes with reduction; so `X_0(N)(ℚ)` injects into `X_0(N)(𝔽_ℓ)`.

**Every hypothesis is load-bearing**, and the leaf is false without any
one of them — which is why none is trimmed:

* without finiteness in `hJ`, a positive-rank Jacobian gives infinitely
  many rational points already in genus `1`;
* without injectivity in `hJ`, `N = 1` refutes it: `X_0(1) = ℙ¹` has
  trivial Jacobian and infinitely many rational points;
* without `hℓ2` the formal-group argument fails at `ℓ = 2`, where
  `2`-torsion can die under reduction;
* without `hℓN` there is no good reduction at `ℓ` and the special fibre
  is not a smooth curve.

The conclusion bounds every `Finset` of rational points rather than
`Nat.card`, because `Nat.card` of an infinite type is `0` and the bound
would then hold vacuously; the `Finset` form also carries finiteness.

IRREDUCIBLE at this pin: it needs the integral model of `X_0(N)`, the
reduction map on the Jacobian, and the formal group of an abelian
scheme. -/
theorem card_le_of_rankZeroJacobian {N : ℕ} {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {j : Y ⟶ X} (hX : IsX0Compactification N strX strY j)
    (hJ : HasRankZeroJacobian strX) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓN : ¬ ℓ ∣ N) {X' Y' : Scheme.{0}} {strX' : X' ⟶ SpecF ℓ}
    {strY' : Y' ⟶ SpecF ℓ} {j' : Y' ⟶ X'}
    (hX' : IsX0Compactification N strX' strY' j') (m : ℕ)
    (hfin : Finite (RelPoint strX' (𝟙 (SpecF ℓ))))
    (hm : Nat.card (RelPoint strX' (𝟙 (SpecF ℓ))) = m)
    (s : Finset (RelPoint strX (𝟙 SpecQ))) : s.card ≤ m :=
  sorry

/-- **The single-prime criterion** (PROVEN): at a level whose Jacobian
has rank `0`, and which has a witness prime whose point count equals the
number of rational cusps, `Y_0(N)(ℚ) = ∅`.

The argument is pure counting, and it is the reason the interface above
is shaped as it is.  Take the compactification `Y ⊆ X` over `ℚ` and the
reduction `X'` over `𝔽_ℓ`.  The `c = numRationalCusps N` rational cusps
are `c` distinct rational points of `X`, none of them the image of a
rational point of `Y`.  A rational point of `Y` would therefore push
forward to a `(c+1)`-st one, giving a `Finset` of `X(ℚ)` of size
`c + 1`; but the reduction bound caps every such `Finset` by
`#X'(𝔽_ℓ) = c`.  So `Y(ℚ)` is empty — and
`y0HasNoRationalPoint_of_isEmpty` propagates that to every coarse moduli
space at once.

This is exactly the step that cannot be taken on the affine curve: rank
`0` bounds `#X_0(N)(ℚ)`, and only the cusp count turns that bound into
emptiness of `Y_0(N)(ℚ)`. -/
theorem y0HasNoRationalPoint_of_witnessPrime (N ℓ : ℕ) (hN : 0 < N)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓN : ¬ ℓ ∣ N) (hlevel : N ∈ kenkuLevels)
    (htable : (N, ℓ, numRationalCusps N) ∈ x0WitnessTable) :
    Y0HasNoRationalPoint N := by
  classical
  obtain ⟨X, Y, strX, strY, j, ⟨hX⟩⟩ := exists_x0Compactification N hN
  obtain ⟨X', Y', strX', strY', j', ⟨hX'⟩, hfin, hcard⟩ :=
    exists_x0Compactification_mod_prime N ℓ (numRationalCusps N) htable
  obtain ⟨s, hscard, hsnot⟩ := exists_rationalCusps N hX
  refine y0HasNoRationalPoint_of_isEmpty hX.coarse ⟨fun y => ?_⟩
  have hp : sectionAlong j hX.comm y ∉ s := fun hmem => hsnot _ hmem y rfl
  have hle : (insert (sectionAlong j hX.comm y) s).card ≤ numRationalCusps N :=
    card_le_of_rankZeroJacobian hX (hasRankZeroJacobian_of_kenkuLevel N hlevel hX)
      hℓ hℓ2 hℓN hX' _ hfin hcard _
  rw [Finset.card_insert_of_notMem hp, hscard] at hle
  omega

/-! #### The multi-prime Mordell–Weil sieve

The four levels `45, 54, 63, 75` are exactly those at which the counting
bound of `card_le_of_rankZeroJacobian` is never sharp: at every odd
`ℓ ∤ N` the reduction `X_0(N)(𝔽_ℓ)` has strictly more points than
`X_0(N)` has rational cusps, so `y0HasNoRationalPoint_of_witnessPrime`
cannot close them however the prime is chosen.  The minima over
`3 ≤ ℓ < 60`, recomputed with Magma on 2026-07-26 from Eichler–Shimura,
against `numRationalCusps N = 4` in all four cases:

| `N` | genus | best `ℓ₁` | `#X_0(N)(𝔽_{ℓ₁})` | `#J_0(N)(𝔽_{ℓ₁})` | `ℓ₂` | `#J_0(N)(𝔽_{ℓ₂})` | `gcd` |
|-----|-------|-----------|--------------------|--------------------|------|--------------------|-------|
| 45 | 3 | 7 | 8 | `512 = 2⁹`        | 19 | `4096 = 2¹²`          | `512`  |
| 54 | 4 | 5 | 6 | `972 = 2²·3⁵`     | 7  | `6561 = 3⁸`           | `243`  |
| 63 | 5 | 5 | 8 | `6144 = 2¹¹·3`    | 11 | `135168 = 2¹²·3·11`   | `6144` |
| 75 | 5 | 7 | 8 | `28160 = 2⁹·5·11` | 11 | `409600 = 2¹⁴·5²`     | `2560` |

**What the extra primes buy, and why only one of them appears in the
statement below.**  Reduction at a good odd `ℓ` is an injective group
homomorphism `J_0(N)(ℚ) → J_0(N)(𝔽_ℓ)`, so by Lagrange `#J_0(N)(ℚ)`
divides `#J_0(N)(𝔽_ℓ)` for every such `ℓ`; ranging over several `ℓ` pins
`#J_0(N)(ℚ)` down to a divisor of the `gcd` above.  That is the whole
arithmetic content of "multi-prime", and it is a statement about the
subgroup `red_ℓ(J_0(N)(ℚ)) ⊆ J_0(N)(𝔽_ℓ)`.

So the sieve leaf is phrased over ONE prime, with the surviving points
cut out by membership in `Set.range red.redJ` rather than by a divisibility
condition on their order.  That is deliberate and it is the *stronger*
formulation: `Set.range red.redJ` is an isomorphic copy of `J_0(N)(ℚ)`
itself, so it already encodes everything that any number of auxiliary
primes could contribute *to the group*, and no bound `D` has to be
carried around and justified separately.  `N = 75` is the row that shows
why this matters — its best counting prime `ℓ₁ = 7` gives
`#J_0(75)(𝔽_7) = 11 · 2560`, so even the *order* of the rational Jacobian
is not pinned there without a second prime.

**Correction, 2026-07-26: that argument is sound but it does NOT by
itself justify the single prime, and the reason the single prime is
nevertheless right is a different one.**  Pinning the group is not what
the multi-prime sieve does.  The classical sieve intersects, over several
`ℓ`, the conditions `red_ℓ(x) ∈ (aj'_ℓ)⁻¹(red_ℓ J_0(N)(ℚ))`; a point of
`X_0(N)(𝔽_{ℓ₁})` that survives at `ℓ₁` may be killed only by a *different*
prime, and no amount of information about `Set.range red.redJ` at `ℓ₁`
sees that.  So "the range encodes what the auxiliary primes say" answers
a question about `#J_0(N)(ℚ)` and leaves the sieve question open.

What actually makes the one-prime formulation true is that `ℓ` is
**existentially quantified over all of `ℕ`**: the leaf has only to find
ONE prime at which the single-prime cut is already sharp, and for a curve
of genus `g ≥ 2` that is what happens at every sufficiently large `ℓ`.
There `#X_0(N)(𝔽_ℓ)` grows like `ℓ + 1` while `#J_0(N)(𝔽_ℓ)` grows like
`ℓ^g`, so the FIXED finite subgroup `red_ℓ J_0(N)(ℚ)` — of order at most
`512, 243, 6144, 2560` — meets the `ℓ + 1` Abel–Jacobi classes only in
the ones it is forced to contain, namely the reductions of `X_0(N)(ℚ)`.
All four sieve levels have `g ≥ 3`.  The existential is therefore not a
hedge against a numerical accident at a small prime; it is the load-
bearing part of the statement, and the small primes of the table are the
*hard* case rather than the easy one.

The leaf is restricted to `x0SieveLevels` on purpose.  Stated for all of
`kenkuLevels` it would subsume `exists_x0Compactification_mod_prime` and
`card_le_of_rankZeroJacobian` — the seven single-prime levels would then
rest on a strictly stronger unproven statement than they need, which is
the "repackaging the consumer" failure this module's interfaces are
shaped to avoid. -/

/-- **The four Kenku levels that no single counting prime settles.**

A sublist of `kenkuLevels`; the other seven are closed by
`y0HasNoRationalPoint_of_witnessPrime` against `x0WitnessTable`.  See the
table in the subsection docstring for the arithmetic that separates the
two groups. -/
def x0SieveLevels : List ℕ := [45, 54, 63, 75]

/-- **Good reduction of the pair `(X_0(N), J_0(N))` at an odd prime
`ℓ ∤ N`, on rational points.**

The data is the commuting square

```
X_0(N)(ℚ)  --aj-->  J_0(N)(ℚ)
   | redX               | redJ
   v                    v
X_0(N)(𝔽_ℓ) --aj'--> J_0(N)(𝔽_ℓ)
```

with `redJ` an INJECTIVE group homomorphism.  Injectivity is not an
axiom about reduction in general — it is the rank-`0` input: `J_0(N)(ℚ)`
is finite, hence torsion, and the kernel of reduction on torsion is the
group of points of a formal group over `ℤ_ℓ`, torsion-free for `ℓ` odd.
It is the same fact that `card_le_of_rankZeroJacobian` rests on, isolated
here as data so that the sieve can speak about the SUBGROUP
`Set.range redJ ≅ J_0(N)(ℚ)` of `J_0(N)(𝔽_ℓ)` rather than only about its
cardinality.

`redJ_add` is what makes that range a subgroup, and hence what makes
"`#J_0(N)(ℚ)` divides `#J_0(N)(𝔽_ℓ)` for every good `ℓ`" — the mechanism
by which the auxiliary primes cut the search space down — a consequence
of this structure rather than a separate assumption.  The counting
argument in `card_le_of_sieve` does not need it, but a `redJ` without it
would not deserve the name reduction. -/
structure IsX0ReductionAt {X J X' J' : Scheme.{0}} {strX : X ⟶ SpecQ}
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {ℓ : ℕ} {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    (jac : IsJacobianOf strX ab o) (jac' : IsJacobianOf strX' ab' o') where
  /-- reduction of rational points of the curve -/
  redX : RelPoint strX (𝟙 SpecQ) → RelPoint strX' (𝟙 (SpecF ℓ))
  /-- reduction of rational points of the Jacobian -/
  redJ : RelPoint jstr (𝟙 SpecQ) → RelPoint jstr' (𝟙 (SpecF ℓ))
  /-- reduction is a homomorphism on the Jacobian -/
  redJ_add : ∀ x y : RelPoint jstr (𝟙 SpecQ),
    redJ (ab.add x y) = ab'.add (redJ x) (redJ y)
  /-- reduction is injective on the rational points of a rank-`0` Jacobian -/
  redJ_inj : Function.Injective redJ
  /-- reduction commutes with Abel–Jacobi -/
  red_aj : ∀ x : RelPoint strX (𝟙 SpecQ),
    redJ (jac.aj (𝟙 SpecQ) x) = jac'.aj (𝟙 (SpecF ℓ)) (redX x)

/-! #### The integral model, and the Néron pinning of `redJ`

The subsection above records that `exists_x0Sieve` does not decompose
*because* `IsX0ReductionAt` leaves `redJ` unpinned, and that the cut
becomes safe exactly when `redJ` is pinned as the map induced by Néron
models over `ℤ_ℓ`.  This subsection builds that pinning, and the cut is
taken below: `exists_x0Sieve` is PROVEN from three leaves, none of which
is the whole of Kenku's determination.

The base is `Spec` of the local ring of `ℤ` at `ℓ`, and the pinning of
that base is what carries the whole construction — a junk base would let
a junk special fibre back in, and since the sharpness leaf quantifies
UNIVERSALLY over data, one junk datum would make it FALSE rather than
merely weak.  `IsReductionBase` pins it with two conditions and no
imports; see its docstring.
-/

/-- **The local ring of `ℤ` at `ℓ`, pinned by two conditions.**

`R` is a subring of `ℚ` and `toF : R → 𝔽_ℓ` a ring map which is
surjective and whose kernel is exactly the set of non-units.  That is all
that is needed, and it pins `(R, toF)` completely:

* the kernel of a ring map is an ideal, so "kernel = non-units" says `R`
  is LOCAL with maximal ideal `ker toF`;
* every subring of `ℚ` contains `ℤ` and therefore has fraction field
  `ℚ`, so no separate fraction-field condition is required;
* the subrings of `ℚ` are the localizations `ℤ[S⁻¹]`, and the local ones
  are `ℚ` itself and the `ℤ_(p)`.  There is no ring map `ℚ → 𝔽_ℓ` at all
  (`ℓ` is a unit in `ℚ` but `toF ℓ = 0`, and `0` is not a unit unless
  `𝔽_ℓ` is trivial, which the kernel condition excludes since `1` is a
  unit).  Hence `R = ℤ_(ℓ)`.
* `R / ker toF ≅ 𝔽_ℓ` is then a field, so `ℓ` is PRIME — this is a
  consequence, not a hypothesis;
* and `toF` itself is pinned, because the induced iso `R/m ≅ 𝔽_ℓ` is a
  field automorphism of `𝔽_ℓ`, of which there is only the identity.

So `IsReductionBase ℓ R toF` says "`R` is `ℤ_(ℓ)` and `toF` is reduction
mod `ℓ`", in a form that needs no `IsDiscreteValuationRing`,
`IsFractionRing` or `IsLocalRing` instance and hence no new import. -/
structure IsReductionBase (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ) : Prop where
  /-- `𝔽_ℓ` is the residue field -/
  surjective : Function.Surjective toF
  /-- the kernel is the maximal ideal, i.e. `R` is local with residue field `𝔽_ℓ` -/
  ker_eq_nonunits : ∀ r : R, toF r = 0 ↔ ¬ IsUnit r

/-- **`Spec` of the base**, the local ring of `ℤ` at `ℓ` once
`IsReductionBase` holds of `R`.  Written for an arbitrary subring of `ℚ`
so that the ring is a TERM and can be quantified over without
existentials in instance position. -/
noncomputable abbrev SpecLoc (R : Subring ℚ) : Scheme.{0} := Spec (CommRingCat.of R)

/-- **The generic point `Spec ℚ ⟶ Spec ℤ_(ℓ)`**, induced by the inclusion
`R ⊆ ℚ`. -/
noncomputable def SpecLoc.generic (R : Subring ℚ) : SpecQ ⟶ SpecLoc R :=
  Spec.map (CommRingCat.ofHom R.subtype)

/-- **The closed point `Spec 𝔽_ℓ ⟶ Spec ℤ_(ℓ)`**, induced by reduction. -/
noncomputable def SpecLoc.special {ℓ : ℕ} {R : Subring ℚ} (toF : R →+* ZMod ℓ) :
    SpecF ℓ ⟶ SpecLoc R :=
  Spec.map (CommRingCat.ofHom toF)

/-- **A Néron-pinned reduction datum for `X_0(N)` at `ℓ`.**

This is `IsX0ReductionAt` with `redJ` no longer free: instead of positing
a map with three properties, the datum carries the INTEGRAL MODELS over
`ℤ_(ℓ)` and reads `redX`, `redJ` off them.  All three properties of
`IsX0ReductionAt` are then theorems (`redJ_add`, `red_aj` here;
`redJ_inj` from `neronReduction_injective`), assembled by `toReduction`.

The data:

* `base` pins the base as `Spec ℤ_(ℓ)` — see `IsReductionBase`;
* `model` pins the integral curve as the smooth model of `X_0(N)` over
  that base, reusing `IsX0Compactification`, whose base was left general
  for exactly this purpose.  For `ℓ ∤ N` this is the Deligne–Rapoport /
  Igusa smooth model;
* `jacZ` pins the integral Jacobian as its relative Jacobian;
* `genX`, `genJ`, `spX`, `spJ` identify the two fibres.  They are stated
  as equivalences of FUNCTORS of points — for every `T` and every base
  point, natural in the "identified base" form used throughout this file
  — so by Yoneda they say `X ≅ 𝒳 ×_{ℤ_(ℓ)} ℚ` and `X' ≅ 𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ`,
  and likewise for the Jacobians, rather than merely comparing point
  sets;
* `genJ_add`, `spJ_add`, `genX_aj`, `spX_aj` say those identifications
  respect the group law and Abel–Jacobi, i.e. that `aj` is defined over
  the base;
* `neronJ` is the **Néron mapping property** in section form,
  `𝒥(ℤ_(ℓ)) ≅ J(ℚ)`, and `properX` is the **valuative criterion of
  properness** for the curve, `𝒳(ℤ_(ℓ)) ≅ X(ℚ)`.  These are what turn a
  rational point into an integral one, which is the only reason a
  reduction map exists at all.

**Why the pinning is the load-bearing part.**  With it, the pair
`(X', J', aj', Set.range redJ)` is determined up to isomorphism by `N`
and `ℓ`: the smooth proper model over `ℤ_(ℓ)` is unique, so its special
fibre is, and `redJ` is the genuine reduction rather than an arbitrary
injective homomorphism.  That is precisely what makes
`exists_sharpSievePrime` — which quantifies universally over data —
a true statement rather than the false one the subsection above warned
about. -/
structure IsX0NeronDatum (N ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    {X J X' J' XZ YZ JZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    (jac : IsJacobianOf strX ab o) (jac' : IsJacobianOf strX' ab' o')
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} (jacZ : IsJacobianOf xstr abZ oZ) where
  /-- the base is the local ring of `ℤ` at `ℓ` -/
  base : IsReductionBase ℓ R toF
  /-- the integral model is the smooth model of `X_0(N)` over that base -/
  model : IsX0Compactification N xstr ystr jZ
  /-- the generic fibre of the curve model is `X`, functorially -/
  genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀
  /-- the generic fibre of the Jacobian model is `J`, functorially -/
  genJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint jstr g ≃ RelPoint jstrZ g₀
  /-- the special fibre of the curve model is `X'`, functorially -/
  spX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint strX' g ≃ RelPoint xstr g₀
  /-- the special fibre of the Jacobian model is `J'`, functorially -/
  spJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint jstr' g ≃ RelPoint jstrZ g₀
  /-- naturality of the generic identification of curves -/
  genX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strX g),
    genX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genX g g₀ h₀ x)
  /-- naturality of the generic identification of Jacobians -/
  genJ_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint jstr g),
    genJ g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genJ g g₀ h₀ x)
  /-- naturality of the special identification of curves -/
  spX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF ℓ} {g' : T' ⟶ SpecF ℓ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint strX' g),
    spX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spX g g₀ h₀ x)
  /-- naturality of the special identification of Jacobians -/
  spJ_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF ℓ} {g' : T' ⟶ SpecF ℓ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint jstr' g),
    spJ g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spJ g g₀ h₀ x)
  /-- the generic identification of Jacobians is additive -/
  genJ_add : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (x y : RelPoint jstr g),
    genJ g g₀ h (ab.add x y) = abZ.add (genJ g g₀ h x) (genJ g g₀ h y)
  /-- the special identification of Jacobians is additive -/
  spJ_add : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀) (x y : RelPoint jstr' g),
    spJ g g₀ h (ab'.add x y) = abZ.add (spJ g g₀ h x) (spJ g g₀ h y)
  /-- Abel–Jacobi is defined over the base: generic fibre -/
  genX_aj : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (x : RelPoint strX g),
    genJ g g₀ h (jac.aj g x) = jacZ.aj g₀ (genX g g₀ h x)
  /-- Abel–Jacobi is defined over the base: special fibre -/
  spX_aj : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀) (x : RelPoint strX' g),
    spJ g g₀ h (jac'.aj g x) = jacZ.aj g₀ (spX g g₀ h x)
  /-- **Néron mapping property**: every rational point of `J` extends
  uniquely to an integral point of the model -/
  neronJ : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint jstrZ (𝟙 (SpecLoc R)) → RelPoint jstrZ (SpecLoc.generic R))
  /-- **valuative criterion of properness**: every rational point of `X`
  extends uniquely to an integral point of the model -/
  properX : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint xstr (𝟙 (SpecLoc R)) → RelPoint xstr (SpecLoc.generic R))

namespace IsX0NeronDatum

variable {N ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X J X' J' XZ YZ JZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    {jac : IsJacobianOf strX ab o} {jac' : IsJacobianOf strX' ab' o'}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} {jacZ : IsJacobianOf xstr abZ oZ}
    (d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ)

/-- **The integral point of the Jacobian model** attached to a rational
point, by the Néron mapping property. -/
noncomputable def intJ (x : RelPoint jstr (𝟙 SpecQ)) : RelPoint jstrZ (𝟙 (SpecLoc R)) :=
  (Equiv.ofBijective _ d.neronJ).symm
    (d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) x)

/-- **The integral point of the curve model** attached to a rational
point, by the valuative criterion of properness. -/
noncomputable def intX (x : RelPoint strX (𝟙 SpecQ)) : RelPoint xstr (𝟙 (SpecLoc R)) :=
  (Equiv.ofBijective _ d.properX).symm
    (d.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) x)

/-- **Reduction of rational points of the Jacobian**: extend to the
integral model, then restrict to the special fibre. -/
noncomputable def redJ (x : RelPoint jstr (𝟙 SpecQ)) : RelPoint jstr' (𝟙 (SpecF ℓ)) :=
  (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
    (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ x))

/-- **Reduction of rational points of the curve.** -/
noncomputable def redX (x : RelPoint strX (𝟙 SpecQ)) : RelPoint strX' (𝟙 (SpecF ℓ)) :=
  (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
    (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intX x))

theorem redJ_def (x : RelPoint jstr (𝟙 SpecQ)) :
    d.redJ x = (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ x)) := rfl

theorem redX_def (x : RelPoint strX (𝟙 SpecQ)) :
    d.redX x = (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intX x)) := rfl

theorem pre_intJ (z : RelPoint jstr (𝟙 SpecQ)) :
    RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) (d.intJ z)
      = d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) z :=
  (Equiv.ofBijective _ d.neronJ).apply_symm_apply _

theorem pre_intX (z : RelPoint strX (𝟙 SpecQ)) :
    RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) (d.intX z)
      = d.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) z :=
  (Equiv.ofBijective _ d.properX).apply_symm_apply _

/-- Extending a rational point to the integral model is additive. -/
theorem intJ_add (x y : RelPoint jstr (𝟙 SpecQ)) :
    d.intJ (ab.add x y) = abZ.add (d.intJ x) (d.intJ y) := by
  apply d.neronJ.1
  rw [d.pre_intJ, abZ.pre_add, d.pre_intJ, d.pre_intJ, d.genJ_add]

/-- Extending a rational point to the integral model commutes with
Abel–Jacobi. -/
theorem intJ_aj (x : RelPoint strX (𝟙 SpecQ)) :
    d.intJ (jac.aj (𝟙 SpecQ) x) = jacZ.aj (𝟙 (SpecLoc R)) (d.intX x) := by
  apply d.neronJ.1
  rw [d.pre_intJ, d.genX_aj, ← d.pre_intX, jacZ.aj_pre]

/-- **`redJ_add` of `IsX0ReductionAt`, as a theorem.** -/
theorem redJ_add (x y : RelPoint jstr (𝟙 SpecQ)) :
    d.redJ (ab.add x y) = ab'.add (d.redJ x) (d.redJ y) := by
  apply (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).injective
  rw [d.spJ_add, redJ_def, redJ_def, redJ_def, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, d.intJ_add, abZ.pre_add]

/-- **`red_aj` of `IsX0ReductionAt`, as a theorem.** -/
theorem red_aj (x : RelPoint strX (𝟙 SpecQ)) :
    d.redJ (jac.aj (𝟙 SpecQ) x) = jac'.aj (𝟙 (SpecF ℓ)) (d.redX x) := by
  apply (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).injective
  rw [d.spX_aj, redJ_def, Equiv.apply_symm_apply, redX_def, Equiv.apply_symm_apply,
    d.intJ_aj, jacZ.aj_pre]

include d in
/-- **Rank `0` transports to the integral model**, along
`𝒥(ℤ_(ℓ)) ≅ J(ℚ)`. -/
theorem finite_intPoints (hfin : Finite (RelPoint jstr (𝟙 SpecQ))) :
    Finite (RelPoint jstrZ (𝟙 (SpecLoc R))) := by
  haveI := hfin
  exact Finite.of_equiv _
    ((d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _)).trans
      (Equiv.ofBijective _ d.neronJ).symm)

/-- **A Néron-pinned datum is a reduction datum** (PROVEN), given
injectivity of reduction on integral points — which is
`neronReduction_injective` below.

This is the whole point of the pinning: `redJ_add` and `red_aj` are no
longer assumptions about an arbitrary map but consequences of the maps
being induced by morphisms of models over `ℤ_(ℓ)`. -/
noncomputable def toReduction
    (hinj : Function.Injective
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) :
        RelPoint jstrZ (𝟙 (SpecLoc R)) → RelPoint jstrZ (SpecLoc.special toF))) :
    IsX0ReductionAt jac jac' where
  redX := d.redX
  redJ := d.redJ
  redJ_add := d.redJ_add
  redJ_inj := by
    intro a b hab
    have h1 : RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ a)
        = RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ b) := by
      have h := congrArg
        (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)) hab
      rwa [redJ_def, redJ_def, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    have h2 := congrArg (RelPoint.pre (SpecLoc.generic R)
      (Category.comp_id (SpecLoc.generic R))) (hinj h1)
    rw [d.pre_intJ, d.pre_intJ] at h2
    exact (d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _)).injective h2
  red_aj := d.red_aj

end IsX0NeronDatum

/-- **Reduction is injective on the integral points of an abelian scheme
over `ℤ_(ℓ)` for `ℓ` odd** (sorry node).

TRUE, and classical.  `hfin` makes `𝒥(ℤ_(ℓ))` finite, hence torsion.
The kernel of reduction `𝒥(ℤ_(ℓ)) → 𝒥(𝔽_ℓ)` embeds in the kernel over
the completion `ℤ_ℓ`, which is the group of points of the formal group
of `𝒥` — and a formal group over a `ℓ`-adic ring of absolute
ramification index `e` is torsion-free when `e < ℓ − 1`.  Here `e = 1`
by `hbase`, so the condition is `ℓ > 2`.  A torsion subgroup of a
torsion-free group is trivial, and a homomorphism (`abZ.pre_add`) with
trivial kernel is injective.

**Every hypothesis is load-bearing.**  `hbase` is what makes the base a
DVR with `e = 1` and residue characteristic `ℓ` — over a ramified base
the formal group can have torsion.  `hℓ2` is exactly the `e < ℓ − 1`
condition and cannot be dropped: at `ℓ = 2`, `e = 1 = ℓ − 1` and
`2`-torsion can die under reduction.  `hfin` is rank `0`; without it the
kernel need not be torsion and the argument gives nothing.

This is the SHARED content that `card_le_of_rankZeroJacobian` also
rests on, isolated here so that it is proven once.

IRREDUCIBLE at this pin: it needs the formal group of an abelian scheme
over a discrete valuation ring, which does not exist in mathlib. -/
theorem neronReduction_injective (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (_hbase : IsReductionBase ℓ R toF) (_hℓ2 : ℓ ≠ 2)
    {JZ : Scheme.{0}} {jstrZ : JZ ⟶ SpecLoc R} (_abZ : AbelianSchemeStruct jstrZ)
    (_hfin : Finite (RelPoint jstrZ (𝟙 (SpecLoc R)))) :
    Function.Injective
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) :
        RelPoint jstrZ (𝟙 (SpecLoc R)) → RelPoint jstrZ (SpecLoc.special toF)) :=
  sorry

/-- **The good-reduction datum exists at every odd `ℓ ∤ N`** (sorry
node).

TRUE, and it is the integral-model half of the sieve: `X_0(N)` has a
smooth proper model over `ℤ[1/N]` (Deligne–Rapoport, Igusa), so over
`ℤ_(ℓ)` for `ℓ ∤ N`; its relative Jacobian is an abelian scheme, and it
is the Néron model of `J_0(N)` over `ℤ_(ℓ)` because an abelian scheme
with the right generic fibre is one.  The identifications of fibres and
the compatibility of Abel–Jacobi with base change are the standard
properties of the relative Jacobian.

Note there is NO sharpness claim here: this leaf is universal in `ℓ`
and says only that the reduction machinery exists.  Combined with
`neronReduction_injective` it is exactly the content of
`card_le_of_rankZeroJacobian` and `exists_x0Compactification_mod_prime`,
which is why factoring it out is a genuine reduction in the total work
rather than a repackaging.

IRREDUCIBLE at this pin: neither the integral model of `X_0(N)` nor the
relative Jacobian exists here. -/
theorem exists_x0NeronDatum (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓ2 : ℓ ≠ 2) (_hℓN : ¬ ℓ ∣ N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (_hX : IsX0Compactification N strX strY j) (jac : IsJacobianOf strX ab o) :
    ∃ (R : Subring ℚ) (toF : R →+* ZMod ℓ) (X' J' XZ YZ JZ : Scheme.{0})
      (strX' : X' ⟶ SpecF ℓ) (jstr' : J' ⟶ SpecF ℓ)
      (ab' : AbelianSchemeStruct jstr') (o' : RelPoint strX' (𝟙 (SpecF ℓ)))
      (jac' : IsJacobianOf strX' ab' o') (xstr : XZ ⟶ SpecLoc R)
      (ystr : YZ ⟶ SpecLoc R) (jZ : YZ ⟶ XZ) (jstrZ : JZ ⟶ SpecLoc R)
      (abZ : AbelianSchemeStruct jstrZ) (oZ : RelPoint xstr (𝟙 (SpecLoc R)))
      (jacZ : IsJacobianOf xstr abZ oZ),
      Nonempty (IsX0NeronDatum N ℓ R toF jac jac'
        (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :=
  sorry

/-- **The sieve at `d` cuts the survivors down to the rational cusps.**

The conclusion of `exists_x0Sieve`, phrased for one pinned datum so that
the sharpness leaf can quantify over data. -/
def IsSharpSieve (N : ℕ) {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X J X' J' XZ YZ JZ : Scheme.{0}} {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    {jac : IsJacobianOf strX ab o} {jac' : IsJacobianOf strX' ab' o'}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} {jacZ : IsJacobianOf xstr abZ oZ}
    (d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) : Prop :=
  ∃ s : Finset (RelPoint strX' (𝟙 (SpecF ℓ))),
    (∀ x' : RelPoint strX' (𝟙 (SpecF ℓ)),
        (∃ a : RelPoint jstr (𝟙 SpecQ), d.redJ a = jac'.aj (𝟙 (SpecF ℓ)) x') → x' ∈ s) ∧
      s.card = numRationalCusps N

/-- **Some good odd prime makes the sieve sharp** (sorry node — this is
the arithmetic heart of the four residual levels).

TRUE: at each of `45, 54, 63, 75` there is a good odd prime `ℓ` at which
only `numRationalCusps N = 4` of the points of `X_0(N)(𝔽_ℓ)` have
Abel–Jacobi class in the image of `J_0(N)(ℚ)`, even though `X_0(N)(𝔽_ℓ)`
itself has `8, 6, 8, 8` points.  The candidate witnesses are `ℓ = 7, 5,
5, 7` respectively.  See the FORMAL-CONTENT AUDIT under
`exists_x0Sieve` for the witness table, the refutation test each witness
passes, and the reason no number of auxiliary primes replaces this leaf.

**Why the universal quantifier over data is SAFE here**, where the
subsection docstring above warns it would not be for `IsX0ReductionAt`.
The warning was that `IsX0ReductionAt` constrains `redJ` only by
injectivity, additivity and `red_aj`, so a subgroup of the right order
sitting differently inside `J_0(N)(𝔽_ℓ)` gives an admissible datum with
MORE survivors — and one such datum would refute a `∀`-statement.
`IsX0NeronDatum` removes exactly that freedom: `base` pins the base as
`Spec ℤ_(ℓ)`, `model` pins the integral curve as the smooth model of
`X_0(N)` there, `genX`/`genJ`/`spX`/`spJ` pin `X'` and `J'` as its
fibres, and `neronJ` pins `redJ` as the genuine reduction.  Any two data
at the same `ℓ` are therefore isomorphic, and the survivor count is an
isomorphism invariant.

**`hfin` is load-bearing** and is the rank-`0` input: without it
`J_0(N)(ℚ)` is infinite, every point of `X_0(N)(𝔽_ℓ)` survives, and no
prime cuts anything.  `hlevel` restricts the leaf to the four levels
where the sieve is the intended route.

IRREDUCIBLE at this pin, and it is the residue of `exists_x0Sieve` after
the model-theoretic content is factored out: it needs the Abel–Jacobi
image of `X_0(N)(𝔽_ℓ)` inside `J_0(N)(𝔽_ℓ)` as an explicitly computable
finite object, plus Eichler–Shimura to know `#J_0(N)(𝔽_ℓ)`. -/
theorem exists_sharpSievePrime (N : ℕ) (_hlevel : N ∈ x0SieveLevels) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ¬ ℓ ∣ N ∧
      ∀ {R : Subring ℚ} {toF : R →+* ZMod ℓ}
        {X J X' J' XZ YZ JZ : Scheme.{0}} {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
        {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
        {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
        {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
        {jac : IsJacobianOf strX ab o} {jac' : IsJacobianOf strX' ab' o'}
        {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
        {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
        {oZ : RelPoint xstr (𝟙 (SpecLoc R))} {jacZ : IsJacobianOf xstr abZ oZ}
        (d : IsX0NeronDatum N ℓ R toF jac jac'
          (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ),
        Finite (RelPoint jstr (𝟙 SpecQ)) → IsSharpSieve N d :=
  sorry

/-- **The Mordell–Weil sieve closes at the four residual levels** (sorry
node — this is the criterion the four levels below rest on).

TRUE, and it is Kenku's determination read through the sieve: at each of
`45, 54, 63, 75` there is a good odd prime `ℓ` at which only
`numRationalCusps N = 4` of the points of `X_0(N)(𝔽_ℓ)` have Abel–Jacobi
class in the image of `J_0(N)(ℚ)`, even though `X_0(N)(𝔽_ℓ)` itself has
`8, 6, 8, 8` points.  The candidate witnesses from the reconnaissance
table above are `ℓ = 7, 5, 5, 7` respectively, with the image constrained
by the auxiliary primes `19, 7, 11, 11`.

**Why the prime is existentially quantified.**  The four rows of the
table are the *recommended* attempt, not part of the claim.  Committing
the statement to a specific `ℓ` would make it false if that particular
reduction happened to leave one extra surviving point — a numerical
accident that says nothing about the mathematics and that no argument
here depends on.  What the sieve method asserts, and what the four levels
actually need, is that SOME good prime cuts the count to the rational
cusps; that is what is stated.

**Every hypothesis is load-bearing.**  `hfin` is rank `0`: without it
`J_0(N)(ℚ)` is infinite, `Set.range redJ` is all of the finite group
`J_0(N)(𝔽_ℓ)` in effect, and no prime cuts anything.  `hX` is what makes
the statement about `X_0(N)` rather than an arbitrary curve, and `jac` is
what makes `Set.range redJ` the rational Jacobian rather than an
arbitrary subgroup.  `hlevel` restricts the leaf to the four levels where
the sieve is the intended route; see the subsection docstring.

**NO LONGER A LEAF (2026-07-26): PROVEN by decomposition.**  It was
recorded as irreducible below, together with the precise condition that
would make it decompose — a field on `IsX0ReductionAt` pinning `redJ`
through Néron models over `ℤ_ℓ`.  That condition has been built
(`IsX0NeronDatum`), and the statement now follows from three leaves:

* `neronReduction_injective` — reduction is injective on integral points
  of an abelian scheme over `ℤ_(ℓ)`, `ℓ` odd (the formal-group fact,
  shared with `card_le_of_rankZeroJacobian`);
* `exists_x0NeronDatum` — the integral model and its relative Jacobian
  exist at every odd `ℓ ∤ N` (Deligne–Rapoport / Igusa, universal in
  `ℓ`, no sharpness claim);
* `exists_sharpSievePrime` — some good odd prime makes the sieve sharp
  (the arithmetic residue).

`redJ_add` and `red_aj` are no longer assumptions anywhere: they are
theorems about the maps induced by the models, assembled by
`IsX0NeronDatum.toReduction`.  See the corrected subsection below for
what changed and why the universal quantifier in the third leaf is safe.

## FORMAL-CONTENT AUDIT (2026-07-26)

Two things about this statement are easy to misread, and one of them
looks at first like a way to discharge it cheaply.  Both were checked.

**The reduced side is NOT pinned to be a reduction of `X_0(N)`.**  Unlike
`card_le_of_rankZeroJacobian`, which takes `IsX0Compactification N strX'
strY' j'` as a hypothesis, this leaf quantifies `X'`, `J'`, `ab'`, `o'`,
`jac'` and `red` existentially and asks only for `IsJacobianOf` and
`IsX0ReductionAt`.  So a prover may supply ANY curve-and-Jacobian pair
over ANY `SpecF ℓ` — `ℓ` is not even required to be prime.  The leaf is
therefore strictly WEAKER than the classical single-prime sieve, which is
what makes it the right thing to ask for; but it also means the obvious
first question is whether some junk witness discharges it.

**NON-VACUITY: no junk witness can.**  The `red_aj` field forces
`jac'.aj (redX x) = redJ (jac.aj x)` for EVERY rational point `x` of `X`.
So every element of `jac.aj '' X_0(N)(ℚ)` produces, through `redX`, a
point of `X'` that satisfies the survival condition and hence lies in
`s`; and `redJ` is injective, so distinct Abel–Jacobi classes give
distinct survivors.  Therefore any witness whatsoever already implies

  `#(jac.aj '' X_0(N)(ℚ)) ≤ s.card = numRationalCusps N = 4`,

which — once `aj` is injective, as `HasRankZeroJacobian` provides — is
Kenku's determination at `N`.  That implication is not an informal remark:
it is exactly the proof of `card_le_of_sieve` immediately below, so the
compiler already certifies that this leaf is at least as hard as the
theorem it is standing in for.  In particular the freedom in the previous
paragraph buys a prover latitude in CONSTRUCTING a witness and no
latitude at all in the arithmetic it has to know.

**A cheap refutation test for any PROPOSED witness prime.**  Suppose the
datum is the genuine one, `X' = X_0(N)_{𝔽_ℓ}` and `J' = J_0(N)_{𝔽_ℓ}`.
Then `J'` has finitely many `𝔽_ℓ`-points, so an injective `redJ` out of a
group of the SAME order is surjective, every point of `X_0(N)(𝔽_ℓ)`
survives, and `s.card = numRationalCusps N` is impossible as soon as
`#X_0(N)(𝔽_ℓ) > numRationalCusps N`.  Hence:

  *if `#J_0(N)(ℚ) = #J_0(N)(𝔽_ℓ)` then `ℓ` is not a witness prime for the
  genuine datum* — not merely unlucky, impossible.

This is worth running before recording any witness, because the four
recommended ones came within one arithmetic coincidence of failing it.
The table above bounds `#J_0(45)(ℚ)` only by `512`, and `512` is exactly
`#J_0(45)(𝔽_7)` at the recommended witness `ℓ = 7`; had the rational
Jacobian attained its recorded bound, `ℓ = 7` would have been refuted.

**The bounds are far from attained, and the recommended witnesses
survive** (Magma, 2026-07-26, `RationalCuspidalSubgroup(JZero(N))`).  The
rational cuspidal subgroup is a LOWER bound for `#J_0(N)(ℚ)`, and the
`gcd` of the Eichler–Shimura counts is an UPPER bound:

| `N` | `dim J_0(N)` | rational cuspidal subgroup | `#J_0(N)(ℚ)` divides | witness `ℓ` | `#J_0(N)(𝔽_ℓ)` | index |
|-----|--------------|----------------------------|----------------------|-------------|-----------------|-------|
| 45 | 3 | `32 = [4, 8]`      | `512`  | 7 | `512`   | ≥ 16  |
| 54 | 4 | `81 = [3, 3, 9]`   | `243`  | 5 | `972`   | ≥ 12  |
| 63 | 5 | `96 = [2, 48]`     | `6144` | 5 | `6144`  | ≥ 64  |
| 75 | 5 | `80 = [2, 40]`     | `2560` | 7 | `28160` | ≥ 352 |

Every one of the four lower bounds divides its upper bound, so the two
computations are consistent; and at each recommended `ℓ` the reduction
`J_0(N)(ℚ) → J_0(N)(𝔽_ℓ)` has index at least `12`, so the refutation test
is nowhere near triggered and the recorded witnesses stand.  Under the
generalized Ogg conjecture — known for many `N` — the rational torsion
IS the rational cuspidal subgroup, and the left column is the exact
order; nothing here depends on that.

**The upper bounds are SATURATED, and that settles the design question
above.**  Recomputing the `gcd` of `#J_0(N)(𝔽_ℓ)` over *every* odd good
`ℓ < 300` — five times the range of the table above — returns `512, 243,
6144, 2560` unchanged, and the individual counts reproduce the recorded
table exactly (a third independent confirmation of the banked
arithmetic).  So no number of auxiliary primes will ever bring the upper
bound for `#J_0(45)(ℚ)` below `512 = #J_0(45)(𝔽_7)`: the multi-prime
"pin the group" argument, run to exhaustion, *cannot on its own rule out*
the case in which `ℓ = 7` is refuted.  The gap between `32` and `512` is
closed from the cuspidal side, not by more primes.

This is the concrete form of the correction recorded in the subsection
docstring.  Auxiliary primes bound the ORDER of the rational Jacobian and
saturate quickly; what the sieve needs is a prime at which the surviving
Abel–Jacobi classes are only the forced ones, and that is a different
question, answered here by the existential quantifier over `ℓ` rather
than by the table.

## WHY THIS LEAF DID NOT DECOMPOSE, and what let it (RESOLVED 2026-07-26)

**Read this as the record of a correct prediction, not as a live
obstruction.**  Everything below is still true of `IsX0ReductionAt`, and
it is exactly why the decomposition had to wait for `IsX0NeronDatum`.
The final paragraph named the missing ingredient; that ingredient was
then built, and the cut it licenses is the one now taken.

The natural cut is into (i) *good reduction exists* — the reduced pair
and the injective reduction map at any good odd `ℓ ∤ N`, which is content
shared with `exists_x0Compactification_mod_prime` and
`card_le_of_rankZeroJacobian` and would be worth factoring out — and
(ii) *the cut is sharp at some prime*.  *This does not compose*, and the
reason is worth recording so it is not rediscovered.

The two halves have to meet at the SAME `ℓ`, so (ii) must be existential
in `ℓ` and universal in the datum: "there is a good `ℓ` such that FOR
EVERY reduction datum at `ℓ` the survivors number `numRationalCusps N`".
That statement is false, or at least unsupported, because
`IsX0ReductionAt` does not pin `redJ` to be the genuine reduction.  Its
only constraints are injectivity, additivity, and `red_aj`; so ANY
injective homomorphism `J_0(N)(ℚ) → J_0(N)(𝔽_ℓ)` carrying
`jac.aj '' X_0(N)(ℚ)` into the Abel–Jacobi image is an admissible `redJ`,
and a subgroup of the right order sitting differently inside
`J_0(N)(𝔽_ℓ)` can meet that image in more than `numRationalCusps N`
classes.  Universally quantifying over data therefore risks a FALSE
sub-leaf, which is worse than the single honest one.

What would make the cut safe is a field on `IsX0ReductionAt` pinning
`redJ` — as the map induced by a morphism of Néron models over `ℤ_ℓ`, say.
That needs the integral model of `J_0(N)`, which is exactly the object
whose absence makes this leaf irreducible in the first place.

**This is what was done.**  The last inference above — "so the
decomposition becomes available at the same moment the leaf does" — is
the one place the analysis was too pessimistic, and the gap is worth
recording.  The integral model is needed as an EXISTENCE statement to
close the leaf, but only as a STRUCTURE to state the pinning; and a
structure can be written before anything is known to satisfy it.  So
`IsX0NeronDatum` was written, the pinned datum's existence became the
separate leaf `exists_x0NeronDatum`, and the sharpness leaf could then be
stated universally over pinned data without being false — because the
pinning removes precisely the freedom (a differently-placed subgroup of
the right order) that the paragraph above identifies as the danger.

The general lesson, since this development keeps meeting it: **"leaf `A`
needs theory `T`, which does not exist" does not imply "the decomposition
of `A` needs `T` to be proven"** — often it needs only `T` to be
*stated*.  An atomicity verdict should say which of the two it means. -/
theorem exists_x0Sieve (N : ℕ) (hlevel : N ∈ x0SieveLevels)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (hX : IsX0Compactification N strX strY j) (jac : IsJacobianOf strX ab o)
    (hfin : Finite (RelPoint jstr (𝟙 SpecQ))) :
    ∃ (ℓ : ℕ) (X' J' : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (jstr' : J' ⟶ SpecF ℓ)
      (ab' : AbelianSchemeStruct jstr') (o' : RelPoint strX' (𝟙 (SpecF ℓ)))
      (jac' : IsJacobianOf strX' ab' o') (red : IsX0ReductionAt jac jac')
      (s : Finset (RelPoint strX' (𝟙 (SpecF ℓ)))),
      (∀ x' : RelPoint strX' (𝟙 (SpecF ℓ)),
          (∃ a : RelPoint jstr (𝟙 SpecQ), red.redJ a = jac'.aj (𝟙 (SpecF ℓ)) x') →
            x' ∈ s) ∧
        s.card = numRationalCusps N := by
  obtain ⟨ℓ, hℓ, hℓ2, hℓN, hsharp⟩ := exists_sharpSievePrime N hlevel
  obtain ⟨R, toF, X', J', XZ, YZ, JZ, strX', jstr', ab', o', jac', xstr, ystr, jZ,
    jstrZ, abZ, oZ, jacZ, ⟨d⟩⟩ := exists_x0NeronDatum N ℓ hℓ hℓ2 hℓN hX jac
  have hinj := neronReduction_injective ℓ R toF d.base hℓ2 abZ (d.finite_intPoints hfin)
  obtain ⟨s, hs, hscard⟩ := hsharp d hfin
  exact ⟨ℓ, X', J', strX', jstr', ab', o', jac', d.toReduction hinj, s, hs, hscard⟩

/-- **The sieve bound, `#X_0(N)(ℚ) ≤ numRationalCusps N`** (PROVEN).

Pure transport along two injections and one commuting square.  Take the
sieve prime `ℓ` and its reduction data.  A finite set `t` of rational
points of `X_0(N)` maps into `X_0(N)(𝔽_ℓ)` by `redX`, and that map is
injective ON `X_0(N)(ℚ)` — not because reduction is injective in any
general sense, but because it is sandwiched between two injections:
`aj` is injective (positive genus, carried by `HasRankZeroJacobian`) and
`redJ` is injective (rank `0`), and `redJ ∘ aj = aj' ∘ redX`.  Every
point in the image has Abel–Jacobi class `redJ (aj x)`, manifestly in
`Set.range redJ`, so the image lands inside the sieve's surviving set
`s`.  Hence `#t ≤ #s = numRationalCusps N`.

Note what does NOT appear: no point count of `X_0(N)(𝔽_ℓ)`.  The bound
is by the surviving set, which is what makes it strictly stronger than
`card_le_of_rankZeroJacobian` and is the only reason the four levels
close at all. -/
theorem card_le_of_sieve {N : ℕ} (hlevel : N ∈ x0SieveLevels)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (hX : IsX0Compactification N strX strY j) (hJ : HasRankZeroJacobian strX)
    (t : Finset (RelPoint strX (𝟙 SpecQ))) : t.card ≤ numRationalCusps N := by
  classical
  obtain ⟨J, jstr, ab, o, jac, hfin, hajinj⟩ := hJ
  obtain ⟨ℓ, X', J', strX', jstr', ab', o', jac', red, s, hs, hscard⟩ :=
    exists_x0Sieve N hlevel hX jac hfin
  have hinjOn : Set.InjOn red.redX ↑t := by
    intro a _ b _ hab
    refine hajinj (red.redJ_inj ?_)
    rw [red.red_aj, red.red_aj, hab]
  have hsub : t.image red.redX ⊆ s := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact hs _ ⟨jac.aj (𝟙 SpecQ) y, red.red_aj y⟩
  calc t.card = (t.image red.redX).card := (Finset.card_image_of_injOn hinjOn).symm
    _ ≤ s.card := Finset.card_le_card hsub
    _ = numRationalCusps N := hscard

/-- **The sieve criterion** (PROVEN): at a residual level, `Y_0(N)(ℚ) = ∅`.

Identical in shape to `y0HasNoRationalPoint_of_witnessPrime`, with the
counting bound replaced by the sieve bound: the `c = numRationalCusps N`
rational cusps are `c` distinct rational points of `X_0(N)`, none of them
the image of a rational point of `Y_0(N)`, so a rational point of
`Y_0(N)` would give a `Finset` of `X_0(N)(ℚ)` of size `c + 1` — which
`card_le_of_sieve` forbids.  `y0HasNoRationalPoint_of_isEmpty` then
propagates emptiness from this one coarse moduli space to every one.

`hlevel` and `hsieve` overlap (`x0SieveLevels` is a sublist of
`kenkuLevels`); both are asked for rather than deriving one from the
other, exactly as `y0HasNoRationalPoint_of_witnessPrime` asks for both
`hlevel` and `htable`.  At the four call sites each is one `decide`. -/
theorem y0HasNoRationalPoint_of_sieveLevel (N : ℕ) (hN : 0 < N)
    (hlevel : N ∈ kenkuLevels) (hsieve : N ∈ x0SieveLevels) :
    Y0HasNoRationalPoint N := by
  classical
  obtain ⟨X, Y, strX, strY, j, ⟨hX⟩⟩ := exists_x0Compactification N hN
  obtain ⟨s, hscard, hsnot⟩ := exists_rationalCusps N hX
  refine y0HasNoRationalPoint_of_isEmpty hX.coarse ⟨fun y => ?_⟩
  have hp : sectionAlong j hX.comm y ∉ s := fun hmem => hsnot _ hmem y rfl
  have hle : (insert (sectionAlong j hX.comm y) s).card ≤ numRationalCusps N :=
    card_le_of_sieve hsieve hX (hasRankZeroJacobian_of_kenkuLevel N hlevel hX) _
  rw [Finset.card_insert_of_notMem hp, hscard] at hle
  omega

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
1980).  Already `X_0(22)` has genus `2`.

PROVEN 2026-07-26, as exactly that reduction from an infinite family to a
finite one.  The case split is on whether the two prime divisors of the
level lie in `mazurIsogenyPrimes`:

* if `p` does not, then `Y_0(p)(ℚ) = ∅` by `y0HasNoRationalPoint_prime`,
  and `p ∣ p * q` carries it up to the level by
  `y0HasNoRationalPoint_of_dvd` — this is where the infinitude goes;
* symmetrically for `q`;
* if both do, the level is one of the `61` residual products and the
  content is `y0HasNoRationalPoint_semiprime_of_mazurPrimes`.

So the mathematics is relocated onto two nodes — Mazur's prime theorem
and Kenku's finite check — and the quantifier over all pairs of distinct
primes is discharged here by the degeneracy map `Y_0(pq) ⟶ Y_0(p)`. -/
theorem y0HasNoRationalPoint_prod_two_primes {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q)
    (hmem : p * q ∉ ({6, 10, 14, 15, 21} : Finset ℕ)) :
    Y0HasNoRationalPoint (p * q) := by
  have hN : p * q ≠ 0 := Nat.mul_ne_zero hp.pos.ne' hq.pos.ne'
  by_cases hpm : p ∈ mazurIsogenyPrimes
  · by_cases hqm : q ∈ mazurIsogenyPrimes
    · exact y0HasNoRationalPoint_semiprime_of_mazurPrimes hp hq hpq hpm hqm hmem
    · exact y0HasNoRationalPoint_of_dvd hN (dvd_mul_left q p)
        (y0HasNoRationalPoint_prime hq hqm)
  · exact y0HasNoRationalPoint_of_dvd hN (dvd_mul_right p q)
      (y0HasNoRationalPoint_prime hp hpm)

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

**The interface that was missing here now exists** (2026-07-26), in the
subsection above: `IsX0Compactification` (`X_0(N)` with its cusp locus),
`IsJacobianOf` / `HasRankZeroJacobian` (`J_0(N)` and the rank-`0`
input), and `card_le_of_rankZeroJacobian` (reduction mod `ℓ`).  The
seven single-prime levels are PROVEN over it by
`y0HasNoRationalPoint_of_witnessPrime`, and what remains open is that
subsection's six leaves — none of them level-specific.

**The four sieve levels `45, 54, 63, 75` are PROVEN too** (2026-07-26),
over `y0HasNoRationalPoint_of_sieveLevel` and the single new leaf
`exists_x0Sieve`.  As predicted, that was a strengthening of the bound
rather than a new theory: `IsX0ReductionAt` records the reduction square
with `redJ` an injective homomorphism, and the bound counts the points of
`X_0(N)(𝔽_ℓ)` whose Abel–Jacobi class lies in the subgroup
`Set.range redJ ≅ J_0(N)(ℚ)` instead of all of them.  Every other piece —
`IsX0Compactification`, `IsJacobianOf`, `HasRankZeroJacobian`,
`exists_x0Compactification`, `exists_rationalCusps`,
`hasRankZeroJacobian_of_kenkuLevel` — is reused unchanged.

So all eleven level nodes of this module are now proven, and the module's
whole remaining content is the six interface leaves. -/

/-- **`Y_0(20)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_witnessPrime`; `X_0(20)` has genus `1`).  Ogg,
*Rational points on certain elliptic modular curves*, Proc. Sympos. Pure
Math. 24 (1973): `X_0(20)` is an elliptic curve of Mordell–Weil rank `0`
over `ℚ` whose six rational points are its six cusps.

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(20)(ℚ) = 0`,
all six cusps are rational, and `#X_0(20)(𝔽_3) = 6`; so the six cusps
exhaust `X_0(20)(ℚ)`.  (`ℓ = 7` also gives `6`.) -/
theorem y0HasNoRationalPoint_twenty : Y0HasNoRationalPoint 20 :=
  y0HasNoRationalPoint_of_witnessPrime 20 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **`Y_0(24)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_witnessPrime`; `X_0(24)` has genus `1`; Ogg
1973).

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(24)(ℚ) = 0`,
all eight cusps are rational, and `#X_0(24)(𝔽_5) = 8`; so the eight
cusps exhaust `X_0(24)(ℚ)`.  (`ℓ = 7` and `ℓ = 11` also give `8`.) -/
theorem y0HasNoRationalPoint_twentyFour : Y0HasNoRationalPoint 24 :=
  y0HasNoRationalPoint_of_witnessPrime 24 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **`Y_0(28)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_witnessPrime`; `X_0(28)` has genus `2`; Ogg,
*Hyperelliptic modular curves*, Bull. Soc. Math. France 102 (1974)).

ROUTE (rank-`0` reduction, closes on one prime).  **This level does NOT
need Chabauty–Coleman**, contrary to what this docstring asserted before
2026-07-26: `J_0(28)` has analytic rank `0` (its single newform factor
has `L(A, 1) ≠ 0`), hence Mordell–Weil rank `0`.  All six cusps are
rational and `#X_0(28)(𝔽_5) = 6`, so the six cusps exhaust
`X_0(28)(ℚ)`.  (`ℓ = 17` also gives `6`.) -/
theorem y0HasNoRationalPoint_twentyEight : Y0HasNoRationalPoint 28 :=
  y0HasNoRationalPoint_of_witnessPrime 28 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **`Y_0(30)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_witnessPrime`; `X_0(30)` has genus `3`).  This is
the minimal level with three distinct prime factors.

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(30)(ℚ) = 0`
(both newform factors have `L(A, 1) ≠ 0`), all eight cusps are rational,
and `#X_0(30)(𝔽_17) = 8`; so the eight cusps exhaust `X_0(30)(ℚ)`.
Note the small primes are *not* good enough here — `ℓ = 7, 11, 13` give
`12, 20, 16` — so `ℓ = 17` is the witness to use. -/
theorem y0HasNoRationalPoint_thirty : Y0HasNoRationalPoint 30 :=
  y0HasNoRationalPoint_of_witnessPrime 30 17 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **`Y_0(36)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_witnessPrime`; `X_0(36)` has genus `1`; Ogg
1973).

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(36)(ℚ) = 0`.
`X_0(36)` has `12` cusps but only `6` rational ones (the divisors
`d ∈ {1, 2, 4, 9, 18, 36}`; the pairs over `d = 3, 6, 12` are conjugate
over `ℚ(ζ_3)`), and `#X_0(36)(𝔽_5) = 6`; so the six rational cusps
exhaust `X_0(36)(ℚ)`. -/
theorem y0HasNoRationalPoint_thirtySix : Y0HasNoRationalPoint 36 :=
  y0HasNoRationalPoint_of_witnessPrime 36 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **`Y_0(42)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_witnessPrime`; `X_0(42)` has genus `5`).  The
second minimal level with three distinct prime factors.

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(42)(ℚ) = 0`
(all three newform factors have `L(A, 1) ≠ 0`), all eight cusps are
rational, and `#X_0(42)(𝔽_11) = 8`; so the eight cusps exhaust
`X_0(42)(ℚ)`.  Despite the genus being `5`, this is the cheapest kind of
argument — no Chabauty–Coleman is involved. -/
theorem y0HasNoRationalPoint_fortyTwo : Y0HasNoRationalPoint 42 :=
  y0HasNoRationalPoint_of_witnessPrime 42 11 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **`Y_0(45)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_sieveLevel`; `X_0(45)` has genus `3`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(45)(ℚ) = 0` (both newform factors have `L(A, 1) ≠ 0`), so
`X_0(45)(ℚ)` is finite and injects into `X_0(45)(𝔽_ℓ)` for every odd
`ℓ ∤ 45`.  But `X_0(45)` has `8` cusps of which only `4` are rational,
and **no** prime `ℓ < 100` attains `#X_0(45)(𝔽_ℓ) = 4`: the minimum over
`3 ≤ ℓ < 60` is `8`, at `ℓ = 7`.  So a single reduction leaves a factor
of `2` unaccounted for, and the four rational points must be pinned by
cutting `X_0(45)(𝔽_ℓ)` down to the classes lying in the image of
`J_0(45)(ℚ)` — which is what `exists_x0Sieve` supplies and what
`y0HasNoRationalPoint_of_sieveLevel` consumes.  `#J_0(45)(ℚ)` divides
`512`.

SIEVE DATA (recomputed from scratch with Magma on 2026-07-26 by a second
owner, *independently* of the pass that produced the table above; every
entry of that table for all eleven levels — genus, cusps, `c(N)`, best
`ℓ`, `#X_0(N)(𝔽_ℓ)` — was reproduced exactly, so the reconnaissance is
confirmed rather than merely inherited).  `#X_0(45)(𝔽_ℓ)` over
`3 ≤ ℓ < 60`: `7 ↦ 8`, `11 ↦ 16`, `13 ↦ 20`, `17 ↦ 16`, `19 ↦ 8`,
`23 ↦ 24`, `29 ↦ 32`, `31 ↦ 32`, `37 ↦ 68`, `41 ↦ 32`, `43 ↦ 32`,
`47 ↦ 40`, `53 ↦ 64`, `59 ↦ 64`.  So `ℓ = 19` is a *second* witness for
the minimum `8`, which the table above does not record.  The Jacobian
orders `#J_0(45)(𝔽_ℓ) = det(ℓ + 1 − T_ℓ ∣ S_2(Γ_0(45)))` are `512, 2048,
4096, 5120, 4096, 13824, 28672, 32768, 110592, 53248, 64000, 89600,
180224, 229376` at those same `ℓ`; their `gcd` is `512`, attained already
at `ℓ = 7`.  Hence `#J_0(45)(ℚ) ∣ 512` and `J_0(45)(ℚ)` is a `2`-group.

**WHY THIS LEAF IS NOT HARDER THAN ITS SEVEN SINGLE-PRIME SIBLINGS
*HERE*** (2026-07-26; this note is shared by all four sieve levels and is
written out only at this one).  The split "seven close on one prime, four
need a sieve" is a fact about the CLASSICAL arguments.  It is **not** a
difficulty ordering for this development, and reading it as one produces
phantom work.  All eleven levels are blocked on exactly the same absent
object — `X_0(N)` as a scheme, its cusps, `J_0(N)`, Mordell–Weil, and
reduction mod `ℓ` — none of which exists in `Mathlib` or in `~/cs/FLT`
(re-surveyed 2026-07-26: `Mathlib/AlgebraicGeometry/` contains no abelian
variety and no modular curve of any kind).  Once that layer exists, a
sieve level costs one extra *finite* computation over a single-prime
level, and the arithmetic for it is fully recorded above.

*Amended 2026-07-26, and this supersedes the paragraph above.*  That
shared layer is now WRITTEN, as the interface `IsX0Compactification` /
`IsJacobianOf` / `HasRankZeroJacobian`, so all eleven levels are proven
over it: the seven single-prime ones through
`card_le_of_rankZeroJacobian`, and these four through
`card_le_of_sieve`, whose one remaining input is `exists_x0Sieve`.  The
level nodes themselves are therefore no longer blocked on anything, and
the sibling `y0HasNoRationalPoint_prod_two_primes` no longer owns them. -/
theorem y0HasNoRationalPoint_fortyFive : Y0HasNoRationalPoint 45 :=
  y0HasNoRationalPoint_of_sieveLevel 45 (by decide) (by decide) (by decide)

/-- **`Y_0(50)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_witnessPrime`; `X_0(50)` has genus `2`; Ogg
1974).

ROUTE (rank-`0` reduction, closes on one prime): `rank J_0(50)(ℚ) = 0`
(both newform factors have `L(A, 1) ≠ 0`).  `X_0(50)` has `12` cusps but
only `4` rational ones, and `#X_0(50)(𝔽_3) = 4`; so the four rational
cusps exhaust `X_0(50)(ℚ)`.  This is the tightest of the seven
single-prime levels — the count matches `c(N)` exactly at the smallest
available prime. -/
theorem y0HasNoRationalPoint_fifty : Y0HasNoRationalPoint 50 :=
  y0HasNoRationalPoint_of_witnessPrime 50 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **`Y_0(54)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_sieveLevel`; `X_0(54)` has genus `4`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(54)(ℚ) = 0` (all three newform factors have `L(A, 1) ≠ 0`).
`X_0(54)` has `12` cusps of which `4` are rational, and no prime
`ℓ < 100` attains `#X_0(54)(𝔽_ℓ) = 4`: the minimum over `3 ≤ ℓ < 60` is
`6`, at `ℓ = 5`.  This is the *closest* of the four sieve levels — the
single-prime bound overshoots by only `2` — so it is the natural one to
attempt first.  `#J_0(54)(ℚ)` divides `243`, and since
`#J_0(54)(𝔽_5) = 2²·3⁵` the image of `J_0(54)(ℚ)` in `J_0(54)(𝔽_5)`
misses the whole `2`-part: the two surplus points are exactly what the
sieve has to push outside that image.

SIEVE DATA (independently recomputed with Magma 2026-07-26; see the
`N = 45` docstring for the provenance note and for the shared warning
that these four are *not* harder than the seven single-prime levels at
this pin).  `#X_0(54)(𝔽_ℓ)` over `3 ≤ ℓ < 60`: `5 ↦ 6`, `7 ↦ 12`,
`11 ↦ 12`, `13 ↦ 12`, `17 ↦ 18`, `19 ↦ 30`, `23 ↦ 24`, `29 ↦ 30`,
`31 ↦ 30`, `37 ↦ 12`, `41 ↦ 42`, `43 ↦ 48`, `47 ↦ 48`, `53 ↦ 54`,
`59 ↦ 60`.  The minimum `6` at `ℓ = 5` is attained ONCE — no second
witness — which is why this level, despite overshooting by only `2`, has
no cheap second prime to pair with.  Jacobian orders
`#J_0(54)(𝔽_ℓ) = det(ℓ + 1 − T_ℓ ∣ S_2(Γ_0(54)))`: `972` at `ℓ = 5`,
`6561` at `7`, `19440` at `11`, `26244` at `13`, then `104976, 236196,
311040, 777600, 944784, 944784, 3048192, 3779136, 5225472, 8266860,
12441600`.  Their `gcd` is `243 = 3⁵`, so `#J_0(54)(ℚ) ∣ 3⁵` and
`J_0(54)(ℚ)` is a `3`-group — note `#J(𝔽_7) = 3⁸` is already a pure
power of `3`, so the prime `7` alone forces the `3`-group conclusion. -/
theorem y0HasNoRationalPoint_fiftyFour : Y0HasNoRationalPoint 54 :=
  y0HasNoRationalPoint_of_sieveLevel 54 (by decide) (by decide) (by decide)

/-- **`Y_0(63)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_sieveLevel`; `X_0(63)` has genus `5`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(63)(ℚ) = 0` (all three newform factors have `L(A, 1) ≠ 0`).
`X_0(63)` has `8` cusps of which `4` are rational, and no prime
`ℓ < 100` attains `#X_0(63)(𝔽_ℓ) = 4`: the minimum over `3 ≤ ℓ < 60` is
`8`, at `ℓ = 5`, and `ℓ = 11` is a second minimum-witness.
`#J_0(63)(ℚ)` divides `6144 = 2¹¹·3`.

SIEVE DATA (independently recomputed with Magma 2026-07-26; see the
`N = 45` docstring for provenance and for the shared warning that these
four are *not* harder than the seven single-prime levels at this pin).
`#X_0(63)(𝔽_ℓ)` over `3 ≤ ℓ < 60`: `5 ↦ 8`, `11 ↦ 8`, `13 ↦ 16`,
`17 ↦ 24`, `19 ↦ 16`, `23 ↦ 24`, `29 ↦ 32`, `31 ↦ 40`, `37 ↦ 16`,
`41 ↦ 40`, `43 ↦ 64`, `47 ↦ 48`, `53 ↦ 48`, `59 ↦ 48`.  So `ℓ = 11` is a
*second* witness for the minimum `8`, which the table above does not
record.  Jacobian orders
`#J_0(63)(𝔽_ℓ) = det(ℓ + 1 − T_ℓ ∣ S_2(Γ_0(63)))`: `6144` at `ℓ = 5`,
then `135168, 589824, 2156544, 2359296, 7796736, 25804800, 42467328,
42467328, 116582400, 254803968, 249495552, 396472320, 589234176`.  Their
`gcd` is `6144 = 2¹¹·3`, attained already at `ℓ = 5`. -/
theorem y0HasNoRationalPoint_sixtyThree : Y0HasNoRationalPoint 63 :=
  y0HasNoRationalPoint_of_sieveLevel 63 (by decide) (by decide) (by decide)

/-- **`Y_0(75)(ℚ) = ∅`** (PROVEN 2026-07-26 over
`y0HasNoRationalPoint_of_sieveLevel`; `X_0(75)` has genus `5`).

ROUTE (rank-`0` **Mordell–Weil sieve** — one prime is not enough).
`rank J_0(75)(ℚ) = 0` (all four newform factors have `L(A, 1) ≠ 0`).
`X_0(75)` has `12` cusps of which `4` are rational, and no prime
`ℓ < 100` attains `#X_0(75)(𝔽_ℓ) = 4`: the minimum over `3 ≤ ℓ < 60` is
`8`, at `ℓ = 7`.  `#J_0(75)(ℚ)` divides `2560`.

`N = 75` is the level that most clearly needs more than one prime, and
so the row that shows why the sieve must be stated over `Set.range redJ`
rather than over any fixed number of counting primes.

SIEVE DATA (independently recomputed with Magma 2026-07-26; see the
`N = 45` docstring for provenance and for the shared warning that these
four are *not* harder than the seven single-prime levels at this pin).
`#X_0(75)(𝔽_ℓ)` over `3 ≤ ℓ < 60`: `7 ↦ 8`, `11 ↦ 20`, `13 ↦ 16`,
`17 ↦ 16`, `19 ↦ 18`, `23 ↦ 24`, `29 ↦ 16`, `31 ↦ 38`, `37 ↦ 48`,
`41 ↦ 28`, `43 ↦ 40`, `47 ↦ 40`, `53 ↦ 64`, `59 ↦ 92`.  The minimum `8`
at `ℓ = 7` is attained ONCE.  Jacobian orders
`#J_0(75)(𝔽_ℓ) = det(ℓ + 1 − T_ℓ ∣ S_2(Γ_0(75)))`: `28160` at `ℓ = 7`,
then `409600, 599040, 1638400, 2560000, 7464960, 13107200, 40140800,
92897280, 81920000, 148608000, 206080000, 522649600, 1284505600`.  Their
`gcd` is `2560 = 2⁹·5`.  Unlike the other three sieve levels the bound is
NOT attained at the best counting prime — `#J(𝔽_7) = 11·2560` — so at
least two primes are needed here even to pin the order of `J_0(75)(ℚ)`,
before any question about which torsion points are cuspidal arises.
(Only with `ℓ = 11`, where `#J_0(75)(𝔽_11) = 409600 = 2¹⁴·5²`, does the
`gcd` drop to `2560 = 2⁹·5`.) -/
theorem y0HasNoRationalPoint_seventyFive : Y0HasNoRationalPoint 75 :=
  y0HasNoRationalPoint_of_sieveLevel 75 (by decide) (by decide) (by decide)

end Fermat

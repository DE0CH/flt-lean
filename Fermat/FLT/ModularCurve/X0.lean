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
-- `padicValRat`: the `q`-adic valuation of the `j`-invariant, in which the
-- `v_q(j) < 0 ⟹ cuspidal reduction` dictionary is stated.  Same spelling as
-- `FreyCurve/MazurTorsion.lean`'s `potentiallyGoodReduction_of_isogenyCharacter`,
-- which is the consumer that dictionary exists for.
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
-- `Scheme.Hom.image` / `imageι` / `toImage`: the scheme-theoretic image of a
-- morphism, which is how the descent leaf's closed subscheme `C` is built.
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
-- `Algebra.IsAlgebraic.isIntegral`, the instance turning `ℚ̄/ℚ` algebraic into
-- `ℚ̄/ℚ` integral.  Reached only PRIVATELY through the imports above, so
-- `isIntegralHom_specAlgClos` cannot synthesise it without this line.
public import Mathlib.RingTheory.Algebraic.Integral
-- `IsIntegralHom.SpecMap_iff` / `IsIntegralHom.of_comp`, the cancellation that
-- makes each `ℚ̄`-point of `A` a closed map; see `isIntegralHom_geomPt`.
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
-- `Localization.subalgebra.ofField`: `ℤ` localized at `(ℓ)` realized INSIDE `ℚ`,
-- i.e. the witness `R = ℤ_(ℓ)` of `exists_isReductionBase`.
public import Mathlib.RingTheory.Localization.AsSubring
-- `IsLocalization.AtPrime.isUnit_mk'_iff`: units of `ℤ_(ℓ)`, which is the
-- `ker toF = nonunits` half of `IsReductionBase`.
public import Mathlib.RingTheory.Localization.AtPrime.Basic
-- `Nat.prime_iff_prime_int`, and `Prime.coprime_iff_not_dvd` transitively: the
-- Bézout witness making `s ∉ (ℓ)` a unit mod `ℓ`.
public import Mathlib.RingTheory.Int.Basic
-- The fpqc topology is subcanonical, and a faithfully flat quasi-compact
-- morphism is an `EffectiveEpi` — hence an `Epi`.  This is what lets
-- `Gamma0Atlas.toIsCoarseModuliY0` cancel the rigidifying cover and so
-- DERIVE the initiality clause of `IsCoarseModuliY0` instead of citing it;
-- see the atlas section before `exists_coarseModuliY0_of_pos`.
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
-- `ValuativeCommSq` and `IsProper.eq_valuativeCriterion`: the valuative criterion
-- of properness, which is what `bijective_pre_generic_of_isProper` runs on — and
-- through it both `properX` of `IsX0CurveModel` and `neronJ` of
-- `IsX0JacobianModel`.
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

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

/-! ### The Katz–Mazur atlas, and the initiality clause it implies

`exists_coarseModuliY0_of_pos` was a single citation covering all three
clauses of `IsCoarseModuliY0`.  It is now DERIVED (2026-07-27) from
`exists_gamma0Atlas`, which asks only for what Katz–Mazur actually
construct.  The clause that stops being cited is the one the citation
never covered: **initiality**.

The docstring below says as much itself — "the initiality clause is not
part of Katz–Mazur's *definition* ... but it follows from it" — and then
left that inference unformalised, inside the sorry.
`Gamma0Atlas.toIsCoarseModuliY0` is that inference, written out:

* an atlas carries the classifying map and its naturality — Katz–Mazur
  (8.1.3), a *construction*, with no universal property in it;
* it carries a **rigidifying cover**: every `Γ₀(N)`-datum is, fppf-locally
  on its base, a base change of one family `dM` over one scheme `M`.  This
  is (8.1.1)'s rigidification by `[Γ(n)]`-structures, which over a
  `ℚ`-scheme form a finite étale `GL₂(ℤ/n)`-torsor, hence a faithfully
  flat quasi-compact cover;
* it carries the **categorical quotient** property of `classify dM`:
  `𝔐(𝒫, [Γ(n)])` is affine, so the quotient of (8.1.1) is `Spec` of the
  ring of invariants, and that is a categorical quotient in the category
  of ALL schemes (Katz–Mazur Ch. 7; Mumford, *GIT*, Ch. 0 §2).

Initiality then follows with **no geometry at all**.  The proof is worth
stating because it is short and it is what the citation was hiding: a
cocone `c` is automatically constant on isomorphism classes, since two
rigidifications `a, b` of one datum `d₁` make `c d₁` equal to both
`a ≫ c dM` and `b ≫ c dM` *by `c`'s own naturality*; so `c dM` factors
uniquely through the quotient, which gives the map `u`.  That `u` computes
`c` on an ARBITRARY datum is then checked after pulling back to the
rigidifying cover `p`, where both sides become statements about `dM`, and
`p` may be cancelled because a faithfully flat quasi-compact morphism is
an epimorphism of schemes (`EffectiveEpi`, from
`AlgebraicGeometry.Sites.Fpqc`).

**THE CUT CANNOT WEAKEN THE TREE, AND HERE IS WHY THAT IS MECHANICAL.**
`Gamma0Atlas.toIsCoarseModuliY0` is a function *from* the new leaf *to*
the old one, so `exists_gamma0Atlas` is at least as strong as
`exists_coarseModuliY0_of_pos`; nothing downstream can be satisfied by an
atlas that a coarse moduli space would not also satisfy.  In particular
the leaf is not vacuously satisfiable: the trivial candidate
`Y = Spec ℚ` with `classify g d = g` does carry a classifying map and its
naturality, and fails `quotient` — take `Y' = M` and `φ = 𝟙`, which would
force `𝟙_M` to factor through `M ⟶ Spec ℚ`.

**Why the cut is at THIS boundary and not at the obvious one.**  The
natural-looking decomposition — construct `classify` by fppf descent from
a rigidification — is NOT writable at this pin, and the obstruction is
specific: descending `classify` requires comparing the pullbacks of a
datum along two maps `g₁, g₂ : Z ⟶ T'`, i.e. it requires *base change of
`Γ₀(N)`-data to be a construction*.  It is not one here — `IsBaseChangeOf`
is deliberately a *stated relation* (see its docstring) — and it cannot
become one until something in this project constructs an
`AbelianSchemeStruct` on a pullback.  Nothing does: every occurrence of
`AbelianSchemeStruct` in the tree is a binder or an existential.  **The
check that would refute this**: `grep -rn "AbelianSchemeStruct" Fermat/`
finding a producer rather than a consumer.  The cut taken here needs no
base change to be constructed, only to be *exhibited by the leaf*, which
is why it goes through. -/

/-- **Morphisms to `Spec ℚ` are unique when they exist.**

`Hom(X, Spec R) ≃ Hom(R, Γ(X, ⊤))` and `Subsingleton (ℚ →+* A)`
(`Rat.subsingleton_ringHom`: a ring map out of `ℚ` is determined, since
`ℚ` is a localisation of the initial ring `ℤ`).

This is what makes the structure-morphism bookkeeping of
`Gamma0Atlas.toIsCoarseModuliY0` disappear: a `Γ₀(N)`-datum over `T`
carries no `ℚ`-structure of its own, so the two base points `p ≫ g` and
`m ≫ strM` that the rigidifying cover produces must be identified, and
over `Spec ℚ` they are equal on the nose. -/
theorem subsingleton_hom_specQ (X : Scheme.{0}) : Subsingleton (X ⟶ SpecQ) := by
  constructor
  intro f g
  apply AlgebraicGeometry.ext_to_Spec
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **A Katz–Mazur atlas for the `Γ₀(N)`-moduli problem over `ℚ`**: the
data Katz–Mazur (8.1.1) and (8.1.3) actually construct, before any
universal property is asserted.

`Gamma0Atlas.toIsCoarseModuliY0` turns it into an `IsCoarseModuliY0`, so
this structure is a *sufficient* presentation of the coarse space; the
section comment above explains why it is also a faithful one.

The three non-trivial fields, and what supplies each:

* `cover` — the rigidification.  Over a `ℚ`-scheme the level-`n`
  structures on an elliptic scheme form a finite étale `GL₂(ℤ/n)`-torsor,
  so after a finite étale surjective — hence flat, surjective and
  quasi-compact — base change `p : T' ⟶ T` the datum acquires one and is
  classified by a map `m : T' ⟶ M`.  Note that `d'` is *supplied* by the
  field rather than constructed: this development states base change and
  never builds it.
* `quotient` — the categorical quotient property of `classify dM`, in the
  form that is actually available from GIT: a morphism out of `M` that
  cannot distinguish two rigidifications of the same datum is invariant
  under the deck group, and an invariant morphism out of an affine scheme
  factors uniquely through `Spec` of the invariants.
* `classify_natural` — Katz–Mazur (8.1.3)'s independence of the auxiliary
  level `n`, which is what makes the classifying map natural in the base.

`Y` is `M/GL₂(ℤ/n)` and `classify strM dM` is the quotient map; the
structure does not name the group, because nothing below needs it — only
the two properties above. -/
structure Gamma0Atlas (N : ℕ) where
  /-- the coarse space to be -/
  Y : Scheme.{0}
  /-- its structure morphism to `Spec ℚ` -/
  str : Y ⟶ SpecQ
  /-- the classifying map of the moduli problem, Katz–Mazur (8.1.3) -/
  classify : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), Gamma0Datum N T → RelPoint str g
  /-- the classifying map is natural in the base -/
  classify_natural : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {d' : Gamma0Datum N T'} {d : Gamma0Datum N T},
    IsBaseChangeOf h d' d → classify g' d' = RelPoint.pre h hg (classify g d)
  /-- the rigidified moduli scheme `𝔐([Γ₀(N)], [Γ(n)])` -/
  M : Scheme.{0}
  /-- its structure morphism -/
  strM : M ⟶ SpecQ
  /-- the family it carries -/
  dM : Gamma0Datum N M
  /-- **rigidification**: every datum is, after a faithfully flat
  quasi-compact base change, a base change of `dM` -/
  cover : ∀ {T : Scheme.{0}} (d : Gamma0Datum N T),
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma0Datum N T') (m : T' ⟶ M),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      Nonempty (IsBaseChangeOf p d' d) ∧ Nonempty (IsBaseChangeOf m d' dM)
  /-- **categorical quotient**: a morphism out of `M` that does not
  separate two rigidifications of one datum factors uniquely through the
  classifying map of `dM` -/
  quotient : ∀ {Y' : Scheme.{0}} (φ : M ⟶ Y'),
    (∀ {Z : Scheme.{0}} (a b : Z ⟶ M) (d₁ : Gamma0Datum N Z),
      IsBaseChangeOf a d₁ dM → IsBaseChangeOf b d₁ dM → a ≫ φ = b ≫ φ) →
    ∃! ψ : Y ⟶ Y', (classify strM dM).1 ≫ ψ = φ

/-- **An atlas IS a coarse moduli space** (PROVEN 2026-07-27) — the
initiality clause of `IsCoarseModuliY0` derived from Katz–Mazur's
construction rather than cited alongside it.

See the section comment above for the argument and for why this is the
boundary at which the node cuts. -/
def Gamma0Atlas.toIsCoarseModuliY0 {N : ℕ} (A : Gamma0Atlas N) :
    IsCoarseModuliY0 N A.str where
  classify := A.classify
  classify_natural := A.classify_natural
  universal := by
    intro Y' str' c hc
    haveI : ∀ Z : Scheme.{0}, Subsingleton (Z ⟶ SpecQ) := subsingleton_hom_specQ
    -- A cocone cannot separate two rigidifications of one datum: its own
    -- naturality equates both composites with its value at that datum.
    have hconst : ∀ {Z : Scheme.{0}} (a b : Z ⟶ A.M) (d₁ : Gamma0Datum N Z),
        IsBaseChangeOf a d₁ A.dM → IsBaseChangeOf b d₁ A.dM →
        a ≫ (c A.strM A.dM).1 = b ≫ (c A.strM A.dM).1 := by
      intro Z a b d₁ ha hb
      have h1 : (c (a ≫ A.strM) d₁).1 = a ≫ (c A.strM A.dM).1 :=
        congrArg Subtype.val (hc a rfl ha)
      have h2 : (c (b ≫ A.strM) d₁).1 = b ≫ (c A.strM A.dM).1 :=
        congrArg Subtype.val (hc b rfl hb)
      rw [← h1, ← h2, Subsingleton.elim (a ≫ A.strM) (b ≫ A.strM)]
    -- so it factors through the quotient, uniquely.
    obtain ⟨u, hu, huniq⟩ := A.quotient (c A.strM A.dM).1 hconst
    refine ⟨u, ⟨Subsingleton.elim _ _, ?_⟩, ?_⟩
    · -- `u` computes `c` at an arbitrary datum: pull back to the
      -- rigidifying cover, where both sides are statements about `dM`,
      -- and cancel the cover.
      intro T g d
      obtain ⟨T', p, d', m, hflat, hsurj, hqc, ⟨hbp⟩, ⟨hbm⟩⟩ := A.cover d
      haveI := hflat
      haveI := hsurj
      haveI := hqc
      have hcp : (c (p ≫ g) d').1 = p ≫ (c g d).1 :=
        congrArg Subtype.val (hc p rfl hbp)
      have hcm : (c (m ≫ A.strM) d').1 = m ≫ (c A.strM A.dM).1 :=
        congrArg Subtype.val (hc m rfl hbm)
      have hAp : (A.classify (p ≫ g) d').1 = p ≫ (A.classify g d).1 :=
        congrArg Subtype.val (A.classify_natural p rfl hbp)
      have hAm : (A.classify (m ≫ A.strM) d').1 = m ≫ (A.classify A.strM A.dM).1 :=
        congrArg Subtype.val (A.classify_natural m rfl hbm)
      have hst : (p ≫ g) = (m ≫ A.strM) := Subsingleton.elim _ _
      rw [hst] at hcp hAp
      have key : p ≫ (c g d).1 = p ≫ ((A.classify g d).1 ≫ u) := by
        rw [← hcp, hcm, ← hu, ← Category.assoc, ← hAm, hAp, Category.assoc]
      exact (cancel_epi p).mp key
    · -- uniqueness: a rival `u₁` factors `c dM` through the quotient too.
      rintro u₁ ⟨-, h₁⟩
      exact huniq u₁ (h₁ A.strM A.dM).symm

/-- **Existence of the Katz–Mazur atlas for `N ≥ 1`** (sorry node — the
CITATION, now carrying only what Katz–Mazur construct).

This replaces the citation formerly attached to
`exists_coarseModuliY0_of_pos`, from which it differs by exactly the
initiality clause: that clause is now PROVEN, in
`Gamma0Atlas.toIsCoarseModuliY0`.  The full citation, the matching of
hypotheses, and the faithfulness audit are recorded on
`exists_coarseModuliY0_of_pos` below and are unchanged; only the shape of
what is assumed has moved.

## What closing this needs, as separable items

Each is stated so that it can be dispatched without the others, and each
carries the check that would refute its being open.

1. **`[Γ(n)]`-structures and the representability of the rigidified
   problem** (Katz–Mazur 4.7, 5.1.1, 6.6.1): the affine scheme `M` and
   its family `dM`.  This is the `M`, `strM`, `dM` block.  *Refuting
   check*: a `Gamma0Datum`-valued producer anywhere in the tree —
   `grep -rn "Gamma0Datum" Fermat/` currently finds only binders,
   existentials, and the two descent leaves.
2. **The level-`n` torsor**: over a `ℚ`-scheme the level-`n` structures on
   an elliptic scheme form a finite étale `GL₂(ℤ/n)`-torsor.  This is the
   `cover` field, and it is where `exists_torsionSubscheme` below would be
   consumed.  *Refuting check*: `grep -rn "IsTorsor\|Torsor" Fermat/` and
   the same over `.lake/packages/mathlib` for a finite étale torsor API.
3. **The categorical quotient of an affine scheme by a finite group**:
   `Spec (A^G)` receives every `G`-invariant morphism out of `Spec A`
   uniquely.  This is the `quotient` field, and it is the one item that is
   **entirely mathlib-facing** — it mentions no modular curve and could be
   proven by someone who has never read this file.  *State of the pin,
   rechecked 2026-07-27*: mathlib has the ring-theoretic half —
   `Algebra.IsInvariant` (`Mathlib/RingTheory/Invariant/Basic.lean`), with
   `Algebra.IsInvariant.isIntegral`, `exists_smul_of_under_eq` and
   `orbit_eq_primesOver`, which say exactly that `Spec A ⟶ Spec (A^G)` is
   integral with the `G`-orbits as its fibres — and does **not** have the
   scheme-level statement.  *Refuting check*:
   `grep -rn "categorical quotient\|CategoricalQuotient" .lake/packages/mathlib/Mathlib/`
   returns nothing today.

## What is NO LONGER needed, and was wrongly recorded as needed

The previous audit said every route "needs a theory that does not exist
here", listing fpqc descent among the missing.  **Descent for morphisms is
present** and is what `Gamma0Atlas.toIsCoarseModuliY0` runs on:
`AlgebraicGeometry.fpqcTopology` is `Subcanonical`, and
`instance : [QuasiCompact f] → [Surjective f] → [Flat f] → EffectiveEpi f`
(`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`) gives `Epi` through
`CategoryTheory.epi_of_effectiveEpi`.  *The check that refutes the old
claim*: those two names resolve, which this file now demonstrates by
using them. -/
theorem exists_gamma0Atlas (N : ℕ) (hN : 0 < N) : Nonempty (Gamma0Atlas N) :=
  sorry

/-- **Existence of the coarse moduli space `Y_0(N)` for `N ≥ 1`**
(PROVEN 2026-07-27 from `exists_gamma0Atlas`, which now carries the
citation).

Everything below — the citation, the matching of hypotheses, the
faithfulness audit — describes what `exists_gamma0Atlas` assumes, and is
unchanged.  What is no longer assumed is the **initiality** clause of
`IsCoarseModuliY0`: it is derived in `Gamma0Atlas.toIsCoarseModuliY0`
from the rigidifying cover and the categorical-quotient property, using
fpqc descent.  See the section comment above that theorem.

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

## The former "IRREDUCIBLE at this pin" audit, CORRECTED 2026-07-27

That audit read: "`Mathlib` has no modular curve, no modular polynomial,
no moduli stack, no coarse-space existence theorem, no geometric invariant
theory and no quotient of a scheme by a finite group ... every route needs
a theory that does not exist here."  The list of *absent* theories is
still accurate — each was re-checked by name against a seeded `.lake` on
2026-07-27 — but the conclusion drawn from it was too strong, in two
separate ways, and both are now demonstrated rather than argued:

* **Descent for morphisms is PRESENT**, and it is the tool the route
  needed: `fpqcTopology` is `Subcanonical` and a faithfully flat
  quasi-compact morphism is an `EffectiveEpi`, hence an `Epi`
  (`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`).  This file now uses both.
* **Stating a theory is not proving it.**  Katz–Mazur's rigidification and
  their quotient by `GL₂(ℤ/n)` had to be *stated* for the cut, not proven,
  and once stated the initiality clause — the only clause the citation did
  not cover — became a short formal argument.

The remaining absences (a modular curve, `[Γ(n)]`-structures, GIT) are
what `exists_gamma0Atlas` now carries, itemised in its docstring. -/
theorem exists_coarseModuliY0_of_pos (N : ℕ) (hN : 0 < N) :
    ∃ (Y : Scheme.{0}) (str : Y ⟶ SpecQ), Nonempty (IsCoarseModuliY0 N str) := by
  obtain ⟨A⟩ := exists_gamma0Atlas N hN
  exact ⟨A.Y, A.str, ⟨A.toIsCoarseModuliY0⟩⟩

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

**MISSING MACHINERY, resurveyed 2026-07-26 against a SEEDED `.lake`.**
This replaces an earlier one-line "IRREDUCIBLE at this pin" note, which
was correct but far too coarse to route work against.

The obstruction is NOT that `Mathlib` lacks elliptic curves.  It is that
`AbelianSchemeStruct.add` is a group law on `RelPoint f g` for an
ARBITRARY test scheme `T`, and there is no functor-of-points description
of `Proj` anywhere at this pin — `ProjectiveSpectrum/Functor.lean` is
only functoriality `Proj ℬ ⟶ Proj 𝒜` in the graded ring, not a
description of `Hom(T, Proj 𝒜)`.  So `add` cannot be written by hand on
`T`-points, and that, rather than the geometry, is why no glue-first
skeleton is writable here: what remains after the definitions is a chain
of existentials, which is the shape this development forbids.  The node
therefore stays a single `sorry` until the items below land.

PRESENT and directly usable, each verified BY NAME at this pin:

* `WeierstrassCurve.Projective.addXYZ`, `addX`, `addY`, `addZ`
  (`EllipticCurve/Projective/Formula.lean`) — the addition FORMULAS, over
  an arbitrary `[CommRing R]`.  Only the group AXIOMS are field-only:
  every `AddCommGroup W.Point` instance at this pin
  (`Projective/Point.lean:572`, `Jacobian/Point.lean:588`,
  `Affine/Point.lean:768`) is stated for `W` over `[Field F]`, the affine
  one via the class group of the coordinate ring.
* `AlgebraicGeometry.Proj`, and `IsProper (Proj.toSpecZero 𝒜)` under
  `[Algebra.FiniteType (𝒜 0) A]` (`ProjectiveSpectrum/Proper.lean:368`).
* `HasPullbacks Scheme` (`AlgebraicGeometry/Pullbacks.lean:479`),
  `SmoothOfRelativeDimension` (`Morphisms/Smooth.lean:135`),
  `GeometricallyConnected` (`Geometrically/Connected.lean:40`).
* `WeierstrassCurve.Projective.toAffineAddEquiv`, giving
  `W.Point ≃+ W.toAffine.Point` over a field — the field-level half of
  the identification in the last conjunct.

ABSENT, as exact statements to route:

1. `GradedRing` on a quotient by a homogeneous ideal.  All of
   `Mathlib/RingTheory/GradedAlgebra/` was searched: `Ideal.IsHomogeneous`
   exists, the induced grading on `A ⧸ I` does NOT.  Without it `Proj` of
   the Weierstrass cubic cannot be FORMED, so this blocks even writing
   down `A`.  Shape needed: for `[GradedRing 𝒜]` and
   `hI : I.IsHomogeneous 𝒜`, a `GradedRing` structure on `A ⧸ I` graded
   by the images of the `𝒜 i`.
2. `WeierstrassCurve.Projective.proj : Scheme.{u}` together with
   `projToSpec : proj ⟶ Spec (CommRingCat.of R)` — the projective model
   as a scheme over its base, built from item 1.
3. THE CRUX: the group law as SCHEME MORPHISMS rather than on points.
   `m : pullback f f ⟶ A`, `e : S ⟶ A`, `i : A ⟶ A`, satisfying
   `m ≫ f = pullback.fst ≫ f`, `e ≫ f = 𝟙 S`, `i ≫ f = f`, with
   associativity, commutativity, unit and inverse stated as EQUATIONS OF
   MORPHISMS.
4. The formal bridge from item 3 to this file's interface — real code,
   and the only cheap part:
   `AbelianSchemeStruct.ofMorphisms f m e i (axioms) (proper) (smooth)
   (connected) : AbelianSchemeStruct f`, defining
   `add x y := pullback.lift x.1 y.1 _ ≫ m`, `zero g := g ≫ e` and
   `neg x := x.1 ≫ i`.  Naturality — the `pre_add` and `pre_zero` fields —
   is then AUTOMATIC, from compatibility of `pullback.lift` with
   precomposition.  That is exactly why the morphism-level route is
   writable where the point-level one is not.  **Build this item FIRST:**
   it is independent of all Weierstrass geometry, needs none of items 1,
   2, 5, 6, 7, 8, and is provable today.
5. Item 3 for the cubic specifically: that `addXYZ` and its companions
   glue to a morphism on `pullback f f`.  The formulas degenerate on the
   locus where the naive chart fails, so this needs the standard
   three-chart cover of `A ×_S A` and agreement on the overlaps.  This is
   the substantial geometric work.
6. Associativity of `m` as an equation of morphisms — classically the
   rigidity lemma or the theorem of the cube, or a reduction to the field
   case using reducedness and density of the generic fibre.
7. `SmoothOfRelativeDimension 1` from the Jacobian criterion with `Δ`
   invertible, and `GeometricallyConnected` for the cubic.  Both CLASSES
   exist at the pin; there is no Jacobian criterion for `Proj`.
8. `Spec ℚ̄`-points of `proj` identified with `W.Point`, which composed
   with `toAffineAddEquiv` yields the `≃+` of the last conjunct.

`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean` does NOT help, and was
checked rather than assumed: it is not on `main` at all, and everything in
it — `flat_mulByNat`, `finite_preimage_mulByNat`, `surjective_mulByNat` —
takes an `AbelianSchemeStruct` as INPUT.  Those are CONSUMERS of this
node, not producers of it, so no amount of progress there closes this
leaf.  `~/cs/FLT` has no abelian schemes and no elliptic-curve-as-scheme
construction either (rechecked 2026-07-26).  Nor does any declaration
anywhere in this project yet CONSTRUCT an `AbelianSchemeStruct`: every
occurrence in `X0.lean`, `KhareWintenberger.lean` and `TateModule.lean`
is a hypothesis binder or an existential, so this node is the first
producer and item 4 is the interface it will go through.

**RE-VERIFIED 2026-07-27, against a SEEDED `.lake`, by a fourth owner who
was sent to ASSEMBLE rather than to cut.**  An audit is a dated claim
about a moving tree, so each load-bearing claim above was re-run rather
than believed.  All four still hold; the refuting check is given for each,
so the next reader can re-run them in seconds instead of re-surveying:

* THE OBSTRUCTION ITSELF.  `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/`
  `Functor.lean` contains exactly `comap`, `comapStructureSheafFun`,
  `comapStructureSheaf`, `germ_map_sectionInBasicOpen`, `map`,
  `ι_comp_map`, `map_comp`, `map_id` — functoriality `Proj ℬ ⟶ Proj 𝒜` in
  the graded ring and nothing else.  There is still NO description of
  `Hom(T, Proj 𝒜)`.  Refuting check: a declaration in that directory
  computing `Hom(T, Proj 𝒜)` for general `T`.
* ITEM 1.  `grep` for `GradedRing`/`GradedAlgebra` on a line containing
  `⧸` over ALL of `Mathlib/` returns EMPTY.  `Homogeneous/Maps.lean`
  carries only `HomogeneousIdeal.map`/`comap` and their Galois
  connection — transport of homogeneous ideals along a graded ring hom,
  not a grading on a quotient.  Refuting check: any `GradedRing` instance
  whose carrier is a quotient ring.
* `~/cs/FLT`.  Its ONLY match for `AbelianScheme`/`GroupScheme`/
  `ProjectiveSpectrum` is a COMMENT in
  `KnownIn1980s/EllipticCurves/Flat.lean` saying `FLT.GroupScheme.`
  `FiniteFlat` "plans a definition" — i.e. it is unwritten there too.
* No project declaration constructs an `AbelianSchemeStruct` yet.

CORRECTION to item 7, and it is a real sharpening rather than a
restatement: the Jacobian criterion is NOT absent from the pin.
`Mathlib/RingTheory/Smooth/Local.lean` states it for LOCAL ALGEBRAS, and
`Smooth/StandardSmoothOfFree.lean` carries
`isUnit_jacobian_of_cotangentRestrict_bijective`.  What is missing is a
`Proj`-level formulation, so item 7 is "descend the LOCAL criterion along
an affine cover of `Proj`", not "build a Jacobian criterion from
nothing".  That is a materially smaller and better-posed task.

OWNERSHIP AT THIS DATE, recorded so no fifth owner manufactures a rival
API — a second independent version of an in-flight interface is the most
expensive object this fleet produces.  Item 1 and items 3+4 are both IN
FLIGHT and unreleased; items 2, 5, 6, 7, 8 are all downstream of item 1,
because without it the scheme `A` cannot be FORMED.  So there is at this
date NO independent sub-item at this node to dispatch a prover at: the
correct action is to WAIT for items 1 and 4 to land and then assemble.
Confirming that, and confirming the audit is not stale, is the whole
deliverable of a visit here until then. -/
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

/-! ### The group law of an abelian scheme as a MORPHISM (Yoneda)

`AbelianSchemeStruct` presents the group law only through the functor of
points: `ab.add` is a family of operations on `RelPoint f g`, natural in
the test object.  The subgroup-scheme conditions of
`CyclicSubgroupOfOrder` are stated at EVERY base `T'`, including
non-reduced ones, so they cannot be checked pointwise — the rigidity
argument ("two morphisms out of a reduced scheme into a separated one
agreeing on geometric points are equal") is simply false at a non-reduced
`T'`.

The fix is Yoneda, and it is carried out here rather than left to the
leaves: apply `ab.add` to the two projections of `A ×_ℚ A` to get an
honest morphism `addHom ab : A ×_ℚ A ⟶ A`, and `ab.neg` to the identity
point to get `negHom ab : A ⟶ A`.  Naturality then makes `ab.add x z` and
`ab.neg x` COMPOSITES with those fixed morphisms, at every base at once
(`add_eq_addHom`, `neg_eq_negHom`).

Consequence, and this is the point: the subgroup conditions at all bases
follow from a SINGLE factorisation of each morphism through the closed
immersion (`add_liesIn_of_factor`, `neg_liesIn_of_factor`).  The rigidity
input is then used exactly once, at `C ×_ℚ C` and at `C` — schemes that
really are reduced — which is the only place it is valid. -/

namespace AbelianSchemeStruct

/-- **Naturality of inversion.**  This is NOT an axiom of
`AbelianSchemeStruct` — the structure carries `pre_add` and `pre_zero`
only — but it follows from them by cancellation, `neg x` being the unique
solution of `add · x = zero`. -/
theorem pre_neg {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f)
    {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (x : RelPoint f g) :
    RelPoint.pre h hg (ab.neg x) = ab.neg (RelPoint.pre h hg x) := by
  letI := ab.addCommGroup g'
  have h1 : ab.add (RelPoint.pre h hg (ab.neg x)) (RelPoint.pre h hg x) = ab.zero g' := by
    rw [← ab.pre_add h hg, ab.neg_add, ab.pre_zero]
  have h2 : ab.add (ab.neg (RelPoint.pre h hg x)) (RelPoint.pre h hg x) = ab.zero g' :=
    ab.neg_add _
  exact add_right_cancel (a := RelPoint.pre h hg (ab.neg x))
    (b := RelPoint.pre h hg x) (c := ab.neg (RelPoint.pre h hg x)) (h1.trans h2.symm)

end AbelianSchemeStruct

/-- The structure morphism of the fibre square `A ×_ℚ A`. -/
noncomputable abbrev sqBase {A : Scheme.{0}} (f : A ⟶ SpecQ) :
    Limits.pullback f f ⟶ SpecQ :=
  Limits.pullback.fst f f ≫ f

/-- The first projection, as a relative point of `A ×_ℚ A`. -/
noncomputable def sqFst {A : Scheme.{0}} (f : A ⟶ SpecQ) : RelPoint f (sqBase f) :=
  ⟨Limits.pullback.fst f f, rfl⟩

/-- The second projection, as a relative point of `A ×_ℚ A`. -/
noncomputable def sqSnd {A : Scheme.{0}} (f : A ⟶ SpecQ) : RelPoint f (sqBase f) :=
  ⟨Limits.pullback.snd f f, Limits.pullback.condition.symm⟩

/-- **The group law of an abelian scheme as a morphism `A ×_ℚ A ⟶ A`**,
obtained by Yoneda: it is `ab.add` applied to the two projections. -/
noncomputable def addHom {A : Scheme.{0}} {f : A ⟶ SpecQ} (ab : AbelianSchemeStruct f) :
    Limits.pullback f f ⟶ A :=
  (ab.add (sqFst f) (sqSnd f)).1

/-- **Inversion as a morphism `A ⟶ A`**, obtained by Yoneda: it is
`ab.neg` applied to the identity point. -/
noncomputable def negHom {A : Scheme.{0}} {f : A ⟶ SpecQ} (ab : AbelianSchemeStruct f) :
    A ⟶ A :=
  (ab.neg (⟨𝟙 A, Category.id_comp f⟩ : RelPoint f f)).1

/-- **`ab.add` IS composition with `addHom ab`, at every base** (PROVEN):
naturality `pre_add` read at the map into `A ×_ℚ A` determined by the two
points. -/
theorem add_eq_addHom {A : Scheme.{0}} {f : A ⟶ SpecQ} (ab : AbelianSchemeStruct f)
    {T' : Scheme.{0}} {g : T' ⟶ SpecQ} (x z : RelPoint f g) :
    (ab.add x z).1 =
      Limits.pullback.lift x.1 z.1 (by rw [x.2, z.2]) ≫ addHom ab := by
  set u : T' ⟶ Limits.pullback f f :=
    Limits.pullback.lift x.1 z.1 (by rw [x.2, z.2]) with hu
  have hg : u ≫ sqBase f = g := by
    show u ≫ Limits.pullback.fst f f ≫ f = g
    rw [← Category.assoc, hu, Limits.pullback.lift_fst, x.2]
  have h := ab.pre_add u hg (sqFst f) (sqSnd f)
  have h1 : RelPoint.pre u hg (sqFst f) = x := by
    apply Subtype.ext
    show u ≫ Limits.pullback.fst f f = x.1
    rw [hu, Limits.pullback.lift_fst]
  have h2 : RelPoint.pre u hg (sqSnd f) = z := by
    apply Subtype.ext
    show u ≫ Limits.pullback.snd f f = z.1
    rw [hu, Limits.pullback.lift_snd]
  rw [h1, h2] at h
  exact (congrArg Subtype.val h).symm

/-- **`ab.neg` IS composition with `negHom ab`, at every base** (PROVEN):
`pre_neg` read at the point itself. -/
theorem neg_eq_negHom {A : Scheme.{0}} {f : A ⟶ SpecQ} (ab : AbelianSchemeStruct f)
    {T' : Scheme.{0}} {g : T' ⟶ SpecQ} (x : RelPoint f g) :
    (ab.neg x).1 = x.1 ≫ negHom ab := by
  have h := ab.pre_neg x.1 (g := f) (g' := g) x.2
    (⟨𝟙 A, Category.id_comp f⟩ : RelPoint f f)
  have hx : RelPoint.pre x.1 (g := f) (g' := g) x.2
      (⟨𝟙 A, Category.id_comp f⟩ : RelPoint f f) = x := by
    apply Subtype.ext
    show x.1 ≫ 𝟙 A = x.1
    rw [Category.comp_id]
  rw [hx] at h
  exact (congrArg Subtype.val h).symm

/-- **`C ×_ℚ C ⟶ A ×_ℚ A`** induced by a subscheme inclusion `ι : C ⟶ A`. -/
noncomputable def sqMap {A C : Scheme.{0}} {f : A ⟶ SpecQ} (ι : C ⟶ A) :
    Limits.pullback (ι ≫ f) (ι ≫ f) ⟶ Limits.pullback f f :=
  Limits.pullback.map (ι ≫ f) (ι ≫ f) f f ι ι (𝟙 SpecQ) (by simp) (by simp)

@[simp] theorem sqMap_fst {A C : Scheme.{0}} {f : A ⟶ SpecQ} (ι : C ⟶ A) :
    sqMap ι ≫ Limits.pullback.fst f f = Limits.pullback.fst (ι ≫ f) (ι ≫ f) ≫ ι :=
  Limits.pullback.lift_fst _ _ _

@[simp] theorem sqMap_snd {A C : Scheme.{0}} {f : A ⟶ SpecQ} (ι : C ⟶ A) :
    sqMap ι ≫ Limits.pullback.snd f f = Limits.pullback.snd (ι ≫ f) (ι ≫ f) ≫ ι :=
  Limits.pullback.lift_snd _ _ _

/-- **ONE factorisation at `C ×_ℚ C` gives closure under the group law at
EVERY base** (PROVEN).

This is what makes the `add_liesIn` field reachable: the field quantifies
over all test schemes `T'`, but by `add_eq_addHom` every instance of it is
a composite with the single morphism `addHom ab`, so a single factorisation
`μ` of `sqMap ι ≫ addHom ab` through `ι` discharges all of them. -/
theorem add_liesIn_of_factor {A C : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (ι : C ⟶ A)
    (μ : Limits.pullback (ι ≫ f) (ι ≫ f) ⟶ C) (hμ : μ ≫ ι = sqMap ι ≫ addHom ab)
    {T' : Scheme.{0}} {g : T' ⟶ SpecQ} {x z : RelPoint f g}
    (hx : RelPoint.LiesIn ι x) (hz : RelPoint.LiesIn ι z) :
    RelPoint.LiesIn ι (ab.add x z) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hz
  have hab : a ≫ (ι ≫ f) = b ≫ (ι ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, ha, hb, x.2, z.2]
  refine ⟨Limits.pullback.lift a b hab ≫ μ, ?_⟩
  rw [Category.assoc, hμ, add_eq_addHom ab x z, ← Category.assoc]
  congr 1
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [Category.assoc, sqMap_fst, ← Category.assoc, Limits.pullback.lift_fst, ha,
      Limits.pullback.lift_fst]
  · rw [Category.assoc, sqMap_snd, ← Category.assoc, Limits.pullback.lift_snd, hb,
      Limits.pullback.lift_snd]

/-- **ONE factorisation at `C` gives closure under inversion at EVERY
base** (PROVEN).  Same mechanism as `add_liesIn_of_factor`, via
`neg_eq_negHom`. -/
theorem neg_liesIn_of_factor {A C : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (ι : C ⟶ A)
    (ν : C ⟶ C) (hν : ν ≫ ι = ι ≫ negHom ab)
    {T' : Scheme.{0}} {g : T' ⟶ SpecQ} {x : RelPoint f g}
    (hx : RelPoint.LiesIn ι x) :
    RelPoint.LiesIn ι (ab.neg x) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a ≫ ν, ?_⟩
  rw [Category.assoc, hν, ← Category.assoc, ha, neg_eq_negHom ab x]

/-! ### The span of a finite family of geometric points

**Added 2026-07-26, and it is what turns the descent leaf below from an
unstartable existential into a construction with five stated properties.**

The obstruction recorded in the pin survey of
`exists_cyclicSubgroupOfOrder_of_galoisStable` was that nothing in the pin
builds a closed subscheme out of a finite set of geometric points.  That
was a naming miss: `AlgebraicGeometry.Scheme.Hom.image` is the
scheme-theoretic image of a morphism, and

    C := the scheme-theoretic image of  ∐_{s ∈ ⟨y⟩} Spec ℚ̄ ⟶ A

is exactly the reduced closed subscheme supported on the (finitely many,
closed) images of the points of `⟨y⟩`.  Classically `C = Spec ∏_i κ_i`
with the `κ_i` the fields of definition of the `Γ_ℚ`-orbits, which is the
descended group scheme; here it is obtained without any Galois-category
machinery, because the scheme-theoretic image already performs the
descent.

Two of the eight fields of `CyclicSubgroupOfOrder` are then FREE for this
`C`, and are proven below rather than left to a successor:

* `isClosedImmersion` — `IsClosedImmersion I.subschemeι` is a mathlib
  instance;
* `flat` — the base is `Spec ℚ`, a one-point integral scheme, and mathlib's
  `[Subsingleton Y] [IsIntegral Y] → Flat f` instance applies verbatim.
  (This confirms the "NOTE ON THE `flat` FIELD" prediction below: the field
  really does cost nothing.) -/

/-- **The coproduct of copies of `Spec ℚ̄` indexed by `J`**, the source of
the morphism whose scheme-theoretic image cuts out the level structure. -/
noncomputable abbrev geomPtSigma (J : Type) : Scheme.{0} :=
  ∐ (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ)))

/-- **The morphism `∐_J Spec ℚ̄ ⟶ A` assembled from a family of
`ℚ̄`-points of `A`.** -/
noncomputable def geomPtDesc {A : Scheme.{0}} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A)) :
    geomPtSigma J ⟶ A :=
  Limits.Sigma.desc p

/-- **The closed subscheme of `A` spanned by a family of `ℚ̄`-points**: the
scheme-theoretic image of `geomPtDesc p`.

For a `Γ_ℚ`-stable family this is the Galois descent of the family — the
smallest closed subscheme of `A` through which every member factors. -/
noncomputable def spanScheme {A : Scheme.{0}} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A)) : Scheme.{0} :=
  (geomPtDesc p).image

/-- **The closed immersion of the span into `A`.** -/
noncomputable def spanSchemeι {A : Scheme.{0}} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A)) :
    spanScheme p ⟶ A :=
  (geomPtDesc p).imageι

/-- The span is a closed subscheme of `A` (PROVEN — a mathlib instance). -/
instance {A : Scheme.{0}} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A)) :
    IsClosedImmersion (spanSchemeι p) :=
  inferInstanceAs (IsClosedImmersion (geomPtDesc p).ker.subschemeι)

/-- **Every member of the family factors through the span** (PROVEN): it is
`Sigma.ι` followed by the factorisation through the scheme-theoretic
image. -/
theorem geomPt_liesIn_spanScheme {A : Scheme.{0}} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A)) (j : J) :
    ∃ w : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ spanScheme p,
      w ≫ spanSchemeι p = p j := by
  refine ⟨Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j ≫
    (geomPtDesc p).toImage, ?_⟩
  show Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j ≫
      (geomPtDesc p).toImage ≫ (geomPtDesc p).imageι = p j
  rw [Scheme.Hom.toImage_imageι]
  exact Limits.colimit.ι_desc _ _

/-- **The `N` multiples of a geometric point `y`**, as a family of
`ℚ̄`-points of `A` indexed by `Fin N`.

Indexing by `Fin N` rather than by `↥(AddSubgroup.zmultiples y)` is
deliberate: the latter's *type* depends on the `AddCommGroup` instance
`ab.addCommGroup`, which would force a `letI` into every signature below.
When `addOrderOf y = N` the two index the same subset of `A(ℚ̄)`, since
`⟨y⟩ = {0 • y, …, (N-1) • y}`. -/
noncomputable def zmulPts {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (y : GeomFibrePt f (𝟙 SpecQ)) :
    Fin N → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A) :=
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  fun k => (((k : ℕ) • y : GeomFibrePt f (𝟙 SpecQ))).1

/-- Every multiple of `y` is a geometric point of the fibre over
`𝟙 SpecQ` (PROVEN — it is the second component of the relative point). -/
theorem zmulPts_comp {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (y : GeomFibrePt f (𝟙 SpecQ)) (k : Fin N) :
    zmulPts ab N y k ≫ f = specAlgClos ℚ ≫ 𝟙 SpecQ :=
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  (((k : ℕ) • y : GeomFibrePt f (𝟙 SpecQ))).2

/-! ### Finiteness of the span

The route below is SHORTER than the one predicted in the docstring of
`isFinite_spanSchemeι`, and does not use artinian schemes at all; see the
correction recorded there. -/

/-- **`Spec ℚ̄ ⟶ Spec ℚ` is an integral morphism** (PROVEN): `ℚ̄` is
algebraic, hence integral, over `ℚ`. -/
theorem isIntegralHom_specAlgClos' {F : Type} [Field F] :
    IsIntegralHom (specAlgClos F) := by
  rw [specAlgClos, IsIntegralHom.SpecMap_iff]
  intro x
  exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (A := AlgebraicClosure F)
    (x : AlgebraicClosure F)).isIntegral

/-- **`Spec ℚ̄ ⟶ Spec ℚ` is an integral morphism** (PROVEN).

STATED OVER A VARIABLE BASE FIELD ON PURPOSE, and then instantiated — this
is CLAUDE.md's `ULift ℚ`/`AlgebraicClosure ℚ` remedy in a fresh spot.  At
the literal `ℚ`, `Algebra ℚ (AlgebraicClosure ℚ)` does not resolve to
`AlgebraicClosure.instAlgebra` (the `Rat`-algebra diamond gets there
first), so `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` fails to
synthesise even though every import is present.  At a variable `F` the
diamond cannot arise and the instance is found immediately. -/
theorem isIntegralHom_specAlgClos : IsIntegralHom (specAlgClos ℚ) :=
  isIntegralHom_specAlgClos'

/-- **The range of `geomPtDesc p` is covered by the ranges of the members
of the family** (PROVEN): every point of `∐_J Spec ℚ̄` lies in one summand,
and `Sigma.ι j ≫ Sigma.desc p = p j`. -/
theorem range_geomPtDesc_subset {A : Scheme.{0}} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A)) :
    Set.range (geomPtDesc p).base ⊆ ⋃ j, Set.range (p j).base := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨⟨j, x⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk
    (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ)))).surjective y
  rw [AlgebraicGeometry.sigmaMk_mk]
  refine Set.mem_iUnion.mpr ⟨j, x, ?_⟩
  rw [← Scheme.Hom.comp_apply,
    show Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j
        ≫ geomPtDesc p = p j from Limits.Sigma.ι_desc p j]

section SpanFinite

variable {A : Scheme.{0}} {f : A ⟶ SpecQ} (ab : AbelianSchemeStruct f)
  {J : Type} [Finite J]
  (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
  (hp : ∀ j, p j ≫ f = specAlgClos ℚ ≫ 𝟙 SpecQ)

omit [Finite J] in
include ab hp in
/-- **Each geometric point of the family is an INTEGRAL morphism**
(PROVEN), hence a closed map.

This is the step that replaces "Zariski's lemma" in the predicted route,
and it is where properness of `f` does the work: `p j ≫ f` is
`specAlgClos ℚ`, which is integral, and `f` is separated because it is
proper, so `p j` is integral by cancellation
(`IsIntegralHom.of_comp`).  In particular the image of `p j` is a single
CLOSED point of `A`, with no residue-field computation anywhere. -/
theorem isIntegralHom_geomPt (j : J) : IsIntegralHom (p j) := by
  have hsep : IsSeparated f := by have := ab.proper; infer_instance
  have : IsIntegralHom (p j ≫ f) := by
    rw [hp j, Category.comp_id]
    exact isIntegralHom_specAlgClos
  exact IsIntegralHom.of_comp (p j) f

include ab hp in
/-- **The span is supported on the finitely many image points of the
family** (PROVEN).  Each `Set.range (p j)` is closed by
`isIntegralHom_geomPt`, so their union is closed and already contains the
closure of `Set.range (geomPtDesc p)`, which is the support of the
scheme-theoretic image. -/
theorem range_spanSchemeι_subset :
    Set.range (spanSchemeι p).base ⊆ ⋃ j, Set.range (p j).base := by
  have hcl : ∀ j, IsClosed (Set.range (p j).base) := by
    intro j
    have := isIntegralHom_geomPt ab p hp j
    exact (p j).isClosedMap.isClosed_range
  have hclU : IsClosed (⋃ j, Set.range (p j).base) := isClosed_iUnion_of_finite hcl
  have hqs : QuasiSeparated f := by have := ab.proper; infer_instance
  have hqc0 : QuasiCompact (geomPtDesc p ≫ f) :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) |>.mpr inferInstance
  have hqc : QuasiCompact (geomPtDesc p) := QuasiCompact.of_comp (geomPtDesc p) f
  show Set.range (Scheme.Hom.imageι _).base ⊆ _
  rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  exact hclU.closure_subset_iff.mpr (range_geomPtDesc_subset p)

include ab hp in
/-- **The span is an AFFINE scheme** (PROVEN): its space is finite and
`T1`, hence discrete, and mathlib's
`[Finite X] [DiscreteTopology X] → IsAffine X` applies.

This is the statement whose absence the docstring of
`isFinite_spanSchemeι` recorded as "the one genuine gap"
(`IsArtinianScheme X → IsAffine X`).  See the correction there: that
implication is already in the pin, and in fact is not needed — no
artinian theory enters this proof. -/
theorem isAffine_spanScheme : IsAffine (spanScheme p) := by
  have hsub := range_spanSchemeι_subset ab p hp
  have hfin : (⋃ j, Set.range (p j).base).Finite :=
    Set.finite_iUnion fun j => Set.finite_range _
  have hinj : Function.Injective (spanSchemeι p).base :=
    (spanSchemeι p).isClosedEmbedding.injective
  have hrf : (Set.range (spanSchemeι p).base).Finite := hfin.subset hsub
  have : Finite (spanScheme p) := by
    have hpre := Set.Finite.preimage (f := (spanSchemeι p).base) hinj.injOn hrf
    rw [Set.preimage_range] at hpre
    exact Set.finite_univ_iff.mp hpre
  have : T1Space (spanScheme p) := by
    refine ⟨fun c => ?_⟩
    obtain ⟨j, x, hx⟩ : ∃ j, ∃ x, (p j).base x = (spanSchemeι p).base c := by
      simpa using hsub ⟨c, rfl⟩
    have hsingle : Set.range (p j).base = {(spanSchemeι p).base c} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨x, hx⟩, ?_⟩
      rintro _ ⟨x', rfl⟩
      rw [← hx]
      congr 1
      exact Subsingleton.elim _ _
    have hclA : IsClosed ({(spanSchemeι p).base c} : Set A) := by
      rw [← hsingle]
      have := isIntegralHom_geomPt ab p hp j
      exact (p j).isClosedMap.isClosed_range
    have heq : ({c} : Set (spanScheme p))
        = (spanSchemeι p).base ⁻¹' {(spanSchemeι p).base c} := by
      ext d
      simp [Set.mem_preimage, hinj.eq_iff]
    rw [heq]
    exact hclA.preimage (spanSchemeι p).continuous
  infer_instance

end SpanFinite

/-! ### Descent of a factorisation along `ℚ̄/ℚ`

The three lemmas below are what turn leaf (ii) into a one-line
kernel-comparison.  The point is that `Spec ℚ̄ ⟶ Spec ℚ` is
schematically dominant — every `app` of it is INJECTIVE — so pulling a
section back to `ℚ̄` does not enlarge its vanishing locus, and the
kernel ideal sheaf of a morphism out of `Spec ℚ` is unchanged by
precomposing with it. -/

/-- An open subset of a ONE-POINT space is `⊥` or `⊤` (PROVEN). -/
theorem opens_eq_bot_or_top {X : Scheme.{0}} [Subsingleton X] (W : X.Opens) :
    W = ⊥ ∨ W = ⊤ := by
  rcases Set.eq_empty_or_nonempty (W : Set X) with h | ⟨x, hx⟩
  · exact Or.inl (TopologicalSpace.Opens.ext h)
  · refine Or.inr (TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_))
    rwa [Subsingleton.elim y x]

/-- **Every `app` of `Spec F̄ ⟶ Spec F` is injective** (PROVEN).

`Spec F` is a one-point space, so there are only two opens to check.  On
`⊥` the sections form the zero ring and injectivity is vacuous; on `⊤`
it is the `ΓSpecIso` naturality square together with injectivity of
`F → F̄`.

Stated over a VARIABLE base field for the reason recorded at
`isIntegralHom_specAlgClos`. -/
theorem app_injective_specAlgClos {F : Type} [Field F]
    (W : (Spec (CommRingCat.of F)).Opens) :
    Function.Injective ((specAlgClos F).app W).hom := by
  have : Subsingleton (Spec (CommRingCat.of F)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rcases opens_eq_bot_or_top W with rfl | rfl
  · intro a b _
    exact Subsingleton.elim a b
  · have hφ : Function.Injective
        (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))).hom :=
      (algebraMap F (AlgebraicClosure F)).injective
    have hiso : Function.Injective
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective
    have hnat := Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))
    -- NOTE: `rw [hnat]` directly under the `⇑(CommRingCat.Hom.hom ·)`
    -- coercion produces a motive error; rewriting at the level of the
    -- underlying FUNCTION is what works.
    have hfun : ⇑(((specAlgClos F).app ⊤ ≫
          (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure F))).hom).hom)
        = ⇑(((Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫
          CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))).hom) :=
      congrArg (fun m => ⇑(CommRingCat.Hom.hom m)) hnat
    have hcomp : Function.Injective
        (((specAlgClos F).app ⊤ ≫
          (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure F))).hom).hom) := by
      rw [hfun]
      simp only [CommRingCat.hom_comp, RingHom.coe_comp]
      exact hφ.comp hiso
    intro a b hab
    refine hcomp ?_
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hab]

/-- **Precomposing with a morphism all of whose `app`s are injective does
not shrink the kernel ideal sheaf** (PROVEN).

Together with `app_injective_specAlgClos` this is the fpqc-descent step
of leaf (ii), in the only form that leaf needs. -/
theorem ker_comp_le_of_app_injective {X Y Z : Scheme.{0}} (g : X ⟶ Y) (r : Y ⟶ Z)
    (hg : ∀ W : Y.Opens, Function.Injective (g.app W).hom) :
    (g ≫ r).ker ≤ r.ker := by
  refine Scheme.IdealSheafData.ofIdeals_mono fun U x hx => ?_
  rw [Scheme.Hom.comp_app g r U] at hx
  simp only [RingHom.mem_ker] at hx ⊢
  exact hg _ (hx.trans (map_zero _).symm)

/-! ### The five properties of the span that the descent leaf needs -/

/-- **The span of finitely many `ℚ̄`-points of a scheme locally of finite
type over `ℚ` is FINITE over `ℚ`** (PROVEN 2026-07-26; formerly leaf (i)
of the descent decomposition).

**PIN-SURVEY CORRECTION, 2026-07-26 — the survey below is STALE in its
load-bearing claim, and the correction is what closed this leaf.**  It
recorded `IsArtinianScheme X → IsAffine X` as "the genuine gap" that
`grep` does not find in the pin.  Two things are wrong with that:

* The implication IS in the pin, and needs no artinian theory to state:
  `AlgebraicGeometry.Limits.lean` carries
  `instance (priority := low) [Finite X] [DiscreteTopology X] : IsAffine X`,
  and `IsArtinianScheme` supplies both hypotheses
  (`IsArtinianScheme.finite`, `IsLocallyArtinian.discreteTopology`).  So
  the implication is `inferInstance`.
* More to the point, **it is not needed**.  No artinian scheme appears in
  the proof.

THE PROOF ACTUALLY USED, which is shorter than the route predicted below.
`IsFinite = IsProper ⊓ IsAffineHom` (`IsFinite.iff_isProper_and_isAffineHom`),
and properness is FREE here: `spanSchemeι p` is a closed immersion and `f`
is proper by `ab.proper`.  So the whole leaf collapses to
`IsAffine (spanScheme p)`, i.e. to `isAffine_spanScheme` above, and that
follows from the span's space being finite and `T1`.

Both of those come from ONE observation, `isIntegralHom_geomPt`: since
`p j ≫ f = specAlgClos ℚ` is integral and `f` is separated (being
proper), `p j` is integral by cancellation, hence a CLOSED map.  So each
`Set.range (p j)` is a single closed point, the support of the
scheme-theoretic image is contained in their finite union, and a finite
`T1` space is discrete.  Zariski's lemma, residue fields, number fields
and artinian rings all drop out of the argument entirely.

The original (correct but unnecessary) route is preserved below.

TRUE, and classical.  Each `ℚ̄`-point `p j` has image a point of `A` whose
residue field embeds in `ℚ̄`, hence is a finitely generated `ℚ`-algebra
which is a field, hence finite over `ℚ` by **Zariski's lemma** — so the
image point is CLOSED and its residue field is a number field.  The
scheme-theoretic image is therefore supported on a finite set of closed
points; being a closed subscheme of a locally-noetherian scheme with
discrete finite support it is an artinian scheme, hence affine, hence
`Spec` of a finite-dimensional `ℚ`-algebra.

WHAT IS MISSING AT THIS PIN, precisely — the survey is worth having
because the pieces are unusually close:

* `AlgebraicGeometry.IsArtinianScheme` exists (`AlgebraicGeometry/Artinian.lean`),
  with `IsArtinianScheme.finite` giving finiteness of the underlying type,
  and `IsLocallyArtinian.of_isImmersion` transporting along immersions.
* `IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` reduces the goal to
  `IsIntegralHom (spanSchemeι p ≫ f)`, and `LocallyOfFiniteType` of that
  composite is free (a closed immersion is of finite type, and `f` is
  smooth hence of finite type).
* ~~**The genuine gap is `IsArtinianScheme X → IsAffine X`** — an artinian
  scheme is a finite disjoint union of `Spec`s of artin local rings — which
  `grep` does not find anywhere in the pin.~~ **REFUTED 2026-07-26**: it is
  in the pin as `[Finite X] [DiscreteTopology X] → IsAffine X`, and it is
  not used here anyway.  See the correction at the head of this docstring.

Note this leaf does NOT need the family to be Galois-stable, and does not
mention the group law: it is a statement about an arbitrary finite family
of geometric points. -/
theorem isFinite_spanSchemeι {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) {J : Type} [Finite J]
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (hp : ∀ j, p j ≫ f = specAlgClos ℚ ≫ 𝟙 SpecQ) :
    IsFinite (spanSchemeι p ≫ f) := by
  have := isAffine_spanScheme ab p hp
  have hproper : IsProper (spanSchemeι p ≫ f) := by
    have := ab.proper
    infer_instance
  rw [IsFinite.iff_isProper_and_isAffineHom]
  exact ⟨hproper, inferInstance⟩

/-- **A `ℚ`-rational point of `A` whose associated `ℚ̄`-point is a member of
the family factors through the span** (PROVEN 2026-07-26; formerly leaf
(ii) of the descent decomposition).

HOW IT CLOSED, which is shorter than either route sketched below and uses
neither the reduced-induced structure nor a general fpqc-descent theorem.
`spanScheme p` is by construction `(geomPtDesc p).ker.subscheme`, so
`IdealSheafData.inclusion` turns the leaf into a comparison of KERNEL
IDEAL SHEAVES on `A`: it is enough that
`(geomPtDesc p).ker ≤ r.ker`.  That splits in two, and both halves are
cheap:

* `(geomPtDesc p).ker ≤ (p j).ker`, because `p j = Sigma.ι j ≫ geomPtDesc p`
  factors through the coproduct — this is mathlib's `Hom.le_ker_comp`;
* `(specAlgClos ℚ ≫ r).ker ≤ r.ker`, the actual descent.  It holds
  because EVERY `app` of `Spec ℚ̄ ⟶ Spec ℚ` is injective
  (`app_injective_specAlgClos`): `Spec ℚ` has exactly two opens, and on
  `⊤` injectivity is the `ΓSpecIso` naturality square applied to the
  injection `ℚ ↪ ℚ̄`.

NOTE ON HYPOTHESES: the proof uses NEITHER `ab` NOR `hr`, and does not
need `[Finite J]`.  They are kept because the statement is called with
them in place, but the fact is more general than advertised — the
factorisation descends for any morphism `r` out of `Spec ℚ` whose
`ℚ̄`-point is a member of the family, with no group structure and no
section condition.  This is not vacuity: the conclusion is a genuine
factorisation, and it is exactly what `zero_liesIn_of_ratPoint` consumes.

The original route sketch is preserved below.

TRUE.  `geomPt_liesIn_spanScheme` already gives the factorisation of the
`ℚ̄`-point `specAlgClos ℚ ≫ r` through `C`; what is asked here is that the
factorisation *descends* to `ℚ`, i.e. that the `ℚ`-point `r` itself lands in
the closed subscheme `C`.  That is the fpqc descent of a closed immersion
along the faithfully flat `Spec ℚ̄ ⟶ Spec ℚ`: `r` factors through the closed
subscheme `C` iff `r^{-1}(I_C) = 0`, and vanishing of a section of a sheaf
may be checked after a faithfully flat base change.

Equivalently and more cheaply: `C` is a closed subscheme and `r` is a
morphism from the REDUCED scheme `Spec ℚ` whose image lands in the support
of `C`, so `r` factors through the reduced induced structure on that
support — and `C` is reduced, being the scheme-theoretic image of a reduced
scheme.

This leaf is what discharges the `zero_liesIn` field, via
`zero_liesIn_of_ratPoint` below: the whole field at every base `T'` reduces
to this single `ℚ`-point, because the zero section at any base is the
zero section at `𝟙 SpecQ` precomposed with the base point. -/
theorem ratPoint_liesIn_spanScheme {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) {J : Type} [Finite J]
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (r : SpecQ ⟶ A) (hr : r ≫ f = 𝟙 SpecQ)
    (hgeom : ∃ j, p j = specAlgClos ℚ ≫ r) :
    ∃ w : SpecQ ⟶ spanScheme p, w ≫ spanSchemeι p = r := by
  obtain ⟨j, hj⟩ := hgeom
  -- (a) The span's kernel ideal sheaf is contained in that of each member of
  -- the family, because each member factors through `geomPtDesc p`.
  have ha : (geomPtDesc p).ker ≤ (p j).ker := by
    have h := Scheme.Hom.le_ker_comp
      (Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j)
      (geomPtDesc p)
    rwa [show Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j
        ≫ geomPtDesc p = p j from Limits.Sigma.ι_desc p j] at h
  -- (b) THE DESCENT STEP.
  have hb : (specAlgClos ℚ ≫ r).ker ≤ r.ker :=
    ker_comp_le_of_app_injective _ _ (app_injective_specAlgClos (F := ℚ))
  have hle : (geomPtDesc p).ker ≤ r.ker := ha.trans (hj ▸ hb)
  -- (c) A smaller kernel means the subscheme is LARGER, so `r`'s
  -- scheme-theoretic image sits inside the span, and `r` factors.
  refine ⟨r.toImage ≫ Scheme.IdealSheafData.inclusion hle, ?_⟩
  rw [Category.assoc]
  show r.toImage ≫ Scheme.IdealSheafData.inclusion hle
    ≫ (geomPtDesc p).ker.subschemeι = r
  rw [Scheme.IdealSheafData.inclusion_subschemeι]
  exact r.toImage_imageι

/-- **`zero_liesIn` at an ARBITRARY base reduces to the single `ℚ`-point
`ab.zero (𝟙 SpecQ)`** (PROVEN 2026-07-26).

This is the naturality axiom `pre_zero` read at `g = 𝟙 SpecQ`: the zero
section over any base `T'` is the zero section over `Spec ℚ` precomposed
with the structure morphism `g : T' ⟶ Spec ℚ`.  So one factorisation of
one `ℚ`-point through `C` gives the factorisation at every base at once,
and no separate descent argument is needed per base. -/
theorem zero_liesIn_of_ratPoint {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (w₀ : SpecQ ⟶ spanScheme p) (hw₀ : w₀ ≫ spanSchemeι p = (ab.zero (𝟙 SpecQ)).1)
    {T' : Scheme.{0}} (g : T' ⟶ SpecQ) :
    RelPoint.LiesIn (spanSchemeι p) (ab.zero g) := by
  refine ⟨g ≫ w₀, ?_⟩
  rw [Category.assoc, hw₀]
  have h := ab.pre_zero g (g := 𝟙 SpecQ) (g' := g) (Category.comp_id g)
  exact congrArg Subtype.val h

/-! ### Machinery for the three remaining leaves

**Added 2026-07-27**, and it is what turns leaves (iii)–(v) from
"rigidity between schemes" into ideal-sheaf bookkeeping.  The whole
subsection rests on three mathlib facts that were not being used:

* `Scheme.IdealSheafData.map_ker : f.ker.map g = (f ≫ g).ker` — the
  pushforward of the kernel ideal sheaf along `g` is the kernel of the
  composite.  With `map_bot : (⊥ : IdealSheafData X).map g = g.ker` this
  turns *every* "does this composite factor through the span" question
  into a computation with `ker`.
* `Scheme.Hom.ker_comp_of_isIso : [IsIso f] → (f ≫ g).ker = g.ker` —
  precomposing with an isomorphism does not change the kernel.
* `Scheme.IdealSheafData.subschemeMap I J f (H : J ≤ I.map f) :
  I.subscheme ⟶ J.subscheme` with
  `subschemeMap_subschemeι : subschemeMap … ≫ J.subschemeι = I.subschemeι ≫ f`
  — a morphism of the ambient scheme restricts to the subschemes exactly
  when the ideal-sheaf inequality holds.

Since `spanScheme p` is by definition `(geomPtDesc p).image`, i.e.
`(geomPtDesc p).ker.subscheme`, and `spanSchemeι p` is its `subschemeι`,
these apply verbatim.  **No reducedness, no rigidity and no Galois
category is needed for the inversion leaf**, which is proven outright
below; the docstring that predicted otherwise was wrong, and is
corrected there. -/

/-- **A permutation of the index set of a constant coproduct**, as an
automorphism of the coproduct.  Used to exhibit `d ≫ negHom ab` as
`(iso) ≫ d`, which is what makes the inversion leaf collapse. -/
noncomputable def sigmaPerm {J : Type} (Z : Scheme.{0}) (σ : J ≃ J) :
    (∐ fun _ : J => Z) ⟶ (∐ fun _ : J => Z) :=
  Limits.Sigma.desc (fun j => Limits.Sigma.ι (fun _ : J => Z) (σ j))

@[simp] theorem ι_sigmaPerm {J : Type} (Z : Scheme.{0}) (σ : J ≃ J) (j : J) :
    Limits.Sigma.ι (fun _ : J => Z) j ≫ sigmaPerm Z σ =
      Limits.Sigma.ι (fun _ : J => Z) (σ j) :=
  Limits.colimit.ι_desc _ _

theorem sigmaPerm_sigmaPerm {J : Type} (Z : Scheme.{0}) (σ : J ≃ J) :
    sigmaPerm Z σ ≫ sigmaPerm Z σ.symm = 𝟙 _ := by
  refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
  rw [← Category.assoc, ι_sigmaPerm, ι_sigmaPerm, Category.comp_id, Equiv.symm_apply_apply]

instance {J : Type} (Z : Scheme.{0}) (σ : J ≃ J) : IsIso (sigmaPerm Z σ) :=
  ⟨sigmaPerm Z σ.symm, sigmaPerm_sigmaPerm Z σ, by
    have h := sigmaPerm_sigmaPerm Z σ.symm
    rwa [Equiv.symm_symm] at h⟩

/-- **`j ↦ -j` on `Fin N`**, written with `%` so that it is total; it is
the index permutation matching inversion on `⟨y⟩ = {0•y, …, (N-1)•y}`. -/
def negIdx {N : ℕ} (hN : N ≠ 0) (j : Fin N) : Fin N :=
  ⟨(N - j.1) % N, Nat.mod_lt _ (Nat.pos_of_ne_zero hN)⟩

theorem negIdx_negIdx {N : ℕ} (hN : N ≠ 0) (j : Fin N) : negIdx hN (negIdx hN j) = j := by
  have hj := j.isLt
  refine Fin.ext ?_
  show (N - (N - j.1) % N) % N = j.1
  rcases Nat.eq_zero_or_pos j.1 with h | h
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega : N - j.1 < N), Nat.sub_sub_self (le_of_lt hj),
      Nat.mod_eq_of_lt hj]

/-- `negIdx` is an involution, hence a permutation of `Fin N`. -/
def negIdxEquiv {N : ℕ} (hN : N ≠ 0) : Fin N ≃ Fin N :=
  Function.Involutive.toPerm _ (negIdx_negIdx hN)

@[simp] theorem negIdxEquiv_apply {N : ℕ} (hN : N ≠ 0) (j : Fin N) :
    negIdxEquiv hN j = negIdx hN j := rfl

/-- **`negIdx` computes inversion on the multiples of an element of order
`N`.**  This is where `hN : N ≠ 0` is consumed on the inversion route. -/
theorem negIdx_nsmul {G : Type*} [AddCommGroup G] {N : ℕ} (hN : N ≠ 0) {y : G}
    (hy : addOrderOf y = N) (j : Fin N) :
    ((negIdx hN j : Fin N) : ℕ) • y = -((j : ℕ) • y) := by
  have h0 : (N : ℕ) • y = 0 := by rw [← hy]; exact addOrderOf_nsmul_eq_zero y
  have hmod := mod_addOrderOf_nsmul y (N - j.1)
  rw [hy] at hmod
  show ((N - j.1) % N) • y = -((j : ℕ) • y)
  rw [hmod]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← add_nsmul, Nat.sub_add_cancel (le_of_lt j.isLt), h0]

/-- **`y` itself is the `(1 % N)`-th multiple of `y`** — the statement is
written with `%` so that it also covers `N = 1`, where `y = 0`. -/
theorem one_mod_nsmul {G : Type*} [AddCommGroup G] {N : ℕ} {y : G}
    (hy : addOrderOf y = N) : (1 % N) • y = y := by
  have h := mod_addOrderOf_nsmul y 1
  rw [hy, one_nsmul] at h
  exact h

/-- **Every integer multiple of an element of order `N` is one of its `N`
natural multiples.**  This is what makes `AddSubgroup.zmultiples y` —
which is defined with `ℤ`-multiples — the image of the family
`zmulPts`, indexed by `Fin N`. -/
theorem exists_fin_zsmul {G : Type*} [AddCommGroup G] {N : ℕ} (hN : N ≠ 0) {y : G}
    (hy : addOrderOf y = N) (k : ℤ) :
    ∃ j : Fin N, (k • y : G) = ((j : ℕ) • y) := by
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h0 : 0 ≤ k % (N : ℤ) := Int.emod_nonneg k (by omega)
  have h1 : k % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos k hNpos
  have hlt : (k % (N : ℤ)).toNat < N := by omega
  have hmod := mod_addOrderOf_zsmul y k
  rw [hy] at hmod
  refine ⟨⟨(k % (N : ℤ)).toNat, hlt⟩, ?_⟩
  calc (k • y : G) = (k % (N : ℤ)) • y := hmod.symm
    _ = (((k % (N : ℤ)).toNat : ℤ)) • y := by rw [Int.toNat_of_nonneg h0]
    _ = ((k % (N : ℤ)).toNat) • y := natCast_zsmul _ _

/-- **Inversion permutes the family `zmulPts`** (PROVEN): `-(j • y)` is
`(N - j) • y`, so composing the `j`-th member with `negHom ab` gives the
`negIdx j`-th member. -/
theorem zmulPts_comp_negHom {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N) (j : Fin N) :
    zmulPts ab N y j ≫ negHom ab = zmulPts ab N y (negIdx hN j) := by
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  show (((j : ℕ) • y : GeomFibrePt f (𝟙 SpecQ))).1 ≫ negHom ab
      = ((((negIdx hN j : Fin N) : ℕ) • y : GeomFibrePt f (𝟙 SpecQ))).1
  rw [← neg_eq_negHom ab ((j : ℕ) • y), negIdx_nsmul hN hy j]
  rfl

/-- **`d ≫ negHom ab` is `d` precomposed with an automorphism of the
coproduct** (PROVEN), where `d = geomPtDesc (zmulPts ab N y)`.  This is
the whole content of the inversion leaf: it makes
`(d ≫ negHom ab).ker = d.ker` immediate. -/
theorem geomPtDesc_comp_negHom {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N) :
    geomPtDesc (zmulPts ab N y) ≫ negHom ab
      = sigmaPerm (Spec (CommRingCat.of (AlgebraicClosure ℚ))) (negIdxEquiv hN)
          ≫ geomPtDesc (zmulPts ab N y) := by
  have hd : ∀ k : Fin N,
      Limits.Sigma.ι (fun _ : Fin N => Spec (CommRingCat.of (AlgebraicClosure ℚ))) k ≫
        geomPtDesc (zmulPts ab N y) = zmulPts ab N y k := fun _ => Limits.colimit.ι_desc _ _
  refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
  simp only [← Category.assoc, hd, ι_sigmaPerm, negIdxEquiv_apply]
  exact zmulPts_comp_negHom ab N hN y hy j

/-- **`D ×_ℚ D ⟶ C ×_ℚ C` induced by a factorisation `q : D ⟶ C` of
`d : D ⟶ A` through `ι : C ⟶ A`.**  Written for a general `q` rather
than for `d.toImage` specifically, because `spanScheme p` is a `def`
rather than an `abbrev` and the two spellings of the scheme-theoretic
image do not rewrite into each other. -/
noncomputable def sqCover {A C D : Scheme.{0}} {f : A ⟶ SpecQ} {ι : C ⟶ A} {d : D ⟶ A}
    (q : D ⟶ C) (hq : q ≫ ι = d) :
    Limits.pullback (d ≫ f) (d ≫ f) ⟶ Limits.pullback (ι ≫ f) (ι ≫ f) :=
  Limits.pullback.map (d ≫ f) (d ≫ f) (ι ≫ f) (ι ≫ f) q q (𝟙 SpecQ)
    (by rw [Category.comp_id, ← Category.assoc, hq])
    (by rw [Category.comp_id, ← Category.assoc, hq])

@[simp] theorem sqCover_fst {A C D : Scheme.{0}} {f : A ⟶ SpecQ} {ι : C ⟶ A} {d : D ⟶ A}
    (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCover (f := f) q hq ≫ Limits.pullback.fst (ι ≫ f) (ι ≫ f)
      = Limits.pullback.fst (d ≫ f) (d ≫ f) ≫ q :=
  Limits.pullback.lift_fst _ _ _

@[simp] theorem sqCover_snd {A C D : Scheme.{0}} {f : A ⟶ SpecQ} {ι : C ⟶ A} {d : D ⟶ A}
    (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCover (f := f) q hq ≫ Limits.pullback.snd (ι ≫ f) (ι ≫ f)
      = Limits.pullback.snd (d ≫ f) (d ≫ f) ≫ q :=
  Limits.pullback.lift_snd _ _ _

theorem sqCover_sqMap {A C D : Scheme.{0}} {f : A ⟶ SpecQ} {ι : C ⟶ A} {d : D ⟶ A}
    (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCover (f := f) q hq ≫ sqMap ι = sqMap d := by
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [Category.assoc, sqMap_fst, ← Category.assoc, sqCover_fst, Category.assoc, hq, sqMap_fst]
  · rw [Category.assoc, sqMap_snd, ← Category.assoc, sqCover_snd, Category.assoc, hq, sqMap_snd]

/-- **The square of the span's tautological cover is schematically
dominant** (sorry leaf (iii-a), split out 2026-07-27).

`Σ = ∐_{Fin N} Spec ℚ̄ ⟶ C` is schematically dominant by construction —
`C` *is* the scheme-theoretic image — and `⊥` is its kernel
(`Hom.toImage_app_injective` is mathlib's form of this).  What is asked
here is that the fibre square of that map over `Spec ℚ` is again
schematically dominant.

TRUE, and it is commutative algebra, not geometry: over a field every
module is flat, so an injection `R ↪ S` of `ℚ`-algebras stays injective
after `- ⊗_ℚ -` with another injection, i.e. `R ⊗_ℚ R' ↪ S ⊗_ℚ S'`.
What has to be supplied at this pin is the passage from that ring
statement to `(sqCover q hq).ker = ⊥` for the *scheme* fibre product,
i.e. that the kernel ideal sheaf of a fibre product of morphisms over an
affine base is computed by the tensor product on affine charts.

CHECK THAT WOULD REFUTE THIS OBSTRUCTION: grep
`.lake/packages/mathlib` for a lemma bounding `Hom.ker` of
`Limits.pullback.map`, or for `ker` of a base change — e.g. names
containing `ker` together with `pullback`/`baseChange`. Two nearby
candidates that do NOT suffice on their own are
`Scheme.IdealSheafData.ker_fst_of_isClosedImmersion` (the wrong shape:
one leg a closed immersion) and `comap_bot` (the wrong direction).

Note this leaf mentions neither `y`, nor `N`, nor the group law: it is a
statement about an arbitrary finite family of geometric points. -/
theorem ker_sqCover_spanScheme {A : Scheme.{0}} {f : A ⟶ SpecQ} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (q : geomPtSigma J ⟶ spanScheme p) (hq : q ≫ spanSchemeι p = geomPtDesc p) :
    (sqCover (f := f) q hq).ker = ⊥ :=
  sorry

/-- **The group law carries the square of the geometric-point family into
the span** (sorry leaf (iii-b), split out 2026-07-27 — this is the half
of leaf (iii) that carries the arithmetic).

`Σ ×_ℚ Σ = ∐_{j,k} Spec (ℚ̄ ⊗_ℚ ℚ̄)`, and the composite into `A` is
`ab.add` of the two points `p j`, `p k` pulled back along the two
*different* projections.  Every point of `Spec (ℚ̄ ⊗_ℚ ℚ̄)` has residue
field `ℚ̄` (the ring is integral over each factor and `ℚ̄` is
algebraically closed), and the corresponding `ℚ̄`-point of `A` is
`p j + σ (p k)` for the `σ ∈ Γ_ℚ` that the point encodes.

**This is exactly, and only, where `hstable` is consumed on the addition
route**: `σ (p k) = σ • (k • y) ∈ ⟨y⟩` by `hstable`, so the sum lies in
`⟨y⟩` and hence in `C`.  Note `hstable` is *not* needed anywhere else in
leaf (iii): the reduction of leaf (iii) to this statement
(`ker_sqCover_spanScheme` plus `Scheme.IdealSheafData.map_ker`) is
formal.

CHECK THAT WOULD REFUTE THE "Galois is unavoidable here" READING: exhibit
a factorisation of `Spec (ℚ̄ ⊗_ℚ ℚ̄) ⟶ Spec ℚ̄ ×_ℚ Spec ℚ̄` through a
`Γ_ℚ`-free description of the points — none is expected, since dropping
`hstable` makes the statement FALSE (take `y` a point whose Galois orbit
leaves `⟨y⟩`; then `C` is bigger than `⟨y⟩` and the sum of two of its
geometric points need not lie in it). -/
theorem exists_addHom_factor_geomSq {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y) :
    ∃ κ : Limits.pullback (geomPtDesc (zmulPts ab N y) ≫ f)
            (geomPtDesc (zmulPts ab N y) ≫ f) ⟶ spanScheme (zmulPts ab N y),
      κ ≫ spanSchemeι (zmulPts ab N y)
        = sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab :=
  sorry

/-- **The group law of `A` restricts to the span: the factorisation at
`C ×_ℚ C`** (sorry leaf (iii) of the descent decomposition).

TRUE, and this is the rigidity half of "`C` is a subgroup SCHEME rather
than merely a subgroup of geometric points".

NOTE THE SHAPE.  This leaf asks for ONE morphism, with no quantification
over test schemes.  That is deliberate, and it is the whole reason the
Yoneda subsection above exists: the `add_liesIn` field quantifies over
every base `T'`, including non-reduced ones where rigidity is FALSE, so it
cannot be attacked base by base.  `add_eq_addHom` turns every instance of
the field into a composite with the single morphism `addHom ab`, and
`add_liesIn_of_factor` then derives the whole field from the factorisation
asked for here.  So the successor closing this leaf never has to think
about a general `T'`.

**PROVEN 2026-07-27 over the two leaves `ker_sqCover_spanScheme` and
`exists_addHom_factor_geomSq` above.**  The route recorded below —
reducedness of `C ×_ℚ C`, then
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated` — is NOT the one
taken, and is not needed:

> `C ×_ℚ C` is reduced — over `ℚ`, `C` is finite étale, and a product of
> étale `ℚ`-schemes is étale hence reduced — and `A` is separated, being
> proper over `ℚ`.  The composite `C ×_ℚ C ⟶ A ×_ℚ A ⟶ A` agrees on
> geometric points with a morphism landing in `C`.

What replaces it is ideal-sheaf bookkeeping.  Write `d` for
`geomPtDesc (zmulPts ab N y)` and `q` for its factorisation through the
span.  Then `sqCover q ≫ sqMap ι = sqMap d` (`sqCover_sqMap`), and

* `(sqCover q).ker = ⊥` (leaf iii-a) gives, via
  `Scheme.IdealSheafData.map_ker` and `map_bot`,
  `(sqCover q ≫ g).ker = g.ker` for every `g` out of `C ×_ℚ C` — this is
  the *only* place the "dominant plus reduced" input is used, and it is
  now isolated in a statement with no group law in it;
* leaf (iii-b) factors `sqMap d ≫ addHom ab` through `ι`, so
  `ι.ker ≤ (sqMap d ≫ addHom ab).ker` by `Scheme.Hom.le_ker_comp`.

Combining the two gives `ι.ker ≤ (sqMap ι ≫ addHom ab).ker`, and
`IsClosedImmersion.lift` produces `μ`.

`hstable` enters exactly once, inside leaf (iii-b): it is what makes
`⟨y⟩` a `Γ_ℚ`-submodule, hence `C` defined over `ℚ` at all. -/
theorem exists_addHom_factor_zmulPts {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y) :
    ∃ μ : Limits.pullback (spanSchemeι (zmulPts ab N y) ≫ f)
            (spanSchemeι (zmulPts ab N y) ≫ f) ⟶ spanScheme (zmulPts ab N y),
      μ ≫ spanSchemeι (zmulPts ab N y)
        = sqMap (spanSchemeι (zmulPts ab N y)) ≫ addHom ab := by
  obtain ⟨κ, hκ⟩ := exists_addHom_factor_geomSq ab N hN y hy hstable
  obtain ⟨q, hq⟩ : ∃ q : geomPtSigma (Fin N) ⟶ spanScheme (zmulPts ab N y),
      q ≫ spanSchemeι (zmulPts ab N y) = geomPtDesc (zmulPts ab N y) :=
    ⟨(geomPtDesc (zmulPts ab N y)).toImage, (geomPtDesc (zmulPts ab N y)).toImage_imageι⟩
  have hcov := ker_sqCover_spanScheme (f := f) (zmulPts ab N y) q hq
  have hstep : (sqCover (f := f) q hq ≫
        (sqMap (spanSchemeι (zmulPts ab N y)) ≫ addHom ab)).ker
      = (sqMap (spanSchemeι (zmulPts ab N y)) ≫ addHom ab).ker := by
    rw [← Scheme.IdealSheafData.map_ker, hcov, Scheme.IdealSheafData.map_bot]
  have hle : (spanSchemeι (zmulPts ab N y)).ker
      ≤ (sqMap (spanSchemeι (zmulPts ab N y)) ≫ addHom ab).ker := by
    rw [← hstep, ← Category.assoc, sqCover_sqMap q hq, ← hκ]
    exact Scheme.Hom.le_ker_comp _ _
  exact ⟨IsClosedImmersion.lift _ _ hle, IsClosedImmersion.lift_fac _ _ _⟩

/-- **Inversion restricts to the span: the factorisation at `C`** (sorry
leaf (iv) of the descent decomposition).

**PROVEN 2026-07-27, and NOT by the route this docstring used to
predict.**  It used to say:

> Same mechanism as `exists_addHom_factor_zmulPts`, one step shorter: the
> rigidity step happens at `C` itself rather than at `C ×_ℚ C`, because
> `negHom ab ∘ ι` agrees on geometric points with a morphism into `C`.

There is **no rigidity step at all**, and no reducedness, no separatedness
and no Galois input: the proof is three lines of ideal-sheaf algebra.
Inversion *permutes the defining family* rather than merely preserving its
span — `-(j • y) = (N - j) • y` — so

    geomPtDesc p ≫ negHom ab  =  sigmaPerm (negIdxEquiv hN) ≫ geomPtDesc p

(`geomPtDesc_comp_negHom`) with `sigmaPerm …` an **isomorphism** of
`∐_{Fin N} Spec ℚ̄`.  Hence, by `Scheme.IdealSheafData.map_ker` and
`Scheme.Hom.ker_comp_of_isIso`,

    (geomPtDesc p).ker.map (negHom ab) = (geomPtDesc p ≫ negHom ab).ker
                                       = (geomPtDesc p).ker,

and `Scheme.IdealSheafData.subschemeMap` turns that equality of ideal
sheaves into the required `ν`.  `neg_liesIn_of_factor` then derives the
`neg_liesIn` field at every base from this one factorisation.

**`hstable` is NOT used** — hence the underscore.  That is not an
oversight: closure of `⟨y⟩` under negation is a property of a cyclic
group, needing no Galois stability, and the ideal-sheaf route never leaves
the family.  `hN` and `hy` *are* consumed, inside `negIdx_nsmul`, which is
what identifies `-(j • y)` with a member of the family.

Note the asymmetry with leaf (iii), which is real rather than an artefact
of how hard anyone tried: addition is a map out of `C ×_ℚ C`, whose
tautological cover `∐_{j,k} Spec (ℚ̄ ⊗_ℚ ℚ̄)` genuinely leaves the family,
and it is exactly there that `hstable` becomes indispensable. -/
theorem exists_negHom_factor_zmulPts {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (_hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y) :
    ∃ ν : spanScheme (zmulPts ab N y) ⟶ spanScheme (zmulPts ab N y),
      ν ≫ spanSchemeι (zmulPts ab N y)
        = spanSchemeι (zmulPts ab N y) ≫ negHom ab := by
  have key : (geomPtDesc (zmulPts ab N y)).ker.map (negHom ab)
      = (geomPtDesc (zmulPts ab N y)).ker := by
    rw [Scheme.IdealSheafData.map_ker, geomPtDesc_comp_negHom ab N hN y hy]
    exact Scheme.Hom.ker_comp_of_isIso _ _
  exact ⟨Scheme.IdealSheafData.subschemeMap _ _ (negHom ab) key.ge,
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _⟩

/-- **A geometric base point over an arbitrary algebraically closed base,
inducing an injection on relative points** (sorry leaf (v-a), split out
2026-07-27).

Two things at once, because they are proven by the same object.  `K` is
algebraically closed and `t : Spec K ⟶ Spec ℚ` makes it a `ℚ`-algebra, so
`ℚ̄` embeds in `K` (`IsAlgClosed.lift`, `ℚ̄/ℚ` being algebraic); `e` is
`Spec` of such an embedding.  And precomposition with `e` is injective on
`Hom(Spec ℚ̄, A)` because `e` is `Spec` of an *injective* map of fields:
both `Spec ℚ̄` and `Spec K` are one-point schemes with the same image point
in `A`, so both morphisms factor through one affine open `U ∋ that point`,
where they are ring maps `Γ(U) → ℚ̄` that become equal after composing with
the injection `ℚ̄ ↪ K`.

TWO TRAPS RECORDED FOR THE SUCCESSOR, both already paid for elsewhere in
this development:

* **State the embedding lemma over a VARIABLE base field and instantiate
  at `ℚ`.**  At the literal `ℚ`, `Algebra ℚ (AlgebraicClosure ℚ)` resolves
  to the `Rat`-algebra diamond rather than `AlgebraicClosure.instAlgebra`,
  and `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` then fails to
  synthesize *with every import present*.  `isIntegralHom_specAlgClos` in
  this very file is stated over a variable field for exactly this reason.
* The `ℚ`-algebra structure on `K` must be read off `t` (via `Spec`'s full
  faithfulness, or `ΓSpecIso` and `t.appTop`); `K` carries no `CharZero`
  instance a priori, and it is `t` that supplies it.

CHECK THAT WOULD REFUTE THE INJECTIVITY HALF being genuine work: find a
mathlib lemma giving `Epi (Spec.map φ)` for `φ` an injective ring map, or
`Function.Injective ((· ≫ ·) (Spec.map φ))`; a grep for `Epi` together
with `Spec.map` found none at this pin. -/
theorem exists_injective_pre_geomBase {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ SpecQ) :
    ∃ (e : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (he : e ≫ (specAlgClos ℚ ≫ 𝟙 SpecQ) = t),
      Function.Injective (fun x : GeomFibrePt f (𝟙 SpecQ) => RelPoint.pre e he x) :=
  sorry

/-- **Every `K`-point of the span is an integer multiple of the geometric
generator** (sorry leaf (v-b), split out 2026-07-27 — THE CRUX of leaf
(v), and the only half of it that carries arithmetic).

The reverse inclusion is proven in `geom_cyclic_zmulPts` below from
`exists_fin_zsmul` and `geomPt_liesIn_spanScheme`; this is the hard
direction, `C(K) ⊆ ⟨y⟩`.

WHY IT IS TRUE.  `C` is the scheme-theoretic image of `∐_{Fin N} Spec ℚ̄`,
so `Γ(C) =: R` injects into `∏_{Fin N} ℚ̄`; `R` is therefore a *reduced*
finite-dimensional `ℚ`-algebra, i.e. a finite product of number fields
`∏ κ_i`, and its maximal ideals are exactly the kernels of the `N`
coordinate maps (a proper sub-family of the factors would have nonzero
intersection of kernels, contradicting injectivity).  A `K`-point of `C`
is a `ℚ`-algebra map `R → K`; its kernel is one of those maximal ideals,
so the point is `σ ∘ (j • y)` for some embedding `σ`.  `hstable` says
exactly that such a translate is again in `⟨y⟩`.

CORRECTION TO THE PREVIOUS AUDIT, which is why this is a leaf and not a
blocked node: the parent docstring recorded "the computation of
`Hom_ℚ(Spec K, C)` for `C` finite over `ℚ`" as MISSING and reached for
`CommAlgCat.FiniteEtale.equivOfIsSepClosed`.  Neither is needed —
`AlgebraicGeometry.pointEquivClosedPoint` together with finiteness of `C`
over `ℚ` (leaf (i), `isFinite_spanSchemeι`) describes the points directly,
and no Galois *category* appears anywhere above; only the Galois *action*
on `ℚ̄`, which `hstable` already speaks about.

CHECK THAT WOULD REFUTE THE REMAINING OBSTRUCTION: exhibit the
decomposition `R ≅ ∏ κ_i` in the pin — grep for
`Algebra.equivProdOfIsArtinian`-style splittings of reduced artinian
algebras, or for `IsArtinianRing.equivPi`; if such a splitting is
available for a reduced finite `ℚ`-algebra, the rest of this leaf is
finite bookkeeping. -/
theorem mem_zmultiples_of_liesIn_span {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y)
    (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ SpecQ)
    (e : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (he : e ≫ (specAlgClos ℚ ≫ 𝟙 SpecQ) = t)
    (x : RelPoint f t) (hx : RelPoint.LiesIn (spanSchemeι (zmulPts ab N y)) x) :
    letI := ab.addCommGroup t
    x ∈ AddSubgroup.zmultiples (RelPoint.pre e he y) :=
  sorry

/-- **The geometric fibres of the span are cyclic of order exactly `N`**
(sorry leaf (v) of the descent decomposition — THE CRUX).

TRUE.  Over `ℚ̄` the span is split: `C_{ℚ̄} = ∐_{s ∈ ⟨y⟩} Spec ℚ̄`, because
the scheme-theoretic image of `∐_{⟨y⟩} Spec ℚ̄ ⟶ A` is `Spec` of the
product of the residue fields of the `Γ_ℚ`-orbits, and base change to `ℚ̄`
splits each orbit into its individual points.  So `C(ℚ̄) = ⟨y⟩`, cyclic of
order `addOrderOf y = N`.

WHY THE STATEMENT QUANTIFIES OVER EVERY ALGEBRAICALLY CLOSED `K`, and why
that is not a strengthening.  `ℚ` is initial among commutative rings, so
the base point `t : Spec K ⟶ Spec ℚ` is unique and carries no data.  The
algebraic closure of `ℚ` inside `K` is a copy of `ℚ̄`, over which `C` is
already split, and a `K`-point of a scheme that is a finite product of
number fields is determined by a `ℚ̄`-point; so `C(K) = C(ℚ̄) = ⟨y⟩` with
the same order `N`.  The generator `z` produced at `K` is the image of `y`
under any embedding `ℚ̄ ↪ K` — a choice, but the resulting SUBGROUP is
independent of it because `⟨y⟩` is `Γ_ℚ`-stable, which is exactly what
`hstable` supplies.

**PROVEN 2026-07-27 over the two leaves `exists_injective_pre_geomBase`
and `mem_zmultiples_of_liesIn_span` above.**  The generator is produced
explicitly: `z := RelPoint.pre e y` for `e : Spec K ⟶ Spec ℚ̄` any
embedding over `ℚ`.  Of the three conjuncts,

* `RelPoint.LiesIn ι z` is `geomPt_liesIn_spanScheme` at the index
  `1 % N` — written with `%` so that it also covers `N = 1`, where
  `y = 0`;
* `addOrderOf z = N` is `addOrderOf_injective` applied to the additive
  map `RelPoint.pre e`, whose additivity is `pre_zero`/`pre_add` and whose
  injectivity is leaf (v-a).  **This is the second place `hN` is
  load-bearing**: without `N ≠ 0` the index `1 % N` is not available and
  the order statement is the false one refuted at the parent;
* the `←` direction of the membership equivalence is `exists_fin_zsmul`
  (every `ℤ`-multiple of an element of order `N` is one of its `N`
  natural multiples) followed by `geomPt_liesIn_spanScheme`.

Only the `→` direction — `C(K) ⊆ ⟨z⟩` — is left, as leaf (v-b).

CORRECTION TO THE PREVIOUS AUDIT.  This docstring used to record as
MISSING "the identification of the base change of a scheme-theoretic image
with the scheme-theoretic image of the base change, plus the computation
of `Hom_ℚ(Spec K, C)`", and to call this "the one leaf of the five that
genuinely needs the finite-étale/Galois-set correspondence", reaching for
`CommAlgCat.FiniteEtale.equivOfIsSepClosed`.  **Both halves of that are
wrong.**  No base change of a scheme-theoretic image occurs anywhere in
the proof above, and no Galois category is used: `pointEquivClosedPoint`
plus finiteness of `C` over `ℚ` (leaf (i)) describes `C(K)` directly.  See
`mem_zmultiples_of_liesIn_span` for what is actually left. -/
theorem geom_cyclic_zmulPts {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y)
    (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ SpecQ) :
    letI := ab.addCommGroup t
    ∃ z : RelPoint f t, RelPoint.LiesIn (spanSchemeι (zmulPts ab N y)) z ∧
      addOrderOf z = N ∧
      ∀ x : RelPoint f t, RelPoint.LiesIn (spanSchemeι (zmulPts ab N y)) x ↔
        x ∈ AddSubgroup.zmultiples z := by
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  letI := ab.addCommGroup t
  obtain ⟨e, he, hinj⟩ := exists_injective_pre_geomBase (f := f) K t
  let Φ : GeomFibrePt f (𝟙 SpecQ) →+ RelPoint f t :=
    { toFun := fun x => RelPoint.pre e he x
      map_zero' := ab.pre_zero e he
      map_add' := fun a b => ab.pre_add e he a b }
  have hΦinj : Function.Injective Φ := fun a b h => hinj h
  have hliesIn : ∀ j : Fin N, RelPoint.LiesIn (spanSchemeι (zmulPts ab N y))
      (Φ (((j : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))) := by
    intro j
    obtain ⟨w, hw⟩ := geomPt_liesIn_spanScheme (zmulPts ab N y) j
    exact ⟨e ≫ w, by rw [Category.assoc, hw]; rfl⟩
  refine ⟨Φ y, ?_, ?_, ?_⟩
  · have h1 : ((⟨1 % N, Nat.mod_lt _ (Nat.pos_of_ne_zero hN)⟩ : Fin N) : ℕ) • y = y :=
      one_mod_nsmul hy
    have h2 := hliesIn ⟨1 % N, Nat.mod_lt _ (Nat.pos_of_ne_zero hN)⟩
    rwa [h1] at h2
  · rw [← hy]
    exact addOrderOf_injective Φ hΦinj y
  · intro x
    refine ⟨fun hx => mem_zmultiples_of_liesIn_span ab N hN y hy hstable K t e he x hx, ?_⟩
    rintro ⟨k, rfl⟩
    obtain ⟨j, hj⟩ := exists_fin_zsmul hN hy k
    have hz : (k • Φ y : RelPoint f t) = Φ ((k : ℤ) • y) := (map_zsmul Φ k y).symm
    show RelPoint.LiesIn (spanSchemeι (zmulPts ab N y)) (k • Φ y)
    rw [hz, hj]
    exact hliesIn j

/-- **Galois descent: a Galois-stable cyclic subgroup of the geometric
points of an abelian scheme over `ℚ` is cut out by a closed cyclic
subgroup scheme** (PROVEN 2026-07-26 from the five leaves of the
subsection above; formerly a single sorry node).

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
* ~~no construction of the reduced induced closed subscheme structure on a
  closed subset of a scheme (`grep` over `AlgebraicGeometry/` finds no
  `reducedSubscheme` of any spelling)~~ — **CORRECTED 2026-07-26.  The
  survey searched for the wrong name.**  `AlgebraicGeometry.Scheme.Hom.image`
  (`IdealSheaf/Subscheme.lean:650`) is the *scheme-theoretic image* of a
  morphism, with `Hom.imageι` the closed immersion into the target,
  `Hom.toImage` the factorisation, `Hom.toImage_imageι` their composite,
  and `IsDominant (Hom.toImage f)` for quasi-compact `f`.  That is exactly
  the construction this leaf needed, and taking it at the morphism
  `∐_{s ∈ ⟨y⟩} Spec ℚ̄ ⟶ A` builds `C` directly.  It is now used below;
  see `Fermat.spanScheme`.

So the honest cut for a successor is no longer "build the reduced induced
structure": `C` and `ι` are CONSTRUCTED below, and what remains are the
five properties of that specific `C` listed in the decomposition note.
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
here.  CONFIRMED 2026-07-26: `flat` is discharged below by
`inferInstance`, from mathlib's `[Subsingleton Y] [IsIntegral Y] → Flat f`.

## DECOMPOSITION, 2026-07-26 — this node is now PROVEN, over five leaves

`C` and `ι` are no longer existential.  They are
`spanScheme (zmulPts ab N y)` and `spanSchemeι (zmulPts ab N y)`: the
scheme-theoretic image of `∐_{k < N} Spec ℚ̄ ⟶ A` assembled from the `N`
multiples of `y`.  Of the eight fields of `CyclicSubgroupOfOrder`, three
are discharged here and five became named leaves:

| field | status |
|---|---|
| `C`, `ι` | CONSTRUCTED (`spanScheme`, `spanSchemeι`) |
| `isClosedImmersion` | PROVEN — mathlib instance on `subschemeι` |
| `flat` | PROVEN — base is a one-point integral scheme |
| `zero_liesIn` | PROVEN from leaf (ii), via `zero_liesIn_of_ratPoint` |
| `isFinite` | leaf (i) `isFinite_spanSchemeι` |
| `add_liesIn` | PROVEN from leaf (iii), via `add_liesIn_of_factor` |
| `neg_liesIn` | PROVEN from leaf (iv), via `neg_liesIn_of_factor` |
| `geom_cyclic` | leaf (v) `geom_cyclic_zmulPts` — the crux |

**STATUS 2026-07-27.**  Leaf (iv) is now PROVEN outright, and leaves (iii)
and (v) are proven over four smaller leaves.  The state of the five is:

| leaf | status |
|---|---|
| (i) `isFinite_spanSchemeι` | open |
| (ii) `ratPoint_liesIn_spanScheme` | open |
| (iii) `exists_addHom_factor_zmulPts` | PROVEN over (iii-a), (iii-b) |
| (iv) `exists_negHom_factor_zmulPts` | **PROVEN** — no leaf |
| (v) `geom_cyclic_zmulPts` | PROVEN over (v-a), (v-b) |
| (iii-a) `ker_sqCover_spanScheme` | open — a fibre square of schematically dominant maps over `ℚ` |
| (iii-b) `exists_addHom_factor_geomSq` | open — the addition law on `∐ Spec (ℚ̄ ⊗_ℚ ℚ̄)`; the only consumer of `hstable` |
| (v-a) `exists_injective_pre_geomBase` | open — `ℚ̄ ↪ K` and injectivity of precomposition |
| (v-b) `mem_zmultiples_of_liesIn_span` | open — `C(K) ⊆ ⟨y⟩`; the crux |

The route recorded here before that date said "(iii) and (iv) are the
rigidity of morphisms out of a reduced scheme into a separated one; (v) is
the split finite-étale computation of `C(K)`".  **All three clauses were
wrong**, and each cost less than it looked:

* (iv) needs *no* rigidity, no reducedness and no `hstable` — inversion
  permutes the defining family, so the ideal sheaf is literally
  preserved;
* (iii) needs rigidity only through leaf (iii-a), a statement with no
  group law in it, and its arithmetic is concentrated in (iii-b);
* (v) needs no finite-étale/Galois-set correspondence at all.

(i) is still Zariski's lemma plus "an artinian scheme is affine" — though
see its own docstring, where the "genuine gap" it names is itself
retracted — and (ii) is still fpqc descent of a point along `ℚ̄/ℚ`.  Each
leaf carries its own route, and its own refuting check, in its
docstring.

**NONE OF THE FIVE QUANTIFIES OVER A TEST SCHEME**, and that is the single
most useful thing the decomposition does.  Three of the eight fields
(`zero_liesIn`, `add_liesIn`, `neg_liesIn`) are stated at EVERY base `T'`,
including non-reduced ones where the rigidity argument that proves them is
outright false.  The Yoneda subsection above (`addHom`, `negHom`,
`add_eq_addHom`, `neg_eq_negHom`) collapses each of those fields to a
single morphism-level factorisation — leaves (ii), (iii), (iv) — so a
successor works with reduced schemes only, where the argument is valid.
Getting this wrong is the obvious way to attack the node and it does not
work. -/
theorem exists_cyclicSubgroupOfOrder_of_galoisStable {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y) :
    Nonempty (CyclicSubgroupOfOrder ab N) := by
  classical
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  -- The zero of the geometric fibre is the `0`-th multiple of `y`, hence a
  -- member of the family; `hN` is what makes `⟨0, _⟩ : Fin N` available, and
  -- this is the one place the repaired hypothesis is consumed.
  have hzero : zmulPts ab N y ⟨0, Nat.pos_of_ne_zero hN⟩
      = specAlgClos ℚ ≫ (ab.zero (𝟙 SpecQ)).1 := by
    have h := ab.pre_zero (specAlgClos ℚ) (g := 𝟙 SpecQ)
      (g' := specAlgClos ℚ ≫ 𝟙 SpecQ) rfl
    show ((0 : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)).1 = _
    rw [zero_smul]
    exact congrArg Subtype.val h.symm
  obtain ⟨w₀, hw₀⟩ := ratPoint_liesIn_spanScheme ab (zmulPts ab N y)
    (ab.zero (𝟙 SpecQ)).1 (ab.zero (𝟙 SpecQ)).2 ⟨_, hzero⟩
  obtain ⟨μ, hμ⟩ := exists_addHom_factor_zmulPts ab N hN y hy hstable
  obtain ⟨ν, hν⟩ := exists_negHom_factor_zmulPts ab N hN y hy hstable
  exact ⟨{ C := spanScheme (zmulPts ab N y)
           ι := spanSchemeι (zmulPts ab N y)
           isClosedImmersion := inferInstance
           isFinite := isFinite_spanSchemeι ab (zmulPts ab N y) (zmulPts_comp ab N y)
           flat := inferInstance
           zero_liesIn := fun g => zero_liesIn_of_ratPoint ab _ w₀ hw₀ g
           add_liesIn := fun hx hz => add_liesIn_of_factor ab _ μ hμ hx hz
           neg_liesIn := fun hx => neg_liesIn_of_factor ab _ ν hν hx
           geom_cyclic := fun K _ _ t => geom_cyclic_zmulPts ab N hN y hy hstable K t }⟩

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

/-- **Kenku's prime-square determination, on `X_0(p²)` for `p ≥ 11`**
(sorry node, introduced 2026-07-26): every rational point of `X_0(p²)` is
a cusp, for every prime `p ≥ 11`.

TRUE, and it is Kenku's theorem.  The Mazur–Kenku list of levels `N` with
`Y_0(N)(ℚ) ≠ ∅` is

    1, …, 19, 21, 25, 27, 37, 43, 67, 163,

whose largest element is `163`; and for a prime `p ≥ 11` the level `p²` is
at least `121`, is a perfect square, and is therefore in the list only if
it is one of `1, 4, 9, 16` — all of which are `< 121`.  So `p² ` is outside
the list for EVERY prime `p ≥ 11`, uniformly, with no case analysis.

**Why `11 ≤ p` and not merely `p` prime.**  The bound is sharp at both
ends of the small range: `4`, `9` and `25` are all IN the Mazur–Kenku
list, so the statement is FALSE at `p = 2, 3, 5`.  (`p = 7` gives `49`,
which is outside the list, so the statement happens to be true there too —
but `49` is the separate concern of `MazurLevelFortyNine` and is left to
it rather than folded in here.)

**Why this node exists.**  It is the modular-curve form of the missing
half of the level-`p` ⟷ level-`p²` dictionary.
`FreyCurve/MazurTorsion.lean` already carries that dictionary in ONE
direction: `not_cyclicIsogeny_sq_of_jInvariant` builds two distinct
Galois-stable lines of order `p` on a Vélu quotient out of a cyclic
`p²`-subgroup, and so is proven FROM the level-`p` leaf
`not_two_stable_lines_of_jInvariant`.  Feeding that implication back would
be circular.  Routing the CONVERSE through this node instead is not: the
statement below is about the modular curve, is independent of both
elliptic-curve leaves, and is exactly the shape in which Kenku proves it.

IRREDUCIBLE at this pin, for the same reason as every other level node
here: `X_0(p²)` has genus `≥ 6` for `p ≥ 11` (already `X_0(121)` has genus
`6`), so this is a determination of the rational points of a curve of high
genus, and neither `J_0(N)`, nor its Mordell–Weil group, nor
Chabauty–Coleman exists in this development.  Sources: Kenku, *The modular
curves `X_0(65)` and `X_0(91)` and rational isogeny*, Math. Proc.
Cambridge Philos. Soc. **87** (1980); *On the modular curves `X_0(125)`,
`X_1(25)` and `X_1(49)`*, J. London Math. Soc. (2) **23** (1981);
*The modular curve `X_0(169)` and rational isogeny*, J. London Math. Soc.
(2) **22** (1980).

Quantified over every model of `IsCompactificationY0`, so it is at least
as strong as the `Y_0(p²)` statement it carries and cannot be discharged
by a degenerate choice of `X`. -/
theorem cuspidal_x0_isogenyPrimeSq {p : ℕ} (_hp : p.Prime) (_hp11 : 11 ≤ p)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (_hc : IsCoarseModuliY0 (p ^ 2) strY) (hX : IsCompactificationY0 strY strX)
    (x : RelPoint strX (𝟙 SpecQ)) : hX.IsCusp x :=
  sorry

/-- **`Y_0(p²)(ℚ) = ∅` for every prime `p ≥ 11`** (PROVEN 2026-07-26 over
`cuspidal_x0_isogenyPrimeSq`, the same compactification route
`y0HasNoRationalPoint_prime` takes).

This is the node that closes
`WeierstrassCurve.not_two_stable_lines_of_jInvariant` in
`FreyCurve/MazurTorsion.lean`: two DISTINCT Galois-stable lines of order
`p` on `E` produce, on the Vélu quotient `E/⟨h₁⟩`, a Galois-stable CYCLIC
subgroup of order `p²`, which `false_of_stable_of_y0HasNoRationalPoint`
then contradicts.  See that leaf for the construction.

Note `y0HasNoRationalPoint_of_dvd` does NOT reach `p²`: its only proper
divisor is `p`, and `Y_0(p)(ℚ) ≠ ∅` for `p ∈ {11, 17, 19, 37, 43, 67,
163}` — which is precisely why the seven isogeny primes need Kenku and not
merely Mazur. -/
theorem y0HasNoRationalPoint_isogenyPrimeSq {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    Y0HasNoRationalPoint (p ^ 2) := by
  obtain ⟨Y, strY, ⟨hc⟩⟩ := exists_coarseModuliY0 (p ^ 2)
  obtain ⟨X, strX, ⟨hX⟩⟩ := exists_compactificationY0 hc
  exact y0HasNoRationalPoint_of_cuspidal hc hX (cuspidal_x0_isogenyPrimeSq hp hp11 hc hX)

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

/-! ### The `j`-map, and the `v_q(j) < 0 ⟹ cuspidal reduction` dictionary

The layer this subsection adds is the one Mazur's Cor. 4.4 opens with:
*"potentially multiplicative reduction at `q` means `v_q(j(x)) < 0`, so
`x` reduces mod `q` to a cusp"*.  Before 2026-07-27 there was no `j`-map
on `X_0(N)` anywhere in this development — `grep jInvariant`/`jMap` over
the tree returned only `WeierstrassCurve`-side hits — and `redX` was
constrained by nothing but `red_aj`, so the sentence could not even be
stated, let alone proved.  Both halves are supplied here.

**Why the `j`-map is a map of POINTS and not a morphism of schemes.**
`IsX0ReductionAt` already presents reduction as a bare function
`RelPoint strX (𝟙 SpecQ) → RelPoint strX' (𝟙 (SpecF ℓ))` rather than as a
morphism, because the integral model that would induce it does not exist
at this pin.  The `j`-map is presented the same way and for the same
reason; carrying it as `Y ⟶ 𝔸¹_ℚ` would additionally require the
identification `Γ(Spec ℚ, 𝒪) ≅ ℚ` at every use site and would pin
nothing extra, since every statement below evaluates it at a rational
point.

**What pins `jm`, and why the pinning is an EXISTENCE statement.**  The
tempting field is the equation `jm (hc.classify d) = E.j` for every
datum `d` whose elliptic scheme is a model of the Weierstrass curve `E`.
It is *not* used, and deliberately: the only "is a model of" relation
available here is the one `exists_ellipticScheme_of_weierstrass`
produces — a Galois-equivariant `≃+` of geometric-fibre point groups —
and that relation is NOT known to determine `E` up to isomorphism, hence
not known to determine `E.j`.  Were two curves with different
`j`-invariants to share a datum, that field would make `IsJMapOn`
UNSATISFIABLE and `exists_jMap` FALSE, silently.  `classify_jm` is
therefore stated existentially (*some* datum is classified by a point
carrying `E.j`), which is what the consumer needs, is true of the genuine
`j`-map, and cannot be contradictory whatever that relation turns out to
pin.

**`hN : N ≠ 0` on `exists_jMap` is load-bearing** — the same propagation
recorded in the FALSITY AUDIT of
`exists_cyclicSubgroupOfOrder_of_galoisStable` and in
`nonempty_gamma0Datum_of_stable`.  At `N = 0` the hypotheses of
`classify_jm` are met by a rational point of infinite order on a
positive-rank curve, while its conclusion demands a
`Gamma0Datum 0 SpecQ`, which `isEmpty_of_gamma0Datum_zero` forbids over
the nonempty base `Spec ℚ`.  So `IsJMapOn 0 hc` is *unsatisfiable*, and
`exists_jMap` without `hN` would be false. -/

/-- **A rational point of the compactification is a cusp when it does not
come from the open part**, on a general base.

The exact analogue of `IsCompactificationY0.IsCusp`, which is hardwired
to `Spec ℚ`; this one is needed over `Spec 𝔽_q`, where the conclusion of
the dictionary below lives.  Phrased through `sectionAlong` rather than
through a bare factorisation of `x.1`, because that is the form
`IsX0Compactification`'s consumers already use. -/
def IsX0Compactification.IsCusp {N : ℕ} {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S}
    {jY : Y ⟶ X} (h : IsX0Compactification N strX strY jY) (x : RelPoint strX (𝟙 S)) : Prop :=
  ¬ ∃ y : RelPoint strY (𝟙 S), sectionAlong jY h.comm y = x

/-- **The `j`-map on the rational points of `Y_0(N)`.**

`Y_0(N)` is an affine curve and `j` is a regular function on it — the
composite of the degeneracy map to level `1` (which this module already
builds, `Gamma0Datum.ofDvd` + `IsBaseChangeOf.ofDvd` + the universal
property of `hc`) with the coordinate identifying `Y_0(1)` with the
`j`-line `𝔸¹`.  Only its values at rational points are ever used, so only
those are carried.

See the subsection docstring for why `classify_jm` is an existence
statement rather than the equation `jm (hc.classify d) = E.j`, and for
why `IsJMapOn 0 hc` is unsatisfiable. -/
structure IsJMapOn (N : ℕ) {Y : Scheme.{0}} {strY : Y ⟶ SpecQ}
    (hc : IsCoarseModuliY0 N strY) where
  /-- the `j`-invariant of a rational moduli point -/
  jm : RelPoint strY (𝟙 SpecQ) → ℚ
  /-- every Weierstrass curve over `ℚ` carrying a Galois-stable cyclic
  subgroup of order `N` is classified by a rational point of `Y_0(N)` at
  which `jm` takes the value `E.j`.  The hypotheses are verbatim those of
  `nonempty_gamma0Datum_of_stable`, which is what supplies the datum. -/
  classify_jm : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
      (g : (E⁄(AlgebraicClosure ℚ)).Point), addOrderOf g = N →
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) →
      ∃ d : Gamma0Datum N SpecQ, jm (hc.classify (𝟙 SpecQ) d) = E.j

/-- **Good reduction at `q` of the pair `(X_0(N), j)`, on rational
points.**

This is the constraint on `redX` that the dictionary needs, and that
`IsX0ReductionAt` deliberately does not carry: that structure's only
axioms are additivity, injectivity of `redJ` and `red_aj`, so `redX`
there is pinned *only* through the Abel–Jacobi square and a dictionary
about `j` could not be proved against it.  Rather than add a field to
`IsX0ReductionAt` — which is concurrently owned — the constraint is
packaged separately; the two structures share no field and can be
carried side by side.

The single axiom `red_jm` is the point-level reading of "the `j`-map
extends to a morphism of smooth models over `ℤ_(q)`", which is
Deligne–Rapoport for `q ∤ N`: if a rational point reduces INTO the open
part `Y'` of the special fibre — i.e. its reduction is not a cusp — then
its `j`-invariant is `q`-integral, and its reduction is the `j`-invariant
of the reduced point.

**Both conjuncts earn their place.**  The dictionary below uses only the
first, `q`-integrality; the second pins `jm'` as the genuine `j`-map of
the special fibre rather than an arbitrary function, and is stated as
`jm' y' * den = num` in `ZMod q` rather than with an inverse precisely so
that it needs no side condition — `q`-integrality, the first conjunct,
already makes `den` invertible mod `q`.

## FORMAL-CONTENT AUDIT (2026-07-27) — READ THIS BEFORE STATING THE
## FORMAL-IMMERSION LEAF OVER THIS STRUCTURE

**`redX` is NOT pinned to be the genuine reduction, and there is an
explicit junk witness.**  Take `redX` to send *every* rational point to a
point of `X'` outside the image of `sectionAlong jY' hX'.comm` — a cusp
of the special fibre.  Then the hypothesis of `red_jm` is never
satisfiable, so `red_jm` holds vacuously for any `jm` and any `jm'`, and
the structure is inhabited with no arithmetic content whatever.

Two consequences, and the second is the one that costs a task if missed.

*The dictionary is unaffected.*  `isCusp_redX_of_padicValRat_neg` is a
true implication for every datum, junk included — under the junk witness
its conclusion is simply true for trivial reasons.  Nothing downstream of
it is weakened by the junk witness alone.

*The formal-immersion leaf MUST NOT be universally quantified over this
structure.*  That leaf is "a rational point whose reduction is a cusp is
itself a cusp", i.e. `hX'.IsCusp (redX x) → hX.IsCusp x`.  Under the junk
witness above its hypothesis holds for EVERY `x` while its conclusion
fails for every `x` coming from `Y`, so the universally quantified form
is **FALSE**, not merely unsupported.  This is the same defect the
`WHY THIS LEAF DOES NOT DECOMPOSE` note under `exists_x0Sieve` records
for `IsX0ReductionAt` and `redJ`, in a new place; it is recorded here so
that it is found before, not after, someone writes the leaf.

**The check that would refute this audit**, and it is one grep: a field
on this structure pinning `redX` as the map induced by a morphism of
integral models.  There is none today because no integral model of
`X_0(N)` exists at this pin.  **The remedy is already in flight**: the
`IsX0NeronDatum` layer being built on branch `flt-lean-12` carries the
integral models with both fibres identified as equivalences of functors
of points, which is exactly the object that turns `redX` from an
arbitrary function into an induced map — the same repair that made
`red_aj` and `redJ_add` theorems rather than assumptions there.  When it
lands, `IsX0JReductionAt` should be re-founded on it and `red_jm` should
become a theorem; until then the formal-immersion leaf must be stated
against a datum produced by `exists_x0JReductionAt`, never against an
arbitrary one. -/
structure IsX0JReductionAt (N q : ℕ)
    {Y X Y' X' : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    (hX : IsCompactificationY0 strY strX)
    (hX' : IsX0Compactification N strX' strY' jY')
    (hj : IsJMapOn N hc) where
  /-- reduction of rational points of `X_0(N)` at `q` -/
  redX : RelPoint strX (𝟙 SpecQ) → RelPoint strX' (𝟙 (SpecF q))
  /-- the `j`-map on the rational points of the special fibre -/
  jm' : RelPoint strY' (𝟙 (SpecF q)) → ZMod q
  /-- the `j`-map extends over `ℤ_(q)` and commutes with reduction: a
  rational point whose reduction lies in the open part has `q`-integral
  `j`-invariant, reducing to the `j`-invariant of the reduced point -/
  red_jm : ∀ (y : RelPoint strY (𝟙 SpecQ)) (y' : RelPoint strY' (𝟙 (SpecF q))),
      redX (sectionAlong hX.j hX.over y) = sectionAlong jY' hX'.comm y' →
      0 ≤ padicValRat q (hj.jm y) ∧
        jm' y' * ((hj.jm y).den : ZMod q) = ((hj.jm y).num : ZMod q)

/-- **THE DICTIONARY** (PROVEN): a rational point of `Y_0(N)` whose
`j`-invariant has a pole at `q` reduces mod `q` into the CUSPIDAL locus.

This is the first sentence of Mazur's Cor. 4.4 argument, and the step
that `WeierstrassCurve.potentiallyGoodReduction_of_isogenyCharacter` in
`FreyCurve/MazurTorsion.lean` is blocked on.

The proof is the contrapositive of `red_jm` and nothing else: if the
reduction were *not* a cusp it would be `sectionAlong` of a rational
point `y'` of the special fibre's open part, and `red_jm` would then make
`j(y)` `q`-integral, contradicting `v_q(j(y)) < 0`.

Note the conclusion is about `redX (sectionAlong … y)` — the reduction of
a point of the OPEN part pushed into the compactification.  That is the
right hypothesis shape for Mazur: the point he starts from is
non-cuspidal by construction (it is the pair `(E, C)`), and the whole
force of the argument is that it nevertheless reduces to a cusp. -/
theorem isCusp_redX_of_padicValRat_neg {N q : ℕ}
    {Y X Y' X' : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    {hX : IsCompactificationY0 strY strX}
    {hX' : IsX0Compactification N strX' strY' jY'}
    {hj : IsJMapOn N hc} (hjr : IsX0JReductionAt N q hX hX' hj)
    (y : RelPoint strY (𝟙 SpecQ)) (hv : padicValRat q (hj.jm y) < 0) :
    hX'.IsCusp (hjr.redX (sectionAlong hX.j hX.over y)) := by
  rintro ⟨y', hy'⟩
  exact absurd (hjr.red_jm y y' hy'.symm).1 (not_le.mpr hv)

/-- **The dictionary in the shape Mazur's Cor. 4.4 consumes it** (PROVEN):
an elliptic curve over `ℚ` with a Galois-stable cyclic subgroup of order
`N` and `v_q(j(E)) < 0` gives a rational point of `Y_0(N)` with that
`j`-invariant whose image in `X_0(N)` reduces mod `q` to a cusp.

This is the composite of `IsJMapOn.classify_jm` — which turns the
elliptic-curve hypotheses into a rational moduli point carrying `E.j` —
with `isCusp_redX_of_padicValRat_neg`.  The hypotheses on `E` and `g` are
verbatim those of `WeierstrassCurve.potentiallyGoodReduction_of_isogenyCharacter`'s
own inputs, so this is the use site that layer will call.

What remains between this and Cor. 4.4 is exactly Mazur's two missing
objects, and neither is in this module: the Eisenstein quotient `J_e(N)`
of rank `0`, and the formal-immersion criterion at `∞` in characteristic
`q ≠ 2`.  This statement is what they are applied TO. -/
theorem exists_cuspidalReduction_of_padicValRat_neg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N q : ℕ}
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g)
    {Y X Y' X' : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    {hX : IsCompactificationY0 strY strX}
    {hX' : IsX0Compactification N strX' strY' jY'}
    {hj : IsJMapOn N hc} (hjr : IsX0JReductionAt N q hX hX' hj)
    (hv : padicValRat q E.j < 0) :
    ∃ y : RelPoint strY (𝟙 SpecQ), hj.jm y = E.j ∧
      hX'.IsCusp (hjr.redX (sectionAlong hX.j hX.over y)) := by
  obtain ⟨d, hd⟩ := hj.classify_jm E g hg hstable
  exact ⟨hc.classify (𝟙 SpecQ) d, hd,
    isCusp_redX_of_padicValRat_neg hjr _ (by rw [hd]; exact hv)⟩

/-- **Existence of the `j`-map on `Y_0(N)`** (sorry node).

TRUE and classical.  Two halves, both already visible in this module:

* the degeneracy map `Y_0(N) ⟶ Y_0(1)` exists — `Gamma0Datum.ofDvd`,
  `IsBaseChangeOf.ofDvd` and `liesIn_ofDvd_iff` are PROVEN here, and
  `d ↦ classify₁ (d.ofDvd hN (one_dvd N))` is a natural transformation
  out of the `Γ₀(N)`-problem, so `hc.universal` yields the morphism (this
  is exactly the argument `y0HasNoRationalPoint_of_dvd` already runs);
* `Y_0(1)` is the `j`-line: the coarse space of the level-`1` problem is
  `𝔸¹_ℚ` with coordinate the `j`-invariant (Deligne–Rapoport VI, or
  Silverman *AEC* III.1 over `ℚ̄` plus descent).  This half is what
  `classify_jm` records, and it is the genuinely missing input — the
  `j`-invariant of an elliptic SCHEME does not exist at this pin, only
  `WeierstrassCurve.j` of a Weierstrass equation does.

`hN : N ≠ 0` is REQUIRED, not decoration: see the subsection docstring —
`IsJMapOn 0 hc` is unsatisfiable, so this statement is FALSE without it.

IRREDUCIBLE at this pin, and for the same reason as
`exists_coarseModuliY0`: it needs the level-`1` coarse space identified
with `𝔸¹` compatibly with `WeierstrassCurve.j`, which is a statement
about a moduli space that does not exist here. -/
theorem exists_jMap (N : ℕ) (_hN : N ≠ 0) {Y : Scheme.{0}} {strY : Y ⟶ SpecQ}
    (hc : IsCoarseModuliY0 N strY) : Nonempty (IsJMapOn N hc) :=
  sorry

/-- **Existence of the good reduction of `(X_0(N), j)` at a prime
`q ∤ N`** (sorry node).

TRUE — Deligne–Rapoport: for `q ∤ N` the modular curve `X_0(N)` has a
smooth proper model over `ℤ_(q)` whose special fibre is `X_0(N)_{𝔽_q}`,
the cusps form a relative divisor, and the `j`-map extends to a morphism
of models.  Reduction of rational points is the valuative criterion
applied to that proper model: a `ℚ`-point extends uniquely to a
`ℤ_(q)`-point, which is then evaluated on the closed fibre.  `red_jm` is
the extension of `j` read on points.

Note what is NOT assumed: `q` is not required to be odd.  Mazur needs
`q ≠ 2` for the FORMAL IMMERSION, which is a different statement and is
not part of this module; the model and the `j`-map extension are fine at
`q = 2` as long as `q ∤ N`, and keeping the hypothesis out is the
direction that leaves the leaf weakest.

IRREDUCIBLE at this pin, and strictly harder than
`exists_x0Compactification`: on top of the compactification over `ℚ` it
needs the integral model, which is the same missing object that makes
`exists_x0Sieve` atomic. -/
theorem exists_x0JReductionAt (N q : ℕ) (_hN : N ≠ 0) (_hq : q.Prime) (_hqN : ¬ q ∣ N)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {hc : IsCoarseModuliY0 N strY} (hX : IsCompactificationY0 strY strX)
    (hj : IsJMapOn N hc) :
    ∃ (Y' X' : Scheme.{0}) (strY' : Y' ⟶ SpecF q) (strX' : X' ⟶ SpecF q) (jY' : Y' ⟶ X')
      (hX' : IsX0Compactification N strX' strY' jY'),
      Nonempty (IsX0JReductionAt N q hX hX' hj) :=
  sorry

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

/-- **`n • x` on relative points of an abelian scheme.**

The `AddCommGroup` structure on `RelPoint f g` is `addCommGroup`, which
is a plain definition rather than an instance because it depends on the
`ab` TERM.  Wrapping the scalar action in a definition is what lets the
torsion hypothesis of `neronKernel_torsionFree` be STATED without a
`letI` inside the statement. -/
noncomputable def AbelianSchemeStruct.nsmulPoint {A S : Scheme.{u}} {f : A ⟶ S}
    (ab : AbelianSchemeStruct f) {T : Scheme.{u}} {g : T ⟶ S} (n : ℕ)
    (x : RelPoint f g) : RelPoint f g :=
  letI := ab.addCommGroup g
  n • x

/-- **A subgroup on which every element of PRIME order vanishes is
torsion-free** (PROVEN).

Pure group theory, and it is what reduces the kernel-of-reduction
statement below from arbitrary `n` to prime order.  Strong induction on
`n`: pick a prime `q ∣ n`, write `n = q * m`; then `m • x` has order
dividing `q` and still lies in `ker φ` (because `φ` is additive), so the
prime hypothesis kills it, leaving `m • x = 0` with `m < n`. -/
theorem torsionFree_of_prime {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H)
    (hp : ∀ q : ℕ, q.Prime → ∀ y : G, φ y = 0 → q • y = 0 → y = 0) :
    ∀ (n : ℕ), n ≠ 0 → ∀ x : G, φ x = 0 → n • x = 0 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx hnx
    rcases eq_or_ne n 1 with rfl | hn1
    · rwa [one_nsmul] at hnx
    · obtain ⟨q, hq, m, rfl⟩ : ∃ q, q.Prime ∧ ∃ m, n = q * m := by
        obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hn1
        obtain ⟨m, rfl⟩ := hqd
        exact ⟨q, hq, m, rfl⟩
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hqy : q • (m • x) = 0 := by rw [← mul_nsmul']; exact hnx
      have hφy : φ (m • x) = 0 := by rw [map_nsmul, hx, nsmul_zero]
      have hy : m • x = 0 := hp q hq _ hφy hqy
      have hlt : m < q * m :=
        calc m = 1 * m := (one_mul m).symm
        _ < q * m := (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hm)).mpr hq.one_lt
      exact ih m hlt hm x hx hy

/-- **The kernel of reduction contains no point of PRIME order `q ≠ ℓ`**
(sorry node — the ÉTALE RIGIDITY fact).

TRUE, and note what is NOT among its hypotheses: **`ℓ ≠ 2` is absent,
and that is the point of separating this case out.**  This half of the
torsion-freeness statement holds at every residue characteristic,
including `ℓ = 2`; the `e < ℓ − 1` condition belongs exclusively to the
`q = ℓ` case in `neronKernel_torsionFree_residue`.

The argument is not formal groups at all.  Since `q ≠ ℓ` and `hbase`
makes `R` local with residue field `𝔽_ℓ`, `q` is a UNIT in `R`, so
`𝒥[q] ⟶ Spec R` is finite étale (multiplication by `q` is étale on an
abelian scheme once `q` is invertible on the base — it is an isomorphism
on the Lie algebra).  An étale morphism is unramified, so the equalizer
of the two sections `x` and `0` of `𝒥[q]` is OPEN; `𝒥 ⟶ Spec R` is
separated (it is proper, `abZ.proper`), so that equalizer is also
CLOSED; `Spec R` of a local ring is connected; and `hker` says the
equalizer contains the closed point.  Hence it is everything and
`x = 0`.

MISSING MACHINERY, and this is a DIFFERENT gap from the one below: the
`q`-torsion subscheme `𝒥[q]` as a scheme, and étaleness of `[q]` when
`q` is invertible.  `Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`
already has `zeroSection`, `mulByNat` and `zeroSection_comp_mulByNat`,
so the kernel is expressible as a fibre product there; what is absent is
its étaleness.

IRREDUCIBLE at this pin ALONG THE ÉTALE AXIS, and the CHECK THAT WOULD
REFUTE THAT: produce, anywhere in the pin, `IsEtale` (or even
`UnramifiedAt`) for multiplication by an invertible integer on an
abelian scheme — grep `AbelianSchemeIsogeny.lean` for an étaleness
statement about `mulByNat`.  One such declaration collapses this leaf to
the connectedness argument above, which is elementary. -/
theorem neronKernel_torsionFree_primeToResidue (ℓ : ℕ) (R : Subring ℚ)
    (toF : R →+* ZMod ℓ) (_hbase : IsReductionBase ℓ R toF)
    (q : ℕ) (_hq : q.Prime) (_hqℓ : q ≠ ℓ)
    {JZ : Scheme.{0}} {jstrZ : JZ ⟶ SpecLoc R} (abZ : AbelianSchemeStruct jstrZ)
    (x : RelPoint jstrZ (𝟙 (SpecLoc R)))
    (_htors : abZ.nsmulPoint q x = abZ.zero (𝟙 (SpecLoc R)))
    (_hker : RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) x
      = abZ.zero (SpecLoc.special toF)) :
    x = abZ.zero (𝟙 (SpecLoc R)) :=
  sorry

/-- **The kernel of reduction contains no point of order `ℓ`, for `ℓ`
odd** (sorry node — the FORMAL-GROUP fact).

TRUE, and classical.  The kernel of `𝒥(ℤ_(ℓ)) → 𝒥(𝔽_ℓ)` embeds in the
kernel over the completion `ℤ_ℓ`, which is the group of points of the
formal group of `𝒥` on the maximal ideal; and a formal group over an
`ℓ`-adic ring of absolute ramification index `e` is torsion-free when
`e < ℓ − 1`.  Here `e = 1` by `hbase`, so the condition is exactly
`ℓ > 2`.

**This is where — and ONLY where — `hℓ2` is load-bearing.**  `hℓ2` is
exactly the `e < ℓ − 1` condition and cannot be dropped: at `ℓ = 2`,
`e = 1 = ℓ − 1`, and the standard counterexample is `𝔾ₘ` over
`ℤ_p[ζ_p]`, where `ζ_p − 1` lies in the maximal ideal and is a
`p`-torsion point of the formal group killed by reduction.  `hbase` is
what makes the base a DVR with `e = 1` and residue characteristic `ℓ`.

Silverman, *ATAEC* IV.6; Bosch–Lütkebohmert–Raynaud, *Néron Models*.

IRREDUCIBLE at this pin ALONG THE FORMAL-GROUP AXIS, and the CHECK THAT
WOULD REFUTE THAT: mathlib gained formal group LAWS
(`Mathlib/RingTheory/FormalGroup/Basic.lean`: `FormalGroup`, `Point`,
`𝔾ₐ`, `𝔾ₘ`, `map`), but a survey on 2026-07-27 found that file **stops
at `AddCommMonoid` on `Point` — there is no `Neg`, no `AddGroup`, and no
formal inverse series** — and its own docstring records the
points-in-a-complete-local-ring construction as a TODO.  Absent
everywhere (mathlib, `~/cs/FLT`, this project) are (a) the formal group
OF an abelian scheme along its zero section, and (b) the
torsion-freeness theorem for `e < p − 1`.  Producing either as a
declaration refutes the claim; `FormalGroup.Point` is the natural target
for (a), and an `AddGroup` instance on it is the prerequisite for
either. -/
theorem neronKernel_torsionFree_residue (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (_hbase : IsReductionBase ℓ R toF) (_hℓ : ℓ.Prime) (_hℓ2 : ℓ ≠ 2)
    {JZ : Scheme.{0}} {jstrZ : JZ ⟶ SpecLoc R} (abZ : AbelianSchemeStruct jstrZ)
    (x : RelPoint jstrZ (𝟙 (SpecLoc R)))
    (_htors : abZ.nsmulPoint ℓ x = abZ.zero (𝟙 (SpecLoc R)))
    (_hker : RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) x
      = abZ.zero (SpecLoc.special toF)) :
    x = abZ.zero (𝟙 (SpecLoc R)) :=
  sorry

/-- **The kernel of reduction on an abelian scheme over `ℤ_(ℓ)` is
TORSION-FREE, for `ℓ` odd** (PROVEN, over the two prime-order leaves
above).

**This is strictly SHARPER than the `neronReduction_injective` it was
factored out of**: rank `0` is NOT among its hypotheses.  Finiteness of
`𝒥(ℤ_(ℓ))` was only ever used to know that every element of the kernel
is torsion, and that step is discharged inside
`neronReduction_injective` itself.

**The cut, and why it is not leaf inflation.**  `torsionFree_of_prime`
reduces arbitrary `n` to PRIME order — that is proven group theory,
costing nothing.  Prime order then splits along the residue
characteristic into two cases that need **entirely different theories**
and share no argument:

* `q ≠ ℓ` (`neronKernel_torsionFree_primeToResidue`) — étale rigidity:
  `𝒥[q]` is finite étale because `q` is a unit, and two sections of a
  separated unramified morphism agreeing at a point of a connected base
  agree.  **Needs no hypothesis on `ℓ` whatsoever.**
* `q = ℓ` (`neronKernel_torsionFree_residue`) — the formal group of
  `𝒥` on the maximal ideal, torsion-free because `e = 1 < ℓ − 1`.

The previous audit here recorded the node as irreducible, but it ranged
only over the formal-group axis; along that axis it was right.  The
ÉTALE axis was never searched, and it carries a strict majority of the
statement (every prime but one).  Isolating it also makes visible that
`hℓ2` is needed for a single prime, which the undivided statement hid.

This is the SHARED content that `card_le_of_rankZeroJacobian` also rests
on, isolated here so that it is proven once. -/
theorem neronKernel_torsionFree (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (hbase : IsReductionBase ℓ R toF) (hℓ2 : ℓ ≠ 2)
    {JZ : Scheme.{0}} {jstrZ : JZ ⟶ SpecLoc R} (abZ : AbelianSchemeStruct jstrZ)
    (n : ℕ) (hn : n ≠ 0) (x : RelPoint jstrZ (𝟙 (SpecLoc R)))
    (htors : abZ.nsmulPoint n x = abZ.zero (𝟙 (SpecLoc R)))
    (hker : RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) x
      = abZ.zero (SpecLoc.special toF)) :
    x = abZ.zero (𝟙 (SpecLoc R)) := by
  letI := abZ.addCommGroup (𝟙 (SpecLoc R))
  letI := abZ.addCommGroup (SpecLoc.special toF)
  refine torsionFree_of_prime
    (AddMonoidHom.mk' (RelPoint.pre (SpecLoc.special toF)
        (Category.comp_id (SpecLoc.special toF)))
      (abZ.pre_add (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF))))
    ?_ n hn x hker htors
  intro q hq y hy hqy
  rcases eq_or_ne q ℓ with rfl | hqℓ
  · exact neronKernel_torsionFree_residue q R toF hbase hq hℓ2 abZ y hqy hy
  · exact neronKernel_torsionFree_primeToResidue ℓ R toF hbase q hq hqℓ abZ y hqy hy

/-- **Reduction is injective on the integral points of an abelian scheme
over `ℤ_(ℓ)` for `ℓ` odd** (PROVEN, over `neronKernel_torsionFree`).

The argument in full, and it is the reason the leaf above carries no
finiteness hypothesis.  `RelPoint.pre` along the closed point is a group
homomorphism — that is `abZ.pre_add`, and `AddMonoidHom.mk'` packages it
— so injectivity is triviality of its kernel
(`injective_iff_map_eq_zero`).  `hfin` makes `𝒥(ℤ_(ℓ))` finite, hence
every element has finite additive order, so an element of the kernel is
torsion; and a torsion element of a torsion-free subgroup is zero, which
is `neronKernel_torsionFree` applied at `n = addOrderOf x`.

So the split is: everything ABOVE the formal group is here, and the
formal group alone is the leaf.  `hfin` is consumed here and nowhere
else. -/
theorem neronReduction_injective (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (hbase : IsReductionBase ℓ R toF) (hℓ2 : ℓ ≠ 2)
    {JZ : Scheme.{0}} {jstrZ : JZ ⟶ SpecLoc R} (abZ : AbelianSchemeStruct jstrZ)
    (hfin : Finite (RelPoint jstrZ (𝟙 (SpecLoc R)))) :
    Function.Injective
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) :
        RelPoint jstrZ (𝟙 (SpecLoc R)) → RelPoint jstrZ (SpecLoc.special toF)) := by
  letI := abZ.addCommGroup (𝟙 (SpecLoc R))
  letI := abZ.addCommGroup (SpecLoc.special toF)
  haveI := hfin
  have hinj : Function.Injective
      (AddMonoidHom.mk' (RelPoint.pre (SpecLoc.special toF)
          (Category.comp_id (SpecLoc.special toF)))
        (abZ.pre_add (SpecLoc.special toF)
          (Category.comp_id (SpecLoc.special toF)))) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine neronKernel_torsionFree ℓ R toF hbase hℓ2 abZ (addOrderOf x) ?_ x ?_ hx
    · exact (addOrderOf_pos x).ne'
    · show abZ.nsmulPoint (addOrderOf x) x = abZ.zero _
      exact addOrderOf_nsmul_eq_zero x
  exact hinj

/-! ### Two base-independent notions: a relative curve, and a fibre

Both halves of the Néron datum are assembled out of the same two shapes,
and neither mentions `X_0(N)`, `ℤ_(ℓ)` or even a number field.  Naming
them is what lets the sub-leaves below be stated over an ARBITRARY base,
which is the difference between a decomposition and a repartition of
fields: `exists_relativeJacobian` and `isSmoothProperCurve_of_fibreIdent`
are statements about smooth proper curves in general, and are reusable
anywhere in the reduction-theory subtree. -/

/-- **A smooth proper curve over a base**: proper, smooth of relative
dimension `1`, with geometrically connected fibres.

These are exactly the three geometric fields `IsX0Compactification`
carries about `strX`, and exactly the hypotheses under which the relative
Picard functor `Pic⁰` is representable by an abelian scheme.  Naming them
is what lets `exists_relativeJacobian` be stated without reference to
modular curves. -/
structure IsSmoothProperCurve {C S : Scheme.{0}} (f : C ⟶ S) : Prop where
  /-- the curve is proper over the base -/
  isProper : IsProper f
  /-- the curve is smooth of relative dimension `1` -/
  smooth : SmoothOfRelativeDimension 1 f
  /-- the fibres are geometrically connected -/
  connected : GeometricallyConnected f

/-- **`f' : A' ⟶ S'` is the fibre of `f : A ⟶ S` along `s : S' ⟶ S`,
as functors of points.**

This is the shape that occurs FOUR times in `IsX0NeronDatum` — as
`(genX, genX_nat)`, `(spX, spX_nat)`, `(genJ, genJ_nat)` and
`(spJ, spJ_nat)` — with `s` the generic or the closed point.  The
equivalence is natural in the test scheme, stated in the "identified
base" form used throughout this file, so `RelPoint f (g ≫ s)` is the
functor of points of the base change `A ×_S S'` and the two fields
together say, by Yoneda in `Over S'`, that `A' ≅ A ×_S S'` over `S'`.

Factoring it out is not cosmetic.  It is what makes
`fibreIdentPullback` — the observation that the pullback IS a fibre —
expressible at all, and that single lemma removes the special fibre of
the curve model from the list of things that have to be POSITED: below,
`X'` is *constructed* as `𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ` rather than assumed to
exist. -/
structure IsFibreIdent {S S' A A' : Scheme.{0}} (s : S' ⟶ S) (f : A ⟶ S) (f' : A' ⟶ S') where
  /-- the identification of relative points, over an identified base point -/
  toEquiv : ∀ {T : Scheme.{0}} (g : T ⟶ S') (g₀ : T ⟶ S), g ≫ s = g₀ →
    RelPoint f' g ≃ RelPoint f g₀
  /-- naturality in the test scheme -/
  nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ S'} {g' : T' ⟶ S'}
    (hg : h ≫ g = g') {g₀ : T ⟶ S} {g₀' : T' ⟶ S}
    (h₀ : g ≫ s = g₀) (h₀' : g' ≫ s = g₀') (x : RelPoint f' g),
    toEquiv g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (toEquiv g g₀ h₀ x)

/-- **The pullback is a fibre** (PROVEN).

`A ×_S S' ⟶ S'` satisfies `IsFibreIdent s f`, by nothing but the
universal property of the pullback: a `T`-point of `A ×_S S'` over
`g : T ⟶ S'` is exactly a `T`-point of `A` over `g ≫ s`, and
precomposition is composition, which is associative.

This is the lemma that turns the special fibre from an assumption into a
construction — see `exists_x0CurveModel_of_base`, where `X'` is no
longer existentially quantified over but is literally
`Limits.pullback xstr (SpecLoc.special toF)`. -/
noncomputable def fibreIdentPullback {S S' A : Scheme.{0}} (s : S' ⟶ S) (f : A ⟶ S) :
    IsFibreIdent s f (Limits.pullback.snd f s) where
  toEquiv g g₀ h :=
    { toFun := fun x => ⟨x.1 ≫ Limits.pullback.fst f s, by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, x.2, h]⟩
      invFun := fun y => ⟨Limits.pullback.lift y.1 g (y.2.trans h.symm),
        Limits.pullback.lift_snd _ _ _⟩
      left_inv := fun x => Subtype.ext (Limits.pullback.hom_ext
        (by rw [Limits.pullback.lift_fst])
        (by rw [Limits.pullback.lift_snd, x.2]))
      right_inv := fun y => Subtype.ext (Limits.pullback.lift_fst _ _ _) }
  nat := by intros; exact Subtype.ext (Category.assoc _ _ _)

/-- **The CURVE half of a Néron datum: the integral model of `X_0(N)`
over `ℤ_(ℓ)` together with its two fibres.**

This is `IsX0NeronDatum` with every field that mentions the Jacobian
deleted.  What is left is exactly the Deligne–Rapoport / Igusa smooth
proper model of `X_0(N)` over `ℤ[1/N]`, restricted to `ℤ_(ℓ)` for
`ℓ ∤ N`, plus the identification of its two fibres as functors of points
and the valuative criterion of properness.

Writing it as a structure is what makes the cut possible: nothing here
is known to be satisfiable yet, but the *statement* is all the Jacobian
half needs as input. -/
structure IsX0CurveModel (N ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    (xstr : XZ ⟶ SpecLoc R) (ystr : YZ ⟶ SpecLoc R) (jZ : YZ ⟶ XZ) where
  /-- the integral model is the smooth model of `X_0(N)` over the base -/
  model : IsX0Compactification N xstr ystr jZ
  /-- the generic fibre of the curve model is `X`, functorially -/
  genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀
  /-- the special fibre of the curve model is `X'`, functorially -/
  spX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint strX' g ≃ RelPoint xstr g₀
  /-- naturality of the generic identification of curves -/
  genX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strX g),
    genX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genX g g₀ h₀ x)
  /-- naturality of the special identification of curves -/
  spX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF ℓ} {g' : T' ⟶ SpecF ℓ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint strX' g),
    spX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spX g g₀ h₀ x)
  /-- **valuative criterion of properness**: every rational point of `X`
  extends uniquely to an integral point of the model -/
  properX : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint xstr (𝟙 (SpecLoc R)) → RelPoint xstr (SpecLoc.generic R))

/-- **The JACOBIAN half of a Néron datum: the relative Jacobian of a
GIVEN integral curve model, and its two fibres.**

This is `IsX0NeronDatum` with every field the curve model already
carries deleted, and the curve model itself taken as a parameter — which
is what `genX_aj` and `spX_aj` need, since they compare Abel–Jacobi
against `cm.genX` and `cm.spX`.

The content is Grothendieck's relative Picard scheme: `Pic⁰` of a smooth
proper curve over a base is an abelian scheme, its formation commutes
with base change (giving `genJ`, `spJ` and their naturality), the group
law and Abel–Jacobi are defined over the base, and it satisfies the
Néron mapping property `𝒥(ℤ_(ℓ)) ≅ J(ℚ)`. -/
structure IsX0JacobianModel {N ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X J X' J' XZ YZ JZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N ℓ R toF (strX := strX) (strX' := strX') xstr ystr jZ)
    (jac : IsJacobianOf strX ab o) (jac' : IsJacobianOf strX' ab' o')
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} (jacZ : IsJacobianOf xstr abZ oZ) where
  /-- the generic fibre of the Jacobian model is `J`, functorially -/
  genJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint jstr g ≃ RelPoint jstrZ g₀
  /-- the special fibre of the Jacobian model is `J'`, functorially -/
  spJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint jstr' g ≃ RelPoint jstrZ g₀
  /-- naturality of the generic identification of Jacobians -/
  genJ_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint jstr g),
    genJ g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genJ g g₀ h₀ x)
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
    genJ g g₀ h (jac.aj g x) = jacZ.aj g₀ (cm.genX g g₀ h x)
  /-- Abel–Jacobi is defined over the base: special fibre -/
  spX_aj : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀) (x : RelPoint strX' g),
    spJ g g₀ h (jac'.aj g x) = jacZ.aj g₀ (cm.spX g g₀ h x)
  /-- **Néron mapping property**: every rational point of `J` extends
  uniquely to an integral point of the model -/
  neronJ : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint jstrZ (𝟙 (SpecLoc R)) → RelPoint jstrZ (SpecLoc.generic R))

/-- **The generic fibre identification of a curve model, as an
`IsFibreIdent`** (PROVEN — pure field copying). -/
def IsX0CurveModel.genIdent {N ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N ℓ R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    IsFibreIdent (SpecLoc.generic R) xstr strX where
  toEquiv := cm.genX
  nat := cm.genX_nat

/-- **The special fibre identification of a curve model, as an
`IsFibreIdent`** (PROVEN — pure field copying). -/
def IsX0CurveModel.spIdent {N ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N ℓ R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    IsFibreIdent (SpecLoc.special toF) xstr strX' where
  toEquiv := cm.spX
  nat := cm.spX_nat

/-- **Every rational number, or its inverse, lies in a local subring of
`ℚ`** (PROVEN).

The arithmetic heart of `bijective_pre_generic_of_isProper`, and the
whole reason no classification of the subrings of `ℚ` is needed.  Write
`q = m/n` in lowest terms.  Both `m` and `n` lie in `R`, because every
subring of `ℚ` contains `ℤ`.  If `n` is a unit of `R` then `q = m·n⁻¹ ∈
R`; if `m` is a unit then `q⁻¹ = n·m⁻¹ ∈ R`.  Otherwise `IsReductionBase`
puts both in `ker toF`, so Bézout's `u·m + v·n = 1` gives `toF 1 = 0` —
and `toF 1 = 0` says `1` is a nonunit, which is false.

Note where coprimality is used: only to get Bézout.  Nothing here needs
`ℓ` prime, or even `R` to be a DVR; locality alone does it. -/
theorem mem_or_inv_mem_of_isReductionBase {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (hbase : IsReductionBase ℓ R toF) (q : ℚ) : q ∈ R ∨ q⁻¹ ∈ R := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact Or.inl (zero_mem R)
  have hcop : IsCoprime (q.num) ((q.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using q.reduced
  obtain ⟨u, v, huv⟩ := hcop
  have hden : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hnum : ((q.num : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hqval : q * (q.den : ℚ) = (q.num : ℚ) :=
    ((div_eq_iff hden).mp (Rat.num_div_den q)).symm
  by_cases hn : IsUnit (((q.den : ℤ) : R))
  · left
    obtain ⟨w, hw⟩ := hn
    have hwq : (q.den : ℚ) * (((w⁻¹ : Rˣ) : R) : ℚ) = 1 := by
      have h := congrArg (fun z : R => (z : ℚ)) w.mul_inv
      rw [hw] at h; push_cast at h; exact h
    have hcoe : (((w⁻¹ : Rˣ) : R) : ℚ) = ((q.den : ℚ))⁻¹ :=
      (inv_eq_of_mul_eq_one_right hwq).symm
    have hmem : ((((q.num : ℤ) : R) * ((w⁻¹ : Rˣ) : R) : R) : ℚ) = q := by
      push_cast [hcoe]
      rw [← div_eq_mul_inv, div_eq_iff hden]
      exact hqval.symm
    exact hmem ▸ (((q.num : ℤ) : R) * ((w⁻¹ : Rˣ) : R)).2
  by_cases hm : IsUnit (((q.num : ℤ) : R))
  · right
    obtain ⟨w, hw⟩ := hm
    have hwq : (q.num : ℚ) * (((w⁻¹ : Rˣ) : R) : ℚ) = 1 := by
      have h := congrArg (fun z : R => (z : ℚ)) w.mul_inv
      rw [hw] at h; push_cast at h; exact h
    have hcoe : (((w⁻¹ : Rˣ) : R) : ℚ) = ((q.num : ℚ))⁻¹ :=
      (inv_eq_of_mul_eq_one_right hwq).symm
    have hmem : ((((q.den : ℤ) : R) * ((w⁻¹ : Rˣ) : R) : R) : ℚ) = q⁻¹ := by
      push_cast [hcoe]
      rw [← div_eq_mul_inv, div_eq_iff hnum, ← hqval]
      field_simp
    exact hmem ▸ (((q.den : ℤ) : R) * ((w⁻¹ : Rˣ) : R)).2
  · exfalso
    have h1 : toF ((q.den : ℤ) : R) = 0 := (hbase.ker_eq_nonunits _).mpr hn
    have h2 : toF ((q.num : ℤ) : R) = 0 := (hbase.ker_eq_nonunits _).mpr hm
    have hb : ((u : R) * ((q.num : ℤ) : R) + (v : R) * ((q.den : ℤ) : R)) = 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : R)) huv
    have hone : toF (1 : R) = 0 := by
      rw [← hb]
      simp only [map_add, map_mul, h1, h2, mul_zero, add_zero]
    exact absurd isUnit_one ((hbase.ker_eq_nonunits 1).mp hone)

/-- **A base pinned by `IsReductionBase` is a valuation ring** (PROVEN).

Immediate from `mem_or_inv_mem_of_isReductionBase`: for `a ≠ 0 ≠ b` in
`R`, either `b/a ∈ R` — and then `a · (b/a) = b` — or `a/b ∈ R`, and then
`b · (a/b) = a`.  The two degenerate cases take `c = 0`. -/
theorem valuationRing_of_isReductionBase {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (hbase : IsReductionBase ℓ R toF) : ValuationRing R := by
  haveI : PreValuationRing R := by
    refine ⟨fun a b => ?_⟩
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, Or.inr (by simp)⟩
    rcases eq_or_ne b 0 with rfl | hb
    · exact ⟨0, Or.inl (by simp)⟩
    have ha' : (a : ℚ) ≠ 0 := fun h => ha (Subtype.ext h)
    have hb' : (b : ℚ) ≠ 0 := fun h => hb (Subtype.ext h)
    rcases mem_or_inv_mem_of_isReductionBase hbase ((b : ℚ) / (a : ℚ)) with hmem | hmem
    · exact ⟨⟨_, hmem⟩, Or.inl (Subtype.ext (by push_cast; field_simp))⟩
    · refine ⟨⟨_, hmem⟩, Or.inr (Subtype.ext ?_)⟩
      push_cast
      rw [inv_div]
      field_simp
  exact ⟨⟩

/-- **The valuative criterion of properness, read on relative points: a
`ℚ`-point of a proper `ℤ_(ℓ)`-scheme extends uniquely to a
`ℤ_(ℓ)`-point** (PROVEN).

TRUE, and it is the ONE piece of geometry both halves of the Néron datum
need: it is `properX` of `IsX0CurveModel` for the curve, and `neronJ` of
`IsX0JacobianModel` for the Jacobian — the Néron mapping property of an
abelian scheme over a DVR is nothing but properness plus the valuative
criterion, since an abelian scheme is proper (`AbelianSchemeStruct.proper`).
Stating it once and citing it twice is why neither of those is a separate
leaf.

**Why `IsReductionBase` is exactly the right hypothesis.**  It says `R`
is a local subring of `ℚ` with residue field `𝔽_ℓ`.  Every subring of
`ℚ` contains `ℤ`, so `Frac R = ℚ`; and a local subring of `ℚ` is a
valuation ring of `ℚ` — the only ones are `ℚ` itself, which is excluded
because a field's only nonunit is `0` while `ker toF` is the whole
maximal ideal of a ring surjecting onto `ZMod ℓ`, and the `ℤ_(p)`.  So
`R` is a DVR with fraction field `ℚ` and `SpecLoc.generic R` is `Spec`
of `R ↪ Frac R`, which is precisely the left edge of mathlib's
`ValuativeCommSq`.

**How it is proved, and why an earlier audit calling it irreducible was
wrong.**  That audit reported the leaf blocked on "the classification of
local subrings of `ℚ`", which sounded like a theory to build.  It is not
needed: `mem_or_inv_mem_of_isReductionBase` gets `ValuationRing ↥R` out
of Bézout in a dozen lines, without ever identifying `R` as `ℤ_(p)`.
With that, everything else is mathlib —
`AlgebraicGeometry.IsProper.eq_valuativeCriterion` presents `IsProper` as
`ValuativeCriterion ⊓ …`, and `ValuativeCriterion` supplies a UNIQUE lift
for every `ValuativeCommSq`, which is exactly surjectivity plus
injectivity of the map on relative points.

One implementation note worth keeping.  The `Algebra ↥R ℚ` used here is
`R.subtype.toAlgebra`, supplied EXPLICITLY as the `algebra` field of the
`ValuativeCommSq` rather than found by instance search.  That is what
makes `algebraMap ↥R ℚ` reduce to `R.subtype`, hence
`Spec.map (CommRingCat.ofHom (algebraMap ↥R ℚ))` reduce to
`SpecLoc.generic R` by `rfl`; with any other algebra path the two
`Spec.map`s print identically and are not defeq. -/
theorem bijective_pre_generic_of_isProper (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (hbase : IsReductionBase ℓ R toF)
    {A : Scheme.{0}} (f : A ⟶ SpecLoc R) (hf : IsProper f) :
    Function.Bijective
      (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
        RelPoint f (𝟙 (SpecLoc R)) → RelPoint f (SpecLoc.generic R)) := by
  letI : Algebra R ℚ := R.subtype.toAlgebra
  haveI : FaithfulSMul R ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing R ℚ := IsFractionRing.of_field _ _ (fun z =>
    ⟨((z.num : ℤ) : R), ((z.den : ℤ) : R), by push_cast; exact (Rat.num_div_den z).symm⟩)
  haveI : ValuationRing R := valuationRing_of_isReductionBase hbase
  rw [IsProper.eq_valuativeCriterion] at hf
  have hvc : ValuativeCriterion f := hf.1.1.1
  constructor
  · intro s₁ s₂ h
    have hval : SpecLoc.generic R ≫ s₁.1 = SpecLoc.generic R ≫ s₂.1 := congrArg Subtype.val h
    let sq : ValuativeCommSq f :=
      { R := R, K := ℚ, i₁ := SpecLoc.generic R ≫ s₁.1, i₂ := 𝟙 (SpecLoc R)
        commSq := ⟨by rw [Category.assoc, s₁.2, Category.comp_id, Category.comp_id]; rfl⟩ }
    haveI := (hvc sq).some
    have e : (⟨s₁.1, rfl, s₁.2⟩ : sq.commSq.LiftStruct)
        = ⟨s₂.1, hval.symm, s₂.2⟩ := Subsingleton.elim _ _
    exact Subtype.ext (congrArg CategoryTheory.CommSq.LiftStruct.l e)
  · intro x
    let sq : ValuativeCommSq f :=
      { R := R, K := ℚ, i₁ := x.1, i₂ := 𝟙 (SpecLoc R)
        commSq := ⟨by rw [Category.comp_id]; exact x.2⟩ }
    obtain ⟨l, hl₁, hl₂⟩ := (hvc sq).some.default
    exact ⟨⟨l, hl₂⟩, Subtype.ext hl₁⟩

/-- **The smooth proper integral model of `X_0(N)` over `ℤ_(ℓ)` exists,
with its generic fibre identified with the given `X/ℚ`** (sorry node —
Deligne–Rapoport / Igusa).

This is `exists_x0CurveModel_of_base` with everything FORMAL removed.
What is left is the one citation: `X_0(N)` has a smooth proper model over
`ℤ[1/N]`, hence over `ℤ_(ℓ)` for `ℓ ∤ N`, and its generic fibre is the
`X_0(N)` we started with — the second half being the uniqueness of the
coarse moduli space and of the smooth compactification of a curve over
`ℚ`, both of which are determined up to unique isomorphism by
`IsCoarseModuliY0`'s initiality clause.

Three things this leaf NO LONGER carries, and each is a genuine
reduction rather than a repackaging:

* the SPECIAL fibre `X'` — it is the pullback `𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ`, by
  `fibreIdentPullback`, which is PROVEN;
* `spX` and `spX_nat` — same lemma;
* `properX` — that is `bijective_pre_generic_of_isProper` applied to
  `model.isProper`.

IRREDUCIBLE at this pin ALONG THE MODULI AXIS, and the CHECK THAT WOULD
REFUTE THAT: a survey on 2026-07-27 found `ModularCurve` absent from
mathlib entirely (zero hits), and no `DeligneRapoport` or integral model
of a modular curve in mathlib, `~/cs/FLT` or this project — mathlib's
`integralModel` is only the Weierstrass-coefficient model of a single
elliptic curve (`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`).
Producing a smooth proper `ℤ[1/N]`-model of the `Γ₀(N)` moduli problem
refutes the claim.  The nearest usable foothold in this file is
`Gamma0Atlas` / `exists_coarseModuliY0_of_pos`, whose base was
deliberately left general — extending that construction from `Spec ℚ` to
`Spec ℤ_(ℓ)` is the concrete attack. -/
theorem exists_x0CompactificationModel (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N)
    (R : Subring ℚ) (toF : R →+* ZMod ℓ) (_hbase : IsReductionBase ℓ R toF)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (_hX : IsX0Compactification N strX strY j) :
    ∃ (XZ YZ : Scheme.{0}) (xstr : XZ ⟶ SpecLoc R) (ystr : YZ ⟶ SpecLoc R)
      (jZ : YZ ⟶ XZ) (_ : IsX0Compactification N xstr ystr jZ),
      Nonempty (IsFibreIdent (SpecLoc.generic R) xstr strX) :=
  sorry

/-- **The integral CURVE model of `X_0(N)` over `ℤ_(ℓ)` exists, at every
`ℓ ∤ N`** (PROVEN, over the integral model and the valuative criterion).

TRUE: `X_0(N)` has a smooth proper model over `ℤ[1/N]`, hence over
`ℤ_(ℓ)` for `ℓ ∤ N`, and the fibre identifications are the definition of
a model.  `properX` is the valuative criterion of properness for it.

Note there is NO sharpness claim and no hypothesis `ℓ ≠ 2`: this leaf is
universal in `ℓ ∤ N` and says only that the model exists.

**The cut (2026-07-27), and what it removed.**  The previous audit here
recorded the node as irreducible along the MODULI axis, citing the
absence of a Deligne–Rapoport integral model from mathlib, `~/cs/FLT`
and this project.  That citation is still correct — it now sits on
`exists_x0CompactificationModel`, which is the only part of this
statement that needs it — but it covered three further obligations that
need no moduli theory at all, and those are now discharged here:

* the SPECIAL fibre `X'` is no longer existentially quantified over.  It
  is `Limits.pullback xstr (SpecLoc.special toF)`, i.e. literally
  `𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ`, and `spX` / `spX_nat` are the universal property of
  that pullback — `fibreIdentPullback`, which is PROVEN;
* `properX` is `bijective_pre_generic_of_isProper` applied to
  `model.isProper`, and that is PROVEN — mathlib's valuative criterion
  over the observation that `IsReductionBase` makes `R` a valuation ring.

So what a Deligne–Rapoport specialist is now asked for is the model and
its generic fibre, and nothing else. -/
theorem exists_x0CurveModel_of_base (N ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (R : Subring ℚ) (toF : R →+* ZMod ℓ) (hbase : IsReductionBase ℓ R toF)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (hX : IsX0Compactification N strX strY j) :
    ∃ (X' XZ YZ : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (xstr : XZ ⟶ SpecLoc R)
      (ystr : YZ ⟶ SpecLoc R) (jZ : YZ ⟶ XZ),
      Nonempty (IsX0CurveModel N ℓ R toF (strX := strX) (strX' := strX') xstr ystr jZ) := by
  obtain ⟨XZ, YZ, xstr, ystr, jZ, hmodel, ⟨eGen⟩⟩ :=
    exists_x0CompactificationModel N ℓ hℓ hℓN R toF hbase hX
  -- the special fibre is not posited: it is the pullback along the closed point
  exact ⟨Limits.pullback xstr (SpecLoc.special toF), XZ, YZ,
    Limits.pullback.snd xstr (SpecLoc.special toF), xstr, ystr, jZ,
    ⟨{ model := hmodel
       genX := eGen.toEquiv
       spX := (fibreIdentPullback (SpecLoc.special toF) xstr).toEquiv
       genX_nat := eGen.nat
       spX_nat := (fibreIdentPullback (SpecLoc.special toF) xstr).nat
       properX := bijective_pre_generic_of_isProper ℓ R toF hbase xstr hmodel.isProper }⟩⟩

/-! ### The Jacobian half: three base-independent leaves

None of the three mentions `X_0(N)`, `ℚ` or `ℤ_(ℓ)`.  That is the point:
the Jacobian half of a Néron datum is a statement about smooth proper
curves over an arbitrary base, and everything specific to this file
happens in the assembly `exists_x0JacobianModel_of_curveModel`, which
instantiates them at the generic and the closed point. -/

/-- **The relative Jacobian of a smooth proper curve with a section
exists** (sorry node — Grothendieck's relative Picard scheme).

TRUE: for `f : C ⟶ S` smooth and proper with geometrically connected
fibres of dimension `1` and a section `o`, the relative Picard functor
`Pic⁰_{C/S}` is representable by an abelian scheme over `S`, and
Abel–Jacobi `x ↦ [x] − [o]` is the universal map to an abelian scheme —
which is exactly `IsJacobianOf`.  (FGA, exposé 232; BLR *Néron Models*
ch. 8–9; the section is what makes `Pic` representable rather than only
its fppf sheafification.)

Note the base is ARBITRARY: this is the level-free, curve-only content
of the Jacobian half, so it benefits the whole reduction-theory subtree
and not only `X_0`.  It is applied TWICE below, once over `Spec ℤ_(ℓ)`
and once over `Spec 𝔽_ℓ`.

IRREDUCIBLE at this pin ALONG THE PICARD AXIS, and the CHECK THAT WOULD
REFUTE THAT: a survey on 2026-07-27 found no Picard SCHEME and no
relative Jacobian in mathlib, `~/cs/FLT` or this project — mathlib's
`Pic` is the ring-theoretic Picard group of a commutative ring
(`Mathlib/RingTheory/PicardGroup.lean`), and this project's
`JacobianPackage` / `ModularJacobianPackage` are axiomatized interfaces,
not constructions.  Producing a representing scheme for the relative
`Pic⁰` functor refutes the claim. -/
theorem exists_relativeJacobian {C S : Scheme.{0}} (f : C ⟶ S)
    (_hf : IsSmoothProperCurve f) (o : RelPoint f (𝟙 S)) :
    ∃ (J : Scheme.{0}) (jf : J ⟶ S) (ab : AbelianSchemeStruct jf),
      Nonempty (IsJacobianOf f ab o) :=
  sorry

/-- **A fibre of a smooth proper curve is a smooth proper curve**
(sorry node).

TRUE, and it is pure base change: `IsFibreIdent s f f'` says by Yoneda in
`Over S'` that `f'` is isomorphic to `f ×_S S'`, and `IsProper`,
`SmoothOfRelativeDimension 1` and `GeometricallyConnected` are each
stable under base change and invariant under isomorphism over the base.

It is needed because the special fibre `X'` of a curve model is
constrained by NOTHING but its functor of points — `IsX0CurveModel`
carries `spX`/`spX_nat` and no geometric field about `strX'` — so
`exists_relativeJacobian` cannot be applied to it until its geometry is
recovered from the identification.

IRREDUCIBLE at this pin ALONG THE YONEDA AXIS, and the CHECK THAT WOULD
REFUTE THAT: mathlib has the three base-change stability results, so what
is missing is only the passage from a natural equivalence of
`RelPoint`-functors to an isomorphism of schemes over `S'`, i.e. Yoneda
for the over-category presentation used in this file.  Producing that
transport — from `IsFibreIdent s f f'` to `Arrow.mk f' ≅ Arrow.mk
(Limits.pullback.snd f s)` — closes this leaf, and `fibreIdentPullback`
supplies the other half of the comparison. -/
theorem isSmoothProperCurve_of_fibreIdent {S S' A A' : Scheme.{0}} {s : S' ⟶ S}
    {f : A ⟶ S} {f' : A' ⟶ S'} (_e : IsFibreIdent s f f')
    (_hf : IsSmoothProperCurve f) : IsSmoothProperCurve f' :=
  sorry

/-- **Formation of the Jacobian commutes with base change** (sorry node).

TRUE: if `jac` presents `J/S` as the Jacobian of `C/S` and `jac'`
presents `J'/S'` as the Jacobian of the fibre `C'/S'`, based at the point
`o'` lying over `o`, then `J'` is the fibre of `J` — and the
identification is additive and intertwines the two Abel–Jacobi maps.
This is "cohomology and base change" for `Pic⁰` (BLR ch. 8.1, 9.4).

**`_ho` is load-bearing, not decoration.**  The Jacobian is only defined
up to translation once the base point moves: if `o'` were not the fibre
of `o`, `jac'` would differ from the base change of `jac` by translation
by `[o'] − [o|_{S'}]`, and the `aj`-compatibility clause would be FALSE.
So the hypothesis that the base points correspond is exactly what makes
this statement true rather than merely plausible.

Note also that this leaf does NOT assert existence — `jac'` is a
hypothesis, supplied below by `exists_relativeJacobian` over `𝔽_ℓ` and by
the ambient `jac` over `ℚ`.  Stating it this way is what avoids needing
uniqueness of the Jacobian as a separate obligation: the given `J/ℚ` of
`exists_x0JacobianModel_of_curveModel` is used directly rather than
compared with a freshly constructed one.

IRREDUCIBLE at this pin ALONG THE PICARD AXIS, for the same reason as
`exists_relativeJacobian`, and with the same refuting check. -/
theorem exists_jacobianFibreIdent {S S' : Scheme.{0}} (s : S' ⟶ S)
    {C C' J J' : Scheme.{0}} {f : C ⟶ S} {f' : C' ⟶ S'}
    {jf : J ⟶ S} {ab : AbelianSchemeStruct jf} {o : RelPoint f (𝟙 S)}
    (jac : IsJacobianOf f ab o)
    {jf' : J' ⟶ S'} {ab' : AbelianSchemeStruct jf'} {o' : RelPoint f' (𝟙 S')}
    (jac' : IsJacobianOf f' ab' o')
    (eX : IsFibreIdent s f f')
    (_ho : eX.toEquiv (𝟙 S') s (Category.id_comp s) o'
      = RelPoint.pre s (Category.comp_id s) o) :
    ∃ eJ : IsFibreIdent s jf jf',
      (∀ {T : Scheme.{0}} (g : T ⟶ S') (g₀ : T ⟶ S) (h : g ≫ s = g₀)
          (x y : RelPoint jf' g),
        eJ.toEquiv g g₀ h (ab'.add x y)
          = ab.add (eJ.toEquiv g g₀ h x) (eJ.toEquiv g g₀ h y)) ∧
      (∀ {T : Scheme.{0}} (g : T ⟶ S') (g₀ : T ⟶ S) (h : g ≫ s = g₀)
          (x : RelPoint f' g),
        eJ.toEquiv g g₀ h (jac'.aj g x) = jac.aj g₀ (eX.toEquiv g g₀ h x)) :=
  sorry

/-- **The relative JACOBIAN of a given integral curve model exists**
(PROVEN, over the three base-independent leaves above).

The ten fields of `IsX0JacobianModel` come from exactly three inputs,
none of which mentions a modular curve:

* `exists_relativeJacobian` over `Spec ℤ_(ℓ)` builds `𝒥` and `jacZ`, and
  over `Spec 𝔽_ℓ` builds `J'` and `jac'` — the latter needs
  `isSmoothProperCurve_of_fibreIdent`, because the special fibre of a
  curve model carries no geometric field of its own;
* `exists_jacobianFibreIdent` at the generic point gives
  `genJ`, `genJ_nat`, `genJ_add`, `genX_aj`, and at the closed point
  gives `spJ`, `spJ_nat`, `spJ_add`, `spX_aj`;
* `bijective_pre_generic_of_isProper` applied to `abZ.proper` gives
  `neronJ` — an abelian scheme is proper, and the Néron mapping property
  over a DVR is the valuative criterion.

**The two base points are CONSTRUCTED, not chosen.**  `oZ` is the
integral point extending `o`, by `cm.properX`; `o'` is its reduction, by
`cm.spX`.  That is forced: `_ho` of `exists_jacobianFibreIdent` requires
the base points to correspond at both ends, and any other choice would
translate the Abel–Jacobi map and break `genX_aj` / `spX_aj`.  So the
assembly has no freedom left in it. -/
theorem exists_x0JacobianModel_of_curveModel (N ℓ : ℕ) (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (hbase : IsReductionBase ℓ R toF)
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N ℓ R toF (strX := strX) (strX' := strX') xstr ystr jZ)
    {J : Scheme.{0}} {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr}
    {o : RelPoint strX (𝟙 SpecQ)} (jac : IsJacobianOf strX ab o) :
    ∃ (J' JZ : Scheme.{0}) (jstr' : J' ⟶ SpecF ℓ) (ab' : AbelianSchemeStruct jstr')
      (o' : RelPoint strX' (𝟙 (SpecF ℓ))) (jac' : IsJacobianOf strX' ab' o')
      (jstrZ : JZ ⟶ SpecLoc R) (abZ : AbelianSchemeStruct jstrZ)
      (oZ : RelPoint xstr (𝟙 (SpecLoc R))) (jacZ : IsJacobianOf xstr abZ oZ),
      Nonempty (IsX0JacobianModel cm jac jac' jacZ) := by
  have hcurve : IsSmoothProperCurve xstr :=
    ⟨cm.model.isProper, cm.model.smooth, cm.model.connected⟩
  -- the integral point extending `o`, by the valuative criterion
  obtain ⟨oZ, hoZ⟩ : ∃ oZ : RelPoint xstr (𝟙 (SpecLoc R)),
      cm.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) o
        = RelPoint.pre (SpecLoc.generic R) (Category.comp_id _) oZ :=
    ⟨(Equiv.ofBijective _ cm.properX).symm _,
      ((Equiv.ofBijective _ cm.properX).apply_symm_apply _).symm⟩
  -- its reduction, the base point of the special fibre
  obtain ⟨o', ho'⟩ : ∃ o' : RelPoint strX' (𝟙 (SpecF ℓ)),
      cm.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _) o'
        = RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) oZ :=
    ⟨(cm.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm _,
      Equiv.apply_symm_apply _ _⟩
  obtain ⟨JZ, jstrZ, abZ, ⟨jacZ⟩⟩ := exists_relativeJacobian xstr hcurve oZ
  obtain ⟨J', jstr', ab', ⟨jac'⟩⟩ :=
    exists_relativeJacobian strX' (isSmoothProperCurve_of_fibreIdent cm.spIdent hcurve) o'
  obtain ⟨eGen, eGen_add, eGen_aj⟩ :=
    exists_jacobianFibreIdent (SpecLoc.generic R) jacZ jac cm.genIdent hoZ
  obtain ⟨eSp, eSp_add, eSp_aj⟩ :=
    exists_jacobianFibreIdent (SpecLoc.special toF) jacZ jac' cm.spIdent ho'
  exact ⟨J', JZ, jstr', ab', o', jac', jstrZ, abZ, oZ, jacZ,
    ⟨{ genJ := eGen.toEquiv
       spJ := eSp.toEquiv
       genJ_nat := eGen.nat
       spJ_nat := eSp.nat
       genJ_add := eGen_add
       spJ_add := eSp_add
       genX_aj := eGen_aj
       spX_aj := eSp_aj
       neronJ := bijective_pre_generic_of_isProper ℓ R toF hbase jstrZ abZ.proper }⟩⟩

/-- **The good-reduction datum exists over a GIVEN `ℤ_(ℓ)`, at every odd
`ℓ ∤ N`** (PROVEN, over the curve half and the Jacobian half).

This is `exists_x0NeronDatum` with the base handed to it rather than
constructed: `(R, toF)` and its `IsReductionBase` pinning are
hypotheses, supplied at the use site by `exists_isReductionBase`, which
is PROVEN.  So the arithmetic of `ℤ_(ℓ)` is no longer part of this leaf
and what remains is purely the geometry.

**The cut, and the check it was made to pass.**  The previous audit here
recorded the node as irreducible because "neither the integral model of
`X_0(N)` nor the relative Jacobian exists".  Both halves of that are
true — a survey on 2026-07-27 reconfirmed them against mathlib,
`~/cs/FLT` and this project — but they are a statement about TWO
theories, and the sentence is itself the argument for splitting rather
than for stopping.  The eighteen fields of `IsX0NeronDatum` partition
cleanly:

* `model`, `genX`, `spX`, `genX_nat`, `spX_nat`, `properX` mention only
  the curve, and become `IsX0CurveModel` — Deligne–Rapoport / Igusa;
* the ten remaining fields all mention the Jacobian, and become
  `IsX0JacobianModel` over a GIVEN curve model — Grothendieck's relative
  Picard scheme.

No field is duplicated, no argument is shared, and the Jacobian half is
stated for an arbitrary smooth proper curve model, so it does not
mention modular curves at all.  That is the refuting check for "this is
merely a repartition of fields": the two halves have disjoint
literature and can be dispatched to different specialists.  Assembling
them back is the proof below, which is pure field-copying.

Note there is NO sharpness claim here: this leaf is universal in `ℓ`
and says only that the reduction machinery exists.  Combined with
`neronReduction_injective` it is exactly the content of
`card_le_of_rankZeroJacobian` and `exists_x0Compactification_mod_prime`,
which is why factoring it out is a genuine reduction in the total work
rather than a repackaging.

`hℓ2` is now UNUSED here — oddness of `ℓ` was never needed for the
existence of the models, only for torsion-freeness of the kernel of
reduction (`neronKernel_torsionFree_residue`).  It is kept in the
signature because `exists_x0NeronDatum` passes it. -/
theorem exists_x0NeronDatum_of_base (N ℓ : ℕ) (hℓ : ℓ.Prime) (_hℓ2 : ℓ ≠ 2)
    (hℓN : ¬ ℓ ∣ N) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (hbase : IsReductionBase ℓ R toF)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (hX : IsX0Compactification N strX strY j) (jac : IsJacobianOf strX ab o) :
    ∃ (X' J' XZ YZ JZ : Scheme.{0})
      (strX' : X' ⟶ SpecF ℓ) (jstr' : J' ⟶ SpecF ℓ)
      (ab' : AbelianSchemeStruct jstr') (o' : RelPoint strX' (𝟙 (SpecF ℓ)))
      (jac' : IsJacobianOf strX' ab' o') (xstr : XZ ⟶ SpecLoc R)
      (ystr : YZ ⟶ SpecLoc R) (jZ : YZ ⟶ XZ) (jstrZ : JZ ⟶ SpecLoc R)
      (abZ : AbelianSchemeStruct jstrZ) (oZ : RelPoint xstr (𝟙 (SpecLoc R)))
      (jacZ : IsJacobianOf xstr abZ oZ),
      Nonempty (IsX0NeronDatum N ℓ R toF jac jac'
        (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) := by
  obtain ⟨X', XZ, YZ, strX', xstr, ystr, jZ, ⟨cm⟩⟩ :=
    exists_x0CurveModel_of_base N ℓ hℓ hℓN R toF hbase hX
  obtain ⟨J', JZ, jstr', ab', o', jac', jstrZ, abZ, oZ, jacZ, ⟨jm⟩⟩ :=
    exists_x0JacobianModel_of_curveModel N ℓ hℓ hℓN R toF hbase cm jac
  exact ⟨X', J', XZ, YZ, JZ, strX', jstr', ab', o', jac', xstr, ystr, jZ, jstrZ, abZ, oZ, jacZ,
    ⟨{ base := hbase
       model := cm.model
       genX := cm.genX
       genJ := jm.genJ
       spX := cm.spX
       spJ := jm.spJ
       genX_nat := cm.genX_nat
       genJ_nat := jm.genJ_nat
       spX_nat := cm.spX_nat
       spJ_nat := jm.spJ_nat
       genJ_add := jm.genJ_add
       spJ_add := jm.spJ_add
       genX_aj := jm.genX_aj
       spX_aj := jm.spX_aj
       neronJ := jm.neronJ
       properX := cm.properX }⟩⟩

/-- **The base `ℤ_(ℓ)` exists: `IsReductionBase` is SATISFIABLE at every
prime `ℓ`** (PROVEN).

This is not bookkeeping.  `IsReductionBase` pins the base by two
conditions on a `Subring ℚ` and no imports, and everything downstream —
`IsX0NeronDatum`, and with it the universally quantified
`exists_sharpSievePrime` — is worthless if no pair `(R, toF)` satisfies
them: an unsatisfiable `base` field would make every datum impossible
and the sharpness leaf VACUOUSLY true.  So this theorem is the
non-vacuity certificate for the whole pinning, and it is what the
docstring of `IsReductionBase` asserts informally when it argues that
the conditions pin `R = ℤ_(ℓ)`.

The witness is the honest one.  `R` is `ℤ` localized at the prime ideal
`(ℓ)`, realized inside `ℚ` by `Localization.subalgebra.ofField` — which
is exactly "the rationals whose denominator is prime to `ℓ`" — and `toF`
is `IsLocalization.lift` of `ℤ → 𝔽_ℓ`, legitimate because every `s ∉ (ℓ)`
becomes a unit mod `ℓ`.  That unit is produced from BÉZOUT
(`Prime.coprime_iff_not_dvd`) rather than from the field structure of
`ZMod ℓ`, which keeps the proof clear of the
`CommRing`-versus-`GroupWithZero` monoid diamond on `ZMod ℓ`.

Surjectivity is surjectivity of `ℤ → 𝔽_ℓ` through `lift_eq`; and
`ker toF = nonunits` is `IsLocalization.AtPrime.isUnit_mk'_iff`
(`mk' a s` is a unit iff `a ∉ (ℓ)`) matched against
`lift_mk'_spec` (`toF (mk' a s) = 0` iff `a ≡ 0 mod ℓ`).  Note `ℓ.Prime`
is genuinely needed here to build the witness, even though
`IsReductionBase` derives it as a consequence for any pair satisfying
the two conditions. -/
theorem exists_isReductionBase (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ (R : Subring ℚ) (toF : R →+* ZMod ℓ), IsReductionBase ℓ R toF := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : ((ℓ : ℤ)) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  set I : Ideal ℤ := Ideal.span {(ℓ : ℤ)} with hI
  haveI hIp : I.IsPrime := by
    rw [hI, Ideal.span_singleton_prime hℓ0]
    exact Nat.prime_iff_prime_int.mp hℓ
  have hmemI : ∀ a : ℤ, a ∈ I ↔ ((a : ZMod ℓ) = 0) := by
    intro a
    rw [hI, Ideal.mem_span_singleton, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hS : I.primeCompl ≤ nonZeroDivisors ℤ := Ideal.primeCompl_le_nonZeroDivisors I
  set R₀ : Subalgebra ℤ ℚ := Localization.subalgebra.ofField ℚ I.primeCompl hS
  haveI : IsLocalization I.primeCompl R₀ :=
    Localization.subalgebra.isLocalization_ofField ℚ I.primeCompl hS
  haveI : IsLocalization I.primeCompl (R₀.toSubring) :=
    inferInstanceAs (IsLocalization I.primeCompl R₀)
  have hunit : ∀ y : I.primeCompl, IsUnit ((Int.castRingHom (ZMod ℓ)) (y : ℤ)) := by
    intro y
    have hnd : ¬ ((ℓ : ℤ) ∣ (y : ℤ)) := by
      intro hd
      refine y.2 ?_
      exact (hmemI (y : ℤ)).mpr (by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd)
    obtain ⟨u, v, huv⟩ :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hnd
    show IsUnit (((y : ℤ) : ZMod ℓ))
    refine IsUnit.of_mul_eq_one ((v : ℤ) : ZMod ℓ) ?_
    have hc := congrArg (fun z : ℤ => (z : ZMod ℓ)) huv
    push_cast at hc
    rw [ZMod.natCast_self, mul_zero, zero_add] at hc
    rw [mul_comm]
    exact hc
  refine ⟨R₀.toSubring, IsLocalization.lift (S := R₀.toSubring) hunit, ?_, ?_⟩
  · intro z
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective (n := ℓ) z
    exact ⟨algebraMap ℤ (R₀.toSubring) n, by rw [IsLocalization.lift_eq]; rfl⟩
  · intro r
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl r
    have hpc : (a ∈ I.primeCompl) ↔ a ∉ I := Iff.rfl
    rw [IsLocalization.AtPrime.isUnit_mk'_iff, hpc, not_not,
      IsLocalization.lift_mk'_spec, mul_zero]
    simpa [Int.castRingHom] using (hmemI a).symm

/-- **The good-reduction datum exists at every odd `ℓ ∤ N`** (PROVEN,
over `exists_isReductionBase` and `exists_x0NeronDatum_of_base`).

The base is constructed rather than posited — that is the whole of the
proof — and the residual geometric content sits in
`exists_x0NeronDatum_of_base`, which is the same statement with the base
HANDED TO IT.  That is how the literature states it (models over a given
discrete valuation ring), and it means a prover attacking the remaining
leaf starts from a concrete `ℤ_(ℓ)` instead of having to invent one. -/
theorem exists_x0NeronDatum (N ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓN : ¬ ℓ ∣ N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (hX : IsX0Compactification N strX strY j) (jac : IsJacobianOf strX ab o) :
    ∃ (R : Subring ℚ) (toF : R →+* ZMod ℓ) (X' J' XZ YZ JZ : Scheme.{0})
      (strX' : X' ⟶ SpecF ℓ) (jstr' : J' ⟶ SpecF ℓ)
      (ab' : AbelianSchemeStruct jstr') (o' : RelPoint strX' (𝟙 (SpecF ℓ)))
      (jac' : IsJacobianOf strX' ab' o') (xstr : XZ ⟶ SpecLoc R)
      (ystr : YZ ⟶ SpecLoc R) (jZ : YZ ⟶ XZ) (jstrZ : JZ ⟶ SpecLoc R)
      (abZ : AbelianSchemeStruct jstrZ) (oZ : RelPoint xstr (𝟙 (SpecLoc R)))
      (jacZ : IsJacobianOf xstr abZ oZ),
      Nonempty (IsX0NeronDatum N ℓ R toF jac jac'
        (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) := by
  obtain ⟨R, toF, hbase⟩ := exists_isReductionBase ℓ hℓ
  obtain ⟨X', J', XZ, YZ, JZ, strX', jstr', ab', o', jac', xstr, ystr, jZ, jstrZ,
    abZ, oZ, jacZ, hd⟩ :=
    exists_x0NeronDatum_of_base N ℓ hℓ hℓ2 hℓN R toF hbase hX jac
  exact ⟨R, toF, X', J', XZ, YZ, JZ, strX', jstr', ab', o', jac', xstr, ystr, jZ,
    jstrZ, abZ, oZ, jacZ, hd⟩

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
the sibling `y0HasNoRationalPoint_prod_two_primes` no longer owns them.

So do NOT dispatch anyone at `y0HasNoRationalPoint_fortyFive`, `_fiftyFour`,
`_sixtyThree` or `_seventyFive`: there is nothing left to prove at any of the
four.  The one open node behind them is `exists_x0Sieve`, and it is shared by
all four — four dispatches at the levels would be four workers discovering the
same single leaf. -/
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

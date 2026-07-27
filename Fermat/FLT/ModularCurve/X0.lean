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
  (`exists_x0Compactification`, `nonempty_cuspIndexing` — the latter is
  what `exists_rationalCusps` was decomposed into on 2026-07-27, and it
  needs only the EASY direction of the cusp classification);
* `J_0(N)` as an actual abelian scheme, its Mordell–Weil group, and the
  reduction map with its formal-group kernel — `neronKernel_torsionFree`
  for the kernel, `exists_x0NeronDatum_of_base` for the models, and
  `exists_isX0Compactification_specialFibre` for the identification of
  the special fibre.  `card_le_of_rankZeroJacobian` itself is PROVEN over
  those, as of 2026-07-27;
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
-- `AbelianSchemeStruct.mulByNat` / `zeroSection` and their free properties
-- (`isProper_mulByNat`, `locallyOfFiniteType_mulByNat`, `nsmul_val`,
-- `zero_val`, `zeroSection_comp_mulByNat`), consumed by the étale-rigidity
-- half of `neronKernel_torsionFree`.  This module imports only
-- `AbelianScheme` from the project, so no cycle is created.
public import Fermat.FLT.Modularity.AbelianSchemeIsogeny
-- `AlgebraicGeometry.FormallyUnramified`, and in particular the instance
-- `FormallyUnramified.isOpenImmersion_diagonal`: the diagonal of a formally
-- unramified morphism locally of finite type is an OPEN immersion.  Together
-- with `IsSeparated` (diagonal a CLOSED immersion) this is what makes
-- `section_eq_of_formallyUnramified` — the rigidity lemma — go through.
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
-- `isIso_iff_isOpenImmersion_and_surjective`, used to turn the clopen
-- equalizer of two sections into an isomorphism.
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
-- `PrimeSpectrum.irreducibleSpace` for a domain, which is how `Spec ℤ_(ℓ)`
-- is seen to be connected in the rigidity argument.
public import Mathlib.RingTheory.Spectrum.Prime.Topology
-- `Fermat.FLT.ModularCurve.EllipticScheme`: the assembly of
-- `exists_ellipticScheme_of_weierstrass` below, out of the projective
-- Weierstrass model as a `Scheme`.
--
-- **This import is deliberately NON-public, and it must stay that way.**  That
-- module reaches `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean`
-- and through it `Mathlib/Tactic/Ring/NamePolyVars.lean`, which reserves the
-- ATOM `over` as a global token — Lean's token table is global, so a reserved
-- atom is a keyword whether or not its notation is opened.  A `public import`
-- would propagate that token to `MazurTorsion.lean` and its whole dependent
-- cone, where `ModThree.lean` uses mathlib's `Ideal.LiesOver.over`, breaking
-- files several modules downstream at their `over` occurrence rather than at
-- the import.  A non-public import confines the token to THIS file, where the
-- single affected field is written `«over»`.
--
-- The only thing consumed from it is `exists_ellipticScheme_of_projModel`, in a
-- PROOF BODY; its statement is existential over the scheme and mentions neither
-- `proj` nor `projToSpec`, which is exactly what makes a non-public import
-- sufficient.
import Fermat.FLT.ModularCurve.EllipticScheme
-- The smooth-compactification theorem for curves over a field, which is what
-- turns `Y_0(N)` into `X_0(N)`; see `exists_compactificationY0` and
-- `exists_x0Compactification` below.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveCompactification
-- `AbelianSchemeStruct.mulByNat` (the morphism `[n] : E ⟶ E`),
-- `AbelianSchemeStruct.zeroSection`, and the two Yoneda bridges
-- `nsmul_val` / `zero_val` that turn `n • x` and `0` on relative points into
-- COMPOSITES with those fixed morphisms.  They are what makes the torsion
-- subscheme `C[n]` formable here (`CyclicSubgroupOfOrder.torsionScheme`); see
-- the note at `exists_torsionSubscheme` correcting the earlier claim that this
-- module "does NOT help".
public import Fermat.FLT.Modularity.AbelianSchemeIsogeny
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
-- `AlgebraicGeometry.Flat`: the flatness half of "finite locally free", which
-- is what makes `CyclicSubgroupOfOrder` the Katz–Mazur moduli problem
-- `[Γ₀(N)]` rather than a strictly larger one.  See the `flat` field of
-- `CyclicSubgroupOfOrder` and the faithfulness audit of
-- `exists_coarseModuliY0_of_pos`.
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
-- `IsSchemeTheoreticallyDominant` and its stability under FLAT BASE CHANGE
-- (`IsSchemeTheoreticallyDominant.of_isPullback`) — this is what proves
-- `ker_sqCover_spanScheme`, since over `Spec ℚ` every structure morphism is
-- flat, so both projections of a fibre square are flat base changes.
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
-- `IsPullback.of_bot`: the pasting lemma that exhibits each half of
-- `sqCover` as a base change of the tautological cover.  (`.Defs`, imported
-- below, has `IsPullback` but not the pasting lemmas.)
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
-- `RingHom.injective_iff_ker_eq_bot`, used to turn mathlib's
-- `Hom.toImage_app_injective` into `(Hom.toImage _).ker = ⊥`.
public import Mathlib.RingTheory.Ideal.Maps
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
-- `Algebra.IsInvariant`, the ring-theoretic half of GIT: it is the hypothesis
-- of `specInvariants_universal`, the pure geometric-invariant-theory leaf that
-- `exists_gamma0Atlas` is split along.
public import Mathlib.RingTheory.Invariant.Basic
-- The GIT quotient theorem itself, proved mathlib-facing and modular-curve-free in
-- `Fermat/FLT/Mathlib/AlgebraicGeometry/InvariantQuotient.lean`; it closes the
-- `¬ IsAffine` branch of `specInvariants_universal`.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.InvariantQuotient

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
`AbelianSchemeStruct` on a pullback.

**THAT REFUTING CHECK HAS NOW FIRED — the paragraph above is half stale
(noticed 2026-07-27).**  It read "nothing does: every occurrence of
`AbelianSchemeStruct` in the tree is a binder or an existential", and
named its own refutation: `grep -rn "AbelianSchemeStruct" Fermat/`
finding a producer rather than a consumer.  It now finds one, and of
exactly the right shape: `AbelianSchemeStruct.baseChange`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean:429`) constructs an
`AbelianSchemeStruct (pullback.snd f g)` — an abelian-scheme structure on
a pullback — and is sorry-free.  `AbelianSchemeStruct.ofMorphisms`
(`Modularity/AbelianScheme.lean`) is a second producer.

**What that opens, and what it does not.**  It supplies the
ABELIAN-SCHEME half of base change only.  A `Gamma0Datum` also carries a
`CyclicSubgroupOfOrder`, so turning base change of `Γ₀(N)`-data into a
*construction* still needs (a) the level structure transported to the
pullback — `C ×_T T'` with its closed immersion, finiteness, flatness and
geometric fibres — and (b) an `IsBaseChangeOf` witness assembled from the
two halves.  Neither exists today; the check that would refute THAT is
`grep -rn "CyclicSubgroupOfOrder" Fermat/`, which currently finds the
structure only in this file and in `MazurTorsion.lean`, with no transport
lemma anywhere.  Note also that this file imports
`Modularity.AbelianScheme` but NOT `Modularity.AbelianSchemeIsogeny`, so
the descent route additionally costs that import.

So the fppf-descent route is no longer blocked by a missing producer; it
is blocked by the level-structure half alone.  The cut taken here needs
no base change to be constructed, only to be *exhibited by the leaf*,
which is why it goes through either way. -/

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
  /-- **rigidification**: every datum **over a `ℚ`-scheme** is, after a
  faithfully flat quasi-compact base change, a base change of `dM`.

  **FALSITY AUDIT (2026-07-27): the binder `g` is what makes this field
  TRUE, and without it `Gamma0Atlas N` is EMPTY.**  The field previously
  read `∀ {T : Scheme.{0}} (d : Gamma0Datum N T), …`, quantifying over
  every scheme whatever, and in that form it is false — so
  `exists_gamma0Atlas` and `exists_gamma0GITPresentation` were both
  unprovable rather than merely open.

  *The counterexample*, at `N = 1`.  Take `T = Spec 𝔽₅`, `E` any elliptic
  curve over `𝔽₅`, and `C` its zero section: `C ⟶ E` is a closed
  immersion, `C ⟶ T` is an isomorphism hence finite and flat, `C` is
  closed under the group law and under inversion, and `geom_cyclic` holds
  at `N = 1` with `y = 0` (`addOrderOf 0 = 1`, and `LiesIn` cuts out
  exactly `zmultiples 0`).  So this is a `Gamma0Datum 1 T` with `T`
  nonempty.  The old field then demands `p : T' ⟶ T` **surjective**,
  forcing `T' ≠ ∅`, together with `m : T' ⟶ M`; composing with `strM`
  gives `T' ⟶ Spec ℚ`, and composing `p` with nothing gives `T' ⟶ Spec 𝔽₅`.
  A nonempty scheme has `Γ(T', 𝒪) ≠ 0`, and that nonzero ring would
  receive ring maps from both `ℚ` and `𝔽₅` — so `5` is simultaneously
  invertible and zero.  No such `T'` exists.

  *The check that would refute this audit*: show `Gamma0Datum N T` is
  uninhabited whenever `T` is nonempty and admits no morphism to
  `Spec ℚ`.  It is not — nothing in `Gamma0Datum`, `AbelianSchemeStruct`
  or `CyclicSubgroupOfOrder` mentions `ℚ` or characteristic zero.

  Adding `g` costs nothing downstream: the only consumer,
  `Gamma0Atlas.toIsCoarseModuliY0`, already has the base point
  `g : T ⟶ SpecQ` in scope, because `IsCoarseModuliY0` quantifies over
  `S`-schemes throughout.  `_g` is a *hypothesis on `T`*, not data the
  field uses — hence the underscore; by `subsingleton_hom_specQ` it is
  unique when it exists. -/
  cover : ∀ {T : Scheme.{0}} (_g : T ⟶ SpecQ) (d : Gamma0Datum N T),
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
      obtain ⟨T', p, d', m, hflat, hsurj, hqc, ⟨hbp⟩, ⟨hbm⟩⟩ := A.cover g d
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

/-! ### Splitting the atlas: the modular-curve half and the GIT half

`exists_gamma0Atlas` is DERIVED (2026-07-27) from two leaves that share
no subject matter, and its own docstring is what made the split
mechanical.  Of the three items it listed as "what closing this needs",
item 3 — the categorical quotient of an affine scheme by a finite group —
mentions no modular curve at all.  It is now a separate leaf,
`specInvariants_universal`, statable and closable by someone who has
never read this file.  Items 1 and 2 stay together in
`exists_gamma0GITPresentation`, because they are one construction: the
rigidified moduli scheme and the torsor that rigidifies it.

**Why the presentation is affine-with-a-finite-group, and why that is not
an extra assumption.**  (8.1.1) does not merely assert that a quotient
exists; it *constructs* `M(𝒫)` as `𝔐(𝒫, [Γ(n)])/G` and notes that the
quotient "exists because `𝔐(𝒫, [Γ(n)])` is itself affine".  So `M`
affine, `G = GL₂(ℤ/n)` finite, and `Y = Spec` of the invariants is
exactly what Katz–Mazur build; the `quotient` field of `Gamma0Atlas` is a
*consequence* of that construction.  Stating the consequence instead of
the construction is what kept a pure GIT statement locked inside a
modular-curve leaf.

**How the two halves meet.**  `Gamma0Atlas.quotient` asks that a morphism
`φ` out of `M` which cannot separate two rigidifications of one datum
factor uniquely through the classifying map of `dM`.  GIT asks instead
that `φ` be `G`-invariant.  The bridge is `dM_equivariant`: `σ^*dM ≅ dM`
exhibits `𝟙` and `Spec σ` as two rigidifications of ONE datum, so `φ`'s
inability to separate them *is* `Spec σ ≫ φ = φ`.  That is the entire
content of `Gamma0GITPresentation.toGamma0Atlas`, and it is why the
presentation carries `dM_equivariant` in place of `quotient`.

**THE SPLIT CANNOT WEAKEN THE TREE, AND THAT IS MECHANICAL.**
`Gamma0GITPresentation.toGamma0Atlas` is a function *from* the new leaf
*to* the old one, so `exists_gamma0GITPresentation` is at least as strong
as `exists_gamma0Atlas`, hence as `exists_coarseModuliY0_of_pos`.  The
junk witness refuted above transports along it: a presentation with
`A = B = ℚ`, `G = 1` and `classify g d = g` would produce precisely the
atlas that was shown to fail `quotient`, so it does not satisfy the new
leaf either. -/

/-- **GIT for an AFFINE target, in the form `Spec R`** (PROVEN
2026-07-27): a `G`-invariant morphism `Spec A ⟶ Spec R` factors uniquely
through `Spec` of the invariant ring.

This is the half of `specInvariants_universal` that is pure algebra, and
it needs no geometry at all: `Spec` is fully faithful, so `φ = Spec.map f`
for a unique `f : R ⟶ A`; `Spec.map_injective` turns `G`-invariance of
`φ` into `G`-invariance of `f`; `Algebra.IsInvariant` lifts `f` pointwise
to `B`, and `hinj` makes that lift a ring homomorphism (each ring axiom
is checked after applying the injective `algebraMap B A`) and makes it
the only one.

It is stated for EVERY triple `(B, A, G)` rather than as a hypothesis of
`specInvariants_universal`, because the reduction of a general target to
affine ones consumes it at the localised triples `(B_b, A_b, G)`. -/
theorem specInvariants_universal_specTarget {B A : Type} [CommRing B] [CommRing A]
    [Algebra B A] (G : Type) [Group G] [Finite G] [MulSemiringAction G A]
    [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (hinj : Function.Injective (algebraMap B A))
    {R : CommRingCat.{0}} (φ : Spec (CommRingCat.of A) ⟶ Spec R)
    (hinv : ∀ σ : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ)) ≫ φ = φ) :
    ∃! ψ : Spec (CommRingCat.of B) ⟶ Spec R,
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ ψ = φ := by
  classical
  set f : R ⟶ CommRingCat.of A := Spec.preimage φ
  have hφ : Spec.map f = φ := Spec.map_preimage φ
  -- the ring map underlying `φ` is `G`-invariant
  have hfinv : ∀ (σ : G) (r : R), σ • (f.hom r) = f.hom r := by
    intro σ r
    have h := hinv σ
    rw [← hφ, ← Spec.map_comp] at h
    exact congrArg (fun u : R ⟶ CommRingCat.of A => u.hom r) (Spec.map_injective h)
  -- so every value of it comes from `B`, and the lift is a ring homomorphism
  choose g hg using fun r : R =>
    Algebra.IsInvariant.isInvariant (A := B) (B := A) (G := G) (f.hom r)
      (fun σ => hfinv σ r)
  have hg1 : g 1 = 1 := hinj (by rw [hg, map_one, map_one])
  have hg0 : g 0 = 0 := hinj (by rw [hg, map_zero, map_zero])
  have hgm : ∀ x y, g (x * y) = g x * g y := by
    intro x y; exact hinj (by rw [hg, map_mul, map_mul, hg, hg])
  have hga : ∀ x y, g (x + y) = g x + g y := by
    intro x y; exact hinj (by rw [hg, map_add, map_add, hg, hg])
  let f' : R →+* B :=
    { toFun := g, map_one' := hg1, map_zero' := hg0, map_mul' := hgm, map_add' := hga }
  have hfactor : CommRingCat.ofHom f' ≫ CommRingCat.ofHom (algebraMap B A) = f :=
    CommRingCat.hom_ext (RingHom.ext hg)
  refine ⟨Spec.map (CommRingCat.ofHom f'), ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ Spec.map (CommRingCat.ofHom f') = φ
    rw [← Spec.map_comp, hfactor, hφ]
  · intro ψ' hψ'
    have hu : Spec.preimage ψ' ≫ CommRingCat.ofHom (algebraMap B A) = f := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, hψ', hφ]
    have hpre : Spec.preimage ψ' = CommRingCat.ofHom f' := by
      refine CommRingCat.hom_ext (RingHom.ext fun r => hinj ?_)
      have h1 := congrArg (fun u : R ⟶ CommRingCat.of A => u.hom r) hu
      have h2 : (algebraMap B A) (f' r) = (CommRingCat.Hom.hom f) r := hg r
      simp only [CommRingCat.hom_ofHom, h2]
      simpa using h1
    rw [← Spec.map_preimage ψ', hpre]

/-- **GIT: `Spec` of a ring of invariants is a categorical quotient in the
category of ALL schemes** (PROVEN 2026-07-27, sorry-free and axiom-clean;
formerly a sorry leaf).

Let a finite group `G` act on a commutative ring `A` by ring
automorphisms and let `B` be its invariant ring: `Algebra.IsInvariant B A
G` says every `G`-fixed element of `A` comes from `B`, and
`SMulCommClass G B A` says conversely that everything from `B` is
`G`-fixed (mathlib's own `smul_algebraMap`, since `σ • (b • 1) = b • (σ •
1) = b • 1`).  Then every `G`-invariant morphism `φ : Spec A ⟶ Y'`, to an
ARBITRARY scheme `Y'`, factors uniquely through `π = Spec (B → A)`.

This is Mumford, *Geometric Invariant Theory*, Ch. 0 §2 (and its
Amplification 1.3), and Katz–Mazur Chapter 7 *Quotients by finite
groups*.  It is the ONLY thing `exists_gamma0Atlas` needed from geometric
invariant theory, and it names no modular curve, no moduli problem and
no elliptic scheme.

## State of the pin, rechecked 2026-07-27

Mathlib has the **ring-theoretic half** and not the scheme-level
statement:

* `Algebra.IsInvariant` (`Mathlib/RingTheory/Invariant/Defs.lean`), with
  `Algebra.IsInvariant.isIntegral`, `.exists_smul_of_under_eq` and
  `.orbit_eq_primesOver` (`Mathlib/RingTheory/Invariant/Basic.lean`):
  `π` is integral, and `G` acts transitively on the primes over a given
  prime, i.e. the fibres of `π` are exactly the `G`-orbits.
* `Spec` is fully faithful (`Spec.preimage`, `Spec.map_injective`), and
  `Scheme.Cover.glueMorphisms` glues morphisms along an open cover.

*The refuting check*:
`grep -rni "categorical quotient" .lake/packages/mathlib/Mathlib/`
returns nothing today, and `grep -rn "IsInvariant" ~/cs/FLT/FLT/` finds
only the number-theoretic uses (`Galois/Infinite.lean`,
`Deformations/.../IntegralClosure.lean`), never a scheme-level quotient.

## HOW IT IS PROVEN

**The AFFINE case** is `specInvariants_universal_specTarget` (2026-07-27),
consumed by the `IsAffine Y'` branch of the proof below.  It is exactly
as short as it looks: `Spec` is fully faithful, so `φ` is `Spec.map f`
for a unique ring map `f : R ⟶ A`; `G`-invariance of `φ` is
`G`-invariance of `f` by `Spec.map_injective`; so `f` lands in `B` by
`Algebra.IsInvariant`, and `hinj` makes the lift a ring homomorphism and
makes it unique.

**The REDUCTION of an arbitrary target to affine ones** — formerly the
`sorry` in the `¬ IsAffine Y'` branch — is
`Fermat.InvariantQuotient.exists_unique_of_isInvariant`, in the
mathlib-facing module
`Fermat/FLT/Mathlib/AlgebraicGeometry/InvariantQuotient.lean`
(2026-07-27).  It proves the statement for EVERY target, so the
`IsAffine Y'` branch above survives only because it is the shorter route
in that case.  The route taken there is the one this docstring predicted:
`π` is integral hence closed, and surjective, and its fibres are
`G`-orbits, so a `G`-stable open of `Spec A` is `π ⁻¹` of an open of
`Spec B`; call `D b` GOOD when `φ (π ⁻¹ (D b))` lies in a single affine
open of `Y'`, note that the good basic opens are closed downwards and
cover `Spec B`, hence form a BASIS, and glue over the resulting cover.

Two things made it shorter than the docstring feared.  First, gluing
along a **locally directed** cover (`Cover.LocallyDirected.ofIsBasisOpensRange`,
which a basis supplies for free) needs only compatibility with the
transition maps `D b ⊆ D b'`, not the pullback compatibility of
`Scheme.Cover.glueMorphisms` — so no pullback of two basic opens is ever
identified.  Second, global uniqueness is NOT a separate "`π` is epi"
argument: `Scheme.Cover.hom_ext` on the same cover reduces it to the
local uniqueness already in hand.

The reduction consumes the affine case **at the localised triples
`(B_b, A_b, G)`**, not only at `(B, A, G)` — which is why the affine case
is stated for every triple rather than carved out as a hypothesis of this
one, and why `InvariantQuotient` states its affine case for a bare ring
map `ι : B →+* A` with a bare family of ring endomorphisms of `A` rather
than for a `MulSemiringAction`: at a localisation, producing the class
instances would be pure overhead, whereas the ring maps are just
`IsLocalization.map`.  The one genuinely new piece of algebra there is
that **invariants localise** (`exists_awayMap_eq_of_fixed`): finiteness
of `G` lets a single power of `ι b` clear denominators for all `σ` at
once, and `(ι b) ^ N * a` is then genuinely `G`-fixed.

*Refuting check for "the reduction is unavoidable"*: an `EffectiveEpi`
or descent-shaped route would refute it — but `π` is not flat, so the
fpqc machinery that `Gamma0Atlas.toIsCoarseModuliY0` uses does not apply
here, and `grep -rn "EffectiveEpi" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/`
finds instances only for open covers and for fpqc covers. -/
theorem specInvariants_universal {B A : Type} [CommRing B] [CommRing A] [Algebra B A]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G B A]
    [Algebra.IsInvariant B A G]
    (hinj : Function.Injective (algebraMap B A))
    {Y' : Scheme.{0}} (φ : Spec (CommRingCat.of A) ⟶ Y')
    (hinv : ∀ σ : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ)) ≫ φ = φ) :
    ∃! ψ : Spec (CommRingCat.of B) ⟶ Y',
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ ψ = φ := by
  classical
  by_cases hY : IsAffine Y'
  · -- PROVEN: transport along `Y' ≅ Spec Γ(Y', ⊤)` and apply the algebra.
    haveI := hY
    obtain ⟨ψ₀, hψ₀, huniq⟩ :=
      specInvariants_universal_specTarget G hinj (φ ≫ Y'.isoSpec.hom)
        (by intro σ; rw [← Category.assoc, hinv σ])
    refine ⟨ψ₀ ≫ Y'.isoSpec.inv, ?_, ?_⟩
    · show Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ ψ₀ ≫ Y'.isoSpec.inv = φ
      rw [← Category.assoc, hψ₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro ψ' hψ'
      have hψ'2 : Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ ψ' = φ := hψ'
      have hE : ψ' ≫ Y'.isoSpec.hom = ψ₀ := huniq _ (by
        show Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ ψ' ≫ Y'.isoSpec.hom
            = φ ≫ Y'.isoSpec.hom
        rw [← Category.assoc, hψ'2])
      rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · -- PROVEN (2026-07-27): the reduction of an arbitrary target to affine ones, by
    -- descending the `G`-stable opens `φ ⁻¹ (Vᵢ)` to basic opens of `Spec B` and gluing.
    -- The whole argument is mathlib-facing and lives in
    -- `Fermat/FLT/Mathlib/AlgebraicGeometry/InvariantQuotient.lean`; note it proves the
    -- statement for EVERY target, affine or not, so the `IsAffine` branch above is now
    -- only kept because it is the shortest route in that case.
    exact InvariantQuotient.exists_unique_of_isInvariant G hinj φ hinv

/-- **A Katz–Mazur atlas presented the way (8.1.1) actually builds it**:
the rigidified moduli scheme as `Spec A` with a finite group `G` acting,
and the coarse space as `Spec` of the invariants.

This is `Gamma0Atlas` with its `quotient` field replaced by the data that
*produces* it — see the section comment above.  The fields it shares with
`Gamma0Atlas` (`classify`, `classify_natural`, `cover`) are unchanged and
documented there; the ones that differ are:

* `A`, `B`, `G` with `Algebra.IsInvariant B A G`: the rigidified moduli
  scheme is `M = Spec A`, affine, the deck group `G = GL₂(ℤ/n)` is
  finite, and the coarse space is `Y = Spec B` with `B = A^G`.
* `classify_dM`: the classifying map of the universal family IS the
  quotient map `π`.  This is what makes `Y` the quotient of `M` rather
  than an unrelated scheme receiving a map.
* `dM_equivariant`: `σ^*dM ≅ dM` for every `σ : G`, stated as "there is a
  datum over `M` which is a base change of `dM` both along `𝟙` and along
  `Spec σ`".  It is phrased that way rather than as an isomorphism
  because `IsBaseChangeOf` is the only comparison of `Γ₀(N)`-data this
  development has, and taking `h = 𝟙` in it is exactly isomorphism of
  data over a fixed base (see `IsBaseChangeOf`'s docstring). -/
structure Gamma0GITPresentation (N : ℕ) where
  /-- the coordinate ring of the rigidified moduli scheme `𝔐([Γ₀(N)], [Γ(n)])` -/
  A : Type
  [commRing_A : CommRing A]
  /-- the ring of invariants, whose spectrum is the coarse space -/
  B : Type
  [commRing_B : CommRing B]
  [algebra_BA : Algebra B A]
  /-- the deck group `GL₂(ℤ/n)` of the rigidification -/
  G : Type
  [group_G : Group G]
  [finite_G : Finite G]
  [action_GA : MulSemiringAction G A]
  [smulComm_GBA : SMulCommClass G B A]
  [isInvariant_BAG : Algebra.IsInvariant B A G]
  /-- `B` is a subring of `A`, not merely an algebra over it -/
  injective_algebraMap : Function.Injective (algebraMap B A)
  /-- the structure morphism of the coarse space -/
  str : Spec (CommRingCat.of B) ⟶ SpecQ
  /-- the structure morphism of the rigidified moduli scheme -/
  strM : Spec (CommRingCat.of A) ⟶ SpecQ
  /-- the classifying map of the moduli problem, Katz–Mazur (8.1.3) -/
  classify : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), Gamma0Datum N T → RelPoint str g
  /-- the classifying map is natural in the base -/
  classify_natural : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {d' : Gamma0Datum N T'} {d : Gamma0Datum N T},
    IsBaseChangeOf h d' d → classify g' d' = RelPoint.pre h hg (classify g d)
  /-- the universal family carried by the rigidified moduli scheme -/
  dM : Gamma0Datum N (Spec (CommRingCat.of A))
  /-- the classifying map of the universal family is the quotient map -/
  classify_dM : (classify strM dM).1 = Spec.map (CommRingCat.ofHom (algebraMap B A))
  /-- **rigidification**: every datum **over a `ℚ`-scheme** is, after a
  faithfully flat quasi-compact base change, a base change of `dM`.

  The binder `_g` is not decoration — see the FALSITY AUDIT on
  `Gamma0Atlas.cover`, which this field must match for
  `toGamma0Atlas` to typecheck.  Without it the field is false at
  `N = 1` over `T = Spec 𝔽₅`, and the whole structure is empty. -/
  cover : ∀ {T : Scheme.{0}} (_g : T ⟶ SpecQ) (d : Gamma0Datum N T),
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma0Datum N T')
      (m : T' ⟶ Spec (CommRingCat.of A)),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      Nonempty (IsBaseChangeOf p d' d) ∧ Nonempty (IsBaseChangeOf m d' dM)
  /-- **`G`-equivariance of the universal family**: `σ^*dM ≅ dM` -/
  dM_equivariant : ∀ σ : G, ∃ d₁ : Gamma0Datum N (Spec (CommRingCat.of A)),
    Nonempty (IsBaseChangeOf (𝟙 (Spec (CommRingCat.of A))) d₁ dM) ∧
    Nonempty (IsBaseChangeOf
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ))) d₁ dM)

/-- **A GIT presentation IS an atlas** (PROVEN 2026-07-27): the
`quotient` field of `Gamma0Atlas` derived from the affine presentation
and `specInvariants_universal`.

The only step with content is turning `Gamma0Atlas.quotient`'s
separation hypothesis into `G`-invariance, which `dM_equivariant`
does — see the section comment above. -/
noncomputable def Gamma0GITPresentation.toGamma0Atlas {N : ℕ}
    (P : Gamma0GITPresentation N) : Gamma0Atlas N :=
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.group_G
  letI := P.finite_G
  letI := P.action_GA
  letI := P.smulComm_GBA
  letI := P.isInvariant_BAG
  { Y := Spec (CommRingCat.of P.B)
    str := P.str
    classify := P.classify
    classify_natural := P.classify_natural
    M := Spec (CommRingCat.of P.A)
    strM := P.strM
    dM := P.dM
    cover := P.cover
    quotient := by
      intro Y' φ hsep
      rw [P.classify_dM]
      refine specInvariants_universal P.G P.injective_algebraMap φ ?_
      intro σ
      -- `𝟙` and `Spec σ` are two rigidifications of the SAME datum `d₁`,
      -- so the separation hypothesis says `φ` cannot tell them apart.
      obtain ⟨d₁, ⟨h1⟩, ⟨h2⟩⟩ := P.dM_equivariant σ
      have h := hsep (𝟙 _) _ d₁ h1 h2
      rw [Category.id_comp] at h
      exact h.symm }

/-! ### Splitting the modular-curve half: representability, and the level-`n` torsor

`exists_gamma0GITPresentation`'s docstring below itemises what closing it
needs, and says of those items that "each is stated so that it can be
dispatched without the others".  Until 2026-07-27 that was true of the
English and false of the Lean — all three items sat inside one `sorry`.
Item 3 was split off as `specInvariants_universal`; items 1 and 2 are
split from each other here.

**The cut that does NOT work, and why it is worth recording.**  The
obvious split — a structure `Gamma0Rigidification` holding item 1, with
item 2 stated as `∀ R : Gamma0Rigidification N, «cover» R` — is the
junk-witness trap, and the resulting leaf would be FALSE.  An arbitrary
inhabitant of such a structure need not be the genuine moduli scheme:
`A = B = ℚ`, `G = 1`, `dM` any single `Γ₀(N)`-datum over `Spec ℚ` and
`classify g d = g` satisfies every field that does not mention `cover`
(`classify_dM` because `Spec.map (algebraMap ℚ ℚ) = 𝟙` and morphisms to
`Spec ℚ` are unique, `dM_equivariant` because `G` is trivial), and
`cover` fails for it as soon as the `Γ₀(N)`-problem has more than one
geometric point.  Producing the structure existentially is the standard
repair, but that puts both items back in one leaf.

**The cut that does work** interposes the notion which makes the two
halves independent — the one Katz–Mazur themselves interpose, a *full
level-`n` structure*.  Item 2 becomes `exists_fullLevelStructure_cover`,
a statement about ONE datum which names no moduli scheme; item 1 becomes
`exists_gamma0GITPresentation_of_cover`, which receives item 2 as a
hypothesis and so owes only representability.  Neither quantifies over
an under-determined structure, so neither can be false for that reason,
and the assembly is three lines.

**Why the Katz–Mazur presentation and not fppf descent.**  The section
comment before `Gamma0Atlas` records that the descent route — build
`classify` by descending `m ≫ π` along the rigidifying cover instead of
assuming it — was blocked because nothing constructs an
`AbelianSchemeStruct` on a pullback, and notes that this is no longer
true (`AbelianSchemeStruct.baseChange`).  It is still not the right
route, for a reason independent of base change: descending `m ≫ π` along
`p` needs `π` to COEQUALISE any two rigidifications `a, b : Z ⟶ M` of one
datum, and `dM_equivariant` gives only that `π` coequalises `𝟙` and
`Spec σ` for a GLOBAL `σ : G`.  Two rigidifications of one datum differ
by a section of the `G`-torsor of level structures, which lies in `G`
only fppf-locally, so the descent route needs a strictly stronger field —
the torsor property — which is the same Katz–Mazur citation, plus the
whole level-structure base-change apparatus.  It relocates the citation
and adds cost; it does not shrink it.  *The check that would refute
this*: derive `a ≫ π = b ≫ π` for two rigidifications of one datum from
the fields of `Gamma0GITPresentation` as they stand.
-/

/-- **A full level-`n` structure** on the elliptic scheme of a
`Γ₀(N)`-datum — Katz–Mazur's `[Γ(n)]`, in the fibrewise idiom this file
already uses for `CyclicSubgroupOfOrder.geom_cyclic`.

The data is a pair of sections `P`, `Q` of `E ⟶ T` which at every
geometric point is a basis of the `n`-torsion: `geom_basis` says a
geometric point of `E` is killed by `n` exactly when it is `a·P + b·Q`
for a UNIQUE pair `(a, b)`.

Three remarks.

* `n • P = 0` and `n • Q = 0` are consequences, not fields: apply
  `geom_basis` at `x = P`, which is `1·P + 0·Q`, and read the `←`
  direction.
* Over a `ℚ`-scheme this is equivalent to the scheme-theoretic
  definition, an isomorphism `(ℤ/n)²_T ≅ E[n]` of group schemes: `n` is
  invertible, so `E[n] ⟶ T` is finite étale, and a fibrewise
  isomorphism of finite étale group schemes is an isomorphism.  Stating
  it fibrewise keeps the same idiom as `geom_cyclic` and needs no
  `Scheme.Hom.finrank`.
* At `n = 0` the condition is unsatisfiable — `Fin 0` is empty while
  `0 • x = 0` always — which is why both consumers below carry
  `3 ≤ n`. -/
structure FullLevelStructure (n : ℕ) {N : ℕ} {T : Scheme.{u}}
    (d : Gamma0Datum N T) where
  /-- the first basis section -/
  P : RelPoint d.f (𝟙 T)
  /-- the second basis section -/
  Q : RelPoint d.f (𝟙 T)
  /-- at every geometric point `P` and `Q` are a basis of the `n`-torsion -/
  geom_basis : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (t : Spec (CommRingCat.of K) ⟶ T),
      letI := d.ab.addCommGroup t
      ∀ x : RelPoint d.f t, n • x = 0 ↔
        ∃! ab : Fin n × Fin n,
          x = (ab.1 : ℕ) • RelPoint.pre t (Category.comp_id t) P
              + (ab.2 : ℕ) • RelPoint.pre t (Category.comp_id t) Q

/-- **Every `Γ₀(N)`-datum over a `ℚ`-scheme acquires a full level-`n`
structure after a faithfully flat quasi-compact base change** (sorry
node) — item 2 of the itemisation on `exists_gamma0GITPresentation`
below, the level-`n` torsor, now a leaf of its own.

## What is cited

Katz–Mazur (8.1.1) rigidify by `[Γ(n)]`-structures for `n ≥ 3`
invertible on the base; over a `ℚ`-scheme every `n` is invertible.  The
content is that `E[n] ⟶ T` is finite étale of rank `n²` (Katz–Mazur
2.3.1; Silverman *AEC* III.6.4 for the fibres, plus flatness of the
multiplication-by-`n` kernel), so the sheaf
`Isom_T((ℤ/n)²_T, E[n])` is representable by a finite étale
`GL₂(ℤ/n)`-torsor `T' ⟶ T` — in particular flat, surjective and
quasi-compact — and the tautological isomorphism over `T'` is a full
level-`n` structure on the pulled-back datum.

## Why this is separable from the representability half

It mentions no moduli scheme: `T'`, `p` and `d'` are produced from `d`
alone.  That is what lets it be dispatched independently of
`exists_gamma0GITPresentation_of_cover`, and it is why the split is safe
— nothing here is quantified over an under-determined structure.

## What it needs that this project does not have

Base change of a `Γ₀(N)`-datum as a **construction**: `d'` must be
produced, not merely related to `d`.  The abelian-scheme half exists and
is sorry-free — `AbelianSchemeStruct.baseChange`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`) — and the
level-structure half does not.  *The check that would refute this*: a
`CyclicSubgroupOfOrder`-valued function taking a base-change square;
`grep -rn "CyclicSubgroupOfOrder" Fermat/` finds the structure only in
this file and in `MazurTorsion.lean`, with no transport lemma anywhere.
Note also that this file does not import
`Modularity.AbelianSchemeIsogeny`, so that import is part of the cost.

`hn` is load-bearing for TRUTH, not merely for the intended proof: at
`n = 0` the conclusion asks for an unsatisfiable `FullLevelStructure`
(see its docstring), so it cannot be dropped. -/
theorem exists_fullLevelStructure_cover {N : ℕ} (n : ℕ) (hn : 3 ≤ n)
    {T : Scheme.{0}} (g : T ⟶ SpecQ) (d : Gamma0Datum N T) :
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma0Datum N T'),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      Nonempty (IsBaseChangeOf p d' d) ∧ Nonempty (FullLevelStructure n d') :=
  sorry

/-- **Representability of the rigidified moduli problem** (sorry node) —
item 1 of the itemisation on `exists_gamma0GITPresentation` below, with
item 2 discharged by the hypothesis `hcov`.

Given that every `Γ₀(N)`-datum over a `ℚ`-scheme acquires a full
level-`n` structure fppf-locally — which is exactly
`exists_fullLevelStructure_cover` — the rigidified moduli scheme
`𝔐([Γ₀(N)], [Γ(n)])` exists as an AFFINE `ℚ`-scheme `Spec A` with the
finite deck group `G = GL₂(ℤ/n)` acting, carrying a universal family
`dM`, and the classifying map of `dM` is the quotient map onto
`Spec A^G`.

## What the prover of this node owes, and what it does NOT

Owes: Katz–Mazur **4.7** and **5.1.1** (the moduli problem `[Γ(n)]` is
representable, and affine, over `(Ell/ℤ[1/n])` for `n ≥ 3`), **6.6.1**
(`[Γ₀(N)]` is relatively representable, finite and flat over `(Ell)`),
and the fact that a relatively representable affine problem over a
representable one has an affine total moduli scheme — which is precisely
Katz–Mazur's parenthesis in (8.1.1), "exists because `𝔐(𝒫, 𝒮)` is itself
affine".  The universal property of `(Spec A, dM)` supplies the
classifying map `m : T' ⟶ Spec A` of a datum-with-level-structure, and
`hcov` supplies the `T'` to apply it to; together they are the `cover`
field of the conclusion.

Does NOT owe: the torsor.  That is `hcov`, and it is a hypothesis here.

## Faithfulness

`hcov` is a Prop-valued hypothesis, not an under-determined structure, so
this node cannot be false for the junk-witness reason discussed in the
section comment above.  It is also not vacuous: `hcov` is TRUE (it is the
statement of `exists_fullLevelStructure_cover`), so the conclusion
carries the full strength of `Nonempty (Gamma0GITPresentation N)`. -/
theorem exists_gamma0GITPresentation_of_cover (N : ℕ) (hN : 0 < N)
    (n : ℕ) (hn : 3 ≤ n)
    (hcov : ∀ {T : Scheme.{0}}, (T ⟶ SpecQ) → ∀ d : Gamma0Datum N T,
      ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma0Datum N T'),
        AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
        Nonempty (IsBaseChangeOf p d' d) ∧ Nonempty (FullLevelStructure n d')) :
    Nonempty (Gamma0GITPresentation N) :=
  sorry

/-- **Existence of the Katz–Mazur GIT presentation for `N ≥ 1`** (PROVEN
2026-07-27 from the two halves it was split into; the docstring below is
the CITATION it carried, retained because it is what the two halves
between them now owe).

This is the citation formerly attached to
`exists_coarseModuliY0_of_pos`, twice reduced:

* the **initiality** clause of `IsCoarseModuliY0` was never covered by it
  and is now PROVEN, in `Gamma0Atlas.toIsCoarseModuliY0` (2026-07-27);
* the **categorical quotient** — item 3 of the itemisation below, the one
  item that names no modular curve — is now the separate, entirely
  mathlib-facing leaf `specInvariants_universal` (2026-07-27).

The full citation, the matching of hypotheses, and the faithfulness audit
are recorded on `exists_coarseModuliY0_of_pos` below and are unchanged;
only the shape of what is assumed has moved.

## What closing this needs, as separable items

Each is stated so that it can be dispatched without the others, and each
carries the check that would refute its being open.

**All three are now SEPARATE LEAVES and none of them is this
declaration** (2026-07-27): item 1 is
`exists_gamma0GITPresentation_of_cover`, item 2 is
`exists_fullLevelStructure_cover`, item 3 is `specInvariants_universal`.
The section comment above explains why items 1 and 2 had to be separated
through `FullLevelStructure` rather than through a rigidification
structure.  The itemisation is kept here because it is the record of what
the citation covers, and because each item's refuting check is still the
right first thing to run.

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
3. **The categorical quotient of an affine scheme by a finite group** —
   **NO LONGER PART OF THIS LEAF.**  It was split off on 2026-07-27 as
   `specInvariants_universal`, where its citation, its state-of-the-pin
   survey and its proof sketch now live.  What remains here in its place
   is only the *presentation* — `A`, `B`, `G`, `classify_dM` and
   `dM_equivariant` — i.e. the assertion that Katz–Mazur's `𝔐(𝒫, [Γ(n)])`
   is affine with a finite deck group acting and that the classifying map
   of the universal family is the quotient map.  That is a statement about
   the modular curve, and it belongs here; the quotient property of
   `Spec (A^G)` is a statement about rings and schemes, and it does not.

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
theorem exists_gamma0GITPresentation (N : ℕ) (hN : 0 < N) :
    Nonempty (Gamma0GITPresentation N) :=
  exists_gamma0GITPresentation_of_cover N hN 3 le_rfl
    (fun {_T} g d => exists_fullLevelStructure_cover 3 le_rfl g d)

/-- **Existence of the Katz–Mazur atlas for `N ≥ 1`** (PROVEN 2026-07-27
from the two halves it was split into).

The citation now lives on `exists_gamma0GITPresentation` (the
modular-curve half) and on `specInvariants_universal` (the GIT half); the
section comment above `specInvariants_universal` explains the split and
why it cannot weaken the tree. -/
theorem exists_gamma0Atlas (N : ℕ) (hN : 0 < N) : Nonempty (Gamma0Atlas N) :=
  (exists_gamma0GITPresentation N hN).map Gamma0GITPresentation.toGamma0Atlas

/-- **Existence of the coarse moduli space `Y_0(N)` for `N ≥ 1`**
(PROVEN 2026-07-27 from `exists_gamma0Atlas`, which is itself now PROVEN
from `exists_gamma0GITPresentation` — the modular-curve half — and
`specInvariants_universal` — the GIT half, whose affine case is proven
too).

Everything below — the citation, the matching of hypotheses, the
faithfulness audit — describes what `exists_gamma0GITPresentation`
assumes, and is unchanged.  What is no longer assumed is the
**initiality** clause of
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

The remaining absences are carried by the two leaves the atlas was split
into on 2026-07-27, and they are now separated by subject matter: a
modular curve and `[Γ(n)]`-structures are what
`exists_gamma0GITPresentation` asks for; GIT is what
`specInvariants_universal` asks for, and its affine case is no longer an
absence — it is proven in `specInvariants_universal_specTarget`. -/
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

/-! ### Assembling the elliptic scheme: where the residual leaves live

The node below is ASSEMBLED (2026-07-27) and is no longer a single
`sorry`.  Its proof is `exists_ellipticScheme_of_projModel`, and that
theorem together with the five open leaves it rests on —
`nonempty_projGroupLaw`, `isProper_projToSpec`,
`smoothOfRelativeDimension_projToSpec`,
`geometricallyConnected_projToSpec`, `exists_projGeomFibreAddEquiv` —
lives in `Fermat/FLT/ModularCurve/EllipticScheme.lean`.

They are in a separate module because the projective Weierstrass model
drags in a mathlib module that reserves the ATOM `over` as a global
token, which would break `IsCompactificationY0.over` here and, through
`MazurTorsion.lean`, several modules downstream.  The import comment at
the top of this file and that module's own docstring give the full
reasoning and the refuting check. -/

/-- **The projective Weierstrass model of `E/ℚ` as an elliptic scheme
over `Spec ℚ`** (ASSEMBLED 2026-07-27 — no longer a single `sorry`; see
the five leaves in `Fermat/FLT/ModularCurve/EllipticScheme.lean`).

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
`T`-points, and that, rather than the geometry, was why no glue-first
skeleton was writable here for as long as the node was a single `sorry`.

**That obstruction is now ROUTED AROUND rather than removed** (2026-07-27).
`Hom(T, Proj 𝒜)` is still not described at this pin — the refuting check
below still returns exactly the eight functoriality declarations — but
`AbelianSchemeStruct.ofMorphisms` accepts the group law as EQUATIONS OF
MORPHISMS, which is writable, and derives the `T`-point presentation from
it.  So the skeleton exists and is the proof below; what remains are the
five leaves in `Fermat/FLT/ModularCurve/EllipticScheme.lean`.

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

The eight-item survey below is kept as the routing record, but items 1,
2, 3 and 4 have since LANDED and are no longer absent — see the preceding
subsection for where each of them now lives.  Items 5, 6, 7 and 8 are the
open ones, and each is now a NAMED leaf rather than a bullet in a
docstring.

ABSENT WHEN WRITTEN, as exact statements to route:

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

STATUS 2026-07-27 — this node has been ASSEMBLED and is no longer a
dispatch target.  The previous version of this paragraph recorded items 1
and 3+4 as in flight and instructed the reader to WAIT; both have landed,
so the instruction is retired.  The node's own proof is now real code and
carries no `sorry` of its own.  **Do not dispatch a prover here.**  The
open work is the five leaves in
`Fermat/FLT/ModularCurve/EllipticScheme.lean`, which are mutually
independent and separately dispatchable:

* `nonempty_projGroupLaw` — items 5+6, the chord–tangent law as
  morphisms plus associativity.  This is the substantial geometric work.
* `smoothOfRelativeDimension_projToSpec` — item 7a, descending the local
  Jacobian criterion along the affine cover of `Proj`.
* `geometricallyConnected_projToSpec` — item 7b.
* `isProper_projToSpec` — properness, which is `Proj.toSpecZero`'s
  properness plus the identification of the degree-zero part with `ℚ`.
* `exists_projGeomFibreAddEquiv` — item 8, the equivariant `≃+`.

Only `exists_projGeomFibreAddEquiv` depends on another of them (it takes
the `ProjGroupLaw` data as an argument); the other four are independent
of each other. -/
theorem exists_ellipticScheme_of_weierstrass (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ (A : Scheme.{0}) (f : A ⟶ SpecQ) (ab : AbelianSchemeStruct f),
      SmoothOfRelativeDimension 1 f ∧
        (letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
         ∃ e : (E⁄(AlgebraicClosure ℚ)).Point ≃+ GeomFibrePt f (𝟙 SpecQ),
           ∀ (σ : Field.absoluteGaloisGroup ℚ) (x : (E⁄(AlgebraicClosure ℚ)).Point),
             e (WeierstrassCurve.Affine.Point.map
                 (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x)
               = ab.galSMul (𝟙 SpecQ) σ (e x)) :=
  exists_ellipticScheme_of_projModel E

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

/-! ### Schematic dominance of the fibre square of the tautological cover

Everything in this subsection is base-free scheme theory; it is the proof
of leaf (iii-a).  The mechanism is mathlib's
`IsSchemeTheoreticallyDominant`, whose stability under **flat** base
change (`IsSchemeTheoreticallyDominant.of_isPullback`) does all the work
once `sqCover` is cut into its two one-sided halves.  Over `Spec ℚ` every
structure morphism is flat (`[Subsingleton Y] [IsIntegral Y] → Flat f`),
so both halves qualify. -/

/-- **The factorisation through the scheme-theoretic image is
schematically dominant** (PROVEN).

Mathlib has `IsDominant f.toImage` and `Hom.toImage_app_injective` for
quasi-compact `f`, but not the ideal-sheaf form; the two are assembled
here by testing `ker` on the affine opens `f.imageι ⁻¹ᵁ U`, which are
affine because `imageι` is a closed immersion and cover `f.image`
because the `U` cover `Y`. -/
theorem ker_toImage_of_quasiCompact {X Y : Scheme.{u}} (r : X ⟶ Y) [QuasiCompact r] :
    r.toImage.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : Y.affineOpens => (⟨r.imageι ⁻¹ᵁ V.1, V.2.preimage r.imageι⟩ : (r.image).affineOpens))
    ?_ ?_
  · refine top_unique fun x _ => ?_
    have hx : r.imageι.base x ∈ (⨆ V : Y.affineOpens, (V : Y.Opens)) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hV⟩
  · intro V
    have hinj : Function.Injective (r.toImage.app (r.imageι ⁻¹ᵁ V.1)).hom :=
      r.toImage_app_injective V
    simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj

instance isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{u}} (r : X ⟶ Y) [QuasiCompact r] :
    IsSchemeTheoreticallyDominant r.toImage :=
  ⟨ker_toImage_of_quasiCompact r⟩

/-- **A morphism out of a scheme with finitely many points is
quasi-compact** (PROVEN): every subset of a finite space is compact.

This is the only place `J` has to be finite on the (iii-a) route; see the
faithfulness note on `ker_sqCover_spanScheme`. -/
theorem quasiCompact_of_finite_carrier {X Y : Scheme.{u}} (r : X ⟶ Y) [Finite ↥X] :
    QuasiCompact r :=
  ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩

/-- **`∐_J Spec ℚ̄` has finitely many points for finite `J`** (PROVEN):
its space is `Σ j : J, Spec ℚ̄` by `AlgebraicGeometry.sigmaMk`, and
`Spec` of a field is a one-point space. -/
instance finite_geomPtSigma {J : Type} [Finite J] : Finite ↥(geomPtSigma J) :=
  Finite.of_equiv _ (AlgebraicGeometry.sigmaMk
    (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ)))).toEquiv

section SqCoverDominant

variable {A C D : Scheme.{0}} {f : A ⟶ SpecQ} {ι : C ⟶ A} {d : D ⟶ A}

/-- **The half-step `D ×_ℚ D ⟶ C ×_ℚ D`** of `sqCover`: `q` on the first
factor, the identity on the second. -/
noncomputable def sqCoverLeft (q : D ⟶ C) (hq : q ≫ ι = d) :
    Limits.pullback (d ≫ f) (d ≫ f) ⟶ Limits.pullback (ι ≫ f) (d ≫ f) :=
  Limits.pullback.map (d ≫ f) (d ≫ f) (ι ≫ f) (d ≫ f) q (𝟙 D) (𝟙 SpecQ)
    (by rw [Category.comp_id, ← Category.assoc, hq]) (by simp)

@[simp] theorem sqCoverLeft_fst (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCoverLeft (f := f) q hq ≫ Limits.pullback.fst (ι ≫ f) (d ≫ f)
      = Limits.pullback.fst (d ≫ f) (d ≫ f) ≫ q :=
  Limits.pullback.lift_fst _ _ _

@[simp] theorem sqCoverLeft_snd (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCoverLeft (f := f) q hq ≫ Limits.pullback.snd (ι ≫ f) (d ≫ f)
      = Limits.pullback.snd (d ≫ f) (d ≫ f) :=
  (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- **The half-step `C ×_ℚ D ⟶ C ×_ℚ C`** of `sqCover`: the identity on
the first factor, `q` on the second. -/
noncomputable def sqCoverRight (q : D ⟶ C) (hq : q ≫ ι = d) :
    Limits.pullback (ι ≫ f) (d ≫ f) ⟶ Limits.pullback (ι ≫ f) (ι ≫ f) :=
  Limits.pullback.map (ι ≫ f) (d ≫ f) (ι ≫ f) (ι ≫ f) (𝟙 C) q (𝟙 SpecQ)
    (by simp) (by rw [Category.comp_id, ← Category.assoc, hq])

@[simp] theorem sqCoverRight_fst (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCoverRight (f := f) q hq ≫ Limits.pullback.fst (ι ≫ f) (ι ≫ f)
      = Limits.pullback.fst (ι ≫ f) (d ≫ f) :=
  (Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[simp] theorem sqCoverRight_snd (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCoverRight (f := f) q hq ≫ Limits.pullback.snd (ι ≫ f) (ι ≫ f)
      = Limits.pullback.snd (ι ≫ f) (d ≫ f) ≫ q :=
  Limits.pullback.lift_snd _ _ _

theorem sqCoverLeft_sqCoverRight (q : D ⟶ C) (hq : q ≫ ι = d) :
    sqCoverLeft (f := f) q hq ≫ sqCoverRight (f := f) q hq = sqCover (f := f) q hq := by
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [Category.assoc, sqCoverRight_fst, sqCoverLeft_fst, sqCover_fst]
  · rw [Category.assoc, sqCoverRight_snd, ← Category.assoc, sqCoverLeft_snd, sqCover_snd]

/-- **`sqCoverLeft` is a base change of `q`** (PROVEN), along the first
projection `C ×_ℚ D ⟶ C`.  This is the pasting lemma `IsPullback.of_bot`
applied to the tautological square of `C ×_ℚ D`. -/
theorem isPullback_sqCoverLeft (q : D ⟶ C) (hq : q ≫ ι = d) :
    IsPullback (Limits.pullback.fst (d ≫ f) (d ≫ f)) (sqCoverLeft (f := f) q hq) q
      (Limits.pullback.fst (ι ≫ f) (d ≫ f)) := by
  refine IsPullback.of_bot (v₂₁ := Limits.pullback.snd (ι ≫ f) (d ≫ f)) (v₂₂ := ι ≫ f)
    ?_ ?_ (IsPullback.of_hasPullback _ _)
  · have h2 : q ≫ (ι ≫ f) = d ≫ f := by rw [← Category.assoc, hq]
    rw [sqCoverLeft_snd, h2]
    exact IsPullback.of_hasPullback _ _
  · rw [sqCoverLeft_fst]

/-- **`sqCoverRight` is a base change of `q`** (PROVEN), along the second
projection `C ×_ℚ C ⟶ C`. -/
theorem isPullback_sqCoverRight (q : D ⟶ C) (hq : q ≫ ι = d) :
    IsPullback (Limits.pullback.snd (ι ≫ f) (d ≫ f)) (sqCoverRight (f := f) q hq) q
      (Limits.pullback.snd (ι ≫ f) (ι ≫ f)) := by
  refine IsPullback.of_bot (v₂₁ := Limits.pullback.fst (ι ≫ f) (ι ≫ f)) (v₂₂ := ι ≫ f)
    ?_ ?_ ((IsPullback.of_hasPullback (ι ≫ f) (ι ≫ f)).flip)
  · have h2 : q ≫ (ι ≫ f) = d ≫ f := by rw [← Category.assoc, hq]
    rw [sqCoverRight_fst, h2]
    exact (IsPullback.of_hasPullback _ _).flip
  · rw [sqCoverRight_snd]

/-- **The fibre square over `ℚ` of a quasi-compact schematically dominant
map is schematically dominant** (PROVEN).

This is leaf (iii-a) in its base-free form.  `sqCover q = sqCoverLeft q ≫
sqCoverRight q`, each factor is a base change of `q` along a projection,
and both projections are flat because they are base changes of structure
morphisms to `Spec ℚ`. -/
theorem ker_sqCover_of_dominant (q : D ⟶ C) (hq : q ≫ ι = d)
    [IsSchemeTheoreticallyDominant q] [QuasiCompact q]
    [AlgebraicGeometry.Flat (ι ≫ f)] [AlgebraicGeometry.Flat (d ≫ f)] :
    (sqCover (f := f) q hq).ker = ⊥ := by
  haveI : IsSchemeTheoreticallyDominant (sqCoverLeft (f := f) q hq) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_sqCoverLeft q hq)
  haveI : IsSchemeTheoreticallyDominant (sqCoverRight (f := f) q hq) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_sqCoverRight q hq)
  rw [← sqCoverLeft_sqCoverRight q hq]
  exact IsSchemeTheoreticallyDominant.ker_eq_bot _

end SqCoverDominant

/-- **The factorisation of `geomPtDesc p` through the span IS
`Hom.toImage`** (PROVEN): `spanSchemeι p` is a closed immersion, hence a
monomorphism, so a factorisation of `geomPtDesc p` through it is
unique. -/
theorem eq_toImage_of_factor_spanScheme {A : Scheme.{0}} {J : Type}
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (q : geomPtSigma J ⟶ spanScheme p) (hq : q ≫ spanSchemeι p = geomPtDesc p) :
    q = (geomPtDesc p).toImage := by
  rw [← cancel_mono (spanSchemeι p), hq]
  exact ((geomPtDesc p).toImage_imageι).symm

/-- **The square of the span's tautological cover is schematically
dominant** (PROVEN 2026-07-27, was sorry leaf (iii-a)).

`Σ = ∐_J Spec ℚ̄ ⟶ C` is schematically dominant by construction — `C`
*is* the scheme-theoretic image — and `⊥` is its kernel
(`ker_toImage_of_quasiCompact` above, assembled from mathlib's
`Hom.toImage_app_injective`).  What is asked here is that the fibre
square of that map over `Spec ℚ` is again schematically dominant.

THE ROUTE ACTUALLY TAKEN is *not* the ring-theoretic one this docstring
used to predict (`R ⊗_ℚ R' ↪ S ⊗_ℚ S'` by flatness over a field, then
transported to ideal sheaves through affine charts).  No chart-level
tensor computation is needed: mathlib already carries
`IsSchemeTheoreticallyDominant` and its stability under **flat base
change**, `IsSchemeTheoreticallyDominant.of_isPullback`.  Cutting
`sqCover` into its two one-sided halves (`sqCoverLeft`, `sqCoverRight`)
exhibits each as a base change of `q` along a projection of a fibre
square over `Spec ℚ`, and over `Spec ℚ` every structure morphism is flat
(mathlib's `[Subsingleton Y] [IsIntegral Y] → Flat f`).  The old
docstring's "check that would refute this obstruction" was the right
instruction and it did refute it: the missing lemma was not about
`Limits.pullback.map` at all but about the morphism *class*.

**A HYPOTHESIS WAS ADDED: `[Finite J]`.**  Say plainly where it is used
and where it is not.  It is used ONLY to obtain `QuasiCompact q` and
`QuasiCompact (geomPtDesc p)` — mathlib's flat-base-change lemma, and
`Hom.toImage_app_injective`, both require quasi-compactness — via
`finite_geomPtSigma` (a finite coproduct of one-point schemes has a
finite space, so every subset is compact).  For infinite `J` the source
is an infinite discrete space and `q` is genuinely NOT quasi-compact, so
this route is unavailable; the statement is nevertheless expected to
remain TRUE there, since the chart-level argument recalled above never
uses finiteness (`Γ` of a coproduct is a product, and
`(∏_j M_j) ⊗_ℚ N ↪ ∏_j (M_j ⊗_ℚ N)` for `N` free).  CHECK THAT WOULD
REFUTE THE NECESSITY OF `[Finite J]`: prove
`(pullback.map … q q (𝟙 _)).ker = ⊥` directly on affine charts, or find
a quasi-compactness-free version of
`IsSchemeTheoreticallyDominant.pullbackSnd`.  Nothing in this
development needs the infinite case: the only consumer,
`exists_addHom_factor_zmulPts`, instantiates `J := Fin N`.

Note this leaf mentions neither `y`, nor `N`, nor the group law: it is a
statement about an arbitrary finite family of geometric points. -/
theorem ker_sqCover_spanScheme {A : Scheme.{0}} {f : A ⟶ SpecQ} {J : Type} [Finite J]
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (q : geomPtSigma J ⟶ spanScheme p) (hq : q ≫ spanSchemeι p = geomPtDesc p) :
    (sqCover (f := f) q hq).ker = ⊥ := by
  haveI hdqc : QuasiCompact (geomPtDesc p) := quasiCompact_of_finite_carrier _
  haveI : QuasiCompact q := quasiCompact_of_finite_carrier _
  haveI : IsSchemeTheoreticallyDominant q := by
    rw [eq_toImage_of_factor_spanScheme p q hq]
    exact ⟨ker_toImage_of_quasiCompact (geomPtDesc p)⟩
  exact ker_sqCover_of_dominant q hq

/-! ### `ℚ̄`-points of the geometric square, and the Galois action

**Added 2026-07-27**, and it is what turns leaf (iii-b) from "the addition
law on `∐ Spec (ℚ̄ ⊗_ℚ ℚ̄)`" into a single statement with no arithmetic in
it.  The two lemmas below say that a `ℚ̄`-point of `∐_J Spec ℚ̄` is nothing
but a member of the family translated by an element of `Γ_ℚ`. -/

/-- **A `ℚ̄`-point of a coproduct of copies of `Spec ℚ̄` factors through one
of the components** (PROVEN).

`Spec ℚ̄` is a ONE-POINT space, so its image meets exactly one summand of
the coproduct, whose underlying space is the disjoint union
(`AlgebraicGeometry.sigmaMk`); `Sigma.ι` is an open immersion (it is the
`j`-th map of `AlgebraicGeometry.sigmaOpenCover`), so
`IsOpenImmersion.lift` produces the factorisation from the containment of
ranges alone. -/
theorem exists_sigmaι_factor_geomPt {J : Type}
    (u : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ geomPtSigma J) :
    ∃ (j : J) (v : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      v ≫ Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j = u := by
  have hsub : Subsingleton (Spec (CommRingCat.of (AlgebraicClosure ℚ))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (AlgebraicClosure ℚ)))
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure ℚ))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (AlgebraicClosure ℚ)))
  obtain ⟨⟨j, x⟩, hjx⟩ := (AlgebraicGeometry.sigmaMk
    (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ)))).surjective (u.base pt)
  haveI : IsOpenImmersion
      (Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j) :=
    (AlgebraicGeometry.sigmaOpenCover
      (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ)))).map_prop j
  refine ⟨j, IsOpenImmersion.lift
    (Limits.Sigma.ι (fun _ : J => Spec (CommRingCat.of (AlgebraicClosure ℚ))) j) u ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  rw [Subsingleton.elim z pt]
  exact ⟨x, by simpa [AlgebraicGeometry.sigmaMk_mk] using hjx⟩

/-- **A ring endomorphism of `F̄` fixing `F` is an element of `Γ_F`**
(PROVEN): `F̄/F` is algebraic, so an `F`-algebra endomorphism is bijective
(`Algebra.IsAlgebraic.algHom_bijective`) and `AlgEquiv.ofBijective` names
the automorphism.

STATED OVER A VARIABLE BASE FIELD ON PURPOSE — this is CLAUDE.md's
`ULift ℚ`/`AlgebraicClosure ℚ` remedy in a fresh spot, and it is
load-bearing rather than stylistic.  At the concrete base `ℚ` the two
`Algebra ℚ (AlgebraicClosure ℚ)` instances (`DivisionRing.toRatAlgebra`
and `AlgebraicClosure.instAlgebra`) form a DIAMOND, elaboration of
`_ →ₐ[ℚ] _` picks the former, and `Algebra.IsAlgebraic ℚ ℚ̄` — an
`instance`, stated for the latter — then fails to synthesise.  With `F` a
variable there is only one instance and the proof is three lines.  Compare
`isIntegralHom_specAlgClos'`, which is stated the same way for the same
reason. -/
theorem exists_absoluteGaloisGroup_ringHom {F : Type} [Field F]
    (φ : AlgebraicClosure F →+* AlgebraicClosure F)
    (hφ : ∀ r : F, φ (algebraMap F (AlgebraicClosure F) r)
      = algebraMap F (AlgebraicClosure F) r) :
    ∃ σ : Field.absoluteGaloisGroup F,
      (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom = φ :=
  ⟨AlgEquiv.ofBijective
    ({ φ with commutes' := hφ } : AlgebraicClosure F →ₐ[F] AlgebraicClosure F)
    (Algebra.IsAlgebraic.algHom_bijective _), rfl⟩

/-- **Every endomorphism of `Spec ℚ̄` is `Spec` of an element of `Γ_ℚ`**
(PROVEN).

`Spec` is fully faithful (`AlgebraicGeometry.Spec.preimage` /
`Spec.map_preimage`), so `v` is `Spec` of a ring endomorphism of `ℚ̄`; that
endomorphism fixes `ℚ` for free, `ℚ` being initial in `CommRing`
(`Subsingleton (ℚ →+* ℚ̄)`, the same fact behind `subsingleton_hom_specQ`);
and `exists_absoluteGaloisGroup_ringHom` upgrades it to an element of
`Γ_ℚ`.  Note there is no continuity condition to check: `Γ_ℚ` here is the
bare automorphism group. -/
theorem exists_specGal_eq (v : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
    Spec (CommRingCat.of (AlgebraicClosure ℚ))) :
    ∃ σ : Field.absoluteGaloisGroup ℚ, specGal σ = v := by
  obtain ⟨σ, hσ⟩ := exists_absoluteGaloisGroup_ringHom (F := ℚ) (Spec.preimage v).hom
    (fun r => congrArg (fun m => m r)
      (Subsingleton.elim ((Spec.preimage v).hom.comp (algebraMap ℚ (AlgebraicClosure ℚ)))
        (algebraMap ℚ (AlgebraicClosure ℚ))))
  refine ⟨σ, ?_⟩
  have hofHom : CommRingCat.ofHom
      ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom.toRingHom)
      = Spec.preimage v := by
    rw [hσ]
    rfl
  rw [specGal, hofHom, Spec.map_preimage]

/-- **The square of the tautological `ℚ̄`-point cover is schematically
dominated by its `ℚ̄`-points** (sorry leaf (iii-b-1), split out
2026-07-27).

`Σ = ∐_J Spec ℚ̄`, so `Σ ×_ℚ Σ = ∐_{j,k} Spec (ℚ̄ ⊗_ℚ ℚ̄)`.  What is asked
is a family of `ℚ̄`-points of that square whose descent
`∐_I Spec ℚ̄ ⟶ Σ ×_ℚ Σ` has trivial kernel ideal sheaf — i.e. a
schematically dominant cover of the square by copies of `Spec ℚ̄`.

**NOTHING ARITHMETIC IS IN THIS LEAF**: no group law, no `y`, no `N`, no
Galois stability, not even an ambient scheme `A`.  It is a statement about
`(∐_J Spec ℚ̄) ×_{Spec ℚ} (∐_J Spec ℚ̄)` alone, and it is the ONLY thing
between the pin and leaf (iii-b).

THE ROUTE, with the pin API located:

* `J` is finite, so `AlgebraicGeometry.sigmaSpec` is an ISO
  (`instance [Finite ι] (R : ι → CommRingCat) : IsIso (sigmaSpec R)`,
  `AlgebraicGeometry/Limits.lean`), giving `Σ ≅ Spec (J → ℚ̄)`.  `s` is
  then `Spec` of the structure map, `Spec ℚ` being terminal
  (`subsingleton_hom_specQ`), so the fibre square is `Spec R` with
  `R = (J → ℚ̄) ⊗_ℚ (J → ℚ̄)` — AFFINE, which is what makes the whole
  question commutative algebra.
* Take `I := (R →ₐ[ℚ̄] ℚ̄)`, equivalently the maximal ideals of `R`, and
  `w` the corresponding `ℚ̄`-points.  Trivial kernel is then exactly
  injectivity of `R → ∏_I ℚ̄`, i.e. `⨅ maximal ideals = 0`.  That holds
  because (a) `R` is REDUCED — `ℚ` is perfect, so `ℚ̄/ℚ` is separable and
  `ℚ̄ ⊗_ℚ ℚ̄` is reduced — and (b) `R` is INTEGRAL over each tensor factor,
  so every prime is maximal with residue field algebraic over `ℚ̄`, hence
  equal to `ℚ̄`.  Reducedness turns `⨅ primes = nilradical` into `0`.
* For (a), `Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean` carries
  `GeometricallyReduced` with `IsStableUnderBaseChange` and the instances
  `[GeometricallyReduced g] → GeometricallyReduced (pullback.fst f g)`.

CHECK THAT WOULD REFUTE THE "just take a FINITE cover" READING — this is
why the leaf quantifies over an arbitrary index type `I` rather than a
finite one, and it is worth stating because the shortcut looks available.
`isSchemeTheoreticallyDominant_iff_isDominant` reduces trivial kernel to
DENSE RANGE over a reduced target, but only for a QUASI-COMPACT morphism,
and `∐_I Spec ℚ̄` is quasi-compact only for finite `I`.  A finite family
cannot work: the points of `Spec (ℚ̄ ⊗_ℚ ℚ̄)` form a profinite space
homeomorphic to `Γ_ℚ`, which is infinite and Hausdorff, so no finite
subset is dense.  So the quasi-compact shortcut is unavailable *by a
proof*, not by an oversight, and the affine/ring route above is the one to
take. -/
theorem exists_geomPts_ker_eq_bot_sigmaSq (J : Type) [Finite J]
    (s : geomPtSigma J ⟶ SpecQ) :
    ∃ (I : Type) (w : I → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        Limits.pullback s s)), (geomPtDesc w).ker = ⊥ :=
  sorry

/-- **Every `ℚ̄`-point of `Σ ×_ℚ Σ` is carried by the group law into the
family `zmulPts`** (PROVEN 2026-07-27) — the arithmetic half of leaf
(iii-b), and the ONLY place `hstable` is consumed on the addition route.

A `ℚ̄`-point `u` of the square is a pair of `ℚ̄`-points of
`Σ = ∐_{Fin N} Spec ℚ̄`; each factors through a component
(`exists_sigmaι_factor_geomPt`) by an endomorphism of `Spec ℚ̄`, which is
`Spec σ` for a `σ ∈ Γ_ℚ` (`exists_specGal_eq`).  So
`u ≫ sqMap d ≫ addHom ab` is `σ₁ · (j • y) + σ₂ · (k • y)`, and since
`galSMul σ` is an ADDITIVE map (`pre_zero`, `pre_add`) this is
`j • (σ₁ · y) + k • (σ₂ · y)`, which lies in `⟨y⟩` by `hstable`.
`exists_fin_zsmul` then names the resulting index in `Fin N`.

Note what is NOT needed: no continuity of `σ ↦ m_σ`, no decomposition of
`ℚ̄ ⊗_ℚ ℚ̄`, and no identification of `Spec (ℚ̄ ⊗_ℚ ℚ̄)` with `Γ_ℚ` — the
statement is *pointwise* in `u`, so each `ℚ̄`-point supplies its own pair
of automorphisms and the profinite structure never enters.  That is the
whole reason the cut of leaf (iii-b) is made here. -/
theorem geomPt_geomSq_addHom_mem {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y)
    (u : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
      Limits.pullback (geomPtDesc (zmulPts ab N y) ≫ f)
        (geomPtDesc (zmulPts ab N y) ≫ f)) :
    ∃ n : Fin N, u ≫ sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab
      = zmulPts ab N y n := by
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  have hd : ∀ m : Fin N, Limits.Sigma.ι
      (fun _ : Fin N => Spec (CommRingCat.of (AlgebraicClosure ℚ))) m
        ≫ geomPtDesc (zmulPts ab N y) = zmulPts ab N y m :=
    fun m => Limits.Sigma.ι_desc _ m
  obtain ⟨j, v₁, hv₁⟩ := exists_sigmaι_factor_geomPt (J := Fin N)
    (u ≫ Limits.pullback.fst (geomPtDesc (zmulPts ab N y) ≫ f)
      (geomPtDesc (zmulPts ab N y) ≫ f))
  obtain ⟨k, v₂, hv₂⟩ := exists_sigmaι_factor_geomPt (J := Fin N)
    (u ≫ Limits.pullback.snd (geomPtDesc (zmulPts ab N y) ≫ f)
      (geomPtDesc (zmulPts ab N y) ≫ f))
  obtain ⟨σ₁, hσ₁⟩ := exists_specGal_eq v₁
  obtain ⟨σ₂, hσ₂⟩ := exists_specGal_eq v₂
  -- the two legs of `u`, computed as Galois translates of members of the family
  have hx : u ≫ Limits.pullback.fst (geomPtDesc (zmulPts ab N y) ≫ f)
        (geomPtDesc (zmulPts ab N y) ≫ f) ≫ geomPtDesc (zmulPts ab N y)
      = (ab.galSMul (𝟙 SpecQ) σ₁ (((j : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))).1 := by
    rw [← Category.assoc, ← hv₁, Category.assoc, hd, ← hσ₁]
    rfl
  have hz : u ≫ Limits.pullback.snd (geomPtDesc (zmulPts ab N y) ≫ f)
        (geomPtDesc (zmulPts ab N y) ≫ f) ≫ geomPtDesc (zmulPts ab N y)
      = (ab.galSMul (𝟙 SpecQ) σ₂ (((k : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))).1 := by
    rw [← Category.assoc, ← hv₂, Category.assoc, hd, ← hσ₂]
    rfl
  -- `u ≫ sqMap d ≫ addHom ab` is the SUM of the two legs (`add_eq_addHom`)
  have hsum : u ≫ sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab
      = ((ab.galSMul (𝟙 SpecQ) σ₁ (((j : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))
          + ab.galSMul (𝟙 SpecQ) σ₂ (((k : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))
          : GeomFibrePt f (𝟙 SpecQ))).1 := by
    rw [show ((ab.galSMul (𝟙 SpecQ) σ₁ (((j : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))
          + ab.galSMul (𝟙 SpecQ) σ₂ (((k : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))
          : GeomFibrePt f (𝟙 SpecQ)))
        = ab.add (ab.galSMul (𝟙 SpecQ) σ₁ (((j : ℕ) • y : GeomFibrePt f (𝟙 SpecQ))))
            (ab.galSMul (𝟙 SpecQ) σ₂ (((k : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))) from rfl,
      add_eq_addHom ab _ _, ← Category.assoc]
    congr 1
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, sqMap_fst, Limits.pullback.lift_fst]
      exact hx
    · rw [Category.assoc, sqMap_snd, Limits.pullback.lift_snd]
      exact hz
  -- the sum is an integer multiple of `y` — THIS is where `hstable` enters
  have hsm : ∀ (σ : Field.absoluteGaloisGroup ℚ) (m : ℕ),
      ab.galSMul (𝟙 SpecQ) σ ((m • y : GeomFibrePt f (𝟙 SpecQ)))
        ∈ AddSubgroup.zmultiples y := by
    intro σ m
    let Ψ : GeomFibrePt f (𝟙 SpecQ) →+ GeomFibrePt f (𝟙 SpecQ) :=
      { toFun := fun w => ab.galSMul (𝟙 SpecQ) σ w
        map_zero' := ab.pre_zero (specGal σ) (specGal_comp_base (𝟙 SpecQ) σ)
        map_add' := fun a b => ab.pre_add (specGal σ) (specGal_comp_base (𝟙 SpecQ) σ) a b }
    have hΨ : ab.galSMul (𝟙 SpecQ) σ ((m • y : GeomFibrePt f (𝟙 SpecQ)))
        = m • ab.galSMul (𝟙 SpecQ) σ y := map_nsmul Ψ m y
    rw [hΨ]
    exact AddSubgroup.nsmul_mem _ (hstable σ) m
  have hmem : (ab.galSMul (𝟙 SpecQ) σ₁ (((j : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))
      + ab.galSMul (𝟙 SpecQ) σ₂ (((k : ℕ) • y : GeomFibrePt f (𝟙 SpecQ)))
      : GeomFibrePt f (𝟙 SpecQ)) ∈ AddSubgroup.zmultiples y :=
    AddSubgroup.add_mem _ (hsm σ₁ j) (hsm σ₂ k)
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  obtain ⟨n, hn⟩ := exists_fin_zsmul hN hy m
  refine ⟨n, ?_⟩
  rw [hsum, ← hm, hn]
  rfl

/-- **The group law carries the square of the geometric-point family into
the span** (formerly sorry leaf (iii-b), split out 2026-07-27 — this is
the half of leaf (iii) that carries the arithmetic).

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
geometric points need not lie in it).

**PROVEN 2026-07-27 over the single leaf `exists_geomPts_ker_eq_bot_sigmaSq`
(iii-b-1), and the two routes predicted for it were both avoided.**  The
task prompt offered `sigmaOpenCover` + `Hom.iInf_ker_openCover_map_comp`,
and reducedness + `PullbackCarrier`; neither is used, and the shared
obligation `QuasiCompact (sqMap d ≫ addHom ab)` never arises.  What
replaces them is the observation that the arithmetic is entirely POINTWISE:

* `geomPt_geomSq_addHom_mem` (PROVEN, axiom-clean) shows that EVERY
  `ℚ̄`-point `u` of `Σ ×_ℚ Σ` satisfies `u ≫ sqMap d ≫ addHom ab = p n`
  for some `n : Fin N`.  Each `ℚ̄`-point carries its own pair of
  automorphisms `σ₁, σ₂ ∈ Γ_ℚ`, so the profinite structure of
  `Spec (ℚ̄ ⊗_ℚ ℚ̄)` — the trap this leaf's docstring and the task prompt
  both warned about — is never touched.  `hstable` is consumed exactly
  here and nowhere else.
* Leaf (iii-b-1) supplies a family of `ℚ̄`-points of `Σ ×_ℚ Σ` whose
  descent has trivial kernel.  The two combine by the SAME ideal-sheaf
  bookkeeping as `exists_addHom_factor_zmulPts`: trivial kernel gives
  `(geomPtDesc w ≫ g).ker = g.ker` through `map_ker`/`map_bot`, and the
  pointwise statement factors `geomPtDesc w ≫ g` through `ι` via a
  reindexing `Sigma.desc` of the cover, so `Hom.le_ker_comp` and
  `IsClosedImmersion.lift` finish.

So the residue of leaf (iii-b) is a statement with NO group law, NO Galois
stability and no abelian scheme in it at all.

## ROUTE AUDIT, 2026-07-27 (by the agent that proved leaf (iii-a))

**SUPERSEDED by the proof above — kept because three of its findings were
checked and remain useful, and because it is a textbook case of an audit
being right about the axis it searched and wrong about the leaf.**  It
declared two routes, both requiring `QuasiCompact (sqMap d ≫ addHom ab)`;
the proof above uses neither and never incurs that obligation.  Its own
"AXIS NOT SEARCHED" note named the Galois-descent isomorphism
`ℚ̄ ⊗_ℚ ℚ̄ ≅ C(Γ_ℚ, ℚ̄)` as the remaining option, and that too was
unnecessary — the missing move was that the arithmetic can be taken
POINTWISE in a `ℚ̄`-point, where no decomposition of `ℚ̄ ⊗_ℚ ℚ̄` is needed
at all.  What survives verbatim and was used: its TRAP paragraph (the
last one below) states exactly the fact the residual leaf (iii-b-1)
isolates.

AXIS SEARCHED: *morphism-class* routes — schematic dominance, flat base
change, rigidity out of a reduced scheme — and *coproduct-decomposition*
routes.  NOT searched: an explicit Galois-descent isomorphism
`ℚ̄ ⊗_ℚ ℚ̄ ≅ C(Γ_ℚ, ℚ̄)`, which is the classical proof and would need
that isomorphism built from scratch.

**Leaf (iii-a) is now PROVEN and it does NOT help here.**  Schematic
dominance is preserved by flat base change, which is what closed (iii-a);
it says nothing about a map that leaves the family, which is what
addition does.  So the two halves of leaf (iii) really are of different
difficulty, exactly as the sibling `exists_negHom_factor_zmulPts`
predicted.

**Rigidity is NOT the tool here either** — the same correction the
inversion sibling recorded, for a different reason: rigidity
(`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`) compares TWO
morphisms that agree on a dense subscheme, and here there is no second
morphism to compare against.  What is wanted is a factorisation, i.e. an
ideal-sheaf inequality.

TARGET INEQUALITY, after `IsClosedImmersion.lift` and
`Scheme.IdealSheafData.ker_subschemeι`: writing `d := geomPtDesc
(zmulPts ab N y)`,

    d.ker ≤ (sqMap d ≫ addHom ab).ker.

Two routes reach it, and BOTH need the same quasi-compactness input.

*Route 1 — cut by the components of the coproduct.*  The pieces exist in
the pin and were located, not guessed:
`AlgebraicGeometry.sigmaOpenCover` (the cover of `∐ g` by the `Sigma.ι`),
`AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight` (the induced
cover of a fibre product, with pieces `pullback (𝒰X.f i ≫ f)
(𝒰Y.f j ≫ g)`), and
`AlgebraicGeometry.Scheme.Hom.iInf_ker_openCover_map_comp`,
`⨅ i, (𝒰.f i ≫ h).ker = h.ker` for `[QuasiCompact h]`.  Together these
reduce the target to: for each `(j, k)`, the composite
`Spec (ℚ̄ ⊗_ℚ ℚ̄) ⟶ A` factors through `spanSchemeι`.

*Route 2 — reduce to a purely TOPOLOGICAL containment.*  Both kernels
are radical because their sources are reduced, so by
`Scheme.Hom.support_ker` and `Scheme.IdealSheafData.vanishingIdeal`
(antitone) the target follows from

    Set.range (sqMap d ≫ addHom ab) ⊆ closure (Set.range d),

and the points of the fibre product are enumerated by
`Mathlib/AlgebraicGeometry/PullbackCarrier.lean`'s `Pullback.Triplet`.
Reducedness of `Σ ×_ℚ Σ` looks INFERRABLE rather than missing: mathlib's
`Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean` carries
`instance [GeometricallyReduced g] [Flat g] [IsReduced X]
[IsLocallyNoetherian X] : IsReduced (pullback f g)`, and `Σ` is a finite
disjoint union of `Spec ℚ̄` — reduced and locally noetherian — over the
separable extension `ℚ̄/ℚ`.  CHECK THAT WOULD REFUTE THIS: try
`example : IsReduced ↑(Limits.pullback (geomPtDesc p ≫ f) (geomPtDesc p ≫ f)) := by
infer_instance` and see whether `GeometricallyReduced (geomPtDesc p ≫ f)`
resolves.

SHARED OBLIGATION, and the first thing the successor should discharge:
`QuasiCompact (sqMap d ≫ addHom ab)`.  It is NOT free — `Spec (ℚ̄ ⊗_ℚ ℚ̄)`
is an infinite (profinite) space, so `quasiCompact_of_finite_carrier`
does not apply — but it should follow from "source quasi-compact, target
quasi-separated": `CompactSpace ↑(Σ ×_ℚ Σ)` is mathlib's
`instance [QuasiCompact f] [CompactSpace Y] : CompactSpace ↑(pullback f g)`
fed by `finite_geomPtSigma`, and `A` is quasi-separated because
`AbelianSchemeStruct` carries the field `proper : IsProper f` (CHECKED in
`Fermat/FLT/Modularity/AbelianScheme.lean`) and `SpecQ` is affine.

TRAP, recorded because it is the natural first guess and it is WRONG:
`Spec (ℚ̄ ⊗_ℚ ℚ̄)` is **not** `∐_{σ ∈ Γ_ℚ} Spec ℚ̄`.  The tensor product
is the ring of *continuous* functions `Γ_ℚ → ℚ̄`, so its spectrum is a
profinite space, not a discrete coproduct, and `σ` varies continuously
over it.  Any plan that writes the fibre square as a coproduct indexed by
`Fin N × Fin N × Γ_ℚ` will not typecheck and, worse, will look like it
should.  What IS true, and is all the arithmetic needs, is that every
residue field of `ℚ̄ ⊗_ℚ ℚ̄` is `ℚ̄` — it is a field algebraic over the
algebraically closed image of the first factor — so each POINT carries a
`ℚ`-embedding `ℚ̄ → ℚ̄`, hence an element of `Field.absoluteGaloisGroup ℚ`
(`IsAlgClosed`/normality upgrades the embedding to an automorphism).
That is the only place `hstable` is consumed. -/
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
        = sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab := by
  obtain ⟨I, w, hw⟩ := exists_geomPts_ker_eq_bot_sigmaSq (Fin N)
    (geomPtDesc (zmulPts ab N y) ≫ f)
  choose nidx hnidx using geomPt_geomSq_addHom_mem ab N hN y hy hstable
  have hd : ∀ m : Fin N, Limits.Sigma.ι
      (fun _ : Fin N => Spec (CommRingCat.of (AlgebraicClosure ℚ))) m
        ≫ geomPtDesc (zmulPts ab N y) = zmulPts ab N y m :=
    fun m => Limits.Sigma.ι_desc _ m
  have hwi : ∀ i : I, Limits.Sigma.ι
      (fun _ : I => Spec (CommRingCat.of (AlgebraicClosure ℚ))) i
        ≫ geomPtDesc w = w i := fun i => Limits.Sigma.ι_desc _ i
  have hstep : (geomPtDesc w ≫ (sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab)).ker
      = (sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab).ker := by
    rw [← Scheme.IdealSheafData.map_ker, hw, Scheme.IdealSheafData.map_bot]
  have hfac : geomPtDesc w ≫ (sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab)
      = (Limits.Sigma.desc (fun i => Limits.Sigma.ι
            (fun _ : Fin N => Spec (CommRingCat.of (AlgebraicClosure ℚ))) (nidx (w i)))
          ≫ (geomPtDesc (zmulPts ab N y)).toImage) ≫ spanSchemeι (zmulPts ab N y) := by
    rw [Category.assoc,
      show (geomPtDesc (zmulPts ab N y)).toImage ≫ spanSchemeι (zmulPts ab N y)
        = geomPtDesc (zmulPts ab N y) from (geomPtDesc (zmulPts ab N y)).toImage_imageι]
    refine Limits.Sigma.hom_ext _ _ (fun i => ?_)
    have hL : Limits.Sigma.ι (fun _ : I => Spec (CommRingCat.of (AlgebraicClosure ℚ))) i ≫
        (geomPtDesc w ≫ (sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab))
        = zmulPts ab N y (nidx (w i)) := by
      rw [← Category.assoc, hwi]
      exact hnidx (w i)
    have hR : Limits.Sigma.ι (fun _ : I => Spec (CommRingCat.of (AlgebraicClosure ℚ))) i ≫
        (Limits.Sigma.desc (fun i' => Limits.Sigma.ι
            (fun _ : Fin N => Spec (CommRingCat.of (AlgebraicClosure ℚ))) (nidx (w i')))
          ≫ geomPtDesc (zmulPts ab N y))
        = zmulPts ab N y (nidx (w i)) := by
      rw [← Category.assoc, Limits.Sigma.ι_desc]
      exact hd _
    rw [hL, hR]
  have hle : (spanSchemeι (zmulPts ab N y)).ker
      ≤ (sqMap (geomPtDesc (zmulPts ab N y)) ≫ addHom ab).ker := by
    rw [← hstep, hfac]
    exact Scheme.Hom.le_ker_comp _ _
  exact ⟨IsClosedImmersion.lift _ _ hle, IsClosedImmersion.lift_fac _ _ _⟩

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

/-- **A ring map into an algebraically closed field extends along an
algebraic closure** (PROVEN).

STATED OVER A VARIABLE BASE FIELD, for the reason recorded at
`isIntegralHom_specAlgClos`: at the literal `ℚ` the `Rat`-algebra diamond
beats `AlgebraicClosure.instAlgebra` and
`Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` fails to synthesise. -/
theorem exists_ringHom_algebraicClosure {F : Type} [Field F] {K : Type} [Field K]
    [IsAlgClosed K] (ψ : F →+* K) : Nonempty (AlgebraicClosure F →+* K) := by
  letI : Algebra F K := ψ.toAlgebra
  exact ⟨(IsAlgClosed.lift (R := F) (S := AlgebraicClosure F) (M := K)).toRingHom⟩

/-- **`Spec` of a ring map between FIELDS is an epimorphism of schemes**
(PROVEN).

This is the lemma whose absence the audit of `exists_injective_pre_geomBase`
recorded, and the audit searched for the wrong hypothesis: `Spec.map φ` is
NOT an epimorphism for a general injective `φ` (take `ℤ ↪ ℚ`, whose `Spec`
is a monomorphism onto a non-closed point), and it IS one whenever `φ` is
faithfully flat and quasi-compact.  A map of fields is both for free — `K`
is a nonzero `F`-vector space, hence free, hence flat, and both spectra are
single points, so surjectivity is `Subsingleton.elim`.  Then
`AlgebraicGeometry.Flat.epi_of_flat_of_surjective` (stacks 02VW) finishes.

CHECK THAT WOULD REFUTE THIS BEING AVAILABLE: `Flat.SpecMap_iff`,
`AlgebraicGeometry.Surjective` and `Flat.epi_of_flat_of_surjective` must all
resolve at this pin — they do, and this declaration is the demonstration. -/
theorem epi_specMap_of_fieldHom {F : Type} [Field F] {K : Type} [Field K]
    (φ : F →+* K) : Epi (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    rw [AlgebraicGeometry.Flat.SpecMap_iff]
    show RingHom.Flat φ
    letI : Algebra F K := φ.toAlgebra
    exact (inferInstance : Module.Flat F K)
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    constructor
    haveI : Subsingleton (Spec (CommRingCat.of F)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Nonempty (PrimeSpectrum K))
    intro _
    exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩
  exact Flat.epi_of_flat_of_surjective _

/-- **A `ℚ`-scheme structure on `Spec K` is a ring map `ℚ → K`** (PROVEN):
`ΓSpecIso` on both sides of `t.appTop`.

This is what supplies characteristic zero: `K` carries no `CharZero`
instance a priori, and it is `t` that forces one. -/
theorem nonempty_ringHom_of_hom_specQ {K : Type} [Field K]
    (t : Spec (CommRingCat.of K) ⟶ SpecQ) : Nonempty (ℚ →+* K) :=
  ⟨((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ t.appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom⟩

/-- **A geometric base point over an arbitrary algebraically closed base,
inducing an injection on relative points** (leaf (v-a), split out
2026-07-27; **PROVEN 2026-07-27**).

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

HOW IT CLOSED, and both halves came in cheaper than predicted.

* **The identification `he` is FREE.**  It is an equality of two morphisms
  `Spec K ⟶ Spec ℚ`, and `subsingleton_hom_specQ` (already in this file,
  for the atlas) says there is at most one.  So `e` needs no compatibility
  construction at all — nothing has to be checked about the embedding
  beyond its existence, and the "read the `ℚ`-algebra structure off `t`"
  trap below applies only to *producing* `e`, not to `he`.
* **The injectivity half was recorded as needing a lemma that does not
  exist, and the audit searched on the wrong hypothesis.**  It asked for
  `Epi (Spec.map φ)` for `φ` INJECTIVE — which is false in general
  (`ℤ ↪ ℚ`) and is why the grep found nothing.  The true hypothesis is
  FAITHFUL FLATNESS, which a map of fields satisfies for free; see
  `epi_specMap_of_fieldHom` above.  `cancel_epi` then does the whole job,
  and neither the one-point-scheme argument nor the affine-open
  factorisation sketched below is used anywhere.

The recorded traps were real and are still worth reading: the embedding
lemma `exists_ringHom_algebraicClosure` IS stated over a variable base
field, and the `ℚ`-algebra structure on `K` IS read off `t`, by
`nonempty_ringHom_of_hom_specQ`. -/
theorem exists_injective_pre_geomBase {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ SpecQ) :
    ∃ (e : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (he : e ≫ (specAlgClos ℚ ≫ 𝟙 SpecQ) = t),
      Function.Injective (fun x : GeomFibrePt f (𝟙 SpecQ) => RelPoint.pre e he x) := by
  haveI := subsingleton_hom_specQ (Spec (CommRingCat.of K))
  obtain ⟨ψ⟩ := nonempty_ringHom_of_hom_specQ t
  obtain ⟨φ⟩ := exists_ringHom_algebraicClosure (F := ℚ) ψ
  haveI : Epi (Spec.map (CommRingCat.ofHom φ)) := epi_specMap_of_fieldHom φ
  refine ⟨Spec.map (CommRingCat.ofHom φ), Subsingleton.elim _ _, ?_⟩
  intro a b hab
  exact Subtype.ext ((cancel_epi (Spec.map (CommRingCat.ofHom φ))).mp
    (congrArg Subtype.val hab))

/-- **An element integral over an algebraically closed subfield lies in
it** (PROVEN) — the POINTWISE form of
`IsAlgClosed.algebraMap_bijective_of_isIntegral`.

Mathlib's version asks for `Algebra.IsIntegral k K`, i.e. that ALL of `K`
be integral over `k`, and that is exactly what fails in the application
below: `K` is an arbitrary algebraically closed field containing `ℚ̄`, and
`K = ℂ` is not integral over `ℚ̄`.  Only the individual values of a ring
map out of a finite `ℚ`-algebra are.  The proof is mathlib's, restricted
to one element: over an algebraically closed field an irreducible
polynomial is linear, so `minpoly k a = X + C c` and `a = -c`. -/
theorem exists_algebraMap_eq_of_isIntegral {k K : Type} [Field k] [Field K]
    [IsAlgClosed k] [Algebra k K] {a : K} (ha : IsIntegral k a) :
    ∃ c : k, algebraMap k K c = a := by
  refine ⟨-(minpoly k a).coeff 0, ?_⟩
  have hq : (minpoly k a).leadingCoeff = 1 := minpoly.monic ha
  have h : (minpoly k a).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible ha)
  have h0 : Polynomial.aeval a (minpoly k a) = 0 := minpoly.aeval k a
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul, map_add,
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at h0
  rw [map_neg]
  exact h0.symm

/-- **A ring map out of an integral `ℚ`-algebra into an algebraically
closed field factors through any copy of `ℚ̄` inside it** (PROVEN).  This
is the ring core of leaf (v-b-i).

NOTE WHAT IS NOT HYPOTHESISED: no compatibility between `χ`, `φ` and `ψ`
over `ℚ`.  None is needed, and this is the step that makes the leaf
cheap.  `χ ∘ ψ` and `φ ∘ (algebraMap ℚ ℚ̄)` are both ring maps `ℚ → K`,
and `Rat.subsingleton_ringHom` says there is at most one — so they are
equal on the nose.  Hence the monic `ℚ`-polynomial killing `r` maps to a
monic `ℚ̄`-polynomial killing `χ r`, and
`exists_algebraMap_eq_of_isIntegral` puts `χ r` in the image of `φ`.
Injectivity of `φ` (a map of fields) then makes the pointwise preimage a
ring map. -/
theorem exists_ringHom_factor_of_isIntegral {R : Type} [CommRing R]
    (ψ : ℚ →+* R) (hint : ψ.IsIntegral)
    {K : Type} [Field K] [IsAlgClosed K]
    (φ : AlgebraicClosure ℚ →+* K) (χ : R →+* K) :
    ∃ ρ : R →+* AlgebraicClosure ℚ, φ.comp ρ = χ := by
  letI : Algebra (AlgebraicClosure ℚ) K := φ.toAlgebra
  have hmap : (algebraMap (AlgebraicClosure ℚ) K) = φ := rfl
  have hmem : ∀ r : R, ∃ c : AlgebraicClosure ℚ, φ c = χ r := by
    intro r
    obtain ⟨q, hqm, hq⟩ := hint r
    have hsub : χ.comp ψ = φ.comp (algebraMap ℚ (AlgebraicClosure ℚ)) :=
      Subsingleton.elim _ _
    have hint2 : IsIntegral (AlgebraicClosure ℚ) (χ r) := by
      refine ⟨q.map (algebraMap ℚ (AlgebraicClosure ℚ)), hqm.map _, ?_⟩
      rw [hmap, Polynomial.eval₂_map, ← hsub, ← Polynomial.hom_eval₂, hq, map_zero]
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isIntegral hint2
    exact ⟨c, by rw [← hmap]; exact hc⟩
  choose g hg using hmem
  have hinj : Function.Injective φ := φ.injective
  refine ⟨{ toFun := g
            map_one' := hinj (by rw [hg, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [hg, map_mul, map_mul, hg, hg])
            map_zero' := hinj (by rw [hg, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [hg, map_add, map_add, hg, hg]) }, ?_⟩
  ext r
  exact hg r

/-- **A finite `ℚ`-scheme acquires no new points over a larger
algebraically closed field** (leaf (v-b-i), split out and **PROVEN**
2026-07-27).

Every `K`-point of the span factors through the given embedding
`e : Spec K ⟶ Spec ℚ̄`, for `K` any algebraically closed field.

NOTE WHAT IS *NOT* ASSUMED.  `e` is arbitrary: no compatibility over `ℚ`
is hypothesised, because none is needed — every morphism
`Spec K ⟶ Spec ℚ̄` is `Spec` of a ring map `ℚ̄ → K`, which is injective
(source a field) and `ℚ`-linear automatically.  And the family `p` is
arbitrary: neither the group law nor Galois stability appears, exactly as
in leaf (i).

THE ROUTE, which needs no product decomposition of `Γ(C)`.  `C` is
AFFINE (`isAffine_spanScheme`) and FINITE over `ℚ`
(`isFinite_spanSchemeι`), so `R := Γ(C, ⊤)` is a finite — hence integral
— `ℚ`-algebra.  A `K`-point of `C` is a ring map `χ : R → K`
(`Scheme.isoSpec` plus `ΓSpec.adjunction.homEquiv`).  Give `K` its
`ℚ̄`-algebra structure through `e`; then every `χ r` is integral over `ℚ`,
hence over `ℚ̄`, so `Algebra.adjoin ℚ̄ (Set.range χ)` is an integral domain
integral over the algebraically closed `ℚ̄` and
`IsAlgClosed.algebraMap_surjective_of_isIntegral` puts every `χ r` in the
image of `ℚ̄`.  That image map is the required `ρ : R → ℚ̄`, and
`v := Spec.map ρ` transported back along `isoSpec`.

HOW IT CLOSED, correcting the route above in one place.  The `Algebra.adjoin`
detour is unnecessary: mathlib's
`IsAlgClosed.algebraMap_bijective_of_isIntegral` demands `Algebra.IsIntegral ℚ̄ K`
— FALSE here, since `K` may be `ℂ` — but its proof is pointwise, and
`exists_algebraMap_eq_of_isIntegral` above is exactly that proof restricted
to one element.  With it, `exists_ringHom_factor_of_isIntegral` is the whole
mathematical content, and the scheme half is six rewrites: `Spec.map_surjective`
turns `w`, `e` and the structure morphism into ring maps, `IsIntegralHom.SpecMap_iff`
turns `IsFinite` into `RingHom.IsIntegral`, and `Spec.map_comp` reassembles.

Note `IsFinite` — not merely finiteness of the SPACE — is what is used: a
`ℚ`-algebra with a one-point spectrum need not be algebraic over `ℚ` (take
`ℚ(x)`), so `isAffine_spanScheme` alone would not do.  `isFinite_spanSchemeι`
is leaf (i), and this leaf therefore consumes it. -/
theorem exists_geomPt_factor_span {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) {J : Type} [Finite J]
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (hp : ∀ j, p j ≫ f = specAlgClos ℚ ≫ 𝟙 SpecQ)
    (K : Type) [Field K] [IsAlgClosed K]
    (e : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (w : Spec (CommRingCat.of K) ⟶ spanScheme p) :
    ∃ v : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ spanScheme p, e ≫ v = w := by
  haveI := isAffine_spanScheme ab p hp
  haveI := isFinite_spanSchemeι ab p hp
  haveI : IsFinite ((spanScheme p).isoSpec.inv ≫ spanSchemeι p ≫ f) := inferInstance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((spanScheme p).isoSpec.inv ≫ spanSchemeι p ≫ f)
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (w ≫ (spanScheme p).isoSpec.hom)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective e
  have hint : ψ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hψ]
    infer_instance
  obtain ⟨ρ, hρ⟩ := exists_ringHom_factor_of_isIntegral ψ.hom hint φ.hom χ.hom
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ (spanScheme p).isoSpec.inv, ?_⟩
  have hcomp : CommRingCat.ofHom ρ ≫ φ = χ := CommRingCat.hom_ext hρ
  rw [← hφ, ← Category.assoc, ← Spec.map_comp, hcomp, hχ, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **Every `ℚ̄`-point of the span is a Galois translate of a member of the
family** (sorry leaf (v-b-ii), split out 2026-07-27 — the arithmetic half
of the crux).

Again the family is arbitrary: this is the statement that the
scheme-theoretic image of finitely many geometric points has no geometric
points beyond the `Γ_ℚ`-orbits of those it was built from.  Galois
stability of the family is NOT assumed and is not needed; it is the
PARENT that consumes stability, to turn the orbit back into `⟨y⟩`.

THE ROUTE.  Write `R := Γ(C, ⊤)` and `χ_j : R → ℚ̄` for the `J` coordinate
maps induced by the family.  Four steps, none of which needs the group
law:

* `R ↪ ∏_J ℚ̄`, i.e. `⋂_j ker χ_j = 0` — this is schematic dominance of
  `toImage`, the defining property of the scheme-theoretic image, and it
  is the ONLY place the construction of `C` enters;
* `R` is a finite `ℚ`-algebra (`isFinite_spanSchemeι`), hence artinian,
  so every prime of `R` is MAXIMAL;
* for `χ : R → ℚ̄`, `ker χ` is prime and contains `⋂_j ker χ_j = 0 ⊇
  ∏_j ker χ_j`, so `ker χ ⊇ ker χ_j` for some `j` by primality of a
  finite product, and maximality of both forces `ker χ = ker χ_j`;
* `χ` and `χ_j` are then two `ℚ`-embeddings of the residue field
  `κ := R ⧸ ker χ_j` into `ℚ̄`, so they differ by an automorphism:
  view `ℚ̄` as a `κ`-algebra through `χ_j`, lift `χ` with
  `IsAlgClosed.lift` to a `ℚ`-algebra endomorphism of `ℚ̄`, and make it an
  `AlgEquiv` — an element of `Field.absoluteGaloisGroup ℚ` — with
  `Algebra.IsAlgebraic.algHom_bijective`.

`Spec` is contravariant, so `χ = σ ∘ χ_j` becomes
`v = specGal σ ≫ q_j` and hence `v ≫ ι = specGal σ ≫ p j`, which is the
conclusion.

**PIN SURVEY, 2026-07-27 — EVERY INGREDIENT RESOLVES; NO THEORY IS
MISSING.**  Each of the four steps was looked up by name against a seeded
`.lake`, and two of them came back cheaper than the sketch above, so the
sketch is corrected here rather than left to mislead:

1. Schematic dominance is **already a lemma**, and it is not the
   `SchemeTheoreticallyDominant` property this docstring first reached
   for: it is `AlgebraicGeometry.Scheme.Hom.toImage_app_injective`
   (`Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean`), which says
   every `app` of `f.toImage` is injective, under `[QuasiCompact f]`.
   And `QuasiCompact (geomPtDesc p)` is ALREADY DERIVED in this file, in
   the proof of `range_spanSchemeι_subset` — `geomPtDesc p ≫ f` is a
   morphism of affines, and `QuasiCompact.of_comp` cancels `f`.  So step
   one costs a citation, not a development.
2. **Artinian theory is NOT needed** — the sketch above overshot.  `R` is
   a finite, hence integral, `ℚ`-algebra, so `R ⧸ ker χ_j` is a DOMAIN
   integral over the field `ℚ`, and `Algebra.IsIntegral.isField_iff_isField`
   / `isField_of_isIntegral_of_isField'`
   (`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`)
   make it a field directly.  So `ker χ_j` is maximal with no reference
   to `IsArtinianRing` and no `Ring.KrullDimLE` at all.
3. "A prime containing a finite intersection contains a factor" is
   `Ideal.IsPrime.inf_le'` (or `IsPrime.prod_le`),
   `Mathlib/RingTheory/Ideal/Operations.lean`.
4. `Algebra.IsAlgebraic.algHom_bijective`
   (`Mathlib/RingTheory/Algebraic/Basic.lean`) plus `AlgEquiv.ofBijective`
   gives the automorphism.  `IsAlgClosure.equiv` in
   `Mathlib/FieldTheory/IsAlgClosed/Basic.lean` is a two-line worked
   example of exactly this assembly and is the thing to copy.

CHECK THAT WOULD REFUTE THIS SURVEY: any one of those five names failing
to resolve, or `Hom.toImage_app_injective` turning out to be stated only
for opens of the form `f.imageι ⁻¹ᵁ U` in a way that does not cover `⊤`
(it is stated for exactly those opens, and `f.imageι ⁻¹ᵁ ⊤ = ⊤`).

What remains is therefore PLUMBING, not mathematics: transporting `v`,
the `q_j` and the structure morphism across `(spanScheme p).isoSpec` into
ring maps, as `exists_geomPt_factor_span` already does, and identifying
`Γ(∐_J Spec ℚ̄, ⊤)` with `∏_J ℚ̄` so that the `χ_j` are literally the
coordinates.  That last identification is the one step with no lemma
found by name and is where a successor should expect the work to be. -/
theorem exists_specGal_factor_span {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) {J : Type} [Finite J]
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (hp : ∀ j, p j ≫ f = specAlgClos ℚ ≫ 𝟙 SpecQ)
    (v : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ spanScheme p) :
    ∃ (σ : Field.absoluteGaloisGroup ℚ) (j : J),
      v ≫ spanSchemeι p = specGal σ ≫ p j :=
  sorry

/-- **Every `K`-point of the span is an integer multiple of the geometric
generator** (leaf (v-b), split out 2026-07-27 — THE CRUX of leaf (v), and
the only half of it that carries arithmetic; **DECOMPOSED and its assembly
PROVEN 2026-07-27** over `exists_geomPt_factor_span` and
`exists_specGal_factor_span`).

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
finite bookkeeping.

**DECOMPOSED 2026-07-27 into the two leaves `exists_geomPt_factor_span`
and `exists_specGal_factor_span` below.**  The split is along the two
independent halves of the argument above, and NEITHER half mentions the
group law, `hstable`, `hy` or `hN` — they are statements about an
arbitrary finite family of geometric points, exactly like leaf (i).  The
full `R ≅ ∏ κ_i` splitting is NOT needed for either: the first half needs
only that `R` is a finite `ℚ`-algebra, the second only that the primes of
an artinian ring are maximal.

**AUDIT: `hN` AND `hy` ARE NOT USED, and are underscored to say so.**
That is not an oversight and it is not vacuity — the conclusion is a
statement about `zmulPts ab N y`, every member of which is a multiple of
`y` by construction, so no order information is needed to see that a
Galois translate of a member is again a multiple of `y`.  `hN` and `hy`
remain in the signature because the PARENT `geom_cyclic_zmulPts` needs
them for its other two conjuncts, and removing them here would cost a
call-site edit for no gain.  (At `N = 0` the family is empty and the
hypothesis `hx` is what carries the weight; the statement stays true.) -/
theorem mem_zmultiples_of_liesIn_span {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (N : ℕ) (_hN : N ≠ 0) (y : GeomFibrePt f (𝟙 SpecQ))
    (_hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hstable : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          ∀ σ : Field.absoluteGaloisGroup ℚ,
            ab.galSMul (𝟙 SpecQ) σ y ∈ AddSubgroup.zmultiples y)
    (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ SpecQ)
    (e : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (he : e ≫ (specAlgClos ℚ ≫ 𝟙 SpecQ) = t)
    (x : RelPoint f t) (hx : RelPoint.LiesIn (spanSchemeι (zmulPts ab N y)) x) :
    letI := ab.addCommGroup t
    x ∈ AddSubgroup.zmultiples (RelPoint.pre e he y) := by
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  letI := ab.addCommGroup t
  -- `RelPoint.pre e he` is additive: that is the naturality of the group law.
  let Φ : GeomFibrePt f (𝟙 SpecQ) →+ RelPoint f t :=
    { toFun := fun x => RelPoint.pre e he x
      map_zero' := ab.pre_zero e he
      map_add' := fun a b => ab.pre_add e he a b }
  -- descend the `K`-point of the span to a `ℚ̄`-point, then to the family
  obtain ⟨w, hw⟩ := hx
  obtain ⟨v, hv⟩ := exists_geomPt_factor_span ab (zmulPts ab N y)
    (zmulPts_comp ab N y) K e w
  obtain ⟨σ, j, hσ⟩ := exists_specGal_factor_span ab (zmulPts ab N y)
    (zmulPts_comp ab N y) v
  set z : GeomFibrePt f (𝟙 SpecQ) := ((j : ℕ) • y) with hz
  have hxeq : x = Φ (ab.galSMul (𝟙 SpecQ) σ z) := by
    apply Subtype.ext
    show x.1 = e ≫ (specGal σ ≫ z.1)
    rw [← hw, ← hv, Category.assoc, hσ]
    rfl
  -- the Galois action is by additive maps, so it commutes with `j • -`
  let Ψ : GeomFibrePt f (𝟙 SpecQ) →+ GeomFibrePt f (𝟙 SpecQ) :=
    { toFun := ab.galSMul (𝟙 SpecQ) σ
      map_zero' := ab.pre_zero (specGal σ) (specGal_comp_base (𝟙 SpecQ) σ)
      map_add' := fun a b => ab.pre_add (specGal σ) (specGal_comp_base (𝟙 SpecQ) σ) a b }
  obtain ⟨k, hk⟩ := hstable σ
  have hgal : ab.galSMul (𝟙 SpecQ) σ z = ((j : ℕ) : ℤ) • (k • y) := by
    show Ψ z = _
    rw [hz, map_nsmul Ψ]
    show ((j : ℕ)) • (ab.galSMul (𝟙 SpecQ) σ y) = _
    rw [← hk, natCast_zsmul]
  refine ⟨((j : ℕ) : ℤ) * k, ?_⟩
  rw [hxeq, hgal, smul_smul, map_zsmul Φ]
  rfl

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

Only the `→` direction — `C(K) ⊆ ⟨z⟩` — is left; it is leaf (v-b),
`mem_zmultiples_of_liesIn_span`, which since 2026-07-27 is itself proven
over the two leaves `exists_geomPt_factor_span` and
`exists_specGal_factor_span`.  Leaf (v-a) is PROVEN.

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
| (i) `isFinite_spanSchemeι` | **PROVEN** 2026-07-27 — no leaf |
| (ii) `ratPoint_liesIn_spanScheme` | **PROVEN** 2026-07-27 — no leaf |
| (iii) `exists_addHom_factor_zmulPts` | PROVEN over (iii-a), (iii-b) |
| (iv) `exists_negHom_factor_zmulPts` | **PROVEN** — no leaf |
| (v) `geom_cyclic_zmulPts` | PROVEN over (v-a), (v-b) |
| (iii-a) `ker_sqCover_spanScheme` | **PROVEN** 2026-07-27 — flat base change of `IsSchemeTheoreticallyDominant`; needed one added hypothesis `[Finite J]` |
| (iii-b) `exists_addHom_factor_geomSq` | **PROVEN** 2026-07-27 over (iii-b-1); the arithmetic moved to `geomPt_geomSq_addHom_mem`, which is the only consumer of `hstable` |
| (iii-b-1) `exists_geomPts_ker_eq_bot_sigmaSq` | open — `(∐_J Spec ℚ̄) ×_ℚ (∐_J Spec ℚ̄)` is schematically dominated by its `ℚ̄`-points; NO group law, NO Galois stability, no abelian scheme |
| (v-a) `exists_injective_pre_geomBase` | **PROVEN** — no leaf; `he` is `subsingleton_hom_specQ`, injectivity is `epi_specMap_of_fieldHom` |
| (v-b) `mem_zmultiples_of_liesIn_span` | PROVEN over (v-b-i), (v-b-ii) |
| (v-b-i) `exists_geomPt_factor_span` | **PROVEN** — no leaf; consumes leaf (i) `isFinite_spanSchemeι` |
| (v-b-ii) `exists_specGal_factor_span` | open — the `ℚ̄`-points of the span are the `Γ_ℚ`-orbits of the family; the arithmetic crux |

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

/-! #### The torsion subscheme `C[n]`, and why it IS formable here

**This section retires the "IRREDUCIBLE at this mathlib pin" verdict that
`exists_torsionSubscheme` carried until 2026-07-27.**  That verdict said
the functor-of-points presentation "carries the group law on `RelPoint`
rather than as a morphism `E ×_T E ⟶ E`, so `[M] : C ⟶ C` is not
available as a morphism of schemes and the fibre product cannot be
formed".  Both halves are wrong, and the refuting check is one `grep`:

* `Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean` already carries
  `AbelianSchemeStruct.mulByNat n : E ⟶ E` — the morphism `[n]` — with
  `nsmul_val : (n • x).1 = x.1 ≫ mulByNat n`, and
  `AbelianSchemeStruct.zeroSection : T ⟶ E` with
  `zero_val : (ab.zero g).1 = g ≫ zeroSection`.  All PROVEN.
* No morphism `E ×_T E ⟶ E` is needed to get them.  `mulByNat` is
  obtained by Yoneda at the TAUTOLOGICAL relative point `RelPoint.self f`
  — a single point of a single test object — and naturality (`pre_nsmul`)
  then makes `n • x` a composite with it at every base at once.  The
  fibre-product-free route is the whole design of that module.

Two stale notes elsewhere in this file are corrected by the same check
and should be read with this section: the audit at
`exists_ellipticScheme_of_weierstrass` records `AbelianSchemeIsogeny.lean`
as "not on `main` at all" and as containing only CONSUMERS of an
`AbelianSchemeStruct`.  It is on `main`, and `mulByNat` / `zeroSection` /
`nsmul_val` / `zero_val` are producers of exactly the interface this node
needed.  (The claim that the file supplies no *construction* of an
`AbelianSchemeStruct` remains true; that is a different claim.)

With those in hand the torsion subscheme is the plain fibre product

    C[n] := C ×_{ι ≫ [n], E, e} T ,

`torsionι n : C[n] ⟶ C ⟶ E` its inclusion.  The zero section `e` is a
closed immersion because it is a section of the SEPARATED (indeed proper)
morphism `f`; closed immersions are stable under base change and compose,
so `torsionι n` is a closed immersion and `torsionι n ≫ f` is finite.
Everything in this section is PROVEN except `flat_torsionι`, which is
FALSE as stated — see its FALSITY AUDIT. -/

/-- **The zero section of an abelian scheme is a closed immersion**
(PROVEN).  It is a section of `f`, and `f` is proper hence separated, so
`IsClosedImmersion.of_comp` applies to `e ≫ f = 𝟙 T`. -/
theorem AbelianSchemeStruct.isClosedImmersion_zeroSection {A S : Scheme.{u}} {f : A ⟶ S}
    (ab : AbelianSchemeStruct f) : IsClosedImmersion ab.zeroSection := by
  haveI := ab.proper
  haveI : IsSeparated f := inferInstance
  haveI : IsClosedImmersion (ab.zeroSection ≫ f) := by
    rw [ab.zeroSection_comp]; infer_instance
  exact IsClosedImmersion.of_comp _ f

/-- **The `n`-torsion subscheme `C[n]` of a cyclic subgroup scheme**: the
fibre product of `ι ≫ [n] : C ⟶ E` with the zero section `T ⟶ E`.  By
`nsmul_val` and `zero_val` its relative points are exactly the relative
points of `C` killed by `n` (`liesIn_torsionι_iff`). -/
@[reducible] noncomputable def CyclicSubgroupOfOrder.torsionScheme {E T : Scheme.{u}}
    {f : E ⟶ T} {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N)
    (n : ℕ) : Scheme.{u} :=
  Limits.pullback (c.ι ≫ ab.mulByNat n) ab.zeroSection

/-- **The inclusion `C[n] ⟶ E`.** -/
noncomputable def CyclicSubgroupOfOrder.torsionι {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ) :
    c.torsionScheme n ⟶ E :=
  Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection ≫ c.ι

/-- **`C[n] ⟶ E` is a closed immersion** (PROVEN): the first projection is
the base change of the zero section, which is a closed immersion, and
closed immersions compose with `ι`. -/
theorem CyclicSubgroupOfOrder.isClosedImmersion_torsionι {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ) :
    IsClosedImmersion (c.torsionι n) := by
  haveI := ab.isClosedImmersion_zeroSection
  haveI := c.isClosedImmersion
  show IsClosedImmersion
    (Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection ≫ c.ι)
  infer_instance

/-- **`C[n] ⟶ T` is finite** (PROVEN): a closed immersion is finite, and
`C ⟶ T` is finite by hypothesis. -/
theorem CyclicSubgroupOfOrder.isFinite_torsionι {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ) :
    IsFinite (c.torsionι n ≫ f) := by
  haveI := ab.isClosedImmersion_zeroSection
  haveI := c.isFinite
  show IsFinite
    ((Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection ≫ c.ι) ≫ f)
  rw [Category.assoc]
  infer_instance

/-- **The relative points of `C[n]` are exactly those of `C` killed by
`n`** (PROVEN), at every base at once.

This is the whole functor-of-points content of the node, and it is where
`nsmul_val` and `zero_val` are used: `n • x = 0` unwinds to
`x.1 ≫ [n] = g ≫ e`, which is precisely the datum a map into the fibre
product `C[n]` is built from. -/
theorem CyclicSubgroupOfOrder.liesIn_torsionι_iff {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ)
    {T' : Scheme.{u}} {g : T' ⟶ T} (x : RelPoint f g) :
    letI := ab.addCommGroup g
    RelPoint.LiesIn (c.torsionι n) x ↔ (RelPoint.LiesIn c.ι x ∧ n • x = 0) := by
  letI := ab.addCommGroup g
  have hval : (n • x).1 = x.1 ≫ ab.mulByNat n := ab.nsmul_val n x
  have hzg : (ab.zero g).1 = g ≫ ab.zeroSection := ab.zero_val g
  constructor
  · rintro ⟨w, hw⟩
    have hy : (w ≫ Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection) ≫ c.ι = x.1 := by
      rw [Category.assoc]; exact hw
    have hkey : (n • x).1
        = (w ≫ Limits.pullback.snd (c.ι ≫ ab.mulByNat n) ab.zeroSection) ≫ ab.zeroSection := by
      rw [hval, ← hy]
      simp only [Category.assoc]
      rw [Limits.pullback.condition]
    have hsnd : w ≫ Limits.pullback.snd (c.ι ≫ ab.mulByNat n) ab.zeroSection = g := by
      have h1 := congrArg (fun m => m ≫ f) hkey
      simp only [Category.assoc, ab.zeroSection_comp, Category.comp_id] at h1
      rw [← h1]
      exact (n • x).2
    refine ⟨⟨_, hy⟩, ?_⟩
    show n • x = ab.zero g
    apply Subtype.ext
    rw [hkey, hsnd, hzg]
  · rintro ⟨⟨y, hy⟩, hz⟩
    have heq : y ≫ (c.ι ≫ ab.mulByNat n) = g ≫ ab.zeroSection := by
      rw [← Category.assoc, hy, ← hval]
      show (n • x).1 = _
      rw [show (n • x) = ab.zero g from hz, hzg]
    refine ⟨Limits.pullback.lift y g heq, ?_⟩
    show (Limits.pullback.lift y g heq
      ≫ Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection) ≫ c.ι = x.1
    rw [Limits.pullback.lift_fst, hy]

/-- **`C[n]` is flat over the base** (sorry leaf).

**FALSITY AUDIT (2026-07-27, with an explicit counterexample). THIS
STATEMENT IS FALSE AS STATED.  Do not dispatch a prover at it; it needs a
CUT-LEVEL repair, described at the end.**

The counterexample lives in characteristic `p`, where `geom_cyclic` — a
condition on the SET of geometric points — does not pin the RANK of `C`,
so `C` may carry an arbitrary infinitesimal part invisible to it.

> Let `k = 𝔽̄_p` (`p ≥ 5`), `R = k[[t]]`, `T = Spec R`.
> * `E₁ / R` = a constant ORDINARY elliptic curve, and `P ∈ E₁[p](k)` a
>   point of order `p`; so `(ℤ/p)_T ⊆ E₁` is a constant étale subgroup
>   scheme.
> * `E₂ / R` = a Legendre family specialised so that the generic fibre is
>   ORDINARY and the closed fibre is SUPERSINGULAR (the supersingular
>   locus of the `λ`-line is a nonempty finite set, so such an `R`-curve
>   exists).
> * `A = E₁ ×_R E₂`, an abelian scheme over `T` of relative dimension 2;
>   `C = (ℤ/p)_T × ker F²_{E₂} ⊆ A`, where `F` is relative Frobenius.
>
> `C ⟶ T` is finite and FLAT of rank `p·p² = p³` (a product of two finite
> flat group schemes), `C ⟶ A` is a closed immersion, and `C` is a
> subgroup functor, so `zero_liesIn` / `add_liesIn` / `neg_liesIn` hold.
> Its geometric fibres are `ℤ/p × {0} ≅ ℤ/p` at BOTH points, because
> `ker F²` is infinitesimal and so has a single geometric point in every
> fibre.  Hence `c : CyclicSubgroupOfOrder ab p` with `N = p`.
>
> Now take `n = p` (note `p ∣ N` and `N ≠ 0`, so no hypothesis available
> at `ofDvd` excludes this either).  `C[p] = (ℤ/p) × ker([p] on ker F²)`,
> and `ker F²` is `μ_{p²}` at the ordinary generic fibre but is `E₂[p]` at
> the supersingular closed fibre.  So
> `ker([p] on ker F²)` is `μ_p` (rank `p`) generically and `E₂[p]`
> (rank `p²`) specially: the rank of `C[p] ⟶ T` JUMPS from `p²` to `p³`.
> A finite module over the DVR `R` of jumping rank is not flat, so
> `C[p] ⟶ T` is NOT flat.

The refutation transfers to `exists_torsionSubscheme` itself, not merely
to this particular `C[n]`: the last conjunct there determines the
subfunctor of `h_E` represented by `ι'` completely, and `ι'` is a
monomorphism, so by Yoneda any `C'` satisfying it is canonically
isomorphic over `E` to `torsionScheme M` (apply the ↔ to the two
tautological points and use that `ι'` and `torsionι M` are monos to see
the two factorisations are mutually inverse — a fifteen-line argument, not
formalised here).  Flatness is invariant under isomorphism, so no other
choice of `C'` can rescue the conjunct.

WHERE THE DEFECT REALLY IS.  `CyclicSubgroupOfOrder.geom_cyclic` pins the
CARDINALITY of the geometric fibres; Katz–Mazur **(6.7.1)** pin the RANK
of the finite locally free group scheme (and cyclicity as a divisor
condition).  The two agree exactly when `C ⟶ T` is étale — which the
field's own docstring notes is automatic over a `ℚ`-scheme, where `N` is
invertible and Cartier's theorem applies, and which is the only case this
development ever evaluates.  Over a general base they come apart, and
this leaf is where they come apart.

THE REPAIR IS AT CUT LEVEL, and it is a choice between:

1. restrict the base: add a hypothesis making `T` a `ℚ`-scheme (or, more
   sharply, `[IsEtale (c.ι ≫ f)]`) to `exists_torsionSubscheme`,
   `CyclicSubgroupOfOrder.ofTorsion`, `ofDvd` and `Gamma0Datum.ofDvd`.
   With `C ⟶ T` étale the leaf becomes TRUE and provable: the diagonal of
   an unramified morphism is an open immersion, so `C[n]`, being the
   equaliser of two `T`-morphisms `C ⇉ C`, is open as well as closed in
   `C`, hence étale over `T`, hence flat;
2. strengthen `CyclicSubgroupOfOrder` itself, replacing or supplementing
   `geom_cyclic` with the Katz–Mazur rank condition.

Route 1 is far cheaper and matches every actual use (the twelve level
nodes all work over `ℚ`); route 2 changes an interface several owners
build on.  Either way it is not a repair to be made inside this leaf. -/
theorem CyclicSubgroupOfOrder.flat_torsionι {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ) :
    AlgebraicGeometry.Flat (c.torsionι n ≫ f) :=
  sorry

/-- **The `M`-torsion of a cyclic subgroup scheme is again cut out by a
closed subscheme, finite over the base** (PROVEN 2026-07-27 over the one
remaining leaf `CyclicSubgroupOfOrder.flat_torsionι`).

`C[M]` is `CyclicSubgroupOfOrder.torsionScheme M`, the fibre product of
`ι ≫ [M] : C ⟶ E` with the zero section `T ⟶ E`; see the section
docstring above for why `[M]` IS available as a morphism (it is
`AbelianSchemeStruct.mulByNat`, and no group law `E ×_T E ⟶ E` is needed
to build it).  Three of the four conjuncts are discharged here:

* `IsClosedImmersion` — `isClosedImmersion_torsionι`;
* `IsFinite` — `isFinite_torsionι`;
* the relative-point characterisation — `liesIn_torsionι_iff`, which is
  `nsmul_val` and `zero_val` read at the fibre square.

This holds for EVERY `M`, with no divisibility hypothesis and no
constraint relating `M` to `N`: for `M = 0` the condition `0 • x = 0` is
vacuous and `C` itself works, and in general `C[M] = C[gcd (M, N)]`.
Keeping the leaf free of hypotheses it does not need is deliberate — the
arithmetic that `M ∣ N` buys is entirely group-theoretic and is
discharged in `CyclicSubgroupOfOrder.ofTorsion` below, so this node
carries only the geometry.

**FLATNESS IS PART OF THIS LEAF** (added at integration, 2026-07-26).
`CyclicSubgroupOfOrder` acquired a `flat` field — that field is what makes
the structure Katz–Mazur's finite *locally free* `[Γ₀(N)]` rather than a
strictly larger moduli problem; see the field's own docstring for the
`Spec ℚ[ε]` counterexample.  It is threaded through `ofTorsion`'s `hflat`
argument to `ofDvd`.

**AND FLATNESS IS WHERE THIS STATEMENT IS FALSE.**  The earlier claim in
this docstring — "`C[M]` is a torsion subscheme of an already-flat `C`, so
whatever construction discharges this leaf produces flatness along with
finiteness, and no separate argument is needed" — is WRONG: a closed
subscheme of a flat scheme is not flat, and in characteristic `p` the rank
of `C[M]` genuinely jumps.  The counterexample, and the two candidate
cut-level repairs, are in the FALSITY AUDIT of
`CyclicSubgroupOfOrder.flat_torsionι`.  Read that before working here. -/
theorem exists_torsionSubscheme {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (M : ℕ) :
    ∃ (C' : Scheme.{u}) (ι' : C' ⟶ E), IsClosedImmersion ι' ∧ IsFinite (ι' ≫ f) ∧
      AlgebraicGeometry.Flat (ι' ≫ f) ∧
      ∀ (T' : Scheme.{u}) (g : T' ⟶ T) (x : RelPoint f g),
        letI := ab.addCommGroup g
        RelPoint.LiesIn ι' x ↔ (RelPoint.LiesIn c.ι x ∧ M • x = 0) :=
  ⟨c.torsionScheme M, c.torsionι M, c.isClosedImmersion_torsionι M, c.isFinite_torsionι M,
    c.flat_torsionι M, fun _ _ x => c.liesIn_torsionι_iff M x⟩

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
  /-- the inclusion is a morphism over `ℚ`.

  **The name is written `«over»`, and it must stay escaped** (2026-07-27).
  This module imports `Fermat.FLT.ModularCurve.EllipticScheme`, whose cone
  reaches `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean` and
  through it `Mathlib/Tactic/Ring/NamePolyVars.lean`, which declares the
  command syntax `name_poly_vars … " over " …`.  Lean's TOKEN TABLE IS GLOBAL —
  an atom reserved by any imported module is a keyword in this file whether or
  not the notation is ever opened — so the bare identifier `over` stops parsing
  here, with the maximally confusing error
  `unexpected token 'over'; expected 'lemma'` reported at the FIELD DECLARATION
  rather than at the import.

  Escaping preserves the declaration name exactly: this is still
  `Fermat.IsCompactificationY0.over`, so docstrings, other branches and other
  modules that refer to it by name are unaffected.  Only the surface syntax
  changes.  Use sites in this file are therefore written `hX.«over»`.

  That the import is NON-public is what stops this spreading: `MazurTorsion.lean`
  and its dependent cone (`ModThree.lean` among them, which uses mathlib's
  `Ideal.LiesOver.over`) do not inherit the token.  Do not make it public.

  The refuting check, if you think this can be reverted: after removing the
  `EllipticScheme` import,
  `grep -rln "Tactic.Ring.NamePolyVars" .lake/packages/mathlib/Mathlib/`
  must no longer name any module in this file's import cone. -/
  «over» : j ≫ strX = strY
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
  exact hall ⟨y.1 ≫ hX.j, by rw [Category.assoc, hX.«over», y.2]⟩ ⟨y.1, rfl⟩

/-- **The degenerate level `N = 0` has an EMPTY coarse space** (PROVEN).

`isEmpty_of_gamma0Datum_zero` says the `Γ₀(0)`-problem has no object over
a nonempty base, so every base carrying a datum is initial and the empty
scheme carries a natural transformation out of the problem.  Initiality
of `Y` then produces a morphism `Y ⟶ ∅`, which is only possible when `Y`
is itself empty.

This is what makes the compactification statement uniform in `N`: at
`N = 0` there is nothing to compactify, and `X = Y = ∅` discharges every
clause vacuously rather than by a separate citation. -/
theorem isEmpty_of_isCoarseModuliY0_zero {Y : Scheme.{0}} {strY : Y ⟶ SpecQ}
    (hc : IsCoarseModuliY0 0 strY) : IsEmpty Y := by
  classical
  have hinit : ∀ {T : Scheme.{0}}, Gamma0Datum 0 T → Limits.IsInitial T := by
    intro T d
    have : IsEmpty T := isEmpty_of_gamma0Datum_zero d
    exact isInitialOfIsEmpty
  obtain ⟨u, -, -⟩ :=
    hc.universal (Y' := (∅ : Scheme.{0})) (emptyIsInitial.to SpecQ)
      (fun {_T} _g d => ⟨(hinit d).to _, (hinit d).hom_ext _ _⟩)
      (by intro _ _ _ _ _ _ d' _ _; exact Subtype.ext ((hinit d').hom_ext _ _))
  exact Function.isEmpty u.base

/-- **`Y_0(N)` is a geometrically connected smooth curve over `ℚ`, for
`N ≥ 1`** (sorry leaf — the MODULAR half of the compactification).

TRUE and classical: for `N ≥ 1` the coarse moduli space of the
`Γ₀(N)`-problem over `ℚ` is a smooth affine geometrically connected curve.
Smoothness is normality of the coarse space of a smooth Deligne–Mumford
stack of dimension one together with "normal curve = smooth curve"
(Deligne–Rapoport III.1; Katz–Mazur 8.2, and 8.2.1 for the
`ℤ[1/N]`-smoothness that specialises to this); geometric connectedness is
the irreducibility of `Γ_0(N)\ℍ` together with the fact that the moduli
problem is defined over `ℚ` (Deligne–Rapoport IV.5.5, or Shimura 6.6).

**This is the ONLY modular input to `X_0(N)`'s existence.**  Everything
else — that a smooth curve over a field has a smooth proper
compactification with finite complement — is
`AlgebraicGeometry.exists_isSmoothCompactification`, which is general
algebraic geometry and lives in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`.
Separating the two is the point of this leaf: a successor can attack the
modular half without touching curve theory, and vice versa.

`hN : 0 < N` is REQUIRED and the statement is FALSE without it.  At
`N = 0` the coarse space is EMPTY (`isEmpty_of_isCoarseModuliY0_zero`),
and both `IsIntegral` and `GeometricallyConnected` carry nonemptiness —
`IsIntegral` through `IrreducibleSpace`, `GeometricallyConnected` through
`ConnectedSpace`.  So the conclusion is unsatisfiable at the degenerate
level, which is handled separately and vacuously below.

The four conclusions are exactly the hypotheses of
`exists_isSmoothCompactification`, and none is decoration:
`QuasiCompact` and `IsSeparated` are what Nagata's compactification
consumes, `IsIntegral` is what makes the relative normalization integral,
and `SmoothOfRelativeDimension 1` is what pins the relative dimension of
the compactification to `1` rather than leaving it arbitrary.

IRREDUCIBLE at this pin: the coarse space is available here only through
`IsCoarseModuliY0`, i.e. through its universal property, and no property
of a scheme beyond that universal property can be extracted without the
Deligne–Rapoport/Katz–Mazur construction, which does not exist at this
pin in any form. -/
theorem isSmoothCurve_of_isCoarseModuliY0 {N : ℕ} (_hN : 0 < N) {Y : Scheme.{0}}
    {strY : Y ⟶ SpecQ} (_hc : IsCoarseModuliY0 N strY) :
    IsIntegral Y ∧ QuasiCompact strY ∧ IsSeparated strY ∧
      SmoothOfRelativeDimension 1 strY ∧ GeometricallyConnected strY :=
  sorry

/-- **Existence of the smooth compactification `X_0(N)`** (PROVEN, over
one modular leaf plus general curve theory; formerly a sorry node).

The two halves the previous version of this docstring named as
"independent" are now genuinely separated, and only the first is still
modular:

* `isSmoothCurve_of_isCoarseModuliY0` — `Y_0(N)` is a geometrically
  connected smooth curve over `ℚ` for `N ≥ 1` (Deligne–Rapoport III.1,
  Katz–Mazur 8.2).  Still a leaf.
* `AlgebraicGeometry.exists_isSmoothCompactification` — every smooth
  curve over a perfect field embeds as a dense open subscheme of a smooth
  proper curve with finite complement.  Now a THEOREM, proved in
  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean` from
  Nagata compactification plus the relative normalization, over four
  named leaves of its own, none of which mentions modular curves.

For `N = 0` the moduli problem is supported on the empty base (a scheme
finite over its base cannot have infinite cyclic geometric fibres), so
`Y_0(0)` is the empty scheme by `isEmpty_of_isCoarseModuliY0_zero`, and
`X = Y` with `j = 𝟙` satisfies every condition vacuously — properness
because a morphism out of an empty scheme is a closed immersion, hence
finite, hence proper, and smoothness because
`SmoothOfRelativeDimension` quantifies over the points of the source.
The statement is therefore uniform in `N` without a citation covering the
degenerate level. -/
theorem exists_compactificationY0 {N : ℕ} {Y : Scheme.{0}} {strY : Y ⟶ SpecQ}
    (hc : IsCoarseModuliY0 N strY) :
    ∃ (X : Scheme.{0}) (strX : X ⟶ SpecQ), Nonempty (IsCompactificationY0 strY strX) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- Degenerate level: `Y = ∅`, and `X = Y` compactifies it vacuously.
    haveI : IsEmpty Y := isEmpty_of_isCoarseModuliY0_zero hc
    haveI : SmoothOfRelativeDimension 1 strY := ⟨fun x => isEmptyElim x⟩
    exact ⟨Y, strY, ⟨{ j := 𝟙 Y
                       over := Category.id_comp strY
                       isOpenImmersion := inferInstance
                       isDominant := inferInstance
                       proper := inferInstance
                       smooth := SmoothOfRelativeDimension.smooth (n := 1) (f := strY) }⟩⟩
  · obtain ⟨hint, hqc, hsep, hsmd, -⟩ := isSmoothCurve_of_isCoarseModuliY0 hN hc
    haveI := hint; haveI := hqc; haveI := hsep; haveI := hsmd
    obtain ⟨X, strX, j, hX⟩ := exists_isSmoothCompactification (K := ℚ) strY
    haveI := hX.smooth
    exact ⟨X, strX, ⟨{ j := j
                       over := hX.comm
                       isOpenImmersion := hX.isOpenImmersion
                       isDominant := hX.isDominant
                       proper := hX.isProper
                       smooth := SmoothOfRelativeDimension.smooth (n := 1) (f := strX) }⟩⟩

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

/-- **`Y_0(N)(ℚ) = ∅` implies every rational point of `X_0(N)` is a cusp**
(PROVEN) — the exact converse of `y0HasNoRationalPoint_of_cuspidal`, and
the direction in which the level nodes below are consumed.

The proof is the definition unwound: a rational point of `X` that is NOT
a cusp factors as `y ≫ hX.j` for some `y : Spec ℚ ⟶ Y`, and
`IsCompactificationY0.over` turns `x.2` into `y ≫ strY = 𝟙`, so `y` is a
rational point of the coarse space, which `Y0HasNoRationalPoint N`
forbids.

**Why this is not circular with `y0HasNoRationalPoint_of_cuspidal`.**
The two together say `X_0(N)(ℚ)` cuspidal ⟺ `Y_0(N)(ℚ) = ∅`, which is
the content of "the cusps are exactly `X ∖ Y`" and carries no arithmetic
at all.  What it buys is that a level node may be discharged by whichever
of the two shapes its argument naturally produces: Mazur's and Kenku's
theorems are proven on `X_0(N)`, while the divisibility glue
(`y0HasNoRationalPoint_of_dvd`) and the reduction counts live on
`Y_0(N)`.  Before this lemma only the `X → Y` direction existed, so a
level node stated on `X` could not consume the divisibility glue — which
is precisely what `cuspidal_x0_isogenyPrimeSq` below needs.

Placed here rather than beside `y0HasNoRationalPoint_of_cuspidal` only to
keep this edit inside one region of a heavily contended file; it belongs
next to its converse and may be moved there freely. -/
theorem cuspidal_of_y0HasNoRationalPoint {N : ℕ} {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ}
    {strX : X ⟶ SpecQ} (hc : IsCoarseModuliY0 N strY)
    (hX : IsCompactificationY0 strY strX) (hY : Y0HasNoRationalPoint N)
    (x : RelPoint strX (𝟙 SpecQ)) : hX.IsCusp x := by
  rintro ⟨y, hy⟩
  refine (hY Y strY hc).false ⟨y, ?_⟩
  rw [← hX.over, ← Category.assoc, hy]
  exact x.2

/-- **The eight prime-square levels that Kenku's determination must treat
one at a time**: `p²` for the eight primes `p ≥ 11` that admit a rational
`p`-isogeny, i.e. for `p ∈ mazurIsogenyPrimes` with `11 ≤ p`, namely
`p ∈ {11, 13, 17, 19, 37, 43, 67, 163}`.

This is the prime-square analogue of `kenkuLevels`, and it exists for the
same reason: the machinery that can actually close a level node here
(`hasRankZeroJacobian_of_kenkuLevel` plus `card_le_of_rankZeroJacobian`,
or the Mordell–Weil sieve of `y0HasNoRationalPoint_of_sieveLevel`) is
LEVEL-INDEXED, so it can only be pointed at an explicit finite list of
levels.  Every prime `p ≥ 11` OUTSIDE `mazurIsogenyPrimes` is handled
uniformly by Mazur instead — see `cuspidal_x0_isogenyPrimeSq`. -/
def isogenyPrimeSqLevels : List ℕ := [121, 169, 289, 361, 1369, 1849, 4489, 26569]

/-- **The arithmetic behind the case split in `cuspidal_x0_isogenyPrimeSq`**
(PROVEN): a prime `p ≥ 11` admitting a rational `p`-isogeny has `p² ` in
`isogenyPrimeSqLevels`.

Pure `Finset`/`List` computation: `mazurIsogenyPrimes` has twelve
elements, `11 ≤ p` removes the four small ones, and the remaining eight
squares are the eight entries of `isogenyPrimeSqLevels` by evaluation. -/
theorem mem_isogenyPrimeSqLevels_of_mem_mazurIsogenyPrimes {p : ℕ}
    (hmem : p ∈ mazurIsogenyPrimes) (hp11 : 11 ≤ p) :
    p ^ 2 ∈ isogenyPrimeSqLevels := by
  fin_cases hmem <;> first | omega | decide

/-- **The seven prime-square levels that reduce to a FINITE set of
`p`-isogeny classes**: `p²` for `p ∈ {11, 17, 19, 37, 43, 67, 163}`, i.e.
every entry of `isogenyPrimeSqLevels` except `169`.

**Why these seven are one node and `169` is another** — this is the
substantive content of the cut, and it corrects the route analysis that
`y0HasNoRationalPoint_of_isogenyPrimeSqLevel` carried before.

*The uniform reduction.*  A rational point of `Y_0(p²)` is a pair
`(E, C)` with `C` cyclic of order `p²`.  Put `E' = E/C[p]`.  Then `E'[p]`
contains TWO DISTINCT Galois-stable lines: the image `C/C[p]` of `C`, and
the image `E[p]/C[p]` of `E[p]` — which is the kernel of the dual
isogeny.  They are distinct because a generator of `C` has order `p²` and
so does not lie in `E[p]`.  Conversely two independent stable lines
`L₁ ≠ L₂` in `E'[p]` give a cyclic `p²`-subgroup of `E'/L₁`.  So, for
each prime `p`, the level node is EQUIVALENT to

> no elliptic curve over `ℚ` admits two independent rational
> `p`-isogenies.

This is the same circle of ideas as
`WeierstrassCurve.not_two_stable_lines_of_jInvariant` and
`not_cyclicIsogeny_sq_of_jInvariant` in `FreyCurve/MazurTorsion.lean`,
whose Vélu construction is exactly the passage `(E, C) ↦ E/C[p]` above.
**That module imports this one**, so the implication may not be used
here; the ARGUMENT may be copied, the declarations may not.

*What the reduction then needs.*  `E'` carries a rational `p`-isogeny, so
its point on `Y_0(p)(ℚ)` lies in a set one can enumerate — PROVIDED that
set is finite.  That is the whole of the split, and it is decided by a
single computable number.  Genus of `X_0(p)`, PARI/GP 2.17.4, 2026-07-27:

| `p`             | `11` | `13`  | `17` | `19` | `37` | `43` | `67` | `163` |
|-----------------|------|-------|------|------|------|------|------|-------|
| `genus X_0(p)`  | `1`  | **`0`** | `1`  | `1`  | `2`  | `3`  | `5`  | `13`  |

* `p = 11, 17, 19`: `X_0(p)` is an elliptic curve of ANALYTIC rank `0`
  (verified 2026-07-27 with PARI/GP on the models `[0,-1,1,-10,-20]`,
  `[1,-1,1,-1,-14]`, `[0,1,1,-9,-15]`, of conductors `11, 17, 19`), so
  Kolyvagin–Gross–Zagier gives Mordell–Weil rank `0` and `X_0(p)(ℚ)` is
  finite: `3`, `2`, `1` non-cuspidal points respectively.
* `p = 37, 43, 67, 163`: `genus X_0(p) ≥ 2`, so `X_0(p)(ℚ)` is finite by
  Faltings; the non-cuspidal points are `2, 1, 1, 1` respectively.  The
  three singletons are CM by the class-number-one order `ℚ(√-p)`, in
  which `p` RAMIFIES — so `E[p]` has a unique stable line and two
  independent `p`-isogenies are impossible on the nose, with no
  enumeration at all.  `p = 37` has two explicit non-CM `j`-invariants,
  `-7·11³` and `-7·137³·2083³`.
* `p = 13` is the exception: `genus X_0(13) = 0`, so `X_0(13) ≅ ℙ¹_ℚ`,
  `Y_0(13)(ℚ)` is INFINITE — a one-parameter family of curves with a
  rational `13`-isogeny — and the reduction above degenerates into a
  tautology.  Level `169` is therefore the only one of the eight that
  must be settled on its own curve; it is `y0HasNoRationalPoint_oneSixtyNine`.

**Correction to the previous reconnaissance** (recorded 2026-07-27 in the
docstring of `y0HasNoRationalPoint_of_isogenyPrimeSqLevel`, and to the
dispatch that quoted it).  That analysis grouped `121, 169, 289, 361` as
"genuine rational-point determinations on curves of genus `6, 8, 17, 22`"
and pointed all four at Chabauty–Coleman, keeping the isogeny-character
route for `1369, 1849, 4489, 26569` alone.  Three of those four do not
need the geometry of `X_0(N)` at all: `121, 289, 361` reduce to the
finite sets `Y_0(11)(ℚ)`, `Y_0(17)(ℚ)`, `Y_0(19)(ℚ)` by exactly the
argument that handles the four large levels, and the genus-`17` and
genus-`22` curves never appear.  Splitting `4 + 4` therefore separates
levels that share a route and joins levels that do not.  **The check that
refutes this correction**, if it is wrong: exhibit a prime among
`11, 17, 19` for which `X_0(p)(ℚ)` is infinite — equivalently for which
`genus X_0(p) = 0`, or `genus = 1` with positive rank.  The table above
is that check, and it is one `gp` line per entry. -/
def isogenyClassPrimeSqLevels : List ℕ := [121, 289, 361, 1369, 1849, 4489, 26569]

/-- **Kenku's prime-square determination at the seven levels with a
finite isogeny classification** (sorry node, introduced 2026-07-27):
`Y_0(N)(ℚ) = ∅` for `N = p²`, `p ∈ {11, 17, 19, 37, 43, 67, 163}`.

TRUE: none of `121, 289, 361, 1369, 1849, 4489, 26569` lies in the
Mazur–Kenku list `1, …, 19, 21, 25, 27, 37, 43, 67, 163` of levels with a
non-cuspidal rational point — every one of them exceeds `163`.

See `isogenyClassPrimeSqLevels` for the route: the two-independent-lines
reduction, and the finiteness of `Y_0(p)(ℚ)` that makes it terminate.
The seven fall into two sub-families, and a successor may split this node
again along them if it prefers — they share the reduction and differ only
in how the finite set is obtained and checked:

* `121, 289, 361` (`p = 11, 17, 19`): `X_0(p)` elliptic of rank `0`,
  `Y_0(p)(ℚ)` explicitly `3, 2, 1` points, checked by enumeration.  For
  `p = 11` the check is visible in the isogeny graph: the three
  `j`-invariants `-32768`, `-121`, `-24729001` sit in conductor-`121`
  classes that are single `11`-isogeny EDGES, so no vertex has degree
  `2` and no chain of two `11`-isogenies exists.
* `1369, 1849, 4489, 26569` (`p = 37, 43, 67, 163`): `genus X_0(p) ≥ 2`,
  finiteness by Faltings, and at `43, 67, 163` the CM argument needs no
  enumeration.

**The one obligation the reduction does not discharge, and it is
shared by both sub-families.**  `Y0HasNoRationalPoint` is a statement
about the COARSE moduli space, and `IsCoarseModuliY0` deliberately omits
bijectivity on geometric points (see its docstring).  So a rational point
of `Y_0(p²)` does not come with a pair `(E, C)` defined over `ℚ`: what it
carries is a `ℚ̄`-pair whose field of moduli is `ℚ`, and descending it to
`ℚ` is Weil descent against `Aut(E, C)`.  This is exactly the gap the
module docstring names when it says the modular-curve statement is
STRONGER than the elliptic-curve one — and it is why
`nonempty_gamma0Datum_of_stable` (curve ⟶ point) exists here while its
converse does not.  A successor must build that bridge, or else run the
whole argument on `X_0(p²)` itself.  **Do not state the bridge as a
universally quantified leaf without the descent hypothesis**: for a pair
with extra automorphisms it is false as a bare implication, which is the
standard `j = 0, 1728` caveat.

IRREDUCIBLE at this pin: it needs the classification of `Y_0(p)(ℚ)` for
the seven primes (Mazur's Theorem 1 in its sharp, point-listing form —
`cuspidal_x0_prime` above is only the emptiness half, which says nothing
at these seven), the Vélu quotient at the modular-curve level, and the
field-of-moduli descent above.

Sources: Mazur, *Rational isogenies of prime degree*, Invent. Math. **44**
(1978), Theorem 1 and Table 1; Kenku, *The modular curves `X_0(65)` and
`X_0(91)` and rational isogeny*, Math. Proc. Cambridge Philos. Soc. **87**
(1980); *On the modular curves `X_0(125)`, `X_1(25)` and `X_1(49)`*,
J. London Math. Soc. (2) **23** (1981). -/
theorem y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel (N : ℕ)
    (_hN : N ∈ isogenyClassPrimeSqLevels) : Y0HasNoRationalPoint N :=
  sorry

/-- **Kenku's determination at level `169`** (sorry node, introduced
2026-07-27): `Y_0(169)(ℚ) = ∅`.

TRUE: `169 > 163`, so it is outside the Mazur–Kenku list.

**Why this is a node of its own**, and not a member of
`isogenyClassPrimeSqLevels`: `genus X_0(13) = 0`.  Every other prime
`p` with `p² ∈ isogenyPrimeSqLevels` has `genus X_0(p) ≥ 1`, hence
`Y_0(p)(ℚ)` finite, hence a finite list of `p`-isogeny classes to check;
at `p = 13` the curve `X_0(13)` is `ℙ¹_ℚ`, `Y_0(13)(ℚ)` is infinite, and
that route does not exist even in principle.  `169` must be settled on
`X_0(169)`, of genus `8`.  This is Kenku, *The modular curve `X_0(169)`
and rational isogeny*, J. London Math. Soc. (2) **22** (1980).

#### Reconnaissance (PARI/GP 2.17.4, 2026-07-27, and its consequence)

`genus X_0(169) = 8`; `dim S_2(Γ_0(169))^new = 8` with newform factors
`(deg 𝕋_f, ord_{s=1} L(f,s)) = (2,0), (3,0), (3,3)`, and the old part
`J_0(13)² = 0`; so the analytic rank of `J_0(169)` is `3`.

`3 < 8`, which is Chabauty's hypothesis — but note two things before
reaching for it.

* **`rank J_0(169)(ℚ) < 8` is not available unconditionally.**  The two
  analytic-rank-`0` factors have Mordell–Weil rank `0` by
  Kolyvagin–Logachev; the analytic-rank-`3` factor is a `3`-dimensional
  modular abelian variety, and Gross–Zagier/Kolyvagin say nothing at
  analytic rank `3`.  Chabauty's input at `169` is thus conditional on
  BSD unless a descent supplies the upper bound directly.  (At `121`,
  `289`, `361` the corresponding vanishing sits on a `deg 𝕋_f = 1`
  factor, so positivity of the rank IS unconditional there — but by the
  correction recorded at `isogenyClassPrimeSqLevels` those three do not
  need a rank input at all.)
* **The CRUDE Chabauty–Coleman bounds cannot close this level, whatever
  the prime.**  What has to be proven is
  `#X_0(169)(ℚ) = numRationalCusps 169 = 2` (the divisors of `p²` are
  `1, p, p²`, and `φ(gcd(p, p)) = p − 1 ≠ 1` for odd `p`, so only the
  cusps `0` and `∞` are rational).  Coleman's bound, for `ℓ > 2g` of good
  reduction and `r < g`, is `#X(ℚ) ≤ #X(𝔽_ℓ) + 2g − 2 = #X(𝔽_ℓ) + 14`;
  Stoll's refinement, for `ℓ > 2`, is `#X(ℚ) ≤ #X(𝔽_ℓ) + 2r`, and
  `r ≥ 3`.  Since `#X(𝔽_ℓ) ≥ 1`, both bounds exceed `2` for EVERY
  admissible `ℓ`.  So "Chabauty–Coleman" here means the refined method —
  Coleman integration residue disk by residue disk, or Chabauty combined
  with a Mordell–Weil sieve — and NOT a counting bound of the shape
  `card_le_of_rankZeroJacobian`, which this file's
  `y0HasNoRationalPoint_of_witnessPrime` and
  `y0HasNoRationalPoint_of_sieveLevel` are the two instances of.  **The
  check that refutes this**: exhibit a prime `ℓ ∤ 169` with
  `#X_0(169)(𝔽_ℓ) + 2·3 ≤ 2`, which is impossible since point counts are
  positive.

IRREDUCIBLE at this pin, and strictly harder than the eleven
`kenkuLevels`: it needs `p`-adic integration on curves, which exists in
no form here, on top of the integral model and Jacobian machinery the
rank-`0` route already lacks. -/
theorem y0HasNoRationalPoint_oneSixtyNine : Y0HasNoRationalPoint 169 :=
  sorry

/-- **Kenku's determination at the eight prime-square levels** (PROVEN
2026-07-27 over `y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel` and
`y0HasNoRationalPoint_oneSixtyNine`; introduced as a sorry node earlier
the same day): `Y_0(N)(ℚ) = ∅` for each of the eight levels `N = p²`,
`p ∈ {11, 13, 17, 19, 37, 43, 67, 163}`.

TRUE: none of `121, 169, 289, 361, 1369, 1849, 4489, 26569` lies in the
Mazur–Kenku list `1, …, 19, 21, 25, 27, 37, 43, 67, 163` of levels with a
non-cuspidal rational point — every one of them exceeds `163`.

**This is the whole remaining content of Kenku's prime-square theorem**,
and it is a FINITE statement.  `cuspidal_x0_isogenyPrimeSq` used to carry
the assertion for every prime `p ≥ 11`; the infinite part of that family
is now discharged by Mazur (`y0HasNoRationalPoint_prime`, through
`y0HasNoRationalPoint_of_dvd` at `p ∣ p²`), because a prime `p` outside
`mazurIsogenyPrimes` already has `Y_0(p)(ℚ) = ∅` and a rational point of
`Y_0(p²)` would push down to one of `Y_0(p)`.  What survives is exactly
the eight primes for which `Y_0(p)(ℚ) ≠ ∅`, so no descent to level `p` is
available and each `p²` must be treated on its own.

**Where each of the eight comes from in the literature.**  These are
Kenku's papers, one level at a time: `X_0(169)` in *The modular curve
`X_0(169)` and rational isogeny*, J. London Math. Soc. (2) **22** (1980);
`X_0(125)`, `X_1(25)`, `X_1(49)` in J. London Math. Soc. (2) **23**
(1981), whose method covers `X_0(121)`; and the four large levels
`1369, 1849, 4489, 26569` (`p = 37, 43, 67, 163`) by the isogeny-character
argument, since a rational point of `Y_0(p²)` gives an elliptic curve
whose mod-`p` representation has TWO independent stable lines, hence is
diagonal — which the CM description of `Y_0(p)(ℚ)` at `p = 43, 67, 163`
and the two `j`-invariants at `p = 37` exclude.

IRREDUCIBLE at this pin, but no longer uniformly so, and the halves have
different prospects — which is the reason for splitting the node out
rather than leaving it inside the `p ≥ 11` statement.

**The split is `7 + 1`, not `4 + 4`** (corrected 2026-07-27; the
superseded `4 + 4` reading is kept below, struck through in prose, because
a dispatch was written from it and the next reader should be able to see
what was wrong with it).  The cut is
`isogenyClassPrimeSqLevels = [121, 289, 361, 1369, 1849, 4489, 26569]`
against the singleton `169`, and the discriminating fact is
`genus X_0(13) = 0` while `genus X_0(p) ≥ 1` for the other seven primes.
See `isogenyClassPrimeSqLevels` for the reduction and the genus table.

*The superseded reading, and why it is wrong.*  It ran:

* ~~`121, 169, 289, 361` are genuine rational-point determinations on
  curves of genus `6, 8, 17, 22`, so the route at all four is
  Chabauty–Coleman~~ — **false for three of the four.**  `121, 289, 361`
  reduce to the FINITE sets `Y_0(11)(ℚ)`, `Y_0(17)(ℚ)`, `Y_0(19)(ℚ)` by
  the same two-independent-lines argument that handles the four large
  levels, and their genus-`6`, `17`, `22` curves never enter.  Only `169`
  is forced onto its own curve.
* ~~and `1369, 1849, 4489, 26569` are the isogeny-character half~~ — true,
  but not a HALF: it is four members of a seven-member family.

What survives from it unchanged, and is the reason the table below is
kept: the machinery this file already carries (`HasRankZeroJacobian`,
`card_le_of_rankZeroJacobian`, `IsSharpSieve`) **does NOT apply at
`121, 169, 289, 361`**, because its rank-`0` input is false at all four.
That warning was right and still is.

  #### Reconnaissance (PARI/GP 2.17.4, 2026-07-27)

  Decomposing `S_2(Γ_0(N))^new` into newform factors and taking
  `ord_{s=1} L(f, s)` on each — the same computation the `kenkuLevels`
  reconnaissance block performs, and the check that would refute the
  claim above if it came back all zeros:

  | `N`   | genus | `dim^new` | factors `(deg 𝕋_f, ord L)`                   | `rank J_0(N)` |
  |-------|-------|-----------|----------------------------------------------|---------------|
  | `121` | `6`   | `4`       | `(1,0) (1,0) (1,1) (1,0)`                    | `1`           |
  | `169` | `8`   | `8`       | `(2,0) (3,0) (3,3)`                          | `3`           |
  | `289` | `17`  | `15`      | `(1,1) (2,0) (2,2) (3,0) (3,3) (4,0)`        | `6`           |
  | `361` | `22`  | `20`      | `(1,0) (1,1) (2,0)×4 (3,0) (3,3) (4,4)`      | `8`           |

  The old part contributes `0` at each: it is `J_0(11)²`, `0`, `J_0(17)²`,
  `J_0(19)²`, and `J_0(11), J_0(17), J_0(19)` all have rank `0`.

  **Unconditionality.**  At `121`, `289` and `361` the vanishing occurs at
  a factor with `deg 𝕋_f = 1` — an elliptic curve of analytic rank `1` —
  so Gross–Zagier plus Kolyvagin give Mordell–Weil rank `1` there
  *unconditionally*, and `rank J_0(N)(ℚ) > 0` is a theorem.  At `169` the
  only vanishing is at a `3`-dimensional factor of analytic rank `3`, so
  positivity of the Mordell–Weil rank is conditional on BSD; what is
  unconditional at `169` is only that the counting route has no rank input
  available.

  **What this leaves.**  Every one of the four satisfies
  `rank J_0(N)(ℚ) < genus X_0(N)` (`1 < 6`, `3 < 8`, `6 < 17`, `8 < 22`),
  which is precisely Chabauty–Coleman's hypothesis.  **Do not dispatch a
  prover at `121, 169, 289, 361` expecting to reuse
  `card_le_of_rankZeroJacobian`; the rank input it needs is false at all
  four.**  But `r < g` says only that Chabauty is *available*, not that it
  is *needed* — and at `121, 289, 361` it is not: see
  `isogenyClassPrimeSqLevels`.  At `169` it is, and there the CRUDE bounds
  do not suffice either; see `y0HasNoRationalPoint_oneSixtyNine` for that
  computation.

The isogeny-character route is the same circle of ideas as
`WeierstrassCurve.not_isogenyCharacter_of_prime_ge_twentyThree` and
`not_two_stable_lines_of_jInvariant` in `FreyCurve/MazurTorsion.lean`.
**Note the direction**: that module imports this one, so the implication
may not be used here, and a successor must prove the modular-curve form
directly — but it may freely copy the ARGUMENT.

Stated as a membership in an explicit list, in the idiom of
`hasRankZeroJacobian_of_kenkuLevel`, so that a successor may close the
levels independently.

**PROVEN 2026-07-27** over the two nodes below, along an axis that is NOT
the one this docstring previously proposed — see
`isogenyClassPrimeSqLevels` for the correction and for the computation
that forces it. -/
theorem y0HasNoRationalPoint_of_isogenyPrimeSqLevel (N : ℕ)
    (hN : N ∈ isogenyPrimeSqLevels) : Y0HasNoRationalPoint N := by
  have h : N = 121 ∨ N = 169 ∨ N = 289 ∨ N = 361 ∨ N = 1369 ∨ N = 1849 ∨
      N = 4489 ∨ N = 26569 := by
    simpa [isogenyPrimeSqLevels] using hN
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel 121 (by decide)
  · exact y0HasNoRationalPoint_oneSixtyNine
  · exact y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel 289 (by decide)
  · exact y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel 361 (by decide)
  · exact y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel 1369 (by decide)
  · exact y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel 1849 (by decide)
  · exact y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel 4489 (by decide)
  · exact y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel 26569 (by decide)

/-- **Kenku's prime-square determination, on `X_0(p²)` for `p ≥ 11`**
(PROVEN 2026-07-27 over `y0HasNoRationalPoint_of_isogenyPrimeSqLevel`;
introduced as a sorry node 2026-07-26): every rational point of `X_0(p²)`
is a cusp, for every prime `p ≥ 11`.

TRUE, and it is Kenku's theorem.  The Mazur–Kenku list of levels `N` with
`Y_0(N)(ℚ) ≠ ∅` is

    1, …, 19, 21, 25, 27, 37, 43, 67, 163,

whose largest element is `163`; and for a prime `p ≥ 11` the level `p²` is
at least `121`, is a perfect square, and is therefore in the list only if
it is one of `1, 4, 9, 16` — all of which are `< 121`.  So `p² ` is outside
the list for EVERY prime `p ≥ 11`, uniformly.

(That uniformity is a fact about the *statement*, not about its proof.
The proof below does split on `p ∈ mazurIsogenyPrimes`, because the two
halves are discharged by genuinely different theorems — Mazur's for the
infinite half, Kenku's eight levels for the rest.  An earlier version of
this docstring read "uniformly, with no case analysis", which was a claim
about the truth and was silently taken for a claim about the route.)

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

**NOT IRREDUCIBLE — the infinite half is Mazur's, and is now discharged**
(2026-07-27, correcting the audit this docstring previously carried,
which read "IRREDUCIBLE at this pin, for the same reason as every other
level node here").  That verdict was recorded before the case split below
was tried, and it is wrong for every prime `p ∉ mazurIsogenyPrimes`:

* if `p ∉ mazurIsogenyPrimes` then `Y_0(p)(ℚ) = ∅` by
  `y0HasNoRationalPoint_prime` — Mazur's theorem, already a node here —
  and `p ∣ p²`, so `y0HasNoRationalPoint_of_dvd` gives
  `Y_0(p²)(ℚ) = ∅` with no reference to the geometry of `X_0(p²)` at all;
* the new `cuspidal_of_y0HasNoRationalPoint` converts that back into
  cuspidality of `X_0(p²)(ℚ)`, which is the shape stated here.

So the genus-`≥ 6` obstruction the old audit named applies only to the
eight levels where the descent to level `p` is unavailable — exactly
`p ∈ mazurIsogenyPrimes` with `11 ≤ p` — and those are now the separate
node `y0HasNoRationalPoint_of_isogenyPrimeSqLevel`, whose docstring
records what each of the eight still needs.  **The check that would
refute this reading**: `y0HasNoRationalPoint_prime` is stated for `p`
prime with `p ∉ mazurIsogenyPrimes` and nothing else, and
`y0HasNoRationalPoint_of_dvd` needs only `N ≠ 0` and `M ∣ N`; if either
acquired a hypothesis this proof does not supply, the split would fail to
elaborate.

Sources for the eight residual levels: Kenku, *The modular curves
`X_0(65)` and `X_0(91)` and rational isogeny*, Math. Proc. Cambridge
Philos. Soc. **87** (1980); *On the modular curves `X_0(125)`, `X_1(25)`
and `X_1(49)`*, J. London Math. Soc. (2) **23** (1981); *The modular curve
`X_0(169)` and rational isogeny*, J. London Math. Soc. (2) **22** (1980).

Quantified over every model of `IsCompactificationY0`, so it is at least
as strong as the `Y_0(p²)` statement it carries and cannot be discharged
by a degenerate choice of `X`. -/
theorem cuspidal_x0_isogenyPrimeSq {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (hc : IsCoarseModuliY0 (p ^ 2) strY) (hX : IsCompactificationY0 strY strX)
    (x : RelPoint strX (𝟙 SpecQ)) : hX.IsCusp x := by
  refine cuspidal_of_y0HasNoRationalPoint hc hX ?_ x
  by_cases hmem : p ∈ mazurIsogenyPrimes
  · exact y0HasNoRationalPoint_of_isogenyPrimeSqLevel (p ^ 2)
      (mem_isogenyPrimeSqLevels_of_mem_mazurIsogenyPrimes hmem hp11)
  · exact y0HasNoRationalPoint_of_dvd (pow_ne_zero 2 hp.pos.ne')
      (dvd_pow_self p two_ne_zero) (y0HasNoRationalPoint_prime hp hmem)

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

/-! #### The `61` semiprime levels, partitioned by the method that settles each

The five declarations below cut `cuspidal_x0_semiprime_of_mazurPrimes`
along the partition that the LITERATURE and the arithmetic actually use,
rather than along a guess.  The partition, and the reconnaissance behind
it, is the substance of this block; read it before dispatching anyone at
the leaves, because the four leaves have four genuinely different
prospects and only one of them is closable with machinery this file
already has.

**The count.**  `mazurIsogenyPrimes` has `12` elements, so `66` unordered
pairs; `5` give the excluded products `6, 10, 14, 15, 21`; `61` remain.

**The dividing line: is `X_0(p)(ℚ)` FINITE?**  Split
`mazurIsogenyPrimes` by the genus of `X_0(p)`:

* `2, 3, 5, 7, 13` — `X_0(p)` has genus `0`, so `X_0(p) ≅ ℙ¹` and
  `X_0(p)(ℚ)` is INFINITE.  Knowing the level-`p` points says nothing.
* `11, 17, 19, 37, 43, 67, 163` — `X_0(p)` has genus `≥ 1` and
  `X_0(p)(ℚ)` is FINITE and explicitly tabulated by Mazur.  These are
  `isolatedIsogenyPrimes` below.

Of the `61` levels, exactly `56` have at least one prime of the second
kind and exactly `5` have both primes of the first kind, namely
`26, 35, 39, 65, 91` (verified with PARI/GP 2.17.4, 2026-07-27, by
enumerating all `66` pairs).  That is the primary cut, and it is not a
convenience: the `56` need no curve geometry at all, and the `5` are five
separate rational-point determinations.

**Reconnaissance on the five (PARI/GP 2.17.4, 2026-07-27).**  Genus and
cusp number from the standard `Γ₀(N)` index formulas; `rank J_0(N)` as
the analytic rank, i.e. `Σ_f ord_{s=1} L(f, s)` over the newform factors
of every level dividing `N` with old multiplicity;
`#X_0(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))` by Eichler–Shimura, all
cusps being rational since every one of the five is squarefree:

| `N` | genus | `rank J_0(N)` | rational cusps | best odd `ℓ ∤ N` | `#X_0(N)(𝔽_ℓ)` | route |
|-----|-------|---------------|----------------|-------------------|------------------|-------|
| `26` | `2` | `0` | `4` | `3`  | `6` | rank `0` + **sieve** |
| `35` | `3` | `0` | `4` | `3`  | `4` | rank `0` + **witness prime** |
| `39` | `3` | `0` | `4` | `5`  | `4` | rank `0` + **witness prime** |
| `65` | `5` | `1` | `4` | `3`  | `4` | **Chabauty–Coleman** |
| `91` | `7` | `2` | `4` | `5`  | `4` | **Chabauty–Coleman** |

Three facts in that table are load-bearing, and each is the reason for
one of the three small leaves:

1. At `35` and `39` the count EQUALS the rational-cusp number at an odd
   prime of good reduction, and the rank is `0`.  That is exactly the
   hypothesis shape of `y0HasNoRationalPoint_of_witnessPrime`, so these
   two are closable with machinery ALREADY IN THIS FILE.
2. At `26` the rank is `0` but the count is NEVER `4`: over
   `3 ≤ ℓ < 60`, `ℓ ∤ 26`, the minimum is `6` (at `ℓ = 3`; the values run
   `6, 10, 8, 8, 24, 12, 28, …`).  So `y0HasNoRationalPoint_of_witnessPrime`
   cannot close `26` however the prime is chosen — it is in the same
   position as `45, 54, 63, 75` and needs the multi-prime Mordell–Weil
   sieve.  **This is the single most useful line here**, because it is
   the route a successor would otherwise try first and waste a cycle on.
3. At `65` and `91` the count IS sharp, and that is a trap: the rank is
   `1` and `2`, so `HasRankZeroJacobian` is FALSE at both and
   `card_le_of_rankZeroJacobian` has no rank input available.  Both do
   satisfy `rank < genus` (`1 < 5`, `2 < 7`), which is Chabauty–Coleman's
   hypothesis — a theory this development does not have in any form.

**Which paper settles which level.**  Checked against the published
titles rather than copied from this node's previous docstring, which was
wrong in two places:

* `X_0(39)` — Kenku, *The modular curve `X_0(39)` and rational isogeny*,
  Math. Proc. Cambridge Philos. Soc. **85** (1979) 21–23.  That paper is
  about `X_0(39)` ONLY; the earlier docstring credited it with `X_0(35)`
  as well, which its title contradicts.
* `X_0(65)`, `X_0(91)` — Kenku, *The modular curves `X_0(65)` and
  `X_0(91)` and rational isogeny*, ibid. **87** (1980) 15–20.  Note these
  are exactly the two positive-rank levels, which is a strong consistency
  check on the table above: Kenku grouped them because they are the hard
  ones.
* `X_0(26)`, `X_0(35)` — **not the subject of any Kenku paper title.**
  Both have rank-`0` Jacobian and genus `2`, `3`, which puts them inside
  the classical method of Ogg, *Rational points on certain elliptic
  modular curves*, Proc. Sympos. Pure Math. **24** (1973) 221–231, and
  *Hyperelliptic modular curves*, Bull. Soc. Math. France **102** (1974)
  449–462.  The standard attribution for the composite levels as a whole
  is "Fricke, Kenku, Klein, Kubert, Ligozat, Mazur, Ogg"; which of them
  owns these two is NOT pinned down here, and a successor should not
  cite Kenku for them.
* **Two citations in the previous docstring belong to a different node.**
  J. London Math. Soc. (2) **22** (1980) is *The modular curve `X_0(169)`*
  and ibid. **23** (1981) is *On the modular curves `X_0(125)`, `X_1(25)`
  and `X_1(49)`* — PRIME-POWER levels.  They settle none of these `61`
  and belong to `cuspidal_x0_isogenyPrimeSq`, where they are already
  correctly cited.
* The `56` are Mazur, *Rational isogenies of prime degree*, Invent. Math.
  **44** (1978), Theorem 1 and its table, together with Kenku, *On the
  number of `ℚ`-isomorphism classes of elliptic curves in each
  `ℚ`-isogeny class*, J. Number Theory **15** (1982) 199–202.

**FAITHFULNESS AUDIT of the statement being cut.**  The level list and
the exclusion set were checked, not assumed.  The semiprimes in the
Mazur–Kenku list `1, …, 19, 21, 25, 27, 37, 43, 67, 163` are `6 = 2·3`,
`10 = 2·5`, `14 = 2·7`, `15 = 3·5`, `21 = 3·7` and no others, so
`{6, 10, 14, 15, 21}` is exactly right.  Every one of the `61` remaining
levels has genus `≥ 2`, the minimum being genus `2` at `N = 26`, so the
docstring's "none is an elliptic-curve rank computation" is correct.  No
error was found in the statement. -/

/-- **The seven Mazur primes at which `X_0(p)(ℚ)` is FINITE**,
`{11, 17, 19, 37, 43, 67, 163}`.

These are exactly the `p ∈ mazurIsogenyPrimes` for which `X_0(p)` has
positive genus; the other five, `2, 3, 5, 7, 13`, have `X_0(p) ≅ ℙ¹` and
so infinitely many rational points.  The distinction is what makes the
`56`-level family uniform and leaves only `5` levels to compute — see
the section docstring above. -/
def isolatedIsogenyPrimes : Finset ℕ := {11, 17, 19, 37, 43, 67, 163}

/-- **The five semiprime levels at which BOTH primes have `X_0(p)` of
genus `0`**, `26 = 2·13`, `35 = 5·7`, `39 = 3·13`, `65 = 5·13`,
`91 = 7·13`.

Every other product of two distinct `mazurIsogenyPrimes` outside
`{6, 10, 14, 15, 21}` has a prime in `isolatedIsogenyPrimes` and is
handled by `y0HasNoRationalPoint_of_isolatedSemiprime`.  These five are
the residue, and each is a genuine determination of the rational points
of a curve of genus `2, 3, 3, 5, 7`. -/
def smallSemiprimeLevels : List ℕ := [26, 35, 39, 65, 91]

/-- **The two small semiprime levels that a single witness prime
closes**, `35` and `39`.

`rank J_0(N)(ℚ) = 0` at both, and the Eichler–Shimura count equals the
number of rational cusps at `ℓ = 3` for `N = 35` and `ℓ = 5` for
`N = 39` (both `4 = 4`). -/
def witnessSemiprimeLevels : List ℕ := [35, 39]

/-- **The two small semiprime levels whose Jacobian has POSITIVE rank**,
`65` (rank `1`, genus `5`) and `91` (rank `2`, genus `7`).

Both satisfy `rank < genus`, so Chabauty–Coleman applies; no rank-`0`
counting argument does. -/
def chabautySemiprimeLevels : List ℕ := [65, 91]

/-- **The `56` levels with an isolated prime** (sorry node, introduced
2026-07-27): for `p ∈ isolatedIsogenyPrimes` and any prime `q ≠ p`,
`Y_0(pq)(ℚ) = ∅`.

TRUE, and it needs NO geometry of `X_0(pq)` — which is why it is one
statement rather than `56`.

**The argument.**  A rational point of `X_0(pq)` pushes forward along the
degree-`ψ(q)` map `X_0(pq) → X_0(p)`, `(E, C_{pq}) ↦ (E, C_p)`, which
sends non-cuspidal points to non-cuspidal points.  For
`p ∈ isolatedIsogenyPrimes` Mazur's Theorem 1 tabulates `X_0(p)(ℚ)`
completely, and the non-cuspidal points are these `j`-invariants:

| `p` | non-cuspidal `j` | CM |
|-----|------------------|----|
| `11`  | `−2¹⁵ = −32768`; `−11² = −121`; `−11·131³ = −24729001` | first only, disc `−11` |
| `17`  | `−17·373³/2¹⁷`; `−17²·101³/2` | no |
| `19`  | `−2¹⁵·3³ = −884736` | disc `−19` |
| `37`  | `−7·11³ = −9317`; `−7·137³·2083³` | no |
| `43`  | `−884736000` | disc `−43` |
| `67`  | `−147197952000` | disc `−67` |
| `163` | `−262537412640768000` | disc `−163` |

None of these is `0` or `1728`, so the coarse point IS represented by an
elliptic curve over `ℚ`, determined up to quadratic twist; and possessing
a Galois-stable cyclic subgroup of order `q` is twist-invariant.  That is
what disposes of the coarse-space subtlety this node's siblings warn
about, and it is why the argument works at the level of the coarse space
and not merely for pairs `(E, C)` defined over `ℚ`.

It then remains that none of those curves has a rational `q`-isogeny for
any prime `q ≠ p`.  For the five CM rows this is uniform and clean: the
mod-`ℓ` image lies in the normalizer of a Cartan subgroup attached to
`K = ℚ(√−p)`, and a Galois-stable line in `E[ℓ]` exists only when `ℓ`
ramifies in `K`, i.e. only for `ℓ = p`.  For the four non-CM `j`-values
it is a finite explicit check, confirmed against LMFDB at `p = 11`, where
the three `j`-invariants give isogeny classes `121.a`, `121.b`, `121.c`,
each of size `2` with the single isogeny degree `11`.

**CIRCULARITY WARNING for whoever proves this.**  Do NOT discharge it by
citing Kenku's list of possible cyclic isogeny degrees over `ℚ`
(J. Number Theory **15** (1982) 199–202).  That list is precisely what
this whole subtree is proving: "a curve with an `11`-isogeny has no
`2`-isogeny" is the assertion `22` is not an isogeny degree.  The proof
must go through the explicit `j`-invariants above.

**Stated uniformly in `q`, which is stronger than needed and easier to
prove.**  Only the `56` cases with `q ∈ mazurIsogenyPrimes` are consumed
here; for the other `q` the conclusion already follows from
`y0HasNoRationalPoint_prime` through `y0HasNoRationalPoint_of_dvd` at
`q ∣ pq`.  The descent argument does not look at `q` at all, so
restricting the statement would buy nothing.  It is TRUE as stated: every
`pq` with `p ≥ 11` is at least `22`, and the only members of the
Mazur–Kenku list that large are `25, 27, 37, 43, 67, 163`, none of which
is a product of two distinct primes.

IRREDUCIBLE at this pin: it needs Mazur's determination of `X_0(p)(ℚ)`
for the seven isolated primes — strictly more than `cuspidal_x0_prime`,
which only covers `p ∉ mazurIsogenyPrimes` — plus the CM theory of the
mod-`ℓ` image. -/
theorem y0HasNoRationalPoint_of_isolatedSemiprime {p q : ℕ}
    (_hp : p ∈ isolatedIsogenyPrimes) (_hq : q.Prime) (_hpq : p ≠ q) :
    Y0HasNoRationalPoint (p * q) :=
  sorry

/-- **`Y_0(35)(ℚ) = Y_0(39)(ℚ) = ∅`** (sorry node, introduced
2026-07-27).

TRUE, and **this is the one leaf here that the machinery already in this
file can close**, so it should be dispatched first and separately.  Both
levels have `rank J_0(N)(ℚ) = 0` and a sharp witness prime:

| `N` | genus | rational cusps | `ℓ` | `#X_0(N)(𝔽_ℓ)` |
|-----|-------|----------------|-----|------------------|
| `35` | `3` | `4` | `3`  | `4` |
| `39` | `3` | `4` | `5`  | `4` |

which is exactly the hypothesis shape of
`y0HasNoRationalPoint_of_witnessPrime`.  Concretely, a successor closes
this by adding `35, 39` to `kenkuLevels` and the rows `(35, 3, 4)`,
`(39, 5, 4)` to `x0WitnessTable`, then reusing that theorem verbatim.
**Those two declarations belong to another owner** (they are the target
of a separate in-flight task), so they are not edited here; the leaf is
stated over its own list instead, and the two edits can be made whenever
that region is free.

`N = 39` is Kenku, *The modular curve `X_0(39)` and rational isogeny*,
Math. Proc. Cambridge Philos. Soc. **85** (1979) 21–23.  `N = 35` is not
the subject of a Kenku paper — see the section docstring. -/
theorem y0HasNoRationalPoint_of_witnessSemiprimeLevel (N : ℕ)
    (_hN : N ∈ witnessSemiprimeLevels) : Y0HasNoRationalPoint N :=
  sorry

/-- **`Y_0(26)(ℚ) = ∅`** (sorry node, introduced 2026-07-27).

TRUE: `26` is not in the Mazur–Kenku list.  `X_0(26)` has genus `2`, four
rational cusps, and `rank J_0(26)(ℚ) = 0` — indeed `J_0(26) ~ 26a × 26b`
with both factors elliptic of rank `0`.

**Why this is its own leaf and not folded in with `35, 39`.**  The rank
is `0`, so `card_le_of_rankZeroJacobian` applies — and it is NEVER SHARP.
Over the odd primes `3 ≤ ℓ < 60` with `ℓ ∤ 26` the Eichler–Shimura counts
`#X_0(26)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(26)))` are

    ℓ  =  3  5  7 11 17 19 23 29 31 37 41 43 47 53 59
    #  =  6 10  8  8 24 12 28 22 32 42 42 50 32 42 76

with minimum `6 > 4 = numRationalCusps 26`.  So
`y0HasNoRationalPoint_of_witnessPrime` cannot close `26` for ANY choice
of prime, and a successor must use the multi-prime Mordell–Weil sieve
instead — the same route as `45, 54, 63, 75`, whose apparatus
(`x0SieveLevels`, `card_le_of_sieve`, `y0HasNoRationalPoint_of_sieveLevel`)
is already in this file and is the thing to reuse.  The sieve has to cut
the `6` points of `X_0(26)(𝔽_3)` down to the `4` cusps, using
`J_0(26)(ℚ) ≅ ℤ/21ℤ`.

**Do not dispatch a prover at this expecting a witness prime**; that is
the mistake the table above exists to prevent.

Attribution: not a Kenku paper title; genus `2` and rank `0` place it
inside Ogg's classical method — see the section docstring. -/
theorem y0HasNoRationalPoint_x0TwentySix : Y0HasNoRationalPoint 26 :=
  sorry

/-- **`Y_0(65)(ℚ) = Y_0(91)(ℚ) = ∅`** (sorry node, introduced
2026-07-27) — the two genuinely hard levels of the `61`.

TRUE: neither `65` nor `91` is in the Mazur–Kenku list.  This is Kenku,
*The modular curves `X_0(65)` and `X_0(91)` and rational isogeny*, Math.
Proc. Cambridge Philos. Soc. **87** (1980) 15–20 — and the fact that
Kenku treated exactly these two together is the historical confirmation
of the arithmetic reason they are grouped here.

**Why no counting argument can work, however sharp it looks.**

| `N` | genus | `rank J_0(N)` | rational cusps | `ℓ` | `#X_0(N)(𝔽_ℓ)` |
|-----|-------|---------------|----------------|-----|------------------|
| `65` | `5` | `1` | `4` | `3` | `4` |
| `91` | `7` | `2` | `4` | `5` | `4` |

The counts ARE equal to the cusp number, which makes these two look like
`35` and `39`.  They are not: `card_le_of_rankZeroJacobian` needs
`HasRankZeroJacobian`, and that is FALSE at both — `J_0(65)` contains the
rank-`1` elliptic curve `65a`, and `J_0(91)` contains a rank-`1` factor
twice over.  With positive rank, `J_0(N)(ℚ)` is infinite and the
Abel–Jacobi image is not bounded by any point count.  **The sharp-looking
count is a trap, and it is the reason these two are split off from
`witnessSemiprimeLevels` rather than listed beside them.**

Both analytic ranks are unconditional as LOWER bounds on the Mordell–Weil
rank in the sense that matters here: the vanishing at `65` occurs at a
`1`-dimensional factor, so Gross–Zagier and Kolyvagin give
`rank J_0(65)(ℚ) ≥ 1` outright.

What is left is Chabauty–Coleman, whose hypothesis `rank < genus` holds
at both (`1 < 5` and `2 < 7`).  IRREDUCIBLE at this pin, and strictly
harder than every other leaf in this block: Chabauty–Coleman exists in
this development in no form at all — it needs `p`-adic integration of
differentials on the curve and the Coleman integral, on top of the
Jacobian and its Mordell–Weil group. -/
theorem y0HasNoRationalPoint_of_chabautySemiprimeLevel (N : ℕ)
    (_hN : N ∈ chabautySemiprimeLevels) : Y0HasNoRationalPoint N :=
  sorry

/-- **The five small semiprime levels, assembled** (PROVEN): a case split
of `smallSemiprimeLevels` into the three method classes.

Pure dispatch — `26` to the sieve leaf, `35, 39` to the witness-prime
leaf, `65, 91` to the Chabauty leaf.  It exists so that the three leaves
can be owned and closed independently while the caller sees one
statement. -/
theorem y0HasNoRationalPoint_of_smallSemiprimeLevel (N : ℕ)
    (hN : N ∈ smallSemiprimeLevels) : Y0HasNoRationalPoint N := by
  fin_cases hN
  · exact y0HasNoRationalPoint_x0TwentySix
  · exact y0HasNoRationalPoint_of_witnessSemiprimeLevel 35 (by decide)
  · exact y0HasNoRationalPoint_of_witnessSemiprimeLevel 39 (by decide)
  · exact y0HasNoRationalPoint_of_chabautySemiprimeLevel 65 (by decide)
  · exact y0HasNoRationalPoint_of_chabautySemiprimeLevel 91 (by decide)

/-- **The arithmetic behind the case split** (PROVEN): if `p, q` are
distinct members of `mazurIsogenyPrimes`, NEITHER of them isolated, and
`p * q` is not one of the five excluded products, then
`p * q ∈ smallSemiprimeLevels`.

Pure finite computation: removing `isolatedIsogenyPrimes` from
`mazurIsogenyPrimes` leaves `{2, 3, 5, 7, 13}`, whose `10` unordered
pairs give `6, 10, 14, 26, 15, 21, 39, 35, 65, 91`; discarding the five
excluded products leaves exactly `26, 35, 39, 65, 91`.  `fin_cases` on
both memberships reduces this to `144` decidable claims.

Note `hpq` is genuinely needed: without it `p = q` would allow `p * q` to
be a square such as `4` or `169`, which is not in the list. -/
theorem mem_smallSemiprimeLevels {p q : ℕ} (hpm : p ∈ mazurIsogenyPrimes)
    (hqm : q ∈ mazurIsogenyPrimes) (hpq : p ≠ q)
    (hpi : p ∉ isolatedIsogenyPrimes) (hqi : q ∉ isolatedIsogenyPrimes)
    (hmem : p * q ∉ ({6, 10, 14, 15, 21} : Finset ℕ)) :
    p * q ∈ smallSemiprimeLevels := by
  fin_cases hpm <;> fin_cases hqm <;> revert hpq hpi hqi hmem <;> decide

/-- **Kenku's semiprime determination, on `X_0(pq)`** (PROVEN 2026-07-27
over the four leaves above): for distinct primes `p, q` both in
`mazurIsogenyPrimes` with `p * q ∉ {6, 10, 14, 15, 21}`, every rational
point of `X_0(pq)` is a cusp.

TRUE, and FINITE: `61` explicit levels, the smallest `2 · 11 = 22` and
the largest `67 · 163 = 10921`.  Every one has genus `≥ 2` (minimum `2`,
at `N = 26`), so none is an elliptic-curve rank computation.

**The cut.**  The section docstring above carries the full partition, the
PARI/GP reconnaissance and the corrected literature map; in outline:

* `56` levels have a prime in `isolatedIsogenyPrimes`, where `X_0(p)(ℚ)`
  is finite and tabulated, and descend to it uniformly —
  `y0HasNoRationalPoint_of_isolatedSemiprime`;
* the residual `5` are `26, 35, 39, 65, 91`, split by the route their
  arithmetic forces: `35, 39` (rank `0`, sharp witness prime — closable
  with this file's existing machinery), `26` (rank `0`, no sharp prime
  exists — needs the sieve), `65, 91` (positive rank — needs
  Chabauty–Coleman).

The proof itself is the case split plus the passage from
`Y_0(pq)(ℚ) = ∅` to cuspidality of `X_0(pq)(ℚ)`, which is immediate for
an open immersion: a non-cusp is by definition a point factoring through
`Y`, and `IsCompactificationY0.over` turns that factorisation into a
rational point of `Y`.

This is `y0HasNoRationalPoint_semiprime_of_mazurPrimes` moved onto the
compactification; see that node's docstring for why the level statements
cannot be phrased against the affine `Y_0(pq)`. -/
theorem cuspidal_x0_semiprime_of_mazurPrimes {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hpm : p ∈ mazurIsogenyPrimes)
    (hqm : q ∈ mazurIsogenyPrimes)
    (hmem : p * q ∉ ({6, 10, 14, 15, 21} : Finset ℕ))
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (hc : IsCoarseModuliY0 (p * q) strY) (hX : IsCompactificationY0 strY strX)
    (x : RelPoint strX (𝟙 SpecQ)) : hX.IsCusp x := by
  have hY : Y0HasNoRationalPoint (p * q) := by
    by_cases hpi : p ∈ isolatedIsogenyPrimes
    · exact y0HasNoRationalPoint_of_isolatedSemiprime hpi hq hpq
    · by_cases hqi : q ∈ isolatedIsogenyPrimes
      · rw [Nat.mul_comm]
        exact y0HasNoRationalPoint_of_isolatedSemiprime hqi hp hpq.symm
      · exact y0HasNoRationalPoint_of_smallSemiprimeLevel _
          (mem_smallSemiprimeLevels hpm hqm hpq hpi hqi hmem)
  rintro ⟨y, hy⟩
  refine (hY Y strY hc).false ⟨y, ?_⟩
  rw [← hX.over, ← Category.assoc, hy]
  exact x.2

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
3. `card_le_of_rankZeroJacobian` — the reduction bound, PROVEN;
4. `y0HasNoRationalPoint_of_witnessPrime` — the assembly, PROVEN, and
   what the seven single-prime levels below call.

Items 3 and 4 are **declared further down**, after the Néron subsection,
because the reduction bound is proven over the integral models built
there; see the `#### The single-prime counting bound` heading for why
that turned out to be the right place for them rather than here.

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

/-- **The divisors of `N` that carry a `ℚ`-rational cusp of `X_0(N)`.**

The index set underlying `numRationalCusps`, named so that the cusps can
be indexed BY it rather than merely counted — see
`IsX0Compactification.CuspIndexing`.  `d` qualifies exactly when the
`φ(gcd(d, N/d))` cusps above `d` form a Galois orbit of size one. -/
def rationalCuspDivisors (N : ℕ) : Finset ℕ :=
  N.divisors.filter fun d => Nat.totient (Nat.gcd d (N / d)) = 1

/-- **`numRationalCusps` counts `rationalCuspDivisors`** (PROVEN, `rfl`).

Stated rather than left to unfolding so that the two never drift apart,
and so that consumers can rewrite without exposing the `DecidablePred`
instance inside the `Finset.filter`. -/
theorem numRationalCusps_eq_card (N : ℕ) :
    numRationalCusps N = (rationalCuspDivisors N).card := rfl

/-- **The divisor `1` always carries a rational cusp** (PROVEN).

`gcd(1, N) = 1` and `φ(1) = 1`, so the single cusp above `d = 1` — the
cusp `∞` of `X_0(N)` — is `ℚ`-rational at every level.  This is what
makes `numRationalCusps` positive, and it is the one entry of the table
that needs no computation. -/
theorem one_mem_rationalCuspDivisors {N : ℕ} (hN : N ≠ 0) :
    1 ∈ rationalCuspDivisors N := by
  show (1 : ℕ) ∈ N.divisors.filter fun d => Nat.totient (Nat.gcd d (N / d)) = 1
  refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, ?_⟩
  show Nat.totient (Nat.gcd 1 (N / 1)) = 1
  rw [Nat.div_one, Nat.gcd_one_left, Nat.totient_one]

/-- **`X_0(N)` has at least one rational cusp whenever `N ≠ 0`** (PROVEN).

Immediate from `one_mem_rationalCuspDivisors`.  Recorded because the
counting arguments below are all of the form "`s.card = numRationalCusps
N` and one more point would exceed it", which is vacuous if the count can
be `0`; and because `numRationalCusps 0 = 0` really is `0`
(`Nat.divisors 0 = ∅`), so the hypothesis cannot be dropped. -/
theorem numRationalCusps_pos {N : ℕ} (hN : N ≠ 0) : 0 < numRationalCusps N := by
  rw [numRationalCusps_eq_card]
  exact Finset.card_pos.mpr ⟨1, one_mem_rationalCuspDivisors hN⟩

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

## FORMAL-CONTENT AUDIT (2026-07-27) — STILL TRUE OF *THIS* STRUCTURE,
## AND THE REMEDY HAS NOW LANDED.  SEE THE POST-SCRIPT.

**`redX` is NOT pinned to be the genuine reduction, and there is an
explicit junk witness.**  Take `redX` to send *every* rational point to a
point of `X'` outside the image of `sectionAlong jY' hX'.comm` — a cusp
of the special fibre.  Then the hypothesis of `red_jm` is never
satisfiable, so `red_jm` holds vacuously for any `jm` and any `jm'`, and
the structure is inhabited with no arithmetic content whatever.

*The dictionary is unaffected.*  `isCusp_redX_of_padicValRat_neg` is a
true implication for every datum, junk included — under the junk witness
its conclusion is simply true for trivial reasons.  Nothing downstream of
it is weakened by the junk witness alone.

**POST-SCRIPT (2026-07-27) — THE PINNING EXISTS NOW: `IsX0JNeronDatum`.**
The audit above predicted that the repair would be to re-found this
structure on the `IsX0NeronDatum` layer.  That layer has landed, and the
`j`-map analogue of it is `IsX0JNeronDatum`, in the subsection
`#### The Néron pinning of the `j`-map` at the end of this file.  There
`redX` is *defined* from the valuative criterion plus the special-fibre
identification, `red_jm` is a **THEOREM**
(`IsX0JNeronDatum.red_jm`), and `IsX0JNeronDatum.toJReduction` produces
this structure.  `exists_x0JReductionAt` — also moved there, since it now
consumes `SpecLoc`, which is declared below — is **PROVEN** from
`exists_x0JNeronDatum`.

So this structure survives unchanged as the *interface* that
`isCusp_redX_of_padicValRat_neg` and
`exists_cuspidalReduction_of_padicValRat_neg` are stated over, and every
datum reaching them through `exists_x0JReductionAt` is now a genuine
reduction.  **Anything that needs `redX` to BE the reduction must be
stated over `IsX0JNeronDatum`, not over this structure.**

**CORRECTION TO THE OLD AUDIT'S "FORMAL-IMMERSION LEAF" (2026-07-27).**
The audit above said the leaf `hX'.IsCusp (redX x) → hX.IsCusp x` is
false *because of the junk witness*, implying that pinning `redX` would
rescue it.  **It would not: that implication is false for the GENUINE
reduction too**, and this file already contains the counterexample.
`exists_cuspidalReduction_of_padicValRat_neg` produces, from any elliptic
curve over `ℚ` with a Galois-stable cyclic subgroup of order `N` and
`v_q(j(E)) < 0`, a point `y` of `Y_0(N)(ℚ)` with
`hX'.IsCusp (redX (sectionAlong hX.j hX.over y))` — while
`sectionAlong hX.j hX.over y` is by construction NOT a cusp (take
`y.1` itself as the witness in `IsCompactificationY0.IsCusp`).  A
non-cusp reducing to a cusp is not a pathology; it is the whole point of
Mazur's Cor. 4.4.

**The check that refutes the old reading**: instantiate
`exists_cuspidalReduction_of_padicValRat_neg` at any Frey curve at a
prime `q` of potentially multiplicative reduction and unfold
`IsCompactificationY0.IsCusp` at the resulting point.

What Mazur actually needs is the *two-point* statement — a rational point
and the cusp `∞` having the SAME reduction forces them equal — and that
is a theorem about the rank-`0` Eisenstein quotient and a formal
immersion at `∞`, neither of which is in this module.  A one-point
"reduction of a cusp is a cusp" leaf should not be written at all. -/
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
      redX (sectionAlong hX.j hX.«over» y) = sectionAlong jY' hX'.comm y' →
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
    hX'.IsCusp (hjr.redX (sectionAlong hX.j hX.«over» y)) := by
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
      hX'.IsCusp (hjr.redX (sectionAlong hX.j hX.«over» y)) := by
  obtain ⟨d, hd⟩ := hj.classify_jm E g hg hstable
  exact ⟨hc.classify (𝟙 SpecQ) d, hd,
    isCusp_redX_of_padicValRat_neg hjr _ (by rw [hd]; exact hv)⟩

/-! #### The `j`-line, and the cut of `exists_jMap`

`exists_jMap` was a leaf until 2026-07-27, recorded IRREDUCIBLE.  It is
not: only ONE of its two halves is missing, and the missing half can be
*stated* without being proved, which is all a safe cut needs.

* The half that is PRESENT is the degeneracy map `Y_0(N) ⟶ Y_0(1)` —
  `Gamma0Datum.ofDvd`, `IsBaseChangeOf.ofDvd` and `liesIn_ofDvd_iff` are
  proven above, so `d ↦ jt (d.ofDvd hN (one_dvd N))` is a natural
  transformation out of the `Γ₀(N)`-problem whenever `jt` is one out of
  the `Γ₀(1)`-problem, and `hc.universal` converts it into a morphism.
  This is verbatim the argument `y0HasNoRationalPoint_of_dvd` runs.
* The half that is MISSING is the `j`-invariant of an elliptic SCHEME:
  a natural transformation from `[Γ₀(1)]` to the affine line, agreeing
  with `WeierstrassCurve.j` on curves given by an equation.  That is
  `IsJLine` below, and `exists_jLine` is the single new leaf.

**One leaf for every level.**  `IsJLine` mentions no `N` in its first two
fields, so the same witness serves every level; `exists_jMap` consumes it
at each `N` through `ofDvd`.  That is the gain over cutting at level `N`,
where the natural transformation would have to be produced again for each
level. -/

/-- **The `j`-line `𝔸¹_ℚ = Spec ℚ[X]`**, the target of the `j`-map.

Presented as `Spec` of the polynomial ring rather than as an abstract
scheme so that the cut below is not a tautology: were the target left as
a *field* of `IsJLine`, the structure would be satisfiable by taking it
to be `Y` itself with `jt := hc.classify`, and `exists_jLine` would be a
restatement of `exists_jMap` rather than a reduction of it.  Fixing the
target to the honest `j`-line, with the honest coordinate `jLineVal`, is
what makes `IsJLine` STRICTLY STRONGER: it asks for the `j`-invariant
over every base `T`, not only over `Spec ℚ`. -/
noncomputable abbrev jLine : Scheme.{0} := Spec (CommRingCat.of (Polynomial ℚ))

/-- **The structure morphism `𝔸¹_ℚ ⟶ Spec ℚ`**, `Spec` of `ℚ ↪ ℚ[X]`. -/
noncomputable def jLineStr : jLine ⟶ SpecQ :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)))

/-- **The rational number carried by a rational point of the `j`-line.**

A `ℚ`-point of `Spec ℚ[X]` is `Spec` of a ring map `ℚ[X] → ℚ`
(`Spec.homEquiv`, which is available because `Scheme.Spec` is fully
faithful), and its coordinate is the image of `X`.

**Checked to be the genuine coordinate, not a degenerate reading.**  For
every `a : ℚ` the point `Spec.map (CommRingCat.ofHom (aeval a))` — whose
section condition is `Spec.map_comp` plus `aeval a ∘ algebraMap = id` —
satisfies `jLineVal … = a`, by `simp [jLineVal, Spec.homEquiv]`.  So
`jLineVal` is ONTO `ℚ`.  This matters for faithfulness in the direction
that is easy to miss: a junk `jLineVal` (say the constant `0`) would not
make `exists_jLine` vacuous, it would make it **FALSE**, since
`jt_weierstrass` demands the value `E.j`.  The check is not kept as a
declaration because nothing consumes it and it would be free-floating. -/
noncomputable def jLineVal (x : RelPoint jLineStr (𝟙 SpecQ)) : ℚ :=
  (Spec.homEquiv x.1).hom Polynomial.X

/-- **The `j`-invariant as a natural transformation out of the
`[Γ₀(1)]`-moduli problem, valued in the `j`-line.**

This is the moduli-theoretic content that `exists_jMap` was blocked on,
isolated: `Y_0(1)` is `𝔸¹` with coordinate `j` (Deligne–Rapoport VI;
Katz–Mazur; Silverman *AEC* III.1 over `ℚ̄` together with descent),
and `[Γ₀(1)]` is the bare elliptic-scheme problem because a cyclic
subgroup scheme of order `1` is the zero section.

Three remarks on the axioms, each load-bearing.

**Why the level is `1` and not `N`.**  `Gamma0Datum.ofDvd` forgets the
level structure without touching the elliptic scheme, and
`IsBaseChangeOf.ofDvd` says it does so compatibly with base change.  So a
natural transformation at level `1` restricts to one at every level, and
`exists_jMap` needs only this one object however large `N` is.

**Why `jt_weierstrass` is EXISTENTIAL in `d`, and quantified over `N`.**
The tempting field is "for every datum `d` whose elliptic scheme is a
model of `E`, the value is `E.j`".  It is avoided for exactly the reason
recorded in the subsection docstring for `IsJMapOn.classify_jm`: the only
"is a model of" relation available at this pin is the Galois-equivariant
`≃+` of `exists_ellipticScheme_of_weierstrass`, which is not known to
determine `E.j`, so the universal form risks being FALSE.  The
existential form is what `classify_jm` consumes, is true of the genuine
`j`-map (take `d` built from `E` itself), and cannot be contradictory
whatever that relation turns out to pin.  `N` and `hN` are quantified
INSIDE the field rather than being parameters of the structure precisely
so that one witness serves all levels; `hN : N ≠ 0` is needed only to
form `d.ofDvd`.

**Why this is not a repackaging of `exists_jMap`.**  `jt` is asked for
over EVERY `ℚ`-scheme `T`, and lands in a FIXED scheme — the honest
`j`-line — whereas `IsJMapOn.jm` is a bare function on the rational
points of one `Y`.  Recovering `jt` from `jm` would require inverting the
universal property, which initiality does not provide.  See `jLineVal`
for why the fixed target is what makes the difference. -/
structure IsJLine where
  /-- the `j`-invariant of an elliptic scheme, as a point of the `j`-line -/
  jt : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), Gamma0Datum 1 T → RelPoint jLineStr g
  /-- `j` is natural: a base change of data is sent to the precomposed point -/
  jt_natural : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {d' : Gamma0Datum 1 T'} {d : Gamma0Datum 1 T},
    IsBaseChangeOf h d' d → jt g' d' = RelPoint.pre h hg (jt g d)
  /-- `j` agrees with `WeierstrassCurve.j`: every Weierstrass curve over `ℚ`
  carrying a Galois-stable cyclic subgroup of order `N` admits a
  `Γ₀(N)`-datum whose underlying elliptic scheme has `j`-invariant `E.j` -/
  jt_weierstrass : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) (hN : N ≠ 0)
      (g : (E⁄(AlgebraicClosure ℚ)).Point), addOrderOf g = N →
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) →
      ∃ d : Gamma0Datum N SpecQ,
        jLineVal (jt (𝟙 SpecQ) (d.ofDvd hN (one_dvd N))) = E.j

/-! #### The cut of `exists_jLine`: the `j`-theory and the Weierstrass model

`exists_jLine` was recorded IRREDUCIBLE on 2026-07-27, and the verdict
was retired the same day.  What the audit established is correct and is
kept below verbatim in `exists_jSection`: the `j`-invariant of an
elliptic scheme does not exist at this pin, in mathlib or in `~/cs/FLT`
or here.  What it did **not** establish is that the LEAF is irreducible,
and the axis it did not search is the one that matters.

**Which axis was searched, and which was not.**  The audit searched the
axis of *presentations of elliptic schemes* — is there machinery
attaching `c₄, Δ` to an `AbelianSchemeStruct`?  There is not.  It did not
search the axis along which `exists_jLine` actually splits, which is the
split between

* the `j`-invariant AS A NATURAL TRANSFORMATION, defined for every
  elliptic scheme over every base and pinned by agreement with
  `WeierstrassCurve.j` on Weierstrass models — `exists_jSection`; and
* the existence over `ℚ` of a `Γ₀(N)`-datum whose elliptic scheme IS the
  Weierstrass model of a given `E` — `exists_weierstrassModel_gamma0Datum`.

The second is not a `j`-statement at all.  It is the projective
Weierstrass construction, which is *already* an owned, in-flight item:
it is exactly what `exists_ellipticScheme_of_weierstrass` is blocked on
(its ITEM 1, the graded quotient ring needed to form `Proj`), recorded
there in detail.  So the cut moves one of the two halves of this leaf
onto work that is already being done, and leaves behind a leaf that is
purely the moduli-theoretic `j`-theory.

**Why the pinning is by MODELS and not by the Galois-module relation.**
`nonempty_gamma0Datum_of_stable` does supply a datum built from `E`, but
it is pinned to `E` only through the Galois-equivariant `≃+` of
`exists_ellipticScheme_of_weierstrass`, which — as the docstring at
`IsJMapOn.classify_jm` records — is not known to determine `E.j`.  Using
it here would make `jt_model` risk being FALSE.  `IsWeierstrassModel`
pins the scheme by COORDINATES instead, and that determines `j`: see its
own docstring.

**What is still missing after the cut**, and it is the honest residue:
Zariski-local Weierstrass presentations of an elliptic scheme, the
independence of `j` from the presentation, and gluing.  Two of the three
ingredients for the middle step are already in the pin —
`WeierstrassCurve.variableChange_j`
(`Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean:246`,
`(C • W).j = W.j`) and `WeierstrassCurve.map_j`
(`Weierstrass.lean:470`, `(W.map f).j = f W.j`, which is naturality of
`j` under base change) — so the missing piece there is only "two models
of one elliptic scheme differ by a variable change", not the invariance
itself. -/

/-- **The affine Weierstrass curve `Spec R[W]` as a scheme.**

`WeierstrassCurve.Affine.CoordinateRing` is mathlib's `R[X,Y]/(W)`; its
spectrum is the affine Weierstrass curve, which is the projective one
with the point at infinity removed.  That last sentence is the whole
content of `IsWeierstrassModel` below. -/
noncomputable def weierstrassAffine {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    Scheme.{0} :=
  Spec (CommRingCat.of W.toAffine.CoordinateRing)

/-- **The structure morphism of the affine Weierstrass curve**, `Spec` of
`R → R[W]`. -/
noncomputable def weierstrassAffineStr {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    weierstrassAffine W ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing))

/-- **`W` is a Weierstrass model of the elliptic scheme carrying `ab`**:
the complement of the zero section is the affine Weierstrass curve of
`W`, as a scheme over the base.

This is the coordinate-level pinning that the moduli-level `≃+` of
`exists_ellipticScheme_of_weierstrass` cannot provide, and it is stated
in the only form available at this pin — an OPEN IMMERSION of
`Spec R[W]` whose set-theoretic range is the complement of the range of
the zero section — because `Proj` of a graded quotient ring, and hence
the projective Weierstrass scheme itself, cannot yet be formed.

**Why this determines `j`, which is what keeps `IsJSection.jt_model`
from being false.**  Over a field the smooth projective completion of an
integral affine curve is unique, and it adds exactly the missing points.
So if `W` and `W'` are both models of one `ab`, the two open immersions
identify `Spec K[W] ≅ A ∖ {O} ≅ Spec K[W']`, hence identify the
completions carrying the single point at infinity of each to the other,
i.e. give an isomorphism of the two Weierstrass curves matching their
origins.  Such an isomorphism is a `VariableChange`, and
`WeierstrassCurve.variableChange_j` then gives `W.j = W'.j`.  Note the
`range_eq` field is what forces the removed point to BE the origin; the
weaker "some open immersion" would still determine `j` (by translation)
but only after an argument, so the stronger form is stated.

**`W` is not required to be elliptic here.**  It cannot be: `Δ` is
invertible automatically, since a singular `Spec R[W]` cannot be an open
subscheme of the smooth `A`.  Consumers that need `W.j` supply
`[W.IsElliptic]` themselves. -/
def IsWeierstrassModel {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (ab : AbelianSchemeStruct f)
    (W : WeierstrassCurve R) : Prop :=
  ∃ ι : weierstrassAffine W ⟶ A, IsOpenImmersion ι ∧
    ι ≫ f = weierstrassAffineStr W ∧
    Set.range ι.base = (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of R)))).1.base)ᶜ

/-- **The `j`-invariant of an elliptic scheme, pinned by Weierstrass
models rather than by a chosen datum.**

The first two fields are those of `IsJLine` verbatim — the natural
transformation and its naturality.  The third replaces `IsJLine`'s
existential `jt_weierstrass` by the statement that actually says "`jt`
IS the `j`-invariant": wherever the elliptic scheme has a Weierstrass
model `W`, the value is `W.j`.

**Why the universal form is safe here where it was not at
`jt_weierstrass`.**  The subsection docstring at `IsJMapOn.classify_jm`
warns against quantifying over every datum "modelling `E`", because the
only modelling relation available there is a Galois-equivariant `≃+`
that is not known to determine `E.j` — so the `∀` form risks being
false.  `IsWeierstrassModel` is a different relation: it pins the scheme
by coordinates and DOES determine `j` (see its docstring).  So here the
`∀` form is the correct one, and it is what makes this field usable
without knowing which datum a producer will hand over.

**This is strictly weaker than `IsJLine` in the direction that matters
for cutting**: it says nothing about which elliptic schemes over `ℚ`
exist.  That half is `exists_weierstrassModel_gamma0Datum`. -/
structure IsJSection where
  /-- the `j`-invariant of an elliptic scheme, as a point of the `j`-line -/
  jt : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), Gamma0Datum 1 T → RelPoint jLineStr g
  /-- `j` is natural: a base change of data is sent to the precomposed point -/
  jt_natural : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {d' : Gamma0Datum 1 T'} {d : Gamma0Datum 1 T},
    IsBaseChangeOf h d' d → jt g' d' = RelPoint.pre h hg (jt g d)
  /-- `j` agrees with `WeierstrassCurve.j` on every Weierstrass model -/
  jt_model : ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic] (d : Gamma0Datum 1 SpecQ),
    IsWeierstrassModel d.ab W → jLineVal (jt (𝟙 SpecQ) d) = W.j

/-- **Existence of the `j`-invariant of an elliptic scheme** (sorry node).

TRUE and classical — this is `Y_0(1) ≅ 𝔸¹_j`, Deligne–Rapoport VI, or
Silverman *AEC* III.1 plus descent.

WHAT IT NEEDS.  A Weierstrass presentation of an elliptic scheme
`f : E ⟶ T` Zariski-locally on `T`, so that `c₄³/Δ` glues to a global
function; equivalently, the line bundle `ω = f_* Ω¹_{E/T}` and the
classical formulas for `c₄, c₆, Δ` as sections of its powers.  None of
that exists at this pin: `AbelianSchemeStruct` is a functor-of-points
presentation with no coordinates anywhere, and mathlib's
`WeierstrassCurve.j` is defined only for a Weierstrass EQUATION over a
ring, not for a scheme.  Searched 2026-07-27 over `Fermat/`,
`.lake/packages/mathlib` and `~/cs/FLT`: mathlib has NO file mentioning
an elliptic scheme at all, `~/cs/FLT` has no `jInvariant`, and the only
`j` anywhere is `WeierstrassCurve.j`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:385`).

THE AXIS THIS VERDICT RANGES OVER, stated so the next reader can see what
it does not cover: presentations of elliptic schemes.  It does NOT cover
the split between the `j`-theory and the existence of models over `ℚ`;
that split is the cut recorded in the subsection docstring above, and it
is what removed `exists_weierstrassModel_gamma0Datum` from this node.

THE CHECK THAT WOULD REFUTE THIS.  Any construction attaching a global
section of `𝒪_T` to an `AbelianSchemeStruct` of relative dimension `1`,
natural in `T`; equivalently, a `grep` for a Weierstrass presentation of
`AbelianSchemeStruct` or for `ω`/`c₄`/`Δ` on a relative curve.

THE FURTHER CUT, when someone attacks this.  Three steps, of which the
middle one is nearly free at this pin: (i) Zariski-locally on `T` an
elliptic scheme is a Weierstrass model; (ii) two models of one elliptic
scheme differ by a `VariableChange`, so `WeierstrassCurve.variableChange_j`
makes the local `j`'s agree on overlaps, and `WeierstrassCurve.map_j`
makes them compatible with base change; (iii) the local sections glue.
Only (i) and the variable-change half of (ii) are genuinely missing.

NOT VACUOUS, and not satisfiable by junk.  Two independent reasons.
First, `jLineVal` is the honest coordinate (see its docstring), so the
value condition has content.  Second — and this is the sharper one — a
`jt` whose value is a CONSTANT section cannot satisfy `jt_model`: pull a
model back along the fibres of any nonisotrivial family and naturality
forces every fibre to take the same value, while `jt_model` demands the
fibre's own `j`.  So `jt` must genuinely vary. -/
theorem exists_jSection : Nonempty IsJSection :=
  sorry

/-- **Existence of a `Γ₀(N)`-datum over `ℚ` with a prescribed Weierstrass
model** (sorry node).

TRUE: take the projective Weierstrass curve of `E`, whose complement of
the point at infinity is `Spec ℚ[E]` by construction, with the subgroup
scheme generated by `g` — which descends to `ℚ` precisely because
`hstable` says the Galois action preserves `⟨g⟩`.

This is the SAME missing construction as
`exists_ellipticScheme_of_weierstrass`, not a new one: both need the
projective Weierstrass scheme, i.e. that theorem's ITEM 1, the grading on
a graded quotient ring needed to form `Proj`, recorded there as in flight
and unreleased.  The difference is only in what is remembered about the
result — that theorem remembers a Galois-equivariant `≃+` on geometric
points, this one remembers the coordinates.  **Whoever closes one should
close both**, and the datum's level structure is exactly the one
`nonempty_gamma0Datum_of_stable` already builds.

The hypotheses are load-bearing and are the same three as everywhere else
in this file: without a Galois-stable cyclic subgroup of order `N` there
is no `Γ₀(N)`-structure on `E` over `ℚ` at all, so the statement would be
false.  They are underscore-prefixed only because the sorry does not
consume them. -/
theorem exists_weierstrassModel_gamma0Datum (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (N : ℕ) (_hN : N ≠ 0) (g : (E⁄(AlgebraicClosure ℚ)).Point) (_hg : addOrderOf g = N)
    (_hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g) :
    ∃ d : Gamma0Datum N SpecQ, IsWeierstrassModel d.ab E :=
  sorry

/-- **Existence of the `j`-invariant of an elliptic scheme, in the form
`exists_jMap` consumes it** (PROVEN 2026-07-27, over `exists_jSection`
and `exists_weierstrassModel_gamma0Datum`).

The proof is the whole content of the cut and is three lines: the first
two fields of `IsJLine` are the first two fields of `IsJSection`
verbatim, and `jt_weierstrass` is `jt_model` applied to the datum that
`exists_weierstrassModel_gamma0Datum` produces.  `Gamma0Datum.ofDvd`
leaves the elliptic scheme, its structure morphism and its
`AbelianSchemeStruct` untouched, so the model hypothesis transports
across `ofDvd` definitionally and no transport lemma is needed. -/
theorem exists_jLine : Nonempty IsJLine := by
  obtain ⟨js⟩ := exists_jSection
  refine ⟨{ jt := js.jt, jt_natural := js.jt_natural, jt_weierstrass := ?_ }⟩
  intro E _ N hN g hg hstable
  obtain ⟨d, hd⟩ := exists_weierstrassModel_gamma0Datum E N hN g hg hstable
  exact ⟨d, js.jt_model E (d.ofDvd hN (one_dvd N)) hd⟩

/-- **Existence of the `j`-map on `Y_0(N)`** (PROVEN 2026-07-27, over
`exists_jLine`).

The proof is the universal property and the degeneracy map, and nothing
else.  `d ↦ jt (d.ofDvd hN (one_dvd N))` is a natural transformation from
the `Γ₀(N)`-problem to the points of the `j`-line — naturality is
`IsJLine.jt_natural` applied to `IsBaseChangeOf.ofDvd` — so `hc.universal`
yields `u : Y ⟶ 𝔸¹_ℚ` over `ℚ` with `(jt g (d.ofDvd …)).1 =
(hc.classify g d).1 ≫ u`.  Then `jm y := jLineVal (y.1 ≫ u)`, and
`classify_jm` is `IsJLine.jt_weierstrass` transported across that
equation by `Subtype.ext`.

`hN : N ≠ 0` is REQUIRED, not decoration: see the subsection docstring —
`IsJMapOn 0 hc` is unsatisfiable, so this statement is FALSE without it.
It is now also USED, twice, by `Gamma0Datum.ofDvd` — the hypothesis was
load-bearing before it was consumed, and is now load-bearing visibly. -/
theorem exists_jMap (N : ℕ) (hN : N ≠ 0) {Y : Scheme.{0}} {strY : Y ⟶ SpecQ}
    (hc : IsCoarseModuliY0 N strY) : Nonempty (IsJMapOn N hc) := by
  obtain ⟨jl⟩ := exists_jLine
  obtain ⟨u, ⟨hu, hu2⟩, -⟩ :=
    hc.universal jLineStr (fun g d => jl.jt g (d.ofDvd hN (one_dvd N)))
      (by intro _ _ h _ _ hg _ _ hb; exact jl.jt_natural h hg (hb.ofDvd hN (one_dvd N)))
  refine ⟨{ jm := fun y => jLineVal ⟨y.1 ≫ u, by rw [Category.assoc, hu, y.2]⟩
            classify_jm := ?_ }⟩
  intro E _ g hg hstable
  obtain ⟨d, hd⟩ := jl.jt_weierstrass E N hN g hg hstable
  refine ⟨d, Eq.trans ?_ hd⟩
  congr 1
  exact Subtype.ext (hu2 (𝟙 SpecQ) d).symm

/- `exists_x0JReductionAt` used to stand here.  It has MOVED to the
subsection `#### The Néron pinning of the `j`-map` at the end of this
file, where it is **PROVEN** from `exists_x0JNeronDatum`; it now consumes
`SpecLoc`, which is declared below this point, so it cannot live here.
See the POST-SCRIPT in the docstring of `IsX0JReductionAt` above. -/

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
`ℚ`** (PROVEN, over `exists_coarseModuliY0` and one modular leaf;
formerly a sorry node).

TRUE and classical: `Y_0(N)` is a smooth affine curve over `ℚ` and every
smooth curve over a field has a unique smooth projective
compactification; for `Y_0(N)` it is the modular curve `X_0(N)` of
Deligne–Rapoport, obtained directly as the coarse space of the moduli
problem of GENERALISED elliptic curves with `Γ₀(N)`-structure, the added
points being the cusps.

This node SUBSUMES `exists_coarseModuliY0` — its `coarse` field is
exactly that statement — and that half is now PROVEN, so the proof below
simply obtains the coarse space and compactifies it.  What remains open
is split cleanly in two, and neither half is modular-curve-specific
except the first:

* `isSmoothCurve_of_isCoarseModuliY0` supplies the four properties of
  `Y_0(N)` that the compactification theorem consumes, plus geometric
  connectedness;
* `AlgebraicGeometry.exists_isSmoothCompactification` and
  `AlgebraicGeometry.geometricallyConnected_of_isSmoothCompactification`
  supply the compactification itself, from
  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`.

Note `connected` and `finite_compl` — the two clauses beyond
`IsCompactificationY0` — come from the general theory and not from
anything modular: geometric connectedness is inherited from `Y_0(N)`
along a dense open immersion, and finiteness of the cusp locus is
finiteness of the complement of a dense open in an irreducible curve.
Neither is assumed here, which is what keeps the interface from
smuggling in a cusp count; see `exists_rationalCusps` for the count
itself, which is a genuinely separate and still-open statement. -/
theorem exists_x0Compactification (N : ℕ) (hN : 0 < N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecQ) (strY : Y ⟶ SpecQ) (j : Y ⟶ X),
      Nonempty (IsX0Compactification N strX strY j) := by
  obtain ⟨Y, strY, ⟨hc⟩⟩ := exists_coarseModuliY0 N
  obtain ⟨hint, hqc, hsep, hsmd, hconn⟩ := isSmoothCurve_of_isCoarseModuliY0 hN hc
  haveI := hint; haveI := hqc; haveI := hsep; haveI := hsmd; haveI := hconn
  obtain ⟨X, strX, j, hX⟩ := exists_isSmoothCompactification (K := ℚ) strY
  exact ⟨X, Y, strX, strY, j,
    ⟨{ comm := hX.comm
       coarse := hc
       isOpen := hX.isOpenImmersion
       isProper := hX.isProper
       smooth := hX.smooth
       connected := geometricallyConnected_of_isSmoothCompactification hX
       finite_compl := hX.finite_compl }⟩⟩

/-- **The `ℚ`-rational cusps of `X_0(N)`, INDEXED by the divisors that
carry one.**

The cusps of `X_0(N)` are indexed by pairs `(d, a)` with `d ∣ N` and
`a ∈ (ℤ/gcd(d, N/d))ˣ`, and `Γ_ℚ` permutes the `φ(gcd(d, N/d))` cusps
above a fixed `d` transitively through the cyclotomic character; so the
cusps above `d` are `ℚ`-rational exactly when `d ∈ rationalCuspDivisors
N`.  This structure carries that indexing.

Presented as a family of POINTS rather than as a cusp subscheme, for the
same reason `IsX0ReductionAt` presents reduction as a bare function and
`IsJMapOn` presents the `j`-map as a function on rational points: the
integral/moduli-theoretic object that would produce the cusps as a closed
subscheme does not exist at this pin, and every consumer here evaluates
at rational points anyway.

**Only an INJECTION is asked for, and that is the whole point of this
cut.**  `exists_rationalCusps` needs *a* `Finset` of rational cusps of
size exactly `numRationalCusps N`; it does NOT need that these are ALL
the rational cusps, because a larger supply could simply be cut down
(`Finset.exists_subset_card_eq`).  So the hard half of Ogg's description
— that the Galois action on the cusps above `d` is *exactly* the
cyclotomic one, hence that no cusp with `φ(gcd(d, N/d)) > 1` is rational
— is **not** an obligation of this development.  A prover of
`nonempty_cuspIndexing` needs only the easy direction: for `d` with
`φ(gcd(d, N/d)) = 1` the unique cusp above `d` is `Γ_ℚ`-fixed, and cusps
over distinct `d` are distinct.  That is a strictly smaller theorem than
the cusp classification, and the previous "IRREDUCIBLE" note on
`exists_rationalCusps` did not distinguish the two.

Stated over `Spec ℚ` rather than over the general base of
`IsX0Compactification`, deliberately: the count is base-dependent, and
over `Spec 𝔽_ℓ` the residue fields of the cusps change, so
`rationalCuspDivisors N` would be the wrong index set. -/
structure IsX0Compactification.CuspIndexing {N : ℕ} {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) where
  /-- the `ℚ`-rational cusp of `X_0(N)` lying above the divisor `d` -/
  cusp : ∀ d ∈ rationalCuspDivisors N, RelPoint strX (𝟙 SpecQ)
  /-- it really is a cusp: it is not the image of a rational point of `Y_0(N)` -/
  isCusp : ∀ (d : ℕ) (hd : d ∈ rationalCuspDivisors N), h.IsCusp (cusp d hd)
  /-- cusps above distinct divisors are distinct -/
  inj : ∀ (d : ℕ) (hd : d ∈ rationalCuspDivisors N) (d' : ℕ)
    (hd' : d' ∈ rationalCuspDivisors N), cusp d hd = cusp d' hd' → d = d'

/-- **`X_0(N)` has a `ℚ`-rational cusp above every divisor `d ∣ N` with
`φ(gcd(d, N/d)) = 1`, and these are pairwise distinct** (sorry node).

TRUE and classical (Ogg; Deligne–Rapoport VI.6, or Diamond–Im §9.3): the
cusps of `X_0(N)` over `ℚ̄` are `Γ_0(N)\ℙ¹(ℚ)`, the cusp `a/d` with
`gcd(a, d) = 1` and `d ∣ N` depends only on `d` and on `a mod gcd(d,
N/d)`, and `σ_t ∈ Gal(ℚ(ζ_n)/ℚ)` sends the class of `a` to the class of
`t⁻¹ a`.  When `φ(gcd(d, N/d)) = 1` that action is trivial, so the cusp
is `ℚ`-rational; and cusps above distinct `d` are distinct because `d`
is a `Γ_0(N)`-invariant of the cusp.

WHAT REMAINS, precisely.  See `IsX0Compactification.CuspIndexing` for
why only the *easy* direction of the classification is needed here.  The
missing input is the identification of `X ∖ Y` with `Γ_0(N)\ℙ¹(ℚ)`
compatibly with the `Γ_ℚ`-action, which is the cuspidal part of the
Deligne–Rapoport model.  `IsX0Compactification` supplies only that the
complement is finite, so nothing weaker than that identification can
produce a single cusp: note that the structure's fields do not by
themselves forbid `j` from being an isomorphism (with no cusps at all) —
that is excluded only because `coarse` pins `Y` as the affine curve
`Y_0(N)`, which is moduli input, not scheme-theoretic bookkeeping.

AXES SEARCHED (2026-07-27, second pass), each with the check that would
refute it.  The first pass searched two and left one open; the open one
is now CLOSED, negatively, and two more are added.

1. *The count* — weakening `=` to `≤`.  Does not help: the difficulty is
   producing cusps, not bounding them.

2. *The index set* — this cut.  Exhausted: `CuspIndexing` and
   `exists_rationalCusps` are interderivable (the proof below is one
   direction, `Finset.exists_subset_card_eq` the other), so moving the
   index set around cannot make either side smaller.

3. *The `j`-map dictionary* — the axis the first pass left open.  The
   route characterises a cusp as a pole of `jm`, which needs `jm`
   extended to `X`.  **That extension is free, and useless for the same
   reason.**  Write the obvious interface

       jmX : RelPoint strX (𝟙 SpecQ) → OnePoint ℚ
       jmX_section : ∀ y, jmX (sectionAlong j h.comm y) = (hj.jm y : OnePoint ℚ)
       isCusp_iff  : ∀ x, h.IsCusp x ↔ jmX x = ∞

   and it is inhabited for EVERY `h`, unconditionally, by
   `jmX x := if hx : ∃ y, sectionAlong j h.comm y = x then hj.jm hx.choose
   else ∞`.  `j` is an open immersion, hence a monomorphism, so
   `sectionAlong` is injective and `jmX_section` holds; `isCusp_iff` is
   then `(q : OnePoint ℚ) ≠ ∞` against the definition of `IsCusp`.  So the
   extended `j`-map is DEFINABLE FROM `IsCusp` and carries no information
   about it — it has a model with no rational cusp at all, hence cannot
   prove this leaf.  The general objection, which kills the whole axis:
   every field of `IsJMapOn` and `IsX0JReductionAt` is a function OUT of a
   point set plus equations between values, so such a datum can only
   RECOGNISE points that already exist, and this leaf asks for points to
   EXIST.  Refuted by a `j`-map field not of that shape — e.g. a section
   of the extended map over `∞`.

4. *An invariant-first cut* — peel off the `Γ_0(N)`-divisor invariant
   `dinv` of a cusp as one leaf and "for each `d` some cusp has invariant
   `d`" as another, making `inj` free.  UNSAFE, for exactly the reason the
   FORMAL-CONTENT AUDIT at `IsX0JReductionAt` records for `redX`:
   quantified over an arbitrary `dinv` the existence half is FALSE — take
   `dinv ≡ 1`, and no cusp has invariant `d ≠ 1`.  Pinning `dinv` is the
   Deligne–Rapoport input again, so the halves do not separate; that is
   why `CuspIndexing` bundles them.  Refuted by a pinning of `dinv` that
   does not already produce the cusps.

5. *Level induction / degeneracy* — get cusps of `X_0(N)` from `X_0(N')`
   for `N' ∣ N`.  Wrong direction: the degeneracy map `X_0(N) ⟶ X_0(N')`
   pushes points forward and this leaf needs them pulled back.

CORRECTION to the first pass's refuting check (2026-07-27).  It claimed
`grep` over `Fermat/`, `.lake/packages/mathlib/` and `~/cs/FLT/` finds
neither a modular-curve cusp theory nor a `Γ_0(N)\ℙ¹(ℚ)` description "in
any form".  **The first half is wrong.**  This pin carries
`Mathlib/NumberTheory/ModularForms/Cusps.lean`, which defines `IsCusp c 𝒢`
for `c : OnePoint ℝ`, proves the cusps of `SL(2, ℤ)` are exactly `ℙ¹(ℚ)`
(`isCusp_SL2Z_iff`), and builds `CuspOrbits 𝒢` — literally `Γ∖ℙ¹(ℚ)` —
with `Finite (CuspOrbits 𝒢)` for arithmetic `𝒢`, plus cusp widths.
`CongruenceSubgroup.Gamma0 N` has finite index in `SL(2, ℤ)`, so
`CuspOrbits (Gamma0 N)` is available and finite.

Why the leaf survives that.  Those cusps are points of `OnePoint ℝ` with a
group action: no Galois action, no `(d, a)` classification, no count, and
— decisively — no relation of any kind to `RelPoint strX (𝟙 SpecQ)`.
Bridging the two is the uniformisation `X_0(N)(ℂ) ≅ Γ_0(N)∖ℍ*` together
with the `ℚ`-structure, i.e. Deligne–Rapoport again.  `grep` over the same
three trees for Galois descent of scheme points (`X(K^sep)^Γ = X(K)`)
finds nothing — `Mathlib/CategoryTheory/Galois/` is the
Galois-category/fundamental-group theory, not this.  So the refuting check
is re-stated: this note falls to a bridge from `CuspOrbits (Gamma0 N)` to
`RelPoint strX (𝟙 SpecQ)`, or to Galois descent for rational points of a
`ℚ`-scheme.

`_hN : N ≠ 0` is NOT load-bearing for truth — at `N = 0` the statement is
true and vacuous, and `nonempty_cuspIndexing` discharges that case
outright.  It is carried because every construction of a cusp needs it
(`Nat.divisors 0 = ∅`, so there is nothing to index at `N = 0`), and
because `N = 0` is a recurring trap in this module — see `exists_jMap`,
where the same hypothesis IS load-bearing. -/
theorem nonempty_cuspIndexing_of_ne_zero (N : ℕ) (_hN : N ≠ 0) {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) :
    Nonempty h.CuspIndexing :=
  sorry

/-- **`X_0(N)` has a `ℚ`-rational cusp above every divisor `d ∣ N` with
`φ(gcd(d, N/d)) = 1`, and these are pairwise distinct** (PROVEN at
`N = 0`, otherwise `nonempty_cuspIndexing_of_ne_zero`).

The degenerate level is discharged here rather than left inside the leaf:
`Nat.divisors 0 = ∅`, so `rationalCuspDivisors 0 = ∅` and every field of
`CuspIndexing` is vacuous.  Splitting it off follows the module's own
idiom — `exists_coarseModuliY0_zero` against
`exists_coarseModuliY0_of_pos` — and it matters here for the same reason
it matters there: `N = 0` satisfies the hypotheses of several statements
in this file while admitting none of their intended objects, so a leaf
that silently includes it invites a prover to look for a cusp that is not
being asked for.

All the modular content is in `nonempty_cuspIndexing_of_ne_zero`; see its
docstring for the five axes searched and for the correction to the pin
survey. -/
theorem nonempty_cuspIndexing (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {j : Y ⟶ X} (h : IsX0Compactification N strX strY j) :
    Nonempty h.CuspIndexing := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hz : ∀ d : ℕ, d ∉ rationalCuspDivisors 0 := fun d => by
      simp only [rationalCuspDivisors, Nat.divisors_zero, Finset.filter_empty,
        Finset.notMem_empty, not_false_eq_true]
    exact ⟨{ cusp := fun d hd => absurd hd (hz d)
             isCusp := fun d hd => absurd hd (hz d)
             inj := fun d hd _ _ _ => absurd hd (hz d) }⟩
  · exact nonempty_cuspIndexing_of_ne_zero N hN h

/-- **`X_0(N)` has `numRationalCusps N` rational cusps, and no cusp is
the image of a rational point of `Y_0(N)`** (PROVEN 2026-07-27 over
`nonempty_cuspIndexing`).

TRUE and classical; see `numRationalCusps` for the divisor count and the
Galois action on the cusps.  The second conjunct is immediate from the
definition of a cusp — it lies in `X ∖ Y` — but it is exactly what the
emptiness argument consumes, so it is stated rather than left implicit.

Quantified over every compactification rather than over a chosen one:
`IsX0Compactification` pins `(X, Y, j)` up to isomorphism so the
statement is invariant, and `exists_x0Compactification` supplies an
instance so it is not vacuous.

The proof is the bookkeeping that turns the INDEXED cusp family of
`IsX0Compactification.CuspIndexing` into an unindexed `Finset` of the
right size: take the image of `(rationalCuspDivisors N).attach`, which is
injective by `CuspIndexing.inj`, so its card is
`(rationalCuspDivisors N).card = numRationalCusps N`.  All the modular
content sits in `nonempty_cuspIndexing`. -/
theorem exists_rationalCusps (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {j : Y ⟶ X} (h : IsX0Compactification N strX strY j) :
    ∃ s : Finset (RelPoint strX (𝟙 SpecQ)), s.card = numRationalCusps N ∧
      ∀ p ∈ s, ∀ y : RelPoint strY (𝟙 SpecQ), sectionAlong j h.comm y ≠ p := by
  classical
  obtain ⟨C⟩ := nonempty_cuspIndexing N h
  have hinj : Function.Injective
      (fun d : {x // x ∈ rationalCuspDivisors N} => C.cusp d.1 d.2) := by
    rintro ⟨d, hd⟩ ⟨d', hd'⟩ heq
    exact Subtype.ext (C.inj d hd d' hd' heq)
  refine ⟨(rationalCuspDivisors N).attach.image (fun d => C.cusp d.1 d.2), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_attach,
      numRationalCusps_eq_card]
  · intro p hp y
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hp
    exact fun hy => C.isCusp d.1 d.2 ⟨y, hy⟩

/-- **The number of cusps of `X_0(N)`**, `ν_∞ = Σ_{d ∣ N} φ(gcd(d, N/d))`.

The sibling of `numRationalCusps`, which counts only those cusps that
are individually `ℚ`-rational.  The two genuinely differ: `X_0(36)` has
`12` cusps but only `6` rational ones, and `X_0(50)` has `12` and `4`.

This is the `ν_∞` of the classical genus formula (Diamond–Shurman,
Theorem 3.1.1), and it is `ν_∞`, not `numRationalCusps`, that enters
`x0Genus`. -/
def numCusps (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d))

/-- **The index `μ(N) = [SL₂(ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1/p)`.**

Written as `(N / rad N) * ∏_{p ∣ N} (p + 1)` so that the only `ℕ`
division is by `rad N = ∏_{p ∣ N} p`, which always divides `N`; the
product is over `N.divisors.filter Nat.Prime`, which is exactly the set
of primes dividing `N` for `N ≠ 0`. -/
def gammaZeroIndex (N : ℕ) : ℕ :=
  (N / (N.divisors.filter Nat.Prime).prod id) * (N.divisors.filter Nat.Prime).prod (· + 1)

/-- **The number `ν₂(N)` of elliptic points of order `2` on `X_0(N)`**,
counted as `#{x ∈ ℤ/N : x² + 1 ≡ 0}`.

This counting form is chosen because it needs NO case split.  The usual
statement — `ν₂ = 0` if `4 ∣ N`, and `∏_{p ∣ N} (1 + (−1/p))` otherwise
— is precisely the CRT evaluation of this count, and both of its special
cases are automatic here: `x² + 1 ≡ 0` is insoluble mod `4`, and
insoluble mod every `p ≡ 3 (mod 4)`.

That is not a cosmetic preference.  The `p = 2` value of the character
is `0`, not `(−1/2)`; evaluating the product form with a Kronecker
symbol at `p = 2` gives `ν₂(50) = 4` instead of `2` and so genus `3/2`
instead of `2`.  The counting form cannot make that mistake. -/
def numEllipticTwo (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun x => (x * x + 1) % N = 0).card

/-- **The number `ν₃(N)` of elliptic points of order `3` on `X_0(N)`**,
counted as `#{x ∈ ℤ/N : x² + x + 1 ≡ 0}`; see `numEllipticTwo` for why
the counting form absorbs the `9 ∣ N` case split (`x² + x + 1 ≡ 0` is
insoluble mod `9`) and the `p = 3` value of the character. -/
def numEllipticThree (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun x => (x * x + x + 1) % N = 0).card

/-- **The genus of `X_0(N)`, by the classical formula**

`g = 1 + μ/12 − ν₂/4 − ν₃/3 − ν_∞/2`

(Diamond–Shurman, Theorem 3.1.1), cleared of denominators and divided
back: the numerator `12 + μ − 3ν₂ − 4ν₃ − 6ν_∞` is always divisible by
`12`, so the `ℤ`-division is exact at every `N` where it is used.

**What this is and is not.**  `x0Genus` is a purely arithmetic,
fully computable function of `N` — it is evaluated by `decide` in
`one_le_x0Genus_of_kenkuLevel`, giving `1, 1, 2, 3, 1, 5, 3, 2, 4, 5, 5`
in the order of `kenkuLevels`.  It is NOT defined as the genus of the
scheme `X`: no genus of a scheme, and no Riemann–Roch, exists at this
pin.  The bridge from this number to the geometry of `X` is
`injective_aj_of_one_le_x0Genus`, and that is a sorry node. -/
def x0Genus (N : ℕ) : ℤ :=
  (12 + (gammaZeroIndex N : ℤ) - 3 * numEllipticTwo N - 4 * numEllipticThree N
    - 6 * numCusps N) / 12

/-- **`genus X_0(N) ≥ 1` at the eleven Kenku levels** (PROVEN).

This is the arithmetic half of `hasRankZeroJacobian_of_kenkuLevel`, and
it is proven rather than asserted: `decide` evaluates `x0Genus` — index,
elliptic points and cusps and all — at each of the eleven levels.  The
values are

`N  : 20 24 28 30 36 42 45 50 54 63 75`
`g  :  1  1  2  3  1  5  3  2  4  5  5`

matching the table in `kenkuLevels`, and independently reproduced with
PARI/GP.  Genus `0` would make the leaf below FALSE (see
`HasRankZeroJacobian`: at `N = 1` the Jacobian is trivial and
`X_0(1) = ℙ¹` has infinitely many rational points), so this is exactly
the hypothesis that rules that out. -/
theorem one_le_x0Genus_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels) : 1 ≤ x0Genus N := by
  fin_cases hN <;> decide

/-- **`X_0(N)` has at least one rational cusp, at the eleven Kenku
levels** (PROVEN, by `decide` on `numRationalCusps`, whose values are
`6, 8, 6, 8, 6, 8, 4, 4, 4, 4, 4`).

This is what supplies the BASE POINT of the Abel–Jacobi map in
`hasRankZeroJacobian_of_kenkuLevel`, so that no separate existence leaf
for a rational point on `X_0(N)` is needed: `exists_rationalCusps`
produces the finset, and this says it is not empty. -/
theorem numRationalCusps_pos_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels) :
    0 < numRationalCusps N := by
  fin_cases hN <;> decide

/-- **The Jacobian of `X_0(N)` exists** (sorry node).

TRUE and classical: `X` is a smooth proper geometrically connected curve
over `ℚ` with a rational point `o`, so its Albanese — equivalently
`Pic⁰` — is an abelian variety over `ℚ` and the Abel–Jacobi map based at
`o` is initial among maps to abelian varieties killing `o`.  That is
exactly `IsJacobianOf`.

`h` is load-bearing: without properness and smoothness there is no
abelian Albanese, and without geometric connectedness `Pic⁰` is not
connected.

IRREDUCIBLE at this pin: neither `Pic⁰` of a relative curve, nor the
Albanese, nor Riemann–Roch exists in `Mathlib`. -/
theorem exists_jacobianOf_x0 (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {j : Y ⟶ X} (h : IsX0Compactification N strX strY j)
    (o : RelPoint strX (𝟙 SpecQ)) :
    ∃ (J : Scheme.{0}) (jstr : J ⟶ SpecQ) (ab : AbelianSchemeStruct jstr),
      Nonempty (IsJacobianOf strX ab o) :=
  sorry

/-- **`rank J_0(N)(ℚ) = 0` at the eleven Kenku levels** (sorry node) —
the DEEP half of `hasRankZeroJacobian_of_kenkuLevel`.

TRUE, by the reconnaissance recorded below: decomposing the cuspidal
subspace `S_2(Γ_0(N))` into newform factors and evaluating `L(A, 1)` on
each, EVERY factor at EVERY one of the eleven levels has `L(A, 1) ≠ 0`;
so `J_0(N)` has analytic rank `0`, hence Mordell–Weil rank `0` by
Kolyvagin–Logachev, hence `J_0(N)(ℚ)` is finite.

`jac` is load-bearing and may not be dropped: the conclusion is FALSE
for an arbitrary abelian scheme over `ℚ` receiving `X` — it is true only
because `jac` pins `J` as the Jacobian of this particular curve, whose
`L`-function is the one being evaluated.

IRREDUCIBLE at this pin, and this is where the depth of the original
leaf now lives, alone: it needs `S_2(Γ_0(N))`, the Hecke algebra,
`L`-functions of modular abelian varieties, and Gross–Zagier/Kolyvagin.
Nothing else in the decomposition below depends on any of that. -/
theorem finite_jacobian_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) : Finite (RelPoint jstr (𝟙 SpecQ)) :=
  sorry

/-- **Positive genus makes Abel–Jacobi injective on rational points**
(sorry node) — the bridge from the arithmetic `x0Genus` to the geometry.

TRUE and classical, and it is the ONLY thing standing between
`one_le_x0Genus_of_kenkuLevel` (proven above, by computation) and the
`Injective` conjunct of `HasRankZeroJacobian`.  Two steps, deliberately
bundled here because neither can be stated separately at this pin:

* `x0Genus N` is the genus of `X` — the classical formula
  (Diamond–Shurman, Theorem 3.1.1).  This cannot be stated as an
  equation because there is no genus of a scheme in `Mathlib`; it is
  therefore absorbed into this leaf rather than left as a phantom.
* a smooth proper geometrically connected curve of genus `≥ 1` has
  injective Abel–Jacobi: if `aj x = aj y` with `x ≠ y` then `x − y` is
  principal, so some function has a single simple pole, giving a degree
  `1` map `X → ℙ¹`, i.e. genus `0`.  This is Riemann–Roch.

`hg` is load-bearing: at genus `0` the statement is FALSE, `X_0(1) = ℙ¹`
having trivial Jacobian and infinitely many rational points.  `N` enters
only through `hg` and `h`.

IRREDUCIBLE at this pin: Riemann–Roch for curves does not exist in
`Mathlib`. -/
theorem injective_aj_of_one_le_x0Genus (N : ℕ) (hg : 1 ≤ x0Genus N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) : Function.Injective (jac.aj (𝟙 SpecQ)) :=
  sorry

/-- **`rank J_0(N)(ℚ) = 0` and `genus X_0(N) ≥ 1` at the eleven Kenku
levels** (PROVEN, from four leaves — two of them closed here).

The original single sorry node has been split along the seam its own
statement exposes.  `HasRankZeroJacobian` is a conjunction of two
conditions on the Jacobian with wildly different costs, and they are now
separated:

* **The genus half is CLOSED.**  `one_le_x0Genus_of_kenkuLevel` proves
  `1 ≤ x0Genus N` at all eleven levels by `decide` on the classical
  genus formula, and `numRationalCusps_pos_of_kenkuLevel` likewise
  supplies the base point.  No sorry, no table lookup: the index,
  elliptic points and cusps are computed from `N`.
* **The rank half is Kolyvagin–Logachev** and stays open, alone, in
  `finite_jacobian_of_kenkuLevel`.

The two remaining geometric leaves — `exists_jacobianOf_x0` and
`injective_aj_of_one_le_x0Genus` — carry the objects `Mathlib` does not
have (Albanese/`Pic⁰`, Riemann–Roch).  Neither is level-specific: they
hold for every smooth proper geometrically connected curve, which is why
splitting them out is worth doing even though they are still open. -/
theorem hasRankZeroJacobian_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) : HasRankZeroJacobian strX := by
  obtain ⟨s, hs, -⟩ := exists_rationalCusps N h
  obtain ⟨o, -⟩ : s.Nonempty :=
    Finset.card_pos.mp (by rw [hs]; exact numRationalCusps_pos_of_kenkuLevel N hN)
  obtain ⟨J, jstr, ab, ⟨jac⟩⟩ := exists_jacobianOf_x0 N h o
  exact ⟨J, jstr, ab, o, jac, finite_jacobian_of_kenkuLevel N hN h jac,
    injective_aj_of_one_le_x0Genus N (one_le_x0Genus_of_kenkuLevel N hN) h jac⟩

/-- **Every row of `x0WitnessTable` has `0 < N`, `ℓ` prime and `ℓ ∤ N`**
(PROVEN, by `decide` over the seven rows).

The side conditions that `exists_x0Compactification_mod_prime` needs in
order to hand its three leaves a good prime.  Note `ℓ ≠ 2` is NOT among
them and is not needed: the point COUNT on the special fibre is a
statement about good reduction only.  Oddness enters one step later, in
`card_le_of_rankZeroJacobian`, where the formal group of the Jacobian
has to be torsion-free.

Verified independently with Magma (2026-07-27): every row's `ℓ` is prime
and prime to its `N`. -/
theorem x0WitnessTable_spec {N ℓ m : ℕ} (h : (N, ℓ, m) ∈ x0WitnessTable) :
    0 < N ∧ ℓ.Prime ∧ ¬ ℓ ∣ N := by
  fin_cases h <;> exact ⟨by decide, by decide, by decide⟩

/-- **`X_0(N)` exists over `𝔽_ℓ` for `ℓ ∤ N`** (sorry node — the
good-reduction half of the point count).

TRUE and classical.  `IsX0Compactification` was written with a GENERAL
base for exactly this purpose (see its docstring), and the statement
here is `exists_x0Compactification` with `Spec ℚ` replaced by
`Spec 𝔽_ℓ`: the `Γ₀(N)`-problem over `𝔽_ℓ` has a coarse space, and a
smooth affine curve over a field has a unique smooth projective
compactification.  For `ℓ ∤ N` the Deligne–Rapoport / Igusa smooth model
over `ℤ[1/N]` exhibits it as the special fibre, which is why `hℓN` is a
hypothesis; but the statement itself is about the moduli problem over
`𝔽_ℓ` and does not mention the model.

**Available for the taking: this leaf and `exists_x0Compactification`
differ only in the base**, and a single statement over an arbitrary base
field of characteristic prime to `N` would subsume both.  That merge is
not made here only because `exists_x0Compactification` is another
owner's declaration; a successor holding both should make it.

IRREDUCIBLE at this pin, for the same reason as
`exists_x0Compactification`: neither modular curves nor a
smooth-compactification theorem for curves exists anywhere in
`Mathlib`. -/
theorem exists_x0Compactification_finiteField (N ℓ : ℕ) (_hN : 0 < N) (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecF ℓ) (strY : Y ⟶ SpecF ℓ) (j : Y ⟶ X),
      Nonempty (IsX0Compactification N strX strY j) :=
  sorry

/-- **A curve proper over a finite field has finitely many rational
points** (sorry node — the finiteness half of the point count).

TRUE, and it is the one piece of this leaf that is not about modular
curves at all: `strX` is proper, hence of finite type, over
`Spec 𝔽_ℓ`; a finite-type scheme over a FINITE ring has finitely many
sections, because a section is determined by the images of finitely many
generators in a finite ring.  The only property of `IsX0Compactification`
consumed is `isProper`.

`hℓ` is `ℓ ≠ 0` rather than `ℓ.Prime` deliberately — that is the honest
minimal hypothesis, since all that is used is that `ZMod ℓ` is finite,
and `ZMod 0 = ℤ` is the only excluded case.  The hypotheses carry
underscores only because the body is `sorry`.

IRREDUCIBLE at this pin: `IsProper` here is this development's own
predicate, and there is no "finite type over a finite ring implies
finitely many points" lemma to appeal to. -/
theorem finite_relPoint_of_x0Compactification_finiteField (N ℓ : ℕ) (_hℓ : ℓ ≠ 0)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {j : Y ⟶ X}
    (_h : IsX0Compactification N strX strY j) :
    Finite (RelPoint strX (𝟙 (SpecF ℓ))) :=
  sorry

/-- **Eichler–Shimura: the special fibre has exactly `m` rational
points, at the seven witness rows** (sorry node — the arithmetic half of
the point count).

TRUE.  `#X_0(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`, and the seven `m`
of `x0WitnessTable` are that formula evaluated.  **Recomputed
independently with Magma on 2026-07-27** (`CuspForms(Gamma0(N), 2)`,
`Trace(HeckeOperator(S, ℓ))`), reproducing the banked table exactly:

| `N` | `ℓ` | genus | `Tr T_ℓ` | `ℓ + 1 − Tr T_ℓ` |
|-----|-----|-------|----------|-------------------|
| 20 | 3  | 1 | `−2` | 6 |
| 24 | 5  | 1 | `−2` | 8 |
| 28 | 5  | 2 | `0`  | 6 |
| 30 | 17 | 3 | `10` | 8 |
| 36 | 5  | 1 | `0`  | 6 |
| 42 | 11 | 5 | `4`  | 8 |
| 50 | 3  | 2 | `0`  | 4 |

**Quantified over every compactification rather than over a chosen one**,
exactly as `exists_rationalCusps` is, and safe for the same reason:
`IsX0Compactification` pins `(X, Y, j)` up to isomorphism, and
`RelPoint strX (𝟙 (SpecF ℓ))` is an isomorphism invariant, so the count
does not depend on which model is supplied.  Non-vacuity is supplied by
`exists_x0Compactification_finiteField`, so this is not a statement about
an empty class.

The good-prime side conditions are not repeated as hypotheses: they are
consequences of `htable` through `x0WitnessTable_spec`.

IRREDUCIBLE at this pin: it needs `S_2(Γ_0(N))`, the Hecke operator
`T_ℓ` and the Eichler–Shimura congruence relation, none of which exist
here. -/
theorem card_relPoint_x0_finiteField (N ℓ m : ℕ) (_htable : (N, ℓ, m) ∈ x0WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {j : Y ⟶ X}
    (_h : IsX0Compactification N strX strY j) :
    Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) = m :=
  sorry

/-- **The reduction `X_0(N)_{𝔽_ℓ}` and its Eichler–Shimura point count,
at the seven witness primes** (PROVEN, by decomposition — 2026-07-27).

TRUE: for `ℓ ∤ N` the modular curve has good reduction at `ℓ` and its
special fibre is the coarse space of the same `Γ₀(N)`-problem over
`𝔽_ℓ`; being proper over a finite field it has finitely many rational
points; and Eichler–Shimura evaluates the count as
`ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`.  The seven rows of `x0WitnessTable` are
that formula computed with Magma.

**The three sentences of that paragraph are three different theories**,
and they are now three leaves rather than one:

* `exists_x0Compactification_finiteField` — the `Γ₀(N)`-moduli problem
  has a smooth compactification over `𝔽_ℓ` (Deligne–Rapoport);
* `finite_relPoint_of_x0Compactification_finiteField` — a proper scheme
  over a finite field has finitely many rational points (no modular
  curves involved);
* `card_relPoint_x0_finiteField` — Eichler–Shimura evaluates the count
  (Hecke operators and `S_2(Γ_0(N))`).

The old docstring's verdict "IRREDUCIBLE at this pin: neither the
integral model of `X_0(N)`, nor its reduction, nor the Hecke operators
exist here" was right about the *theories* and wrong about
irreducibility, in the way this development keeps meeting: **a leaf that
needs three missing theories usually splits ALONG them.**  Note also
that no integral model appears in any of the three — the special fibre
is obtained as the coarse space of the problem over `𝔽_ℓ` directly, so
the reduction map, which is what would need the model, is never
formed. -/
theorem exists_x0Compactification_mod_prime (N ℓ m : ℕ)
    (h : (N, ℓ, m) ∈ x0WitnessTable) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecF ℓ) (strY : Y ⟶ SpecF ℓ) (j : Y ⟶ X),
      Nonempty (IsX0Compactification N strX strY j) ∧
        Finite (RelPoint strX (𝟙 (SpecF ℓ))) ∧
        Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) = m := by
  obtain ⟨hN, hℓ, hℓN⟩ := x0WitnessTable_spec h
  obtain ⟨X, Y, strX, strY, j, ⟨hX⟩⟩ :=
    exists_x0Compactification_finiteField N ℓ hN hℓ hℓN
  exact ⟨X, Y, strX, strY, j, ⟨hX⟩,
    finite_relPoint_of_x0Compactification_finiteField N ℓ hℓ.ne_zero hX,
    card_relPoint_x0_finiteField N ℓ m h hX⟩

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

section NeronEtaleRigidity

open _root_.CategoryTheory.Limits

/-- **A fibre square whose first projection is an isomorphism factors its
first leg through the second** (PROVEN).

Elementary, and it is the last step of the rigidity lemma below: once the
equalizer `E ⟶ S` of two sections has been shown to be an isomorphism, the
square `E ⟶ S`, `E ⟶ Z` exhibits `S ⟶ Z ×_S Z` as factoring through the
diagonal, which is what forces the two sections to coincide. -/
theorem exists_comp_eq_of_isIso_pullback_fst {A B C : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C)
    [IsIso (pullback.fst f g)] : ∃ u : A ⟶ B, f = u ≫ g :=
  ⟨inv (pullback.fst f g) ≫ pullback.snd f g, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]⟩

/-- **RIGIDITY: two sections of a separated, formally unramified morphism of
finite type over a CONNECTED base that agree at a point agree everywhere**
(PROVEN).

This is the whole geometric content of the `q ≠ ℓ` half of
`neronKernel_torsionFree`, isolated from the abelian scheme entirely — it is
a statement about an arbitrary morphism of schemes, and it is proven here
outright.

The argument, in the form the compiler checks it.  Let `s t : S ⟶ Z` be
sections of `p` and let `e := (s, t) : S ⟶ Z ×_S Z`.  Their equalizer is the
fibre square `E := S ×_{Z ×_S Z} Z` formed along the DIAGONAL `Δ` of `p`, and
`E ⟶ S` is a base change of `Δ`.  Now `Δ` is:

* an OPEN immersion, because `p` is formally unramified and locally of finite
  type — mathlib's `FormallyUnramified.isOpenImmersion_diagonal`; and
* a CLOSED immersion, because `p` is separated — that is the definition of
  `IsSeparated`.

Both properties are stable under base change, so `Set.range (E ⟶ S)` is
CLOPEN.  It is nonempty because `w ≫ s = w ≫ t` supplies a lift of `w`
through `E` and `T` is nonempty.  A clopen nonempty subset of a preconnected
space is everything, so `E ⟶ S` is an open immersion that is surjective,
hence an isomorphism (`isIso_iff_isOpenImmersion_and_surjective`), and
`exists_comp_eq_of_isIso_pullback_fst` then factors `e` through `Δ`.
Composing with the two projections of `Z ×_S Z` gives `s = u = t`.

Note what is NOT needed: no properness, no finiteness of the fibres, no
hypothesis on the base beyond preconnectedness, and no group structure. -/
theorem section_eq_of_formallyUnramified {Z S : Scheme.{u}} (p : Z ⟶ S)
    [FormallyUnramified p] [LocallyOfFiniteType p] [IsSeparated p]
    [PreconnectedSpace S] {T : Scheme.{u}} [Nonempty T] (w : T ⟶ S)
    {s t : S ⟶ Z} (hs : s ≫ p = 𝟙 S) (ht : t ≫ p = 𝟙 S)
    (hw : w ≫ s = w ≫ t) : s = t := by
  have hst : s ≫ p = t ≫ p := by rw [hs, ht]
  have hefst : pullback.lift s t hst ≫ pullback.fst p p = s := pullback.lift_fst _ _ _
  have hesnd : pullback.lift s t hst ≫ pullback.snd p p = t := pullback.lift_snd _ _ _
  have hfac : w ≫ pullback.lift s t hst = (w ≫ s) ≫ pullback.diagonal p := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hefst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hesnd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hw]
  obtain ⟨x⟩ := ‹Nonempty ↥T›
  haveI hne := Nonempty.intro ((pullback.lift w (w ≫ s) hfac).base x)
  haveI : IsIso (pullback.fst (pullback.lift s t hst) (pullback.diagonal p)) := by
    refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨?_⟩⟩
    rw [← Set.range_eq_univ]
    refine IsClopen.eq_univ ⟨?_, ?_⟩ (Set.range_nonempty _)
    · exact (pullback.fst (pullback.lift s t hst)
        (pullback.diagonal p)).isClosedEmbedding.isClosed_range
    · exact (pullback.fst (pullback.lift s t hst)
        (pullback.diagonal p)).isOpenEmbedding.isOpen_range
  obtain ⟨u, hu⟩ := exists_comp_eq_of_isIso_pullback_fst
    (pullback.lift s t hst) (pullback.diagonal p)
  have h1 : s = u := by
    rw [← hefst, hu, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have h2 : t = u := by
    rw [← hesnd, hu, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  rw [h1, h2]

/-- **The kernel of `A(R) ⟶ A(R/I)` along a SQUARE-ZERO extension has no
`q`-torsion when `q` is a unit of `R`** (sorry node — and, after the
reduction below, the ONLY thing left in the whole `q ≠ ℓ` half of
`neronKernel_torsionFree`).

TRUE, and it is the standard first statement of deformation theory.  For a
SMOOTH `f : A ⟶ S` (here `ab.smooth`) and a square-zero extension
`R ↠ R/I`, the kernel of `A(R) ⟶ A(R/I)` is canonically

    Hom_{R/I}(e^* Ω_{A/S} ⊗ R/I, I)  ≅  Lie(A/S) ⊗ I,

the lifts of a fixed `(R/I)`-point forming a TORSOR under it.  The point
that matters is not the precise identification but its consequence: the
kernel is an `R`-MODULE, not merely an abelian group (the `R`-action factors
through `R/I` because `I² = 0`).  Multiplication by `q` on an `R`-module is
bijective as soon as `q ∈ Rˣ`, so a `q`-torsion element of the kernel is
`0`.

**Why THIS is the right atom, and why the previous statement of the gap was
not** (2026-07-27).  The gap used to be recorded as "`[q]` is formally
unramified", with the repair plan "globalize `HopfKaehler.lean` from Hopf
algebras to group schemes" — i.e. build translation-invariance of `Ω_{A/S}`
for a non-affine group scheme.  That plan is sound but enormous, and it is
not necessary.  Mathlib's `FormallyUnramified.of_hom_ext` is the
INFINITESIMAL LIFTING CRITERION, phrased on `Spec R`-points — which is
exactly the language `AbelianSchemeStruct` is written in — and reduces
unramifiedness of `[q]` to this statement in about thirty lines (see
`formallyUnramified_mulByNat_of_isUnit` immediately below, PROVEN).  So the
differential-geometric packaging can be dropped entirely: nothing in the
STATEMENT here mentions `Ω`, Kähler differentials, diagonals, or even
morphisms of schemes.  It is a sentence about relative points.

That is the general lesson from this leaf twice over: an irreducibility
verdict is only as wide as the axis searched, and a gap is only as large as
the language it happens to be stated in.

MISSING MACHINERY, checked rather than assumed (2026-07-27).  Mathlib has the
AFFINE-ALGEBRA half of exactly this in
`Mathlib/RingTheory/Smooth/Kaehler.lean`: `derivationOfSectionOfKerSqZero`
(the difference of two sections of a square-zero extension IS a derivation),
`retractionKerToTensorEquivSection`, `tensorKaehlerQuotKerSqEquiv`.  What is
absent is the SCHEME-level statement, and — the harder half — the
compatibility saying that the group law of `ab` on relative points
corresponds to ADDITION of derivations under that identification.  This
project's `Fermat/FLT/GroupScheme/HopfKaehler.lean` has the affine group
scheme version; `~/cs/FLT` has no abelian-scheme development at all.

THE CHECK THAT WOULD REFUTE THE VERDICT: produce, at this pin, an
`R`-module structure (or even just an `R`-scalar action) on the kernel of
`RelPoint.pre` along a square-zero extension, compatible with `ab.add`.  A
single such declaration closes this leaf, since `IsUnit.map` then makes `[q]`
bijective on it.  Note the smoothness hypothesis is already available as
`ab.smooth` and is the only geometric input the construction needs — no
properness, no connectedness, no abelian-ness. -/
theorem eq_zero_of_squareZero_of_isUnit_nsmul
    {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f) (q : ℕ)
    {R S' : CommRingCat.{u}} (φ : R ⟶ S') (_hφ : Function.Surjective φ)
    (_hsq : RingHom.ker φ.hom ^ 2 = ⊥) (_hq : IsUnit ((q : ℕ) : R))
    {b : Spec R ⟶ S} (c : RelPoint f b)
    (_htors : ab.nsmulPoint q c = ab.zero b)
    (_hker : RelPoint.pre (Spec.map φ) rfl c = ab.zero (Spec.map φ ≫ b)) :
    c = ab.zero b :=
  sorry

/-- **`[q]` is formally unramified on an abelian scheme over a base on which
`q` is invertible** (PROVEN, over the deformation-theoretic leaf above).

The reduction is mathlib's `FormallyUnramified.of_hom_ext`: it suffices that
along every square-zero extension `R ↠ R/I` any two `R`-points `g₁, g₂` of
`A` that agree on `Spec (R/I)` and satisfy `[q] ∘ g₁ = [q] ∘ g₂` are equal.

Everything then happens inside the group of relative points, and this is
where the functor-of-points presentation of `AbelianSchemeStruct` pays for
itself:

* `g₁` and `g₂` lie over the SAME base point, because `[q] ≫ f = f`
  (`mulByNat_comp`) — so they are two elements of one group `RelPoint f b`,
  and their difference `c := g₁ − g₂` is meaningful;
* `q • c = 0`, because `nsmul_val` says `q • gᵢ` is `gᵢ ≫ [q]` and those are
  equal by hypothesis;
* `c` dies on `Spec (R/I)`, because `RelPoint.pre` is a group homomorphism
  (`pre_add`, packaged by `AddMonoidHom.mk'`) and `g₁`, `g₂` agree there;
* `q` is a unit in `R`, transported from the base along the ring map
  underlying `b : Spec R ⟶ Spec B` via `map_natCast` and `IsUnit.map`.

The leaf then gives `c = 0`, i.e. `g₁ = g₂`. -/
theorem formallyUnramified_mulByNat_of_isUnit (B : CommRingCat.{u}) (q : ℕ)
    (hq : IsUnit ((q : ℕ) : B)) {A : Scheme.{u}} {f : A ⟶ Spec B}
    (ab : AbelianSchemeStruct f) : FormallyUnramified (ab.mulByNat q) := by
  refine FormallyUnramified.of_hom_ext _ ?_
  intro R S' φ hφ hsq g₁ g₂ hagree hcomp
  have hb : g₂ ≫ f = g₁ ≫ f := by
    rw [← ab.mulByNat_comp q, ← Category.assoc, ← hcomp, Category.assoc, ab.mulByNat_comp]
  letI := ab.addCommGroup (g₁ ≫ f)
  letI := ab.addCommGroup (Spec.map φ ≫ (g₁ ≫ f))
  have pre_sub : ∀ y z : RelPoint f (g₁ ≫ f),
      RelPoint.pre (Spec.map φ) rfl (y - z)
        = RelPoint.pre (Spec.map φ) rfl y - RelPoint.pre (Spec.map φ) rfl z :=
    fun y z => map_sub (AddMonoidHom.mk' (RelPoint.pre (Spec.map φ)
      (rfl : Spec.map φ ≫ (g₁ ≫ f) = Spec.map φ ≫ (g₁ ≫ f)))
      (ab.pre_add (Spec.map φ) rfl)) y z
  set p₁ : RelPoint f (g₁ ≫ f) := ⟨g₁, rfl⟩ with hp₁
  set p₂ : RelPoint f (g₁ ≫ f) := ⟨g₂, hb⟩ with hp₂
  obtain ⟨ψ, hψ⟩ := Spec.homEquiv.symm.surjective (g₁ ≫ f)
  have hqR : IsUnit ((q : ℕ) : R) := by
    have := hq.map ψ.hom
    rwa [map_natCast] at this
  have hq12 : ab.nsmulPoint q p₁ = ab.nsmulPoint q p₂ := by
    refine Subtype.ext ?_
    show (q • p₁ : RelPoint f (g₁ ≫ f)).1 = (q • p₂ : RelPoint f (g₁ ≫ f)).1
    rw [ab.nsmul_val q p₁, ab.nsmul_val q p₂]
    exact hcomp
  have htors : ab.nsmulPoint q (p₁ - p₂) = ab.zero (g₁ ≫ f) := by
    show (q • (p₁ - p₂) : RelPoint f (g₁ ≫ f)) = (0 : RelPoint f (g₁ ≫ f))
    rw [nsmul_sub]
    exact sub_eq_zero_of_eq hq12
  have hker : RelPoint.pre (Spec.map φ) rfl (p₁ - p₂)
      = ab.zero (Spec.map φ ≫ (g₁ ≫ f)) := by
    rw [pre_sub p₁ p₂]
    have h : RelPoint.pre (Spec.map φ) (rfl : Spec.map φ ≫ (g₁ ≫ f) = _) p₁
        = RelPoint.pre (Spec.map φ) rfl p₂ := Subtype.ext hagree
    rw [h]
    exact sub_self _
  have hzero := eq_zero_of_squareZero_of_isUnit_nsmul ab q φ hφ hsq hqR (p₁ - p₂) htors hker
  have hp : p₁ = p₂ := by
    rw [show (ab.zero (g₁ ≫ f)) = (0 : RelPoint f (g₁ ≫ f)) from rfl] at hzero
    exact sub_eq_zero.mp hzero
  exact congrArg Subtype.val hp

/-- **`𝔽_ℓ` is nontrivial when `IsReductionBase` holds** (PROVEN).

Immediate, and needed twice below: `Spec 𝔽_ℓ` must be NONEMPTY for it to
witness the agreement of two sections, and `ℓ = 1` must be excluded when
deducing `ℓ ∤ q`.  If `ZMod ℓ` were trivial then `toF 1 = 0`, so
`ker_eq_nonunits` would make `1` a non-unit of `R`. -/
theorem nontrivial_zmod_of_reductionBase {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (hbase : IsReductionBase ℓ R toF) : Nontrivial (ZMod ℓ) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  rw [← map_one toF, Ne, hbase.ker_eq_nonunits 1]
  exact fun h => h isUnit_one

/-- **A prime `q ≠ ℓ` is a UNIT in the base `ℤ_(ℓ)`** (PROVEN).

`ker_eq_nonunits` turns this into `toF (q : R) ≠ 0`, i.e. `(q : 𝔽_ℓ) ≠ 0`,
i.e. `¬ ℓ ∣ q` — via `CharP.cast_eq_zero_iff`, which holds for `ZMod ℓ` at
EVERY `ℓ`, including `0` and `1`, so no `NeZero` side condition appears.  As
`q` is prime, `ℓ ∣ q` forces `ℓ = 1` or `ℓ = q`; the second is `hqℓ` and the
first is `nontrivial_zmod_of_reductionBase`.

Note this is where — and the only place where — primality of `q` is used in
the `q ≠ ℓ` leaf, and that **`ℓ.Prime` is not needed at all**, which is why it
is absent from the leaf's hypotheses. -/
theorem isUnit_natCast_of_reductionBase {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (hbase : IsReductionBase ℓ R toF) {q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    IsUnit ((q : ℕ) : R) := by
  haveI := nontrivial_zmod_of_reductionBase hbase
  have hone : ¬ (toF 1 = 0) := by
    rw [hbase.ker_eq_nonunits 1]
    exact fun h => h isUnit_one
  by_contra hcon
  have hz : toF ((q : ℕ) : R) = 0 := (hbase.ker_eq_nonunits _).mpr hcon
  rw [map_natCast] at hz
  have hdvd : ℓ ∣ q := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ q).mp hz
  rcases hq.eq_one_or_self_of_dvd ℓ hdvd with h1 | h2
  · subst h1
    exact hone (Subsingleton.elim _ _)
  · exact hqℓ h2.symm

/-- **The kernel of reduction contains no point of PRIME order `q ≠ ℓ`**
(PROVEN, over the single leaf `formallyUnramified_mulByNat_of_isUnit`).

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

**The old audit here recorded this leaf as IRREDUCIBLE along the étale
axis, and that verdict is now RETIRED** (2026-07-27).  It named two
missing ingredients — the `q`-torsion subscheme `𝒥[q]` as a scheme, and
étaleness of `[q]` — and the first of the two turned out not to be
needed at all.  The rigidity argument never studies `𝒥[q]` as an object:
it forms the fibre square `pullback [q] e` and reads two SECTIONS off
it, which mathlib's `pullback` supplies for free.  Everything else — the
open/closed equalizer, connectedness, the passage back to `x = 0` — is
`section_eq_of_formallyUnramified`, proven above outright.

So the whole leaf is now proven over ONE hypothesis,
`formallyUnramified_mulByNat_of_isUnit`, whose own docstring carries the
sharpened audit and the check that would refute it.

The proof, concretely.  `isUnit_natCast_of_reductionBase` makes `q` a
unit of `R`, so `[q]` is formally unramified; it is locally of finite
type and separated for free (`locallyOfFiniteType_mulByNat`,
`isProper_mulByNat`).  Base-changing along the zero section, the
projection `p : 𝒥 ×_{[q],𝒥,e} R ⟶ Spec R` inherits all three.  The
torsion point `x` and the zero section are two SECTIONS of `p` — that is
exactly what `htors` and the zero-section identity say — and `hker` says
they agree after `Spec 𝔽_ℓ ⟶ Spec ℤ_(ℓ)`.  `Spec ℤ_(ℓ)` is preconnected
because `R ⊆ ℚ` is a DOMAIN (`PrimeSpectrum.irreducibleSpace`), and
`Spec 𝔽_ℓ` is nonempty by `nontrivial_zmod_of_reductionBase`.  Rigidity
gives the two sections equal, and composing with the first projection
gives `x.1 = e`, i.e. `x = 0`. -/
theorem neronKernel_torsionFree_primeToResidue (ℓ : ℕ) (R : Subring ℚ)
    (toF : R →+* ZMod ℓ) (hbase : IsReductionBase ℓ R toF)
    (q : ℕ) (hq : q.Prime) (hqℓ : q ≠ ℓ)
    {JZ : Scheme.{0}} {jstrZ : JZ ⟶ SpecLoc R} (abZ : AbelianSchemeStruct jstrZ)
    (x : RelPoint jstrZ (𝟙 (SpecLoc R)))
    (htors : abZ.nsmulPoint q x = abZ.zero (𝟙 (SpecLoc R)))
    (hker : RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) x
      = abZ.zero (SpecLoc.special toF)) :
    x = abZ.zero (𝟙 (SpecLoc R)) := by
  haveI := nontrivial_zmod_of_reductionBase hbase
  haveI : Nonempty ↥(SpecF ℓ) := inferInstanceAs (Nonempty (PrimeSpectrum (ZMod ℓ)))
  haveI : PreconnectedSpace ↥(SpecLoc R) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  haveI hfu : FormallyUnramified (abZ.mulByNat q) :=
    formallyUnramified_mulByNat_of_isUnit (CommRingCat.of R) q
      (isUnit_natCast_of_reductionBase hbase hq hqℓ) abZ
  haveI : LocallyOfFiniteType (abZ.mulByNat q) := abZ.locallyOfFiniteType_mulByNat q
  haveI : IsSeparated (abZ.mulByNat q) := (abZ.isProper_mulByNat q).toIsSeparated
  have hx : x.1 ≫ abZ.mulByNat q = 𝟙 (SpecLoc R) ≫ abZ.zeroSection := by
    have h := congrArg Subtype.val htors
    rw [abZ.zero_val (𝟙 (SpecLoc R))] at h
    rw [← h]
    exact (abZ.nsmul_val q x).symm
  have h0 : abZ.zeroSection ≫ abZ.mulByNat q = 𝟙 (SpecLoc R) ≫ abZ.zeroSection := by
    rw [abZ.zeroSection_comp_mulByNat q, Category.id_comp]
  set sx : SpecLoc R ⟶ pullback (abZ.mulByNat q) abZ.zeroSection :=
    pullback.lift x.1 (𝟙 _) hx with hsx
  set s0 : SpecLoc R ⟶ pullback (abZ.mulByNat q) abZ.zeroSection :=
    pullback.lift abZ.zeroSection (𝟙 _) h0 with hs0
  have hsxs : sx ≫ pullback.snd (abZ.mulByNat q) abZ.zeroSection = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hs0s : s0 ≫ pullback.snd (abZ.mulByNat q) abZ.zeroSection = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hw : SpecLoc.special toF ≫ sx = SpecLoc.special toF ≫ s0 := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hsx, pullback.lift_fst, Category.assoc, hs0, pullback.lift_fst]
      have h := congrArg Subtype.val hker
      rw [abZ.zero_val (SpecLoc.special toF)] at h
      exact h
    · rw [Category.assoc, hsx, pullback.lift_snd, Category.assoc, hs0, pullback.lift_snd]
  haveI : FormallyUnramified (pullback.snd (abZ.mulByNat q) abZ.zeroSection) :=
    MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ hfu
  have heq : sx = s0 :=
    section_eq_of_formallyUnramified _ (SpecLoc.special toF) hsxs hs0s hw
  refine Subtype.ext ?_
  rw [abZ.zero_val (𝟙 (SpecLoc R)), Category.id_comp]
  have hfin := congrArg (fun m => m ≫ pullback.fst (abZ.mulByNat q) abZ.zeroSection) heq
  simp only [hsx, hs0, pullback.lift_fst] at hfin
  exact hfin

end NeronEtaleRigidity

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
either.

**RE-VERIFIED 2026-07-27** (an audit is only as good as its last check).
`Mathlib/RingTheory/FormalGroup/Basic.lean` is still the only file in
that directory, and it still stops exactly where the audit said: it has
`Add` and `Zero` on `Point`, `AddMonoid`, and `AddCommMonoid` under
`IsComm` — and **no `Neg` and no `AddGroup`** — with the
points-in-a-complete-local-ring construction still a `TODO` in its own
docstring.  The verdict stands.

**AND THE ÉTALE ROUTE DOES NOT TRANSFER HERE — do not try it.**  The
sibling leaf `neronKernel_torsionFree_primeToResidue` was closed on
2026-07-27 by rigidity: `[q]` is formally unramified when `q` is a unit
on the base, so the equalizer of a `q`-torsion section with the zero
section is CLOPEN, and `Spec ℤ_(ℓ)` is connected.  Every step of that
argument is available here EXCEPT the first, and the first is false:
`q = ℓ` is precisely the case where `ℓ` is NOT a unit on `ℤ_(ℓ)`, `[ℓ]`
is ramified in residue characteristic `ℓ`, and the equalizer is closed
but not open.  This is not an accident of the proof — it is the same
distinction that makes `hℓ2` load-bearing here and absent there.  So the
two halves really do share no argument, as the cut's docstring claims,
and the rigidity machinery
(`section_eq_of_formallyUnramified`, proven above) buys nothing at this
leaf. -/
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
  two sections of a separated unramified morphism agreeing at a point of
  a connected base agree.  **Needs no hypothesis on `ℓ` whatsoever**, and
  is now PROVEN (2026-07-27), over the single residual leaf
  `formallyUnramified_mulByNat_of_isUnit`.
* `q = ℓ` (`neronKernel_torsionFree_residue`) — the formal group of
  `𝒥` on the maximal ideal, torsion-free because `e = 1 < ℓ − 1`.  Still
  a sorry node, and the formal-group axis is genuinely empty at this pin.

The previous audit here recorded the node as irreducible, but it ranged
only over the formal-group axis; along that axis it was right.  The
ÉTALE axis was never searched, and it carries a strict majority of the
statement (every prime but one).  Isolating it also makes visible that
`hℓ2` is needed for a single prime, which the undivided statement hid.

**How that played out** (2026-07-27, worth recording because it is the
general lesson).  Once the étale half was attacked on its own axis it
turned out that the "missing machinery" the old audit listed was
half-imaginary: the `q`-torsion SUBSCHEME is never needed, only a fibre
square and two sections of it, and the rigidity step is a theorem about
arbitrary morphisms of schemes that mathlib fully supports.  What
survived is one differential-geometric fact about `[q]`, and it is now
the only thing standing between this half and a complete proof.

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

/-- **The integral CURVE model of `X_0(N)` over `ℤ_(ℓ)` exists, at every
`ℓ ∤ N`** (sorry node — Deligne–Rapoport / Igusa).

TRUE: `X_0(N)` has a smooth proper model over `ℤ[1/N]`, hence over
`ℤ_(ℓ)` for `ℓ ∤ N`, and the fibre identifications are the definition of
a model.  `properX` is the valuative criterion of properness for it.

Note there is NO sharpness claim and no hypothesis `ℓ ≠ 2`: this leaf is
universal in `ℓ ∤ N` and says only that the model exists.

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
theorem exists_x0CurveModel_of_base (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N)
    (R : Subring ℚ) (toF : R →+* ZMod ℓ) (_hbase : IsReductionBase ℓ R toF)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (_hX : IsX0Compactification N strX strY j) :
    ∃ (X' XZ YZ : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (xstr : XZ ⟶ SpecLoc R)
      (ystr : YZ ⟶ SpecLoc R) (jZ : YZ ⟶ XZ),
      Nonempty (IsX0CurveModel N ℓ R toF (strX := strX) (strX' := strX') xstr ystr jZ) :=
  sorry

/-- **The relative JACOBIAN of a given integral curve model exists**
(sorry node — Grothendieck's relative Picard scheme).

TRUE: for a smooth proper curve with a section over a base, `Pic⁰` is
representable by an abelian scheme, its formation commutes with base
change, and Abel–Jacobi is defined over the base.  An abelian scheme
with the right generic fibre IS the Néron model, which is `neronJ`.

Note what this leaf does NOT need: it is stated for an arbitrary
`IsX0CurveModel`, so it knows nothing about modular curves.  It is a
statement about smooth proper curves in general, and proving it that way
is the intended route.

IRREDUCIBLE at this pin ALONG THE PICARD AXIS, and the CHECK THAT WOULD
REFUTE THAT: a survey on 2026-07-27 found no Picard SCHEME and no
relative Jacobian in mathlib, `~/cs/FLT` or this project — mathlib's
`Pic` is the ring-theoretic Picard group of a commutative ring
(`Mathlib/RingTheory/PicardGroup.lean`), and this project's
`JacobianPackage` / `ModularJacobianPackage` are axiomatized interfaces,
not constructions.  Producing a representing scheme for the relative
`Pic⁰` functor refutes the claim. -/
theorem exists_x0JacobianModel_of_curveModel (N ℓ : ℕ) (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    (_hbase : IsReductionBase ℓ R toF)
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N ℓ R toF (strX := strX) (strX' := strX') xstr ystr jZ)
    {J : Scheme.{0}} {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr}
    {o : RelPoint strX (𝟙 SpecQ)} (jac : IsJacobianOf strX ab o) :
    ∃ (J' JZ : Scheme.{0}) (jstr' : J' ⟶ SpecF ℓ) (ab' : AbelianSchemeStruct jstr')
      (o' : RelPoint strX' (𝟙 (SpecF ℓ))) (jac' : IsJacobianOf strX' ab' o')
      (jstrZ : JZ ⟶ SpecLoc R) (abZ : AbelianSchemeStruct jstrZ)
      (oZ : RelPoint xstr (𝟙 (SpecLoc R))) (jacZ : IsJacobianOf xstr abZ oZ),
      Nonempty (IsX0JacobianModel cm jac jac' jacZ) :=
  sorry

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

section SharpSieve

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

/-- **The special fibre of a Néron-pinned datum has finitely many
rational points** (sorry node — geometry, UNIVERSAL in `ℓ`).

TRUE, and it carries no sharpness claim whatever, which is why it is
separated out: `d.spX` identifies `X_0(N)(𝔽_ℓ)` with the `𝔽_ℓ`-points of
the integral model `xstr`, and `d.model.isProper` makes that model
proper over `Spec ℤ_(ℓ)`; so the special fibre is a proper scheme over
the finite field `𝔽_ℓ` and has finitely many rational points.  `ℓ ≠ 0`
is not a hypothesis because `d.base` already forces `ℓ` prime — see
`IsReductionBase`, whose docstring derives primality from the two
conditions.

This is the SAME mathematics as
`finite_relPoint_of_x0Compactification_finiteField`, reached from a
Néron datum instead of from a compactification over `𝔽_ℓ`; the two
cannot be shared as stated because a Néron datum does not carry an
`IsX0Compactification` over `𝔽_ℓ`, only over `Spec ℤ_(ℓ)`.  **The check
that would refute that**: a lemma deducing
`IsX0Compactification N strX' strY' j'` from `d` — i.e. that the special
fibre of the model is again a compactification of the `Γ₀(N)`-problem —
would let this leaf be discharged from the other one, and it is the
natural thing for an owner of the integral model to produce.

`_d` carries an underscore only because the body is `sorry`; it is
entirely load-bearing, since without it `strX'` is an arbitrary scheme
over `𝔽_ℓ` and the statement is false. -/
theorem finite_specialFibre_of_x0NeronDatum
    (_d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :
    Finite (RelPoint strX' (𝟙 (SpecF ℓ))) :=
  sorry

/-- **Abel–Jacobi is injective on the special fibre** (sorry node —
geometry, UNIVERSAL in `ℓ`).

TRUE: `x ↦ [x] − [o']` is injective on the points of a curve exactly
when the genus is positive, since `[x] − [y] = 0` with `x ≠ y` gives a
degree-`1` map to `ℙ¹`.  `d.model` pins the curve as `X_0(N)`, and
`hlevel` supplies positivity of the genus — the genus values at the
eleven Kenku levels, in the order of `kenkuLevels`, are
`1, 1, 2, 3, 1, 5, 3, 2, 4, 5, 5`, and the four sieve levels have genus
`3, 4, 5, 5` (Magma, 2026-07-27).  Positivity is preserved by good
reduction, so it holds on the special fibre.

This is the same condition that `IsJacobianOf` deliberately does NOT
carry as a field — see its docstring, "Note what is deliberately NOT a
field here: injectivity of `aj` on points" — and that
`HasRankZeroJacobian` carries on the GENERIC fibre.  This leaf is its
special-fibre counterpart, and it is what lets the sharpness leaf below
speak about Abel–Jacobi CLASSES rather than about points, which is the
form in which the count is actually computable.

Stated over `kenkuLevels` rather than `x0SieveLevels` because nothing in
it is special to the sieve: the seven single-prime levels have positive
genus too, and a successor proving `card_le_of_rankZeroJacobian` will
want it there.

IRREDUCIBLE at this pin: the genus of a curve does not exist in this
development in any form. -/
theorem aj_injective_of_x0NeronDatum (_hlevel : N ∈ kenkuLevels)
    (_d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :
    Function.Injective (jac'.aj (𝟙 (SpecF ℓ))) :=
  sorry

end SharpSieve

/-- **At some good odd prime the reduced rational Jacobian meets the
Abel–Jacobi image in at most `numRationalCusps N` classes** (sorry node
— the arithmetic residue of the sieve).

This is `exists_sharpSievePrime` with the two pieces of geometry above
removed, and it is the statement Magma actually computes: a count of the
intersection of two subsets of the FINITE abelian group `J_0(N)(𝔽_ℓ)` —
the subgroup `Set.range d.redJ ≅ J_0(N)(ℚ)` and the set of Abel–Jacobi
classes `Set.range (jac'.aj)` of the `ℓ + 1 − Tr T_ℓ` points of
`X_0(N)(𝔽_ℓ)`.

The second conjunct, `numRationalCusps N ≤ #X_0(N)(𝔽_ℓ)`, is what lets
the consumer inflate a possibly-smaller survivor set to a `Finset` of
size exactly `numRationalCusps N`, which is the shape `IsSharpSieve`
asks for.  It is true with room to spare — the four counts are
`8, 6, 8, 8` against `numRationalCusps N = 4` — and it must be stated
here rather than separately, because it has to hold at the SAME `ℓ` the
existential produces.

**Why one prime, and why the prime is existentially quantified**: see
the subsection docstring and the FORMAL-CONTENT AUDIT under
`exists_x0Sieve`.  Both apply verbatim; nothing in this reformulation
changes them.  The candidate witnesses are `ℓ = 7, 5, 5, 7` at
`N = 45, 54, 63, 75`, and each passes the refutation test recorded
there.

**Reconnaissance re-run independently with Magma on 2026-07-27**, and
the whole banked table reproduces exactly — the four genera `3, 4, 5, 5`;
the minimising primes `7, 5, 5, 7` over odd good `ℓ < 60` with counts
`8, 6, 8, 8`; the orders `#J_0(N)(𝔽_ℓ) = 512, 972, 6144, 28160` at those
primes and `4096, 6561, 135168, 409600` at the auxiliary `19, 7, 11, 11`;
and the rational cuspidal subgroups `[4,8], [3,3,9], [2,48], [2,40]` of
orders `32, 81, 96, 80`.  So the refutation test is nowhere near
triggered at any of the four witnesses and the statement stands.

**Why the universal quantifier over data is still SAFE** — unchanged
from `exists_sharpSievePrime`, and it is the whole reason
`IsX0NeronDatum` exists: `base` pins the base, `model` pins the integral
curve, `genX`/`genJ`/`spX`/`spJ` pin the fibres and `neronJ` pins `redJ`
as the genuine reduction, so any two data at the same `ℓ` are isomorphic
and both counts are isomorphism invariants.  Weakening `IsX0NeronDatum`
to `IsX0ReductionAt` would make this FALSE, exactly as the subsection
docstring above warns.

`hfin` is load-bearing and is the rank-`0` input: without it
`J_0(N)(ℚ)` is infinite, `Set.range d.redJ` is unconstrained, and no
prime cuts anything.

IRREDUCIBLE at this pin: it needs `#J_0(N)(𝔽_ℓ)` from Eichler–Shimura
and the Abel–Jacobi image inside it as an explicitly computable finite
object. -/
theorem exists_sharpSievePrime_classCount (N : ℕ) (_hlevel : N ∈ x0SieveLevels) :
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
        Finite (RelPoint jstr (𝟙 SpecQ)) →
        (Set.range d.redJ ∩ Set.range (jac'.aj (𝟙 (SpecF ℓ)))).ncard
            ≤ numRationalCusps N ∧
          numRationalCusps N ≤ Nat.card (RelPoint strX' (𝟙 (SpecF ℓ))) :=
  sorry

/-- **Some good odd prime makes the sieve sharp** (PROVEN by
decomposition, 2026-07-27 — the arithmetic heart is now
`exists_sharpSievePrime_classCount`).

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

**The cut, and what each piece costs.**  The old docstring called this
"the residue of `exists_x0Sieve` after the model-theoretic content is
factored out", needing the Abel–Jacobi image of `X_0(N)(𝔽_ℓ)` inside
`J_0(N)(𝔽_ℓ)` plus Eichler–Shimura for `#J_0(N)(𝔽_ℓ)`.  That is a
correct description of the ARITHMETIC, and it left two pieces of pure
geometry mixed in with it, which are now separate leaves:

* `finite_specialFibre_of_x0NeronDatum` — the special fibre has finitely
  many points (properness over a finite field, universal in `ℓ`);
* `aj_injective_of_x0NeronDatum` — Abel–Jacobi is injective there
  (positive genus, universal in `ℓ`);
* `exists_sharpSievePrime_classCount` — the arithmetic residue proper.

Injectivity is what converts the count of surviving POINTS of
`X_0(N)(𝔽_ℓ)` into a count of surviving CLASSES in `J_0(N)(𝔽_ℓ)`, and
the class count is the one a computation can produce, since it is an
intersection of two subsets of a finite abelian group.  Both geometric
leaves are universal in `ℓ`, so neither has to be found at the same
prime as the arithmetic — the "the two halves must meet at the same `ℓ`"
obstruction recorded under `exists_x0Sieve` applies only to the
existential leaf, and the padding bound `4 ≤ #X_0(N)(𝔽_ℓ)` is carried
there for exactly that reason.

The proof below is the counting argument in full: the survivors form a
`Finset`, Abel–Jacobi maps it injectively into
`Set.range redJ ∩ Set.range aj'`, so it has at most `numRationalCusps N`
elements, and `Finset.exists_superset_card_eq` inflates it to exactly
that many inside the finite point set. -/
theorem exists_sharpSievePrime (N : ℕ) (hlevel : N ∈ x0SieveLevels) :
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
        Finite (RelPoint jstr (𝟙 SpecQ)) → IsSharpSieve N d := by
  classical
  have hkenku : N ∈ kenkuLevels := by fin_cases hlevel <;> decide
  obtain ⟨ℓ, hℓ, hℓ2, hℓN, hcount⟩ := exists_sharpSievePrime_classCount N hlevel
  refine ⟨ℓ, hℓ, hℓ2, hℓN, ?_⟩
  intro R toF X J X' J' XZ YZ JZ strX jstr ab o strX' jstr' ab' o' jac jac' xstr ystr
    jZ jstrZ abZ oZ jacZ d hfin
  obtain ⟨hle, hge⟩ := hcount d hfin
  haveI : Finite (RelPoint strX' (𝟙 (SpecF ℓ))) := finite_specialFibre_of_x0NeronDatum d
  haveI : Fintype (RelPoint strX' (𝟙 (SpecF ℓ))) := Fintype.ofFinite _
  have haj : Function.Injective (jac'.aj (𝟙 (SpecF ℓ))) :=
    aj_injective_of_x0NeronDatum hkenku d
  set t : Finset (RelPoint strX' (𝟙 (SpecF ℓ))) :=
    Finset.univ.filter (fun x' => ∃ a, d.redJ a = jac'.aj (𝟙 (SpecF ℓ)) x') with ht
  have hsub : ↑(t.image (jac'.aj (𝟙 (SpecF ℓ)))) ⊆
      Set.range d.redJ ∩ Set.range (jac'.aj (𝟙 (SpecF ℓ))) := by
    intro y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, ht, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    obtain ⟨x', ⟨a, ha⟩, rfl⟩ := hy
    exact ⟨⟨a, ha⟩, ⟨x', rfl⟩⟩
  have hfinI : (Set.range d.redJ ∩ Set.range (jac'.aj (𝟙 (SpecF ℓ)))).Finite :=
    (Set.finite_range _).subset Set.inter_subset_right
  have hcard : t.card ≤ numRationalCusps N := by
    have h2 := Set.ncard_le_ncard hsub hfinI
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective t haj] at h2
    exact h2.trans hle
  have hge' : numRationalCusps N ≤ Fintype.card (RelPoint strX' (𝟙 (SpecF ℓ))) := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨s, hts, hscard⟩ := Finset.exists_superset_card_eq hcard hge'
  refine ⟨s, fun x' hx' => hts ?_, hscard⟩
  simp only [ht, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hx'

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

/-! #### The Néron pinning of the `j`-map, and `red_jm` as a theorem

The FORMAL-CONTENT AUDIT in the docstring of `IsX0JReductionAt` records
that `redX` there is pinned by nothing — send every rational point to a
cusp of the special fibre and `red_jm`'s hypothesis becomes unsatisfiable,
so the structure is inhabited with no arithmetic content.  It also
records the remedy: re-found the structure on an integral model, exactly
as `IsX0NeronDatum` did for `redJ` in the subsection above.

This subsection carries that out.  `IsX0JNeronDatum` is the `j`-map
analogue of `IsX0NeronDatum`: it holds the smooth model of `X_0(N)` and
of `Y_0(N)` over `ℤ_(q)`, identifies both fibres of each as equivalences
of FUNCTORS of points (so Yoneda pins them as fibre products rather than
as bare point sets — the naturality fields are what make that true, and
without them a point-set relabelling would reintroduce exactly the junk
`redX` the audit describes), and carries the `j`-invariant as a function
on integral points with values in `ℤ_(q)` itself.

Three things then stop being assumptions:

* `redX` is DEFINED — extend a rational point to the integral model by
  the valuative criterion (`properX`), then restrict to the special
  fibre;
* the `q`-integrality half of `red_jm` becomes the statement that an
  element of `ℤ_(q)` has non-negative `q`-adic valuation, which is
  `IsReductionBase.padicValRat_nonneg` (PROVEN here from the two axioms
  of `IsReductionBase`, by an explicit Bézout construction of `1/q`);
* the congruence half becomes the image under `toF` of the identity
  `j · den = num` inside `ℤ_(q)`.

`red_jm` is therefore a THEOREM (`IsX0JNeronDatum.red_jm`), and
`IsX0JNeronDatum.toJReduction` produces an `IsX0JReductionAt`.
`exists_x0JReductionAt` — moved here from the `j`-map subsection, since
it now consumes `SpecLoc` — is PROVEN from `exists_x0JNeronDatum`.

**UPDATE (2026-07-27, later the same day): `exists_x0JNeronDatum` is now
PROVEN too, and this paragraph's claim that it is the one open leaf is
retired.**  As first written it demanded the Deligne–Rapoport / Igusa
model for itself — the same missing object as `exists_x0NeronDatum`
above, and therefore a DUPLICATE of it.  It has been re-founded on the
shared `IsX0CurveModel`; see the subsection *Sharing ONE integral model*
below for what replaced it.  The two leaves that remain in this
subsection are `isX0Compactification_data_of_compactificationY0` (three
facts about `X_0(N)/ℚ`) and `exists_x0JOpenModel_of_curveModel` (the open
part's fibres, and `j` integral on the model).

Everything else this subsection needs is PROVEN here,
including the two facts that would most naturally have been posited:

* `exists_relSectionAlong_of_special` — an integral section of the proper
  model whose SPECIAL value lies in the open part `𝒴` lies in `𝒴`
  throughout.  Not modular at all: `jZ` is an open immersion, so the
  section's preimage of `𝒴` is open in `Spec ℤ_(q)`; the image of the
  closed point lies in it (`IsReductionBase.comap_eq_closedPoint`); and
  the only open of the spectrum of a local ring containing the closed
  point is the whole space.  `IsOpenImmersion.lift` then factors the
  section.
* `IsReductionBase.isLocalRing` and `IsReductionBase.nontrivialResidue` —
  the two consequences of `IsReductionBase` its own docstring asserts
  informally, now derived. -/

/-- **`sectionAlong` at an arbitrary base point.**

`sectionAlong` is hardwired to the base point `𝟙 S`, which is all its
consumers above need.  The pinning below has to push a section of the
integral model down to BOTH fibres, i.e. along the base points
`SpecLoc.generic R` and `SpecLoc.special toF`, so the same construction
is needed at a general `g`.  At `g = 𝟙 S` the two agree definitionally
(`sectionAlong_eq_relSectionAlong`), so nothing above is disturbed. -/
def relSectionAlong {X Y S T : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S} (j : Y ⟶ X)
    (hj : j ≫ strX = strY) {g : T ⟶ S} (y : RelPoint strY g) : RelPoint strX g :=
  ⟨y.1 ≫ j, by rw [Category.assoc, hj, y.2]⟩

/-- `relSectionAlong` extends `sectionAlong`, definitionally. -/
theorem sectionAlong_eq_relSectionAlong {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S}
    (j : Y ⟶ X) (hj : j ≫ strX = strY) (y : RelPoint strY (𝟙 S)) :
    sectionAlong j hj y = relSectionAlong j hj y := rfl

/-- Pushing a section into the ambient curve commutes with change of base
point.  This is what lets one integral section of `𝒴` be read on both
fibres. -/
theorem pre_relSectionAlong {X Y S T' T : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S}
    (j : Y ⟶ X) (hj : j ≫ strX = strY) {h : T' ⟶ T} {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (y : RelPoint strY g) :
    RelPoint.pre h hg (relSectionAlong j hj y) = relSectionAlong j hj (RelPoint.pre h hg y) :=
  Subtype.ext (Category.assoc _ _ _).symm

/-- **An open immersion is a monomorphism**, so a point of the ambient
curve comes from at most one point of the open part.  This is the
uniqueness that makes the integral lift produced by
`exists_relSectionAlong_of_special` well determined on both fibres. -/
theorem relSectionAlong_injective {X Y S T : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S}
    (j : Y ⟶ X) [Mono j] (hj : j ≫ strX = strY) {g : T ⟶ S} :
    Function.Injective (relSectionAlong (strX := strX) j hj (g := g)) := fun _ _ hab =>
  Subtype.ext ((cancel_mono j).mp (congrArg Subtype.val hab))

/-- **`ℓ` does not divide the denominator of any element of `R`**
(PROVEN), for `R` pinned by `IsReductionBase`.

Exactly the content of "`R = ℤ_(ℓ)`", in the only form the `j`-map
dictionary needs, and derived from the two axioms of `IsReductionBase`
rather than from any localization API.

The proof is Bézout run backwards.  Write `r = a/b` in lowest terms and
suppose `ℓ ∣ b`, say `b = ℓ c`.  Coprimality of `a` and `b` gives
`u a + v b = 1`, and then

`ℓ · (u r c + v c) = u (ℓ c) r + v (ℓ c) = u (b r) + v b = u a + v b = 1`,

with `u r c + v c` visibly an element of `R` — `r ∈ R`, and `R` contains
`ℤ` because it is a subring of `ℚ`.  So `ℓ` is a UNIT of `R`.  But
`toF (ℓ : R) = 0` in `ZMod ℓ`, and `ker_eq_nonunits` turns that into
`¬ IsUnit (ℓ : R)`.  Contradiction.

Note both axioms are used: `ker_eq_nonunits` supplies the contradiction,
and it is also what forces `ZMod ℓ` to be nontrivial (were `ℓ = 1`, then
`toF 1 = 0` would make `1` a non-unit). -/
theorem IsReductionBase.not_dvd_den {q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    (h : IsReductionBase q R toF) (r : R) : ¬ q ∣ ((r : ℚ)).den := by
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hbezZ : IsCoprime ((r : ℚ)).num (((r : ℚ)).den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact (r : ℚ).reduced
  obtain ⟨u, v, hbezZ⟩ := hbezZ
  have hbez : (u : ℚ) * (((r : ℚ)).num : ℚ) + (v : ℚ) * (((r : ℚ)).den : ℚ) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hbezZ
  have hx : (r : ℚ) * (((r : ℚ)).den : ℚ) = (((r : ℚ)).num : ℚ) := Rat.mul_den_eq_num _
  have hqc : (q : ℚ) * (c : ℚ) = (((r : ℚ)).den : ℚ) := by exact_mod_cast congrArg Nat.cast hc.symm
  set s : R := (u : R) * r * (c : R) + (v : R) * (c : R) with hs
  have hunit : ((q : ℕ) : R) * s = 1 := by
    apply Subtype.ext
    push_cast [hs]
    linear_combination hbez + (u : ℚ) * hx + ((u : ℚ) * (r : ℚ) + (v : ℚ)) * hqc
  have h1 : IsUnit ((q : ℕ) : R) := IsUnit.of_mul_eq_one _ hunit
  have h2 : toF ((q : ℕ) : R) = 0 := by rw [map_natCast, ZMod.natCast_self]
  exact ((h.ker_eq_nonunits _).mp h2) h1

/-- **Every element of `ℤ_(q)` is `q`-integral** (PROVEN): the first
conjunct of `red_jm`, once the `j`-invariant is known to be the value of
a function with values in `R`. -/
theorem IsReductionBase.padicValRat_nonneg {q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    (h : IsReductionBase q R toF) (r : R) : 0 ≤ padicValRat q ((r : ℚ)) := by
  have hz : padicValNat q ((r : ℚ)).den = 0 :=
    padicValNat.eq_zero_of_not_dvd (h.not_dvd_den r)
  simp only [padicValRat, hz]
  simp

/-- **The residue ring is nontrivial** (PROVEN).  Were `ZMod ℓ` trivial —
i.e. `ℓ = 1` — then `toF 1 = 0`, and `ker_eq_nonunits` would make `1` a
non-unit.  So `ℓ ≠ 1` is a consequence of `IsReductionBase`, not a
hypothesis, exactly as its docstring claims. -/
theorem IsReductionBase.nontrivialResidue {q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    (h : IsReductionBase q R toF) : Nontrivial (ZMod q) := by
  rcases subsingleton_or_nontrivial (ZMod q) with _ | hn
  · exact absurd isUnit_one ((h.ker_eq_nonunits 1).mp (Subsingleton.elim _ _))
  · exact hn

/-- **`R` is a LOCAL ring** (PROVEN), which is the half of
`IsReductionBase` that `exists_relSectionAlong_of_special` needs: it is
what makes `Spec R` have a unique closed point, so that an open
containing that point is everything.

`ker_eq_nonunits` is exactly "the non-units are an ideal", read
backwards: if `a` is not a unit then `toF a = 0`, so `toF (1 - a) = 1`,
which is nonzero because the residue ring is nontrivial, so `1 - a` IS a
unit. -/
theorem IsReductionBase.isLocalRing {q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    (h : IsReductionBase q R toF) : IsLocalRing R := by
  haveI := h.nontrivialResidue
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => ?_)
  by_cases ha : IsUnit a
  · exact Or.inl ha
  · refine Or.inr ?_
    by_contra hb
    have h1 : toF a = 0 := (h.ker_eq_nonunits a).mpr ha
    have h2 : toF (1 - a) = 0 := (h.ker_eq_nonunits _).mpr hb
    rw [map_sub, map_one, h1, sub_zero] at h2
    exact one_ne_zero h2

/-- **`Spec 𝔽_ℓ ⟶ Spec R` hits the CLOSED point** (PROVEN).

Every point of `Spec 𝔽_ℓ` pulls back to the maximal ideal of `R`: the
pullback of a prime is prime, hence proper, hence contained in the
maximal ideal; and it contains `ker toF`, which IS the maximal ideal by
`ker_eq_nonunits`.  Note `ℓ` is not assumed prime anywhere — the
statement is about an arbitrary point of `Spec (ZMod ℓ)`, and
`nontrivialResidue` is what guarantees there is one. -/
theorem IsReductionBase.comap_eq_closedPoint {q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    (h : IsReductionBase q R toF) (P : PrimeSpectrum (ZMod q)) :
    letI := h.isLocalRing
    PrimeSpectrum.comap toF P = IsLocalRing.closedPoint R := by
  letI := h.isLocalRing
  apply PrimeSpectrum.ext
  apply le_antisymm
  · exact IsLocalRing.le_maximalIdeal (PrimeSpectrum.comap toF P).2.ne_top
  · intro x hx
    have hx0 : toF x = 0 := (h.ker_eq_nonunits x).mpr (IsLocalRing.mem_maximalIdeal x |>.mp hx)
    show toF x ∈ P.asIdeal
    rw [hx0]
    exact Ideal.zero_mem _

/-- **A Néron-pinned `j`-reduction datum for `X_0(N)` at `q`.**

This is `IsX0JReductionAt` with `redX` no longer free, in exactly the way
`IsX0NeronDatum` is `IsX0ReductionAt` with `redJ` no longer free.
Instead of positing a reduction map and an axiom relating it to the
`j`-map, the datum carries the INTEGRAL MODELS over `ℤ_(q)` and reads
both off them.

The data:

* `base` pins the base as `Spec ℤ_(q)` — see `IsReductionBase`;
* `model` pins the integral curve, together with its open part, as the
  smooth model of `X_0(N)` over that base; for `q ∤ N` this is the
  Deligne–Rapoport / Igusa model, and reusing `IsX0Compactification`
  (whose base was left general for exactly this purpose) is what makes
  `jZ` an open immersion, hence a mono, hence the lift below unique;
* `genX`, `genY`, `spX`, `spY` identify the two fibres of each of the two
  models.  They are equivalences of FUNCTORS of points — for every `T`
  and every base point, natural in the "identified base" form used
  throughout this file — so by Yoneda they say `X ≅ 𝒳 ×_{ℤ_(q)} ℚ` and
  `X' ≅ 𝒳 ×_{ℤ_(q)} 𝔽_q`, and likewise for `Y`.  **The `_nat` fields are
  load-bearing for faithfulness, not decoration**: without them the
  identifications are bare bijections of point sets, and composing `spX`
  with a permutation of `X'(𝔽_q)` that preserves the open part would
  satisfy every other field while changing `redX` — which is the junk
  witness of the audit, reintroduced one level up;
* `genX_j` and `spX_j` say the identifications carry the open immersion
  `Y ⊆ X` to the open immersion `𝒴 ⊆ 𝒳`, i.e. that cuspidality is
  preserved by the identifications;
* `properX` is the **valuative criterion of properness** for the curve,
  `𝒳(ℤ_(q)) ≅ X(ℚ)`.  It is what turns a rational point into an integral
  one, and hence the only reason a reduction map exists at all;
* `jmZ`, `jmGen`, `jmSp` are the `j`-invariant on integral sections, on
  the generic fibre and on the special fibre.  `jmZ` lands in `R`
  ITSELF — that is the whole `q`-integrality statement, and it is the one
  place the classical fact "`j` is a regular function on the integral
  model of the open part" enters;
* `jmGen_pre`, `jmSp_pre` say those three agree, and `jm_gen` identifies
  the generic one with the `j`-map `hj.jm` the consumers use.

**What is deliberately NOT a field**: a Jacobian, the Néron mapping
property, or anything about `redJ`.  This datum and `IsX0NeronDatum`
share no field and can be carried side by side, which is the same
separation `IsX0JReductionAt` already keeps from `IsX0ReductionAt`. -/
structure IsX0JNeronDatum (N q : ℕ) (R : Subring ℚ) (toF : R →+* ZMod q)
    {Y X Y' X' YZ XZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    (hX : IsCompactificationY0 strY strX)
    (hX' : IsX0Compactification N strX' strY' jY')
    (hj : IsJMapOn N hc)
    {ystr : YZ ⟶ SpecLoc R} {xstr : XZ ⟶ SpecLoc R} (jZ : YZ ⟶ XZ) where
  /-- the base is the local ring of `ℤ` at `q` -/
  base : IsReductionBase q R toF
  /-- the integral model is the smooth model of `X_0(N)` over that base,
  together with its open part -/
  model : IsX0Compactification N xstr ystr jZ
  /-- the generic fibre of the curve model is `X`, functorially -/
  genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀
  /-- the generic fibre of the open model is `Y`, functorially -/
  genY : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strY g ≃ RelPoint ystr g₀
  /-- the special fibre of the curve model is `X'`, functorially -/
  spX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF q) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint strX' g ≃ RelPoint xstr g₀
  /-- the special fibre of the open model is `Y'`, functorially -/
  spY : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF q) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint strY' g ≃ RelPoint ystr g₀
  /-- naturality of the generic identification of curves -/
  genX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strX g),
    genX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genX g g₀ h₀ x)
  /-- naturality of the generic identification of open parts -/
  genY_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strY g),
    genY g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genY g g₀ h₀ x)
  /-- naturality of the special identification of curves -/
  spX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF q} {g' : T' ⟶ SpecF q}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint strX' g),
    spX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spX g g₀ h₀ x)
  /-- naturality of the special identification of open parts -/
  spY_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF q} {g' : T' ⟶ SpecF q}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint strY' g),
    spY g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spY g g₀ h₀ x)
  /-- the generic identification carries the open immersion -/
  genX_j : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (y : RelPoint strY g),
    genX g g₀ h (relSectionAlong hX.j hX.over y)
      = relSectionAlong jZ model.comm (genY g g₀ h y)
  /-- the special identification carries the open immersion -/
  spX_j : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF q) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀) (y' : RelPoint strY' g),
    spX g g₀ h (relSectionAlong jY' hX'.comm y')
      = relSectionAlong jZ model.comm (spY g g₀ h y')
  /-- **valuative criterion of properness**: every rational point of `X`
  extends uniquely to an integral point of the model -/
  properX : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint xstr (𝟙 (SpecLoc R)) → RelPoint xstr (SpecLoc.generic R))
  /-- the `j`-invariant of an integral point, INTEGRAL: `j` is a regular
  function on the integral model of the open part -/
  jmZ : RelPoint ystr (𝟙 (SpecLoc R)) → R
  /-- the `j`-invariant on the generic fibre -/
  jmGen : RelPoint ystr (SpecLoc.generic R) → ℚ
  /-- the `j`-invariant on the special fibre -/
  jmSp : RelPoint ystr (SpecLoc.special toF) → ZMod q
  /-- the generic `j`-invariant of an integral point is its integral one -/
  jmGen_pre : ∀ yZ : RelPoint ystr (𝟙 (SpecLoc R)),
    jmGen (RelPoint.pre (SpecLoc.generic R) (Category.comp_id _) yZ) = ((jmZ yZ : R) : ℚ)
  /-- the special `j`-invariant of an integral point is the reduction of
  its integral one -/
  jmSp_pre : ∀ yZ : RelPoint ystr (𝟙 (SpecLoc R)),
    jmSp (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) yZ) = toF (jmZ yZ)
  /-- the generic `j`-invariant is the `j`-map the consumers use -/
  jm_gen : ∀ y : RelPoint strY (𝟙 SpecQ),
    hj.jm y = jmGen (genY (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) y)

/-- **An integral section of the proper model whose special value lies in
the open part lies in the open part throughout** (PROVEN).

Pure topology of a local base — no modular input at all, and the reason
`red_jm` needs no further geometric assumption.  `jZ` is an open
immersion, so `jZ.opensRange` is open; the hypothesis puts the image of
the CLOSED point of `Spec R` inside it (the image of
`SpecLoc.special toF` is the closed point by
`IsReductionBase.comap_eq_closedPoint`); and the only open subset of the
spectrum of a LOCAL ring containing the closed point is the whole space
(`Scheme.preimage_eq_top_of_closedPoint_mem`).  So
`Set.range xZ.1.base ⊆ Set.range jZ.base`, and
`AlgebraicGeometry.IsOpenImmersion.lift` factors the section through
`𝒴`.

`hbase` is load-bearing twice over: it is what makes `R` local (so that
"open and contains the closed point" implies "everything"), and it is
what identifies the image of `SpecLoc.special toF` with the closed
point.  Drop it and the statement is FALSE — over a base with two closed
points, a section can meet `𝒴` at one of them and a cusp at the other.

Only the factorisation is asserted.  That the lift restricts to `y'` on
the special fibre is NOT a second conjunct because it is a consequence:
`jZ` is a mono, so `relSectionAlong jZ` is injective
(`relSectionAlong_injective`), and `red_jm` derives it that way. -/
theorem exists_relSectionAlong_of_special {N q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    (hbase : IsReductionBase q R toF)
    {YZ XZ : Scheme.{0}} {ystr : YZ ⟶ SpecLoc R} {xstr : XZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (model : IsX0Compactification N xstr ystr jZ)
    (xZ : RelPoint xstr (𝟙 (SpecLoc R))) (y' : RelPoint ystr (SpecLoc.special toF))
    (hh : RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) xZ
        = relSectionAlong jZ model.comm y') :
    ∃ yZ : RelPoint ystr (𝟙 (SpecLoc R)), relSectionAlong jZ model.comm yZ = xZ := by
  haveI := model.isOpen
  haveI := hbase.nontrivialResidue
  haveI := hbase.isLocalRing
  obtain ⟨P⟩ : Nonempty (PrimeSpectrum (ZMod q)) := inferInstance
  have heq : SpecLoc.special toF ≫ xZ.1 = y'.1 ≫ jZ := congrArg Subtype.val hh
  have hclosed : (SpecLoc.special toF).base P = IsLocalRing.closedPoint R :=
    hbase.comap_eq_closedPoint P
  have hmem : xZ.1.base (IsLocalRing.closedPoint R) ∈ jZ.opensRange := by
    rw [← hclosed]
    have hp := congrArg (fun (f : SpecF q ⟶ XZ) => f.base P) heq
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hp
    exact ⟨y'.1.base P, hp.symm⟩
  have hsub : Set.range xZ.1.base ⊆ Set.range jZ.base := by
    rintro _ ⟨z, rfl⟩
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem xZ.1 hmem
    have hz : z ∈ xZ.1 ⁻¹ᵁ jZ.opensRange := by rw [htop]; trivial
    exact hz
  refine ⟨⟨IsOpenImmersion.lift jZ xZ.1 hsub, ?_⟩, ?_⟩
  · rw [← model.comm, ← Category.assoc, IsOpenImmersion.lift_fac, xZ.2]
  · exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

namespace IsX0JNeronDatum

variable {N q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    {Y X Y' X' YZ XZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    {hX : IsCompactificationY0 strY strX}
    {hX' : IsX0Compactification N strX' strY' jY'}
    {hj : IsJMapOn N hc}
    {ystr : YZ ⟶ SpecLoc R} {xstr : XZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (d : IsX0JNeronDatum N q R toF hX hX' hj (ystr := ystr) (xstr := xstr) jZ)

/-- **The integral point of the curve model** attached to a rational
point, by the valuative criterion of properness. -/
noncomputable def intX (x : RelPoint strX (𝟙 SpecQ)) : RelPoint xstr (𝟙 (SpecLoc R)) :=
  (Equiv.ofBijective _ d.properX).symm
    (d.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) x)

theorem pre_intX (x : RelPoint strX (𝟙 SpecQ)) :
    RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) (d.intX x)
      = d.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) x :=
  (Equiv.ofBijective _ d.properX).apply_symm_apply _

/-- **Reduction of rational points of the curve**: extend to the integral
model, then restrict to the special fibre.  This is `redX` of
`IsX0JReductionAt`, no longer posited. -/
noncomputable def redX (x : RelPoint strX (𝟙 SpecQ)) : RelPoint strX' (𝟙 (SpecF q)) :=
  (d.spX (𝟙 (SpecF q)) (SpecLoc.special toF) (Category.id_comp _)).symm
    (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intX x))

theorem redX_def (x : RelPoint strX (𝟙 SpecQ)) :
    d.redX x = (d.spX (𝟙 (SpecF q)) (SpecLoc.special toF) (Category.id_comp _)).symm
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intX x)) := rfl

/-- **The `j`-map on the rational points of the special fibre**, read off
the model.  This is `jm'` of `IsX0JReductionAt`, no longer posited. -/
noncomputable def jm' (y' : RelPoint strY' (𝟙 (SpecF q))) : ZMod q :=
  d.jmSp (d.spY (𝟙 (SpecF q)) (SpecLoc.special toF) (Category.id_comp _) y')

theorem jm'_def (y' : RelPoint strY' (𝟙 (SpecF q))) :
    d.jm' y' = d.jmSp (d.spY (𝟙 (SpecF q)) (SpecLoc.special toF) (Category.id_comp _) y') := rfl

/-- **`red_jm` of `IsX0JReductionAt`, as a THEOREM** — the repair the
FORMAL-CONTENT AUDIT of that structure asked for.

The proof is the classical one, read on points.  Push the hypothesis
through `spX`: the integral extension of `sectionAlong hX.j hX.over y`
restricts on the special fibre to a point of the OPEN part `𝒴`.  By
`exists_relSectionAlong_of_special` the whole integral section therefore
lies in `𝒴`, giving an integral point `yZ` of the open model; since `jZ`
is a mono, `yZ` restricts to `y` generically and to `y'` specially.  Then

* `hj.jm y` is `jmZ yZ`, an element of `R = ℤ_(q)`, so it has
  non-negative `q`-adic valuation — `IsReductionBase.padicValRat_nonneg`;
* `jm' y'` is `toF (jmZ yZ)`, and the congruence is the image under `toF`
  of the identity `jmZ yZ · den = num`, which holds in `R` because it
  holds in `ℚ` and `R ⊆ ℚ`.

Note where the pinning is used: nowhere is `redX` assumed to do anything.
Every step is a consequence of `properX`, `spX_j`, `genX_j` and the
model. -/
theorem red_jm (y : RelPoint strY (𝟙 SpecQ)) (y' : RelPoint strY' (𝟙 (SpecF q)))
    (hred : d.redX (sectionAlong hX.j hX.over y) = sectionAlong jY' hX'.comm y') :
    0 ≤ padicValRat q (hj.jm y) ∧
      d.jm' y' * ((hj.jm y).den : ZMod q) = ((hj.jm y).num : ZMod q) := by
  haveI := d.model.isOpen
  have hA : RelPoint.pre (SpecLoc.special toF) (Category.comp_id _)
        (d.intX (sectionAlong hX.j hX.over y))
      = relSectionAlong jZ d.model.comm
        (d.spY (𝟙 (SpecF q)) (SpecLoc.special toF) (Category.id_comp _) y') := by
    have hcong := congrArg (d.spX (𝟙 (SpecF q)) (SpecLoc.special toF) (Category.id_comp _)) hred
    rwa [d.redX_def, Equiv.apply_symm_apply,
      sectionAlong_eq_relSectionAlong jY' hX'.comm y', d.spX_j] at hcong
  obtain ⟨yZ, hyZ⟩ := exists_relSectionAlong_of_special d.base d.model _ _ hA
  have hgen : RelPoint.pre (SpecLoc.generic R) (Category.comp_id _) yZ
      = d.genY (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) y := by
    apply relSectionAlong_injective jZ d.model.comm
    rw [← pre_relSectionAlong, hyZ, d.pre_intX,
      sectionAlong_eq_relSectionAlong hX.j hX.over y, d.genX_j]
  have hsp : RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) yZ
      = d.spY (𝟙 (SpecF q)) (SpecLoc.special toF) (Category.id_comp _) y' := by
    apply relSectionAlong_injective jZ d.model.comm
    rw [← pre_relSectionAlong, hyZ, hA]
  have hjm : hj.jm y = ((d.jmZ yZ : R) : ℚ) := by
    rw [d.jm_gen y, ← hgen, d.jmGen_pre]
  have hjm' : d.jm' y' = toF (d.jmZ yZ) := by
    rw [d.jm'_def, ← hsp, d.jmSp_pre]
  refine ⟨?_, ?_⟩
  · rw [hjm]; exact d.base.padicValRat_nonneg _
  · rw [hjm', hjm]
    have hR : (d.jmZ yZ) * ((((d.jmZ yZ : R) : ℚ)).den : R)
        = ((((d.jmZ yZ : R) : ℚ)).num : R) := by
      apply Subtype.ext
      push_cast
      exact Rat.mul_den_eq_num _
    have hF := congrArg toF hR
    rwa [map_mul, map_natCast, map_intCast] at hF

/-- **A Néron-pinned `j`-datum is a `j`-reduction datum** (PROVEN).

This is the whole point of the pinning: `redX` is no longer an arbitrary
function and `red_jm` is no longer an assumption about it, but a
consequence of both maps being induced by morphisms of models over
`ℤ_(q)`.  Exactly the shape of `IsX0NeronDatum.toReduction`. -/
noncomputable def toJReduction : IsX0JReductionAt N q hX hX' hj where
  redX := d.redX
  jm' := d.jm'
  red_jm := d.red_jm

end IsX0JNeronDatum

/-! #### Sharing ONE integral model: the `j`-datum over `IsX0CurveModel`

`exists_x0JNeronDatum` was written (2026-07-27) as a single leaf
demanding the whole Deligne–Rapoport / Igusa model for itself.  Its own
docstring said so: *"the same missing object as `exists_x0NeronDatum`"*.
That is exactly the problem — it was a SECOND statement of an object the
Jacobian side already needs, so proving Deligne–Rapoport once would not
have discharged it.

Meanwhile the Jacobian side had been cut: `IsX0NeronDatum` is now
assembled from `IsX0CurveModel` (the smooth proper model of `X_0(N)`
over `ℤ_(ℓ)` with both fibres of the CURVE identified and the valuative
criterion) and `IsX0JacobianModel` (the relative Picard scheme over that
same model).  `IsX0CurveModel` mentions no Jacobian and no `j`; it is
precisely the shared object.

So this subsection re-founds `exists_x0JNeronDatum` on it.  The residual
content is genuinely disjoint from the curve model:

* **the OPEN part's two fibres.**  `IsX0CurveModel` carries the open part
  `𝒴 ⊆ 𝒳` of the integral model (inside its `model` field) but identifies
  only the fibres of the PROPER curve — `genX`, `spX`.  `genY`, `spY`,
  their naturality, and the compatibility of both identifications with
  the open immersion (`genX_j`, `spX_j`) are what the `j`-layer adds.
  Mathematically this is base change of an open immersion, which is why
  it is a different statement from the model's existence and not a
  weaker copy of it;
* **the `j`-invariant on integral points** — `jmZ`, valued in `R` itself,
  with its two restrictions.  This is Igusa: `j` is a regular function on
  the integral model of `Y_0(N)` for `q ∤ N`.

Both are collected in `IsX0JOpenModel`, taking the curve model as a
PARAMETER — exactly the shape `IsX0JacobianModel` already uses, so the
three halves of the integral story now sit side by side over one model.

**One gap is bookkeeping rather than geometry, and it is separated out
rather than hidden.**  This leaf's hypothesis on the generic curve is
`IsCompactificationY0`, which carries `proper` and `smooth` but not the
relative dimension, the geometric connectedness, or the finiteness of the
cusp locus that `IsX0Compactification` — the hypothesis of
`exists_x0CurveModel_of_base` — also demands.  Those three facts are the
leaf `isX0Compactification_data_of_compactificationY0`; the packaging
around them is proven (`IsCompactificationY0.toX0Compactification`).
They are true because `hc` pins `Y` as `Y_0(N)`, hence as a geometrically
connected smooth affine CURVE, and a dominant open immersion into a
smooth proper `X` then forces `X` to be its smooth compactification.

**Net effect on the frontier.**  One leaf becomes two, and the object
that was duplicated becomes shared.  Counting leaves alone this looks
like a step backwards; counting THEOREMS TO PROVE it is a strict
reduction, because the Deligne–Rapoport model — by far the largest of the
three — is now demanded once for the whole file instead of once per
consumer. -/

/-- **The three facts about `X_0(N)/ℚ` that `IsCompactificationY0` does
not carry** (sorry node).

TRUE for `N ≠ 0`.  `hc` pins `Y` up to isomorphism as the coarse moduli
space of the `Γ₀(N)`-problem over `ℚ`, which is a geometrically connected
smooth affine curve; `hX` presents `X` as a smooth proper scheme
containing it as a DENSE open (`isDominant`).  Hence `X` is a smooth
proper geometrically connected curve — relative dimension `1` and
geometric connectedness transfer along a dominant open immersion from
`Y` — and its cusp locus, the complement of a dense open in an
irreducible curve, is finite.

`_hN` is load-bearing and not decoration: at `N = 0` the `Γ₀(0)`-problem
over `Spec ℚ` is empty (`isEmpty_of_gamma0Datum_zero`), so `Y` may be the
empty scheme, `isDominant` then forces `X` empty, and the empty scheme is
not geometrically connected.  `_hc` is load-bearing too — without it `X`
is merely *some* smooth proper scheme with a dense open, which need not
have dimension `1` at all.  Both are underscored only because the proof
is a `sorry` and every hypothesis is therefore unused.

Stated as the three MISSING facts rather than as
`Nonempty (IsX0Compactification …)` on purpose: four of that structure's
seven fields are already available from `hX` and `hc`, and burying them
in a sorry node would overstate what is open. -/
theorem isX0Compactification_data_of_compactificationY0 (N : ℕ) (_hN : N ≠ 0)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (_hc : IsCoarseModuliY0 N strY) (hX : IsCompactificationY0 strY strX) :
    SmoothOfRelativeDimension 1 strX ∧ GeometricallyConnected strX ∧
      (Set.range hX.j.base)ᶜ.Finite :=
  sorry

/-- **`IsCompactificationY0` plus the three facts above IS an
`IsX0Compactification`** (PROVEN).

Pure packaging, and it is what lets this file's `j`-layer call
`exists_x0CurveModel_of_base` — whose hypothesis is the stronger
structure — instead of restating the integral model for itself. -/
def IsCompactificationY0.toX0Compactification {N : ℕ}
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (hX : IsCompactificationY0 strY strX) (hc : IsCoarseModuliY0 N strY)
    (h : SmoothOfRelativeDimension 1 strX ∧ GeometricallyConnected strX ∧
      (Set.range hX.j.base)ᶜ.Finite) :
    IsX0Compactification N strX strY hX.j where
  comm := hX.«over»
  coarse := hc
  isOpen := hX.isOpenImmersion
  isProper := hX.proper
  smooth := h.1
  connected := h.2.1
  finite_compl := h.2.2

/-- **The OPEN-PART and `j` half of a Néron-pinned `j`-datum, over a
GIVEN integral curve model.**

This is `IsX0JNeronDatum` with every field the curve model already
carries deleted, and the curve model itself taken as a parameter — the
same discipline `IsX0JacobianModel` follows for the Jacobian half.
Deleted here, because `cm` supplies them: `model`, `genX`, `spX`,
`genX_nat`, `spX_nat`, `properX`.  (`base` is supplied by
`exists_isReductionBase`.)

What remains splits in two, and both parts are stated over `cm` so that
they cannot be satisfied by a *different* model:

* `genY`, `spY`, `genY_nat`, `spY_nat` identify the two fibres of the
  OPEN part `𝒴` as equivalences of FUNCTORS of points, and `genX_j`,
  `spX_j` say the curve identifications `cm.genX`, `cm.spX` carry the
  open immersion `Y ⊆ X` (resp. `Y' ⊆ X'`) to `jZ`.  The naturality
  fields are load-bearing for the same reason as in `IsX0JNeronDatum`:
  without them these are bare bijections of point sets and a point-set
  relabelling preserving the open part satisfies everything else while
  changing nothing that Yoneda can see;
* `jmZ`, `jmGen`, `jmSp` and their three compatibilities carry the
  `j`-invariant on integral points, valued in `R = ℤ_(q)` ITSELF.  That
  integrality is the whole `q`-integrality half of `red_jm`. -/
structure IsX0JOpenModel (N q : ℕ) (R : Subring ℚ) (toF : R →+* ZMod q)
    {Y X Y' X' XZ YZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    (hX : IsCompactificationY0 strY strX)
    (hX' : IsX0Compactification N strX' strY' jY')
    (hj : IsJMapOn N hc)
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) where
  /-- the generic fibre of the open model is `Y`, functorially -/
  genY : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strY g ≃ RelPoint ystr g₀
  /-- the special fibre of the open model is `Y'`, functorially -/
  spY : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF q) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint strY' g ≃ RelPoint ystr g₀
  /-- naturality of the generic identification of open parts -/
  genY_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strY g),
    genY g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genY g g₀ h₀ x)
  /-- naturality of the special identification of open parts -/
  spY_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF q} {g' : T' ⟶ SpecF q}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint strY' g),
    spY g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spY g g₀ h₀ x)
  /-- the generic identification carries the open immersion -/
  genX_j : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (y : RelPoint strY g),
    cm.genX g g₀ h (relSectionAlong hX.j hX.over y)
      = relSectionAlong jZ cm.model.comm (genY g g₀ h y)
  /-- the special identification carries the open immersion -/
  spX_j : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF q) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀) (y' : RelPoint strY' g),
    cm.spX g g₀ h (relSectionAlong jY' hX'.comm y')
      = relSectionAlong jZ cm.model.comm (spY g g₀ h y')
  /-- the `j`-invariant of an integral point, INTEGRAL: `j` is a regular
  function on the integral model of the open part -/
  jmZ : RelPoint ystr (𝟙 (SpecLoc R)) → R
  /-- the `j`-invariant on the generic fibre -/
  jmGen : RelPoint ystr (SpecLoc.generic R) → ℚ
  /-- the `j`-invariant on the special fibre -/
  jmSp : RelPoint ystr (SpecLoc.special toF) → ZMod q
  /-- the generic `j`-invariant of an integral point is its integral one -/
  jmGen_pre : ∀ yZ : RelPoint ystr (𝟙 (SpecLoc R)),
    jmGen (RelPoint.pre (SpecLoc.generic R) (Category.comp_id _) yZ) = ((jmZ yZ : R) : ℚ)
  /-- the special `j`-invariant of an integral point is the reduction of
  its integral one -/
  jmSp_pre : ∀ yZ : RelPoint ystr (𝟙 (SpecLoc R)),
    jmSp (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) yZ) = toF (jmZ yZ)
  /-- the generic `j`-invariant is the `j`-map the consumers use -/
  jm_gen : ∀ y : RelPoint strY (𝟙 SpecQ),
    hj.jm y = jmGen (genY (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) y)

/-- **A curve model plus its open-and-`j` half IS a Néron-pinned
`j`-datum** (PROVEN).

Field-by-field assembly, and the point of the whole cut: every curve
field of the datum is taken VERBATIM from `cm`, so the datum this
produces is built on the shared Deligne–Rapoport model rather than on
one of its own. -/
def IsX0JOpenModel.toJNeronDatum
    {N q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    {Y X Y' X' XZ YZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    {hX : IsCompactificationY0 strY strX}
    {hX' : IsX0Compactification N strX' strY' jY'}
    {hj : IsJMapOn N hc}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    {cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ}
    (om : IsX0JOpenModel N q R toF hX hX' hj cm) (hbase : IsReductionBase q R toF) :
    IsX0JNeronDatum N q R toF hX hX' hj (ystr := ystr) (xstr := xstr) jZ where
  base := hbase
  model := cm.model
  genX := cm.genX
  genY := om.genY
  spX := cm.spX
  spY := om.spY
  genX_nat := cm.genX_nat
  genY_nat := om.genY_nat
  spX_nat := cm.spX_nat
  spY_nat := om.spY_nat
  genX_j := om.genX_j
  spX_j := om.spX_j
  properX := cm.properX
  jmZ := om.jmZ
  jmGen := om.jmGen
  jmSp := om.jmSp
  jmGen_pre := om.jmGen_pre
  jmSp_pre := om.jmSp_pre
  jm_gen := om.jm_gen

/-- **The open-part fibres and the integral `j` exist over a given curve
model** (sorry node — base change of the open immersion, and Igusa).

TRUE for `q ∤ N`.  Two independent statements, deliberately kept in one
leaf because both are read off the SAME model and neither is usable
without the other:

* the special fibre `𝒴 ×_{ℤ_(q)} 𝔽_q` of the open part exists and its
  complement in `𝒳 ×_{ℤ_(q)} 𝔽_q` is the special fibre of the cusp locus,
  which is what `hX'` and `spX_j` record; the generic side is the same
  statement over `ℚ`.  This is formal — base change of an open immersion
  is an open immersion, and the fibre identifications are the universal
  property of the fibre product read on points — but it is not FREE here,
  because `IsX0CurveModel` identifies `X'` only through a natural
  equivalence of functors and recovering `Y' ↪ X'` from it needs Yoneda
  in the slice category over `Spec ℤ_(q)`;
* `j` is a regular function on `𝒴`, valued in `ℤ_(q)` on integral
  sections.  This is Igusa's good-reduction statement for the `j`-line at
  `q ∤ N`, and it is the only genuinely modular input left in this
  subsection.

Note what is NOT assumed, exactly as before the cut: `q` is not required
to be odd.  Mazur needs `q ≠ 2` for the FORMAL IMMERSION, which is a
different statement, is not part of this module, and would only weaken
this leaf.

IRREDUCIBLE at this pin ALONG THE MODULI AXIS, and the CHECK THAT WOULD
REFUTE THAT: the `j`-half needs the `j`-line over `ℤ_(q)`, and the survey
recorded in `exists_x0CurveModel_of_base` found no integral model of a
modular curve in mathlib, `~/cs/FLT` or this project.  Producing one — or
producing a Yoneda-style reconstruction of `Y' ↪ X'` from `cm.spX` alone,
which would split the first bullet off as PROVEN — refutes it.  The
second of those is the cheaper attack and is the recommended next cut. -/
theorem exists_x0JOpenModel_of_curveModel (N q : ℕ) (_hN : N ≠ 0) (_hq : q.Prime)
    (_hqN : ¬ q ∣ N) (R : Subring ℚ) (toF : R →+* ZMod q)
    (_hbase : IsReductionBase q R toF)
    {Y X X' XZ YZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {hc : IsCoarseModuliY0 N strY}
    (hX : IsCompactificationY0 strY strX) (hj : IsJMapOn N hc)
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    ∃ (Y' : Scheme.{0}) (strY' : Y' ⟶ SpecF q) (jY' : Y' ⟶ X')
      (hX' : IsX0Compactification N strX' strY' jY'),
      Nonempty (IsX0JOpenModel N q R toF hX hX' hj cm) :=
  sorry

/-- **Existence of the Néron-pinned `j`-reduction datum at a prime
`q ∤ N`** (PROVEN, was a sorry node until 2026-07-27).

Re-founded on the SHARED integral curve model.  The proof is the
assembly and nothing else:

1. `exists_isReductionBase` constructs the base `ℤ_(q)` — PROVEN, and the
   same witness the Jacobian side uses;
2. `isX0Compactification_data_of_compactificationY0` supplies the three
   facts about `X/ℚ` that `IsCompactificationY0` omits, and
   `IsCompactificationY0.toX0Compactification` packages them;
3. `exists_x0CurveModel_of_base` — the SHARED Deligne–Rapoport / Igusa
   model, already required by `exists_x0NeronDatum` — produces `cm`;
4. `exists_x0JOpenModel_of_curveModel` produces the open-part fibres and
   the integral `j` over that same `cm`;
5. `IsX0JOpenModel.toJNeronDatum` assembles them, taking every curve
   field verbatim from `cm`.

The old docstring's *"IRREDUCIBLE at this pin"* verdict is retired: it
was true of the leaf as a single statement, and the axis it did not
search was the SHARING axis — that the integral model it needed was
already being demanded, in a Jacobian-free form, a thousand lines above.
See the subsection docstring. -/
theorem exists_x0JNeronDatum (N q : ℕ) (hN : N ≠ 0) (hq : q.Prime) (hqN : ¬ q ∣ N)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {hc : IsCoarseModuliY0 N strY} (hX : IsCompactificationY0 strY strX)
    (hj : IsJMapOn N hc) :
    ∃ (R : Subring ℚ) (toF : R →+* ZMod q) (Y' X' YZ XZ : Scheme.{0})
      (strY' : Y' ⟶ SpecF q) (strX' : X' ⟶ SpecF q) (jY' : Y' ⟶ X')
      (hX' : IsX0Compactification N strX' strY' jY')
      (ystr : YZ ⟶ SpecLoc R) (xstr : XZ ⟶ SpecLoc R) (jZ : YZ ⟶ XZ),
      Nonempty (IsX0JNeronDatum N q R toF hX hX' hj (ystr := ystr) (xstr := xstr) jZ) := by
  obtain ⟨R, toF, hbase⟩ := exists_isReductionBase q hq
  obtain ⟨X', XZ, YZ, strX', xstr, ystr, jZ, ⟨cm⟩⟩ :=
    exists_x0CurveModel_of_base N q hq hqN R toF hbase
      (hX.toX0Compactification hc
        (isX0Compactification_data_of_compactificationY0 N hN hc hX))
  obtain ⟨Y', strY', jY', hX', ⟨om⟩⟩ :=
    exists_x0JOpenModel_of_curveModel N q hN hq hqN R toF hbase hX hj cm
  exact ⟨R, toF, Y', X', YZ, XZ, strY', strX', jY', hX', ystr, xstr, jZ,
    ⟨om.toJNeronDatum hbase⟩⟩

/-- **Existence of the good reduction of `(X_0(N), j)` at a prime
`q ∤ N`** (PROVEN, was a sorry node until 2026-07-27).

Moved here from the `j`-map subsection — it consumes `SpecLoc`, which is
declared in the integral-model subsection above — and re-founded on
`IsX0JNeronDatum` exactly as the FORMAL-CONTENT AUDIT of
`IsX0JReductionAt` asked.  The whole content is now in
`exists_x0JNeronDatum` — which is itself PROVEN as of later the same day,
over the SHARED `IsX0CurveModel`, so what this ultimately rests on is
`exists_x0CurveModel_of_base` together with the two smaller leaves named
in its docstring.  The three hypotheses that used to be decoration
(`hN`, `hq`, `hqN`, formerly underscored) are passed straight through. -/
theorem exists_x0JReductionAt (N q : ℕ) (hN : N ≠ 0) (hq : q.Prime) (hqN : ¬ q ∣ N)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {hc : IsCoarseModuliY0 N strY} (hX : IsCompactificationY0 strY strX)
    (hj : IsJMapOn N hc) :
    ∃ (Y' X' : Scheme.{0}) (strY' : Y' ⟶ SpecF q) (strX' : X' ⟶ SpecF q) (jY' : Y' ⟶ X')
      (hX' : IsX0Compactification N strX' strY' jY'),
      Nonempty (IsX0JReductionAt N q hX hX' hj) := by
  obtain ⟨R, toF, Y', X', YZ, XZ, strY', strX', jY', hX', ystr, xstr, jZ, ⟨d⟩⟩ :=
    exists_x0JNeronDatum N q hN hq hqN hX hj
  exact ⟨Y', X', strY', strX', jY', hX', ⟨d.toJReduction⟩⟩
/-! #### The single-prime counting bound

`card_le_of_rankZeroJacobian` — the criterion the seven single-prime
levels rest on — is PROVEN here, over the Néron pinning built above.  It
used to sit beside `exists_x0Compactification_mod_prime`, before the
sieve subsection existed; **it was moved down to this point on
2026-07-27 for the only reason Lean ever forces a relocation**, namely
that its proof consumes `exists_x0NeronDatum`, `neronReduction_injective`
and `IsX0NeronDatum.toReduction`, all of which are declared above.
`y0HasNoRationalPoint_of_witnessPrime` moved with it, unchanged, because
it is its sole consumer; nothing in between referred to either.

**What the move bought, and it is the point of doing it.**  The
reduction bound and the sieve bound were being developed as if they were
two theories.  They are one: both are "reduction at a good odd prime is
injective on a rank-`0` Jacobian, and Abel–Jacobi is injective in
positive genus, so `X_0(N)(ℚ)` injects into `X_0(N)(𝔽_ℓ)`".  The sieve
half then *bounds the image by the surviving set*; the counting half
merely bounds it by the whole of `X_0(N)(𝔽_ℓ)`.  So the counting bound
is the WEAKER of the two, and once the sieve's machinery exists it is a
corollary rather than an independent leaf — exactly as
`exists_x0NeronDatum_of_base`'s docstring predicted when it said that
factoring the models out is "a genuine reduction in the total work
rather than a repackaging".

**What genuinely remained**, and it is the mismatch between the two
statements rather than any missing formal-group theory.
`exists_x0NeronDatum` manufactures its OWN special fibre, whereas
`card_le_of_rankZeroJacobian` is handed an ARBITRARY `X_0(N)_{𝔽_ℓ}` by
its caller and must bound by *that* curve's point count.  Bridging the
two needs precisely the two leaves below: the special fibre of the smooth
model IS `X_0(N)` over `𝔽_ℓ` (good reduction), and any two `X_0(N)`'s
over `𝔽_ℓ` have the same rational points (uniqueness).  Neither is
formal-group theory, and neither was previously stated anywhere.
-/

/-- **The special fibre of the smooth model over `ℤ_(ℓ)` is `X_0(N)` over
`𝔽_ℓ`** (sorry node — good reduction, on the curve side).

TRUE, and it is the defining property of good reduction: for `ℓ ∤ N` the
Deligne–Rapoport/Igusa model `𝒳` over `ℤ_(ℓ)` has `𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ` the
coarse space of the same `Γ₀(N)`-moduli problem over `𝔽_ℓ`, and it is
smooth, proper and geometrically connected there because those properties
are fibrewise for a smooth proper model.  So the datum's special fibre
`X'` carries an `IsX0Compactification N` over `𝔽_ℓ`, its open part being
the special fibre of the model's own open part.

**The hypothesis that does the work is `d`**, and it cannot be weakened
to "`X'` is *some* scheme whose points biject with the model's".  It is
`d.model` that says the integral curve is the smooth model of `X_0(N)`,
and `d.spX` *together with* `d.spX_nat` that identify `X'` as its special
fibre — as an isomorphism of FUNCTORS of points over `𝔽_ℓ`, hence by
Yoneda as `X' ≅ 𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ` rather than as a bare bijection of
point sets.  Dropping naturality would leave `X'` free to be any scheme
abstractly equinumerous with the special fibre, which is not a modular
curve and would make this leaf FALSE.  The same reasoning is recorded at
`exists_sharpSievePrime` for why quantifying over `IsX0NeronDatum` is
safe where quantifying over `IsX0ReductionAt` would not be.

`_hℓN` is load-bearing for the same reason it is in
`exists_x0NeronDatum_of_base`: at `ℓ ∣ N` there is no smooth model and
the special fibre is not a smooth curve.  The hypotheses carry
underscores only because the body is `sorry`.

IRREDUCIBLE at this pin: it is the curve half of the statement that
`exists_x0NeronDatum_of_base` is the model half of, and neither the
integral model of `X_0(N)` nor base change of coarse moduli spaces exists
here. -/
theorem exists_isX0Compactification_specialFibre {N ℓ : ℕ} (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X J X' J' XZ YZ JZ : Scheme.{0}} {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    {jac : IsJacobianOf strX ab o} {jac' : IsJacobianOf strX' ab' o'}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} {jacZ : IsJacobianOf xstr abZ oZ}
    (_d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :
    ∃ (Y'' : Scheme.{0}) (strY'' : Y'' ⟶ SpecF ℓ) (j'' : Y'' ⟶ X'),
      Nonempty (IsX0Compactification N strX' strY'' j'') :=
  sorry

/-- **`X_0(N)` over `𝔽_ℓ` is unique up to isomorphism, hence its rational
points up to bijection** (sorry node).

TRUE, and classical, in two steps — and both steps are already *stated*
in this file, which is why this is a small leaf rather than a theory:

* `IsCoarseModuliY0` is an INITIALITY property, so it determines
  `(Y, classify)` up to unique isomorphism over the base.  Its own
  docstring says exactly this, and `Y0HasNoRationalPoint` is quantified
  over all coarse moduli spaces for precisely this reason.  So
  `Y₁ ≅ Y₂` over `𝔽_ℓ`.
* Over a FIELD, a smooth curve has a unique smooth proper
  compactification: two smooth proper geometrically connected curves
  containing a common dense open glue along it, the closure of the graph
  in `X₁ ×_k X₂` being proper and birational over both.  This is what the
  docstring of `IsX0Compactification` means by "`finite_compl` is what
  makes `X` the unique smooth compactification".  So `X₁ ≅ X₂` over
  `𝔽_ℓ`, and an isomorphism over the base induces a bijection on
  `𝔽_ℓ`-points.

**Why `𝔽_ℓ` and not a general base.**  The compactification is stated
here only over `Spec 𝔽_ℓ`, with `ℓ` prime, because that is the base at
which the second step is unconditionally true.  Over a general base — a
non-normal or non-reduced one, say — the closure-of-the-graph argument
fails, and stating the leaf there would risk a FALSE statement for the
sake of a generality nothing consumes.  `_hℓ` is what makes `ZMod ℓ` a
field and is load-bearing for exactly that reason.

**Not vacuous, and not silently degenerate.**  At `N = 0` the hypotheses
are unsatisfiable — `isEmpty_of_gamma0Datum_zero` forces `Y` initial,
hence empty, while `finite_compl` then makes the whole space of `X`
finite, which a smooth proper curve over a field is not — so the leaf is
vacuously true there and carries no content it should not.  At the levels
that matter it is satisfied, by `exists_x0Compactification_mod_prime`.

The conclusion is `Nonempty (… ≃ …)` on points rather than an
isomorphism of schemes: that is all any consumer needs, it is implied by
the scheme-level statement, and it avoids committing this file to a
transport of `RelPoint` along an isomorphism that nothing else here uses.

IRREDUCIBLE at this pin: no smooth-compactification theorem for curves
exists in `Mathlib`, which is the same obstruction recorded at
`exists_x0Compactification`. -/
theorem nonempty_relPointEquiv_of_isX0Compactification {N ℓ : ℕ} (_hℓ : ℓ.Prime)
    {X₁ Y₁ X₂ Y₂ : Scheme.{0}} {strX₁ : X₁ ⟶ SpecF ℓ} {strY₁ : Y₁ ⟶ SpecF ℓ}
    {jY₁ : Y₁ ⟶ X₁} {strX₂ : X₂ ⟶ SpecF ℓ} {strY₂ : Y₂ ⟶ SpecF ℓ} {jY₂ : Y₂ ⟶ X₂}
    (_h₁ : IsX0Compactification N strX₁ strY₁ jY₁)
    (_h₂ : IsX0Compactification N strX₂ strY₂ jY₂) :
    Nonempty (RelPoint strX₁ (𝟙 (SpecF ℓ)) ≃ RelPoint strX₂ (𝟙 (SpecF ℓ))) :=
  sorry

/-- **The rank-`0` reduction bound, `#X_0(N)(ℚ) ≤ #X_0(N)(𝔽_ℓ)`**
(PROVEN 2026-07-27 — this is the criterion).

Classical, and the proof here is the classical one, assembled from the
Néron pinning above rather than from anything new.  `hJ` makes
`J_0(N)(ℚ)` finite, hence torsion; for `ℓ` an odd prime of good reduction
the reduction map on torsion `J_0(N)(ℚ) → J_0(N)(𝔽_ℓ)` is INJECTIVE, its
kernel being the points of a formal group over `ℤ_ℓ`, which is
torsion-free for `ℓ` odd; Abel–Jacobi based at a rational point embeds
`X_0(N)(ℚ)` into `J_0(N)(ℚ)` and commutes with reduction; so
`X_0(N)(ℚ)` injects into `X_0(N)(𝔽_ℓ)`.

Each clause is now a named declaration:
`exists_x0NeronDatum` supplies the models, `neronReduction_injective`
(over `neronKernel_torsionFree`) the injectivity, and
`IsX0NeronDatum.toReduction` packages them as `redX`, `redJ`, `red_aj`.
`redX` is then injective because it is sandwiched between two injections,
which is the identical two-line argument that `card_le_of_sieve` runs —
the two theorems differ only in what they bound the image by.

**Every hypothesis is load-bearing**, the leaf is false without any one
of them, and the proof consumes each exactly where the refutation says it
must:

* without finiteness in `hJ`, a positive-rank Jacobian gives infinitely
  many rational points already in genus `1` — consumed as
  `d.finite_intPoints`, feeding `neronReduction_injective`;
* without injectivity in `hJ`, `N = 1` refutes it: `X_0(1) = ℙ¹` has
  trivial Jacobian and infinitely many rational points — consumed as
  `hajinj`, the outer of the two injections;
* without `hℓ2` the formal-group argument fails at `ℓ = 2`, where
  `2`-torsion can die under reduction — consumed twice, by
  `exists_x0NeronDatum` and by `neronReduction_injective`;
* without `hℓN` there is no good reduction at `ℓ` and the special fibre
  is not a smooth curve — consumed by `exists_x0NeronDatum`.

The conclusion bounds every `Finset` of rational points rather than
`Nat.card`, because `Nat.card` of an infinite type is `0` and the bound
would then hold vacuously; the `Finset` form also carries finiteness.
`hfin` is what turns the bound on a `Finset` into a bound by `Nat.card`,
and it is used for nothing else.

What is left open is not this argument but its two geometric inputs, and
they are the two leaves directly above: the caller's `X'` and the
datum's own special fibre are both `X_0(N)` over `𝔽_ℓ`
(`exists_isX0Compactification_specialFibre`), and any two such have the
same points (`nonempty_relPointEquiv_of_isX0Compactification`). -/
theorem card_le_of_rankZeroJacobian {N : ℕ} {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {j : Y ⟶ X} (hX : IsX0Compactification N strX strY j)
    (hJ : HasRankZeroJacobian strX) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓN : ¬ ℓ ∣ N) {X' Y' : Scheme.{0}} {strX' : X' ⟶ SpecF ℓ}
    {strY' : Y' ⟶ SpecF ℓ} {j' : Y' ⟶ X'}
    (hX' : IsX0Compactification N strX' strY' j') (m : ℕ)
    (hfin : Finite (RelPoint strX' (𝟙 (SpecF ℓ))))
    (hm : Nat.card (RelPoint strX' (𝟙 (SpecF ℓ))) = m)
    (s : Finset (RelPoint strX (𝟙 SpecQ))) : s.card ≤ m := by
  classical
  obtain ⟨J, jstr, ab, o, jac, hJfin, hajinj⟩ := hJ
  obtain ⟨R, toF, X'', J'', XZ, YZ, JZ, strX'', jstr'', ab'', o'', jac'', xstr, ystr,
    jZ, jstrZ, abZ, oZ, jacZ, ⟨d⟩⟩ := exists_x0NeronDatum N ℓ hℓ hℓ2 hℓN hX jac
  -- the special fibre of the smooth model is `X_0(N)` over `𝔽_ℓ` …
  obtain ⟨Y'', strY'', j'', ⟨hX''⟩⟩ :=
    exists_isX0Compactification_specialFibre (jac := jac) hℓ hℓN d
  -- … hence has the same rational points as the reduction we were handed
  obtain ⟨e⟩ := nonempty_relPointEquiv_of_isX0Compactification hℓ hX'' hX'
  have hinj := neronReduction_injective ℓ R toF d.base hℓ2 abZ (d.finite_intPoints hJfin)
  have red : IsX0ReductionAt jac jac'' := d.toReduction hinj
  -- `redX` is injective because it is sandwiched between two injections
  have hFinj : Function.Injective fun x => e (red.redX x) := by
    intro a b hab
    refine hajinj (red.redJ_inj ?_)
    rw [red.red_aj, red.red_aj, e.injective hab]
  haveI := hfin
  haveI : Fintype (RelPoint strX' (𝟙 (SpecF ℓ))) := Fintype.ofFinite _
  calc s.card = (s.image fun x => e (red.redX x)).card :=
        (Finset.card_image_of_injective s hFinj).symm
    _ ≤ Nat.card (RelPoint strX' (𝟙 (SpecF ℓ))) := by
        rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
        exact Finset.card_le_univ _
    _ = m := hm

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

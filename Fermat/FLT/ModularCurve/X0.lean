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
an INTERFACE, and all thirteen levels are proven over it — seven on a
single counting prime, four on the sieve `exists_x0Sieve`, and the two
semiprime levels `35`, `39` added 2026-07-27.
What the interface's six leaves still need, and none of it exists at
this pin:

* the smooth compactification of a coarse moduli space, and the cusps
  of `X_0(N)` with their field of definition
  (`exists_x0Compactification`, `nonempty_cuspLocus` — the latter is
  what `exists_rationalCusps` was decomposed into on 2026-07-27, through
  `nonempty_cuspIndexing`, and it needs only the EASY direction of the
  cusp classification, stated as the cusp locus with its residue
  degrees so that no Galois descent enters);
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
-- half of `neronKernel_torsionFree`.  It is ALSO the source of
-- `AbelianSchemeStruct.baseChange` and the relative-point bijection
-- `RelPoint.baseChangeDown` / `RelPoint.baseChangeUp`, out of which
-- `exists_gamma0Datum_baseChange` is built.  PUBLIC on both counts: those
-- names appear in the SIGNATURES of the `Gamma0BaseChange` helpers, not only
-- in their proof bodies.  It is FURTHER the source of the two Yoneda bridges
-- `nsmul_val` / `zero_val`, which turn `n • x` and `0` on relative points into
-- COMPOSITES with those fixed morphisms and are what makes the torsion
-- subscheme `C[n]` formable here (`CyclicSubgroupOfOrder.torsionScheme`); see
-- the note at `exists_torsionSubscheme` correcting the earlier claim that this
-- module "does NOT help".  This module imports only `AbelianScheme` from the
-- project, so no cycle is created.
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
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
-- `AlgebraicGeometry.Flat`: the flatness half of "finite locally free", which
-- is what makes `CyclicSubgroupOfOrder` the Katz–Mazur moduli problem
-- `[Γ₀(N)]` rather than a strictly larger one.  See the `flat` field of
-- `CyclicSubgroupOfOrder` and the faithfulness audit of
-- `exists_coarseModuliY0_of_pos`.
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
-- `AlgebraicGeometry.Etale`: the hypothesis carried by every declaration in the
-- torsion-subscheme section below.  It is what repairs the FALSE leaf
-- `flat_torsionι` (see the REPAIR RECORD there): `geom_cyclic` pins the
-- CARDINALITY of the geometric fibres of `C`, Katz–Mazur pin their RANK, and
-- the two agree exactly when `C ⟶ T` is étale.  Consumed through
-- `Etale.of_comp`, `Etale.iff_flat_and_formallyUnramified` and the base-change
-- stability instance.  The module is already in the cone through
-- `Morphisms.Smooth`, which `AbelianSchemeStruct.smooth` needs.
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
-- `ValuativeCommSq` and `IsProper.eq_valuativeCriterion`: the valuative criterion
-- of properness, which is what `bijective_pre_generic_of_isProper` runs on — and
-- through it both `properX` of `IsX0CurveModel` and `neronJ` of
-- `IsX0JacobianModel`.
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
-- `Algebra.IsInvariant`, the ring-theoretic half of GIT: it is the hypothesis
-- of `specInvariants_universal`, the pure geometric-invariant-theory leaf that
-- `exists_gamma0Atlas` is split along.
public import Mathlib.RingTheory.Invariant.Basic
-- The GIT quotient theorem itself, proved mathlib-facing and modular-curve-free in
-- `Fermat/FLT/Mathlib/AlgebraicGeometry/InvariantQuotient.lean`; it closes the
-- `¬ IsAffine` branch of `specInvariants_universal`.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.InvariantQuotient
-- `AddCommGroup.finite_of_fg_torsion`, which turns Mordell–Weil (finite
-- generation) plus rank `0` (torsion) into finiteness of `J_0(N)(ℚ)`; it is the
-- whole proof of `finite_jacobian_of_kenkuLevel` from its two leaves.
public import Mathlib.GroupTheory.FiniteAbelian.Basic
-- The affine/ring input to leaf (iii-b-1) — see the `GeomSquareRing` section.
-- `AlgebraicGeometry.pullbackSpecIso`: the square of two affines over an affine
-- base is `Spec` of the tensor product.  This is what makes leaf (iii-b-1) a
-- question of commutative algebra rather than of scheme theory.
public import Mathlib.AlgebraicGeometry.Pullbacks
-- `Algebra.IsGeometricallyReduced` and `Algebra.IsGeometricallyReduced.of_forall_fg`:
-- reducedness of `ℚ̄ ⊗_ℚ ℚ̄` by reduction to finitely generated subalgebras.
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
-- `Algebra.FormallyUnramified.of_isSeparable` / `.isReduced_of_field`: a finite
-- separable extension stays reduced after base change to `ℚ̄`.
public import Mathlib.RingTheory.Unramified.Field
-- `Algebra.FormallyEtale` and the `EssFiniteType` instances it carries.
public import Mathlib.RingTheory.Etale.Field
-- `Algebra.TensorProduct.piRight`: the tensor product commutes with FINITE
-- products, which is what splits `(J → ℚ̄) ⊗_ℚ (J → ℚ̄)` into copies of `ℚ̄ ⊗_ℚ ℚ̄`.
public import Mathlib.RingTheory.TensorProduct.Pi
-- `PerfectField.ofCharZero`: `ℚ` is perfect, which is why `ℚ̄/ℚ` is separable.
public import Mathlib.FieldTheory.Perfect
-- `CommAlgCat` bundles "a finite-type `R`-algebra" as ONE object, which is what
-- `exists_finiteType_algHom_injection_of_isProper` existentially quantifies over;
-- an unbundled `∃ (A : Type) (_ : CommRing A) (_ : Algebra R A), …` cannot be
-- written, since the later binders need the earlier ones as instances.
public import Mathlib.Algebra.Category.CommAlgCat.Basic

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
points over the shifted base point.  **That bijection IS needed and IS
available** (corrected 2026-07-27; this docstring previously said the
development never needs it and therefore never proves it):
`exists_gamma0Datum_baseChange` consumes it in both directions, as
`RelPoint.baseChangeDown` / `RelPoint.baseChangeUp` from
`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean` at the defining
cartesian square, and as `IsPullback.lift` at the level structure
(`Gamma0BaseChange.liesIn_iota_iff`).

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

**Both halves were split again the same day**, on the same principle —
put the citation on one side of a hypothesis and the formalisation on the
other — so that neither of the four leaves below carries both:

* item 2 became `exists_gamma0Datum_baseChange` (the `Γ₀(N)`-moduli
  problem is a FUNCTOR: base change as a construction, no `ℚ`, no `n`, no
  moduli scheme) and `exists_fullLevelStructure_cover_of_baseChange`
  (the finite étale `GL₂(ℤ/n)`-torsor), which receives the former as a
  hypothesis.  **The first of those is PROVEN**, the same day it was
  opened — so item 2 is now exactly the torsor and nothing else;
* item 1 became `exists_rigidifiedModuli` (Katz–Mazur 4.7, 5.1.1, 6.6.1
  and the affineness parenthesis of 8.1.1, and NOTHING else) and
  `exists_gamma0GITPresentation_of_rigidified` (deck group, invariants,
  fppf descent of the classifying map, and NO citation), which receives
  the former as a parameter.

The second of those needed a structure to be interposed, and the
junk-witness objection above applies to it verbatim — the escape is that
`RigidifiedModuli`'s universal property is a **fine** moduli property,
which pins its inhabitant up to unique isomorphism, whereas the rejected
`Gamma0Rigidification` pinned nothing.  See `RigidifiedModuli`'s
docstring.  Note this also *strengthens* what is available downstream:
`exists_gamma0GITPresentation_of_rigidified` can compare two full level
structures over a base and get a locally constant `GL₂(ℤ/n)`-valued
answer, which is exactly the "torsor property" the paragraph below finds
missing from `dM_equivariant`.

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

/-! #### Base change of a `Γ₀(N)`-datum, as a construction

The `Γ₀(N)`-moduli problem is a FUNCTOR: every datum pulls back along
every `h : T' ⟶ T`.  `exists_fullLevelStructure_cover`'s docstring
recorded this as "what it needs that this project does not have"; it was
split off as its own leaf on 2026-07-27 and PROVEN the same day.  The
construction is here and the leaf is `exists_gamma0Datum_baseChange`
below.

Everything rests on `AbelianSchemeStruct.baseChange`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`) and its bijection
`RelPoint.baseChangeDown` / `RelPoint.baseChangeUp` on relative points,
which is why this file now carries that import.  The only genuinely new
work is the level structure, and its two non-formal steps are:

* `iota` is a base change of `d.cyc.ι` — obtained by pullback PASTING
  (`IsPullback.of_bot`) rather than by definition, because `C'` is built
  as `C ×_T T'` (which makes `IsFinite` and `Flat` of `ι' ≫ f'`
  immediate, those being properties of the composite) and the closed
  immersion then has to be recovered;
* `geom_cyclic`, where the generator at a geometric point `t` of `T'` is
  the one at `t ≫ h` transported by `baseChangeUp`, and `addOrderOf` and
  `AddSubgroup.zmultiples` transport because `baseChangeDown` is an
  injective additive map (`downHom`).
-/

namespace Gamma0BaseChange

open CategoryTheory.Limits

variable {N : ℕ} {T' T : Scheme.{u}} (h : T' ⟶ T) (d : Gamma0Datum N T)

/-- the projection of the base-changed total space to `E` -/
noncomputable abbrev qq : pullback d.f h ⟶ d.E := pullback.fst d.f h

/-- the structure morphism of the base-changed total space -/
noncomputable abbrev fb : pullback d.f h ⟶ T' := pullback.snd d.f h

/-- the base-changed level subscheme, built as `C ×_T T'` -/
noncomputable abbrev Cb : Scheme.{u} := pullback (d.cyc.ι ≫ d.f) h

/-- its projection to `C` -/
noncomputable abbrev cq : Cb h d ⟶ d.cyc.C := pullback.fst (d.cyc.ι ≫ d.f) h

/-- its projection to `T'` -/
noncomputable abbrev cp : Cb h d ⟶ T' := pullback.snd (d.cyc.ι ≫ d.f) h

/-- the inclusion of the base-changed level subscheme into the
base-changed total space -/
noncomputable def iota : Cb h d ⟶ pullback d.f h :=
  pullback.lift (cq h d ≫ d.cyc.ι) (cp h d) (by
    rw [Category.assoc]; exact pullback.condition)

lemma iota_snd : iota h d ≫ fb h d = cp h d := pullback.lift_snd _ _ _

lemma iota_fst : iota h d ≫ qq h d = cq h d ≫ d.cyc.ι := pullback.lift_fst _ _ _

/-- **`iota` is a base change of `d.cyc.ι`** — pullback pasting: the outer
square `C ×_T T'` and the lower square `E ×_T T'` are cartesian, hence so
is the upper one. -/
lemma isPullback_iota : IsPullback (cq h d) (iota h d) d.cyc.ι (qq h d) := by
  refine IsPullback.of_bot ?_ (iota_fst h d).symm (IsPullback.of_hasPullback d.f h)
  rw [iota_snd]
  exact IsPullback.of_hasPullback (d.cyc.ι ≫ d.f) h

lemma isClosedImmersion_iota : IsClosedImmersion (iota h d) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_iota h d) d.cyc.isClosedImmersion

lemma isFinite_iota_comp : IsFinite (iota h d ≫ fb h d) := by
  rw [iota_snd]
  haveI := d.cyc.isFinite
  infer_instance

lemma flat_iota_comp : AlgebraicGeometry.Flat (iota h d ≫ fb h d) := by
  rw [iota_snd]
  haveI := d.cyc.flat
  infer_instance

/-- **Lying in the base-changed level subscheme is lying in the original
one.**  The `←` direction is exactly where cartesianness of
`isPullback_iota` is consumed. -/
lemma liesIn_iota_iff {U : Scheme.{u}} {g : U ⟶ T'} (x : RelPoint (fb h d) g) :
    RelPoint.LiesIn (iota h d) x ↔
      RelPoint.LiesIn d.cyc.ι (RelPoint.baseChangeDown h x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ cq h d, ?_⟩
    show (y ≫ cq h d) ≫ d.cyc.ι = x.1 ≫ qq h d
    rw [Category.assoc, ← iota_fst h d, ← Category.assoc, hy]
  · rintro ⟨z, hz⟩
    have hz' : z ≫ d.cyc.ι = x.1 ≫ qq h d := hz
    exact ⟨(isPullback_iota h d).lift z x.1 hz',
      (isPullback_iota h d).lift_snd z x.1 hz'⟩

/-- **`baseChangeDown` as an additive map on relative points.**  This is
what carries `addOrderOf` and `AddSubgroup.zmultiples` between the two
sides in `geom_cyclic`; it is injective by
`RelPoint.baseChangeDown_injective`. -/
noncomputable def downHom {U : Scheme.{u}} (g : U ⟶ T') :
    letI := (d.ab.baseChange h).addCommGroup g
    letI := d.ab.addCommGroup (g ≫ h)
    RelPoint (fb h d) g →+ RelPoint d.f (g ≫ h) :=
  letI := (d.ab.baseChange h).addCommGroup g
  letI := d.ab.addCommGroup (g ≫ h)
  { toFun := RelPoint.baseChangeDown h
    map_zero' := by
      show RelPoint.baseChangeDown h ((d.ab.baseChange h).zero g) = d.ab.zero (g ≫ h)
      rw [AbelianSchemeStruct.baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]
    map_add' := by
      intro x y
      show RelPoint.baseChangeDown h ((d.ab.baseChange h).add x y)
          = d.ab.add (RelPoint.baseChangeDown h x) (RelPoint.baseChangeDown h y)
      rw [AbelianSchemeStruct.baseChange_add, RelPoint.baseChangeDown_baseChangeUp] }

lemma downHom_apply {U : Scheme.{u}} (g : U ⟶ T') (x : RelPoint (fb h d) g) :
    downHom h d g x = RelPoint.baseChangeDown h x := rfl

/-- **The base-changed cyclic subgroup scheme of order `N`.** -/
noncomputable def cycBC : CyclicSubgroupOfOrder (d.ab.baseChange h) N where
  C := Cb h d
  ι := iota h d
  isClosedImmersion := isClosedImmersion_iota h d
  isFinite := isFinite_iota_comp h d
  flat := flat_iota_comp h d
  zero_liesIn := by
    intro U g
    rw [liesIn_iota_iff]
    show RelPoint.LiesIn d.cyc.ι
      (RelPoint.baseChangeDown h ((d.ab.baseChange h).zero g))
    rw [AbelianSchemeStruct.baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]
    exact d.cyc.zero_liesIn (g ≫ h)
  add_liesIn := by
    intro U g x y hx hy
    rw [liesIn_iota_iff] at hx hy ⊢
    show RelPoint.LiesIn d.cyc.ι
      (RelPoint.baseChangeDown h ((d.ab.baseChange h).add x y))
    rw [AbelianSchemeStruct.baseChange_add, RelPoint.baseChangeDown_baseChangeUp]
    exact d.cyc.add_liesIn hx hy
  neg_liesIn := by
    intro U g x hx
    rw [liesIn_iota_iff] at hx ⊢
    show RelPoint.LiesIn d.cyc.ι
      (RelPoint.baseChangeDown h ((d.ab.baseChange h).neg x))
    show RelPoint.LiesIn d.cyc.ι
      (RelPoint.baseChangeDown h
        (RelPoint.baseChangeUp h (d.ab.neg (RelPoint.baseChangeDown h x))))
    rw [RelPoint.baseChangeDown_baseChangeUp]
    exact d.cyc.neg_liesIn hx
  geom_cyclic := by
    intro K _ _ t
    letI := (d.ab.baseChange h).addCommGroup t
    letI := d.ab.addCommGroup (t ≫ h)
    obtain ⟨y, hy1, hy2, hy3⟩ := d.cyc.geom_cyclic K (t ≫ h)
    have hinj : Function.Injective (downHom h d t) :=
      RelPoint.baseChangeDown_injective h
    have hdu : ∀ z : RelPoint d.f (t ≫ h),
        downHom h d t (RelPoint.baseChangeUp h z) = z :=
      fun z => RelPoint.baseChangeDown_baseChangeUp h z
    refine ⟨RelPoint.baseChangeUp h y, ?_, ?_, ?_⟩
    · rw [liesIn_iota_iff, ← downHom_apply, hdu]
      exact hy1
    · rw [← addOrderOf_injective (downHom h d t) hinj, hdu]
      exact hy2
    · intro x
      rw [liesIn_iota_iff, ← downHom_apply, hy3]
      constructor
      · rintro ⟨k, hk⟩
        have hk' : k • y = downHom h d t x := hk
        refine ⟨k, hinj ?_⟩
        show downHom h d t (k • RelPoint.baseChangeUp h y) = downHom h d t x
        rw [map_zsmul, hdu]
        exact hk'
      · rintro ⟨k, hk⟩
        have hk' : k • RelPoint.baseChangeUp h y = x := hk
        refine ⟨k, ?_⟩
        show k • y = downHom h d t x
        rw [← hdu y, ← map_zsmul]
        exact congrArg (downHom h d t) hk'

/-- **The base-changed `Γ₀(N)`-datum.** -/
noncomputable def datumBC : Gamma0Datum N T' where
  E := pullback d.f h
  f := fb h d
  ab := d.ab.baseChange h
  relativeDimensionOne :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      (IsPullback.of_hasPullback d.f h) d.relativeDimensionOne
  cyc := cycBC h d

/-- **And it IS a base change**, with the cartesian square the defining
one and all three compatibilities holding because
`RelPoint.along (qq h d) _` and `RelPoint.baseChangeDown h` are the same
function. -/
noncomputable def isBaseChangeBC : IsBaseChangeOf h (datumBC h d) d where
  map := qq h d
  isPullback := (IsPullback.of_hasPullback d.f h).flip
  map_zero := by
    intro U g
    show RelPoint.baseChangeDown h ((d.ab.baseChange h).zero g) = d.ab.zero (g ≫ h)
    rw [AbelianSchemeStruct.baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]
  map_add := by
    intro U g x y
    show RelPoint.baseChangeDown h ((d.ab.baseChange h).add x y)
        = d.ab.add (RelPoint.baseChangeDown h x) (RelPoint.baseChangeDown h y)
    rw [AbelianSchemeStruct.baseChange_add, RelPoint.baseChangeDown_baseChangeUp]
  liesIn_iff := by
    intro U g x
    exact liesIn_iota_iff h d x

end Gamma0BaseChange

/-- **Base change of a `Γ₀(N)`-datum, as a CONSTRUCTION** (PROVEN
2026-07-27, on the day it was split out of
`exists_fullLevelStructure_cover` below, whose docstring recorded exactly
this as the one thing it needed that the project does not have).

Given any `h : T' ⟶ T` and any datum over `T`, there is a datum over `T'`
which is a base change of it.  Nothing here mentions the level `n`, `ℚ`,
or any moduli scheme: it is the statement that the `Γ₀(N)`-moduli problem
is a FUNCTOR, and `exists_fullLevelStructure_cover_of_baseChange` consumes
it purely to produce the datum living on the cover.

## How it is proven

`E' = E ×_T T'`, `f' = pullback.snd d.f h`, and the three components are
built in the `Gamma0BaseChange` namespace above:

* the abelian-scheme structure is `AbelianSchemeStruct.baseChange`
  (`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`), with the bijection
  `RelPoint.baseChangeDown` / `RelPoint.baseChangeUp` on relative points
  and `baseChange_add` / `baseChange_zero`.  **This file now imports that
  module**, which was the anticipated cost; the import creates no cycle,
  since `AbelianSchemeIsogeny.lean`'s only project import is
  `Fermat.FLT.Modularity.AbelianScheme`.
* `relativeDimensionOne` is mathlib's
  `smoothOfRelativeDimension_isStableUnderBaseChange`
  (`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`), which is a `lemma`
  and NOT an instance — `infer_instance` does not find it, unlike the
  `IsFinite` and `Flat` cases below.
* the level structure is `Gamma0BaseChange.cycBC`.  `C'` is built as
  `C ×_T T'`, so `IsFinite` and `Flat` of `ι' ≫ f'` — which is what the
  structure actually asks for — are immediate; the price is that
  `IsClosedImmersion ι'` must be recovered by pullback PASTING
  (`IsPullback.of_bot`, in `isPullback_iota`) instead of holding by
  definition.

  The step with real content is `geom_cyclic`: a geometric point
  `t : Spec K ⟶ T'` is carried to `t ≫ h` and the generator produced there
  is transported by `RelPoint.baseChangeUp`.  That `baseChangeDown` is a
  bijection preserving `LiesIn` and the group law is `liesIn_iota_iff`
  together with `downHom`; `addOrderOf` and `AddSubgroup.zmultiples`
  transport because `downHom` is an INJECTIVE additive map, via
  `addOrderOf_injective` and `map_zsmul`.

  Note this consumes the fact `IsBaseChangeOf`'s docstring used to call
  "a fact this development never needs and therefore never proves"; that
  sentence has been corrected.

Stated at universe `u` rather than at `0` because nothing in it is
specific to the modular-curve layer. -/
theorem exists_gamma0Datum_baseChange {N : ℕ} {T' T : Scheme.{u}} (h : T' ⟶ T)
    (d : Gamma0Datum N T) :
    ∃ d' : Gamma0Datum N T', Nonempty (IsBaseChangeOf h d' d) :=
  ⟨Gamma0BaseChange.datumBC h d, ⟨Gamma0BaseChange.isBaseChangeBC h d⟩⟩

/-- **The level-`n` torsor** (sorry leaf, opened 2026-07-27) — what
remains of `exists_fullLevelStructure_cover` once base change is supplied
as the hypothesis `hbc`.

## What the prover of this node owes, and what it does NOT

Owes: that over a `ℚ`-scheme the full level-`n` structures on an elliptic
scheme form a finite étale `GL₂(ℤ/n)`-torsor.  Concretely — `n` is
invertible on a `ℚ`-scheme, so `E[n] ⟶ T` is finite étale of rank `n²`
(Katz–Mazur 2.3.1; Silverman *AEC* III.6.4 for the fibres, plus flatness
of the multiplication-by-`n` kernel), hence the sheaf
`Isom_T((ℤ/n)²_T, E[n])` is representable by a finite étale
`GL₂(ℤ/n)`-torsor `T' ⟶ T`, in particular flat, surjective and
quasi-compact; and the tautological isomorphism over `T'` is a full
level-`n` structure on the pulled-back datum.  Katz–Mazur (8.1.1) is the
citation for rigidifying by `[Γ(n)]`-structures at `n ≥ 3`.

Does NOT owe: the production of `d'` itself.  That is `hbc`, and it is a
hypothesis here — apply it to the `p : T' ⟶ T` this node builds.

## Faithfulness

`hbc` is a Prop-valued hypothesis, not an under-determined structure, so
this node cannot be false for the junk-witness reason discussed in the
section comment above; and it is not vacuous, because `hbc` is TRUE (it is
the statement of `exists_gamma0Datum_baseChange`).  The conclusion is
verbatim that of `exists_fullLevelStructure_cover`, so nothing is weakened.

`hn` is load-bearing for TRUTH exactly as on the parent: at `n = 0` a
`FullLevelStructure` is unsatisfiable. -/
theorem exists_fullLevelStructure_cover_of_baseChange {N : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (hbc : ∀ {U V : Scheme.{0}} (h : U ⟶ V) (d₀ : Gamma0Datum N V),
      ∃ d' : Gamma0Datum N U, Nonempty (IsBaseChangeOf h d' d₀))
    {T : Scheme.{0}} (g : T ⟶ SpecQ) (d : Gamma0Datum N T) :
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma0Datum N T'),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      Nonempty (IsBaseChangeOf p d' d) ∧ Nonempty (FullLevelStructure n d') :=
  sorry

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

## What it needs that this project does not have — NOW A SEPARATE LEAF

Base change of a `Γ₀(N)`-datum as a **construction**: `d'` must be
produced, not merely related to `d`.  That is **no longer part of this
declaration** (2026-07-27): it is
`exists_gamma0Datum_baseChange` immediately below, and this leaf is
`exists_fullLevelStructure_cover_of_baseChange`, which receives it as a
hypothesis and so owes only the torsor.  The two are assembled here.

`hn` is load-bearing for TRUTH, not merely for the intended proof: at
`n = 0` the conclusion asks for an unsatisfiable `FullLevelStructure`
(see its docstring), so it cannot be dropped. -/
theorem exists_fullLevelStructure_cover {N : ℕ} (n : ℕ) (hn : 3 ≤ n)
    {T : Scheme.{0}} (g : T ⟶ SpecQ) (d : Gamma0Datum N T) :
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma0Datum N T'),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      Nonempty (IsBaseChangeOf p d' d) ∧ Nonempty (FullLevelStructure n d') :=
  exists_fullLevelStructure_cover_of_baseChange n hn
    (fun {_ _} h d₀ => exists_gamma0Datum_baseChange h d₀) g d

/-- **The rigidified moduli scheme `𝔐([Γ₀(N)], [Γ(n)])`, as a FINE
moduli scheme which is AFFINE** — Katz–Mazur (8.1.1).

The data is an affine `ℚ`-scheme `Spec A`, a universal `Γ₀(N)`-datum `dM`
on it carrying a universal full level-`n` structure `lvlM`, and the fine
moduli property: every datum-with-level-structure over a `ℚ`-scheme is
the base change of `(dM, lvlM)` along a **unique** morphism.

## Why this is NOT the junk-witness trap

The section comment above rejects the "obvious" split precisely because
an arbitrary inhabitant of a `Gamma0Rigidification`-shaped structure need
not be the genuine moduli scheme — the fields did not pin it, so the
companion leaf `∀ R, «cover» R` would have been FALSE at the junk
witness.  `universal` here is a **fine** moduli property, and a fine
moduli scheme is pinned up to unique isomorphism by it: the junk witness
`A = ℚ`, `G = 1`, `dM` a single datum fails `universal` as soon as the
rigidified problem has two non-isomorphic objects over some base.  So
quantifying over `RigidifiedModuli N n` — which is what
`exists_gamma0GITPresentation_of_rigidified` does — is safe, and that is
what lets the citation and the assembly be separated at all.

## Level compatibility is stated on the underlying morphisms

`IsBaseChangeOf` compares only the `Γ₀(N)`-data, so on its own it would
make `m` far from unique (the classifying map of a `Γ₀(N)`-datum is not
unique; that is the whole reason for rigidifying).  The two equations
pin the level structure as well.  They are stated between morphisms
`T ⟶ dM.E` rather than between relative points because
`RelPoint.along bc.map _ L.P` lands over `𝟙 T ≫ m` while
`RelPoint.pre m _ lvlM.P` lands over `m`, and `𝟙 T ≫ m = m` holds
propositionally but not definitionally, so the two relative points
inhabit different types.  Unfolding both to `.1` — `L.P.1 ≫ bc.map` and
`m ≫ lvlM.P.1` — removes the transport with no loss.

## The structure morphism needs no compatibility field

A morphism `T ⟶ Spec ℚ` is unique when it exists, because `ℚ` is initial
in `CommRing` and `Hom(T, Spec R) ≅ Hom(R, Γ(T, 𝒪))`.  So `m ≫ strM = g`
is automatic and stating it would be redundant — the same reason
`Gamma0Atlas.cover`'s repaired binder is written `_g`.

`hn : 3 ≤ n` is load-bearing for TRUTH of the existence statement below:
at `n ≤ 2` the rigidified problem still has the automorphism `-1` (and
more at `n = 1`), so it is not representable and no inhabitant exists. -/
structure RigidifiedModuli (N n : ℕ) where
  /-- the coordinate ring of the rigidified moduli scheme -/
  A : Type
  [commRing_A : CommRing A]
  /-- the structure morphism to `Spec ℚ` -/
  strM : Spec (CommRingCat.of A) ⟶ SpecQ
  /-- the universal `Γ₀(N)`-datum -/
  dM : Gamma0Datum N (Spec (CommRingCat.of A))
  /-- the universal full level-`n` structure on it -/
  lvlM : FullLevelStructure n dM
  /-- **fine moduli**: a datum-with-level-structure over a `ℚ`-scheme is
  a base change of `(dM, lvlM)` along a UNIQUE morphism -/
  universal : ∀ {T : Scheme.{0}} (_g : T ⟶ SpecQ) (d : Gamma0Datum N T)
      (L : FullLevelStructure n d),
    ∃! m : T ⟶ Spec (CommRingCat.of A),
      ∃ bc : IsBaseChangeOf m d dM,
        L.P.1 ≫ bc.map = m ≫ lvlM.P.1 ∧ L.Q.1 ≫ bc.map = m ≫ lvlM.Q.1

/-- **Katz–Mazur representability: the rigidified moduli scheme exists and
is affine** (sorry leaf, opened 2026-07-27) — the pure CITATION half of
`exists_gamma0GITPresentation_of_cover` below.

## What the prover of this node owes

Exactly the four citations that `exists_gamma0GITPresentation`'s
itemisation records, and nothing else:

* **Katz–Mazur 4.7** and **5.1.1** — `[Γ(n)]` is representable, and
  affine and smooth over `(Ell/ℤ[1/n])`, for `n ≥ 3`.  Over a
  `ℚ`-scheme every `n` is invertible.
* **Katz–Mazur 6.6.1** — `[Γ₀(N)]` is relatively representable, finite
  and flat over `(Ell)`.
* the parenthesis of **(8.1.1)**, that a relatively representable affine
  problem over a representable affine one has an affine total moduli
  scheme: "exists because `𝔐(𝒫, 𝒮)` is itself affine".

The fine moduli property `universal` is what "representable" means; the
affineness is what `A : Type` with the moduli scheme spelled
`Spec (CommRingCat.of A)` records.

## What it does NOT owe

Nothing about `GL₂(ℤ/n)`, invariants, descent, or the coarse space.  All
of that is `exists_gamma0GITPresentation_of_rigidified`, which is a
formalisation task with no citation left in it.

## Faithfulness

`hn` is load-bearing for TRUTH (see `RigidifiedModuli`'s docstring: at
`n ≤ 2` the rigidified problem has automorphisms and is not
representable).  `hN` is **not** — at `N = 0` the moduli problem is
supported on the empty scheme (`isEmpty_of_gamma0Datum_zero` above) and
`A = 0` represents it — and is carried only to match the signature of the
consumer below. -/
theorem exists_rigidifiedModuli (N : ℕ) (hN : 0 < N) (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (RigidifiedModuli N n) :=
  sorry

/-- **The GIT presentation, assembled from the fine moduli scheme and the
level torsor** (sorry leaf, opened 2026-07-27) — the pure FORMALISATION
half of `exists_gamma0GITPresentation_of_cover` below, with the
Katz–Mazur citation discharged by `R` and the torsor by `hcov`.

## What the prover of this node owes, and what it does NOT

Owes, and every step of it is available in principle from `R` alone:

* **the deck group and its action on `A`.**  For `σ : GL₂(ℤ/n)` the pair
  `(R.dM, σ · R.lvlM)` is again a rigidified datum over `Spec R.A` — a
  matrix acts on a full level structure by `(P, Q) ↦ (aP + bQ, cP + dQ)`,
  and `geom_basis` is preserved exactly because the matrix is invertible
  mod `n`.  `R.universal` classifies it by a unique endomorphism of
  `Spec R.A`, which is an automorphism because `σ⁻¹` gives the inverse,
  and `Spec` is fully faithful on affines, so this is a
  `MulSemiringAction (GL₂(ℤ/n)) R.A`.  `Finite` is `Finite (GL₂(ZMod n))`.
* **`B` and `Algebra.IsInvariant`**: take `B` the fixed subring; then
  `Algebra.IsInvariant B A G` and injectivity of `algebraMap B A` hold by
  construction.
* **`classify`, by fppf descent along the torsor.**  Given `d` over a
  `ℚ`-scheme `T`, `hcov` gives a flat surjective quasi-compact
  `p : T' ⟶ T` with `d'` and a full level structure; `R.universal`
  classifies `(d', L')` by `m : T' ⟶ Spec A`; and `m ≫ π` descends along
  `p` because `AlgebraicGeometry.fpqcTopology` is `Subcanonical` and
  `p` is an `EffectiveEpi` (the two facts
  `Gamma0Atlas.toIsCoarseModuliY0` already runs on).
* **the descent datum, which is where the real content is.**  On
  `T' ×_T T'` the two pullbacks of `(d', L')` share their `Γ₀(N)`-datum
  and differ only in the level structure, so the two classifying maps
  differ by the `GL₂(ℤ/n)`-valued *comparison* of two full level
  structures.  That comparison is **locally constant**, not global — this
  is the same obstruction the section comment above records against the
  naive descent route — but here it suffices: locally constant means a
  finite clopen decomposition of `T' ×_T T'`, on each piece the two maps
  differ by composition with a global `Spec σ`, and `π ∘ Spec σ = π`, so
  the two composites with `π` agree piecewise and hence globally.  **This
  is exactly what the fine moduli property buys and `dM_equivariant`
  alone does not**, and it is why the citation had to be interposed as a
  fine moduli scheme rather than as a bare rigidification.
* `classify_dM` then holds because the descent is independent of the
  chosen cover and `(R.dM, R.lvlM)` is already rigidified over
  `Spec A` itself, so the trivial cover `𝟙` computes it as `π`; and
  `dM_equivariant` is the action above, read back through `R.universal`.

Does NOT owe: any Katz–Mazur citation.  Representability is `R`; the
torsor is `hcov`.

## Faithfulness

Both `R` and `hcov` are non-degenerate — `R` is pinned by a fine moduli
property (see `RigidifiedModuli`) rather than being an under-determined
structure, and `hcov` is a Prop which is TRUE (it is the statement of
`exists_fullLevelStructure_cover`).  So this node is neither false for
the junk-witness reason nor vacuous, and its conclusion carries the full
strength of `Nonempty (Gamma0GITPresentation N)`. -/
theorem exists_gamma0GITPresentation_of_rigidified (N : ℕ) (hN : 0 < N)
    (n : ℕ) (hn : 3 ≤ n) (R : RigidifiedModuli N n)
    (hcov : ∀ {T : Scheme.{0}}, (T ⟶ SpecQ) → ∀ d : Gamma0Datum N T,
      ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma0Datum N T'),
        AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
        Nonempty (IsBaseChangeOf p d' d) ∧ Nonempty (FullLevelStructure n d')) :
    Nonempty (Gamma0GITPresentation N) :=
  sorry

/-- **Representability of the rigidified moduli problem** (PROVEN
2026-07-27 from the two halves it was split into) —
item 1 of the itemisation on `exists_gamma0GITPresentation` below, with
item 2 discharged by the hypothesis `hcov`.

Given that every `Γ₀(N)`-datum over a `ℚ`-scheme acquires a full
level-`n` structure fppf-locally — which is exactly
`exists_fullLevelStructure_cover` — the rigidified moduli scheme
`𝔐([Γ₀(N)], [Γ(n)])` exists as an AFFINE `ℚ`-scheme `Spec A` with the
finite deck group `G = GL₂(ℤ/n)` acting, carrying a universal family
`dM`, and the classifying map of `dM` is the quotient map onto
`Spec A^G`.

## What this node owed, and where each half now lives

It owed Katz–Mazur **4.7** and **5.1.1** (the moduli problem `[Γ(n)]` is
representable, and affine, over `(Ell/ℤ[1/n])` for `n ≥ 3`), **6.6.1**
(`[Γ₀(N)]` is relatively representable, finite and flat over `(Ell)`),
and the fact that a relatively representable affine problem over a
representable one has an affine total moduli scheme — which is precisely
Katz–Mazur's parenthesis in (8.1.1), "exists because `𝔐(𝒫, 𝒮)` is itself
affine" — and then the assembly of those into the presentation.

**Those two are now SEPARATE LEAVES** (2026-07-27): the whole citation is
`exists_rigidifiedModuli` above, which asserts nothing but that the
rigidified problem has an affine FINE moduli scheme; and the assembly —
deck group, invariants, fppf descent of the classifying map — is
`exists_gamma0GITPresentation_of_rigidified`, which contains no citation
at all.  The interposed structure is `RigidifiedModuli`, and its
docstring records why a *fine* moduli property escapes the junk-witness
trap that the section comment above rejects the naive split for.

Did NOT owe, and still does not: the torsor.  That is `hcov`, and it is a
hypothesis here, passed straight through to the assembly half.

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
  (exists_rigidifiedModuli N hN n hn).elim fun R =>
    exists_gamma0GITPresentation_of_rigidified N hN n hn R
      (fun {_T} g₀ d₀ => hcov g₀ d₀)

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

**And items 1 and 2 were each split once more, later the same day**, so
that no leaf carries both a citation and a formalisation task.  Item 1 is
now `exists_rigidifiedModuli` (the citation: 4.7, 5.1.1, 6.6.1, and the
affineness parenthesis of 8.1.1) plus
`exists_gamma0GITPresentation_of_rigidified` (the assembly); item 2 is now
`exists_gamma0Datum_baseChange` (functoriality of the moduli problem —
**PROVEN 2026-07-27**) plus
`exists_fullLevelStructure_cover_of_baseChange` (the torsor).  The refuting
checks recorded under each item below are still the right first thing to
run, and each new leaf carries its own.
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
`exists_projAdd`, `isProper_projToSpec`,
`smoothOfRelativeDimension_projToSpec`,
`geometricallyConnected_projToSpec`,
`exists_projGroupLaw_geomFibreAddEquiv` —
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
checked rather than assumed.  **Correction (2026-07-27): that module IS on
`main`** — the claim that it "is not on `main` at all" was true when
written and is now stale — but the substance of the objection stands:
everything in it — `flat_mulByNat`, `finite_preimage_mulByNat`,
`surjective_mulByNat`, and `AbelianSchemeStruct.baseChange` —
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

* `exists_projAdd` — items 5+6, the chord–tangent law `m` as a morphism
  plus the four group axioms.  This is the substantial geometric work.
  (`nonempty_projGroupLaw` is PROVEN from it: `e` and `i` are constructed
  outright as `projInfty` and `projNeg`.)
* `smoothOfRelativeDimension_projToSpec` — item 7a, descending the local
  Jacobian criterion along the affine cover of `Proj`.
* `geometricallyConnected_projToSpec` — item 7b.
* `isProper_projToSpec` — properness, which is `Proj.toSpecZero`'s
  properness plus the identification of the degree-zero part with `ℚ`.
* `exists_projGroupLaw_geomFibreAddEquiv` — item 8, the equivariant `≃+`,
  RESTATED 2026-07-27 with the group law bound EXISTENTIALLY.

All five are independent of each other.  The item-8 leaf no longer takes
a `ProjGroupLaw` argument: the earlier form quantified over an ARBITRARY
one, which pins nothing about `m`, and was therefore provable only
through the rigidity theorem.  `exists_projGeomFibreAddEquiv` survives
under its own name as a PROVEN consequence about the concrete
`projGroupLaw E`.  The item-8 leaf as restated SUBSUMES `exists_projAdd`
— a witness supplies `m` and `hassoc` too — so the two are candidates to
be merged into one cut; until then they are separately dispatchable. -/
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

/-! ### The affine/ring input to leaf (iii-b-1)

**Added 2026-07-27**, and it is the whole content of leaf (iii-b-1): the
square `Σ ×_ℚ Σ` is AFFINE, so the question is the commutative-algebra one
of whether `(J → ℚ̄) ⊗_ℚ (J → ℚ̄)` is separated by its `ℚ`-algebra maps to
`ℚ̄`.  It is, because that ring is REDUCED (`ℚ` is perfect, so `ℚ̄/ℚ` is
separable) and INTEGRAL over `ℚ` (so every residue field is algebraic over
`ℚ`, hence embeds in `ℚ̄`).

Everything in this section is stated over a VARIABLE base field `F` — see
`isIntegralHom_specAlgClos'` for the same discipline and the same reason:
at the literal `ℚ` the two `Algebra ℚ (AlgebraicClosure ℚ)` instances form
a diamond and `Algebra.IsAlgebraic ℚ ℚ̄` stops synthesising. -/

section GeomSquareRing

open scoped TensorProduct

/-- **Every finitely generated subalgebra of `F̄` is geometrically reduced
over a perfect field `F`** (PROVEN).

Such a `B` is a field (`Subalgebra.isField_of_algebraic`), algebraic over
`F` and essentially of finite type, so `PerfectField F` makes it separable
and hence formally unramified; base change carries that to `F̄ ⊗_F B`,
which `Algebra.FormallyUnramified.isReduced_of_field` then shows is
reduced.  That is exactly `Algebra.isGeometricallyReduced_field_iff`. -/
theorem isGeometricallyReduced_fg_subalgebra {F : Type} [Field F] [PerfectField F]
    (B : Subalgebra F (AlgebraicClosure F)) (hB : B.FG) :
    Algebra.IsGeometricallyReduced F B := by
  haveI : Algebra.IsAlgebraic F B := Algebra.IsAlgebraic.tower_bot_of_injective
    (A := AlgebraicClosure F) (Subtype.val_injective)
  haveI : Algebra.FiniteType F B := (Subalgebra.fg_iff_finiteType B).mp hB
  haveI : Algebra.EssFiniteType F B := inferInstance
  letI : Field B := (Subalgebra.isField_of_algebraic (K := F) (L := AlgebraicClosure F)
    (A := B)).toField
  haveI : Algebra.FormallyUnramified F B := Algebra.FormallyUnramified.of_isSeparable F B
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact Algebra.FormallyUnramified.isReduced_of_field (AlgebraicClosure F)
    (AlgebraicClosure F ⊗[F] B)

/-- **`F̄` is geometrically reduced over a perfect field `F`** (PROVEN):
`Algebra.IsGeometricallyReduced.of_forall_fg` reduces it to the finitely
generated subalgebras, which is the previous lemma.

Deliberately NOT an `instance`: this file is large and shared, and the
class is needed at exactly one place below. -/
theorem isGeometricallyReduced_algebraicClosure {F : Type} [Field F] [PerfectField F] :
    Algebra.IsGeometricallyReduced F (AlgebraicClosure F) :=
  Algebra.IsGeometricallyReduced.of_forall_fg (isGeometricallyReduced_fg_subalgebra (F := F))

/-- **`F̄ ⊗_F F̄` is integral over `F`** (PROVEN): the elementary tensors are
products `includeLeft a * includeRight b` of images of integral elements
under `F`-algebra maps, and integral elements are closed under `+` and `*`. -/
theorem isIntegral_tensor_algebraicClosure {F : Type} [Field F] :
    Algebra.IsIntegral F (AlgebraicClosure F ⊗[F] AlgebraicClosure F) := by
  constructor
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul a b =>
      have ha : IsIntegral F ((Algebra.TensorProduct.includeLeft (R := F) (S := F)
        (A := AlgebraicClosure F) (B := AlgebraicClosure F)) a) :=
        IsIntegral.map _ (Algebra.IsIntegral.isIntegral a)
      have hb : IsIntegral F ((Algebra.TensorProduct.includeRight (R := F)
        (A := AlgebraicClosure F) (B := AlgebraicClosure F)) b) :=
        IsIntegral.map _ (Algebra.IsIntegral.isIntegral b)
      have htm : a ⊗ₜ[F] b = (Algebra.TensorProduct.includeLeft (R := F) (S := F)
          (A := AlgebraicClosure F) (B := AlgebraicClosure F)) a *
        (Algebra.TensorProduct.includeRight (R := F)
          (A := AlgebraicClosure F) (B := AlgebraicClosure F)) b := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [htm]
      exact ha.mul hb
  | add x y hx hy => exact hx.add hy

/-- **`R` is separated by its `F`-algebra maps to `F̄`.**

This is the property that a family of `F̄`-points of `Spec R` needs in
order to be schematically dominant, written on the ring side where it is
provable. -/
def SeparatedByAlgHom (F R : Type) [Field F] [CommRing R] [Algebra F R] : Prop :=
  ∀ x : R, (∀ ψ : R →ₐ[F] AlgebraicClosure F, ψ x = 0) → x = 0

/-- **A reduced `F`-algebra integral over `F` is separated by its maps to
`F̄`** (PROVEN) — the arithmetic heart of leaf (iii-b-1).

If `x ≠ 0` then `x` is not nilpotent (reducedness), so `x` avoids some
prime `p`; `R ⧸ p` is a domain integral over the field `F`, hence itself a
field (`Algebra.IsIntegral.isField_iff_isField`) and algebraic over `F`,
so `IsAlgClosed.lift` embeds it in `F̄`.  The resulting `ψ` does not kill
`x`. -/
theorem separatedByAlgHom_of_isIntegral {F : Type} [Field F] (R : Type) [CommRing R]
    [Algebra F R] [IsReduced R] [Algebra.IsIntegral F R] : SeparatedByAlgHom F R := by
  intro x hx
  by_contra hne
  have hnil : ¬ IsNilpotent x := fun h => hne (IsReduced.eq_zero x h)
  rw [nilpotent_iff_mem_prime] at hnil
  push_neg at hnil
  obtain ⟨p, hp, hxp⟩ := hnil
  haveI : p.IsPrime := hp
  haveI : Algebra.IsIntegral F (R ⧸ p) := inferInstance
  haveI : Algebra.IsAlgebraic F (R ⧸ p) := Algebra.IsIntegral.isAlgebraic
  have hfield : IsField (R ⧸ p) := by
    refine (Algebra.IsIntegral.isField_iff_isField (R := F) (S := R ⧸ p) ?_).mp
      (Semifield.toIsField F)
    exact (algebraMap F (R ⧸ p)).injective
  letI : Field (R ⧸ p) := hfield.toField
  let ψ₀ : (R ⧸ p) →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let ψ : R →ₐ[F] AlgebraicClosure F := ψ₀.comp (Ideal.Quotient.mkₐ F p)
  have hψ : ψ x = 0 := hx ψ
  have hmk : (Ideal.Quotient.mk p) x ≠ 0 := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hxp
  exact hmk ((map_eq_zero_iff _ (RingHom.injective ψ₀.toRingHom)).mp hψ)

/-- **Separation transports along an `F`-algebra equivalence** (PROVEN). -/
theorem separatedByAlgHom_of_algEquiv {F : Type} [Field F] {R S : Type} [CommRing R]
    [CommRing S] [Algebra F R] [Algebra F S] (e : R ≃ₐ[F] S)
    (h : SeparatedByAlgHom F S) : SeparatedByAlgHom F R := by
  intro x hx
  have he : e x = 0 := h (e x) fun ψ => by
    simpa using hx (ψ.comp (e : R →ₐ[F] S))
  simpa using congrArg e.symm he

/-- **Separation passes to products** (PROVEN): project with
`Pi.evalAlgHom`. -/
theorem separatedByAlgHom_pi {F : Type} [Field F] {ι : Type} (R : ι → Type)
    [∀ i, CommRing (R i)] [∀ i, Algebra F (R i)] (h : ∀ i, SeparatedByAlgHom F (R i)) :
    SeparatedByAlgHom F (∀ i, R i) := by
  intro x hx
  funext i
  exact h i (x i) fun ψ => hx (ψ.comp (Pi.evalAlgHom F R i))

/-- **`F̄ ⊗_F F̄` is separated by its `F`-algebra maps to `F̄`** (PROVEN):
reduced, by `isGeometricallyReduced_algebraicClosure`, and integral, by
`isIntegral_tensor_algebraicClosure`. -/
theorem separatedByAlgHom_tensor_algebraicClosure {F : Type} [Field F] [PerfectField F] :
    SeparatedByAlgHom F (AlgebraicClosure F ⊗[F] AlgebraicClosure F) := by
  haveI := isGeometricallyReduced_algebraicClosure (F := F)
  haveI : IsReduced (AlgebraicClosure F ⊗[F] AlgebraicClosure F) := inferInstance
  haveI := isIntegral_tensor_algebraicClosure (F := F)
  exact separatedByAlgHom_of_isIntegral _

/-- **`(J → F̄) ⊗_F (J → F̄)` is separated by its `F`-algebra maps to `F̄`**
(PROVEN), for finite `J`.

`Algebra.TensorProduct.piRight` splits the tensor product over a finite
product of algebras, twice — once on each side, with
`Algebra.TensorProduct.comm` in between — leaving a `J × J`-indexed
product of copies of `F̄ ⊗_F F̄`. -/
theorem separatedByAlgHom_piTensorPi {F : Type} [Field F] [PerfectField F] (J : Type)
    [Finite J] :
    SeparatedByAlgHom F ((J → AlgebraicClosure F) ⊗[F] (J → AlgebraicClosure F)) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  refine separatedByAlgHom_of_algEquiv
    (Algebra.TensorProduct.piRight F F (J → AlgebraicClosure F)
      (fun _ : J => AlgebraicClosure F)) ?_
  refine separatedByAlgHom_pi _ fun _ => ?_
  refine separatedByAlgHom_of_algEquiv
    ((Algebra.TensorProduct.comm F (J → AlgebraicClosure F) (AlgebraicClosure F)).trans
      (Algebra.TensorProduct.piRight F F (AlgebraicClosure F)
        (fun _ : J => AlgebraicClosure F))) ?_
  exact separatedByAlgHom_pi _ fun _ => separatedByAlgHom_tensor_algebraicClosure

/-- **A separated `ℚ`-algebra `R` has `Spec R` schematically dominated by
its `ℚ̄`-points** (PROVEN) — the bridge from the ring statement to the ideal
sheaf one.

`Spec R` is affine, so `Scheme.ker_of_isAffine` reduces `ker = ⊥` to
injectivity of the map on global sections; that map is beaten below by
every `Sigma.ι ψ`, and `Scheme.ΓSpecIso_naturality` identifies the
resulting condition with `ψ r = 0` for every `ψ`.  NOTE the index type is
the FULL set of `ℚ`-algebra maps `R → ℚ̄`, which is not finite — see the
trap recorded in `exists_geomPts_ker_eq_bot_sigmaSq`. -/
theorem exists_ker_eq_bot_Spec (R : Type) [CommRing R] [Algebra ℚ R]
    (hsep : SeparatedByAlgHom ℚ R) :
    ∃ (I : Type) (w : I → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        Spec (CommRingCat.of R))), (geomPtDesc w).ker = ⊥ := by
  classical
  refine ⟨R →ₐ[ℚ] AlgebraicClosure ℚ,
    fun ψ => Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  set f : (∐ fun _ : (R →ₐ[ℚ] AlgebraicClosure ℚ) =>
      Spec (CommRingCat.of (AlgebraicClosure ℚ))) ⟶ Spec (CommRingCat.of R) :=
    Limits.Sigma.desc (fun ψ => Spec.map (CommRingCat.ofHom ψ.toRingHom)) with hf
  have hker : RingHom.ker f.appTop.hom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [RingHom.mem_ker] at hx
    have key : ∀ ψ : R →ₐ[ℚ] AlgebraicClosure ℚ,
        (Spec.map (CommRingCat.ofHom ψ.toRingHom)).appTop.hom x = 0 := by
      intro ψ
      have hcomp : Limits.Sigma.ι
          (fun _ : (R →ₐ[ℚ] AlgebraicClosure ℚ) =>
            Spec (CommRingCat.of (AlgebraicClosure ℚ))) ψ ≫ f
          = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
        rw [hf]; exact Limits.Sigma.ι_desc _ ψ
      rw [← hcomp, Scheme.Hom.comp_appTop]
      simp [hx]
    have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x = 0 := by
      apply hsep
      intro ψ
      have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ.toRingHom)
      have h2 : ((Spec.map (CommRingCat.ofHom ψ.toRingHom)).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom).hom x
          = ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
              CommRingCat.ofHom ψ.toRingHom).hom x :=
        congrArg (fun g => CommRingCat.Hom.hom g x) h1
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, key ψ, map_zero] at h2
      simpa using h2.symm
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    simpa using hinj (by simpa using hr)
  rw [geomPtDesc, ← hf, AlgebraicGeometry.Scheme.ker_of_isAffine, hker]
  apply AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine
  simp

/-- **The square of the tautological `ℚ̄`-point cover is schematically
dominated by its `ℚ̄`-points** (leaf (iii-b-1), split out 2026-07-27 and
**PROVEN 2026-07-27** by exactly the affine/ring route recorded below).

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
take.

**PROVEN 2026-07-27 along exactly that route**, with two corrections to
the sketch above that are worth recording because both looked harmless:

* The index type is `I := (R →ₐ[ℚ] ℚ̄)`, the `ℚ`-algebra maps — **not**
  `R →ₐ[ℚ̄] ℚ̄` as written above.  `R` carries no canonical `ℚ̄`-algebra
  structure in the statement (which of the two tensor factors would
  supply it?), and none is needed: the residue fields are algebraic over
  `ℚ` already, so `IsAlgClosed.lift` embeds them over `ℚ`.
* Reducedness does NOT go through `GeometricallyReduced` of the *scheme*
  morphism (item (a) above).  That class quantifies over ALL field
  extensions `K/ℚ`, and `IsReduced (A ⊗_ℚ K)` for arbitrary `K` is an
  explicit TODO in mathlib (`Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`).
  What is available, and all that is needed, is the *algebra* class
  `Algebra.IsGeometricallyReduced`, whose consumer instance requires the
  extension to be ALGEBRAIC — which `ℚ̄/ℚ` is.  An agent that reached for
  the scheme-level class would have hit mathlib's TODO and concluded the
  leaf was blocked.

The chain actually used, all of it stated over a variable base field: `ℚ`
is perfect, so every f.g. subalgebra of `ℚ̄` is a finite separable
extension and hence formally unramified; base change and
`Algebra.FormallyUnramified.isReduced_of_field` make `ℚ̄ ⊗_ℚ B` reduced;
`Algebra.IsGeometricallyReduced.of_forall_fg` passes to `ℚ̄` itself; and
`Algebra.TensorProduct.piRight` (twice, with `comm` between) reduces
`(J → ℚ̄) ⊗_ℚ (J → ℚ̄)` to a `J × J`-indexed product of copies of
`ℚ̄ ⊗_ℚ ℚ̄`.  Integrality is the one-line tensor induction
`isIntegral_tensor_algebraicClosure`.  See `separatedByAlgHom_piTensorPi`
and `exists_ker_eq_bot_Spec` in the `GeomSquareRing` section above. -/
theorem exists_geomPts_ker_eq_bot_sigmaSq (J : Type) [Finite J]
    (s : geomPtSigma J ⟶ SpecQ) :
    ∃ (I : Type) (w : I → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        Limits.pullback s s)), (geomPtDesc w).ker = ⊥ := by
  classical
  -- `Σ = ∐_J Spec ℚ̄` is `Spec (J → ℚ̄)`, because `J` is finite.
  haveI : IsIso (AlgebraicGeometry.sigmaSpec
      (fun _ : J => CommRingCat.of (AlgebraicClosure ℚ))) := inferInstance
  set eJ : geomPtSigma J ≅ Spec (CommRingCat.of (J → AlgebraicClosure ℚ)) :=
    asIso (AlgebraicGeometry.sigmaSpec (fun _ : J => CommRingCat.of (AlgebraicClosure ℚ)))
      with heJ
  set t : Spec (CommRingCat.of (J → AlgebraicClosure ℚ)) ⟶ SpecQ :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (J → AlgebraicClosure ℚ))) with ht
  -- `Spec ℚ` receives at most one morphism from anything, so `s` factors as `eJ.hom ≫ t`.
  have hst : s = eJ.hom ≫ t := (subsingleton_hom_specQ _).elim _ _
  have heq : t ≫ 𝟙 SpecQ = eJ.inv ≫ s := by
    rw [hst, Category.comp_id, Iso.inv_hom_id_assoc]
  set c : Limits.pullback t t ⟶ Limits.pullback s s :=
    Limits.pullback.map t t s s eJ.inv eJ.inv (𝟙 _) heq heq with hc
  haveI : IsIso c := by rw [hc]; infer_instance
  -- and the square of `Spec (J → ℚ̄)` over `Spec ℚ` is `Spec` of the tensor square.
  set e : Spec (CommRingCat.of ((J → AlgebraicClosure ℚ) ⊗[ℚ] (J → AlgebraicClosure ℚ))) ⟶
      Limits.pullback s s :=
    (AlgebraicGeometry.pullbackSpecIso ℚ (J → AlgebraicClosure ℚ)
      (J → AlgebraicClosure ℚ)).inv ≫ c with he
  haveI : IsIso e := by rw [he]; infer_instance
  obtain ⟨I, w₀, hw₀⟩ := exists_ker_eq_bot_Spec
    ((J → AlgebraicClosure ℚ) ⊗[ℚ] (J → AlgebraicClosure ℚ))
    (separatedByAlgHom_piTensorPi J)
  refine ⟨I, fun i => w₀ i ≫ e, ?_⟩
  have hdesc : geomPtDesc (fun i => w₀ i ≫ e) = geomPtDesc w₀ ≫ e := by
    rw [geomPtDesc, geomPtDesc]
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    conv_rhs => rw [← Category.assoc, Limits.Sigma.ι_desc]
  rw [hdesc]
  haveI : IsSchemeTheoreticallyDominant (geomPtDesc w₀) := ⟨hw₀⟩
  exact IsSchemeTheoreticallyDominant.ker_eq_bot _

end GeomSquareRing

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

## ROUTE AUDIT, 2026-07-27 — **SUPERSEDED** (see the PROVEN note above)

Kept rather than deleted because its TRAP paragraph states exactly the
fact that the residual leaf `exists_geomPts_ker_eq_bot_sigmaSq` isolates.
Its two proposed routes, and their shared quasi-compactness obligation,
were all avoided.

(by the agent that proved leaf (iii-a))

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

/-- **Two ring maps out of an integral `F`-algebra into `F̄` with the SAME
KERNEL differ by an element of `Gal(F̄/F)`** (PROVEN).  This is the ring
core of leaf (v-b-ii), and the only arithmetic in it.

Both maps kill `I := ker b`, so both factor through `κ := R ⧸ I`, which is
a DOMAIN (kernel of a map to a field) that is INTEGRAL over `F` (a
quotient of the integral `F`-algebra `R`), hence a FIELD by
`isField_of_isIntegral_of_isField'` — no artinian theory, no
`Ring.KrullDimLE`, and `I` is maximal only as a by-product
(`Ideal.Quotient.maximal_ideal_iff_isField_quotient`) of wanting the
`Field (R ⧸ I)` instance.

The extension of the resulting pair of `F`-embeddings `κ ↪ F̄` to an
automorphism of `F̄` is `AlgEquiv.liftNormal`, applied to the isomorphism
between the two `AlgHom.fieldRange`s.  **That detour through the two
ranges is not decoration: it is what avoids putting two `Algebra κ F̄`
instances on the same type**, which is where the direct
`IsAlgClosed.lift` route deadlocks.  `L₁ := B.fieldRange` and
`L₂ := A.fieldRange` are two DIFFERENT `IntermediateField F F̄`s, each
carrying exactly one canonical `Algebra ↥Lᵢ F̄` and one `IsScalarTower`,
so `AlgEquiv.liftNormal` applies with no instance juggling at all.

TWO TRAPS PAID FOR HERE, both worth reusing:

* **State this over a VARIABLE base field `F`, never at the literal `ℚ`.**
  `Normal ℚ (AlgebraicClosure ℚ)` runs into the `Rat`-algebra diamond that
  the docstring of `exists_injective_pre_geomBase` records; over a
  variable `F` it is just `IsAlgClosure.normal`.  Instantiating at `F = ℚ`
  afterwards is fine, because the statement itself pins the instance to
  `AlgebraicClosure.instAlgebra`, which is also the one inside
  `Field.absoluteGaloisGroup`.
* **`letI : Field (R ⧸ I) := Ideal.Quotient.field I` must come BEFORE the
  `AlgHom`s are built.**  Otherwise they are elaborated against
  `Ideal.Quotient.semiring I` and `AlgHom.equivFieldRange` — which derives
  its `Semiring` from the `Field` — rejects them with an application type
  mismatch on instance paths that print identically.

NOTE the two compatibility hypotheses `ha`/`hb`.  Over a variable `F` they
are genuinely needed (nothing forces `a ∘ ψ` to be the structure map); at
`F = ℚ` they are free, by `Rat.subsingleton_ringHom`. -/
theorem exists_algEquiv_comp_of_ker_eq {F : Type} [Field F] {R : Type} [CommRing R]
    (ψ : F →+* R) (hint : ψ.IsIntegral)
    (a b : R →+* AlgebraicClosure F)
    (ha : a.comp ψ = algebraMap F (AlgebraicClosure F))
    (hb : b.comp ψ = algebraMap F (AlgebraicClosure F))
    (hker : RingHom.ker a = RingHom.ker b) :
    ∃ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ r : R, σ (b r) = a r := by
  letI : Algebra F R := ψ.toAlgebra
  haveI : Algebra.IsIntegral F R := Algebra.isIntegral_def.mpr hint
  set I : Ideal R := RingHom.ker b with hIdef
  haveI : I.IsPrime := RingHom.ker_isPrime b
  haveI : Algebra.IsIntegral F (R ⧸ I) := by
    refine Algebra.isIntegral_def.mpr fun x => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Algebra.IsIntegral.isIntegral (R := F) r).map (Ideal.Quotient.mkₐ F I)
  have hfield : IsField (R ⧸ I) := isField_of_isIntegral_of_isField' (Field.toIsField F)
  haveI hmax : I.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr hfield
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hBz : ∀ r ∈ I, b r = 0 := fun r hr => hr
  have hAz : ∀ r ∈ I, a r = 0 := fun r hr => by rw [← hker] at hr; exact hr
  set A : (R ⧸ I) →+* AlgebraicClosure F := Ideal.Quotient.lift I a hAz with hA
  set B : (R ⧸ I) →+* AlgebraicClosure F := Ideal.Quotient.lift I b hBz with hB
  have hAmk : ∀ r : R, A (Ideal.Quotient.mk I r) = a r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hBmk : ∀ r : R, B (Ideal.Quotient.mk I r) = b r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hAcomm : ∀ x : F, A (algebraMap F (R ⧸ I) x) = algebraMap F (AlgebraicClosure F) x := by
    intro x
    have h1 : algebraMap F (R ⧸ I) x = Ideal.Quotient.mk I (ψ x) := rfl
    rw [h1, hAmk, ← ha]
    rfl
  have hBcomm : ∀ x : F, B (algebraMap F (R ⧸ I) x) = algebraMap F (AlgebraicClosure F) x := by
    intro x
    have h1 : algebraMap F (R ⧸ I) x = Ideal.Quotient.mk I (ψ x) := rfl
    rw [h1, hBmk, ← hb]
    rfl
  set A' : (R ⧸ I) →ₐ[F] AlgebraicClosure F := { A with commutes' := hAcomm } with hA'
  set B' : (R ⧸ I) →ₐ[F] AlgebraicClosure F := { B with commutes' := hBcomm } with hB'
  set e₁ : (R ⧸ I) ≃ₐ[F] B'.fieldRange := B'.equivFieldRange with he₁
  set e₂ : (R ⧸ I) ≃ₐ[F] A'.fieldRange := A'.equivFieldRange with he₂
  set ϕ : B'.fieldRange ≃ₐ[F] A'.fieldRange := e₁.symm.trans e₂ with hϕ
  refine ⟨ϕ.liftNormal (AlgebraicClosure F), fun r => ?_⟩
  have key := AlgEquiv.liftNormal_commutes ϕ (AlgebraicClosure F) (e₁ (Ideal.Quotient.mk I r))
  have hL : (algebraMap B'.fieldRange (AlgebraicClosure F)) (e₁ (Ideal.Quotient.mk I r))
      = b r := by
    show ((e₁ (Ideal.Quotient.mk I r) : B'.fieldRange) : AlgebraicClosure F) = b r
    rw [he₁, AlgHom.equivFieldRange_apply_coe]
    exact hBmk r
  have hR' : (algebraMap A'.fieldRange (AlgebraicClosure F)) (ϕ (e₁ (Ideal.Quotient.mk I r)))
      = a r := by
    have hϕe : ϕ (e₁ (Ideal.Quotient.mk I r)) = e₂ (Ideal.Quotient.mk I r) := by
      rw [hϕ]; simp
    rw [hϕe]
    show ((e₂ (Ideal.Quotient.mk I r) : A'.fieldRange) : AlgebraicClosure F) = a r
    rw [he₂, AlgHom.equivFieldRange_apply_coe]
    exact hAmk r
  rw [hL, hR'] at key
  exact key

/-- **Every `ℚ̄`-point of the span is a Galois translate of a member of the
family** (leaf (v-b-ii), split out 2026-07-27 — the arithmetic half of the
crux; **PROVEN 2026-07-27**).

Again the family is arbitrary: this is the statement that the
scheme-theoretic image of finitely many geometric points has no geometric
points beyond the `Γ_ℚ`-orbits of those it was built from.  Galois
stability of the family is NOT assumed and is not needed; it is the
PARENT that consumes stability, to turn the orbit back into `⟨y⟩`.

HOW IT CLOSED, and it is NOT the route the pin survey below prescribes.
Write `C := spanScheme p`, `R := Γ(C, ⊤)`, and let `w_j : Spec ℚ̄ ⟶ C` be
the factorisation of `p j` through the span (`geomPt_liesIn_spanScheme`).
Three steps:

* **Topology picks the index.**  `range_spanSchemeι_subset` (already
  proven in this file) says the support of `C` sits inside the finitely
  many image points of the family, and `spanSchemeι p` is a closed
  immersion, hence injective on points.  `Spec ℚ̄` is a ONE-POINT space,
  so the image point of `v` equals the image point of `w_j` for some `j`,
  and injectivity of `ι` on points transfers that equality up to `C`:
  `v.base o = (w_j).base o`.
* **`isoSpec` turns that into an equality of KERNELS.**  `C` is affine
  (`isAffine_spanScheme`), so `v` and `w_j` become ring maps
  `χ, χ_j : R → ℚ̄` and the structure morphism becomes an INTEGRAL
  `ψ : ℚ → R` (`isFinite_spanSchemeι`, then `IsIntegralHom.SpecMap_iff`)
  — exactly the transport `exists_geomPt_factor_span` already performs.
  `Spec.map_apply` is `rfl`, so `(Spec.map χ).base o` IS
  `PrimeSpectrum.comap χ o`; at the unique point `o = ⟨⊥, _⟩` of
  `Spec ℚ̄` its `asIdeal` is literally `ker χ`.  So the topological
  equality of points is DEFINITIONALLY `ker χ = ker χ_j`.
* **`exists_algEquiv_comp_of_ker_eq` above** turns equal kernels into
  `σ ∘ χ_j = χ` for a `σ ∈ Gal(ℚ̄/ℚ)`.  `Spec` is contravariant, so that
  is `v = specGal σ ≫ w_j`, and composing with `ι` gives the conclusion.

**THE PIN SURVEY BELOW WAS CORRECT AND IS NO LONGER THE CHEAPEST ROUTE —
BOTH OF ITS HARD STEPS ARE UNUSED.**  It is kept because its individual
claims are true and were checked, but a successor reading it should know:

* Its step 1, schematic dominance via `Scheme.Hom.toImage_app_injective`,
  is NOT needed.  Dominance was only ever wanted to force
  `⋂_j ker χ_j = 0`; the topological containment
  `range_spanSchemeι_subset` gives the strictly stronger and much cheaper
  fact that the point of `v` IS one of the points of the family, which
  hands over the index `j` directly instead of extracting it from a
  primality argument.
* Consequently its step 3 (`Ideal.IsPrime.inf_le'`) is unused, and so is
  the maximality of `ker χ_j` as an ingredient — maximality reappears
  only inside `exists_algEquiv_comp_of_ker_eq`, and only to obtain the
  `Field (R ⧸ I)` INSTANCE.
* **And the identification `Γ(∐_J Spec ℚ̄, ⊤) ≅ ∏_J ℚ̄`, recorded below as
  "the one step with no lemma found by name" and as "where a successor
  should expect the work to be", NEVER ARISES.**  The coproduct's global
  sections are not touched anywhere in the proof.  That is worth
  recording as a general lesson: the gap an audit identifies is a
  property of the route it chose, not of the leaf.

For the record, the survey's step 2 IS used (in
`exists_algEquiv_comp_of_ker_eq`), and its step 4 is replaced by
`AlgEquiv.liftNormal` — see that lemma's docstring for why the
`IsAlgClosed.lift` assembly it recommends deadlocks on duplicate
`Algebra κ ℚ̄` instances.

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
   example of exactly this assembly and is the thing to copy. -/
theorem exists_specGal_factor_span {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) {J : Type} [Finite J]
    (p : J → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ A))
    (hp : ∀ j, p j ≫ f = specAlgClos ℚ ≫ 𝟙 SpecQ)
    (v : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ spanScheme p) :
    ∃ (σ : Field.absoluteGaloisGroup ℚ) (j : J),
      v ≫ spanSchemeι p = specGal σ ≫ p j := by
  haveI := isAffine_spanScheme ab p hp
  haveI := isFinite_spanSchemeι ab p hp
  -- the unique point of `Spec ℚ̄`
  let o : ↑(Spec (CommRingCat.of (AlgebraicClosure ℚ))) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (AlgebraicClosure ℚ))
  -- STEP 1 (topology): the image point of `v` is the image point of some member
  have hsub := range_spanSchemeι_subset ab p hp
  obtain ⟨j, x, hx⟩ : ∃ j, ∃ x, (p j).base x = (spanSchemeι p).base (v.base o) := by
    simpa using hsub ⟨v.base o, rfl⟩
  obtain ⟨w, hw⟩ := geomPt_liesIn_spanScheme p j
  have hpt : v.base o = w.base o := by
    apply (spanSchemeι p).isClosedEmbedding.injective
    have h1 : (spanSchemeι p).base (w.base o) = (p j).base o := by rw [← hw]; rfl
    rw [h1, ← hx]
    congr 1
    exact Subsingleton.elim _ _
  -- STEP 2: transport `v`, `w` and the structure morphism across `isoSpec`
  haveI : IsFinite ((spanScheme p).isoSpec.inv ≫ spanSchemeι p ≫ f) := inferInstance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((spanScheme p).isoSpec.inv ≫ spanSchemeι p ≫ f)
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (v ≫ (spanScheme p).isoSpec.hom)
  obtain ⟨χj, hχj⟩ := Spec.map_surjective (w ≫ (spanScheme p).isoSpec.hom)
  have hint : ψ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hψ]
    infer_instance
  -- STEP 3: equal image points ARE equal kernels (`Spec.map_apply` is `rfl`)
  have hker : RingHom.ker χ.hom = RingHom.ker χj.hom := by
    have h2 : (Spec.map χ).base o = (Spec.map χj).base o := by
      rw [hχ, hχj]
      show (spanScheme p).isoSpec.hom.base (v.base o) = (spanScheme p).isoSpec.hom.base (w.base o)
      rw [hpt]
    exact congrArg PrimeSpectrum.asIdeal h2
  -- STEP 4: two embeddings of the residue field differ by a Galois element
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp_of_ker_eq ψ.hom hint χ.hom χj.hom
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) hker
  refine ⟨σ, j, ?_⟩
  have hcomp : χj ≫ CommRingCat.ofHom (σ.toAlgHom.toRingHom) = χ :=
    CommRingCat.hom_ext (RingHom.ext hσ)
  have hvw : v = specGal σ ≫ w := by
    refine (cancel_mono (spanScheme p).isoSpec.hom).mp ?_
    rw [Category.assoc, ← hχ, ← hχj, specGal, ← Spec.map_comp, hcomp]
  rw [← hw, ← Category.assoc, ← hvw]

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

**DECOMPOSED 2026-07-27 into `exists_geomPt_factor_span` and
`exists_specGal_factor_span` below, and BOTH are now PROVEN, so this node
has no open descendants.**  The split is along the two independent halves
of the argument above, and NEITHER half mentions the group law,
`hstable`, `hy` or `hN` — they are statements about an arbitrary finite
family of geometric points, exactly like leaf (i).  The full
`R ≅ ∏ κ_i` splitting is NOT needed for either: the first half needs only
that `R` is a finite `ℚ`-algebra, and the second — contrary to what this
paragraph said before the second half was proven — does NOT need "the
primes of an artinian ring are maximal" either.  It needs only that the
image point of a `ℚ̄`-point of `C` is one of the finitely many image
points of the family (`range_spanSchemeι_subset`), which hands over the
index directly; maximality survives only as the way
`exists_algEquiv_comp_of_ker_eq` obtains a `Field` instance on `R ⧸ I`.

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
over `exists_geomPt_factor_span` and `exists_specGal_factor_span`.  Leaf
(v-a) is PROVEN, and as of 2026-07-27 so are BOTH of those two, so the
whole (v) subtree is leaf-free.

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
| (iii-b-1) `exists_geomPts_ker_eq_bot_sigmaSq` | **PROVEN** 2026-07-27 — no leaf; the affine/ring route, over `separatedByAlgHom_piTensorPi` |
| (v-a) `exists_injective_pre_geomBase` | **PROVEN** — no leaf; `he` is `subsingleton_hom_specQ`, injectivity is `epi_specMap_of_fieldHom` |
| (v-b) `mem_zmultiples_of_liesIn_span` | PROVEN over (v-b-i), (v-b-ii) |
| (v-b-i) `exists_geomPt_factor_span` | **PROVEN** — no leaf; consumes leaf (i) `isFinite_spanSchemeι` |
| (v-b-ii) `exists_specGal_factor_span` | **PROVEN** 2026-07-27 — no leaf; `range_spanSchemeι_subset` picks the index, `isoSpec` turns equal image points into equal kernels, and `exists_algEquiv_comp_of_ker_eq` supplies `σ`. |

**EVERY ROW OF THIS TABLE IS NOW PROVEN** (verified at integration
2026-07-27 against the file's actual comment-stripped sorry set, not
inherited from any side of a merge): the last two to close were (iii-b-1)
`exists_geomPts_ker_eq_bot_sigmaSq` and (v-b-ii)
`exists_specGal_factor_span`, and the whole
`exists_ellipticScheme_of_weierstrass` subtree is LEAF-FREE.

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

FLATNESS is the fourth conjunct and it was FALSE as originally stated;
`flat_torsionι` now carries `[Etale (c.ι ≫ f)]` and is PROVEN.  Its
docstring keeps the counterexample that forced the hypothesis, together
with a record of the repair and of which consumers were threaded.  The
only leaf left in this section is
`CyclicSubgroupOfOrder.etale_of_specQBase` — Cartier's theorem, which is
what supplies that hypothesis over a `ℚ`-scheme. -/

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

/-! #### `[n]` and the zero section, RESTRICTED to `C`

These declarations are what the étale repair of `flat_torsionι`
needs, and they are the only place where the *subgroup* axioms of
`CyclicSubgroupOfOrder` are used geometrically rather than
point-theoretically.

The point is Yoneda at the TAUTOLOGICAL relative point.  `C` is given as
a subFUNCTOR of `h_E` — `zero_liesIn` / `add_liesIn` say that its points
are closed under the group law — and no morphism `C ⟶ C` is part of the
data.  But `ι : C ⟶ E`, read as a `C`-point of `E` (`tautPoint`), lies in
`C` tautologically, so `n • tautPoint` lies in `C` too, and a witness of
THAT is exactly a morphism `[n]_C : C ⟶ C` with `[n]_C ≫ ι = ι ≫ [n]`.
The same read at the zero section gives `e_C : T ⟶ C` with
`e_C ≫ ι = e`.  One test object, one point, no fibre products. -/

/-- **`C` is closed under `n • (-)`**, by induction on `n` from
`zero_liesIn` and `add_liesIn`. -/
theorem CyclicSubgroupOfOrder.liesIn_nsmul {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N)
    {T' : Scheme.{u}} {g : T' ⟶ T} (x : RelPoint f g) (hx : RelPoint.LiesIn c.ι x) (n : ℕ) :
    letI := ab.addCommGroup g
    RelPoint.LiesIn c.ι (n • x) := by
  letI := ab.addCommGroup g
  induction n with
  | zero => rw [zero_nsmul]; exact c.zero_liesIn g
  | succ k ih => rw [succ_nsmul]; exact c.add_liesIn ih hx

/-- **The tautological relative point**: `ι : C ⟶ E` read as a `C`-point
of `E` over the base point `ι ≫ f`. -/
def CyclicSubgroupOfOrder.tautPoint {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) :
    RelPoint f (c.ι ≫ f) :=
  ⟨c.ι, rfl⟩

/-- **The tautological point lies in `C`**, witnessed by `𝟙 C`. -/
theorem CyclicSubgroupOfOrder.tautPoint_liesIn {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) :
    RelPoint.LiesIn c.ι c.tautPoint :=
  ⟨𝟙 _, Category.id_comp _⟩

/-- **`[n]` restricts to `C`**: `liesIn_nsmul` at the tautological point,
with `nsmul_val` identifying `(n • tautPoint).1` as `ι ≫ [n]`. -/
theorem CyclicSubgroupOfOrder.exists_mulByNatRestrict {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ) :
    ∃ w : c.C ⟶ c.C, w ≫ c.ι = c.ι ≫ ab.mulByNat n := by
  letI := ab.addCommGroup (c.ι ≫ f)
  obtain ⟨w, hw⟩ := c.liesIn_nsmul c.tautPoint c.tautPoint_liesIn n
  exact ⟨w, by rw [hw, ab.nsmul_val n c.tautPoint]; rfl⟩

/-- **`[n]_C : C ⟶ C`.** -/
noncomputable def CyclicSubgroupOfOrder.mulByNatRestrict {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ) :
    c.C ⟶ c.C :=
  (c.exists_mulByNatRestrict n).choose

/-- **`[n]_C` restricts `[n]`**: `[n]_C ≫ ι = ι ≫ [n]`. -/
theorem CyclicSubgroupOfOrder.mulByNatRestrict_comp {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) (n : ℕ) :
    c.mulByNatRestrict n ≫ c.ι = c.ι ≫ ab.mulByNat n :=
  (c.exists_mulByNatRestrict n).choose_spec

/-- **The zero section factors through `C`** — this is `zero_liesIn` at
the base point `𝟙 T`, and `ab.zeroSection` is by definition
`(ab.zero (𝟙 T)).1`, so no rewriting is needed. -/
theorem CyclicSubgroupOfOrder.exists_zeroSectionSub {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) :
    ∃ z : T ⟶ c.C, z ≫ c.ι = ab.zeroSection :=
  c.zero_liesIn (𝟙 T)

/-- **The zero section of `C`, `e_C : T ⟶ C`.** -/
noncomputable def CyclicSubgroupOfOrder.zeroSectionSub {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) : T ⟶ c.C :=
  c.exists_zeroSectionSub.choose

/-- **`e_C ≫ ι = e`.** -/
theorem CyclicSubgroupOfOrder.zeroSectionSub_comp {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) :
    c.zeroSectionSub ≫ c.ι = ab.zeroSection :=
  c.exists_zeroSectionSub.choose_spec

/-- **`e_C` is a SECTION of `C ⟶ T`**, which is the whole reason it is
étale below: `e_C ≫ (ι ≫ f) = e ≫ f = 𝟙 T`. -/
theorem CyclicSubgroupOfOrder.zeroSectionSub_comp_str {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N) :
    c.zeroSectionSub ≫ (c.ι ≫ f) = 𝟙 T := by
  rw [← Category.assoc, c.zeroSectionSub_comp, ab.zeroSection_comp]

/-- **A section of an étale morphism is étale** (PROVEN), here for
`e_C : T ⟶ C`.

`e_C ≫ (ι ≫ f) = 𝟙 T` is étale, and `ι ≫ f` is étale hence locally of
finite type and formally unramified, so `Etale.of_comp` applies.  (This is
the scheme-theoretic form of "a section of an unramified separated
morphism is an open immersion"; only étaleness of the section is needed
below, so the open-immersion refinement is not proven here.) -/
theorem CyclicSubgroupOfOrder.etale_zeroSectionSub {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N)
    [AlgebraicGeometry.Etale (c.ι ≫ f)] :
    AlgebraicGeometry.Etale c.zeroSectionSub := by
  haveI : AlgebraicGeometry.Etale (c.zeroSectionSub ≫ (c.ι ≫ f)) := by
    rw [c.zeroSectionSub_comp_str]; infer_instance
  exact AlgebraicGeometry.Etale.of_comp _ (c.ι ≫ f)

/-- **`C[n] ⟶ C` is étale** (PROVEN), because it is a BASE CHANGE of the
zero section `e_C : T ⟶ C` along `[n]_C : C ⟶ C`.

That re-presentation of the fibre square is the mathematical heart of the
repair, and it is where `ι` being a MONOMORPHISM is used.  `C[n]` is
defined as `C ×_{ι ≫ [n], E, e} T`; pasting that square with the square

    T --𝟙--> T
    |        |
   e_C       e
    v        v
    C --ι--> E

— cartesian by `of_horiz_isIso_mono`, since `𝟙` is iso and `ι` is mono —
and cancelling `ι` exhibits

    C[n] --snd--> T
     |            |
    fst          e_C
     v            v
     C --[n]_C--> C

as cartesian.  Now `e_C` is étale (`etale_zeroSectionSub`) and étale is
stable under base change, so `fst : C[n] ⟶ C` is étale.

Note this is FALSE without the étale hypothesis: over `𝔽̄_p[[t]]` the
base change of a zero section along `[p]` is the connected-component
jump that the FALSITY AUDIT below exhibits. -/
theorem CyclicSubgroupOfOrder.etale_torsionFst {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N)
    [AlgebraicGeometry.Etale (c.ι ≫ f)] (n : ℕ) :
    AlgebraicGeometry.Etale
      (Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection) := by
  haveI := c.isClosedImmersion
  have hp : Limits.pullback.snd (c.ι ≫ ab.mulByNat n) ab.zeroSection ≫ c.zeroSectionSub
      = Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection ≫ c.mulByNatRestrict n := by
    rw [← cancel_mono c.ι, Category.assoc, Category.assoc, c.zeroSectionSub_comp,
      c.mulByNatRestrict_comp, ← Category.assoc]
    exact Limits.pullback.condition.symm
  have ht : IsPullback (𝟙 T) c.zeroSectionSub ab.zeroSection c.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, c.zeroSectionSub_comp]⟩
  have hs : IsPullback
      (Limits.pullback.snd (c.ι ≫ ab.mulByNat n) ab.zeroSection ≫ 𝟙 T)
      (Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection)
      ab.zeroSection (c.mulByNatRestrict n ≫ c.ι) := by
    rw [Category.comp_id, c.mulByNatRestrict_comp]
    exact (IsPullback.of_hasPullback (c.ι ≫ ab.mulByNat n) ab.zeroSection).flip
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
    (IsPullback.of_right hs hp ht) c.etale_zeroSectionSub

/-- **`C[n]` is flat over the base** (PROVEN 2026-07-27, over the étale
hypothesis introduced by the cut-level repair recorded below).

`C[n] ⟶ C` is étale (`etale_torsionFst`) and `C ⟶ T` is étale by
hypothesis, so `C[n] ⟶ T` is étale, and étale implies flat
(`Etale.iff_flat_and_formallyUnramified`).

**REPAIR RECORD (2026-07-27).  Without `[Etale (ι ≫ f)]` THIS STATEMENT
IS FALSE**; the audit and its counterexample are kept below because they
are what pins the hypothesis, and because they refute the version of this
docstring that claimed flatness of `C[M]` follows from flatness of `C`.

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

THE REPAIR CARRIED OUT (route 1, 2026-07-27).  `[Etale (c.ι ≫ f)]` is
now a hypothesis of this leaf and of `exists_torsionSubscheme`,
`CyclicSubgroupOfOrder.ofDvd`, `liesIn_ofDvd_iff_mem`,
`Gamma0Datum.ofDvd`, `liesIn_ofDvd_iff` and `IsBaseChangeOf.ofDvd`.  The
sharp form was chosen over "`T` is a `ℚ`-scheme" because it is what the
proof actually consumes, and because `Etale` is a `Prop`-valued class, so
proof irrelevance makes the threading through `Gamma0Datum.ofDvd` and
`IsBaseChangeOf.ofDvd` free.  Its ℚ-base instance is
`CyclicSubgroupOfOrder.etale_of_specQBase` below, which is where
Cartier's theorem now sits as a single named leaf.

`CyclicSubgroupOfOrder.ofTorsion` was deliberately NOT changed: it takes
flatness as the explicit argument `hflat` and never forms `C[M]` itself,
so an étale hypothesis there would be an unused binding and an
unnecessary obligation on its callers.

The proof is NOT the one the audit guessed at ("the diagonal of an
unramified morphism is an open immersion, so `C[n]` is the equaliser of
two `T`-morphisms `C ⇉ C`").  That route needs `E ⟶ T` unramified, which
is false for an abelian scheme; unramifiedness is available for `C ⟶ T`,
not for the ambient `E`, and the equaliser as written lands in `E`.  What
works instead is `etale_torsionFst`: re-present the fibre square as a
base change of the SECTION `e_C : T ⟶ C` along `[n]_C : C ⟶ C`, using
that `ι` is a mono.  Route 2 — strengthening `CyclicSubgroupOfOrder` with
the Katz–Mazur rank condition — remains unexplored and unneeded. -/
theorem CyclicSubgroupOfOrder.flat_torsionι {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N)
    [AlgebraicGeometry.Etale (c.ι ≫ f)] (n : ℕ) :
    AlgebraicGeometry.Flat (c.torsionι n ≫ f) := by
  haveI := c.etale_torsionFst n
  show AlgebraicGeometry.Flat
    ((Limits.pullback.fst (c.ι ≫ ab.mulByNat n) ab.zeroSection ≫ c.ι) ≫ f)
  rw [Category.assoc]
  exact (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp inferInstance).1

/-- **Cartier's theorem: over a `ℚ`-scheme a finite flat commutative group
scheme is étale** (sorry leaf, and the ONLY thing the étale repair of
`flat_torsionι` left open).

`ι ≫ f` is finite (`c.isFinite`) and flat (`c.flat`), hence finite
locally free, hence of finite presentation; `C` is a subgroup scheme of
`E` because `ι` is a monomorphism and `zero_liesIn` / `add_liesIn` /
`neg_liesIn` make its points a subgroup at every base.  Étaleness of a
finite flat morphism of finite presentation may be checked fibrewise, and
every fibre of `T ⟶ Spec ℚ` has characteristic-zero residue field, where
a finite group scheme is reduced (Cartier) hence étale.

Faithfulness: this is NOT vacuous and NOT circular — it is the exact
mathematical content that `geom_cyclic` was silently being asked to
supply, isolated so that it has a name and an owner.  It is the reason
the repair costs nothing at the twelve level nodes, all of which work
over `ℚ`.

REFERENCES: Oort, *Commutative group schemes*, and Katz–Mazur ch. 1;
Cartier's theorem in the relative form is SGA 3, VI_B 1.6.1. -/
theorem CyclicSubgroupOfOrder.etale_of_specQBase {E T : Scheme.{0}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N)
    (_q : T ⟶ SpecQ) : AlgebraicGeometry.Etale (c.ι ≫ f) :=
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

**AND FLATNESS IS WHERE THIS STATEMENT WAS FALSE**, which is why it now
carries `[Etale (c.ι ≫ f)]`.  The earlier claim in this docstring —
"`C[M]` is a torsion subscheme of an already-flat `C`, so whatever
construction discharges this leaf produces flatness along with finiteness,
and no separate argument is needed" — is WRONG: a closed subscheme of a
flat scheme is not flat, and in characteristic `p` the rank of `C[M]`
genuinely jumps.  The counterexample, and the repair actually carried out,
are in the docstring of `CyclicSubgroupOfOrder.flat_torsionι`.  Read that
before working here. -/
theorem exists_torsionSubscheme {E T : Scheme.{u}} {f : E ⟶ T}
    {ab : AbelianSchemeStruct f} {N : ℕ} (c : CyclicSubgroupOfOrder ab N)
    [AlgebraicGeometry.Etale (c.ι ≫ f)] (M : ℕ) :
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
    (c : CyclicSubgroupOfOrder ab N) [AlgebraicGeometry.Etale (c.ι ≫ f)] :
    CyclicSubgroupOfOrder ab M :=
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
    (c : CyclicSubgroupOfOrder ab N) [AlgebraicGeometry.Etale (c.ι ≫ f)]
    (T' : Scheme.{u}) (g : T' ⟶ T) (x : RelPoint f g) :
    letI := ab.addCommGroup g
    RelPoint.LiesIn (c.ofDvd hN hMN).ι x ↔ (RelPoint.LiesIn c.ι x ∧ M • x = 0) :=
  (exists_torsionSubscheme c M).choose_spec.choose_spec.2.2.2 T' g x

/-- **The degeneracy map on `Γ₀`-data, `(E, C) ↦ (E, C[M])` for `M ∣ N`.**

The elliptic scheme is untouched — same total space, same structure
morphism, same abelian-scheme structure, same relative dimension — and
only the level structure is cut down by `CyclicSubgroupOfOrder.ofDvd`.
Writing it this way is what makes `IsBaseChangeOf.ofDvd` below carry the
*same* `map` and the *same* cartesian square, so that the only thing left
to check there is the level-structure axiom.

`[Etale (d.cyc.ι ≫ d.f)]` comes from the repair of `flat_torsionι`; over
a `ℚ`-scheme base it is supplied by
`CyclicSubgroupOfOrder.etale_of_specQBase`, which is how the two
universal-property consumers below discharge it. -/
noncomputable def Gamma0Datum.ofDvd {M N : ℕ} (hN : N ≠ 0) (hMN : M ∣ N)
    {T : Scheme.{u}} (d : Gamma0Datum N T)
    [AlgebraicGeometry.Etale (d.cyc.ι ≫ d.f)] : Gamma0Datum M T where
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
    {d : Gamma0Datum N T} [AlgebraicGeometry.Etale (d'.cyc.ι ≫ d'.f)]
    [AlgebraicGeometry.Etale (d.cyc.ι ≫ d.f)] (hb : IsBaseChangeOf h d' d)
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
    {d : Gamma0Datum N T} [AlgebraicGeometry.Etale (d'.cyc.ι ≫ d'.f)]
    [AlgebraicGeometry.Etale (d.cyc.ι ≫ d.f)] (hb : IsBaseChangeOf h d' d) :
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
    hcoarse.universal str'
      (fun g d => haveI := d.cyc.etale_of_specQBase g; cM.classify g (d.ofDvd hN hMN))
      (by
        intro _ _ h g g' hg d' d hb
        haveI := d'.cyc.etale_of_specQBase g'
        haveI := d.cyc.etale_of_specQBase g
        exact cM.classify_natural h hg (hb.ofDvd hN hMN))
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

/-- **Any two coarse moduli spaces of the `Γ₀(N)`-problem over `ℚ` are
canonically isomorphic over `ℚ`** (PROVEN — pure initiality).

This is the standard "an initial object is unique up to unique
isomorphism" argument, written out for the shape of
`IsCoarseModuliY0.universal`.  Feeding `hc'`'s classifying map to `hc`'s
universal property gives `u : Y ⟶ Y'`, and symmetrically `v : Y' ⟶ Y`;
both `u ≫ v` and `𝟙 Y` solve the initiality problem of `hc` against
*itself*, so the uniqueness half of `∃!` identifies them, and likewise on
the other side.

**This is what makes the modular half statable on a CONSTRUCTED model.**
`isSmoothCurve_of_isCoarseModuliY0` asks for geometric properties of an
*arbitrary* scheme presented only by a universal property; nothing can be
extracted from a universal property alone, which is exactly what the old
docstring of that leaf recorded as making it irreducible.  With this
lemma the burden moves to `exists_isCoarseModuliY0_isSmoothCurve`, which
is existential and so may be discharged by exhibiting the Katz–Mazur
model and reading its properties off the construction. -/
theorem exists_isIso_of_isCoarseModuliY0 {N : ℕ} {Y Y' : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strY' : Y' ⟶ SpecQ}
    (hc : IsCoarseModuliY0 N strY) (hc' : IsCoarseModuliY0 N strY') :
    ∃ u : Y ⟶ Y', IsIso u ∧ u ≫ strY' = strY := by
  obtain ⟨u, ⟨hus, huc⟩, -⟩ := hc.universal strY' hc'.classify hc'.classify_natural
  obtain ⟨v, ⟨hvs, hvc⟩, -⟩ := hc'.universal strY hc.classify hc.classify_natural
  -- `u ≫ v` and `𝟙 Y` both solve the initiality problem of `hc` against itself.
  obtain ⟨w, -, hYuniq⟩ := hc.universal strY hc.classify hc.classify_natural
  have huv : u ≫ v = 𝟙 Y :=
    (hYuniq (u ≫ v) ⟨by rw [Category.assoc, hvs, hus],
        fun {_T} g d => by rw [← Category.assoc, ← huc g d, ← hvc g d]⟩).trans
      (hYuniq (𝟙 Y) ⟨Category.id_comp _, fun {_T} _g _d => (Category.comp_id _).symm⟩).symm
  -- and symmetrically on the other side.
  obtain ⟨w', -, hY'uniq⟩ := hc'.universal strY' hc'.classify hc'.classify_natural
  have hvu : v ≫ u = 𝟙 Y' :=
    (hY'uniq (v ≫ u) ⟨by rw [Category.assoc, hus, hvs],
        fun {_T} g d => by rw [← Category.assoc, ← hvc g d, ← huc g d]⟩).trans
      (hY'uniq (𝟙 Y') ⟨Category.id_comp _, fun {_T} _g _d => (Category.comp_id _).symm⟩).symm
  exact ⟨u, ⟨v, huv, hvu⟩, hus⟩

/-- **The five curve properties transport along an isomorphism over the
base** (PROVEN).

Each of the five is transported by an off-the-shelf mathlib mechanism, and
none of them needs anything about modular curves:

* `IsIntegral` is a property of the underlying scheme and moves along
  `inv u` by `IsIntegral.of_isIso`;
* `QuasiCompact` and `IsSeparated` are stable under composition and hold
  of an isomorphism, so they hold of `u ≫ strY'`;
* `SmoothOfRelativeDimension` adds relative dimensions under composition
  and an isomorphism is an open immersion, hence smooth of relative
  dimension `0`, so `0 + 1 = 1`;
* `GeometricallyConnected` is stable under base change, hence respects
  isomorphisms (`MorphismProperty.RespectsIso.precomp`). -/
theorem isSmoothCurve_transport {Y Y' : Scheme.{0}} {strY : Y ⟶ SpecQ} {strY' : Y' ⟶ SpecQ}
    (u : Y ⟶ Y') [IsIso u] (hu : u ≫ strY' = strY)
    (hint : IsIntegral Y') (hqc : QuasiCompact strY') (hsep : IsSeparated strY')
    (hsmd : SmoothOfRelativeDimension 1 strY') (hconn : GeometricallyConnected strY') :
    IsIntegral Y ∧ QuasiCompact strY ∧ IsSeparated strY ∧
      SmoothOfRelativeDimension 1 strY ∧ GeometricallyConnected strY := by
  haveI := hint; haveI := hqc; haveI := hsep; haveI := hsmd; haveI := hconn
  haveI : IsIntegral Y := IsIntegral.of_isIso (inv u)
  subst hu
  haveI : GeometricallyConnected (u ≫ strY') :=
    MorphismProperty.RespectsIso.precomp (P := @GeometricallyConnected) u strY' hconn
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, inferInstance⟩
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (u ≫ strY'))

/-! ### The model that is exhibited: an atlas with an AFFINE coarse space

`exists_isCoarseModuliY0_isSmoothCurve` asks for five properties of a
coarse space.  Three of them are not modular at all once the model is
known to be **affine with a domain of global functions**, which is
exactly what Katz–Mazur (8.1.1) build — `Y = Spec (A^G)` for the affine
rigidified moduli scheme `M = Spec A`:

* `IsIntegral Y` is `isIntegral_of_isAffine_of_isDomain`;
* `QuasiCompact str` and `IsSeparated str` hold because a morphism
  between affine schemes is affine (`isAffineHom_of_isAffine`, and
  `SpecQ` is affine by construction), and an affine morphism is both
  quasi-compact and separated.

So the modular input shrinks from five properties to two —
`SmoothOfRelativeDimension 1` and `GeometricallyConnected` — plus the
affineness and integrality of the constructed model.  That is
`Gamma0AffineModel`, and it is the only thing left below. -/

/-- **A Katz–Mazur atlas whose coarse space is an affine integral curve**:
the atlas data of `Gamma0Atlas`, together with the geometry that the
construction of `Y = Spec (A^G)` actually provides.

Note `toGamma0Atlas`: a `Gamma0AffineModel` **is** a `Gamma0Atlas`, so
`exists_gamma0AffineModel` is mechanically at least as strong as
`exists_gamma0Atlas`, and cannot weaken the tree.  (The two existence
leaves are not yet merged only because `exists_gamma0GITPresentation` —
the branch `exists_gamma0Atlas` currently runs through — is being
decomposed by another owner; re-deriving `exists_gamma0Atlas` from this
structure is the follow-up, and it belongs in that region, not here.)

`isDomain` is stated on `Γ(Y, ⊤)` rather than as `IsIntegral Y` because
that is the form in which the GIT construction supplies it: `A^G` is a
subring of the domain `A` (`Gamma0GITPresentation.injective_algebraMap`),
so `Function.Injective.isDomain` gives it directly, with no scheme-level
argument.

`hN : 0 < N` is required for the same reason as on the consumer: at
`N = 0` every coarse space is EMPTY (`isEmpty_of_isCoarseModuliY0_zero`),
so `Γ(Y, ⊤)` is the trivial ring and `isDomain` is unsatisfiable.  The
degenerate level is handled separately and vacuously below; the branches
are deliberately not merged. -/
structure Gamma0AffineModel (N : ℕ) extends Gamma0Atlas N where
  /-- the coarse space is affine — Katz–Mazur (8.1.1)'s `Spec (A^G)` -/
  isAffine : IsAffine toGamma0Atlas.Y
  /-- its ring of global functions is a domain -/
  isDomain : IsDomain Γ(toGamma0Atlas.Y, ⊤)
  /-- it is smooth of relative dimension `1` over `ℚ` -/
  smooth : SmoothOfRelativeDimension 1 toGamma0Atlas.str
  /-- and geometrically connected -/
  connected : GeometricallyConnected toGamma0Atlas.str

/-- **Existence of the affine integral Katz–Mazur model of `Y_0(N)` for
`N ≥ 1`** (sorry leaf — the MODULAR half of the compactification, and the
ONLY modular input to `X_0(N)`'s existence).

TRUE and classical.  Affineness and integrality are Katz–Mazur (8.1.1)'s
construction read literally: `𝔐([Γ₀(N)], [Γ(n)]) = Spec A` is affine and
irreducible over `ℚ`, hence `A` is a domain, and `Y = Spec (A^G)` with
`A^G ⊆ A`.  Smoothness is normality of the coarse space of a smooth
Deligne–Mumford stack of dimension one together with "normal curve =
smooth curve" (Deligne–Rapoport III.1; Katz–Mazur 8.2, and 8.2.1 for the
`ℤ[1/N]`-smoothness that specialises to this).  Geometric connectedness
is the irreducibility of `Γ_0(N)\ℍ` together with the fact that the
moduli problem is defined over `ℚ` (Deligne–Rapoport IV.5.5, or Shimura
6.6).

**What is still missing here, and what is NOT.**  The atlas half —
`classify`, `classify_natural`, `M`, `dM`, `cover`, `quotient` — is
exactly `exists_gamma0Atlas`, already reduced to
`exists_gamma0GITPresentation` (modular) plus `specInvariants_universal`
(pure GIT).  What this leaf adds beyond that is only the four geometric
fields, and of those `isAffine` and `isDomain` are *already implicit in
the GIT presentation*: `Spec (A^G)` is affine by construction, and
`IsDomain (A^G)` follows from `IsDomain A` by
`Function.Injective.isDomain` applied to `injective_algebraMap`.  So the
genuinely new content is `smooth` and `connected` — Deligne–Rapoport
III.1 and Katz–Mazur 8.2, and nothing else. -/
theorem exists_gamma0AffineModel (N : ℕ) (hN : 0 < N) :
    Nonempty (Gamma0AffineModel N) :=
  sorry

/-- **SOME coarse moduli space of the `Γ₀(N)`-problem is a geometrically
connected smooth curve over `ℚ`, for `N ≥ 1`** (PROVEN 2026-07-27 over
`exists_gamma0AffineModel`, by exhibiting the Katz–Mazur model and
reading the five properties off it; formerly a sorry leaf itself).

TRUE and classical: for `N ≥ 1` the coarse moduli space of the
`Γ₀(N)`-problem over `ℚ` is a smooth affine geometrically connected curve.
Smoothness is normality of the coarse space of a smooth Deligne–Mumford
stack of dimension one together with "normal curve = smooth curve"
(Deligne–Rapoport III.1; Katz–Mazur 8.2, and 8.2.1 for the
`ℤ[1/N]`-smoothness that specialises to this); geometric connectedness is
the irreducibility of `Γ_0(N)\ℍ` together with the fact that the moduli
problem is defined over `ℚ` (Deligne–Rapoport IV.5.5, or Shimura 6.6).

**Why the statement is EXISTENTIAL, and this is the whole point of the
cut.**  The consumer `isSmoothCurve_of_isCoarseModuliY0` quantifies over
*every* coarse space, and its previous docstring recorded — correctly —
that this made it irreducible at this pin: a scheme presented only by a
universal property carries no extractable geometry.  That objection dies
here.  Initiality (`exists_isIso_of_isCoarseModuliY0`) makes all coarse
spaces isomorphic over `ℚ`, and the five properties transport
(`isSmoothCurve_transport`), so it suffices to exhibit **one** model.

**The model exhibited is `Gamma0AffineModel.Y`**, and the five properties
are read off it rather than off the universal property — exactly the form
in which Deligne–Rapoport III.1 and Katz–Mazur 8.2 state them.  Three of
the five are then *not* modular: the model is affine over the affine
`SpecQ`, so `QuasiCompact` and `IsSeparated` come from
`isAffineHom_of_isAffine`, and `IsIntegral` comes from
`isIntegral_of_isAffine_of_isDomain`.  Only `SmoothOfRelativeDimension 1`
and `GeometricallyConnected` survive into the leaf; see
`exists_gamma0AffineModel` above.

`hN : 0 < N` is REQUIRED and the statement is FALSE without it.  At
`N = 0` the coarse space is EMPTY (`isEmpty_of_isCoarseModuliY0_zero`),
and both `IsIntegral` and `GeometricallyConnected` carry nonemptiness —
`IsIntegral` through `IrreducibleSpace`, `GeometricallyConnected` through
`ConnectedSpace`.  So the conclusion is unsatisfiable at the degenerate
level, which is handled separately and vacuously below.  Note the
existential form does **not** soften this: `exists_coarseModuliY0_zero`
produces a coarse space at `N = 0` too, and it is empty, so there is no
model to exhibit.

The five conclusions are exactly the hypotheses of
`exists_isSmoothCompactification`, and none is decoration:
`QuasiCompact` and `IsSeparated` are what Nagata's compactification
consumes, `IsIntegral` is what makes the relative normalization integral,
`SmoothOfRelativeDimension 1` is what pins the relative dimension of
the compactification to `1` rather than leaving it arbitrary, and
`GeometricallyConnected` is what
`AlgebraicGeometry.geometricallyConnected_of_isSmoothCompactification`
carries across to `X_0(N)`. -/
theorem exists_isCoarseModuliY0_isSmoothCurve (N : ℕ) (hN : 0 < N) :
    ∃ (Y : Scheme.{0}) (strY : Y ⟶ SpecQ) (_hc : IsCoarseModuliY0 N strY),
      IsIntegral Y ∧ QuasiCompact strY ∧ IsSeparated strY ∧
        SmoothOfRelativeDimension 1 strY ∧ GeometricallyConnected strY := by
  obtain ⟨M⟩ := exists_gamma0AffineModel N hN
  haveI := M.isAffine
  haveI := M.isDomain
  haveI := M.smooth
  haveI := M.connected
  -- `Γ(Y, ⊤)` is a domain, hence nontrivial, so `Spec Γ(Y, ⊤) ≅ Y` is nonempty.
  haveI : Nonempty M.toGamma0Atlas.Y :=
    Nonempty.map M.toGamma0Atlas.Y.isoSpec.inv.base inferInstance
  haveI : IsIntegral M.toGamma0Atlas.Y :=
    isIntegral_of_isAffine_of_isDomain (X := M.toGamma0Atlas.Y)
  -- affine source over the affine `SpecQ`: the structure morphism is affine,
  -- hence quasi-compact and separated.
  haveI : IsAffineHom M.toGamma0Atlas.str := inferInstance
  exact ⟨_, M.toGamma0Atlas.str, M.toGamma0Atlas.toIsCoarseModuliY0,
    inferInstance, inferInstance, IsSeparated.of_isAffineHom _, inferInstance, inferInstance⟩

/-- **`Y_0(N)` is a geometrically connected smooth curve over `ℚ`, for
`N ≥ 1`** (PROVEN 2026-07-27, over the single modular leaf
`exists_isCoarseModuliY0_isSmoothCurve`; formerly a sorry leaf itself).

The proof is the two-step reduction described at that leaf: exhibit one
model with the five properties, transport them to the given coarse space
along the canonical isomorphism supplied by initiality.

**This is the ONLY modular input to `X_0(N)`'s existence.**  Everything
else — that a smooth curve over a field has a smooth proper
compactification with finite complement — is
`AlgebraicGeometry.exists_isSmoothCompactification`, which is general
algebraic geometry and lives in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`. -/
theorem isSmoothCurve_of_isCoarseModuliY0 {N : ℕ} (hN : 0 < N) {Y : Scheme.{0}}
    {strY : Y ⟶ SpecQ} (hc : IsCoarseModuliY0 N strY) :
    IsIntegral Y ∧ QuasiCompact strY ∧ IsSeparated strY ∧
      SmoothOfRelativeDimension 1 strY ∧ GeometricallyConnected strY := by
  obtain ⟨Y', strY', hc', hint, hqc, hsep, hsmd, hconn⟩ :=
    exists_isCoarseModuliY0_isSmoothCurve N hN
  obtain ⟨u, hu, hcomm⟩ := exists_isIso_of_isCoarseModuliY0 hc hc'
  haveI := hu
  exact isSmoothCurve_transport u hcomm hint hqc hsep hsmd hconn

/-- **Existence of the smooth compactification `X_0(N)`** (PROVEN, over
one modular leaf plus general curve theory; formerly a sorry node).

The two halves the previous version of this docstring named as
"independent" are now genuinely separated, and only the first is still
modular:

* `isSmoothCurve_of_isCoarseModuliY0` — `Y_0(N)` is a geometrically
  connected smooth curve over `ℚ` for `N ≥ 1` (Deligne–Rapoport III.1,
  Katz–Mazur 8.2).  Now a THEOREM (2026-07-27), over the single leaf
  `exists_gamma0AffineModel`, which asks only for `smooth` and
  `connected` on the Katz–Mazur model — the other three properties are
  discharged from affineness and integrality of that model.
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
                       «over» := Category.id_comp strY
                       isOpenImmersion := inferInstance
                       isDominant := inferInstance
                       proper := inferInstance
                       smooth := SmoothOfRelativeDimension.smooth (n := 1) (f := strY) }⟩⟩
  · obtain ⟨hint, hqc, hsep, hsmd, -⟩ := isSmoothCurve_of_isCoarseModuliY0 hN hc
    haveI := hint; haveI := hqc; haveI := hsep; haveI := hsmd
    obtain ⟨X, strX, j, hX⟩ := exists_isSmoothCompactification (K := ℚ) strY
    haveI := hX.smooth
    exact ⟨X, strX, ⟨{ j := j
                       «over» := hX.comm
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

/-! ### The descent bridge: from a rational point of `Y_0(N)` back to a curve

**The exact converse of `false_of_stable_of_y0HasNoRationalPoint`**, and the
only obligation in the two prime-square nodes below that is about the modular
CURVE rather than about elliptic curves.  Introduced 2026-07-27 while cutting
those two nodes; it is stated once here because it is uniform in `N` and
therefore serves every level node in this file, not only the eight
prime squares.

#### Why the tree needs it, stated bluntly (2026-07-27)

`false_of_stable_of_y0HasNoRationalPoint` runs *modular ⟹ elementary*: from
`Y_0(N)(ℚ) = ∅` it concludes that no elliptic curve over `ℚ` carries a
Galois-stable cyclic subgroup of order `N`.  Every consumer in
`FreyCurve/MazurTorsion.lean` uses it in that direction, and consequently
**all of that module's prime-square material is `ex falso` from the two
sorried nodes below.**  This is checkable in one read:
`WeierstrassCurve.exists_atkinLehnerEnd_of_stable_cyclic_subgroup_order_169`
derives `Fermat.Y0HasNoRationalPoint 169` from
`y0HasNoRationalPoint_isogenyPrimeSq` at `p = 13`, feeds it to
`false_of_stable_of_y0HasNoRationalPoint`, and finishes with `.elim` — so the
Atkin–Lehner endomorphism, the class polynomial of discriminant `-676`, and
`not_cyclicIsogeny_oneHundredSixtyNine` above it are all consequences of a
contradiction, carrying no arithmetic of their own.  The same holds at the
seven other primes through
`WeierstrassCurve.not_two_stable_lines_of_jInvariant`, whose Vélu
construction is real but whose closing step is again
`y0HasNoRationalPoint_isogenyPrimeSq`.

The consequence for a successor is the important part: **the arithmetic
content of Kenku's prime-square theorem lives nowhere in this tree except in
the two sorried nodes below**, and it cannot be imported from
`MazurTorsion.lean`, which imports this module.  So the elementary statements
have to be restated HERE — which is what
`not_stableCyclic_sq_of_isogenyClassPrime` and
`not_stableCyclic_oneHundredSixtyNine` do — and `MazurTorsion.lean`'s
`not_cyclicIsogeny_sq_of_isogenyPrime_ge_eleven` and
`not_cyclicIsogeny_oneHundredSixtyNine` should be re-based onto them, which
would delete the `ex falso` laundering and let that module's genuine work (the
`j`-invariant table `jInvariant_mem_of_isogenyPrime_ge_eleven` and the Vélu
quotient) discharge them instead.  That re-basing is a cut-level repair across
two modules and two owners' regions; it is recorded here rather than performed. -/

/-! #### The cut of the descent bridge (2026-07-27)

`y0HasNoRationalPoint_of_not_stableCyclic` was a single `sorry`.  It is now
DERIVED from four proven lemmas and two named leaves, along the two
ingredients its own docstring listed:

* *bijectivity of `classify` on geometric points* — the half of the
  coarse-moduli definition that `IsCoarseModuliY0` deliberately omits.  The
  half the descent actually consumes is SURJECTIVITY on `ℚ̄`-points, and that
  is now **PROVEN**, in `IsCoarseModuliY0.exists_gamma0Datum_of_algClosPoint`.
  It really is unreachable from initiality and really is reachable from the
  presentation: over `Gamma0GITPresentation` the coarse space is `Spec B` with
  `B = A^G`, so a `ℚ̄`-point of it is a ring map `B → ℚ̄`, which lifts to
  `A → ℚ̄` because `A` is integral over `B`; the lift is a `ℚ̄`-point `m` of the
  rigidified moduli scheme, and the base change of the universal family `dM`
  along `m` is the datum wanted.  Only two general facts are used, and both
  were already here: `exists_gamma0Datum_baseChange` (PROVEN — note the
  docstring of `Gamma0Atlas` above still says base change "does not exist
  today"; that is stale) and `classify_dM`, which is what makes `classify dM`
  the quotient map `Spec A ⟶ Spec B` and hence lets `m` be pushed to the given
  point.  Transport from the GIT presentation to an ARBITRARY coarse moduli
  space is pure initiality, exactly as in `IsCoarseModuliY0.exists_inverse`
  (which cannot be cited here — it is declared six thousand lines below — so
  the two-line argument is repeated inline).
* *the twisting/Kummer computation* — this is `exists_gamma0Datum_specQ_of_ratPoint`,
  the one genuinely arithmetic leaf of the bridge.

What is left over is the translation back from a `Γ₀(N)`-datum over `ℚ` to a
Weierstrass curve, `false_of_gamma0Datum_specQ`: the exact converse of
`nonempty_gamma0Datum_of_stable`, and a statement with no modular curve in it
at all.

The degenerate level is separated as everywhere else in this file:
`y0HasNoRationalPoint_zero` is PROVEN (from `isEmpty_of_gamma0Datum_zero` and
initiality), which is what lets the two leaves carry `N ≠ 0`. -/

/-- **A ring map into an algebraically closed field extends along an integral
extension** (PROVEN 2026-07-27) — pure commutative algebra, stated here
because the geometric surjectivity below is exactly this fact read through
`Spec`.

`p := ker f` is prime because `K` is a domain; lying over
(`Ideal.exists_ideal_over_prime_of_isIntegral`, applicable because `hinj`
makes `⊥.comap (algebraMap B A) = ⊥ ≤ p`) produces a prime `Q` of `A` over
`p`; `A ⧸ Q` is then an integral — hence algebraic — extension of the domain
`B ⧸ p`, and `IsAlgClosed.lift` embeds it into `K` over `B ⧸ p`.  Composing
with `Ideal.Quotient.mk Q` gives `f'`, and `AlgHom.commutes` is the
compatibility.

`hinj` is load-bearing and the statement is FALSE without it: take `A = 0`,
`B = ℚ`, which satisfies `Algebra.IsIntegral B A` vacuously while admitting no
ring map to a field at all. -/
theorem exists_ringHom_of_isIntegral_isAlgClosed {B A K : Type} [CommRing B] [CommRing A]
    [Algebra B A] [Field K] [IsAlgClosed K] [Algebra.IsIntegral B A]
    (hinj : Function.Injective (algebraMap B A)) (f : B →+* K) :
    ∃ f' : A →+* K, f'.comp (algebraMap B A) = f := by
  classical
  haveI hp : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := B) (S := A) (RingHom.ker f) ⊥
      (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI : Q.IsPrime := hQprime
  haveI : Q.LiesOver (RingHom.ker f) := ⟨hQcomap.symm⟩
  letI : Algebra (B ⧸ RingHom.ker f) K :=
    (Ideal.Quotient.lift (RingHom.ker f) f (fun _ ha => ha)).toAlgebra
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker f) K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (RingHom.lift_injective_of_ker_le_ideal _ _ le_rfl)
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker f) (A ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  have φ : (A ⧸ Q) →ₐ[B ⧸ RingHom.ker f] K := IsAlgClosed.lift
  refine ⟨(φ.toRingHom).comp (Ideal.Quotient.mk Q), RingHom.ext fun b => ?_⟩
  show φ (Ideal.Quotient.mk Q (algebraMap B A b)) = f b
  have hb : Ideal.Quotient.mk Q (algebraMap B A b)
      = algebraMap (B ⧸ RingHom.ker f) (A ⧸ Q) (Ideal.Quotient.mk _ b) := rfl
  rw [hb, AlgHom.commutes]
  rfl

/-- **`classify` is surjective on `ℚ̄`-points, over the GIT presentation**
(PROVEN 2026-07-27): every `ℚ̄`-point of the coarse space `Spec B` is the class
of an honest `Γ₀(N)`-datum over `Spec ℚ̄`.

This is the half of the coarse-moduli definition that `IsCoarseModuliY0`
omits, and the reason it is proved HERE rather than there is exactly the
reason recorded in the docstring of `y0HasNoRationalPoint_of_not_stableCyclic`:
initiality determines `(Y, classify)` up to unique isomorphism and says
nothing about which points of `Y` are hit, whereas a *presentation* says which
points there are.

The argument in one line: `classify_dM` identifies `(classify strM dM).1` with
the quotient map `Spec A ⟶ Spec B`, so lifting the point is lifting a ring map
`B → ℚ̄` to `A → ℚ̄` — `exists_ringHom_of_isIntegral_isAlgClosed`, available
because `Algebra.IsInvariant.isIntegral` makes `A` integral over `B = A^G` —
and the datum is the base change of the universal family along the lift,
`exists_gamma0Datum_baseChange`.  `subsingleton_hom_specQ` disposes of the
structure-morphism bookkeeping, as it does throughout this file.

Note what is NOT needed: no properness, no finiteness of `G` beyond what
`Algebra.IsInvariant` already carries, and no injectivity of `classify`.  The
descent leaf below is where injectivity would enter, and it enters there in
the packaged form of the hypothesis `hd` rather than as a separate statement. -/
theorem Gamma0GITPresentation.exists_gamma0Datum_of_algClosPoint {N : ℕ}
    (P : Gamma0GITPresentation N) (x : RelPoint P.str (specAlgClos ℚ)) :
    ∃ d : Gamma0Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      P.classify (specAlgClos ℚ) d = x := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.group_G
  letI := P.finite_G
  letI := P.action_GA
  letI := P.smulComm_GBA
  letI := P.isInvariant_BAG
  haveI : Algebra.IsIntegral P.B P.A := Algebra.IsInvariant.isIntegral P.B P.A P.G
  obtain ⟨f', hf'⟩ := exists_ringHom_of_isIntegral_isAlgClosed (K := AlgebraicClosure ℚ)
    P.injective_algebraMap (Spec.preimage x.1).hom
  have hmx : Spec.map (CommRingCat.ofHom f') ≫
      Spec.map (CommRingCat.ofHom (algebraMap P.B P.A)) = x.1 := by
    rw [← Spec.map_comp]
    have hcomp : CommRingCat.ofHom (algebraMap P.B P.A) ≫ CommRingCat.ofHom f'
        = Spec.preimage x.1 := CommRingCat.hom_ext hf'
    rw [hcomp, Spec.map_preimage]
  obtain ⟨d, ⟨hbc⟩⟩ := exists_gamma0Datum_baseChange (Spec.map (CommRingCat.ofHom f')) P.dM
  have hg : Spec.map (CommRingCat.ofHom f') ≫ P.strM = specAlgClos ℚ :=
    (subsingleton_hom_specQ _).elim _ _
  refine ⟨d, (P.classify_natural _ hg hbc).trans (Subtype.ext ?_)⟩
  show Spec.map (CommRingCat.ofHom f') ≫ (P.classify P.strM P.dM).1 = x.1
  rw [P.classify_dM]
  exact hmx

/-- **`classify` is surjective on `ℚ̄`-points, over ANY coarse moduli space**
(PROVEN 2026-07-27) — the previous lemma transported off the presentation by
initiality alone.

`Y0HasNoRationalPoint` quantifies over every coarse moduli space rather than a
chosen one, so the surjectivity statement has to be available at an arbitrary
`IsCoarseModuliY0` too.  Initiality supplies mutually inverse `u : Y_P ⟶ Y`
and `v : Y ⟶ Y_P` over `Spec ℚ` that are compatible with both classifying
maps; a point of `Y` is pushed to `Y_P` by `v`, lifted there, and pushed back
by `u`.  This is `IsCoarseModuliY0.exists_inverse` in miniature — it cannot be
cited, being declared six thousand lines below this one, so the `v ≫ u = 𝟙`
argument is repeated here.

`hN : 0 < N` is consumed only by `exists_gamma0GITPresentation`, which is
stated for `N ≥ 1` because `[Γ₀(N)]` is a moduli problem only there; the
degenerate level is `y0HasNoRationalPoint_zero`. -/
theorem IsCoarseModuliY0.exists_gamma0Datum_of_algClosPoint {N : ℕ} (hN : 0 < N)
    {Y : Scheme.{0}} {str : Y ⟶ SpecQ} (hY : IsCoarseModuliY0 N str)
    (x : RelPoint str (specAlgClos ℚ)) :
    ∃ d : Gamma0Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      hY.classify (specAlgClos ℚ) d = x := by
  obtain ⟨P⟩ := exists_gamma0GITPresentation N hN
  let h₁ := P.toGamma0Atlas.toIsCoarseModuliY0
  obtain ⟨u, ⟨hu, hucl⟩, -⟩ := h₁.universal str hY.classify hY.classify_natural
  obtain ⟨v, ⟨hv, hvcl⟩, -⟩ := hY.universal P.toGamma0Atlas.str h₁.classify h₁.classify_natural
  obtain ⟨w, -, hwuniq⟩ := hY.universal str hY.classify hY.classify_natural
  have hvu : v ≫ u = 𝟙 Y := by
    refine (hwuniq (v ≫ u) ⟨?_, ?_⟩).trans (hwuniq (𝟙 Y) ⟨Category.id_comp _, ?_⟩).symm
    · rw [Category.assoc, hu, hv]
    · intro T g dd
      conv_lhs => rw [hucl g dd, hvcl g dd]
      exact Category.assoc _ _ _
    · intro T g dd
      exact (Category.comp_id _).symm
  obtain ⟨d, hd⟩ := P.exists_gamma0Datum_of_algClosPoint
    (⟨x.1 ≫ v, by rw [Category.assoc, hv]; exact x.2⟩ :
      RelPoint P.toGamma0Atlas.str (specAlgClos ℚ))
  refine ⟨d, Subtype.ext ?_⟩
  have hd' : (h₁.classify (specAlgClos ℚ) d).1 = x.1 ≫ v := congrArg Subtype.val hd
  rw [hucl (specAlgClos ℚ) d, hd', Category.assoc, hvu, Category.comp_id]

/-- **The degenerate level has no rational point** (PROVEN 2026-07-27).

VACUITY AUDIT — this carries no arithmetic, and is recorded only so that
`y0HasNoRationalPoint_of_not_stableCyclic` can be stated for every `N` while
its two leaves are restricted, correctly, to `N ≥ 1`.  By
`isEmpty_of_gamma0Datum_zero` the `Γ₀(0)`-problem has no object over a
nonempty base, so the empty scheme is a cocone for it; initiality then gives
`Y ⟶ ∅`, which forces `Y` — and hence `Spec ℚ`, through the supposed rational
point — to be empty, contradicting `Nontrivial ℚ`.

This is the same observation as `exists_coarseModuliY0_zero`, read in the
opposite direction: there it produced a coarse space, here it empties an
arbitrary one. -/
theorem y0HasNoRationalPoint_zero : Y0HasNoRationalPoint 0 := by
  intro Y str hY
  have hinit : ∀ {T : Scheme.{0}}, Gamma0Datum 0 T → Limits.IsInitial T := by
    intro T d
    have : IsEmpty T := isEmpty_of_gamma0Datum_zero d
    exact isInitialOfIsEmpty
  obtain ⟨u, -, -⟩ := hY.universal (emptyIsInitial.to SpecQ)
    (fun {_T} _g d => ⟨(hinit d).to _, (hinit d).hom_ext _ _⟩)
    (fun {_T' _T} _h {_g _g'} _hg {d'} {_d} _hbc => Subtype.ext ((hinit d').hom_ext _ _))
  constructor
  intro y
  haveI : IsEmpty ↥Y := u.base.hom.1.isEmpty
  haveI : IsEmpty ↥SpecQ := y.1.base.hom.1.isEmpty
  have hne : Nonempty ↥SpecQ := inferInstanceAs (Nonempty (PrimeSpectrum ℚ))
  exact (‹IsEmpty ↥SpecQ›).elim hne.some

/-- **A `ℚ̄`-datum whose class is a RATIONAL point of the coarse space descends
to `ℚ`, after a twist** (sorry leaf, opened 2026-07-27) — the twisting/Kummer
computation of the section above, and the one genuinely arithmetic ingredient
of the descent bridge.

`hd` says that the class of `d` in the coarse space is the base change to `ℚ̄`
of the rational point `y`.  That is precisely "the field of moduli of `d` is
`ℚ`": the class of `σ^*d` is `σ^*(classify d) = σ^*(y|_ℚ̄) = y|_ℚ̄`, because a
`ℚ`-rational point is Galois-invariant by construction, so `classify` cannot
separate `σ^*d` from `d`.  Injectivity of `classify` on geometric points — the
other half of the omitted clause — then makes `σ^*d ≅ d` for every `σ`, and
that is the input to the twisting argument.

#### The argument, and it is the one written out in the section docstring above

`j(E) ∈ ℚ`, so `E` has a model over `ℚ` and we may take `E^σ = E`; the
comparison isomorphisms `α_σ` form a cocycle in `Z¹(G_ℚ, Aut(E)/Aut(E, C))`;
`−1 ∈ Aut(E, C)` always, since `−C = C`, so the quotient is `1` or `μ_{n/2}`
with `n ∈ {2, 4, 6}`; and `ℚˣ/(ℚˣ)ⁿ ↠ ℚˣ/(ℚˣ)^{n/2}` is surjective, so the
cocycle is realised by a quadratic/quartic/sextic twist `E^{(d)}`, which is
defined over `ℚ` and carries a `G_ℚ`-stable subgroup.

**NO CASE SPLIT ON `j`, and do not reintroduce one.**  The `j ∈ {0, 1728}`
caveat is a caveat about the strictly stronger statement that the PAIR
`(E, C)` descend; only `Nonempty (Gamma0Datum N SpecQ)` is asked for here, so a
twist is allowed and the obstruction vanishes.  Neither
`isolatedJInvariants` nor any `p`-hypothesis belongs in this leaf; the former
is load-bearing for the two arithmetic level leaves, not for this one.

**The check that refutes this**: exhibit `n ∈ {4, 6}` and a class in
`ℚˣ/(ℚˣ)^{n/2}` outside the image of `ℚˣ/(ℚˣ)ⁿ` — impossible, both maps being
induced by the identity on representatives.

WHAT A PROVER OWES.  The injectivity half of the geometric bijection is
*inside* this leaf: `hd` is stated in terms of `classify` rather than in terms
of an isomorphism `σ^*d ≅ d`, because `IsBaseChangeOf` along `specGal σ` is the
only comparison of data this development has and the Galois-twisted datum
would have to be produced before it could be compared.  A successor who wants
to split that off should state it as
`classify _ d₁ = classify _ d₂ → Nonempty (IsBaseChangeOf (𝟙 _) d₁ d₂)` and
obtain `σ^*d` from `exists_gamma0Datum_baseChange (specGal σ) d`, both of which
are now available. -/
theorem exists_gamma0Datum_specQ_of_ratPoint {N : ℕ} {Y : Scheme.{0}} {str : Y ⟶ SpecQ}
    (hY : IsCoarseModuliY0 N str) (y : RelPoint str (𝟙 SpecQ))
    (d : Gamma0Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
    (hd : hY.classify (specAlgClos ℚ) d
      = RelPoint.pre (specAlgClos ℚ) (Category.comp_id _) y) :
    Nonempty (Gamma0Datum N SpecQ) :=
  sorry

/-- **A `Γ₀(N)`-datum over `ℚ` produces an elliptic curve over `ℚ` with a
Galois-stable cyclic subgroup of order `N`** (sorry leaf, opened 2026-07-27),
stated in the contradiction form its only consumer wants.

THE EXACT CONVERSE OF `nonempty_gamma0Datum_of_stable`, and there is no modular
curve in it: it is the dictionary between the scheme-theoretic phrasing of the
moduli problem and the elementary phrasing that `FreyCurve/MazurTorsion.lean`
uses, read in the direction that has never been needed before.

#### What proving it needs

1. **A Weierstrass model of an elliptic scheme over a field.**  `d.ab` is an
   abelian scheme of relative dimension one over `Spec ℚ`; classical
   Riemann–Roch on the genus-one curve `d.E` with the origin `d.ab.zero` gives
   a Weierstrass equation over `ℚ`.  `IsWeierstrassModel` (below in this file)
   is the relation to produce, and `exists_weierstrassModel_gamma0Datum` is the
   same relation produced in the OPPOSITE direction, so its statement is the
   template.  This is the missing "Zariski-local Weierstrass presentations"
   item that the cut of `exists_jLine` also records as its honest residue —
   closing it here would close half of that too.
2. **The generator.**  `d.cyc.geom_cyclic` applied at the geometric point
   `specAlgClos ℚ` hands over a point `y` of the geometric fibre with
   `addOrderOf y = N` whose multiples are exactly the points lying in `d.cyc.C`.
3. **Stability, which is free.**  `d.cyc.C` is a subscheme over `Spec ℚ`, so
   `RelPoint.LiesIn d.cyc.ι` is invariant under precomposition with
   `specGal σ`; the multiples of `y` are therefore a `Γ_ℚ`-stable set, which is
   the hypothesis `hstable` in the elementary phrasing.
4. **Transport along the identification** of `E(ℚ̄)` with the geometric fibre.
   The `≃+` of `exists_ellipticScheme_of_weierstrass` is Galois-equivariant
   (`he`) and `nonempty_gamma0Datum_of_stable` transports order and stability
   ACROSS it in the other direction; the same two `have`s run backwards here.

`hN : N ≠ 0` is load-bearing for step 2 — a "cyclic subgroup of order `0`" is
infinite and there is no generator of finite order to produce.  At `N = 0` the
statement is nevertheless TRUE, and vacuously so, since
`isEmpty_of_gamma0Datum_zero` makes `Gamma0Datum 0 SpecQ` uninhabited over the
nonempty base `Spec ℚ`; the hypothesis is kept because the call site supplies
it and it removes a degenerate branch from the main argument.

FAITHFULNESS.  The conclusion is `False`, so the leaf cannot be weakened by
strengthening its own conclusion; the risk is the opposite one, of weakening
`h`.  `h` is transcribed VERBATIM from `y0HasNoRationalPoint_of_not_stableCyclic`
and must stay so — in particular the quantifier is over all of
`Field.absoluteGaloisGroup ℚ` and not over inertia, which is correct here
because the base is `ℚ` and there is no local field in sight. -/
theorem false_of_gamma0Datum_specQ {N : ℕ} (hN : N ≠ 0)
    (h : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
        (g : (E⁄(AlgebraicClosure ℚ)).Point), addOrderOf g = N →
        (∀ σ : Field.absoluteGaloisGroup ℚ,
          ∀ x ∈ AddSubgroup.zmultiples g,
            WeierstrassCurve.Affine.Point.map
              (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
              AddSubgroup.zmultiples g) → False)
    (d : Gamma0Datum N SpecQ) : False :=
  sorry

/-- **A rational point of `Y_0(N)` comes from an elliptic curve over `ℚ`**
(PROVEN 2026-07-27 by the decomposition recorded in the subsection above;
formerly a single sorry node), in the contrapositive form that its
consumers want: if no elliptic curve over `ℚ` carries a Galois-stable cyclic
subgroup of order `N`, then `Y_0(N)` has no rational point.

The hypothesis is *verbatim* the hypothesis list of
`false_of_stable_of_y0HasNoRationalPoint`, so the two together say that the
modular and the elementary statements are EQUIVALENT for every `N`.

#### FAITHFULNESS AUDIT — this is TRUE unconditionally, and the standard
#### `j = 0, 1728` caveat does NOT apply to it

The docstring of `y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel` below
warned, correctly, that a bridge of this kind must not be stated "as a
universally quantified leaf without the descent hypothesis", because at a pair
with extra automorphisms it is false as a bare implication.  **That warning is
about a strictly stronger statement than this one and does not refute it.**
The distinction is exactly which object is required to be defined over `ℚ`:

* FALSE as a bare implication: *the pair `(E, C)` itself descends to `ℚ`*.  A
  `ℚ`-point of `Y_0(N)` carries only a `ℚ̄`-pair whose field of moduli is `ℚ`,
  and demanding that this particular pair be `ℚ`-rational is Weil descent with
  a possibly non-trivial obstruction.
* TRUE, and what is stated here: *SOME elliptic curve over `ℚ` carries a stable
  cyclic subgroup of order `N`*.  A quadratic/quartic/sextic TWIST is allowed,
  and that is what makes the obstruction vanish.

The computation, which is the check that would refute this if it were wrong.
Let `y ∈ Y_0(N)(ℚ)`.  Coarse moduli gives a `ℚ̄`-pair `(E, C)` with
`(E^σ, C^σ) ≅ (E, C)` for every `σ ∈ G_ℚ`; in particular `j(E) ∈ ℚ`, so `E`
already has a model over `ℚ` and we may take `E^σ = E`.  Then for each `σ`
there is `α_σ ∈ Aut_ℚ̄(E)` with `α_σ(σ C) = C`, well defined modulo
`A := Aut(E, C)`, and `σ ↦ ᾱ_σ` is a cocycle in `Z¹(G_ℚ, Aut(E)/A)`.  Now
`Aut(E) ≅ μ_n` as a `G_ℚ`-module with `n ∈ {2, 4, 6}`, and `−1 ∈ A` always,
since `−C = C`; so `A ∈ {μ₂, μ_n}` and the quotient is `1` or `μ_{n/2}`, the
isomorphism being induced by `x ↦ x²`.  Under Kummer theory that map on
cohomology is

`H¹(G_ℚ, μ_n) = ℚˣ/(ℚˣ)ⁿ ⟶ H¹(G_ℚ, μ_{n/2}) = ℚˣ/(ℚˣ)^{n/2}`, `a ↦ a`,

because `δ_n(a)(σ)² = (σ(a^{1/n})/a^{1/n})² = σ(a^{1/(n/2)})/a^{1/(n/2)}`.
That map is SURJECTIVE, so the cocycle is realised by a twist `E^{(d)}` of `E`
by some `d ∈ ℚˣ`, and the accompanying `ψ : E ≅ E^{(d)}` carries `C` to a
`G_ℚ`-stable subgroup — `μ₂` acting trivially on subgroups is what makes the
quotient by `A` harmless.  `E^{(d)}` is defined over `ℚ`.  ∎

Note the argument needs no case split on `j`: at `n = 2` the quotient is
already trivial, and the only inputs at `n = 4, 6` are surjectivity of
`ℚˣ/(ℚˣ)⁴ ↠ ℚˣ/(ℚˣ)²` and `ℚˣ/(ℚˣ)⁶ ↠ ℚˣ/(ℚˣ)³`.  **The check that refutes
this**: exhibit `n ∈ {4, 6}` and a class in `ℚˣ/(ℚˣ)^{n/2}` not in the image
of `ℚˣ/(ℚˣ)ⁿ` — impossible, both maps being induced by the identity on
representatives.

#### What proving it needs — and what of that is now DONE

Precisely the half of the coarse-moduli definition that `IsCoarseModuliY0`
deliberately omits — bijectivity of `classify` on geometric points, i.e.
`Y(ℚ̄) ↔ {(E, C)/ℚ̄}/≅`, `G_ℚ`-equivariantly — together with the descent
computation above.  The first was correctly diagnosed as reachable from
`Gamma0Atlas` / `Gamma0GITPresentation` and unreachable from initiality, and
its SURJECTIVITY half — the half this node consumes — is now PROVEN, as
`IsCoarseModuliY0.exists_gamma0Datum_of_algClosPoint`.  Its injectivity half
survives inside `exists_gamma0Datum_specQ_of_ratPoint`, packaged as the
hypothesis `hd`; see that leaf's docstring for how to split it off.

So exactly two leaves remain under this node, and they share no subject
matter: `exists_gamma0Datum_specQ_of_ratPoint` (the twisting/Kummer descent,
arithmetic) and `false_of_gamma0Datum_specQ` (the Weierstrass dictionary, the
converse of `nonempty_gamma0Datum_of_stable`, no modular curve in it).

Cusps are not an obstacle and need no hypothesis: `Y_0(N)` is the coarse space
of the moduli problem `[Γ₀(N)]`, whose objects are genuine elliptic schemes, so
it has no cuspidal points to begin with — the cusps appear only on the
compactification `X_0(N)` of `IsX0Compactification`. -/
theorem y0HasNoRationalPoint_of_not_stableCyclic {N : ℕ}
    (h : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
        (g : (E⁄(AlgebraicClosure ℚ)).Point), addOrderOf g = N →
        (∀ σ : Field.absoluteGaloisGroup ℚ,
          ∀ x ∈ AddSubgroup.zmultiples g,
            WeierstrassCurve.Affine.Point.map
              (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
              AddSubgroup.zmultiples g) → False) :
    Y0HasNoRationalPoint N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact y0HasNoRationalPoint_zero
  intro Y str hY
  constructor
  intro y
  obtain ⟨d, hd⟩ := hY.exists_gamma0Datum_of_algClosPoint hN
    (RelPoint.pre (specAlgClos ℚ) (Category.comp_id _) y)
  obtain ⟨d₀⟩ := exists_gamma0Datum_specQ_of_ratPoint hY y d hd
  exact false_of_gamma0Datum_specQ hN.ne' h d₀

/-- **No elliptic curve over `ℚ` has a Galois-stable cyclic subgroup of order
`p²`, for the seven isogeny primes with `genus X_0(p) ≥ 1`** (sorry node,
introduced 2026-07-27): `p ∈ {11, 17, 19, 37, 43, 67, 163}`.

TRUE, and it is the elementary half of Kenku's prime-square theorem: the
Mazur–Kenku list of `N` admitting a rational cyclic `N`-isogeny is
`1, …, 19, 21, 25, 27, 37, 43, 67, 163`, and each of
`121, 289, 361, 1369, 1849, 4489, 26569` exceeds `163`.

**The route, and why it terminates at exactly these seven primes.**  A
Galois-stable cyclic `⟨g⟩` of order `p²` gives the stable line `⟨p·g⟩ ⊂ E[p]`;
the Vélu quotient `E' := E/⟨p·g⟩` then carries TWO DISTINCT stable lines,
namely the image of `⟨g⟩` and the kernel of the dual isogeny `E' → E`, distinct
because `g` has order `p²` rather than `p`.  So the statement is equivalent to
*no elliptic curve over `ℚ` has two independent rational `p`-isogenies*, and
that terminates as soon as `Y_0(p)(ℚ)` is finite and listable.  See
`isogenyClassPrimeSqLevels` for the genus table that decides this: `X_0(p)` has
genus `1` and analytic rank `0` at `p = 11, 17, 19` (so `3, 2, 1` non-cuspidal
points, checked by enumeration), and genus `≥ 2` at `p = 37, 43, 67, 163` (so
finiteness by Faltings, with `1` non-cuspidal point at `43, 67, 163` — CM by
the class-number-one order of `ℚ(√-p)`, in which `p` RAMIFIES, so `E[p]` has a
unique stable line and two independent `p`-isogenies are impossible with no
enumeration at all — and the two explicit non-CM `j`-invariants `-7·11³` and
`-7·137³·2083³` at `p = 37`).

`p = 13` is excluded because `genus X_0(13) = 0` makes `Y_0(13)(ℚ)` infinite
and the reduction vacuous; that level is
`not_stableCyclic_oneHundredSixtyNine`.

DUPLICATES A DOWNSTREAM STATEMENT, DELIBERATELY.  This is the same assertion as
`WeierstrassCurve.not_cyclicIsogeny_sq_of_isogenyPrime_ge_eleven` in
`FreyCurve/MazurTorsion.lean`, which is marked PROVEN there — but that proof
routes through `y0HasNoRationalPoint_isogenyPrimeSq`, i.e. through the very
node this leaf is being used to prove, so it carries no content that can be
reused here, and that module imports this one in any case.  See the section
note above `y0HasNoRationalPoint_of_not_stableCyclic` for the re-basing that
removes the duplication.

Sources: Mazur, *Rational isogenies of prime degree*, Invent. Math. **44**
(1978), Theorem 1 and Table 1; Kenku, *On the modular curves `X_0(125)`,
`X_1(25)` and `X_1(49)`*, J. London Math. Soc. (2) **23** (1981). -/
theorem not_stableCyclic_sq_of_isogenyClassPrime {p : ℕ}
    (_hp : p ∈ ({11, 17, 19, 37, 43, 67, 163} : Finset ℕ))
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (_hg : addOrderOf g = p ^ 2)
    (_hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **No elliptic curve over `ℚ` has a Galois-stable cyclic subgroup of order
`169`** (sorry node, introduced 2026-07-27).

TRUE: `169 > 163`, so it is outside the Mazur–Kenku list.

**Why this is a node of its own** and not an instance of
`not_stableCyclic_sq_of_isogenyClassPrime`: `genus X_0(13) = 0`, so
`X_0(13) ≅ ℙ¹_ℚ`, `Y_0(13)(ℚ)` is INFINITE — a one-parameter family of curves
with a rational `13`-isogeny — and the two-independent-lines reduction that
handles the other seven primes degenerates into a tautology.  Level `169` must
be settled on `X_0(169)` itself, of genus `8`.  This is Kenku, *The modular
curve `X_0(169)` and rational isogeny*, J. London Math. Soc. (2) **22** (1980).

The reconnaissance and the two warnings recorded at
`y0HasNoRationalPoint_oneSixtyNine` below apply verbatim to this leaf, since
the two are now equivalent through `y0HasNoRationalPoint_of_not_stableCyclic`:
`rank J_0(169) < 8` is BSD-conditional, and the CRUDE Chabauty–Coleman counting
bounds cannot close the level for any prime.

DUPLICATES A DOWNSTREAM STATEMENT, DELIBERATELY — this is
`WeierstrassCurve.not_cyclicIsogeny_oneHundredSixtyNine` of
`FreyCurve/MazurTorsion.lean`, whose proof is `ex falso` from
`y0HasNoRationalPoint_oneSixtyNine` and therefore reusable nowhere.  See the
section note above `y0HasNoRationalPoint_of_not_stableCyclic`. -/
theorem not_stableCyclic_oneHundredSixtyNine
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (_hg : addOrderOf g = 169)
    (_hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **Kenku's prime-square determination at the seven levels with a
finite isogeny classification** (PROVEN 2026-07-27 over
`y0HasNoRationalPoint_of_not_stableCyclic` and
`not_stableCyclic_sq_of_isogenyClassPrime`; introduced as a sorry node
earlier the same day):
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

**~~The one obligation the reduction does not discharge~~ — NOW A NAMED
NODE, and the "do not state it" half of this paragraph is REFUTED**
(2026-07-27).  The paragraph read, correctly, that `Y0HasNoRationalPoint`
is a statement about the COARSE moduli space, that `IsCoarseModuliY0`
deliberately omits bijectivity on geometric points, and that a rational
point of `Y_0(p²)` therefore carries only a `ℚ̄`-pair with field of moduli
`ℚ`, whose descent to `ℚ` is Weil descent against `Aut(E, C)`.  All of
that is retained and is now the content of
`y0HasNoRationalPoint_of_not_stableCyclic`.

What is struck out is the injunction that followed — *"do not state the
bridge as a universally quantified leaf without the descent hypothesis;
for a pair with extra automorphisms it is false as a bare implication"*.
It conflates two statements, and only the stronger one is false:

* FALSE: *the pair `(E, C)` itself is defined over `ℚ`.*  That is where
  the `j = 0, 1728` caveat bites.
* TRUE: *SOME elliptic curve over `ℚ` carries a stable cyclic subgroup of
  order `p²`.*  A TWIST is permitted, and permitting it kills the
  obstruction — `−1 ∈ Aut(E, C)` always, `Aut(E) ≅ μ_n` with
  `n ∈ {2, 4, 6}`, and `ℚˣ/(ℚˣ)ⁿ ↠ ℚˣ/(ℚˣ)^{n/2}` is surjective, so the
  obstruction class is always realised by a twist.  The full computation
  is the FAITHFULNESS AUDIT of
  `y0HasNoRationalPoint_of_not_stableCyclic`.

Consumers only ever need the weaker form, so the bridge is stated
unconditionally and this node is proven from it.

NO LONGER IRREDUCIBLE, but the remaining content is unchanged and now
sits in `not_stableCyclic_sq_of_isogenyClassPrime`: the classification of
`Y_0(p)(ℚ)` for the seven primes (Mazur's Theorem 1 in its sharp,
point-listing form — `cuspidal_x0_prime` above is only the emptiness
half, which says nothing at these seven) and the Vélu quotient.  What the
cut removes from that leaf is the field-of-moduli descent, which is
uniform in `N` and is now shared with every other level node.

Sources: Mazur, *Rational isogenies of prime degree*, Invent. Math. **44**
(1978), Theorem 1 and Table 1; Kenku, *The modular curves `X_0(65)` and
`X_0(91)` and rational isogeny*, Math. Proc. Cambridge Philos. Soc. **87**
(1980); *On the modular curves `X_0(125)`, `X_1(25)` and `X_1(49)`*,
J. London Math. Soc. (2) **23** (1981). -/
theorem y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel (N : ℕ)
    (hN : N ∈ isogenyClassPrimeSqLevels) : Y0HasNoRationalPoint N := by
  refine y0HasNoRationalPoint_of_not_stableCyclic (fun E _ g hg hstable => ?_)
  simp only [isogenyClassPrimeSqLevels, List.mem_cons, List.not_mem_nil,
    or_false] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_stableCyclic_sq_of_isogenyClassPrime (p := 11) (by decide) E g
      (hg.trans (by norm_num)) hstable
  · exact not_stableCyclic_sq_of_isogenyClassPrime (p := 17) (by decide) E g
      (hg.trans (by norm_num)) hstable
  · exact not_stableCyclic_sq_of_isogenyClassPrime (p := 19) (by decide) E g
      (hg.trans (by norm_num)) hstable
  · exact not_stableCyclic_sq_of_isogenyClassPrime (p := 37) (by decide) E g
      (hg.trans (by norm_num)) hstable
  · exact not_stableCyclic_sq_of_isogenyClassPrime (p := 43) (by decide) E g
      (hg.trans (by norm_num)) hstable
  · exact not_stableCyclic_sq_of_isogenyClassPrime (p := 67) (by decide) E g
      (hg.trans (by norm_num)) hstable
  · exact not_stableCyclic_sq_of_isogenyClassPrime (p := 163) (by decide) E g
      (hg.trans (by norm_num)) hstable

/-- **Kenku's determination at level `169`** (PROVEN 2026-07-27 over
`y0HasNoRationalPoint_of_not_stableCyclic` and
`not_stableCyclic_oneHundredSixtyNine`; introduced as a sorry node
earlier the same day): `Y_0(169)(ℚ) = ∅`.

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

NO LONGER IRREDUCIBLE, but not one step easier either (2026-07-27).  The
node is now PROVEN from `y0HasNoRationalPoint_of_not_stableCyclic` and
`not_stableCyclic_oneHundredSixtyNine`, which strips off the
field-of-moduli descent — uniform in `N`, and shared with every other
level node — and leaves the arithmetic exactly as it was.  Both warnings
above transfer verbatim to
`not_stableCyclic_oneHundredSixtyNine` and neither is weakened by the
cut: the level still needs `p`-adic integration on curves, which exists
in no form here, on top of the integral model and Jacobian machinery the
rank-`0` route already lacks, and `rank J_0(169) < 8` is still available
only conditionally on BSD. -/
theorem y0HasNoRationalPoint_oneSixtyNine : Y0HasNoRationalPoint 169 :=
  y0HasNoRationalPoint_of_not_stableCyclic
    (fun E _ g hg hstable => not_stableCyclic_oneHundredSixtyNine E g hg hstable)

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

/-! #### The `61` semiprime levels, partitioned by the method that settles each

The declarations below cut `cuspidal_x0_semiprime_of_mazurPrimes`
along the partition that the LITERATURE and the arithmetic actually use,
rather than along a guess.  The partition, and the reconnaissance behind
it, is the substance of this block; read it before dispatching anyone at
the leaves, because the four leaves have four genuinely different
prospects and only one of them was closable with machinery this file
already had.

**Where the assembly lives (2026-07-27).**  That one leaf —
`y0HasNoRationalPoint_of_witnessSemiprimeLevel`, the levels `35, 39` —
is now CLOSED, over `y0HasNoRationalPoint_of_witnessPrime`.  Since that
criterion needs the whole compactification/Jacobian/reduction section,
Lean's declaration order forced the four assembled declarations —
`y0HasNoRationalPoint_of_witnessSemiprimeLevel`,
`y0HasNoRationalPoint_of_smallSemiprimeLevel`,
`cuspidal_x0_semiprime_of_mazurPrimes` and
`y0HasNoRationalPoint_semiprime_of_mazurPrimes` — down into
`### The twelve levels of Kenku's non-prime-power determination`, where
they sit immediately before their consumer
`y0HasNoRationalPoint_prod_two_primes`.  What stays HERE is the
partition itself: the three `List ℕ` definitions, the three open leaves,
and `mem_smallSemiprimeLevels`.  Nothing about the mathematics changed
with the move.

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

/-- **The `j`-invariants of the non-cuspidal rational points of `X_0(p)`,
for the seven `p ∈ isolatedIsogenyPrimes`** — Mazur, *Rational isogenies
of prime degree*, Invent. Math. **44** (1978), Theorem 1 and its table.

| `p` | non-cuspidal `j` | CM |
|-----|------------------|----|
| `11`  | `−2¹⁵ = −32768`; `−11² = −121`; `−11·131³ = −24729001` | first only, disc `−11` |
| `17`  | `−17·373³/2¹⁷`; `−17²·101³/2` | no |
| `19`  | `−2¹⁵·3³ = −884736` | disc `−19` |
| `37`  | `−7·11³ = −9317`; `−7·137³·2083³` | no |
| `43`  | `−2¹⁸·3³·5³ = −884736000` | disc `−43` |
| `67`  | `−2¹⁵·3³·5³·11³ = −147197952000` | disc `−67` |
| `163` | `−2¹⁸·3³·5³·23³·29³ = −262537412640768000` | disc `−163` |

The two fractional and the two large entries were recomputed with
PARI/GP 2.17.4 on 2026-07-27 from the factorisations in the middle
column: `−17·373³ = −882216989` over `2¹⁷ = 131072`;
`−17²·101³ = −297756989` over `2`; `−7·137³·2083³ =
−162677523113838677`; `−2¹⁸·3³·5³ = −884736000`.  Only the last four CM
values are the classical singular moduli of discriminants
`−19, −43, −67, −163`.

**CORRECTED 2026-07-27 — what this table is FOR.**  This paragraph
previously read "the one property of this table that the argument
actually uses is that no entry is `0` or `1728`", and attributed that
use to `y0HasNoRationalPoint_of_no_stable_isolated`, on the ground that
at `j ∉ {0, 1728}` the geometric automorphism group of a pair `(E, C)`
is `{±1}` and so a `ℚ`-rational point of the coarse space descends to a
pair over `ℚ` up to quadratic twist.  **That descent does not need the
table**, and the node in question is no longer a leaf: it is a wrapper
around `y0HasNoRationalPoint_of_not_stableCyclic`, whose FAITHFULNESS
AUDIT gives the descent with no case split on `j` at all, because a
twist by any `d ∈ ℚˣ` is allowed and `−1 ∈ Aut(E, C)` always.

The table's real consumers are the two ARITHMETIC leaves,
`mem_isolatedJInvariants_of_stable` (it is the target of Mazur's
Theorem 1) and `not_stable_of_mem_isolatedJInvariants` (the CM /
explicit-check split runs row by row over it).  There it is entirely
load-bearing, and the `0`/`1728` observation is a true remark about it
rather than the property the tree consumes.

Levels outside `isolatedIsogenyPrimes` get `∅`, which is *false* as a
statement about `X_0(p)(ℚ)` for `p ∈ {2, 3, 5, 7, 13}` (there the curve
is `ℙ¹` and there are infinitely many `j`); every consumer below carries
`p ∈ isolatedIsogenyPrimes`, so the junk branch is never reached. -/
def isolatedJInvariants (p : ℕ) : Finset ℚ :=
  if p = 11 then {-32768, -121, -24729001}
  else if p = 17 then {-882216989 / 131072, -297756989 / 2}
  else if p = 19 then {-884736}
  else if p = 37 then {-9317, -162677523113838677}
  else if p = 43 then {-884736000}
  else if p = 67 then {-147197952000}
  else if p = 163 then {-262537412640768000}
  else ∅

/-- **Galois stability passes from `⟨g⟩` to `⟨n • g⟩`** (PROVEN).

This is the elementary step that turns a Galois-stable cyclic subgroup
of order `p * q` into one of order `p` and one of order `q`: the
subgroups of a cyclic group are its `⟨n • g⟩`, and stability is
inherited because `σ` is additive and sends `g` into `⟨g⟩`.

Concretely, if `σ · g = m • g` then
`σ · (k • n • g) = k • n • m • g = (k m) • n • g`, so the image stays in
`⟨n • g⟩`.  Nothing about elliptic curves enters — only that
`WeierstrassCurve.Affine.Point.map` is an `AddMonoidHom`. -/
theorem stable_zmultiples_nsmul {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {g : (E⁄(AlgebraicClosure ℚ)).Point} (n : ℕ)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g) :
    ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples (n • g),
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples (n • g) := by
  intro σ x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hstable σ g (AddSubgroup.mem_zmultiples g))
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k * m, ?_⟩
  rw [map_zsmul, map_nsmul, ← hm, smul_comm n m g, smul_smul]

/-- **The coarse-to-fine descent at a level divisible by an isolated
Mazur prime** (PROVEN 2026-07-27 BY CITATION; formerly a sorry leaf): to
prove `Y_0(N)(ℚ) = ∅` it is enough to refute the existence of a
Weierstrass curve over `ℚ` with a Galois-stable cyclic subgroup of order
`N`.

This is the exact CONVERSE of `false_of_stable_of_y0HasNoRationalPoint`,
and it is the only place where the coarse-space subtlety enters the
`56`-level family.  Stated in contrapositive form — "no curve ⟹ no
point" rather than "point ⟹ curve" — so that the hypothesis is literally
the hypothesis shape of the two arithmetic leaves below, with no
existential repackaging of `[E.IsElliptic]`.

## THIS NODE WAS A REDUNDANT RESTATEMENT (found 2026-07-27)

`y0HasNoRationalPoint_of_not_stableCyclic`, six hundred lines above in
this same file and introduced on the same day as this one, has
**verbatim the same hypothesis and verbatim the same conclusion, with no
`p` in it at all**.  This node is that node plus three hypotheses that
its proof does not use, so it follows from it by application and nothing
else — which is what its proof now is.  Two cuts were made
independently at the same statement, and the frontier carried **two**
open leaves standing for **one** open question.  It now carries it once,
at `y0HasNoRationalPoint_of_not_stableCyclic`, and that is where a
prover should be sent; the general node is also already the descent
bridge for the prime-square family
(`y0HasNoRationalPoint_of_isogenyClassPrimeSqLevel`,
`y0HasNoRationalPoint_oneSixtyNine`), so closing it closes three level
families at once rather than one.

**`_hp`, `_hN` and `_hpN` are unused, and that is a fact about the
descent rather than an artefact of the wrapper.**  The
`isolatedJInvariants` route set out below — push down to level `p`, read
off Mazur's table, observe that no entry is `0` or `1728`, hence
`Aut_ℚ̄(E) = {±1}` — is *a* proof, and it is the one this node's cut was
designed around.  It is not the one the general node needs.  The
FAITHFULNESS AUDIT of `y0HasNoRationalPoint_of_not_stableCyclic` gives a
descent that **needs no case split on `j` whatever**, because only
*some* curve over `ℚ` is asked for, so a quadratic/quartic/sextic TWIST
is allowed: `−1 ∈ Aut(E, C)` always (`−C = C`), the obstruction lives in
`H¹(G_ℚ, Aut(E)/A)` with `Aut(E)/A` a quotient of `μ_n` by `μ₂`, and
`ℚˣ/(ℚˣ)ⁿ ↠ ℚˣ/(ℚˣ)^(n/2)` is surjective.  So the `j = 0, 1728` caveat
that motivates `_hp`/`_hpN` here is a caveat about a *strictly stronger*
statement — that the pair `(E, C)` itself descend — and a successor
should not reintroduce these hypotheses.

The two arithmetic leaves below are untouched by this and the table is
genuinely load-bearing in them: `mem_isolatedJInvariants_of_stable` is
Mazur's Theorem 1 and `not_stable_of_mem_isolatedJInvariants` is the
no-second-isogeny statement.  What the finding removes is only the
*third* copy of the coarse-space obligation, not any arithmetic.

### The argument this node was cut for, kept for the record

**TRUE, and here is the proof.**  A `ℚ`-rational point of the coarse
space is a `Γ_ℚ`-stable `ℚ̄`-isomorphism class of pairs `(E, C)` with `C`
cyclic of order `N`.  Push it down the degeneracy map to level `p`
(`Gamma0Datum.ofDvd`, `hpN`); by Mazur's Theorem 1 its `j`-invariant is
one of the entries of `isolatedJInvariants p`, **none of which is `0` or
`1728`**.  So `Aut_ℚ̄(E) = {±1}`.  Choose any `E₀/ℚ` with that
`j`-invariant (an explicit Weierstrass equation) and transport `C` to
`C₀ ⊆ E₀(ℚ̄)`; for each `σ` the comparison isomorphism differs from its
conjugate by an element of `{±1}`, which fixes every subgroup, so
`σ(C₀) = C₀`.  Hence `C₀` is Galois-stable and `(E₀, C₀)` is the curve
`hno` refutes.

**Why `hp`/`hpN` are load-bearing, i.e. why this is NOT stated for all
`N`.**  The `{±1}` step needs `j ∉ {0, 1728}`, and at `j = 0` (`Aut = μ₆`)
or `j = 1728` (`Aut = μ₄`) an automorphism of order `3` or `4` can MOVE
`C`, so the pair need not descend.  A version of this statement
quantified over all `N` with no isolated-prime hypothesis would therefore
be an unsupported — quite possibly false — leaf, and `isolatedJInvariants`
is precisely the certificate that rules those two `j`-values out.

**NOT VACUOUS**, and this is worth checking because the leaf feeds a
theorem asserting the emptiness of the very set it quantifies over.  Take
`N = p`: `Y_0(11)(ℚ)` has three non-cuspidal points, `Y_0(17)(ℚ)` and
`Y_0(37)(ℚ)` two each, and the remaining four one each, so at `N = p` the
statement has genuine content and its proof is exactly the descent above.
It is the SAME argument at `N = p q`, which is why the leaf is stated for
`p ∣ N` rather than for `N = p q`: the general form is the honest one and
the divisible form is what the assembly needs.

**The obstruction is REAL and it has simply MOVED, one declaration up
the chain.**  The verdict this paragraph replaces read "IRREDUCIBLE at
this pin: the descent needs the identification of the `ℚ`-points of the
coarse space with `Γ_ℚ`-stable `ℚ̄`-classes, which is the content of
`IsCoarseModuliY0.universal` in the direction initiality does not
provide, plus `Aut(E) = {±1}` for `j ∉ {0, 1728}`".  The first half of
that is exactly right and is now recorded where it belongs, in the
"What proving it needs" section of
`y0HasNoRationalPoint_of_not_stableCyclic`: bijectivity of `classify` on
geometric points is the half of the coarse-moduli definition that
`IsCoarseModuliY0` deliberately omits, initiality alone can never supply
it, and it is reachable from `Gamma0Atlas` / `Gamma0GITPresentation`,
which are already in this file.  The second half is *not* needed, per
the twisting argument above.  **Nothing here has become easier; one of
two copies of the same open question has gone away.** -/
theorem y0HasNoRationalPoint_of_no_stable_isolated {p N : ℕ}
    (_hp : p ∈ isolatedIsogenyPrimes) (_hN : N ≠ 0) (_hpN : p ∣ N)
    (hno : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point),
      addOrderOf g = N →
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) → False) :
    Y0HasNoRationalPoint N :=
  y0HasNoRationalPoint_of_not_stableCyclic hno

/-- **Mazur's Theorem 1, in the form the descent needs** (sorry node,
introduced 2026-07-27): a curve over `ℚ` with a rational `p`-isogeny, for
`p` one of the seven isolated Mazur primes, has one of the tabulated
`j`-invariants.

TRUE: Mazur, *Rational isogenies of prime degree*, Invent. Math. **44**
(1978), Theorem 1.  For `p ∈ {11, 17, 19, 37, 43, 67, 163}` the curve
`X_0(p)` has positive genus and `X_0(p)(ℚ)` is finite and completely
tabulated; the non-cuspidal points are the `j`-invariants collected in
`isolatedJInvariants`.

**No scheme theory appears in this statement.**  That is deliberate and
is the point of the cut: `mem_isolatedJInvariants_of_stable` and
`not_stable_of_mem_isolatedJInvariants` are pure statements about
Weierstrass curves over `ℚ` and their `ℚ̄`-torsion, so they can be owned
and attacked by someone with no modular-curve machinery, while all the
moduli theory sits in `y0HasNoRationalPoint_of_no_stable_isolated`.

IRREDUCIBLE at this pin: Mazur's theorem is not in `Mathlib`, not in
`~/cs/FLT`, and not in this project.  Its proof is the Eisenstein-ideal
argument — the deepest input to the whole `X_0` subtree. -/
theorem mem_isolatedJInvariants_of_stable {p : ℕ} (_hp : p ∈ isolatedIsogenyPrimes)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point)
    (_hg : addOrderOf g = p)
    (_hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g) :
    E.j ∈ isolatedJInvariants p :=
  sorry

/-- **None of the seven isolated `j`-invariant families admits a second
isogeny** (sorry node, introduced 2026-07-27): if `E.j` is one of the
`j`-invariants of `X_0(p)(ℚ)` for `p` isolated, then `E` has no rational
`q`-isogeny for any prime `q ≠ p`.

TRUE, and it is the arithmetic heart of the `56`-level family.

**For the five CM rows** — `j = −32768` (disc `−11`), `−884736`
(`−19`), `−884736000` (`−43`), `−147197952000` (`−67`),
`−262537412640768000` (`−163`) — the argument is uniform and clean.  The
mod-`ℓ` image of `Γ_ℚ` lies in the normalizer of a Cartan subgroup
attached to `K = ℚ(√−p)`, and a `Γ_ℚ`-stable line in `E[ℓ]` exists only
when `ℓ` ramifies in `K`, i.e. only for `ℓ = p`.

**For the four non-CM values** — `−121` and `−24729001` at `p = 11`, and
`−9317`, `−162677523113838677` at `p = 37`, plus the two `p = 17` values
— it is a finite explicit check.  Confirmed against LMFDB at `p = 11`:
the three `j`-invariants give isogeny classes `121.a`, `121.b`, `121.c`,
each of size `2`, each with the single isogeny degree `11`.

**CIRCULARITY WARNING — READ THIS BEFORE ATTEMPTING A PROOF.**  Do NOT
discharge this by citing Kenku's list of possible cyclic isogeny degrees
over `ℚ` (J. Number Theory **15** (1982) 199–202).  That list is
precisely what this subtree is proving: "a curve with an `11`-isogeny has
no `2`-isogeny" IS the assertion that `22` is not an isogeny degree.  The
proof must go through the explicit `j`-invariants above and the CM /
explicit-check split.

IRREDUCIBLE at this pin: it needs the CM theory of the mod-`ℓ` image
(Deuring; Serre 1972 §4) for the five CM rows, and an explicit
`ℓ`-division-polynomial computation for the four non-CM ones.  Neither
the Cartan-normalizer classification nor `E[ℓ]` as a Galois module in the
required form exists here. -/
theorem not_stable_of_mem_isolatedJInvariants {p q : ℕ} (_hp : p ∈ isolatedIsogenyPrimes)
    (_hq : q.Prime) (_hpq : p ≠ q) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (_hj : E.j ∈ isolatedJInvariants p) (g : (E⁄(AlgebraicClosure ℚ)).Point)
    (_hg : addOrderOf g = q)
    (_hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g) :
    False :=
  sorry

/-- **The `56` levels with an isolated prime** (PROVEN 2026-07-27 by
decomposition): for `p ∈ isolatedIsogenyPrimes` and any prime `q ≠ p`,
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
must go through the explicit `j`-invariants above.  The warning is now
carried by `not_stable_of_mem_isolatedJInvariants`, which is where a
prover will meet it.

**Stated uniformly in `q`, which is stronger than needed and easier to
prove.**  Only the `56` cases with `q ∈ mazurIsogenyPrimes` are consumed
here; for the other `q` the conclusion already follows from
`y0HasNoRationalPoint_prime` through `y0HasNoRationalPoint_of_dvd` at
`q ∣ pq`.  The descent argument does not look at `q` at all, so
restricting the statement would buy nothing.  It is TRUE as stated: every
`pq` with `p ≥ 11` is at least `22`, and the only members of the
Mazur–Kenku list that large are `25, 27, 37, 43, 67, 163`, none of which
is a product of two distinct primes.

## THE CUT (2026-07-27) — this node is NO LONGER A LEAF

The previous version of this docstring recorded the node as IRREDUCIBLE
"because it needs Mazur's determination of `X_0(p)(ℚ)` plus the CM
theory of the mod-`ℓ` image".  Both halves of that are true and neither
of them has become available — but the verdict conflated *needing* a
theory with *needing it proven before the node can be cut*.  Three
declarations above carry the three ingredients separately:

* `y0HasNoRationalPoint_of_no_stable_isolated` — the coarse-to-fine
  descent, and the ONLY piece that touches moduli theory.  **It is no
  longer a leaf** (2026-07-27): it turned out to be a strictly weaker
  restatement of `y0HasNoRationalPoint_of_not_stableCyclic`, six hundred
  lines above, which has the same hypothesis and the same conclusion
  with no `p` in it, and is already the descent bridge for the
  prime-square family.  So the moduli obligation of this family is the
  *same* obligation as that of the prime squares, not a second one, and
  it is open in exactly one place.  See that node's docstring for what
  proving it needs;
* `mem_isolatedJInvariants_of_stable` — Mazur's Theorem 1;
* `not_stable_of_mem_isolatedJInvariants` — no second isogeny.

The last two are statements about Weierstrass curves over `ℚ` and their
`ℚ̄`-torsion, with **no scheme theory in sight**, so they are ownable by
someone who never opens this module's first four thousand lines.  That
separation is most of the value of the cut, and it survives the merge of
the first item into the general bridge.

**The assembly, which is what this proof is.**  A Galois-stable cyclic
subgroup of order `p q` contains one of order `p` (namely `⟨q • g⟩`) and
one of order `q` (namely `⟨p • g⟩`), both still Galois-stable by
`stable_zmultiples_nsmul`; the orders are `addOrderOf_nsmul'` plus
`Nat.gcd (p q) q = q`.  Mazur's table applied to the first pins `E.j`,
and the second-isogeny leaf applied to the second gives `False`.  Note
that the SAME `E` carries both, which is exactly what a push-forward to
level `p` and to level `q` separately would NOT give — and is why the
descent leaf is stated at level `p q` rather than at level `p`. -/
theorem y0HasNoRationalPoint_of_isolatedSemiprime {p q : ℕ}
    (hp : p ∈ isolatedIsogenyPrimes) (hq : q.Prime) (hpq : p ≠ q) :
    Y0HasNoRationalPoint (p * q) := by
  have hp0 : p ≠ 0 := by fin_cases hp <;> decide
  refine y0HasNoRationalPoint_of_no_stable_isolated hp
    (Nat.mul_ne_zero hp0 hq.ne_zero) (dvd_mul_right p q) ?_
  intro E _ g hg hstable
  have hordp : addOrderOf (q • g) = p := by
    rw [addOrderOf_nsmul' _ hq.ne_zero, hg, Nat.gcd_eq_right (dvd_mul_left q p),
      Nat.mul_div_cancel _ hq.pos]
  have hordq : addOrderOf (p • g) = q := by
    rw [addOrderOf_nsmul' _ hp0, hg, Nat.gcd_eq_right (dvd_mul_right p q),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp0)]
  exact not_stable_of_mem_isolatedJInvariants hp hq hpq E
    (mem_isolatedJInvariants_of_stable hp E (q • g) hordp
      (stable_zmultiples_nsmul q hstable))
    (p • g) hordq (stable_zmultiples_nsmul p hstable)

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
inside Ogg's classical method — see the section docstring.

## THE CUT IS BLOCKED BY DECLARATION ORDER, NOT BY MATHEMATICS
## (audited and MEASURED 2026-07-27 — read this before dispatching)

The right decomposition is known, it is three lines long, and it
**compiles**.  What blocks taking it *here* is that every declaration it
needs is defined **about 900 lines BELOW this point** in this same file.
The two halves are:

* a criterion, provable from `exists_x0Compactification`,
  `exists_rationalCusps` and `y0HasNoRationalPoint_of_isEmpty`, identical
  in shape to `y0HasNoRationalPoint_of_sieveLevel`:

      theorem y0HasNoRationalPoint_of_cardLeCusps (N : ℕ) (hN : 0 < N)
          (hbound : ∀ {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ}
              {jm : Y ⟶ X}, IsX0Compactification N strX strY jm →
              ∀ t : Finset (RelPoint strX (𝟙 SpecQ)), t.card ≤ numRationalCusps N) :
          Y0HasNoRationalPoint N

* and the single residual leaf it consumes, which is where the sieve
  goes:

      theorem card_le_x0TwentySix {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
          {strY : Y ⟶ SpecQ} {jm : Y ⟶ X}
          (hX : IsX0Compactification 26 strX strY jm)
          (t : Finset (RelPoint strX (𝟙 SpecQ))) : t.card ≤ numRationalCusps 26

  after which this node is `y0HasNoRationalPoint_of_cardLeCusps 26
  (by norm_num) (fun hX t => card_le_x0TwentySix hX t)`.

Both were written out and verified green in a scratch module importing
`Fermat.FLT.ModularCurve.X0` on 2026-07-27; the only reason they are not
in the file is that `IsX0Compactification`, `numRationalCusps`,
`sectionAlong`, `exists_x0Compactification` and `exists_rationalCusps`
all come after this line.  **A CLEAN SCRATCH MODULE PROVES NOTHING ABOUT
DECLARATION ORDER** — that is the trap this note exists to record, and it
is the reason the cut was designed, verified, and then not taken.

**So the task at this node is a RELOCATION, not a proof.**  Moving
`y0HasNoRationalPoint_x0TwentySix` below `exists_rationalCusps` drags
`y0HasNoRationalPoint_of_smallSemiprimeLevel`,
`cuspidal_x0_semiprime_of_mazurPrimes` and
`y0HasNoRationalPoint_semiprime_of_mazurPrimes` with it, and on
2026-07-27 that whole block was under concurrent edit by another owner
(`y0HasNoRationalPoint_of_witnessSemiprimeLevel`, immediately above).
Whoever takes it should first check `~/.flt-inflight.jsonl` for owners in
this block and do the move in one commit.

**Then, and only then, the deeper cut becomes available.**  Once
`card_le_x0TwentySix` sits beside the sieve machinery it should NOT stay
a single leaf: `exists_x0Sieve`'s proof is five lines, and `26` needs
only its own two inputs — `hasRankZeroJacobian_x0TwentySix` (rank `0` at
`26`, Kolyvagin–Logachev, the same statement as
`hasRankZeroJacobian_of_kenkuLevel`) and `exists_sharpSievePrime_twentySix`
(the arithmetic residue) — because `exists_x0NeronDatum` and
`neronReduction_injective` are already universal in `ℓ` and in `N`.
Adding `26` to `x0SieveLevels` and `kenkuLevels` instead would be
simpler still, and is the right move whenever those two lists are not
under concurrent edit; on 2026-07-27 both were. -/
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
Jacobian and its Mordell–Weil group.

## WHICH AXIS THE IRREDUCIBILITY VERDICT WAS SEARCHED ON (2026-07-27)

The verdict above is about the **theory** axis: no route to a BOUND on
`#X_0(N)(ℚ)` exists here for positive rank, and that was re-checked —
`card_le_of_rankZeroJacobian` and `card_le_of_sieve` both consume
`HasRankZeroJacobian`, which is FALSE at `65` and `91`, so neither can be
weakened into service by any amount of interface work.  Nothing was found
on the `~/cs/FLT` or `Mathlib` axes either: neither has a Coleman
integral, a `p`-adic differential, or a Jacobian of a curve.

What the verdict does **not** cover, and what a successor should take, is
the **placement** axis.  The node still decomposes into one criterion and
one leaf, exactly as `26` does above, and the criterion is shared:

    theorem card_le_of_chabautySemiprimeLevel {N : ℕ}
        (hN : N ∈ chabautySemiprimeLevels) {X Y : Scheme.{0}}
        {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jm : Y ⟶ X}
        (hX : IsX0Compactification N strX strY jm)
        (t : Finset (RelPoint strX (𝟙 SpecQ))) : t.card ≤ numRationalCusps N

    theorem y0HasNoRationalPoint_of_chabautySemiprimeLevel (N : ℕ)
        (hN : N ∈ chabautySemiprimeLevels) : Y0HasNoRationalPoint N := by
      have hpos : 0 < N := by fin_cases hN <;> norm_num
      exact y0HasNoRationalPoint_of_cardLeCusps N hpos
        (fun hX t => card_le_of_chabautySemiprimeLevel hN hX t)

Verified green in a scratch module on 2026-07-27, and blocked in place by
the same declaration-order obstruction recorded under
`y0HasNoRationalPoint_x0TwentySix` — `IsX0Compactification`,
`numRationalCusps` and `exists_rationalCusps` are all defined below this
line.  **The gain from taking it is real but modest**: it moves the leaf
off the coarse moduli space and onto a point count for `X_0(N)`, which is
the only form in which Chabauty–Coleman can ever be applied, and it makes
`exists_rationalCusps` — already proven here — carry the cusp half.  It
does not make the leaf any less deep. -/
theorem y0HasNoRationalPoint_of_chabautySemiprimeLevel (N : ℕ)
    (_hN : N ∈ chabautySemiprimeLevels) : Y0HasNoRationalPoint N :=
  sorry

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
strictly larger at two of the nine levels below — `12` against `6` at
`N = 36`, and `12` against `4` at `N = 50`.  Counting against the total
rather than against the rational count would make the level statements
unprovable there, and is the trap this definition exists to avoid.

Values consumed below, each by `decide`:
`20 ↦ 6`, `24 ↦ 8`, `28 ↦ 6`, `30 ↦ 8`, `35 ↦ 4`, `36 ↦ 6`, `39 ↦ 4`,
`42 ↦ 8`, `50 ↦ 4`.  At the two squarefree semiprime levels `35 = 5 · 7`
and `39 = 3 · 13` every divisor `d` has `gcd(d, N/d) = 1`, so all four
cusps are rational and the total and rational counts agree. -/
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
"reduction of a cusp is a cusp" leaf should not be written at all.

**STALE-NOTE CORRECTION (2026-07-27).**  An earlier version of the audit
above said the remedy was "already in flight ... on branch `flt-lean-12`".
It has LANDED, and it is in this very file: `IsX0NeronDatum` (below, in the
Néron subsection) carries the integral models over `ℤ_(ℓ)` with both fibres
identified as equivalences of FUNCTORS of points, and there `redX`/`redJ`
are induced maps — which is why `red_aj` and `redJ_add` are theorems there
rather than assumptions.  So re-founding `IsX0JReductionAt` on
`IsX0NeronDatum`, and making `red_jm` a theorem, is available work TODAY.
Until someone does it, the audit above still applies to THIS structure, and
the formal-immersion leaf must be stated against a datum produced together
with it — which is what `exists_eisensteinFormalImmersionAt` does — never
against an arbitrary one. -/
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
        letI := d.cyc.etale_of_specQBase (𝟙 SpecQ)
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
Weierstrass construction, which was *already* an owned item when this cut
was written.  **UPDATE 2026-07-27: it has since landed, and that half is
now CLOSED.**  `exists_weierstrassModel_gamma0Datum` is PROVEN below,
from `exists_ellipticScheme_isWeierstrassModel_of_projModel`
(`Fermat/FLT/ModularCurve/EllipticScheme.lean`), which is
`exists_ellipticScheme_of_projModel` with the coordinate conjunct
retained.  Its one residual leaf, `exists_affineChart_projModel`, is a
concrete statement about `Proj` — the basic open `D₊(Z)` is `Spec` of the
affine coordinate ring and its complement is the unit section — and it
lives with the other five projective-model leaves rather than here.  So
what is left in THIS subsection is purely the moduli-theoretic `j`-theory,
`exists_jSection`.

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

/-! #### The cut of `exists_jSection`: affine bases, and Zariski descent

`exists_jSection` asks for the `j`-invariant over EVERY `ℚ`-scheme `T`,
and that is two different difficulties welded together:

* over an AFFINE base the question is elliptic-curve geometry — an
  elliptic scheme over `Spec R` acquires a Weierstrass model after
  inverting finitely many elements of `R`, `c₄³/Δ` is a well-defined
  element of each localization, and the pieces agree because two models
  of one elliptic scheme differ by a variable change;
* over a GENERAL base the question is descent — a natural transformation
  defined on affines extends uniquely to all schemes, because
  `Hom(-, 𝔸¹_ℚ)` is a Zariski sheaf.

Nothing about elliptic curves enters the second, and nothing about
schemes-in-general enters the first.  So they are cut apart below into
`exists_jSectionOnAffine` and `exists_jTransformation_of_affine`, with a
third leaf, `exists_gamma0Datum_baseChange`, supplying the one piece of
infrastructure both of them need and neither of them is about.

**Why a third leaf for base change, and why it is not pedantry.**
`IsBaseChangeOf` is *stated* in this file, never CONSTRUCTED — the module
docstring for it says so explicitly, and every consumer so far has
received one as a hypothesis.  But the descent argument has to RESTRICT a
datum to an affine open before it can apply the affine theory, and there
is nothing at this pin that produces the restricted datum.  That gap is
invisible in the statement of `exists_jSection` and would have been
discovered only by whoever tried to prove it, which is exactly the kind
of thing a cut should surface.  It is also reusable: any future argument
that localizes a moduli problem needs it.

**What the assembly actually contributes**, so that this is visibly not a
repackaging: `exists_jTransformation_of_affine` produces only the first
TWO fields of `IsJSection` — the transformation and its naturality —
together with the statement that it AGREES with the affine one on affine
bases.  The pinning field `jt_model` is not among them, and is derived
below by instantiating the agreement at `R = ℚ` and composing with
`IsJSectionOnAffine.jt_model`.  Had the descent leaf been allowed to
return an `IsJSection` outright it would have been the whole theorem
again under a new name, and the agreement clause would have been an
unconsumed binding.

**Why the agreement clause also makes the descent leaf non-vacuous.**
`IsJTransformation` on its own is satisfiable by junk — take `jt` to be
the constant section `0`, which is natural.  It is the agreement on
affines that gives the leaf content, and it gives it FULLY: every scheme
has an affine open cover, so naturality plus agreement on affines
determines `jt` on all of `T`.  So the leaf is neither vacuous nor
under-determined. -/

/-- **The `j`-invariant of an elliptic scheme over an AFFINE base.**

This is `IsJSection` with the base restricted to affine schemes in the
first two fields, and with the third — the pinning against
`WeierstrassCurve.j` — unchanged, since `SpecQ` is itself affine.

The restriction is a genuine weakening and not a reformulation: `jt` is
asked for only at `Spec R`, and `jt_natural` only for morphisms of affine
schemes, so a witness carries no information about a general `T`.  Adding
that information back is exactly `exists_jTransformation_of_affine`.

`R : Type` rather than `R : Type u`: everything in this file lives in
`Scheme.{0}`, and `Spec : CommRingCat.{0}ᵒᵖ ⥤ Scheme.{0}` needs its ring
in `Type 0`. -/
structure IsJSectionOnAffine where
  /-- the `j`-invariant of an elliptic scheme over an affine base -/
  jt : ∀ {R : Type} [CommRing R] (g : Spec (CommRingCat.of R) ⟶ SpecQ),
    Gamma0Datum 1 (Spec (CommRingCat.of R)) → RelPoint jLineStr g
  /-- `j` is natural for base changes between affine bases -/
  jt_natural : ∀ {R' R : Type} [CommRing R'] [CommRing R]
    (h : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {g : Spec (CommRingCat.of R) ⟶ SpecQ} {g' : Spec (CommRingCat.of R') ⟶ SpecQ}
    (hg : h ≫ g = g') {d' : Gamma0Datum 1 (Spec (CommRingCat.of R'))}
    {d : Gamma0Datum 1 (Spec (CommRingCat.of R))},
    IsBaseChangeOf h d' d → jt g' d' = RelPoint.pre h hg (jt g d)
  /-- `j` agrees with `WeierstrassCurve.j` on every Weierstrass model -/
  jt_model : ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic] (d : Gamma0Datum 1 SpecQ),
    IsWeierstrassModel d.ab W → jLineVal (jt (R := ℚ) (𝟙 SpecQ) d) = W.j

/-- **A natural transformation from `[Γ₀(1)]` to the points of the
`j`-line, with NO pinning.**

`IsJSection` minus its `jt_model` field.  Alone it is satisfiable by junk
— the constant section is natural — which is deliberate: it is the target
of the DESCENT leaf, whose content lies entirely in the accompanying
agreement clause, and keeping the pinning out of it is what stops that
leaf from being `exists_jSection` under another name. -/
structure IsJTransformation where
  /-- the transformation -/
  jt : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), Gamma0Datum 1 T → RelPoint jLineStr g
  /-- naturality: a base change of data is sent to the precomposed point -/
  jt_natural : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {d' : Gamma0Datum 1 T'} {d : Gamma0Datum 1 T},
    IsBaseChangeOf h d' d → jt g' d' = RelPoint.pre h hg (jt g d)

/- `exists_gamma0Datum_baseChange` used to be stated HERE a second time, as a
`Scheme.{0}` sorry node.  It is now a DUPLICATE: the declaration is PROVEN
earlier in this file, for arbitrary `Scheme.{u}`, out of `Gamma0BaseChange`.
Its own docstring's "CHECK THAT WOULD REFUTE 'OPEN'" — *any declaration in
this project constructing a `Gamma0Datum` over `T'` out of one over `T`* —
had FIRED, and the two copies were in the same namespace, so keeping both
was a hard "already declared" error rather than merely redundant.  Deleted at
integration 2026-07-27; use the general version above. -/

/-- **Zariski descent for the `j`-invariant: an affine `j`-theory extends
to all bases** (sorry node).

TRUE, and it is descent and nothing else — no elliptic curve enters the
argument, which is the point of cutting here.

THE ARGUMENT.  Let `T` be any `ℚ`-scheme and `d` a `Γ₀(1)`-datum on it.
Choose an affine open cover `T = ⋃ Uᵢ`; by `hbc` restrict `d` to each
`Uᵢ`, giving `dᵢ`, and apply `ja.jt` there to get `uᵢ : Uᵢ ⟶ 𝔸¹_ℚ` over
`ℚ`.  On an overlap `Uᵢ ∩ Uⱼ`, restrict `dᵢ` and `dⱼ` further; both
results are base changes of `d` along the same morphism, hence pullbacks
of the same object, hence carry an `IsBaseChangeOf 𝟙` between them by the
universal property — so `ja.jt_natural` (twice, plus once at `𝟙`) makes
`uᵢ` and `uⱼ` agree there.  `Hom(-, 𝔸¹_ℚ)` is a Zariski sheaf, so the
`uᵢ` glue to a unique `u : T ⟶ 𝔸¹_ℚ`; uniqueness of the gluing gives both
the naturality of `d ↦ u` for arbitrary morphisms of schemes and its
agreement with `ja.jt` when `T` is already affine.

WHAT IS MISSING, precisely: the "two base changes along the same morphism
differ by an `IsBaseChangeOf 𝟙`" step, which is `IsBaseChangeOf.isPullback`
plus `IsPullback.isoIsPullback` — available at this pin, but the transport
of `map_zero`, `map_add` and `liesIn_iff` across that isomorphism has to be
written; and the sheaf gluing itself, for which
`AlgebraicGeometry.Scheme.OpenCover` and the fact that morphisms glue are
the relevant mathlib API.

WHY `hbc` IS A HYPOTHESIS RATHER THAN A CALL.  So that the base-change
leaf is visibly consumed at the assembly site below, and so that this leaf
and `exists_gamma0Datum_baseChange` can be worked on by different owners
without either waiting on the other.

NOT VACUOUS.  See the subsection docstring: `IsJTransformation` alone is
junk-satisfiable, and the agreement clause is what removes that — and
removes it completely, since every scheme has an affine open cover. -/
theorem exists_jTransformation_of_affine (ja : IsJSectionOnAffine)
    (hbc : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) (d : Gamma0Datum 1 T),
      ∃ d' : Gamma0Datum 1 T', Nonempty (IsBaseChangeOf h d' d)) :
    ∃ jtr : IsJTransformation, ∀ {R : Type} [CommRing R]
      (g : Spec (CommRingCat.of R) ⟶ SpecQ) (d : Gamma0Datum 1 (Spec (CommRingCat.of R))),
      jtr.jt g d = ja.jt g d :=
  sorry

/-- **Existence of the `j`-invariant of an elliptic scheme over an affine
base** (sorry node).

TRUE and classical — this is `Y_0(1) ≅ 𝔸¹_j`, Deligne–Rapoport VI, or
Silverman *AEC* III.1 plus descent.  **This leaf carries all of the
elliptic-curve geometry of `exists_jSection`**; what it no longer carries
is the passage to non-affine bases, which is
`exists_jTransformation_of_affine`.

WHAT IT NEEDS.  A Weierstrass presentation of an elliptic scheme
`f : E ⟶ Spec R` after inverting finitely many elements of `R`, so that
`c₄³/Δ` is defined on each piece; equivalently, the line bundle
`ω = f_* Ω¹_{E/T}` and the classical formulas for `c₄, c₆, Δ` as sections
of its powers.  None of that exists at this pin: `AbelianSchemeStruct` is
a functor-of-points presentation with no coordinates anywhere, and
mathlib's `WeierstrassCurve.j` is defined only for a Weierstrass EQUATION
over a ring, not for a scheme.  Searched 2026-07-27 over `Fermat/`,
`.lake/packages/mathlib` and `~/cs/FLT`: mathlib has NO file mentioning
an elliptic scheme at all, `~/cs/FLT` has no `jInvariant`, and the only
`j` anywhere is `WeierstrassCurve.j`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:385`).

THE AXIS THAT VERDICT RANGES OVER, stated so the next reader can see what
it does not cover: presentations of elliptic schemes.  It does NOT cover
the split between the `j`-theory and the existence of models over `ℚ` —
that was the earlier cut, and it produced
`exists_weierstrassModel_gamma0Datum`, now PROVEN.  Nor does it cover the
split between affine and general bases, which is the cut this leaf is the
residue of.

THE CHECK THAT WOULD REFUTE THIS.  Any construction attaching a global
section of `𝒪_T` to an `AbelianSchemeStruct` of relative dimension `1`,
natural in `T`; equivalently, a `grep` for a Weierstrass presentation of
`AbelianSchemeStruct` or for `ω`/`c₄`/`Δ` on a relative curve.

THE FURTHER CUT, when someone attacks this.  Three steps, of which the
middle one is nearly free at this pin, and only the FIRST is now genuinely
missing:

* (i) after inverting finitely many elements of `R`, an elliptic scheme
  over `Spec R` is a Weierstrass model — i.e. `IsWeierstrassModel` holds
  for a base change of the datum to `Spec (Localization.Away a)`.  This
  needs `exists_gamma0Datum_baseChange` to even state, which is why that
  leaf is worth having independently of the descent one.
* (ii) two Weierstrass models of ONE elliptic scheme have the same `j`.
  `WeierstrassCurve.variableChange_j`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean:246`,
  `(C • W).j = W.j`) and `WeierstrassCurve.map_j` (`Weierstrass.lean:470`,
  `(W.map f).j = f W.j`, naturality of `j` under base change) are BOTH
  already in the pin, so what is missing here is only "two models of one
  elliptic scheme differ by a variable change" — and the argument for
  that is written out in the docstring of `IsWeierstrassModel` above.
* (iii) the finitely many local values glue over `Spec R`.  This is
  ordinary commutative algebra — an equalizer over a cover by basic opens
  `D(aᵢ)` with `span {aᵢ} = ⊤` — and is much lighter than the
  scheme-level gluing, which has already been factored out into
  `exists_jTransformation_of_affine`.

Step (ii) is deliberately NOT a separate declaration: nothing else would
consume it, so it would be free-floating.  Whoever proves (i) and (iii)
should write it as a `have` inside this proof.

NOT VACUOUS, and not satisfiable by junk.  Two independent reasons.
First, `jLineVal` is the honest coordinate (see its docstring), so the
value condition has content.  Second — and this is the sharper one — a
`jt` whose value is a CONSTANT section cannot satisfy `jt_model`: pull a
model back along the fibres of any nonisotrivial family and naturality
forces every fibre to take the same value, while `jt_model` demands the
fibre's own `j`.  So `jt` must genuinely vary.  Both reasons survive the
restriction to affine bases, since the pinning field is unchanged and
`SpecQ` is affine. -/
theorem exists_jSectionOnAffine : Nonempty IsJSectionOnAffine :=
  sorry

/-- **Existence of the `j`-invariant of an elliptic scheme** (PROVEN
2026-07-27, over the three-leaf cut of the subsection above; formerly a
sorry node carrying an IRREDUCIBLE verdict).

The proof is the assembly and nothing else, and it is worth reading for
what it does rather than for its length: the descent leaf hands back a
natural transformation over ALL bases together with the promise that it
agrees with the affine one on affine bases, and `SpecQ` is affine — so
instantiating the agreement at `R = ℚ` rewrites the pinning goal into
`IsJSectionOnAffine.jt_model`, which is where the elliptic-curve content
lives.  That step is the whole reason the descent leaf is stated with an
agreement clause and returns an `IsJTransformation` rather than an
`IsJSection`; see the subsection docstring.

The earlier IRREDUCIBLE verdict on this node is RETIRED, for the same
reason the one on `exists_jLine` was: it was not wrong, it was narrow.
It ranged over *presentations of elliptic schemes*, and both axes that
actually split this node — models-over-`ℚ` versus `j`-theory, then affine
versus general base — lay outside it.  The verdict, with that axis now
named explicitly, is preserved verbatim on `exists_jSectionOnAffine`,
which is where it still applies. -/
theorem exists_jSection : Nonempty IsJSection := by
  obtain ⟨ja⟩ := exists_jSectionOnAffine
  obtain ⟨jtr, hagree⟩ :=
    exists_jTransformation_of_affine ja fun h d => exists_gamma0Datum_baseChange h d
  refine ⟨{ jt := jtr.jt, jt_natural := jtr.jt_natural, jt_model := ?_ }⟩
  intro W _ d hd
  rw [hagree (R := ℚ) (𝟙 SpecQ) d]
  exact ja.jt_model W d hd

/-- **Existence of a `Γ₀(N)`-datum over `ℚ` with a prescribed Weierstrass
model** (PROVEN 2026-07-27; formerly a sorry node).

TRUE: take the projective Weierstrass curve of `E`, whose complement of
the point at infinity is `Spec ℚ[E]` by construction, with the subgroup
scheme generated by `g` — which descends to `ℚ` precisely because
`hstable` says the Galois action preserves `⟨g⟩`.  The proof below is
exactly that sentence.

**THE PREVIOUS VERSION OF THIS DOCSTRING WAS STALE AND IS RETRACTED.**
It said that this leaf needs `exists_ellipticScheme_of_weierstrass`'s
ITEM 1 — the grading on a graded quotient ring — and recorded that item
as "in flight and unreleased", i.e. it instructed the reader to WAIT.
Both halves have since landed: `HomogeneousIdeal.quotientGrading` is item
1, `WeierstrassCurve.Projective.proj` is item 2, and
`exists_ellipticScheme_of_weierstrass` has been ASSEMBLED over the five
leaves of `Fermat/FLT/ModularCurve/EllipticScheme.lean`.  So the blocking
construction exists; what this leaf needed beyond it was never ITEM 1 at
all, but the identification of the affine chart, which is now the single
named leaf `exists_affineChart_projModel` in that module.

**Why this is not just `nonempty_gamma0Datum_of_stable`.**  That theorem
consumes `exists_ellipticScheme_of_weierstrass`, whose statement is
existential over the scheme and remembers `E` only through a
Galois-equivariant `≃+` on geometric points — which, as the docstring at
`IsJMapOn.classify_jm` records, is **not** known to determine `E.j`.  So
its datum cannot be shown to satisfy `IsWeierstrassModel`, and using it
here would leave `IsJSection.jt_model` with nothing to fire on.  This
proof instead consumes `exists_ellipticScheme_isWeierstrassModel_of_projModel`,
the same statement with the COORDINATE conjunct retained.  Everything else
— the transport of the order and of the stability of `g` along the `≃+`,
and the appeal to `exists_cyclicSubgroupOfOrder_of_galoisStable` — is
`nonempty_gamma0Datum_of_stable`'s proof verbatim, and the two should be
kept in step.

The hypotheses are load-bearing and are the same three as everywhere else
in this file: without a Galois-stable cyclic subgroup of order `N` there
is no `Γ₀(N)`-structure on `E` over `ℚ` at all, so the statement would be
false.  They are no longer underscore-prefixed, because the proof now
consumes all three: `hN` and `hg` feed the order of the generator and
`hstable` its Galois stability. -/
theorem exists_weierstrassModel_gamma0Datum (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (N : ℕ) (hN : N ≠ 0) (g : (E⁄(AlgebraicClosure ℚ)).Point) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g) :
    ∃ d : Gamma0Datum N SpecQ, IsWeierstrassModel d.ab E := by
  obtain ⟨A, f, ab, hdim, hmodel, e, he⟩ :=
    exists_ellipticScheme_isWeierstrassModel_of_projModel E
  -- The `AddCommGroup` structure on the geometric fibre.  As in
  -- `nonempty_gamma0Datum_of_stable`, this binding is load-bearing: the
  -- `letI`s inside the two `have`s below scope over those statements only.
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  -- The order of the generator transports along the additive equivalence.
  have hord : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
      addOrderOf (e g) = N := by
    rw [AddEquiv.addOrderOf_eq]
    exact hg
  -- So does its Galois stability.
  have hst : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        ab.galSMul (𝟙 SpecQ) σ (e g) ∈ AddSubgroup.zmultiples (e g) := by
    intro σ
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (hstable σ g (AddSubgroup.mem_zmultiples g))
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
    rw [← he σ g, ← hk, map_zsmul]
  obtain ⟨cyc⟩ := exists_cyclicSubgroupOfOrder_of_galoisStable ab N hN (e g) hord hst
  exact ⟨{ E := A, f := f, ab := ab, relativeDimensionOne := hdim, cyc := cyc }, hmodel⟩

/-- **Existence of the `j`-invariant of an elliptic scheme, in the form
`exists_jMap` consumes it** (PROVEN 2026-07-27, over `exists_jSection`
and `exists_weierstrassModel_gamma0Datum`).

The proof is the whole content of the cut and is three lines: the first
two fields of `IsJLine` are the first two fields of `IsJSection`
verbatim, and `jt_weierstrass` is `jt_model` applied to the datum that
`exists_weierstrassModel_gamma0Datum` produces.  `Gamma0Datum.ofDvd`
leaves the elliptic scheme, its structure morphism and its
`AbelianSchemeStruct` untouched, so the model hypothesis transports
across `ofDvd` definitionally and no transport lemma is needed.

INTEGRATION NOTE (2026-07-27).  `Gamma0Datum.ofDvd` acquired
`[Etale (d.cyc.ι ≫ d.f)]` in the falsity repair of `flat_torsionι`, which
landed after this proof was written.  The base here is `SpecQ`, so the
instance is exactly what `CyclicSubgroupOfOrder.etale_of_specQBase`
supplies; the `letI` below is the same discharge `exists_jMap` uses, and
matches the one inside `IsJLine.jt_weierstrass`'s own statement. -/
theorem exists_jLine : Nonempty IsJLine := by
  obtain ⟨js⟩ := exists_jSection
  refine ⟨{ jt := js.jt, jt_natural := js.jt_natural, jt_weierstrass := ?_ }⟩
  intro E _ N hN g hg hstable
  obtain ⟨d, hd⟩ := exists_weierstrassModel_gamma0Datum E N hN g hg hstable
  letI := d.cyc.etale_of_specQBase (𝟙 SpecQ)
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
    hc.universal jLineStr
      (fun g d => haveI := d.cyc.etale_of_specQBase g; jl.jt g (d.ofDvd hN (one_dvd N)))
      (by
        intro _ _ h g g' hg d' d hb
        haveI := d'.cyc.etale_of_specQBase g'
        haveI := d.cyc.etale_of_specQBase g
        exact jl.jt_natural h hg (hb.ofDvd hN (one_dvd N)))
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

/-- **Mazur's Cor. 4.3–4.4 package at `q`, read on points** (interface,
introduced 2026-07-27).

This is the ANATOMY of the formal-immersion argument: the three inputs
Mazur combines, named separately so that each can be recognised, attacked
and refuted on its own instead of hiding inside one opaque leaf.  It is
carried by `exists_eisensteinFormalImmersionAt` and consumed by
`exists_x0JReductionDatum_formalImmersion`, which is PROVEN from it.

* `redE_inj` is **Cor. 4.3**: the Eisenstein quotient `J_e(p)` has
  Mordell–Weil rank `0` (Mazur, *Eisenstein ideal*, §II.7 and III.2), so
  `J_e(p)(ℚ)` is finite, and reduction mod `q` is injective on a finite
  group of points of an abelian variety with good reduction at an ODD
  prime.  The second half is the same formal-group fact this module
  already isolates as `neronKernel_torsionFree`, which is exactly why
  `q ≠ 2` is a hypothesis of the leaf below.
* `formalImmersion` is the **formal immersion at the cusp** in
  characteristic `q ≠ 2`: `X_0(p) → J_e(p)` is a formal immersion at `∞`
  over `𝔽_q`, so two integral points congruent mod `q` to a cusp with the
  same image in `J_e` coincide.  (Mazur proves it at `∞`; the Atkin–Lehner
  involution `w_p` swaps the two cusps of `X_0(p)` for `p` prime, which is
  what lets the field be stated at every cusp of the special fibre.)
* `cusp_lift` is the **rationality and surjectivity of the cusps**: for
  `p` prime the two cusps `0, ∞` of `X_0(p)` are rational and their
  reductions are exactly the cusps of the special fibre.  This is the one
  input of the three that is not deep, and a successor may well be able to
  split it off against `exists_rationalCusps`.

## WHAT IS DELIBERATELY *NOT* HERE

`Eis` and `EisRed` are bare `Type`s and `redE` a bare function: no group
structure, no abelian scheme, no quotient map from `J_0(p)`.  The argument
below uses only injectivity of `redE` and its commutation with
Abel–Jacobi, so carrying the group law would be an unused field — and
every field this structure does not carry makes the EXISTENCE leaf weaker,
which is the direction that leaves the least for a prover to invent.  The
mathematics that produces them (the Eisenstein ideal in the Hecke algebra
acting on `J_0(p)`, and its rank-`0` quotient) is named in the docstrings
and in this comment, not in the type.

## WHY IT IS PARAMETERISED BY `hjr` AND MUST STAY THAT WAY

Same reason as the leaf below, and the same junk witness: `IsX0JReductionAt`
does not pin `redX`, so `formalImmersion` and `cusp_lift` are FALSE if
quantified over an arbitrary datum (see the FORMAL-CONTENT AUDIT above).
Parameterising by `hjr` is harmless because the datum is produced together
with the package, never taken as a hypothesis. -/
structure IsEisensteinFormalImmersionAt {N q : ℕ}
    {Y X Y' X' : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {strY' : Y' ⟶ SpecF q} {strX' : X' ⟶ SpecF q} {jY' : Y' ⟶ X'}
    {hc : IsCoarseModuliY0 N strY}
    {hX : IsCompactificationY0 strY strX}
    {hX' : IsX0Compactification N strX' strY' jY'}
    {hj : IsJMapOn N hc} (hjr : IsX0JReductionAt N q hX hX' hj) where
  /-- the rational points of the Eisenstein quotient, `J_e(N)(ℚ)`, as a
  bare set — only injectivity of reduction on it is ever used -/
  Eis : Type
  /-- the points of its reduction, `J_e(N)(𝔽_q)` -/
  EisRed : Type
  /-- `x ↦` the class of `[x] − [∞]` in `J_e(N)(ℚ)` -/
  ajE : RelPoint strX (𝟙 SpecQ) → Eis
  /-- the same map on the special fibre -/
  ajE' : RelPoint strX' (𝟙 (SpecF q)) → EisRed
  /-- reduction mod `q` on the Eisenstein quotient -/
  redE : Eis → EisRed
  /-- Abel–Jacobi into `J_e` commutes with reduction, i.e. the quotient map
  is defined over `ℤ_(q)` -/
  red_ajE : ∀ x : RelPoint strX (𝟙 SpecQ), redE (ajE x) = ajE' (hjr.redX x)
  /-- **Mazur Cor. 4.3**: `J_e(N)(ℚ)` is finite (rank `0`) and `q` is odd,
  so reduction is injective on it -/
  redE_inj : Function.Injective redE
  /-- **the formal immersion at the cusps**, in characteristic `q ≠ 2`:
  two rational points with the same CUSPIDAL reduction and the same image
  in `J_e(N)(ℚ)` are equal -/
  formalImmersion : ∀ x z : RelPoint strX (𝟙 SpecQ), hX'.IsCusp (hjr.redX x) →
      hjr.redX x = hjr.redX z → ajE x = ajE z → x = z
  /-- **the cusps of the special fibre are reductions of rational cusps**:
  for `N` prime the two cusps of `X_0(N)` are rational and reduction is
  onto the cusps of the special fibre -/
  cusp_lift : ∀ x : RelPoint strX (𝟙 SpecQ), hX'.IsCusp (hjr.redX x) →
      ∃ c : RelPoint strX (𝟙 SpecQ), hX.IsCusp c ∧ hjr.redX c = hjr.redX x

/-- **Mazur's Cor. 4.3–4.4, PACKAGED WITH THE DATUM IT IS ABOUT** (sorry
node, introduced 2026-07-27): for a prime `p ∉ mazurIsogenyPrimes` and a
prime `q ∉ {2, p}` there is a good-reduction datum for `(X_0(p), j)` at `q`
carrying the Eisenstein/formal-immersion package above.

TRUE — Mazur, *Rational isogenies of prime degree*, Invent. Math. 44 (1978),
Cor. 4.3–4.4, over *Modular curves and the Eisenstein ideal*, Publ. Math.
IHÉS 47 (1977).  See `IsEisensteinFormalImmersionAt` for the anatomy: the
three fields are the rank-`0`/injectivity half, the formal-immersion half,
and the cusp bookkeeping, and a prover should expect to supply them
separately even though they are produced together.

**`p ∉ mazurIsogenyPrimes` with `p` prime already gives `19 < p`** — every
prime `≤ 19` lies in the list — which is exactly the hypothesis `p ≥ 23`
that the formal-immersion half needs.  No separate bound is added.

**The datum is bundled into the existential and MUST STAY THAT WAY**; the
reason is spelled out on `exists_x0JReductionDatum_formalImmersion` below,
and it is the FORMAL-CONTENT AUDIT's junk witness for `redX`.

Consequently this leaf is strictly STRONGER than `exists_x0JReductionAt` at
the same `q` — it produces the same datum and more.

IRREDUCIBLE at this pin: `J_0(p)`, the Hecke algebra, the Eisenstein ideal
and reduction of an abelian variety are all missing.  **The check that
would refute that**: a declaration in the tree producing an abelian-variety
quotient of `J_0(p)` of rank `0`.  Note that the reduction-injectivity
input alone is NOT missing — `neronReduction_injective` (PROVEN here, over
the single formal-group leaf `neronKernel_torsionFree`) is exactly it, so a
prover who gets as far as building `J_e(p)` as an abelian scheme over
`ℤ_(q)` can discharge `redE_inj` from material already in this file. -/
theorem exists_eisensteinFormalImmersionAt {p q : ℕ} (_hp : p.Prime)
    (_hmem : p ∉ mazurIsogenyPrimes) (_hq : q.Prime) (_hq2 : q ≠ 2) (_hqp : q ≠ p)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {hc : IsCoarseModuliY0 p strY} (hX : IsCompactificationY0 strY strX)
    (hj : IsJMapOn p hc) :
    ∃ (Y' X' : Scheme.{0}) (strY' : Y' ⟶ SpecF q) (strX' : X' ⟶ SpecF q) (jY' : Y' ⟶ X')
      (hX' : IsX0Compactification p strX' strY' jY') (hjr : IsX0JReductionAt p q hX hX' hj),
      Nonempty (IsEisensteinFormalImmersionAt hjr) :=
  sorry

/-- **Mazur's formal-immersion criterion at `q`, PACKAGED WITH THE DATUM IT
IS ABOUT** (PROVEN 2026-07-27 over `exists_eisensteinFormalImmersionAt`):
for a prime `p ∉ mazurIsogenyPrimes` and a prime `q ∉ {2, p}` there is a
good-reduction datum for `(X_0(p), j)` at `q` whose reduction map detects
cusps — a rational point of `X_0(p)` whose reduction mod `q` is a cusp of
the special fibre is itself a cusp.

TRUE — Mazur, *Rational isogenies of prime degree*, Invent. Math. 44 (1978),
Cor. 4.3–4.4, over *Modular curves and the Eisenstein ideal*, Publ. Math.
IHÉS 47 (1977): the Eisenstein quotient `J_e(p)` has Mordell–Weil rank `0`,
so `J_e(p)(ℚ)` is finite and reduction mod `q` is injective on it for
`q ≠ 2`; and `X_0(p) → J_e(p)` is a formal immersion at the cusp `∞` in
characteristic `q ≠ 2`.  Together those say that a rational point congruent
to a cusp mod `q` *is* that cusp.

## THE CUT (2026-07-27): THE MECHANISM IS PROVEN, THE OBJECTS ARE THE LEAF

The bare `sorry` is gone.  The three inputs of Mazur's argument are named as
the fields of `IsEisensteinFormalImmersionAt` above and produced by the
single leaf `exists_eisensteinFormalImmersionAt`; the four lines below are
the argument itself, and they are the whole of Cor. 4.4 given Cor. 4.3:

1. the reduction of `z` is a cusp, so by `cusp_lift` some RATIONAL cusp `c`
   has the same reduction;
2. `redE (ajE z) = ajE' (redX z) = ajE' (redX c) = redE (ajE c)` by
   `red_ajE`, so `ajE z = ajE c` by `redE_inj` — this is the step that
   consumes rank `0` and `q ≠ 2`;
3. `formalImmersion` then gives `z = c`, and `c` is a cusp.

What this buys is that the surviving leaf mentions the Eisenstein quotient,
the formal immersion and the cusps SEPARATELY, so a partial advance on any
one of them is visible.  What it does not buy is a smaller total: the leaf
is still Mazur's theorem, and the count is unchanged.

**`p ∉ mazurIsogenyPrimes` with `p` prime already gives `19 < p`** — every
prime `≤ 19` lies in the list — which is exactly the hypothesis
`p ≥ 23` that the formal-immersion half needs.  No separate bound is added.

## WHY THE DATUM IS BUNDLED INTO THE EXISTENTIAL, AND MUST STAY THAT WAY

The natural-looking statement takes `hjr : IsX0JReductionAt p q hX hX' hj`
as a HYPOTHESIS and concludes `hX'.IsCusp (hjr.redX z) → hX.IsCusp z`.  That
statement is **FALSE**, and the FORMAL-CONTENT AUDIT on `IsX0JReductionAt`
above gives the counterexample: `redX` is pinned by nothing, so sending every
rational point to a cusp of the special fibre makes `red_jm`'s hypothesis
unsatisfiable and therefore satisfies the structure vacuously — whereupon the
hypothesis of that implication holds for EVERY `z` while its conclusion fails
for every `z` coming from `Y`.

Quantifying the datum EXISTENTIALLY, as here, is what the audit prescribes
("the formal-immersion leaf must be stated against a datum produced by
`exists_x0JReductionAt`, never against an arbitrary one") and is immune to
that witness: it asks for SOME datum with the property, and the junk witness
is simply not that one.  **Do not refactor this into a hypothesis on `hjr`**;
that is the one edit that silently turns this leaf false.

Consequently this leaf is strictly STRONGER than `exists_x0JReductionAt` at
the same `q` — it produces the same datum and more — and a prover should
expect to discharge both together.

**STALE-NOTE CORRECTION, SECOND ROUND (2026-07-27).**  Two earlier versions
of this paragraph said the remedy was "in flight on branch `flt-lean-12`",
then that it "has LANDED as `IsX0NeronDatum`, so re-founding
`IsX0JReductionAt` on it is available work TODAY".  Both are now out of
date, and in opposite directions:

* **The pinning has landed, and in a better shape than either note
  predicted.**  It is not a re-founding of `IsX0JReductionAt` at all —
  which would have edited a concurrently-owned structure — but a SEPARATE
  pinned datum, `IsX0JNeronDatum`, in the integral-model subsection below.
  There `redX` and `jm'` are induced by morphisms of models over `ℤ_(q)`,
  `red_jm` is a **THEOREM** (`IsX0JNeronDatum.red_jm`) rather than a field,
  `IsX0JNeronDatum.toJReduction` produces an `IsX0JReductionAt`, and
  `exists_x0JReductionAt` is consequently **PROVEN** from
  `exists_x0JNeronDatum`.  So the junk witness for `redX` is dead for every
  datum that arrives through that route.
* **The split of THIS leaf is nevertheless still blocked, for a completely
  different reason: DECLARATION ORDER.**  `IsX0JNeronDatum` consumes
  `SpecLoc` and therefore cannot be declared before the integral-model
  subsection, which sits some two thousand lines BELOW this point.  A leaf
  stated over an arbitrary `IsX0JNeronDatum` — which is what the split
  needs, and what would finally let the implication be stated against a
  datum taken as a hypothesis — cannot be written here.

**Why relocation is not a local fix, measured rather than guessed.**  This
leaf's consumer chain is `exists_x0JReductionDatum_formalImmersion` →
`cuspidal_x0_prime` → `y0HasNoRationalPoint_prime`, and the last of those
is consumed further up this very section by `cuspidal_x0_isogenyPrimeSq`
and by the semiprime nodes.  So moving the split below the integral-model
subsection drags essentially the whole tail of the prime-levels section
with it — in a file with several concurrent owners, and one that has
already taken one relocation of this exact section.  The cost is an
integration conflict, not a proof.

**The check that would refute this, and it is one grep**: a declaration of
`SpecLoc` (or of `IsX0JNeronDatum`) ABOVE this point, or any consumer-free
route from `y0HasNoRationalPoint_prime` to the prime-square and semiprime
nodes.  If either appears, the split becomes a local edit and should be
done: state `exists_eisensteinQuotient_of_x0JNeronDatum` (the DEEP half —
Eisenstein quotient, `redE_inj`, `formalImmersion`) and
`cuspLift_of_x0JNeronDatum` (the SHALLOW half, attackable against
`exists_rationalCusps`) over an arbitrary `IsX0JNeronDatum`, and prove
`exists_eisensteinFormalImmersionAt` from those two plus
`exists_x0JNeronDatum` — which also deletes this leaf's duplication of the
integral-model existence, since it would then share it with
`exists_x0JReductionAt`.

**Do not attempt the split by weakening the pin instead.**  Neither
`formalImmersion` nor `cusp_lift` is true over an unpinned
`IsX0JReductionAt`, and the witnesses are explicit.  For `formalImmersion`:
`red_ajE` forces `redE = ajE' ∘ redX` on the image of `ajE`, so `redE_inj`
forces `redX` injective, and a junk `redX` collapsing two rational points
makes the structure unsatisfiable rather than vacuous.  For `cusp_lift`:
take a junk `redX` that is injective and sends exactly one NON-cusp to a
cusp of the special fibre, and no rational cusp `c` has `redX c = redX x`.
That is why the bundled form above is the correct statement today. -/
theorem exists_x0JReductionDatum_formalImmersion {p q : ℕ} (hp : p.Prime)
    (hmem : p ∉ mazurIsogenyPrimes) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    {hc : IsCoarseModuliY0 p strY} (hX : IsCompactificationY0 strY strX)
    (hj : IsJMapOn p hc) :
    ∃ (Y' X' : Scheme.{0}) (strY' : Y' ⟶ SpecF q) (strX' : X' ⟶ SpecF q) (jY' : Y' ⟶ X')
      (hX' : IsX0Compactification p strX' strY' jY') (hjr : IsX0JReductionAt p q hX hX' hj),
      ∀ z : RelPoint strX (𝟙 SpecQ), hX'.IsCusp (hjr.redX z) → hX.IsCusp z := by
  obtain ⟨Y', X', strY', strX', jY', hX', hjr, ⟨d⟩⟩ :=
    exists_eisensteinFormalImmersionAt hp hmem hq hq2 hqp hX hj
  refine ⟨Y', X', strY', strX', jY', hX', hjr, fun z hz => ?_⟩
  -- the reduction of `z` is a cusp of the special fibre, so it is the
  -- reduction of a RATIONAL cusp `c`
  obtain ⟨c, hcusp, hcz⟩ := d.cusp_lift z hz
  -- `z` and `c` have the same image in `J_e(p)(ℚ)`: their images agree
  -- after reduction, and reduction is injective there (rank `0`, `q ≠ 2`)
  have hE : d.ajE z = d.ajE c :=
    d.redE_inj (by rw [d.red_ajE, d.red_ajE, hcz])
  -- the formal immersion at the cusp then identifies them
  rw [d.formalImmersion z c hz hcz.symm hE]
  exact hcusp

/-- **Every `ℚ̄`-point of the coarse space is classified by a `Γ₀(p)`-datum
over `ℚ̄`** (sorry node, introduced 2026-07-27): the geometric half of
`exists_gamma0Datum_classify_eq` below.

TRUE, and **this is the one non-vacuous statement in the cluster** — that
is the whole reason the cut is here.  Over an algebraically closed field
the field of moduli is trivially a field of definition, so a `ℚ̄`-point of
the coarse space is literally a `ℚ̄`-isomorphism class of pairs `(E, C)`
and any representative is the datum asked for.  No membership hypothesis
appears, and none is needed: `j = 0` and `j = 1728` are harmless here
because there is no descent to obstruct.

## THIS IS THE CLAUSE `IsCoarseModuliY0` DELIBERATELY OMITS

Its own docstring says so: "the bijectivity on geometric points — the
second half of the usual definition — deliberately omitted".  So this leaf
is not mathematics awaiting a prover; it is the missing half of a
DEFINITION, and it closes in one of two ways:

1. the `IsCoarseModuliY0` owner adds the geometric-points clause (or
   `Gamma0Atlas` gains it, since `Gamma0Atlas.toIsCoarseModuliY0` is where
   `IsCoarseModuliY0`s come from), whereupon this leaf is that field; or
2. it is cited directly from Katz–Mazur (8.1.1)/Mumford *GIT* Ch. 0 §2,
   which is what the omitted clause states.

**The check that would refute the diagnosis**: any field of
`IsCoarseModuliY0` or of `Gamma0Atlas` relating points of `Y` back to
data.  RUN 2026-07-27 — `IsCoarseModuliY0` has `classify`,
`classify_natural`, `universal`; `Gamma0Atlas` adds `cover` and
`quotient`, and both run FROM data TO `Y`, never back.  See the extended
note on `exists_gamma0Datum_classify_eq` below. -/
theorem exists_gamma0Datum_geomClassify {p : ℕ} (_hp : p.Prime)
    {Y : Scheme.{0}} {strY : Y ⟶ SpecQ} (hc : IsCoarseModuliY0 p strY)
    (y : RelPoint strY (specAlgClos ℚ ≫ 𝟙 SpecQ)) :
    ∃ d : Gamma0Datum p (Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      hc.classify (specAlgClos ℚ ≫ 𝟙 SpecQ) d = y :=
  sorry

/-- **A `Γ₀(p)`-datum over `ℚ̄` whose moduli point is defined over `ℚ`
descends to `ℚ`** (sorry node, introduced 2026-07-27): the field-of-moduli
half of `exists_gamma0Datum_classify_eq` below, and **the only place
`hmem` does any work.**

TRUE.  The hypothesis `hd'` says exactly that the `ℚ̄`-class of `d'` is the
base change of a RATIONAL point, i.e. that the class is Galois-stable and
its field of moduli is `ℚ`.  When `Aut(E, C) = {±1}` — i.e. `j ≠ 0, 1728` —
the field of moduli is a field of definition, so the class contains a pair
defined over `ℚ`; that pair is a `Gamma0Datum p SpecQ`, and it classifies
to a rational point whose base change is `hc.classify _ d'`, hence to `y`
itself because `Y(ℚ) → Y(ℚ̄)` is injective.

`hmem` is what excludes `j = 0, 1728`: there the automorphism group of the
pair is larger than `{±1}` and the descent obstruction lives in `Br(ℚ)[n]`,
which does not vanish.  With `p ∉ mazurIsogenyPrimes` those values do not
arise — a curve with CM by `ℤ[ζ₃]` or `ℤ[i]` has a rational `p`-isogeny
only for `p` in the list.  **Do not drop it**, and do not "generalise" this
leaf by removing it.

**Quadratic twists are not an obstruction.**  Descent produces the pair
only up to quadratic twist; a twist changes neither `j` nor the
Galois-stability of `C`, and maps to the SAME point of the coarse space,
which is all that is asked.

**VACUITY, inherited.**  By Mazur's theorem `Y_0(p)(ℚ) = ∅` for these `p`,
so `y` cannot exist and this half is vacuous — unlike
`exists_gamma0Datum_geomClassify`, which is not.  Separating the two is the
point of the cut: the vacuity is now confined to the half that carries
`hmem`, and the geometric half is a statement that can be tested against
examples.

IRREDUCIBLE at this pin: there is no descent or twisting API in `Fermat/`,
in the mathlib pin, or in `~/cs/FLT` (`grep -rni 'fieldOfModuli|field of
moduli|quadraticTwist'`, run 2026-07-27, finds only prose in this file). -/
theorem exists_gamma0Datum_descent {p : ℕ} (_hp : p.Prime)
    (_hmem : p ∉ mazurIsogenyPrimes)
    {Y : Scheme.{0}} {strY : Y ⟶ SpecQ} (hc : IsCoarseModuliY0 p strY)
    (y : RelPoint strY (𝟙 SpecQ))
    (d' : Gamma0Datum p (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
    (_hd' : hc.classify (specAlgClos ℚ ≫ 𝟙 SpecQ) d'
      = RelPoint.pre (specAlgClos ℚ) rfl y) :
    ∃ d : Gamma0Datum p SpecQ, hc.classify (𝟙 SpecQ) d = y :=
  sorry

/-- **Every rational point of the coarse space is classified by a
`Γ₀(p)`-datum over `ℚ` itself** (PROVEN 2026-07-27 over
`exists_gamma0Datum_geomClassify` and `exists_gamma0Datum_descent`; a
sorry node from 2026-07-27 until then): for a
prime `p ∉ mazurIsogenyPrimes` the map `hc.classify (𝟙 SpecQ)` is
surjective on rational points.

TRUE, and this is the **field-of-moduli half** of
`exists_weierstrass_jm_of_relPointY0` below, isolated from it.  A rational
point of the coarse space is a `ℚ̄`-isomorphism class of pairs `(E, C)`
fixed by `Gal(ℚ̄/ℚ)`; the field of moduli of such a class is `ℚ`, and when
`Aut(E, C) = {±1}` — i.e. `j ≠ 0, 1728` — the field of moduli is a field of
definition, so the class contains a pair defined over `ℚ`.  That pair is a
`Gamma0Datum p SpecQ`, and it classifies the point we started from.

## WHY `hmem` IS HERE AND NOT ON THE SIBLING

`hmem` is doing exactly one job, and it is this leaf's job: at `j = 0` and
`j = 1728` the automorphism group of the pair is larger than `{±1}` and the
descent obstruction lives in `Br(ℚ)[n]`, which does not vanish.  With
`p ∉ mazurIsogenyPrimes` those values do not arise — a curve with CM by
`ℤ[ζ₃]` or `ℤ[i]` has a rational `p`-isogeny only for `p` in the list — so
the hypothesis buys the descent honestly rather than by assumption.  The
sibling `exists_weierstrass_jm_of_gamma0Datum` does not need it for descent
and carries it only to state the same vacuity.

**Quadratic twists are not an obstruction here.**  Descent produces the
pair only up to quadratic twist, and a twist changes neither `j` nor the
Galois-stability of `C`; and it maps to the SAME point of the coarse space,
which is all this statement asks for.  So the twist ambiguity is invisible
to this leaf — that is the point of stating it as a bare surjectivity.

**VACUITY, inherited.**  By Mazur's theorem `Y_0(p)(ℚ) = ∅` for these `p`,
so `y` cannot exist and the leaf is vacuously true.  That is inherent to
the whole node (see `exists_weierstrass_jm_of_relPointY0`), not introduced
by this cut; a prover must not "prove" it by an argument that quietly
assumes the conclusion of `cuspidal_x0_prime`.  The non-vacuous statement
it specialises is the surjectivity for `p` prime, `p ≥ 5` and
`j ≠ 0, 1728`, which is where a proof should start.

IRREDUCIBLE at this pin: it needs the `ℚ̄`-points of `Y_0(p)` identified
with `ℚ̄`-isomorphism classes of pairs, and the field-of-moduli/twisting
theory, neither of which exists here.  **The check that would refute
that**: a declaration in the tree giving a surjection onto
`RelPoint strY (𝟙 SpecQ)` from data over `ℚ`, or any statement of
`IsCoarseModuliY0` beyond the categorical-quotient clause it already
carries.

## THAT CHECK WAS RUN 2026-07-27 AND CAME BACK NEGATIVE

Recorded so the next owner does not repeat the survey.

* `IsCoarseModuliY0` has exactly three fields — `classify`,
  `classify_natural`, `universal` — and its own docstring says the
  bijectivity on geometric points is "deliberately omitted".  So the
  structure carries initiality and nothing else, and **initiality cannot
  give surjectivity on rational points**: it determines `(Y, classify)`
  up to unique isomorphism, which transports rational points between
  models but never produces a datum for one.
* `Gamma0Atlas` — the only richer presentation, and the source of
  `IsCoarseModuliY0` via `Gamma0Atlas.toIsCoarseModuliY0` — does not help
  either, and the direction is the point.  `cover` runs FROM a datum TO a
  map `T' ⟶ M`; it never runs from a point of `Y` back to a datum.
  `quotient` is a factorisation property of `(classify strM dM).1`, i.e.
  it makes that morphism an epimorphism among invariant maps — and an
  epimorphism of schemes need not be surjective on `ℚ`-points.  That gap
  IS the field-of-moduli obstruction, restated categorically.
* `grep -rn 'IsGamma0DatumOf|fieldOfModuli|field of moduli' Fermat/`
  finds only prose in this file; there is no descent or twisting API
  anywhere in `Fermat/`, in the mathlib pin, or in `~/cs/FLT`.

So the missing ingredient is a single, nameable thing: **a geometric-points
clause on `IsCoarseModuliY0`** (the omitted half of the usual coarse-space
definition), plus the field-of-moduli descent that turns a Galois-stable
`ℚ̄`-class into a `ℚ`-rational datum.  The first is a structure field owned
elsewhere; only the second is mathematics for this leaf.  Note the sibling
`exists_weierstrass_jm_of_gamma0Datum` is blocked in exactly the same
shape — on a missing field of `IsJMapOn` — which is why neither leaf is a
prover's task until a structure owner moves.

## THE CUT (2026-07-27): THE OMITTED CLAUSE AND THE DESCENT ARE NOW TWO LEAVES

The survey above found the blockage to be two things of very different
kinds glued together, so they are now two leaves and the two lines below
are the whole assembly:

* `exists_gamma0Datum_geomClassify` — surjectivity of `classify` on
  `ℚ̄`-points.  This is the **omitted half of the definition** of a coarse
  moduli space, not mathematics: it closes either as a new field of
  `IsCoarseModuliY0`/`Gamma0Atlas` or as a direct Katz–Mazur citation.  It
  carries **no** membership hypothesis and, crucially, **it is NOT
  vacuous** — `Y_0(p)(ℚ̄)` is large for every `p`.
* `exists_gamma0Datum_descent` — the field-of-moduli/twisting descent from
  `ℚ̄` to `ℚ`.  **`hmem` is consumed there and nowhere else**, which is
  right: `hmem` exists to exclude `j = 0, 1728`, and that exclusion is
  needed only where descent happens.

What the cut buys is that the whole cluster's vacuity is now confined to
the descent half.  Before it, the only leaf on this branch was vacuous, so
no statement here could be checked against an example and a prover had
nothing to grip; the geometric half is a genuine, testable statement whose
closure does not wait on Mazur.  What it does not buy is a smaller total:
the sum is still this statement. -/
theorem exists_gamma0Datum_classify_eq {p : ℕ} (hp : p.Prime)
    (hmem : p ∉ mazurIsogenyPrimes)
    {Y : Scheme.{0}} {strY : Y ⟶ SpecQ} (hc : IsCoarseModuliY0 p strY)
    (y : RelPoint strY (𝟙 SpecQ)) :
    ∃ d : Gamma0Datum p SpecQ, hc.classify (𝟙 SpecQ) d = y := by
  -- the base change of `y` to `ℚ̄` is classified by a datum over `ℚ̄`
  obtain ⟨d', hd'⟩ :=
    exists_gamma0Datum_geomClassify hp hc (RelPoint.pre (specAlgClos ℚ) rfl y)
  -- and that datum descends, because `hmem` excludes `j = 0, 1728`
  exact exists_gamma0Datum_descent hp hmem hc y d' hd'

/-- **A `Γ₀(p)`-datum over `ℚ` is a Weierstrass curve with a stable cyclic
subgroup, and `jm` reads its `j`-invariant** (sorry node, introduced
2026-07-27).

This is the **`jm`-pinning half** of `exists_weierstrass_jm_of_relPointY0`,
isolated from the descent.  It is the converse of
`nonempty_gamma0Datum_of_stable`, which is the only direction this module
has had, together with the assertion that `hj.jm` takes the expected value
at the classifying point.

## THE WHOLE DIFFICULTY IS THE LAST CONJUNCT, AND IT IS A GAP IN `IsJMapOn`

Turning the datum into a Weierstrass curve is the ordinary Weierstrass
bridge: an elliptic scheme over `Spec ℚ` has a Weierstrass model, and the
cyclic subgroup scheme of order `p` gives a `ℚ̄`-point `g` of order `p`
whose `zmultiples` are Galois-stable.  That half is bookkeeping.

The conjunct `hj.jm (hc.classify (𝟙 SpecQ) d) = E.j` is not.  `IsJMapOn`
pins `jm` **only** through `classify_jm`, which is an EXISTENCE statement —
"for every `(E, g)` there is SOME `d` with `jm (hc.classify _ d) = E.j`" —
and deliberately not the equation `jm (hc.classify _ d) = E.j` for a GIVEN
`d`.  So going from a given `d` to a curve realising `jm` at that specific
point is not available from the structure, and this leaf is where that gap
now lives, by name.

## THE RECOMMENDED NON-VACUOUS TARGET IS FALSE — REFUTED 2026-07-27

The 2026-07-27 cut closed by saying "the non-vacuous statement to aim at
is the same one with `p ≥ 5`, `j ≠ 0, 1728` and no membership hypothesis".
**That statement is FALSE**, and the witness is explicit, so nobody should
spend a cycle on it.

Take `N = 5`, let `hc` be a genuine coarse moduli structure, and let
`S := {E.j | E/ℚ elliptic carrying a Galois-stable cyclic subgroup of
order 5}`.  Then `S ⊊ ℚ` — a generic `j` admits no rational `5`-isogeny —
while `S` and the image of `hc.classify (𝟙 SpecQ)` are both countably
infinite.  Pick `d₀` and set `y₀ := hc.classify (𝟙 SpecQ) d₀`; pick
`v ∉ S`; and define

    jm y₀ := v,    jm ↾ (image of classify \ {y₀}) := any surjection onto S.

`IsJMapOn 5 hc` has exactly **two** fields, `jm` and `classify_jm`, so
this `jm` is a legitimate `IsJMapOn`: every `E.j` lies in `S` and is
therefore attained at some classified point other than `y₀`, which is all
`classify_jm` asks.  But at `d₀` the conclusion demands a curve with
`j = v ∉ S` carrying a Galois-stable cyclic subgroup of order `5`, and
`v ∉ S` denies exactly that.

So `classify_jm`'s existential does not merely fail to PROVE the
membership-free statement; it fails to make it TRUE.  **This leaf is true
only through its vacuity.**  That does not license an `exfalso`
discharge — the unsatisfiability is knowable only through the chain this
leaf belongs to — but it does mean the "start from the non-vacuous
version" advice is unusable here.

## THE REPAIR IS A FIELD ON `IsJMapOn`, AND THE OBVIOUS FIELD IS UNSAFE

The repair is still a field pinning `jm` at a classifying point given in
advance, roughly `jm_classify : ∀ (E) [E.IsElliptic] (g) …
(d : Gamma0Datum N SpecQ), IsGamma0DatumOf d E g → jm (hc.classify _ d) =
E.j`.  **But `IsGamma0DatumOf` cannot be the "is a model of" relation this
tree has**, and the reason is already on record — in the `IsJMapOn`
subsection docstring above, the paragraph beginning "What pins `jm`, and
why the pinning is an EXISTENCE statement".  The only such relation
available is the Galois-equivariant `≃+` of geometric-fibre point groups
produced by `exists_ellipticScheme_of_weierstrass`, and it is not known to
determine `E` up to isomorphism: it determines the Tate modules, hence by
Faltings only the ISOGENY class, and isogenous curves have different `j`
in general.  Two curves with different `j` sharing a datum would make that
field UNSATISFIABLE and `exists_jMap` FALSE, silently.

The two docstrings read as contradictory — one prescribes the field, the
other forbids it — and they are not.  This is the reconciliation: **the
field is the right repair, and the relation it quantifies over is the
missing ingredient.**

**What the safe relation is, and the mechanical obstruction to writing it
HERE.**  A SCHEME-level identification of `d.E` with the projective
Weierstrass model of `E` over `Spec ℚ`, compatible with the group law and
carrying `d.cyc` onto `⟨g⟩`, does determine `E.j`.  That model exists and
is concrete — `proj` and `projToSpec` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveModel.lean`,
consumed by `exists_ellipticScheme_of_projModel` — but it is **not
nameable in this file**.  `X0.lean` takes a deliberately NON-public
`import Fermat.FLT.ModularCurve.EllipticScheme` (line 307) because a
`public import` propagates the reserved token `over` through the whole
`MazurTorsion` cone; see `EllipticScheme.lean`'s module docstring, which
says in as many words that its statement "is existential over the scheme
… that is what makes a proof-body-only use in `X0.lean`, and hence the
non-public import, sufficient".

So the repair is a two-step job, each step with a different owner:

1. in `EllipticScheme.lean` (or `ProjectiveModel.lean`), record the
   scheme-level model relation that `exists_ellipticScheme_of_projModel`
   already CONSTRUCTS and currently discards — strengthen its conclusion,
   or state an `IsEllipticSchemeModelOf` relation there where `proj` is
   nameable;
2. add `jm_classify` to `IsJMapOn` against THAT relation, whereupon this
   leaf's last conjunct becomes free and only the Weierstrass bridge
   survives.

**The check that would refute step 1's premise**: a scheme-level
identification already present in `exists_ellipticScheme_of_projModel`'s
conclusion.  RUN 2026-07-27 — the conclusion is
`∃ (A : Scheme.{0}) (f : A ⟶ SpecQ) (ab : AbelianSchemeStruct f),
SmoothOfRelativeDimension 1 f ∧ (∃ e : (E⁄ℚ̄).Point ≃+ GeomFibrePt f (𝟙
SpecQ), <Galois equivariance>)`: a point-group equivalence and nothing
more.

**The Weierstrass bridge half is also unbuilt**, and that is worth saying
plainly since the paragraph above calls it bookkeeping: the tree has only
the FORWARD bridge `exists_ellipticScheme_of_weierstrass`.  `grep -rn
'WeierstrassCurve' Fermat/FLT/Modularity/AbelianScheme.lean
Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean` returns nothing, and
there is no declaration anywhere in `Fermat/` producing a
`WeierstrassCurve ℚ` from an `AbelianSchemeStruct`.  Checked 2026-07-27.

**VACUITY, inherited and now sharper.**  `Gamma0Datum p SpecQ` is itself
empty for `p ∉ mazurIsogenyPrimes` — that is Mazur's theorem again — so
this leaf is vacuously true, exactly like its parent.  Note the vacuity is
NOT visible from the type: `Gamma0Datum p SpecQ` is a perfectly ordinary
structure, and its emptiness is the deep theorem. -/
theorem exists_weierstrass_jm_of_gamma0Datum {p : ℕ} (_hp : p.Prime)
    (_hmem : p ∉ mazurIsogenyPrimes)
    {Y : Scheme.{0}} {strY : Y ⟶ SpecQ} {hc : IsCoarseModuliY0 p strY}
    (hj : IsJMapOn p hc) (d : Gamma0Datum p SpecQ) :
    ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic) (g : (E⁄(AlgebraicClosure ℚ)).Point),
      addOrderOf g = p ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) ∧
      hj.jm (hc.classify (𝟙 SpecQ) d) = E.j :=
  sorry

/-- **The coarse-to-fine descent on `Y_0(p)`** (PROVEN 2026-07-27 over
`exists_gamma0Datum_classify_eq` and `exists_weierstrass_jm_of_gamma0Datum`;
a sorry node from 2026-07-27 until then): a rational point of the COARSE
space `Y_0(p)` for a prime
`p ∉ mazurIsogenyPrimes` is represented by a Weierstrass curve over `ℚ`
carrying a Galois-stable cyclic subgroup of order `p`, whose `j`-invariant
is the value of the `j`-map at the point.

TRUE.  This is the converse direction of `nonempty_gamma0Datum_of_stable`,
which is the only direction this module has had: a rational point of `Y_0(p)`
is a `ℚ̄`-isomorphism class of pairs `(E, C)` fixed by `Gal(ℚ̄/ℚ)`, and for
`Aut(E, C) = {±1}` — i.e. `j ≠ 0, 1728` — the field of moduli is a field of
definition, so the pair descends to `ℚ` up to quadratic twist and a twist
changes neither `j` nor the Galois-stability of `C`.

## THE CUT (2026-07-27): THE TWO GAPS ARE NOW TWO LEAVES

The docstring below used to list two distinct gaps and note that they are
independent.  They are now two named leaves, and the three lines of proof
are the whole of the assembly:

* **the CM values / field of moduli** — `exists_gamma0Datum_classify_eq`.
  At `j = 0` and `j = 1728` the automorphism group of the pair can be
  larger than `{±1}` and descent from the field of moduli is not automatic;
  the obstruction lives in `Br(ℚ)[n]`, which does not vanish.  With
  `p ∉ mazurIsogenyPrimes` those values do not arise (a curve with CM by
  `ℤ[ζ₃]` or `ℤ[i]` has a rational `p`-isogeny only for `p` in the list),
  so the hypothesis buys the descent honestly rather than by assumption.
  **`hmem` is consumed there and nowhere else.**
* **`jm` at an unclassified point** —
  `exists_weierstrass_jm_of_gamma0Datum`.  `IsJMapOn` pins `jm` only
  through `classify_jm`, which is an EXISTENCE statement about points
  classifying a curve — see the subsection docstring for why it
  deliberately is not the equation `jm (hc.classify d) = E.j`.  So `jm y`
  for a general `y` is unconstrained by the structure, and the final
  conjunct `hj.jm y = E.j` is the one clause here that needs `jm` to be the
  genuine `j`-map rather than merely an `IsJMapOn`.  **This is a gap in
  `IsJMapOn`, not in this leaf**, and the repair — a field pinning `jm` at
  a classifying point given in advance — is owned elsewhere.  The cut makes
  that gap a NAMED leaf, so the `IsJMapOn` owner can see it.

What the cut buys is that a repair to `IsJMapOn` collapses the second leaf
to the Weierstrass bridge without touching the first, and an advance on the
field-of-moduli theory closes the first without touching the second.  What
it does not buy is a smaller total: the sum is still this statement.

**VACUITY, stated plainly.**  By Mazur's theorem itself `Y_0(p)(ℚ) = ∅` for
these `p`, so this leaf is vacuously true and cannot be tested against an
example.  That is inherent to the whole node — its sibling and their
consumer are non-existence statements — and is not a defect introduced by
the cut; but it does mean a prover must be careful not to "prove" this leaf
by an argument that quietly assumes the conclusion of `cuspidal_x0_prime`.

**CORRECTION 2026-07-27 — the sentence that used to end this paragraph,
"the non-vacuous statement it specialises is the descent for `p` prime,
`p ≥ 5` and `j ≠ 0, 1728`, which is where a proof should start", is
WRONG for the `hj.jm y = E.j` conjunct.**  That membership-free statement
is FALSE, with an explicit junk-`jm` witness at `N = 5`; see the section
"THE RECOMMENDED NON-VACUOUS TARGET IS FALSE" in
`exists_weierstrass_jm_of_gamma0Datum`'s docstring above.  The advice is
sound for the DESCENT half only (`exists_gamma0Datum_classify_eq`), where
the field-of-moduli theorem really is the non-vacuous statement.

The residual irreducibility is now recorded on the two leaves, not here:
the coarse space with its `ℚ̄`-points identified with pairs `(E, C)` and the
twisting/field-of-moduli theory on the first, the `IsJMapOn` gap on the
second. -/
theorem exists_weierstrass_jm_of_relPointY0 {p : ℕ} (hp : p.Prime)
    (hmem : p ∉ mazurIsogenyPrimes)
    {Y : Scheme.{0}} {strY : Y ⟶ SpecQ} {hc : IsCoarseModuliY0 p strY}
    (hj : IsJMapOn p hc) (y : RelPoint strY (𝟙 SpecQ)) :
    ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic) (g : (E⁄(AlgebraicClosure ℚ)).Point),
      addOrderOf g = p ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
        WeierstrassCurve.Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) ∧
      hj.jm y = E.j := by
  -- the point is classified by a `Γ₀(p)`-datum over `ℚ` itself: this is the
  -- field-of-moduli descent, and the only place `hmem` is used
  obtain ⟨d, hd⟩ := exists_gamma0Datum_classify_eq hp hmem hc y
  subst hd
  -- and such a datum is a Weierstrass curve whose `j` is the value of `jm`
  exact exists_weierstrass_jm_of_gamma0Datum hp hmem hj d

/-- **Mazur 1978 §5 on the elliptic-curve side** (sorry node, introduced
2026-07-27): no elliptic curve over `ℚ` with a Galois-stable cyclic subgroup
of order `p`, `p` a prime outside `mazurIsogenyPrimes`, has `q`-integral
`j`-invariant at every prime `q ∉ {2, p}`.

TRUE — this is Mazur 1978 §5: the isogeny character `λ` attached to the
`p`-isogeny satisfies `λ^12` unramified outside `p`, and potentially good
reduction away from `{2, p}` is exactly what licenses the Frobenius-trace
computation; the Serre–Raynaud signature, the resultant elimination and the
class-number-one determination then force `p ∈ mazurIsogenyPrimes`.

## THIS IS DUPLICATED CONTENT, AND THE DUPLICATION IS FORCED BY IMPORTS

`FreyCurve/MazurTorsion.lean` already PROVES the corresponding statement,
`WeierstrassCurve.not_isogenyCharacter_of_prime_ge_twentyThree`, over four
leaves — `potentiallyGoodReduction_of_isogenyCharacter`,
`exists_isogenySignature`, `not_isogenyCharacter_of_isogenySignature_ne_six`
and `mem_classNumberOnePrimes_of_isogenySignature_six`.  That module IMPORTS
this one, so the theorem cannot be cited here and the statement has to be
made again.

**The relationship is precise, and it is NOT circular.**  That proof's step
`0` is `potentiallyGoodReduction_of_isogenyCharacter`, which is Mazur's
Cor. 4.4 — the *sibling* of this leaf, and the thing
`exists_eisensteinFormalImmersionAt` above is about.  This leaf takes
potential good reduction as a HYPOTHESIS instead of deriving it, so it is
steps 1–3 only.  Discharging it must therefore NOT go through Cor. 4.4, and
in particular not through `cuspidal_x0_prime` below; see that theorem's
`⚠ DO NOT CLOSE` warning, which records the same trap in the other
direction.

**The right repair is a HOIST, not a proof.**  The three signature/resultant
/class-number leaves of `MazurTorsion.lean` mention only `WeierstrassCurve`,
`Field.absoluteGaloisGroup` and `padicValRat`; nothing in them needs this
module.  Moving them (and the `hstable ↔ hlam` bridge
`exists_isogenyCharacter`) to a module upstream of BOTH would let this leaf
be discharged by citation and would delete the duplication outright.  That
is a cross-module refactor with two owners and is deliberately not done
here.

Stated in the `hstable` form rather than with an isogeny character `λ`
because that is the form this module has (`nonempty_gamma0Datum_of_stable`,
`IsJMapOn.classify_jm`); the two are equivalent, by the bridge named above.

`2` is excluded because the reduction analysis is at odd primes, and `p`
itself because the character is ramified there by construction; keeping both
out of the quantifier is the direction that leaves the leaf weakest. -/
theorem false_of_stable_of_forall_padicValRat_nonneg (E : WeierstrassCurve ℚ)
    [E.IsElliptic] {p : ℕ} (_hp : p.Prime) (_hmem : p ∉ mazurIsogenyPrimes)
    (g : (E⁄(AlgebraicClosure ℚ)).Point) (_hg : addOrderOf g = p)
    (_hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ AddSubgroup.zmultiples g,
      WeierstrassCurve.Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
        AddSubgroup.zmultiples g)
    (_hint : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → 0 ≤ padicValRat q E.j) :
    False :=
  sorry

/-- **The potentially-good-reduction case of Mazur's Theorem 1** (PROVEN
2026-07-27 over `exists_weierstrass_jm_of_relPointY0` and
`false_of_stable_of_forall_padicValRat_nonneg`): for a prime
`p ∉ mazurIsogenyPrimes` there is no rational point of `Y_0(p)` whose
`j`-invariant is integral at every prime outside `{2, p}`.

TRUE — this is Mazur 1978 §5, the half of Theorem 1 that Cor. 4.4 does *not*
cover.  A point with no `j`-pole outside `{2, p}` gives a curve with
potentially good reduction there, so the isogeny character `λ` attached to
the `p`-isogeny satisfies `λ^12` unramified outside `p`; the resulting
class-number and CM analysis forces `p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 37, 43,
67, 163}` — that is, `p ∈ mazurIsogenyPrimes`, contradicting the hypothesis.
The list in `mazurIsogenyPrimes` is exactly the output of that analysis, which
is why the leaf is stated against the list rather than against a bound.

`2` is excluded because the reduction analysis is at odd primes, and `p`
itself because the character is ramified there by construction; keeping both
out of the quantifier is the direction that leaves the leaf weakest.

## THE CUT (2026-07-27): THE COARSE SPACE AND THE ARITHMETIC ARE SEPARATE

This leaf was about the COARSE space: `y` is a rational point of `Y_0(p)`,
which need not be represented by a pair `(E, C)` defined over `ℚ`.  That
descent is a completely different subject from Mazur §5, and the two are now
separate leaves:

* `exists_weierstrass_jm_of_relPointY0` — the descent (field of moduli,
  twists, the `Aut(E, C) = {±1}` condition);
* `false_of_stable_of_forall_padicValRat_nonneg` — Mazur §5 proper (isogeny
  character, Serre–Raynaud, resultants, class number one), stated purely in
  terms of Weierstrass curves and therefore quotable, hoistable, and
  testable independently of every scheme in this file.

The three-line assembly below is the whole of what joined them.  Note the
second leaf duplicates content already decomposed in
`FreyCurve/MazurTorsion.lean`; its docstring records why the import
direction forces that, and what the real repair is. -/
theorem false_of_relPointY0_of_forall_padicValRat_nonneg {p : ℕ} (hp : p.Prime)
    (hmem : p ∉ mazurIsogenyPrimes)
    {Y : Scheme.{0}} {strY : Y ⟶ SpecQ} {hc : IsCoarseModuliY0 p strY}
    (hj : IsJMapOn p hc) (y : RelPoint strY (𝟙 SpecQ))
    (hint : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → 0 ≤ padicValRat q (hj.jm y)) :
    False := by
  -- the coarse point is represented by a curve with a stable `p`-subgroup
  obtain ⟨E, hE, g, hg, hstable, hjE⟩ :=
    exists_weierstrass_jm_of_relPointY0 hp hmem hj y
  letI := hE
  -- and its `j`-invariant inherits the integrality hypothesis
  exact false_of_stable_of_forall_padicValRat_nonneg E hp hmem g hg hstable
    (fun q hq hq2 hqp => hjE ▸ hint q hq hq2 hqp)

/-- **Mazur 1978, Theorem 1** (PROVEN over two leaves, 2026-07-27): for every
prime `p ∉ mazurIsogenyPrimes`, every rational point of `X_0(p)` is a cusp.

TRUE — Mazur, *Rational isogenies of prime degree*, Invent. Math. 44
(1978), Theorem 1: `X_0(p)(ℚ)` consists of the two cusps `0` and `∞` for
every prime `p ∉ {2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}`.

**This is the statement in the shape Mazur proves it**, which is the
point of routing `y0HasNoRationalPoint_prime` through it.

## THE DECOMPOSITION (2026-07-27), AND WHY THE CASE SPLIT IS THE RIGHT ONE

The bare `sorry` is gone: the proof below is written out, and both branches
are themselves now proven — the three surviving leaves under this node are
`exists_eisensteinFormalImmersionAt` (Mazur Cor. 4.3–4.4),
`exists_weierstrass_jm_of_relPointY0` (the coarse-to-fine descent) and
`false_of_stable_of_forall_padicValRat_nonneg` (Mazur §5), all stated
immediately above.  The split is Mazur's own, and
it is the *tautological* one on the `j`-invariant of the point — either `j`
has a pole somewhere outside `{2, p}` or it does not:

* a pole at some prime `q ∉ {2, p}` is potentially MULTIPLICATIVE reduction
  at `q`.  `isCusp_redX_of_padicValRat_neg` — THE DICTIONARY, proven above —
  turns that pole into "the point reduces mod `q` into the cuspidal locus",
  and `exists_x0JReductionDatum_formalImmersion` (Mazur Cor. 4.3–4.4, the
  Eisenstein quotient plus the formal immersion at `∞`) turns *that* into
  "the point was a cusp all along" — contradicting that it came from the
  open part `Y_0(p)`;
* no such pole is potentially GOOD reduction outside `{2, p}`, which is
  `false_of_relPointY0_of_forall_padicValRat_nonneg` (Mazur §5, the isogeny
  character and the class-number-one determination).

Being tautological, the split loses nothing: neither leaf carries a
hypothesis the other needs, and together they are exactly the theorem.  The
objects that do not exist at this pin — `J_0(p)`, the Hecke algebra, the
Eisenstein ideal, reduction of an abelian variety, the isogeny character —
are now confined to those two leaves rather than to this node.

**This node is also where the `j`-map dictionary enters the root cone.**
Before this proof was written, `isCusp_redX_of_padicValRat_neg` and the
machinery under it were free-floating: their only possible in-cone consumers
were this node and `potentiallyGoodReduction_of_isogenyCharacter` in
`FreyCurve/MazurTorsion.lean`, and both were bare sorries.

## ⚠ DO NOT CLOSE `potentiallyGoodReduction_of_isogenyCharacter` WITH THIS

That leaf in `FreyCurve/MazurTorsion.lean` can be discharged from this node
in about ten lines, with **no build error** — and doing so makes the whole
chain VACUOUS.  It feeds
`WeierstrassCurve.not_isogenyCharacter_of_prime_ge_twentyThree`, which proves
the elliptic-curve form of Mazur's Theorem 1; and Mazur proves Cor. 4.4 as a
*step toward* Theorem 1, not the other way round.  The honest direction is
the one recorded on `y0HasNoRationalPoint_prime` below: prove this node, then
DERIVE the elliptic-curve statement from it.

Quantified over every model of `IsCompactificationY0`, so it is at least
as strong as the `Y_0(p)` statement it replaces and cannot be discharged
by a degenerate choice of `X`.

Note the conclusion is genuinely stronger than the elliptic-curve
statement `WeierstrassCurve.prime_mem_cyclicIsogenyDegrees` in
`FreyCurve/MazurTorsion.lean` (which is downstream of this module and so
unusable here): it rules out rational points of a COARSE space, which
need not be represented by a pair `(E, C)` defined over `ℚ`. -/
theorem cuspidal_x0_prime {p : ℕ} (hp : p.Prime) (hmem : p ∉ mazurIsogenyPrimes)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (hc : IsCoarseModuliY0 p strY) (hX : IsCompactificationY0 strY strX)
    (x : RelPoint strX (𝟙 SpecQ)) : hX.IsCusp x := by
  -- Suppose `x` is NOT a cusp: it comes from a point `y0` of the open part.
  rintro ⟨y0, hy0⟩
  -- `y0` is then a rational point of `Y_0(p)`; the compatibility
  -- `y0 ≫ strY = 𝟙` is forced, exactly as `IsCompactificationY0.IsCusp`'s
  -- docstring records, and is not an extra assumption.
  have hy : y0 ≫ strY = 𝟙 SpecQ := by
    rw [← hX.over, ← Category.assoc, hy0]; exact x.2
  set y : RelPoint strY (𝟙 SpecQ) := ⟨y0, hy⟩
  -- the `j`-map on `Y_0(p)(ℚ)`; `p ≠ 0` because `p` is prime
  obtain ⟨hj⟩ := exists_jMap p hp.ne_zero hc
  by_cases hint : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → 0 ≤ padicValRat q (hj.jm y)
  · -- potentially GOOD reduction outside `{2, p}`
    exact false_of_relPointY0_of_forall_padicValRat_nonneg hp hmem hj y hint
  · -- potentially MULTIPLICATIVE reduction at some `q ∉ {2, p}`
    push Not at hint
    obtain ⟨q, hq, hq2, hqp, hv⟩ := hint
    obtain ⟨Y', X', strY', strX', jY', hX', hjr, hfi⟩ :=
      exists_x0JReductionDatum_formalImmersion hp hmem hq hq2 hqp hX hj
    -- THE DICTIONARY: the pole makes the reduction of `y` cuspidal …
    -- … and the formal immersion makes `y` itself a cusp, which it is not.
    exact hfi _ (isCusp_redX_of_padicValRat_neg hjr y hv) ⟨y.1, rfl⟩

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

Both hold at all thirteen Kenku levels — see
`hasRankZeroJacobian_of_kenkuLevel`. -/
def HasRankZeroJacobian {X : Scheme.{0}} (strX : X ⟶ SpecQ) : Prop :=
  ∃ (J : Scheme.{0}) (jstr : J ⟶ SpecQ) (ab : AbelianSchemeStruct jstr)
    (o : RelPoint strX (𝟙 SpecQ)) (jac : IsJacobianOf strX ab o),
    Finite (RelPoint jstr (𝟙 SpecQ)) ∧ Function.Injective (jac.aj (𝟙 SpecQ))

/-- **The thirteen rank-`0` levels of Kenku's non-prime-power
determination**, i.e. the named level nodes below.  All thirteen have
`rank J_0(N)(ℚ) = 0` and `genus X_0(N) ≥ 1`; nine of them additionally
have a single witness prime (`x0WitnessTable`), and the remaining four —
`45, 54, 63, 75` — need a multi-prime Mordell–Weil sieve.

**`35` and `39` were added 2026-07-27** (this list previously held the
eleven levels `20, 24, 28, 30, 36, 42, 45, 50, 54, 63, 75`).  They are
the two small semiprime levels of `witnessSemiprimeLevels`, and they
belong here for exactly the reason the other nine do: rank `0` plus a
sharp witness prime.  Adding them is what closes
`y0HasNoRationalPoint_of_witnessSemiprimeLevel`, which is now proven by
`y0HasNoRationalPoint_of_witnessPrime` verbatim.

Note what this does and does not change.  The two `decide`-proved
consequences — `one_le_x0Genus_of_kenkuLevel` and
`numRationalCusps_pos_of_kenkuLevel` — still close, because
`x0Genus 35 = x0Genus 39 = 3` and `numRationalCusps 35 =
numRationalCusps 39 = 4`.  The two sorried consequences —
`finite_jacobian_of_kenkuLevel` and `exists_x0Compactification_mod_prime`
— acquire two further cases each; both are true at `35` and `39` by the
same reconnaissance that justifies the other levels, and neither leaf's
IRREDUCIBLE verdict changes.

The rank-`0` claim at the two new levels, independently reproduced with
PARI/GP: `S_2(Γ_0(35))` is `3`-dimensional and all new, splitting as a
`1`-dimensional and a `2`-dimensional newform factor, with
`L(f, 1) = 0.7029…, 0.4601…, 0.8102…` on the three embeddings — all
nonzero, so analytic rank `0` on every factor, hence Mordell–Weil rank
`0` by Kolyvagin–Logachev.  Likewise `S_2(Γ_0(39))` is `3`-dimensional
and all new with `L(f, 1) = 0.8267…, 0.4797…, 0.7964…`.  (Contrast `65`
and `91`, whose sharp-looking counts are a trap precisely because their
ranks are `1` and `2`; see
`y0HasNoRationalPoint_of_chabautySemiprimeLevel`.) -/
def kenkuLevels : List ℕ := [20, 24, 28, 30, 35, 36, 39, 42, 45, 50, 54, 63, 75]

/-- **The witness table `(N, ℓ, #X_0(N)(𝔽_ℓ))` for the nine levels that
close on a single prime.**

Computed with Magma from Eichler–Shimura,
`#X_0(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`; see the
`#### Reconnaissance` block below for the full table with genus and
cusp data.  In every row the count EQUALS `numRationalCusps N`, which is
precisely why these nine close on one prime.

Two entries are traps for anyone regenerating this table.  `N = 30`
needs `ℓ = 17`: the small primes `7, 11, 13` give `12, 20, 16`, all
strictly larger than `8`.  And `N = 36`, `N = 50` must be counted
against their RATIONAL cusps (`6` and `4`), not against their `12`
cusps.

**The rows `(35, 3, 4)` and `(39, 5, 4)` were added 2026-07-27**, and
they were reproduced with PARI/GP from the trace form of the cuspidal
space rather than taken from the prose table they close:
`Tr(T_3 ∣ S_2(Γ_0(35))) = 0`, so `#X_0(35)(𝔽_3) = 3 + 1 − 0 = 4`; and
`Tr(T_5 ∣ S_2(Γ_0(39))) = 2`, so `#X_0(39)(𝔽_5) = 5 + 1 − 2 = 4`.  Both
levels have `numRationalCusps N = 4` — all four divisors `1, p, q, pq`
of a squarefree semiprime satisfy `gcd(d, N/d) = 1` — so both rows are
sharp, which is what
`y0HasNoRationalPoint_of_witnessSemiprimeLevel` consumes.  Note `3 ∤ 35`
and `5 ∤ 39`, as `card_le_of_rankZeroJacobian` requires. -/
def x0WitnessTable : List (ℕ × ℕ × ℕ) :=
  [(20, 3, 6), (24, 5, 8), (28, 5, 6), (30, 17, 8), (35, 3, 4), (36, 5, 6), (39, 5, 4),
    (42, 11, 8), (50, 3, 4)]

/-- **Existence of the compactified coarse moduli space `X_0(N)` over an
ARBITRARY base field whose characteristic does not divide `N`** (sorry
node — the single remaining existence leaf for `X_0(N)` in POSITIVE
characteristic).

IRREDUCIBLE at this pin for the same reason as `exists_coarseModuliY0`:
neither modular curves nor a smooth-compactification theorem for curves
exists anywhere in `Mathlib`.  AXIS SEARCHED: the BASE direction, which
is what produced this merge; not searched is a cut along the moduli
problem itself (generalised elliptic curves / Néron polygons), which
would need the Deligne–Rapoport degeneration theory that
`Gamma0Datum` deliberately does not carry.

INTEGRATION NOTE (2026-07-27).  As introduced, this leaf also carried the
characteristic-`0` case, and `exists_x0Compactification` was derived from
it.  That derivation is NOT kept: the ℚ case was PROVEN independently, from
`exists_isSmoothCompactification` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`, and
routing it through a sorry node would have REGRESSED a proven declaration.
So this leaf's remaining consumer is
`exists_x0Compactification_finiteField`, i.e. characteristic `ℓ` only —
which is also where the generality was wanted.  A prover who closes it may
optionally re-derive the ℚ case from it, but must not delete the direct
proof below in the process. -/
theorem exists_x0Compactification_field (N : ℕ) (hN : 0 < N) (K : Type)
    [Field K] (hchar : ¬ ringChar K ∣ N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ Spec (CommRingCat.of K))
      (strY : Y ⟶ Spec (CommRingCat.of K)) (j : Y ⟶ X),
      Nonempty (IsX0Compactification N strX strY j) :=
  sorry

/-- **Existence of the compactified coarse moduli space `X_0(N)` over
`ℚ`** (PROVEN, over `exists_coarseModuliY0` and one modular leaf;
formerly a sorry node).

TRUE and classical: `Y_0(N)` is a smooth affine curve over `K` and every
smooth curve over a field has a unique smooth projective
compactification; for `Y_0(N)` it is the modular curve `X_0(N)` of
Deligne–Rapoport, obtained directly as the coarse space of the moduli
problem of GENERALISED elliptic curves with `Γ₀(N)`-structure, the added
points being the cusps.  Deligne–Rapoport construct the smooth proper
model over `ℤ[1/N]`, and this statement is its fibre at `Spec K` for any
`K` with `char K ∤ N`; `IsX0Compactification` was written with a general
base `S` for exactly this reason (see its docstring).

**This leaf is the MERGE of two former ones** (2026-07-27, authorized):
`exists_x0Compactification` (base `ℚ`) and
`exists_x0Compactification_finiteField` (base `𝔽_ℓ`, `ℓ ∤ N`) differed
only in the base field, and both are now one-line corollaries below.  The
two names are kept so no call site moves.

**Why `¬ ringChar K ∣ N` and not something weaker.**  It is exactly the
condition under which the `Γ₀(N)`-problem is smooth: at `char K = p ∣ N`
the `Γ₀(N)`-structure degenerates (the subgroup scheme of order `N`
acquires an infinitesimal part) and `X_0(N)_K` is no longer smooth, so
the `smooth` field of `IsX0Compactification` would be FALSE.  At
`char K = 0` the hypothesis reads `¬ 0 ∣ N`, i.e. `N ≠ 0`, which is why
`hN` alone suffices at `K = ℚ`.  Geometric connectedness — the
`connected` field — is the one clause that is not formal: it holds for
`Γ₀(N)` because `det : Γ₀(N) → (ℤ/N)ˣ` is surjective, so the cusps are
not split apart by the cyclotomic field, unlike for `Γ₁(N)` or `Γ(N)`.

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
itself, which is a genuinely separate and still-open statement.

This is the ℚ case.  The GENERAL-BASE leaf
`exists_x0Compactification_field` is stated just above; this statement
does NOT go through it (see the integration note there). -/
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
`nonempty_cuspLocus` (the leaf this reduces to since 2026-07-27) needs
only the easy direction: for `d` with
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

/-- **A `ℚ`-algebra of dimension one has a `ℚ`-point on its spectrum**
(PROVEN 2026-07-27).

`Module.finrank ℚ A = 1` makes `algebraMap ℚ A` bijective
(`Algebra.finrank_eq_one_iff_bijective_algebraMap`, whose `Module.Free`
hypothesis is automatic over a field), and the inverse ring map
`A →+* ℚ` is a section of the structure morphism on spectra.

Small, but it is the whole of the arithmetic that converts a statement
about RESIDUE DEGREES into a statement about RATIONAL POINTS, and it is
what lets the cusp route below avoid Galois descent; see the ROUTE note
on `IsX0Compactification.CuspLocus`. -/
theorem exists_specSection_of_finrank_eq_one {A : Type} [CommRing A] [Algebra ℚ A]
    (hrank : Module.finrank ℚ A = 1) :
    ∃ σ : SpecQ ⟶ Spec (CommRingCat.of A),
      σ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) = 𝟙 SpecQ := by
  have hbij : Function.Bijective (algebraMap ℚ A) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hrank
  let e : ℚ ≃+* A := RingEquiv.ofBijective _ hbij
  refine ⟨Spec.map (CommRingCat.ofHom (e.symm : A →+* ℚ)), ?_⟩
  rw [← Spec.map_comp]
  have hid : (CommRingCat.ofHom (algebraMap ℚ A) ≫ CommRingCat.ofHom (e.symm : A →+* ℚ))
      = 𝟙 (CommRingCat.of ℚ) := by
    ext x
    exact e.symm_apply_apply x
  rw [hid, Spec.map_id]

/-- **The cusp locus of `X_0(N)`, as a finite `ℚ`-scheme with prescribed
residue degrees.**

The cuspidal part of the Deligne–Rapoport model, written down as data:
`X ∖ Y` is the disjoint union, over the divisors `d ∣ N`, of `Spec` of a
field `K d` of degree `φ(gcd(d, N/d))` over `ℚ`.  The genuine `K d` is
`ℚ(ζ_{gcd(d, N/d)})`; only its DEGREE is recorded, because only the
degree is consumed.

**ROUTE — what this cut avoids, and how.**  The obstruction recorded on
`nonempty_cuspLocus` below is *Galois descent for rational points of a
`ℚ`-scheme*.  Mathlib's `CuspOrbits (Gamma0 N)` (in
`Mathlib/NumberTheory/ModularForms/Cusps.lean`) does describe the cusps
— but as a `Γ_0(N)`-set of points of `OnePoint ℝ`, and turning a
`Γ_ℚ`-fixed geometric point into an element of `RelPoint strX (𝟙 SpecQ)`
needs a descent theorem present in none of `Fermat/`,
`.lake/packages/mathlib/`, `~/cs/FLT/`.  This structure sidesteps that
entirely by recording the cusps **over `ℚ` from the start**, as a residue
ALGEBRA rather than as a Galois orbit: rationality of the cusp above `d`
becomes `finrank ℚ (K d) = 1`, and
`exists_specSection_of_finrank_eq_one` extracts the `ℚ`-point by pure
algebra.  Descent is not defeated here, it is *relocated* — absorbed into
the Deligne–Rapoport statement, which is where the literature proves it
and where a formalisation would have to prove it anyway.

**WHY `cover` IS A FIELD, and why this is not the unsafe
"invariant-first" cut.**  Axis 4 on `nonempty_cuspLocus` records that
peeling a divisor invariant off as a separate leaf is unsafe: quantified
over an arbitrary invariant the existence half is FALSE, by the junk
witness `dinv ≡ 1` — the same defect the FORMAL-CONTENT AUDIT records
for `redX`.  `cover` is what rules the analogue out here.  It forces the
`κ d` to EXHAUST `(Set.range j.base)ᶜ`, so the datum determines the cusp
locus exactly and cannot be satisfied by a curve whose cusps are wrong or
too few.  It is strictly more than `nonempty_cuspIndexing_of_ne_zero`
consumes — the derivation uses only the `⊆` direction — and it is carried
anyway, so that the leaf states the theorem the literature proves rather
than the weakest thing that happens to suffice.

Only the EASY half of Ogg's description is asked for even so: the residue
degrees are recorded, but nothing here says the Galois action on the
`φ(gcd(d, N/d))` geometric cusps above `d` is the cyclotomic one.  See
`IsX0Compactification.CuspIndexing` for why the hard half is not an
obligation of this development.

Stated over `Spec ℚ` rather than over the general base of
`IsX0Compactification`, for the same reason `CuspIndexing` is: residue
fields change under base change, so `φ(gcd(d, N/d))` would be the wrong
degree over `Spec 𝔽_ℓ`. -/
structure IsX0Compactification.CuspLocus {N : ℕ} {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) where
  /-- the residue field of the cusp above `d` — genuinely `ℚ(ζ_{gcd(d, N/d)})` -/
  K : N.divisors → Type
  /-- each residue algebra is a field -/
  [isField : ∀ d, Field (K d)]
  /-- each residue field is a `ℚ`-algebra -/
  [isAlgebra : ∀ d, Algebra ℚ (K d)]
  /-- the cusp above `d` has residue degree `φ(gcd(d, N/d))` -/
  degree : ∀ d : N.divisors,
    Module.finrank ℚ (K d) = Nat.totient (Nat.gcd d.1 (N / d.1))
  /-- the cusp above `d`, as a `ℚ`-morphism `Spec (K d) ⟶ X` -/
  κ : ∀ d : N.divisors, Spec (CommRingCat.of (K d)) ⟶ X
  /-- `κ d` is a morphism over `Spec ℚ`.  Named `comm` rather than the
  obvious `over`, which is a reserved token in this file's notation
  scope and silently truncates the structure. -/
  comm : ∀ d : N.divisors,
    κ d ≫ strX = Spec.map (CommRingCat.ofHom (algebraMap ℚ (K d)))
  /-- the cusps exhaust the complement of `Y` -/
  cover : ⋃ d : N.divisors, Set.range (κ d).base = (Set.range j.base)ᶜ
  /-- cusps above distinct divisors are disjoint -/
  disj : ∀ d d' : N.divisors, d ≠ d' →
    Disjoint (Set.range (κ d).base) (Set.range (κ d').base)

attribute [instance] IsX0Compactification.CuspLocus.isField
  IsX0Compactification.CuspLocus.isAlgebra

/-- **The indexed `ℚ`-rational cusps, from the cusp locus** (PROVEN
2026-07-27; axiom-audited `[propext, Classical.choice, Quot.sound]`).

This is the sorry-free half of `nonempty_cuspIndexing_of_ne_zero`, and it
is where the divisor bookkeeping happens, so that `nonempty_cuspLocus`
carries only Deligne–Rapoport.  Three steps, one per field of
`CuspIndexing`:

* `cusp` — `d ∈ rationalCuspDivisors N` unfolds to `d ∈ N.divisors`
  together with `φ(gcd(d, N/d)) = 1`, so `degree` gives
  `finrank ℚ (K ⟨d, _⟩) = 1` and
  `exists_specSection_of_finrank_eq_one` a section
  `σ : Spec ℚ ⟶ Spec (K ⟨d, _⟩)`; the cusp is `σ ≫ κ ⟨d, _⟩`, a section
  of `strX` by `comm`.
* `isCusp` — evaluate at the unique point of `Spec ℚ`.  The image lies in
  `Set.range (κ ⟨d, _⟩).base`, hence in `(Set.range j.base)ᶜ` by `cover`,
  while any point of the form `sectionAlong j h.comm y` lies in
  `Set.range j.base`.
* `inj` — two cusps that are equal as morphisms have the same image
  point, contradicting `disj`.

Note what is NOT needed: no Galois action, no descent, and none of the
cyclotomic identification of `K d` beyond its degree. -/
theorem nonempty_cuspIndexing_of_cuspLocus {N : ℕ} {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    {h : IsX0Compactification N strX strY j} (C : h.CuspLocus) :
    Nonempty h.CuspIndexing := by
  classical
  have hmem : ∀ d ∈ rationalCuspDivisors N,
      d ∈ N.divisors ∧ Nat.totient (Nat.gcd d (N / d)) = 1 := by
    intro d hd
    simpa [rationalCuspDivisors, Finset.mem_filter] using hd
  have hsec : ∀ (d : ℕ) (hd : d ∈ rationalCuspDivisors N),
      ∃ σ : SpecQ ⟶ Spec (CommRingCat.of (C.K ⟨d, (hmem d hd).1⟩)),
        σ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (C.K ⟨d, (hmem d hd).1⟩)))
          = 𝟙 SpecQ := fun d hd =>
    exists_specSection_of_finrank_eq_one
      (by rw [C.degree ⟨d, (hmem d hd).1⟩, (hmem d hd).2])
  choose σ hσ using hsec
  refine ⟨{ cusp := fun d hd => ⟨σ d hd ≫ C.κ ⟨d, (hmem d hd).1⟩, ?_⟩
            isCusp := ?_
            inj := ?_ }⟩
  · rw [Category.assoc, C.comm ⟨d, (hmem d hd).1⟩, hσ d hd]
  · rintro d hd ⟨y, hy⟩
    obtain ⟨P⟩ : Nonempty (PrimeSpectrum ℚ) := inferInstance
    have heq : y.1 ≫ j = σ d hd ≫ C.κ ⟨d, (hmem d hd).1⟩ := congrArg Subtype.val hy
    have hp := congrArg (fun (f : SpecQ ⟶ X) => f.base P) heq
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hp
    have hout : ((C.κ ⟨d, (hmem d hd).1⟩).base ((σ d hd).base P))
        ∈ (Set.range j.base)ᶜ := by
      rw [← C.cover]
      exact Set.mem_iUnion.mpr ⟨⟨d, (hmem d hd).1⟩, ⟨_, rfl⟩⟩
    exact hout ⟨y.1.base P, hp⟩
  · intro d hd d' hd' heqc
    by_contra hne
    obtain ⟨P⟩ : Nonempty (PrimeSpectrum ℚ) := inferInstance
    have heq : σ d hd ≫ C.κ ⟨d, (hmem d hd).1⟩ = σ d' hd' ≫ C.κ ⟨d', (hmem d' hd').1⟩ :=
      congrArg Subtype.val heqc
    have hp := congrArg (fun (f : SpecQ ⟶ X) => f.base P) heq
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hp
    exact Set.disjoint_left.mp
      (C.disj ⟨d, (hmem d hd).1⟩ ⟨d', (hmem d' hd').1⟩
        (fun hh => hne (congrArg Subtype.val hh))) ⟨_, rfl⟩ ⟨_, hp.symm⟩

/-- **The cusp locus of `X_0(N)` exists: `X ∖ Y` is `∐_{d ∣ N} Spec
ℚ(ζ_{gcd(d, N/d)})`** (sorry node).

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

6. *The RESIDUE-FIELD axis* — TAKEN, and it is why this leaf now carries
   the whole obstruction while `nonempty_cuspIndexing_of_ne_zero` is
   proven.  The previous five all asked how to produce a RATIONAL POINT
   from a description of the cusps as a Galois SET, which is why they kept
   arriving at descent.  Describe the cusp locus instead as a finite
   `ℚ`-SCHEME with prescribed residue degrees — this structure — and
   rationality above `d` becomes `finrank ℚ (K d) = 1`, from which
   `exists_specSection_of_finrank_eq_one` produces the point with no
   Galois theory whatsoever.  What that buys is a change of STATEMENT, not
   a proof: this leaf is still exactly Deligne–Rapoport, but it is now the
   statement DR actually proves, over `ℚ` and with the cusps as a scheme.
   This axis is refuted by exhibiting a model of `CuspLocus` over some
   `IsX0Compactification` whose cusps are not those of `X_0(N)` — `cover`
   is the field that is supposed to forbid it.

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
the cusp locus of `X`, i.e. to the uniformisation together with its
`ℚ`-structure.

AMENDMENT (2026-07-27, axis 6).  That correction also said the alternative
was "Galois descent for rational points of a `ℚ`-scheme".  **Descent is no
longer on the route.**  It was needed only because the cusps were being
described as a Galois SET; stated as a `ℚ`-SCHEME with residue degrees —
which is how Deligne–Rapoport states it — the rational points come out by
`exists_specSection_of_finrank_eq_one`, pure algebra.  So a successor
should NOT go and build descent for this leaf.  What remains is the
uniformisation and the `ℚ`-structure, and nothing else.

`hN : N ≠ 0` is carried because every construction of a cusp needs it
(`Nat.divisors 0 = ∅`, so there is nothing to index at `N = 0`), and
because `N = 0` is a recurring trap in this module — see `exists_jMap`,
where the same hypothesis IS load-bearing.  It is not needed for TRUTH:
`IsX0Compactification 0` looks unsatisfiable (the `Γ₀(0)`-problem is
supported on the empty scheme, so `coarse` forces `Y = ∅`, whence
`finite_compl` asks a smooth proper geometrically connected curve to be
finite), but nothing in this file proves that, and `N = 0` never reaches
here — `nonempty_cuspIndexing` discharges it separately and vacuously. -/
theorem nonempty_cuspLocus (N : ℕ) (hN : N ≠ 0) {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) :
    Nonempty h.CuspLocus :=
  sorry

/-- **`X_0(N)` has a `ℚ`-rational cusp above every divisor `d ∣ N` with
`φ(gcd(d, N/d)) = 1`, and these are pairwise distinct** (PROVEN
2026-07-27 over `nonempty_cuspLocus`).

The former sorry leaf.  Everything that was open here is now open at
`nonempty_cuspLocus`, in the form the literature states it — the cusp
locus as a finite `ℚ`-scheme with prescribed residue degrees — and the
step from there to this indexed family is `nonempty_cuspIndexing_of_cuspLocus`,
which is sorry-free.

The cut is what removes GALOIS DESCENT from the route; see the ROUTE note
on `IsX0Compactification.CuspLocus` for why the previously recorded
obstruction (a bridge from mathlib's `CuspOrbits (Gamma0 N)` to
`RelPoint strX (𝟙 SpecQ)`) is not on this path at all. -/
theorem nonempty_cuspIndexing_of_ne_zero (N : ℕ) (hN : N ≠ 0) {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) :
    Nonempty h.CuspIndexing :=
  (nonempty_cuspLocus N hN h).elim nonempty_cuspIndexing_of_cuspLocus

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
`not_isIso_jacobian_of_one_le_x0Genus` — "the Jacobian is
positive-dimensional" — and that is the sorry node.  (Before 2026-07-27
the bridge was `injective_aj_of_one_le_x0Genus`; that is now a PROVEN
assembly over the bridge and the Riemann–Roch leaf.) -/
def x0Genus (N : ℕ) : ℤ :=
  (12 + (gammaZeroIndex N : ℤ) - 3 * numEllipticTwo N - 4 * numEllipticThree N
    - 6 * numCusps N) / 12

/-- **`genus X_0(N) ≥ 1` at the thirteen Kenku levels** (PROVEN).

This is the arithmetic half of `hasRankZeroJacobian_of_kenkuLevel`, and
it is proven rather than asserted: `decide` evaluates `x0Genus` — index,
elliptic points and cusps and all — at each of the thirteen levels.  The
values are

`N  : 20 24 28 30 35 36 39 42 45 50 54 63 75`
`g  :  1  1  2  3  3  1  3  5  3  2  4  5  5`

matching the table in `kenkuLevels`, and independently reproduced with
PARI/GP.  Genus `0` would make the leaf below FALSE (see
`HasRankZeroJacobian`: at `N = 1` the Jacobian is trivial and
`X_0(1) = ℙ¹` has infinitely many rational points), so this is exactly
the hypothesis that rules that out.

**The `decide` still closes after `35, 39` were added to `kenkuLevels`
on 2026-07-27**, which was the one mechanical risk of that extension:
`x0Genus 35 = x0Genus 39 = 3`, from `gammaZeroIndex 35 = 48`,
`gammaZeroIndex 39 = 56`, `numEllipticTwo = 0` at both,
`numEllipticThree 35 = 0`, `numEllipticThree 39 = 2` and
`numCusps = 4` at both. -/
theorem one_le_x0Genus_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels) : 1 ≤ x0Genus N := by
  fin_cases hN <;> decide

/-- **`X_0(N)` has at least one rational cusp, at the thirteen Kenku
levels** (PROVEN, by `decide` on `numRationalCusps`, whose values are
`6, 8, 6, 8, 4, 6, 4, 8, 4, 4, 4, 4, 4`).

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

**FAITHFULNESS AUDIT (2026-07-27), two checks, both passed.**

*Not vacuous.*  The obvious junk witness is the trivial abelian scheme
`J = Spec ℚ`, `jstr = 𝟙`, for which `RelPoint jstr g` is a singleton.
It does **not** discharge the leaf: `universal` would then force every
natural pointed `c : X(−) ⟶ A(−)` to be constant, which fails for the
genuine `X_0(N)` at every level of positive genus.  So the existential
really does demand the Albanese, and cannot be met cheaply.

*The `∃!` is not too strong.*  `u` is asked to be a bare morphism of
`ℚ`-schemes, **not** a homomorphism, so uniqueness looks suspicious: for
`g ≥ 2` the image of `X` in `J` is a curve inside a `g`-dimensional
variety and is nowhere dense, and two morphisms agreeing on a nowhere
dense subscheme are not usually equal.  Uniqueness nevertheless holds,
by **rigidity**: any morphism `v : J ⟶ A` of abelian varieties over a
field is a homomorphism followed by a translation.  If `u, u'` both
satisfy the displayed condition then `v = u − u'` vanishes on `aj(X)`,
so its homomorphism part is constant on `aj(X)`, hence kills the
subgroup `aj(X)` generates — which is all of `J` — and the translation
part is `0` as well.  So `v = 0`.  The statement is therefore correct as
written, and a prover must not weaken `∃!` to `∃`.

IRREDUCIBLE at this pin, and here is the axis that was searched, so the
next reader need not redo it.  *Cuts along the universal property* were
tried and all fail:

* "existence of `(J, aj)` natural and pointed" + "that `aj` is initial"
  is **not** a cut — the first half is discharged by the trivial `J`
  above, so all the content stays in the second half, which can no
  longer be stated once the witness is chosen.
* "`aj` generates `J`" + "a generating pointed `aj` is initial" is
  UNSOUND: points of `J` are sums of differences of points of `X` only
  fppf-locally, not on the nose as a functor, so the second half would
  be a false leaf.
* the honest cut is *representability of `Pic⁰`* + *autoduality of the
  Jacobian*, and stating it needs a relative Picard functor — line
  bundles on `X ×_S T` modulo pullbacks from `T` — which does not exist
  in `Mathlib`, in `~/cs/FLT`, or here.  The check that would refute
  this: `grep -rn "PicardFunctor\|Pic⁰\|Albanese" Fermat/
  .lake/packages/mathlib/ ~/cs/FLT/`.

So this leaf is gated on writing a relative Picard functor first; that
is real, statable infrastructure and is the correct next step, not
another direct proof attempt. -/
theorem exists_jacobianOf_x0 (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {j : Y ⟶ X} (h : IsX0Compactification N strX strY j)
    (o : RelPoint strX (𝟙 SpecQ)) :
    ∃ (J : Scheme.{0}) (jstr : J ⟶ SpecQ) (ab : AbelianSchemeStruct jstr),
      Nonempty (IsJacobianOf strX ab o) :=
  sorry

/-- **Mordell–Weil: `A(ℚ)` is finitely generated, for EVERY abelian
scheme `A` over `ℚ`** (sorry node) — LEVEL-FREE, CURVE-FREE, and not
about Jacobians at all.

TRUE: this is the Mordell–Weil theorem in its abelian-variety form
(Weil, 1929) — for an abelian variety `A` over a number field `K` the
group `A(K)` is finitely generated.  The classical proof is in two
halves: *weak* Mordell–Weil (`A(K)/nA(K)` is finite, via the Kummer
sequence, finiteness of the class group and Dirichlet's unit theorem),
and the theory of canonical heights together with the descent lemma
(a group with a height function and finite `A(K)/nA(K)` is finitely
generated).

Stated only over the base `Spec ℚ`, which is all this development
consumes.  Note what is NOT a hypothesis: no curve, no `IsJacobianOf`,
no level.  That is the point of splitting it out — every consumer of
`AbelianSchemeStruct` over `ℚ` in this development can use it, and it
carries none of the modular content.

IRREDUCIBLE at this pin, along the axis searched: neither heights on
abelian varieties, nor the weak Mordell–Weil theorem, nor the descent
lemma exists in `Mathlib`, in `~/cs/FLT`, or in this project.  The check
that would refute this: `grep -rn "MordellWeil\|NeronTateHeight" ` over
the three trees.  (`Fermat/FLT/EllipticCurve/MordellWeil.lean` is NOT a
counterexample — despite the name it contains no Mordell–Weil theorem and
no descent machinery; it is an explicit `2`-descent computation for the
two named curves `11a3` and `14a4`, done by hand over `ℤ`.) -/
theorem fg_relPoint_of_abelianScheme {J : Scheme.{0}} {jstr : J ⟶ SpecQ}
    (ab : AbelianSchemeStruct jstr) :
    letI := ab.addCommGroup (𝟙 SpecQ)
    AddGroup.FG (RelPoint jstr (𝟙 SpecQ)) :=
  sorry

/-- **`rank J_0(N)(ℚ) = 0` at the thirteen Kenku levels** (sorry node) —
the DEEP half of `hasRankZeroJacobian_of_kenkuLevel`, and now stated as
what it actually is: `J_0(N)(ℚ)` is a TORSION group.

TRUE, by the reconnaissance recorded below: decomposing the cuspidal
subspace `S_2(Γ_0(N))` into newform factors and evaluating `L(A, 1)` on
each, EVERY factor at EVERY one of the thirteen levels has
`L(A, 1) ≠ 0`;
so `J_0(N)` has analytic rank `0`, hence Mordell–Weil rank `0` by
Kolyvagin–Logachev, hence `J_0(N)(ℚ)` is torsion.

**Why torsion and not finiteness.**  Rank `0` and finiteness are the
same statement only *given* Mordell–Weil, and Mordell–Weil is a
general theorem about abelian varieties that has nothing to do with
modular curves.  Keeping them together made one leaf carrying two
unrelated theories; separated, `fg_relPoint_of_abelianScheme` above holds
the general half and this leaf holds exactly the Kolyvagin–Logachev
half — which is literally the rank statement, since for a finitely
generated abelian group `rank = 0` ⟺ torsion.  The two are recombined by
`AddCommGroup.finite_of_fg_torsion` in `finite_jacobian_of_kenkuLevel`
below, which is now PROVEN.

**Two of the thirteen, `35` and `39`, were added on 2026-07-27** and
their reconnaissance is NOT in the `#### Reconnaissance` block below,
which predates them; it is on
`y0HasNoRationalPoint_of_witnessSemiprimeLevel`.  In brief, both
`S_2(Γ_0(35))` and `S_2(Γ_0(39))` are `3`-dimensional and entirely new,
splitting as a `1`-dimensional plus a `2`-dimensional newform factor,
and all six embeddings give `L(f, 1) ≠ 0` (PARI/GP:
`0.7029…, 0.4601…, 0.8102…` at `35`; `0.8267…, 0.4797…, 0.7964…` at
`39`).  Contrast `65` and `91`, which are deliberately NOT in
`kenkuLevels` because their ranks are `1` and `2`.

`jac` is load-bearing and may not be dropped: the conclusion is FALSE
for an arbitrary abelian scheme over `ℚ` receiving `X` — it is true only
because `jac` pins `J` as the Jacobian of this particular curve, whose
`L`-function is the one being evaluated.  `hN` is likewise load-bearing:
`J_0(N)(ℚ)` has positive rank for many `N` (the first is `N = 37`).

IRREDUCIBLE at this pin, and this is where the depth of the original
leaf now lives, alone: it needs `S_2(Γ_0(N))`, the Hecke algebra,
`L`-functions of modular abelian varieties, and Gross–Zagier/Kolyvagin.
Nothing else in the decomposition below depends on any of that. -/
theorem isTorsion_jacobian_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    letI := ab.addCommGroup (𝟙 SpecQ)
    AddMonoid.IsTorsion (RelPoint jstr (𝟙 SpecQ)) :=
  sorry

/-- **`J_0(N)(ℚ)` is finite at the thirteen Kenku levels** (PROVEN, from
the two leaves above).

Mordell–Weil (`fg_relPoint_of_abelianScheme`) makes `J_0(N)(ℚ)` finitely
generated; Kolyvagin–Logachev (`isTorsion_jacobian_of_kenkuLevel`) makes
it torsion; `AddCommGroup.finite_of_fg_torsion` — the structure theorem
for finitely generated abelian groups — makes it finite.  The group
structure used throughout is `ab.addCommGroup (𝟙 SpecQ)`, the functor of
points of the abelian scheme evaluated at the base. -/
theorem finite_jacobian_of_kenkuLevel (N : ℕ) (hN : N ∈ kenkuLevels)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) : Finite (RelPoint jstr (𝟙 SpecQ)) := by
  letI := ab.addCommGroup (𝟙 SpecQ)
  haveI := fg_relPoint_of_abelianScheme ab
  exact AddCommGroup.finite_of_fg_torsion _
    (isTorsion_jacobian_of_kenkuLevel N hN h jac)

/-- **A curve with a NONTRIVIAL Jacobian has injective Abel–Jacobi**
(sorry node) — LEVEL-FREE: this is the Riemann–Roch half of
`injective_aj_of_one_le_x0Genus`, and it mentions neither `N` nor
`x0Genus` nor `IsX0Compactification`.

TRUE and classical.  `hJ : ¬ IsIso jstr` says `J ≠ Spec ℚ`, i.e. the
Jacobian is positive-dimensional, which for the Jacobian of a curve is
exactly `genus ≥ 1`.  Then: if `aj x = aj y` with `x ≠ y` then
`[x] − [o] = [y] − [o]`, so `x − y` is a principal divisor, so some
rational function has a single simple pole, giving a degree `1` map
`X → ℙ¹`, i.e. `X ≅ ℙ¹` and `genus = 0` — whose Jacobian *is* trivial,
contradicting `hJ`.

**Why `¬ IsIso jstr` rather than a genus.**  There is no genus of a
scheme at this pin, but `dim J = genus X` for the Jacobian, and
`dim J = 0` ⟺ `J ≅ Spec ℚ` ⟺ `IsIso jstr` for an abelian scheme over a
field.  So `¬ IsIso jstr` is a faithful, pin-available rendering of
`genus ≥ 1`, and it needs no dimension theory.

**The three geometric hypotheses may NOT be dropped**, and the leaf is
FALSE without them — `X` must be a *curve*.  Counterexample with `X`
smooth, proper and geometrically connected but of dimension `2`: take
`X = ℙ¹ × E` for an elliptic curve `E`, `o = (0, 0)`.  Its Albanese is
`E`, so `jstr` is not an iso and `hJ` holds, while
`aj (t, e) = e` collapses every `ℙ¹`-fibre and is very far from
injective.  This is why `h.isProper`, `h.smooth` (relative dimension
`1` — the curve condition) and `h.connected` are all passed through.

IRREDUCIBLE at this pin, along the axis searched (divisors and linear
systems): Riemann–Roch for curves does not exist in `Mathlib`.  What
mathlib *does* have, and what a prover should start from, is
`Mathlib/AlgebraicGeometry/AlgebraicCycle`, `.../OrderOfVanishing.lean`,
`.../FunctionField.lean` and `.../RationalMap.lean` — divisors, orders
of vanishing and the function field are all present; the sheaf
cohomology that computes `h⁰(D)` is what is missing. -/
theorem injective_aj_of_not_isIso_jacobian {X J : Scheme.{0}} {strX : X ⟶ SpecQ}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) (hJ : ¬ IsIso jstr) :
    Function.Injective (jac.aj (𝟙 SpecQ)) :=
  sorry

/-- **The genus formula, in its geometric form: `genus X_0(N) ≥ 1` makes
the Jacobian nontrivial** (sorry node) — the arithmetic half of
`injective_aj_of_one_le_x0Genus`, and the ONLY place where the computed
number `x0Genus N` meets the scheme `X`.

TRUE: `x0Genus N` is the genus of `X` by the classical formula
(Diamond–Shurman, Theorem 3.1.1), and `dim J = genus X` for the
Jacobian, so `1 ≤ x0Genus N` gives `dim J ≥ 1`, i.e. `J ≇ Spec ℚ`.

`hg` is load-bearing and is exactly what makes the already-proven
arithmetic of `one_le_x0Genus_of_kenkuLevel` consumed rather than
floating: at genus `0` the conclusion is FALSE, `X_0(1) = ℙ¹` having
trivial Jacobian.  `jac` is load-bearing too — without it `J` is an
arbitrary abelian scheme, and `Spec ℚ` itself is one.  `N` enters only
through `hg` and `h`.

IRREDUCIBLE at this pin: this is the identification of the arithmetic
`x0Genus` with a geometric invariant of `X`, and no such invariant
exists in `Mathlib` (no genus, no `h¹(𝒪_X)`, no Riemann–Hurwitz for the
degree-`μ(N)` map to the `j`-line). -/
theorem not_isIso_jacobian_of_one_le_x0Genus (N : ℕ) (hg : 1 ≤ x0Genus N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) : ¬ IsIso jstr :=
  sorry

/-- **Positive genus makes Abel–Jacobi injective on rational points**
(PROVEN, from the two leaves above) — the bridge from the arithmetic
`x0Genus` to the geometry.

The seam is `¬ IsIso jstr`, "the Jacobian is positive-dimensional".  It
splits the old single leaf into the two theories it was carrying:
`not_isIso_jacobian_of_one_le_x0Genus` is the genus formula and is the
only half that mentions `N`, while `injective_aj_of_not_isIso_jacobian`
is Riemann–Roch and holds for every smooth proper geometrically
connected curve over `ℚ`. -/
theorem injective_aj_of_one_le_x0Genus (N : ℕ) (hg : 1 ≤ x0Genus N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) : Function.Injective (jac.aj (𝟙 SpecQ)) :=
  injective_aj_of_not_isIso_jacobian h.isProper h.smooth h.connected jac
    (not_isIso_jacobian_of_one_le_x0Genus N hg h jac)

/-- **`rank J_0(N)(ℚ) = 0` and `genus X_0(N) ≥ 1` at the thirteen Kenku
levels** (PROVEN, from four leaves — two of them closed here).

The original single sorry node has been split along the seam its own
statement exposes.  `HasRankZeroJacobian` is a conjunction of two
conditions on the Jacobian with wildly different costs, and they are now
separated:

* **The genus half is CLOSED.**  `one_le_x0Genus_of_kenkuLevel` proves
  `1 ≤ x0Genus N` at all thirteen levels by `decide` on the classical
  genus formula, and `numRationalCusps_pos_of_kenkuLevel` likewise
  supplies the base point.  No sorry, no table lookup: the index,
  elliptic points and cusps are computed from `N`.
* **The rank half is Kolyvagin–Logachev** and stays open, alone, in
  `isTorsion_jacobian_of_kenkuLevel`.

**Second round of splitting (2026-07-27).**  Both remaining halves were
each still carrying two unrelated theories, and both have been split
along the seam their own statements expose; `finite_jacobian_of_kenkuLevel`
and `injective_aj_of_one_le_x0Genus` are now PROVEN assemblies rather
than leaves.  The five open leaves under this node, and the single
theory each one needs, are:

| leaf | theory | level-specific? |
|---|---|---|
| `exists_jacobianOf_x0` | Albanese / `Pic⁰` | no |
| `fg_relPoint_of_abelianScheme` | Mordell–Weil | no |
| `isTorsion_jacobian_of_kenkuLevel` | Kolyvagin–Logachev | **yes** |
| `injective_aj_of_not_isIso_jacobian` | Riemann–Roch | no |
| `not_isIso_jacobian_of_one_le_x0Genus` | genus formula | **yes** |

Only two of the five mention `N` at all, and each of the other three is
a named classical theorem stated for an arbitrary object — which is what
makes them dispatchable independently, and reusable by the rest of the
modular-curve subtree. -/
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

/-- **`X_0(N)` exists over `𝔽_ℓ` for `ℓ ∤ N`** (PROVEN 2026-07-27, as the
characteristic-`ℓ` case of `exists_x0Compactification_field`).

The merge flagged in the previous version of this docstring as "available
for the taking" HAS BEEN MADE: this leaf and `exists_x0Compactification`
differed only in the base field, and both are now corollaries of one
statement over an arbitrary base field of characteristic prime to `N`.
`ringChar (ZMod ℓ) = ℓ`, so `hℓN` is literally the characteristic
hypothesis; `hℓ` is needed only to make `ZMod ℓ` a field. -/
theorem exists_x0Compactification_finiteField (N ℓ : ℕ) (hN : 0 < N) (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecF ℓ) (strY : Y ⟶ SpecF ℓ) (j : Y ⟶ X),
      Nonempty (IsX0Compactification N strX strY j) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact exists_x0Compactification_field N hN (ZMod ℓ)
    (by simpa only [ZMod.ringChar_zmod_n] using hℓN)

/-- **`R`-algebra homomorphisms from a finite-type algebra into a FINITE
ring form a finite set** (PROVEN 2026-07-27).

The algebra half of `finite_relPoint_of_x0Compactification_finiteField`,
and the only half of it that is not scheme theory.  A finite-type algebra
is a quotient of `R[x_1, …, x_n]`
(`Algebra.FiniteType.iff_quotient_mvPolynomial''`), so an `R`-algebra map
out of it is pinned by the `n` images of the variables — an injection into
`Fin n → R`, which is finite because `R` is.

Stated for a general finite `R` rather than for `ZMod ℓ`: nothing here
needs `R` to be a field, let alone `ℤ/ℓ`. -/
theorem finite_algHom_of_finiteType (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Finite R] [Algebra.FiniteType R A] : Finite (A →ₐ[R] R) := by
  obtain ⟨n, p, hp⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  have hinj : Function.Injective
      (fun φ : A →ₐ[R] R => fun i : Fin n => φ (p (MvPolynomial.X i))) := by
    intro φ ψ hφψ
    have hcomp : φ.comp p = ψ.comp p :=
      MvPolynomial.algHom_ext fun i => congrFun hφψ i
    refine AlgHom.ext fun a => ?_
    obtain ⟨q, rfl⟩ := hp a
    simpa only [AlgHom.comp_apply] using
      congrArg (fun t : MvPolynomial (Fin n) R →ₐ[R] R => t q) hcomp
  exact Finite.of_injective _ hinj

/-- **The sections of a proper morphism to `Spec R` are cut out by ONE
finite-type `R`-algebra** (sorry node — the scheme-theoretic half of
`finite_relPoint_of_x0Compactification_finiteField`).

TRUE, and this is the standard "finitely many points over a finite field"
argument with the algebra factored out:

1. `IsProper f` gives `UniversallyClosed f`, hence `QuasiCompact f`
   (`AlgebraicGeometry.UniversallyClosed`'s instance at priority `900`),
   and `Spec R` is compact, so `X` is a compact space;
2. so `X.affineCover` has a FINITE subfamily of affine opens
   `U_1, …, U_n` covering `X`, and `LocallyOfFiniteType f` makes each
   `Γ(X, U_i)` a finite-type `R`-algebra;
3. every section `s : Spec R ⟶ X` factors through some `U_i`.  For `R`
   LOCAL this is exactly
   `AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem`: pick
   `U_i` containing the image of the closed point, and the preimage of
   `U_i` is already all of `Spec R`.  For general finite `R`, `Spec R` is
   a finite discrete space (`R` is Artinian) and the argument is run on
   each connected component;
4. take `A := ∏_i Γ(X, U_i)` — a finite product of finite-type algebras
   is finite type — and send `s` to the projection onto the factor of the
   LEAST `i` through which it factors, composed with the induced
   `Γ(X, U_i) →ₐ[R] R`.  That is injective: two sections through the same
   chart differ already on that chart, and two sections through different
   least charts kill different idempotents of the product.

Stated as ONE bundled algebra rather than as a family precisely so that
step 4's product bookkeeping lives inside this leaf and not in the
assembly.  `CommAlgCat.{0} R` is used because an unbundled
`∃ (A : Type) (_ : CommRing A) (_ : Algebra R A), …` cannot be written —
the third binder needs the second as an instance.

REMAINING WORK is entirely items 2–4; nothing modular appears anywhere in
it, and nothing about `R` beyond `Finite R` is used.  The one place a
real gap could hide is step 3 for NON-LOCAL `R`, i.e. composite `ℓ`; the
consumer only ever supplies a prime `ℓ`, but the statement is kept at
`Finite R` because that is the honest hypothesis and the component
argument is routine. -/
theorem exists_finiteType_algHom_injection_of_isProper {R : Type} [CommRing R] [Finite R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    ∃ A : CommAlgCat.{0} R, Algebra.FiniteType R A ∧
      ∃ g : RelPoint f (𝟙 (Spec (CommRingCat.of R))) → (A →ₐ[R] R), Function.Injective g :=
  sorry

/-- **A scheme proper over `Spec R` with `R` finite has finitely many
sections** (PROVEN 2026-07-27, by decomposition).

The assembly of `exists_finiteType_algHom_injection_of_isProper` (scheme
theory) with `finite_algHom_of_finiteType` (algebra).  Stated over a
general finite base ring, since neither half uses anything else.

**Note for the owner of `finite_specialFibre_of_x0NeronDatum`**, whose
docstring records that it is "the SAME mathematics" as
`finite_relPoint_of_x0Compactification_finiteField` but not shareable.
It IS shareable, through this lemma rather than through that one — but it
needs one generalisation, from SECTIONS to `R`-POINTS: what that leaf has
is `d.spX (𝟙 _) (SpecLoc.special toF) rfl :
RelPoint strX' (𝟙 (SpecF ℓ)) ≃ RelPoint xstr (SpecLoc.special toF)`,
whose right-hand side is `Hom_{Spec ℤ_(ℓ)}(Spec 𝔽_ℓ, XZ)`, not a set of
sections.  The general statement — `Finite (RelPoint f g)` for `f` proper
and `g : Spec R ⟶ S` with `R` finite — reduces to this one by base
change along `g`, since `IsProper` is stable under base change
(`AlgebraicGeometry.IsProper.isStableUnderBaseChange`) and sections of
the pullback are exactly the `R`-points of `f` over `g`.  So that leaf
does NOT need "a lemma deducing `IsX0Compactification` from `d`", which
is what its docstring names as the refuting check; it needs a pullback. -/
theorem finite_relPoint_of_isProper {R : Type} [CommRing R] [Finite R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    Finite (RelPoint f (𝟙 (Spec (CommRingCat.of R)))) := by
  obtain ⟨A, hA, g, hg⟩ := exists_finiteType_algHom_injection_of_isProper f
  haveI := hA
  haveI : Finite ((A : Type) →ₐ[R] R) := finite_algHom_of_finiteType R A
  exact Finite.of_injective g hg

/-- **A curve proper over a finite field has finitely many rational
points** (PROVEN 2026-07-27, by decomposition).

TRUE, and it is the one piece of this cluster that is not about modular
curves at all: `strX` is proper, hence of finite type, over
`Spec 𝔽_ℓ`; a finite-type scheme over a FINITE ring has finitely many
sections, because a section is determined by the images of finitely many
generators in a finite ring.  The only property of `IsX0Compactification`
consumed is `isProper` — which is why the proof is a one-line appeal to
`finite_relPoint_of_isProper`, a statement with no modular content at
all.

`hℓ` is `ℓ ≠ 0` rather than `ℓ.Prime` deliberately — that is the honest
minimal hypothesis, since all that is used is that `ZMod ℓ` is finite,
and `ZMod 0 = ℤ` is the only excluded case.

The previous docstring's verdict "IRREDUCIBLE at this pin: there is no
'finite type over a finite ring implies finitely many points' lemma to
appeal to" was right about `Mathlib` and wrong about irreducibility: the
statement splits cleanly into scheme theory
(`exists_finiteType_algHom_injection_of_isProper`, still open) and
algebra (`finite_algHom_of_finiteType`, proven). -/
theorem finite_relPoint_of_x0Compactification_finiteField (N ℓ : ℕ) (hℓ : ℓ ≠ 0)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {j : Y ⟶ X}
    (h : IsX0Compactification N strX strY j) :
    Finite (RelPoint strX (𝟙 (SpecF ℓ))) := by
  haveI : NeZero ℓ := ⟨hℓ⟩
  haveI := h.isProper
  exact finite_relPoint_of_isProper (R := ZMod ℓ) strX

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

**ROUTE AUDIT, 2026-07-27 — the previous verdict "it needs `S_2(Γ_0(N))`,
the Hecke operator `T_ℓ` and the Eichler–Shimura congruence relation,
none of which exist here" is HALF WRONG, and the correction is
actionable.**

Two of the three DO exist in this development, with real definitions and
no `opaque` constant anywhere in them:

* `S_2(Γ_0(N))` is `CuspForm (Gamma0GL N) 2`, with
  `Gamma0GL` at `Fermat/FLT/Modularity/Interface.lean:485`;
* `T_ℓ` is `heckeOp N ℓ : Module.End ℂ (CuspForm (Gamma0GL N) 2)`
  (`Interface.lean:28709`), pinned to the Hecke slash-sum by
  `heckeOp_coe`, so `LinearMap.trace ℂ _ (heckeOp N ℓ)` is a genuine
  complex number and not a placeholder.  `EichlerShimuraPackage`
  (`Interface.lean:28157`) is already the seam this leaf wants.

So the cut is available in principle and is the obvious one:

1. **Eichler–Shimura / Lefschetz** —
   `(Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) : ℤ) = ℓ + 1
   − LinearMap.trace ℂ _ (heckeOp N ℓ)` (needs the trace to be an
   integer, which is the integrality of the Hecke action);
2. **The Magma table** — `(N, ℓ, m) ∈ x0WitnessTable →
   LinearMap.trace ℂ _ (heckeOp N ℓ) = ((ℓ : ℤ) + 1 − m)`, the seven
   rows above.

**WHAT ACTUALLY BLOCKS IT IS A MODULE CYCLE, not missing mathematics.**
`heckeOp` lives in `Modularity/Interface.lean`, and

    Interface → HardlyRamified/ModThree → FreyCurve/MazurTorsion → ModularCurve/X0

so `X0.lean` cannot import it.  (Verified 2026-07-27 by reading the
import lines, not the docstrings: `Interface.lean:302` imports
`ModThree`, `ModThree` imports `MazurTorsion`, and `MazurTorsion:190`
is the ONLY `import` of this module anywhere in the tree.)

**The repair, stated so it can be checked rather than merely believed:**
hoist `Gamma0GL` and the `heckeTransform`/`exists_heckeOpLinear`/`heckeOp`
block out of `Interface.lean` into a small upstream module depending only
on `Mathlib.NumberTheory.ModularForms` — they use nothing else — and
import THAT here.  This note is refuted by exhibiting `heckeOp`, or any
Hecke operator on `CuspForm`, in a module that `X0.lean` may import;
as of 2026-07-27 `grep` over `Fermat/`, `.lake/packages/mathlib/` and
`~/cs/FLT/` finds a Hecke operator on `CuspForm` only in `Interface.lean`.

Do NOT work around this by introducing a local `traceHeckeT : ℕ → ℕ → ℤ`
with no definition: that would make item 2 an equation in an `opaque`
constant and hence unprovable in principle, which is strictly worse than
the present open leaf.

AXIS SEARCHED: the theory axis (which theories are missing) and the
module axis (where they live).  NOT searched: a route that counts
`X_0(N)(𝔽_ℓ)` directly from the seven levels' explicit plane models,
avoiding modular forms entirely — at genus `1`–`5` and `ℓ ≤ 17` that is a
finite computation, and it is the one direction that would make this leaf
independent of `Interface.lean`. -/
theorem card_relPoint_x0_finiteField (N ℓ m : ℕ) (_htable : (N, ℓ, m) ∈ x0WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {j : Y ⟶ X}
    (_h : IsX0Compactification N strX strY j) :
    Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) = m :=
  sorry

/-- **The reduction `X_0(N)_{𝔽_ℓ}` and its Eichler–Shimura point count,
at the nine witness primes** (PROVEN, by decomposition — 2026-07-27).

TRUE: for `ℓ ∤ N` the modular curve has good reduction at `ℓ` and its
special fibre is the coarse space of the same `Γ₀(N)`-problem over
`𝔽_ℓ`; being proper over a finite field it has finitely many rational
points; and Eichler–Shimura evaluates the count as
`ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`.  The nine rows of `x0WitnessTable` are
that formula computed with Magma — except the two added on 2026-07-27,
`(35, 3, 4)` and `(39, 5, 4)`, which were computed with PARI/GP from the
trace form of the cuspidal space (`Tr(T_3 ∣ S_2(Γ_0(35))) = 0` and
`Tr(T_5 ∣ S_2(Γ_0(39))) = 2`).

**The three sentences of that paragraph are three different theories**,
and they are now three leaves rather than one:

* `exists_x0Compactification_finiteField` — the `Γ₀(N)`-moduli problem
  has a smooth compactification over `𝔽_ℓ` (Deligne–Rapoport).  PROVEN
  2026-07-27 as a corollary of `exists_x0Compactification_field`, the
  merge of this leaf with `exists_x0Compactification`; the open content
  moved there, and it is now ONE leaf for both base fields rather than
  two;
* `finite_relPoint_of_x0Compactification_finiteField` — a proper scheme
  over a finite field has finitely many rational points (no modular
  curves involved).  PROVEN 2026-07-27 by decomposition, into
  `finite_algHom_of_finiteType` (algebra, proven) and
  `exists_finiteType_algHom_injection_of_isProper` (scheme theory, open,
  and with no modular content whatsoever);
* `card_relPoint_x0_finiteField` — Eichler–Shimura evaluates the count
  (Hecke operators and `S_2(Γ_0(N))`).  STILL OPEN, and the only one of
  the three that still carries modular content.

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

/-- **The kernel of reduction along a square-zero extension**, as a subtype of
`RelPoint f b`.

`RelPoint.pre (Spec.map φ) rfl` is the reduction map `A(R) ⟶ A(R/I)` read on
relative points; this is its kernel.  It is packaged as a SUBTYPE rather than
as an `AddSubgroup` because the `AddCommGroup` structure on `RelPoint f b` is
`ab.addCommGroup b`, a plain definition depending on the TERM `ab`, so it is
not available to instance synthesis inside a statement — the same reason
`nsmulPoint` exists. -/
abbrev AbelianSchemeStruct.KerPre {A S : Scheme.{u}} {f : A ⟶ S}
    (ab : AbelianSchemeStruct f) {R S' : CommRingCat.{u}} (φ : R ⟶ S')
    (b : Spec R ⟶ S) : Type u :=
  {c : RelPoint f b // RelPoint.pre (Spec.map φ) rfl c = ab.zero (Spec.map φ ≫ b)}

/-- **The kernel of `A(R) ⟶ A(R/I)` along a square-zero extension is an
`R`-MODULE** (sorry node — the whole deformation-theoretic content of the
`q ≠ ℓ` half of `neronKernel_torsionFree`, and now the only thing left in it).

The `R`-action is stated in explicit, typeclass-free form: a scalar map
`smul : R → KerPre → KerPre` together with the four module axioms
`one_smul`, `mul_smul`, `add_smul`, `smul_add`, each read through the
subtype projection and with `ab.add` in place of `+` (the additive
structure on `RelPoint f b` is `ab.addCommGroup b`, which is not an
instance).  `zero_smul` and `smul_zero` are consequences of `add_smul`
and `smul_add` respectively and are therefore not listed.

TRUE, and it is the standard first statement of deformation theory.  For a
SMOOTH `f : A ⟶ S` (here `ab.smooth`) and a square-zero extension
`R ↠ R/I`, the kernel of `A(R) ⟶ A(R/I)` is canonically

    Hom_{R/I}(e^* Ω_{A/S} ⊗ R/I, I)  ≅  Lie(A/S) ⊗ I,

the lifts of a fixed `(R/I)`-point forming a TORSOR under it.  The point
that matters is not the precise identification but its consequence: the
kernel is an `R`-MODULE, not merely an abelian group (the `R`-action factors
through `R/I` because `I² = 0`).

STATE OF THE PIN, checked rather than assumed (2026-07-27), and this is what
makes the leaf expensive:

* Mathlib has the AFFINE-ALGEBRA half in `Mathlib/RingTheory/Smooth/Kaehler.lean`
  — `derivationOfSectionOfKerSqZero` (the difference of two sections of a
  square-zero extension IS a derivation), `retractionOfSectionOfKerSqZero`,
  `retractionKerToTensorEquivSection`, `tensorKaehlerQuotKerSqEquiv`.
* There is **no scheme-level Kähler differential module at all**: nothing
  under `Mathlib/AlgebraicGeometry/` mentions `KaehlerDifferential` or
  `Cotangent` except `Morphisms/FormallyUnramified.lean` and
  `Morphisms/Etale.lean`, and neither builds `Ω_{X/Y}`.
* There is **no scheme-level `FormallySmooth` class** — `Morphisms/Smooth.lean`
  has `Smooth`, `SmoothOfRelativeDimension` and a `smoothLocus`, but formal
  smoothness appears only through `f.stalkMap x` at the ring level, so the
  infinitesimal lifting property is not available as a scheme-level API the
  way `FormallyUnramified.of_hom_ext` is for unramifiedness.
* `Fermat/FLT/GroupScheme/HopfKaehler.lean` has the AFFINE group-scheme
  version; `~/cs/FLT` has no abelian-scheme development at all.

THE ROUTE, recorded so the successor does not have to rediscover it.  The
construction of `smul` needs the trivial square-zero extension, which is the
ring `R ×_{S'} R` (pairs agreeing mod `I`); via `(a, x) ↦ (a, a + x)` it is
`R ⊕ I` with `I² = 0`, and there `μ_r : (a, x) ↦ (a, r x)` IS an `R`-algebra
endomorphism — that endomorphism is the whole source of the scalar action.
To feed a kernel element into it one needs a map `Spec (R ×_{S'} R) ⟶ A`
built from the two `R`-points `c` and `ab.zero b`, i.e. the Ferrand pushout
`Spec R ⊔_{Spec S'} Spec R`, which is ABSENT from the pin.

Two reductions make that affordable, and neither is in the docstring this
replaces:

1. **For an AFFINE target the pushout is free.**  `Hom(Spec D, X)` for
   affine `X` is `Hom(Γ(X), D)` by the `Γ ⊣ Spec` adjunction, so the
   universal property of `R ×_{S'} R` as a fibre product of RINGS is
   already the universal property needed.  No Ferrand theorem is required.
2. **One may assume the kernel element factors through an affine open of
   `A`.**  Equality of morphisms is local on the source, and `Spec S' ⟶ Spec R`
   is a homeomorphism (its ideal is square-zero, hence nilpotent), so
   `hker` forces `c` and `(ab.zero b).1` to have the SAME underlying
   continuous map.  Cover `Spec R` by basic opens `D(g)` whose image under
   that common map lies in an affine chart of `A`; `RelPoint.pre` along
   `Spec R_g ⟶ Spec R` is a group homomorphism (`ab.pre_add`, `ab.pre_zero`),
   localisation is exact so `ker φ_g` is still square-zero, and `q` stays a
   unit.  So the statement descends to the affine case.

THE CHECK THAT WOULD REFUTE THIS VERDICT: a scheme-level `FormallySmooth`
class with the lifting property phrased on `Spec R`-points, in the style of
`FormallyUnramified.of_hom_ext`, would collapse step 2; and any scheme-level
`Ω_{X/Y}` would make the direct torsor argument available. -/
theorem exists_smul_kerPre_of_squareZero {A S : Scheme.{u}} {f : A ⟶ S}
    (ab : AbelianSchemeStruct f) {R S' : CommRingCat.{u}} (φ : R ⟶ S')
    (_hφ : Function.Surjective φ) (_hsq : RingHom.ker φ.hom ^ 2 = ⊥)
    (b : Spec R ⟶ S) :
    ∃ smul : R → ab.KerPre φ b → ab.KerPre φ b,
      (∀ x, (smul 1 x).1 = x.1) ∧
      (∀ (r r' : R) (x : ab.KerPre φ b),
        (smul (r * r') x).1 = (smul r (smul r' x)).1) ∧
      (∀ (r r' : R) (x : ab.KerPre φ b),
        (smul (r + r') x).1 = ab.add (smul r x).1 (smul r' x).1) ∧
      (∀ (r : R) (x y z : ab.KerPre φ b), z.1 = ab.add x.1 y.1 →
        (smul r z).1 = ab.add (smul r x).1 (smul r y).1) :=
  sorry

/-- **The kernel of `A(R) ⟶ A(R/I)` along a SQUARE-ZERO extension has no
`q`-torsion when `q` is a unit of `R`** (PROVEN, over the single leaf
`exists_smul_kerPre_of_squareZero` immediately above).

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

WHAT IS LEFT, and what is now discharged (2026-07-27).  The entire
deformation-theoretic content has been isolated into the single leaf
`exists_smul_kerPre_of_squareZero` above — the `R`-module structure on the
kernel, which is exactly the "check that would refute the verdict" the
previous version of this docstring called for.  Everything else is
GROUP THEORY and is proven here:

* `zero_smul` and `smul_zero` are derived from `add_smul` and `smul_add`
  (`a = a + a` in a group forces `a = 0`), so the leaf does not have to
  state them;
* `smul ((n : ℕ) : R) = n • ·` by induction on `n`, from `one_smul` and
  `add_smul` — this is the bridge between the `R`-action and the `ℕ`-action
  that `nsmulPoint` uses, and it is the only place the two meet;
* with `q = ↑u` a unit, `c = 1 • c = (u⁻¹ * u) • c = u⁻¹ • (q • c) = u⁻¹ • 0 = 0`.

No hypothesis is now unused: `hφ` and `hsq` are consumed by the leaf, `hq`
by the unit inversion, `htors` and `hker` by the computation. -/
theorem eq_zero_of_squareZero_of_isUnit_nsmul
    {A S : Scheme.{u}} {f : A ⟶ S} (ab : AbelianSchemeStruct f) (q : ℕ)
    {R S' : CommRingCat.{u}} (φ : R ⟶ S') (hφ : Function.Surjective φ)
    (hsq : RingHom.ker φ.hom ^ 2 = ⊥) (hq : IsUnit ((q : ℕ) : R))
    {b : Spec R ⟶ S} (c : RelPoint f b)
    (htors : ab.nsmulPoint q c = ab.zero b)
    (hker : RelPoint.pre (Spec.map φ) rfl c = ab.zero (Spec.map φ ≫ b)) :
    c = ab.zero b := by
  letI := ab.addCommGroup b
  obtain ⟨smul, hone, hmul, hadd, hsmul_add⟩ :=
    exists_smul_kerPre_of_squareZero ab φ hφ hsq b
  -- `smul r` kills the zero point: `smul_add` at `x = y = z = 0` gives `a = a + a`.
  have hsmul_zero : ∀ (r : R) (y : ab.KerPre φ b), y.1 = ab.zero b →
      (smul r y).1 = ab.zero b := by
    intro r y hy
    have hz : y.1 = ab.add y.1 y.1 := by rw [hy]; exact (ab.zero_add _).symm
    have h : (smul r y).1 = (smul r y).1 + (smul r y).1 := hsmul_add r y y y hz
    exact left_eq_add.mp h
  -- the `R`-action restricted to `ℕ` is the `ℕ`-action, which is what `nsmulPoint` uses
  have hnat : ∀ (n : ℕ) (y : ab.KerPre φ b), (smul ((n : ℕ) : R) y).1 = n • y.1 := by
    have hzero_smul : ∀ y : ab.KerPre φ b, (smul (0 : R) y).1 = ab.zero b := by
      intro y
      have h := hadd (0 : R) (0 : R) y
      rw [add_zero] at h
      have h' : (smul (0 : R) y).1 = (smul (0 : R) y).1 + (smul (0 : R) y).1 := h
      exact left_eq_add.mp h'
    intro n
    induction n with
    | zero => intro y; rw [Nat.cast_zero, zero_nsmul]; exact hzero_smul y
    | succ k ih =>
      intro y
      have h := hadd ((k : ℕ) : R) 1 y
      rw [hone y, ih y] at h
      rw [Nat.cast_succ, h, succ_nsmul]
      rfl
  -- a `q`-torsion kernel element is `0`, because `q` is invertible in `R`
  have main : ∀ y : ab.KerPre φ b, (smul ((q : ℕ) : R) y).1 = ab.zero b →
      y.1 = ab.zero b := by
    intro y hy
    obtain ⟨u, hu⟩ := hq
    have hux : (smul ((u : R)) y).1 = ab.zero b := by rw [hu]; exact hy
    have h1 : (smul (1 : R) y).1 = y.1 := hone y
    rw [show (1 : R) = ((u⁻¹ : Rˣ) : R) * ((u : Rˣ) : R) from (u.inv_mul).symm, hmul,
      hsmul_zero _ (smul ((u : R)) y) hux] at h1
    exact h1.symm
  exact main ⟨c, hker⟩ (by rw [hnat q ⟨c, hker⟩]; exact htors)

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

/-! ### The Jacobian half: three base-independent statements

`isSmoothProperCurve_of_fibreIdent` is now PROVEN, so two of the three
are still open leaves; both are Grothendieck's relative Picard scheme.

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
`Pic⁰` functor refutes the claim.

That survey was re-run independently on 2026-07-27 over all three trees
and CONFIRMED: `PicardScheme`, `RelativePicard`, `PicardFunctor`, `Pic⁰`
and `relativeJacobian` have zero declaration hits in mathlib and in
`~/cs/FLT`, and in this project only ever occur inside docstrings or on
the axiomatized interfaces named above.

**FAITHFULNESS NOTE on `IsJacobianOf.universal`, recorded because a
future prover is likely to suspect it of being TOO STRONG and to
"repair" it.**  Do not weaken it: the `∃!` is correct as stated, even
though `u` is quantified over ARBITRARY `S`-morphisms `J ⟶ A` rather
than over homomorphisms.  Existence is the Albanese property.  For
uniqueness, note first that the point equation at the base point forces
`u` to send the origin to the origin — `c (𝟙 S) o = ab'.zero` and
`aj (𝟙 S) o = ab.zero` are the two hypotheses of `universal`, and they
say exactly `0_A = 0_J ≫ u`.  A morphism of abelian schemes sending the
origin to the origin is a HOMOMORPHISM — the rigidity theorem (Mumford,
*Abelian Varieties* §4; BLR *Néron Models* 8.4 in the relative case) —
so any two competitors are homomorphisms agreeing on the image of `aj`,
i.e. on the curve, which generates `J` as a group scheme.  Hence they
are equal.

So rigidity is already built INTO this interface, which is worth knowing
before proving anything against it: the interface is not weaker than the
classical Jacobian, and a construction discharging this leaf must supply
the full Albanese property, not merely a representing object. -/
theorem exists_relativeJacobian {C S : Scheme.{0}} (f : C ⟶ S)
    (_hf : IsSmoothProperCurve f) (o : RelPoint f (𝟙 S)) :
    ∃ (J : Scheme.{0}) (jf : J ⟶ S) (ab : AbelianSchemeStruct jf),
      Nonempty (IsJacobianOf f ab o) :=
  sorry

/-- **A fibre of a smooth proper curve is a smooth proper curve**
(PROVEN — Yoneda for the over-category presentation, then base change).

TRUE, and it is pure base change: `IsFibreIdent s f f'` says by Yoneda in
`Over S'` that `f'` is isomorphic to `f ×_S S'`, and `IsProper`,
`SmoothOfRelativeDimension 1` and `GeometricallyConnected` are each
stable under base change and invariant under isomorphism over the base.

It is needed because the special fibre `X'` of a curve model is
constrained by NOTHING but its functor of points — `IsX0CurveModel`
carries `spX`/`spX_nat` and no geometric field about `strX'` — so
`exists_relativeJacobian` cannot be applied to it until its geometry is
recovered from the identification.

**The previous audit here recorded this leaf as IRREDUCIBLE ALONG THE
YONEDA AXIS, and named the check that would refute it: produce the
transport from `IsFibreIdent s f f'` to an isomorphism over `S'` with
`Limits.pullback.snd f s`.  That check has now been run, and the audit
is REFUTED — no general Yoneda-in-`Over S'` machinery was needed.**  The
transport is four elements and three naturality squares, written out
directly:

* `p := e.toEquiv f' (f' ≫ s) rfl ⟨𝟙 A', _⟩ : RelPoint f (f' ≫ s)` — the
  identity of `A'` read through the identification.  It is a map
  `A' ⟶ A` over `s`, so `φ := pullback.lift p.1 f' p.2 : A' ⟶ A ×_S S'`,
  with `φ ≫ snd = f'` by `pullback.lift_snd`.
* `q : RelPoint f' (pullback.snd f s)` — the tautological point
  `⟨pullback.fst f s, pullback.condition⟩` read BACKWARDS through the
  identification.  It is a map `A ×_S S' ⟶ A'` over `S'`.
* `q.1 ≫ p.1 = pullback.fst f s` is naturality along `q.1` at the
  identity point (the only step needing `Category.comp_id` to see
  `RelPoint.pre q.1 _ ⟨𝟙 A', _⟩` as `q`); with `q.1 ≫ f' = snd` it gives
  `q.1 ≫ φ = 𝟙` by `pullback.hom_ext`.
* `φ ≫ q.1 = 𝟙 A'` is naturality along `φ` at `q`, then INJECTIVITY of
  `e.toEquiv f' (f' ≫ s) rfl` — the one place where the identification
  being an `Equiv` rather than a map is used.

So `φ` is an isomorphism with `φ ≫ pullback.snd f s = f'`, and the three
fields follow from mathlib: `IsProper (pullback.snd f s)` and
`GeometricallyConnected (pullback.snd f s)` are instances,
`SmoothOfRelativeDimension 1 (pullback.snd f s)` is
`smoothOfRelativeDimension_isStableUnderBaseChange`, and each property
is `RespectsIso`, so `MorphismProperty.cancel_left_of_respectsIso`
strips the `φ`.

Note what this does NOT close: the identification is transported, not
constructed.  `exists_jacobianFibreIdent` — which produces an
`IsFibreIdent` for the Jacobian — remains a genuine base-change theorem
for `Pic⁰` and is untouched by this. -/
theorem isSmoothProperCurve_of_fibreIdent {S S' A A' : Scheme.{0}} {s : S' ⟶ S}
    {f : A ⟶ S} {f' : A' ⟶ S'} (e : IsFibreIdent s f f')
    (hf : IsSmoothProperCurve f) : IsSmoothProperCurve f' := by
  haveI := hf.isProper
  haveI := hf.smooth
  haveI := hf.connected
  -- the universal point of `A'`: the identity, read through the identification
  obtain ⟨p, hp⟩ : ∃ p : RelPoint f (f' ≫ s),
      e.toEquiv f' (f' ≫ s) rfl ⟨𝟙 A', Category.id_comp f'⟩ = p := ⟨_, rfl⟩
  -- the comparison morphism `A' ⟶ A ×_S S'`
  obtain ⟨φ, hφf, hφs⟩ : ∃ φ : A' ⟶ Limits.pullback f s,
      φ ≫ Limits.pullback.fst f s = p.1 ∧ φ ≫ Limits.pullback.snd f s = f' :=
    ⟨Limits.pullback.lift p.1 f' p.2, Limits.pullback.lift_fst _ _ _,
      Limits.pullback.lift_snd _ _ _⟩
  -- the tautological point of the pullback, read backwards through the identification
  obtain ⟨q, hq⟩ : ∃ q : RelPoint f' (Limits.pullback.snd f s),
      e.toEquiv (Limits.pullback.snd f s) (Limits.pullback.snd f s ≫ s) rfl q
        = ⟨Limits.pullback.fst f s, Limits.pullback.condition⟩ :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  -- naturality along `q.1`, at the identity point: `q.1 ≫ p.1 = fst`
  have key1 : q.1 ≫ p.1 = Limits.pullback.fst f s := by
    have hnat := e.nat q.1 q.2 (rfl : f' ≫ s = f' ≫ s)
      (rfl : Limits.pullback.snd f s ≫ s = Limits.pullback.snd f s ≫ s)
      (⟨𝟙 A', Category.id_comp f'⟩ : RelPoint f' f')
    rw [hp] at hnat
    have hpre : RelPoint.pre q.1 q.2 (⟨𝟙 A', Category.id_comp f'⟩ : RelPoint f' f') = q :=
      Subtype.ext (Category.comp_id q.1)
    rw [hpre, hq] at hnat
    exact (congrArg Subtype.val hnat).symm
  -- naturality along `φ`, at the tautological point: `φ ≫ q.1 = 𝟙`
  have key2 : φ ≫ q.1 = 𝟙 A' := by
    have hnat := e.nat φ hφs
      (rfl : Limits.pullback.snd f s ≫ s = Limits.pullback.snd f s ≫ s)
      (rfl : f' ≫ s = f' ≫ s) q
    rw [hq] at hnat
    have h1 : e.toEquiv f' (f' ≫ s) rfl (RelPoint.pre φ hφs q)
        = e.toEquiv f' (f' ≫ s) rfl ⟨𝟙 A', Category.id_comp f'⟩ := by
      rw [hnat, hp]; exact Subtype.ext hφf
    exact congrArg Subtype.val ((e.toEquiv f' (f' ≫ s) rfl).injective h1)
  have key3 : q.1 ≫ φ = 𝟙 (Limits.pullback f s) := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hφf, key1, Category.id_comp]
    · rw [Category.assoc, hφs, q.2, Category.id_comp]
  haveI : IsIso φ := ⟨⟨q.1, key2, key3⟩⟩
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  rw [← hφs]
  refine ⟨?_, ?_, ?_⟩
  · exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) φ
      (Limits.pullback.snd f s)).mpr inferInstance
  · exact (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1) φ
      (Limits.pullback.snd f s)).mpr (MorphismProperty.pullback_snd f s hf.smooth)
  · exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected) φ
      (Limits.pullback.snd f s)).mpr inferInstance

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
`exists_relativeJacobian`, and with the same refuting check.  A second
survey on 2026-07-27 adds a sharper obstruction, which is worth stating
because it is NOT the same as the missing Picard scheme: the proof
technique this leaf names — "cohomology and base change" — is itself
absent from ALL THREE trees.  `CohomologyAndBaseChange`,
`higherDirectImage`, a derived pushforward and `IsCohomologicallyFlat`
have zero hits in this project, in mathlib at our pin, and in
`~/cs/FLT`.  So this leaf is gated on two independent missing theories,
not one, and mathlib is the blocker for the second.

**A DECOMPOSITION ALONG THE CANONICAL-COMPARISON AXIS WAS SEARCHED AND
REJECTED (2026-07-27).  Stating the axis, since an irreducibility
verdict is only as wide as what its author looked at.**  The cut that
suggests itself is to CONSTRUCT the comparison map rather than posit the
identification, exactly as `fibreIdentPullback` did for the curve:

1. transport `ab` along `fibreIdentPullback s jf` to an
   `AbelianSchemeStruct (Limits.pullback.snd jf s)` — all thirteen
   fields go through, the group data by the equivalence, `pre_add` /
   `pre_zero` by `e.nat`, and `proper` / `smooth` / `connected` by the
   same base-change-plus-iso argument now used in
   `isSmoothProperCurve_of_fibreIdent`;
2. push Abel–Jacobi across `eX` to a natural `c` from `C'` into it,
   whose value at `o'` is the origin — this is precisely where `_ho` is
   consumed;
3. feed `c` to `jac'.universal`, obtaining a CANONICAL
   `u : J' ⟶ J ×_S S'` over `S'`, unique with the `aj` equation.

What is left after that is `IsIso u` plus additivity of `u`, and the
conclusions of this leaf follow formally from those two.  **The reason
this is not a reduction: it replaces ONE blocked obligation with TWO
blocked obligations** — `IsIso u` is still base change for `Pic⁰`, and
additivity of `u` is the rigidity theorem, which is likewise absent
everywhere (see the FAITHFULNESS NOTE on `exists_relativeJacobian`) —
**at a cost of roughly 250 lines of new glue.**  Splitting is worth it
when the halves have disjoint literature AND at least one half becomes
attackable; here neither does.

THE CHECK THAT WOULD REFUTE THIS: formalize the relative rigidity lemma
(a morphism of abelian schemes carrying the origin to the origin is a
homomorphism).  If rigidity lands, additivity of `u` stops being a leaf,
the cut becomes one blocked obligation plus proven glue, and it should
then be made. -/
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
(PROVEN, over the three base-independent statements above — of which
`isSmoothProperCurve_of_fibreIdent` is itself PROVEN, leaving
`exists_relativeJacobian` and `exists_jacobianFibreIdent` as the only
open inputs).

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

/-- **`IsReductionBase` forces `ℓ ≠ 0`** (PROVEN).

`IsReductionBase`'s own docstring derives PRIMALITY of `ℓ` from its two
axioms; this is the weakest consequence of that derivation, and the only
one the finiteness leaf below needs — `ZMod 0 = ℤ` is infinite, and the
whole point of reducing at `ℓ` is that the residue field is FINITE.

The proof deliberately avoids the local-ring route
(`IsReductionBase.isLocalRing`, `IsReductionBase.nontrivialResidue`),
which is declared far below in the `j`-map subsection and so is not in
scope here; and `nontrivialResidue` would not suffice anyway, since
`ZMod 0 = ℤ` is perfectly nontrivial.  Instead: at `ℓ = 0` surjectivity
produces `r` with `toF r = 2`; `ker_eq_nonunits` makes `r` a unit
because `2 ≠ 0`; so `2 = toF r` is a unit of `ℤ`, and it is not. -/
theorem IsReductionBase.ne_zero {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (h : IsReductionBase ℓ R toF) : ℓ ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := h.surjective (2 : ZMod 0)
  have h2 : (2 : ZMod 0) ≠ 0 := by decide
  have hu : IsUnit r := by
    by_contra hnu
    exact h2 (hr ▸ (h.ker_eq_nonunits r).mpr hnu)
  have hz : IsUnit (2 : ℤ) := hr ▸ hu.map toF
  rcases Int.isUnit_iff.mp hz with h1 | h1 <;> omega

/-- **A proper morphism has finitely many `𝔽_ℓ`-points over ANY base
point** (sorry node — general scheme theory, no modular curves anywhere
in it).

TRUE: `f` proper is in particular quasi-compact and locally of finite
type, so `Z` is covered by finitely many affine opens `Spec A_i`, each
`A_i` of finite type over the coordinate ring of an affine open of `S`.
A morphism `Spec 𝔽_ℓ ⟶ Z` has a ONE-POINT image, hence factors through
one of them; and once the base point `g` is fixed, the restriction of
the induced ring map `A_i →+* 𝔽_ℓ` to that coordinate ring is fixed too,
so the map is determined by the images of finitely many generators in a
FINITE ring.  Finitely many opens, finitely many maps each.

`hℓ` is `ℓ ≠ 0` rather than `ℓ.Prime` deliberately — that is the honest
minimal hypothesis, since all that is used is that `ZMod ℓ` is finite,
and `ZMod 0 = ℤ` is the only excluded case.

**Why the generality is load-bearing, and not a gratuitous rewrite of
`finite_relPoint_of_x0Compactification_finiteField`.**  That leaf fixes
the base to `Spec 𝔽_ℓ` and the base point to `𝟙`.  The Néron-datum
consumer below has base `Spec ℤ_(ℓ)` and base point the CLOSED POINT
`SpecLoc.special toF`, so the identity-base-point form does not apply to
it at all — there is no `IsX0Compactification` over `𝔽_ℓ` anywhere in
`IsX0NeronDatum`, only one over `Spec ℤ_(ℓ)`.  Generalising the base
POINT, rather than manufacturing a special-fibre compactification, is
what keeps this question elementary: the alternative route would have
made an elementary finiteness fact depend on Deligne–Rapoport.

**A merge is AVAILABLE and should be taken by whoever holds both.**  This
statement subsumes `finite_relPoint_of_x0Compactification_finiteField`
exactly — that leaf is the case `S = Spec 𝔽_ℓ`, `g = 𝟙`,
`hf = h.isProper`, and its own docstring records that `isProper` is the
only field of `IsX0Compactification` it consumes.  It is not merged here
only because that declaration is another owner's and was in flight when
this was written.

IRREDUCIBLE at this pin, and the axis searched is the SCHEME-THEORETIC
one: `IsProper` is this development's own predicate, and neither the pin,
nor `~/cs/FLT`, nor this tree has a "finite type over a finite ring
implies finitely many sections" lemma.  NOT searched: an affine-local
reduction written directly against `IsAffineOpen.isoSpec`,
`IsOpenImmersion.lift` and the `ΓSpec` adjunction, which is how the
sketch above would actually be mechanised and is the route a successor
should try first. **The check that would refute this verdict**: such a
lemma appearing in `Mathlib` under any name, or the affine-local
reduction going through. -/
theorem finite_relPoint_of_isProper_finiteField {ℓ : ℕ} (_hℓ : ℓ ≠ 0)
    {Z S : Scheme.{0}} {f : Z ⟶ S} (_hf : IsProper f) (g : SpecF ℓ ⟶ S) :
    Finite (RelPoint f g) :=
  sorry

/-- **Abel–Jacobi is injective on relative points at every Kenku level,
over every base and at every test object** (sorry node — Riemann–Roch).

TRUE: at `N ∈ kenkuLevels` the fibres of `X_0(N)` have genus `≥ 1` — the
values, in the order of `kenkuLevels`, are `1, 1, 2, 3, 1, 5, 3, 2, 4, 5,
5`, and the four sieve levels have genus `3, 4, 5, 5` (Magma,
2026-07-27).  For a smooth proper geometrically connected curve of
positive genus carrying a section, `x ↦ [x] − [o]` is a CLOSED IMMERSION
into the Jacobian, hence a monomorphism, hence injective on `T`-points
for every `T`.  Contrapositively: `aj g x = aj g y` with `x ≠ y` makes
`x − y` principal, so some function has a single simple pole and the
curve admits a degree-`1` map to `ℙ¹` — genus `0`.

**Both generalisations are load-bearing**, and neither is available from
the `Spec ℚ`-shaped statements already in this file.  The base `S` is
arbitrary because the consumer below applies this over `Spec ℤ_(ℓ)`; the
test object `T` is arbitrary because the point that matters there is the
CLOSED point `Spec 𝔽_ℓ ⟶ Spec ℤ_(ℓ)`, not `𝟙 S`.  `HasRankZeroJacobian`
carries the `Spec ℚ`, `T = S` case and cannot be specialised to either.

IRREDUCIBLE at this pin, and the axis searched is the GEOMETRIC one:
Riemann–Roch, the genus of a scheme and `Pic⁰` are absent from the pin,
from `~/cs/FLT` and from this development.  NOT searched: an ARITHMETIC
axis, in which `1 ≤ genus` is replaced by a computable invariant of `N`
so that positivity is a `decide` rather than a theorem about the curve.
That is the shape a successor should prefer, and `hN` is written as
`N ∈ kenkuLevels` for exactly that reason: `kenkuLevels` is consumed
ONLY to supply positivity of the genus, so the hypothesis should become
`1 ≤ x0Genus N` the moment such an invariant lands, without touching
anything else here. -/
theorem injective_aj_of_x0Compactification {N : ℕ} (_hN : N ∈ kenkuLevels)
    {XZ YZ JZ S : Scheme.{0}} {xstr : XZ ⟶ S} {ystr : YZ ⟶ S} {jZ : YZ ⟶ XZ}
    {jstrZ : JZ ⟶ S} {abZ : AbelianSchemeStruct jstrZ} {oZ : RelPoint xstr (𝟙 S)}
    (_hmodel : IsX0Compactification N xstr ystr jZ)
    (jacZ : IsJacobianOf xstr abZ oZ) {T : Scheme.{0}} (g : T ⟶ S) :
    Function.Injective (jacZ.aj g) :=
  sorry

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
rational points** (PROVEN 2026-07-27, over
`finite_relPoint_of_isProper_finiteField`).

The whole of the proof is bookkeeping, and that is the point: `d.spX`
identifies `X_0(N)(𝔽_ℓ)` with the `𝔽_ℓ`-points of the integral model
`xstr` taken over the CLOSED POINT `SpecLoc.special toF`, and
`d.model.isProper` makes that model proper over `Spec ℤ_(ℓ)`.  So the
remaining content is entirely the general fact that a proper morphism
has finitely many points valued in a finite field — with no modular
curve, no `N`, and no Néron datum in it — which is exactly what
`finite_relPoint_of_isProper_finiteField` states.

`ℓ ≠ 0` is not a hypothesis because `d.base` supplies it
(`IsReductionBase.ne_zero`, proven above); `IsReductionBase`'s docstring
derives full primality, but only nonvanishing is needed.

**The route deliberately NOT taken.**  An earlier note here proposed
discharging this leaf from
`finite_relPoint_of_x0Compactification_finiteField` by first deducing
`IsX0Compactification N strX' strY' j'` from `d` — that the special
fibre of the model is again a compactification of the `Γ₀(N)`-problem.
That is true and is the natural thing for the integral-model owner to
produce, but it is the WRONG dependency for this leaf: it would make an
elementary finiteness fact rest on Deligne–Rapoport.  Generalising the
base POINT instead keeps the residue elementary, and is what the proof
below does. -/
theorem finite_specialFibre_of_x0NeronDatum
    (d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :
    Finite (RelPoint strX' (𝟙 (SpecF ℓ))) :=
  haveI : Finite (RelPoint xstr (SpecLoc.special toF)) :=
    finite_relPoint_of_isProper_finiteField d.base.ne_zero d.model.isProper
      (SpecLoc.special toF)
  Finite.of_equiv _
    (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm

/-- **Abel–Jacobi is injective on the special fibre** (sorry node —
geometry, UNIVERSAL in `ℓ`).

TRUE: `x ↦ [x] − [o']` is injective on the points of a curve exactly
when the genus is positive, since `[x] − [y] = 0` with `x ≠ y` gives a
degree-`1` map to `ℙ¹`.  `d.model` pins the curve as `X_0(N)`, and
`hlevel` supplies positivity of the genus — the genus values at the
ORIGINAL eleven Kenku levels (this list PREDATES the addition of `35`
and `39` on 2026-07-27 and has not been re-tabulated for them; both have
genus `3`), in the order they then had in `kenkuLevels`, are
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

**PROVEN 2026-07-27, over `injective_aj_of_x0Compactification`.**  The
earlier verdict — "IRREDUCIBLE: the genus of a curve does not exist in
this development in any form" — was right about the mathematics and
wrong about the cut.  What the Néron datum contributes is not genus but
a TRANSPORT: `d.spX_aj` says Abel–Jacobi on the special fibre is
Abel–Jacobi on the integral model read through the equivalences `spX`
and `spJ`, so injectivity here is equivalent to injectivity of
`jacZ.aj` at the closed point `SpecLoc.special toF`.  The genus content
is then a statement about `d.model` alone, with no `𝔽_ℓ` and no datum in
it, and that is where it now lives.

The residue that this factoring exposes, and which is worth saying: the
missing theorem is needed at an ARBITRARY base and an ARBITRARY test
object, not over `Spec ℚ` at the identity.  `HasRankZeroJacobian`
carries only the latter, which is why nothing already in this file could
be specialised to close this leaf. -/
theorem aj_injective_of_x0NeronDatum (hlevel : N ∈ kenkuLevels)
    (d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :
    Function.Injective (jac'.aj (𝟙 (SpecF ℓ))) := by
  intro x y hxy
  have hz : jacZ.aj (SpecLoc.special toF)
        (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _) x)
      = jacZ.aj (SpecLoc.special toF)
        (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _) y) := by
    rw [← d.spX_aj (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _) x,
      ← d.spX_aj (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _) y, hxy]
  exact (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).injective
    (injective_aj_of_x0Compactification hlevel d.model jacZ (SpecLoc.special toF) hz)

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
object.

**Which axes that verdict covers** (2026-07-27, recorded because an
irreducibility verdict is only as wide as the axis its author searched):

* *The geometric axis is EXHAUSTED.*  It is what produced this leaf:
  `finite_specialFibre_of_x0NeronDatum` and
  `aj_injective_of_x0NeronDatum` were split off, and both are now
  PROVEN by reduction to base-general statements.  Nothing geometric
  remains mixed in here.
* *Splitting the two conjuncts into two existentials is BLOCKED* and
  always will be — they have to hold at the SAME `ℓ`, which is the
  whole reason the padding bound is carried here.
* *NOT searched to exhaustion, and the most promising direction: making
  the padding conjunct UNIVERSAL in `ℓ` and lifting it out.*  Sketch:
  `red_aj` plus injectivity of `redJ` (`neronReduction_injective`, which
  needs exactly the `hfin` and `ℓ ≠ 2` already present) plus injectivity
  of the GENERIC Abel–Jacobi makes `redX` injective, so
  `#X_0(N)(ℚ) ≤ #X_0(N)(𝔽_ℓ)`; and the rational cusps give
  `numRationalCusps N ≤ #X_0(N)(ℚ)`.  That would prove
  `numRationalCusps N ≤ #X_0(N)(𝔽_ℓ)` for EVERY good odd `ℓ`, leaving
  this leaf with the intersection bound alone.  It is blocked here only
  because this statement's context carries no `Spec ℚ`-side modular
  structure at all — `IsX0NeronDatum` has an `IsX0Compactification` over
  `Spec ℤ_(ℓ)` and none over `Spec ℚ` — while `exists_rationalCusps` and
  `HasRankZeroJacobian` are both `Spec ℚ`-hardwired.  **The check that
  would refute the blockage**: a general-base form of
  `exists_rationalCusps` (cusps of `IsX0Compactification N xstr ystr jZ`
  over an arbitrary base), together with injectivity of specialisation
  on cusps.  Both are natural products of the integral-model owner, and
  neither needs Eichler–Shimura. -/
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

**Both geometric pieces are now PROVEN** (2026-07-27), and what closing
them showed is that neither was about the Néron datum at all.  Each
reduced, by pure transport along the datum's `spX`/`spJ` equivalences, to
a statement about the INTEGRAL MODEL over `Spec ℤ_(ℓ)` at its closed
point — `finite_relPoint_of_isProper_finiteField` and
`injective_aj_of_x0Compactification` respectively.  The lesson for the
rest of this subsection is that the datum's role is to TRANSPORT
questions from the special fibre to the model, and that the honest
residue of a special-fibre leaf is almost always a base-general
statement with no `𝔽_ℓ` in it.  Note in particular that both residues
need an arbitrary base POINT: the identity-base-point forms already in
this file (`finite_relPoint_of_x0Compactification_finiteField`,
`HasRankZeroJacobian`) cannot be specialised to either.

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
below for what replaced it.

**UPDATE (2026-07-27, later still).**  Both leaves named by the previous
update — `isX0Compactification_data_of_compactificationY0` and
`exists_x0JOpenModel_of_curveModel` — are now PROVEN as assemblies, and
the three that remain in this subsection are strictly smaller:

* `smoothOfRelativeDimension_finite_compl_of_compactificationY0` — the
  relative dimension and the finite cusp locus of `X_0(N)/ℚ`.  Geometric
  connectedness, the third of the old three facts, is now derived from
  these two through `geometricallyConnected_of_isSmoothCompactification`;
* `isX0CoarseModuli_specialOpen_of_curveModel` — good reduction of the
  `Γ₀(N)`-problem at `q ∤ N`, i.e. the special fibre of the integral open
  part is `Y_0(N)/𝔽_q` with finite cusp locus;
* `exists_x0JGenericOpen_of_curveModel` — the generic fibre of the open
  part, and Igusa's integrality of `j` on the model.

What made that possible was closing the YONEDA axis, which the old
verdict on `exists_x0JOpenModel_of_curveModel` itself named as the
cheaper attack it had not tried: `IsFibreIdent.compareIso` turns a fibre
identification of functors of points into an isomorphism with the
pullback, so the special fibre of the open part and its inclusion into
`X'` are now CONSTRUCTED rather than posited, and `spX_j` is a theorem.

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

/-- **The relative dimension and the finite cusp locus of `X_0(N)/ℚ`**
(sorry node — the two of the three facts below that do not follow from
the others).

TRUE for `N ≠ 0`, and both are consequences of `X` being IRREDUCIBLE of
dimension `1`, which it is because `hc` makes `Y` integral
(`isSmoothCurve_of_isCoarseModuliY0`) and `hX.isDominant` makes `Y` dense
in `X`:

* relative dimension `1`.  `hX.smooth` already gives `Smooth strX`; what
  is missing is only the DIMENSION.  The relative dimension of a smooth
  morphism is locally constant on the source, and `X` is connected
  because it contains a dense irreducible open, so the value `1` taken on
  `Y` propagates to all of `X`;
* finiteness of the cusp locus.  `(Set.range hX.j.base)ᶜ` is closed
  (`hX.isOpenImmersion` makes the range open) and is not everything
  (`Y` is nonempty, being integral), so on an irreducible noetherian
  sober space of Krull dimension `≤ 1` it is finite — which is exactly
  `AlgebraicGeometry.finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one`,
  PROVEN in `CurveCompactification.lean`.

IRREDUCIBLE at this pin ALONG THE DIMENSION-THEORY AXIS, and the TWO
CHECKS THAT WOULD REFUTE THAT, each of which closes one bullet:

1. *local constancy of the relative dimension of a smooth morphism.*
   Mathlib's `SmoothOfRelativeDimension n` is a pointwise
   standard-smoothness condition with no comparison between the values at
   two points, and a survey on 2026-07-27 found no
   `relativeDimension`-style invariant anywhere in
   `Mathlib.AlgebraicGeometry`.  Producing "smooth, plus relative
   dimension `n` on a dense open of a connected source, implies relative
   dimension `n`" closes the first bullet;
2. *`topologicalKrullDim X ≤ 1` together with `NoetherianSpace X`* for a
   proper smooth curve over a field.  With those two the second bullet is
   three lines over the already-proven finiteness lemma cited above:
   `QuasiSober` and `T0Space` are instances for schemes, and
   `IrreducibleSpace X` follows from `IsIntegral Y` and `IsDominant hX.j`
   exactly as `connectedSpace_of_denseRange` handles connectedness.

Note the second bullet is the ONLY consumer of the first outside this
statement, so a successor may take them in either order.

Every hypothesis is underscored only because the proof is a `sorry`.
`_hN` is load-bearing for the same reason as in
`isX0Compactification_data_of_compactificationY0` below: at `N = 0` the
coarse space is EMPTY, `isDominant` forces `X` empty, and an empty scheme
has no dimension to speak of — the first conjunct then holds vacuously
but the argument above does not apply. -/
theorem smoothOfRelativeDimension_finite_compl_of_compactificationY0 (N : ℕ) (_hN : N ≠ 0)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (_hc : IsCoarseModuliY0 N strY) (hX : IsCompactificationY0 strY strX) :
    SmoothOfRelativeDimension 1 strX ∧ (Set.range hX.j.base)ᶜ.Finite :=
  sorry

/-- **The three facts about `X_0(N)/ℚ` that `IsCompactificationY0` does
not carry** (PROVEN over one smaller leaf, was a sorry node until
2026-07-27).

TRUE for `N ≠ 0`.  `hc` pins `Y` up to isomorphism as the coarse moduli
space of the `Γ₀(N)`-problem over `ℚ`, which is a geometrically connected
smooth affine curve; `hX` presents `X` as a smooth proper scheme
containing it as a DENSE open (`isDominant`).  Hence `X` is a smooth
proper geometrically connected curve — relative dimension `1` and
geometric connectedness transfer along a dominant open immersion from
`Y` — and its cusp locus, the complement of a dense open in an
irreducible curve, is finite.

`hN` is load-bearing and not decoration: at `N = 0` the `Γ₀(0)`-problem
over `Spec ℚ` is empty (`isEmpty_of_gamma0Datum_zero`), so `Y` may be the
empty scheme, `isDominant` then forces `X` empty, and the empty scheme is
not geometrically connected.  `hc` is load-bearing too — without it `X`
is merely *some* smooth proper scheme with a dense open, which need not
have dimension `1` at all.  Both are now CONSUMED rather than
underscored: `hN` and `hc` feed `isSmoothCurve_of_isCoarseModuliY0`,
whose geometric connectedness of `Y` is what
`geometricallyConnected_of_isSmoothCompactification` transports to `X`.

Stated as the three MISSING facts rather than as
`Nonempty (IsX0Compactification …)` on purpose: four of that structure's
seven fields are already available from `hX` and `hc`, and burying them
in a sorry node would overstate what is open.

**Cut (2026-07-27): the geometric-connectedness third is now PROVEN, and
this statement is an assembly over the other two.**  See
`smoothOfRelativeDimension_finite_compl_of_compactificationY0` below, and
the note there for why that one is not further divisible at this pin. -/
theorem isX0Compactification_data_of_compactificationY0 (N : ℕ) (hN : N ≠ 0)
    {Y X : Scheme.{0}} {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ}
    (hc : IsCoarseModuliY0 N strY) (hX : IsCompactificationY0 strY strX) :
    SmoothOfRelativeDimension 1 strX ∧ GeometricallyConnected strX ∧
      (Set.range hX.j.base)ᶜ.Finite := by
  obtain ⟨hsm, hfin⟩ :=
    smoothOfRelativeDimension_finite_compl_of_compactificationY0 N hN hc hX
  obtain ⟨-, -, -, -, hconnY⟩ := isSmoothCurve_of_isCoarseModuliY0 (Nat.pos_of_ne_zero hN) hc
  haveI := hconnY
  refine ⟨hsm, ?_, hfin⟩
  exact geometricallyConnected_of_isSmoothCompactification
    { comm := hX.«over»
      isOpenImmersion := hX.isOpenImmersion
      isDominant := hX.isDominant
      isProper := hX.proper
      smooth := hsm
      finite_compl := hfin }

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

/-! #### Yoneda in the slice category: a fibre identification IS the pullback

`IsX0CurveModel` pins the special fibre `X'` only through a natural
equivalence of functors of points — `spX` together with `spX_nat` — so a
consumer that needs an actual MORPHISM out of, or into, `X'` cannot read
one off the structure directly.  Recovering one is Yoneda in `Over S'`,
and it is PROVEN here from those two fields alone.

The argument is the usual one, written out rather than invoked through
the `Over`-category API so that no transport is needed at the use sites:
a natural transformation of representable functors is composition with
the image of the IDENTITY (`IsFibreIdent.apply_eq_comp`), and the two
comparison morphisms built from that image are mutually inverse
(`IsFibreIdent.compareIso`).  Only `nat` is ever used; `apply_eq_comp` is
the single place it enters.

This is what
`exists_x0JOpenModel_of_curveModel`'s previous docstring named as the
CHEAPER of the two attacks on it, and what
`isSmoothProperCurve_of_fibreIdent`'s docstring names as the whole of its
residue ("the passage from a natural equivalence of `RelPoint`-functors
to an isomorphism of schemes over `S'`").

**Possible duplication, and it is deliberate rather than overlooked.**
`isSmoothProperCurve_of_fibreIdent` is owned concurrently and asks for
the same transport in the `Arrow.mk f' ≅ Arrow.mk (pullback.snd f s)`
form.  If both land, keep one — this one is a plain `Iso` of schemes plus
the two identities that pin it over the base, which is the shape every
consumer here wants. -/

namespace IsFibreIdent

variable {S S' A A' : Scheme.{0}} {s : S' ⟶ S} {f : A ⟶ S} {f' : A' ⟶ S'}
  (e : IsFibreIdent s f f')

/-- **The universal relative point**: the identity of `A'`, read through
the identification.  Yoneda's lemma, in one line. -/
noncomputable def universalPoint : RelPoint f (f' ≫ s) :=
  e.toEquiv f' (f' ≫ s) rfl ⟨𝟙 A', Category.id_comp f'⟩

/-- **Every value of a fibre identification is composition with the
universal point** (PROVEN).

This is Yoneda for the two representable functors involved, and it is the
ONLY place `nat` is consumed: everything below is a corollary of it
together with the universal property of the pullback. -/
theorem apply_eq_comp {T : Scheme.{0}} (g : T ⟶ S') (g₀ : T ⟶ S) (h : g ≫ s = g₀)
    (x : RelPoint f' g) : (e.toEquiv g g₀ h x).1 = x.1 ≫ e.universalPoint.1 := by
  have hx : RelPoint.pre x.1 x.2 (⟨𝟙 A', Category.id_comp f'⟩ : RelPoint f' f') = x :=
    Subtype.ext (Category.comp_id _)
  have hnat := e.nat x.1 x.2 (rfl : f' ≫ s = f' ≫ s) h
    (⟨𝟙 A', Category.id_comp f'⟩ : RelPoint f' f')
  rw [hx] at hnat
  exact congrArg Subtype.val hnat

/-- The comparison morphism `A' ⟶ A ×_S S'`, built from the universal
point and `f'` by the universal property of the pullback. -/
noncomputable def compareHom : A' ⟶ Limits.pullback f s :=
  Limits.pullback.lift e.universalPoint.1 f' e.universalPoint.2

theorem compareHom_fst : e.compareHom ≫ Limits.pullback.fst f s = e.universalPoint.1 :=
  Limits.pullback.lift_fst _ _ _

theorem compareHom_snd : e.compareHom ≫ Limits.pullback.snd f s = f' :=
  Limits.pullback.lift_snd _ _ _

/-- The inverse comparison, as a relative point of `A'`: the identification
run backwards on the tautological point of the pullback. -/
noncomputable def compareInvPt : RelPoint f' (Limits.pullback.snd f s) :=
  (e.toEquiv (Limits.pullback.snd f s) (Limits.pullback.snd f s ≫ s) rfl).symm
    ⟨Limits.pullback.fst f s, Limits.pullback.condition⟩

/-- The comparison morphism `A ×_S S' ⟶ A'`. -/
noncomputable def compareInv : Limits.pullback f s ⟶ A' := e.compareInvPt.1

theorem compareInv_comp : e.compareInv ≫ f' = Limits.pullback.snd f s := e.compareInvPt.2

theorem compareInv_universalPoint :
    e.compareInv ≫ e.universalPoint.1 = Limits.pullback.fst f s := by
  have h := e.apply_eq_comp (Limits.pullback.snd f s) (Limits.pullback.snd f s ≫ s) rfl
    e.compareInvPt
  rw [show e.toEquiv (Limits.pullback.snd f s) (Limits.pullback.snd f s ≫ s) rfl e.compareInvPt
      = ⟨Limits.pullback.fst f s, Limits.pullback.condition⟩ from
    Equiv.apply_symm_apply _ _] at h
  exact h.symm

theorem compareInv_compareHom : e.compareInv ≫ e.compareHom = 𝟙 (Limits.pullback f s) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, e.compareHom_fst, e.compareInv_universalPoint, Category.id_comp]
  · rw [Category.assoc, e.compareHom_snd, e.compareInv_comp, Category.id_comp]

theorem compareHom_compareInv : e.compareHom ≫ e.compareInv = 𝟙 A' := by
  have hcomp : (e.compareHom ≫ e.compareInv) ≫ f' = f' := by
    rw [Category.assoc, e.compareInv_comp, e.compareHom_snd]
  have key := e.nat e.compareHom e.compareHom_snd
    (rfl : Limits.pullback.snd f s ≫ s = Limits.pullback.snd f s ≫ s) (rfl : f' ≫ s = f' ≫ s)
    e.compareInvPt
  rw [show e.toEquiv (Limits.pullback.snd f s) (Limits.pullback.snd f s ≫ s) rfl e.compareInvPt
      = ⟨Limits.pullback.fst f s, Limits.pullback.condition⟩ from
    Equiv.apply_symm_apply _ _] at key
  have h1 : (⟨e.compareHom ≫ e.compareInv, hcomp⟩ : RelPoint f' f')
      = RelPoint.pre e.compareHom e.compareHom_snd e.compareInvPt := rfl
  have h2 : e.toEquiv f' (f' ≫ s) rfl ⟨e.compareHom ≫ e.compareInv, hcomp⟩
      = e.toEquiv f' (f' ≫ s) rfl ⟨𝟙 A', Category.id_comp f'⟩ := by
    rw [h1, key]
    exact Subtype.ext e.compareHom_fst
  exact congrArg Subtype.val ((e.toEquiv f' (f' ≫ s) rfl).injective h2)

/-- **Yoneda in the slice category** (PROVEN): a fibre identification of
functors of points IS an isomorphism onto the pullback, over `S'`. -/
noncomputable def compareIso : A' ≅ Limits.pullback f s where
  hom := e.compareHom
  inv := e.compareInv
  hom_inv_id := e.compareHom_compareInv
  inv_hom_id := e.compareInv_compareHom

end IsFibreIdent

/-- **The base change of an open immersion of models to a fibre**
(PROVEN).

`𝒴 ⊆ 𝒳` over `S` gives `𝒴 ×_S S' ⊆ 𝒳 ×_S S'`; the morphism is written as
an explicit `Limits.pullback.lift` so that its two projections are
definitional, and identified with `Limits.pullback.map` only where the
open-immersion instance is needed. -/
noncomputable def fibreBaseChangeMap {S S' A B : Scheme.{0}} {f : A ⟶ S} {fY : B ⟶ S}
    {jZ : B ⟶ A} (hjZ : jZ ≫ f = fY) (s : S' ⟶ S) :
    Limits.pullback fY s ⟶ Limits.pullback f s :=
  Limits.pullback.lift (Limits.pullback.fst fY s ≫ jZ) (Limits.pullback.snd fY s)
    (by rw [Category.assoc, hjZ]; exact Limits.pullback.condition)

theorem fibreBaseChangeMap_fst {S S' A B : Scheme.{0}} {f : A ⟶ S} {fY : B ⟶ S}
    {jZ : B ⟶ A} (hjZ : jZ ≫ f = fY) (s : S' ⟶ S) :
    fibreBaseChangeMap hjZ s ≫ Limits.pullback.fst f s
      = Limits.pullback.fst fY s ≫ jZ :=
  Limits.pullback.lift_fst _ _ _

theorem fibreBaseChangeMap_snd {S S' A B : Scheme.{0}} {f : A ⟶ S} {fY : B ⟶ S}
    {jZ : B ⟶ A} (hjZ : jZ ≫ f = fY) (s : S' ⟶ S) :
    fibreBaseChangeMap hjZ s ≫ Limits.pullback.snd f s = Limits.pullback.snd fY s :=
  Limits.pullback.lift_snd _ _ _

theorem isOpenImmersion_fibreBaseChangeMap {S S' A B : Scheme.{0}} {f : A ⟶ S} {fY : B ⟶ S}
    {jZ : B ⟶ A} [IsOpenImmersion jZ] (hjZ : jZ ≫ f = fY) (s : S' ⟶ S) :
    IsOpenImmersion (fibreBaseChangeMap hjZ s) := by
  have hmap : fibreBaseChangeMap hjZ s
      = Limits.pullback.map fY s f s jZ (𝟙 S') (𝟙 S)
          (by rw [Category.comp_id, hjZ]) (by simp) := by
    apply Limits.pullback.hom_ext
    · rw [fibreBaseChangeMap_fst]
      exact (Limits.pullback.lift_fst _ _ _).symm
    · rw [fibreBaseChangeMap_snd, show Limits.pullback.map fY s f s jZ (𝟙 S') (𝟙 S)
            (by rw [Category.comp_id, hjZ]) (by simp) ≫ Limits.pullback.snd f s
            = Limits.pullback.snd fY s ≫ 𝟙 S' from Limits.pullback.lift_snd _ _ _,
        Category.comp_id]
  rw [hmap]
  infer_instance

namespace IsFibreIdent

variable {S S' A A' B : Scheme.{0}} {s : S' ⟶ S} {f : A ⟶ S} {f' : A' ⟶ S'} {fY : B ⟶ S}
  {jZ : B ⟶ A} (e : IsFibreIdent s f f') (hjZ : jZ ≫ f = fY)

/-- **The inclusion of the open part into the fibre `A'`, reconstructed
from the identification** (PROVEN).

`A'` is pinned only as a functor, so this cannot be written down directly;
it is `e.toEquiv` run BACKWARDS on the tautological open point of
`B ×_S S'`.  Everything the consumers need about it —
`openSection_comp`, `apply_openSection`, `isOpenImmersion_openSection` —
follows from `apply_eq_comp` and the pullback's universal property. -/
noncomputable def openSection : Limits.pullback fY s ⟶ A' :=
  ((e.toEquiv (Limits.pullback.snd fY s) (Limits.pullback.snd fY s ≫ s) rfl).symm
    ⟨Limits.pullback.fst fY s ≫ jZ, by
      rw [Category.assoc, hjZ]; exact Limits.pullback.condition⟩).1

theorem openSection_comp : openSection e hjZ ≫ f' = Limits.pullback.snd fY s :=
  ((e.toEquiv (Limits.pullback.snd fY s) (Limits.pullback.snd fY s ≫ s) rfl).symm
    ⟨Limits.pullback.fst fY s ≫ jZ, by
      rw [Category.assoc, hjZ]; exact Limits.pullback.condition⟩).2

theorem openSection_universalPoint :
    openSection e hjZ ≫ e.universalPoint.1 = Limits.pullback.fst fY s ≫ jZ := by
  have h := e.apply_eq_comp (Limits.pullback.snd fY s) (Limits.pullback.snd fY s ≫ s) rfl
    ((e.toEquiv (Limits.pullback.snd fY s) (Limits.pullback.snd fY s ≫ s) rfl).symm
      ⟨Limits.pullback.fst fY s ≫ jZ, by
        rw [Category.assoc, hjZ]; exact Limits.pullback.condition⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- **The identification carries the open immersion** (PROVEN) — this is
`spX_j`, in the generality in which it is true. -/
theorem apply_openSection {T : Scheme.{0}} (g : T ⟶ S') (g₀ : T ⟶ S) (h : g ≫ s = g₀)
    (y : RelPoint (Limits.pullback.snd fY s) g) :
    (e.toEquiv g g₀ h ⟨y.1 ≫ openSection e hjZ, by
        rw [Category.assoc, openSection_comp e hjZ, y.2]⟩).1
      = (y.1 ≫ Limits.pullback.fst fY s) ≫ jZ := by
  rw [e.apply_eq_comp, Category.assoc, openSection_universalPoint e hjZ, Category.assoc]

/-- **The reconstructed inclusion is an open immersion** (PROVEN): it is
the base change of `jZ` composed with `compareIso.inv`. -/
theorem isOpenImmersion_openSection [IsOpenImmersion jZ] :
    IsOpenImmersion (openSection e hjZ) := by
  have hfac : openSection e hjZ ≫ e.compareHom = fibreBaseChangeMap hjZ s := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, e.compareHom_fst, openSection_universalPoint e hjZ,
        fibreBaseChangeMap_fst]
    · rw [Category.assoc, e.compareHom_snd, openSection_comp e hjZ, fibreBaseChangeMap_snd]
  have h : openSection e hjZ = fibreBaseChangeMap hjZ s ≫ e.compareInv := by
    rw [← hfac, Category.assoc, e.compareHom_compareInv, Category.comp_id]
  haveI := isOpenImmersion_fibreBaseChangeMap (f := f) hjZ s
  haveI : IsIso e.compareInv := e.compareIso.isIso_inv
  rw [h]
  infer_instance

end IsFibreIdent

/-! #### The two residues of the open-and-`j` half

With the Yoneda reconstruction above, the first bullet of the old
`exists_x0JOpenModel_of_curveModel` — "the special fibre of the open part
exists, and the special identification carries the open immersion" — is
no longer open.  `Y'` is `𝒴 ×_{ℤ_(q)} 𝔽_q`, its inclusion into `X'` is
`IsX0CurveModel.specialOpen` below, `spY`/`spY_nat` are
`fibreIdentPullback`, and `spX_j` is `IsFibreIdent.apply_openSection`.
The geometry of `X'` — proper, smooth of relative dimension `1`,
geometrically connected — is `isSmoothProperCurve_of_fibreIdent` applied
to `cm.spX`, so it costs no leaf of this subsection either.

What is genuinely left splits along the two fibres, and the split is
along the modular/formal line rather than along the generic/special one:

* `isX0CoarseModuli_specialOpen_of_curveModel` — the special fibre of the
  moduli space over `ℤ_(q)` is the moduli space over `𝔽_q`, and the cusp
  locus stays finite.  This is good reduction of the `Γ₀(N)`-problem at
  `q ∤ N` (Deligne–Rapoport III; Katz–Mazur 8.6), and it is modular;
* `exists_x0JGenericOpen_of_curveModel` — the GENERIC fibre of the open
  part is `Y` compatibly with `cm.genX`, and `j` is a regular function on
  `𝒴` valued in `ℤ_(q)` on integral sections.  The second half is Igusa's
  good-reduction statement for the `j`-line.

Note what is NOT assumed, exactly as before the cut: `q` is not required
to be odd.  Mazur needs `q ≠ 2` for the FORMAL IMMERSION, which is a
different statement and is not part of this module. -/

/-- **The special fibre of the open part of a curve model, included in
`X'`** — the Yoneda reconstruction, specialised. -/
noncomputable def IsX0CurveModel.specialOpen {N q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    Limits.pullback ystr (SpecLoc.special toF) ⟶ X' :=
  IsFibreIdent.openSection ⟨cm.spX, cm.spX_nat⟩ cm.model.comm

/-- `specialOpen` is a morphism over `𝔽_q` (PROVEN). -/
theorem IsX0CurveModel.specialOpen_comm {N q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    cm.specialOpen ≫ strX' = Limits.pullback.snd ystr (SpecLoc.special toF) :=
  IsFibreIdent.openSection_comp
    (⟨cm.spX, cm.spX_nat⟩ : IsFibreIdent (SpecLoc.special toF) xstr strX') cm.model.comm

/-- `specialOpen` is an OPEN IMMERSION (PROVEN) — it is the base change of
`jZ` composed with `IsFibreIdent.compareIso.inv`. -/
theorem IsX0CurveModel.isOpenImmersion_specialOpen {N q : ℕ} {R : Subring ℚ}
    {toF : R →+* ZMod q} {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    IsOpenImmersion cm.specialOpen := by
  haveI : IsOpenImmersion jZ := cm.model.isOpen
  exact IsFibreIdent.isOpenImmersion_openSection
    (⟨cm.spX, cm.spX_nat⟩ : IsFibreIdent (SpecLoc.special toF) xstr strX') cm.model.comm

/-- **`spX_j` for the reconstructed inclusion** (PROVEN): the special
identification of curves carries `specialOpen` to `jZ`. -/
theorem IsX0CurveModel.spX_specialOpen {N q : ℕ} {R : Subring ℚ} {toF : R →+* ZMod q}
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ)
    {T : Scheme.{0}} (g : T ⟶ SpecF q) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀)
    (y' : RelPoint (Limits.pullback.snd ystr (SpecLoc.special toF)) g)
    (hcomm : cm.specialOpen ≫ strX' = Limits.pullback.snd ystr (SpecLoc.special toF)) :
    cm.spX g g₀ h (relSectionAlong cm.specialOpen hcomm y')
      = relSectionAlong jZ cm.model.comm
          ((fibreIdentPullback (SpecLoc.special toF) ystr).toEquiv g g₀ h y') :=
  Subtype.ext (IsFibreIdent.apply_openSection
    (⟨cm.spX, cm.spX_nat⟩ : IsFibreIdent (SpecLoc.special toF) xstr strX')
    cm.model.comm g g₀ h y')

/-- **The special fibre of `Y_0(N)`'s integral model is `Y_0(N)` over
`𝔽_q`, with finite cusp locus** (sorry node — good reduction of the
`Γ₀(N)`-moduli problem).

TRUE for `q ∤ N`: this is exactly the statement that the Deligne–Rapoport
model has good reduction at a prime not dividing the level — the special
fibre of the coarse space represents the `Γ₀(N)`-problem in
characteristic `q`, and the cusps are a finite étale `ℤ_(q)`-scheme, so
they stay finite in the fibre (Deligne–Rapoport III.1 and VI.6.7;
Katz–Mazur 8.6.8, the `[Γ₀(N)]`-case of "the moduli problem is relatively
representable and étale over `ℤ[1/N]`").

Stated as the two facts the special fibre's `IsX0Compactification`
actually lacks, not as `Nonempty (IsX0Compactification …)`: the other
five fields are PROVEN above and burying them here would overstate what
is open.  `comm` is `IsFibreIdent.openSection_comp`, `isOpen` is
`IsFibreIdent.isOpenImmersion_openSection`, and `isProper`, `smooth`,
`connected` are `isSmoothProperCurve_of_fibreIdent` applied to `cm.spX`.

The conclusion is written `∃ _ : IsCoarseModuliY0 …, …` rather than with
`∧` because `IsCoarseModuliY0` is DATA (a `Type 1`, carrying `classify`
and the initiality clause), not a proposition.  The consumer's own goal
is a `Prop`, so eliminating this existential to build the coarse-space
field of an `IsX0Compactification` is legitimate.

Every hypothesis is underscored only because the proof is a `sorry`;
`_hqN` is the load-bearing one — at `q ∣ N` the model is not smooth and
the conclusion is FALSE, which is the whole reason `q ∤ N` runs through
this subsection. -/
theorem isX0CoarseModuli_specialOpen_of_curveModel (N q : ℕ) (_hN : N ≠ 0) (_hq : q.Prime)
    (_hqN : ¬ q ∣ N) (R : Subring ℚ) (toF : R →+* ZMod q)
    (_hbase : IsReductionBase q R toF)
    {X X' XZ YZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    ∃ _ : IsCoarseModuliY0 N (Limits.pullback.snd ystr (SpecLoc.special toF)),
      (Set.range cm.specialOpen.base)ᶜ.Finite :=
  sorry

/-- **The GENERIC fibre of the open part, and the integral `j`-invariant.**

`IsX0JOpenModel` minus everything the Yoneda reconstruction supplies:
what is left is the generic side — `genY`, `genY_nat`, `genX_j` — and the
`j`-invariant on integral points with its three compatibilities.  It is
stated over `cm` for the same reason `IsX0JOpenModel` is, so that it
cannot be satisfied by a *different* model, and it deliberately does not
mention the special fibre at all: nothing here depends on `X'`, so the
leaf below can be attacked without the moduli input of
`isX0CoarseModuli_specialOpen_of_curveModel`.

The naturality fields are preserved VERBATIM from `IsX0JOpenModel`.
Without them these are bare bijections of point sets and a point-set
relabelling preserving the open part satisfies everything else while
changing nothing Yoneda can see — i.e. the leaf would become false in the
only direction that matters. -/
structure IsX0JGenericOpen (N q : ℕ) (R : Subring ℚ) (toF : R →+* ZMod q)
    {Y X X' XZ YZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {hc : IsCoarseModuliY0 N strY}
    (hX : IsCompactificationY0 strY strX)
    (hj : IsJMapOn N hc)
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) where
  /-- the generic fibre of the open model is `Y`, functorially -/
  genY : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strY g ≃ RelPoint ystr g₀
  /-- naturality of the generic identification of open parts -/
  genY_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strY g),
    genY g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genY g g₀ h₀ x)
  /-- the generic identification carries the open immersion -/
  genX_j : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (y : RelPoint strY g),
    cm.genX g g₀ h (relSectionAlong hX.j hX.over y)
      = relSectionAlong jZ cm.model.comm (genY g g₀ h y)
  /-- the `j`-invariant of an integral point, INTEGRAL -/
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

/-- **The generic open part and the integral `j` exist over a given curve
model** (sorry node — Igusa, plus the generic fibre of the open part).

TRUE for `q ∤ N`.  Two statements, kept in one leaf because both are read
off the SAME model and `jm_gen` ties them together:

* the generic fibre of `𝒴` is `Y` compatibly with `cm.genX` and the two
  open immersions.  Note this is NOT formal in the way the special side
  turned out to be: `cm` identifies the generic fibre of the PROPER model
  with `X`, and there is nothing in `IsX0CurveModel` forcing the model's
  open part to restrict to the given `Y ⊆ X` rather than to some other
  dense open.  It is true because both are the complement of the cusp
  locus, which is a statement about the model;
* `j` is a regular function on `𝒴`, valued in `ℤ_(q)` on integral
  sections.  This is Igusa's good-reduction statement for the `j`-line at
  `q ∤ N`, and it is the only genuinely modular input left on the generic
  side.

IRREDUCIBLE at this pin ALONG THE MODULI AXIS, and the CHECK THAT WOULD
REFUTE THAT: the `j`-half needs the `j`-line over `ℤ_(q)`, and the survey
recorded in `exists_x0CurveModel_of_base` found no integral model of a
modular curve in mathlib, `~/cs/FLT` or this project.  Producing one
refutes it.  **The Yoneda axis, which the previous version of this
verdict named as the cheaper attack, is now CLOSED** — see
`IsFibreIdent.compareIso` — and the part of the old leaf it governed is
proven, which is why this statement is strictly smaller than the one it
replaces. -/
theorem exists_x0JGenericOpen_of_curveModel (N q : ℕ) (_hN : N ≠ 0) (_hq : q.Prime)
    (_hqN : ¬ q ∣ N) (R : Subring ℚ) (toF : R →+* ZMod q)
    (_hbase : IsReductionBase q R toF)
    {Y X X' XZ YZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {hc : IsCoarseModuliY0 N strY}
    (hX : IsCompactificationY0 strY strX) (hj : IsJMapOn N hc)
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    Nonempty (IsX0JGenericOpen N q R toF hX hj cm) :=
  sorry

/-- **The open-part fibres and the integral `j` exist over a given curve
model** (PROVEN over two smaller leaves, was a sorry node until
2026-07-27).

The proof is the assembly, and everything in it that is not one of the
two leaves is proven in this subsection:

1. `Y'` is not posited — it is `𝒴 ×_{ℤ_(q)} 𝔽_q`, and `spY`/`spY_nat` are
   `fibreIdentPullback`, exactly as `exists_x0CurveModel_of_base` already
   does for `X'`;
2. `jY'` is not posited either — `IsX0CurveModel.specialOpen`
   reconstructs it from `cm.spX` by Yoneda in the slice category
   (`IsFibreIdent.compareIso`), and `comm`, `isOpen` and `spX_j` are then
   theorems (`openSection_comp`, `isOpenImmersion_openSection`,
   `apply_openSection`);
3. the geometry of `X'` — proper, smooth of relative dimension `1`,
   geometrically connected — is `isSmoothProperCurve_of_fibreIdent`
   applied to `cm.spX` and `cm.model`, so it is charged to the Jacobian
   half's leaf rather than to this one;
4. `isX0CoarseModuli_specialOpen_of_curveModel` supplies the two
   remaining fields of `hX'`;
5. `exists_x0JGenericOpen_of_curveModel` supplies the generic side and
   the integral `j`.

The old *"IRREDUCIBLE at this pin ALONG THE MODULI AXIS"* verdict on this
statement is retired in the same way its predecessor's was: the axis it
did not search is named in its own last sentence — the Yoneda
reconstruction — and searching it turned the whole special-fibre bullet
into theorems. -/
theorem exists_x0JOpenModel_of_curveModel (N q : ℕ) (hN : N ≠ 0) (hq : q.Prime)
    (hqN : ¬ q ∣ N) (R : Subring ℚ) (toF : R →+* ZMod q)
    (hbase : IsReductionBase q R toF)
    {Y X X' XZ YZ : Scheme.{0}}
    {strY : Y ⟶ SpecQ} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF q}
    {hc : IsCoarseModuliY0 N strY}
    (hX : IsCompactificationY0 strY strX) (hj : IsJMapOn N hc)
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (cm : IsX0CurveModel N q R toF (strX := strX) (strX' := strX') xstr ystr jZ) :
    ∃ (Y' : Scheme.{0}) (strY' : Y' ⟶ SpecF q) (jY' : Y' ⟶ X')
      (hX' : IsX0Compactification N strX' strY' jY'),
      Nonempty (IsX0JOpenModel N q R toF hX hX' hj cm) := by
  have hspc : IsSmoothProperCurve strX' :=
    isSmoothProperCurve_of_fibreIdent
      (⟨cm.spX, cm.spX_nat⟩ : IsFibreIdent (SpecLoc.special toF) xstr strX')
      ⟨cm.model.isProper, cm.model.smooth, cm.model.connected⟩
  obtain ⟨hcoarse, hfin⟩ :=
    isX0CoarseModuli_specialOpen_of_curveModel N q hN hq hqN R toF hbase cm
  obtain ⟨go⟩ := exists_x0JGenericOpen_of_curveModel N q hN hq hqN R toF hbase hX hj cm
  refine ⟨Limits.pullback ystr (SpecLoc.special toF),
    Limits.pullback.snd ystr (SpecLoc.special toF), cm.specialOpen,
    { comm := cm.specialOpen_comm
      coarse := hcoarse
      isOpen := cm.isOpenImmersion_specialOpen
      isProper := hspc.isProper
      smooth := hspc.smooth
      connected := hspc.connected
      finite_compl := hfin }, ⟨?_⟩⟩
  exact
    { genY := go.genY
      spY := (fibreIdentPullback (SpecLoc.special toF) ystr).toEquiv
      genY_nat := go.genY_nat
      spY_nat := (fibreIdentPullback (SpecLoc.special toF) ystr).nat
      genX_j := go.genX_j
      spX_j := fun g g₀ h y' => cm.spX_specialOpen g g₀ h y' cm.specialOpen_comm
      jmZ := go.jmZ
      jmGen := go.jmGen
      jmSp := go.jmSp
      jmGen_pre := go.jmGen_pre
      jmSp_pre := go.jmSp_pre
      jm_gen := go.jm_gen }

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
two needs precisely the two statements below: the special fibre of the
smooth model IS `X_0(N)` over `𝔽_ℓ` (good reduction), and any two
`X_0(N)`'s over `𝔽_ℓ` have the same rational points (uniqueness).
Neither is formal-group theory, and neither was previously stated
anywhere.

**Both are now PROVEN from strictly smaller leaves** (2026-07-27), and
the cut is worth describing because it separates three things that were
tangled together in the original two-leaf statement.

*Rigidity, and it is pure category theory.*  `IsCoarseModuliY0` is an
initiality property, so any two coarse moduli spaces for `Γ₀(N)` over a
common base are isomorphic over it — that is
`IsCoarseModuliY0.exists_inverse`, PROVEN, and it is the first half of
the uniqueness statement.  Dually, `d.spX` *together with* `d.spX_nat` is
a natural isomorphism of functors of points over `𝔽_ℓ`, so Yoneda
identifies `X'` with the honest base change `𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ` — that is
`exists_inverse_pullbackSpecial`, PROVEN, and it is exactly the step the
docstring of `exists_isX0Compactification_specialFibre` says naturality
is load-bearing for.  Neither needs any geometry.

*Transport, and it is bookkeeping.*  `IsX0Compactification.ofInverse`
moves the structure along an isomorphism over the base
(`RespectsIso` for `IsProper`, `SmoothOfRelativeDimension 1` and
`GeometricallyConnected`; the cusp locus moves as a preimage), and
`relPointEquivOfInverse` moves relative points.  Both PROVEN.

*Geometry, and it is all that is left.*  Three leaves, each a single
classical fact rather than a bundle:

1. `nonempty_isCoarseModuliY0_pullbackSpecial` — the coarse moduli space
   of `Γ₀(N)` base-changes to the special fibre at `ℓ ∤ N`.  This is
   where good reduction actually lives, and where `_hℓN` is consumed;
2. `finite_compl_pullbackSpecial` — the cusp locus of the special fibre
   is still finite;
3. `exists_inverse_of_isX0Compactification` — a smooth proper
   geometrically connected curve over a FIELD is determined by a dense
   open, by closure of the graph in `X₁ ×_k X₂`.

Everything else in the base change — properness, smoothness of relative
dimension `1`, geometric connectedness, openness of the immersion — is
supplied by `Mathlib`'s base-change instances and needs no leaf. -/

section SpecialFibre

open _root_.CategoryTheory.Limits

/-- **A pair of mutually inverse morphisms over the base transports
relative points** (PROVEN).

Stated with an explicit inverse pair rather than with `IsIso` because
that is the form both consumers below produce: the initiality argument
of `IsCoarseModuliY0.exists_inverse` and the Yoneda argument of
`exists_inverse_pullbackSpecial` each manufacture the two morphisms and
the two composites separately, and never an `Iso` bundle. -/
def relPointEquivOfInverse {X₁ X₂ S T : Scheme.{u}} {strX₁ : X₁ ⟶ S} {strX₂ : X₂ ⟶ S}
    {g : T ⟶ S} {w : X₁ ⟶ X₂} {w' : X₂ ⟶ X₁}
    (hw : w ≫ strX₂ = strX₁) (hw' : w' ≫ strX₁ = strX₂)
    (hww' : w ≫ w' = 𝟙 X₁) (hw'w : w' ≫ w = 𝟙 X₂) :
    RelPoint strX₁ g ≃ RelPoint strX₂ g where
  toFun x := ⟨x.1 ≫ w, by rw [Category.assoc, hw]; exact x.2⟩
  invFun y := ⟨y.1 ≫ w', by rw [Category.assoc, hw']; exact y.2⟩
  left_inv x := Subtype.ext
    (show (x.1 ≫ w) ≫ w' = x.1 by rw [Category.assoc, hww', Category.comp_id])
  right_inv y := Subtype.ext
    (show (y.1 ≫ w') ≫ w = y.1 by rw [Category.assoc, hw'w, Category.comp_id])

/-- **Any two coarse moduli spaces for the `Γ₀(N)`-problem over a common
base are isomorphic over it** (PROVEN).

Pure initiality, and no geometry: `h₁.universal` applied to
`(Y₂, h₂.classify)` gives `u : Y₁ ⟶ Y₂` over the base, `h₂.universal`
applied to `(Y₁, h₁.classify)` gives `v : Y₂ ⟶ Y₁`, and both `u ≫ v` and
`𝟙 Y₁` satisfy the property that `h₁.universal` applied to
`(Y₁, h₁.classify)` says EXACTLY ONE morphism satisfies — so they are
equal, and symmetrically.

This is what the docstring of `IsCoarseModuliY0` means by "initiality
already determines `(Y, classify)` up to unique isomorphism", and what
the docstring of `Y0HasNoRationalPoint` appeals to when it says that
quantifying over all coarse moduli spaces is a statement about the
genuine `Y_0(N)`.  Both were assertions in prose until now.

Deliberately stated with a raw inverse pair rather than as `X₁ ≅ X₂`, for
the reason recorded at `relPointEquivOfInverse`. -/
theorem IsCoarseModuliY0.exists_inverse {N : ℕ} {Y₁ Y₂ S : Scheme.{u}}
    {str₁ : Y₁ ⟶ S} {str₂ : Y₂ ⟶ S}
    (h₁ : IsCoarseModuliY0 N str₁) (h₂ : IsCoarseModuliY0 N str₂) :
    ∃ (u : Y₁ ⟶ Y₂) (v : Y₂ ⟶ Y₁),
      u ≫ str₂ = str₁ ∧ v ≫ str₁ = str₂ ∧ u ≫ v = 𝟙 Y₁ ∧ v ≫ u = 𝟙 Y₂ := by
  obtain ⟨u, ⟨hu, hucl⟩, -⟩ := h₁.universal str₂ h₂.classify h₂.classify_natural
  obtain ⟨v, ⟨hv, hvcl⟩, -⟩ := h₂.universal str₁ h₁.classify h₁.classify_natural
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · obtain ⟨w, -, hwuniq⟩ := h₁.universal str₁ h₁.classify h₁.classify_natural
    refine (hwuniq (u ≫ v) ⟨?_, ?_⟩).trans (hwuniq (𝟙 Y₁) ⟨Category.id_comp _, ?_⟩).symm
    · rw [Category.assoc, hv, hu]
    · intro T g dd
      conv_lhs => rw [hvcl g dd, hucl g dd]
      exact Category.assoc _ _ _
    · intro T g dd
      exact (Category.comp_id _).symm
  · obtain ⟨w, -, hwuniq⟩ := h₂.universal str₂ h₂.classify h₂.classify_natural
    refine (hwuniq (v ≫ u) ⟨?_, ?_⟩).trans (hwuniq (𝟙 Y₂) ⟨Category.id_comp _, ?_⟩).symm
    · rw [Category.assoc, hu, hv]
    · intro T g dd
      conv_lhs => rw [hucl g dd, hvcl g dd]
      exact Category.assoc _ _ _
    · intro T g dd
      exact (Category.comp_id _).symm

/-- **`IsX0Compactification` transports along an isomorphism of the
compactification over the base** (PROVEN).

Every field moves for a standard reason and none of them needs a leaf:
`coarse` does not mention `X` at all; `isOpen` because an isomorphism is
an open immersion and open immersions compose; `isProper`, `smooth` and
`connected` because all three properties are `RespectsIso` in `Mathlib`
(`IsProper` directly, `SmoothOfRelativeDimension 1` through
`HasRingHomProperty`, `GeometricallyConnected` through
`IsStableUnderBaseChange`); and `finite_compl` because the cusp locus of
the target is the PREIMAGE of the cusp locus of the source under the
inverse, which is injective.

The preimage formulation is the one that works: pushing the complement
forward as an image would need `w.base` surjective as a separate step,
whereas `Set.Finite.preimage` needs only injectivity, which the inverse
pair hands over directly. -/
def IsX0Compactification.ofInverse {N : ℕ} {X₁ X₂ Y S : Scheme.{0}}
    {strX₁ : X₁ ⟶ S} {strX₂ : X₂ ⟶ S} {strY : Y ⟶ S} {j : Y ⟶ X₁}
    (h : IsX0Compactification N strX₁ strY j)
    {w : X₁ ⟶ X₂} {w' : X₂ ⟶ X₁} (hw : w ≫ strX₂ = strX₁) (hw' : w' ≫ strX₁ = strX₂)
    (hww' : w ≫ w' = 𝟙 X₁) (hw'w : w' ≫ w = 𝟙 X₂) :
    IsX0Compactification N strX₂ strY (j ≫ w) := by
  haveI hiso : IsIso w := ⟨w', hww', hw'w⟩
  haveI hiso' : IsIso w' := ⟨w, hw'w, hww'⟩
  haveI := h.isOpen
  have hbase : ∀ x, w'.base (w.base x) = x := fun x =>
    congrArg (fun f : X₁ ⟶ X₁ => f.base x) hww'
  have hbase' : ∀ x, w.base (w'.base x) = x := fun x =>
    congrArg (fun f : X₂ ⟶ X₂ => f.base x) hw'w
  have hcomp : ∀ y, (j ≫ w).base y = w.base (j.base y) := fun _ => rfl
  refine ⟨?_, h.coarse, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hw, h.comm]
  · rw [← hw']
    exact MorphismProperty.RespectsIso.precomp (@IsProper) w' strX₁ h.isProper
  · rw [← hw']
    exact MorphismProperty.RespectsIso.precomp (@SmoothOfRelativeDimension 1) w' strX₁ h.smooth
  · rw [← hw']
    exact MorphismProperty.RespectsIso.precomp (@GeometricallyConnected) w' strX₁ h.connected
  · have hset : (Set.range (j ≫ w).base)ᶜ = w'.base ⁻¹' (Set.range j.base)ᶜ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_range, not_exists]
      constructor
      · intro hx y hy
        exact hx y (by rw [hcomp, hy, hbase'])
      · intro hx y hy
        rw [hcomp] at hy
        exact hx y (by rw [← hy, hbase])
    rw [hset]
    exact Set.Finite.preimage
      (Set.injOn_of_injective (Function.LeftInverse.injective hbase')) h.finite_compl

/-- **`X'` really IS the special fibre of the integral model** (PROVEN —
Yoneda, and this is what `spX_nat` is for).

`d.spX` alone is a family of bijections of point sets, one for each base
point; `d.spX_nat` makes that family NATURAL, hence a natural isomorphism
between the functor of points of `strX'` over `Spec 𝔽_ℓ` and the functor
`T ↦ 𝒳(T → Spec ℤ_(ℓ))` represented by the base change
`𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ`.  Yoneda then produces an honest isomorphism of
schemes over `Spec 𝔽_ℓ`, which is precisely the content the docstring of
`exists_isX0Compactification_specialFibre` says would be lost if
naturality were dropped: without it `X'` could be any scheme abstractly
equinumerous with the special fibre.

The proof is Yoneda evaluated by hand at two tautological points, and it
uses no property of `Spec ℤ_(ℓ)`, of `ℓ`, or of `N`:

* `w : X' ⟶ 𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ` is `pullback.lift` of the image of the
  identity point `𝟙 X' ∈ X'(X')` under `spX`;
* `w' : 𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ ⟶ X'` is the `spX`-preimage of the tautological
  point `pullback.fst`;
* `w ≫ w' = 𝟙` follows from `spX_nat` along `w` plus injectivity of
  `spX`; `w' ≫ w = 𝟙` from `spX_nat` along `w'` plus `pullback.hom_ext`.

Only the CURVE half of the datum is consumed, so the Jacobian
identifications `spJ`/`spJ_nat` and the Néron mapping property play no
part here. -/
theorem exists_inverse_pullbackSpecial {N ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X J X' J' XZ YZ JZ : Scheme.{0}} {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    {jac : IsJacobianOf strX ab o} {jac' : IsJacobianOf strX' ab' o'}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} {jacZ : IsJacobianOf xstr abZ oZ}
    (d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :
    ∃ (w : X' ⟶ pullback xstr (SpecLoc.special toF))
      (w' : pullback xstr (SpecLoc.special toF) ⟶ X'),
      w ≫ pullback.snd xstr (SpecLoc.special toF) = strX' ∧
      w' ≫ strX' = pullback.snd xstr (SpecLoc.special toF) ∧
      w ≫ w' = 𝟙 X' ∧
      w' ≫ w = 𝟙 (pullback xstr (SpecLoc.special toF)) := by
  obtain ⟨w, hwq, hwf⟩ :
      ∃ w : X' ⟶ pullback xstr (SpecLoc.special toF),
        w ≫ pullback.snd xstr (SpecLoc.special toF) = strX' ∧
        w ≫ pullback.fst xstr (SpecLoc.special toF) =
          (d.spX strX' (strX' ≫ SpecLoc.special toF) rfl
            (⟨𝟙 X', Category.id_comp _⟩ : RelPoint strX' strX')).1 :=
    ⟨pullback.lift _ strX'
        (d.spX strX' (strX' ≫ SpecLoc.special toF) rfl
          (⟨𝟙 X', Category.id_comp _⟩ : RelPoint strX' strX')).2,
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  obtain ⟨wp, hwpsp⟩ :
      ∃ wp : RelPoint strX' (pullback.snd xstr (SpecLoc.special toF)),
        d.spX (pullback.snd xstr (SpecLoc.special toF))
            (pullback.snd xstr (SpecLoc.special toF) ≫ SpecLoc.special toF) rfl wp =
          ⟨pullback.fst xstr (SpecLoc.special toF), pullback.condition⟩ :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  refine ⟨w, wp.1, hwq, wp.2, ?_, ?_⟩
  · have hnat := d.spX_nat w hwq
      (rfl : pullback.snd xstr (SpecLoc.special toF) ≫ SpecLoc.special toF = _)
      (rfl : strX' ≫ SpecLoc.special toF = _) wp
    rw [hwpsp] at hnat
    have hkey : RelPoint.pre w hwq wp = (⟨𝟙 X', Category.id_comp _⟩ : RelPoint strX' strX') :=
      (d.spX strX' (strX' ≫ SpecLoc.special toF) rfl).injective
        (by rw [hnat]; exact Subtype.ext hwf)
    exact congrArg Subtype.val hkey
  · refine pullback.hom_ext ?_ ?_
    · have hnat := d.spX_nat wp.1 wp.2
        (rfl : strX' ≫ SpecLoc.special toF = _)
        (rfl : pullback.snd xstr (SpecLoc.special toF) ≫ SpecLoc.special toF = _)
        (⟨𝟙 X', Category.id_comp _⟩ : RelPoint strX' strX')
      have hpre : RelPoint.pre wp.1 wp.2
          (⟨𝟙 X', Category.id_comp _⟩ : RelPoint strX' strX') = wp :=
        Subtype.ext (Category.comp_id _)
      rw [hpre, hwpsp] at hnat
      have hval : pullback.fst xstr (SpecLoc.special toF) =
          wp.1 ≫ (d.spX strX' (strX' ≫ SpecLoc.special toF) rfl
            (⟨𝟙 X', Category.id_comp _⟩ : RelPoint strX' strX')).1 :=
        congrArg Subtype.val hnat
      rw [Category.assoc, hwf, ← hval, Category.id_comp]
    · rw [Category.assoc, hwq, wp.2, Category.id_comp]

/-- **The coarse moduli space of `Γ₀(N)` base-changes to the special
fibre** (sorry node — this is where good reduction lives).

TRUE for `ℓ ∤ N`, and it is the ONE genuinely modular input to the
identification of the special fibre.  The `Γ₀(N)`-moduli problem is
defined over `ℤ[1/N]`, so at `ℓ ∤ N` the base change of a coarse moduli
space over `ℤ_(ℓ)` along `Spec 𝔽_ℓ ⟶ Spec ℤ_(ℓ)` is again one, over
`𝔽_ℓ` — the classifying map base-changes by naturality, and initiality
survives because the moduli problem is compatible with the base change
(Deligne–Rapoport IV; Katz–Mazur 8.2 for the coarse space, 3.7 for the
smoothness of the moduli problem away from the level).

**`_hℓN` cannot be dropped.**  At `ℓ ∣ N` the special fibre of the
`Γ₀(N)`-problem is not the `Γ₀(N)`-problem over `𝔽_ℓ` at all: the moduli
stack acquires the Deligne–Rapoport crossing of two Igusa components, and
the special fibre of `Y_0(N)_{ℤ_(ℓ)}` is not a coarse moduli space for
`Γ₀(N)/𝔽_ℓ`.  `_hbase` is what makes `SpecLoc.special toF` the honest
closed point.

The hypotheses carry underscores only because the body is `sorry`.

IRREDUCIBLE at this pin: coarse moduli spaces exist in this development
only as the `IsCoarseModuliY0` interface, with no base-change lemma and
no representability, and `Mathlib` has neither. -/
theorem nonempty_isCoarseModuliY0_pullbackSpecial {N ℓ : ℕ} (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (_hbase : IsReductionBase ℓ R toF) {YZ : Scheme.{0}} {ystr : YZ ⟶ SpecLoc R}
    (_hcoarse : IsCoarseModuliY0 N ystr) :
    Nonempty (IsCoarseModuliY0 N (pullback.snd ystr (SpecLoc.special toF))) :=
  sorry

/-- **The cusp locus of the special fibre is finite** (sorry node).

TRUE, and it is the one clause of `IsX0Compactification` that `Mathlib`'s
base-change instances do not supply, because the underlying space of a
fibre product of schemes is not the fibre product of the underlying
spaces.  The honest argument: the complement of `Y ⊆ 𝒳` is a closed
subscheme finite over `Spec ℤ_(ℓ)` (finite as a set and proper over the
base, hence finite), its base change to `𝔽_ℓ` is finite over `Spec 𝔽_ℓ`,
and the complement of the base-changed open is exactly that base change
because forming an open subscheme commutes with base change.

`jsp` is characterised by its two components rather than taken to be
`pullback.map` on the nose, so that the statement does not carry a
`pullback.map` proof obligation inside its own type; `_hfst` and `_hsnd`
pin it uniquely by `pullback.hom_ext`.

The hypotheses carry underscores only because the body is `sorry`. -/
theorem finite_compl_pullbackSpecial {N ℓ : ℕ} (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (_hbase : IsReductionBase ℓ R toF)
    {XZ YZ : Scheme.{0}} {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (_hmodel : IsX0Compactification N xstr ystr jZ)
    (jsp : pullback ystr (SpecLoc.special toF) ⟶ pullback xstr (SpecLoc.special toF))
    (_hfst : jsp ≫ pullback.fst xstr (SpecLoc.special toF)
      = pullback.fst ystr (SpecLoc.special toF) ≫ jZ)
    (_hsnd : jsp ≫ pullback.snd xstr (SpecLoc.special toF)
      = pullback.snd ystr (SpecLoc.special toF)) :
    (Set.range jsp.base)ᶜ.Finite :=
  sorry

/-- **The base change of the smooth model to `𝔽_ℓ` is `X_0(N)` over
`𝔽_ℓ`** (PROVEN from the two leaves above).

Everything except the coarse-moduli clause and the cusp count is
`Mathlib`: `IsProper`, `GeometricallyConnected` and `IsOpenImmersion`
have base-change instances that fire directly, and
`SmoothOfRelativeDimension 1` has
`smoothOfRelativeDimension_isStableUnderBaseChange` — a `lemma` rather
than an `instance`, which is why it is supplied by hand here.

The open part of the special fibre is `𝒴 ×_{ℤ_(ℓ)} 𝔽_ℓ` and the
immersion is `pullback.map` of `jZ`; `comm` is `pullback.lift_snd`. -/
theorem exists_isX0Compactification_pullbackSpecial {N ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    (hbase : IsReductionBase ℓ R toF)
    {XZ YZ : Scheme.{0}} {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    (hmodel : IsX0Compactification N xstr ystr jZ) :
    ∃ (Y'' : Scheme.{0}) (strY'' : Y'' ⟶ SpecF ℓ)
      (j'' : Y'' ⟶ pullback xstr (SpecLoc.special toF)),
      Nonempty (IsX0Compactification N
        (pullback.snd xstr (SpecLoc.special toF)) strY'' j'') := by
  haveI := hmodel.isOpen
  haveI := hmodel.isProper
  haveI := hmodel.connected
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  obtain ⟨hcoarse⟩ :=
    nonempty_isCoarseModuliY0_pullbackSpecial hℓ hℓN hbase hmodel.coarse
  refine ⟨_, pullback.snd ystr (SpecLoc.special toF),
    pullback.map ystr (SpecLoc.special toF) xstr (SpecLoc.special toF) jZ
      (𝟙 (SpecF ℓ)) (𝟙 (SpecLoc R)) (by rw [Category.comp_id, hmodel.comm])
      (by rw [Category.comp_id, Category.id_comp]),
    ⟨?_, hcoarse, inferInstance, inferInstance,
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ hmodel.smooth,
      inferInstance, ?_⟩⟩
  · rw [pullback.lift_snd, Category.comp_id]
  · exact finite_compl_pullbackSpecial hℓ hℓN hbase hmodel _
      (by rw [pullback.lift_fst]) (by rw [pullback.lift_snd, Category.comp_id])

/-- **The special fibre of the smooth model over `ℤ_(ℓ)` is `X_0(N)` over
`𝔽_ℓ`** (PROVEN 2026-07-27 — good reduction, on the curve side).

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

**How it is proven, and where the two halves went.**  The naturality
half is `exists_inverse_pullbackSpecial`: `spX` together with `spX_nat`
is a natural isomorphism of functors of points, so Yoneda gives an honest
isomorphism `X' ≅ 𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ` over `Spec 𝔽_ℓ`.  The good-reduction
half is `exists_isX0Compactification_pullbackSpecial`, which puts the
compactification structure on that base change and is itself reduced to
`nonempty_isCoarseModuliY0_pullbackSpecial` and
`finite_compl_pullbackSpecial`.  `IsX0Compactification.ofInverse` then
carries the structure across the isomorphism.

So the earlier verdict "IRREDUCIBLE at this pin" was right about the
mathematics and wrong about the cut: base change of coarse moduli spaces
really is missing, but it is the ONLY missing piece, and it did not have
to be entangled with the Yoneda rigidity or with the base change of
properness, smoothness and connectedness — all of which `Mathlib`
already has. -/
theorem exists_isX0Compactification_specialFibre {N ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X J X' J' XZ YZ JZ : Scheme.{0}} {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    {jac : IsJacobianOf strX ab o} {jac' : IsJacobianOf strX' ab' o'}
    {xstr : XZ ⟶ SpecLoc R} {ystr : YZ ⟶ SpecLoc R} {jZ : YZ ⟶ XZ}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} {jacZ : IsJacobianOf xstr abZ oZ}
    (d : IsX0NeronDatum N ℓ R toF jac jac'
      (ystr := ystr) (jZ := jZ) (abZ := abZ) jacZ) :
    ∃ (Y'' : Scheme.{0}) (strY'' : Y'' ⟶ SpecF ℓ) (j'' : Y'' ⟶ X'),
      Nonempty (IsX0Compactification N strX' strY'' j'') := by
  obtain ⟨Y'', strY'', j'', ⟨hP⟩⟩ :=
    exists_isX0Compactification_pullbackSpecial (N := N) hℓ hℓN d.base d.model
  obtain ⟨w, w', hw, hw', hww', hw'w⟩ := exists_inverse_pullbackSpecial d
  exact ⟨Y'', strY'', j'' ≫ w', ⟨hP.ofInverse hw' hw hw'w hww'⟩⟩

/-- **A smooth proper curve over a field is determined by a dense open**
(sorry node — the closure-of-the-graph argument).

TRUE over a FIELD, and this is the second of the two steps of the
uniqueness statement below; the first, initiality of the coarse moduli
space, is `IsCoarseModuliY0.exists_inverse` and is PROVEN.

The argument: `Y₁ ≅ Y₂` over `k` by hypothesis, and both `X_i` are smooth
proper geometrically connected curves containing `Y_i` as a dense open —
dense because a nonempty open of an irreducible curve is dense, which is
where `finite_compl` is consumed.  Take the closure `Γ` of the graph of
`u` inside `X₁ ×_k X₂`.  Both projections `Γ ⟶ X_i` are proper (closed
subscheme of a proper `k`-scheme) and birational (isomorphisms over the
dense open), hence isomorphisms, because a proper birational morphism to
a smooth — hence normal — curve is an isomorphism (Zariski's main
theorem in dimension one).  Composing gives `w : X₁ ⟶ X₂` extending `u`,
and the same construction run backwards gives its inverse.

**Why the base is `Spec 𝔽_ℓ` and not a general scheme.**  Over a general
base the graph closure argument fails — a non-reduced or non-normal base
breaks both the density step and the normality step — and the leaf would
be FALSE for a generality nothing here consumes.  `_hℓ` is what makes
`ZMod ℓ` a field, and it is load-bearing for exactly that.

**Not vacuous.**  At `N = 0` the hypotheses are unsatisfiable
(`isEmpty_of_gamma0Datum_zero` forces `Y` initial, hence empty, and
`finite_compl` then makes the whole space of `X` finite, which a smooth
proper curve over a field is not), so the leaf is vacuously true there
and carries no content it should not; at the levels that matter it is
satisfied, by `exists_x0Compactification_mod_prime`.

The conclusion carries `jY₁ ≫ w = u ≫ jY₂` — that `w` extends the given
isomorphism of the open parts — even though the consumer below uses only
the inverse pair.  Without it the statement would be strictly weaker than
the theorem it names, and a later consumer wanting compatibility on cusps
would have to reopen it.

The hypotheses carry underscores only because the body is `sorry`.

IRREDUCIBLE at this pin: no smooth-compactification theorem for curves
exists in `Mathlib`, which is the same obstruction recorded at
`exists_x0Compactification`. -/
theorem exists_inverse_of_isX0Compactification {N ℓ : ℕ} (_hℓ : ℓ.Prime)
    {X₁ Y₁ X₂ Y₂ : Scheme.{0}} {strX₁ : X₁ ⟶ SpecF ℓ} {strY₁ : Y₁ ⟶ SpecF ℓ}
    {jY₁ : Y₁ ⟶ X₁} {strX₂ : X₂ ⟶ SpecF ℓ} {strY₂ : Y₂ ⟶ SpecF ℓ} {jY₂ : Y₂ ⟶ X₂}
    (_h₁ : IsX0Compactification N strX₁ strY₁ jY₁)
    (_h₂ : IsX0Compactification N strX₂ strY₂ jY₂)
    {u : Y₁ ⟶ Y₂} {v : Y₂ ⟶ Y₁} (_hu : u ≫ strY₂ = strY₁) (_hv : v ≫ strY₁ = strY₂)
    (_huv : u ≫ v = 𝟙 Y₁) (_hvu : v ≫ u = 𝟙 Y₂) :
    ∃ (w : X₁ ⟶ X₂) (w' : X₂ ⟶ X₁),
      w ≫ strX₂ = strX₁ ∧ w' ≫ strX₁ = strX₂ ∧
      w ≫ w' = 𝟙 X₁ ∧ w' ≫ w = 𝟙 X₂ ∧ jY₁ ≫ w = u ≫ jY₂ :=
  sorry

/-- **`X_0(N)` over `𝔽_ℓ` is unique up to isomorphism, hence its rational
points up to bijection** (PROVEN 2026-07-27).

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

**How it is proven.**  Step 1 is `IsCoarseModuliY0.exists_inverse`,
PROVEN here: initiality of `IsCoarseModuliY0` gives the inverse pair
`Y₁ ⇄ Y₂` over `𝔽_ℓ` outright.  Step 2 is
`exists_inverse_of_isX0Compactification`, which is the only thing still
open — the closure-of-the-graph argument, and the sole remaining content
of this statement.  `relPointEquivOfInverse` then turns the resulting
inverse pair on `X` into the bijection of points. -/
theorem nonempty_relPointEquiv_of_isX0Compactification {N ℓ : ℕ} (hℓ : ℓ.Prime)
    {X₁ Y₁ X₂ Y₂ : Scheme.{0}} {strX₁ : X₁ ⟶ SpecF ℓ} {strY₁ : Y₁ ⟶ SpecF ℓ}
    {jY₁ : Y₁ ⟶ X₁} {strX₂ : X₂ ⟶ SpecF ℓ} {strY₂ : Y₂ ⟶ SpecF ℓ} {jY₂ : Y₂ ⟶ X₂}
    (h₁ : IsX0Compactification N strX₁ strY₁ jY₁)
    (h₂ : IsX0Compactification N strX₂ strY₂ jY₂) :
    Nonempty (RelPoint strX₁ (𝟙 (SpecF ℓ)) ≃ RelPoint strX₂ (𝟙 (SpecF ℓ))) := by
  obtain ⟨u, v, hu, hv, huv, hvu⟩ := IsCoarseModuliY0.exists_inverse h₁.coarse h₂.coarse
  obtain ⟨w, w', hw, hw', hww', hw'w, -⟩ :=
    exists_inverse_of_isX0Compactification hℓ h₁ h₂ hu hv huv hvu
  exact ⟨relPointEquivOfInverse hw hw' hww' hw'w⟩

end SpecialFibre

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

/-! #### The semiprime chain, relocated here by declaration order

The four declarations immediately below belong, thematically, to the
`#### The `61` semiprime levels` block far above, beside the partition
and the three leaves they consume.  They sit here instead because
`y0HasNoRationalPoint_of_witnessSemiprimeLevel` was CLOSED on 2026-07-27
by `y0HasNoRationalPoint_of_witnessPrime`, and that theorem needs the
whole compactification/Jacobian/reduction section in between.  Lean's
declaration order then forces the chain — the `35, 39` leaf, the
five-way dispatch over `smallSemiprimeLevels`, the cuspidality statement
on `X_0(pq)` and the `Y_0(pq)` form — down past that section.  Nothing
about the mathematics moved; only the position did. -/

/-- **`Y_0(35)(ℚ) = Y_0(39)(ℚ) = ∅`** (PROVEN 2026-07-27; introduced as a
sorry node the same day).

Proven exactly as its own docstring predicted: `35` and `39` were added
to `kenkuLevels`, the rows `(35, 3, 4)` and `(39, 5, 4)` to
`x0WitnessTable`, and `y0HasNoRationalPoint_of_witnessPrime` then applies
verbatim at both levels.  Both have `rank J_0(N)(ℚ) = 0` and a sharp
witness prime:

| `N` | genus | rational cusps | `ℓ` | `#X_0(N)(𝔽_ℓ)` |
|-----|-------|----------------|-----|------------------|
| `35` | `3` | `4` | `3`  | `4` |
| `39` | `3` | `4` | `5`  | `4` |

Every entry was reproduced with PARI/GP 2.17.4 before the tables were
touched, rather than copied from the prose that motivated the leaf.  The
genus values are `x0Genus 35 = x0Genus 39 = 3` — now also machine-checked
by `one_le_x0Genus_of_kenkuLevel`, whose `decide` still closes with the
two new levels present.  The counts are Eichler–Shimura,
`#X_0(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_0(N)))`, from the trace form of
the cuspidal space: `Tr(T_3 ∣ S_2(Γ_0(35))) = 0` and
`Tr(T_5 ∣ S_2(Γ_0(39))) = 2`.  The rank-`0` claims are the vanishing
order of `L` at `s = 1` on each newform factor: `S_2(Γ_0(35))` and
`S_2(Γ_0(39))` are each `3`-dimensional and all new, and all six
embeddings give `L(f, 1) ≠ 0`, so Kolyvagin–Logachev gives Mordell–Weil
rank `0`.

What this leaf did NOT need, despite its siblings: no sieve (unlike
`26`, where no prime is ever sharp) and no Chabauty–Coleman (unlike
`65, 91`, whose equally sharp-looking counts are a trap because their
ranks are `1` and `2`).

The two obligations that adding the levels EXTENDS rather than
discharges, recorded so no later owner mistakes them for closed:
`finite_jacobian_of_kenkuLevel` and
`exists_x0Compactification_mod_prime` are both still sorry nodes, and
each now carries two further cases.  The reconnaissance above is exactly
what a prover of those two needs at `35` and `39`.

`N = 39` is Kenku, *The modular curve `X_0(39)` and rational isogeny*,
Math. Proc. Cambridge Philos. Soc. **85** (1979) 21–23.  `N = 35` is not
the subject of a Kenku paper — see the section docstring. -/
theorem y0HasNoRationalPoint_of_witnessSemiprimeLevel (N : ℕ)
    (hN : N ∈ witnessSemiprimeLevels) : Y0HasNoRationalPoint N := by
  fin_cases hN
  · exact y0HasNoRationalPoint_of_witnessPrime 35 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact y0HasNoRationalPoint_of_witnessPrime 39 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

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

/-- **Kenku's semiprime determination, on `X_0(pq)`** (PROVEN 2026-07-27
over the four leaves above): for distinct primes `p, q` both in
`mazurIsogenyPrimes` with `p * q ∉ {6, 10, 14, 15, 21}`, every rational
point of `X_0(pq)` is a cusp.

TRUE, and FINITE: `61` explicit levels, the smallest `2 · 11 = 22` and
the largest `67 · 163 = 10921`.  Every one has genus `≥ 2` (minimum `2`,
at `N = 26`), so none is an elliptic-curve rank computation.

**The cut.**  The `#### The `61` semiprime levels` docstring far above
carries the full partition, the PARI/GP reconnaissance and the corrected
literature map; in outline:

* `56` levels have a prime in `isolatedIsogenyPrimes`, where `X_0(p)(ℚ)`
  is finite and tabulated, and descend to it uniformly —
  `y0HasNoRationalPoint_of_isolatedSemiprime`;
* the residual `5` are `26, 35, 39, 65, 91`, split by the route their
  arithmetic forces: `35, 39` (rank `0`, sharp witness prime — CLOSED
  2026-07-27), `26` (rank `0`, no sharp prime exists — needs the sieve),
  `65, 91` (positive rank — needs Chabauty–Coleman).

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
(PROVEN 2026-07-26): `Y_0(pq)(ℚ) = ∅` for distinct primes `p, q` BOTH in
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

**The rank-`0`-plus-reduction route is now REALISED in this file**, and
that is what changed on 2026-07-27: `y0HasNoRationalPoint_of_witnessPrime`
is exactly that criterion, and `35, 39` — two of the five residual levels
— are closed by it.  What remains of the `61` is `26` (needs the
multi-prime sieve, `y0HasNoRationalPoint_x0TwentySix`), `65, 91` (need
Chabauty–Coleman, `y0HasNoRationalPoint_of_chabautySemiprimeLevel`) and
the `56` isolated-prime levels
(`y0HasNoRationalPoint_of_isolatedSemiprime`).  Note that this node
itself is PROVEN — it is those three leaves, not this assembly, that
carry what is left.

Neither criterion was stated as a leaf when this module was written,
deliberately.  Both are statements about `X_0(pq)` — the SMOOTH
COMPACTIFICATION, its cusps, its Jacobian, and an integral model to
reduce along — and this module stopped at the affine coarse space
`Y_0(N)` precisely to keep that out of the critical path.  Writing
either criterion against `Y_0(N)` alone would have to smuggle the point
count into a hypothesis, since rank `0` by itself gives FINITENESS of
`X_0(N)(ℚ)` and never emptiness of `Y_0(N)(ℚ)`; the step from finite to
empty *is* the cusp count.  A criterion whose hypothesis is equivalent
to its conclusion would be a false economy, so the honest decomposition
was the compactification interface first (`X_0(N) ⊇ Y_0(N)` proper
smooth, with its rational cusps), then `J_0(N)` as an abelian scheme,
and only then the two criteria.

**All three of those steps now exist.**  `IsCompactificationY0` is the
interface, `HasRankZeroJacobian` and `card_le_of_rankZeroJacobian` are
the Jacobian and the reduction bound, and
`y0HasNoRationalPoint_of_witnessPrime` is the criterion — stated
honestly, with the cusp count entering as a count of `X(𝔽_ℓ)` and never
as a hypothesis about `X(ℚ)`.  Its own remaining obligations are
`finite_jacobian_of_kenkuLevel`, `injective_aj_of_one_le_x0Genus`,
`card_le_of_rankZeroJacobian` and
`exists_x0Compactification_mod_prime`. -/
theorem y0HasNoRationalPoint_semiprime_of_mazurPrimes {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hpm : p ∈ mazurIsogenyPrimes)
    (hqm : q ∈ mazurIsogenyPrimes)
    (hmem : p * q ∉ ({6, 10, 14, 15, 21} : Finset ℕ)) :
    Y0HasNoRationalPoint (p * q) := by
  obtain ⟨Y, strY, ⟨hc⟩⟩ := exists_coarseModuliY0 (p * q)
  obtain ⟨X, strX, ⟨hX⟩⟩ := exists_compactificationY0 hc
  exact y0HasNoRationalPoint_of_cuspidal hc hX
    (cuspidal_x0_semiprime_of_mazurPrimes hp hq hpq hpm hqm hmem hc hX)

/-- **`Y_0(pq)(ℚ) = ∅` for `pq` a product of two distinct primes outside
`{6, 10, 14, 15, 21}`** (PROVEN 2026-07-26 — the uniform, squarefree part
of Kenku's determination; the `(sorry node)` label this docstring carried
until 2026-07-27 was stale, and the proof below has been here since the
day it says).

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

**Scope note (2026-07-27).**  This block covers the ELEVEN named level
nodes below — the original `kenkuLevels`.  `kenkuLevels` itself has
since grown to thirteen: `35` and `39` were added so that
`y0HasNoRationalPoint_of_witnessSemiprimeLevel` could be closed by
`y0HasNoRationalPoint_of_witnessPrime`.  Those two have no named level
node of their own, and their reconnaissance — genus `3` and `3`,
rank `0` and `0`, four rational cusps each, witness primes `3` and `5`
with `#X_0(N)(𝔽_ℓ) = 4` — is recorded on that leaf instead, computed
with PARI/GP rather than Magma.  So the counts below read "eleven"
throughout and are correct as written; do not "fix" them to thirteen.

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
phantom work.  All thirteen levels are blocked on exactly the same absent
object — `X_0(N)` as a scheme, its cusps, `J_0(N)`, Mordell–Weil, and
reduction mod `ℓ` — none of which exists in `Mathlib` or in `~/cs/FLT`
(re-surveyed 2026-07-26: `Mathlib/AlgebraicGeometry/` contains no abelian
variety and no modular curve of any kind).  Once that layer exists, a
sieve level costs one extra *finite* computation over a single-prime
level, and the arithmetic for it is fully recorded above.

*Amended 2026-07-26, and this supersedes the paragraph above.*  That
shared layer is now WRITTEN, as the interface `IsX0Compactification` /
`IsJacobianOf` / `HasRankZeroJacobian`, so all thirteen levels are proven
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

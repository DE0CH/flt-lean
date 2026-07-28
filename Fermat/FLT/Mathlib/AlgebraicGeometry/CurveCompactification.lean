/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- E. Noether's finiteness theorem below (`module_finite_integralClosure_of_isFractionRing` and
-- the three statements it is proven over) needs the separable/purely-inseparable factorisation
-- of a finite field extension and the integral-closure finiteness engine over an integrally
-- closed Noetherian base.
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
-- The shared "smooth curve over a field ⟺ DVR local rings" node, and the extension theorem
-- built on it.  `smoothOfRelativeDimension_one_fromNormalization` below consumes the
-- backward direction; `Fermat/FLT/ModularCurve/X0.lean` consumes the forward one.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveExtension

/-!
# Smooth compactification of a smooth curve over a field

Every smooth curve over a field embeds as a **dense open subscheme of a smooth proper
curve**, and the complement is finite.  This is the classical statement behind the
equivalence "smooth projective curves over `k` ↔ function fields of transcendence degree
one over `k`" (Hartshorne I.6), and it is what makes `X_0(N)` exist as soon as `Y_0(N)`
does.

Nothing of this kind is in `Mathlib` at this pin: there is no `IsNormal` for schemes, no
`Scheme.dimension`, no projective closure, and no compactification statement anywhere.
What *is* available — and what this file is built on — is enough to reduce the theorem to
four genuinely separate classical inputs, with the entire glue proved:

* `AlgebraicGeometry.Scheme.Hom.normalization`, the **relative normalization**
  (`Mathlib/AlgebraicGeometry/Normalization.lean`), with `toNormalization : Y ⟶ Y'` and
  `fromNormalization : Y' ⟶ P`, the latter always `IsIntegralHom` and the former always
  `IsDominant`;
* **Zariski's Main Theorem** (`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`), whose
  corollary `IsOpenImmersion f.toNormalization` for `f` quasi-finite, separated,
  quasi-compact and locally of finite type is exactly the statement that `Y` sits inside
  its relative normalization as an *open* subscheme.

## The construction

Given a smooth curve `strY : Y ⟶ Spec K`:

1. compactify `Y` as a *scheme*, ignoring smoothness — Nagata's compactification theorem
   produces a proper `strP : P ⟶ Spec K` and an open immersion `i : Y ⟶ P`
   (`exists_isOpenImmersion_isProper`, PROVEN as of the third pass below over three
   sharper leaves);
2. take `X := i.normalization`, the normalization of `P` in `Y`.  Then
   `j := i.toNormalization : Y ⟶ X` is an open immersion **by Zariski's Main Theorem**
   and dominant **by construction** — both free from `Mathlib`;
3. `i.fromNormalization : X ⟶ P` is integral, and it is *finite* because normalization is of
   finite type for schemes of finite type over a field
   (`locallyOfFiniteType_fromNormalization`, PROVEN over the affine-local ring statement
   `finiteType_integralClosure_sections`, itself PROVEN 2026-07-27 over E. Noether's finiteness
   theorem `module_finite_integralClosure_of_isFractionRing`, which is in turn PROVEN the same
   day over `module_finite_integralClosure_of_isPurelyInseparable` — itself PROVEN 2026-07-28
   over `module_finite_integralClosure_mvPolynomial`, whose single remaining residue is
   `module_finite_integralClosure_mvPolynomial_of_isPurelyInseparable`, the classical
   "a polynomial ring over a field is Japanese");
   finite ⟹ proper, so `X` is proper over `K`;
4. `X` is normal of dimension one over a perfect field, hence smooth
   (`smoothOfRelativeDimension_one_fromNormalization`, PROVEN over the normality statement
   `isDiscreteValuationRing_stalk_normalization`, LEAF, and the shared DVR node in
   `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`);
5. the complement of a dense open in an irreducible noetherian curve is finite — proven
   here from the one-dimensionality of `X` (`topologicalKrullDim_normalization_le_one`,
   PROVEN over `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one`, which is itself
   now PROVEN over the single ring-theoretic leaf
   `ringKrullDim_le_one_of_locally_isStandardSmoothOfRelativeDimension_one`, and over
   `topologicalKrullDim_le_of_isOpenImmersion_of_irreducible`, PROVEN outright 2026-07-27).

Step 2, the assembly, and the whole of steps 3 and 5 apart from their two named inputs are
PROVEN here.

## The leaves, after the 2026-07-27 decompositions

Every one of the original five leaves has now been cut down; the remaining leaves are
(`nonempty_projChart_mvPolynomial` and `smoothOfRelativeDimension_of_isDominant` left this
list on 2026-07-27, both PROVEN):

**⚠ THIS TABLE IS NOT THE COMPILER'S SORRY SET AND HAS BEEN WRONG BEFORE.**  Several rows below
name declarations that are PROVEN; a dispatch built from the table alone is a phantom dispatch.
The authoritative list is the `declaration uses 'sorry'` warning set of a green
`lake build Fermat.FLT.Mathlib.AlgebraicGeometry.CurveCompactification`.  At `31bdb897` (verified
2026-07-28, `EXIT=0`) that set was exactly five: `nonempty_projChart_of_surjective`,
`exists_isOpenImmersion_isProper_of_affineCase`,
`module_finite_integralClosure_of_isPurelyInseparable` (closed by this pass, replaced by the two
rows below), `isDiscreteValuationRing_stalk_normalization`, and
`ringKrullDim_le_one_of_locally_isStandardSmoothOfRelativeDimension_one`.

| leaf | content |
| --- | --- |
| `nonempty_projChart_of_surjective` | the projective closure of an affine variety |
| `exists_isOpenImmersion_isProper_of_affineCase` | Nagata's gluing induction (all that is left of Nagata) |
| `topologicalKrullDim_normalization_le_one` | dimension = transcendence degree, so the normalized model is a curve |
| `exists_isOpenImmersion_isProper` | Nagata compactification (unchanged — a single citation, no cut available) |
| `finiteType_integralClosure_sections` | Nagata/Japanese rings: the integral closure of a finite-type `K`-algebra in the sections of `Y` over an affine chart is of finite type |
| `ringKrullDim_le_one_of_locally_isStandardSmoothOfRelativeDimension_one` | a locally standard smooth `K`-algebra of relative dimension one has Krull dimension `≤ 1` (all that is left of "a smooth curve over a field is one-dimensional", 2026-07-27) |
| `module_finite_integralClosure_mvPolynomial_of_isPurelyInseparable` | **a polynomial ring over a field is JAPANESE** (Stacks `0334`), in the only direction the pin cannot reach: `L / Frac (k[x₁,…,x_d])` finite PURELY INSEPARABLE ⟹ the integral closure of `k[x₁,…,x_d]` in `L` is module-finite.  The base being a POLYNOMIAL ring is essential and not a convenience — see the docstring |
| ~~`isSeparable_perfectClosure_of_normal`~~ | for `N / K` finite NORMAL, `N` is separable over the relative perfect closure `perfectClosure K N` — the order opposite to `separableClosure`, absent from the pin.  Cut as a leaf and **PROVEN the same day, 2026-07-28**, from Artin's theorem plus `AlgHom.liftNormal`; listed only so nobody re-cuts it |
| `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` | a smooth curve over a field is one-dimensional |
| `topologicalKrullDim_le_of_isOpenImmersion_of_irreducible` | a nonempty open of an irreducible finite-type `K`-scheme carries the full dimension |
| `smoothOfRelativeDimension_one_fromNormalization` | normal + dimension one + perfect base ⟹ smooth (unchanged; the deepest) |
| ~~`infinite_of_smoothOfRelativeDimension_one`~~ (in `CurveExtension.lean`) | a nonempty smooth curve over a field has infinitely many points — the only input to the density subsection at the end of this file. **NO LONGER A LEAF: PROVEN 2026-07-27** in `CurveExtension.lean`, over Krull's height theorem and the Nullstellensatz; do not dispatch at it |
| `isDiscreteValuationRing_stalk_normalization` | the relative normalization is NORMAL, hence its local rings in dimension one are DVRs |

## Third decomposition pass, 2026-07-27: the DVR node is shared with `X0.lean`

`smoothOfRelativeDimension_one_fromNormalization` — the leaf the table above used to call
"the deepest" — is **PROVEN**.  It split along the seam that the "IRREDUCIBLE at this pin"
verdict on it had missed: `Mathlib` *does* have `IsRegularLocalRing`
(`Mathlib/RingTheory/RegularLocalRing/Defs.lean`) and *does* have
`IsLocalRing.finrank_CotangentSpace_eq_one_iff` identifying regularity with
`IsDiscreteValuationRing` in dimension one.  So what is missing is not "a notion of
regularity" but two separate things, and only one of them lives here:

* *normality of the relative normalization* — `isDiscreteValuationRing_stalk_normalization`
  above, genuinely absent from `Mathlib`, which records `IsIntegralHom f.fromNormalization`
  but nothing about the stalks being integrally closed;
* *regular ⟹ smooth over a perfect field* — `smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk`
  in `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`, which is **shared** with
  `Fermat/FLT/ModularCurve/X0.lean`: that file needs the same equivalence in the *forward*
  direction (it has smoothness and wants DVRs, to run the valuative criterion at the cusps),
  and both directions now live in one module with one owner.

## Second decomposition pass, 2026-07-27

Two more of the leaves in the table above are gone, replaced by the three sharper ones now in
it:

* `locallyOfFiniteType_fromNormalization` is a THEOREM over `finiteType_integralClosure_sections`.
  What came out of it is the entire `IsZariskiLocalAtTarget` descent — a transcription of
  `Mathlib`'s own proof of `instance : IsIntegralHom f.fromNormalization` — leaving a statement
  with no scheme theory in it at all.
* `topologicalKrullDim_normalization_le_one` is a THEOREM over the two dimension leaves.  What
  came out of it is the identification of `i.toNormalization` as an open immersion into an
  irreducible scheme of finite type over `K` — Zariski's Main Theorem plus
  `IsIntegral Y ⟹ IsIntegral i.normalization` plus `isFinite_fromNormalization` — which is
  exactly the hypothesis threading the `ULift ℚ`-shaped copy of the statement in
  `Modularity/KhareWintenberger.lean` had to receive from its consumer.

`isFinite_fromNormalization`, `finite_compl_range_toNormalization`, `denseRange_of_isPullback`
and `geometricallyConnected_of_isSmoothCompactification` are also THEOREMS over these.  What was
removed from them was, in each case, real: the integrality half of finiteness (free from
`Mathlib`), the entire noetherian-ness bookkeeping and point-set argument behind the finite
complement, the closure-of-a-connected-set half of geometric connectedness, and — as of the
second pass below — the whole pullback-pasting and point-set argument behind base change.

None of the leaves mentions modular curves; each is independent of the others; all are
dispatchable in isolation.

## `denseRange_of_isPullback` was FALSE, and is now a THEOREM (2026-07-27, second pass)

It quantified over an arbitrary base scheme `S`, and its own justification named the false
step: `Spec L ⟶ S` is flat for a field `L` only when `S` is itself the spectrum of a field.
`S = Spec ℤ`, `Y' = Spec ℚ ↪ Spec ℤ = X'` and `L = 𝔽_p` refutes it, the base change of the
dense `Spec ℚ` being empty inside the one-point `Spec 𝔽_p`.  See the FALSITY AUDIT on the
declaration for that counterexample in full, for a second one showing that adding `[Flat y]`
would NOT have been enough, and for the two hypotheses that had to be added to make `m` the
base change of `j` rather than an arbitrary lift.

Restricted to the field base the consumer actually has, it is now PROVEN, over the sharper
and entirely classical `universallyOpen_of_specField` — which is itself now proven outright
from `Mathlib`, so this whole path is sorry-free; see the CORRECTION in that declaration's
docstring, which retracts its own "not free at this pin" audit.  Everything else inside it —
that `m` is a base change of `j` (a pasting of pullback squares), that the range of a
pullback projection is the preimage of the range (`range_base_of_isPullback`, proven here by
transporting `Mathlib`'s `Scheme.Pullback.range_fst` along `IsPullback.isoPullback`), and the
open-image density argument — is proven here.

## Faithfulness

`IsSmoothCompactification` is deliberately a *bundle of properties of a given `(X, j)`*
rather than an existential, so that a consumer quantifying over all compactifications
(as `Fermat.IsCompactificationY0` and `Fermat.IsX0Compactification` do) states something
at least as strong as the one about a chosen model.  Uniqueness up to unique isomorphism
is true and classical but is **not** stated here, because nothing consumes it; adding it
would be free-floating.

`PerfectField K` is load-bearing in step 4 and only there.  Over an imperfect field the
normalization of a curve can be regular without being smooth, so the theorem as stated is
false without it; `ℚ` is perfect, which is all the modular application needs.

## Relation to `Modularity/KhareWintenberger.lean` — READ BEFORE PROVING ANY LEAF HERE

That module independently states the SAME construction as its LEAF A/B/C
(`exists_quasiFinite_toProper_of_isAffine_finiteType`,
`isFinite_fromNormalization_of_smooth_affine`, and the smoothness of the normalized
model), in the special case of an **affine** `C` over `Spec (ULift ℚ)`.  Those three are
exactly `exists_isOpenImmersion_isProper`, `isFinite_fromNormalization` and
`smoothOfRelativeDimension_one_fromNormalization` below, specialised.

**Its LEAF A is now REDUNDANT (2026-07-27)**: `exists_quasiFinite_toProper_of_isAffine_finiteType`
is the affine case, and the affine case is PROVEN here as
`exists_isOpenImmersion_isProper_of_isAffine`, modulo the two purely ring-theoretic chart
leaves.  It should be re-derived from that rather than attacked.

Neither file can use the other today — `X0.lean` and `KhareWintenberger.lean` are
siblings, both importing only `Modularity/AbelianScheme.lean`, and neither imports the
other.  This module sits UPSTREAM of both, which is why it is in the shim tree rather than
in either consumer.  **The two sets should be unified here**, with the
`KhareWintenberger` leaves re-derived as corollaries; that is a follow-up for an owner of
that file, not something to do from this side (its leaves carry hypotheses tuned to its
own consumer).  Whoever proves a leaf here should say so on that file's copy, and vice
versa, so the same theorem is not proven twice.

**Message for that file's owner (2026-07-27)**: its `isFinite_fromNormalization_of_smooth_affine`
should NOT be attacked as stated.  `IsIntegralHom` of a relative normalization is free in
`Mathlib`, so by `IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` the whole content is
finite-*type*-ness — see `locallyOfFiniteType_fromNormalization` below, and
`isFinite_fromNormalization`, which is now a two-line consequence of it.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Order

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

/-! ### Topological preliminaries

Two statements of pure general topology, kept inside `AlgebraicGeometry` rather than at the
root so that this module adds no root-level names to the cone of everything that
`public import`s it.  Both are stated for an arbitrary topological space and would be
`Mathlib`-ready after a hoist. -/

/-- **In an irreducible sober noetherian space of Krull dimension at most one, every proper
closed subset is finite.**

This is the whole topological content of `finite_compl_range_toNormalization` below.  The
argument: a noetherian space writes any closed `Z` as a *finite* union of irreducible closed
sets (`NoetherianSpace.exists_finite_set_isClosed_irreducible`); such a piece `t` is not the
whole space, so it is not maximal in `IrreducibleCloseds α`, so `krullDim ≤ 1` forces it to be
*minimal*; a minimal irreducible closed set contains the closure of each of its points, hence
each of its points is a generic point of it, hence — by sobriety and `T0` — it is a single
point. -/
theorem finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one
    {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α] [T0Space α]
    [IrreducibleSpace α] (hdim : topologicalKrullDim α ≤ 1)
    {Z : Set α} (hZc : IsClosed Z) (hZ : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZc
  refine hSf.sUnion fun t ht => ?_
  have htu : t ≠ Set.univ := fun h => hZ (Set.eq_univ_of_univ_subset
    (h ▸ Set.subset_sUnion_of_mem ht))
  have hti : IsIrreducible t := hSirr t ht
  have htc : IsClosed t := hScl t ht
  let W : IrreducibleCloseds α := ⟨t, hti, htc⟩
  let T : IrreducibleCloseds α :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ α, isClosed_univ⟩
  have hWT : W < T := by
    refine lt_of_le_of_ne (Set.subset_univ t) fun h => htu ?_
    exact congrArg (fun (u : IrreducibleCloseds α) => (u : Set α)) h
  have hmin : IsMin W := by
    rcases (krullDim_le_one_iff (α := IrreducibleCloseds α)).mp hdim W with h | h
    · exact h
    · exact absurd (h hWT.le) hWT.not_ge
  obtain ⟨w, hw⟩ := QuasiSober.sober hti htc
  have hsingleton : t = {w} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hw.mem, fun v hv => ?_⟩
    let V : IrreducibleCloseds α :=
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hVW : V ≤ W := htc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hv)
    have hWV : (t : Set α) ⊆ closure {v} := hmin hVW
    exact IsGenericPoint.eq (show IsGenericPoint v t from le_antisymm hVW hWV) hw
  exact hsingleton ▸ Set.finite_singleton w

/-- **A space with a dense connected image is connected.**

The closure of a connected subset is connected, and a dense range has closure everything.
This is the topological half of
`geometricallyConnected_of_isSmoothCompactification` below. -/
theorem connectedSpace_of_denseRange {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [ConnectedSpace β] {f : β → α} (hf : Continuous f) (hd : DenseRange f) :
    ConnectedSpace α := by
  rw [connectedSpace_iff_univ, ← hd.closure_eq]
  exact (isConnected_range hf).closure

/-- **`strX : X ⟶ S` together with `j : Y ⟶ X` is a smooth compactification of
`strY : Y ⟶ S`.**

`Y` sits inside `X` as a dense open subscheme with finite complement, and `X` is a smooth
proper curve over the base.  This is the interface `Fermat.IsCompactificationY0` and
`Fermat.IsX0Compactification` are instances of.

`isDominant` (density) and `finite_compl` are not redundant with each other: density says
the closure of `Y` is all of `X`, finiteness of the complement says `X ∖ Y` is a finite
set of closed points.  On an irreducible curve each follows from the other, but the
structure does not assume irreducibility, and both are what the cusp count downstream
consumes. -/
structure IsSmoothCompactification {Y X S : Scheme.{u}} (strY : Y ⟶ S) (strX : X ⟶ S)
    (j : Y ⟶ X) : Prop where
  /-- `j` is a morphism over the base -/
  comm : j ≫ strX = strY
  /-- `Y` is an open subscheme of `X` -/
  isOpenImmersion : IsOpenImmersion j
  /-- `Y` is dense in `X` -/
  isDominant : IsDominant j
  /-- `X` is proper over the base -/
  isProper : IsProper strX
  /-- `X` is a smooth curve over the base -/
  smooth : SmoothOfRelativeDimension 1 strX
  /-- the complement of `Y` in `X` is finite -/
  finite_compl : (Set.range j.base)ᶜ.Finite

/-! ### The four leaves -/

/-! #### Nagata compactification, decomposed (2026-07-27)

`exists_isOpenImmersion_isProper` below is no longer a citation: it is PROVEN from three
sharper leaves, two of which are pure commutative algebra.  The route is the classical one
for a scheme over a field, and it exists here only because `Mathlib` turns out to carry the
one hard geometric input — `AlgebraicGeometry.Proj.instIsProperToSpecZero`, the properness
of `Proj 𝒜` over `Spec 𝒜₀` for `𝒜` a finite-type graded algebra
(`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`, proven there by the valuative
criterion).  Every previous audit of this leaf recorded "`Proj` exists only as
`ProjectiveSpectrum` of a graded ring, with no closure-of-a-quasi-projective-scheme API",
which is true of the *closure* and false of the *properness*; the properness is the part
one cannot write oneself.

The three pieces:

* `nonempty_projChart_mvPolynomial` (PROVEN 2026-07-27) — the standard affine chart of `ℙⁿ`:
  dehomogenisation at `X₀`, now a theorem over the single arithmetic leaf
  `eq_zero_of_isHomogeneous_of_dehomogenisation`, which is itself proven;
* `nonempty_projChart_of_surjective` (LEAF) — the projective closure: a chart for `B'`
  descends along a surjection `B' ↠ B`;
* `exists_isOpenImmersion_isProper_of_affineCase` (LEAF) — Nagata's gluing induction, which
  is the only piece that is still Nagata's theorem proper.

Everything joining them is proven here.  Note the same `Proj`-chart pattern (a
`HomogeneousLocalization.Away` identified with a concrete ring, together with the commuting
triangle out of the base field) is already used by
`Fermat/FLT/ModularCurve/EllipticScheme.lean` for the projective Weierstrass model, whose
`exists_projChartRingEquiv` is the Weierstrass instance of `nonempty_projChart_mvPolynomial`
composed with `nonempty_projChart_of_surjective`.  Whoever proves one should look at the
other; the second file's docstring carries a proof plan for the dehomogenisation isomorphism
(surjectivity from `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`, the kernel by a
UFD divisibility argument).  **That plan is now superseded on this side**: see the docstring
of `nonempty_projChart_mvPolynomial` below, which builds the map DOWNWARD by
`Localization.awayLift` out of `aeval (Fin.cons 1 X)` and so gets surjectivity from an explicit
section rather than from `adjoin_mk_prod_pow_eq_top`.  The same reversal should apply there. -/

/-- For an affine `Y` and an affine target, a morphism is recovered from its ring map:
`g = Y.isoSpec.hom ≫ Spec.map (Γ g)`.  This is `Scheme.isoSpec_hom_naturality` with the
target's own `isoSpec` cancelled away, which is what every consumer here wants. -/
theorem eq_isoSpec_hom_comp_specMap {Y : Scheme.{u}} [IsAffine Y] (R : CommRingCat.{u})
    (g : Y ⟶ Spec R) :
    g = Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality g, Category.assoc,
    Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- **A projective chart for a `K`-algebra `B`**: a presentation of `Spec B` as the standard
affine open `D₊(f)` of a `Proj` that is proper over `Spec K`.

The data is a finitely generated graded `K`-algebra `A = ⨁ 𝒜ᵢ` whose degree-zero part is a
finite `K`-module, a degree-one element `f`, and an identification of the degree-zero part
of the localisation `A_f` with `B`, compatible with the two structure maps out of `K`.
Given one, `Proj 𝒜` is a proper `K`-scheme containing `Spec B` as an open subscheme —
that is `exists_isOpenImmersion_isProper_of_proj` below.

Two deliberate choices, both learned expensively elsewhere in this development:

* `zeroFinite : Module.Finite K ↥(grading 0)` rather than `grading 0 ≅ K`.  The weaker
  hypothesis is all that properness needs (`Spec (𝒜₀) ⟶ Spec K` is then finite, hence
  proper), and it is what makes the DEGENERATE case `B = 0` fall out uniformly: the
  projective closure of the empty scheme has `𝒜₀ = 0`, which is finite over `K` but is not
  isomorphic to it.  A chart demanding `𝒜₀ ≅ K` would make
  `nonempty_projChart_of_surjective` FALSE for the zero ring.
* the identification is a `CommRingCat` iso plus a commuting triangle, not an `AlgEquiv`.
  The source carries an `Algebra ↥(𝒜 0)` instance and the target an `Algebra K` one, and
  forcing them into one `Algebra K` structure is exactly the "two defeq but never
  syntactically equal instances" trap — the same reasoning as in
  `Fermat.exists_projChartRingEquiv`. -/
structure ProjChart (K : Type u) [Field K] (B : CommRingCat.{u})
    (b : CommRingCat.of K ⟶ B) where
  /-- the homogeneous coordinate ring -/
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra K A]
  /-- its grading -/
  grading : ℕ → Submodule K A
  [gradedAlgebra : GradedAlgebra grading]
  [finiteType : Algebra.FiniteType ↥(grading 0) A]
  [zeroFinite : Module.Finite K ↥(grading 0)]
  /-- the degree-one element cutting out the chart -/
  f : A
  /-- `f` has degree one -/
  f_deg : f ∈ grading 1
  /-- the chart `D₊(f)` is `Spec B` -/
  awayIso : CommRingCat.of (HomogeneousLocalization.Away grading f) ≅ B
  /-- the identification is compatible with the structure maps out of `K` -/
  compat : CommRingCat.ofHom (algebraMap K ↥(grading 0)) ≫
    CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers f)) ≫
      awayIso.hom = b

/-- **A projective chart compactifies an affine scheme** (PROVEN).

`Proj 𝒜` is proper over `Spec 𝒜₀` (`Mathlib`, by the valuative criterion) and `𝒜₀` is finite
over `K`, so `Proj 𝒜 ⟶ Spec K` is proper; `Spec (A_f)₀ ⟶ Proj 𝒜` is an open immersion
(`Mathlib`'s `Proj.awayι`); and the triangle commutes by `Proj.awayι_toSpecZero` together
with the chart's own `compat`.  Quasi-compactness of the immersion is then free: the
composite is `strY`, which is quasi-compact because `Y` is affine, and the proper `strP` is
quasi-separated, so `QuasiCompact.of_comp` applies.

Everything in this proof is `Mathlib`; the content of the compactification is entirely in
producing the chart. -/
theorem exists_isOpenImmersion_isProper_of_proj {Y : Scheme.{u}} [IsAffine Y]
    (strY : Y ⟶ Spec (CommRingCat.of K))
    (A : Type u) [CommRing A] [Algebra K A] (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
    [Algebra.FiniteType ↥(𝒜 0) A] [Module.Finite K ↥(𝒜 0)] (f : A) (hf : f ∈ 𝒜 1)
    (e : CommRingCat.of (HomogeneousLocalization.Away 𝒜 f) ≅ Γ(Y, ⊤))
    (hcomp : CommRingCat.ofHom (algebraMap K ↥(𝒜 0)) ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫
          e.hom
        = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strY.appTop) :
    ∃ (P : Scheme.{u}) (strP : P ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ P),
      IsOpenImmersion i ∧ QuasiCompact i ∧ IsProper strP ∧ i ≫ strP = strY := by
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K ↥(𝒜 0)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hiso : IsIso e.hom := inferInstance
  have hcomm : (Y.isoSpec.hom ≫ Spec.map e.hom ≫ Proj.awayι 𝒜 f hf one_pos) ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K ↥(𝒜 0)))) = strY := by
    simp only [Category.assoc]
    rw [← Category.assoc (Proj.awayι 𝒜 f hf one_pos), Proj.awayι_toSpecZero 𝒜 f hf one_pos]
    simp only [← Spec.map_comp, Category.assoc]
    rw [hcomp]
    exact (eq_isoSpec_hom_comp_specMap _ strY).symm
  have hqcY : QuasiCompact strY :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := strY)).mpr inferInstance
  refine ⟨Proj 𝒜, Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K ↥(𝒜 0))),
    Y.isoSpec.hom ≫ Spec.map e.hom ≫
      Proj.awayι 𝒜 f hf one_pos, inferInstance, ?_, inferInstance, hcomm⟩
  have h3 : QuasiCompact ((Y.isoSpec.hom ≫ Spec.map e.hom ≫
      Proj.awayι 𝒜 f hf one_pos) ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K ↥(𝒜 0))))) := by
    rw [hcomm]; exact hqcY
  have h4 : IsProper (Proj.toSpecZero 𝒜 ≫
    Spec.map (CommRingCat.ofHom (algebraMap K ↥(𝒜 0)))) := inferInstance
  have h5 : QuasiSeparated (Proj.toSpecZero 𝒜 ≫
    Spec.map (CommRingCat.ofHom (algebraMap K ↥(𝒜 0)))) := inferInstance
  exact QuasiCompact.of_comp (Y.isoSpec.hom ≫ Spec.map e.hom ≫ Proj.awayι 𝒜 f hf one_pos)
    (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K ↥(𝒜 0))))

section ProjChartMvPolynomial

open _root_.MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Dehomogenisation is injective on homogeneous polynomials**: if `a ∈ K[X₀, …, Xₙ]` is
homogeneous of degree `k` and `a(1, Y₁, …, Yₙ) = 0`, then `a = 0`.

This is the whole arithmetic content of `nonempty_projChart_mvPolynomial` below, and it is
what makes the dehomogenisation map an ISOMORPHISM rather than merely a surjection.

The proof goes through `MvPolynomial.finSuccEquiv`, which presents `K[X₀, …, Xₙ]` as
`(K[Y₁, …, Yₙ])[X₀]`, and through `Mathlib`'s
`MvPolynomial.IsHomogeneous.finSuccEquiv_coeff_isHomogeneous`: the `X₀`-coefficient of index
`i` of a form of degree `k` is homogeneous of degree `k - i`, and vanishes for `i > k`.
Setting `X₀ = 1` is `Polynomial.eval 1`, so the hypothesis says exactly that the sum of those
coefficients is zero — a sum of homogeneous polynomials of PAIRWISE DISTINCT degrees `k - i`.
Applying `MvPolynomial.homogeneousComponent (k - i)` picks off each one, so every coefficient
vanishes and `a = 0`.

Note what this replaces: the audit on the old leaf proposed injectivity "by a UFD divisibility
argument" (copied from `Fermat.exists_projChartRingEquiv`, where the ideal is nonzero and such
an argument really is needed).  Here the ideal is zero and the grading alone does it, with no
divisibility and no unique factorisation. -/
theorem eq_zero_of_isHomogeneous_of_dehomogenisation {n k : ℕ}
    {a : MvPolynomial (Fin (n + 1)) K} (ha : a.IsHomogeneous k)
    (h : aeval (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) K) a = 0) :
    a = 0 := by
  classical
  have hdeg : ∀ (i : ℕ) (m : Fin n →₀ ℕ), (Finsupp.cons i m).degree = i + m.degree := by
    intro i m
    have hs := Finsupp.sum_cons n m i
    simpa [Finsupp.degree, Finsupp.sum] using hs
  set P := finSuccEquiv K n a with hP
  have hzero : ∀ i, k < i → P.coeff i = 0 := by
    intro i hi
    ext m
    rw [hP, finSuccEquiv_coeff_coeff]
    refine ha.coeff_eq_zero ?_
    rw [hdeg]
    omega
  have hhom : ∀ i, i ≤ k → (P.coeff i).IsHomogeneous (k - i) := fun i hi =>
    ha.finSuccEquiv_coeff_isHomogeneous i (k - i) (by omega)
  -- `aeval (Fin.cons 1 X)` is evaluation of `finSuccEquiv` at `1`
  have hev : ∀ b : MvPolynomial (Fin (n + 1)) K,
      aeval (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) K) b
        = Polynomial.eval 1 (finSuccEquiv K n b) := by
    have : ((Polynomial.evalRingHom (1 : MvPolynomial (Fin n) K)).comp
        (finSuccEquiv K n : MvPolynomial (Fin (n + 1)) K →+* _))
        = (aeval (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) K)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [finSuccEquiv_apply]
      · refine Fin.cases ?_ ?_ i
        · simp [finSuccEquiv_X_zero]
        · intro j; simp [finSuccEquiv_X_succ]
    intro b
    exact (congrArg (fun (F : MvPolynomial (Fin (n + 1)) K →+*
      MvPolynomial (Fin n) K) => F b) this).symm
  -- so the sum of the coefficients vanishes
  have hnd : P.natDegree < k + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hzero)
  have hsum : ∑ i ∈ Finset.range (k + 1), P.coeff i = 0 := by
    have h1 : Polynomial.eval 1 P = 0 := by rw [hP, ← hev]; exact h
    rw [Polynomial.eval_eq_sum_range' hnd] at h1
    simpa using h1
  -- picking off the homogeneous components
  have hcoeff : ∀ i ∈ Finset.range (k + 1), P.coeff i = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have := congrArg (homogeneousComponent (k - i)) hsum
    rw [map_sum, map_zero] at this
    rw [← this]
    rw [Finset.sum_eq_single i]
    · exact (homogeneousComponent_eq_self (hhom i (by omega))).symm
    · intro j hj hji
      rw [Finset.mem_range] at hj
      refine homogeneousComponent_of_mem (hhom j (by omega)) |>.trans ?_
      rw [if_neg]
      omega
    · intro hni
      exact absurd (Finset.mem_range.mpr (by omega : i < k + 1)) hni
  have hPzero : P = 0 := by
    refine Polynomial.ext fun i => ?_
    rcases le_or_gt i k with hik | hik
    · exact (hcoeff i (Finset.mem_range.mpr (by omega))).trans (Polynomial.coeff_zero i).symm
    · exact (hzero i hik).trans (Polynomial.coeff_zero i).symm
  exact (map_eq_zero_iff (finSuccEquiv K n) (finSuccEquiv K n).injective).mp (hP.symm.trans hPzero)

/-- **The standard affine chart of `ℙⁿ`** (PROVEN 2026-07-27, over the single arithmetic leaf
`eq_zero_of_isHomogeneous_of_dehomogenisation` above).

Take `A := K[X₀, …, Xₙ]` with its grading by total degree
(`MvPolynomial.homogeneousSubmodule`, whose `GradedAlgebra` instance is `MvPolynomial.gradedAlgebra`
— note it is an `abbrev`, not a global instance, so it has to be turned on locally) and `f := X₀`.
Then `𝒜₀ = 1` as a submodule (`MvPolynomial.homogeneousSubmodule_zero`), so `Module.Finite K 𝒜₀`
is `Submodule.fg_span_singleton`; `A` is generated over `𝒜₀` by the `n + 1` variables; and the
degree-zero part of `A[X₀⁻¹]` is `K[X₁/X₀, …, Xₙ/X₀] ≅ K[Y₁, …, Yₙ]` — dehomogenisation,
`Xᵢ ↦ Yᵢ`, `X₀ ↦ 1`.  Stacks tag `01M3`.

**How the identification is built, since the previous audit's route was harder than necessary.**
That audit said `Mathlib` has no identification of an away-localisation's degree-zero part with a
concrete polynomial ring — still true — and proposed getting surjectivity from
`HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` and injectivity from a UFD divisibility
argument.  Both halves are avoidable, and the map is built in the OTHER direction:

* `dh := aeval (Fin.cons 1 X) : A →ₐ[K] K[Y₁, …, Yₙ]` sends `X₀ ↦ 1`, so `dh X₀` is a unit and
  `dh` factors through `Localization.Away X₀` by `Localization.awayLift`.  Composing with
  `HomogeneousLocalization.val` gives `θ : 𝒜_(X₀) →+* K[Y₁, …, Yₙ]`, and
  `Localization.awayLift_mk` computes it on `Away.mk`: `θ (a / X₀ ^ j) = dh a`, with no
  bookkeeping about degrees at all.
* SURJECTIVITY is then free: `θ` has the explicit section `eval₂Hom` sending `Yᵢ ↦ Xᵢ₊₁ / X₀`,
  and `θ ∘ ψ = id` is checked on `C r` and on the `Yᵢ` by `MvPolynomial.ringHom_ext`.  No
  `adjoin_mk_prod_pow_eq_top`, and in particular none of the product-of-powers manipulation
  that route needs.
* INJECTIVITY is `HomogeneousLocalization.Away.mk_surjective` plus the leaf above.

The same pattern should transfer to `Fermat.exists_projChartRingEquiv`
(`Fermat/FLT/ModularCurve/EllipticScheme.lean`), whose docstring carries the older plan: build the
map DOWN by `awayLift` rather than up by generators, and only the kernel computation is left —
which there, unlike here, genuinely needs the Weierstrass ideal.

This is `Mathlib`-ready material: stated for an arbitrary base commutative ring it is the
standard affine cover of projective space. -/
theorem nonempty_projChart_mvPolynomial (n : ℕ) :
    Nonempty (ProjChart K (CommRingCat.of (MvPolynomial (Fin n) K))
      (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))) := by
  classical
  haveI hfin0 : Module.Finite K ↥(homogeneousSubmodule (Fin (n + 1)) K 0) := by
    have h0 : homogeneousSubmodule (Fin (n + 1)) K 0
        = (1 : Submodule K (MvPolynomial (Fin (n + 1)) K)) :=
      homogeneousSubmodule_zero (Fin (n + 1))
    rw [h0]
    refine Module.Finite.iff_fg.mpr ?_
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton 1
  haveI hft : Algebra.FiniteType ↥(homogeneousSubmodule (Fin (n + 1)) K 0)
      (MvPolynomial (Fin (n + 1)) K) := by
    refine ⟨⟨Finset.univ.image (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K), ?_⟩⟩
    rw [eq_top_iff]
    rintro p -
    induction p using MvPolynomial.induction_on with
    | C a =>
        have hmem : (C a : MvPolynomial (Fin (n + 1)) K)
            ∈ homogeneousSubmodule (Fin (n + 1)) K 0 := isHomogeneous_C _ a
        exact Subalgebra.algebraMap_mem _ (⟨C a, hmem⟩ :
          ↥(homogeneousSubmodule (Fin (n + 1)) K 0))
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
        exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (by simp))
  -- the dehomogenisation map
  set dh : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
    aeval (Fin.cons 1 X) with hdh
  have hdh0 : dh (X 0) = 1 := by simp [hdh]
  have hdhs : ∀ i : Fin n, dh (X i.succ) = X i := by intro i; simp [hdh]
  have hu : (dh : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K) (X 0) * 1 = 1 := by
    simpa using hdh0
  have hf : (X 0 : MvPolynomial (Fin (n + 1)) K) ∈ homogeneousSubmodule (Fin (n + 1)) K 1 :=
    isHomogeneous_X K 0
  -- the ring map out of the away-localisation
  set θ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n + 1)) K) (X 0) →+*
      MvPolynomial (Fin n) K :=
    (Localization.awayLift (dh : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K) (X 0)
      (isUnit_iff_exists_inv.mpr ⟨1, hu⟩)).comp (algebraMap _ _) with hθ
  have θ_mk : ∀ (j : ℕ) (a : MvPolynomial (Fin (n + 1)) K)
      (haj : a ∈ homogeneousSubmodule (Fin (n + 1)) K (j • 1)),
      θ (HomogeneousLocalization.Away.mk _ hf j a haj) = dh a := by
    intro j a haj
    rw [hθ]
    show Localization.awayLift (dh : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K)
      (X 0) (isUnit_iff_exists_inv.mpr ⟨1, hu⟩)
      (HomogeneousLocalization.Away.mk _ hf j a haj).val = _
    rw [HomogeneousLocalization.Away.val_mk, Localization.awayLift_mk _ _ _ 1 hu]
    simp
  -- `θ` is surjective, because it has a section on the polynomial generators
  have hXs : ∀ i : Fin n, (X i.succ : MvPolynomial (Fin (n + 1)) K)
      ∈ homogeneousSubmodule (Fin (n + 1)) K (1 • 1) := by
    intro i
    simpa using isHomogeneous_X K i.succ
  have hC0 : ∀ r : K, (C r : MvPolynomial (Fin (n + 1)) K)
      ∈ homogeneousSubmodule (Fin (n + 1)) K (0 • 1) := by
    intro r
    simp
  set cmap : K →+* HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n + 1)) K) (X 0) :=
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (n + 1)) K) _).comp
      (algebraMap K ↥(homogeneousSubmodule (Fin (n + 1)) K 0)) with hcmap
  have hc : ∀ r : K, cmap r
      = HomogeneousLocalization.Away.mk _ hf 0 (C r) (hC0 r) := by
    intro r
    rw [HomogeneousLocalization.ext_iff_val]
    simp [hcmap, HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.Away.mk,
      algebraMap_eq]
  set ψ : MvPolynomial (Fin n) K →+*
      HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n + 1)) K) (X 0) :=
    eval₂Hom cmap (fun i => HomogeneousLocalization.Away.mk _ hf 1 (X i.succ) (hXs i)) with hψ
  have hθψ : ∀ p, θ (ψ p) = p := by
    have : θ.comp ψ = RingHom.id (MvPolynomial (Fin n) K) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · show θ (ψ (C r)) = C r
        rw [hψ, eval₂Hom_C, hc, θ_mk]
        simp [hdh]
      · show θ (ψ (X i)) = X i
        rw [hψ, eval₂Hom_X', θ_mk]
        exact hdhs i
    exact fun p => congrArg (fun (F : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K) => F p) this
  have hsurj : Function.Surjective θ := fun p => ⟨ψ p, hθψ p⟩
  have hinj : Function.Injective θ := by
    refine (injective_iff_map_eq_zero θ).mpr ?_
    intro z hz
    obtain ⟨j, a, haj, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hf z
    rw [θ_mk] at hz
    have ha : a.IsHomogeneous j := by simpa using haj
    have : a = 0 := eq_zero_of_isHomogeneous_of_dehomogenisation ha (by simpa [hdh] using hz)
    subst this
    exact HomogeneousLocalization.mk_eq_zero_of_num _ rfl
  exact ⟨{ A := MvPolynomial (Fin (n + 1)) K
           grading := homogeneousSubmodule (Fin (n + 1)) K
           f := X 0
           f_deg := hf
           awayIso := (RingEquiv.ofBijective θ ⟨hinj, hsurj⟩).toCommRingCatIso
           compat := by
             refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
             show θ (cmap r) = _
             rw [hc, θ_mk]
             simp [hdh] }⟩

end ProjChartMvPolynomial

/-- **Projective closure: a chart descends along a surjection** (sorry leaf).

TRUE and classical.  Given a chart `(A', 𝒜', f')` for `B'` and a surjection `q : B' ↠ B`,
let `I ⊆ A'` be the homogeneous ideal whose degree-`d` part is
`{a ∈ 𝒜'_d : q(a / f'^d) = 0}` — the homogeneous vanishing ideal of the closed subscheme
`Spec B ⊆ Spec B'` — and take `A := A' ⧸ I` with the induced grading and `f :=` the image of
`f'`.  Geometrically `Proj A` is the SCHEME-THEORETIC CLOSURE of `Spec B` inside `Proj A'`,
which is exactly the classical construction of the projective closure of an affine variety
(Stacks tag `01MZ`, Hartshorne I.2.9 in the classical language).

The obligations are: `I` is a homogeneous ideal; `A ⧸ I` is still of finite type over its
degree-zero part (a quotient of a finite-type algebra is); `Module.Finite K (𝒜 0)` — here
`𝒜₀ = 𝒜'₀ ⧸ I₀` is a quotient of a finite `K`-module; and
`(A_f)₀ ≅ (A'_{f'})₀ ⧸ (that ideal) ≅ B`, which is where the surjectivity of `q` and the
saturation built into `I` are consumed.

**The degenerate case is real and is the reason `ProjChart` asks only for
`Module.Finite K 𝒜₀`.**  If `B = 0` then `I = A'` and `A = 0`, so `𝒜₀ = 0`; that is finite
over `K` but NOT isomorphic to `K`.  (A chart still exists for `B = 0` by other means —
`A := K` concentrated in degree zero and `f := 0`, whose away-localisation is the zero ring
by `HomogeneousLocalization.subsingleton` — but the uniform construction is the one above,
and it only works because the chart does not demand `𝒜₀ ≅ K`.)

`Mathlib` has no Nagata/Japanese-ring theory and no projective closure at this pin; it does
have `HomogeneousIdeal`, `GradedRing`, and the quotient grading, which is what this is to be
built from.

**A CHEAPER ROUTE THAN THE SATURATED IDEAL ABOVE (2026-07-27, from the author of
`nonempty_projChart_mvPolynomial`, which closed by an analogous reversal).**  Do not construct
`I` and prove it saturated; construct `A` as an IMAGE instead, and the saturation is what you
get for free rather than what you have to prove.

Grade `B[t]` (a one-variable polynomial ring over `B`) by `t`-degree, and define a GRADED
`K`-algebra map `Φ : A' → B[t]` by sending `a ∈ 𝒜'_d` to `q (C.awayIso ⟦a / f'^d⟧) · t^d`.  It
is multiplicative because `(ab)/f'^{d+e} = (a/f'^d)(b/f'^e)` in the away-localisation, and
additive within each degree; so it is determined on the `GradedRing` decomposition of `A'`.
Take `A := Φ.range` with the induced grading and `f := Φ f' = t` (note `f'/f' = 1`, so
`Φ f' = q 1 · t = t`, giving `f ∈ 𝒜 1` on the nose).  Then:

* `Algebra.FiniteType 𝒜₀ A` and `Module.Finite K 𝒜₀` are inherited from `A'` because `A` is a
  quotient of `A'` and `𝒜₀` a quotient of `𝒜'₀` — no separate argument for either;
* `(A_f)₀ = B` **by construction**: `(A_t)₀ = {a/t^d : a ∈ 𝒜_d}` is exactly the union over `d`
  of `q (C.awayIso ⟦𝒜'_d / f'^d⟧)`, which is `q '' B' = B` since `q` is surjective and
  `B' = (A'_{f'})₀`.  Surjectivity is where `q` is consumed and injectivity is by construction
  of the image — the two places the saturated-ideal route needs real work;
* the DEGENERATE case is automatic: for `B = 0`, `q 1 = 0` so `A = 0` and `𝒜₀ = 0`, which is
  finite over `K` and not `≅ K` — exactly the reason `ProjChart` asks only for
  `Module.Finite K 𝒜₀`.

**The check that would refute this note**: that `Φ` cannot be assembled as a ring hom from its
degreewise pieces at this pin.  It is assembled from `DirectSum.toSemiring` / the `GradedRing`
decomposition of `A'`, and the degreewise pieces are `HomogeneousLocalization.Away.mk` composed
with `C.awayIso.hom` and `q`; if that assembly is genuinely unavailable, the note is wrong and
the saturated-ideal route stands. -/
theorem nonempty_projChart_of_surjective {B B' : CommRingCat.{u}}
    {b' : CommRingCat.of K ⟶ B'} (_C : ProjChart K B' b') (q : B' ⟶ B)
    (_hq : Function.Surjective q.hom) : Nonempty (ProjChart K B (b' ≫ q)) :=
  sorry

/-- **Every finite-type `K`-algebra has a projective chart** (PROVEN over the two leaves
above).

A finite-type algebra is a quotient of a polynomial ring
(`Algebra.FiniteType.iff_quotient_mvPolynomial''`), so the chart of `ℙⁿ` descends to it.
This is the whole of the affine case of Nagata's theorem over a field. -/
theorem nonempty_projChart (B : CommRingCat.{u}) (b : CommRingCat.of K ⟶ B)
    (hb : RingHom.FiniteType b.hom) : Nonempty (ProjChart K B b) := by
  letI : Algebra K B := b.hom.toAlgebra
  haveI : Algebra.FiniteType K B := hb
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType K B›
  obtain ⟨C⟩ := nonempty_projChart_mvPolynomial (K := K) n
  have hb' : CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)) ≫
      CommRingCat.ofHom (φ : MvPolynomial (Fin n) K →+* B) = b := by
    ext x; exact φ.commutes x
  rw [← hb']
  exact nonempty_projChart_of_surjective C _ hφ

/-- **Nagata's theorem for an AFFINE scheme of finite type over a field** (PROVEN).

This is the case that `Modularity/KhareWintenberger.lean` states independently as its
`exists_quasiFinite_toProper_of_isAffine_finiteType`; that leaf is now redundant with this
one and should be re-derived from it (its `C` is affine over `Spec (ULift ℚ)`). -/
theorem exists_isOpenImmersion_isProper_of_isAffine {Y : Scheme.{u}} [IsAffine Y]
    (strY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType strY] :
    ∃ (P : Scheme.{u}) (strP : P ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ P),
      IsOpenImmersion i ∧ QuasiCompact i ∧ IsProper strP ∧ i ≫ strP = strY := by
  set b : CommRingCat.of K ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strY.appTop
    with hb
  have hSpec : Spec.map b = Y.isoSpec.inv ≫ strY := by
    rw [Iso.eq_inv_comp]
    exact (eq_isoSpec_hom_comp_specMap _ strY).symm
  have hft : LocallyOfFiniteType (Spec.map b) := by rw [hSpec]; infer_instance
  obtain ⟨C⟩ := nonempty_projChart (K := K) _ b
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  letI := C.commRing
  letI := C.algebra
  letI := C.gradedAlgebra
  letI := C.finiteType
  letI := C.zeroFinite
  exact exists_isOpenImmersion_isProper_of_proj strY C.A C.grading C.f C.f_deg C.awayIso
    C.compat

/-- **Nagata's gluing induction: the affine case implies the general case** (sorry leaf).

TRUE and classical, and this is the only part of the decomposition that is still Nagata's
theorem proper: Nagata (1962), Deligne's notes as written up by Conrad, Lütkebohmert
(1993), Temkin; Stacks tags `0F3T`–`0F41`.  A quasi-compact separated finite-type `Y` has a
FINITE affine open cover, and the induction is on its size: given compactifications of
`U = U₁ ∪ ⋯ ∪ Uₖ₋₁` and of the affine `V = Uₖ`, one produces a compactification of `U ∪ V`
by blowing up along the boundary and gluing the two proper models along the closure of the
graph over `U ∩ V`.  Nothing of this is in `Mathlib` and nothing of it is in this project.

`H` is the affine case, which is PROVEN here — see
`exists_isOpenImmersion_isProper_of_isAffine`.  Passing it as a hypothesis rather than
using it directly is what makes this leaf strictly the gluing content and nothing else.

Note that the induction genuinely needs blowups (equivalently, scheme-theoretic images of
non-quasi-compact opens): the naive "glue the two closures along `U ∩ V`" fails because the
two proper models need not agree there.  That is the whole reason Nagata's theorem was open
for so long and why Deligne's write-up exists. -/
theorem exists_isOpenImmersion_isProper_of_affineCase {Y : Scheme.{u}}
    (strY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact strY] [IsSeparated strY]
    [LocallyOfFiniteType strY]
    (_H : ∀ (Z : Scheme.{u}) (strZ : Z ⟶ Spec (CommRingCat.of K)), IsAffine Z →
      LocallyOfFiniteType strZ → ∃ (P : Scheme.{u}) (strP : P ⟶ Spec (CommRingCat.of K))
        (i : Z ⟶ P), IsOpenImmersion i ∧ QuasiCompact i ∧ IsProper strP ∧ i ≫ strP = strZ) :
    ∃ (P : Scheme.{u}) (strP : P ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ P),
      IsOpenImmersion i ∧ QuasiCompact i ∧ IsProper strP ∧ i ≫ strP = strY :=
  sorry

/-- **Nagata's compactification theorem, for a quasi-compact separated finite-type scheme
over a field** (PROVEN over the three leaves above — no longer a citation).

Any separated finite-type morphism to a quasi-compact quasi-separated base factors as an
open immersion followed by a proper morphism.  Nagata (1962); Stacks tag `0F41`.

Note what is NOT claimed: `P` is **not** asserted normal, smooth, or even reduced.  That
is the whole point of routing through the normalization afterwards — Nagata's `P` is an
arbitrary proper model, and steps 3–4 of the module docstring repair it.

`QuasiCompact i` is part of the conclusion rather than derived: an open immersion need not
be quasi-compact in general, and every consumer here needs it (Zariski's Main Theorem takes
it as a hypothesis).  In the affine case it is free (see
`exists_isOpenImmersion_isProper_of_proj`); in general it is carried through the
induction. -/
theorem exists_isOpenImmersion_isProper {Y : Scheme.{u}}
    (strY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact strY] [IsSeparated strY]
    [LocallyOfFiniteType strY] :
    ∃ (P : Scheme.{u}) (strP : P ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ P),
      IsOpenImmersion i ∧ QuasiCompact i ∧ IsProper strP ∧ i ≫ strP = strY :=
  exists_isOpenImmersion_isProper_of_affineCase strY fun _ strZ hZ hft => by
    letI := hZ; letI := hft
    exact exists_isOpenImmersion_isProper_of_isAffine strZ

/-! ### E. Noether's finiteness theorem for the normalization

The two ring-theoretic statements below are what `finiteType_integralClosure_sections` is
really about; they are kept inside `AlgebraicGeometry` for the same reason as the
topological preliminaries above — so that this module adds no root-level names to the cone
of everything that `public import`s it. -/

/-- Transfer of finite generation of a submodule between two base rings whose images in the
ambient ring `X` are nested: if every element of `X` in the image of `S` is already in the
image of `R`, then an `S`-submodule and an `R`-submodule with the SAME CARRIER are finitely
generated together.

This is the workhorse that lets the reductions below change the base ring of an integral
closure without ever building a linear equivalence between the two subtypes
`↥(integralClosure R X)` and `↥(integralClosure S X)`, which are different types carrying the
same set.

HOISTED 2026-07-27 from `Fermat/FLT/Modularity/MoretBailly.lean` (which carries the
characteristic-zero twin of Noether's theorem and proves the same lemma for it): it is pure
module theory, characteristic-free, and it belongs in the shim tree.  The only change is that
the three carriers here live in independent universes rather than a common `Type u`. -/
theorem fg_of_algebraMap_range_le {R S X : Type*} [CommRing R] [CommRing S] [CommRing X]
    [Algebra R X] [Algebra S X]
    (hle : (algebraMap S X).range ≤ (algebraMap R X).range)
    {N : Submodule S X} {M : Submodule R X}
    (hcar : (N : Set X) = (M : Set X)) (hN : N.FG) : M.FG := by
  obtain ⟨T, hT⟩ := hN
  refine ⟨T, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro t ht
    have h1 : t ∈ N := hT ▸ Submodule.subset_span ht
    have h2 : t ∈ (N : Set X) := h1
    rw [hcar] at h2
    exact h2
  · have key : ∀ x ∈ N, x ∈ Submodule.span R (T : Set X) := by
      intro x hxN
      rw [← hT] at hxN
      induction hxN using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span hy
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | smul c a _ ha =>
          obtain ⟨r, hr⟩ := hle ⟨c, rfl⟩
          have hcr : c • a = r • a := by
            rw [Algebra.smul_def, Algebra.smul_def, hr]
          rw [hcr]
          exact Submodule.smul_mem _ _ ha
    intro x hx
    refine key x ?_
    have h2 : x ∈ (M : Set X) := hx
    rw [← hcar] at h2
    exact h2

/-- The subalgebra form of `fg_of_algebraMap_range_le`: two subalgebras of `X` over different
base rings, with the same carrier, are module-finite together as soon as the image of the
smaller base ring is contained in that of the larger.  HOISTED with the lemma above. -/
theorem module_finite_of_algebraMap_range_le {R S X : Type*} [CommRing R] [CommRing S]
    [CommRing X] [Algebra R X] [Algebra S X]
    (hle : (algebraMap S X).range ≤ (algebraMap R X).range)
    (N : Subalgebra S X) (M : Subalgebra R X)
    (hcar : (N : Set X) = (M : Set X)) (hN : Module.Finite S N) : Module.Finite R M := by
  have h1 : (Subalgebra.toSubmodule N).FG := Module.Finite.iff_fg.mp (by exact hN)
  have h2 : (Subalgebra.toSubmodule M).FG := fg_of_algebraMap_range_le hle (by simpa using hcar) h1
  exact Module.Finite.iff_fg.mpr h2

open _root_.IntermediateField _root_.Polynomial in
/-- **A normal extension splits purely-inseparable-FIRST** (cut 2026-07-28 as one of the two
residues of E. Noether's finiteness theorem, and **PROVEN the same day** — it was a leaf for
about an hour, so do not dispatch at it).

`N / K` is a FINITE NORMAL extension.  Then `N` is SEPARABLE over the relative perfect closure
`perfectClosure K N` (`Mathlib`'s maximal purely inseparable subextension, over which `K` is
purely inseparable for free by `perfectClosure.isPurelyInseparable`).  So a normal extension
factors as *purely inseparable, then separable* — the order OPPOSITE to the one `Mathlib`
supplies.

**Why this statement exists at all, and why normality is not decoration.**  The pin gives the split
in the other order and only in that order: `separableClosure.isPurelyInseparable` says `N` is
purely inseparable over `separableClosure K N` for any algebraic `N / K`.  That order is useless
for E. Noether's theorem, because the separable step MOVES THE BASE off the polynomial ring —
`integralClosure A₀ (separableClosure K L)` is a general normal finite-type `k`-algebra — and
the classical proof of the inseparable step (see
`module_finite_integralClosure_mvPolynomial_of_isPurelyInseparable` below) genuinely needs a
POLYNOMIAL base.  Taking the inseparable step FIRST keeps the base at `A₀`, and that is exactly
what this theorem buys.

NORMALITY is load-bearing and is not a convenience hypothesis: it is what makes the Galois action
transitive on the roots of a minimal polynomial, which is the ONLY step of the proof below that
uses it.  (The pin's opposite-order split needs no normality precisely because it is the easy
order — `separableClosure K N` is defined by a separability condition on elements, whereas the
purely inseparable closure has to be recognised as a fixed field.)  The general finite `N / K` is
NOT covered: this docstring deliberately does not assert a counterexample, since none was
verified here — treat "false without `Normal`" as the expected state of affairs rather than as a
checked fact.

**The proof** (Bourbaki *Algèbre* A.V §7 no. 6; Stacks `04KW` for the Galois-theoretic
form).  Let `G = Aut(N / K)`, finite because `N / K` is finite.  Artin's theorem — in the pin as
`FixedPoints.isSeparable` (`Mathlib/FieldTheory/Fixed.lean`) — gives `N` separable over the fixed
field `N^G`.  So it suffices that `N^G ≤ perfectClosure K N`, i.e. that every `G`-fixed element
is purely inseparable over `K`; and that is where NORMALITY enters: for `x ∈ N^G` the minimal
polynomial `minpoly K x` splits in `N`, `G` acts transitively on its roots (lift a
`K⟮x⟯ →ₐ[K] N` through `AlgHom.liftNormal`), and every root is therefore `x` itself, so
`(minpoly K x).natSepDegree = 1` and `mem_perfectClosure_iff_natSepDegree_eq_one` applies.  The
converse inclusion `perfectClosure K N ≤ N^G` is free (Frobenius is injective) and is NOT what
is needed here — note the direction, since separability transfers UP a tower, not down.

Two notes for anyone editing this.  (i) The fixed field is taken as `FixedPoints.subfield` (a
`Subfield`) rather than `IntermediateField.fixedField ⊤`, because that is the spelling Artin's
theorem is stated against in the pin; the transport to `perfectClosure K N` is then a bare
`RingHom` between the two subtypes plus `Algebra.isSeparable_tower_top_of_isSeparable`, and needs
no `IsGalois`.  (ii) `IsIntegral` and `IsNoetherian` must be written `_root_.IsIntegral` /
`_root_.IsNoetherian` in this file — `AlgebraicGeometry` has SCHEME-valued declarations of both
names, and the resulting error reads `expected to have type Scheme` — but `Normal`,
`perfectClosure` and `Splits` do not clash. -/
theorem isSeparable_perfectClosure_of_normal (K N : Type*) [Field K] [Field N] [Algebra K N]
    [FiniteDimensional K N] [Normal K N] :
    Algebra.IsSeparable ↥(perfectClosure K N) N := by
  classical
  haveI : Finite (N ≃ₐ[K] N) := inferInstance
  have hsub : ∀ x : N, (∀ σ : N ≃ₐ[K] N, σ x = x) → x ∈ perfectClosure K N := by
    intro x hx
    rw [mem_perfectClosure_iff_natSepDegree_eq_one]
    have hint : _root_.IsIntegral K x := Normal.isIntegral ‹Normal K N› x
    have hsplits : ((minpoly K x).map (algebraMap K N)).Splits := Normal.splits ‹Normal K N› x
    rw [Polynomial.natSepDegree_eq_of_splits (F := K) (E := N) (f := minpoly K x) hsplits]
    have hxr : x ∈ ((minpoly K x).aroots N).toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
      exact ⟨minpoly.ne_zero hint, minpoly.aeval K x⟩
    have hone : ((minpoly K x).aroots N).toFinset = {x} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hxr, ?_⟩
      intro y hy
      have hy' : y ∈ (minpoly K x).aroots N := Multiset.mem_toFinset.mp hy
      set φ : K⟮x⟯ →ₐ[K] N := (algHomAdjoinIntegralEquiv K hint).symm ⟨y, hy'⟩ with hφdef
      have hφ : φ (AdjoinSimple.gen K x) = y := by
        rw [hφdef, algHomAdjoinIntegralEquiv_symm_apply_gen K hint]
      set ψ : N →ₐ[K] N := φ.liftNormal N with hψ
      set σ : N ≃ₐ[K] N := AlgEquiv.ofBijective ψ (AlgHom.normal_bijective K N N ψ) with hσ
      have hσx : σ x = y := by
        have h1 : ψ (algebraMap K⟮x⟯ N (AdjoinSimple.gen K x))
            = algebraMap N N (φ (AdjoinSimple.gen K x)) := φ.liftNormal_commutes N _
        have h2 : ψ x = y := by simpa [hφ, AdjoinSimple.algebraMap_gen] using h1
        rw [hσ, AlgEquiv.coe_ofBijective]
        exact h2
      rw [← hσx, hx σ]
    rw [hone]
    simp
  set F0 := FixedPoints.subfield (N ≃ₐ[K] N) N with hF0
  have hle : ∀ z : N, z ∈ F0 → z ∈ perfectClosure K N := by
    intro z hz
    exact hsub z fun σ => hz σ
  letI : Algebra ↥F0 ↥(perfectClosure K N) :=
    RingHom.toAlgebra
      { toFun := fun z => ⟨(z : N), hle z z.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
  haveI : IsScalarTower ↥F0 ↥(perfectClosure K N) N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.isSeparable_tower_top_of_isSeparable ↥F0 ↥(perfectClosure K N) N

/-- **LEAF — a polynomial ring over a field is JAPANESE** (Stacks `0334`; cut 2026-07-28, the
second and deeper residue of E. Noether's finiteness theorem).

`A₀ = k[x₁,…,x_d] = MvPolynomial (Fin d) k`, `K = Frac A₀`, and `L / K` is a finite PURELY
INSEPARABLE extension.  Then the integral closure of `A₀` in `L` is a finite `A₀`-module.

**Why the base must be a POLYNOMIAL ring — this is the whole point of the 2026-07-28 recut, and
it is not a matter of convenience.**  The previous form of this leaf asked the same question over
a general integrally closed finite-type `k`-algebra `B`.  That statement is TRUE but it is not
the classical lemma, and the classical proof does not reach it: the proof produces the
`q`-th-root ring and needs it to be NORMAL, and

* for `B = k[x]` the `q`-th-root ring `k'[x₁^{1/q},…,x_d^{1/q}]` IS a polynomial ring, hence
  normal, and IS finite over `k[x]` (basis: a `k`-basis of `k'` times the monomials
  `x^{α/q}`, `αᵢ < q`);
* for a general normal `B` the two requirements are in direct tension.  The ring one can afford
  to build, `k''·B^{1/q}` with `k''/k` finite, has Frobenius image `(k'')^q · B = B` only when
  `(k'')^q ⊇ k`, i.e. `k'' ⊇ k^{1/q}` — infinite; while the ring that IS finite over `B` has
  Frobenius image `k₁[b₁,…,b_N]` for a proper subfield `k₁ ⊊ k`, which need not be normal.  The
  general-`B` statement is genuinely the Nagata/N-2 theory ("N-2 passes to finite-type
  extensions"), not this lemma.

`module_finite_integralClosure_of_isPurelyInseparable` below is what bridges the gap, and it does
so through `module_finite_integralClosure_mvPolynomial`: Noether-normalize `B`, then take the
inseparable step FIRST over the polynomial base (which is what
`isSeparable_perfectClosure_of_normal` above is for) instead of after a separable step that has
already moved the base.

**The classical proof of this leaf** (Stacks `0334` ⟸ `032L`).  Let `p` be the exponential
characteristic and `q = pᵉ` the exponent of `L / K` (`IsPurelyInseparable.exponent`, with
`HasExponent` free from `FiniteDimensional K L`).  For `c` in the integral closure, `c ^ q ∈ K`
and is integral over `A₀`, so `c ^ q ∈ A₀` because `A₀` is a UFD hence integrally closed — i.e.
the integral closure IS `{x ∈ L | x ^ q ∈ A₀}` (both inclusions: `X ^ q - c ^ q` is a monic
witness for the other one).  Now `L ⊆ K^{1/q} = k^{1/q}(x₁^{1/q},…,x_d^{1/q})`, so a finite
`K`-basis of `L` involves only finitely many elements of `k^{1/q}`; let `k'` be the subfield of
`k^{1/q}` they generate, finite over `k`.  Then `L ⊆ k'(x₁^{1/q},…,x_d^{1/q})`, whose integral
closure over `A₀` is the POLYNOMIAL RING `k'[x₁^{1/q},…,x_d^{1/q}]` — normal, and free over `A₀`
on the finite basis above.  A submodule of a finite module over a Noetherian ring is finite.

Two things a prover should know before starting.  (i) The finiteness of `k'` is CHEAP here and
should not be mistaken for the gap: `k' = {a ∈ L | a ^ q ∈ k}` is algebraic over `k` and sits
inside the finitely generated extension `L / k`, so
`Algebra.finite_of_essFiniteType_of_isAlgebraic` (`Mathlib`, via `Algebra.EssFiniteType`) already
gives `[k' : k] < ∞`.  What is missing is the `q`-th-root polynomial ring as an actual object.
(ii) **A `PerfectField k` hypothesis would NOT let you skip the construction** — it only makes
`k' = k`; the counterexample often quoted for it, `k = 𝔽_p`, `A = k[x,y]/(yᵖ - x)` finite over
`A₀ = k[x]` with `Frac A / Frac A₀` purely inseparable, shows the inseparable case is live over a
perfect field too.

**A REFORMULATION THAT LOOKS LIKE THE CHEAPER ROUTE** (worked out 2026-07-27, not carried out;
restated here over the polynomial base, which is where it is elementary).  In characteristic
`p > 0` the map `φ : L → K`, `x ↦ x ^ q`, is an INJECTIVE RING HOMOMORPHISM — Frobenius is
additive — semilinear over its own restriction `A₀ → A₀ᵍ`; in the pin it is
`IsPurelyInseparable.iterateFrobenius` (`Mathlib/FieldTheory/PurelyInseparable/Exponent.lean`),
with an `iterateFrobeniusₛₗ` semilinear form.  So `Module.Finite A₀ C` is equivalent to `φ C`
being a finitely generated `A₀ᵍ`-module, and `φ C = φ L ∩ A₀`, where `φ L` is a subfield of `K`
with `Kᵍ ⊆ φ L ⊆ K` and `[φ L : Kᵍ] = [L : K] < ∞`.  The leaf is therefore equivalent to

  `Kᵍ ⊆ F ⊆ K` with `[F : Kᵍ] < ∞`  ⟹  `F ∩ A₀` is a finite `A₀ᵍ`-module,

which mentions no extension of `K` at all: every object lives inside `K` and `A₀`, and no `q`-th
root is ever constructed.  Over the polynomial base that statement is elementary — `F` is
generated over `Kᵍ` by finitely many rational functions; the subfield `k₁ ⊆ k` generated by `kᵍ`
together with their finitely many coefficients is finite over `kᵍ`; `F ⊆ k₁(x)`; and
`k₁(x) ∩ k[x] = k₁[x]` is free over `kᵍ[xᵍ]` on `{x^α : αᵢ < q}` times a `kᵍ`-basis of `k₁`.
That `k₁` is the classical `k'`, transported through Frobenius.  (This is the same tension as
above, seen from the other side: the elementary argument reads off COEFFICIENTS, which only a
polynomial base has.)

**A PROVEN CHARACTERISTIC-ZERO TWIN EXISTS IN THIS TREE — do not redevelop it.**
`Fermat/FLT/Modularity/MoretBailly.lean` carries `module_finite_integralClosure_of_finiteType`
over `[Field k] [CharZero k]`, three supporting lemmas, and a globalisation
`module_finite_integralClosure_sections_of_isReduced` (Stacks `03GR`, a finite affine cover plus
the sheaf axiom rather than the function field).  Its `CharZero` enters at exactly one place — to
make the residue extension separable so that `IsIntegralClosure.finite` applies — i.e. precisely
at THIS leaf, so closing this leaf is what would let that cluster drop its characteristic
hypothesis.  Its two `…_range_le` lemmas are pure module theory and have been hoisted above; the
rest of it cannot be consumed from here, since it lives in the `Modularity` cone, strictly
downstream of this shim module. -/
theorem module_finite_integralClosure_mvPolynomial_of_isPurelyInseparable
    (k : Type*) [Field k] (d : ℕ) (K L : Type*) [Field K]
    [Algebra (MvPolynomial (Fin d) k) K] [IsFractionRing (MvPolynomial (Fin d) k) K]
    [Field L] [Algebra K L] [Algebra (MvPolynomial (Fin d) k) L]
    [IsScalarTower (MvPolynomial (Fin d) k) K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L] :
    Module.Finite (MvPolynomial (Fin d) k) ↥(integralClosure (MvPolynomial (Fin d) k) L) :=
  sorry

/-- **The inseparable-then-separable split over an integrally closed Noetherian base** (PROVEN
2026-07-28).  This is the mirror image of
`module_finite_integralClosure_of_isSeparable_of_isPurelyInseparable` below, and the mirror is
the point: here the PURELY INSEPARABLE step is taken first, so the base ring `A` is still `A`
when the hard finiteness `hfin` is consumed, whereas in the other order it has already moved.

`A` is an integrally closed Noetherian domain with fraction field `K`, `K ⊆ E ⊆ N` a tower with
`E / K` finite and `N / E` finite separable, and `hfin` says the integral closure of `A` in `E`
is `A`-finite.  Then the integral closure of `A` in `N` is `A`-finite.

The proof is the standard two-step: `A₁ := integralClosure A E` is `A`-finite by `hfin`, is
integrally closed with fraction field `E`
(`integralClosure.isIntegrallyClosedOfFiniteExtension`,
`integralClosure.isFractionRing_of_finite_extension`) and Noetherian
(`isNoetherian_of_tower`), so `IsIntegralClosure.finite` applies to the separable step
`N / E` — this is where separability is spent — and `integralClosure A N` embeds `A`-linearly
into `integralClosure A₁ N`.  The two carriers are in fact equal, but only the inclusion is
needed. -/
theorem module_finite_integralClosure_of_isPurelyInseparable_of_isSeparable
    (A K E N : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra A E] [Algebra K E] [IsScalarTower A K E] [FiniteDimensional K E]
    [Field N] [Algebra A N] [Algebra K N] [Algebra E N]
    [IsScalarTower A K N] [IsScalarTower K E N] [IsScalarTower A E N]
    [FiniteDimensional E N] [Algebra.IsSeparable E N]
    (hfin : Module.Finite A ↥(integralClosure A E)) :
    Module.Finite A ↥(integralClosure A N) := by
  haveI := hfin
  haveI : IsFractionRing ↥(integralClosure A E) E :=
    integralClosure.isFractionRing_of_finite_extension K E
  haveI : IsIntegrallyClosed ↥(integralClosure A E) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : _root_.IsNoetherian A ↥(integralClosure A E) := inferInstance
  haveI : IsNoetherianRing ↥(integralClosure A E) :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower A inferInstance)
  haveI := IsIntegralClosure.finite ↥(integralClosure A E) E N
    ↥(integralClosure ↥(integralClosure A E) N)
  haveI : Module.Finite A ↥(integralClosure ↥(integralClosure A E) N) :=
    Module.Finite.trans ↥(integralClosure A E) _
  haveI : Algebra.IsIntegral A ↥(integralClosure A E) := inferInstance
  refine Module.Finite.of_injective
    ({ toFun := fun x => ⟨(x : N), x.2.tower_top⟩
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      ↥(integralClosure A N) →ₗ[A] ↥(integralClosure ↥(integralClosure A E) N)) ?_
  intro x y h
  apply Subtype.ext
  have h2 := congrArg (fun z : ↥(integralClosure ↥(integralClosure A E) N) => (z : N)) h
  simpa using h2

/-- **E. Noether's finiteness theorem over a POLYNOMIAL base** (Stacks `0334`; PROVEN 2026-07-28
over the two leaves above).

`A₀ = k[x₁,…,x_d]`, `K = Frac A₀`, and `L / K` is ANY finite extension.  Then the integral
closure of `A₀` in `L` is a finite `A₀`-module.

**How it is proven, and why it is not the same cut as the one below.**  Embed `L` in
`Ω = AlgebraicClosure K` (`IsAlgClosed.lift`) and pass to the normal closure
`N = IntermediateField.normalClosure K L Ω`, finite and normal over `K`; `integralClosure A₀ L`
injects `A₀`-linearly into `integralClosure A₀ N`, and `A₀` is Noetherian, so it is enough to
treat `N`.  Inside a NORMAL extension the purely inseparable part comes FIRST:
`E := perfectClosure K N` is purely inseparable over `K` for free, and `N / E` is separable by
`isSeparable_perfectClosure_of_normal`.  So the inseparable step
`module_finite_integralClosure_mvPolynomial_of_isPurelyInseparable` is taken over `A₀` ITSELF —
the polynomial ring, where the classical proof lives — and the separable step is then free from
`Mathlib`'s `IsIntegralClosure.finite`, assembled by
`module_finite_integralClosure_of_isPurelyInseparable_of_isSeparable` above.

Contrast `module_finite_integralClosure_of_isIntegrallyClosed` below, which splits at
`separableClosure K L` instead: that takes the SEPARABLE step first, which is equally free, but
leaves the inseparable residue over a base that has moved off the polynomial ring.  Both cuts are
correct; only this one lands on a statement whose classical proof exists. -/
theorem module_finite_integralClosure_mvPolynomial
    (k : Type*) [Field k] (d : ℕ) (K L : Type*) [Field K]
    [Algebra (MvPolynomial (Fin d) k) K] [IsFractionRing (MvPolynomial (Fin d) k) K]
    [Field L] [Algebra K L] [Algebra (MvPolynomial (Fin d) k) L]
    [IsScalarTower (MvPolynomial (Fin d) k) K L] [FiniteDimensional K L] :
    Module.Finite (MvPolynomial (Fin d) k) ↥(integralClosure (MvPolynomial (Fin d) k) L) := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  set Ω := AlgebraicClosure K with hΩ
  set N := IntermediateField.normalClosure K L Ω with hN
  haveI : Normal K ↥N := inferInstance
  haveI : FiniteDimensional K ↥N := inferInstance
  set f : L →ₐ[K] Ω := IsAlgClosed.lift with hf
  have hfr : ∀ x : L, f x ∈ N := fun x => AlgHom.fieldRange_le_normalClosure f ⟨x, rfl⟩
  set g : L →ₐ[K] ↥N := f.codRestrict N.toSubalgebra hfr with hg
  set E := perfectClosure K ↥N with hE
  haveI : Algebra.IsSeparable ↥E ↥N := isSeparable_perfectClosure_of_normal K ↥N
  letI : Algebra (MvPolynomial (Fin d) k) ↥N :=
    ((algebraMap K ↥N).comp (algebraMap (MvPolynomial (Fin d) k) K)).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) k) K ↥N :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra (MvPolynomial (Fin d) k) ↥E :=
    ((algebraMap K ↥E).comp (algebraMap (MvPolynomial (Fin d) k) K)).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) k) K ↥E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (MvPolynomial (Fin d) k) ↥E ↥N :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) K ↥E,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) K ↥N,
        ← IsScalarTower.algebraMap_apply K ↥E ↥N]
  haveI hleaf : Module.Finite (MvPolynomial (Fin d) k)
      ↥(integralClosure (MvPolynomial (Fin d) k) ↥E) :=
    module_finite_integralClosure_mvPolynomial_of_isPurelyInseparable k d K ↥E
  haveI hbig : Module.Finite (MvPolynomial (Fin d) k)
      ↥(integralClosure (MvPolynomial (Fin d) k) ↥N) :=
    module_finite_integralClosure_of_isPurelyInseparable_of_isSeparable
      (MvPolynomial (Fin d) k) K ↥E ↥N hleaf
  refine Module.Finite.of_injective
    ({ toFun := fun x => ⟨g (x : L), ?_⟩
       map_add' := fun _ _ => by ext; simp
       map_smul' := fun a x => by ext; simp [Algebra.smul_def, IsScalarTower.algebraMap_apply
         (MvPolynomial (Fin d) k) K L, IsScalarTower.algebraMap_apply
         (MvPolynomial (Fin d) k) K ↥N] } :
      ↥(integralClosure (MvPolynomial (Fin d) k) L) →ₗ[MvPolynomial (Fin d) k]
        ↥(integralClosure (MvPolynomial (Fin d) k) ↥N)) ?_
  · exact x.2.map g
  · intro x y h
    apply Subtype.ext
    have h2 := congrArg (fun z : ↥(integralClosure (MvPolynomial (Fin d) k) ↥N) => (z : ↥N)) h
    exact g.injective (by simpa using h2)

/-- **The purely inseparable residue of E. Noether's finiteness theorem** (**PROVEN 2026-07-28**
over `module_finite_integralClosure_mvPolynomial` above — it was the file's single classical leaf
from 2026-07-27 until then).

`B` is an integrally closed domain of finite type over a field `k`, `S = Frac B`, and `L / S` is
a finite PURELY INSEPARABLE extension.  Then the integral closure of `B` in `L` is a finite
`B`-module.  Stacks `0335` / `032E`.

**How it is proven, and why the purely inseparable hypothesis is not used.**  Noether
normalization (`exists_finite_inj_algHom_of_fg`) gives `A₀ = MvPolynomial (Fin s) k ↪ B` with `B`
module-finite over `A₀`; `L` is then finite over `K₀ = Frac A₀` (algebraic by transitivity
through `S`, essentially of finite type by `Algebra.EssFiniteType.comp`/`.of_comp`, hence finite
by `Algebra.finite_of_essFiniteType_of_isAlgebraic`), and `B` is integral over `A₀`, so
`integralClosure A₀ L` and `integralClosure B L` have the SAME CARRIER and
`module_finite_of_algebraMap_range_le` moves module-finiteness from `A₀` up to `B`.  That reduces
this statement to `module_finite_integralClosure_mvPolynomial`, which asks nothing about the type
of the extension — so `[IsPurelyInseparable S L]` is inert in the proof.  The hypothesis is kept
because the consumer
`module_finite_integralClosure_of_isSeparable_of_isPurelyInseparable` below supplies it and
changing the signature would ripple upward for no gain; a later pass that reroutes
`module_finite_integralClosure_of_isFractionRing` directly through
`module_finite_integralClosure_mvPolynomial` can delete this theorem and its two consumers
outright. -/
theorem module_finite_integralClosure_of_isPurelyInseparable
    (k B S L : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B]
    [Field S] [Algebra B S] [IsFractionRing B S]
    [Field L] [Algebra B L] [Algebra S L] [IsScalarTower B S L]
    [FiniteDimensional S L] [IsPurelyInseparable S L] :
    Module.Finite B (integralClosure B L) := by
  classical
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI hfinB : Module.Finite (MvPolynomial (Fin s) k) B := hgfin
  letI : Algebra (MvPolynomial (Fin s) k) L := ((algebraMap B L).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra (MvPolynomial (Fin s) k) S := ((algebraMap B S).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) B S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (MvPolynomial (Fin s) k) S L :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k) B S,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) k) B L,
        ← IsScalarTower.algebraMap_apply B S L]
  have hBS : Function.Injective (algebraMap B S) := IsFractionRing.injective B S
  have hSL : Function.Injective (algebraMap S L) := (algebraMap S L).injective
  have hBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B S L]; exact hSL.comp hBS
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) k) L) := hBL.comp hginj
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) L := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinj x).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B :=
    Algebra.IsIntegral.of_finite (MvPolynomial (Fin s) k) B
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) S :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hBS.comp hginj)
  haveI : Module.IsTorsionFree (MvPolynomial (Fin s) k) S := inferInstance
  haveI halgB : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B := inferInstance
  haveI halgS : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) S :=
    (IsFractionRing.isAlgebraic_iff' (MvPolynomial (Fin s) k) B S).mp halgB
  haveI : Algebra.IsAlgebraic S L := Algebra.IsAlgebraic.of_finite S L
  haveI halgL : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) L :=
    Algebra.IsAlgebraic.trans (MvPolynomial (Fin s) k) S L
  haveI : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin s) k)) L :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := MvPolynomial (Fin s) k) (K := FractionRing (MvPolynomial (Fin s) k))
      (C := L)).mp halgL
  haveI : Algebra.EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.FiniteType S L := Module.Finite.finiteType _
  haveI : Algebra.EssFiniteType S L := inferInstance
  haveI : Algebra.EssFiniteType B L := Algebra.EssFiniteType.comp B S L
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin s) k) L :=
    Algebra.EssFiniteType.comp (MvPolynomial (Fin s) k) B L
  haveI : Algebra.EssFiniteType (FractionRing (MvPolynomial (Fin s) k)) L :=
    Algebra.EssFiniteType.of_comp (MvPolynomial (Fin s) k) _ L
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : Module.Finite (MvPolynomial (Fin s) k) ↥(integralClosure (MvPolynomial (Fin s) k) L) :=
    module_finite_integralClosure_mvPolynomial k s (FractionRing (MvPolynomial (Fin s) k)) L
  refine module_finite_of_algebraMap_range_le (R := B) (S := MvPolynomial (Fin s) k) (X := L)
    ?_ _ _ ?_ ‹_›
  · rintro _ ⟨c, rfl⟩
    exact ⟨g c, rfl⟩
  · ext x
    simp only [SetLike.mem_coe, mem_integralClosure_iff]
    exact ⟨fun h => h.tower_top, fun h => isIntegral_trans _ h⟩

/-- **Noether's finiteness theorem over an integrally closed base, split at an intermediate
field** (PROVEN 2026-07-27 over the leaf above).

`A` is an integrally closed domain of finite type over `k` with fraction field `K`, and
`K ⊆ S ⊆ L` is a tower with `S / K` finite separable and `L / S` finite purely inseparable.

The proof is the standard two-step: `B := integralClosure A S` is `A`-finite by
`IsIntegralClosure.finite` (this is where separability is spent), it is again an integrally
closed domain of finite type over `k` with fraction field `S`
(`integralClosure.isIntegrallyClosedOfFiniteExtension`,
`integralClosure.isFractionRing_of_finite_extension`), the leaf applies to it, and
`integralClosure A L` embeds `A`-linearly into `integralClosure B L` — the two carriers are in
fact equal, but only the inclusion is needed, and `A` is Noetherian. -/
theorem module_finite_integralClosure_of_isSeparable_of_isPurelyInseparable
    (k A K S L : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field S] [Algebra K S] [Algebra A S] [IsScalarTower A K S] [FiniteDimensional K S]
    [Algebra.IsSeparable K S]
    [Field L] [Algebra S L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower K S L] [IsScalarTower A S L]
    [FiniteDimensional S L] [IsPurelyInseparable S L] :
    Module.Finite A (integralClosure A L) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI hBfin : Module.Finite A ↥(integralClosure A S) :=
    IsIntegralClosure.finite A K S ↥(integralClosure A S)
  haveI : IsFractionRing ↥(integralClosure A S) S :=
    integralClosure.isFractionRing_of_finite_extension K S
  haveI : IsIntegrallyClosed ↥(integralClosure A S) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  letI : Algebra k ↥(integralClosure A S) :=
    ((algebraMap A ↥(integralClosure A S)).comp (algebraMap k A)).toAlgebra
  haveI : IsScalarTower k A ↥(integralClosure A S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType A ↥(integralClosure A S) := Module.Finite.finiteType _
  haveI : Algebra.FiniteType k ↥(integralClosure A S) :=
    Algebra.FiniteType.trans ‹Algebra.FiniteType k A› ‹_›
  haveI : Module.Finite ↥(integralClosure A S) ↥(integralClosure ↥(integralClosure A S) L) :=
    module_finite_integralClosure_of_isPurelyInseparable k ↥(integralClosure A S) S L
  haveI : Module.Finite A ↥(integralClosure ↥(integralClosure A S) L) :=
    Module.Finite.trans ↥(integralClosure A S) _
  haveI : Algebra.IsIntegral A ↥(integralClosure A S) :=
    Algebra.IsIntegral.of_finite A ↥(integralClosure A S)
  refine Module.Finite.of_injective
    ({ toFun := fun x => ⟨(x : L), x.2.tower_top⟩
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      ↥(integralClosure A L) →ₗ[A] ↥(integralClosure ↥(integralClosure A S) L)) ?_
  intro x y h
  apply Subtype.ext
  have h2 := congrArg (fun z : ↥(integralClosure ↥(integralClosure A S) L) => (z : L)) h
  simpa using h2

/-- **Noether's finiteness theorem over an integrally closed Noetherian base of finite type
over a field** (PROVEN 2026-07-27 over the leaf above).

`A` is an integrally closed domain of finite type over `k` with fraction field `K`, and `L` is
any FINITE extension of `K`.  Instantiating the previous theorem at
`S := separableClosure K L` — which is separable over `K` by `separableClosure.isSeparable`
and under which `L` is purely inseparable by `separableClosure.isPurelyInseparable` (`L / K` is
algebraic, being finite) — reduces this to the leaf. -/
theorem module_finite_integralClosure_of_isIntegrallyClosed
    (k A K L : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (integralClosure A L) := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : IsPurelyInseparable ↥(separableClosure K L) L := separableClosure.isPurelyInseparable K L
  haveI : IsScalarTower A ↥(separableClosure K L) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact module_finite_integralClosure_of_isSeparable_of_isPurelyInseparable k A K
    ↥(separableClosure K L) L

/-- **E. Noether's finiteness theorem for the normalization of a finite-type domain over a
field** (**PROVEN 2026-07-27** over the single leaf
`module_finite_integralClosure_of_isPurelyInseparable` above — it used to be the leaf itself).

`A` is a domain of finite type over a field `k` and `L = Frac A`.  Then the integral closure
of `A` in `L` — the normalization of `A` — is a FINITE `A`-module.  Stacks `0335` / `032E`.
This is the ONE classical input of `finiteType_integralClosure_sections` below.

**How it is proven.**  Noether normalization (`exists_finite_inj_algHom_of_fg`,
`Mathlib/RingTheory/NoetherNormalization.lean`, PRESENT at the pin) gives
`A₀ = MvPolynomial (Fin s) k ↪ A` with `A` module-finite over `A₀`.  `A₀` is a UFD, hence
`IsIntegrallyClosed`, and Noetherian, so `module_finite_integralClosure_of_isIntegrallyClosed`
applies to it once `L` is known to be FINITE over `K = Frac A₀`; and it is, because `L` is
algebraic over `K` (`IsFractionRing.isAlgebraic_iff'` then
`IsFractionRing.comap_isAlgebraic_iff`) and essentially of finite type over it
(`Algebra.EssFiniteType.of_comp`), which is exactly the hypothesis of
`Algebra.finite_of_essFiniteType_of_isAlgebraic`.  Finally `A` is integral over `A₀`, so
`integralClosure A₀ L` and `integralClosure A L` have the SAME CARRIER and
`module_finite_of_algebraMap_range_le` moves module-finiteness from `A₀` up to `A`. -/
theorem module_finite_integralClosure_of_isFractionRing
    {k A L : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field L] [Algebra A L] [IsFractionRing A L] :
    Module.Finite A (integralClosure A L) := by
  classical
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI hfinA : Module.Finite (MvPolynomial (Fin s) k) A := hgfin
  letI : Algebra (MvPolynomial (Fin s) k) L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) k) L) := hAL.comp hginj
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) L := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinj x).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A :=
    Algebra.IsIntegral.of_finite (MvPolynomial (Fin s) k) A
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI halgA : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) A := inferInstance
  haveI halgL : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) L :=
    (IsFractionRing.isAlgebraic_iff' (MvPolynomial (Fin s) k) A L).mp halgA
  haveI : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin s) k)) L :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := MvPolynomial (Fin s) k) (K := FractionRing (MvPolynomial (Fin s) k))
      (C := L)).mp halgL
  haveI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin s) k) L :=
    Algebra.EssFiniteType.comp (MvPolynomial (Fin s) k) A L
  haveI : Algebra.EssFiniteType (FractionRing (MvPolynomial (Fin s) k)) L :=
    Algebra.EssFiniteType.of_comp (MvPolynomial (Fin s) k) _ L
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : Module.Finite (MvPolynomial (Fin s) k) ↥(integralClosure (MvPolynomial (Fin s) k) L) :=
    module_finite_integralClosure_of_isIntegrallyClosed k (MvPolynomial (Fin s) k)
      (FractionRing (MvPolynomial (Fin s) k)) L
  refine module_finite_of_algebraMap_range_le (R := A) (S := MvPolynomial (Fin s) k) (X := L)
    ?_ _ _ ?_ ‹_›
  · rintro _ ⟨c, rfl⟩
    exact ⟨g c, rfl⟩
  · ext x
    simp only [SetLike.mem_coe, mem_integralClosure_iff]
    exact ⟨fun h => h.tower_top, fun h => isIntegral_trans _ h⟩

/-- **Noether's finiteness theorem at a prime** (PROVEN over
`module_finite_integralClosure_of_isFractionRing`).

The same conclusion without assuming `A` a domain: it is enough that `L` be the localization
of the finite-type `k`-algebra `A` at a prime `q` **and** a field.  Being a field forces
`q A_q = 0`, so `q` is exactly the kernel of `A → L` and `L = Frac (A ⧸ q)`.  This is the
shape the scheme-level statement actually produces — there `L` is the stalk of an affine
chart at a generic point, and the chart's ring is not a domain because `P` is not assumed
integral — so the quotient reduction is done once, here.  It goes:

* `q` is exactly `ker (algebraMap A L)`, by `IsLocalization.AtPrime.isUnit_to_map_iff` in
  both directions (outside `q` the image is a unit, hence nonzero; inside `q` a nonzero
  image would be a unit in the field `L`, hence outside `q`);
* so `A ⧸ q` embeds in `L`, and `IsLocalization.surj` at `q.primeCompl` writes every element
  of `L` as a fraction from `A ⧸ q`, which is `IsFractionRing (A ⧸ q) L`;
* `integralClosure A L ⊆ integralClosure (A ⧸ q) L` by `IsIntegral.tower_top`; the latter is
  `(A ⧸ q)`-finite by the leaf, hence `A`-finite because `A ↠ A ⧸ q`, and `A` is Noetherian
  (finite type over a field), so the submodule is finite. -/
theorem module_finite_integralClosure_of_isLocalizationAtPrime
    (k : Type*) {A L : Type*} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [Field L] [Algebra A L] (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime L q] :
    Module.Finite A (integralClosure A L) := by
  classical
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hker : ∀ x : A, algebraMap A L x = 0 ↔ x ∈ q := by
    intro x
    constructor
    · intro hx
      by_contra hxq
      have hu : IsUnit (algebraMap A L x) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff L q x).mpr hxq
      rw [hx] at hu
      exact not_isUnit_zero hu
    · intro hx
      by_contra hx0
      have hu : IsUnit (algebraMap A L x) := isUnit_iff_ne_zero.mpr hx0
      exact ((IsLocalization.AtPrime.isUnit_to_map_iff L q x).mp hu) hx
  letI : Algebra (A ⧸ q) L :=
    (Ideal.Quotient.lift q (algebraMap A L) (fun a ha => (hker a).mpr ha)).toAlgebra
  have hmapq : ∀ x : A, algebraMap (A ⧸ q) L (Ideal.Quotient.mk q x) = algebraMap A L x :=
    fun x => rfl
  haveI : IsScalarTower A (A ⧸ q) L :=
    IsScalarTower.of_algebraMap_eq (fun x => (hmapq x).symm)
  have hinj : Function.Injective (algebraMap (A ⧸ q) L) := by
    intro x y hxy
    induction x using Quotient.inductionOn' with
    | h x =>
      induction y using Quotient.inductionOn' with
      | h y =>
        have h0 : algebraMap A L (x - y) = 0 := by
          rw [map_sub, ← hmapq x, ← hmapq y]
          exact sub_eq_zero_of_eq hxy
        exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).mpr ((hker _).mp h0)
  haveI : IsFractionRing (A ⧸ q) L := by
    refine (isLocalization_iff (nonZeroDivisors (A ⧸ q)) L).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      refine isUnit_iff_ne_zero.mpr ?_
      simpa using fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hy) (hinj (by simpa using h))
    · intro z
      obtain ⟨⟨a, s, hs⟩, hz⟩ := IsLocalization.surj (M := q.primeCompl) z
      refine ⟨⟨Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q s, ?_⟩⟩, ?_⟩
      · exact mem_nonZeroDivisors_iff_ne_zero.mpr
          (fun h => hs ((Ideal.Quotient.eq_zero_iff_mem).mp h))
      · simpa [hmapq] using hz
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩
  haveI : Module.Finite (A ⧸ q) (integralClosure (A ⧸ q) L) :=
    module_finite_integralClosure_of_isFractionRing (k := k)
  haveI : Module.Finite A (A ⧸ q) :=
    Module.Finite.of_surjective (Algebra.linearMap A (A ⧸ q)) Ideal.Quotient.mk_surjective
  haveI : Module.Finite A (integralClosure (A ⧸ q) L) := Module.Finite.trans (A ⧸ q) _
  refine Module.Finite.of_injective
    ({ toFun := fun x => ⟨(x : L), x.2.tower_top⟩
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : integralClosure A L →ₗ[A] integralClosure (A ⧸ q) L)
    ?_
  intro x y h
  apply Subtype.ext
  have h2 := congrArg (fun z : integralClosure (A ⧸ q) L => (z : L)) h
  simpa using h2

/-- **The integral closure of an affine chart of `P` in the sections of `Y` over its preimage is
a finite-type algebra** (**PROVEN 2026-07-27** over
`module_finite_integralClosure_of_isFractionRing`, itself now PROVEN over the single classical
leaf `module_finite_integralClosure_of_isPurelyInseparable` above — this was the
Nagata/Japanese input, and, after the 2026-07-27 cut below, all that was left of the old
`isFinite_fromNormalization`).

TRUE and classical.  Write `A := Γ(P, U)` and `B := Γ(Y, i ⁻¹ᵁ U)`.  A domain of finite type
over a field is a Nagata (universally Japanese) ring, so its integral closure in a finite
extension of its fraction field is a finite module, in particular a finite-type algebra.
Stacks tag `032E` (Nagata ⟸ finite type over a field) and `03GH` (finiteness of the relative
normalization over a Nagata base).

**Why the ambient leaf is stated as `LocallyOfFiniteType` rather than `IsFinite`**
(2026-07-27): the integrality half of `IsFinite` is FREE — `IsIntegralHom i.fromNormalization`
is a `Mathlib` instance for every relative normalization, and
`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` says the two together are exactly
`IsFinite`.  So the entire content of the old leaf is this one, and
`isFinite_fromNormalization` below is now a two-line consequence.  Anyone attacking it should
know that only finite-*type*-ness has to be produced; integrality is not in play.

**WHY THIS IS THE LEAF AND NOT THE SCHEME-LEVEL STATEMENT** (2026-07-27).  For `U = Spec A` an
affine open of `P`, the ring `Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U)` is by construction
the integral closure of `A` in `B` (`AlgebraicGeometry.Scheme.Hom.normalizationObjIso`), and
`LocallyOfFiniteType` is Zariski-local at the target, so the scheme-level statement is exactly
this one over every affine `U`.  That descent is now PROVEN — see
`locallyOfFiniteType_fromNormalization` immediately below — so no scheme theory is owed here.

**HOW IT IS PROVEN (2026-07-27), and what is left.**  Everything below is now written out; the
only thing still owed is `module_finite_integralClosure_of_isPurelyInseparable` above, the
purely inseparable residue of Noether's theorem.

* When `i ⁻¹ᵁ U` is EMPTY the open is `⊥`, so `B` is the trivial ring —
  `instance {X : Scheme.{u}} : Subsingleton Γ(X, ⊥)` in `Mathlib/AlgebraicGeometry/Scheme.lean`
  — hence so is `integralClosure A B`, and `Algebra.FiniteType` is automatic.  That case is
  split off first.
* Otherwise `B` embeds in the FUNCTION FIELD `L := Y.functionField`, injectively, by
  `Scheme.germToFunctionField_injective` (`Mathlib/AlgebraicGeometry/FunctionField.lean`).
* `L` is the LOCALIZATION OF `A` AT A PRIME, namely at
  `U.2.primeIdealOf ⟨i.base (genericPoint Y), _⟩`.  This is where the geometry is spent, and it
  is a cleaner route than the "fraction field of the image of `A`" one this docstring used to
  describe: `U.2.isLocalization_stalk` says the stalk of `P` at that point is the localization
  of `A` at that prime, and `i.stalkMap (genericPoint Y)` is an ISO because `i` is an open
  immersion, so it transports the `IsLocalization.AtPrime` along
  `IsLocalization.isLocalization_iff_of_algEquiv`.  That the transport is an *algebra* equiv
  over `A` is exactly `Scheme.Hom.germ_stalkMap`.  Note this needs no affineness of
  `i ⁻¹ᵁ U`, which is the reason `functionField_isFractionRing_of_isAffineOpen` — the obvious
  first thing to reach for — does NOT apply: an open subscheme of an affine scheme is not
  affine in general.
* `A` is of FINITE TYPE over `K`, hence NOETHERIAN: `IsProper strP` gives
  `LocallyOfFiniteType strP`, and `HasRingHomProperty.appLE` reads that off at `U`, after
  transporting the base along `Scheme.ΓSpecIso (CommRingCat.of K)`.
* `integralClosure A B` then injects, as an `A`-module, into `integralClosure A L` — the map is
  `AlgHom.mapIntegralClosure`, already in the pin — and the latter is a FINITE `A`-module by
  `module_finite_integralClosure_of_isLocalizationAtPrime`, so the submodule is finite because
  `A` is Noetherian (`Module.Finite.of_injective`).
* The final conversion is `RingHom.finiteType_algebraMap`
  (`Mathlib/RingTheory/FiniteType.lean`): `(algebraMap A C).FiniteType ↔ Algebra.FiniteType A C`,
  together with the instance `Module.Finite A C → Algebra.FiniteType A C`.

`IsIntegral Y` is used twice and only twice: for the generic point to exist and lie in every
nonempty open, and for `germToFunctionField` to be injective.  `IsDomain B` is never needed —
`IsIntegral.component_integral` is not used — because the quotient reduction happens one level
down, inside `module_finite_integralClosure_of_isLocalizationAtPrime`, where it is a statement
about `A` rather than about `B`.  `QuasiCompact i` is not used by this proof at all; it is kept
because every consumer already carries it and because Zariski's Main Theorem needs it. -/
theorem finiteType_integralClosure_sections {Y P : Scheme.{u}}
    (strP : P ⟶ Spec (CommRingCat.of K)) [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y] (U : P.affineOpens) :
    letI := (i.app U.1).hom.toAlgebra
    RingHom.FiniteType
      (algebraMap Γ(P, U.1) (integralClosure Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1))) := by
  letI algB : Algebra Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
  show RingHom.FiniteType (algebraMap Γ(P, U.1) (integralClosure Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1)))
  rw [RingHom.finiteType_algebraMap]
  -- The affine chart is a finite-type `K`-algebra, hence Noetherian.
  have hle : U.1 ≤ strP ⁻¹ᵁ ⊤ := by simp
  letI algKA : Algebra K Γ(P, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strP.appLE ⊤ U.1 hle).hom.toAlgebra
  haveI hftA : Algebra.FiniteType K Γ(P, U.1) := by
    rw [← RingHom.finiteType_algebraMap]
    show RingHom.FiniteType
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strP.appLE ⊤ U.1 hle).hom)
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp
      (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) strP inferInstance
        ⟨⊤, isAffineOpen_top _⟩ U hle)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  haveI : IsNoetherianRing Γ(P, U.1) := Algebra.FiniteType.isNoetherianRing K _
  rcases isEmpty_or_nonempty (i ⁻¹ᵁ U.1) with hV | hV
  · -- Empty preimage: the sections ring is trivial, so there is nothing to generate.
    have hbot : (i ⁻¹ᵁ U.1) = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hV.false ⟨x, hx⟩
    haveI : Subsingleton Γ(Y, i ⁻¹ᵁ U.1) := by rw [hbot]; infer_instance
    haveI : Subsingleton ↥(integralClosure Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1)) := inferInstance
    infer_instance
  · -- Nonempty preimage: everything embeds in the function field of `Y`.
    haveI := hV
    have hη : genericPoint Y ∈ (i ⁻¹ᵁ U.1) :=
      ((genericPoint_spec Y).mem_open_set_iff (i ⁻¹ᵁ U.1).isOpen).mpr (by simpa using hV)
    letI algAL : Algebra Γ(P, U.1) Y.functionField :=
      ((i.app U.1) ≫ Y.germToFunctionField (i ⁻¹ᵁ U.1)).hom.toAlgebra
    haveI : IsScalarTower Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1) Y.functionField :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    -- The function field is the stalk of `P` at the image of the generic point, hence the
    -- localization of the chart at the corresponding prime.
    letI algAS : Algebra Γ(P, U.1) (P.presheaf.stalk (i.base (genericPoint Y))) :=
      TopCat.Presheaf.algebra_section_stalk P.presheaf
        (⟨i.base (genericPoint Y), hη⟩ : U.1)
    have hstalk : IsLocalization.AtPrime (P.presheaf.stalk (i.base (genericPoint Y)))
        (U.2.primeIdealOf ⟨i.base (genericPoint Y), hη⟩).asIdeal :=
      U.2.isLocalization_stalk ⟨i.base (genericPoint Y), hη⟩
    letI e : P.presheaf.stalk (i.base (genericPoint Y)) ≃ₐ[Γ(P, U.1)] Y.functionField :=
      { (asIso (i.stalkMap (genericPoint Y))).commRingCatIsoToRingEquiv with
        commutes' := fun r => by
          have := Scheme.Hom.germ_stalkMap i U.1 (genericPoint Y) hη
          exact congrArg (fun (f : Γ(P, U.1) ⟶ Y.functionField) => f.hom r) this }
    haveI : IsLocalization.AtPrime Y.functionField
        (U.2.primeIdealOf ⟨i.base (genericPoint Y), hη⟩).asIdeal :=
      (IsLocalization.isLocalization_iff_of_algEquiv _ e).mp hstalk
    haveI : Module.Finite Γ(P, U.1) ↥(integralClosure Γ(P, U.1) Y.functionField) :=
      module_finite_integralClosure_of_isLocalizationAtPrime K
        (U.2.primeIdealOf ⟨i.base (genericPoint Y), hη⟩).asIdeal
    haveI : Module.Finite Γ(P, U.1) ↥(integralClosure Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1)) := by
      refine Module.Finite.of_injective
        (AlgHom.mapIntegralClosure
          (IsScalarTower.toAlgHom Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1) Y.functionField)).toLinearMap ?_
      intro a b h
      apply Subtype.ext
      exact Y.germToFunctionField_injective (i ⁻¹ᵁ U.1) (congrArg Subtype.val h)
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- **The normalization of a scheme of finite type over a field is of finite type over it**
(PROVEN over `finiteType_integralClosure_sections`).

The whole content is now the affine-local ring statement; what is proven here is the descent
from it, and it is a transcription of `Mathlib`'s own proof of
`instance : IsIntegralHom f.fromNormalization` (`Mathlib/AlgebraicGeometry/Normalization.lean`)
with `IsIntegralHom` replaced by `LocallyOfFiniteType`: both are
`IsZariskiLocalAtTarget`, the affine opens of `P` cover it, and over such a `U` the restriction
of `i.fromNormalization` is — after transporting along
`IsOpenImmersion.isoOfRangeEq … (i.normalizationOpenCover.f U)` and `U.2.isoSpec` — literally
`Spec.map (i.normalizationDiagramMap.app (.op U))`, i.e. `Spec` of the inclusion
`Γ(P, U) ⟶ integralClosure Γ(P, U) Γ(Y, i ⁻¹ᵁ U)`.  `HasRingHomProperty.Spec_iff` then turns
the morphism property into `RingHom.FiniteType`, which is the leaf. -/
theorem locallyOfFiniteType_fromNormalization {Y P : Scheme.{u}}
    (strP : P ⟶ Spec (CommRingCat.of K)) [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y] :
    LocallyOfFiniteType i.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) _
    (iSup_affineOpens_eq_top P)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (i.fromNormalization ⁻¹ᵁ U).ι
      (i.normalizationOpenCover.f U)
      (by simpa using congr($(i.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @LocallyOfFiniteType _ U.2.isoSpec.hom]
  have h : RingHom.FiniteType (i.normalizationDiagramMap.app (.op U.1)).hom :=
    finiteType_integralClosure_sections strP i U
  convert! HasRingHomProperty.Spec_iff.mpr h
  · rw [← cancel_mono U.2.fromSpec]
    simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]
  · infer_instance

/-- **The normalization of a scheme of finite type over a field is finite over it**
(PROVEN over `locallyOfFiniteType_fromNormalization`).

TRUE and classical: a domain of finite type over a field is a Nagata (universally
Japanese) ring, so its integral closure in any finite extension of its fraction field is a
finite module.  Stacks tag `0335` (`0BXQ` for the geometric form).  Here the extension is
trivial — `i` is an open immersion, so `Y` and `P` share a function field — and the
statement is the familiar "normalization of a variety is finite".

Stated as `IsFinite` rather than `LocallyOfFiniteType`: `IsIntegralHom i.fromNormalization`
is already a `Mathlib` instance, and
`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` shows the two formulations agree, but
`IsFinite` is what the consumer wants (it yields `IsProper` immediately).  That equivalence
is exactly how this is now proven: integrality is free, so the only content is
`locallyOfFiniteType_fromNormalization` above.

Note this is the ONLY place excellence/Nagata-ness of the base enters, and it is why the
theorem is stated over a field rather than over an arbitrary base scheme: over a general
noetherian base the normalization need not be finite (Nagata's counterexample).

Note `strP` is an EXPLICIT argument even though the conclusion does not mention it: it is
the finite-type structure on `P` that makes normalization finite, and leaving it implicit
would leave it undetermined at every use site. -/
theorem isFinite_fromNormalization {Y P : Scheme.{u}}
    (strP : P ⟶ Spec (CommRingCat.of K)) [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y] :
    IsFinite i.fromNormalization :=
  haveI := locallyOfFiniteType_fromNormalization strP i
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

/-- **The local rings of the normalized model are discrete valuation rings** (sorry leaf —
the normality half of the old `smoothOfRelativeDimension_one_fromNormalization`).

TRUE and classical: the relative normalization `X` of `P` in the integral scheme `Y` is
NORMAL — that is what "normalization" means, and it is the one thing `Mathlib`'s
`Scheme.Hom.normalization` does not record — and it has the same function field as `Y`, hence
dimension one.  A noetherian normal local domain of dimension one is a discrete valuation
ring (Serre's criterion in dimension one; equivalently
`IsDiscreteValuationRing.TFAE` item 3, `IsIntegrallyClosed` together with a unique nonzero
prime, which is what dimension one supplies).

`¬ IsField` is exactly the exclusion of the generic point, where the stalk is the function
field: see the discussion on
`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`.

**What is genuinely missing at this pin, and what is not.**  `IsDiscreteValuationRing.TFAE`
and `IsRegularLocalRing` are both present (`Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`,
`Mathlib/RingTheory/RegularLocalRing/Defs.lean`), so the local ring theory is available; what
`Mathlib` does not have is (a) any statement that the stalks of `f.normalization` are
integrally closed, and (b) any notion of a normal scheme to phrase it with.  So a prover's
first move is to compute a stalk of `i.normalization` through
`Scheme.Hom.normalizationOpenCover` / `normalizationDiagramMap` — over an affine `U ∋` the
image, `Γ(X, ·)` is `integralClosure Γ(P, U) Γ(Y, i ⁻¹ᵁ U)`, whose localizations are
integrally closed by `IsIntegralClosure.isIntegrallyClosed_of_isLocalization`-style transport
— and only then apply the TFAE.

`hY` is what pins the dimension to one; without it the same construction applies in every
dimension and no local ring need be a DVR. -/
theorem isDiscreteValuationRing_stalk_normalization {Y P : Scheme.{u}}
    {strP : P ⟶ Spec (CommRingCat.of K)} [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y]
    (_hY : SmoothOfRelativeDimension 1 (i ≫ strP)) (x : i.normalization)
    (_hx : ¬ IsField (i.normalization.presheaf.stalk x)) :
    IsDiscreteValuationRing (i.normalization.presheaf.stalk x) :=
  sorry

/-- **The normalization of a curve over a perfect field is a smooth curve** (PROVEN
2026-07-27 over `isDiscreteValuationRing_stalk_normalization` and the shared DVR node
`smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`).

TRUE and classical, in three steps: the relative normalization `X` of `P` in the integral
scheme `Y` is normal and integral, and has the same function field as `Y`, hence the same
dimension `1`; a noetherian normal local domain of dimension one is a discrete valuation
ring, so `X` is regular; and over a **perfect** field regular is equivalent to smooth
(Stacks `056S`), the relative dimension being `1` because `X` is a curve.

**The old "IRREDUCIBLE at this pin" verdict is RETIRED, and it was wrong on a checkable
point.**  It read: "`Mathlib` has no notion of a normal scheme, no dimension theory for
schemes beyond `coheight`, and no regular-implies-smooth-over-a-perfect-field statement."
The first and third clauses are right; the implicit claim that regularity itself is
unavailable is not — `IsRegularLocalRing` is at this pin, with
`IsLocalRing.finrank_CotangentSpace_eq_one_iff` linking it to `IsDiscreteValuationRing` in
dimension one.  That is what makes the cut below possible: the statement splits cleanly into
*normality of the normalization* (leaf above, and genuinely absent) and *regular ⟹ smooth
over a perfect field* (the shared node), rather than being one indivisible citation.

`PerfectField K` is load-bearing and the statement is FALSE without it: over an imperfect
field `k` of characteristic `p` the curve `y^p = t x^p + t` (`t ∈ k ∖ k^p`) is regular but
not smooth, and it is its own normalization.  `ℚ` is perfect, so the modular application
is unaffected.

`hY` — that `Y` itself is a smooth curve — is what pins the dimension to `1`; it enters the
proof twice, once through the DVR leaf and once as the dense smooth open
`i.toNormalization` that fixes the relative dimension at `1` rather than `0`.  Zariski's Main
Theorem is what makes `i.toNormalization` an open immersion, and dominance is free by
construction — so the "dense open which is already a smooth curve" that the shared node asks
for is exactly `Y` itself. -/
theorem smoothOfRelativeDimension_one_fromNormalization [PerfectField K] {Y P : Scheme.{u}}
    {strP : P ⟶ Spec (CommRingCat.of K)} [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y]
    (hY : SmoothOfRelativeDimension 1 (i ≫ strP)) :
    SmoothOfRelativeDimension 1 (i.fromNormalization ≫ strP) := by
  haveI : IsFinite i.fromNormalization := isFinite_fromNormalization strP i
  haveI : IsIntegral i.normalization := inferInstance
  haveI : LocallyOfFiniteType (i.fromNormalization ≫ strP) := inferInstance
  have hsm : SmoothOfRelativeDimension 1 (i.toNormalization ≫ i.fromNormalization ≫ strP) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    exact hY
  exact smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk
    (i.fromNormalization ≫ strP) i.toNormalization hsm
    (fun x hx => isDiscreteValuationRing_stalk_normalization i hY x hx)

/-! ### Dimension theory over a general base field

The two dimension leaves below are both bounds on `topologicalKrullDim`, and both are reached
through the same three-step machine, which is proved in this block:

1. *the dimension of a scheme is the supremum of the heights of its points*
   (`topologicalKrullDim_eq_iSup_coheight`, from sobriety plus
   `Order.krullDim_eq_iSup_coheight`), which turns a comparison of dimensions into a
   POINTWISE one;
2. *coheight is affine-local* — `coheight_eq_of_isOpenImmersion` moves it across an open
   immersion and `idealHeight_eq_coheight` identifies it with `Ideal.height` on an affine
   chart;
3. *Noether normalization plus the easy half of Cohen–Seidenberg*, which bounds heights on a
   chart by the number of normalizing variables.

**PROVENANCE, AND THE COLLAPSE THAT IS OWED** (2026-07-27).  A `ULift ℚ`-shaped copy of this
block is proven in `Fermat/FLT/Modularity/MoretBailly.lean` (`schemeIrreducibleClosedsOrderIso`
… `topologicalKrullDim_le_of_isOpenImmersion_of_locallyOfFiniteType`, under
`namespace GaloisRepresentation.Modularity`).  That file is DOWNSTREAM of this one, so the copy
here is the hoist, not a second development: everything below is stated over an arbitrary base
field `K`, and the `ℚ`-shaped copies there are now redundant and should be re-derived from these
(a follow-up, deliberately not done here — `MoretBailly.lean` has many concurrent owners).

**WHAT HAD TO CHANGE FOR A GENERAL `K`, AND IT IS EXACTLY ONE STEP.**  The `ℚ`-shaped proof
produces its chain of primes in `K[X₀,…,X_{s-1}]` from a RATIONAL point at which a prescribed
`b ≠ 0` does not vanish, and `ℚ` being infinite is what supplies it.  Over a FINITE `K` no such
point need exist (`b = X^q - X` vanishes identically on `𝔽_q`).  The replacement is a
two-line reduction rather than a new argument: `MvPolynomial (Fin s) (AlgebraicClosure K)` is
INTEGRAL over `MvPolynomial (Fin s) K` (mathlib's
`instance : Algebra.IsIntegral (MvPolynomial σ R) (MvPolynomial σ S)` for an integral `R → S`),
so incomparability makes `PrimeSpectrum.comap` strictly monotone and the chain found over the
(infinite) algebraic closure CONTRACTS to a chain of the same length over `K`.  See
`exists_ltSeries_length_eq_notMem_of_mvPolynomial`. -/

/-- **A scheme is sober**: its irreducible closed subsets are exactly the closures of its
points, and the correspondence is an order isomorphism.

`Mathlib`'s `irreducibleSetEquivPoints` is the same map, but it is stated under
`attribute [local instance] specializationOrder` — a `PartialOrder`. A scheme instead carries
the GLOBAL `instance {X : Scheme} : Preorder X := specializationPreorder X`, and every
scheme-level coheight fact used below (`coheight_eq_of_isOpenImmersion`,
`idealHeight_eq_coheight`) is stated against THAT one.  The two are defeq and never
syntactically equal, so mixing them is this project's recurring "duplicate instances that print
identically" trap; re-proving `map_rel_iff'` against the global preorder removes the whole
class. -/
noncomputable def schemeIrreducibleClosedsOrderIso (X : Scheme.{u}) :
    TopologicalSpace.IrreducibleCloseds ↥X ≃o ↥X where
  toFun s := s.2.genericPoint
  invFun x := ⟨closure ({x} : Set ↥X), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := by
    refine TopologicalSpace.IrreducibleCloseds.ext ?_
    simp only [IsIrreducible.genericPoint_closure_eq, TopologicalSpace.IrreducibleCloseds.coe_mk,
      closure_eq_iff_isClosed.mpr s.3]
    rfl
  right_inv x := isIrreducible_singleton.closure.isGenericPoint_genericPoint_closure.eq
      (by rw [closure_closure]; exact isGenericPoint_closure)
  map_rel_iff' := by
    rintro ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
    refine specializes_iff_closure_subset.trans ?_
    simp
    rfl

/-- **The Krull dimension of a scheme is the supremum of the coheights of its points**:
`topologicalKrullDim` is by definition `krullDim` of the poset of irreducible closed subsets,
that poset is order-isomorphic to the points by sobriety, and `Order.krullDim_eq_iSup_coheight`
rewrites a `krullDim` as a supremum of coheights.

This is the bridge that turns a dimension comparison into a POINTWISE one. -/
theorem topologicalKrullDim_eq_iSup_coheight (X : Scheme.{u}) :
    topologicalKrullDim ↥X = ⨆ (x : ↥X), (Order.coheight x : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (schemeIrreducibleClosedsOrderIso X),
    Order.krullDim_eq_iSup_coheight]

section Integral

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Cohen–Seidenberg, the easy half**: an integral extension does not raise Krull dimension.
Incomparability (`Ideal.IsIntegral.comap_lt_comap`) makes `PrimeSpectrum.comap` strictly
monotone, and `Order.krullDim_le_of_strictMono` does the rest.

This is the item the `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` docstring
below used to record as "MISSING (1): invariance of `ringKrullDim` under an injective integral
ring extension".  Only the bound in this direction is ever needed, and it is four lines. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) ?_
  intro p q h
  have hp : p.asIdeal.IsPrime := p.isPrime
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at h ⊢
  exact Ideal.IsIntegral.comap_lt_comap h

/-- **Going up along a chain**: given an integral extension `R → A` whose kernel is contained in
the head of a chain of primes of `R`, there is a prime `Q` of `A` lying over the chain's last
term whose height is at least the chain's length. -/
theorem exists_isPrime_under_eq_and_le_height_of_isIntegral [Algebra.IsIntegral R A]
    (l : LTSeries (PrimeSpectrum R))
    (hker : RingHom.ker (algebraMap R A) ≤ l.head.asIdeal) :
    ∃ Q : Ideal A, ∃ _ : Q.IsPrime, Q.under R = l.last.asIdeal ∧
      (l.length : ℕ∞) ≤ Q.height := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
      have hx : x.asIdeal.IsPrime := x.isPrime
      obtain ⟨Q, -, hQ, hQ'⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := A) x.asIdeal ⊥ (by
          simpa [← RingHom.ker_eq_comap_bot] using hker)
      exact ⟨Q, hQ, hQ', by simp⟩
  | snoc p x hx ih =>
      have hhead : RingHom.ker (algebraMap R A) ≤ p.head.asIdeal := by
        simpa using hker
      obtain ⟨Q', hQ'p, hQ'under, hQ'ht⟩ := ih hhead
      have hxp : x.asIdeal.IsPrime := x.isPrime
      have hle : Q'.under R ≤ x.asIdeal := by
        rw [hQ'under]
        exact le_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hx)
      obtain ⟨Q, hQge, hQ, hQunder⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (R := R) (S := A)
          x.asIdeal Q' hle
      have hne : p.last.asIdeal ≠ x.asIdeal :=
        ne_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hx)
      refine ⟨Q, hQ, by rw [RelSeries.last_snoc]; exact hQunder, ?_⟩
      have hlt : Q' < Q := by
        refine lt_of_le_of_ne hQge ?_
        intro h
        exact hne (by rw [← hQ'under, Ideal.under_def, h, hQunder])
      have hstep : Q'.height + 1 ≤ Q.height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hlt
      calc ((p.snoc x hx).length : ℕ∞) = (p.length : ℕ∞) + 1 := by
            simp [RelSeries.snoc_length]
        _ ≤ Q'.height + 1 := by gcongr
        _ ≤ Q.height := hstep

end Integral

section Const

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- If `f` is killed by a polynomial `P` over `B`, then the image of `P`'s constant coefficient
lies in the ideal generated by `f`: writing `P = X * P.divX + C (P.coeff 0)` and evaluating at
`f` exhibits `algebraMap B A (P.coeff 0)` as a multiple of `f`. -/
theorem algebraMap_coeff_zero_mem_span_singleton {f : A} (P : Polynomial B)
    (hP : Polynomial.aeval f P = 0) :
    algebraMap B A (P.coeff 0) ∈ Ideal.span ({f} : Set A) := by
  have hsplit := congrArg (Polynomial.aeval f) P.X_mul_divX_add
  rw [hP, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hsplit
  have hval : algebraMap B A (P.coeff 0) = f * (-(Polynomial.aeval f P.divX)) := by
    rw [mul_neg]; linear_combination hsplit
  rw [hval]
  exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩

/-- **The `b₀` trick.** If `A` is a domain integral over `B` and `0 ≠ f ∈ A`, then the ideal
`f · A` meets `B` in a nonzero element: strip factors of `X` from an integrality equation for
`f` until the constant coefficient is nonzero, which the domain hypothesis permits. -/
theorem exists_ne_zero_algebraMap_mem_span_singleton [IsDomain A] {f : A} (hf : f ≠ 0)
    (hint : _root_.IsIntegral B f) :
    ∃ b : B, b ≠ 0 ∧ algebraMap B A b ∈ Ideal.span ({f} : Set A) := by
  have hntB : Nontrivial B := by
    refine ⟨1, 0, fun h => hf ?_⟩
    have h1 : (1 : A) = 0 := by
      rw [← map_one (algebraMap B A), h, map_zero]
    calc f = f * 1 := (mul_one f).symm
      _ = f * 0 := by rw [h1]
      _ = 0 := mul_zero f
  obtain ⟨P, hPm, hPe⟩ := hint
  have hPe' : Polynomial.aeval f P = 0 := by rw [Polynomial.aeval_def]; exact hPe
  clear hPe
  have key : ∀ (n : ℕ) (Q : Polynomial B), Q.natDegree ≤ n → Q ≠ 0 →
      Polynomial.aeval f Q = 0 → ∃ b : B, b ≠ 0 ∧ algebraMap B A b ∈ Ideal.span ({f} : Set A) := by
    intro n
    induction n with
    | zero =>
        intro Q hdeg hQ0 hQe
        by_cases h0 : Q.coeff 0 = 0
        · exact absurd (by
            have hQC : Q = Polynomial.C (Q.coeff 0) :=
              Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hdeg)
            rw [h0, map_zero] at hQC; exact hQC) hQ0
        · exact ⟨Q.coeff 0, h0, algebraMap_coeff_zero_mem_span_singleton Q hQe⟩
    | succ n ih =>
        intro Q hdeg hQ0 hQe
        by_cases h0 : Q.coeff 0 = 0
        · have hdvx : Polynomial.X * Q.divX = Q := by
            have h := Q.X_mul_divX_add
            rwa [h0, map_zero, add_zero] at h
          have hdne : Q.divX ≠ 0 := by
            intro hz
            rw [hz, mul_zero] at hdvx
            exact hQ0 hdvx.symm
          have hzero : Polynomial.aeval f Q.divX = 0 := by
            have hmul : f * Polynomial.aeval f Q.divX = 0 := by
              have h := congrArg (Polynomial.aeval f) hdvx
              rw [hQe, map_mul, Polynomial.aeval_X] at h
              exact h
            exact (mul_eq_zero.mp hmul).resolve_left hf
          refine ih Q.divX ?_ hdne hzero
          rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
          lia
        · exact ⟨Q.coeff 0, h0, algebraMap_coeff_zero_mem_span_singleton Q hQe⟩
  exact key P.natDegree P le_rfl hPm.ne_zero hPe'

end Const

section MvPoly

/-- **A chain of primes of full length in a polynomial ring over an INFINITE field, avoiding a
prescribed nonzero element.** Choose a point `a` at which `b` does not vanish (possible because
`k` is infinite), and take the kernels of the partial substitutions `X_j ↦ a j` for `j < i`.
Each is prime as the kernel of a map into a domain; the inclusions are strict because
`X_i - C (a i)` enters at step `i + 1`; and `b` avoids the last one exactly because `b(a) ≠ 0`.

The infinitude hypothesis is removed in `exists_ltSeries_length_eq_notMem_of_mvPolynomial`
immediately below, which is the form actually used.  This is where "finite type over a FIELD"
becomes load-bearing: over a general base a dense open really can drop dimension
(`Spec ℤ_[p]` and its generic point). -/
theorem exists_ltSeries_length_eq_notMem_of_mvPolynomial_of_infinite
    {k : Type*} [Field k] [Infinite k] {s : ℕ} (b : MvPolynomial (Fin s) k) (hb : b ≠ 0) :
    ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin s) k)),
      l.length = s ∧ b ∉ l.last.asIdeal := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin s → k, MvPolynomial.eval a b ≠ 0 := by
    by_contra h
    refine hb (MvPolynomial.funext (fun x => ?_))
    simp only [map_zero]
    by_contra hx
    exact h ⟨x, hx⟩
  set φ : ℕ → (MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k) := fun i =>
    MvPolynomial.aeval
      (fun j : Fin s => if (j : ℕ) < i then MvPolynomial.C (a j) else MvPolynomial.X j) with hφ
  set ψ : ℕ → (MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k) := fun i =>
    MvPolynomial.aeval
      (fun j : Fin s => if (j : ℕ) = i then MvPolynomial.C (a j) else MvPolynomial.X j) with hψ
  have hcomp : ∀ i : ℕ, φ (i + 1) = (ψ i).comp (φ i) := by
    intro i
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [hφ, hψ, AlgHom.comp_apply, MvPolynomial.aeval_X]
    rcases lt_trichotomy (j : ℕ) i with h | h | h
    · rw [if_pos (by lia : (j : ℕ) < i + 1), if_pos h, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq]
    · rw [if_pos (by lia : (j : ℕ) < i + 1), if_neg (by lia : ¬ (j : ℕ) < i),
        MvPolynomial.aeval_X, if_pos h]
    · rw [if_neg (by lia : ¬ (j : ℕ) < i + 1), if_neg (by lia : ¬ (j : ℕ) < i),
        MvPolynomial.aeval_X, if_neg (by lia : ¬ (j : ℕ) = i)]
  set K : ℕ → Ideal (MvPolynomial (Fin s) k) := fun i =>
    (⊥ : Ideal (MvPolynomial (Fin s) k)).comap
      ((φ i : MvPolynomial (Fin s) k →+* MvPolynomial (Fin s) k)) with hK
  have hker : ∀ i : ℕ, (K i).IsPrime := fun i => Ideal.comap_isPrime _ _
  have hmem : ∀ (i : ℕ) (g : MvPolynomial (Fin s) k), g ∈ K i ↔ φ i g = 0 := by
    intro i g; simp [hK, Ideal.mem_comap]
  refine ⟨⟨s, fun i => ⟨K (i : ℕ), hker (i : ℕ)⟩, ?_⟩, rfl, ?_⟩
  · intro i
    have hc : ((i.castSucc : Fin (s + 1)) : ℕ) = (i : ℕ) := Fin.val_castSucc i
    have hs' : ((i.succ : Fin (s + 1)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
    have hmk : ∀ x y : PrimeSpectrum (MvPolynomial (Fin s) k), x.asIdeal < y.asIdeal → x < y :=
      fun x y h => (PrimeSpectrum.asIdeal_lt_asIdeal x y).mp h
    refine hmk _ _ ?_
    show K ((i.castSucc : Fin (s + 1)) : ℕ) < K ((i.succ : Fin (s + 1)) : ℕ)
    rw [hc, hs']
    have hle : K (i : ℕ) ≤ K ((i : ℕ) + 1) := by
      intro g hg
      rw [hmem] at hg ⊢
      rw [hcomp, AlgHom.comp_apply, hg, map_zero]
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : (i : ℕ) < s := i.isLt
    set x : Fin s := ⟨(i : ℕ), hi⟩ with hx
    set g : MvPolynomial (Fin s) k := MvPolynomial.X x - MvPolynomial.C (a x) with hg
    have hgtop : φ ((i : ℕ) + 1) g = 0 := by
      rw [hg, map_sub]
      simp only [hφ, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
      rw [if_pos (by rw [hx]; lia : ((x : Fin s) : ℕ) < (i : ℕ) + 1), sub_self]
    have hgeq : φ (i : ℕ) g = g := by
      rw [hg, map_sub]
      simp only [hφ, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
      rw [if_neg (by rw [hx]; lia : ¬ ((x : Fin s) : ℕ) < (i : ℕ))]
    have hgne : g ≠ 0 := by
      intro hzero
      have hev := congrArg
        (MvPolynomial.eval (fun j : Fin s => if j = x then a x + 1 else 0)) hzero
      rw [hg] at hev
      simp at hev
    apply hgne
    rw [← hgeq, ← hmem, heq, hmem]
    exact hgtop
  · have hlast : ((Fin.last s : Fin (s + 1)) : ℕ) = s := rfl
    show b ∉ K (((Fin.last s : Fin (s + 1)) : ℕ))
    rw [hlast, hmem]
    have hfull : (MvPolynomial.aeval a).comp (φ s) = MvPolynomial.aeval a := by
      refine MvPolynomial.algHom_ext fun j => ?_
      simp only [hφ, AlgHom.comp_apply, MvPolynomial.aeval_X]
      rw [if_pos j.isLt, MvPolynomial.aeval_C]
      simp
    intro hzero
    have hb' : (MvPolynomial.aeval a) (φ s b) = (MvPolynomial.aeval a) b := by
      rw [← AlgHom.comp_apply, hfull]
    rw [hzero, map_zero] at hb'
    exact ha (by simpa [MvPolynomial.aeval_eq_eval] using hb'.symm)

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- **A chain of primes of full length in a polynomial ring over an ARBITRARY field, avoiding a
prescribed nonzero element.**

This is the general-`K` form, and it is the one step of the dense-open dimension transfer that
the `ULift ℚ`-shaped development in `Modularity/MoretBailly.lean` could not supply: that proof
picks a rational point at which `b` does not vanish, and over a FINITE field no such point need
exist — `b = X^q - X` vanishes on all of `𝔽_q`.

The replacement is a contraction, not a new argument.  `AlgebraicClosure K` is infinite and
ALGEBRAIC over `K`, so `MvPolynomial (Fin s) (AlgebraicClosure K)` is INTEGRAL over
`MvPolynomial (Fin s) K` (mathlib's
`instance : Algebra.IsIntegral (MvPolynomial σ R) (MvPolynomial σ S)`, via `Algebra.IsPushout`).
Incomparability (`Ideal.IsIntegral.comap_lt_comap`) then makes `PrimeSpectrum.comap` STRICTLY
monotone, so the length-`s` chain produced over the algebraic closure contracts to a length-`s`
chain over `K`, and the top of the contracted chain still misses `b` because the top of the
original misses the image of `b`. -/
theorem exists_ltSeries_length_eq_notMem_of_mvPolynomial
    {k : Type*} [Field k] {s : ℕ} (b : MvPolynomial (Fin s) k) (hb : b ≠ 0) :
    ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin s) k)),
      l.length = s ∧ b ∉ l.last.asIdeal := by
  classical
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) (MvPolynomial (Fin s) (AlgebraicClosure k)) :=
    inferInstance
  have hmap : (algebraMap (MvPolynomial (Fin s) k) (MvPolynomial (Fin s) (AlgebraicClosure k)))
      = (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
        MvPolynomial (Fin s) k →+* MvPolynomial (Fin s) (AlgebraicClosure k)) := rfl
  have hb' : MvPolynomial.map (algebraMap k (AlgebraicClosure k)) b ≠ 0 := by
    intro h
    exact hb (MvPolynomial.map_injective _ (algebraMap k (AlgebraicClosure k)).injective
      (by simpa using h))
  obtain ⟨l', hlen', hnot'⟩ :=
    exists_ltSeries_length_eq_notMem_of_mvPolynomial_of_infinite
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) b) hb'
  have hsm : StrictMono (PrimeSpectrum.comap
      (algebraMap (MvPolynomial (Fin s) k) (MvPolynomial (Fin s) (AlgebraicClosure k)))) := by
    intro p q h
    have hp : p.asIdeal.IsPrime := p.isPrime
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at h ⊢
    exact Ideal.IsIntegral.comap_lt_comap h
  refine ⟨l'.map _ hsm, by simpa using hlen', ?_⟩
  have hlast : (l'.map _ hsm).last = PrimeSpectrum.comap
      (algebraMap (MvPolynomial (Fin s) k) (MvPolynomial (Fin s) (AlgebraicClosure k)))
      l'.last := rfl
  rw [hlast]
  intro hmem
  exact hnot' (by rw [← hmap]; exact hmem)

end MvPoly

section Assembly

/-- **The commutative-algebra core of the dense-open dimension transfer.**

For a finitely generated domain `A` over a field `k`, a nonzero `f : A` and any prime `p`, the
basic open `D(f)` carries a prime at least as high as `p`.  Equivalently
`ringKrullDim A_f = ringKrullDim A`, which is the "dense opens of an irreducible finite-type
scheme are equidimensional" fact.

The route avoids transcendence degree entirely — which matters, because there is no
`dim = trdeg` at this pin:

1. Noether-normalize, `B = k[X₀,…,X_{s-1}] ↪ A` integral, so `p.height ≤ dim A ≤ dim B = s`
   by incomparability (`ringKrullDim_le_of_isIntegral`).
2. The `b₀` trick: an integrality equation for `f` with nonzero constant coefficient exhibits
   a nonzero `b ∈ B` inside `f · A`.
3. `B` has a chain of primes of length `s` whose top avoids `b`
   (`exists_ltSeries_length_eq_notMem_of_mvPolynomial`).
4. Going up lifts that chain to `A`, producing `q` over its top with `s ≤ q.height`; and
   `f ∉ q`, since `f ∈ q` would drag `b` into `q ∩ B`.

Note what this shows about the shape of the obstruction: `dim A_f = dim A` is a statement about
SUPREMA, and proving it in that form does force equidimensionality and hence the dimension
theorem.  The pointwise statement asked for here does not — one high enough prime suffices, and
Noether normalization hands you one. -/
theorem exists_isPrime_notMem_and_height_le_of_finiteType
    {k : Type*} [Field k] {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {f : A} (hf : f ≠ 0) (p : Ideal A) [p.IsPrime] :
    ∃ q : Ideal A, ∃ _ : q.IsPrime, f ∉ q ∧ p.height ≤ q.height := by
  obtain ⟨s, g, hginj, hgint⟩ := _root_.exists_integral_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hgint x⟩
  have hmapg : (algebraMap (MvPolynomial (Fin s) k) A) = g.toRingHom := rfl
  have hdimB : ringKrullDim (MvPolynomial (Fin s) k) = (s : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k]
    simp
  have hps : p.height ≤ (s : ℕ∞) := by
    have h1 : (p.height : WithBot ℕ∞) ≤ ringKrullDim A :=
      Ideal.height_le_ringKrullDim_of_isPrime
    have h2 : ringKrullDim A ≤ (s : WithBot ℕ∞) :=
      le_trans (ringKrullDim_le_of_isIntegral) (le_of_eq hdimB)
    exact_mod_cast h1.trans h2
  obtain ⟨b, hb0, hbmem⟩ :=
    exists_ne_zero_algebraMap_mem_span_singleton (B := MvPolynomial (Fin s) k) (A := A)
      hf (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin s) k) f)
  obtain ⟨l, hlen, hbnot⟩ := exists_ltSeries_length_eq_notMem_of_mvPolynomial b hb0
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) k) A) ≤ l.head.asIdeal := by
    rw [hmapg]
    intro y hy
    have : g y = 0 := hy
    rw [show (0 : A) = g 0 by simp] at this
    rw [hginj this]
    exact Ideal.zero_mem _
  obtain ⟨q, hqp, hqunder, hqht⟩ :=
    exists_isPrime_under_eq_and_le_height_of_isIntegral (R := MvPolynomial (Fin s) k) (A := A)
      l hker
  refine ⟨q, hqp, ?_, ?_⟩
  · intro hfq
    refine hbnot ?_
    rw [← hqunder]
    have : algebraMap (MvPolynomial (Fin s) k) A b ∈ q :=
      (Ideal.span_le.mpr (by simpa using hfq)) hbmem
    exact this
  · exact hps.trans (by rwa [hlen] at hqht)

/-- Killing the nilradical does not change the prime spectrum as an ordered set. -/
noncomputable def primeSpectrumQuotNilradicalOrderIso (R : Type*) [CommRing R] :
    PrimeSpectrum (R ⧸ nilradical R) ≃o PrimeSpectrum R where
  toEquiv := Equiv.ofBijective (PrimeSpectrum.comap (Ideal.Quotient.mk (nilradical R)))
    (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl)
  map_rel_iff' {a b} := by
    simp only [Equiv.ofBijective_apply]
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _

/-- **The dense-open dimension transfer, affine form.** Drop the domain hypothesis of
`exists_isPrime_notMem_and_height_le_of_finiteType` to irreducibility of `Spec R`, by passing
to `R ⧸ nilradical R` — which has the same spectrum, as an ordered set, hence the same
heights. -/
theorem exists_isPrime_notMem_height_le_of_finiteType_of_irreducible
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (hirr : IrreducibleSpace (PrimeSpectrum R))
    {r : R} (hr : ¬ IsNilpotent r) (p : Ideal R) [p.IsPrime] :
    ∃ q : Ideal R, ∃ _ : q.IsPrime, r ∉ q ∧ p.height ≤ q.height := by
  haveI hnil : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirr
  haveI : IsDomain (R ⧸ nilradical R) := Ideal.Quotient.isDomain _
  set e := primeSpectrumQuotNilradicalOrderIso R with he
  have hheight : ∀ z : PrimeSpectrum (R ⧸ nilradical R),
      (e z).asIdeal.height = z.asIdeal.height := by
    intro z
    rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight,
      Order.height_orderIso]
  set p' : PrimeSpectrum (R ⧸ nilradical R) := e.symm ⟨p, ‹p.IsPrime›⟩ with hp'
  haveI : p'.asIdeal.IsPrime := p'.isPrime
  have hr' : (Ideal.Quotient.mk (nilradical R)) r ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, mem_nilradical]
    exact hr
  obtain ⟨q', hq'p, hq'r, hq'ht⟩ :=
    exists_isPrime_notMem_and_height_le_of_finiteType (k := k) hr' p'.asIdeal
  refine ⟨(e ⟨q', hq'p⟩).asIdeal, (e ⟨q', hq'p⟩).isPrime, ?_, ?_⟩
  · intro hmem
    exact hq'r (by simpa [he, primeSpectrumQuotNilradicalOrderIso, Ideal.mem_comap] using hmem)
  · calc p.height = p'.asIdeal.height := by
          rw [← hheight p', hp', OrderIso.apply_symm_apply]
      _ ≤ q'.height := hq'ht
      _ = (e ⟨q', hq'p⟩).asIdeal.height := (hheight ⟨q', hq'p⟩).symm

end Assembly

/-- **Every point of an irreducible finite-type `K`-scheme is dominated in coheight by a point
of any nonempty open** (PROVEN — this is the pointwise form of
`topologicalKrullDim_le_of_isOpenImmersion_of_irreducible` below).

THE PROOF:

1. Coheight is LOCAL: choose an affine open `U = Spec R` containing `x`; then
   `coheight_X x = coheight_U x = height 𝔭ₓ` (`coheight_eq_of_isOpenImmersion`, then
   `idealHeight_eq_coheight`).
2. `LocallyOfFiniteType strX` makes `R` a finitely generated `K`-algebra and `U` is irreducible
   (a nonempty open of the irreducible `X`).  Both halves are proved inline here: irreducibility
   is `Topology.IsOpenEmbedding.irreducibleSpace`, and the algebra structure is `appTop` of
   `f ≫ strX` conjugated by the two `Scheme.ΓSpecIso`s, `RingHom.FiniteType` surviving the
   conjugation by `RingHom.finiteType_respectsIso`.  (In the `ULift ℚ`-shaped copy in
   `Modularity/MoretBailly.lean` this step is still an open `sorry`.)
3. `C ∩ U` is nonempty — two nonempty opens of an irreducible space meet — and open, so it
   contains a nonempty basic open `D(r)` with `r` not nilpotent.
4. `exists_isPrime_notMem_height_le_of_finiteType_of_irreducible` produces a prime of `R`
   avoiding `r` whose height dominates that of `𝔭ₓ`; it lies in `D(r) ⊆ C`. ∎ -/
theorem exists_coheight_le_of_isOpenImmersion_of_irreducible {C X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType strX] [IrreducibleSpace ↥X]
    (j : C ⟶ X) [IsOpenImmersion j] [Nonempty ↥C] (x : ↥X) :
    ∃ y : ↥C, Order.coheight x ≤ Order.coheight (j.base y) := by
  obtain ⟨R, f, hfimm, hxmem, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := X) (x := x) (U := ⊤) trivial
  haveI := hfimm
  obtain ⟨x₀, rfl⟩ := hxmem
  haveI hx₀p : x₀.asIdeal.IsPrime := x₀.isPrime
  obtain ⟨algR, hRfin, hRirr⟩ :
      ∃ _ : Algebra K R, Algebra.FiniteType K R ∧ IrreducibleSpace (PrimeSpectrum R) := by
    haveI : Nonempty ↥(Spec R) := ⟨x₀⟩
    haveI hirrR : IrreducibleSpace ↥(Spec R) := f.isOpenEmbedding.irreducibleSpace
    haveI : LocallyOfFiniteType (f ≫ strX) := inferInstance
    have hQ : RingHom.FiniteType (f ≫ strX).appTop.hom :=
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) (f ≫ strX) ‹_›
    letI : Algebra K R :=
      RingHom.toAlgebra (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (f ≫ strX).appTop ≫ (Scheme.ΓSpecIso R).hom).hom)
    refine ⟨inferInstance, ?_, hirrR⟩
    have hfin : RingHom.FiniteType (algebraMap K R) := by
      show RingHom.FiniteType (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (f ≫ strX).appTop ≫ (Scheme.ΓSpecIso R).hom).hom)
      rw [CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_left_isIso,
        CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_right_isIso]
      exact hQ
    exact RingHom.finiteType_algebraMap.mp hfin
  obtain ⟨r, hr, hrsub⟩ :
      ∃ r : R, ¬ IsNilpotent r ∧
        ∀ z : ↥(Spec R), r ∉ z.asIdeal → f.base z ∈ Set.range j.base := by
    have hUopen : IsOpen (Set.range f.base) := f.isOpenEmbedding.isOpen_range
    have hVopen : IsOpen (Set.range j.base) := j.isOpenEmbedding.isOpen_range
    have hUne : (Set.univ ∩ Set.range f.base).Nonempty := ⟨f.base x₀, trivial, ⟨x₀, rfl⟩⟩
    have hVne : (Set.univ ∩ Set.range j.base).Nonempty :=
      ⟨j.base (Classical.arbitrary ↥C), trivial, ⟨Classical.arbitrary ↥C, rfl⟩⟩
    obtain ⟨w, -, hwU, hwV⟩ :=
      (IrreducibleSpace.isIrreducible_univ ↥X).2 _ _ hUopen hVopen hUne hVne
    obtain ⟨z, rfl⟩ := hwU
    have hWopen : IsOpen (f.base ⁻¹' (Set.range j.base)) :=
      hVopen.preimage f.isOpenEmbedding.continuous
    have hzW : z ∈ f.base ⁻¹' (Set.range j.base) := hwV
    obtain ⟨v, hvb, hzv, hvsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hzW hWopen
    obtain ⟨r, rfl⟩ := hvb
    refine ⟨r, ?_, ?_⟩
    · intro hnilp
      exact (PrimeSpectrum.mem_basicOpen r z).mp hzv
        (nilradical_le_prime z.asIdeal (mem_nilradical.mpr hnilp))
    · intro z' hz'
      exact hvsub ((PrimeSpectrum.mem_basicOpen r z').mpr hz')
  obtain ⟨q, hqp, hqr, hqht⟩ :=
    exists_isPrime_notMem_height_le_of_finiteType_of_irreducible (k := K) hRirr hr x₀.asIdeal
  obtain ⟨y, hy⟩ := hrsub ⟨q, hqp⟩ hqr
  refine ⟨y, ?_⟩
  rw [hy, coheight_eq_of_isOpenImmersion (x := x₀) f,
    coheight_eq_of_isOpenImmersion (x := (⟨q, hqp⟩ : ↥(Spec R))) f,
    ← idealHeight_eq_coheight R x₀, ← idealHeight_eq_coheight R ⟨q, hqp⟩]
  exact hqht

/-- **A locally standard smooth `K`-algebra of relative dimension one has Krull dimension at
most one** (sorry leaf — 2026-07-27, and it is ALL that is left of the old dimension leaf
`topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one`, which is now a THEOREM over it).

TRUE and classical.  `RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
(algebraMap K R)` says there are `f₁,…,f_m` generating the unit ideal of `R` with each
`R_{f_i} ≅ K[x₁,…,x_n]/(g₁,…,g_{n-1})` carrying an invertible Jacobian minor.  Such a ring has
Krull dimension `1` (Stacks `02JS` for the relative dimension of a smooth morphism, `0A21` for
dimension = transcendence degree over a field).  `R` is allowed to be trivial, in which case
`ringKrullDim R = ⊥ ≤ 1`; only the UPPER bound is asked, so the easy direction of the dimension
theorem is not enough.

**WHY THIS IS THE LEAF AND NOT THE SCHEME STATEMENT.** Everything scheme-theoretic in the old
leaf is now proven immediately below: the reduction of `topologicalKrullDim Y ≤ 1` to a bound on
each affine chart is `topologicalKrullDim_eq_iSup_coheight` plus `coheight_eq_of_isOpenImmersion`
plus `idealHeight_eq_coheight` plus `Ideal.height_le_ringKrullDim_of_isPrime`, and the transport
of the smoothness hypothesis onto the chart is `HasRingHomProperty.appTop` for
`SmoothOfRelativeDimension 1` (whose ring-hom property is literally `Locally
(IsStandardSmoothOfRelativeDimension 1)`) conjugated by the two `Scheme.ΓSpecIso`s, which
`RingHom.locally_respectsIso` lets through.  So what remains has NO scheme theory in it at all.

**PIN AUDIT — RE-RUN THESE, TWO OF THEM HAVE ALREADY GONE STALE ONCE.**

* **present**: `MvPolynomial.ringKrullDim_of_isNoetherianRing`
  (`Mathlib/RingTheory/KrullDimension/Polynomial.lean:119`) gives `ringKrullDim K[x₁…xₛ] = s` —
  note this makes the `proof_wanted` `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing`
  at `Mathlib/RingTheory/KrullDimension/Basic.lean:94` **stale**;
* **present**: Noether normalization, `exists_integral_inj_algHom_of_fg`
  (`Mathlib/RingTheory/NoetherNormalization.lean:276`, ROOT namespace, not `Algebra.`);
* **present**: `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
  (`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`) — `Ω` is free of rank `n`;
* **NO LONGER MISSING**: what the previous version of this audit called "MISSING (1):
  invariance of `ringKrullDim` under an injective integral ring extension".  The half that is
  actually needed is `ringKrullDim_le_of_isIntegral`, **proven above in this file** (four lines,
  from `Ideal.IsIntegral.comap_lt_comap`), and going-up in the other direction is
  `exists_isPrime_under_eq_and_le_height_of_isIntegral`, also proven above.  Do not go looking
  for it in `Mathlib`;
* **MISSING**: the link from `IsStandardSmoothOfRelativeDimension 1` to `s = 1` in the Noether
  normalization — i.e. relative dimension equals transcendence degree.  There is still **no
  occurrence of `ringKrullDim` or `krullDim` anywhere under `Mathlib/RingTheory/Smooth/`,
  `Mathlib/RingTheory/Extension/` or in `Mathlib/RingTheory/Presentation.lean`**, so nothing at
  this pin connects a smooth presentation to any dimension, and mathlib has no
  smooth-implies-regular statement either (`grep -rn "IsRegularLocalRing"
  Mathlib/RingTheory/Smooth/ Mathlib/AlgebraicGeometry/` is empty).

So the leaf is ONE named ring-theoretic statement away, not a whole dimension theory.  Finding
that link in the pin refutes this verdict.

**THE ROUTE A NEXT OWNER SHOULD PRICE FIRST**, since it is the one that does not need `dim =
trdeg`: `~/cs/FLT/FLT/Slop/DimensionTheorem/` proves the LOCAL dimension theorem
`ringKrullDim R = minGenPrimary R` for Noetherian local rings, sorry-free and with clean axioms
(see its `README.md`; `Main.lean`'s `dimension_theorem`).  Vendoring it (five files, pin-drift
audit required — its mathlib pin is `81a5d2` against our `a3364fa`) would reduce the leaf to
exhibiting a length-`1` system of parameters in each `R_𝔭`, which the Jacobian criterion
supplies.  That is a costing, not a proof; it has NOT been attempted here.

RELATION TO `Modularity/MoretBailly.lean`: that file does NOT own this statement; it takes
`hdim : topologicalKrullDim ↥C ≤ 1` as a HYPOTHESIS on every declaration in the cluster and
pushes the obligation out to `X0.lean`.  So this leaf is genuinely unowned there, and whoever
proves it here discharges that hypothesis for both files. -/
theorem ringKrullDim_le_one_of_locally_isStandardSmoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [Algebra K R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap K R)) :
    ringKrullDim R ≤ 1 :=
  sorry

/-- **A smooth curve over a field is one-dimensional** (**PROVEN 2026-07-27** over the single
ring-theoretic leaf `ringKrullDim_le_one_of_locally_isStandardSmoothOfRelativeDimension_one`
stated immediately above — was itself a sorry leaf, the dimension half of the
old `topologicalKrullDim_normalization_le_one`).

TRUE and classical: `SmoothOfRelativeDimension 1 strY` says that every point of `Y` has an
affine neighbourhood on which `strY` is *standard* smooth of relative dimension `1`, i.e.
`Γ(Y, V) ≅ K[x₁, …, x_m] / (f₁, …, f_{m-1})` with invertible Jacobian; such a ring has Krull
dimension `1` (Stacks `02JS` for the relative dimension of a smooth morphism, `0A21` for
dimension = transcendence degree over a field), and `topologicalKrullDim` of a scheme is the
supremum of the Krull dimensions of its local rings.  No hypothesis beyond smoothness is
needed: `SmoothOfRelativeDimension` already entails `LocallyOfFinitePresentation` and hence
`LocallyOfFiniteType`, which is what makes the dimension finite at all.

Only `≤ 1` is asked, so the EASY direction of the dimension theorem is not enough — the bound
that has to be produced is the upper one.  Note `Y` is allowed to be empty, in which case
`topologicalKrullDim Y = ⊥ ≤ 1`.

**WHAT THE PROOF BELOW DOES**, and what it does NOT do.  It is pure localisation bookkeeping:
`topologicalKrullDim_eq_iSup_coheight` turns the bound into a pointwise one; an affine chart
`f : Spec R ⟶ Y` around each point carries the coheight to `Ideal.height` there
(`coheight_eq_of_isOpenImmersion`, `idealHeight_eq_coheight`), which
`Ideal.height_le_ringKrullDim_of_isPrime` bounds by `ringKrullDim R`; and
`HasRingHomProperty.appTop` for `SmoothOfRelativeDimension 1` — whose ring-hom property is
literally `Locally (IsStandardSmoothOfRelativeDimension 1)` — transports the smoothness onto
that chart, `RingHom.locally_respectsIso` absorbing the two `Scheme.ΓSpecIso` conjugations.
The mathematics is untouched and sits entirely in the leaf above.

Note no hypothesis beyond smoothness is needed: `SmoothOfRelativeDimension` already entails
`LocallyOfFinitePresentation` and hence `LocallyOfFiniteType`.  The earlier version of this
docstring recorded the reduction as needing `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`
and `topologicalKrullDim_subspace_le`; the coheight route above is shorter and is what is used.

**SUPERSEDED AUDITS** (2026-07-27).  Two route audits used to live here, one of them concluding
IRREDUCIBLE at this pin over two MISSING items.  Both have moved — corrected — into the leaf's
own docstring above, where they belong now that the leaf is the only open thing.  The
correction worth flagging in passing: their "MISSING (1), invariance of `ringKrullDim` under an
injective integral extension" is **not missing**; the half that is needed is
`ringKrullDim_le_of_isIntegral`, proven in this file. -/
theorem topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one {Y : Scheme.{u}}
    (strY : Y ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 strY] :
    topologicalKrullDim Y ≤ 1 := by
  rw [topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun y => ?_
  obtain ⟨R, f, hfimm, hymem, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := Y) (x := y) (U := ⊤) trivial
  haveI := hfimm
  obtain ⟨y₀, rfl⟩ := hymem
  haveI : y₀.asIdeal.IsPrime := y₀.isPrime
  haveI : SmoothOfRelativeDimension 1 (f ≫ strY) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (f ≫ strY))
  have hQ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (f ≫ strY).appTop.hom :=
    HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension 1) (f ≫ strY) ‹_›
  letI : Algebra K R :=
    RingHom.toAlgebra (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (f ≫ strY).appTop ≫ (Scheme.ΓSpecIso R).hom).hom)
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K R) := by
    show RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (f ≫ strY).appTop ≫ (Scheme.ΓSpecIso R).hom).hom)
    rw [CommRingCat.hom_comp,
      (RingHom.locally_respectsIso
        RingHom.isStandardSmoothOfRelativeDimension_respectsIso).cancel_left_isIso,
      CommRingCat.hom_comp,
      (RingHom.locally_respectsIso
        RingHom.isStandardSmoothOfRelativeDimension_respectsIso).cancel_right_isIso]
    exact hQ
  rw [coheight_eq_of_isOpenImmersion (x := y₀) f, ← idealHeight_eq_coheight R y₀]
  exact le_trans Ideal.height_le_ringKrullDim_of_isPrime
    (ringKrullDim_le_one_of_locally_isStandardSmoothOfRelativeDimension_one (K := K) hloc)

/-- **A nonempty open subscheme of an irreducible scheme of finite type over a field has the
full dimension of the ambient scheme** (**PROVEN 2026-07-27, sorry-free** — was the transfer
half of the old `topologicalKrullDim_normalization_le_one`).

TRUE and classical.  This is the direction `Mathlib` does not supply: its whole
`topologicalKrullDim` API (`Topology.IsInducing.topologicalKrullDim_le`,
`IsHomeomorph.topologicalKrullDim_eq`, `topologicalKrullDim_subspace_le`) gives only
`dim (subspace) ≤ dim (ambient)`.  Combined with `topologicalKrullDim_subspace_le` this
upgrades to an EQUALITY, which is the "dense opens of a variety are equidimensional" fact.

Both geometric hypotheses are load-bearing and neither may be dropped:

* WITHOUT `IrreducibleSpace X`: take `X = Spec (K[s] × K[u,v])`, two components of dimensions
  `1` and `2`, and `C` the first component.  `C` is a nonempty open, `dim C = 1`,
  `dim X = 2`.
* WITHOUT finite type over a FIELD: take `X = Spec ℤ_[p]` and `C` its generic point, a
  nonempty — indeed dense — open with `dim C = 0` while `dim X = 1`.  Over a general base a
  dense open may drop dimension.
* WITHOUT `[Nonempty C]`: an empty `C` has `dim C = ⊥`.

**THIS IS THE GENERAL-`K` FORM OF A LEMMA THAT WAS ALREADY PROVEN OVER `ULift ℚ`**, in
`Modularity/MoretBailly.lean`, as
`topologicalKrullDim_le_of_isOpenImmersion_of_locallyOfFiniteType`, itself over the leaf
`exists_coheight_le_of_isOpenImmersion_of_locallyOfFiniteType` there (still open at the time of
writing).  That module is DOWNSTREAM of this one, so the transport had to be a HOIST, and it
is: the whole machine is proved above in this file, over an arbitrary base field, and the
`ℚ`-shaped pair there is now redundant.  **The collapse is owed and is deliberately not done
here** — `MoretBailly.lean` has many concurrent owners; whoever does it should re-derive both
declarations there from these two, per the module docstring's standing instruction not to prove
the same theorem twice.

TWO THINGS WERE OWED BEYOND A COPY, and both are discharged:

* the `ℚ`-shaped proof picks a RATIONAL point out of an infinite field, and over a FINITE `K`
  no such point need exist.  The replacement is a contraction along the integral extension
  `MvPolynomial (Fin s) K → MvPolynomial (Fin s) (AlgebraicClosure K)`; see
  `exists_ltSeries_length_eq_notMem_of_mvPolynomial` above.  It is the ONLY step that changed.
* the `ℚ`-shaped copy leaves a sorried plumbing `have` — that the affine chart carries a
  finitely generated `K`-algebra structure with irreducible spectrum.  It is PROVEN here,
  inside `exists_coheight_le_of_isOpenImmersion_of_irreducible`: irreducibility from
  `Topology.IsOpenEmbedding.irreducibleSpace`, finite type from `HasRingHomProperty.appTop`
  conjugated by the two `Scheme.ΓSpecIso`s with `RingHom.finiteType_respectsIso`.

The threading that makes this applicable at `i.toNormalization` is that `IsIntegral Y` gives
`IsIntegral i.normalization` and hence `IrreducibleSpace` — free here, whereas the `ℚ`-shaped
copy had to receive it from its consumer. -/
theorem topologicalKrullDim_le_of_isOpenImmersion_of_irreducible {C X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType strX] [IrreducibleSpace X]
    (j : C ⟶ X) [IsOpenImmersion j] [Nonempty C] :
    topologicalKrullDim X ≤ topologicalKrullDim C := by
  rw [topologicalKrullDim_eq_iSup_coheight, topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨y, hy⟩ := exists_coheight_le_of_isOpenImmersion_of_irreducible strX j x
  refine le_trans ?_ (le_iSup (fun y : ↥C => (Order.coheight y : WithBot ℕ∞)) y)
  rw [← coheight_eq_of_isOpenImmersion (x := y) j]
  exact_mod_cast hy

/-- **The normalized proper model of a smooth curve is one-dimensional** (PROVEN over the two
leaves above — was itself a sorry leaf until 2026-07-27).

TRUE: `i.normalization` contains the smooth curve `Y` as a dense open (Zariski's Main
Theorem), and is finite over the finite-type `K`-scheme `P`, so it is itself of finite type
over `K` and has the same function field as `Y`; a variety of finite type over a field has
topological dimension equal to the transcendence degree of its function field, which is `1`
because `Y ⟶ Spec K` is smooth of relative dimension `1`.  Stacks tags `0A21` (dimension =
transcendence degree) and `02JS` (relative dimension of a smooth morphism).

**Why this is the right leaf, and what the old one contained** (2026-07-27): the previous
`finite_compl_range_toNormalization` bundled this dimension fact together with a chain of
noetherian-ness bookkeeping and a point-set argument.  Both of the latter are now proven —
see `finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one` above and the assembly
below — so the ONLY thing an attacker has to produce is this bound.  Only `≤ 1` is needed;
the matching lower bound is never used.

**DECOMPOSED 2026-07-27 — this is no longer a leaf.** It splits, with all the glue proven,
along the obvious seam: the dimension of `Y` itself, and the transfer of a dimension bound
from a dense open to the ambient scheme.  The two halves are
`topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` and
`topologicalKrullDim_le_of_isOpenImmersion_of_irreducible`, stated immediately above; the
paragraph below records what mathlib does and does not supply for each.  The threading that
makes the second one applicable is that `IsIntegral Y` gives `IsIntegral i.normalization` and
hence `IrreducibleSpace`, which is precisely the hypothesis the transfer needs and which the
`ULift ℚ`-shaped copy of this statement in `Modularity/KhareWintenberger.lean` had to have
threaded in from its consumer.

`Mathlib` has `topologicalKrullDim` and `Order.coheight`, and `Scheme.functionField`, but no
dimension-equals-transcendence-degree theorem and no link at all between
`SmoothOfRelativeDimension n` and any dimension of the source — which is why both halves are
leaves rather than one of them being free. -/
theorem topologicalKrullDim_normalization_le_one {Y P : Scheme.{u}}
    {strP : P ⟶ Spec (CommRingCat.of K)} [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y]
    (_hY : SmoothOfRelativeDimension 1 (i ≫ strP)) :
    topologicalKrullDim i.normalization ≤ 1 := by
  haveI : IsFinite i.fromNormalization := isFinite_fromNormalization strP i
  haveI : IsIntegral i.normalization := inferInstance
  haveI : LocallyOfFiniteType (i.fromNormalization ≫ strP) := inferInstance
  haveI : Nonempty Y := inferInstance
  refine le_trans (topologicalKrullDim_le_of_isOpenImmersion_of_irreducible
    (i.fromNormalization ≫ strP) i.toNormalization) ?_
  exact topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one (i ≫ strP)

/-- **The complement of a curve in its compactification is finite** (PROVEN over
`topologicalKrullDim_normalization_le_one`).

`i.toNormalization` is a dominant open immersion into the integral scheme
`i.normalization`, so its complement is a proper closed subset of an irreducible
noetherian space of dimension one, hence a finite set of closed points.

Everything except the dimension bound is proven here.  The two halves of the assembly are:

* *noetherian-ness of `i.normalization`*, which is where the sibling leaf
  `isFinite_fromNormalization` is consumed — `P` is locally noetherian because it is of
  finite type over a field, `i.normalization` is finite and hence of finite type over `P`,
  and both are quasi-compact because `Spec K` is;
* *the point-set argument*, isolated as
  `finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one` above.

The complement is closed because `IsOpenImmersion i.toNormalization` is Zariski's Main
Theorem (`Mathlib`'s instance needs `LocallyQuasiFinite`, `LocallyOfFiniteType`,
`IsSeparated` and `QuasiCompact` for `i`, all of which an open immersion with
`[QuasiCompact i]` supplies), and it is not everything because `IsIntegral Y` makes `Y`
nonempty. -/
theorem finite_compl_range_toNormalization {Y P : Scheme.{u}}
    {strP : P ⟶ Spec (CommRingCat.of K)} [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y]
    (_hY : SmoothOfRelativeDimension 1 (i ≫ strP)) :
    (Set.range i.toNormalization.base)ᶜ.Finite := by
  haveI : IsNoetherianRing (CommRingCat.of K) := inferInstanceAs (IsNoetherianRing K)
  haveI : IsFinite i.fromNormalization := isFinite_fromNormalization strP i
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian strP
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace strP
  haveI : IsLocallyNoetherian i.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian i.fromNormalization
  haveI : CompactSpace i.normalization :=
    QuasiCompact.compactSpace_of_compactSpace i.fromNormalization
  haveI : IsNoetherian i.normalization := ⟨⟩
  refine finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one
    (topologicalKrullDim_normalization_le_one i _hY)
    (isClosed_compl_iff.mpr i.toNormalization.isOpenEmbedding.isOpen_range) ?_
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  intro h
  exact (h ▸ Set.mem_univ (i.toNormalization.base y) :
    i.toNormalization.base y ∈ (Set.range i.toNormalization.base)ᶜ) (Set.mem_range_self y)

/-! ### The theorem -/

/-- **Every smooth curve over a perfect field has a smooth compactification** (PROVEN over
the four leaves above).

The construction is the one in the module docstring: compactify as a scheme (Nagata),
then normalize.  What `Mathlib` supplies for free, and what makes this assembly short, is
that both of the properties relating `Y` to `X` — openness of the immersion and density of
the image — are already theorems about the relative normalization:
`IsOpenImmersion i.toNormalization` is Zariski's Main Theorem, and
`IsDominant i.toNormalization` holds by construction.  Everything else is the properness
and smoothness of `X`, which are the leaves.

`IsIntegral Y` (irreducible and reduced) is required and is not a weakening: without
irreducibility the relative normalization is still defined but `IsIntegral i.normalization`
fails, and the finiteness of the complement is false for a disconnected `Y` with an
infinite component structure.  A geometrically connected smooth curve over a field is
integral, so the hypothesis is met in the intended application. -/
theorem exists_isSmoothCompactification [PerfectField K] {Y : Scheme.{u}}
    (strY : Y ⟶ Spec (CommRingCat.of K)) [IsIntegral Y] [QuasiCompact strY]
    [IsSeparated strY] [hsm : SmoothOfRelativeDimension 1 strY] :
    ∃ (X : Scheme.{u}) (strX : X ⟶ Spec (CommRingCat.of K)) (j : Y ⟶ X),
      IsSmoothCompactification strY strX j := by
  have _ : Smooth strY := SmoothOfRelativeDimension.smooth (n := 1) (f := strY)
  obtain ⟨P, strP, i, hi, hqc, hP, hcomm⟩ := exists_isOpenImmersion_isProper strY
  -- `i` inherits from `strY` everything Zariski's Main Theorem needs.
  have _ : IsOpenImmersion i := hi
  have _ : QuasiCompact i := hqc
  have _ : IsProper strP := hP
  -- the smoothness hypothesis, transported along `i ≫ strP = strY`
  have hsmP : SmoothOfRelativeDimension 1 (i ≫ strP) := hcomm ▸ hsm
  -- the two leaves that make `X` a smooth proper curve
  have _ : IsFinite i.fromNormalization := isFinite_fromNormalization strP i
  have hsX : SmoothOfRelativeDimension 1 (i.fromNormalization ≫ strP) :=
    smoothOfRelativeDimension_one_fromNormalization i hsmP
  have hfin : (Set.range i.toNormalization.base)ᶜ.Finite :=
    finite_compl_range_toNormalization i hsmP
  refine ⟨i.normalization, i.fromNormalization ≫ strP, i.toNormalization, ?_⟩
  exact
    { comm := by
        rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hcomm]
      isOpenImmersion := inferInstance
      isDominant := inferInstance
      isProper := inferInstance
      smooth := hsX
      finite_compl := hfin }

/-- **The range of a projection of an arbitrary pullback square of schemes.**

`Mathlib`'s `Scheme.Pullback.range_fst` states this for the CHOSEN pullback
`Limits.pullback f g`; this transports it along `IsPullback.isoPullback`, so that a consumer
stated over an arbitrary pullback square — which `Mathlib`'s `geometrically` forces, since it
unfolds to a statement about all such squares — can use it without transporting first.

Kept inside `namespace AlgebraicGeometry` for the same reason as the topological
preliminaries at the top of the file: this module adds no root-level names to the cone of
everything that `public import`s it. -/
theorem range_base_of_isPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  rw [← Scheme.Pullback.range_fst f g, ← h.isoPullback_hom_fst]
  exact (Scheme.Hom.surjective (f := h.isoPullback.hom)).range_comp _

/-- **A field extension is universally open** (PROVEN — `Mathlib` has it, see the audit
correction below).  The base-change input behind `denseRange_of_isPullback`, and the last
thing that was left of the old `geometricallyConnected_of_isSmoothCompactification`.

TRUE and classical: for any field extension `L / K` the morphism `Spec L ⟶ Spec K` is
universally open.  Stacks tag `0383`; EGA IV 2.4.9.  No hypothesis relating `L` to `K` is
needed, because a ring homomorphism between fields is automatically injective, so every
`y : Spec L ⟶ Spec K` IS a field extension.

## CORRECTION to the previous "why this is not free at this pin" audit (2026-07-27)

That audit was WRONG, and it was wrong in the way this project's doctrine warns about: it
surveyed exactly one route, found it blocked, and concluded the leaf was expensive.  It said
`Mathlib`'s only route from flatness to openness is `AlgebraicGeometry.UniversallyOpen.of_flat`,
which additionally requires `LocallyOfFinitePresentation` — true of *that* lemma, and the
observation that `Spec L ⟶ Spec K` is of finite presentation exactly when `L / K` is FINITE
(Zariski's lemma) is also correct, so the `of_flat` route genuinely cannot serve a consumer
quantifying over all `L`, `ℚ̄ / ℚ` included.  What the audit missed is that `of_flat` is not
the only route: the very same file, `Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean`,
closes with a strictly more general instance

  `instance [IsIntegral Y] [Subsingleton Y] : UniversallyOpen f`

for an ARBITRARY `f : X ⟶ Y`.  A one-point integral scheme is the spectrum of a field, so this
says that **every** morphism into `Spec K` is universally open — no flatness hypothesis, no
finite presentation, no relation between source and target at all.  It is backed by
`PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`, i.e. by the ring-level fact
that `Spec (A ⊗[K] B) ⟶ Spec B` is open for any two `K`-algebras, which is the statement the
transcendence/colimit argument below was going to reconstruct by hand.

Both instances needed to fire it are already in `Mathlib` too: `Unique (Spec (.of K))` for a
field (`AlgebraicGeometry/Scheme.lean`) and `IsIntegral (Spec R)` for `[IsDomain R]`
(`AlgebraicGeometry/Properties.lean`).  So the proof is `inferInstance`, and the filtered-colimit
development over `Mathlib.AlgebraicGeometry.AffineTransitionLimit` that the audit prescribed is
not needed and should not be written.

The declaration is kept rather than inlined at its one call site so that
`denseRange_of_isPullback` continues to read as a statement about a named classical input, and
so that the correction above is recorded where the next reader of that audit will find it.

Note what is NOT needed and should not be added: surjectivity, faithful flatness, and
quasi-compactness of anything play no part.  Only openness of the base-changed projection is
consumed, and it is consumed through `Mathlib`'s own
`UniversallyOpen.isStableUnderBaseChange`, so the statement is in exactly the form that
instance takes. -/
theorem universallyOpen_of_specField {L : Type u} [Field L]
    (y : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) : UniversallyOpen y :=
  inferInstance

/-- **A dominant morphism stays dominant after base change along a field extension** (PROVEN
over `universallyOpen_of_specField`).

`px : V ⟶ X'` is a base change of the universally open `y`, hence open; and `m` is a base
change of `j`, hence has range exactly `px ⁻¹ (range j)`.  So a nonempty open `U ⊆ V` has
open nonempty image `px(U)`, which meets the dense `range j`, and any `b ∈ U` mapping into
`range j` lies in `range m`.  That is the whole proof, and none of it is the leaf: the leaf
is only the openness of `px`.

Only `IsDominant j` is used, so this is genuinely independent of the compactification: no
smoothness, no properness, no perfect field.

Stated over an ARBITRARY pullback square rather than over `Limits.pullback` so that the
consumer does not have to transport along a `pullbackRightPullbackFstIso`: `Mathlib`'s
`geometrically` unfolds to a statement about all pullback squares, and this shape plugs
straight in.

## FALSITY AUDIT (2026-07-27) — the previous statement was FALSE, over an arbitrary base

The leaf used to quantify over an ARBITRARY base scheme `S`.  Its own justification named the
false step: "`y : Spec L ⟶ S` with `L` a field is flat" holds over a FIELD base and nowhere
else — `𝔽_p` is not flat over `ℤ`.

*Counterexample.*  `S = X' = Spec ℤ`, `strX = 𝟙`, `Y' = Spec ℚ`, and `strY = j` the generic
point `Spec ℚ ⟶ Spec ℤ`.  Then `j` is dominant, because `ℤ` is a domain and so `{(0)}` is
dense in `Spec ℤ`.  Take `L = 𝔽_p`.  Now `V = X' ×ₛ Spec L ≅ Spec 𝔽_p` is a ONE-POINT space,
while `W = Y' ×ₛ Spec L = Spec (ℚ ⊗ℤ 𝔽_p) = Spec 0 = ∅`, since `p` is a unit in `ℚ` and zero
in `𝔽_p`.  The unique `m : ∅ ⟶ V` has empty range, which is not dense in a nonempty space.

Both hypotheses added below hold in that counterexample — `hcomm` because `strX = 𝟙`, and
`hm₂` because `W` is initial, so any two morphisms out of it agree — which is what shows the
restriction of the base to a FIELD is INDEPENDENTLY necessary rather than an artefact of the
other repairs.

*Why `[Flat y]` is NOT the right repair, although it kills the counterexample above.*  It is
still insufficient: take `S = X' = Spec ℤ`, `strX = 𝟙`, `Y' = ∐_p Spec 𝔽_p` and `j` the
canonical map, which is dominant because the closed points are dense in `Spec ℤ`.  Base
change along `y : Spec ℚ ⟶ Spec ℤ`, which IS flat, gives `V = Spec ℚ` (one point) and
`W = ∐_p Spec (𝔽_p ⊗ℤ ℚ) = ∅`.  What fails here is quasi-compactness of `j`, not flatness of
`y`.  Over a field base neither question arises, and a field base is what the consumer has —
so restricting `S` is both the weakest sufficient repair and the faithful one.

## Two hypotheses ADDED (2026-07-27), each supplied free at the one call site

* `hcomm : j ≫ strX = strY`.  Without it `j` need not be a morphism over the base at all, so
  `W` is not `Y' ×_{X'} V` and the statement is not about the base change of `j`.  Supplied
  by `IsSmoothCompactification.comm`.
* `hm₂ : m ≫ qx = qy`.  `hm₁` pins only the `X'`-component of `m`, leaving `m ≫ qx` free, so
  `m` need not be the base change of `j` but merely some lift making one triangle commute.
  Supplied by `pullback.lift_snd`.

Neither is a weakening of the intended content: together they are exactly what makes `m` *the*
base change of `j`, which is what the name of the leaf claims. -/
theorem denseRange_of_isPullback {X' Y' W V : Scheme.{u}}
    {strY : Y' ⟶ Spec (CommRingCat.of K)} {strX : X' ⟶ Spec (CommRingCat.of K)}
    {j : Y' ⟶ X'} [IsDominant j] (hcomm : j ≫ strX = strY)
    {L : Type u} [Field L] {y : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
    {py : W ⟶ Y'} {qy : W ⟶ Spec (CommRingCat.of L)} (hW : IsPullback py qy strY y)
    {px : V ⟶ X'} {qx : V ⟶ Spec (CommRingCat.of L)} (hV : IsPullback px qx strX y)
    (m : W ⟶ V) (hm₁ : m ≫ px = py ≫ j) (hm₂ : m ≫ qx = qy) :
    DenseRange m.base := by
  haveI : UniversallyOpen y := universallyOpen_of_specField y
  haveI : UniversallyOpen px := MorphismProperty.of_isPullback hV.flip ‹UniversallyOpen y›
  -- `m` is the base change of `j` along `px`, by pasting the right-hand square `hV` off `hW`
  have hsq : IsPullback m py px j := by
    refine IsPullback.of_right ?_ hm₁ hV.flip
    rw [hm₂, hcomm]
    exact hW.flip
  have hrange : Set.range m.base = px.base ⁻¹' Set.range j.base := range_base_of_isPullback hsq
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨a, haU⟩ := hUne
  obtain ⟨x, ⟨b, hbU, hbx⟩, hxj⟩ :=
    dense_iff_inter_open.mp (Scheme.Hom.denseRange j) _ (px.isOpenMap U hU)
      ⟨px.base a, a, haU, rfl⟩
  exact ⟨b, hbU, hrange ▸ Set.mem_preimage.mpr (hbx ▸ hxj)⟩

/-- **A compactification of a geometrically connected curve is geometrically connected**
(PROVEN over `denseRange_of_isPullback`).

TRUE, and it is the one clause of the modular interface that the construction above does
not deliver directly.  The argument is short and purely topological once base change is in
place: `Spec K̄ ⟶ Spec K` is flat, so `Y_K̄ ⟶ X_K̄` is again a dominant open immersion; a
dense subspace of a space is connected only together with the whole space, i.e. the
closure of a connected subspace is connected, and the closure of `Y_K̄` is `X_K̄`.

Stated as a separate leaf rather than folded into `IsSmoothCompactification` because it is
a hypothesis-carrying implication, not a property of `(X, j)` alone: a compactification of
a DISCONNECTED curve is of course disconnected, and `Fermat.IsCompactificationY0` — which
is used at the degenerate level `N = 0`, where the curve is empty — deliberately does not
ask for it.  Only `Fermat.IsX0Compactification`, which is restricted to `N ≥ 1`, does.

The density-of-base-change step is `denseRange_of_isPullback` above, itself now a THEOREM
over `universallyOpen_of_specField`, which is in turn PROVEN from `Mathlib`'s
`[IsIntegral Y] [Subsingleton Y]` instance for `UniversallyOpen`; the closure-of-a-connected-set
half is `connectedSpace_of_denseRange`, proven at the top of this file.  So **nothing sorried
remains on this path at all**.  Note that only
`h.isDominant` and `h.comm` are consumed — properness, smoothness and the finiteness of the
complement play no part, which is why the leaf above carries none of them. -/
theorem geometricallyConnected_of_isSmoothCompactification {Y X : Scheme.{u}}
    {strY : Y ⟶ Spec (CommRingCat.of K)} {strX : X ⟶ Spec (CommRingCat.of K)} {j : Y ⟶ X}
    (h : IsSmoothCompactification strY strX j) [GeometricallyConnected strY] :
    GeometricallyConnected strX := by
  haveI : IsDominant j := h.isDominant
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y ↦ ?_⟩
  have hW : IsPullback (pullback.fst strY y) (pullback.snd strY y) strY y := .of_hasPullback _ _
  have hV : IsPullback (pullback.fst strX y) (pullback.snd strX y) strX y := .of_hasPullback _ _
  have hcond : (pullback.fst strY y ≫ j) ≫ strX = pullback.snd strY y ≫ y := by
    rw [Category.assoc, h.comm]; exact pullback.condition
  exact connectedSpace_of_denseRange
    (Scheme.Hom.continuous (pullback.lift (pullback.fst strY y ≫ j) (pullback.snd strY y) hcond))
    (denseRange_of_isPullback h.comm hW hV _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))

/-! ### Relative dimension and the finiteness of the complement, for a GIVEN compactification

The theorem above *constructs* a smooth compactification, so the consumer that quantifies
over an arbitrary one — `Fermat.IsCompactificationY0`, which carries only `Smooth strX` and
`IsProper strX` — cannot read the relative dimension or the finite complement off it.  This
subsection supplies exactly those two, for an arbitrary `(X, j)`, and reduces them to two
named inputs.

Kept in one block at the end of the file rather than interleaved with the material above so
that the two leaves already dispatched here (`locallyOfFiniteType_fromNormalization`,
`topologicalKrullDim_normalization_le_one`) keep their region untouched.  The module
docstring's leaf table above therefore does NOT list the two leaves added here; see the two
declarations themselves.

DUPLICATION CORRECTION (integration, 2026-07-27).  An earlier version of this note claimed
that the `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` written here was a new
statement, distinct from anything else in the file.  That was WRONG, and it was wrong at the
moment it was written: the same declaration, under the same name, was being added in the same
batch to the earlier part of this file with strictly FEWER hypotheses.  The two collided at
integration and the copy that lived here was DELETED; its route audit was moved into the
surviving declaration's docstring.  What the note says about
`topologicalKrullDim_normalization_le_one` remains true and is kept: that one bounds the
dimension of a relative *normalization*, about which no smoothness is known, from the
smoothness of a dense open inside it, so neither implies the other at this pin.

So this subsection added ONE leaf, `smoothOfRelativeDimension_of_isDominant`; the dimension
bound it also needs is the one already stated above.  **That leaf is now PROVEN
(2026-07-27)**, over the new purely ring-theoretic
`eq_of_isStandardSmoothOfRelativeDimension_of_locally`, so this subsection adds NO leaf at
all; see the declaration's docstring for why the irreducibility verdict recorded there was
wrong. -/

/-- **A space with a dense irreducible image is irreducible.**

The image of an irreducible space under a continuous map is irreducible, the closure of an
irreducible set is irreducible, and a dense range has closure everything.  This is the exact
analogue of `connectedSpace_of_denseRange` at the top of this file, and it is what supplies
`IrreducibleSpace X` to `finite_compl_range_of_topologicalKrullDim_le_one` below from
`IsIntegral Y` alone. -/
theorem irreducibleSpace_of_denseRange {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [IrreducibleSpace β] {f : β → α} (hf : Continuous f) (hd : DenseRange f) :
    IrreducibleSpace α := by
  have h : IsIrreducible (Set.range f) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ β).image f hf.continuousOn
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hd.closure_eq]
  exact h.closure

/-- **The relative dimension is well defined**: a ring map that is standard smooth of relative
dimension `m`, and *locally* standard smooth of relative dimension `n`, with nontrivial target,
has `m = n`.

This is the entire arithmetic content of `smoothOfRelativeDimension_of_isDominant` below, and it
is where the audit that declared that leaf irreducible was wrong.  The audit is correct that
**`Mathlib.AlgebraicGeometry` has no lemma relating `SmoothOfRelativeDimension` at two values of
`n`** — but `Mathlib.RingTheory` does, and it is exactly the invariant one wants: for a nontrivial
standard smooth algebra, `Ω[S⁄R]` is free of rank the relative dimension
(`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`, in
`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`).  Two relative dimensions for one
algebra therefore give two values for one rank.

`Nontrivial A` is load-bearing and the statement is FALSE without it: over the zero ring every
`n` works at once.  Getting a nontrivial *common* localisation is the only real step: from
`Locally` one has a family spanning the unit ideal, and a maximal ideal of `A` must miss one
member `t` of it; `t` is then not nilpotent, so `A_t` is nontrivial, and it inherits both
relative dimensions — `n` from the `Locally` witness, `m` by composing with the localisation
away map, which is standard smooth of relative dimension `0`. -/
theorem eq_of_isStandardSmoothOfRelativeDimension_of_locally
    {R A : Type u} [CommRing R] [CommRing A] [Nontrivial A] {φ : R →+* A} {m n : ℕ}
    (hm : φ.IsStandardSmoothOfRelativeDimension m)
    (hn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ) :
    m = n := by
  obtain ⟨s, hs, hP⟩ := hn
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A
  obtain ⟨t, hts, htm⟩ : ∃ t ∈ s, t ∉ 𝔪 := by
    by_contra h
    push Not at h
    exact h𝔪.ne_top (eq_top_iff.mpr (hs ▸ Ideal.span_le.mpr h))
  haveI : Nontrivial (Localization.Away t) := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    rw [show (1 : Localization.Away t) = algebraMap A _ 1 by simp,
      show (0 : Localization.Away t) = algebraMap A _ 0 by simp] at h
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) _).mp h
    obtain ⟨k, hk⟩ := c.2
    rw [mul_one, mul_zero] at hc
    have hzero : t ^ k = 0 := by simpa using hk.trans hc
    exact htm (h𝔪.isPrime.mem_of_pow_mem k (hzero ▸ 𝔪.zero_mem))
  have h1 : ((algebraMap A (Localization.Away t)).comp φ).IsStandardSmoothOfRelativeDimension n :=
    hP t hts
  have h2 : ((algebraMap A (Localization.Away t)).comp φ).IsStandardSmoothOfRelativeDimension m := by
    have h0 : (algebraMap A (Localization.Away t)).IsStandardSmoothOfRelativeDimension 0 :=
      RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway t
    simpa using h0.comp hm
  letI := ((algebraMap A (Localization.Away t)).comp φ).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away t) := h1
  haveI : Algebra.IsStandardSmoothOfRelativeDimension m R (Localization.Away t) := h2
  have e1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := Localization.Away t) n
  have e2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := Localization.Away t) m
  exact_mod_cast e2.symm.trans e1

/-- **The relative dimension of a smooth morphism propagates from a dense open** (PROVEN
2026-07-27, over `eq_of_isStandardSmoothOfRelativeDimension_of_locally` above; it is the whole
content of the first half of
`Fermat.smoothOfRelativeDimension_finite_compl_of_compactificationY0`).

TRUE and classical.  For a smooth morphism `strX : X ⟶ S` the function sending `x : X` to
the dimension of the fibre `X_{strX x}` at `x` is **locally constant** on `X` (EGA IV
17.10.2; Stacks tag `02NM`, "the relative dimension of a smooth morphism is locally
constant on the source").  So `{x | relative dimension at x = n}` and its complement are
both open; `j` is an open immersion so its range carries relative dimension `n` from
`strY = j ≫ strX`, and `j` is dominant so its range meets every nonempty open.  The
complement is therefore an open set disjoint from a dense set, hence empty.

**Density alone suffices; connectedness of `X` is NOT needed** and is deliberately not a
hypothesis.  (The justification recorded on the consumer in `X0.lean` routed through
"`X` is connected because it contains a dense irreducible open"; that is a strictly weaker
argument, since local constancy already makes every level set open.)

**THE IRREDUCIBILITY VERDICT PREVIOUSLY RECORDED HERE WAS WRONG, and the axis it missed is
worth stating.**  The audit said: `Mathlib`'s `SmoothOfRelativeDimension n f` is a *pointwise*
condition, its whole API is `.smooth`, the `HasRingHomProperty` instance, base change, the
`SmoothOfRelativeDimension 0` instance for open immersions and additivity under composition,
and **not one lemma relates the property at two different values of `n`**.  All of that is
true — *of `Mathlib.AlgebraicGeometry`*.  It is false of `Mathlib.RingTheory`, which the audit
never searched: `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` and its
companion `iff_of_isStandardSmooth` (`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`)
say that over a NONTRIVIAL standard smooth algebra the relative dimension IS the rank of
`Ω[S⁄R]`, hence is unique.  That is precisely the "two values of `n`" lemma, one level down.

**The proof, which needs no local-constancy theorem at all.**  Local constancy of the fibre
dimension (EGA IV 17.10.2, Stacks `02NM`) is the classical route and is genuinely absent from
the pin; it is also unnecessary.  Fix `x : X`.  `Smooth strX` hands us affine opens `U ⊆ S`,
`V ∋ x` with `strX.appLE U V` standard smooth, hence standard smooth of *some* relative
dimension `m` (read off the dimension of the submersive presentation).  It suffices to prove
`m = n`, because the very same chart then witnesses the conclusion at `x`.  Now use density
ONCE: `V` is a nonempty open, so it meets the range of `j`, and
`IsAffineOpen.exists_basicOpen_le` produces a nonempty basic open `D = X.basicOpen a` with
`D ≤ V ⊓ j.opensRange`.  Over `D` the two dimensions are visible simultaneously:

* `m`, because `Γ(X, V) ⟶ Γ(X, D)` is a localisation away from `a`, which is standard smooth
  of relative dimension `0`;
* `n`, because `W := j ⁻¹ᵁ D` is an affine open of `Y` with `j ''ᵁ W = D`, so
  `HasRingHomProperty.appLE` applied to `strY` on `(U, W)` gives
  `Locally (IsStandardSmoothOfRelativeDimension n)` for `strY.appLE U W`, which factors as
  `strX.appLE U D ≫ j.appLE D W` with the second map an isomorphism (`Scheme.Hom.appIso`).

`Γ(X, D)` is nontrivial because `D` is nonempty (`Scheme.component_nontrivial`), so
`eq_of_isStandardSmoothOfRelativeDimension_of_locally` above closes it.

**Density is used exactly once, and connectedness of `X` is NOT needed** — nor is any
openness-of-level-sets argument.  (The justification recorded on the consumer in `X0.lean`
routed through "`X` is connected because it contains a dense irreducible open"; that is a
strictly weaker argument.)

The general lesson, for the next audit written in this file: *an irreducibility verdict is
only as wide as the axis the auditor searched*, and "there is no lemma in
`Mathlib.AlgebraicGeometry`" is not the same claim as "there is no lemma in `Mathlib`".

`hsm : Smooth strX` is load-bearing and the statement is FALSE without it: a morphism can
restrict to something smooth of relative dimension `n` over a dense open and be arbitrarily
bad elsewhere.  `IsOpenImmersion j` is what makes `strY` the restriction of `strX` rather
than an unrelated morphism. -/
theorem smoothOfRelativeDimension_of_isDominant {S Y X : Scheme.{u}} {n : ℕ}
    {strY : Y ⟶ S} {strX : X ⟶ S} {j : Y ⟶ X} [IsOpenImmersion j] [IsDominant j]
    (hcomm : j ≫ strX = strY) (hsm : Smooth strX)
    (hY : SmoothOfRelativeDimension n strY) :
    SmoothOfRelativeDimension n strX := by
  subst hcomm
  haveI := hsm
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ := Smooth.exists_isStandardSmooth strX x
  -- the chart at `x` is standard smooth of *some* relative dimension `m`
  obtain ⟨m, hm⟩ : ∃ m, RingHom.IsStandardSmoothOfRelativeDimension m (strX.appLE U V e).hom := by
    letI := (strX.appLE U V e).hom.toAlgebra
    have h : Algebra.IsStandardSmooth Γ(S, U) Γ(X, V) := hss
    obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := h.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  refine ⟨U, hU, V, hV, hxV, e, ?_⟩
  -- it remains to see `m = n`; pick a nonempty basic open `D ≤ V` inside the range of `j`
  obtain ⟨z, hzV, hzj⟩ : ∃ z : X, z ∈ V ⊓ j.opensRange ∧ z ∈ V := by
    obtain ⟨z, hz⟩ := (Scheme.Hom.denseRange j).inter_open_nonempty (V : Set X) V.isOpen ⟨x, hxV⟩
    exact ⟨z, ⟨hz.1, hz.2⟩, hz.1⟩
  obtain ⟨a, haD, haz⟩ := hV.exists_basicOpen_le (V := V ⊓ j.opensRange) ⟨z, hzV⟩ hzj
  set D : X.Opens := X.basicOpen a with hDdef
  have hDV : D ≤ V := haD.trans inf_le_left
  have hDj : D ≤ j.opensRange := haD.trans inf_le_right
  have hD : IsAffineOpen D := hV.basicOpen a
  have e₁ : D ≤ strX ⁻¹ᵁ U := hDV.trans e
  -- `W := j ⁻¹ᵁ D` is an affine open of `Y` mapping isomorphically onto `D`
  set W : Y.Opens := j ⁻¹ᵁ D with hWdef
  have hW : IsAffineOpen W := hD.preimage_of_isOpenImmersion j hDj
  have hjW : j ''ᵁ W = D := by
    rw [hWdef, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hDj]
  have e₂ : W ≤ j ⁻¹ᵁ D := le_rfl
  have e₀ : W ≤ (j ≫ strX) ⁻¹ᵁ U := fun w hw => e₁ hw
  -- the relative dimension `n` of `strY`, read off on `(U, W)`
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      ((j ≫ strX).appLE U W e₀).hom :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) (j ≫ strX) hY ⟨U, hU⟩ ⟨W, hW⟩ e₀
  have hfac : strX.appLE U D e₁ ≫ j.appLE D W e₂ = (j ≫ strX).appLE U W e₀ :=
    Scheme.Hom.appLE_comp_appLE j strX U D W e₁ e₂
  have hiso : IsIso (j.appLE D W e₂) := by
    rw [Scheme.Hom.appLE_congr (f := j) e₂ hjW.symm rfl (fun g => IsIso g),
      ← Scheme.Hom.appIso_hom']
    infer_instance
  have hlocD : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (strX.appLE U D e₁).hom := by
    rw [← RingHom.RespectsIso.cancel_right_isIso
      (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
      (strX.appLE U D e₁) (j.appLE D W e₂)]
    rw [← CommRingCat.hom_comp, hfac]
    exact hloc
  -- the relative dimension `m` of `strX`, transported to the localisation `D`
  haveI : IsLocalization.Away a Γ(X, D) := hV.isLocalization_basicOpen a
  have hmD : RingHom.IsStandardSmoothOfRelativeDimension m (strX.appLE U D e₁).hom := by
    have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0
        (algebraMap Γ(X, V) Γ(X, D)) :=
      RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway a
    have h2 := h0.comp hm
    rw [zero_add] at h2
    have hcomp : (algebraMap Γ(X, V) Γ(X, D)).comp (strX.appLE U V e).hom
        = (strX.appLE U D e₁).hom := by
      have halg : algebraMap Γ(X, V) Γ(X, D)
          = (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom := rfl
      rw [halg, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    rwa [hcomp] at h2
  haveI : Nonempty D := ⟨⟨z, haz⟩⟩
  haveI : Nontrivial Γ(X, D) := Scheme.component_nontrivial X D
  exact (eq_of_isStandardSmoothOfRelativeDimension_of_locally hmD hlocD) ▸ hm

/-- **The complement of a dense open in a one-dimensional proper curve is finite** (PROVEN;
it takes the dimension bound as the hypothesis `hdim`, which a consumer discharges from
`topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` above).

The same three-line assembly as `finite_compl_range_toNormalization` above, but for an
ARBITRARY dominant open immersion `j : Y ⟶ X` rather than for `i.toNormalization`, and taking
the dimension bound as a hypothesis rather than producing it.  All four typeclass hypotheses
of `finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one` are discharged here:

* `NoetherianSpace X` from `IsLocallyNoetherian X` (finite type over the noetherian `K`) and
  `CompactSpace X` (quasi-compact over the compact `Spec K`);
* `QuasiSober X` and `T0Space X` are instances for every scheme;
* `IrreducibleSpace X` from `IsIntegral Y` and the density of `j`, via
  `irreducibleSpace_of_denseRange` above.

The complement is closed because `j` is an open immersion, and is not everything because
`IsIntegral Y` makes `Y` nonempty. -/
theorem finite_compl_range_of_topologicalKrullDim_le_one {Y X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType strX] [QuasiCompact strX]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j] [IsIntegral Y]
    (hdim : topologicalKrullDim X ≤ 1) :
    (Set.range j.base)ᶜ.Finite := by
  haveI : IsNoetherianRing (CommRingCat.of K) := inferInstanceAs (IsNoetherianRing K)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian strX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace strX
  haveI : IsNoetherian X := ⟨⟩
  haveI : IrreducibleSpace X :=
    irreducibleSpace_of_denseRange j.continuous (Scheme.Hom.denseRange j)
  refine finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one hdim
    (isClosed_compl_iff.mpr j.isOpenEmbedding.isOpen_range) ?_
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  intro h
  exact (h ▸ Set.mem_univ (j.base y) : j.base y ∈ (Set.range j.base)ᶜ) (Set.mem_range_self y)

/-! ### The converse direction: a finite complement is already dense

`finite_compl_range_of_topologicalKrullDim_le_one` above goes from DENSITY to a finite
complement.  The two statements are *not* interchangeable, and the other direction is what
`Fermat.IsX0Compactification` needs, because — unlike `IsSmoothCompactification` here — it
carries `finite_compl` as a field and does **not** carry `isDominant`.  So every consumer of
it that needs density has to derive it, and this subsection is that derivation.

The whole point-set content is one line: a range is dense exactly when the interior of its
complement is empty, so on a space with *no nonempty finite open subset* a finite complement
is automatically dense.  All the geometry sits in that parenthesis, and it is isolated as
the single leaf below. -/

-- **THE LEAF THIS SUBSECTION RESTS ON LIVES UPSTREAM**, as
-- `AlgebraicGeometry.infinite_of_smoothOfRelativeDimension_one` in
-- `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`, which this file
-- `public import`s.  It used to be stated HERE as well, by a second branch on the same
-- day, and the two collided at integration (`has already been declared`); the properness-
-- free form survived, because the consumer below applies it to an OPEN subscheme and an
-- open of a proper scheme is not proper.  The reasoning that made this file's copy worth
-- writing is preserved in that declaration's docstring; do not restate it here.
--
-- What that leaf says: a NONEMPTY scheme smooth of relative dimension one over a field has
-- infinitely many points.  `Nonempty X` is load-bearing — the empty scheme satisfies
-- `SmoothOfRelativeDimension 1` vacuously and is finite — and a `topologicalKrullDim`
-- statement would NOT do instead: `Spec` of a DVR has Krull dimension one and two points,
-- so a finite nonempty open of Krull dimension one is not by itself a contradiction.  The
-- route is `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` plus Jacobson-ness.

/-- **On a smooth curve over a field, an open immersion with finite complement is dense**
(PROVEN, over the single leaf above).

This is the exact converse of `finite_compl_range_of_topologicalKrullDim_le_one`, and it is
what `Fermat.isDominant_of_isX0Compactification` is.

**The proof, and what it does NOT need.**  `DenseRange j.base` says
`closure (Set.range j.base) = ⊤`, which by `interior_compl` is the same as
`interior ((Set.range j.base)ᶜ) = ∅`.  That interior is an OPEN subset of a FINITE set, so
if it were nonempty it would be a nonempty finite open subscheme `U ⊆ X`; and `U.ι ≫ strX`
is smooth of relative dimension `0 + 1 = 1`, because an open immersion is smooth of relative
dimension `0`.  The leaf then makes `U` infinite, contradicting its finiteness.

Note what is absent: **no irreducibility, no connectedness, and no nonemptiness of `Y`**.
The obvious route — "`X` is irreducible, and a nonempty open of an irreducible space is
dense" — would need `X` normal (smooth over a field) and connected, i.e. two further
missing implications, *and* a separate argument that `Y` is nonempty at all.  Passing
through the interior of the complement avoids all three: if `Y` is empty the complement is
everything, and then `X` itself is a nonempty finite open, which the same leaf refutes. -/
theorem isDominant_of_finite_compl_of_smoothOfRelativeDimension_one {X Y : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 strX]
    {j : Y ⟶ X} [IsOpenImmersion j] (hfin : (Set.range j.base)ᶜ.Finite) :
    IsDominant j := by
  have hint : interior ((Set.range j.base)ᶜ) = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    let U : X.Opens := ⟨interior ((Set.range j.base)ᶜ), isOpen_interior⟩
    have hUfin : (U : Set X).Finite := hfin.subset interior_subset
    haveI : Finite U.toScheme := hUfin.to_subtype
    haveI : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
    haveI : SmoothOfRelativeDimension 1 (U.ι ≫ strX) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ strX))
    haveI := infinite_of_smoothOfRelativeDimension_one (U.ι ≫ strX)
    exact not_finite U.toScheme
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, ← Set.compl_empty_iff, ← interior_compl, hint]

end AlgebraicGeometry

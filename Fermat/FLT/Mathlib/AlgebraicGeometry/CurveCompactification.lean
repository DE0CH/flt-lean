/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.Perfect

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
   (`exists_isOpenImmersion_isProper`, LEAF);
2. take `X := i.normalization`, the normalization of `P` in `Y`.  Then
   `j := i.toNormalization : Y ⟶ X` is an open immersion **by Zariski's Main Theorem**
   and dominant **by construction** — both free from `Mathlib`;
3. `i.fromNormalization : X ⟶ P` is integral, and it is *finite* because normalization is of
   finite type for schemes of finite type over a field
   (`locallyOfFiniteType_fromNormalization`, LEAF); finite ⟹ proper, so `X` is proper
   over `K`;
4. `X` is normal of dimension one over a perfect field, hence smooth
   (`smoothOfRelativeDimension_one_fromNormalization`, LEAF);
5. the complement of a dense open in an irreducible noetherian curve is finite — proven
   here from the one-dimensionality of `X` (`topologicalKrullDim_normalization_le_one`,
   LEAF).

Step 2, the assembly, and the whole of steps 3 and 5 apart from their two named inputs are
PROVEN here.

## The leaves, after the 2026-07-27 decomposition

The remaining leaves are:

| leaf | content |
| --- | --- |
| `exists_isOpenImmersion_isProper` | Nagata compactification (unchanged — a single citation, no cut available) |
| `locallyOfFiniteType_fromNormalization` | Nagata/Japanese rings: the normalization of a finite-type `K`-algebra is of finite type |
| `topologicalKrullDim_normalization_le_one` | dimension = transcendence degree, so the normalized model is a curve |
| `smoothOfRelativeDimension_one_fromNormalization` | normal + dimension one + perfect base ⟹ smooth (unchanged; the deepest) |

`isFinite_fromNormalization`, `finite_compl_range_toNormalization`, `universallyOpen_of_specField`,
`denseRange_of_isPullback`
and `geometricallyConnected_of_isSmoothCompactification` are now THEOREMS over those.  What was
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

/-- **Nagata's compactification theorem, for a quasi-compact separated finite-type scheme
over a field** (sorry leaf).

TRUE and classical: Nagata (1962), *Imbedding of an abstract variety in a complete
variety*; see also Conrad's *Deligne's notes on Nagata compactifications* and Stacks
project tag `0F41`.  Any separated finite-type morphism to a quasi-compact
quasi-separated base factors as an open immersion followed by a proper morphism.

Note what is NOT claimed: `P` is **not** asserted normal, smooth, or even reduced.  That
is the whole point of routing through the normalization afterwards — Nagata's `P` is an
arbitrary proper model, and steps 3–4 of the module docstring repair it.  Weakening the
conclusion this far is what makes the leaf a citation rather than a construction.

`QuasiCompact i` is part of the conclusion rather than derived: an open immersion need not
be quasi-compact in general, and every consumer here needs it (Zariski's Main Theorem
takes it as a hypothesis).  Nagata's construction does deliver it, since `Y` is
quasi-compact and `P` is noetherian.

IRREDUCIBLE at this pin: there is no compactification statement of any kind in
`Mathlib.AlgebraicGeometry`, and no projective closure to build one from — `Proj` exists
only as `ProjectiveSpectrum` of a graded ring, with no closure-of-a-quasi-projective-scheme
API. -/
theorem exists_isOpenImmersion_isProper {Y : Scheme.{u}}
    (strY : Y ⟶ Spec (CommRingCat.of K)) [QuasiCompact strY] [IsSeparated strY]
    [LocallyOfFiniteType strY] :
    ∃ (P : Scheme.{u}) (strP : P ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ P),
      IsOpenImmersion i ∧ QuasiCompact i ∧ IsProper strP ∧ i ≫ strP = strY :=
  sorry

/-- **The normalization of a scheme of finite type over a field is of finite type over it**
(sorry leaf — the Nagata/Japanese input, and all that is left of the old
`isFinite_fromNormalization`).

TRUE and classical: a domain of finite type over a field is a Nagata (universally Japanese)
ring, so its integral closure in a finite extension of its fraction field is a finite module,
in particular a finite-type algebra.  Stacks tag `032E` (Nagata ⟸ finite type over a field)
and `03GH` (finiteness of the relative normalization over a Nagata base).

**Why the leaf is stated as `LocallyOfFiniteType` rather than `IsFinite`** (2026-07-27): the
integrality half of `IsFinite` is FREE — `IsIntegralHom i.fromNormalization` is a `Mathlib`
instance for every relative normalization, and
`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` says the two together are exactly
`IsFinite`.  So the entire content of the old leaf is this one, and
`isFinite_fromNormalization` below is now a two-line consequence.  Anyone attacking it should
know that only finite-*type*-ness has to be produced; integrality is not in play.

The affine-local shape of what remains: for `U = Spec A` an affine open of `P`, the ring
`Γ(i.normalization, i.fromNormalization ⁻¹ᵁ U)` is by construction the integral closure of `A`
in `Γ(Y, i ⁻¹ᵁ U)` (`AlgebraicGeometry.Scheme.Hom.normalizationObjIso`), and the claim is that
this integral closure is a finite-type `A`-algebra.  `Mathlib` has no Nagata/Japanese-ring
theory at this pin, which is why this is a leaf. -/
theorem locallyOfFiniteType_fromNormalization {Y P : Scheme.{u}}
    (strP : P ⟶ Spec (CommRingCat.of K)) [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y] :
    LocallyOfFiniteType i.fromNormalization :=
  sorry

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

/-- **The normalization of a curve over a perfect field is a smooth curve** (sorry leaf).

TRUE and classical, in three steps: the relative normalization `X` of `P` in the integral
scheme `Y` is normal and integral, and has the same function field as `Y`, hence the same
dimension `1`; a noetherian normal local domain of dimension one is a discrete valuation
ring, so `X` is regular (Serre's criterion in dimension one, or just
`IsIntegrallyClosed` + noetherian + dimension one ⟹ `IsDedekindDomain`); and over a
**perfect** field regular is equivalent to smooth (Stacks `056S`), the relative dimension
being `1` because `X` is a curve.

`PerfectField K` is load-bearing and the statement is FALSE without it: over an imperfect
field `k` of characteristic `p` the curve `y^p = t x^p + t` (`t ∈ k ∖ k^p`) is regular but
not smooth, and it is its own normalization.  `ℚ` is perfect, so the modular application
is unaffected.

`hY` — that `Y` itself is a smooth curve — is what pins the dimension to `1`; without it
the same construction applies in every dimension and the relative dimension in the
conclusion is unconstrained.  Note that smoothness of `Y` is used ONLY through its
dimension: the normalization forgets everything else about `Y`, which is exactly why the
same leaf serves a merely *normal* `Y`.

IRREDUCIBLE at this pin, and it is the deepest of the four: `Mathlib` has no notion of a
normal scheme, no dimension theory for schemes beyond `coheight`, and no
regular-implies-smooth-over-a-perfect-field statement. -/
theorem smoothOfRelativeDimension_one_fromNormalization [PerfectField K] {Y P : Scheme.{u}}
    {strP : P ⟶ Spec (CommRingCat.of K)} [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y]
    (_hY : SmoothOfRelativeDimension 1 (i ≫ strP)) :
    SmoothOfRelativeDimension 1 (i.fromNormalization ≫ strP) :=
  sorry

/-- **The normalized proper model of a smooth curve is one-dimensional** (sorry leaf — the
dimension-theoretic input, and all that is left of the old
`finite_compl_range_toNormalization`).

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

IRREDUCIBLE at this pin: `Mathlib` has `topologicalKrullDim` and `Order.coheight`, and
`Scheme.functionField`, but no dimension-equals-transcendence-degree theorem and no link at
all between `SmoothOfRelativeDimension n` and any dimension of the source. -/
theorem topologicalKrullDim_normalization_le_one {Y P : Scheme.{u}}
    {strP : P ⟶ Spec (CommRingCat.of K)} [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y]
    (_hY : SmoothOfRelativeDimension 1 (i ≫ strP)) :
    topologicalKrullDim i.normalization ≤ 1 :=
  sorry

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

end AlgebraicGeometry

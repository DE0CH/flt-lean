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
   `finiteType_integralClosure_sections`, LEAF); finite ⟹ proper, so `X` is proper over `K`;
4. `X` is normal of dimension one over a perfect field, hence smooth
   (`smoothOfRelativeDimension_one_fromNormalization`, LEAF);
5. the complement of a dense open in an irreducible noetherian curve is finite — proven
   here from the one-dimensionality of `X` (`topologicalKrullDim_normalization_le_one`,
   PROVEN over `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` and
   `topologicalKrullDim_le_of_isOpenImmersion_of_irreducible`, LEAVES).

Step 2, the assembly, and the whole of steps 3 and 5 apart from their two named inputs are
PROVEN here.

## The leaves, after the 2026-07-27 decompositions

Every one of the original five leaves has now been cut down; the remaining leaves are:

| leaf | content |
| --- | --- |
| `nonempty_projChart_mvPolynomial` | dehomogenisation: the standard affine chart of `ℙⁿ` |
| `nonempty_projChart_of_surjective` | the projective closure of an affine variety |
| `exists_isOpenImmersion_isProper_of_affineCase` | Nagata's gluing induction (all that is left of Nagata) |
| `locallyOfFiniteType_fromNormalization` | Nagata/Japanese rings: the normalization of a finite-type `K`-algebra is of finite type |
| `topologicalKrullDim_normalization_le_one` | dimension = transcendence degree, so the normalized model is a curve |
| `exists_isOpenImmersion_isProper` | Nagata compactification (unchanged — a single citation, no cut available) |
| `finiteType_integralClosure_sections` | Nagata/Japanese rings: the integral closure of a finite-type `K`-algebra in the sections of `Y` over an affine chart is of finite type |
| `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` | a smooth curve over a field is one-dimensional |
| `topologicalKrullDim_le_of_isOpenImmersion_of_irreducible` | a nonempty open of an irreducible finite-type `K`-scheme carries the full dimension |
| `smoothOfRelativeDimension_one_fromNormalization` | normal + dimension one + perfect base ⟹ smooth (unchanged; the deepest) |
| `infinite_of_smoothOfRelativeDimension_one` | a nonempty smooth curve over a field has infinitely many points (added 2026-07-27; the only input to the density subsection at the end of this file) |

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

* `nonempty_projChart_mvPolynomial` (LEAF) — the standard affine chart of `ℙⁿ`:
  dehomogenisation at `X₀`;
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
other; the second file's docstring carries a full proof plan for the dehomogenisation
isomorphism (surjectivity from `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`, the
kernel by a UFD divisibility argument). -/

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

/-- **The standard affine chart of `ℙⁿ`** (sorry leaf — dehomogenisation).

TRUE and elementary: take `A := K[X₀, …, Xₙ]` with its grading by total degree
(`MvPolynomial.homogeneousSubmodule`) and `f := X₀`.  Then `𝒜₀ = K` (so `Module.Finite K 𝒜₀`
is immediate), `A` is generated over `𝒜₀` by `n + 1` elements, and the degree-zero part of
`A[X₀⁻¹]` is `K[X₁/X₀, …, Xₙ/X₀] ≅ K[Y₁, …, Yₙ]` — dehomogenisation, `Xᵢ ↦ Yᵢ`, `X₀ ↦ 1`.
Stacks tag `01M3`.

**Why it is not free at this pin**: a grep for `dehomogeni` over the whole of `Mathlib`
returns NOTHING.  `HomogeneousLocalization.Away` and `Proj.awayι` exist, but no
identification of an away-localisation's degree-zero part with a concrete polynomial ring.
The same gap is recorded independently at `Fermat.exists_projChartRingEquiv`
(`Fermat/FLT/ModularCurve/EllipticScheme.lean`), whose docstring carries a full proof plan —
surjectivity from `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`, injectivity by a
UFD divisibility argument.  Here the ideal is zero, so only the surjectivity half plus the
triviality of the kernel is needed, which makes this the EASIER of the two; a proof here
should be lifted to that one, and vice versa.

This is `Mathlib`-ready material: stated for an arbitrary base commutative ring it is the
standard affine cover of projective space. -/
theorem nonempty_projChart_mvPolynomial (n : ℕ) :
    Nonempty (ProjChart K (CommRingCat.of (MvPolynomial (Fin n) K))
      (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))) :=
  sorry

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
built from. -/
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

/-- **The integral closure of an affine chart of `P` in the sections of `Y` over its preimage is
a finite-type algebra** (sorry leaf — the Nagata/Japanese input, and, after the 2026-07-27 cut
below, all that is left of the old `isFinite_fromNormalization`).

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

**THE FURTHER CUT THIS ADMITS, and everything a next owner needs to know.**  Only one classical
theorem is genuinely missing from the pin; the rest is available and is named here.

* `B` is a DOMAIN whenever `i ⁻¹ᵁ U` is nonempty: `IsIntegral Y` gives
  `IsIntegral.component_integral`, i.e. `IsDomain Γ(Y, V)` for every nonempty open `V`.  When
  `i ⁻¹ᵁ U` is EMPTY, `B` is the trivial ring — `instance {X : Scheme.{u}} : Subsingleton Γ(X, ⊥)`
  in `Mathlib/AlgebraicGeometry/Scheme.lean` — the integral closure is everything, and the
  algebra map is surjective, so the statement is immediate; that case must be split off first.
* `B` embeds in the FUNCTION FIELD `L := Y.functionField`, injectively, by
  `Scheme.germToFunctionField_injective` (`Mathlib/AlgebraicGeometry/FunctionField.lean`).
* `L` is the fraction field of the image `A'` of `A` in `B`: `i` is an open immersion, so
  `i ⁻¹ᵁ U` is an open subscheme of the affine `U`, dense in `Spec A'` because `Y` is
  irreducible, and the stalk of `Spec A` at the generic point is `A'`-localized to a field,
  which is `L`.  `functionField_isFractionRing_of_isAffineOpen` is the affine form of this.
* `A` is of FINITE TYPE over `K`, hence NOETHERIAN: `IsProper strP` gives
  `LocallyOfFiniteType strP`, and `HasRingHomProperty.appLE` reads that off at `U`.
* Hence `integralClosure A B` injects, as an `A`-module, into `integralClosure A L` — the map is
  `AlgHom.mapIntegralClosure`, which is already in the pin — and it is enough to know that the
  latter is a FINITE `A`-module, since a submodule of a finite module over a Noetherian ring is
  finite.
* The final conversion is `RingHom.finiteType_algebraMap`
  (`Mathlib/RingTheory/FiniteType.lean`): `(algebraMap A C).FiniteType ↔ Algebra.FiniteType A C`,
  and `Module.Finite A C → Algebra.FiniteType A C`.

So the one missing classical input, and the only thing a next owner has to import or prove, is

    A a finite-type algebra over a field, L a field which is the fraction field of the image
    of A  ⟹  `Module.Finite A (integralClosure A L)`

(Noether's finiteness of the integral closure; Stacks `0335`, `032E`).  `Mathlib` has it only
in the SEPARABLE case, as `IsIntegralClosure.finite`
(`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`, which needs `[IsIntegrallyClosed A]`,
`[IsNoetherianRing A]` and separability of the residue extension); the general case needs
Noether normalization — which IS at the pin, `Mathlib/RingTheory/NoetherNormalization.lean`,
`exists_finite_inj_algHom_of_fg` — plus the inseparable descent.  That is the genuine gap. -/
theorem finiteType_integralClosure_sections {Y P : Scheme.{u}}
    (strP : P ⟶ Spec (CommRingCat.of K)) [IsProper strP]
    (i : Y ⟶ P) [IsOpenImmersion i] [QuasiCompact i] [IsIntegral Y] (U : P.affineOpens) :
    letI := (i.app U.1).hom.toAlgebra
    RingHom.FiniteType
      (algebraMap Γ(P, U.1) (integralClosure Γ(P, U.1) Γ(Y, i ⁻¹ᵁ U.1))) :=
  sorry

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

/-- **A smooth curve over a field is one-dimensional** (sorry leaf — the dimension half of the
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

**WHAT THE PIN DOES AND DOES NOT HAVE** (checked 2026-07-27; re-run these greps before
believing them).  `Mathlib` relates `SmoothOfRelativeDimension n` to nothing
dimension-theoretic: `grep -rn "SmoothOfRelativeDimension" Mathlib/` returns only
`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` (the definition, `smooth`, base change,
composition and the open-immersion instance), and there is no smooth-implies-regular result at
all (`grep -rn "IsRegularLocalRing" Mathlib/RingTheory/Smooth/ Mathlib/AlgebraicGeometry/` is
empty).  That is the gap.

But three pieces that a proof needs ARE present, and a next owner should not go looking for
them:

* `MvPolynomial.ringKrullDim_of_isNoetherianRing`
  (`Mathlib/RingTheory/KrullDimension/Polynomial.lean`):
  `ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι`, so `dim K[x₁, …, x_m] = m`.
* `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
  (`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`): the module of differentials of a
  standard smooth algebra of relative dimension `n` is free of rank `n`.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` and
  `Order.krullDim_eq_iSup_coheight`, which reduce `topologicalKrullDim Y ≤ 1` to a bound on
  every stalk (`Modularity/KhareWintenberger.lean` packages exactly that reduction as its
  PROVEN `krullDimLE_stalk_of_topologicalKrullDim_le` and
  `topologicalKrullDim_eq_iSup_coheight`).

So the missing step is specifically: for `S = K[x₁, …, x_m]/(f₁, …, f_{m-1})` with invertible
Jacobian, `ringKrullDim S ≤ 1`.  The lower bound is Krull's height theorem; the upper bound is
the one that needs the dimension theorem for finite-type `K`-algebras.

RELATION TO `Modularity/KhareWintenberger.lean`: that file does NOT own this statement; it
takes `hdim : topologicalKrullDim ↥C ≤ 1` as a HYPOTHESIS on every declaration in the cluster
and pushes the obligation out to `X0.lean`.  So this leaf is genuinely unowned there, and
whoever proves it here discharges that hypothesis for both files.

PIN AUDIT INHERITED FROM A DUPLICATE OF THIS LEAF (dropped at integration 2026-07-27).
A second, less general statement of this same lemma — carrying the extra hypotheses
`[LocallyOfFiniteType strX] [QuasiCompact strX]`, which a Krull-dimension bound does not
need — was written independently on another branch and is deleted here; its route audit is
kept because it is about this statement and is complementary to the survey above.

IRREDUCIBLE at this pin, and here is the state of the ingredients — this is the check to
re-run before accepting the verdict, because two of the three pieces DO exist:

* **present**: `MvPolynomial.ringKrullDim_of_isNoetherianRing`
  (`Mathlib/RingTheory/KrullDimension/Polynomial.lean:119`) gives
  `ringKrullDim K[x₁ … xₛ] = s` — note this makes the `proof_wanted`
  `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing` at
  `Mathlib/RingTheory/KrullDimension/Basic.lean:94` **stale**, so do not conclude from that
  `proof_wanted` that the polynomial dimension is unavailable;
* **present**: Noether normalization,
  `NoetherNormalization.exists_finite_inj_algHom_of_fg`
  (`Mathlib/RingTheory/NoetherNormalization.lean:289`) — every f.g. `K`-algebra is finite over
  some `K[x₁ … xₛ]`;
* **present**: `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` and
  `topologicalKrullDim_subspace_le`, which is how an affine-open-local bound is assembled into
  a bound on `X` (`IsLocallyArtinian.of_topologicalKrullDim_le_zero` in
  `Mathlib/AlgebraicGeometry/Artinian.lean` is the worked precedent for exactly this pattern
  one dimension down);
* **MISSING (1)**: invariance of `ringKrullDim` under an *injective integral* ring extension
  (lying over + going up + incomparability).  A grep for `ringKrullDim` across
  `Mathlib/RingTheory/` turns up transport along `RingEquiv` and the surjective bound
  `ringKrullDim_le_of_surjective`, and nothing for integral extensions;
* **MISSING (2)**: the link from `IsStandardSmoothOfRelativeDimension 1` to `s = 1` in the
  Noether normalization — i.e. relative dimension equals transcendence degree.  There is **no
  occurrence of `ringKrullDim` or `krullDim` anywhere under `Mathlib/RingTheory/Smooth/`,
  `Mathlib/RingTheory/Extension/` or in `Mathlib/RingTheory/Presentation.lean`**, so nothing
  at this pin connects a smooth presentation to any dimension.

So the leaf is two named ring-theoretic statements away, not a whole dimension theory. Either
of the two MISSING items being found in the pin refutes this verdict. -/
theorem topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one {Y : Scheme.{u}}
    (strY : Y ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 strY] :
    topologicalKrullDim Y ≤ 1 :=
  sorry

/-- **A nonempty open subscheme of an irreducible scheme of finite type over a field has the
full dimension of the ambient scheme** (sorry leaf — the transfer half of the old
`topologicalKrullDim_normalization_le_one`).

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

**THIS IS THE GENERAL-`K` FORM OF A LEMMA THAT IS ALREADY PROVEN OVER `ULift ℚ`**, in
`Modularity/KhareWintenberger.lean`, as
`topologicalKrullDim_le_of_isOpenImmersion_of_locallyOfFiniteType`, itself over the single leaf
`exists_coheight_le_of_isOpenImmersion_of_locallyOfFiniteType` there.  That proof runs
`topologicalKrullDim_eq_iSup_coheight` (sobriety plus `Order.krullDim_eq_iSup_coheight`) to
turn the comparison into a POINTWISE one, uses `coheight_eq_of_isOpenImmersion` to move
coheights across the open immersion, and produces the dominating point of `C` from Noether
normalization plus going-up on an affine chart.  Two things must be checked before that proof
is transported here: it picks a rational point out of an infinite field (`ℚ` being infinite is
what supplies it), so a general `K` — in particular a FINITE one — needs the standard
replacement (pass to an infinite extension, or use a general position argument); and this
module is UPSTREAM of `KhareWintenberger.lean`, so the transport is a hoist into this file
rather than a citation.  Whoever proves it here should re-derive that file's copy from this
one, per the module docstring's standing instruction not to prove the same theorem twice. -/
theorem topologicalKrullDim_le_of_isOpenImmersion_of_irreducible {C X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType strX] [IrreducibleSpace X]
    (j : C ⟶ X) [IsOpenImmersion j] [Nonempty C] :
    topologicalKrullDim X ≤ topologicalKrullDim C :=
  sorry

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

So this subsection now adds ONE leaf, `smoothOfRelativeDimension_of_isDominant`; the dimension
bound it also needs is the one already stated above. -/

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

/-- **The relative dimension of a smooth morphism propagates from a dense open** (sorry leaf
— local constancy of the relative dimension, and the whole content of the first half of
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

IRREDUCIBLE at this pin, and here is the check that would refute it.  `Mathlib`'s
`SmoothOfRelativeDimension n f` (`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:135`) is a
*pointwise* condition — for every `x` there exist affine opens on which `f.appLE` is
`IsStandardSmoothOfRelativeDimension n` — and the entire API around it consists of
`.smooth`, the `HasRingHomProperty` instance, stability under base change, the instance
`SmoothOfRelativeDimension 0` for open immersions, and additivity under composition.
**Not one lemma in `Mathlib` relates the property at two different values of `n`, and there
is no `relativeDimension`/fibre-dimension function anywhere in
`Mathlib.AlgebraicGeometry`** (`Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean` is
about smoothness of fibres, not their dimension).  Producing the local constancy — most
cheaply as "the set of `x` at which `SmoothOfRelativeDimension n` holds locally is open" —
closes this leaf, and refutes the irreducibility verdict.

The axis searched is the RELATIVE-dimension one.  A route through absolute dimension (`X` is
one-dimensional, the base is a point, hence the relative dimension is one) is a *different*
axis and was not searched; it would need the same missing dimension theory as
`topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` below **plus** a converse
linking dimension back to the standard-smooth presentation, so it looks strictly harder, but
it has not been ruled out.

`_hsm : Smooth strX` is load-bearing and the statement is FALSE without it: a morphism can
restrict to something smooth of relative dimension `n` over a dense open and be arbitrarily
bad elsewhere.  `IsOpenImmersion j` is what makes `strY` the restriction of `strX` rather
than an unrelated morphism. -/
theorem smoothOfRelativeDimension_of_isDominant {S Y X : Scheme.{u}} {n : ℕ}
    {strY : Y ⟶ S} {strX : X ⟶ S} {j : Y ⟶ X} [IsOpenImmersion j] [IsDominant j]
    (_hcomm : j ≫ strX = strY) (_hsm : Smooth strX)
    (_hY : SmoothOfRelativeDimension n strY) :
    SmoothOfRelativeDimension n strX :=
  sorry

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

/-- **A nonempty smooth curve over a field has infinitely many points** (sorry leaf — the
one-dimensionality of a smooth curve, in its point-counting form).

TRUE and classical.  On an affine chart `Spec A` the algebra `A` is standard smooth of
relative dimension `1` over `K` (`Smooth.exists_isStandardSmooth`, and `A` is of finite type
over `K`), so `dim A = 1`; a finite-type `K`-algebra is Jacobson, and a Jacobson ring of
dimension one has infinitely many maximal ideals — a chain `p ⊊ m` forces the Jacobson
radical (an intersection of *finitely many* maximals, were there only finitely many) to
differ from the nilradical, which is contained in the minimal prime `p`.

**`Nonempty X` is load-bearing**, not decoration: the empty scheme satisfies
`SmoothOfRelativeDimension 1` vacuously and is finite.

**Why this and not a `topologicalKrullDim` statement.**  The sibling leaf
`topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one` above bounds the dimension
from ABOVE, and its companion lower bound `1 ≤ topologicalKrullDim X` would **not** suffice
for the consumer below: `Spec` of a discrete valuation ring has Krull dimension one and just
two points, so a finite nonempty open of Krull dimension one is not by itself a
contradiction.  Finiteness of the point set is the property that actually has to fail, so it
is the property that is stated.  (What rules the DVR out here is `LocallyOfFiniteType`, which
is why the argument above goes through Jacobson-ness rather than through dimension alone.)

**Where the missing input lives.**  This is the same class of fact as
`AlgebraicGeometry.geometricallyReduced_of_smooth` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean` — a property of smooth
morphisms over a field that `Mathlib` does not derive from smoothness at this pin — and, as
there, the route is through the local structure theorem
`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`
(`Mathlib/RingTheory/Smooth/StandardSmoothOfFree.lean`), which IS present and should not be
re-derived. -/
theorem infinite_of_smoothOfRelativeDimension_one {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] [Nonempty X] :
    Infinite X :=
  sorry

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

/-
Material for `Mathlib.RingTheory.DedekindDomain.AdicValuation`; own work for the
Fermat project (not vendored from the FLT project).
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# The valuation ring of an adic completion is Henselian

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one
prime of `R`.  Mathlib knows that `v.adicCompletionIntegers K` is a discrete
valuation ring (`Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`)
and that an adically complete ring is Henselian
(`IsAdicComplete.henselianRing`, `Mathlib/RingTheory/Henselian.lean`), but it
does **not** carry the bridge between the two: there is no

    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K)

instance anywhere in the pin, in `~/cs/FLT`, or in this tree (re-checked by
`grep` on 2026-07-28: mathlib's supply is `ℤ_[p]`, Artinian local rings,
`AdicCompletion (maximalIdeal R) R`, `PowerSeries`, Witt vectors, and `𝒪[K]`
for `[IsNonarchimedeanLocalField K]` — and `v.adicCompletion K` carries no
`IsNonarchimedeanLocalField` instance, that class occurring only inside
`Mathlib/NumberTheory/LocalField/`).  This file supplies it, deduces
`HenselianLocalRing`, and records the two arithmetic bridges that let one apply
Hensel's lemma to images of elements of `R`.

## Main declarations

* `isAdicComplete_adicCompletionIntegers` — the sorry leaf.
* `henselianLocalRing_adicCompletionIntegers` — the instance consumers want.
* `algebraMap_mem_maximalIdeal_adicCompletionIntegers`,
  `isUnit_algebraMap_adicCompletionIntegers` — `r ∈ v` and `r ∉ v` transported
  to `v.adicCompletionIntegers K`; these are what turn a congruence modulo `v`
  in `R` into the two hypotheses of Hensel's lemma.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- **THE VALUATION RING OF AN ADIC COMPLETION IS ADICALLY COMPLETE** (sorry
leaf; CUT 2026-07-28 out of the two local leaves of STEP 1a-i′ in
`Modularity/KhareWintenberger.lean`, both of which need Hensel's lemma in
`w.adicCompletionIntegers F` and are PROVEN from this one statement).

`v.adicCompletionIntegers K` is the valuation ring of the complete discretely
valued field `v.adicCompletion K`, so it is a *complete* discrete valuation
ring, and its `𝔪`-adic filtration is its valuation filtration.  Both halves of
`IsAdicComplete` are therefore standard:

* `IsHausdorff` is already an instance for **any** Noetherian local ring
  (`Mathlib/RingTheory/AdicCompletion/Noetherian.lean`:
  `instance [IsLocalRing R] : IsHausdorff (maximalIdeal R) M`, via Krull
  intersection), and `v.adicCompletionIntegers K` is a discrete valuation ring,
  hence Noetherian and local.  So only precompleteness is at issue.

* `IsPrecomplete` is `IsAdic.isPrecomplete_iff`
  (`Mathlib/RingTheory/AdicCompletion/Topology.lean`) applied to the subspace
  topology, whose two inputs are:
  - `CompleteSpace (v.adicCompletionIntegers K)` — the valuation subring is a
    CLOSED subset (`Valued.isClosed_valuationSubring`) of the complete field
    `v.adicCompletion K` (a `UniformSpace.Completion`);
  - `IsAdic (maximalIdeal (v.adicCompletionIntegers K))` — via `isAdic_iff`,
    i.e. each `𝔪ⁿ` is open, and the `𝔪ⁿ` are cofinal in the neighbourhood
    filter of `0`.  Here
    `Valuation.Integers.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow`
    (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`, applied to
    `Valuation.valuationSubring.integers Valued.v`) turns `𝔪ⁿ` into the closed
    ball `{y | v y ≤ v ϖ ^ n}` for a uniformizer `ϖ`, whose openness is
    `Valued.isOpen_closedBall` and whose cofinality against
    `Valued.hasBasis_nhds_zero` is the (multiplicative) archimedean property of
    `ℤᵐ⁰`.

ROUTE NOT TAKEN, and why — recorded so a successor does not re-survey it.
Mathlib proves the analogous `IsAdicComplete 𝓂[K] 𝒪[K]` for
`[IsNonarchimedeanLocalField K]` (`Mathlib/NumberTheory/LocalField/Basic.lean`)
by a COMPACTNESS argument, because the closedness of `𝔪ⁿ` it uses is
`IsNoetherianRing.isClosed_ideal`, which needs `[CompactSpace R]`.  That proof
transfers here only after `CompactSpace (v.adicCompletionIntegers K)`, which in
turn needs the residue field to be FINITE — genuinely extra content (it is
`Valued.WithZeroMulInt.integer_compactSpace` together with
`HeightOneSpectrum.ResidueFieldEquivCompletionResidueField` in `~/cs/FLT`,
neither of which is in our pin) and genuinely unnecessary: a complete discrete
valuation ring is adically complete whatever its residue field.  So the route
above deliberately avoids compactness, and a successor should not vendor the
`~/cs/FLT` compactness chain for this.

FAITHFULNESS.  No finiteness and no number-field hypothesis appears — the
statement is about an arbitrary Dedekind domain and an arbitrary height-one
prime, which is the generality in which it is true.  It is not vacuous:
`HeightOneSpectrum` carries `asIdeal ≠ ⊥` and `asIdeal.IsPrime`, so the
valuation is genuinely nontrivial, `v.adicCompletionIntegers K` is not a field,
and `maximalIdeal ≠ ⊥` — the statement is not the trivial
`IsAdicComplete ⊥` instance in disguise. -/
theorem isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  sorry

/-- The valuation ring of an adic completion is a Henselian local ring.

This is `isAdicComplete_adicCompletionIntegers` followed by mathlib's
`IsAdicComplete.henselianRing`; the only step is strengthening the hypothesis
`IsUnit (f.derivative.eval a₀)` of `HenselianLocalRing` to the weaker
`IsUnit (Ideal.Quotient.mk _ (f.derivative.eval a₀))` that `HenselianRing`
asks for, which is `IsUnit.map`. -/
instance henselianLocalRing_adicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) := by
  haveI := isAdicComplete_adicCompletionIntegers v (K := K)
  haveI : HenselianRing (v.adicCompletionIntegers K)
      (maximalIdeal (v.adicCompletionIntegers K)) := inferInstance
  exact ⟨fun f hf a₀ h₁ h₂ => HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)⟩

/-- An element of `R` lying in `v` maps into the maximal ideal of
`v.adicCompletionIntegers K`. -/
theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers {r : R} (hr : r ∈ v.asIdeal) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
      maximalIdeal (v.adicCompletionIntegers K) := by
  have h : Valued.v (algebraMap R (v.adicCompletion K) r) < 1 := by
    rw [valuedAdicCompletion_eq_valuation]
    exact (v.valuation_lt_one_iff_mem (K := K) r).2 hr
  exact (Valuation.mem_maximalIdeal_iff _ _).2 h

/-- An element of `R` **not** lying in `v` maps to a unit of
`v.adicCompletionIntegers K`. -/
theorem isUnit_algebraMap_adicCompletionIntegers {r : R} (hr : r ∉ v.asIdeal) :
    IsUnit (algebraMap R (v.adicCompletionIntegers K) r) := by
  have h : ¬ Valued.v (algebraMap R (v.adicCompletion K) r) < 1 := by
    rw [valuedAdicCompletion_eq_valuation, not_lt]
    exact ((v.valuation_eq_one_iff_notMem (K := K)).2 hr).ge
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => h ((Valuation.mem_maximalIdeal_iff _ _).1 hmem)

/-- The coercion into `v.adicCompletion K` of the image in
`v.adicCompletionIntegers K` of a global integer. -/
theorem coe_algebraMap_adicCompletionIntegers (r : R) :
    ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap K (v.adicCompletion K) (algebraMap R K r) := rfl

end IsDedekindDomain.HeightOneSpectrum

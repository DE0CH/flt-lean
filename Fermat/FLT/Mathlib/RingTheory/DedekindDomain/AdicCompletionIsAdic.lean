/-
DedekindDomain/AdicCompletionIsAdic.lean — own work for the Fermat project.

# The valuation ring of an adic completion is `𝔪`-adically complete

Material destined for Mathlib. This module fills the ONE pin gap that blocks
the local leaves of STEP 1a-i′ of `Modularity/KhareWintenberger.lean`:
nothing in the pin connects the **uniform** completeness of
`v.adicCompletion K` to the **`𝔪`-adic** completeness of its integers
`v.adicCompletionIntegers K`.

Everything here is stated for a Dedekind domain `R` with fraction field `K`
and a height-one prime `v`; no number field is needed.

## Contents

* `IsDedekindDomain.HeightOneSpectrum.instIsUniformAddGroupAdicCompletionIntegers`
  and `…instIsTopologicalRingAdicCompletionIntegers` — two instances that the
  pin does NOT synthesise on `↥(v.adicCompletionIntegers K)` (verified
  2026-07-28 by `inferInstance` probes: both give `synthInstanceFailed`),
  although `IsLocalRing`, `IsDiscreteValuationRing`, `IsPrincipalIdealRing`,
  `IsNoetherianRing`, `UniformSpace`, `T2Space` and `IsHausdorff` all do.
  They are recovered from the underlying `AddSubgroup` / `Subring`.
* `isAdic_maximalIdeal_adicCompletionIntegers` — the subspace topology on the
  integers IS the `𝔪`-adic topology. This is the whole content: with `ϖ` a
  uniformizer, `𝔪 ^ n = {y : v ↑y ≤ (v ↑ϖ) ^ n}` is a closed ball, closed
  balls are OPEN in a valued ring (the value group is discretely ordered
  around each point), and `(v ↑ϖ) ^ n → 0` because `ℤᵐ⁰` is
  `MulArchimedean`, so those balls are cofinal in the neighbourhood filter
  of `0`.
* `isAdicComplete_maximalIdeal_adicCompletionIntegers` — the target:
  `IsAdicComplete (maximalIdeal O) O`. Immediate from the previous item via
  `IsAdic.isAdicComplete_iff`, `CompleteSpace O` (the integers are a CLOSED
  subset of the complete `v.adicCompletion K`) and `T2Space O` (a subspace of
  a T2 space).
* `henselianLocalRing_adicCompletionIntegers` — the Henselian corollary, via
  `IsAdicComplete.henselianRing` plus the upgrade `HenselianRing O 𝔪 →
  HenselianLocalRing O`, which mathlib has ONLY in the converse direction
  (`instance [HenselianLocalRing R] : HenselianRing R (maximalIdeal R)`).
  The upgrade is one line: the two `is_henselian` fields differ only in
  asking `IsUnit (f.derivative.eval a₀)` in `O` versus in `O ⧸ 𝔪`, and
  `IsUnit.map` crosses that gap.

## COORDINATION NOTE (2026-07-28, `flt-lean-350`)

`flt-lean-243` is concurrently writing
`Fermat/FLT/Mathlib/RingTheory/DedekindDomain/AdicCompletionHenselian.lean`
carrying the same relocation, over a sub-leaf it names
`isAdicComplete_adicCompletionIntegers` and leaves SORRIED. This module is
that sub-leaf, PROVEN. Every declaration here is deliberately given a name
DIFFERENT from theirs so that the two modules can coexist in one import cone
without a duplicate-declaration error; the intended reconciliation is to
discharge their sorry with

  `:= isAdicComplete_maximalIdeal_adicCompletionIntegers K v`

and then keep whichever copy of the Henselian corollary the merger prefers.

This module is deliberately NOT yet imported by any consumer, precisely to
keep it out of `KhareWintenberger.lean` while `flt-lean-243` is editing that
file. It compiles standalone (`lake build
Fermat.FLT.Mathlib.RingTheory.DedekindDomain.AdicCompletionIsAdic`, green,
2026-07-28). Wiring it in is ONE `public import` line in whichever module
consumes it.
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The integers of an adic completion form a uniform additive group. NOT in the pin: the
`UniformSpace` instance on `↥(v.adicCompletionIntegers K)` is there, but nothing derives
`IsUniformAddGroup` from it; it comes from the underlying `AddSubgroup`. -/
instance instIsUniformAddGroupAdicCompletionIntegers :
    IsUniformAddGroup (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsUniformAddGroup (v.adicCompletionIntegers K).toSubring.toAddSubgroup)

/-- The integers of an adic completion form a topological ring. NOT in the pin either; it comes
from the underlying `Subring`. -/
instance instIsTopologicalRingAdicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing (v.adicCompletionIntegers K).toSubring)

/-- **The subspace topology on `v.adicCompletionIntegers K` is the `𝔪`-adic topology.**

Both clauses of `isAdic_iff` come from the single identification
`𝔪 ^ n = {y : v ↑y ≤ v ↑(ϖ ^ n)}` with `ϖ` a uniformizer of the (discrete!) valuation ring
`O := v.adicCompletionIntegers K`:

* the right-hand side is a CLOSED BALL of the valuation, and closed balls of a valued ring are
  open (`Valued.isOpen_closedBall`), pulled back along the continuous inclusion `O → K_v`;
* conversely a basic neighbourhood `{x : v x < γ}` of `0` contains such a ball, because
  `v ↑ϖ < 1` and `ℤᵐ⁰` is `MulArchimedean`, so `(v ↑ϖ) ^ n < γ` for `n` large
  (`exists_pow_lt₀`). -/
theorem isAdic_maximalIdeal_adicCompletionIntegers :
    IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hint := HeightOneSpectrum.adicCompletionIntegers.integers K v
  have hpow : ∀ n : ℕ,
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
          Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K))
        = {y : v.adicCompletionIntegers K |
            Valued.v (y : v.adicCompletion K) ≤ Valued.v ((ϖ ^ n : _) : v.adicCompletion K)} := by
    intro n
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow,
      Valuation.Integers.coe_span_singleton_eq_setOf_le_v_algebraMap hint]
    rfl
  have hϖ0 : ∀ n : ℕ, Valued.v ((ϖ ^ n : _) : v.adicCompletion K) ≠ 0 := by
    intro n
    simpa using (hint.valuation_pos_iff_ne_zero (x := ϖ ^ n)).mpr (pow_ne_zero n hϖ.ne_zero) |>.ne'
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [hpow n, show {y : v.adicCompletionIntegers K |
        Valued.v (y : v.adicCompletion K) ≤ Valued.v ((ϖ ^ n : _) : v.adicCompletion K)}
        = (Subtype.val ⁻¹' {x : v.adicCompletion K |
            (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict x ≤
              (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
                ((ϖ ^ n : _) : v.adicCompletion K)}) from by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.restrict_le_iff]]
    exact (Valued.isOpen_closedBall _ (by simpa using hϖ0 n)).preimage continuous_subtype_val
  · rw [mem_nhds_subtype] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [ZeroMemClass.coe_zero] at ht
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
    obtain ⟨n, hn⟩ := exists_pow_lt₀ (hint.valuation_irreducible_lt_one hϖ)
      (Units.mk0 (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
        (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ))
    refine ⟨n, fun y hy => ?_⟩
    refine hts (hγ ?_)
    show (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
      (y : v.adicCompletion K) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    calc Valued.v (y : v.adicCompletion K)
        ≤ Valued.v ((ϖ ^ n : _) : v.adicCompletion K) := by
          rw [hpow n] at hy; exact hy
      _ = Valued.v ((ϖ : _) : v.adicCompletion K) ^ n := by push_cast; simp
      _ < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hn

/-- **The valuation ring of an adic completion is `𝔪`-adically complete.**

`IsAdic.isAdicComplete_iff` reduces this to `CompleteSpace` and `T2Space` for the subspace
topology, which is the `𝔪`-adic one by `isAdic_maximalIdeal_adicCompletionIntegers`. The
integers are a closed subset of the complete field `v.adicCompletion K`
(`Valued.isClosed_valuationSubring`), hence complete; and a subspace of a T2 space is T2. -/
theorem isAdicComplete_maximalIdeal_adicCompletionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  (IsAdic.isAdicComplete_iff (isAdic_maximalIdeal_adicCompletionIntegers K v)).mpr
    ⟨(Valued.isClosed_valuationSubring (v.adicCompletion K)).completeSpace_coe, inferInstance⟩

/-!
### The Henselian corollary is deliberately NOT stated here

`henselianLocalRing_adicCompletionIntegers` is `flt-lean-243`'s declaration and is not
duplicated in this module (see the COORDINATION NOTE at the top). For the record, it is two
lines on top of the theorem above, and was verified green in this worktree's scratch module on
2026-07-28 before being removed:

```
instance henselianLocalRing_adicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) := by
  haveI := isAdicComplete_maximalIdeal_adicCompletionIntegers K v
  exact { (inferInstance : IsLocalRing (v.adicCompletionIntegers K)) with
    is_henselian := fun f hf a₀ h₁ h₂ =>
      HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        f hf a₀ h₁ (h₂.map _) }
```

The `haveI` fires mathlib's `IsAdicComplete.henselianRing` to get `HenselianRing O 𝔪`, and
`h₂.map _` is the whole `HenselianRing → HenselianLocalRing` upgrade: `IsUnit.map` of the
quotient map turns `IsUnit (f.derivative.eval a₀)` in `O` into `IsUnit` of its residue.
-/

end IsDedekindDomain.HeightOneSpectrum

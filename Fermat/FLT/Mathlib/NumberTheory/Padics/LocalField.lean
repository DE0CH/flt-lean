/-
LocalField.lean — own work for the Fermat project.

`ℚ_[p]` is a nonarchimedean local field in the mathlib
`IsNonarchimedeanLocalField` sense: mathlib provides the
`ValuativeRel`, `IsNontrivial`, and `LocallyCompactSpace` instances,
and this file supplies the missing `IsValuativeTopology` instance (the
norm topology of `ℚ_[p]` is the valuation topology of
`Padic.mulValuation`: norm balls and valuation balls coincide via
`‖z‖ = p^(−v(z))`). This is the gateway that lets the Tate-curve
framework of `KnownIn1980s/EllipticCurves/TateCurve.lean` (stated over
an abstract nonarchimedean local field) be instantiated at the local
fields `ℚ_[q]` when deriving the multiplicative-reduction leaves of
`FreyCurve/Semistable.lean`.
-/
module

public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

@[expose] public section

open ValuativeRel WithZero

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- The defining formula of `Padic.mulValuation` at a nonzero argument. -/
lemma mulValuation_eq {x : ℚ_[p]} (hx : x ≠ 0) :
    Padic.mulValuation x = exp (-x.valuation) := by
  simp [Padic.mulValuation, hx]

/-- **The norm topology of `ℚ_[p]` is the valuative topology**: norm
balls and valuation balls coincide, `‖z‖ < p^m ↔ v(z) < exp m`, via
`‖z‖ = p^(−valuation z)`. -/
noncomputable instance isValuativeTopology : IsValuativeTopology ℚ_[p] := by
  apply IsValuativeTopology.of_mem_nhds_zero_iff_vle (v := Padic.mulValuation)
  intro s
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 :=
    (Nat.cast_ne_zero (R := ℚ_[p])).mpr (Fact.out : p.Prime).ne_zero
  constructor
  · intro hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ hp1)
    have hx0 : ((p : ℚ_[p]) ^ (n : ℤ)) ≠ 0 := zpow_ne_zero _ hp0
    have hval : Padic.mulValuation ((p : ℚ_[p]) ^ (n : ℤ)) =
        exp (-(n : ℤ)) := by
      rw [mulValuation_eq hx0, Padic.valuation_zpow, Padic.valuation_p,
        mul_one]
    refine ⟨Units.mk0 (Padic.mulValuation.restrict ((p : ℚ_[p]) ^ (n : ℤ)))
      (fun h => hx0 ((Padic.mulValuation).zero_iff.mp
        ((Valuation.restrict_eq_zero_iff _).mp h))), ?_⟩
    intro z hz
    simp only [Set.mem_setOf_eq, Units.val_mk0] at hz
    rw [Valuation.restrict_lt_iff] at hz
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    by_cases hz0 : z = 0
    · rw [hz0, norm_zero]; exact hε
    · rw [mulValuation_eq hz0, hval, exp_lt_exp, neg_lt_neg_iff] at hz
      rw [Padic.norm_eq_zpow_neg_valuation hz0]
      calc ((p : ℝ)) ^ (-z.valuation) < (p : ℝ) ^ (-(n : ℤ)) := by
            apply zpow_lt_zpow_right₀ hp1
            omega
        _ = ((p : ℝ)⁻¹) ^ (n : ℕ) := by
            rw [inv_pow, ← zpow_natCast, ← zpow_neg]
        _ < ε := hn
  · rintro ⟨γ, hγ⟩
    have hδ0 : (0 : ℤᵐ⁰) <
        MonoidWithZeroHom.ValueGroup₀.embedding γ.val := by
      rw [zero_lt_iff]
      intro h
      exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
        (h.trans (map_zero _).symm))
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hδ0.ne'
    apply Metric.mem_nhds_iff.mpr
    refine ⟨(p : ℝ) ^ (Multiplicative.toAdd m),
      zpow_pos (by positivity) _, ?_⟩
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    apply hγ
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_lt_iff_lt_embedding, ← hm]
    by_cases hz0 : z = 0
    · rw [hz0, map_zero, zero_lt_iff]
      exact_mod_cast (WithZero.coe_ne_zero)
    · rw [mulValuation_eq hz0]
      rw [Padic.norm_eq_zpow_neg_valuation hz0] at hz
      have hlt : -z.valuation < Multiplicative.toAdd m :=
        (zpow_lt_zpow_iff_right₀ hp1).mp hz
      show exp (-z.valuation) < (m : ℤᵐ⁰)
      rw [show ((m : ℤᵐ⁰)) = exp (Multiplicative.toAdd m) from rfl,
        exp_lt_exp]
      exact hlt

/-- **`ℚ_[p]` is a nonarchimedean local field**: the valuative topology
instance above together with mathlib's local compactness and
nontriviality. Gateway for instantiating the Tate-curve framework at
`k = ℚ_[q]`. -/
noncomputable instance isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end Padic

/-!
### The adic completions of `ℚ` as nonarchimedean local fields

The same instance package for `IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v`
directly — this is the spelling in which the local Galois groups
(`localInertiaGroup`, `GaloisRep.toLocal`) of the tree are phrased, so
instantiating the Tate-curve framework here avoids any transport
through `ℚ_[p]`. The `ValuativeRel` is the one induced by the `Valued`
instance; `IsValuativeTopology` is definitional
(`Valued.mem_nhds_zero` is already stated in the `ValueGroup₀` form);
local compactness transports along the continuous algebra isomorphism
with `ℚ_[p]` (`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`);
nontriviality is witnessed by any nonzero element of the prime.
-/

namespace AdicCompletionRat

open ValuativeRel IsDedekindDomain

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

noncomputable instance valuativeRelAdicCompletionRat :
    ValuativeRel (HeightOneSpectrum.adicCompletion ℚ v) :=
  .ofValuation (Valued.v : Valuation _ ℤᵐ⁰)

instance compatibleValuedAdicCompletionRat :
    (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
      ℤᵐ⁰).Compatible :=
  .ofValuation _

noncomputable instance isValuativeTopologyAdicCompletionRat :
    IsValuativeTopology (HeightOneSpectrum.adicCompletion ℚ v) := by
  have H : ∀ {s : Set (HeightOneSpectrum.adicCompletion ℚ v)},
      s ∈ nhds 0 ↔
      ∃ (γ : ((MonoidWithZeroHom.ofClass
        (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
          ℤᵐ⁰)).ValueGroup₀)ˣ),
      {z | (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
        ℤᵐ⁰).restrict z < γ} ⊆ s := by
    intro s
    rw [Valued.mem_nhds_zero]
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (v := Valued.v) H

noncomputable instance locallyCompactSpaceAdicCompletionRat :
    LocallyCompactSpace (HeightOneSpectrum.adicCompletion ℚ v) := by
  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v).1.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
    v).toHomeomorph.symm.locallyCompactSpace_iff.mp inferInstance

set_option maxHeartbeats 1000000 in
instance isNontrivialAdicCompletionRat :
    ValuativeRel.IsNontrivial (HeightOneSpectrum.adicCompletion ℚ v) := by
  constructor
  obtain ⟨π, hmem, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set x : HeightOneSpectrum.adicCompletion ℚ v :=
    algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)
      (algebraMap (NumberField.RingOfIntegers ℚ) ℚ π) with hx
  have hveq : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
      ℤᵐ⁰) x =
      v.valuation ℚ (algebraMap (NumberField.RingOfIntegers ℚ) ℚ π) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hv0 : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
      ℤᵐ⁰) x ≠ 0 := by
    rw [hveq, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v π hne
  have hv1 : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
      ℤᵐ⁰) x < 1 := by
    rw [hveq, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem
      _ _).mpr hmem
  refine ⟨ValuativeRel.valuation _ x, ?_, ?_⟩
  · intro h
    exact hv0 ((ValuativeRel.isEquiv (ValuativeRel.valuation _)
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
        ℤᵐ⁰)).eq_zero.mp h)
  · exact ne_of_lt ((ValuativeRel.isEquiv (ValuativeRel.valuation _)
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v)
        ℤᵐ⁰)).lt_one_iff_lt_one.mpr hv1)

/-- **The adic completions of `ℚ` are nonarchimedean local fields** —
the gateway that lets the Tate-curve framework be instantiated at
`k = adicCompletion ℚ v`, the exact spelling of the tree's local
Galois machinery. -/
noncomputable instance isNonarchimedeanLocalFieldAdicCompletionRat :
    IsNonarchimedeanLocalField (HeightOneSpectrum.adicCompletion ℚ v) where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The completion is a valuative extension of `ℚ`-with-the-`v`-adic
valuation** (PROVEN): the coercion `WithVal (v.valuation ℚ) →
adicCompletion ℚ v` matches the two `ofValuation` valuative relations
(`Valued.valuedCompletion_apply` through the `toCompletion`
projection). This is the hypothesis under which the sorry-free
reduction-type transfer of `ReductionBaseChange.lean`
(`hasMultiplicativeReduction_baseChange`,
`hasSplitMultiplicativeReduction_baseChange`) applies to the
completion. -/
noncomputable instance valuativeExtensionWithValAdicCompletionRat :
    ValuativeExtension (WithVal (v.valuation ℚ))
      (HeightOneSpectrum.adicCompletion ℚ v) where
  vle_iff_vle a b := by
    show Valued.v ((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) a) ≤
      Valued.v ((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) b) ↔
      Valued.v a ≤ Valued.v b
    rw [show Valued.v ((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) a) =
      Valued.v (((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) a).toCompletion) from rfl,
      show Valued.v ((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) b) =
      Valued.v (((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) b).toCompletion) from rfl]
    rw [show (((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) a).toCompletion) =
      (↑a : (v.valuation ℚ).Completion) from rfl,
      show (((algebraMap (WithVal (v.valuation ℚ))
        (HeightOneSpectrum.adicCompletion ℚ v)) b).toCompletion) =
      (↑b : (v.valuation ℚ).Completion) from rfl,
      Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]

end AdicCompletionRat

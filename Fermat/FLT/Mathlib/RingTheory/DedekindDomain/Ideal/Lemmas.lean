/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.NumberField.Basic
public import Fermat.FLT.DedekindDomain.AdicValuation
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Prime.Int

/-!
# Lemmas

Material destined for Mathlib.
-/

@[expose] public section

open IsDedekindDomain
open scoped NumberField

/-- Pulling back elements of `HeightOneSpectrum` along a ring isomorphism. -/
def RingEquiv.heightOneSpectrumComap {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (P : HeightOneSpectrum B) : HeightOneSpectrum A :=
  {
    asIdeal := .comap e P.asIdeal
    isPrime := P.asIdeal.comap_isPrime e
    ne_bot h := P.ne_bot <| Ideal.comap_injective_of_surjective e e.surjective <| by
      rw [h, Ideal.comap_bot_of_injective e e.injective]
  }

open IsDedekindDomain in
/-- The bijection `HeightOneSpectrum A ≃ HeightOneSpectrum B` induced by a ring isomorphism
between `A` and `B`. -/
def RingEquiv.heightOneSpectrum {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    HeightOneSpectrum A ≃ HeightOneSpectrum B where
      toFun := e.symm.heightOneSpectrumComap
      invFun := e.heightOneSpectrumComap
      left_inv P := by
        ext1
        convert! Ideal.comap_comap e.toRingHom e.symm.toRingHom
        simp
      right_inv Q := by
        ext1
        convert! Ideal.comap_comap e.symm.toRingHom e.toRingHom
        simp

/-- The element of `HeightOneSpectrum ℤ` associated to a prime number. -/
def Nat.Prime.toHeightOneSpectrumInt {p : ℕ} (hp : p.Prime) : HeightOneSpectrum ℤ where
  asIdeal := .span {(p : ℤ)}
  isPrime := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hp.ne_zero), ← prime_iff_prime_int]
  ne_bot := mt Submodule.span_singleton_eq_bot.mp (Int.ofNat_ne_zero.mpr hp.ne_zero)

/-- The element of `HeightOneSpectrum (𝓞 ℚ)` associated to a prime number. -/
noncomputable def Nat.Prime.toHeightOneSpectrumRingOfIntegersRat {p : ℕ} (hp : p.Prime) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
  Rat.ringOfIntegersEquiv.symm.heightOneSpectrum <| hp.toHeightOneSpectrumInt

/-- Membership in the ideal of the `p`-place of `ℚ`, computed through the
integer equivalence (an exposed unfolding for downstream modules). -/
lemma Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal {p : ℕ}
    (hp : p.Prime) (x : NumberField.RingOfIntegers ℚ) :
    x ∈ hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal ↔
      (p : ℤ) ∣ Rat.ringOfIntegersEquiv x := by
  show x ∈ Ideal.comap _ (Ideal.span {(p : ℤ)}) ↔ _
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  rfl

/-- **The prime of `𝓞 ℚ` attached to the prime number `q` is `(q)`**
(PROVEN): unfolding `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`,
the ideal is the comap of `span {(q : ℤ)}` along
`Rat.ringOfIntegersEquiv`, and a ring isomorphism carries spans of
singletons to spans of singletons while preserving `Nat.cast`. -/
lemma asIdeal_toHeightOneSpectrumRingOfIntegersRat {q : ℕ} (hq : q.Prime) :
    hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal =
      Ideal.span {(q : NumberField.RingOfIntegers ℚ)} := by
  have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal =
      Ideal.comap (Rat.ringOfIntegersEquiv.symm.symm) (Ideal.span {(q : ℤ)}) := rfl
  rw [h1, RingEquiv.symm_symm, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton,
    map_natCast]

open IsDedekindDomain.HeightOneSpectrum in
set_option maxHeartbeats 1000000 in
/-- **`q` is a uniformizer of `𝒪ᵥ = ℤ_q`** (PROVEN — this expresses the
ABSOLUTE UNRAMIFIEDNESS of the base, `e = 1`): the maximal ideal of the
`v`-adic integer ring at the place `v = v_q` of `ℚ` is the span of `q`.
Through `adicCompletion.maximalIdeal_eq_span_uniformizer` it suffices
that the valuation of `q` in `ℚ_q` is exactly `ofAdd (−1)`, which
reduces along `valuedAdicCompletion_eq_valuation` and
`valuation_of_algebraMap` to the `intValuation` of `q` in `𝓞 ℚ`,
computed by `intValuation_singleton` from `v_q = span {q}`
(`asIdeal_toHeightOneSpectrumRingOfIntegersRat`). -/
lemma maximalIdeal_adicCompletionIntegers_eq_span {q : ℕ} (hq : q.Prime) :
    IsLocalRing.maximalIdeal
        (adicCompletionIntegers ℚ hq.toHeightOneSpectrumRingOfIntegersRat) =
      Ideal.span
        {(q : adicCompletionIntegers ℚ hq.toHeightOneSpectrumRingOfIntegersRat)} := by
  have hq0 : ((q : NumberField.RingOfIntegers ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hq.ne_zero
  have hval : hq.toHeightOneSpectrumRingOfIntegersRat.intValuation
      ((q : NumberField.RingOfIntegers ℚ)) = Multiplicative.ofAdd (-1 : ℤ) :=
    hq.toHeightOneSpectrumRingOfIntegersRat.intValuation_singleton hq0
      (asIdeal_toHeightOneSpectrumRingOfIntegersRat hq)
  apply adicCompletion.maximalIdeal_eq_span_uniformizer
  -- the valuation of `q` in `ℚ_q`, assembled entirely in the mathlib
  -- lemmas' own coercion spelling (avoiding any cross-spelling defeq)
  have h := (valuedAdicCompletion_eq_valuation
      (v := hq.toHeightOneSpectrumRingOfIntegersRat) (K := ℚ)
      ((q : NumberField.RingOfIntegers ℚ))).trans
    ((valuation_of_algebraMap
      (v := hq.toHeightOneSpectrumRingOfIntegersRat) (K := ℚ)
      ((q : NumberField.RingOfIntegers ℚ))).trans hval)
  convert h using 2
  norm_cast

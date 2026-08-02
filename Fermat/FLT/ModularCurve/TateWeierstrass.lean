/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter
public import Fermat.FLT.Mathlib.RingTheory.InvariantCoarseRing
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

/-!
# The Tate curve over `ℚ((q))` as a Weierstrass curve, and its transcendental `j`

This module carries the *arithmetic* half of the q-expansion principle at the cusp `∞`
of `X_0(N)` — see `exists_nonConstantClassify_gamma0Datum_fractionRingPowerSeries` in
`Fermat/FLT/ModularCurve/X0.lean`, which is what consumes it.

`Fermat/FLT/KnownIn1980s/EllipticCurves/TateParameter.lean` already builds, sorry-free,
the formal series

* `TateCurve.a₄Formal = -5s₃(q)` and `TateCurve.a₆Formal = -(5s₃(q) + 7s₅(q))/12` in `ℤ⟦q⟧`,
* `TateCurve.ΔFormal`, DEFINED as the Weierstrass discriminant of `⟨1, 0, 0, a₄, a₆⟩`,
  with `constantCoeff ΔFormal = 0` and `coeff 1 ΔFormal = 1`,
* `TateCurve.c₄Formal = 1 + 240s₃(q)`,

but only as *series*: `WeierstrassCurve.tateCurve` there lives over a complete
nonarchimedean field and is reached through `TateCurve.evalInt`, which needs a
`ValuativeRel` structure that `ℚ((q))` does not carry at this pin.

Nothing of the sort is needed to write the curve down over `ℚ((q))` itself: the
coefficients are *already* power series, so one only has to push them along the ring
homomorphism `ℤ⟦q⟧ → ℚ⟦q⟧ → ℚ((q))`.  That is `Fermat.TateQ.toLaurentQ`, and
`Fermat.TateQ.tateWeierstrass` is the Tate curve it produces.

## What is proven here

* `Fermat.TateQ.tateWeierstrass.IsElliptic` — the discriminant is `q + O(q²) ≠ 0`.
* `Fermat.TateQ.not_isAlgebraic_j_tateWeierstrass` — `j(Tate(q))` is **transcendental
  over `ℚ`**.  This is the non-constancy witness of the q-expansion principle, and the
  proof is three lines of coefficient bookkeeping rather than the classical appeal to
  the pole of `j = 1/q + 744 + 196884q + ⋯`:

  > `j·Δ = c₄³`.  If `j` were algebraic over `ℚ` it would lie in `ℚ`, because `ℚ` is
  > algebraically closed in `ℚ((q))`
  > (`mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries`).  Both `Δ` and
  > `c₄³` come from `ℚ⟦q⟧`, where `algebraMap` is injective, so the identity holds
  > there; comparing constant coefficients gives `j·0 = 1`.

  Note the proof never mentions the pole, and in particular never needs `jInv` to be
  inverted: the vanishing of `constantCoeff Δ` is doing all the work, which is the
  formal content of "the Tate curve degenerates at `q = 0`".

## What is NOT here

The canonical cyclic subgroup `μ_N ⊆ Tate(q)[N]` — the *level* structure — is not
constructed here.  It is the open leaf
`exists_stableCyclicPoint_tateWeierstrass` in `X0.lean`, stated about
`tateWeierstrass` so that it pins this curve and no other.
-/

namespace Fermat.TateQ

open PowerSeries

/-- The field `ℚ((q))` of formal Laurent series, as the fraction field of `ℚ⟦q⟧`.

This is the spelling the q-expansion cluster of `X0.lean` uses throughout
(`FractionRing (PowerSeries ℚ)` rather than `LaurentSeries ℚ`), because it is what
`mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries` is stated about. -/
abbrev LaurentQ : Type := FractionRing (PowerSeries ℚ)

/-- The group law on the points of a Weierstrass curve over `AlgebraicClosure LaurentQ`
needs a `DecidableEq`, which is supplied classically once here so that every consumer
picks up the SAME instance.  `Fermat/FLT/GaloisRepresentation/HardlyRamified/Frey.lean`
does exactly this for `AlgebraicClosure ℚ` (`instDecidableEqAlgebraicClosureRat_fermat`);
without an analogue here, `AddGroup (E⁄(AlgebraicClosure LaurentQ)).Point` fails to
synthesize, which is what the level-structure leaf in `X0.lean` is stated over. -/
noncomputable instance : DecidableEq (AlgebraicClosure LaurentQ) :=
  Classical.typeDecidableEq _

/-- The coefficient map `ℤ⟦q⟧ → ℚ((q))`: extend the coefficients to `ℚ` and include the
power series into their fraction field. -/
noncomputable def toLaurentQ : (PowerSeries ℤ) →+* LaurentQ :=
  (algebraMap (PowerSeries ℚ) LaurentQ).comp (PowerSeries.map (Int.castRingHom ℚ))

theorem toLaurentQ_apply (F : PowerSeries ℤ) :
    toLaurentQ F = algebraMap (PowerSeries ℚ) LaurentQ (PowerSeries.map (Int.castRingHom ℚ) F) :=
  rfl

theorem toLaurentQ_injective : Function.Injective toLaurentQ :=
  (IsFractionRing.injective (PowerSeries ℚ) LaurentQ).comp
    (PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective)

/-- **The Tate curve `E_q : y² + xy = x³ + a₄(q)x + a₆(q)` over `ℚ((q))`.**

The coefficients are the formal series of `TateParameter.lean` with their coefficients
read in `ℚ`; no valuation, completeness or convergence input is used. -/
noncomputable def tateWeierstrass : WeierstrassCurve LaurentQ :=
  ⟨1, 0, 0, toLaurentQ TateCurve.a₄Formal, toLaurentQ TateCurve.a₆Formal⟩

@[simp] theorem tateWeierstrass_a₁ : tateWeierstrass.a₁ = 1 := rfl
@[simp] theorem tateWeierstrass_a₂ : tateWeierstrass.a₂ = 0 := rfl
@[simp] theorem tateWeierstrass_a₃ : tateWeierstrass.a₃ = 0 := rfl
@[simp] theorem tateWeierstrass_a₄ :
    tateWeierstrass.a₄ = toLaurentQ TateCurve.a₄Formal := rfl
@[simp] theorem tateWeierstrass_a₆ :
    tateWeierstrass.a₆ = toLaurentQ TateCurve.a₆Formal := rfl

/-- The discriminant of the Tate curve is the image of `TateCurve.ΔFormal`.

This is an identity of *definitions*: `ΔFormal` is defined in `TateParameter.lean` as
the Weierstrass discriminant of `⟨1, 0, 0, a₄Formal, a₆Formal⟩`, specialised by hand to
`a₁ = 1`, `a₂ = a₃ = 0`. -/
theorem Δ_tateWeierstrass : tateWeierstrass.Δ = toLaurentQ TateCurve.ΔFormal := by
  simp only [TateCurve.ΔFormal, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tateWeierstrass_a₁, tateWeierstrass_a₂, tateWeierstrass_a₃,
    tateWeierstrass_a₄, tateWeierstrass_a₆]
  ring

/-- The `c₄` of the Tate curve is the image of `TateCurve.c₄Formal = 1 + 240s₃`. -/
theorem c₄_tateWeierstrass : tateWeierstrass.c₄ = toLaurentQ TateCurve.c₄Formal := by
  simp only [TateCurve.c₄Formal, TateCurve.a₄Formal, map_add, map_mul, map_neg, map_one,
    map_ofNat, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    tateWeierstrass_a₁, tateWeierstrass_a₂, tateWeierstrass_a₃, tateWeierstrass_a₄]
  ring

theorem ΔFormal_ne_zero : TateCurve.ΔFormal ≠ 0 := fun h => by
  have h1 := TateCurve.coeff_one_ΔFormal
  rw [h] at h1
  simp at h1

theorem Δ_tateWeierstrass_ne_zero : tateWeierstrass.Δ ≠ 0 := by
  rw [Δ_tateWeierstrass]
  intro h
  exact ΔFormal_ne_zero (toLaurentQ_injective (by simpa using h))

instance : tateWeierstrass.IsElliptic :=
  ⟨(isUnit_iff_ne_zero).mpr Δ_tateWeierstrass_ne_zero⟩

/-- `j · Δ = c₄³`, i.e. the defining relation of the `j`-invariant with the unit
`Δ'` cleared. -/
theorem j_mul_Δ_tateWeierstrass :
    tateWeierstrass.j * tateWeierstrass.Δ = tateWeierstrass.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ' tateWeierstrass]
  rw [mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- `c₄(q) = 1 + 240s₃(q)` has constant coefficient `1`, since `σ₃(0) = 0`. -/
theorem constantCoeff_c₄Formal : PowerSeries.constantCoeff TateCurve.c₄Formal = 1 := by
  have h : PowerSeries.constantCoeff (TateCurve.sInt 3) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, TateCurve.sInt, PowerSeries.coeff_mk]
    simp
  rw [TateCurve.c₄Formal, map_add, map_mul, h]
  simp

/-- **The `j`-invariant of the Tate curve is transcendental over `ℚ`** (PROVEN).

This is the non-constancy witness of the q-expansion principle at the cusp `∞`.

`ℚ` is algebraically closed in `ℚ((q))`, so an algebraic `j` would be a rational
constant `r`; then `r · Δ = c₄³` already in `ℚ⟦q⟧`, where `constantCoeff Δ = 0` and
`constantCoeff c₄ = 1`, giving `0 = 1`. -/
theorem not_isAlgebraic_j_tateWeierstrass : ¬ IsAlgebraic ℚ tateWeierstrass.j := by
  intro hj
  obtain ⟨r, hr⟩ := mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries hj
  -- The identity `r · Δ = c₄³` in `ℚ((q))`.
  have key : algebraMap ℚ LaurentQ r * toLaurentQ TateCurve.ΔFormal
      = toLaurentQ TateCurve.c₄Formal ^ 3 := by
    rw [hr, ← Δ_tateWeierstrass, ← c₄_tateWeierstrass]
    exact j_mul_Δ_tateWeierstrass
  -- Both sides come from `ℚ⟦q⟧`, where `algebraMap` is injective.
  have hC : algebraMap (PowerSeries ℚ) LaurentQ (PowerSeries.C r)
      = algebraMap ℚ LaurentQ r := by
    rw [IsScalarTower.algebraMap_apply ℚ (PowerSeries ℚ) LaurentQ r]
    simp
  have key' : PowerSeries.C r * PowerSeries.map (Int.castRingHom ℚ) TateCurve.ΔFormal
      = (PowerSeries.map (Int.castRingHom ℚ) TateCurve.c₄Formal) ^ 3 := by
    apply IsFractionRing.injective (PowerSeries ℚ) LaurentQ
    rw [map_mul, map_pow, hC]
    exact key
  have hΔ : PowerSeries.constantCoeff
      (PowerSeries.map (Int.castRingHom ℚ) TateCurve.ΔFormal) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, TateCurve.constantCoeff_ΔFormal]
    simp
  have hc : PowerSeries.constantCoeff
      (PowerSeries.map (Int.castRingHom ℚ) TateCurve.c₄Formal) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_c₄Formal]
    simp
  have hcc := congrArg (PowerSeries.constantCoeff) key'
  rw [map_mul, hΔ, mul_zero, map_pow, hc] at hcc
  simp at hcc

end Fermat.TateQ

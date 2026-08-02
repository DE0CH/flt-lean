/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenA.Factor1
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenA.Factor2
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenA.Factor3
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenA.Factor4

/-!
# Row `p = 17`, `j = −882216989/131072`: `H ∣ X ^ (67 ^ 34) - X`, and `IsCoprime H (X ^ (67 ^ 2) - X)`

The certificate is machine-checked twice outside Lean — PARI/GP 2.15.4 and an independent
Python reimplementation — and then re-derived here by the compiler, which is the only check
that counts.  Everything below is generated; see `MazurNonCMFrobenius.lean` for `XPow` and why
the exponents have to stay behind it.

**THIS ROW IS SPLIT ONE MODULE PER FACTOR, AND THE SPLIT IS WHAT MAKES IT BUILD AT ALL.**
Lean elaborates a module SINGLE-THREADED, so the whole row in one file — 14 200 lines, ~2 500
theorems — was still running after 60 minutes at 47 GB resident when it was stopped
(2026-07-31).  `H` is a product of 4 pairwise-coprime factors of degree 34 whose
square-and-multiply chains share nothing but the factor definitions, so each chain lives in
`SeventeenA/Factor{i}.lean` and `lake` elaborates the 4 of them CONCURRENTLY.  What is left here
is everything that mentions more than one factor: the product identity, the 6 Bézout
coprimalities, the `xpow_mul` assembly and the coprimality leaf.
-/

@[expose] public section

open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- Every step below carries the same `simp only […]; reduce_mod_char; all_goals ring_nf;
-- all_goals reduce_mod_char`.  `reduce_mod_char` closes SOME of the zero-cofactor identities
-- outright and leaves work behind in others, so the tail is genuinely needed and genuinely
-- unreachable case by case; deciding the branch from the cofactor was tried and is wrong.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Fermat.MazurNonCMCertificate

/-- The factorisation of `H` used by every statement below. -/
theorem factor_hPolySeventeenA : hPolySeventeenA = fSeventeenA1 * fSeventeenA2 * fSeventeenA3 * fSeventeenA4 := by
  simp only [hPolySeventeenA, fSeventeenA1, fSeventeenA2, fSeventeenA3, fSeventeenA4]
  ring_nf
  reduce_mod_char

/-! ### Pairwise coprimality of the factors, by explicit Bézout identities -/

theorem copSeventeenA1_2 : IsCoprime fSeventeenA1 fSeventeenA2 :=
  ⟨20*X^33 + 33*X^32 + 15*X^31 + 43*X^30 + 12*X^29 + 42*X^28 + 42*X^27 + 54*X^26 + 44*X^25 + 30*X^24 +
    61*X^23 + 18*X^22 + 54*X^21 + 62*X^20 + 17*X^19 + 2*X^18 + 62*X^17 + 52*X^16 + 5*X^15 + 21*X^14 +
    63*X^13 + 19*X^12 + 9*X^11 + 8*X^10 + 17*X^9 + 37*X^8 + 14*X^7 + 59*X^6 + 41*X^5 + 9*X^4 +
    46*X^3 + 62*X^2 + 61*X + 53,
   47*X^33 + 5*X^32 + 62*X^31 + 2*X^30 + 11*X^29 + 10*X^28 + 22*X^27 + 28*X^26 + 39*X^25 + 6*X^24 +
    11*X^23 + 62*X^22 + 23*X^21 + 65*X^20 + 59*X^19 + 27*X^18 + 6*X^17 + 30*X^16 + 63*X^15 + 64*X^14 +
    60*X^13 + 66*X^12 + 41*X^11 + 52*X^10 + 36*X^9 + 25*X^8 + 2*X^7 + 9*X^6 + 35*X^5 + 24*X^4 +
    26*X^3 + 26*X^2 + 66*X,
   by simp only [fSeventeenA1, fSeventeenA2]; ring_nf; reduce_mod_char⟩

theorem copSeventeenA1_3 : IsCoprime fSeventeenA1 fSeventeenA3 :=
  ⟨38*X^33 + 59*X^32 + 4*X^31 + 37*X^30 + 58*X^29 + 65*X^28 + 53*X^27 + 65*X^26 + 15*X^25 + 24*X^24 +
    7*X^23 + 18*X^22 + 17*X^21 + 2*X^20 + 43*X^19 + 31*X^18 + 16*X^17 + 33*X^16 + 51*X^15 + 16*X^14 +
    25*X^13 + 65*X^12 + 21*X^11 + 51*X^10 + 35*X^9 + 53*X^8 + 66*X^7 + 17*X^6 + 26*X^5 + 20*X^4 +
    11*X^3 + X^2 + 9*X + 39,
   29*X^33 + 20*X^32 + 34*X^31 + 65*X^30 + 15*X^29 + 40*X^28 + 44*X^27 + 58*X^26 + 30*X^24 + 51*X^23 +
    25*X^22 + 4*X^21 + 18*X^20 + 5*X^19 + 20*X^18 + 23*X^17 + 58*X^16 + 7*X^14 + 7*X^13 + 60*X^12 +
    43*X^11 + 33*X^10 + 27*X^9 + 45*X^8 + 51*X^7 + 27*X^6 + 18*X^5 + 30*X^4 + 28*X^3 + 44*X^2 + 8*X +
    25,
   by simp only [fSeventeenA1, fSeventeenA3]; ring_nf; reduce_mod_char⟩

theorem copSeventeenA1_4 : IsCoprime fSeventeenA1 fSeventeenA4 :=
  ⟨56*X^33 + 63*X^32 + 19*X^31 + 51*X^30 + 8*X^29 + 59*X^28 + 12*X^27 + 16*X^26 + 2*X^25 + 44*X^24 +
    13*X^23 + 32*X^22 + 12*X^21 + 17*X^20 + 4*X^19 + 8*X^18 + 9*X^17 + 56*X^16 + 43*X^15 + 11*X^14 +
    39*X^13 + 27*X^12 + 41*X^11 + 55*X^10 + 37*X^9 + 11*X^8 + 66*X^7 + 51*X^6 + 63*X^5 + 13*X^4 +
    6*X^3 + 39*X^2 + 62*X + 10,
   11*X^33 + 23*X^32 + 52*X^31 + 37*X^30 + 20*X^29 + 46*X^28 + 52*X^27 + 27*X^26 + 61*X^25 + 27*X^24 +
    3*X^23 + 6*X^22 + 61*X^21 + 15*X^20 + 60*X^19 + 66*X^18 + 21*X^17 + 37*X^16 + 47*X^15 + 58*X^14 +
    38*X^13 + 56*X^12 + 60*X^11 + 49*X^10 + 50*X^9 + 20*X^8 + 25*X^7 + 49*X^6 + 66*X^5 + 50*X^4 +
    20*X^3 + 5*X^2 + 21*X + 31,
   by simp only [fSeventeenA1, fSeventeenA4]; ring_nf; reduce_mod_char⟩

theorem copSeventeenA2_3 : IsCoprime fSeventeenA2 fSeventeenA3 :=
  ⟨63*X^33 + 44*X^32 + 53*X^31 + 61*X^30 + 58*X^29 + 16*X^28 + 33*X^27 + 35*X^26 + 57*X^25 + 14*X^24 +
    30*X^23 + 64*X^22 + 28*X^21 + 59*X^20 + 28*X^19 + 53*X^18 + 65*X^17 + 8*X^16 + 56*X^15 + 10*X^14 +
    10*X^13 + 22*X^12 + 51*X^11 + 37*X^10 + 45*X^9 + 52*X^8 + 10*X^7 + 7*X^6 + 16*X^5 + 30*X^4 +
    18*X^3 + 32*X^2 + 43*X + 30,
   4*X^33 + 11*X^32 + 29*X^31 + 43*X^30 + 19*X^29 + 6*X^28 + 31*X^27 + 50*X^26 + 41*X^25 + 3*X^24 +
    28*X^23 + 13*X^22 + 16*X^21 + 7*X^20 + 6*X^18 + 39*X^17 + 30*X^16 + 20*X^15 + 9*X^14 + 7*X^13 +
    2*X^12 + 65*X^11 + 3*X^10 + 28*X^9 + 66*X^8 + 36*X^7 + 13*X^6 + 48*X^5 + 23*X^4 + 33*X^3 +
    36*X^2 + 26*X + 33,
   by simp only [fSeventeenA2, fSeventeenA3]; ring_nf; reduce_mod_char⟩

theorem copSeventeenA2_4 : IsCoprime fSeventeenA2 fSeventeenA4 :=
  ⟨33*X^33 + 12*X^32 + 11*X^31 + 61*X^30 + 31*X^29 + 54*X^28 + 66*X^27 + 53*X^26 + 44*X^25 + 40*X^24 +
    42*X^23 + 65*X^22 + 12*X^21 + 53*X^20 + 17*X^19 + 25*X^18 + 13*X^17 + 35*X^16 + 37*X^15 +
    23*X^14 + 37*X^13 + 54*X^12 + 19*X^11 + 29*X^10 + 48*X^9 + 65*X^8 + 42*X^7 + 37*X^5 + 28*X^4 +
    28*X^3 + 24*X^2 + 49*X + 5,
   34*X^33 + 9*X^32 + 3*X^31 + 49*X^30 + 30*X^29 + 24*X^28 + 32*X^27 + 62*X^26 + 24*X^25 + 42*X^24 +
    64*X^23 + 32*X^22 + 27*X^21 + 49*X^20 + 12*X^19 + 47*X^18 + 11*X^17 + 40*X^16 + 32*X^15 +
    30*X^14 + 30*X^13 + 47*X^12 + 24*X^11 + 58*X^10 + 29*X^9 + 31*X^8 + 43*X^7 + 57*X^6 + 35*X^5 +
    32*X^4 + 29*X^3 + 2*X^2 + 58*X + 30,
   by simp only [fSeventeenA2, fSeventeenA4]; ring_nf; reduce_mod_char⟩

theorem copSeventeenA3_4 : IsCoprime fSeventeenA3 fSeventeenA4 :=
  ⟨42*X^33 + 64*X^32 + 57*X^31 + 58*X^30 + 29*X^29 + 37*X^28 + 48*X^27 + 25*X^26 + 62*X^25 + 16*X^24 +
    22*X^23 + 56*X^22 + 51*X^21 + 20*X^20 + 20*X^19 + 7*X^18 + 25*X^17 + 27*X^16 + 10*X^15 + 7*X^14 +
    30*X^13 + 63*X^12 + 21*X^11 + 10*X^10 + 58*X^9 + 27*X^8 + 25*X^7 + 13*X^6 + 44*X^5 + 60*X^4 +
    28*X^3 + 27*X^2 + 26*X + 13,
   25*X^33 + 56*X^32 + 18*X^31 + 14*X^30 + 3*X^29 + 26*X^28 + 46*X^27 + 18*X^26 + 2*X^25 + 35*X^24 +
    35*X^23 + 24*X^22 + 52*X^21 + 20*X^20 + 39*X^19 + 38*X^18 + 14*X^17 + 63*X^16 + 62*X^15 +
    16*X^14 + 45*X^13 + 27*X^12 + 65*X^11 + 3*X^10 + 57*X^9 + 38*X^8 + 58*X^7 + 15*X^6 + 12*X^5 +
    62*X^4 + 31*X^3 + 16*X^2 + 25*X + 19,
   by simp only [fSeventeenA3, fSeventeenA4]; ring_nf; reduce_mod_char⟩

/-! ### Assembly -/

theorem dvd_X_pow_card_pow_sub_X_hPolySeventeenA :
    hPolySeventeenA ∣ X ^ (Nat.card (ZMod 67)) ^ 34 - X := by
  have h2 := xpow_mul copSeventeenA1_2 pSeventeenA1s307 pSeventeenA2s307
  have c3 : IsCoprime (fSeventeenA1 * fSeventeenA2) fSeventeenA3 :=
    (copSeventeenA1_3).mul_left copSeventeenA2_3
  have h3 := xpow_mul c3 h2 pSeventeenA3s307
  have c4 : IsCoprime (fSeventeenA1 * fSeventeenA2 * fSeventeenA3) fSeventeenA4 :=
    ((copSeventeenA1_4).mul_left copSeventeenA2_4).mul_left copSeventeenA3_4
  have h4 := xpow_mul c4 h3 pSeventeenA4s307
  rw [factor_hPolySeventeenA]
  exact xpow_card (by rw [Nat.card_zmod]; norm_num) h4

theorem cofrobSeventeenA1 : IsCoprime fSeventeenA1 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenA1 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (32*X^33 + 37*X^32 + 31*X^31 + 6*X^30 + 62*X^29 + 52*X^28 + 5*X^27 + 36*X^26 + 59*X^25 + 35*X^24 +
        45*X^23 + 14*X^22 + 53*X^21 + 33*X^20 + 41*X^19 + 64*X^18 + 21*X^17 + 46*X^16 + 65*X^15 +
        55*X^14 + 18*X^13 + 17*X^12 + 54*X^11 + 16*X^10 + 40*X^9 + 66*X^8 + 47*X^7 + 5*X^6 + 41*X^5 +
        49*X^4 + 45*X^3 + 5*X^2 + 36*X + 34) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenA1cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (32*X^33 + 37*X^32 + 31*X^31 + 6*X^30 + 62*X^29 + 52*X^28 + 5*X^27 + 36*X^26 + 59*X^25 + 35*X^24 +
        45*X^23 + 14*X^22 + 53*X^21 + 33*X^20 + 41*X^19 + 64*X^18 + 21*X^17 + 46*X^16 + 65*X^15 +
        55*X^14 + 18*X^13 + 17*X^12 + 54*X^11 + 16*X^10 + 40*X^9 + 66*X^8 + 47*X^7 + 5*X^6 + 41*X^5 +
        49*X^4 + 45*X^3 + 5*X^2 + 35*X + 34) +
      fSeventeenA1 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨33*X^32 + 54*X^31 + 47*X^30 + 63*X^29 + 6*X^28 + 4*X^27 + 57*X^26 + 11*X^25 + 8*X^24 + 3*X^23 +
      13*X^22 + 48*X^21 + 3*X^20 + 49*X^19 + 25*X^18 + 49*X^17 + 36*X^16 + 58*X^15 + 24*X^14 +
      66*X^13 + 9*X^12 + 26*X^11 + 12*X^10 + 51*X^9 + 49*X^8 + 54*X^7 + 41*X^6 + 17*X^5 + 15*X^4 +
      52*X^3 + 35*X^2 + 10*X + 38,
    22*X^33 + 20*X^32 + 6*X^31 + 11*X^30 + 14*X^29 + 13*X^28 + 32*X^27 + 19*X^26 + 52*X^25 + 65*X^24 +
      8*X^23 + X^22 + 18*X^21 + 43*X^20 + 66*X^19 + 58*X^18 + 14*X^17 + 56*X^16 + 25*X^15 + 55*X^14 +
      58*X^13 + 30*X^12 + 3*X^11 + 30*X^10 + 20*X^9 + 17*X^8 + 37*X^7 + 44*X^6 + 10*X^5 + 22*X^4 +
      23*X^3 + 57*X^2 + 47*X + 17,
    by simp only [fSeventeenA1]; ring_nf; reduce_mod_char⟩ w

theorem cofrobSeventeenA2 : IsCoprime fSeventeenA2 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenA2 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (48*X^33 + 16*X^32 + 25*X^31 + 35*X^30 + 35*X^29 + 64*X^28 + 10*X^27 + 34*X^26 + 53*X^25 + 40*X^24 +
        30*X^23 + 41*X^22 + 51*X^21 + 33*X^20 + 25*X^19 + 49*X^18 + 39*X^17 + 60*X^16 + 25*X^15 +
        10*X^14 + 9*X^12 + 42*X^11 + 56*X^10 + 55*X^9 + 6*X^8 + 31*X^7 + 33*X^6 + 31*X^5 + 29*X^4 +
        33*X^3 + 5*X^2 + 47*X + 30) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenA2cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (48*X^33 + 16*X^32 + 25*X^31 + 35*X^30 + 35*X^29 + 64*X^28 + 10*X^27 + 34*X^26 + 53*X^25 + 40*X^24 +
        30*X^23 + 41*X^22 + 51*X^21 + 33*X^20 + 25*X^19 + 49*X^18 + 39*X^17 + 60*X^16 + 25*X^15 +
        10*X^14 + 9*X^12 + 42*X^11 + 56*X^10 + 55*X^9 + 6*X^8 + 31*X^7 + 33*X^6 + 31*X^5 + 29*X^4 +
        33*X^3 + 5*X^2 + 46*X + 30) +
      fSeventeenA2 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨22*X^32 + 17*X^31 + 10*X^30 + 29*X^29 + 53*X^28 + 17*X^27 + 38*X^26 + 44*X^25 + 5*X^24 + 61*X^23 +
      62*X^22 + 24*X^21 + 4*X^20 + 44*X^19 + 15*X^18 + 50*X^17 + 48*X^16 + 23*X^15 + 57*X^14 +
      39*X^13 + X^12 + 29*X^11 + 55*X^10 + 6*X^9 + 51*X^8 + 35*X^7 + 63*X^6 + 10*X^5 + 52*X^4 +
      25*X^3 + 64*X^2 + 7*X + 57,
    47*X^33 + 53*X^32 + 34*X^31 + 62*X^30 + 45*X^29 + 40*X^28 + 31*X^27 + 59*X^26 + 58*X^25 + 26*X^24 +
      47*X^23 + 55*X^22 + 10*X^21 + 15*X^20 + 28*X^19 + 43*X^18 + 54*X^17 + 9*X^16 + 47*X^15 +
      17*X^14 + 14*X^13 + 33*X^12 + 58*X^11 + 2*X^10 + 53*X^9 + 18*X^8 + 21*X^7 + 38*X^6 + 60*X^5 +
      39*X^4 + 26*X^3 + 10*X^2 + 44*X + 12,
    by simp only [fSeventeenA2]; ring_nf; reduce_mod_char⟩ w

theorem cofrobSeventeenA3 : IsCoprime fSeventeenA3 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenA3 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (X^33 + 57*X^32 + 57*X^31 + 66*X^30 + 34*X^28 + 7*X^27 + 62*X^26 + 57*X^25 + 10*X^24 + 25*X^23 +
        49*X^22 + 39*X^21 + 38*X^20 + 29*X^19 + 14*X^18 + 44*X^17 + 51*X^16 + 32*X^15 + 52*X^14 +
        17*X^13 + 5*X^12 + 35*X^11 + 62*X^10 + 54*X^9 + 3*X^8 + 59*X^7 + 8*X^6 + 12*X^5 + 45*X^4 +
        45*X^3 + 36*X^2 + 13*X + 5) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenA3cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (X^33 + 57*X^32 + 57*X^31 + 66*X^30 + 34*X^28 + 7*X^27 + 62*X^26 + 57*X^25 + 10*X^24 + 25*X^23 +
        49*X^22 + 39*X^21 + 38*X^20 + 29*X^19 + 14*X^18 + 44*X^17 + 51*X^16 + 32*X^15 + 52*X^14 +
        17*X^13 + 5*X^12 + 35*X^11 + 62*X^10 + 54*X^9 + 3*X^8 + 59*X^7 + 8*X^6 + 12*X^5 + 45*X^4 +
        45*X^3 + 36*X^2 + 12*X + 5) +
      fSeventeenA3 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨42*X^32 + 66*X^31 + 44*X^30 + 51*X^29 + 19*X^28 + 17*X^27 + 23*X^26 + 4*X^25 + 56*X^24 + X^23 +
      56*X^22 + 19*X^21 + 60*X^20 + 44*X^19 + 41*X^18 + 23*X^17 + 66*X^16 + 48*X^15 + 55*X^14 +
      21*X^13 + 58*X^12 + 22*X^11 + 60*X^10 + 62*X^9 + 58*X^8 + 12*X^7 + 5*X^6 + 34*X^5 + 45*X^4 +
      5*X^3 + 27*X^2 + 4*X + 25,
    25*X^33 + 30*X^32 + 34*X^31 + 19*X^30 + 38*X^29 + X^28 + 50*X^27 + 53*X^26 + 11*X^25 + 23*X^24 +
      30*X^23 + 53*X^22 + 29*X^21 + 44*X^20 + 63*X^19 + 12*X^18 + 31*X^17 + 49*X^16 + 7*X^15 +
      29*X^14 + 46*X^13 + 18*X^12 + 63*X^11 + 5*X^10 + 2*X^9 + X^8 + 61*X^7 + 42*X^6 + X^5 + 36*X^4 +
      64*X^3 + 24*X^2 + 53*X + 54,
    by simp only [fSeventeenA3]; ring_nf; reduce_mod_char⟩ w

theorem cofrobSeventeenA4 : IsCoprime fSeventeenA4 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenA4 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (22*X^33 + 66*X^32 + 47*X^31 + 47*X^30 + 3*X^29 + 20*X^28 + 56*X^27 + 58*X^26 + 26*X^25 + 48*X^24 +
        23*X^23 + 60*X^22 + 43*X^21 + 5*X^20 + 48*X^19 + 2*X^18 + 15*X^17 + 38*X^16 + 32*X^15 +
        18*X^14 + 46*X^13 + 36*X^12 + 56*X^11 + 25*X^10 + 57*X^8 + 55*X^7 + 12*X^6 + 15*X^5 + 27*X^4 +
        61*X^3 + 22*X^2 + 61*X + 3) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenA4cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (22*X^33 + 66*X^32 + 47*X^31 + 47*X^30 + 3*X^29 + 20*X^28 + 56*X^27 + 58*X^26 + 26*X^25 + 48*X^24 +
        23*X^23 + 60*X^22 + 43*X^21 + 5*X^20 + 48*X^19 + 2*X^18 + 15*X^17 + 38*X^16 + 32*X^15 +
        18*X^14 + 46*X^13 + 36*X^12 + 56*X^11 + 25*X^10 + 57*X^8 + 55*X^7 + 12*X^6 + 15*X^5 + 27*X^4 +
        61*X^3 + 22*X^2 + 60*X + 3) +
      fSeventeenA4 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨62*X^32 + 65*X^31 + 6*X^30 + 46*X^29 + 5*X^28 + 58*X^27 + 54*X^26 + 43*X^25 + 33*X^24 + 38*X^23 +
      2*X^22 + 58*X^21 + 26*X^20 + 56*X^19 + 14*X^18 + 38*X^17 + 36*X^16 + 59*X^15 + 64*X^14 +
      22*X^13 + 13*X^12 + 8*X^11 + 24*X^10 + 65*X^9 + 45*X^8 + 7*X^7 + 10*X^6 + 24*X^5 + 32*X^4 +
      66*X^3 + 46*X^2 + 17*X + 55,
    52*X^33 + 56*X^32 + 18*X^30 + 21*X^29 + 60*X^27 + 62*X^26 + 61*X^25 + 11*X^24 + 10*X^23 + 33*X^22 +
      17*X^21 + 63*X^20 + 65*X^19 + 38*X^18 + 16*X^17 + 44*X^16 + 57*X^15 + 26*X^14 + 52*X^13 +
      49*X^12 + 43*X^11 + 60*X^10 + 16*X^9 + 42*X^8 + 46*X^7 + 24*X^6 + 48*X^5 + 30*X^4 + 25*X^3 +
      34*X^2 + 24*X + 48,
    by simp only [fSeventeenA4]; ring_nf; reduce_mod_char⟩ w

theorem isCoprime_hPolySeventeenA :
    IsCoprime hPolySeventeenA (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  rw [factor_hPolySeventeenA]
  exact (((cofrobSeventeenA1).mul_left cofrobSeventeenA2).mul_left cofrobSeventeenA3).mul_left cofrobSeventeenA4

end Fermat.MazurNonCMCertificate

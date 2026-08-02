/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenB.Factor1
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenB.Factor2
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenB.Factor3
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.SeventeenB.Factor4

/-!
# Row `p = 17`, `j = −297756989/2`: `H ∣ X ^ (67 ^ 34) - X`, and `IsCoprime H (X ^ (67 ^ 2) - X)`

The certificate is machine-checked twice outside Lean — PARI/GP 2.15.4 and an independent
Python reimplementation — and then re-derived here by the compiler, which is the only check
that counts.  Everything below is generated; see `MazurNonCMFrobenius.lean` for `XPow` and why
the exponents have to stay behind it.

**THIS ROW IS SPLIT ONE MODULE PER FACTOR, AND THE SPLIT IS WHAT MAKES IT BUILD AT ALL.**
Lean elaborates a module SINGLE-THREADED, so the whole row in one file — 14 200 lines, ~2 500
theorems — was still running after 60 minutes at 47 GB resident when it was stopped
(2026-07-31).  `H` is a product of 4 pairwise-coprime factors of degree 34 whose
square-and-multiply chains share nothing but the factor definitions, so each chain lives in
`SeventeenB/Factor{i}.lean` and `lake` elaborates the 4 of them CONCURRENTLY.  What is left here
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
theorem factor_hPolySeventeenB : hPolySeventeenB = fSeventeenB1 * fSeventeenB2 * fSeventeenB3 * fSeventeenB4 := by
  simp only [hPolySeventeenB, fSeventeenB1, fSeventeenB2, fSeventeenB3, fSeventeenB4]
  ring_nf
  reduce_mod_char

/-! ### Pairwise coprimality of the factors, by explicit Bézout identities -/

theorem copSeventeenB1_2 : IsCoprime fSeventeenB1 fSeventeenB2 :=
  ⟨58*X^33 + 38*X^32 + 50*X^31 + 56*X^30 + 16*X^29 + 53*X^28 + 53*X^27 + 10*X^26 + 27*X^25 + 51*X^24 +
    23*X^23 + 50*X^22 + 25*X^21 + 4*X^20 + 12*X^19 + 14*X^18 + 23*X^17 + 47*X^16 + 12*X^15 + 7*X^14 +
    53*X^13 + 29*X^12 + 27*X^11 + 7*X^10 + 17*X^8 + 65*X^7 + 50*X^6 + 17*X^5 + 38*X^4 + 44*X^3 +
    4*X^2 + 42*X + 9,
   9*X^33 + 51*X^32 + 22*X^31 + 61*X^30 + 62*X^29 + 12*X^28 + 49*X^27 + 47*X^26 + 56*X^25 + 41*X^24 +
    52*X^23 + 28*X^22 + 42*X^21 + 19*X^20 + 13*X^19 + 27*X^18 + 59*X^17 + 55*X^16 + 2*X^14 + 65*X^13 +
    43*X^12 + 18*X^11 + 66*X^10 + 56*X^9 + 24*X^8 + 66*X^7 + 28*X^6 + 37*X^5 + 49*X^4 + 8*X^3 +
    36*X^2 + 47*X + 3,
   by simp only [fSeventeenB1, fSeventeenB2]; ring_nf; reduce_mod_char⟩

theorem copSeventeenB1_3 : IsCoprime fSeventeenB1 fSeventeenB3 :=
  ⟨20*X^33 + 48*X^32 + 23*X^31 + 42*X^30 + 32*X^29 + 5*X^28 + 65*X^27 + 9*X^26 + 66*X^25 + 62*X^24 +
    27*X^23 + 61*X^22 + 34*X^21 + 25*X^20 + 36*X^19 + 6*X^18 + 43*X^17 + 3*X^16 + 31*X^15 + 18*X^14 +
    63*X^13 + 9*X^12 + 19*X^11 + 66*X^10 + 25*X^9 + 17*X^8 + 28*X^7 + 28*X^6 + 60*X^5 + 23*X^4 +
    29*X^3 + 60*X^2 + 7*X,
   47*X^33 + 25*X^32 + 55*X^31 + 11*X^30 + 49*X^29 + 2*X^28 + 19*X^27 + 25*X^26 + 23*X^25 + 13*X^24 +
    47*X^23 + 5*X^22 + 12*X^21 + 55*X^20 + 11*X^19 + 31*X^18 + 51*X^17 + 31*X^16 + 13*X^14 + 16*X^13 +
    34*X^12 + 44*X^11 + 63*X^10 + 56*X^9 + 39*X^8 + 44*X^7 + 33*X^6 + 60*X^5 + 26*X^4 + 62*X^3 +
    43*X^2 + 5*X + 14,
   by simp only [fSeventeenB1, fSeventeenB3]; ring_nf; reduce_mod_char⟩

theorem copSeventeenB1_4 : IsCoprime fSeventeenB1 fSeventeenB4 :=
  ⟨43*X^33 + 64*X^32 + 31*X^31 + 10*X^30 + 20*X^29 + 48*X^28 + 28*X^27 + 45*X^26 + 26*X^25 + 32*X^24 +
    26*X^23 + 26*X^22 + 41*X^21 + 21*X^20 + 64*X^19 + 64*X^18 + 49*X^17 + 34*X^16 + 18*X^15 + 8*X^14 +
    19*X^13 + 13*X^12 + 3*X^11 + 40*X^10 + 66*X^9 + 26*X^8 + 17*X^7 + 5*X^6 + 64*X^5 + 25*X^4 +
    45*X^3 + 64*X^2 + 28*X + 53,
   24*X^33 + 66*X^32 + 40*X^31 + 32*X^30 + 24*X^29 + 7*X^28 + 49*X^27 + 34*X^26 + 61*X^25 + 51*X^24 +
    33*X^23 + 35*X^22 + 3*X^21 + 16*X^20 + 50*X^19 + 9*X^18 + 45*X^17 + 32*X^16 + 7*X^14 + 9*X^13 +
    37*X^12 + 62*X^11 + 36*X^10 + 33*X^9 + 31*X^8 + 44*X^7 + 62*X^6 + 38*X^5 + 39*X^4 + 52*X^3 +
    16*X^2 + 53*X + 4,
   by simp only [fSeventeenB1, fSeventeenB4]; ring_nf; reduce_mod_char⟩

theorem copSeventeenB2_3 : IsCoprime fSeventeenB2 fSeventeenB3 :=
  ⟨65*X^33 + 42*X^32 + 8*X^31 + 37*X^30 + 66*X^29 + 60*X^28 + X^27 + 12*X^26 + 31*X^25 + 37*X^24 +
    30*X^23 + 9*X^22 + 36*X^21 + 39*X^20 + 48*X^19 + 18*X^18 + 37*X^17 + 37*X^16 + 58*X^15 + 44*X^14 +
    19*X^13 + 47*X^12 + 55*X^11 + 18*X^10 + 40*X^9 + 37*X^8 + 20*X^7 + X^6 + 50*X^5 + 13*X^4 +
    66*X^3 + 10*X^2 + 23*X + 36,
   2*X^33 + 21*X^32 + 44*X^31 + 15*X^30 + 30*X^29 + 46*X^28 + 41*X^27 + 49*X^26 + 48*X^25 + 18*X^24 +
    27*X^23 + 25*X^22 + 38*X^21 + 6*X^20 + 41*X^19 + 29*X^18 + 59*X^17 + 29*X^15 + 53*X^14 + 2*X^13 +
    15*X^12 + 45*X^11 + 64*X^10 + 23*X^9 + 49*X^8 + 38*X^7 + 14*X^6 + 65*X^5 + 23*X^4 + 9*X^3 +
    49*X^2 + 44*X + 61,
   by simp only [fSeventeenB2, fSeventeenB3]; ring_nf; reduce_mod_char⟩

theorem copSeventeenB2_4 : IsCoprime fSeventeenB2 fSeventeenB4 :=
  ⟨58*X^33 + 58*X^32 + 35*X^31 + 15*X^30 + 2*X^29 + 39*X^28 + 25*X^27 + 34*X^26 + 6*X^25 + 29*X^24 +
    49*X^23 + 62*X^22 + 46*X^21 + 10*X^20 + 7*X^19 + 12*X^18 + 61*X^17 + 55*X^16 + 52*X^15 + 41*X^14 +
    X^13 + 7*X^12 + 23*X^11 + 37*X^10 + 22*X^9 + 66*X^8 + 50*X^7 + 30*X^6 + 66*X^5 + 39*X^4 + 34*X^3 +
    62*X^2 + 51*X + 22,
   9*X^33 + 19*X^32 + 40*X^31 + 8*X^30 + 8*X^29 + 50*X^28 + 34*X^27 + 8*X^26 + 52*X^25 + 25*X^24 +
    47*X^23 + 6*X^22 + 31*X^21 + 24*X^20 + 25*X^19 + 56*X^18 + 2*X^17 + 43*X^16 + 44*X^14 + 3*X^13 +
    56*X^12 + 29*X^11 + 39*X^10 + 20*X^9 + 3*X^8 + 12*X^7 + 11*X^6 + 14*X^5 + 12*X^4 + 28*X^3 +
    41*X^2 + 17*X + 5,
   by simp only [fSeventeenB2, fSeventeenB4]; ring_nf; reduce_mod_char⟩

theorem copSeventeenB3_4 : IsCoprime fSeventeenB3 fSeventeenB4 :=
  ⟨33*X^33 + 8*X^32 + 15*X^31 + 19*X^30 + 22*X^29 + 13*X^28 + 32*X^27 + 52*X^26 + 65*X^25 + 4*X^24 +
    13*X^23 + 30*X^22 + 3*X^21 + 19*X^20 + 65*X^19 + 20*X^18 + 18*X^17 + 42*X^16 + 37*X^15 + 49*X^14 +
    29*X^13 + 30*X^12 + 15*X^10 + X^9 + 61*X^8 + 53*X^7 + 8*X^6 + 3*X^5 + 34*X^4 + 52*X^3 + 39*X^2 +
    66*X + 42,
   34*X^33 + X^32 + 53*X^31 + 60*X^30 + 32*X^29 + 29*X^28 + 25*X^27 + 21*X^26 + 40*X^25 + 31*X^24 +
    51*X^23 + 20*X^22 + 16*X^21 + 25*X^20 + 17*X^19 + 34*X^18 + 15*X^17 + 6*X^16 + 61*X^15 + 15*X^14 +
    17*X^13 + 24*X^12 + 59*X^11 + 14*X^10 + 27*X^9 + 46*X^8 + 53*X^7 + 15*X^6 + 13*X^5 + 63*X^4 +
    33*X^3 + 66*X + 5,
   by simp only [fSeventeenB3, fSeventeenB4]; ring_nf; reduce_mod_char⟩

/-! ### Assembly -/

theorem dvd_X_pow_card_pow_sub_X_hPolySeventeenB :
    hPolySeventeenB ∣ X ^ (Nat.card (ZMod 67)) ^ 34 - X := by
  have h2 := xpow_mul copSeventeenB1_2 pSeventeenB1s307 pSeventeenB2s307
  have c3 : IsCoprime (fSeventeenB1 * fSeventeenB2) fSeventeenB3 :=
    (copSeventeenB1_3).mul_left copSeventeenB2_3
  have h3 := xpow_mul c3 h2 pSeventeenB3s307
  have c4 : IsCoprime (fSeventeenB1 * fSeventeenB2 * fSeventeenB3) fSeventeenB4 :=
    ((copSeventeenB1_4).mul_left copSeventeenB2_4).mul_left copSeventeenB3_4
  have h4 := xpow_mul c4 h3 pSeventeenB4s307
  rw [factor_hPolySeventeenB]
  exact xpow_card (by rw [Nat.card_zmod]; norm_num) h4

theorem cofrobSeventeenB1 : IsCoprime fSeventeenB1 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenB1 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (14*X^33 + 66*X^32 + 2*X^31 + 16*X^30 + 9*X^29 + 62*X^28 + 8*X^27 + 15*X^26 + 12*X^25 + 51*X^24 +
        40*X^23 + 44*X^22 + 34*X^21 + 55*X^20 + 13*X^18 + 50*X^17 + 43*X^16 + 38*X^15 + 54*X^14 +
        62*X^13 + 11*X^12 + 45*X^11 + 8*X^10 + 32*X^9 + 5*X^8 + 35*X^7 + 66*X^6 + 30*X^5 + 2*X^4 +
        8*X^3 + 52*X^2 + 10*X + 20) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenB1cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (14*X^33 + 66*X^32 + 2*X^31 + 16*X^30 + 9*X^29 + 62*X^28 + 8*X^27 + 15*X^26 + 12*X^25 + 51*X^24 +
        40*X^23 + 44*X^22 + 34*X^21 + 55*X^20 + 13*X^18 + 50*X^17 + 43*X^16 + 38*X^15 + 54*X^14 +
        62*X^13 + 11*X^12 + 45*X^11 + 8*X^10 + 32*X^9 + 5*X^8 + 35*X^7 + 66*X^6 + 30*X^5 + 2*X^4 +
        8*X^3 + 52*X^2 + 9*X + 20) +
      fSeventeenB1 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨16*X^31 + 35*X^30 + 10*X^29 + 15*X^28 + 16*X^27 + 62*X^26 + 60*X^25 + 59*X^24 + 9*X^23 + 3*X^22 +
      53*X^21 + 33*X^20 + 64*X^19 + 12*X^18 + 2*X^17 + 35*X^16 + 49*X^15 + 22*X^14 + 17*X^13 +
      6*X^12 + 11*X^11 + 16*X^10 + 56*X^9 + 32*X^8 + 28*X^7 + 31*X^6 + 18*X^5 + 18*X^4 + 42*X^3 +
      8*X^2 + 60*X + 20,
    18*X^32 + 22*X^31 + 56*X^30 + 37*X^29 + 48*X^28 + 34*X^27 + 21*X^26 + 46*X^25 + 47*X^24 + 11*X^23 +
      64*X^22 + 52*X^21 + 18*X^20 + 29*X^19 + 40*X^18 + 46*X^17 + 9*X^16 + 13*X^15 + 16*X^14 +
      43*X^13 + 37*X^12 + 24*X^11 + 21*X^10 + 38*X^9 + 44*X^8 + 42*X^7 + 47*X^6 + 49*X^5 + 47*X^4 +
      43*X^3 + 32*X^2 + 10*X + 39,
    by simp only [fSeventeenB1]; ring_nf; reduce_mod_char⟩ w

theorem cofrobSeventeenB2 : IsCoprime fSeventeenB2 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenB2 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (7*X^33 + 46*X^32 + 65*X^31 + 59*X^30 + 43*X^29 + 15*X^28 + 38*X^27 + 43*X^26 + 38*X^25 + 52*X^24 +
        39*X^23 + 48*X^22 + 16*X^21 + 66*X^20 + 58*X^19 + 62*X^18 + 38*X^17 + X^16 + 26*X^15 +
        12*X^14 + 53*X^13 + 14*X^12 + 26*X^11 + 15*X^10 + 41*X^9 + 53*X^8 + 23*X^7 + 19*X^6 + 10*X^5 +
        22*X^4 + 51*X^3 + 5*X^2 + 9*X + 64) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenB2cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (7*X^33 + 46*X^32 + 65*X^31 + 59*X^30 + 43*X^29 + 15*X^28 + 38*X^27 + 43*X^26 + 38*X^25 + 52*X^24 +
        39*X^23 + 48*X^22 + 16*X^21 + 66*X^20 + 58*X^19 + 62*X^18 + 38*X^17 + X^16 + 26*X^15 +
        12*X^14 + 53*X^13 + 14*X^12 + 26*X^11 + 15*X^10 + 41*X^9 + 53*X^8 + 23*X^7 + 19*X^6 + 10*X^5 +
        22*X^4 + 51*X^3 + 5*X^2 + 8*X + 64) +
      fSeventeenB2 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨65*X^32 + 8*X^31 + 39*X^30 + 16*X^29 + 66*X^28 + 15*X^27 + 65*X^26 + 32*X^25 + 60*X^24 + 26*X^23 +
      66*X^22 + 61*X^21 + 48*X^20 + 37*X^19 + 31*X^18 + X^17 + 45*X^16 + 11*X^15 + 37*X^14 + 2*X^13 +
      10*X^12 + 53*X^11 + 24*X^10 + 27*X^9 + 50*X^8 + 48*X^7 + 24*X^6 + 39*X^5 + 37*X^4 + 60*X^3 +
      49*X^2 + 41*X + 40,
    29*X^33 + 42*X^32 + 7*X^31 + 35*X^30 + 27*X^29 + 50*X^28 + 13*X^27 + 15*X^25 + 58*X^24 + 7*X^23 +
      39*X^22 + 2*X^21 + 59*X^20 + 46*X^19 + X^18 + 19*X^17 + 57*X^16 + 50*X^15 + 4*X^14 + 32*X^13 +
      58*X^12 + X^11 + 52*X^10 + 25*X^9 + 35*X^8 + 32*X^7 + 39*X^6 + 28*X^5 + 55*X^4 + 9*X^3 +
      20*X^2 + 13*X + 36,
    by simp only [fSeventeenB2]; ring_nf; reduce_mod_char⟩ w

theorem cofrobSeventeenB3 : IsCoprime fSeventeenB3 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenB3 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (59*X^33 + 24*X^32 + 31*X^31 + 28*X^30 + 43*X^29 + 6*X^28 + 48*X^27 + 14*X^26 + 62*X^25 + 14*X^24 +
        10*X^23 + 6*X^22 + 42*X^21 + 16*X^20 + 50*X^19 + 30*X^18 + 14*X^17 + 45*X^16 + 3*X^15 +
        9*X^14 + 44*X^13 + 36*X^12 + 24*X^11 + 2*X^10 + 22*X^9 + 12*X^8 + 50*X^7 + 60*X^6 + 45*X^5 +
        48*X^4 + 34*X^3 + 33*X^2 + 58*X + 1) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenB3cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (59*X^33 + 24*X^32 + 31*X^31 + 28*X^30 + 43*X^29 + 6*X^28 + 48*X^27 + 14*X^26 + 62*X^25 + 14*X^24 +
        10*X^23 + 6*X^22 + 42*X^21 + 16*X^20 + 50*X^19 + 30*X^18 + 14*X^17 + 45*X^16 + 3*X^15 +
        9*X^14 + 44*X^13 + 36*X^12 + 24*X^11 + 2*X^10 + 22*X^9 + 12*X^8 + 50*X^7 + 60*X^6 + 45*X^5 +
        48*X^4 + 34*X^3 + 33*X^2 + 57*X + 1) +
      fSeventeenB3 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨46*X^32 + 10*X^31 + 50*X^30 + 57*X^29 + 24*X^28 + 2*X^27 + 45*X^26 + 16*X^25 + 55*X^24 + 28*X^23 +
      22*X^22 + 16*X^21 + 47*X^20 + 33*X^19 + 4*X^18 + 23*X^17 + 58*X^16 + 36*X^15 + 50*X^14 +
      8*X^13 + 40*X^12 + 12*X^11 + 34*X^10 + X^9 + 5*X^8 + 11*X^7 + 29*X^6 + 66*X^5 + 28*X^4 +
      40*X^3 + 36*X^2 + 61*X + 61,
    56*X^33 + 10*X^32 + 13*X^31 + 53*X^30 + 22*X^29 + 15*X^28 + 8*X^27 + 32*X^26 + 42*X^25 + 33*X^24 +
      4*X^23 + 16*X^22 + 10*X^21 + 59*X^20 + 58*X^19 + 32*X^18 + 40*X^17 + 41*X^16 + 7*X^15 +
      39*X^14 + 30*X^13 + 32*X^12 + 54*X^11 + 24*X^10 + 22*X^9 + 24*X^8 + 42*X^6 + 51*X^5 + X^4 +
      28*X^3 + 11*X^2 + 5*X + 11,
    by simp only [fSeventeenB3]; ring_nf; reduce_mod_char⟩ w

theorem cofrobSeventeenB4 : IsCoprime fSeventeenB4 (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  have hd : fSeventeenB4 ∣ X ^ (Nat.card (ZMod 67)) ^ 2 -
      (24*X^33 + 5*X^32 + 20*X^31 + 23*X^30 + 24*X^29 + 60*X^28 + 61*X^27 + 43*X^26 + 11*X^25 + 66*X^24 +
        45*X^23 + 27*X^22 + 24*X^21 + 3*X^20 + 62*X^19 + 45*X^18 + 51*X^17 + 23*X^16 + X^15 +
        26*X^14 + 51*X^13 + 51*X^12 + 17*X^11 + 12*X^10 + 53*X^9 + 43*X^8 + 43*X^7 + 11*X^6 + 44*X^5 +
        13*X^4 + 62*X^3 + 52*X^2 + 22*X + 52) :=
    xpow_card (by rw [Nat.card_zmod]; norm_num) pSeventeenB4cs15
  obtain ⟨w, hw⟩ := hd
  have key : (X : (ZMod 67)[X]) ^ (Nat.card (ZMod 67)) ^ 2 - X =
      (24*X^33 + 5*X^32 + 20*X^31 + 23*X^30 + 24*X^29 + 60*X^28 + 61*X^27 + 43*X^26 + 11*X^25 + 66*X^24 +
        45*X^23 + 27*X^22 + 24*X^21 + 3*X^20 + 62*X^19 + 45*X^18 + 51*X^17 + 23*X^16 + X^15 +
        26*X^14 + 51*X^13 + 51*X^12 + 17*X^11 + 12*X^10 + 53*X^9 + 43*X^8 + 43*X^7 + 11*X^6 + 44*X^5 +
        13*X^4 + 62*X^3 + 52*X^2 + 21*X + 52) +
      fSeventeenB4 * w := by linear_combination hw
  rw [key]
  exact IsCoprime.add_mul_left_right ⟨32*X^32 + 42*X^31 + 66*X^30 + 66*X^29 + 38*X^28 + 17*X^27 + 45*X^26 + 4*X^25 + 30*X^24 + 48*X^23 +
      55*X^22 + 41*X^21 + 30*X^20 + 66*X^19 + 16*X^18 + 61*X^17 + 3*X^16 + 10*X^15 + 47*X^14 +
      44*X^13 + 32*X^12 + 18*X^11 + 51*X^10 + 8*X^9 + 39*X^8 + 5*X^7 + 61*X^6 + 31*X^5 + 35*X^4 +
      31*X^3 + 6*X^2 + 23*X + 52,
    21*X^33 + 44*X^32 + 33*X^31 + 50*X^29 + 26*X^28 + 42*X^27 + 56*X^26 + 43*X^25 + 44*X^24 + 28*X^23 +
      25*X^22 + 54*X^21 + 43*X^20 + 57*X^19 + 31*X^18 + 23*X^17 + 13*X^16 + 32*X^15 + 13*X^14 +
      50*X^13 + 16*X^12 + 3*X^11 + 16*X^10 + 34*X^9 + 26*X^8 + 42*X^7 + 12*X^6 + 6*X^5 + 14*X^4 +
      12*X^3 + 52*X^2 + 53*X + 45,
    by simp only [fSeventeenB4]; ring_nf; reduce_mod_char⟩ w

theorem isCoprime_hPolySeventeenB :
    IsCoprime hPolySeventeenB (X ^ (Nat.card (ZMod 67)) ^ 2 - X) := by
  rw [factor_hPolySeventeenB]
  exact (((cofrobSeventeenB1).mul_left cofrobSeventeenB2).mul_left cofrobSeventeenB3).mul_left cofrobSeventeenB4

end Fermat.MazurNonCMCertificate

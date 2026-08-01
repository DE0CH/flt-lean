/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius

/-!
# Row `p = 17`, `j = −297756989/2`: factor 4 of `H`, and its two square-and-multiply chains

Generated.  This module holds ONE of the 4 pairwise-coprime degree-`34` factors of `H` and
the two chains run modulo it: `X ^ (67 ^ 34)` for the divisibility, and `X ^ (67 ^ 2)` for
the coprimality.  Both chains start from the same `XPow f 1 X`, so they cannot be separated
from each other; nothing else in the row refers to anything here except the final step of each
chain and the factor's own definition.

It is a separate module because elaboration is single-threaded per module — see
`SeventeenB.lean` for the measurement.  Every identity handed to `ring_nf` has degree `< 2 · 34`
however large the exponent, which is what square-and-multiply buys.
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

/-- Irreducible factor 4 of `H` on this row, of degree 34.  Its irreducibility is
not used anywhere — only that the 4 factors are pairwise coprime. -/
noncomputable def fSeventeenB4 : (ZMod 67)[X] :=
  X^34 + 65*X^33 + 27*X^32 + 11*X^31 + 66*X^30 + 61*X^29 + 59*X^28 + 27*X^27 + 45*X^26 + 39*X^25 +
    61*X^24 + 14*X^23 + X^22 + 8*X^21 + 30*X^20 + 51*X^19 + 59*X^18 + 18*X^17 + 35*X^16 + 44*X^15 +
    26*X^14 + 64*X^13 + 36*X^12 + 20*X^11 + 64*X^10 + 7*X^9 + 40*X^8 + 21*X^7 + 16*X^6 + 38*X^5 +
    23*X^4 + 4*X^3 + 28*X^2 + 21*X + 13

/-! ### Factor 4: `X ^ (67 ^ 34)` mod `f` by square-and-multiply -/

theorem pSeventeenB41 : XPow fSeventeenB4 1 X := xpow_one _

theorem pSeventeenB4s0 : XPow fSeventeenB4 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenB41 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s1 : XPow fSeventeenB4 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenB4s0 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s2 : XPow fSeventeenB4 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenB4s1 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s3 : XPow fSeventeenB4 9
    (X^9) :=
  mul_step (by norm_num) pSeventeenB4s2 pSeventeenB41 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s4 : XPow fSeventeenB4 18
    (X^18) :=
  sq_step (by norm_num) pSeventeenB4s3 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s5 : XPow fSeventeenB4 36
    (23*X^33 + 64*X^32 + 60*X^31 + 64*X^30 + 52*X^29 + 52*X^28 + 23*X^27 + 25*X^26 + 24*X^25 + 34*X^24 +
      44*X^23 + 44*X^22 + 6*X^21 + 60*X^20 + 32*X^19 + 13*X^18 + 32*X^17 + 21*X^16 + 25*X^15 +
      32*X^14 + 40*X^13 + 54*X^12 + 57*X^11 + 11*X^10 + 60*X^9 + 58*X^8 + 11*X^7 + X^6 + 20*X^5 +
      24*X^4 + 15*X^3 + 53*X^2 + 55*X + 31) :=
  sq_step (by norm_num) pSeventeenB4s4 ⟨
    X^2 + 2*X + 44,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s6 : XPow fSeventeenB4 37
    (43*X^33 + 42*X^32 + 12*X^31 + 8*X^30 + 56*X^29 + 6*X^28 + 7*X^27 + 61*X^26 + 8*X^25 + 48*X^24 +
      57*X^23 + 50*X^22 + 10*X^21 + 12*X^20 + 46*X^19 + 15*X^18 + 9*X^17 + 24*X^16 + 25*X^15 +
      45*X^14 + 56*X^13 + 33*X^12 + 20*X^11 + 62*X^10 + 31*X^9 + 29*X^8 + 54*X^7 + 54*X^6 + 21*X^5 +
      22*X^4 + 28*X^3 + 14*X^2 + 17*X + 36) :=
  mul_step (by norm_num) pSeventeenB4s5 pSeventeenB41 ⟨
    23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s7 : XPow fSeventeenB4 74
    (2*X^33 + 33*X^32 + 59*X^31 + 20*X^30 + 10*X^29 + 58*X^28 + 4*X^27 + 30*X^26 + 4*X^25 + 59*X^24 +
      41*X^23 + 53*X^22 + 38*X^21 + 9*X^20 + 4*X^19 + 41*X^18 + 57*X^17 + 61*X^16 + 49*X^15 + 4*X^14 +
      48*X^13 + 25*X^12 + 3*X^11 + 54*X^10 + 66*X^9 + 30*X^8 + 50*X^7 + 26*X^6 + 61*X^5 + 57*X^4 +
      59*X^3 + 50*X^2 + 62*X + 2) :=
  sq_step (by norm_num) pSeventeenB4s6 ⟨
    40*X^32 + 7*X^31 + 55*X^30 + 38*X^29 + 32*X^28 + 5*X^27 + 51*X^26 + 4*X^25 + 36*X^23 + 48*X^22 +
      64*X^21 + 52*X^20 + 18*X^19 + 20*X^18 + 2*X^17 + 28*X^16 + 54*X^15 + 43*X^14 + 55*X^13 +
      8*X^12 + 24*X^11 + 66*X^10 + 49*X^9 + 39*X^7 + 4*X^6 + 59*X^4 + 34*X^3 + 63*X^2 + 17*X + 48,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s8 : XPow fSeventeenB4 75
    (37*X^33 + 5*X^32 + 65*X^31 + 12*X^30 + 3*X^29 + 20*X^28 + 43*X^27 + 48*X^26 + 48*X^25 + 53*X^24 +
      25*X^23 + 36*X^22 + 60*X^21 + 11*X^20 + 6*X^19 + 6*X^18 + 25*X^17 + 46*X^16 + 50*X^15 +
      63*X^14 + 31*X^13 + 65*X^12 + 14*X^11 + 5*X^10 + 16*X^9 + 37*X^8 + 51*X^7 + 29*X^6 + 48*X^5 +
      13*X^4 + 42*X^3 + 6*X^2 + 27*X + 41) :=
  mul_step (by norm_num) pSeventeenB4s7 pSeventeenB41 ⟨
    2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s9 : XPow fSeventeenB4 150
    (14*X^33 + 19*X^32 + 4*X^31 + 2*X^30 + 60*X^29 + 35*X^28 + 49*X^27 + 24*X^26 + 40*X^25 + 33*X^24 +
      40*X^23 + 25*X^22 + 19*X^21 + 54*X^20 + 66*X^19 + 2*X^18 + 42*X^17 + 36*X^16 + 43*X^15 +
      37*X^14 + 64*X^13 + 10*X^12 + 13*X^11 + 53*X^10 + 49*X^9 + 13*X^8 + 47*X^7 + 16*X^6 + 12*X^5 +
      36*X^4 + 53*X^3 + 18*X^2 + 59*X + 56) :=
  sq_step (by norm_num) pSeventeenB4s8 ⟨
    29*X^32 + 26*X^31 + 17*X^30 + 15*X^29 + 62*X^28 + 55*X^27 + 46*X^26 + 34*X^25 + 47*X^24 + 10*X^23 +
      31*X^22 + 12*X^21 + 18*X^20 + 22*X^19 + 22*X^18 + 50*X^17 + X^16 + 3*X^15 + 14*X^14 + 32*X^13 +
      20*X^12 + 38*X^11 + 20*X^10 + 61*X^9 + 39*X^8 + 40*X^7 + 38*X^6 + 33*X^5 + 47*X^4 + 6*X^3 +
      28*X^2 + 36*X + 58,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s10 : XPow fSeventeenB4 151
    (47*X^33 + 28*X^32 + 49*X^31 + 7*X^30 + 52*X^29 + 27*X^28 + 48*X^27 + 13*X^26 + 23*X^25 + 57*X^24 +
      30*X^23 + 5*X^22 + 9*X^21 + 48*X^20 + 25*X^19 + 20*X^18 + 52*X^17 + 22*X^16 + 24*X^15 +
      35*X^14 + 52*X^13 + 45*X^12 + 41*X^11 + 24*X^10 + 49*X^9 + 23*X^8 + 57*X^7 + 56*X^6 + 40*X^5 +
      66*X^4 + 29*X^3 + 2*X^2 + 30*X + 19) :=
  mul_step (by norm_num) pSeventeenB4s9 pSeventeenB41 ⟨
    14,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s11 : XPow fSeventeenB4 302
    (50*X^33 + 12*X^32 + 29*X^31 + 48*X^30 + 12*X^29 + 20*X^28 + 11*X^27 + 4*X^26 + 57*X^25 + 65*X^24 +
      28*X^23 + 59*X^22 + 40*X^21 + 9*X^20 + 52*X^19 + 59*X^18 + 10*X^17 + 53*X^16 + 54*X^14 +
      47*X^13 + 7*X^12 + 29*X^11 + 9*X^10 + 51*X^9 + 57*X^8 + 27*X^7 + 12*X^6 + 47*X^5 + 35*X^4 +
      15*X^3 + 19*X^2 + 21*X + 5) :=
  sq_step (by norm_num) pSeventeenB4s10 ⟨
    65*X^32 + 15*X^31 + 47*X^30 + 31*X^29 + 9*X^28 + 46*X^27 + 11*X^26 + 20*X^25 + 52*X^24 + 12*X^23 +
      66*X^22 + 31*X^21 + 59*X^20 + 10*X^19 + 40*X^18 + 3*X^17 + 38*X^16 + 32*X^15 + 28*X^14 +
      24*X^13 + 55*X^12 + 52*X^11 + 46*X^10 + 29*X^9 + 43*X^8 + 6*X^7 + 7*X^6 + 15*X^5 + 60*X^4 +
      59*X^3 + 50*X^2 + 24*X + 48,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s12 : XPow fSeventeenB4 303
    (45*X^33 + 19*X^32 + 34*X^31 + 62*X^30 + 52*X^29 + 9*X^28 + 61*X^27 + 18*X^26 + 58*X^25 + 60*X^24 +
      29*X^23 + 57*X^22 + 11*X^21 + 26*X^20 + 55*X^19 + 8*X^18 + 24*X^17 + 59*X^16 + 65*X^15 +
      20*X^14 + 23*X^13 + 38*X^12 + 14*X^11 + 42*X^9 + 37*X^8 + 34*X^7 + 51*X^6 + 11*X^5 + 4*X^4 +
      20*X^3 + 28*X^2 + 27*X + 20) :=
  mul_step (by norm_num) pSeventeenB4s11 pSeventeenB41 ⟨
    50,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s13 : XPow fSeventeenB4 606
    (36*X^33 + 17*X^32 + 47*X^31 + 6*X^30 + 14*X^29 + 10*X^28 + 28*X^27 + 3*X^26 + 13*X^25 + 4*X^24 +
      49*X^23 + 39*X^22 + 19*X^21 + 32*X^20 + 10*X^19 + 5*X^18 + 48*X^17 + 2*X^16 + 2*X^15 + 46*X^14 +
      64*X^13 + 30*X^12 + 36*X^11 + 27*X^10 + 18*X^9 + 60*X^8 + 41*X^7 + 17*X^6 + 5*X^5 + 39*X^4 +
      13*X^3 + 59*X^2 + 55*X + 10) :=
  sq_step (by norm_num) pSeventeenB4s12 ⟨
    15*X^32 + 65*X^31 + 64*X^30 + 55*X^29 + 45*X^28 + 33*X^27 + 39*X^26 + 60*X^25 + 45*X^24 + 20*X^23 +
      63*X^22 + 47*X^21 + 54*X^20 + 48*X^19 + 30*X^18 + 15*X^17 + 12*X^16 + 42*X^15 + 30*X^14 +
      8*X^13 + 47*X^12 + 16*X^11 + 3*X^10 + 31*X^9 + 60*X^8 + 13*X^7 + 60*X^6 + 22*X^5 + 20*X^4 +
      51*X^3 + X^2 + 51*X + 30,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s14 : XPow fSeventeenB4 607
    (22*X^33 + 13*X^32 + 12*X^31 + 50*X^30 + 25*X^29 + 48*X^28 + 36*X^27 + X^26 + 7*X^25 + 64*X^24 +
      4*X^23 + 50*X^22 + 12*X^21 + 2*X^20 + 45*X^19 + X^18 + 24*X^17 + 15*X^16 + 3*X^15 + 66*X^14 +
      4*X^13 + 13*X^12 + 44*X^11 + 59*X^10 + 9*X^9 + 8*X^8 + 65*X^7 + 32*X^6 + 11*X^5 + 56*X^4 +
      49*X^3 + 52*X^2 + 58*X + 1) :=
  mul_step (by norm_num) pSeventeenB4s13 pSeventeenB41 ⟨
    36,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s15 : XPow fSeventeenB4 1214
    (23*X^33 + 44*X^32 + 41*X^31 + 4*X^30 + 42*X^29 + 61*X^28 + 33*X^27 + 41*X^26 + 59*X^25 + 42*X^24 +
      29*X^23 + 66*X^22 + 18*X^21 + 19*X^20 + 22*X^19 + 57*X^18 + 3*X^17 + 60*X^16 + 36*X^15 +
      25*X^14 + 30*X^13 + 55*X^12 + 25*X^11 + 37*X^10 + 49*X^8 + 17*X^7 + 30*X^6 + 7*X^5 + 29*X^4 +
      33*X^3 + 38*X^2 + 15*X + 35) :=
  sq_step (by norm_num) pSeventeenB4s14 ⟨
    15*X^32 + 66*X^31 + 22*X^30 + 6*X^29 + 45*X^28 + 52*X^27 + 46*X^25 + 57*X^24 + 28*X^23 + 53*X^22 +
      49*X^21 + 22*X^19 + 16*X^18 + 61*X^17 + 25*X^16 + 24*X^15 + 34*X^14 + 55*X^13 + 11*X^12 +
      57*X^11 + 12*X^10 + 40*X^9 + 58*X^7 + 4*X^6 + 26*X^5 + 17*X^4 + 35*X^3 + 47*X^2 + 56*X + 18,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s16 : XPow fSeventeenB4 1215
    (23*X^33 + 23*X^32 + 19*X^31 + 65*X^30 + 65*X^29 + 16*X^28 + 23*X^27 + 29*X^26 + 16*X^25 + 33*X^24 +
      12*X^23 + 62*X^22 + 36*X^21 + 2*X^20 + 23*X^19 + 53*X^18 + 48*X^17 + 35*X^16 + 18*X^15 +
      35*X^14 + 57*X^13 + X^12 + 46*X^11 + 2*X^10 + 22*X^9 + 35*X^8 + 16*X^7 + 41*X^6 + 26*X^5 +
      40*X^4 + 13*X^3 + 41*X^2 + 21*X + 36) :=
  mul_step (by norm_num) pSeventeenB4s15 pSeventeenB41 ⟨
    23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s17 : XPow fSeventeenB4 2430
    (39*X^33 + 52*X^31 + 24*X^30 + 21*X^29 + 44*X^28 + 20*X^27 + 46*X^26 + 60*X^25 + 48*X^24 + 40*X^23 +
      54*X^22 + 11*X^21 + 42*X^20 + 43*X^19 + 47*X^18 + 57*X^17 + 59*X^16 + 21*X^15 + 65*X^14 +
      7*X^13 + 26*X^12 + 20*X^11 + 15*X^10 + 23*X^9 + 63*X^8 + 56*X^7 + 66*X^6 + 29*X^5 + 28*X^4 +
      55*X^3 + 63*X^2 + 19) :=
  sq_step (by norm_num) pSeventeenB4s16 ⟨
    60*X^32 + 39*X^31 + 62*X^30 + 64*X^29 + 4*X^28 + 39*X^27 + 22*X^26 + 11*X^25 + 19*X^24 + 51*X^23 +
      19*X^22 + 52*X^21 + 12*X^20 + 55*X^19 + 32*X^18 + 27*X^17 + 31*X^16 + 27*X^15 + 14*X^14 +
      9*X^13 + 66*X^12 + 64*X^11 + 28*X^10 + 43*X^9 + 23*X^8 + 2*X^7 + 5*X^6 + 5*X^5 + 66*X^4 +
      13*X^3 + 32*X^2 + 50*X + 57,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s18 : XPow fSeventeenB4 4860
    (65*X^33 + 57*X^32 + 18*X^31 + 33*X^30 + 5*X^29 + 56*X^28 + 12*X^27 + 41*X^26 + 19*X^25 + 18*X^24 +
      65*X^23 + 25*X^22 + 54*X^21 + 58*X^20 + 57*X^19 + 6*X^18 + 36*X^17 + 10*X^16 + 6*X^14 + 2*X^13 +
      55*X^12 + 53*X^11 + 22*X^10 + 39*X^9 + 15*X^8 + 43*X^7 + 46*X^5 + 54*X^4 + 44*X^3 + 45*X^2 +
      17*X + 2) :=
  sq_step (by norm_num) pSeventeenB4s17 ⟨
    47*X^32 + 27*X^31 + 27*X^30 + 10*X^29 + 33*X^28 + 41*X^27 + 13*X^26 + 13*X^25 + 39*X^24 + 25*X^23 +
      8*X^22 + 23*X^21 + 34*X^20 + 56*X^19 + 61*X^18 + 31*X^17 + 17*X^16 + 49*X^15 + 33*X^14 +
      22*X^13 + 8*X^12 + 60*X^11 + 39*X^10 + 30*X^9 + 48*X^8 + 6*X^7 + 60*X^6 + 65*X^5 + 7*X^4 +
      19*X^3 + 29*X^2 + 8*X + 7,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s19 : XPow fSeventeenB4 9720
    (57*X^33 + 19*X^32 + X^31 + 41*X^30 + 53*X^29 + 55*X^28 + 13*X^27 + 49*X^26 + 34*X^25 + 62*X^24 +
      3*X^23 + 24*X^22 + 18*X^21 + 44*X^20 + 8*X^19 + 34*X^18 + 15*X^17 + 61*X^16 + 23*X^15 + 7*X^14 +
      46*X^13 + 10*X^12 + 44*X^11 + 65*X^10 + 52*X^9 + 41*X^8 + 5*X^7 + 45*X^6 + 51*X^5 + 23*X^4 +
      20*X^3 + 47*X^2 + 56*X + 66) :=
  sq_step (by norm_num) pSeventeenB4s18 ⟨
    4*X^32 + 48*X^31 + 16*X^30 + 9*X^29 + 46*X^28 + 6*X^27 + 46*X^26 + 5*X^25 + 41*X^24 + 26*X^23 +
      9*X^22 + 14*X^21 + 24*X^20 + 13*X^19 + 31*X^18 + 42*X^17 + 43*X^16 + 47*X^15 + 62*X^14 +
      46*X^13 + 52*X^12 + 6*X^11 + 9*X^10 + 35*X^9 + 29*X^8 + 3*X^7 + 44*X^6 + 46*X^5 + 29*X^4 +
      42*X^3 + 56*X^2 + 34*X + 21,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s20 : XPow fSeventeenB4 9721
    (66*X^33 + 3*X^32 + 17*X^31 + 43*X^30 + 62*X^29 + 51*X^27 + 15*X^26 + 50*X^25 + 10*X^24 + 30*X^23 +
      28*X^22 + 57*X^21 + 40*X^20 + 8*X^19 + 2*X^18 + 40*X^17 + 38*X^16 + 45*X^15 + 38*X^14 +
      47*X^13 + 2*X^12 + 64*X^11 + 22*X^10 + 44*X^9 + 3*X^8 + 54*X^7 + 10*X^6 + X^5 + 49*X^4 +
      20*X^3 + X^2 + 8*X + 63) :=
  mul_step (by norm_num) pSeventeenB4s19 pSeventeenB41 ⟨
    57,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s21 : XPow fSeventeenB4 19442
    (4*X^33 + 56*X^32 + 15*X^31 + 16*X^30 + 25*X^29 + 28*X^28 + 20*X^27 + 25*X^26 + 64*X^25 + 6*X^24 +
      21*X^23 + 36*X^22 + 48*X^21 + 17*X^20 + 60*X^19 + 9*X^18 + 9*X^17 + 66*X^16 + 23*X^15 +
      40*X^14 + 39*X^13 + 25*X^12 + 53*X^11 + 57*X^10 + 38*X^8 + 6*X^6 + 26*X^5 + 12*X^4 + 37*X^3 +
      52*X^2 + 39*X + 33) :=
  sq_step (by norm_num) pSeventeenB4s20 ⟨
    X^32 + 63*X^31 + 7*X^30 + 60*X^29 + 64*X^28 + 66*X^27 + 49*X^26 + 47*X^25 + 2*X^24 + 33*X^23 +
      20*X^22 + 5*X^21 + 62*X^20 + 22*X^19 + 27*X^18 + 4*X^17 + 16*X^16 + 45*X^15 + 32*X^14 + 9*X^13 +
      11*X^12 + 51*X^11 + 35*X^10 + 42*X^9 + 12*X^8 + 65*X^7 + 28*X^6 + 52*X^5 + 64*X^4 + 26*X^3 +
      18*X^2 + 60*X + 9,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s22 : XPow fSeventeenB4 19443
    (64*X^33 + 41*X^32 + 39*X^31 + 29*X^30 + 52*X^29 + 52*X^28 + 51*X^27 + 18*X^26 + 51*X^25 + 45*X^24 +
      47*X^23 + 44*X^22 + 52*X^21 + 7*X^20 + 6*X^19 + 41*X^18 + 61*X^17 + 17*X^16 + 65*X^15 + 2*X^14 +
      37*X^13 + 43*X^12 + 44*X^11 + 12*X^10 + 10*X^9 + 41*X^8 + 56*X^7 + 29*X^6 + 61*X^5 + 12*X^4 +
      36*X^3 + 61*X^2 + 16*X + 15) :=
  mul_step (by norm_num) pSeventeenB4s21 pSeventeenB41 ⟨
    4,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s23 : XPow fSeventeenB4 38886
    (50*X^33 + 50*X^32 + 64*X^31 + 60*X^30 + 18*X^29 + 51*X^28 + 30*X^27 + 61*X^26 + 45*X^25 + 42*X^24 +
      36*X^23 + 65*X^22 + 48*X^21 + 24*X^20 + 58*X^19 + X^18 + 11*X^16 + 4*X^15 + 50*X^14 + 48*X^13 +
      7*X^12 + 34*X^11 + 46*X^10 + 54*X^9 + 3*X^8 + 36*X^7 + 35*X^6 + 57*X^5 + 59*X^4 + 57*X^3 + 6*X +
      54) :=
  sq_step (by norm_num) pSeventeenB4s22 ⟨
    9*X^32 + 40*X^31 + 11*X^30 + 58*X^29 + 27*X^28 + 52*X^27 + 9*X^26 + 16*X^25 + 18*X^24 + 27*X^23 +
      3*X^22 + 13*X^21 + 64*X^20 + 27*X^19 + 9*X^17 + 45*X^16 + 36*X^15 + 24*X^14 + 15*X^13 +
      58*X^12 + 18*X^11 + 32*X^10 + 60*X^9 + 30*X^8 + 50*X^7 + 59*X^6 + 43*X^5 + 49*X^4 + 33*X^3 +
      39*X^2 + 39*X + 8,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s24 : XPow fSeventeenB4 38887
    (16*X^33 + 54*X^32 + 46*X^31 + X^30 + 16*X^29 + 28*X^28 + 51*X^27 + 6*X^26 + 35*X^25 + X^24 + 35*X^23 +
      65*X^22 + 26*X^21 + 32*X^20 + 64*X^19 + 65*X^18 + 49*X^17 + 63*X^16 + 61*X^15 + 21*X^14 +
      23*X^13 + 43*X^12 + 51*X^11 + 3*X^10 + 55*X^9 + 46*X^8 + 57*X^7 + 61*X^6 + 35*X^5 + 46*X^4 +
      X^3 + 13*X^2 + 9*X + 20) :=
  mul_step (by norm_num) pSeventeenB4s23 pSeventeenB41 ⟨
    50,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s25 : XPow fSeventeenB4 77774
    (8*X^33 + 61*X^32 + 60*X^31 + 66*X^30 + 16*X^29 + 41*X^28 + 4*X^27 + 20*X^26 + 26*X^25 + 40*X^24 +
      13*X^23 + 10*X^22 + 60*X^21 + 12*X^20 + 14*X^19 + 20*X^18 + 19*X^17 + 25*X^16 + 40*X^15 +
      61*X^14 + 17*X^13 + 16*X^12 + 4*X^11 + 26*X^10 + 19*X^9 + 21*X^8 + 59*X^7 + 57*X^6 + 3*X^5 +
      65*X^4 + 24*X^3 + 38*X^2 + 34*X + 12) :=
  sq_step (by norm_num) pSeventeenB4s24 ⟨
    55*X^32 + 29*X^31 + 13*X^30 + 20*X^29 + 17*X^28 + 14*X^27 + 8*X^26 + 38*X^25 + 44*X^24 + 7*X^23 +
      35*X^22 + 39*X^21 + 23*X^20 + 48*X^19 + 37*X^18 + 43*X^17 + 23*X^16 + 10*X^15 + 47*X^14 +
      65*X^13 + 64*X^12 + 47*X^11 + 62*X^10 + 47*X^9 + 63*X^8 + 51*X^7 + 57*X^6 + 20*X^5 + 33*X^4 +
      7*X^3 + 35*X^2 + 51*X + 35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s26 : XPow fSeventeenB4 77775
    (10*X^33 + 45*X^32 + 45*X^31 + 24*X^30 + 22*X^29 + X^28 + 5*X^27 + X^26 + 63*X^25 + 61*X^24 + 32*X^23 +
      52*X^22 + 15*X^21 + 42*X^20 + 14*X^19 + 16*X^18 + 15*X^17 + 28*X^16 + 44*X^15 + 10*X^14 +
      40*X^13 + 51*X^12 + 43*X^10 + 32*X^9 + 7*X^8 + 23*X^7 + 9*X^6 + 29*X^5 + 41*X^4 + 6*X^3 +
      11*X^2 + 45*X + 30) :=
  mul_step (by norm_num) pSeventeenB4s25 pSeventeenB41 ⟨
    8,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s27 : XPow fSeventeenB4 155550
    (24*X^33 + 46*X^32 + 50*X^31 + 5*X^30 + X^29 + 5*X^28 + 41*X^27 + 59*X^26 + 37*X^25 + 17*X^24 +
      42*X^22 + 25*X^21 + 39*X^20 + 43*X^19 + 19*X^18 + 45*X^17 + 32*X^16 + 52*X^15 + 43*X^14 +
      4*X^13 + 5*X^12 + 4*X^11 + 66*X^10 + 22*X^9 + 20*X^8 + 41*X^7 + 51*X^6 + 46*X^5 + 19*X^4 +
      46*X^3 + 55*X^2 + 45*X + 29) :=
  sq_step (by norm_num) pSeventeenB4s26 ⟨
    33*X^32 + 28*X^31 + 13*X^30 + 20*X^29 + 19*X^28 + 56*X^27 + 24*X^26 + 44*X^25 + 29*X^24 + 19*X^23 +
      20*X^22 + X^21 + 49*X^20 + 56*X^19 + 16*X^18 + 7*X^17 + 48*X^16 + 38*X^15 + 39*X^14 + 31*X^13 +
      15*X^12 + 40*X^11 + 22*X^10 + 33*X^9 + 8*X^8 + 58*X^7 + 50*X^6 + 39*X^5 + 25*X^4 + 23*X^3 +
      6*X^2 + 29*X,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s28 : XPow fSeventeenB4 155551
    (27*X^33 + 5*X^32 + 9*X^31 + 25*X^30 + 15*X^29 + 32*X^28 + 14*X^27 + 29*X^26 + 19*X^25 + 10*X^24 +
      41*X^23 + X^22 + 48*X^21 + 60*X^20 + X^19 + 36*X^18 + 2*X^17 + 16*X^16 + 59*X^15 + 50*X^14 +
      10*X^13 + 11*X^12 + 55*X^11 + 27*X^10 + 53*X^9 + 19*X^8 + 16*X^7 + 64*X^6 + 45*X^5 + 30*X^4 +
      26*X^3 + 43*X^2 + 61*X + 23) :=
  mul_step (by norm_num) pSeventeenB4s27 pSeventeenB41 ⟨
    24,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s29 : XPow fSeventeenB4 311102
    (56*X^33 + 24*X^32 + 15*X^31 + 40*X^30 + 6*X^29 + 53*X^28 + 64*X^27 + 53*X^26 + 18*X^25 + 7*X^24 +
      30*X^23 + 22*X^22 + 60*X^21 + 45*X^20 + 55*X^19 + 38*X^18 + 36*X^17 + 35*X^16 + 11*X^15 +
      46*X^14 + 46*X^13 + 9*X^12 + 10*X^11 + 54*X^10 + 53*X^9 + 15*X^8 + 28*X^7 + 34*X^6 + 52*X^5 +
      22*X^4 + 47*X^3 + 2*X^2 + 32*X + 6) :=
  sq_step (by norm_num) pSeventeenB4s28 ⟨
    59*X^32 + 53*X^31 + 29*X^30 + 21*X^29 + 10*X^28 + 60*X^27 + 64*X^26 + 54*X^25 + 8*X^24 + 7*X^23 +
      65*X^22 + 4*X^21 + 23*X^20 + 59*X^19 + 57*X^18 + 22*X^17 + 50*X^16 + 28*X^15 + 43*X^14 +
      13*X^13 + 11*X^12 + 21*X^11 + 17*X^10 + 33*X^9 + 45*X^8 + 41*X^7 + 65*X^6 + 28*X^5 + 46*X^4 +
      35*X^3 + 57*X^2 + 14*X + 66,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s30 : XPow fSeventeenB4 622204
    (40*X^33 + 14*X^32 + 4*X^31 + 45*X^30 + 33*X^29 + X^28 + 63*X^27 + 9*X^26 + 65*X^25 + 57*X^23 +
      6*X^22 + 66*X^21 + 32*X^20 + 58*X^19 + 51*X^18 + 44*X^17 + 5*X^16 + 15*X^15 + 53*X^14 +
      30*X^13 + 30*X^12 + 41*X^11 + 39*X^10 + 33*X^9 + 4*X^8 + 62*X^7 + 38*X^6 + 36*X^5 + 9*X^4 +
      34*X^3 + 20*X^2 + 11*X + 42) :=
  sq_step (by norm_num) pSeventeenB4s29 ⟨
    54*X^32 + 49*X^31 + 25*X^30 + 50*X^29 + 15*X^28 + 38*X^27 + 41*X^26 + 58*X^25 + 12*X^24 + 64*X^23 +
      42*X^22 + 9*X^21 + 58*X^20 + 22*X^19 + 9*X^18 + 15*X^17 + 21*X^16 + 15*X^15 + 26*X^14 +
      36*X^13 + 43*X^12 + 4*X^11 + 5*X^10 + 14*X^9 + 38*X^8 + 38*X^7 + 12*X^6 + 41*X^5 + 43*X^4 +
      59*X^3 + 13*X^2 + 56*X + 15,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s31 : XPow fSeventeenB4 622205
    (27*X^33 + 63*X^32 + 7*X^31 + 6*X^30 + 40*X^29 + 48*X^28 + X^27 + 7*X^26 + 48*X^25 + 29*X^24 +
      49*X^23 + 26*X^22 + 47*X^21 + 64*X^20 + 21*X^19 + 29*X^18 + 22*X^17 + 22*X^16 + 35*X^15 +
      62*X^14 + 16*X^13 + 8*X^12 + 43*X^11 + 19*X^10 + 59*X^9 + 3*X^8 + 2*X^7 + 66*X^6 + 30*X^5 +
      52*X^4 + 61*X^3 + 30*X^2 + 6*X + 16) :=
  mul_step (by norm_num) pSeventeenB4s30 pSeventeenB41 ⟨
    40,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s32 : XPow fSeventeenB4 1244410
    (47*X^33 + 61*X^32 + 4*X^31 + 51*X^30 + 9*X^29 + 8*X^28 + 44*X^27 + 62*X^26 + 14*X^25 + 28*X^24 +
      9*X^23 + 56*X^22 + 29*X^21 + 33*X^20 + 43*X^19 + 18*X^18 + 13*X^17 + 5*X^16 + 20*X^15 +
      14*X^14 + 39*X^12 + 35*X^11 + 43*X^10 + 11*X^9 + 39*X^8 + 51*X^7 + 6*X^6 + 26*X^5 + 20*X^4 +
      22*X^3 + 7*X^2 + 56*X + 5) :=
  sq_step (by norm_num) pSeventeenB4s31 ⟨
    59*X^32 + 36*X^31 + 12*X^30 + 11*X^29 + 48*X^28 + X^27 + 20*X^26 + 53*X^25 + 60*X^24 + X^23 +
      12*X^21 + 28*X^20 + 49*X^19 + 12*X^18 + 9*X^17 + 37*X^16 + 3*X^15 + 60*X^14 + 40*X^13 +
      57*X^12 + 37*X^11 + 13*X^10 + 63*X^9 + 33*X^8 + 45*X^7 + 42*X^6 + 42*X^5 + 11*X^4 + 50*X^3 +
      5*X^2 + 32*X + 9,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s33 : XPow fSeventeenB4 1244411
    (21*X^33 + 8*X^32 + 3*X^31 + 56*X^30 + 22*X^29 + 18*X^28 + 66*X^27 + 43*X^26 + 4*X^25 + 23*X^24 +
      X^23 + 49*X^22 + 59*X^21 + 40*X^20 + 33*X^19 + 54*X^18 + 30*X^17 + 50*X^16 + 23*X^15 + 51*X^14 +
      46*X^13 + 18*X^12 + 41*X^11 + 18*X^10 + 45*X^9 + 47*X^8 + 24*X^7 + 11*X^6 + 43*X^5 + 13*X^4 +
      20*X^3 + 13*X^2 + 23*X + 59) :=
  mul_step (by norm_num) pSeventeenB4s32 pSeventeenB41 ⟨
    47,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s34 : XPow fSeventeenB4 2488822
    (49*X^33 + 29*X^32 + 56*X^31 + 64*X^30 + 60*X^29 + 22*X^28 + 33*X^27 + 51*X^26 + 37*X^25 + 49*X^24 +
      12*X^23 + 31*X^22 + 45*X^21 + 56*X^20 + 16*X^19 + 24*X^18 + 41*X^17 + 9*X^16 + 56*X^15 +
      39*X^14 + 2*X^13 + 62*X^11 + 5*X^10 + 5*X^9 + 16*X^8 + 59*X^7 + 59*X^6 + 2*X^5 + 66*X^4 +
      55*X^3 + 59*X^2 + 62*X + 11) :=
  sq_step (by norm_num) pSeventeenB4s33 ⟨
    39*X^32 + 12*X^31 + 32*X^30 + 36*X^29 + 6*X^28 + 43*X^27 + 41*X^26 + 9*X^25 + 53*X^24 + 28*X^23 +
      15*X^22 + 34*X^21 + 20*X^20 + 45*X^19 + 9*X^18 + 4*X^17 + 63*X^16 + X^15 + 23*X^14 + 21*X^13 +
      33*X^12 + 56*X^11 + 4*X^10 + 4*X^9 + 26*X^8 + 26*X^7 + 18*X^6 + 42*X^5 + 52*X^4 + 38*X^3 +
      15*X^2 + 65*X + 35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s35 : XPow fSeventeenB4 2488823
    (60*X^33 + 6*X^32 + 61*X^31 + 42*X^30 + 48*X^29 + 23*X^28 + X^27 + 43*X^26 + 14*X^25 + 38*X^24 +
      15*X^23 + 63*X^22 + 66*X^21 + 20*X^20 + 4*X^19 + 31*X^18 + 65*X^17 + 16*X^16 + 27*X^15 + X^14 +
      13*X^13 + 40*X^12 + 30*X^11 + 18*X^10 + 8*X^9 + 42*X^8 + 35*X^7 + 22*X^6 + 13*X^5 + 64*X^3 +
      30*X^2 + 54*X + 33) :=
  mul_step (by norm_num) pSeventeenB4s34 pSeventeenB41 ⟨
    49,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s36 : XPow fSeventeenB4 4977646
    (8*X^33 + 51*X^32 + 16*X^31 + 51*X^30 + 62*X^29 + 57*X^28 + 27*X^27 + 56*X^26 + 49*X^25 + 58*X^24 +
      29*X^23 + 35*X^22 + 18*X^21 + 66*X^19 + X^18 + 8*X^17 + 31*X^16 + 21*X^15 + 57*X^14 + 44*X^13 +
      58*X^12 + 52*X^11 + 22*X^10 + 44*X^9 + 35*X^8 + 45*X^7 + 64*X^6 + 28*X^5 + 34*X^4 + 54*X^3 +
      47*X^2 + 61*X + 21) :=
  sq_step (by norm_num) pSeventeenB4s35 ⟨
    49*X^32 + 14*X^31 + 31*X^30 + 26*X^29 + 50*X^28 + 53*X^27 + 25*X^26 + 35*X^25 + 21*X^24 + 30*X^23 +
      8*X^22 + 48*X^21 + 54*X^20 + 66*X^19 + 25*X^18 + 33*X^17 + 33*X^16 + 47*X^15 + 56*X^14 +
      42*X^13 + 60*X^12 + 54*X^11 + 18*X^10 + 66*X^9 + 31*X^8 + 22*X^7 + 40*X^6 + 20*X^5 + 13*X^4 +
      31*X^3 + 62*X^2 + 42*X + 10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s37 : XPow fSeventeenB4 9955292
    (18*X^33 + 48*X^32 + 10*X^31 + 6*X^30 + 59*X^29 + 12*X^28 + X^27 + 41*X^26 + 14*X^25 + 52*X^24 +
      23*X^23 + 28*X^22 + 20*X^21 + 44*X^20 + 53*X^19 + 42*X^18 + 26*X^17 + 62*X^16 + 51*X^15 +
      39*X^14 + 5*X^13 + 26*X^12 + 64*X^11 + 28*X^10 + 54*X^8 + 56*X^7 + 51*X^6 + 62*X^5 + 28*X^4 +
      14*X^3 + 19*X^2 + 33*X + 7) :=
  sq_step (by norm_num) pSeventeenB4s36 ⟨
    64*X^32 + 6*X^31 + 2*X^30 + 45*X^29 + 52*X^28 + 18*X^27 + 4*X^26 + 13*X^25 + 31*X^24 + 2*X^23 +
      28*X^22 + 57*X^21 + 25*X^20 + 38*X^19 + 50*X^18 + 30*X^17 + 50*X^16 + 35*X^15 + X^14 + 53*X^13 +
      8*X^12 + 16*X^11 + 30*X^10 + 49*X^9 + 48*X^8 + 54*X^7 + 16*X^6 + 28*X^5 + 17*X^4 + 60*X^3 +
      9*X^2 + 30*X + 54,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s38 : XPow fSeventeenB4 9955293
    (17*X^33 + 60*X^32 + 9*X^31 + 10*X^30 + 53*X^29 + 11*X^28 + 24*X^27 + 8*X^26 + 20*X^25 + 64*X^24 +
      44*X^23 + 2*X^22 + 34*X^21 + 49*X^20 + 62*X^19 + 36*X^18 + 6*X^17 + 24*X^16 + 51*X^15 + 6*X^14 +
      13*X^13 + 19*X^12 + 3*X^11 + 54*X^10 + 62*X^9 + 6*X^8 + 8*X^7 + 42*X^6 + 14*X^5 + 2*X^4 +
      14*X^3 + 65*X^2 + 31*X + 34) :=
  mul_step (by norm_num) pSeventeenB4s37 pSeventeenB41 ⟨
    18,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s39 : XPow fSeventeenB4 19910586
    (43*X^33 + 13*X^32 + 21*X^31 + 14*X^30 + 54*X^29 + 4*X^28 + 62*X^27 + 7*X^26 + 37*X^24 + 34*X^23 +
      18*X^22 + 37*X^21 + 49*X^20 + 27*X^19 + 25*X^18 + 38*X^17 + 61*X^16 + 66*X^15 + 60*X^14 +
      34*X^13 + 22*X^12 + 60*X^11 + 43*X^10 + 32*X^9 + 33*X^8 + 54*X^7 + 51*X^6 + 49*X^5 + 15*X^4 +
      7*X^3 + 58*X^2 + 54*X + 44) :=
  sq_step (by norm_num) pSeventeenB4s38 ⟨
    21*X^32 + 5*X^31 + 66*X^30 + 47*X^29 + 21*X^28 + 25*X^26 + 58*X^25 + 5*X^24 + 36*X^22 + 33*X^21 +
      30*X^20 + 39*X^19 + 38*X^18 + 24*X^17 + 5*X^16 + 7*X^15 + 27*X^14 + 26*X^13 + 6*X^12 + 10*X^11 +
      22*X^10 + 53*X^9 + 43*X^8 + 16*X^7 + 16*X^6 + 47*X^5 + 12*X^4 + 40*X^3 + 27*X^2 + 34,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s40 : XPow fSeventeenB4 19910587
    (32*X^33 + 66*X^32 + 10*X^31 + 30*X^30 + 61*X^29 + 4*X^28 + 52*X^27 + 8*X^26 + 35*X^25 + 24*X^24 +
      19*X^23 + 61*X^22 + 40*X^21 + 10*X^20 + 43*X^19 + 47*X^18 + 24*X^17 + 35*X^16 + 44*X^15 +
      55*X^14 + 17*X^13 + 53*X^12 + 54*X^11 + 27*X^10 + 9*X^8 + 19*X^7 + 31*X^6 + 56*X^5 + 23*X^4 +
      20*X^3 + 56*X^2 + 12*X + 44) :=
  mul_step (by norm_num) pSeventeenB4s39 pSeventeenB41 ⟨
    43,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s41 : XPow fSeventeenB4 39821174
    (48*X^33 + 53*X^32 + 31*X^31 + 58*X^30 + 66*X^29 + 43*X^28 + 21*X^27 + 44*X^26 + 20*X^25 + 7*X^24 +
      11*X^23 + 35*X^22 + 25*X^21 + 44*X^20 + 49*X^18 + 48*X^17 + 35*X^16 + 2*X^15 + 47*X^14 +
      51*X^13 + 58*X^12 + 11*X^11 + 39*X^10 + 5*X^9 + 44*X^8 + 22*X^7 + 6*X^6 + 61*X^5 + 30*X^4 +
      65*X^3 + 33*X^2 + 38*X + 21) :=
  sq_step (by norm_num) pSeventeenB4s40 ⟨
    19*X^32 + 41*X^31 + 9*X^30 + 66*X^29 + 51*X^28 + 48*X^27 + 21*X^26 + 57*X^25 + 44*X^24 + 64*X^23 +
      46*X^22 + 26*X^21 + 36*X^20 + 26*X^19 + 66*X^18 + 42*X^17 + 27*X^16 + 31*X^15 + X^14 + 49*X^13 +
      22*X^12 + 45*X^11 + 41*X^10 + 4*X^9 + 4*X^8 + 44*X^7 + 24*X^6 + 42*X^5 + 65*X^4 + 19*X^3 +
      4*X^2 + 58*X + 3,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s42 : XPow fSeventeenB4 39821175
    (15*X^33 + 8*X^32 + 66*X^31 + 47*X^30 + 63*X^29 + 3*X^28 + 21*X^27 + 4*X^26 + 11*X^25 + 31*X^24 +
      33*X^23 + 44*X^22 + 62*X^21 + 34*X^20 + 13*X^19 + 30*X^18 + 42*X^17 + 64*X^16 + 12*X^15 +
      9*X^14 + X^13 + 25*X^12 + 17*X^11 + 15*X^10 + 43*X^9 + 45*X^8 + 3*X^7 + 30*X^6 + 15*X^5 +
      33*X^4 + 42*X^3 + 34*X^2 + 18*X + 46) :=
  mul_step (by norm_num) pSeventeenB4s41 pSeventeenB41 ⟨
    48,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s43 : XPow fSeventeenB4 79642350
    (40*X^33 + 66*X^32 + 27*X^31 + 3*X^30 + 38*X^29 + 23*X^28 + 18*X^27 + 50*X^26 + 45*X^25 + 62*X^24 +
      59*X^23 + 55*X^22 + 57*X^21 + 42*X^20 + 23*X^19 + 38*X^18 + 45*X^17 + 61*X^16 + 58*X^15 +
      56*X^14 + X^13 + 7*X^12 + 33*X^11 + 14*X^10 + 35*X^9 + 19*X^8 + 46*X^7 + 44*X^6 + 65*X^5 +
      51*X^4 + 31*X^3 + 5*X^2 + 49*X + 29) :=
  sq_step (by norm_num) pSeventeenB4s42 ⟨
    24*X^32 + 20*X^31 + 29*X^30 + 45*X^29 + 12*X^28 + 60*X^27 + 58*X^26 + 45*X^25 + 21*X^24 + 48*X^23 +
      16*X^22 + 3*X^21 + 4*X^20 + 14*X^19 + 16*X^18 + 27*X^17 + 29*X^16 + 60*X^15 + 27*X^14 +
      21*X^13 + 43*X^12 + 26*X^11 + 26*X^10 + 57*X^9 + 64*X^8 + 64*X^7 + 50*X^6 + 46*X^5 + 55*X^4 +
      35*X^3 + 18*X^2 + 30*X + 42,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s44 : XPow fSeventeenB4 79642351
    (12*X^33 + 19*X^32 + 32*X^31 + 11*X^30 + 62*X^29 + 3*X^28 + 42*X^27 + 54*X^26 + 43*X^25 + 31*X^24 +
      31*X^23 + 17*X^22 + 57*X^21 + 29*X^20 + 8*X^19 + 30*X^18 + 11*X^17 + 65*X^16 + 38*X^15 +
      33*X^14 + 60*X^13 + 18*X^11 + 21*X^10 + 7*X^9 + 54*X^8 + 8*X^7 + 28*X^6 + 5*X^5 + 49*X^4 +
      46*X^3 + X^2 + 60*X + 16) :=
  mul_step (by norm_num) pSeventeenB4s43 pSeventeenB41 ⟨
    40,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s45 : XPow fSeventeenB4 159284702
    (22*X^33 + 11*X^32 + 28*X^30 + 20*X^29 + 18*X^28 + 38*X^27 + 43*X^26 + 13*X^25 + 16*X^24 + 5*X^23 +
      31*X^22 + 58*X^21 + 6*X^20 + 58*X^19 + 2*X^18 + 65*X^17 + 60*X^16 + 27*X^15 + 37*X^14 +
      34*X^13 + 5*X^12 + 22*X^11 + 53*X^10 + 19*X^9 + 7*X^8 + 62*X^7 + 48*X^6 + 47*X^5 + 17*X^4 +
      36*X^3 + 40*X^2 + 55*X + 58) :=
  sq_step (by norm_num) pSeventeenB4s44 ⟨
    10*X^32 + 7*X^31 + 2*X^30 + 46*X^29 + 20*X^28 + 32*X^27 + 65*X^26 + 55*X^25 + 55*X^24 + 44*X^23 +
      43*X^22 + 34*X^21 + 2*X^20 + 39*X^19 + 16*X^18 + 16*X^17 + 2*X^16 + 5*X^15 + 36*X^14 + 33*X^13 +
      27*X^12 + 3*X^11 + 36*X^10 + 20*X^9 + 64*X^8 + 12*X^7 + 65*X^6 + 39*X^5 + 25*X^4 + 64*X^3 +
      X^2 + 36*X + 41,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s46 : XPow fSeventeenB4 318569404
    (51*X^33 + 18*X^32 + 15*X^31 + 17*X^30 + 19*X^29 + 46*X^28 + 57*X^27 + 47*X^26 + 57*X^25 + 14*X^24 +
      34*X^23 + 10*X^22 + 59*X^21 + 57*X^20 + 24*X^19 + 14*X^18 + 6*X^17 + 40*X^16 + 64*X^15 +
      10*X^14 + 30*X^13 + 2*X^12 + 8*X^11 + 35*X^10 + 36*X^9 + 20*X^8 + 39*X^7 + 43*X^6 + 13*X^5 +
      30*X^4 + 23*X^3 + 55*X^2 + 8*X) :=
  sq_step (by norm_num) pSeventeenB4s45 ⟨
    15*X^32 + 45*X^31 + 7*X^30 + 23*X^28 + 63*X^27 + 7*X^26 + 29*X^25 + 23*X^24 + 24*X^23 + 42*X^22 +
      60*X^21 + 62*X^20 + 46*X^19 + 51*X^18 + 54*X^17 + 48*X^16 + 33*X^15 + 66*X^14 + 38*X^13 +
      61*X^12 + 43*X^11 + 45*X^10 + 62*X^9 + 42*X^8 + 50*X^7 + 28*X^6 + 42*X^5 + 43*X^4 + 20*X^3 +
      29*X^2 + 21*X + 32,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s47 : XPow fSeventeenB4 637138808
    (66*X^33 + 63*X^32 + 30*X^31 + 21*X^30 + 61*X^29 + 65*X^28 + 2*X^27 + 11*X^26 + 32*X^25 + 24*X^24 +
      23*X^23 + 6*X^22 + 43*X^21 + 5*X^20 + 28*X^19 + 52*X^18 + 53*X^17 + 2*X^16 + 4*X^15 + 35*X^14 +
      34*X^13 + 28*X^12 + 17*X^11 + 38*X^10 + 34*X^9 + 13*X^8 + 60*X^7 + 65*X^6 + 14*X^5 + 8*X^4 +
      57*X^3 + 58*X^2 + 15*X + 59) :=
  sq_step (by norm_num) pSeventeenB4s46 ⟨
    55*X^32 + 3*X^31 + 40*X^30 + 60*X^29 + 28*X^28 + 61*X^27 + 29*X^26 + 52*X^25 + 37*X^24 + 55*X^23 +
      9*X^22 + 14*X^21 + 9*X^20 + 22*X^19 + 52*X^18 + 42*X^17 + X^16 + 22*X^15 + 2*X^14 + 12*X^13 +
      18*X^12 + 26*X^11 + X^10 + 27*X^9 + 39*X^8 + 64*X^7 + 32*X^6 + 27*X^5 + 47*X^4 + 53*X^3 +
      17*X^2 + 26*X + 47,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s48 : XPow fSeventeenB4 1274277616
    (18*X^33 + 21*X^32 + 29*X^31 + 51*X^30 + 63*X^29 + 22*X^28 + 55*X^27 + 52*X^26 + 51*X^25 + 31*X^24 +
      41*X^23 + 52*X^22 + 32*X^21 + 24*X^20 + 20*X^19 + 47*X^18 + 48*X^17 + 55*X^16 + 60*X^15 +
      25*X^14 + 4*X^13 + 30*X^12 + 39*X^11 + 43*X^9 + 56*X^8 + 19*X^7 + 50*X^6 + 11*X^5 + 52*X^4 +
      30*X^3 + 35*X^2 + 6*X + 15) :=
  sq_step (by norm_num) pSeventeenB4s47 ⟨
    X^32 + 10*X^31 + 16*X^30 + 5*X^29 + 12*X^28 + 36*X^27 + 4*X^26 + 55*X^25 + 51*X^24 + 6*X^23 +
      35*X^22 + 30*X^21 + 9*X^20 + 45*X^19 + 19*X^18 + 64*X^17 + 32*X^16 + X^15 + 44*X^14 + 28*X^13 +
      36*X^12 + 3*X^11 + 46*X^10 + 55*X^9 + 17*X^8 + 2*X^7 + 66*X^6 + 41*X^5 + 33*X^4 + 47*X^3 +
      28*X^2 + 63*X + 45,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s49 : XPow fSeventeenB4 1274277617
    (57*X^33 + 12*X^32 + 54*X^31 + 14*X^30 + 63*X^29 + 65*X^28 + 35*X^27 + 45*X^26 + 66*X^25 + 15*X^24 +
      X^23 + 14*X^22 + 14*X^21 + 16*X^20 + 58*X^18 + 66*X^17 + 33*X^16 + 37*X^15 + 5*X^14 + 17*X^13 +
      61*X^12 + 42*X^11 + 30*X^10 + 64*X^9 + 36*X^8 + 7*X^7 + 58*X^6 + 38*X^5 + 18*X^4 + 30*X^3 +
      38*X^2 + 39*X + 34) :=
  mul_step (by norm_num) pSeventeenB4s48 pSeventeenB41 ⟨
    18,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s50 : XPow fSeventeenB4 2548555234
    (37*X^33 + 20*X^32 + 45*X^31 + 53*X^30 + 27*X^29 + 42*X^26 + 12*X^25 + 24*X^24 + 54*X^23 + 6*X^22 +
      29*X^21 + 3*X^20 + 18*X^19 + 28*X^18 + 12*X^17 + 58*X^16 + 50*X^15 + 21*X^14 + 7*X^13 + 7*X^12 +
      53*X^11 + 39*X^10 + 65*X^9 + 16*X^8 + 22*X^7 + 7*X^6 + 6*X^5 + 25*X^4 + 49*X^3 + 51*X^2 + 3*X +
      27) :=
  sq_step (by norm_num) pSeventeenB4s49 ⟨
    33*X^32 + 27*X^31 + 36*X^30 + 63*X^29 + 11*X^28 + 8*X^27 + 45*X^26 + 41*X^25 + 5*X^24 + 39*X^23 +
      63*X^22 + 16*X^21 + 3*X^20 + 40*X^19 + 39*X^18 + 16*X^17 + 44*X^16 + 26*X^15 + 58*X^14 +
      44*X^13 + 31*X^12 + 56*X^11 + 51*X^10 + 15*X^9 + 35*X^8 + 57*X^7 + 21*X^6 + 50*X^5 + 61*X^4 +
      10*X^3 + 2*X^2 + 50*X + 25,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s51 : XPow fSeventeenB4 2548555235
    (27*X^33 + 51*X^32 + 48*X^31 + 64*X^30 + 21*X^29 + 28*X^28 + 48*X^27 + 22*X^26 + 55*X^25 + 8*X^24 +
      24*X^23 + 59*X^22 + 42*X^21 + 47*X^20 + 17*X^19 + 40*X^18 + 62*X^17 + 28*X^16 + X^15 + 50*X^14 +
      51*X^13 + 61*X^12 + 36*X^11 + 42*X^10 + 25*X^9 + 16*X^8 + 34*X^7 + 17*X^6 + 26*X^5 + 2*X^4 +
      37*X^3 + 39*X^2 + 54*X + 55) :=
  mul_step (by norm_num) pSeventeenB4s50 pSeventeenB41 ⟨
    37,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s52 : XPow fSeventeenB4 5097110470
    (23*X^33 + 59*X^32 + 46*X^31 + 21*X^30 + 3*X^29 + 36*X^28 + 36*X^27 + 36*X^26 + 8*X^25 + 6*X^24 +
      66*X^23 + 63*X^22 + 27*X^21 + 22*X^20 + 26*X^19 + 29*X^18 + 46*X^17 + 14*X^16 + 36*X^15 +
      17*X^14 + 3*X^13 + 56*X^12 + 4*X^11 + 54*X^10 + 64*X^9 + 33*X^8 + 53*X^7 + 7*X^6 + X^5 +
      21*X^4 + 47*X^3 + 44*X^2 + 7*X + 41) :=
  sq_step (by norm_num) pSeventeenB4s51 ⟨
    59*X^32 + 58*X^31 + 31*X^30 + 35*X^29 + 44*X^28 + 34*X^27 + 52*X^26 + 8*X^25 + 58*X^24 + 51*X^23 +
      44*X^22 + 13*X^21 + 55*X^20 + 10*X^19 + 63*X^18 + 7*X^17 + 29*X^16 + 15*X^15 + 6*X^14 +
      14*X^13 + 58*X^12 + 11*X^11 + 51*X^10 + 17*X^9 + 61*X^8 + 26*X^7 + 18*X^6 + 20*X^5 + 45*X^4 +
      5*X^2 + 40*X + 44,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s53 : XPow fSeventeenB4 5097110471
    (38*X^33 + 28*X^32 + 36*X^31 + 26*X^30 + 40*X^29 + 19*X^28 + 18*X^27 + 45*X^26 + 47*X^25 + 3*X^24 +
      9*X^23 + 4*X^22 + 39*X^21 + 6*X^20 + 62*X^19 + 29*X^18 + 2*X^17 + 35*X^16 + 10*X^15 + 8*X^14 +
      58*X^13 + 47*X^12 + 63*X^11 + 66*X^10 + 6*X^9 + 4*X^8 + 60*X^7 + 35*X^6 + 18*X^5 + 54*X^4 +
      19*X^3 + 33*X^2 + 27*X + 36) :=
  mul_step (by norm_num) pSeventeenB4s52 pSeventeenB41 ⟨
    23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s54 : XPow fSeventeenB4 10194220942
    (25*X^33 + 33*X^32 + 39*X^31 + 47*X^30 + 33*X^29 + 2*X^28 + 61*X^27 + 25*X^26 + 5*X^25 + 24*X^24 +
      13*X^23 + 49*X^22 + 58*X^21 + 49*X^20 + 49*X^19 + 27*X^18 + 39*X^17 + 5*X^16 + 60*X^15 +
      29*X^14 + 57*X^13 + 44*X^12 + 40*X^11 + 42*X^10 + 54*X^9 + 18*X^8 + 30*X^6 + 13*X^5 + 52*X^4 +
      57*X^3 + 12*X^2 + X + 35) :=
  sq_step (by norm_num) pSeventeenB4s53 ⟨
    37*X^32 + 58*X^31 + 24*X^30 + 57*X^29 + 34*X^28 + 14*X^27 + 47*X^26 + 50*X^25 + 27*X^24 + 36*X^23 +
      33*X^22 + 59*X^21 + 62*X^20 + 24*X^19 + 46*X^18 + 13*X^17 + 18*X^16 + 32*X^15 + 42*X^14 + X^13 +
      8*X^12 + 25*X^11 + 39*X^10 + 2*X^9 + 35*X^8 + 5*X^7 + 2*X^6 + 38*X^5 + 9*X^4 + 34*X^3 + 5*X^2 +
      34*X + 30,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s55 : XPow fSeventeenB4 20388441884
    (50*X^33 + 42*X^32 + 13*X^31 + 12*X^30 + 27*X^29 + 43*X^28 + 19*X^27 + 17*X^26 + 38*X^25 + 50*X^24 +
      20*X^23 + 56*X^22 + 54*X^21 + 48*X^20 + 38*X^19 + 6*X^18 + 65*X^17 + 31*X^16 + 50*X^15 + X^14 +
      24*X^13 + 32*X^12 + 33*X^11 + 8*X^10 + 43*X^9 + 60*X^8 + 54*X^7 + 63*X^6 + 31*X^5 + 60*X^4 +
      65*X^3 + 65*X^2 + 51*X + 59) :=
  sq_step (by norm_num) pSeventeenB4s54 ⟨
    22*X^32 + 19*X^31 + 4*X^30 + 23*X^29 + 61*X^28 + 58*X^27 + 43*X^26 + 25*X^25 + 23*X^24 + 63*X^23 +
      65*X^22 + 18*X^21 + 24*X^20 + 50*X^19 + 51*X^18 + 43*X^17 + 55*X^16 + 52*X^15 + 5*X^14 +
      61*X^13 + 19*X^12 + 41*X^11 + 24*X^10 + 31*X^9 + 26*X^8 + 63*X^7 + 48*X^6 + 44*X^5 + 28*X^4 +
      22*X^3 + 24*X^2 + 10*X + 33,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s56 : XPow fSeventeenB4 20388441885
    (8*X^33 + 3*X^32 + 65*X^31 + 10*X^30 + 8*X^29 + 17*X^28 + 7*X^27 + 66*X^26 + 43*X^25 + 52*X^24 +
      26*X^23 + 4*X^22 + 50*X^21 + 12*X^20 + 2*X^19 + 63*X^18 + 2*X^17 + 42*X^16 + 12*X^15 + 64*X^14 +
      48*X^13 + 42*X^12 + 13*X^11 + 59*X^10 + 45*X^9 + 64*X^8 + 18*X^7 + 35*X^6 + 36*X^5 + 54*X^4 +
      66*X^3 + 58*X^2 + 14*X + 20) :=
  mul_step (by norm_num) pSeventeenB4s55 pSeventeenB41 ⟨
    50,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s57 : XPow fSeventeenB4 40776883770
    (29*X^33 + 55*X^32 + 35*X^31 + 66*X^30 + 31*X^29 + 55*X^28 + 36*X^27 + 19*X^26 + 37*X^25 + 26*X^24 +
      26*X^23 + 32*X^22 + 66*X^21 + 9*X^20 + 22*X^19 + 62*X^18 + 53*X^17 + 32*X^16 + 30*X^15 +
      25*X^14 + 13*X^13 + 38*X^12 + 33*X^11 + 34*X^10 + 31*X^9 + 25*X^8 + 62*X^7 + 29*X^6 + 66*X^5 +
      59*X^4 + 14*X^3 + 59*X^2 + 40*X + 46) :=
  sq_step (by norm_num) pSeventeenB4s56 ⟨
    64*X^32 + 42*X^31 + 8*X^30 + X^29 + 49*X^28 + 19*X^27 + 26*X^26 + 53*X^25 + 43*X^24 + 16*X^23 +
      59*X^22 + 19*X^21 + 17*X^20 + 58*X^19 + 5*X^18 + 36*X^17 + 66*X^16 + 20*X^15 + 26*X^14 +
      40*X^13 + 16*X^12 + 31*X^11 + 47*X^10 + 19*X^9 + 58*X^8 + 26*X^7 + 29*X^6 + 13*X^5 + 59*X^4 +
      13*X^3 + 7*X^2 + 42*X + 53,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s58 : XPow fSeventeenB4 81553767540
    (52*X^33 + 65*X^32 + 7*X^31 + 43*X^30 + 36*X^29 + 23*X^28 + 28*X^27 + 53*X^26 + 55*X^25 + 61*X^24 +
      8*X^23 + 15*X^22 + 24*X^21 + 10*X^20 + 14*X^19 + 27*X^18 + 45*X^17 + 61*X^16 + 38*X^15 +
      28*X^14 + 28*X^13 + 22*X^12 + 13*X^11 + 26*X^10 + 6*X^9 + 12*X^8 + 16*X^7 + 9*X^6 + 11*X^5 +
      8*X^4 + 36*X^3 + 47*X^2 + 58*X + 40) :=
  sq_step (by norm_num) pSeventeenB4s57 ⟨
    37*X^32 + 48*X^31 + 65*X^30 + 8*X^29 + 13*X^28 + 66*X^27 + 65*X^26 + 4*X^25 + 7*X^24 + 66*X^23 +
      11*X^22 + 40*X^21 + 16*X^20 + 39*X^19 + 21*X^18 + 34*X^17 + 29*X^16 + X^15 + 11*X^14 + 44*X^13 +
      59*X^12 + 58*X^11 + 55*X^10 + 18*X^9 + 57*X^8 + 20*X^7 + 30*X^6 + 45*X^5 + 51*X^4 + 12*X^3 +
      51*X^2 + 4*X + 36,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s59 : XPow fSeventeenB4 81553767541
    (35*X^33 + 10*X^32 + 7*X^31 + 21*X^30 + 42*X^28 + 56*X^27 + 60*X^26 + 43*X^25 + 52*X^24 + 24*X^23 +
      39*X^22 + 63*X^21 + 62*X^20 + 55*X^19 + 59*X^18 + 63*X^17 + 27*X^16 + 18*X^15 + 16*X^14 +
      44*X^13 + 17*X^12 + 58*X^11 + 28*X^10 + 50*X^9 + 13*X^8 + 56*X^7 + 50*X^6 + 42*X^5 + 46*X^4 +
      40*X^3 + 9*X^2 + 20*X + 61) :=
  mul_step (by norm_num) pSeventeenB4s58 pSeventeenB41 ⟨
    52,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s60 : XPow fSeventeenB4 163107535082
    (49*X^33 + 17*X^32 + 46*X^31 + 62*X^30 + 15*X^29 + 6*X^28 + 57*X^27 + 29*X^26 + 12*X^25 + 37*X^24 +
      54*X^23 + 10*X^22 + 28*X^21 + 23*X^20 + 14*X^19 + 10*X^18 + 19*X^17 + 44*X^16 + 54*X^15 +
      19*X^14 + 14*X^13 + 58*X^12 + 50*X^11 + 17*X^10 + 63*X^9 + 4*X^8 + 5*X^7 + 57*X^6 + 53*X^5 +
      47*X^4 + 50*X^3 + X^2 + 51*X + 19) :=
  sq_step (by norm_num) pSeventeenB4s59 ⟨
    19*X^32 + X^31 + 12*X^30 + 58*X^29 + X^28 + 45*X^27 + 39*X^26 + 30*X^25 + 9*X^24 + 47*X^23 + 53*X^22 +
      13*X^21 + 61*X^20 + 56*X^19 + 7*X^18 + 57*X^17 + 31*X^16 + 59*X^15 + 28*X^14 + 64*X^13 +
      24*X^12 + 26*X^11 + 50*X^10 + 30*X^9 + 43*X^8 + 39*X^7 + 50*X^6 + 36*X^5 + 28*X^4 + 61*X^3 +
      37*X^2 + 54*X + 58,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s61 : XPow fSeventeenB4 326215070164
    (44*X^33 + 42*X^32 + 40*X^31 + 18*X^30 + 25*X^29 + 24*X^28 + 64*X^27 + 66*X^26 + 32*X^25 + 7*X^24 +
      13*X^23 + 54*X^22 + 19*X^21 + 61*X^20 + 64*X^19 + 61*X^18 + 16*X^17 + 57*X^16 + 9*X^15 +
      7*X^14 + 34*X^13 + 8*X^12 + 55*X^11 + 36*X^10 + 8*X^9 + 33*X^8 + 65*X^7 + 57*X^6 + 60*X^5 +
      48*X^4 + 12*X^3 + 26*X^2 + 41*X + 27) :=
  sq_step (by norm_num) pSeventeenB4s60 ⟨
    56*X^32 + 36*X^31 + 7*X^30 + 36*X^29 + 11*X^28 + 50*X^27 + 37*X^26 + 26*X^25 + 51*X^24 + 41*X^23 +
      38*X^22 + 66*X^21 + 62*X^20 + 35*X^19 + 66*X^18 + 7*X^17 + 62*X^16 + 62*X^15 + 55*X^14 +
      59*X^13 + 65*X^12 + 24*X^11 + 14*X^10 + 35*X^9 + 56*X^8 + 19*X^7 + 10*X^6 + 27*X^5 + 7*X^4 +
      39*X^3 + 13*X^2 + 62*X + 36,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s62 : XPow fSeventeenB4 652430140328
    (16*X^33 + 6*X^32 + 39*X^31 + 62*X^30 + 29*X^29 + 36*X^28 + 54*X^27 + 12*X^26 + 44*X^25 + 15*X^24 +
      34*X^23 + 56*X^22 + 7*X^21 + 49*X^20 + 22*X^19 + 39*X^18 + 13*X^17 + 31*X^16 + 56*X^15 +
      27*X^14 + 57*X^13 + 63*X^12 + 11*X^11 + 22*X^10 + 39*X^9 + X^7 + 11*X^6 + 47*X^5 + 40*X^4 +
      26*X^3 + 8*X^2 + 20*X + 45) :=
  sq_step (by norm_num) pSeventeenB4s61 ⟨
    60*X^32 + 64*X^31 + 40*X^30 + 23*X^29 + 16*X^28 + 22*X^27 + 51*X^26 + 29*X^25 + 7*X^24 + 3*X^23 +
      X^22 + 13*X^21 + 56*X^20 + 66*X^19 + 18*X^18 + X^17 + 17*X^16 + 29*X^15 + 18*X^14 + 59*X^13 +
      10*X^12 + 52*X^11 + 4*X^10 + 8*X^9 + 42*X^8 + 28*X^7 + 42*X^6 + 62*X^5 + 12*X^4 + 23*X^3 +
      6*X^2 + 14*X + 32,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s63 : XPow fSeventeenB4 652430140329
    (38*X^33 + 9*X^32 + 20*X^31 + 45*X^30 + 65*X^29 + 48*X^28 + 49*X^27 + 61*X^26 + 61*X^25 + 63*X^24 +
      33*X^23 + 58*X^22 + 55*X^21 + 11*X^20 + 27*X^19 + 7*X^18 + 11*X^17 + 32*X^16 + 60*X^15 +
      43*X^14 + 44*X^13 + 38*X^12 + 37*X^11 + 20*X^10 + 22*X^9 + 31*X^8 + 10*X^7 + 59*X^6 + 35*X^5 +
      60*X^4 + 11*X^3 + 41*X^2 + 44*X + 60) :=
  mul_step (by norm_num) pSeventeenB4s62 pSeventeenB41 ⟨
    16,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s64 : XPow fSeventeenB4 1304860280658
    (46*X^33 + 65*X^32 + 27*X^31 + 27*X^30 + 21*X^29 + 17*X^28 + 16*X^27 + 24*X^26 + 44*X^25 + 46*X^24 +
      65*X^23 + 40*X^22 + 35*X^21 + 16*X^20 + 21*X^19 + 37*X^18 + 60*X^17 + 56*X^16 + 49*X^15 +
      43*X^14 + 57*X^13 + 18*X^12 + 31*X^11 + 19*X^10 + 32*X^9 + 20*X^8 + 59*X^7 + 18*X^6 + 45*X^5 +
      24*X^4 + 5*X^3 + 25*X^2 + 42*X + 46) :=
  sq_step (by norm_num) pSeventeenB4s63 ⟨
    37*X^32 + 21*X^31 + 41*X^30 + 7*X^29 + 39*X^28 + X^27 + 39*X^26 + 4*X^25 + 27*X^24 + 13*X^23 +
      6*X^22 + 55*X^21 + 31*X^20 + 12*X^19 + 44*X^18 + 6*X^17 + 28*X^16 + 7*X^15 + 53*X^14 + 59*X^13 +
      24*X^12 + 8*X^11 + 21*X^10 + 39*X^9 + 12*X^8 + 50*X^7 + 8*X^6 + 30*X^5 + 43*X^4 + 18*X^3 +
      24*X^2 + 62*X + 26,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s65 : XPow fSeventeenB4 2609720561316
    (18*X^33 + 28*X^32 + 61*X^31 + 32*X^30 + 58*X^29 + 66*X^28 + 16*X^27 + 25*X^26 + 6*X^25 + 31*X^24 +
      45*X^23 + 21*X^22 + 23*X^21 + 39*X^20 + 32*X^19 + 31*X^18 + 3*X^17 + 15*X^16 + 11*X^15 +
      27*X^14 + 23*X^13 + 47*X^12 + 34*X^11 + 41*X^10 + 3*X^9 + 28*X^8 + 5*X^7 + 21*X^6 + 45*X^5 +
      41*X^4 + 34*X^3 + 33*X^2 + 31*X + 21) :=
  sq_step (by norm_num) pSeventeenB4s64 ⟨
    39*X^32 + 28*X^31 + 17*X^30 + 19*X^29 + 54*X^28 + 62*X^27 + 10*X^26 + 34*X^25 + 2*X^24 + 55*X^23 +
      12*X^22 + 24*X^21 + 41*X^20 + 50*X^19 + 47*X^18 + 32*X^16 + 35*X^15 + 15*X^14 + X^13 + 40*X^12 +
      12*X^11 + 39*X^9 + 37*X^8 + 62*X^7 + 19*X^6 + 48*X^5 + 34*X^4 + 15*X^3 + 46*X^2 + 48*X + 22,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s66 : XPow fSeventeenB4 2609720561317
    (64*X^33 + 44*X^32 + 35*X^31 + 9*X^30 + 40*X^29 + 26*X^28 + 8*X^27 + 66*X^25 + 19*X^24 + 37*X^23 +
      5*X^22 + 29*X^21 + 28*X^20 + 51*X^19 + 13*X^18 + 26*X^17 + 51*X^16 + 39*X^15 + 24*X^14 +
      34*X^13 + 56*X^12 + 16*X^11 + 57*X^10 + 36*X^9 + 22*X^8 + 45*X^7 + 25*X^6 + 27*X^5 + 22*X^4 +
      28*X^3 + 63*X^2 + 45*X + 34) :=
  mul_step (by norm_num) pSeventeenB4s65 pSeventeenB41 ⟨
    18,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s67 : XPow fSeventeenB4 5219441122634
    (44*X^33 + 2*X^32 + 54*X^31 + 37*X^30 + 64*X^29 + 55*X^28 + 11*X^27 + 15*X^26 + 17*X^25 + 11*X^24 +
      60*X^23 + 38*X^22 + 52*X^21 + 41*X^20 + 64*X^19 + 35*X^18 + 3*X^17 + 54*X^16 + 3*X^15 +
      25*X^14 + 52*X^13 + 4*X^12 + 24*X^11 + 19*X^10 + 42*X^9 + 15*X^8 + 50*X^6 + 60*X^5 + 4*X^4 +
      21*X^3 + 38*X^2 + 57*X + 25) :=
  sq_step (by norm_num) pSeventeenB4s66 ⟨
    9*X^32 + 22*X^31 + 53*X^30 + 27*X^29 + 33*X^28 + 10*X^27 + 56*X^26 + 53*X^25 + X^24 + 41*X^23 +
      37*X^22 + 11*X^21 + 49*X^20 + 6*X^19 + 39*X^18 + 9*X^17 + 25*X^16 + 43*X^15 + 61*X^14 +
      59*X^12 + 26*X^11 + 7*X^10 + 43*X^9 + 56*X^8 + 36*X^7 + 8*X^6 + 5*X^5 + 55*X^4 + 52*X^3 +
      45*X^2 + 8*X + 20,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s68 : XPow fSeventeenB4 10438882245268
    (40*X^33 + 15*X^32 + 8*X^31 + 30*X^30 + 54*X^28 + 58*X^27 + 53*X^26 + 17*X^25 + 56*X^23 + 18*X^22 +
      57*X^21 + 10*X^20 + 29*X^19 + 32*X^18 + 35*X^17 + 22*X^16 + 49*X^15 + 18*X^14 + 29*X^13 +
      32*X^12 + 11*X^11 + 57*X^10 + 32*X^9 + 34*X^8 + 43*X^7 + 64*X^6 + 54*X^5 + 51*X^4 + 2*X^3 +
      49*X^2 + 26*X + 52) :=
  sq_step (by norm_num) pSeventeenB4s67 ⟨
    60*X^32 + 28*X^31 + 43*X^30 + 65*X^29 + 47*X^28 + 43*X^27 + 21*X^26 + 18*X^25 + 62*X^24 + 38*X^23 +
      38*X^22 + 66*X^21 + 12*X^20 + 45*X^19 + 24*X^18 + 40*X^17 + 34*X^16 + 57*X^15 + 46*X^14 +
      35*X^13 + 13*X^12 + 51*X^11 + 39*X^10 + 22*X^9 + 51*X^8 + 19*X^7 + 48*X^6 + 57*X^5 + 18*X^4 +
      37*X^3 + 5*X^2 + 60*X + 8,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s69 : XPow fSeventeenB4 20877764490536
    (28*X^33 + 28*X^32 + 23*X^31 + 34*X^30 + 37*X^29 + 52*X^27 + 5*X^26 + 7*X^25 + 47*X^24 + 41*X^23 +
      15*X^22 + 3*X^20 + 44*X^19 + 39*X^18 + 23*X^17 + 10*X^16 + 59*X^15 + 23*X^14 + 59*X^13 +
      66*X^12 + 25*X^11 + 31*X^10 + 46*X^9 + 35*X^8 + 63*X^7 + 62*X^6 + 58*X^5 + 14*X^4 + 51*X^3 +
      64*X^2 + 52*X + 35) :=
  sq_step (by norm_num) pSeventeenB4s68 ⟨
    59*X^32 + 45*X^31 + 32*X^30 + 36*X^29 + 4*X^28 + 64*X^27 + 54*X^26 + 21*X^25 + 63*X^24 + 61*X^23 +
      29*X^21 + 27*X^20 + 8*X^18 + 58*X^17 + 16*X^16 + 29*X^15 + 43*X^14 + 59*X^13 + 2*X^12 +
      60*X^11 + 2*X^10 + 39*X^9 + 45*X^8 + 61*X^7 + 52*X^6 + 2*X^5 + 3*X^4 + 54*X^3 + 18*X^2 + 23*X +
      61,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s70 : XPow fSeventeenB4 20877764490537
    (17*X^33 + 4*X^32 + 61*X^31 + 65*X^30 + 34*X^29 + 8*X^28 + 53*X^27 + 20*X^26 + 27*X^25 + 8*X^24 +
      25*X^23 + 39*X^22 + 47*X^21 + 8*X^20 + 18*X^19 + 46*X^18 + 42*X^17 + 17*X^16 + 64*X^15 + X^14 +
      16*X^13 + 22*X^12 + 7*X^11 + 63*X^10 + 40*X^9 + 15*X^8 + 10*X^7 + 12*X^6 + 22*X^5 + 10*X^4 +
      19*X^3 + 5*X^2 + 50*X + 38) :=
  mul_step (by norm_num) pSeventeenB4s69 pSeventeenB41 ⟨
    28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s71 : XPow fSeventeenB4 41755528981074
    (20*X^33 + 34*X^32 + 10*X^31 + 4*X^30 + 10*X^29 + 2*X^28 + 56*X^27 + 29*X^26 + 64*X^25 + 14*X^24 +
      2*X^23 + X^22 + 42*X^21 + 13*X^20 + 10*X^19 + 6*X^18 + 60*X^17 + X^16 + 11*X^15 + 25*X^14 +
      63*X^13 + 16*X^12 + 23*X^11 + 19*X^10 + 21*X^9 + 54*X^8 + 3*X^7 + 32*X^6 + 13*X^5 + 47*X^4 +
      61*X^3 + 12*X^2 + 32*X + 61) :=
  sq_step (by norm_num) pSeventeenB4s70 ⟨
    21*X^32 + 44*X^31 + 3*X^30 + 12*X^29 + 53*X^28 + 18*X^27 + 35*X^26 + 23*X^25 + 26*X^24 + 59*X^23 +
      50*X^22 + 10*X^21 + 45*X^20 + 47*X^19 + 24*X^18 + 44*X^17 + 66*X^16 + 11*X^15 + 14*X^14 +
      6*X^13 + 55*X^12 + 36*X^11 + 31*X^10 + 23*X^9 + 52*X^8 + 66*X^7 + 54*X^6 + 33*X^4 + 5*X^3 +
      41*X^2 + 28*X + 60,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s72 : XPow fSeventeenB4 83511057962148
    (11*X^33 + 57*X^32 + 13*X^31 + 22*X^30 + 32*X^29 + 8*X^28 + 29*X^27 + 48*X^26 + 26*X^25 + 32*X^24 +
      27*X^23 + 36*X^22 + 24*X^20 + 35*X^19 + 24*X^18 + 43*X^17 + 5*X^16 + 15*X^15 + 13*X^14 +
      62*X^13 + 21*X^12 + 6*X^11 + 31*X^10 + 27*X^9 + 38*X^8 + 7*X^6 + 18*X^5 + 43*X^4 + 56*X^3 +
      11*X^2 + 4*X + 9) :=
  sq_step (by norm_num) pSeventeenB4s71 ⟨
    65*X^32 + 16*X^31 + 34*X^30 + 29*X^29 + 2*X^28 + 26*X^27 + 40*X^26 + 35*X^25 + 22*X^24 + 66*X^23 +
      17*X^22 + 49*X^21 + 3*X^20 + 56*X^19 + 33*X^18 + 2*X^17 + 63*X^16 + 25*X^15 + 60*X^14 +
      63*X^13 + 25*X^12 + 19*X^11 + 40*X^10 + 21*X^9 + 51*X^8 + 32*X^7 + 23*X^6 + 37*X^5 + 16*X^4 +
      27*X^3 + 29*X^2 + 56*X + 33,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s73 : XPow fSeventeenB4 167022115924296
    (48*X^33 + 52*X^32 + 14*X^31 + 27*X^30 + 32*X^29 + 6*X^28 + 19*X^27 + 10*X^26 + 50*X^25 + 35*X^24 +
      59*X^23 + 4*X^21 + 25*X^20 + 26*X^19 + 26*X^18 + 6*X^17 + 35*X^16 + 34*X^15 + 35*X^14 + 3*X^13 +
      57*X^12 + 28*X^11 + 36*X^10 + 7*X^9 + 30*X^8 + 47*X^7 + 29*X^6 + 55*X^5 + 28*X^4 + 47*X^3 +
      61*X^2 + 33*X + 15) :=
  sq_step (by norm_num) pSeventeenB4s72 ⟨
    54*X^32 + 22*X^31 + 44*X^30 + 62*X^29 + 52*X^28 + 8*X^27 + 64*X^26 + 7*X^25 + 37*X^24 + 5*X^23 +
      3*X^22 + 20*X^21 + 19*X^20 + 20*X^19 + 43*X^18 + 44*X^17 + 19*X^16 + 38*X^15 + 29*X^14 +
      46*X^13 + 63*X^12 + 39*X^11 + 29*X^10 + 2*X^9 + 55*X^8 + 45*X^7 + 34*X^6 + 59*X^5 + 48*X^4 +
      50*X^3 + 15*X^2 + 17*X + 36,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s74 : XPow fSeventeenB4 334044231848592
    (6*X^33 + 44*X^32 + 46*X^31 + 35*X^30 + 43*X^29 + X^28 + 4*X^27 + 48*X^26 + 33*X^25 + 12*X^24 +
      14*X^23 + 20*X^22 + 29*X^21 + 39*X^20 + 6*X^19 + 54*X^18 + 36*X^17 + 22*X^16 + 21*X^15 +
      46*X^14 + 15*X^13 + 26*X^12 + 10*X^11 + 16*X^10 + 15*X^9 + 34*X^8 + 36*X^7 + 46*X^6 + 55*X^5 +
      12*X^4 + 21*X^3 + 28*X^2 + 33*X + 63) :=
  sq_step (by norm_num) pSeventeenB4s73 ⟨
    26*X^32 + 19*X^31 + 34*X^30 + 34*X^29 + 18*X^28 + 28*X^27 + 7*X^26 + 29*X^25 + 62*X^24 + 33*X^23 +
      16*X^22 + 17*X^21 + 4*X^20 + 16*X^19 + 19*X^18 + 4*X^17 + 26*X^16 + 30*X^15 + 4*X^14 + 27*X^13 +
      14*X^12 + 30*X^11 + 66*X^10 + 7*X^9 + 53*X^8 + 51*X^7 + 34*X^6 + 6*X^5 + 22*X^4 + 42*X^3 +
      24*X^2 + 63*X + 64,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s75 : XPow fSeventeenB4 668088463697184
    (25*X^33 + 44*X^32 + 43*X^31 + 19*X^30 + 34*X^28 + 54*X^27 + 41*X^26 + 25*X^25 + 11*X^24 + 54*X^23 +
      33*X^22 + 35*X^21 + 14*X^20 + 4*X^18 + 11*X^17 + 25*X^16 + 42*X^15 + 46*X^14 + 43*X^13 +
      11*X^12 + 40*X^11 + 51*X^10 + 34*X^9 + 28*X^8 + 65*X^7 + 31*X^6 + 17*X^5 + 19*X^4 + X^3 +
      10*X^2 + 29*X) :=
  sq_step (by norm_num) pSeventeenB4s74 ⟨
    36*X^32 + 64*X^31 + 36*X^30 + 4*X^29 + 60*X^28 + 11*X^27 + 28*X^26 + 8*X^25 + 55*X^24 + 17*X^23 +
      44*X^22 + 28*X^21 + 47*X^20 + 20*X^19 + 19*X^18 + 39*X^17 + 56*X^16 + 45*X^15 + 45*X^14 +
      6*X^13 + 21*X^12 + 36*X^11 + 45*X^10 + 20*X^9 + 13*X^8 + 7*X^7 + 60*X^6 + 58*X^5 + 63*X^4 +
      53*X^3 + 34*X^2 + 6*X + 27,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s76 : XPow fSeventeenB4 1336176927394368
    (25*X^33 + 57*X^32 + 7*X^31 + 15*X^30 + 52*X^29 + 56*X^28 + 43*X^27 + 55*X^26 + 49*X^25 + 49*X^24 +
      10*X^23 + 46*X^22 + 41*X^21 + 57*X^20 + 40*X^19 + 51*X^18 + 63*X^17 + 62*X^16 + 33*X^15 +
      59*X^14 + 44*X^13 + 22*X^12 + 24*X^11 + 32*X^10 + 44*X^9 + 54*X^8 + 64*X^7 + 24*X^6 + 40*X^5 +
      38*X^4 + 20*X^3 + 28*X^2 + 31*X + 47) :=
  sq_step (by norm_num) pSeventeenB4s75 ⟨
    22*X^32 + 33*X^31 + 7*X^30 + 64*X^29 + 37*X^28 + 26*X^27 + 26*X^26 + 3*X^25 + 33*X^24 + 24*X^23 +
      45*X^22 + 52*X^21 + 21*X^20 + 33*X^19 + 38*X^18 + 56*X^17 + 34*X^16 + 44*X^15 + X^14 + 18*X^13 +
      44*X^12 + X^11 + 2*X^10 + 24*X^9 + 28*X^8 + 40*X^7 + 65*X^6 + 49*X^5 + 54*X^4 + 5*X^3 + 32*X +
      17,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s77 : XPow fSeventeenB4 2672353854788736
    (28*X^33 + 46*X^32 + 6*X^31 + 28*X^30 + 48*X^29 + 30*X^28 + 61*X^27 + 35*X^26 + 39*X^25 + 11*X^24 +
      33*X^23 + 57*X^22 + X^21 + 19*X^20 + 51*X^19 + 29*X^18 + 47*X^17 + 33*X^16 + 64*X^15 + 58*X^14 +
      38*X^13 + 24*X^12 + 21*X^11 + 45*X^10 + 36*X^9 + 20*X^8 + 32*X^7 + 50*X^6 + 32*X^5 + 45*X^4 +
      49*X^3 + 39*X^2 + 53*X + 36) :=
  sq_step (by norm_num) pSeventeenB4s76 ⟨
    22*X^32 + 13*X^31 + 16*X^30 + 49*X^29 + 18*X^28 + 49*X^27 + 53*X^26 + 62*X^25 + 38*X^24 + 18*X^23 +
      36*X^22 + 65*X^21 + 30*X^20 + 20*X^19 + 42*X^18 + 5*X^17 + 62*X^16 + 18*X^15 + 24*X^14 +
      44*X^13 + 43*X^12 + 40*X^11 + 41*X^10 + 38*X^9 + 16*X^8 + 16*X^7 + 40*X^6 + 26*X^5 + 25*X^4 +
      46*X^3 + 46*X^2 + 46*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s78 : XPow fSeventeenB4 5344707709577472
    (52*X^33 + 19*X^32 + 33*X^31 + 61*X^30 + 17*X^29 + 10*X^28 + 55*X^27 + 16*X^26 + 24*X^25 + 11*X^24 +
      26*X^23 + 26*X^22 + 41*X^21 + 48*X^20 + 40*X^19 + 55*X^18 + 59*X^17 + 49*X^16 + 63*X^15 +
      45*X^14 + 21*X^13 + 24*X^12 + 46*X^11 + 34*X^10 + 30*X^9 + 43*X^8 + 19*X^7 + 29*X^6 + 31*X^5 +
      40*X^4 + 12*X^3 + 2*X^2 + 15*X + 64) :=
  sq_step (by norm_num) pSeventeenB4s77 ⟨
    47*X^32 + 57*X^31 + 24*X^30 + 45*X^29 + 8*X^28 + 15*X^27 + 26*X^26 + 41*X^25 + 54*X^24 + 54*X^23 +
      23*X^22 + 64*X^21 + 17*X^20 + 19*X^19 + 13*X^18 + 21*X^17 + 11*X^16 + 11*X^15 + 7*X^14 +
      28*X^13 + 51*X^12 + 61*X^11 + 9*X^10 + 37*X^9 + 30*X^8 + 7*X^7 + 47*X^6 + 32*X^5 + 11*X^4 +
      13*X^3 + 41*X^2 + 16*X + 2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s79 : XPow fSeventeenB4 5344707709577473
    (56*X^33 + 36*X^32 + 25*X^31 + 2*X^30 + 54*X^29 + 2*X^28 + 19*X^27 + 29*X^26 + 60*X^25 + 3*X^24 +
      35*X^23 + 56*X^22 + 34*X^21 + 21*X^20 + 16*X^19 + 6*X^18 + 51*X^17 + 52*X^16 + 35*X^15 +
      9*X^14 + 46*X^13 + 50*X^12 + 66*X^11 + 52*X^10 + 14*X^9 + 16*X^8 + 9*X^7 + 3*X^6 + 7*X^5 +
      22*X^4 + 62*X^3 + 33*X^2 + 44*X + 61) :=
  mul_step (by norm_num) pSeventeenB4s78 pSeventeenB41 ⟨
    52,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s80 : XPow fSeventeenB4 10689415419154946
    (66*X^33 + 22*X^32 + 14*X^31 + 48*X^30 + 42*X^29 + 29*X^28 + 16*X^27 + 59*X^26 + 12*X^25 + 56*X^24 +
      14*X^23 + 13*X^22 + X^21 + 11*X^20 + 28*X^19 + 25*X^18 + 56*X^17 + 56*X^16 + 48*X^15 + 21*X^14 +
      27*X^13 + 51*X^12 + 43*X^11 + 34*X^9 + 30*X^8 + 39*X^7 + 13*X^6 + 50*X^4 + 52*X^3 + 48*X^2 +
      14*X + 61) :=
  sq_step (by norm_num) pSeventeenB4s79 ⟨
    54*X^32 + 53*X^31 + 64*X^30 + 60*X^29 + 57*X^28 + 34*X^27 + 41*X^26 + 65*X^25 + 24*X^24 + 16*X^23 +
      23*X^22 + 58*X^21 + 41*X^19 + 9*X^18 + 5*X^17 + 37*X^16 + 55*X^15 + 61*X^14 + 46*X^13 +
      14*X^12 + 49*X^11 + 36*X^10 + 34*X^9 + 30*X^8 + 55*X^7 + 3*X^6 + 65*X^5 + 3*X^4 + 38*X^3 +
      9*X^2 + 30*X + 29,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s81 : XPow fSeventeenB4 10689415419154947
    (20*X^33 + 41*X^32 + 59*X^31 + 41*X^30 + 23*X^29 + 8*X^28 + 19*X^27 + 57*X^26 + 28*X^25 + 8*X^24 +
      27*X^23 + 2*X^22 + 19*X^21 + 58*X^20 + 9*X^19 + 48*X^18 + 7*X^17 + 16*X^16 + 65*X^15 + 53*X^14 +
      48*X^13 + 12*X^12 + 20*X^11 + 31*X^10 + 37*X^9 + 12*X^8 + 34*X^7 + 16*X^6 + 21*X^5 + 8*X^4 +
      52*X^3 + 42*X^2 + 15*X + 13) :=
  mul_step (by norm_num) pSeventeenB4s80 pSeventeenB41 ⟨
    66,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s82 : XPow fSeventeenB4 21378830838309894
    (31*X^33 + 21*X^32 + 38*X^31 + 26*X^30 + 36*X^29 + 55*X^28 + 29*X^26 + 3*X^25 + 20*X^24 + 36*X^23 +
      39*X^22 + 31*X^21 + 36*X^20 + 65*X^19 + 28*X^18 + 5*X^17 + 35*X^16 + 45*X^15 + 44*X^14 +
      45*X^13 + 60*X^12 + 60*X^11 + 53*X^10 + 36*X^9 + 39*X^8 + 35*X^7 + 38*X^6 + 29*X^5 + 45*X^4 +
      51*X^3 + 51*X^2 + 29*X + 54) :=
  sq_step (by norm_num) pSeventeenB4s81 ⟨
    65*X^32 + 28*X^31 + 64*X^30 + 43*X^29 + 49*X^28 + 10*X^26 + 20*X^25 + 32*X^24 + 35*X^23 + 4*X^22 +
      18*X^21 + 65*X^20 + 34*X^19 + 13*X^18 + 14*X^17 + 10*X^16 + 54*X^15 + 13*X^14 + 32*X^13 +
      54*X^12 + 62*X^11 + 59*X^10 + 57*X^9 + 14*X^8 + 16*X^7 + 39*X^6 + 31*X^5 + 15*X^4 + 27*X^3 +
      26*X^2 + 14,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s83 : XPow fSeventeenB4 42757661676619788
    (65*X^33 + 55*X^32 + 5*X^31 + 66*X^30 + 52*X^29 + 18*X^28 + 13*X^27 + X^26 + 40*X^25 + 7*X^24 +
      2*X^23 + 37*X^22 + 45*X^21 + 39*X^20 + 43*X^19 + 53*X^18 + 35*X^17 + 37*X^16 + 2*X^15 +
      53*X^14 + 38*X^13 + 2*X^12 + 16*X^11 + 65*X^10 + 45*X^9 + 37*X^8 + 31*X^6 + 19*X^5 + 66*X^4 +
      5*X^3 + 34*X^2 + 56*X + 6) :=
  sq_step (by norm_num) pSeventeenB4s82 ⟨
    23*X^32 + 8*X^31 + 48*X^30 + 21*X^29 + 32*X^28 + 50*X^27 + 49*X^26 + 35*X^25 + 33*X^24 + 16*X^23 +
      5*X^22 + 65*X^21 + 35*X^20 + 52*X^19 + 56*X^18 + 53*X^17 + 13*X^16 + 65*X^15 + 60*X^14 +
      46*X^13 + 37*X^12 + 3*X^11 + 54*X^10 + 10*X^9 + 24*X^8 + 17*X^7 + 40*X^6 + 63*X^5 + 39*X^4 +
      16*X^2 + 11*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s84 : XPow fSeventeenB4 42757661676619789
    (51*X^33 + 59*X^32 + 21*X^31 + 50*X^30 + 6*X^29 + 64*X^28 + 55*X^27 + 63*X^26 + 18*X^25 + 57*X^24 +
      65*X^23 + 47*X^22 + 55*X^21 + 36*X^20 + 21*X^19 + 19*X^18 + 6*X^17 + 5*X^16 + 7*X^15 + 23*X^14 +
      63*X^13 + 21*X^12 + 38*X^11 + 39*X^10 + 51*X^9 + 13*X^8 + 6*X^7 + 51*X^6 + 8*X^5 + 51*X^4 +
      42*X^3 + 45*X^2 + 48*X + 26) :=
  mul_step (by norm_num) pSeventeenB4s83 pSeventeenB41 ⟨
    65,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s85 : XPow fSeventeenB4 85515323353239578
    (34*X^33 + 29*X^32 + 41*X^31 + 58*X^30 + 7*X^29 + 18*X^28 + 22*X^27 + 32*X^26 + 65*X^25 + 33*X^24 +
      9*X^23 + 17*X^22 + 16*X^21 + 23*X^19 + 56*X^18 + 61*X^17 + 35*X^16 + 37*X^15 + 3*X^14 + 5*X^13 +
      3*X^12 + 43*X^10 + 38*X^9 + 28*X^8 + 45*X^7 + 41*X^6 + 48*X^5 + 33*X^4 + 10*X^3 + 52*X^2 +
      20*X + 13) :=
  sq_step (by norm_num) pSeventeenB4s84 ⟨
    55*X^32 + 31*X^31 + 46*X^30 + 64*X^29 + 59*X^28 + 10*X^27 + 38*X^26 + 59*X^25 + 25*X^24 + 64*X^23 +
      33*X^22 + 20*X^21 + 64*X^20 + 38*X^19 + 25*X^18 + 65*X^17 + 29*X^16 + 54*X^15 + 58*X^14 +
      36*X^13 + 13*X^12 + 25*X^11 + 15*X^10 + 5*X^9 + 32*X^8 + 46*X^7 + 2*X^6 + 37*X^5 + 40*X^4 +
      22*X^3 + 24*X^2 + 5*X + 51,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s86 : XPow fSeventeenB4 171030646706479156
    (28*X^33 + 39*X^32 + 39*X^31 + 42*X^30 + 66*X^29 + 60*X^28 + X^27 + 61*X^26 + 46*X^25 + 26*X^24 +
      40*X^23 + 13*X^22 + 17*X^21 + 26*X^20 + 30*X^19 + 3*X^18 + 26*X^17 + 43*X^16 + 6*X^15 +
      23*X^14 + 53*X^13 + 58*X^12 + 20*X^11 + 12*X^10 + 3*X^9 + 56*X^8 + 27*X^7 + 62*X^6 + 42*X^4 +
      66*X^3 + 18*X^2 + 24*X + 10) :=
  sq_step (by norm_num) pSeventeenB4s85 ⟨
    17*X^32 + 63*X^31 + 13*X^30 + 38*X^29 + 14*X^28 + 50*X^27 + 11*X^26 + 64*X^25 + 8*X^24 + 34*X^23 +
      33*X^22 + 48*X^21 + 60*X^20 + 35*X^19 + 8*X^18 + 19*X^17 + 64*X^16 + 61*X^15 + 35*X^14 +
      17*X^13 + 64*X^12 + 59*X^11 + 26*X^10 + 2*X^9 + 24*X^8 + 13*X^7 + 9*X^6 + X^5 + 65*X^4 +
      41*X^3 + 7*X^2 + 18*X + 38,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s87 : XPow fSeventeenB4 342061293412958312
    (53*X^33 + 13*X^32 + 13*X^31 + 46*X^30 + 2*X^29 + 31*X^28 + 44*X^27 + 56*X^26 + 64*X^25 + 22*X^24 +
      57*X^23 + 30*X^22 + 15*X^21 + 26*X^20 + 43*X^19 + 59*X^18 + 14*X^17 + 5*X^16 + 50*X^15 +
      26*X^14 + 21*X^13 + 35*X^12 + 60*X^11 + 14*X^9 + 26*X^8 + 18*X^7 + 48*X^6 + 64*X^5 + 21*X^4 +
      14*X^3 + 49*X^2 + 62*X + 45) :=
  sq_step (by norm_num) pSeventeenB4s86 ⟨
    47*X^32 + 24*X^30 + 34*X^29 + 54*X^28 + 4*X^27 + 40*X^26 + 12*X^25 + 40*X^24 + 32*X^23 + 6*X^22 +
      61*X^21 + 52*X^20 + 60*X^19 + 38*X^18 + 64*X^17 + 23*X^16 + 20*X^15 + 64*X^14 + 48*X^13 +
      59*X^12 + 41*X^11 + 28*X^10 + 13*X^9 + 55*X^8 + 32*X^7 + 6*X^6 + 57*X^5 + 22*X^4 + 6*X^3 +
      3*X^2 + 61*X + 30,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s88 : XPow fSeventeenB4 342061293412958313
    (52*X^33 + 56*X^32 + 66*X^31 + 55*X^30 + 14*X^29 + 66*X^28 + 32*X^27 + 24*X^26 + 32*X^25 + 40*X^24 +
      25*X^23 + 29*X^22 + 4*X^21 + 61*X^20 + 36*X^19 + 36*X^18 + 56*X^17 + 4*X^16 + 39*X^15 +
      50*X^14 + 60*X^13 + 28*X^12 + 12*X^11 + 39*X^10 + 57*X^9 + 42*X^8 + 7*X^7 + 20*X^6 + 17*X^5 +
      X^4 + 38*X^3 + 52*X^2 + 4*X + 48) :=
  mul_step (by norm_num) pSeventeenB4s87 pSeventeenB41 ⟨
    53,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s89 : XPow fSeventeenB4 684122586825916626
    (5*X^33 + 13*X^31 + 16*X^30 + 45*X^29 + 54*X^28 + 57*X^27 + 24*X^26 + 14*X^25 + 53*X^24 + 55*X^23 +
      63*X^22 + 52*X^21 + 35*X^20 + 15*X^19 + 31*X^18 + 35*X^17 + 32*X^16 + 58*X^15 + 25*X^14 +
      9*X^13 + 4*X^12 + 2*X^11 + 50*X^10 + 48*X^9 + 53*X^8 + 65*X^7 + 19*X^6 + 25*X^5 + 64*X^4 +
      24*X^3 + 60*X^2 + 29*X + 15) :=
  sq_step (by norm_num) pSeventeenB4s88 ⟨
    24*X^32 + 43*X^31 + 58*X^30 + 11*X^29 + 63*X^28 + 62*X^27 + 65*X^26 + 13*X^25 + 36*X^24 + 54*X^23 +
      17*X^22 + 52*X^21 + 62*X^19 + 5*X^18 + 62*X^17 + 28*X^16 + 59*X^15 + 50*X^14 + 34*X^13 +
      25*X^12 + 58*X^11 + 59*X^10 + 22*X^9 + 18*X^8 + 21*X^7 + 40*X^6 + 41*X^5 + 33*X^4 + 3*X^3 +
      53*X^2 + 64*X + 6,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s90 : XPow fSeventeenB4 684122586825916627
    (10*X^33 + 12*X^32 + 28*X^31 + 50*X^30 + 17*X^29 + 30*X^28 + 23*X^27 + 57*X^26 + 59*X^25 + 18*X^24 +
      60*X^23 + 47*X^22 + 62*X^21 + 66*X^20 + 44*X^19 + 8*X^18 + 9*X^17 + 17*X^16 + 6*X^15 + 13*X^14 +
      19*X^13 + 23*X^12 + 17*X^11 + 63*X^10 + 18*X^9 + 66*X^8 + 48*X^7 + 12*X^6 + 8*X^5 + 43*X^4 +
      40*X^3 + 23*X^2 + 44*X + 2) :=
  mul_step (by norm_num) pSeventeenB4s89 pSeventeenB41 ⟨
    5,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s91 : XPow fSeventeenB4 1368245173651833254
    (28*X^33 + 23*X^32 + 23*X^31 + 51*X^30 + 61*X^29 + 29*X^28 + 43*X^27 + 18*X^26 + 34*X^25 + 59*X^24 +
      55*X^23 + 23*X^22 + 2*X^21 + 62*X^20 + 46*X^19 + 47*X^18 + 60*X^17 + 41*X^16 + 36*X^14 +
      18*X^13 + 26*X^12 + 37*X^11 + 66*X^10 + 58*X^9 + 62*X^8 + 49*X^7 + 49*X^6 + 62*X^5 + 18*X^4 +
      65*X^3 + 26*X^2 + 55*X + 4) :=
  sq_step (by norm_num) pSeventeenB4s90 ⟨
    33*X^32 + 38*X^31 + 23*X^30 + 61*X^29 + 33*X^28 + 66*X^27 + 32*X^26 + 57*X^25 + 36*X^24 + 52*X^23 +
      45*X^22 + 5*X^21 + 36*X^20 + 3*X^19 + 25*X^18 + 62*X^17 + 34*X^16 + 57*X^15 + 8*X^14 + 32*X^13 +
      19*X^12 + 50*X^11 + 40*X^10 + 10*X^9 + 19*X^8 + 43*X^7 + 24*X^6 + 21*X^5 + 22*X^4 + 45*X^3 +
      X^2 + 66*X,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s92 : XPow fSeventeenB4 2736490347303666508
    (5*X^33 + 46*X^32 + 41*X^31 + 50*X^30 + 55*X^29 + 47*X^28 + 48*X^27 + 47*X^26 + 34*X^25 + 14*X^24 +
      2*X^23 + 21*X^22 + 59*X^21 + 2*X^20 + 2*X^19 + 53*X^18 + 62*X^17 + 63*X^16 + 20*X^15 + 55*X^14 +
      42*X^13 + 16*X^12 + 40*X^11 + 46*X^10 + 62*X^9 + 4*X^8 + 4*X^6 + 58*X^5 + 44*X^4 + 26*X^3 +
      64*X^2 + 45*X + 13) :=
  sq_step (by norm_num) pSeventeenB4s91 ⟨
    47*X^32 + 42*X^31 + 29*X^30 + 43*X^29 + 20*X^28 + 32*X^27 + 13*X^26 + 58*X^25 + 23*X^24 + 41*X^23 +
      61*X^22 + 50*X^21 + 11*X^20 + 42*X^19 + 42*X^18 + 54*X^17 + 12*X^16 + 53*X^15 + 33*X^14 +
      6*X^12 + 30*X^11 + 28*X^10 + 52*X^9 + 62*X^8 + 28*X^7 + 24*X^6 + 33*X^5 + 40*X^4 + 38*X^3 +
      65*X^2 + 9*X + 26,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s93 : XPow fSeventeenB4 5472980694607333016
    (13*X^33 + 36*X^32 + 61*X^31 + 42*X^30 + 65*X^29 + 42*X^28 + 15*X^27 + 33*X^26 + 21*X^25 + 19*X^24 +
      21*X^23 + 52*X^22 + 46*X^21 + 52*X^20 + 35*X^19 + 32*X^18 + 51*X^17 + 49*X^16 + 58*X^15 + X^14 +
      51*X^13 + 63*X^12 + 22*X^11 + 32*X^10 + 18*X^9 + 37*X^8 + 49*X^7 + 55*X^6 + 59*X^4 + 34*X^3 +
      16*X^2 + 26*X + 20) :=
  sq_step (by norm_num) pSeventeenB4s92 ⟨
    25*X^32 + 41*X^31 + 57*X^30 + 56*X^29 + 20*X^28 + 17*X^27 + 6*X^26 + 23*X^25 + 63*X^24 + 27*X^23 +
      15*X^22 + 44*X^20 + 47*X^19 + 40*X^17 + 10*X^16 + 27*X^15 + 18*X^14 + 39*X^13 + 59*X^12 +
      38*X^11 + 11*X^10 + 59*X^9 + 57*X^8 + 65*X^7 + 4*X^6 + 32*X^5 + 56*X^4 + 55*X^3 + 45*X^2 +
      12*X + 63,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s94 : XPow fSeventeenB4 5472980694607333017
    (62*X^33 + 45*X^32 + 33*X^31 + 11*X^30 + 53*X^29 + 52*X^28 + 17*X^27 + 39*X^26 + 48*X^25 + 32*X^24 +
      4*X^23 + 33*X^22 + 15*X^21 + 47*X^20 + 39*X^19 + 21*X^18 + 16*X^17 + 5*X^16 + 32*X^15 +
      48*X^14 + 35*X^13 + 23*X^12 + 40*X^11 + 57*X^10 + 13*X^9 + 65*X^8 + 50*X^7 + 60*X^6 + 34*X^5 +
      3*X^4 + 31*X^3 + 64*X^2 + 15*X + 32) :=
  mul_step (by norm_num) pSeventeenB4s93 pSeventeenB41 ⟨
    13,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s95 : XPow fSeventeenB4 10945961389214666034
    (65*X^33 + 38*X^32 + 33*X^31 + 29*X^30 + 19*X^29 + 17*X^28 + 25*X^27 + 8*X^26 + 35*X^25 + 58*X^24 +
      50*X^23 + 31*X^22 + 44*X^21 + 33*X^20 + 61*X^19 + 65*X^18 + 26*X^17 + 48*X^16 + 50*X^15 +
      22*X^14 + 53*X^13 + 62*X^12 + 6*X^11 + 4*X^10 + 55*X^9 + 45*X^8 + 32*X^7 + 65*X^6 + 12*X^5 +
      61*X^4 + 32*X^3 + 17*X^2 + X + 60) :=
  sq_step (by norm_num) pSeventeenB4s94 ⟨
    25*X^32 + 2*X^31 + 19*X^30 + 23*X^29 + 13*X^28 + 36*X^27 + 56*X^26 + 59*X^25 + 12*X^24 + 17*X^23 +
      25*X^22 + 10*X^21 + 13*X^20 + 18*X^19 + 18*X^18 + 33*X^17 + 27*X^16 + 6*X^15 + 57*X^14 +
      26*X^13 + 2*X^12 + 10*X^11 + 47*X^10 + 45*X^9 + 20*X^8 + 26*X^7 + 26*X^6 + 5*X^5 + 62*X^4 +
      27*X^3 + 59*X^2 + 19*X + 2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s96 : XPow fSeventeenB4 10945961389214666035
    (34*X^33 + 20*X^32 + 51*X^31 + 17*X^30 + 5*X^29 + 9*X^28 + 62*X^27 + 58*X^26 + 2*X^25 + 38*X^24 +
      59*X^23 + 46*X^22 + 49*X^21 + 54*X^20 + 33*X^19 + 10*X^18 + 17*X^17 + 53*X^16 + 43*X^15 +
      38*X^14 + 56*X^13 + 11*X^12 + 44*X^11 + 49*X^10 + 59*X^9 + 45*X^8 + 40*X^7 + 44*X^6 + 3*X^5 +
      11*X^4 + 25*X^3 + 57*X^2 + 35*X + 26) :=
  mul_step (by norm_num) pSeventeenB4s95 pSeventeenB41 ⟨
    65,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s97 : XPow fSeventeenB4 21891922778429332070
    (35*X^33 + 31*X^32 + 27*X^31 + 20*X^30 + 48*X^29 + 39*X^28 + 60*X^27 + 23*X^26 + 47*X^25 + 22*X^24 +
      48*X^23 + 3*X^22 + 39*X^21 + 40*X^20 + 63*X^19 + 60*X^18 + 58*X^17 + 2*X^16 + 32*X^15 +
      53*X^14 + 30*X^13 + 14*X^12 + 17*X^11 + 26*X^10 + 57*X^9 + 51*X^8 + 36*X^7 + 51*X^6 + 14*X^5 +
      33*X^4 + 28*X^3 + 55*X^2 + 56*X + 63) :=
  sq_step (by norm_num) pSeventeenB4s96 ⟨
    17*X^32 + 54*X^31 + 33*X^30 + 9*X^29 + 27*X^28 + 6*X^27 + 27*X^26 + 51*X^25 + 41*X^24 + 15*X^23 +
      35*X^22 + 27*X^21 + 55*X^20 + 2*X^19 + 42*X^18 + 26*X^17 + 6*X^16 + 65*X^15 + 6*X^14 + 31*X^13 +
      46*X^12 + 62*X^11 + 11*X^10 + 40*X^9 + 45*X^8 + 47*X^7 + 26*X^6 + 37*X^5 + 34*X^4 + 29*X^3 +
      22*X^2 + 6*X + 42,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s98 : XPow fSeventeenB4 21891922778429332071
    (34*X^33 + 20*X^32 + 37*X^31 + 16*X^30 + 48*X^29 + 5*X^28 + 16*X^27 + 13*X^26 + 64*X^25 + 57*X^24 +
      49*X^23 + 4*X^22 + 28*X^21 + 18*X^20 + 17*X^19 + 3*X^18 + 42*X^17 + 13*X^16 + 54*X^15 +
      58*X^14 + 52*X^13 + 30*X^12 + 63*X^11 + 28*X^10 + 7*X^9 + 43*X^8 + 53*X^7 + 57*X^6 + 43*X^5 +
      27*X^4 + 49*X^3 + 14*X^2 + 65*X + 14) :=
  mul_step (by norm_num) pSeventeenB4s97 pSeventeenB41 ⟨
    35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s99 : XPow fSeventeenB4 43783845556858664142
    (4*X^33 + 51*X^32 + 25*X^31 + 57*X^30 + 3*X^29 + 12*X^28 + 31*X^27 + 64*X^26 + 41*X^25 + 12*X^24 +
      21*X^23 + 2*X^22 + 44*X^21 + 15*X^20 + 46*X^19 + 59*X^18 + 12*X^17 + 25*X^16 + 43*X^15 +
      6*X^14 + 8*X^13 + 2*X^12 + 31*X^11 + X^10 + 35*X^9 + 6*X^8 + 20*X^7 + 33*X^6 + 47*X^5 + 29*X^4 +
      43*X^3 + 60*X^2 + 58*X + 50) :=
  sq_step (by norm_num) pSeventeenB4s98 ⟨
    17*X^32 + 54*X^31 + 19*X^30 + 23*X^29 + 8*X^28 + 39*X^27 + 25*X^26 + 37*X^25 + 4*X^24 + 37*X^23 +
      17*X^22 + 53*X^21 + 21*X^20 + 25*X^19 + 29*X^18 + 47*X^17 + 25*X^16 + 51*X^15 + 30*X^14 +
      4*X^13 + X^12 + 63*X^11 + 66*X^10 + 4*X^9 + 27*X^8 + 29*X^6 + 53*X^5 + 14*X^4 + 29*X^3 +
      20*X^2 + 50*X + 37,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s100 : XPow fSeventeenB4 87567691113717328284
    (27*X^33 + 64*X^32 + 48*X^31 + 28*X^30 + 18*X^29 + 59*X^28 + 44*X^27 + 64*X^26 + 22*X^25 + 23*X^24 +
      53*X^23 + 50*X^22 + 49*X^21 + 24*X^20 + 44*X^19 + 45*X^18 + 49*X^17 + 13*X^16 + 55*X^15 +
      27*X^14 + 56*X^13 + 9*X^12 + 33*X^11 + 18*X^10 + 59*X^9 + 13*X^8 + 7*X^7 + 54*X^6 + 18*X^5 +
      58*X^4 + 30*X^3 + 7*X^2 + 46*X + 47) :=
  sq_step (by norm_num) pSeventeenB4s99 ⟨
    16*X^32 + 38*X^31 + 33*X^30 + 61*X^29 + 66*X^28 + 34*X^27 + 61*X^26 + 9*X^25 + 30*X^24 + 17*X^23 +
      36*X^22 + 54*X^20 + 64*X^19 + 13*X^18 + 55*X^17 + 18*X^16 + 29*X^15 + 35*X^14 + 45*X^13 +
      34*X^12 + 32*X^11 + 50*X^10 + 37*X^9 + 26*X^8 + 56*X^7 + 51*X^6 + 34*X^5 + 21*X^4 + 66*X^3 +
      11*X^2 + 49*X + 65,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s101 : XPow fSeventeenB4 175135382227434656568
    (20*X^33 + 31*X^32 + 40*X^31 + 32*X^30 + 56*X^29 + 35*X^28 + 55*X^27 + 56*X^26 + 26*X^25 + 6*X^24 +
      14*X^23 + 9*X^22 + 16*X^21 + 55*X^20 + 3*X^19 + 13*X^18 + 52*X^17 + 51*X^16 + 19*X^15 +
      54*X^14 + 34*X^13 + 13*X^12 + 2*X^11 + 13*X^10 + 35*X^9 + 27*X^8 + 36*X^7 + 63*X^6 + 6*X^5 +
      42*X^4 + 22*X^3 + 22*X^2 + 16*X + 65) :=
  sq_step (by norm_num) pSeventeenB4s100 ⟨
    59*X^32 + 23*X^31 + 49*X^30 + 52*X^29 + 20*X^28 + 19*X^27 + 32*X^26 + 25*X^25 + 56*X^24 + 56*X^23 +
      58*X^22 + 32*X^21 + 16*X^20 + 46*X^19 + 65*X^18 + 64*X^17 + 12*X^16 + X^15 + 5*X^14 + 31*X^13 +
      17*X^12 + 21*X^11 + 11*X^10 + 45*X^9 + 35*X^8 + 10*X^7 + 38*X^6 + 50*X^5 + 33*X^4 + 59*X^3 +
      9*X^2 + 17*X,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s102 : XPow fSeventeenB4 350270764454869313136
    (21*X^33 + 7*X^32 + 55*X^31 + 23*X^30 + 59*X^29 + 19*X^28 + 3*X^27 + 41*X^26 + 21*X^25 + 51*X^24 +
      10*X^23 + 48*X^22 + 60*X^21 + 53*X^20 + 53*X^19 + 10*X^18 + 6*X^17 + 13*X^16 + 52*X^15 +
      3*X^14 + 31*X^13 + 8*X^12 + 10*X^11 + 63*X^10 + 31*X^9 + 35*X^8 + 12*X^7 + 11*X^6 + 29*X^5 +
      65*X^4 + 12*X^3 + 15*X^2 + 60*X + 12) :=
  sq_step (by norm_num) pSeventeenB4s101 ⟨
    65*X^32 + 30*X^31 + 62*X^30 + 14*X^29 + 27*X^28 + 12*X^27 + 62*X^26 + 23*X^25 + 20*X^24 + 9*X^22 +
      30*X^21 + 45*X^20 + 36*X^19 + 5*X^18 + 20*X^17 + 58*X^16 + 36*X^15 + 31*X^14 + X^13 + 47*X^12 +
      6*X^11 + 23*X^10 + 14*X^9 + 60*X^8 + 60*X^7 + 55*X^6 + 23*X^5 + 62*X^4 + 10*X^3 + 24*X^2 +
      20*X + 20,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s103 : XPow fSeventeenB4 700541528909738626272
    (23*X^33 + 40*X^32 + 29*X^31 + 51*X^30 + 42*X^29 + 54*X^28 + 10*X^27 + 52*X^26 + 14*X^24 + X^23 +
      46*X^22 + 53*X^21 + 21*X^20 + 22*X^19 + 48*X^18 + 54*X^17 + 29*X^16 + 62*X^15 + 55*X^14 +
      57*X^13 + 43*X^12 + 14*X^11 + 57*X^10 + 6*X^9 + 38*X^8 + 37*X^7 + 21*X^6 + 26*X^5 + 28*X^4 +
      9*X^3 + 45*X^2 + 31*X + 45) :=
  sq_step (by norm_num) pSeventeenB4s102 ⟨
    39*X^32 + 37*X^31 + 40*X^30 + 53*X^29 + 61*X^28 + 63*X^27 + 52*X^26 + 17*X^25 + 13*X^24 + 17*X^23 +
      9*X^22 + 44*X^21 + 22*X^20 + 9*X^19 + 8*X^18 + 45*X^17 + 26*X^16 + 24*X^15 + 33*X^14 + 38*X^13 +
      10*X^12 + 17*X^11 + 48*X^10 + 51*X^9 + 3*X^8 + 15*X^7 + 28*X^6 + 42*X^5 + 6*X^4 + 53*X^3 +
      25*X^2 + 16*X + 54,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s104 : XPow fSeventeenB4 700541528909738626273
    (19*X^33 + 11*X^32 + 66*X^31 + 65*X^30 + 58*X^29 + 60*X^28 + 34*X^27 + 37*X^26 + 55*X^25 + 5*X^24 +
      59*X^23 + 30*X^22 + 38*X^21 + 2*X^20 + 14*X^19 + 37*X^18 + 17*X^17 + 61*X^16 + 48*X^15 +
      62*X^14 + 45*X^13 + 57*X^12 + 66*X^11 + 8*X^10 + 11*X^9 + 55*X^8 + 7*X^7 + 60*X^6 + 25*X^5 +
      16*X^4 + 20*X^3 + 57*X^2 + 31*X + 36) :=
  mul_step (by norm_num) pSeventeenB4s103 pSeventeenB41 ⟨
    23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s105 : XPow fSeventeenB4 1401083057819477252546
    (39*X^33 + 30*X^32 + 3*X^31 + 33*X^30 + 51*X^29 + 58*X^28 + 19*X^27 + 52*X^26 + 64*X^25 + 63*X^24 +
      59*X^22 + 57*X^20 + 14*X^19 + 42*X^18 + 18*X^17 + 59*X^16 + 49*X^15 + 37*X^14 + 2*X^13 +
      53*X^12 + 18*X^11 + 39*X^10 + 28*X^9 + 23*X^8 + 14*X^7 + 21*X^6 + 15*X^5 + 27*X^4 + 52*X^3 +
      20*X^2 + 38*X + 23) :=
  sq_step (by norm_num) pSeventeenB4s104 ⟨
    26*X^32 + X^31 + 53*X^30 + 30*X^29 + X^28 + 48*X^27 + 27*X^26 + 2*X^25 + 28*X^24 + 31*X^23 + 3*X^22 +
      23*X^21 + 65*X^20 + 6*X^19 + 53*X^18 + 15*X^17 + 51*X^16 + 50*X^15 + 46*X^14 + 40*X^13 +
      20*X^12 + 36*X^10 + 64*X^9 + 65*X^8 + 37*X^7 + 13*X^6 + 14*X^5 + 28*X^4 + 4*X^3 + 54*X^2 + 9*X,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s106 : XPow fSeventeenB4 2802166115638954505092
    (19*X^33 + 5*X^32 + X^31 + 18*X^30 + 21*X^29 + 14*X^28 + 17*X^27 + 35*X^26 + 44*X^24 + 21*X^23 +
      48*X^22 + 48*X^21 + 8*X^20 + 7*X^19 + 45*X^18 + 35*X^17 + 42*X^16 + 13*X^15 + 54*X^14 + 8*X^13 +
      14*X^12 + 59*X^11 + 58*X^10 + 50*X^9 + 47*X^8 + 18*X^7 + 22*X^6 + 33*X^5 + 41*X^4 + 56*X^3 +
      53*X^2 + 8*X + 13) :=
  sq_step (by norm_num) pSeventeenB4s105 ⟨
    47*X^32 + 22*X^31 + 43*X^30 + 54*X^29 + 29*X^28 + 49*X^27 + X^26 + 57*X^25 + 64*X^24 + 28*X^23 +
      55*X^22 + 16*X^21 + 36*X^20 + 8*X^19 + 7*X^18 + 8*X^17 + 55*X^16 + 3*X^15 + 18*X^14 + 41*X^13 +
      65*X^12 + 35*X^11 + 53*X^10 + 20*X^9 + 57*X^8 + 28*X^7 + 16*X^6 + 57*X^5 + 53*X^4 + 39*X^3 +
      22*X^2 + 17*X + 50,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s107 : XPow fSeventeenB4 2802166115638954505093
    (43*X^33 + 24*X^32 + 10*X^31 + 40*X^30 + 61*X^29 + 35*X^28 + 58*X^27 + 16*X^26 + 40*X^25 + X^24 +
      50*X^23 + 29*X^22 + 57*X^21 + 40*X^20 + 14*X^19 + 53*X^18 + 35*X^17 + 18*X^16 + 22*X^15 +
      50*X^14 + 4*X^13 + 45*X^12 + 13*X^11 + 40*X^10 + 48*X^9 + 62*X^8 + 25*X^7 + 64*X^6 + 56*X^5 +
      21*X^4 + 44*X^3 + 12*X^2 + 16*X + 21) :=
  mul_step (by norm_num) pSeventeenB4s106 pSeventeenB41 ⟨
    19,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s108 : XPow fSeventeenB4 5604332231277909010186
    (23*X^33 + 51*X^32 + 3*X^31 + 2*X^30 + 8*X^29 + 64*X^28 + 33*X^27 + 58*X^26 + 66*X^25 + 20*X^24 +
      27*X^23 + 65*X^22 + 61*X^21 + 37*X^20 + 38*X^19 + 34*X^18 + 65*X^17 + 63*X^16 + 56*X^15 +
      33*X^14 + 50*X^13 + 29*X^12 + 46*X^11 + 43*X^10 + 60*X^9 + 9*X^8 + 7*X^7 + 48*X^6 + 21*X^5 +
      53*X^4 + 3*X^3 + 66*X^2 + 8*X + 31) :=
  sq_step (by norm_num) pSeventeenB4s107 ⟨
    40*X^32 + 21*X^30 + 38*X^29 + 48*X^28 + 55*X^27 + 51*X^26 + 12*X^25 + 66*X^24 + 25*X^23 + 40*X^22 +
      66*X^21 + 32*X^20 + 11*X^19 + 52*X^18 + 26*X^17 + 56*X^16 + 50*X^15 + 60*X^14 + 52*X^13 +
      11*X^12 + 47*X^11 + 18*X^10 + 65*X^9 + 5*X^8 + 60*X^7 + 32*X^6 + 50*X^5 + 24*X^4 + 22*X^3 +
      47*X^2 + 37*X + 47,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s109 : XPow fSeventeenB4 11208664462555818020372
    (60*X^33 + 44*X^32 + 13*X^31 + 33*X^30 + 28*X^29 + 14*X^28 + 64*X^27 + 6*X^26 + 56*X^25 + 47*X^24 +
      11*X^23 + 28*X^22 + 18*X^21 + 2*X^20 + 62*X^19 + 63*X^18 + 64*X^17 + 64*X^16 + 22*X^15 +
      27*X^14 + 37*X^13 + 20*X^12 + 32*X^11 + 26*X^10 + 15*X^9 + 64*X^8 + 11*X^7 + 27*X^6 + 25*X^5 +
      31*X^4 + 57*X^3 + 9*X^2 + 51*X + 37) :=
  sq_step (by norm_num) pSeventeenB4s108 ⟨
    60*X^32 + 54*X^31 + 21*X^30 + 64*X^29 + 10*X^28 + 36*X^27 + 48*X^26 + 44*X^25 + 49*X^24 + 62*X^23 +
      29*X^22 + 34*X^21 + 3*X^20 + 62*X^19 + 34*X^18 + 57*X^17 + 33*X^16 + 52*X^15 + 30*X^14 +
      58*X^13 + 13*X^12 + 11*X^11 + 29*X^10 + 13*X^9 + 41*X^7 + 42*X^6 + 38*X^5 + 49*X^4 + 37*X^3 +
      62*X^2 + 55*X + 35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s110 : XPow fSeventeenB4 22417328925111636040744
    (37*X^33 + 19*X^32 + 30*X^31 + 25*X^30 + 43*X^29 + 58*X^28 + 40*X^27 + 34*X^26 + 37*X^25 + 60*X^24 +
      41*X^23 + 16*X^22 + 29*X^21 + 28*X^20 + 11*X^19 + 38*X^18 + 33*X^17 + 25*X^16 + 24*X^15 +
      7*X^14 + 9*X^13 + 26*X^12 + 62*X^11 + 48*X^10 + 27*X^9 + 35*X^8 + 4*X^7 + 36*X^6 + 13*X^5 +
      27*X^4 + 12*X^3 + 43*X^2 + 4*X + 56) :=
  sq_step (by norm_num) pSeventeenB4s109 ⟨
    49*X^32 + 18*X^31 + 65*X^30 + 55*X^29 + 16*X^28 + 64*X^27 + 30*X^25 + 44*X^24 + 12*X^23 + 62*X^22 +
      53*X^21 + 52*X^20 + 48*X^19 + 11*X^18 + 26*X^17 + 53*X^16 + 32*X^15 + 8*X^14 + 14*X^13 +
      54*X^12 + 11*X^11 + 22*X^10 + 31*X^9 + 66*X^8 + 47*X^7 + 12*X^6 + 14*X^5 + 27*X^4 + 18*X^3 +
      44*X^2 + 65*X + 34,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s111 : XPow fSeventeenB4 22417328925111636040745
    (26*X^33 + 36*X^32 + 20*X^31 + 13*X^30 + 12*X^29 + X^28 + 40*X^27 + 47*X^26 + 24*X^25 + 62*X^24 +
      34*X^23 + 59*X^22 + 40*X^20 + 27*X^19 + 61*X^18 + 29*X^17 + 2*X^16 + 54*X^15 + 52*X^14 +
      3*X^13 + 3*X^12 + 45*X^11 + 4*X^10 + 44*X^9 + 65*X^8 + 63*X^7 + 24*X^6 + 28*X^5 + 32*X^4 +
      29*X^3 + 40*X^2 + 16*X + 55) :=
  mul_step (by norm_num) pSeventeenB4s110 pSeventeenB41 ⟨
    37,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s112 : XPow fSeventeenB4 44834657850223272081490
    (10*X^33 + 32*X^32 + 59*X^31 + 57*X^30 + 12*X^29 + 63*X^28 + 40*X^27 + 57*X^26 + 34*X^25 + 27*X^24 +
      59*X^23 + 12*X^22 + 24*X^21 + 39*X^20 + 23*X^19 + 31*X^18 + 2*X^17 + 21*X^16 + 46*X^15 +
      2*X^14 + 22*X^13 + 50*X^12 + 65*X^11 + 60*X^10 + 9*X^9 + 49*X^8 + 12*X^7 + 49*X^6 + 46*X^5 +
      62*X^4 + 30*X^3 + 7*X^2 + 57*X + 49) :=
  sq_step (by norm_num) pSeventeenB4s111 ⟨
    6*X^32 + 8*X^31 + 46*X^30 + 50*X^29 + 66*X^28 + 24*X^27 + 56*X^26 + 19*X^25 + 21*X^24 + 31*X^23 +
      65*X^22 + 24*X^21 + 2*X^20 + 51*X^19 + 28*X^18 + 5*X^17 + 33*X^16 + 10*X^15 + 17*X^14 +
      23*X^13 + 7*X^12 + 65*X^11 + 55*X^10 + 32*X^9 + 37*X^8 + 28*X^7 + 61*X^6 + 49*X^5 + 56*X^4 +
      62*X^3 + 59*X^2 + 7*X + 64,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s113 : XPow fSeventeenB4 44834657850223272081491
    (52*X^33 + 57*X^32 + 14*X^31 + 22*X^30 + 56*X^29 + 53*X^28 + 55*X^27 + 53*X^26 + 39*X^25 + 52*X^24 +
      6*X^23 + 14*X^22 + 26*X^21 + 58*X^20 + 57*X^19 + 15*X^18 + 42*X^17 + 31*X^16 + 31*X^15 +
      30*X^14 + 13*X^13 + 40*X^12 + 61*X^11 + 39*X^10 + 46*X^9 + 14*X^8 + 40*X^7 + 20*X^6 + 17*X^5 +
      X^4 + 34*X^3 + 45*X^2 + 40*X + 4) :=
  mul_step (by norm_num) pSeventeenB4s112 pSeventeenB41 ⟨
    10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s114 : XPow fSeventeenB4 89669315700446544162982
    (56*X^33 + 42*X^32 + 36*X^31 + 43*X^30 + 28*X^29 + 58*X^28 + 56*X^27 + 29*X^26 + 58*X^25 + 6*X^24 +
      57*X^23 + 19*X^22 + 42*X^21 + 34*X^20 + 46*X^19 + 34*X^18 + 8*X^17 + 46*X^16 + 10*X^15 +
      17*X^14 + 12*X^13 + 7*X^12 + 40*X^11 + 38*X^10 + 20*X^9 + 39*X^8 + 7*X^7 + 25*X^6 + 27*X^5 +
      51*X^4 + 54*X^3 + 63*X^2 + 64*X + 22) :=
  sq_step (by norm_num) pSeventeenB4s113 ⟨
    24*X^32 + 13*X^31 + 63*X^30 + 45*X^29 + 31*X^28 + 36*X^27 + 23*X^26 + 4*X^25 + 61*X^24 + 65*X^23 +
      58*X^22 + 40*X^21 + 16*X^20 + 51*X^19 + 5*X^18 + 59*X^17 + 10*X^16 + 56*X^15 + 29*X^14 +
      35*X^13 + 23*X^12 + 41*X^11 + 6*X^10 + 63*X^9 + 42*X^8 + 47*X^7 + 14*X^6 + 35*X^5 + 30*X^4 +
      33*X^3 + 48*X^2 + 47*X + 15,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s115 : XPow fSeventeenB4 179338631400893088325964
    (29*X^33 + 45*X^32 + 18*X^31 + 2*X^30 + 2*X^29 + 19*X^28 + 45*X^27 + 9*X^26 + 61*X^25 + 56*X^24 +
      31*X^23 + 37*X^22 + 22*X^21 + 11*X^20 + 2*X^19 + 12*X^18 + 19*X^17 + 48*X^16 + 42*X^15 +
      64*X^14 + 13*X^13 + 9*X^12 + 34*X^11 + 51*X^10 + 12*X^9 + 13*X^8 + 11*X^7 + 62*X^6 + 36*X^5 +
      42*X^4 + 47*X^3 + 30*X^2 + 42*X + 53) :=
  sq_step (by norm_num) pSeventeenB4s114 ⟨
    54*X^32 + 55*X^31 + 26*X^30 + 51*X^29 + 59*X^28 + 58*X^27 + 24*X^26 + 34*X^25 + 39*X^24 + 12*X^23 +
      56*X^22 + 54*X^21 + 26*X^20 + 29*X^19 + 39*X^18 + 65*X^17 + 21*X^16 + 40*X^15 + 53*X^14 +
      13*X^13 + 66*X^12 + 47*X^11 + 53*X^10 + 20*X^9 + 34*X^8 + 21*X^7 + 52*X^6 + 54*X^5 + 41*X^4 +
      28*X^3 + 22*X^2 + 29*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s116 : XPow fSeventeenB4 179338631400893088325965
    (36*X^33 + 39*X^32 + 18*X^31 + 31*X^30 + 59*X^29 + 9*X^28 + 30*X^27 + 29*X^26 + 64*X^25 + 4*X^24 +
      33*X^23 + 60*X^22 + 47*X^21 + 3*X^20 + 7*X^19 + 50*X^18 + 62*X^17 + 32*X^16 + 61*X^15 +
      63*X^14 + 29*X^13 + 62*X^12 + 7*X^11 + 32*X^10 + 11*X^9 + 57*X^8 + 56*X^7 + 41*X^6 + 12*X^5 +
      50*X^4 + 48*X^3 + 34*X^2 + 47*X + 25) :=
  mul_step (by norm_num) pSeventeenB4s115 pSeventeenB41 ⟨
    29,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s117 : XPow fSeventeenB4 358677262801786176651930
    (48*X^33 + 2*X^32 + 56*X^31 + 19*X^29 + 20*X^28 + 17*X^27 + 23*X^26 + X^25 + 20*X^24 + 66*X^23 +
      8*X^22 + 46*X^21 + 17*X^20 + 62*X^19 + 43*X^18 + 8*X^17 + 38*X^16 + 40*X^15 + 50*X^14 + 5*X^13 +
      8*X^12 + 31*X^11 + 55*X^10 + 59*X^9 + 57*X^8 + 53*X^7 + 38*X^6 + 47*X^5 + 55*X^4 + 21*X^3 +
      65*X^2 + 52*X + 32) :=
  sq_step (by norm_num) pSeventeenB4s116 ⟨
    23*X^32 + 40*X^31 + 65*X^30 + 21*X^29 + 36*X^28 + 41*X^27 + 22*X^26 + 26*X^25 + 49*X^24 + 18*X^23 +
      58*X^22 + 28*X^21 + 8*X^20 + 48*X^19 + 31*X^18 + 12*X^17 + 14*X^16 + 39*X^15 + X^14 + 48*X^13 +
      16*X^12 + 53*X^11 + 24*X^10 + 51*X^9 + 6*X^8 + 65*X^7 + 47*X^6 + 38*X^5 + 51*X^4 + 14*X^3 +
      14*X^2 + 23*X + 25,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s118 : XPow fSeventeenB4 358677262801786176651931
    (31*X^33 + 33*X^32 + 8*X^31 + 40*X^29 + 66*X^28 + 52*X^26 + 24*X^25 + 19*X^24 + 6*X^23 + 65*X^22 +
      35*X^21 + 29*X^20 + 7*X^19 + 57*X^18 + 45*X^17 + 35*X^16 + 15*X^15 + 30*X^14 + 18*X^13 +
      45*X^12 + 33*X^11 + 2*X^10 + 56*X^9 + 9*X^8 + 35*X^7 + 16*X^6 + 40*X^5 + 56*X^4 + 7*X^3 +
      48*X^2 + 29*X + 46) :=
  mul_step (by norm_num) pSeventeenB4s117 pSeventeenB41 ⟨
    48,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s119 : XPow fSeventeenB4 717354525603572353303862
    (3*X^33 + 29*X^32 + 18*X^31 + 49*X^30 + 39*X^29 + 48*X^28 + 66*X^27 + 37*X^26 + 14*X^25 + 7*X^24 +
      12*X^23 + 22*X^22 + 30*X^21 + 48*X^20 + 21*X^19 + 29*X^18 + 26*X^17 + 31*X^16 + 3*X^15 +
      54*X^14 + 9*X^13 + 15*X^12 + 4*X^11 + 6*X^10 + 52*X^9 + 8*X^8 + 37*X^7 + 41*X^6 + 25*X^5 +
      64*X^4 + 55*X^3 + 56*X^2 + 17*X + 9) :=
  sq_step (by norm_num) pSeventeenB4s118 ⟨
    23*X^32 + 15*X^31 + 56*X^30 + 49*X^29 + 50*X^28 + 21*X^27 + 62*X^26 + 22*X^25 + 58*X^24 + 50*X^23 +
      18*X^22 + 55*X^21 + 23*X^20 + 31*X^19 + 16*X^18 + 28*X^17 + 2*X^16 + 17*X^15 + 54*X^14 +
      25*X^13 + 47*X^12 + 4*X^11 + 35*X^10 + 31*X^9 + 3*X^8 + X^7 + 10*X^6 + 27*X^5 + 36*X^4 +
      64*X^3 + 2*X^2 + 21*X + 59,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s120 : XPow fSeventeenB4 717354525603572353303863
    (35*X^33 + 4*X^32 + 16*X^31 + 42*X^30 + 66*X^29 + 23*X^28 + 23*X^27 + 13*X^26 + 24*X^25 + 30*X^24 +
      47*X^23 + 27*X^22 + 24*X^21 + 65*X^20 + 10*X^19 + 50*X^18 + 44*X^17 + 32*X^16 + 56*X^15 +
      65*X^14 + 24*X^13 + 30*X^12 + 13*X^11 + 61*X^10 + 54*X^9 + 51*X^8 + 45*X^7 + 44*X^6 + 17*X^5 +
      53*X^4 + 44*X^3 + 13*X + 28) :=
  mul_step (by norm_num) pSeventeenB4s119 pSeventeenB41 ⟨
    3,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s121 : XPow fSeventeenB4 1434709051207144706607726
    (13*X^33 + 61*X^32 + 31*X^31 + 32*X^30 + 52*X^29 + 11*X^28 + 49*X^27 + 63*X^26 + 29*X^25 + 21*X^24 +
      52*X^23 + 36*X^22 + 61*X^21 + 6*X^20 + 24*X^19 + 60*X^18 + 65*X^17 + 41*X^15 + 9*X^14 +
      56*X^13 + 57*X^12 + 29*X^11 + 45*X^10 + 58*X^9 + 46*X^8 + 17*X^7 + 20*X^6 + 30*X^5 + 51*X^4 +
      15*X^3 + 59*X^2 + 5*X + 12) :=
  sq_step (by norm_num) pSeventeenB4s120 ⟨
    19*X^32 + 50*X^31 + 53*X^30 + 7*X^29 + 48*X^28 + 22*X^27 + 22*X^26 + 9*X^25 + X^24 + 55*X^23 +
      42*X^22 + 61*X^21 + 41*X^20 + 53*X^19 + 53*X^18 + 5*X^17 + 63*X^16 + 61*X^15 + 4*X^14 +
      51*X^13 + 60*X^12 + 31*X^11 + 57*X^10 + 58*X^9 + 28*X^8 + 55*X^7 + 4*X^6 + 58*X^5 + 50*X^4 +
      13*X^3 + 30*X^2 + 14*X + 13,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s122 : XPow fSeventeenB4 1434709051207144706607727
    (20*X^33 + 15*X^32 + 23*X^31 + 65*X^30 + 22*X^29 + 19*X^28 + 47*X^27 + 47*X^26 + 50*X^25 + 63*X^24 +
      55*X^23 + 48*X^22 + 36*X^21 + 36*X^20 + 35*X^18 + 34*X^17 + 55*X^16 + 40*X^15 + 53*X^14 +
      29*X^13 + 30*X^12 + 53*X^11 + 30*X^10 + 22*X^9 + 33*X^8 + 15*X^7 + 23*X^6 + 26*X^5 + 51*X^4 +
      7*X^3 + 43*X^2 + 7*X + 32) :=
  mul_step (by norm_num) pSeventeenB4s121 pSeventeenB41 ⟨
    13,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s123 : XPow fSeventeenB4 2869418102414289413215454
    (52*X^33 + 57*X^32 + 9*X^31 + 34*X^30 + 21*X^29 + 40*X^28 + 32*X^27 + 61*X^26 + 28*X^25 + 33*X^24 +
      9*X^23 + 66*X^22 + X^21 + 12*X^20 + 15*X^19 + 12*X^18 + 30*X^17 + 63*X^16 + 8*X^15 + 29*X^14 +
      57*X^13 + 7*X^12 + 10*X^11 + 46*X^10 + 65*X^9 + 65*X^8 + 14*X^7 + 44*X^6 + 43*X^5 + 65*X^4 +
      34*X^3 + 43*X^2 + 37) :=
  sq_step (by norm_num) pSeventeenB4s122 ⟨
    65*X^32 + 60*X^31 + 46*X^30 + 42*X^29 + 65*X^28 + 31*X^26 + 54*X^25 + 51*X^24 + 52*X^23 + 17*X^22 +
      30*X^21 + 51*X^20 + 37*X^19 + 5*X^18 + 57*X^17 + 19*X^16 + 12*X^15 + 38*X^14 + 20*X^13 +
      8*X^12 + 15*X^11 + 16*X^10 + 55*X^9 + 64*X^8 + 20*X^7 + 12*X^6 + 59*X^5 + 8*X^4 + 6*X^3 +
      64*X^2 + 3*X + 45,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s124 : XPow fSeventeenB4 5738836204828578826430908
    (5*X^33 + 16*X^32 + 30*X^31 + 45*X^30 + 27*X^29 + 9*X^28 + 51*X^27 + X^26 + 18*X^25 + 12*X^24 +
      32*X^23 + 55*X^22 + 26*X^21 + 46*X^20 + 32*X^19 + 25*X^18 + 29*X^17 + 5*X^16 + 29*X^15 +
      8*X^14 + 22*X^13 + 35*X^12 + 46*X^11 + 62*X^10 + 21*X^9 + 57*X^8 + 48*X^7 + 63*X^6 + 61*X^5 +
      X^4 + 8*X^3 + 22*X^2 + 7*X + 4) :=
  sq_step (by norm_num) pSeventeenB4s123 ⟨
    24*X^32 + 13*X^31 + 12*X^30 + 18*X^29 + 39*X^28 + 16*X^27 + 43*X^26 + 57*X^25 + 3*X^24 + 14*X^23 +
      23*X^22 + X^21 + 4*X^20 + 5*X^19 + 47*X^18 + 31*X^17 + 41*X^16 + 20*X^15 + 10*X^14 + X^13 +
      18*X^12 + 52*X^11 + 43*X^10 + 43*X^9 + 7*X^8 + 48*X^7 + 35*X^6 + 37*X^5 + 59*X^4 + 47*X^3 +
      36*X + 38,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s125 : XPow fSeventeenB4 5738836204828578826430909
    (26*X^33 + 29*X^32 + 57*X^31 + 32*X^30 + 39*X^29 + 24*X^28 + 61*X^26 + 18*X^25 + 62*X^24 + 52*X^23 +
      21*X^22 + 6*X^21 + 16*X^20 + 38*X^19 + 2*X^18 + 49*X^17 + 55*X^16 + 56*X^15 + 26*X^14 +
      50*X^13 + 29*X^11 + 36*X^10 + 22*X^9 + 49*X^8 + 25*X^7 + 48*X^6 + 12*X^5 + 27*X^4 + 2*X^3 +
      X^2 + 33*X + 2) :=
  mul_step (by norm_num) pSeventeenB4s124 pSeventeenB41 ⟨
    5,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s126 : XPow fSeventeenB4 11477672409657157652861818
    (43*X^33 + 64*X^32 + 60*X^31 + 47*X^30 + 20*X^29 + 5*X^28 + 53*X^27 + 63*X^26 + 57*X^25 + 6*X^24 +
      34*X^23 + 66*X^22 + 66*X^21 + 14*X^20 + 52*X^19 + 49*X^18 + 4*X^17 + 10*X^16 + 62*X^15 +
      26*X^14 + X^13 + 6*X^12 + 42*X^11 + 50*X^10 + 33*X^9 + 64*X^8 + 61*X^7 + 33*X^6 + 32*X^5 +
      53*X^4 + 31*X^3 + 28*X^2 + 30*X + 12) :=
  sq_step (by norm_num) pSeventeenB4s125 ⟨
    6*X^32 + 46*X^31 + 50*X^30 + 10*X^29 + 10*X^28 + 8*X^27 + 38*X^26 + 27*X^25 + 2*X^24 + 3*X^23 +
      17*X^21 + 14*X^20 + 43*X^19 + 19*X^18 + 48*X^17 + 23*X^16 + 14*X^15 + 33*X^14 + 41*X^13 +
      65*X^12 + 54*X^11 + 37*X^10 + 46*X^9 + 41*X^8 + 36*X^7 + 54*X^6 + 42*X^5 + 61*X^4 + 31*X^3 +
      7*X^2 + 58*X + 20,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s127 : XPow fSeventeenB4 11477672409657157652861819
    (16*X^33 + 38*X^32 + 43*X^31 + 63*X^30 + 62*X^29 + 62*X^28 + 41*X^27 + 65*X^26 + 4*X^25 + 24*X^24 +
      23*X^22 + 5*X^21 + 35*X^20 + 13*X^18 + 40*X^17 + 31*X^16 + 10*X^15 + 22*X^14 + X^13 + 35*X^12 +
      61*X^11 + 28*X^10 + 31*X^9 + 16*X^8 + X^7 + 14*X^6 + 27*X^5 + 47*X^4 + 57*X^3 + 32*X^2 + 47*X +
      44) :=
  mul_step (by norm_num) pSeventeenB4s126 pSeventeenB41 ⟨
    43,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s128 : XPow fSeventeenB4 22955344819314315305723638
    (47*X^33 + 46*X^31 + 49*X^30 + 58*X^29 + 65*X^28 + 33*X^27 + 53*X^26 + 2*X^25 + 60*X^24 + 55*X^23 +
      66*X^22 + 9*X^21 + 46*X^20 + 30*X^19 + 41*X^18 + 24*X^17 + 57*X^16 + 9*X^15 + 19*X^14 + 6*X^13 +
      40*X^12 + 43*X^11 + 49*X^10 + 26*X^9 + 65*X^7 + 47*X^6 + 6*X^5 + 46*X^4 + 15*X^3 + 64*X^2 +
      36*X + 7) :=
  sq_step (by norm_num) pSeventeenB4s127 ⟨
    55*X^32 + 53*X^31 + 34*X^30 + 33*X^29 + 5*X^28 + 53*X^27 + 47*X^26 + 44*X^25 + 47*X^24 + 7*X^23 +
      59*X^22 + 13*X^21 + 23*X^20 + 44*X^19 + 48*X^18 + 12*X^17 + 51*X^16 + 52*X^15 + 4*X^14 +
      26*X^13 + 26*X^12 + 4*X^11 + 55*X^10 + 51*X^9 + 43*X^8 + 43*X^7 + 4*X^6 + 9*X^5 + 22*X^4 +
      20*X^3 + 55*X^2 + 63*X + 35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s129 : XPow fSeventeenB4 45910689638628630611447276
    (5*X^33 + 41*X^32 + 9*X^31 + 5*X^30 + 60*X^29 + 34*X^28 + 8*X^27 + 37*X^26 + 23*X^25 + 28*X^24 +
      5*X^23 + 3*X^22 + 13*X^21 + 44*X^20 + 38*X^19 + 4*X^18 + 44*X^17 + 13*X^16 + 64*X^15 + 28*X^14 +
      47*X^13 + 41*X^12 + 5*X^11 + 17*X^10 + 31*X^9 + 34*X^8 + 29*X^7 + 65*X^6 + 28*X^5 + 31*X^4 +
      21*X^3 + 26*X^2 + 17) :=
  sq_step (by norm_num) pSeventeenB4s128 ⟨
    65*X^32 + 63*X^31 + 15*X^30 + 9*X^29 + 54*X^28 + 51*X^27 + 46*X^26 + 14*X^25 + 18*X^24 + 39*X^23 +
      26*X^22 + 50*X^21 + 16*X^20 + 17*X^19 + 19*X^18 + 11*X^17 + 25*X^16 + 41*X^15 + 39*X^14 +
      2*X^13 + 29*X^12 + 44*X^11 + 29*X^10 + 62*X^9 + 50*X^8 + 63*X^7 + X^6 + 61*X^5 + 36*X^4 +
      42*X^3 + 16*X^2 + 34*X + 54,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s130 : XPow fSeventeenB4 91821379277257261222894552
    (17*X^33 + 52*X^32 + 17*X^31 + 19*X^30 + 27*X^29 + 6*X^28 + 24*X^27 + 56*X^26 + 56*X^25 + 12*X^24 +
      44*X^23 + 53*X^22 + 13*X^21 + 8*X^20 + 45*X^19 + 57*X^18 + 33*X^17 + 28*X^16 + 58*X^15 +
      60*X^14 + 56*X^13 + 59*X^12 + 40*X^11 + 13*X^10 + 31*X^9 + 49*X^8 + 19*X^7 + 66*X^6 + 33*X^5 +
      25*X^4 + X^3 + 36*X^2 + 4*X + 3) :=
  sq_step (by norm_num) pSeventeenB4s129 ⟨
    25*X^32 + 58*X^31 + 6*X^30 + 31*X^29 + 43*X^28 + 51*X^27 + 45*X^26 + 66*X^25 + 7*X^24 + 65*X^23 +
      61*X^22 + 55*X^21 + 12*X^20 + 18*X^19 + 44*X^18 + 40*X^17 + 23*X^16 + 21*X^15 + 65*X^14 +
      21*X^13 + 27*X^12 + 47*X^11 + 11*X^10 + 45*X^9 + 60*X^8 + 37*X^7 + 61*X^6 + 58*X^5 + 63*X^4 +
      64*X^3 + 48*X^2 + 26*X + 22,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s131 : XPow fSeventeenB4 183642758554514522445789104
    (20*X^33 + 55*X^32 + 44*X^31 + 59*X^30 + 39*X^29 + 30*X^28 + 13*X^27 + 29*X^26 + 38*X^25 + 59*X^24 +
      58*X^23 + 15*X^22 + 11*X^21 + 6*X^20 + 63*X^19 + 27*X^18 + 38*X^17 + 26*X^16 + 54*X^15 +
      48*X^14 + 64*X^13 + 66*X^12 + 18*X^11 + 7*X^10 + 7*X^9 + 57*X^8 + 55*X^7 + 9*X^6 + 44*X^5 +
      25*X^4 + 56*X^3 + 18*X^2 + 55*X + 63) :=
  sq_step (by norm_num) pSeventeenB4s130 ⟨
    21*X^32 + X^31 + 37*X^30 + 19*X^29 + 21*X^28 + 26*X^27 + 62*X^26 + 14*X^25 + 60*X^24 + 39*X^23 +
      17*X^22 + 15*X^21 + 44*X^20 + 53*X^19 + 11*X^18 + 20*X^17 + 9*X^15 + 16*X^13 + 59*X^12 +
      64*X^11 + 58*X^10 + 57*X^9 + 14*X^8 + 24*X^7 + X^6 + 29*X^5 + 32*X^4 + 45*X^3 + 62*X^2 + 63*X +
      1,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s132 : XPow fSeventeenB4 183642758554514522445789105
    (28*X^33 + 40*X^32 + 40*X^31 + 59*X^30 + 16*X^29 + 39*X^28 + 25*X^27 + 9*X^26 + 16*X^25 + 44*X^24 +
      3*X^23 + 58*X^22 + 47*X^21 + 66*X^20 + 12*X^19 + 64*X^18 + X^17 + 24*X^16 + 39*X^15 + 13*X^14 +
      59*X^13 + 35*X^12 + 9*X^11 + 51*X^9 + 59*X^8 + 58*X^7 + 59*X^6 + 2*X^5 + 65*X^4 + 5*X^3 +
      31*X^2 + 45*X + 8) :=
  mul_step (by norm_num) pSeventeenB4s131 pSeventeenB41 ⟨
    20,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s133 : XPow fSeventeenB4 367285517109029044891578210
    (66*X^33 + 59*X^32 + 48*X^31 + 64*X^30 + 32*X^29 + 61*X^28 + 10*X^27 + 10*X^26 + 6*X^25 + 36*X^24 +
      X^23 + 37*X^22 + 11*X^21 + 14*X^20 + 11*X^19 + 17*X^18 + 45*X^17 + 3*X^16 + 30*X^15 + 39*X^14 +
      15*X^13 + 30*X^12 + 14*X^11 + 61*X^10 + 32*X^9 + 63*X^8 + 62*X^7 + 31*X^6 + 35*X^5 + 38*X^4 +
      8*X^3 + 26*X^2 + 28*X + 13) :=
  sq_step (by norm_num) pSeventeenB4s132 ⟨
    47*X^32 + 56*X^31 + 3*X^30 + 59*X^29 + 51*X^28 + 30*X^27 + 57*X^26 + 17*X^25 + 24*X^24 + 45*X^23 +
      65*X^22 + 17*X^21 + 57*X^20 + 41*X^19 + 7*X^18 + 12*X^17 + 9*X^16 + 15*X^15 + 42*X^14 +
      63*X^13 + 18*X^12 + X^11 + 3*X^10 + 21*X^9 + 7*X^8 + 3*X^7 + 20*X^6 + 49*X^5 + 44*X^4 + X^3 +
      8*X^2 + 35*X + 40,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s134 : XPow fSeventeenB4 367285517109029044891578211
    (57*X^33 + 8*X^32 + 8*X^31 + 31*X^30 + 55*X^29 + 2*X^28 + 37*X^27 + 51*X^26 + 8*X^25 + 62*X^24 +
      51*X^23 + 12*X^22 + 22*X^21 + 41*X^20 + X^19 + 37*X^18 + 21*X^17 + 65*X^16 + 16*X^15 + 41*X^14 +
      27*X^13 + 50*X^12 + 14*X^11 + 29*X^10 + 3*X^9 + 35*X^8 + 52*X^7 + 51*X^6 + 9*X^5 + 31*X^4 +
      30*X^3 + 56*X^2 + 34*X + 13) :=
  mul_step (by norm_num) pSeventeenB4s133 pSeventeenB41 ⟨
    66,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s135 : XPow fSeventeenB4 734571034218058089783156422
    (27*X^33 + 13*X^32 + 53*X^31 + 64*X^30 + 21*X^29 + 21*X^28 + 21*X^27 + 34*X^26 + 47*X^25 + 20*X^24 +
      6*X^23 + 57*X^22 + 24*X^21 + 40*X^20 + 32*X^19 + 62*X^18 + 27*X^17 + 7*X^16 + 2*X^15 + 22*X^14 +
      65*X^13 + 36*X^12 + 28*X^11 + 23*X^10 + 18*X^9 + 25*X^7 + 28*X^6 + 26*X^5 + 65*X^4 + 43*X^3 +
      44*X^2 + 37*X + 4) :=
  sq_step (by norm_num) pSeventeenB4s134 ⟨
    33*X^32 + 40*X^31 + 31*X^30 + 3*X^29 + 31*X^28 + 8*X^27 + 10*X^26 + 18*X^25 + 65*X^24 + 56*X^23 +
      15*X^22 + 14*X^21 + 37*X^20 + 19*X^19 + 54*X^18 + 15*X^17 + 49*X^16 + 47*X^15 + 35*X^14 +
      65*X^13 + 51*X^12 + 11*X^11 + 32*X^10 + 31*X^9 + 7*X^8 + 63*X^7 + 34*X^6 + 64*X^5 + 54*X^4 +
      29*X^3 + 10*X^2 + 28*X + 23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s136 : XPow fSeventeenB4 734571034218058089783156423
    (61*X^32 + 35*X^31 + 48*X^30 + 49*X^29 + 36*X^28 + 42*X^27 + 38*X^26 + 39*X^25 + 34*X^24 + 14*X^23 +
      64*X^22 + 25*X^21 + 26*X^20 + 25*X^19 + 42*X^18 + 57*X^17 + 62*X^16 + 40*X^15 + 33*X^14 +
      50*X^13 + 61*X^12 + 19*X^11 + 32*X^10 + 12*X^9 + 17*X^8 + 64*X^7 + 63*X^6 + 44*X^5 + 25*X^4 +
      3*X^3 + 18*X^2 + 40*X + 51) :=
  mul_step (by norm_num) pSeventeenB4s135 pSeventeenB41 ⟨
    27,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s137 : XPow fSeventeenB4 1469142068436116179566312846
    (17*X^33 + 53*X^32 + 3*X^31 + 66*X^30 + 52*X^29 + 36*X^28 + 25*X^27 + 9*X^26 + 40*X^25 + 36*X^24 +
      26*X^23 + 51*X^22 + 31*X^21 + 54*X^20 + 48*X^19 + 47*X^18 + 54*X^17 + 36*X^16 + 42*X^15 +
      51*X^14 + 30*X^13 + 28*X^12 + 25*X^11 + 47*X^10 + 10*X^9 + 38*X^8 + 50*X^7 + 6*X^6 + 21*X^5 +
      58*X^4 + 5*X^3 + 13*X^2 + 42*X + 8) :=
  sq_step (by norm_num) pSeventeenB4s136 ⟨
    36*X^30 + 54*X^29 + 53*X^28 + 19*X^27 + X^26 + 60*X^24 + 10*X^23 + 7*X^22 + 48*X^21 + 41*X^20 +
      19*X^19 + 10*X^18 + 16*X^17 + 35*X^16 + 58*X^15 + 4*X^14 + 66*X^13 + 43*X^12 + 27*X^11 +
      9*X^10 + 35*X^9 + 24*X^8 + 19*X^7 + 44*X^6 + 26*X^5 + 62*X^4 + 44*X^2 + 34*X + 50,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s138 : XPow fSeventeenB4 1469142068436116179566312847
    (20*X^33 + 13*X^32 + 13*X^31 + 2*X^30 + 4*X^29 + 27*X^28 + 19*X^27 + 12*X^26 + 43*X^25 + 61*X^24 +
      14*X^23 + 14*X^22 + 52*X^21 + 7*X^20 + 51*X^19 + 56*X^18 + 65*X^17 + 50*X^16 + 40*X^15 +
      57*X^14 + 12*X^13 + 16*X^12 + 42*X^11 + 61*X^10 + 53*X^9 + 40*X^8 + 51*X^7 + 17*X^6 + 15*X^5 +
      16*X^4 + 12*X^3 + 35*X^2 + 53*X + 47) :=
  mul_step (by norm_num) pSeventeenB4s137 pSeventeenB41 ⟨
    17,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s139 : XPow fSeventeenB4 2938284136872232359132625694
    (47*X^33 + 26*X^32 + 30*X^31 + 2*X^30 + 37*X^29 + 57*X^28 + 13*X^27 + 32*X^26 + 27*X^24 + 12*X^23 +
      5*X^22 + 47*X^21 + 36*X^19 + 20*X^18 + 59*X^17 + 66*X^16 + 23*X^15 + 31*X^14 + 19*X^13 +
      30*X^12 + 17*X^11 + 47*X^10 + 59*X^9 + 60*X^8 + 52*X^7 + 51*X^6 + 56*X^5 + 13*X^4 + 13*X^3 +
      48*X^2 + 35*X + 39) :=
  sq_step (by norm_num) pSeventeenB4s138 ⟨
    65*X^32 + 47*X^31 + 33*X^30 + 41*X^29 + 58*X^28 + 51*X^27 + 21*X^26 + 53*X^25 + 12*X^24 + 55*X^23 +
      18*X^22 + 30*X^21 + 39*X^20 + 37*X^19 + 61*X^18 + 57*X^17 + 46*X^16 + 2*X^15 + 15*X^14 +
      6*X^13 + 38*X^12 + 50*X^11 + 30*X^10 + 17*X^9 + 41*X^8 + 17*X^7 + 36*X^6 + 2*X^5 + 61*X^4 +
      62*X^3 + 59*X^2 + 32*X + 2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s140 : XPow fSeventeenB4 5876568273744464718265251388
    (43*X^33 + 39*X^32 + 60*X^31 + 22*X^30 + 53*X^29 + 34*X^28 + 38*X^27 + 56*X^26 + 32*X^25 + 39*X^24 +
      17*X^23 + 6*X^22 + 5*X^21 + 4*X^20 + 61*X^19 + 51*X^17 + 12*X^16 + 45*X^15 + 51*X^14 + 58*X^13 +
      27*X^12 + 29*X^10 + 66*X^9 + 4*X^8 + 64*X^7 + 61*X^6 + 5*X^5 + 3*X^4 + 31*X^3 + 22*X^2 + 49) :=
  sq_step (by norm_num) pSeventeenB4s139 ⟨
    65*X^32 + 28*X^31 + 55*X^30 + 52*X^29 + 44*X^28 + 3*X^27 + 39*X^26 + 55*X^25 + 46*X^24 + 31*X^23 +
      43*X^22 + 9*X^21 + 23*X^20 + 47*X^19 + 43*X^18 + X^17 + 6*X^16 + 44*X^15 + 30*X^14 + 11*X^13 +
      41*X^12 + 55*X^11 + 51*X^10 + 55*X^9 + 16*X^8 + 3*X^7 + 63*X^6 + 48*X^5 + 34*X^4 + 51*X^3 +
      42*X^2 + 37*X + 5,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s141 : XPow fSeventeenB4 5876568273744464718265251389
    (58*X^33 + 38*X^32 + 18*X^31 + 29*X^30 + 24*X^29 + 47*X^28 + 34*X^27 + 40*X^26 + 37*X^25 + 7*X^24 +
      7*X^23 + 29*X^22 + 62*X^21 + 44*X^20 + 18*X^19 + 60*X^18 + 42*X^17 + 14*X^16 + 35*X^15 +
      12*X^14 + 22*X^13 + 60*X^12 + 40*X^11 + 61*X^10 + 38*X^9 + 19*X^8 + 29*X^7 + 54*X^6 + 44*X^5 +
      47*X^4 + 51*X^3 + 2*X^2 + 17*X + 44) :=
  mul_step (by norm_num) pSeventeenB4s140 pSeventeenB41 ⟨
    43,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s142 : XPow fSeventeenB4 11753136547488929436530502778
    (7*X^33 + 4*X^31 + 53*X^30 + 66*X^29 + 29*X^28 + 2*X^27 + 33*X^26 + 41*X^25 + 23*X^24 + 8*X^23 +
      3*X^22 + 13*X^21 + 64*X^20 + 15*X^19 + 24*X^18 + 36*X^17 + 59*X^16 + 22*X^15 + 11*X^14 +
      52*X^13 + 63*X^12 + 66*X^11 + 59*X^10 + 10*X^9 + 45*X^8 + 27*X^7 + 25*X^6 + 48*X^5 + 21*X^4 +
      51*X^3 + 32*X^2 + 43*X + 5) :=
  sq_step (by norm_num) pSeventeenB4s141 ⟨
    14*X^32 + 14*X^31 + 33*X^30 + 45*X^29 + 16*X^28 + 38*X^27 + 23*X^26 + 17*X^25 + 10*X^24 + 59*X^23 +
      20*X^22 + 52*X^21 + 49*X^20 + 57*X^19 + 9*X^18 + 3*X^17 + 52*X^16 + 28*X^15 + 19*X^14 +
      58*X^13 + 29*X^12 + 30*X^11 + 2*X^10 + 41*X^9 + 7*X^8 + 18*X^7 + 56*X^6 + 11*X^5 + 24*X^4 +
      58*X^3 + 48*X^2 + 53*X + 30,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s143 : XPow fSeventeenB4 11753136547488929436530502779
    (14*X^33 + 16*X^32 + 43*X^31 + 6*X^30 + 4*X^29 + 58*X^28 + 45*X^27 + 61*X^26 + 18*X^25 + 50*X^24 +
      39*X^23 + 6*X^22 + 8*X^21 + 6*X^20 + 2*X^19 + 25*X^18 + 45*X^16 + 38*X^15 + 4*X^14 + 17*X^13 +
      15*X^12 + 53*X^11 + 31*X^10 + 63*X^9 + 15*X^8 + 12*X^7 + 3*X^6 + 23*X^5 + 24*X^4 + 4*X^3 +
      48*X^2 + 59*X + 43) :=
  mul_step (by norm_num) pSeventeenB4s142 pSeventeenB41 ⟨
    7,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s144 : XPow fSeventeenB4 23506273094977858873061005558
    (59*X^33 + 60*X^32 + 20*X^31 + 61*X^30 + 19*X^29 + 26*X^28 + 8*X^27 + 30*X^26 + 12*X^25 + 48*X^24 +
      27*X^23 + 10*X^22 + 18*X^21 + 59*X^20 + 50*X^19 + 35*X^18 + 21*X^17 + 35*X^16 + 27*X^15 + X^14 +
      66*X^13 + 9*X^12 + 37*X^11 + 53*X^10 + 63*X^9 + 61*X^8 + 26*X^7 + 10*X^6 + 21*X^5 + 8*X^4 +
      10*X^3 + 43*X^2 + 8*X + 11) :=
  sq_step (by norm_num) pSeventeenB4s143 ⟨
    62*X^32 + 36*X^31 + 59*X^30 + 8*X^29 + 41*X^28 + 17*X^27 + 24*X^26 + 54*X^24 + 19*X^23 + 8*X^22 +
      44*X^21 + 43*X^20 + 63*X^19 + 42*X^18 + 61*X^17 + 65*X^16 + 56*X^15 + 7*X^14 + 2*X^13 +
      53*X^12 + 36*X^11 + 42*X^10 + 51*X^9 + 27*X^8 + 27*X^7 + 29*X^6 + 35*X^5 + 50*X^4 + 43*X^3 +
      16*X^2 + 61*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s145 : XPow fSeventeenB4 23506273094977858873061005559
    (44*X^33 + 35*X^32 + 15*X^31 + 11*X^30 + 45*X^29 + 11*X^28 + 45*X^27 + 37*X^26 + 25*X^25 + 46*X^24 +
      55*X^23 + 26*X^22 + 56*X^21 + 22*X^20 + 41*X^19 + 24*X^18 + 45*X^17 + 39*X^16 + 18*X^15 +
      6*X^14 + 52*X^13 + 57*X^12 + 12*X^11 + 39*X^10 + 50*X^9 + 11*X^8 + 44*X^7 + 15*X^6 + 44*X^5 +
      60*X^4 + 8*X^3 + 31*X^2 + 45*X + 37) :=
  mul_step (by norm_num) pSeventeenB4s144 pSeventeenB41 ⟨
    59,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s146 : XPow fSeventeenB4 47012546189955717746122011118
    (35*X^33 + 40*X^32 + 49*X^31 + 34*X^30 + 3*X^29 + 42*X^28 + 30*X^27 + 19*X^26 + 29*X^25 + 19*X^24 +
      27*X^23 + 46*X^22 + 38*X^21 + 57*X^20 + 50*X^19 + 9*X^18 + 27*X^17 + 65*X^16 + 40*X^15 + X^14 +
      8*X^13 + 5*X^12 + 29*X^11 + 54*X^9 + 22*X^8 + 41*X^7 + 15*X^6 + 60*X^5 + 60*X^4 + 56*X^3 +
      26*X^2 + 21*X + 49) :=
  sq_step (by norm_num) pSeventeenB4s145 ⟨
    60*X^32 + 51*X^31 + 22*X^30 + 25*X^29 + 24*X^28 + 37*X^27 + 63*X^26 + 40*X^25 + 39*X^24 + 38*X^22 +
      3*X^21 + 47*X^20 + 36*X^19 + 66*X^18 + 48*X^17 + 37*X^16 + 29*X^15 + 2*X^14 + 2*X^13 + 49*X^12 +
      21*X^11 + 37*X^10 + 52*X^9 + 43*X^8 + X^7 + 48*X^6 + 39*X^5 + 14*X^4 + 61*X^3 + 35*X^2 + 14*X +
      50,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s147 : XPow fSeventeenB4 47012546189955717746122011119
    (43*X^33 + 42*X^32 + 51*X^31 + 38*X^30 + 51*X^29 + 42*X^28 + 12*X^27 + 62*X^26 + 61*X^25 + 36*X^24 +
      25*X^23 + 3*X^22 + 45*X^21 + 5*X^20 + 33*X^19 + 39*X^18 + 38*X^17 + 21*X^16 + 2*X^15 + 36*X^14 +
      43*X^13 + 42*X^12 + 37*X^11 + 25*X^10 + 45*X^9 + 48*X^8 + 17*X^7 + 36*X^6 + 3*X^5 + 55*X^4 +
      20*X^3 + 46*X^2 + 51*X + 14) :=
  mul_step (by norm_num) pSeventeenB4s146 pSeventeenB41 ⟨
    35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s148 : XPow fSeventeenB4 94025092379911435492244022238
    (27*X^33 + 39*X^32 + 46*X^31 + 4*X^30 + 28*X^29 + 51*X^28 + 38*X^27 + 6*X^26 + 35*X^25 + 43*X^24 +
      59*X^23 + 47*X^22 + 26*X^21 + 50*X^20 + 11*X^19 + 15*X^18 + 4*X^17 + 19*X^16 + 15*X^15 +
      56*X^14 + 11*X^13 + 32*X^12 + 5*X^11 + 42*X^10 + 47*X^9 + 22*X^8 + 61*X^7 + 14*X^6 + 24*X^5 +
      64*X^4 + 32*X^3 + 64*X^2 + 51*X + 16) :=
  sq_step (by norm_num) pSeventeenB4s147 ⟨
    40*X^32 + 7*X^31 + 59*X^30 + 6*X^29 + 52*X^28 + 56*X^27 + 18*X^26 + 63*X^25 + 58*X^24 + 31*X^23 +
      12*X^22 + 10*X^21 + 29*X^20 + 33*X^19 + 13*X^18 + 21*X^17 + 2*X^16 + 66*X^15 + 48*X^14 +
      22*X^13 + 2*X^12 + 64*X^11 + 25*X^10 + 29*X^9 + 6*X^8 + 37*X^7 + 47*X^6 + 47*X^5 + 39*X^4 +
      46*X^3 + 18*X^2 + 34*X + 19,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s149 : XPow fSeventeenB4 188050184759822870984488044476
    (8*X^33 + 7*X^32 + 27*X^31 + 54*X^30 + 52*X^29 + 10*X^28 + 15*X^27 + 22*X^26 + 39*X^25 + 58*X^24 +
      20*X^23 + 13*X^22 + 57*X^21 + 51*X^20 + 12*X^19 + 12*X^18 + 9*X^17 + 26*X^16 + 40*X^15 +
      17*X^14 + 45*X^12 + 9*X^11 + 21*X^10 + 37*X^9 + 51*X^8 + 40*X^7 + 62*X^6 + 2*X^5 + 9*X^4 +
      55*X^3 + 30*X^2 + 6*X + 25) :=
  sq_step (by norm_num) pSeventeenB4s148 ⟨
    59*X^32 + 13*X^31 + 26*X^30 + 42*X^29 + 22*X^28 + 9*X^27 + 53*X^26 + 35*X^25 + 47*X^24 + 65*X^23 +
      52*X^22 + 18*X^21 + 48*X^20 + 4*X^19 + 22*X^18 + 7*X^17 + 5*X^16 + 48*X^15 + 42*X^14 + 31*X^13 +
      3*X^12 + 49*X^11 + 60*X^10 + 12*X^9 + 55*X^8 + 58*X^7 + 39*X^6 + 36*X^5 + 36*X^4 + 22*X^3 +
      62*X^2 + 4*X + 59,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s150 : XPow fSeventeenB4 188050184759822870984488044477
    (23*X^33 + 12*X^32 + 33*X^31 + 60*X^30 + 58*X^29 + 12*X^28 + 7*X^27 + 14*X^26 + 14*X^25 + X^24 +
      35*X^23 + 49*X^22 + 54*X^21 + 40*X^20 + 6*X^19 + 6*X^18 + 16*X^17 + 28*X^16 + 60*X^14 + 2*X^13 +
      56*X^12 + 62*X^11 + 61*X^10 + 62*X^9 + 55*X^8 + 28*X^7 + 8*X^6 + 40*X^5 + 5*X^4 + 65*X^3 +
      50*X^2 + 58*X + 30) :=
  mul_step (by norm_num) pSeventeenB4s149 pSeventeenB41 ⟨
    8,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s151 : XPow fSeventeenB4 376100369519645741968976088954
    (15*X^33 + 34*X^32 + 32*X^31 + 13*X^30 + 64*X^29 + 36*X^28 + 32*X^27 + 64*X^26 + 9*X^25 + 7*X^24 +
      5*X^22 + 37*X^21 + 31*X^20 + 3*X^19 + 22*X^18 + 56*X^17 + 28*X^16 + 4*X^15 + 3*X^14 + 65*X^13 +
      29*X^11 + 57*X^10 + 19*X^9 + 60*X^8 + 39*X^7 + 36*X^6 + 30*X^5 + 15*X^4 + 8*X^3 + 11*X^2 +
      54*X + 55) :=
  sq_step (by norm_num) pSeventeenB4s150 ⟨
    60*X^32 + 2*X^31 + 46*X^30 + 49*X^29 + 4*X^28 + 23*X^27 + 2*X^26 + 58*X^25 + 14*X^24 + 18*X^23 +
      2*X^22 + 42*X^21 + 23*X^20 + 21*X^19 + 14*X^18 + 42*X^17 + 66*X^16 + 47*X^15 + 36*X^14 +
      50*X^13 + 3*X^12 + 65*X^11 + 65*X^10 + 60*X^9 + 34*X^8 + 9*X^7 + 58*X^6 + 29*X^5 + 12*X^3 +
      47*X^2 + 40*X + 65,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s152 : XPow fSeventeenB4 752200739039291483937952177908
    (24*X^33 + 31*X^32 + 22*X^31 + 10*X^30 + 31*X^29 + 57*X^28 + 37*X^27 + 65*X^26 + 23*X^25 + 6*X^24 +
      43*X^22 + 50*X^21 + 17*X^20 + 33*X^19 + 30*X^18 + 26*X^17 + 56*X^16 + 37*X^15 + 30*X^14 +
      54*X^13 + 26*X^12 + 55*X^11 + 27*X^10 + 20*X^9 + 31*X^8 + 42*X^6 + 8*X^5 + 22*X^4 + 7*X^3 +
      44*X^2 + 43*X + 15) :=
  sq_step (by norm_num) pSeventeenB4s151 ⟨
    24*X^32 + 63*X^31 + 53*X^30 + 37*X^29 + 60*X^28 + 51*X^27 + 6*X^26 + 19*X^25 + 31*X^24 + 53*X^23 +
      52*X^22 + 56*X^21 + 23*X^20 + 43*X^19 + 40*X^18 + 9*X^17 + 7*X^16 + 46*X^15 + 20*X^14 +
      44*X^13 + 50*X^12 + 26*X^11 + 62*X^10 + 16*X^9 + 25*X^8 + 25*X^7 + 38*X^6 + 29*X^5 + 35*X^4 +
      24*X^3 + 26*X^2 + 34*X + 46,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s153 : XPow fSeventeenB4 1504401478078582967875904355816
    (59*X^33 + 25*X^32 + 22*X^31 + 28*X^30 + 45*X^29 + 27*X^28 + 3*X^27 + 30*X^26 + 29*X^25 + 33*X^24 +
      45*X^23 + 50*X^22 + 44*X^21 + 8*X^20 + 43*X^19 + 37*X^17 + 18*X^16 + 2*X^15 + 23*X^14 +
      37*X^13 + 37*X^12 + 48*X^11 + 57*X^10 + 56*X^9 + 29*X^8 + 28*X^7 + 32*X^6 + 61*X^5 + 11*X^4 +
      43*X^3 + 45*X^2 + 2*X + 59) :=
  sq_step (by norm_num) pSeventeenB4s152 ⟨
    40*X^32 + 27*X^31 + 53*X^30 + 44*X^29 + 54*X^28 + 17*X^27 + 41*X^26 + 34*X^25 + 21*X^24 + 55*X^23 +
      34*X^22 + 15*X^21 + 31*X^20 + 36*X^19 + 24*X^18 + 45*X^17 + 15*X^16 + 65*X^15 + 37*X^14 +
      51*X^13 + 40*X^12 + 5*X^11 + 60*X^10 + 23*X^9 + 16*X^8 + 12*X^7 + 49*X^6 + 49*X^5 + 64*X^4 +
      44*X^3 + 45*X^2 + 17*X + 54,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s154 : XPow fSeventeenB4 1504401478078582967875904355817
    (9*X^33 + 37*X^32 + 49*X^31 + 37*X^30 + 46*X^29 + 6*X^28 + 45*X^27 + 54*X^26 + 10*X^25 + 64*X^24 +
      28*X^23 + 52*X^22 + 5*X^21 + 15*X^20 + 6*X^19 + 40*X^18 + 28*X^17 + 14*X^16 + 40*X^15 +
      44*X^14 + 13*X^13 + X^12 + 16*X^11 + 32*X^10 + 18*X^9 + 13*X^8 + 66*X^7 + 55*X^6 + 47*X^5 +
      26*X^4 + 10*X^3 + 25*X^2 + 26*X + 37) :=
  mul_step (by norm_num) pSeventeenB4s153 pSeventeenB41 ⟨
    59,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s155 : XPow fSeventeenB4 3008802956157165935751808711634
    (52*X^33 + 45*X^32 + 7*X^31 + 30*X^30 + 41*X^29 + 54*X^27 + 53*X^26 + 7*X^25 + 20*X^24 + 31*X^23 +
      49*X^22 + 3*X^21 + 32*X^20 + 39*X^19 + 22*X^18 + 51*X^17 + 60*X^16 + 65*X^15 + 39*X^14 +
      7*X^13 + 39*X^12 + 11*X^11 + 21*X^10 + 50*X^9 + 44*X^8 + 28*X^7 + 55*X^6 + 31*X^5 + 47*X^4 +
      63*X^3 + 18*X^2 + 54*X + 65) :=
  sq_step (by norm_num) pSeventeenB4s154 ⟨
    14*X^32 + 24*X^31 + 45*X^30 + 29*X^29 + 4*X^28 + 13*X^27 + 63*X^26 + 31*X^25 + 48*X^24 + 25*X^23 +
      5*X^22 + 37*X^21 + 3*X^20 + 13*X^19 + 4*X^18 + 46*X^15 + 34*X^14 + 3*X^13 + 44*X^12 + 56*X^11 +
      48*X^10 + 61*X^9 + 53*X^8 + 63*X^7 + 14*X^6 + 17*X^5 + 52*X^4 + 21*X^3 + 42*X^2 + 50*X + 23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s156 : XPow fSeventeenB4 3008802956157165935751808711635
    (15*X^33 + 10*X^32 + 61*X^31 + 26*X^30 + 44*X^29 + X^28 + 56*X^27 + 12*X^26 + 2*X^25 + 8*X^24 +
      58*X^23 + 18*X^22 + 18*X^21 + 20*X^20 + 50*X^19 + 65*X^18 + 62*X^17 + 54*X^16 + 29*X^15 +
      62*X^14 + 61*X^13 + 15*X^12 + 53*X^11 + 5*X^10 + 15*X^9 + 25*X^8 + 35*X^7 + 3*X^6 + 14*X^5 +
      6*X^4 + 11*X^3 + 5*X^2 + 45*X + 61) :=
  mul_step (by norm_num) pSeventeenB4s155 pSeventeenB41 ⟨
    52,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s157 : XPow fSeventeenB4 6017605912314331871503617423270
    (24*X^33 + 7*X^31 + 28*X^30 + 66*X^29 + 63*X^28 + 54*X^27 + 42*X^26 + 35*X^25 + 22*X^24 + 24*X^23 +
      25*X^22 + 6*X^21 + 50*X^20 + 31*X^19 + 65*X^18 + 66*X^17 + 36*X^16 + 58*X^15 + 60*X^14 +
      6*X^13 + 26*X^12 + 37*X^11 + 43*X^10 + 24*X^9 + 58*X^8 + 30*X^7 + 25*X^6 + 19*X^5 + 24*X^4 +
      38*X^3 + 60*X^2 + 41*X + 43) :=
  sq_step (by norm_num) pSeventeenB4s156 ⟨
    24*X^32 + 13*X^31 + 35*X^30 + 48*X^29 + 37*X^28 + 19*X^27 + 61*X^26 + 59*X^25 + 57*X^24 + 16*X^23 +
      31*X^22 + 19*X^21 + 35*X^20 + 32*X^19 + 7*X^18 + 20*X^17 + 45*X^16 + 27*X^15 + 4*X^14 +
      46*X^13 + 37*X^12 + 39*X^10 + 38*X^9 + 15*X^8 + 43*X^7 + 59*X^6 + 66*X^5 + 38*X^4 + 7*X^3 +
      60*X^2 + 43*X + 51,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s158 : XPow fSeventeenB4 6017605912314331871503617423271
    (48*X^33 + 29*X^32 + 32*X^31 + 23*X^30 + 6*X^29 + 45*X^28 + 64*X^27 + 27*X^26 + 24*X^25 + 34*X^24 +
      24*X^23 + 49*X^22 + 59*X^21 + 48*X^20 + 47*X^19 + 57*X^18 + 6*X^17 + 22*X^16 + 9*X^15 +
      52*X^14 + 31*X^13 + 44*X^12 + 32*X^11 + 29*X^10 + 24*X^9 + 8*X^8 + 57*X^7 + 37*X^6 + 50*X^5 +
      22*X^4 + 31*X^3 + 39*X^2 + 8*X + 23) :=
  mul_step (by norm_num) pSeventeenB4s157 pSeventeenB41 ⟨
    24,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s159 : XPow fSeventeenB4 12035211824628663743007234846542
    (7*X^33 + 36*X^32 + 31*X^31 + 46*X^30 + 29*X^29 + X^28 + 9*X^27 + 28*X^26 + 26*X^25 + 44*X^24 +
      45*X^23 + 15*X^22 + 4*X^21 + 56*X^20 + 63*X^19 + 59*X^18 + 45*X^17 + 65*X^16 + 22*X^15 +
      61*X^14 + 57*X^13 + 25*X^12 + 46*X^11 + 48*X^10 + 39*X^9 + 21*X^8 + 10*X^7 + 31*X^6 + 56*X^5 +
      63*X^4 + 65*X^3 + 60*X^2 + 15*X + 49) :=
  sq_step (by norm_num) pSeventeenB4s158 ⟨
    26*X^32 + 22*X^31 + 39*X^30 + 46*X^29 + 15*X^28 + 54*X^27 + 64*X^26 + 14*X^25 + 51*X^24 + 45*X^23 +
      56*X^22 + 13*X^21 + 61*X^20 + 6*X^19 + 56*X^18 + 24*X^17 + 3*X^16 + 6*X^15 + 45*X^14 + 32*X^13 +
      37*X^12 + 63*X^11 + 56*X^10 + 16*X^9 + 55*X^8 + 50*X^7 + 65*X^6 + 13*X^5 + 24*X^4 + 40*X^3 +
      50*X^2 + 2*X + 6,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s160 : XPow fSeventeenB4 24070423649257327486014469693084
    (6*X^33 + 13*X^32 + 13*X^31 + 47*X^30 + 13*X^29 + 29*X^28 + 59*X^27 + 25*X^26 + 26*X^25 + X^24 +
      36*X^23 + 3*X^22 + 13*X^21 + 4*X^20 + 28*X^19 + 41*X^18 + 5*X^17 + 66*X^16 + 54*X^15 + 14*X^14 +
      34*X^13 + X^12 + 47*X^11 + 54*X^10 + 28*X^9 + 3*X^8 + 13*X^7 + 58*X^6 + 5*X^5 + 19*X^4 +
      47*X^3 + 15*X^2 + 51*X + 29) :=
  sq_step (by norm_num) pSeventeenB4s159 ⟨
    49*X^32 + 66*X^31 + 3*X^30 + 25*X^29 + 18*X^28 + 19*X^27 + 26*X^26 + 14*X^25 + 64*X^24 + 6*X^23 +
      14*X^22 + 40*X^21 + 60*X^20 + 66*X^19 + 38*X^18 + 34*X^17 + 47*X^16 + 49*X^15 + 27*X^14 +
      35*X^13 + 37*X^12 + 65*X^11 + X^10 + 40*X^9 + 17*X^8 + 47*X^7 + 2*X^6 + 36*X^5 + 26*X^4 +
      18*X^3 + 36*X^2 + 61*X + 33,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s161 : XPow fSeventeenB4 48140847298514654972028939386168
    (5*X^33 + 53*X^32 + 25*X^31 + 5*X^30 + 30*X^29 + 23*X^28 + 42*X^27 + 9*X^26 + 26*X^25 + 6*X^24 +
      28*X^23 + 47*X^22 + 36*X^21 + 23*X^20 + 47*X^19 + 46*X^18 + 33*X^17 + 41*X^16 + 11*X^15 +
      55*X^14 + 23*X^13 + 16*X^12 + 15*X^11 + 7*X^10 + 33*X^9 + 27*X^8 + 2*X^7 + 24*X^6 + 53*X^5 +
      21*X^4 + 7*X^3 + 34*X^2 + 46*X + 22) :=
  sq_step (by norm_num) pSeventeenB4s160 ⟨
    36*X^32 + 27*X^31 + 10*X^30 + 65*X^29 + 7*X^28 + 32*X^27 + 11*X^26 + 49*X^25 + 20*X^24 + 53*X^23 +
      26*X^22 + 28*X^21 + 33*X^20 + 17*X^19 + 47*X^18 + 5*X^17 + 5*X^16 + 37*X^15 + 6*X^14 + 7*X^13 +
      9*X^12 + 64*X^11 + 16*X^10 + 34*X^9 + 26*X^8 + 7*X^7 + 23*X^6 + 11*X^5 + 4*X^4 + 56*X^3 +
      3*X^2 + 14*X + 63,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s162 : XPow fSeventeenB4 96281694597029309944057878772336
    (12*X^33 + 53*X^32 + 12*X^31 + X^30 + 21*X^29 + 21*X^28 + 30*X^27 + 65*X^26 + 41*X^25 + 41*X^24 +
      10*X^23 + 42*X^22 + 38*X^21 + 51*X^20 + 65*X^19 + 14*X^18 + 55*X^17 + 34*X^16 + 37*X^15 +
      33*X^14 + 64*X^13 + 24*X^12 + 9*X^11 + 63*X^10 + 63*X^9 + 28*X^8 + 60*X^7 + 8*X^5 + 63*X^4 +
      4*X^3 + 63*X^2 + 6*X + 44) :=
  sq_step (by norm_num) pSeventeenB4s161 ⟨
    25*X^32 + 44*X^31 + 60*X^30 + 17*X^29 + 13*X^28 + 14*X^27 + 42*X^26 + 48*X^25 + 60*X^24 + 19*X^23 +
      23*X^22 + 2*X^21 + 49*X^20 + 58*X^19 + 48*X^18 + 32*X^17 + 41*X^16 + 6*X^15 + 22*X^14 + 7*X^13 +
      16*X^12 + 62*X^11 + 63*X^10 + 51*X^9 + 27*X^8 + 39*X^7 + 29*X^6 + 39*X^5 + 58*X^4 + 29*X^3 +
      19*X^2 + 51*X + 39,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s163 : XPow fSeventeenB4 96281694597029309944057878772337
    (10*X^33 + 23*X^32 + 3*X^31 + 33*X^30 + 26*X^29 + 59*X^28 + 9*X^27 + 37*X^26 + 42*X^25 + 15*X^24 +
      8*X^23 + 26*X^22 + 22*X^21 + 40*X^20 + 5*X^19 + 17*X^18 + 19*X^17 + 19*X^16 + 41*X^15 +
      20*X^14 + 60*X^13 + 46*X^12 + 24*X^11 + 32*X^10 + 11*X^9 + 49*X^8 + 16*X^7 + 17*X^6 + 9*X^5 +
      63*X^4 + 15*X^3 + 5*X^2 + 60*X + 45) :=
  mul_step (by norm_num) pSeventeenB4s162 pSeventeenB41 ⟨
    12,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s164 : XPow fSeventeenB4 192563389194058619888115757544674
    (2*X^33 + 56*X^32 + 30*X^31 + 15*X^30 + 11*X^29 + 45*X^28 + 29*X^27 + 26*X^26 + 14*X^25 + 48*X^23 +
      53*X^22 + 27*X^21 + 36*X^20 + 58*X^19 + 47*X^18 + 40*X^17 + 17*X^16 + 22*X^15 + 63*X^14 +
      10*X^13 + 54*X^12 + 46*X^11 + 3*X^10 + 45*X^9 + 18*X^8 + 15*X^7 + 61*X^6 + 13*X^5 + 28*X^4 +
      19*X^3 + 38*X^2 + 41*X) :=
  sq_step (by norm_num) pSeventeenB4s163 ⟨
    33*X^32 + 57*X^31 + 13*X^30 + 61*X^29 + 18*X^28 + 3*X^27 + 56*X^26 + 14*X^25 + 31*X^24 + 39*X^23 +
      62*X^22 + 39*X^21 + X^20 + 58*X^19 + X^18 + 43*X^17 + 17*X^16 + 5*X^15 + 50*X^14 + 56*X^13 +
      16*X^12 + 63*X^11 + 15*X^10 + 60*X^9 + 24*X^8 + 21*X^7 + 57*X^6 + 35*X^5 + 8*X^4 + 54*X^3 +
      52*X^2 + 27*X + 63,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s165 : XPow fSeventeenB4 192563389194058619888115757544675
    (60*X^33 + 43*X^32 + 60*X^31 + 13*X^30 + 57*X^29 + 45*X^28 + 39*X^27 + 58*X^26 + 56*X^25 + 60*X^24 +
      25*X^23 + 25*X^22 + 20*X^21 + 65*X^20 + 12*X^19 + 56*X^18 + 48*X^17 + 19*X^16 + 42*X^15 +
      25*X^14 + 60*X^13 + 41*X^12 + 30*X^11 + 51*X^10 + 4*X^9 + 2*X^8 + 19*X^7 + 48*X^6 + 19*X^5 +
      40*X^4 + 30*X^3 + 52*X^2 + 25*X + 41) :=
  mul_step (by norm_num) pSeventeenB4s164 pSeventeenB41 ⟨
    2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s166 : XPow fSeventeenB4 385126778388117239776231515089350
    (32*X^33 + 22*X^32 + 29*X^31 + 52*X^30 + 49*X^29 + 30*X^28 + 37*X^27 + 21*X^26 + 52*X^25 + 15*X^24 +
      54*X^23 + 37*X^22 + 21*X^21 + 48*X^20 + 10*X^19 + 3*X^18 + 26*X^17 + 61*X^16 + 20*X^15 +
      59*X^14 + 11*X^13 + 14*X^12 + 46*X^11 + 37*X^10 + 57*X^9 + 20*X^8 + 8*X^7 + 10*X^6 + 24*X^5 +
      66*X^4 + 19*X^3 + 14*X^2 + 42*X + 52) :=
  sq_step (by norm_num) pSeventeenB4s165 ⟨
    49*X^32 + 32*X^31 + 18*X^30 + 60*X^29 + 35*X^28 + 55*X^27 + 60*X^26 + 8*X^25 + 55*X^24 + 23*X^23 +
      59*X^22 + 27*X^21 + 28*X^20 + 46*X^19 + 12*X^18 + 63*X^17 + 7*X^16 + 3*X^15 + 14*X^14 +
      58*X^13 + 27*X^12 + 29*X^11 + 65*X^10 + 63*X^9 + 16*X^8 + 3*X^7 + 47*X^6 + 27*X^5 + 8*X^4 +
      44*X^3 + 53*X^2 + 46*X + 48,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s167 : XPow fSeventeenB4 770253556776234479552463030178700
    (2*X^33 + 46*X^32 + 63*X^31 + 62*X^30 + 32*X^29 + 36*X^28 + 45*X^27 + 57*X^26 + 28*X^25 + 20*X^24 +
      3*X^23 + 13*X^22 + 8*X^21 + 20*X^20 + 57*X^19 + 26*X^18 + 4*X^17 + 56*X^16 + 2*X^15 + 21*X^14 +
      X^13 + 28*X^12 + 29*X^11 + 38*X^10 + 66*X^9 + 12*X^8 + 44*X^7 + 64*X^6 + 14*X^5 + 37*X^4 +
      58*X^3 + 36*X^2 + 60*X + 14) :=
  sq_step (by norm_num) pSeventeenB4s166 ⟨
    19*X^32 + 39*X^31 + 29*X^30 + 50*X^29 + 13*X^28 + 41*X^27 + 53*X^26 + 44*X^25 + 52*X^24 + 60*X^23 +
      40*X^22 + 64*X^21 + 32*X^20 + 47*X^19 + 15*X^18 + 43*X^17 + 42*X^16 + 17*X^15 + 44*X^14 +
      26*X^13 + 46*X^12 + 8*X^11 + 54*X^10 + 44*X^9 + 54*X^8 + 31*X^7 + 34*X^6 + 15*X^5 + 11*X^4 +
      13*X^2 + 11*X + 42,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s168 : XPow fSeventeenB4 1540507113552468959104926060357400
    (14*X^33 + 51*X^32 + 62*X^31 + 47*X^30 + 18*X^29 + 4*X^28 + 64*X^27 + 32*X^26 + 12*X^25 + X^24 +
      34*X^23 + 39*X^22 + 3*X^21 + 58*X^20 + 46*X^19 + 33*X^18 + 37*X^17 + 2*X^16 + 57*X^15 +
      49*X^14 + 40*X^13 + 34*X^12 + 45*X^11 + 49*X^10 + 8*X^9 + 17*X^8 + 47*X^7 + 51*X^6 + 24*X^5 +
      37*X^4 + 16*X^3 + 65*X^2 + 66*X + 63) :=
  sq_step (by norm_num) pSeventeenB4s167 ⟨
    4*X^32 + 58*X^31 + 31*X^30 + 7*X^29 + 36*X^28 + 5*X^27 + 20*X^26 + 66*X^25 + 25*X^24 + 49*X^23 +
      45*X^22 + 7*X^21 + 16*X^20 + 33*X^19 + 34*X^18 + 35*X^17 + 37*X^16 + 18*X^15 + 51*X^14 +
      2*X^13 + 52*X^12 + 58*X^11 + 41*X^10 + 5*X^9 + 2*X^8 + 55*X^7 + 59*X^6 + 24*X^5 + 37*X^4 +
      6*X^3 + 21*X^2 + 66*X + 36,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s169 : XPow fSeventeenB4 1540507113552468959104926060357401
    (12*X^33 + 19*X^32 + 27*X^31 + 32*X^30 + 21*X^29 + 42*X^28 + 56*X^27 + 52*X^26 + 58*X^25 + 51*X^24 +
      44*X^23 + 56*X^22 + 13*X^21 + 28*X^20 + 56*X^19 + 15*X^18 + 18*X^17 + 36*X^16 + 36*X^15 +
      11*X^14 + 9*X^13 + 10*X^12 + 37*X^11 + 50*X^10 + 53*X^9 + 23*X^8 + 25*X^7 + X^6 + 41*X^5 +
      29*X^4 + 9*X^3 + 9*X^2 + 37*X + 19) :=
  mul_step (by norm_num) pSeventeenB4s168 pSeventeenB41 ⟨
    14,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s170 : XPow fSeventeenB4 3081014227104937918209852120714802
    (41*X^33 + 64*X^32 + 18*X^31 + 56*X^30 + 51*X^28 + 5*X^27 + 42*X^26 + 34*X^25 + 11*X^24 + 37*X^23 +
      42*X^22 + 19*X^21 + 65*X^20 + 45*X^19 + 9*X^18 + 39*X^17 + 47*X^16 + 27*X^15 + 15*X^14 +
      16*X^13 + 26*X^12 + 2*X^11 + 33*X^10 + 54*X^9 + 31*X^8 + 38*X^7 + 35*X^6 + 2*X^5 + 40*X^4 +
      22*X^3 + 45*X^2 + 39*X + 32) :=
  sq_step (by norm_num) pSeventeenB4s169 ⟨
    10*X^32 + 7*X^31 + 16*X^30 + 53*X^29 + 46*X^28 + 9*X^27 + 12*X^26 + 34*X^25 + 41*X^24 + 4*X^23 +
      50*X^22 + 15*X^21 + 9*X^20 + 29*X^19 + X^18 + 8*X^17 + 39*X^16 + 60*X^14 + 65*X^13 + 38*X^12 +
      10*X^11 + 29*X^10 + 37*X^9 + 7*X^8 + 18*X^7 + 60*X^6 + 6*X^5 + 53*X^4 + 49*X^3 + 46*X^2 + 50*X +
      15,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s171 : XPow fSeventeenB4 6162028454209875836419704241429604
    (20*X^33 + 31*X^32 + 61*X^31 + 22*X^30 + 18*X^29 + 21*X^27 + 64*X^26 + 29*X^25 + 12*X^24 + 44*X^23 +
      4*X^22 + 48*X^21 + 4*X^20 + 14*X^19 + 55*X^18 + 17*X^17 + 21*X^16 + 36*X^15 + 57*X^14 +
      15*X^13 + 55*X^12 + 59*X^11 + 35*X^10 + 46*X^9 + 18*X^8 + 53*X^7 + 33*X^6 + 19*X^5 + 21*X^4 +
      22*X^3 + 39*X^2 + 53*X + 27) :=
  sq_step (by norm_num) pSeventeenB4s170 ⟨
    6*X^32 + 34*X^31 + 51*X^30 + 51*X^29 + 20*X^28 + 15*X^27 + 60*X^26 + 53*X^25 + 64*X^24 + 18*X^23 +
      14*X^22 + 57*X^21 + 17*X^20 + 44*X^19 + 42*X^18 + 31*X^17 + 56*X^16 + 34*X^15 + 51*X^14 +
      3*X^13 + 20*X^12 + 27*X^11 + 11*X^10 + 15*X^9 + 30*X^8 + 21*X^7 + 5*X^6 + 53*X^5 + 42*X^4 +
      19*X^3 + 28*X^2 + X + 20,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s172 : XPow fSeventeenB4 12324056908419751672839408482859208
    (12*X^33 + 62*X^32 + 66*X^31 + 15*X^30 + 46*X^29 + 58*X^28 + 15*X^27 + 55*X^26 + 40*X^25 + 61*X^24 +
      46*X^23 + 33*X^22 + 9*X^21 + 11*X^20 + 46*X^19 + 19*X^18 + 3*X^17 + 15*X^16 + 17*X^15 +
      39*X^14 + 16*X^13 + 28*X^12 + 3*X^11 + 28*X^10 + 25*X^9 + 58*X^8 + 44*X^7 + 58*X^6 + 7*X^5 +
      37*X^4 + 58*X^3 + 37*X^2 + 13*X + 50) :=
  sq_step (by norm_num) pSeventeenB4s171 ⟨
    65*X^32 + 30*X^31 + 31*X^30 + 50*X^29 + 46*X^28 + 8*X^27 + 63*X^26 + 32*X^25 + 66*X^24 + 53*X^23 +
      51*X^22 + 49*X^21 + 28*X^20 + 3*X^19 + 57*X^18 + 12*X^17 + 57*X^16 + 19*X^15 + 6*X^14 +
      20*X^13 + 4*X^12 + 23*X^11 + 31*X^10 + 58*X^9 + 51*X^8 + 31*X^7 + 17*X^6 + 57*X^5 + 3*X^4 +
      26*X^3 + 29*X^2 + 21*X + 11,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s173 : XPow fSeventeenB4 12324056908419751672839408482859209
    (19*X^33 + 10*X^32 + 17*X^31 + 58*X^30 + 63*X^29 + 44*X^28 + 66*X^27 + 36*X^26 + 62*X^25 + 51*X^24 +
      66*X^23 + 64*X^22 + 49*X^21 + 21*X^20 + 10*X^19 + 32*X^18 + 66*X^16 + 47*X^15 + 39*X^14 +
      64*X^13 + 40*X^12 + 56*X^11 + 61*X^10 + 41*X^9 + 33*X^8 + 7*X^7 + 16*X^6 + 50*X^5 + 50*X^4 +
      56*X^3 + 12*X^2 + 66*X + 45) :=
  mul_step (by norm_num) pSeventeenB4s172 pSeventeenB41 ⟨
    12,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s174 : XPow fSeventeenB4 24648113816839503345678816965718418
    (56*X^33 + 50*X^32 + 50*X^31 + 42*X^30 + 6*X^29 + 5*X^28 + 39*X^27 + 18*X^26 + 20*X^25 + 50*X^24 +
      20*X^23 + 15*X^22 + 41*X^21 + 45*X^19 + 41*X^18 + 13*X^17 + 26*X^16 + 21*X^15 + 20*X^14 +
      3*X^13 + 30*X^12 + 47*X^11 + 56*X^10 + 4*X^9 + 63*X^8 + 43*X^7 + 2*X^6 + 2*X^5 + 46*X^4 +
      45*X^3 + 50*X^2 + 48*X + 45) :=
  sq_step (by norm_num) pSeventeenB4s173 ⟨
    26*X^32 + 30*X^31 + 37*X^30 + 48*X^29 + 23*X^28 + 16*X^27 + 28*X^26 + 18*X^25 + 64*X^24 + 41*X^23 +
      14*X^22 + 60*X^21 + 49*X^20 + 42*X^19 + 18*X^18 + 32*X^17 + 53*X^16 + 29*X^15 + 47*X^14 +
      60*X^13 + 15*X^12 + 46*X^11 + 60*X^10 + 12*X^9 + 15*X^8 + 55*X^7 + 29*X^6 + 63*X^5 + 65*X^4 +
      47*X^3 + 22*X^2 + 28*X + 8,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s175 : XPow fSeventeenB4 49296227633679006691357633931436836
    (44*X^33 + 3*X^32 + 57*X^31 + 57*X^30 + 48*X^29 + 39*X^28 + 24*X^27 + 60*X^26 + 56*X^25 + 14*X^24 +
      3*X^23 + 10*X^22 + 13*X^21 + 40*X^20 + 12*X^19 + 54*X^18 + 31*X^17 + 26*X^16 + 40*X^15 + X^14 +
      3*X^13 + 47*X^12 + 17*X^11 + 35*X^10 + 38*X^9 + 10*X^8 + 21*X^7 + 32*X^6 + 8*X^5 + 28*X^4 +
      17*X^3 + 53*X^2 + 12*X + 32) :=
  sq_step (by norm_num) pSeventeenB4s174 ⟨
    54*X^32 + 13*X^31 + 35*X^30 + 52*X^29 + 10*X^28 + 42*X^27 + 51*X^26 + 63*X^25 + 15*X^24 + 16*X^23 +
      30*X^22 + 49*X^21 + 56*X^20 + 52*X^19 + 46*X^18 + 2*X^17 + 47*X^16 + 4*X^15 + 21*X^14 +
      60*X^13 + 45*X^12 + 16*X^11 + 25*X^10 + 2*X^9 + 15*X^8 + 47*X^7 + 8*X^6 + 18*X^5 + 15*X^4 +
      42*X^3 + 21*X^2 + 54*X + 9,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s176 : XPow fSeventeenB4 49296227633679006691357633931436837
    (24*X^33 + 8*X^32 + 42*X^31 + 25*X^30 + 35*X^29 + 41*X^28 + 11*X^27 + 19*X^26 + 40*X^25 + 66*X^24 +
      64*X^23 + 36*X^22 + 23*X^21 + 32*X^20 + 21*X^19 + 48*X^18 + 38*X^17 + 41*X^16 + 8*X^15 +
      65*X^14 + 45*X^13 + 41*X^12 + 26*X^11 + 36*X^10 + 37*X^9 + 3*X^8 + 46*X^7 + 41*X^6 + 31*X^5 +
      10*X^4 + 11*X^3 + 53*X^2 + 46*X + 31) :=
  mul_step (by norm_num) pSeventeenB4s175 pSeventeenB41 ⟨
    44,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s177 : XPow fSeventeenB4 98592455267358013382715267862873674
    (17*X^33 + 32*X^32 + X^30 + 5*X^29 + X^28 + 40*X^27 + 55*X^26 + 40*X^25 + 9*X^24 + X^23 + 49*X^22 +
      55*X^21 + 53*X^20 + 53*X^18 + 30*X^17 + 10*X^16 + 39*X^15 + 34*X^14 + 58*X^13 + 37*X^12 +
      59*X^11 + 5*X^10 + 9*X^9 + 4*X^8 + 41*X^7 + 61*X^6 + 18*X^5 + 36*X^4 + 7*X^3 + 64*X + 51) :=
  sq_step (by norm_num) pSeventeenB4s176 ⟨
    40*X^32 + 62*X^31 + 52*X^30 + 63*X^29 + 48*X^28 + 6*X^27 + 32*X^26 + 20*X^25 + 20*X^24 + X^23 +
      9*X^22 + 48*X^21 + 50*X^20 + 36*X^19 + 14*X^18 + 24*X^17 + 53*X^16 + 25*X^15 + 46*X^13 +
      45*X^12 + 64*X^11 + 42*X^10 + 29*X^9 + 2*X^8 + 26*X^7 + 48*X^6 + 47*X^5 + 38*X^4 + 27*X^3 +
      11*X^2 + 55*X + 3,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s178 : XPow fSeventeenB4 98592455267358013382715267862873675
    (66*X^33 + 10*X^32 + 15*X^31 + 22*X^30 + 36*X^29 + 42*X^28 + 65*X^27 + 12*X^26 + 16*X^25 + 36*X^24 +
      12*X^23 + 38*X^22 + 51*X^21 + 26*X^20 + 57*X^19 + 32*X^18 + 39*X^17 + 47*X^16 + 23*X^15 +
      18*X^14 + 21*X^13 + 50*X^12 + 60*X^10 + 19*X^9 + 31*X^8 + 39*X^7 + 14*X^6 + 60*X^5 + 18*X^4 +
      66*X^3 + 57*X^2 + 29*X + 47) :=
  mul_step (by norm_num) pSeventeenB4s177 pSeventeenB41 ⟨
    17,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s179 : XPow fSeventeenB4 197184910534716026765430535725747350
    (11*X^33 + 15*X^32 + 34*X^31 + 60*X^30 + 12*X^29 + 8*X^28 + 4*X^27 + 66*X^26 + 9*X^24 + 8*X^23 +
      54*X^22 + 7*X^21 + 57*X^20 + 37*X^19 + 33*X^18 + 11*X^17 + 25*X^16 + 43*X^15 + 50*X^14 +
      40*X^13 + 64*X^12 + 50*X^11 + 47*X^10 + 9*X^9 + 56*X^8 + 47*X^7 + 21*X^6 + 23*X^5 + 7*X^4 +
      44*X^3 + 21*X^2 + 59*X + 53) :=
  sq_step (by norm_num) pSeventeenB4s178 ⟨
    X^32 + 49*X^31 + 7*X^30 + 8*X^29 + 16*X^28 + 18*X^27 + 22*X^26 + 31*X^25 + 41*X^24 + 24*X^23 +
      14*X^22 + 23*X^21 + 65*X^20 + 41*X^19 + 13*X^18 + 52*X^17 + 11*X^16 + 38*X^15 + 5*X^14 +
      50*X^13 + 10*X^12 + 35*X^11 + 4*X^10 + 13*X^9 + 14*X^8 + 8*X^7 + 32*X^6 + 41*X^5 + 22*X^4 +
      48*X^3 + 14*X^2 + 32*X + 37,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s180 : XPow fSeventeenB4 197184910534716026765430535725747351
    (37*X^33 + 5*X^32 + 6*X^31 + 23*X^30 + 7*X^29 + 25*X^28 + 37*X^27 + 41*X^26 + 49*X^25 + 7*X^24 +
      34*X^23 + 63*X^22 + 36*X^21 + 42*X^20 + 8*X^19 + 32*X^18 + 28*X^17 + 60*X^16 + 35*X^15 +
      22*X^14 + 30*X^13 + 56*X^12 + 28*X^11 + 42*X^10 + 46*X^9 + 9*X^8 + 58*X^7 + 48*X^6 + 58*X^5 +
      59*X^4 + 44*X^3 + 19*X^2 + 23*X + 58) :=
  mul_step (by norm_num) pSeventeenB4s179 pSeventeenB41 ⟨
    11,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s181 : XPow fSeventeenB4 394369821069432053530861071451494702
    (28*X^33 + 38*X^32 + 61*X^31 + 62*X^30 + 5*X^29 + 31*X^28 + 66*X^27 + 37*X^26 + 53*X^25 + X^24 +
      59*X^23 + 53*X^22 + 32*X^21 + 58*X^20 + 47*X^19 + 5*X^18 + 45*X^17 + 29*X^16 + 59*X^15 +
      5*X^14 + 37*X^13 + 46*X^12 + 25*X^11 + 56*X^10 + 30*X^9 + 50*X^8 + 15*X^7 + 43*X^6 + 33*X^5 +
      28*X^4 + 43*X^3 + 39*X^2 + 19*X + 30) :=
  sq_step (by norm_num) pSeventeenB4s180 ⟨
    29*X^32 + 26*X^31 + 6*X^30 + 16*X^29 + 62*X^28 + 12*X^27 + 25*X^26 + X^25 + 58*X^24 + 8*X^23 +
      8*X^22 + 64*X^21 + 35*X^20 + 12*X^19 + 47*X^18 + 21*X^17 + 34*X^16 + 3*X^15 + 56*X^14 +
      43*X^13 + 62*X^12 + 36*X^11 + 30*X^10 + 19*X^9 + 48*X^8 + 22*X^6 + 57*X^5 + 39*X^4 + 8*X^3 +
      18*X^2 + 40,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s182 : XPow fSeventeenB4 788739642138864107061722142902989404
    (17*X^33 + 49*X^32 + 23*X^31 + 15*X^30 + 21*X^29 + 30*X^28 + 31*X^27 + 56*X^26 + 2*X^25 + 4*X^24 +
      10*X^23 + 47*X^22 + 11*X^21 + 8*X^20 + 6*X^19 + 38*X^18 + 2*X^17 + 58*X^16 + 9*X^15 + 60*X^14 +
      65*X^13 + 43*X^12 + 27*X^11 + 26*X^10 + 63*X^9 + 29*X^8 + 62*X^7 + 37*X^6 + 50*X^5 + 18*X^4 +
      44*X^3 + 41*X^2 + 45*X + 32) :=
  sq_step (by norm_num) pSeventeenB4s181 ⟨
    47*X^32 + 11*X^31 + 62*X^30 + 48*X^29 + 26*X^28 + 7*X^27 + 12*X^26 + 27*X^25 + 7*X^24 + 60*X^23 +
      60*X^22 + 58*X^21 + 20*X^20 + 39*X^19 + 47*X^18 + 39*X^17 + 10*X^16 + 8*X^15 + 34*X^14 +
      62*X^13 + 14*X^12 + 57*X^11 + 51*X^10 + 56*X^9 + 24*X^8 + 30*X^7 + 45*X^6 + 38*X^5 + 3*X^4 +
      3*X^3 + 46*X^2 + 18*X + 41,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s183 : XPow fSeventeenB4 788739642138864107061722142902989405
    (16*X^33 + 33*X^32 + 29*X^31 + 38*X^30 + 65*X^29 + 33*X^28 + 66*X^27 + 41*X^26 + 11*X^25 + 45*X^24 +
      10*X^23 + 61*X^22 + 6*X^21 + 32*X^20 + 42*X^19 + 4*X^18 + 20*X^17 + 17*X^16 + 49*X^15 +
      25*X^14 + 27*X^13 + 18*X^12 + 21*X^11 + 47*X^10 + 44*X^9 + 52*X^8 + 15*X^7 + 46*X^6 + 42*X^5 +
      55*X^4 + 40*X^3 + 38*X^2 + 10*X + 47) :=
  mul_step (by norm_num) pSeventeenB4s182 pSeventeenB41 ⟨
    17,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s184 : XPow fSeventeenB4 1577479284277728214123444285805978810
    (10*X^33 + 44*X^32 + 44*X^31 + 29*X^29 + 42*X^28 + 35*X^27 + 17*X^26 + 8*X^25 + 31*X^24 + 33*X^23 +
      43*X^22 + 43*X^21 + 41*X^20 + 41*X^19 + 57*X^18 + 60*X^17 + 66*X^16 + 57*X^15 + 8*X^14 +
      31*X^13 + 21*X^12 + 46*X^11 + 9*X^10 + 24*X^9 + 54*X^8 + 31*X^7 + 43*X^6 + 15*X^5 + 9*X^4 +
      33*X^3 + 22*X^2 + 29*X + 41) :=
  sq_step (by norm_num) pSeventeenB4s183 ⟨
    55*X^32 + 27*X^31 + 50*X^30 + 20*X^29 + 58*X^28 + 32*X^27 + 59*X^26 + 5*X^25 + 13*X^24 + 11*X^23 +
      64*X^22 + 35*X^21 + 4*X^20 + 3*X^19 + 56*X^18 + 5*X^17 + 19*X^16 + 31*X^15 + 50*X^14 + 64*X^13 +
      22*X^12 + 34*X^11 + 13*X^10 + 56*X^9 + 46*X^8 + 21*X^7 + X^6 + 27*X^5 + 55*X^4 + 45*X^3 +
      32*X^2 + 33*X + 7,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s185 : XPow fSeventeenB4 1577479284277728214123444285805978811
    (64*X^33 + 42*X^32 + 24*X^31 + 39*X^30 + 35*X^29 + 48*X^28 + 15*X^27 + 27*X^26 + 43*X^25 + 26*X^24 +
      37*X^23 + 33*X^22 + 28*X^21 + 9*X^20 + 16*X^19 + 6*X^18 + 20*X^17 + 42*X^16 + 37*X^15 +
      39*X^14 + 51*X^13 + 21*X^12 + 10*X^11 + 54*X^10 + 51*X^9 + 33*X^8 + 34*X^7 + 56*X^6 + 31*X^5 +
      4*X^4 + 49*X^3 + 17*X^2 + 32*X + 4) :=
  mul_step (by norm_num) pSeventeenB4s184 pSeventeenB41 ⟨
    10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s186 : XPow fSeventeenB4 3154958568555456428246888571611957622
    (36*X^33 + 5*X^32 + 66*X^31 + 46*X^30 + 62*X^29 + 48*X^28 + 20*X^27 + 19*X^26 + 3*X^25 + 28*X^24 +
      34*X^23 + 20*X^22 + 22*X^21 + 52*X^20 + 51*X^19 + 53*X^18 + 33*X^17 + 26*X^16 + 37*X^15 +
      9*X^14 + 6*X^13 + 25*X^12 + 64*X^11 + 25*X^10 + 19*X^9 + 48*X^8 + 25*X^7 + 41*X^6 + 61*X^5 +
      10*X^4 + 17*X^3 + 65*X^2 + 63*X + 51) :=
  sq_step (by norm_num) pSeventeenB4s185 ⟨
    9*X^32 + 34*X^31 + 38*X^30 + 37*X^29 + 47*X^28 + 6*X^27 + 31*X^26 + 47*X^25 + 43*X^24 + 8*X^23 +
      65*X^22 + 62*X^21 + 10*X^20 + X^19 + 39*X^18 + 53*X^17 + 41*X^16 + 6*X^15 + 57*X^14 + 66*X^13 +
      60*X^12 + 49*X^11 + 31*X^10 + 29*X^9 + 13*X^8 + 31*X^7 + 17*X^5 + 38*X^4 + 57*X^3 + 46*X^2 +
      41*X + 54,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s187 : XPow fSeventeenB4 3154958568555456428246888571611957623
    (10*X^33 + 32*X^32 + 52*X^31 + 31*X^30 + 63*X^29 + 40*X^28 + 52*X^27 + 58*X^26 + 31*X^25 + 49*X^24 +
      52*X^23 + 53*X^22 + 32*X^21 + 43*X^20 + 26*X^19 + 53*X^18 + 48*X^17 + 50*X^16 + 33*X^15 +
      8*X^14 + 66*X^13 + 41*X^12 + 42*X^11 + 60*X^10 + 64*X^9 + 59*X^8 + 22*X^7 + 21*X^6 + 49*X^5 +
      60*X^4 + 55*X^3 + 60*X^2 + 32*X + 1) :=
  mul_step (by norm_num) pSeventeenB4s186 pSeventeenB41 ⟨
    36,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s188 : XPow fSeventeenB4 6309917137110912856493777143223915246
    (64*X^33 + 59*X^32 + 65*X^31 + 20*X^30 + 30*X^29 + 24*X^28 + 55*X^27 + 31*X^26 + 17*X^25 + 57*X^24 +
      X^23 + 12*X^22 + 7*X^21 + 33*X^20 + 3*X^19 + 39*X^18 + 5*X^17 + 2*X^16 + 28*X^15 + 52*X^14 +
      12*X^13 + 11*X^12 + 31*X^11 + 25*X^10 + 40*X^9 + 20*X^8 + 60*X^7 + 36*X^6 + 16*X^5 + 2*X^4 +
      45*X^3 + 29*X^2 + 49*X + 42) :=
  sq_step (by norm_num) pSeventeenB4s187 ⟨
    33*X^32 + 36*X^31 + 39*X^30 + 11*X^29 + 65*X^28 + 56*X^27 + 19*X^26 + 24*X^25 + 29*X^24 + 37*X^23 +
      47*X^22 + 62*X^21 + 46*X^20 + 62*X^19 + 42*X^18 + 19*X^17 + 14*X^16 + 58*X^15 + 15*X^14 +
      2*X^13 + 11*X^12 + 48*X^11 + 35*X^10 + 38*X^9 + 63*X^8 + 10*X^7 + 6*X^6 + 11*X^5 + 35*X^4 +
      35*X^3 + 42*X^2 + 34*X + 2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s189 : XPow fSeventeenB4 12619834274221825712987554286447830492
    (64*X^33 + 49*X^32 + 65*X^31 + 55*X^30 + 33*X^29 + 24*X^28 + 35*X^27 + 40*X^26 + 21*X^25 + 65*X^24 +
      16*X^23 + 50*X^22 + 30*X^21 + 54*X^20 + 36*X^19 + 35*X^18 + 24*X^17 + 23*X^16 + 56*X^15 +
      23*X^14 + 54*X^13 + 39*X^12 + 6*X^11 + 25*X^10 + 27*X^9 + 11*X^8 + 24*X^7 + 50*X^6 + 11*X^5 +
      25*X^4 + X^3 + 20*X^2 + 10*X + 31) :=
  sq_step (by norm_num) pSeventeenB4s188 ⟨
    9*X^32 + 66*X^31 + 32*X^30 + 38*X^29 + 9*X^28 + 66*X^27 + 6*X^26 + 24*X^25 + 49*X^24 + 66*X^23 +
      39*X^22 + 10*X^21 + 39*X^20 + X^19 + 64*X^18 + 19*X^17 + 12*X^16 + 31*X^15 + 53*X^14 + 61*X^13 +
      58*X^12 + 2*X^11 + 65*X^10 + 40*X^9 + 62*X^8 + 2*X^7 + 64*X^6 + 32*X^5 + 65*X^4 + 26*X^3 +
      2*X^2 + 45*X + 56,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s190 : XPow fSeventeenB4 25239668548443651425975108572895660984
    (52*X^33 + 55*X^32 + 4*X^31 + 4*X^30 + 46*X^29 + 23*X^28 + 61*X^27 + 20*X^26 + 50*X^25 + 63*X^24 +
      59*X^23 + 30*X^22 + 22*X^21 + 49*X^20 + 24*X^19 + 15*X^18 + 25*X^17 + 30*X^16 + 37*X^15 +
      61*X^14 + 12*X^13 + 45*X^12 + 22*X^11 + 38*X^10 + 19*X^9 + 66*X^8 + 64*X^7 + 6*X^6 + 16*X^5 +
      47*X^4 + 28*X^3 + 33*X^2 + 36*X + 12) :=
  sq_step (by norm_num) pSeventeenB4s189 ⟨
    9*X^32 + 59*X^31 + 10*X^30 + 13*X^29 + 24*X^28 + 24*X^27 + 38*X^26 + 26*X^25 + 41*X^24 + 19*X^23 +
      30*X^21 + 11*X^20 + 14*X^19 + 7*X^18 + 7*X^17 + 41*X^16 + 40*X^15 + 53*X^14 + 44*X^13 +
      39*X^12 + 8*X^11 + 45*X^10 + 46*X^9 + 11*X^8 + 17*X^7 + 53*X^6 + 26*X^5 + 59*X^4 + 7*X^3 +
      20*X^2 + 61*X + 6,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s191 : XPow fSeventeenB4 50479337096887302851950217145791321968
    (22*X^33 + 57*X^32 + 34*X^31 + 7*X^30 + 14*X^29 + 10*X^28 + 16*X^27 + 9*X^26 + 27*X^25 + 25*X^24 +
      47*X^23 + 59*X^22 + 37*X^21 + 43*X^20 + 3*X^19 + 21*X^18 + 7*X^17 + 57*X^16 + 41*X^15 + 6*X^14 +
      14*X^13 + 49*X^12 + 56*X^11 + 10*X^10 + 22*X^9 + 33*X^8 + 7*X^7 + 58*X^6 + 25*X^5 + 58*X^4 +
      31*X^3 + 17*X^2 + 32*X + 9) :=
  sq_step (by norm_num) pSeventeenB4s190 ⟨
    24*X^32 + 6*X^31 + 58*X^30 + 10*X^29 + 34*X^28 + 27*X^27 + 61*X^26 + 12*X^25 + 13*X^24 + 63*X^23 +
      51*X^22 + 32*X^21 + 37*X^20 + 50*X^19 + 39*X^18 + 28*X^17 + 5*X^16 + 64*X^15 + 50*X^14 +
      3*X^13 + 23*X^12 + 14*X^11 + 59*X^10 + 10*X^9 + 51*X^8 + 9*X^7 + 2*X^6 + 63*X^5 + 17*X^4 +
      55*X^3 + 53*X^2 + 50*X + 31,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s192 : XPow fSeventeenB4 100958674193774605703900434291582643936
    (27*X^33 + 58*X^32 + 21*X^31 + 37*X^30 + 63*X^29 + 2*X^28 + 13*X^27 + 10*X^26 + 34*X^25 + 8*X^24 +
      18*X^23 + 10*X^22 + 9*X^21 + 13*X^20 + 62*X^19 + 54*X^18 + 19*X^17 + 20*X^16 + 51*X^15 +
      65*X^14 + 16*X^13 + 60*X^12 + 55*X^11 + 59*X^10 + 21*X^9 + 30*X^8 + 51*X^7 + 10*X^6 + 63*X^5 +
      11*X^4 + 30*X^3 + 66*X^2 + 47*X + 39) :=
  sq_step (by norm_num) pSeventeenB4s191 ⟨
    15*X^32 + 59*X^31 + 36*X^30 + 19*X^29 + 64*X^28 + 4*X^27 + 19*X^26 + 11*X^25 + 28*X^24 + 33*X^23 +
      14*X^22 + 52*X^21 + 39*X^20 + 56*X^19 + 6*X^18 + 11*X^17 + 46*X^15 + 62*X^14 + 53*X^13 +
      59*X^12 + 63*X^11 + 65*X^10 + 21*X^9 + 11*X^8 + 46*X^7 + 16*X^6 + 3*X^5 + 18*X^4 + 10*X^3 +
      57*X^2 + 66*X + 29,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s193 : XPow fSeventeenB4 201917348387549211407800868583165287872
    (25*X^32 + 44*X^31 + 48*X^30 + X^29 + 29*X^28 + X^27 + X^26 + 52*X^25 + 32*X^24 + 22*X^23 + 60*X^22 +
      50*X^21 + 32*X^20 + 52*X^19 + 64*X^18 + 10*X^17 + 15*X^16 + 30*X^15 + 17*X^14 + 40*X^13 +
      66*X^12 + 42*X^11 + 28*X^10 + 34*X^9 + 5*X^8 + 55*X^7 + 24*X^6 + 11*X^5 + 37*X^4 + 51*X^3 +
      12*X^2 + 31*X + 2) :=
  sq_step (by norm_num) pSeventeenB4s192 ⟨
    59*X^32 + 34*X^31 + 25*X^30 + 36*X^29 + 48*X^28 + 33*X^27 + 4*X^26 + 27*X^25 + 46*X^24 + 25*X^23 +
      63*X^22 + 65*X^21 + 36*X^20 + 10*X^19 + 8*X^18 + 17*X^17 + 29*X^16 + 50*X^14 + 14*X^13 +
      17*X^12 + 25*X^11 + 22*X^10 + 7*X^9 + 6*X^8 + 52*X^7 + 21*X^6 + 30*X^5 + 2*X^4 + 16*X^3 +
      46*X^2 + 31*X + 55,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s194 : XPow fSeventeenB4 403834696775098422815601737166330575744
    (54*X^33 + 29*X^32 + 50*X^31 + 49*X^30 + 53*X^29 + 21*X^28 + 54*X^27 + 64*X^26 + 61*X^25 + 46*X^24 +
      64*X^23 + 30*X^22 + 14*X^21 + 6*X^20 + 26*X^19 + 4*X^18 + 27*X^17 + 53*X^16 + 26*X^15 +
      29*X^14 + 14*X^13 + 60*X^12 + 62*X^11 + 49*X^10 + 45*X^9 + 42*X^8 + 15*X^7 + 38*X^6 + 47*X^5 +
      49*X^4 + 19*X^3 + 9*X^2 + 37*X + 3) :=
  sq_step (by norm_num) pSeventeenB4s193 ⟨
    22*X^30 + 33*X^29 + 56*X^28 + 37*X^27 + 53*X^26 + 14*X^25 + 2*X^24 + 52*X^23 + 24*X^22 + 8*X^21 +
      56*X^20 + 22*X^19 + 33*X^18 + 44*X^17 + 5*X^16 + 23*X^15 + 31*X^14 + 43*X^13 + 53*X^12 +
      58*X^11 + 65*X^10 + 26*X^9 + 9*X^8 + 46*X^7 + 52*X^6 + 38*X^5 + 12*X^4 + 12*X^3 + 62*X^2 + 3*X +
      31,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s195 : XPow fSeventeenB4 807669393550196845631203474332661151488
    (44*X^33 + 18*X^32 + 61*X^31 + 52*X^30 + 40*X^29 + 65*X^28 + 3*X^27 + 30*X^26 + 29*X^25 + 14*X^24 +
      60*X^23 + 18*X^22 + 13*X^21 + 13*X^20 + 7*X^19 + 35*X^18 + 31*X^17 + 50*X^16 + 15*X^15 +
      54*X^14 + 20*X^13 + 64*X^12 + 37*X^11 + 50*X^10 + 48*X^9 + 50*X^8 + 57*X^7 + 44*X^6 + 63*X^5 +
      55*X^4 + 40*X^3 + 55*X^2 + 15*X + 23) :=
  sq_step (by norm_num) pSeventeenB4s194 ⟨
    35*X^32 + 53*X^31 + 42*X^30 + 28*X^29 + 60*X^28 + 27*X^27 + 50*X^26 + 63*X^25 + 55*X^24 + 64*X^23 +
      12*X^22 + 62*X^21 + 8*X^20 + 40*X^19 + 61*X^18 + 12*X^17 + 43*X^16 + 55*X^15 + 29*X^14 +
      38*X^13 + 66*X^12 + 37*X^11 + 51*X^10 + 12*X^9 + 24*X^8 + 54*X^7 + 35*X^6 + 7*X^5 + 29*X^4 +
      59*X^3 + 57*X^2 + 47*X + 35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s196 : XPow fSeventeenB4 807669393550196845631203474332661151489
    (39*X^33 + 12*X^32 + 37*X^31 + 17*X^30 + 61*X^29 + 20*X^28 + 48*X^27 + 59*X^26 + 40*X^25 + 56*X^24 +
      5*X^23 + 36*X^22 + 63*X^21 + 27*X^20 + 2*X^19 + 48*X^18 + 62*X^17 + 16*X^16 + 61*X^15 +
      15*X^14 + 62*X^13 + 61*X^12 + 41*X^11 + 46*X^10 + 10*X^9 + 39*X^8 + 58*X^7 + 29*X^6 + 58*X^5 +
      33*X^4 + 13*X^3 + 56*X^2 + 37*X + 31) :=
  mul_step (by norm_num) pSeventeenB4s195 pSeventeenB41 ⟨
    44,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s197 : XPow fSeventeenB4 1615338787100393691262406948665322302978
    (8*X^33 + 34*X^32 + 49*X^31 + 48*X^30 + 63*X^29 + 13*X^28 + 43*X^27 + 58*X^26 + 52*X^25 + 50*X^24 +
      49*X^23 + 46*X^22 + 64*X^21 + 5*X^20 + 7*X^19 + 52*X^18 + 18*X^17 + 42*X^16 + 17*X^15 +
      51*X^14 + 64*X^13 + 14*X^12 + 53*X^11 + 28*X^10 + 62*X^9 + 31*X^8 + 51*X^7 + 42*X^6 + 36*X^5 +
      19*X^4 + 16*X^3 + 47*X^2 + 40*X + 9) :=
  sq_step (by norm_num) pSeventeenB4s196 ⟨
    47*X^32 + 25*X^31 + 2*X^30 + 21*X^29 + 64*X^28 + 41*X^27 + 40*X^26 + 42*X^25 + 16*X^24 + 23*X^23 +
      32*X^22 + 31*X^21 + 12*X^20 + 44*X^19 + 8*X^18 + 4*X^17 + 26*X^16 + 7*X^15 + 32*X^14 + 62*X^13 +
      30*X^12 + 22*X^11 + 54*X^10 + 61*X^9 + 37*X^8 + 45*X^7 + 28*X^6 + 20*X^5 + 50*X^4 + 20*X^3 +
      66*X^2 + 65*X + 32,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s198 : XPow fSeventeenB4 1615338787100393691262406948665322302979
    (50*X^33 + 34*X^32 + 27*X^31 + 4*X^30 + 61*X^29 + 40*X^28 + 43*X^27 + 27*X^26 + 6*X^25 + 30*X^24 +
      X^23 + 56*X^22 + 8*X^21 + 35*X^20 + 46*X^19 + 15*X^18 + 32*X^17 + 5*X^16 + 34*X^15 + 57*X^14 +
      38*X^13 + 33*X^12 + 2*X^11 + 19*X^10 + 42*X^9 + 66*X^8 + 8*X^7 + 42*X^6 + 50*X^5 + 33*X^4 +
      15*X^3 + 17*X^2 + 42*X + 30) :=
  mul_step (by norm_num) pSeventeenB4s197 pSeventeenB41 ⟨
    8,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s199 : XPow fSeventeenB4 3230677574200787382524813897330644605958
    (47*X^33 + 7*X^32 + 52*X^31 + 56*X^30 + 3*X^29 + 58*X^28 + 28*X^27 + 60*X^26 + 39*X^25 + 13*X^24 +
      44*X^23 + 47*X^22 + 16*X^21 + 12*X^20 + 10*X^19 + 29*X^18 + 40*X^17 + 36*X^16 + 61*X^15 +
      58*X^14 + 17*X^13 + 29*X^12 + 12*X^11 + 50*X^9 + 26*X^8 + 29*X^7 + 44*X^6 + 2*X^5 + 6*X^4 +
      17*X^2 + 64*X + 52) :=
  sq_step (by norm_num) pSeventeenB4s198 ⟨
    21*X^32 + 25*X^31 + 56*X^30 + 35*X^29 + 45*X^28 + 9*X^27 + 10*X^26 + 54*X^25 + 50*X^24 + 30*X^23 +
      6*X^21 + 14*X^20 + 48*X^19 + 52*X^18 + 7*X^17 + 17*X^16 + 49*X^15 + 32*X^14 + 30*X^13 +
      51*X^12 + 66*X^11 + 40*X^10 + 34*X^9 + 15*X^8 + 38*X^7 + 54*X^5 + 16*X^4 + 48*X^3 + 30*X^2 +
      11*X + 24,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s200 : XPow fSeventeenB4 3230677574200787382524813897330644605959
    (34*X^33 + 56*X^32 + 8*X^31 + 50*X^30 + 5*X^29 + 2*X^28 + 64*X^27 + X^26 + 56*X^25 + 58*X^24 +
      59*X^23 + 36*X^22 + 38*X^21 + 7*X^20 + 44*X^19 + 14*X^18 + 61*X^17 + 24*X^16 + X^14 + 36*X^13 +
      62*X^12 + 65*X^11 + 57*X^10 + 32*X^9 + 25*X^8 + 62*X^7 + 54*X^6 + 29*X^5 + 58*X^4 + 30*X^3 +
      21*X^2 + 3*X + 59) :=
  mul_step (by norm_num) pSeventeenB4s199 pSeventeenB41 ⟨
    47,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s201 : XPow fSeventeenB4 6461355148401574765049627794661289211918
    (19*X^33 + 42*X^32 + 66*X^31 + 19*X^30 + 52*X^29 + 9*X^28 + 29*X^27 + 64*X^26 + 21*X^25 + 11*X^24 +
      47*X^23 + 46*X^22 + 61*X^21 + 7*X^20 + 11*X^19 + 64*X^18 + 47*X^17 + 15*X^16 + 66*X^15 +
      53*X^14 + 21*X^13 + 3*X^12 + 18*X^11 + 6*X^10 + 10*X^9 + 50*X^8 + 4*X^7 + 24*X^6 + 8*X^5 +
      46*X^4 + 36*X^3 + 26*X^2 + 35*X + 7) :=
  sq_step (by norm_num) pSeventeenB4s200 ⟨
    17*X^32 + 23*X^31 + 51*X^30 + 39*X^29 + 47*X^28 + 34*X^27 + 22*X^26 + 15*X^25 + 50*X^24 + 57*X^23 +
      37*X^22 + 29*X^21 + 54*X^20 + 38*X^19 + 12*X^17 + 13*X^16 + 53*X^15 + 56*X^14 + 3*X^13 +
      40*X^12 + 49*X^11 + 7*X^10 + 17*X^9 + 55*X^8 + 66*X^7 + 50*X^6 + 26*X^5 + 17*X^4 + 15*X^3 +
      56*X^2 + 46*X + 25,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s202 : XPow fSeventeenB4 12922710296803149530099255589322578423836
    (50*X^33 + 39*X^32 + 52*X^31 + 65*X^30 + 66*X^29 + 66*X^28 + 34*X^27 + 61*X^26 + 61*X^25 + 18*X^24 +
      3*X^23 + 25*X^22 + 42*X^21 + 65*X^20 + 14*X^19 + 12*X^18 + 34*X^17 + 43*X^16 + 18*X^15 +
      49*X^14 + 8*X^13 + 4*X^12 + 60*X^11 + 4*X^10 + 47*X^9 + 41*X^8 + 8*X^7 + 33*X^6 + 66*X^5 +
      43*X^4 + 9*X^3 + 39*X^2 + 37*X + 9) :=
  sq_step (by norm_num) pSeventeenB4s201 ⟨
    26*X^32 + 40*X^31 + 32*X^30 + 6*X^29 + 29*X^28 + 57*X^27 + 51*X^26 + 62*X^25 + 60*X^24 + 52*X^23 +
      2*X^21 + 46*X^20 + 27*X^19 + 20*X^18 + 32*X^17 + 46*X^16 + 64*X^15 + 6*X^14 + 19*X^13 +
      19*X^12 + 12*X^11 + 38*X^10 + 27*X^9 + 5*X^8 + 17*X^7 + 2*X^6 + 24*X^5 + 12*X^4 + 11*X^3 +
      15*X^2 + 16*X + 34,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s203 : XPow fSeventeenB4 25845420593606299060198511178645156847672
    (50*X^33 + 25*X^32 + 4*X^31 + 53*X^30 + 62*X^29 + 13*X^28 + 19*X^27 + 18*X^26 + 52*X^25 + 59*X^24 +
      36*X^23 + 64*X^22 + 45*X^21 + 23*X^20 + 53*X^19 + 25*X^18 + 66*X^17 + 36*X^16 + 66*X^15 +
      65*X^14 + 27*X^13 + 16*X^12 + 22*X^11 + 50*X^10 + 36*X^9 + 52*X^8 + 32*X^7 + 57*X^6 + 35*X^5 +
      26*X^4 + 24*X^3 + 57*X^2 + 52*X + 31) :=
  sq_step (by norm_num) pSeventeenB4s202 ⟨
    21*X^32 + 56*X^31 + 35*X^30 + 39*X^29 + 48*X^28 + 62*X^27 + 16*X^26 + 46*X^25 + 25*X^24 + 6*X^23 +
      41*X^22 + 14*X^21 + 33*X^20 + 22*X^19 + 30*X^18 + 49*X^17 + 44*X^16 + 35*X^15 + 26*X^13 +
      21*X^12 + 26*X^11 + 12*X^10 + 10*X^9 + 51*X^8 + 59*X^7 + 38*X^6 + 60*X^5 + 56*X^4 + 63*X^3 +
      30*X^2 + 43*X + 9,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s204 : XPow fSeventeenB4 51690841187212598120397022357290313695344
    (12*X^33 + 58*X^32 + 43*X^31 + 42*X^30 + 2*X^29 + 53*X^28 + 20*X^27 + 8*X^26 + 4*X^25 + 10*X^24 +
      14*X^23 + 19*X^22 + 58*X^21 + 17*X^20 + 21*X^19 + 2*X^18 + 2*X^17 + 2*X^16 + 61*X^15 + 30*X^14 +
      26*X^13 + 34*X^12 + 11*X^11 + 23*X^10 + 37*X^9 + 55*X^8 + 10*X^7 + 27*X^6 + 55*X^5 + 42*X^4 +
      51*X^3 + 26*X^2 + 64*X + 63) :=
  sq_step (by norm_num) pSeventeenB4s203 ⟨
    21*X^32 + 63*X^31 + 48*X^30 + 46*X^29 + 22*X^28 + 4*X^27 + 64*X^26 + 28*X^25 + 22*X^24 + 43*X^23 +
      22*X^22 + 19*X^21 + 64*X^20 + 3*X^19 + 57*X^18 + 15*X^17 + 32*X^16 + 21*X^15 + 53*X^14 +
      36*X^13 + 50*X^12 + 63*X^11 + 16*X^10 + 40*X^9 + 10*X^8 + 4*X^7 + 15*X^6 + 61*X^5 + 42*X^4 +
      43*X^3 + 13*X^2 + 30*X + 33,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s205 : XPow fSeventeenB4 103381682374425196240794044714580627390688
    (31*X^33 + 50*X^32 + 29*X^31 + 5*X^30 + 27*X^29 + 17*X^28 + 47*X^27 + 47*X^26 + 42*X^25 + 21*X^24 +
      52*X^23 + 41*X^22 + 53*X^21 + 55*X^20 + 45*X^19 + 36*X^18 + 8*X^17 + 39*X^16 + 8*X^15 + 5*X^14 +
      46*X^13 + 3*X^12 + 12*X^11 + 8*X^10 + 2*X^9 + 21*X^8 + 28*X^7 + 64*X^6 + 44*X^5 + 20*X^4 +
      6*X^3 + 23*X^2 + 51*X + 55) :=
  sq_step (by norm_num) pSeventeenB4s204 ⟨
    10*X^32 + 5*X^31 + 49*X^30 + 20*X^29 + 14*X^28 + 43*X^27 + 37*X^26 + 51*X^25 + 9*X^24 + X^23 +
      49*X^22 + 38*X^21 + 14*X^20 + 31*X^19 + 41*X^17 + 40*X^16 + 12*X^15 + 18*X^14 + 10*X^13 +
      66*X^12 + 64*X^11 + 38*X^10 + 29*X^9 + 45*X^8 + 23*X^7 + 63*X^6 + 53*X^5 + 12*X^4 + 47*X^3 +
      42*X^2 + 44*X + 64,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s206 : XPow fSeventeenB4 103381682374425196240794044714580627390689
    (45*X^33 + 63*X^32 + 66*X^31 + 58*X^30 + 2*X^29 + 27*X^28 + 14*X^27 + 54*X^26 + 18*X^25 + 37*X^24 +
      9*X^23 + 22*X^22 + 8*X^21 + 53*X^20 + 63*X^19 + 55*X^18 + 17*X^17 + 62*X^16 + 48*X^15 +
      44*X^14 + 29*X^13 + 35*X^12 + 58*X^11 + 28*X^10 + 5*X^9 + 61*X^8 + 16*X^7 + 17*X^6 + 48*X^5 +
      30*X^4 + 33*X^3 + 54*X^2 + 7*X + 66) :=
  mul_step (by norm_num) pSeventeenB4s205 pSeventeenB41 ⟨
    31,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s207 : XPow fSeventeenB4 206763364748850392481588089429161254781378
    (53*X^33 + 66*X^32 + 14*X^31 + 19*X^30 + 47*X^29 + 3*X^28 + 63*X^27 + 50*X^26 + 58*X^25 + 43*X^24 +
      38*X^23 + 43*X^22 + 60*X^21 + 53*X^20 + 48*X^19 + 21*X^18 + 50*X^17 + 20*X^16 + 39*X^15 +
      42*X^14 + 41*X^13 + 19*X^12 + 56*X^11 + 43*X^10 + 58*X^9 + 36*X^8 + 64*X^7 + 59*X^6 + 63*X^5 +
      45*X^4 + 13*X^3 + 36*X^2 + 46*X + 39) :=
  sq_step (by norm_num) pSeventeenB4s206 ⟨
    15*X^32 + 5*X^31 + 37*X^29 + 19*X^28 + 25*X^27 + 66*X^26 + 27*X^25 + 49*X^24 + 63*X^23 + 4*X^22 +
      56*X^21 + 36*X^20 + 57*X^19 + 18*X^17 + 51*X^16 + 30*X^15 + 9*X^14 + 45*X^13 + 55*X^12 +
      54*X^11 + 33*X^10 + 61*X^9 + 3*X^8 + 64*X^7 + 25*X^6 + 46*X^5 + 46*X^4 + 19*X^3 + 47*X^2 +
      12*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s208 : XPow fSeventeenB4 206763364748850392481588089429161254781379
    (38*X^33 + 57*X^32 + 39*X^31 + 33*X^30 + 53*X^29 + 18*X^28 + 26*X^27 + 18*X^26 + 53*X^25 + 21*X^24 +
      38*X^23 + 7*X^22 + 31*X^21 + 66*X^20 + 65*X^19 + 5*X^18 + 4*X^17 + 60*X^16 + 55*X^15 + 3*X^14 +
      44*X^13 + 24*X^12 + 55*X^11 + 16*X^10 + 21*X^8 + 18*X^7 + 19*X^6 + 41*X^5 + 25*X^3 + 36*X^2 +
      65*X + 48) :=
  mul_step (by norm_num) pSeventeenB4s207 pSeventeenB41 ⟨
    53,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s209 : XPow fSeventeenB4 413526729497700784963176178858322509562758
    (41*X^33 + 53*X^32 + 24*X^31 + 50*X^30 + 7*X^29 + 62*X^28 + 42*X^27 + 9*X^26 + 30*X^25 + 64*X^24 +
      35*X^23 + 19*X^22 + 29*X^21 + 66*X^20 + 3*X^19 + 52*X^18 + 8*X^17 + 46*X^16 + 61*X^15 +
      44*X^14 + 8*X^13 + 49*X^12 + 56*X^11 + 48*X^10 + 44*X^9 + 50*X^8 + 15*X^7 + 47*X^6 + 16*X^5 +
      31*X^4 + 33*X^3 + 32*X^2 + 46*X + 49) :=
  sq_step (by norm_num) pSeventeenB4s208 ⟨
    37*X^32 + 51*X^31 + 23*X^30 + 57*X^29 + 39*X^28 + 34*X^27 + 23*X^26 + 33*X^25 + 56*X^24 + 26*X^23 +
      19*X^22 + 44*X^21 + 21*X^20 + 20*X^19 + 43*X^18 + 22*X^17 + 25*X^16 + 34*X^15 + 7*X^14 +
      30*X^13 + 3*X^12 + 57*X^11 + 17*X^10 + 26*X^9 + 66*X^8 + 19*X^7 + 7*X^6 + 13*X^5 + 16*X^4 +
      11*X^3 + 14*X^2 + 46*X + 24,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s210 : XPow fSeventeenB4 413526729497700784963176178858322509562759
    (X^33 + 56*X^32 + X^31 + 48*X^30 + 40*X^29 + 35*X^28 + 41*X^27 + 61*X^26 + 6*X^25 + 13*X^24 + 48*X^23 +
      55*X^22 + 6*X^21 + 46*X^20 + 38*X^19 + X^18 + 45*X^17 + 33*X^16 + 49*X^15 + 14*X^14 + 38*X^13 +
      54*X^12 + 32*X^11 + 33*X^10 + 31*X^9 + 50*X^8 + 57*X^7 + 30*X^6 + 14*X^5 + 28*X^4 + 2*X^3 +
      37*X^2 + 59*X + 3) :=
  mul_step (by norm_num) pSeventeenB4s209 pSeventeenB41 ⟨
    41,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s211 : XPow fSeventeenB4 827053458995401569926352357716645019125518
    (52*X^33 + 51*X^32 + 48*X^31 + 24*X^30 + 56*X^29 + 30*X^28 + 17*X^27 + 8*X^26 + 58*X^25 + 60*X^24 +
      44*X^23 + 51*X^22 + 51*X^21 + 64*X^20 + 36*X^19 + 11*X^18 + 35*X^17 + 40*X^16 + 30*X^14 +
      53*X^13 + 64*X^12 + 7*X^11 + 2*X^10 + 54*X^9 + 55*X^8 + 46*X^7 + 9*X^6 + 13*X^5 + 50*X^4 +
      20*X^3 + 66*X^2 + 55*X + 10) :=
  sq_step (by norm_num) pSeventeenB4s210 ⟨
    X^32 + 47*X^31 + 56*X^30 + 45*X^29 + 35*X^28 + 57*X^27 + 46*X^26 + 18*X^25 + 45*X^24 + 64*X^23 +
      51*X^22 + 10*X^21 + 46*X^20 + 46*X^19 + 24*X^18 + 53*X^17 + 51*X^16 + 64*X^15 + 62*X^14 +
      6*X^13 + 61*X^12 + 31*X^11 + 34*X^10 + X^9 + 11*X^8 + 13*X^7 + 48*X^6 + 54*X^5 + 36*X^4 +
      29*X^3 + 60*X^2 + 37*X + 36,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s212 : XPow fSeventeenB4 1654106917990803139852704715433290038251036
    (48*X^33 + 4*X^32 + 46*X^31 + 8*X^29 + 6*X^28 + 60*X^27 + 45*X^26 + 42*X^25 + 11*X^24 + 48*X^23 +
      6*X^22 + 38*X^21 + 29*X^20 + 58*X^19 + 28*X^18 + 19*X^17 + 39*X^16 + 58*X^15 + 35*X^14 +
      53*X^13 + 64*X^12 + 25*X^11 + 7*X^10 + 3*X^9 + 47*X^8 + 13*X^7 + 22*X^6 + 23*X^5 + 63*X^4 +
      34*X^3 + 12*X^2 + 34*X + 24) :=
  sq_step (by norm_num) pSeventeenB4s211 ⟨
    24*X^32 + 59*X^31 + 28*X^30 + 30*X^29 + 9*X^28 + 55*X^27 + 37*X^26 + 13*X^25 + 39*X^24 + 27*X^23 +
      50*X^22 + 50*X^21 + 33*X^20 + 64*X^19 + 3*X^18 + 66*X^17 + 25*X^16 + 53*X^15 + 5*X^14 +
      40*X^13 + 47*X^12 + 51*X^11 + 64*X^10 + 26*X^9 + 45*X^7 + 10*X^5 + 53*X^4 + 56*X^2 + 23*X + 11,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s213 : XPow fSeventeenB4 3308213835981606279705409430866580076502072
    (15*X^33 + 42*X^32 + 21*X^31 + 46*X^30 + 58*X^29 + 25*X^28 + 42*X^27 + 41*X^26 + 34*X^25 + 44*X^24 +
      33*X^23 + 9*X^22 + 50*X^21 + 5*X^20 + 36*X^19 + 57*X^18 + 33*X^17 + 42*X^16 + 16*X^15 +
      23*X^14 + 14*X^13 + 18*X^12 + 55*X^11 + 8*X^10 + 55*X^9 + 55*X^8 + 56*X^7 + 19*X^6 + 56*X^5 +
      9*X^4 + 30*X^3 + 15*X^2 + 29*X + 43) :=
  sq_step (by norm_num) pSeventeenB4s212 ⟨
    26*X^32 + 34*X^31 + 46*X^30 + 60*X^29 + 7*X^28 + 58*X^27 + 38*X^26 + 6*X^25 + 3*X^24 + 39*X^23 +
      44*X^22 + 11*X^21 + 56*X^20 + 31*X^19 + 46*X^18 + 29*X^17 + 11*X^16 + 43*X^15 + 3*X^14 +
      35*X^13 + 54*X^12 + 10*X^11 + 27*X^10 + 63*X^9 + 51*X^8 + 28*X^7 + 60*X^6 + 17*X^5 + 37*X^4 +
      6*X^3 + 15*X^2 + 21*X + 41,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s214 : XPow fSeventeenB4 6616427671963212559410818861733160153004144
    (56*X^33 + 28*X^32 + 29*X^31 + 14*X^30 + 65*X^29 + 36*X^28 + 45*X^27 + 43*X^26 + 39*X^25 + 25*X^24 +
      55*X^23 + 36*X^22 + 47*X^21 + 26*X^20 + 14*X^19 + 15*X^18 + 6*X^17 + 6*X^16 + 3*X^15 + 22*X^14 +
      25*X^13 + 62*X^12 + 60*X^11 + 66*X^10 + 40*X^9 + 27*X^8 + 62*X^7 + X^6 + 21*X^3 + 32*X + 46) :=
  sq_step (by norm_num) pSeventeenB4s213 ⟨
    24*X^32 + 35*X^31 + 7*X^30 + 6*X^29 + 13*X^28 + 16*X^27 + 30*X^26 + 58*X^25 + 57*X^24 + 14*X^23 +
      41*X^22 + 31*X^21 + 39*X^20 + 20*X^19 + 19*X^18 + 54*X^17 + 13*X^16 + 26*X^15 + 19*X^14 +
      38*X^13 + 7*X^12 + 2*X^11 + 58*X^10 + 36*X^9 + 4*X^8 + 20*X^7 + 65*X^6 + 31*X^5 + 38*X^4 +
      35*X^3 + 2*X^2 + 26*X + 15,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s215 : XPow fSeventeenB4 6616427671963212559410818861733160153004145
    (6*X^33 + 58*X^32 + X^31 + 54*X^30 + 37*X^29 + 24*X^28 + 5*X^27 + 65*X^26 + 52*X^25 + 56*X^24 +
      56*X^23 + 58*X^22 + 47*X^21 + 9*X^20 + 40*X^19 + 52*X^18 + 3*X^17 + 53*X^16 + 37*X^15 +
      43*X^14 + 29*X^13 + 54*X^12 + 18*X^11 + 7*X^10 + 37*X^9 + 33*X^8 + 31*X^7 + 42*X^6 + 16*X^5 +
      6*X^4 + 44*X^3 + 5*X^2 + 9*X + 9) :=
  mul_step (by norm_num) pSeventeenB4s214 pSeventeenB41 ⟨
    56,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s216 : XPow fSeventeenB4 13232855343926425118821637723466320306008290
    (10*X^33 + 27*X^32 + 55*X^31 + 38*X^30 + 42*X^29 + 66*X^28 + 19*X^27 + 20*X^26 + 9*X^25 + 36*X^24 +
      22*X^23 + 22*X^22 + 27*X^21 + 60*X^20 + 28*X^19 + 31*X^18 + 15*X^17 + 22*X^16 + X^15 + 46*X^14 +
      8*X^13 + 15*X^12 + 57*X^11 + 6*X^10 + 32*X^9 + 8*X^8 + 3*X^7 + 61*X^6 + 24*X^5 + 12*X^4 +
      36*X^3 + 41*X^2 + 60*X + 43) :=
  sq_step (by norm_num) pSeventeenB4s215 ⟨
    36*X^32 + 31*X^31 + 54*X^30 + 41*X^29 + 3*X^28 + 24*X^27 + 49*X^26 + 40*X^25 + 8*X^24 + 42*X^23 +
      35*X^22 + 63*X^21 + 57*X^20 + 33*X^19 + 28*X^18 + 58*X^17 + 12*X^16 + 20*X^15 + 54*X^14 +
      57*X^13 + 5*X^12 + 43*X^11 + 61*X^10 + 27*X^9 + 60*X^8 + 54*X^7 + 50*X^6 + 9*X^5 + 42*X^3 +
      48*X^2 + 17*X + 39,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s217 : XPow fSeventeenB4 13232855343926425118821637723466320306008291
    (47*X^33 + 53*X^32 + 62*X^31 + 52*X^30 + 59*X^29 + 32*X^28 + 18*X^27 + 28*X^26 + 48*X^25 + 15*X^24 +
      16*X^23 + 17*X^22 + 47*X^21 + 63*X^20 + 57*X^19 + 28*X^18 + 43*X^17 + 53*X^16 + 8*X^15 +
      16*X^14 + 45*X^13 + 32*X^12 + 7*X^11 + 62*X^10 + 5*X^9 + 5*X^8 + 52*X^7 + 65*X^6 + 34*X^5 +
      7*X^4 + X^3 + 48*X^2 + 34*X + 4) :=
  mul_step (by norm_num) pSeventeenB4s216 pSeventeenB41 ⟨
    10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s218 : XPow fSeventeenB4 26465710687852850237643275446932640612016582
    (59*X^33 + 16*X^31 + 47*X^30 + 63*X^29 + 44*X^28 + 57*X^27 + 42*X^26 + 49*X^25 + 32*X^24 + 6*X^23 +
      5*X^22 + 2*X^21 + 64*X^20 + 66*X^19 + 32*X^18 + 38*X^17 + 31*X^16 + 28*X^15 + 21*X^14 +
      32*X^13 + 24*X^12 + 10*X^11 + 39*X^10 + 27*X^9 + X^8 + 61*X^7 + 46*X^6 + 59*X^5 + 34*X^4 +
      20*X^3 + 63*X^2 + 59*X + 23) :=
  sq_step (by norm_num) pSeventeenB4s217 ⟨
    65*X^32 + 20*X^31 + 21*X^30 + 63*X^29 + 35*X^28 + 54*X^27 + 31*X^26 + 12*X^24 + 7*X^23 + 63*X^21 +
      17*X^20 + 48*X^19 + 15*X^18 + 18*X^17 + 44*X^16 + 32*X^15 + 34*X^14 + 52*X^13 + 39*X^12 +
      45*X^11 + 26*X^10 + 43*X^9 + 57*X^8 + 6*X^7 + 6*X^6 + 50*X^4 + 31*X^3 + 64*X^2 + X + 51,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s219 : XPow fSeventeenB4 26465710687852850237643275446932640612016583
    (51*X^33 + 31*X^32 + X^31 + 55*X^30 + 63*X^29 + 60*X^28 + 57*X^27 + 7*X^26 + 9*X^25 + 25*X^24 +
      50*X^23 + 10*X^22 + 61*X^21 + 38*X^20 + 38*X^19 + 41*X^18 + 41*X^17 + 40*X^16 + 38*X^15 +
      39*X^14 + 30*X^12 + 65*X^11 + 3*X^10 + 57*X^9 + 46*X^8 + 13*X^7 + 53*X^6 + 3*X^5 + 3*X^4 +
      28*X^3 + 15*X^2 + 57*X + 37) :=
  mul_step (by norm_num) pSeventeenB4s218 pSeventeenB41 ⟨
    59,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s220 : XPow fSeventeenB4 52931421375705700475286550893865281224033166
    (54*X^33 + 11*X^32 + 24*X^31 + 8*X^30 + 38*X^29 + 10*X^28 + 58*X^27 + 23*X^26 + 44*X^25 + 54*X^24 +
      46*X^22 + 58*X^21 + 59*X^20 + 37*X^19 + 5*X^18 + 37*X^17 + 44*X^16 + 33*X^15 + 61*X^14 +
      21*X^13 + 15*X^12 + 49*X^11 + 48*X^10 + 8*X^9 + 43*X^8 + 36*X^7 + 64*X^6 + 16*X^5 + 33*X^4 +
      22*X^3 + 21*X^2 + 50*X + 1) :=
  sq_step (by norm_num) pSeventeenB4s219 ⟨
    55*X^32 + 56*X^31 + 25*X^30 + 54*X^29 + 66*X^28 + 10*X^27 + 8*X^26 + 38*X^25 + 13*X^24 + 39*X^23 +
      20*X^22 + 40*X^21 + 55*X^20 + 7*X^19 + 24*X^18 + 34*X^17 + 25*X^16 + 56*X^15 + 23*X^14 +
      23*X^13 + 38*X^12 + 54*X^11 + 47*X^10 + 55*X^9 + 3*X^8 + 50*X^7 + 39*X^6 + 50*X^5 + 40*X^4 +
      29*X^3 + 61*X^2 + 42*X + 64,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s221 : XPow fSeventeenB4 52931421375705700475286550893865281224033167
    (52*X^33 + 40*X^32 + 17*X^31 + 25*X^30 + 66*X^29 + 21*X^28 + 39*X^27 + 26*X^26 + 25*X^25 + 56*X^24 +
      27*X^23 + 4*X^22 + 29*X^21 + 25*X^20 + 65*X^19 + 10*X^17 + 19*X^16 + 30*X^15 + 24*X^14 +
      43*X^13 + 48*X^12 + 40*X^11 + 36*X^10 + 20*X^8 + 2*X^7 + 23*X^6 + 58*X^5 + 53*X^4 + 6*X^3 +
      12*X^2 + 6*X + 35) :=
  mul_step (by norm_num) pSeventeenB4s220 pSeventeenB41 ⟨
    54,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s222 : XPow fSeventeenB4 105862842751411400950573101787730562448066334
    (16*X^33 + 47*X^32 + 58*X^31 + 24*X^30 + 55*X^29 + 47*X^28 + 66*X^27 + 46*X^26 + 28*X^25 + 38*X^24 +
      62*X^23 + 21*X^22 + 38*X^21 + 39*X^20 + 13*X^19 + 47*X^18 + 19*X^17 + 57*X^16 + 16*X^15 +
      64*X^14 + 53*X^13 + 35*X^12 + 60*X^11 + 22*X^10 + 48*X^9 + 64*X^8 + 9*X^7 + 49*X^6 + 37*X^5 +
      60*X^4 + 49*X^3 + 54*X^2 + X + 48) :=
  sq_step (by norm_num) pSeventeenB4s221 ⟨
    24*X^32 + 54*X^31 + 14*X^30 + 55*X^29 + 7*X^28 + 53*X^27 + 5*X^26 + 22*X^25 + 6*X^24 + 3*X^23 +
      10*X^22 + 21*X^21 + 56*X^20 + 20*X^19 + 21*X^18 + 35*X^17 + 26*X^16 + 20*X^15 + 19*X^14 +
      4*X^13 + 3*X^12 + 41*X^11 + 50*X^10 + 35*X^9 + 2*X^8 + 49*X^7 + 59*X^6 + 41*X^5 + 50*X^4 +
      24*X^3 + 44*X^2 + 62*X + 39,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s223 : XPow fSeventeenB4 105862842751411400950573101787730562448066335
    (12*X^33 + 28*X^32 + 49*X^31 + 4*X^30 + 9*X^29 + 60*X^28 + 16*X^27 + 45*X^26 + 17*X^25 + 24*X^24 +
      65*X^23 + 22*X^22 + 45*X^21 + 2*X^20 + 35*X^19 + 13*X^18 + 37*X^17 + 59*X^16 + 30*X^15 +
      39*X^14 + 16*X^13 + 20*X^12 + 37*X^11 + 29*X^10 + 19*X^9 + 39*X^8 + 48*X^7 + 49*X^6 + 55*X^5 +
      16*X^4 + 57*X^3 + 22*X^2 + 47*X + 60) :=
  mul_step (by norm_num) pSeventeenB4s222 pSeventeenB41 ⟨
    16,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s224 : XPow fSeventeenB4 211725685502822801901146203575461124896132670
    (13*X^33 + 4*X^32 + 9*X^31 + 6*X^30 + 44*X^29 + 25*X^28 + 37*X^27 + 25*X^26 + 34*X^25 + 19*X^24 +
      32*X^23 + 30*X^22 + 52*X^21 + 62*X^20 + 12*X^19 + 12*X^18 + 19*X^17 + 37*X^16 + X^15 + 35*X^14 +
      58*X^13 + 23*X^12 + 57*X^11 + 17*X^10 + 22*X^9 + 62*X^8 + 57*X^7 + 6*X^6 + 66*X^5 + 44*X^4 +
      21*X^3 + 36*X^2 + 44*X + 52) :=
  sq_step (by norm_num) pSeventeenB4s223 ⟨
    10*X^32 + 22*X^31 + 59*X^30 + 43*X^29 + 30*X^28 + 65*X^27 + 8*X^26 + 65*X^25 + 19*X^24 + 9*X^23 +
      14*X^22 + 52*X^21 + 6*X^20 + 56*X^19 + 51*X^18 + 23*X^17 + 24*X^16 + 45*X^15 + 8*X^14 +
      36*X^13 + 53*X^12 + 44*X^11 + 18*X^10 + 35*X^9 + 38*X^8 + 24*X^7 + 23*X^6 + 42*X^5 + 63*X^4 +
      23*X^2 + 55*X + 41,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s225 : XPow fSeventeenB4 423451371005645603802292407150922249792265340
    (18*X^33 + 4*X^32 + 57*X^31 + 41*X^30 + 27*X^29 + 43*X^28 + 37*X^27 + 52*X^26 + 6*X^25 + 47*X^24 +
      63*X^23 + 38*X^22 + 24*X^21 + 48*X^20 + 15*X^19 + 41*X^18 + X^17 + 64*X^16 + 2*X^15 + 15*X^14 +
      19*X^13 + 41*X^12 + 52*X^11 + 38*X^10 + 47*X^9 + 31*X^8 + 66*X^7 + 56*X^6 + 34*X^5 + 28*X^4 +
      16*X^3 + 46*X^2 + 31*X + 13) :=
  sq_step (by norm_num) pSeventeenB4s224 ⟨
    35*X^32 + 40*X^31 + 55*X^30 + 12*X^29 + 10*X^28 + 49*X^27 + 50*X^26 + 40*X^25 + 44*X^24 + 17*X^23 +
      56*X^22 + 53*X^21 + 36*X^20 + 28*X^19 + 42*X^18 + 60*X^17 + 61*X^16 + 55*X^14 + 37*X^13 +
      50*X^12 + 25*X^11 + 30*X^10 + 48*X^9 + 26*X^8 + 63*X^7 + 33*X^6 + 35*X^5 + 43*X^4 + 26*X^3 +
      45*X^2 + 41*X + 6,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s226 : XPow fSeventeenB4 846902742011291207604584814301844499584530680
    (19*X^33 + 37*X^32 + 28*X^31 + 40*X^30 + 36*X^29 + 48*X^28 + 41*X^27 + 11*X^26 + 5*X^25 + 42*X^24 +
      42*X^23 + X^22 + 28*X^20 + 48*X^19 + 57*X^18 + 45*X^17 + 25*X^16 + 15*X^15 + 29*X^14 + 6*X^13 +
      22*X^12 + 45*X^11 + 19*X^10 + 14*X^9 + 28*X^8 + 62*X^7 + 34*X^6 + 4*X^5 + 3*X^4 + 19*X^3 +
      33*X^2 + 11*X + 62) :=
  sq_step (by norm_num) pSeventeenB4s225 ⟨
    56*X^32 + 55*X^31 + 63*X^30 + 24*X^29 + 2*X^28 + 65*X^27 + 53*X^26 + 42*X^25 + 3*X^24 + 63*X^23 +
      25*X^22 + 19*X^21 + 17*X^20 + 47*X^19 + 17*X^18 + 27*X^17 + 7*X^16 + 33*X^15 + 28*X^14 +
      54*X^13 + 65*X^12 + 37*X^11 + 45*X^10 + 15*X^9 + 31*X^8 + 12*X^7 + 13*X^6 + X^5 + 9*X^4 +
      20*X^3 + 23*X^2 + 32*X + 34,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s227 : XPow fSeventeenB4 1693805484022582415209169628603688999169061360
    (12*X^33 + 4*X^32 + 47*X^31 + 38*X^30 + 30*X^29 + 45*X^28 + 63*X^27 + 40*X^26 + 59*X^25 + 24*X^24 +
      64*X^23 + 26*X^22 + 58*X^21 + 50*X^20 + 59*X^19 + 35*X^18 + 46*X^17 + 18*X^15 + 2*X^14 +
      59*X^13 + 62*X^12 + 35*X^11 + 41*X^10 + 59*X^9 + 38*X^8 + 56*X^7 + 20*X^6 + 48*X^5 + 32*X^4 +
      26*X^3 + 12*X^2 + 57*X + 16) :=
  sq_step (by norm_num) pSeventeenB4s226 ⟨
    26*X^32 + 51*X^31 + 24*X^30 + 34*X^29 + 44*X^28 + 12*X^27 + 21*X^26 + 31*X^25 + 64*X^24 + 11*X^23 +
      59*X^22 + 53*X^21 + 50*X^20 + 47*X^19 + 54*X^18 + 63*X^17 + 47*X^16 + X^15 + 18*X^14 + 9*X^13 +
      29*X^12 + 24*X^11 + 61*X^10 + 21*X^9 + 35*X^8 + 40*X^7 + 34*X^6 + 28*X^5 + 56*X^4 + 55*X^3 +
      27*X^2 + 57*X + 11,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s228 : XPow fSeventeenB4 1693805484022582415209169628603688999169061361
    (28*X^33 + 58*X^32 + 40*X^31 + 42*X^30 + 50*X^29 + 25*X^28 + 51*X^27 + 55*X^26 + 25*X^25 + 2*X^24 +
      59*X^23 + 46*X^22 + 21*X^21 + 34*X^20 + 26*X^19 + 8*X^18 + 52*X^17 + 10*X^15 + 15*X^14 +
      31*X^13 + 5*X^12 + 2*X^11 + 28*X^10 + 21*X^9 + 45*X^8 + 36*X^7 + 57*X^6 + 45*X^5 + 18*X^4 +
      31*X^3 + 56*X^2 + 32*X + 45) :=
  mul_step (by norm_num) pSeventeenB4s227 pSeventeenB41 ⟨
    12,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s229 : XPow fSeventeenB4 3387610968045164830418339257207377998338122722
    (46*X^33 + 64*X^32 + 39*X^31 + 39*X^30 + 35*X^29 + 62*X^28 + 36*X^27 + 35*X^26 + 35*X^25 + 46*X^24 +
      53*X^23 + 12*X^22 + 57*X^21 + 49*X^20 + 58*X^19 + 12*X^18 + 26*X^17 + 37*X^16 + 43*X^15 +
      42*X^14 + 10*X^13 + 58*X^12 + 4*X^11 + 57*X^10 + 27*X^9 + 14*X^8 + 7*X^7 + 29*X^6 + 60*X^5 +
      52*X^4 + 52*X^3 + 14*X^2 + 3*X + 48) :=
  sq_step (by norm_num) pSeventeenB4s228 ⟨
    47*X^32 + 59*X^31 + 31*X^30 + 53*X^29 + 33*X^28 + 16*X^27 + 52*X^26 + 11*X^25 + X^24 + 66*X^23 +
      42*X^22 + 15*X^21 + 34*X^20 + 25*X^19 + 27*X^17 + 20*X^16 + 7*X^15 + 58*X^14 + 42*X^13 +
      46*X^12 + 16*X^11 + 45*X^10 + 64*X^9 + 40*X^8 + 62*X^7 + 25*X^6 + 9*X^5 + 40*X^4 + 15*X^3 +
      20*X^2 + 3*X + 49,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s230 : XPow fSeventeenB4 6775221936090329660836678514414755996676245444
    (45*X^33 + 27*X^32 + 64*X^31 + 12*X^30 + 6*X^29 + 51*X^28 + 17*X^27 + 3*X^26 + 22*X^25 + 44*X^24 +
      60*X^23 + 45*X^22 + 22*X^21 + 61*X^20 + 22*X^19 + 62*X^18 + 12*X^17 + 21*X^16 + 61*X^15 +
      58*X^14 + 58*X^13 + 4*X^12 + 53*X^11 + 12*X^10 + 29*X^9 + 49*X^8 + 12*X^7 + 56*X^6 + 52*X^5 +
      8*X^4 + 19*X^3 + 45*X^2 + 60*X + 64) :=
  sq_step (by norm_num) pSeventeenB4s229 ⟨
    39*X^32 + 3*X^31 + 4*X^30 + 38*X^29 + 59*X^28 + 49*X^27 + 51*X^26 + 28*X^25 + 60*X^24 + 55*X^23 +
      63*X^22 + 28*X^21 + 47*X^20 + 45*X^19 + 15*X^18 + 57*X^17 + 66*X^16 + 26*X^15 + 63*X^14 +
      40*X^13 + 53*X^12 + 8*X^11 + 40*X^10 + 2*X^9 + 22*X^8 + 49*X^7 + 22*X^6 + 44*X^5 + 20*X^4 +
      3*X^3 + 45*X^2 + 29*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s231 : XPow fSeventeenB4 13550443872180659321673357028829511993352490888
    (23*X^33 + 28*X^32 + 23*X^31 + 60*X^30 + 62*X^29 + 16*X^28 + 11*X^27 + 14*X^26 + 57*X^25 + 34*X^24 +
      3*X^23 + 21*X^22 + 18*X^21 + 39*X^20 + 47*X^19 + 58*X^18 + 17*X^17 + 25*X^16 + 21*X^15 +
      65*X^14 + 3*X^13 + 35*X^12 + 39*X^11 + 27*X^10 + 3*X^9 + 32*X^8 + 16*X^7 + 37*X^6 + 49*X^5 +
      40*X^4 + 8*X^3 + 48*X^2 + 47*X + 47) :=
  sq_step (by norm_num) pSeventeenB4s230 ⟨
    15*X^32 + 48*X^31 + 16*X^30 + 25*X^29 + 34*X^28 + 43*X^27 + 24*X^26 + 41*X^25 + 66*X^24 + 37*X^23 +
      44*X^22 + 66*X^21 + 12*X^20 + 65*X^19 + 32*X^18 + 48*X^17 + 60*X^16 + 9*X^15 + 22*X^14 +
      53*X^13 + 16*X^12 + 9*X^11 + 63*X^10 + 50*X^9 + 14*X^8 + 6*X^7 + 38*X^6 + 39*X^5 + 4*X^4 +
      30*X^3 + 47*X^2 + 42*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s232 : XPow fSeventeenB4 27100887744361318643346714057659023986704981776
    (47*X^33 + 13*X^32 + 56*X^31 + 55*X^30 + 35*X^29 + 43*X^28 + 48*X^27 + 32*X^26 + 30*X^25 + 19*X^24 +
      50*X^23 + 45*X^22 + 45*X^21 + 60*X^20 + 12*X^19 + 14*X^18 + 31*X^17 + 61*X^16 + 27*X^15 +
      8*X^14 + 37*X^13 + 15*X^12 + 28*X^11 + 49*X^10 + 16*X^9 + 38*X^8 + 42*X^7 + 43*X^6 + 14*X^5 +
      26*X^4 + 39*X^3 + 46*X^2 + 34) :=
  sq_step (by norm_num) pSeventeenB4s231 ⟨
    60*X^32 + X^31 + 23*X^30 + 57*X^29 + 52*X^28 + 13*X^27 + 60*X^26 + 47*X^25 + 29*X^24 + 52*X^23 +
      44*X^22 + 45*X^21 + 23*X^20 + 41*X^19 + 15*X^18 + 52*X^17 + 6*X^16 + 44*X^15 + 24*X^14 +
      42*X^13 + 33*X^12 + 53*X^11 + 25*X^10 + 58*X^9 + 33*X^8 + 47*X^7 + 56*X^6 + 47*X^5 + 54*X^4 +
      16*X^3 + 15*X^2 + 45*X + 23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s233 : XPow fSeventeenB4 27100887744361318643346714057659023986704981777
    (40*X^33 + 60*X^32 + 7*X^31 + 15*X^30 + 57*X^29 + 22*X^28 + 36*X^27 + 59*X^26 + 62*X^25 + 64*X^24 +
      57*X^23 + 65*X^22 + 19*X^21 + 9*X^20 + 29*X^19 + 5*X^18 + 19*X^17 + 57*X^16 + 17*X^15 +
      21*X^14 + 22*X^13 + 11*X^12 + 47*X^11 + 23*X^10 + 44*X^9 + 38*X^8 + 61*X^7 + 66*X^6 + 49*X^5 +
      30*X^4 + 59*X^3 + 24*X^2 + 52*X + 59) :=
  mul_step (by norm_num) pSeventeenB4s232 pSeventeenB41 ⟨
    47,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s234 : XPow fSeventeenB4 54201775488722637286693428115318047973409963554
    (50*X^33 + 38*X^32 + 20*X^31 + 52*X^30 + 27*X^29 + 59*X^28 + 37*X^27 + 8*X^26 + 7*X^25 + 4*X^24 +
      11*X^23 + X^22 + 57*X^21 + 20*X^20 + 64*X^19 + 4*X^18 + 57*X^17 + 24*X^16 + 31*X^15 + 4*X^14 +
      47*X^13 + 40*X^12 + 55*X^11 + 57*X^10 + 60*X^9 + 49*X^8 + 13*X^7 + 38*X^6 + 32*X^5 + 21*X^4 +
      13*X^3 + 36*X^2 + 36*X + 28) :=
  sq_step (by norm_num) pSeventeenB4s233 ⟨
    59*X^32 + 27*X^31 + 8*X^30 + 8*X^29 + 8*X^28 + 59*X^27 + 31*X^26 + 11*X^25 + 45*X^23 + 50*X^22 +
      3*X^21 + 59*X^20 + 3*X^19 + 47*X^18 + 54*X^17 + 9*X^16 + 5*X^15 + 31*X^14 + 23*X^13 + 51*X^12 +
      30*X^11 + 8*X^10 + 20*X^9 + 6*X^8 + 31*X^7 + 2*X^6 + 32*X^5 + 22*X^4 + 62*X^3 + 13*X^2 + 58*X +
      44,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s235 : XPow fSeventeenB4 108403550977445274573386856230636095946819927108
    (57*X^33 + 31*X^32 + 6*X^31 + 50*X^30 + 14*X^29 + 62*X^28 + 9*X^27 + 16*X^26 + 50*X^25 + 51*X^24 +
      24*X^23 + 6*X^22 + 8*X^21 + 34*X^20 + 15*X^19 + 59*X^18 + 64*X^17 + 23*X^16 + 65*X^15 +
      18*X^14 + 25*X^13 + 57*X^12 + 32*X^11 + 27*X^9 + 52*X^8 + 17*X^7 + 39*X^6 + 50*X^5 + 9*X^4 +
      54*X^3 + 34*X^2 + 6*X + 36) :=
  sq_step (by norm_num) pSeventeenB4s234 ⟨
    21*X^32 + 23*X^31 + 42*X^30 + 56*X^29 + 36*X^28 + 38*X^27 + 17*X^26 + 14*X^25 + 40*X^24 + 21*X^23 +
      14*X^22 + 40*X^21 + 46*X^20 + 10*X^19 + X^18 + 26*X^17 + 10*X^16 + 57*X^15 + 21*X^14 + 47*X^13 +
      55*X^12 + 59*X^11 + 5*X^10 + 63*X^9 + 62*X^8 + 18*X^7 + X^6 + 2*X^5 + 41*X^4 + 35*X^3 + 19*X^2 +
      47*X + 6,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s236 : XPow fSeventeenB4 216807101954890549146773712461272191893639854216
    (15*X^33 + 36*X^32 + 66*X^31 + 43*X^30 + 39*X^29 + 52*X^28 + 41*X^27 + X^26 + 53*X^25 + 47*X^23 +
      20*X^22 + 49*X^21 + 26*X^20 + 62*X^18 + X^17 + 32*X^16 + 38*X^15 + 60*X^14 + 40*X^13 + 13*X^12 +
      26*X^11 + 55*X^10 + 5*X^9 + 33*X^8 + 10*X^7 + 21*X^6 + 25*X^5 + 45*X^4 + 22*X^2 + 46*X + 13) :=
  sq_step (by norm_num) pSeventeenB4s235 ⟨
    33*X^32 + 49*X^31 + 48*X^30 + 60*X^29 + 35*X^28 + 5*X^27 + 50*X^26 + 2*X^25 + 51*X^24 + 45*X^23 +
      57*X^22 + 65*X^21 + 61*X^20 + 56*X^19 + 26*X^18 + 60*X^17 + 33*X^16 + 20*X^15 + 34*X^14 +
      54*X^13 + 52*X^12 + 45*X^11 + 44*X^10 + 64*X^9 + 60*X^8 + 11*X^7 + 26*X^6 + 16*X^5 + 14*X^4 +
      65*X^3 + 44*X^2 + 34*X + 42,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s237 : XPow fSeventeenB4 216807101954890549146773712461272191893639854217
    (66*X^33 + 63*X^32 + 12*X^31 + 54*X^30 + 8*X^29 + 27*X^28 + 65*X^27 + 48*X^26 + 18*X^25 + 3*X^24 +
      11*X^23 + 34*X^22 + 40*X^21 + 19*X^20 + 34*X^19 + 54*X^18 + 30*X^17 + 49*X^16 + 3*X^15 +
      52*X^14 + 58*X^13 + 22*X^12 + 23*X^11 + 50*X^10 + 62*X^9 + 13*X^8 + 41*X^7 + 53*X^6 + 11*X^5 +
      57*X^4 + 29*X^3 + 28*X^2 + 33*X + 6) :=
  mul_step (by norm_num) pSeventeenB4s236 pSeventeenB41 ⟨
    15,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s238 : XPow fSeventeenB4 433614203909781098293547424922544383787279708434
    (2*X^33 + 62*X^32 + 48*X^31 + 6*X^30 + 7*X^29 + 40*X^28 + 63*X^27 + 65*X^26 + 62*X^25 + 8*X^24 +
      28*X^23 + 3*X^22 + 19*X^21 + 10*X^20 + 35*X^19 + 52*X^18 + 19*X^17 + 10*X^16 + 58*X^14 +
      50*X^13 + 54*X^12 + 39*X^11 + 49*X^10 + 47*X^9 + 33*X^8 + 53*X^7 + 64*X^5 + 54*X^4 + 10*X^3 +
      25*X^2 + 59*X + 38) :=
  sq_step (by norm_num) pSeventeenB4s237 ⟨
    X^32 + 10*X^31 + 52*X^30 + 21*X^29 + 34*X^28 + 56*X^27 + 36*X^26 + 4*X^25 + 54*X^24 + 27*X^23 +
      28*X^22 + 19*X^21 + 54*X^20 + 56*X^19 + 9*X^18 + 54*X^17 + 53*X^16 + 36*X^15 + 33*X^14 +
      31*X^13 + 51*X^11 + 63*X^10 + 50*X^9 + 31*X^8 + 4*X^7 + 13*X^6 + 23*X^5 + 49*X^4 + 57*X^3 +
      34*X^2 + 23*X + 5,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s239 : XPow fSeventeenB4 867228407819562196587094849845088767574559416868
    (2*X^33 + 19*X^32 + 55*X^31 + 48*X^30 + 11*X^29 + 19*X^28 + 61*X^27 + 11*X^26 + 14*X^25 + 32*X^24 +
      61*X^23 + 46*X^22 + 52*X^20 + 23*X^19 + 22*X^18 + 65*X^17 + 51*X^16 + 27*X^15 + 24*X^14 +
      8*X^13 + 35*X^12 + X^11 + 13*X^10 + 36*X^9 + 34*X^8 + 52*X^7 + 47*X^6 + 66*X^5 + 51*X^4 +
      39*X^3 + 19*X^2 + 66*X + 46) :=
  sq_step (by norm_num) pSeventeenB4s238 ⟨
    4*X^32 + 55*X^31 + 18*X^30 + 61*X^29 + 34*X^28 + 40*X^27 + 34*X^26 + 56*X^25 + 56*X^24 + 62*X^23 +
      61*X^22 + 41*X^21 + X^20 + 12*X^19 + 52*X^18 + 55*X^17 + 24*X^16 + 12*X^15 + 22*X^14 + 24*X^13 +
      60*X^12 + 57*X^11 + 10*X^10 + 36*X^9 + 42*X^8 + 31*X^7 + 5*X^6 + 37*X^5 + 14*X^4 + 65*X^3 +
      2*X + 56,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s240 : XPow fSeventeenB4 867228407819562196587094849845088767574559416869
    (23*X^33 + X^32 + 26*X^31 + 13*X^30 + 31*X^29 + 10*X^28 + 24*X^27 + 58*X^26 + 21*X^25 + 6*X^24 +
      18*X^23 + 65*X^22 + 36*X^21 + 30*X^20 + 54*X^19 + 14*X^18 + 15*X^17 + 24*X^16 + 3*X^15 +
      23*X^14 + 41*X^13 + 63*X^12 + 40*X^11 + 42*X^10 + 20*X^9 + 39*X^8 + 5*X^7 + 34*X^6 + 42*X^5 +
      60*X^4 + 11*X^3 + 10*X^2 + 4*X + 41) :=
  mul_step (by norm_num) pSeventeenB4s239 pSeventeenB41 ⟨
    2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s241 : XPow fSeventeenB4 1734456815639124393174189699690177535149118833738
    (X^33 + 58*X^32 + 56*X^31 + 31*X^30 + 50*X^29 + 7*X^28 + 58*X^27 + 11*X^26 + 37*X^25 + 18*X^24 +
      51*X^23 + 57*X^22 + 57*X^21 + 16*X^20 + 17*X^19 + 23*X^18 + 60*X^17 + 63*X^16 + 30*X^14 +
      49*X^13 + 44*X^12 + 5*X^11 + 48*X^10 + 2*X^9 + 21*X^8 + 47*X^7 + 20*X^6 + 22*X^5 + 39*X^4 +
      56*X^3 + 59*X^2 + 48*X + 3) :=
  sq_step (by norm_num) pSeventeenB4s240 ⟨
    60*X^32 + 32*X^31 + 43*X^30 + 16*X^29 + 37*X^28 + 22*X^27 + 10*X^26 + 28*X^25 + 8*X^24 + 30*X^23 +
      5*X^22 + 9*X^21 + 46*X^20 + 25*X^19 + 8*X^18 + 30*X^17 + 9*X^16 + 56*X^15 + 66*X^14 + 27*X^13 +
      43*X^12 + 30*X^11 + 32*X^10 + 55*X^9 + 64*X^8 + 63*X^7 + X^6 + 46*X^5 + 18*X^4 + 62*X^3 +
      17*X^2 + 62*X + 26,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s242 : XPow fSeventeenB4 3468913631278248786348379399380355070298237667476
    (14*X^33 + 5*X^32 + 4*X^31 + 9*X^30 + 10*X^29 + 5*X^28 + 48*X^27 + 35*X^26 + 55*X^25 + 38*X^24 +
      61*X^23 + 56*X^22 + 53*X^21 + 61*X^20 + 52*X^19 + 15*X^18 + 7*X^17 + 51*X^16 + 23*X^15 +
      49*X^14 + 18*X^13 + 25*X^12 + 65*X^11 + 36*X^10 + 5*X^9 + 6*X^8 + 6*X^7 + 22*X^6 + 57*X^5 +
      7*X^4 + 6*X^3 + 54*X^2 + 43*X + 49) :=
  sq_step (by norm_num) pSeventeenB4s241 ⟨
    X^32 + 51*X^31 + 11*X^29 + 63*X^28 + 60*X^27 + 4*X^26 + 11*X^25 + 31*X^24 + 64*X^23 + 37*X^22 +
      24*X^21 + 46*X^20 + 32*X^19 + 14*X^18 + 12*X^17 + 2*X^16 + 8*X^15 + 43*X^14 + 66*X^13 +
      59*X^12 + 54*X^11 + 40*X^10 + 48*X^9 + 15*X^8 + 30*X^7 + 61*X^6 + 66*X^5 + 54*X^4 + 62*X^2 +
      48*X + 33,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s243 : XPow fSeventeenB4 3468913631278248786348379399380355070298237667477
    (33*X^33 + 28*X^32 + 56*X^31 + 24*X^30 + 22*X^29 + 26*X^28 + 59*X^27 + 28*X^26 + 28*X^25 + 11*X^24 +
      61*X^23 + 39*X^22 + 16*X^21 + 34*X^20 + 38*X^19 + 52*X^18 + 2*X^16 + 36*X^15 + 56*X^14 +
      30*X^12 + 24*X^11 + 47*X^10 + 42*X^9 + 49*X^8 + 63*X^7 + 34*X^6 + 11*X^5 + 19*X^4 + 65*X^3 +
      53*X^2 + 23*X + 19) :=
  mul_step (by norm_num) pSeventeenB4s242 pSeventeenB41 ⟨
    14,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s244 : XPow fSeventeenB4 6937827262556497572696758798760710140596475334954
    (28*X^33 + 2*X^32 + 51*X^31 + 38*X^30 + 31*X^29 + 61*X^28 + 36*X^27 + 16*X^26 + 5*X^25 + 47*X^24 +
      59*X^23 + 55*X^22 + 46*X^21 + 28*X^20 + 24*X^19 + 63*X^18 + 32*X^17 + 50*X^16 + 8*X^15 +
      57*X^14 + 44*X^13 + 14*X^12 + 12*X^11 + 4*X^10 + 60*X^9 + 32*X^8 + X^7 + 39*X^6 + 55*X^5 +
      53*X^4 + 7*X^3 + 52*X^2 + 15*X + 61) :=
  sq_step (by norm_num) pSeventeenB4s243 ⟨
    17*X^32 + 6*X^31 + 13*X^30 + 42*X^29 + 55*X^28 + 21*X^27 + 37*X^26 + 26*X^25 + 12*X^24 + 19*X^23 +
      55*X^22 + 20*X^21 + 22*X^20 + 64*X^19 + 63*X^18 + 49*X^17 + 39*X^16 + 25*X^15 + 38*X^14 +
      55*X^13 + 28*X^12 + 49*X^11 + 43*X^10 + 51*X^9 + 2*X^8 + 12*X^7 + 51*X^6 + 23*X^5 + 40*X^4 +
      13*X^3 + 29*X^2 + 51*X + 54,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s245 : XPow fSeventeenB4 6937827262556497572696758798760710140596475334955
    (58*X^33 + 32*X^32 + 65*X^31 + 59*X^30 + 28*X^29 + 59*X^28 + 64*X^27 + 18*X^26 + 27*X^25 + 26*X^24 +
      65*X^23 + 18*X^22 + 5*X^21 + 55*X^20 + 42*X^19 + 55*X^18 + 15*X^17 + 33*X^16 + 31*X^15 +
      53*X^14 + 31*X^13 + 9*X^12 + 47*X^11 + 10*X^10 + 37*X^9 + 20*X^8 + 54*X^7 + 9*X^6 + 61*X^5 +
      33*X^4 + 7*X^3 + 35*X^2 + 9*X + 38) :=
  mul_step (by norm_num) pSeventeenB4s244 pSeventeenB41 ⟨
    28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s246 : XPow fSeventeenB4 13875654525112995145393517597521420281192950669910
    (55*X^33 + 21*X^32 + 10*X^31 + 66*X^30 + 64*X^29 + 20*X^28 + 3*X^27 + 38*X^26 + 16*X^25 + 30*X^24 +
      34*X^23 + 42*X^22 + 28*X^21 + 37*X^20 + 29*X^19 + 58*X^18 + 61*X^17 + 5*X^16 + 12*X^15 +
      42*X^14 + 34*X^13 + 19*X^12 + 40*X^11 + 12*X^10 + 66*X^9 + 30*X^8 + 47*X^7 + 17*X^6 + 57*X^5 +
      12*X^4 + 19*X^3 + 21*X^2 + 6) :=
  sq_step (by norm_num) pSeventeenB4s245 ⟨
    14*X^32 + 55*X^31 + 55*X^30 + 28*X^29 + 50*X^28 + 42*X^27 + 25*X^26 + 65*X^25 + 64*X^24 + 38*X^23 +
      47*X^22 + 57*X^21 + 58*X^20 + 21*X^19 + 25*X^18 + 65*X^17 + 13*X^16 + 19*X^15 + 37*X^14 +
      23*X^13 + 29*X^12 + 17*X^11 + 8*X^10 + 27*X^9 + 53*X^8 + 11*X^7 + 61*X^6 + 52*X^5 + 11*X^4 +
      33*X^3 + 36*X^2 + 23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s247 : XPow fSeventeenB4 13875654525112995145393517597521420281192950669911
    (64*X^33 + 66*X^32 + 64*X^31 + 52*X^30 + 15*X^29 + 41*X^28 + 27*X^27 + 20*X^26 + 29*X^25 + 29*X^24 +
      9*X^23 + 40*X^22 + 66*X^21 + 54*X^20 + 32*X^18 + 20*X^17 + 30*X^16 + 34*X^15 + 11*X^14 +
      50*X^13 + 3*X^12 + 51*X^11 + 30*X^10 + 47*X^9 + 58*X^8 + X^7 + 48*X^6 + 66*X^5 + 27*X^4 +
      2*X^3 + X^2 + 57*X + 22) :=
  mul_step (by norm_num) pSeventeenB4s246 pSeventeenB41 ⟨
    55,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s248 : XPow fSeventeenB4 27751309050225990290787035195042840562385901339822
    (22*X^33 + 38*X^32 + 23*X^31 + 57*X^30 + 37*X^29 + 41*X^28 + 22*X^27 + 7*X^26 + 20*X^25 + 55*X^24 +
      48*X^23 + 5*X^22 + 57*X^21 + 5*X^20 + 36*X^19 + 51*X^18 + 17*X^17 + 38*X^16 + 49*X^15 +
      15*X^14 + 57*X^13 + 18*X^12 + 35*X^11 + 31*X^10 + 18*X^9 + 42*X^8 + 49*X^7 + X^6 + 9*X^5 +
      23*X^4 + 13*X^3 + 37*X^2 + 46*X + 56) :=
  sq_step (by norm_num) pSeventeenB4s247 ⟨
    9*X^32 + 24*X^31 + 25*X^30 + 2*X^29 + 28*X^28 + 21*X^27 + 66*X^26 + 29*X^25 + 5*X^24 + 18*X^23 +
      11*X^22 + 51*X^21 + 53*X^20 + 7*X^19 + 58*X^18 + 65*X^17 + 52*X^16 + 36*X^15 + 65*X^14 +
      35*X^13 + 3*X^12 + 33*X^11 + 65*X^10 + 65*X^9 + 30*X^8 + 17*X^7 + 20*X^6 + 21*X^5 + 48*X^4 +
      29*X^3 + 62*X^2 + 47*X + 2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s249 : XPow fSeventeenB4 55502618100451980581574070390085681124771802679644
    (30*X^33 + 15*X^32 + 20*X^31 + 25*X^30 + 21*X^29 + 56*X^28 + 61*X^27 + 22*X^26 + 17*X^25 + 20*X^24 +
      44*X^23 + 43*X^22 + 59*X^21 + 8*X^20 + 35*X^19 + 49*X^18 + 52*X^17 + 7*X^16 + 3*X^15 + 42*X^14 +
      53*X^13 + 24*X^12 + 17*X^11 + 47*X^10 + 16*X^9 + 28*X^8 + 12*X^6 + 35*X^5 + 15*X^4 + 48*X^3 +
      39*X^2 + 34*X + 14) :=
  sq_step (by norm_num) pSeventeenB4s248 ⟨
    15*X^32 + 27*X^31 + 28*X^30 + X^29 + 26*X^28 + 37*X^27 + 63*X^26 + 4*X^25 + 60*X^24 + X^23 + 61*X^22 +
      47*X^21 + 43*X^20 + 49*X^19 + 2*X^18 + 22*X^17 + 21*X^16 + 24*X^15 + 42*X^14 + 11*X^13 +
      28*X^12 + 37*X^11 + 36*X^10 + 64*X^9 + 64*X^8 + 49*X^7 + X^5 + 59*X^4 + X^3 + 44*X^2 + 45*X +
      34,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s250 : XPow fSeventeenB4 111005236200903961163148140780171362249543605359288
    (59*X^33 + 22*X^32 + 48*X^31 + 44*X^30 + 25*X^29 + 40*X^28 + 17*X^27 + 2*X^26 + 29*X^25 + 46*X^23 +
      10*X^22 + 12*X^21 + 15*X^20 + 2*X^19 + 7*X^18 + 39*X^17 + 60*X^16 + 14*X^15 + 8*X^14 + 30*X^13 +
      24*X^11 + 12*X^10 + 54*X^9 + 36*X^8 + 39*X^7 + 29*X^6 + 19*X^5 + 35*X^4 + 12*X^3 + 61*X^2 +
      53*X + 31) :=
  sq_step (by norm_num) pSeventeenB4s249 ⟨
    29*X^32 + 20*X^31 + 12*X^30 + 59*X^29 + 3*X^28 + 48*X^27 + 36*X^26 + X^25 + 49*X^24 + 21*X^23 +
      65*X^21 + 42*X^20 + 34*X^19 + 30*X^18 + 12*X^17 + 64*X^16 + 41*X^14 + 34*X^13 + 40*X^12 +
      63*X^11 + 27*X^10 + 52*X^9 + 32*X^8 + 58*X^7 + 2*X^6 + 5*X^4 + 14*X^3 + 32*X + 23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s251 : XPow fSeventeenB4 111005236200903961163148140780171362249543605359289
    (6*X^33 + 63*X^32 + 65*X^31 + 17*X^30 + 59*X^29 + 20*X^28 + 17*X^27 + 54*X^26 + 44*X^25 + 65*X^24 +
      55*X^23 + 20*X^22 + 12*X^21 + 41*X^20 + 13*X^19 + 42*X^18 + 3*X^17 + 26*X^16 + 25*X^15 +
      37*X^14 + 43*X^13 + 44*X^12 + 38*X^11 + 30*X^10 + 25*X^9 + 24*X^8 + 63*X^7 + 13*X^6 + 4*X^5 +
      62*X^4 + 26*X^3 + 9*X^2 + 65*X + 37) :=
  mul_step (by norm_num) pSeventeenB4s250 pSeventeenB41 ⟨
    59,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s252 : XPow fSeventeenB4 222010472401807922326296281560342724499087210718578
    (7*X^33 + 57*X^32 + 51*X^31 + 24*X^30 + 26*X^29 + 60*X^27 + 14*X^26 + 55*X^25 + 65*X^24 + 4*X^23 +
      9*X^22 + 19*X^21 + 26*X^20 + 16*X^19 + 27*X^18 + 61*X^17 + 37*X^16 + 43*X^15 + 61*X^14 +
      9*X^13 + 59*X^12 + 49*X^11 + 25*X^10 + 47*X^9 + 41*X^8 + 65*X^7 + 53*X^6 + 64*X^5 + 39*X^4 +
      28*X^3 + 61*X^2 + 34*X + 38) :=
  sq_step (by norm_num) pSeventeenB4s251 ⟨
    36*X^32 + 24*X^31 + 6*X^30 + 59*X^29 + 36*X^28 + 28*X^27 + 42*X^26 + 15*X^25 + 9*X^24 + 36*X^23 +
      43*X^22 + 23*X^21 + 42*X^20 + 35*X^19 + 63*X^18 + 3*X^17 + 25*X^16 + 32*X^15 + X^14 + 26*X^13 +
      13*X^12 + 34*X^11 + 15*X^10 + 3*X^9 + 24*X^8 + 24*X^7 + 53*X^6 + 32*X^5 + 42*X^4 + 55*X^3 +
      3*X^2 + 45*X + 56,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s253 : XPow fSeventeenB4 444020944803615844652592563120685448998174421437156
    (35*X^33 + 8*X^32 + X^31 + 4*X^30 + 19*X^29 + 15*X^28 + 59*X^27 + 27*X^26 + 4*X^25 + 8*X^24 + 24*X^23 +
      28*X^22 + 38*X^21 + 33*X^20 + 18*X^19 + 9*X^18 + 33*X^17 + 62*X^16 + 18*X^15 + 5*X^14 +
      43*X^13 + 18*X^12 + 48*X^11 + 4*X^10 + 26*X^9 + 64*X^8 + 21*X^7 + 6*X^6 + 63*X^5 + 7*X^4 +
      12*X^3 + 10*X^2 + 30*X + 65) :=
  sq_step (by norm_num) pSeventeenB4s252 ⟨
    49*X^32 + 25*X^31 + 10*X^30 + 65*X^29 + 42*X^28 + 64*X^27 + 18*X^26 + 40*X^25 + 56*X^24 + 13*X^23 +
      64*X^22 + 56*X^21 + 52*X^20 + 9*X^19 + 4*X^18 + 61*X^17 + 8*X^16 + 6*X^15 + 15*X^14 + 7*X^13 +
      X^12 + 6*X^11 + 9*X^10 + 66*X^9 + 63*X^8 + 40*X^7 + 64*X^6 + 38*X^5 + 7*X^3 + 59*X^2 + 37*X +
      3,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s254 : XPow fSeventeenB4 444020944803615844652592563120685448998174421437157
    (11*X^33 + 61*X^32 + 21*X^31 + 54*X^30 + 24*X^29 + 4*X^28 + 20*X^27 + 37*X^26 + 50*X^25 + 33*X^24 +
      7*X^23 + 3*X^22 + 21*X^21 + 40*X^20 + 33*X^19 + 45*X^18 + 35*X^17 + 66*X^16 + 6*X^15 + 4*X^14 +
      56*X^13 + 61*X^12 + 41*X^11 + 64*X^10 + 20*X^9 + 28*X^8 + 8*X^7 + 39*X^6 + 17*X^5 + 11*X^4 +
      4*X^3 + 55*X^2 + 14) :=
  mul_step (by norm_num) pSeventeenB4s253 pSeventeenB41 ⟨
    35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s255 : XPow fSeventeenB4 888041889607231689305185126241370897996348842874314
    (15*X^33 + 54*X^32 + 44*X^31 + 58*X^30 + 32*X^29 + 58*X^27 + 13*X^26 + 9*X^25 + 39*X^24 + 66*X^23 +
      45*X^22 + 29*X^21 + 18*X^20 + 66*X^19 + 20*X^18 + 58*X^17 + 60*X^16 + 47*X^15 + 51*X^14 +
      46*X^13 + 43*X^12 + 19*X^11 + 3*X^10 + 9*X^9 + 3*X^8 + 24*X^7 + 45*X^6 + 61*X^5 + 2*X^4 +
      18*X^3 + 20*X^2 + 6*X + 35) :=
  sq_step (by norm_num) pSeventeenB4s254 ⟨
    54*X^32 + 43*X^31 + 64*X^30 + 46*X^29 + 8*X^28 + 36*X^27 + 65*X^26 + 45*X^25 + 60*X^24 + 54*X^23 +
      28*X^22 + 8*X^21 + 14*X^20 + X^19 + 33*X^18 + 46*X^17 + 41*X^16 + 2*X^15 + 24*X^14 + 21*X^13 +
      29*X^12 + 40*X^11 + 42*X^10 + 45*X^9 + 21*X^8 + 46*X^7 + 45*X^6 + 40*X^5 + 52*X^4 + 51*X^3 +
      55*X^2 + 39*X + 33,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s256 : XPow fSeventeenB4 888041889607231689305185126241370897996348842874315
    (17*X^33 + 41*X^32 + 27*X^31 + 47*X^30 + 23*X^29 + 44*X^28 + 10*X^27 + 4*X^26 + 57*X^25 + 22*X^24 +
      36*X^23 + 14*X^22 + 32*X^21 + 18*X^20 + 59*X^19 + 44*X^18 + 58*X^17 + 58*X^16 + 61*X^15 +
      58*X^14 + 21*X^13 + 15*X^12 + 38*X^11 + 54*X^10 + 32*X^9 + 27*X^8 + 65*X^7 + 22*X^6 + 35*X^5 +
      8*X^4 + 27*X^3 + 55*X^2 + 55*X + 6) :=
  mul_step (by norm_num) pSeventeenB4s255 pSeventeenB41 ⟨
    15,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s257 : XPow fSeventeenB4 1776083779214463378610370252482741795992697685748630
    (66*X^33 + 11*X^32 + 17*X^31 + 21*X^30 + 29*X^29 + 40*X^28 + 61*X^27 + 59*X^26 + 35*X^25 + 22*X^24 +
      49*X^23 + 8*X^22 + 35*X^21 + 19*X^20 + 45*X^19 + 28*X^18 + 36*X^17 + 6*X^16 + 44*X^15 +
      27*X^14 + 18*X^13 + 59*X^12 + 40*X^11 + 24*X^9 + 54*X^8 + 58*X^7 + 5*X^6 + 14*X^5 + 6*X^4 +
      32*X^3 + 53*X^2 + 19*X + 48) :=
  sq_step (by norm_num) pSeventeenB4s256 ⟨
    21*X^32 + 29*X^31 + 13*X^30 + 10*X^29 + 46*X^28 + 59*X^27 + 21*X^26 + 41*X^25 + 62*X^24 + 35*X^23 +
      11*X^22 + 48*X^21 + 53*X^20 + 2*X^19 + 53*X^18 + 28*X^17 + 36*X^16 + 59*X^15 + 22*X^14 +
      22*X^13 + 2*X^12 + 22*X^11 + 42*X^10 + 33*X^9 + 10*X^8 + 28*X^7 + 5*X^6 + 30*X^5 + 15*X^4 +
      2*X^3 + 35*X^2 + 6*X + 30,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s258 : XPow fSeventeenB4 1776083779214463378610370252482741795992697685748631
    (9*X^33 + 44*X^32 + 32*X^31 + 28*X^30 + 34*X^29 + 53*X^28 + 19*X^27 + 13*X^26 + 61*X^25 + 43*X^24 +
      22*X^23 + 36*X^22 + 27*X^21 + 8*X^20 + 12*X^19 + 28*X^18 + 24*X^17 + 12*X^16 + 4*X^15 +
      44*X^14 + 56*X^13 + 9*X^12 + 20*X^11 + 21*X^10 + 61*X^9 + 31*X^8 + 26*X^7 + 30*X^6 + 44*X^5 +
      55*X^4 + 57*X^3 + 47*X^2 + 2*X + 13) :=
  mul_step (by norm_num) pSeventeenB4s257 pSeventeenB41 ⟨
    66,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s259 : XPow fSeventeenB4 3552167558428926757220740504965483591985395371497262
    (35*X^33 + 63*X^32 + 16*X^31 + 23*X^30 + 64*X^29 + 52*X^28 + 51*X^27 + 24*X^26 + 8*X^25 + 55*X^24 +
      6*X^23 + 46*X^22 + 39*X^21 + 55*X^20 + 26*X^19 + 13*X^18 + 6*X^17 + 64*X^16 + 46*X^15 +
      38*X^14 + 18*X^13 + 29*X^12 + 16*X^11 + 53*X^10 + 23*X^9 + 48*X^8 + 31*X^7 + 20*X^6 + 20*X^5 +
      62*X^4 + 65*X^3 + 65*X^2 + 49*X + 23) :=
  sq_step (by norm_num) pSeventeenB4s258 ⟨
    14*X^32 + 16*X^31 + 22*X^30 + 31*X^29 + 56*X^28 + 47*X^27 + 5*X^26 + 14*X^25 + 16*X^24 + 29*X^23 +
      33*X^22 + 9*X^21 + 32*X^20 + 30*X^19 + 19*X^18 + 34*X^17 + 16*X^16 + 61*X^15 + X^14 + 19*X^13 +
      42*X^12 + 9*X^11 + 6*X^10 + 66*X^9 + 51*X^8 + 53*X^7 + 66*X^6 + 40*X^5 + 52*X^4 + 37*X^3 +
      38*X^2 + 59*X + 37,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s260 : XPow fSeventeenB4 3552167558428926757220740504965483591985395371497263
    (66*X^33 + 9*X^32 + 40*X^31 + 32*X^30 + 61*X^29 + 63*X^28 + 17*X^27 + 41*X^26 + 30*X^25 + 15*X^24 +
      25*X^23 + 4*X^22 + 43*X^21 + 48*X^20 + 37*X^19 + 18*X^18 + 37*X^17 + 27*X^16 + 39*X^15 +
      46*X^14 + 29*X^12 + 23*X^11 + 61*X^10 + 4*X^9 + 38*X^8 + 22*X^7 + 63*X^6 + 5*X^5 + 64*X^4 +
      59*X^3 + 7*X^2 + 25*X + 14) :=
  mul_step (by norm_num) pSeventeenB4s259 pSeventeenB41 ⟨
    35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s261 : XPow fSeventeenB4 7104335116857853514441481009930967183970790742994526
    (10*X^33 + 15*X^32 + 41*X^31 + X^30 + 6*X^29 + 39*X^28 + 2*X^27 + 4*X^26 + 34*X^25 + 61*X^24 +
      35*X^23 + 33*X^22 + 27*X^21 + 50*X^20 + 37*X^19 + 49*X^18 + 25*X^17 + 27*X^15 + 33*X^14 +
      24*X^13 + 42*X^12 + 7*X^11 + 7*X^10 + 25*X^9 + 51*X^8 + 22*X^7 + 46*X^6 + 42*X^5 + 32*X^4 +
      3*X^3 + 33*X^2 + 24*X + 19) :=
  sq_step (by norm_num) pSeventeenB4s260 ⟨
    X^32 + 51*X^31 + 9*X^30 + 23*X^29 + 24*X^28 + 36*X^27 + 66*X^26 + 13*X^25 + 19*X^24 + 66*X^23 +
      54*X^22 + 6*X^21 + 3*X^20 + 61*X^19 + 51*X^18 + 4*X^17 + 18*X^16 + 16*X^15 + 61*X^14 + 65*X^13 +
      54*X^12 + 19*X^11 + 40*X^10 + 28*X^9 + 37*X^8 + 46*X^7 + 60*X^6 + 3*X^5 + 64*X^4 + 13*X^3 +
      21*X^2 + 53*X + 60,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s262 : XPow fSeventeenB4 7104335116857853514441481009930967183970790742994527
    (35*X^33 + 39*X^32 + 25*X^31 + 16*X^30 + 32*X^29 + 15*X^28 + 2*X^27 + 53*X^26 + 6*X^25 + 28*X^24 +
      27*X^23 + 17*X^22 + 37*X^21 + 5*X^20 + 8*X^19 + 38*X^18 + 21*X^17 + 12*X^16 + 62*X^15 +
      32*X^14 + 5*X^13 + 49*X^12 + 8*X^11 + 55*X^10 + 48*X^9 + 24*X^8 + 37*X^7 + 16*X^6 + 54*X^5 +
      41*X^4 + 60*X^3 + 12*X^2 + 10*X + 4) :=
  mul_step (by norm_num) pSeventeenB4s261 pSeventeenB41 ⟨
    10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s263 : XPow fSeventeenB4 14208670233715707028882962019861934367941581485989054
    (39*X^33 + 11*X^32 + 34*X^31 + 21*X^30 + 39*X^29 + 61*X^28 + 34*X^27 + 20*X^26 + 19*X^25 + 11*X^24 +
      61*X^23 + 10*X^21 + 14*X^20 + 62*X^19 + 34*X^18 + 30*X^17 + 17*X^16 + 39*X^15 + 21*X^14 +
      49*X^13 + 33*X^12 + 44*X^11 + 15*X^10 + 64*X^9 + 5*X^8 + 8*X^7 + 13*X^6 + 60*X^5 + 17*X^4 +
      17*X^3 + 31*X^2 + 61*X + 54) :=
  sq_step (by norm_num) pSeventeenB4s262 ⟨
    19*X^32 + 21*X^31 + 53*X^30 + 55*X^29 + 34*X^28 + 2*X^27 + 35*X^26 + 17*X^25 + 35*X^24 + 43*X^23 +
      49*X^22 + 61*X^21 + 10*X^20 + 66*X^19 + 29*X^18 + 9*X^17 + 41*X^16 + 54*X^15 + 14*X^14 +
      10*X^13 + 40*X^12 + 55*X^11 + 2*X^10 + 35*X^9 + 14*X^8 + 49*X^7 + 51*X^6 + 50*X^5 + 38*X^4 +
      33*X^2 + 49*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s264 : XPow fSeventeenB4 14208670233715707028882962019861934367941581485989055
    (22*X^33 + 53*X^32 + 61*X^31 + 11*X^30 + 27*X^29 + 11*X^28 + 39*X^27 + 6*X^26 + 31*X^25 + 27*X^24 +
      57*X^23 + 38*X^22 + 37*X^21 + 31*X^20 + 55*X^19 + 7*X^18 + 52*X^17 + 14*X^16 + 47*X^15 +
      40*X^14 + 16*X^13 + 47*X^12 + 39*X^11 + 47*X^10 + 56*X^8 + 65*X^7 + 39*X^6 + 9*X^5 + 58*X^4 +
      9*X^3 + 41*X^2 + 39*X + 29) :=
  mul_step (by norm_num) pSeventeenB4s263 pSeventeenB41 ⟨
    39,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s265 : XPow fSeventeenB4 28417340467431414057765924039723868735883162971978110
    (53*X^33 + 39*X^32 + 7*X^31 + 49*X^30 + 41*X^29 + X^28 + 49*X^27 + 40*X^26 + 46*X^25 + 36*X^24 +
      45*X^23 + 9*X^22 + 32*X^21 + 9*X^20 + 66*X^19 + 25*X^18 + 48*X^17 + 10*X^16 + 36*X^15 +
      49*X^14 + 28*X^13 + 45*X^12 + 53*X^11 + 6*X^10 + 51*X^9 + 55*X^8 + 30*X^7 + 20*X^6 + 13*X^5 +
      12*X^4 + 64*X^3 + 4*X^2 + 13*X + 51) :=
  sq_step (by norm_num) pSeventeenB4s264 ⟨
    15*X^32 + 17*X^31 + 30*X^30 + 21*X^29 + 43*X^28 + 31*X^27 + 60*X^26 + 51*X^25 + 53*X^24 + 9*X^23 +
      66*X^22 + 6*X^21 + 45*X^20 + 22*X^19 + 32*X^18 + 43*X^17 + 34*X^16 + 3*X^15 + 41*X^14 +
      41*X^13 + 30*X^12 + 20*X^11 + 53*X^10 + 39*X^9 + 40*X^8 + 13*X^7 + 50*X^6 + 24*X^5 + 12*X^4 +
      28*X^3 + 25*X^2 + 34*X + 35,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s266 : XPow fSeventeenB4 56834680934862828115531848079447737471766325943956220
    (62*X^33 + 60*X^32 + 38*X^31 + 47*X^30 + 27*X^29 + 33*X^28 + 46*X^27 + 17*X^26 + 57*X^25 + 19*X^24 +
      63*X^23 + 8*X^22 + 7*X^21 + 19*X^20 + 7*X^19 + 29*X^18 + 31*X^17 + 51*X^16 + 36*X^15 + 52*X^14 +
      26*X^13 + 23*X^12 + 5*X^11 + 3*X^10 + 40*X^9 + 57*X^8 + 11*X^7 + 60*X^6 + 51*X^5 + 56*X^4 +
      23*X^3 + 47*X^2 + 42*X + 26) :=
  sq_step (by norm_num) pSeventeenB4s265 ⟨
    62*X^32 + 37*X^31 + 60*X^30 + 25*X^29 + 4*X^28 + 57*X^27 + 46*X^26 + 29*X^25 + X^24 + 42*X^23 +
      14*X^22 + 38*X^21 + 47*X^20 + 47*X^19 + 45*X^18 + 57*X^17 + 34*X^16 + 66*X^15 + 48*X^14 +
      27*X^13 + 11*X^12 + 22*X^11 + 57*X^10 + 53*X^9 + 26*X^8 + 6*X^7 + 28*X^6 + 11*X^5 + 32*X^4 +
      X^3 + 3*X^2 + 2*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s267 : XPow fSeventeenB4 113669361869725656231063696158895474943532651887912440
    (28*X^33 + 11*X^32 + 37*X^30 + 18*X^29 + 24*X^28 + 25*X^27 + 64*X^26 + 40*X^25 + 5*X^24 + 47*X^23 +
      27*X^22 + 28*X^21 + 54*X^20 + X^19 + 26*X^18 + 47*X^17 + 37*X^16 + 44*X^15 + 22*X^14 + 41*X^13 +
      58*X^12 + 58*X^11 + 45*X^10 + 21*X^9 + 51*X^8 + 55*X^7 + 57*X^6 + 28*X^5 + 60*X^4 + 14*X^3 +
      2*X^2 + 3*X + 6) :=
  sq_step (by norm_num) pSeventeenB4s266 ⟨
    25*X^32 + 53*X^31 + 38*X^30 + 48*X^29 + 33*X^28 + 12*X^27 + 21*X^26 + 61*X^25 + 58*X^24 + 52*X^23 +
      32*X^22 + 50*X^21 + 39*X^20 + 56*X^19 + 13*X^18 + 63*X^17 + 51*X^16 + 66*X^15 + 6*X^14 +
      29*X^13 + 56*X^12 + 26*X^11 + 49*X^10 + 56*X^9 + 44*X^8 + 10*X^7 + 7*X^6 + 28*X^5 + 10*X^4 +
      12*X^3 + 22*X^2 + 8*X,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s268 : XPow fSeventeenB4 227338723739451312462127392317790949887065303775824880
    (58*X^33 + 59*X^32 + 40*X^31 + 29*X^30 + 46*X^29 + 41*X^28 + 61*X^26 + 5*X^25 + 19*X^24 + 12*X^23 +
      41*X^22 + 2*X^21 + 32*X^20 + 21*X^19 + 16*X^18 + 31*X^17 + 61*X^16 + 2*X^15 + 23*X^14 +
      40*X^13 + 26*X^12 + 58*X^11 + 5*X^10 + 38*X^9 + 59*X^8 + 13*X^7 + 24*X^6 + 18*X^5 + 15*X^4 +
      15*X^3 + 35*X^2 + 66*X + 2) :=
  sq_step (by norm_num) pSeventeenB4s267 ⟨
    47*X^32 + 40*X^31 + 4*X^30 + 14*X^29 + 9*X^28 + 50*X^27 + 2*X^26 + 28*X^25 + 53*X^24 + 12*X^23 +
      15*X^22 + 24*X^21 + 44*X^20 + 25*X^19 + 12*X^18 + 27*X^17 + 26*X^16 + 47*X^15 + 44*X^14 +
      27*X^13 + 3*X^12 + 39*X^11 + 17*X^10 + 3*X^9 + 21*X^8 + X^7 + 60*X^6 + 47*X^5 + 64*X^4 +
      13*X^3 + 37*X^2 + X + 49,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s269 : XPow fSeventeenB4 454677447478902624924254784635581899774130607551649760
    (54*X^33 + 23*X^32 + 63*X^31 + 32*X^30 + 17*X^29 + 3*X^28 + 66*X^27 + 6*X^26 + 32*X^25 + 34*X^24 +
      12*X^23 + 33*X^22 + 48*X^21 + 10*X^20 + 7*X^19 + 34*X^18 + 11*X^17 + 40*X^16 + 31*X^15 +
      2*X^14 + 28*X^13 + 37*X^12 + 49*X^11 + 36*X^10 + 26*X^9 + 39*X^8 + 35*X^7 + 32*X^6 + 30*X^5 +
      14*X^4 + 34*X^3 + 29*X^2 + 14*X + 31) :=
  sq_step (by norm_num) pSeventeenB4s268 ⟨
    14*X^32 + 38*X^31 + 47*X^30 + 30*X^29 + 35*X^28 + 46*X^27 + 54*X^26 + 18*X^25 + 33*X^24 + 33*X^23 +
      28*X^22 + 32*X^21 + 22*X^20 + 56*X^19 + 53*X^18 + 20*X^17 + 66*X^16 + 52*X^15 + 18*X^14 +
      6*X^13 + 37*X^12 + 5*X^11 + 54*X^10 + 61*X^9 + 15*X^8 + 48*X^7 + 29*X^6 + 18*X^5 + 43*X^4 +
      22*X^3 + 20*X^2 + 21*X + 34,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s270 : XPow fSeventeenB4 909354894957805249848509569271163799548261215103299520
    (66*X^33 + 2*X^32 + 50*X^31 + 59*X^30 + 3*X^29 + 48*X^28 + 44*X^27 + 33*X^26 + 61*X^25 + 40*X^24 +
      52*X^23 + 39*X^22 + 37*X^21 + 56*X^20 + 45*X^19 + 39*X^18 + 18*X^17 + 57*X^16 + 9*X^15 +
      55*X^14 + 4*X^13 + 33*X^12 + 30*X^11 + 25*X^10 + 29*X^9 + 29*X^8 + 3*X^7 + 60*X^6 + 22*X^5 +
      34*X^4 + 38*X^3 + 61*X^2 + 16*X + 59) :=
  sq_step (by norm_num) pSeventeenB4s269 ⟨
    35*X^32 + 8*X^31 + 39*X^30 + 2*X^29 + 11*X^28 + 4*X^27 + 36*X^26 + 60*X^25 + 60*X^24 + 10*X^23 +
      12*X^22 + 60*X^21 + 59*X^20 + 65*X^19 + 59*X^18 + 38*X^17 + 57*X^16 + 51*X^15 + 56*X^14 +
      2*X^13 + 48*X^12 + 35*X^11 + 36*X^10 + 55*X^9 + 57*X^8 + 36*X^7 + 58*X^6 + X^5 + 26*X^4 +
      51*X^3 + 20*X^2 + 49*X + 23,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s271 : XPow fSeventeenB4 1818709789915610499697019138542327599096522430206599040
    (65*X^33 + 28*X^32 + 52*X^31 + 53*X^30 + 29*X^29 + 54*X^28 + 17*X^27 + 58*X^26 + 50*X^25 + 51*X^24 +
      20*X^23 + 51*X^22 + 66*X^21 + 45*X^20 + 61*X^19 + 4*X^18 + 56*X^17 + 47*X^16 + 46*X^15 +
      2*X^14 + 56*X^13 + 31*X^12 + 21*X^11 + 20*X^10 + 23*X^9 + 28*X^8 + 3*X^7 + 3*X^6 + 50*X^5 +
      45*X^4 + 53*X^3 + 13*X^2 + 50*X + 63) :=
  sq_step (by norm_num) pSeventeenB4s270 ⟨
    X^32 + 65*X^31 + 7*X^30 + 5*X^29 + 28*X^28 + 36*X^27 + 35*X^25 + 31*X^24 + 60*X^23 + 66*X^22 +
      33*X^21 + 58*X^20 + 35*X^19 + 44*X^18 + 50*X^17 + 22*X^16 + 22*X^15 + 64*X^14 + 9*X^13 +
      20*X^12 + 23*X^11 + 48*X^10 + 9*X^9 + 8*X^8 + 8*X^7 + 8*X^6 + 37*X^5 + 5*X^4 + 37*X^3 + 14*X^2 +
      14*X + 31,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s272 : XPow fSeventeenB4 3637419579831220999394038277084655198193044860413198080
    (16*X^33 + 16*X^32 + 18*X^31 + 33*X^30 + 2*X^29 + 5*X^28 + 44*X^27 + 38*X^26 + 62*X^25 + 37*X^24 +
      18*X^23 + 65*X^22 + 21*X^21 + 56*X^20 + 16*X^19 + 2*X^18 + 15*X^17 + 64*X^16 + 22*X^15 +
      8*X^14 + 24*X^13 + 58*X^12 + 63*X^11 + 60*X^10 + 66*X^9 + 55*X^8 + 54*X^7 + 2*X^6 + 12*X^5 +
      4*X^4 + 43*X^3 + 59*X^2 + 40*X + 23) :=
  sq_step (by norm_num) pSeventeenB4s271 ⟨
    4*X^32 + 30*X^31 + 59*X^30 + 21*X^29 + 61*X^28 + 51*X^27 + 40*X^26 + 43*X^25 + 48*X^24 + 29*X^23 +
      51*X^22 + 43*X^21 + 2*X^20 + 29*X^19 + 16*X^18 + 31*X^17 + 30*X^16 + 59*X^15 + X^14 + 60*X^13 +
      18*X^12 + 50*X^11 + 4*X^10 + 37*X^9 + 65*X^8 + 53*X^7 + 16*X^6 + 25*X^5 + 63*X^4 + 42*X^3 +
      21*X^2 + 59*X + 51,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s273 : XPow fSeventeenB4 3637419579831220999394038277084655198193044860413198081
    (48*X^33 + 55*X^32 + 58*X^31 + 18*X^30 + 34*X^29 + 38*X^28 + 8*X^27 + 12*X^26 + 16*X^25 + 47*X^24 +
      42*X^23 + 5*X^22 + 62*X^21 + 5*X^20 + 57*X^19 + 9*X^18 + 44*X^17 + 65*X^16 + 41*X^15 + 10*X^14 +
      39*X^13 + 23*X^12 + 8*X^11 + 47*X^10 + 10*X^9 + 17*X^8 + X^7 + 24*X^6 + 66*X^5 + 10*X^4 +
      62*X^3 + 61*X^2 + 22*X + 60) :=
  mul_step (by norm_num) pSeventeenB4s272 pSeventeenB41 ⟨
    16,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s274 : XPow fSeventeenB4 7274839159662441998788076554169310396386089720826396162
    (42*X^33 + 39*X^32 + 33*X^31 + 19*X^30 + 17*X^29 + 9*X^28 + 10*X^27 + 51*X^26 + 61*X^25 + 41*X^24 +
      41*X^23 + 22*X^22 + 56*X^21 + 24*X^20 + 45*X^19 + 46*X^18 + 2*X^17 + 17*X^16 + 60*X^15 +
      11*X^14 + 28*X^13 + 24*X^12 + 25*X^11 + 39*X^10 + 25*X^9 + 29*X^8 + 7*X^7 + 40*X^6 + 26*X^5 +
      16*X^4 + 23*X^3 + 55*X^2 + 58*X + 11) :=
  sq_step (by norm_num) pSeventeenB4s273 ⟨
    26*X^32 + 39*X^31 + 63*X^30 + 61*X^29 + 60*X^28 + 14*X^27 + 21*X^26 + 17*X^25 + 40*X^24 + 20*X^23 +
      21*X^22 + 26*X^21 + 9*X^20 + 65*X^19 + 2*X^18 + 29*X^17 + 35*X^15 + 55*X^14 + 38*X^13 +
      20*X^12 + 38*X^11 + 64*X^10 + 5*X^9 + 15*X^8 + 17*X^7 + 39*X^6 + 5*X^5 + 25*X^4 + 12*X^3 +
      48*X^2 + 48*X + 39,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s275 : XPow fSeventeenB4 14549678319324883997576153108338620792772179441652792324
    (31*X^33 + 62*X^32 + 8*X^31 + 50*X^30 + 2*X^29 + 35*X^28 + 14*X^27 + 39*X^26 + 47*X^25 + 17*X^24 +
      52*X^23 + 10*X^22 + 19*X^21 + 20*X^20 + 20*X^19 + 54*X^18 + 18*X^17 + 35*X^16 + 7*X^15 +
      19*X^14 + 37*X^13 + 24*X^12 + 5*X^11 + 59*X^10 + 27*X^9 + 5*X^8 + 28*X^7 + 4*X^6 + 25*X^5 +
      59*X^4 + 59*X^3 + 25*X^2 + 38*X + 58) :=
  sq_step (by norm_num) pSeventeenB4s274 ⟨
    22*X^32 + 37*X^31 + 21*X^30 + 23*X^29 + 11*X^28 + 62*X^27 + 3*X^26 + 11*X^25 + 7*X^24 + 48*X^23 +
      14*X^22 + 16*X^21 + 5*X^20 + 62*X^19 + 31*X^18 + 15*X^17 + 33*X^16 + 58*X^15 + 42*X^14 +
      5*X^13 + 11*X^12 + 8*X^11 + 54*X^10 + 33*X^9 + 56*X^8 + 47*X^7 + 36*X^6 + 30*X^5 + 49*X^4 +
      56*X^3 + 27*X^2 + 43*X + 10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s276 : XPow fSeventeenB4 29099356638649767995152306216677241585544358883305584648
    (9*X^33 + 9*X^32 + 17*X^31 + 65*X^30 + 66*X^29 + 41*X^28 + 61*X^27 + 49*X^26 + 41*X^25 + 7*X^24 +
      6*X^23 + 25*X^22 + 10*X^21 + 63*X^20 + 19*X^19 + X^18 + 26*X^17 + 25*X^16 + 44*X^15 + 49*X^14 +
      32*X^13 + 5*X^12 + 57*X^11 + 18*X^10 + 63*X^9 + 18*X^7 + 10*X^6 + 64*X^5 + 45*X^4 + 10*X^3 +
      44*X^2 + 23*X + 59) :=
  sq_step (by norm_num) pSeventeenB4s275 ⟨
    23*X^32 + 4*X^31 + 42*X^30 + 63*X^29 + 66*X^28 + 56*X^27 + 66*X^26 + 55*X^25 + 50*X^24 + 52*X^23 +
      35*X^22 + 10*X^21 + 39*X^20 + 49*X^19 + 47*X^18 + 5*X^17 + 11*X^16 + 32*X^15 + 31*X^14 +
      38*X^13 + 42*X^12 + 61*X^11 + 62*X^10 + 5*X^9 + 2*X^8 + 55*X^7 + 59*X^6 + 49*X^5 + 56*X^4 +
      55*X^3 + 32*X^2 + 19*X + 12,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s277 : XPow fSeventeenB4 29099356638649767995152306216677241585544358883305584649
    (27*X^33 + 42*X^32 + 33*X^31 + 8*X^30 + 28*X^29 + 66*X^28 + 7*X^27 + 38*X^26 + 58*X^25 + 60*X^24 +
      33*X^23 + X^22 + 58*X^21 + 17*X^20 + 11*X^19 + 31*X^18 + 64*X^17 + 64*X^16 + 55*X^15 + 66*X^14 +
      32*X^13 + X^12 + 39*X^11 + 23*X^10 + 4*X^9 + 60*X^8 + 22*X^7 + 54*X^6 + 38*X^5 + 4*X^4 + 8*X^3 +
      39*X^2 + 4*X + 17) :=
  mul_step (by norm_num) pSeventeenB4s276 pSeventeenB41 ⟨
    9,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s278 : XPow fSeventeenB4 58198713277299535990304612433354483171088717766611169298
    (37*X^33 + 63*X^32 + 10*X^31 + 39*X^30 + 26*X^29 + 43*X^28 + 9*X^27 + 37*X^26 + 12*X^25 + 61*X^24 +
      39*X^23 + 30*X^22 + 25*X^21 + 44*X^20 + 64*X^19 + 61*X^18 + 15*X^17 + 33*X^16 + 22*X^15 +
      33*X^14 + 56*X^13 + 22*X^12 + 56*X^11 + 44*X^10 + 46*X^9 + 26*X^8 + 56*X^7 + 63*X^6 + 13*X^5 +
      31*X^4 + 35*X^3 + 39*X^2 + 5*X + 9) :=
  sq_step (by norm_num) pSeventeenB4s277 ⟨
    59*X^32 + 41*X^31 + 25*X^30 + 24*X^29 + 43*X^28 + 39*X^27 + 61*X^26 + 58*X^25 + 8*X^24 + 36*X^23 +
      48*X^22 + 42*X^21 + 49*X^20 + 63*X^19 + 17*X^18 + 4*X^17 + 61*X^16 + 38*X^15 + 21*X^13 +
      6*X^12 + 11*X^11 + 36*X^10 + 45*X^9 + 55*X^8 + 32*X^7 + 60*X^6 + 21*X^5 + 37*X^4 + 52*X^3 +
      35*X^2 + 7*X + 37,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s279 : XPow fSeventeenB4 116397426554599071980609224866708966342177435533222338596
    (37*X^33 + 25*X^32 + 12*X^31 + 3*X^29 + 34*X^28 + 15*X^27 + 6*X^26 + 2*X^25 + 33*X^24 + 21*X^23 +
      30*X^22 + 62*X^21 + 17*X^20 + 59*X^19 + 48*X^18 + 27*X^17 + 66*X^16 + 2*X^15 + 45*X^14 +
      34*X^13 + 37*X^12 + 37*X^11 + 6*X^10 + 65*X^9 + 4*X^8 + 57*X^7 + 46*X^6 + 51*X^5 + 21*X^4 +
      54*X^3 + 40*X^2 + 28*X + 36) :=
  sq_step (by norm_num) pSeventeenB4s278 ⟨
    29*X^32 + 30*X^31 + 33*X^30 + X^29 + 53*X^28 + 56*X^27 + 4*X^26 + 41*X^25 + 23*X^24 + 48*X^23 +
      29*X^22 + 48*X^21 + 38*X^20 + 38*X^19 + 9*X^18 + 4*X^17 + 3*X^16 + 59*X^15 + 37*X^14 + 10*X^13 +
      6*X^12 + 63*X^11 + 51*X^10 + 56*X^9 + 54*X^8 + 61*X^7 + 28*X^6 + 17*X^5 + 50*X^4 + 42*X^3 +
      48*X^2 + 19*X + 55,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s280 : XPow fSeventeenB4 116397426554599071980609224866708966342177435533222338597
    (32*X^33 + 18*X^32 + 62*X^31 + 40*X^30 + 55*X^29 + 43*X^28 + 12*X^27 + 12*X^26 + 64*X^25 + 42*X^24 +
      48*X^23 + 25*X^22 + 56*X^21 + 21*X^20 + 37*X^19 + 55*X^18 + 3*X^17 + 47*X^16 + 25*X^15 +
      10*X^14 + 14*X^13 + 45*X^12 + 3*X^11 + 42*X^10 + 13*X^9 + 51*X^8 + 6*X^7 + 62*X^6 + 22*X^5 +
      7*X^4 + 26*X^3 + 64*X^2 + 63*X + 55) :=
  mul_step (by norm_num) pSeventeenB4s279 pSeventeenB41 ⟨
    37,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s281 : XPow fSeventeenB4 232794853109198143961218449733417932684354871066444677194
    (3*X^33 + 66*X^32 + 29*X^31 + 22*X^30 + 31*X^29 + 3*X^28 + 13*X^27 + 35*X^26 + 34*X^25 + 59*X^24 +
      27*X^23 + 31*X^22 + 3*X^21 + 18*X^20 + 50*X^19 + 19*X^18 + 59*X^17 + 65*X^16 + 22*X^15 +
      10*X^14 + 30*X^13 + 8*X^12 + 40*X^11 + 49*X^10 + 45*X^9 + 37*X^8 + 24*X^7 + X^6 + 18*X^5 +
      44*X^4 + 39*X^3 + 33*X^2 + 15*X + 42) :=
  sq_step (by norm_num) pSeventeenB4s280 ⟨
    19*X^32 + 51*X^31 + 62*X^30 + 47*X^29 + 49*X^28 + 31*X^27 + 31*X^26 + 16*X^25 + 14*X^24 + 46*X^23 +
      8*X^22 + 16*X^21 + 29*X^20 + 32*X^19 + 13*X^18 + 44*X^17 + 27*X^16 + 18*X^15 + 18*X^14 +
      12*X^13 + 66*X^12 + 31*X^11 + 8*X^10 + 25*X^9 + 31*X^8 + 34*X^7 + 54*X^6 + 64*X^5 + 14*X^4 +
      41*X^3 + 10*X^2 + 11*X + 13,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s282 : XPow fSeventeenB4 465589706218396287922436899466835865368709742132889354388
    (62*X^33 + 60*X^32 + 55*X^31 + 24*X^30 + 20*X^29 + 44*X^28 + 35*X^27 + 14*X^26 + 29*X^25 + 2*X^24 +
      51*X^23 + 58*X^22 + 26*X^21 + 48*X^20 + 4*X^19 + 39*X^18 + 19*X^17 + 26*X^16 + 4*X^15 +
      26*X^14 + 13*X^13 + 61*X^12 + 51*X^11 + 43*X^10 + 22*X^9 + 24*X^8 + 28*X^7 + 15*X^6 + 50*X^5 +
      31*X^4 + 27*X^3 + 51*X^2 + 52*X + 44) :=
  sq_step (by norm_num) pSeventeenB4s281 ⟨
    9*X^32 + 12*X^31 + 23*X^30 + 32*X^29 + 35*X^28 + 50*X^27 + 51*X^26 + 45*X^25 + 27*X^24 + 21*X^23 +
      33*X^22 + 29*X^21 + 24*X^20 + 22*X^19 + 41*X^18 + 35*X^17 + 12*X^16 + 24*X^15 + 64*X^14 +
      6*X^13 + 2*X^12 + 45*X^11 + 36*X^10 + 20*X^9 + 17*X^8 + 8*X^7 + 42*X^6 + 25*X^5 + 19*X^4 +
      60*X^3 + 31*X^2 + 35*X + 55,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s283 : XPow fSeventeenB4 465589706218396287922436899466835865368709742132889354389
    (50*X^33 + 56*X^32 + 12*X^31 + 15*X^30 + 14*X^29 + 62*X^28 + 15*X^27 + 53*X^26 + 63*X^25 + 21*X^24 +
      61*X^23 + 31*X^22 + 21*X^21 + 20*X^20 + 26*X^19 + 46*X^18 + 49*X^17 + 45*X^16 + 45*X^15 +
      9*X^14 + 46*X^13 + 30*X^12 + 9*X^11 + 7*X^10 + 59*X^9 + 27*X^8 + 53*X^7 + 63*X^6 + 20*X^5 +
      8*X^4 + 4*X^3 + 58*X^2 + 15*X + 65) :=
  mul_step (by norm_num) pSeventeenB4s282 pSeventeenB41 ⟨
    62,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s284 : XPow fSeventeenB4 931179412436792575844873798933671730737419484265778708778
    (65*X^33 + 11*X^32 + 62*X^31 + 34*X^30 + 65*X^29 + 5*X^28 + 43*X^27 + 37*X^26 + 3*X^25 + 49*X^24 +
      8*X^23 + 34*X^22 + 19*X^21 + 27*X^20 + 61*X^19 + 33*X^18 + 61*X^17 + 24*X^16 + 2*X^15 +
      55*X^14 + 35*X^13 + 15*X^12 + 36*X^11 + 58*X^10 + 9*X^9 + 66*X^8 + 38*X^7 + 42*X^6 + 41*X^5 +
      19*X^4 + 18*X^3 + 21*X^2 + 16*X + 17) :=
  sq_step (by norm_num) pSeventeenB4s283 ⟨
    21*X^32 + 14*X^31 + 45*X^30 + 47*X^29 + 27*X^28 + 59*X^27 + 26*X^25 + X^24 + 65*X^23 + 29*X^22 +
      3*X^21 + 53*X^20 + 46*X^18 + 9*X^17 + 56*X^16 + 62*X^15 + 57*X^14 + 65*X^13 + 43*X^12 +
      35*X^11 + 18*X^10 + 51*X^9 + 8*X^8 + 9*X^7 + 8*X^6 + 28*X^5 + X^4 + 14*X^3 + 33*X^2 + 37*X +
      66,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s285 : XPow fSeventeenB4 1862358824873585151689747597867343461474838968531557417556
    (21*X^33 + 49*X^32 + 37*X^31 + 30*X^30 + 66*X^29 + 52*X^28 + 13*X^27 + 2*X^26 + 29*X^25 + 8*X^24 +
      34*X^23 + 28*X^22 + 3*X^21 + 50*X^20 + 55*X^19 + 13*X^18 + 12*X^17 + 18*X^16 + 33*X^15 +
      16*X^14 + 41*X^13 + 5*X^12 + 2*X^11 + 17*X^10 + 45*X^9 + 46*X^8 + 24*X^7 + 65*X^6 + 63*X^5 +
      48*X^4 + 60*X^3 + 36*X^2 + 40*X + 42) :=
  sq_step (by norm_num) pSeventeenB4s284 ⟨
    4*X^32 + 31*X^31 + 28*X^30 + X^29 + 25*X^28 + 36*X^27 + 9*X^26 + 27*X^25 + 39*X^24 + 10*X^23 +
      8*X^22 + 50*X^21 + 20*X^20 + 42*X^19 + 61*X^18 + 39*X^17 + 38*X^16 + 47*X^15 + 55*X^14 +
      23*X^13 + 5*X^12 + 14*X^11 + 31*X^10 + 26*X^9 + 45*X^8 + X^7 + 25*X^6 + 40*X^5 + 60*X^4 +
      3*X^3 + 4*X^2 + 39*X + 19,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s286 : XPow fSeventeenB4 1862358824873585151689747597867343461474838968531557417557
    (24*X^33 + 6*X^32 + 20*X^30 + 44*X^29 + 47*X^28 + 38*X^27 + 22*X^26 + 60*X^25 + 26*X^24 + 2*X^23 +
      49*X^22 + 16*X^21 + 28*X^20 + 14*X^19 + 46*X^18 + 42*X^17 + 35*X^16 + 30*X^15 + 31*X^14 + X^13 +
      50*X^12 + 66*X^11 + 41*X^10 + 33*X^9 + 55*X^8 + 26*X^7 + 62*X^6 + 54*X^5 + 46*X^4 + 19*X^3 +
      55*X^2 + 3*X + 62) :=
  mul_step (by norm_num) pSeventeenB4s285 pSeventeenB41 ⟨
    21,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s287 : XPow fSeventeenB4 3724717649747170303379495195734686922949677937063114835114
    (27*X^33 + 46*X^32 + 53*X^31 + 64*X^30 + 6*X^29 + 11*X^28 + 51*X^27 + 50*X^26 + 66*X^25 + 63*X^24 +
      31*X^23 + 4*X^22 + 18*X^21 + 14*X^20 + 25*X^19 + 5*X^18 + 5*X^17 + 39*X^16 + 2*X^15 + 48*X^14 +
      23*X^13 + 47*X^12 + 57*X^11 + 20*X^10 + 33*X^9 + 53*X^8 + 27*X^7 + 39*X^6 + 37*X^5 + 45*X^4 +
      66*X^3 + 26*X^2 + 48) :=
  sq_step (by norm_num) pSeventeenB4s286 ⟨
    40*X^32 + 33*X^31 + 27*X^30 + 18*X^29 + 63*X^28 + 55*X^27 + 3*X^26 + 62*X^25 + 7*X^24 + 54*X^23 +
      13*X^22 + 9*X^21 + 9*X^20 + 42*X^19 + 21*X^18 + 59*X^17 + 32*X^16 + 31*X^15 + 14*X^14 +
      27*X^13 + 38*X^12 + 66*X^11 + 48*X^10 + 10*X^9 + 60*X^8 + 31*X^7 + 17*X^6 + 52*X^5 + 37*X^3 +
      21*X^2 + 62*X + 24,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s288 : XPow fSeventeenB4 7449435299494340606758990391469373845899355874126229670228
    (2*X^33 + 22*X^32 + 58*X^31 + 22*X^30 + 64*X^29 + 19*X^28 + 60*X^27 + 33*X^26 + 31*X^25 + 16*X^24 +
      37*X^23 + 52*X^22 + 50*X^21 + 63*X^20 + 50*X^19 + 58*X^18 + 28*X^17 + 64*X^16 + 29*X^15 +
      65*X^14 + 48*X^13 + 7*X^12 + 3*X^11 + 35*X^10 + 57*X^9 + 60*X^8 + 14*X^7 + 43*X^6 + 18*X^5 +
      18*X^4 + 34*X^3 + 55*X^2 + 49*X + 23) :=
  sq_step (by norm_num) pSeventeenB4s287 ⟨
    59*X^32 + 56*X^31 + 13*X^30 + 33*X^29 + 5*X^28 + 13*X^27 + 3*X^26 + 53*X^25 + 48*X^24 + 59*X^23 +
      37*X^22 + 17*X^21 + 65*X^20 + 44*X^19 + 49*X^18 + 19*X^17 + 50*X^16 + 12*X^15 + 55*X^14 +
      30*X^13 + 46*X^12 + 31*X^11 + 41*X^10 + 37*X^9 + 40*X^8 + 2*X^7 + 27*X^6 + 49*X^5 + 58*X^4 +
      9*X^3 + 61*X^2 + 47*X + 26,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s289 : XPow fSeventeenB4 14898870598988681213517980782938747691798711748252459340456
    (50*X^33 + 22*X^32 + 34*X^31 + 45*X^30 + 61*X^29 + 29*X^28 + 23*X^27 + 14*X^26 + 56*X^25 + 35*X^24 +
      38*X^23 + 5*X^22 + 20*X^21 + 16*X^20 + 17*X^19 + 63*X^18 + 29*X^17 + 31*X^16 + 19*X^15 +
      39*X^14 + 65*X^13 + 59*X^12 + 8*X^10 + 37*X^9 + 7*X^8 + 44*X^7 + 32*X^6 + 2*X^5 + 14*X^4 +
      57*X^3 + 38*X^2 + 2*X + 22) :=
  sq_step (by norm_num) pSeventeenB4s288 ⟨
    4*X^32 + 29*X^31 + 63*X^30 + 63*X^29 + 18*X^28 + 57*X^27 + 14*X^26 + 15*X^25 + 35*X^24 + 43*X^23 +
      2*X^22 + 22*X^21 + 33*X^20 + 47*X^19 + 53*X^18 + 8*X^17 + 9*X^16 + 52*X^15 + 23*X^14 + 60*X^13 +
      35*X^12 + 59*X^11 + 39*X^10 + 8*X^9 + 39*X^8 + 66*X^7 + 49*X^6 + 55*X^5 + 17*X^4 + 40*X^3 +
      16*X^2 + 2*X + 39,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s290 : XPow fSeventeenB4 29797741197977362427035961565877495383597423496504918680912
    (42*X^33 + 22*X^32 + 5*X^31 + 2*X^30 + 64*X^29 + 66*X^28 + 4*X^27 + 22*X^26 + 14*X^25 + 42*X^24 +
      16*X^23 + 44*X^22 + 13*X^21 + 50*X^20 + 14*X^19 + 65*X^18 + 18*X^17 + 18*X^16 + 34*X^15 +
      25*X^14 + 8*X^12 + 65*X^11 + 29*X^10 + 20*X^9 + 4*X^8 + 46*X^7 + 61*X^6 + 28*X^5 + 28*X^4 +
      14*X^3 + 26*X^2 + 22*X + 42) :=
  sq_step (by norm_num) pSeventeenB4s289 ⟨
    21*X^32 + 31*X^31 + 29*X^30 + 28*X^29 + 15*X^28 + 51*X^27 + 7*X^26 + 55*X^25 + 44*X^24 + 43*X^23 +
      56*X^22 + 59*X^21 + 9*X^20 + 5*X^19 + 63*X^18 + 6*X^17 + 12*X^16 + 12*X^15 + 12*X^14 + 19*X^13 +
      35*X^12 + 34*X^11 + 34*X^10 + 66*X^9 + 15*X^8 + 53*X^7 + 51*X^6 + 43*X^5 + 51*X^4 + 46*X^3 +
      24*X^2 + 12*X + 34,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s291 : XPow fSeventeenB4 29797741197977362427035961565877495383597423496504918680913
    (39*X^33 + 10*X^32 + 9*X^31 + 39*X^30 + 50*X^29 + 5*X^28 + 27*X^27 + 12*X^25 + 59*X^23 + 38*X^22 +
      49*X^21 + 27*X^20 + 19*X^18 + 66*X^17 + 38*X^16 + 53*X^15 + 47*X^14 + 27*X^12 + 60*X^11 +
      12*X^10 + 45*X^9 + 41*X^8 + 50*X^7 + 26*X^6 + 40*X^5 + 53*X^4 + 59*X^3 + 52*X^2 + 31*X + 57) :=
  mul_step (by norm_num) pSeventeenB4s290 pSeventeenB41 ⟨
    42,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s292 : XPow fSeventeenB4 59595482395954724854071923131754990767194846993009837361826
    (47*X^33 + 53*X^32 + 40*X^31 + 31*X^30 + 8*X^29 + 6*X^28 + 55*X^27 + 7*X^26 + 23*X^25 + 21*X^24 +
      22*X^23 + 59*X^22 + 23*X^21 + 50*X^20 + 30*X^19 + 17*X^18 + 58*X^17 + 40*X^16 + 22*X^15 +
      4*X^14 + 40*X^13 + 34*X^12 + 23*X^11 + 40*X^10 + 11*X^9 + 59*X^8 + 23*X^7 + 8*X^6 + 40*X^5 +
      57*X^4 + 64*X^3 + 3*X^2 + 61*X + 65) :=
  sq_step (by norm_num) pSeventeenB4s291 ⟨
    47*X^32 + 3*X^31 + 8*X^30 + 27*X^29 + 57*X^28 + 66*X^27 + 42*X^26 + 30*X^25 + 63*X^24 + 6*X^23 +
      58*X^21 + 14*X^20 + 51*X^19 + 56*X^18 + 59*X^17 + 8*X^16 + 31*X^15 + 11*X^14 + 56*X^13 +
      15*X^12 + 60*X^11 + 50*X^10 + 30*X^9 + 29*X^8 + 37*X^7 + 62*X^6 + 62*X^5 + 10*X^4 + 38*X^3 +
      66*X^2 + 40*X + 13,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s293 : XPow fSeventeenB4 59595482395954724854071923131754990767194846993009837361827
    (13*X^33 + 44*X^32 + 50*X^31 + 55*X^30 + 20*X^29 + 29*X^28 + 11*X^27 + 52*X^26 + 64*X^25 + 36*X^24 +
      4*X^23 + 43*X^22 + 9*X^21 + 27*X^20 + 32*X^19 + 32*X^18 + 65*X^17 + 52*X^16 + 13*X^15 +
      24*X^14 + 41*X^13 + 6*X^12 + 38*X^11 + 18*X^10 + 65*X^9 + 19*X^8 + 26*X^7 + 25*X^6 + 13*X^5 +
      55*X^4 + 16*X^3 + 18*X^2 + 16*X + 59) :=
  mul_step (by norm_num) pSeventeenB4s292 pSeventeenB41 ⟨
    47,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s294 : XPow fSeventeenB4 119190964791909449708143846263509981534389693986019674723654
    (40*X^33 + 18*X^32 + 8*X^31 + 62*X^30 + 34*X^29 + 43*X^28 + 22*X^27 + 47*X^26 + 62*X^25 + 3*X^24 +
      61*X^23 + 11*X^22 + 20*X^21 + 44*X^20 + 6*X^19 + 65*X^18 + 4*X^17 + 49*X^16 + 33*X^15 +
      29*X^14 + 44*X^13 + 18*X^12 + 35*X^11 + 19*X^10 + 39*X^9 + 15*X^8 + 33*X^7 + 31*X^6 + 60*X^5 +
      55*X^4 + 34*X^3 + 58*X^2 + 11*X + 59) :=
  sq_step (by norm_num) pSeventeenB4s293 ⟨
    35*X^32 + 8*X^31 + 29*X^30 + 61*X^29 + 44*X^28 + 56*X^27 + 41*X^26 + 36*X^25 + 23*X^24 + 6*X^23 +
      10*X^22 + 9*X^21 + 38*X^20 + 46*X^19 + 23*X^18 + 26*X^17 + 7*X^16 + 18*X^15 + 54*X^14 +
      56*X^13 + 34*X^12 + 33*X^11 + 36*X^10 + 2*X^9 + 56*X^8 + 47*X^7 + 48*X^6 + X^5 + 29*X^4 +
      17*X^3 + 16*X^2 + 28*X + 21,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s295 : XPow fSeventeenB4 119190964791909449708143846263509981534389693986019674723655
    (31*X^33 + 24*X^31 + 7*X^30 + 15*X^29 + 7*X^28 + 39*X^27 + 4*X^26 + 51*X^25 + 33*X^24 + 54*X^23 +
      47*X^22 + 59*X^21 + 12*X^20 + 35*X^19 + 56*X^18 + 66*X^17 + 40*X^16 + 11*X^15 + 9*X^14 +
      4*X^13 + 2*X^12 + 23*X^11 + 25*X^10 + 3*X^9 + 41*X^8 + 62*X^7 + 23*X^6 + 9*X^5 + 52*X^4 +
      32*X^3 + 30*X^2 + 23*X + 16) :=
  mul_step (by norm_num) pSeventeenB4s294 pSeventeenB41 ⟨
    40,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s296 : XPow fSeventeenB4 238381929583818899416287692527019963068779387972039349447310
    (62*X^33 + 18*X^32 + 41*X^30 + 53*X^29 + 26*X^28 + 5*X^27 + 12*X^26 + 24*X^25 + 10*X^24 + 30*X^23 +
      27*X^22 + 17*X^21 + 21*X^20 + 24*X^19 + 40*X^18 + 4*X^17 + 46*X^16 + 28*X^15 + 10*X^14 +
      20*X^13 + 19*X^12 + 60*X^11 + 52*X^10 + 5*X^9 + 47*X^8 + 37*X^7 + 28*X^6 + 34*X^5 + 64*X^4 +
      42*X^3 + 27*X^2 + 35*X + 31) :=
  sq_step (by norm_num) pSeventeenB4s295 ⟨
    23*X^32 + 46*X^31 + 21*X^30 + 53*X^29 + 26*X^28 + 14*X^27 + 66*X^26 + 54*X^25 + 22*X^24 + 58*X^23 +
      47*X^22 + 37*X^21 + 14*X^20 + X^19 + 61*X^18 + 17*X^17 + 29*X^16 + 58*X^15 + 65*X^14 + 8*X^13 +
      20*X^12 + 39*X^11 + 17*X^10 + 13*X^9 + 8*X^8 + 64*X^7 + 28*X^6 + 31*X^5 + 40*X^4 + 60*X^3 +
      22*X + 7,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s297 : XPow fSeventeenB4 476763859167637798832575385054039926137558775944078698894620
    (54*X^33 + 29*X^32 + 40*X^31 + 11*X^30 + 52*X^29 + 61*X^28 + 40*X^27 + 63*X^26 + 14*X^25 + 63*X^24 +
      20*X^23 + 64*X^22 + 32*X^21 + 4*X^20 + 7*X^19 + 30*X^18 + 34*X^17 + 9*X^16 + 21*X^15 + 62*X^14 +
      17*X^13 + 16*X^12 + 6*X^11 + 37*X^10 + 5*X^9 + 4*X^8 + 58*X^7 + 15*X^6 + 22*X^5 + 15*X^4 +
      55*X^3 + 62*X^2 + 58*X + 15) :=
  sq_step (by norm_num) pSeventeenB4s296 ⟨
    25*X^32 + 4*X^31 + 59*X^30 + 62*X^29 + 61*X^28 + 3*X^27 + 58*X^26 + 59*X^25 + 41*X^24 + 32*X^23 +
      3*X^22 + 53*X^21 + 41*X^20 + 54*X^19 + 25*X^18 + 52*X^17 + 29*X^16 + 66*X^15 + 22*X^14 +
      36*X^13 + 19*X^12 + 36*X^11 + 58*X^10 + 57*X^9 + 45*X^8 + 21*X^7 + 15*X^6 + 6*X^5 + 43*X^4 +
      14*X^3 + 45*X^2 + 35*X + 47,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s298 : XPow fSeventeenB4 953527718335275597665150770108079852275117551888157397789240
    (63*X^33 + 36*X^32 + 56*X^31 + 58*X^30 + 45*X^29 + 36*X^28 + 33*X^27 + 48*X^26 + 55*X^25 + 27*X^24 +
      42*X^23 + 60*X^22 + 60*X^21 + 31*X^20 + 6*X^18 + 27*X^17 + 16*X^16 + 21*X^15 + 15*X^14 +
      26*X^13 + 59*X^12 + 18*X^11 + 13*X^10 + 11*X^9 + 28*X^8 + 17*X^7 + 10*X^6 + 44*X^5 + 61*X^4 +
      16*X^3 + 30*X^2 + 40*X + 2) :=
  sq_step (by norm_num) pSeventeenB4s297 ⟨
    35*X^32 + 53*X^31 + 34*X^30 + 18*X^29 + 59*X^28 + 22*X^27 + 36*X^26 + 10*X^25 + 8*X^24 + 7*X^23 +
      60*X^22 + 24*X^21 + 4*X^20 + 11*X^19 + 63*X^18 + 28*X^17 + 10*X^16 + 27*X^15 + 55*X^14 +
      39*X^13 + 36*X^12 + 63*X^11 + 54*X^10 + 50*X^9 + 16*X^8 + 21*X^7 + 20*X^6 + 37*X^5 + 23*X^4 +
      33*X^3 + 11*X^2 + 65*X + 12,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s299 : XPow fSeventeenB4 1907055436670551195330301540216159704550235103776314795578480
    (19*X^33 + 42*X^32 + 6*X^31 + 13*X^30 + 46*X^29 + 9*X^28 + 6*X^27 + 28*X^26 + 44*X^25 + 55*X^24 +
      60*X^23 + 52*X^22 + 2*X^21 + 29*X^20 + 5*X^19 + 31*X^18 + 53*X^17 + 56*X^16 + 57*X^15 +
      30*X^14 + 10*X^13 + 7*X^12 + 32*X^11 + 60*X^10 + 2*X^9 + 36*X^8 + 53*X^7 + 5*X^6 + 6*X^5 +
      39*X^4 + 62*X^3 + 27*X^2 + 14*X + 7) :=
  sq_step (by norm_num) pSeventeenB4s298 ⟨
    16*X^32 + 12*X^31 + 38*X^30 + 62*X^29 + 38*X^28 + 36*X^27 + 21*X^26 + X^25 + 31*X^24 + 23*X^23 +
      51*X^22 + 19*X^21 + 55*X^20 + 4*X^19 + 45*X^18 + 20*X^17 + 5*X^16 + 57*X^15 + 56*X^14 +
      47*X^13 + 38*X^12 + 30*X^11 + 19*X^10 + 42*X^9 + 31*X^8 + 38*X^7 + 18*X^5 + 54*X^3 + 38*X^2 +
      12*X + 41,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s300 : XPow fSeventeenB4 3814110873341102390660603080432319409100470207552629591156960
    (11*X^33 + 17*X^32 + 32*X^31 + 61*X^30 + 3*X^29 + 54*X^28 + 24*X^27 + 59*X^26 + 15*X^25 + 5*X^24 +
      20*X^23 + 34*X^22 + 60*X^21 + 51*X^20 + 45*X^19 + 50*X^18 + 55*X^17 + 53*X^16 + 49*X^15 +
      36*X^14 + 57*X^13 + 58*X^12 + 9*X^11 + 19*X^10 + 5*X^9 + 64*X^8 + 49*X^7 + 63*X^6 + X^5 +
      33*X^4 + 29*X^3 + 4*X^2 + 15*X + 56) :=
  sq_step (by norm_num) pSeventeenB4s299 ⟨
    26*X^32 + 40*X^31 + 30*X^30 + 27*X^29 + 31*X^28 + 10*X^27 + 64*X^26 + 3*X^25 + 50*X^24 + 60*X^23 +
      60*X^22 + 9*X^21 + 11*X^20 + 26*X^19 + 56*X^18 + 23*X^17 + 4*X^16 + 13*X^15 + 43*X^14 +
      31*X^13 + 16*X^12 + 14*X^11 + 62*X^10 + 59*X^9 + 48*X^8 + 42*X^7 + 62*X^6 + 58*X^5 + 4*X^4 +
      63*X^3 + 66*X^2 + 14*X + 51,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s301 : XPow fSeventeenB4 7628221746682204781321206160864638818200940415105259182313920
    (38*X^33 + 14*X^32 + 36*X^31 + 43*X^30 + 31*X^29 + 21*X^28 + 45*X^27 + 64*X^26 + 44*X^25 + 11*X^24 +
      32*X^23 + 66*X^22 + 62*X^21 + 63*X^20 + 49*X^19 + 53*X^18 + 28*X^17 + 46*X^16 + 57*X^15 +
      29*X^14 + 35*X^13 + 49*X^12 + 27*X^11 + 52*X^10 + 31*X^9 + 53*X^8 + 38*X^7 + X^6 + 60*X^5 +
      X^4 + 62*X^3 + 17*X^2 + 33*X) :=
  sq_step (by norm_num) pSeventeenB4s300 ⟨
    54*X^32 + 13*X^31 + 30*X^30 + 4*X^29 + 62*X^28 + 58*X^27 + 56*X^26 + 17*X^25 + 2*X^24 + 54*X^23 +
      33*X^22 + 14*X^21 + 35*X^20 + 55*X^19 + 37*X^18 + 11*X^17 + 45*X^16 + 55*X^15 + 4*X^14 +
      18*X^13 + 33*X^12 + 6*X^11 + 63*X^10 + 6*X^9 + 49*X^8 + 29*X^7 + 36*X^6 + 35*X^5 + 56*X^4 +
      43*X^3 + 63*X^2 + 51*X + 66,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s302 : XPow fSeventeenB4 15256443493364409562642412321729277636401880830210518364627840
    (10*X^33 + 63*X^32 + 46*X^31 + 26*X^30 + 60*X^29 + 37*X^28 + 45*X^27 + 46*X^26 + 22*X^25 + 40*X^24 +
      27*X^23 + 8*X^22 + 30*X^21 + 31*X^20 + 37*X^17 + 42*X^16 + 10*X^15 + 31*X^14 + 62*X^13 +
      16*X^12 + 27*X^11 + 31*X^10 + 56*X^9 + 4*X^8 + 12*X^7 + 58*X^6 + 35*X^5 + 36*X^4 + 8*X^3 +
      2*X^2 + 23*X + 18) :=
  sq_step (by norm_num) pSeventeenB4s301 ⟨
    37*X^32 + 66*X^31 + 55*X^30 + 53*X^29 + 41*X^28 + 8*X^27 + 60*X^26 + 19*X^25 + 58*X^24 + 10*X^23 +
      31*X^22 + 3*X^20 + 10*X^19 + 6*X^18 + 33*X^17 + X^16 + 55*X^15 + 50*X^14 + 38*X^13 + 16*X^12 +
      66*X^11 + 20*X^10 + 2*X^9 + 2*X^8 + 12*X^7 + 29*X^6 + 32*X^5 + 55*X^4 + 51*X^3 + 15*X^2 + 8*X +
      45,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s303 : XPow fSeventeenB4 15256443493364409562642412321729277636401880830210518364627841
    (16*X^33 + 44*X^32 + 50*X^31 + 3*X^30 + 30*X^29 + 58*X^28 + 44*X^27 + 41*X^26 + 52*X^25 + 20*X^24 +
      2*X^23 + 20*X^22 + 18*X^21 + 35*X^20 + 26*X^19 + 50*X^18 + 63*X^17 + 62*X^16 + 60*X^15 +
      3*X^14 + 46*X^13 + 2*X^12 + 32*X^11 + 19*X^10 + X^9 + 14*X^8 + 49*X^7 + 9*X^6 + 58*X^5 +
      46*X^4 + 29*X^3 + 11*X^2 + 9*X + 4) :=
  mul_step (by norm_num) pSeventeenB4s302 pSeventeenB41 ⟨
    10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s304 : XPow fSeventeenB4 30512886986728819125284824643458555272803761660421036729255682
    (52*X^33 + 9*X^32 + 62*X^31 + 60*X^30 + 64*X^29 + 21*X^28 + 9*X^27 + 16*X^26 + 35*X^25 + 65*X^24 +
      40*X^23 + 65*X^22 + 25*X^21 + 30*X^20 + 51*X^19 + 62*X^18 + 54*X^17 + 34*X^16 + 61*X^15 +
      60*X^14 + 49*X^13 + 40*X^12 + 37*X^11 + 45*X^10 + 20*X^9 + 12*X^8 + 42*X^7 + 46*X^6 + 21*X^5 +
      49*X^4 + 44*X^3 + 19*X^2 + 46*X + 14) :=
  sq_step (by norm_num) pSeventeenB4s303 ⟨
    55*X^32 + 44*X^31 + 62*X^30 + 13*X^29 + 39*X^28 + 61*X^27 + 34*X^26 + 33*X^25 + 49*X^24 + 61*X^23 +
      56*X^22 + 24*X^21 + 11*X^20 + 33*X^19 + 63*X^18 + 3*X^17 + 65*X^16 + 40*X^14 + 61*X^13 +
      14*X^12 + 53*X^11 + 41*X^10 + 31*X^9 + 64*X^8 + 36*X^7 + 12*X^6 + 6*X^5 + 57*X^4 + 54*X^2 +
      41*X + 62,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s305 : XPow fSeventeenB4 61025773973457638250569649286917110545607523320842073458511364
    (66) :=
  sq_step (by norm_num) pSeventeenB4s304 ⟨
    24*X^32 + 46*X^31 + 10*X^30 + 41*X^29 + 56*X^28 + 12*X^27 + 66*X^26 + X^25 + 36*X^24 + 12*X^23 +
      22*X^22 + 19*X^21 + 45*X^20 + X^19 + 8*X^18 + 61*X^17 + 4*X^16 + 54*X^14 + 12*X^13 + 39*X^12 +
      28*X^11 + 52*X^10 + 5*X^9 + 6*X^8 + 62*X^7 + 43*X^6 + 55*X^5 + 20*X^4 + 26*X^2 + 52*X + 10,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s306 : XPow fSeventeenB4 122051547946915276501139298573834221091215046641684146917022728
    (1) :=
  sq_step (by norm_num) pSeventeenB4s305 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4s307 : XPow fSeventeenB4 122051547946915276501139298573834221091215046641684146917022729
    (X) :=
  mul_step (by norm_num) pSeventeenB4s306 pSeventeenB41 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! Factor 4 again, at the smaller exponent `67 ^ 2`, for the coprimality below. -/

theorem pSeventeenB4cs0 : XPow fSeventeenB4 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenB41 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs1 : XPow fSeventeenB4 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenB4cs0 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs2 : XPow fSeventeenB4 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenB4cs1 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs3 : XPow fSeventeenB4 16
    (X^16) :=
  sq_step (by norm_num) pSeventeenB4cs2 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs4 : XPow fSeventeenB4 17
    (X^17) :=
  mul_step (by norm_num) pSeventeenB4cs3 pSeventeenB41 ⟨
    0,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs5 : XPow fSeventeenB4 34
    (2*X^33 + 40*X^32 + 56*X^31 + X^30 + 6*X^29 + 8*X^28 + 40*X^27 + 22*X^26 + 28*X^25 + 6*X^24 + 53*X^23 +
      66*X^22 + 59*X^21 + 37*X^20 + 16*X^19 + 8*X^18 + 49*X^17 + 32*X^16 + 23*X^15 + 41*X^14 +
      3*X^13 + 31*X^12 + 47*X^11 + 3*X^10 + 60*X^9 + 27*X^8 + 46*X^7 + 51*X^6 + 29*X^5 + 44*X^4 +
      63*X^3 + 39*X^2 + 46*X + 54) :=
  sq_step (by norm_num) pSeventeenB4cs4 ⟨
    1,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs6 : XPow fSeventeenB4 35
    (44*X^33 + 2*X^32 + 46*X^31 + 8*X^30 + 20*X^29 + 56*X^28 + 35*X^27 + 5*X^26 + 62*X^25 + 65*X^24 +
      38*X^23 + 57*X^22 + 21*X^21 + 23*X^20 + 40*X^19 + 65*X^18 + 63*X^17 + 20*X^16 + 20*X^15 +
      18*X^14 + 37*X^13 + 42*X^12 + 30*X^11 + 66*X^10 + 13*X^9 + 33*X^8 + 9*X^7 + 64*X^6 + 35*X^5 +
      17*X^4 + 31*X^3 + 57*X^2 + 12*X + 41) :=
  mul_step (by norm_num) pSeventeenB4cs5 pSeventeenB41 ⟨
    2,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs7 : XPow fSeventeenB4 70
    (24*X^33 + 18*X^32 + 29*X^31 + 10*X^30 + 7*X^29 + 28*X^28 + 13*X^27 + 42*X^26 + 38*X^25 + 21*X^24 +
      17*X^23 + 29*X^22 + 49*X^21 + 35*X^20 + X^19 + 36*X^18 + 32*X^17 + 16*X^16 + 19*X^15 + 28*X^14 +
      30*X^13 + 16*X^12 + 65*X^11 + 29*X^10 + 30*X^9 + 16*X^8 + 38*X^7 + 42*X^6 + 12*X^5 + 11*X^4 +
      46*X^3 + 31*X^2 + 36*X + 40) :=
  sq_step (by norm_num) pSeventeenB4cs6 ⟨
    60*X^32 + 28*X^31 + 9*X^30 + 26*X^29 + 52*X^28 + 8*X^27 + 37*X^26 + 2*X^25 + 38*X^24 + 34*X^23 +
      15*X^22 + 54*X^21 + 18*X^20 + 17*X^19 + 41*X^18 + 46*X^17 + 53*X^16 + 45*X^15 + 24*X^14 +
      38*X^13 + 37*X^12 + 15*X^11 + 66*X^10 + 24*X^9 + 52*X^8 + 5*X^7 + 58*X^6 + 36*X^5 + 25*X^4 +
      51*X^3 + 39*X^2 + 49*X + 18,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs8 : XPow fSeventeenB4 140
    (29*X^33 + 13*X^32 + 45*X^31 + 18*X^30 + 15*X^29 + 29*X^28 + 56*X^27 + 45*X^26 + 19*X^25 + 61*X^24 +
      22*X^23 + 52*X^22 + X^21 + 35*X^20 + 35*X^19 + 34*X^18 + 33*X^17 + 17*X^16 + 32*X^15 + 29*X^14 +
      52*X^13 + 8*X^12 + 37*X^11 + 37*X^10 + 20*X^9 + 31*X^7 + 3*X^6 + 28*X^5 + 32*X^4 + 16*X^3 +
      56*X^2 + 48*X + 21) :=
  sq_step (by norm_num) pSeventeenB4cs7 ⟨
    40*X^32 + 6*X^31 + 45*X^30 + 7*X^29 + 42*X^28 + 13*X^27 + 14*X^26 + 28*X^25 + 36*X^24 + 26*X^23 +
      28*X^22 + 7*X^21 + 18*X^20 + 43*X^19 + 30*X^18 + 64*X^17 + 48*X^16 + 56*X^15 + 14*X^14 +
      24*X^13 + 33*X^12 + 47*X^11 + 12*X^10 + 44*X^9 + 52*X^8 + 32*X^7 + 29*X^6 + 16*X^5 + 5*X^4 +
      63*X^3 + 21*X^2 + 26*X + 39,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs9 : XPow fSeventeenB4 280
    (6*X^33 + 56*X^32 + 39*X^31 + 42*X^30 + 3*X^29 + 44*X^28 + 63*X^27 + 14*X^26 + 7*X^25 + 32*X^24 +
      33*X^23 + 58*X^22 + 30*X^21 + 37*X^20 + 27*X^19 + 23*X^18 + 32*X^17 + 38*X^16 + 13*X^15 + X^14 +
      16*X^13 + 48*X^12 + 43*X^11 + 66*X^10 + 14*X^9 + 24*X^8 + 8*X^7 + 13*X^6 + 49*X^5 + 27*X^4 +
      2*X^3 + 45*X^2 + 64*X + 24) :=
  sq_step (by norm_num) pSeventeenB4cs8 ⟨
    37*X^32 + 24*X^31 + 19*X^30 + 58*X^29 + 59*X^28 + 3*X^27 + 24*X^26 + 3*X^25 + 55*X^24 + 9*X^23 +
      36*X^22 + 62*X^21 + 19*X^19 + 32*X^18 + 44*X^17 + 23*X^16 + 6*X^15 + 25*X^14 + 60*X^13 +
      16*X^12 + 56*X^11 + 19*X^10 + 28*X^9 + 14*X^8 + 28*X^7 + 23*X^6 + 35*X^5 + 10*X^4 + 52*X^3 +
      56*X^2 + 2*X + 63,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs10 : XPow fSeventeenB4 560
    (13*X^33 + X^32 + 27*X^31 + 56*X^30 + 4*X^29 + 17*X^28 + 44*X^27 + 21*X^26 + 5*X^25 + 54*X^24 +
      55*X^23 + 14*X^22 + 42*X^21 + 63*X^20 + 6*X^19 + 47*X^18 + 10*X^17 + 6*X^16 + 43*X^15 +
      50*X^14 + 46*X^13 + 20*X^12 + 29*X^11 + 45*X^10 + 25*X^9 + 56*X^8 + 59*X^7 + 59*X^6 + 42*X^5 +
      41*X^4 + 52*X^3 + 3*X^2 + 37*X + 35) :=
  sq_step (by norm_num) pSeventeenB4cs9 ⟨
    36*X^32 + 7*X^31 + 33*X^30 + 65*X^29 + 32*X^28 + 31*X^27 + 29*X^26 + 12*X^25 + 8*X^24 + 29*X^23 +
      9*X^22 + 45*X^21 + 58*X^20 + 10*X^19 + 7*X^18 + 44*X^17 + 59*X^16 + 47*X^15 + 39*X^14 +
      25*X^13 + 34*X^12 + 31*X^11 + 34*X^10 + 52*X^9 + 39*X^8 + 13*X^7 + 27*X^6 + 44*X^5 + 64*X^4 +
      60*X^3 + 6*X^2 + 14*X + 21,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs11 : XPow fSeventeenB4 561
    (27*X^33 + 11*X^32 + 47*X^31 + 17*X^30 + 28*X^29 + 14*X^28 + 5*X^27 + 23*X^26 + 16*X^25 + 66*X^24 +
      33*X^23 + 29*X^22 + 26*X^21 + 18*X^20 + 54*X^19 + 47*X^18 + 40*X^17 + 57*X^16 + 14*X^15 +
      43*X^14 + 59*X^13 + 30*X^12 + 53*X^11 + 64*X^10 + 32*X^9 + 8*X^8 + 54*X^7 + 35*X^6 + 16*X^5 +
      21*X^4 + 18*X^3 + 8*X^2 + 30*X + 32) :=
  mul_step (by norm_num) pSeventeenB4cs10 pSeventeenB41 ⟨
    13,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs12 : XPow fSeventeenB4 1122
    (3*X^33 + 34*X^32 + 46*X^31 + 56*X^30 + 53*X^29 + 43*X^28 + 43*X^27 + 26*X^26 + 52*X^25 + 19*X^24 +
      41*X^23 + 49*X^22 + 35*X^21 + 8*X^20 + 7*X^19 + 8*X^18 + 34*X^17 + 33*X^16 + 5*X^15 + 7*X^14 +
      28*X^13 + 38*X^12 + 46*X^11 + 46*X^10 + 52*X^9 + 58*X^8 + 55*X^7 + 49*X^6 + 6*X^5 + 18*X^4 +
      21*X^3 + 65*X^2 + 8*X + 15) :=
  sq_step (by norm_num) pSeventeenB4cs11 ⟨
    59*X^32 + 42*X^31 + 11*X^30 + 57*X^29 + 25*X^28 + 14*X^27 + 12*X^26 + 48*X^25 + 54*X^24 + 35*X^23 +
      53*X^22 + 66*X^21 + 50*X^20 + 26*X^19 + 28*X^18 + 10*X^17 + X^16 + 37*X^15 + 66*X^14 + 45*X^13 +
      20*X^12 + 65*X^11 + 25*X^10 + 31*X^9 + 44*X^8 + 18*X^7 + 17*X^6 + 52*X^5 + 35*X^4 + 49*X^3 +
      26*X^2 + 55*X + 57,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs13 : XPow fSeventeenB4 2244
    (25*X^33 + 23*X^32 + 50*X^31 + 30*X^30 + 42*X^29 + 17*X^28 + 31*X^27 + 8*X^25 + 8*X^24 + 52*X^23 +
      17*X^22 + 60*X^21 + 21*X^20 + 36*X^19 + 47*X^18 + 6*X^17 + 26*X^16 + 20*X^15 + 53*X^14 +
      8*X^13 + 60*X^12 + 38*X^11 + 59*X^10 + 31*X^9 + 37*X^8 + 66*X^7 + 33*X^6 + 24*X^5 + 5*X^4 +
      61*X^3 + 27*X^2 + 62*X + 62) :=
  sq_step (by norm_num) pSeventeenB4cs12 ⟨
    9*X^32 + 21*X^31 + 25*X^30 + 34*X^29 + 53*X^28 + 29*X^27 + 22*X^26 + 34*X^25 + 40*X^24 + 53*X^23 +
      45*X^22 + 64*X^21 + 10*X^20 + 2*X^19 + 60*X^18 + 59*X^17 + 40*X^16 + 39*X^15 + 54*X^14 +
      16*X^13 + 61*X^12 + 3*X^11 + 47*X^10 + 25*X^9 + 55*X^8 + 17*X^7 + 45*X^6 + 48*X^5 + 20*X^4 +
      62*X^3 + 19*X^2 + 20*X + 28,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs14 : XPow fSeventeenB4 4488
    (63*X^33 + 32*X^32 + 31*X^31 + 43*X^30 + 27*X^29 + 48*X^28 + 25*X^27 + 20*X^26 + 64*X^25 + 56*X^24 +
      23*X^23 + 56*X^22 + 23*X^21 + 59*X^20 + 17*X^19 + 59*X^18 + 10*X^17 + 46*X^16 + 17*X^15 +
      26*X^14 + 56*X^13 + 63*X^12 + 41*X^11 + 4*X^10 + 24*X^9 + 25*X^8 + 17*X^7 + 26*X^6 + 14*X^5 +
      26*X^4 + 55*X^3 + 46*X^2 + 7*X + 5) :=
  sq_step (by norm_num) pSeventeenB4cs13 ⟨
    22*X^32 + 55*X^31 + 66*X^30 + 61*X^29 + 52*X^28 + 15*X^27 + 63*X^26 + 6*X^25 + 20*X^24 + 13*X^23 +
      20*X^22 + 54*X^21 + 66*X^20 + X^19 + 12*X^18 + 53*X^17 + 33*X^16 + 65*X^15 + 36*X^14 + 64*X^13 +
      19*X^12 + 2*X^11 + 39*X^10 + 46*X^9 + 9*X^8 + 62*X^7 + 63*X^6 + 47*X^5 + 52*X^4 + 65*X^3 +
      49*X^2 + 48*X + 17,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB4cs15 : XPow fSeventeenB4 4489
    (24*X^33 + 5*X^32 + 20*X^31 + 23*X^30 + 24*X^29 + 60*X^28 + 61*X^27 + 43*X^26 + 11*X^25 + 66*X^24 +
      45*X^23 + 27*X^22 + 24*X^21 + 3*X^20 + 62*X^19 + 45*X^18 + 51*X^17 + 23*X^16 + X^15 + 26*X^14 +
      51*X^13 + 51*X^12 + 17*X^11 + 12*X^10 + 53*X^9 + 43*X^8 + 43*X^7 + 11*X^6 + 44*X^5 + 13*X^4 +
      62*X^3 + 52*X^2 + 22*X + 52) :=
  mul_step (by norm_num) pSeventeenB4cs14 pSeventeenB41 ⟨
    63,
    by simp only [fSeventeenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

end Fermat.MazurNonCMCertificate

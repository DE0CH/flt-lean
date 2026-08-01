/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius

/-!
# Row `p = 17`, `j = −297756989/2`: factor 2 of `H`, and its two square-and-multiply chains

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

/-- Irreducible factor 2 of `H` on this row, of degree 34.  Its irreducibility is
not used anywhere — only that the 4 factors are pairwise coprime. -/
noncomputable def fSeventeenB2 : (ZMod 67)[X] :=
  X^34 + 14*X^33 + 32*X^32 + 32*X^31 + 34*X^30 + 56*X^29 + 60*X^28 + 10*X^27 + 51*X^26 + 63*X^25 +
    15*X^24 + 58*X^23 + 50*X^22 + 50*X^21 + 66*X^20 + 38*X^19 + 60*X^18 + 6*X^17 + 36*X^16 + 8*X^15 +
    53*X^14 + 65*X^13 + 65*X^12 + 14*X^11 + 17*X^10 + 8*X^9 + 63*X^8 + 20*X^7 + 66*X^6 + 11*X^5 +
    43*X^4 + 27*X^3 + 66*X^2 + 3*X + 58

/-! ### Factor 2: `X ^ (67 ^ 34)` mod `f` by square-and-multiply -/

theorem pSeventeenB21 : XPow fSeventeenB2 1 X := xpow_one _

theorem pSeventeenB2s0 : XPow fSeventeenB2 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenB21 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s1 : XPow fSeventeenB2 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenB2s0 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s2 : XPow fSeventeenB2 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenB2s1 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s3 : XPow fSeventeenB2 9
    (X^9) :=
  mul_step (by norm_num) pSeventeenB2s2 pSeventeenB21 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s4 : XPow fSeventeenB2 18
    (X^18) :=
  sq_step (by norm_num) pSeventeenB2s3 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s5 : XPow fSeventeenB2 36
    (63*X^33 + 57*X^32 + 63*X^31 + 39*X^30 + 21*X^29 + 31*X^28 + 16*X^27 + 7*X^26 + 4*X^25 + 44*X^24 +
      49*X^23 + 5*X^22 + 56*X^21 + 33*X^20 + 29*X^19 + 57*X^18 + 48*X^17 + 51*X^16 + 35*X^15 +
      59*X^14 + 18*X^13 + 38*X^12 + 11*X^11 + 8*X^10 + 19*X^9 + 66*X^8 + 45*X^7 + 7*X^6 + 44*X^5 +
      27*X^4 + 44*X^3 + 14*X^2 + 52*X + 2) :=
  sq_step (by norm_num) pSeventeenB2s4 ⟨
    X^2 + 53*X + 30,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s6 : XPow fSeventeenB2 37
    (46*X^33 + 57*X^32 + 33*X^31 + 23*X^30 + 54*X^29 + 55*X^28 + 47*X^27 + 7*X^26 + 28*X^25 + 42*X^24 +
      36*X^23 + 55*X^22 + 32*X^21 + 25*X^20 + 8*X^19 + 20*X^18 + 8*X^17 + 45*X^16 + 24*X^15 +
      29*X^14 + 30*X^13 + 3*X^12 + 64*X^11 + 20*X^10 + 31*X^9 + 29*X^8 + 20*X^7 + 40*X^6 + 4*X^5 +
      15*X^4 + 55*X^3 + 48*X^2 + 14*X + 31) :=
  mul_step (by norm_num) pSeventeenB2s5 pSeventeenB21 ⟨
    63,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s7 : XPow fSeventeenB2 74
    (49*X^33 + 38*X^32 + 38*X^31 + 5*X^30 + 13*X^29 + 6*X^28 + 53*X^27 + 31*X^26 + 43*X^25 + 35*X^24 +
      47*X^23 + 50*X^22 + 56*X^21 + 46*X^20 + 16*X^19 + 24*X^18 + 47*X^17 + 20*X^16 + 52*X^15 +
      18*X^14 + 9*X^13 + 11*X^12 + 39*X^11 + 50*X^10 + 57*X^9 + 56*X^8 + 35*X^7 + 35*X^6 + 10*X^5 +
      34*X^4 + 12*X^3 + 2*X^2 + 37*X + 27) :=
  sq_step (by norm_num) pSeventeenB2s6 ⟨
    39*X^32 + 8*X^31 + 34*X^30 + 12*X^29 + 12*X^28 + 62*X^27 + 62*X^26 + 3*X^25 + 43*X^24 + 2*X^23 +
      57*X^22 + 7*X^21 + 41*X^20 + 31*X^19 + 35*X^18 + 62*X^17 + 32*X^16 + 10*X^15 + 46*X^14 +
      48*X^13 + 50*X^12 + 53*X^11 + 62*X^10 + 20*X^9 + 36*X^8 + 21*X^7 + 14*X^6 + 34*X^5 + 62*X^4 +
      19*X^2 + 17*X + 60,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s8 : XPow fSeventeenB2 75
    (22*X^33 + 11*X^32 + 45*X^31 + 22*X^30 + 9*X^29 + 61*X^28 + 10*X^27 + 23*X^26 + 30*X^25 + 49*X^24 +
      22*X^23 + 18*X^22 + 8*X^21 + 65*X^20 + 38*X^19 + 55*X^18 + 61*X^17 + 30*X^16 + 28*X^15 +
      25*X^14 + 42*X^13 + 3*X^12 + 34*X^11 + 28*X^10 + 66*X^9 + 30*X^8 + 60*X^7 + 59*X^6 + 31*X^5 +
      49*X^4 + 19*X^3 + 19*X^2 + 14*X + 39) :=
  mul_step (by norm_num) pSeventeenB2s7 pSeventeenB21 ⟨
    49,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s9 : XPow fSeventeenB2 150
    (33*X^33 + 35*X^32 + 43*X^31 + 38*X^30 + 46*X^29 + 34*X^28 + 5*X^27 + 50*X^26 + 21*X^25 + 10*X^24 +
      57*X^23 + 2*X^22 + 52*X^21 + 5*X^20 + 13*X^19 + 5*X^18 + 11*X^17 + 23*X^16 + 32*X^15 + 27*X^14 +
      4*X^13 + 60*X^12 + 6*X^11 + 33*X^10 + 2*X^9 + 45*X^8 + 11*X^7 + 52*X^6 + 53*X^5 + 57*X^4 +
      40*X^3 + 5*X^2 + 11*X + 56) :=
  sq_step (by norm_num) pSeventeenB2s8 ⟨
    15*X^32 + 6*X^31 + 63*X^30 + 2*X^29 + 25*X^28 + 48*X^27 + 38*X^26 + 10*X^25 + 47*X^24 + X^23 +
      46*X^22 + 52*X^21 + 14*X^20 + 50*X^19 + 31*X^18 + 56*X^17 + 56*X^16 + 14*X^15 + 55*X^14 +
      36*X^13 + 33*X^12 + 2*X^11 + 64*X^10 + 43*X^9 + 33*X^8 + 65*X^7 + 49*X^6 + 31*X^5 + 12*X^4 +
      12*X^3 + 52*X^2 + 44*X + 1,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s10 : XPow fSeventeenB2 151
    (42*X^33 + 59*X^32 + 54*X^31 + 63*X^30 + 62*X^29 + 35*X^28 + 55*X^27 + 13*X^26 + 8*X^25 + 31*X^24 +
      31*X^23 + 10*X^22 + 30*X^21 + 46*X^20 + 24*X^19 + 41*X^18 + 26*X^17 + 50*X^16 + 31*X^15 +
      64*X^14 + 59*X^13 + 5*X^12 + 40*X^11 + 44*X^10 + 49*X^9 + 9*X^8 + 62*X^7 + 19*X^6 + 29*X^5 +
      28*X^4 + 52*X^3 + 44*X^2 + 24*X + 29) :=
  mul_step (by norm_num) pSeventeenB2s9 pSeventeenB21 ⟨
    33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s11 : XPow fSeventeenB2 302
    (15*X^33 + 24*X^32 + 38*X^31 + 37*X^30 + 27*X^29 + 44*X^28 + 55*X^27 + 15*X^26 + 8*X^25 + 9*X^24 +
      22*X^23 + 37*X^21 + 50*X^20 + 63*X^19 + 18*X^18 + 37*X^17 + 59*X^16 + 29*X^15 + 66*X^13 +
      28*X^12 + X^11 + 20*X^10 + 49*X^9 + 25*X^8 + 9*X^7 + 24*X^6 + 40*X^5 + 40*X^4 + 63*X^3 +
      47*X^2 + 35*X + 11) :=
  sq_step (by norm_num) pSeventeenB2s10 ⟨
    22*X^32 + 25*X^31 + 62*X^30 + 46*X^29 + 59*X^28 + 43*X^27 + 39*X^26 + 32*X^25 + 36*X^24 + 26*X^23 +
      61*X^22 + 14*X^21 + 6*X^20 + 61*X^19 + 63*X^18 + 53*X^17 + 36*X^16 + 65*X^15 + 11*X^14 +
      20*X^13 + 66*X^12 + 32*X^11 + 29*X^10 + 17*X^9 + 59*X^8 + 33*X^7 + 54*X^6 + 8*X^5 + 23*X^4 +
      51*X^3 + 64*X^2 + 17*X + 12,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s12 : XPow fSeventeenB2 303
    (15*X^33 + 27*X^32 + 26*X^31 + 53*X^30 + 8*X^29 + 26*X^28 + 66*X^27 + 47*X^26 + 2*X^25 + 65*X^24 +
      X^23 + 24*X^22 + 37*X^21 + 11*X^20 + 51*X^19 + 8*X^18 + 36*X^17 + 25*X^16 + 14*X^15 + 8*X^14 +
      58*X^13 + 31*X^12 + 11*X^11 + 62*X^10 + 39*X^9 + 2*X^8 + 59*X^7 + 55*X^6 + 9*X^5 + 21*X^4 +
      44*X^3 + 50*X^2 + 33*X + 1) :=
  mul_step (by norm_num) pSeventeenB2s11 pSeventeenB21 ⟨
    15,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s13 : XPow fSeventeenB2 606
    (15*X^33 + 48*X^32 + 30*X^31 + 17*X^30 + 56*X^29 + 58*X^28 + 25*X^27 + 49*X^26 + 24*X^25 + 36*X^24 +
      2*X^23 + 7*X^22 + 40*X^21 + 29*X^20 + 6*X^19 + 42*X^18 + 26*X^17 + 16*X^16 + 16*X^15 + 4*X^14 +
      23*X^13 + 46*X^12 + 14*X^11 + 31*X^10 + 42*X^9 + 50*X^8 + 13*X^7 + 11*X^6 + 2*X^5 + 12*X^4 +
      30*X^3 + 12*X^2 + 8*X + 4) :=
  sq_step (by norm_num) pSeventeenB2s12 ⟨
    24*X^32 + 5*X^31 + X^30 + 42*X^29 + 38*X^28 + 10*X^27 + 11*X^26 + 43*X^25 + 52*X^24 + 13*X^23 +
      29*X^22 + 4*X^21 + 3*X^20 + 52*X^19 + 30*X^18 + 6*X^17 + 60*X^16 + 10*X^15 + 34*X^14 + 54*X^13 +
      57*X^12 + 38*X^11 + 30*X^10 + 32*X^9 + 29*X^8 + 37*X^7 + 60*X^6 + 46*X^5 + 16*X^4 + 2*X^3 +
      11*X^2 + 16*X + 45,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s14 : XPow fSeventeenB2 607
    (39*X^33 + 19*X^32 + 6*X^31 + 15*X^30 + 22*X^29 + 63*X^28 + 33*X^27 + 63*X^26 + 29*X^25 + 45*X^24 +
      8*X^23 + 27*X^22 + 16*X^21 + 21*X^20 + 8*X^19 + 64*X^18 + 60*X^17 + 12*X^16 + 18*X^15 +
      32*X^14 + 9*X^13 + 44*X^12 + 22*X^11 + 55*X^10 + 64*X^9 + 6*X^8 + 46*X^7 + 17*X^6 + 48*X^5 +
      55*X^4 + 9*X^3 + 23*X^2 + 26*X + 1) :=
  mul_step (by norm_num) pSeventeenB2s13 pSeventeenB21 ⟨
    15,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s15 : XPow fSeventeenB2 1214
    (33*X^33 + 55*X^32 + 26*X^31 + 58*X^30 + 39*X^29 + 40*X^28 + 12*X^27 + 41*X^26 + 34*X^25 + 9*X^24 +
      3*X^23 + 38*X^22 + 14*X^21 + X^20 + 27*X^19 + 24*X^18 + 4*X^17 + 49*X^15 + 65*X^14 + 44*X^13 +
      62*X^12 + 22*X^11 + 39*X^9 + 66*X^8 + 16*X^7 + 10*X^6 + 51*X^5 + 40*X^4 + 62*X^3 + 54*X^2 +
      49*X + 19) :=
  sq_step (by norm_num) pSeventeenB2s14 ⟨
    47*X^32 + 20*X^31 + 50*X^30 + 28*X^29 + 35*X^28 + 34*X^27 + 5*X^26 + 18*X^25 + 50*X^24 + 25*X^23 +
      39*X^22 + 14*X^20 + 57*X^19 + 49*X^18 + 9*X^17 + 55*X^16 + 62*X^15 + 52*X^14 + 5*X^13 +
      57*X^12 + 16*X^11 + 64*X^10 + 16*X^9 + 36*X^8 + 31*X^7 + 18*X^6 + 6*X^5 + 6*X^4 + 12*X^3 +
      15*X^2 + 45*X + 2,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s16 : XPow fSeventeenB2 1215
    (62*X^33 + 42*X^32 + 7*X^31 + 56*X^30 + X^29 + 42*X^28 + 46*X^27 + 26*X^26 + 7*X^25 + 44*X^24 +
      39*X^22 + 26*X^21 + 60*X^20 + 43*X^19 + 34*X^18 + 3*X^17 + 2*X^15 + 37*X^14 + 61*X^13 +
      21*X^12 + 7*X^11 + 14*X^10 + 3*X^9 + 14*X^8 + 20*X^7 + 17*X^6 + 12*X^5 + 50*X^4 + 34*X^3 +
      15*X^2 + 54*X + 29) :=
  mul_step (by norm_num) pSeventeenB2s15 pSeventeenB21 ⟨
    33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s17 : XPow fSeventeenB2 2430
    (23*X^33 + 58*X^32 + 64*X^31 + 19*X^30 + 16*X^29 + 59*X^28 + 40*X^27 + 10*X^26 + 14*X^25 + 5*X^24 +
      63*X^23 + 9*X^22 + 64*X^20 + 5*X^19 + 30*X^18 + 44*X^17 + 12*X^16 + 46*X^15 + 9*X^14 + 51*X^13 +
      61*X^12 + 39*X^11 + 38*X^10 + 26*X^9 + 32*X^8 + 44*X^7 + 40*X^6 + 11*X^5 + 64*X^4 + 27*X^3 +
      52*X^2 + 24*X + 28) :=
  sq_step (by norm_num) pSeventeenB2s16 ⟨
    25*X^32 + 34*X^31 + 16*X^30 + 60*X^29 + 46*X^28 + 42*X^27 + 32*X^26 + 35*X^25 + 54*X^24 + 16*X^23 +
      47*X^22 + 21*X^21 + 53*X^20 + 8*X^19 + 30*X^18 + 52*X^17 + 34*X^15 + 34*X^14 + 25*X^13 +
      16*X^12 + 60*X^11 + 49*X^10 + 46*X^9 + 16*X^8 + 11*X^7 + 55*X^6 + 56*X^5 + 61*X^4 + 16*X^3 +
      6*X^2 + 34*X + 66,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s18 : XPow fSeventeenB2 4860
    (31*X^33 + 15*X^32 + 46*X^31 + 62*X^30 + 16*X^29 + 43*X^28 + 2*X^27 + 8*X^26 + 39*X^25 + 31*X^24 +
      61*X^23 + 51*X^22 + 15*X^21 + 50*X^20 + 47*X^19 + 46*X^18 + 57*X^17 + 19*X^16 + 52*X^15 +
      48*X^14 + X^13 + 51*X^12 + 36*X^11 + 61*X^10 + 34*X^9 + 38*X^8 + 37*X^7 + 9*X^6 + 11*X^5 +
      17*X^4 + 7*X^3 + 23*X^2 + 27*X + 18) :=
  sq_step (by norm_num) pSeventeenB2s17 ⟨
    60*X^32 + 19*X^31 + 35*X^30 + 54*X^29 + 33*X^28 + 21*X^27 + 17*X^26 + 63*X^25 + 39*X^24 + 39*X^23 +
      53*X^22 + 35*X^21 + 63*X^20 + 64*X^19 + 15*X^18 + 64*X^17 + 4*X^16 + 61*X^15 + 60*X^14 +
      11*X^13 + 9*X^11 + 17*X^10 + 66*X^9 + 26*X^8 + 40*X^7 + 2*X^6 + 46*X^5 + 11*X^4 + 44*X^3 +
      65*X^2 + 66*X + 34,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s19 : XPow fSeventeenB2 9720
    (10*X^33 + 13*X^32 + 26*X^31 + 27*X^30 + 33*X^29 + 7*X^28 + 54*X^27 + 65*X^26 + 51*X^25 + 8*X^24 +
      32*X^23 + 63*X^22 + 28*X^21 + 63*X^20 + 64*X^19 + 40*X^18 + 45*X^17 + 56*X^16 + 8*X^15 +
      44*X^14 + 24*X^13 + 2*X^12 + 4*X^11 + 48*X^10 + 52*X^9 + 41*X^8 + 42*X^7 + 46*X^6 + 45*X^5 +
      66*X^4 + 8*X^3 + 47*X^2 + 19*X + 6) :=
  sq_step (by norm_num) pSeventeenB2s18 ⟨
    23*X^32 + 5*X^31 + 60*X^30 + 4*X^29 + 40*X^28 + 27*X^27 + 38*X^26 + 62*X^25 + 13*X^24 + 53*X^23 +
      37*X^22 + 35*X^21 + 60*X^20 + 32*X^19 + 10*X^18 + 27*X^17 + 60*X^16 + 52*X^15 + 40*X^14 +
      40*X^13 + 32*X^12 + 66*X^11 + 52*X^10 + 17*X^9 + 20*X^8 + 14*X^7 + 32*X^6 + 10*X^5 + 43*X^4 +
      X^3 + 55*X^2 + 61*X + 54,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s20 : XPow fSeventeenB2 9721
    (7*X^33 + 41*X^32 + 42*X^31 + 28*X^30 + 50*X^29 + 57*X^28 + 32*X^27 + 10*X^26 + 48*X^25 + 16*X^24 +
      19*X^23 + 64*X^22 + 32*X^21 + 7*X^20 + 62*X^19 + 48*X^18 + 63*X^17 + 50*X^16 + 31*X^15 +
      30*X^14 + 22*X^13 + 24*X^12 + 42*X^11 + 16*X^10 + 28*X^9 + 15*X^8 + 47*X^7 + 55*X^6 + 23*X^5 +
      47*X^4 + 45*X^3 + 29*X^2 + 43*X + 23) :=
  mul_step (by norm_num) pSeventeenB2s19 pSeventeenB21 ⟨
    10,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s21 : XPow fSeventeenB2 19442
    (25*X^33 + 49*X^32 + 66*X^31 + 20*X^30 + 60*X^29 + 56*X^28 + 37*X^27 + 6*X^26 + 17*X^25 + 5*X^24 +
      7*X^23 + 37*X^22 + 19*X^21 + 23*X^20 + 41*X^19 + 53*X^18 + 16*X^17 + 54*X^16 + 57*X^15 +
      58*X^14 + 34*X^13 + 54*X^12 + 2*X^11 + 48*X^10 + 50*X^9 + 8*X^8 + 13*X^7 + 6*X^6 + 6*X^5 +
      32*X^4 + 55*X^3 + 8*X^2 + 5*X + 6) :=
  sq_step (by norm_num) pSeventeenB2s20 ⟨
    49*X^32 + 22*X^31 + 58*X^30 + 15*X^29 + 56*X^28 + 35*X^27 + 61*X^26 + 13*X^25 + 20*X^24 + 30*X^23 +
      61*X^22 + 65*X^21 + 61*X^20 + 26*X^19 + 49*X^18 + 52*X^17 + 34*X^16 + 21*X^15 + 42*X^14 +
      20*X^13 + 17*X^12 + 42*X^11 + 36*X^10 + 30*X^9 + 27*X^8 + 23*X^7 + 17*X^6 + 47*X^5 + 39*X^4 +
      51*X^3 + 63*X^2 + 17*X + 61,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s22 : XPow fSeventeenB2 19443
    (34*X^33 + 3*X^32 + 24*X^31 + 14*X^30 + 63*X^29 + 11*X^28 + 24*X^27 + 15*X^26 + 38*X^25 + 34*X^24 +
      61*X^23 + 42*X^22 + 46*X^21 + 66*X^20 + 41*X^19 + 57*X^18 + 38*X^17 + 28*X^16 + 59*X^15 +
      49*X^14 + 37*X^13 + 52*X^12 + 33*X^11 + 27*X^10 + 9*X^9 + 46*X^8 + 42*X^7 + 31*X^6 + 25*X^5 +
      52*X^4 + 3*X^3 + 30*X^2 + 65*X + 24) :=
  mul_step (by norm_num) pSeventeenB2s21 pSeventeenB21 ⟨
    25,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s23 : XPow fSeventeenB2 38886
    (65*X^33 + 56*X^32 + 35*X^31 + 48*X^30 + 63*X^29 + 8*X^28 + 52*X^27 + 12*X^26 + 8*X^25 + 7*X^24 +
      32*X^23 + 47*X^22 + 59*X^21 + 25*X^20 + X^19 + 15*X^18 + 46*X^17 + 31*X^16 + 21*X^15 + 4*X^14 +
      28*X^13 + 37*X^12 + 35*X^11 + 51*X^10 + 4*X^9 + 65*X^8 + 37*X^7 + 2*X^6 + 38*X^5 + 12*X^4 +
      10*X^3 + 47*X^2 + 7*X + 11) :=
  sq_step (by norm_num) pSeventeenB2s22 ⟨
    17*X^32 + 33*X^31 + 32*X^30 + 53*X^29 + 3*X^28 + 44*X^27 + 28*X^26 + 37*X^25 + 32*X^24 + 31*X^23 +
      12*X^22 + 17*X^21 + 61*X^20 + 18*X^19 + 54*X^18 + 46*X^17 + 7*X^16 + 61*X^15 + 52*X^14 +
      33*X^13 + 31*X^12 + 61*X^11 + X^10 + 42*X^9 + 53*X^8 + 54*X^7 + 50*X^6 + 65*X^5 + 4*X^4 +
      40*X^3 + 62*X^2 + 60*X + 34,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s24 : XPow fSeventeenB2 38887
    (17*X^33 + 32*X^32 + 45*X^31 + 64*X^30 + 53*X^29 + 38*X^28 + 32*X^27 + 43*X^26 + 66*X^25 + 62*X^24 +
      29*X^23 + 25*X^22 + 58*X^21 + 66*X^20 + 24*X^19 + 32*X^18 + 43*X^17 + 26*X^16 + 20*X^15 +
      33*X^13 + 31*X^12 + 12*X^11 + 38*X^10 + 14*X^9 + 29*X^8 + 42*X^7 + 36*X^6 + 34*X^5 + 29*X^4 +
      34*X^3 + 5*X^2 + 17*X + 49) :=
  mul_step (by norm_num) pSeventeenB2s23 pSeventeenB21 ⟨
    65,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s25 : XPow fSeventeenB2 77774
    (12*X^33 + 59*X^32 + 21*X^31 + 3*X^30 + 27*X^29 + 59*X^28 + 53*X^27 + 35*X^26 + 58*X^25 + 6*X^24 +
      49*X^23 + 9*X^22 + 65*X^21 + 12*X^20 + 37*X^19 + 45*X^18 + 28*X^17 + 45*X^16 + 59*X^15 +
      8*X^14 + 35*X^13 + 35*X^12 + 23*X^11 + 24*X^10 + 47*X^9 + 27*X^8 + 60*X^7 + 58*X^6 + 65*X^5 +
      62*X^4 + 5*X^3 + 59*X^2 + 38*X + 27) :=
  sq_step (by norm_num) pSeventeenB2s24 ⟨
    21*X^32 + 57*X^31 + 12*X^30 + 47*X^29 + 55*X^28 + 49*X^27 + 25*X^26 + 49*X^25 + 4*X^24 + 33*X^23 +
      25*X^22 + 23*X^21 + 16*X^20 + 54*X^19 + 26*X^18 + 64*X^17 + 46*X^16 + 49*X^15 + 19*X^14 +
      20*X^13 + 16*X^12 + 22*X^11 + 65*X^10 + 20*X^9 + 18*X^8 + 25*X^7 + 3*X^6 + 49*X^5 + 23*X^4 +
      23*X^3 + 21*X^2 + 24*X + 34,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s26 : XPow fSeventeenB2 77775
    (25*X^33 + 39*X^32 + 21*X^31 + 21*X^30 + 57*X^29 + 3*X^28 + 49*X^27 + 49*X^26 + 54*X^25 + 3*X^24 +
      50*X^23 + X^22 + 15*X^21 + 49*X^20 + 58*X^19 + 45*X^18 + 40*X^17 + 29*X^16 + 46*X^15 + 2*X^14 +
      59*X^13 + 47*X^12 + 57*X^11 + 44*X^10 + 65*X^9 + 41*X^8 + 19*X^7 + 10*X^6 + 64*X^5 + 25*X^4 +
      3*X^3 + 50*X^2 + 58*X + 41) :=
  mul_step (by norm_num) pSeventeenB2s25 pSeventeenB21 ⟨
    12,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s27 : XPow fSeventeenB2 155550
    (22*X^33 + 57*X^32 + 61*X^31 + 30*X^30 + 49*X^29 + 61*X^28 + 57*X^27 + 52*X^25 + 8*X^24 + 27*X^23 +
      61*X^22 + 32*X^21 + 43*X^20 + 21*X^19 + 11*X^18 + 62*X^17 + 8*X^16 + 16*X^15 + 11*X^14 +
      26*X^13 + 40*X^12 + 6*X^11 + 19*X^10 + 63*X^9 + 11*X^8 + 2*X^7 + 32*X^6 + 36*X^5 + 30*X^4 +
      49*X^3 + 10*X^2 + 31*X + 35) :=
  sq_step (by norm_num) pSeventeenB2s26 ⟨
    22*X^32 + 34*X^31 + 51*X^30 + 48*X^29 + 52*X^28 + 65*X^27 + 2*X^26 + 14*X^25 + 34*X^24 + 19*X^23 +
      13*X^22 + 35*X^21 + 44*X^20 + 36*X^19 + 21*X^18 + 34*X^17 + 65*X^16 + 34*X^15 + 23*X^14 +
      40*X^13 + 16*X^12 + 22*X^11 + 7*X^9 + 43*X^8 + 39*X^7 + 17*X^6 + 37*X^5 + 9*X^4 + 9*X^3 +
      39*X^2 + 22*X + 33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s28 : XPow fSeventeenB2 155551
    (17*X^33 + 27*X^32 + 63*X^31 + 38*X^30 + 35*X^29 + 10*X^28 + 48*X^27 + 2*X^26 + 29*X^25 + 32*X^24 +
      58*X^23 + 4*X^22 + 15*X^21 + 43*X^20 + 46*X^19 + 15*X^18 + 10*X^17 + 28*X^16 + 36*X^15 +
      66*X^14 + 17*X^13 + 50*X^12 + 46*X^11 + 24*X^10 + 36*X^9 + 23*X^8 + 61*X^7 + 58*X^6 + 56*X^5 +
      41*X^4 + 19*X^3 + 53*X^2 + 36*X + 64) :=
  mul_step (by norm_num) pSeventeenB2s27 pSeventeenB21 ⟨
    22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s29 : XPow fSeventeenB2 311102
    (34*X^32 + 42*X^31 + 37*X^30 + 50*X^29 + 24*X^28 + 22*X^27 + 18*X^26 + 13*X^25 + 56*X^24 + 60*X^23 +
      X^22 + 60*X^21 + 14*X^20 + 15*X^19 + 49*X^18 + 31*X^17 + 36*X^16 + 43*X^15 + 32*X^14 + 24*X^13 +
      31*X^12 + 39*X^11 + 14*X^10 + 4*X^9 + 9*X^8 + 60*X^7 + 22*X^6 + 56*X^5 + 65*X^4 + 46*X^3 +
      2*X^2 + 5*X + 20) :=
  sq_step (by norm_num) pSeventeenB2s28 ⟨
    21*X^32 + 21*X^31 + 29*X^30 + 63*X^29 + 62*X^28 + 43*X^27 + 2*X^26 + 33*X^25 + 42*X^24 + 44*X^23 +
      17*X^22 + 24*X^21 + 31*X^20 + 17*X^19 + 25*X^18 + 59*X^17 + 45*X^16 + 14*X^15 + 9*X^14 +
      42*X^13 + 41*X^12 + 28*X^11 + 27*X^10 + 45*X^9 + 24*X^8 + 31*X^7 + 56*X^6 + 10*X^5 + 63*X^4 +
      49*X^3 + 66*X^2 + 20*X + 31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s30 : XPow fSeventeenB2 622204
    (55*X^33 + 24*X^32 + 27*X^31 + 38*X^30 + 63*X^29 + 26*X^28 + 40*X^27 + 21*X^26 + 55*X^25 + 53*X^24 +
      56*X^23 + 13*X^22 + 30*X^21 + 49*X^20 + 14*X^19 + 58*X^18 + 26*X^17 + 59*X^16 + 42*X^15 +
      56*X^14 + 26*X^13 + 28*X^12 + 42*X^11 + 57*X^10 + 48*X^9 + 12*X^8 + 55*X^7 + 50*X^6 + 9*X^5 +
      39*X^4 + 4*X^3 + 56*X^2 + 15*X + 11) :=
  sq_step (by norm_num) pSeventeenB2s29 ⟨
    17*X^30 + 5*X^29 + 48*X^28 + 40*X^27 + 12*X^26 + 24*X^25 + 4*X^24 + 28*X^23 + 2*X^22 + 27*X^21 +
      53*X^20 + 64*X^19 + 61*X^18 + 9*X^17 + 3*X^16 + 39*X^15 + 32*X^14 + 56*X^13 + 24*X^12 +
      45*X^11 + 55*X^10 + 43*X^9 + 53*X^8 + 60*X^7 + 2*X^6 + 22*X^5 + 20*X^4 + 15*X^2 + 37*X + 61,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s31 : XPow fSeventeenB2 622205
    (58*X^33 + 9*X^32 + 20*X^31 + 2*X^30 + 28*X^29 + 23*X^28 + 7*X^27 + 64*X^26 + 5*X^25 + 35*X^24 +
      39*X^23 + 27*X^22 + 46*X^21 + 2*X^20 + 45*X^19 + 9*X^18 + 64*X^17 + 5*X^16 + 18*X^15 + 59*X^14 +
      4*X^13 + 18*X^12 + 24*X^11 + 51*X^10 + 41*X^9 + 7*X^8 + 22*X^7 + 64*X^6 + 37*X^5 + 51*X^4 +
      45*X^3 + 3*X^2 + 47*X + 26) :=
  mul_step (by norm_num) pSeventeenB2s30 pSeventeenB21 ⟨
    55,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s32 : XPow fSeventeenB2 1244410
    (41*X^33 + 18*X^32 + 6*X^31 + 54*X^30 + 39*X^29 + 11*X^28 + 51*X^26 + 53*X^25 + 12*X^24 + 44*X^23 +
      18*X^22 + 27*X^21 + 64*X^20 + 66*X^19 + 54*X^18 + 57*X^17 + 51*X^16 + 57*X^15 + 55*X^14 +
      34*X^13 + 44*X^12 + 6*X^11 + 10*X^10 + 65*X^9 + 37*X^8 + 33*X^7 + 12*X^6 + 37*X^5 + 56*X^4 +
      34*X^3 + 30*X^2 + 36*X + 17) :=
  sq_step (by norm_num) pSeventeenB2s31 ⟨
    14*X^32 + 44*X^31 + 64*X^30 + 51*X^29 + 43*X^28 + 40*X^27 + 2*X^26 + 11*X^25 + 51*X^24 + 54*X^23 +
      53*X^22 + 2*X^21 + 14*X^20 + 65*X^19 + 31*X^18 + 53*X^17 + 29*X^16 + 39*X^15 + 58*X^14 +
      52*X^13 + 64*X^12 + 58*X^11 + 52*X^10 + 13*X^9 + 7*X^8 + 14*X^7 + 25*X^6 + 19*X^5 + 7*X^4 +
      28*X^3 + 36*X^2 + 48*X + 31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s33 : XPow fSeventeenB2 1244411
    (47*X^33 + 34*X^32 + 15*X^31 + 52*X^30 + 60*X^29 + 19*X^28 + 43*X^27 + 39*X^26 + 42*X^25 + 32*X^24 +
      52*X^23 + 54*X^22 + 24*X^21 + 40*X^20 + 37*X^19 + 9*X^18 + 6*X^17 + 55*X^16 + 62*X^15 + 5*X^14 +
      59*X^13 + 21*X^12 + 39*X^11 + 38*X^10 + 44*X^9 + 63*X^8 + 63*X^7 + 11*X^6 + 7*X^5 + 13*X^4 +
      62*X^3 + 10*X^2 + 28*X + 34) :=
  mul_step (by norm_num) pSeventeenB2s32 pSeventeenB21 ⟨
    41,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s34 : XPow fSeventeenB2 2488822
    (38*X^33 + 52*X^32 + 58*X^31 + 41*X^30 + 41*X^29 + 16*X^28 + 64*X^27 + 44*X^26 + 64*X^25 + 38*X^24 +
      15*X^23 + 17*X^22 + 23*X^21 + 21*X^20 + 23*X^19 + 49*X^18 + 23*X^17 + 39*X^16 + 10*X^15 +
      31*X^14 + 63*X^13 + 5*X^11 + 20*X^10 + 58*X^9 + 45*X^8 + 45*X^7 + 5*X^6 + 21*X^5 + 25*X^4 +
      6*X^3 + 38*X^2 + 20*X + 4) :=
  sq_step (by norm_num) pSeventeenB2s33 ⟨
    65*X^32 + 8*X^31 + 39*X^30 + 11*X^29 + 39*X^28 + 28*X^27 + 28*X^26 + 7*X^25 + 13*X^24 + 43*X^23 +
      47*X^22 + 52*X^21 + 42*X^20 + 46*X^19 + 66*X^18 + 56*X^17 + 14*X^16 + X^15 + 28*X^14 + 47*X^13 +
      9*X^12 + 28*X^11 + 6*X^10 + 34*X^9 + 51*X^8 + 63*X^7 + 2*X^6 + 58*X^5 + 26*X^4 + 33*X^3 +
      10*X^2 + 16*X + 6,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s35 : XPow fSeventeenB2 2488823
    (56*X^33 + 48*X^32 + 31*X^31 + 22*X^30 + 32*X^29 + 62*X^28 + 66*X^27 + 2*X^26 + 56*X^25 + 48*X^24 +
      24*X^23 + 66*X^22 + 64*X^21 + 61*X^20 + 12*X^19 + 21*X^18 + 12*X^17 + 49*X^16 + 62*X^15 +
      59*X^14 + 9*X^13 + 14*X^12 + 24*X^11 + 15*X^10 + 9*X^9 + 63*X^8 + 49*X^7 + 59*X^6 + 9*X^5 +
      47*X^4 + 17*X^3 + 58*X^2 + 24*X + 7) :=
  mul_step (by norm_num) pSeventeenB2s34 pSeventeenB21 ⟨
    38,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s36 : XPow fSeventeenB2 4977646
    (X^33 + 42*X^32 + 30*X^31 + 43*X^30 + 26*X^29 + 37*X^28 + 52*X^27 + 20*X^26 + 16*X^25 + 29*X^24 +
      35*X^23 + 17*X^22 + 26*X^21 + 39*X^20 + 36*X^19 + 55*X^18 + 49*X^17 + 16*X^16 + 11*X^15 +
      56*X^14 + 57*X^13 + 8*X^12 + 48*X^11 + 64*X^10 + 35*X^9 + 6*X^8 + 9*X^7 + 14*X^6 + 3*X^5 +
      61*X^4 + 19*X^3 + 18*X^2 + 59*X + 27) :=
  sq_step (by norm_num) pSeventeenB2s35 ⟨
    54*X^32 + 64*X^31 + 3*X^30 + 14*X^29 + 2*X^28 + 47*X^27 + 11*X^26 + 41*X^25 + 15*X^24 + 62*X^23 +
      30*X^22 + 66*X^21 + 64*X^20 + 61*X^19 + 28*X^18 + 7*X^17 + 10*X^16 + 53*X^15 + 32*X^14 +
      38*X^13 + 53*X^12 + 57*X^11 + 51*X^9 + 66*X^8 + 59*X^7 + 43*X^6 + 20*X^5 + 63*X^4 + 20*X^3 +
      41*X^2 + 23*X + 5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s37 : XPow fSeventeenB2 9955292
    (33*X^33 + 57*X^32 + 26*X^31 + 45*X^30 + 14*X^29 + 39*X^27 + 2*X^26 + 56*X^25 + 12*X^24 + 27*X^23 +
      34*X^22 + 24*X^21 + 31*X^20 + 12*X^19 + 9*X^18 + 42*X^17 + 2*X^16 + 47*X^15 + 12*X^14 +
      48*X^13 + 39*X^12 + 10*X^11 + 28*X^10 + X^9 + X^8 + 60*X^7 + 16*X^6 + 22*X^5 + 24*X^4 + 52*X^3 +
      25*X^2 + 47*X + 66) :=
  sq_step (by norm_num) pSeventeenB2s36 ⟨
    X^32 + 3*X^31 + 8*X^30 + 21*X^29 + 65*X^28 + 28*X^27 + 29*X^26 + 43*X^25 + 39*X^24 + 29*X^22 +
      19*X^21 + 31*X^20 + 17*X^19 + 17*X^18 + 41*X^17 + 16*X^16 + 51*X^15 + 58*X^14 + 47*X^13 +
      33*X^12 + 59*X^11 + 66*X^9 + 63*X^8 + 54*X^7 + 37*X^6 + 64*X^5 + 7*X^4 + 56*X^3 + 27*X^2 +
      51*X + 38,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s38 : XPow fSeventeenB2 9955293
    (64*X^33 + 42*X^32 + 61*X^31 + 31*X^30 + 28*X^29 + 2*X^28 + 7*X^27 + 48*X^26 + 10*X^25 + X^24 +
      63*X^23 + 49*X^22 + 56*X^21 + 45*X^20 + 28*X^19 + 5*X^18 + 5*X^17 + 65*X^16 + 16*X^15 +
      41*X^14 + 38*X^13 + 9*X^12 + 35*X^11 + 43*X^10 + 5*X^9 + 58*X^8 + 26*X^7 + 55*X^6 + 63*X^5 +
      40*X^4 + 5*X^3 + 13*X^2 + 34*X + 29) :=
  mul_step (by norm_num) pSeventeenB2s37 pSeventeenB21 ⟨
    33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s39 : XPow fSeventeenB2 19910586
    (12*X^33 + 18*X^32 + 5*X^31 + 34*X^30 + 54*X^29 + 27*X^28 + 33*X^27 + 46*X^26 + 50*X^25 + 9*X^24 +
      43*X^23 + 46*X^22 + 41*X^21 + 22*X^20 + 52*X^19 + 14*X^18 + 12*X^17 + 6*X^16 + 26*X^15 +
      34*X^14 + 7*X^13 + 23*X^12 + 12*X^11 + 43*X^10 + 24*X^9 + 35*X^8 + 33*X^7 + 35*X^6 + 42*X^5 +
      13*X^4 + 16*X^3 + 58*X^2 + 33*X + 47) :=
  sq_step (by norm_num) pSeventeenB2s38 ⟨
    9*X^32 + 24*X^31 + 37*X^30 + 14*X^29 + 18*X^28 + 37*X^27 + 20*X^26 + 48*X^25 + 62*X^24 + 64*X^23 +
      14*X^22 + 40*X^21 + 50*X^20 + 52*X^19 + 49*X^18 + 9*X^17 + 28*X^16 + 26*X^15 + 56*X^14 +
      33*X^13 + 57*X^12 + 15*X^11 + 36*X^10 + 13*X^9 + 34*X^8 + 16*X^7 + 5*X^6 + 9*X^5 + 8*X^4 +
      4*X^3 + 45*X^2 + 43*X + 16,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s40 : XPow fSeventeenB2 19910587
    (51*X^33 + 23*X^32 + 52*X^31 + 48*X^30 + 25*X^29 + 50*X^28 + 60*X^27 + 41*X^26 + 57*X^25 + 64*X^24 +
      20*X^23 + 44*X^22 + 25*X^21 + 64*X^20 + 27*X^19 + 29*X^18 + X^17 + 63*X^16 + 5*X^15 + 41*X^14 +
      47*X^13 + 36*X^12 + 9*X^11 + 21*X^10 + 6*X^9 + 14*X^8 + 63*X^7 + 54*X^6 + 15*X^5 + 36*X^4 +
      2*X^3 + 45*X^2 + 11*X + 41) :=
  mul_step (by norm_num) pSeventeenB2s39 pSeventeenB21 ⟨
    12,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s41 : XPow fSeventeenB2 39821174
    (17*X^33 + 36*X^32 + 25*X^31 + 20*X^30 + 27*X^29 + 21*X^28 + 55*X^27 + 12*X^26 + 5*X^25 + 38*X^24 +
      45*X^23 + 2*X^22 + 65*X^21 + 32*X^20 + 52*X^19 + 55*X^18 + 39*X^17 + 59*X^16 + 55*X^15 +
      39*X^14 + 41*X^13 + 45*X^12 + 51*X^11 + 44*X^10 + 12*X^9 + 60*X^8 + 64*X^7 + 30*X^6 + 59*X^5 +
      56*X^4 + 51*X^3 + 2*X^2 + 38*X + 32) :=
  sq_step (by norm_num) pSeventeenB2s40 ⟨
    55*X^32 + 35*X^31 + 32*X^30 + 7*X^29 + 29*X^27 + 48*X^26 + 21*X^25 + 18*X^24 + 44*X^23 + 44*X^22 +
      31*X^21 + 59*X^20 + 55*X^19 + 43*X^18 + 34*X^17 + 9*X^16 + 48*X^15 + 51*X^14 + 14*X^13 +
      51*X^12 + 47*X^11 + 23*X^10 + 57*X^9 + 27*X^8 + 24*X^7 + 25*X^6 + 63*X^5 + 27*X^4 + 11*X^3 +
      51*X^2 + 34*X + 55,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s42 : XPow fSeventeenB2 39821175
    (66*X^33 + 17*X^32 + 12*X^31 + 52*X^30 + 7*X^29 + 40*X^28 + 43*X^27 + 9*X^26 + 39*X^25 + 58*X^24 +
      21*X^23 + 19*X^22 + 53*X^21 + 2*X^20 + 12*X^19 + 24*X^18 + 24*X^17 + 46*X^16 + 37*X^15 +
      11*X^14 + 12*X^13 + 18*X^12 + 7*X^11 + 58*X^10 + 58*X^9 + 65*X^8 + 25*X^7 + 9*X^6 + 3*X^5 +
      57*X^4 + 12*X^3 + 55*X^2 + 48*X + 19) :=
  mul_step (by norm_num) pSeventeenB2s41 pSeventeenB21 ⟨
    17,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s43 : XPow fSeventeenB2 79642350
    (38*X^33 + 45*X^32 + 61*X^31 + 17*X^30 + 46*X^29 + 41*X^28 + 32*X^27 + 63*X^26 + 58*X^25 + 49*X^24 +
      64*X^23 + 34*X^22 + 9*X^21 + 47*X^20 + 62*X^19 + 57*X^18 + 36*X^17 + 25*X^16 + 22*X^15 +
      57*X^14 + 33*X^13 + 63*X^12 + 51*X^11 + 19*X^10 + 59*X^9 + 47*X^8 + 28*X^7 + 38*X^6 + 36*X^5 +
      38*X^4 + 18*X^3 + 62*X^2 + 54*X + 47) :=
  sq_step (by norm_num) pSeventeenB2s42 ⟨
    X^32 + 19*X^31 + 34*X^30 + 59*X^29 + 12*X^28 + 39*X^27 + 53*X^26 + 53*X^25 + 11*X^24 + 22*X^23 +
      29*X^22 + 60*X^21 + 42*X^20 + 62*X^19 + 13*X^18 + 62*X^17 + 26*X^16 + 2*X^14 + 62*X^13 +
      32*X^12 + 60*X^11 + 2*X^10 + 43*X^9 + 51*X^8 + 15*X^7 + 36*X^6 + 47*X^5 + 19*X^4 + 11*X^3 +
      4*X^2 + 20*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s44 : XPow fSeventeenB2 79642351
    (49*X^33 + 51*X^32 + 7*X^31 + 27*X^30 + 57*X^29 + 30*X^28 + 18*X^27 + 63*X^26 + 30*X^24 + 41*X^23 +
      52*X^22 + 23*X^21 + 33*X^20 + 20*X^19 + 34*X^18 + 65*X^17 + 61*X^16 + 21*X^15 + 29*X^14 +
      5*X^13 + 60*X^12 + 23*X^11 + 16*X^10 + 11*X^9 + 46*X^8 + 15*X^7 + 7*X^6 + 22*X^5 + 59*X^4 +
      41*X^3 + 25*X^2 + 7) :=
  mul_step (by norm_num) pSeventeenB2s43 pSeventeenB21 ⟨
    38,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s45 : XPow fSeventeenB2 159284702
    (47*X^33 + 34*X^32 + 3*X^31 + 8*X^30 + 48*X^29 + 44*X^28 + 61*X^27 + 56*X^26 + 41*X^25 + 36*X^23 +
      49*X^22 + 41*X^21 + 29*X^20 + 63*X^19 + 7*X^18 + 38*X^17 + 4*X^16 + 13*X^15 + 32*X^14 +
      15*X^13 + 28*X^12 + 49*X^11 + 17*X^10 + 30*X^9 + 21*X^8 + 23*X^7 + 19*X^6 + 20*X^5 + 2*X^3 +
      15*X^2 + 6*X + 46) :=
  sq_step (by norm_num) pSeventeenB2s44 ⟨
    56*X^32 + 60*X^31 + 52*X^30 + 59*X^29 + 65*X^28 + 30*X^27 + 41*X^26 + 22*X^25 + 26*X^24 + 40*X^23 +
      51*X^22 + 11*X^21 + 63*X^20 + 48*X^19 + 2*X^18 + 40*X^17 + 10*X^16 + 57*X^14 + 20*X^13 +
      13*X^12 + 37*X^11 + X^10 + 31*X^9 + 4*X^8 + 36*X^7 + 16*X^6 + 20*X^5 + 23*X^4 + 19*X^3 +
      30*X^2 + 8*X + 22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s46 : XPow fSeventeenB2 318569404
    (15*X^33 + 18*X^32 + 37*X^31 + 58*X^30 + 37*X^29 + 52*X^28 + 6*X^27 + 29*X^26 + 46*X^25 + 3*X^24 +
      28*X^23 + 35*X^22 + 6*X^21 + 59*X^20 + 34*X^19 + 63*X^18 + 40*X^17 + 36*X^16 + 4*X^15 +
      26*X^14 + 34*X^13 + 51*X^12 + 29*X^11 + 61*X^10 + 21*X^9 + 44*X^8 + 65*X^7 + 44*X^6 + 21*X^5 +
      X^4 + 23*X^3 + 40*X^2 + 31*X + 65) :=
  sq_step (by norm_num) pSeventeenB2s45 ⟨
    65*X^32 + 8*X^31 + 50*X^30 + 64*X^29 + 36*X^28 + 54*X^27 + 12*X^26 + 17*X^25 + 29*X^24 + 57*X^23 +
      55*X^22 + 46*X^21 + 18*X^20 + 59*X^19 + 40*X^18 + 4*X^17 + 10*X^16 + 51*X^15 + 21*X^14 +
      27*X^13 + 22*X^12 + 14*X^11 + 17*X^10 + 29*X^9 + 47*X^8 + 35*X^7 + 56*X^6 + 32*X^5 + 49*X^4 +
      22*X^3 + 4*X^2 + 20*X + 55,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s47 : XPow fSeventeenB2 637138808
    (64*X^33 + 23*X^32 + 24*X^31 + 63*X^30 + X^29 + 46*X^28 + 55*X^27 + 2*X^26 + 11*X^25 + 59*X^24 +
      50*X^23 + 33*X^22 + 65*X^21 + 54*X^20 + 24*X^19 + 35*X^18 + 62*X^17 + 22*X^16 + 19*X^15 +
      34*X^14 + 41*X^13 + 64*X^12 + 33*X^11 + 25*X^10 + 12*X^9 + 51*X^8 + 3*X^7 + 13*X^6 + 41*X^5 +
      9*X^4 + 50*X^3 + 30*X^2 + 51*X + 50) :=
  sq_step (by norm_num) pSeventeenB2s46 ⟨
    24*X^32 + 3*X^31 + 21*X^30 + 38*X^29 + 39*X^28 + 21*X^27 + 59*X^26 + 41*X^25 + 28*X^24 + 2*X^23 +
      34*X^22 + 48*X^21 + 45*X^20 + 46*X^19 + 36*X^18 + 2*X^17 + 49*X^16 + 47*X^15 + 64*X^14 +
      16*X^13 + 63*X^12 + 10*X^11 + 31*X^10 + 60*X^9 + 55*X^8 + 23*X^7 + 49*X^6 + 11*X^5 + 39*X^4 +
      29*X^3 + 30*X^2 + 41*X + 20,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s48 : XPow fSeventeenB2 1274277616
    (28*X^33 + 38*X^32 + 33*X^31 + 13*X^30 + 25*X^29 + 14*X^28 + 4*X^27 + 28*X^26 + 41*X^25 + 63*X^24 +
      8*X^23 + 24*X^22 + 44*X^21 + 56*X^20 + 41*X^19 + 16*X^18 + 39*X^17 + 35*X^16 + 50*X^15 +
      51*X^14 + 36*X^13 + 43*X^12 + 28*X^11 + 30*X^10 + 33*X^9 + 36*X^7 + 28*X^6 + 6*X^5 + 46*X^4 +
      40*X^3 + 37*X + 31) :=
  sq_step (by norm_num) pSeventeenB2s47 ⟨
    9*X^32 + 4*X^31 + 41*X^30 + 4*X^29 + 58*X^28 + 36*X^27 + 18*X^26 + 36*X^25 + 4*X^24 + 62*X^23 +
      6*X^22 + 43*X^21 + 33*X^20 + 37*X^19 + 59*X^18 + 33*X^17 + 51*X^16 + 35*X^15 + 51*X^14 +
      6*X^13 + 22*X^12 + 52*X^11 + 53*X^10 + 31*X^9 + 38*X^8 + 23*X^7 + 47*X^6 + 25*X^5 + 54*X^4 +
      X^3 + 14*X^2 + 16*X + 16,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s49 : XPow fSeventeenB2 1274277617
    (48*X^33 + 8*X^32 + 55*X^31 + 11*X^30 + 54*X^29 + 66*X^28 + 16*X^27 + 20*X^26 + 41*X^25 + 57*X^24 +
      8*X^23 + 51*X^22 + 63*X^21 + 2*X^20 + 24*X^19 + 34*X^18 + X^17 + 47*X^16 + 28*X^15 + 26*X^14 +
      32*X^13 + 17*X^12 + 40*X^11 + 26*X^10 + 44*X^9 + 14*X^8 + 4*X^7 + 34*X^6 + 6*X^5 + 42*X^4 +
      48*X^3 + 65*X^2 + 14*X + 51) :=
  mul_step (by norm_num) pSeventeenB2s48 pSeventeenB21 ⟨
    28,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s50 : XPow fSeventeenB2 2548555234
    (45*X^33 + 24*X^32 + 26*X^31 + 15*X^30 + 2*X^29 + 40*X^28 + 20*X^27 + 60*X^26 + 56*X^25 + 56*X^24 +
      32*X^23 + 6*X^22 + 29*X^21 + 33*X^20 + 52*X^19 + 41*X^18 + 42*X^17 + 8*X^16 + 66*X^15 +
      20*X^14 + 29*X^12 + 27*X^11 + 19*X^10 + 49*X^9 + 60*X^8 + 19*X^7 + 46*X^6 + 10*X^5 + 66*X^4 +
      29*X^3 + 15*X^2 + 11*X + 57) :=
  sq_step (by norm_num) pSeventeenB2s49 ⟨
    26*X^32 + 2*X^31 + 62*X^30 + 38*X^29 + 30*X^28 + 50*X^27 + 54*X^26 + 20*X^25 + 36*X^24 + 25*X^23 +
      11*X^22 + 43*X^21 + 3*X^20 + 65*X^19 + 29*X^18 + 18*X^17 + 4*X^16 + 5*X^15 + 17*X^14 + 10*X^13 +
      44*X^12 + 13*X^11 + 37*X^10 + 42*X^9 + 45*X^8 + 45*X^7 + 30*X^6 + 3*X^5 + 19*X^4 + 49*X^3 +
      27*X^2 + 61*X + 30,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s51 : XPow fSeventeenB2 2548555235
    (64*X^33 + 60*X^32 + 49*X^31 + 13*X^30 + 66*X^29 + 12*X^27 + 39*X^26 + 35*X^25 + 27*X^24 + 9*X^23 +
      57*X^22 + 61*X^21 + 30*X^20 + 6*X^19 + 22*X^18 + 6*X^17 + 54*X^16 + 62*X^15 + 27*X^14 +
      52*X^13 + 50*X^12 + 59*X^11 + 21*X^10 + 35*X^9 + 65*X^8 + 17*X^7 + 55*X^6 + 40*X^5 + 37*X^4 +
      6*X^3 + 56*X^2 + 56*X + 3) :=
  mul_step (by norm_num) pSeventeenB2s50 pSeventeenB21 ⟨
    45,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s52 : XPow fSeventeenB2 5097110470
    (46*X^33 + 28*X^32 + 54*X^31 + 10*X^30 + 63*X^29 + 47*X^28 + 16*X^27 + 49*X^26 + 8*X^25 + 15*X^24 +
      54*X^23 + 41*X^22 + 26*X^21 + 39*X^20 + 34*X^19 + 31*X^18 + 56*X^17 + 61*X^16 + 27*X^15 +
      6*X^14 + 15*X^13 + 65*X^12 + 50*X^11 + 28*X^10 + 50*X^9 + 55*X^8 + 42*X^7 + 52*X^6 + 34*X^5 +
      21*X^4 + 48*X^3 + 39*X^2 + 8*X + 29) :=
  sq_step (by norm_num) pSeventeenB2s51 ⟨
    9*X^32 + 50*X^31 + 40*X^30 + 4*X^29 + 55*X^28 + 55*X^27 + 11*X^26 + 13*X^25 + 44*X^24 + 24*X^23 +
      27*X^22 + 61*X^21 + 29*X^20 + 9*X^19 + 43*X^18 + 65*X^17 + 59*X^16 + 59*X^15 + 51*X^14 +
      57*X^13 + 36*X^12 + 65*X^11 + 24*X^10 + 30*X^9 + 63*X^8 + 42*X^7 + 46*X^6 + 45*X^5 + 48*X^4 +
      24*X^3 + 63*X^2 + 4*X + 32,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s53 : XPow fSeventeenB2 5097110471
    (54*X^33 + 56*X^32 + 12*X^31 + 40*X^30 + 17*X^29 + 3*X^28 + 58*X^27 + 7*X^26 + 65*X^25 + 34*X^24 +
      53*X^23 + 4*X^22 + 17*X^21 + 13*X^20 + 25*X^19 + 43*X^18 + 53*X^17 + 46*X^16 + 40*X^15 +
      56*X^14 + 23*X^13 + 8*X^12 + 54*X^11 + 5*X^10 + 22*X^9 + 25*X^8 + 3*X^7 + 13*X^6 + 51*X^5 +
      13*X^4 + 3*X^3 + 54*X^2 + 25*X + 12) :=
  mul_step (by norm_num) pSeventeenB2s52 pSeventeenB21 ⟨
    46,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s54 : XPow fSeventeenB2 10194220942
    (52*X^33 + X^32 + 45*X^31 + 32*X^30 + 21*X^29 + 39*X^28 + 63*X^27 + 45*X^26 + 64*X^25 + X^24 +
      12*X^23 + 33*X^22 + 2*X^21 + 31*X^20 + 45*X^19 + 54*X^18 + 36*X^17 + 34*X^16 + 16*X^15 +
      63*X^14 + 41*X^13 + 17*X^12 + 35*X^11 + 34*X^10 + 63*X^9 + 60*X^8 + 15*X^7 + 31*X^6 + 55*X^5 +
      58*X^4 + 3*X^3 + 34*X^2 + 40*X + 9) :=
  sq_step (by norm_num) pSeventeenB2s53 ⟨
    35*X^32 + 64*X^31 + 4*X^30 + 28*X^29 + 22*X^28 + 65*X^27 + 10*X^26 + 59*X^25 + 44*X^24 + 62*X^23 +
      66*X^22 + 45*X^21 + 11*X^20 + 42*X^19 + 63*X^18 + 2*X^17 + 14*X^16 + 54*X^15 + 16*X^14 +
      36*X^13 + 56*X^12 + 13*X^11 + 29*X^10 + 27*X^9 + 5*X^8 + 34*X^7 + 34*X^6 + 43*X^5 + 23*X^4 +
      47*X^3 + 50*X^2 + 37*X + 52,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s55 : XPow fSeventeenB2 20388441884
    (25*X^33 + 59*X^32 + 55*X^31 + 55*X^30 + 27*X^29 + 46*X^28 + 26*X^27 + 65*X^26 + 11*X^25 + 21*X^24 +
      33*X^23 + 51*X^22 + 51*X^21 + 7*X^20 + 15*X^19 + 35*X^18 + 7*X^17 + 19*X^16 + 2*X^15 + 18*X^14 +
      20*X^13 + 60*X^12 + 26*X^11 + 51*X^10 + 29*X^9 + 11*X^8 + 39*X^7 + 66*X^6 + 23*X^5 + 45*X^4 +
      36*X^3 + 43*X^2 + 47*X + 46) :=
  sq_step (by norm_num) pSeventeenB2s54 ⟨
    24*X^32 + 36*X^31 + 59*X^30 + 2*X^29 + 54*X^28 + 27*X^27 + 36*X^26 + 55*X^25 + X^24 + 31*X^23 +
      64*X^22 + 59*X^21 + 13*X^20 + 30*X^19 + 64*X^18 + 58*X^17 + 45*X^16 + 53*X^15 + 57*X^14 +
      13*X^13 + 11*X^12 + 5*X^11 + 23*X^10 + 38*X^9 + 61*X^8 + 66*X^6 + 9*X^5 + 7*X^4 + 55*X^3 +
      12*X^2 + 48*X + 11,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s56 : XPow fSeventeenB2 20388441885
    (44*X^33 + 59*X^32 + 59*X^31 + 48*X^30 + 53*X^29 + 16*X^27 + 9*X^26 + 54*X^25 + 60*X^24 + 8*X^23 +
      7*X^22 + 30*X^21 + 40*X^20 + 23*X^19 + 48*X^18 + 3*X^17 + 40*X^16 + 19*X^15 + 35*X^14 +
      43*X^13 + 9*X^12 + 36*X^11 + 6*X^10 + 12*X^9 + 5*X^8 + 35*X^7 + 48*X^6 + 38*X^5 + 33*X^4 +
      38*X^3 + 5*X^2 + 38*X + 24) :=
  mul_step (by norm_num) pSeventeenB2s55 pSeventeenB21 ⟨
    25,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s57 : XPow fSeventeenB2 40776883770
    (46*X^33 + 37*X^32 + 6*X^31 + 23*X^30 + 46*X^29 + 49*X^28 + 3*X^27 + 9*X^26 + 14*X^25 + 34*X^24 +
      42*X^23 + 28*X^22 + 2*X^21 + 57*X^20 + 31*X^19 + 24*X^18 + 55*X^17 + 20*X^16 + 58*X^15 +
      20*X^14 + 53*X^13 + 38*X^12 + 38*X^11 + 11*X^10 + 9*X^9 + 53*X^8 + 48*X^7 + 65*X^6 + 9*X^5 +
      50*X^4 + 19*X^3 + 38*X^2 + 24*X + 49) :=
  sq_step (by norm_num) pSeventeenB2s56 ⟨
    60*X^32 + 64*X^31 + 28*X^30 + 59*X^29 + 26*X^28 + 18*X^27 + 64*X^26 + 63*X^25 + 50*X^24 + 38*X^23 +
      3*X^22 + 63*X^21 + 37*X^20 + 64*X^19 + 19*X^18 + 25*X^17 + 21*X^16 + 11*X^15 + 46*X^14 +
      59*X^13 + 19*X^12 + 43*X^11 + 18*X^10 + 66*X^9 + 3*X^8 + 30*X^7 + 45*X^6 + 6*X^5 + 41*X^4 +
      64*X^3 + 11*X^2 + 46*X + 1,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s58 : XPow fSeventeenB2 81553767540
    (60*X^33 + 44*X^31 + 29*X^30 + 62*X^29 + 31*X^28 + 26*X^27 + 6*X^26 + 43*X^25 + 34*X^24 + 4*X^23 +
      25*X^22 + 13*X^21 + 42*X^20 + 18*X^19 + 30*X^18 + 48*X^17 + 65*X^16 + 31*X^15 + 65*X^14 +
      36*X^13 + 62*X^12 + 54*X^11 + 61*X^10 + 21*X^9 + 55*X^8 + 58*X^7 + 33*X^6 + 53*X^5 + 66*X^4 +
      52*X^3 + 21*X^2 + 48*X + 57) :=
  sq_step (by norm_num) pSeventeenB2s57 ⟨
    39*X^32 + 44*X^31 + 57*X^30 + 44*X^29 + 59*X^28 + 48*X^27 + 35*X^26 + 28*X^25 + 28*X^24 + 28*X^23 +
      33*X^22 + 46*X^21 + 64*X^20 + 9*X^19 + 19*X^18 + 38*X^17 + 23*X^16 + 10*X^15 + 2*X^14 + 4*X^13 +
      22*X^12 + 24*X^11 + 21*X^10 + 47*X^9 + 12*X^8 + 58*X^7 + 37*X^6 + 5*X^5 + 15*X^4 + 43*X^3 +
      5*X^2 + 17*X + 15,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s59 : XPow fSeventeenB2 81553767541
    (31*X^33 + 52*X^31 + 32*X^30 + 21*X^29 + 44*X^28 + 9*X^27 + 65*X^26 + 6*X^25 + 42*X^24 + 29*X^23 +
      28*X^22 + 57*X^21 + 11*X^20 + 28*X^19 + 66*X^18 + 40*X^17 + 15*X^16 + 54*X^15 + 5*X^14 +
      48*X^13 + 40*X^12 + 25*X^11 + 6*X^10 + 44*X^9 + 30*X^8 + 39*X^7 + 46*X^6 + 9*X^5 + 18*X^4 +
      9*X^3 + 41*X^2 + 11*X + 4) :=
  mul_step (by norm_num) pSeventeenB2s58 pSeventeenB21 ⟨
    60,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s60 : XPow fSeventeenB2 163107535082
    (10*X^33 + 15*X^32 + 41*X^31 + 26*X^30 + 42*X^29 + 35*X^28 + 25*X^27 + 47*X^26 + 19*X^25 + 49*X^24 +
      21*X^23 + 29*X^22 + 60*X^21 + 14*X^20 + 56*X^19 + 11*X^18 + 53*X^17 + 62*X^16 + 24*X^15 +
      29*X^14 + 50*X^13 + 27*X^12 + 44*X^11 + 42*X^10 + 27*X^9 + 11*X^8 + 66*X^7 + 29*X^6 + 59*X^5 +
      13*X^4 + 5*X^3 + 21*X^2 + 36*X + 63) :=
  sq_step (by norm_num) pSeventeenB2s59 ⟨
    23*X^32 + 13*X^31 + 28*X^30 + 38*X^29 + 40*X^28 + 46*X^27 + 45*X^26 + 18*X^25 + 22*X^24 + 50*X^23 +
      51*X^22 + 25*X^21 + 35*X^20 + 38*X^19 + 59*X^18 + 37*X^17 + 9*X^16 + 64*X^15 + 23*X^14 +
      45*X^13 + 65*X^12 + 22*X^11 + 57*X^10 + 62*X^9 + 5*X^8 + 58*X^7 + 9*X^6 + 23*X^5 + 28*X^4 +
      5*X^3 + 20*X^2 + 58*X + 35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s61 : XPow fSeventeenB2 326215070164
    (36*X^33 + 60*X^32 + 59*X^31 + 54*X^30 + 26*X^29 + 59*X^28 + 62*X^27 + 47*X^26 + 62*X^25 + 42*X^24 +
      40*X^23 + 47*X^22 + 23*X^21 + 61*X^20 + 13*X^19 + 3*X^18 + 54*X^16 + 61*X^15 + 51*X^14 +
      52*X^13 + X^12 + 52*X^11 + 52*X^10 + 33*X^9 + 14*X^8 + 32*X^7 + 37*X^6 + 45*X^5 + 61*X^4 +
      41*X^3 + 64*X^2 + 56*X + 37) :=
  sq_step (by norm_num) pSeventeenB2s60 ⟨
    33*X^32 + 39*X^31 + 46*X^30 + 8*X^29 + 17*X^28 + 24*X^27 + 12*X^26 + 14*X^25 + 16*X^24 + 3*X^23 +
      65*X^22 + 24*X^21 + 6*X^20 + 41*X^19 + 28*X^18 + 16*X^17 + 65*X^16 + 26*X^15 + 17*X^14 +
      39*X^13 + 3*X^12 + 66*X^11 + 48*X^10 + 33*X^9 + 29*X^8 + 12*X^7 + 61*X^6 + 26*X^5 + 55*X^4 +
      55*X^3 + 31*X^2 + 39*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s62 : XPow fSeventeenB2 652430140328
    (24*X^33 + 6*X^31 + 6*X^30 + 2*X^29 + 26*X^28 + 29*X^27 + 66*X^26 + 3*X^25 + 60*X^24 + 33*X^23 +
      8*X^22 + 11*X^21 + 39*X^18 + 7*X^17 + 52*X^16 + 47*X^15 + 43*X^14 + 29*X^13 + 53*X^12 +
      34*X^11 + 47*X^10 + X^9 + 7*X^8 + 8*X^7 + 62*X^6 + 24*X^5 + 49*X^4 + 35*X^3 + 59*X^2 + X + 53) :=
  sq_step (by norm_num) pSeventeenB2s61 ⟨
    23*X^32 + 45*X^31 + 50*X^30 + 52*X^29 + 47*X^28 + 32*X^27 + 4*X^26 + 60*X^25 + 10*X^24 + 40*X^23 +
      20*X^22 + 42*X^21 + 21*X^20 + 38*X^19 + 32*X^18 + 45*X^17 + 13*X^16 + 26*X^15 + 30*X^14 +
      50*X^13 + 12*X^12 + 20*X^11 + 50*X^10 + 49*X^9 + 50*X^8 + 28*X^7 + 58*X^6 + 15*X^5 + 7*X^4 +
      43*X^2 + 17*X + 25,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s63 : XPow fSeventeenB2 652430140329
    (66*X^33 + 42*X^32 + 42*X^31 + 57*X^30 + 22*X^29 + 63*X^28 + 27*X^27 + 52*X^26 + 22*X^25 + 8*X^24 +
      23*X^23 + 17*X^22 + 6*X^21 + 24*X^20 + 65*X^19 + 41*X^18 + 42*X^17 + 54*X^16 + 52*X^15 +
      30*X^14 + 34*X^13 + 15*X^12 + 46*X^11 + 62*X^10 + 16*X^9 + 37*X^8 + 51*X^7 + 48*X^6 + 53*X^5 +
      8*X^4 + 14*X^3 + 25*X^2 + 48*X + 15) :=
  mul_step (by norm_num) pSeventeenB2s62 pSeventeenB21 ⟨
    24,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s64 : XPow fSeventeenB2 1304860280658
    (54*X^33 + 12*X^32 + 56*X^31 + 42*X^30 + 57*X^29 + 22*X^28 + 30*X^27 + 19*X^26 + 2*X^25 + 33*X^24 +
      43*X^23 + 4*X^22 + 58*X^21 + 36*X^20 + 4*X^19 + 23*X^18 + 16*X^17 + 16*X^16 + 13*X^15 + X^14 +
      7*X^13 + 60*X^12 + 7*X^11 + 61*X^10 + 5*X^9 + 15*X^8 + 61*X^7 + 30*X^6 + 49*X^5 + 32*X^4 +
      44*X^3 + 48*X^2 + 60*X + 45) :=
  sq_step (by norm_num) pSeventeenB2s63 ⟨
    X^32 + 36*X^31 + 5*X^30 + 16*X^29 + 47*X^28 + 14*X^27 + 48*X^26 + 58*X^25 + 16*X^24 + 5*X^23 +
      38*X^22 + 56*X^21 + 63*X^20 + 23*X^19 + 6*X^18 + 27*X^17 + 46*X^16 + 26*X^15 + 2*X^14 +
      20*X^13 + 29*X^12 + 43*X^11 + X^10 + 3*X^9 + 57*X^8 + 38*X^6 + 47*X^5 + 26*X^4 + 52*X^3 +
      2*X^2 + 41*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s65 : XPow fSeventeenB2 2609720561316
    (61*X^33 + 66*X^32 + 46*X^31 + 21*X^30 + 16*X^29 + 38*X^28 + 40*X^27 + 41*X^26 + 28*X^25 + 66*X^24 +
      2*X^23 + 20*X^22 + 9*X^21 + 51*X^20 + 37*X^19 + 12*X^18 + 63*X^17 + 12*X^16 + 8*X^15 + 34*X^14 +
      51*X^13 + 49*X^12 + 51*X^11 + 64*X^10 + 40*X^9 + 66*X^8 + 56*X^7 + 10*X^6 + 34*X^5 + 59*X^4 +
      43*X^3 + 56*X^2 + 50*X + 21) :=
  sq_step (by norm_num) pSeventeenB2s64 ⟨
    35*X^32 + 2*X^31 + 19*X^30 + 8*X^29 + 18*X^28 + 11*X^27 + 32*X^26 + 8*X^25 + 18*X^24 + 53*X^23 +
      10*X^22 + 34*X^21 + 57*X^20 + 62*X^19 + 28*X^18 + 33*X^17 + 57*X^16 + 13*X^15 + 9*X^14 +
      22*X^13 + 14*X^12 + 58*X^11 + 8*X^10 + 5*X^9 + 4*X^8 + 42*X^7 + 62*X^6 + 7*X^5 + 50*X^4 +
      64*X^3 + 10*X^2 + 46*X + 23,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s66 : XPow fSeventeenB2 2609720561317
    (16*X^33 + 37*X^32 + 12*X^31 + 19*X^30 + 39*X^29 + 65*X^28 + 34*X^27 + 66*X^26 + 42*X^25 + 25*X^24 +
      33*X^23 + 41*X^22 + 16*X^21 + 31*X^20 + 39*X^19 + 21*X^18 + 48*X^17 + 23*X^16 + 15*X^15 +
      34*X^14 + 37*X^13 + 39*X^12 + 14*X^11 + 8*X^10 + 47*X^9 + 32*X^8 + 63*X^7 + 28*X^6 + 58*X^5 +
      33*X^4 + 17*X^3 + 44*X^2 + 39*X + 13) :=
  mul_step (by norm_num) pSeventeenB2s65 pSeventeenB21 ⟨
    61,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s67 : XPow fSeventeenB2 5219441122634
    (16*X^33 + 53*X^32 + 54*X^31 + 47*X^30 + 12*X^29 + 41*X^28 + 48*X^27 + 38*X^26 + 41*X^25 + 24*X^24 +
      19*X^23 + 47*X^22 + 37*X^21 + 25*X^20 + 30*X^19 + 45*X^18 + 57*X^17 + 11*X^16 + 32*X^15 +
      25*X^14 + 63*X^13 + 58*X^12 + 35*X^11 + 63*X^10 + 24*X^9 + 7*X^8 + 44*X^7 + 30*X^6 + X^5 +
      27*X^4 + 33*X^2 + 58*X + 31) :=
  sq_step (by norm_num) pSeventeenB2s66 ⟨
    55*X^32 + 12*X^31 + 26*X^30 + 60*X^29 + 11*X^28 + 33*X^27 + 7*X^26 + 58*X^25 + 54*X^24 + 13*X^23 +
      64*X^22 + 23*X^21 + 29*X^20 + 49*X^19 + 46*X^18 + 40*X^17 + 38*X^16 + 27*X^15 + 32*X^14 +
      3*X^13 + 13*X^12 + 60*X^11 + 31*X^10 + 24*X^9 + 29*X^8 + 20*X^7 + 31*X^6 + 50*X^5 + 47*X^4 +
      4*X^3 + 27*X^2 + 45*X + 7,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s68 : XPow fSeventeenB2 10438882245268
    (43*X^33 + 5*X^32 + 47*X^31 + 60*X^30 + 35*X^29 + 33*X^28 + 15*X^27 + 62*X^26 + 20*X^25 + 14*X^24 +
      56*X^23 + 26*X^22 + 5*X^21 + 39*X^20 + 6*X^19 + 52*X^18 + 55*X^17 + 26*X^16 + 7*X^15 + 6*X^14 +
      11*X^13 + 3*X^12 + 57*X^11 + 40*X^10 + 15*X^9 + 47*X^8 + 18*X^7 + 8*X^6 + 52*X^5 + 30*X^4 +
      9*X^3 + 11*X^2 + X + 41) :=
  sq_step (by norm_num) pSeventeenB2s67 ⟨
    55*X^32 + 55*X^31 + 64*X^30 + 65*X^29 + 19*X^28 + 58*X^27 + 11*X^26 + 29*X^24 + 43*X^23 + 25*X^22 +
      61*X^21 + 60*X^20 + 50*X^19 + 46*X^18 + 60*X^17 + 41*X^16 + 13*X^14 + 17*X^13 + 63*X^12 +
      24*X^11 + 60*X^10 + X^9 + 56*X^8 + 54*X^7 + 42*X^6 + 11*X^5 + 29*X^4 + 2*X^3 + 66*X^2 + 33*X +
      2,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s69 : XPow fSeventeenB2 20877764490536
    (7*X^33 + 55*X^32 + 37*X^31 + 64*X^30 + 28*X^29 + 59*X^28 + 66*X^27 + 8*X^26 + 23*X^25 + 59*X^24 +
      43*X^23 + 7*X^22 + 12*X^21 + 13*X^20 + 24*X^19 + 29*X^18 + 19*X^17 + 59*X^16 + 13*X^15 +
      48*X^13 + 46*X^12 + 15*X^11 + 57*X^10 + 45*X^9 + 35*X^8 + 13*X^7 + 8*X^6 + 10*X^5 + 36*X^4 +
      43*X^3 + 5*X^2 + 29*X + 64) :=
  sq_step (by norm_num) pSeventeenB2s68 ⟨
    40*X^32 + 4*X^31 + 51*X^30 + 24*X^29 + 18*X^28 + 48*X^27 + 59*X^26 + 40*X^25 + 66*X^24 + 3*X^23 +
      30*X^22 + 33*X^21 + 46*X^20 + 56*X^19 + 13*X^18 + 19*X^17 + 65*X^16 + 32*X^15 + 31*X^14 +
      53*X^13 + 66*X^12 + 29*X^11 + 3*X^10 + 42*X^9 + 2*X^8 + 33*X^7 + 18*X^6 + 54*X^5 + 8*X^4 +
      33*X^3 + 31*X + 66,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s70 : XPow fSeventeenB2 20877764490537
    (24*X^33 + 14*X^32 + 41*X^31 + 58*X^30 + 2*X^29 + 48*X^28 + 5*X^27 + X^26 + 20*X^25 + 5*X^24 + 3*X^23 +
      64*X^22 + 65*X^21 + 31*X^20 + 31*X^19 + X^18 + 17*X^17 + 29*X^16 + 11*X^15 + 12*X^14 + 60*X^13 +
      29*X^12 + 26*X^11 + 60*X^10 + 46*X^9 + 41*X^8 + 2*X^7 + 17*X^6 + 26*X^5 + 10*X^4 + 17*X^3 +
      36*X^2 + 43*X + 63) :=
  mul_step (by norm_num) pSeventeenB2s69 pSeventeenB21 ⟨
    7,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s71 : XPow fSeventeenB2 41755528981074
    (23*X^33 + 33*X^32 + 40*X^31 + X^30 + 10*X^29 + 9*X^28 + 46*X^27 + 35*X^26 + 55*X^25 + 28*X^24 +
      27*X^23 + 51*X^22 + 17*X^21 + 34*X^20 + 50*X^19 + 53*X^18 + 65*X^17 + 36*X^16 + 17*X^15 +
      22*X^14 + 44*X^13 + 53*X^12 + 48*X^11 + 9*X^10 + 65*X^9 + 64*X^8 + 3*X^7 + 30*X^6 + 6*X^5 +
      3*X^4 + 62*X^3 + 10*X^2 + 28*X + 10) :=
  sq_step (by norm_num) pSeventeenB2s70 ⟨
    40*X^32 + 45*X^31 + 53*X^30 + X^29 + 30*X^28 + 59*X^27 + 56*X^26 + 49*X^25 + 12*X^24 + 23*X^23 +
      56*X^22 + 25*X^21 + 16*X^20 + 25*X^19 + 9*X^18 + 55*X^17 + 35*X^16 + 8*X^15 + 8*X^14 + 6*X^13 +
      X^12 + 53*X^11 + 60*X^10 + 12*X^9 + 39*X^8 + 37*X^7 + 13*X^6 + 11*X^5 + 28*X^4 + 9*X^3 +
      35*X^2 + 56*X + 44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s72 : XPow fSeventeenB2 83511057962148
    (40*X^33 + 41*X^32 + 51*X^31 + 24*X^30 + 14*X^29 + 11*X^28 + 16*X^27 + 18*X^26 + 11*X^25 + 33*X^24 +
      9*X^23 + 55*X^22 + 45*X^21 + 38*X^20 + 52*X^19 + 26*X^18 + 59*X^17 + 44*X^16 + 50*X^15 +
      47*X^14 + 58*X^13 + 12*X^12 + 43*X^11 + 19*X^10 + X^9 + 36*X^8 + 23*X^7 + 36*X^6 + 54*X^5 +
      28*X^4 + 63*X^3 + 14*X^2 + 40*X + 32) :=
  sq_step (by norm_num) pSeventeenB2s71 ⟨
    60*X^32 + 8*X^31 + 26*X^30 + 12*X^29 + 36*X^28 + 23*X^27 + 4*X^26 + 29*X^25 + 35*X^24 + 19*X^23 +
      14*X^22 + 29*X^21 + 23*X^20 + 59*X^19 + 41*X^18 + 22*X^17 + 50*X^16 + 15*X^15 + 24*X^14 +
      66*X^13 + 66*X^12 + 45*X^11 + 6*X^10 + 56*X^9 + 59*X^8 + 34*X^7 + 19*X^6 + 49*X^5 + 58*X^4 +
      12*X^3 + 2*X^2 + 34*X + 52,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s73 : XPow fSeventeenB2 167022115924296
    (17*X^33 + 40*X^32 + 11*X^31 + 15*X^30 + 19*X^29 + 36*X^28 + 38*X^27 + 13*X^26 + 11*X^25 + 26*X^24 +
      62*X^23 + 17*X^22 + 28*X^21 + 15*X^20 + 33*X^19 + 27*X^18 + 31*X^17 + 2*X^16 + 64*X^15 +
      36*X^14 + 10*X^13 + 21*X^12 + 29*X^11 + 15*X^10 + 31*X^9 + 26*X^8 + 8*X^7 + 38*X^6 + 13*X^5 +
      37*X^4 + 2*X^3 + 43*X^2 + 51*X + 30) :=
  sq_step (by norm_num) pSeventeenB2s72 ⟨
    59*X^32 + 42*X^31 + 2*X^30 + 28*X^29 + 7*X^28 + 26*X^27 + 25*X^26 + 38*X^25 + 7*X^24 + 61*X^23 +
      63*X^22 + 51*X^21 + 51*X^20 + 14*X^19 + 28*X^18 + 50*X^17 + 61*X^16 + 65*X^15 + 54*X^14 +
      9*X^13 + 15*X^12 + 44*X^11 + 23*X^10 + 48*X^9 + 56*X^8 + 43*X^7 + 57*X^6 + 13*X^5 + 14*X^4 +
      2*X^3 + 39*X^2 + 7*X + 31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s74 : XPow fSeventeenB2 334044231848592
    (48*X^33 + 66*X^32 + 30*X^31 + 65*X^30 + 2*X^29 + 3*X^28 + 3*X^27 + 55*X^26 + 24*X^25 + 30*X^24 +
      15*X^23 + 35*X^22 + 41*X^21 + 17*X^20 + 9*X^19 + 19*X^18 + 6*X^17 + 15*X^16 + 27*X^15 +
      20*X^14 + 13*X^13 + 63*X^12 + 13*X^11 + 13*X^10 + 29*X^9 + 31*X^8 + 53*X^7 + 53*X^6 + 42*X^5 +
      60*X^4 + 36*X^3 + 25*X^2 + 44*X + 60) :=
  sq_step (by norm_num) pSeventeenB2s73 ⟨
    21*X^32 + 61*X^31 + 46*X^30 + 65*X^29 + X^28 + 10*X^27 + 8*X^26 + 12*X^25 + 58*X^24 + 13*X^23 +
      40*X^22 + 41*X^21 + 41*X^20 + 21*X^19 + 40*X^18 + 33*X^17 + 12*X^16 + 19*X^15 + 24*X^14 +
      51*X^13 + 45*X^12 + 59*X^11 + 22*X^10 + 60*X^9 + 32*X^8 + 59*X^7 + 56*X^6 + 61*X^5 + 31*X^4 +
      40*X^3 + 40*X^2 + 6*X + 63,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s75 : XPow fSeventeenB2 668088463697184
    (54*X^33 + 31*X^32 + 7*X^31 + 64*X^30 + 48*X^29 + 54*X^28 + 31*X^27 + 16*X^26 + 16*X^25 + 11*X^24 +
      19*X^23 + 46*X^22 + 27*X^21 + 51*X^20 + 48*X^19 + 61*X^18 + 58*X^17 + 12*X^16 + 66*X^15 +
      41*X^14 + 30*X^13 + 56*X^12 + 27*X^11 + 21*X^10 + 29*X^9 + 2*X^8 + 38*X^7 + 17*X^6 + 56*X^5 +
      40*X^4 + 41*X^3 + 8*X^2 + 64*X + 32) :=
  sq_step (by norm_num) pSeventeenB2s74 ⟨
    26*X^32 + 9*X^31 + 47*X^30 + 47*X^29 + 40*X^28 + 60*X^27 + 21*X^26 + 4*X^25 + 66*X^24 + 34*X^23 +
      59*X^22 + 55*X^21 + 65*X^20 + 45*X^19 + 45*X^18 + 12*X^17 + 16*X^16 + 64*X^15 + 50*X^14 +
      5*X^13 + 53*X^12 + 16*X^11 + 22*X^10 + X^9 + 28*X^8 + 59*X^7 + 2*X^6 + 16*X^5 + 49*X^4 +
      22*X^3 + 31*X^2 + 65*X + 13,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s76 : XPow fSeventeenB2 1336176927394368
    (18*X^33 + 10*X^32 + 4*X^31 + 65*X^30 + 62*X^29 + 61*X^28 + 21*X^27 + 42*X^26 + 32*X^25 + 7*X^24 +
      43*X^23 + 57*X^22 + 22*X^21 + 61*X^20 + 37*X^19 + 8*X^18 + 55*X^17 + 5*X^16 + 23*X^15 +
      60*X^14 + 24*X^13 + 53*X^12 + 28*X^11 + 46*X^10 + 31*X^9 + 20*X^8 + 59*X^7 + 42*X^6 + 21*X^5 +
      10*X^4 + 47*X^3 + 32*X^2 + 19*X + 33) :=
  sq_step (by norm_num) pSeventeenB2s75 ⟨
    35*X^32 + 44*X^31 + 48*X^30 + 59*X^29 + 20*X^28 + 65*X^27 + 21*X^26 + 53*X^25 + 55*X^24 + 36*X^23 +
      7*X^22 + 49*X^21 + 66*X^20 + 6*X^19 + 60*X^18 + 17*X^17 + 35*X^16 + 17*X^15 + 17*X^14 + 4*X^13 +
      55*X^12 + 40*X^11 + 7*X^10 + 66*X^9 + 11*X^8 + 52*X^7 + 5*X^6 + 11*X^5 + 22*X^4 + 3*X^3 +
      18*X^2 + 19*X + 9,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s77 : XPow fSeventeenB2 2672353854788736
    (21*X^33 + 61*X^32 + 49*X^31 + 15*X^30 + 8*X^29 + 27*X^28 + 12*X^27 + 28*X^26 + 54*X^25 + 55*X^24 +
      38*X^23 + X^22 + 49*X^21 + 27*X^20 + 59*X^19 + 30*X^18 + 4*X^17 + 52*X^16 + 21*X^15 + 57*X^14 +
      X^13 + 27*X^12 + 16*X^11 + 3*X^10 + 57*X^9 + 45*X^8 + 61*X^7 + 38*X^6 + 14*X^5 + 44*X^4 +
      55*X^3 + 27*X^2 + 18*X + 12) :=
  sq_step (by norm_num) pSeventeenB2s76 ⟨
    56*X^32 + 45*X^31 + 33*X^30 + 66*X^29 + 33*X^28 + 15*X^27 + 2*X^26 + 23*X^25 + 16*X^24 + 37*X^23 +
      42*X^22 + 50*X^21 + 65*X^20 + 27*X^19 + 63*X^18 + 15*X^17 + 61*X^16 + 7*X^15 + 2*X^14 + 3*X^13 +
      38*X^12 + 19*X^11 + 6*X^10 + 36*X^9 + 23*X^8 + 65*X^7 + 14*X^6 + 9*X^5 + 60*X^4 + 20*X^3 +
      10*X^2 + 61*X + 59,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s78 : XPow fSeventeenB2 5344707709577472
    (48*X^33 + 15*X^32 + 32*X^31 + 46*X^30 + 20*X^29 + 37*X^28 + 5*X^27 + 10*X^26 + 48*X^25 + 22*X^24 +
      15*X^23 + 11*X^22 + 56*X^21 + 25*X^20 + 14*X^19 + 35*X^18 + 18*X^17 + 22*X^16 + 58*X^15 +
      27*X^14 + 25*X^13 + 40*X^12 + 7*X^11 + 41*X^9 + 57*X^8 + 45*X^7 + 36*X^6 + 15*X^5 + 13*X^4 +
      34*X^3 + 12*X^2 + 12*X + 5) :=
  sq_step (by norm_num) pSeventeenB2s77 ⟨
    39*X^32 + 6*X^31 + 25*X^30 + 61*X^29 + 55*X^28 + 15*X^27 + 39*X^26 + 57*X^25 + 58*X^24 + 29*X^23 +
      11*X^22 + 50*X^21 + 30*X^20 + 56*X^19 + 5*X^18 + 55*X^17 + 22*X^16 + 15*X^15 + 18*X^14 +
      37*X^13 + 6*X^12 + 24*X^11 + 13*X^10 + 33*X^9 + 20*X^8 + 41*X^7 + 30*X^6 + 28*X^5 + 11*X^4 +
      5*X^3 + 49*X^2 + 40*X + 59,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s79 : XPow fSeventeenB2 5344707709577473
    (13*X^33 + 37*X^32 + 51*X^31 + 63*X^30 + 29*X^29 + 6*X^28 + 66*X^27 + 12*X^26 + 13*X^25 + 32*X^24 +
      41*X^23 + X^22 + 37*X^21 + 62*X^20 + 20*X^19 + 19*X^18 + 2*X^17 + 5*X^16 + 45*X^15 + 27*X^14 +
      2*X^13 + 36*X^12 + 65*X^11 + 29*X^10 + 8*X^9 + 36*X^8 + 14*X^7 + 63*X^6 + 21*X^5 + 47*X^4 +
      56*X^3 + 60*X^2 + 62*X + 30) :=
  mul_step (by norm_num) pSeventeenB2s78 pSeventeenB21 ⟨
    48,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s80 : XPow fSeventeenB2 10689415419154946
    (47*X^33 + 34*X^32 + 64*X^31 + 19*X^30 + 6*X^29 + 28*X^28 + 26*X^27 + 52*X^26 + 26*X^25 + 64*X^24 +
      42*X^23 + 61*X^22 + 50*X^21 + 54*X^20 + 40*X^19 + 56*X^18 + 60*X^17 + 5*X^16 + 5*X^15 +
      54*X^13 + X^12 + 32*X^11 + 58*X^10 + 29*X^9 + 6*X^8 + 11*X^7 + 23*X^6 + 60*X^5 + 5*X^4 +
      42*X^3 + 4*X^2 + 2*X + 27) :=
  sq_step (by norm_num) pSeventeenB2s79 ⟨
    35*X^32 + 3*X^31 + 59*X^30 + 20*X^29 + 7*X^28 + 20*X^27 + 51*X^26 + 20*X^25 + 22*X^24 + 63*X^23 +
      43*X^22 + 4*X^21 + 28*X^20 + 22*X^19 + 9*X^18 + 29*X^17 + 57*X^16 + 2*X^15 + 11*X^14 + 45*X^13 +
      38*X^12 + 17*X^11 + 22*X^10 + 15*X^9 + 2*X^8 + 16*X^7 + 64*X^6 + 11*X^5 + 11*X^4 + 11*X^3 +
      58*X^2 + 31*X + 37,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s81 : XPow fSeventeenB2 10689415419154947
    (46*X^33 + 34*X^32 + 56*X^31 + 16*X^30 + 9*X^29 + 20*X^28 + 51*X^27 + 41*X^26 + 51*X^25 + 7*X^24 +
      15*X^23 + 45*X^22 + 49*X^21 + 20*X^20 + 12*X^19 + 54*X^18 + 58*X^17 + 55*X^16 + 26*X^15 +
      42*X^14 + 28*X^13 + 59*X^12 + 3*X^11 + 34*X^10 + 32*X^9 + 65*X^8 + 21*X^7 + 40*X^6 + 24*X^5 +
      31*X^4 + 8*X^3 + 49*X^2 + 20*X + 21) :=
  mul_step (by norm_num) pSeventeenB2s80 pSeventeenB21 ⟨
    47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s82 : XPow fSeventeenB2 21378830838309894
    (8*X^33 + 58*X^32 + 11*X^31 + 35*X^30 + 7*X^29 + 46*X^28 + 19*X^27 + 50*X^26 + 4*X^25 + 21*X^24 +
      36*X^23 + 11*X^22 + 63*X^21 + 38*X^20 + 45*X^19 + 4*X^18 + 42*X^17 + 19*X^16 + 4*X^15 +
      48*X^14 + X^13 + 49*X^12 + 24*X^11 + 8*X^10 + 53*X^9 + 19*X^8 + 66*X^7 + 37*X^6 + 44*X^5 +
      17*X^4 + 56*X^3 + 12*X^2 + 4*X + 55) :=
  sq_step (by norm_num) pSeventeenB2s81 ⟨
    39*X^32 + 36*X^31 + 66*X^29 + 42*X^28 + 12*X^27 + 6*X^26 + 13*X^25 + 54*X^24 + 61*X^23 + 23*X^22 +
      8*X^21 + 57*X^20 + 41*X^19 + 59*X^18 + 51*X^17 + 39*X^16 + 30*X^15 + 23*X^14 + 14*X^13 +
      58*X^12 + 19*X^11 + 66*X^10 + 38*X^9 + 6*X^8 + 29*X^7 + 53*X^6 + 38*X^5 + 63*X^4 + 54*X^3 +
      2*X + 39,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s83 : XPow fSeventeenB2 42757661676619788
    (41*X^33 + 12*X^32 + 65*X^31 + 61*X^30 + 20*X^29 + 56*X^28 + 3*X^27 + 28*X^26 + 8*X^25 + 9*X^24 +
      24*X^23 + 10*X^22 + 32*X^21 + 60*X^20 + 63*X^19 + 27*X^18 + 63*X^17 + 33*X^16 + 46*X^15 +
      14*X^14 + 27*X^13 + 55*X^12 + 62*X^11 + 50*X^10 + 36*X^9 + 65*X^8 + 45*X^7 + 27*X^6 + 37*X^5 +
      66*X^4 + 37*X^3 + 7*X^2 + 41*X + 31) :=
  sq_step (by norm_num) pSeventeenB2s82 ⟨
    64*X^32 + 32*X^31 + 39*X^30 + 27*X^29 + 3*X^28 + 48*X^27 + 37*X^26 + 44*X^25 + 17*X^24 + 12*X^23 +
      47*X^22 + 28*X^21 + 9*X^20 + 59*X^19 + 41*X^18 + 17*X^17 + 8*X^16 + 28*X^15 + 30*X^14 +
      14*X^13 + 38*X^12 + 66*X^11 + 39*X^10 + 8*X^9 + 62*X^8 + 56*X^7 + 57*X^6 + X^5 + 11*X^4 +
      7*X^3 + 46*X^2 + 16*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s84 : XPow fSeventeenB2 42757661676619789
    (41*X^33 + 26*X^32 + 22*X^31 + 33*X^30 + 38*X^29 + 22*X^28 + 20*X^27 + 61*X^26 + 39*X^25 + 12*X^24 +
      44*X^23 + 59*X^22 + 20*X^21 + 37*X^20 + 10*X^19 + 15*X^18 + 55*X^17 + 44*X^16 + 21*X^15 +
      65*X^14 + 3*X^13 + 10*X^12 + 12*X^11 + 9*X^10 + 5*X^9 + 8*X^8 + 11*X^7 + 11*X^6 + 17*X^5 +
      16*X^4 + 39*X^3 + 15*X^2 + 42*X + 34) :=
  mul_step (by norm_num) pSeventeenB2s83 pSeventeenB21 ⟨
    41,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s85 : XPow fSeventeenB2 85515323353239578
    (17*X^33 + 65*X^32 + 10*X^31 + 16*X^30 + 56*X^29 + 38*X^28 + 65*X^27 + X^26 + 35*X^25 + 58*X^24 +
      55*X^23 + 29*X^22 + 29*X^21 + 41*X^20 + 56*X^19 + 57*X^18 + 57*X^17 + 25*X^16 + 43*X^15 +
      6*X^14 + 34*X^13 + 15*X^12 + 21*X^11 + 64*X^10 + 43*X^9 + 26*X^8 + 45*X^7 + 41*X^6 + 39*X^5 +
      46*X^4 + 47*X^3 + X^2 + 34*X + 27) :=
  sq_step (by norm_num) pSeventeenB2s84 ⟨
    6*X^32 + 38*X^31 + 14*X^30 + 35*X^29 + 10*X^28 + 20*X^27 + 57*X^26 + 29*X^25 + 33*X^24 + 13*X^23 +
      60*X^22 + 14*X^21 + 28*X^20 + 18*X^19 + 24*X^18 + 7*X^17 + 24*X^16 + 45*X^15 + 55*X^14 +
      18*X^13 + 40*X^12 + 27*X^11 + 58*X^10 + 16*X^9 + 20*X^8 + 3*X^7 + 19*X^6 + 13*X^5 + 56*X^4 +
      36*X^3 + 23*X^2 + 64*X + 16,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s86 : XPow fSeventeenB2 171030646706479156
    (34*X^33 + 15*X^32 + 52*X^31 + 29*X^30 + 10*X^29 + 42*X^28 + 57*X^27 + 42*X^26 + 64*X^25 + 36*X^24 +
      26*X^23 + 8*X^22 + 11*X^21 + 7*X^20 + 53*X^19 + 61*X^18 + 62*X^17 + 4*X^16 + 12*X^15 + 38*X^13 +
      16*X^12 + 27*X^11 + 39*X^10 + 18*X^9 + 58*X^8 + 12*X^7 + 54*X^6 + 51*X^5 + 10*X^4 + 4*X^3 +
      5*X^2 + 12*X + 52) :=
  sq_step (by norm_num) pSeventeenB2s85 ⟨
    21*X^32 + 40*X^31 + 50*X^30 + 63*X^29 + 10*X^28 + 54*X^27 + 33*X^26 + 36*X^25 + 35*X^24 + 7*X^23 +
      40*X^22 + 43*X^21 + 38*X^20 + 42*X^19 + 19*X^18 + 25*X^17 + 42*X^16 + 60*X^15 + 39*X^14 +
      49*X^13 + 53*X^12 + 56*X^11 + 40*X^10 + 12*X^9 + 34*X^8 + 3*X^7 + 38*X^6 + 52*X^5 + 38*X^4 +
      45*X^3 + 7*X^2 + 8*X + 29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s87 : XPow fSeventeenB2 342061293412958312
    (27*X^33 + X^32 + 42*X^31 + 56*X^30 + 38*X^29 + 34*X^28 + 16*X^27 + 21*X^26 + 49*X^25 + 40*X^24 +
      32*X^23 + 37*X^22 + 39*X^21 + 51*X^20 + 46*X^19 + 46*X^18 + 52*X^17 + 30*X^16 + 18*X^15 +
      19*X^14 + 51*X^13 + 28*X^12 + 53*X^10 + 42*X^9 + 36*X^8 + 28*X^7 + 8*X^6 + 15*X^5 + 39*X^4 +
      6*X^3 + 57*X^2 + 17*X + 37) :=
  sq_step (by norm_num) pSeventeenB2s86 ⟨
    17*X^32 + 45*X^31 + 41*X^30 + 36*X^29 + 18*X^28 + 36*X^27 + 52*X^26 + 65*X^25 + 59*X^24 + 10*X^23 +
      63*X^22 + 54*X^21 + 53*X^20 + 63*X^19 + 24*X^18 + 55*X^17 + 9*X^16 + 8*X^15 + 16*X^14 +
      21*X^13 + 51*X^12 + 57*X^11 + 6*X^10 + 20*X^9 + 3*X^8 + 46*X^7 + 61*X^6 + X^5 + 44*X^4 +
      15*X^3 + 16*X^2 + 25*X + 61,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s88 : XPow fSeventeenB2 342061293412958313
    (25*X^33 + 49*X^32 + 63*X^31 + 58*X^30 + 63*X^29 + 4*X^28 + 19*X^27 + 12*X^26 + 14*X^25 + 29*X^24 +
      12*X^23 + 29*X^22 + 41*X^21 + 6*X^20 + 25*X^19 + 40*X^18 + 2*X^17 + 51*X^16 + 4*X^15 + 27*X^14 +
      15*X^13 + 54*X^12 + 10*X^11 + 52*X^10 + 21*X^9 + 2*X^8 + 4*X^7 + 42*X^6 + 10*X^5 + 51*X^4 +
      65*X^3 + 44*X^2 + 23*X + 42) :=
  mul_step (by norm_num) pSeventeenB2s87 pSeventeenB21 ⟨
    27,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s89 : XPow fSeventeenB2 684122586825916626
    (37*X^33 + 51*X^32 + 28*X^31 + 8*X^30 + 60*X^29 + 57*X^28 + 46*X^27 + 6*X^26 + 39*X^25 + 48*X^24 +
      63*X^23 + 15*X^22 + 15*X^21 + 38*X^20 + 21*X^19 + 59*X^18 + 63*X^17 + 40*X^16 + 65*X^15 +
      53*X^14 + 44*X^13 + 53*X^12 + 44*X^11 + 43*X^10 + 50*X^9 + 10*X^8 + 43*X^7 + 43*X^6 + 59*X^5 +
      6*X^4 + 27*X^3 + 19*X^2 + 10*X + 60) :=
  sq_step (by norm_num) pSeventeenB2s88 ⟨
    22*X^32 + 65*X^31 + 51*X^30 + 15*X^29 + 26*X^28 + 59*X^27 + 60*X^26 + 32*X^25 + 35*X^24 + 65*X^23 +
      48*X^22 + 63*X^21 + 51*X^20 + 31*X^19 + 63*X^18 + X^17 + 8*X^16 + 37*X^15 + 8*X^14 + 31*X^13 +
      X^12 + 4*X^11 + 27*X^10 + 29*X^9 + 19*X^8 + 25*X^7 + 61*X^6 + 37*X^5 + 44*X^4 + 42*X^3 +
      62*X^2 + 36*X + 34,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s90 : XPow fSeventeenB2 684122586825916627
    (2*X^33 + 50*X^32 + 30*X^31 + 8*X^30 + 62*X^29 + 37*X^28 + 38*X^27 + 28*X^26 + 62*X^25 + 44*X^24 +
      13*X^23 + 41*X^22 + 64*X^21 + 58*X^20 + 60*X^19 + 54*X^18 + 19*X^17 + 6*X^16 + 25*X^15 +
      26*X^14 + 60*X^13 + 51*X^12 + 61*X^11 + 24*X^10 + 49*X^9 + 57*X^8 + 40*X^7 + 29*X^6 + X^5 +
      44*X^4 + 25*X^3 + 47*X^2 + 16*X + 65) :=
  mul_step (by norm_num) pSeventeenB2s89 pSeventeenB21 ⟨
    37,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s91 : XPow fSeventeenB2 1368245173651833254
    (58*X^33 + 35*X^32 + 60*X^31 + 28*X^30 + 31*X^29 + 20*X^28 + 56*X^27 + 37*X^26 + 21*X^25 + 16*X^24 +
      32*X^23 + 49*X^22 + 20*X^21 + 65*X^20 + 44*X^19 + 17*X^18 + 48*X^17 + 37*X^16 + 4*X^15 +
      8*X^14 + 46*X^13 + 37*X^12 + 63*X^11 + 3*X^10 + 17*X^9 + 24*X^8 + 14*X^7 + 29*X^6 + 59*X^5 +
      35*X^4 + 18*X^3 + 60*X^2 + 14*X + 25) :=
  sq_step (by norm_num) pSeventeenB2s90 ⟨
    4*X^32 + 10*X^31 + 7*X^30 + 7*X^29 + 31*X^28 + 22*X^27 + 49*X^26 + 55*X^25 + 63*X^24 + 13*X^23 +
      44*X^22 + 37*X^21 + 63*X^20 + 56*X^19 + 3*X^18 + 43*X^17 + 23*X^16 + 6*X^15 + 60*X^13 +
      10*X^12 + 60*X^11 + 7*X^10 + 46*X^9 + 34*X^8 + 59*X^7 + 63*X^6 + 50*X^5 + 17*X^4 + 47*X^3 +
      2*X^2 + 2*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s92 : XPow fSeventeenB2 2736490347303666508
    (6*X^33 + 65*X^32 + 63*X^31 + 47*X^30 + 53*X^29 + 20*X^28 + 18*X^27 + 33*X^26 + 43*X^25 + 58*X^24 +
      23*X^23 + 56*X^22 + 66*X^21 + 23*X^20 + 11*X^19 + 27*X^18 + 52*X^17 + 41*X^16 + 38*X^15 +
      44*X^14 + 39*X^13 + 64*X^12 + 22*X^10 + 42*X^9 + 15*X^8 + 34*X^7 + 21*X^6 + 48*X^5 + 30*X^4 +
      43*X^3 + 16*X^2 + 57*X + 37) :=
  sq_step (by norm_num) pSeventeenB2s91 ⟨
    14*X^32 + 45*X^31 + 5*X^30 + 63*X^29 + 34*X^28 + 3*X^27 + 29*X^26 + 2*X^25 + 61*X^24 + 10*X^23 +
      63*X^22 + 14*X^21 + 24*X^20 + 30*X^19 + 50*X^18 + 64*X^17 + 24*X^16 + 36*X^15 + 17*X^14 +
      14*X^13 + 24*X^12 + 3*X^11 + 64*X^10 + 36*X^9 + 16*X^8 + 42*X^7 + 30*X^6 + 48*X^5 + 58*X^4 +
      66*X^3 + 5*X^2 + 11*X + 24,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s93 : XPow fSeventeenB2 5472980694607333016
    (27*X^33 + 25*X^32 + 26*X^31 + 37*X^30 + 29*X^29 + 17*X^28 + X^27 + 35*X^26 + 17*X^25 + 27*X^24 +
      25*X^23 + 38*X^22 + 42*X^21 + 39*X^20 + 47*X^19 + 66*X^18 + 40*X^17 + 11*X^16 + 26*X^15 +
      41*X^14 + 42*X^13 + 38*X^12 + 9*X^11 + 33*X^10 + 31*X^9 + 57*X^8 + 5*X^7 + 11*X^6 + 66*X^5 +
      3*X^4 + 9*X^3 + 62*X + 62) :=
  sq_step (by norm_num) pSeventeenB2s92 ⟨
    36*X^32 + 8*X^31 + 32*X^30 + 64*X^29 + 12*X^28 + 20*X^27 + 2*X^26 + 23*X^25 + 28*X^24 + 52*X^23 +
      5*X^22 + 64*X^21 + 40*X^20 + 37*X^19 + X^18 + 20*X^17 + 35*X^16 + 38*X^15 + 25*X^14 + 41*X^13 +
      5*X^12 + 10*X^11 + 58*X^10 + 38*X^9 + 16*X^8 + 27*X^7 + 5*X^6 + 52*X^5 + 42*X^4 + 45*X^3 +
      26*X^2 + X + 26,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s94 : XPow fSeventeenB2 5472980694607333017
    (49*X^33 + 33*X^32 + 44*X^31 + 49*X^30 + 46*X^29 + 56*X^28 + 33*X^27 + 47*X^26 + X^25 + 22*X^24 +
      13*X^23 + 32*X^22 + 29*X^21 + 7*X^20 + 45*X^19 + 28*X^18 + 50*X^17 + 59*X^16 + 26*X^15 +
      18*X^14 + 25*X^13 + 63*X^12 + 57*X^11 + 41*X^10 + 42*X^9 + 46*X^8 + 7*X^7 + 26*X^6 + 41*X^5 +
      54*X^4 + 8*X^3 + 22*X^2 + 48*X + 42) :=
  mul_step (by norm_num) pSeventeenB2s93 pSeventeenB21 ⟨
    27,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s95 : XPow fSeventeenB2 10945961389214666034
    (52*X^33 + 63*X^32 + 19*X^31 + 32*X^30 + 46*X^29 + 9*X^28 + 39*X^27 + 41*X^26 + 23*X^25 + 4*X^24 +
      3*X^23 + 14*X^22 + 8*X^21 + 60*X^20 + 18*X^19 + 37*X^18 + 30*X^17 + 58*X^16 + 43*X^15 +
      11*X^14 + 28*X^13 + 65*X^12 + 42*X^11 + 6*X^10 + 64*X^9 + 13*X^8 + 14*X^7 + 5*X^6 + 49*X^5 +
      60*X^4 + 19*X^3 + 35*X^2 + 44*X + 12) :=
  sq_step (by norm_num) pSeventeenB2s94 ⟨
    56*X^32 + 38*X^31 + 62*X^30 + 11*X^29 + 65*X^28 + 3*X^27 + 26*X^26 + 26*X^25 + 21*X^24 + 20*X^23 +
      15*X^22 + 66*X^21 + 25*X^20 + 38*X^19 + 20*X^18 + 30*X^17 + 32*X^16 + 32*X^15 + 36*X^14 +
      26*X^13 + 31*X^12 + 10*X^11 + 14*X^10 + 14*X^9 + 36*X^8 + 6*X^7 + 62*X^6 + 63*X^5 + 11*X^4 +
      14*X^3 + 45*X^2 + 28*X + 51,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s96 : XPow fSeventeenB2 10945961389214666035
    (5*X^33 + 30*X^32 + 43*X^31 + 20*X^30 + 45*X^29 + X^28 + 57*X^27 + 51*X^26 + 11*X^25 + 27*X^24 +
      13*X^23 + 21*X^22 + 6*X^21 + 3*X^20 + 4*X^19 + 59*X^18 + 14*X^17 + 47*X^16 + 64*X^15 + 19*X^14 +
      35*X^13 + 12*X^12 + 15*X^11 + 51*X^10 + 66*X^9 + 21*X^8 + 37*X^7 + 34*X^6 + 24*X^5 + 61*X^4 +
      38*X^3 + 29*X^2 + 57*X + 66) :=
  mul_step (by norm_num) pSeventeenB2s95 pSeventeenB21 ⟨
    52,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s97 : XPow fSeventeenB2 21891922778429332070
    (32*X^33 + 38*X^32 + 12*X^31 + 57*X^30 + 35*X^29 + 22*X^28 + 61*X^27 + 26*X^26 + 40*X^25 + 3*X^24 +
      2*X^23 + 59*X^22 + 47*X^21 + 57*X^20 + X^19 + 38*X^18 + 13*X^17 + 30*X^16 + 17*X^14 + 55*X^13 +
      24*X^12 + 28*X^11 + 56*X^10 + 24*X^9 + 65*X^8 + 48*X^7 + 56*X^6 + 32*X^5 + 65*X^4 + 21*X^3 +
      59*X^2 + 17*X + 62) :=
  sq_step (by norm_num) pSeventeenB2s96 ⟨
    25*X^32 + 17*X^31 + 24*X^30 + 28*X^29 + 7*X^28 + 20*X^27 + 31*X^26 + 14*X^25 + 8*X^23 + 11*X^22 +
      53*X^21 + 20*X^20 + 50*X^19 + 15*X^18 + 14*X^17 + 60*X^16 + 55*X^15 + 18*X^14 + 44*X^13 +
      30*X^12 + 18*X^11 + 39*X^10 + 65*X^9 + 30*X^8 + 29*X^7 + 18*X^6 + 52*X^5 + 49*X^4 + 35*X^3 +
      39*X^2 + 59*X + 44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s98 : XPow fSeventeenB2 21891922778429332071
    (59*X^33 + 60*X^32 + 38*X^31 + 19*X^30 + 39*X^29 + 17*X^28 + 41*X^27 + 16*X^26 + 64*X^25 + 58*X^24 +
      12*X^23 + 55*X^22 + 65*X^21 + 33*X^20 + 28*X^19 + 36*X^18 + 39*X^17 + 54*X^16 + 29*X^15 +
      34*X^14 + 21*X^13 + 25*X^12 + 10*X^11 + 16*X^10 + 10*X^9 + 42*X^8 + 19*X^7 + 64*X^6 + 48*X^5 +
      52*X^4 + 66*X^3 + 49*X^2 + 33*X + 20) :=
  mul_step (by norm_num) pSeventeenB2s97 pSeventeenB21 ⟨
    32,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s99 : XPow fSeventeenB2 43783845556858664142
    (54*X^33 + 65*X^32 + 27*X^31 + 53*X^30 + 60*X^29 + 28*X^28 + 28*X^27 + 5*X^26 + X^25 + 9*X^24 +
      16*X^23 + 33*X^22 + 61*X^21 + 21*X^20 + 13*X^19 + 10*X^18 + 42*X^17 + 14*X^16 + 19*X^15 +
      41*X^14 + 49*X^13 + 61*X^12 + 16*X^11 + 55*X^10 + 45*X^9 + 29*X^8 + 53*X^7 + 23*X^6 + 55*X^5 +
      33*X^4 + 59*X^3 + 25*X^2 + 44*X + 24) :=
  sq_step (by norm_num) pSeventeenB2s98 ⟨
    64*X^32 + 20*X^31 + 61*X^30 + 44*X^29 + 61*X^28 + 54*X^27 + 58*X^26 + 13*X^25 + 64*X^24 + 26*X^23 +
      13*X^22 + 61*X^21 + 64*X^20 + 54*X^19 + 11*X^18 + 35*X^17 + 42*X^16 + 15*X^15 + 23*X^14 +
      53*X^13 + 59*X^12 + 66*X^11 + 64*X^10 + 51*X^9 + 34*X^8 + X^7 + 45*X^6 + 51*X^4 + 55*X^3 +
      51*X^2 + 18*X + 55,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s100 : XPow fSeventeenB2 87567691113717328284
    (20*X^33 + 2*X^32 + 40*X^31 + 48*X^30 + 17*X^29 + 34*X^28 + 48*X^27 + X^26 + 61*X^25 + 53*X^24 +
      6*X^23 + 47*X^22 + 64*X^21 + 8*X^20 + 13*X^19 + 22*X^18 + 19*X^17 + 16*X^16 + 60*X^15 +
      51*X^14 + 66*X^13 + 36*X^12 + 28*X^11 + 28*X^10 + 41*X^9 + 38*X^8 + 15*X^7 + 2*X^6 + 2*X^5 +
      15*X^4 + 56*X^3 + 59*X^2 + 25*X + 7) :=
  sq_step (by norm_num) pSeventeenB2s99 ⟨
    35*X^32 + 31*X^31 + 26*X^30 + 58*X^29 + 22*X^28 + 38*X^27 + 10*X^26 + 66*X^25 + 42*X^23 + 37*X^22 +
      43*X^21 + 40*X^20 + 28*X^19 + 50*X^18 + 25*X^17 + 55*X^16 + 39*X^15 + 32*X^14 + 43*X^13 +
      65*X^11 + 44*X^10 + 6*X^9 + 14*X^8 + 45*X^7 + 64*X^6 + 16*X^5 + 53*X^4 + 8*X^3 + 25*X^2 + 20*X +
      41,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s101 : XPow fSeventeenB2 175135382227434656568
    (63*X^33 + 63*X^32 + 23*X^31 + 17*X^30 + 4*X^29 + 30*X^28 + 41*X^27 + 12*X^26 + 27*X^25 + 10*X^24 +
      24*X^23 + 42*X^22 + 64*X^21 + 48*X^20 + 46*X^19 + 59*X^18 + 53*X^17 + 27*X^16 + 52*X^15 +
      2*X^14 + 32*X^13 + 28*X^12 + 32*X^11 + 61*X^10 + 27*X^9 + 42*X^8 + 21*X^7 + 18*X^6 + 25*X^5 +
      31*X^4 + 42*X^3 + 41*X^2 + 33*X + 17) :=
  sq_step (by norm_num) pSeventeenB2s100 ⟨
    65*X^32 + 41*X^31 + 22*X^30 + 55*X^29 + 22*X^28 + 8*X^27 + 19*X^26 + 27*X^25 + 57*X^24 + 21*X^23 +
      2*X^22 + 42*X^21 + 42*X^20 + 14*X^19 + 57*X^17 + 3*X^16 + 47*X^14 + 39*X^13 + 43*X^12 +
      38*X^11 + X^10 + 60*X^9 + 62*X^8 + 57*X^7 + 54*X^6 + 53*X^5 + 58*X^4 + 36*X^3 + 45*X^2 + 43*X +
      56,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s102 : XPow fSeventeenB2 350270764454869313136
    (44*X^33 + 51*X^32 + 28*X^31 + 16*X^30 + 11*X^29 + 36*X^28 + 10*X^27 + 28*X^26 + 11*X^25 + 29*X^24 +
      3*X^23 + 28*X^22 + 41*X^21 + 66*X^20 + 19*X^19 + 10*X^18 + 31*X^17 + 18*X^16 + 66*X^15 +
      27*X^14 + 44*X^13 + 53*X^12 + 22*X^11 + 15*X^10 + 13*X^9 + 47*X^8 + 58*X^7 + 54*X^6 + 6*X^5 +
      3*X^4 + 32*X^3 + 13*X^2 + 42*X + 18) :=
  sq_step (by norm_num) pSeventeenB2s101 ⟨
    16*X^32 + 9*X^31 + 65*X^30 + 47*X^29 + 7*X^28 + 48*X^27 + 62*X^26 + 30*X^25 + 39*X^24 + 15*X^23 +
      28*X^22 + 24*X^21 + 3*X^20 + 23*X^19 + 42*X^18 + 55*X^17 + 9*X^16 + 11*X^15 + 36*X^14 +
      33*X^13 + 51*X^12 + 26*X^11 + 5*X^10 + 6*X^9 + 59*X^8 + 56*X^7 + 5*X^6 + 33*X^5 + 53*X^4 +
      44*X^3 + 28*X^2 + 66*X + 22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s103 : XPow fSeventeenB2 700541528909738626272
    (24*X^33 + 49*X^32 + 33*X^31 + 59*X^30 + 58*X^29 + 18*X^28 + 7*X^27 + 29*X^26 + 26*X^25 + 65*X^24 +
      16*X^23 + 37*X^21 + 22*X^20 + 14*X^19 + 39*X^18 + 6*X^17 + 21*X^16 + 24*X^15 + 36*X^14 +
      20*X^13 + 8*X^12 + 19*X^11 + 26*X^10 + 28*X^9 + 59*X^8 + 12*X^7 + 62*X^6 + 12*X^5 + 36*X^4 +
      46*X^3 + X^2 + 5*X + 19) :=
  sq_step (by norm_num) pSeventeenB2s102 ⟨
    60*X^32 + 30*X^31 + 45*X^30 + 17*X^29 + 46*X^28 + 54*X^27 + 63*X^26 + 24*X^25 + 36*X^24 + 48*X^23 +
      58*X^22 + 38*X^21 + 56*X^20 + 31*X^19 + 43*X^18 + 10*X^17 + 14*X^16 + 33*X^15 + 40*X^14 +
      13*X^13 + 52*X^12 + 33*X^11 + 25*X^10 + 54*X^9 + 59*X^8 + 17*X^7 + 35*X^6 + 51*X^5 + 22*X^4 +
      66*X^3 + 4*X^2 + 57*X + 48,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s104 : XPow fSeventeenB2 700541528909738626273
    (48*X^33 + 2*X^32 + 28*X^31 + 46*X^30 + 14*X^29 + 41*X^28 + 57*X^27 + 8*X^26 + 27*X^25 + 58*X^24 +
      15*X^23 + 43*X^22 + 28*X^21 + 38*X^20 + 65*X^19 + 40*X^18 + 11*X^17 + 31*X^16 + 45*X^15 +
      21*X^14 + 56*X^13 + 25*X^11 + 22*X^10 + X^9 + 41*X^8 + 51*X^7 + 36*X^6 + 40*X^5 + 19*X^4 +
      23*X^3 + 29*X^2 + 14*X + 15) :=
  mul_step (by norm_num) pSeventeenB2s103 pSeventeenB21 ⟨
    24,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s105 : XPow fSeventeenB2 1401083057819477252546
    (33*X^33 + 11*X^32 + 60*X^31 + 35*X^30 + 20*X^29 + 9*X^28 + 63*X^27 + 61*X^26 + 65*X^25 + 37*X^24 +
      4*X^23 + 40*X^22 + 14*X^21 + 56*X^20 + 26*X^19 + 32*X^18 + 36*X^17 + 11*X^16 + 21*X^15 +
      3*X^14 + 27*X^13 + 52*X^12 + 48*X^11 + 17*X^10 + 42*X^9 + 9*X^8 + 5*X^7 + 15*X^6 + 15*X^5 +
      14*X^4 + 8*X^3 + 31*X^2 + 21*X + 53) :=
  sq_step (by norm_num) pSeventeenB2s104 ⟨
    26*X^32 + 29*X^31 + 47*X^30 + 33*X^29 + 8*X^28 + 47*X^27 + 42*X^26 + 29*X^25 + 41*X^24 + 47*X^23 +
      41*X^22 + 10*X^21 + 33*X^20 + 35*X^19 + 11*X^18 + 34*X^17 + 9*X^16 + 62*X^15 + 40*X^14 +
      40*X^13 + 5*X^12 + 63*X^11 + 30*X^10 + 5*X^9 + 7*X^8 + 21*X^7 + 35*X^6 + 48*X^5 + 5*X^4 +
      20*X^3 + 34*X^2 + 56*X + 33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s106 : XPow fSeventeenB2 2802166115638954505092
    (58*X^33 + 55*X^32 + 57*X^31 + 9*X^30 + 65*X^29 + 34*X^28 + 13*X^27 + 39*X^26 + 27*X^25 + 35*X^24 +
      23*X^23 + 43*X^22 + 54*X^21 + 30*X^20 + 18*X^19 + 18*X^18 + 15*X^17 + 38*X^16 + 64*X^15 +
      53*X^14 + 53*X^13 + 62*X^12 + 32*X^11 + 14*X^10 + 23*X^9 + 38*X^8 + 19*X^7 + 17*X^6 + 23*X^5 +
      10*X^4 + 40*X^3 + 3*X^2 + 16*X + 43) :=
  sq_step (by norm_num) pSeventeenB2s105 ⟨
    17*X^32 + 19*X^31 + 55*X^30 + 33*X^29 + 4*X^28 + 27*X^27 + 53*X^26 + 43*X^25 + 29*X^24 + 5*X^23 +
      8*X^22 + 42*X^21 + 35*X^20 + 19*X^19 + 29*X^18 + 8*X^17 + 13*X^16 + 39*X^15 + 53*X^14 +
      47*X^13 + 4*X^12 + 31*X^11 + 54*X^10 + 29*X^9 + 44*X^8 + 52*X^7 + 51*X^6 + 17*X^5 + 43*X^4 +
      14*X^3 + 23*X^2 + 54*X + 50,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s107 : XPow fSeventeenB2 2802166115638954505093
    (47*X^33 + 10*X^32 + 29*X^31 + 36*X^30 + 2*X^29 + 17*X^28 + 62*X^27 + 17*X^26 + 66*X^25 + 24*X^24 +
      29*X^23 + 35*X^22 + 11*X^21 + 9*X^20 + 25*X^19 + 19*X^18 + 25*X^17 + 53*X^16 + 58*X^15 +
      61*X^14 + 44*X^13 + 14*X^12 + 6*X^11 + 42*X^10 + 43*X^9 + 50*X^8 + 63*X^7 + 14*X^6 + 42*X^5 +
      25*X^4 + 45*X^3 + 7*X^2 + 3*X + 53) :=
  mul_step (by norm_num) pSeventeenB2s106 pSeventeenB21 ⟨
    58,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s108 : XPow fSeventeenB2 5604332231277909010186
    (4*X^33 + 25*X^32 + 31*X^31 + 3*X^30 + 29*X^29 + 44*X^28 + 28*X^27 + 39*X^26 + 18*X^25 + 19*X^24 +
      14*X^23 + 7*X^22 + 61*X^21 + 28*X^20 + 64*X^19 + 2*X^18 + 41*X^17 + 26*X^16 + 5*X^15 + 56*X^14 +
      54*X^13 + 51*X^12 + 50*X^11 + 16*X^10 + 41*X^9 + 43*X^8 + 31*X^7 + 14*X^6 + 61*X^5 + 39*X^4 +
      44*X^3 + 35*X^2 + 58*X + 25) :=
  sq_step (by norm_num) pSeventeenB2s107 ⟨
    65*X^32 + 30*X^31 + 58*X^30 + 45*X^29 + 46*X^28 + 17*X^27 + 27*X^26 + 41*X^25 + 16*X^24 + 62*X^23 +
      24*X^22 + 29*X^21 + 46*X^20 + 59*X^19 + 12*X^18 + 40*X^17 + 66*X^16 + 50*X^15 + 20*X^14 +
      33*X^13 + 5*X^12 + 29*X^11 + 50*X^10 + 3*X^9 + 53*X^8 + 59*X^7 + 24*X^6 + 39*X^5 + 64*X^4 +
      45*X^3 + 20*X^2 + 2*X + 48,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s109 : XPow fSeventeenB2 11208664462555818020372
    (6*X^33 + 48*X^32 + 2*X^31 + 22*X^30 + 47*X^29 + 44*X^28 + 25*X^27 + 20*X^26 + 19*X^25 + 65*X^24 +
      14*X^23 + 49*X^22 + 27*X^21 + 54*X^20 + 19*X^19 + 18*X^18 + 17*X^17 + 4*X^16 + 5*X^15 +
      45*X^14 + 66*X^13 + 18*X^12 + X^11 + 54*X^10 + 44*X^9 + 21*X^8 + 32*X^7 + 3*X^6 + 44*X^5 +
      31*X^4 + 23*X^3 + 10*X^2 + 30*X + 1) :=
  sq_step (by norm_num) pSeventeenB2s108 ⟨
    16*X^32 + 43*X^31 + 27*X^30 + 45*X^29 + 6*X^28 + 56*X^27 + 8*X^26 + 19*X^25 + 46*X^24 + 23*X^23 +
      51*X^22 + 61*X^21 + 50*X^20 + 18*X^19 + 32*X^18 + 38*X^17 + 65*X^16 + 2*X^15 + 37*X^14 +
      61*X^13 + X^12 + 47*X^11 + 57*X^10 + 22*X^9 + 62*X^8 + 59*X^7 + 3*X^6 + 52*X^5 + 2*X^4 +
      11*X^3 + 9*X^2 + 60*X + 20,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s110 : XPow fSeventeenB2 22417328925111636040744
    (27*X^33 + 56*X^32 + 29*X^31 + 59*X^30 + 45*X^29 + 12*X^28 + 4*X^27 + 62*X^26 + 41*X^25 + 60*X^24 +
      57*X^23 + 61*X^22 + 62*X^21 + 7*X^20 + 24*X^19 + 38*X^18 + 33*X^17 + 40*X^16 + 21*X^15 +
      15*X^14 + 4*X^13 + 3*X^12 + 54*X^11 + 38*X^10 + 41*X^9 + 60*X^8 + 60*X^7 + 23*X^6 + 53*X^5 +
      50*X^4 + 48*X^3 + 30*X^2 + 66*X + 7) :=
  sq_step (by norm_num) pSeventeenB2s109 ⟨
    36*X^32 + 5*X^31 + 34*X^30 + 8*X^29 + 29*X^28 + 53*X^27 + 9*X^26 + 35*X^25 + 33*X^24 + 18*X^23 +
      65*X^22 + 49*X^21 + 38*X^20 + 22*X^19 + 7*X^18 + 18*X^17 + 31*X^16 + 20*X^15 + 59*X^14 +
      31*X^13 + 5*X^12 + 4*X^11 + 30*X^10 + 63*X^9 + 43*X^8 + 19*X^7 + 28*X^6 + 33*X^5 + 35*X^4 +
      X^3 + 13*X^2 + 53*X + 23,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s111 : XPow fSeventeenB2 22417328925111636040745
    (13*X^33 + 36*X^32 + 66*X^31 + 65*X^30 + 41*X^29 + 59*X^28 + 60*X^27 + 4*X^26 + 34*X^25 + 54*X^24 +
      36*X^23 + 52*X^22 + 64*X^21 + 51*X^20 + 17*X^19 + 21*X^18 + 12*X^17 + 54*X^16 + 47*X^14 +
      57*X^13 + 41*X^12 + 62*X^11 + 51*X^10 + 45*X^9 + 34*X^8 + 19*X^7 + 13*X^6 + 21*X^5 + 26*X^4 +
      38*X^3 + 26*X^2 + 60*X + 42) :=
  mul_step (by norm_num) pSeventeenB2s110 pSeventeenB21 ⟨
    27,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s112 : XPow fSeventeenB2 44834657850223272081490
    (33*X^33 + 62*X^32 + 53*X^31 + 10*X^30 + 60*X^29 + 16*X^28 + 59*X^27 + 64*X^26 + 58*X^25 + X^24 +
      20*X^23 + 39*X^22 + 10*X^21 + 52*X^20 + 47*X^19 + 30*X^18 + 50*X^17 + 50*X^16 + 8*X^15 +
      62*X^14 + 60*X^13 + 12*X^12 + 57*X^11 + 26*X^10 + 21*X^9 + 27*X^8 + 66*X^7 + 55*X^6 + 51*X^5 +
      65*X^4 + 16*X^3 + 49*X^2 + 35*X + 23) :=
  sq_step (by norm_num) pSeventeenB2s111 ⟨
    35*X^32 + 44*X^31 + 3*X^30 + 53*X^29 + 33*X^28 + 53*X^27 + 49*X^26 + 32*X^25 + 62*X^24 + 38*X^23 +
      12*X^22 + 42*X^21 + 21*X^20 + 64*X^19 + 8*X^18 + 10*X^17 + 36*X^16 + 40*X^15 + 28*X^14 +
      42*X^13 + 50*X^12 + 54*X^11 + 10*X^10 + 55*X^9 + 2*X^8 + 9*X^7 + 29*X^6 + 31*X^5 + 2*X^4 + X^3 +
      36*X^2 + 37*X + 15,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s113 : XPow fSeventeenB2 44834657850223272081491
    (2*X^33 + 2*X^32 + 26*X^31 + 10*X^30 + 44*X^29 + 22*X^28 + 2*X^27 + 50*X^26 + 66*X^25 + 61*X^24 +
      X^23 + 35*X^22 + 10*X^21 + 13*X^20 + 49*X^19 + 13*X^18 + 53*X^17 + 26*X^16 + 66*X^15 + 53*X^14 +
      11*X^13 + 56*X^12 + 33*X^11 + 63*X^10 + 31*X^9 + 64*X^8 + 65*X^7 + 17*X^6 + 37*X^5 + 4*X^4 +
      29*X^3 + X^2 + 58*X + 29) :=
  mul_step (by norm_num) pSeventeenB2s112 pSeventeenB21 ⟨
    33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s114 : XPow fSeventeenB2 89669315700446544162982
    (52*X^33 + 9*X^32 + 21*X^31 + 13*X^30 + 22*X^29 + 58*X^28 + 59*X^27 + 55*X^26 + 16*X^25 + 39*X^24 +
      43*X^23 + 17*X^22 + 54*X^21 + 16*X^20 + 53*X^19 + 65*X^18 + 25*X^17 + 11*X^16 + 5*X^15 +
      36*X^14 + 18*X^13 + 55*X^12 + 61*X^11 + 47*X^10 + 47*X^9 + 45*X^8 + 42*X^7 + 46*X^6 + 12*X^5 +
      37*X^4 + 42*X^3 + 51*X^2 + 25*X + 17) :=
  sq_step (by norm_num) pSeventeenB2s113 ⟨
    4*X^32 + 19*X^31 + 49*X^30 + 62*X^29 + 57*X^28 + 53*X^27 + 56*X^26 + 3*X^25 + 50*X^24 + 44*X^23 +
      8*X^22 + 22*X^21 + 53*X^20 + 21*X^19 + 46*X^18 + 61*X^17 + 40*X^16 + 36*X^15 + 47*X^14 +
      2*X^13 + X^12 + 39*X^11 + 61*X^10 + 14*X^9 + 62*X^8 + 56*X^7 + 37*X^6 + 46*X^5 + 31*X^4 +
      17*X^3 + 8*X^2 + 65*X + 35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s115 : XPow fSeventeenB2 179338631400893088325964
    (55*X^33 + 30*X^32 + 65*X^31 + 5*X^30 + 66*X^29 + 13*X^28 + 54*X^27 + 48*X^26 + 42*X^25 + 57*X^24 +
      34*X^23 + 58*X^22 + 11*X^21 + 6*X^20 + 6*X^19 + 22*X^18 + 13*X^17 + 26*X^16 + X^15 + 66*X^13 +
      10*X^12 + 12*X^11 + 39*X^10 + 52*X^9 + 43*X^8 + 51*X^7 + 49*X^5 + 19*X^4 + 2*X^3 + 37*X^2 +
      34*X + 36) :=
  sq_step (by norm_num) pSeventeenB2s114 ⟨
    24*X^32 + 64*X^31 + 65*X^30 + 14*X^29 + 34*X^28 + 48*X^27 + 37*X^26 + 60*X^25 + 14*X^24 + 50*X^23 +
      20*X^22 + 54*X^21 + 66*X^20 + 55*X^19 + 62*X^18 + 47*X^17 + 62*X^16 + 56*X^15 + 24*X^13 +
      40*X^12 + 16*X^11 + 30*X^10 + 36*X^9 + 16*X^8 + 14*X^7 + 9*X^6 + 19*X^5 + 65*X^4 + 57*X^3 +
      17*X^2 + 29*X + 24,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s116 : XPow fSeventeenB2 179338631400893088325965
    (64*X^33 + 47*X^32 + 54*X^31 + 5*X^30 + 15*X^29 + 37*X^28 + 34*X^27 + 51*X^26 + 9*X^25 + 13*X^24 +
      17*X^23 + 8*X^22 + 3*X^21 + 61*X^20 + 9*X^19 + 63*X^18 + 31*X^17 + 31*X^16 + 29*X^15 + 32*X^14 +
      53*X^13 + 55*X^12 + 6*X^11 + 55*X^10 + 5*X^9 + 3*X^8 + 39*X^7 + 37*X^6 + 17*X^5 + 49*X^4 +
      26*X^3 + 22*X^2 + 5*X + 26) :=
  mul_step (by norm_num) pSeventeenB2s115 pSeventeenB21 ⟨
    55,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s117 : XPow fSeventeenB2 358677262801786176651930
    (3*X^33 + 10*X^32 + 30*X^31 + 14*X^30 + 35*X^29 + 4*X^28 + 15*X^27 + 43*X^26 + 42*X^25 + 9*X^24 +
      53*X^23 + 66*X^22 + 44*X^21 + 7*X^20 + 46*X^19 + 63*X^18 + 3*X^17 + 55*X^16 + 28*X^15 +
      57*X^14 + 26*X^13 + 32*X^12 + 52*X^11 + 53*X^10 + 58*X^9 + 23*X^8 + 13*X^7 + 17*X^6 + 38*X^5 +
      61*X^4 + 55*X^3 + 11*X^2 + 25*X) :=
  sq_step (by norm_num) pSeventeenB2s116 ⟨
    9*X^32 + 61*X^31 + 6*X^30 + 42*X^29 + 57*X^28 + 32*X^27 + 24*X^26 + 13*X^25 + 41*X^24 + 53*X^23 +
      30*X^22 + 52*X^21 + 48*X^20 + 22*X^19 + 57*X^18 + 43*X^17 + 26*X^16 + 29*X^14 + 25*X^13 +
      8*X^12 + 28*X^11 + 52*X^10 + 63*X^9 + 33*X^8 + 37*X^7 + 12*X^6 + 15*X^5 + 53*X^4 + 43*X^3 +
      14*X^2 + 63*X + 44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s118 : XPow fSeventeenB2 358677262801786176651931
    (35*X^33 + X^32 + 52*X^31 + 37*X^29 + 36*X^28 + 13*X^27 + 23*X^26 + 21*X^25 + 8*X^24 + 26*X^23 +
      28*X^22 + 58*X^21 + 49*X^20 + 16*X^19 + 24*X^18 + 37*X^17 + 54*X^16 + 33*X^15 + X^14 + 38*X^13 +
      58*X^12 + 11*X^11 + 7*X^10 + 66*X^9 + 25*X^8 + 24*X^7 + 41*X^6 + 28*X^5 + 60*X^4 + 64*X^3 +
      28*X^2 + 58*X + 27) :=
  mul_step (by norm_num) pSeventeenB2s117 pSeventeenB21 ⟨
    3,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s119 : XPow fSeventeenB2 717354525603572353303862
    (10*X^33 + 33*X^32 + 33*X^31 + 39*X^30 + 37*X^29 + 19*X^28 + 46*X^27 + 40*X^26 + 37*X^25 + 29*X^24 +
      11*X^23 + 7*X^22 + 24*X^21 + 11*X^20 + 22*X^19 + 13*X^18 + 16*X^17 + 18*X^16 + 28*X^15 +
      38*X^14 + 53*X^13 + 35*X^12 + 10*X^11 + 41*X^10 + 41*X^9 + 7*X^8 + 57*X^7 + 33*X^6 + 8*X^5 +
      37*X^4 + 28*X^3 + 38*X^2 + 27*X + 36) :=
  sq_step (by norm_num) pSeventeenB2s118 ⟨
    19*X^32 + 5*X^31 + 15*X^30 + 64*X^29 + 30*X^28 + 20*X^27 + 14*X^26 + 11*X^25 + 23*X^24 + 17*X^23 +
      20*X^22 + 32*X^21 + 40*X^20 + 5*X^19 + 21*X^18 + 58*X^17 + 28*X^16 + 38*X^15 + 13*X^14 +
      41*X^13 + 61*X^12 + 20*X^11 + 60*X^10 + 13*X^9 + 35*X^8 + 2*X^7 + 29*X^6 + 59*X^5 + 27*X^4 +
      42*X^3 + 10*X^2 + 9*X + 57,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s120 : XPow fSeventeenB2 717354525603572353303863
    (27*X^33 + 48*X^32 + 54*X^31 + 32*X^30 + 62*X^29 + 49*X^28 + 7*X^27 + 63*X^26 + 2*X^25 + 62*X^24 +
      30*X^23 + 60*X^22 + 47*X^21 + 32*X^20 + 35*X^19 + 19*X^18 + 25*X^17 + 3*X^16 + 25*X^15 +
      59*X^14 + 55*X^13 + 30*X^12 + 35*X^11 + 5*X^10 + 61*X^9 + 30*X^8 + 34*X^7 + 18*X^6 + 61*X^5 +
      36*X^3 + 37*X^2 + 6*X + 23) :=
  mul_step (by norm_num) pSeventeenB2s119 pSeventeenB21 ⟨
    10,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s121 : XPow fSeventeenB2 1434709051207144706607726
    (27*X^33 + 28*X^32 + 32*X^31 + 61*X^30 + 56*X^29 + 55*X^28 + 13*X^27 + 42*X^26 + 47*X^25 + 29*X^24 +
      44*X^23 + 43*X^22 + 16*X^21 + 11*X^20 + 9*X^19 + 10*X^18 + 63*X^17 + 40*X^16 + 28*X^15 +
      30*X^14 + 42*X^13 + 12*X^12 + 35*X^11 + 26*X^10 + 62*X^9 + 66*X^8 + 30*X^6 + 13*X^5 + 14*X^4 +
      16*X^3 + 12*X^2 + 31*X + 19) :=
  sq_step (by norm_num) pSeventeenB2s120 ⟨
    59*X^32 + 24*X^31 + 48*X^30 + 33*X^29 + 8*X^28 + 4*X^27 + 27*X^26 + 32*X^25 + 49*X^24 + 11*X^23 +
      52*X^22 + 15*X^21 + 49*X^20 + 29*X^19 + 41*X^18 + 27*X^17 + 8*X^16 + 31*X^15 + 52*X^14 +
      26*X^13 + 53*X^12 + 23*X^11 + 53*X^10 + 9*X^9 + 2*X^8 + 33*X^7 + 54*X^6 + 8*X^5 + 35*X^4 +
      66*X^3 + 20*X^2 + 6*X + 55,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s122 : XPow fSeventeenB2 1434709051207144706607727
    (52*X^33 + 39*X^32 + X^31 + 9*X^30 + 17*X^29 + X^28 + 40*X^27 + 10*X^26 + 3*X^25 + 41*X^24 + 18*X^23 +
      6*X^22 + X^21 + 36*X^20 + 56*X^19 + 51*X^18 + 12*X^17 + 61*X^16 + 15*X^15 + 18*X^14 + 66*X^13 +
      22*X^12 + 50*X^11 + 5*X^10 + 51*X^9 + 41*X^8 + 26*X^7 + 40*X^6 + 52*X^5 + 61*X^4 + 20*X^3 +
      58*X^2 + 5*X + 42) :=
  mul_step (by norm_num) pSeventeenB2s121 pSeventeenB21 ⟨
    27,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s123 : XPow fSeventeenB2 2869418102414289413215454
    (21*X^33 + 65*X^32 + 7*X^31 + 39*X^30 + 65*X^29 + 49*X^28 + 26*X^27 + 5*X^26 + 50*X^25 + 8*X^24 +
      15*X^23 + 62*X^22 + 9*X^21 + 20*X^20 + 42*X^19 + 24*X^18 + 45*X^17 + X^16 + 2*X^15 + 51*X^14 +
      11*X^13 + 36*X^11 + 31*X^10 + 17*X^9 + 61*X^8 + 25*X^7 + 8*X^6 + 31*X^5 + 53*X^3 + 29*X^2 +
      59*X + 28) :=
  sq_step (by norm_num) pSeventeenB2s122 ⟨
    24*X^32 + 35*X^31 + 32*X^30 + 18*X^29 + 63*X^28 + 50*X^27 + 57*X^26 + 54*X^24 + 3*X^23 + 59*X^22 +
      53*X^21 + 63*X^20 + X^19 + 51*X^18 + 15*X^17 + 61*X^16 + 62*X^15 + 41*X^14 + 39*X^13 + 19*X^12 +
      53*X^11 + 41*X^10 + 20*X^9 + 26*X^8 + 39*X^7 + 11*X^6 + 46*X^5 + 49*X^4 + 62*X^3 + 14*X^2 +
      42*X + 23,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s124 : XPow fSeventeenB2 5738836204828578826430908
    (60*X^33 + 34*X^32 + 55*X^31 + 15*X^30 + 59*X^29 + 60*X^28 + 59*X^27 + 23*X^26 + 28*X^25 + 13*X^24 +
      48*X^23 + 56*X^22 + 36*X^21 + 15*X^20 + 46*X^19 + 35*X^18 + 66*X^17 + 31*X^16 + 54*X^14 +
      58*X^13 + 5*X^12 + 49*X^11 + 18*X^10 + 28*X^9 + 62*X^8 + 8*X^7 + 35*X^6 + 26*X^5 + 24*X^4 +
      20*X^3 + 59*X^2 + 2*X + 40) :=
  sq_step (by norm_num) pSeventeenB2s123 ⟨
    39*X^32 + 40*X^31 + 31*X^30 + 55*X^29 + 64*X^28 + 43*X^27 + 50*X^26 + 32*X^25 + 41*X^24 + 25*X^23 +
      41*X^22 + 45*X^21 + 2*X^20 + 25*X^19 + 32*X^18 + 54*X^17 + 59*X^16 + 66*X^15 + 62*X^14 + X^13 +
      62*X^12 + 12*X^11 + 2*X^10 + 62*X^9 + 37*X^8 + 7*X^7 + 3*X^6 + 41*X^5 + 49*X^4 + 30*X^3 +
      59*X^2 + 15*X + 29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s125 : XPow fSeventeenB2 5738836204828578826430909
    (65*X^33 + 11*X^32 + 38*X^31 + 29*X^30 + 50*X^29 + 10*X^28 + 26*X^27 + 50*X^26 + 52*X^25 + 19*X^24 +
      60*X^23 + 51*X^22 + 30*X^21 + 39*X^20 + 33*X^19 + 17*X^18 + 6*X^17 + 51*X^16 + 43*X^15 +
      27*X^14 + 58*X^13 + 35*X^12 + 49*X^11 + 13*X^10 + 51*X^9 + 47*X^8 + 41*X^7 + 19*X^6 + 34*X^5 +
      53*X^4 + 47*X^3 + 62*X^2 + 61*X + 4) :=
  mul_step (by norm_num) pSeventeenB2s124 pSeventeenB21 ⟨
    60,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s126 : XPow fSeventeenB2 11477672409657157652861818
    (51*X^33 + 9*X^32 + 37*X^31 + 52*X^30 + 48*X^29 + 3*X^28 + 32*X^27 + 19*X^26 + 29*X^25 + 6*X^24 +
      43*X^23 + 54*X^22 + 40*X^21 + 36*X^20 + 48*X^19 + 24*X^18 + 25*X^17 + 24*X^16 + 17*X^15 +
      57*X^14 + 18*X^13 + 15*X^12 + 54*X^11 + 17*X^10 + 41*X^9 + 48*X^8 + 27*X^7 + 30*X^6 + 54*X^5 +
      10*X^4 + 48*X^3 + 58*X^2 + 37*X + 23) :=
  sq_step (by norm_num) pSeventeenB2s125 ⟨
    4*X^32 + 34*X^31 + 35*X^30 + 19*X^29 + 9*X^28 + 30*X^27 + 40*X^26 + 17*X^25 + 59*X^24 + 61*X^23 +
      27*X^22 + 63*X^21 + 32*X^20 + 44*X^19 + 49*X^18 + 53*X^17 + 65*X^16 + 62*X^15 + 17*X^14 +
      41*X^13 + 61*X^11 + 13*X^10 + 63*X^9 + 21*X^8 + 17*X^7 + 21*X^6 + 64*X^5 + 21*X^4 + 42*X^3 +
      15*X^2 + 37*X + 38,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s127 : XPow fSeventeenB2 11477672409657157652861819
    (32*X^33 + 13*X^32 + 28*X^31 + 56*X^30 + 28*X^29 + 54*X^28 + 45*X^27 + 41*X^26 + 9*X^25 + 15*X^24 +
      44*X^23 + 36*X^22 + 32*X^21 + 32*X^20 + 29*X^19 + 47*X^18 + 53*X^17 + 57*X^16 + 51*X^15 +
      62*X^14 + 50*X^13 + 22*X^12 + 40*X^11 + 45*X^10 + 42*X^9 + 30*X^8 + 15*X^7 + 38*X^6 + 52*X^5 +
      66*X^4 + 21*X^3 + 21*X^2 + 4*X + 57) :=
  mul_step (by norm_num) pSeventeenB2s126 pSeventeenB21 ⟨
    51,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s128 : XPow fSeventeenB2 22955344819314315305723638
    (32*X^33 + 39*X^32 + 52*X^31 + 64*X^30 + 27*X^29 + 20*X^28 + 20*X^27 + 21*X^26 + 15*X^25 + 13*X^24 +
      63*X^23 + 14*X^22 + 33*X^21 + 37*X^20 + 48*X^19 + 58*X^18 + 3*X^17 + 8*X^16 + 2*X^15 + 5*X^14 +
      54*X^13 + 4*X^12 + 64*X^11 + 25*X^10 + 6*X^9 + 31*X^8 + 17*X^7 + 60*X^6 + 3*X^5 + 9*X^4 +
      11*X^3 + 15*X^2 + 51*X + 13) :=
  sq_step (by norm_num) pSeventeenB2s127 ⟨
    19*X^32 + 30*X^31 + 62*X^30 + 40*X^28 + 12*X^27 + 66*X^26 + 28*X^25 + 15*X^24 + 63*X^23 + 23*X^22 +
      16*X^21 + 28*X^20 + 57*X^19 + 31*X^18 + 14*X^17 + 43*X^16 + 52*X^15 + 30*X^14 + 29*X^13 +
      54*X^12 + 8*X^11 + 60*X^10 + 9*X^9 + 6*X^8 + 49*X^7 + 4*X^6 + 57*X^5 + 41*X^4 + 7*X^3 + 39*X^2 +
      56*X + 35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s129 : XPow fSeventeenB2 45910689638628630611447276
    (31*X^33 + 65*X^32 + 13*X^31 + 36*X^30 + 38*X^29 + 58*X^28 + 61*X^27 + 44*X^26 + 47*X^25 + 32*X^24 +
      35*X^23 + 13*X^22 + 6*X^21 + 66*X^20 + 44*X^19 + 45*X^18 + 12*X^17 + 27*X^16 + 10*X^15 +
      66*X^14 + 9*X^13 + 42*X^12 + 64*X^11 + 58*X^10 + 28*X^9 + 40*X^8 + 63*X^7 + 61*X^6 + 66*X^5 +
      9*X^4 + 9*X^3 + 29*X^2 + 61*X + 2) :=
  sq_step (by norm_num) pSeventeenB2s128 ⟨
    19*X^32 + 19*X^31 + 22*X^30 + 62*X^29 + 32*X^28 + 37*X^27 + 50*X^26 + 58*X^25 + 12*X^24 + 4*X^23 +
      31*X^22 + 39*X^21 + 7*X^20 + 62*X^19 + 38*X^18 + 35*X^17 + 38*X^16 + 2*X^15 + 48*X^14 +
      43*X^13 + 16*X^12 + 10*X^11 + 43*X^10 + 40*X^9 + 26*X^8 + 6*X^7 + 8*X^6 + 22*X^5 + 58*X^4 +
      12*X^3 + 31*X^2 + 22*X + 41,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s130 : XPow fSeventeenB2 91821379277257261222894552
    (38*X^33 + 66*X^32 + 40*X^31 + 7*X^30 + 18*X^29 + 34*X^28 + 2*X^27 + 32*X^26 + 35*X^25 + 21*X^24 +
      63*X^23 + 15*X^22 + 22*X^21 + 58*X^20 + 31*X^19 + 42*X^18 + 9*X^17 + 27*X^16 + 65*X^15 +
      35*X^14 + X^13 + 7*X^12 + 7*X^11 + 26*X^10 + 11*X^9 + 37*X^8 + 52*X^7 + 8*X^6 + 22*X^5 +
      11*X^4 + 65*X^3 + 64*X^2 + 51*X + 48) :=
  sq_step (by norm_num) pSeventeenB2s129 ⟨
    23*X^32 + 23*X^31 + 20*X^30 + 26*X^29 + 60*X^28 + 65*X^27 + 30*X^26 + 34*X^25 + 61*X^24 + 25*X^23 +
      43*X^22 + 12*X^21 + 12*X^20 + 29*X^19 + 5*X^18 + 44*X^17 + 51*X^16 + 65*X^15 + 37*X^14 +
      29*X^13 + 50*X^12 + 40*X^11 + 38*X^10 + 22*X^9 + 4*X^8 + 41*X^7 + 10*X^6 + 18*X^5 + 58*X^4 +
      9*X^3 + 60*X^2 + 5*X + 57,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s131 : XPow fSeventeenB2 183642758554514522445789104
    (35*X^33 + 46*X^32 + 53*X^31 + 14*X^30 + 19*X^29 + 62*X^28 + 21*X^27 + 47*X^26 + 9*X^25 + 22*X^24 +
      13*X^23 + 6*X^22 + 62*X^21 + 25*X^20 + 19*X^19 + 26*X^18 + 34*X^17 + 48*X^16 + 51*X^15 +
      37*X^14 + 43*X^13 + 41*X^12 + 61*X^11 + 57*X^10 + 63*X^9 + 59*X^8 + 63*X^7 + 59*X^6 + 33*X^5 +
      14*X^4 + 53*X^3 + 11*X^2 + 9*X + 63) :=
  sq_step (by norm_num) pSeventeenB2s130 ⟨
    37*X^32 + 9*X^31 + 56*X^30 + 5*X^29 + 15*X^28 + 42*X^27 + 5*X^26 + 27*X^25 + 36*X^24 + 36*X^23 +
      56*X^22 + 28*X^21 + 2*X^20 + 7*X^19 + 58*X^18 + 13*X^17 + 63*X^16 + 36*X^15 + 34*X^14 +
      55*X^13 + 21*X^12 + 4*X^11 + 13*X^10 + 28*X^9 + 13*X^8 + 19*X^7 + 45*X^6 + 41*X^5 + 25*X^4 +
      62*X^2 + 44*X + 19,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s132 : XPow fSeventeenB2 183642758554514522445789105
    (25*X^33 + 5*X^32 + 33*X^31 + 35*X^30 + 45*X^29 + 65*X^28 + 32*X^27 + 33*X^26 + 28*X^25 + 24*X^24 +
      53*X^23 + 54*X^22 + 17*X^21 + 54*X^20 + 36*X^19 + 11*X^18 + 39*X^17 + 64*X^16 + 25*X^15 +
      64*X^14 + 44*X^13 + 64*X^12 + 36*X^11 + 4*X^10 + 47*X^9 + 2*X^8 + 29*X^7 + X^6 + 31*X^5 +
      22*X^4 + 4*X^3 + 44*X^2 + 25*X + 47) :=
  mul_step (by norm_num) pSeventeenB2s131 pSeventeenB21 ⟨
    35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s133 : XPow fSeventeenB2 367285517109029044891578210
    (64*X^33 + 4*X^32 + 8*X^31 + 60*X^30 + 41*X^29 + 9*X^28 + 28*X^27 + 25*X^26 + 46*X^25 + 47*X^24 +
      43*X^23 + 33*X^22 + 2*X^21 + 46*X^20 + 62*X^19 + 2*X^18 + 41*X^17 + 13*X^16 + 63*X^15 +
      33*X^14 + 47*X^13 + 3*X^12 + 5*X^11 + 32*X^10 + 48*X^9 + 12*X^8 + 15*X^7 + 14*X^6 + 42*X^5 +
      45*X^4 + 35*X^3 + 33*X^2 + 56*X) :=
  sq_step (by norm_num) pSeventeenB2s132 ⟨
    22*X^32 + 9*X^31 + 41*X^30 + 45*X^29 + 41*X^28 + 7*X^27 + 42*X^26 + 20*X^25 + 45*X^24 + 37*X^23 +
      18*X^22 + 6*X^21 + 21*X^20 + 33*X^19 + 3*X^18 + 51*X^17 + 10*X^16 + 28*X^15 + 6*X^14 + 19*X^13 +
      47*X^12 + 28*X^11 + 14*X^10 + 9*X^9 + 19*X^8 + 37*X^7 + 58*X^6 + 34*X^5 + 25*X^4 + 26*X^3 +
      20*X^2 + 38*X + 30,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s134 : XPow fSeventeenB2 367285517109029044891578211
    (46*X^33 + 37*X^32 + 22*X^31 + 9*X^30 + 43*X^29 + 7*X^28 + 55*X^27 + 65*X^26 + 35*X^25 + 21*X^24 +
      6*X^23 + 18*X^22 + 62*X^21 + 59*X^20 + 49*X^19 + 20*X^18 + 31*X^17 + 37*X^16 + 57*X^15 +
      5*X^14 + 64*X^13 + 66*X^12 + 7*X^11 + 32*X^10 + 36*X^9 + 3*X^8 + 7*X^7 + 39*X^6 + 11*X^5 +
      30*X^4 + 47*X^3 + 53*X^2 + 9*X + 40) :=
  mul_step (by norm_num) pSeventeenB2s133 pSeventeenB21 ⟨
    64,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s135 : XPow fSeventeenB2 734571034218058089783156422
    (44*X^33 + 22*X^32 + 44*X^31 + 20*X^30 + 40*X^29 + 19*X^28 + 9*X^27 + 25*X^26 + 12*X^25 + 29*X^23 +
      62*X^22 + 51*X^21 + 39*X^20 + 54*X^19 + 41*X^18 + 61*X^17 + 47*X^16 + 23*X^15 + 20*X^14 +
      9*X^13 + 63*X^12 + 5*X^11 + 24*X^10 + 61*X^9 + 27*X^8 + 23*X^7 + 27*X^6 + 45*X^5 + 43*X^4 +
      22*X^3 + 61*X^2 + 6*X + 8) :=
  sq_step (by norm_num) pSeventeenB2s134 ⟨
    39*X^32 + 44*X^31 + 55*X^30 + 35*X^29 + 55*X^28 + 41*X^27 + 36*X^26 + 55*X^25 + 34*X^24 + 59*X^23 +
      26*X^22 + 48*X^21 + 51*X^20 + 41*X^19 + 49*X^18 + 28*X^17 + 41*X^16 + 64*X^15 + 15*X^14 +
      42*X^13 + 35*X^12 + 52*X^11 + 23*X^10 + 66*X^9 + 34*X^8 + 22*X^7 + 30*X^6 + 8*X^5 + 15*X^4 +
      32*X^3 + 66*X^2 + 23*X + 39,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s136 : XPow fSeventeenB2 734571034218058089783156423
    (9*X^33 + 43*X^32 + 19*X^31 + 18*X^30 + 34*X^29 + 49*X^28 + 54*X^27 + 46*X^26 + 42*X^25 + 39*X^24 +
      56*X^23 + 62*X^22 + 50*X^21 + 31*X^20 + 44*X^19 + 34*X^18 + 51*X^17 + 47*X^16 + 3*X^15 +
      22*X^14 + 17*X^13 + 26*X^12 + 11*X^11 + 50*X^10 + 10*X^9 + 65*X^8 + 18*X^7 + 22*X^6 + 28*X^5 +
      6*X^4 + 12*X^3 + 50*X^2 + 10*X + 61) :=
  mul_step (by norm_num) pSeventeenB2s135 pSeventeenB21 ⟨
    44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s137 : XPow fSeventeenB2 1469142068436116179566312846
    (23*X^33 + 44*X^32 + 12*X^31 + 33*X^30 + 21*X^29 + 44*X^28 + 31*X^26 + 14*X^25 + 32*X^24 + 23*X^23 +
      16*X^22 + 44*X^21 + 66*X^20 + 18*X^19 + 30*X^18 + 29*X^17 + 16*X^16 + 13*X^15 + 49*X^14 + X^13 +
      56*X^12 + 35*X^11 + 9*X^10 + 36*X^9 + 34*X^8 + 2*X^7 + 43*X^6 + 30*X^5 + 35*X^4 + 21*X^3 +
      7*X^2 + 51*X + 29) :=
  sq_step (by norm_num) pSeventeenB2s136 ⟨
    14*X^32 + 42*X^31 + 16*X^30 + 9*X^29 + 63*X^28 + 60*X^27 + 56*X^26 + 43*X^25 + 27*X^24 + 41*X^23 +
      10*X^22 + 10*X^21 + 11*X^20 + 18*X^19 + 47*X^18 + 17*X^17 + 41*X^16 + 9*X^15 + 25*X^14 +
      30*X^13 + 18*X^12 + 20*X^11 + 55*X^10 + 20*X^9 + 62*X^8 + 47*X^7 + 44*X^6 + 40*X^5 + 20*X^4 +
      2*X^3 + 18*X^2 + 51*X + 29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s138 : XPow fSeventeenB2 1469142068436116179566312847
    (57*X^33 + 13*X^32 + 34*X^31 + 43*X^30 + 29*X^29 + 27*X^28 + 2*X^27 + 47*X^26 + 57*X^25 + 13*X^24 +
      22*X^23 + 33*X^22 + 55*X^21 + 41*X^20 + 27*X^19 + 56*X^18 + 12*X^17 + 56*X^16 + 66*X^15 +
      55*X^14 + 35*X^13 + 14*X^12 + 22*X^11 + 47*X^10 + 51*X^9 + 27*X^8 + 52*X^7 + 53*X^6 + 50*X^5 +
      37*X^4 + 56*X^3 + 7*X^2 + 27*X + 6) :=
  mul_step (by norm_num) pSeventeenB2s137 pSeventeenB21 ⟨
    23,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s139 : XPow fSeventeenB2 2938284136872232359132625694
    (33*X^33 + 6*X^32 + X^31 + 34*X^30 + 57*X^29 + 45*X^28 + 28*X^27 + 51*X^26 + 26*X^25 + 40*X^24 +
      51*X^23 + 3*X^22 + 16*X^21 + 9*X^20 + 62*X^19 + 28*X^18 + 56*X^17 + 66*X^16 + 47*X^15 +
      26*X^14 + 58*X^13 + 9*X^12 + 42*X^11 + 42*X^9 + 25*X^8 + 11*X^7 + 4*X^6 + 58*X^5 + 20*X^4 +
      9*X^2 + 56*X + 46) :=
  sq_step (by norm_num) pSeventeenB2s138 ⟨
    33*X^32 + 15*X^31 + 32*X^30 + 50*X^29 + 43*X^28 + 33*X^27 + 18*X^26 + 56*X^25 + 52*X^24 + 66*X^23 +
      24*X^22 + 31*X^21 + 31*X^20 + 2*X^19 + 27*X^18 + 7*X^17 + 21*X^16 + 37*X^15 + 15*X^14 +
      59*X^13 + 34*X^12 + 15*X^11 + 29*X^10 + 4*X^9 + 36*X^8 + 49*X^7 + 10*X^6 + 46*X^5 + 34*X^4 +
      30*X^3 + 50*X + 16,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s140 : XPow fSeventeenB2 5876568273744464718265251388
    (25*X^33 + 17*X^32 + 11*X^31 + 42*X^30 + 66*X^29 + 44*X^28 + 16*X^27 + 9*X^26 + 11*X^25 + 27*X^24 +
      3*X^23 + X^22 + 3*X^21 + 33*X^20 + 39*X^19 + 10*X^18 + 63*X^17 + 11*X^16 + 3*X^15 + 49*X^14 +
      44*X^13 + 25*X^12 + 43*X^11 + 49*X^10 + 14*X^9 + 4*X^8 + 37*X^7 + 9*X^6 + 5*X^5 + 12*X^4 +
      30*X^3 + 45*X^2 + 56*X + 5) :=
  sq_step (by norm_num) pSeventeenB2s139 ⟨
    17*X^32 + 24*X^31 + 26*X^30 + 44*X^29 + 37*X^28 + 29*X^26 + 42*X^25 + 51*X^24 + 36*X^23 + 19*X^22 +
      29*X^21 + 51*X^20 + 2*X^19 + 31*X^18 + 53*X^17 + 66*X^16 + 58*X^15 + 9*X^14 + 52*X^13 +
      58*X^12 + 4*X^11 + 36*X^10 + 48*X^9 + 13*X^8 + 55*X^7 + 41*X^6 + 51*X^5 + 12*X^4 + 54*X^3 +
      21*X^2 + 38*X + 26,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s141 : XPow fSeventeenB2 5876568273744464718265251389
    (2*X^33 + 15*X^32 + 46*X^31 + 20*X^30 + 51*X^29 + 57*X^28 + 27*X^27 + 9*X^26 + 60*X^25 + 30*X^24 +
      25*X^23 + 26*X^22 + 56*X^21 + 64*X^20 + 65*X^19 + 37*X^18 + 62*X^17 + 41*X^16 + 50*X^15 +
      59*X^14 + 8*X^13 + 26*X^12 + 34*X^11 + 58*X^10 + 5*X^9 + 3*X^8 + 45*X^7 + 30*X^6 + 5*X^5 +
      27*X^4 + 40*X^3 + 14*X^2 + 64*X + 24) :=
  mul_step (by norm_num) pSeventeenB2s140 pSeventeenB21 ⟨
    25,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s142 : XPow fSeventeenB2 11753136547488929436530502778
    (22*X^33 + 35*X^32 + 24*X^31 + 38*X^30 + 53*X^29 + 27*X^28 + 18*X^27 + 20*X^26 + 33*X^25 + 4*X^24 +
      45*X^23 + 9*X^22 + 55*X^21 + 2*X^20 + 10*X^19 + 47*X^18 + 25*X^17 + 45*X^16 + 6*X^15 + X^14 +
      3*X^13 + 65*X^12 + 56*X^11 + 66*X^10 + 55*X^9 + 56*X^8 + 19*X^7 + 59*X^6 + 24*X^5 + 25*X^4 +
      41*X^3 + X^2 + 26*X + 4) :=
  sq_step (by norm_num) pSeventeenB2s141 ⟨
    4*X^32 + 4*X^31 + 24*X^30 + 64*X^29 + 54*X^28 + X^27 + 31*X^26 + 59*X^25 + 60*X^24 + 3*X^23 +
      28*X^22 + X^21 + 65*X^20 + 24*X^19 + 65*X^18 + 33*X^17 + 61*X^16 + 28*X^15 + 39*X^14 + 16*X^13 +
      25*X^12 + 56*X^11 + 56*X^10 + 30*X^9 + 36*X^8 + 42*X^7 + 7*X^6 + 4*X^5 + 2*X^4 + 34*X^3 +
      30*X^2 + 25*X + 63,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s143 : XPow fSeventeenB2 11753136547488929436530502779
    (62*X^33 + 57*X^32 + 4*X^31 + 42*X^30 + X^29 + 38*X^28 + X^27 + 50*X^26 + 25*X^25 + 50*X^24 + 6*X^23 +
      27*X^22 + 41*X^21 + 32*X^20 + 15*X^19 + 45*X^18 + 47*X^17 + 18*X^16 + 26*X^15 + 43*X^14 +
      42*X^13 + 33*X^12 + 26*X^11 + 16*X^10 + 14*X^9 + 40*X^8 + 21*X^7 + 46*X^6 + 51*X^5 + 33*X^4 +
      10*X^3 + 48*X^2 + 5*X + 64) :=
  mul_step (by norm_num) pSeventeenB2s142 pSeventeenB21 ⟨
    22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s144 : XPow fSeventeenB2 23506273094977858873061005558
    (24*X^33 + 66*X^32 + 25*X^31 + 11*X^30 + 35*X^29 + 42*X^28 + 62*X^27 + 32*X^26 + 6*X^25 + 57*X^24 +
      6*X^23 + 12*X^22 + 21*X^21 + 63*X^20 + 4*X^19 + 40*X^18 + 37*X^17 + 37*X^16 + 61*X^15 +
      17*X^14 + 34*X^13 + 38*X^12 + 41*X^11 + 2*X^10 + 55*X^9 + 16*X^8 + 34*X^7 + 15*X^6 + 51*X^5 +
      40*X^3 + 49*X^2 + 64*X + 18) :=
  sq_step (by norm_num) pSeventeenB2s143 ⟨
    25*X^32 + 18*X^31 + 13*X^30 + 19*X^29 + 6*X^28 + 32*X^27 + 20*X^26 + 23*X^25 + 13*X^24 + 51*X^23 +
      4*X^22 + 28*X^21 + 33*X^20 + 65*X^19 + 40*X^18 + 44*X^17 + 22*X^15 + 58*X^14 + 26*X^13 +
      35*X^12 + 23*X^11 + 30*X^10 + 65*X^9 + 22*X^8 + 34*X^7 + 27*X^6 + 16*X^5 + 65*X^4 + 12*X^3 +
      58*X^2 + 48*X + 1,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s145 : XPow fSeventeenB2 23506273094977858873061005559
    (65*X^33 + 61*X^32 + 47*X^31 + 23*X^30 + 38*X^29 + 29*X^28 + 60*X^27 + 55*X^26 + 19*X^25 + 48*X^24 +
      27*X^23 + 27*X^22 + 2*X^21 + 28*X^20 + 66*X^19 + 4*X^18 + 27*X^17 + X^16 + 26*X^15 + 35*X^14 +
      19*X^13 + 22*X^12 + X^11 + 49*X^10 + 25*X^9 + 63*X^8 + 4*X^7 + 8*X^6 + 4*X^5 + 13*X^4 + 4*X^3 +
      21*X^2 + 13*X + 15) :=
  mul_step (by norm_num) pSeventeenB2s144 pSeventeenB21 ⟨
    24,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s146 : XPow fSeventeenB2 47012546189955717746122011118
    (2*X^33 + 18*X^32 + 61*X^31 + 4*X^30 + 56*X^29 + 52*X^28 + 44*X^27 + 34*X^26 + 5*X^25 + 66*X^24 +
      20*X^23 + 43*X^22 + 26*X^21 + 46*X^20 + 4*X^18 + 2*X^17 + 7*X^16 + 8*X^15 + 45*X^14 + 8*X^13 +
      41*X^12 + 8*X^11 + 43*X^10 + 48*X^9 + 19*X^8 + 7*X^7 + 41*X^6 + 21*X^5 + 7*X^4 + 18*X^3 +
      3*X^2 + 15*X + 18) :=
  sq_step (by norm_num) pSeventeenB2s145 ⟨
    4*X^32 + 35*X^31 + 34*X^30 + 32*X^29 + 61*X^28 + 24*X^27 + 61*X^26 + 54*X^25 + 24*X^24 + 50*X^23 +
      X^22 + 7*X^21 + X^20 + 36*X^19 + 51*X^18 + 3*X^17 + 66*X^16 + 58*X^15 + 22*X^14 + 44*X^13 +
      28*X^12 + 63*X^11 + 59*X^10 + 51*X^9 + 24*X^8 + 47*X^7 + 38*X^6 + 61*X^5 + 62*X^4 + 14*X^3 +
      54*X^2 + 40*X + 44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s147 : XPow fSeventeenB2 47012546189955717746122011119
    (57*X^33 + 64*X^32 + 7*X^31 + 55*X^30 + 7*X^29 + 58*X^28 + 14*X^27 + 37*X^26 + 7*X^25 + 57*X^24 +
      61*X^23 + 60*X^22 + 13*X^21 + 2*X^20 + 62*X^19 + 16*X^18 + 62*X^17 + 3*X^16 + 29*X^15 +
      36*X^14 + 45*X^13 + 12*X^12 + 15*X^11 + 14*X^10 + 3*X^9 + 15*X^8 + X^7 + 23*X^6 + 52*X^5 +
      66*X^4 + 16*X^3 + 17*X^2 + 12*X + 18) :=
  mul_step (by norm_num) pSeventeenB2s146 pSeventeenB21 ⟨
    2,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s148 : XPow fSeventeenB2 94025092379911435492244022238
    (56*X^33 + 26*X^32 + 12*X^31 + 24*X^30 + 53*X^29 + 17*X^28 + 13*X^27 + 54*X^26 + 12*X^25 + 7*X^24 +
      12*X^23 + 62*X^22 + 56*X^21 + 52*X^20 + 32*X^19 + 20*X^18 + 13*X^17 + 36*X^16 + 35*X^15 +
      54*X^14 + 3*X^13 + 36*X^12 + 57*X^11 + 25*X^10 + 35*X^9 + 64*X^8 + 49*X^7 + 47*X^6 + 61*X^5 +
      3*X^4 + 20*X^3 + 53*X^2 + 28*X + 41) :=
  sq_step (by norm_num) pSeventeenB2s147 ⟨
    33*X^32 + 19*X^30 + 15*X^29 + 51*X^28 + 5*X^27 + 32*X^26 + 31*X^25 + 52*X^24 + 52*X^23 + 23*X^22 +
      7*X^21 + 49*X^20 + 18*X^19 + 23*X^18 + 12*X^17 + 11*X^16 + 50*X^15 + 40*X^14 + 33*X^13 +
      60*X^11 + 63*X^10 + 51*X^9 + 40*X^8 + 4*X^7 + 18*X^6 + 26*X^5 + 57*X^4 + 29*X^3 + 31*X^2 +
      29*X + 43,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s149 : XPow fSeventeenB2 188050184759822870984488044476
    (40*X^33 + 22*X^32 + 24*X^31 + 12*X^30 + 18*X^29 + 28*X^28 + 12*X^27 + 49*X^26 + 16*X^25 + 52*X^24 +
      41*X^23 + 19*X^22 + 6*X^21 + 62*X^20 + 16*X^19 + 32*X^18 + 45*X^17 + 5*X^16 + 56*X^15 +
      65*X^14 + 26*X^13 + 54*X^12 + 34*X^11 + 29*X^10 + 46*X^9 + 61*X^8 + 28*X^7 + 57*X^6 + 8*X^5 +
      16*X^4 + X^3 + 4*X^2 + 46*X + 26) :=
  sq_step (by norm_num) pSeventeenB2s148 ⟨
    54*X^32 + 12*X^31 + 57*X^30 + X^28 + 33*X^27 + 55*X^26 + 16*X^25 + 61*X^24 + 61*X^23 + 46*X^22 +
      26*X^21 + 47*X^20 + 65*X^19 + 30*X^18 + 66*X^17 + 44*X^16 + 15*X^15 + 19*X^14 + 12*X^13 +
      14*X^12 + X^11 + 50*X^10 + 20*X^9 + 35*X^8 + 42*X^7 + 46*X^6 + 40*X^5 + 6*X^4 + 6*X^3 + 32*X^2 +
      51*X + 32,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s150 : XPow fSeventeenB2 188050184759822870984488044477
    (65*X^33 + 17*X^32 + 5*X^31 + 65*X^30 + 66*X^29 + 24*X^28 + 51*X^27 + 53*X^26 + 11*X^25 + 44*X^24 +
      44*X^23 + 16*X^22 + 5*X^21 + 56*X^20 + 53*X^19 + 57*X^18 + 33*X^17 + 23*X^16 + 13*X^15 +
      50*X^14 + 47*X^12 + 5*X^11 + 36*X^10 + 9*X^9 + 54*X^8 + 61*X^7 + 48*X^6 + 45*X^5 + 23*X^4 +
      63*X^3 + 19*X^2 + 40*X + 25) :=
  mul_step (by norm_num) pSeventeenB2s149 pSeventeenB21 ⟨
    40,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s151 : XPow fSeventeenB2 376100369519645741968976088954
    (65*X^33 + 38*X^32 + 14*X^31 + 55*X^30 + X^29 + 62*X^28 + X^27 + 27*X^26 + 34*X^25 + 24*X^24 +
      37*X^23 + 31*X^22 + 55*X^21 + 28*X^20 + 8*X^19 + 44*X^18 + 6*X^17 + 16*X^16 + 3*X^15 + 49*X^14 +
      29*X^13 + 9*X^12 + 13*X^11 + 14*X^10 + 21*X^9 + 15*X^8 + 21*X^7 + 31*X^6 + 65*X^5 + 37*X^4 +
      45*X^3 + 32*X^2 + 63*X + 44) :=
  sq_step (by norm_num) pSeventeenB2s150 ⟨
    4*X^32 + 10*X^31 + X^30 + 51*X^29 + 32*X^28 + 55*X^27 + 31*X^26 + 4*X^25 + 15*X^24 + 27*X^23 +
      34*X^22 + 43*X^21 + 20*X^19 + 39*X^18 + 33*X^17 + 56*X^16 + 53*X^15 + 4*X^14 + 41*X^13 +
      32*X^12 + 40*X^11 + 11*X^10 + 43*X^9 + 19*X^8 + 45*X^7 + 63*X^6 + 24*X^5 + 21*X^4 + 53*X^3 +
      48*X^2 + 66*X + 62,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s152 : XPow fSeventeenB2 752200739039291483937952177908
    (55*X^33 + 27*X^32 + 64*X^31 + 56*X^30 + 49*X^29 + 6*X^28 + 15*X^27 + 51*X^26 + 37*X^25 + 66*X^24 +
      8*X^23 + 35*X^22 + 53*X^21 + 24*X^20 + 14*X^19 + 29*X^18 + 39*X^17 + 28*X^16 + 7*X^15 +
      27*X^14 + 6*X^13 + 46*X^12 + 35*X^11 + 49*X^10 + 66*X^9 + 32*X^8 + 66*X^7 + 27*X^6 + 36*X^5 +
      57*X^4 + 41*X^3 + 6*X^2 + 55*X + 56) :=
  sq_step (by norm_num) pSeventeenB2s151 ⟨
    4*X^32 + 60*X^31 + 18*X^30 + 18*X^29 + 14*X^28 + 34*X^27 + 39*X^26 + 33*X^25 + 53*X^24 + 17*X^23 +
      59*X^22 + 31*X^21 + 64*X^20 + 53*X^19 + 5*X^18 + 7*X^17 + 60*X^16 + 7*X^15 + 58*X^14 + 2*X^13 +
      19*X^12 + 37*X^11 + 25*X^10 + 9*X^9 + 13*X^8 + 45*X^7 + 13*X^6 + 20*X^5 + 43*X^4 + 55*X^3 +
      46*X^2 + 55*X + 7,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s153 : XPow fSeventeenB2 1504401478078582967875904355816
    (7*X^33 + 64*X^32 + 58*X^31 + 66*X^30 + 13*X^29 + 28*X^28 + 60*X^27 + 41*X^26 + 17*X^25 + 29*X^24 +
      63*X^23 + 23*X^22 + X^21 + 66*X^20 + 38*X^19 + 46*X^18 + 42*X^17 + 5*X^16 + 9*X^15 + 22*X^14 +
      5*X^13 + 29*X^12 + 36*X^11 + 22*X^10 + 28*X^9 + 41*X^8 + 32*X^7 + 7*X^6 + 33*X^5 + 15*X^4 +
      47*X^3 + 66*X + 41) :=
  sq_step (by norm_num) pSeventeenB2s152 ⟨
    10*X^32 + 16*X^31 + 56*X^30 + 27*X^29 + 41*X^28 + 43*X^27 + 45*X^26 + 23*X^25 + X^24 + 38*X^23 +
      61*X^22 + 27*X^21 + 42*X^20 + 61*X^19 + 29*X^18 + 28*X^17 + 61*X^16 + 14*X^14 + 27*X^13 +
      63*X^12 + 16*X^11 + 27*X^10 + 58*X^9 + 34*X^8 + 61*X^7 + 30*X^6 + 26*X^5 + 24*X^4 + 42*X^3 +
      36*X^2 + 47*X + 6,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s154 : XPow fSeventeenB2 1504401478078582967875904355817
    (33*X^33 + 35*X^32 + 43*X^31 + 43*X^30 + 38*X^29 + 42*X^28 + 38*X^27 + 62*X^26 + 57*X^25 + 25*X^24 +
      19*X^23 + 53*X^22 + 51*X^21 + 45*X^20 + 48*X^19 + 24*X^18 + 30*X^17 + 25*X^16 + 33*X^15 +
      36*X^14 + 43*X^13 + 50*X^12 + 58*X^11 + 43*X^10 + 52*X^9 + 60*X^8 + X^7 + 40*X^6 + 5*X^5 +
      14*X^4 + 12*X^3 + 6*X^2 + 20*X + 63) :=
  mul_step (by norm_num) pSeventeenB2s153 pSeventeenB21 ⟨
    7,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s155 : XPow fSeventeenB2 3008802956157165935751808711634
    (43*X^33 + 33*X^32 + 37*X^31 + 35*X^30 + 23*X^29 + 31*X^28 + 27*X^26 + 64*X^25 + 50*X^24 + 27*X^23 +
      28*X^22 + 18*X^21 + 59*X^20 + 61*X^19 + 7*X^18 + 47*X^17 + 15*X^16 + 59*X^15 + 11*X^14 +
      49*X^13 + 7*X^12 + 12*X^11 + 46*X^10 + 3*X^9 + 3*X^8 + 13*X^7 + 20*X^6 + 21*X^5 + 37*X^4 +
      2*X^3 + 31*X^2 + 11*X + 60) :=
  sq_step (by norm_num) pSeventeenB2s154 ⟨
    17*X^32 + 62*X^31 + 38*X^30 + 41*X^29 + 58*X^27 + 44*X^26 + 63*X^25 + 53*X^24 + 44*X^22 + 37*X^21 +
      17*X^20 + 32*X^19 + 10*X^18 + 58*X^17 + 28*X^16 + 28*X^15 + 62*X^14 + 12*X^13 + 50*X^12 +
      20*X^11 + 14*X^10 + 20*X^9 + 3*X^8 + 22*X^7 + 31*X^6 + 36*X^5 + 46*X^4 + 37*X^3 + 60*X^2 +
      38*X + 57,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s156 : XPow fSeventeenB2 3008802956157165935751808711635
    (34*X^33 + X^32 + 66*X^31 + 35*X^30 + 35*X^29 + 33*X^28 + 66*X^27 + 15*X^26 + 21*X^25 + 52*X^24 +
      13*X^23 + 12*X^22 + 53*X^21 + 37*X^20 + 48*X^19 + 13*X^18 + 25*X^17 + 52*X^16 + 2*X^15 +
      48*X^14 + 26*X^13 + 31*X^12 + 47*X^11 + 9*X^10 + 61*X^9 + 51*X^8 + 31*X^7 + 64*X^6 + 33*X^5 +
      29*X^4 + 9*X^3 + 54*X^2 + 65*X + 52) :=
  mul_step (by norm_num) pSeventeenB2s155 pSeventeenB21 ⟨
    43,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s157 : XPow fSeventeenB2 6017605912314331871503617423270
    (44*X^33 + 49*X^32 + 10*X^30 + 8*X^29 + 64*X^28 + 48*X^27 + 11*X^26 + 32*X^25 + 47*X^24 + 55*X^23 +
      23*X^22 + 50*X^21 + 39*X^20 + 9*X^19 + 3*X^18 + 58*X^17 + 48*X^16 + 35*X^15 + 64*X^14 +
      62*X^13 + 63*X^12 + 37*X^11 + 14*X^10 + 26*X^9 + 8*X^8 + 66*X^7 + 51*X^6 + 39*X^5 + 52*X^4 +
      48*X^3 + 39*X^2 + 2*X + 29) :=
  sq_step (by norm_num) pSeventeenB2s156 ⟨
    17*X^32 + 31*X^31 + 27*X^30 + 62*X^29 + 20*X^28 + 58*X^27 + 6*X^26 + 63*X^25 + 7*X^24 + 46*X^23 +
      51*X^22 + 35*X^21 + 57*X^20 + 27*X^19 + 30*X^18 + 39*X^17 + 57*X^16 + 18*X^15 + 50*X^14 +
      11*X^13 + 42*X^12 + 37*X^11 + 24*X^10 + 45*X^9 + 56*X^8 + 51*X^7 + 23*X^6 + 19*X^5 + 57*X^4 +
      55*X^3 + 13*X^2 + 26*X + 8,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s158 : XPow fSeventeenB2 6017605912314331871503617423271
    (36*X^33 + 66*X^32 + 9*X^31 + 53*X^30 + 12*X^29 + 21*X^28 + 40*X^27 + 66*X^26 + 22*X^25 + 65*X^24 +
      17*X^23 + 61*X^22 + 50*X^21 + 53*X^20 + 6*X^19 + 31*X^18 + 52*X^17 + 59*X^16 + 47*X^15 +
      8*X^14 + 17*X^13 + 58*X^12 + X^11 + 15*X^10 + 58*X^9 + 41*X^8 + 42*X^7 + 16*X^6 + 37*X^5 +
      32*X^4 + 57*X^3 + 46*X^2 + 31*X + 61) :=
  mul_step (by norm_num) pSeventeenB2s157 pSeventeenB21 ⟨
    44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s159 : XPow fSeventeenB2 12035211824628663743007234846542
    (29*X^33 + 29*X^32 + 26*X^31 + 17*X^30 + 15*X^29 + 61*X^28 + 17*X^27 + 54*X^26 + 23*X^25 + 17*X^24 +
      66*X^23 + 6*X^22 + 10*X^21 + 19*X^20 + 44*X^19 + 4*X^18 + 33*X^17 + 50*X^16 + 11*X^15 +
      16*X^14 + 21*X^13 + 19*X^12 + 27*X^11 + 49*X^10 + 4*X^9 + 7*X^8 + 62*X^7 + 41*X^6 + 64*X^5 +
      12*X^4 + 11*X^3 + 49*X^2 + 35*X + 39) :=
  sq_step (by norm_num) pSeventeenB2s158 ⟨
    23*X^32 + 8*X^31 + 2*X^30 + 31*X^29 + 40*X^28 + 3*X^27 + 45*X^26 + 28*X^25 + 21*X^24 + 50*X^23 +
      49*X^22 + 15*X^21 + 6*X^20 + 26*X^19 + 56*X^18 + 66*X^16 + 34*X^15 + 62*X^14 + 23*X^13 +
      42*X^12 + 28*X^11 + 6*X^10 + 9*X^9 + 46*X^8 + 40*X^7 + 35*X^6 + 58*X^5 + 64*X^4 + 59*X^3 +
      52*X^2 + 23*X + 45,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s160 : XPow fSeventeenB2 24070423649257327486014469693084
    (41*X^33 + 17*X^32 + 14*X^31 + 37*X^30 + 51*X^29 + 43*X^28 + 13*X^27 + 52*X^26 + 15*X^25 + 49*X^24 +
      39*X^23 + X^22 + 44*X^21 + 31*X^20 + 13*X^19 + 45*X^18 + X^17 + 50*X^16 + 51*X^15 + 47*X^14 +
      48*X^13 + 43*X^12 + 43*X^11 + 36*X^10 + 30*X^9 + 40*X^8 + 12*X^7 + 5*X^6 + 58*X^5 + 48*X^4 +
      42*X^3 + 14*X^2 + 52*X + 5) :=
  sq_step (by norm_num) pSeventeenB2s159 ⟨
    37*X^32 + 25*X^31 + 11*X^30 + 21*X^29 + 29*X^28 + 2*X^27 + 38*X^26 + 61*X^25 + 20*X^24 + 33*X^23 +
      30*X^22 + 64*X^21 + 12*X^20 + 47*X^19 + 21*X^18 + 5*X^17 + 56*X^16 + 5*X^15 + 17*X^14 +
      66*X^13 + 36*X^12 + 45*X^11 + 63*X^10 + 38*X^9 + 14*X^8 + 65*X^7 + 41*X^6 + 46*X^5 + 30*X^4 +
      41*X^3 + 24*X^2 + 21*X + 40,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s161 : XPow fSeventeenB2 48140847298514654972028939386168
    (36*X^33 + 5*X^32 + 28*X^31 + 30*X^30 + 57*X^29 + 59*X^28 + 44*X^27 + 30*X^26 + 29*X^25 + 42*X^24 +
      44*X^23 + 8*X^22 + 21*X^21 + 46*X^20 + 51*X^19 + 4*X^18 + 9*X^17 + 27*X^16 + 28*X^15 + 55*X^14 +
      22*X^13 + 49*X^12 + 16*X^11 + 10*X^10 + 54*X^9 + 26*X^8 + 15*X^7 + 6*X^6 + 2*X^5 + 38*X^4 +
      63*X^3 + 25*X^2 + 35*X + 49) :=
  sq_step (by norm_num) pSeventeenB2s160 ⟨
    6*X^32 + 37*X^31 + 57*X^30 + 63*X^29 + X^28 + 44*X^27 + 33*X^26 + 34*X^25 + 21*X^24 + 57*X^23 +
      11*X^22 + 63*X^21 + 52*X^20 + 51*X^19 + 39*X^18 + 26*X^17 + 2*X^16 + 39*X^15 + 43*X^14 +
      24*X^13 + 35*X^12 + 35*X^11 + 27*X^10 + 24*X^9 + 38*X^8 + 64*X^7 + 22*X^6 + 35*X^5 + 39*X^4 +
      66*X^3 + 46*X^2 + 14*X + 25,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s162 : XPow fSeventeenB2 96281694597029309944057878772336
    (49*X^33 + 37*X^31 + 29*X^30 + 10*X^29 + 17*X^28 + 65*X^27 + 2*X^26 + 3*X^25 + 29*X^24 + 28*X^23 +
      4*X^22 + 3*X^21 + 45*X^20 + 47*X^19 + 11*X^18 + 22*X^17 + 5*X^16 + 14*X^15 + 27*X^14 + 59*X^13 +
      33*X^12 + 38*X^11 + 52*X^10 + 6*X^9 + 66*X^8 + 59*X^7 + 33*X^6 + X^5 + 3*X^4 + 23*X^3 + 14*X^2 +
      25*X + 31) :=
  sq_step (by norm_num) pSeventeenB2s161 ⟨
    23*X^32 + 38*X^31 + 36*X^30 + 51*X^29 + 51*X^28 + 18*X^27 + 4*X^26 + 63*X^25 + 10*X^24 + 59*X^23 +
      43*X^22 + 47*X^21 + 53*X^20 + 31*X^19 + 40*X^18 + 34*X^17 + 20*X^16 + 48*X^15 + 7*X^14 +
      51*X^13 + 64*X^12 + 2*X^11 + 61*X^10 + 22*X^9 + 21*X^8 + 45*X^7 + 48*X^6 + 4*X^5 + 51*X^4 +
      7*X^3 + 18*X^2 + 55*X + 27,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s163 : XPow fSeventeenB2 96281694597029309944057878772337
    (51*X^33 + 10*X^32 + 2*X^31 + 19*X^30 + 20*X^29 + 6*X^28 + 48*X^27 + 50*X^26 + 24*X^25 + 30*X^24 +
      43*X^23 + 32*X^22 + 7*X^21 + 29*X^20 + 25*X^19 + 30*X^18 + 46*X^17 + 59*X^16 + 37*X^15 +
      8*X^14 + 64*X^13 + 2*X^12 + 36*X^11 + 44*X^10 + 9*X^9 + 54*X^8 + 58*X^7 + 50*X^6 + 60*X^4 +
      31*X^3 + 7*X^2 + 18*X + 39) :=
  mul_step (by norm_num) pSeventeenB2s162 pSeventeenB21 ⟨
    49,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s164 : XPow fSeventeenB2 192563389194058619888115757544674
    (14*X^33 + 19*X^32 + 54*X^31 + 42*X^30 + 18*X^29 + 7*X^28 + 13*X^27 + 24*X^26 + 11*X^25 + 63*X^24 +
      46*X^23 + 45*X^22 + 7*X^21 + 62*X^20 + 2*X^19 + 33*X^18 + 52*X^17 + 10*X^16 + 36*X^15 +
      30*X^14 + 20*X^13 + 23*X^12 + 5*X^11 + 49*X^10 + 44*X^9 + 28*X^8 + 37*X^7 + 7*X^6 + 16*X^5 +
      47*X^4 + 38*X^3 + 28*X^2 + 4*X + 44) :=
  sq_step (by norm_num) pSeventeenB2s163 ⟨
    55*X^32 + 49*X^31 + 2*X^30 + 29*X^29 + 57*X^28 + 46*X^27 + 36*X^26 + 64*X^25 + 2*X^24 + 12*X^23 +
      25*X^22 + 46*X^21 + 39*X^19 + 6*X^18 + 32*X^17 + 16*X^16 + 35*X^15 + 28*X^14 + X^13 + 15*X^12 +
      3*X^11 + 37*X^10 + 62*X^9 + 35*X^8 + 65*X^7 + 37*X^6 + 44*X^5 + 64*X^4 + 17*X^3 + X^2 + 23*X +
      22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s165 : XPow fSeventeenB2 192563389194058619888115757544675
    (24*X^33 + 8*X^32 + 63*X^31 + 11*X^30 + 27*X^29 + 44*X^28 + 18*X^27 + 34*X^26 + 52*X^25 + 37*X^24 +
      37*X^23 + 44*X^22 + 32*X^21 + 16*X^20 + 37*X^19 + 16*X^18 + 60*X^17 + X^16 + 52*X^15 + 15*X^14 +
      51*X^13 + 33*X^12 + 54*X^11 + 7*X^10 + 50*X^9 + 26*X^8 + 62*X^7 + 30*X^6 + 27*X^5 + 39*X^4 +
      52*X^3 + 18*X^2 + 2*X + 59) :=
  mul_step (by norm_num) pSeventeenB2s164 pSeventeenB21 ⟨
    14,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s166 : XPow fSeventeenB2 385126778388117239776231515089350
    (24*X^33 + 10*X^32 + 29*X^31 + 26*X^30 + 65*X^29 + 44*X^28 + 18*X^27 + 33*X^26 + 27*X^25 + 10*X^24 +
      35*X^23 + 66*X^22 + 63*X^21 + 19*X^20 + 17*X^19 + 25*X^18 + 3*X^17 + 37*X^16 + 23*X^15 +
      51*X^14 + 37*X^13 + 13*X^12 + 66*X^11 + 56*X^10 + 11*X^9 + 66*X^8 + 30*X^7 + 50*X^6 + 14*X^5 +
      13*X^4 + 33*X^3 + 45*X^2 + 23*X + 40) :=
  sq_step (by norm_num) pSeventeenB2s165 ⟨
    40*X^32 + 25*X^31 + 51*X^30 + 15*X^29 + 32*X^28 + 22*X^27 + 23*X^26 + 5*X^25 + 26*X^24 + 56*X^23 +
      64*X^22 + 46*X^21 + X^20 + 49*X^19 + 7*X^18 + 52*X^17 + 52*X^16 + 18*X^15 + 60*X^14 + 5*X^13 +
      39*X^12 + 56*X^11 + 34*X^10 + 51*X^9 + 54*X^8 + X^7 + 24*X^6 + 54*X^5 + 40*X^4 + 56*X^3 +
      51*X^2 + 35*X + 42,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s167 : XPow fSeventeenB2 770253556776234479552463030178700
    (23*X^33 + 42*X^32 + 35*X^31 + 26*X^30 + 32*X^29 + 51*X^28 + 41*X^27 + 38*X^26 + 39*X^25 + 48*X^24 +
      40*X^23 + 55*X^22 + 52*X^21 + 64*X^20 + 66*X^19 + 8*X^18 + 42*X^17 + 36*X^16 + 57*X^15 +
      4*X^14 + 48*X^13 + 41*X^12 + 12*X^11 + 29*X^10 + 39*X^9 + 38*X^8 + 9*X^7 + 15*X^6 + 18*X^5 +
      59*X^4 + 60*X^3 + 44*X^2 + 35*X + 8) :=
  sq_step (by norm_num) pSeventeenB2s166 ⟨
    40*X^32 + 54*X^31 + 59*X^30 + 4*X^29 + 52*X^28 + 43*X^27 + 51*X^26 + 57*X^25 + 7*X^24 + 47*X^23 +
      57*X^22 + 17*X^21 + 54*X^20 + 39*X^19 + 19*X^18 + 44*X^17 + 3*X^16 + 65*X^15 + 38*X^14 +
      45*X^13 + 17*X^12 + 37*X^11 + 44*X^10 + 23*X^9 + 13*X^8 + 59*X^7 + 62*X^6 + 28*X^5 + 63*X^3 +
      50*X^2 + 6*X + 39,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s168 : XPow fSeventeenB2 1540507113552468959104926060357400
    (27*X^33 + 56*X^32 + 28*X^31 + 22*X^30 + 9*X^29 + 7*X^28 + 38*X^27 + 24*X^26 + 31*X^25 + 32*X^24 +
      33*X^23 + 23*X^22 + 7*X^21 + 10*X^20 + 28*X^19 + 12*X^18 + 57*X^17 + 40*X^16 + 3*X^15 +
      47*X^14 + 61*X^13 + 7*X^12 + 44*X^11 + 62*X^10 + 39*X^9 + 7*X^8 + 52*X^7 + 24*X^6 + 56*X^5 +
      57*X^4 + 23*X^3 + 43*X^2 + 51*X + 51) :=
  sq_step (by norm_num) pSeventeenB2s167 ⟨
    60*X^32 + 20*X^31 + 35*X^30 + 14*X^29 + 14*X^28 + 45*X^27 + 42*X^26 + 29*X^25 + 47*X^24 + 28*X^23 +
      19*X^22 + 4*X^21 + 30*X^20 + 56*X^19 + 3*X^18 + 8*X^17 + 36*X^16 + 55*X^15 + 5*X^14 + 53*X^13 +
      32*X^12 + 40*X^11 + 29*X^10 + 33*X^9 + 58*X^8 + 37*X^7 + 31*X^6 + 62*X^5 + 41*X^4 + 50*X^3 +
      52*X^2 + 5*X + 6,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s169 : XPow fSeventeenB2 1540507113552468959104926060357401
    (13*X^33 + 35*X^32 + 29*X^31 + 29*X^30 + 36*X^29 + 26*X^28 + 22*X^27 + 61*X^26 + 6*X^25 + 30*X^24 +
      65*X^23 + 64*X^22 + 55*X^20 + 58*X^19 + 45*X^18 + 12*X^17 + 36*X^16 + 32*X^15 + 37*X^14 +
      61*X^13 + 31*X^12 + 19*X^11 + 49*X^10 + 59*X^9 + 26*X^8 + 20*X^7 + 16*X^6 + 28*X^5 + X^4 +
      51*X^3 + 11*X^2 + 37*X + 42) :=
  mul_step (by norm_num) pSeventeenB2s168 pSeventeenB21 ⟨
    27,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s170 : XPow fSeventeenB2 3081014227104937918209852120714802
    (62*X^33 + 22*X^32 + 64*X^31 + 41*X^30 + 17*X^29 + 3*X^28 + 16*X^27 + 37*X^26 + 64*X^25 + 51*X^24 +
      40*X^23 + 29*X^22 + 16*X^21 + 65*X^20 + 24*X^19 + 35*X^18 + 34*X^17 + 10*X^16 + 18*X^15 +
      56*X^14 + 28*X^13 + 26*X^12 + 43*X^11 + 25*X^10 + 52*X^9 + 15*X^8 + 53*X^7 + 54*X^6 + 20*X^5 +
      40*X^4 + 42*X^3 + 46*X^2 + 57*X + 28) :=
  sq_step (by norm_num) pSeventeenB2s169 ⟨
    35*X^32 + 18*X^31 + 4*X^30 + 27*X^29 + 61*X^28 + 58*X^27 + 57*X^26 + 13*X^25 + 59*X^24 + 9*X^23 +
      11*X^22 + 56*X^21 + 63*X^20 + 14*X^19 + 33*X^18 + 25*X^17 + 7*X^16 + 21*X^15 + 39*X^14 +
      24*X^13 + 13*X^12 + 43*X^11 + 28*X^10 + 55*X^9 + 36*X^8 + 27*X^7 + 35*X^6 + 55*X^5 + 54*X^4 +
      46*X^3 + 17*X^2 + 26*X + 23,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s171 : XPow fSeventeenB2 6162028454209875836419704241429604
    (6*X^33 + 42*X^32 + 60*X^31 + 32*X^30 + 15*X^29 + 49*X^28 + 53*X^27 + 15*X^26 + 3*X^25 + 52*X^24 +
      46*X^23 + 64*X^22 + 6*X^21 + 12*X^20 + 17*X^19 + 22*X^18 + 18*X^17 + 13*X^16 + 26*X^15 +
      64*X^14 + 42*X^13 + 30*X^12 + 54*X^11 + 24*X^10 + 58*X^9 + 66*X^8 + 21*X^7 + 7*X^6 + 62*X^5 +
      30*X^4 + 61*X^3 + 3*X^2 + 52*X + 19) :=
  sq_step (by norm_num) pSeventeenB2s170 ⟨
    25*X^32 + 33*X^31 + 56*X^30 + 34*X^29 + 15*X^28 + 19*X^27 + 26*X^26 + 34*X^25 + 38*X^24 + 7*X^22 +
      33*X^21 + 60*X^20 + 52*X^19 + 40*X^18 + 7*X^17 + 60*X^16 + 38*X^15 + 52*X^14 + 10*X^13 +
      56*X^12 + 22*X^11 + 5*X^10 + 46*X^9 + 47*X^8 + 16*X^7 + 41*X^6 + 16*X^5 + 56*X^4 + 8*X^3 +
      16*X^2 + 62*X + 49,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s172 : XPow fSeventeenB2 12324056908419751672839408482859208
    (41*X^33 + 57*X^32 + 64*X^31 + 32*X^30 + 26*X^29 + 66*X^28 + 16*X^27 + 13*X^26 + 3*X^25 + 31*X^24 +
      16*X^23 + 30*X^22 + X^21 + 20*X^20 + 6*X^19 + 58*X^18 + 62*X^17 + 47*X^16 + 28*X^15 + 66*X^14 +
      41*X^13 + 37*X^12 + 3*X^11 + 48*X^10 + 34*X^9 + 58*X^8 + 3*X^7 + 3*X^6 + 62*X^5 + 7*X^4 +
      54*X^3 + 66*X + 34) :=
  sq_step (by norm_num) pSeventeenB2s171 ⟨
    36*X^32 + 59*X^30 + 29*X^29 + 2*X^28 + 24*X^27 + 5*X^26 + 24*X^25 + 5*X^24 + 9*X^23 + 19*X^22 +
      57*X^21 + 52*X^20 + 61*X^19 + 19*X^18 + 21*X^17 + 31*X^16 + 27*X^15 + 51*X^14 + 14*X^13 +
      11*X^12 + 3*X^11 + 16*X^10 + 12*X^9 + 26*X^8 + 23*X^7 + 26*X^6 + 9*X^5 + 56*X^4 + 27*X^3 +
      38*X^2 + 66*X + 53,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s173 : XPow fSeventeenB2 12324056908419751672839408482859209
    (19*X^33 + 25*X^32 + 60*X^31 + 39*X^30 + 48*X^29 + 35*X^28 + 5*X^27 + 56*X^26 + 61*X^25 + 4*X^24 +
      64*X^23 + 28*X^22 + 47*X^21 + 47*X^20 + 41*X^19 + 14*X^18 + 2*X^17 + 26*X^16 + 6*X^15 +
      12*X^14 + 52*X^13 + 18*X^12 + 10*X^11 + 7*X^10 + 65*X^9 + 33*X^8 + 54*X^7 + 36*X^6 + 25*X^5 +
      33*X^4 + 32*X^3 + 40*X^2 + 45*X + 34) :=
  mul_step (by norm_num) pSeventeenB2s172 pSeventeenB21 ⟨
    41,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s174 : XPow fSeventeenB2 24648113816839503345678816965718418
    (22*X^33 + 13*X^32 + 44*X^31 + 22*X^30 + 34*X^29 + 2*X^28 + 29*X^27 + 42*X^26 + 15*X^25 + 64*X^24 +
      18*X^23 + 59*X^22 + 58*X^21 + 57*X^20 + 38*X^19 + 62*X^17 + 3*X^16 + 61*X^15 + 60*X^14 +
      9*X^13 + 10*X^12 + 48*X^11 + 30*X^10 + 7*X^9 + 32*X^8 + 24*X^7 + 15*X^6 + 27*X^5 + 20*X^4 +
      36*X^3 + 7*X^2 + 34*X + 54) :=
  sq_step (by norm_num) pSeventeenB2s173 ⟨
    26*X^32 + 50*X^31 + 33*X^30 + 47*X^29 + 27*X^28 + 38*X^27 + 35*X^26 + 41*X^25 + 17*X^24 + 56*X^23 +
      7*X^22 + 22*X^21 + 47*X^20 + 57*X^19 + 45*X^18 + 34*X^17 + 55*X^16 + 3*X^15 + 9*X^14 + 48*X^13 +
      22*X^12 + 65*X^11 + 59*X^10 + 66*X^9 + 53*X^8 + 11*X^7 + 38*X^6 + 55*X^5 + 23*X^4 + 52*X^3 +
      29*X^2 + 20*X + 19,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s175 : XPow fSeventeenB2 49296227633679006691357633931436836
    (52*X^33 + 10*X^32 + 24*X^31 + 7*X^30 + 20*X^29 + 22*X^28 + 54*X^27 + 33*X^26 + 14*X^25 + 28*X^24 +
      47*X^23 + 25*X^22 + 53*X^21 + 25*X^19 + 63*X^18 + 40*X^17 + 61*X^16 + 60*X^15 + 4*X^14 +
      64*X^13 + 25*X^12 + 64*X^11 + 23*X^10 + 7*X^9 + 65*X^8 + 38*X^7 + 62*X^6 + 45*X^5 + 50*X^4 +
      57*X^3 + 25*X^2 + 66*X + 44) :=
  sq_step (by norm_num) pSeventeenB2s174 ⟨
    15*X^32 + 27*X^31 + 41*X^30 + 60*X^29 + 9*X^28 + 3*X^27 + 21*X^26 + 36*X^25 + 63*X^24 + 10*X^23 +
      62*X^22 + 5*X^21 + 12*X^20 + 56*X^19 + 46*X^18 + 65*X^17 + 21*X^16 + 6*X^15 + 11*X^14 + 8*X^13 +
      38*X^12 + 38*X^11 + 17*X^10 + 26*X^9 + 23*X^8 + 32*X^7 + 33*X^6 + 22*X^5 + 6*X^4 + 60*X^3 +
      29*X^2 + 24*X + 1,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s176 : XPow fSeventeenB2 49296227633679006691357633931436837
    (19*X^33 + 35*X^32 + 18*X^31 + 61*X^30 + 58*X^29 + 16*X^28 + 49*X^27 + 42*X^26 + 35*X^25 + 4*X^24 +
      24*X^23 + 66*X^22 + 13*X^21 + 10*X^20 + 30*X^19 + 2*X^18 + 17*X^17 + 64*X^16 + 57*X^15 +
      55*X^14 + 62*X^13 + 34*X^12 + 32*X^11 + 61*X^10 + 51*X^9 + 45*X^8 + 27*X^7 + 30*X^6 + 14*X^5 +
      32*X^4 + 28*X^3 + 51*X^2 + 22*X + 66) :=
  mul_step (by norm_num) pSeventeenB2s175 pSeventeenB21 ⟨
    52,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s177 : XPow fSeventeenB2 98592455267358013382715267862873674
    (58*X^33 + 25*X^32 + 33*X^31 + 8*X^30 + 49*X^29 + 47*X^28 + 47*X^27 + 59*X^26 + 20*X^25 + 9*X^24 +
      55*X^23 + 11*X^22 + 30*X^21 + 29*X^20 + 15*X^19 + 52*X^18 + 22*X^17 + 22*X^16 + 15*X^15 +
      20*X^14 + 38*X^13 + 30*X^11 + 24*X^10 + 5*X^9 + 27*X^8 + X^7 + 42*X^6 + 15*X^5 + 57*X^4 +
      47*X^3 + 15*X^2 + 54*X) :=
  sq_step (by norm_num) pSeventeenB2s176 ⟨
    26*X^32 + 28*X^31 + 15*X^30 + 32*X^29 + 3*X^28 + 29*X^27 + 9*X^26 + 22*X^25 + 66*X^24 + 57*X^23 +
      64*X^22 + 3*X^21 + 63*X^20 + 57*X^19 + 32*X^18 + 25*X^17 + 24*X^16 + 37*X^15 + 25*X^14 +
      32*X^13 + 11*X^12 + 51*X^11 + 54*X^10 + 24*X^9 + 40*X^8 + 37*X^7 + 41*X^6 + 56*X^5 + 55*X^4 +
      49*X^3 + 10*X^2 + 58*X + 52,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s178 : XPow fSeventeenB2 98592455267358013382715267862873675
    (17*X^33 + 53*X^32 + 28*X^31 + 20*X^30 + 15*X^29 + 51*X^28 + 15*X^27 + 10*X^26 + 40*X^25 + 56*X^24 +
      64*X^23 + 11*X^22 + 10*X^21 + 6*X^20 + 59*X^19 + 26*X^18 + 9*X^17 + 4*X^16 + 25*X^15 + 46*X^14 +
      49*X^13 + 12*X^12 + 16*X^11 + 24*X^10 + 32*X^9 + 32*X^8 + 21*X^7 + 6*X^6 + 22*X^5 + 32*X^4 +
      57*X^3 + 45*X^2 + 27*X + 53) :=
  mul_step (by norm_num) pSeventeenB2s177 pSeventeenB21 ⟨
    58,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s179 : XPow fSeventeenB2 197184910534716026765430535725747350
    (48*X^33 + 38*X^32 + 60*X^31 + 19*X^30 + 37*X^29 + 55*X^28 + 42*X^27 + 15*X^26 + 40*X^25 + 63*X^24 +
      39*X^23 + 60*X^22 + 34*X^21 + 27*X^20 + 45*X^19 + 41*X^18 + 44*X^17 + 23*X^16 + 35*X^15 +
      59*X^14 + 60*X^13 + 9*X^12 + 56*X^11 + 62*X^10 + 35*X^9 + X^8 + 25*X^7 + 65*X^6 + 10*X^5 +
      62*X^4 + 21*X^3 + 62*X^2 + 49) :=
  sq_step (by norm_num) pSeventeenB2s178 ⟨
    21*X^32 + 34*X^31 + 12*X^29 + 37*X^28 + 4*X^27 + 23*X^26 + 22*X^25 + 7*X^24 + 38*X^23 + 41*X^22 +
      24*X^21 + 31*X^20 + 24*X^19 + 18*X^18 + 46*X^17 + 63*X^16 + 34*X^15 + 41*X^14 + 3*X^13 +
      64*X^12 + 17*X^11 + 66*X^10 + 64*X^9 + 19*X^8 + 12*X^7 + 59*X^6 + 21*X^5 + 42*X^4 + 4*X^3 +
      12*X^2 + 19*X + 6,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s180 : XPow fSeventeenB2 197184910534716026765430535725747351
    (36*X^33 + 65*X^32 + 24*X^31 + 13*X^30 + 47*X^29 + 43*X^28 + 4*X^27 + 4*X^26 + 54*X^25 + 56*X^24 +
      23*X^23 + 46*X^22 + 39*X^21 + 26*X^20 + 26*X^19 + 45*X^18 + 3*X^17 + 49*X^16 + 10*X^15 +
      62*X^14 + 38*X^13 + 18*X^12 + 60*X^11 + 23*X^10 + 19*X^9 + 16*X^8 + 43*X^7 + 58*X^6 + 3*X^5 +
      34*X^4 + 39*X^3 + 48*X^2 + 39*X + 30) :=
  mul_step (by norm_num) pSeventeenB2s179 pSeventeenB21 ⟨
    48,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s181 : XPow fSeventeenB2 394369821069432053530861071451494702
    (64*X^33 + 57*X^32 + 50*X^31 + 61*X^30 + 36*X^29 + 9*X^28 + 12*X^27 + 51*X^26 + 50*X^25 + 19*X^24 +
      52*X^23 + 53*X^22 + 38*X^21 + 40*X^20 + 37*X^19 + 31*X^18 + 29*X^17 + 45*X^16 + 16*X^15 +
      45*X^14 + 51*X^13 + 8*X^12 + 25*X^11 + 17*X^10 + 57*X^9 + 34*X^8 + 50*X^7 + 17*X^6 + 35*X^5 +
      17*X^4 + 42*X^3 + 59*X^2 + 32*X + 2) :=
  sq_step (by norm_num) pSeventeenB2s180 ⟨
    23*X^32 + 3*X^31 + 16*X^30 + 52*X^29 + 48*X^28 + 31*X^27 + 31*X^26 + X^25 + 26*X^24 + 18*X^23 +
      42*X^22 + 36*X^21 + 9*X^20 + 47*X^19 + 38*X^18 + 37*X^17 + 33*X^16 + 3*X^15 + 45*X^14 +
      11*X^13 + 31*X^12 + 23*X^11 + 8*X^10 + 41*X^9 + 55*X^8 + 42*X^7 + 23*X^6 + 58*X^5 + 58*X^4 +
      25*X^3 + 45*X^2 + 18*X + 64,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s182 : XPow fSeventeenB2 788739642138864107061722142902989404
    (59*X^33 + 27*X^32 + 50*X^31 + 41*X^30 + 57*X^29 + 50*X^28 + 57*X^27 + 40*X^26 + 38*X^25 + 28*X^24 +
      29*X^23 + 6*X^22 + 13*X^21 + 38*X^20 + 25*X^19 + 59*X^18 + 12*X^17 + X^16 + 34*X^15 + 38*X^14 +
      17*X^13 + X^12 + 35*X^11 + 34*X^10 + 51*X^9 + 17*X^8 + 32*X^7 + 49*X^6 + 61*X^5 + 7*X^4 +
      41*X^3 + 20*X^2 + 43*X + 31) :=
  sq_step (by norm_num) pSeventeenB2s181 ⟨
    9*X^32 + X^31 + 34*X^30 + 49*X^29 + 24*X^28 + 54*X^27 + 14*X^26 + 9*X^25 + 26*X^23 + 44*X^22 +
      4*X^21 + 43*X^20 + 13*X^19 + 61*X^18 + 29*X^17 + 24*X^16 + 39*X^15 + 40*X^13 + 17*X^12 +
      63*X^11 + 34*X^10 + 20*X^9 + 13*X^8 + 50*X^7 + 13*X^6 + 36*X^5 + 61*X^4 + 38*X^3 + 3*X^2 +
      66*X + 3,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s183 : XPow fSeventeenB2 788739642138864107061722142902989405
    (5*X^33 + 38*X^32 + 29*X^31 + 61*X^30 + 29*X^29 + X^28 + 53*X^27 + 44*X^26 + 63*X^25 + 15*X^24 + X^23 +
      11*X^22 + 36*X^21 + 17*X^20 + 28*X^19 + 23*X^18 + 49*X^17 + 54*X^16 + 35*X^15 + 39*X^14 +
      52*X^13 + 19*X^12 + 12*X^11 + 53*X^10 + 14*X^9 + 8*X^7 + 53*X^6 + 28*X^5 + 50*X^4 + 35*X^3 +
      35*X^2 + 55*X + 62) :=
  mul_step (by norm_num) pSeventeenB2s182 pSeventeenB21 ⟨
    59,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s184 : XPow fSeventeenB2 1577479284277728214123444285805978810
    (42*X^33 + 46*X^32 + 45*X^31 + 65*X^30 + 7*X^29 + 56*X^28 + 62*X^27 + 57*X^26 + 22*X^25 + 58*X^24 +
      2*X^23 + 47*X^22 + 5*X^21 + 11*X^20 + 42*X^19 + 28*X^18 + 43*X^17 + X^16 + 21*X^15 + 28*X^14 +
      8*X^13 + 28*X^12 + 53*X^11 + 47*X^10 + 16*X^9 + 50*X^8 + 21*X^7 + 57*X^6 + 10*X^5 + 10*X^4 +
      54*X^3 + 25*X^2 + 49*X + 50) :=
  sq_step (by norm_num) pSeventeenB2s183 ⟨
    25*X^32 + 30*X^31 + 45*X^30 + 22*X^29 + 65*X^28 + 10*X^27 + 50*X^26 + 48*X^25 + 47*X^24 + 25*X^23 +
      56*X^22 + 56*X^21 + 21*X^20 + 16*X^19 + 13*X^18 + 46*X^17 + 26*X^16 + 63*X^15 + 38*X^14 +
      12*X^13 + 15*X^12 + 66*X^11 + 8*X^10 + X^9 + 11*X^8 + 48*X^7 + 53*X^6 + 10*X^5 + 37*X^4 +
      37*X^3 + 28*X^2 + 65*X + 40,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s185 : XPow fSeventeenB2 1577479284277728214123444285805978811
    (61*X^33 + 41*X^32 + 61*X^31 + 53*X^30 + 49*X^29 + 21*X^28 + 39*X^27 + 24*X^26 + 25*X^25 + 42*X^24 +
      23*X^23 + 49*X^22 + 55*X^21 + 17*X^20 + 40*X^19 + 2*X^18 + 17*X^17 + 50*X^16 + 27*X^15 +
      60*X^14 + 45*X^13 + 3*X^12 + 62*X^11 + 39*X^10 + 49*X^9 + 55*X^8 + 21*X^7 + 52*X^6 + 17*X^5 +
      57*X^4 + 30*X^3 + 24*X^2 + 58*X + 43) :=
  mul_step (by norm_num) pSeventeenB2s184 pSeventeenB21 ⟨
    42,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s186 : XPow fSeventeenB2 3154958568555456428246888571611957622
    (13*X^33 + 2*X^32 + 52*X^31 + 49*X^30 + 19*X^29 + 55*X^28 + 65*X^27 + 32*X^26 + 63*X^25 + 58*X^24 +
      54*X^23 + 13*X^22 + 44*X^21 + 7*X^20 + 49*X^19 + 19*X^18 + 53*X^17 + 44*X^16 + 60*X^15 +
      3*X^14 + 2*X^13 + 66*X^12 + 16*X^11 + 35*X^10 + 65*X^9 + 63*X^8 + 57*X^7 + 40*X^6 + 20*X^5 +
      40*X^4 + 30*X^3 + 29*X^2 + 32*X + 2) :=
  sq_step (by norm_num) pSeventeenB2s185 ⟨
    36*X^32 + 9*X^31 + 6*X^30 + 28*X^29 + 23*X^28 + X^27 + 33*X^26 + 12*X^25 + 2*X^24 + 59*X^23 +
      63*X^22 + 35*X^21 + 40*X^20 + 3*X^19 + 38*X^18 + 32*X^17 + 5*X^16 + 39*X^15 + 61*X^14 +
      16*X^13 + 5*X^12 + 24*X^11 + 56*X^10 + 5*X^9 + 63*X^8 + 6*X^7 + 6*X^6 + 40*X^5 + 22*X^4 +
      62*X^3 + 28*X^2 + 41*X + 33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s187 : XPow fSeventeenB2 3154958568555456428246888571611957623
    (21*X^33 + 38*X^32 + 35*X^31 + 46*X^30 + 64*X^29 + 22*X^28 + 36*X^27 + 3*X^26 + 43*X^25 + 60*X^24 +
      63*X^23 + 64*X^22 + 27*X^21 + 62*X^20 + 61*X^19 + 10*X^18 + 33*X^17 + 61*X^16 + 33*X^15 +
      50*X^14 + 25*X^13 + 42*X^12 + 54*X^11 + 45*X^10 + 26*X^9 + 42*X^8 + 48*X^7 + 33*X^6 + 31*X^5 +
      7*X^4 + 13*X^3 + 45*X^2 + 30*X + 50) :=
  mul_step (by norm_num) pSeventeenB2s186 pSeventeenB21 ⟨
    13,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s188 : XPow fSeventeenB2 6309917137110912856493777143223915246
    (36*X^33 + 6*X^32 + 43*X^31 + 35*X^30 + 6*X^29 + 3*X^28 + 5*X^27 + 30*X^26 + 27*X^25 + 24*X^24 +
      8*X^23 + 60*X^22 + 4*X^21 + 56*X^20 + 46*X^19 + 24*X^18 + 54*X^17 + 9*X^16 + 22*X^15 + 2*X^14 +
      43*X^13 + 65*X^11 + 55*X^10 + 52*X^9 + 27*X^8 + 11*X^7 + 52*X^6 + 47*X^5 + 25*X^4 + 4*X^3 +
      X^2 + 9*X + 66) :=
  sq_step (by norm_num) pSeventeenB2s187 ⟨
    39*X^32 + 45*X^31 + 31*X^30 + 63*X^29 + 22*X^28 + 35*X^27 + 53*X^26 + 19*X^25 + 22*X^24 + 59*X^23 +
      53*X^22 + 28*X^21 + 9*X^20 + 12*X^19 + 66*X^18 + 4*X^17 + 44*X^16 + 38*X^15 + 3*X^14 + 55*X^13 +
      15*X^12 + 24*X^11 + 33*X^10 + 38*X^9 + 34*X^8 + 62*X^7 + 59*X^6 + 34*X^5 + 29*X^4 + 21*X^3 +
      4*X^2 + 49*X + 5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s189 : XPow fSeventeenB2 12619834274221825712987554286447830492
    (32*X^33 + 19*X^32 + 45*X^31 + 19*X^30 + 18*X^29 + 30*X^28 + 17*X^27 + 14*X^26 + 18*X^25 + 36*X^24 +
      35*X^23 + 61*X^22 + 47*X^21 + 20*X^20 + 6*X^19 + 61*X^18 + 50*X^17 + 54*X^16 + 21*X^15 +
      38*X^14 + 65*X^13 + 3*X^12 + 52*X^11 + 9*X^10 + 16*X^9 + 22*X^8 + 66*X^7 + 46*X^6 + 7*X^5 +
      59*X^4 + 65*X^3 + 19*X^2 + 31*X + 53) :=
  sq_step (by norm_num) pSeventeenB2s188 ⟨
    23*X^32 + 43*X^31 + 52*X^30 + 62*X^29 + 21*X^28 + 23*X^27 + 35*X^26 + 4*X^25 + 65*X^24 + 55*X^23 +
      18*X^22 + 2*X^21 + 39*X^20 + 21*X^19 + 17*X^18 + 22*X^17 + 58*X^16 + 29*X^15 + 17*X^14 +
      45*X^13 + 54*X^12 + 8*X^11 + 6*X^10 + 16*X^9 + 36*X^8 + 35*X^7 + 16*X^6 + 52*X^5 + 4*X^4 +
      37*X^3 + 15*X^2 + 57*X + 43,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s190 : XPow fSeventeenB2 25239668548443651425975108572895660984
    (17*X^33 + 52*X^32 + 13*X^31 + 25*X^30 + 17*X^29 + 38*X^28 + 3*X^27 + 36*X^26 + 65*X^25 + 31*X^24 +
      42*X^23 + 17*X^22 + 22*X^21 + 18*X^20 + 53*X^19 + 45*X^18 + 14*X^17 + 37*X^16 + 60*X^15 +
      4*X^14 + 56*X^13 + 27*X^12 + 45*X^11 + 29*X^10 + 32*X^9 + 6*X^8 + 7*X^7 + 50*X^6 + 57*X^5 +
      31*X^4 + 7*X^3 + 16*X^2 + 17*X + 16) :=
  sq_step (by norm_num) pSeventeenB2s189 ⟨
    19*X^32 + 12*X^31 + 53*X^30 + 53*X^29 + 29*X^28 + 49*X^27 + 32*X^26 + 54*X^25 + 8*X^24 + 63*X^23 +
      54*X^22 + 38*X^21 + 8*X^20 + 18*X^19 + 58*X^18 + 38*X^17 + 53*X^16 + X^15 + 26*X^14 + 39*X^13 +
      30*X^12 + 7*X^11 + 66*X^10 + 52*X^9 + 11*X^8 + 32*X^7 + 42*X^6 + 12*X^5 + 62*X^4 + 5*X^3 +
      39*X^2 + 47*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s191 : XPow fSeventeenB2 50479337096887302851950217145791321968
    (5*X^33 + 2*X^32 + 17*X^31 + 48*X^30 + 13*X^29 + 8*X^28 + 59*X^27 + 3*X^26 + 19*X^25 + 32*X^24 +
      65*X^23 + 16*X^22 + 44*X^21 + 29*X^20 + 62*X^19 + 3*X^18 + 51*X^17 + 21*X^16 + 47*X^15 +
      57*X^14 + 63*X^13 + 9*X^12 + 45*X^11 + 63*X^10 + 43*X^9 + 24*X^8 + 21*X^7 + 14*X^6 + 18*X^5 +
      18*X^4 + 65*X^3 + 49*X^2 + 61*X + 50) :=
  sq_step (by norm_num) pSeventeenB2s190 ⟨
    21*X^32 + 62*X^30 + 59*X^29 + 24*X^28 + X^27 + 21*X^26 + 9*X^25 + 21*X^24 + 39*X^22 + 58*X^21 +
      51*X^20 + 20*X^19 + 13*X^18 + 54*X^17 + 25*X^16 + 60*X^15 + 58*X^14 + 43*X^13 + 19*X^12 +
      30*X^11 + 33*X^10 + 34*X^9 + 26*X^8 + 2*X^7 + 29*X^6 + 41*X^5 + 51*X^4 + 49*X^3 + 40*X^2 +
      33*X + 59,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s192 : XPow fSeventeenB2 100958674193774605703900434291582643936
    (34*X^33 + 32*X^32 + 15*X^31 + 22*X^30 + 36*X^29 + 41*X^28 + 5*X^27 + 4*X^26 + 26*X^25 + 29*X^24 +
      31*X^23 + 46*X^22 + 28*X^21 + 18*X^20 + 4*X^19 + 16*X^18 + 64*X^17 + 24*X^16 + 38*X^15 +
      22*X^14 + 41*X^13 + 29*X^12 + 20*X^11 + 33*X^10 + 53*X^9 + 34*X^8 + 17*X^7 + 21*X^6 + 41*X^5 +
      8*X^4 + 12*X^3 + 47*X^2 + 32*X + 41) :=
  sq_step (by norm_num) pSeventeenB2s191 ⟨
    25*X^32 + 5*X^31 + 41*X^30 + 19*X^29 + 33*X^28 + 23*X^27 + 17*X^26 + 16*X^25 + 25*X^24 + 26*X^23 +
      43*X^22 + X^21 + 25*X^20 + 39*X^19 + 30*X^18 + 43*X^17 + 25*X^16 + 19*X^15 + 23*X^14 + 54*X^13 +
      36*X^12 + 18*X^11 + 14*X^10 + 65*X^9 + 61*X^8 + 5*X^7 + 29*X^6 + 24*X^5 + 11*X^4 + 20*X^3 +
      41*X^2 + 66*X + 32,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s193 : XPow fSeventeenB2 201917348387549211407800868583165287872
    (18*X^33 + 56*X^32 + 59*X^31 + 51*X^30 + 7*X^29 + 54*X^28 + 18*X^27 + 12*X^26 + 2*X^25 + 48*X^24 +
      37*X^23 + 29*X^22 + 32*X^21 + 38*X^20 + 3*X^19 + 5*X^18 + 2*X^17 + 39*X^16 + 38*X^15 + 34*X^14 +
      14*X^13 + 29*X^12 + 40*X^11 + 5*X^10 + 58*X^9 + 66*X^8 + 59*X^7 + 33*X^6 + 31*X^5 + 56*X^4 +
      X^3 + 10*X^2 + 54*X + 55) :=
  sq_step (by norm_num) pSeventeenB2s192 ⟨
    17*X^32 + 62*X^31 + 29*X^30 + 58*X^29 + 47*X^28 + 54*X^27 + 26*X^26 + 29*X^25 + 64*X^24 + 42*X^23 +
      30*X^22 + 3*X^21 + 17*X^20 + 16*X^19 + 7*X^18 + 26*X^17 + 58*X^16 + 30*X^15 + 65*X^14 +
      31*X^13 + 36*X^12 + 54*X^11 + 41*X^10 + 8*X^9 + 5*X^8 + 60*X^7 + 18*X^6 + 19*X^5 + 33*X^4 +
      18*X^3 + 24*X^2 + 19*X + 65,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s194 : XPow fSeventeenB2 403834696775098422815601737166330575744
    (6*X^33 + 44*X^32 + 8*X^31 + 11*X^30 + 18*X^29 + 31*X^28 + 34*X^27 + 61*X^26 + 6*X^25 + 10*X^24 +
      22*X^23 + 3*X^22 + 31*X^21 + 31*X^20 + 38*X^19 + 13*X^18 + 4*X^17 + 3*X^16 + 8*X^15 + 4*X^14 +
      9*X^13 + 19*X^12 + 27*X^11 + 10*X^10 + 15*X^9 + 8*X^8 + 22*X^7 + 18*X^6 + 54*X^5 + 23*X^4 +
      23*X^3 + 64*X^2 + 46*X + 61) :=
  sq_step (by norm_num) pSeventeenB2s193 ⟨
    56*X^32 + 26*X^31 + 22*X^30 + 18*X^29 + 58*X^28 + 21*X^27 + 24*X^26 + 26*X^25 + 11*X^24 + 53*X^23 +
      24*X^22 + 37*X^21 + 51*X^20 + 32*X^19 + 32*X^18 + 53*X^17 + 42*X^16 + 13*X^15 + 28*X^14 +
      16*X^13 + 32*X^12 + 54*X^11 + 13*X^10 + 10*X^9 + 23*X^8 + 22*X^7 + 52*X^6 + 41*X^5 + 57*X^4 +
      65*X^3 + 25*X^2 + 17*X + 28,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s195 : XPow fSeventeenB2 807669393550196845631203474332661151488
    (41*X^33 + 63*X^32 + 44*X^31 + 59*X^30 + 54*X^29 + 35*X^28 + 64*X^27 + 60*X^26 + 6*X^25 + 12*X^24 +
      16*X^23 + 49*X^22 + 16*X^21 + 63*X^20 + 23*X^19 + 54*X^18 + 48*X^17 + 31*X^16 + 64*X^15 +
      29*X^14 + 27*X^13 + 24*X^12 + 55*X^11 + 33*X^10 + 65*X^9 + 14*X^8 + 66*X^7 + 44*X^6 + 52*X^5 +
      30*X^4 + 17*X^3 + 29*X^2 + 61*X + 40) :=
  sq_step (by norm_num) pSeventeenB2s194 ⟨
    36*X^32 + 24*X^31 + 8*X^30 + 10*X^29 + 66*X^28 + 11*X^27 + 64*X^26 + 8*X^25 + 56*X^24 + 64*X^23 +
      15*X^22 + 44*X^21 + 60*X^20 + 64*X^19 + 19*X^18 + 52*X^17 + 26*X^16 + 58*X^15 + 59*X^14 +
      11*X^13 + 49*X^12 + 23*X^11 + 25*X^10 + 26*X^9 + 65*X^8 + 57*X^7 + 66*X^6 + 43*X^5 + 44*X^4 +
      11*X^3 + 30*X^2 + 36*X + 60,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s196 : XPow fSeventeenB2 807669393550196845631203474332661151489
    (25*X^33 + 5*X^32 + 20*X^31 + 17*X^29 + 16*X^28 + 52*X^27 + 59*X^26 + 42*X^25 + 4*X^24 + 16*X^23 +
      43*X^22 + 23*X^21 + 64*X^20 + 37*X^19 + 53*X^17 + 62*X^16 + 36*X^15 + 65*X^14 + 39*X^13 +
      3*X^12 + 62*X^11 + 38*X^10 + 21*X^9 + 29*X^8 + 28*X^7 + 26*X^6 + 48*X^5 + 63*X^4 + 61*X^3 +
      35*X^2 + 51*X + 34) :=
  mul_step (by norm_num) pSeventeenB2s195 pSeventeenB21 ⟨
    41,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s197 : XPow fSeventeenB2 1615338787100393691262406948665322302978
    (46*X^33 + 63*X^32 + 55*X^30 + 34*X^29 + 29*X^28 + 52*X^27 + 26*X^26 + 22*X^25 + 13*X^24 + 63*X^23 +
      61*X^22 + 11*X^21 + 47*X^20 + 18*X^19 + 42*X^18 + 48*X^17 + 40*X^16 + 60*X^15 + 26*X^14 +
      50*X^13 + 32*X^12 + 37*X^11 + 20*X^10 + 33*X^9 + 7*X^8 + 64*X^7 + 57*X^6 + 35*X^5 + 15*X^4 +
      15*X^3 + 44*X^2 + 26*X + 53) :=
  sq_step (by norm_num) pSeventeenB2s196 ⟨
    22*X^32 + 9*X^31 + 61*X^30 + 29*X^29 + 36*X^27 + 53*X^26 + 2*X^25 + 42*X^24 + 45*X^23 + 18*X^22 +
      19*X^21 + 65*X^20 + 54*X^19 + 54*X^18 + 5*X^17 + 21*X^16 + 30*X^15 + 20*X^14 + 50*X^13 +
      61*X^12 + 17*X^11 + 36*X^10 + 52*X^9 + 21*X^8 + 47*X^7 + 56*X^6 + 37*X^4 + 60*X^3 + 56*X^2 +
      6*X + 4,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s198 : XPow fSeventeenB2 1615338787100393691262406948665322302979
    (22*X^33 + 2*X^32 + 57*X^31 + 11*X^30 + 66*X^29 + 39*X^28 + 35*X^27 + 21*X^26 + 63*X^25 + 43*X^24 +
      6*X^23 + 56*X^22 + 25*X^21 + 64*X^20 + 36*X^19 + 35*X^18 + 32*X^17 + 12*X^16 + 60*X^15 +
      24*X^14 + 57*X^13 + 62*X^12 + 46*X^11 + 55*X^10 + 41*X^9 + 47*X^8 + 8*X^7 + 14*X^6 + 45*X^5 +
      47*X^4 + 8*X^3 + 5*X^2 + 49*X + 12) :=
  mul_step (by norm_num) pSeventeenB2s197 pSeventeenB21 ⟨
    46,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s199 : XPow fSeventeenB2 3230677574200787382524813897330644605958
    (51*X^33 + 21*X^32 + 61*X^31 + 20*X^29 + 14*X^28 + 59*X^27 + 2*X^26 + 35*X^25 + 3*X^24 + X^23 +
      38*X^22 + 15*X^21 + 41*X^20 + 36*X^19 + 38*X^18 + 36*X^17 + 3*X^16 + 12*X^15 + 60*X^14 +
      37*X^13 + 8*X^12 + 23*X^11 + 53*X^10 + 5*X^9 + 7*X^8 + 64*X^7 + 56*X^6 + 31*X^5 + 9*X^4 +
      13*X^3 + 22*X^2 + 15*X + 41) :=
  sq_step (by norm_num) pSeventeenB2s198 ⟨
    15*X^32 + 12*X^31 + 55*X^30 + 16*X^29 + 36*X^28 + 14*X^27 + 19*X^26 + 66*X^25 + 23*X^24 + 46*X^23 +
      44*X^22 + 7*X^21 + 14*X^20 + 9*X^19 + 15*X^18 + 12*X^17 + 62*X^16 + 21*X^15 + 38*X^14 +
      19*X^13 + 62*X^12 + 40*X^11 + 48*X^10 + 45*X^9 + 28*X^8 + 11*X^7 + 47*X^6 + 27*X^5 + 6*X^4 +
      57*X^3 + 59*X^2 + 26*X + 63,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s200 : XPow fSeventeenB2 3230677574200787382524813897330644605959
    (44*X^33 + 37*X^32 + 43*X^31 + 28*X^30 + 39*X^29 + 14*X^28 + 28*X^27 + 47*X^26 + 6*X^25 + 40*X^24 +
      28*X^23 + 11*X^22 + 37*X^21 + 20*X^20 + 43*X^19 + 58*X^18 + 32*X^17 + 52*X^16 + 54*X^15 +
      14*X^14 + 43*X^13 + 58*X^12 + 9*X^11 + 9*X^10 + X^9 + 41*X^7 + 15*X^6 + 51*X^5 + 31*X^4 +
      52*X^3 + 66*X^2 + 22*X + 57) :=
  mul_step (by norm_num) pSeventeenB2s199 pSeventeenB21 ⟨
    51,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s201 : XPow fSeventeenB2 6461355148401574765049627794661289211918
    (14*X^33 + 7*X^32 + 21*X^31 + 18*X^30 + 26*X^29 + 12*X^28 + 13*X^27 + 24*X^26 + 66*X^25 + 44*X^24 +
      51*X^23 + 20*X^22 + 60*X^21 + 29*X^20 + 20*X^19 + 55*X^18 + 41*X^17 + 49*X^16 + 20*X^15 +
      38*X^14 + 56*X^13 + 46*X^12 + 22*X^11 + 19*X^10 + 51*X^9 + 17*X^8 + 62*X^7 + 36*X^6 + 55*X^5 +
      22*X^4 + 20*X^3 + 7*X^2 + 32*X + 21) :=
  sq_step (by norm_num) pSeventeenB2s200 ⟨
    60*X^32 + 4*X^31 + 28*X^30 + 57*X^29 + 7*X^28 + 11*X^27 + 57*X^26 + 57*X^25 + 14*X^24 + 47*X^23 +
      22*X^22 + 27*X^21 + 66*X^20 + X^18 + 48*X^17 + 38*X^16 + 66*X^15 + X^14 + 33*X^13 + 34*X^12 +
      50*X^11 + 9*X^10 + 42*X^9 + X^8 + 52*X^7 + 12*X^6 + 16*X^5 + 39*X^4 + 30*X^3 + 64*X^2 + 52*X +
      21,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s202 : XPow fSeventeenB2 12922710296803149530099255589322578423836
    (22*X^33 + 55*X^32 + 7*X^31 + 7*X^30 + 62*X^29 + 34*X^28 + 46*X^27 + 19*X^26 + 59*X^25 + 31*X^24 +
      27*X^23 + 42*X^22 + 65*X^21 + 30*X^20 + 9*X^19 + 59*X^18 + 22*X^17 + 17*X^16 + 32*X^15 +
      49*X^14 + 51*X^13 + 59*X^12 + 61*X^11 + 23*X^10 + 42*X^9 + 10*X^8 + 21*X^7 + 43*X^6 + 12*X^5 +
      11*X^4 + 49*X^3 + 3*X^2 + 9*X + 46) :=
  sq_step (by norm_num) pSeventeenB2s201 ⟨
    62*X^32 + 65*X^31 + 21*X^30 + 58*X^29 + 37*X^28 + 31*X^27 + 48*X^26 + 19*X^25 + 42*X^24 + 16*X^23 +
      33*X^22 + 39*X^21 + 61*X^20 + 56*X^19 + 58*X^18 + 3*X^17 + 57*X^16 + 62*X^15 + 13*X^14 +
      10*X^13 + 52*X^12 + 10*X^11 + 39*X^10 + 16*X^9 + 63*X^8 + 23*X^7 + 46*X^6 + 32*X^5 + 47*X^4 +
      23*X^3 + 65*X^2 + 43*X + 38,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s203 : XPow fSeventeenB2 25845420593606299060198511178645156847672
    (14*X^33 + 27*X^32 + 21*X^31 + 14*X^30 + 58*X^29 + 64*X^28 + 45*X^27 + 5*X^26 + 47*X^25 + 49*X^24 +
      29*X^23 + 15*X^22 + 12*X^21 + 51*X^19 + 26*X^18 + 48*X^17 + 37*X^16 + 49*X^15 + 17*X^14 +
      4*X^13 + 7*X^12 + 49*X^11 + 60*X^10 + 28*X^9 + 40*X^8 + 3*X^7 + 52*X^6 + 49*X^5 + 59*X^4 +
      10*X^3 + 66*X^2 + 63*X + 33) :=
  sq_step (by norm_num) pSeventeenB2s202 ⟨
    15*X^32 + 66*X^31 + 53*X^30 + 22*X^29 + 60*X^28 + 13*X^27 + 23*X^26 + 39*X^25 + 8*X^24 + 50*X^23 +
      7*X^22 + 30*X^21 + 39*X^20 + 25*X^19 + 4*X^18 + 29*X^17 + 4*X^16 + 60*X^15 + 35*X^14 + 48*X^13 +
      41*X^12 + 29*X^11 + 66*X^10 + 17*X^9 + 17*X^8 + 7*X^7 + 59*X^6 + 18*X^5 + 9*X^4 + 58*X^3 +
      51*X^2 + 19*X + 44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s204 : XPow fSeventeenB2 51690841187212598120397022357290313695344
    (64*X^33 + 44*X^32 + 8*X^31 + 66*X^30 + 37*X^29 + 29*X^28 + 18*X^27 + 51*X^26 + 13*X^25 + 15*X^24 +
      52*X^23 + 34*X^22 + 36*X^21 + 22*X^20 + 6*X^19 + 53*X^18 + 44*X^17 + 13*X^16 + 22*X^15 +
      57*X^14 + 25*X^13 + 53*X^12 + 31*X^11 + 37*X^10 + 9*X^9 + 46*X^8 + 28*X^7 + 13*X^6 + 40*X^5 +
      30*X^4 + 12*X^3 + 34*X^2 + 18*X + 56) :=
  sq_step (by norm_num) pSeventeenB2s203 ⟨
    62*X^32 + 22*X^31 + 30*X^30 + 26*X^29 + 25*X^28 + 21*X^27 + 53*X^26 + 30*X^25 + 31*X^24 + 42*X^23 +
      12*X^22 + 40*X^21 + 57*X^20 + 55*X^19 + 7*X^18 + 2*X^17 + 53*X^16 + 30*X^15 + 5*X^14 + 18*X^13 +
      30*X^12 + 31*X^11 + 50*X^10 + 63*X^9 + 50*X^8 + 34*X^7 + 45*X^6 + 50*X^5 + X^4 + 63*X^3 +
      57*X^2 + 3*X + 49,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s205 : XPow fSeventeenB2 103381682374425196240794044714580627390688
    (29*X^33 + 7*X^32 + 13*X^31 + 23*X^30 + 28*X^29 + 35*X^28 + 14*X^27 + 62*X^26 + 33*X^25 + 66*X^24 +
      51*X^23 + 35*X^22 + 13*X^21 + 15*X^20 + 25*X^19 + 57*X^18 + 39*X^17 + 20*X^16 + 59*X^15 +
      52*X^14 + 42*X^13 + 21*X^12 + 20*X^11 + 40*X^10 + 22*X^9 + 29*X^8 + 33*X^7 + 46*X^6 + 52*X^5 +
      11*X^4 + 41*X^3 + 61*X^2 + 9*X + 10) :=
  sq_step (by norm_num) pSeventeenB2s204 ⟨
    9*X^32 + 12*X^31 + 25*X^30 + 23*X^29 + 19*X^28 + 17*X^27 + 63*X^26 + 59*X^25 + 17*X^24 + 10*X^23 +
      48*X^22 + 19*X^21 + 26*X^20 + 59*X^19 + X^18 + 35*X^17 + 23*X^16 + 25*X^15 + 60*X^14 + 11*X^13 +
      12*X^12 + 4*X^11 + 18*X^10 + 42*X^9 + 61*X^8 + 28*X^7 + 56*X^6 + 36*X^5 + 51*X^4 + 10*X^3 +
      54*X^2 + 26*X + 10,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s206 : XPow fSeventeenB2 103381682374425196240794044714580627390689
    (3*X^33 + 23*X^32 + 33*X^31 + 47*X^30 + 19*X^29 + 16*X^28 + 40*X^27 + 28*X^26 + 48*X^25 + 18*X^24 +
      28*X^23 + 37*X^22 + 39*X^21 + 54*X^20 + 27*X^19 + 41*X^18 + 47*X^17 + 20*X^16 + 21*X^15 +
      46*X^14 + 12*X^13 + 11*X^12 + 36*X^11 + 65*X^10 + 65*X^9 + 15*X^8 + 2*X^7 + 14*X^6 + 27*X^5 +
      15*X^3 + 38*X^2 + 57*X + 60) :=
  mul_step (by norm_num) pSeventeenB2s205 pSeventeenB21 ⟨
    29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s207 : XPow fSeventeenB2 206763364748850392481588089429161254781378
    (31*X^33 + 26*X^32 + 49*X^31 + 10*X^30 + 60*X^29 + 18*X^28 + 53*X^27 + 33*X^26 + 50*X^25 + 55*X^24 +
      37*X^23 + 28*X^22 + 27*X^21 + 37*X^20 + 61*X^19 + 20*X^18 + 35*X^17 + 5*X^16 + 62*X^15 +
      55*X^14 + 15*X^13 + 37*X^12 + 40*X^11 + 50*X^10 + 46*X^9 + 29*X^8 + 56*X^7 + 44*X^6 + 42*X^5 +
      15*X^4 + 54*X^3 + 34*X^2 + 50*X + 6) :=
  sq_step (by norm_num) pSeventeenB2s206 ⟨
    9*X^32 + 12*X^31 + 3*X^30 + 14*X^29 + 38*X^28 + 7*X^27 + 23*X^26 + 26*X^25 + 46*X^24 + 29*X^23 +
      18*X^22 + 47*X^21 + 24*X^20 + 34*X^19 + 5*X^18 + 8*X^17 + 58*X^16 + 57*X^15 + 64*X^14 +
      36*X^13 + 6*X^12 + 19*X^11 + 27*X^10 + 28*X^9 + 65*X^8 + 10*X^7 + 5*X^6 + 48*X^5 + 28*X^4 +
      19*X^3 + 41*X^2 + 43*X + 25,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s208 : XPow fSeventeenB2 206763364748850392481588089429161254781379
    (61*X^33 + 62*X^32 + 23*X^31 + 11*X^30 + 24*X^29 + 2*X^28 + 58*X^27 + 10*X^26 + 45*X^25 + 41*X^24 +
      39*X^23 + 18*X^22 + 28*X^21 + 25*X^20 + 48*X^19 + 51*X^18 + 20*X^17 + 18*X^16 + 8*X^15 +
      47*X^14 + 32*X^13 + 35*X^12 + 18*X^11 + 55*X^10 + 49*X^9 + 46*X^8 + 27*X^7 + 6*X^6 + 9*X^5 +
      61*X^4 + X^3 + 14*X^2 + 47*X + 11) :=
  mul_step (by norm_num) pSeventeenB2s207 pSeventeenB21 ⟨
    31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s209 : XPow fSeventeenB2 413526729497700784963176178858322509562758
    (42*X^33 + 58*X^32 + 13*X^31 + 5*X^30 + 13*X^29 + 37*X^28 + 26*X^27 + 10*X^26 + 6*X^25 + 63*X^24 +
      28*X^22 + 4*X^21 + 6*X^20 + 31*X^19 + 65*X^18 + 4*X^17 + 28*X^16 + 26*X^15 + 63*X^14 + X^13 +
      34*X^12 + 24*X^11 + 39*X^10 + X^9 + 18*X^8 + 66*X^7 + 8*X^6 + 8*X^5 + 20*X^4 + 20*X^3 + 66*X^2 +
      57*X + 31) :=
  sq_step (by norm_num) pSeventeenB2s208 ⟨
    36*X^32 + 25*X^31 + 56*X^30 + 51*X^29 + 23*X^28 + 62*X^27 + 50*X^26 + 21*X^25 + 4*X^24 + 63*X^23 +
      66*X^22 + 5*X^21 + 54*X^20 + 58*X^19 + 58*X^18 + 46*X^17 + 35*X^16 + 27*X^15 + 52*X^14 + X^13 +
      19*X^12 + 46*X^11 + 21*X^10 + 33*X^9 + 13*X^8 + 5*X^7 + 47*X^6 + 32*X^5 + 15*X^4 + 21*X^3 +
      24*X^2 + 37*X + 57,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s210 : XPow fSeventeenB2 413526729497700784963176178858322509562759
    (6*X^33 + 9*X^32 + X^31 + 59*X^30 + 30*X^29 + 52*X^28 + 59*X^27 + 8*X^26 + 30*X^25 + 40*X^24 + 4*X^23 +
      48*X^22 + 50*X^21 + 6*X^20 + 10*X^19 + 30*X^18 + 44*X^17 + 55*X^16 + 62*X^15 + 53*X^14 +
      51*X^13 + 41*X^12 + 54*X^11 + 24*X^10 + 17*X^9 + 33*X^8 + 39*X^7 + 50*X^6 + 27*X^5 + 23*X^4 +
      4*X^3 + 32*X^2 + 39*X + 43) :=
  mul_step (by norm_num) pSeventeenB2s209 pSeventeenB21 ⟨
    42,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s211 : XPow fSeventeenB2 827053458995401569926352357716645019125518
    (20*X^33 + 2*X^32 + 24*X^31 + 47*X^30 + 51*X^29 + 48*X^28 + 14*X^27 + 4*X^26 + 9*X^25 + 9*X^24 +
      59*X^23 + 47*X^22 + 15*X^21 + 49*X^20 + 30*X^19 + 53*X^18 + 34*X^17 + 58*X^16 + 55*X^15 +
      24*X^14 + 48*X^13 + 60*X^12 + 37*X^11 + 10*X^10 + 11*X^9 + 18*X^8 + 25*X^7 + 6*X^6 + 16*X^5 +
      58*X^4 + 52*X^3 + 43*X^2 + 19*X + 21) :=
  sq_step (by norm_num) pSeventeenB2s210 ⟨
    36*X^32 + 6*X^31 + 63*X^30 + 41*X^29 + 30*X^28 + 4*X^27 + 28*X^26 + 25*X^25 + 39*X^24 + 56*X^23 +
      12*X^22 + 31*X^21 + 53*X^20 + 64*X^19 + 41*X^18 + 51*X^17 + 53*X^16 + 61*X^15 + 22*X^14 +
      64*X^13 + 52*X^12 + 43*X^11 + 34*X^10 + 49*X^9 + 24*X^8 + 11*X^7 + 20*X^6 + 40*X^5 + 13*X^4 +
      44*X^3 + 7*X^2 + 63*X + 50,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s212 : XPow fSeventeenB2 1654106917990803139852704715433290038251036
    (3*X^33 + 12*X^32 + 40*X^31 + 15*X^30 + 28*X^29 + 28*X^28 + 54*X^27 + 28*X^26 + 62*X^25 + 23*X^24 +
      50*X^23 + 27*X^22 + 7*X^21 + 45*X^20 + 20*X^19 + 11*X^18 + 40*X^17 + 36*X^16 + 62*X^15 +
      55*X^14 + 50*X^13 + 46*X^12 + 18*X^11 + 15*X^10 + 28*X^9 + 65*X^8 + 31*X^7 + 61*X^6 + 14*X^5 +
      52*X^4 + 38*X^3 + 25*X^2 + 34*X + 50) :=
  sq_step (by norm_num) pSeventeenB2s211 ⟨
    65*X^32 + 41*X^31 + 52*X^30 + 30*X^28 + 9*X^27 + 44*X^26 + 31*X^25 + 42*X^24 + 11*X^23 + 64*X^22 +
      49*X^21 + 34*X^20 + 40*X^19 + 15*X^18 + 36*X^17 + 2*X^16 + 64*X^15 + 63*X^14 + 20*X^13 +
      25*X^12 + 66*X^11 + 35*X^10 + 53*X^9 + 62*X^8 + 26*X^7 + 57*X^6 + 2*X^5 + 12*X^4 + 64*X^3 +
      29*X^2 + 52*X + 31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s213 : XPow fSeventeenB2 3308213835981606279705409430866580076502072
    (63*X^33 + 10*X^32 + 6*X^31 + 57*X^30 + 23*X^29 + 36*X^28 + 57*X^27 + 20*X^26 + 34*X^25 + 14*X^24 +
      34*X^23 + 42*X^22 + 64*X^21 + 58*X^20 + 36*X^19 + 52*X^18 + 64*X^17 + 54*X^16 + 24*X^15 +
      21*X^13 + 18*X^12 + 33*X^11 + 4*X^10 + 59*X^9 + X^8 + 66*X^7 + 29*X^6 + 46*X^5 + 30*X^4 +
      11*X^3 + 46*X^2 + 2*X + 57) :=
  sq_step (by norm_num) pSeventeenB2s212 ⟨
    9*X^32 + 13*X^31 + 48*X^30 + 9*X^29 + 12*X^28 + 40*X^27 + 66*X^26 + 35*X^25 + 65*X^24 + 37*X^23 +
      56*X^22 + 30*X^21 + 49*X^20 + X^19 + 39*X^18 + 59*X^17 + 63*X^16 + 49*X^15 + 65*X^14 + 51*X^13 +
      49*X^12 + 31*X^11 + 31*X^10 + 4*X^8 + 45*X^7 + 6*X^6 + 17*X^5 + 11*X^4 + 40*X^3 + 14*X^2 +
      63*X + 4,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s214 : XPow fSeventeenB2 6616427671963212559410818861733160153004144
    (60*X^33 + 45*X^32 + 61*X^31 + 43*X^30 + 7*X^29 + 29*X^28 + 12*X^27 + 19*X^26 + 20*X^25 + 33*X^24 +
      13*X^23 + 11*X^22 + 23*X^21 + 60*X^20 + 62*X^19 + 38*X^18 + 23*X^17 + 53*X^16 + 51*X^15 +
      27*X^14 + 57*X^13 + 28*X^12 + 64*X^11 + 37*X^10 + 9*X^9 + 41*X^8 + 52*X^7 + X^6 + 22*X^5 +
      43*X^4 + 12*X^3 + 22*X^2 + 19*X + 7) :=
  sq_step (by norm_num) pSeventeenB2s213 ⟨
    16*X^32 + 31*X^31 + 44*X^30 + 23*X^29 + 4*X^28 + 56*X^27 + 26*X^26 + 35*X^25 + 22*X^24 + 31*X^23 +
      52*X^22 + 26*X^21 + 47*X^20 + 41*X^19 + 34*X^18 + 52*X^17 + 49*X^16 + 9*X^15 + 8*X^14 +
      14*X^13 + 63*X^12 + 12*X^10 + 13*X^9 + 57*X^8 + 51*X^7 + 34*X^6 + 4*X^5 + 8*X^4 + 26*X^3 +
      27*X^2 + 18*X + 12,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s215 : XPow fSeventeenB2 6616427671963212559410818861733160153004145
    (9*X^33 + 17*X^32 + 66*X^31 + 44*X^30 + 19*X^29 + 30*X^28 + 22*X^27 + 42*X^26 + 5*X^25 + 51*X^24 +
      15*X^23 + 38*X^22 + 8*X^21 + 55*X^20 + 36*X^19 + 41*X^18 + 28*X^17 + 35*X^16 + 16*X^15 +
      26*X^14 + 14*X^13 + 50*X^12 + X^11 + 61*X^10 + 30*X^9 + 24*X^8 + 7*X^7 + 15*X^6 + 53*X^5 +
      45*X^4 + 10*X^3 + 12*X^2 + 28*X + 4) :=
  mul_step (by norm_num) pSeventeenB2s214 pSeventeenB21 ⟨
    60,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s216 : XPow fSeventeenB2 13232855343926425118821637723466320306008290
    (22*X^33 + 11*X^32 + 6*X^31 + 32*X^30 + 21*X^29 + 7*X^28 + 61*X^27 + 57*X^26 + 14*X^25 + 16*X^24 +
      31*X^23 + 5*X^22 + 61*X^21 + 63*X^20 + 59*X^19 + 66*X^18 + 30*X^17 + 46*X^16 + 47*X^15 +
      3*X^14 + 17*X^13 + 12*X^12 + 20*X^11 + 29*X^10 + 52*X^9 + 4*X^8 + 19*X^7 + 47*X^6 + 43*X^5 +
      8*X^4 + 27*X^3 + 56*X^2 + 49*X + 24) :=
  sq_step (by norm_num) pSeventeenB2s215 ⟨
    14*X^32 + 43*X^31 + 25*X^30 + 58*X^29 + 50*X^28 + 52*X^27 + 57*X^26 + 64*X^25 + 3*X^24 + 49*X^23 +
      12*X^22 + 33*X^21 + 62*X^20 + 66*X^19 + 25*X^18 + 64*X^17 + 60*X^16 + 48*X^15 + 41*X^14 +
      20*X^13 + 40*X^12 + 56*X^11 + 25*X^10 + 55*X^9 + 20*X^8 + 19*X^7 + 48*X^6 + 42*X^5 + 44*X^4 +
      41*X^3 + 31*X^2 + 28*X + 53,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s217 : XPow fSeventeenB2 13232855343926425118821637723466320306008291
    (38*X^33 + 39*X^32 + 65*X^31 + 10*X^30 + 48*X^29 + 14*X^28 + 38*X^27 + 31*X^26 + 37*X^25 + 36*X^24 +
      2*X^23 + 33*X^22 + 35*X^21 + 14*X^20 + 34*X^19 + 50*X^18 + 48*X^17 + 59*X^16 + 28*X^15 +
      57*X^14 + 56*X^13 + 64*X^12 + 56*X^11 + 13*X^10 + 29*X^9 + 40*X^8 + 9*X^7 + 65*X^6 + 34*X^5 +
      19*X^4 + 65*X^3 + 4*X^2 + 25*X + 64) :=
  mul_step (by norm_num) pSeventeenB2s216 pSeventeenB21 ⟨
    22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s218 : XPow fSeventeenB2 26465710687852850237643275446932640612016582
    (8*X^33 + 55*X^32 + 8*X^31 + 47*X^30 + 31*X^29 + X^28 + 35*X^27 + 62*X^26 + 25*X^25 + 17*X^24 +
      51*X^23 + 61*X^22 + 21*X^21 + 32*X^20 + 7*X^19 + 27*X^18 + 2*X^17 + 3*X^16 + 54*X^15 + 9*X^14 +
      32*X^13 + 36*X^12 + 58*X^11 + 9*X^10 + 26*X^9 + 10*X^8 + 61*X^7 + 40*X^6 + 2*X^5 + 60*X^4 +
      20*X^3 + 8*X^2 + 53*X + 17) :=
  sq_step (by norm_num) pSeventeenB2s217 ⟨
    37*X^32 + 34*X^31 + 44*X^30 + 61*X^29 + 25*X^28 + 41*X^27 + 34*X^26 + 38*X^25 + 19*X^24 + 36*X^23 +
      6*X^22 + 56*X^21 + 17*X^20 + 40*X^19 + 21*X^18 + 29*X^17 + 10*X^16 + 61*X^15 + 49*X^14 +
      45*X^13 + 64*X^12 + 12*X^11 + 28*X^10 + 55*X^9 + 44*X^8 + 29*X^7 + 27*X^6 + X^5 + 24*X^4 +
      12*X^3 + 26*X^2 + 3*X + 53,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s219 : XPow fSeventeenB2 26465710687852850237643275446932640612016583
    (10*X^33 + 20*X^32 + 59*X^31 + 27*X^30 + 22*X^29 + 24*X^28 + 49*X^27 + 19*X^26 + 49*X^25 + 65*X^24 +
      66*X^23 + 23*X^22 + 34*X^21 + 15*X^20 + 58*X^19 + 58*X^18 + 22*X^17 + 34*X^16 + 12*X^15 +
      10*X^14 + 52*X^13 + 7*X^12 + 31*X^11 + 24*X^10 + 13*X^9 + 26*X^8 + 14*X^7 + 10*X^6 + 39*X^5 +
      11*X^4 + 60*X^3 + 61*X^2 + 60*X + 5) :=
  mul_step (by norm_num) pSeventeenB2s218 pSeventeenB21 ⟨
    8,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s220 : XPow fSeventeenB2 52931421375705700475286550893865281224033166
    (20*X^33 + 5*X^32 + 64*X^31 + 36*X^30 + 37*X^29 + 18*X^28 + 47*X^27 + 34*X^26 + 3*X^25 + 51*X^24 +
      36*X^23 + 44*X^22 + 32*X^21 + 17*X^19 + 7*X^18 + 18*X^17 + 49*X^16 + X^15 + 54*X^14 + 17*X^13 +
      44*X^12 + 11*X^11 + 25*X^10 + 35*X^9 + 31*X^8 + 56*X^7 + 20*X^6 + 27*X^5 + 2*X^4 + 56*X^3 +
      34*X^2 + 32*X + 47) :=
  sq_step (by norm_num) pSeventeenB2s219 ⟨
    33*X^32 + 5*X^31 + 52*X^30 + 18*X^29 + 61*X^28 + 37*X^27 + 8*X^25 + 4*X^24 + 16*X^23 + 61*X^22 +
      63*X^21 + 19*X^19 + 28*X^18 + 10*X^17 + 7*X^16 + 16*X^15 + 45*X^14 + 45*X^13 + 55*X^12 +
      17*X^11 + 2*X^10 + 27*X^9 + 19*X^8 + 21*X^7 + 17*X^6 + 10*X^5 + 53*X^4 + 61*X^3 + 46*X^2 +
      32*X + 62,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s221 : XPow fSeventeenB2 52931421375705700475286550893865281224033167
    (60*X^33 + 27*X^32 + 66*X^31 + 27*X^30 + 37*X^29 + 53*X^28 + 35*X^27 + 55*X^26 + 64*X^25 + 4*X^24 +
      23*X^23 + 37*X^22 + 5*X^21 + 37*X^20 + 51*X^19 + 24*X^18 + 63*X^17 + 18*X^16 + 28*X^15 +
      29*X^14 + 17*X^13 + 51*X^12 + 13*X^11 + 30*X^10 + 5*X^9 + 2*X^8 + 22*X^7 + 47*X^6 + 50*X^5 +
      30*X^3 + 52*X^2 + 54*X + 46) :=
  mul_step (by norm_num) pSeventeenB2s220 pSeventeenB21 ⟨
    20,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s222 : XPow fSeventeenB2 105862842751411400950573101787730562448066334
    (31*X^33 + 20*X^32 + 58*X^31 + 49*X^30 + 5*X^29 + 5*X^28 + 34*X^27 + 66*X^26 + 58*X^25 + 26*X^24 +
      21*X^23 + 44*X^22 + 24*X^21 + 10*X^20 + 21*X^19 + 54*X^18 + 24*X^17 + 29*X^16 + 51*X^15 +
      3*X^14 + 28*X^13 + 16*X^12 + 2*X^11 + 48*X^10 + 36*X^9 + 66*X^8 + 14*X^7 + 11*X^6 + 33*X^5 +
      24*X^4 + 43*X^3 + 43*X^2 + 63*X + 2) :=
  sq_step (by norm_num) pSeventeenB2s221 ⟨
    49*X^32 + 8*X^31 + X^30 + 8*X^29 + 14*X^28 + 47*X^27 + 52*X^26 + 39*X^25 + 30*X^24 + 6*X^23 +
      37*X^22 + 53*X^21 + 26*X^20 + 34*X^19 + 30*X^18 + 21*X^17 + 9*X^16 + 66*X^15 + 50*X^14 +
      61*X^13 + 50*X^12 + 27*X^11 + 40*X^10 + 19*X^9 + 31*X^8 + 34*X^7 + 48*X^6 + 38*X^5 + 24*X^4 +
      37*X^3 + 47*X^2 + 7*X + 48,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s223 : XPow fSeventeenB2 105862842751411400950573101787730562448066335
    (55*X^33 + 4*X^32 + 62*X^31 + 23*X^30 + 11*X^29 + 50*X^28 + 24*X^27 + 18*X^26 + 16*X^25 + 25*X^24 +
      55*X^23 + 15*X^22 + X^21 + 52*X^20 + 15*X^19 + 40*X^18 + 44*X^17 + 7*X^16 + 23*X^15 + 60*X^14 +
      11*X^13 + 64*X^12 + 16*X^11 + 45*X^10 + 19*X^9 + 4*X^8 + 61*X^7 + 64*X^6 + 18*X^5 + 50*X^4 +
      10*X^3 + 27*X^2 + 43*X + 11) :=
  mul_step (by norm_num) pSeventeenB2s222 pSeventeenB21 ⟨
    31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s224 : XPow fSeventeenB2 211725685502822801901146203575461124896132670
    (5*X^33 + 60*X^31 + 61*X^30 + 66*X^29 + 49*X^28 + 20*X^27 + 30*X^26 + 24*X^25 + 24*X^24 + 62*X^23 +
      63*X^22 + 31*X^21 + 42*X^20 + 19*X^19 + 6*X^18 + 46*X^17 + 52*X^16 + 27*X^15 + 39*X^14 +
      36*X^13 + 54*X^12 + 48*X^11 + 60*X^10 + 50*X^9 + 14*X^8 + 38*X^7 + 49*X^6 + 6*X^5 + 60*X^4 +
      42*X^3 + 22*X^2 + 15*X + 9) :=
  sq_step (by norm_num) pSeventeenB2s223 ⟨
    10*X^32 + 32*X^31 + 38*X^30 + 11*X^29 + 25*X^28 + 50*X^27 + 13*X^25 + 5*X^24 + 24*X^23 + 51*X^22 +
      43*X^21 + 26*X^20 + 27*X^19 + 32*X^18 + 49*X^17 + 22*X^16 + 17*X^15 + 15*X^14 + 23*X^13 +
      42*X^12 + 55*X^11 + 66*X^10 + 11*X^8 + 36*X^7 + 47*X^6 + 35*X^5 + 15*X^4 + 52*X^3 + 34*X^2 +
      14*X + 62,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s225 : XPow fSeventeenB2 423451371005645603802292407150922249792265340
    (16*X^33 + 26*X^32 + 29*X^31 + 57*X^30 + 5*X^28 + 4*X^27 + 21*X^26 + 26*X^25 + 47*X^24 + 61*X^23 +
      4*X^22 + 26*X^21 + 63*X^20 + 6*X^19 + 61*X^18 + X^17 + 47*X^16 + 53*X^15 + 6*X^14 + 40*X^13 +
      44*X^12 + 49*X^11 + 6*X^10 + 14*X^9 + 47*X^8 + 37*X^7 + 6*X^6 + 47*X^5 + 53*X^4 + 54*X^3 +
      15*X^2 + 65*X + 7) :=
  sq_step (by norm_num) pSeventeenB2s224 ⟨
    25*X^32 + 52*X^31 + 10*X^30 + 16*X^29 + 63*X^28 + 47*X^27 + 17*X^26 + 37*X^25 + 17*X^24 + 34*X^23 +
      26*X^22 + 21*X^21 + 51*X^20 + 23*X^19 + 37*X^18 + 49*X^17 + 7*X^16 + 54*X^15 + 52*X^14 +
      32*X^13 + 25*X^12 + 38*X^11 + 6*X^10 + 15*X^9 + 12*X^8 + 62*X^7 + 43*X^6 + 19*X^5 + 29*X^4 +
      66*X^3 + 2*X^2 + 39*X + 29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s226 : XPow fSeventeenB2 846902742011291207604584814301844499584530680
    (13*X^33 + 28*X^32 + 5*X^31 + 45*X^30 + 37*X^29 + 33*X^28 + 9*X^27 + 22*X^26 + 14*X^25 + 63*X^24 +
      43*X^23 + 10*X^22 + 44*X^21 + 12*X^20 + 22*X^19 + 7*X^18 + 18*X^17 + 47*X^16 + 3*X^15 +
      34*X^14 + 46*X^13 + 5*X^12 + 44*X^11 + 35*X^10 + 47*X^9 + 38*X^8 + 35*X^7 + 55*X^6 + 36*X^5 +
      19*X^4 + 8*X^3 + 51*X^2 + 45*X + 17) :=
  sq_step (by norm_num) pSeventeenB2s225 ⟨
    55*X^32 + 62*X^31 + 48*X^30 + 55*X^29 + 57*X^28 + 13*X^27 + 43*X^26 + 19*X^25 + 65*X^24 + 57*X^23 +
      7*X^22 + 55*X^21 + 49*X^20 + 47*X^19 + 30*X^18 + 45*X^17 + 23*X^16 + 34*X^15 + 30*X^14 +
      45*X^13 + 7*X^12 + 63*X^11 + 61*X^10 + 50*X^9 + 59*X^8 + 40*X^7 + 35*X^6 + 45*X^5 + 54*X^4 +
      9*X^3 + 64*X^2 + 64*X + 56,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s227 : XPow fSeventeenB2 1693805484022582415209169628603688999169061360
    (22*X^32 + 29*X^31 + 26*X^30 + 58*X^29 + 45*X^28 + 5*X^27 + 62*X^26 + 20*X^25 + 25*X^24 + 16*X^23 +
      27*X^22 + 58*X^21 + 57*X^20 + 17*X^19 + 16*X^18 + 65*X^17 + 40*X^16 + 29*X^15 + 61*X^14 +
      35*X^13 + 18*X^12 + 32*X^11 + 21*X^10 + 2*X^9 + 14*X^8 + 64*X^7 + 29*X^6 + 64*X^5 + 27*X^4 +
      X^3 + 4*X^2 + 24*X + 41) :=
  sq_step (by norm_num) pSeventeenB2s226 ⟨
    35*X^32 + 37*X^31 + 13*X^30 + 36*X^29 + 12*X^28 + 34*X^27 + 62*X^26 + 18*X^25 + 22*X^24 + 42*X^23 +
      52*X^22 + 24*X^21 + 4*X^20 + 37*X^19 + 21*X^18 + 10*X^17 + 59*X^16 + 29*X^15 + 18*X^14 +
      16*X^13 + 61*X^12 + 23*X^11 + 24*X^10 + 18*X^9 + 57*X^8 + 24*X^7 + 28*X^6 + 32*X^5 + 2*X^4 +
      36*X^3 + 63*X^2 + 22*X + 32,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s228 : XPow fSeventeenB2 1693805484022582415209169628603688999169061361
    (22*X^33 + 29*X^32 + 26*X^31 + 58*X^30 + 45*X^29 + 5*X^28 + 62*X^27 + 20*X^26 + 25*X^25 + 16*X^24 +
      27*X^23 + 58*X^22 + 57*X^21 + 17*X^20 + 16*X^19 + 65*X^18 + 40*X^17 + 29*X^16 + 61*X^15 +
      35*X^14 + 18*X^13 + 32*X^12 + 21*X^11 + 2*X^10 + 14*X^9 + 64*X^8 + 29*X^7 + 64*X^6 + 27*X^5 +
      X^4 + 4*X^3 + 24*X^2 + 41*X) :=
  mul_step (by norm_num) pSeventeenB2s227 pSeventeenB21 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s229 : XPow fSeventeenB2 3387610968045164830418339257207377998338122722
    (4*X^33 + 34*X^32 + 47*X^31 + 23*X^30 + 30*X^29 + 3*X^28 + 10*X^27 + 21*X^26 + 43*X^25 + 53*X^24 +
      37*X^23 + 62*X^22 + 48*X^21 + 35*X^20 + 62*X^19 + 62*X^18 + 65*X^17 + 51*X^16 + 55*X^15 +
      30*X^14 + 31*X^13 + 4*X^12 + 66*X^11 + 3*X^10 + 25*X^9 + 47*X^8 + 19*X^7 + 15*X^6 + 33*X^5 +
      54*X^4 + 36*X^3 + 59*X^2 + 65*X + 47) :=
  sq_step (by norm_num) pSeventeenB2s228 ⟨
    15*X^32 + 61*X^31 + 48*X^30 + 18*X^29 + 28*X^28 + 26*X^27 + 46*X^25 + 63*X^24 + 12*X^23 + 64*X^22 +
      54*X^21 + 25*X^20 + 38*X^19 + 60*X^18 + 20*X^17 + 13*X^16 + 44*X^15 + 42*X^14 + 37*X^13 +
      15*X^12 + 45*X^11 + 39*X^10 + 43*X^9 + 62*X^8 + 37*X^7 + X^6 + 17*X^5 + 58*X^4 + 25*X^3 +
      48*X^2 + 4*X + 35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s230 : XPow fSeventeenB2 6775221936090329660836678514414755996676245444
    (54*X^33 + 32*X^32 + 8*X^31 + 42*X^30 + 45*X^29 + 46*X^28 + 60*X^27 + 55*X^26 + 7*X^25 + 36*X^24 +
      48*X^23 + 44*X^22 + 24*X^21 + 46*X^20 + 28*X^18 + 58*X^17 + 51*X^16 + 45*X^15 + 42*X^14 +
      46*X^13 + 33*X^12 + 34*X^11 + 7*X^10 + 41*X^9 + 29*X^8 + 3*X^7 + X^6 + 49*X^5 + 50*X^4 +
      53*X^3 + 19*X^2 + 31*X + 58) :=
  sq_step (by norm_num) pSeventeenB2s229 ⟨
    16*X^32 + 48*X^31 + 13*X^30 + 11*X^29 + 23*X^28 + 5*X^27 + 60*X^26 + 49*X^25 + 56*X^24 + 6*X^23 +
      11*X^22 + 34*X^21 + 34*X^20 + 45*X^19 + 58*X^18 + 64*X^17 + 62*X^16 + 51*X^15 + 3*X^14 +
      21*X^13 + 8*X^12 + 52*X^11 + 10*X^10 + 27*X^9 + 65*X^8 + 28*X^7 + 30*X^6 + 59*X^5 + 21*X^4 +
      31*X^3 + 4*X^2 + 34*X + 29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s231 : XPow fSeventeenB2 13550443872180659321673357028829511993352490888
    (29*X^33 + 9*X^32 + 58*X^31 + 66*X^30 + 35*X^29 + 55*X^28 + 13*X^27 + 42*X^26 + 25*X^25 + 9*X^24 +
      18*X^23 + 61*X^22 + 43*X^21 + 18*X^20 + 15*X^19 + 4*X^18 + 22*X^17 + 14*X^16 + 55*X^15 +
      17*X^14 + 55*X^13 + 10*X^12 + 6*X^11 + 33*X^10 + 63*X^9 + 16*X^8 + 10*X^7 + 58*X^6 + 56*X^5 +
      65*X^4 + 16*X^3 + 33*X^2 + 7*X + 5) :=
  sq_step (by norm_num) pSeventeenB2s230 ⟨
    35*X^32 + 18*X^31 + 47*X^30 + 14*X^29 + 59*X^28 + 21*X^27 + 16*X^26 + 6*X^25 + 4*X^24 + 26*X^23 +
      15*X^22 + 50*X^21 + 9*X^20 + 12*X^19 + 46*X^18 + 18*X^17 + 31*X^16 + 24*X^15 + 35*X^14 +
      60*X^13 + 21*X^11 + 66*X^10 + 22*X^9 + 39*X^8 + 40*X^7 + 38*X^6 + 41*X^5 + 50*X^4 + 49*X^3 +
      65*X^2 + 55*X + 66,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s232 : XPow fSeventeenB2 27100887744361318643346714057659023986704981776
    (64*X^33 + 38*X^32 + 29*X^31 + 64*X^30 + 16*X^29 + 60*X^28 + 15*X^27 + 17*X^26 + 14*X^25 + 16*X^24 +
      42*X^23 + 9*X^22 + 26*X^21 + 16*X^20 + 11*X^19 + 26*X^18 + 10*X^17 + 46*X^16 + 24*X^15 +
      8*X^14 + 6*X^13 + X^12 + 9*X^11 + 19*X^10 + 13*X^9 + 50*X^8 + 66*X^7 + 44*X^6 + 55*X^5 +
      45*X^3 + 3*X^2 + 45*X + 8) :=
  sq_step (by norm_num) pSeventeenB2s231 ⟨
    37*X^32 + 4*X^31 + 61*X^30 + 26*X^29 + 66*X^28 + 66*X^27 + 32*X^26 + X^25 + 30*X^24 + 26*X^23 +
      44*X^22 + 32*X^21 + 13*X^19 + 22*X^18 + 20*X^17 + 5*X^16 + 27*X^15 + 47*X^14 + 63*X^13 +
      23*X^12 + 18*X^11 + 24*X^10 + 34*X^9 + 30*X^8 + 18*X^7 + 30*X^6 + 60*X^5 + 36*X^4 + 25*X^3 +
      64*X^2 + 9*X + 13,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s233 : XPow fSeventeenB2 27100887744361318643346714057659023986704981777
    (13*X^33 + 58*X^32 + 26*X^31 + 51*X^30 + 27*X^29 + 61*X^28 + 47*X^27 + 33*X^26 + 4*X^25 + 20*X^24 +
      49*X^23 + 42*X^22 + 32*X^21 + 8*X^20 + 6*X^19 + 56*X^18 + 64*X^17 + 65*X^16 + 32*X^15 +
      31*X^14 + 62*X^13 + 3*X^12 + 61*X^11 + 64*X^10 + 7*X^9 + 54*X^8 + 37*X^7 + 52*X^6 + 33*X^5 +
      40*X^4 + 17*X^3 + 42*X^2 + 17*X + 40) :=
  mul_step (by norm_num) pSeventeenB2s232 pSeventeenB21 ⟨
    64,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s234 : XPow fSeventeenB2 54201775488722637286693428115318047973409963554
    (53*X^33 + 58*X^32 + 63*X^31 + 26*X^30 + 27*X^29 + 4*X^28 + 63*X^27 + X^26 + 52*X^25 + 62*X^24 +
      50*X^23 + 58*X^22 + 33*X^21 + 12*X^20 + 31*X^19 + 22*X^18 + X^17 + 7*X^16 + 61*X^15 + 56*X^14 +
      44*X^13 + 12*X^12 + 47*X^11 + 19*X^10 + 34*X^9 + 33*X^8 + 6*X^7 + 58*X^6 + 63*X^5 + 26*X^4 +
      18*X^3 + 26*X^2 + 61*X + 15) :=
  sq_step (by norm_num) pSeventeenB2s233 ⟨
    35*X^32 + 13*X^31 + 58*X^30 + 51*X^29 + 36*X^28 + 38*X^27 + 33*X^26 + 11*X^25 + 19*X^24 + 35*X^23 +
      13*X^22 + 19*X^21 + 15*X^20 + 23*X^19 + 44*X^18 + X^17 + 10*X^16 + 34*X^15 + 22*X^14 + 65*X^13 +
      59*X^12 + 29*X^11 + 27*X^10 + 20*X^9 + 36*X^8 + 33*X^7 + 32*X^6 + 39*X^5 + 66*X^4 + 12*X^3 +
      63*X^2 + 60*X + 10,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s235 : XPow fSeventeenB2 108403550977445274573386856230636095946819927108
    (64*X^33 + 62*X^32 + 50*X^31 + 19*X^30 + 24*X^29 + 61*X^28 + 12*X^27 + 36*X^26 + 44*X^25 + 23*X^24 +
      37*X^23 + 58*X^22 + 47*X^20 + 31*X^19 + 15*X^18 + 34*X^17 + 59*X^16 + 50*X^15 + 63*X^14 +
      60*X^13 + 20*X^12 + 48*X^11 + 44*X^10 + 60*X^9 + 26*X^8 + 59*X^7 + 38*X^6 + 36*X^5 + 34*X^4 +
      9*X^3 + 51*X^2 + 49*X + 1) :=
  sq_step (by norm_num) pSeventeenB2s234 ⟨
    62*X^32 + 54*X^31 + 66*X^30 + X^29 + 66*X^28 + 64*X^27 + 63*X^26 + 40*X^25 + 51*X^24 + 32*X^23 +
      18*X^22 + 34*X^21 + 54*X^20 + 10*X^19 + 24*X^18 + 58*X^17 + 58*X^16 + 59*X^15 + 42*X^14 +
      57*X^13 + 28*X^12 + 61*X^11 + 13*X^10 + 49*X^9 + 63*X^8 + 34*X^7 + 59*X^6 + 41*X^5 + 9*X^4 +
      12*X^3 + 55*X^2 + 37*X + 57,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s236 : XPow fSeventeenB2 216807101954890549146773712461272191893639854216
    (5*X^33 + 42*X^32 + 3*X^31 + 35*X^30 + 26*X^28 + 45*X^27 + 41*X^26 + 58*X^25 + X^24 + 31*X^23 +
      8*X^22 + 31*X^21 + 45*X^20 + 18*X^19 + 21*X^18 + 65*X^17 + 50*X^16 + 21*X^15 + 2*X^14 +
      40*X^13 + 63*X^12 + 52*X^11 + 58*X^10 + 5*X^9 + 63*X^8 + 58*X^7 + 8*X^6 + 4*X^5 + 35*X^4 +
      60*X^3 + 34*X^2 + 18*X + 44) :=
  sq_step (by norm_num) pSeventeenB2s235 ⟨
    9*X^32 + 38*X^31 + 44*X^30 + 13*X^29 + 59*X^28 + 64*X^27 + 8*X^26 + 32*X^25 + 66*X^24 + 22*X^23 +
      34*X^22 + 31*X^21 + 4*X^20 + 34*X^19 + 31*X^18 + 63*X^17 + 2*X^16 + 18*X^14 + 10*X^13 +
      13*X^12 + 8*X^11 + 64*X^10 + 26*X^9 + 27*X^8 + 15*X^7 + 21*X^6 + 27*X^5 + 23*X^4 + 63*X^3 +
      18*X^2 + 20*X + 42,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s237 : XPow fSeventeenB2 216807101954890549146773712461272191893639854217
    (39*X^33 + 44*X^32 + 9*X^31 + 31*X^30 + 14*X^29 + 13*X^28 + 58*X^27 + 4*X^26 + 21*X^25 + 23*X^24 +
      53*X^23 + 49*X^22 + 63*X^21 + 23*X^20 + 32*X^19 + 33*X^18 + 20*X^17 + 42*X^16 + 29*X^15 +
      43*X^14 + 6*X^13 + 62*X^12 + 55*X^11 + 54*X^10 + 23*X^9 + 11*X^8 + 42*X^7 + 9*X^6 + 47*X^5 +
      46*X^4 + 33*X^3 + 23*X^2 + 29*X + 45) :=
  mul_step (by norm_num) pSeventeenB2s236 pSeventeenB21 ⟨
    5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s238 : XPow fSeventeenB2 433614203909781098293547424922544383787279708434
    (44*X^33 + 60*X^32 + 8*X^31 + 43*X^30 + 25*X^29 + 22*X^28 + 19*X^27 + 59*X^26 + 29*X^25 + 12*X^24 +
      42*X^23 + 57*X^22 + 49*X^21 + 49*X^20 + 49*X^19 + 39*X^18 + 30*X^17 + X^16 + 46*X^15 + 63*X^14 +
      31*X^13 + 57*X^12 + 2*X^11 + 13*X^10 + 22*X^9 + 26*X^8 + 18*X^7 + 31*X^6 + 31*X^5 + 9*X^4 +
      41*X^3 + 7*X^2 + 36*X + 1) :=
  sq_step (by norm_num) pSeventeenB2s237 ⟨
    47*X^32 + 27*X^31 + 19*X^30 + 40*X^29 + 3*X^28 + 4*X^27 + 2*X^26 + 10*X^25 + 34*X^24 + 51*X^23 +
      64*X^22 + 44*X^21 + 3*X^20 + 11*X^19 + 27*X^18 + 9*X^17 + 19*X^16 + 35*X^15 + 40*X^14 +
      17*X^13 + 3*X^12 + 60*X^11 + 14*X^10 + 29*X^9 + 12*X^8 + 5*X^7 + 65*X^6 + 8*X^5 + 62*X^4 +
      10*X^3 + 51*X^2 + 46*X + 58,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s239 : XPow fSeventeenB2 867228407819562196587094849845088767574559416868
    (56*X^33 + 8*X^32 + 19*X^31 + 10*X^30 + 53*X^29 + 56*X^28 + 49*X^27 + 10*X^26 + 38*X^25 + 21*X^24 +
      59*X^23 + 33*X^22 + 28*X^21 + 53*X^20 + 53*X^19 + 50*X^18 + 32*X^17 + 37*X^16 + 42*X^15 +
      51*X^14 + 66*X^13 + 56*X^12 + 61*X^11 + 19*X^10 + 41*X^9 + 65*X^8 + 9*X^7 + 66*X^6 + 39*X^5 +
      36*X^4 + 31*X^3 + 13*X^2 + 5*X) :=
  sq_step (by norm_num) pSeventeenB2s238 ⟨
    60*X^32 + 18*X^31 + 55*X^30 + 4*X^29 + 44*X^28 + 19*X^27 + 23*X^26 + 60*X^25 + 66*X^24 + 56*X^23 +
      4*X^22 + 40*X^21 + 43*X^20 + 54*X^19 + 35*X^18 + 58*X^17 + 23*X^16 + 2*X^15 + 61*X^14 +
      44*X^13 + 9*X^12 + 5*X^11 + 16*X^10 + 44*X^9 + 58*X^8 + 48*X^7 + 38*X^6 + 8*X^5 + 18*X^4 +
      27*X^3 + 42*X^2 + 62*X + 52,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s240 : XPow fSeventeenB2 867228407819562196587094849845088767574559416869
    (28*X^33 + 36*X^32 + 27*X^31 + 25*X^30 + 2*X^29 + 39*X^28 + 53*X^27 + 63*X^26 + 44*X^25 + 23*X^24 +
      X^23 + 42*X^22 + 42*X^20 + 66*X^19 + 22*X^18 + 36*X^17 + 36*X^16 + 5*X^15 + 46*X^14 + 34*X^13 +
      39*X^12 + 39*X^11 + 27*X^10 + 19*X^9 + 32*X^8 + 18*X^7 + 28*X^6 + 23*X^5 + 35*X^4 + 42*X^3 +
      61*X^2 + 33*X + 35) :=
  mul_step (by norm_num) pSeventeenB2s239 pSeventeenB21 ⟨
    56,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s241 : XPow fSeventeenB2 1734456815639124393174189699690177535149118833738
    (59*X^33 + 43*X^32 + 31*X^31 + 38*X^30 + 46*X^29 + 6*X^28 + 43*X^27 + 41*X^26 + 39*X^25 + 64*X^24 +
      36*X^23 + 14*X^22 + 42*X^21 + X^20 + 4*X^19 + 52*X^18 + 61*X^16 + 47*X^15 + 8*X^14 + 17*X^13 +
      44*X^12 + 42*X^11 + 43*X^10 + 6*X^9 + 44*X^8 + 63*X^7 + 53*X^6 + 12*X^5 + 2*X^4 + 27*X^3 +
      25*X^2 + X + 33) :=
  sq_step (by norm_num) pSeventeenB2s240 ⟨
    47*X^32 + 18*X^31 + 47*X^30 + 3*X^29 + 60*X^28 + 4*X^27 + 16*X^26 + 46*X^25 + 46*X^24 + 11*X^23 +
      53*X^22 + 18*X^21 + 19*X^20 + 10*X^19 + 43*X^18 + 26*X^17 + 29*X^16 + 22*X^15 + 6*X^14 +
      25*X^13 + 45*X^12 + 47*X^11 + 29*X^10 + 15*X^9 + 61*X^8 + 43*X^7 + 57*X^6 + 13*X^5 + X^4 +
      11*X^3 + 34*X^2 + 7*X + 9,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s242 : XPow fSeventeenB2 3468913631278248786348379399380355070298237667476
    (29*X^33 + 47*X^32 + 61*X^31 + 25*X^30 + 51*X^29 + 29*X^28 + 46*X^27 + 31*X^26 + 42*X^25 + 62*X^24 +
      53*X^23 + 26*X^22 + 29*X^21 + 3*X^19 + 52*X^18 + 46*X^17 + 20*X^16 + 34*X^15 + 18*X^14 +
      34*X^13 + 57*X^12 + 8*X^11 + 31*X^10 + 13*X^9 + 14*X^7 + 52*X^6 + X^5 + 20*X^4 + 52*X^3 +
      2*X^2 + 62*X + 3) :=
  sq_step (by norm_num) pSeventeenB2s241 ⟨
    64*X^32 + 24*X^31 + 41*X^30 + 8*X^29 + 63*X^28 + 36*X^27 + 63*X^26 + 21*X^25 + 10*X^24 + 58*X^23 +
      2*X^22 + 4*X^21 + 16*X^20 + 10*X^19 + 34*X^18 + 57*X^17 + 16*X^16 + 24*X^15 + 13*X^14 +
      28*X^13 + 31*X^12 + 37*X^11 + 31*X^10 + 29*X^9 + 23*X^8 + 17*X^7 + 56*X^6 + 15*X^5 + 12*X^4 +
      47*X^3 + 35*X^2 + 4*X + 58,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s243 : XPow fSeventeenB2 3468913631278248786348379399380355070298237667477
    (43*X^33 + 4*X^32 + 35*X^31 + 3*X^30 + 13*X^29 + 48*X^28 + 9*X^27 + 37*X^26 + 44*X^25 + 20*X^24 +
      19*X^23 + 53*X^22 + 24*X^21 + 32*X^20 + 22*X^19 + 48*X^18 + 47*X^17 + 62*X^16 + 54*X^15 +
      38*X^14 + 48*X^13 + 66*X^12 + 27*X^11 + 56*X^10 + 36*X^9 + 63*X^8 + 8*X^7 + 30*X^6 + 36*X^5 +
      11*X^4 + 23*X^3 + 24*X^2 + 50*X + 60) :=
  mul_step (by norm_num) pSeventeenB2s242 pSeventeenB21 ⟨
    29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s244 : XPow fSeventeenB2 6937827262556497572696758798760710140596475334954
    (35*X^33 + 45*X^32 + 49*X^30 + 33*X^29 + 6*X^28 + 40*X^27 + 35*X^26 + 40*X^25 + 3*X^24 + 34*X^23 +
      63*X^22 + 2*X^21 + 15*X^20 + 7*X^19 + 59*X^18 + 17*X^17 + 66*X^16 + 8*X^15 + 32*X^14 + 45*X^13 +
      19*X^12 + 43*X^11 + 9*X^10 + 64*X^9 + 4*X^8 + 64*X^7 + 33*X^6 + 35*X^5 + 61*X^4 + 24*X^3 +
      35*X^2 + 12*X + 52) :=
  sq_step (by norm_num) pSeventeenB2s243 ⟨
    40*X^32 + 52*X^31 + 13*X^30 + 25*X^29 + 51*X^28 + 45*X^27 + 28*X^26 + 6*X^25 + 25*X^24 + 38*X^23 +
      15*X^22 + 19*X^21 + 13*X^20 + 24*X^19 + 41*X^18 + X^17 + 46*X^16 + 56*X^15 + 20*X^14 + 47*X^13 +
      23*X^12 + 66*X^11 + 53*X^10 + 61*X^9 + 45*X^8 + 57*X^7 + 64*X^6 + 57*X^5 + 40*X^4 + 62*X^3 +
      33*X^2 + 42*X + 45,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s245 : XPow fSeventeenB2 6937827262556497572696758798760710140596475334955
    (24*X^33 + 19*X^32 + X^31 + 49*X^30 + 56*X^29 + 17*X^28 + 20*X^27 + 64*X^26 + 9*X^25 + 45*X^24 +
      43*X^23 + 61*X^22 + 7*X^21 + 42*X^20 + 2*X^19 + 61*X^18 + 57*X^17 + 21*X^16 + 20*X^15 +
      66*X^14 + 22*X^13 + 46*X^12 + 55*X^11 + 5*X^10 + 59*X^9 + 3*X^8 + 3*X^7 + 3*X^6 + 11*X^5 +
      60*X^4 + 28*X^3 + 47*X^2 + 14*X + 47) :=
  mul_step (by norm_num) pSeventeenB2s244 pSeventeenB21 ⟨
    35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s246 : XPow fSeventeenB2 13875654525112995145393517597521420281192950669910
    (40*X^33 + 59*X^32 + 13*X^31 + 56*X^29 + 29*X^28 + 46*X^27 + 12*X^26 + 52*X^25 + 7*X^24 + 43*X^23 +
      49*X^22 + 36*X^21 + 32*X^20 + 6*X^19 + 5*X^18 + 14*X^17 + 20*X^16 + 32*X^15 + 38*X^14 +
      37*X^13 + 29*X^12 + 21*X^11 + 28*X^10 + 13*X^9 + 35*X^8 + 65*X^7 + 41*X^6 + 33*X^5 + 55*X^4 +
      19*X^3 + 53*X^2 + 4*X + 58) :=
  sq_step (by norm_num) pSeventeenB2s245 ⟨
    40*X^32 + 17*X^31 + 30*X^30 + 12*X^29 + 45*X^28 + 59*X^27 + 45*X^26 + 12*X^25 + 8*X^24 + 47*X^23 +
      38*X^22 + 33*X^21 + 47*X^20 + 42*X^19 + 49*X^18 + 17*X^17 + 58*X^16 + 59*X^15 + 17*X^14 +
      50*X^13 + 12*X^12 + 31*X^11 + 6*X^10 + 59*X^9 + 48*X^8 + 37*X^7 + 49*X^6 + 31*X^4 + 9*X^3 +
      65*X^2 + 50*X + 29,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s247 : XPow fSeventeenB2 13875654525112995145393517597521420281192950669911
    (35*X^33 + 6*X^32 + 60*X^31 + 36*X^30 + 58*X^28 + 14*X^27 + 22*X^26 + 33*X^25 + 46*X^24 + 7*X^23 +
      46*X^22 + 42*X^21 + 46*X^20 + 26*X^19 + 26*X^18 + 48*X^17 + 66*X^16 + 53*X^15 + 61*X^14 +
      42*X^13 + 34*X^12 + 4*X^11 + 3*X^10 + 50*X^9 + 24*X^8 + 45*X^7 + 6*X^6 + 17*X^5 + 41*X^4 +
      45*X^3 + 44*X^2 + 5*X + 25) :=
  mul_step (by norm_num) pSeventeenB2s246 pSeventeenB21 ⟨
    40,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s248 : XPow fSeventeenB2 27751309050225990290787035195042840562385901339822
    (47*X^33 + 50*X^32 + 30*X^31 + 30*X^30 + 30*X^29 + 7*X^28 + 57*X^27 + 63*X^26 + 39*X^25 + 44*X^24 +
      12*X^23 + 43*X^22 + 8*X^21 + 32*X^20 + 24*X^19 + 30*X^18 + 3*X^17 + 21*X^16 + 63*X^15 + 6*X^14 +
      9*X^12 + 26*X^11 + 10*X^10 + 26*X^9 + 35*X^8 + 63*X^7 + 5*X^6 + 45*X^5 + 52*X^4 + 37*X^3 +
      17*X^2 + 53*X + 21) :=
  sq_step (by norm_num) pSeventeenB2s247 ⟨
    19*X^32 + 20*X^31 + 65*X^30 + 10*X^29 + 57*X^28 + 21*X^27 + 17*X^26 + 28*X^25 + 59*X^24 + 37*X^23 +
      65*X^22 + 39*X^21 + 47*X^20 + 29*X^19 + 27*X^18 + 38*X^17 + 24*X^16 + 4*X^15 + 39*X^14 +
      57*X^13 + 15*X^12 + 22*X^11 + 60*X^10 + 27*X^9 + 49*X^8 + 38*X^7 + 57*X^6 + 36*X^5 + 17*X^4 +
      48*X^3 + 65*X^2 + 55*X + 52,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s249 : XPow fSeventeenB2 55502618100451980581574070390085681124771802679644
    (9*X^33 + 32*X^32 + 59*X^31 + 62*X^30 + 61*X^28 + 48*X^27 + 51*X^26 + 39*X^25 + 37*X^24 + 58*X^23 +
      21*X^22 + 10*X^21 + 36*X^20 + 46*X^19 + 22*X^18 + 39*X^17 + 35*X^16 + 32*X^15 + 15*X^14 +
      30*X^13 + X^12 + 24*X^11 + 21*X^10 + 15*X^9 + 10*X^8 + 46*X^7 + 12*X^6 + 13*X^5 + 52*X^4 +
      37*X^3 + 4*X^2 + 9*X + 8) :=
  sq_step (by norm_num) pSeventeenB2s248 ⟨
    65*X^32 + 38*X^31 + 28*X^30 + 55*X^29 + 20*X^28 + 2*X^27 + 20*X^26 + 58*X^25 + 35*X^24 + 60*X^23 +
      9*X^22 + 50*X^21 + 45*X^20 + 59*X^19 + 50*X^18 + 2*X^17 + 22*X^16 + 18*X^15 + 7*X^14 + 33*X^13 +
      36*X^12 + 41*X^11 + 46*X^10 + 40*X^9 + 34*X^8 + 47*X^7 + 25*X^6 + 51*X^5 + 8*X^4 + 14*X^3 +
      48*X^2 + 23*X + 4,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s250 : XPow fSeventeenB2 111005236200903961163148140780171362249543605359288
    (17*X^33 + 36*X^32 + 55*X^31 + 50*X^30 + X^29 + 62*X^28 + 13*X^27 + 66*X^26 + 53*X^25 + 17*X^24 +
      30*X^23 + 16*X^22 + 58*X^21 + 66*X^20 + 39*X^19 + 27*X^18 + 13*X^17 + 19*X^16 + 37*X^15 +
      62*X^14 + 22*X^13 + X^12 + 62*X^11 + 7*X^10 + 33*X^9 + 6*X^8 + 31*X^7 + 13*X^6 + 40*X^5 +
      27*X^4 + 44*X^3 + 9*X^2 + 28*X + 19) :=
  sq_step (by norm_num) pSeventeenB2s249 ⟨
    14*X^32 + 45*X^31 + 3*X^30 + 14*X^29 + 15*X^28 + 53*X^27 + 63*X^26 + 23*X^25 + 3*X^24 + 21*X^23 +
      14*X^22 + 47*X^21 + 24*X^20 + 8*X^19 + 4*X^18 + 19*X^17 + 8*X^16 + 65*X^15 + 2*X^14 + 46*X^13 +
      65*X^12 + 13*X^11 + 66*X^10 + 28*X^9 + 57*X^8 + 64*X^7 + 53*X^6 + 22*X^5 + 18*X^4 + 13*X^3 +
      60*X^2 + 45*X + 62,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s251 : XPow fSeventeenB2 111005236200903961163148140780171362249543605359289
    (66*X^33 + 47*X^32 + 42*X^31 + 26*X^30 + 48*X^29 + 65*X^28 + 30*X^27 + 57*X^26 + 18*X^25 + 43*X^24 +
      35*X^23 + 12*X^22 + 20*X^21 + 56*X^20 + 51*X^19 + 65*X^18 + 51*X^17 + 28*X^16 + 60*X^15 +
      59*X^14 + 35*X^13 + 29*X^12 + 37*X^11 + 12*X^10 + 4*X^9 + 32*X^8 + 8*X^7 + 57*X^6 + 41*X^5 +
      50*X^4 + 19*X^3 + 45*X^2 + 35*X + 19) :=
  mul_step (by norm_num) pSeventeenB2s250 pSeventeenB21 ⟨
    17,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s252 : XPow fSeventeenB2 222010472401807922326296281560342724499087210718578
    (23*X^33 + 12*X^32 + 18*X^31 + 48*X^30 + 60*X^29 + 46*X^28 + 17*X^27 + 25*X^26 + 56*X^25 + 51*X^24 +
      50*X^23 + 21*X^22 + 28*X^21 + 16*X^20 + 63*X^19 + 59*X^18 + 59*X^17 + 35*X^16 + 43*X^15 +
      24*X^14 + 63*X^13 + 51*X^12 + 14*X^11 + 37*X^9 + 49*X^8 + 38*X^7 + 42*X^6 + 48*X^5 + 62*X^3 +
      55*X + 23) :=
  sq_step (by norm_num) pSeventeenB2s251 ⟨
    X^32 + 26*X^31 + 54*X^30 + 65*X^29 + 5*X^28 + 6*X^27 + 57*X^26 + 28*X^25 + 5*X^24 + 66*X^23 +
      46*X^22 + 5*X^21 + 42*X^20 + 5*X^19 + 58*X^18 + 41*X^17 + 12*X^15 + 55*X^14 + X^13 + 41*X^12 +
      33*X^11 + 15*X^10 + 58*X^9 + 62*X^8 + 21*X^7 + 10*X^6 + 49*X^5 + 43*X^4 + 22*X^3 + 51*X^2 +
      22*X + 22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s253 : XPow fSeventeenB2 444020944803615844652592563120685448998174421437156
    (40*X^33 + 28*X^32 + 25*X^31 + 41*X^30 + 31*X^29 + 2*X^28 + 49*X^27 + 51*X^26 + 46*X^25 + 32*X^24 +
      14*X^23 + 37*X^22 + 18*X^21 + 2*X^20 + 4*X^19 + 62*X^18 + 44*X^17 + 50*X^16 + 65*X^15 +
      59*X^14 + 51*X^13 + 21*X^12 + 30*X^11 + 44*X^10 + 29*X^9 + 34*X^8 + 44*X^7 + 56*X^6 + 49*X^5 +
      44*X^4 + 44*X^3 + 20*X^2 + 8*X + 18) :=
  sq_step (by norm_num) pSeventeenB2s252 ⟨
    60*X^32 + 47*X^31 + 2*X^30 + 59*X^29 + 3*X^28 + 7*X^27 + 45*X^26 + 7*X^25 + 38*X^24 + 6*X^23 +
      31*X^22 + 31*X^21 + 22*X^20 + 62*X^19 + 7*X^18 + 54*X^17 + 27*X^16 + 30*X^15 + 31*X^14 +
      4*X^13 + 29*X^12 + 48*X^11 + 24*X^9 + 25*X^8 + 37*X^7 + 21*X^6 + 3*X^5 + 42*X^4 + 60*X^3 +
      2*X^2 + 16*X + 40,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s254 : XPow fSeventeenB2 444020944803615844652592563120685448998174421437157
    (4*X^33 + 18*X^32 + 34*X^31 + 11*X^30 + 40*X^29 + 61*X^28 + 53*X^27 + 16*X^26 + 58*X^25 + 17*X^24 +
      62*X^23 + 28*X^22 + 12*X^21 + 44*X^20 + 16*X^19 + 56*X^18 + 11*X^17 + 32*X^16 + 7*X^15 +
      8*X^14 + 34*X^13 + 43*X^12 + 20*X^11 + 19*X^10 + 49*X^9 + 3*X^8 + 60*X^7 + 22*X^6 + 6*X^5 +
      66*X^4 + 12*X^3 + 48*X^2 + 32*X + 25) :=
  mul_step (by norm_num) pSeventeenB2s253 pSeventeenB21 ⟨
    40,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s255 : XPow fSeventeenB2 888041889607231689305185126241370897996348842874314
    (3*X^33 + 46*X^31 + 19*X^30 + 29*X^29 + 24*X^28 + 55*X^27 + 50*X^26 + 60*X^25 + 4*X^24 + 55*X^23 +
      53*X^22 + 32*X^21 + 23*X^20 + 24*X^19 + 48*X^18 + 16*X^17 + X^16 + 9*X^15 + 14*X^14 + 23*X^13 +
      9*X^12 + 30*X^11 + 59*X^8 + 23*X^7 + 66*X^6 + 65*X^5 + 36*X^4 + 49*X^3 + 38*X^2 + 19*X + 2) :=
  sq_step (by norm_num) pSeventeenB2s254 ⟨
    16*X^32 + 54*X^31 + 65*X^30 + 38*X^29 + 3*X^28 + 23*X^27 + 45*X^26 + 17*X^25 + 31*X^24 + 35*X^23 +
      66*X^22 + 66*X^21 + 23*X^20 + 60*X^19 + 26*X^18 + 65*X^17 + 57*X^16 + 34*X^15 + 64*X^14 +
      34*X^12 + 48*X^11 + 37*X^10 + 36*X^9 + 56*X^8 + 63*X^7 + 39*X^6 + 21*X^5 + 32*X^4 + 10*X^3 +
      64*X^2 + 37*X + 35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s256 : XPow fSeventeenB2 888041889607231689305185126241370897996348842874315
    (25*X^33 + 17*X^32 + 57*X^31 + 61*X^30 + 57*X^29 + 9*X^28 + 20*X^27 + 41*X^26 + 16*X^25 + 10*X^24 +
      13*X^23 + 16*X^22 + 7*X^21 + 27*X^20 + X^19 + 37*X^18 + 50*X^17 + 35*X^16 + 57*X^15 + 65*X^14 +
      15*X^13 + 36*X^12 + 25*X^11 + 16*X^10 + 35*X^9 + 35*X^8 + 6*X^7 + X^6 + 3*X^5 + 54*X^4 +
      24*X^3 + 22*X^2 + 60*X + 27) :=
  mul_step (by norm_num) pSeventeenB2s255 pSeventeenB21 ⟨
    3,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s257 : XPow fSeventeenB2 1776083779214463378610370252482741795992697685748630
    (42*X^33 + 49*X^32 + 38*X^31 + 66*X^30 + 65*X^29 + 16*X^28 + 6*X^27 + 15*X^26 + 26*X^25 + 33*X^24 +
      4*X^23 + 25*X^22 + 41*X^21 + 22*X^20 + 62*X^19 + 14*X^18 + 19*X^17 + 38*X^16 + 65*X^15 +
      32*X^14 + 34*X^13 + 54*X^12 + 58*X^11 + 63*X^10 + 39*X^9 + 26*X^8 + 47*X^7 + 57*X^6 + 21*X^5 +
      19*X^4 + 22*X^3 + 3*X^2 + 37*X + 26) :=
  sq_step (by norm_num) pSeventeenB2s256 ⟨
    22*X^32 + 6*X^31 + 6*X^30 + 55*X^29 + 40*X^28 + 34*X^27 + 52*X^26 + 4*X^25 + 31*X^24 + 51*X^23 +
      37*X^22 + 8*X^21 + 23*X^20 + 4*X^19 + 53*X^18 + 49*X^17 + 5*X^16 + 40*X^15 + 64*X^14 + 45*X^13 +
      26*X^12 + 6*X^11 + 20*X^10 + 17*X^9 + 38*X^8 + 5*X^7 + 15*X^6 + 28*X^5 + 41*X^4 + 28*X^3 +
      47*X^2 + 30*X + 41,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s258 : XPow fSeventeenB2 1776083779214463378610370252482741795992697685748631
    (64*X^33 + 34*X^32 + 62*X^31 + 44*X^30 + 9*X^29 + 32*X^28 + 64*X^27 + 28*X^26 + 44*X^24 + X^23 +
      18*X^22 + 66*X^21 + 37*X^20 + 26*X^19 + 45*X^18 + 54*X^17 + 27*X^16 + 31*X^15 + 19*X^14 +
      4*X^13 + 8*X^12 + 11*X^11 + 62*X^10 + 25*X^9 + 14*X^8 + 21*X^7 + 63*X^6 + 26*X^5 + 25*X^4 +
      8*X^3 + 12*X^2 + 34*X + 43) :=
  mul_step (by norm_num) pSeventeenB2s257 pSeventeenB21 ⟨
    42,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s259 : XPow fSeventeenB2 3552167558428926757220740504965483591985395371497262
    (33*X^33 + 30*X^32 + 29*X^31 + 43*X^30 + 45*X^29 + 22*X^28 + 34*X^27 + 11*X^26 + 2*X^25 + 53*X^24 +
      45*X^23 + 33*X^22 + 59*X^21 + 55*X^20 + 6*X^19 + 35*X^17 + 26*X^16 + 54*X^15 + 56*X^14 +
      60*X^13 + 29*X^12 + 63*X^11 + X^10 + 2*X^9 + 26*X^8 + 8*X^7 + 36*X^6 + 4*X^5 + 46*X^4 + 26*X^3 +
      31*X^2 + 26*X + 28) :=
  sq_step (by norm_num) pSeventeenB2s258 ⟨
    9*X^32 + 5*X^31 + 24*X^30 + 19*X^29 + 56*X^28 + 27*X^27 + 28*X^26 + 32*X^25 + 51*X^24 + 57*X^23 +
      35*X^22 + 32*X^21 + 41*X^20 + 65*X^19 + 35*X^18 + 64*X^17 + 38*X^16 + 25*X^15 + 26*X^14 +
      62*X^13 + 40*X^12 + 11*X^11 + 4*X^9 + 32*X^8 + 8*X^7 + 6*X^6 + 44*X^5 + 34*X^4 + 34*X^3 +
      55*X^2 + 20*X + 21,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s260 : XPow fSeventeenB2 3552167558428926757220740504965483591985395371497263
    (37*X^33 + 45*X^32 + 59*X^31 + 62*X^30 + 50*X^29 + 64*X^28 + 16*X^27 + 61*X^26 + 51*X^25 + 19*X^24 +
      62*X^23 + 17*X^22 + 13*X^21 + 39*X^20 + 19*X^19 + 65*X^18 + 29*X^17 + 5*X^16 + 60*X^15 +
      53*X^14 + 28*X^13 + 62*X^12 + 8*X^11 + 44*X^10 + 30*X^9 + 6*X^8 + 46*X^7 + 37*X^6 + 18*X^5 +
      14*X^4 + 11*X^3 + 59*X^2 + 63*X + 29) :=
  mul_step (by norm_num) pSeventeenB2s259 pSeventeenB21 ⟨
    33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s261 : XPow fSeventeenB2 7104335116857853514441481009930967183970790742994526
    (15*X^33 + 59*X^32 + 3*X^31 + 36*X^29 + 65*X^28 + 54*X^27 + 33*X^26 + 30*X^25 + 65*X^24 + 47*X^23 +
      3*X^22 + 34*X^21 + 28*X^20 + 28*X^19 + 48*X^18 + 19*X^17 + 18*X^16 + 22*X^15 + 34*X^14 +
      27*X^12 + 15*X^11 + 58*X^10 + 45*X^9 + 41*X^8 + 9*X^7 + 64*X^6 + 20*X^5 + 56*X^4 + 51*X^3 +
      47*X^2 + 28*X + 61) :=
  sq_step (by norm_num) pSeventeenB2s260 ⟨
    29*X^32 + 43*X^31 + 37*X^30 + 41*X^29 + 65*X^28 + 10*X^27 + 45*X^26 + 22*X^25 + 31*X^24 + 63*X^23 +
      43*X^22 + 32*X^21 + 42*X^20 + 39*X^19 + 32*X^18 + 43*X^17 + 7*X^16 + 28*X^15 + 24*X^14 +
      49*X^13 + 50*X^12 + 17*X^11 + 51*X^10 + 40*X^9 + 53*X^7 + 61*X^6 + 63*X^5 + 39*X^4 + 30*X^3 +
      15*X^2 + 25,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s262 : XPow fSeventeenB2 7104335116857853514441481009930967183970790742994527
    (50*X^33 + 59*X^32 + 56*X^31 + 62*X^30 + 29*X^29 + 25*X^28 + 17*X^27 + 2*X^26 + 58*X^25 + 23*X^24 +
      4*X^23 + 21*X^22 + 15*X^21 + 43*X^20 + 14*X^19 + 57*X^18 + 62*X^17 + 18*X^16 + 48*X^15 +
      9*X^14 + 57*X^13 + 45*X^12 + 49*X^11 + 58*X^10 + 55*X^9 + 2*X^8 + 32*X^7 + 35*X^6 + 25*X^5 +
      9*X^4 + 44*X^3 + 43*X^2 + 16*X + 1) :=
  mul_step (by norm_num) pSeventeenB2s261 pSeventeenB21 ⟨
    15,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s263 : XPow fSeventeenB2 14208670233715707028882962019861934367941581485989054
    (3*X^33 + 12*X^32 + 60*X^31 + 8*X^30 + 2*X^29 + 66*X^28 + 56*X^27 + 58*X^26 + 4*X^25 + 28*X^24 +
      62*X^23 + 49*X^22 + 35*X^21 + 14*X^20 + 42*X^19 + 29*X^18 + 25*X^17 + 59*X^16 + 62*X^15 +
      13*X^14 + 57*X^13 + 16*X^12 + 53*X^11 + 61*X^10 + 8*X^9 + 47*X^8 + 31*X^7 + 24*X^6 + 24*X^5 +
      28*X^4 + 29*X^3 + 54*X^2 + 6*X + 40) :=
  sq_step (by norm_num) pSeventeenB2s262 ⟨
    21*X^32 + 45*X^31 + 7*X^30 + 12*X^29 + 19*X^28 + 40*X^27 + 8*X^26 + 11*X^25 + 31*X^24 + 27*X^23 +
      56*X^22 + 20*X^21 + 55*X^20 + 37*X^19 + 61*X^18 + 34*X^17 + 50*X^16 + 31*X^15 + 17*X^14 +
      28*X^13 + 63*X^12 + 20*X^11 + 51*X^10 + 16*X^9 + 49*X^8 + 17*X^7 + 55*X^6 + 55*X^5 + 16*X^4 +
      52*X^3 + 39*X^2 + 6*X + 49,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s264 : XPow fSeventeenB2 14208670233715707028882962019861934367941581485989055
    (37*X^33 + 31*X^32 + 46*X^31 + 34*X^30 + 32*X^29 + 10*X^28 + 28*X^27 + 52*X^26 + 40*X^25 + 17*X^24 +
      9*X^23 + 19*X^22 + 65*X^21 + 45*X^20 + 49*X^19 + 46*X^18 + 41*X^17 + 21*X^16 + 56*X^15 +
      32*X^14 + 22*X^13 + 59*X^12 + 19*X^11 + 24*X^10 + 23*X^9 + 43*X^8 + 31*X^7 + 27*X^6 + 62*X^5 +
      34*X^4 + 40*X^3 + 9*X^2 + 31*X + 27) :=
  mul_step (by norm_num) pSeventeenB2s263 pSeventeenB21 ⟨
    3,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s265 : XPow fSeventeenB2 28417340467431414057765924039723868735883162971978110
    (56*X^33 + X^32 + X^31 + 65*X^30 + 48*X^29 + 39*X^28 + 64*X^27 + 45*X^26 + 58*X^25 + 12*X^24 +
      59*X^23 + 35*X^22 + 30*X^21 + 44*X^20 + 59*X^19 + 51*X^18 + 3*X^17 + 11*X^16 + 46*X^15 +
      51*X^14 + 38*X^13 + 42*X^12 + 61*X^11 + 45*X^10 + 50*X^9 + 17*X^8 + 5*X^7 + 8*X^6 + 26*X^5 +
      8*X^4 + 32*X^3 + X^2 + 47*X + 54) :=
  sq_step (by norm_num) pSeventeenB2s264 ⟨
    29*X^32 + 12*X^31 + 53*X^30 + 31*X^29 + 10*X^28 + 54*X^27 + 41*X^26 + 21*X^25 + 7*X^24 + 17*X^23 +
      3*X^22 + 13*X^21 + 41*X^20 + 12*X^19 + 13*X^18 + 27*X^17 + 20*X^16 + 28*X^15 + 23*X^14 +
      43*X^13 + 32*X^12 + 51*X^11 + 49*X^10 + 49*X^9 + 63*X^8 + 56*X^7 + 15*X^6 + 38*X^5 + 4*X^4 +
      66*X^3 + 57*X^2 + 25*X + 59,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s266 : XPow fSeventeenB2 56834680934862828115531848079447737471766325943956220
    (3*X^33 + 3*X^32 + 25*X^31 + 27*X^30 + 15*X^29 + 31*X^28 + 16*X^27 + 57*X^26 + 65*X^25 + 8*X^24 +
      23*X^23 + 5*X^22 + 10*X^21 + 12*X^20 + 5*X^19 + 26*X^18 + 55*X^16 + 60*X^15 + 3*X^14 + 41*X^13 +
      46*X^12 + 13*X^11 + 38*X^10 + X^9 + 53*X^8 + 24*X^7 + 20*X^6 + X^5 + 53*X^4 + 18*X^3 + 30*X^2 +
      19*X + 33) :=
  sq_step (by norm_num) pSeventeenB2s265 ⟨
    54*X^32 + 26*X^31 + 31*X^30 + 38*X^28 + 33*X^27 + 52*X^26 + 27*X^25 + 51*X^23 + 50*X^22 + 16*X^21 +
      37*X^20 + 13*X^19 + 25*X^18 + 28*X^17 + 21*X^16 + 51*X^15 + 11*X^14 + 57*X^13 + 42*X^12 +
      55*X^11 + 12*X^10 + 18*X^9 + 57*X^8 + 34*X^7 + 25*X^6 + 66*X^5 + 38*X^4 + 32*X^3 + 40*X^2 +
      46*X + 37,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s267 : XPow fSeventeenB2 113669361869725656231063696158895474943532651887912440
    (30*X^33 + 7*X^32 + 29*X^31 + 5*X^30 + 8*X^29 + 3*X^28 + 53*X^27 + 57*X^26 + 15*X^25 + 53*X^24 +
      38*X^23 + 2*X^22 + 14*X^21 + 24*X^20 + 42*X^19 + 22*X^18 + 7*X^17 + 12*X^16 + 52*X^15 +
      39*X^14 + 23*X^13 + 51*X^12 + 18*X^11 + 65*X^10 + 62*X^9 + 59*X^8 + 65*X^7 + 53*X^6 + 25*X^5 +
      16*X^4 + 48*X^3 + 62*X^2 + 53*X + 3) :=
  sq_step (by norm_num) pSeventeenB2s266 ⟨
    9*X^32 + 26*X^31 + 43*X^30 + 64*X^29 + 13*X^28 + 49*X^27 + 44*X^26 + 61*X^25 + 48*X^24 + 64*X^23 +
      42*X^22 + 41*X^21 + 30*X^20 + 20*X^19 + 2*X^18 + 30*X^17 + 18*X^16 + 26*X^15 + 34*X^14 +
      47*X^13 + 38*X^12 + 37*X^11 + 19*X^10 + 10*X^9 + 51*X^8 + 65*X^7 + 21*X^6 + 63*X^5 + 50*X^4 +
      50*X^3 + 10*X^2 + 5*X + 58,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s268 : XPow fSeventeenB2 227338723739451312462127392317790949887065303775824880
    (61*X^33 + 31*X^32 + 48*X^31 + 33*X^30 + 41*X^29 + 32*X^28 + 22*X^27 + 62*X^26 + 43*X^25 + 42*X^24 +
      42*X^23 + 22*X^22 + 44*X^21 + 40*X^20 + 22*X^19 + 52*X^18 + 25*X^17 + 48*X^16 + 66*X^15 +
      65*X^14 + 4*X^13 + 2*X^12 + 65*X^11 + 29*X^10 + 39*X^9 + 39*X^8 + 48*X^7 + 58*X^6 + 3*X^5 +
      45*X^4 + 47*X^3 + 18*X^2 + 8*X + 17) :=
  sq_step (by norm_num) pSeventeenB2s267 ⟨
    29*X^32 + 14*X^31 + 62*X^30 + 3*X^29 + 8*X^28 + 42*X^27 + 15*X^26 + 46*X^25 + 36*X^24 + 3*X^23 +
      28*X^22 + 15*X^21 + 31*X^20 + X^19 + 34*X^18 + 63*X^17 + 50*X^16 + 18*X^15 + 52*X^14 + 37*X^13 +
      64*X^12 + 43*X^11 + 23*X^10 + 25*X^9 + X^8 + 46*X^7 + 31*X^6 + 64*X^5 + 5*X^4 + 5*X^3 + 49*X^2 +
      13*X + 53,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s269 : XPow fSeventeenB2 454677447478902624924254784635581899774130607551649760
    (49*X^33 + 4*X^32 + 37*X^31 + 38*X^30 + 22*X^29 + 11*X^28 + 37*X^27 + 50*X^26 + 17*X^25 + 48*X^24 +
      41*X^23 + 64*X^22 + 4*X^21 + 45*X^20 + 28*X^19 + 48*X^17 + 34*X^16 + 23*X^15 + 15*X^14 +
      27*X^13 + 65*X^12 + 8*X^11 + 28*X^10 + 22*X^9 + 16*X^8 + 24*X^7 + 61*X^6 + 64*X^5 + 17*X^4 +
      26*X^3 + 61*X^2 + 47*X + 31) :=
  sq_step (by norm_num) pSeventeenB2s268 ⟨
    36*X^32 + 62*X^31 + 40*X^30 + 23*X^29 + 53*X^28 + 52*X^27 + 10*X^26 + 17*X^25 + 3*X^24 + 8*X^23 +
      52*X^22 + 41*X^21 + 65*X^20 + 2*X^19 + 48*X^18 + 42*X^17 + 42*X^16 + 26*X^15 + 66*X^14 +
      12*X^13 + 34*X^12 + 51*X^11 + 61*X^10 + 34*X^9 + 37*X^8 + 53*X^7 + 49*X^6 + 2*X^5 + 6*X^4 +
      14*X^3 + 35*X^2 + 25*X + 16,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s270 : XPow fSeventeenB2 909354894957805249848509569271163799548261215103299520
    (10*X^33 + 18*X^32 + 63*X^31 + 22*X^30 + 42*X^29 + 5*X^28 + 18*X^27 + 61*X^26 + 39*X^25 + 36*X^24 +
      19*X^23 + 54*X^22 + 29*X^21 + 34*X^20 + 10*X^19 + 11*X^18 + 8*X^17 + 17*X^16 + 15*X^15 +
      20*X^14 + 63*X^13 + 45*X^12 + 31*X^11 + 66*X^10 + 53*X^9 + 8*X^8 + 31*X^7 + 10*X^6 + 47*X^5 +
      21*X^4 + 63*X^3 + 7*X^2 + 36*X + 51) :=
  sq_step (by norm_num) pSeventeenB2s269 ⟨
    56*X^32 + 10*X^31 + 35*X^30 + 11*X^29 + 63*X^28 + 45*X^27 + 18*X^26 + 11*X^25 + 26*X^24 + 36*X^23 +
      48*X^22 + 55*X^21 + 55*X^20 + 6*X^19 + 38*X^18 + 26*X^17 + 49*X^16 + 63*X^15 + 60*X^14 +
      60*X^13 + 55*X^12 + 21*X^11 + 4*X^10 + 35*X^9 + 65*X^8 + 42*X^7 + 8*X^6 + 58*X^5 + 2*X^4 +
      25*X^3 + 35*X^2 + 51*X + 18,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s271 : XPow fSeventeenB2 1818709789915610499697019138542327599096522430206599040
    (8*X^33 + 10*X^32 + 35*X^31 + 39*X^30 + 15*X^29 + 18*X^28 + 60*X^27 + 62*X^26 + 50*X^25 + 10*X^24 +
      6*X^23 + 31*X^22 + 22*X^21 + 55*X^20 + 22*X^19 + 19*X^18 + 23*X^17 + 55*X^16 + 38*X^15 +
      66*X^14 + 34*X^13 + 28*X^12 + 49*X^11 + 45*X^10 + 44*X^9 + 55*X^8 + 48*X^7 + 8*X^6 + 26*X^5 +
      55*X^4 + 47*X^3 + 26*X^2 + 66*X + 40) :=
  sq_step (by norm_num) pSeventeenB2s270 ⟨
    33*X^32 + 32*X^31 + 13*X^30 + 44*X^29 + 11*X^28 + 6*X^27 + 57*X^26 + 4*X^25 + 4*X^24 + 38*X^23 +
      58*X^22 + 33*X^21 + 56*X^20 + 6*X^19 + 9*X^18 + 61*X^17 + 32*X^16 + 66*X^15 + 48*X^14 +
      57*X^13 + 51*X^12 + 28*X^11 + 41*X^10 + 55*X^9 + 7*X^8 + 25*X^7 + 38*X^6 + 33*X^5 + 5*X^4 +
      46*X^3 + 48*X^2 + 38*X + 43,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s272 : XPow fSeventeenB2 3637419579831220999394038277084655198193044860413198080
    (51*X^33 + 31*X^32 + 41*X^31 + 36*X^30 + 44*X^29 + 55*X^28 + 30*X^27 + 64*X^26 + 38*X^25 + 49*X^24 +
      42*X^23 + 55*X^22 + 7*X^21 + 20*X^20 + 43*X^19 + 52*X^18 + 29*X^17 + 5*X^16 + 39*X^15 +
      27*X^14 + 44*X^13 + 43*X^12 + 51*X^11 + 13*X^10 + 41*X^9 + 12*X^8 + 46*X^7 + X^6 + 6*X^5 +
      4*X^4 + 36*X^3 + 30*X^2 + 65*X + 11) :=
  sq_step (by norm_num) pSeventeenB2s271 ⟨
    64*X^32 + X^31 + 5*X^30 + 45*X^29 + 51*X^28 + 66*X^27 + 50*X^26 + 13*X^25 + 33*X^24 + 61*X^23 +
      55*X^22 + 52*X^21 + 31*X^20 + 9*X^19 + 54*X^18 + 33*X^16 + 51*X^15 + 17*X^14 + 4*X^13 +
      24*X^12 + 34*X^11 + 10*X^10 + X^9 + 18*X^8 + 25*X^7 + 31*X^6 + 43*X^5 + 43*X^4 + 23*X^3 +
      43*X^2 + 59*X + 17,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s273 : XPow fSeventeenB2 3637419579831220999394038277084655198193044860413198081
    (54*X^33 + 17*X^32 + 12*X^31 + 52*X^30 + 13*X^29 + 52*X^28 + 23*X^27 + 50*X^26 + 52*X^25 + 14*X^24 +
      45*X^23 + 3*X^22 + 16*X^21 + 27*X^20 + 57*X^19 + 51*X^18 + 34*X^17 + 12*X^16 + 21*X^15 +
      21*X^14 + 11*X^13 + 19*X^12 + 36*X^11 + 45*X^10 + 6*X^9 + 49*X^8 + 53*X^7 + 57*X^6 + 46*X^5 +
      54*X^4 + 60*X^3 + 49*X^2 + 59*X + 57) :=
  mul_step (by norm_num) pSeventeenB2s272 pSeventeenB21 ⟨
    51,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s274 : XPow fSeventeenB2 7274839159662441998788076554169310396386089720826396162
    (15*X^33 + 43*X^32 + 23*X^31 + 55*X^30 + 40*X^29 + 34*X^28 + 22*X^27 + 39*X^26 + 52*X^25 + 59*X^24 +
      46*X^23 + 6*X^22 + 43*X^21 + 48*X^20 + 2*X^19 + 39*X^18 + 38*X^17 + 28*X^16 + 40*X^15 +
      65*X^14 + 32*X^13 + 63*X^12 + 20*X^11 + 44*X^10 + 32*X^9 + 21*X^8 + 34*X^7 + 51*X^6 + 44*X^5 +
      25*X^4 + 14*X^3 + 42*X^2 + 30*X + 11) :=
  sq_step (by norm_num) pSeventeenB2s273 ⟨
    35*X^32 + 6*X^31 + 46*X^30 + 48*X^29 + 58*X^28 + 49*X^27 + 61*X^26 + 55*X^25 + 24*X^24 + 44*X^23 +
      49*X^22 + 62*X^21 + 33*X^20 + 26*X^19 + 47*X^18 + 11*X^17 + 42*X^16 + 41*X^15 + 43*X^14 +
      60*X^13 + 56*X^12 + 7*X^11 + 2*X^10 + 52*X^9 + 61*X^8 + 33*X^7 + 50*X^6 + 32*X^5 + 39*X^4 +
      44*X^3 + 52*X^2 + 17*X + 5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s275 : XPow fSeventeenB2 14549678319324883997576153108338620792772179441652792324
    (36*X^33 + 66*X^32 + 32*X^31 + 16*X^30 + 7*X^29 + 10*X^28 + 56*X^27 + 8*X^26 + 20*X^25 + 36*X^24 +
      10*X^23 + 29*X^22 + 32*X^21 + 54*X^20 + 30*X^18 + 58*X^17 + 58*X^16 + 19*X^15 + 59*X^14 +
      52*X^13 + 13*X^12 + 6*X^11 + 41*X^10 + 22*X^9 + 65*X^8 + 18*X^7 + 28*X^6 + 26*X^5 + 28*X^4 +
      58*X^3 + 22*X^2 + 7*X + 32) :=
  sq_step (by norm_num) pSeventeenB2s274 ⟨
    24*X^32 + 16*X^31 + 6*X^30 + 53*X^29 + 43*X^28 + 66*X^27 + 37*X^26 + 7*X^25 + 23*X^24 + 20*X^23 +
      49*X^22 + 26*X^21 + 49*X^20 + 24*X^19 + 46*X^18 + 15*X^17 + 19*X^16 + 46*X^15 + 23*X^14 +
      60*X^13 + 8*X^12 + 35*X^11 + 60*X^10 + 17*X^9 + 9*X^8 + 34*X^7 + 58*X^6 + 31*X^5 + 21*X^4 +
      15*X^3 + 56*X^2 + 11*X + 5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s276 : XPow fSeventeenB2 29099356638649767995152306216677241585544358883305584648
    (39*X^33 + 8*X^32 + 47*X^31 + 27*X^30 + 53*X^29 + 16*X^28 + 57*X^27 + 3*X^26 + 16*X^25 + 25*X^24 +
      59*X^23 + 50*X^22 + 59*X^21 + 52*X^20 + 18*X^19 + 13*X^17 + X^16 + X^15 + 58*X^14 + 48*X^13 +
      9*X^12 + 44*X^11 + 42*X^10 + 53*X^9 + 11*X^8 + 21*X^7 + 57*X^6 + 5*X^5 + 63*X^4 + 26*X^3 +
      9*X^2 + 51*X + 48) :=
  sq_step (by norm_num) pSeventeenB2s275 ⟨
    23*X^32 + 8*X^31 + 50*X^30 + 66*X^29 + 11*X^28 + 56*X^27 + 17*X^26 + 26*X^25 + 49*X^24 + 60*X^23 +
      38*X^22 + 3*X^21 + 21*X^20 + 4*X^19 + 27*X^18 + 58*X^17 + 60*X^16 + 33*X^15 + 20*X^14 +
      59*X^13 + 57*X^12 + 3*X^11 + 59*X^10 + 62*X^9 + 56*X^8 + 16*X^7 + 58*X^6 + 47*X^5 + 21*X^4 +
      52*X^3 + 13*X^2 + 19*X + 33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s277 : XPow fSeventeenB2 29099356638649767995152306216677241585544358883305584649
    (65*X^33 + 5*X^32 + 52*X^31 + 43*X^29 + 62*X^28 + 15*X^27 + 37*X^26 + 47*X^25 + 10*X^24 + 66*X^23 +
      52*X^22 + 45*X^21 + 57*X^20 + 59*X^19 + 18*X^18 + 35*X^17 + 4*X^16 + 14*X^15 + 58*X^14 +
      20*X^13 + 55*X^12 + 32*X^11 + 60*X^10 + 34*X^9 + 43*X^8 + 14*X^7 + 44*X^6 + 36*X^5 + 24*X^4 +
      28*X^3 + 23*X^2 + 65*X + 16) :=
  mul_step (by norm_num) pSeventeenB2s276 pSeventeenB21 ⟨
    39,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s278 : XPow fSeventeenB2 58198713277299535990304612433354483171088717766611169298
    (59*X^33 + 27*X^32 + 44*X^31 + 11*X^30 + 45*X^29 + 8*X^28 + 56*X^27 + 58*X^26 + 31*X^25 + 33*X^24 +
      43*X^23 + 4*X^22 + 50*X^21 + 39*X^20 + 50*X^19 + 17*X^18 + 38*X^17 + 51*X^16 + 58*X^15 +
      34*X^14 + 50*X^13 + 6*X^12 + 44*X^11 + 42*X^10 + 64*X^9 + 41*X^8 + 52*X^7 + 11*X^6 + 17*X^5 +
      32*X^4 + 36*X^3 + 33*X^2 + 39*X + 64) :=
  sq_step (by norm_num) pSeventeenB2s277 ⟨
    4*X^32 + 58*X^31 + 16*X^30 + 54*X^29 + 9*X^28 + 42*X^27 + 4*X^26 + 51*X^25 + 16*X^24 + 22*X^23 +
      45*X^22 + 13*X^21 + 65*X^20 + 46*X^19 + 3*X^18 + 9*X^17 + 26*X^16 + 6*X^15 + 49*X^14 + 39*X^13 +
      42*X^12 + 44*X^11 + 15*X^10 + 60*X^9 + 22*X^8 + 39*X^7 + 29*X^6 + 20*X^5 + 49*X^4 + 18*X^3 +
      27*X^2 + 49*X + 1,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s279 : XPow fSeventeenB2 116397426554599071980609224866708966342177435533222338596
    (65*X^33 + 54*X^32 + 34*X^31 + X^30 + 50*X^29 + 22*X^28 + 42*X^27 + 6*X^26 + 47*X^25 + 39*X^24 +
      62*X^23 + 34*X^22 + 49*X^21 + 31*X^20 + 38*X^19 + 45*X^18 + 53*X^17 + 27*X^16 + 53*X^15 +
      38*X^14 + 54*X^13 + 33*X^12 + 29*X^11 + 5*X^10 + 6*X^9 + 28*X^8 + 41*X^7 + 20*X^6 + 37*X^5 +
      45*X^4 + 16*X^3 + 3*X^2 + 33*X + 18) :=
  sq_step (by norm_num) pSeventeenB2s278 ⟨
    64*X^32 + 12*X^31 + 20*X^30 + 24*X^29 + 16*X^28 + 58*X^27 + 18*X^26 + 18*X^25 + 6*X^24 + 25*X^23 +
      15*X^22 + 60*X^21 + X^20 + 61*X^19 + 12*X^18 + 37*X^17 + 51*X^16 + 27*X^15 + 58*X^14 + 48*X^13 +
      8*X^12 + 64*X^11 + 3*X^10 + 33*X^9 + 42*X^8 + 10*X^7 + 24*X^5 + 38*X^4 + 9*X^3 + 27*X^2 + 30*X +
      1,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s280 : XPow fSeventeenB2 116397426554599071980609224866708966342177435533222338597
    (15*X^33 + 31*X^32 + 65*X^31 + 51*X^30 + 28*X^28 + 26*X^27 + 15*X^26 + 31*X^25 + 25*X^24 + 16*X^23 +
      15*X^22 + 64*X^21 + 36*X^20 + 54*X^19 + 39*X^18 + 39*X^17 + 58*X^16 + 54*X^15 + 26*X^14 +
      29*X^13 + 25*X^12 + 33*X^11 + 40*X^10 + 44*X^9 + 33*X^8 + 60*X^7 + 35*X^6 + 35*X^4 + 57*X^3 +
      31*X^2 + 24*X + 49) :=
  mul_step (by norm_num) pSeventeenB2s279 pSeventeenB21 ⟨
    65,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s281 : XPow fSeventeenB2 232794853109198143961218449733417932684354871066444677194
    (10*X^33 + 63*X^32 + 53*X^31 + 27*X^30 + 61*X^29 + 20*X^28 + 15*X^27 + 8*X^26 + 12*X^25 + 66*X^24 +
      20*X^23 + 32*X^22 + 32*X^21 + 9*X^20 + 12*X^19 + 15*X^18 + 37*X^17 + 13*X^16 + 10*X^15 +
      12*X^14 + 46*X^13 + 10*X^12 + 22*X^11 + 66*X^10 + 23*X^9 + 31*X^8 + 32*X^7 + 45*X^6 + 62*X^5 +
      21*X^4 + 54*X^3 + 34*X^2 + 47*X) :=
  sq_step (by norm_num) pSeventeenB2s280 ⟨
    24*X^32 + 58*X^31 + 58*X^30 + 47*X^29 + 57*X^28 + 63*X^27 + 9*X^26 + 4*X^25 + 36*X^24 + 51*X^23 +
      59*X^22 + 35*X^21 + 44*X^20 + 60*X^19 + 27*X^18 + 59*X^17 + 58*X^16 + 41*X^15 + 42*X^14 +
      7*X^13 + 31*X^12 + 10*X^11 + 57*X^10 + 2*X^9 + 13*X^8 + 30*X^7 + 37*X^6 + 32*X^5 + 38*X^4 +
      18*X^3 + 33*X^2 + 52*X + 31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s282 : XPow fSeventeenB2 465589706218396287922436899466835865368709742132889354388
    (5*X^33 + 15*X^32 + 56*X^31 + 25*X^30 + 5*X^29 + 19*X^28 + 23*X^27 + 2*X^26 + 28*X^25 + 31*X^23 +
      11*X^22 + 55*X^21 + 7*X^20 + 53*X^19 + 61*X^18 + 27*X^17 + 19*X^16 + 25*X^15 + 40*X^14 +
      56*X^13 + 43*X^12 + 24*X^11 + 5*X^10 + 9*X^9 + 35*X^8 + 43*X^7 + 65*X^6 + 44*X^5 + 59*X^4 +
      5*X^3 + 47*X^2 + X + 57) :=
  sq_step (by norm_num) pSeventeenB2s281 ⟨
    33*X^32 + 61*X^31 + 37*X^30 + 7*X^29 + 60*X^28 + 21*X^27 + 52*X^26 + 55*X^25 + 18*X^23 + 10*X^22 +
      41*X^21 + 65*X^20 + 20*X^19 + 32*X^18 + 6*X^17 + 41*X^16 + 51*X^15 + X^14 + 49*X^13 + 49*X^12 +
      62*X^11 + 38*X^10 + 60*X^9 + 30*X^8 + 39*X^7 + 39*X^6 + 57*X^5 + 42*X^4 + 49*X^3 + 3*X^2 +
      32*X + 51,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s283 : XPow fSeventeenB2 465589706218396287922436899466835865368709742132889354389
    (12*X^33 + 30*X^32 + 66*X^31 + 36*X^30 + 7*X^29 + 58*X^28 + 19*X^27 + 41*X^26 + 20*X^25 + 23*X^24 +
      56*X^23 + 6*X^22 + 25*X^21 + 58*X^20 + 5*X^19 + 62*X^18 + 56*X^17 + 46*X^16 + 59*X^14 +
      53*X^13 + 34*X^12 + 2*X^11 + 58*X^10 + 62*X^9 + 63*X^8 + 32*X^7 + 49*X^6 + 4*X^5 + 58*X^4 +
      46*X^3 + 6*X^2 + 42*X + 45) :=
  mul_step (by norm_num) pSeventeenB2s282 pSeventeenB21 ⟨
    5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s284 : XPow fSeventeenB2 931179412436792575844873798933671730737419484265778708778
    (38*X^33 + 16*X^32 + 62*X^31 + 33*X^30 + 40*X^29 + 64*X^28 + 60*X^27 + 36*X^26 + 2*X^25 + 37*X^24 +
      57*X^23 + 18*X^22 + 22*X^21 + 61*X^20 + 33*X^19 + 64*X^18 + 35*X^16 + 30*X^15 + 18*X^14 +
      31*X^13 + 29*X^12 + 27*X^11 + 11*X^10 + X^9 + 38*X^8 + 17*X^7 + 55*X^6 + 18*X^5 + 64*X^4 +
      3*X^3 + 10*X^2 + 2*X + 58) :=
  sq_step (by norm_num) pSeventeenB2s283 ⟨
    10*X^32 + 44*X^31 + 7*X^30 + 50*X^29 + 59*X^28 + 49*X^27 + 20*X^26 + 41*X^25 + 45*X^24 + 2*X^23 +
      31*X^22 + 19*X^21 + 55*X^20 + 55*X^19 + 2*X^18 + 62*X^17 + 25*X^16 + 31*X^15 + 51*X^14 +
      38*X^13 + 3*X^12 + 8*X^11 + 41*X^10 + 21*X^9 + 20*X^8 + 60*X^7 + 64*X^6 + 15*X^5 + 25*X^4 +
      35*X^3 + 32*X^2 + 26*X + 42,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s285 : XPow fSeventeenB2 1862358824873585151689747597867343461474838968531557417556
    (8*X^33 + 58*X^32 + 53*X^31 + 21*X^30 + 3*X^29 + 58*X^28 + 58*X^27 + 58*X^26 + 54*X^25 + 20*X^24 +
      22*X^23 + 17*X^22 + 58*X^21 + 57*X^20 + 62*X^19 + 40*X^18 + 6*X^17 + 62*X^16 + 6*X^15 +
      14*X^14 + 7*X^13 + 29*X^12 + 56*X^11 + 7*X^10 + 12*X^9 + X^8 + 37*X^7 + 60*X^6 + 65*X^5 +
      37*X^4 + 47*X^3 + 23*X^2 + 63*X + 63) :=
  sq_step (by norm_num) pSeventeenB2s284 ⟨
    37*X^32 + 28*X^31 + 42*X^30 + 15*X^29 + 11*X^28 + 8*X^27 + 65*X^26 + 25*X^25 + 18*X^24 + 18*X^23 +
      42*X^22 + 47*X^21 + 50*X^20 + 51*X^19 + 24*X^18 + 10*X^17 + 64*X^16 + 62*X^15 + 2*X^14 +
      15*X^13 + 31*X^12 + 39*X^11 + 13*X^10 + 59*X^9 + 63*X^8 + 58*X^6 + 53*X^5 + 50*X^4 + 38*X^3 +
      63*X^2 + 55*X + 65,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s286 : XPow fSeventeenB2 1862358824873585151689747597867343461474838968531557417557
    (13*X^33 + 65*X^32 + 33*X^31 + 66*X^30 + 12*X^29 + 47*X^28 + 45*X^27 + 48*X^26 + 52*X^25 + 36*X^24 +
      22*X^23 + 60*X^22 + 59*X^21 + 3*X^20 + 4*X^19 + 62*X^18 + 14*X^17 + 53*X^16 + 17*X^15 +
      52*X^14 + 45*X^13 + 5*X^12 + 29*X^11 + 10*X^10 + 4*X^9 + 2*X^8 + 34*X^7 + 6*X^6 + 16*X^5 +
      38*X^4 + 8*X^3 + 4*X^2 + 39*X + 5) :=
  mul_step (by norm_num) pSeventeenB2s285 pSeventeenB21 ⟨
    8,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s287 : XPow fSeventeenB2 3724717649747170303379495195734686922949677937063114835114
    (45*X^33 + 26*X^32 + 38*X^31 + 33*X^30 + 24*X^29 + 28*X^28 + 50*X^27 + 29*X^26 + 59*X^25 + 2*X^24 +
      47*X^23 + 18*X^22 + 18*X^21 + 61*X^20 + 24*X^19 + 39*X^18 + 52*X^17 + 34*X^16 + 50*X^15 +
      44*X^14 + 47*X^13 + 66*X^12 + 33*X^11 + 62*X^10 + 19*X^9 + 37*X^8 + 24*X^7 + 27*X^6 + 29*X^5 +
      52*X^4 + 37*X^3 + 33*X^2 + 6*X + 6) :=
  sq_step (by norm_num) pSeventeenB2s286 ⟨
    35*X^32 + 61*X^31 + 27*X^30 + 10*X^29 + 6*X^28 + 27*X^27 + 12*X^26 + 8*X^25 + 51*X^24 + 26*X^23 +
      26*X^22 + 59*X^21 + 44*X^20 + 27*X^19 + 2*X^18 + 12*X^17 + 23*X^16 + 25*X^15 + 19*X^14 +
      9*X^13 + 57*X^12 + 35*X^11 + 32*X^10 + 38*X^9 + 16*X^8 + 25*X^7 + 25*X^6 + 61*X^5 + 44*X^4 +
      17*X^2 + 41*X + 50,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s288 : XPow fSeventeenB2 7449435299494340606758990391469373845899355874126229670228
    (16*X^33 + 31*X^32 + 15*X^31 + 37*X^30 + 34*X^29 + 54*X^28 + 8*X^27 + 23*X^26 + 31*X^25 + 16*X^24 +
      7*X^23 + 51*X^22 + 18*X^21 + 64*X^20 + 62*X^19 + 18*X^18 + 54*X^17 + 52*X^16 + 17*X^15 +
      25*X^14 + 24*X^13 + 25*X^12 + X^11 + 54*X^10 + 50*X^9 + 40*X^8 + 53*X^7 + 34*X^6 + 8*X^5 +
      42*X^4 + 38*X^3 + 12*X^2 + 9*X + 46) :=
  sq_step (by norm_num) pSeventeenB2s287 ⟨
    15*X^32 + 53*X^31 + 60*X^30 + 54*X^29 + 36*X^28 + 18*X^27 + 30*X^26 + 57*X^25 + 24*X^24 + 9*X^23 +
      47*X^22 + 11*X^21 + 10*X^20 + 26*X^19 + 12*X^18 + 26*X^17 + 46*X^15 + 38*X^14 + 33*X^13 +
      24*X^12 + 26*X^11 + 50*X^10 + 66*X^9 + 34*X^8 + 58*X^7 + 58*X^6 + 29*X^5 + 42*X^4 + 42*X^3 +
      18*X^2 + 43*X + 16,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s289 : XPow fSeventeenB2 14898870598988681213517980782938747691798711748252459340456
    (35*X^33 + 62*X^32 + 38*X^31 + 7*X^30 + 62*X^29 + 19*X^28 + 36*X^27 + 11*X^26 + 45*X^25 + 61*X^24 +
      43*X^23 + 58*X^22 + 61*X^21 + 46*X^20 + 21*X^19 + 5*X^18 + 8*X^17 + 43*X^16 + 10*X^15 +
      66*X^14 + 21*X^13 + 62*X^12 + 57*X^11 + 46*X^10 + 43*X^9 + 7*X^8 + 52*X^7 + 47*X^6 + 42*X^5 +
      38*X^4 + 27*X^3 + 60*X^2 + 11*X + 35) :=
  sq_step (by norm_num) pSeventeenB2s288 ⟨
    55*X^32 + 21*X^31 + 57*X^30 + 23*X^29 + 58*X^28 + 58*X^27 + 61*X^26 + 43*X^25 + 3*X^24 + 17*X^23 +
      20*X^22 + 62*X^21 + 64*X^20 + 21*X^19 + 9*X^18 + 31*X^17 + 32*X^16 + 12*X^15 + 10*X^14 +
      45*X^13 + 36*X^12 + 3*X^11 + X^10 + 64*X^9 + 4*X^8 + 38*X^7 + 62*X^6 + 18*X^5 + 65*X^4 +
      56*X^3 + 11*X^2 + 53*X + 7,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s290 : XPow fSeventeenB2 29797741197977362427035961565877495383597423496504918680912
    (18*X^33 + 40*X^32 + 33*X^31 + 11*X^30 + 13*X^29 + 46*X^28 + 39*X^27 + 61*X^26 + 22*X^25 + 58*X^24 +
      5*X^23 + 43*X^22 + 26*X^21 + 55*X^20 + 6*X^19 + 12*X^18 + 45*X^17 + 11*X^16 + 32*X^15 + 7*X^14 +
      11*X^13 + 37*X^12 + 8*X^11 + 16*X^10 + 58*X^9 + 33*X^8 + 49*X^7 + 62*X^6 + 15*X^5 + 9*X^4 +
      16*X^3 + X^2 + 27*X + 64) :=
  sq_step (by norm_num) pSeventeenB2s289 ⟨
    19*X^32 + 54*X^31 + 48*X^30 + 50*X^29 + 32*X^28 + 51*X^27 + 34*X^26 + 13*X^25 + 47*X^24 + 25*X^23 +
      49*X^22 + 49*X^21 + 4*X^20 + 34*X^19 + 27*X^18 + 65*X^17 + 7*X^16 + 45*X^15 + 18*X^14 + 5*X^13 +
      19*X^12 + 19*X^11 + 45*X^10 + 21*X^9 + 12*X^8 + 19*X^7 + 30*X^6 + X^5 + 24*X^4 + 26*X^3 +
      26*X^2 + X + 5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s291 : XPow fSeventeenB2 29797741197977362427035961565877495383597423496504918680913
    (56*X^33 + 60*X^32 + 38*X^31 + 4*X^30 + 43*X^29 + 31*X^28 + 15*X^27 + 42*X^26 + 63*X^25 + 3*X^24 +
      4*X^23 + 64*X^22 + 26*X^21 + 24*X^20 + 65*X^19 + 37*X^18 + 37*X^17 + 54*X^16 + 64*X^15 +
      62*X^14 + 6*X^13 + 44*X^12 + 32*X^11 + 20*X^10 + 23*X^9 + 54*X^8 + 37*X^7 + 33*X^6 + 12*X^5 +
      46*X^4 + 51*X^3 + 45*X^2 + 10*X + 28) :=
  mul_step (by norm_num) pSeventeenB2s290 pSeventeenB21 ⟨
    18,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s292 : XPow fSeventeenB2 59595482395954724854071923131754990767194846993009837361826
    (35*X^33 + 32*X^32 + 7*X^31 + 60*X^30 + 63*X^29 + 50*X^28 + 26*X^27 + 39*X^26 + 43*X^25 + 37*X^24 +
      26*X^23 + 23*X^22 + 47*X^21 + 14*X^19 + 26*X^18 + 3*X^17 + 52*X^16 + 20*X^15 + 17*X^14 +
      30*X^13 + 26*X^12 + 16*X^11 + 15*X^10 + 32*X^9 + 25*X^8 + 57*X^7 + X^6 + 18*X^5 + 6*X^4 +
      43*X^3 + 17*X^2 + 57*X + 64) :=
  sq_step (by norm_num) pSeventeenB2s291 ⟨
    54*X^32 + X^31 + 17*X^30 + 62*X^29 + 43*X^28 + X^27 + 29*X^26 + 45*X^25 + 46*X^23 + 50*X^22 +
      61*X^21 + 50*X^20 + 30*X^19 + 31*X^18 + 41*X^17 + 47*X^16 + 44*X^15 + 57*X^14 + 57*X^13 +
      15*X^12 + 19*X^11 + 40*X^10 + 16*X^9 + 50*X^8 + 38*X^7 + 54*X^6 + 5*X^5 + 11*X^4 + 58*X^3 +
      47*X^2 + 44*X + 54,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s293 : XPow fSeventeenB2 59595482395954724854071923131754990767194846993009837361827
    (11*X^33 + 26*X^32 + 12*X^31 + 12*X^30 + 33*X^29 + 3*X^28 + 24*X^27 + 43*X^25 + 37*X^24 + 3*X^23 +
      39*X^22 + 59*X^21 + 49*X^20 + 36*X^19 + 47*X^18 + 43*X^17 + 33*X^16 + 5*X^15 + 51*X^14 +
      29*X^13 + 19*X^12 + 61*X^11 + 40*X^10 + 13*X^9 + 63*X^8 + 38*X^7 + 53*X^6 + 23*X^5 + 12*X^4 +
      10*X^3 + 25*X^2 + 26*X + 47) :=
  mul_step (by norm_num) pSeventeenB2s292 pSeventeenB21 ⟨
    35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s294 : XPow fSeventeenB2 119190964791909449708143846263509981534389693986019674723654
    (16*X^33 + 9*X^32 + 14*X^31 + 17*X^30 + 4*X^29 + 6*X^28 + 5*X^27 + 14*X^26 + 7*X^25 + 34*X^24 +
      11*X^23 + 27*X^22 + 43*X^21 + 8*X^19 + 18*X^18 + 44*X^17 + 47*X^16 + 51*X^15 + 59*X^14 +
      35*X^13 + 23*X^12 + 9*X^11 + 46*X^10 + 33*X^9 + 63*X^8 + 14*X^7 + 44*X^6 + X^5 + 5*X^4 +
      20*X^3 + 3*X^2 + 44*X + 45) :=
  sq_step (by norm_num) pSeventeenB2s293 ⟨
    54*X^32 + 17*X^31 + 46*X^30 + 49*X^29 + 38*X^28 + 55*X^27 + 15*X^26 + 25*X^25 + 21*X^24 + 30*X^23 +
      42*X^22 + 37*X^21 + 20*X^20 + 36*X^19 + 6*X^18 + 51*X^17 + 55*X^16 + 56*X^15 + 19*X^14 +
      2*X^13 + 62*X^12 + 6*X^11 + 59*X^10 + 58*X^9 + 63*X^8 + 18*X^7 + 19*X^6 + 63*X^5 + 43*X^4 +
      23*X^3 + 7*X^2 + 13*X + 35,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s295 : XPow fSeventeenB2 119190964791909449708143846263509981534389693986019674723655
    (53*X^33 + 38*X^32 + 41*X^31 + 63*X^30 + 48*X^29 + 50*X^28 + 55*X^27 + 62*X^26 + 31*X^25 + 39*X^24 +
      37*X^23 + 47*X^22 + 4*X^21 + 24*X^20 + 13*X^19 + 22*X^18 + 18*X^17 + 11*X^16 + 65*X^15 +
      58*X^14 + 55*X^13 + 41*X^12 + 23*X^11 + 29*X^10 + 2*X^9 + 11*X^8 + 59*X^7 + 17*X^6 + 30*X^5 +
      2*X^4 + 40*X^3 + 60*X^2 + 64*X + 10) :=
  mul_step (by norm_num) pSeventeenB2s294 pSeventeenB21 ⟨
    16,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s296 : XPow fSeventeenB2 238381929583818899416287692527019963068779387972039349447310
    (38*X^33 + 34*X^32 + 9*X^31 + 15*X^30 + 32*X^29 + 4*X^28 + 45*X^27 + 16*X^26 + 38*X^25 + 65*X^24 +
      39*X^23 + 25*X^22 + 8*X^21 + 55*X^20 + 22*X^19 + 19*X^18 + 54*X^17 + 52*X^16 + 8*X^15 +
      49*X^14 + 36*X^13 + 4*X^12 + 43*X^11 + 10*X^10 + 51*X^9 + 9*X^8 + 62*X^7 + 58*X^6 + 60*X^5 +
      5*X^4 + 32*X^3 + 5*X^2 + 66*X + 47) :=
  sq_step (by norm_num) pSeventeenB2s295 ⟨
    62*X^32 + 11*X^31 + 34*X^30 + 14*X^29 + 41*X^28 + 51*X^27 + 55*X^26 + 59*X^25 + 24*X^24 + 62*X^23 +
      26*X^22 + 21*X^21 + 55*X^20 + 42*X^19 + 27*X^18 + 40*X^17 + 54*X^16 + 21*X^15 + 31*X^14 +
      38*X^13 + 32*X^12 + 41*X^11 + 20*X^10 + 15*X^9 + 5*X^8 + 33*X^7 + 61*X^6 + 4*X^5 + 50*X^4 +
      36*X^3 + 57*X^2 + 17*X + 9,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s297 : XPow fSeventeenB2 476763859167637798832575385054039926137558775944078698894620
    (40*X^33 + 12*X^32 + 49*X^31 + 40*X^30 + 50*X^29 + 31*X^28 + 10*X^27 + 26*X^26 + 33*X^25 + 26*X^24 +
      48*X^23 + 25*X^22 + 5*X^21 + 16*X^20 + 31*X^19 + 25*X^18 + 6*X^17 + 3*X^16 + 21*X^15 + 30*X^14 +
      51*X^13 + 3*X^12 + 62*X^11 + 14*X^10 + 10*X^9 + 50*X^8 + 5*X^7 + X^6 + 55*X^5 + 45*X^4 +
      38*X^3 + 18*X^2 + 48*X + 27) :=
  sq_step (by norm_num) pSeventeenB2s296 ⟨
    37*X^32 + 56*X^31 + 6*X^30 + 32*X^29 + 44*X^28 + 24*X^27 + 51*X^26 + 11*X^25 + 28*X^24 + 12*X^23 +
      3*X^22 + 34*X^21 + 35*X^20 + 31*X^19 + 43*X^18 + 50*X^17 + 58*X^16 + 37*X^15 + 59*X^14 +
      11*X^13 + 25*X^12 + X^11 + 9*X^10 + 2*X^9 + 33*X^8 + 32*X^7 + 31*X^6 + 20*X^5 + 64*X^4 +
      35*X^3 + 12*X^2 + 64*X + 33,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s298 : XPow fSeventeenB2 953527718335275597665150770108079852275117551888157397789240
    (8*X^33 + 50*X^32 + 18*X^31 + 49*X^30 + 32*X^29 + 38*X^28 + 20*X^27 + 10*X^26 + 29*X^25 + 13*X^24 +
      48*X^23 + 7*X^22 + 51*X^21 + 4*X^20 + 56*X^19 + 52*X^18 + 37*X^17 + 22*X^16 + 23*X^15 +
      17*X^14 + 34*X^13 + 47*X^12 + 56*X^11 + 53*X^10 + 50*X^9 + 5*X^8 + 60*X^7 + 33*X^6 + 24*X^5 +
      24*X^4 + 11*X^3 + 12*X^2 + 47*X + 13) :=
  sq_step (by norm_num) pSeventeenB2s297 ⟨
    59*X^32 + 32*X^30 + 30*X^29 + 25*X^28 + 19*X^27 + 50*X^26 + 29*X^25 + 22*X^24 + 8*X^23 + 33*X^22 +
      4*X^21 + 8*X^20 + 16*X^19 + 35*X^18 + 59*X^17 + 2*X^16 + 10*X^15 + 56*X^14 + 50*X^13 + 13*X^12 +
      51*X^11 + 31*X^10 + 53*X^9 + 31*X^8 + 55*X^7 + 18*X^6 + 65*X^5 + 27*X^4 + 14*X^3 + 22*X^2 +
      53*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s299 : XPow fSeventeenB2 1907055436670551195330301540216159704550235103776314795578480
    (33*X^33 + 20*X^32 + 4*X^31 + 41*X^30 + 35*X^29 + 7*X^28 + 4*X^27 + X^26 + 25*X^25 + 46*X^24 +
      32*X^23 + 18*X^22 + 24*X^21 + 29*X^20 + 40*X^19 + 63*X^18 + 60*X^17 + 16*X^16 + 48*X^15 +
      21*X^14 + 26*X^13 + 46*X^12 + 18*X^11 + 25*X^10 + 64*X^9 + 3*X^8 + 25*X^7 + 39*X^6 + 26*X^5 +
      61*X^4 + 32*X^3 + 39*X^2 + 49*X + 29) :=
  sq_step (by norm_num) pSeventeenB2s298 ⟨
    64*X^32 + 38*X^31 + 7*X^30 + 26*X^29 + 14*X^28 + 47*X^27 + 65*X^26 + 8*X^25 + 54*X^24 + 12*X^23 +
      36*X^22 + 4*X^21 + 3*X^20 + 38*X^19 + 21*X^18 + 13*X^17 + 58*X^16 + 55*X^15 + 62*X^14 +
      17*X^13 + 53*X^12 + 47*X^11 + 35*X^10 + 59*X^9 + 25*X^8 + 55*X^7 + 21*X^6 + 28*X^5 + 30*X^4 +
      4*X^3 + 53*X^2 + 63*X + 44,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s300 : XPow fSeventeenB2 3814110873341102390660603080432319409100470207552629591156960
    (28*X^33 + 41*X^32 + 4*X^31 + 47*X^30 + 38*X^29 + 43*X^28 + 3*X^27 + 26*X^26 + 52*X^25 + 22*X^24 +
      19*X^23 + 42*X^22 + 49*X^21 + 62*X^20 + 61*X^19 + 7*X^18 + 18*X^17 + 22*X^16 + 39*X^15 +
      9*X^14 + 52*X^13 + 49*X^12 + 26*X^11 + 16*X^10 + 55*X^9 + 8*X^8 + 57*X^7 + 20*X^6 + 30*X^5 +
      14*X^4 + 7*X^3 + 8*X^2 + 6*X + 62) :=
  sq_step (by norm_num) pSeventeenB2s299 ⟨
    17*X^32 + 10*X^31 + 47*X^30 + 4*X^29 + 34*X^28 + 63*X^27 + 43*X^26 + 62*X^25 + 57*X^24 + 62*X^23 +
      54*X^22 + 40*X^21 + 10*X^20 + 62*X^19 + 65*X^18 + 24*X^17 + 10*X^16 + 10*X^15 + 63*X^14 +
      56*X^13 + 8*X^12 + 35*X^11 + 29*X^10 + 29*X^8 + 60*X^7 + 27*X^6 + 22*X^5 + X^4 + 53*X^3 +
      13*X^2 + 63*X + 40,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s301 : XPow fSeventeenB2 7628221746682204781321206160864638818200940415105259182313920
    (16*X^33 + 37*X^32 + 30*X^31 + 51*X^30 + 43*X^29 + 6*X^28 + 44*X^27 + 55*X^26 + 14*X^25 + 59*X^24 +
      62*X^23 + 38*X^22 + 37*X^21 + 60*X^20 + 48*X^19 + 20*X^18 + 66*X^17 + 44*X^16 + 32*X^15 +
      27*X^14 + 47*X^13 + 26*X^12 + 50*X^11 + 49*X^10 + 20*X^9 + 47*X^8 + 49*X^7 + 56*X^6 + 35*X^5 +
      32*X^4 + 57*X^3 + 24*X^2 + 10*X + 56) :=
  sq_step (by norm_num) pSeventeenB2s300 ⟨
    47*X^32 + 30*X^31 + 48*X^30 + 25*X^29 + 13*X^28 + 65*X^27 + 26*X^26 + 32*X^25 + 43*X^24 + 34*X^22 +
      64*X^21 + 42*X^20 + 8*X^19 + 25*X^18 + 20*X^17 + 44*X^16 + 16*X^15 + 33*X^14 + 39*X^13 +
      13*X^12 + 30*X^11 + 66*X^10 + 27*X^8 + 53*X^7 + 42*X^6 + 59*X^5 + 10*X^4 + 9*X^3 + 30*X^2 +
      66*X + 63,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s302 : XPow fSeventeenB2 15256443493364409562642412321729277636401880830210518364627840
    (4*X^33 + 6*X^32 + 28*X^31 + 59*X^30 + 51*X^29 + 17*X^28 + 20*X^27 + 52*X^26 + 33*X^25 + 52*X^24 +
      66*X^23 + 10*X^22 + 33*X^21 + 26*X^20 + X^19 + 19*X^18 + 47*X^17 + 17*X^16 + 45*X^15 + 11*X^14 +
      52*X^13 + 66*X^12 + 25*X^11 + 44*X^10 + 45*X^9 + 65*X^8 + 53*X^7 + 66*X^6 + 63*X^5 + 38*X^4 +
      42*X^3 + 45*X^2 + 49*X) :=
  sq_step (by norm_num) pSeventeenB2s301 ⟨
    55*X^32 + 12*X^31 + 66*X^30 + 47*X^29 + 21*X^28 + 41*X^27 + 10*X^26 + 2*X^25 + 6*X^24 + 30*X^23 +
      65*X^22 + 8*X^21 + 32*X^20 + 49*X^19 + 57*X^18 + 41*X^17 + 44*X^16 + 11*X^15 + 8*X^14 +
      39*X^13 + 30*X^12 + 22*X^11 + 32*X^10 + X^9 + 22*X^8 + 2*X^7 + 25*X^6 + 24*X^5 + 40*X^4 +
      11*X^3 + 65*X^2 + 13*X + 61,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s303 : XPow fSeventeenB2 15256443493364409562642412321729277636401880830210518364627841
    (17*X^33 + 34*X^32 + 65*X^31 + 49*X^30 + 61*X^29 + 48*X^28 + 12*X^27 + 30*X^26 + X^25 + 6*X^24 +
      46*X^23 + 34*X^22 + 27*X^21 + 5*X^20 + X^19 + 8*X^18 + 60*X^17 + 35*X^16 + 46*X^15 + 41*X^14 +
      7*X^13 + 33*X^12 + 55*X^11 + 44*X^10 + 33*X^9 + 2*X^8 + 53*X^7 + 61*X^5 + 4*X^4 + 4*X^3 +
      53*X^2 + 55*X + 36) :=
  mul_step (by norm_num) pSeventeenB2s302 pSeventeenB21 ⟨
    4,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s304 : XPow fSeventeenB2 30512886986728819125284824643458555272803761660421036729255682
    (5*X^33 + 10*X^32 + 27*X^31 + 42*X^30 + 14*X^29 + 22*X^28 + 39*X^27 + 64*X^26 + 20*X^25 + 53*X^24 +
      49*X^23 + 10*X^22 + 4*X^21 + 33*X^20 + 20*X^19 + 26*X^18 + 61*X^17 + 30*X^16 + 49*X^15 +
      16*X^14 + 6*X^13 + 57*X^12 + 28*X^11 + 9*X^10 + 57*X^9 + 40*X^8 + 55*X^7 + 14*X^5 + 13*X^4 +
      13*X^3 + 55*X^2 + 28*X + 51) :=
  sq_step (by norm_num) pSeventeenB2s303 ⟨
    21*X^32 + 58*X^31 + 6*X^30 + 57*X^29 + 41*X^28 + 47*X^27 + 3*X^26 + 6*X^25 + 26*X^24 + 36*X^23 +
      57*X^22 + 26*X^21 + 27*X^20 + 64*X^19 + 35*X^18 + 63*X^17 + 49*X^16 + 18*X^15 + 20*X^14 +
      11*X^13 + 52*X^12 + 61*X^11 + 37*X^10 + 29*X^9 + 18*X^8 + 47*X^7 + 25*X^6 + 61*X^5 + 28*X^4 +
      17*X^3 + 21*X^2 + 53*X + 18,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s305 : XPow fSeventeenB2 61025773973457638250569649286917110545607523320842073458511364
    (66) :=
  sq_step (by norm_num) pSeventeenB2s304 ⟨
    25*X^32 + 18*X^31 + 55*X^30 + 20*X^29 + 52*X^28 + 40*X^27 + 61*X^26 + 55*X^25 + 15*X^24 + 62*X^23 +
      20*X^22 + 15*X^21 + 13*X^20 + 6*X^19 + 64*X^18 + 8*X^17 + 36*X^16 + 31*X^15 + 27*X^14 +
      45*X^13 + 30*X^12 + 12*X^11 + 60*X^10 + 9*X^9 + 31*X^8 + 40*X^7 + 17*X^6 + 12*X^5 + 11*X^4 +
      33*X^3 + 25*X^2 + 28*X + 31,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s306 : XPow fSeventeenB2 122051547946915276501139298573834221091215046641684146917022728
    (1) :=
  sq_step (by norm_num) pSeventeenB2s305 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2s307 : XPow fSeventeenB2 122051547946915276501139298573834221091215046641684146917022729
    (X) :=
  mul_step (by norm_num) pSeventeenB2s306 pSeventeenB21 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! Factor 2 again, at the smaller exponent `67 ^ 2`, for the coprimality below. -/

theorem pSeventeenB2cs0 : XPow fSeventeenB2 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenB21 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs1 : XPow fSeventeenB2 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenB2cs0 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs2 : XPow fSeventeenB2 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenB2cs1 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs3 : XPow fSeventeenB2 16
    (X^16) :=
  sq_step (by norm_num) pSeventeenB2cs2 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs4 : XPow fSeventeenB2 17
    (X^17) :=
  mul_step (by norm_num) pSeventeenB2cs3 pSeventeenB21 ⟨
    0,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs5 : XPow fSeventeenB2 34
    (53*X^33 + 35*X^32 + 35*X^31 + 33*X^30 + 11*X^29 + 7*X^28 + 57*X^27 + 16*X^26 + 4*X^25 + 52*X^24 +
      9*X^23 + 17*X^22 + 17*X^21 + X^20 + 29*X^19 + 7*X^18 + 61*X^17 + 31*X^16 + 59*X^15 + 14*X^14 +
      2*X^13 + 2*X^12 + 53*X^11 + 50*X^10 + 59*X^9 + 4*X^8 + 47*X^7 + X^6 + 56*X^5 + 24*X^4 + 40*X^3 +
      X^2 + 64*X + 9) :=
  sq_step (by norm_num) pSeventeenB2cs4 ⟨
    1,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs6 : XPow fSeventeenB2 35
    (30*X^33 + 14*X^32 + 12*X^31 + 18*X^30 + 54*X^29 + 26*X^28 + 22*X^27 + 48*X^26 + 63*X^25 + 18*X^24 +
      25*X^23 + 47*X^22 + 31*X^21 + 15*X^20 + 3*X^19 + 30*X^18 + 48*X^17 + 27*X^16 + 59*X^15 +
      7*X^14 + 41*X^13 + 25*X^12 + 45*X^11 + 29*X^10 + 49*X^9 + 58*X^8 + 13*X^7 + 42*X^6 + 44*X^5 +
      39*X^4 + 44*X^3 + 50*X^2 + 51*X + 8) :=
  mul_step (by norm_num) pSeventeenB2cs5 pSeventeenB21 ⟨
    53,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs7 : XPow fSeventeenB2 70
    (50*X^33 + 44*X^32 + 7*X^31 + 53*X^30 + 65*X^29 + 30*X^28 + 42*X^27 + 21*X^26 + 51*X^25 + 29*X^24 +
      55*X^23 + 65*X^22 + 25*X^21 + 18*X^20 + 62*X^19 + 4*X^18 + 33*X^17 + 65*X^15 + 22*X^14 +
      63*X^13 + 59*X^12 + 3*X^11 + 5*X^10 + 4*X^9 + 52*X^8 + 65*X^7 + 66*X^6 + 30*X^5 + 42*X^4 +
      34*X^3 + 60*X^2 + 25*X + 35) :=
  sq_step (by norm_num) pSeventeenB2cs6 ⟨
    29*X^32 + 32*X^31 + 9*X^30 + 8*X^29 + 4*X^28 + 58*X^27 + 41*X^26 + 51*X^25 + 19*X^24 + 37*X^23 +
      11*X^22 + 49*X^21 + 22*X^20 + 25*X^19 + 23*X^18 + 43*X^17 + 27*X^16 + 11*X^15 + 48*X^14 +
      14*X^13 + 32*X^12 + 30*X^11 + 3*X^10 + 38*X^9 + 29*X^8 + 65*X^7 + 65*X^6 + 31*X^5 + 64*X^4 +
      58*X^3 + 66*X^2 + 50*X + 34,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs8 : XPow fSeventeenB2 140
    (8*X^33 + 52*X^32 + 60*X^31 + 42*X^30 + 36*X^29 + 17*X^28 + 10*X^27 + 20*X^26 + 39*X^25 + 37*X^24 +
      31*X^23 + 22*X^22 + 40*X^21 + 48*X^20 + 15*X^19 + 19*X^18 + 11*X^17 + 57*X^16 + 2*X^15 +
      17*X^14 + 59*X^13 + 16*X^12 + 3*X^11 + 7*X^10 + 47*X^9 + 39*X^8 + 40*X^7 + 21*X^6 + 19*X^5 +
      60*X^4 + 16*X^3 + 27*X^2 + 15*X + 64) :=
  sq_step (by norm_num) pSeventeenB2cs7 ⟨
    21*X^32 + 19*X^31 + 23*X^30 + 26*X^29 + 14*X^28 + 47*X^27 + 21*X^26 + 35*X^25 + 64*X^24 + 48*X^23 +
      16*X^22 + 12*X^21 + 10*X^20 + 17*X^19 + 51*X^18 + 43*X^17 + 30*X^16 + 41*X^15 + 64*X^14 +
      43*X^13 + 50*X^12 + 38*X^11 + 60*X^10 + 17*X^9 + 35*X^8 + 9*X^7 + 33*X^6 + 36*X^5 + 48*X^4 +
      60*X^3 + 23*X^2 + 62*X + 5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs9 : XPow fSeventeenB2 280
    (13*X^33 + 22*X^32 + 2*X^31 + 61*X^30 + 22*X^29 + 45*X^28 + 36*X^27 + 33*X^26 + 65*X^25 + 11*X^24 +
      19*X^23 + 24*X^22 + 21*X^21 + 65*X^20 + 42*X^19 + 3*X^18 + 21*X^17 + 54*X^16 + 18*X^15 +
      62*X^14 + 25*X^13 + 66*X^12 + 39*X^11 + 45*X^10 + 61*X^9 + 45*X^8 + 61*X^7 + 13*X^6 + 39*X^5 +
      38*X^4 + 43*X^3 + 17*X^2 + 10*X + 50) :=
  sq_step (by norm_num) pSeventeenB2cs8 ⟨
    64*X^32 + 3*X^31 + 33*X^30 + 18*X^29 + 6*X^28 + 36*X^27 + 2*X^26 + 30*X^25 + 47*X^24 + 7*X^23 +
      10*X^22 + 26*X^21 + 19*X^20 + 36*X^19 + 20*X^18 + 5*X^17 + 11*X^16 + 14*X^15 + 32*X^14 +
      44*X^13 + 24*X^12 + 39*X^11 + 31*X^10 + 13*X^9 + 3*X^8 + 60*X^7 + 56*X^6 + 20*X^5 + 11*X^4 +
      66*X^3 + 11*X^2 + 30*X + 12,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs10 : XPow fSeventeenB2 560
    (58*X^33 + 26*X^32 + 61*X^31 + 20*X^30 + 23*X^29 + 16*X^28 + 2*X^27 + 30*X^26 + 25*X^25 + 38*X^24 +
      56*X^23 + 22*X^22 + 46*X^20 + 42*X^19 + 36*X^18 + 10*X^17 + 29*X^16 + 22*X^15 + 9*X^14 +
      17*X^13 + 38*X^12 + 44*X^11 + 6*X^10 + 49*X^9 + 66*X^8 + 47*X^7 + 41*X^6 + 26*X^5 + 57*X^4 +
      64*X^3 + 41*X^2 + 20*X + 65) :=
  sq_step (by norm_num) pSeventeenB2cs9 ⟨
    35*X^32 + 15*X^31 + 10*X^30 + X^29 + 50*X^28 + 66*X^27 + 18*X^26 + 34*X^25 + 63*X^24 + 2*X^23 +
      61*X^22 + 24*X^21 + 42*X^20 + 28*X^19 + 57*X^18 + 40*X^17 + 15*X^16 + 2*X^15 + 18*X^14 +
      6*X^13 + 37*X^12 + 44*X^10 + 2*X^9 + 18*X^8 + 66*X^7 + 33*X^6 + 12*X^5 + 7*X^4 + 37*X^3 +
      4*X^2 + 59*X + 57,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs11 : XPow fSeventeenB2 561
    (18*X^33 + 14*X^32 + 40*X^31 + 61*X^30 + 51*X^29 + 6*X^28 + 53*X^27 + 15*X^26 + 2*X^25 + 57*X^24 +
      8*X^23 + 48*X^22 + 27*X^21 + 33*X^20 + 43*X^19 + 14*X^18 + 16*X^17 + 11*X^16 + 14*X^15 +
      25*X^14 + 20*X^13 + 26*X^12 + 65*X^11 + X^10 + 4*X^9 + 11*X^8 + 20*X^7 + 17*X^6 + 22*X^5 +
      49*X^4 + 16*X^3 + 11*X^2 + 25*X + 53) :=
  mul_step (by norm_num) pSeventeenB2cs10 pSeventeenB21 ⟨
    58,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs12 : XPow fSeventeenB2 1122
    (42*X^33 + 39*X^32 + 65*X^31 + 65*X^30 + 30*X^29 + 41*X^28 + 54*X^27 + 21*X^26 + 37*X^25 + 62*X^24 +
      11*X^23 + 55*X^22 + 18*X^21 + 38*X^19 + 38*X^18 + 32*X^17 + 60*X^16 + 41*X^15 + 35*X^14 +
      28*X^13 + 16*X^12 + 18*X^11 + 17*X^10 + 63*X^9 + 29*X^8 + 62*X^7 + 9*X^6 + 37*X^5 + 52*X^4 +
      44*X^3 + 43*X^2 + 18*X + 40) :=
  sq_step (by norm_num) pSeventeenB2cs11 ⟨
    56*X^32 + 55*X^31 + 12*X^30 + 65*X^29 + 52*X^28 + X^27 + 8*X^26 + 42*X^25 + 43*X^23 + 30*X^22 +
      10*X^21 + 27*X^20 + 64*X^19 + 58*X^18 + 18*X^17 + 55*X^16 + 42*X^15 + 56*X^14 + 40*X^13 +
      57*X^12 + 12*X^11 + 57*X^10 + 49*X^9 + 21*X^8 + 30*X^7 + 27*X^6 + 53*X^5 + 19*X^4 + 28*X^3 +
      16*X^2 + 7*X + 5,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs13 : XPow fSeventeenB2 2244
    (50*X^33 + 25*X^32 + 54*X^31 + 12*X^30 + 37*X^29 + 38*X^28 + 55*X^27 + 15*X^26 + 29*X^25 + 10*X^24 +
      40*X^23 + 21*X^22 + 60*X^21 + 31*X^20 + 12*X^19 + 59*X^18 + 17*X^17 + 46*X^16 + 50*X^15 +
      43*X^14 + 42*X^13 + 64*X^12 + 36*X^11 + 16*X^10 + 23*X^9 + 58*X^8 + 30*X^7 + 45*X^6 + 37*X^5 +
      30*X^4 + 47*X^3 + 50*X^2 + 53*X + 56) :=
  sq_step (by norm_num) pSeventeenB2cs12 ⟨
    22*X^32 + 20*X^31 + 34*X^30 + 26*X^28 + 16*X^27 + 18*X^26 + 35*X^25 + 45*X^24 + 33*X^23 + 30*X^22 +
      48*X^21 + 50*X^20 + 12*X^19 + 4*X^18 + 20*X^17 + 31*X^16 + 24*X^15 + 31*X^14 + 2*X^13 +
      59*X^12 + 9*X^11 + 2*X^10 + X^9 + 34*X^8 + 47*X^7 + 15*X^6 + 41*X^5 + 47*X^4 + 5*X^3 + 17*X +
      22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs14 : XPow fSeventeenB2 4488
    (22*X^33 + 47*X^32 + 13*X^31 + 32*X^30 + 3*X^29 + 2*X^28 + 62*X^27 + 57*X^26 + 26*X^25 + 17*X^24 +
      47*X^23 + 42*X^22 + 9*X^21 + 44*X^20 + 44*X^19 + 23*X^18 + 42*X^17 + 36*X^16 + 56*X^15 + X^14 +
      39*X^13 + 9*X^12 + 37*X^11 + 66*X^10 + 54*X^9 + 16*X^8 + 32*X^7 + 61*X^6 + 64*X^5 + 51*X^4 +
      30*X^3 + 42*X^2 + 50*X + 8) :=
  sq_step (by norm_num) pSeventeenB2cs13 ⟨
    21*X^32 + 62*X^31 + 63*X^30 + 27*X^29 + 47*X^28 + 57*X^27 + 26*X^26 + 55*X^25 + 65*X^24 + 28*X^23 +
      34*X^22 + 39*X^21 + 24*X^20 + 9*X^19 + 32*X^18 + 7*X^17 + 39*X^16 + 6*X^15 + 31*X^14 + 26*X^13 +
      55*X^12 + 15*X^11 + 66*X^10 + 6*X^9 + 24*X^8 + 37*X^7 + 18*X^6 + 16*X^5 + 36*X^4 + 56*X^3 +
      36*X^2 + 54*X + 47,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenB2cs15 : XPow fSeventeenB2 4489
    (7*X^33 + 46*X^32 + 65*X^31 + 59*X^30 + 43*X^29 + 15*X^28 + 38*X^27 + 43*X^26 + 38*X^25 + 52*X^24 +
      39*X^23 + 48*X^22 + 16*X^21 + 66*X^20 + 58*X^19 + 62*X^18 + 38*X^17 + X^16 + 26*X^15 + 12*X^14 +
      53*X^13 + 14*X^12 + 26*X^11 + 15*X^10 + 41*X^9 + 53*X^8 + 23*X^7 + 19*X^6 + 10*X^5 + 22*X^4 +
      51*X^3 + 5*X^2 + 9*X + 64) :=
  mul_step (by norm_num) pSeventeenB2cs14 pSeventeenB21 ⟨
    22,
    by simp only [fSeventeenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

end Fermat.MazurNonCMCertificate

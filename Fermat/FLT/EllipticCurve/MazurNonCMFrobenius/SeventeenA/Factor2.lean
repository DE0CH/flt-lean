/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius

/-!
# Row `p = 17`, `j = −882216989/131072`: factor 2 of `H`, and its two square-and-multiply chains

Generated.  This module holds ONE of the 4 pairwise-coprime degree-`34` factors of `H` and
the two chains run modulo it: `X ^ (67 ^ 34)` for the divisibility, and `X ^ (67 ^ 2)` for
the coprimality.  Both chains start from the same `XPow f 1 X`, so they cannot be separated
from each other; nothing else in the row refers to anything here except the final step of each
chain and the factor's own definition.

It is a separate module because elaboration is single-threaded per module — see
`SeventeenA.lean` for the measurement.  Every identity handed to `ring_nf` has degree `< 2 · 34`
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
noncomputable def fSeventeenA2 : (ZMod 67)[X] :=
  X^34 + 23*X^33 + 41*X^32 + 27*X^31 + 4*X^30 + 24*X^29 + 44*X^28 + X^27 + 62*X^26 + 37*X^25 + 14*X^24 +
    25*X^23 + 59*X^22 + 65*X^21 + 25*X^20 + 25*X^19 + 56*X^18 + 41*X^17 + 41*X^16 + 61*X^15 +
    42*X^14 + 25*X^13 + 66*X^12 + 27*X^11 + 63*X^10 + 46*X^9 + X^8 + 34*X^7 + 5*X^6 + 12*X^5 +
    27*X^4 + 14*X^3 + 29*X^2 + 12*X + 56

/-! ### Factor 2: `X ^ (67 ^ 34)` mod `f` by square-and-multiply -/

theorem pSeventeenA21 : XPow fSeventeenA2 1 X := xpow_one _

theorem pSeventeenA2s0 : XPow fSeventeenA2 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenA21 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s1 : XPow fSeventeenA2 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenA2s0 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s2 : XPow fSeventeenA2 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenA2s1 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s3 : XPow fSeventeenA2 9
    (X^9) :=
  mul_step (by norm_num) pSeventeenA2s2 pSeventeenA21 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s4 : XPow fSeventeenA2 18
    (X^18) :=
  sq_step (by norm_num) pSeventeenA2s3 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s5 : XPow fSeventeenA2 36
    (10*X^33 + 39*X^32 + 24*X^31 + 30*X^30 + 19*X^29 + 63*X^28 + 30*X^27 + 61*X^26 + 63*X^25 + 49*X^24 +
      13*X^23 + 14*X^22 + 52*X^21 + 44*X^20 + 35*X^19 + 39*X^18 + 36*X^17 + 46*X^16 + 50*X^15 +
      46*X^14 + 11*X^13 + 41*X^12 + 19*X^11 + 61*X^10 + 53*X^9 + 21*X^8 + 60*X^7 + 20*X^6 + 44*X^5 +
      48*X^4 + 54*X^3 + 4*X^2 + 55*X + 8) :=
  sq_step (by norm_num) pSeventeenA2s4 ⟨
    X^2 + 44*X + 19,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s6 : XPow fSeventeenA2 37
    (10*X^33 + 16*X^32 + 28*X^31 + 46*X^30 + 24*X^29 + 59*X^28 + 51*X^27 + 46*X^26 + 14*X^25 + 7*X^24 +
      32*X^23 + 65*X^22 + 64*X^21 + 53*X^20 + 57*X^19 + 12*X^18 + 38*X^17 + 42*X^16 + 39*X^15 +
      60*X^14 + 59*X^13 + 29*X^12 + 59*X^11 + 26*X^10 + 30*X^9 + 50*X^8 + 15*X^7 + 61*X^6 + 62*X^5 +
      52*X^4 + 65*X^3 + 33*X^2 + 22*X + 43) :=
  mul_step (by norm_num) pSeventeenA2s5 pSeventeenA21 ⟨
    10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s7 : XPow fSeventeenA2 74
    (44*X^33 + 62*X^32 + 17*X^31 + 53*X^30 + 57*X^29 + 36*X^28 + 39*X^27 + 60*X^26 + 66*X^25 + 25*X^24 +
      46*X^23 + 64*X^22 + 32*X^21 + 66*X^20 + 25*X^19 + 37*X^18 + 63*X^17 + 24*X^16 + 49*X^15 +
      35*X^14 + 31*X^13 + 18*X^12 + 50*X^11 + 63*X^10 + 46*X^9 + 19*X^8 + 4*X^7 + 16*X^6 + 11*X^5 +
      52*X^4 + 60*X^3 + 13*X^2 + 15*X + 51) :=
  sq_step (by norm_num) pSeventeenA2s6 ⟨
    33*X^32 + 30*X^31 + 46*X^30 + 44*X^29 + 35*X^28 + 29*X^27 + 52*X^26 + 24*X^25 + 40*X^24 + 21*X^23 +
      49*X^22 + 28*X^21 + 13*X^20 + 63*X^19 + 33*X^18 + 9*X^17 + 47*X^16 + 49*X^15 + 37*X^14 +
      40*X^13 + 45*X^12 + 57*X^11 + 26*X^10 + 43*X^9 + 59*X^8 + 43*X^7 + 53*X^6 + 35*X^5 + 62*X^4 +
      8*X^3 + 44*X^2 + X + 1,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s8 : XPow fSeventeenA2 75
    (55*X^33 + 22*X^32 + 4*X^31 + 15*X^30 + 52*X^29 + 46*X^28 + 16*X^27 + 18*X^26 + 5*X^25 + 33*X^24 +
      36*X^23 + 49*X^22 + 20*X^21 + 64*X^20 + 9*X^19 + 11*X^18 + 29*X^17 + 54*X^16 + 31*X^15 +
      59*X^14 + 57*X^13 + 27*X^12 + 14*X^11 + 21*X^10 + 5*X^9 + 27*X^8 + 61*X^7 + 59*X^6 + 60*X^5 +
      11*X^4 + 12*X^2 + 59*X + 15) :=
  mul_step (by norm_num) pSeventeenA2s7 pSeventeenA21 ⟨
    44,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s9 : XPow fSeventeenA2 150
    (38*X^33 + 52*X^32 + 6*X^31 + 38*X^30 + 63*X^29 + 16*X^28 + 18*X^27 + 49*X^26 + 4*X^25 + 40*X^24 +
      32*X^23 + 16*X^22 + 4*X^21 + 11*X^20 + 12*X^19 + 19*X^18 + 66*X^17 + 66*X^16 + 20*X^15 +
      50*X^14 + 31*X^13 + 5*X^12 + 31*X^11 + 10*X^10 + 43*X^9 + 56*X^8 + 15*X^7 + 60*X^6 + 58*X^5 +
      26*X^4 + 23*X^3 + 38*X^2 + 40*X + 65) :=
  sq_step (by norm_num) pSeventeenA2s8 ⟨
    10*X^32 + 46*X^31 + 59*X^30 + 55*X^29 + 23*X^28 + 54*X^27 + 47*X^26 + 41*X^25 + 36*X^24 + 16*X^23 +
      43*X^22 + 14*X^21 + 24*X^20 + 58*X^19 + 54*X^18 + 13*X^17 + 21*X^16 + 63*X^15 + 34*X^14 +
      46*X^13 + 13*X^12 + 33*X^11 + 30*X^10 + 61*X^9 + 19*X^7 + 2*X^6 + 45*X^5 + 52*X^4 + 50*X^3 +
      X^2 + 19*X + 22,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s10 : XPow fSeventeenA2 151
    (49*X^33 + 56*X^32 + 17*X^31 + 45*X^30 + 42*X^29 + 21*X^28 + 11*X^27 + 60*X^26 + 41*X^25 + 36*X^24 +
      4*X^23 + 40*X^22 + 20*X^21 + 7*X^19 + 15*X^18 + 49*X^17 + 3*X^16 + 10*X^15 + 43*X^14 + 60*X^13 +
      2*X^12 + 56*X^11 + 61*X^10 + 50*X^9 + 44*X^8 + 41*X^7 + 2*X^6 + 39*X^5 + 2*X^4 + 42*X^3 +
      10*X^2 + 11*X + 16) :=
  mul_step (by norm_num) pSeventeenA2s9 pSeventeenA21 ⟨
    38,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s11 : XPow fSeventeenA2 302
    (16*X^33 + 34*X^32 + 20*X^31 + 37*X^30 + 7*X^29 + 30*X^28 + 60*X^27 + 33*X^26 + 48*X^25 + 38*X^24 +
      12*X^23 + 9*X^22 + 34*X^21 + 5*X^20 + 53*X^19 + 58*X^18 + 22*X^17 + 38*X^16 + 45*X^15 +
      61*X^14 + 6*X^13 + 17*X^12 + 47*X^11 + 52*X^10 + 31*X^9 + 19*X^8 + 26*X^7 + 60*X^6 + 20*X^5 +
      41*X^4 + 5*X^3 + 26*X^2 + 34*X + 37) :=
  sq_step (by norm_num) pSeventeenA2s10 ⟨
    56*X^32 + 46*X^31 + 41*X^30 + 30*X^29 + 47*X^28 + 63*X^27 + 37*X^26 + 34*X^25 + 47*X^24 + 33*X^23 +
      59*X^22 + 40*X^20 + 53*X^19 + 56*X^18 + 19*X^17 + 19*X^16 + 29*X^15 + 40*X^14 + 20*X^13 +
      66*X^12 + 46*X^11 + 45*X^10 + 7*X^9 + 15*X^8 + 49*X^7 + 51*X^6 + 27*X^5 + 7*X^4 + 34*X^3 +
      40*X^2 + 28*X + 41,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s12 : XPow fSeventeenA2 303
    (X^33 + 34*X^32 + 7*X^31 + 10*X^30 + 48*X^29 + 26*X^28 + 17*X^27 + 61*X^26 + 49*X^25 + 56*X^24 +
      11*X^23 + 28*X^22 + 37*X^21 + 55*X^20 + 60*X^19 + 64*X^18 + 52*X^17 + 59*X^16 + 23*X^15 +
      4*X^14 + 19*X^13 + 63*X^12 + 22*X^11 + 28*X^10 + 20*X^9 + 10*X^8 + 52*X^7 + 7*X^6 + 50*X^5 +
      42*X^4 + 3*X^3 + 39*X^2 + 46*X + 42) :=
  mul_step (by norm_num) pSeventeenA2s11 pSeventeenA21 ⟨
    16,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s13 : XPow fSeventeenA2 606
    (15*X^33 + 41*X^32 + 56*X^31 + 31*X^30 + 21*X^29 + 33*X^28 + 57*X^27 + 44*X^26 + 49*X^25 + 14*X^24 +
      2*X^23 + 40*X^22 + X^21 + 58*X^20 + 8*X^19 + 45*X^18 + 24*X^17 + 60*X^16 + 15*X^15 + 40*X^14 +
      42*X^13 + 65*X^12 + 63*X^11 + 20*X^10 + 60*X^9 + 22*X^8 + 26*X^7 + 32*X^6 + 43*X^5 + 63*X^4 +
      15*X^3 + 57*X^2 + 5*X + 60) :=
  sq_step (by norm_num) pSeventeenA2s12 ⟨
    X^32 + 45*X^31 + 27*X^30 + 13*X^29 + 9*X^28 + 41*X^27 + 14*X^26 + 20*X^25 + 40*X^24 + 4*X^23 +
      32*X^22 + 26*X^21 + 7*X^20 + 9*X^19 + 29*X^18 + 10*X^17 + 31*X^16 + 18*X^15 + 4*X^14 + 10*X^13 +
      3*X^12 + 38*X^11 + 42*X^10 + 18*X^9 + 65*X^8 + 17*X^7 + 63*X^6 + 13*X^5 + 26*X^4 + 2*X^3 +
      60*X^2 + 40*X + 40,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s14 : XPow fSeventeenA2 607
    (31*X^33 + 44*X^32 + 28*X^31 + 28*X^30 + 8*X^29 + 29*X^27 + 57*X^26 + 62*X^25 + 60*X^24 + 54*X^22 +
      21*X^21 + 35*X^20 + 5*X^19 + 55*X^18 + 48*X^17 + 3*X^16 + 63*X^15 + 15*X^14 + 25*X^13 +
      11*X^12 + 17*X^11 + 53*X^10 + 2*X^9 + 11*X^8 + 58*X^7 + 35*X^6 + 17*X^5 + 12*X^4 + 48*X^3 +
      39*X^2 + 14*X + 31) :=
  mul_step (by norm_num) pSeventeenA2s13 pSeventeenA21 ⟨
    15,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s15 : XPow fSeventeenA2 1214
    (54*X^33 + 39*X^32 + 66*X^31 + 41*X^30 + 11*X^29 + 6*X^28 + 56*X^27 + 9*X^26 + X^25 + 39*X^24 +
      13*X^23 + 37*X^22 + 57*X^21 + 49*X^20 + 59*X^19 + 65*X^18 + 23*X^17 + 21*X^16 + 6*X^15 +
      48*X^14 + 46*X^13 + 35*X^12 + 13*X^11 + 7*X^10 + 59*X^9 + 8*X^8 + 28*X^7 + 33*X^6 + 41*X^5 +
      58*X^3 + 59*X^2 + 42*X + 2) :=
  sq_step (by norm_num) pSeventeenA2s14 ⟨
    23*X^32 + 55*X^31 + 57*X^30 + 13*X^29 + 31*X^27 + 9*X^26 + 54*X^25 + 47*X^24 + 13*X^23 + 30*X^22 +
      65*X^21 + 38*X^20 + 16*X^19 + 64*X^18 + 26*X^17 + 13*X^16 + 11*X^15 + 33*X^14 + 23*X^13 +
      56*X^12 + 37*X^11 + 65*X^10 + 43*X^9 + 54*X^8 + 5*X^7 + 38*X^6 + 10*X^5 + 31*X^4 + 48*X^3 +
      50*X^2 + 38*X + 59,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s16 : XPow fSeventeenA2 1215
    (3*X^33 + 63*X^32 + 57*X^31 + 63*X^30 + 50*X^29 + 25*X^28 + 22*X^27 + 3*X^26 + 51*X^25 + 61*X^24 +
      27*X^23 + 20*X^22 + 23*X^21 + 49*X^20 + 55*X^19 + 14*X^18 + 18*X^17 + 3*X^16 + 37*X^15 +
      56*X^14 + 25*X^13 + 23*X^11 + 7*X^10 + 3*X^9 + 41*X^8 + 6*X^7 + 39*X^6 + 22*X^5 + 7*X^4 +
      40*X^3 + 17*X^2 + 24*X + 58) :=
  mul_step (by norm_num) pSeventeenA2s15 pSeventeenA21 ⟨
    54,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s17 : XPow fSeventeenA2 2430
    (13*X^32 + 66*X^31 + 25*X^30 + 26*X^29 + 65*X^28 + 15*X^27 + 16*X^26 + 31*X^25 + 20*X^24 + 44*X^23 +
      61*X^22 + 24*X^20 + 44*X^19 + 38*X^18 + 37*X^17 + 22*X^16 + 65*X^15 + 38*X^14 + 56*X^13 +
      47*X^12 + 13*X^11 + 61*X^10 + 14*X^9 + 29*X^8 + 9*X^7 + 23*X^6 + 28*X^5 + 26*X^4 + X^3 +
      31*X^2 + 18*X + 22) :=
  sq_step (by norm_num) pSeventeenA2s16 ⟨
    9*X^32 + 37*X^31 + 9*X^30 + 32*X^29 + 34*X^28 + 10*X^27 + 31*X^26 + 12*X^25 + 38*X^24 + 10*X^23 +
      21*X^22 + 64*X^21 + 16*X^20 + 31*X^19 + 43*X^18 + 14*X^17 + 56*X^16 + 14*X^15 + 39*X^14 +
      50*X^13 + 3*X^12 + 33*X^11 + 41*X^9 + 54*X^8 + 40*X^7 + 10*X^6 + 50*X^5 + 7*X^4 + 9*X^3 +
      43*X^2 + 19*X + 19,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s18 : XPow fSeventeenA2 4860
    (48*X^33 + 33*X^32 + 44*X^31 + 54*X^30 + 52*X^29 + 25*X^28 + 23*X^27 + 43*X^26 + 54*X^25 + 61*X^24 +
      56*X^23 + X^22 + 27*X^21 + 6*X^20 + 56*X^19 + 25*X^18 + 5*X^16 + 28*X^15 + 23*X^14 + 57*X^13 +
      15*X^12 + 10*X^11 + 17*X^10 + 28*X^9 + 53*X^8 + 8*X^7 + 29*X^6 + 27*X^5 + 15*X^4 + 39*X^3 +
      21*X^2 + 31*X + 35) :=
  sq_step (by norm_num) pSeventeenA2s17 ⟨
    35*X^30 + 40*X^29 + 38*X^28 + 48*X^27 + 56*X^26 + 30*X^25 + 58*X^24 + 6*X^23 + 24*X^22 + 38*X^21 +
      22*X^20 + 59*X^19 + 22*X^18 + 38*X^17 + 4*X^16 + 30*X^15 + 49*X^14 + 33*X^13 + 22*X^12 +
      22*X^11 + 59*X^10 + 49*X^9 + 18*X^8 + 18*X^7 + 21*X^6 + 42*X^5 + 29*X^4 + 43*X^3 + 27*X^2 +
      7*X + 14,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s19 : XPow fSeventeenA2 9720
    (13*X^33 + 23*X^32 + 54*X^31 + 18*X^30 + 14*X^29 + 51*X^28 + 11*X^27 + 54*X^26 + 62*X^25 + 13*X^24 +
      25*X^23 + 23*X^22 + 23*X^21 + 57*X^20 + 36*X^19 + 32*X^18 + 23*X^17 + 50*X^16 + 13*X^15 +
      8*X^14 + 14*X^13 + 12*X^12 + 58*X^11 + 26*X^10 + 64*X^9 + 18*X^8 + 19*X^7 + 26*X^6 + 44*X^5 +
      7*X^4 + 21*X^3 + 54*X^2 + 61*X + 43) :=
  sq_step (by norm_num) pSeventeenA2s18 ⟨
    26*X^32 + 24*X^31 + 10*X^30 + 8*X^29 + 34*X^28 + 42*X^27 + 46*X^26 + 35*X^25 + 42*X^24 + 62*X^23 +
      22*X^22 + 64*X^21 + 16*X^20 + 63*X^19 + 58*X^18 + 21*X^17 + 56*X^16 + 42*X^15 + 28*X^14 +
      38*X^13 + 59*X^12 + 23*X^11 + 36*X^10 + 65*X^9 + 10*X^8 + 14*X^7 + 66*X^6 + 19*X^5 + 20*X^4 +
      25*X^3 + 52*X^2 + 41*X + 57,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s20 : XPow fSeventeenA2 9721
    (59*X^33 + 57*X^32 + 2*X^31 + 29*X^30 + 7*X^29 + 42*X^28 + 41*X^27 + 60*X^26 + X^25 + 44*X^24 +
      33*X^23 + 60*X^22 + 16*X^21 + 46*X^20 + 42*X^19 + 32*X^18 + 53*X^17 + 16*X^16 + 19*X^15 +
      4*X^14 + 22*X^13 + 4*X^12 + 10*X^11 + 49*X^10 + 23*X^9 + 6*X^8 + 53*X^7 + 46*X^6 + 52*X^5 +
      5*X^4 + 6*X^3 + 19*X^2 + 21*X + 9) :=
  mul_step (by norm_num) pSeventeenA2s19 pSeventeenA21 ⟨
    13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s21 : XPow fSeventeenA2 19442
    (22*X^33 + 63*X^32 + 40*X^31 + 64*X^30 + 40*X^29 + 56*X^28 + 42*X^27 + 48*X^26 + 55*X^25 + 52*X^24 +
      13*X^23 + 58*X^22 + 4*X^21 + 28*X^20 + 40*X^19 + 51*X^18 + 48*X^17 + 32*X^16 + 19*X^15 +
      18*X^14 + 46*X^13 + 4*X^12 + 22*X^11 + 11*X^10 + 25*X^9 + 37*X^8 + 11*X^7 + 27*X^6 + 22*X^5 +
      19*X^4 + 62*X^3 + 8*X^2 + 42*X + 24) :=
  sq_step (by norm_num) pSeventeenA2s20 ⟨
    64*X^32 + 28*X^31 + 16*X^30 + 4*X^29 + 31*X^28 + 32*X^27 + 4*X^26 + 16*X^25 + 8*X^24 + 51*X^23 +
      18*X^22 + 34*X^21 + 17*X^20 + 41*X^19 + 44*X^18 + 13*X^17 + 7*X^16 + 13*X^15 + 13*X^14 +
      42*X^13 + 54*X^12 + 29*X^11 + 32*X^10 + 28*X^9 + 48*X^8 + 54*X^7 + 6*X^6 + 38*X^5 + 18*X^4 +
      12*X^3 + 26*X^2 + 38*X + 7,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s22 : XPow fSeventeenA2 19443
    (26*X^33 + 9*X^32 + 6*X^31 + 19*X^30 + 64*X^29 + 12*X^28 + 26*X^27 + 31*X^26 + 42*X^25 + 40*X^24 +
      44*X^23 + 46*X^22 + 5*X^21 + 26*X^20 + 37*X^19 + 22*X^18 + X^17 + 55*X^16 + 16*X^15 + 60*X^14 +
      57*X^13 + 44*X^12 + 20*X^11 + 46*X^10 + 30*X^9 + 56*X^8 + 16*X^7 + 46*X^6 + 23*X^5 + 4*X^4 +
      35*X^3 + 7*X^2 + 28*X + 41) :=
  mul_step (by norm_num) pSeventeenA2s21 pSeventeenA21 ⟨
    22,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s23 : XPow fSeventeenA2 38886
    (39*X^33 + 25*X^32 + 45*X^30 + 34*X^29 + 41*X^28 + 32*X^27 + 66*X^26 + 35*X^25 + 29*X^24 + 47*X^23 +
      63*X^22 + 13*X^21 + 40*X^20 + 31*X^19 + 40*X^18 + 34*X^17 + 24*X^16 + 3*X^15 + 33*X^14 +
      3*X^13 + 56*X^12 + 6*X^11 + 36*X^10 + 29*X^9 + 44*X^8 + 10*X^7 + 54*X^6 + 45*X^5 + 31*X^4 +
      30*X^3 + 58*X^2 + X + 36) :=
  sq_step (by norm_num) pSeventeenA2s22 ⟨
    6*X^32 + 62*X^31 + 61*X^30 + 4*X^29 + 18*X^28 + 57*X^27 + 18*X^26 + 19*X^25 + 65*X^24 + 19*X^23 +
      37*X^22 + 44*X^21 + 30*X^20 + 16*X^19 + 64*X^18 + 44*X^17 + 28*X^16 + 58*X^15 + 20*X^14 +
      54*X^13 + 44*X^12 + 50*X^11 + 49*X^10 + 32*X^9 + 5*X^8 + 30*X^7 + 60*X^6 + 37*X^5 + 30*X^4 +
      25*X^3 + 7*X^2 + 64*X + 21,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s24 : XPow fSeventeenA2 38887
    (66*X^33 + 9*X^32 + 64*X^31 + 12*X^30 + 43*X^29 + 58*X^28 + 27*X^27 + 29*X^26 + 60*X^25 + 37*X^24 +
      26*X^23 + 57*X^22 + 51*X^21 + 61*X^20 + 3*X^19 + 61*X^18 + 33*X^17 + 12*X^16 + 66*X^15 +
      40*X^14 + 19*X^13 + 45*X^12 + 55*X^11 + 51*X^10 + 59*X^9 + 38*X^8 + X^7 + 51*X^6 + 32*X^5 +
      49*X^4 + 48*X^3 + 9*X^2 + 37*X + 27) :=
  mul_step (by norm_num) pSeventeenA2s23 pSeventeenA21 ⟨
    39,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s25 : XPow fSeventeenA2 77774
    (56*X^33 + 16*X^32 + 19*X^31 + 7*X^30 + 16*X^29 + 39*X^28 + 26*X^27 + 8*X^26 + 38*X^25 + 39*X^24 +
      13*X^23 + 51*X^22 + 52*X^21 + 39*X^20 + 53*X^19 + 38*X^18 + 25*X^17 + 45*X^16 + 45*X^15 +
      33*X^14 + 47*X^13 + 46*X^12 + 18*X^11 + 64*X^10 + 6*X^9 + 50*X^8 + 19*X^7 + 58*X^6 + 5*X^5 +
      62*X^4 + 61*X^3 + 32*X^2 + 47*X + 11) :=
  sq_step (by norm_num) pSeventeenA2s24 ⟨
    X^32 + 26*X^31 + 51*X^30 + X^29 + 66*X^28 + X^27 + 62*X^26 + 46*X^25 + 48*X^24 + 13*X^23 + 33*X^22 +
      21*X^21 + 16*X^20 + 41*X^19 + 49*X^18 + 65*X^17 + 59*X^16 + 17*X^15 + 58*X^14 + 27*X^13 +
      7*X^12 + 23*X^11 + 11*X^10 + 46*X^9 + 25*X^8 + 52*X^7 + 24*X^6 + 50*X^5 + 22*X^4 + 20*X^3 +
      13*X^2 + 15*X + 20,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s26 : XPow fSeventeenA2 77775
    (X^33 + X^32 + 36*X^31 + 60*X^30 + 35*X^29 + 41*X^28 + 19*X^27 + 50*X^26 + 44*X^25 + 33*X^24 +
      58*X^23 + 31*X^22 + 17*X^21 + 60*X^20 + 45*X^19 + 38*X^18 + 27*X^17 + 27*X^16 + 34*X^15 +
      40*X^14 + 53*X^13 + 7*X^12 + 26*X^11 + 29*X^10 + 20*X^9 + 30*X^8 + 30*X^7 + 60*X^6 + 60*X^5 +
      23*X^4 + 52*X^3 + 31*X^2 + 9*X + 13) :=
  mul_step (by norm_num) pSeventeenA2s25 pSeventeenA21 ⟨
    56,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s27 : XPow fSeventeenA2 155550
    (21*X^33 + 54*X^32 + 66*X^31 + 52*X^30 + 33*X^29 + 49*X^28 + 11*X^27 + 26*X^26 + 66*X^25 + 30*X^24 +
      3*X^23 + 54*X^22 + 17*X^21 + 62*X^20 + 13*X^19 + 26*X^18 + 18*X^17 + 11*X^16 + 42*X^15 +
      64*X^14 + 21*X^13 + 52*X^12 + 28*X^11 + 13*X^10 + 50*X^9 + 22*X^8 + 51*X^7 + 30*X^6 + 61*X^5 +
      36*X^4 + 26*X^3 + 6*X^2 + 49*X + 49) :=
  sq_step (by norm_num) pSeventeenA2s26 ⟨
    X^32 + 46*X^31 + 46*X^30 + 35*X^29 + 28*X^28 + 5*X^27 + 20*X^26 + 54*X^25 + 8*X^24 + 62*X^23 +
      32*X^22 + 27*X^21 + 44*X^20 + 19*X^19 + 66*X^18 + 50*X^17 + X^16 + 2*X^14 + 29*X^13 + 5*X^12 +
      11*X^11 + 4*X^10 + 39*X^9 + 58*X^8 + 20*X^7 + 2*X^6 + 51*X^5 + 9*X^4 + 18*X^3 + 58*X^2 + 56*X +
      50,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s28 : XPow fSeventeenA2 155551
    (40*X^33 + 9*X^32 + 21*X^31 + 16*X^30 + 14*X^29 + 25*X^28 + 5*X^27 + 37*X^26 + 57*X^25 + 44*X^24 +
      65*X^23 + 51*X^22 + 37*X^21 + 24*X^20 + 37*X^19 + 48*X^18 + 21*X^17 + 52*X^16 + 56*X^15 +
      10*X^14 + 63*X^13 + 49*X^12 + 49*X^11 + 61*X^9 + 30*X^8 + 53*X^7 + 23*X^6 + 52*X^5 + 62*X^4 +
      47*X^3 + 43*X^2 + 65*X + 30) :=
  mul_step (by norm_num) pSeventeenA2s27 pSeventeenA21 ⟨
    21,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s29 : XPow fSeventeenA2 311102
    (17*X^33 + 55*X^32 + 39*X^31 + 37*X^30 + 32*X^29 + 22*X^28 + 16*X^27 + 38*X^26 + 7*X^25 + 9*X^24 +
      29*X^23 + 41*X^22 + 57*X^21 + 39*X^20 + 44*X^19 + 28*X^18 + 26*X^17 + 59*X^16 + 35*X^15 +
      3*X^14 + 50*X^13 + 51*X^12 + 17*X^11 + 10*X^10 + 53*X^9 + 56*X^8 + 32*X^7 + 61*X^6 + 6*X^5 +
      21*X^4 + 14*X^3 + 12*X^2 + 32*X + 41) :=
  sq_step (by norm_num) pSeventeenA2s28 ⟨
    59*X^32 + 33*X^31 + 57*X^30 + 14*X^29 + 6*X^28 + 63*X^27 + 25*X^26 + 35*X^25 + 27*X^24 + 3*X^23 +
      6*X^22 + 49*X^21 + 52*X^20 + 33*X^19 + 61*X^18 + 15*X^17 + 48*X^16 + 33*X^15 + 7*X^14 + 5*X^13 +
      52*X^12 + 11*X^11 + 41*X^10 + 12*X^9 + 30*X^8 + 29*X^7 + 22*X^6 + 23*X^5 + 2*X^4 + 11*X^3 +
      34*X^2 + 51*X + 62,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s30 : XPow fSeventeenA2 622204
    (39*X^33 + 63*X^32 + 66*X^31 + 27*X^30 + 50*X^29 + 21*X^28 + 14*X^27 + 2*X^26 + 6*X^25 + 65*X^24 +
      56*X^23 + 50*X^22 + 28*X^21 + 46*X^20 + 11*X^19 + 16*X^18 + 66*X^17 + 14*X^16 + 55*X^15 +
      39*X^14 + 14*X^13 + 33*X^12 + 62*X^11 + 6*X^10 + 64*X^9 + 62*X^8 + 7*X^7 + 26*X^6 + 49*X^5 +
      65*X^4 + 38*X^3 + 25*X^2 + 23*X + 37) :=
  sq_step (by norm_num) pSeventeenA2s29 ⟨
    21*X^32 + 47*X^31 + 64*X^30 + 41*X^29 + 17*X^28 + 49*X^27 + 49*X^26 + 20*X^25 + 46*X^24 + 15*X^23 +
      63*X^22 + 65*X^21 + 60*X^20 + 36*X^19 + 37*X^18 + 43*X^17 + 27*X^16 + 27*X^15 + 52*X^14 +
      49*X^13 + 48*X^12 + 11*X^11 + 48*X^10 + 20*X^9 + 38*X^8 + 8*X^7 + 16*X^6 + 46*X^5 + 62*X^4 +
      10*X^3 + 40*X^2 + 54*X + 15,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s31 : XPow fSeventeenA2 622205
    (37*X^33 + 8*X^32 + 46*X^31 + 28*X^30 + 23*X^29 + 40*X^28 + 30*X^27 + 29*X^25 + 46*X^24 + 13*X^23 +
      5*X^22 + 57*X^21 + 41*X^20 + 46*X^19 + 26*X^18 + 23*X^17 + 64*X^16 + 5*X^15 + 51*X^14 +
      63*X^13 + 34*X^12 + 25*X^11 + 19*X^10 + 10*X^9 + 35*X^8 + 40*X^7 + 55*X^6 + 66*X^5 + 57*X^4 +
      15*X^3 + 31*X^2 + 38*X + 27) :=
  mul_step (by norm_num) pSeventeenA2s30 pSeventeenA21 ⟨
    39,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s32 : XPow fSeventeenA2 1244410
    (10*X^33 + 49*X^32 + 32*X^31 + 12*X^30 + 65*X^28 + 61*X^27 + 13*X^26 + 45*X^25 + 9*X^24 + 62*X^23 +
      60*X^22 + 38*X^21 + 23*X^20 + 49*X^19 + 46*X^18 + 30*X^17 + 32*X^16 + 29*X^15 + 59*X^14 +
      47*X^13 + 10*X^12 + 25*X^10 + 49*X^9 + 22*X^8 + 13*X^7 + 59*X^6 + 2*X^5 + 9*X^4 + 50*X^3 +
      7*X^2 + 7) :=
  sq_step (by norm_num) pSeventeenA2s31 ⟨
    29*X^32 + 59*X^31 + 51*X^30 + 41*X^29 + 59*X^28 + 21*X^27 + 61*X^26 + 57*X^25 + 52*X^24 + 18*X^23 +
      21*X^22 + 33*X^21 + X^20 + 6*X^19 + 37*X^18 + 45*X^17 + 47*X^16 + 26*X^15 + 55*X^14 + 11*X^13 +
      14*X^12 + 57*X^11 + 47*X^10 + 38*X^9 + 57*X^8 + 22*X^7 + 35*X^6 + 8*X^5 + 33*X^4 + 5*X^3 +
      63*X^2 + 32*X + 44,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s33 : XPow fSeventeenA2 1244411
    (20*X^33 + 24*X^32 + 10*X^31 + 27*X^30 + 26*X^29 + 23*X^28 + 3*X^27 + 28*X^26 + 41*X^25 + 56*X^24 +
      11*X^23 + 51*X^22 + 43*X^21 + 64*X^19 + 6*X^18 + 24*X^17 + 21*X^16 + 52*X^15 + 29*X^14 +
      28*X^13 + 10*X^12 + 23*X^11 + 22*X^10 + 31*X^9 + 3*X^8 + 54*X^7 + 19*X^6 + 23*X^5 + 48*X^4 +
      X^3 + 45*X^2 + 21*X + 43) :=
  mul_step (by norm_num) pSeventeenA2s32 pSeventeenA21 ⟨
    10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s34 : XPow fSeventeenA2 2488822
    (17*X^33 + 21*X^32 + 23*X^31 + 22*X^30 + 24*X^29 + 54*X^28 + 62*X^27 + 39*X^26 + 61*X^25 + 36*X^24 +
      44*X^23 + 35*X^22 + 45*X^21 + 2*X^20 + 18*X^19 + 12*X^18 + 31*X^17 + 54*X^16 + 28*X^15 +
      18*X^14 + 8*X^13 + 43*X^12 + 64*X^11 + 12*X^10 + 23*X^9 + 25*X^8 + 20*X^7 + 9*X^6 + 31*X^5 +
      59*X^4 + 9*X^3 + 44*X^2 + 61*X + 32) :=
  sq_step (by norm_num) pSeventeenA2s33 ⟨
    65*X^32 + X^31 + 30*X^30 + 12*X^29 + 40*X^28 + 61*X^27 + 55*X^26 + 18*X^25 + 6*X^24 + 5*X^23 +
      40*X^22 + 7*X^21 + 37*X^20 + 43*X^19 + 56*X^18 + 63*X^17 + 14*X^16 + 64*X^15 + 14*X^14 +
      25*X^13 + 13*X^12 + 34*X^11 + 26*X^10 + 64*X^9 + 6*X^8 + 31*X^7 + 62*X^6 + 29*X^5 + 52*X^4 +
      24*X^3 + 2*X^2 + 46*X + 48,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s35 : XPow fSeventeenA2 2488823
    (32*X^33 + 63*X^32 + 32*X^31 + 23*X^30 + 48*X^29 + 51*X^28 + 22*X^27 + 12*X^26 + 10*X^25 + 7*X^24 +
      12*X^23 + 47*X^22 + 36*X^21 + 62*X^20 + 56*X^19 + 17*X^18 + 27*X^17 + X^16 + 53*X^15 + 31*X^14 +
      20*X^13 + 14*X^12 + 22*X^11 + 24*X^10 + 47*X^9 + 3*X^8 + 34*X^7 + 13*X^6 + 56*X^5 + 19*X^4 +
      7*X^3 + 37*X^2 + 29*X + 53) :=
  mul_step (by norm_num) pSeventeenA2s34 pSeventeenA21 ⟨
    17,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s36 : XPow fSeventeenA2 4977646
    (26*X^33 + 2*X^32 + 38*X^31 + 65*X^30 + 22*X^29 + 29*X^28 + 13*X^27 + 46*X^26 + 35*X^25 + 64*X^24 +
      42*X^23 + 44*X^22 + 49*X^21 + 14*X^20 + 33*X^19 + 12*X^18 + 23*X^17 + 25*X^16 + 42*X^15 +
      16*X^14 + 50*X^13 + 45*X^12 + 58*X^11 + 33*X^10 + 44*X^9 + 32*X^8 + 32*X^7 + 13*X^6 + 27*X^5 +
      47*X^4 + 41*X^3 + 26*X^2 + 60*X + 63) :=
  sq_step (by norm_num) pSeventeenA2s35 ⟨
    19*X^32 + 44*X^31 + 5*X^30 + 57*X^29 + 60*X^28 + 2*X^27 + 51*X^26 + 15*X^25 + 57*X^24 + 34*X^23 +
      17*X^22 + 62*X^21 + 66*X^20 + 50*X^19 + 43*X^18 + 64*X^17 + 57*X^16 + 3*X^15 + 46*X^14 + X^13 +
      56*X^12 + 40*X^11 + 4*X^10 + 18*X^9 + 46*X^8 + 54*X^7 + 46*X^6 + 54*X^5 + 52*X^4 + 10*X^3 +
      24*X + 61,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s37 : XPow fSeventeenA2 9955292
    (54*X^33 + 19*X^32 + 18*X^31 + 61*X^30 + 15*X^29 + 59*X^28 + 13*X^27 + 60*X^26 + 51*X^25 + 44*X^24 +
      64*X^23 + 37*X^22 + 26*X^21 + 24*X^20 + 2*X^19 + 33*X^18 + 52*X^17 + 48*X^16 + 29*X^15 +
      18*X^14 + 58*X^13 + 22*X^12 + 59*X^11 + 41*X^10 + 56*X^9 + 29*X^8 + 53*X^7 + 18*X^6 + 64*X^4 +
      38*X^3 + 49*X^2 + 9*X + 35) :=
  sq_step (by norm_num) pSeventeenA2s36 ⟨
    6*X^32 + 33*X^31 + 37*X^30 + 27*X^29 + 63*X^28 + 25*X^27 + 57*X^26 + 12*X^25 + 20*X^24 + 56*X^23 +
      21*X^22 + 3*X^21 + 35*X^20 + 38*X^19 + 42*X^18 + 20*X^17 + 3*X^16 + 30*X^15 + 35*X^14 +
      59*X^13 + 64*X^12 + 30*X^11 + 51*X^10 + X^9 + 11*X^8 + 26*X^7 + 12*X^6 + 13*X^5 + 64*X^4 +
      43*X^3 + 57*X^2 + 48*X + 20,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s38 : XPow fSeventeenA2 9955293
    (50*X^33 + 15*X^32 + 10*X^31 + 36*X^29 + 49*X^28 + 6*X^27 + 53*X^26 + 56*X^25 + 45*X^24 + 27*X^23 +
      56*X^22 + 65*X^21 + 59*X^20 + 23*X^19 + 43*X^18 + 45*X^17 + 26*X^16 + 7*X^15 + X^14 + 12*X^13 +
      46*X^12 + 57*X^11 + 4*X^10 + 24*X^9 + 66*X^8 + 58*X^7 + 65*X^6 + 19*X^5 + 54*X^4 + 30*X^3 +
      51*X^2 + 57*X + 58) :=
  mul_step (by norm_num) pSeventeenA2s37 pSeventeenA21 ⟨
    54,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s39 : XPow fSeventeenA2 19910586
    (24*X^33 + 42*X^32 + 46*X^31 + 11*X^30 + 29*X^29 + 18*X^28 + 35*X^27 + 29*X^26 + 17*X^25 + 60*X^24 +
      31*X^23 + 25*X^22 + 11*X^21 + 13*X^20 + 30*X^19 + 24*X^18 + 54*X^17 + 28*X^16 + 35*X^15 +
      66*X^14 + 20*X^13 + 17*X^12 + 2*X^11 + 28*X^10 + 16*X^9 + 23*X^8 + 60*X^7 + 9*X^6 + 20*X^5 +
      27*X^4 + 17*X^3 + 52*X^2 + 20*X + 57) :=
  sq_step (by norm_num) pSeventeenA2s38 ⟨
    21*X^32 + 12*X^31 + 21*X^30 + 31*X^29 + 43*X^28 + 55*X^27 + 41*X^26 + 53*X^25 + 62*X^24 + 28*X^23 +
      16*X^22 + 66*X^21 + 64*X^20 + 43*X^19 + 6*X^18 + 4*X^17 + 39*X^16 + 64*X^15 + 6*X^14 + 58*X^13 +
      4*X^12 + 64*X^11 + 53*X^10 + 22*X^9 + 19*X^8 + 46*X^7 + 62*X^6 + 10*X^5 + 50*X^4 + 61*X^3 +
      14*X^2 + 39*X + 10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s40 : XPow fSeventeenA2 19910587
    (26*X^33 + 33*X^31 + 45*X^29 + 51*X^28 + 5*X^27 + 3*X^26 + 43*X^25 + 30*X^24 + 28*X^23 + 2*X^22 +
      61*X^21 + 33*X^20 + 27*X^19 + 50*X^18 + 49*X^17 + 56*X^16 + 9*X^15 + 17*X^14 + 20*X^13 +
      26*X^12 + 50*X^11 + 45*X^10 + 58*X^9 + 36*X^8 + 64*X^7 + 34*X^6 + 7*X^5 + 39*X^4 + 51*X^3 +
      61*X^2 + 37*X + 63) :=
  mul_step (by norm_num) pSeventeenA2s39 pSeventeenA21 ⟨
    24,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s41 : XPow fSeventeenA2 39821174
    (50*X^33 + 46*X^32 + 37*X^31 + 44*X^30 + 15*X^29 + 27*X^28 + 47*X^27 + 38*X^26 + 34*X^25 + 57*X^24 +
      60*X^23 + 19*X^22 + 30*X^21 + 38*X^20 + 38*X^19 + 11*X^18 + 9*X^17 + 23*X^16 + 56*X^15 +
      13*X^14 + 16*X^13 + 12*X^12 + 4*X^11 + 60*X^10 + 65*X^9 + 31*X^8 + 13*X^7 + 22*X^6 + 65*X^5 +
      52*X^4 + 41*X^3 + 10*X^2 + 22*X + 52) :=
  sq_step (by norm_num) pSeventeenA2s40 ⟨
    6*X^32 + 63*X^31 + 21*X^30 + 55*X^29 + 47*X^28 + 28*X^27 + 61*X^26 + 19*X^25 + 40*X^24 + 17*X^23 +
      55*X^22 + 25*X^21 + 55*X^20 + 15*X^19 + 65*X^18 + 9*X^17 + 50*X^16 + 2*X^15 + 21*X^14 +
      58*X^13 + 7*X^12 + 48*X^11 + 6*X^10 + 44*X^9 + 29*X^8 + 14*X^7 + 30*X^6 + 17*X^5 + 63*X^4 +
      29*X^3 + 50*X^2 + 43*X + 52,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s42 : XPow fSeventeenA2 39821175
    (35*X^33 + 64*X^32 + 34*X^31 + 16*X^30 + 33*X^29 + 58*X^28 + 55*X^27 + 16*X^26 + 16*X^25 + 30*X^24 +
      42*X^23 + 28*X^22 + 4*X^21 + 61*X^20 + 34*X^19 + 23*X^18 + 50*X^17 + 16*X^16 + 45*X^15 +
      60*X^14 + 35*X^13 + 54*X^12 + 50*X^11 + 64*X^10 + 9*X^9 + 30*X^8 + 64*X^7 + 16*X^6 + 55*X^5 +
      31*X^4 + 47*X^3 + 46*X^2 + 55*X + 14) :=
  mul_step (by norm_num) pSeventeenA2s41 pSeventeenA21 ⟨
    50,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s43 : XPow fSeventeenA2 79642350
    (18*X^33 + 51*X^32 + 14*X^31 + 17*X^30 + 61*X^29 + 61*X^28 + 44*X^27 + 24*X^26 + 56*X^25 + 7*X^24 +
      43*X^23 + 33*X^22 + 43*X^21 + 34*X^20 + 11*X^19 + 42*X^18 + 24*X^17 + 29*X^15 + 13*X^14 +
      17*X^12 + 62*X^11 + 43*X^10 + 6*X^9 + 11*X^8 + 47*X^7 + 29*X^6 + 32*X^5 + 16*X^4 + 25*X^3 +
      63*X^2 + 62*X + 32) :=
  sq_step (by norm_num) pSeventeenA2s42 ⟨
    19*X^32 + 23*X^31 + 9*X^30 + 57*X^29 + 55*X^28 + 21*X^27 + 33*X^26 + 4*X^25 + 33*X^24 + 12*X^23 +
      5*X^22 + 62*X^21 + 7*X^20 + 40*X^19 + 23*X^18 + 34*X^17 + 24*X^16 + 26*X^15 + 15*X^14 +
      40*X^13 + 41*X^12 + 35*X^11 + 55*X^10 + 5*X^9 + 31*X^8 + 8*X^7 + 46*X^6 + 15*X^5 + 61*X^4 +
      35*X^3 + 34*X^2 + 62*X + 46,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s44 : XPow fSeventeenA2 79642351
    (39*X^33 + 13*X^32 + 56*X^30 + 31*X^29 + 56*X^28 + 6*X^27 + 12*X^26 + 11*X^25 + 59*X^24 + 52*X^23 +
      53*X^22 + 3*X^21 + 30*X^20 + 61*X^19 + 21*X^18 + 66*X^17 + 28*X^16 + 54*X^15 + 48*X^14 +
      36*X^13 + 13*X^12 + 26*X^11 + 11*X^10 + 54*X^9 + 29*X^8 + 20*X^7 + 9*X^6 + X^5 + 8*X^4 +
      12*X^3 + 9*X^2 + 17*X + 64) :=
  mul_step (by norm_num) pSeventeenA2s43 pSeventeenA21 ⟨
    18,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s45 : XPow fSeventeenA2 159284702
    (56*X^33 + 47*X^32 + 25*X^31 + 55*X^30 + 53*X^29 + 66*X^28 + 35*X^27 + 25*X^26 + 42*X^25 + 42*X^24 +
      4*X^23 + 8*X^22 + 45*X^21 + 42*X^19 + 35*X^18 + 60*X^17 + 46*X^16 + 29*X^15 + 46*X^14 +
      14*X^13 + X^12 + 21*X^11 + 44*X^10 + 16*X^9 + 46*X^8 + 53*X^7 + 44*X^6 + 44*X^5 + 59*X^4 +
      37*X^3 + 56*X^2 + 7*X + 34) :=
  sq_step (by norm_num) pSeventeenA2s44 ⟨
    47*X^32 + 51*X^30 + 50*X^29 + 43*X^28 + 32*X^27 + 11*X^26 + 32*X^25 + 23*X^24 + 2*X^23 + 5*X^22 +
      48*X^21 + 9*X^20 + 47*X^19 + 40*X^18 + 48*X^17 + 63*X^16 + X^15 + 40*X^14 + 18*X^13 + 48*X^12 +
      11*X^11 + 25*X^10 + 50*X^9 + 3*X^8 + 33*X^7 + 6*X^6 + 41*X^5 + 22*X^4 + 20*X^3 + 28*X^2 + 29*X +
      51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s46 : XPow fSeventeenA2 318569404
    (24*X^33 + 40*X^31 + 59*X^30 + 37*X^29 + 6*X^28 + 41*X^27 + 28*X^26 + 8*X^25 + 3*X^24 + 7*X^23 + X^22 +
      65*X^21 + 14*X^20 + 6*X^19 + 40*X^18 + 11*X^17 + 4*X^16 + 36*X^15 + 63*X^14 + 63*X^13 + 5*X^12 +
      27*X^11 + 16*X^10 + 52*X^9 + 25*X^8 + 2*X^6 + 32*X^5 + 19*X^3 + 17*X^2 + 2*X + 7) :=
  sq_step (by norm_num) pSeventeenA2s45 ⟨
    54*X^32 + 2*X^31 + 2*X^30 + 23*X^29 + 63*X^28 + 51*X^27 + 12*X^26 + 16*X^25 + 66*X^24 + 65*X^23 +
      20*X^22 + 61*X^21 + 65*X^20 + 26*X^19 + 54*X^17 + 56*X^16 + 57*X^15 + 19*X^14 + 8*X^13 +
      6*X^12 + 42*X^11 + 29*X^10 + 21*X^9 + 18*X^8 + 17*X^7 + 50*X^6 + 57*X^5 + 57*X^4 + 50*X^3 +
      14*X^2 + 65*X + 60,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s47 : XPow fSeventeenA2 637138808
    (6*X^33 + 2*X^32 + 6*X^31 + 42*X^30 + 4*X^28 + 59*X^27 + 23*X^26 + 22*X^25 + 19*X^24 + 23*X^23 +
      40*X^22 + 42*X^21 + 9*X^20 + 61*X^19 + 14*X^18 + 63*X^17 + 22*X^16 + 54*X^15 + 22*X^14 +
      27*X^13 + 26*X^12 + 8*X^11 + 15*X^10 + 54*X^9 + 23*X^8 + 39*X^7 + 44*X^6 + 63*X^5 + 64*X^4 +
      29*X^3 + 59*X^2 + 14*X + 26) :=
  sq_step (by norm_num) pSeventeenA2s46 ⟨
    40*X^32 + 18*X^31 + 9*X^29 + 44*X^28 + 49*X^27 + 28*X^26 + 7*X^25 + 18*X^24 + 22*X^23 + 51*X^22 +
      9*X^21 + 44*X^20 + 30*X^19 + 55*X^18 + 61*X^17 + 4*X^16 + 5*X^15 + 48*X^14 + 15*X^13 + 23*X^11 +
      55*X^10 + 48*X^9 + 31*X^8 + 62*X^7 + 6*X^6 + 32*X^5 + 16*X^4 + 65*X^3 + 15*X^2 + 64*X + 4,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s48 : XPow fSeventeenA2 1274277616
    (12*X^33 + 29*X^32 + 33*X^31 + 19*X^30 + 19*X^29 + 58*X^28 + 10*X^27 + 52*X^26 + 10*X^25 + 47*X^24 +
      8*X^23 + 10*X^22 + 3*X^21 + 25*X^20 + 4*X^19 + 21*X^18 + 62*X^17 + 19*X^16 + 48*X^15 + 12*X^14 +
      64*X^13 + 8*X^12 + 30*X^11 + 42*X^10 + 48*X^9 + 10*X^8 + 50*X^7 + 13*X^6 + 38*X^5 + 30*X^4 +
      47*X^3 + 45*X^2 + 55*X + 38) :=
  sq_step (by norm_num) pSeventeenA2s47 ⟨
    36*X^32 + 7*X^30 + 65*X^29 + 20*X^28 + 59*X^27 + 26*X^26 + 23*X^25 + 62*X^24 + 41*X^23 + 13*X^22 +
      57*X^21 + 3*X^20 + 13*X^19 + 39*X^18 + 25*X^17 + 37*X^16 + 19*X^15 + 56*X^14 + 40*X^13 +
      66*X^12 + 64*X^11 + 65*X^10 + 42*X^9 + 13*X^8 + 57*X^7 + 8*X^6 + 55*X^5 + 11*X^4 + 4*X^3 +
      61*X^2 + 40*X + 9,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s49 : XPow fSeventeenA2 1274277617
    (21*X^33 + 10*X^32 + 30*X^31 + 38*X^30 + 38*X^29 + 18*X^28 + 40*X^27 + 3*X^26 + 5*X^25 + 41*X^24 +
      45*X^23 + 32*X^22 + 49*X^21 + 39*X^20 + 56*X^19 + 60*X^18 + 63*X^17 + 25*X^16 + 17*X^15 +
      29*X^14 + 43*X^13 + 42*X^12 + 53*X^11 + 29*X^10 + 61*X^9 + 38*X^8 + 7*X^7 + 45*X^6 + 20*X^5 +
      58*X^4 + 11*X^3 + 42*X^2 + 28*X + 65) :=
  mul_step (by norm_num) pSeventeenA2s48 pSeventeenA21 ⟨
    12,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s50 : XPow fSeventeenA2 2548555234
    (33*X^33 + 22*X^32 + 34*X^31 + 56*X^30 + 14*X^29 + 45*X^28 + 48*X^27 + 48*X^26 + 19*X^25 + 19*X^24 +
      3*X^23 + 49*X^22 + 63*X^21 + 45*X^20 + 2*X^19 + 19*X^18 + 30*X^17 + 29*X^16 + 24*X^15 +
      29*X^14 + 38*X^13 + 34*X^12 + 32*X^11 + 37*X^10 + 51*X^9 + 6*X^8 + 48*X^7 + 10*X^6 + 46*X^5 +
      33*X^4 + 28*X^3 + 4*X^2 + 31*X + 52) :=
  sq_step (by norm_num) pSeventeenA2s49 ⟨
    39*X^32 + 59*X^31 + 12*X^30 + 56*X^29 + 62*X^28 + 52*X^27 + 14*X^26 + 31*X^25 + 3*X^24 + 42*X^23 +
      63*X^22 + 65*X^21 + 2*X^20 + 15*X^19 + 28*X^18 + 7*X^17 + 8*X^16 + 26*X^15 + 53*X^14 + 26*X^13 +
      31*X^11 + 36*X^10 + 27*X^9 + 41*X^8 + 15*X^7 + 20*X^6 + 10*X^5 + 29*X^4 + 15*X^3 + 21*X^2 +
      46*X + 47,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s51 : XPow fSeventeenA2 2548555235
    (21*X^32 + 36*X^31 + 16*X^30 + 57*X^29 + 3*X^28 + 15*X^27 + 50*X^26 + 4*X^25 + 10*X^24 + 28*X^23 +
      59*X^22 + 44*X^21 + 48*X^20 + 65*X^19 + 58*X^18 + 16*X^17 + 11*X^16 + 26*X^15 + 59*X^14 +
      13*X^13 + 65*X^12 + 17*X^11 + 49*X^10 + 29*X^9 + 15*X^8 + 27*X^7 + 15*X^6 + 39*X^5 + 8*X^4 +
      11*X^3 + 12*X^2 + 58*X + 28) :=
  mul_step (by norm_num) pSeventeenA2s50 pSeventeenA21 ⟨
    33,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s52 : XPow fSeventeenA2 5097110470
    (33*X^33 + 47*X^32 + 38*X^31 + 36*X^30 + 20*X^29 + 39*X^28 + 35*X^27 + 5*X^26 + 53*X^25 + 28*X^24 +
      56*X^23 + 6*X^22 + 13*X^21 + 10*X^20 + 55*X^19 + 10*X^18 + 63*X^17 + 25*X^15 + 36*X^14 +
      34*X^13 + 3*X^12 + 39*X^11 + 50*X^10 + 20*X^9 + 18*X^8 + 57*X^7 + 8*X^6 + 23*X^5 + 5*X^4 +
      49*X^3 + 59*X^2 + X + 40) :=
  sq_step (by norm_num) pSeventeenA2s51 ⟨
    39*X^30 + 12*X^29 + 26*X^28 + 63*X^27 + 17*X^26 + 20*X^25 + 18*X^24 + 47*X^23 + 65*X^22 + 41*X^21 +
      35*X^20 + 31*X^19 + 39*X^17 + 6*X^16 + 35*X^15 + 66*X^14 + 37*X^13 + 49*X^12 + 31*X^11 +
      23*X^10 + 12*X^9 + 31*X^8 + 46*X^7 + 15*X^6 + 5*X^5 + 58*X^4 + 52*X^3 + 58*X^2 + 43*X + 42,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s53 : XPow fSeventeenA2 5097110471
    (25*X^33 + 25*X^32 + 16*X^31 + 22*X^30 + 51*X^29 + 57*X^28 + 39*X^27 + 17*X^26 + 13*X^25 + 63*X^24 +
      52*X^23 + 9*X^22 + 9*X^21 + 34*X^20 + 56*X^19 + 24*X^18 + 54*X^17 + 12*X^16 + 33*X^15 +
      55*X^14 + 49*X^13 + 5*X^12 + 30*X^11 + 18*X^10 + 41*X^9 + 24*X^8 + 25*X^7 + 59*X^6 + 11*X^5 +
      29*X^4 + 66*X^3 + 49*X^2 + 46*X + 28) :=
  mul_step (by norm_num) pSeventeenA2s52 pSeventeenA21 ⟨
    33,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s54 : XPow fSeventeenA2 10194220942
    (43*X^33 + 46*X^32 + 34*X^31 + 57*X^30 + 64*X^29 + 56*X^28 + 45*X^27 + 15*X^25 + 7*X^24 + 59*X^23 +
      43*X^22 + 41*X^21 + 54*X^20 + 52*X^19 + 61*X^18 + 16*X^17 + 59*X^16 + 28*X^15 + 37*X^14 +
      64*X^13 + 28*X^12 + 57*X^11 + X^10 + 57*X^9 + 7*X^8 + X^7 + 40*X^6 + 20*X^5 + 19*X^4 + 56*X^3 +
      4*X^2 + 53*X + 31) :=
  sq_step (by norm_num) pSeventeenA2s53 ⟨
    22*X^32 + 7*X^31 + 27*X^30 + 63*X^29 + X^28 + 2*X^27 + 65*X^26 + 14*X^25 + 4*X^24 + 14*X^23 +
      35*X^22 + 58*X^21 + 52*X^20 + 22*X^19 + 50*X^18 + 64*X^16 + 16*X^15 + 41*X^14 + 61*X^13 +
      13*X^12 + 63*X^11 + 3*X^10 + 37*X^9 + 53*X^7 + 52*X^6 + 61*X^5 + 52*X^4 + 61*X^3 + 45*X^2 +
      52*X + 29,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s55 : XPow fSeventeenA2 20388441884
    (2*X^33 + 21*X^32 + 27*X^31 + 58*X^30 + 7*X^29 + 23*X^28 + 63*X^27 + 26*X^26 + 19*X^25 + 4*X^24 +
      9*X^23 + 13*X^22 + 19*X^21 + 29*X^20 + 16*X^19 + 14*X^18 + 32*X^17 + 7*X^16 + 8*X^15 + 31*X^14 +
      44*X^13 + 18*X^12 + 26*X^11 + 53*X^10 + 10*X^9 + 59*X^8 + 11*X^7 + 47*X^6 + 56*X^5 + 8*X^4 +
      47*X^3 + 17*X^2 + 36*X + 6) :=
  sq_step (by norm_num) pSeventeenA2s54 ⟨
    40*X^32 + 21*X^31 + 36*X^30 + 35*X^29 + 52*X^28 + 17*X^27 + 27*X^26 + 35*X^25 + 23*X^24 + 17*X^23 +
      46*X^22 + 21*X^21 + 14*X^20 + 51*X^19 + 63*X^18 + 65*X^17 + 33*X^16 + 60*X^15 + 22*X^14 +
      42*X^13 + 51*X^12 + 39*X^11 + 14*X^10 + 30*X^9 + 65*X^8 + 52*X^7 + 5*X^6 + 38*X^5 + 44*X^4 +
      40*X^3 + 12*X^2 + 29*X + 35,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s56 : XPow fSeventeenA2 20388441885
    (42*X^33 + 12*X^32 + 4*X^31 + 66*X^30 + 42*X^29 + 42*X^28 + 24*X^27 + 29*X^26 + 64*X^25 + 48*X^24 +
      30*X^23 + 35*X^22 + 33*X^21 + 33*X^20 + 31*X^19 + 54*X^18 + 59*X^17 + 60*X^16 + 43*X^15 +
      27*X^14 + 35*X^13 + 28*X^12 + 66*X^11 + 18*X^10 + 34*X^9 + 9*X^8 + 46*X^7 + 46*X^6 + 51*X^5 +
      60*X^4 + 56*X^3 + 45*X^2 + 49*X + 22) :=
  mul_step (by norm_num) pSeventeenA2s55 pSeventeenA21 ⟨
    2,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s57 : XPow fSeventeenA2 40776883770
    (39*X^33 + 38*X^32 + 25*X^31 + 6*X^30 + 58*X^29 + 3*X^28 + 43*X^27 + 53*X^26 + 35*X^25 + 60*X^24 +
      31*X^23 + 66*X^22 + 26*X^21 + 3*X^20 + 22*X^19 + 12*X^18 + 52*X^17 + 2*X^16 + 6*X^15 + 18*X^14 +
      61*X^13 + 4*X^12 + 51*X^11 + 45*X^10 + 65*X^9 + 20*X^8 + 8*X^7 + 21*X^6 + 41*X^5 + 49*X^4 +
      25*X^3 + 46*X^2 + 37*X + 36) :=
  sq_step (by norm_num) pSeventeenA2s56 ⟨
    22*X^32 + 33*X^31 + 25*X^30 + 36*X^29 + 18*X^28 + 30*X^27 + 39*X^26 + 41*X^25 + 20*X^24 + 60*X^23 +
      17*X^22 + 45*X^21 + 56*X^20 + 57*X^19 + 31*X^18 + 36*X^17 + 23*X^16 + 21*X^15 + 48*X^14 +
      45*X^13 + 17*X^12 + 25*X^11 + 33*X^10 + 6*X^9 + 64*X^8 + 51*X^7 + 42*X^6 + 12*X^5 + 53*X^4 +
      46*X^3 + 41*X^2 + 11*X + 8,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s58 : XPow fSeventeenA2 81553767540
    (40*X^33 + 27*X^32 + 58*X^31 + 61*X^30 + X^29 + 5*X^28 + 42*X^27 + 18*X^26 + 53*X^25 + 39*X^24 +
      7*X^23 + 39*X^22 + 39*X^21 + 29*X^20 + 12*X^19 + 51*X^18 + X^17 + 52*X^16 + 47*X^15 + 45*X^14 +
      22*X^13 + 41*X^12 + 42*X^11 + 16*X^10 + 55*X^9 + 10*X^8 + 36*X^7 + 46*X^6 + 49*X^5 + 65*X^4 +
      51*X^3 + 59*X^2 + 37*X + 40) :=
  sq_step (by norm_num) pSeventeenA2s57 ⟨
    47*X^32 + 7*X^31 + 33*X^30 + 53*X^29 + 43*X^28 + X^27 + 62*X^26 + 40*X^25 + 54*X^24 + 54*X^23 +
      22*X^22 + 9*X^21 + 27*X^20 + 41*X^19 + 8*X^18 + 34*X^17 + 65*X^16 + 60*X^15 + 65*X^14 + 4*X^13 +
      57*X^12 + 30*X^11 + 37*X^10 + 7*X^9 + 49*X^8 + 26*X^7 + 30*X^6 + 36*X^5 + 30*X^4 + 22*X^3 +
      32*X^2 + 58*X + 32,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s59 : XPow fSeventeenA2 81553767541
    (45*X^33 + 26*X^32 + 53*X^31 + 42*X^30 + 50*X^29 + 24*X^28 + 45*X^27 + 52*X^26 + 33*X^25 + 50*X^24 +
      44*X^23 + 24*X^22 + 42*X^21 + 17*X^20 + 56*X^19 + 39*X^18 + 20*X^17 + 15*X^16 + 17*X^15 +
      17*X^14 + 46*X^13 + 15*X^12 + 8*X^11 + 14*X^10 + 46*X^9 + 63*X^8 + 26*X^7 + 50*X^6 + 54*X^5 +
      43*X^4 + 35*X^3 + 16*X^2 + 29*X + 38) :=
  mul_step (by norm_num) pSeventeenA2s58 pSeventeenA21 ⟨
    40,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s60 : XPow fSeventeenA2 163107535082
    (43*X^33 + 55*X^32 + 30*X^31 + 4*X^30 + 50*X^29 + 46*X^28 + 45*X^27 + 41*X^26 + 35*X^25 + 19*X^24 +
      26*X^23 + 27*X^22 + 17*X^21 + 61*X^20 + 61*X^19 + 25*X^18 + 42*X^17 + 12*X^16 + 41*X^15 +
      64*X^14 + 49*X^13 + 32*X^12 + 41*X^11 + 11*X^10 + 42*X^9 + 58*X^8 + 53*X^7 + 61*X^6 + 31*X^5 +
      37*X^4 + 50*X^3 + 43*X^2 + 64*X + 17) :=
  sq_step (by norm_num) pSeventeenA2s59 ⟨
    15*X^32 + 52*X^31 + 17*X^30 + 57*X^29 + 58*X^28 + 25*X^27 + 65*X^26 + 39*X^25 + 23*X^24 + 65*X^23 +
      41*X^22 + 7*X^21 + 45*X^20 + 65*X^19 + 46*X^18 + 51*X^17 + 38*X^16 + 3*X^15 + 52*X^14 +
      30*X^13 + 42*X^12 + 19*X^11 + 31*X^10 + 58*X^9 + 56*X^8 + 10*X^7 + 46*X^6 + 20*X^5 + 24*X^4 +
      34*X^3 + 19*X^2 + 46*X + 53,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s61 : XPow fSeventeenA2 326215070164
    (8*X^33 + 57*X^32 + 20*X^31 + 66*X^30 + 27*X^28 + 38*X^27 + 45*X^26 + 17*X^25 + 48*X^24 + 45*X^23 +
      31*X^22 + 10*X^21 + 49*X^20 + 27*X^19 + 44*X^18 + 19*X^17 + 19*X^16 + 41*X^15 + 20*X^14 +
      41*X^13 + 54*X^11 + 5*X^10 + 14*X^9 + 58*X^8 + 29*X^7 + 39*X^6 + 4*X^5 + 61*X^4 + X^3 + 15*X^2 +
      18*X + 64) :=
  sq_step (by norm_num) pSeventeenA2s60 ⟨
    40*X^32 + 58*X^31 + 18*X^30 + 40*X^29 + 45*X^28 + 50*X^27 + 24*X^26 + 12*X^25 + 45*X^24 + 49*X^23 +
      55*X^22 + 47*X^21 + 5*X^20 + 66*X^19 + 32*X^18 + 44*X^17 + 23*X^16 + 19*X^15 + 6*X^14 +
      66*X^13 + 37*X^12 + 49*X^11 + 65*X^10 + 49*X^9 + 2*X^8 + 55*X^7 + 66*X^6 + 54*X^5 + 57*X^4 +
      54*X^3 + 59*X^2 + 34*X + 10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s62 : XPow fSeventeenA2 652430140328
    (59*X^33 + 12*X^32 + 4*X^31 + 24*X^30 + 56*X^29 + 16*X^28 + 52*X^27 + 61*X^26 + 51*X^25 + 16*X^24 +
      27*X^23 + 31*X^22 + 59*X^21 + 52*X^20 + 20*X^19 + 55*X^18 + 21*X^17 + 19*X^16 + 54*X^15 +
      33*X^14 + 48*X^13 + 58*X^12 + 43*X^11 + 34*X^10 + 32*X^9 + 48*X^8 + 3*X^7 + 48*X^6 + 15*X^5 +
      28*X^4 + 34*X^3 + X^2 + 4*X + 59) :=
  sq_step (by norm_num) pSeventeenA2s61 ⟨
    64*X^32 + 43*X^31 + 23*X^30 + 53*X^29 + 57*X^28 + 6*X^27 + 62*X^26 + 53*X^24 + 59*X^23 + 63*X^22 +
      3*X^21 + 56*X^20 + 7*X^19 + 17*X^18 + 21*X^17 + 54*X^16 + 46*X^15 + 6*X^14 + 18*X^13 + 56*X^12 +
      58*X^11 + 23*X^10 + 45*X^9 + 58*X^8 + 65*X^7 + 31*X^6 + 3*X^5 + 57*X^4 + 45*X^3 + 12*X^2 +
      24*X + 35,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s63 : XPow fSeventeenA2 652430140329
    (62*X^33 + 64*X^32 + 39*X^31 + 21*X^30 + 7*X^29 + 2*X^28 + 2*X^27 + 11*X^26 + 44*X^25 + 5*X^24 +
      30*X^23 + 62*X^22 + 36*X^21 + 19*X^20 + 54*X^19 + 12*X^17 + 47*X^16 + 52*X^15 + 49*X^14 +
      57*X^13 + 35*X^12 + 49*X^11 + 14*X^9 + 11*X^8 + 52*X^7 + 55*X^6 + 57*X^5 + 49*X^4 + 46*X^3 +
      35*X^2 + 21*X + 46) :=
  mul_step (by norm_num) pSeventeenA2s62 pSeventeenA21 ⟨
    59,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s64 : XPow fSeventeenA2 1304860280658
    (17*X^33 + 58*X^32 + 7*X^31 + 49*X^30 + 5*X^29 + 36*X^28 + 63*X^27 + 25*X^26 + 65*X^25 + 59*X^24 +
      24*X^23 + 44*X^22 + 17*X^21 + 49*X^20 + 20*X^19 + 31*X^18 + 31*X^17 + 13*X^16 + 22*X^15 +
      27*X^14 + 39*X^13 + 11*X^12 + 30*X^11 + 30*X^10 + 26*X^9 + 20*X^8 + 23*X^7 + 56*X^6 + 13*X^5 +
      45*X^4 + 41*X^3 + 64*X^2 + 19*X + 39) :=
  sq_step (by norm_num) pSeventeenA2s63 ⟨
    25*X^32 + 58*X^31 + 7*X^30 + 27*X^29 + 24*X^28 + 35*X^27 + 4*X^26 + 57*X^25 + 63*X^24 + 45*X^23 +
      2*X^22 + 53*X^21 + 62*X^20 + 51*X^19 + 58*X^18 + 7*X^17 + 18*X^16 + 45*X^15 + 60*X^14 + 7*X^13 +
      56*X^12 + 58*X^11 + 21*X^10 + 38*X^9 + 49*X^8 + 60*X^7 + 21*X^6 + 16*X^5 + 46*X^4 + 44*X^3 +
      37*X^2 + 21*X,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s65 : XPow fSeventeenA2 2609720561316
    (27*X^33 + 13*X^32 + 14*X^31 + 46*X^30 + 63*X^29 + 10*X^28 + 47*X^27 + 4*X^26 + 27*X^25 + 16*X^24 +
      51*X^23 + 39*X^22 + 65*X^21 + 23*X^20 + 55*X^19 + 19*X^18 + 40*X^17 + 3*X^16 + 47*X^15 +
      64*X^14 + 60*X^13 + 44*X^12 + 54*X^11 + 41*X^10 + 17*X^9 + 37*X^8 + 54*X^7 + 36*X^6 + 20*X^5 +
      63*X^4 + 46*X^3 + 28*X^2 + 41*X + 13) :=
  sq_step (by norm_num) pSeventeenA2s64 ⟨
    21*X^32 + 15*X^31 + 51*X^30 + 56*X^29 + 25*X^28 + 23*X^27 + 14*X^26 + 58*X^25 + X^24 + 27*X^23 +
      52*X^22 + 2*X^21 + 24*X^20 + 12*X^19 + 31*X^18 + 25*X^17 + 15*X^16 + 45*X^15 + 28*X^14 +
      64*X^13 + 21*X^12 + 6*X^11 + 45*X^10 + 49*X^9 + 34*X^8 + 66*X^7 + 48*X^6 + 16*X^5 + 63*X^4 +
      41*X^3 + 65*X^2 + 55*X + 3,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s66 : XPow fSeventeenA2 2609720561317
    (62*X^33 + 46*X^32 + 54*X^31 + 22*X^30 + 32*X^29 + 65*X^28 + 44*X^27 + 28*X^26 + 22*X^25 + 8*X^24 +
      34*X^23 + 13*X^22 + 10*X^21 + 50*X^20 + 14*X^19 + 2*X^18 + 35*X^17 + 12*X^16 + 25*X^15 +
      65*X^14 + 39*X^13 + 14*X^12 + 49*X^11 + 58*X^10 + X^9 + 27*X^8 + 56*X^7 + 19*X^6 + 7*X^5 +
      54*X^4 + 52*X^3 + 62*X^2 + 24*X + 29) :=
  mul_step (by norm_num) pSeventeenA2s65 pSeventeenA21 ⟨
    27,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s67 : XPow fSeventeenA2 5219441122634
    (10*X^33 + 3*X^32 + 52*X^31 + X^30 + 56*X^29 + 63*X^28 + 22*X^27 + 31*X^26 + 56*X^25 + 47*X^23 +
      13*X^22 + 14*X^21 + 60*X^20 + 53*X^19 + 48*X^18 + 39*X^17 + 24*X^16 + 20*X^15 + 18*X^14 +
      46*X^13 + 33*X^12 + 30*X^11 + 28*X^10 + 57*X^9 + 44*X^8 + 3*X^7 + 42*X^6 + 2*X^5 + 64*X^4 +
      65*X^3 + 19*X^2 + 6*X + 54) :=
  sq_step (by norm_num) pSeventeenA2s66 ⟨
    25*X^32 + 37*X^31 + 35*X^30 + 9*X^29 + 3*X^28 + 60*X^27 + 45*X^26 + 61*X^25 + 22*X^24 + 66*X^23 +
      55*X^22 + 10*X^21 + 32*X^20 + 59*X^19 + 58*X^18 + 35*X^17 + 28*X^16 + 45*X^15 + 33*X^14 +
      42*X^13 + 22*X^12 + 59*X^11 + 40*X^10 + 55*X^9 + 15*X^8 + 44*X^7 + 31*X^6 + 55*X^5 + 30*X^4 +
      44*X^3 + 10*X^2 + 49*X + 32,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s68 : XPow fSeventeenA2 10438882245268
    (54*X^33 + 28*X^32 + 31*X^31 + 47*X^30 + 58*X^29 + 44*X^28 + 14*X^27 + 7*X^26 + 43*X^25 + 62*X^24 +
      64*X^23 + 30*X^22 + 18*X^21 + 56*X^20 + 44*X^18 + 39*X^17 + 65*X^16 + 55*X^15 + 47*X^14 +
      23*X^13 + 9*X^12 + 39*X^11 + 16*X^10 + 63*X^9 + 50*X^8 + 42*X^7 + 53*X^5 + 15*X^4 + 36*X^3 +
      41*X^2 + 20) :=
  sq_step (by norm_num) pSeventeenA2s67 ⟨
    33*X^32 + 38*X^31 + 28*X^30 + 53*X^29 + 37*X^28 + 58*X^27 + 19*X^26 + 8*X^25 + 60*X^24 + 42*X^23 +
      50*X^22 + 15*X^21 + 25*X^20 + 58*X^19 + 16*X^18 + 5*X^17 + 37*X^16 + 18*X^15 + 46*X^14 +
      4*X^13 + 32*X^12 + 36*X^11 + 52*X^10 + 40*X^9 + 53*X^8 + 27*X^7 + 56*X^6 + 24*X^5 + 18*X^4 +
      27*X^3 + X^2 + 21*X + 23,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s69 : XPow fSeventeenA2 20877764490536
    (45*X^33 + 49*X^32 + 11*X^31 + 3*X^30 + 39*X^29 + 44*X^28 + 42*X^27 + 17*X^26 + 34*X^25 + 10*X^24 +
      65*X^23 + 9*X^22 + 11*X^21 + 13*X^20 + 16*X^19 + 62*X^18 + 46*X^17 + 20*X^16 + 34*X^15 +
      20*X^14 + 26*X^13 + 14*X^12 + 14*X^11 + 9*X^10 + 63*X^9 + 14*X^8 + 53*X^7 + 35*X^6 + 29*X^5 +
      22*X^4 + 50*X^3 + 7*X^2 + 65*X + 52) :=
  sq_step (by norm_num) pSeventeenA2s68 ⟨
    35*X^32 + 8*X^31 + 34*X^30 + 12*X^27 + 66*X^26 + 8*X^25 + 17*X^24 + 60*X^23 + 5*X^22 + 18*X^21 +
      9*X^20 + 53*X^19 + 62*X^17 + 62*X^16 + 7*X^15 + 26*X^14 + 43*X^13 + 31*X^12 + 42*X^11 +
      44*X^10 + 31*X^9 + 16*X^8 + 4*X^7 + 25*X^6 + 35*X^5 + 41*X^4 + 64*X^3 + 59*X^2 + 24*X + 11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s70 : XPow fSeventeenA2 20877764490537
    (19*X^33 + 42*X^32 + 61*X^31 + 60*X^30 + 36*X^29 + 5*X^28 + 39*X^27 + 58*X^26 + 20*X^25 + 38*X^24 +
      23*X^23 + 36*X^22 + 36*X^21 + 30*X^20 + 9*X^19 + 5*X^18 + 51*X^17 + 65*X^16 + 22*X^15 +
      12*X^14 + 28*X^13 + 59*X^12 + 42*X^10 + 21*X^9 + 8*X^8 + 46*X^7 + 5*X^6 + 18*X^5 + 41*X^4 +
      47*X^3 + 33*X^2 + 48*X + 26) :=
  mul_step (by norm_num) pSeventeenA2s69 pSeventeenA21 ⟨
    45,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s71 : XPow fSeventeenA2 41755528981074
    (35*X^33 + 58*X^32 + 29*X^31 + 65*X^30 + 59*X^29 + 62*X^28 + 22*X^27 + 31*X^26 + 52*X^25 + 65*X^24 +
      38*X^23 + 17*X^22 + 11*X^21 + 22*X^20 + 54*X^19 + 35*X^18 + 3*X^17 + 62*X^16 + 42*X^15 +
      22*X^14 + 18*X^13 + 51*X^12 + 44*X^11 + 20*X^10 + 37*X^9 + 45*X^8 + 23*X^7 + 32*X^6 + 17*X^5 +
      15*X^4 + 2*X^3 + 66*X^2 + 24*X + 29) :=
  sq_step (by norm_num) pSeventeenA2s70 ⟨
    26*X^32 + 60*X^31 + 28*X^30 + 47*X^29 + 12*X^28 + 11*X^27 + 25*X^26 + 40*X^25 + X^24 + 30*X^23 +
      50*X^22 + 37*X^21 + 53*X^20 + 22*X^19 + 62*X^18 + 2*X^17 + 43*X^16 + 25*X^15 + 8*X^14 +
      23*X^13 + 21*X^12 + 50*X^11 + 10*X^10 + 16*X^9 + 60*X^8 + 15*X^6 + 48*X^5 + 63*X^4 + 63*X^3 +
      8*X^2 + 45*X + 63,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s72 : XPow fSeventeenA2 83511057962148
    (45*X^33 + 24*X^32 + 66*X^31 + 55*X^30 + 50*X^29 + 2*X^28 + 48*X^27 + X^26 + 58*X^25 + 58*X^24 +
      36*X^23 + 24*X^22 + 62*X^21 + 62*X^20 + 3*X^19 + 58*X^18 + 38*X^17 + 39*X^16 + 27*X^15 +
      8*X^14 + 28*X^13 + 43*X^12 + 36*X^11 + 45*X^10 + 51*X^9 + 3*X^8 + 43*X^7 + 46*X^6 + 21*X^5 +
      65*X^4 + 3*X^3 + 29*X^2 + 3*X + 57) :=
  sq_step (by norm_num) pSeventeenA2s71 ⟨
    19*X^32 + 5*X^31 + 11*X^30 + 42*X^29 + 29*X^28 + 58*X^26 + X^25 + 54*X^24 + 59*X^23 + 52*X^22 +
      65*X^21 + 41*X^20 + 42*X^19 + 19*X^18 + 22*X^17 + 55*X^16 + 49*X^15 + 22*X^14 + 37*X^12 +
      58*X^10 + 36*X^9 + 12*X^8 + 35*X^7 + 16*X^6 + 14*X^5 + 44*X^4 + 64*X^3 + 48*X^2 + 23*X + 14,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s73 : XPow fSeventeenA2 167022115924296
    (47*X^33 + 16*X^32 + 30*X^31 + 2*X^30 + 9*X^29 + 38*X^28 + 66*X^27 + 39*X^26 + 12*X^25 + 57*X^24 +
      23*X^23 + 32*X^21 + 4*X^20 + 3*X^19 + 41*X^18 + 14*X^17 + 64*X^16 + 63*X^15 + 51*X^14 +
      63*X^13 + 12*X^12 + 45*X^11 + 18*X^10 + 24*X^9 + 32*X^8 + 35*X^7 + 54*X^6 + 34*X^5 + 35*X^4 +
      60*X^3 + 42*X^2 + 10*X + 55) :=
  sq_step (by norm_num) pSeventeenA2s72 ⟨
    15*X^32 + 6*X^31 + X^30 + 7*X^29 + 17*X^28 + 41*X^27 + 14*X^26 + 5*X^25 + 56*X^24 + 21*X^23 +
      58*X^22 + 12*X^21 + 25*X^20 + 30*X^19 + 66*X^18 + 24*X^17 + 11*X^16 + 65*X^15 + 66*X^14 +
      52*X^13 + 19*X^12 + 47*X^11 + 50*X^10 + 8*X^9 + 11*X^8 + 57*X^7 + 39*X^6 + 35*X^5 + 28*X^4 +
      3*X^3 + 39*X + 2,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s74 : XPow fSeventeenA2 334044231848592
    (2*X^33 + 40*X^32 + 7*X^31 + 65*X^30 + 32*X^29 + 37*X^28 + 44*X^27 + 53*X^26 + 9*X^25 + 33*X^24 +
      11*X^23 + 31*X^22 + 18*X^21 + 45*X^20 + 50*X^19 + 17*X^18 + 6*X^17 + 16*X^16 + 28*X^15 +
      34*X^14 + 53*X^13 + 16*X^12 + 64*X^11 + 50*X^10 + 12*X^9 + 14*X^8 + 28*X^7 + 42*X^6 + 55*X^5 +
      5*X^4 + 38*X^3 + 10*X^2 + 48*X + 27) :=
  sq_step (by norm_num) pSeventeenA2s73 ⟨
    65*X^32 + 9*X^31 + 3*X^30 + 27*X^29 + 27*X^28 + 39*X^27 + 66*X^26 + 56*X^25 + 12*X^24 + 53*X^23 +
      25*X^22 + 31*X^21 + 17*X^20 + 12*X^19 + 53*X^18 + 56*X^17 + 40*X^16 + X^15 + 59*X^14 + 62*X^13 +
      11*X^12 + 49*X^11 + 33*X^10 + X^9 + 24*X^8 + 61*X^7 + 65*X^6 + X^5 + 10*X^4 + 39*X^2 + 55*X +
      32,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s75 : XPow fSeventeenA2 668088463697184
    (41*X^33 + 10*X^32 + 20*X^31 + 33*X^30 + 27*X^29 + 44*X^28 + 54*X^27 + 30*X^26 + 9*X^25 + 24*X^24 +
      11*X^23 + 35*X^22 + 56*X^21 + 18*X^20 + 40*X^19 + 43*X^18 + 55*X^17 + 64*X^16 + 25*X^15 +
      46*X^14 + 63*X^13 + 20*X^12 + 52*X^11 + 10*X^10 + 27*X^9 + 33*X^8 + 17*X^7 + 38*X^6 + 43*X^5 +
      58*X^4 + 58*X^3 + 29*X^2 + 50*X + 34) :=
  sq_step (by norm_num) pSeventeenA2s74 ⟨
    4*X^32 + X^31 + 34*X^30 + 23*X^29 + 61*X^28 + 53*X^27 + 50*X^26 + 5*X^25 + 33*X^24 + 14*X^23 + X^21 +
      62*X^20 + 34*X^19 + 19*X^18 + 10*X^17 + 49*X^16 + 51*X^15 + 3*X^14 + 8*X^13 + 54*X^12 +
      25*X^11 + 66*X^10 + 27*X^9 + 35*X^8 + 9*X^7 + 46*X^6 + 20*X^5 + X^4 + 5*X^3 + 20*X^2 + 30*X +
      16,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s76 : XPow fSeventeenA2 1336176927394368
    (63*X^33 + 43*X^32 + 39*X^31 + 19*X^30 + 13*X^29 + 41*X^28 + 59*X^27 + 22*X^26 + 65*X^25 + 18*X^24 +
      25*X^23 + 10*X^22 + 46*X^21 + 56*X^20 + 10*X^19 + 41*X^18 + 32*X^17 + 26*X^16 + 61*X^15 +
      41*X^14 + 62*X^13 + 50*X^12 + 48*X^11 + 17*X^9 + 35*X^8 + 6*X^7 + 9*X^6 + 62*X^5 + 55*X^4 +
      33*X^3 + 21*X^2 + 20*X + 33) :=
  sq_step (by norm_num) pSeventeenA2s75 ⟨
    6*X^32 + 12*X^31 + 12*X^30 + 32*X^29 + 23*X^28 + 29*X^27 + 48*X^26 + 2*X^25 + 16*X^24 + 66*X^23 +
      60*X^22 + 20*X^21 + 23*X^20 + 60*X^19 + 30*X^18 + 53*X^17 + 41*X^16 + 63*X^15 + 10*X^14 +
      40*X^13 + 52*X^12 + 3*X^11 + 43*X^10 + 37*X^9 + 12*X^8 + 48*X^7 + 27*X^6 + 33*X^5 + 30*X^4 +
      66*X^3 + 44*X^2 + 57*X + 38,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s77 : XPow fSeventeenA2 2672353854788736
    (21*X^33 + X^32 + 23*X^31 + 64*X^30 + 45*X^29 + 34*X^28 + 9*X^27 + 60*X^26 + 55*X^25 + 4*X^24 +
      9*X^23 + 15*X^22 + 32*X^21 + 46*X^20 + 38*X^19 + 15*X^18 + 56*X^17 + 41*X^16 + 9*X^15 +
      11*X^14 + 41*X^13 + 12*X^12 + X^11 + 35*X^10 + 17*X^9 + 13*X^8 + 66*X^7 + 11*X^6 + 4*X^5 +
      28*X^4 + 59*X^3 + 12*X^2 + 8*X + 48) :=
  sq_step (by norm_num) pSeventeenA2s76 ⟨
    16*X^32 + 25*X^31 + 38*X^30 + 17*X^28 + 36*X^27 + 41*X^26 + 66*X^25 + 36*X^24 + 15*X^23 + 44*X^22 +
      65*X^21 + 9*X^20 + 47*X^19 + 55*X^18 + 3*X^17 + 2*X^16 + 26*X^15 + 14*X^14 + 29*X^13 + 12*X^12 +
      66*X^11 + 55*X^10 + 37*X^9 + 7*X^8 + 49*X^7 + 6*X^6 + 8*X^5 + 48*X^4 + 2*X^3 + 3*X^2 + 25*X +
      15,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s78 : XPow fSeventeenA2 5344707709577472
    (51*X^33 + 46*X^32 + 33*X^31 + 51*X^30 + 35*X^29 + 64*X^28 + 41*X^27 + 10*X^26 + 61*X^25 + 7*X^24 +
      32*X^23 + 48*X^22 + 13*X^21 + 32*X^20 + 55*X^19 + 11*X^18 + 46*X^17 + 55*X^16 + 24*X^15 +
      45*X^14 + 25*X^13 + 49*X^12 + 9*X^11 + 57*X^10 + 7*X^9 + 45*X^8 + 31*X^7 + 40*X^6 + 22*X^5 +
      13*X^4 + 41*X^3 + 39*X^2 + 17*X + 41) :=
  sq_step (by norm_num) pSeventeenA2s77 ⟨
    39*X^32 + 16*X^31 + 5*X^30 + 39*X^29 + 53*X^28 + 40*X^27 + 11*X^26 + 25*X^25 + 30*X^24 + 52*X^23 +
      15*X^22 + 62*X^21 + 26*X^20 + 2*X^19 + 62*X^18 + 27*X^17 + 22*X^16 + 34*X^15 + 60*X^14 +
      36*X^13 + 56*X^12 + 61*X^11 + 61*X^10 + 16*X^9 + 21*X^8 + 15*X^7 + 51*X^6 + 60*X^5 + 65*X^4 +
      24*X^3 + 19*X^2 + 65*X + 44,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s79 : XPow fSeventeenA2 5344707709577473
    (12*X^33 + 19*X^32 + 14*X^31 + 32*X^30 + 46*X^29 + 8*X^28 + 26*X^27 + 48*X^26 + 63*X^25 + 55*X^24 +
      46*X^23 + 19*X^22 + 53*X^20 + 9*X^19 + 4*X^18 + 41*X^17 + 10*X^16 + 16*X^15 + 27*X^14 +
      47*X^13 + 60*X^12 + 20*X^11 + 10*X^10 + 44*X^9 + 47*X^8 + 48*X^7 + 35*X^6 + 4*X^5 + 4*X^4 +
      62*X^3 + 12*X^2 + 32*X + 25) :=
  mul_step (by norm_num) pSeventeenA2s78 pSeventeenA21 ⟨
    51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s80 : XPow fSeventeenA2 10689415419154946
    (18*X^33 + 22*X^32 + 8*X^31 + 65*X^30 + 15*X^29 + 45*X^28 + 7*X^27 + 7*X^26 + 64*X^25 + 55*X^24 +
      55*X^23 + 31*X^22 + 56*X^21 + 54*X^20 + 48*X^19 + 3*X^18 + 9*X^17 + 36*X^16 + 30*X^15 +
      50*X^14 + 8*X^13 + 34*X^12 + 30*X^11 + 58*X^10 + 10*X^9 + 39*X^8 + 16*X^7 + 53*X^6 + 27*X^5 +
      45*X^4 + 38*X^3 + 10*X^2 + 59*X + 1) :=
  sq_step (by norm_num) pSeventeenA2s79 ⟨
    10*X^32 + 25*X^31 + 47*X^30 + 63*X^29 + 33*X^28 + 29*X^27 + 33*X^26 + 46*X^25 + 12*X^24 + 31*X^23 +
      42*X^22 + 43*X^21 + 4*X^20 + 50*X^19 + 38*X^18 + X^17 + 38*X^16 + 58*X^15 + 58*X^14 + 28*X^13 +
      33*X^12 + 9*X^11 + 14*X^10 + 2*X^9 + 37*X^8 + 8*X^7 + 45*X^6 + 46*X^5 + 48*X^4 + 33*X^3 +
      22*X^2 + 40*X + 59,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s81 : XPow fSeventeenA2 10689415419154947
    (10*X^33 + 7*X^32 + 48*X^31 + 10*X^30 + 15*X^29 + 19*X^28 + 56*X^27 + 20*X^26 + 59*X^25 + 4*X^24 +
      50*X^23 + 66*X^22 + 23*X^21 + 22*X^19 + 6*X^18 + 35*X^17 + 29*X^16 + 24*X^15 + 56*X^14 +
      53*X^13 + 48*X^12 + 41*X^11 + 15*X^10 + 15*X^9 + 65*X^8 + 44*X^7 + 4*X^6 + 30*X^5 + 21*X^4 +
      26*X^3 + 6*X^2 + 53*X + 64) :=
  mul_step (by norm_num) pSeventeenA2s80 pSeventeenA21 ⟨
    18,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s82 : XPow fSeventeenA2 21378830838309894
    (30*X^33 + 23*X^32 + 8*X^31 + 34*X^30 + 66*X^29 + 46*X^28 + 42*X^27 + 28*X^26 + 6*X^25 + 64*X^24 +
      24*X^23 + 24*X^22 + 19*X^21 + 33*X^20 + 16*X^19 + 7*X^18 + 22*X^17 + 21*X^16 + 10*X^15 +
      9*X^14 + 27*X^13 + 4*X^12 + 42*X^11 + 15*X^10 + 7*X^9 + 3*X^8 + 15*X^7 + 40*X^6 + 3*X^5 +
      28*X^4 + 17*X^3 + 47*X^2 + 33*X + 29) :=
  sq_step (by norm_num) pSeventeenA2s81 ⟨
    33*X^32 + 51*X^31 + 24*X^30 + 18*X^29 + 38*X^28 + 36*X^27 + 29*X^26 + 28*X^25 + 28*X^24 + 41*X^23 +
      8*X^22 + 63*X^21 + 35*X^20 + 64*X^19 + 29*X^18 + 52*X^17 + 41*X^16 + 56*X^15 + 10*X^14 +
      30*X^13 + 17*X^12 + 33*X^11 + 61*X^10 + 24*X^9 + 2*X^8 + 53*X^7 + 61*X^6 + 65*X^5 + 13*X^4 +
      18*X^3 + 10*X^2 + 35*X + 14,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s83 : XPow fSeventeenA2 42757661676619788
    (24*X^33 + 39*X^32 + 4*X^31 + 48*X^30 + 59*X^29 + 24*X^28 + 2*X^27 + 61*X^26 + 8*X^25 + 30*X^24 +
      6*X^23 + 22*X^22 + 40*X^21 + 51*X^20 + 40*X^19 + 18*X^18 + 42*X^17 + 46*X^16 + 34*X^15 +
      54*X^14 + 45*X^13 + 29*X^12 + 57*X^11 + 61*X^10 + 59*X^9 + 32*X^8 + 8*X^7 + 14*X^6 + 14*X^5 +
      8*X^4 + 28*X^3 + 35*X^2 + 42*X + 34) :=
  sq_step (by norm_num) pSeventeenA2s82 ⟨
    29*X^32 + 43*X^31 + 37*X^30 + 16*X^29 + 14*X^28 + 11*X^27 + 51*X^26 + 8*X^25 + 40*X^24 + 44*X^23 +
      23*X^22 + X^21 + 41*X^20 + 9*X^19 + 59*X^18 + 60*X^17 + 20*X^16 + 48*X^15 + 41*X^14 + 24*X^13 +
      65*X^12 + 25*X^11 + 45*X^10 + 62*X^9 + 23*X^8 + 52*X^7 + 5*X^6 + 22*X^5 + X^4 + 49*X^3 +
      18*X^2 + 20*X + 18,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s84 : XPow fSeventeenA2 42757661676619789
    (23*X^33 + 25*X^32 + 3*X^31 + 30*X^30 + 51*X^29 + 18*X^28 + 37*X^27 + 61*X^26 + 13*X^25 + 5*X^24 +
      25*X^23 + 31*X^22 + 32*X^21 + 43*X^20 + 21*X^19 + 38*X^18 + 55*X^16 + 64*X^15 + 42*X^14 +
      32*X^13 + 14*X^12 + 16*X^11 + 21*X^10 + 51*X^8 + 2*X^7 + 28*X^6 + 55*X^5 + 50*X^4 + 34*X^3 +
      16*X^2 + 14*X + 63) :=
  mul_step (by norm_num) pSeventeenA2s83 pSeventeenA21 ⟨
    24,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s85 : XPow fSeventeenA2 85515323353239578
    (29*X^33 + 6*X^32 + X^31 + 51*X^30 + 16*X^29 + 42*X^28 + 28*X^27 + 56*X^26 + 66*X^25 + 12*X^24 +
      55*X^23 + 53*X^22 + 12*X^21 + 66*X^20 + 22*X^19 + 3*X^18 + 28*X^17 + 35*X^16 + X^15 + 43*X^14 +
      48*X^13 + 33*X^12 + 21*X^11 + 53*X^10 + 3*X^9 + 5*X^8 + 17*X^7 + 9*X^6 + 39*X^5 + 4*X^4 +
      30*X^2 + 34*X + 10) :=
  sq_step (by norm_num) pSeventeenA2s84 ⟨
    60*X^32 + 38*X^31 + 42*X^30 + 66*X^29 + 19*X^28 + 34*X^27 + 28*X^26 + 58*X^25 + 34*X^24 + 39*X^23 +
      39*X^22 + 8*X^21 + 65*X^20 + 34*X^19 + 6*X^18 + 47*X^17 + 8*X^16 + 45*X^15 + 35*X^14 + 41*X^13 +
      27*X^12 + 17*X^11 + 60*X^10 + 49*X^9 + 53*X^8 + 4*X^7 + 12*X^6 + 52*X^5 + 52*X^4 + 33*X^3 +
      48*X^2 + 16*X + 36,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s86 : XPow fSeventeenA2 171030646706479156
    (55*X^33 + 6*X^32 + 7*X^31 + 27*X^30 + 39*X^29 + 20*X^28 + 51*X^27 + 34*X^26 + 19*X^25 + 60*X^24 +
      60*X^22 + 39*X^21 + 53*X^20 + 16*X^19 + 29*X^18 + 21*X^17 + 28*X^16 + 37*X^15 + 59*X^14 +
      45*X^13 + 59*X^12 + 18*X^11 + 66*X^10 + 58*X^9 + 65*X^8 + 32*X^7 + X^6 + 58*X^5 + 2*X^4 +
      35*X^3 + 64*X^2 + 52*X + 43) :=
  sq_step (by norm_num) pSeventeenA2s85 ⟨
    37*X^32 + 33*X^31 + 29*X^30 + 18*X^29 + 38*X^28 + 52*X^27 + 57*X^26 + 48*X^25 + 64*X^24 + 21*X^23 +
      62*X^22 + 8*X^21 + 53*X^20 + 41*X^19 + X^18 + 9*X^17 + 55*X^16 + 30*X^15 + 54*X^14 + 2*X^13 +
      66*X^12 + 64*X^11 + 37*X^10 + 11*X^9 + 15*X^8 + 21*X^7 + 63*X^6 + 43*X^5 + 31*X^4 + 21*X^3 +
      51*X^2 + 48*X + 7,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s87 : XPow fSeventeenA2 342061293412958312
    (56*X^33 + 26*X^32 + 26*X^31 + 33*X^30 + 9*X^29 + 31*X^28 + 57*X^27 + 9*X^26 + 6*X^25 + 29*X^24 +
      30*X^23 + 29*X^22 + 65*X^21 + 63*X^20 + 28*X^19 + 59*X^18 + 44*X^17 + 25*X^16 + 24*X^15 + X^14 +
      59*X^13 + 19*X^12 + 57*X^11 + 64*X^10 + 49*X^9 + 61*X^8 + 57*X^7 + 65*X^6 + 58*X^5 + 9*X^4 +
      45*X^3 + 49*X^2 + 9*X + 61) :=
  sq_step (by norm_num) pSeventeenA2s86 ⟨
    10*X^32 + 28*X^31 + 20*X^30 + 37*X^29 + 52*X^28 + 44*X^27 + 48*X^26 + 20*X^25 + 42*X^24 + 8*X^23 +
      38*X^22 + 40*X^21 + 22*X^20 + 53*X^19 + 39*X^18 + 8*X^17 + 16*X^16 + 26*X^15 + 36*X^14 +
      56*X^13 + 6*X^12 + 62*X^11 + 51*X^10 + 56*X^9 + 18*X^8 + 51*X^7 + 19*X^6 + 16*X^5 + 21*X^4 +
      2*X^3 + 34*X^2 + 5*X + 8,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s88 : XPow fSeventeenA2 342061293412958313
    (11*X^33 + 8*X^32 + 62*X^31 + 53*X^30 + 27*X^29 + 5*X^28 + 20*X^27 + 18*X^26 + 34*X^25 + 50*X^24 +
      36*X^23 + 44*X^22 + 41*X^21 + 35*X^20 + 66*X^19 + 57*X^18 + 7*X^17 + 6*X^16 + 2*X^15 + 52*X^14 +
      26*X^13 + 46*X^12 + 26*X^11 + 5*X^10 + 31*X^9 + X^8 + 37*X^7 + 46*X^6 + 7*X^5 + 7*X^4 + 2*X^3 +
      60*X^2 + 59*X + 13) :=
  mul_step (by norm_num) pSeventeenA2s87 pSeventeenA21 ⟨
    56,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s89 : XPow fSeventeenA2 684122586825916626
    (43*X^32 + 16*X^31 + X^30 + 25*X^29 + 47*X^28 + 43*X^27 + 28*X^26 + 26*X^25 + 2*X^24 + 34*X^23 +
      50*X^22 + 10*X^20 + 44*X^19 + 37*X^18 + 51*X^17 + 38*X^16 + 60*X^15 + 20*X^14 + 11*X^13 +
      19*X^12 + 47*X^11 + 31*X^10 + 49*X^9 + 25*X^8 + 63*X^7 + 29*X^6 + 40*X^5 + 30*X^4 + 20*X^3 +
      41*X^2 + 16*X + 19) :=
  sq_step (by norm_num) pSeventeenA2s88 ⟨
    54*X^32 + 6*X^31 + 14*X^30 + 65*X^29 + 25*X^28 + 32*X^27 + 49*X^26 + 36*X^25 + 41*X^23 + 50*X^22 +
      16*X^21 + 57*X^20 + 38*X^19 + 51*X^18 + 64*X^17 + 57*X^16 + 20*X^15 + 14*X^14 + 47*X^13 +
      64*X^12 + 25*X^11 + 54*X^10 + 34*X^9 + 65*X^8 + 45*X^7 + 35*X^6 + 8*X^5 + 57*X^4 + 44*X^3 +
      38*X^2 + 52*X + 29,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s90 : XPow fSeventeenA2 684122586825916627
    (43*X^33 + 16*X^32 + X^31 + 25*X^30 + 47*X^29 + 43*X^28 + 28*X^27 + 26*X^26 + 2*X^25 + 34*X^24 +
      50*X^23 + 10*X^21 + 44*X^20 + 37*X^19 + 51*X^18 + 38*X^17 + 60*X^16 + 20*X^15 + 11*X^14 +
      19*X^13 + 47*X^12 + 31*X^11 + 49*X^10 + 25*X^9 + 63*X^8 + 29*X^7 + 40*X^6 + 30*X^5 + 20*X^4 +
      41*X^3 + 16*X^2 + 19*X) :=
  mul_step (by norm_num) pSeventeenA2s89 pSeventeenA21 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s91 : XPow fSeventeenA2 1368245173651833254
    (51*X^33 + 15*X^32 + 13*X^31 + 38*X^30 + 56*X^29 + 37*X^28 + 18*X^27 + 43*X^26 + 59*X^25 + 52*X^24 +
      53*X^23 + 49*X^22 + 38*X^21 + 60*X^20 + X^19 + 61*X^18 + 60*X^17 + 21*X^16 + 52*X^15 + X^14 +
      49*X^13 + 10*X^12 + 30*X^11 + 47*X^10 + 34*X^9 + 10*X^8 + 54*X^7 + 54*X^6 + 57*X^5 + 28*X^4 +
      65*X^3 + 64*X^2 + 43*X + 17) :=
  sq_step (by norm_num) pSeventeenA2s90 ⟨
    40*X^32 + 54*X^31 + 6*X^30 + 23*X^29 + 38*X^28 + 20*X^27 + 57*X^26 + 27*X^25 + 27*X^24 + 52*X^23 +
      61*X^22 + 42*X^21 + 25*X^20 + 30*X^19 + 35*X^18 + 49*X^17 + 52*X^16 + 45*X^15 + 56*X^14 +
      22*X^13 + 54*X^12 + 29*X^11 + 31*X^10 + 19*X^9 + 6*X^8 + 8*X^7 + 43*X^6 + 57*X^5 + 2*X^4 +
      42*X^3 + 46*X^2 + 51*X + 32,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s92 : XPow fSeventeenA2 2736490347303666508
    (26*X^33 + 27*X^32 + 20*X^31 + 25*X^30 + 48*X^29 + 56*X^28 + 38*X^27 + 26*X^26 + 37*X^25 + 37*X^24 +
      45*X^23 + 51*X^21 + 15*X^20 + 64*X^19 + 42*X^18 + 66*X^17 + 34*X^16 + 8*X^15 + 50*X^14 +
      56*X^13 + 17*X^12 + 25*X^11 + 26*X^10 + 13*X^9 + 21*X^8 + 32*X^7 + 52*X^6 + 31*X^5 + 56*X^4 +
      53*X^3 + 26*X^2 + 50*X + 7) :=
  sq_step (by norm_num) pSeventeenA2s91 ⟨
    55*X^32 + 64*X^31 + 35*X^30 + 22*X^29 + 50*X^28 + 60*X^27 + 4*X^26 + 31*X^25 + 58*X^24 + 66*X^23 +
      27*X^22 + 10*X^21 + 41*X^20 + 65*X^19 + 59*X^18 + 65*X^17 + 18*X^16 + 50*X^15 + 64*X^14 +
      45*X^13 + 11*X^12 + 62*X^11 + 43*X^10 + 64*X^9 + 29*X^8 + 34*X^7 + 4*X^6 + 18*X^5 + 31*X^4 +
      14*X^3 + 5*X^2 + 12*X + 17,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s93 : XPow fSeventeenA2 5472980694607333016
    (22*X^33 + 25*X^32 + 20*X^31 + 49*X^30 + 58*X^29 + 45*X^28 + 5*X^27 + 59*X^26 + 42*X^24 + 11*X^23 +
      63*X^22 + 25*X^21 + 22*X^20 + 32*X^19 + 52*X^18 + 49*X^17 + 24*X^16 + 13*X^15 + 9*X^14 +
      10*X^13 + 65*X^12 + 52*X^11 + 48*X^10 + 17*X^9 + 41*X^8 + X^7 + 27*X^6 + 58*X^5 + 8*X^4 +
      60*X^3 + 14*X^2 + 38*X + 43) :=
  sq_step (by norm_num) pSeventeenA2s92 ⟨
    6*X^32 + 60*X^31 + 9*X^30 + 20*X^29 + 31*X^28 + 56*X^27 + 26*X^26 + 31*X^25 + 3*X^24 + 42*X^23 +
      51*X^22 + 45*X^21 + 2*X^20 + 30*X^19 + 8*X^18 + 22*X^17 + 11*X^16 + 63*X^15 + 63*X^14 +
      44*X^13 + 54*X^12 + 51*X^11 + 38*X^10 + 9*X^9 + 37*X^8 + 37*X^7 + 33*X^6 + 24*X^5 + 53*X^4 +
      11*X^3 + 50*X^2 + 40*X + 36,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s94 : XPow fSeventeenA2 5472980694607333017
    (55*X^33 + 56*X^32 + 58*X^31 + 37*X^30 + 53*X^29 + 42*X^28 + 37*X^27 + 43*X^26 + 32*X^25 + 38*X^24 +
      49*X^23 + 66*X^21 + 18*X^20 + 38*X^19 + 23*X^18 + 60*X^17 + 49*X^16 + 7*X^15 + 24*X^14 +
      51*X^13 + 7*X^12 + 57*X^11 + 38*X^10 + 34*X^9 + 46*X^8 + 16*X^7 + 15*X^6 + 12*X^5 + 2*X^4 +
      41*X^3 + 3*X^2 + 47*X + 41) :=
  mul_step (by norm_num) pSeventeenA2s93 pSeventeenA21 ⟨
    22,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s95 : XPow fSeventeenA2 10945961389214666034
    (52*X^33 + 23*X^32 + 23*X^31 + 62*X^30 + 14*X^29 + 11*X^28 + 36*X^27 + 44*X^26 + 58*X^25 + 27*X^24 +
      56*X^23 + 24*X^22 + 45*X^21 + 53*X^20 + 56*X^19 + 24*X^18 + 45*X^17 + 38*X^16 + 36*X^15 +
      38*X^14 + 51*X^13 + 57*X^12 + 9*X^11 + 30*X^10 + 50*X^9 + 18*X^8 + 24*X^7 + 49*X^6 + 39*X^5 +
      60*X^4 + 9*X^3 + 20*X^2 + 63*X + 49) :=
  sq_step (by norm_num) pSeventeenA2s94 ⟨
    10*X^32 + 34*X^31 + 16*X^30 + 25*X^29 + 27*X^28 + 66*X^27 + 13*X^26 + 18*X^25 + 15*X^24 + 66*X^23 +
      30*X^22 + 30*X^21 + 26*X^20 + 14*X^19 + 16*X^18 + 35*X^17 + 39*X^16 + 19*X^15 + 27*X^14 +
      62*X^13 + 14*X^12 + 30*X^11 + 14*X^10 + 29*X^9 + 65*X^8 + 4*X^7 + X^6 + 21*X^5 + 23*X^4 +
      23*X^3 + 24*X^2 + 50*X + 10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s96 : XPow fSeventeenA2 10945961389214666035
    (33*X^33 + 35*X^32 + 65*X^31 + 7*X^30 + 36*X^29 + 26*X^28 + 59*X^27 + 50*X^26 + 46*X^25 + 65*X^24 +
      64*X^23 + 59*X^22 + 23*X^21 + 29*X^20 + 64*X^19 + 14*X^18 + 50*X^17 + 48*X^16 + 15*X^15 +
      11*X^14 + 30*X^13 + 61*X^12 + 33*X^11 + 57*X^10 + 38*X^9 + 39*X^8 + 23*X^7 + 47*X^6 + 39*X^5 +
      12*X^4 + 29*X^3 + 29*X^2 + 28*X + 36) :=
  mul_step (by norm_num) pSeventeenA2s95 pSeventeenA21 ⟨
    52,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s97 : XPow fSeventeenA2 21891922778429332070
    (4*X^33 + 59*X^32 + 56*X^31 + 40*X^30 + 32*X^29 + 63*X^28 + 43*X^27 + 56*X^26 + 28*X^25 + 16*X^24 +
      45*X^23 + 11*X^22 + 64*X^21 + 26*X^20 + 29*X^19 + 56*X^18 + 57*X^17 + 13*X^16 + 44*X^15 +
      29*X^14 + 8*X^13 + 17*X^12 + 21*X^11 + 27*X^10 + 40*X^9 + 18*X^8 + 17*X^7 + 63*X^6 + 11*X^5 +
      2*X^4 + 43*X^3 + 60*X^2 + 43*X + 32) :=
  sq_step (by norm_num) pSeventeenA2s96 ⟨
    17*X^32 + 43*X^31 + 10*X^30 + 14*X^29 + 38*X^28 + 34*X^27 + 9*X^26 + 50*X^25 + 14*X^24 + 12*X^23 +
      59*X^22 + 6*X^21 + 6*X^20 + 26*X^19 + 63*X^18 + 31*X^17 + 45*X^16 + 46*X^15 + 36*X^14 + 5*X^13 +
      22*X^12 + 61*X^11 + 3*X^10 + 7*X^9 + 14*X^8 + 46*X^7 + 39*X^6 + 44*X^5 + 7*X^4 + 15*X^3 +
      32*X^2 + 48*X + 13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s98 : XPow fSeventeenA2 21891922778429332071
    (34*X^33 + 26*X^32 + 66*X^31 + 16*X^30 + 34*X^29 + X^28 + 52*X^27 + 48*X^26 + 2*X^25 + 56*X^24 +
      45*X^23 + 29*X^22 + 34*X^21 + 63*X^20 + 23*X^19 + 34*X^18 + 50*X^17 + 14*X^16 + 53*X^15 +
      41*X^14 + 51*X^13 + 25*X^12 + 53*X^11 + 56*X^10 + 35*X^9 + 13*X^8 + 61*X^7 + 58*X^6 + 21*X^5 +
      2*X^4 + 4*X^3 + 61*X^2 + 51*X + 44) :=
  mul_step (by norm_num) pSeventeenA2s97 pSeventeenA21 ⟨
    4,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s99 : XPow fSeventeenA2 43783845556858664142
    (53*X^33 + 30*X^32 + 66*X^31 + 15*X^30 + 66*X^29 + 62*X^28 + 55*X^27 + 18*X^26 + 48*X^25 + 13*X^24 +
      58*X^23 + 15*X^22 + 12*X^21 + 58*X^20 + 45*X^19 + 19*X^18 + X^17 + 37*X^16 + 52*X^15 + 66*X^14 +
      54*X^13 + 54*X^12 + 7*X^11 + 54*X^10 + 60*X^9 + 30*X^8 + 29*X^7 + 40*X^6 + 38*X^5 + 52*X^4 +
      41*X^3 + 25*X^2 + 9*X + 32) :=
  sq_step (by norm_num) pSeventeenA2s98 ⟨
    17*X^32 + 37*X^31 + 65*X^30 + 44*X^29 + 9*X^28 + 28*X^27 + 14*X^26 + 17*X^25 + 34*X^24 + 47*X^23 +
      29*X^22 + 17*X^21 + 34*X^19 + 3*X^18 + 3*X^17 + 37*X^16 + 65*X^15 + 53*X^14 + 8*X^13 + 24*X^12 +
      4*X^11 + 58*X^10 + 57*X^9 + 33*X^8 + 25*X^7 + 49*X^6 + 61*X^5 + 22*X^4 + 26*X^3 + 18*X^2 +
      38*X + 34,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s100 : XPow fSeventeenA2 87567691113717328284
    (17*X^33 + 27*X^32 + 44*X^31 + 63*X^30 + 21*X^29 + 20*X^28 + 2*X^27 + 21*X^26 + 54*X^25 + 37*X^24 +
      19*X^23 + 20*X^22 + 24*X^21 + 3*X^20 + 57*X^19 + 40*X^18 + 53*X^17 + 34*X^16 + 52*X^15 +
      26*X^14 + 21*X^13 + 21*X^12 + 36*X^11 + 26*X^10 + 22*X^9 + 54*X^8 + 13*X^7 + 54*X^6 + 13*X^5 +
      62*X^4 + 14*X^3 + 56*X^2 + 55*X + 23) :=
  sq_step (by norm_num) pSeventeenA2s99 ⟨
    62*X^32 + 12*X^31 + 53*X^30 + 21*X^29 + 46*X^28 + 55*X^27 + 17*X^26 + 24*X^25 + 51*X^24 + 4*X^23 +
      43*X^22 + 40*X^21 + 63*X^20 + 60*X^19 + 23*X^18 + 5*X^17 + 26*X^16 + 49*X^15 + 11*X^14 +
      59*X^13 + 29*X^12 + 47*X^11 + 7*X^10 + 56*X^9 + 65*X^8 + 37*X^7 + 24*X^6 + 17*X^5 + 49*X^4 +
      10*X^3 + 41*X^2 + 30*X + 43,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s101 : XPow fSeventeenA2 175135382227434656568
    (42*X^33 + 18*X^32 + 39*X^31 + 35*X^30 + 50*X^28 + 52*X^27 + 63*X^26 + 14*X^25 + 19*X^24 + 47*X^23 +
      54*X^22 + 28*X^21 + 45*X^20 + 27*X^19 + 51*X^18 + 11*X^17 + 11*X^16 + 43*X^15 + 25*X^14 +
      17*X^13 + X^12 + 13*X^11 + 41*X^10 + 14*X^9 + 44*X^8 + 59*X^7 + 46*X^6 + 8*X^5 + 22*X^4 +
      16*X^3 + 57*X^2 + 17*X + 48) :=
  sq_step (by norm_num) pSeventeenA2s100 ⟨
    21*X^32 + 33*X^31 + 2*X^30 + 6*X^29 + 33*X^28 + 35*X^27 + 40*X^26 + 35*X^25 + 13*X^24 + 11*X^23 +
      8*X^22 + 65*X^21 + 31*X^20 + 65*X^19 + 16*X^18 + 57*X^17 + 7*X^16 + 19*X^15 + 9*X^14 + 60*X^13 +
      60*X^12 + 30*X^11 + 52*X^10 + 14*X^9 + 52*X^8 + 38*X^7 + 35*X^6 + 62*X^5 + 62*X^4 + 5*X^3 +
      9*X^2 + 45*X + 5,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s102 : XPow fSeventeenA2 350270764454869313136
    (6*X^33 + 58*X^32 + 11*X^31 + 21*X^30 + 59*X^29 + 33*X^28 + 37*X^27 + 22*X^26 + 33*X^25 + 55*X^24 +
      57*X^23 + 45*X^22 + 23*X^21 + 36*X^20 + 4*X^19 + 2*X^18 + 65*X^17 + 4*X^16 + 5*X^15 + 37*X^14 +
      6*X^13 + 55*X^12 + 63*X^11 + 11*X^10 + 12*X^9 + 28*X^8 + 51*X^7 + 41*X^6 + 36*X^5 + 22*X^4 +
      31*X^3 + 57*X^2 + 61*X + 51) :=
  sq_step (by norm_num) pSeventeenA2s101 ⟨
    22*X^32 + X^31 + 62*X^30 + 5*X^29 + 9*X^28 + 24*X^27 + 5*X^26 + 41*X^25 + 64*X^24 + 32*X^22 + 8*X^21 +
      54*X^20 + 19*X^19 + 42*X^18 + 10*X^17 + 28*X^16 + 28*X^15 + 24*X^14 + 14*X^13 + 7*X^12 +
      34*X^11 + 23*X^10 + 35*X^9 + 2*X^8 + 51*X^7 + 51*X^6 + 43*X^5 + 27*X^4 + 26*X^3 + 64*X^2 +
      59*X + 51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s103 : XPow fSeventeenA2 700541528909738626272
    (11*X^33 + 31*X^32 + 47*X^31 + 50*X^30 + 64*X^29 + 17*X^27 + 2*X^26 + 6*X^25 + 17*X^24 + 27*X^23 +
      60*X^22 + 6*X^21 + 64*X^20 + 25*X^19 + 21*X^18 + 57*X^16 + 6*X^14 + 29*X^13 + 25*X^12 +
      65*X^11 + 43*X^10 + 48*X^9 + 11*X^8 + 58*X^7 + 29*X^6 + 44*X^5 + 51*X^4 + 66*X^3 + 6*X^2 +
      56*X + 65) :=
  sq_step (by norm_num) pSeventeenA2s102 ⟨
    36*X^32 + 2*X^31 + 31*X^30 + 29*X^29 + 57*X^28 + 9*X^27 + 57*X^26 + 6*X^25 + 49*X^24 + 58*X^23 +
      24*X^22 + 58*X^21 + 10*X^20 + 62*X^19 + 45*X^18 + 5*X^17 + 17*X^16 + 31*X^15 + 60*X^14 +
      9*X^13 + 64*X^12 + 35*X^11 + 39*X^10 + 36*X^9 + 34*X^8 + 22*X^7 + 19*X^6 + 66*X^5 + 64*X^4 +
      37*X^3 + 59*X^2 + 44*X + 7,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s104 : XPow fSeventeenA2 700541528909738626273
    (46*X^33 + 65*X^32 + 21*X^31 + 20*X^30 + 4*X^29 + 2*X^28 + 58*X^27 + 61*X^26 + 12*X^25 + 7*X^24 +
      53*X^23 + 27*X^22 + 19*X^21 + 18*X^20 + 14*X^19 + 54*X^18 + 8*X^17 + 18*X^16 + 5*X^15 +
      36*X^14 + 18*X^13 + 9*X^12 + 14*X^11 + 25*X^10 + 41*X^9 + 47*X^8 + 57*X^7 + 56*X^6 + 53*X^5 +
      37*X^4 + 53*X^3 + 5*X^2 + 54) :=
  mul_step (by norm_num) pSeventeenA2s103 pSeventeenA21 ⟨
    11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s105 : XPow fSeventeenA2 1401083057819477252546
    (39*X^33 + 61*X^32 + 11*X^31 + 29*X^30 + 40*X^29 + X^28 + 32*X^27 + 66*X^26 + X^25 + 30*X^24 +
      57*X^23 + 44*X^22 + 33*X^21 + 15*X^20 + 6*X^19 + 40*X^18 + 46*X^17 + 14*X^16 + 49*X^15 +
      65*X^14 + 6*X^13 + 50*X^12 + 20*X^11 + 24*X^10 + 27*X^9 + 40*X^8 + 57*X^7 + 37*X^6 + 26*X^5 +
      10*X^4 + 14*X^3 + 49*X^2 + 49*X + 3) :=
  sq_step (by norm_num) pSeventeenA2s104 ⟨
    39*X^32 + 58*X^31 + 8*X^30 + 17*X^29 + 30*X^28 + 46*X^27 + 9*X^26 + 4*X^25 + 8*X^24 + 13*X^23 +
      51*X^22 + 39*X^21 + X^20 + 38*X^19 + 43*X^18 + 15*X^17 + 36*X^16 + 47*X^15 + 18*X^14 + 40*X^13 +
      64*X^12 + 22*X^11 + 20*X^10 + 34*X^9 + 32*X^8 + 56*X^7 + 45*X^6 + 19*X^5 + 56*X^4 + 44*X^3 +
      62*X^2 + 19*X + 58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s106 : XPow fSeventeenA2 2802166115638954505092
    (54*X^33 + 66*X^32 + 29*X^31 + 7*X^30 + 6*X^29 + 43*X^28 + 55*X^27 + 28*X^26 + 14*X^25 + 57*X^24 +
      7*X^23 + 34*X^22 + 49*X^21 + 41*X^20 + 2*X^18 + 57*X^17 + 21*X^16 + 31*X^15 + 11*X^14 +
      20*X^13 + 53*X^12 + 28*X^11 + 18*X^10 + 2*X^9 + 9*X^8 + 7*X^7 + 9*X^6 + 55*X^5 + 24*X^4 +
      26*X^3 + 34*X^2 + 27*X + 39) :=
  sq_step (by norm_num) pSeventeenA2s105 ⟨
    47*X^32 + 59*X^31 + 22*X^30 + 13*X^29 + 45*X^28 + 60*X^27 + 5*X^26 + 26*X^25 + 18*X^24 + 6*X^23 +
      55*X^22 + 15*X^21 + 4*X^20 + 48*X^19 + 25*X^18 + 66*X^17 + 21*X^16 + 30*X^15 + 51*X^14 +
      52*X^13 + 27*X^12 + 28*X^11 + 8*X^10 + 34*X^9 + 41*X^8 + 23*X^7 + 41*X^6 + 8*X^5 + 63*X^3 +
      3*X^2 + 23*X + 21,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s107 : XPow fSeventeenA2 2802166115638954505093
    (30*X^33 + 26*X^32 + 23*X^31 + 58*X^30 + 20*X^29 + 24*X^28 + 41*X^27 + 16*X^26 + 2*X^25 + 55*X^24 +
      24*X^23 + 12*X^22 + 15*X^21 + 57*X^20 + 59*X^19 + 48*X^18 + 18*X^17 + 28*X^16 + 30*X^14 +
      43*X^13 + 15*X^12 + 34*X^11 + 17*X^10 + 4*X^9 + 20*X^8 + 49*X^7 + 53*X^6 + 46*X^5 + 42*X^4 +
      15*X^3 + 2*X^2 + 61*X + 58) :=
  mul_step (by norm_num) pSeventeenA2s106 pSeventeenA21 ⟨
    54,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s108 : XPow fSeventeenA2 5604332231277909010186
    (37*X^33 + 39*X^32 + 17*X^31 + 20*X^30 + 54*X^29 + 9*X^28 + 27*X^27 + 16*X^26 + 28*X^25 + 64*X^24 +
      41*X^23 + 9*X^22 + 56*X^21 + 3*X^20 + 46*X^18 + 3*X^17 + 34*X^16 + 10*X^15 + 64*X^14 + 46*X^13 +
      8*X^12 + 45*X^11 + 24*X^10 + 32*X^9 + 62*X^8 + 64*X^7 + 38*X^6 + 7*X^5 + 44*X^4 + 7*X^3 +
      13*X^2 + 59*X + 59) :=
  sq_step (by norm_num) pSeventeenA2s107 ⟨
    29*X^32 + 22*X^31 + 26*X^30 + 48*X^29 + 56*X^28 + 4*X^27 + 55*X^26 + 20*X^25 + 65*X^24 + 54*X^23 +
      32*X^22 + 50*X^21 + 64*X^20 + 36*X^19 + 31*X^18 + 2*X^17 + 60*X^16 + 33*X^15 + X^14 + 64*X^13 +
      22*X^12 + 20*X^11 + 53*X^10 + 15*X^9 + 27*X^8 + 23*X^7 + 62*X^6 + 50*X^5 + 57*X^4 + 23*X^3 +
      23*X^2 + 36*X + 65,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s109 : XPow fSeventeenA2 11208664462555818020372
    (43*X^33 + 65*X^32 + 37*X^31 + 49*X^30 + 48*X^29 + 45*X^28 + 66*X^27 + 9*X^26 + 44*X^25 + 62*X^24 +
      57*X^23 + 62*X^22 + 18*X^21 + 64*X^20 + 49*X^19 + 47*X^18 + 34*X^17 + 27*X^16 + 37*X^15 +
      37*X^14 + 26*X^13 + 47*X^12 + 66*X^11 + 22*X^10 + 54*X^9 + 32*X^8 + 35*X^7 + 3*X^6 + 7*X^5 +
      28*X^4 + 35*X^3 + 30) :=
  sq_step (by norm_num) pSeventeenA2s108 ⟨
    29*X^32 + 8*X^31 + 66*X^30 + 43*X^29 + 9*X^28 + 6*X^27 + 62*X^26 + 29*X^25 + 40*X^24 + 23*X^23 +
      18*X^22 + 53*X^21 + 14*X^20 + 44*X^19 + 40*X^18 + 16*X^17 + 17*X^16 + 30*X^15 + 54*X^14 +
      52*X^13 + 51*X^12 + 63*X^11 + 35*X^10 + 40*X^9 + 17*X^8 + 54*X^7 + 58*X^5 + 65*X^4 + 20*X^3 +
      8*X^2 + 16*X + 3,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s110 : XPow fSeventeenA2 22417328925111636040744
    (40*X^33 + 50*X^32 + 8*X^31 + 20*X^30 + 2*X^29 + 4*X^28 + 62*X^27 + 32*X^26 + 23*X^25 + 49*X^24 +
      4*X^23 + 48*X^22 + 18*X^21 + 13*X^20 + 61*X^19 + 20*X^18 + 45*X^17 + 35*X^16 + 38*X^15 +
      64*X^14 + 12*X^13 + 58*X^12 + 47*X^11 + 21*X^10 + 22*X^9 + 27*X^8 + 29*X^7 + 50*X^6 + 20*X^5 +
      17*X^4 + 26*X^3 + 62*X^2 + 29*X + 6) :=
  sq_step (by norm_num) pSeventeenA2s109 ⟨
    40*X^32 + 47*X^31 + 63*X^30 + 12*X^29 + 8*X^28 + 27*X^27 + X^26 + 46*X^25 + 60*X^24 + 59*X^23 +
      49*X^22 + 58*X^21 + 30*X^20 + 14*X^19 + 55*X^18 + 47*X^17 + 4*X^16 + 19*X^15 + 59*X^14 +
      31*X^13 + 52*X^12 + 48*X^11 + 61*X^10 + 54*X^9 + 43*X^8 + 50*X^7 + 26*X^6 + 52*X^5 + 49*X^4 +
      57*X^3 + 36*X^2 + 7*X + 4,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s111 : XPow fSeventeenA2 22417328925111636040745
    (X^33 + 43*X^32 + 12*X^31 + 43*X^30 + 49*X^29 + 44*X^28 + 59*X^27 + 22*X^26 + 43*X^25 + 47*X^24 +
      53*X^23 + 3*X^22 + 26*X^21 + 66*X^20 + 25*X^19 + 16*X^18 + 3*X^17 + 6*X^16 + 36*X^15 + 7*X^14 +
      63*X^13 + 20*X^12 + 13*X^11 + 48*X^10 + 63*X^9 + 56*X^8 + 30*X^7 + 21*X^6 + 6*X^5 + 18*X^4 +
      38*X^3 + 8*X^2 + 62*X + 38) :=
  mul_step (by norm_num) pSeventeenA2s110 pSeventeenA21 ⟨
    40,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s112 : XPow fSeventeenA2 44834657850223272081490
    (51*X^33 + 11*X^32 + 62*X^31 + 65*X^30 + X^29 + 34*X^28 + 52*X^27 + 29*X^26 + 20*X^25 + 32*X^24 +
      2*X^23 + 15*X^22 + 47*X^21 + 14*X^20 + 22*X^19 + 2*X^18 + 37*X^17 + 34*X^16 + 54*X^15 +
      33*X^14 + 52*X^13 + 45*X^12 + 45*X^11 + 19*X^10 + 50*X^9 + 49*X^8 + 56*X^7 + 12*X^6 + 39*X^5 +
      45*X^4 + 52*X^3 + 30*X^2 + 23*X + 5) :=
  sq_step (by norm_num) pSeventeenA2s111 ⟨
    X^32 + 63*X^31 + 48*X^30 + 17*X^29 + 10*X^28 + 21*X^27 + 8*X^26 + 55*X^25 + 44*X^24 + X^23 + 5*X^22 +
      60*X^21 + 45*X^20 + 21*X^19 + 23*X^18 + 12*X^17 + 53*X^16 + 59*X^15 + 58*X^14 + 45*X^13 +
      61*X^12 + 30*X^11 + 57*X^10 + 50*X^9 + 29*X^8 + 35*X^7 + 58*X^6 + 7*X^5 + 5*X^4 + 33*X^3 +
      31*X^2 + 39*X + 58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s113 : XPow fSeventeenA2 44834657850223272081491
    (44*X^33 + 48*X^32 + 28*X^31 + 65*X^30 + 16*X^29 + 19*X^28 + 45*X^27 + 7*X^26 + 21*X^25 + 25*X^24 +
      13*X^23 + 53*X^22 + 49*X^21 + 20*X^20 + 62*X^18 + 20*X^17 + 40*X^16 + 4*X^15 + 54*X^14 +
      43*X^13 + 29*X^12 + 49*X^11 + 53*X^10 + 48*X^9 + 5*X^8 + 20*X^7 + 52*X^6 + 36*X^5 + 15*X^4 +
      53*X^3 + 18*X^2 + 63*X + 25) :=
  mul_step (by norm_num) pSeventeenA2s112 pSeventeenA21 ⟨
    51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s114 : XPow fSeventeenA2 89669315700446544162982
    (46*X^33 + 5*X^32 + 65*X^31 + 49*X^30 + 6*X^29 + 46*X^28 + 51*X^27 + 56*X^26 + 59*X^25 + 22*X^24 +
      12*X^23 + 5*X^22 + 59*X^21 + 45*X^20 + 22*X^19 + 49*X^18 + 57*X^17 + 44*X^16 + 2*X^15 +
      50*X^14 + 2*X^13 + 12*X^12 + 45*X^11 + 34*X^10 + 59*X^9 + 7*X^8 + 10*X^7 + 59*X^6 + 44*X^5 +
      45*X^4 + 41*X^3 + 28*X^2 + 46*X + 51) :=
  sq_step (by norm_num) pSeventeenA2s113 ⟨
    60*X^32 + 30*X^31 + 10*X^30 + 35*X^29 + 3*X^28 + 30*X^27 + 52*X^26 + 61*X^25 + 54*X^24 + 30*X^23 +
      19*X^22 + 35*X^21 + 18*X^20 + 63*X^19 + 7*X^18 + 41*X^17 + 65*X^16 + 40*X^15 + 16*X^14 +
      43*X^13 + 18*X^12 + 8*X^11 + 21*X^10 + 9*X^9 + 60*X^8 + 58*X^7 + 15*X^6 + 51*X^5 + 55*X^4 +
      37*X^3 + 42*X^2 + 64*X + 27,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s115 : XPow fSeventeenA2 179338631400893088325964
    (13*X^33 + 10*X^32 + 61*X^31 + 17*X^30 + 6*X^29 + 31*X^28 + 44*X^27 + 27*X^26 + 11*X^25 + 37*X^24 +
      23*X^23 + 27*X^22 + 42*X^21 + 36*X^20 + 41*X^19 + 29*X^18 + 45*X^17 + 38*X^16 + 59*X^15 +
      39*X^14 + 33*X^13 + 30*X^12 + 22*X^11 + 13*X^10 + 8*X^9 + 6*X^8 + 64*X^7 + 27*X^6 + 17*X^5 +
      33*X^4 + 41*X^3 + 49*X^2 + 49*X + 51) :=
  sq_step (by norm_num) pSeventeenA2s114 ⟨
    39*X^32 + 32*X^31 + 52*X^30 + 56*X^29 + 23*X^28 + 9*X^27 + 31*X^26 + 37*X^25 + 47*X^24 + 51*X^23 +
      49*X^22 + 26*X^21 + 9*X^20 + 35*X^19 + 23*X^18 + 24*X^17 + 2*X^16 + 21*X^15 + 66*X^14 +
      52*X^13 + 60*X^12 + 11*X^11 + 46*X^10 + 21*X^9 + 27*X^8 + 34*X^7 + 24*X^6 + 53*X^5 + 56*X^4 +
      50*X^3 + 36*X^2 + 24,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s116 : XPow fSeventeenA2 179338631400893088325965
    (46*X^33 + 64*X^32 + X^31 + 21*X^30 + 54*X^29 + 8*X^28 + 14*X^27 + 9*X^26 + 25*X^25 + 42*X^24 +
      37*X^23 + 12*X^22 + 62*X^21 + 51*X^20 + 39*X^19 + 54*X^18 + 41*X^17 + 62*X^16 + 50*X^15 +
      23*X^14 + 40*X^13 + 35*X^12 + 64*X^11 + 60*X^10 + 11*X^9 + 51*X^8 + 54*X^7 + 19*X^6 + 11*X^5 +
      25*X^4 + X^3 + 7*X^2 + 29*X + 9) :=
  mul_step (by norm_num) pSeventeenA2s115 pSeventeenA21 ⟨
    13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s117 : XPow fSeventeenA2 358677262801786176651930
    (53*X^33 + 64*X^32 + 54*X^31 + 16*X^30 + 11*X^29 + 16*X^28 + 61*X^27 + 44*X^26 + 6*X^25 + 29*X^24 +
      21*X^23 + 49*X^22 + 37*X^21 + 13*X^20 + 36*X^19 + 53*X^18 + 15*X^17 + 52*X^16 + X^15 + 16*X^14 +
      37*X^13 + 25*X^12 + 5*X^11 + 46*X^10 + 65*X^9 + 50*X^8 + 41*X^7 + 16*X^6 + 42*X^5 + 13*X^4 +
      13*X^3 + 3*X^2 + 35*X + 7) :=
  sq_step (by norm_num) pSeventeenA2s116 ⟨
    39*X^32 + 33*X^31 + 21*X^30 + 42*X^29 + 26*X^28 + 50*X^27 + X^26 + 33*X^25 + 28*X^24 + 60*X^23 +
      30*X^22 + 12*X^21 + X^20 + 17*X^19 + 36*X^18 + 39*X^17 + 58*X^16 + 26*X^15 + 44*X^14 + 56*X^13 +
      21*X^12 + 14*X^11 + 66*X^10 + 31*X^9 + 21*X^8 + 48*X^7 + 43*X^6 + X^5 + 56*X^4 + 48*X^3 +
      58*X^2 + 32*X + 42,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s118 : XPow fSeventeenA2 358677262801786176651931
    (51*X^33 + 25*X^32 + 59*X^31 + 17*X^29 + 7*X^28 + 58*X^27 + 3*X^26 + 11*X^25 + 16*X^24 + 64*X^23 +
      59*X^22 + 52*X^21 + 51*X^20 + X^19 + 62*X^18 + 23*X^17 + 39*X^16 + 66*X^15 + 22*X^14 + 40*X^13 +
      58*X^12 + 22*X^11 + 9*X^10 + 24*X^9 + 55*X^8 + 23*X^7 + 45*X^6 + 47*X^5 + 56*X^4 + 65*X^3 +
      39*X^2 + 41*X + 47) :=
  mul_step (by norm_num) pSeventeenA2s117 pSeventeenA21 ⟨
    53,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s119 : XPow fSeventeenA2 717354525603572353303862
    (37*X^33 + 63*X^32 + 37*X^31 + 47*X^30 + 29*X^29 + 17*X^28 + 36*X^27 + 9*X^26 + 7*X^25 + 26*X^24 +
      16*X^23 + 14*X^22 + 26*X^21 + 17*X^20 + 47*X^19 + 33*X^18 + 45*X^17 + 58*X^16 + 5*X^15 +
      23*X^14 + 41*X^13 + 25*X^12 + 18*X^11 + 57*X^10 + 49*X^9 + 2*X^8 + 17*X^7 + 38*X^6 + 51*X^5 +
      62*X^4 + 3*X^3 + 65*X^2 + 8*X + 60) :=
  sq_step (by norm_num) pSeventeenA2s118 ⟨
    55*X^32 + 12*X^31 + 25*X^30 + 63*X^29 + 53*X^28 + 7*X^27 + 22*X^26 + 38*X^25 + 60*X^24 + 4*X^23 +
      46*X^22 + 21*X^21 + 43*X^20 + 43*X^19 + 33*X^18 + 30*X^17 + 23*X^16 + 35*X^15 + 31*X^14 +
      37*X^13 + 6*X^12 + 44*X^11 + 50*X^10 + 62*X^9 + 65*X^8 + 38*X^7 + 10*X^6 + 28*X^5 + 8*X^4 +
      31*X^3 + 14*X^2 + 12*X + 30,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s120 : XPow fSeventeenA2 717354525603572353303863
    (16*X^33 + 61*X^32 + 53*X^31 + 15*X^30 + 16*X^28 + 39*X^27 + 58*X^26 + 64*X^25 + 34*X^24 + 27*X^23 +
      54*X^22 + 24*X^21 + 60*X^20 + 46*X^19 + 50*X^18 + 15*X^17 + 29*X^16 + 44*X^15 + 28*X^14 +
      38*X^13 + 55*X^12 + 63*X^11 + 63*X^10 + 42*X^9 + 47*X^8 + 53*X^7 + 20*X^5 + 9*X^4 + 16*X^3 +
      7*X^2 + 18*X + 5) :=
  mul_step (by norm_num) pSeventeenA2s119 pSeventeenA21 ⟨
    37,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s121 : XPow fSeventeenA2 1434709051207144706607726
    (X^33 + 37*X^32 + 3*X^31 + 24*X^30 + 18*X^29 + 23*X^28 + 40*X^27 + 26*X^26 + 2*X^25 + 23*X^24 +
      65*X^23 + 4*X^22 + 2*X^21 + 65*X^20 + 52*X^19 + 3*X^18 + 51*X^17 + 44*X^16 + 15*X^15 + 15*X^14 +
      18*X^13 + 49*X^12 + 48*X^11 + 25*X^10 + 14*X^9 + 55*X^8 + 51*X^7 + 10*X^6 + 13*X^5 + 14*X^4 +
      40*X^3 + 59*X^2 + 35*X + 55) :=
  sq_step (by norm_num) pSeventeenA2s120 ⟨
    55*X^32 + 17*X^31 + 24*X^30 + 58*X^29 + 34*X^28 + 55*X^27 + 28*X^26 + X^25 + 46*X^24 + 20*X^23 +
      52*X^22 + 46*X^21 + 58*X^20 + 9*X^19 + 36*X^18 + 25*X^17 + 32*X^16 + 24*X^15 + 14*X^14 +
      64*X^13 + 22*X^12 + 3*X^11 + 52*X^10 + 19*X^9 + 2*X^8 + 16*X^7 + 15*X^6 + 21*X^5 + 64*X^4 +
      27*X^3 + 25*X^2 + 28*X + 21,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s122 : XPow fSeventeenA2 1434709051207144706607727
    (14*X^33 + 29*X^32 + 64*X^31 + 14*X^30 + 66*X^29 + 63*X^28 + 25*X^27 + 7*X^26 + 53*X^25 + 51*X^24 +
      46*X^23 + 10*X^22 + 27*X^20 + 45*X^19 + 62*X^18 + 3*X^17 + 41*X^16 + 21*X^15 + 43*X^14 +
      24*X^13 + 49*X^12 + 65*X^11 + 18*X^10 + 9*X^9 + 50*X^8 + 43*X^7 + 8*X^6 + 2*X^5 + 13*X^4 +
      45*X^3 + 6*X^2 + 43*X + 11) :=
  mul_step (by norm_num) pSeventeenA2s121 pSeventeenA21 ⟨
    1,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s123 : XPow fSeventeenA2 2869418102414289413215454
    (66*X^33 + 44*X^32 + 6*X^31 + 57*X^30 + 45*X^29 + 59*X^28 + 32*X^27 + 42*X^26 + 4*X^25 + 32*X^23 +
      8*X^22 + 20*X^21 + 43*X^20 + 16*X^19 + 64*X^18 + 13*X^17 + 8*X^16 + 64*X^15 + 44*X^14 +
      38*X^13 + 53*X^12 + 60*X^11 + 28*X^10 + 12*X^9 + 49*X^8 + 8*X^7 + 48*X^6 + 32*X^5 + 42*X^4 +
      28*X^3 + 34*X^2 + 56*X + 15) :=
  sq_step (by norm_num) pSeventeenA2s122 ⟨
    62*X^32 + 56*X^31 + 9*X^30 + 61*X^29 + 8*X^28 + 64*X^27 + 16*X^26 + 4*X^25 + 61*X^24 + 24*X^23 +
      41*X^22 + 45*X^21 + 37*X^20 + 58*X^19 + 24*X^18 + 49*X^17 + 15*X^16 + 38*X^15 + 53*X^14 +
      45*X^13 + 23*X^12 + X^11 + 65*X^10 + 35*X^9 + 15*X^8 + 56*X^7 + 8*X^6 + 22*X^5 + 46*X^4 +
      8*X^3 + 31*X^2 + 16*X + 33,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s124 : XPow fSeventeenA2 5738836204828578826430908
    (57*X^33 + 49*X^32 + 32*X^31 + 39*X^30 + 59*X^29 + 48*X^28 + 30*X^27 + 21*X^26 + 10*X^25 + 48*X^24 +
      65*X^23 + 32*X^22 + 6*X^21 + 28*X^20 + 58*X^19 + 19*X^18 + 65*X^17 + 47*X^16 + 25*X^15 +
      21*X^14 + 55*X^12 + 56*X^11 + 3*X^10 + 33*X^9 + 33*X^8 + 24*X^7 + 20*X^6 + 41*X^5 + 56*X^4 +
      15*X^3 + 20*X^2 + 10*X + 16) :=
  sq_step (by norm_num) pSeventeenA2s123 ⟨
    X^32 + 23*X^31 + 14*X^30 + 60*X^29 + 38*X^28 + 28*X^27 + 21*X^26 + 36*X^25 + 45*X^24 + 54*X^23 +
      39*X^22 + 50*X^21 + 36*X^19 + 55*X^18 + 43*X^17 + 36*X^16 + 48*X^15 + 59*X^14 + 15*X^13 +
      41*X^12 + 11*X^11 + 65*X^10 + 44*X^9 + 9*X^8 + 51*X^7 + 17*X^6 + 48*X^5 + 58*X^4 + 34*X^3 +
      59*X^2 + 65*X + 48,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s125 : XPow fSeventeenA2 5738836204828578826430909
    (11*X^33 + 40*X^32 + 41*X^31 + 32*X^30 + 20*X^29 + X^28 + 31*X^27 + 27*X^26 + 16*X^25 + 4*X^24 +
      14*X^23 + 60*X^22 + 8*X^21 + 40*X^20 + X^19 + 22*X^18 + 55*X^17 + 33*X^16 + 28*X^15 + 18*X^14 +
      37*X^13 + 46*X^12 + 5*X^11 + 60*X^10 + 24*X^9 + 34*X^8 + 25*X^7 + 24*X^6 + 42*X^5 + 17*X^4 +
      26*X^3 + 32*X^2 + 2*X + 24) :=
  mul_step (by norm_num) pSeventeenA2s124 pSeventeenA21 ⟨
    57,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s126 : XPow fSeventeenA2 11477672409657157652861818
    (20*X^33 + 58*X^32 + 17*X^31 + 56*X^30 + 19*X^29 + 34*X^28 + 30*X^27 + 37*X^26 + 26*X^25 + 54*X^24 +
      51*X^23 + 16*X^22 + 8*X^21 + 66*X^20 + 57*X^19 + 7*X^18 + 27*X^17 + 56*X^16 + 41*X^15 +
      60*X^14 + 31*X^13 + 63*X^11 + 60*X^10 + 28*X^9 + 63*X^8 + 44*X^7 + 14*X^6 + 45*X^5 + 15*X^4 +
      39*X^3 + 2*X^2 + 27*X + 61) :=
  sq_step (by norm_num) pSeventeenA2s125 ⟨
    54*X^32 + 40*X^31 + 38*X^30 + 12*X^29 + 10*X^28 + 37*X^27 + 28*X^26 + 35*X^25 + 59*X^24 + 43*X^23 +
      6*X^22 + 22*X^21 + 5*X^20 + 39*X^19 + 46*X^18 + 52*X^17 + 39*X^16 + 18*X^15 + 23*X^14 +
      14*X^13 + 44*X^12 + 25*X^11 + 59*X^10 + 59*X^9 + 37*X^8 + 50*X^7 + 48*X^6 + 31*X^5 + 50*X^4 +
      13*X^3 + 3*X^2 + 39*X + 8,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s127 : XPow fSeventeenA2 11477672409657157652861819
    (X^32 + 52*X^31 + 6*X^30 + 23*X^29 + 21*X^28 + 17*X^27 + 59*X^26 + 51*X^25 + 39*X^24 + 52*X^23 +
      34*X^22 + 39*X^21 + 26*X^20 + 43*X^19 + 46*X^18 + 40*X^17 + 25*X^16 + 46*X^15 + 62*X^14 +
      36*X^13 + 16*X^12 + 56*X^11 + 41*X^10 + 14*X^9 + 24*X^8 + 4*X^7 + 12*X^6 + 43*X^5 + 35*X^4 +
      57*X^3 + 50*X^2 + 22*X + 19) :=
  mul_step (by norm_num) pSeventeenA2s126 pSeventeenA21 ⟨
    20,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s128 : XPow fSeventeenA2 22955344819314315305723638
    (36*X^33 + 47*X^32 + 46*X^31 + 63*X^30 + 42*X^29 + 30*X^28 + 19*X^27 + 40*X^26 + 63*X^25 + 6*X^24 +
      47*X^23 + 19*X^21 + 20*X^20 + 43*X^19 + 8*X^18 + 36*X^17 + 34*X^16 + 8*X^15 + 44*X^14 +
      41*X^13 + 29*X^12 + 46*X^11 + 54*X^10 + 31*X^9 + 42*X^8 + 31*X^7 + 31*X^6 + 6*X^5 + 46*X^4 +
      21*X^3 + 3*X^2 + 11*X + 2) :=
  sq_step (by norm_num) pSeventeenA2s127 ⟨
    X^30 + 14*X^29 + 8*X^28 + 19*X^27 + 50*X^26 + X^25 + 4*X^24 + 15*X^23 + 65*X^22 + 14*X^21 + 23*X^20 +
      17*X^19 + 27*X^18 + 28*X^17 + 46*X^16 + 36*X^15 + 32*X^14 + 27*X^13 + 36*X^12 + 30*X^11 +
      11*X^10 + 37*X^9 + 39*X^8 + 6*X^7 + 8*X^6 + 61*X^5 + 20*X^4 + 19*X^3 + 39*X^2 + 9*X + 10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s129 : XPow fSeventeenA2 45910689638628630611447276
    (33*X^33 + 25*X^32 + 8*X^31 + 30*X^30 + 21*X^29 + 56*X^28 + 47*X^27 + 55*X^26 + 29*X^25 + 13*X^24 +
      39*X^23 + 26*X^22 + 18*X^21 + 61*X^20 + 15*X^19 + 16*X^18 + 38*X^17 + 51*X^16 + 33*X^15 +
      26*X^13 + 44*X^12 + 3*X^11 + 13*X^10 + 46*X^9 + 55*X^8 + 34*X^7 + 18*X^6 + 63*X^5 + 6*X^4 +
      22*X^3 + 63*X^2 + 65*X + 50) :=
  sq_step (by norm_num) pSeventeenA2s128 ⟨
    23*X^32 + 41*X^31 + 17*X^30 + 3*X^29 + 52*X^28 + 30*X^27 + 19*X^26 + 30*X^25 + 27*X^24 + 36*X^23 +
      46*X^22 + 49*X^21 + 53*X^20 + 52*X^19 + 64*X^18 + 20*X^17 + 48*X^16 + 45*X^15 + 28*X^14 +
      40*X^13 + 26*X^12 + 53*X^11 + 32*X^10 + 17*X^9 + 22*X^8 + 21*X^7 + 17*X^6 + 25*X^5 + 11*X^4 +
      35*X^3 + 31*X^2 + 48*X + 59,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s130 : XPow fSeventeenA2 91821379277257261222894552
    (20*X^33 + 47*X^32 + 5*X^31 + 51*X^30 + 10*X^29 + 13*X^28 + 66*X^27 + 57*X^26 + 24*X^25 + 48*X^24 +
      46*X^23 + 31*X^22 + 51*X^21 + 49*X^20 + 32*X^19 + 48*X^18 + 52*X^17 + 2*X^16 + 11*X^15 +
      21*X^14 + 39*X^13 + 46*X^12 + 9*X^11 + 27*X^10 + 54*X^9 + 27*X^8 + 32*X^7 + X^6 + 9*X^5 +
      9*X^4 + 11*X^3 + 21*X^2 + 54*X + 15) :=
  sq_step (by norm_num) pSeventeenA2s129 ⟨
    17*X^32 + 53*X^31 + 41*X^30 + 11*X^29 + 53*X^28 + 20*X^27 + 14*X^26 + 42*X^25 + 65*X^24 + 45*X^23 +
      46*X^22 + 42*X^21 + 42*X^20 + 33*X^19 + 48*X^18 + 50*X^17 + 21*X^16 + 56*X^15 + 4*X^14 +
      14*X^13 + 9*X^12 + 14*X^11 + 43*X^10 + 58*X^9 + 26*X^8 + 65*X^7 + X^6 + 2*X^5 + 44*X^4 +
      22*X^2 + 38*X + 36,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s131 : XPow fSeventeenA2 183642758554514522445789104
    (36*X^33 + 40*X^32 + 63*X^31 + 52*X^30 + 6*X^29 + 64*X^28 + 54*X^27 + 13*X^26 + 49*X^25 + 49*X^24 +
      27*X^23 + 2*X^22 + 58*X^21 + 19*X^20 + 53*X^19 + 32*X^18 + 62*X^17 + 48*X^16 + 22*X^15 +
      66*X^14 + 14*X^13 + 52*X^12 + 52*X^11 + 9*X^10 + 40*X^9 + 52*X^8 + 51*X^7 + 33*X^6 + 56*X^5 +
      24*X^4 + 2*X^3 + 12*X^2 + 2*X + 63) :=
  sq_step (by norm_num) pSeventeenA2s130 ⟨
    65*X^32 + 50*X^31 + X^30 + 22*X^29 + 47*X^28 + 9*X^27 + 39*X^26 + 32*X^25 + 48*X^24 + 28*X^23 +
      43*X^22 + 2*X^21 + 5*X^20 + 22*X^19 + 3*X^18 + 4*X^17 + 32*X^16 + 10*X^15 + 6*X^14 + 44*X^13 +
      5*X^12 + 17*X^11 + 63*X^10 + 41*X^9 + 46*X^8 + 61*X^7 + 22*X^6 + 16*X^5 + 12*X^4 + 39*X^3 +
      26*X^2 + 24*X + 34,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s132 : XPow fSeventeenA2 183642758554514522445789105
    (16*X^33 + 61*X^32 + 18*X^31 + 63*X^30 + 4*X^29 + 11*X^28 + 44*X^27 + 28*X^26 + 57*X^25 + 59*X^24 +
      40*X^23 + 11*X^22 + 24*X^21 + 24*X^20 + 3*X^19 + 56*X^18 + 46*X^17 + 20*X^16 + 14*X^15 +
      43*X^14 + 23*X^13 + 21*X^12 + 42*X^11 + 50*X^10 + 4*X^9 + 15*X^8 + 15*X^7 + 10*X^6 + 61*X^5 +
      35*X^4 + 44*X^3 + 30*X^2 + 33*X + 61) :=
  mul_step (by norm_num) pSeventeenA2s131 pSeventeenA21 ⟨
    36,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s133 : XPow fSeventeenA2 367285517109029044891578210
    (5*X^33 + 28*X^32 + 64*X^31 + 60*X^30 + 43*X^29 + X^28 + 55*X^27 + 2*X^26 + 53*X^25 + 57*X^24 +
      3*X^23 + 29*X^22 + 50*X^21 + 39*X^20 + 2*X^19 + 53*X^18 + 5*X^17 + 24*X^16 + 61*X^15 + 3*X^14 +
      66*X^13 + 20*X^12 + 13*X^11 + 24*X^10 + 4*X^9 + 11*X^8 + 39*X^7 + 27*X^6 + 5*X^5 + 49*X^4 +
      4*X^3 + 6*X^2 + 31*X + 42) :=
  sq_step (by norm_num) pSeventeenA2s132 ⟨
    55*X^32 + 17*X^31 + 43*X^30 + 36*X^29 + 44*X^28 + 14*X^27 + 28*X^26 + 32*X^25 + 7*X^24 + 55*X^23 +
      2*X^22 + 46*X^21 + 55*X^20 + 42*X^19 + 52*X^18 + 48*X^17 + 9*X^16 + 63*X^15 + 64*X^14 + X^13 +
      53*X^12 + 4*X^11 + 54*X^10 + 38*X^9 + 53*X^8 + 38*X^7 + 15*X^6 + 37*X^5 + 41*X^4 + 60*X^3 +
      30*X + 31,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s134 : XPow fSeventeenA2 367285517109029044891578211
    (47*X^33 + 60*X^32 + 59*X^31 + 23*X^30 + 15*X^29 + 36*X^28 + 64*X^27 + 11*X^26 + 6*X^25 + 38*X^23 +
      23*X^22 + 49*X^21 + 11*X^20 + 62*X^19 + 60*X^18 + 20*X^17 + 57*X^16 + 33*X^15 + 57*X^14 +
      29*X^13 + 18*X^12 + 23*X^11 + 24*X^10 + 49*X^9 + 34*X^8 + 58*X^7 + 47*X^6 + 56*X^5 + 3*X^4 +
      3*X^3 + 20*X^2 + 49*X + 55) :=
  mul_step (by norm_num) pSeventeenA2s133 pSeventeenA21 ⟨
    5,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s135 : XPow fSeventeenA2 734571034218058089783156422
    (60*X^33 + 21*X^32 + 42*X^31 + 22*X^30 + 18*X^29 + 40*X^28 + 18*X^27 + 9*X^26 + 13*X^25 + 26*X^24 +
      60*X^23 + 57*X^22 + 43*X^21 + 33*X^20 + 61*X^19 + 5*X^18 + 58*X^17 + 60*X^16 + 51*X^15 +
      65*X^14 + 17*X^13 + 38*X^12 + 53*X^11 + 61*X^10 + 11*X^9 + 49*X^8 + 39*X^7 + 3*X^6 + 49*X^5 +
      15*X^4 + 28*X^3 + 58*X^2 + 14*X + 33) :=
  sq_step (by norm_num) pSeventeenA2s134 ⟨
    65*X^32 + 58*X^31 + 55*X^30 + 25*X^29 + 47*X^28 + 36*X^27 + 43*X^26 + 52*X^25 + 23*X^24 + 23*X^23 +
      20*X^22 + 14*X^21 + 50*X^20 + 61*X^19 + 53*X^18 + 2*X^17 + 22*X^16 + 37*X^15 + X^14 + 4*X^13 +
      32*X^12 + 65*X^11 + 66*X^10 + 47*X^9 + 5*X^8 + 35*X^7 + 58*X^6 + 38*X^5 + 30*X^4 + 33*X^3 +
      38*X^2 + 49*X + 63,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s136 : XPow fSeventeenA2 734571034218058089783156423
    (48*X^33 + 61*X^32 + 10*X^31 + 46*X^30 + 7*X^29 + 58*X^28 + 16*X^27 + 45*X^26 + 17*X^25 + 24*X^24 +
      31*X^23 + 54*X^22 + 19*X^21 + 35*X^20 + 46*X^19 + 48*X^18 + 12*X^17 + 3*X^16 + 23*X^15 +
      43*X^14 + 12*X^13 + 46*X^12 + 49*X^11 + 50*X^10 + 36*X^9 + 46*X^8 + 40*X^7 + 17*X^6 + 32*X^5 +
      16*X^4 + 22*X^3 + 16*X^2 + 50*X + 57) :=
  mul_step (by norm_num) pSeventeenA2s135 pSeventeenA21 ⟨
    60,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s137 : XPow fSeventeenA2 1469142068436116179566312846
    (49*X^33 + 35*X^32 + 8*X^31 + 50*X^30 + 53*X^29 + 2*X^28 + 22*X^27 + 61*X^26 + 12*X^25 + 64*X^24 +
      3*X^23 + 28*X^22 + 66*X^21 + 36*X^20 + 41*X^19 + 45*X^18 + 7*X^17 + 23*X^16 + 50*X^15 +
      40*X^14 + 17*X^13 + 55*X^12 + 33*X^11 + 22*X^10 + X^9 + 63*X^8 + 60*X^7 + 63*X^6 + 13*X^5 +
      60*X^4 + 60*X^3 + 13*X^2 + 10*X + 22) :=
  sq_step (by norm_num) pSeventeenA2s136 ⟨
    26*X^32 + 32*X^31 + 65*X^30 + 50*X^29 + 60*X^28 + 65*X^27 + 41*X^26 + 56*X^25 + 15*X^24 + 52*X^23 +
      54*X^22 + 58*X^21 + 49*X^20 + 3*X^19 + 60*X^18 + 54*X^17 + 61*X^16 + 17*X^15 + 46*X^14 +
      46*X^13 + 28*X^12 + 60*X^11 + 15*X^10 + 63*X^9 + 2*X^8 + 28*X^7 + 34*X^6 + 33*X^5 + 27*X^4 +
      5*X^3 + 35*X^2 + 42*X + 66,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s138 : XPow fSeventeenA2 1469142068436116179566312847
    (47*X^33 + 9*X^32 + 58*X^30 + 32*X^29 + 10*X^28 + 12*X^27 + 56*X^26 + 60*X^25 + 54*X^24 + 9*X^23 +
      56*X^22 + 22*X^20 + 26*X^19 + 10*X^18 + 24*X^17 + 51*X^16 + 66*X^15 + 36*X^14 + 36*X^13 +
      15*X^12 + 39*X^11 + 63*X^10 + 20*X^9 + 11*X^8 + 5*X^7 + 36*X^6 + 8*X^5 + 10*X^4 + 64*X^3 +
      63*X^2 + 37*X + 3) :=
  mul_step (by norm_num) pSeventeenA2s137 pSeventeenA21 ⟨
    49,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s139 : XPow fSeventeenA2 2938284136872232359132625694
    (34*X^33 + 6*X^32 + 59*X^31 + 29*X^30 + X^29 + 45*X^28 + 10*X^27 + 13*X^26 + 58*X^25 + 13*X^24 +
      26*X^23 + 50*X^22 + 64*X^21 + 47*X^20 + 37*X^19 + 64*X^18 + 42*X^17 + 17*X^16 + 38*X^15 +
      34*X^14 + 19*X^13 + 65*X^12 + 44*X^11 + 23*X^10 + 46*X^9 + 26*X^8 + 55*X^7 + 60*X^6 + 42*X^5 +
      2*X^4 + 55*X^3 + 6*X^2 + 25*X + 58) :=
  sq_step (by norm_num) pSeventeenA2s138 ⟨
    65*X^32 + 21*X^31 + 15*X^30 + 12*X^29 + 56*X^28 + 32*X^27 + 36*X^26 + 56*X^25 + 48*X^24 + 37*X^23 +
      52*X^22 + 66*X^21 + 42*X^20 + 22*X^19 + 53*X^18 + 12*X^17 + 40*X^16 + 10*X^15 + 10*X^14 +
      40*X^13 + 7*X^12 + 13*X^11 + 52*X^10 + 21*X^9 + 32*X^8 + 18*X^6 + 51*X^5 + 36*X^4 + 44*X^3 +
      35*X^2 + 39*X + 41,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s140 : XPow fSeventeenA2 5876568273744464718265251388
    (62*X^33 + 48*X^32 + 20*X^31 + 50*X^30 + 5*X^29 + 25*X^28 + 10*X^27 + 54*X^26 + 59*X^25 + 33*X^24 +
      66*X^23 + 11*X^22 + 15*X^21 + 55*X^20 + 44*X^19 + 29*X^18 + 51*X^17 + 31*X^16 + 26*X^15 +
      58*X^14 + 62*X^13 + 64*X^12 + 30*X^11 + 51*X^10 + 3*X^9 + 26*X^8 + 12*X^7 + 35*X^6 + 51*X^5 +
      45*X^4 + 25*X^3 + 36*X^2 + 3*X + 22) :=
  sq_step (by norm_num) pSeventeenA2s139 ⟨
    17*X^32 + 17*X^31 + 12*X^30 + 42*X^29 + 36*X^28 + 62*X^27 + 21*X^26 + 15*X^25 + 49*X^24 + 36*X^23 +
      32*X^22 + 34*X^21 + 36*X^20 + X^19 + 33*X^18 + 5*X^17 + 14*X^16 + 58*X^15 + 26*X^14 + 64*X^13 +
      7*X^12 + 17*X^11 + 44*X^10 + 19*X^9 + 23*X^8 + 5*X^7 + 59*X^5 + 29*X^4 + 18*X^3 + 44*X^2 + X +
      19,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s141 : XPow fSeventeenA2 5876568273744464718265251389
    (29*X^33 + 24*X^32 + 51*X^31 + 25*X^30 + 11*X^29 + 29*X^28 + 59*X^27 + 34*X^26 + 17*X^25 + 2*X^24 +
      2*X^23 + 42*X^22 + 45*X^21 + 35*X^20 + 20*X^19 + 63*X^18 + 35*X^17 + 30*X^16 + 28*X^15 +
      4*X^14 + 55*X^13 + 25*X^12 + 52*X^11 + 50*X^10 + 55*X^9 + 17*X^8 + 4*X^7 + 9*X^6 + 38*X^5 +
      26*X^4 + 39*X^3 + 14*X^2 + 15*X + 12) :=
  mul_step (by norm_num) pSeventeenA2s140 pSeventeenA21 ⟨
    62,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s142 : XPow fSeventeenA2 11753136547488929436530502778
    (61*X^33 + 63*X^32 + 65*X^31 + 51*X^30 + 58*X^29 + 9*X^28 + 44*X^26 + 49*X^25 + 49*X^24 + 66*X^23 +
      16*X^22 + 60*X^21 + 17*X^20 + 43*X^19 + X^18 + 9*X^16 + 28*X^15 + 24*X^14 + 61*X^12 + 10*X^11 +
      43*X^10 + 58*X^9 + 27*X^8 + 40*X^7 + 54*X^6 + 11*X^5 + 53*X^4 + 23*X^3 + 33*X^2 + 60*X + 58) :=
  sq_step (by norm_num) pSeventeenA2s141 ⟨
    37*X^32 + 5*X^31 + 26*X^30 + 19*X^29 + 40*X^28 + 44*X^27 + 3*X^26 + 47*X^25 + 4*X^24 + 61*X^22 +
      3*X^21 + 7*X^20 + 19*X^19 + 51*X^18 + 6*X^17 + 45*X^16 + 56*X^15 + 39*X^14 + 62*X^13 + 6*X^12 +
      43*X^11 + 24*X^10 + 41*X^9 + 9*X^8 + 35*X^7 + 4*X^6 + X^5 + 43*X^4 + 64*X^3 + 29*X^2 + 24*X +
      47,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s143 : XPow fSeventeenA2 11753136547488929436530502779
    (43*X^32 + 12*X^31 + 15*X^30 + 19*X^29 + 63*X^28 + 50*X^27 + 19*X^26 + 3*X^25 + 16*X^24 + 32*X^23 +
      12*X^22 + 5*X^21 + 59*X^20 + 17*X^19 + X^18 + 54*X^17 + 6*X^16 + 55*X^15 + 51*X^14 + 10*X^13 +
      4*X^12 + 4*X^11 + 34*X^10 + 35*X^9 + 46*X^8 + 57*X^7 + 41*X^6 + 58*X^5 + 51*X^4 + 50*X^3 +
      33*X^2 + 63*X + 1) :=
  mul_step (by norm_num) pSeventeenA2s142 pSeventeenA21 ⟨
    61,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s144 : XPow fSeventeenA2 23506273094977858873061005558
    (40*X^33 + 25*X^32 + 47*X^31 + 8*X^30 + 61*X^29 + 46*X^28 + 23*X^27 + 16*X^26 + 26*X^25 + 13*X^24 +
      57*X^23 + 6*X^22 + 24*X^21 + 16*X^20 + 25*X^19 + 41*X^18 + 9*X^17 + 46*X^16 + 8*X^15 + 49*X^14 +
      54*X^13 + 38*X^12 + 35*X^11 + 44*X^10 + 57*X^9 + 57*X^8 + 50*X^7 + 38*X^6 + 35*X^5 + 18*X^4 +
      23*X^3 + 20*X^2 + 63*X + 16) :=
  sq_step (by norm_num) pSeventeenA2s143 ⟨
    40*X^30 + 45*X^29 + 32*X^28 + 8*X^27 + 12*X^26 + 22*X^25 + 32*X^24 + 27*X^23 + 48*X^22 + 66*X^21 +
      17*X^20 + 30*X^19 + 40*X^18 + 30*X^17 + 47*X^16 + 37*X^15 + 33*X^14 + 36*X^13 + 60*X^12 +
      7*X^11 + 49*X^10 + 2*X^9 + 8*X^8 + 62*X^7 + 57*X^5 + 37*X^4 + 20*X^3 + 33*X^2 + 24*X + 44,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s145 : XPow fSeventeenA2 23506273094977858873061005559
    (43*X^33 + 15*X^32 + 35*X^30 + 24*X^29 + 5*X^28 + 43*X^27 + 25*X^26 + 7*X^25 + 33*X^24 + 11*X^23 +
      9*X^22 + 29*X^21 + 30*X^20 + 46*X^19 + 47*X^18 + 14*X^17 + 43*X^16 + 21*X^15 + 49*X^14 +
      43*X^13 + 8*X^12 + 36*X^11 + 16*X^10 + 26*X^9 + 10*X^8 + 18*X^7 + 36*X^6 + 7*X^5 + 15*X^4 +
      63*X^3 + 42*X^2 + 5*X + 38) :=
  mul_step (by norm_num) pSeventeenA2s144 pSeventeenA21 ⟨
    40,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s146 : XPow fSeventeenA2 47012546189955717746122011118
    (9*X^33 + 13*X^32 + 31*X^31 + 13*X^30 + 31*X^29 + 52*X^27 + 54*X^26 + 19*X^25 + 35*X^24 + 5*X^23 +
      X^22 + 21*X^21 + 11*X^20 + 45*X^19 + 57*X^18 + 49*X^17 + 53*X^16 + 30*X^15 + 50*X^14 + 46*X^13 +
      50*X^12 + 2*X^11 + 18*X^10 + 57*X^9 + 24*X^8 + 7*X^7 + 29*X^6 + 36*X^5 + 12*X^4 + 4*X^3 +
      38*X^2 + 9*X + 46) :=
  sq_step (by norm_num) pSeventeenA2s145 ⟨
    40*X^32 + 35*X^31 + 58*X^30 + 32*X^29 + 34*X^28 + 8*X^27 + 37*X^25 + 64*X^24 + 25*X^23 + 34*X^22 +
      34*X^21 + 53*X^20 + 14*X^19 + 5*X^18 + 43*X^17 + 46*X^16 + 45*X^15 + 32*X^14 + 17*X^13 +
      10*X^12 + 62*X^11 + 40*X^10 + 24*X^9 + 10*X^8 + 33*X^7 + 4*X^6 + 7*X^5 + 60*X^4 + 20*X^3 +
      44*X^2 + 17*X + 13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s147 : XPow fSeventeenA2 47012546189955717746122011119
    (7*X^33 + 64*X^32 + 38*X^31 + 62*X^30 + 52*X^29 + 58*X^28 + 45*X^27 + 64*X^26 + 37*X^25 + 13*X^24 +
      44*X^23 + 26*X^22 + 29*X^21 + 21*X^20 + 33*X^19 + 14*X^18 + 19*X^17 + 63*X^16 + 37*X^15 +
      3*X^14 + 26*X^13 + 11*X^12 + 43*X^11 + 26*X^10 + 12*X^9 + 65*X^8 + 58*X^7 + 58*X^6 + 38*X^5 +
      29*X^4 + 46*X^3 + 16*X^2 + 5*X + 32) :=
  mul_step (by norm_num) pSeventeenA2s146 pSeventeenA21 ⟨
    9,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s148 : XPow fSeventeenA2 94025092379911435492244022238
    (21*X^33 + 45*X^32 + 65*X^31 + 31*X^30 + 54*X^29 + 26*X^28 + 56*X^27 + 54*X^26 + 36*X^25 + 10*X^24 +
      18*X^23 + 41*X^22 + 26*X^21 + 41*X^20 + 24*X^19 + 15*X^18 + 35*X^17 + 17*X^16 + 57*X^15 +
      40*X^14 + 37*X^13 + 8*X^12 + 57*X^11 + 57*X^10 + 33*X^9 + 3*X^8 + 60*X^7 + 60*X^6 + 33*X^5 +
      15*X^4 + 35*X^3 + 43*X^2 + 13*X + 17) :=
  sq_step (by norm_num) pSeventeenA2s147 ⟨
    49*X^32 + 37*X^31 + 26*X^30 + 16*X^29 + 42*X^28 + 23*X^27 + 36*X^26 + 48*X^25 + 51*X^24 + 21*X^23 +
      54*X^22 + 24*X^21 + 7*X^20 + 57*X^19 + 24*X^18 + 47*X^17 + 4*X^16 + 43*X^15 + 52*X^14 + 4*X^13 +
      11*X^12 + 42*X^11 + 15*X^10 + 46*X^9 + 35*X^8 + 62*X^7 + 41*X^6 + 57*X^5 + 11*X^4 + 14*X^3 +
      63*X^2 + 40*X + 12,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s149 : XPow fSeventeenA2 188050184759822870984488044476
    (47*X^33 + 40*X^32 + 66*X^31 + 38*X^30 + 27*X^29 + 52*X^28 + 55*X^27 + 46*X^26 + 6*X^25 + 65*X^24 +
      39*X^23 + 32*X^22 + 65*X^21 + 6*X^20 + 48*X^19 + 33*X^18 + 50*X^17 + 20*X^16 + 6*X^15 + 9*X^14 +
      43*X^13 + 12*X^12 + 27*X^11 + 43*X^10 + 22*X^9 + 21*X^8 + 45*X^7 + 31*X^6 + 62*X^5 + 59*X^4 +
      9*X^3 + 40*X^2 + 14*X + 23) :=
  sq_step (by norm_num) pSeventeenA2s148 ⟨
    39*X^32 + 55*X^31 + 15*X^30 + 15*X^29 + 49*X^28 + 46*X^27 + 8*X^26 + 59*X^25 + 40*X^24 + 18*X^23 +
      47*X^22 + 20*X^21 + 22*X^20 + 36*X^19 + 63*X^18 + 23*X^17 + 31*X^16 + 30*X^15 + 60*X^14 +
      10*X^13 + 61*X^12 + 63*X^11 + 18*X^10 + 44*X^9 + 3*X^8 + X^7 + 42*X^6 + 60*X^5 + 66*X^4 +
      24*X^3 + 35*X^2 + 15*X + 55,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s150 : XPow fSeventeenA2 188050184759822870984488044477
    (31*X^33 + 15*X^32 + 42*X^31 + 40*X^30 + 63*X^29 + 64*X^28 + 66*X^27 + 40*X^26 + X^25 + 51*X^24 +
      63*X^23 + 39*X^22 + 33*X^21 + 12*X^20 + 64*X^19 + 31*X^18 + 36*X^17 + 22*X^16 + 23*X^15 +
      12*X^14 + 43*X^13 + 7*X^12 + 47*X^11 + 9*X^10 + 3*X^9 + 65*X^8 + 41*X^7 + 28*X^6 + 31*X^5 +
      13*X^4 + 52*X^3 + 58*X^2 + 62*X + 48) :=
  mul_step (by norm_num) pSeventeenA2s149 pSeventeenA21 ⟨
    47,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s151 : XPow fSeventeenA2 376100369519645741968976088954
    (30*X^33 + 34*X^32 + 47*X^31 + 54*X^30 + 6*X^29 + 15*X^28 + 20*X^27 + 44*X^26 + 16*X^25 + 3*X^24 +
      19*X^23 + 64*X^22 + X^21 + 33*X^20 + 16*X^19 + 65*X^18 + 16*X^17 + 60*X^16 + 44*X^14 + 44*X^13 +
      28*X^12 + 43*X^11 + 32*X^10 + 4*X^9 + 10*X^8 + 41*X^7 + 60*X^6 + 32*X^5 + 15*X^4 + 48*X^3 +
      26*X^2 + 59*X + 53) :=
  sq_step (by norm_num) pSeventeenA2s150 ⟨
    23*X^32 + 66*X^31 + 33*X^30 + 56*X^29 + 10*X^28 + 27*X^27 + 62*X^26 + 23*X^25 + 62*X^24 + 25*X^23 +
      3*X^22 + 37*X^21 + 38*X^20 + 3*X^19 + 65*X^18 + 43*X^17 + 23*X^16 + 12*X^15 + 19*X^14 +
      23*X^13 + 23*X^12 + 39*X^11 + 36*X^10 + 56*X^9 + 15*X^8 + 48*X^7 + 54*X^6 + 28*X^5 + 16*X^4 +
      22*X^3 + 10*X^2 + 55*X + 39,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s152 : XPow fSeventeenA2 752200739039291483937952177908
    (23*X^33 + 10*X^32 + 11*X^31 + X^30 + 53*X^29 + 33*X^28 + 65*X^27 + 3*X^26 + 23*X^25 + 63*X^24 +
      13*X^23 + 2*X^22 + 30*X^21 + 50*X^20 + 14*X^19 + 61*X^18 + 33*X^17 + 58*X^16 + 2*X^15 +
      24*X^14 + 26*X^13 + 38*X^12 + 13*X^11 + 10*X^10 + 56*X^9 + 22*X^8 + 61*X^7 + 46*X^6 + 48*X^5 +
      3*X^4 + 51*X^3 + 50*X^2 + 22*X + 39) :=
  sq_step (by norm_num) pSeventeenA2s151 ⟨
    29*X^32 + 33*X^31 + 18*X^30 + 7*X^28 + 18*X^27 + 45*X^26 + 39*X^25 + X^24 + 56*X^23 + 10*X^22 +
      20*X^21 + 26*X^20 + 23*X^19 + 6*X^18 + 3*X^17 + 52*X^16 + 56*X^15 + 52*X^14 + 35*X^13 +
      65*X^12 + 15*X^11 + 5*X^9 + 33*X^8 + 65*X^7 + 16*X^6 + 41*X^5 + 13*X^4 + 39*X^3 + 48*X^2 +
      53*X + 4,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s153 : XPow fSeventeenA2 1504401478078582967875904355816
    (33*X^33 + 3*X^32 + 16*X^31 + 7*X^30 + 45*X^29 + 7*X^28 + 26*X^27 + 12*X^26 + 34*X^25 + 2*X^24 +
      52*X^23 + 24*X^22 + 36*X^21 + 41*X^20 + 33*X^19 + 17*X^18 + 19*X^17 + 4*X^16 + 57*X^15 +
      36*X^14 + 49*X^13 + 49*X^12 + 62*X^10 + 61*X^9 + 44*X^8 + 20*X^7 + 37*X^6 + 57*X^5 + 57*X^4 +
      61*X^3 + 50*X^2 + 53*X + 51) :=
  sq_step (by norm_num) pSeventeenA2s152 ⟨
    60*X^32 + 18*X^31 + 10*X^30 + 23*X^29 + 43*X^28 + 25*X^27 + 19*X^26 + 4*X^25 + 47*X^24 + 5*X^23 +
      65*X^22 + 2*X^21 + 3*X^20 + 34*X^19 + 21*X^18 + 34*X^17 + 33*X^16 + 52*X^15 + 13*X^14 +
      52*X^13 + 58*X^12 + 15*X^11 + 17*X^10 + 4*X^9 + 28*X^8 + 58*X^7 + 39*X^6 + 50*X^5 + 29*X^4 +
      60*X^3 + 58*X^2 + 48*X + 43,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s154 : XPow fSeventeenA2 1504401478078582967875904355817
    (48*X^33 + 3*X^32 + 54*X^31 + 47*X^30 + 19*X^29 + 48*X^28 + 46*X^27 + 65*X^26 + 54*X^25 + 59*X^24 +
      3*X^23 + 32*X^22 + 40*X^21 + 12*X^20 + 63*X^19 + 47*X^18 + 58*X^17 + 44*X^16 + 33*X^15 +
      3*X^14 + 28*X^13 + 33*X^12 + 42*X^11 + 59*X^10 + 54*X^8 + 54*X^7 + 26*X^6 + 63*X^5 + 41*X^4 +
      57*X^3 + 34*X^2 + 57*X + 28) :=
  mul_step (by norm_num) pSeventeenA2s153 pSeventeenA21 ⟨
    33,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s155 : XPow fSeventeenA2 3008802956157165935751808711634
    (11*X^33 + 58*X^32 + 29*X^31 + 5*X^30 + 58*X^29 + 15*X^28 + 24*X^27 + 13*X^26 + 48*X^25 + 57*X^24 +
      57*X^23 + 11*X^22 + 43*X^21 + 23*X^20 + 40*X^19 + 55*X^18 + 9*X^17 + 34*X^16 + 40*X^15 +
      31*X^14 + 18*X^13 + 31*X^12 + 38*X^11 + 55*X^10 + 24*X^9 + 42*X^8 + 41*X^7 + 11*X^6 + 49*X^5 +
      24*X^4 + 22*X^3 + 19*X^2 + 62*X + 10) :=
  sq_step (by norm_num) pSeventeenA2s154 ⟨
    26*X^32 + 25*X^31 + X^30 + 4*X^29 + 23*X^28 + 46*X^27 + 16*X^26 + 65*X^25 + 36*X^24 + 14*X^23 +
      34*X^22 + 45*X^21 + 46*X^20 + 17*X^19 + 3*X^18 + 28*X^17 + 25*X^16 + X^15 + 34*X^14 + 18*X^13 +
      13*X^12 + 56*X^11 + 26*X^10 + 17*X^9 + 62*X^8 + 48*X^7 + 60*X^6 + 2*X^5 + 11*X^4 + 38*X^3 +
      38*X^2 + 49*X + 21,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s156 : XPow fSeventeenA2 3008802956157165935751808711635
    (6*X^33 + 47*X^32 + 43*X^31 + 14*X^30 + 19*X^29 + 9*X^28 + 2*X^27 + 36*X^26 + 52*X^25 + 37*X^24 +
      4*X^23 + 64*X^22 + 45*X^21 + 33*X^20 + 48*X^19 + 63*X^18 + 52*X^17 + 58*X^16 + 30*X^15 +
      25*X^14 + 24*X^13 + 49*X^12 + 26*X^11 + X^10 + 5*X^9 + 30*X^8 + 39*X^7 + 61*X^6 + 26*X^5 +
      60*X^4 + 66*X^3 + 11*X^2 + 12*X + 54) :=
  mul_step (by norm_num) pSeventeenA2s155 pSeventeenA21 ⟨
    11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s157 : XPow fSeventeenA2 6017605912314331871503617423270
    (41*X^33 + 63*X^32 + 26*X^31 + 10*X^30 + 25*X^29 + 43*X^28 + 30*X^27 + 20*X^26 + 40*X^25 + 33*X^24 +
      51*X^23 + 8*X^22 + 12*X^21 + 2*X^20 + 48*X^19 + 46*X^18 + 21*X^17 + 32*X^16 + X^15 + 61*X^14 +
      32*X^13 + 58*X^12 + 64*X^11 + 13*X^10 + 16*X^9 + 49*X^8 + 50*X^7 + 49*X^6 + 6*X^5 + 11*X^4 +
      22*X^3 + 19*X^2 + 56*X + 64) :=
  sq_step (by norm_num) pSeventeenA2s156 ⟨
    36*X^32 + 4*X^31 + 18*X^30 + 47*X^29 + 49*X^28 + 18*X^27 + 3*X^26 + 36*X^25 + 9*X^24 + 4*X^23 +
      32*X^22 + 48*X^21 + 5*X^20 + 9*X^19 + 8*X^18 + 7*X^17 + 6*X^16 + 27*X^15 + 65*X^14 + 35*X^13 +
      52*X^12 + 62*X^11 + 54*X^9 + 38*X^8 + 38*X^7 + 9*X^6 + 37*X^5 + 49*X^4 + 26*X^3 + 21*X^2 + 2*X +
      27,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s158 : XPow fSeventeenA2 6017605912314331871503617423271
    (58*X^33 + 20*X^32 + 42*X^31 + 62*X^30 + 64*X^29 + 35*X^28 + 46*X^27 + 44*X^26 + 57*X^25 + 13*X^24 +
      55*X^23 + 5*X^22 + 17*X^21 + 28*X^20 + 26*X^19 + 3*X^18 + 26*X^17 + 62*X^16 + 39*X^15 +
      52*X^14 + 38*X^13 + 38*X^12 + 45*X^11 + 46*X^10 + 39*X^9 + 9*X^8 + 62*X^7 + 2*X^6 + 55*X^5 +
      54*X^4 + 48*X^3 + 6*X^2 + 41*X + 49) :=
  mul_step (by norm_num) pSeventeenA2s157 pSeventeenA21 ⟨
    41,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s159 : XPow fSeventeenA2 12035211824628663743007234846542
    (14*X^33 + 33*X^32 + 20*X^31 + 25*X^30 + 48*X^29 + 2*X^28 + 41*X^27 + 21*X^26 + 4*X^25 + 54*X^24 +
      X^23 + 14*X^22 + 29*X^21 + 31*X^20 + 26*X^19 + 24*X^18 + 66*X^17 + 60*X^16 + 18*X^15 + 54*X^14 +
      47*X^13 + 46*X^12 + 28*X^11 + 37*X^10 + 33*X^9 + 54*X^8 + 25*X^7 + 6*X^6 + X^5 + 60*X^4 +
      34*X^3 + 22*X^2 + 58*X + 21) :=
  sq_step (by norm_num) pSeventeenA2s158 ⟨
    14*X^32 + 55*X^31 + 16*X^30 + 42*X^29 + 63*X^28 + 31*X^27 + 12*X^26 + 62*X^25 + 22*X^24 + 34*X^23 +
      X^21 + 19*X^20 + 21*X^19 + 40*X^18 + 55*X^17 + 7*X^16 + 46*X^15 + 4*X^14 + 54*X^13 + 11*X^12 +
      21*X^11 + 36*X^10 + 6*X^9 + 52*X^8 + 41*X^7 + 25*X^6 + 48*X^5 + 16*X^4 + 27*X^3 + 5*X^2 + 64*X +
      9,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s160 : XPow fSeventeenA2 24070423649257327486014469693084
    (47*X^33 + 36*X^32 + 28*X^31 + 26*X^30 + 2*X^29 + 9*X^28 + 25*X^27 + 59*X^26 + 18*X^25 + 6*X^24 +
      24*X^23 + 22*X^22 + 52*X^21 + 8*X^20 + 6*X^19 + 18*X^18 + 19*X^17 + 60*X^16 + 62*X^15 + 8*X^14 +
      36*X^13 + 58*X^12 + 18*X^11 + 66*X^10 + 42*X^9 + 34*X^8 + 40*X^7 + 34*X^6 + 4*X^5 + 41*X^4 +
      36*X^3 + 15*X^2 + 25*X + 29) :=
  sq_step (by norm_num) pSeventeenA2s159 ⟨
    62*X^32 + 34*X^31 + 24*X^29 + X^28 + 52*X^27 + 4*X^26 + 60*X^25 + 12*X^24 + 9*X^23 + 17*X^22 +
      53*X^21 + 39*X^20 + 13*X^19 + 60*X^18 + 65*X^17 + 37*X^16 + 44*X^15 + 49*X^14 + 65*X^13 +
      17*X^12 + 12*X^11 + 12*X^10 + 4*X^9 + 37*X^8 + X^7 + 16*X^6 + 65*X^5 + 50*X^4 + 20*X^3 +
      45*X^2 + 29*X + 60,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s161 : XPow fSeventeenA2 48140847298514654972028939386168
    (7*X^33 + 30*X^32 + 65*X^31 + 33*X^30 + 12*X^29 + 61*X^28 + 10*X^27 + 36*X^26 + 21*X^25 + 61*X^24 +
      55*X^23 + 51*X^22 + 39*X^21 + 5*X^20 + 56*X^19 + 53*X^18 + 2*X^17 + 12*X^16 + 25*X^15 +
      31*X^14 + 36*X^13 + 4*X^12 + 14*X^11 + 52*X^10 + 6*X^9 + 9*X^8 + 42*X^7 + 35*X^6 + 65*X^5 +
      34*X^4 + 49*X^3 + 61*X^2 + 13*X + 41) :=
  sq_step (by norm_num) pSeventeenA2s160 ⟨
    65*X^32 + 13*X^31 + 26*X^30 + 33*X^29 + 6*X^28 + 48*X^27 + 11*X^26 + 24*X^25 + 46*X^24 + 7*X^23 +
      22*X^22 + 44*X^21 + 40*X^20 + 11*X^19 + 40*X^18 + 25*X^17 + 10*X^16 + 57*X^15 + 49*X^14 +
      44*X^13 + 29*X^12 + 48*X^11 + 58*X^10 + 20*X^9 + 27*X^8 + 61*X^6 + 5*X^5 + 4*X^4 + 64*X^3 +
      24*X^2 + 32*X + 43,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s162 : XPow fSeventeenA2 96281694597029309944057878772336
    (5*X^33 + 25*X^32 + 24*X^31 + 41*X^30 + 6*X^29 + 51*X^28 + 18*X^27 + 23*X^26 + 26*X^25 + 48*X^24 +
      48*X^23 + 43*X^22 + 36*X^21 + 5*X^20 + 53*X^19 + 52*X^18 + 57*X^17 + 24*X^16 + 7*X^15 +
      23*X^14 + 57*X^13 + 40*X^12 + 61*X^11 + 47*X^10 + 15*X^9 + 49*X^8 + 61*X^7 + 46*X^6 + 12*X^5 +
      48*X^4 + 32*X^3 + 20*X^2 + X + 42) :=
  sq_step (by norm_num) pSeventeenA2s161 ⟨
    49*X^32 + 30*X^31 + 49*X^30 + 12*X^29 + 6*X^27 + 34*X^26 + 41*X^25 + 47*X^24 + 26*X^23 + 49*X^22 +
      7*X^21 + 14*X^20 + 66*X^19 + 62*X^18 + 62*X^17 + 38*X^16 + 3*X^15 + 28*X^14 + 37*X^13 +
      64*X^12 + 17*X^11 + X^10 + 2*X^9 + 23*X^8 + 64*X^7 + 46*X^6 + 4*X^5 + 33*X^4 + 14*X^3 + 52*X^2 +
      33*X + 52,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s163 : XPow fSeventeenA2 96281694597029309944057878772337
    (44*X^33 + 20*X^32 + 40*X^31 + 53*X^30 + 65*X^29 + 66*X^28 + 18*X^27 + 51*X^26 + 64*X^25 + 45*X^24 +
      52*X^23 + 9*X^22 + 15*X^21 + 62*X^20 + 61*X^19 + 45*X^18 + 20*X^17 + 3*X^16 + 53*X^15 +
      48*X^14 + 49*X^13 + 66*X^12 + 46*X^11 + 35*X^10 + 20*X^9 + 56*X^8 + 10*X^7 + 54*X^6 + 55*X^5 +
      31*X^4 + 17*X^3 + 57*X^2 + 49*X + 55) :=
  mul_step (by norm_num) pSeventeenA2s162 pSeventeenA21 ⟨
    5,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s164 : XPow fSeventeenA2 192563389194058619888115757544674
    (27*X^33 + 17*X^32 + 24*X^31 + 52*X^30 + 22*X^29 + 17*X^28 + 15*X^27 + 12*X^26 + 40*X^25 + 22*X^24 +
      51*X^23 + 2*X^22 + 52*X^21 + 5*X^20 + 54*X^19 + 40*X^18 + 10*X^17 + 6*X^16 + 49*X^15 + 29*X^14 +
      46*X^13 + 20*X^12 + 41*X^11 + 62*X^10 + 17*X^9 + 27*X^8 + 47*X^7 + 64*X^6 + 32*X^5 + 6*X^4 +
      32*X^3 + 25*X^2 + 46*X + 18) :=
  sq_step (by norm_num) pSeventeenA2s163 ⟨
    60*X^32 + 45*X^31 + 23*X^30 + 59*X^29 + 57*X^28 + 44*X^27 + 62*X^26 + 66*X^25 + 21*X^24 + 17*X^23 +
      32*X^22 + 29*X^21 + 29*X^20 + 58*X^19 + 2*X^18 + 3*X^17 + 17*X^16 + 58*X^15 + 24*X^14 +
      13*X^13 + 42*X^12 + 17*X^11 + 56*X^10 + 47*X^9 + 14*X^8 + 40*X^7 + 58*X^6 + 63*X^5 + 40*X^4 +
      10*X^3 + 12*X^2 + 10*X + 19,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s165 : XPow fSeventeenA2 192563389194058619888115757544675
    (66*X^33 + 56*X^32 + 60*X^31 + 48*X^30 + 39*X^29 + 33*X^28 + 52*X^27 + 41*X^26 + 28*X^25 + 8*X^24 +
      64*X^23 + 59*X^21 + 49*X^20 + 35*X^19 + 39*X^18 + 38*X^17 + 14*X^16 + 57*X^15 + 51*X^14 +
      15*X^13 + X^12 + 3*X^11 + 58*X^10 + 58*X^9 + 20*X^8 + 17*X^7 + 31*X^6 + 17*X^5 + 40*X^4 +
      49*X^3 + 29*X + 29) :=
  mul_step (by norm_num) pSeventeenA2s164 pSeventeenA21 ⟨
    27,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s166 : XPow fSeventeenA2 385126778388117239776231515089350
    (3*X^33 + 34*X^32 + 47*X^31 + 4*X^30 + 39*X^29 + 42*X^28 + 53*X^27 + 47*X^26 + 66*X^25 + 30*X^24 +
      10*X^23 + 13*X^22 + 24*X^21 + 65*X^20 + 66*X^19 + 50*X^18 + 7*X^17 + 33*X^16 + 27*X^15 +
      47*X^14 + 51*X^13 + 51*X^12 + 9*X^11 + 45*X^10 + 21*X^9 + X^8 + 17*X^7 + 16*X^6 + 28*X^5 +
      11*X^4 + 21*X^3 + 8*X^2 + 36*X + 36) :=
  sq_step (by norm_num) pSeventeenA2s165 ⟨
    X^32 + 66*X^31 + 50*X^30 + 61*X^29 + 41*X^28 + 22*X^27 + 23*X^26 + 60*X^25 + 16*X^24 + X^23 +
      55*X^22 + 23*X^21 + 17*X^20 + 20*X^19 + 47*X^18 + 56*X^17 + 46*X^16 + 57*X^15 + 20*X^14 +
      33*X^13 + 37*X^12 + 15*X^11 + 41*X^10 + 60*X^9 + 6*X^8 + 41*X^7 + 31*X^6 + 57*X^5 + 32*X^4 +
      47*X^3 + 16*X^2 + 64*X + 6,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s167 : XPow fSeventeenA2 770253556776234479552463030178700
    (53*X^33 + 20*X^32 + 31*X^31 + 52*X^30 + 38*X^29 + 4*X^28 + 18*X^27 + 16*X^26 + 40*X^25 + 37*X^24 +
      31*X^23 + 30*X^22 + 38*X^21 + 44*X^20 + 36*X^19 + 57*X^18 + 34*X^17 + 20*X^16 + 49*X^15 +
      65*X^14 + 28*X^13 + 49*X^12 + 50*X^11 + 14*X^10 + 49*X^9 + 17*X^8 + 63*X^7 + 22*X^6 + 16*X^5 +
      9*X^4 + 6*X^3 + 57*X^2 + 10*X + 66) :=
  sq_step (by norm_num) pSeventeenA2s166 ⟨
    9*X^32 + 64*X^31 + 66*X^30 + 41*X^29 + 49*X^28 + 27*X^27 + 52*X^26 + 14*X^25 + 63*X^24 + 28*X^23 +
      61*X^22 + 63*X^21 + 33*X^20 + 43*X^19 + X^18 + 26*X^17 + 6*X^16 + 16*X^15 + 64*X^14 + 31*X^13 +
      22*X^12 + 51*X^11 + 16*X^10 + 41*X^9 + 7*X^8 + 59*X^7 + 24*X^6 + 23*X^5 + 16*X^4 + 61*X^3 +
      12*X^2 + 32*X + 10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s168 : XPow fSeventeenA2 1540507113552468959104926060357400
    (58*X^33 + X^32 + 43*X^31 + 31*X^30 + 38*X^29 + 44*X^28 + 63*X^27 + 9*X^26 + 50*X^25 + 23*X^24 +
      35*X^23 + 20*X^22 + 62*X^21 + 32*X^20 + 44*X^19 + 63*X^18 + 13*X^17 + 28*X^16 + 40*X^15 +
      53*X^14 + 13*X^13 + 24*X^12 + 62*X^11 + 18*X^9 + 42*X^8 + 56*X^7 + 21*X^6 + 22*X^5 + 12*X^4 +
      36*X^3 + 47*X^2 + 11*X + 58) :=
  sq_step (by norm_num) pSeventeenA2s167 ⟨
    62*X^32 + 24*X^31 + 56*X^30 + 59*X^29 + 41*X^28 + 50*X^27 + 47*X^26 + 15*X^25 + 7*X^24 + 32*X^23 +
      52*X^22 + 33*X^21 + 3*X^20 + 64*X^19 + 63*X^18 + 28*X^17 + 33*X^16 + 4*X^15 + 13*X^14 +
      42*X^13 + 46*X^12 + 49*X^11 + 11*X^10 + 25*X^9 + 52*X^8 + 54*X^7 + 20*X^5 + 60*X^4 + 53*X^3 +
      66*X^2 + 50*X + 60,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s169 : XPow fSeventeenA2 1540507113552468959104926060357401
    (7*X^33 + 10*X^32 + 6*X^31 + 7*X^30 + 59*X^29 + 57*X^28 + 18*X^27 + 5*X^26 + 21*X^25 + 27*X^24 +
      44*X^23 + 57*X^22 + 14*X^21 + X^20 + 20*X^19 + 48*X^18 + 62*X^17 + 7*X^16 + 66*X^15 + 56*X^14 +
      48*X^13 + 53*X^12 + 42*X^11 + 49*X^10 + 54*X^9 + 65*X^8 + 59*X^7 + 53*X^5 + 11*X^4 + 39*X^3 +
      4*X^2 + 32*X + 35) :=
  mul_step (by norm_num) pSeventeenA2s168 pSeventeenA21 ⟨
    58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s170 : XPow fSeventeenA2 3081014227104937918209852120714802
    (17*X^33 + 2*X^32 + 29*X^31 + 41*X^30 + 43*X^29 + 42*X^28 + 45*X^27 + 64*X^26 + 21*X^25 + 44*X^24 +
      14*X^23 + 17*X^22 + 41*X^21 + 51*X^20 + 24*X^19 + 60*X^18 + 41*X^17 + 50*X^16 + 7*X^15 +
      36*X^14 + 9*X^13 + 52*X^12 + 41*X^11 + 52*X^10 + 63*X^9 + 15*X^8 + 41*X^7 + 4*X^6 + 2*X^5 +
      25*X^4 + 29*X^3 + 17*X^2 + 32*X + 2) :=
  sq_step (by norm_num) pSeventeenA2s169 ⟨
    49*X^32 + 18*X^31 + 39*X^30 + 7*X^29 + 34*X^28 + 32*X^27 + 34*X^26 + 4*X^25 + 9*X^24 + 49*X^23 +
      8*X^22 + 23*X^21 + 9*X^20 + 20*X^19 + 27*X^18 + 31*X^17 + 30*X^16 + 31*X^15 + 13*X^14 +
      61*X^13 + 29*X^11 + 42*X^10 + 28*X^9 + 24*X^8 + 18*X^7 + 15*X^6 + 11*X^5 + 57*X^4 + 23*X^3 +
      51*X^2 + 8*X + 35,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s171 : XPow fSeventeenA2 6162028454209875836419704241429604
    (52*X^33 + 61*X^32 + 37*X^31 + 33*X^30 + 16*X^28 + 53*X^27 + 10*X^26 + 44*X^25 + 17*X^24 + 7*X^23 +
      11*X^22 + 41*X^21 + 66*X^20 + 49*X^19 + 45*X^18 + 14*X^17 + 64*X^16 + 16*X^15 + 44*X^14 +
      43*X^13 + 21*X^12 + 8*X^11 + 32*X^10 + 26*X^9 + 56*X^8 + 32*X^7 + 33*X^6 + 65*X^5 + 45*X^4 +
      11*X^3 + 55*X^2 + 25*X + 29) :=
  sq_step (by norm_num) pSeventeenA2s170 ⟨
    21*X^32 + 54*X^31 + 26*X^30 + 7*X^29 + 33*X^28 + 36*X^27 + 40*X^26 + 39*X^25 + 18*X^24 + 19*X^23 +
      50*X^22 + 2*X^21 + 63*X^20 + 36*X^19 + 38*X^18 + 12*X^17 + 17*X^16 + 19*X^15 + 22*X^14 +
      15*X^13 + 19*X^12 + 40*X^11 + 60*X^10 + 18*X^9 + 40*X^8 + 26*X^7 + X^5 + 52*X^4 + 36*X^3 +
      22*X^2 + 28*X + 51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s172 : XPow fSeventeenA2 12324056908419751672839408482859208
    (11*X^33 + 63*X^32 + 42*X^31 + 59*X^30 + 12*X^29 + 22*X^28 + 6*X^27 + 6*X^26 + 13*X^25 + 12*X^24 +
      53*X^23 + 18*X^22 + 18*X^21 + 19*X^20 + 26*X^19 + 14*X^18 + 5*X^17 + 10*X^16 + 54*X^15 +
      19*X^14 + 36*X^13 + 41*X^12 + 18*X^11 + 2*X^10 + 28*X^9 + 22*X^8 + 44*X^7 + 38*X^6 + 30*X^5 +
      2*X^4 + 33*X^3 + 37*X^2 + 54*X + 3) :=
  sq_step (by norm_num) pSeventeenA2s171 ⟨
    24*X^32 + 30*X^31 + 66*X^30 + 61*X^29 + 45*X^28 + 35*X^27 + 5*X^26 + 6*X^25 + 3*X^24 + 52*X^23 +
      2*X^22 + 41*X^21 + X^20 + 16*X^19 + 57*X^18 + 20*X^17 + 13*X^16 + 50*X^15 + 14*X^14 + 40*X^13 +
      63*X^12 + 49*X^11 + 17*X^10 + 42*X^9 + 47*X^8 + 38*X^7 + 63*X^6 + 61*X^5 + 3*X^4 + 9*X^3 +
      39*X^2 + 53*X + 3,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s173 : XPow fSeventeenA2 12324056908419751672839408482859209
    (11*X^33 + 60*X^32 + 30*X^31 + 35*X^30 + 26*X^29 + 58*X^28 + 62*X^27 + X^26 + 7*X^25 + 33*X^24 +
      11*X^23 + 39*X^22 + 41*X^21 + 19*X^20 + 7*X^19 + 59*X^18 + 28*X^17 + 5*X^16 + 18*X^15 +
      43*X^14 + 34*X^13 + 29*X^12 + 40*X^11 + 5*X^10 + 52*X^9 + 33*X^8 + 66*X^7 + 42*X^6 + 4*X^5 +
      4*X^4 + 17*X^3 + 3*X^2 + 5*X + 54) :=
  mul_step (by norm_num) pSeventeenA2s172 pSeventeenA21 ⟨
    11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s174 : XPow fSeventeenA2 24648113816839503345678816965718418
    (33*X^33 + 23*X^32 + 42*X^31 + 14*X^29 + 17*X^28 + 44*X^27 + 25*X^26 + 56*X^25 + 5*X^24 + 13*X^23 +
      50*X^22 + 50*X^21 + 53*X^20 + 34*X^19 + 19*X^18 + 7*X^17 + 56*X^16 + 31*X^15 + 13*X^14 +
      28*X^13 + 15*X^12 + 42*X^11 + 35*X^10 + 39*X^9 + 17*X^8 + 14*X^7 + X^6 + 63*X^5 + 31*X^4 +
      59*X^3 + 24*X + 3) :=
  sq_step (by norm_num) pSeventeenA2s173 ⟨
    54*X^32 + 11*X^31 + 51*X^30 + 15*X^29 + 43*X^28 + 31*X^27 + 24*X^26 + 50*X^25 + 26*X^24 + 50*X^22 +
      52*X^21 + 44*X^20 + 28*X^19 + 33*X^18 + 52*X^17 + 3*X^16 + 64*X^15 + 31*X^14 + 26*X^13 +
      9*X^12 + 12*X^11 + 8*X^10 + 61*X^9 + 11*X^8 + 19*X^7 + 66*X^6 + 45*X^5 + 65*X^4 + 51*X^3 +
      15*X^2 + 59*X + 58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s175 : XPow fSeventeenA2 49296227633679006691357633931436836
    (65*X^33 + 28*X^32 + 14*X^31 + 45*X^30 + 58*X^29 + 39*X^28 + 42*X^27 + 34*X^26 + 66*X^25 + 6*X^24 +
      X^23 + 65*X^22 + 43*X^21 + 13*X^20 + 62*X^19 + 5*X^18 + 34*X^17 + 45*X^16 + 21*X^15 + 55*X^14 +
      28*X^13 + 23*X^12 + 11*X^11 + 19*X^10 + 28*X^9 + 25*X^8 + 15*X^7 + 4*X^6 + 26*X^5 + 40*X^4 +
      61*X^3 + 62*X^2 + 21*X + 59) :=
  sq_step (by norm_num) pSeventeenA2s174 ⟨
    17*X^32 + 55*X^31 + 66*X^30 + 45*X^29 + 7*X^28 + 30*X^27 + 3*X^26 + 16*X^25 + 38*X^24 + 44*X^23 +
      10*X^22 + 53*X^21 + 53*X^20 + 36*X^19 + 20*X^18 + 2*X^17 + 43*X^16 + 50*X^15 + 10*X^14 +
      66*X^13 + 14*X^12 + 62*X^11 + 8*X^10 + 53*X^9 + 27*X^8 + 2*X^7 + 35*X^6 + 4*X^5 + 15*X^4 +
      43*X^3 + 8*X^2 + 27*X + 35,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s176 : XPow fSeventeenA2 49296227633679006691357633931436837
    (7*X^33 + 29*X^32 + 32*X^31 + 66*X^30 + 20*X^29 + 63*X^28 + 36*X^27 + 56*X^26 + 13*X^25 + 29*X^24 +
      48*X^23 + 27*X^22 + 9*X^21 + 45*X^20 + 55*X^19 + 12*X^18 + 60*X^17 + 36*X^16 + 43*X^15 +
      45*X^14 + 6*X^13 + 9*X^12 + 6*X^11 + 20*X^10 + 50*X^9 + 17*X^8 + 5*X^7 + 36*X^6 + 64*X^5 +
      48*X^4 + 23*X^3 + 12*X^2 + 16*X + 45) :=
  mul_step (by norm_num) pSeventeenA2s175 pSeventeenA21 ⟨
    65,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s177 : XPow fSeventeenA2 98592455267358013382715267862873674
    (3*X^33 + 54*X^32 + 62*X^31 + 59*X^30 + 8*X^29 + 22*X^27 + 57*X^26 + 51*X^25 + 34*X^24 + 58*X^23 +
      38*X^22 + 25*X^21 + 57*X^20 + 62*X^19 + 19*X^18 + 6*X^17 + 22*X^16 + 26*X^15 + 29*X^14 +
      42*X^13 + 33*X^12 + 15*X^10 + 5*X^9 + 46*X^8 + 22*X^7 + 56*X^6 + 14*X^5 + 43*X^4 + 40*X^3 +
      14*X^2 + 55*X + 41) :=
  sq_step (by norm_num) pSeventeenA2s176 ⟨
    49*X^32 + 16*X^31 + 51*X^30 + 30*X^29 + 48*X^28 + 42*X^27 + 23*X^26 + 14*X^25 + 12*X^24 + 24*X^23 +
      49*X^22 + 25*X^21 + 13*X^20 + 28*X^19 + 36*X^18 + 61*X^17 + 46*X^16 + 60*X^14 + 27*X^13 +
      9*X^12 + 17*X^11 + 48*X^10 + 45*X^9 + 25*X^8 + 30*X^7 + 53*X^6 + 22*X^5 + 44*X^4 + 5*X^3 +
      11*X^2 + 45*X + 45,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s178 : XPow fSeventeenA2 98592455267358013382715267862873675
    (52*X^33 + 6*X^32 + 45*X^31 + 63*X^30 + 62*X^29 + 24*X^28 + 54*X^27 + 66*X^26 + 57*X^25 + 16*X^24 +
      30*X^23 + 49*X^22 + 63*X^21 + 54*X^20 + 11*X^19 + 39*X^18 + 33*X^17 + 37*X^16 + 47*X^15 +
      50*X^14 + 25*X^13 + 3*X^12 + X^11 + 17*X^10 + 42*X^9 + 19*X^8 + 21*X^7 + 66*X^6 + 7*X^5 +
      26*X^4 + 39*X^3 + 35*X^2 + 5*X + 33) :=
  mul_step (by norm_num) pSeventeenA2s177 pSeventeenA21 ⟨
    3,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s179 : XPow fSeventeenA2 197184910534716026765430535725747350
    (54*X^33 + 62*X^32 + 45*X^31 + 47*X^30 + 43*X^29 + 26*X^28 + 23*X^27 + 60*X^26 + 28*X^25 + 27*X^24 +
      57*X^23 + 19*X^22 + 61*X^21 + 39*X^20 + X^19 + 19*X^18 + 13*X^17 + 27*X^16 + 39*X^15 + 9*X^14 +
      30*X^13 + 44*X^12 + 34*X^11 + 50*X^10 + 20*X^9 + 15*X^8 + X^7 + 2*X^6 + 25*X^5 + 62*X^4 +
      31*X^3 + 10*X^2 + 3*X + 21) :=
  sq_step (by norm_num) pSeventeenA2s178 ⟨
    24*X^32 + 5*X^31 + 66*X^30 + 31*X^29 + 18*X^28 + 23*X^27 + 50*X^26 + 22*X^25 + 8*X^24 + 18*X^23 +
      24*X^22 + 50*X^21 + 3*X^20 + 49*X^19 + 61*X^18 + 33*X^17 + 2*X^16 + 3*X^15 + 15*X^14 + 15*X^13 +
      42*X^12 + 54*X^11 + 24*X^10 + 28*X^9 + 62*X^8 + 44*X^7 + 29*X^6 + 49*X^5 + 10*X^4 + 24*X^3 +
      11*X^2 + 5*X + 43,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s180 : XPow fSeventeenA2 197184910534716026765430535725747351
    (26*X^33 + 42*X^32 + 63*X^31 + 28*X^30 + 3*X^29 + 59*X^28 + 6*X^27 + 30*X^26 + 39*X^25 + 38*X^24 +
      9*X^23 + 24*X^22 + 13*X^21 + 58*X^20 + 9*X^19 + 4*X^18 + 24*X^17 + 36*X^16 + 65*X^15 + 40*X^14 +
      34*X^13 + 21*X^12 + 66*X^11 + 35*X^10 + 10*X^9 + 14*X^8 + 42*X^7 + 23*X^6 + 17*X^5 + 47*X^4 +
      58*X^3 + 45*X^2 + 43*X + 58) :=
  mul_step (by norm_num) pSeventeenA2s179 pSeventeenA21 ⟨
    54,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s181 : XPow fSeventeenA2 394369821069432053530861071451494702
    (8*X^33 + 15*X^32 + 39*X^31 + 34*X^30 + 25*X^29 + 37*X^28 + 56*X^27 + 6*X^26 + 65*X^25 + 19*X^24 +
      16*X^23 + 15*X^22 + 25*X^21 + 46*X^20 + X^18 + 55*X^17 + 6*X^16 + 19*X^15 + 20*X^14 + 14*X^13 +
      45*X^12 + 64*X^11 + 53*X^10 + 19*X^9 + 45*X^8 + 32*X^7 + 60*X^6 + 56*X^5 + 32*X^4 + 43*X^3 +
      62*X^2 + 32*X + 9) :=
  sq_step (by norm_num) pSeventeenA2s180 ⟨
    6*X^32 + 36*X^31 + 13*X^30 + 54*X^29 + 21*X^28 + 28*X^27 + 9*X^26 + 65*X^25 + 19*X^24 + 47*X^23 +
      17*X^22 + 17*X^21 + 8*X^20 + 56*X^19 + 10*X^18 + 16*X^17 + 15*X^16 + 30*X^15 + 15*X^14 +
      56*X^13 + 6*X^12 + 51*X^11 + 43*X^10 + 52*X^9 + 12*X^8 + 45*X^7 + 55*X^6 + 66*X^5 + 17*X^4 +
      65*X^3 + 45*X^2 + 39*X + 30,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s182 : XPow fSeventeenA2 788739642138864107061722142902989404
    (9*X^33 + 13*X^32 + 22*X^31 + 6*X^30 + 16*X^29 + 31*X^28 + 37*X^27 + 24*X^26 + 29*X^25 + 32*X^24 +
      46*X^23 + 42*X^22 + 60*X^21 + 45*X^20 + 37*X^19 + 26*X^18 + 14*X^17 + 19*X^16 + 9*X^15 +
      57*X^14 + 58*X^13 + 53*X^12 + 28*X^11 + 65*X^10 + 33*X^9 + 62*X^8 + 14*X^7 + 14*X^6 + 43*X^5 +
      29*X^4 + 65*X^3 + 14*X^2 + 54*X + 23) :=
  sq_step (by norm_num) pSeventeenA2s181 ⟨
    64*X^32 + 41*X^31 + 29*X^30 + 50*X^29 + 43*X^28 + 13*X^27 + 62*X^26 + 9*X^25 + 44*X^24 + 50*X^23 +
      27*X^22 + 61*X^21 + 3*X^20 + 55*X^19 + 54*X^18 + 37*X^17 + 54*X^16 + 37*X^15 + 65*X^14 +
      58*X^13 + 28*X^12 + 52*X^11 + 61*X^10 + 23*X^9 + 31*X^8 + 35*X^7 + 40*X^6 + 36*X^5 + 26*X^4 +
      51*X^3 + 50*X^2 + 52*X + 13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s183 : XPow fSeventeenA2 788739642138864107061722142902989405
    (7*X^33 + 55*X^32 + 31*X^31 + 47*X^30 + 16*X^29 + 43*X^28 + 15*X^27 + 7*X^26 + 34*X^25 + 54*X^24 +
      18*X^23 + 65*X^22 + 63*X^21 + 13*X^20 + 2*X^19 + 46*X^18 + 52*X^17 + 42*X^16 + 44*X^15 +
      15*X^14 + 29*X^13 + 37*X^12 + 23*X^11 + 2*X^10 + 50*X^9 + 5*X^8 + 43*X^7 + 65*X^6 + 55*X^5 +
      23*X^4 + 22*X^3 + 61*X^2 + 49*X + 32) :=
  mul_step (by norm_num) pSeventeenA2s182 pSeventeenA21 ⟨
    9,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s184 : XPow fSeventeenA2 1577479284277728214123444285805978810
    (29*X^33 + 41*X^32 + 12*X^31 + 64*X^30 + 60*X^29 + 50*X^28 + 45*X^27 + 57*X^26 + 10*X^25 + 41*X^24 +
      31*X^23 + 15*X^22 + 27*X^21 + 51*X^20 + 49*X^19 + 64*X^18 + 44*X^17 + 45*X^16 + 37*X^15 + X^14 +
      15*X^13 + 58*X^12 + 16*X^11 + 51*X^10 + 27*X^9 + 52*X^8 + 15*X^7 + 31*X^6 + 21*X^4 + 28*X^3 +
      44*X^2 + 8*X + 11) :=
  sq_step (by norm_num) pSeventeenA2s183 ⟨
    49*X^32 + 45*X^31 + 13*X^30 + 65*X^29 + 35*X^28 + 32*X^27 + 56*X^26 + 40*X^25 + 54*X^24 + 37*X^23 +
      48*X^22 + 35*X^21 + 56*X^20 + 63*X^19 + 33*X^18 + 20*X^17 + X^16 + 48*X^15 + 62*X^14 + 44*X^13 +
      20*X^12 + 21*X^11 + 40*X^10 + 39*X^9 + 45*X^8 + 58*X^7 + 24*X^6 + 23*X^5 + 42*X^4 + 36*X^3 +
      23*X^2 + 36*X + 48,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s185 : XPow fSeventeenA2 1577479284277728214123444285805978811
    (44*X^33 + 29*X^32 + 18*X^31 + 11*X^30 + 24*X^29 + 42*X^28 + 28*X^27 + 21*X^26 + 40*X^25 + 27*X^24 +
      27*X^23 + 58*X^22 + 42*X^21 + 61*X^20 + 9*X^19 + 28*X^18 + 62*X^17 + 54*X^16 + 41*X^15 +
      3*X^14 + 3*X^13 + 45*X^12 + 5*X^11 + 9*X^10 + 58*X^9 + 53*X^8 + 50*X^7 + 56*X^6 + 8*X^5 +
      49*X^4 + 40*X^3 + 38*X^2 + 65*X + 51) :=
  mul_step (by norm_num) pSeventeenA2s184 pSeventeenA21 ⟨
    29,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s186 : XPow fSeventeenA2 3154958568555456428246888571611957622
    (2*X^33 + 47*X^32 + 19*X^31 + 6*X^30 + 44*X^29 + 65*X^28 + 62*X^27 + 44*X^26 + 42*X^25 + 44*X^24 +
      21*X^23 + 22*X^22 + 5*X^21 + 32*X^20 + 64*X^19 + 54*X^18 + 3*X^17 + 31*X^16 + 44*X^15 + 5*X^14 +
      41*X^12 + 36*X^11 + 65*X^10 + 30*X^9 + 19*X^8 + 25*X^7 + 59*X^6 + 4*X^5 + 66*X^4 + 32*X^3 +
      16*X^2 + 11*X + 30) :=
  sq_step (by norm_num) pSeventeenA2s185 ⟨
    60*X^32 + 33*X^31 + 10*X^30 + 15*X^29 + 49*X^28 + 24*X^27 + 50*X^26 + 42*X^25 + 39*X^24 + 51*X^23 +
      21*X^22 + 41*X^21 + 35*X^20 + 16*X^19 + 46*X^18 + 4*X^17 + 56*X^16 + 13*X^15 + 21*X^14 +
      3*X^13 + 64*X^12 + 16*X^11 + 61*X^10 + 30*X^9 + 40*X^8 + 36*X^7 + 54*X^6 + 32*X^5 + 7*X^4 +
      11*X^3 + 48*X^2 + 37*X + 16,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s187 : XPow fSeventeenA2 3154958568555456428246888571611957623
    (X^33 + 4*X^32 + 19*X^31 + 36*X^30 + 17*X^29 + 41*X^28 + 42*X^27 + 52*X^26 + 37*X^25 + 60*X^24 +
      39*X^23 + 21*X^22 + 36*X^21 + 14*X^20 + 4*X^19 + 25*X^18 + 16*X^17 + 29*X^16 + 17*X^15 +
      50*X^14 + 58*X^13 + 38*X^12 + 11*X^11 + 38*X^10 + 61*X^9 + 23*X^8 + 58*X^7 + 61*X^6 + 42*X^5 +
      45*X^4 + 55*X^3 + 20*X^2 + 6*X + 22) :=
  mul_step (by norm_num) pSeventeenA2s186 pSeventeenA21 ⟨
    2,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s188 : XPow fSeventeenA2 6309917137110912856493777143223915246
    (7*X^33 + 10*X^32 + 28*X^31 + 59*X^30 + 48*X^29 + 11*X^28 + 61*X^27 + 15*X^26 + 58*X^25 + 31*X^24 +
      36*X^23 + 12*X^22 + 18*X^21 + 19*X^20 + 66*X^19 + 37*X^18 + 26*X^17 + 9*X^16 + 53*X^15 +
      21*X^14 + 31*X^13 + 63*X^12 + 9*X^11 + 62*X^10 + 48*X^9 + 29*X^8 + 52*X^7 + 27*X^6 + 60*X^5 +
      36*X^4 + 15*X^3 + 42*X^2 + 12*X + 66) :=
  sq_step (by norm_num) pSeventeenA2s187 ⟨
    X^32 + 52*X^31 + 23*X^30 + 15*X^29 + 64*X^28 + 53*X^27 + 5*X^26 + 57*X^25 + 35*X^24 + 52*X^23 +
      41*X^22 + 6*X^21 + 43*X^20 + 33*X^19 + 56*X^18 + 45*X^17 + 24*X^16 + 3*X^15 + 5*X^14 + 52*X^13 +
      37*X^12 + 64*X^11 + 47*X^10 + 58*X^9 + 54*X^8 + 5*X^7 + 12*X^6 + 40*X^5 + 46*X^3 + 63*X^2 +
      27*X + 29,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s189 : XPow fSeventeenA2 12619834274221825712987554286447830492
    (37*X^33 + 66*X^32 + 43*X^31 + 19*X^30 + 46*X^29 + 26*X^28 + 27*X^27 + 8*X^26 + 11*X^25 + 62*X^24 +
      53*X^23 + 60*X^22 + 36*X^21 + 32*X^20 + 66*X^19 + 7*X^18 + 19*X^16 + 34*X^15 + 8*X^14 + 6*X^13 +
      47*X^12 + 9*X^11 + 43*X^10 + 33*X^9 + 22*X^8 + 65*X^7 + 34*X^6 + 36*X^5 + 47*X^4 + 46*X^3 +
      19*X^2 + 50*X + 36) :=
  sq_step (by norm_num) pSeventeenA2s188 ⟨
    49*X^32 + 18*X^31 + 12*X^30 + 54*X^29 + 19*X^28 + 61*X^27 + 29*X^26 + 4*X^25 + 45*X^24 + 9*X^23 +
      33*X^22 + 17*X^21 + 6*X^20 + 66*X^19 + 29*X^18 + 35*X^17 + 62*X^16 + 54*X^15 + 50*X^14 +
      41*X^13 + 16*X^12 + 16*X^11 + 36*X^10 + 66*X^9 + 59*X^8 + 30*X^7 + 6*X^6 + 24*X^5 + 31*X^4 +
      57*X^3 + 55*X^2 + 3*X + 58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s190 : XPow fSeventeenA2 25239668548443651425975108572895660984
    (4*X^33 + 13*X^32 + 41*X^31 + 59*X^30 + 17*X^29 + 9*X^28 + 34*X^27 + 22*X^26 + 29*X^25 + 18*X^24 +
      11*X^23 + 18*X^22 + 22*X^21 + 21*X^20 + 50*X^19 + 66*X^18 + 26*X^17 + 5*X^16 + 15*X^15 +
      7*X^14 + 4*X^13 + 7*X^12 + 60*X^11 + 34*X^10 + 58*X^9 + 63*X^8 + 7*X^7 + 43*X^6 + 12*X^5 +
      29*X^4 + 19*X^3 + 17*X^2 + 38*X + 3) :=
  sq_step (by norm_num) pSeventeenA2s189 ⟨
    29*X^32 + 63*X^31 + 9*X^30 + 25*X^29 + 42*X^28 + 16*X^27 + 4*X^26 + 59*X^25 + 40*X^24 + 8*X^23 +
      27*X^22 + 66*X^21 + 65*X^20 + 5*X^19 + 45*X^18 + 21*X^17 + 7*X^16 + 47*X^15 + 58*X^14 +
      46*X^13 + 32*X^12 + 62*X^11 + 30*X^10 + 13*X^9 + 27*X^8 + X^7 + 48*X^6 + 40*X^5 + 62*X^4 +
      2*X^3 + 5*X^2 + 2*X + 53,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s191 : XPow fSeventeenA2 50479337096887302851950217145791321968
    (21*X^33 + 13*X^32 + 48*X^31 + 41*X^30 + 50*X^29 + 60*X^28 + 56*X^27 + 5*X^26 + 31*X^25 + 40*X^24 +
      27*X^23 + 11*X^22 + X^21 + 60*X^20 + 9*X^19 + 16*X^18 + 56*X^17 + 63*X^16 + 29*X^15 + 36*X^14 +
      16*X^13 + 15*X^12 + 10*X^11 + 3*X^10 + 23*X^9 + 22*X^8 + 26*X^7 + 62*X^6 + 57*X^5 + 17*X^4 +
      32*X^3 + 11*X^2 + 60*X + 52) :=
  sq_step (by norm_num) pSeventeenA2s190 ⟨
    16*X^32 + 4*X^31 + 17*X^30 + 15*X^29 + 60*X^28 + 19*X^27 + 5*X^26 + 27*X^25 + 54*X^24 + 29*X^23 +
      7*X^22 + 4*X^21 + 61*X^20 + 25*X^19 + 37*X^18 + 46*X^17 + 14*X^16 + 3*X^15 + 52*X^14 + 17*X^13 +
      30*X^12 + 10*X^11 + 55*X^10 + 14*X^9 + 37*X^8 + 37*X^7 + 60*X^6 + 64*X^5 + 11*X^4 + 38*X^3 +
      20*X + 10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s192 : XPow fSeventeenA2 100958674193774605703900434291582643936
    (39*X^33 + 31*X^32 + 46*X^30 + 6*X^29 + 52*X^28 + 60*X^27 + 38*X^26 + 21*X^25 + 39*X^24 + 21*X^23 +
      21*X^22 + 41*X^21 + 3*X^20 + 49*X^19 + 5*X^18 + 30*X^17 + 10*X^16 + 13*X^15 + 25*X^14 +
      32*X^13 + 17*X^12 + 29*X^11 + 65*X^10 + 6*X^9 + 29*X^8 + 55*X^7 + 53*X^6 + 28*X^5 + 56*X^4 +
      29*X^3 + 10*X^2 + 37*X + 26) :=
  sq_step (by norm_num) pSeventeenA2s191 ⟨
    39*X^32 + 51*X^31 + 16*X^30 + 61*X^29 + 2*X^28 + 19*X^27 + 64*X^26 + 12*X^25 + 6*X^24 + 19*X^23 +
      20*X^22 + 56*X^21 + 15*X^20 + 43*X^19 + 21*X^18 + 24*X^17 + 21*X^16 + 26*X^15 + 17*X^14 +
      54*X^13 + 33*X^12 + 43*X^11 + 17*X^10 + 2*X^9 + 6*X^8 + 65*X^6 + 52*X^5 + 11*X^4 + 23*X^3 +
      11*X^2 + 26*X + 55,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s193 : XPow fSeventeenA2 201917348387549211407800868583165287872
    (8*X^33 + 54*X^32 + 37*X^31 + 12*X^30 + 16*X^29 + 47*X^28 + 33*X^27 + 59*X^26 + 64*X^25 + 32*X^24 +
      47*X^23 + 33*X^22 + 6*X^21 + 13*X^20 + 17*X^19 + 22*X^18 + 50*X^17 + 36*X^16 + 10*X^15 +
      61*X^14 + 14*X^13 + 15*X^12 + 22*X^11 + 33*X^10 + 61*X^9 + 23*X^8 + 28*X^7 + 55*X^6 + 61*X^5 +
      43*X^4 + 46*X^3 + 56*X^2 + 25*X + 2) :=
  sq_step (by norm_num) pSeventeenA2s192 ⟨
    47*X^32 + 64*X^31 + 41*X^30 + 25*X^29 + 19*X^28 + 6*X^27 + 37*X^26 + 4*X^25 + 44*X^24 + 47*X^23 +
      56*X^22 + 36*X^21 + 64*X^20 + 5*X^19 + X^18 + 59*X^17 + 42*X^16 + 6*X^15 + 25*X^14 + 21*X^13 +
      56*X^12 + 62*X^11 + 18*X^10 + 25*X^9 + 55*X^8 + 45*X^7 + 55*X^6 + 13*X^5 + 34*X^4 + 65*X^3 +
      32*X^2 + 18*X + 24,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s194 : XPow fSeventeenA2 403834696775098422815601737166330575744
    (13*X^33 + 2*X^32 + 2*X^31 + 35*X^30 + 31*X^29 + 56*X^28 + 55*X^27 + 62*X^26 + 17*X^25 + 14*X^24 +
      13*X^23 + 19*X^22 + 65*X^21 + 66*X^20 + 47*X^19 + 66*X^18 + 59*X^17 + 28*X^16 + 17*X^15 +
      65*X^14 + 21*X^13 + 61*X^12 + 35*X^11 + 38*X^10 + 4*X^9 + 42*X^8 + 6*X^7 + 36*X^6 + 18*X^5 +
      28*X^4 + 46*X^3 + 46*X^2 + 17*X + 33) :=
  sq_step (by norm_num) pSeventeenA2s193 ⟨
    64*X^32 + 62*X^31 + 61*X^30 + 56*X^29 + 16*X^28 + 20*X^27 + 24*X^26 + 9*X^25 + 29*X^24 + 52*X^23 +
      9*X^22 + 63*X^21 + 35*X^20 + 54*X^19 + 59*X^18 + 60*X^17 + 60*X^16 + 35*X^15 + 22*X^14 +
      16*X^13 + 39*X^12 + 60*X^11 + 17*X^10 + 28*X^9 + 54*X^8 + 48*X^7 + 62*X^6 + 53*X^5 + 7*X^4 +
      2*X^3 + 47*X^2 + 28*X + 27,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s195 : XPow fSeventeenA2 807669393550196845631203474332661151488
    (58*X^33 + 10*X^32 + 47*X^31 + 33*X^30 + 26*X^29 + 31*X^28 + 18*X^27 + 14*X^26 + 30*X^25 + 8*X^24 +
      26*X^23 + 59*X^22 + 45*X^21 + 20*X^20 + 32*X^19 + 51*X^18 + 23*X^17 + 60*X^16 + 56*X^15 +
      29*X^14 + 2*X^13 + 15*X^12 + 37*X^11 + 30*X^10 + 27*X^9 + 19*X^8 + 2*X^7 + 39*X^6 + 54*X^5 +
      66*X^4 + 9*X^3 + 34*X^2 + 8*X + 53) :=
  sq_step (by norm_num) pSeventeenA2s194 ⟨
    35*X^32 + 51*X^31 + 61*X^30 + 30*X^29 + 61*X^28 + 14*X^27 + 47*X^26 + 9*X^25 + 23*X^24 + 18*X^23 +
      16*X^22 + 43*X^21 + 13*X^20 + 46*X^19 + 33*X^18 + 13*X^17 + 51*X^16 + 40*X^15 + 48*X^14 +
      31*X^13 + 11*X^12 + 66*X^11 + 53*X^10 + 65*X^9 + 66*X^8 + 9*X^7 + 40*X^6 + 44*X^5 + 55*X^4 +
      25*X^3 + 18*X^2 + 59*X + 52,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s196 : XPow fSeventeenA2 807669393550196845631203474332661151489
    (16*X^33 + 14*X^32 + 8*X^31 + 62*X^30 + 46*X^29 + 12*X^28 + 23*X^27 + 52*X^26 + 6*X^25 + 18*X^24 +
      16*X^23 + 40*X^22 + 2*X^21 + 56*X^20 + 8*X^19 + 58*X^18 + 27*X^17 + 23*X^16 + 42*X^15 +
      45*X^14 + 39*X^13 + 28*X^12 + 5*X^11 + 58*X^10 + 31*X^9 + 11*X^8 + 10*X^7 + 32*X^6 + 40*X^5 +
      51*X^4 + 26*X^3 + X^2 + 27*X + 35) :=
  mul_step (by norm_num) pSeventeenA2s195 pSeventeenA21 ⟨
    58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s197 : XPow fSeventeenA2 1615338787100393691262406948665322302978
    (65*X^33 + 65*X^32 + 6*X^31 + 6*X^30 + 45*X^29 + 50*X^28 + 14*X^27 + 35*X^26 + 53*X^25 + 25*X^24 +
      65*X^23 + 3*X^22 + 55*X^21 + 57*X^20 + 21*X^19 + 23*X^18 + X^17 + 56*X^16 + 57*X^15 + 20*X^14 +
      9*X^13 + 51*X^12 + 34*X^11 + 10*X^10 + 23*X^9 + 29*X^8 + 25*X^7 + 37*X^6 + 28*X^5 + 42*X^4 +
      48*X^3 + 52*X^2 + 58*X + 14) :=
  sq_step (by norm_num) pSeventeenA2s196 ⟨
    55*X^32 + 54*X^31 + 37*X^30 + 3*X^29 + 8*X^28 + 23*X^27 + 46*X^26 + 43*X^25 + 10*X^24 + 12*X^23 +
      11*X^22 + 27*X^21 + 54*X^20 + 37*X^19 + 19*X^18 + 50*X^17 + 10*X^16 + 28*X^15 + 3*X^14 +
      41*X^13 + 34*X^12 + 14*X^11 + 48*X^10 + 28*X^9 + 33*X^8 + 66*X^7 + 11*X^6 + 2*X^5 + 46*X^4 +
      45*X^3 + 59*X^2 + 55*X + 30,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s198 : XPow fSeventeenA2 1615338787100393691262406948665322302979
    (44*X^33 + 21*X^32 + 60*X^31 + 53*X^30 + 31*X^29 + 35*X^28 + 37*X^27 + 43*X^26 + 32*X^25 + 26*X^24 +
      53*X^23 + 39*X^22 + 53*X^21 + 4*X^20 + 6*X^19 + 46*X^18 + 4*X^17 + 5*X^16 + 8*X^15 + 26*X^14 +
      34*X^13 + 32*X^12 + 64*X^11 + 15*X^10 + 54*X^9 + 27*X^8 + 38*X^7 + 38*X^6 + 66*X^5 + 35*X^4 +
      13*X^3 + 49*X^2 + 38*X + 45) :=
  mul_step (by norm_num) pSeventeenA2s197 pSeventeenA21 ⟨
    65,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s199 : XPow fSeventeenA2 3230677574200787382524813897330644605958
    (31*X^33 + 5*X^32 + 29*X^31 + 65*X^30 + 61*X^29 + 55*X^28 + 66*X^27 + 34*X^26 + 16*X^25 + 16*X^24 +
      46*X^23 + 2*X^22 + 40*X^21 + 3*X^20 + 64*X^19 + 60*X^18 + 61*X^17 + 46*X^15 + 44*X^14 + X^13 +
      5*X^12 + 57*X^11 + 4*X^10 + 16*X^9 + 62*X^8 + 14*X^7 + 40*X^6 + 55*X^5 + 35*X^4 + 40*X^2 + 4*X +
      38) :=
  sq_step (by norm_num) pSeventeenA2s198 ⟨
    60*X^32 + 66*X^31 + X^30 + 21*X^29 + 45*X^28 + 13*X^27 + 28*X^26 + 57*X^25 + 44*X^24 + 65*X^23 +
      31*X^22 + 9*X^21 + 20*X^20 + 56*X^19 + 38*X^18 + 60*X^17 + 63*X^16 + 29*X^15 + 31*X^14 +
      30*X^13 + 14*X^12 + 49*X^11 + 40*X^10 + 41*X^9 + 19*X^8 + 53*X^7 + 24*X^6 + 3*X^5 + 63*X^4 +
      62*X^3 + 14*X + 63,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s200 : XPow fSeventeenA2 3230677574200787382524813897330644605959
    (29*X^33 + 31*X^32 + 32*X^31 + 4*X^30 + 48*X^29 + 42*X^28 + 3*X^27 + 37*X^26 + 8*X^25 + 14*X^24 +
      31*X^23 + 20*X^22 + 65*X^21 + 26*X^20 + 22*X^19 + 2*X^17 + 48*X^16 + 29*X^15 + 39*X^14 +
      34*X^13 + 21*X^12 + 38*X^11 + 6*X^10 + 43*X^9 + 50*X^8 + 58*X^7 + 34*X^6 + 65*X^5 + 34*X^4 +
      8*X^3 + 43*X^2 + X + 6) :=
  mul_step (by norm_num) pSeventeenA2s199 pSeventeenA21 ⟨
    31,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s201 : XPow fSeventeenA2 6461355148401574765049627794661289211918
    (59*X^33 + 36*X^32 + 32*X^31 + 29*X^30 + 25*X^29 + 15*X^28 + 11*X^27 + 52*X^26 + 33*X^25 + 31*X^24 +
      35*X^23 + 2*X^22 + 10*X^21 + 25*X^20 + 3*X^19 + 33*X^18 + 58*X^17 + 21*X^16 + 40*X^15 +
      33*X^14 + 24*X^13 + 49*X^12 + 49*X^11 + 15*X^10 + 29*X^9 + 37*X^8 + 57*X^7 + 55*X^6 + 6*X^5 +
      30*X^4 + 10*X^3 + 27*X^2 + 24*X + 23) :=
  sq_step (by norm_num) pSeventeenA2s200 ⟨
    37*X^32 + 9*X^31 + 21*X^30 + 30*X^29 + 37*X^28 + 19*X^27 + 35*X^26 + 22*X^25 + 46*X^24 + 59*X^23 +
      29*X^22 + 39*X^21 + 7*X^20 + 31*X^18 + 36*X^17 + 46*X^16 + 54*X^15 + 25*X^14 + 44*X^13 +
      64*X^12 + 61*X^11 + 36*X^10 + 56*X^9 + 47*X^8 + 47*X^7 + 40*X^6 + 27*X^5 + 31*X^4 + 32*X^3 +
      53*X^2 + 7*X + 11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s202 : XPow fSeventeenA2 12922710296803149530099255589322578423836
    (4*X^33 + 62*X^32 + 54*X^31 + 45*X^30 + 49*X^29 + 50*X^28 + 52*X^27 + 50*X^26 + 8*X^25 + 17*X^24 +
      64*X^23 + 31*X^22 + 24*X^21 + 19*X^20 + 15*X^19 + 65*X^18 + 8*X^17 + 50*X^16 + 52*X^15 +
      37*X^14 + 42*X^13 + 25*X^12 + 45*X^10 + 49*X^9 + 12*X^8 + 51*X^7 + 36*X^6 + 46*X^5 + 13*X^4 +
      64*X^3 + 48*X^2 + 46*X + 46) :=
  sq_step (by norm_num) pSeventeenA2s201 ⟨
    64*X^32 + 29*X^31 + 39*X^30 + 36*X^29 + 50*X^28 + 28*X^27 + 31*X^26 + 22*X^25 + 58*X^24 + 40*X^23 +
      16*X^22 + 24*X^21 + 36*X^19 + 34*X^18 + 15*X^17 + 41*X^16 + 15*X^15 + 52*X^14 + 40*X^13 +
      34*X^12 + 9*X^11 + 10*X^10 + 7*X^9 + 23*X^8 + 43*X^7 + 49*X^6 + 46*X^5 + 26*X^4 + 17*X^3 +
      65*X^2 + 32*X + 17,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s203 : XPow fSeventeenA2 25845420593606299060198511178645156847672
    (54*X^32 + 40*X^31 + 11*X^30 + 65*X^29 + 40*X^28 + 25*X^27 + 55*X^26 + 3*X^25 + 14*X^24 + 4*X^23 +
      45*X^22 + 57*X^21 + 49*X^20 + 20*X^19 + 3*X^18 + 4*X^17 + 32*X^16 + 5*X^15 + 5*X^14 + 40*X^13 +
      56*X^12 + 48*X^11 + 9*X^10 + 58*X^9 + 22*X^8 + 40*X^7 + 46*X^6 + 38*X^5 + 63*X^4 + 55*X^3 +
      18*X^2 + 22*X + 47) :=
  sq_step (by norm_num) pSeventeenA2s202 ⟨
    16*X^32 + 61*X^31 + 6*X^30 + 32*X^29 + 31*X^28 + 12*X^27 + 17*X^26 + 40*X^25 + 25*X^24 + 20*X^23 +
      35*X^22 + 17*X^21 + 66*X^20 + 55*X^19 + 27*X^18 + 53*X^17 + 56*X^16 + 17*X^15 + 11*X^14 +
      22*X^13 + 54*X^12 + 30*X^11 + 52*X^10 + 51*X^9 + 30*X^8 + 27*X^7 + 21*X^6 + 60*X^5 + 11*X^4 +
      3*X^3 + X^2 + 40*X + 19,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s204 : XPow fSeventeenA2 51690841187212598120397022357290313695344
    (49*X^33 + 20*X^32 + 17*X^31 + 24*X^30 + 56*X^29 + 46*X^28 + 61*X^27 + 36*X^26 + 30*X^25 + 6*X^24 +
      58*X^23 + 21*X^22 + 47*X^21 + 64*X^20 + 45*X^19 + 36*X^18 + 30*X^17 + 37*X^16 + 65*X^15 +
      19*X^14 + 55*X^13 + 52*X^12 + 61*X^11 + 23*X^10 + 3*X^9 + 19*X^8 + 16*X^7 + 2*X^6 + 16*X^5 +
      9*X^4 + 25*X^3 + 35*X^2 + 52*X + 12) :=
  sq_step (by norm_num) pSeventeenA2s203 ⟨
    35*X^30 + 31*X^29 + 37*X^28 + 9*X^27 + 39*X^26 + 14*X^25 + 7*X^24 + 65*X^23 + 44*X^22 + 49*X^21 +
      63*X^20 + 61*X^19 + 37*X^18 + 40*X^17 + 45*X^16 + 21*X^15 + 22*X^14 + 31*X^13 + 56*X^12 +
      44*X^11 + X^10 + 57*X^9 + 42*X^8 + 44*X^7 + X^6 + 48*X^5 + 11*X^4 + 33*X^3 + 57*X^2 + 54*X +
      50,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s205 : XPow fSeventeenA2 103381682374425196240794044714580627390688
    (45*X^33 + 17*X^32 + 50*X^31 + 21*X^30 + 64*X^29 + 5*X^28 + X^27 + 58*X^26 + 7*X^25 + 29*X^24 +
      62*X^23 + 7*X^22 + 13*X^20 + 8*X^19 + 3*X^18 + 64*X^17 + 44*X^16 + 61*X^15 + 4*X^14 + 27*X^13 +
      56*X^12 + 16*X^11 + 63*X^10 + 3*X^9 + 43*X^8 + 42*X^6 + 35*X^5 + 65*X^4 + X^3 + 41*X^2 + 25*X +
      44) :=
  sq_step (by norm_num) pSeventeenA2s204 ⟨
    56*X^32 + 2*X^31 + 59*X^30 + 14*X^29 + 33*X^28 + 3*X^27 + 55*X^26 + 27*X^25 + 25*X^24 + 29*X^23 +
      14*X^22 + 38*X^21 + 57*X^20 + 62*X^19 + 7*X^18 + 4*X^17 + 54*X^16 + 18*X^15 + 33*X^14 +
      53*X^13 + 21*X^12 + 35*X^11 + 54*X^10 + 40*X^9 + 37*X^8 + 26*X^7 + 33*X^6 + 36*X^5 + 40*X^4 +
      48*X^3 + 51*X^2 + 50*X + 64,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s206 : XPow fSeventeenA2 103381682374425196240794044714580627390689
    (54*X^33 + 14*X^32 + 12*X^31 + 18*X^30 + 64*X^29 + 31*X^28 + 13*X^27 + 31*X^26 + 39*X^25 + 35*X^24 +
      21*X^23 + 25*X^22 + 36*X^21 + 22*X^20 + 17*X^19 + 23*X^18 + 8*X^17 + 25*X^16 + 6*X^15 +
      13*X^14 + 3*X^13 + 61*X^12 + 54*X^11 + 49*X^10 + 50*X^9 + 22*X^8 + 53*X^7 + 11*X^6 + 61*X^5 +
      59*X^4 + 14*X^3 + 60*X^2 + 40*X + 26) :=
  mul_step (by norm_num) pSeventeenA2s205 pSeventeenA21 ⟨
    45,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s207 : XPow fSeventeenA2 206763364748850392481588089429161254781378
    (37*X^33 + 18*X^32 + 58*X^31 + 12*X^30 + 20*X^29 + 12*X^28 + 43*X^27 + 57*X^26 + 62*X^25 + 40*X^24 +
      56*X^23 + 35*X^22 + 14*X^21 + 34*X^20 + 15*X^19 + 5*X^18 + 52*X^17 + 53*X^16 + 21*X^15 +
      63*X^14 + 60*X^13 + 8*X^12 + 39*X^11 + 2*X^10 + 19*X^9 + 31*X^8 + 51*X^7 + 32*X^6 + 62*X^5 +
      22*X^4 + 5*X^3 + 44*X^2 + 34*X + 59) :=
  sq_step (by norm_num) pSeventeenA2s206 ⟨
    35*X^32 + 37*X^31 + 10*X^30 + 57*X^29 + 10*X^28 + 5*X^27 + 2*X^26 + 21*X^25 + 20*X^24 + 32*X^23 +
      18*X^22 + 36*X^21 + 47*X^20 + 6*X^19 + 58*X^18 + 51*X^17 + 58*X^16 + 27*X^15 + 21*X^14 + X^13 +
      23*X^12 + X^11 + 62*X^10 + 55*X^9 + 21*X^8 + 4*X^7 + 18*X^6 + 47*X^5 + 29*X^4 + 65*X^3 +
      55*X^2 + 64*X + 17,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s208 : XPow fSeventeenA2 206763364748850392481588089429161254781379
    (38*X^33 + 15*X^32 + 18*X^31 + 6*X^30 + 62*X^29 + 23*X^28 + 20*X^27 + 46*X^26 + 11*X^25 + 7*X^24 +
      48*X^23 + 42*X^22 + 41*X^21 + 28*X^20 + 18*X^19 + 57*X^18 + 10*X^17 + 45*X^16 + 17*X^15 +
      47*X^14 + 21*X^13 + 9*X^12 + 8*X^11 + 33*X^10 + 4*X^9 + 14*X^8 + 47*X^7 + 11*X^6 + 47*X^5 +
      11*X^4 + 62*X^3 + 33*X^2 + 17*X + 5) :=
  mul_step (by norm_num) pSeventeenA2s207 pSeventeenA21 ⟨
    37,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s209 : XPow fSeventeenA2 413526729497700784963176178858322509562758
    (58*X^33 + 8*X^32 + 38*X^31 + 17*X^30 + 49*X^29 + 36*X^28 + 64*X^27 + 20*X^26 + 63*X^25 + 45*X^24 +
      66*X^23 + 57*X^22 + 13*X^21 + 14*X^20 + 56*X^19 + 25*X^18 + 21*X^17 + 28*X^16 + 47*X^15 +
      55*X^14 + 20*X^13 + 14*X^12 + 17*X^11 + 46*X^10 + 6*X^9 + 42*X^8 + 62*X^7 + 13*X^6 + 40*X^5 +
      49*X^4 + 52*X^3 + 47*X^2 + 4*X + 1) :=
  sq_step (by norm_num) pSeventeenA2s208 ⟨
    37*X^32 + 21*X^31 + 62*X^30 + 55*X^29 + 24*X^28 + 46*X^27 + 45*X^26 + 33*X^25 + 34*X^24 + 32*X^23 +
      7*X^22 + 4*X^21 + 45*X^20 + 18*X^19 + 61*X^18 + 36*X^17 + 38*X^16 + 22*X^15 + 38*X^14 + 3*X^13 +
      50*X^12 + 35*X^11 + 41*X^10 + 40*X^9 + 48*X^8 + 41*X^7 + 60*X^6 + 39*X^5 + 37*X^4 + 50*X^3 +
      44*X^2 + 8*X + 10,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s210 : XPow fSeventeenA2 413526729497700784963176178858322509562759
    (14*X^33 + 5*X^32 + 59*X^31 + 18*X^30 + 51*X^29 + 58*X^28 + 29*X^27 + 18*X^26 + 43*X^25 + 58*X^24 +
      14*X^23 + 8*X^22 + 63*X^21 + 13*X^20 + 49*X^19 + 56*X^18 + 62*X^17 + 14*X^16 + X^15 + 63*X^14 +
      38*X^13 + 8*X^12 + 21*X^11 + 37*X^10 + 54*X^9 + 4*X^8 + 51*X^7 + 18*X^6 + 23*X^5 + 27*X^4 +
      39*X^3 + 64*X^2 + 42*X + 35) :=
  mul_step (by norm_num) pSeventeenA2s209 pSeventeenA21 ⟨
    58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s211 : XPow fSeventeenA2 827053458995401569926352357716645019125518
    (50*X^33 + 62*X^32 + 6*X^31 + 18*X^30 + 12*X^29 + 59*X^28 + 6*X^27 + 49*X^26 + 32*X^25 + 40*X^24 +
      34*X^23 + 39*X^22 + 34*X^21 + 29*X^20 + X^19 + 2*X^18 + 64*X^17 + 55*X^16 + 47*X^15 + 55*X^14 +
      60*X^13 + 64*X^12 + 16*X^11 + 39*X^10 + 59*X^9 + 44*X^8 + 41*X^7 + 64*X^6 + 19*X^5 + 39*X^4 +
      22*X^3 + 4*X^2 + 44*X + 53) :=
  sq_step (by norm_num) pSeventeenA2s210 ⟨
    62*X^32 + 54*X^31 + 37*X^30 + 40*X^29 + 8*X^28 + 66*X^27 + 33*X^26 + 29*X^25 + 46*X^24 + 38*X^23 +
      61*X^22 + 46*X^21 + 22*X^20 + 57*X^19 + 21*X^18 + 51*X^17 + 48*X^16 + 43*X^15 + 43*X^14 +
      21*X^13 + 15*X^12 + 32*X^11 + 9*X^10 + 63*X^9 + 41*X^8 + 10*X^7 + 14*X^6 + 25*X^5 + 4*X^4 +
      14*X^3 + 51*X^2 + 38*X + 64,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s212 : XPow fSeventeenA2 1654106917990803139852704715433290038251036
    (23*X^33 + 20*X^32 + 7*X^31 + 47*X^30 + 28*X^29 + 47*X^28 + 25*X^27 + 10*X^26 + 12*X^25 + 51*X^24 +
      37*X^23 + 28*X^22 + 8*X^21 + 37*X^20 + 32*X^19 + 7*X^18 + 7*X^17 + 27*X^16 + 25*X^15 + 16*X^14 +
      16*X^13 + 13*X^12 + 46*X^11 + 47*X^10 + 63*X^9 + 34*X^8 + 21*X^7 + 59*X^6 + 13*X^5 + 15*X^4 +
      35*X^3 + 12*X^2 + 11*X + 59) :=
  sq_step (by norm_num) pSeventeenA2s211 ⟨
    21*X^32 + 22*X^31 + 62*X^30 + 51*X^29 + 13*X^28 + 17*X^26 + 11*X^25 + 45*X^24 + 50*X^22 + 34*X^21 +
      60*X^20 + 4*X^19 + 44*X^18 + 17*X^17 + 45*X^16 + 49*X^15 + 31*X^14 + 31*X^13 + 65*X^12 +
      14*X^11 + 53*X^10 + 44*X^9 + 14*X^8 + 2*X^7 + 42*X^6 + 56*X^5 + 40*X^4 + 60*X^3 + 54*X^2 +
      23*X + 18,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s213 : XPow fSeventeenA2 3308213835981606279705409430866580076502072
    (44*X^33 + 61*X^32 + 34*X^31 + 11*X^30 + 34*X^29 + 62*X^28 + 41*X^27 + 11*X^26 + 56*X^25 + 61*X^24 +
      3*X^23 + 52*X^22 + 2*X^21 + 31*X^20 + 57*X^19 + 21*X^18 + 61*X^17 + 59*X^16 + 16*X^15 +
      50*X^14 + 63*X^13 + 54*X^12 + 26*X^11 + 31*X^10 + 7*X^9 + 42*X^8 + 64*X^7 + 63*X^6 + 30*X^5 +
      2*X^4 + 2*X^3 + 22*X^2 + 39*X + 2) :=
  sq_step (by norm_num) pSeventeenA2s212 ⟨
    60*X^32 + 9*X^31 + 65*X^30 + 30*X^29 + 49*X^28 + 27*X^27 + 13*X^26 + 19*X^25 + 47*X^24 + 22*X^23 +
      37*X^22 + 64*X^21 + 11*X^20 + 33*X^19 + 8*X^18 + 21*X^17 + 9*X^16 + 43*X^15 + 30*X^14 +
      54*X^13 + 2*X^12 + 5*X^11 + 12*X^10 + 7*X^9 + 26*X^8 + 62*X^7 + 54*X^6 + 58*X^5 + 34*X^4 +
      16*X^3 + 44*X^2 + 66*X + 37,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s214 : XPow fSeventeenA2 6616427671963212559410818861733160153004144
    (22*X^33 + 5*X^32 + 16*X^31 + 42*X^30 + 57*X^29 + 53*X^28 + 52*X^27 + 16*X^26 + 13*X^25 + 54*X^24 +
      63*X^23 + 30*X^22 + 19*X^21 + 62*X^20 + X^19 + 58*X^18 + 44*X^17 + 7*X^16 + 38*X^15 + 64*X^14 +
      66*X^13 + 47*X^12 + 48*X^11 + 14*X^10 + 60*X^9 + 10*X^8 + 33*X^7 + 44*X^6 + 23*X^5 + 15*X^4 +
      34*X^3 + 61*X^2 + 63*X + 41) :=
  sq_step (by norm_num) pSeventeenA2s213 ⟨
    60*X^32 + 35*X^31 + 31*X^30 + 8*X^29 + 36*X^28 + 12*X^27 + 60*X^26 + 19*X^25 + 21*X^24 + 52*X^23 +
      60*X^22 + 64*X^21 + 19*X^20 + X^19 + 24*X^18 + 24*X^17 + 28*X^16 + 34*X^15 + 13*X^14 + 25*X^13 +
      61*X^12 + 65*X^11 + 30*X^10 + 57*X^9 + 22*X^8 + 22*X^7 + 34*X^6 + 14*X^5 + 46*X^4 + 28*X^3 +
      46*X^2 + 60*X + 46,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s215 : XPow fSeventeenA2 6616427671963212559410818861733160153004145
    (35*X^33 + 52*X^32 + 51*X^31 + 36*X^30 + 61*X^29 + 22*X^28 + 61*X^27 + 56*X^26 + 44*X^25 + 23*X^24 +
      16*X^23 + 61*X^22 + 39*X^21 + 54*X^20 + 44*X^19 + 18*X^18 + 43*X^17 + 7*X^16 + 62*X^15 +
      13*X^14 + 33*X^13 + 3*X^12 + 23*X^11 + 14*X^10 + 3*X^9 + 11*X^8 + 33*X^7 + 47*X^6 + 19*X^5 +
      43*X^4 + 21*X^3 + 28*X^2 + 45*X + 41) :=
  mul_step (by norm_num) pSeventeenA2s214 pSeventeenA21 ⟨
    22,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s216 : XPow fSeventeenA2 13232855343926425118821637723466320306008290
    (8*X^33 + 28*X^32 + 51*X^31 + 7*X^30 + 2*X^29 + 35*X^28 + 48*X^27 + 39*X^26 + 27*X^25 + 4*X^24 +
      25*X^23 + 42*X^22 + 64*X^21 + 40*X^20 + 33*X^19 + 22*X^18 + 63*X^17 + 31*X^16 + 26*X^15 +
      47*X^14 + 26*X^13 + 52*X^12 + 50*X^11 + 62*X^10 + 10*X^9 + 66*X^7 + 6*X^6 + 55*X^5 + 55*X^4 +
      13*X^3 + 52*X^2 + 9*X + 43) :=
  sq_step (by norm_num) pSeventeenA2s215 ⟨
    19*X^32 + 54*X^31 + 32*X^30 + 6*X^29 + 60*X^28 + 19*X^27 + 47*X^26 + 49*X^25 + 38*X^24 + 48*X^23 +
      60*X^22 + 59*X^21 + 17*X^20 + 26*X^19 + 60*X^18 + 37*X^17 + 34*X^16 + 59*X^15 + 60*X^14 +
      30*X^13 + 18*X^12 + 57*X^11 + 14*X^10 + 42*X^9 + 47*X^8 + 43*X^7 + 55*X^6 + 25*X^5 + 15*X^4 +
      49*X^3 + 53*X^2 + 14*X + 46,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s217 : XPow fSeventeenA2 13232855343926425118821637723466320306008291
    (45*X^33 + 58*X^32 + 59*X^31 + 37*X^30 + 44*X^29 + 31*X^28 + 31*X^27 + 43*X^25 + 47*X^24 + 43*X^23 +
      61*X^22 + 56*X^21 + 34*X^20 + 23*X^19 + 17*X^18 + 38*X^17 + 33*X^16 + 28*X^15 + 25*X^14 +
      53*X^13 + 58*X^12 + 47*X^11 + 42*X^10 + 34*X^9 + 58*X^8 + 2*X^7 + 15*X^6 + 26*X^5 + 65*X^4 +
      7*X^3 + 45*X^2 + 14*X + 21) :=
  mul_step (by norm_num) pSeventeenA2s216 pSeventeenA21 ⟨
    8,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s218 : XPow fSeventeenA2 26465710687852850237643275446932640612016582
    (2*X^33 + 24*X^32 + X^31 + 66*X^30 + 32*X^29 + 28*X^28 + 5*X^27 + 8*X^26 + 52*X^25 + 39*X^24 +
      35*X^23 + 45*X^22 + 43*X^21 + 64*X^20 + X^19 + 18*X^18 + 64*X^17 + 24*X^16 + 41*X^15 + 7*X^14 +
      44*X^13 + 60*X^12 + 13*X^11 + 55*X^10 + 32*X^9 + 21*X^8 + 44*X^7 + 11*X^6 + 18*X^5 + 37*X^4 +
      51*X^3 + 38*X^2 + 47*X + 43) :=
  sq_step (by norm_num) pSeventeenA2s217 ⟨
    15*X^32 + 51*X^31 + 52*X^30 + 50*X^29 + 46*X^28 + 15*X^27 + 38*X^26 + 52*X^25 + 60*X^24 + 23*X^23 +
      23*X^22 + 47*X^21 + 10*X^20 + 29*X^19 + 9*X^18 + 25*X^17 + 34*X^16 + 29*X^15 + 31*X^14 +
      38*X^13 + 56*X^12 + 63*X^11 + 9*X^10 + 64*X^9 + 23*X^8 + 24*X^7 + 7*X^6 + 10*X^5 + 20*X^4 +
      30*X^3 + 36*X^2 + 16*X + 43,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s219 : XPow fSeventeenA2 26465710687852850237643275446932640612016583
    (45*X^33 + 53*X^32 + 12*X^31 + 24*X^30 + 47*X^29 + 51*X^28 + 6*X^27 + 62*X^26 + 32*X^25 + 7*X^24 +
      62*X^23 + 59*X^22 + X^21 + 18*X^20 + 35*X^19 + 19*X^18 + 9*X^17 + 26*X^16 + 19*X^15 + 27*X^14 +
      10*X^13 + 15*X^12 + X^11 + 40*X^10 + 63*X^9 + 42*X^8 + 10*X^7 + 8*X^6 + 13*X^5 + 64*X^4 +
      10*X^3 + 56*X^2 + 19*X + 22) :=
  mul_step (by norm_num) pSeventeenA2s218 pSeventeenA21 ⟨
    2,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s220 : XPow fSeventeenA2 52931421375705700475286550893865281224033166
    (44*X^33 + 48*X^32 + 25*X^31 + 18*X^30 + 15*X^29 + 29*X^28 + 63*X^27 + 25*X^26 + 2*X^25 + 23*X^24 +
      33*X^23 + 61*X^22 + 17*X^21 + 31*X^20 + 63*X^19 + 59*X^18 + 18*X^17 + 54*X^16 + 56*X^15 +
      8*X^13 + 15*X^12 + 21*X^11 + 12*X^10 + 44*X^9 + 43*X^8 + 24*X^7 + 51*X^6 + 26*X^5 + 38*X^4 +
      34*X^3 + 60*X^2 + 41*X + 40) :=
  sq_step (by norm_num) pSeventeenA2s219 ⟨
    15*X^32 + 3*X^31 + 56*X^30 + 8*X^29 + 9*X^28 + 24*X^27 + 63*X^26 + 3*X^25 + 25*X^24 + 32*X^23 +
      66*X^22 + 26*X^21 + 30*X^20 + 29*X^19 + 65*X^18 + 63*X^17 + 66*X^16 + 60*X^15 + 39*X^14 +
      9*X^13 + 37*X^12 + 18*X^11 + 39*X^10 + 54*X^9 + 28*X^8 + 47*X^7 + 27*X^6 + 32*X^5 + 4*X^4 +
      23*X^3 + 15*X^2 + 26*X + 51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s221 : XPow fSeventeenA2 52931421375705700475286550893865281224033167
    (41*X^33 + 30*X^32 + 36*X^31 + 40*X^30 + 45*X^29 + 3*X^28 + 48*X^27 + 21*X^26 + 3*X^25 + 20*X^24 +
      33*X^23 + 34*X^22 + 52*X^21 + 35*X^20 + 31*X^19 + 33*X^18 + 59*X^17 + 61*X^16 + 63*X^15 +
      36*X^14 + 54*X^13 + 65*X^12 + 30*X^11 + 19*X^10 + 29*X^9 + 47*X^8 + 29*X^7 + 7*X^6 + 46*X^5 +
      52*X^4 + 47*X^3 + 38*X^2 + 48*X + 15) :=
  mul_step (by norm_num) pSeventeenA2s220 pSeventeenA21 ⟨
    44,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s222 : XPow fSeventeenA2 105862842751411400950573101787730562448066334
    (2*X^33 + 34*X^32 + 26*X^31 + 55*X^30 + 55*X^29 + 32*X^28 + 35*X^27 + 8*X^26 + 18*X^25 + 46*X^24 +
      64*X^23 + 34*X^22 + 40*X^21 + 5*X^20 + 66*X^19 + 7*X^18 + 51*X^17 + 24*X^16 + 22*X^15 + 3*X^14 +
      20*X^13 + 64*X^12 + 22*X^11 + 3*X^10 + 39*X^9 + 43*X^8 + 50*X^7 + 21*X^6 + 8*X^5 + 57*X^4 +
      57*X^3 + 63*X^2 + 55*X + 47) :=
  sq_step (by norm_num) pSeventeenA2s221 ⟨
    6*X^32 + 44*X^31 + 48*X^30 + 25*X^29 + 13*X^28 + 5*X^27 + 24*X^26 + 29*X^25 + 50*X^24 + 25*X^23 +
      16*X^22 + 62*X^21 + 54*X^20 + 22*X^19 + 53*X^18 + 52*X^17 + 3*X^16 + 37*X^15 + 25*X^14 + X^13 +
      62*X^12 + 59*X^11 + 42*X^10 + 19*X^9 + 21*X^8 + 32*X^7 + 61*X^6 + 27*X^5 + 38*X^4 + 8*X^3 +
      35*X^2 + 22*X + 63,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s223 : XPow fSeventeenA2 105862842751411400950573101787730562448066335
    (55*X^33 + 11*X^32 + X^31 + 47*X^30 + 51*X^29 + 14*X^28 + 6*X^27 + 28*X^26 + 39*X^25 + 36*X^24 +
      51*X^23 + 56*X^22 + 9*X^21 + 16*X^20 + 24*X^19 + 6*X^18 + 9*X^17 + 7*X^16 + 15*X^15 + 3*X^14 +
      14*X^13 + 24*X^12 + 16*X^11 + 47*X^10 + 18*X^9 + 48*X^8 + 20*X^7 + 65*X^6 + 33*X^5 + 3*X^4 +
      35*X^3 + 64*X^2 + 23*X + 22) :=
  mul_step (by norm_num) pSeventeenA2s222 pSeventeenA21 ⟨
    2,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s224 : XPow fSeventeenA2 211725685502822801901146203575461124896132670
    (66*X^33 + 16*X^32 + 63*X^31 + 44*X^30 + 14*X^29 + 21*X^28 + 44*X^27 + 20*X^26 + 40*X^25 + 41*X^24 +
      25*X^23 + 9*X^22 + 47*X^21 + 39*X^20 + 43*X^19 + 27*X^18 + 4*X^17 + 50*X^16 + 20*X^15 +
      23*X^14 + 29*X^13 + 35*X^12 + 24*X^11 + 24*X^10 + 48*X^9 + 62*X^8 + 66*X^7 + 14*X^6 + 49*X^5 +
      43*X^4 + 29*X^3 + 65*X^2 + 22*X + 9) :=
  sq_step (by norm_num) pSeventeenA2s223 ⟨
    10*X^32 + 42*X^31 + 61*X^30 + 55*X^29 + 30*X^28 + 34*X^27 + 33*X^26 + 55*X^25 + 44*X^24 + 15*X^23 +
      28*X^22 + 8*X^21 + X^20 + 54*X^19 + 29*X^18 + 40*X^17 + 62*X^16 + 50*X^15 + 28*X^14 + 63*X^13 +
      23*X^12 + 14*X^11 + 4*X^10 + 65*X^9 + 33*X^8 + 26*X^7 + 10*X^6 + 10*X^5 + 35*X^4 + 5*X^3 +
      26*X^2 + 65*X + 36,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s225 : XPow fSeventeenA2 423451371005645603802292407150922249792265340
    (43*X^33 + 13*X^32 + 48*X^31 + 19*X^30 + 6*X^29 + 60*X^28 + 42*X^27 + 8*X^26 + 46*X^25 + 29*X^24 +
      27*X^23 + 37*X^22 + 10*X^21 + 57*X^20 + 13*X^19 + 9*X^18 + 34*X^17 + 54*X^16 + 49*X^15 +
      57*X^14 + 6*X^13 + 48*X^12 + 48*X^11 + X^10 + 18*X^9 + 66*X^8 + 50*X^7 + 53*X^6 + 21*X^5 +
      20*X^4 + 36*X^3 + 12*X^2 + 59*X + 65) :=
  sq_step (by norm_num) pSeventeenA2s224 ⟨
    X^32 + 12*X^31 + 14*X^30 + 15*X^29 + 15*X^28 + 51*X^27 + 28*X^26 + 42*X^25 + 63*X^24 + 21*X^23 +
      54*X^22 + 49*X^21 + 12*X^20 + 31*X^19 + 39*X^18 + 37*X^17 + 38*X^16 + 15*X^15 + 66*X^14 +
      64*X^13 + 27*X^12 + 13*X^11 + 53*X^10 + 66*X^9 + 55*X^8 + 56*X^7 + 47*X^6 + 55*X^5 + 33*X^4 +
      27*X^3 + 44*X^2 + X + 29,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s226 : XPow fSeventeenA2 846902742011291207604584814301844499584530680
    (9*X^33 + 36*X^32 + 66*X^31 + 53*X^30 + 64*X^29 + 47*X^28 + 12*X^27 + 64*X^26 + 18*X^25 + 26*X^24 +
      63*X^23 + 30*X^22 + 15*X^21 + 60*X^20 + 47*X^19 + 22*X^18 + 21*X^17 + 14*X^16 + X^15 + 30*X^14 +
      49*X^13 + 35*X^12 + 51*X^11 + 46*X^10 + 40*X^9 + 50*X^8 + 46*X^7 + 31*X^6 + 31*X^5 + 34*X^4 +
      X^3 + 52*X^2 + 6*X + 15) :=
  sq_step (by norm_num) pSeventeenA2s225 ⟨
    40*X^32 + 64*X^31 + 46*X^30 + 63*X^29 + 34*X^28 + 44*X^27 + 63*X^26 + 55*X^25 + 64*X^24 + 61*X^23 +
      19*X^22 + 25*X^21 + 61*X^20 + 32*X^19 + 38*X^18 + 18*X^17 + 32*X^16 + 41*X^15 + 27*X^14 +
      40*X^13 + 51*X^12 + 29*X^11 + 11*X^10 + 36*X^9 + 23*X^8 + 3*X^7 + 13*X^6 + 42*X^4 + 58*X^3 +
      61*X^2 + 17*X + 1,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s227 : XPow fSeventeenA2 1693805484022582415209169628603688999169061360
    (47*X^33 + 8*X^32 + 45*X^31 + 11*X^30 + 62*X^29 + 43*X^28 + 19*X^27 + 14*X^26 + 57*X^25 + 9*X^24 +
      16*X^23 + 22*X^22 + 64*X^21 + 64*X^20 + 16*X^19 + 15*X^18 + 33*X^17 + 12*X^16 + 44*X^15 +
      22*X^14 + 55*X^13 + 35*X^12 + 30*X^11 + 29*X^10 + 4*X^9 + 54*X^8 + 51*X^7 + 30*X^6 + 24*X^5 +
      61*X^4 + 14*X^3 + 20*X^2 + 37*X + 8) :=
  sq_step (by norm_num) pSeventeenA2s226 ⟨
    14*X^32 + 58*X^31 + 40*X^30 + 20*X^29 + 41*X^28 + 61*X^27 + 20*X^26 + 27*X^25 + 64*X^24 + 12*X^23 +
      5*X^22 + 22*X^21 + 37*X^20 + 11*X^19 + 19*X^18 + 20*X^17 + 20*X^16 + 7*X^15 + 63*X^14 +
      10*X^13 + 33*X^12 + 34*X^11 + 56*X^10 + 19*X^9 + 24*X^8 + 32*X^7 + 60*X^6 + 7*X^5 + 32*X^4 +
      15*X^3 + 41*X^2 + 43*X + 29,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s228 : XPow fSeventeenA2 1693805484022582415209169628603688999169061361
    (66*X^33 + 61*X^32 + 15*X^31 + 8*X^30 + 54*X^29 + 28*X^28 + 34*X^27 + 24*X^26 + 12*X^25 + 28*X^24 +
      53*X^23 + 38*X^22 + 24*X^21 + 47*X^20 + 46*X^19 + 14*X^18 + 28*X^17 + 60*X^16 + 36*X^15 +
      24*X^14 + 66*X^13 + 10*X^12 + 33*X^11 + 58*X^10 + 36*X^9 + 4*X^8 + 40*X^7 + 57*X^6 + 33*X^5 +
      18*X^4 + 32*X^3 + 14*X^2 + 47*X + 48) :=
  mul_step (by norm_num) pSeventeenA2s227 pSeventeenA21 ⟨
    47,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s229 : XPow fSeventeenA2 3387610968045164830418339257207377998338122722
    (7*X^33 + 56*X^32 + 36*X^31 + 50*X^30 + 25*X^29 + 41*X^28 + 5*X^27 + 24*X^26 + 43*X^25 + 27*X^24 +
      9*X^23 + 43*X^22 + 12*X^21 + 16*X^20 + 12*X^19 + 16*X^18 + 31*X^17 + 16*X^16 + 60*X^15 +
      59*X^14 + 27*X^13 + 16*X^12 + 51*X^11 + 18*X^10 + 20*X^9 + 45*X^8 + 41*X^7 + 14*X^6 + 36*X^4 +
      16*X^3 + 58*X^2 + 54*X + 7) :=
  sq_step (by norm_num) pSeventeenA2s228 ⟨
    X^32 + 56*X^31 + 17*X^30 + 38*X^29 + 16*X^28 + 52*X^27 + 28*X^26 + 40*X^25 + 31*X^24 + 13*X^23 +
      15*X^22 + 57*X^21 + 7*X^20 + 5*X^19 + 23*X^18 + 40*X^17 + 11*X^16 + 43*X^15 + 49*X^14 +
      14*X^13 + 56*X^12 + 34*X^11 + 30*X^10 + 46*X^9 + 59*X^8 + 16*X^7 + 13*X^6 + 15*X^5 + 52*X^4 +
      15*X^3 + 23*X^2 + 48*X + 47,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s230 : XPow fSeventeenA2 6775221936090329660836678514414755996676245444
    (63*X^33 + 44*X^32 + 2*X^31 + 54*X^30 + 51*X^29 + 10*X^28 + 37*X^27 + 29*X^26 + 24*X^24 + X^23 +
      47*X^22 + 53*X^21 + 32*X^20 + 34*X^19 + 18*X^18 + 13*X^17 + 57*X^16 + 33*X^15 + 22*X^14 +
      9*X^13 + 48*X^12 + 9*X^11 + 29*X^10 + 14*X^9 + 49*X^8 + 44*X^7 + 10*X^6 + 33*X^5 + 4*X^4 +
      19*X^3 + 2*X^2 + 12*X) :=
  sq_step (by norm_num) pSeventeenA2s229 ⟨
    49*X^32 + 59*X^31 + 6*X^30 + 48*X^29 + 20*X^28 + 24*X^27 + 18*X^26 + 22*X^25 + 14*X^24 + 66*X^23 +
      59*X^22 + 54*X^21 + 42*X^20 + 32*X^19 + 11*X^18 + 6*X^17 + 26*X^16 + 66*X^15 + 51*X^14 +
      34*X^13 + 54*X^12 + 45*X^11 + 6*X^10 + 65*X^9 + 31*X^8 + 19*X^7 + 35*X^6 + 7*X^5 + 15*X^4 +
      45*X^3 + 48*X^2 + 46*X + 26,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s231 : XPow fSeventeenA2 13550443872180659321673357028829511993352490888
    (17*X^33 + 23*X^32 + 45*X^31 + 18*X^30 + 58*X^29 + 37*X^28 + 56*X^27 + 5*X^26 + 52*X^25 + 21*X^24 +
      61*X^23 + 37*X^22 + 4*X^21 + 25*X^20 + 32*X^19 + 30*X^18 + 2*X^17 + X^16 + 14*X^15 + 13*X^14 +
      40*X^13 + 54*X^12 + 12*X^11 + 48*X^10 + 30*X^9 + 37*X^8 + 28*X^7 + 40*X^6 + 11*X^5 + 21*X^4 +
      6*X^3 + 9*X^2 + 42*X + 40) :=
  sq_step (by norm_num) pSeventeenA2s230 ⟨
    16*X^32 + 17*X^31 + 2*X^30 + 43*X^29 + 7*X^28 + 50*X^27 + 53*X^26 + 43*X^25 + 47*X^24 + 40*X^23 +
      17*X^22 + 11*X^21 + 7*X^20 + 12*X^19 + 4*X^18 + 48*X^17 + 7*X^16 + 2*X^15 + 57*X^14 + 35*X^13 +
      13*X^12 + 53*X^11 + X^10 + 26*X^9 + 13*X^8 + 17*X^7 + 19*X^6 + 14*X^5 + 16*X^4 + 37*X^3 +
      42*X^2 + 10*X + 28,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s232 : XPow fSeventeenA2 27100887744361318643346714057659023986704981776
    (54*X^33 + 50*X^32 + 12*X^31 + 49*X^30 + 20*X^29 + 29*X^28 + 29*X^27 + 60*X^26 + 57*X^25 + 19*X^24 +
      66*X^23 + 33*X^22 + 13*X^21 + 53*X^20 + 3*X^19 + 20*X^18 + 15*X^17 + 33*X^16 + 14*X^15 +
      43*X^14 + 28*X^13 + 25*X^12 + 16*X^11 + 15*X^10 + 34*X^9 + 22*X^8 + 17*X^7 + 19*X^6 + 12*X^5 +
      51*X^4 + 59*X^3 + 9*X^2 + 35*X + 32) :=
  sq_step (by norm_num) pSeventeenA2s231 ⟨
    21*X^32 + 31*X^31 + 16*X^30 + 7*X^29 + 5*X^28 + 64*X^27 + 58*X^26 + 63*X^25 + X^24 + 15*X^23 +
      4*X^22 + 6*X^21 + 60*X^20 + 40*X^19 + X^18 + 61*X^17 + 2*X^16 + 36*X^15 + 34*X^14 + 54*X^13 +
      55*X^12 + 63*X^11 + 54*X^10 + 47*X^9 + 9*X^8 + 27*X^7 + 55*X^6 + 38*X^5 + 32*X^4 + 40*X^3 +
      38*X^2 + 45*X + 28,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s233 : XPow fSeventeenA2 27100887744361318643346714057659023986704981777
    (14*X^33 + 9*X^32 + 65*X^31 + 5*X^30 + 6*X^29 + 65*X^28 + 6*X^27 + 59*X^26 + 31*X^25 + 47*X^24 +
      23*X^23 + 43*X^22 + 27*X^21 + 60*X^20 + 10*X^19 + 6*X^18 + 30*X^17 + 11*X^16 + 32*X^15 +
      38*X^14 + 15*X^13 + 3*X^12 + 31*X^11 + 49*X^10 + 17*X^9 + 30*X^8 + 59*X^7 + 10*X^6 + 6*X^5 +
      8*X^4 + 57*X^3 + 10*X^2 + 54*X + 58) :=
  mul_step (by norm_num) pSeventeenA2s232 pSeventeenA21 ⟨
    54,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s234 : XPow fSeventeenA2 54201775488722637286693428115318047973409963554
    (59*X^33 + 51*X^32 + 63*X^31 + 23*X^30 + 50*X^29 + 3*X^28 + 59*X^27 + 27*X^26 + 3*X^25 + 41*X^24 +
      50*X^23 + 10*X^22 + 7*X^21 + 63*X^20 + 46*X^19 + 12*X^18 + 36*X^17 + 61*X^16 + 56*X^15 +
      30*X^14 + 22*X^13 + 20*X^12 + 35*X^11 + 50*X^10 + 24*X^9 + 54*X^7 + 27*X^6 + 33*X^5 + 36*X^4 +
      59*X^3 + 58*X^2 + 45*X + 1) :=
  sq_step (by norm_num) pSeventeenA2s233 ⟨
    62*X^32 + 32*X^31 + 30*X^30 + 46*X^29 + 11*X^28 + 23*X^27 + 57*X^26 + 52*X^25 + 25*X^23 + 57*X^22 +
      38*X^21 + 17*X^20 + 19*X^19 + 3*X^18 + 12*X^17 + 33*X^16 + 32*X^15 + 27*X^14 + 66*X^13 +
      23*X^12 + 19*X^11 + 57*X^9 + 8*X^8 + 8*X^7 + 62*X^6 + 21*X^5 + 58*X^4 + 62*X^3 + 49*X^2 + 7*X +
      11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s235 : XPow fSeventeenA2 108403550977445274573386856230636095946819927108
    (25*X^33 + 46*X^32 + 51*X^31 + 3*X^30 + 55*X^29 + 30*X^28 + 27*X^27 + 6*X^26 + 55*X^25 + 23*X^24 +
      51*X^23 + 46*X^22 + 30*X^21 + 47*X^20 + 62*X^19 + 43*X^18 + 40*X^17 + 23*X^16 + 16*X^15 +
      8*X^14 + 2*X^13 + 30*X^12 + 9*X^11 + 10*X^10 + 39*X^9 + 57*X^8 + 4*X^7 + 64*X^6 + 7*X^5 +
      15*X^4 + 40*X^3 + 37*X^2 + 52*X + 6) :=
  sq_step (by norm_num) pSeventeenA2s234 ⟨
    64*X^32 + 57*X^31 + 3*X^30 + 48*X^29 + 14*X^28 + 63*X^27 + 16*X^26 + 22*X^25 + 61*X^24 + 17*X^23 +
      51*X^22 + 33*X^21 + 34*X^20 + 22*X^19 + 66*X^18 + 29*X^17 + 66*X^16 + 55*X^15 + 44*X^14 +
      54*X^13 + 41*X^12 + 4*X^11 + 41*X^10 + 55*X^9 + 31*X^8 + 54*X^7 + 63*X^6 + 3*X^5 + 52*X^4 +
      53*X^3 + 8*X^2 + 43*X + 37,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s236 : XPow fSeventeenA2 216807101954890549146773712461272191893639854216
    (55*X^33 + 21*X^32 + 16*X^31 + 25*X^30 + 33*X^29 + 45*X^28 + 50*X^27 + 10*X^26 + 41*X^25 + 6*X^24 +
      24*X^23 + 4*X^22 + 25*X^21 + 6*X^20 + 30*X^19 + 21*X^18 + 33*X^17 + 53*X^16 + 10*X^15 + 2*X^14 +
      42*X^13 + 64*X^12 + 40*X^11 + 65*X^10 + 50*X^9 + 50*X^8 + 26*X^7 + 63*X^6 + 20*X^5 + 16*X^4 +
      55*X^3 + 2*X^2 + 34*X + 43) :=
  sq_step (by norm_num) pSeventeenA2s235 ⟨
    22*X^32 + 52*X^31 + 22*X^30 + 2*X^29 + 38*X^28 + 24*X^27 + 35*X^26 + 44*X^25 + 31*X^24 + 58*X^23 +
      48*X^22 + 20*X^21 + 40*X^20 + 31*X^19 + 40*X^18 + 22*X^17 + 13*X^16 + 7*X^15 + 58*X^14 +
      60*X^13 + 34*X^12 + 9*X^11 + 35*X^10 + 7*X^9 + 54*X^8 + 35*X^7 + 43*X^6 + 61*X^5 + X^4 +
      49*X^3 + 64*X^2 + 65*X + 25,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s237 : XPow fSeventeenA2 216807101954890549146773712461272191893639854217
    (29*X^33 + 39*X^32 + 14*X^31 + 14*X^30 + 65*X^29 + 42*X^28 + 22*X^27 + 48*X^26 + 48*X^25 + 58*X^24 +
      36*X^23 + 63*X^22 + 49*X^21 + 62*X^20 + 53*X^19 + 35*X^18 + 9*X^17 + 33*X^16 + 64*X^15 +
      10*X^14 + 29*X^13 + 28*X^12 + 54*X^11 + 2*X^10 + 66*X^9 + 38*X^8 + 2*X^7 + 13*X^6 + 26*X^5 +
      44*X^4 + 36*X^3 + 47*X^2 + 53*X + 2) :=
  mul_step (by norm_num) pSeventeenA2s236 pSeventeenA21 ⟨
    55,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s238 : XPow fSeventeenA2 433614203909781098293547424922544383787279708434
    (4*X^33 + 65*X^32 + 17*X^31 + 56*X^30 + 33*X^29 + 14*X^27 + 64*X^26 + 36*X^25 + 47*X^24 + 53*X^23 +
      44*X^22 + 31*X^21 + 32*X^20 + 26*X^19 + 53*X^18 + 65*X^17 + 57*X^16 + 14*X^15 + 59*X^14 +
      10*X^13 + 27*X^12 + 32*X^11 + 11*X^10 + 61*X^9 + 8*X^8 + 37*X^7 + 49*X^6 + 46*X^5 + 33*X^4 +
      28*X^3 + 59*X^2 + 37*X + 64) :=
  sq_step (by norm_num) pSeventeenA2s237 ⟨
    37*X^32 + 4*X^31 + 54*X^30 + 35*X^29 + 41*X^28 + 9*X^27 + 53*X^26 + 3*X^25 + 27*X^24 + 15*X^23 +
      13*X^22 + 27*X^21 + 4*X^20 + X^19 + 58*X^18 + 16*X^17 + 2*X^16 + 17*X^15 + 40*X^14 + 46*X^13 +
      34*X^12 + 4*X^11 + 54*X^10 + 3*X^9 + 19*X^8 + 39*X^7 + 8*X^6 + 8*X^5 + 39*X^4 + 45*X^3 +
      23*X^2 + 36*X + 42,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s239 : XPow fSeventeenA2 867228407819562196587094849845088767574559416868
    (16*X^33 + 9*X^32 + 25*X^31 + 21*X^30 + 38*X^29 + 51*X^28 + 29*X^27 + X^26 + 14*X^25 + 52*X^24 +
      15*X^23 + 9*X^22 + 55*X^21 + 25*X^20 + 37*X^19 + 52*X^18 + 9*X^17 + 6*X^16 + 35*X^15 + 24*X^14 +
      11*X^13 + 10*X^12 + 34*X^11 + 47*X^10 + 59*X^9 + 60*X^8 + 58*X^7 + 12*X^6 + 34*X^5 + 64*X^4 +
      33*X^3 + 62*X^2 + 36*X + 47) :=
  sq_step (by norm_num) pSeventeenA2s238 ⟨
    16*X^32 + 18*X^31 + 8*X^30 + 31*X^29 + 11*X^28 + 45*X^27 + 8*X^26 + 32*X^25 + 49*X^24 + 8*X^23 +
      65*X^22 + 59*X^21 + 39*X^20 + 36*X^19 + 58*X^18 + 58*X^17 + 41*X^16 + 24*X^15 + 16*X^14 +
      27*X^13 + 53*X^12 + 27*X^11 + 24*X^10 + 2*X^9 + 65*X^8 + 49*X^7 + 24*X^6 + 55*X^5 + 59*X^4 +
      58*X^3 + 61*X^2 + 61*X + 40,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s240 : XPow fSeventeenA2 867228407819562196587094849845088767574559416869
    (43*X^33 + 39*X^32 + 58*X^31 + 41*X^30 + 2*X^29 + 62*X^28 + 52*X^27 + 27*X^26 + 63*X^25 + 59*X^24 +
      11*X^23 + 49*X^22 + 57*X^21 + 39*X^20 + 54*X^19 + 51*X^18 + 20*X^17 + 49*X^16 + 53*X^15 +
      9*X^14 + 12*X^13 + 50*X^12 + 17*X^11 + 56*X^10 + 61*X^9 + 42*X^8 + 4*X^7 + 21*X^6 + 6*X^5 +
      3*X^4 + 39*X^3 + 41*X^2 + 56*X + 42) :=
  mul_step (by norm_num) pSeventeenA2s239 pSeventeenA21 ⟨
    16,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s241 : XPow fSeventeenA2 1734456815639124393174189699690177535149118833738
    (20*X^33 + X^32 + 24*X^31 + 30*X^30 + 49*X^29 + 42*X^28 + 26*X^27 + 18*X^26 + 5*X^24 + 19*X^23 +
      19*X^22 + 65*X^21 + 34*X^20 + 7*X^19 + 52*X^18 + 64*X^17 + 58*X^16 + 21*X^15 + 39*X^14 +
      35*X^13 + 31*X^12 + 22*X^11 + 40*X^10 + 7*X^9 + 66*X^8 + X^7 + 53*X^6 + 46*X^5 + 42*X^4 +
      57*X^3 + 64*X^2 + 54*X + 63) :=
  sq_step (by norm_num) pSeventeenA2s240 ⟨
    40*X^32 + 22*X^31 + 8*X^30 + 55*X^29 + 32*X^28 + 26*X^27 + 12*X^26 + 58*X^25 + 22*X^24 + 39*X^23 +
      27*X^22 + 44*X^21 + 51*X^20 + 38*X^19 + 2*X^18 + 35*X^17 + 53*X^16 + 58*X^15 + 11*X^14 +
      21*X^13 + 63*X^12 + 20*X^11 + 25*X^10 + 24*X^9 + 64*X^8 + 59*X^7 + 43*X^6 + 31*X^5 + 12*X^4 +
      22*X^3 + 34*X^2 + 52*X + 22,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s242 : XPow fSeventeenA2 3468913631278248786348379399380355070298237667476
    (15*X^33 + 17*X^32 + 56*X^31 + 53*X^30 + 35*X^29 + 16*X^28 + 47*X^27 + 4*X^26 + 25*X^25 + 11*X^24 +
      47*X^23 + 36*X^22 + 9*X^21 + 21*X^20 + 6*X^19 + 62*X^18 + 30*X^17 + 50*X^16 + 15*X^15 + 7*X^14 +
      63*X^13 + 44*X^12 + 4*X^11 + 39*X^10 + 23*X^9 + 54*X^8 + 52*X^7 + 24*X^6 + 21*X^5 + 32*X^4 +
      16*X^3 + 40*X^2 + 10*X + 42) :=
  sq_step (by norm_num) pSeventeenA2s241 ⟨
    65*X^32 + 19*X^31 + 3*X^30 + 52*X^29 + 35*X^28 + 38*X^27 + 15*X^26 + 24*X^25 + 51*X^24 + 59*X^23 +
      48*X^22 + 57*X^20 + 13*X^19 + 38*X^18 + 7*X^17 + 19*X^16 + 16*X^15 + 15*X^14 + 57*X^13 +
      5*X^12 + 7*X^11 + 33*X^10 + 55*X^9 + 20*X^8 + 52*X^7 + 14*X^6 + 8*X^5 + 47*X^4 + 15*X^3 +
      36*X^2 + 4*X + 45,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s243 : XPow fSeventeenA2 3468913631278248786348379399380355070298237667477
    (7*X^33 + 44*X^32 + 50*X^31 + 42*X^30 + 58*X^29 + 57*X^28 + 56*X^27 + 33*X^26 + 59*X^25 + 38*X^24 +
      63*X^23 + 62*X^22 + 51*X^21 + 33*X^20 + 22*X^19 + 61*X^18 + 38*X^17 + 3*X^16 + 30*X^15 +
      36*X^14 + 4*X^13 + 19*X^12 + 36*X^11 + 16*X^10 + 34*X^9 + 37*X^8 + 50*X^7 + 13*X^6 + 53*X^5 +
      13*X^4 + 31*X^3 + 44*X^2 + 63*X + 31) :=
  mul_step (by norm_num) pSeventeenA2s242 pSeventeenA21 ⟨
    15,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s244 : XPow fSeventeenA2 6937827262556497572696758798760710140596475334954
    (57*X^33 + 47*X^32 + 49*X^31 + 40*X^30 + 12*X^29 + 21*X^28 + 8*X^27 + 29*X^26 + 48*X^25 + 7*X^24 +
      15*X^23 + 44*X^22 + 28*X^21 + 36*X^20 + 23*X^19 + 29*X^18 + 35*X^17 + 26*X^16 + 34*X^15 +
      29*X^14 + 59*X^13 + 2*X^12 + 12*X^11 + 32*X^10 + 31*X^9 + X^8 + 29*X^7 + 3*X^6 + 14*X^5 +
      47*X^4 + 49*X^3 + 8*X^2 + 59*X + 2) :=
  sq_step (by norm_num) pSeventeenA2s243 ⟨
    49*X^32 + 25*X^31 + 52*X^30 + 37*X^29 + 5*X^28 + 28*X^27 + 43*X^26 + 23*X^25 + X^24 + 7*X^23 +
      5*X^22 + 47*X^21 + 33*X^20 + 51*X^19 + 35*X^18 + 60*X^17 + 64*X^16 + 42*X^15 + 17*X^14 +
      46*X^13 + 52*X^12 + 10*X^11 + 52*X^10 + 8*X^9 + 34*X^8 + 60*X^7 + 65*X^6 + 39*X^5 + 25*X^4 +
      48*X^3 + 18*X^2 + 7*X + 59,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s245 : XPow fSeventeenA2 6937827262556497572696758798760710140596475334955
    (9*X^33 + 57*X^32 + 42*X^31 + 52*X^30 + 60*X^29 + 46*X^28 + 39*X^27 + 65*X^26 + 42*X^25 + 21*X^24 +
      26*X^23 + 15*X^22 + 16*X^21 + 5*X^20 + 11*X^19 + 59*X^18 + 34*X^17 + 42*X^16 + 36*X^15 +
      10*X^14 + 51*X^13 + 2*X^12 + 34*X^11 + 58*X^10 + 59*X^9 + 39*X^8 + 8*X^7 + 64*X^6 + 33*X^5 +
      51*X^4 + 14*X^3 + 14*X^2 + 55*X + 24) :=
  mul_step (by norm_num) pSeventeenA2s244 pSeventeenA21 ⟨
    57,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s246 : XPow fSeventeenA2 13875654525112995145393517597521420281192950669910
    (54*X^33 + 31*X^32 + 34*X^31 + 32*X^30 + 61*X^29 + 14*X^28 + 44*X^27 + 25*X^26 + 28*X^25 + 63*X^24 +
      18*X^23 + 5*X^22 + 10*X^21 + 51*X^20 + 23*X^19 + 31*X^18 + 46*X^17 + 23*X^16 + 64*X^15 +
      62*X^14 + 61*X^13 + 39*X^12 + 38*X^11 + 66*X^10 + 19*X^9 + 26*X^8 + 55*X^7 + 62*X^6 + 5*X^5 +
      34*X^4 + 56*X^3 + 36*X^2 + 50*X + 59) :=
  sq_step (by norm_num) pSeventeenA2s245 ⟨
    14*X^32 + 34*X^31 + 36*X^30 + 42*X^29 + 63*X^28 + 51*X^27 + 55*X^26 + 14*X^25 + 66*X^24 + 14*X^23 +
      20*X^22 + 46*X^21 + 44*X^20 + 11*X^19 + 24*X^18 + 5*X^17 + X^16 + 25*X^15 + 57*X^14 + 26*X^12 +
      25*X^11 + 42*X^10 + 43*X^8 + 56*X^7 + 28*X^6 + 30*X^5 + 10*X^4 + 49*X^3 + 45*X^2 + 30*X + 20,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s247 : XPow fSeventeenA2 13875654525112995145393517597521420281192950669911
    (62*X^33 + 31*X^32 + 48*X^31 + 46*X^30 + 58*X^29 + 13*X^28 + 38*X^27 + 30*X^26 + 8*X^25 + 66*X^24 +
      62*X^23 + 40*X^22 + 25*X^21 + 13*X^20 + 21*X^19 + 37*X^18 + 20*X^17 + 61*X^16 + 51*X^15 +
      4*X^14 + 29*X^13 + 25*X^12 + 15*X^11 + 34*X^10 + 21*X^9 + X^8 + 35*X^7 + 3*X^6 + 56*X^5 +
      5*X^4 + 17*X^3 + 25*X^2 + 14*X + 58) :=
  mul_step (by norm_num) pSeventeenA2s246 pSeventeenA21 ⟨
    54,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s248 : XPow fSeventeenA2 27751309050225990290787035195042840562385901339822
    (15*X^33 + 38*X^32 + 53*X^31 + 48*X^30 + 6*X^29 + 65*X^28 + 43*X^27 + 65*X^26 + 19*X^25 + 36*X^24 +
      22*X^23 + 6*X^22 + 33*X^21 + 16*X^20 + 12*X^19 + 61*X^18 + 35*X^17 + 60*X^16 + 21*X^15 +
      48*X^14 + 7*X^13 + 9*X^12 + 66*X^11 + 17*X^10 + 45*X^9 + 41*X^8 + 12*X^7 + 64*X^6 + 22*X^5 +
      17*X^4 + 35*X^3 + 40*X^2 + 63*X + 49) :=
  sq_step (by norm_num) pSeventeenA2s247 ⟨
    25*X^32 + 53*X^31 + 46*X^30 + 17*X^29 + 31*X^28 + 63*X^27 + 30*X^26 + 63*X^25 + 42*X^24 + 40*X^23 +
      63*X^22 + 49*X^21 + 7*X^20 + 64*X^19 + 58*X^18 + 42*X^17 + 46*X^16 + 39*X^15 + 15*X^14 +
      11*X^13 + 32*X^12 + 28*X^11 + 43*X^10 + 42*X^9 + 17*X^8 + 62*X^7 + 21*X^6 + 26*X^5 + 21*X^4 +
      18*X^3 + 49*X^2 + 31*X + 58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s249 : XPow fSeventeenA2 55502618100451980581574070390085681124771802679644
    (66*X^33 + 56*X^32 + 64*X^31 + 27*X^30 + 56*X^29 + 21*X^28 + 14*X^27 + 43*X^26 + 36*X^25 + 45*X^24 +
      51*X^23 + 64*X^22 + 63*X^21 + 22*X^20 + 43*X^19 + 46*X^18 + 49*X^17 + 2*X^16 + 22*X^15 +
      60*X^14 + 41*X^13 + 35*X^12 + 53*X^11 + 39*X^10 + 7*X^9 + 24*X^8 + 33*X^7 + 24*X^6 + 4*X^5 +
      59*X^4 + 64*X^3 + 53*X^2 + 13*X) :=
  sq_step (by norm_num) pSeventeenA2s248 ⟨
    24*X^32 + 52*X^31 + 50*X^30 + 64*X^29 + 7*X^28 + 29*X^27 + 31*X^26 + 58*X^25 + 14*X^24 + 39*X^23 +
      35*X^22 + 50*X^20 + 26*X^19 + 30*X^18 + 64*X^17 + 53*X^16 + X^15 + 2*X^14 + 8*X^13 + 38*X^12 +
      55*X^11 + 31*X^9 + 2*X^8 + 49*X^7 + 20*X^6 + 55*X^5 + 34*X^4 + 57*X^2 + 44*X + 1,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s250 : XPow fSeventeenA2 111005236200903961163148140780171362249543605359288
    (59*X^33 + 64*X^32 + 18*X^31 + 60*X^30 + 46*X^29 + 46*X^28 + 38*X^27 + 66*X^26 + 61*X^25 + 17*X^24 +
      20*X^23 + 33*X^22 + 47*X^21 + 5*X^20 + 42*X^19 + 25*X^18 + 45*X^17 + 13*X^16 + 5*X^15 +
      53*X^14 + 32*X^13 + 32*X^12 + 64*X^11 + 38*X^10 + 8*X^9 + 35*X^8 + 31*X^7 + 40*X^6 + 61*X^5 +
      58*X^3 + 55*X^2 + 40*X + 20) :=
  sq_step (by norm_num) pSeventeenA2s249 ⟨
    X^32 + 66*X^31 + 42*X^30 + 65*X^29 + 62*X^28 + 19*X^27 + 6*X^26 + 28*X^25 + 58*X^24 + 42*X^23 +
      37*X^22 + 32*X^21 + 3*X^20 + 23*X^19 + 34*X^18 + 27*X^17 + 66*X^16 + 51*X^15 + 57*X^14 +
      46*X^13 + 15*X^12 + 59*X^11 + 49*X^10 + 36*X^9 + 27*X^8 + 29*X^7 + 20*X^6 + 17*X^5 + 63*X^4 +
      54*X^3 + 66*X^2 + 25*X + 14,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s251 : XPow fSeventeenA2 111005236200903961163148140780171362249543605359289
    (47*X^33 + 11*X^32 + 8*X^31 + 11*X^30 + 37*X^29 + 55*X^28 + 7*X^27 + 21*X^26 + 45*X^25 + 65*X^24 +
      32*X^23 + 50*X^22 + 56*X^21 + 41*X^20 + 24*X^19 + 24*X^18 + 6*X^17 + 65*X^16 + 5*X^15 +
      33*X^14 + 31*X^13 + 56*X^12 + 53*X^11 + 43*X^10 + X^9 + 39*X^8 + 44*X^7 + 34*X^6 + 29*X^5 +
      6*X^4 + 33*X^3 + 4*X^2 + 49*X + 46) :=
  mul_step (by norm_num) pSeventeenA2s250 pSeventeenA21 ⟨
    59,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s252 : XPow fSeventeenA2 222010472401807922326296281560342724499087210718578
    (26*X^33 + 49*X^32 + 45*X^31 + 35*X^30 + 27*X^29 + X^28 + 10*X^27 + 51*X^26 + 49*X^25 + 65*X^24 +
      40*X^23 + 63*X^22 + 58*X^21 + 52*X^20 + 50*X^19 + 58*X^18 + 10*X^17 + 49*X^16 + 55*X^15 +
      21*X^14 + 3*X^13 + 42*X^12 + 60*X^11 + 6*X^10 + 12*X^9 + 29*X^8 + 27*X^7 + 44*X^6 + 30*X^5 +
      25*X^4 + 11*X^3 + 36*X^2 + 6*X + 66) :=
  sq_step (by norm_num) pSeventeenA2s251 ⟨
    65*X^32 + 8*X^31 + 34*X^30 + 20*X^29 + 47*X^28 + 7*X^27 + 48*X^26 + 50*X^25 + 18*X^24 + 48*X^23 +
      8*X^22 + 39*X^21 + 52*X^20 + 14*X^19 + 58*X^18 + 17*X^17 + 25*X^16 + 12*X^15 + 42*X^14 +
      5*X^13 + 35*X^12 + 39*X^11 + 21*X^10 + 47*X^9 + 30*X^8 + 7*X^7 + 26*X^6 + 8*X^5 + 63*X^4 +
      66*X^3 + 13*X^2 + 17*X + 39,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s253 : XPow fSeventeenA2 444020944803615844652592563120685448998174421437156
    (36*X^33 + 27*X^32 + 47*X^31 + 46*X^30 + 48*X^29 + 27*X^28 + 37*X^27 + 62*X^26 + X^25 + 3*X^24 + X^22 +
      41*X^21 + 24*X^20 + 64*X^19 + 32*X^18 + 29*X^17 + 4*X^16 + 8*X^15 + 18*X^14 + 50*X^13 +
      65*X^12 + 43*X^11 + 9*X^10 + 60*X^9 + 14*X^7 + 29*X^6 + 43*X^5 + 14*X^4 + 55*X^3 + 45*X^2 +
      63*X + 4) :=
  sq_step (by norm_num) pSeventeenA2s252 ⟨
    6*X^32 + 65*X^31 + 52*X^30 + 63*X^29 + 25*X^28 + 11*X^27 + 66*X^26 + 9*X^25 + 23*X^24 + 44*X^23 +
      66*X^22 + 57*X^21 + 13*X^20 + 25*X^19 + 54*X^18 + 26*X^17 + 17*X^16 + 25*X^15 + 62*X^14 +
      55*X^13 + 17*X^12 + 33*X^11 + 43*X^10 + 34*X^9 + 36*X^8 + 66*X^7 + 8*X^6 + 30*X^5 + 15*X^4 +
      33*X^3 + 24*X^2 + 42*X + 49,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s254 : XPow fSeventeenA2 444020944803615844652592563120685448998174421437157
    (3*X^33 + 45*X^32 + 12*X^31 + 38*X^30 + 34*X^29 + 61*X^28 + 26*X^27 + 47*X^26 + 11*X^25 + 32*X^24 +
      39*X^23 + 61*X^22 + 29*X^21 + 35*X^20 + 3*X^19 + 23*X^18 + 2*X^17 + 6*X^16 + 33*X^15 + 12*X^14 +
      36*X^13 + 12*X^12 + 42*X^11 + 3*X^10 + 19*X^9 + 45*X^8 + 11*X^7 + 64*X^6 + 51*X^5 + 21*X^4 +
      10*X^3 + 24*X^2 + 41*X + 61) :=
  mul_step (by norm_num) pSeventeenA2s253 pSeventeenA21 ⟨
    36,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s255 : XPow fSeventeenA2 888041889607231689305185126241370897996348842874314
    (19*X^33 + 19*X^32 + 53*X^31 + 62*X^30 + 38*X^29 + 26*X^28 + 13*X^27 + 37*X^24 + 13*X^23 + 57*X^22 +
      38*X^21 + 27*X^20 + 12*X^19 + 64*X^18 + 44*X^17 + 3*X^16 + 57*X^15 + 21*X^14 + 41*X^13 +
      37*X^12 + 50*X^11 + 43*X^10 + 30*X^9 + X^8 + 15*X^7 + 45*X^6 + 54*X^5 + 62*X^4 + 44*X^3 +
      36*X^2 + 63*X + 45) :=
  sq_step (by norm_num) pSeventeenA2s254 ⟨
    9*X^32 + 63*X^31 + 11*X^30 + 38*X^29 + 36*X^28 + 48*X^27 + 3*X^26 + 62*X^25 + 11*X^24 + 54*X^23 +
      65*X^22 + 30*X^21 + 15*X^20 + 66*X^19 + 52*X^18 + 16*X^17 + 42*X^16 + 57*X^15 + 36*X^14 +
      21*X^13 + 7*X^12 + 3*X^11 + 43*X^10 + 56*X^9 + X^8 + 62*X^7 + 36*X^6 + 33*X^4 + 35*X^3 + 8*X^2 +
      22*X + 13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s256 : XPow fSeventeenA2 888041889607231689305185126241370897996348842874315
    (51*X^33 + 11*X^32 + 18*X^31 + 29*X^30 + 39*X^29 + 48*X^28 + 48*X^27 + 28*X^26 + 4*X^25 + 15*X^24 +
      51*X^23 + 56*X^22 + 65*X^21 + 6*X^20 + 58*X^19 + 52*X^18 + 28*X^17 + 15*X^16 + X^15 + 47*X^14 +
      31*X^13 + 2*X^12 + 66*X^11 + 39*X^10 + 65*X^9 + 63*X^8 + 2*X^7 + 26*X^6 + 35*X^5 + 38*X^3 +
      48*X^2 + 18*X + 8) :=
  mul_step (by norm_num) pSeventeenA2s255 pSeventeenA21 ⟨
    19,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s257 : XPow fSeventeenA2 1776083779214463378610370252482741795992697685748630
    (20*X^33 + 52*X^32 + 62*X^31 + 66*X^30 + 4*X^29 + 8*X^28 + 63*X^26 + 50*X^25 + 40*X^24 + 30*X^23 +
      63*X^22 + 22*X^21 + 5*X^20 + 17*X^19 + 60*X^18 + 16*X^17 + 47*X^16 + 64*X^15 + 62*X^14 +
      66*X^13 + 65*X^12 + 37*X^11 + 57*X^10 + 56*X^9 + 34*X^8 + 44*X^7 + 31*X^6 + 2*X^5 + 33*X^4 +
      2*X^3 + 8*X^2 + 45*X + 17) :=
  sq_step (by norm_num) pSeventeenA2s256 ⟨
    55*X^32 + 58*X^31 + 43*X^30 + 43*X^29 + 44*X^27 + 30*X^26 + 56*X^25 + 41*X^24 + 43*X^23 + 20*X^22 +
      2*X^21 + 65*X^20 + 52*X^19 + 28*X^18 + 48*X^17 + 64*X^16 + 2*X^15 + 57*X^14 + 56*X^13 +
      34*X^12 + 23*X^11 + 37*X^10 + 38*X^9 + 50*X^8 + 63*X^7 + 11*X^6 + 58*X^5 + 54*X^4 + 9*X^3 +
      9*X^2 + 48*X + 14,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s258 : XPow fSeventeenA2 1776083779214463378610370252482741795992697685748631
    (61*X^33 + 46*X^32 + 62*X^31 + 58*X^30 + 64*X^29 + 58*X^28 + 43*X^27 + 16*X^26 + 37*X^25 + 18*X^24 +
      32*X^23 + 48*X^22 + 45*X^21 + 53*X^20 + 29*X^19 + 35*X^18 + 31*X^17 + 48*X^16 + 48*X^15 +
      30*X^14 + 34*X^13 + 57*X^12 + 53*X^11 + 2*X^10 + 52*X^9 + 24*X^8 + 21*X^7 + 36*X^6 + 61*X^5 +
      65*X^4 + 63*X^3 + X^2 + 45*X + 19) :=
  mul_step (by norm_num) pSeventeenA2s257 pSeventeenA21 ⟨
    20,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s259 : XPow fSeventeenA2 3552167558428926757220740504965483591985395371497262
    (22*X^33 + 54*X^32 + 51*X^31 + 66*X^30 + X^29 + 44*X^28 + 21*X^27 + 32*X^26 + 65*X^25 + 12*X^24 +
      57*X^23 + 35*X^22 + 16*X^21 + 35*X^20 + 30*X^19 + 39*X^18 + 16*X^17 + 42*X^16 + 26*X^15 +
      18*X^14 + 33*X^13 + 55*X^12 + 41*X^11 + 29*X^10 + 58*X^9 + 10*X^8 + 51*X^7 + 16*X^6 + 2*X^5 +
      45*X^4 + 18*X^3 + 58*X^2 + 23*X + 50) :=
  sq_step (by norm_num) pSeventeenA2s258 ⟨
    36*X^32 + 27*X^31 + 12*X^30 + 40*X^29 + 30*X^28 + 48*X^27 + 41*X^26 + 56*X^25 + 7*X^24 + 22*X^23 +
      43*X^22 + 65*X^21 + 32*X^20 + 47*X^19 + 64*X^18 + 61*X^17 + 38*X^16 + 36*X^15 + 54*X^14 +
      46*X^13 + 36*X^12 + 26*X^11 + 3*X^10 + 43*X^9 + 27*X^8 + 54*X^7 + 2*X^6 + 60*X^5 + 19*X^4 +
      30*X^3 + 28*X^2 + 55*X + 57,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s260 : XPow fSeventeenA2 3552167558428926757220740504965483591985395371497263
    (17*X^33 + 20*X^32 + 8*X^31 + 47*X^30 + 52*X^29 + 58*X^28 + 10*X^27 + 41*X^26 + 2*X^25 + 17*X^24 +
      21*X^23 + 58*X^22 + 12*X^21 + 16*X^20 + 25*X^19 + 57*X^18 + 11*X^17 + 62*X^16 + 16*X^15 +
      47*X^14 + 41*X^13 + 63*X^12 + 38*X^11 + 12*X^10 + 3*X^9 + 29*X^8 + 5*X^7 + 26*X^6 + 49*X^5 +
      27*X^4 + 18*X^3 + 55*X^2 + 54*X + 41) :=
  mul_step (by norm_num) pSeventeenA2s259 pSeventeenA21 ⟨
    22,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s261 : XPow fSeventeenA2 7104335116857853514441481009930967183970790742994526
    (13*X^33 + 48*X^32 + 45*X^31 + 26*X^30 + 11*X^29 + 4*X^28 + 21*X^27 + 50*X^26 + 5*X^25 + 38*X^24 +
      46*X^23 + 15*X^22 + 65*X^21 + 66*X^20 + 35*X^19 + 31*X^18 + 2*X^17 + 4*X^16 + 40*X^15 +
      63*X^14 + 36*X^13 + 29*X^12 + 31*X^11 + 41*X^10 + 65*X^9 + 24*X^8 + 55*X^7 + 38*X^6 + 29*X^5 +
      66*X^4 + 63*X^3 + 56*X^2 + 8*X + 18) :=
  sq_step (by norm_num) pSeventeenA2s260 ⟨
    21*X^32 + 63*X^31 + 37*X^30 + 61*X^29 + 12*X^28 + 4*X^27 + 15*X^26 + 38*X^25 + 36*X^24 + 65*X^23 +
      23*X^22 + 19*X^21 + 12*X^20 + 66*X^19 + 52*X^18 + 2*X^17 + 65*X^16 + 23*X^14 + 3*X^13 +
      36*X^12 + 24*X^11 + 19*X^10 + 21*X^9 + 32*X^8 + 61*X^7 + 21*X^6 + X^5 + 66*X^4 + 61*X^3 + X^2 +
      13*X + 62,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s262 : XPow fSeventeenA2 7104335116857853514441481009930967183970790742994527
    (17*X^33 + 48*X^32 + 10*X^31 + 26*X^30 + 27*X^29 + 52*X^28 + 37*X^27 + 3*X^26 + 26*X^25 + 65*X^24 +
      25*X^23 + 35*X^22 + 25*X^21 + 45*X^20 + 41*X^19 + 11*X^18 + 7*X^17 + 43*X^16 + 7*X^15 +
      26*X^14 + 39*X^13 + 44*X^12 + 25*X^11 + 50*X^10 + 29*X^9 + 42*X^8 + 65*X^7 + 31*X^6 + 44*X^5 +
      47*X^4 + 8*X^3 + 33*X^2 + 63*X + 9) :=
  mul_step (by norm_num) pSeventeenA2s261 pSeventeenA21 ⟨
    13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s263 : XPow fSeventeenA2 14208670233715707028882962019861934367941581485989054
    (16*X^33 + 25*X^32 + 15*X^31 + 2*X^30 + 42*X^29 + 26*X^28 + X^27 + 65*X^26 + 46*X^25 + 42*X^24 +
      10*X^23 + 21*X^22 + 56*X^21 + 34*X^20 + 29*X^19 + 6*X^18 + 14*X^17 + 58*X^16 + 19*X^15 +
      50*X^14 + X^13 + 56*X^12 + 34*X^11 + 64*X^10 + 25*X^9 + 61*X^8 + 36*X^7 + 21*X^6 + 5*X^5 +
      48*X^4 + 40*X^3 + 44*X^2 + 48*X + 44) :=
  sq_step (by norm_num) pSeventeenA2s262 ⟨
    21*X^32 + 10*X^31 + 12*X^30 + 55*X^29 + 63*X^28 + 40*X^27 + 60*X^26 + 6*X^25 + 64*X^24 + 56*X^23 +
      11*X^22 + 45*X^21 + 45*X^20 + 6*X^19 + 56*X^18 + 48*X^17 + 57*X^16 + 21*X^15 + 24*X^14 +
      16*X^13 + 65*X^12 + 59*X^11 + 33*X^10 + 14*X^9 + 14*X^8 + 28*X^7 + 25*X^6 + 60*X^5 + 44*X^4 +
      20*X^3 + 48*X^2 + 46*X + 21,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s264 : XPow fSeventeenA2 14208670233715707028882962019861934367941581485989055
    (59*X^33 + 29*X^32 + 39*X^31 + 45*X^30 + 44*X^29 + 34*X^28 + 49*X^27 + 59*X^26 + 53*X^25 + 54*X^24 +
      23*X^23 + 50*X^22 + 66*X^21 + 31*X^20 + 8*X^19 + 56*X^18 + 5*X^17 + 33*X^16 + 12*X^15 +
      66*X^14 + 58*X^13 + 50*X^12 + 34*X^11 + 22*X^10 + 62*X^9 + 20*X^8 + 13*X^7 + 59*X^6 + 57*X^5 +
      10*X^4 + 21*X^3 + 53*X^2 + 53*X + 42) :=
  mul_step (by norm_num) pSeventeenA2s263 pSeventeenA21 ⟨
    16,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s265 : XPow fSeventeenA2 28417340467431414057765924039723868735883162971978110
    (34*X^33 + 38*X^32 + 66*X^31 + 44*X^30 + 36*X^29 + 12*X^28 + 3*X^27 + 11*X^26 + 43*X^25 + 37*X^24 +
      4*X^22 + 50*X^21 + 35*X^19 + 63*X^18 + 36*X^17 + 23*X^16 + 56*X^15 + 14*X^14 + 47*X^13 +
      16*X^12 + 9*X^11 + 11*X^10 + 34*X^9 + 59*X^8 + 26*X^7 + 57*X^6 + 58*X^5 + 10*X^4 + 30*X^3 +
      8*X^2 + 3*X + 25) :=
  sq_step (by norm_num) pSeventeenA2s264 ⟨
    64*X^32 + 7*X^31 + 45*X^30 + 33*X^29 + 43*X^28 + 62*X^27 + 4*X^26 + 49*X^25 + 34*X^24 + 41*X^23 +
      9*X^22 + 62*X^21 + 22*X^20 + 54*X^19 + 41*X^18 + 36*X^17 + 55*X^16 + 60*X^15 + 57*X^14 +
      43*X^13 + 28*X^12 + 7*X^11 + 47*X^10 + 13*X^9 + 51*X^8 + 20*X^7 + X^6 + 41*X^5 + 22*X^4 +
      13*X^3 + 31*X^2 + 51*X + 49,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s266 : XPow fSeventeenA2 56834680934862828115531848079447737471766325943956220
    (31*X^33 + 34*X^32 + 7*X^31 + 33*X^30 + 51*X^29 + 12*X^27 + 4*X^26 + 19*X^24 + 46*X^23 + 59*X^22 +
      48*X^21 + 56*X^20 + 48*X^19 + 54*X^18 + 25*X^17 + 52*X^16 + 32*X^15 + 43*X^14 + 53*X^13 +
      48*X^12 + 50*X^11 + 8*X^10 + 50*X^9 + 51*X^8 + 43*X^7 + 14*X^6 + 30*X^5 + 49*X^4 + 30*X^3 +
      35*X^2 + 11*X + 32) :=
  sq_step (by norm_num) pSeventeenA2s265 ⟨
    17*X^32 + 49*X^31 + 21*X^30 + 32*X^29 + 58*X^28 + 49*X^27 + 20*X^26 + 27*X^25 + 47*X^24 + 24*X^23 +
      18*X^22 + 61*X^21 + 14*X^20 + 35*X^19 + 6*X^18 + 19*X^17 + 26*X^16 + 54*X^15 + 57*X^14 +
      30*X^13 + 32*X^12 + 12*X^11 + 2*X^10 + 27*X^9 + 19*X^8 + 29*X^7 + 52*X^6 + 62*X^5 + 36*X^4 +
      48*X^3 + 46*X^2 + 62*X + 7,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s267 : XPow fSeventeenA2 113669361869725656231063696158895474943532651887912440
    (9*X^33 + 13*X^32 + 44*X^31 + 57*X^30 + 57*X^29 + 32*X^28 + 9*X^27 + 38*X^26 + 51*X^25 + 17*X^24 +
      20*X^23 + 44*X^22 + 17*X^21 + 49*X^20 + 21*X^19 + 43*X^18 + 30*X^17 + 37*X^16 + 25*X^15 +
      8*X^14 + 11*X^13 + 28*X^11 + 63*X^10 + 15*X^9 + 44*X^8 + 22*X^7 + 32*X^6 + 54*X^5 + 25*X^4 +
      7*X^3 + 37*X^2 + 25*X + 17) :=
  sq_step (by norm_num) pSeventeenA2s266 ⟨
    23*X^32 + 38*X^31 + 41*X^30 + 3*X^29 + 41*X^28 + 48*X^27 + 5*X^26 + 23*X^25 + 53*X^24 + 64*X^23 +
      13*X^22 + 8*X^21 + 19*X^20 + 9*X^19 + 34*X^18 + 64*X^17 + 43*X^16 + 4*X^15 + 11*X^14 + 18*X^13 +
      36*X^12 + 58*X^11 + 33*X^10 + 24*X^9 + 16*X^8 + 54*X^7 + 63*X^6 + 43*X^5 + 56*X^4 + 53*X^3 +
      27*X^2 + 61*X + 12,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s268 : XPow fSeventeenA2 227338723739451312462127392317790949887065303775824880
    (55*X^33 + 34*X^32 + 13*X^31 + 3*X^30 + 12*X^29 + 63*X^28 + X^27 + 46*X^26 + 40*X^25 + 36*X^24 +
      42*X^23 + 48*X^22 + 47*X^21 + 35*X^20 + 39*X^19 + 31*X^18 + 37*X^17 + 44*X^16 + 50*X^15 +
      47*X^14 + 54*X^13 + 66*X^12 + 8*X^11 + 26*X^10 + 65*X^9 + 39*X^8 + 17*X^7 + 50*X^6 + 36*X^5 +
      32*X^4 + 13*X^3 + X^2 + 47*X + 2) :=
  sq_step (by norm_num) pSeventeenA2s267 ⟨
    14*X^32 + 46*X^31 + 66*X^30 + 63*X^29 + 63*X^28 + 3*X^27 + 41*X^26 + 40*X^25 + 58*X^24 + 48*X^23 +
      59*X^22 + 25*X^21 + 64*X^20 + 28*X^19 + 59*X^18 + 33*X^17 + 43*X^16 + 10*X^15 + 24*X^14 +
      14*X^13 + 32*X^12 + X^10 + 23*X^9 + 56*X^8 + 45*X^7 + 62*X^6 + 64*X^5 + 59*X^4 + 31*X^3 +
      31*X^2 + 27*X + 47,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s269 : XPow fSeventeenA2 454677447478902624924254784635581899774130607551649760
    (23*X^33 + 2*X^32 + 10*X^31 + 54*X^30 + 62*X^29 + 43*X^28 + 17*X^27 + 38*X^26 + 28*X^25 + 48*X^24 +
      17*X^23 + 9*X^22 + 41*X^21 + 26*X^20 + 16*X^19 + 66*X^18 + 48*X^17 + 66*X^16 + 13*X^15 +
      10*X^14 + 37*X^13 + 58*X^12 + 63*X^11 + 33*X^10 + 55*X^9 + 64*X^8 + 23*X^7 + 43*X^6 + 27*X^5 +
      10*X^4 + 59*X^3 + 2*X^2 + 42*X + 16) :=
  sq_step (by norm_num) pSeventeenA2s268 ⟨
    10*X^32 + 26*X^31 + 37*X^30 + 32*X^29 + 38*X^28 + 7*X^27 + 49*X^26 + 17*X^25 + 15*X^24 + 49*X^23 +
      22*X^22 + 55*X^21 + 55*X^20 + 60*X^19 + 40*X^18 + 22*X^17 + 19*X^16 + 27*X^15 + 66*X^14 +
      33*X^13 + 4*X^12 + 15*X^11 + 27*X^10 + 64*X^9 + 52*X^8 + 63*X^7 + 34*X^6 + 32*X^5 + 42*X^4 +
      28*X^3 + 50*X^2 + 30*X + 62,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s270 : XPow fSeventeenA2 909354894957805249848509569271163799548261215103299520
    (65*X^33 + 15*X^32 + 13*X^31 + 15*X^30 + 46*X^29 + 40*X^28 + 28*X^27 + 38*X^26 + 38*X^25 + 33*X^24 +
      4*X^23 + 5*X^22 + 12*X^21 + 46*X^20 + 11*X^19 + 27*X^18 + 7*X^17 + 40*X^16 + 21*X^15 + 29*X^14 +
      6*X^13 + 64*X^12 + 38*X^11 + 22*X^10 + 45*X^9 + 47*X^8 + 64*X^7 + 42*X^6 + 43*X^5 + 55*X^4 +
      29*X^3 + 36*X^2 + 8*X + 57) :=
  sq_step (by norm_num) pSeventeenA2s269 ⟨
    60*X^32 + 52*X^31 + 24*X^30 + 29*X^29 + 7*X^28 + 62*X^27 + 37*X^26 + 3*X^25 + 49*X^24 + 35*X^23 +
      6*X^22 + 66*X^21 + 43*X^20 + 31*X^19 + 48*X^18 + 50*X^17 + 28*X^16 + 62*X^15 + 28*X^14 +
      22*X^13 + 59*X^12 + 47*X^11 + 34*X^10 + 36*X^9 + 30*X^8 + 24*X^7 + 43*X^6 + 7*X^5 + 6*X^4 +
      20*X^3 + 64*X^2 + 36*X + 55,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s271 : XPow fSeventeenA2 1818709789915610499697019138542327599096522430206599040
    (33*X^33 + 48*X^32 + 57*X^31 + 56*X^30 + 60*X^29 + 2*X^28 + 57*X^27 + 16*X^26 + 16*X^25 + 59*X^24 +
      8*X^23 + 59*X^22 + 52*X^21 + 32*X^20 + 47*X^19 + 36*X^18 + 34*X^17 + 6*X^16 + 59*X^15 +
      26*X^14 + 39*X^13 + 41*X^12 + 23*X^11 + 19*X^10 + 9*X^9 + 6*X^8 + 10*X^7 + 32*X^6 + 11*X^5 +
      X^4 + 23*X^3 + 53*X^2 + 11*X + 23) :=
  sq_step (by norm_num) pSeventeenA2s270 ⟨
    4*X^32 + 49*X^31 + 21*X^30 + 8*X^29 + 61*X^28 + 25*X^27 + 59*X^26 + X^25 + 57*X^24 + 56*X^23 +
      9*X^22 + 23*X^21 + 13*X^20 + 66*X^19 + 31*X^18 + 46*X^17 + 20*X^16 + 34*X^15 + 46*X^14 +
      38*X^13 + 61*X^12 + 66*X^11 + 26*X^10 + 66*X^9 + 35*X^8 + 22*X^7 + 11*X^6 + 7*X^5 + 51*X^4 +
      53*X^3 + 43*X^2 + 14*X + 60,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s272 : XPow fSeventeenA2 3637419579831220999394038277084655198193044860413198080
    (36*X^33 + 19*X^32 + 42*X^31 + 61*X^30 + 54*X^29 + 44*X^28 + 33*X^27 + 34*X^26 + 6*X^25 + 39*X^24 +
      39*X^23 + 52*X^22 + 41*X^21 + 16*X^20 + 61*X^19 + 25*X^18 + 9*X^17 + 54*X^16 + 31*X^15 +
      37*X^14 + 3*X^13 + 46*X^12 + 39*X^11 + 38*X^10 + 61*X^9 + 21*X^8 + 61*X^7 + 9*X^6 + 38*X^5 +
      6*X^4 + 13*X^3 + 3*X^2 + 41*X + 20) :=
  sq_step (by norm_num) pSeventeenA2s271 ⟨
    17*X^32 + 30*X^31 + 56*X^30 + 27*X^29 + 13*X^28 + 53*X^27 + 42*X^26 + 28*X^25 + 45*X^24 + 6*X^23 +
      19*X^22 + 14*X^21 + 24*X^20 + X^19 + 36*X^18 + 53*X^17 + 38*X^16 + 32*X^15 + 37*X^14 + 11*X^13 +
      57*X^12 + 22*X^11 + 12*X^10 + 56*X^9 + 61*X^8 + 25*X^7 + 28*X^6 + 62*X^5 + 9*X^4 + 5*X^3 +
      64*X^2 + 49*X + 39,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s273 : XPow fSeventeenA2 3637419579831220999394038277084655198193044860413198081
    (62*X^33 + 40*X^32 + 27*X^31 + 44*X^30 + 51*X^29 + 57*X^28 + 65*X^27 + 52*X^26 + 47*X^25 + 4*X^24 +
      23*X^23 + 61*X^22 + 21*X^21 + 32*X^20 + 63*X^19 + 3*X^18 + 52*X^17 + 29*X^16 + 52*X^15 +
      32*X^14 + 17*X^13 + 8*X^12 + 4*X^11 + 4*X^10 + 40*X^9 + 25*X^8 + 58*X^7 + 59*X^6 + 43*X^5 +
      46*X^4 + 35*X^3 + 2*X^2 + 57*X + 61) :=
  mul_step (by norm_num) pSeventeenA2s272 pSeventeenA21 ⟨
    36,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s274 : XPow fSeventeenA2 7274839159662441998788076554169310396386089720826396162
    (13*X^33 + 2*X^32 + 59*X^31 + 57*X^30 + 59*X^29 + 34*X^28 + 55*X^27 + 13*X^26 + 54*X^25 + 38*X^24 +
      60*X^23 + 13*X^22 + 32*X^21 + 64*X^20 + 15*X^19 + 9*X^18 + 62*X^17 + 33*X^15 + 59*X^14 +
      53*X^13 + 11*X^12 + 56*X^11 + 50*X^10 + 33*X^9 + 24*X^8 + 8*X^7 + 2*X^6 + 17*X^5 + 12*X^4 +
      7*X^3 + 34*X^2 + 48*X + 64) :=
  sq_step (by norm_num) pSeventeenA2s273 ⟨
    25*X^32 + 30*X^31 + 17*X^30 + 27*X^29 + 37*X^28 + 2*X^27 + 65*X^26 + 37*X^25 + 16*X^24 + 22*X^23 +
      60*X^22 + 16*X^21 + 45*X^20 + 64*X^19 + 19*X^18 + 51*X^17 + 23*X^16 + 21*X^15 + 39*X^14 +
      61*X^13 + 7*X^12 + 53*X^11 + 42*X^10 + 55*X^9 + 53*X^8 + 62*X^7 + 37*X^6 + 57*X^5 + 40*X^4 +
      49*X^3 + 9*X^2 + 66*X + 33,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s275 : XPow fSeventeenA2 14549678319324883997576153108338620792772179441652792324
    (35*X^33 + 56*X^32 + 7*X^31 + 20*X^30 + 27*X^29 + 26*X^28 + 25*X^27 + X^26 + 55*X^25 + 12*X^24 +
      49*X^23 + 13*X^22 + 16*X^21 + 49*X^20 + 48*X^19 + 31*X^18 + 36*X^17 + 54*X^16 + 19*X^15 +
      39*X^13 + 29*X^12 + 41*X^11 + 3*X^10 + 24*X^9 + 40*X^8 + 59*X^7 + 2*X^6 + 63*X^5 + 58*X^4 +
      29*X^3 + 23*X^2 + 31*X + 40) :=
  sq_step (by norm_num) pSeventeenA2s274 ⟨
    35*X^32 + 51*X^31 + 2*X^30 + 43*X^29 + 42*X^28 + 66*X^27 + 48*X^26 + 34*X^25 + 26*X^24 + 32*X^23 +
      16*X^22 + 53*X^21 + 65*X^20 + 32*X^19 + 29*X^18 + 22*X^17 + 65*X^16 + 51*X^15 + 54*X^14 +
      3*X^12 + 12*X^11 + 11*X^10 + 39*X^9 + 43*X^8 + 24*X^7 + 16*X^6 + 5*X^5 + 21*X^4 + 14*X^3 +
      32*X^2 + 21*X + 15,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s276 : XPow fSeventeenA2 29099356638649767995152306216677241585544358883305584648
    (33*X^33 + 21*X^32 + 33*X^31 + 59*X^30 + 14*X^29 + 40*X^28 + 59*X^27 + 63*X^26 + 2*X^25 + X^24 +
      19*X^23 + 60*X^22 + 10*X^21 + 53*X^20 + 41*X^19 + 61*X^18 + 5*X^17 + 6*X^16 + 27*X^15 +
      26*X^14 + 8*X^13 + 62*X^12 + 6*X^11 + 45*X^10 + 11*X^9 + 49*X^8 + 26*X^7 + 61*X^6 + 38*X^5 +
      47*X^4 + 64*X^3 + 35*X^2 + 5*X + 14) :=
  sq_step (by norm_num) pSeventeenA2s275 ⟨
    19*X^32 + 66*X^31 + 56*X^30 + 22*X^29 + 55*X^28 + 55*X^27 + 22*X^26 + X^25 + 19*X^24 + 49*X^23 +
      2*X^22 + 45*X^21 + 43*X^19 + 7*X^18 + 29*X^17 + 41*X^16 + 52*X^15 + 9*X^14 + 8*X^13 + 7*X^12 +
      37*X^11 + 5*X^10 + 30*X^9 + 48*X^8 + 53*X^7 + 8*X^6 + 50*X^5 + 14*X^4 + 20*X^3 + 3*X^2 + 33*X +
      2,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s277 : XPow fSeventeenA2 29099356638649767995152306216677241585544358883305584649
    (66*X^33 + 20*X^32 + 39*X^31 + 16*X^30 + 52*X^29 + 14*X^28 + 30*X^27 + 33*X^26 + 53*X^25 + 26*X^24 +
      39*X^23 + 6*X^22 + 52*X^21 + 20*X^20 + 40*X^19 + 33*X^18 + 60*X^17 + 14*X^16 + 23*X^15 +
      29*X^14 + 41*X^13 + 39*X^12 + 25*X^11 + 9*X^10 + 5*X^9 + 60*X^8 + 11*X^7 + 7*X^6 + 53*X^5 +
      44*X^4 + 42*X^3 + 53*X^2 + 20*X + 28) :=
  mul_step (by norm_num) pSeventeenA2s276 pSeventeenA21 ⟨
    33,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s278 : XPow fSeventeenA2 58198713277299535990304612433354483171088717766611169298
    (35*X^33 + 30*X^32 + 39*X^31 + 3*X^30 + 27*X^29 + 66*X^28 + 8*X^27 + 17*X^26 + 6*X^25 + 41*X^24 +
      37*X^23 + 58*X^22 + 16*X^21 + 24*X^20 + 44*X^19 + 46*X^18 + 15*X^17 + 29*X^16 + 30*X^15 +
      14*X^14 + 57*X^13 + 55*X^12 + 56*X^11 + 10*X^10 + 55*X^9 + 26*X^8 + 46*X^7 + 64*X^6 + 7*X^5 +
      56*X^4 + 27*X^3 + 17*X^2 + 38*X + 53) :=
  sq_step (by norm_num) pSeventeenA2s277 ⟨
    X^32 + 4*X^31 + 55*X^30 + 5*X^29 + 44*X^28 + 22*X^27 + 64*X^26 + 17*X^25 + 47*X^24 + 39*X^23 +
      22*X^22 + 56*X^21 + 23*X^20 + 6*X^19 + 3*X^18 + 60*X^17 + 33*X^16 + 53*X^15 + 6*X^14 + 26*X^13 +
      4*X^12 + X^11 + 23*X^10 + 66*X^9 + 53*X^8 + 23*X^7 + 47*X^6 + 35*X^5 + 11*X^4 + 37*X^3 +
      45*X^2 + 39*X + 31,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s279 : XPow fSeventeenA2 116397426554599071980609224866708966342177435533222338596
    (8*X^33 + 9*X^32 + 9*X^31 + 59*X^30 + 18*X^29 + 33*X^28 + 41*X^27 + 54*X^26 + 40*X^25 + 23*X^24 +
      60*X^23 + 22*X^22 + 20*X^21 + 39*X^20 + 20*X^19 + 58*X^18 + 39*X^17 + 31*X^16 + 42*X^15 +
      56*X^14 + 44*X^13 + X^12 + 47*X^11 + 66*X^10 + 27*X^9 + 41*X^8 + 56*X^7 + X^6 + 2*X^5 + 59*X^4 +
      21*X^3 + 24*X^2 + 42*X + 53) :=
  sq_step (by norm_num) pSeventeenA2s278 ⟨
    19*X^32 + 55*X^31 + 45*X^30 + 20*X^29 + 60*X^28 + 38*X^27 + 23*X^26 + 9*X^25 + 28*X^24 + 38*X^23 +
      58*X^22 + 30*X^21 + 53*X^20 + 37*X^19 + 31*X^18 + 33*X^17 + 34*X^16 + 22*X^15 + 58*X^14 +
      30*X^13 + 61*X^12 + 9*X^11 + 6*X^10 + 11*X^9 + 29*X^8 + 42*X^7 + 60*X^6 + 47*X^5 + 37*X^4 +
      3*X^3 + 45*X^2 + 62*X + 54,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s280 : XPow fSeventeenA2 116397426554599071980609224866708966342177435533222338597
    (26*X^33 + 16*X^32 + 44*X^31 + 53*X^30 + 42*X^29 + 24*X^28 + 46*X^27 + 13*X^26 + 62*X^25 + 15*X^24 +
      23*X^23 + 17*X^22 + 55*X^21 + 21*X^20 + 59*X^19 + 60*X^18 + 38*X^17 + 49*X^16 + 37*X^15 +
      43*X^14 + 2*X^13 + 55*X^12 + 51*X^11 + 59*X^10 + 8*X^9 + 48*X^8 + 64*X^7 + 29*X^6 + 30*X^5 +
      6*X^4 + 46*X^3 + 11*X^2 + 24*X + 21) :=
  mul_step (by norm_num) pSeventeenA2s279 pSeventeenA21 ⟨
    8,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s281 : XPow fSeventeenA2 232794853109198143961218449733417932684354871066444677194
    (28*X^33 + 36*X^32 + 19*X^31 + 19*X^30 + 19*X^29 + 29*X^28 + 25*X^27 + 7*X^26 + 33*X^25 + 25*X^24 +
      36*X^23 + 5*X^22 + 12*X^21 + 18*X^20 + 63*X^19 + 16*X^18 + 27*X^17 + 53*X^16 + 13*X^15 +
      19*X^14 + 62*X^13 + 54*X^12 + 39*X^11 + 48*X^10 + 51*X^9 + 9*X^8 + 28*X^7 + 5*X^6 + 21*X^5 +
      41*X^4 + 49*X^3 + 37*X^2 + 64*X + 10) :=
  sq_step (by norm_num) pSeventeenA2s280 ⟨
    6*X^32 + 24*X^31 + 4*X^30 + 45*X^29 + 59*X^28 + 21*X^27 + 2*X^26 + 50*X^25 + X^24 + 62*X^23 +
      65*X^22 + 6*X^21 + 29*X^20 + 50*X^19 + 51*X^18 + 10*X^17 + 42*X^16 + 57*X^15 + 49*X^14 +
      26*X^13 + 23*X^12 + 37*X^11 + 21*X^10 + 42*X^9 + 59*X^8 + 21*X^7 + 34*X^6 + 4*X^5 + 45*X^3 +
      37*X + 40,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s282 : XPow fSeventeenA2 465589706218396287922436899466835865368709742132889354388
    (31*X^33 + 49*X^32 + 17*X^31 + 41*X^30 + 63*X^29 + X^28 + 41*X^27 + 15*X^26 + 18*X^25 + 38*X^24 +
      12*X^23 + 13*X^22 + 59*X^20 + X^19 + 65*X^18 + 17*X^17 + 34*X^16 + 19*X^15 + 6*X^14 + 66*X^13 +
      33*X^12 + 20*X^11 + 36*X^10 + 46*X^9 + 20*X^8 + 63*X^7 + 14*X^6 + 22*X^5 + 44*X^4 + 57*X^3 +
      6*X^2 + 61*X + 44) :=
  sq_step (by norm_num) pSeventeenA2s281 ⟨
    47*X^32 + 64*X^31 + 33*X^30 + 58*X^29 + 66*X^28 + 22*X^27 + 10*X^26 + 29*X^25 + 23*X^24 + 38*X^23 +
      12*X^22 + 12*X^21 + 27*X^20 + 55*X^19 + 29*X^18 + 50*X^17 + 19*X^16 + 34*X^15 + 59*X^14 +
      39*X^12 + 10*X^11 + 54*X^10 + 30*X^9 + 66*X^8 + 17*X^7 + X^6 + 41*X^5 + 49*X^4 + 32*X^3 +
      33*X^2 + 6*X + 1,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s283 : XPow fSeventeenA2 465589706218396287922436899466835865368709742132889354389
    (6*X^33 + 19*X^32 + 8*X^31 + 6*X^30 + 61*X^29 + 17*X^28 + 51*X^27 + 39*X^26 + 30*X^25 + 47*X^24 +
      42*X^23 + 47*X^22 + 54*X^21 + 30*X^20 + 27*X^19 + 23*X^18 + 36*X^17 + 21*X^16 + 58*X^15 +
      37*X^14 + 62*X^13 + 51*X^12 + 3*X^11 + 36*X^10 + X^9 + 32*X^8 + 32*X^7 + X^6 + 7*X^5 + 24*X^4 +
      41*X^3 + 33*X^2 + 7*X + 6) :=
  mul_step (by norm_num) pSeventeenA2s282 pSeventeenA21 ⟨
    31,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s284 : XPow fSeventeenA2 931179412436792575844873798933671730737419484265778708778
    (56*X^33 + 2*X^32 + 2*X^31 + 60*X^30 + 66*X^29 + 32*X^28 + 29*X^27 + 23*X^26 + 14*X^25 + 10*X^24 +
      51*X^23 + 5*X^22 + 44*X^21 + 7*X^20 + 38*X^19 + 64*X^18 + 19*X^17 + 40*X^16 + 21*X^15 +
      53*X^14 + 34*X^13 + 16*X^12 + 52*X^11 + 37*X^10 + 15*X^9 + 55*X^8 + 60*X^7 + 8*X^6 + 55*X^5 +
      42*X^4 + 40*X^3 + 62*X^2 + 53*X + 5) :=
  sq_step (by norm_num) pSeventeenA2s283 ⟨
    36*X^32 + 3*X^31 + 51*X^30 + 51*X^29 + 14*X^28 + 29*X^27 + 3*X^26 + 44*X^25 + 45*X^24 + 40*X^23 +
      41*X^22 + 45*X^21 + 61*X^20 + 44*X^19 + 21*X^18 + X^17 + 63*X^16 + 56*X^15 + 41*X^14 + 28*X^13 +
      19*X^12 + 46*X^11 + 60*X^10 + 22*X^9 + 65*X^8 + 31*X^7 + 55*X^6 + 51*X^5 + 12*X^4 + 64*X^3 +
      52*X^2 + 60*X + 52,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s285 : XPow fSeventeenA2 1862358824873585151689747597867343461474838968531557417556
    (32*X^33 + 21*X^32 + 62*X^31 + 60*X^30 + 5*X^29 + 3*X^28 + 29*X^27 + 55*X^26 + 39*X^25 + 14*X^24 +
      50*X^23 + 56*X^22 + 45*X^21 + 39*X^20 + 37*X^19 + 30*X^18 + 31*X^17 + 12*X^16 + 24*X^15 +
      3*X^14 + 60*X^13 + 25*X^12 + 45*X^11 + 36*X^10 + 30*X^9 + 18*X^8 + 49*X^7 + 56*X^6 + 64*X^5 +
      31*X^4 + 5*X^3 + 58*X^2 + 18*X + 30) :=
  sq_step (by norm_num) pSeventeenA2s284 ⟨
    54*X^32 + 54*X^31 + 55*X^30 + 49*X^29 + 34*X^28 + 42*X^27 + 29*X^24 + 32*X^23 + 31*X^22 + 63*X^21 +
      23*X^20 + 25*X^19 + 41*X^18 + 6*X^17 + 59*X^15 + 55*X^14 + 23*X^13 + 21*X^12 + 20*X^11 +
      32*X^10 + 40*X^9 + 26*X^8 + 59*X^7 + 49*X^6 + 42*X^5 + 63*X^4 + 15*X^3 + 23*X^2 + 6*X + 37,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s286 : XPow fSeventeenA2 1862358824873585151689747597867343461474838968531557417557
    (22*X^33 + 23*X^32 + 11*X^30 + 39*X^29 + 28*X^28 + 23*X^27 + 65*X^26 + 36*X^25 + 4*X^24 + 60*X^23 +
      33*X^22 + 36*X^21 + 41*X^20 + 34*X^19 + 48*X^18 + 40*X^17 + 52*X^16 + 61*X^15 + 56*X^14 +
      29*X^13 + 10*X^12 + 43*X^11 + 24*X^10 + 20*X^9 + 17*X^8 + 40*X^7 + 38*X^6 + 49*X^5 + 12*X^4 +
      12*X^3 + 28*X^2 + 48*X + 17) :=
  mul_step (by norm_num) pSeventeenA2s285 pSeventeenA21 ⟨
    32,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s287 : XPow fSeventeenA2 3724717649747170303379495195734686922949677937063114835114
    (22*X^33 + 31*X^32 + 66*X^31 + 19*X^30 + 38*X^29 + 12*X^28 + 17*X^27 + 29*X^26 + 39*X^25 + 48*X^24 +
      46*X^23 + X^22 + 62*X^21 + 25*X^20 + 44*X^19 + X^18 + 64*X^17 + 20*X^16 + 46*X^15 + 37*X^14 +
      52*X^13 + 48*X^12 + 58*X^11 + 41*X^10 + 38*X^9 + 63*X^8 + 64*X^7 + 32*X^6 + 26*X^5 + 49*X^4 +
      36*X^3 + 48*X^2 + 52) :=
  sq_step (by norm_num) pSeventeenA2s286 ⟨
    15*X^32 + 64*X^31 + 50*X^30 + 57*X^29 + 21*X^28 + 49*X^27 + 49*X^26 + 30*X^25 + 53*X^24 + 4*X^23 +
      14*X^22 + 54*X^21 + 51*X^20 + 30*X^19 + 48*X^18 + 49*X^17 + 37*X^16 + 38*X^15 + 9*X^14 +
      29*X^13 + 35*X^12 + 19*X^11 + 18*X^10 + 18*X^9 + 27*X^8 + 27*X^7 + 11*X^6 + 19*X^5 + 61*X^4 +
      9*X^3 + 12*X^2 + 2*X + 15,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s288 : XPow fSeventeenA2 7449435299494340606758990391469373845899355874126229670228
    (23*X^33 + 7*X^32 + 59*X^31 + 20*X^30 + 34*X^29 + 52*X^28 + 57*X^27 + 56*X^26 + 8*X^25 + 13*X^24 +
      21*X^23 + 59*X^22 + 52*X^21 + 21*X^20 + 27*X^19 + 6*X^18 + 4*X^17 + 62*X^16 + 36*X^15 +
      63*X^14 + 12*X^13 + 26*X^12 + 10*X^11 + 62*X^10 + 31*X^9 + 63*X^8 + 53*X^7 + 18*X^6 + 32*X^5 +
      12*X^4 + 33*X^3 + 60*X^2 + 62*X + 33) :=
  sq_step (by norm_num) pSeventeenA2s287 ⟨
    15*X^32 + 14*X^31 + 47*X^30 + 54*X^29 + 48*X^28 + 54*X^27 + 12*X^26 + 66*X^25 + 25*X^24 + 25*X^23 +
      8*X^22 + 61*X^21 + 14*X^20 + 32*X^19 + 55*X^18 + 17*X^17 + 14*X^16 + 46*X^15 + 23*X^14 +
      61*X^13 + X^12 + 20*X^11 + 59*X^10 + 15*X^9 + 5*X^8 + 30*X^7 + 36*X^6 + 2*X^5 + 40*X^4 +
      21*X^3 + 35*X^2 + 32*X + 13,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s289 : XPow fSeventeenA2 14898870598988681213517980782938747691798711748252459340456
    (12*X^33 + 13*X^32 + 56*X^31 + 40*X^30 + 14*X^29 + 3*X^28 + 18*X^27 + 56*X^26 + 37*X^25 + 18*X^24 +
      56*X^23 + 4*X^22 + 56*X^21 + 33*X^20 + 33*X^19 + 24*X^18 + 31*X^17 + 35*X^16 + 47*X^15 +
      54*X^14 + 40*X^13 + 14*X^12 + 10*X^11 + 38*X^10 + 16*X^9 + 6*X^8 + 41*X^7 + 12*X^6 + 27*X^5 +
      37*X^4 + 13*X^3 + 46*X^2 + 62*X + 15) :=
  sq_step (by norm_num) pSeventeenA2s288 ⟨
    60*X^32 + 14*X^31 + 48*X^30 + 56*X^29 + 44*X^28 + 66*X^27 + 28*X^26 + 59*X^25 + 64*X^24 + 26*X^23 +
      18*X^22 + 54*X^21 + 15*X^20 + X^19 + 25*X^18 + 4*X^17 + 47*X^16 + 46*X^15 + 31*X^14 + 46*X^13 +
      37*X^12 + 44*X^11 + 14*X^10 + 5*X^9 + 6*X^8 + 7*X^7 + 17*X^6 + 10*X^5 + 12*X^4 + 13*X^3 +
      39*X^2 + 12,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s290 : XPow fSeventeenA2 29797741197977362427035961565877495383597423496504918680912
    (34*X^33 + 20*X^32 + 58*X^31 + 50*X^30 + 17*X^29 + 17*X^28 + 65*X^27 + 39*X^26 + 23*X^25 + 58*X^24 +
      24*X^23 + 39*X^22 + 20*X^21 + 30*X^20 + 31*X^19 + 41*X^18 + 18*X^17 + 32*X^16 + 64*X^15 +
      33*X^14 + 5*X^13 + 47*X^12 + 29*X^11 + 24*X^10 + 59*X^9 + 36*X^7 + 66*X^6 + 60*X^5 + 20*X^4 +
      42*X^3 + 39*X^2 + 6*X + 11) :=
  sq_step (by norm_num) pSeventeenA2s289 ⟨
    10*X^32 + 15*X^31 + 21*X^30 + 43*X^29 + 6*X^28 + 4*X^27 + 22*X^26 + 18*X^25 + 20*X^24 + 5*X^23 +
      5*X^22 + 46*X^21 + 62*X^20 + 15*X^19 + 64*X^18 + 63*X^17 + 44*X^16 + 12*X^15 + 27*X^14 +
      20*X^13 + 14*X^12 + 65*X^11 + 62*X^10 + 29*X^9 + 4*X^8 + 29*X^6 + 28*X^5 + 31*X^4 + 16*X^3 +
      48*X^2 + 14*X + 11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s291 : XPow fSeventeenA2 29797741197977362427035961565877495383597423496504918680913
    (42*X^33 + 4*X^32 + 3*X^31 + 15*X^30 + 5*X^29 + 43*X^28 + 5*X^27 + 59*X^26 + 6*X^25 + 17*X^24 +
      60*X^23 + 24*X^22 + 31*X^21 + 52*X^20 + 62*X^19 + 57*X^18 + 45*X^17 + 10*X^16 + 36*X^15 +
      51*X^14 + X^13 + 63*X^12 + 44*X^11 + 61*X^10 + 44*X^9 + 2*X^8 + 49*X^7 + 24*X^6 + 14*X^5 +
      62*X^4 + 32*X^3 + 25*X^2 + 5*X + 39) :=
  mul_step (by norm_num) pSeventeenA2s290 pSeventeenA21 ⟨
    34,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s292 : XPow fSeventeenA2 59595482395954724854071923131754990767194846993009837361826
    (39*X^33 + 64*X^32 + 47*X^31 + 59*X^30 + 59*X^29 + 18*X^28 + 33*X^27 + 30*X^26 + 41*X^25 + 62*X^24 +
      23*X^23 + 11*X^22 + 2*X^21 + 26*X^20 + 37*X^19 + 16*X^18 + 47*X^17 + 56*X^16 + X^15 + 5*X^14 +
      32*X^13 + 66*X^12 + 18*X^11 + 3*X^10 + 36*X^9 + 32*X^8 + 64*X^7 + 5*X^6 + 16*X^5 + 22*X^4 +
      44*X^3 + 31*X^2 + 8*X + 52) :=
  sq_step (by norm_num) pSeventeenA2s291 ⟨
    22*X^32 + 31*X^31 + 60*X^30 + 49*X^29 + 57*X^28 + 26*X^27 + 35*X^26 + 44*X^25 + 31*X^24 + 28*X^23 +
      29*X^22 + 57*X^21 + 57*X^20 + 55*X^19 + 35*X^18 + 63*X^17 + 24*X^16 + 43*X^15 + 37*X^14 +
      41*X^12 + 37*X^11 + 20*X^10 + 19*X^9 + 63*X^8 + 40*X^7 + 34*X^6 + 60*X^5 + 59*X^4 + 58*X^3 +
      51*X^2 + 30*X + 37,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s293 : XPow fSeventeenA2 59595482395954724854071923131754990767194846993009837361827
    (38*X^33 + 56*X^32 + 11*X^31 + 37*X^30 + 20*X^29 + 59*X^28 + 58*X^27 + 35*X^26 + 26*X^25 + 13*X^24 +
      41*X^23 + 46*X^22 + 37*X^21 + 46*X^19 + 7*X^18 + 65*X^17 + 10*X^16 + 38*X^15 + 2*X^14 +
      29*X^13 + 57*X^12 + 22*X^11 + 58*X^10 + 47*X^9 + 25*X^8 + 19*X^7 + 22*X^6 + 23*X^5 + 63*X^4 +
      21*X^3 + 16*X^2 + 53*X + 27) :=
  mul_step (by norm_num) pSeventeenA2s292 pSeventeenA21 ⟨
    39,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s294 : XPow fSeventeenA2 119190964791909449708143846263509981534389693986019674723654
    (32*X^33 + 19*X^32 + 44*X^31 + 63*X^30 + 27*X^29 + 17*X^28 + 28*X^27 + 54*X^26 + 50*X^25 + X^24 +
      28*X^23 + 18*X^22 + 24*X^21 + 35*X^20 + 23*X^19 + 34*X^18 + 12*X^17 + 64*X^16 + 51*X^15 +
      6*X^14 + 61*X^13 + 14*X^12 + 6*X^11 + 5*X^10 + 44*X^9 + 30*X^8 + 31*X^7 + 47*X^6 + 66*X^5 +
      58*X^4 + 47*X^3 + 9*X^2 + 57*X + 46) :=
  sq_step (by norm_num) pSeventeenA2s293 ⟨
    37*X^32 + 55*X^31 + 51*X^30 + 19*X^29 + 16*X^28 + 20*X^27 + 4*X^26 + 66*X^25 + 47*X^24 + 24*X^23 +
      62*X^22 + 3*X^21 + 66*X^20 + 38*X^19 + 51*X^18 + 58*X^17 + 36*X^16 + 21*X^15 + 12*X^14 +
      50*X^13 + 50*X^12 + 25*X^11 + 58*X^10 + 43*X^9 + 4*X^8 + 55*X^7 + 63*X^6 + 55*X^5 + 64*X^4 +
      5*X^3 + 46*X^2 + 25*X + 11,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s295 : XPow fSeventeenA2 119190964791909449708143846263509981534389693986019674723655
    (20*X^33 + 5*X^32 + 3*X^31 + 33*X^30 + 53*X^29 + 27*X^28 + 22*X^27 + 9*X^26 + 23*X^25 + 49*X^24 +
      22*X^23 + 12*X^22 + 32*X^21 + 27*X^20 + 38*X^19 + 29*X^18 + 25*X^17 + 12*X^16 + 64*X^15 +
      57*X^14 + 18*X^13 + 38*X^12 + 12*X^11 + 38*X^10 + 32*X^9 + 66*X^8 + 31*X^7 + 40*X^6 + 9*X^5 +
      54*X^4 + 30*X^3 + 64*X + 17) :=
  mul_step (by norm_num) pSeventeenA2s294 pSeventeenA21 ⟨
    32,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s296 : XPow fSeventeenA2 238381929583818899416287692527019963068779387972039349447310
    (55*X^33 + 11*X^32 + 45*X^31 + 8*X^30 + 55*X^29 + 9*X^28 + 30*X^27 + 52*X^26 + 41*X^25 + 13*X^24 +
      25*X^23 + 54*X^22 + 19*X^21 + 36*X^20 + 34*X^19 + 31*X^18 + 48*X^17 + 43*X^16 + 52*X^15 +
      33*X^14 + 16*X^13 + 31*X^12 + 35*X^11 + 41*X^10 + 61*X^9 + 30*X^8 + 3*X^7 + 4*X^6 + 60*X^5 +
      43*X^4 + 26*X^3 + 58*X^2 + 10*X + 25) :=
  sq_step (by norm_num) pSeventeenA2s295 ⟨
    65*X^32 + 45*X^31 + 63*X^30 + 53*X^29 + 63*X^28 + 38*X^27 + 43*X^26 + 42*X^25 + 39*X^24 + 23*X^23 +
      20*X^22 + 34*X^21 + 59*X^20 + 47*X^19 + 20*X^18 + 55*X^17 + 57*X^16 + 8*X^15 + 52*X^14 +
      54*X^13 + 24*X^12 + 38*X^11 + 55*X^10 + 24*X^9 + 39*X^8 + 10*X^7 + X^6 + 41*X^5 + 16*X^4 +
      66*X^3 + 9*X^2 + 51*X + 43,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s297 : XPow fSeventeenA2 476763859167637798832575385054039926137558775944078698894620
    (13*X^33 + 25*X^32 + 62*X^31 + 33*X^30 + 39*X^29 + 19*X^28 + 15*X^27 + 55*X^26 + 51*X^25 + 39*X^24 +
      61*X^23 + 29*X^22 + 16*X^21 + 63*X^20 + 5*X^19 + 13*X^18 + 3*X^17 + 47*X^16 + 38*X^15 +
      17*X^14 + 51*X^12 + 65*X^11 + 38*X^10 + 7*X^9 + 42*X^8 + 27*X^7 + 43*X^6 + 50*X^5 + 3*X^4 +
      26*X^3 + 38*X^2 + 61*X + 39) :=
  sq_step (by norm_num) pSeventeenA2s296 ⟨
    10*X^32 + 42*X^31 + 10*X^30 + 50*X^29 + 23*X^28 + 65*X^27 + 20*X^26 + 16*X^25 + 22*X^24 + 47*X^23 +
      24*X^22 + 16*X^21 + 40*X^20 + 25*X^19 + 4*X^18 + 62*X^17 + 5*X^16 + 56*X^15 + 2*X^14 + 52*X^13 +
      41*X^12 + 13*X^11 + 54*X^10 + 48*X^9 + 63*X^8 + 60*X^7 + 4*X^6 + 20*X^5 + 65*X^4 + 15*X^3 +
      35*X^2 + 62*X + 32,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s298 : XPow fSeventeenA2 953527718335275597665150770108079852275117551888157397789240
    (11*X^33 + 22*X^32 + 19*X^31 + 21*X^30 + 66*X^29 + 39*X^28 + 9*X^27 + 59*X^26 + 56*X^25 + 53*X^24 +
      31*X^23 + 52*X^22 + 46*X^21 + 27*X^20 + 63*X^19 + 7*X^18 + 2*X^17 + 57*X^16 + 45*X^15 +
      63*X^14 + 10*X^13 + X^12 + 52*X^11 + 59*X^10 + 10*X^9 + 64*X^8 + 45*X^7 + 55*X^6 + 22*X^5 +
      2*X^4 + 44*X^3 + 34*X^2 + 59*X + 45) :=
  sq_step (by norm_num) pSeventeenA2s297 ⟨
    35*X^32 + 46*X^31 + 12*X^30 + 47*X^29 + 2*X^28 + 66*X^27 + 29*X^26 + 9*X^25 + 45*X^24 + 43*X^23 +
      4*X^22 + 55*X^21 + 13*X^20 + 27*X^19 + 3*X^18 + 9*X^17 + 21*X^16 + 49*X^15 + 61*X^14 + 42*X^13 +
      32*X^12 + 66*X^11 + 57*X^10 + 65*X^9 + 40*X^8 + 50*X^7 + 10*X^6 + 53*X^5 + 24*X^4 + 60*X^3 +
      60*X^2 + 61*X + 12,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s299 : XPow fSeventeenA2 1907055436670551195330301540216159704550235103776314795578480
    (7*X^33 + 2*X^32 + 34*X^31 + 8*X^30 + 15*X^29 + 33*X^28 + 54*X^27 + 39*X^26 + 2*X^25 + 62*X^24 +
      25*X^23 + 21*X^22 + 24*X^21 + 15*X^20 + 66*X^19 + 19*X^18 + 65*X^17 + 36*X^16 + 27*X^15 +
      43*X^14 + 41*X^13 + 37*X^12 + 54*X^11 + 42*X^10 + 40*X^9 + 49*X^8 + 28*X^7 + 60*X^6 + 66*X^5 +
      27*X^4 + 12*X^3 + 11*X^2 + 53*X + 59) :=
  sq_step (by norm_num) pSeventeenA2s298 ⟨
    54*X^32 + 46*X^31 + 42*X^30 + 3*X^29 + 24*X^28 + 65*X^27 + 62*X^26 + 54*X^25 + 19*X^24 + 7*X^23 +
      2*X^22 + 32*X^21 + 49*X^20 + 3*X^19 + 60*X^18 + 6*X^17 + 9*X^16 + 33*X^15 + 36*X^14 + 51*X^13 +
      9*X^12 + 18*X^11 + 45*X^10 + 59*X^9 + 10*X^8 + 22*X^7 + 50*X^6 + 8*X^5 + 54*X^4 + 48*X^3 +
      32*X + 4,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s300 : XPow fSeventeenA2 3814110873341102390660603080432319409100470207552629591156960
    (60*X^33 + 17*X^32 + 64*X^31 + 6*X^30 + 28*X^29 + 26*X^28 + 23*X^27 + 41*X^26 + 16*X^25 + 61*X^24 +
      36*X^23 + 42*X^22 + 28*X^21 + 10*X^20 + 13*X^19 + 62*X^18 + 30*X^17 + 41*X^16 + 60*X^15 +
      39*X^14 + 38*X^13 + 33*X^12 + 29*X^11 + 37*X^10 + 64*X^9 + 20*X^8 + 19*X^7 + 33*X^6 + 19*X^5 +
      45*X^4 + 42*X^3 + 22*X^2 + 40*X + 56) :=
  sq_step (by norm_num) pSeventeenA2s299 ⟨
    49*X^32 + 40*X^31 + 30*X^30 + 12*X^29 + 23*X^28 + 43*X^27 + 31*X^26 + 51*X^25 + 45*X^24 + 65*X^23 +
      45*X^22 + 36*X^21 + 66*X^20 + 48*X^19 + 25*X^18 + 15*X^17 + 54*X^16 + 24*X^15 + 10*X^14 +
      64*X^13 + 37*X^12 + 18*X^11 + 62*X^10 + 52*X^9 + 53*X^8 + 5*X^7 + 14*X^6 + 32*X^5 + 9*X^4 +
      2*X^3 + 46*X^2 + 60*X + 48,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s301 : XPow fSeventeenA2 7628221746682204781321206160864638818200940415105259182313920
    (23*X^33 + 65*X^32 + 6*X^31 + 30*X^30 + 53*X^29 + 55*X^28 + 40*X^27 + 41*X^26 + X^25 + 54*X^24 +
      44*X^23 + 50*X^22 + 59*X^21 + 5*X^20 + 62*X^19 + 43*X^18 + 9*X^17 + 15*X^16 + 36*X^15 +
      42*X^14 + 23*X^13 + 41*X^12 + 53*X^11 + 12*X^10 + 27*X^9 + 20*X^8 + 39*X^7 + 49*X^6 + 55*X^5 +
      30*X^4 + 46*X^3 + 45*X^2 + 66*X + 5) :=
  sq_step (by norm_num) pSeventeenA2s300 ⟨
    49*X^32 + 42*X^31 + 36*X^30 + 28*X^29 + 56*X^28 + 21*X^27 + 19*X^26 + 65*X^25 + 25*X^24 + 25*X^23 +
      66*X^22 + 55*X^21 + 48*X^20 + 3*X^19 + 65*X^18 + 40*X^17 + 43*X^16 + 16*X^15 + 58*X^14 +
      15*X^13 + 55*X^12 + 12*X^11 + 26*X^10 + 19*X^9 + 47*X^8 + 34*X^7 + 37*X^6 + X^5 + 2*X^4 +
      4*X^3 + 45*X^2 + 23*X + 26,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s302 : XPow fSeventeenA2 15256443493364409562642412321729277636401880830210518364627840
    (12*X^33 + 18*X^32 + 41*X^31 + 23*X^30 + 10*X^29 + 54*X^28 + 24*X^27 + 19*X^26 + 47*X^25 + 11*X^24 +
      22*X^23 + 65*X^22 + 23*X^21 + 40*X^20 + 52*X^19 + 20*X^18 + 34*X^17 + 46*X^16 + 12*X^15 +
      63*X^14 + 13*X^13 + X^12 + 16*X^11 + 4*X^10 + 64*X^9 + 65*X^8 + 23*X^7 + 40*X^6 + 6*X^5 +
      56*X^4 + 9*X^3 + 3*X^2 + 29*X + 41) :=
  sq_step (by norm_num) pSeventeenA2s301 ⟨
    60*X^32 + 2*X^31 + 52*X^30 + 66*X^29 + 18*X^28 + 56*X^27 + 3*X^26 + 50*X^25 + 40*X^24 + 51*X^23 +
      25*X^22 + 13*X^21 + 38*X^20 + 3*X^19 + 44*X^18 + 32*X^17 + 48*X^16 + 26*X^15 + 43*X^14 +
      55*X^13 + 29*X^12 + 23*X^11 + 6*X^10 + 31*X^9 + 31*X^8 + 9*X^7 + 55*X^6 + 7*X^5 + 29*X^4 +
      30*X^3 + 5*X^2 + 45*X + 38,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s303 : XPow fSeventeenA2 15256443493364409562642412321729277636401880830210518364627841
    (10*X^33 + 18*X^32 + 34*X^31 + 29*X^30 + 34*X^29 + 32*X^28 + 7*X^27 + 40*X^26 + 36*X^25 + 55*X^24 +
      33*X^23 + 52*X^22 + 64*X^21 + 20*X^20 + 55*X^19 + 32*X^18 + 23*X^17 + 56*X^16 + X^15 + 45*X^14 +
      36*X^13 + 28*X^12 + 15*X^11 + 45*X^10 + 49*X^9 + 11*X^8 + 34*X^7 + 13*X^6 + 46*X^5 + 20*X^4 +
      36*X^3 + 16*X^2 + 31*X + 65) :=
  mul_step (by norm_num) pSeventeenA2s302 pSeventeenA21 ⟨
    12,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s304 : XPow fSeventeenA2 30512886986728819125284824643458555272803761660421036729255682
    (66) :=
  sq_step (by norm_num) pSeventeenA2s303 ⟨
    33*X^32 + 3*X^31 + 51*X^30 + 19*X^29 + 5*X^28 + 24*X^27 + 40*X^26 + 21*X^25 + 51*X^24 + 64*X^23 +
      X^22 + 24*X^21 + 56*X^20 + 57*X^19 + 49*X^18 + 46*X^17 + 51*X^16 + 55*X^15 + 30*X^14 + 4*X^13 +
      60*X^12 + 36*X^11 + 9*X^10 + 35*X^9 + 30*X^8 + 15*X^7 + 10*X^6 + 11*X^5 + 42*X^4 + 26*X^3 +
      9*X^2 + 44*X + 30,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s305 : XPow fSeventeenA2 61025773973457638250569649286917110545607523320842073458511364
    (1) :=
  sq_step (by norm_num) pSeventeenA2s304 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s306 : XPow fSeventeenA2 122051547946915276501139298573834221091215046641684146917022728
    (1) :=
  sq_step (by norm_num) pSeventeenA2s305 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2s307 : XPow fSeventeenA2 122051547946915276501139298573834221091215046641684146917022729
    (X) :=
  mul_step (by norm_num) pSeventeenA2s306 pSeventeenA21 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! Factor 2 again, at the smaller exponent `67 ^ 2`, for the coprimality below. -/

theorem pSeventeenA2cs0 : XPow fSeventeenA2 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenA21 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs1 : XPow fSeventeenA2 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenA2cs0 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs2 : XPow fSeventeenA2 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenA2cs1 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs3 : XPow fSeventeenA2 16
    (X^16) :=
  sq_step (by norm_num) pSeventeenA2cs2 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs4 : XPow fSeventeenA2 17
    (X^17) :=
  mul_step (by norm_num) pSeventeenA2cs3 pSeventeenA21 ⟨
    0,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs5 : XPow fSeventeenA2 34
    (44*X^33 + 26*X^32 + 40*X^31 + 63*X^30 + 43*X^29 + 23*X^28 + 66*X^27 + 5*X^26 + 30*X^25 + 53*X^24 +
      42*X^23 + 8*X^22 + 2*X^21 + 42*X^20 + 42*X^19 + 11*X^18 + 26*X^17 + 26*X^16 + 6*X^15 + 25*X^14 +
      42*X^13 + X^12 + 40*X^11 + 4*X^10 + 21*X^9 + 66*X^8 + 33*X^7 + 62*X^6 + 55*X^5 + 40*X^4 +
      53*X^3 + 38*X^2 + 55*X + 11) :=
  sq_step (by norm_num) pSeventeenA2cs4 ⟨
    1,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs6 : XPow fSeventeenA2 35
    (19*X^33 + 45*X^32 + 14*X^31 + X^30 + 39*X^29 + 6*X^28 + 28*X^27 + 49*X^26 + 33*X^25 + 29*X^24 +
      47*X^23 + 19*X^22 + 63*X^21 + 14*X^20 + 50*X^19 + 41*X^18 + 31*X^17 + 11*X^16 + 21*X^15 +
      3*X^14 + 40*X^13 + 17*X^12 + 22*X^11 + 63*X^10 + 52*X^9 + 56*X^8 + 40*X^7 + 36*X^6 + 48*X^5 +
      4*X^4 + 25*X^3 + 52*X^2 + 19*X + 15) :=
  mul_step (by norm_num) pSeventeenA2cs5 pSeventeenA21 ⟨
    44,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs7 : XPow fSeventeenA2 70
    (18*X^33 + 16*X^32 + 59*X^31 + 31*X^30 + 33*X^29 + 44*X^28 + 11*X^27 + 16*X^26 + 42*X^25 + 48*X^24 +
      35*X^23 + 34*X^22 + 16*X^21 + 49*X^20 + 11*X^19 + 48*X^18 + 31*X^17 + 32*X^16 + 16*X^15 +
      55*X^14 + 54*X^13 + 25*X^12 + 3*X^11 + 14*X^10 + 22*X^9 + 17*X^8 + 32*X^7 + 4*X^6 + 31*X^5 +
      66*X^4 + 14*X^3 + 46*X^2 + 19*X + 21) :=
  sq_step (by norm_num) pSeventeenA2cs6 ⟨
    26*X^32 + 40*X^31 + 35*X^30 + 27*X^29 + 2*X^28 + 13*X^27 + 13*X^26 + 3*X^25 + 31*X^24 + 16*X^23 +
      18*X^22 + 56*X^21 + 28*X^20 + 60*X^19 + 57*X^18 + 6*X^17 + 12*X^16 + 40*X^15 + 44*X^14 +
      47*X^13 + 55*X^12 + 24*X^11 + X^10 + 52*X^9 + 59*X^8 + 45*X^7 + 32*X^6 + 32*X^5 + 39*X^4 +
      32*X^3 + 11*X^2 + 18,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs8 : XPow fSeventeenA2 140
    (27*X^33 + 48*X^32 + 46*X^31 + 7*X^30 + 24*X^29 + 62*X^28 + 15*X^27 + 22*X^26 + 56*X^25 + 7*X^24 +
      22*X^23 + 10*X^22 + 3*X^21 + 22*X^20 + 36*X^19 + 60*X^18 + 17*X^17 + 5*X^16 + 35*X^15 +
      10*X^14 + 57*X^13 + 26*X^12 + 52*X^11 + 26*X^10 + 10*X^9 + 31*X^8 + 9*X^7 + 66*X^6 + 37*X^5 +
      15*X^4 + 36*X^3 + 58*X^2 + 24*X + 7) :=
  sq_step (by norm_num) pSeventeenA2cs7 ⟨
    56*X^32 + 25*X^31 + 45*X^30 + 35*X^29 + 35*X^28 + 59*X^27 + 13*X^26 + 50*X^25 + 19*X^24 + 28*X^23 +
      19*X^22 + X^21 + 41*X^20 + 48*X^19 + 65*X^18 + 10*X^17 + 39*X^16 + 16*X^15 + 53*X^14 + 41*X^13 +
      25*X^12 + 60*X^11 + 10*X^10 + 8*X^9 + 26*X^8 + 14*X^7 + 26*X^6 + 24*X^5 + 56*X^4 + 58*X^3 +
      40*X^2 + 66*X + 58,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs9 : XPow fSeventeenA2 280
    (28*X^33 + 24*X^32 + 35*X^31 + 66*X^30 + 17*X^29 + 41*X^28 + 50*X^27 + 3*X^26 + 29*X^25 + 23*X^24 +
      34*X^23 + 53*X^22 + 44*X^21 + 21*X^20 + 11*X^19 + 36*X^18 + 65*X^17 + 62*X^16 + 57*X^15 +
      53*X^14 + 62*X^13 + 21*X^12 + 2*X^11 + 54*X^10 + 7*X^9 + 36*X^8 + 29*X^7 + 62*X^6 + 42*X^5 +
      60*X^4 + 44*X^3 + 3*X^2 + 54*X + 7) :=
  sq_step (by norm_num) pSeventeenA2cs8 ⟨
    59*X^32 + 29*X^31 + 27*X^30 + 51*X^29 + 48*X^28 + 36*X^27 + 39*X^26 + 65*X^25 + 15*X^24 + 23*X^23 +
      18*X^22 + 49*X^21 + 12*X^20 + 11*X^19 + 54*X^18 + 47*X^17 + 17*X^16 + 4*X^15 + 21*X^14 +
      40*X^13 + 55*X^12 + 37*X^11 + 62*X^10 + 34*X^9 + 30*X^8 + 31*X^7 + 61*X^6 + 61*X^5 + 5*X^4 +
      63*X^3 + 23*X^2 + 30*X + 51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs10 : XPow fSeventeenA2 560
    (63*X^33 + 2*X^32 + 57*X^31 + 34*X^30 + 65*X^29 + 4*X^28 + 16*X^27 + 47*X^26 + 20*X^25 + 60*X^24 +
      10*X^23 + 14*X^22 + 58*X^21 + 29*X^20 + X^19 + 13*X^18 + 39*X^17 + 26*X^16 + 10*X^15 + 23*X^14 +
      54*X^13 + 66*X^12 + 13*X^11 + 60*X^10 + 52*X^9 + 32*X^8 + 23*X^7 + 50*X^6 + 31*X^5 + 55*X^4 +
      5*X^3 + 3*X^2 + 15*X + 56) :=
  sq_step (by norm_num) pSeventeenA2cs9 ⟨
    47*X^32 + 62*X^31 + 54*X^30 + 55*X^29 + 4*X^28 + 5*X^27 + 21*X^26 + 49*X^25 + 14*X^24 + 14*X^23 +
      62*X^22 + 3*X^21 + 36*X^20 + 59*X^19 + 35*X^18 + 43*X^17 + 48*X^16 + 49*X^15 + 66*X^14 +
      3*X^13 + 40*X^12 + 26*X^11 + 33*X^10 + 65*X^9 + 50*X^8 + 28*X^7 + 2*X^6 + 20*X^5 + 55*X^4 +
      33*X^3 + 16*X^2 + 33*X + 25,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs11 : XPow fSeventeenA2 561
    (27*X^33 + 20*X^32 + 8*X^31 + 14*X^30 + 33*X^29 + 58*X^28 + 51*X^27 + 7*X^25 + 66*X^24 + 47*X^23 +
      26*X^22 + 21*X^21 + 34*X^20 + 46*X^19 + 62*X^18 + 56*X^17 + 40*X^16 + 66*X^15 + 21*X^14 +
      32*X^13 + 9*X^12 + 34*X^11 + 36*X^10 + 15*X^9 + 27*X^8 + 52*X^7 + 51*X^6 + 36*X^5 + 46*X^4 +
      59*X^3 + 64*X^2 + 37*X + 23) :=
  mul_step (by norm_num) pSeventeenA2cs10 pSeventeenA21 ⟨
    63,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs12 : XPow fSeventeenA2 1122
    (15*X^33 + 7*X^32 + 13*X^31 + 27*X^30 + 15*X^29 + 27*X^28 + 16*X^27 + 37*X^26 + 43*X^25 + 20*X^24 +
      36*X^23 + 47*X^22 + 37*X^21 + 32*X^20 + 59*X^19 + 59*X^18 + 18*X^17 + 40*X^16 + 52*X^15 +
      9*X^14 + 6*X^13 + 38*X^12 + 28*X^11 + 41*X^10 + 14*X^9 + 28*X^8 + 30*X^7 + 48*X^6 + 35*X^5 +
      44*X^4 + 63*X^3 + 64*X^2 + 65*X + 7) :=
  sq_step (by norm_num) pSeventeenA2cs11 ⟨
    59*X^32 + 58*X^31 + 27*X^30 + 35*X^29 + 32*X^28 + 61*X^27 + 52*X^26 + 19*X^25 + 50*X^24 + 22*X^23 +
      51*X^22 + 10*X^21 + 29*X^20 + 3*X^18 + 24*X^17 + 38*X^16 + 30*X^15 + 49*X^14 + 55*X^13 +
      54*X^12 + 4*X^11 + 54*X^10 + 33*X^9 + 52*X^8 + 60*X^7 + 7*X^6 + 17*X^5 + 51*X^4 + 38*X^3 +
      22*X^2 + 58*X + 50,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs13 : XPow fSeventeenA2 2244
    (29*X^33 + 22*X^32 + 47*X^31 + 21*X^30 + 8*X^29 + 62*X^28 + 10*X^27 + 14*X^26 + 33*X^25 + 50*X^24 +
      35*X^23 + 18*X^22 + 55*X^21 + 55*X^20 + 50*X^19 + 51*X^18 + 29*X^17 + 66*X^16 + 50*X^15 +
      48*X^14 + 29*X^13 + 17*X^12 + 20*X^11 + 60*X^10 + 21*X^9 + 14*X^8 + 40*X^7 + 64*X^6 + 40*X^5 +
      53*X^4 + 50*X^3 + 14*X^2 + 60*X + 7) :=
  sq_step (by norm_num) pSeventeenA2cs12 ⟨
    24*X^32 + 60*X^31 + 18*X^30 + 16*X^29 + 51*X^28 + 65*X^27 + 14*X^26 + 12*X^25 + 49*X^24 + 52*X^23 +
      35*X^22 + 30*X^21 + 60*X^19 + 20*X^18 + 64*X^17 + 51*X^16 + 31*X^15 + 48*X^14 + 57*X^13 +
      62*X^12 + 66*X^11 + 33*X^10 + 24*X^9 + 5*X^8 + 9*X^7 + 44*X^6 + 12*X^5 + 38*X^4 + 31*X^3 +
      22*X^2 + 21*X + 51,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs14 : XPow fSeventeenA2 4488
    (21*X^33 + 62*X^32 + 6*X^31 + 56*X^30 + 52*X^29 + 3*X^28 + 50*X^27 + 31*X^26 + 63*X^25 + 26*X^24 +
      66*X^23 + 19*X^22 + 7*X^21 + 9*X^20 + 22*X^19 + 14*X^18 + 19*X^17 + 29*X^16 + 50*X^15 +
      33*X^14 + 21*X^13 + 56*X^12 + 55*X^11 + 6*X^10 + 39*X^9 + 16*X^8 + 27*X^7 + 8*X^6 + 4*X^5 +
      15*X^4 + 60*X^3 + 59*X^2 + 11*X + 31) :=
  sq_step (by norm_num) pSeventeenA2cs13 ⟨
    37*X^32 + 23*X^31 + 25*X^30 + 32*X^29 + 62*X^28 + 55*X^27 + 29*X^26 + 38*X^25 + 33*X^24 + 54*X^23 +
      49*X^22 + 24*X^21 + 20*X^20 + 6*X^19 + 54*X^18 + 39*X^17 + 4*X^16 + 38*X^15 + 57*X^14 +
      66*X^13 + 56*X^12 + 29*X^11 + 53*X^10 + 40*X^9 + 8*X^8 + 63*X^7 + 25*X^6 + 63*X^5 + 38*X^4 +
      52*X^3 + 19*X^2 + 12*X + 41,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA2cs15 : XPow fSeventeenA2 4489
    (48*X^33 + 16*X^32 + 25*X^31 + 35*X^30 + 35*X^29 + 64*X^28 + 10*X^27 + 34*X^26 + 53*X^25 + 40*X^24 +
      30*X^23 + 41*X^22 + 51*X^21 + 33*X^20 + 25*X^19 + 49*X^18 + 39*X^17 + 60*X^16 + 25*X^15 +
      10*X^14 + 9*X^12 + 42*X^11 + 56*X^10 + 55*X^9 + 6*X^8 + 31*X^7 + 33*X^6 + 31*X^5 + 29*X^4 +
      33*X^3 + 5*X^2 + 47*X + 30) :=
  mul_step (by norm_num) pSeventeenA2cs14 pSeventeenA21 ⟨
    21,
    by simp only [fSeventeenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

end Fermat.MazurNonCMCertificate

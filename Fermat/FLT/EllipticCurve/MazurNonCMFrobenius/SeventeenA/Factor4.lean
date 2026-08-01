/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius

/-!
# Row `p = 17`, `j = −882216989/131072`: factor 4 of `H`, and its two square-and-multiply chains

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

/-- Irreducible factor 4 of `H` on this row, of degree 34.  Its irreducibility is
not used anywhere — only that the 4 factors are pairwise coprime. -/
noncomputable def fSeventeenA4 : (ZMod 67)[X] :=
  X^34 + 48*X^33 + 4*X^32 + 34*X^31 + 35*X^30 + 34*X^29 + 45*X^28 + 52*X^27 + 61*X^26 + 58*X^25 +
    9*X^24 + 49*X^23 + 56*X^22 + 33*X^21 + 51*X^20 + 13*X^19 + 35*X^18 + 48*X^17 + 26*X^16 + 13*X^15 +
    22*X^14 + 65*X^13 + 29*X^12 + 42*X^11 + 30*X^10 + 23*X^9 + X^8 + 52*X^7 + 37*X^6 + 51*X^5 +
    10*X^4 + 61*X^3 + 10*X^2 + 51

/-! ### Factor 4: `X ^ (67 ^ 34)` mod `f` by square-and-multiply -/

theorem pSeventeenA41 : XPow fSeventeenA4 1 X := xpow_one _

theorem pSeventeenA4s0 : XPow fSeventeenA4 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenA41 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s1 : XPow fSeventeenA4 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenA4s0 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s2 : XPow fSeventeenA4 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenA4s1 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s3 : XPow fSeventeenA4 9
    (X^9) :=
  mul_step (by norm_num) pSeventeenA4s2 pSeventeenA41 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s4 : XPow fSeventeenA4 18
    (X^18) :=
  sq_step (by norm_num) pSeventeenA4s3 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s5 : XPow fSeventeenA4 36
    (40*X^33 + 35*X^32 + 27*X^31 + 13*X^30 + 20*X^29 + 38*X^28 + 51*X^27 + 26*X^26 + 45*X^25 + 21*X^24 +
      36*X^23 + 33*X^22 + 34*X^21 + 3*X^20 + 6*X^19 + 34*X^18 + 45*X^17 + 30*X^16 + 35*X^15 +
      61*X^14 + 54*X^13 + 8*X^12 + 24*X^11 + 41*X^10 + 26*X^9 + 25*X^8 + 45*X^7 + 16*X^6 + 34*X^5 +
      18*X^4 + 9*X^3 + 64*X^2 + 36*X + 17) :=
  sq_step (by norm_num) pSeventeenA4s4 ⟨
    X^2 + 19*X + 22,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s6 : XPow fSeventeenA4 37
    (58*X^33 + X^32 + 60*X^31 + 27*X^30 + 18*X^29 + 60*X^28 + 23*X^27 + 17*X^26 + 46*X^25 + 11*X^24 +
      16*X^23 + 5*X^22 + 23*X^21 + 43*X^20 + 50*X^19 + 52*X^18 + 53*X^17 + 10*X^15 + 45*X^14 +
      21*X^13 + 3*X^12 + 36*X^11 + 32*X^10 + 43*X^9 + 5*X^8 + 13*X^7 + 28*X^6 + 55*X^5 + 11*X^4 +
      36*X^3 + 38*X^2 + 17*X + 37) :=
  mul_step (by norm_num) pSeventeenA4s5 pSeventeenA41 ⟨
    40,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s7 : XPow fSeventeenA4 74
    (15*X^33 + 64*X^32 + 64*X^31 + 62*X^30 + 64*X^29 + 57*X^28 + 37*X^27 + 52*X^26 + 22*X^25 + 39*X^24 +
      36*X^23 + 37*X^22 + 58*X^21 + 54*X^20 + 12*X^19 + 16*X^18 + 17*X^17 + 47*X^16 + 62*X^15 + X^14 +
      37*X^13 + 13*X^12 + 58*X^11 + 61*X^10 + 37*X^9 + 25*X^8 + 20*X^7 + 11*X^6 + 28*X^5 + 30*X^4 +
      65*X^3 + 16*X^2 + 45*X + 22) :=
  sq_step (by norm_num) pSeventeenA4s6 ⟨
    14*X^32 + 47*X^31 + 26*X^30 + 66*X^28 + 43*X^27 + 10*X^26 + 16*X^25 + 33*X^24 + 62*X^23 + 6*X^22 +
      60*X^21 + 43*X^20 + 27*X^19 + 45*X^17 + 61*X^16 + 10*X^15 + 41*X^14 + 6*X^13 + 43*X^11 +
      47*X^10 + 14*X^9 + 12*X^8 + 5*X^7 + 64*X^6 + 33*X^5 + 37*X^4 + 9*X^3 + 21*X^2 + 54*X + 54,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s8 : XPow fSeventeenA4 75
    (14*X^33 + 4*X^32 + 21*X^31 + 8*X^30 + 16*X^29 + 32*X^28 + 9*X^27 + 45*X^26 + 40*X^25 + 35*X^24 +
      39*X^23 + 22*X^22 + 28*X^21 + 51*X^20 + 22*X^19 + 28*X^18 + 64*X^17 + 7*X^16 + 7*X^15 +
      42*X^14 + 43*X^13 + 25*X^12 + 34*X^11 + 56*X^10 + 15*X^9 + 5*X^8 + 35*X^7 + 9*X^6 + 2*X^5 +
      49*X^4 + 39*X^3 + 29*X^2 + 22*X + 39) :=
  mul_step (by norm_num) pSeventeenA4s7 pSeventeenA41 ⟨
    15,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s9 : XPow fSeventeenA4 150
    (64*X^33 + 65*X^32 + 59*X^31 + 46*X^30 + 12*X^29 + 20*X^28 + 40*X^27 + 11*X^26 + 31*X^25 + 41*X^24 +
      33*X^23 + 47*X^22 + 45*X^21 + 40*X^20 + 5*X^19 + 58*X^18 + 64*X^17 + 53*X^16 + 23*X^15 +
      42*X^14 + 7*X^13 + 3*X^12 + 20*X^11 + 65*X^10 + 25*X^9 + 37*X^8 + 12*X^7 + 38*X^6 + 39*X^5 +
      47*X^4 + 36*X^3 + 47*X^2 + 21*X + 66) :=
  sq_step (by norm_num) pSeventeenA4s8 ⟨
    62*X^32 + 17*X^31 + 9*X^30 + 62*X^29 + 17*X^28 + 34*X^27 + 51*X^26 + 5*X^25 + 19*X^24 + 6*X^23 +
      16*X^22 + 39*X^21 + 52*X^20 + 2*X^19 + 11*X^18 + 20*X^17 + 56*X^16 + 48*X^15 + 42*X^14 +
      45*X^13 + 40*X^12 + 30*X^11 + 21*X^10 + 54*X^9 + 7*X^8 + 28*X^7 + 66*X^6 + 19*X^5 + 38*X^4 +
      7*X^3 + 43*X^2 + 49*X + 64,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s10 : XPow fSeventeenA4 151
    (8*X^33 + 4*X^32 + 14*X^31 + 50*X^30 + 55*X^29 + 41*X^28 + 33*X^27 + 13*X^26 + 14*X^25 + 60*X^24 +
      60*X^23 + 12*X^22 + 5*X^21 + 24*X^20 + 30*X^19 + 35*X^18 + 63*X^17 + 34*X^16 + 14*X^15 +
      6*X^14 + 64*X^13 + 40*X^12 + 57*X^11 + 48*X^10 + 39*X^9 + 15*X^8 + 60*X^7 + 16*X^6 + 66*X^5 +
      66*X^4 + 29*X^3 + 51*X^2 + 66*X + 19) :=
  mul_step (by norm_num) pSeventeenA4s9 pSeventeenA41 ⟨
    64,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s11 : XPow fSeventeenA4 302
    (44*X^33 + 58*X^32 + 32*X^31 + 43*X^30 + 47*X^29 + 46*X^28 + 13*X^27 + 64*X^26 + 16*X^25 + 59*X^24 +
      33*X^23 + 8*X^22 + 12*X^21 + 43*X^20 + 13*X^19 + 59*X^18 + 5*X^17 + 37*X^16 + 13*X^15 +
      38*X^14 + 28*X^13 + X^12 + 51*X^11 + 16*X^10 + 38*X^9 + 10*X^8 + 17*X^7 + 57*X^6 + 14*X^5 +
      66*X^4 + 12*X^3 + 21*X^2 + 61*X + 45) :=
  sq_step (by norm_num) pSeventeenA4s10 ⟨
    64*X^32 + 7*X^31 + 50*X^30 + 60*X^29 + 5*X^28 + 39*X^27 + 49*X^26 + 14*X^25 + 63*X^24 + 25*X^23 +
      50*X^22 + 36*X^21 + 62*X^20 + 7*X^19 + 29*X^18 + 47*X^16 + 20*X^15 + 8*X^14 + 66*X^13 +
      18*X^12 + 37*X^11 + 4*X^10 + 45*X^9 + 21*X^8 + 14*X^7 + 30*X^6 + 31*X^5 + 18*X^4 + 16*X^3 +
      29*X^2 + 2*X + 64,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s12 : XPow fSeventeenA4 303
    (23*X^33 + 57*X^32 + 21*X^31 + 48*X^30 + 24*X^29 + 43*X^28 + 54*X^27 + 12*X^26 + 53*X^25 + 39*X^24 +
      63*X^23 + 27*X^22 + 65*X^21 + 47*X^20 + 23*X^19 + 6*X^18 + 2*X^17 + 8*X^16 + 2*X^15 + 65*X^14 +
      22*X^13 + 48*X^12 + 44*X^11 + 58*X^10 + 3*X^9 + 40*X^8 + 47*X^7 + 61*X^6 + 33*X^5 + 41*X^4 +
      17*X^3 + 23*X^2 + 45*X + 34) :=
  mul_step (by norm_num) pSeventeenA4s11 pSeventeenA41 ⟨
    44,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s13 : XPow fSeventeenA4 606
    (62*X^33 + 42*X^32 + 8*X^31 + 37*X^30 + 66*X^29 + 6*X^28 + 13*X^27 + 66*X^26 + 42*X^25 + 63*X^24 +
      60*X^23 + 5*X^22 + 15*X^21 + 39*X^20 + 34*X^19 + 49*X^18 + 30*X^17 + 16*X^16 + 38*X^15 +
      45*X^14 + 25*X^13 + 32*X^12 + 32*X^11 + 66*X^10 + 41*X^9 + 64*X^8 + 64*X^7 + 16*X^6 + 8*X^5 +
      56*X^4 + 59*X^3 + 64*X^2 + 34*X + 31) :=
  sq_step (by norm_num) pSeventeenA4s12 ⟨
    60*X^32 + 10*X^31 + 11*X^30 + 51*X^29 + 8*X^28 + 28*X^27 + 9*X^26 + 52*X^25 + 2*X^24 + 2*X^23 +
      52*X^22 + 48*X^21 + 50*X^20 + 7*X^19 + 9*X^18 + 18*X^17 + 6*X^16 + 21*X^15 + 65*X^14 + 16*X^13 +
      34*X^12 + 49*X^11 + 4*X^10 + 15*X^9 + 3*X^8 + 10*X^7 + 51*X^6 + 7*X^5 + 2*X^4 + 29*X^3 +
      43*X^2 + 37*X + 26,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s14 : XPow fSeventeenA4 607
    (14*X^33 + 28*X^32 + 6*X^31 + 40*X^30 + 42*X^29 + 37*X^28 + 58*X^27 + 12*X^26 + 18*X^25 + 38*X^24 +
      49*X^23 + 27*X^22 + 3*X^21 + 21*X^20 + 47*X^19 + 4*X^18 + 55*X^17 + 34*X^16 + 43*X^15 + X^14 +
      22*X^13 + 43*X^12 + 8*X^11 + 57*X^10 + 45*X^9 + 2*X^8 + 8*X^7 + 59*X^6 + 43*X^5 + 42*X^4 +
      34*X^3 + 17*X^2 + 31*X + 54) :=
  mul_step (by norm_num) pSeventeenA4s13 pSeventeenA41 ⟨
    62,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s15 : XPow fSeventeenA4 1214
    (37*X^33 + 57*X^32 + 45*X^31 + 21*X^30 + 17*X^29 + 17*X^28 + 17*X^27 + 39*X^26 + 48*X^25 + 21*X^24 +
      32*X^23 + 37*X^22 + 8*X^21 + 59*X^20 + 26*X^19 + 51*X^18 + 65*X^17 + 8*X^16 + 64*X^15 +
      35*X^14 + 19*X^13 + 6*X^12 + 15*X^11 + 25*X^10 + 27*X^9 + 51*X^8 + 53*X^7 + 13*X^6 + 35*X^5 +
      10*X^4 + 22*X^3 + 14*X^2 + 49*X + 58) :=
  sq_step (by norm_num) pSeventeenA4s14 ⟨
    62*X^32 + 19*X^31 + 60*X^30 + 10*X^29 + 50*X^28 + 32*X^27 + 64*X^26 + 39*X^25 + 51*X^24 + 2*X^23 +
      17*X^22 + 25*X^21 + 57*X^20 + 8*X^19 + 50*X^18 + 33*X^17 + 61*X^16 + 17*X^15 + 40*X^14 +
      59*X^13 + 22*X^12 + 3*X^11 + 49*X^10 + 24*X^9 + 64*X^8 + X^7 + 30*X^6 + 44*X^5 + 16*X^4 +
      10*X^3 + 40*X^2 + 66*X + 14,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s16 : XPow fSeventeenA4 1215
    (23*X^33 + 31*X^32 + 36*X^31 + 62*X^30 + 32*X^29 + 27*X^28 + 58*X^27 + 2*X^26 + 19*X^25 + 34*X^24 +
      33*X^23 + 13*X^22 + 44*X^21 + 15*X^20 + 39*X^19 + 43*X^18 + 41*X^17 + 40*X^16 + 23*X^15 +
      9*X^14 + 13*X^13 + 14*X^12 + 12*X^11 + 56*X^10 + 4*X^9 + 16*X^8 + 32*X^7 + 6*X^6 + 66*X^5 +
      54*X^4 + 35*X^3 + 14*X^2 + 58*X + 56) :=
  mul_step (by norm_num) pSeventeenA4s15 pSeventeenA41 ⟨
    37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s17 : XPow fSeventeenA4 2430
    (39*X^33 + 34*X^32 + 17*X^31 + 9*X^30 + 19*X^29 + 33*X^28 + 57*X^27 + 40*X^26 + 60*X^25 + 20*X^24 +
      56*X^23 + 48*X^22 + 9*X^21 + 64*X^20 + 43*X^19 + X^18 + 38*X^17 + 15*X^16 + 51*X^15 + 59*X^14 +
      34*X^13 + 19*X^12 + 5*X^11 + 43*X^10 + 60*X^9 + 29*X^8 + 61*X^7 + 38*X^6 + 45*X^5 + 64*X^4 +
      37*X^3 + 13*X^2 + 10*X + 12) :=
  sq_step (by norm_num) pSeventeenA4s16 ⟨
    60*X^32 + 20*X^31 + 10*X^30 + 5*X^29 + X^28 + 53*X^27 + 22*X^26 + 11*X^25 + 31*X^24 + 48*X^23 +
      19*X^22 + 37*X^21 + 37*X^20 + 21*X^19 + 42*X^18 + 61*X^17 + 6*X^16 + 45*X^15 + 59*X^14 +
      20*X^13 + 4*X^12 + 44*X^11 + 45*X^10 + 44*X^9 + 64*X^8 + 63*X^7 + 45*X^6 + 4*X^5 + 19*X^4 +
      19*X^3 + 50*X^2 + 5*X + 56,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s18 : XPow fSeventeenA4 4860
    (30*X^33 + 5*X^32 + 26*X^31 + 38*X^30 + 51*X^29 + 36*X^28 + 58*X^27 + 50*X^26 + 35*X^25 + 52*X^24 +
      21*X^23 + 39*X^22 + 63*X^21 + 44*X^20 + 18*X^19 + 37*X^18 + 17*X^17 + 47*X^16 + 31*X^15 +
      53*X^14 + 5*X^13 + 41*X^12 + 21*X^11 + 57*X^10 + 57*X^9 + 19*X^8 + 31*X^7 + 8*X^6 + 30*X^5 +
      25*X^4 + 64*X^3 + 38*X^2 + 33*X + 9) :=
  sq_step (by norm_num) pSeventeenA4s17 ⟨
    47*X^32 + 61*X^31 + 36*X^30 + 30*X^29 + 28*X^28 + 29*X^27 + 47*X^26 + 18*X^25 + 3*X^24 + 51*X^23 +
      11*X^22 + 58*X^21 + 57*X^20 + 54*X^19 + 18*X^18 + 30*X^17 + 40*X^16 + 13*X^15 + 18*X^14 +
      42*X^13 + 12*X^12 + 21*X^11 + 36*X^10 + 22*X^9 + 5*X^8 + 18*X^7 + 22*X^6 + 31*X^5 + 15*X^4 +
      54*X^3 + 64*X^2 + 8*X + 46,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s19 : XPow fSeventeenA4 9720
    (56*X^33 + 54*X^32 + 15*X^31 + 35*X^30 + 52*X^29 + 45*X^28 + 23*X^27 + 57*X^26 + 65*X^25 + 35*X^24 +
      14*X^23 + 58*X^21 + 29*X^20 + 21*X^19 + 16*X^18 + 58*X^17 + 30*X^16 + 39*X^15 + 2*X^14 +
      11*X^13 + 34*X^12 + 47*X^11 + 52*X^10 + 37*X^9 + 66*X^8 + 65*X^7 + 62*X^6 + 31*X^5 + 26*X^4 +
      46*X^3 + 64*X^2 + 54*X + 38) :=
  sq_step (by norm_num) pSeventeenA4s18 ⟨
    29*X^32 + 47*X^31 + 17*X^30 + 14*X^29 + 26*X^28 + 66*X^27 + 20*X^26 + 50*X^25 + 66*X^24 + 41*X^23 +
      5*X^22 + 19*X^21 + 56*X^20 + 64*X^19 + 46*X^18 + 2*X^17 + 54*X^16 + 63*X^15 + 64*X^14 +
      36*X^13 + 3*X^12 + 34*X^11 + 18*X^10 + 48*X^9 + 44*X^8 + X^7 + 59*X^6 + 44*X^5 + 43*X^4 +
      10*X^3 + 3*X^2 + 50*X + 35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s20 : XPow fSeventeenA4 9721
    (46*X^33 + 59*X^32 + 7*X^31 + 35*X^30 + 17*X^29 + 49*X^28 + 26*X^27 + 66*X^26 + 3*X^25 + 46*X^24 +
      3*X^23 + 4*X^22 + 57*X^21 + 46*X^20 + 25*X^19 + 41*X^18 + 22*X^17 + 57*X^16 + 11*X^15 +
      52*X^14 + 12*X^13 + 31*X^12 + 45*X^11 + 32*X^10 + 51*X^9 + 9*X^8 + 31*X^7 + 36*X^6 + 51*X^5 +
      22*X^4 + 65*X^3 + 30*X^2 + 38*X + 25) :=
  mul_step (by norm_num) pSeventeenA4s19 pSeventeenA41 ⟨
    56,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s21 : XPow fSeventeenA4 19442
    (12*X^33 + 2*X^32 + 21*X^31 + 41*X^30 + 63*X^29 + 63*X^28 + 47*X^27 + 46*X^26 + 13*X^25 + 25*X^24 +
      10*X^23 + 24*X^22 + 65*X^21 + 5*X^19 + X^18 + 40*X^17 + 65*X^16 + X^15 + 40*X^14 + 19*X^13 +
      7*X^12 + 22*X^11 + 22*X^10 + 13*X^9 + 18*X^8 + 66*X^7 + 60*X^6 + 34*X^5 + 53*X^4 + 33*X^3 +
      46*X^2 + 18*X + 57) :=
  sq_step (by norm_num) pSeventeenA4s20 ⟨
    39*X^32 + 5*X^31 + 44*X^30 + 52*X^29 + 62*X^28 + 19*X^27 + 28*X^26 + 43*X^25 + 31*X^24 + 34*X^23 +
      55*X^22 + 47*X^21 + 50*X^20 + 21*X^19 + 20*X^18 + 28*X^17 + 66*X^16 + 48*X^15 + 20*X^14 +
      6*X^13 + 33*X^12 + 41*X^11 + 55*X^10 + 6*X^9 + 35*X^8 + 22*X^7 + 38*X^6 + 23*X^5 + 47*X^4 +
      60*X^3 + 27*X^2 + 8*X + 65,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s22 : XPow fSeventeenA4 19443
    (29*X^33 + 40*X^32 + 35*X^31 + 45*X^30 + 57*X^29 + 43*X^28 + 25*X^27 + 18*X^26 + 66*X^25 + 36*X^24 +
      39*X^23 + 63*X^22 + 6*X^21 + 63*X^20 + 46*X^19 + 22*X^18 + 25*X^17 + 24*X^16 + 18*X^15 +
      23*X^14 + 31*X^13 + 9*X^12 + 54*X^11 + 55*X^10 + 10*X^9 + 54*X^8 + 39*X^7 + 59*X^6 + 44*X^5 +
      47*X^4 + 51*X^3 + 32*X^2 + 57*X + 58) :=
  mul_step (by norm_num) pSeventeenA4s21 pSeventeenA41 ⟨
    12,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s23 : XPow fSeventeenA4 38886
    (44*X^33 + 42*X^32 + 6*X^31 + 42*X^30 + 20*X^29 + 35*X^28 + 66*X^27 + 12*X^26 + 10*X^25 + 51*X^24 +
      58*X^23 + 26*X^22 + 34*X^21 + 50*X^20 + 40*X^19 + X^18 + 48*X^17 + 64*X^16 + 14*X^15 + 43*X^14 +
      40*X^13 + 39*X^12 + 22*X^11 + 46*X^10 + 19*X^9 + 3*X^8 + 54*X^7 + 20*X^6 + 23*X^5 + 18*X^4 +
      4*X^3 + 53*X^2 + 37*X + 43) :=
  sq_step (by norm_num) pSeventeenA4s22 ⟨
    37*X^32 + 8*X^31 + 16*X^30 + 2*X^29 + 39*X^28 + 11*X^27 + 18*X^26 + 22*X^25 + 37*X^24 + 64*X^23 +
      40*X^22 + 50*X^21 + 19*X^20 + 54*X^19 + X^18 + 20*X^17 + 45*X^16 + 43*X^15 + 37*X^14 + 9*X^13 +
      49*X^12 + 29*X^11 + 5*X^10 + 66*X^9 + 31*X^8 + 19*X^7 + 53*X^6 + 43*X^5 + 20*X^4 + 61*X^3 +
      41*X^2 + 12*X + 6,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s24 : XPow fSeventeenA4 38887
    (7*X^33 + 31*X^32 + 20*X^31 + 21*X^30 + 13*X^29 + 29*X^28 + 2*X^27 + 6*X^26 + 45*X^25 + 64*X^24 +
      14*X^23 + 49*X^22 + 5*X^21 + 7*X^20 + 32*X^19 + 49*X^18 + 29*X^17 + 9*X^16 + 7*X^15 + 10*X^14 +
      60*X^13 + 19*X^12 + 7*X^11 + 39*X^10 + 63*X^9 + 10*X^8 + 10*X^7 + 3*X^6 + 52*X^5 + 33*X^4 +
      49*X^3 + 66*X^2 + 43*X + 34) :=
  mul_step (by norm_num) pSeventeenA4s23 pSeventeenA41 ⟨
    44,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s25 : XPow fSeventeenA4 77774
    (6*X^33 + 21*X^32 + 23*X^31 + 24*X^30 + 61*X^29 + 26*X^28 + 46*X^27 + 22*X^26 + 63*X^25 + 57*X^24 +
      54*X^23 + 6*X^22 + 51*X^21 + 58*X^20 + 64*X^19 + 13*X^18 + 15*X^17 + 20*X^16 + 60*X^15 +
      45*X^14 + 5*X^12 + 49*X^11 + 13*X^10 + 42*X^9 + 45*X^8 + 41*X^7 + 9*X^6 + 26*X^5 + 39*X^4 +
      23*X^3 + 16*X^2 + 20*X + 24) :=
  sq_step (by norm_num) pSeventeenA4s24 ⟨
    49*X^32 + 25*X^31 + 46*X^30 + 39*X^29 + 10*X^28 + 58*X^27 + 2*X^26 + 4*X^25 + 34*X^24 + 3*X^23 +
      22*X^22 + 9*X^21 + 58*X^20 + 39*X^19 + 3*X^18 + 49*X^17 + 40*X^16 + 7*X^15 + 17*X^14 + 2*X^13 +
      53*X^12 + 44*X^11 + 27*X^10 + 8*X^9 + 23*X^8 + 38*X^7 + X^6 + 38*X^5 + 45*X^4 + 32*X^3 +
      36*X^2 + 53*X + 13,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s26 : XPow fSeventeenA4 77775
    (X^33 + 66*X^32 + 21*X^31 + 52*X^30 + 23*X^29 + 44*X^28 + 45*X^27 + 32*X^26 + 44*X^25 + 47*X^23 +
      50*X^22 + 61*X^21 + 26*X^20 + 2*X^19 + 6*X^18 + 38*X^16 + 34*X^15 + 2*X^14 + 17*X^13 + 9*X^12 +
      29*X^11 + 63*X^10 + 41*X^9 + 35*X^8 + 32*X^7 + 5*X^6 + X^5 + 30*X^4 + 52*X^3 + 27*X^2 + 24*X +
      29) :=
  mul_step (by norm_num) pSeventeenA4s25 pSeventeenA41 ⟨
    6,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s27 : XPow fSeventeenA4 155550
    (64*X^33 + 21*X^32 + 20*X^31 + 66*X^30 + 5*X^29 + 58*X^28 + 8*X^27 + 64*X^26 + 24*X^25 + 11*X^24 +
      22*X^23 + 37*X^22 + 27*X^21 + 55*X^20 + 56*X^19 + 35*X^18 + 29*X^17 + 45*X^16 + 52*X^15 +
      21*X^14 + 42*X^13 + 60*X^12 + 65*X^11 + 2*X^10 + 64*X^9 + 24*X^8 + 61*X^7 + 56*X^6 + 34*X^5 +
      31*X^4 + 66*X^3 + 52*X^2 + 56*X + 13) :=
  sq_step (by norm_num) pSeventeenA4s26 ⟨
    X^32 + 17*X^31 + 27*X^30 + 4*X^29 + 6*X^28 + 40*X^27 + 24*X^26 + 19*X^25 + X^24 + 57*X^23 + 34*X^22 +
      36*X^21 + 24*X^20 + 11*X^19 + 13*X^18 + 21*X^17 + 36*X^16 + 51*X^15 + 18*X^14 + 37*X^13 +
      30*X^12 + 62*X^11 + 12*X^10 + 15*X^9 + 36*X^8 + 28*X^7 + 9*X^6 + 2*X^5 + 58*X^4 + 18*X^3 +
      15*X^2 + 17*X + 32,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s28 : XPow fSeventeenA4 155551
    (31*X^33 + 32*X^32 + 34*X^31 + 43*X^30 + 26*X^29 + 9*X^28 + 19*X^27 + 6*X^26 + 51*X^25 + 49*X^24 +
      50*X^23 + 61*X^22 + 20*X^21 + 8*X^20 + 7*X^19 + 55*X^17 + 63*X^16 + 60*X^15 + 41*X^14 +
      54*X^13 + 18*X^12 + 61*X^11 + 20*X^10 + 26*X^9 + 64*X^8 + 11*X^7 + 11*X^6 + 50*X^5 + 29*X^4 +
      34*X^3 + 19*X^2 + 13*X + 19) :=
  mul_step (by norm_num) pSeventeenA4s27 pSeventeenA41 ⟨
    64,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s29 : XPow fSeventeenA4 311102
    (12*X^33 + 65*X^32 + 20*X^31 + 27*X^30 + 21*X^29 + 8*X^28 + 11*X^27 + 10*X^26 + 31*X^25 + 12*X^24 +
      26*X^23 + 63*X^22 + 56*X^21 + 58*X^20 + 41*X^19 + 46*X^18 + 37*X^17 + 31*X^16 + 26*X^15 +
      61*X^14 + 57*X^13 + 8*X^12 + 65*X^11 + 30*X^10 + 62*X^9 + 7*X^8 + 42*X^7 + 66*X^6 + 10*X^5 +
      35*X^4 + 13*X^3 + 39*X^2 + 60*X + 1) :=
  sq_step (by norm_num) pSeventeenA4s28 ⟨
    23*X^32 + 9*X^31 + 62*X^30 + 43*X^29 + 20*X^28 + 5*X^27 + 11*X^26 + 4*X^25 + 64*X^24 + 66*X^23 +
      63*X^22 + 14*X^21 + 28*X^20 + 57*X^19 + 54*X^18 + 23*X^17 + 35*X^16 + 25*X^15 + 57*X^14 +
      2*X^13 + 15*X^12 + 28*X^11 + 5*X^10 + 7*X^9 + 47*X^8 + 10*X^7 + 60*X^6 + 21*X^5 + 32*X^4 +
      22*X^3 + 29*X^2 + 65*X + 11,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s30 : XPow fSeventeenA4 622204
    (46*X^33 + 48*X^32 + 63*X^31 + 61*X^30 + 28*X^29 + 21*X^28 + 18*X^27 + 66*X^26 + X^25 + 57*X^24 +
      52*X^23 + 42*X^22 + 54*X^21 + 47*X^20 + 30*X^19 + 52*X^18 + 27*X^17 + 46*X^16 + 4*X^15 +
      46*X^14 + 17*X^13 + 5*X^12 + 53*X^11 + 29*X^10 + 18*X^9 + 57*X^8 + 18*X^7 + 13*X^6 + 40*X^5 +
      58*X^4 + 37*X^3 + 54*X^2 + X + 49) :=
  sq_step (by norm_num) pSeventeenA4s29 ⟨
    10*X^32 + 8*X^31 + 60*X^30 + 63*X^29 + 59*X^28 + 18*X^26 + 20*X^25 + 20*X^24 + 59*X^23 + 39*X^22 +
      26*X^21 + X^20 + 50*X^19 + 56*X^18 + 25*X^17 + 19*X^16 + 62*X^15 + 56*X^14 + 25*X^13 + 55*X^12 +
      34*X^11 + 20*X^10 + 58*X^9 + 34*X^8 + 63*X^7 + 12*X^6 + 51*X^5 + 18*X^4 + 17*X^3 + 35*X^2 +
      47*X + 3,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s31 : XPow fSeventeenA4 622205
    (51*X^33 + 13*X^32 + 38*X^31 + 26*X^30 + 65*X^29 + 25*X^28 + 19*X^27 + 9*X^26 + 2*X^25 + 40*X^24 +
      66*X^23 + 24*X^22 + 3*X^21 + 29*X^20 + 57*X^19 + 25*X^18 + 49*X^17 + 14*X^16 + 51*X^15 +
      10*X^14 + 30*X^13 + 59*X^12 + 40*X^11 + 45*X^10 + 4*X^9 + 39*X^8 + 33*X^7 + 13*X^6 + 57*X^5 +
      46*X^4 + 62*X^3 + 10*X^2 + 49*X + 66) :=
  mul_step (by norm_num) pSeventeenA4s30 pSeventeenA41 ⟨
    46,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s32 : XPow fSeventeenA4 1244410
    (28*X^33 + 50*X^32 + 48*X^31 + 43*X^30 + 22*X^29 + 53*X^28 + 25*X^27 + 39*X^26 + 36*X^25 + 55*X^24 +
      58*X^23 + 4*X^22 + 53*X^21 + 20*X^20 + 30*X^19 + 40*X^18 + 26*X^17 + 41*X^16 + 19*X^15 +
      57*X^14 + 37*X^13 + 60*X^12 + 3*X^11 + 36*X^10 + 12*X^9 + X^8 + 15*X^7 + 50*X^6 + 65*X^5 +
      62*X^4 + 29*X^3 + 23*X^2 + 61*X + 44) :=
  sq_step (by norm_num) pSeventeenA4s31 ⟨
    55*X^32 + 26*X^31 + 31*X^30 + 44*X^29 + 20*X^28 + 40*X^27 + 63*X^26 + 23*X^25 + 11*X^24 + 65*X^23 +
      43*X^22 + 31*X^21 + 53*X^20 + 21*X^19 + 17*X^18 + 62*X^17 + 13*X^16 + 55*X^15 + 29*X^14 +
      53*X^13 + 43*X^12 + 4*X^11 + 32*X^10 + 65*X^9 + 63*X^8 + 54*X^7 + 48*X^6 + 36*X^5 + 34*X^4 +
      9*X^3 + 15*X^2 + 56*X + 32,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s33 : XPow fSeventeenA4 1244411
    (46*X^33 + 3*X^32 + 29*X^31 + 47*X^30 + 39*X^29 + 38*X^28 + 57*X^27 + 3*X^26 + 39*X^25 + 7*X^24 +
      39*X^23 + 26*X^22 + 34*X^21 + 9*X^20 + 11*X^19 + 51*X^18 + 37*X^17 + 28*X^16 + 28*X^15 +
      24*X^14 + 49*X^13 + 62*X^12 + 66*X^11 + 43*X^10 + 27*X^9 + 54*X^8 + X^7 + 34*X^6 + 41*X^5 +
      17*X^4 + 57*X^3 + 49*X^2 + 44*X + 46) :=
  mul_step (by norm_num) pSeventeenA4s32 pSeventeenA41 ⟨
    28,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s34 : XPow fSeventeenA4 2488822
    (62*X^33 + 13*X^32 + 24*X^31 + 16*X^29 + 20*X^28 + 47*X^27 + 32*X^26 + 20*X^25 + 3*X^24 + 46*X^23 +
      23*X^22 + 46*X^21 + 34*X^20 + 44*X^19 + 33*X^18 + 65*X^17 + 59*X^16 + 63*X^15 + 35*X^14 +
      21*X^13 + 13*X^12 + 46*X^11 + 5*X^10 + 37*X^9 + 43*X^8 + X^7 + 17*X^6 + 18*X^5 + 26*X^4 +
      8*X^3 + 14*X^2 + 50*X + 56) :=
  sq_step (by norm_num) pSeventeenA4s33 ⟨
    39*X^32 + 12*X^31 + 2*X^30 + 13*X^29 + 28*X^28 + 30*X^27 + 21*X^26 + 44*X^25 + 53*X^24 + 54*X^23 +
      23*X^22 + 20*X^21 + 20*X^19 + 26*X^18 + 52*X^17 + 46*X^16 + 41*X^15 + 12*X^14 + 6*X^13 +
      25*X^12 + 5*X^11 + 48*X^10 + 54*X^9 + 32*X^8 + 12*X^7 + 23*X^6 + 20*X^5 + 38*X^4 + 2*X^3 +
      39*X^2 + 60*X + 22,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s35 : XPow fSeventeenA4 2488823
    (52*X^33 + 44*X^32 + 36*X^31 + 57*X^30 + 56*X^29 + 4*X^28 + 24*X^27 + 57*X^26 + 25*X^25 + 24*X^24 +
      58*X^22 + 65*X^21 + 31*X^20 + 31*X^19 + 39*X^18 + 31*X^17 + 59*X^16 + 33*X^15 + 64*X^14 +
      3*X^13 + 57*X^12 + 14*X^11 + 53*X^10 + 24*X^9 + 6*X^8 + 9*X^7 + 2*X^6 + 13*X^5 + 58*X^4 +
      51*X^3 + 33*X^2 + 56*X + 54) :=
  mul_step (by norm_num) pSeventeenA4s34 pSeventeenA41 ⟨
    62,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s36 : XPow fSeventeenA4 4977646
    (9*X^33 + 55*X^32 + 9*X^31 + 23*X^30 + 42*X^29 + 60*X^28 + 17*X^27 + 7*X^26 + 53*X^25 + 30*X^24 +
      28*X^23 + 3*X^22 + 39*X^21 + 11*X^20 + 57*X^19 + 31*X^18 + 56*X^17 + 43*X^16 + 14*X^15 +
      40*X^14 + 9*X^13 + 17*X^12 + 10*X^11 + 15*X^10 + 42*X^9 + X^8 + X^7 + 53*X^6 + 29*X^5 + 27*X^4 +
      19*X^3 + 26*X^2 + 24*X + 36) :=
  sq_step (by norm_num) pSeventeenA4s35 ⟨
    24*X^32 + 7*X^31 + 22*X^30 + 27*X^29 + 26*X^28 + 52*X^27 + 34*X^26 + 22*X^25 + 37*X^24 + 5*X^23 +
      60*X^22 + 32*X^21 + 13*X^20 + 20*X^19 + 12*X^18 + 25*X^17 + 11*X^16 + 6*X^15 + 16*X^14 +
      63*X^13 + 15*X^12 + 7*X^11 + 53*X^10 + 15*X^9 + 53*X^8 + 61*X^7 + 56*X^6 + 20*X^5 + 4*X^4 +
      37*X^3 + 65*X^2 + 59*X + 21,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s37 : XPow fSeventeenA4 9955292
    (45*X^33 + 51*X^32 + 32*X^31 + 42*X^30 + 9*X^29 + 55*X^28 + 19*X^27 + 7*X^26 + 55*X^25 + 54*X^24 +
      31*X^23 + 37*X^22 + 57*X^21 + 20*X^20 + X^19 + 40*X^18 + 6*X^17 + 2*X^16 + 31*X^15 + 22*X^14 +
      5*X^12 + 2*X^11 + 34*X^10 + 36*X^9 + 8*X^8 + 45*X^7 + 35*X^6 + 18*X^5 + 18*X^4 + 48*X^3 +
      45*X^2 + 54*X + 23) :=
  sq_step (by norm_num) pSeventeenA4s36 ⟨
    14*X^32 + 50*X^31 + 61*X^30 + 11*X^29 + 3*X^28 + 18*X^27 + 64*X^26 + 10*X^25 + 2*X^24 + 3*X^23 +
      47*X^22 + 46*X^21 + 50*X^20 + 64*X^19 + 30*X^18 + 39*X^17 + 20*X^16 + 59*X^15 + 30*X^14 +
      35*X^13 + 32*X^12 + 28*X^11 + 9*X^10 + 63*X^9 + 57*X^8 + 12*X^7 + 21*X^6 + 2*X^5 + 33*X^4 +
      62*X^3 + 55*X^2 + 21*X,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s38 : XPow fSeventeenA4 9955293
    (35*X^33 + 53*X^32 + 53*X^31 + 42*X^30 + 66*X^29 + 4*X^28 + 12*X^27 + 57*X^26 + 57*X^25 + 28*X^24 +
      43*X^23 + 16*X^22 + 9*X^21 + 51*X^20 + 58*X^19 + 39*X^18 + 53*X^17 + 40*X^15 + 15*X^14 +
      28*X^13 + 37*X^12 + 20*X^11 + 26*X^10 + 45*X^9 + 40*X^7 + 28*X^6 + X^5 + 47*X^3 + 6*X^2 + 23*X +
      50) :=
  mul_step (by norm_num) pSeventeenA4s37 pSeventeenA41 ⟨
    45,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s39 : XPow fSeventeenA4 19910586
    (48*X^33 + 33*X^32 + 40*X^31 + 45*X^29 + 20*X^28 + 46*X^27 + 49*X^26 + 24*X^25 + 25*X^24 + 32*X^23 +
      50*X^22 + 23*X^21 + 31*X^20 + 42*X^19 + 54*X^18 + 10*X^17 + 23*X^16 + 33*X^15 + 21*X^14 +
      60*X^13 + 52*X^12 + 28*X^11 + 50*X^10 + 30*X^9 + 28*X^8 + 48*X^7 + 25*X^6 + 42*X^5 + 5*X^4 +
      13*X^3 + 58*X^2 + 44*X + 30) :=
  sq_step (by norm_num) pSeventeenA4s38 ⟨
    19*X^32 + 51*X^31 + 42*X^30 + 64*X^29 + 11*X^28 + 50*X^27 + 5*X^26 + 48*X^25 + 25*X^24 + 4*X^23 +
      3*X^22 + 4*X^21 + 14*X^20 + 7*X^19 + 15*X^18 + 47*X^17 + 21*X^16 + 27*X^15 + 51*X^14 + 36*X^13 +
      47*X^12 + 29*X^11 + 43*X^10 + 29*X^9 + 3*X^8 + 59*X^7 + 49*X^6 + 29*X^5 + 34*X^4 + 4*X^3 +
      47*X^2 + 60*X + 55,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s40 : XPow fSeventeenA4 19910587
    (7*X^33 + 49*X^32 + 43*X^31 + 40*X^30 + 63*X^29 + 30*X^28 + 32*X^27 + 44*X^26 + 55*X^25 + 2*X^24 +
      43*X^23 + 15*X^22 + 55*X^21 + 6*X^20 + 33*X^19 + 5*X^18 + 64*X^17 + 58*X^16 + 9*X^14 + 14*X^13 +
      43*X^12 + 44*X^11 + 64*X^10 + 63*X^9 + 8*X^7 + 8*X^6 + 36*X^5 + 2*X^4 + 11*X^3 + 33*X^2 + 30*X +
      31) :=
  mul_step (by norm_num) pSeventeenA4s39 pSeventeenA41 ⟨
    48,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s41 : XPow fSeventeenA4 39821174
    (24*X^33 + 10*X^32 + 40*X^31 + 42*X^30 + 38*X^29 + 63*X^28 + 66*X^27 + 27*X^26 + 11*X^25 + 62*X^24 +
      62*X^23 + 21*X^22 + 11*X^21 + 39*X^20 + 63*X^19 + 11*X^18 + 2*X^17 + 17*X^16 + 33*X^15 +
      56*X^14 + 20*X^13 + X^12 + 23*X^11 + 26*X^10 + 54*X^9 + 65*X^8 + 63*X^7 + 24*X^6 + 66*X^5 +
      23*X^4 + 40*X^3 + 14*X^2 + 65*X + 42) :=
  sq_step (by norm_num) pSeventeenA4s40 ⟨
    49*X^32 + 9*X^31 + 30*X^30 + 24*X^29 + 8*X^28 + 54*X^27 + 55*X^26 + 14*X^25 + 11*X^24 + 4*X^23 +
      14*X^22 + 17*X^21 + 51*X^20 + X^19 + 2*X^18 + 21*X^17 + 52*X^16 + 49*X^15 + 3*X^14 + 34*X^13 +
      53*X^12 + 34*X^11 + 54*X^10 + 66*X^9 + 64*X^8 + 52*X^7 + 54*X^6 + 13*X^5 + 24*X^4 + 21*X^3 +
      41*X^2 + 26*X + 64,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s42 : XPow fSeventeenA4 39821175
    (64*X^33 + 11*X^32 + 30*X^31 + 2*X^30 + 51*X^29 + 58*X^28 + 52*X^27 + 21*X^26 + 10*X^25 + 47*X^24 +
      51*X^23 + 7*X^22 + 51*X^21 + 45*X^20 + 34*X^19 + 33*X^18 + 4*X^17 + 12*X^16 + 12*X^15 +
      28*X^14 + 49*X^13 + 64*X^12 + 23*X^11 + 4*X^10 + 49*X^9 + 39*X^8 + 49*X^7 + 49*X^6 + 5*X^5 +
      X^4 + 24*X^3 + 26*X^2 + 42*X + 49) :=
  mul_step (by norm_num) pSeventeenA4s41 pSeventeenA41 ⟨
    24,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s43 : XPow fSeventeenA4 79642350
    (52*X^33 + 51*X^32 + 26*X^31 + 24*X^30 + 46*X^29 + 3*X^28 + 27*X^27 + 11*X^26 + 47*X^25 + 43*X^24 +
      36*X^23 + 23*X^22 + 25*X^21 + 57*X^20 + 32*X^19 + 48*X^18 + 22*X^17 + 48*X^16 + 29*X^15 +
      18*X^14 + 35*X^13 + 59*X^12 + 27*X^11 + 43*X^10 + 4*X^9 + 43*X^8 + 25*X^7 + 15*X^6 + 42*X^5 +
      26*X^4 + 5*X^3 + 57*X^2 + 43*X + 38) :=
  sq_step (by norm_num) pSeventeenA4s42 ⟨
    9*X^32 + 38*X^31 + 24*X^30 + 43*X^29 + 20*X^28 + 57*X^27 + 27*X^26 + 9*X^25 + 53*X^24 + 17*X^23 +
      50*X^22 + 17*X^21 + 51*X^20 + 4*X^19 + 26*X^18 + 60*X^17 + 19*X^16 + 28*X^15 + 49*X^14 +
      48*X^13 + 23*X^12 + 58*X^11 + 22*X^10 + 49*X^9 + 65*X^8 + 25*X^7 + 44*X^6 + 34*X^5 + 7*X^4 +
      13*X^3 + 38*X^2 + 26*X + 24,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s44 : XPow fSeventeenA4 79642351
    (34*X^33 + 19*X^32 + 65*X^31 + 35*X^30 + 44*X^29 + 32*X^28 + 54*X^27 + 24*X^26 + 42*X^25 + 37*X^24 +
      21*X^23 + 61*X^22 + 16*X^21 + 60*X^20 + 42*X^19 + 11*X^18 + 31*X^17 + 17*X^16 + 12*X^15 +
      30*X^14 + 29*X^13 + 60*X^12 + 3*X^11 + 52*X^10 + 53*X^9 + 40*X^8 + 58*X^7 + 61*X^6 + 54*X^5 +
      21*X^4 + 34*X^3 + 59*X^2 + 38*X + 28) :=
  mul_step (by norm_num) pSeventeenA4s43 pSeventeenA41 ⟨
    52,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s45 : XPow fSeventeenA4 159284702
    (62*X^33 + 13*X^32 + 37*X^31 + 45*X^30 + 53*X^29 + 55*X^28 + 41*X^27 + 16*X^26 + 29*X^25 + 18*X^24 +
      39*X^23 + 6*X^22 + 31*X^21 + 63*X^20 + 36*X^19 + 3*X^18 + 23*X^17 + 35*X^16 + 28*X^15 +
      39*X^14 + 62*X^13 + 48*X^12 + 64*X^11 + 26*X^10 + 5*X^9 + 26*X^8 + 63*X^7 + 26*X^6 + 40*X^5 +
      60*X^4 + 55*X^3 + 17*X^2 + 36*X + 2) :=
  sq_step (by norm_num) pSeventeenA4s44 ⟨
    17*X^32 + 7*X^31 + 22*X^30 + 39*X^29 + 59*X^28 + 20*X^27 + 34*X^26 + 8*X^25 + 9*X^24 + 31*X^23 +
      6*X^22 + 20*X^21 + 37*X^20 + 38*X^19 + 31*X^18 + 58*X^17 + 52*X^16 + 15*X^15 + 57*X^14 +
      17*X^13 + 25*X^12 + 17*X^11 + 5*X^10 + 45*X^9 + 40*X^8 + 22*X^7 + 45*X^6 + 25*X^5 + 38*X^4 +
      59*X^3 + 14*X^2 + 20*X + 60,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s46 : XPow fSeventeenA4 318569404
    (54*X^33 + 39*X^32 + 17*X^31 + 25*X^30 + 53*X^29 + 60*X^28 + 65*X^27 + 65*X^26 + 64*X^25 + 65*X^24 +
      X^23 + 52*X^22 + 25*X^21 + 4*X^20 + 43*X^19 + 33*X^18 + 20*X^17 + 52*X^16 + 33*X^15 + 29*X^14 +
      58*X^13 + 16*X^11 + 9*X^10 + 4*X^9 + 57*X^8 + 5*X^7 + X^6 + 25*X^5 + 23*X^4 + 12*X^3 + 39*X^2 +
      53*X + 17) :=
  sq_step (by norm_num) pSeventeenA4s45 ⟨
    25*X^32 + 10*X^31 + 23*X^30 + 59*X^29 + 14*X^28 + 62*X^27 + 61*X^26 + 23*X^25 + 11*X^24 + 27*X^23 +
      37*X^22 + 18*X^21 + 51*X^20 + 31*X^19 + 58*X^18 + 40*X^17 + 49*X^16 + 44*X^15 + 51*X^14 +
      30*X^13 + 60*X^12 + 59*X^11 + 65*X^10 + 46*X^9 + 10*X^8 + 47*X^7 + 25*X^6 + 19*X^5 + 4*X^4 +
      4*X^3 + 25*X^2 + 32*X + 5,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s47 : XPow fSeventeenA4 637138808
    (44*X^33 + 30*X^32 + 25*X^31 + 54*X^30 + 24*X^29 + 49*X^28 + 36*X^27 + 33*X^26 + 63*X^25 + 57*X^24 +
      20*X^23 + 10*X^22 + 22*X^21 + 21*X^20 + 41*X^19 + 23*X^18 + 53*X^17 + 12*X^16 + 8*X^15 +
      26*X^14 + 16*X^13 + 10*X^12 + 66*X^11 + 48*X^10 + 12*X^9 + 8*X^8 + 35*X^7 + 62*X^6 + 3*X^5 +
      41*X^4 + 4*X^3 + 41*X^2 + 59*X + 45) :=
  sq_step (by norm_num) pSeventeenA4s46 ⟨
    35*X^32 + 53*X^31 + 3*X^30 + X^29 + 52*X^28 + 55*X^27 + 58*X^26 + 28*X^25 + 27*X^24 + 39*X^23 +
      57*X^22 + 36*X^21 + X^20 + 42*X^19 + 31*X^18 + 42*X^17 + 7*X^16 + 13*X^15 + 46*X^14 + 17*X^13 +
      17*X^12 + 38*X^11 + 51*X^10 + 28*X^9 + 9*X^8 + 55*X^7 + 22*X^6 + 48*X^5 + 6*X^4 + 34*X^2 +
      46*X + 35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s48 : XPow fSeventeenA4 1274277616
    (5*X^33 + 18*X^32 + 53*X^31 + 39*X^30 + 53*X^29 + 62*X^28 + 18*X^27 + 55*X^26 + 15*X^25 + 24*X^24 +
      56*X^23 + 13*X^22 + 13*X^21 + 26*X^20 + 7*X^19 + 23*X^18 + 60*X^17 + 40*X^16 + 7*X^15 +
      19*X^14 + 50*X^13 + 51*X^12 + 37*X^11 + 30*X^10 + 3*X^9 + 61*X^8 + 56*X^7 + 3*X^6 + 20*X^5 +
      3*X^4 + 54*X^3 + 24*X^2 + 20*X + 42) :=
  sq_step (by norm_num) pSeventeenA4s47 ⟨
    60*X^32 + 28*X^31 + 42*X^30 + 7*X^29 + 9*X^28 + 60*X^27 + 5*X^26 + 51*X^25 + 43*X^24 + X^23 +
      61*X^22 + X^21 + 50*X^20 + 6*X^19 + 56*X^18 + 35*X^17 + 35*X^16 + 62*X^15 + 63*X^14 + 2*X^13 +
      26*X^12 + 46*X^11 + 12*X^10 + 58*X^9 + 17*X^8 + 34*X^7 + 18*X^6 + 48*X^5 + 52*X^4 + 58*X^3 +
      4*X^2 + 63*X + 31,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s49 : XPow fSeventeenA4 1274277617
    (46*X^33 + 33*X^32 + 3*X^31 + 12*X^30 + 26*X^29 + 61*X^28 + 63*X^27 + 45*X^26 + 2*X^25 + 11*X^24 +
      36*X^23 + X^22 + 62*X^21 + 20*X^20 + 25*X^19 + 19*X^18 + X^17 + 11*X^16 + 21*X^15 + 7*X^14 +
      61*X^13 + 26*X^12 + 21*X^11 + 54*X^10 + 13*X^9 + 51*X^8 + 11*X^7 + 36*X^6 + 16*X^5 + 4*X^4 +
      54*X^3 + 37*X^2 + 42*X + 13) :=
  mul_step (by norm_num) pSeventeenA4s48 pSeventeenA41 ⟨
    5,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s50 : XPow fSeventeenA4 2548555234
    (56*X^33 + 65*X^32 + 27*X^31 + 16*X^30 + 25*X^29 + 61*X^28 + 60*X^27 + 48*X^26 + 49*X^25 + 41*X^24 +
      58*X^23 + 33*X^22 + 31*X^21 + 35*X^20 + 7*X^19 + 15*X^18 + 30*X^17 + 5*X^16 + 24*X^15 +
      22*X^14 + 18*X^13 + 2*X^12 + 61*X^11 + 25*X^10 + 51*X^9 + 39*X^8 + 16*X^7 + 60*X^6 + 22*X^5 +
      18*X^4 + 34*X^3 + 28*X^2 + 15*X + 53) :=
  sq_step (by norm_num) pSeventeenA4s49 ⟨
    39*X^32 + 25*X^31 + 9*X^30 + 47*X^29 + 26*X^28 + 40*X^27 + 29*X^26 + 6*X^25 + 63*X^24 + 43*X^23 +
      62*X^22 + 58*X^21 + X^20 + 53*X^19 + 56*X^18 + 55*X^17 + 47*X^16 + 64*X^15 + 51*X^14 + 38*X^13 +
      27*X^12 + 6*X^11 + 43*X^10 + 4*X^9 + 62*X^8 + 55*X^7 + 50*X^6 + 23*X^5 + 45*X^4 + 32*X^3 +
      9*X^2 + 29*X + 43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s51 : XPow fSeventeenA4 2548555235
    (57*X^33 + 4*X^32 + 55*X^31 + 8*X^30 + 33*X^29 + 19*X^28 + 17*X^27 + 50*X^26 + 9*X^25 + 23*X^24 +
      36*X^23 + 44*X^22 + 63*X^21 + 32*X^20 + 24*X^19 + 13*X^18 + 64*X^17 + 42*X^16 + 31*X^15 +
      59*X^14 + 47*X^13 + 45*X^12 + 18*X^11 + 46*X^10 + 24*X^9 + 27*X^8 + 29*X^7 + 27*X^6 + 43*X^5 +
      10*X^4 + 29*X^3 + 58*X^2 + 53*X + 25) :=
  mul_step (by norm_num) pSeventeenA4s50 pSeventeenA41 ⟨
    56,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s52 : XPow fSeventeenA4 5097110470
    (36*X^33 + 60*X^32 + 40*X^31 + 57*X^30 + 53*X^29 + 36*X^28 + 64*X^27 + 26*X^26 + 24*X^25 + 23*X^24 +
      36*X^23 + 35*X^22 + 61*X^21 + 18*X^20 + 66*X^19 + 10*X^18 + 40*X^17 + 53*X^16 + 52*X^15 +
      35*X^14 + 62*X^13 + 49*X^12 + 46*X^11 + 31*X^10 + 49*X^9 + 41*X^8 + 45*X^7 + 19*X^6 + 35*X^5 +
      23*X^4 + 8*X^3 + 57*X^2 + 60*X + 3) :=
  sq_step (by norm_num) pSeventeenA4s51 ⟨
    33*X^32 + 11*X^31 + 65*X^30 + 14*X^29 + 35*X^28 + X^27 + 48*X^26 + 45*X^25 + 50*X^24 + 33*X^23 +
      20*X^22 + 65*X^21 + 51*X^20 + 14*X^19 + 57*X^18 + 4*X^17 + 41*X^16 + 37*X^15 + 24*X^14 +
      33*X^13 + 41*X^12 + 53*X^11 + 56*X^10 + 43*X^9 + 62*X^8 + 18*X^7 + 20*X^6 + 60*X^5 + 41*X^4 +
      19*X^3 + 59*X^2 + 14*X + 3,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s53 : XPow fSeventeenA4 5097110471
    (7*X^33 + 30*X^32 + 39*X^31 + 66*X^30 + 18*X^29 + 52*X^28 + 30*X^27 + 39*X^26 + 12*X^25 + 47*X^24 +
      13*X^23 + 55*X^22 + 36*X^21 + 39*X^20 + 11*X^19 + 53*X^18 + 54*X^16 + 36*X^15 + 7*X^14 +
      54*X^13 + 7*X^12 + 60*X^11 + 41*X^10 + 17*X^9 + 9*X^8 + 23*X^7 + 43*X^6 + 63*X^5 + 50*X^4 +
      5*X^3 + 35*X^2 + 3*X + 40) :=
  mul_step (by norm_num) pSeventeenA4s52 pSeventeenA41 ⟨
    36,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s54 : XPow fSeventeenA4 10194220942
    (36*X^33 + 44*X^32 + 27*X^31 + 31*X^30 + 43*X^29 + 32*X^28 + 38*X^27 + 23*X^26 + 30*X^25 + 58*X^24 +
      64*X^23 + 29*X^22 + 41*X^21 + 25*X^20 + 32*X^19 + 44*X^18 + 49*X^17 + 17*X^16 + 42*X^15 +
      31*X^14 + 30*X^13 + 27*X^12 + 43*X^11 + 6*X^10 + X^9 + 16*X^8 + 25*X^7 + 26*X^6 + 7*X^5 +
      25*X^4 + 12*X^3 + 52*X^2 + 50*X + 14) :=
  sq_step (by norm_num) pSeventeenA4s53 ⟨
    49*X^32 + 11*X^31 + 52*X^30 + 63*X^29 + 10*X^28 + 60*X^27 + 40*X^26 + 66*X^25 + 17*X^24 + 5*X^23 +
      40*X^22 + 61*X^21 + 58*X^20 + 42*X^19 + 23*X^18 + 45*X^17 + 56*X^16 + 33*X^15 + X^14 + 47*X^13 +
      9*X^12 + 58*X^11 + 5*X^10 + 33*X^9 + 62*X^8 + 8*X^7 + 57*X^6 + 10*X^5 + 48*X^4 + 51*X^3 +
      62*X^2 + 30*X + 60,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s55 : XPow fSeventeenA4 20388441884
    (12*X^33 + 26*X^32 + 39*X^31 + 57*X^30 + 53*X^29 + 23*X^28 + 7*X^27 + 57*X^26 + 15*X^25 + 17*X^24 +
      20*X^23 + 35*X^22 + 50*X^21 + 46*X^20 + 31*X^19 + 66*X^18 + 24*X^17 + 24*X^16 + 9*X^15 +
      47*X^14 + 30*X^13 + 57*X^12 + 40*X^11 + 62*X^10 + 48*X^9 + 17*X^8 + 38*X^7 + 49*X^6 + 47*X^5 +
      61*X^4 + 64*X^3 + 8*X^2 + 59*X + 53) :=
  sq_step (by norm_num) pSeventeenA4s54 ⟨
    23*X^32 + 54*X^31 + 57*X^30 + 3*X^29 + 56*X^28 + 50*X^27 + 37*X^26 + 46*X^25 + 56*X^24 + 28*X^22 +
      5*X^21 + 65*X^20 + 57*X^19 + 64*X^18 + 60*X^17 + X^16 + 66*X^15 + 5*X^14 + 7*X^13 + 56*X^12 +
      62*X^11 + 11*X^10 + 7*X^9 + 54*X^8 + 5*X^7 + 66*X^6 + 37*X^5 + 53*X^4 + 34*X^3 + 12*X^2 + 46*X +
      12,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s56 : XPow fSeventeenA4 20388441885
    (53*X^33 + 58*X^32 + 51*X^31 + 35*X^30 + 17*X^29 + 3*X^28 + 36*X^27 + 20*X^26 + 58*X^25 + 46*X^24 +
      50*X^23 + 48*X^22 + 52*X^21 + 22*X^20 + 44*X^19 + 6*X^18 + 51*X^17 + 32*X^16 + 25*X^15 +
      34*X^14 + 14*X^13 + 27*X^12 + 27*X^11 + 23*X^10 + 9*X^9 + 26*X^8 + 28*X^7 + 5*X^6 + 52*X^5 +
      11*X^4 + 13*X^3 + 6*X^2 + 53*X + 58) :=
  mul_step (by norm_num) pSeventeenA4s55 pSeventeenA41 ⟨
    12,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s57 : XPow fSeventeenA4 40776883770
    (22*X^33 + 52*X^32 + 33*X^31 + 28*X^30 + 24*X^29 + 34*X^28 + 58*X^27 + 42*X^26 + 47*X^24 + 10*X^23 +
      25*X^22 + 53*X^21 + 5*X^20 + 2*X^19 + 23*X^18 + 51*X^17 + 51*X^16 + 50*X^15 + 37*X^14 +
      41*X^13 + 27*X^12 + 8*X^11 + 45*X^10 + 63*X^9 + 37*X^8 + 19*X^7 + 51*X^6 + 23*X^5 + 31*X^4 +
      26*X^3 + 37*X^2 + 14*X + 22) :=
  sq_step (by norm_num) pSeventeenA4s56 ⟨
    62*X^32 + 23*X^31 + 48*X^30 + 30*X^29 + 60*X^28 + 57*X^27 + 19*X^26 + 16*X^25 + X^24 + 15*X^23 +
      3*X^22 + 54*X^21 + 21*X^20 + 55*X^19 + 13*X^18 + 50*X^17 + 19*X^16 + 27*X^15 + 45*X^14 +
      52*X^13 + 32*X^12 + 13*X^11 + 63*X^10 + 40*X^9 + 14*X^8 + 26*X^7 + 36*X^6 + 35*X^5 + 41*X^4 +
      56*X^3 + 39*X^2 + 27*X + 34,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s58 : XPow fSeventeenA4 81553767540
    (X^33 + 15*X^32 + 58*X^31 + 17*X^30 + 33*X^29 + 46*X^28 + 20*X^27 + 43*X^26 + 36*X^25 + 7*X^24 +
      56*X^23 + 54*X^22 + X^21 + 51*X^20 + 27*X^19 + 40*X^18 + 53*X^17 + 44*X^16 + X^15 + 19*X^14 +
      17*X^13 + 38*X^12 + 4*X^11 + 47*X^10 + 48*X^9 + 43*X^8 + 40*X^7 + 37*X^6 + 12*X^5 + 60*X^4 +
      30*X^3 + 22*X^2 + 48*X + 50) :=
  sq_step (by norm_num) pSeventeenA4s57 ⟨
    15*X^32 + 27*X^31 + 53*X^30 + 28*X^29 + 48*X^28 + 33*X^27 + 2*X^26 + 7*X^25 + 65*X^24 + 65*X^23 +
      2*X^22 + 56*X^21 + 37*X^20 + 53*X^19 + 22*X^18 + 12*X^17 + 41*X^16 + 52*X^15 + 58*X^14 +
      65*X^13 + 3*X^12 + 65*X^11 + 60*X^10 + 48*X^9 + 5*X^8 + 60*X^7 + 6*X^6 + 9*X^5 + 56*X^4 +
      41*X^3 + 62*X^2 + 65*X + 65,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s59 : XPow fSeventeenA4 81553767541
    (34*X^33 + 54*X^32 + 50*X^31 + 65*X^30 + 12*X^29 + 42*X^28 + 58*X^27 + 42*X^26 + 16*X^25 + 47*X^24 +
      5*X^23 + 12*X^22 + 18*X^21 + 43*X^20 + 27*X^19 + 18*X^18 + 63*X^17 + 42*X^16 + 6*X^15 +
      62*X^14 + 40*X^13 + 42*X^12 + 5*X^11 + 18*X^10 + 20*X^9 + 39*X^8 + 52*X^7 + 42*X^6 + 9*X^5 +
      20*X^4 + 28*X^3 + 38*X^2 + 50*X + 16) :=
  mul_step (by norm_num) pSeventeenA4s58 pSeventeenA41 ⟨
    1,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s60 : XPow fSeventeenA4 163107535082
    (57*X^33 + 4*X^32 + 44*X^31 + 35*X^30 + 38*X^29 + 4*X^28 + 20*X^27 + 43*X^26 + 22*X^25 + 57*X^24 +
      61*X^23 + 37*X^22 + 27*X^21 + 37*X^20 + 65*X^19 + 45*X^18 + 44*X^17 + 21*X^16 + 15*X^15 +
      35*X^14 + 25*X^13 + 46*X^12 + 18*X^11 + 2*X^10 + 30*X^9 + 12*X^8 + 54*X^7 + 33*X^6 + 41*X^5 +
      19*X^4 + 38*X^3 + 47*X^2 + 37) :=
  sq_step (by norm_num) pSeventeenA4s59 ⟨
    17*X^32 + 42*X^31 + 11*X^30 + 37*X^29 + 61*X^28 + 62*X^27 + 15*X^26 + 25*X^25 + 52*X^24 + 48*X^23 +
      33*X^22 + 24*X^21 + 22*X^20 + 20*X^19 + 31*X^18 + 10*X^17 + 25*X^16 + 66*X^15 + 21*X^14 +
      29*X^13 + 43*X^12 + 42*X^11 + 25*X^10 + 41*X^9 + 60*X^8 + 47*X^7 + 51*X^6 + X^5 + 39*X^4 +
      31*X^3 + 16*X^2 + 34*X + 24,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s61 : XPow fSeventeenA4 326215070164
    (24*X^33 + 65*X^32 + 25*X^31 + 57*X^30 + 57*X^29 + 24*X^28 + 6*X^27 + 39*X^26 + 57*X^25 + 22*X^24 +
      42*X^23 + 46*X^22 + 40*X^21 + 62*X^20 + 51*X^19 + 36*X^18 + 35*X^17 + 44*X^16 + 26*X^15 +
      18*X^14 + 51*X^13 + 42*X^12 + 33*X^11 + 39*X^10 + 5*X^9 + 57*X^8 + 12*X^7 + 42*X^6 + 50*X^5 +
      48*X^4 + 52*X^3 + 36*X^2 + 33*X + 37) :=
  sq_step (by norm_num) pSeventeenA4s60 ⟨
    33*X^32 + 11*X^31 + 17*X^30 + 15*X^29 + 10*X^28 + 9*X^27 + 28*X^26 + 25*X^25 + 39*X^24 + 17*X^23 +
      11*X^22 + 34*X^21 + 40*X^20 + 17*X^19 + 49*X^18 + 19*X^16 + 24*X^15 + 11*X^14 + 54*X^13 +
      23*X^12 + 12*X^11 + 12*X^10 + 39*X^9 + 60*X^8 + 49*X^7 + 29*X^6 + 16*X^5 + 59*X^4 + 5*X^3 +
      49*X^2 + 23*X + 34,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s62 : XPow fSeventeenA4 652430140328
    (43*X^33 + 25*X^32 + 32*X^31 + 27*X^30 + 39*X^29 + 13*X^28 + 47*X^27 + 35*X^26 + 15*X^25 + 49*X^24 +
      34*X^23 + 46*X^22 + 65*X^21 + 8*X^20 + 28*X^19 + 52*X^18 + 31*X^17 + 28*X^16 + 60*X^15 +
      47*X^14 + 4*X^13 + 4*X^12 + 8*X^11 + 2*X^9 + 22*X^8 + 65*X^7 + 11*X^6 + 2*X^5 + 34*X^4 +
      21*X^3 + 46*X^2 + 19*X + 39) :=
  sq_step (by norm_num) pSeventeenA4s61 ⟨
    40*X^32 + 61*X^31 + 59*X^30 + 9*X^29 + 63*X^28 + 37*X^27 + 28*X^26 + 39*X^25 + 4*X^24 + 54*X^23 +
      11*X^22 + 22*X^21 + 54*X^20 + 4*X^19 + 24*X^18 + 59*X^17 + 51*X^16 + 42*X^15 + 53*X^14 +
      12*X^13 + 44*X^12 + 57*X^11 + 9*X^10 + 23*X^9 + 12*X^8 + 65*X^7 + 24*X^6 + 14*X^5 + 59*X^4 +
      55*X^3 + 21*X^2 + 37*X + 9,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s63 : XPow fSeventeenA4 652430140329
    (38*X^33 + 61*X^32 + 39*X^31 + 8*X^30 + 25*X^29 + 55*X^28 + 10*X^27 + 5*X^26 + 34*X^25 + 49*X^24 +
      16*X^23 + 2*X^22 + 63*X^21 + 46*X^20 + 29*X^19 + 41*X^17 + 14*X^16 + 24*X^15 + 63*X^14 +
      23*X^13 + 34*X^12 + 3*X^11 + 52*X^10 + 38*X^9 + 22*X^8 + 53*X^7 + 19*X^6 + 52*X^5 + 60*X^4 +
      36*X^3 + 58*X^2 + 39*X + 18) :=
  mul_step (by norm_num) pSeventeenA4s62 pSeventeenA41 ⟨
    43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s64 : XPow fSeventeenA4 1304860280658
    (31*X^33 + 6*X^32 + 59*X^31 + 14*X^30 + 14*X^29 + 20*X^28 + 20*X^27 + 43*X^26 + 11*X^25 + 53*X^24 +
      65*X^23 + 25*X^22 + 61*X^21 + 56*X^20 + 60*X^19 + 16*X^18 + 19*X^17 + 20*X^16 + 61*X^15 +
      11*X^14 + 16*X^13 + 62*X^12 + 51*X^11 + 23*X^10 + 19*X^9 + 8*X^8 + 50*X^7 + 52*X^6 + 64*X^5 +
      48*X^4 + 20*X^3 + 56*X^2 + 26*X + 57) :=
  sq_step (by norm_num) pSeventeenA4s63 ⟨
    37*X^32 + 46*X^31 + 41*X^30 + 13*X^29 + 13*X^28 + 35*X^27 + 33*X^26 + 23*X^25 + 17*X^24 + 7*X^23 +
      8*X^22 + X^21 + 48*X^20 + 37*X^19 + 55*X^18 + 30*X^17 + 54*X^16 + 42*X^15 + 21*X^14 + 50*X^13 +
      8*X^12 + 60*X^11 + 44*X^10 + X^9 + 2*X^8 + 15*X^7 + 40*X^6 + 15*X^5 + 54*X^4 + 27*X^3 + 13*X^2 +
      6*X + 21,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s65 : XPow fSeventeenA4 2609720561316
    (41*X^33 + 9*X^32 + 40*X^31 + 49*X^30 + 23*X^29 + 41*X^28 + 40*X^27 + 49*X^26 + 50*X^25 + 53*X^24 +
      57*X^23 + 52*X^22 + 54*X^21 + 21*X^20 + 61*X^19 + 10*X^18 + 25*X^17 + 6*X^16 + 32*X^15 +
      37*X^14 + 52*X^13 + 11*X^12 + 14*X^11 + 41*X^10 + 4*X^9 + 52*X^8 + 16*X^7 + 39*X^6 + 66*X^5 +
      30*X^4 + 57*X^3 + 56*X^2 + 14*X + 65) :=
  sq_step (by norm_num) pSeventeenA4s64 ⟨
    23*X^32 + 5*X^31 + 12*X^30 + 64*X^29 + 20*X^28 + 10*X^27 + 39*X^26 + 2*X^25 + 50*X^24 + 40*X^23 +
      51*X^22 + 7*X^21 + 16*X^20 + 26*X^19 + 36*X^18 + 53*X^17 + 60*X^16 + 34*X^15 + 18*X^14 +
      5*X^13 + 19*X^12 + 27*X^11 + 32*X^10 + 64*X^9 + 64*X^7 + 3*X^6 + 50*X^5 + 35*X^4 + 8*X^3 +
      66*X^2 + 25*X + 2,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s66 : XPow fSeventeenA4 2609720561317
    (51*X^33 + 10*X^32 + 62*X^31 + 62*X^30 + 54*X^29 + 4*X^28 + 61*X^27 + 28*X^26 + 20*X^25 + 23*X^24 +
      53*X^23 + 36*X^22 + 8*X^21 + 47*X^20 + 13*X^19 + 64*X^18 + 48*X^17 + 38*X^16 + 40*X^15 +
      21*X^14 + 26*X^13 + 31*X^12 + 61*X^11 + 47*X^10 + 47*X^9 + 42*X^8 + 51*X^7 + 23*X^6 + 16*X^5 +
      49*X^4 + 34*X^3 + 6*X^2 + 65*X + 53) :=
  mul_step (by norm_num) pSeventeenA4s65 pSeventeenA41 ⟨
    41,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s67 : XPow fSeventeenA4 5219441122634
    (51*X^33 + 14*X^32 + 3*X^31 + 31*X^30 + 43*X^29 + 46*X^28 + 44*X^27 + 44*X^26 + 25*X^25 + 2*X^24 +
      53*X^23 + 44*X^22 + 45*X^21 + 25*X^20 + 38*X^19 + 59*X^18 + 40*X^17 + 53*X^16 + 11*X^15 +
      16*X^14 + 46*X^13 + 50*X^12 + 63*X^11 + 24*X^10 + 10*X^9 + 57*X^8 + 30*X^7 + 60*X^6 + 8*X^5 +
      8*X^4 + 55*X^3 + 3*X^2 + 5*X + 8) :=
  sq_step (by norm_num) pSeventeenA4s66 ⟨
    55*X^32 + 55*X^31 + 13*X^30 + 26*X^29 + 3*X^28 + X^27 + 43*X^26 + 66*X^25 + X^24 + 26*X^23 + 52*X^22 +
      32*X^21 + 42*X^20 + 24*X^19 + 7*X^18 + 43*X^17 + 18*X^16 + 44*X^15 + 29*X^14 + 47*X^13 +
      9*X^12 + 20*X^11 + 36*X^10 + 51*X^9 + 17*X^8 + 65*X^7 + 33*X^6 + 39*X^5 + 54*X^4 + 59*X^3 +
      X^2 + X + 5,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s68 : XPow fSeventeenA4 10438882245268
    (18*X^33 + 31*X^32 + 34*X^31 + 58*X^29 + 31*X^28 + 58*X^27 + 60*X^26 + 43*X^25 + X^24 + 22*X^23 +
      44*X^22 + 57*X^21 + 63*X^20 + 5*X^19 + 24*X^18 + 55*X^17 + 36*X^16 + 62*X^15 + 47*X^14 + X^13 +
      24*X^12 + 10*X^11 + 19*X^10 + 23*X^9 + X^8 + 16*X^7 + 28*X^6 + 45*X^5 + X^4 + 42*X^3 + 10*X^2 +
      30*X + 31) :=
  sq_step (by norm_num) pSeventeenA4s67 ⟨
    55*X^32 + 61*X^31 + 34*X^30 + 36*X^29 + 3*X^28 + 30*X^27 + 54*X^26 + 38*X^25 + 53*X^24 + 43*X^23 +
      50*X^22 + 47*X^21 + 57*X^20 + 3*X^19 + 62*X^18 + 22*X^17 + 16*X^16 + 5*X^15 + 45*X^14 +
      54*X^13 + 30*X^12 + 61*X^11 + 5*X^10 + 15*X^9 + 7*X^8 + 66*X^7 + 16*X^6 + 29*X^5 + 10*X^3 +
      11*X^2 + 22*X + 44,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s69 : XPow fSeventeenA4 20877764490536
    (15*X^33 + 5*X^32 + 3*X^31 + 58*X^30 + 5*X^29 + X^28 + 23*X^27 + 29*X^26 + 55*X^25 + 13*X^24 +
      63*X^23 + 22*X^22 + 48*X^21 + 12*X^20 + 51*X^19 + 6*X^18 + 47*X^17 + 11*X^16 + 55*X^15 +
      32*X^14 + 10*X^13 + 33*X^12 + 11*X^11 + 42*X^10 + 58*X^9 + 65*X^8 + 56*X^7 + 41*X^6 + 19*X^5 +
      20*X^4 + 23*X^3 + 46*X^2 + 49*X + 51) :=
  sq_step (by norm_num) pSeventeenA4s68 ⟨
    56*X^32 + 36*X^31 + 32*X^30 + 65*X^29 + 28*X^28 + 62*X^27 + 3*X^26 + 32*X^25 + 7*X^24 + 7*X^23 +
      25*X^22 + 27*X^21 + 16*X^20 + 25*X^19 + 34*X^18 + 64*X^17 + 2*X^16 + 61*X^15 + 22*X^14 +
      32*X^13 + 20*X^12 + 18*X^11 + 53*X^10 + 16*X^9 + 50*X^8 + 63*X^7 + 29*X^6 + 46*X^5 + 32*X^4 +
      36*X^3 + 66*X^2 + 25*X + 52,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s70 : XPow fSeventeenA4 20877764490537
    (22*X^33 + 10*X^32 + 17*X^31 + 16*X^30 + 27*X^29 + 18*X^28 + 53*X^27 + 11*X^26 + 14*X^25 + 62*X^24 +
      24*X^23 + 12*X^22 + 53*X^21 + 23*X^20 + 12*X^19 + 58*X^18 + 28*X^17 + 38*X^15 + 15*X^14 +
      63*X^13 + 45*X^12 + 15*X^11 + 10*X^10 + 55*X^9 + 41*X^8 + 65*X^7 + 59*X^5 + 7*X^4 + 2*X^3 +
      33*X^2 + 51*X + 39) :=
  mul_step (by norm_num) pSeventeenA4s69 pSeventeenA41 ⟨
    15,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s71 : XPow fSeventeenA4 41755528981074
    (63*X^33 + 24*X^32 + 65*X^31 + 57*X^30 + 45*X^29 + 52*X^28 + 34*X^27 + 25*X^26 + 58*X^25 + 10*X^24 +
      46*X^23 + 22*X^22 + 11*X^21 + 27*X^20 + 36*X^19 + 55*X^18 + 55*X^17 + 36*X^16 + 2*X^15 +
      14*X^14 + 41*X^13 + 53*X^12 + 64*X^11 + 47*X^10 + 15*X^9 + 8*X^8 + 54*X^7 + 60*X^6 + 35*X^5 +
      56*X^4 + 10*X^3 + 29*X^2 + 16*X + 48) :=
  sq_step (by norm_num) pSeventeenA4s70 ⟨
    15*X^32 + 55*X^31 + 24*X^30 + 33*X^29 + 34*X^27 + 5*X^26 + 31*X^25 + 59*X^24 + 2*X^23 + 36*X^22 +
      63*X^21 + 10*X^20 + 13*X^19 + 61*X^18 + 50*X^17 + 6*X^16 + 38*X^15 + 58*X^14 + 45*X^13 +
      22*X^12 + 3*X^11 + 4*X^10 + 14*X^9 + 41*X^8 + 22*X^7 + 56*X^6 + 63*X^5 + 31*X^4 + 23*X^3 +
      60*X^2 + 12*X + 21,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s72 : XPow fSeventeenA4 83511057962148
    (58*X^33 + 64*X^32 + 7*X^31 + 29*X^30 + 54*X^29 + 25*X^28 + 11*X^27 + 8*X^26 + 16*X^25 + 37*X^24 +
      61*X^23 + 20*X^22 + 2*X^21 + 49*X^20 + 37*X^19 + 19*X^18 + 54*X^17 + 19*X^16 + 12*X^15 +
      29*X^14 + 9*X^13 + 51*X^12 + 24*X^11 + 22*X^10 + 24*X^9 + 46*X^8 + 48*X^7 + 65*X^6 + 54*X^5 +
      17*X^4 + 2*X^3 + 53*X^2 + 31*X + 47) :=
  sq_step (by norm_num) pSeventeenA4s71 ⟨
    16*X^32 + 45*X^31 + 43*X^30 + 10*X^29 + 40*X^28 + 62*X^27 + 5*X^26 + 38*X^25 + 22*X^24 + 27*X^23 +
      59*X^22 + 39*X^21 + 9*X^20 + 47*X^19 + 23*X^18 + 63*X^17 + 24*X^16 + 55*X^15 + 48*X^13 +
      25*X^12 + 39*X^11 + 57*X^10 + 47*X^9 + 23*X^8 + 2*X^7 + 57*X^6 + 6*X^5 + 4*X^4 + 5*X^3 + X^2 +
      19*X + 39,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s73 : XPow fSeventeenA4 167022115924296
    (66*X^33 + 55*X^32 + 19*X^31 + 40*X^30 + 6*X^29 + 47*X^28 + 28*X^27 + 25*X^26 + 59*X^25 + 46*X^24 +
      42*X^23 + 31*X^22 + 54*X^21 + 60*X^20 + 27*X^19 + 34*X^18 + 2*X^17 + 25*X^16 + 9*X^15 +
      36*X^14 + 51*X^13 + 22*X^12 + 35*X^11 + 51*X^10 + 65*X^9 + 64*X^8 + 29*X^7 + 64*X^6 + 57*X^5 +
      45*X^4 + 10*X^3 + 14*X^2 + 52*X + 38) :=
  sq_step (by norm_num) pSeventeenA4s72 ⟨
    14*X^32 + 52*X^31 + 11*X^30 + 33*X^29 + 42*X^28 + 40*X^27 + 13*X^26 + 14*X^25 + 11*X^24 + 29*X^23 +
      18*X^22 + 32*X^21 + 44*X^20 + 30*X^19 + 8*X^18 + 12*X^17 + 26*X^16 + 40*X^15 + 23*X^14 +
      35*X^13 + 57*X^12 + 49*X^11 + 37*X^10 + 17*X^9 + 40*X^8 + 4*X^7 + 33*X^6 + 37*X^5 + 57*X^4 +
      11*X^3 + 33*X^2 + 64*X + 36,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s74 : XPow fSeventeenA4 334044231848592
    (19*X^33 + 46*X^32 + 42*X^31 + 27*X^30 + 16*X^29 + 34*X^28 + 26*X^27 + 52*X^26 + 16*X^24 + 11*X^23 +
      47*X^22 + 40*X^21 + 35*X^20 + 11*X^19 + 11*X^18 + 55*X^17 + 48*X^16 + 24*X^15 + 63*X^14 +
      11*X^13 + 51*X^12 + 23*X^11 + 53*X^10 + 19*X^9 + 6*X^8 + 29*X^7 + 62*X^6 + 48*X^5 + 41*X^4 +
      12*X^3 + 46*X^2 + 31*X + 55) :=
  sq_step (by norm_num) pSeventeenA4s73 ⟨
    X^32 + 43*X^31 + 48*X^30 + 36*X^29 + 59*X^28 + 26*X^27 + 42*X^26 + 43*X^25 + 47*X^24 + 12*X^22 +
      X^21 + 38*X^20 + 46*X^19 + 3*X^18 + 47*X^17 + 36*X^16 + 37*X^15 + 58*X^14 + 57*X^13 + 2*X^12 +
      5*X^11 + 30*X^10 + 12*X^9 + 13*X^8 + 39*X^7 + 56*X^6 + 4*X^5 + 9*X^4 + 40*X^3 + 12*X^2 + 2*X +
      43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s75 : XPow fSeventeenA4 668088463697184
    (54*X^33 + 34*X^32 + 12*X^31 + 3*X^29 + 25*X^28 + 63*X^27 + 60*X^26 + 2*X^25 + 27*X^24 + 12*X^23 +
      43*X^22 + 34*X^21 + 32*X^20 + 20*X^19 + 7*X^18 + 23*X^17 + 19*X^16 + 35*X^15 + 15*X^14 +
      23*X^13 + 42*X^12 + 5*X^11 + 10*X^10 + 66*X^9 + 15*X^8 + 17*X^7 + X^6 + 43*X^5 + 52*X^4 +
      14*X^3 + 41*X^2 + 23*X + 20) :=
  sq_step (by norm_num) pSeventeenA4s74 ⟨
    26*X^32 + 31*X^31 + 43*X^30 + 9*X^29 + 10*X^28 + 13*X^27 + 16*X^26 + 59*X^25 + 54*X^23 + 2*X^22 +
      24*X^21 + 14*X^20 + 65*X^19 + 41*X^18 + 23*X^17 + 65*X^16 + 13*X^15 + 2*X^14 + 9*X^13 +
      23*X^12 + 57*X^11 + 66*X^10 + 62*X^9 + X^8 + 27*X^7 + 61*X^6 + 23*X^5 + 44*X^4 + 30*X^3 +
      59*X^2 + 27*X + 9,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s76 : XPow fSeventeenA4 1336176927394368
    (5*X^33 + 45*X^32 + 53*X^31 + 36*X^30 + 61*X^29 + 26*X^28 + 35*X^27 + 48*X^26 + 48*X^25 + 51*X^24 +
      18*X^23 + 6*X^22 + 13*X^21 + 2*X^20 + 47*X^19 + 59*X^18 + 11*X^17 + 32*X^16 + 56*X^15 +
      24*X^14 + 17*X^13 + 51*X^12 + 8*X^11 + 51*X^10 + 55*X^9 + 15*X^8 + 19*X^7 + 24*X^6 + 60*X^5 +
      15*X^4 + 14*X^3 + 54*X^2 + 57*X + 59) :=
  sq_step (by norm_num) pSeventeenA4s75 ⟨
    35*X^32 + 49*X^31 + 27*X^30 + 10*X^29 + 4*X^28 + 55*X^27 + 54*X^26 + 41*X^25 + 8*X^24 + 24*X^23 +
      46*X^22 + 39*X^21 + 8*X^20 + 65*X^19 + 27*X^18 + 50*X^17 + 46*X^16 + 60*X^15 + 41*X^14 +
      7*X^13 + 55*X^12 + 47*X^11 + 20*X^10 + 24*X^9 + 10*X^8 + 38*X^7 + 44*X^6 + 13*X^5 + 43*X^4 +
      17*X^3 + 11*X^2 + 34*X + 8,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s77 : XPow fSeventeenA4 2672353854788736
    (45*X^33 + 60*X^32 + 6*X^31 + 59*X^30 + 9*X^29 + 65*X^28 + 53*X^27 + 6*X^26 + 44*X^25 + 22*X^24 +
      45*X^23 + 38*X^22 + 45*X^21 + 52*X^20 + 9*X^19 + 38*X^18 + 19*X^17 + 40*X^16 + 28*X^15 +
      15*X^14 + 25*X^13 + 22*X^12 + 57*X^11 + 52*X^10 + 33*X^9 + 48*X^8 + 64*X^7 + 65*X^6 + 63*X^5 +
      35*X^4 + 41*X^3 + 63*X^2 + 54*X + 53) :=
  sq_step (by norm_num) pSeventeenA4s76 ⟨
    25*X^32 + 54*X^31 + 64*X^30 + 54*X^29 + 28*X^28 + 8*X^27 + 38*X^26 + 40*X^25 + 55*X^24 + 52*X^23 +
      47*X^22 + 56*X^21 + 62*X^20 + 53*X^19 + 47*X^18 + 36*X^17 + 58*X^16 + 16*X^15 + 38*X^14 +
      32*X^13 + 21*X^12 + 53*X^11 + 12*X^10 + 22*X^9 + 66*X^8 + 12*X^7 + 22*X^6 + 24*X^5 + 52*X^4 +
      65*X^3 + 12*X^2 + 52*X + 37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s78 : XPow fSeventeenA4 5344707709577472
    (60*X^33 + 37*X^32 + 2*X^31 + 31*X^30 + 13*X^29 + 53*X^28 + 2*X^27 + 51*X^26 + 12*X^25 + 47*X^24 +
      41*X^23 + 65*X^22 + 19*X^21 + 45*X^20 + 2*X^19 + 8*X^18 + 52*X^17 + 32*X^16 + 3*X^15 + 30*X^14 +
      10*X^13 + 2*X^12 + 65*X^11 + 10*X^10 + 47*X^9 + 38*X^8 + 63*X^7 + 48*X^6 + 22*X^5 + 40*X^4 +
      14*X^3 + 54*X^2 + 32*X + 1) :=
  sq_step (by norm_num) pSeventeenA4s77 ⟨
    15*X^32 + 57*X^31 + 4*X^30 + 8*X^29 + 38*X^28 + 59*X^27 + 33*X^26 + 60*X^25 + 43*X^24 + 43*X^23 +
      58*X^22 + 18*X^20 + 8*X^19 + 57*X^18 + 63*X^17 + 66*X^16 + 33*X^15 + 13*X^14 + 16*X^13 +
      57*X^12 + 15*X^11 + 42*X^10 + 51*X^8 + 10*X^7 + 10*X^6 + 46*X^5 + 16*X^4 + 8*X^3 + 52*X^2 +
      63*X + 59,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s79 : XPow fSeventeenA4 5344707709577473
    (38*X^33 + 30*X^32 + X^31 + 57*X^30 + 23*X^29 + 49*X^28 + 13*X^27 + 37*X^26 + 51*X^25 + 37*X^24 +
      6*X^23 + 9*X^22 + 8*X^21 + 24*X^20 + 32*X^19 + 29*X^18 + 33*X^17 + 51*X^16 + 54*X^15 + 30*X^14 +
      55*X^13 + 36*X^11 + 56*X^10 + 65*X^9 + 3*X^8 + 10*X^7 + 13*X^6 + 62*X^5 + 17*X^4 + 12*X^3 +
      35*X^2 + X + 22) :=
  mul_step (by norm_num) pSeventeenA4s78 pSeventeenA41 ⟨
    60,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s80 : XPow fSeventeenA4 10689415419154946
    (6*X^33 + 65*X^32 + 23*X^31 + 7*X^30 + 30*X^29 + 36*X^28 + 23*X^27 + 48*X^26 + 60*X^25 + 12*X^24 +
      39*X^23 + 66*X^22 + 17*X^20 + 33*X^19 + 60*X^18 + 9*X^17 + 64*X^16 + 52*X^15 + 32*X^14 +
      58*X^13 + 16*X^12 + 4*X^11 + 12*X^10 + 24*X^9 + 50*X^8 + 53*X^7 + 29*X^6 + 64*X^5 + 55*X^4 +
      21*X^3 + 17*X^2 + 7*X + 26) :=
  sq_step (by norm_num) pSeventeenA4s79 ⟨
    37*X^32 + 35*X^31 + 19*X^30 + 5*X^29 + 23*X^28 + 27*X^27 + X^26 + 49*X^25 + 41*X^24 + 62*X^23 +
      22*X^22 + 51*X^21 + 24*X^20 + 27*X^19 + 21*X^18 + 9*X^17 + 17*X^16 + 62*X^15 + 37*X^14 +
      4*X^13 + 43*X^12 + 21*X^11 + 29*X^10 + 48*X^9 + 65*X^8 + 49*X^7 + 36*X^6 + 23*X^5 + 53*X^4 +
      24*X^3 + 24*X^2 + 27*X + 30,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s81 : XPow fSeventeenA4 10689415419154947
    (45*X^33 + 66*X^32 + 4*X^31 + 21*X^30 + 33*X^29 + 21*X^28 + 4*X^27 + 29*X^26 + 66*X^25 + 52*X^24 +
      40*X^23 + 66*X^22 + 20*X^21 + 62*X^20 + 49*X^19 + 44*X^17 + 30*X^16 + 21*X^15 + 60*X^14 +
      28*X^13 + 31*X^12 + 28*X^11 + 45*X^10 + 46*X^9 + 47*X^8 + 52*X^7 + 43*X^6 + 17*X^5 + 28*X^4 +
      53*X^3 + 14*X^2 + 26*X + 29) :=
  mul_step (by norm_num) pSeventeenA4s80 pSeventeenA41 ⟨
    6,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s82 : XPow fSeventeenA4 21378830838309894
    (20*X^33 + 43*X^32 + 43*X^31 + 14*X^30 + 7*X^29 + 47*X^28 + 63*X^27 + 60*X^26 + 18*X^25 + 48*X^24 +
      27*X^23 + 12*X^22 + 17*X^21 + 16*X^20 + 20*X^19 + 60*X^18 + 59*X^17 + 40*X^16 + 40*X^15 +
      26*X^14 + 29*X^13 + 66*X^12 + 49*X^11 + 24*X^10 + 14*X^9 + 34*X^8 + 24*X^7 + 6*X^6 + 32*X^5 +
      48*X^4 + 59*X^3 + 11*X^2 + 36*X + 60) :=
  sq_step (by norm_num) pSeventeenA4s81 ⟨
    15*X^32 + 61*X^31 + 53*X^30 + 58*X^29 + 29*X^28 + 8*X^27 + 44*X^26 + 34*X^25 + 31*X^24 + 31*X^23 +
      56*X^22 + 40*X^21 + 59*X^20 + 27*X^19 + 50*X^18 + 6*X^17 + 46*X^16 + 26*X^15 + 25*X^14 +
      4*X^13 + 20*X^12 + 51*X^11 + 57*X^10 + 60*X^9 + 29*X^8 + 28*X^7 + 28*X^6 + 44*X^5 + 9*X^4 +
      9*X^3 + 63*X^2 + 42*X + 14,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s83 : XPow fSeventeenA4 42757661676619788
    (41*X^33 + 61*X^32 + 60*X^31 + 39*X^30 + 48*X^29 + 21*X^28 + 50*X^27 + 13*X^26 + 14*X^25 + 48*X^24 +
      30*X^23 + 39*X^22 + 43*X^21 + 56*X^20 + 44*X^19 + 3*X^18 + 56*X^17 + 59*X^16 + 38*X^15 +
      49*X^14 + 50*X^13 + 17*X^12 + 22*X^11 + 20*X^10 + 30*X^9 + 34*X^7 + 59*X^6 + 5*X^5 + 25*X^4 +
      65*X^3 + 10*X^2 + 15*X + 27) :=
  sq_step (by norm_num) pSeventeenA4s82 ⟨
    65*X^32 + 7*X^31 + 25*X^30 + 16*X^29 + 19*X^28 + 8*X^27 + 40*X^26 + 65*X^25 + 36*X^24 + 23*X^23 +
      50*X^22 + 24*X^21 + 52*X^20 + 7*X^19 + 50*X^18 + 47*X^17 + 14*X^16 + 22*X^15 + 20*X^14 +
      30*X^13 + 10*X^12 + 32*X^11 + 50*X^10 + 14*X^9 + 5*X^8 + 42*X^7 + 9*X^5 + 40*X^4 + 61*X^3 +
      9*X^2 + 45*X + 7,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s84 : XPow fSeventeenA4 42757661676619789
    (36*X^33 + 30*X^32 + 52*X^31 + 20*X^30 + 34*X^29 + 14*X^28 + 25*X^27 + 59*X^26 + 15*X^25 + 63*X^24 +
      40*X^23 + 25*X^22 + 43*X^21 + 30*X^20 + 6*X^19 + 28*X^18 + 34*X^17 + 44*X^16 + 52*X^15 +
      19*X^14 + 32*X^13 + 39*X^12 + 40*X^11 + 6*X^10 + 62*X^9 + 60*X^8 + 4*X^7 + 29*X^6 + 11*X^5 +
      57*X^4 + 55*X^3 + 7*X^2 + 27*X + 53) :=
  mul_step (by norm_num) pSeventeenA4s83 pSeventeenA41 ⟨
    41,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s85 : XPow fSeventeenA4 85515323353239578
    (7*X^33 + 6*X^32 + 15*X^31 + 29*X^30 + 30*X^29 + 19*X^28 + 65*X^27 + 40*X^26 + 22*X^25 + 65*X^24 +
      61*X^23 + 13*X^22 + 25*X^21 + 17*X^20 + 64*X^19 + 43*X^18 + 59*X^17 + 20*X^16 + 30*X^15 +
      24*X^14 + 60*X^13 + 13*X^12 + 33*X^11 + 27*X^10 + 56*X^9 + 13*X^8 + 13*X^7 + 40*X^6 + 25*X^5 +
      57*X^4 + 42*X^3 + 10*X^2 + 7*X + 57) :=
  sq_step (by norm_num) pSeventeenA4s84 ⟨
    23*X^32 + 51*X^31 + 27*X^30 + 20*X^28 + 13*X^27 + 14*X^26 + 4*X^25 + 65*X^24 + 47*X^23 + 31*X^22 +
      18*X^21 + 5*X^20 + 23*X^19 + 31*X^18 + 16*X^17 + 57*X^16 + 25*X^15 + 39*X^14 + 39*X^13 + X^12 +
      8*X^11 + 16*X^10 + 10*X^9 + 16*X^8 + 40*X^7 + 66*X^6 + 38*X^5 + 45*X^4 + 12*X^3 + 65*X^2 +
      10*X + 29,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s86 : XPow fSeventeenA4 171030646706479156
    (53*X^33 + 48*X^32 + 59*X^31 + 34*X^30 + 28*X^29 + 47*X^28 + 51*X^27 + 49*X^26 + 18*X^25 + 3*X^24 +
      51*X^23 + 55*X^22 + 11*X^21 + 31*X^20 + 45*X^19 + 56*X^18 + 29*X^17 + 41*X^16 + 62*X^15 +
      32*X^14 + 36*X^13 + 22*X^12 + 33*X^11 + 61*X^10 + 35*X^9 + 2*X^8 + 55*X^7 + 9*X^6 + 38*X^5 +
      32*X^4 + 51*X^3 + 37*X^2 + 56*X + 28) :=
  sq_step (by norm_num) pSeventeenA4s85 ⟨
    49*X^32 + 10*X^31 + 39*X^30 + 23*X^29 + 23*X^28 + 40*X^27 + 61*X^26 + 11*X^25 + 45*X^24 + 4*X^23 +
      8*X^22 + 25*X^21 + 47*X^20 + 43*X^19 + 51*X^18 + 5*X^17 + 32*X^16 + 19*X^15 + 4*X^14 + 16*X^13 +
      62*X^12 + 53*X^11 + 9*X^10 + 51*X^9 + 49*X^8 + 64*X^7 + 62*X^6 + 65*X^5 + 30*X^4 + 50*X^3 +
      55*X^2 + 29*X + 29,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s87 : XPow fSeventeenA4 342061293412958312
    (49*X^33 + 8*X^32 + 36*X^31 + 66*X^30 + 52*X^29 + 32*X^28 + 23*X^27 + 10*X^26 + 6*X^25 + X^23 +
      26*X^22 + 43*X^21 + 24*X^20 + 47*X^19 + 25*X^18 + 47*X^17 + 56*X^16 + 37*X^15 + 25*X^14 +
      43*X^13 + 29*X^12 + 59*X^11 + 36*X^10 + 9*X^9 + 35*X^8 + 39*X^7 + 45*X^6 + 40*X^5 + 48*X^4 +
      53*X^3 + 10*X^2 + 58*X + 51) :=
  sq_step (by norm_num) pSeventeenA4s86 ⟨
    62*X^32 + 35*X^31 + 64*X^30 + 62*X^29 + 39*X^28 + 33*X^27 + 22*X^26 + 52*X^25 + 11*X^24 + 57*X^23 +
      46*X^22 + 37*X^21 + 53*X^20 + 12*X^19 + 36*X^18 + 5*X^16 + 56*X^15 + 20*X^14 + 49*X^13 +
      15*X^12 + 60*X^11 + 31*X^10 + 65*X^9 + 57*X^8 + 6*X^7 + 38*X^6 + 59*X^5 + 54*X^4 + 60*X^3 +
      4*X^2 + 17*X + 17,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s88 : XPow fSeventeenA4 342061293412958313
    (X^33 + 41*X^32 + 8*X^31 + 12*X^30 + 41*X^29 + 29*X^28 + 8*X^27 + 32*X^26 + 39*X^25 + 29*X^24 +
      37*X^23 + 46*X^22 + 15*X^21 + 27*X^20 + 58*X^19 + 7*X^18 + 49*X^17 + 36*X^16 + 58*X^15 +
      37*X^14 + 60*X^13 + 45*X^12 + 55*X^11 + 13*X^10 + 47*X^9 + 57*X^8 + 43*X^7 + 36*X^6 + 28*X^5 +
      32*X^4 + 36*X^3 + 37*X^2 + 51*X + 47) :=
  mul_step (by norm_num) pSeventeenA4s87 pSeventeenA41 ⟨
    49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s89 : XPow fSeventeenA4 684122586825916626
    (34*X^33 + 66*X^32 + 26*X^31 + 28*X^30 + 29*X^29 + 51*X^28 + 15*X^27 + 9*X^26 + 10*X^25 + 57*X^24 +
      37*X^23 + 30*X^22 + 11*X^21 + 28*X^20 + 21*X^19 + 52*X^18 + 23*X^17 + 9*X^16 + 28*X^15 +
      7*X^14 + 20*X^13 + 65*X^12 + 16*X^11 + 61*X^10 + 44*X^9 + 64*X^8 + 39*X^7 + 43*X^6 + 10*X^5 +
      62*X^4 + 3*X^3 + 56*X^2 + 45*X + 46) :=
  sq_step (by norm_num) pSeventeenA4s88 ⟨
    X^32 + 34*X^31 + 61*X^30 + 61*X^29 + 50*X^28 + 15*X^27 + 13*X^26 + 23*X^25 + 34*X^24 + 62*X^23 +
      11*X^22 + 45*X^21 + 65*X^20 + 42*X^19 + 32*X^18 + 7*X^17 + 31*X^16 + 45*X^15 + 28*X^14 +
      64*X^13 + 6*X^12 + 38*X^11 + 45*X^10 + 44*X^9 + 59*X^8 + 16*X^7 + 29*X^6 + 18*X^5 + 30*X^4 +
      21*X^3 + 40*X^2 + 34*X + 3,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s90 : XPow fSeventeenA4 684122586825916627
    (42*X^33 + 24*X^32 + 11*X^31 + 45*X^30 + 34*X^29 + 26*X^28 + 50*X^27 + 13*X^26 + 28*X^25 + 66*X^24 +
      39*X^23 + 50*X^22 + 45*X^21 + 29*X^20 + 12*X^19 + 39*X^18 + 52*X^17 + 15*X^16 + 34*X^15 +
      9*X^14 + 66*X^13 + 35*X^12 + 40*X^11 + 29*X^10 + 19*X^9 + 5*X^8 + 17*X^7 + 25*X^6 + 3*X^5 +
      65*X^4 + 59*X^3 + 40*X^2 + 46*X + 8) :=
  mul_step (by norm_num) pSeventeenA4s89 pSeventeenA41 ⟨
    34,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s91 : XPow fSeventeenA4 1368245173651833254
    (2*X^33 + 12*X^32 + 4*X^31 + 32*X^30 + 47*X^29 + 18*X^28 + 47*X^27 + 6*X^26 + 9*X^25 + 16*X^24 +
      7*X^23 + 53*X^22 + 27*X^21 + 21*X^20 + 15*X^19 + 26*X^18 + 36*X^17 + 48*X^16 + 41*X^15 +
      8*X^14 + 12*X^13 + 43*X^12 + 50*X^11 + 4*X^10 + 12*X^9 + 5*X^8 + 19*X^7 + 18*X^6 + 29*X^5 +
      19*X^4 + 58*X^3 + 57*X^2 + 45*X + 41) :=
  sq_step (by norm_num) pSeventeenA4s90 ⟨
    22*X^32 + 22*X^31 + 21*X^30 + 52*X^29 + 34*X^28 + 64*X^27 + 35*X^26 + 34*X^25 + 49*X^24 + 50*X^23 +
      40*X^22 + 63*X^21 + 22*X^20 + 30*X^19 + 36*X^18 + 50*X^17 + 25*X^16 + 44*X^15 + 30*X^14 +
      50*X^13 + 52*X^12 + 27*X^11 + 28*X^10 + 20*X^9 + 56*X^8 + 15*X^7 + 18*X^6 + 13*X^5 + 8*X^4 +
      64*X^3 + 11*X^2 + 28*X + 53,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s92 : XPow fSeventeenA4 2736490347303666508
    (25*X^33 + 26*X^32 + 25*X^31 + 54*X^30 + 6*X^29 + 26*X^28 + 23*X^27 + 37*X^26 + 32*X^25 + 61*X^24 +
      54*X^23 + 38*X^22 + 52*X^21 + 36*X^20 + 43*X^19 + 61*X^18 + 16*X^17 + 63*X^16 + 39*X^15 +
      47*X^14 + 65*X^13 + 56*X^12 + 53*X^11 + 47*X^10 + 15*X^9 + 47*X^8 + 7*X^7 + 56*X^6 + 56*X^5 +
      50*X^4 + 44*X^3 + 7*X^2 + 39*X + 66) :=
  sq_step (by norm_num) pSeventeenA4s91 ⟨
    4*X^32 + 57*X^31 + 21*X^30 + 58*X^29 + 46*X^28 + 57*X^27 + 37*X^26 + 43*X^25 + 5*X^24 + 26*X^23 +
      55*X^22 + 38*X^21 + 25*X^20 + 24*X^19 + 62*X^18 + 20*X^17 + 21*X^16 + 63*X^15 + 31*X^14 +
      38*X^13 + 49*X^12 + 26*X^11 + 30*X^10 + 22*X^9 + 52*X^8 + 31*X^7 + 39*X^6 + 66*X^5 + 16*X^4 +
      37*X^3 + 51*X^2 + 44*X + 54,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s93 : XPow fSeventeenA4 5472980694607333016
    (45*X^33 + 7*X^32 + 44*X^31 + 41*X^30 + 63*X^29 + 37*X^28 + 62*X^27 + 13*X^26 + 60*X^25 + 19*X^24 +
      4*X^23 + 37*X^22 + 50*X^21 + 8*X^20 + 32*X^19 + 17*X^18 + 6*X^17 + 9*X^16 + 65*X^15 + 28*X^14 +
      57*X^13 + 28*X^12 + 34*X^11 + 62*X^10 + 58*X^9 + 38*X^8 + 28*X^7 + 47*X^6 + 63*X^5 + 5*X^4 +
      34*X^3 + 62*X^2 + 18*X) :=
  sq_step (by norm_num) pSeventeenA4s92 ⟨
    22*X^32 + 43*X^31 + 42*X^30 + 59*X^29 + 42*X^28 + 54*X^27 + 45*X^26 + 45*X^25 + 26*X^24 + 41*X^23 +
      19*X^22 + 30*X^21 + 33*X^20 + X^19 + 63*X^18 + 44*X^17 + 65*X^16 + 57*X^15 + 46*X^14 + 31*X^13 +
      X^12 + 13*X^11 + 33*X^10 + 57*X^9 + 2*X^8 + 53*X^7 + 3*X^6 + 19*X^5 + 11*X^4 + 27*X^3 + 18*X^2 +
      6*X + 46,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s94 : XPow fSeventeenA4 5472980694607333017
    (58*X^33 + 65*X^32 + 52*X^31 + 29*X^30 + 48*X^29 + 47*X^28 + 18*X^27 + 62*X^26 + 22*X^25 + X^24 +
      43*X^23 + 9*X^22 + 64*X^21 + 15*X^20 + 35*X^19 + 39*X^18 + 60*X^17 + 34*X^16 + 46*X^15 +
      5*X^14 + 51*X^13 + 2*X^12 + 48*X^11 + 48*X^10 + 8*X^9 + 50*X^8 + 52*X^7 + 6*X^6 + 55*X^5 +
      53*X^4 + 64*X^3 + 37*X^2 + 50) :=
  mul_step (by norm_num) pSeventeenA4s93 pSeventeenA41 ⟨
    45,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s95 : XPow fSeventeenA4 10945961389214666034
    (24*X^33 + 64*X^32 + 63*X^31 + 55*X^30 + 59*X^29 + 60*X^28 + 30*X^27 + 28*X^26 + 10*X^25 + 4*X^24 +
      40*X^23 + 9*X^22 + 15*X^21 + 21*X^20 + 55*X^19 + 35*X^18 + 36*X^17 + 37*X^16 + 9*X^15 +
      54*X^14 + 17*X^13 + 21*X^12 + 53*X^11 + 15*X^10 + 47*X^8 + 40*X^7 + 51*X^6 + 4*X^5 + 40*X^4 +
      43*X^3 + 47*X^2 + 62*X + 55) :=
  sq_step (by norm_num) pSeventeenA4s94 ⟨
    14*X^32 + 34*X^31 + 60*X^30 + 66*X^29 + 20*X^28 + 63*X^27 + 40*X^26 + 39*X^25 + 49*X^24 + 55*X^23 +
      26*X^22 + 39*X^21 + 47*X^20 + 13*X^19 + 60*X^17 + 45*X^16 + 32*X^15 + 33*X^14 + 42*X^13 +
      22*X^12 + 34*X^11 + 62*X^10 + 43*X^9 + 16*X^8 + 31*X^7 + 12*X^6 + 42*X^5 + 6*X^4 + 44*X^3 +
      63*X^2 + 29*X + 44,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s96 : XPow fSeventeenA4 10945961389214666035
    (51*X^33 + 34*X^32 + 43*X^31 + 23*X^30 + 48*X^29 + 22*X^28 + 53*X^27 + 20*X^26 + 19*X^25 + 25*X^24 +
      39*X^23 + 11*X^22 + 33*X^21 + 37*X^20 + 58*X^19 + 24*X^17 + 55*X^16 + 10*X^15 + 25*X^14 +
      2*X^13 + 27*X^12 + 12*X^11 + 17*X^10 + 31*X^9 + 16*X^8 + 9*X^7 + 54*X^6 + 22*X^5 + 4*X^4 +
      57*X^3 + 23*X^2 + 55*X + 49) :=
  mul_step (by norm_num) pSeventeenA4s95 pSeventeenA41 ⟨
    24,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s97 : XPow fSeventeenA4 21891922778429332070
    (4*X^33 + 44*X^32 + 18*X^31 + 45*X^30 + 59*X^29 + 20*X^28 + 55*X^27 + 58*X^26 + 7*X^25 + 59*X^24 +
      56*X^23 + 50*X^22 + 29*X^21 + 18*X^20 + 24*X^19 + 53*X^18 + 30*X^17 + 39*X^16 + 7*X^15 +
      53*X^13 + 29*X^12 + 47*X^11 + 56*X^10 + 66*X^9 + 54*X^8 + 31*X^7 + 53*X^6 + 38*X^5 + 38*X^4 +
      46*X^3 + 53*X^2 + 37*X + 61) :=
  sq_step (by norm_num) pSeventeenA4s96 ⟨
    55*X^32 + 24*X^31 + 16*X^30 + 57*X^29 + 21*X^28 + 48*X^27 + 32*X^26 + 19*X^25 + 35*X^24 + 39*X^23 +
      14*X^22 + 61*X^21 + 52*X^20 + 36*X^19 + 42*X^18 + 4*X^17 + 38*X^16 + 18*X^14 + 58*X^13 +
      44*X^12 + 47*X^11 + 60*X^10 + 6*X^9 + 30*X^8 + 27*X^7 + 26*X^6 + 24*X^5 + 41*X^4 + 59*X^3 +
      7*X^2 + 13*X + 38,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s98 : XPow fSeventeenA4 21891922778429332071
    (53*X^33 + 2*X^32 + 43*X^31 + 53*X^30 + 18*X^29 + 9*X^28 + 51*X^27 + 31*X^26 + 28*X^25 + 20*X^24 +
      55*X^23 + 6*X^22 + 20*X^21 + 21*X^20 + X^19 + 24*X^18 + 48*X^17 + 37*X^16 + 15*X^15 + 32*X^14 +
      37*X^13 + 65*X^12 + 22*X^11 + 13*X^10 + 29*X^9 + 27*X^8 + 46*X^7 + 24*X^6 + 35*X^5 + 6*X^4 +
      10*X^3 + 64*X^2 + 61*X + 64) :=
  mul_step (by norm_num) pSeventeenA4s97 pSeventeenA41 ⟨
    4,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s99 : XPow fSeventeenA4 43783845556858664142
    (27*X^33 + 46*X^32 + 14*X^31 + 24*X^30 + 15*X^29 + 7*X^28 + X^27 + 30*X^26 + 32*X^25 + 49*X^24 +
      20*X^23 + 23*X^22 + 64*X^21 + 14*X^20 + 15*X^19 + 46*X^18 + 6*X^17 + 47*X^16 + 31*X^15 +
      27*X^14 + X^13 + 58*X^12 + 65*X^11 + 34*X^10 + 33*X^9 + 66*X^8 + 47*X^7 + 29*X^6 + 41*X^5 +
      35*X^4 + 49*X^3 + 28*X^2 + 28*X + 27) :=
  sq_step (by norm_num) pSeventeenA4s98 ⟨
    62*X^32 + 50*X^31 + 38*X^30 + 50*X^29 + 26*X^28 + 58*X^27 + 61*X^26 + 44*X^25 + 24*X^24 + 6*X^23 +
      65*X^22 + 30*X^21 + 48*X^20 + 5*X^19 + 38*X^18 + 35*X^17 + 51*X^16 + 47*X^15 + 47*X^14 +
      12*X^13 + 27*X^12 + 66*X^11 + 40*X^10 + 6*X^9 + 5*X^8 + 54*X^7 + 56*X^6 + 59*X^5 + 27*X^4 +
      30*X^3 + 42*X^2 + 33*X + 43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s100 : XPow fSeventeenA4 87567691113717328284
    (7*X^33 + 2*X^32 + 45*X^31 + 37*X^30 + 37*X^29 + 21*X^28 + 47*X^27 + 36*X^26 + 12*X^25 + 61*X^24 +
      33*X^23 + 4*X^22 + 55*X^21 + 49*X^20 + 26*X^19 + 43*X^18 + 6*X^17 + 62*X^16 + 38*X^15 +
      40*X^14 + 24*X^13 + 18*X^12 + 46*X^11 + 29*X^10 + 58*X^9 + 17*X^8 + 48*X^7 + 8*X^6 + 15*X^5 +
      44*X^4 + 32*X^3 + 35*X^2 + 39) :=
  sq_step (by norm_num) pSeventeenA4s99 ⟨
    59*X^32 + 54*X^31 + 44*X^30 + 59*X^29 + 57*X^28 + 29*X^27 + 10*X^26 + 13*X^25 + 17*X^24 + 47*X^23 +
      28*X^22 + 51*X^21 + 53*X^20 + 46*X^19 + 56*X^18 + 66*X^17 + 62*X^16 + 43*X^15 + 19*X^14 +
      20*X^13 + 47*X^12 + 16*X^11 + 38*X^10 + 22*X^9 + 18*X^8 + 53*X^7 + 33*X^6 + 44*X^5 + 7*X^4 +
      59*X^3 + 61*X^2 + 6*X + 49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s101 : XPow fSeventeenA4 175135382227434656568
    (23*X^33 + 54*X^32 + 33*X^31 + 7*X^30 + 32*X^29 + 19*X^28 + 45*X^27 + 3*X^26 + 56*X^25 + 47*X^23 +
      27*X^22 + X^21 + 8*X^20 + 47*X^19 + 53*X^18 + 56*X^17 + 47*X^16 + 12*X^15 + 47*X^14 + 5*X^13 +
      3*X^12 + 40*X^11 + 29*X^10 + 56*X^8 + 56*X^7 + 50*X^6 + 44*X^5 + 48*X^4 + 41*X^3 + 53*X^2 + 27) :=
  sq_step (by norm_num) pSeventeenA4s100 ⟨
    49*X^32 + 21*X^31 + 33*X^30 + 44*X^29 + 28*X^28 + 2*X^27 + 65*X^26 + 43*X^25 + 46*X^24 + 31*X^23 +
      27*X^22 + 59*X^21 + 15*X^20 + 8*X^19 + 52*X^18 + 41*X^17 + 30*X^16 + 55*X^15 + 57*X^14 +
      30*X^13 + 55*X^12 + 14*X^11 + 33*X^10 + 18*X^9 + 46*X^8 + 19*X^7 + 50*X^6 + 53*X^5 + 45*X^4 +
      25*X^3 + 35*X^2 + 49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s102 : XPow fSeventeenA4 350270764454869313136
    (2*X^33 + 54*X^32 + 19*X^31 + 59*X^30 + 56*X^29 + 3*X^28 + 48*X^27 + 59*X^26 + 12*X^25 + 60*X^24 +
      54*X^23 + 41*X^22 + 40*X^21 + 39*X^20 + 54*X^19 + 20*X^18 + 25*X^17 + 22*X^16 + 4*X^15 +
      24*X^14 + 7*X^13 + 50*X^12 + 33*X^11 + 29*X^10 + 22*X^9 + 12*X^8 + 33*X^7 + 14*X^6 + 19*X^5 +
      18*X^4 + 54*X^3 + 63*X^2 + 64*X + 66) :=
  sq_step (by norm_num) pSeventeenA4s101 ⟨
    60*X^32 + 6*X^31 + 20*X^30 + 58*X^29 + 25*X^28 + 28*X^27 + 40*X^25 + 53*X^24 + 15*X^23 + 50*X^22 +
      58*X^21 + 58*X^20 + 14*X^19 + 26*X^18 + 62*X^17 + 32*X^16 + 10*X^15 + 55*X^14 + 38*X^13 +
      28*X^12 + 14*X^11 + 62*X^10 + 51*X^9 + 34*X^8 + 51*X^7 + 15*X^6 + 44*X^5 + 3*X^4 + 5*X^3 +
      30*X^2 + 4*X + 13,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s103 : XPow fSeventeenA4 700541528909738626272
    (17*X^33 + 62*X^32 + 13*X^31 + 60*X^30 + 19*X^29 + 12*X^28 + 59*X^27 + 43*X^26 + 10*X^25 + 41*X^24 +
      11*X^23 + 62*X^22 + 54*X^21 + 49*X^20 + 4*X^19 + 12*X^18 + 35*X^17 + 27*X^16 + 26*X^15 +
      58*X^14 + 27*X^13 + 61*X^12 + 23*X^11 + 14*X^10 + 14*X^9 + 48*X^8 + 32*X^7 + 38*X^6 + 41*X^5 +
      6*X^4 + 34*X^3 + 7*X^2 + 25*X + 61) :=
  sq_step (by norm_num) pSeventeenA4s102 ⟨
    4*X^32 + 24*X^31 + 15*X^30 + 63*X^29 + 36*X^28 + 12*X^27 + 33*X^25 + 19*X^24 + 37*X^23 + 34*X^22 +
      43*X^21 + 46*X^20 + 41*X^19 + 15*X^18 + 24*X^17 + 37*X^16 + 25*X^14 + 28*X^13 + 11*X^12 +
      17*X^11 + 45*X^10 + 63*X^9 + 6*X^8 + 33*X^7 + 15*X^6 + 2*X^5 + 45*X^4 + 2*X^3 + 8*X^2 + 64*X +
      54,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s104 : XPow fSeventeenA4 700541528909738626273
    (50*X^33 + 12*X^32 + 18*X^31 + 27*X^30 + 37*X^29 + 31*X^28 + 30*X^27 + 45*X^26 + 60*X^25 + 59*X^24 +
      33*X^23 + 40*X^22 + 24*X^21 + 8*X^20 + 59*X^19 + 43*X^18 + 15*X^17 + 53*X^16 + 38*X^15 +
      55*X^14 + 28*X^13 + 66*X^12 + 37*X^11 + 40*X^10 + 59*X^9 + 15*X^8 + 25*X^7 + 15*X^6 + 10*X^5 +
      65*X^4 + 42*X^3 + 56*X^2 + 61*X + 4) :=
  mul_step (by norm_num) pSeventeenA4s103 pSeventeenA41 ⟨
    17,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s105 : XPow fSeventeenA4 1401083057819477252546
    (34*X^33 + 55*X^32 + 43*X^31 + 52*X^30 + 30*X^29 + 51*X^28 + 46*X^27 + 26*X^26 + 29*X^25 + 58*X^24 +
      46*X^23 + 20*X^22 + 9*X^21 + 30*X^20 + 13*X^19 + 56*X^18 + 37*X^17 + 54*X^16 + 41*X^15 +
      13*X^14 + 49*X^13 + 35*X^12 + 12*X^11 + 24*X^10 + 54*X^9 + 31*X^8 + 17*X^7 + 66*X^6 + 32*X^5 +
      24*X^4 + 42*X^3 + 26*X^2 + 35*X + 11) :=
  sq_step (by norm_num) pSeventeenA4s104 ⟨
    21*X^32 + 58*X^31 + 14*X^30 + 40*X^29 + 56*X^28 + 31*X^27 + 63*X^26 + 49*X^25 + 35*X^24 + 57*X^23 +
      34*X^22 + 66*X^21 + 37*X^20 + 29*X^19 + 9*X^18 + 10*X^17 + 59*X^16 + 5*X^15 + 29*X^14 +
      53*X^13 + 43*X^12 + 28*X^11 + 26*X^10 + 50*X^9 + 3*X^8 + 15*X^7 + 11*X^6 + 11*X^5 + 46*X^4 +
      5*X^3 + 23*X^2 + X + 29,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s106 : XPow fSeventeenA4 2802166115638954505092
    (24*X^33 + 28*X^32 + 39*X^31 + 9*X^30 + 30*X^29 + 19*X^28 + 44*X^27 + 52*X^26 + 4*X^25 + 64*X^24 +
      49*X^23 + 34*X^22 + 34*X^21 + 23*X^20 + 4*X^19 + 3*X^18 + 63*X^17 + 64*X^16 + 59*X^15 +
      43*X^14 + 5*X^13 + 11*X^12 + 23*X^11 + 48*X^10 + 29*X^9 + 19*X^8 + 6*X^7 + 47*X^6 + 49*X^5 +
      53*X^4 + 46*X^3 + 45*X^2 + 23*X + 42) :=
  sq_step (by norm_num) pSeventeenA4s105 ⟨
    17*X^32 + 43*X^31 + 65*X^30 + 41*X^29 + 31*X^28 + 2*X^27 + 41*X^25 + 58*X^24 + 20*X^23 + 38*X^22 +
      8*X^21 + 18*X^20 + 14*X^18 + 6*X^17 + 52*X^16 + 34*X^15 + 14*X^14 + 41*X^13 + 10*X^12 +
      60*X^11 + 22*X^10 + 51*X^9 + 49*X^8 + 66*X^7 + 25*X^6 + 54*X^5 + 64*X^4 + 4*X^3 + X^2 + 58*X +
      16,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s107 : XPow fSeventeenA4 2802166115638954505093
    (15*X^33 + 10*X^32 + 64*X^31 + 61*X^30 + 7*X^29 + 36*X^28 + 10*X^27 + 14*X^26 + 12*X^25 + 34*X^24 +
      64*X^23 + 30*X^22 + 35*X^21 + 53*X^20 + 26*X^19 + 27*X^18 + 51*X^17 + 38*X^16 + 66*X^15 +
      13*X^14 + 59*X^13 + 64*X^12 + 45*X^11 + 46*X^10 + 3*X^9 + 49*X^8 + 5*X^7 + 32*X^6 + 35*X^5 +
      7*X^4 + 55*X^3 + 51*X^2 + 42*X + 49) :=
  mul_step (by norm_num) pSeventeenA4s106 pSeventeenA41 ⟨
    24,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s108 : XPow fSeventeenA4 5604332231277909010186
    (9*X^32 + 45*X^31 + 27*X^30 + 60*X^29 + 54*X^28 + 34*X^27 + 7*X^26 + 11*X^25 + 31*X^24 + 61*X^23 +
      35*X^22 + 6*X^20 + 39*X^19 + 11*X^18 + 35*X^17 + 60*X^16 + 7*X^15 + 7*X^14 + 16*X^13 + 16*X^12 +
      21*X^11 + 46*X^10 + 63*X^9 + 30*X^8 + X^7 + 34*X^6 + 59*X^5 + 17*X^4 + 48*X^3 + 50*X^2 + 41*X +
      47) :=
  sq_step (by norm_num) pSeventeenA4s107 ⟨
    24*X^32 + 19*X^31 + 7*X^30 + 6*X^29 + 39*X^28 + 53*X^27 + 25*X^26 + 56*X^25 + 48*X^24 + 57*X^23 +
      46*X^22 + 58*X^21 + 41*X^20 + 16*X^19 + 42*X^18 + 11*X^17 + 13*X^16 + 55*X^15 + 41*X^14 +
      16*X^13 + 6*X^12 + 21*X^11 + 45*X^10 + 19*X^9 + X^8 + 24*X^7 + 11*X^6 + 57*X^5 + 25*X^4 +
      12*X^3 + 57*X^2 + 51*X + 12,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s109 : XPow fSeventeenA4 11208664462555818020372
    (52*X^33 + 15*X^32 + 24*X^31 + 24*X^30 + 56*X^29 + 36*X^28 + 47*X^27 + 13*X^26 + 50*X^25 + 65*X^24 +
      58*X^23 + 31*X^22 + 60*X^21 + 43*X^20 + 17*X^19 + 8*X^18 + 52*X^17 + 16*X^16 + 43*X^15 +
      36*X^14 + 45*X^13 + 9*X^12 + 10*X^11 + 26*X^10 + 59*X^9 + 4*X^8 + 52*X^7 + 10*X^6 + 34*X^5 +
      62*X^4 + 5*X^3 + 60*X^2 + 59*X + 57) :=
  sq_step (by norm_num) pSeventeenA4s108 ⟨
    14*X^30 + 4*X^29 + 52*X^28 + 53*X^27 + 38*X^26 + 4*X^25 + 12*X^24 + 49*X^23 + 53*X^22 + 11*X^21 +
      X^20 + 24*X^19 + 20*X^18 + 17*X^17 + 11*X^16 + 13*X^15 + 2*X^14 + 47*X^13 + 63*X^12 + 35*X^11 +
      24*X^10 + 4*X^9 + 33*X^8 + 9*X^7 + 6*X^6 + 19*X^5 + 63*X^4 + 62*X^3 + 15*X^2 + 35*X + 33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s110 : XPow fSeventeenA4 22417328925111636040744
    (33*X^33 + 29*X^32 + 42*X^31 + 41*X^30 + 5*X^29 + 30*X^27 + 47*X^26 + 4*X^25 + 43*X^24 + 14*X^23 +
      63*X^22 + 56*X^21 + 64*X^20 + 20*X^19 + 29*X^18 + 56*X^17 + 64*X^16 + 39*X^15 + 23*X^14 +
      49*X^13 + 4*X^12 + 37*X^11 + 12*X^10 + 54*X^9 + 43*X^8 + 59*X^7 + 35*X^6 + 7*X^5 + 12*X^4 +
      28*X^3 + 38*X^2 + 56*X + 55) :=
  sq_step (by norm_num) pSeventeenA4s109 ⟨
    24*X^32 + 6*X^31 + 59*X^30 + 13*X^29 + 57*X^28 + 19*X^27 + 13*X^26 + 25*X^25 + 58*X^24 + 13*X^23 +
      52*X^22 + 22*X^21 + 14*X^20 + 53*X^19 + 16*X^18 + 54*X^17 + 2*X^16 + 11*X^15 + 66*X^14 +
      6*X^13 + 25*X^12 + 25*X^11 + 5*X^10 + 42*X^9 + 60*X^8 + 66*X^7 + 47*X^6 + 28*X^5 + 46*X^4 +
      54*X^3 + 2*X^2 + 27*X + 60,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s111 : XPow fSeventeenA4 22417328925111636040745
    (53*X^33 + 44*X^32 + 58*X^31 + 56*X^30 + 17*X^29 + 19*X^28 + 6*X^27 + X^26 + 5*X^25 + 52*X^24 +
      54*X^23 + 17*X^22 + 47*X^21 + 12*X^20 + 2*X^19 + 40*X^18 + 21*X^17 + 52*X^16 + 63*X^15 +
      60*X^14 + 3*X^13 + 18*X^12 + 33*X^11 + 2*X^10 + 21*X^9 + 26*X^8 + 61*X^7 + 59*X^6 + 4*X^5 +
      33*X^4 + 35*X^3 + 61*X^2 + 55*X + 59) :=
  mul_step (by norm_num) pSeventeenA4s110 pSeventeenA41 ⟨
    33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s112 : XPow fSeventeenA4 44834657850223272081490
    (39*X^33 + 8*X^32 + 18*X^31 + 64*X^30 + 10*X^29 + 59*X^28 + 17*X^27 + 20*X^26 + 10*X^25 + 8*X^24 +
      29*X^23 + 30*X^22 + 60*X^21 + 9*X^20 + 2*X^19 + 28*X^18 + 14*X^17 + 14*X^16 + 65*X^15 +
      12*X^14 + 29*X^13 + 29*X^12 + 58*X^11 + 58*X^10 + 38*X^9 + 52*X^8 + 15*X^7 + 17*X^6 + 24*X^5 +
      43*X^4 + X^3 + 6*X^2 + 60*X + 37) :=
  sq_step (by norm_num) pSeventeenA4s111 ⟨
    62*X^32 + 13*X^31 + 43*X^30 + 49*X^29 + 23*X^27 + 43*X^26 + 22*X^25 + 27*X^24 + 64*X^23 + 65*X^22 +
      23*X^21 + 26*X^20 + 12*X^19 + 42*X^18 + 42*X^17 + 7*X^16 + 20*X^15 + 3*X^14 + 44*X^13 +
      54*X^12 + 61*X^11 + 58*X^10 + 11*X^9 + 28*X^8 + 9*X^7 + 12*X^6 + 19*X^5 + 17*X^4 + 43*X^3 +
      33*X^2 + 42*X + 36,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s113 : XPow fSeventeenA4 44834657850223272081491
    (12*X^33 + 63*X^32 + 11*X^31 + 52*X^30 + 6*X^29 + 4*X^28 + 2*X^27 + 43*X^26 + 24*X^25 + 13*X^24 +
      62*X^23 + 20*X^22 + 62*X^21 + 23*X^20 + 57*X^19 + 56*X^18 + 18*X^17 + 56*X^16 + 41*X^15 +
      42*X^14 + 40*X^13 + 66*X^12 + 28*X^11 + 7*X^10 + 26*X^9 + 43*X^8 + 66*X^7 + 55*X^6 + 64*X^5 +
      13*X^4 + 39*X^3 + 5*X^2 + 37*X + 21) :=
  mul_step (by norm_num) pSeventeenA4s112 pSeventeenA41 ⟨
    39,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s114 : XPow fSeventeenA4 89669315700446544162982
    (4*X^33 + 49*X^32 + 14*X^31 + 18*X^29 + 37*X^28 + 13*X^26 + 53*X^25 + 49*X^24 + 35*X^23 + 52*X^22 +
      40*X^21 + 62*X^20 + 34*X^18 + 51*X^17 + 32*X^16 + 63*X^15 + 51*X^14 + 15*X^13 + 37*X^12 +
      60*X^11 + 12*X^10 + 2*X^9 + 44*X^8 + 24*X^7 + 47*X^6 + 9*X^5 + 49*X^4 + 65*X^3 + 22*X^2 + 17*X +
      41) :=
  sq_step (by norm_num) pSeventeenA4s113 ⟨
    10*X^32 + 27*X^31 + 16*X^30 + 11*X^29 + 66*X^28 + 37*X^27 + 51*X^26 + 53*X^25 + 14*X^24 + 53*X^23 +
      41*X^22 + 9*X^21 + X^20 + 59*X^19 + 24*X^18 + 14*X^17 + 49*X^16 + 7*X^15 + 18*X^14 + 35*X^13 +
      61*X^12 + 20*X^11 + 57*X^10 + 3*X^9 + 14*X^8 + 41*X^7 + 58*X^6 + 61*X^5 + 9*X^4 + 20*X^3 +
      42*X^2 + 17*X + 42,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s115 : XPow fSeventeenA4 179338631400893088325964
    (48*X^33 + 52*X^32 + 35*X^31 + 46*X^30 + 8*X^29 + 42*X^28 + 26*X^27 + 53*X^26 + 17*X^25 + 51*X^24 +
      34*X^23 + 39*X^22 + 64*X^21 + 39*X^20 + 25*X^19 + 50*X^18 + 39*X^17 + 60*X^16 + 60*X^15 +
      65*X^14 + 55*X^13 + 42*X^12 + 26*X^11 + 63*X^10 + 38*X^9 + 17*X^8 + 23*X^7 + 14*X^6 + 19*X^5 +
      51*X^4 + 45*X^3 + 48*X^2 + 32*X + 62) :=
  sq_step (by norm_num) pSeventeenA4s114 ⟨
    16*X^32 + 26*X^31 + 62*X^30 + 26*X^29 + 13*X^28 + 48*X^27 + 64*X^26 + 52*X^25 + 25*X^24 + 28*X^23 +
      46*X^22 + 3*X^21 + 30*X^20 + 12*X^19 + 11*X^18 + 22*X^17 + 41*X^16 + 29*X^15 + 5*X^13 +
      60*X^12 + 23*X^11 + 30*X^10 + 20*X^9 + 10*X^8 + 53*X^7 + 6*X^6 + 13*X^5 + 2*X^4 + 28*X^3 + 7*X +
      37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s116 : XPow fSeventeenA4 179338631400893088325965
    (26*X^33 + 44*X^32 + 22*X^31 + 3*X^30 + 18*X^29 + 10*X^28 + 36*X^27 + 37*X^26 + 14*X^25 + 4*X^24 +
      32*X^23 + 56*X^22 + 63*X^21 + 56*X^20 + 29*X^19 + 34*X^18 + 34*X^17 + 18*X^16 + 44*X^15 +
      4*X^14 + 4*X^13 + 41*X^12 + 57*X^11 + 5*X^10 + 52*X^9 + 42*X^8 + 64*X^7 + 52*X^6 + 15*X^5 +
      34*X^4 + X^3 + 21*X^2 + 62*X + 31) :=
  mul_step (by norm_num) pSeventeenA4s115 pSeventeenA41 ⟨
    48,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s117 : XPow fSeventeenA4 358677262801786176651930
    (10*X^33 + 27*X^32 + 52*X^31 + 40*X^30 + 54*X^29 + 29*X^28 + 25*X^27 + 59*X^26 + 5*X^25 + 3*X^24 +
      42*X^23 + 24*X^22 + 36*X^21 + 59*X^20 + 59*X^19 + 46*X^18 + 64*X^17 + 25*X^16 + 10*X^15 +
      38*X^14 + 4*X^13 + X^12 + 45*X^11 + 9*X^10 + 44*X^9 + 6*X^8 + X^7 + 29*X^6 + 53*X^5 + 55*X^4 +
      9*X^3 + 12*X^2 + 30*X + 18) :=
  sq_step (by norm_num) pSeventeenA4s116 ⟨
    6*X^32 + 57*X^31 + 52*X^30 + 35*X^29 + 60*X^28 + 6*X^27 + 18*X^26 + 58*X^25 + 29*X^24 + 32*X^23 +
      63*X^22 + 19*X^21 + 12*X^20 + 10*X^19 + 54*X^18 + 36*X^17 + 45*X^16 + 21*X^15 + 25*X^14 +
      48*X^13 + 48*X^12 + 33*X^11 + 27*X^10 + 10*X^9 + 42*X^8 + 18*X^7 + 18*X^6 + 2*X^5 + 30*X^4 +
      52*X^3 + 49*X^2 + 38*X + 29,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s118 : XPow fSeventeenA4 358677262801786176651931
    (16*X^33 + 12*X^32 + 35*X^31 + 39*X^30 + 24*X^29 + 44*X^28 + 8*X^27 + 65*X^26 + 26*X^25 + 19*X^24 +
      3*X^23 + 12*X^22 + 64*X^21 + 18*X^20 + 50*X^19 + 49*X^18 + 14*X^17 + 18*X^16 + 42*X^15 +
      52*X^14 + 21*X^13 + 23*X^12 + 58*X^11 + 12*X^10 + 44*X^9 + 58*X^8 + 45*X^7 + 18*X^6 + 14*X^5 +
      43*X^4 + 5*X^3 + 64*X^2 + 18*X + 26) :=
  mul_step (by norm_num) pSeventeenA4s117 pSeventeenA41 ⟨
    10,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s119 : XPow fSeventeenA4 717354525603572353303862
    (2*X^33 + 18*X^32 + 39*X^31 + 7*X^30 + 33*X^29 + 47*X^28 + 29*X^27 + 44*X^26 + 30*X^25 + 31*X^24 +
      25*X^23 + 59*X^22 + 64*X^21 + 26*X^20 + 39*X^19 + 3*X^18 + 24*X^17 + 27*X^16 + 15*X^15 +
      49*X^14 + 23*X^13 + 5*X^12 + 44*X^11 + 37*X^10 + 9*X^9 + 34*X^8 + 48*X^7 + 4*X^6 + 28*X^5 +
      15*X^4 + 27*X^3 + 51*X^2 + 57*X + 47) :=
  sq_step (by norm_num) pSeventeenA4s118 ⟨
    55*X^32 + 22*X^31 + 55*X^30 + 36*X^29 + 50*X^28 + 5*X^27 + 46*X^26 + X^25 + 27*X^24 + 60*X^23 +
      8*X^21 + 25*X^20 + 44*X^19 + 12*X^18 + 16*X^17 + 57*X^16 + 62*X^15 + 20*X^14 + 26*X^13 +
      52*X^12 + 12*X^11 + 15*X^10 + 19*X^9 + 65*X^8 + 20*X^7 + 42*X^6 + 54*X^5 + 6*X^4 + 4*X^3 +
      66*X^2 + 33*X + 57,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s120 : XPow fSeventeenA4 717354525603572353303863
    (56*X^33 + 31*X^32 + 6*X^31 + 30*X^30 + 46*X^29 + 6*X^28 + 7*X^27 + 42*X^26 + 49*X^25 + 7*X^24 +
      28*X^23 + 19*X^22 + 27*X^21 + 4*X^20 + 44*X^19 + 21*X^18 + 65*X^17 + 30*X^16 + 23*X^15 +
      46*X^14 + 9*X^13 + 53*X^12 + 20*X^11 + 16*X^10 + 55*X^9 + 46*X^8 + 34*X^7 + 21*X^6 + 47*X^5 +
      7*X^4 + 63*X^3 + 37*X^2 + 47*X + 32) :=
  mul_step (by norm_num) pSeventeenA4s119 pSeventeenA41 ⟨
    2,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s121 : XPow fSeventeenA4 1434709051207144706607726
    (66*X^33 + 62*X^32 + 25*X^31 + 34*X^30 + 36*X^29 + 30*X^28 + 38*X^27 + 19*X^26 + 20*X^25 + 57*X^24 +
      6*X^23 + 15*X^22 + 10*X^21 + 57*X^20 + 14*X^19 + 57*X^18 + 25*X^17 + 64*X^16 + 53*X^15 +
      52*X^14 + 52*X^13 + 54*X^12 + 22*X^11 + 59*X^10 + 11*X^9 + 39*X^8 + 8*X^7 + 15*X^5 + 49*X^4 +
      27*X^3 + 36*X^2 + 60*X + 61) :=
  sq_step (by norm_num) pSeventeenA4s120 ⟨
    54*X^32 + 9*X^31 + 47*X^30 + 6*X^29 + 21*X^28 + 41*X^27 + 58*X^26 + 24*X^25 + 53*X^24 + 48*X^23 +
      26*X^22 + 46*X^21 + 46*X^20 + 34*X^19 + 29*X^18 + 37*X^17 + 58*X^16 + 36*X^15 + 16*X^14 +
      60*X^13 + 22*X^12 + 33*X^11 + 3*X^10 + X^9 + 60*X^8 + 36*X^7 + 6*X^6 + 51*X^5 + 53*X^4 +
      60*X^3 + 12*X^2 + 11,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s122 : XPow fSeventeenA4 1434709051207144706607727
    (43*X^33 + 29*X^32 + X^31 + 4*X^30 + 64*X^29 + 16*X^28 + 4*X^27 + 14*X^26 + 48*X^25 + 15*X^24 +
      64*X^23 + 66*X^22 + 23*X^21 + 65*X^20 + 3*X^19 + 60*X^18 + 45*X^17 + 12*X^16 + 65*X^15 +
      7*X^14 + 52*X^13 + 51*X^12 + 34*X^11 + 41*X^10 + 62*X^9 + 9*X^8 + 52*X^7 + 52*X^6 + 33*X^5 +
      37*X^4 + 30*X^3 + 3*X^2 + 61*X + 51) :=
  mul_step (by norm_num) pSeventeenA4s121 pSeventeenA41 ⟨
    66,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s123 : XPow fSeventeenA4 2869418102414289413215454
    (34*X^33 + 16*X^32 + 39*X^31 + 23*X^30 + 45*X^29 + 43*X^28 + 57*X^27 + 9*X^26 + 29*X^25 + 50*X^24 +
      48*X^23 + 17*X^22 + 35*X^21 + 61*X^20 + 7*X^19 + 11*X^18 + 43*X^17 + 50*X^16 + 52*X^15 +
      58*X^14 + 33*X^13 + 13*X^12 + 5*X^11 + 2*X^10 + 18*X^9 + 49*X^8 + 30*X^7 + 17*X^6 + 32*X^5 +
      24*X^4 + 4*X^3 + 5*X^2 + 26*X + 33) :=
  sq_step (by norm_num) pSeventeenA4s122 ⟨
    40*X^32 + 38*X^31 + 15*X^30 + 46*X^29 + 40*X^28 + 60*X^27 + 29*X^26 + 46*X^25 + 36*X^24 + 41*X^23 +
      50*X^22 + 7*X^21 + 34*X^20 + 7*X^19 + 21*X^18 + 51*X^17 + 7*X^16 + 33*X^15 + 35*X^14 + 48*X^13 +
      21*X^12 + 53*X^11 + 9*X^10 + 29*X^9 + 2*X^8 + 41*X^7 + 56*X^6 + 60*X^5 + 11*X^4 + 21*X^2 +
      65*X + 7,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s124 : XPow fSeventeenA4 5738836204828578826430908
    (2*X^33 + 62*X^32 + 54*X^31 + 31*X^30 + 50*X^29 + 39*X^28 + 8*X^27 + 5*X^26 + 28*X^24 + 32*X^23 +
      52*X^22 + 54*X^21 + 25*X^20 + 54*X^19 + 51*X^18 + 6*X^17 + 13*X^16 + 14*X^15 + 34*X^14 +
      35*X^13 + 35*X^12 + 56*X^11 + 50*X^10 + 42*X^9 + 53*X^8 + 58*X^7 + 51*X^6 + 29*X^5 + 52*X^4 +
      34*X^3 + 62*X^2 + 30*X + 9) :=
  sq_step (by norm_num) pSeventeenA4s123 ⟨
    17*X^32 + 4*X^31 + 35*X^30 + 2*X^29 + 62*X^28 + 60*X^27 + 16*X^26 + 8*X^25 + 14*X^24 + 45*X^23 +
      64*X^22 + 7*X^21 + 32*X^20 + 65*X^19 + 33*X^18 + 6*X^17 + 12*X^16 + 31*X^15 + 42*X^14 + 3*X^13 +
      4*X^12 + 53*X^11 + 64*X^9 + 50*X^8 + 46*X^7 + 52*X^6 + 18*X^5 + 41*X^4 + 22*X^3 + 37*X^2 +
      37*X + 33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s125 : XPow fSeventeenA4 5738836204828578826430909
    (33*X^33 + 46*X^32 + 30*X^31 + 47*X^30 + 38*X^29 + 52*X^28 + 35*X^27 + 12*X^26 + 46*X^25 + 14*X^24 +
      21*X^23 + 9*X^22 + 26*X^21 + 19*X^20 + 25*X^19 + 3*X^18 + 51*X^17 + 29*X^16 + 8*X^15 + 58*X^14 +
      39*X^13 + 65*X^12 + 33*X^11 + 49*X^10 + 7*X^9 + 56*X^8 + 14*X^7 + 22*X^6 + 17*X^5 + 14*X^4 +
      7*X^3 + 10*X^2 + 9*X + 32) :=
  mul_step (by norm_num) pSeventeenA4s124 pSeventeenA41 ⟨
    2,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s126 : XPow fSeventeenA4 11477672409657157652861818
    (46*X^33 + 54*X^32 + 48*X^31 + 57*X^30 + 36*X^29 + 7*X^28 + 38*X^27 + X^26 + 11*X^25 + 35*X^24 +
      27*X^23 + 59*X^22 + 60*X^21 + 51*X^20 + 31*X^19 + 39*X^18 + 9*X^17 + 24*X^16 + 59*X^15 +
      25*X^14 + 22*X^13 + 25*X^12 + X^11 + 58*X^10 + 55*X^9 + 61*X^8 + 62*X^7 + 56*X^6 + 63*X^4 +
      43*X^3 + 13*X^2 + 5*X + 45) :=
  sq_step (by norm_num) pSeventeenA4s125 ⟨
    17*X^32 + 9*X^31 + 45*X^30 + 6*X^29 + 65*X^28 + 27*X^27 + 8*X^26 + 15*X^25 + 2*X^24 + 30*X^23 +
      36*X^22 + 39*X^21 + 49*X^19 + 48*X^18 + 64*X^17 + 52*X^16 + 39*X^15 + 46*X^14 + 54*X^13 +
      19*X^12 + 62*X^11 + 13*X^10 + 13*X^9 + 37*X^8 + 24*X^7 + 57*X^6 + 43*X^5 + 37*X^4 + 7*X^3 +
      29*X^2 + 2*X + 10,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s127 : XPow fSeventeenA4 11477672409657157652861819
    (57*X^33 + 65*X^32 + 34*X^31 + 34*X^30 + 51*X^29 + 45*X^28 + 21*X^27 + 19*X^26 + 47*X^25 + 15*X^24 +
      16*X^23 + 30*X^22 + 7*X^21 + 30*X^20 + 44*X^19 + 7*X^18 + 27*X^17 + 2*X^16 + 30*X^15 + 15*X^14 +
      50*X^13 + 7*X^12 + 2*X^11 + 15*X^10 + 8*X^9 + 16*X^8 + 9*X^7 + 40*X^6 + 62*X^5 + 52*X^4 +
      21*X^3 + 14*X^2 + 45*X + 66) :=
  mul_step (by norm_num) pSeventeenA4s126 pSeventeenA41 ⟨
    46,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s128 : XPow fSeventeenA4 22955344819314315305723638
    (14*X^33 + 9*X^32 + 14*X^31 + 43*X^30 + 42*X^29 + 44*X^28 + 26*X^27 + 55*X^26 + 9*X^25 + 46*X^24 +
      29*X^23 + 18*X^22 + 22*X^21 + 59*X^20 + 62*X^19 + 18*X^18 + 26*X^17 + 66*X^16 + 66*X^15 +
      53*X^14 + 38*X^13 + 63*X^12 + 65*X^11 + 34*X^10 + 57*X^9 + 33*X^8 + 52*X^7 + 11*X^6 + 37*X^5 +
      43*X^4 + 37*X^3 + 13*X^2 + 48*X + 22) :=
  sq_step (by norm_num) pSeventeenA4s127 ⟨
    33*X^32 + 64*X^31 + 6*X^30 + 64*X^29 + 5*X^28 + 27*X^27 + 11*X^26 + 27*X^25 + 7*X^24 + 33*X^23 +
      65*X^22 + 11*X^21 + 59*X^20 + 12*X^19 + 27*X^18 + 52*X^17 + 38*X^16 + 48*X^15 + 39*X^14 +
      56*X^13 + 29*X^12 + 14*X^11 + 32*X^10 + 20*X^8 + 16*X^7 + 57*X^6 + 6*X^5 + X^4 + 52*X^3 +
      26*X^2 + 17*X + 39,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s129 : XPow fSeventeenA4 45910689638628630611447276
    (37*X^33 + 60*X^32 + X^31 + 4*X^30 + 17*X^29 + 33*X^28 + 12*X^27 + 30*X^26 + 61*X^25 + 56*X^24 +
      57*X^23 + 38*X^22 + 29*X^21 + 24*X^20 + 48*X^19 + 27*X^18 + 11*X^17 + 32*X^16 + 64*X^15 +
      15*X^14 + 59*X^13 + 61*X^12 + 52*X^11 + 49*X^10 + 41*X^9 + 38*X^8 + 39*X^7 + 32*X^6 + 24*X^5 +
      19*X^4 + 30*X^3 + 66*X^2 + 52*X + 23) :=
  sq_step (by norm_num) pSeventeenA4s128 ⟨
    62*X^32 + 23*X^31 + 59*X^30 + 42*X^29 + 24*X^28 + 35*X^27 + 59*X^26 + 19*X^25 + 36*X^24 + 15*X^23 +
      36*X^22 + 33*X^21 + 26*X^20 + 52*X^19 + 19*X^18 + 30*X^17 + 26*X^16 + 34*X^15 + 11*X^14 +
      62*X^13 + 2*X^12 + 28*X^11 + 63*X^10 + 8*X^9 + 11*X^8 + 22*X^7 + 60*X^6 + 51*X^5 + 16*X^4 +
      66*X^3 + 55*X^2 + 22*X + 34,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s130 : XPow fSeventeenA4 91821379277257261222894552
    (31*X^33 + 42*X^32 + 55*X^31 + 29*X^30 + 19*X^29 + 10*X^28 + 58*X^27 + 65*X^26 + 37*X^25 + 58*X^24 +
      31*X^23 + 10*X^22 + 22*X^21 + 7*X^20 + 27*X^19 + 9*X^18 + 15*X^17 + 41*X^16 + 28*X^15 +
      59*X^14 + 49*X^13 + 11*X^12 + 12*X^11 + 43*X^10 + 35*X^9 + 46*X^8 + 55*X^7 + 18*X^6 + 17*X^5 +
      5*X^4 + 60*X^3 + 61*X^2 + 45*X + 10) :=
  sq_step (by norm_num) pSeventeenA4s129 ⟨
    29*X^32 + 33*X^31 + 31*X^30 + 21*X^29 + 11*X^28 + 13*X^27 + 4*X^26 + 3*X^25 + 33*X^24 + 43*X^23 +
      43*X^22 + 32*X^21 + 37*X^20 + 24*X^19 + 26*X^18 + 45*X^17 + 60*X^16 + 38*X^15 + 13*X^14 +
      36*X^13 + 23*X^12 + 6*X^11 + 27*X^10 + 33*X^9 + 4*X^8 + 15*X^7 + 49*X^6 + 14*X^5 + 5*X^4 +
      57*X^3 + 65*X^2 + 25*X + 22,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s131 : XPow fSeventeenA4 183642758554514522445789104
    (50*X^33 + 37*X^32 + 64*X^31 + 24*X^30 + 25*X^29 + 27*X^28 + 64*X^27 + 38*X^26 + 6*X^25 + 37*X^24 +
      62*X^22 + 38*X^21 + 44*X^20 + 53*X^19 + 3*X^18 + 56*X^17 + 37*X^16 + 56*X^15 + 53*X^14 +
      11*X^13 + 7*X^12 + 42*X^11 + 16*X^10 + 30*X^9 + 18*X^8 + 32*X^7 + 14*X^6 + 15*X^5 + 10*X^4 +
      49*X^3 + 13*X^2 + 34*X + 56) :=
  sq_step (by norm_num) pSeventeenA4s130 ⟨
    23*X^32 + 26*X^31 + 15*X^30 + 55*X^29 + 39*X^28 + 40*X^27 + 39*X^26 + 64*X^25 + 3*X^24 + 3*X^23 +
      13*X^22 + 54*X^21 + 64*X^20 + 12*X^19 + 19*X^18 + 24*X^17 + 37*X^16 + 23*X^15 + 41*X^14 +
      33*X^13 + 19*X^12 + 10*X^11 + 26*X^10 + X^9 + 5*X^8 + 15*X^7 + 53*X^6 + 12*X^4 + 18*X^3 +
      58*X^2 + 38*X + 14,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s132 : XPow fSeventeenA4 183642758554514522445789105
    (49*X^33 + 65*X^32 + 66*X^31 + 17*X^30 + 2*X^29 + 25*X^28 + 51*X^27 + 38*X^26 + 18*X^25 + 19*X^24 +
      24*X^23 + 52*X^22 + 2*X^21 + 49*X^20 + 23*X^19 + 48*X^18 + 49*X^17 + 29*X^16 + 6*X^15 +
      50*X^14 + 40*X^13 + 66*X^12 + 60*X^11 + 4*X^10 + 7*X^9 + 49*X^8 + 27*X^7 + 41*X^6 + 6*X^5 +
      18*X^4 + 45*X^3 + 3*X^2 + 56*X + 63) :=
  mul_step (by norm_num) pSeventeenA4s131 pSeventeenA41 ⟨
    50,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s133 : XPow fSeventeenA4 367285517109029044891578210
    (48*X^33 + 15*X^32 + 44*X^31 + 35*X^30 + 48*X^29 + 45*X^28 + X^27 + 34*X^26 + 41*X^25 + 64*X^24 +
      22*X^23 + 14*X^22 + 51*X^21 + 16*X^20 + 66*X^19 + 63*X^18 + 33*X^17 + 5*X^16 + 30*X^15 +
      53*X^14 + 17*X^13 + 61*X^12 + 17*X^11 + 7*X^10 + 56*X^9 + 33*X^8 + 53*X^6 + 58*X^5 + 16*X^4 +
      19*X^3 + 51*X^2 + 52*X + 40) :=
  sq_step (by norm_num) pSeventeenA4s132 ⟨
    56*X^32 + 64*X^31 + 27*X^30 + 23*X^29 + 7*X^28 + 5*X^26 + 34*X^25 + 34*X^24 + 22*X^23 + 25*X^22 +
      30*X^21 + 64*X^20 + 56*X^19 + 65*X^18 + 22*X^17 + 53*X^16 + 51*X^15 + 53*X^14 + 32*X^13 +
      37*X^12 + 40*X^11 + 17*X^10 + 59*X^9 + 10*X^8 + 46*X^7 + 21*X^6 + 57*X^5 + 41*X^4 + 7*X^3 +
      19*X^2 + 48*X + 35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s134 : XPow fSeventeenA4 367285517109029044891578211
    (56*X^33 + 53*X^32 + 11*X^31 + 43*X^30 + 21*X^29 + 52*X^28 + 17*X^27 + 61*X^26 + 27*X^25 + 59*X^24 +
      7*X^23 + 43*X^22 + 40*X^21 + 30*X^20 + 42*X^19 + 28*X^18 + 46*X^17 + 55*X^16 + 32*X^15 +
      33*X^14 + 23*X^13 + 32*X^12 + X^11 + 23*X^10 + X^9 + 19*X^8 + 36*X^7 + 24*X^6 + 47*X^5 + 8*X^4 +
      4*X^3 + 41*X^2 + 40*X + 31) :=
  mul_step (by norm_num) pSeventeenA4s133 pSeventeenA41 ⟨
    48,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s135 : XPow fSeventeenA4 734571034218058089783156422
    (11*X^33 + 22*X^32 + 66*X^31 + 16*X^30 + 35*X^29 + 17*X^28 + 60*X^27 + 58*X^26 + 34*X^25 + 54*X^24 +
      56*X^23 + 5*X^22 + 40*X^21 + 28*X^20 + 24*X^19 + 37*X^18 + 34*X^17 + 29*X^16 + 9*X^15 +
      21*X^14 + 52*X^13 + 14*X^12 + 51*X^11 + 49*X^10 + 33*X^9 + 36*X^8 + 62*X^7 + 3*X^6 + 28*X^5 +
      4*X^4 + 8*X^3 + 44*X^2 + 23*X + 3) :=
  sq_step (by norm_num) pSeventeenA4s134 ⟨
    54*X^32 + 61*X^31 + 26*X^30 + 41*X^29 + 57*X^28 + 35*X^27 + 6*X^26 + 6*X^25 + 39*X^24 + 16*X^23 +
      44*X^22 + 60*X^21 + 59*X^20 + 4*X^19 + 9*X^18 + 2*X^17 + 11*X^16 + 9*X^15 + 15*X^14 + 32*X^13 +
      28*X^12 + X^11 + 20*X^10 + 57*X^9 + 19*X^8 + 13*X^7 + 7*X^6 + 5*X^5 + 38*X^4 + 42*X^3 + 9*X^2 +
      60*X + 49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s136 : XPow fSeventeenA4 734571034218058089783156423
    (30*X^33 + 22*X^32 + 44*X^31 + 52*X^30 + 45*X^29 + 34*X^28 + 22*X^27 + 33*X^26 + 19*X^25 + 24*X^24 +
      2*X^23 + 27*X^22 + 66*X^20 + 28*X^19 + 51*X^18 + 37*X^17 + 58*X^16 + 12*X^15 + 11*X^14 +
      36*X^13 + 56*X^11 + 38*X^10 + 51*X^9 + 51*X^8 + 34*X^7 + 23*X^6 + 46*X^5 + 32*X^4 + 43*X^3 +
      47*X^2 + 3*X + 42) :=
  mul_step (by norm_num) pSeventeenA4s135 pSeventeenA41 ⟨
    11,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s137 : XPow fSeventeenA4 1469142068436116179566312846
    (60*X^33 + X^32 + 47*X^31 + 47*X^30 + 51*X^29 + 5*X^28 + 26*X^27 + 32*X^26 + 9*X^25 + 9*X^24 +
      20*X^23 + 25*X^22 + 42*X^21 + 14*X^20 + 3*X^19 + 58*X^18 + 16*X^17 + 49*X^16 + 2*X^15 +
      15*X^14 + 33*X^13 + 45*X^12 + 60*X^11 + 65*X^10 + 26*X^9 + 56*X^8 + 15*X^6 + 11*X^5 + 54*X^4 +
      65*X^3 + 40*X^2 + 48*X + 39) :=
  sq_step (by norm_num) pSeventeenA4s136 ⟨
    29*X^32 + 62*X^31 + 32*X^30 + 8*X^29 + 6*X^28 + 12*X^27 + 55*X^26 + 52*X^25 + 50*X^24 + 15*X^23 +
      44*X^22 + 4*X^21 + 48*X^20 + 26*X^19 + 38*X^18 + 58*X^17 + 6*X^16 + 16*X^15 + 47*X^14 +
      29*X^13 + 5*X^12 + 37*X^11 + 42*X^10 + 24*X^9 + 37*X^8 + 48*X^7 + 41*X^6 + 44*X^5 + 51*X^4 +
      2*X^3 + 16*X^2 + 4*X + 22,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s138 : XPow fSeventeenA4 1469142068436116179566312847
    (2*X^33 + 8*X^32 + 17*X^31 + 28*X^30 + 42*X^29 + 6*X^28 + 61*X^27 + 34*X^26 + 13*X^25 + 16*X^24 +
      33*X^23 + 32*X^22 + 44*X^21 + 25*X^20 + 15*X^19 + 60*X^18 + 50*X^17 + 50*X^16 + 39*X^15 +
      53*X^14 + 31*X^13 + 62*X^12 + 24*X^11 + 35*X^10 + 16*X^9 + 7*X^8 + 44*X^7 + 2*X^6 + 9*X^5 +
      X^4 + 65*X^3 + 51*X^2 + 39*X + 22) :=
  mul_step (by norm_num) pSeventeenA4s137 pSeventeenA41 ⟨
    60,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s139 : XPow fSeventeenA4 2938284136872232359132625694
    (2*X^33 + 15*X^32 + 10*X^31 + 36*X^30 + 6*X^29 + 16*X^28 + 66*X^27 + 45*X^26 + 12*X^25 + 53*X^24 +
      22*X^23 + 9*X^22 + 39*X^21 + 66*X^20 + 19*X^19 + 31*X^18 + 26*X^17 + 40*X^16 + 55*X^15 +
      25*X^14 + 25*X^13 + 47*X^12 + 60*X^10 + 13*X^9 + 23*X^8 + 50*X^7 + 40*X^6 + 61*X^5 + 57*X^3 +
      28*X^2 + 7*X + 56) :=
  sq_step (by norm_num) pSeventeenA4s138 ⟨
    4*X^32 + 41*X^31 + 24*X^30 + 4*X^29 + 21*X^28 + 46*X^27 + 55*X^26 + 2*X^25 + 37*X^24 + 33*X^23 +
      53*X^22 + 41*X^21 + 61*X^20 + 43*X^19 + 5*X^18 + 38*X^17 + 4*X^16 + 30*X^14 + 17*X^13 +
      23*X^12 + 64*X^11 + 46*X^10 + 44*X^9 + 16*X^8 + 58*X^7 + 7*X^6 + 11*X^5 + 33*X^4 + 34*X^3 +
      24*X^2 + 23*X + 57,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s140 : XPow fSeventeenA4 5876568273744464718265251388
    (32*X^33 + 46*X^32 + 59*X^31 + 11*X^30 + 27*X^29 + 38*X^28 + 29*X^27 + 66*X^26 + 24*X^25 + 51*X^24 +
      26*X^23 + 32*X^22 + 63*X^21 + 43*X^20 + 41*X^19 + 26*X^18 + 13*X^17 + 17*X^16 + 58*X^15 +
      30*X^14 + 26*X^12 + 60*X^11 + 11*X^10 + 61*X^9 + 45*X^8 + 44*X^7 + 54*X^6 + 34*X^5 + 62*X^4 +
      17*X^3 + 51*X^2 + 16*X + 27) :=
  sq_step (by norm_num) pSeventeenA4s139 ⟨
    4*X^32 + 2*X^31 + 19*X^30 + 58*X^29 + 12*X^28 + 41*X^27 + 6*X^26 + 16*X^25 + X^24 + 37*X^23 +
      24*X^22 + 5*X^21 + 51*X^20 + 21*X^19 + 13*X^18 + 39*X^17 + 35*X^16 + 38*X^15 + X^14 + 21*X^13 +
      27*X^12 + 26*X^10 + 31*X^9 + 15*X^8 + 27*X^7 + 23*X^6 + 23*X^5 + 35*X^4 + 24*X^3 + 36*X^2 +
      19*X + 36,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s141 : XPow fSeventeenA4 5876568273744464718265251389
    (51*X^33 + 65*X^32 + 62*X^31 + 46*X^30 + 22*X^29 + 63*X^28 + 10*X^27 + 15*X^26 + 4*X^25 + 6*X^24 +
      5*X^23 + 13*X^22 + 59*X^21 + 17*X^20 + 12*X^19 + 32*X^18 + 22*X^17 + 30*X^16 + 16*X^15 +
      33*X^14 + 23*X^13 + 3*X^12 + 7*X^11 + 39*X^10 + 46*X^9 + 12*X^8 + 65*X^7 + 56*X^6 + 38*X^5 +
      32*X^4 + 42*X^3 + 31*X^2 + 27*X + 43) :=
  mul_step (by norm_num) pSeventeenA4s140 pSeventeenA41 ⟨
    32,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s142 : XPow fSeventeenA4 11753136547488929436530502778
    (54*X^33 + 4*X^32 + 32*X^31 + 35*X^30 + 6*X^29 + 14*X^28 + 44*X^27 + 33*X^26 + 46*X^25 + 9*X^24 +
      38*X^23 + 53*X^22 + 19*X^21 + 5*X^20 + 53*X^19 + 24*X^18 + 26*X^17 + 56*X^16 + 54*X^15 +
      61*X^14 + 14*X^13 + 66*X^12 + 66*X^11 + 32*X^10 + 2*X^9 + 8*X^8 + 65*X^7 + 6*X^6 + 9*X^5 +
      25*X^4 + 5*X^3 + 26*X^2 + 48*X + 20) :=
  sq_step (by norm_num) pSeventeenA4s141 ⟨
    55*X^32 + 37*X^31 + 44*X^30 + 46*X^29 + 2*X^28 + 66*X^27 + 21*X^26 + 10*X^25 + 53*X^24 + 47*X^23 +
      11*X^22 + 16*X^21 + 15*X^20 + 19*X^19 + 54*X^18 + 24*X^17 + 9*X^16 + 7*X^15 + 6*X^14 + 56*X^13 +
      54*X^12 + 6*X^11 + 42*X^10 + 47*X^9 + 37*X^8 + 35*X^7 + 21*X^6 + 24*X^5 + 30*X^4 + 60*X^3 +
      42*X^2 + 17*X + 49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s143 : XPow fSeventeenA4 11753136547488929436530502779
    (25*X^33 + 17*X^32 + 8*X^31 + 59*X^30 + 54*X^29 + 26*X^28 + 39*X^27 + 35*X^26 + 26*X^25 + 21*X^24 +
      20*X^23 + 10*X^22 + 32*X^21 + 46*X^20 + 59*X^19 + 12*X^18 + 10*X^17 + 57*X^16 + 29*X^15 +
      32*X^14 + 40*X^13 + 41*X^12 + 42*X^11 + 57*X^10 + 39*X^9 + 11*X^8 + 12*X^7 + 21*X^6 + 18*X^5 +
      X^4 + 15*X^3 + 44*X^2 + 20*X + 60) :=
  mul_step (by norm_num) pSeventeenA4s142 pSeventeenA41 ⟨
    54,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s144 : XPow fSeventeenA4 23506273094977858873061005558
    (2*X^33 + 64*X^32 + 50*X^31 + X^30 + 16*X^29 + 66*X^28 + 49*X^27 + 53*X^26 + 24*X^25 + 32*X^24 +
      39*X^23 + 58*X^22 + 33*X^21 + 12*X^20 + 64*X^19 + 33*X^18 + 61*X^17 + 61*X^16 + 33*X^15 +
      7*X^14 + 60*X^13 + 40*X^12 + 53*X^11 + 59*X^10 + 25*X^9 + 16*X^8 + 2*X^7 + 2*X^6 + 48*X^5 +
      29*X^4 + X^3 + 57*X^2 + 15*X + 6) :=
  sq_step (by norm_num) pSeventeenA4s143 ⟨
    22*X^32 + 62*X^31 + 37*X^30 + 48*X^29 + 43*X^28 + 60*X^27 + 45*X^26 + X^25 + 8*X^24 + 39*X^23 +
      4*X^22 + 45*X^21 + 23*X^20 + 48*X^19 + 6*X^18 + 36*X^17 + 44*X^16 + 50*X^15 + 28*X^14 +
      32*X^13 + 44*X^12 + 27*X^11 + 39*X^10 + 2*X^9 + 38*X^8 + 31*X^7 + 29*X^6 + 5*X^5 + 29*X^4 +
      56*X^3 + 18*X^2 + 31*X + 35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s145 : XPow fSeventeenA4 23506273094977858873061005559
    (35*X^33 + 42*X^32 + 13*X^30 + 65*X^29 + 26*X^28 + 16*X^27 + 36*X^26 + 50*X^25 + 21*X^24 + 27*X^23 +
      55*X^22 + 13*X^21 + 29*X^20 + 7*X^19 + 58*X^18 + 32*X^17 + 48*X^16 + 48*X^15 + 16*X^14 +
      44*X^13 + 62*X^12 + 42*X^11 + 32*X^10 + 37*X^9 + 32*X^7 + 41*X^6 + 61*X^5 + 48*X^4 + 2*X^3 +
      62*X^2 + 6*X + 32) :=
  mul_step (by norm_num) pSeventeenA4s144 pSeventeenA41 ⟨
    2,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s146 : XPow fSeventeenA4 47012546189955717746122011118
    (32*X^33 + 11*X^32 + 10*X^31 + 52*X^30 + 14*X^29 + 11*X^28 + 61*X^27 + 33*X^26 + 44*X^25 + 47*X^23 +
      52*X^22 + 41*X^21 + 9*X^20 + 5*X^19 + 16*X^18 + 64*X^17 + 52*X^16 + 48*X^15 + 3*X^14 + 33*X^13 +
      28*X^12 + 13*X^11 + 47*X^10 + 8*X^9 + 36*X^8 + 28*X^7 + 50*X^6 + 66*X^5 + 51*X^4 + 43*X^3 +
      56*X^2 + 62*X + 47) :=
  sq_step (by norm_num) pSeventeenA4s145 ⟨
    19*X^32 + 18*X^31 + 20*X^30 + 36*X^29 + 11*X^28 + 29*X^27 + 53*X^26 + 55*X^25 + 35*X^24 + 51*X^23 +
      2*X^22 + 47*X^21 + 39*X^20 + 53*X^19 + 30*X^18 + 13*X^17 + 38*X^16 + 21*X^15 + 28*X^14 +
      39*X^13 + 62*X^12 + 18*X^11 + 61*X^10 + 46*X^9 + 23*X^8 + 65*X^7 + 7*X^6 + 33*X^5 + 21*X^4 +
      3*X^3 + 37*X^2 + 5*X + 52,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s147 : XPow fSeventeenA4 47012546189955717746122011119
    (16*X^33 + 16*X^32 + 36*X^31 + 33*X^30 + 62*X^29 + 28*X^28 + 44*X^27 + 35*X^26 + 20*X^25 + 27*X^24 +
      25*X^23 + 58*X^22 + 25*X^21 + 48*X^20 + 2*X^19 + 16*X^18 + 57*X^17 + 20*X^16 + 56*X^15 +
      66*X^14 + 25*X^13 + 23*X^12 + 43*X^11 + 53*X^10 + 37*X^9 + 63*X^8 + 61*X^7 + 21*X^6 + 27*X^5 +
      58*X^4 + 47*X^3 + 10*X^2 + 47*X + 43) :=
  mul_step (by norm_num) pSeventeenA4s146 pSeventeenA41 ⟨
    32,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s148 : XPow fSeventeenA4 94025092379911435492244022238
    (55*X^33 + 10*X^32 + 8*X^31 + 26*X^30 + 66*X^29 + 2*X^28 + 10*X^27 + 32*X^26 + 36*X^25 + 27*X^24 +
      56*X^23 + 6*X^22 + 34*X^21 + 54*X^20 + 36*X^19 + 42*X^18 + 2*X^17 + 43*X^16 + 25*X^15 +
      48*X^14 + 33*X^13 + 29*X^12 + 12*X^11 + 21*X^10 + 2*X^9 + 60*X^8 + 17*X^7 + 28*X^6 + 35*X^5 +
      64*X^4 + 30*X^3 + 11*X^2 + 39*X + 66) :=
  sq_step (by norm_num) pSeventeenA4s147 ⟨
    55*X^32 + 16*X^31 + 18*X^30 + 13*X^29 + 32*X^28 + 23*X^27 + 55*X^26 + 35*X^25 + 39*X^24 + 10*X^23 +
      5*X^22 + 45*X^21 + 17*X^20 + 57*X^19 + 64*X^18 + 63*X^17 + 43*X^16 + 41*X^15 + 22*X^14 +
      30*X^13 + 64*X^12 + 37*X^11 + 46*X^10 + 53*X^9 + 62*X^8 + 57*X^7 + 60*X^6 + 48*X^5 + 22*X^4 +
      2*X^3 + 58*X^2 + 22*X + 10,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s149 : XPow fSeventeenA4 188050184759822870984488044476
    (9*X^33 + 53*X^32 + 26*X^31 + 2*X^30 + 34*X^29 + 46*X^28 + 26*X^27 + 16*X^26 + 60*X^25 + 37*X^24 +
      5*X^23 + 14*X^22 + 61*X^21 + 48*X^20 + 30*X^19 + 33*X^18 + 3*X^17 + 21*X^16 + 8*X^15 + 33*X^14 +
      24*X^13 + 65*X^12 + 13*X^11 + 15*X^10 + 13*X^9 + 44*X^8 + 28*X^7 + 21*X^6 + 60*X^5 + 23*X^4 +
      44*X^3 + 22*X^2 + 20*X + 41) :=
  sq_step (by norm_num) pSeventeenA4s148 ⟨
    10*X^32 + 17*X^31 + 57*X^30 + 10*X^29 + 44*X^28 + 13*X^27 + 49*X^26 + 46*X^25 + 33*X^24 + 64*X^23 +
      38*X^22 + 66*X^21 + 33*X^20 + 36*X^19 + 54*X^18 + 8*X^17 + 54*X^16 + 56*X^15 + 5*X^14 + 9*X^13 +
      11*X^12 + 57*X^11 + 15*X^10 + 33*X^9 + 4*X^8 + 37*X^7 + 41*X^6 + 4*X^5 + 40*X^4 + 28*X^3 +
      60*X^2 + 48*X + 36,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s150 : XPow fSeventeenA4 188050184759822870984488044477
    (23*X^33 + 57*X^32 + 31*X^31 + 54*X^30 + 8*X^29 + 23*X^28 + 17*X^27 + 47*X^26 + 51*X^25 + 58*X^24 +
      42*X^23 + 26*X^22 + 19*X^21 + 40*X^20 + 50*X^19 + 23*X^18 + 58*X^17 + 42*X^16 + 50*X^15 +
      27*X^14 + 16*X^13 + 20*X^12 + 39*X^11 + 11*X^10 + 38*X^9 + 19*X^8 + 22*X^7 + 62*X^6 + 33*X^5 +
      21*X^4 + 9*X^3 + 64*X^2 + 41*X + 10) :=
  mul_step (by norm_num) pSeventeenA4s149 pSeventeenA41 ⟨
    9,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s151 : XPow fSeventeenA4 376100369519645741968976088954
    (22*X^33 + 29*X^32 + 66*X^31 + 25*X^30 + 40*X^29 + 34*X^28 + 27*X^27 + 63*X^26 + 8*X^25 + 16*X^24 +
      46*X^23 + 19*X^22 + 29*X^21 + 35*X^20 + 57*X^19 + 65*X^18 + 15*X^17 + 33*X^16 + 26*X^15 +
      45*X^14 + 20*X^13 + 9*X^12 + 31*X^11 + 22*X^10 + 45*X^9 + 43*X^8 + 46*X^7 + 39*X^6 + 9*X^5 +
      47*X^4 + 43*X^3 + 51*X^2 + 42*X + 25) :=
  sq_step (by norm_num) pSeventeenA4s150 ⟨
    60*X^32 + 10*X^31 + 2*X^30 + 23*X^29 + 47*X^28 + 43*X^27 + 2*X^26 + 14*X^25 + 55*X^24 + 25*X^23 +
      21*X^22 + 4*X^21 + 41*X^20 + 52*X^19 + 63*X^18 + 12*X^17 + 38*X^16 + 43*X^15 + 9*X^14 +
      57*X^13 + 28*X^12 + 11*X^11 + 62*X^10 + 23*X^9 + 8*X^8 + 31*X^7 + 53*X^6 + 52*X^5 + 45*X^4 +
      30*X^3 + 23*X^2 + 10*X + 33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s152 : XPow fSeventeenA4 752200739039291483937952177908
    (31*X^33 + 64*X^32 + 48*X^31 + 12*X^30 + 50*X^29 + 14*X^28 + 27*X^27 + 45*X^26 + 43*X^25 + 25*X^24 +
      4*X^23 + 11*X^22 + 30*X^21 + 44*X^20 + 12*X^19 + 30*X^18 + 19*X^17 + 34*X^16 + 23*X^15 +
      65*X^14 + 46*X^13 + 65*X^12 + 6*X^11 + 30*X^10 + 31*X^9 + 65*X^8 + 21*X^7 + 47*X^6 + 11*X^5 +
      24*X^4 + 39*X^3 + 8*X^2 + 59*X + 8) :=
  sq_step (by norm_num) pSeventeenA4s151 ⟨
    15*X^32 + 20*X^31 + 45*X^30 + 34*X^29 + 60*X^28 + 20*X^27 + 27*X^26 + 62*X^25 + 4*X^24 + 12*X^23 +
      53*X^22 + 3*X^21 + 37*X^20 + 43*X^19 + 5*X^18 + 19*X^17 + 43*X^16 + 48*X^15 + 8*X^14 + 47*X^13 +
      24*X^12 + 63*X^11 + 50*X^10 + 9*X^9 + 51*X^8 + 26*X^7 + 18*X^6 + 35*X^5 + 11*X^4 + 3*X^3 +
      58*X^2 + 19*X + 41,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s153 : XPow fSeventeenA4 1504401478078582967875904355816
    (13*X^33 + 46*X^32 + 45*X^31 + 37*X^30 + 23*X^29 + 39*X^28 + 64*X^27 + 19*X^26 + 52*X^25 + 12*X^24 +
      52*X^23 + 3*X^21 + 6*X^20 + 61*X^19 + 51*X^18 + 41*X^17 + 57*X^16 + 42*X^15 + 57*X^14 +
      25*X^13 + 51*X^12 + 18*X^11 + 40*X^10 + 38*X^9 + 65*X^8 + 49*X^7 + 11*X^6 + 2*X^5 + 25*X^4 +
      66*X^3 + 29*X^2 + 20*X + 1) :=
  sq_step (by norm_num) pSeventeenA4s152 ⟨
    23*X^32 + 50*X^31 + 24*X^30 + 64*X^29 + 61*X^28 + 12*X^27 + 30*X^26 + 66*X^25 + 27*X^24 + 37*X^23 +
      12*X^22 + 20*X^21 + 33*X^20 + 14*X^19 + 63*X^18 + 20*X^17 + 17*X^16 + 35*X^15 + X^14 + 46*X^13 +
      65*X^12 + 17*X^11 + 15*X^10 + 24*X^9 + 27*X^8 + 50*X^7 + 34*X^6 + 50*X^5 + 9*X^4 + 50*X^3 +
      13*X^2 + 26*X + 17,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s154 : XPow fSeventeenA4 1504401478078582967875904355817
    (25*X^33 + 60*X^32 + 64*X^31 + 37*X^30 + 66*X^29 + 15*X^28 + 13*X^27 + 63*X^26 + 62*X^25 + 2*X^24 +
      33*X^23 + 12*X^22 + 46*X^21 + X^20 + 16*X^19 + 55*X^18 + 36*X^17 + 39*X^16 + 22*X^15 + 7*X^14 +
      10*X^13 + 43*X^12 + 30*X^11 + 50*X^10 + 34*X^9 + 36*X^8 + 5*X^7 + 57*X^6 + 32*X^5 + 3*X^4 +
      40*X^3 + 24*X^2 + X + 7) :=
  mul_step (by norm_num) pSeventeenA4s153 pSeventeenA41 ⟨
    13,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s155 : XPow fSeventeenA4 3008802956157165935751808711634
    (49*X^33 + 41*X^32 + 23*X^31 + 25*X^30 + 39*X^29 + 45*X^28 + 34*X^27 + X^26 + 38*X^25 + 49*X^24 +
      5*X^23 + 26*X^22 + 32*X^21 + 56*X^20 + 25*X^19 + 21*X^18 + 13*X^17 + 41*X^16 + 9*X^15 +
      12*X^14 + 8*X^12 + 64*X^11 + 45*X^10 + 38*X^9 + 22*X^8 + 37*X^7 + 51*X^6 + 39*X^5 + 46*X^4 +
      16*X^3 + 2*X^2 + 38*X) :=
  sq_step (by norm_num) pSeventeenA4s154 ⟨
    22*X^32 + X^31 + 31*X^30 + 54*X^29 + 8*X^28 + 48*X^27 + 23*X^26 + 51*X^25 + 3*X^24 + 35*X^23 +
      25*X^22 + 53*X^21 + 18*X^20 + 52*X^19 + 15*X^18 + 63*X^17 + 45*X^16 + 54*X^15 + 59*X^14 +
      56*X^13 + 61*X^12 + 47*X^11 + 46*X^10 + 11*X^9 + 66*X^8 + 2*X^7 + 55*X^6 + 64*X^5 + 39*X^4 +
      19*X^3 + 52*X^2 + 35*X + 43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s156 : XPow fSeventeenA4 3008802956157165935751808711635
    (34*X^33 + 28*X^32 + 34*X^31 + 66*X^30 + 54*X^29 + 40*X^28 + 66*X^27 + 64*X^26 + 21*X^25 + 33*X^24 +
      37*X^23 + 35*X^22 + 47*X^21 + 5*X^20 + 54*X^19 + 40*X^18 + 34*X^17 + 8*X^16 + 45*X^15 +
      61*X^14 + 39*X^13 + 50*X^12 + 64*X^11 + 42*X^10 + 34*X^9 + 55*X^8 + 49*X^7 + 35*X^6 + 26*X^5 +
      62*X^4 + 28*X^3 + 17*X^2 + 47) :=
  mul_step (by norm_num) pSeventeenA4s155 pSeventeenA41 ⟨
    49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s157 : XPow fSeventeenA4 6017605912314331871503617423270
    (43*X^33 + 63*X^32 + 64*X^31 + 47*X^30 + 24*X^29 + 13*X^28 + 27*X^27 + 59*X^26 + 7*X^25 + 16*X^23 +
      52*X^22 + 33*X^21 + 42*X^20 + 15*X^19 + 30*X^18 + 64*X^17 + 44*X^16 + 2*X^15 + 16*X^14 +
      45*X^13 + 6*X^12 + 65*X^11 + X^10 + 10*X^9 + 34*X^8 + 18*X^7 + 9*X^6 + 55*X^5 + 24*X^4 +
      10*X^3 + 10*X^2 + 62*X + 57) :=
  sq_step (by norm_num) pSeventeenA4s156 ⟨
    17*X^32 + 16*X^31 + 49*X^30 + 48*X^29 + 61*X^28 + 20*X^27 + 52*X^26 + 55*X^25 + 29*X^24 + 7*X^23 +
      58*X^22 + 47*X^20 + 21*X^19 + 40*X^18 + 41*X^17 + 52*X^16 + 64*X^15 + X^14 + 47*X^13 + 6*X^12 +
      7*X^11 + 65*X^10 + 54*X^9 + 27*X^8 + 46*X^7 + 3*X^6 + 65*X^5 + 31*X^4 + X^3 + 47*X^2 + 29*X +
      33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s158 : XPow fSeventeenA4 6017605912314331871503617423271
    (9*X^33 + 26*X^32 + 59*X^31 + 60*X^30 + 25*X^29 + 35*X^28 + 34*X^27 + 64*X^26 + 52*X^25 + 31*X^24 +
      22*X^23 + 37*X^22 + 30*X^21 + 33*X^20 + 7*X^19 + 33*X^18 + 57*X^17 + 23*X^16 + 60*X^15 +
      37*X^14 + 25*X^13 + 24*X^12 + 4*X^11 + 60*X^10 + 50*X^9 + 42*X^8 + 51*X^7 + 5*X^6 + 42*X^5 +
      49*X^4 + 34*X^2 + 57*X + 18) :=
  mul_step (by norm_num) pSeventeenA4s157 pSeventeenA41 ⟨
    43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s159 : XPow fSeventeenA4 12035211824628663743007234846542
    (14*X^33 + 29*X^32 + 27*X^31 + 31*X^30 + 2*X^29 + 52*X^28 + 56*X^27 + 61*X^25 + 36*X^24 + 51*X^23 +
      53*X^22 + 57*X^21 + 52*X^20 + 18*X^19 + 20*X^18 + 28*X^17 + 61*X^16 + 3*X^15 + 11*X^14 +
      60*X^12 + 51*X^11 + 42*X^10 + 15*X^9 + 37*X^8 + 20*X^7 + 34*X^6 + 46*X^5 + 15*X^4 + 27*X^3 +
      49*X^2 + 46*X + 53) :=
  sq_step (by norm_num) pSeventeenA4s158 ⟨
    14*X^32 + 64*X^31 + 17*X^30 + 54*X^29 + 50*X^28 + 18*X^27 + X^26 + 10*X^25 + 55*X^24 + 19*X^23 +
      64*X^22 + 53*X^21 + 2*X^20 + 66*X^19 + 10*X^18 + 62*X^17 + 3*X^16 + 36*X^15 + 23*X^14 +
      35*X^13 + 3*X^12 + 7*X^11 + 61*X^10 + 33*X^9 + 40*X^8 + 12*X^7 + 34*X^6 + 27*X^5 + 16*X^4 +
      24*X^3 + 61*X^2 + 17*X + 4,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s160 : XPow fSeventeenA4 24070423649257327486014469693084
    (16*X^33 + 35*X^32 + 3*X^31 + 58*X^30 + 23*X^29 + 10*X^28 + 64*X^27 + 55*X^26 + 4*X^24 + 48*X^23 +
      65*X^22 + 53*X^21 + 37*X^20 + 26*X^19 + 61*X^18 + 11*X^17 + 65*X^16 + 26*X^15 + 64*X^14 +
      3*X^13 + 51*X^12 + 51*X^11 + 63*X^10 + 29*X^8 + 31*X^7 + 24*X^6 + 44*X^5 + 28*X^4 + 64*X^3 +
      45*X^2 + 40*X + 51) :=
  sq_step (by norm_num) pSeventeenA4s159 ⟨
    62*X^32 + 47*X^31 + 31*X^30 + 57*X^29 + 42*X^28 + 14*X^27 + 15*X^26 + 10*X^25 + 2*X^24 + 47*X^23 +
      57*X^22 + 54*X^21 + 42*X^20 + 27*X^19 + 5*X^18 + 63*X^17 + 57*X^16 + 39*X^15 + 8*X^14 +
      26*X^13 + 52*X^12 + 49*X^11 + 51*X^10 + 38*X^9 + 21*X^8 + 16*X^7 + 64*X^6 + 60*X^5 + 7*X^4 +
      42*X^3 + 59*X^2 + 16*X + 37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s161 : XPow fSeventeenA4 48140847298514654972028939386168
    (37*X^33 + 60*X^32 + 30*X^31 + 41*X^30 + 57*X^29 + 34*X^28 + 49*X^27 + 56*X^26 + 50*X^25 + 20*X^24 +
      29*X^23 + 46*X^22 + 3*X^21 + 45*X^19 + 49*X^18 + 22*X^17 + 37*X^16 + 3*X^15 + 46*X^14 +
      11*X^13 + 35*X^12 + 30*X^11 + 66*X^10 + 47*X^9 + 7*X^8 + 48*X^7 + 28*X^6 + 8*X^5 + 24*X^4 +
      49*X^3 + 6*X^2 + 39*X + 18) :=
  sq_step (by norm_num) pSeventeenA4s160 ⟨
    55*X^32 + 21*X^31 + 26*X^30 + 3*X^29 + 42*X^28 + 44*X^27 + 37*X^26 + 57*X^25 + 49*X^24 + 32*X^22 +
      43*X^21 + 7*X^20 + 42*X^19 + 61*X^18 + 64*X^17 + 25*X^16 + 2*X^15 + 57*X^14 + 53*X^13 + 4*X^12 +
      7*X^11 + 21*X^10 + 57*X^9 + 33*X^8 + 33*X^7 + 20*X^6 + 43*X^5 + 5*X^4 + 60*X^3 + 24*X^2 + 28*X +
      27,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s162 : XPow fSeventeenA4 96281694597029309944057878772336
    (25*X^33 + 49*X^32 + 10*X^31 + X^30 + 23*X^29 + 13*X^28 + 59*X^27 + 24*X^26 + 56*X^25 + X^24 +
      38*X^23 + 49*X^22 + 24*X^21 + 52*X^20 + 21*X^19 + 11*X^18 + 12*X^17 + 20*X^16 + 58*X^15 +
      24*X^14 + 62*X^13 + 50*X^12 + 8*X^11 + 33*X^10 + 48*X^9 + 22*X^8 + 37*X^7 + 19*X^6 + 16*X^5 +
      38*X^4 + 59*X^3 + 51*X^2 + 65*X + 2) :=
  sq_step (by norm_num) pSeventeenA4s161 ⟨
    29*X^32 + 33*X^31 + 33*X^30 + 46*X^29 + 61*X^27 + 43*X^26 + 62*X^25 + 3*X^24 + 28*X^23 + 31*X^22 +
      13*X^21 + 43*X^20 + 37*X^19 + 37*X^18 + 28*X^17 + 36*X^16 + 28*X^15 + 41*X^14 + 11*X^13 +
      35*X^12 + 15*X^11 + 40*X^10 + 49*X^9 + 60*X^8 + 18*X^7 + 40*X^6 + 13*X^5 + 5*X^4 + 22*X^3 +
      15*X^2 + 21*X + 5,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s163 : XPow fSeventeenA4 96281694597029309944057878772337
    (55*X^33 + 44*X^32 + 22*X^31 + 19*X^30 + 34*X^29 + 6*X^28 + 64*X^27 + 5*X^26 + 25*X^25 + 14*X^24 +
      30*X^23 + 31*X^22 + 31*X^21 + 19*X^20 + 21*X^19 + 8*X^18 + 26*X^17 + 11*X^16 + 34*X^15 +
      48*X^14 + 33*X^13 + 20*X^12 + 55*X^11 + 35*X^10 + 50*X^9 + 12*X^8 + 59*X^7 + 29*X^6 + 36*X^5 +
      10*X^4 + 16*X^2 + 2*X + 65) :=
  mul_step (by norm_num) pSeventeenA4s162 pSeventeenA41 ⟨
    25,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s164 : XPow fSeventeenA4 192563389194058619888115757544674
    (53*X^33 + 55*X^32 + 27*X^31 + 54*X^30 + 32*X^29 + 56*X^28 + 60*X^27 + 44*X^26 + 31*X^25 + 8*X^24 +
      18*X^23 + 58*X^22 + 6*X^21 + 32*X^20 + 29*X^19 + 51*X^18 + 16*X^17 + 50*X^16 + 63*X^15 +
      48*X^14 + 16*X^13 + 14*X^12 + 62*X^11 + 51*X^10 + 8*X^9 + 27*X^8 + 11*X^7 + 53*X^6 + 10*X^5 +
      41*X^4 + 17*X^3 + 28*X^2 + 32*X + 17) :=
  sq_step (by norm_num) pSeventeenA4s163 ⟨
    10*X^32 + 5*X^31 + 56*X^30 + 40*X^29 + 16*X^28 + 2*X^27 + 32*X^26 + 60*X^25 + 9*X^24 + 35*X^23 +
      10*X^22 + 11*X^21 + 33*X^20 + 4*X^19 + 20*X^18 + 27*X^17 + 30*X^16 + 24*X^15 + X^14 + 40*X^13 +
      64*X^12 + 10*X^11 + 34*X^10 + 23*X^9 + 65*X^8 + 52*X^7 + 34*X^6 + 56*X^5 + 27*X^4 + 47*X^3 +
      17*X^2 + 36*X + 5,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s165 : XPow fSeventeenA4 192563389194058619888115757544675
    (57*X^33 + 16*X^32 + 61*X^31 + 53*X^30 + 63*X^29 + 20*X^28 + 35*X^27 + 14*X^26 + 16*X^25 + 10*X^24 +
      7*X^23 + 53*X^22 + 25*X^21 + 6*X^20 + 32*X^19 + 37*X^18 + 52*X^17 + 25*X^16 + 29*X^15 +
      56*X^14 + 53*X^13 + 66*X^12 + 36*X^11 + 26*X^10 + 14*X^9 + 25*X^8 + 44*X^7 + 59*X^6 + 18*X^5 +
      23*X^4 + 11*X^3 + 38*X^2 + 17*X + 44) :=
  mul_step (by norm_num) pSeventeenA4s164 pSeventeenA41 ⟨
    53,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s166 : XPow fSeventeenA4 385126778388117239776231515089350
    (30*X^33 + 62*X^32 + 11*X^31 + 40*X^30 + 54*X^29 + 5*X^28 + 5*X^27 + 26*X^26 + 9*X^25 + 51*X^24 +
      50*X^23 + 62*X^22 + 13*X^21 + 14*X^20 + 47*X^19 + 20*X^18 + 42*X^17 + 45*X^16 + 40*X^15 +
      11*X^14 + 7*X^13 + 20*X^12 + 8*X^11 + 23*X^10 + 51*X^9 + 35*X^8 + 17*X^7 + 40*X^6 + 50*X^5 +
      51*X^4 + 14*X^3 + 52*X^2 + 41*X + 4) :=
  sq_step (by norm_num) pSeventeenA4s165 ⟨
    33*X^32 + 39*X^31 + 47*X^30 + 38*X^29 + 66*X^28 + 7*X^27 + 14*X^25 + 20*X^24 + 50*X^23 + 19*X^22 +
      42*X^21 + 11*X^20 + 12*X^19 + 65*X^18 + 13*X^17 + 4*X^16 + 6*X^15 + 23*X^14 + 38*X^13 +
      33*X^12 + 8*X^11 + 52*X^10 + 13*X^9 + 64*X^8 + 45*X^7 + 43*X^6 + 7*X^5 + 6*X^4 + 14*X^3 +
      42*X^2 + 64*X + 30,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s167 : XPow fSeventeenA4 770253556776234479552463030178700
    (33*X^33 + 17*X^32 + 65*X^31 + 45*X^30 + 35*X^29 + 47*X^28 + 48*X^27 + 58*X^26 + 47*X^25 + 17*X^24 +
      18*X^23 + 28*X^22 + 45*X^21 + 2*X^20 + 6*X^19 + 27*X^18 + 38*X^17 + 20*X^16 + 60*X^15 +
      37*X^14 + 13*X^13 + 39*X^12 + 46*X^11 + X^10 + 3*X^9 + 13*X^8 + 58*X^7 + 40*X^6 + 17*X^5 +
      19*X^4 + 29*X^3 + 59*X^2 + 42*X + 12) :=
  sq_step (by norm_num) pSeventeenA4s166 ⟨
    29*X^32 + 50*X^31 + 45*X^30 + 16*X^29 + 35*X^28 + 57*X^27 + 63*X^26 + 5*X^25 + 14*X^24 + 51*X^23 +
      52*X^22 + 22*X^21 + 50*X^20 + 16*X^19 + 39*X^18 + 12*X^17 + 63*X^16 + 33*X^15 + 14*X^14 +
      19*X^13 + 66*X^12 + 54*X^11 + 48*X^10 + 47*X^9 + 53*X^8 + 7*X^7 + 56*X^6 + 9*X^5 + 52*X^4 +
      47*X^3 + 63*X^2 + 24*X + 50,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s168 : XPow fSeventeenA4 1540507113552468959104926060357400
    (64*X^33 + 50*X^32 + 47*X^31 + 39*X^30 + 7*X^29 + 37*X^28 + 49*X^27 + 11*X^26 + 28*X^25 + 19*X^24 +
      9*X^23 + 39*X^22 + 50*X^21 + 51*X^20 + 12*X^18 + 64*X^17 + 30*X^16 + 65*X^15 + 31*X^14 +
      64*X^13 + 20*X^12 + 31*X^11 + 30*X^10 + 52*X^9 + 59*X^7 + 49*X^6 + 31*X^5 + 9*X^4 + 19*X^3 +
      56*X^2 + 35*X + 60) :=
  sq_step (by norm_num) pSeventeenA4s167 ⟨
    17*X^32 + 38*X^31 + 7*X^30 + 27*X^29 + 30*X^28 + 16*X^27 + 64*X^26 + 20*X^25 + 65*X^24 + X^23 +
      42*X^22 + 34*X^21 + 44*X^20 + 15*X^19 + 27*X^18 + 34*X^17 + 27*X^16 + 24*X^15 + 50*X^14 +
      36*X^13 + 3*X^12 + 33*X^11 + 52*X^10 + 18*X^9 + 34*X^8 + 40*X^7 + 42*X^6 + 23*X^5 + 35*X^4 +
      5*X^3 + 59*X^2 + 2*X + 45,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s169 : XPow fSeventeenA4 1540507113552468959104926060357401
    (60*X^33 + 59*X^32 + 7*X^31 + 45*X^30 + 5*X^29 + 50*X^28 + 33*X^27 + 10*X^26 + 59*X^25 + 36*X^24 +
      52*X^23 + 17*X^22 + 16*X^21 + 19*X^20 + 51*X^19 + 35*X^18 + 40*X^17 + 9*X^16 + 3*X^15 +
      63*X^14 + 14*X^13 + 51*X^12 + 22*X^11 + 8*X^10 + 2*X^9 + 62*X^8 + 4*X^7 + 8*X^6 + 28*X^5 +
      49*X^4 + 38*X^3 + 65*X^2 + 60*X + 19) :=
  mul_step (by norm_num) pSeventeenA4s168 pSeventeenA41 ⟨
    64,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s170 : XPow fSeventeenA4 3081014227104937918209852120714802
    (19*X^33 + 52*X^32 + 18*X^31 + 50*X^30 + 39*X^29 + 26*X^28 + 59*X^27 + 13*X^26 + 14*X^25 + 38*X^24 +
      9*X^23 + 42*X^22 + 45*X^21 + 64*X^19 + 28*X^18 + 16*X^17 + 43*X^16 + 51*X^15 + 32*X^14 +
      42*X^13 + 22*X^12 + 65*X^11 + 30*X^10 + 5*X^9 + 22*X^8 + 23*X^7 + 19*X^6 + 60*X^5 + 54*X^4 +
      19*X^3 + 54*X^2 + 63*X + 31) :=
  sq_step (by norm_num) pSeventeenA4s169 ⟨
    49*X^32 + 38*X^31 + 23*X^30 + 21*X^29 + 43*X^28 + 21*X^27 + 64*X^26 + 5*X^25 + 66*X^24 + 30*X^23 +
      59*X^22 + 31*X^21 + 26*X^20 + 27*X^19 + 26*X^18 + 48*X^17 + 10*X^16 + 39*X^15 + 35*X^14 +
      7*X^12 + 49*X^11 + 64*X^10 + 30*X^9 + 54*X^8 + 53*X^7 + 41*X^6 + 11*X^5 + 20*X^4 + 13*X^3 +
      33*X^2 + 8*X + 38,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s171 : XPow fSeventeenA4 6162028454209875836419704241429604
    (59*X^33 + 35*X^32 + 48*X^31 + 20*X^30 + 10*X^29 + 57*X^28 + 7*X^27 + 42*X^26 + 29*X^25 + 38*X^24 +
      64*X^23 + 22*X^22 + 56*X^21 + 48*X^20 + 5*X^19 + 42*X^18 + 47*X^17 + 52*X^16 + 35*X^15 +
      65*X^14 + 21*X^13 + 25*X^12 + 58*X^11 + 23*X^10 + 31*X^9 + 43*X^8 + 4*X^7 + 8*X^6 + 40*X^5 +
      64*X^4 + 40*X^3 + 66*X^2 + 6*X + 37) :=
  sq_step (by norm_num) pSeventeenA4s170 ⟨
    26*X^32 + 58*X^31 + 31*X^30 + 29*X^29 + 62*X^28 + 52*X^27 + 22*X^26 + 53*X^25 + 3*X^24 + 43*X^23 +
      64*X^22 + 10*X^21 + 23*X^20 + 52*X^19 + 24*X^18 + 28*X^17 + 65*X^16 + 30*X^15 + 27*X^14 +
      64*X^13 + 27*X^12 + 29*X^11 + 5*X^10 + 16*X^9 + 56*X^8 + 63*X^7 + 6*X^6 + 14*X^5 + 58*X^4 +
      22*X^3 + 53*X^2 + 41*X + 26,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s172 : XPow fSeventeenA4 12324056908419751672839408482859208
    (50*X^33 + 18*X^32 + 52*X^31 + 23*X^30 + 16*X^29 + 54*X^28 + 2*X^27 + 55*X^26 + 65*X^25 + 42*X^24 +
      53*X^23 + 9*X^22 + 56*X^21 + 17*X^20 + 2*X^19 + 59*X^18 + 7*X^17 + 36*X^16 + 14*X^15 + 40*X^14 +
      22*X^13 + 55*X^12 + 19*X^11 + 25*X^10 + 45*X^9 + 26*X^8 + 6*X^7 + 33*X^6 + 24*X^5 + 53*X^4 +
      45*X^3 + 35*X^2 + 30*X + 49) :=
  sq_step (by norm_num) pSeventeenA4s171 ⟨
    64*X^32 + 53*X^31 + 2*X^30 + 20*X^29 + 8*X^28 + 26*X^27 + 39*X^25 + 20*X^24 + 44*X^23 + 49*X^22 +
      2*X^21 + 42*X^20 + 18*X^19 + 49*X^18 + 25*X^17 + 30*X^16 + 55*X^15 + 59*X^14 + 38*X^13 +
      13*X^12 + 15*X^11 + 24*X^10 + 63*X^9 + 56*X^8 + 19*X^7 + 28*X^6 + X^5 + 30*X^4 + 27*X^3 +
      20*X^2 + 16*X + 18,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s173 : XPow fSeventeenA4 12324056908419751672839408482859209
    (30*X^33 + 53*X^32 + 65*X^31 + 8*X^30 + 29*X^29 + 30*X^28 + X^27 + 30*X^26 + 23*X^25 + 5*X^24 +
      38*X^23 + 3*X^22 + 42*X^21 + 65*X^20 + 12*X^19 + 66*X^18 + 48*X^17 + 54*X^16 + 60*X^15 +
      61*X^14 + 21*X^13 + 43*X^12 + 2*X^11 + 19*X^10 + 15*X^9 + 23*X^8 + 46*X^7 + 50*X^6 + 49*X^5 +
      14*X^4 + 66*X^2 + 49*X + 63) :=
  mul_step (by norm_num) pSeventeenA4s172 pSeventeenA41 ⟨
    50,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s174 : XPow fSeventeenA4 24648113816839503345678816965718418
    (7*X^33 + 63*X^32 + 19*X^31 + 32*X^30 + 29*X^29 + 33*X^28 + 45*X^27 + 66*X^26 + 58*X^25 + 27*X^24 +
      45*X^23 + 48*X^22 + 20*X^21 + 48*X^20 + 59*X^19 + 41*X^18 + 56*X^17 + 8*X^16 + 27*X^15 +
      53*X^14 + 61*X^13 + 39*X^12 + 62*X^11 + 61*X^10 + 5*X^9 + 62*X^8 + 52*X^7 + 13*X^5 + 11*X^4 +
      46*X^3 + 51*X^2 + 60*X + 10) :=
  sq_step (by norm_num) pSeventeenA4s173 ⟨
    29*X^32 + 46*X^31 + 30*X^30 + 3*X^29 + 17*X^28 + 63*X^27 + 28*X^26 + 63*X^25 + 19*X^24 + 59*X^23 +
      19*X^22 + 25*X^21 + 34*X^20 + 15*X^19 + 66*X^18 + 46*X^17 + 66*X^16 + 31*X^15 + 27*X^14 + X^13 +
      65*X^12 + 21*X^11 + 58*X^10 + 44*X^9 + 2*X^8 + 60*X^7 + 27*X^6 + 3*X^5 + 46*X^4 + 9*X^3 + 45*X +
      8,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s175 : XPow fSeventeenA4 49296227633679006691357633931436836
    (32*X^33 + 43*X^32 + 41*X^31 + 10*X^30 + 37*X^29 + 50*X^28 + 41*X^27 + 18*X^26 + 3*X^25 + 22*X^24 +
      20*X^23 + 54*X^22 + 58*X^21 + 28*X^20 + 4*X^19 + X^18 + 4*X^17 + 47*X^16 + 49*X^15 + 48*X^14 +
      28*X^13 + 16*X^12 + 12*X^11 + 56*X^10 + 49*X^9 + 15*X^8 + 10*X^7 + 28*X^6 + 15*X^5 + 29*X^4 +
      4*X^3 + 55*X^2 + 30*X + 48) :=
  sq_step (by norm_num) pSeventeenA4s174 ⟨
    49*X^32 + 4*X^31 + 28*X^30 + 17*X^29 + 10*X^28 + 16*X^27 + 63*X^26 + 58*X^25 + 2*X^24 + 13*X^23 +
      66*X^22 + 60*X^21 + X^20 + 7*X^19 + 44*X^18 + 23*X^17 + 61*X^16 + 23*X^15 + 43*X^14 + 13*X^13 +
      58*X^12 + 61*X^11 + 56*X^10 + 63*X^9 + 3*X^8 + 45*X^7 + 53*X^6 + 20*X^5 + 51*X^4 + 57*X^3 +
      33*X^2 + 19*X + 47,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s176 : XPow fSeventeenA4 49296227633679006691357633931436837
    (48*X^33 + 47*X^32 + 61*X^31 + 56*X^30 + 34*X^29 + 8*X^28 + 29*X^27 + 61*X^26 + 42*X^25 + 27*X^23 +
      8*X^22 + 44*X^21 + 47*X^20 + 54*X^19 + 23*X^18 + 52*X^17 + 21*X^16 + 34*X^15 + 61*X^14 +
      13*X^13 + 22*X^12 + 52*X^11 + 27*X^10 + 16*X^9 + 45*X^8 + 39*X^7 + 37*X^6 + 5*X^5 + 19*X^4 +
      46*X^3 + 45*X^2 + 48*X + 43) :=
  mul_step (by norm_num) pSeventeenA4s175 pSeventeenA41 ⟨
    32,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s177 : XPow fSeventeenA4 98592455267358013382715267862873674
    (35*X^33 + 29*X^32 + 10*X^31 + 39*X^30 + 8*X^29 + 65*X^28 + 35*X^27 + 49*X^26 + 7*X^25 + 38*X^24 +
      21*X^23 + 26*X^22 + 55*X^21 + 66*X^20 + 61*X^19 + 27*X^18 + 40*X^17 + 3*X^16 + 32*X^14 +
      18*X^13 + 23*X^12 + 3*X^11 + 2*X^10 + 40*X^9 + 65*X^8 + 25*X^7 + 2*X^6 + 30*X^5 + 42*X^4 +
      29*X^3 + 46*X^2 + 34*X + 30) :=
  sq_step (by norm_num) pSeventeenA4s176 ⟨
    26*X^32 + 48*X^31 + 29*X^30 + 66*X^29 + 58*X^28 + 44*X^27 + 3*X^26 + 45*X^25 + 17*X^24 + 50*X^23 +
      22*X^22 + 51*X^21 + 27*X^20 + 33*X^19 + 14*X^18 + 46*X^17 + 58*X^16 + 29*X^15 + 15*X^14 +
      53*X^13 + 33*X^12 + 9*X^11 + 24*X^10 + 28*X^9 + 54*X^8 + 14*X^7 + 31*X^6 + 66*X^5 + 7*X^4 +
      20*X^3 + 5*X^2 + 54*X + 58,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s178 : XPow fSeventeenA4 98592455267358013382715267862873675
    (24*X^33 + 4*X^32 + 55*X^31 + 56*X^30 + 14*X^29 + X^28 + 38*X^27 + 16*X^26 + 18*X^25 + 41*X^24 +
      53*X^23 + 38*X^22 + 50*X^21 + 18*X^20 + 41*X^19 + 21*X^18 + 65*X^17 + 28*X^16 + 46*X^15 +
      52*X^14 + 26*X^13 + 60*X^12 + 6*X^11 + 62*X^10 + 64*X^9 + 57*X^8 + 58*X^7 + 8*X^6 + 66*X^5 +
      14*X^4 + 55*X^3 + 19*X^2 + 30*X + 24) :=
  mul_step (by norm_num) pSeventeenA4s177 pSeventeenA41 ⟨
    35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s179 : XPow fSeventeenA4 197184910534716026765430535725747350
    (25*X^33 + 64*X^32 + 62*X^31 + 36*X^30 + 65*X^29 + 52*X^28 + 39*X^27 + 56*X^26 + 52*X^25 + 52*X^24 +
      5*X^23 + 51*X^22 + 34*X^21 + 38*X^20 + 13*X^19 + 8*X^18 + 15*X^17 + 30*X^16 + 6*X^15 + 11*X^14 +
      20*X^13 + 14*X^11 + 14*X^10 + X^9 + 21*X^8 + 49*X^7 + 18*X^6 + 50*X^5 + 61*X^4 + 44*X^3 +
      35*X^2 + 22*X + 23) :=
  sq_step (by norm_num) pSeventeenA4s178 ⟨
    40*X^32 + 14*X^31 + 15*X^30 + 54*X^29 + 19*X^28 + 18*X^27 + 60*X^26 + 5*X^25 + 54*X^24 + 65*X^23 +
      29*X^22 + 36*X^21 + 14*X^20 + 2*X^19 + 53*X^18 + 41*X^17 + 51*X^16 + 48*X^15 + X^14 + 40*X^13 +
      20*X^12 + 60*X^11 + 50*X^10 + 11*X^9 + 41*X^8 + 47*X^7 + 27*X^6 + 32*X^5 + 10*X^4 + 24*X^3 +
      5*X^2 + 37*X + 45,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s180 : XPow fSeventeenA4 197184910534716026765430535725747351
    (3*X^33 + 29*X^32 + 57*X^31 + 61*X^30 + 6*X^29 + 53*X^28 + 29*X^27 + X^26 + 9*X^25 + 48*X^24 +
      32*X^23 + 41*X^22 + 17*X^21 + 11*X^20 + 18*X^19 + 11*X^18 + 36*X^17 + 26*X^16 + 21*X^15 +
      6*X^14 + 50*X^13 + 26*X^12 + 36*X^11 + 55*X^10 + 49*X^9 + 24*X^8 + 58*X^7 + 63*X^6 + 59*X^5 +
      62*X^4 + 51*X^3 + 40*X^2 + 23*X + 65) :=
  mul_step (by norm_num) pSeventeenA4s179 pSeventeenA41 ⟨
    25,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s181 : XPow fSeventeenA4 394369821069432053530861071451494702
    (19*X^33 + 53*X^32 + 30*X^31 + 33*X^30 + 38*X^29 + 27*X^28 + 2*X^27 + 32*X^26 + 62*X^25 + 59*X^23 +
      40*X^22 + 62*X^21 + X^20 + 36*X^19 + 24*X^18 + 33*X^17 + 50*X^16 + 39*X^15 + 44*X^14 + 54*X^13 +
      15*X^12 + 24*X^11 + 43*X^10 + 22*X^9 + 48*X^8 + 4*X^7 + 25*X^6 + 65*X^5 + 46*X^4 + 36*X^3 +
      40*X^2 + 6*X + 27) :=
  sq_step (by norm_num) pSeventeenA4s180 ⟨
    9*X^32 + 10*X^31 + 64*X^30 + 53*X^29 + 18*X^28 + 27*X^27 + 24*X^26 + 33*X^25 + 3*X^24 + 26*X^23 +
      35*X^22 + 16*X^21 + 52*X^20 + 46*X^19 + 16*X^18 + 49*X^17 + 34*X^16 + 23*X^15 + 31*X^14 +
      59*X^13 + 64*X^12 + 59*X^11 + 47*X^10 + 49*X^9 + 15*X^8 + 42*X^7 + 4*X^6 + 40*X^5 + 54*X^4 +
      42*X^3 + 51*X^2 + 48*X + 14,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s182 : XPow fSeventeenA4 788739642138864107061722142902989404
    (30*X^33 + 51*X^32 + 35*X^31 + 40*X^30 + 66*X^29 + 51*X^28 + 38*X^27 + 21*X^26 + 25*X^25 + 56*X^24 +
      39*X^23 + X^22 + 65*X^21 + 21*X^20 + 30*X^19 + 39*X^18 + 17*X^17 + 40*X^16 + 32*X^15 + 49*X^14 +
      37*X^13 + 29*X^12 + 35*X^11 + 64*X^10 + 52*X^9 + 34*X^8 + 41*X^7 + 24*X^6 + 16*X^5 + 51*X^4 +
      13*X^3 + 15*X^2 + 17*X + 44) :=
  sq_step (by norm_num) pSeventeenA4s181 ⟨
    26*X^32 + 29*X^31 + 41*X^30 + 59*X^29 + 12*X^28 + 48*X^27 + 33*X^26 + 3*X^25 + 22*X^24 + 9*X^23 +
      22*X^21 + 17*X^20 + 30*X^19 + 53*X^18 + 36*X^17 + 33*X^16 + 11*X^15 + 41*X^14 + 15*X^13 +
      55*X^12 + 66*X^11 + 64*X^10 + 61*X^9 + 42*X^8 + 53*X^7 + 50*X^6 + 50*X^5 + 15*X^4 + 46*X^3 +
      6*X^2 + 52*X + 20,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s183 : XPow fSeventeenA4 788739642138864107061722142902989405
    (18*X^33 + 49*X^32 + 25*X^31 + 21*X^30 + 36*X^29 + 28*X^28 + 2*X^27 + 4*X^26 + 58*X^25 + 37*X^24 +
      5*X^23 + 60*X^22 + 36*X^21 + 41*X^20 + 51*X^19 + 39*X^18 + 7*X^17 + 56*X^16 + 61*X^15 +
      47*X^14 + 22*X^13 + 36*X^12 + 10*X^11 + 23*X^10 + 14*X^9 + 11*X^8 + 5*X^7 + 45*X^6 + 62*X^5 +
      48*X^4 + 61*X^3 + 52*X^2 + 44*X + 11) :=
  mul_step (by norm_num) pSeventeenA4s182 pSeventeenA41 ⟨
    30,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s184 : XPow fSeventeenA4 1577479284277728214123444285805978810
    (65*X^33 + 18*X^32 + 49*X^30 + 63*X^29 + 51*X^28 + 9*X^27 + 43*X^26 + 32*X^25 + 24*X^24 + 37*X^23 +
      X^22 + 65*X^21 + 32*X^20 + 45*X^19 + X^18 + 8*X^17 + 18*X^16 + 46*X^15 + 5*X^14 + 19*X^13 +
      33*X^12 + 37*X^11 + 8*X^10 + 42*X^9 + 21*X^8 + 22*X^7 + 18*X^6 + 65*X^5 + 56*X^4 + 34*X^3 +
      19*X^2 + 43*X + 66) :=
  sq_step (by norm_num) pSeventeenA4s183 ⟨
    56*X^32 + 14*X^31 + 60*X^30 + 41*X^29 + 5*X^28 + 11*X^27 + 29*X^26 + 56*X^25 + 27*X^24 + 2*X^23 +
      54*X^22 + 43*X^21 + 2*X^20 + 53*X^19 + 58*X^18 + 3*X^17 + 8*X^16 + 6*X^15 + 42*X^14 + 43*X^13 +
      39*X^12 + 44*X^11 + 19*X^10 + 53*X^9 + 61*X^8 + 25*X^7 + 46*X^6 + 38*X^5 + 59*X^4 + 35*X^3 +
      29*X^2 + 5*X + 51,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s185 : XPow fSeventeenA4 1577479284277728214123444285805978811
    (47*X^33 + 8*X^32 + 50*X^31 + 66*X^30 + 52*X^29 + 32*X^28 + 13*X^27 + 20*X^26 + 6*X^25 + 55*X^24 +
      32*X^23 + 43*X^22 + 31*X^21 + 13*X^20 + 27*X^19 + 11*X^18 + 47*X^17 + 31*X^16 + 31*X^15 +
      63*X^14 + 29*X^13 + 28*X^12 + 25*X^11 + 35*X^10 + 24*X^8 + 55*X^7 + 5*X^6 + 24*X^5 + 54*X^4 +
      7*X^3 + 63*X^2 + 66*X + 35) :=
  mul_step (by norm_num) pSeventeenA4s184 pSeventeenA41 ⟨
    65,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s186 : XPow fSeventeenA4 3154958568555456428246888571611957622
    (33*X^33 + 63*X^32 + 9*X^31 + 61*X^30 + 47*X^29 + 59*X^28 + 8*X^27 + 47*X^26 + 33*X^25 + 62*X^24 +
      6*X^23 + 11*X^22 + 50*X^21 + 63*X^20 + 4*X^19 + 57*X^18 + 10*X^17 + 48*X^15 + 2*X^14 + 10*X^13 +
      41*X^12 + 66*X^11 + 13*X^10 + 51*X^9 + 49*X^8 + 60*X^7 + 7*X^6 + 37*X^5 + 61*X^4 + 19*X^3 +
      27*X^2 + 63*X + 23) :=
  sq_step (by norm_num) pSeventeenA4s185 ⟨
    65*X^32 + 44*X^31 + 47*X^30 + 17*X^29 + 51*X^28 + 30*X^27 + 54*X^26 + 19*X^25 + 52*X^24 + 11*X^23 +
      49*X^22 + 35*X^21 + 61*X^20 + 24*X^19 + 12*X^18 + 59*X^17 + 65*X^16 + 45*X^15 + 43*X^14 +
      15*X^13 + 22*X^12 + 49*X^11 + 9*X^10 + 15*X^9 + 61*X^8 + 41*X^7 + 36*X^6 + 39*X^5 + 16*X^4 +
      5*X^3 + 13*X^2 + 46*X + 17,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s187 : XPow fSeventeenA4 3154958568555456428246888571611957623
    (20*X^33 + 11*X^32 + 11*X^31 + 31*X^30 + 9*X^29 + 64*X^28 + 6*X^27 + 30*X^26 + 24*X^25 + 44*X^24 +
      2*X^23 + 11*X^22 + 46*X^21 + 63*X^20 + 30*X^19 + 61*X^18 + 24*X^17 + 61*X^16 + 42*X^15 +
      21*X^14 + 40*X^13 + 47*X^12 + 34*X^11 + 66*X^10 + 27*X^9 + 27*X^8 + 33*X^7 + 22*X^6 + 53*X^5 +
      24*X^4 + 24*X^3 + X^2 + 23*X + 59) :=
  mul_step (by norm_num) pSeventeenA4s186 pSeventeenA41 ⟨
    33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s188 : XPow fSeventeenA4 6309917137110912856493777143223915246
    (23*X^33 + 56*X^32 + 3*X^31 + 3*X^30 + 26*X^29 + 65*X^28 + 58*X^27 + 27*X^26 + 20*X^25 + 34*X^24 +
      12*X^23 + 44*X^22 + 6*X^21 + 29*X^20 + 15*X^19 + X^18 + 14*X^17 + 2*X^16 + 14*X^15 + 7*X^14 +
      63*X^13 + 46*X^12 + 29*X^11 + 2*X^10 + 11*X^9 + 40*X^8 + 26*X^7 + 49*X^6 + 5*X^5 + 52*X^4 +
      34*X^3 + 18*X^2 + 16*X + 49) :=
  sq_step (by norm_num) pSeventeenA4s187 ⟨
    65*X^32 + 33*X^30 + 33*X^29 + 53*X^28 + 45*X^27 + 57*X^26 + 25*X^25 + 44*X^24 + 24*X^23 + 62*X^22 +
      49*X^21 + 20*X^20 + 12*X^19 + 58*X^18 + 38*X^17 + 66*X^16 + 64*X^15 + 61*X^14 + 46*X^13 +
      64*X^12 + 30*X^11 + 24*X^10 + 3*X^9 + 54*X^8 + 60*X^7 + 24*X^6 + 26*X^5 + 47*X^4 + 14*X^3 +
      36*X^2 + 24*X + 20,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s189 : XPow fSeventeenA4 12619834274221825712987554286447830492
    (30*X^33 + 66*X^32 + 57*X^31 + 64*X^30 + 47*X^29 + 9*X^28 + 62*X^27 + 5*X^26 + 64*X^25 + 34*X^24 +
      11*X^23 + 45*X^22 + 59*X^21 + 56*X^20 + 15*X^19 + 5*X^18 + 9*X^17 + 55*X^16 + 59*X^15 +
      47*X^14 + X^13 + 46*X^12 + 36*X^11 + 31*X^10 + 45*X^9 + 56*X^8 + 42*X^7 + 10*X^6 + 2*X^5 +
      48*X^4 + 51*X^3 + 11*X^2 + 22*X + 36) :=
  sq_step (by norm_num) pSeventeenA4s188 ⟨
    60*X^32 + 31*X^31 + 5*X^30 + 13*X^29 + 21*X^28 + 24*X^27 + 17*X^26 + 44*X^25 + 43*X^24 + 54*X^23 +
      5*X^22 + 49*X^21 + 27*X^20 + 28*X^19 + 51*X^18 + 47*X^17 + 3*X^16 + 25*X^15 + 42*X^14 +
      36*X^13 + 15*X^12 + 23*X^11 + 62*X^10 + 26*X^9 + 44*X^8 + 58*X^7 + 22*X^6 + 47*X^5 + 22*X^4 +
      56*X^3 + 60*X^2 + 29*X + 49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s190 : XPow fSeventeenA4 25239668548443651425975108572895660984
    (19*X^33 + 29*X^32 + 29*X^31 + 52*X^30 + 7*X^29 + 33*X^28 + 47*X^27 + 25*X^26 + 26*X^25 + 8*X^24 +
      20*X^23 + 29*X^22 + 58*X^21 + 52*X^20 + 20*X^19 + 51*X^18 + 50*X^17 + 36*X^16 + 26*X^15 +
      31*X^14 + 57*X^13 + 20*X^12 + 5*X^11 + 51*X^10 + 31*X^9 + 55*X^8 + 3*X^7 + 8*X^6 + 47*X^5 +
      48*X^4 + 50*X^3 + 4*X^2 + 58*X + 23) :=
  sq_step (by norm_num) pSeventeenA4s189 ⟨
    29*X^32 + 22*X^31 + 38*X^30 + 24*X^29 + 60*X^28 + 43*X^27 + 20*X^26 + 19*X^25 + 45*X^24 + 63*X^23 +
      19*X^22 + 8*X^21 + 3*X^20 + 3*X^19 + 36*X^18 + 42*X^17 + 63*X^16 + 29*X^15 + 4*X^14 + 32*X^13 +
      49*X^12 + 20*X^11 + 10*X^10 + 7*X^9 + 14*X^8 + 47*X^7 + 59*X^6 + 66*X^4 + 24*X^3 + 21*X^2 +
      47*X,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s191 : XPow fSeventeenA4 50479337096887302851950217145791321968
    (49*X^33 + 26*X^32 + 14*X^31 + 60*X^30 + 60*X^29 + 5*X^28 + 19*X^27 + 36*X^26 + 26*X^25 + 37*X^24 +
      59*X^23 + 64*X^22 + 59*X^21 + 65*X^20 + 56*X^19 + 41*X^18 + 56*X^17 + 18*X^16 + 4*X^15 +
      31*X^14 + 48*X^13 + 25*X^12 + 63*X^11 + 26*X^10 + 12*X^9 + 12*X^8 + 17*X^7 + 41*X^6 + 53*X^5 +
      34*X^4 + 6*X^3 + 13*X^2 + 54*X + 39) :=
  sq_step (by norm_num) pSeventeenA4s190 ⟨
    26*X^32 + 55*X^31 + 3*X^30 + 65*X^29 + 20*X^28 + 9*X^27 + 5*X^26 + 29*X^25 + 39*X^24 + 61*X^23 +
      X^22 + 66*X^21 + 13*X^20 + 15*X^19 + 20*X^18 + 23*X^17 + 42*X^16 + 62*X^15 + 65*X^14 + 16*X^13 +
      66*X^12 + 60*X^11 + 59*X^10 + 50*X^9 + 15*X^8 + 19*X^7 + 36*X^6 + 3*X^5 + 61*X^4 + 5*X^3 +
      52*X^2 + 46*X + 28,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s192 : XPow fSeventeenA4 100958674193774605703900434291582643936
    (11*X^33 + 17*X^32 + 9*X^31 + 31*X^30 + 12*X^29 + 15*X^28 + 23*X^27 + 15*X^26 + 64*X^25 + 40*X^24 +
      59*X^23 + 64*X^22 + 66*X^21 + 23*X^20 + 55*X^19 + 42*X^18 + 29*X^17 + 32*X^16 + 12*X^15 +
      13*X^14 + 23*X^13 + 32*X^12 + 52*X^11 + 62*X^10 + 19*X^9 + 33*X^8 + 11*X^7 + 33*X^6 + 59*X^5 +
      46*X^4 + 62*X^3 + 7*X^2 + 25*X + 40) :=
  sq_step (by norm_num) pSeventeenA4s191 ⟨
    56*X^32 + 61*X^31 + 35*X^30 + 33*X^29 + 21*X^28 + 60*X^27 + 43*X^26 + 32*X^25 + 7*X^24 + 16*X^23 +
      55*X^22 + 14*X^21 + 43*X^20 + 8*X^19 + 11*X^18 + 10*X^17 + X^16 + 8*X^15 + 56*X^14 + 24*X^13 +
      6*X^12 + 49*X^11 + 31*X^10 + 52*X^9 + 31*X^8 + 61*X^7 + 15*X^6 + 47*X^5 + 36*X^4 + 3*X^3 +
      44*X^2 + 44*X + 54,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s193 : XPow fSeventeenA4 201917348387549211407800868583165287872
    (57*X^33 + 20*X^32 + 64*X^31 + 19*X^30 + 34*X^29 + 44*X^28 + 50*X^27 + 59*X^26 + 59*X^25 + 63*X^24 +
      33*X^23 + 46*X^22 + X^21 + 28*X^20 + 27*X^19 + 54*X^18 + 28*X^17 + 43*X^16 + 25*X^15 + 59*X^14 +
      18*X^13 + 56*X^12 + 15*X^11 + 39*X^10 + 14*X^9 + 32*X^8 + 41*X^7 + 14*X^6 + 27*X^5 + 33*X^4 +
      26*X^3 + 62*X^2 + 55*X + 31) :=
  sq_step (by norm_num) pSeventeenA4s192 ⟨
    54*X^32 + 60*X^31 + 4*X^30 + 60*X^29 + 66*X^27 + 13*X^26 + 60*X^25 + 48*X^24 + 32*X^23 + 28*X^22 +
      24*X^21 + 32*X^20 + 18*X^19 + 35*X^18 + 35*X^17 + 54*X^16 + 3*X^15 + 11*X^14 + 56*X^13 +
      40*X^12 + 62*X^11 + 40*X^10 + 35*X^9 + 18*X^8 + 38*X^7 + 56*X^6 + 14*X^5 + 12*X^4 + 65*X^3 +
      2*X^2 + 25*X + 15,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s194 : XPow fSeventeenA4 403834696775098422815601737166330575744
    (18*X^33 + 44*X^32 + 15*X^31 + 43*X^30 + 42*X^29 + 42*X^28 + 44*X^27 + 45*X^26 + 39*X^25 + 32*X^24 +
      49*X^22 + 35*X^21 + 7*X^20 + 32*X^19 + 10*X^18 + 50*X^17 + 55*X^16 + 35*X^15 + 48*X^14 +
      8*X^13 + 51*X^12 + 65*X^11 + 63*X^10 + 66*X^9 + 66*X^8 + 65*X^7 + 6*X^6 + 59*X^5 + 8*X^4 +
      52*X^3 + 11*X^2 + 57*X + 47) :=
  sq_step (by norm_num) pSeventeenA4s193 ⟨
    33*X^32 + 26*X^31 + 18*X^30 + 23*X^29 + 23*X^28 + 10*X^27 + 48*X^26 + 47*X^25 + 49*X^24 + 22*X^23 +
      18*X^22 + 43*X^21 + 18*X^20 + 20*X^19 + 33*X^18 + 58*X^17 + 19*X^16 + 53*X^15 + 50*X^14 +
      16*X^13 + 2*X^12 + 22*X^11 + 65*X^10 + 4*X^9 + 9*X^8 + 51*X^7 + 65*X^6 + 22*X^5 + 51*X^4 +
      10*X^3 + 12*X^2 + 4*X + 35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s195 : XPow fSeventeenA4 807669393550196845631203474332661151488
    (37*X^33 + 58*X^32 + 29*X^31 + 43*X^30 + 24*X^29 + 11*X^28 + 57*X^27 + 34*X^26 + 18*X^25 + 60*X^24 +
      13*X^23 + 63*X^22 + 60*X^21 + 39*X^20 + 8*X^19 + 29*X^18 + X^17 + 55*X^16 + X^15 + 41*X^14 +
      27*X^13 + 39*X^12 + 55*X^11 + 22*X^10 + 43*X^9 + 64*X^8 + 29*X^7 + 10*X^6 + 64*X^5 + 23*X^4 +
      33*X^3 + 22*X^2 + 39*X) :=
  sq_step (by norm_num) pSeventeenA4s194 ⟨
    56*X^32 + 35*X^31 + 36*X^30 + 34*X^29 + 59*X^28 + 48*X^27 + 58*X^26 + 22*X^25 + X^24 + 7*X^23 +
      16*X^22 + 12*X^21 + 4*X^20 + 42*X^19 + 23*X^18 + 63*X^17 + 52*X^16 + 57*X^15 + 61*X^14 +
      47*X^13 + 43*X^12 + 5*X^11 + 37*X^10 + 46*X^9 + 24*X^8 + 55*X^7 + 29*X^6 + 27*X^5 + 63*X^4 +
      61*X^3 + 7*X^2 + 57*X + 42,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s196 : XPow fSeventeenA4 807669393550196845631203474332661151489
    (24*X^33 + 15*X^32 + 58*X^31 + 2*X^30 + 26*X^29 + 53*X^27 + 39*X^26 + 58*X^25 + 15*X^24 + 59*X^23 +
      65*X^22 + 24*X^21 + 64*X^20 + 17*X^19 + 46*X^18 + 21*X^17 + 44*X^16 + 29*X^15 + 17*X^14 +
      46*X^13 + 54*X^12 + 9*X^11 + 5*X^10 + 17*X^9 + 59*X^8 + 29*X^7 + 35*X^6 + 12*X^5 + 65*X^4 +
      43*X^3 + 4*X^2 + 56) :=
  mul_step (by norm_num) pSeventeenA4s195 pSeventeenA41 ⟨
    37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s197 : XPow fSeventeenA4 1615338787100393691262406948665322302978
    (X^33 + 21*X^32 + 61*X^31 + 66*X^30 + 24*X^29 + 42*X^28 + 24*X^27 + 59*X^26 + 42*X^25 + 19*X^24 +
      57*X^23 + 53*X^22 + 39*X^21 + 51*X^20 + 19*X^19 + 42*X^18 + 4*X^17 + 40*X^16 + 2*X^15 +
      21*X^14 + 52*X^13 + 11*X^12 + 26*X^11 + 10*X^10 + 58*X^9 + 11*X^8 + 65*X^7 + 5*X^6 + 8*X^5 +
      3*X^4 + 44*X^3 + 51*X^2 + 62*X + 28) :=
  sq_step (by norm_num) pSeventeenA4s196 ⟨
    40*X^32 + 6*X^31 + 15*X^30 + 60*X^28 + 5*X^27 + 9*X^26 + 23*X^25 + 55*X^24 + 18*X^23 + 17*X^22 +
      65*X^21 + 52*X^20 + 21*X^19 + 4*X^18 + 43*X^17 + 55*X^16 + 29*X^15 + 23*X^14 + 60*X^13 +
      31*X^12 + 48*X^11 + 59*X^10 + 53*X^9 + 41*X^8 + 56*X^7 + 28*X^6 + 18*X^5 + 18*X^4 + 15*X^2 +
      29*X + 57,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s198 : XPow fSeventeenA4 1615338787100393691262406948665322302979
    (40*X^33 + 57*X^32 + 32*X^31 + 56*X^30 + 8*X^29 + 46*X^28 + 7*X^27 + 48*X^26 + 28*X^25 + 48*X^24 +
      4*X^23 + 50*X^22 + 18*X^21 + 35*X^20 + 29*X^19 + 36*X^18 + 59*X^17 + 43*X^16 + 8*X^15 +
      30*X^14 + 13*X^13 + 64*X^12 + 35*X^11 + 28*X^10 + 55*X^9 + 64*X^8 + 20*X^7 + 38*X^6 + 19*X^5 +
      34*X^4 + 57*X^3 + 52*X^2 + 28*X + 16) :=
  mul_step (by norm_num) pSeventeenA4s197 pSeventeenA41 ⟨
    1,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s199 : XPow fSeventeenA4 3230677574200787382524813897330644605958
    (65*X^33 + 12*X^32 + 20*X^31 + 28*X^30 + 33*X^29 + 38*X^28 + 3*X^27 + 24*X^26 + 27*X^25 + 9*X^24 +
      42*X^23 + 30*X^22 + 48*X^21 + 36*X^20 + 66*X^19 + 64*X^18 + 61*X^17 + 23*X^16 + 12*X^15 +
      57*X^14 + 58*X^13 + 31*X^12 + 29*X^11 + 59*X^10 + 15*X^9 + 56*X^8 + 14*X^7 + 28*X^6 + 16*X^5 +
      23*X^4 + 15*X^3 + 10*X^2 + 41*X + 35) :=
  sq_step (by norm_num) pSeventeenA4s198 ⟨
    59*X^32 + 53*X^31 + 14*X^30 + 12*X^29 + 65*X^28 + X^27 + 37*X^26 + 15*X^25 + 59*X^24 + 53*X^23 +
      15*X^22 + 23*X^21 + 7*X^20 + 13*X^18 + 32*X^17 + 36*X^16 + 65*X^15 + 16*X^14 + 12*X^13 +
      45*X^12 + 59*X^11 + 24*X^10 + 65*X^9 + 7*X^8 + 31*X^7 + 61*X^6 + 62*X^5 + 53*X^4 + 18*X^3 +
      29*X^2 + X + 49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s200 : XPow fSeventeenA4 3230677574200787382524813897330644605959
    (41*X^33 + 28*X^32 + 29*X^31 + 36*X^30 + 39*X^29 + 26*X^28 + 61*X^27 + 15*X^26 + 58*X^25 + 60*X^24 +
      61*X^23 + 26*X^22 + 35*X^21 + 34*X^20 + 23*X^19 + 64*X^18 + 52*X^17 + 64*X^16 + 16*X^15 +
      35*X^14 + 27*X^13 + 20*X^12 + 9*X^11 + 8*X^10 + 35*X^9 + 16*X^8 + 65*X^7 + 23*X^6 + 58*X^5 +
      35*X^4 + 65*X^3 + 61*X^2 + 35*X + 35) :=
  mul_step (by norm_num) pSeventeenA4s199 pSeventeenA41 ⟨
    65,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s201 : XPow fSeventeenA4 6461355148401574765049627794661289211918
    (2*X^33 + 61*X^32 + 16*X^31 + 64*X^30 + 33*X^29 + 21*X^28 + 34*X^27 + 11*X^26 + 62*X^25 + 52*X^24 +
      42*X^23 + 59*X^22 + 10*X^21 + 27*X^20 + 10*X^19 + 28*X^18 + 3*X^17 + 29*X^16 + 49*X^15 +
      15*X^14 + 52*X^13 + 66*X^12 + 13*X^11 + 37*X^10 + 21*X^9 + 7*X^8 + 60*X^7 + 45*X^6 + 36*X^5 +
      63*X^4 + 4*X^3 + 54*X^2 + 17*X + 28) :=
  sq_step (by norm_num) pSeventeenA4s200 ⟨
    6*X^32 + 65*X^31 + 18*X^30 + 32*X^29 + 17*X^28 + 24*X^27 + 42*X^26 + 30*X^25 + 45*X^24 + 25*X^23 +
      39*X^22 + 32*X^21 + 60*X^20 + 31*X^19 + 29*X^18 + 37*X^17 + 64*X^16 + X^15 + 61*X^14 + 36*X^13 +
      X^12 + 9*X^11 + 57*X^10 + 62*X^9 + 24*X^8 + 15*X^7 + 4*X^6 + 13*X^5 + 11*X^4 + 7*X^3 + 28*X +
      55,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s202 : XPow fSeventeenA4 12922710296803149530099255589322578423836
    (17*X^33 + 38*X^32 + 6*X^31 + 46*X^30 + 6*X^29 + 64*X^28 + 6*X^27 + 14*X^26 + 51*X^25 + 31*X^24 +
      X^23 + 31*X^22 + 19*X^21 + 12*X^20 + 8*X^19 + 28*X^18 + 50*X^17 + 12*X^16 + 23*X^15 + 64*X^14 +
      X^13 + 25*X^12 + 54*X^11 + 63*X^10 + 17*X^9 + 44*X^8 + 63*X^7 + 63*X^6 + 12*X^5 + 51*X^4 +
      33*X^3 + 22*X^2 + 7*X + 62) :=
  sq_step (by norm_num) pSeventeenA4s201 ⟨
    4*X^32 + 52*X^31 + 55*X^29 + 30*X^28 + 63*X^27 + 17*X^26 + 48*X^25 + 26*X^24 + 60*X^23 + 51*X^22 +
      56*X^21 + 33*X^20 + 34*X^19 + 32*X^18 + 58*X^16 + 41*X^15 + 6*X^14 + 40*X^13 + 60*X^12 +
      5*X^11 + 63*X^10 + 30*X^9 + 9*X^8 + 8*X^7 + 64*X^6 + 63*X^5 + 41*X^4 + 36*X^3 + 54*X^2 + 54*X +
      47,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s203 : XPow fSeventeenA4 25845420593606299060198511178645156847672
    (31*X^33 + 44*X^32 + 53*X^31 + 49*X^30 + 17*X^29 + 49*X^28 + 35*X^27 + 45*X^25 + 22*X^24 + 36*X^23 +
      50*X^22 + 21*X^21 + 22*X^20 + 8*X^19 + 19*X^18 + 53*X^17 + 31*X^16 + 56*X^15 + 56*X^14 +
      39*X^13 + 36*X^12 + 42*X^11 + 55*X^10 + 20*X^9 + 40*X^8 + 17*X^7 + 50*X^6 + 33*X^5 + 38*X^4 +
      61*X^3 + 54*X^2 + 2*X + 22) :=
  sq_step (by norm_num) pSeventeenA4s202 ⟨
    21*X^32 + 16*X^31 + 59*X^30 + 18*X^29 + 17*X^28 + 21*X^27 + 4*X^26 + 32*X^25 + 17*X^24 + 30*X^23 +
      65*X^22 + 28*X^21 + 31*X^20 + 12*X^19 + 38*X^18 + X^17 + 5*X^16 + 34*X^15 + 15*X^14 + 31*X^13 +
      X^12 + 12*X^11 + X^10 + 8*X^9 + 6*X^8 + 37*X^7 + 49*X^6 + 64*X^5 + 58*X^4 + 40*X^3 + 4*X^2 +
      38*X + 4,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s204 : XPow fSeventeenA4 51690841187212598120397022357290313695344
    (61*X^33 + 13*X^32 + 2*X^31 + 54*X^30 + 44*X^29 + 30*X^28 + 15*X^27 + 57*X^26 + 61*X^25 + 66*X^24 +
      10*X^23 + 55*X^22 + 38*X^21 + 59*X^20 + 9*X^19 + 46*X^18 + 52*X^17 + 39*X^16 + 35*X^15 +
      55*X^14 + 66*X^13 + 27*X^12 + 60*X^11 + 19*X^10 + 8*X^9 + 46*X^8 + 7*X^7 + 12*X^6 + 30*X^5 +
      39*X^4 + 37*X^3 + 36*X^2 + 2*X + 52) :=
  sq_step (by norm_num) pSeventeenA4s203 ⟨
    23*X^32 + 16*X^31 + 7*X^30 + 21*X^29 + 28*X^28 + 20*X^27 + 40*X^26 + 12*X^25 + 35*X^24 + 51*X^23 +
      55*X^22 + 19*X^21 + 19*X^20 + 29*X^19 + 3*X^18 + 33*X^17 + 26*X^16 + 6*X^15 + 9*X^14 + 46*X^13 +
      44*X^12 + 40*X^11 + 16*X^10 + 26*X^9 + 52*X^8 + 26*X^7 + 30*X^6 + 30*X^5 + 42*X^4 + 55*X^3 +
      46*X^2 + 3*X + 40,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s205 : XPow fSeventeenA4 103381682374425196240794044714580627390688
    (30*X^33 + 11*X^32 + 11*X^31 + 37*X^30 + 54*X^29 + 15*X^28 + 59*X^27 + 10*X^26 + 59*X^25 + 19*X^24 +
      11*X^23 + 23*X^22 + 22*X^21 + 48*X^20 + 12*X^19 + 36*X^18 + 36*X^17 + 57*X^16 + 5*X^15 +
      27*X^14 + 58*X^13 + 58*X^12 + 46*X^11 + 31*X^10 + 60*X^9 + 2*X^8 + 29*X^7 + 46*X^6 + 50*X^5 +
      22*X^4 + 43*X^3 + 60*X^2 + 35*X + 55) :=
  sq_step (by norm_num) pSeventeenA4s204 ⟨
    36*X^32 + 59*X^31 + 50*X^30 + 33*X^29 + 51*X^28 + 64*X^27 + 15*X^26 + 47*X^25 + 51*X^24 + 48*X^23 +
      39*X^22 + 40*X^21 + 34*X^20 + 17*X^19 + 66*X^18 + 49*X^17 + 23*X^16 + 30*X^15 + 64*X^14 +
      62*X^13 + 5*X^12 + 10*X^11 + 61*X^10 + 50*X^9 + 48*X^8 + 17*X^7 + 53*X^6 + 63*X^5 + 16*X^4 +
      65*X^3 + 34*X^2 + 52*X + 48,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s206 : XPow fSeventeenA4 103381682374425196240794044714580627390689
    (45*X^33 + 25*X^32 + 22*X^31 + 9*X^30 + 49*X^28 + 58*X^27 + 38*X^26 + 21*X^25 + 9*X^24 + 27*X^23 +
      17*X^22 + 63*X^21 + 23*X^20 + 48*X^19 + 58*X^18 + 24*X^17 + 29*X^16 + 39*X^15 + X^14 + 51*X^13 +
      47*X^12 + 44*X^11 + 31*X^10 + 49*X^9 + 66*X^8 + 27*X^7 + 12*X^6 + 33*X^5 + 11*X^4 + 39*X^3 +
      3*X^2 + 55*X + 11) :=
  mul_step (by norm_num) pSeventeenA4s205 pSeventeenA41 ⟨
    30,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s207 : XPow fSeventeenA4 206763364748850392481588089429161254781378
    (X^33 + 18*X^32 + 43*X^31 + 36*X^30 + 45*X^29 + 42*X^28 + 3*X^27 + 9*X^26 + 25*X^25 + 57*X^24 +
      55*X^23 + 10*X^22 + 54*X^21 + 25*X^20 + 64*X^19 + 2*X^18 + 16*X^17 + 30*X^16 + 18*X^15 +
      26*X^14 + 62*X^13 + 57*X^12 + 8*X^11 + X^10 + 23*X^9 + 10*X^8 + 11*X^7 + 52*X^6 + 43*X^5 +
      64*X^4 + 63*X^3 + 33*X^2 + 40*X + 31) :=
  sq_step (by norm_num) pSeventeenA4s206 ⟨
    15*X^32 + 56*X^31 + 58*X^30 + 15*X^28 + 46*X^27 + 3*X^26 + 21*X^25 + 23*X^24 + 28*X^23 + 30*X^22 +
      54*X^21 + 16*X^20 + 48*X^19 + 16*X^18 + 10*X^17 + 64*X^16 + 59*X^15 + 10*X^14 + 21*X^13 +
      54*X^12 + 59*X^11 + 39*X^10 + 33*X^9 + 59*X^8 + 45*X^7 + 66*X^6 + 43*X^5 + 62*X^4 + 18*X^3 +
      43*X^2 + 19*X + 53,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s208 : XPow fSeventeenA4 206763364748850392481588089429161254781379
    (37*X^33 + 39*X^32 + 2*X^31 + 10*X^30 + 8*X^29 + 25*X^28 + 24*X^27 + 31*X^26 + 66*X^25 + 46*X^24 +
      28*X^23 + 65*X^22 + 59*X^21 + 13*X^20 + 56*X^19 + 48*X^18 + 49*X^17 + 59*X^16 + 13*X^15 +
      40*X^14 + 59*X^13 + 46*X^12 + 26*X^11 + 60*X^10 + 54*X^9 + 10*X^8 + 6*X^6 + 13*X^5 + 53*X^4 +
      39*X^3 + 30*X^2 + 31*X + 16) :=
  mul_step (by norm_num) pSeventeenA4s207 pSeventeenA41 ⟨
    1,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s209 : XPow fSeventeenA4 413526729497700784963176178858322509562758
    (61*X^33 + 61*X^32 + 30*X^31 + 6*X^30 + 26*X^29 + 20*X^28 + 51*X^27 + 8*X^26 + 59*X^25 + 20*X^24 +
      45*X^23 + 62*X^22 + 63*X^21 + 3*X^20 + 36*X^19 + 49*X^18 + 31*X^17 + 60*X^16 + 19*X^15 +
      28*X^14 + 25*X^13 + 66*X^12 + 60*X^11 + 12*X^10 + 36*X^9 + 41*X^8 + 22*X^7 + 26*X^6 + 16*X^4 +
      12*X^3 + 55*X^2 + 48*X + 5) :=
  sq_step (by norm_num) pSeventeenA4s208 ⟨
    29*X^32 + 20*X^31 + 57*X^30 + 42*X^29 + 50*X^28 + 7*X^27 + 58*X^26 + 61*X^25 + 32*X^24 + 56*X^23 +
      41*X^22 + 61*X^21 + 47*X^20 + 10*X^19 + 6*X^18 + 60*X^17 + 53*X^16 + 36*X^15 + 54*X^14 +
      8*X^13 + 50*X^12 + 31*X^11 + 28*X^10 + 5*X^9 + 22*X^8 + 20*X^7 + 56*X^6 + 35*X^5 + 12*X^4 +
      21*X^3 + 6*X^2 + 8*X + 22,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s210 : XPow fSeventeenA4 413526729497700784963176178858322509562759
    (14*X^33 + 54*X^32 + 9*X^31 + 35*X^30 + 23*X^29 + 53*X^28 + 52*X^27 + 23*X^26 + 33*X^25 + 32*X^24 +
      21*X^23 + 64*X^22 + 7*X^20 + 60*X^19 + 40*X^18 + 13*X^17 + 41*X^16 + 39*X^15 + 23*X^14 +
      54*X^13 + 33*X^12 + 63*X^11 + 15*X^10 + 45*X^9 + 28*X^8 + 3*X^7 + 21*X^6 + 54*X^5 + 5*X^4 +
      19*X^3 + 41*X^2 + 5*X + 38) :=
  mul_step (by norm_num) pSeventeenA4s209 pSeventeenA41 ⟨
    61,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s211 : XPow fSeventeenA4 827053458995401569926352357716645019125518
    (51*X^33 + 6*X^32 + 12*X^31 + 66*X^30 + 2*X^29 + 46*X^28 + 35*X^27 + 11*X^25 + 62*X^24 + 60*X^23 +
      6*X^22 + 64*X^21 + 62*X^20 + 38*X^19 + 58*X^18 + 23*X^17 + 41*X^16 + 35*X^15 + 28*X^14 +
      3*X^13 + 42*X^12 + 41*X^11 + 54*X^9 + 3*X^8 + 56*X^7 + 38*X^6 + 53*X^5 + 55*X^4 + 22*X^3 +
      58*X^2 + 18*X + 40) :=
  sq_step (by norm_num) pSeventeenA4s210 ⟨
    62*X^32 + 10*X^31 + 28*X^30 + X^29 + 26*X^28 + 3*X^27 + 5*X^26 + 12*X^25 + 39*X^24 + 22*X^23 +
      57*X^22 + 64*X^21 + 43*X^20 + 28*X^19 + 63*X^18 + 56*X^17 + 27*X^16 + 5*X^15 + 8*X^14 +
      60*X^13 + 40*X^12 + 34*X^11 + 21*X^10 + 55*X^9 + 51*X^8 + 15*X^7 + 42*X^6 + 48*X^5 + 54*X^4 +
      10*X^3 + 10*X^2 + 36*X + 63,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s212 : XPow fSeventeenA4 1654106917990803139852704715433290038251036
    (10*X^33 + 53*X^32 + 33*X^31 + 21*X^30 + 51*X^29 + 22*X^28 + 58*X^27 + 44*X^26 + 33*X^25 + 2*X^24 +
      19*X^23 + 54*X^22 + 32*X^21 + 49*X^20 + 10*X^19 + 29*X^18 + 2*X^17 + 54*X^16 + 26*X^14 +
      32*X^13 + 44*X^12 + 31*X^11 + 59*X^10 + 45*X^9 + 7*X^8 + 10*X^7 + 38*X^6 + 45*X^5 + 38*X^4 +
      12*X^3 + 53*X^2 + 42*X + 28) :=
  sq_step (by norm_num) pSeventeenA4s211 ⟨
    55*X^32 + 49*X^31 + 28*X^30 + 49*X^29 + 43*X^28 + 39*X^27 + 30*X^26 + 43*X^25 + 23*X^24 + 49*X^23 +
      6*X^22 + X^21 + 51*X^20 + 7*X^19 + 29*X^18 + 59*X^16 + 53*X^15 + 16*X^14 + 11*X^13 + 17*X^12 +
      40*X^11 + 31*X^10 + 31*X^8 + 45*X^7 + 57*X^4 + 22*X^3 + 19*X^2 + 55*X + 19,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s213 : XPow fSeventeenA4 3308213835981606279705409430866580076502072
    (21*X^33 + 66*X^32 + 41*X^31 + 7*X^30 + 50*X^29 + 9*X^28 + 29*X^27 + 6*X^26 + 5*X^25 + 27*X^24 +
      50*X^23 + 9*X^22 + X^21 + 18*X^20 + 19*X^19 + 10*X^18 + 22*X^17 + 18*X^16 + 17*X^15 + 21*X^14 +
      11*X^12 + 60*X^11 + 7*X^10 + 45*X^9 + 25*X^8 + 27*X^7 + 27*X^6 + 31*X^5 + 28*X^4 + 16*X^3 +
      16*X^2 + 22*X + 63) :=
  sq_step (by norm_num) pSeventeenA4s212 ⟨
    33*X^32 + 12*X^31 + 14*X^30 + 66*X^29 + 17*X^28 + 47*X^27 + 13*X^26 + 36*X^25 + 44*X^24 + 58*X^23 +
      10*X^22 + 56*X^21 + 56*X^20 + 62*X^19 + X^18 + 44*X^17 + 18*X^16 + 12*X^15 + 62*X^13 + 60*X^12 +
      52*X^11 + 45*X^10 + 45*X^9 + 47*X^8 + 46*X^7 + 29*X^6 + 43*X^5 + 2*X^4 + 28*X^3 + 66*X^2 +
      47*X + 1,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s214 : XPow fSeventeenA4 6616427671963212559410818861733160153004144
    (43*X^33 + 17*X^32 + 35*X^31 + 65*X^30 + 46*X^29 + 56*X^28 + 8*X^27 + 32*X^26 + 15*X^25 + 19*X^24 +
      50*X^23 + 23*X^22 + 35*X^21 + 36*X^20 + 54*X^19 + 26*X^18 + 62*X^17 + 24*X^16 + 44*X^15 +
      8*X^14 + 45*X^13 + 50*X^12 + 31*X^11 + 11*X^10 + 32*X^9 + 8*X^8 + 30*X^7 + 53*X^6 + 46*X^5 +
      36*X^4 + 59*X^3 + 11*X^2 + X + 10) :=
  sq_step (by norm_num) pSeventeenA4s213 ⟨
    39*X^32 + 29*X^31 + 41*X^30 + 18*X^29 + 53*X^28 + 62*X^27 + 53*X^26 + 56*X^25 + 35*X^24 + 63*X^23 +
      25*X^22 + 22*X^21 + 2*X^20 + 35*X^19 + 28*X^18 + 28*X^17 + 23*X^16 + 20*X^15 + 32*X^14 +
      21*X^13 + 8*X^12 + 49*X^11 + 17*X^10 + 12*X^9 + 66*X^8 + 50*X^6 + 7*X^5 + 64*X^4 + 14*X^3 +
      63*X^2 + 32*X + 8,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s215 : XPow fSeventeenA4 6616427671963212559410818861733160153004145
    (30*X^33 + 64*X^32 + 10*X^31 + 15*X^30 + X^29 + 16*X^28 + 7*X^27 + 5*X^26 + 4*X^25 + 65*X^24 +
      60*X^23 + 39*X^22 + 24*X^21 + 5*X^20 + 3*X^19 + 31*X^18 + 37*X^17 + 65*X^16 + 52*X^15 +
      37*X^14 + 2*X^13 + 57*X^12 + 14*X^11 + 15*X^10 + 24*X^9 + 54*X^8 + 28*X^7 + 63*X^6 + 54*X^5 +
      31*X^4 + X^3 + 40*X^2 + 10*X + 18) :=
  mul_step (by norm_num) pSeventeenA4s214 pSeventeenA41 ⟨
    43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s216 : XPow fSeventeenA4 13232855343926425118821637723466320306008290
    (27*X^33 + 51*X^32 + 22*X^31 + 5*X^30 + 49*X^29 + 52*X^28 + 14*X^27 + 7*X^26 + 60*X^25 + 59*X^24 +
      46*X^23 + 53*X^22 + 34*X^21 + 25*X^20 + 66*X^19 + 21*X^18 + 28*X^17 + 57*X^16 + 40*X^15 +
      34*X^14 + 56*X^13 + 15*X^12 + 66*X^11 + 19*X^10 + 16*X^9 + 31*X^8 + 15*X^7 + 33*X^6 + 5*X^4 +
      64*X^3 + 49*X^2 + 46*X + 8) :=
  sq_step (by norm_num) pSeventeenA4s215 ⟨
    29*X^32 + 36*X^31 + 38*X^30 + 30*X^29 + 58*X^28 + 38*X^27 + 66*X^26 + 30*X^25 + 20*X^24 + 36*X^23 +
      34*X^22 + 42*X^21 + 62*X^20 + 15*X^19 + 8*X^18 + 64*X^17 + 50*X^16 + 58*X^15 + 45*X^14 +
      24*X^13 + 59*X^12 + 37*X^11 + 27*X^10 + 54*X^9 + 52*X^8 + 25*X^7 + 57*X^6 + 61*X^5 + 46*X^4 +
      61*X^3 + 18*X^2 + 39*X + 64,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s217 : XPow fSeventeenA4 13232855343926425118821637723466320306008291
    (28*X^33 + 48*X^32 + 25*X^31 + 42*X^30 + 5*X^29 + 5*X^28 + 10*X^27 + 21*X^26 + 34*X^25 + 4*X^24 +
      3*X^23 + 63*X^22 + 5*X^21 + 29*X^20 + 5*X^19 + 21*X^18 + 34*X^17 + 8*X^16 + 18*X^15 + 65*X^14 +
      2*X^13 + 20*X^12 + 24*X^11 + 10*X^10 + 13*X^9 + 55*X^8 + 36*X^7 + 6*X^6 + 35*X^5 + 62*X^4 +
      10*X^3 + 44*X^2 + 8*X + 30) :=
  mul_step (by norm_num) pSeventeenA4s216 pSeventeenA41 ⟨
    27,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s218 : XPow fSeventeenA4 26465710687852850237643275446932640612016582
    (60*X^33 + 51*X^32 + 50*X^31 + 55*X^30 + 32*X^29 + 8*X^28 + 43*X^27 + 26*X^26 + 24*X^25 + 57*X^24 +
      55*X^23 + 38*X^22 + 32*X^21 + 53*X^20 + 17*X^19 + 33*X^18 + 42*X^17 + 40*X^16 + 4*X^15 +
      52*X^14 + 11*X^13 + 33*X^12 + 45*X^11 + 60*X^10 + 42*X^9 + 38*X^8 + 55*X^7 + 59*X^6 + 17*X^5 +
      5*X^4 + 42*X^3 + 33*X^2 + 12*X + 29) :=
  sq_step (by norm_num) pSeventeenA4s217 ⟨
    47*X^32 + 30*X^31 + 66*X^30 + 65*X^28 + 7*X^27 + 28*X^26 + 20*X^25 + 47*X^24 + 5*X^23 + 4*X^22 +
      56*X^21 + 20*X^20 + 44*X^19 + 25*X^18 + 53*X^17 + 17*X^16 + 58*X^15 + 24*X^14 + 65*X^13 +
      15*X^12 + 66*X^11 + 33*X^10 + 17*X^9 + 18*X^8 + 10*X^7 + 51*X^6 + 12*X^5 + 36*X^4 + 18*X^3 +
      55*X^2 + 21*X,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s219 : XPow fSeventeenA4 26465710687852850237643275446932640612016583
    (52*X^33 + 11*X^32 + 25*X^31 + 9*X^30 + 45*X^29 + 23*X^28 + 55*X^27 + 49*X^26 + 61*X^25 + 51*X^24 +
      46*X^23 + 22*X^22 + 16*X^21 + 39*X^20 + 57*X^19 + 19*X^18 + 41*X^17 + 52*X^16 + 9*X^15 +
      31*X^14 + 19*X^13 + 47*X^12 + 19*X^11 + 51*X^10 + 65*X^9 + 62*X^8 + 21*X^7 + 8*X^6 + 27*X^5 +
      45*X^4 + 58*X^3 + 15*X^2 + 29*X + 22) :=
  mul_step (by norm_num) pSeventeenA4s218 pSeventeenA41 ⟨
    60,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s220 : XPow fSeventeenA4 52931421375705700475286550893865281224033166
    (43*X^33 + 40*X^32 + 10*X^31 + 11*X^30 + 15*X^29 + 18*X^28 + 56*X^27 + 15*X^26 + 4*X^25 + 41*X^24 +
      50*X^23 + 6*X^22 + 63*X^21 + 28*X^20 + 34*X^19 + 48*X^18 + 22*X^17 + 11*X^16 + 53*X^15 +
      42*X^14 + 28*X^13 + 26*X^12 + 54*X^11 + 35*X^10 + 35*X^9 + 40*X^8 + 38*X^7 + 26*X^6 + 40*X^5 +
      31*X^4 + 57*X^3 + 49*X^2 + 34*X + 5) :=
  sq_step (by norm_num) pSeventeenA4s219 ⟨
    24*X^32 + 59*X^31 + 61*X^30 + 52*X^29 + 51*X^28 + 40*X^27 + 47*X^26 + 4*X^25 + 41*X^24 + 29*X^23 +
      4*X^22 + 58*X^21 + 27*X^20 + 10*X^19 + 44*X^18 + 12*X^17 + 7*X^16 + 32*X^15 + 64*X^14 + 6*X^13 +
      46*X^12 + 49*X^11 + 66*X^10 + 33*X^9 + 42*X^8 + 18*X^7 + 8*X^6 + 58*X^5 + 61*X^4 + 45*X^3 +
      46*X^2 + 48*X + 58,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s221 : XPow fSeventeenA4 52931421375705700475286550893865281224033167
    (53*X^33 + 39*X^32 + 23*X^31 + 51*X^30 + 30*X^29 + 64*X^28 + 57*X^27 + 61*X^26 + 26*X^25 + 65*X^24 +
      43*X^23 + 16*X^21 + 52*X^20 + 25*X^19 + 58*X^18 + 24*X^17 + 7*X^16 + 19*X^15 + 20*X^14 +
      45*X^13 + 13*X^12 + 38*X^11 + 18*X^10 + 56*X^9 + 62*X^8 + X^7 + 57*X^6 + 49*X^5 + 29*X^4 +
      39*X^3 + 6*X^2 + 5*X + 18) :=
  mul_step (by norm_num) pSeventeenA4s220 pSeventeenA41 ⟨
    43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s222 : XPow fSeventeenA4 105862842751411400950573101787730562448066334
    (27*X^33 + 38*X^32 + 37*X^31 + 36*X^30 + X^29 + 63*X^28 + 54*X^27 + 44*X^26 + 43*X^25 + 22*X^24 +
      32*X^23 + 47*X^22 + 14*X^21 + 52*X^20 + 59*X^19 + 17*X^18 + 25*X^17 + 16*X^16 + 16*X^15 +
      11*X^14 + 18*X^13 + 9*X^12 + 45*X^11 + 33*X^10 + 43*X^9 + 25*X^8 + 38*X^7 + 61*X^6 + 17*X^5 +
      14*X^4 + 32*X^3 + 45*X^2 + 33*X + 17) :=
  sq_step (by norm_num) pSeventeenA4s221 ⟨
    62*X^32 + 19*X^31 + 52*X^30 + 41*X^29 + 15*X^28 + 15*X^27 + 14*X^26 + 17*X^25 + 51*X^24 + 7*X^23 +
      65*X^22 + 66*X^21 + 15*X^20 + 63*X^19 + 21*X^18 + 60*X^17 + 50*X^16 + 54*X^15 + 13*X^14 +
      59*X^13 + 4*X^12 + 56*X^11 + 41*X^10 + 48*X^9 + 59*X^8 + 13*X^7 + 18*X^6 + 9*X^5 + 47*X^3 +
      37*X^2 + 62*X + 52,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s223 : XPow fSeventeenA4 105862842751411400950573101787730562448066335
    (15*X^33 + 63*X^32 + 56*X^31 + 61*X^30 + 16*X^29 + 45*X^28 + 47*X^27 + 4*X^26 + 64*X^25 + 57*X^24 +
      64*X^23 + 43*X^22 + 32*X^21 + 22*X^20 + X^19 + 18*X^18 + 60*X^17 + 51*X^16 + 62*X^15 + 27*X^14 +
      63*X^13 + 66*X^12 + 38*X^11 + 37*X^10 + 7*X^9 + 11*X^8 + 64*X^7 + 23*X^6 + 44*X^5 + 30*X^4 +
      6*X^3 + 31*X^2 + 17*X + 30) :=
  mul_step (by norm_num) pSeventeenA4s222 pSeventeenA41 ⟨
    27,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s224 : XPow fSeventeenA4 211725685502822801901146203575461124896132670
    (27*X^33 + 52*X^32 + 46*X^31 + 20*X^30 + 35*X^29 + 16*X^28 + 17*X^27 + 65*X^26 + 58*X^25 + 60*X^24 +
      58*X^23 + 4*X^22 + 66*X^21 + 48*X^20 + 34*X^19 + 60*X^18 + 59*X^17 + 31*X^16 + 25*X^15 +
      29*X^14 + 3*X^13 + 41*X^12 + 13*X^11 + 24*X^10 + 25*X^9 + 14*X^8 + 14*X^7 + 13*X^6 + 19*X^5 +
      34*X^4 + 59*X^3 + 61*X^2 + 56*X + 55) :=
  sq_step (by norm_num) pSeventeenA4s223 ⟨
    24*X^32 + X^31 + 11*X^30 + 34*X^29 + 42*X^28 + 54*X^27 + 9*X^26 + 61*X^25 + 44*X^24 + 22*X^23 +
      43*X^22 + 38*X^21 + 6*X^20 + 20*X^19 + 59*X^18 + 30*X^17 + 11*X^16 + 33*X^15 + 25*X^14 +
      26*X^13 + 53*X^12 + 41*X^11 + 63*X^10 + 20*X^9 + 35*X^8 + 31*X^7 + 39*X^6 + 14*X^5 + 36*X^4 +
      10*X^3 + 60*X^2 + 57*X + 10,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s225 : XPow fSeventeenA4 423451371005645603802292407150922249792265340
    (2*X^33 + 41*X^32 + 50*X^31 + 38*X^30 + 50*X^29 + 47*X^28 + 7*X^27 + 9*X^26 + 26*X^25 + 14*X^24 +
      59*X^23 + 45*X^22 + 17*X^21 + 45*X^20 + 3*X^19 + 46*X^18 + 24*X^17 + 48*X^16 + 64*X^15 +
      64*X^14 + 21*X^13 + 57*X^12 + 57*X^11 + 66*X^10 + 65*X^9 + 50*X^8 + 10*X^7 + 4*X^6 + 19*X^5 +
      59*X^4 + 28*X^3 + 47*X^2 + 63*X + 37) :=
  sq_step (by norm_num) pSeventeenA4s224 ⟨
    59*X^32 + 43*X^31 + 7*X^30 + 52*X^28 + 32*X^27 + 29*X^26 + 23*X^25 + 28*X^24 + 40*X^23 + 5*X^22 +
      37*X^21 + 4*X^20 + 46*X^19 + 7*X^18 + 4*X^17 + 27*X^16 + 3*X^15 + 4*X^14 + 51*X^13 + 37*X^12 +
      46*X^11 + 2*X^10 + 31*X^9 + 5*X^8 + 58*X^7 + 50*X^6 + 53*X^5 + 33*X^4 + 62*X^3 + 56*X^2 + 31,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s226 : XPow fSeventeenA4 846902742011291207604584814301844499584530680
    (14*X^33 + 35*X^32 + 56*X^31 + 18*X^30 + 3*X^29 + 4*X^28 + 54*X^27 + 44*X^26 + 39*X^25 + 34*X^24 +
      6*X^23 + 8*X^22 + 45*X^20 + 63*X^19 + 42*X^18 + 10*X^17 + 23*X^16 + 62*X^15 + 43*X^14 + 8*X^13 +
      15*X^12 + 30*X^11 + 57*X^10 + 49*X^9 + 7*X^8 + 11*X^7 + 48*X^6 + 14*X^5 + 13*X^4 + 38*X^3 +
      62*X^2 + 33*X + 43) :=
  sq_step (by norm_num) pSeventeenA4s225 ⟨
    4*X^32 + 39*X^31 + 60*X^30 + 8*X^29 + 41*X^28 + X^27 + 5*X^26 + 40*X^25 + 33*X^24 + 25*X^23 + 8*X^22 +
      17*X^21 + 19*X^19 + 35*X^18 + 40*X^17 + 36*X^16 + 39*X^15 + 10*X^14 + 45*X^13 + 62*X^12 +
      4*X^11 + 21*X^10 + 5*X^9 + 56*X^8 + 9*X^7 + 49*X^6 + 18*X^5 + 2*X^4 + 34*X^3 + 53*X^2 + 8*X +
      26,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s227 : XPow fSeventeenA4 1693805484022582415209169628603688999169061360
    (12*X^33 + 39*X^32 + 40*X^31 + 47*X^30 + 4*X^29 + 46*X^28 + 40*X^27 + 14*X^26 + 30*X^25 + 27*X^24 +
      17*X^23 + 10*X^22 + 8*X^21 + 13*X^20 + 36*X^19 + 13*X^18 + 7*X^17 + 35*X^16 + 2*X^15 + 23*X^14 +
      59*X^13 + 8*X^12 + 52*X^11 + 29*X^10 + 54*X^9 + 36*X^8 + 4*X^7 + 27*X^6 + 37*X^5 + 15*X^4 +
      34*X^3 + 60*X^2 + 34*X + 48) :=
  sq_step (by norm_num) pSeventeenA4s226 ⟨
    62*X^32 + 14*X^31 + 64*X^30 + 59*X^29 + 19*X^28 + 34*X^27 + 66*X^26 + 22*X^25 + 47*X^24 + 19*X^23 +
      24*X^22 + 47*X^21 + 48*X^20 + 34*X^19 + 20*X^18 + 15*X^17 + 15*X^16 + 24*X^15 + 55*X^14 +
      12*X^13 + 40*X^12 + 62*X^11 + 47*X^10 + 61*X^9 + 24*X^8 + 15*X^7 + 45*X^6 + 14*X^5 + 26*X^4 +
      4*X^3 + 55*X^2 + 9*X + 34,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s228 : XPow fSeventeenA4 1693805484022582415209169628603688999169061361
    (66*X^33 + 59*X^32 + 41*X^31 + 53*X^30 + 40*X^29 + 36*X^28 + 60*X^27 + 35*X^26 + X^25 + 43*X^24 +
      25*X^23 + 6*X^22 + 19*X^21 + 27*X^20 + 58*X^19 + 56*X^18 + 62*X^17 + 25*X^16 + X^15 + 63*X^14 +
      32*X^13 + 39*X^12 + 61*X^11 + 29*X^10 + 28*X^9 + 59*X^8 + 6*X^7 + 62*X^6 + 6*X^5 + 48*X^4 +
      65*X^3 + 48*X^2 + 48*X + 58) :=
  mul_step (by norm_num) pSeventeenA4s227 pSeventeenA41 ⟨
    12,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s229 : XPow fSeventeenA4 3387610968045164830418339257207377998338122722
    (53*X^33 + 22*X^32 + 9*X^31 + 52*X^30 + 34*X^29 + 24*X^28 + 48*X^27 + 47*X^26 + 44*X^25 + 32*X^24 +
      36*X^23 + 16*X^22 + 52*X^21 + 4*X^20 + 45*X^19 + 55*X^18 + 47*X^17 + 44*X^16 + 27*X^15 +
      24*X^14 + 52*X^13 + 40*X^12 + 6*X^11 + 24*X^10 + 8*X^9 + 23*X^8 + 36*X^7 + 5*X^6 + 54*X^5 +
      39*X^4 + 19*X^3 + 39*X^2 + 63*X + 9) :=
  sq_step (by norm_num) pSeventeenA4s228 ⟨
    X^32 + 35*X^31 + 40*X^30 + 25*X^29 + 44*X^28 + 9*X^27 + 27*X^26 + 8*X^25 + 24*X^24 + 17*X^23 +
      28*X^22 + 12*X^21 + 3*X^20 + 37*X^19 + 23*X^18 + 31*X^17 + 32*X^16 + 27*X^15 + 20*X^14 +
      10*X^13 + 57*X^12 + 30*X^11 + 22*X^9 + 26*X^8 + 15*X^7 + 46*X^6 + 44*X^5 + 24*X^4 + 54*X^3 +
      52*X^2 + 37*X + 29,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s230 : XPow fSeventeenA4 6775221936090329660836678514414755996676245444
    (65*X^33 + 52*X^32 + 30*X^31 + 3*X^30 + 34*X^29 + 4*X^28 + 33*X^27 + 14*X^26 + 49*X^25 + 59*X^24 +
      49*X^23 + 52*X^22 + 59*X^21 + 2*X^20 + 64*X^19 + 22*X^18 + 29*X^17 + 42*X^16 + 64*X^15 +
      45*X^14 + 42*X^13 + 46*X^12 + 21*X^11 + X^10 + 31*X^9 + 50*X^8 + 14*X^7 + 41*X^6 + 13*X^5 +
      6*X^4 + 42*X^3 + 39*X^2 + 55*X + 52) :=
  sq_step (by norm_num) pSeventeenA4s229 ⟨
    62*X^32 + 26*X^31 + 9*X^30 + 48*X^29 + 43*X^28 + 66*X^27 + 30*X^26 + 42*X^25 + X^24 + 47*X^23 +
      46*X^22 + 32*X^21 + 24*X^20 + 26*X^19 + 54*X^18 + 17*X^17 + 14*X^16 + 41*X^15 + 3*X^14 +
      30*X^13 + 55*X^12 + 21*X^11 + 50*X^10 + 13*X^9 + 18*X^8 + 29*X^7 + 43*X^6 + 48*X^5 + 51*X^4 +
      20*X^3 + 25*X^2 + 54*X + 61,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s231 : XPow fSeventeenA4 13550443872180659321673357028829511993352490888
    (45*X^33 + 50*X^32 + 19*X^31 + 36*X^30 + 30*X^29 + 13*X^28 + 5*X^27 + 54*X^26 + 13*X^25 + 53*X^24 +
      19*X^23 + 61*X^22 + 43*X^21 + 16*X^20 + 14*X^19 + 9*X^18 + 25*X^17 + 9*X^16 + 37*X^15 +
      24*X^14 + 12*X^13 + 23*X^12 + 13*X^11 + 8*X^10 + 33*X^9 + 61*X^8 + 63*X^7 + 14*X^6 + 58*X^5 +
      60*X^4 + 50*X^3 + 21*X^2 + 52*X + 18) :=
  sq_step (by norm_num) pSeventeenA4s230 ⟨
    4*X^32 + 2*X^31 + 60*X^30 + 17*X^29 + 13*X^28 + 25*X^27 + 31*X^26 + 63*X^25 + 26*X^24 + 3*X^23 +
      10*X^22 + 44*X^21 + 12*X^20 + 46*X^19 + 28*X^18 + 4*X^17 + 13*X^16 + 44*X^15 + 31*X^14 +
      57*X^13 + X^12 + 7*X^11 + 12*X^10 + 44*X^9 + 59*X^8 + 61*X^7 + 35*X^6 + 34*X^5 + 24*X^4 +
      6*X^3 + 16*X^2 + 31*X + 8,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s232 : XPow fSeventeenA4 27100887744361318643346714057659023986704981776
    (10*X^33 + 29*X^32 + 54*X^31 + 8*X^30 + 65*X^29 + 15*X^28 + 28*X^27 + 35*X^26 + 57*X^25 + 47*X^24 +
      14*X^23 + 13*X^22 + 24*X^21 + 51*X^20 + 39*X^19 + 24*X^18 + 66*X^17 + 51*X^16 + 44*X^15 +
      6*X^14 + 16*X^13 + 38*X^12 + 56*X^11 + 59*X^10 + 15*X^9 + 48*X^8 + 11*X^7 + 26*X^6 + 19*X^5 +
      X^4 + 31*X^3 + 45*X^2 + 4*X + 62) :=
  sq_step (by norm_num) pSeventeenA4s231 ⟨
    15*X^32 + 28*X^31 + 59*X^30 + 11*X^29 + 65*X^28 + 17*X^27 + 49*X^26 + 25*X^25 + 19*X^24 + 50*X^23 +
      26*X^21 + 10*X^20 + 53*X^19 + 50*X^18 + 46*X^17 + 12*X^16 + 23*X^15 + 38*X^14 + 17*X^13 +
      29*X^12 + 54*X^11 + 49*X^10 + 54*X^9 + 56*X^8 + 14*X^7 + 21*X^6 + 6*X^5 + 12*X^4 + 41*X^3 +
      37*X^2 + 34*X + 59,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s233 : XPow fSeventeenA4 27100887744361318643346714057659023986704981777
    (18*X^33 + 14*X^32 + 3*X^31 + 50*X^30 + 10*X^29 + 47*X^28 + 51*X^27 + 50*X^26 + 3*X^25 + 58*X^24 +
      59*X^23 + 56*X^21 + 65*X^20 + 28*X^19 + 51*X^18 + 40*X^17 + 52*X^16 + 10*X^15 + 64*X^14 +
      58*X^13 + 34*X^12 + 41*X^11 + 50*X^10 + 19*X^9 + X^8 + 42*X^7 + 51*X^6 + 27*X^5 + 65*X^4 +
      38*X^3 + 38*X^2 + 62*X + 26) :=
  mul_step (by norm_num) pSeventeenA4s232 pSeventeenA41 ⟨
    10,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s234 : XPow fSeventeenA4 54201775488722637286693428115318047973409963554
    (44*X^33 + 5*X^32 + 13*X^31 + 39*X^30 + 57*X^29 + 62*X^28 + 49*X^27 + 20*X^26 + 41*X^25 + 4*X^24 +
      31*X^23 + 32*X^22 + 45*X^21 + 35*X^20 + 25*X^19 + 49*X^18 + 66*X^17 + 29*X^16 + 52*X^15 +
      14*X^14 + 43*X^13 + 40*X^12 + 5*X^11 + 49*X^10 + 17*X^9 + 31*X^8 + 42*X^7 + 45*X^6 + 43*X^5 +
      48*X^4 + 13*X^3 + 32*X^2 + 44*X + 65) :=
  sq_step (by norm_num) pSeventeenA4s233 ⟨
    56*X^32 + 27*X^31 + 57*X^30 + 17*X^29 + 58*X^28 + 60*X^27 + 6*X^26 + 40*X^25 + 7*X^24 + 7*X^23 +
      52*X^22 + 62*X^21 + 30*X^20 + 51*X^19 + 43*X^18 + 19*X^17 + 40*X^16 + 42*X^15 + 61*X^14 +
      29*X^13 + 48*X^12 + 10*X^11 + 20*X^10 + 44*X^9 + 22*X^8 + 13*X^7 + 52*X^6 + 16*X^5 + 27*X^4 +
      22*X^3 + 19*X^2 + 19*X + 33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s235 : XPow fSeventeenA4 108403550977445274573386856230636095946819927108
    (39*X^33 + 39*X^32 + 31*X^31 + 33*X^30 + 42*X^29 + 20*X^28 + 3*X^27 + 31*X^26 + 7*X^25 + 4*X^24 +
      47*X^23 + 16*X^22 + 23*X^21 + 57*X^20 + 23*X^19 + 53*X^18 + 44*X^17 + 12*X^16 + 13*X^15 +
      7*X^14 + 49*X^13 + 13*X^12 + 19*X^11 + 55*X^10 + 28*X^8 + 64*X^7 + 5*X^6 + 16*X^5 + 28*X^4 +
      61*X^3 + 39*X^2 + 37*X + 11) :=
  sq_step (by norm_num) pSeventeenA4s234 ⟨
    60*X^32 + 39*X^31 + 62*X^30 + 65*X^29 + 54*X^28 + 15*X^27 + 35*X^25 + 7*X^24 + 7*X^23 + 31*X^22 +
      16*X^21 + 55*X^20 + 47*X^19 + 47*X^18 + 2*X^17 + 65*X^16 + 11*X^15 + 42*X^14 + 11*X^13 +
      60*X^12 + 25*X^11 + 56*X^10 + 22*X^8 + 5*X^7 + 41*X^6 + 59*X^5 + 55*X^4 + 13*X^3 + 19*X^2 +
      51*X + 13,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s236 : XPow fSeventeenA4 216807101954890549146773712461272191893639854216
    (35*X^33 + 45*X^32 + 38*X^31 + 61*X^30 + 37*X^29 + 39*X^28 + 49*X^27 + 58*X^26 + 57*X^25 + 54*X^24 +
      44*X^23 + 33*X^22 + 24*X^21 + 51*X^20 + 54*X^19 + 63*X^18 + 53*X^17 + 49*X^16 + 28*X^15 +
      15*X^14 + 64*X^13 + 9*X^12 + 9*X^11 + 25*X^10 + 20*X^9 + 63*X^8 + 56*X^7 + 7*X^6 + 14*X^5 +
      40*X^4 + X^3 + 58*X^2 + 41*X + 49) :=
  sq_step (by norm_num) pSeventeenA4s235 ⟨
    47*X^32 + 49*X^31 + 59*X^30 + 31*X^29 + 34*X^28 + 8*X^27 + 10*X^26 + 3*X^25 + 20*X^24 + 40*X^23 +
      8*X^22 + 45*X^21 + 34*X^20 + 10*X^19 + 47*X^18 + 43*X^17 + 2*X^16 + 60*X^15 + 24*X^14 +
      29*X^13 + 6*X^12 + 23*X^11 + 57*X^10 + 45*X^9 + 46*X^8 + 6*X^7 + 47*X^6 + 5*X^5 + 4*X^4 +
      2*X^3 + 4*X^2 + 48*X + 29,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s237 : XPow fSeventeenA4 216807101954890549146773712461272191893639854217
    (40*X^33 + 32*X^32 + 10*X^31 + 18*X^30 + 55*X^29 + 15*X^28 + 47*X^27 + 66*X^26 + 34*X^25 + 64*X^24 +
      60*X^23 + 7*X^22 + 35*X^21 + 11*X^20 + 10*X^19 + 34*X^18 + 44*X^17 + 56*X^16 + 29*X^15 +
      31*X^14 + 12*X^13 + 66*X^12 + 29*X^11 + 42*X^10 + 62*X^9 + 21*X^8 + 63*X^7 + 59*X^6 + 64*X^5 +
      53*X^4 + 26*X^2 + 49*X + 24) :=
  mul_step (by norm_num) pSeventeenA4s236 pSeventeenA41 ⟨
    35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s238 : XPow fSeventeenA4 433614203909781098293547424922544383787279708434
    (56*X^33 + 32*X^32 + 62*X^31 + 27*X^30 + 46*X^29 + 58*X^28 + 64*X^27 + 12*X^26 + 62*X^25 + 28*X^24 +
      43*X^23 + 42*X^22 + 14*X^21 + 53*X^20 + 19*X^19 + 29*X^18 + 49*X^17 + 35*X^16 + 27*X^15 +
      23*X^14 + 13*X^13 + 21*X^12 + 10*X^11 + 49*X^10 + 27*X^9 + 17*X^8 + 18*X^7 + 11*X^6 + 41*X^5 +
      40*X^4 + X^3 + X^2 + 30*X + 4) :=
  sq_step (by norm_num) pSeventeenA4s237 ⟨
    59*X^32 + 63*X^31 + 38*X^30 + 8*X^29 + 38*X^28 + 66*X^27 + 43*X^26 + 9*X^25 + 22*X^24 + 20*X^23 +
      64*X^22 + 7*X^21 + 64*X^20 + 30*X^19 + 26*X^18 + 64*X^17 + 25*X^16 + 17*X^15 + 33*X^14 +
      36*X^13 + 65*X^12 + 14*X^11 + X^10 + 9*X^9 + 41*X^8 + 16*X^7 + 42*X^6 + 15*X^5 + 54*X^4 +
      20*X^3 + 3*X^2 + 14*X + 48,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s239 : XPow fSeventeenA4 867228407819562196587094849845088767574559416868
    (52*X^33 + 25*X^32 + 60*X^31 + 10*X^30 + 3*X^29 + 28*X^28 + 6*X^27 + 12*X^26 + 42*X^25 + 45*X^24 +
      34*X^23 + 27*X^22 + 47*X^21 + 25*X^20 + 6*X^19 + 7*X^18 + 61*X^17 + 57*X^16 + 2*X^15 + 53*X^14 +
      3*X^13 + 27*X^12 + 51*X^11 + 32*X^10 + 63*X^9 + 33*X^8 + 8*X^7 + 41*X^6 + 4*X^5 + 62*X^4 +
      44*X^3 + 10*X^2 + 16*X + 21) :=
  sq_step (by norm_num) pSeventeenA4s238 ⟨
    54*X^32 + 54*X^31 + X^30 + X^29 + 45*X^28 + 30*X^27 + 35*X^26 + 47*X^25 + 9*X^24 + 39*X^23 + 26*X^22 +
      62*X^21 + X^20 + 62*X^19 + 19*X^18 + 20*X^17 + 18*X^16 + 2*X^15 + 4*X^14 + 2*X^12 + 65*X^11 +
      35*X^10 + 5*X^9 + 40*X^8 + 25*X^7 + 40*X^6 + 32*X^5 + 15*X^4 + 9*X^3 + 43*X^2 + 53*X + 38,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s240 : XPow fSeventeenA4 867228407819562196587094849845088767574559416869
    (8*X^33 + 53*X^32 + 51*X^31 + 59*X^30 + 2*X^29 + 11*X^28 + 55*X^27 + 19*X^26 + 44*X^25 + 35*X^24 +
      25*X^23 + 16*X^22 + 51*X^21 + 34*X^20 + X^19 + 50*X^18 + 40*X^17 + 57*X^16 + 47*X^15 + 65*X^14 +
      64*X^13 + 17*X^12 + 59*X^11 + 44*X^10 + 43*X^9 + 23*X^8 + 17*X^7 + 23*X^6 + 23*X^5 + 60*X^4 +
      54*X^3 + 32*X^2 + 21*X + 28) :=
  mul_step (by norm_num) pSeventeenA4s239 pSeventeenA41 ⟨
    52,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s241 : XPow fSeventeenA4 1734456815639124393174189699690177535149118833738
    (43*X^33 + 54*X^32 + 47*X^31 + 55*X^30 + 39*X^29 + 49*X^28 + 20*X^27 + 39*X^26 + 21*X^25 + 42*X^24 +
      43*X^23 + 58*X^22 + 22*X^21 + 49*X^20 + 59*X^19 + 7*X^18 + 20*X^17 + 34*X^16 + 18*X^15 +
      17*X^14 + 25*X^13 + 8*X^12 + 58*X^11 + 16*X^10 + 36*X^9 + 32*X^8 + 46*X^7 + 35*X^6 + 37*X^5 +
      24*X^4 + 10*X^3 + 15*X^2 + 61*X + 3) :=
  sq_step (by norm_num) pSeventeenA4s240 ⟨
    64*X^32 + 54*X^31 + 40*X^30 + 28*X^29 + 24*X^28 + 51*X^27 + 5*X^26 + 10*X^25 + 40*X^24 + 26*X^23 +
      46*X^22 + 48*X^21 + 35*X^20 + 19*X^19 + 27*X^18 + 4*X^17 + 4*X^16 + 44*X^15 + 48*X^14 +
      21*X^13 + 20*X^12 + 36*X^11 + 49*X^10 + 57*X^9 + X^8 + 59*X^7 + 45*X^6 + 47*X^5 + 54*X^4 +
      29*X^3 + 46*X^2 + 35*X + 14,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s242 : XPow fSeventeenA4 3468913631278248786348379399380355070298237667476
    (56*X^33 + 40*X^32 + 31*X^31 + 26*X^30 + 66*X^29 + 2*X^28 + 17*X^27 + 12*X^26 + 4*X^25 + 41*X^24 +
      35*X^23 + X^22 + 44*X^21 + 49*X^20 + 55*X^19 + 5*X^18 + 45*X^17 + 4*X^16 + 47*X^15 + 4*X^14 +
      57*X^13 + 34*X^12 + 30*X^10 + 46*X^9 + 41*X^8 + 22*X^7 + 30*X^6 + 34*X^5 + 50*X^4 + 42*X^3 +
      53*X^2 + 20*X + 54) :=
  sq_step (by norm_num) pSeventeenA4s241 ⟨
    40*X^32 + 44*X^31 + 63*X^30 + 20*X^29 + 25*X^28 + 38*X^27 + 37*X^26 + 40*X^25 + 53*X^24 + 45*X^23 +
      4*X^22 + 58*X^21 + 25*X^20 + 24*X^19 + 34*X^18 + 60*X^17 + 47*X^16 + 38*X^15 + 4*X^14 +
      62*X^13 + 40*X^12 + 6*X^11 + 25*X^10 + 20*X^8 + 18*X^7 + 17*X^6 + 60*X^5 + 35*X^4 + 39*X^3 +
      4*X^2 + 37*X + 7,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s243 : XPow fSeventeenA4 3468913631278248786348379399380355070298237667477
    (32*X^33 + 8*X^32 + 65*X^31 + 49*X^30 + 41*X^29 + 43*X^28 + 48*X^27 + 5*X^26 + 9*X^25 + 4*X^23 +
      57*X^22 + 10*X^21 + 13*X^20 + 14*X^19 + 28*X^18 + 63*X^17 + 65*X^16 + 13*X^15 + 31*X^14 +
      12*X^13 + 51*X^12 + 23*X^11 + 41*X^10 + 26*X^9 + 33*X^8 + 66*X^7 + 39*X^6 + 8*X^5 + 18*X^4 +
      54*X^3 + 63*X^2 + 54*X + 25) :=
  mul_step (by norm_num) pSeventeenA4s242 pSeventeenA41 ⟨
    56,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s244 : XPow fSeventeenA4 6937827262556497572696758798760710140596475334954
    (31*X^33 + 60*X^32 + 29*X^31 + 11*X^30 + 54*X^29 + 40*X^28 + 8*X^27 + 58*X^26 + 20*X^25 + 44*X^24 +
      3*X^23 + 43*X^22 + 35*X^21 + 41*X^20 + 24*X^19 + 2*X^18 + 51*X^17 + 61*X^16 + 46*X^14 +
      34*X^13 + 51*X^12 + 16*X^11 + 56*X^10 + 40*X^9 + 47*X^8 + 30*X^7 + 38*X^6 + 46*X^5 + 5*X^4 +
      30*X^3 + 41*X^2 + 12*X + 56) :=
  sq_step (by norm_num) pSeventeenA4s243 ⟨
    19*X^32 + 2*X^31 + 32*X^30 + 43*X^29 + 18*X^28 + 37*X^27 + 41*X^26 + 9*X^25 + 45*X^24 + 44*X^23 +
      6*X^22 + 13*X^21 + 11*X^20 + 7*X^19 + 4*X^18 + 18*X^17 + 64*X^16 + 52*X^15 + 20*X^14 + 62*X^12 +
      19*X^11 + 41*X^10 + 64*X^9 + 17*X^8 + 7*X^7 + 66*X^6 + 50*X^5 + 45*X^4 + 15*X^3 + 32*X^2 +
      33*X + 44,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s245 : XPow fSeventeenA4 6937827262556497572696758798760710140596475334955
    (46*X^33 + 39*X^32 + 29*X^31 + 41*X^30 + 58*X^29 + 20*X^28 + 54*X^27 + 5*X^26 + 55*X^25 + 59*X^24 +
      65*X^23 + 41*X^22 + 23*X^21 + 51*X^20 + X^19 + 38*X^18 + 47*X^17 + 65*X^16 + 45*X^15 + 22*X^14 +
      46*X^13 + 55*X^12 + 27*X^11 + 48*X^10 + 4*X^9 + 66*X^8 + 34*X^7 + 38*X^6 + 32*X^5 + 55*X^4 +
      26*X^3 + 37*X^2 + 56*X + 27) :=
  mul_step (by norm_num) pSeventeenA4s244 pSeventeenA41 ⟨
    31,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s246 : XPow fSeventeenA4 13875654525112995145393517597521420281192950669910
    (60*X^33 + 55*X^32 + 35*X^31 + 12*X^30 + 8*X^29 + 31*X^28 + 36*X^27 + 17*X^26 + 8*X^25 + 38*X^24 +
      32*X^23 + 31*X^22 + 2*X^21 + 42*X^20 + 28*X^18 + 23*X^17 + 29*X^16 + 53*X^15 + 65*X^13 +
      30*X^12 + 16*X^11 + 51*X^10 + 17*X^9 + 55*X^8 + 63*X^7 + 53*X^6 + 6*X^5 + 22*X^4 + 58*X^3 +
      24*X^2 + 3*X + 63) :=
  sq_step (by norm_num) pSeventeenA4s245 ⟨
    39*X^32 + 41*X^31 + 55*X^30 + 28*X^29 + 27*X^28 + 23*X^27 + 47*X^26 + 63*X^25 + 39*X^24 + 16*X^23 +
      32*X^22 + 19*X^21 + 22*X^20 + 3*X^19 + 63*X^18 + 63*X^17 + 60*X^16 + 47*X^15 + 26*X^14 +
      42*X^13 + 36*X^12 + 47*X^11 + 28*X^10 + 39*X^9 + 44*X^8 + 47*X^7 + 7*X^6 + 44*X^5 + 14*X^4 +
      24*X^3 + 43*X^2 + 8*X + 17,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s247 : XPow fSeventeenA4 13875654525112995145393517597521420281192950669911
    (56*X^33 + 63*X^32 + 49*X^31 + 52*X^30 + X^29 + 16*X^28 + 46*X^27 + 33*X^26 + 42*X^25 + 28*X^24 +
      39*X^23 + 59*X^22 + 5*X^21 + 22*X^20 + 52*X^19 + 30*X^17 + 34*X^16 + 24*X^15 + 18*X^14 +
      16*X^13 + 18*X^12 + 10*X^11 + 26*X^10 + 15*X^9 + 3*X^8 + 15*X^7 + 64*X^6 + 44*X^5 + 61*X^4 +
      49*X^3 + 6*X^2 + 63*X + 22) :=
  mul_step (by norm_num) pSeventeenA4s246 pSeventeenA41 ⟨
    60,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s248 : XPow fSeventeenA4 27751309050225990290787035195042840562385901339822
    (5*X^33 + 56*X^32 + 2*X^31 + 53*X^30 + 10*X^29 + 59*X^28 + 39*X^27 + X^26 + 4*X^25 + 34*X^24 +
      10*X^23 + 32*X^22 + 46*X^21 + 15*X^20 + 51*X^19 + 20*X^18 + 21*X^17 + 58*X^16 + 59*X^15 +
      57*X^14 + 32*X^13 + 16*X^12 + 50*X^11 + 36*X^10 + 12*X^9 + 47*X^8 + 13*X^7 + 7*X^6 + 25*X^5 +
      20*X^4 + 47*X^3 + 15*X^2 + 31*X + 28) :=
  sq_step (by norm_num) pSeventeenA4s247 ⟨
    54*X^32 + 42*X^31 + 56*X^30 + 3*X^29 + 19*X^28 + 9*X^27 + 58*X^26 + 53*X^25 + 39*X^24 + 40*X^23 +
      18*X^22 + 50*X^21 + 50*X^20 + 19*X^19 + 48*X^18 + 37*X^17 + 27*X^16 + 28*X^15 + 51*X^14 +
      2*X^13 + 28*X^12 + 4*X^11 + 54*X^10 + 63*X^9 + 66*X^8 + 28*X^7 + 14*X^6 + 18*X^5 + 55*X^4 +
      36*X^3 + 41*X^2 + 59*X + 5,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s249 : XPow fSeventeenA4 55502618100451980581574070390085681124771802679644
    (50*X^33 + 26*X^32 + 56*X^31 + 15*X^30 + 29*X^29 + 38*X^28 + 3*X^27 + 3*X^26 + 63*X^25 + 17*X^24 +
      32*X^23 + 50*X^22 + 42*X^21 + 33*X^20 + 45*X^19 + 20*X^18 + 48*X^17 + 19*X^16 + 65*X^15 +
      47*X^14 + 13*X^13 + 3*X^12 + 49*X^11 + 54*X^10 + 18*X^9 + 54*X^8 + 31*X^7 + X^6 + 51*X^5 +
      59*X^4 + 43*X^3 + 58*X^2 + 46*X + 43) :=
  sq_step (by norm_num) pSeventeenA4s248 ⟨
    25*X^32 + 30*X^31 + 8*X^30 + 3*X^29 + 16*X^28 + 42*X^27 + 14*X^26 + 57*X^25 + 10*X^24 + 15*X^23 +
      11*X^22 + 34*X^21 + 37*X^20 + 21*X^19 + 56*X^18 + 64*X^17 + 52*X^15 + 55*X^14 + 2*X^13 +
      12*X^12 + 65*X^11 + 23*X^10 + 28*X^9 + 4*X^8 + 44*X^7 + 46*X^6 + 62*X^5 + 21*X^4 + 46*X^3 +
      27*X^2 + 20*X + 50,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s250 : XPow fSeventeenA4 111005236200903961163148140780171362249543605359288
    (51*X^33 + 52*X^32 + 54*X^31 + X^30 + 27*X^28 + 57*X^27 + 5*X^26 + 6*X^25 + 31*X^24 + 37*X^23 +
      9*X^22 + 48*X^21 + 15*X^20 + 4*X^19 + 18*X^18 + 54*X^17 + 51*X^16 + X^15 + 56*X^14 + 9*X^13 +
      48*X^12 + 5*X^11 + 41*X^10 + 30*X^9 + 29*X^8 + 49*X^7 + 41*X^6 + 38*X^5 + 33*X^4 + 55*X^3 +
      64*X + 26) :=
  sq_step (by norm_num) pSeventeenA4s249 ⟨
    21*X^32 + 51*X^31 + 59*X^30 + 59*X^29 + 6*X^28 + 16*X^27 + 16*X^26 + 36*X^25 + 45*X^24 + 39*X^23 +
      59*X^22 + 22*X^21 + 23*X^20 + 58*X^19 + 32*X^18 + 30*X^17 + 8*X^16 + 3*X^15 + 62*X^14 +
      20*X^13 + 20*X^12 + 19*X^11 + 41*X^10 + 51*X^9 + 45*X^8 + 50*X^7 + 36*X^6 + 60*X^5 + 3*X^4 +
      44*X^3 + 59*X^2 + 8*X + 41,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s251 : XPow fSeventeenA4 111005236200903961163148140780171362249543605359289
    (16*X^33 + 51*X^32 + 9*X^31 + 24*X^30 + 35*X^29 + 40*X^28 + 33*X^27 + 44*X^26 + 21*X^25 + 47*X^24 +
      56*X^23 + 6*X^22 + 7*X^21 + 16*X^20 + 25*X^19 + 11*X^18 + 15*X^17 + 15*X^16 + 63*X^15 +
      26*X^14 + 16*X^13 + 43*X^11 + 41*X^10 + 62*X^9 + 65*X^8 + 2*X^7 + 27*X^6 + 45*X^5 + 14*X^4 +
      38*X^3 + 23*X^2 + 26*X + 12) :=
  mul_step (by norm_num) pSeventeenA4s250 pSeventeenA41 ⟨
    51,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s252 : XPow fSeventeenA4 222010472401807922326296281560342724499087210718578
    (53*X^33 + 39*X^32 + 50*X^31 + 56*X^30 + 63*X^29 + 52*X^28 + 2*X^27 + 54*X^26 + 45*X^25 + 60*X^24 +
      20*X^23 + 63*X^22 + 10*X^21 + 56*X^20 + 23*X^19 + 42*X^18 + 61*X^17 + 56*X^16 + 65*X^15 +
      40*X^14 + 31*X^13 + 54*X^12 + 25*X^11 + 47*X^10 + 4*X^9 + 28*X^8 + 27*X^7 + 30*X^6 + 48*X^5 +
      54*X^4 + 55*X^3 + 5*X^2 + 48*X + 45) :=
  sq_step (by norm_num) pSeventeenA4s251 ⟨
    55*X^32 + 64*X^31 + 66*X^30 + 10*X^29 + 10*X^28 + 16*X^27 + 42*X^26 + 38*X^25 + 40*X^24 + 12*X^23 +
      9*X^22 + 65*X^21 + 35*X^20 + 62*X^19 + 50*X^18 + 4*X^17 + 52*X^16 + 19*X^15 + 45*X^14 +
      19*X^13 + 20*X^12 + 4*X^11 + 28*X^10 + 62*X^9 + X^8 + 7*X^7 + 45*X^6 + 62*X^5 + 35*X^4 +
      30*X^3 + 27*X^2 + 31*X + 65,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s253 : XPow fSeventeenA4 444020944803615844652592563120685448998174421437156
    (21*X^33 + 9*X^32 + 40*X^31 + 13*X^30 + 65*X^29 + 61*X^28 + 31*X^27 + 54*X^26 + 35*X^25 + 60*X^24 +
      27*X^23 + 55*X^22 + 33*X^21 + 52*X^20 + 22*X^19 + X^18 + 34*X^17 + 18*X^16 + 29*X^15 + 13*X^14 +
      15*X^13 + 5*X^12 + 2*X^11 + 23*X^10 + 63*X^9 + 41*X^8 + 6*X^7 + 51*X^6 + 62*X^5 + 21*X^4 +
      42*X^3 + 57*X^2 + 33*X + 11) :=
  sq_step (by norm_num) pSeventeenA4s252 ⟨
    62*X^32 + 19*X^31 + 33*X^30 + 38*X^29 + 64*X^28 + 63*X^27 + 52*X^26 + 48*X^25 + 45*X^24 + 4*X^23 +
      47*X^22 + 9*X^21 + 36*X^20 + 33*X^19 + 64*X^18 + 28*X^17 + 28*X^16 + X^15 + 25*X^14 + 26*X^13 +
      40*X^12 + 59*X^11 + 55*X^10 + 50*X^9 + 33*X^8 + 66*X^7 + 31*X^6 + 33*X^5 + 17*X^4 + X^3 +
      26*X^2 + 21*X + 50,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s254 : XPow fSeventeenA4 444020944803615844652592563120685448998174421437157
    (6*X^33 + 23*X^32 + 36*X^31 + 17*X^29 + 24*X^28 + 34*X^27 + 27*X^26 + 48*X^25 + 39*X^24 + 31*X^23 +
      63*X^22 + 29*X^21 + 23*X^20 + 63*X^19 + 36*X^18 + 15*X^17 + 19*X^16 + 8*X^15 + 22*X^14 +
      47*X^13 + 63*X^12 + 12*X^11 + 36*X^10 + 27*X^9 + 52*X^8 + 31*X^7 + 22*X^6 + 22*X^5 + 33*X^4 +
      49*X^3 + 24*X^2 + 11*X + 1) :=
  mul_step (by norm_num) pSeventeenA4s253 pSeventeenA41 ⟨
    21,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s255 : XPow fSeventeenA4 888041889607231689305185126241370897996348842874314
    (36*X^33 + 30*X^32 + 60*X^31 + 9*X^30 + 40*X^29 + 8*X^28 + 50*X^27 + 11*X^26 + 52*X^25 + 30*X^24 +
      29*X^23 + 52*X^22 + 18*X^21 + 30*X^20 + 45*X^19 + 26*X^18 + 37*X^17 + 15*X^16 + 25*X^15 +
      39*X^14 + 65*X^13 + 21*X^12 + 48*X^11 + 23*X^10 + 9*X^9 + 36*X^8 + 25*X^7 + 14*X^6 + 47*X^5 +
      57*X^3 + 37*X^2 + 43*X + 24) :=
  sq_step (by norm_num) pSeventeenA4s254 ⟨
    36*X^32 + 22*X^31 + 29*X^30 + 24*X^29 + 33*X^28 + 28*X^27 + 9*X^26 + 9*X^25 + 3*X^24 + 46*X^23 +
      5*X^22 + 51*X^21 + 49*X^20 + 29*X^19 + 5*X^18 + 22*X^17 + 11*X^16 + 44*X^15 + 59*X^14 +
      45*X^13 + 20*X^12 + 35*X^11 + 10*X^10 + 11*X^9 + 29*X^8 + 42*X^7 + 50*X^6 + 26*X^5 + 38*X^3 +
      34*X^2 + 39*X + 14,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s256 : XPow fSeventeenA4 888041889607231689305185126241370897996348842874315
    (44*X^33 + 50*X^32 + 58*X^31 + 53*X^30 + 57*X^29 + 38*X^28 + 15*X^27 + 19*X^25 + 40*X^24 + 30*X^23 +
      12*X^22 + 48*X^21 + 18*X^20 + 27*X^19 + 50*X^18 + 29*X^17 + 27*X^16 + 40*X^15 + 10*X^14 +
      26*X^13 + 9*X^12 + 52*X^11 + X^10 + 12*X^9 + 56*X^8 + 18*X^7 + 55*X^6 + 40*X^5 + 32*X^4 +
      52*X^3 + 18*X^2 + 24*X + 40) :=
  mul_step (by norm_num) pSeventeenA4s255 pSeventeenA41 ⟨
    36,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s257 : XPow fSeventeenA4 1776083779214463378610370252482741795992697685748630
    (9*X^33 + 26*X^32 + 40*X^31 + 46*X^30 + 58*X^29 + 47*X^28 + 59*X^27 + 48*X^26 + 39*X^25 + 38*X^24 +
      66*X^23 + 54*X^22 + 8*X^21 + 29*X^20 + 57*X^19 + 46*X^18 + 14*X^17 + 27*X^16 + 8*X^15 +
      35*X^14 + 63*X^13 + 51*X^12 + 6*X^11 + 7*X^10 + 15*X^9 + 40*X^8 + 46*X^7 + 8*X^6 + 29*X^5 +
      11*X^4 + 46*X^3 + 42*X^2 + 30*X + 10) :=
  sq_step (by norm_num) pSeventeenA4s256 ⟨
    60*X^32 + 46*X^31 + 64*X^30 + 9*X^29 + 15*X^28 + 34*X^27 + 9*X^26 + 42*X^25 + 63*X^24 + 11*X^23 +
      64*X^22 + 50*X^21 + 10*X^20 + 43*X^19 + 40*X^18 + 66*X^17 + 46*X^16 + 21*X^15 + 20*X^14 +
      44*X^13 + 32*X^12 + 22*X^11 + 10*X^10 + 40*X^9 + 11*X^8 + 35*X^7 + 6*X^6 + 42*X^5 + 26*X^4 +
      25*X^3 + 4*X^2 + 41*X + 43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s258 : XPow fSeventeenA4 1776083779214463378610370252482741795992697685748631
    (63*X^33 + 4*X^32 + 8*X^31 + 11*X^30 + 9*X^29 + 56*X^28 + 49*X^27 + 26*X^26 + 52*X^25 + 52*X^24 +
      15*X^23 + 40*X^22 + 63*X^19 + 34*X^18 + 64*X^17 + 42*X^16 + 52*X^15 + 66*X^14 + 2*X^13 +
      13*X^12 + 31*X^11 + 13*X^10 + 34*X^9 + 37*X^8 + 9*X^7 + 31*X^6 + 21*X^5 + 23*X^4 + 29*X^3 +
      7*X^2 + 10*X + 10) :=
  mul_step (by norm_num) pSeventeenA4s257 pSeventeenA41 ⟨
    9,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s259 : XPow fSeventeenA4 3552167558428926757220740504965483591985395371497262
    (48*X^33 + 46*X^32 + 17*X^31 + 19*X^30 + 17*X^29 + 46*X^28 + 4*X^27 + 16*X^26 + 8*X^25 + 52*X^24 +
      22*X^23 + 33*X^22 + 24*X^21 + 26*X^20 + 4*X^19 + 23*X^18 + 20*X^17 + 39*X^16 + 27*X^15 +
      57*X^14 + 50*X^13 + 13*X^12 + 25*X^11 + 15*X^10 + 28*X^9 + 41*X^8 + 12*X^7 + 46*X^6 + 5*X^5 +
      15*X^4 + 29*X^3 + 17*X^2 + 55*X + 22) :=
  sq_step (by norm_num) pSeventeenA4s258 ⟨
    16*X^32 + 4*X^31 + 31*X^30 + 5*X^29 + 25*X^28 + 58*X^27 + 16*X^26 + X^25 + 18*X^23 + 43*X^22 +
      60*X^21 + 13*X^20 + 12*X^19 + 45*X^18 + 31*X^17 + 26*X^16 + 4*X^15 + 10*X^14 + 64*X^13 +
      54*X^12 + 8*X^11 + 6*X^10 + 36*X^9 + 25*X^7 + 32*X^6 + 51*X^5 + 29*X^4 + 54*X^3 + 5*X^2 + 37*X +
      37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s260 : XPow fSeventeenA4 3552167558428926757220740504965483591985395371497263
    (20*X^33 + 26*X^32 + 62*X^31 + 12*X^30 + 22*X^29 + 55*X^28 + 66*X^27 + 28*X^26 + 15*X^25 + 59*X^24 +
      26*X^23 + 16*X^22 + 50*X^21 + 35*X^20 + 2*X^19 + 15*X^18 + 13*X^17 + 52*X^16 + 36*X^15 +
      66*X^14 + 42*X^13 + 40*X^12 + 9*X^11 + 62*X^10 + 9*X^9 + 31*X^8 + 29*X^7 + 38*X^6 + 46*X^5 +
      18*X^4 + 37*X^3 + 44*X^2 + 22*X + 31) :=
  mul_step (by norm_num) pSeventeenA4s259 pSeventeenA41 ⟨
    48,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s261 : XPow fSeventeenA4 7104335116857853514441481009930967183970790742994526
    (24*X^33 + 2*X^32 + 33*X^30 + 34*X^29 + X^28 + 50*X^27 + 12*X^26 + 61*X^25 + 18*X^24 + 23*X^23 +
      51*X^22 + 21*X^21 + 43*X^20 + 40*X^19 + 41*X^18 + 23*X^17 + 18*X^16 + 30*X^15 + 66*X^14 +
      52*X^13 + 58*X^12 + 59*X^11 + 20*X^10 + 27*X^9 + 54*X^8 + 4*X^7 + 26*X^6 + 44*X^5 + 29*X^4 +
      34*X^3 + 15*X + 37) :=
  sq_step (by norm_num) pSeventeenA4s260 ⟨
    65*X^32 + 64*X^31 + 25*X^30 + 38*X^29 + 45*X^28 + 34*X^27 + 29*X^26 + 23*X^24 + 13*X^23 + 60*X^22 +
      51*X^21 + 27*X^20 + 37*X^19 + 58*X^18 + 3*X^17 + 30*X^16 + 6*X^15 + 28*X^14 + 39*X^13 +
      44*X^12 + 44*X^11 + 29*X^10 + 28*X^9 + 5*X^8 + 58*X^7 + X^6 + 18*X^5 + 58*X^4 + 37*X^3 +
      50*X^2 + 12*X + 26,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s262 : XPow fSeventeenA4 7104335116857853514441481009930967183970790742994527
    (56*X^33 + 38*X^32 + 21*X^31 + 65*X^30 + 56*X^29 + 42*X^28 + 37*X^27 + 4*X^26 + 33*X^25 + 8*X^24 +
      14*X^23 + 17*X^22 + 55*X^21 + 22*X^20 + 64*X^19 + 54*X^18 + 5*X^17 + 9*X^16 + 22*X^15 +
      60*X^14 + 39*X^13 + 33*X^12 + 17*X^11 + 44*X^10 + 38*X^9 + 47*X^8 + 51*X^7 + 27*X^6 + 11*X^5 +
      62*X^4 + 10*X^3 + 43*X^2 + 37*X + 49) :=
  mul_step (by norm_num) pSeventeenA4s261 pSeventeenA41 ⟨
    24,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s263 : XPow fSeventeenA4 14208670233715707028882962019861934367941581485989054
    (46*X^33 + 62*X^32 + 41*X^31 + 5*X^30 + X^29 + 41*X^28 + 29*X^27 + 47*X^26 + 27*X^25 + 18*X^24 +
      18*X^23 + 5*X^22 + 10*X^21 + 15*X^20 + 50*X^19 + 59*X^18 + 48*X^17 + 56*X^16 + 43*X^15 +
      46*X^14 + 14*X^13 + 61*X^12 + 27*X^11 + 30*X^10 + 32*X^9 + 62*X^8 + 25*X^7 + 33*X^6 + 59*X^5 +
      31*X^4 + 3*X^3 + 13*X^2 + 63*X + 31) :=
  sq_step (by norm_num) pSeventeenA4s262 ⟨
    54*X^32 + 56*X^31 + 21*X^30 + 46*X^29 + 6*X^28 + 8*X^27 + 38*X^26 + 46*X^25 + 47*X^24 + 31*X^23 +
      17*X^22 + 8*X^21 + 56*X^20 + 5*X^19 + 30*X^18 + 45*X^17 + 46*X^16 + 53*X^15 + 60*X^14 +
      52*X^13 + 20*X^12 + 42*X^11 + 66*X^10 + 61*X^9 + 38*X^8 + 3*X^7 + 52*X^6 + 22*X^5 + 8*X^4 +
      60*X^3 + 44*X^2 + 16*X + 11,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s264 : XPow fSeventeenA4 14208670233715707028882962019861934367941581485989055
    (65*X^33 + 58*X^32 + 49*X^31 + 66*X^30 + 18*X^29 + 36*X^28 + 35*X^26 + 30*X^25 + 6*X^24 + 29*X^23 +
      47*X^22 + 38*X^21 + 49*X^20 + 64*X^19 + 46*X^18 + 59*X^17 + 53*X^16 + 51*X^15 + 7*X^14 +
      19*X^13 + 33*X^12 + 41*X^11 + 59*X^10 + 9*X^9 + 46*X^8 + 53*X^7 + 32*X^6 + 30*X^5 + 12*X^4 +
      21*X^3 + 5*X^2 + 31*X + 66) :=
  mul_step (by norm_num) pSeventeenA4s263 pSeventeenA41 ⟨
    46,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s265 : XPow fSeventeenA4 28417340467431414057765924039723868735883162971978110
    (27*X^33 + 55*X^32 + 29*X^31 + 60*X^30 + 2*X^29 + 64*X^28 + 55*X^27 + 63*X^26 + 63*X^25 + 28*X^24 +
      37*X^23 + 36*X^22 + 48*X^21 + 46*X^20 + 43*X^19 + 17*X^18 + 13*X^17 + 58*X^16 + 8*X^15 +
      58*X^14 + 2*X^13 + 40*X^12 + 63*X^11 + 54*X^10 + 59*X^9 + 10*X^8 + 25*X^7 + 32*X^6 + 28*X^5 +
      44*X^4 + 61*X^3 + 30*X^2 + 18*X + 3) :=
  sq_step (by norm_num) pSeventeenA4s264 ⟨
    4*X^32 + 45*X^31 + 54*X^30 + 33*X^29 + 16*X^28 + 12*X^27 + 43*X^26 + 28*X^25 + 61*X^24 + 2*X^23 +
      66*X^22 + 3*X^21 + 4*X^20 + 14*X^19 + 24*X^18 + 21*X^17 + 63*X^16 + 22*X^15 + 36*X^14 +
      44*X^13 + 36*X^12 + 64*X^11 + 15*X^10 + 35*X^9 + 41*X^8 + 35*X^7 + 45*X^6 + 42*X^5 + 24*X^4 +
      54*X^3 + 65*X^2 + 5*X + 42,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s266 : XPow fSeventeenA4 56834680934862828115531848079447737471766325943956220
    (26*X^33 + 14*X^32 + 44*X^31 + 16*X^30 + 5*X^29 + 45*X^28 + 47*X^27 + 36*X^26 + 39*X^25 + 29*X^24 +
      12*X^23 + 47*X^22 + 44*X^21 + 47*X^20 + 51*X^19 + 38*X^18 + 51*X^17 + 3*X^16 + 4*X^15 + 6*X^14 +
      18*X^13 + 14*X^12 + 18*X^11 + 53*X^10 + 42*X^9 + 17*X^8 + 26*X^7 + 5*X^6 + 43*X^5 + 38*X^4 +
      3*X^3 + 20*X^2 + 43*X + 56) :=
  sq_step (by norm_num) pSeventeenA4s265 ⟨
    59*X^32 + 4*X^31 + 9*X^30 + 23*X^29 + 54*X^28 + 10*X^27 + 30*X^26 + 34*X^25 + 36*X^24 + 3*X^23 +
      39*X^22 + 17*X^21 + 48*X^20 + 47*X^19 + 34*X^18 + 21*X^17 + 45*X^16 + 20*X^15 + 4*X^14 +
      20*X^13 + 54*X^12 + 41*X^11 + 40*X^10 + 18*X^9 + 25*X^8 + 14*X^7 + 41*X^6 + X^5 + 20*X^4 +
      14*X^3 + 59*X^2 + 42*X + 49,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s267 : XPow fSeventeenA4 113669361869725656231063696158895474943532651887912440
    (34*X^33 + 37*X^32 + 9*X^31 + 28*X^30 + 11*X^29 + 62*X^28 + 29*X^27 + 33*X^26 + 49*X^25 + 8*X^24 +
      65*X^23 + 47*X^22 + 6*X^21 + 49*X^20 + 22*X^19 + 27*X^18 + 32*X^17 + 33*X^16 + 28*X^15 +
      53*X^14 + 34*X^13 + 64*X^12 + 27*X^11 + 58*X^10 + 28*X^9 + 19*X^8 + 13*X^7 + 24*X^6 + 4*X^5 +
      51*X^4 + 33*X^3 + 57*X^2 + 66*X + 5) :=
  sq_step (by norm_num) pSeventeenA4s266 ⟨
    6*X^32 + 38*X^31 + 33*X^30 + 57*X^29 + 16*X^28 + 35*X^27 + 11*X^26 + 19*X^25 + 32*X^24 + 35*X^23 +
      15*X^22 + 17*X^21 + 44*X^20 + 24*X^19 + 65*X^18 + 61*X^17 + 64*X^16 + 66*X^15 + 30*X^14 +
      11*X^13 + 7*X^12 + 17*X^11 + 64*X^10 + 27*X^9 + 12*X^8 + 48*X^7 + 60*X^6 + 22*X^5 + 16*X^4 +
      54*X^3 + X^2 + 13*X + 43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s268 : XPow fSeventeenA4 227338723739451312462127392317790949887065303775824880
    (12*X^33 + 51*X^32 + 52*X^31 + 51*X^30 + 25*X^29 + 64*X^28 + 46*X^27 + 4*X^26 + 35*X^25 + 42*X^24 +
      17*X^23 + 39*X^22 + 30*X^21 + 64*X^20 + 3*X^19 + 29*X^18 + 38*X^17 + 62*X^16 + 13*X^15 +
      45*X^14 + 7*X^13 + 46*X^12 + 30*X^11 + 65*X^10 + 24*X^9 + 6*X^8 + 43*X^7 + 56*X^6 + 10*X^5 +
      32*X^4 + 64*X^3 + 5*X^2 + 4*X + 60) :=
  sq_step (by norm_num) pSeventeenA4s267 ⟨
    17*X^32 + 25*X^31 + 43*X^30 + 29*X^29 + 26*X^28 + 49*X^27 + 42*X^26 + 14*X^25 + 9*X^24 + 66*X^23 +
      45*X^22 + 15*X^21 + 57*X^20 + 57*X^19 + 57*X^18 + 14*X^17 + 43*X^16 + 62*X^15 + 38*X^14 +
      17*X^13 + 29*X^12 + 36*X^11 + 22*X^10 + 50*X^9 + 55*X^8 + 17*X^7 + 20*X^6 + 6*X^5 + 21*X^4 +
      41*X^3 + 22*X^2 + 26*X + 65,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s269 : XPow fSeventeenA4 454677447478902624924254784635581899774130607551649760
    (16*X^33 + 38*X^32 + 65*X^31 + 54*X^30 + 58*X^29 + 5*X^28 + 49*X^27 + 20*X^26 + 46*X^24 + 8*X^23 +
      65*X^22 + 15*X^21 + 13*X^20 + 8*X^19 + 20*X^18 + 55*X^17 + 63*X^16 + 2*X^15 + 58*X^14 +
      16*X^13 + 60*X^12 + 56*X^11 + 2*X^10 + 44*X^9 + 37*X^8 + 45*X^7 + 38*X^6 + 60*X^5 + 54*X^4 +
      38*X^3 + 10*X^2 + 36*X + 38) :=
  sq_step (by norm_num) pSeventeenA4s268 ⟨
    10*X^32 + 7*X^31 + 56*X^30 + 55*X^29 + 29*X^28 + 63*X^27 + 16*X^26 + 21*X^25 + 41*X^24 + 35*X^23 +
      57*X^22 + 50*X^21 + 5*X^20 + 2*X^19 + 7*X^18 + 60*X^17 + 18*X^16 + 25*X^15 + 5*X^13 + 17*X^12 +
      47*X^11 + 16*X^10 + 2*X^9 + 31*X^8 + 18*X^7 + 51*X^6 + 27*X^5 + 64*X^4 + 10*X^3 + 2*X^2 + 56*X +
      37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s270 : XPow fSeventeenA4 909354894957805249848509569271163799548261215103299520
    (35*X^33 + 50*X^32 + 13*X^31 + 52*X^30 + 30*X^29 + 29*X^28 + 43*X^27 + 51*X^26 + 53*X^25 + 62*X^24 +
      28*X^23 + 18*X^22 + 56*X^21 + 50*X^20 + 17*X^19 + 3*X^18 + 57*X^17 + 43*X^16 + 29*X^15 +
      56*X^14 + 27*X^13 + 30*X^12 + 34*X^11 + 25*X^9 + 15*X^8 + 12*X^7 + 59*X^6 + 42*X^5 + 54*X^4 +
      29*X^3 + 4*X^2 + 25*X + 39) :=
  sq_step (by norm_num) pSeventeenA4s269 ⟨
    55*X^32 + 50*X^31 + 33*X^30 + 66*X^29 + 44*X^28 + 48*X^27 + 5*X^26 + 4*X^25 + 66*X^24 + 59*X^23 +
      50*X^22 + 58*X^21 + 42*X^20 + 44*X^19 + 55*X^18 + 29*X^17 + 65*X^16 + 34*X^15 + 23*X^14 +
      39*X^13 + X^12 + 25*X^11 + 52*X^10 + 60*X^9 + 15*X^8 + 6*X^7 + 52*X^6 + 63*X^5 + 61*X^4 +
      53*X^3 + 32*X^2 + 19*X + 42,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s271 : XPow fSeventeenA4 1818709789915610499697019138542327599096522430206599040
    (30*X^33 + 4*X^32 + 54*X^31 + 49*X^30 + 58*X^29 + 18*X^28 + 53*X^27 + 23*X^26 + 62*X^25 + 11*X^24 +
      53*X^23 + 16*X^22 + 8*X^21 + 13*X^20 + 60*X^19 + 57*X^18 + 44*X^17 + 66*X^16 + 22*X^15 +
      39*X^14 + 58*X^13 + 24*X^12 + 31*X^11 + 58*X^10 + 36*X^9 + 29*X^8 + 60*X^7 + 34*X^6 + 40*X^5 +
      8*X^4 + 32*X^3 + 3*X^2 + 50*X + 29) :=
  sq_step (by norm_num) pSeventeenA4s270 ⟨
    19*X^32 + 42*X^31 + 45*X^30 + 23*X^29 + 5*X^28 + 59*X^27 + 26*X^26 + 53*X^25 + 51*X^24 + 5*X^23 +
      30*X^22 + 22*X^21 + 47*X^20 + 10*X^19 + 62*X^18 + 37*X^17 + 27*X^16 + 5*X^15 + 24*X^14 +
      48*X^13 + 61*X^12 + 5*X^11 + 3*X^10 + 15*X^9 + 37*X^8 + 42*X^7 + 65*X^6 + 14*X^5 + 12*X^4 +
      35*X^3 + 32*X^2 + 32*X + 24,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s272 : XPow fSeventeenA4 3637419579831220999394038277084655198193044860413198080
    (40*X^33 + 55*X^32 + 11*X^31 + 43*X^30 + 40*X^29 + 28*X^28 + 17*X^27 + 11*X^26 + 44*X^25 + 51*X^24 +
      44*X^23 + 61*X^22 + 20*X^21 + 35*X^20 + 38*X^19 + 21*X^18 + 30*X^17 + 28*X^16 + 10*X^14 +
      46*X^13 + 28*X^12 + 51*X^11 + 66*X^10 + 47*X^9 + 51*X^8 + 37*X^7 + 44*X^6 + 47*X^5 + 51*X^4 +
      51*X^3 + 48*X^2 + 63*X + 14) :=
  sq_step (by norm_num) pSeventeenA4s271 ⟨
    29*X^32 + 54*X^31 + 12*X^30 + 53*X^29 + 5*X^28 + 18*X^27 + 47*X^26 + 63*X^25 + 19*X^24 + 45*X^23 +
      58*X^22 + 44*X^21 + 13*X^20 + 21*X^19 + 53*X^18 + 50*X^17 + 11*X^16 + 37*X^15 + 46*X^14 +
      53*X^13 + 46*X^12 + 11*X^11 + 33*X^10 + 34*X^9 + 30*X^8 + 5*X^7 + 65*X^6 + 25*X^5 + 40*X^4 +
      45*X^3 + 3*X^2 + 53*X + 53,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s273 : XPow fSeventeenA4 3637419579831220999394038277084655198193044860413198081
    (11*X^33 + 52*X^32 + 23*X^31 + 47*X^30 + 8*X^29 + 26*X^28 + 8*X^27 + 16*X^26 + 9*X^25 + 19*X^24 +
      44*X^23 + 58*X^22 + 55*X^21 + 8*X^20 + 37*X^19 + 37*X^18 + 51*X^17 + 32*X^16 + 26*X^15 +
      37*X^14 + 41*X^13 + 30*X^12 + 61*X^11 + 53*X^10 + 2*X^9 + 64*X^8 + 41*X^7 + 41*X^6 + 21*X^5 +
      53*X^4 + 20*X^3 + 65*X^2 + 14*X + 37) :=
  mul_step (by norm_num) pSeventeenA4s272 pSeventeenA41 ⟨
    40,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s274 : XPow fSeventeenA4 7274839159662441998788076554169310396386089720826396162
    (12*X^33 + 7*X^32 + 13*X^31 + 18*X^30 + 17*X^29 + 62*X^28 + 41*X^27 + 15*X^26 + 34*X^25 + 32*X^24 +
      63*X^23 + 63*X^22 + 63*X^21 + 4*X^20 + 66*X^19 + 44*X^18 + 61*X^17 + 49*X^16 + 42*X^15 +
      18*X^14 + 43*X^12 + 25*X^11 + 29*X^10 + 51*X^9 + 5*X^8 + 15*X^7 + 49*X^6 + 4*X^5 + 20*X^4 +
      33*X^3 + 7*X^2 + 3*X + 45) :=
  sq_step (by norm_num) pSeventeenA4s273 ⟨
    54*X^32 + 26*X^31 + 4*X^30 + 21*X^29 + 53*X^28 + 66*X^27 + 53*X^26 + 38*X^25 + 31*X^24 + 17*X^23 +
      52*X^22 + 18*X^21 + 29*X^20 + 23*X^19 + 24*X^18 + 42*X^17 + 47*X^16 + 36*X^15 + 50*X^14 +
      17*X^13 + 17*X^12 + 6*X^11 + 56*X^10 + 23*X^9 + 22*X^8 + 11*X^7 + 32*X^6 + 49*X^5 + 46*X^4 +
      10*X^3 + 19*X^2 + 15*X + 1,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s275 : XPow fSeventeenA4 14549678319324883997576153108338620792772179441652792324
    (58*X^33 + 26*X^32 + 56*X^31 + 32*X^30 + 3*X^29 + 59*X^28 + 26*X^27 + 3*X^26 + 59*X^25 + 33*X^24 +
      25*X^23 + 5*X^22 + 51*X^21 + 50*X^20 + 41*X^19 + 55*X^18 + 61*X^17 + 62*X^16 + 7*X^15 +
      11*X^14 + 29*X^13 + 6*X^12 + 2*X^11 + 54*X^10 + 35*X^9 + 18*X^8 + 60*X^7 + 10*X^6 + 51*X^5 +
      30*X^4 + 65*X^3 + 44*X^2 + 11*X + 43) :=
  sq_step (by norm_num) pSeventeenA4s274 ⟨
    10*X^32 + 23*X^31 + 21*X^30 + 45*X^29 + 66*X^28 + 2*X^27 + 34*X^26 + 53*X^25 + 31*X^24 + 40*X^23 +
      59*X^22 + 31*X^21 + 62*X^20 + 6*X^19 + 12*X^18 + 54*X^17 + 46*X^16 + 57*X^15 + 4*X^14 +
      35*X^13 + 64*X^12 + 64*X^11 + 10*X^10 + 17*X^9 + 53*X^8 + 62*X^7 + 23*X^6 + 32*X^5 + 53*X^4 +
      61*X^3 + 33*X^2 + 55*X + 52,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s276 : XPow fSeventeenA4 29099356638649767995152306216677241585544358883305584648
    (22*X^33 + 57*X^32 + 7*X^31 + 4*X^30 + 60*X^29 + 33*X^28 + 58*X^27 + 42*X^26 + 41*X^25 + 24*X^24 +
      4*X^23 + 34*X^22 + 52*X^21 + 64*X^20 + X^19 + 2*X^18 + 36*X^17 + 17*X^16 + 59*X^15 + 16*X^14 +
      28*X^13 + 58*X^12 + 13*X^11 + 13*X^10 + 51*X^9 + 5*X^8 + X^7 + 59*X^6 + 24*X^5 + 56*X^4 +
      24*X^3 + 57*X^2 + 44*X + 15) :=
  sq_step (by norm_num) pSeventeenA4s275 ⟨
    14*X^32 + 66*X^31 + 62*X^30 + 27*X^29 + 66*X^28 + 2*X^27 + 50*X^26 + 45*X^25 + 27*X^24 + 44*X^23 +
      55*X^22 + 7*X^21 + 46*X^20 + 40*X^19 + 12*X^18 + 31*X^17 + 60*X^16 + 31*X^15 + 21*X^14 +
      5*X^13 + 44*X^12 + 38*X^11 + X^10 + 21*X^9 + 57*X^8 + 9*X^7 + 38*X^6 + 44*X^5 + 8*X^4 + 60*X^3 +
      26*X^2 + 19*X + 11,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s277 : XPow fSeventeenA4 29099356638649767995152306216677241585544358883305584649
    (6*X^33 + 53*X^32 + 60*X^31 + 27*X^30 + 22*X^29 + 6*X^28 + 37*X^27 + 39*X^26 + 21*X^25 + 7*X^24 +
      28*X^23 + 26*X^22 + 8*X^21 + 18*X^20 + 51*X^19 + 3*X^18 + 33*X^17 + 23*X^16 + 65*X^15 +
      13*X^14 + 35*X^13 + 45*X^12 + 27*X^11 + 61*X^10 + 35*X^9 + 46*X^8 + 54*X^7 + 14*X^6 + 6*X^5 +
      5*X^4 + 55*X^3 + 25*X^2 + 15*X + 17) :=
  mul_step (by norm_num) pSeventeenA4s276 pSeventeenA41 ⟨
    22,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s278 : XPow fSeventeenA4 58198713277299535990304612433354483171088717766611169298
    (9*X^33 + 19*X^32 + 47*X^31 + 58*X^30 + X^29 + 58*X^28 + 46*X^27 + 59*X^26 + 38*X^25 + 7*X^24 +
      31*X^23 + 38*X^22 + 4*X^21 + 12*X^20 + 34*X^19 + 43*X^18 + 55*X^17 + 26*X^16 + 11*X^15 +
      6*X^14 + 29*X^13 + 29*X^12 + 41*X^11 + 41*X^10 + 45*X^9 + 51*X^8 + 58*X^7 + 49*X^6 + 26*X^5 +
      13*X^4 + 29*X^3 + 32*X^2 + 23*X + 64) :=
  sq_step (by norm_num) pSeventeenA4s277 ⟨
    36*X^32 + 47*X^31 + 57*X^30 + 57*X^29 + 33*X^28 + 30*X^27 + 14*X^26 + 15*X^25 + 19*X^24 + 39*X^23 +
      62*X^22 + 46*X^21 + 26*X^20 + 28*X^19 + 58*X^18 + 61*X^17 + 53*X^16 + 37*X^15 + 37*X^14 +
      21*X^13 + 57*X^12 + 64*X^11 + 23*X^10 + 38*X^9 + 19*X^8 + 55*X^7 + 34*X^6 + 38*X^5 + 26*X^4 +
      63*X^3 + 26*X^2 + 24*X + 32,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s279 : XPow fSeventeenA4 116397426554599071980609224866708966342177435533222338596
    (42*X^33 + 42*X^32 + 17*X^31 + 11*X^30 + X^29 + X^28 + 56*X^27 + 57*X^26 + 42*X^25 + 40*X^24 +
      62*X^23 + 7*X^22 + 19*X^21 + 24*X^20 + 24*X^19 + 59*X^18 + 53*X^17 + 32*X^16 + 38*X^15 +
      11*X^14 + 29*X^13 + 52*X^12 + 65*X^11 + 37*X^10 + 41*X^9 + 27*X^8 + 56*X^7 + 22*X^6 + 37*X^5 +
      54*X^4 + 47*X^3 + 62*X^2 + 39*X + 27) :=
  sq_step (by norm_num) pSeventeenA4s278 ⟨
    14*X^32 + 5*X^31 + 40*X^30 + 12*X^29 + 20*X^28 + 31*X^27 + 36*X^26 + 31*X^25 + 35*X^24 + 18*X^23 +
      48*X^22 + 21*X^21 + 32*X^20 + 37*X^19 + 3*X^18 + 22*X^17 + 9*X^16 + 46*X^15 + 10*X^14 +
      16*X^13 + 25*X^12 + 17*X^11 + 52*X^10 + 63*X^9 + 15*X^8 + 2*X^7 + 5*X^6 + 40*X^5 + 9*X^4 +
      22*X^3 + 39*X^2 + 32*X + 43,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s280 : XPow fSeventeenA4 116397426554599071980609224866708966342177435533222338597
    (36*X^33 + 50*X^32 + 57*X^31 + 5*X^30 + 47*X^29 + 42*X^28 + 17*X^27 + 26*X^26 + 16*X^25 + 19*X^24 +
      26*X^23 + 12*X^22 + 45*X^21 + 26*X^20 + 49*X^19 + 57*X^18 + 26*X^17 + 18*X^16 + X^15 + 43*X^14 +
      2*X^13 + 53*X^12 + 15*X^11 + 54*X^10 + 66*X^9 + 14*X^8 + 49*X^7 + 24*X^6 + 56*X^5 + 29*X^4 +
      46*X^3 + 21*X^2 + 27*X + 2) :=
  mul_step (by norm_num) pSeventeenA4s279 pSeventeenA41 ⟨
    42,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s281 : XPow fSeventeenA4 232794853109198143961218449733417932684354871066444677194
    (51*X^33 + 24*X^32 + 5*X^31 + 15*X^30 + 42*X^29 + 38*X^28 + 58*X^27 + 57*X^26 + 11*X^25 + 24*X^24 +
      39*X^23 + 11*X^22 + 57*X^21 + 44*X^20 + 18*X^19 + 3*X^18 + 62*X^17 + 26*X^16 + 55*X^15 +
      11*X^14 + 59*X^13 + 63*X^12 + 37*X^11 + 27*X^10 + 40*X^9 + 19*X^8 + 65*X^7 + 26*X^6 + 29*X^5 +
      62*X^4 + 22*X^3 + 28*X^2 + 13*X + 59) :=
  sq_step (by norm_num) pSeventeenA4s280 ⟨
    23*X^32 + 17*X^31 + X^30 + 3*X^29 + 41*X^28 + 12*X^27 + 9*X^26 + 32*X^25 + 58*X^24 + 48*X^23 +
      8*X^22 + 21*X^21 + 14*X^20 + 60*X^19 + 35*X^18 + 58*X^17 + 14*X^16 + 55*X^15 + 5*X^13 +
      30*X^12 + 31*X^11 + 34*X^10 + 4*X^9 + 10*X^8 + 44*X^7 + 49*X^6 + 37*X^5 + 11*X^4 + 48*X^3 +
      7*X^2 + 15*X + 16,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s282 : XPow fSeventeenA4 465589706218396287922436899466835865368709742132889354388
    (14*X^33 + 10*X^32 + 54*X^31 + 16*X^30 + 5*X^29 + 29*X^28 + 20*X^27 + 54*X^26 + 31*X^25 + 54*X^24 +
      33*X^23 + 60*X^22 + 59*X^21 + 40*X^20 + 45*X^19 + 3*X^18 + 54*X^17 + 58*X^16 + 22*X^15 +
      3*X^14 + 58*X^13 + 51*X^12 + 12*X^11 + 60*X^10 + 10*X^9 + 41*X^8 + 21*X^7 + 50*X^6 + 51*X^5 +
      62*X^4 + 23*X^3 + 16*X^2 + 39*X + 24) :=
  sq_step (by norm_num) pSeventeenA4s281 ⟨
    55*X^32 + 9*X^31 + 32*X^30 + 3*X^29 + 47*X^28 + 32*X^27 + 45*X^26 + 18*X^25 + 9*X^24 + 64*X^23 +
      35*X^22 + 61*X^21 + 32*X^20 + 40*X^19 + 33*X^18 + 12*X^17 + 33*X^16 + 24*X^15 + 49*X^14 +
      22*X^13 + 26*X^12 + 12*X^11 + 8*X^10 + 45*X^9 + 33*X^8 + 49*X^7 + 35*X^6 + 48*X^5 + 33*X^4 +
      55*X^3 + 42*X^2 + 28*X + 31,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s283 : XPow fSeventeenA4 465589706218396287922436899466835865368709742132889354389
    (8*X^33 + 65*X^32 + 9*X^31 + 51*X^30 + 22*X^29 + 60*X^28 + 63*X^27 + 48*X^26 + 46*X^25 + 41*X^24 +
      44*X^23 + 12*X^22 + 47*X^21 + X^20 + 22*X^19 + 33*X^18 + 56*X^17 + 60*X^16 + 22*X^15 + 18*X^14 +
      12*X^13 + 8*X^12 + 8*X^11 + 59*X^10 + 54*X^9 + 7*X^8 + 59*X^7 + 2*X^6 + 18*X^5 + 17*X^4 +
      33*X^3 + 33*X^2 + 24*X + 23) :=
  mul_step (by norm_num) pSeventeenA4s282 pSeventeenA41 ⟨
    14,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s284 : XPow fSeventeenA4 931179412436792575844873798933671730737419484265778708778
    (54*X^33 + 49*X^32 + 36*X^31 + 9*X^30 + 62*X^29 + 8*X^28 + 20*X^27 + 30*X^26 + 28*X^25 + 49*X^24 +
      17*X^23 + 41*X^22 + 56*X^21 + 63*X^20 + 58*X^19 + 38*X^18 + 16*X^17 + 28*X^16 + 33*X^15 +
      43*X^14 + 56*X^13 + 6*X^12 + 28*X^11 + 48*X^10 + 37*X^9 + 7*X^8 + 31*X^7 + 8*X^6 + 57*X^5 +
      44*X^4 + 21*X^3 + 5*X^2 + 12*X + 4) :=
  sq_step (by norm_num) pSeventeenA4s283 ⟨
    64*X^32 + 45*X^31 + 10*X^30 + 21*X^29 + 34*X^28 + 3*X^27 + 21*X^26 + 60*X^25 + 35*X^24 + 59*X^23 +
      34*X^22 + 65*X^21 + 39*X^20 + 36*X^19 + 37*X^18 + 28*X^17 + 26*X^16 + 27*X^15 + 3*X^14 +
      44*X^13 + 38*X^12 + 64*X^11 + 37*X^10 + 19*X^9 + 23*X^8 + 12*X^7 + 60*X^6 + 34*X^5 + 12*X^4 +
      32*X^3 + 18*X^2 + 49*X + 30,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s285 : XPow fSeventeenA4 1862358824873585151689747597867343461474838968531557417556
    (53*X^33 + 7*X^32 + 42*X^31 + 63*X^30 + 13*X^29 + 2*X^28 + 23*X^27 + 37*X^26 + 53*X^25 + 51*X^24 +
      36*X^23 + 61*X^22 + 40*X^21 + 31*X^20 + 4*X^19 + 21*X^18 + 9*X^17 + 47*X^16 + 50*X^15 +
      18*X^14 + 45*X^13 + 42*X^12 + 2*X^11 + 47*X^10 + X^9 + 55*X^8 + X^7 + 43*X^6 + 32*X^5 + 5*X^4 +
      61*X^3 + 12*X^2 + 64*X + 46) :=
  sq_step (by norm_num) pSeventeenA4s284 ⟨
    35*X^32 + 61*X^31 + 5*X^30 + 12*X^29 + 21*X^28 + 22*X^27 + 40*X^26 + 20*X^25 + 35*X^24 + 58*X^23 +
      58*X^22 + 53*X^21 + 23*X^20 + 4*X^19 + 22*X^18 + 22*X^17 + 52*X^16 + 44*X^15 + 28*X^14 +
      25*X^13 + 11*X^12 + 37*X^11 + 20*X^10 + 3*X^9 + X^8 + 39*X^7 + 65*X^6 + 41*X^5 + 18*X^4 +
      54*X^3 + 48*X^2 + 65*X + 27,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s286 : XPow fSeventeenA4 1862358824873585151689747597867343461474838968531557417557
    (9*X^33 + 31*X^32 + 3*X^31 + 34*X^30 + 9*X^29 + 50*X^28 + 28*X^27 + 36*X^26 + 59*X^25 + 28*X^24 +
      10*X^23 + 20*X^22 + 24*X^21 + 48*X^20 + 2*X^19 + 30*X^18 + 49*X^17 + 12*X^16 + 66*X^15 +
      18*X^14 + 14*X^13 + 6*X^12 + 32*X^11 + 19*X^10 + 42*X^9 + 15*X^8 + 34*X^7 + 14*X^6 + 49*X^5 +
      62*X^3 + 3*X^2 + 46*X + 44) :=
  mul_step (by norm_num) pSeventeenA4s285 pSeventeenA41 ⟨
    53,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s287 : XPow fSeventeenA4 3724717649747170303379495195734686922949677937063114835114
    (50*X^33 + 30*X^32 + 32*X^31 + 60*X^30 + 22*X^29 + 59*X^28 + 60*X^27 + 62*X^26 + 48*X^25 + 21*X^24 +
      59*X^23 + 10*X^22 + 57*X^21 + 39*X^20 + 58*X^19 + 56*X^18 + 17*X^17 + 52*X^16 + 9*X^15 +
      10*X^14 + 8*X^13 + 20*X^12 + 43*X^11 + 20*X^10 + 49*X^9 + 22*X^8 + 30*X^7 + 63*X^6 + 48*X^5 +
      44*X^4 + 7*X^3 + 32*X^2 + 50*X + 29) :=
  sq_step (by norm_num) pSeventeenA4s286 ⟨
    14*X^32 + 20*X^31 + 66*X^30 + 22*X^29 + 57*X^28 + 41*X^27 + 59*X^26 + 18*X^25 + 58*X^24 + 64*X^23 +
      36*X^22 + 15*X^21 + 11*X^20 + 28*X^19 + 25*X^18 + 61*X^17 + 47*X^16 + 9*X^15 + 45*X^14 +
      18*X^13 + 35*X^12 + 6*X^11 + 24*X^10 + 2*X^9 + 59*X^8 + 19*X^7 + 35*X^6 + 62*X^5 + 25*X^4 +
      62*X^3 + 41*X^2 + 60*X + 19,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s288 : XPow fSeventeenA4 7449435299494340606758990391469373845899355874126229670228
    (48*X^33 + 5*X^32 + 16*X^31 + 36*X^30 + 26*X^29 + 25*X^28 + 9*X^27 + 3*X^26 + 61*X^25 + 2*X^24 +
      19*X^23 + 29*X^22 + 6*X^21 + 23*X^20 + 33*X^19 + 46*X^18 + 6*X^17 + 62*X^16 + 51*X^15 +
      24*X^14 + 50*X^13 + 22*X^12 + 42*X^11 + 12*X^10 + 11*X^9 + 36*X^8 + 40*X^7 + 17*X^6 + 36*X^5 +
      24*X^4 + 47*X^3 + 26*X^2 + 26*X + 15) :=
  sq_step (by norm_num) pSeventeenA4s287 ⟨
    21*X^32 + 49*X^31 + 56*X^30 + 34*X^29 + 21*X^28 + 22*X^27 + 43*X^26 + 58*X^25 + 7*X^24 + 15*X^23 +
      12*X^22 + 38*X^21 + 26*X^20 + 8*X^19 + 64*X^18 + 7*X^17 + 29*X^16 + 30*X^15 + 45*X^14 +
      46*X^13 + 39*X^12 + 10*X^11 + 48*X^10 + 61*X^9 + 16*X^8 + 41*X^7 + 46*X^5 + 51*X^4 + 5*X^3 +
      52*X^2 + 13*X + 7,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s289 : XPow fSeventeenA4 14898870598988681213517980782938747691798711748252459340456
    (34*X^33 + 58*X^32 + 13*X^31 + 27*X^30 + 2*X^29 + 41*X^28 + 6*X^27 + 59*X^26 + 48*X^25 + 45*X^24 +
      51*X^22 + 47*X^19 + 2*X^18 + 23*X^17 + 40*X^16 + 16*X^15 + 64*X^14 + 36*X^13 + 66*X^12 +
      60*X^11 + 5*X^10 + 60*X^9 + 9*X^8 + 12*X^7 + 42*X^6 + 52*X^5 + 45*X^4 + 37*X^3 + 10*X^2 + 14*X +
      56) :=
  sq_step (by norm_num) pSeventeenA4s288 ⟨
    26*X^32 + 36*X^31 + 64*X^30 + 52*X^29 + 35*X^28 + 16*X^27 + 19*X^26 + 13*X^25 + 18*X^24 + 11*X^23 +
      54*X^22 + 35*X^21 + 23*X^20 + 8*X^19 + 52*X^18 + 3*X^17 + 8*X^16 + 52*X^15 + 51*X^14 + 46*X^13 +
      33*X^12 + 59*X^11 + 56*X^10 + 21*X^9 + 5*X^8 + 9*X^7 + 43*X^6 + 5*X^5 + 32*X^4 + 22*X^3 +
      3*X^2 + 61*X + 2,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s290 : XPow fSeventeenA4 29797741197977362427035961565877495383597423496504918680912
    (19*X^33 + 58*X^32 + 56*X^31 + 18*X^30 + 33*X^29 + 41*X^28 + 9*X^27 + 21*X^26 + 12*X^25 + 23*X^24 +
      47*X^23 + 24*X^22 + 59*X^21 + 57*X^20 + 46*X^19 + 56*X^18 + 47*X^17 + 34*X^16 + 38*X^15 +
      59*X^14 + 49*X^13 + 21*X^12 + 48*X^11 + 28*X^10 + 54*X^9 + 58*X^8 + 19*X^7 + 30*X^6 + X^5 +
      29*X^4 + 60*X^3 + 25*X^2 + 65*X + 56) :=
  sq_step (by norm_num) pSeventeenA4s289 ⟨
    17*X^32 + 46*X^31 + 29*X^30 + 51*X^29 + 54*X^28 + 30*X^27 + 15*X^26 + 27*X^25 + 6*X^24 + 4*X^22 +
      63*X^21 + 37*X^20 + 49*X^19 + 4*X^18 + 38*X^17 + 58*X^16 + 62*X^15 + 54*X^14 + 4*X^13 +
      58*X^12 + 17*X^11 + 47*X^10 + 32*X^9 + 66*X^8 + 37*X^7 + 2*X^6 + 5*X^5 + 17*X^4 + 26*X^3 +
      61*X + 42,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s291 : XPow fSeventeenA4 29797741197977362427035961565877495383597423496504918680913
    (17*X^33 + 47*X^32 + 42*X^31 + 38*X^30 + 65*X^29 + 25*X^28 + 38*X^27 + 59*X^26 + 60*X^25 + 10*X^24 +
      31*X^23 + 33*X^21 + 15*X^20 + 10*X^19 + 52*X^18 + 60*X^17 + 13*X^16 + 13*X^15 + 33*X^14 +
      59*X^13 + 33*X^12 + 34*X^11 + 20*X^10 + 23*X^9 + 47*X^7 + 35*X^6 + 65*X^5 + 4*X^4 + 5*X^3 +
      9*X^2 + 56*X + 36) :=
  mul_step (by norm_num) pSeventeenA4s290 pSeventeenA41 ⟨
    19,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s292 : XPow fSeventeenA4 59595482395954724854071923131754990767194846993009837361826
    (33*X^33 + 2*X^32 + 13*X^31 + 17*X^30 + 61*X^29 + 13*X^28 + 35*X^27 + 6*X^26 + 35*X^25 + 39*X^24 +
      5*X^23 + 38*X^22 + 21*X^21 + 4*X^20 + 45*X^19 + X^18 + 32*X^17 + 36*X^16 + 16*X^15 + 19*X^14 +
      49*X^13 + 14*X^12 + 35*X^11 + 13*X^10 + 37*X^9 + 66*X^8 + 45*X^7 + 63*X^6 + 22*X^5 + 22*X^4 +
      53*X^3 + 53*X^2 + 28*X + 59) :=
  sq_step (by norm_num) pSeventeenA4s291 ⟨
    21*X^32 + 54*X^31 + 23*X^30 + 57*X^29 + 3*X^28 + 29*X^27 + 4*X^25 + 49*X^24 + 23*X^23 + 4*X^22 +
      34*X^21 + 23*X^20 + 8*X^19 + 66*X^18 + 15*X^17 + 8*X^16 + 62*X^15 + 45*X^14 + 61*X^13 +
      37*X^12 + 10*X^11 + 26*X^10 + 11*X^9 + 57*X^8 + 60*X^7 + 35*X^6 + 32*X^5 + 40*X^4 + 16*X^3 +
      9*X^2 + X + 19,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s293 : XPow fSeventeenA4 59595482395954724854071923131754990767194846993009837361827
    (26*X^33 + 15*X^32 + 34*X^31 + 45*X^30 + 30*X^29 + 24*X^28 + 32*X^27 + 32*X^26 + X^25 + 43*X^24 +
      29*X^23 + 49*X^22 + 54*X^21 + 37*X^20 + 41*X^19 + 16*X^18 + 60*X^17 + 29*X^16 + 59*X^15 +
      60*X^14 + 13*X^13 + 16*X^12 + 34*X^11 + 52*X^10 + 44*X^9 + 12*X^8 + 22*X^7 + 7*X^6 + 14*X^5 +
      58*X^4 + 50*X^3 + 33*X^2 + 59*X + 59) :=
  mul_step (by norm_num) pSeventeenA4s292 pSeventeenA41 ⟨
    33,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s294 : XPow fSeventeenA4 119190964791909449708143846263509981534389693986019674723654
    (5*X^33 + 6*X^32 + 16*X^31 + 6*X^30 + 9*X^29 + 12*X^28 + 15*X^27 + 19*X^26 + 40*X^24 + 59*X^23 +
      60*X^22 + 12*X^21 + 31*X^20 + 17*X^19 + 28*X^18 + 41*X^17 + 34*X^16 + 57*X^15 + 27*X^14 +
      10*X^13 + 38*X^12 + 26*X^11 + 19*X^10 + 25*X^9 + 33*X^8 + 52*X^7 + 30*X^6 + 60*X^5 + 4*X^4 +
      64*X^3 + 41*X^2 + 4*X + 52) :=
  sq_step (by norm_num) pSeventeenA4s293 ⟨
    6*X^32 + 23*X^31 + 61*X^30 + 2*X^29 + 54*X^28 + 61*X^27 + 50*X^26 + 57*X^25 + 65*X^24 + 23*X^23 +
      39*X^22 + 10*X^21 + 17*X^20 + 25*X^19 + 11*X^18 + 26*X^17 + 22*X^16 + 3*X^15 + 9*X^14 +
      59*X^13 + 34*X^12 + 16*X^11 + 28*X^10 + 47*X^9 + 17*X^8 + 44*X^7 + 59*X^6 + 50*X^5 + 44*X^4 +
      28*X^3 + 29*X^2 + 9*X + 16,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s295 : XPow fSeventeenA4 119190964791909449708143846263509981534389693986019674723655
    (34*X^33 + 63*X^32 + 37*X^31 + 35*X^30 + 43*X^29 + 58*X^28 + 27*X^27 + 30*X^26 + 18*X^25 + 14*X^24 +
      16*X^23 + 30*X^20 + 30*X^19 + 62*X^17 + 61*X^16 + 29*X^15 + 34*X^14 + 48*X^13 + 15*X^12 +
      10*X^11 + 9*X^10 + 52*X^9 + 47*X^8 + 38*X^7 + 9*X^6 + 17*X^5 + 14*X^4 + 4*X^3 + 21*X^2 + 52*X +
      13) :=
  mul_step (by norm_num) pSeventeenA4s294 pSeventeenA41 ⟨
    5,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s296 : XPow fSeventeenA4 238381929583818899416287692527019963068779387972039349447310
    (58*X^33 + 25*X^32 + 8*X^31 + 17*X^30 + 20*X^29 + 66*X^28 + 34*X^27 + 51*X^26 + 12*X^25 + 30*X^24 +
      27*X^23 + 53*X^22 + 51*X^21 + 56*X^20 + 34*X^19 + 5*X^18 + 12*X^17 + 56*X^16 + 10*X^15 +
      29*X^14 + 22*X^13 + 55*X^12 + 52*X^11 + 25*X^10 + 3*X^8 + 11*X^7 + 4*X^6 + 55*X^5 + 49*X^4 +
      23*X^3 + 7*X^2 + 21*X + 37) :=
  sq_step (by norm_num) pSeventeenA4s295 ⟨
    17*X^32 + 51*X^31 + 16*X^30 + 65*X^29 + 41*X^28 + 50*X^27 + 23*X^26 + 28*X^25 + 46*X^24 + 27*X^23 +
      66*X^22 + 24*X^21 + 43*X^20 + 13*X^19 + X^18 + 3*X^17 + 62*X^16 + 52*X^15 + 14*X^14 + 48*X^13 +
      62*X^12 + 37*X^11 + 18*X^10 + 25*X^9 + 40*X^8 + 29*X^7 + 29*X^6 + 12*X^5 + 32*X^4 + 32*X^3 +
      12*X^2 + 55*X + 42,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s297 : XPow fSeventeenA4 476763859167637798832575385054039926137558775944078698894620
    (40*X^33 + 28*X^32 + 4*X^31 + 45*X^30 + 46*X^29 + 52*X^28 + 3*X^27 + 56*X^26 + 66*X^25 + 64*X^24 +
      22*X^23 + X^22 + 11*X^21 + 36*X^20 + 44*X^19 + 13*X^18 + 43*X^17 + 7*X^16 + 29*X^15 + 22*X^14 +
      34*X^13 + 18*X^12 + 35*X^11 + 6*X^10 + 35*X^9 + 26*X^8 + 64*X^7 + 35*X^6 + 24*X^5 + 58*X^4 +
      47*X^3 + 15*X^2 + 37*X + 53) :=
  sq_step (by norm_num) pSeventeenA4s296 ⟨
    14*X^32 + 17*X^31 + 11*X^30 + 27*X^29 + 22*X^28 + 21*X^27 + 25*X^26 + 19*X^25 + 9*X^24 + 4*X^23 +
      6*X^22 + 5*X^21 + 39*X^19 + 44*X^18 + 11*X^17 + 9*X^16 + 56*X^15 + 12*X^14 + 24*X^13 + 30*X^12 +
      31*X^11 + 5*X^9 + 28*X^8 + 4*X^7 + 24*X^6 + 42*X^5 + 54*X^4 + 55*X^2 + 35*X + 35,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s298 : XPow fSeventeenA4 953527718335275597665150770108079852275117551888157397789240
    (19*X^33 + 39*X^32 + 27*X^31 + 18*X^30 + 30*X^29 + 17*X^28 + 42*X^27 + 32*X^26 + 39*X^25 + 40*X^24 +
      32*X^23 + 6*X^22 + 62*X^21 + 12*X^20 + 53*X^19 + 60*X^18 + 8*X^17 + 16*X^16 + 56*X^15 +
      16*X^14 + 11*X^13 + 63*X^12 + 65*X^11 + 27*X^10 + 37*X^9 + 50*X^8 + 19*X^7 + 6*X^6 + 30*X^5 +
      20*X^4 + 60*X^3 + 48*X^2 + 64*X + 6) :=
  sq_step (by norm_num) pSeventeenA4s297 ⟨
    59*X^32 + 11*X^31 + 5*X^30 + 60*X^29 + 6*X^28 + 54*X^27 + 30*X^26 + 37*X^25 + 34*X^24 + 26*X^23 +
      16*X^22 + 7*X^21 + 4*X^20 + 33*X^19 + 51*X^18 + 4*X^17 + 26*X^16 + 35*X^15 + 25*X^14 + 16*X^13 +
      28*X^12 + 33*X^11 + 35*X^10 + 8*X^9 + 12*X^8 + 43*X^6 + 57*X^5 + 35*X^4 + 63*X^3 + 42*X^2 +
      52*X + 30,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s299 : XPow fSeventeenA4 1907055436670551195330301540216159704550235103776314795578480
    (43*X^33 + 27*X^32 + 24*X^31 + 13*X^30 + 14*X^29 + 18*X^28 + 31*X^27 + 40*X^26 + 57*X^25 + 3*X^24 +
      63*X^23 + 53*X^22 + 27*X^21 + 16*X^20 + 53*X^19 + 62*X^18 + 58*X^16 + 36*X^15 + 46*X^14 +
      60*X^13 + 20*X^12 + 29*X^11 + 20*X^10 + 63*X^9 + 19*X^7 + X^6 + 7*X^5 + 63*X^4 + 34*X^3 +
      44*X^2 + 37*X + 39) :=
  sq_step (by norm_num) pSeventeenA4s298 ⟨
    26*X^32 + 33*X^31 + 55*X^30 + 5*X^29 + 44*X^28 + 61*X^27 + 55*X^26 + 42*X^25 + 48*X^24 + 5*X^23 +
      17*X^22 + 27*X^21 + 48*X^20 + 23*X^19 + 40*X^18 + 23*X^17 + 26*X^16 + 8*X^15 + 40*X^14 +
      7*X^13 + 63*X^12 + 47*X^11 + 9*X^10 + 9*X^9 + 65*X^8 + 3*X^7 + 27*X^6 + 4*X^5 + 52*X^4 +
      47*X^3 + 60*X^2 + 59*X + 63,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s300 : XPow fSeventeenA4 3814110873341102390660603080432319409100470207552629591156960
    (6*X^33 + 33*X^32 + 31*X^31 + 48*X^30 + 36*X^29 + 61*X^28 + 33*X^27 + 22*X^26 + 56*X^25 + 35*X^24 +
      51*X^23 + 62*X^22 + 47*X^21 + 63*X^20 + 19*X^19 + 6*X^18 + 62*X^17 + 35*X^16 + 41*X^15 +
      36*X^14 + 46*X^13 + 6*X^11 + 7*X^10 + 15*X^9 + 19*X^8 + 39*X^7 + 44*X^6 + 58*X^5 + 50*X^4 +
      30*X^3 + 11*X^2 + 60*X + 36) :=
  sq_step (by norm_num) pSeventeenA4s299 ⟨
    40*X^32 + 20*X^30 + 27*X^29 + 41*X^28 + 18*X^27 + 33*X^26 + 56*X^25 + 22*X^24 + 44*X^23 + 49*X^22 +
      33*X^21 + 38*X^20 + 23*X^19 + 47*X^18 + 59*X^17 + 6*X^16 + 50*X^15 + 27*X^14 + 34*X^13 +
      52*X^12 + 15*X^11 + 66*X^10 + 49*X^9 + 42*X^8 + 61*X^7 + 26*X^6 + 35*X^5 + 39*X^4 + 14*X^3 +
      42*X^2 + 16*X + 37,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s301 : XPow fSeventeenA4 7628221746682204781321206160864638818200940415105259182313920
    (7*X^33 + 6*X^32 + 33*X^31 + 2*X^30 + 66*X^29 + 60*X^28 + 30*X^27 + 9*X^26 + 47*X^25 + 66*X^24 +
      28*X^23 + 53*X^22 + 49*X^21 + 4*X^20 + 18*X^19 + 28*X^18 + 40*X^17 + 5*X^16 + 38*X^15 +
      29*X^14 + 28*X^13 + 22*X^12 + 5*X^11 + 44*X^10 + 3*X^9 + 62*X^8 + 29*X^7 + 28*X^6 + 11*X^5 +
      65*X^4 + 17*X^3 + 19*X^2 + 2*X + 33) :=
  sq_step (by norm_num) pSeventeenA4s300 ⟨
    36*X^32 + 8*X^31 + 62*X^30 + 65*X^29 + 63*X^28 + 59*X^27 + 4*X^26 + 26*X^25 + 44*X^24 + 34*X^23 +
      52*X^22 + 47*X^21 + 50*X^20 + 58*X^19 + 20*X^18 + X^17 + 13*X^16 + 5*X^15 + 61*X^14 + 5*X^13 +
      3*X^12 + 28*X^11 + 32*X^10 + 18*X^9 + 45*X^8 + 57*X^7 + 65*X^6 + 9*X^5 + 55*X^4 + 2*X^3 +
      38*X^2 + 40*X + 9,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s302 : XPow fSeventeenA4 15256443493364409562642412321729277636401880830210518364627840
    (30*X^33 + 63*X^32 + 53*X^31 + 58*X^30 + 43*X^29 + 55*X^28 + 31*X^27 + 20*X^26 + 24*X^25 + 61*X^24 +
      66*X^23 + 48*X^22 + 17*X^21 + 38*X^20 + 34*X^19 + 60*X^18 + 53*X^17 + 56*X^16 + 48*X^15 +
      3*X^14 + 55*X^13 + 20*X^12 + 50*X^11 + 64*X^10 + 4*X^9 + 45*X^8 + 65*X^7 + 66*X^6 + 58*X^5 +
      8*X^4 + 46*X^3 + 45*X^2 + 23*X + 22) :=
  sq_step (by norm_num) pSeventeenA4s301 ⟨
    49*X^32 + 10*X^31 + 23*X^30 + 26*X^29 + 49*X^28 + 61*X^27 + 18*X^26 + 60*X^25 + 64*X^24 + 63*X^23 +
      21*X^22 + 57*X^21 + 37*X^20 + 52*X^19 + 31*X^18 + 21*X^17 + 60*X^15 + 59*X^14 + 61*X^13 +
      40*X^12 + 32*X^11 + 12*X^10 + 59*X^9 + 10*X^8 + 31*X^7 + 31*X^6 + 51*X^5 + 27*X^4 + 66*X^3 +
      61*X^2 + 56*X + 38,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s303 : XPow fSeventeenA4 15256443493364409562642412321729277636401880830210518364627841
    (30*X^33 + 43*X^31 + 65*X^30 + 40*X^29 + 21*X^28 + X^27 + 3*X^26 + 63*X^25 + 64*X^24 + 52*X^23 +
      12*X^22 + 53*X^21 + 45*X^20 + 5*X^19 + 8*X^18 + 23*X^17 + 5*X^16 + 15*X^15 + 65*X^14 + 13*X^13 +
      51*X^12 + 10*X^11 + 42*X^10 + 25*X^9 + 35*X^8 + 47*X^7 + 20*X^6 + 19*X^5 + 14*X^4 + 24*X^3 +
      58*X^2 + 22*X + 11) :=
  mul_step (by norm_num) pSeventeenA4s302 pSeventeenA41 ⟨
    30,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s304 : XPow fSeventeenA4 30512886986728819125284824643458555272803761660421036729255682
    (3*X^33 + 11*X^31 + 40*X^30 + 4*X^29 + 49*X^28 + 47*X^27 + 7*X^26 + 13*X^25 + 60*X^24 + 32*X^23 +
      28*X^22 + 12*X^21 + 38*X^20 + 34*X^19 + 41*X^18 + 9*X^17 + 34*X^16 + 35*X^15 + 40*X^14 +
      8*X^13 + 52*X^12 + X^11 + 31*X^10 + 36*X^9 + 37*X^8 + 65*X^7 + 2*X^6 + 22*X^5 + 55*X^4 +
      56*X^3 + 46*X^2 + 29*X + 49) :=
  sq_step (by norm_num) pSeventeenA4s303 ⟨
    29*X^32 + 15*X^31 + 2*X^30 + 11*X^29 + 44*X^28 + 33*X^27 + 21*X^26 + 38*X^25 + 10*X^24 + 55*X^23 +
      16*X^22 + 49*X^21 + 17*X^20 + 57*X^19 + 3*X^18 + 2*X^17 + 14*X^16 + 37*X^15 + 10*X^14 +
      58*X^13 + 60*X^12 + 60*X^11 + 55*X^10 + 55*X^9 + 14*X^8 + 26*X^7 + 36*X^6 + 57*X^5 + 25*X^4 +
      9*X^3 + 45*X^2 + 26*X + 29,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s305 : XPow fSeventeenA4 61025773973457638250569649286917110545607523320842073458511364
    (66) :=
  sq_step (by norm_num) pSeventeenA4s304 ⟨
    9*X^32 + 37*X^31 + 63*X^30 + 45*X^29 + 46*X^28 + X^27 + 25*X^26 + 58*X^25 + 47*X^24 + 24*X^23 +
      35*X^22 + 36*X^21 + 33*X^20 + 20*X^19 + 61*X^18 + 63*X^17 + 39*X^16 + 60*X^15 + 47*X^14 +
      18*X^13 + 14*X^12 + 14*X^11 + 24*X^10 + 24*X^9 + 39*X^8 + 15*X^7 + 62*X^6 + 20*X^5 + 17*X^4 +
      49*X^3 + 44*X^2 + 15*X + 9,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s306 : XPow fSeventeenA4 122051547946915276501139298573834221091215046641684146917022728
    (1) :=
  sq_step (by norm_num) pSeventeenA4s305 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4s307 : XPow fSeventeenA4 122051547946915276501139298573834221091215046641684146917022729
    (X) :=
  mul_step (by norm_num) pSeventeenA4s306 pSeventeenA41 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! Factor 4 again, at the smaller exponent `67 ^ 2`, for the coprimality below. -/

theorem pSeventeenA4cs0 : XPow fSeventeenA4 2
    (X^2) :=
  sq_step (by norm_num) pSeventeenA41 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs1 : XPow fSeventeenA4 4
    (X^4) :=
  sq_step (by norm_num) pSeventeenA4cs0 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs2 : XPow fSeventeenA4 8
    (X^8) :=
  sq_step (by norm_num) pSeventeenA4cs1 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs3 : XPow fSeventeenA4 16
    (X^16) :=
  sq_step (by norm_num) pSeventeenA4cs2 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs4 : XPow fSeventeenA4 17
    (X^17) :=
  mul_step (by norm_num) pSeventeenA4cs3 pSeventeenA41 ⟨
    0,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs5 : XPow fSeventeenA4 34
    (19*X^33 + 63*X^32 + 33*X^31 + 32*X^30 + 33*X^29 + 22*X^28 + 15*X^27 + 6*X^26 + 9*X^25 + 58*X^24 +
      18*X^23 + 11*X^22 + 34*X^21 + 16*X^20 + 54*X^19 + 32*X^18 + 19*X^17 + 41*X^16 + 54*X^15 +
      45*X^14 + 2*X^13 + 38*X^12 + 25*X^11 + 37*X^10 + 44*X^9 + 66*X^8 + 15*X^7 + 30*X^6 + 16*X^5 +
      57*X^4 + 6*X^3 + 57*X^2 + 16) :=
  sq_step (by norm_num) pSeventeenA4cs4 ⟨
    1,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs6 : XPow fSeventeenA4 35
    (22*X^33 + 24*X^32 + 56*X^31 + 38*X^30 + 46*X^29 + 31*X^28 + 23*X^27 + 56*X^26 + 28*X^25 + 48*X^24 +
      18*X^23 + 42*X^22 + 59*X^21 + 23*X^20 + 53*X^19 + 24*X^18 + 29*X^16 + 66*X^15 + 53*X^14 +
      9*X^13 + 10*X^12 + 43*X^11 + 10*X^10 + 31*X^9 + 63*X^8 + 47*X^7 + 50*X^6 + 26*X^5 + 17*X^4 +
      37*X^3 + 11*X^2 + 16*X + 36) :=
  mul_step (by norm_num) pSeventeenA4cs5 pSeventeenA41 ⟨
    19,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs7 : XPow fSeventeenA4 70
    (32*X^33 + 40*X^31 + 30*X^30 + 59*X^29 + 63*X^28 + 6*X^27 + X^26 + 8*X^25 + 56*X^24 + 8*X^23 +
      36*X^22 + 41*X^21 + 47*X^20 + 6*X^19 + 11*X^18 + 29*X^17 + 25*X^16 + 32*X^15 + 50*X^14 +
      29*X^13 + 2*X^12 + 38*X^11 + 49*X^10 + 17*X^9 + 52*X^8 + 54*X^7 + 6*X^6 + 54*X^5 + 55*X^4 +
      21*X^3 + 34*X^2 + 31*X + 35) :=
  sq_step (by norm_num) pSeventeenA4cs6 ⟨
    15*X^32 + X^31 + 51*X^30 + 58*X^29 + 20*X^28 + 2*X^27 + 32*X^26 + 38*X^25 + 66*X^24 + 29*X^23 +
      65*X^22 + 57*X^21 + 51*X^20 + 60*X^19 + 51*X^18 + 18*X^17 + 4*X^16 + 57*X^15 + 29*X^14 +
      8*X^13 + 53*X^12 + 37*X^11 + 31*X^10 + 38*X^9 + 51*X^8 + 56*X^7 + 65*X^6 + 55*X^4 + 9*X^3 +
      2*X^2 + 43*X + 51,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs8 : XPow fSeventeenA4 140
    (42*X^33 + 10*X^32 + 14*X^31 + 42*X^30 + 24*X^29 + 48*X^28 + 20*X^27 + 27*X^26 + 30*X^25 + 31*X^24 +
      6*X^23 + 15*X^22 + 40*X^21 + 35*X^20 + 28*X^19 + 33*X^18 + 52*X^17 + 35*X^16 + 55*X^15 +
      26*X^14 + 25*X^13 + 47*X^12 + 55*X^11 + 32*X^10 + 18*X^9 + 5*X^8 + 34*X^7 + 65*X^6 + 39*X^5 +
      33*X^4 + 61*X^3 + 48*X^2 + 20*X + 56) :=
  sq_step (by norm_num) pSeventeenA4cs7 ⟨
    19*X^32 + 26*X^31 + 30*X^30 + 65*X^29 + 51*X^28 + 9*X^27 + 34*X^26 + 57*X^25 + 33*X^24 + 5*X^23 +
      X^22 + 34*X^21 + 54*X^20 + 36*X^19 + 38*X^18 + 42*X^17 + 20*X^16 + 41*X^15 + 11*X^14 + 5*X^13 +
      26*X^12 + 5*X^11 + 14*X^10 + 13*X^9 + 6*X^8 + 3*X^6 + X^5 + 46*X^4 + 34*X^3 + 16*X^2 + 8*X +
      40,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs9 : XPow fSeventeenA4 280
    (36*X^33 + 27*X^32 + 61*X^31 + 36*X^30 + 30*X^29 + 35*X^28 + 66*X^27 + 10*X^26 + 34*X^25 + 36*X^24 +
      50*X^23 + 48*X^22 + 44*X^21 + 40*X^20 + 24*X^19 + 3*X^18 + 27*X^17 + 21*X^16 + 8*X^15 +
      66*X^14 + 19*X^13 + 15*X^12 + 10*X^11 + 63*X^10 + 21*X^9 + 30*X^8 + 13*X^7 + 62*X^6 + 63*X^5 +
      31*X^4 + 9*X^3 + 57*X^2 + 56*X + 23) :=
  sq_step (by norm_num) pSeventeenA4cs8 ⟨
    22*X^32 + 52*X^31 + 32*X^30 + 43*X^29 + 64*X^28 + 61*X^27 + 36*X^26 + 24*X^25 + 25*X^24 + 34*X^23 +
      42*X^22 + 66*X^21 + 9*X^20 + 20*X^19 + 59*X^18 + 61*X^17 + X^16 + 32*X^15 + 63*X^14 + 11*X^13 +
      27*X^12 + 37*X^11 + 9*X^10 + 48*X^9 + 28*X^8 + 49*X^7 + 7*X^6 + 27*X^5 + 58*X^4 + 6*X^3 +
      2*X^2 + 31*X + 19,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs10 : XPow fSeventeenA4 560
    (9*X^33 + 65*X^32 + 43*X^31 + 55*X^30 + 61*X^29 + 17*X^28 + 58*X^27 + 43*X^26 + 24*X^25 + 3*X^24 +
      12*X^23 + 26*X^22 + 34*X^21 + 62*X^20 + 6*X^19 + 29*X^18 + 5*X^17 + 51*X^15 + 8*X^14 + 22*X^13 +
      41*X^12 + 52*X^11 + 24*X^10 + 2*X^9 + 46*X^8 + 21*X^7 + 66*X^6 + 53*X^5 + 20*X^4 + 37*X^3 +
      17*X^2 + 13*X + 36) :=
  sq_step (by norm_num) pSeventeenA4cs9 ⟨
    23*X^32 + 36*X^31 + 18*X^30 + 9*X^29 + 66*X^28 + 61*X^27 + 52*X^26 + 44*X^25 + 15*X^24 + 50*X^23 +
      45*X^22 + 3*X^21 + 8*X^20 + 13*X^19 + 20*X^18 + 27*X^17 + 45*X^16 + 3*X^15 + 64*X^14 + 46*X^13 +
      16*X^12 + 65*X^11 + X^10 + 36*X^9 + 26*X^8 + 6*X^7 + 7*X^6 + 53*X^5 + 42*X^4 + 50*X^3 + 59*X^2 +
      45*X + 32,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs11 : XPow fSeventeenA4 561
    (35*X^33 + 7*X^32 + 17*X^31 + 14*X^30 + 46*X^29 + 55*X^28 + 44*X^27 + 11*X^26 + 17*X^25 + 65*X^24 +
      54*X^23 + 66*X^22 + 33*X^21 + 16*X^20 + 46*X^19 + 25*X^18 + 37*X^17 + 18*X^16 + 25*X^15 +
      25*X^14 + 59*X^13 + 59*X^12 + 48*X^11 + 40*X^9 + 12*X^8 + 55*X^6 + 30*X^5 + 14*X^4 + 4*X^3 +
      57*X^2 + 36*X + 10) :=
  mul_step (by norm_num) pSeventeenA4cs10 pSeventeenA41 ⟨
    9,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs12 : XPow fSeventeenA4 1122
    (34*X^33 + 30*X^32 + 38*X^31 + 33*X^30 + 33*X^29 + 10*X^28 + 45*X^27 + 19*X^26 + 4*X^25 + X^24 +
      48*X^23 + 36*X^22 + 27*X^21 + 27*X^20 + 44*X^19 + 48*X^18 + 30*X^17 + 53*X^16 + 40*X^15 +
      12*X^14 + 3*X^13 + 42*X^12 + 11*X^11 + 13*X^10 + 55*X^9 + 29*X^8 + 10*X^7 + 13*X^6 + 44*X^5 +
      12*X^4 + 39*X^3 + 55*X^2 + 14*X + 10) :=
  sq_step (by norm_num) pSeventeenA4cs11 ⟨
    19*X^32 + 47*X^31 + 46*X^30 + 52*X^29 + 35*X^28 + 31*X^27 + 27*X^26 + 3*X^25 + 8*X^24 + 35*X^23 +
      60*X^22 + 61*X^21 + 59*X^20 + 55*X^19 + 56*X^18 + 4*X^17 + 47*X^16 + 47*X^15 + 36*X^14 +
      64*X^13 + 36*X^12 + 29*X^11 + 21*X^10 + 45*X^9 + 14*X^8 + 16*X^7 + 7*X^6 + 39*X^5 + 51*X^4 +
      40*X^3 + 56*X^2 + 48*X + 53,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs13 : XPow fSeventeenA4 2244
    (2*X^33 + 61*X^32 + 10*X^31 + 31*X^30 + 48*X^29 + 44*X^28 + 41*X^27 + 3*X^26 + 61*X^25 + 42*X^24 +
      24*X^23 + 32*X^22 + 6*X^21 + 42*X^20 + 32*X^19 + 43*X^18 + 48*X^17 + 33*X^16 + 10*X^15 +
      46*X^14 + 60*X^13 + 2*X^12 + 58*X^11 + 40*X^10 + 14*X^9 + 4*X^8 + 25*X^7 + 50*X^6 + 60*X^5 +
      48*X^4 + 62*X^3 + 50*X^2 + 15*X + 49) :=
  sq_step (by norm_num) pSeventeenA4cs12 ⟨
    17*X^32 + 18*X^31 + 6*X^30 + 35*X^29 + 10*X^28 + 54*X^27 + 39*X^26 + 39*X^25 + 6*X^24 + 24*X^23 +
      24*X^22 + 65*X^21 + 8*X^20 + 16*X^19 + 21*X^18 + 49*X^17 + 46*X^16 + 21*X^15 + 31*X^14 +
      7*X^13 + 20*X^11 + 4*X^10 + 51*X^9 + 9*X^8 + 37*X^7 + 29*X^6 + 62*X^5 + 30*X^4 + 57*X^3 +
      40*X^2 + 63*X + 1,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs14 : XPow fSeventeenA4 4488
    (63*X^33 + 31*X^32 + 50*X^31 + 45*X^30 + 41*X^29 + X^28 + 41*X^27 + 49*X^26 + 15*X^25 + 62*X^24 +
      12*X^23 + 28*X^22 + 37*X^21 + 45*X^20 + 2*X^19 + 63*X^18 + 63*X^17 + 24*X^16 + X^15 + 47*X^14 +
      64*X^13 + 54*X^12 + 54*X^11 + 22*X^10 + 39*X^9 + 42*X^8 + 53*X^7 + 48*X^6 + 65*X^5 + 12*X^4 +
      54*X^3 + 18*X^2 + 49*X + 61) :=
  sq_step (by norm_num) pSeventeenA4cs13 ⟨
    4*X^32 + 52*X^31 + 43*X^30 + 8*X^29 + 2*X^28 + 24*X^27 + 22*X^26 + 10*X^25 + 54*X^24 + 61*X^23 +
      41*X^22 + 57*X^21 + 18*X^20 + 31*X^19 + 44*X^17 + 38*X^16 + 11*X^15 + 18*X^14 + 46*X^13 +
      44*X^12 + 56*X^11 + 13*X^9 + 8*X^8 + 59*X^7 + 37*X^6 + 37*X^5 + 29*X^4 + 27*X^3 + 27*X^2 +
      41*X + 38,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pSeventeenA4cs15 : XPow fSeventeenA4 4489
    (22*X^33 + 66*X^32 + 47*X^31 + 47*X^30 + 3*X^29 + 20*X^28 + 56*X^27 + 58*X^26 + 26*X^25 + 48*X^24 +
      23*X^23 + 60*X^22 + 43*X^21 + 5*X^20 + 48*X^19 + 2*X^18 + 15*X^17 + 38*X^16 + 32*X^15 +
      18*X^14 + 46*X^13 + 36*X^12 + 56*X^11 + 25*X^10 + 57*X^8 + 55*X^7 + 12*X^6 + 15*X^5 + 27*X^4 +
      61*X^3 + 22*X^2 + 61*X + 3) :=
  mul_step (by norm_num) pSeventeenA4cs14 pSeventeenA41 ⟨
    63,
    by simp only [fSeventeenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

end Fermat.MazurNonCMCertificate

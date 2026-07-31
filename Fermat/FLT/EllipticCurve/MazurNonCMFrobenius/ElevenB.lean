/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius

/-!
# Row `p = 11`, `j = −24729001`: `H ∣ X ^ (23 ^ 11) - X`

The certificate is machine-checked twice outside Lean — PARI/GP 2.15.4 and an independent
Python reimplementation — and then re-derived here by the compiler, which is the only check
that counts.  Everything below is generated; see `MazurNonCMFrobenius.lean` for `XPow` and why
the exponents have to stay behind it.
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

/-- Irreducible factor 1 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenB1 : (ZMod 23)[X] :=
  X^11 + 7*X^9 + 20*X^8 + 17*X^7 + 4*X^6 + 21*X^5 + 4*X^4 + X^3 + 2*X^2 + 21*X + 20

/-- Irreducible factor 2 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenB2 : (ZMod 23)[X] :=
  X^11 + 7*X^10 + 19*X^9 + 20*X^8 + 8*X^7 + 11*X^6 + 6*X^5 + X^4 + 8*X^3 + 14*X^2 + 21*X + 2

/-- Irreducible factor 3 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenB3 : (ZMod 23)[X] :=
  X^11 + 13*X^10 + 3*X^9 + 20*X^8 + 20*X^7 + 17*X^6 + 3*X^5 + 5*X^4 + 14*X^3 + 21*X^2 + 21*X + 3

/-- Irreducible factor 4 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenB4 : (ZMod 23)[X] :=
  X^11 + 15*X^10 + 13*X^9 + 20*X^8 + X^7 + 19*X^6 + 2*X^5 + 14*X^4 + 16*X^3 + 8*X^2 + 21*X + 11

/-- Irreducible factor 5 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenB5 : (ZMod 23)[X] :=
  X^11 + 22*X^10 + 2*X^9 + 20*X^8 + 15*X^7 + 3*X^6 + 10*X^5 + 11*X^4 + 20*X^2 + 21*X + 16

/-- The factorisation of `H` used by every statement below. -/
theorem factor_hPolyElevenB : hPolyElevenB = fElevenB1 * fElevenB2 * fElevenB3 * fElevenB4 * fElevenB5 := by
  simp only [hPolyElevenB, fElevenB1, fElevenB2, fElevenB3, fElevenB4, fElevenB5]
  ring_nf
  reduce_mod_char

/-! ### Factor 1: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenB11 : XPow fElevenB1 1 X := xpow_one _

theorem pElevenB1s0 : XPow fElevenB1 2
    (X^2) :=
  sq_step (by norm_num) pElevenB11 ⟨
    0,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s1 : XPow fElevenB1 3
    (X^3) :=
  mul_step (by norm_num) pElevenB1s0 pElevenB11 ⟨
    0,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s2 : XPow fElevenB1 6
    (X^6) :=
  sq_step (by norm_num) pElevenB1s1 ⟨
    0,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s3 : XPow fElevenB1 12
    (16*X^10 + 3*X^9 + 6*X^8 + 19*X^7 + 2*X^6 + 19*X^5 + 22*X^4 + 21*X^3 + 2*X^2 + 3*X) :=
  sq_step (by norm_num) pElevenB1s2 ⟨
    X,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s4 : XPow fElevenB1 13
    (3*X^10 + 9*X^9 + 21*X^8 + 6*X^7 + X^6 + 8*X^5 + 3*X^4 + 9*X^3 + 17*X^2 + 9*X + 2) :=
  mul_step (by norm_num) pElevenB1s3 pElevenB11 ⟨
    16,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s5 : XPow fElevenB1 26
    (15*X^10 + 20*X^9 + 11*X^8 + X^7 + 10*X^6 + 19*X^5 + 13*X^4 + 6*X^3 + X^2 + 8*X + 3) :=
  sq_step (by norm_num) pElevenB1s4 ⟨
    9*X^9 + 8*X^8 + 6*X^7 + 17*X^6 + 16*X^5 + 22*X^4 + 17*X^3 + 17*X^2 + 19*X + 15,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s6 : XPow fElevenB1 27
    (20*X^10 + 21*X^9 + 8*X^7 + 5*X^6 + 20*X^5 + 15*X^4 + 9*X^3 + X^2 + 10*X + 22) :=
  mul_step (by norm_num) pElevenB1s5 pElevenB11 ⟨
    15,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s7 : XPow fElevenB1 54
    (17*X^10 + 9*X^9 + 19*X^8 + 12*X^7 + 13*X^6 + 8*X^5 + 8*X^4 + 21*X^3 + 15*X^2 + 10*X + 6) :=
  sq_step (by norm_num) pElevenB1s6 ⟨
    9*X^9 + 12*X^8 + 10*X^7 + 10*X^6 + 4*X^5 + 17*X^4 + 18*X^3 + 5*X^2 + 14*X + 17,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s8 : XPow fElevenB1 108
    (X^10 + 5*X^9 + 10*X^8 + 20*X^7 + 5*X^6 + 11*X^5 + 4*X^4 + 10*X^3 + 5*X^2 + 3) :=
  sq_step (by norm_num) pElevenB1s7 ⟨
    13*X^9 + 7*X^8 + 15*X^7 + 4*X^6 + X^5 + 3*X^4 + 20*X^3 + 2*X^2 + 21*X + 12,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s9 : XPow fElevenB1 216
    (15*X^10 + 10*X^9 + 7*X^8 + 18*X^7 + 10*X^5 + 9*X^4 + 8*X^3 + 4*X^2 + 11*X + 12) :=
  sq_step (by norm_num) pElevenB1s8 ⟨
    X^9 + 10*X^8 + 15*X^7 + 4*X^6 + 11*X^5 + 16*X^4 + 7*X^3 + 13*X^2 + 3*X + 1,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s10 : XPow fElevenB1 432
    (11*X^10 + 21*X^9 + 4*X^8 + 6*X^7 + 5*X^6 + 21*X^5 + 3*X^4 + 14*X^3 + 16*X^2 + 10*X + 11) :=
  sq_step (by norm_num) pElevenB1s9 ⟨
    18*X^9 + X^8 + 14*X^6 + 14*X^5 + 20*X^4 + 11*X^3 + 16*X^2 + 19*X + 17,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s11 : XPow fElevenB1 433
    (21*X^10 + 19*X^9 + 16*X^8 + 2*X^7 + 2*X^5 + 16*X^4 + 5*X^3 + 11*X^2 + 10*X + 10) :=
  mul_step (by norm_num) pElevenB1s10 pElevenB11 ⟨
    11,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s12 : XPow fElevenB1 866
    (22*X^10 + X^9 + 21*X^8 + 11*X^7 + 3*X^6 + 20*X^5 + 13*X^4 + 16*X^3 + 10*X^2 + 5*X + 9) :=
  sq_step (by norm_num) pElevenB1s11 ⟨
    4*X^9 + 16*X^8 + 16*X^7 + 17*X^6 + 16*X^5 + 19*X^4 + 18*X^3 + 14*X + 8,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s13 : XPow fElevenB1 1732
    (17*X^10 + 9*X^9 + 11*X^8 + 15*X^7 + 19*X^6 + 10*X^5 + 3*X^4 + 4*X^3 + 16*X^2 + 7*X + 1) :=
  sq_step (by norm_num) pElevenB1s12 ⟨
    X^9 + 21*X^8 + 21*X^7 + 14*X^6 + 11*X^5 + 9*X^4 + 17*X^3 + 11*X^2 + 8*X + 4,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s14 : XPow fElevenB1 1733
    (9*X^10 + 7*X^9 + 20*X^8 + 6*X^7 + 11*X^6 + 14*X^5 + 5*X^4 + 22*X^3 + 19*X^2 + 12*X + 5) :=
  mul_step (by norm_num) pElevenB1s13 pElevenB11 ⟨
    17,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s15 : XPow fElevenB1 3466
    (10*X^10 + 8*X^9 + 21*X^8 + 21*X^7 + 12*X^6 + 21*X^5 + 7*X^3 + 3*X^2 + 3*X + 21) :=
  sq_step (by norm_num) pElevenB1s14 ⟨
    12*X^9 + 11*X^8 + 3*X^7 + 2*X^6 + 7*X^5 + 15*X^4 + 4*X^3 + 13*X^2 + 13*X + 14,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s16 : XPow fElevenB1 6932
    (11*X^10 + 10*X^9 + 9*X^8 + 8*X^7 + 6*X^6 + 9*X^5 + 17*X^4 + 8*X^3 + 15*X^2 + 10*X + 3) :=
  sq_step (by norm_num) pElevenB1s15 ⟨
    8*X^9 + 22*X^8 + 14*X^7 + 5*X^6 + 21*X^5 + 14*X^4 + 11*X^3 + 5*X^2 + 5*X + 15,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s17 : XPow fElevenB1 13864
    (7*X^10 + 19*X^9 + 5*X^8 + 2*X^7 + 6*X^6 + 13*X^5 + 12*X^4 + 16*X^3 + 20*X + 3) :=
  sq_step (by norm_num) pElevenB1s16 ⟨
    6*X^9 + 13*X^8 + 3*X^7 + 7*X^6 + 13*X^5 + 16*X^4 + 13*X^3 + 20*X^2 + 11*X + 21,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s18 : XPow fElevenB1 13865
    (19*X^10 + 2*X^9 + 2*X^7 + 8*X^6 + 3*X^5 + 11*X^4 + 16*X^3 + 6*X^2 + 17*X + 21) :=
  mul_step (by norm_num) pElevenB1s17 pElevenB11 ⟨
    7,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s19 : XPow fElevenB1 27730
    (21*X^10 + 13*X^9 + 17*X^8 + 7*X^7 + 6*X^6 + 19*X^5 + 19*X^4 + 7*X^3 + 3*X^2 + 21*X) :=
  sq_step (by norm_num) pElevenB1s18 ⟨
    16*X^9 + 7*X^8 + 7*X^7 + 6*X^6 + 12*X^5 + 11*X^4 + 3*X^2 + 5*X + 14,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s20 : XPow fElevenB1 55460
    (17*X^10 + 10*X^9 + 20*X^8 + 22*X^7 + 21*X^6 + 6*X^5 + 4*X^4 + 3*X^3 + 9*X^2 + 13*X + 6) :=
  sq_step (by norm_num) pElevenB1s19 ⟨
    4*X^9 + 17*X^8 + 4*X^7 + 8*X^6 + 11*X^5 + 15*X^4 + 7*X^3 + X^2 + 3*X + 2,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s21 : XPow fElevenB1 110920
    (13*X^10 + 5*X^9 + 17*X^8 + 15*X^7 + 22*X^5 + 5*X^4 + 17*X^3 + 2*X^2 + 10*X + 20) :=
  sq_step (by norm_num) pElevenB1s20 ⟨
    13*X^9 + 18*X^8 + 22*X^7 + 3*X^6 + 14*X^5 + 18*X^4 + 13*X^3 + 3*X^2 + 6*X + 10,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s22 : XPow fElevenB1 110921
    (5*X^10 + 18*X^9 + 8*X^8 + 9*X^7 + 16*X^6 + 8*X^5 + 11*X^4 + 12*X^3 + 7*X^2 + 16) :=
  mul_step (by norm_num) pElevenB1s21 pElevenB11 ⟨
    13,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s23 : XPow fElevenB1 221842
    (22*X^10 + 10*X^9 + 17*X^8 + 11*X^7 + 7*X^5 + 3*X^4 + 5*X^3 + X + 10) :=
  sq_step (by norm_num) pElevenB1s22 ⟨
    2*X^9 + 19*X^8 + 22*X^7 + 21*X^6 + 3*X^5 + 20*X^4 + 9*X^3 + 18*X^2 + 9*X + 10,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s24 : XPow fElevenB1 221843
    (10*X^10 + X^9 + 8*X^8 + 17*X^7 + 11*X^6 + X^5 + 9*X^4 + X^3 + 3*X^2 + 8*X + 20) :=
  mul_step (by norm_num) pElevenB1s23 pElevenB11 ⟨
    22,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s25 : XPow fElevenB1 443686
    (7*X^10 + 10*X^9 + 14*X^8 + 6*X^6 + 3*X^4 + 8*X^2 + 13) :=
  sq_step (by norm_num) pElevenB1s24 ⟨
    8*X^9 + 20*X^8 + 13*X^7 + 10*X^6 + 13*X^5 + 3*X^4 + 2*X^3 + 2*X^2 + 10*X + 9,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s26 : XPow fElevenB1 887372
    (10*X^8 + 2*X^7 + 4*X^6 + 6*X^5 + 12*X^4 + X^3 + 3*X^2 + 21*X + 5) :=
  sq_step (by norm_num) pElevenB1s25 ⟨
    3*X^9 + 2*X^8 + 22*X^7 + 22*X^6 + 12*X^5 + 9*X^4 + 22,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s27 : XPow fElevenB1 887373
    (10*X^9 + 2*X^8 + 4*X^7 + 6*X^6 + 12*X^5 + X^4 + 3*X^3 + 21*X^2 + 5*X) :=
  mul_step (by norm_num) pElevenB1s26 pElevenB11 ⟨
    0,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s28 : XPow fElevenB1 1774746
    (19*X^10 + 22*X^8 + 13*X^6 + 18*X^5 + 14*X^4 + 17*X^3 + 14*X^2 + 8*X + 1) :=
  sq_step (by norm_num) pElevenB1s27 ⟨
    8*X^7 + 17*X^6 + 5*X^5 + 18*X^4 + 22*X^3 + 6*X^2 + 5*X + 8,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s29 : XPow fElevenB1 3549492
    (17*X^10 + 20*X^9 + 2*X^8 + X^7 + 9*X^6 + 18*X^5 + 17*X^4 + 4*X^3 + 11*X^2 + 22*X + 10) :=
  sq_step (by norm_num) pElevenB1s28 ⟨
    16*X^9 + 11*X^7 + 2*X^6 + 8*X^5 + 18*X^4 + 2*X^3 + 21*X^2 + 3,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s30 : XPow fElevenB1 7098984
    (2*X^10 + 8*X^9 + 15*X^8 + 8*X^7 + 11*X^6 + X^5 + 3*X^4 + 10*X^3 + 18*X^2 + 20*X + 19) :=
  sq_step (by norm_num) pElevenB1s29 ⟨
    13*X^9 + 13*X^8 + 9*X^7 + 16*X^6 + 13*X^5 + 20*X^4 + 9*X^3 + 11*X^2 + 16*X + 19,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s31 : XPow fElevenB1 7098985
    (8*X^10 + X^9 + 14*X^8 + 16*X^6 + 7*X^5 + 2*X^4 + 16*X^3 + 16*X^2 + 6) :=
  mul_step (by norm_num) pElevenB1s30 pElevenB11 ⟨
    2,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s32 : XPow fElevenB1 14197970
    (7*X^10 + 12*X^9 + 4*X^8 + 7*X^7 + 11*X^6 + 20*X^4 + 19*X^3 + 11*X + 4) :=
  sq_step (by norm_num) pElevenB1s31 ⟨
    18*X^9 + 16*X^8 + 7*X^7 + 16*X^6 + 7*X^5 + 8*X^4 + X^3 + 12*X^2 + 21*X + 20,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s33 : XPow fElevenB1 14197971
    (12*X^10 + X^9 + 5*X^8 + 7*X^7 + 18*X^6 + 11*X^5 + 14*X^4 + 16*X^3 + 20*X^2 + 18*X + 21) :=
  mul_step (by norm_num) pElevenB1s32 pElevenB11 ⟨
    7,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s34 : XPow fElevenB1 28395942
    (X^10 + 20*X^9 + 22*X^8 + 11*X^7 + 13*X^6 + 10*X^5 + 14*X^4 + 3*X^3 + 18*X^2 + 21*X + 6) :=
  sq_step (by norm_num) pElevenB1s33 ⟨
    6*X^9 + X^8 + 10*X^7 + 5*X^6 + 3*X^5 + 2*X^4 + 5*X^3 + X^2 + 5*X + 16,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s35 : XPow fElevenB1 28395943
    (20*X^10 + 15*X^9 + 14*X^8 + 19*X^7 + 6*X^6 + 16*X^5 + 22*X^4 + 17*X^3 + 19*X^2 + 8*X + 3) :=
  mul_step (by norm_num) pElevenB1s34 pElevenB11 ⟨
    1,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s36 : XPow fElevenB1 56791886
    (11*X^10 + 17*X^9 + 18*X^8 + 8*X^7 + 10*X^6 + 2*X^5 + 11*X^4 + 14*X^3 + 8*X^2 + 16*X + 9) :=
  sq_step (by norm_num) pElevenB1s35 ⟨
    9*X^9 + 2*X^8 + 9*X^7 + 20*X^6 + 14*X^5 + 19*X^4 + 6*X^3 + 22*X^2 + 20*X,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s37 : XPow fElevenB1 56791887
    (17*X^10 + 10*X^9 + 18*X^8 + 7*X^7 + 4*X^6 + 10*X^5 + 16*X^4 + 20*X^3 + 17*X^2 + 8*X + 10) :=
  mul_step (by norm_num) pElevenB1s36 pElevenB11 ⟨
    11,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s38 : XPow fElevenB1 113583774
    (X^10 + 13*X^9 + 8*X^8 + 9*X^7 + 13*X^6 + 6*X^5 + 12*X^4 + 22*X^2 + 3*X + 16) :=
  sq_step (by norm_num) pElevenB1s37 ⟨
    13*X^9 + 18*X^8 + 5*X^6 + 19*X^5 + 3*X^4 + 14*X^3 + 17*X^2 + 20*X + 18,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s39 : XPow fElevenB1 227167548
    (7*X^10 + 20*X^9 + 18*X^8 + 7*X^7 + 15*X^6 + 10*X^5 + 18*X^4 + 19*X^3 + 15*X^2 + 21*X + 2) :=
  sq_step (by norm_num) pElevenB1s38 ⟨
    X^9 + 3*X^8 + 17*X^7 + X^6 + 13*X^5 + 13*X^3 + 11*X + 15,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s40 : XPow fElevenB1 454335096
    (8*X^10 + 13*X^9 + X^8 + 14*X^7 + 15*X^6 + 21*X^5 + 9*X^3 + 8*X^2 + 11*X + 12) :=
  sq_step (by norm_num) pElevenB1s39 ⟨
    3*X^9 + 4*X^8 + 10*X^7 + 17*X^6 + 15*X^5 + 18*X^4 + 18*X^3 + 15*X^2 + 2*X + 18,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s41 : XPow fElevenB1 454335097
    (13*X^10 + 14*X^9 + 15*X^8 + 17*X^7 + 12*X^6 + 16*X^5 + 18*X^2 + 5*X + 1) :=
  mul_step (by norm_num) pElevenB1s40 pElevenB11 ⟨
    8,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s42 : XPow fElevenB1 908670194
    (13*X^10 + 12*X^9 + 13*X^8 + 12*X^7 + 9*X^6 + 19*X^5 + 10*X^4 + 6*X^2 + 5*X + 2) :=
  sq_step (by norm_num) pElevenB1s41 ⟨
    8*X^9 + 19*X^8 + X^7 + 17*X^6 + 7*X^5 + 9*X^4 + 10*X^3 + 7*X^2 + 16*X + 8,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s43 : XPow fElevenB1 1817340388
    (10*X^10 + 16*X^9 + 15*X^8 + 9*X^7 + 7*X^6 + 17*X^5 + 22*X^4 + 5*X^2 + 16*X + 13) :=
  sq_step (by norm_num) pElevenB1s42 ⟨
    8*X^9 + 13*X^8 + 12*X^7 + 5*X^6 + 4*X^5 + 11*X^4 + 13*X^3 + 10*X^2 + 12*X + 3,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s44 : XPow fElevenB1 1817340389
    (16*X^10 + 14*X^9 + 16*X^8 + 21*X^7 + 19*X^5 + 6*X^4 + 18*X^3 + 19*X^2 + 10*X + 7) :=
  mul_step (by norm_num) pElevenB1s43 pElevenB11 ⟨
    10,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s45 : XPow fElevenB1 3634680778
    (6*X^10 + 20*X^9 + 4*X^8 + 16*X^7 + 20*X^6 + 6*X^5 + 8*X^4 + 16*X^3 + 18*X^2 + 4*X + 1) :=
  sq_step (by norm_num) pElevenB1s44 ⟨
    3*X^9 + 11*X^8 + 20*X^7 + 17*X^6 + 19*X^5 + 10*X^4 + 15*X^3 + 14*X^2 + 19*X + 7,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s46 : XPow fElevenB1 7269361556
    (21*X^10 + 17*X^9 + 11*X^8 + 11*X^7 + 19*X^6 + 7*X^4 + 12*X^3 + 16*X^2 + 6*X + 19) :=
  sq_step (by norm_num) pElevenB1s45 ⟨
    13*X^9 + 10*X^8 + 12*X^7 + 22*X^6 + 16*X^4 + 2*X^3 + 13*X^2 + 3*X + 6,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s47 : XPow fElevenB1 14538723112
    (5*X^10 + 17*X^9 + 5*X^8 + 20*X^7 + 17*X^5 + 14*X^3 + X^2 + 15*X + 8) :=
  sq_step (by norm_num) pElevenB1s46 ⟨
    4*X^9 + X^8 + 10*X^7 + 13*X^6 + 8*X^5 + 12*X^4 + 6*X^3 + 20*X^2 + 10*X + 5,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s48 : XPow fElevenB1 29077446224
    (15*X^10 + 7*X^9 + 2*X^8 + 6*X^7 + 3*X^6 + 16*X^5 + 2*X^4 + 4*X^3 + 7*X^2 + 9*X + 1) :=
  sq_step (by norm_num) pElevenB1s47 ⟨
    2*X^9 + 9*X^8 + 3*X^7 + 14*X^6 + 10*X^5 + 5*X^4 + 16*X^3 + 19*X^2 + 6*X + 2,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s49 : XPow fElevenB1 29077446225
    (7*X^10 + 12*X^9 + 5*X^8 + X^7 + 2*X^6 + 9*X^5 + 13*X^4 + 15*X^3 + 2*X^2 + 8*X + 22) :=
  mul_step (by norm_num) pElevenB1s48 pElevenB11 ⟨
    15,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s50 : XPow fElevenB1 58154892450
    (8*X^10 + 9*X^9 + 20*X^8 + 22*X^7 + 2*X^6 + 19*X^5 + 22*X^4 + 2*X^3 + 11*X^2 + 12*X + 15) :=
  sq_step (by norm_num) pElevenB1s49 ⟨
    3*X^9 + 7*X^8 + 9*X^7 + 2*X^6 + 7*X^5 + 20*X^4 + 17*X^3 + 15*X^2 + 19*X + 20,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s51 : XPow fElevenB1 116309784900
    (22*X^10 + 15*X^9 + 15*X^8 + 11*X^7 + 19*X^5 + 5*X^4 + 11*X^3 + 12*X^2 + 21*X + 12) :=
  sq_step (by norm_num) pElevenB1s50 ⟨
    18*X^9 + 6*X^8 + 22*X^7 + 11*X^6 + 18*X^5 + 21*X^3 + 6*X^2 + 11*X + 21,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s52 : XPow fElevenB1 116309784901
    (15*X^10 + 22*X^9 + 8*X^8 + 17*X^7 + 3*X^5 + 15*X^4 + 13*X^3 + 10*X + 20) :=
  mul_step (by norm_num) pElevenB1s51 pElevenB11 ⟨
    22,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s53 : XPow fElevenB1 232619569802
    (11*X^10 + X^9 + 13*X^8 + 20*X^7 + 11*X^6 + 16*X^5 + 14*X^4 + 13*X^3 + 19*X^2 + 18*X + 15) :=
  sq_step (by norm_num) pElevenB1s52 ⟨
    18*X^9 + 16*X^8 + 22*X^6 + 2*X^5 + 2*X^4 + 21*X^3 + 9*X^2 + 17*X + 2,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s54 : XPow fElevenB1 232619569803
    (X^10 + 5*X^9 + 7*X^8 + 8*X^7 + 18*X^6 + 13*X^5 + 15*X^4 + 8*X^3 + 19*X^2 + 14*X + 10) :=
  mul_step (by norm_num) pElevenB1s53 pElevenB11 ⟨
    11,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s55 : XPow fElevenB1 465239139606
    (20*X^10 + 16*X^9 + 13*X^6 + 8*X^5 + 20*X^4 + 3*X^3 + 11*X^2 + X + 8) :=
  sq_step (by norm_num) pElevenB1s54 ⟨
    X^9 + 10*X^8 + 9*X^7 + 19*X^6 + 15*X^4 + 20*X^3 + 4*X^2 + 22*X,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s56 : XPow fElevenB1 930478279212
    (5*X^10 + 7*X^9 + 4*X^8 + 18*X^7 + 9*X^6 + 11*X^5 + 3*X^4 + 2*X^3 + 10*X^2 + 5*X + 5) :=
  sq_step (by norm_num) pElevenB1s55 ⟨
    9*X^9 + 19*X^8 + 9*X^7 + 9*X^6 + 16*X^5 + 19*X^4 + X^3 + 5*X^2 + 12*X + 11,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s57 : XPow fElevenB1 1860956558424
    (4*X^10 + 17*X^9 + 12*X^8 + 19*X^7 + 19*X^6 + 8*X^5 + 21*X^4 + 18*X^3 + 7*X^2 + 13*X + 7) :=
  sq_step (by norm_num) pElevenB1s56 ⟨
    2*X^9 + X^8 + 6*X^7 + 5*X^6 + 9*X^5 + 16*X^4 + 16*X^3 + 21*X^2 + 7*X + 17,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s58 : XPow fElevenB1 1860956558425
    (17*X^10 + 7*X^9 + 8*X^8 + 20*X^7 + 15*X^6 + 6*X^5 + 2*X^4 + 3*X^3 + 5*X^2 + 15*X + 12) :=
  mul_step (by norm_num) pElevenB1s57 pElevenB11 ⟨
    4,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s59 : XPow fElevenB1 3721913116850
    (13*X^10 + 15*X^9 + 13*X^8 + X^7 + 9*X^6 + 4*X^4 + 10*X^3 + 8*X^2 + 11*X + 16) :=
  sq_step (by norm_num) pElevenB1s58 ⟨
    13*X^9 + 8*X^8 + 16*X^6 + 13*X^5 + 20*X^4 + 7*X^3 + 3*X^2 + 22*X + 11,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s60 : XPow fElevenB1 3721913116851
    (15*X^10 + 14*X^9 + 17*X^8 + 18*X^7 + 17*X^6 + 7*X^5 + 4*X^4 + 18*X^3 + 8*X^2 + 19*X + 16) :=
  mul_step (by norm_num) pElevenB1s59 pElevenB11 ⟨
    13,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s61 : XPow fElevenB1 7443826233702
    (10*X^10 + 8*X^9 + 3*X^8 + 4*X^7 + 16*X^6 + 12*X^5 + 3*X^4 + 18*X^3 + 16*X^2 + 3*X + 20) :=
  sq_step (by norm_num) pElevenB1s60 ⟨
    18*X^9 + 6*X^8 + 5*X^7 + 16*X^6 + 14*X^5 + 15*X^4 + 14*X^3 + 6*X^2 + 22*X + 21,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s62 : XPow fElevenB1 14887652467404
    (22*X^10 + 8*X^9 + 15*X^8 + 5*X^7 + 11*X^6 + 14*X^5 + 13*X^3 + 7*X^2 + 2*X + 11) :=
  sq_step (by norm_num) pElevenB1s61 ⟨
    8*X^9 + 22*X^8 + 22*X^7 + 21*X^6 + 8*X^5 + 10*X^4 + 17*X^3 + 14*X^2 + 19*X + 16,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s63 : XPow fElevenB1 14887652467405
    (8*X^10 + 22*X^9 + 2*X^8 + 5*X^7 + 18*X^6 + 21*X^5 + 17*X^4 + 8*X^3 + 4*X^2 + 9*X + 20) :=
  mul_step (by norm_num) pElevenB1s62 pElevenB11 ⟨
    22,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s64 : XPow fElevenB1 29775304934810
    (21*X^10 + 21*X^8 + 4*X^7 + 16*X^6 + 6*X^5 + 13*X^3 + 18*X^2 + 19*X + 22) :=
  sq_step (by norm_num) pElevenB1s63 ⟨
    18*X^9 + 7*X^8 + 22*X^7 + 12*X^6 + 4*X^5 + 19*X^4 + 15*X^3 + 2*X^2 + X + 12,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s65 : XPow fElevenB1 59550609869620
    (14*X^10 + 18*X^9 + X^8 + 22*X^7 + 20*X^6 + 7*X^5 + 21*X^4 + 8*X^3 + 15*X^2 + X + 3) :=
  sq_step (by norm_num) pElevenB1s64 ⟨
    4*X^9 + 3*X^7 + 19*X^6 + 12*X^5 + 4*X^4 + 20*X^3 + 8*X^2 + 10*X + 16,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s66 : XPow fElevenB1 119101219739240
    (10*X^10 + 7*X^9 + 5*X^8 + 17*X^7 + 19*X^6 + 21*X^5 + 11*X^3 + 15*X^2 + 7*X + 19) :=
  sq_step (by norm_num) pElevenB1s65 ⟨
    12*X^9 + 21*X^8 + 15*X^7 + 12*X^6 + 3*X^5 + 10*X^4 + 6*X^3 + 2*X^2 + 16*X + 11,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s67 : XPow fElevenB1 238202439478480
    (6*X^10 + 18*X^9 + 3*X^8 + 7*X^7 + 4*X^6 + 16*X^5 + 3*X^4 + 2*X^3 + 18*X^2 + 18*X) :=
  sq_step (by norm_num) pElevenB1s66 ⟨
    8*X^9 + 2*X^8 + X^7 + 6*X^6 + 15*X^4 + 9*X^2 + 18*X + 10,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s68 : XPow fElevenB1 238202439478481
    (18*X^10 + 7*X^9 + 2*X^8 + 17*X^7 + 15*X^6 + 15*X^5 + X^4 + 12*X^3 + 6*X^2 + 12*X + 18) :=
  mul_step (by norm_num) pElevenB1s67 pElevenB11 ⟨
    6,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s69 : XPow fElevenB1 476404878956962
    (8*X^10 + 10*X^8 + 22*X^7 + 21*X^6 + 9*X^5 + 7*X^4 + 9*X^3 + 8*X^2 + 16*X + 7) :=
  sq_step (by norm_num) pElevenB1s68 ⟨
    2*X^9 + 22*X^8 + 15*X^7 + 9*X^6 + 19*X^5 + 4*X^4 + 12*X^3 + 17*X^2 + 11*X + 17,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s70 : XPow fElevenB1 476404878956963
    (1) :=
  mul_step (by norm_num) pElevenB1s69 pElevenB11 ⟨
    8,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s71 : XPow fElevenB1 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenB1s70 ⟨
    0,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB1s72 : XPow fElevenB1 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenB1s71 pElevenB11 ⟨
    0,
    by simp only [fElevenB1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 2: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenB21 : XPow fElevenB2 1 X := xpow_one _

theorem pElevenB2s0 : XPow fElevenB2 2
    (X^2) :=
  sq_step (by norm_num) pElevenB21 ⟨
    0,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s1 : XPow fElevenB2 3
    (X^3) :=
  mul_step (by norm_num) pElevenB2s0 pElevenB21 ⟨
    0,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s2 : XPow fElevenB2 6
    (X^6) :=
  sq_step (by norm_num) pElevenB2s1 ⟨
    0,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s3 : XPow fElevenB2 12
    (7*X^10 + 21*X^9 + 17*X^8 + 22*X^7 + 2*X^6 + 18*X^5 + 22*X^4 + 19*X^3 + 8*X^2 + 7*X + 14) :=
  sq_step (by norm_num) pElevenB2s2 ⟨
    X + 16,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s4 : XPow fElevenB2 13
    (18*X^10 + 22*X^9 + 20*X^8 + 15*X^7 + 10*X^6 + 3*X^5 + 12*X^4 + 21*X^3 + X^2 + 5*X + 9) :=
  mul_step (by norm_num) pElevenB2s3 pElevenB21 ⟨
    7,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s5 : XPow fElevenB2 26
    (6*X^10 + 7*X^9 + 3*X^8 + 14*X^7 + 5*X^6 + 21*X^5 + 14*X^4 + 7*X^3 + 4*X^2 + 4*X + 5) :=
  sq_step (by norm_num) pElevenB2s4 ⟨
    2*X^9 + 19*X^8 + 21*X^7 + 21*X^6 + 18*X^5 + 6*X^4 + 19*X^3 + 7*X^2 + 12*X + 15,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s6 : XPow fElevenB2 27
    (11*X^10 + 4*X^9 + 9*X^8 + 3*X^7 + X^6 + X^5 + X^4 + 2*X^3 + 12*X^2 + 17*X + 11) :=
  mul_step (by norm_num) pElevenB2s5 pElevenB21 ⟨
    6,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s7 : XPow fElevenB2 54
    (22*X^9 + 22*X^8 + X^7 + 15*X^6 + 2*X^5 + 22*X^4 + 8*X^3 + 14*X^2 + 16*X + 12) :=
  sq_step (by norm_num) pElevenB2s6 ⟨
    6*X^9 + 8*X^7 + 8*X^6 + 9*X^5 + 11*X^4 + 9*X^3 + 18*X^2 + 15*X + 20,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s8 : XPow fElevenB2 108
    (4*X^10 + 17*X^9 + 10*X^8 + 6*X^7 + 2*X^5 + 12*X^4 + 12*X^3 + 9*X^2 + 15*X + 11) :=
  sq_step (by norm_num) pElevenB2s7 ⟨
    X^7 + 18*X^6 + 15*X^5 + 7*X^4 + X^3 + 8*X^2 + 21*X + 9,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s9 : XPow fElevenB2 216
    (9*X^10 + 14*X^9 + X^8 + 2*X^7 + 22*X^6 + 4*X^4 + 13*X^3 + 6*X^2 + 7*X + 14) :=
  sq_step (by norm_num) pElevenB2s8 ⟨
    16*X^9 + X^8 + 12*X^7 + 11*X^6 + 12*X^5 + 17*X^4 + 5*X^3 + 3*X^2 + 8*X + 19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s10 : XPow fElevenB2 432
    (22*X^10 + 12*X^9 + 21*X^8 + 12*X^7 + 12*X^6 + 2*X^5 + X^4 + 19*X^3 + 19*X^2 + 6) :=
  sq_step (by norm_num) pElevenB2s9 ⟨
    12*X^9 + 7*X^8 + 6*X^7 + 17*X^6 + 7*X^5 + 9*X^4 + 8*X^3 + 18*X^2 + 9*X + 3,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s11 : XPow fElevenB2 433
    (19*X^10 + 17*X^9 + 9*X^8 + 20*X^7 + 13*X^6 + 7*X^5 + 20*X^4 + 4*X^3 + 14*X^2 + 4*X + 2) :=
  mul_step (by norm_num) pElevenB2s10 pElevenB21 ⟨
    22,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s12 : XPow fElevenB2 866
    (2*X^10 + 11*X^9 + 20*X^8 + 5*X^7 + 22*X^6 + 4*X^5 + 15*X^4 + X^3 + 13*X^2 + 5*X + 18) :=
  sq_step (by norm_num) pElevenB2s11 ⟨
    16*X^9 + 5*X^8 + 16*X^7 + 10*X^6 + 9*X^5 + 3*X^4 + 18*X^3 + 8*X^2 + 10*X + 16,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s13 : XPow fElevenB2 1732
    (15*X^10 + 13*X^9 + 16*X^8 + 5*X^7 + 16*X^6 + 5*X^5 + 18*X^4 + 2*X^3 + 12*X^2 + 20*X + 15) :=
  sq_step (by norm_num) pElevenB2s12 ⟨
    4*X^9 + 16*X^8 + 13*X^7 + 8*X^6 + 12*X^5 + 9*X^4 + 22*X^3 + 3*X^2 + 16*X + 5,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s14 : XPow fElevenB2 1733
    (7*X^9 + 4*X^8 + 11*X^7 + X^6 + 20*X^5 + 10*X^4 + 7*X^3 + 17*X^2 + 22*X + 16) :=
  mul_step (by norm_num) pElevenB2s13 pElevenB21 ⟨
    15,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s15 : XPow fElevenB2 3466
    (19*X^10 + 6*X^9 + 5*X^8 + 10*X^7 + 4*X^6 + 4*X^5 + 8*X^4 + 4*X^3 + 12*X^2 + 22*X + 14) :=
  sq_step (by norm_num) pElevenB2s14 ⟨
    3*X^7 + 12*X^6 + 6*X^5 + 2*X^4 + 17*X^3 + 8*X^2 + 2*X + 6,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s16 : XPow fElevenB2 6932
    (9*X^10 + 7*X^8 + 22*X^7 + 7*X^6 + 21*X^5 + 20*X^4 + 2*X^3 + 17*X^2 + 22) :=
  sq_step (by norm_num) pElevenB2s15 ⟨
    16*X^9 + X^8 + 7*X^7 + 6*X^6 + 20*X^5 + 21*X^4 + 4*X^3 + 15*X^2 + 4*X + 18,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s17 : XPow fElevenB2 13864
    (2*X^10 + 11*X^9 + 14*X^8 + 17*X^7 + 11*X^6 + 2*X^5 + 13*X^4 + 5*X^3 + 5*X^2 + 13*X) :=
  sq_step (by norm_num) pElevenB2s16 ⟨
    12*X^9 + 8*X^8 + 3*X^7 + 6*X^6 + 4*X^5 + 12*X^4 + 18*X^3 + 17*X^2 + 17*X + 12,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s18 : XPow fElevenB2 13865
    (20*X^10 + 22*X^9 + 18*X^7 + 3*X^6 + X^5 + 3*X^4 + 12*X^3 + 8*X^2 + 4*X + 19) :=
  mul_step (by norm_num) pElevenB2s17 pElevenB21 ⟨
    2,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s19 : XPow fElevenB2 27730
    (20*X^10 + 3*X^9 + 18*X^8 + 12*X^7 + 14*X^6 + 10*X^5 + 20*X^4 + 6*X^3 + 6*X^2 + 15*X + 6) :=
  sq_step (by norm_num) pElevenB2s18 ⟨
    9*X^9 + 12*X^8 + 22*X^7 + 20*X^6 + 19*X^5 + 13*X^4 + 10*X^3 + 16*X + 5,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s20 : XPow fElevenB2 55460
    (3*X^10 + 21*X^9 + 19*X^8 + 21*X^7 + 3*X^6 + X^5 + 15*X^4 + 13*X^3 + 6*X^2 + 14*X + 20) :=
  sq_step (by norm_num) pElevenB2s19 ⟨
    9*X^9 + 11*X^8 + 21*X^7 + 6*X^6 + 16*X^5 + 14*X^4 + 22*X^3 + 8*X^2 + 22*X + 8,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s21 : XPow fElevenB2 110920
    (3*X^10 + 3*X^9 + 2*X^8 + 20*X^7 + 20*X^6 + 14*X^5 + 2*X^4 + 7*X^3 + 8*X^2 + 13*X + 15) :=
  sq_step (by norm_num) pElevenB2s20 ⟨
    9*X^9 + 17*X^8 + 12*X^7 + 15*X^6 + 10*X^5 + 8*X^4 + 11*X^3 + 11*X^2 + 6*X + 20,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s22 : XPow fElevenB2 110921
    (5*X^10 + 14*X^9 + 6*X^8 + 19*X^7 + 4*X^6 + 7*X^5 + 4*X^4 + 7*X^3 + 17*X^2 + 21*X + 17) :=
  mul_step (by norm_num) pElevenB2s21 pElevenB21 ⟨
    3,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s23 : XPow fElevenB2 221842
    (11*X^10 + 13*X^8 + 17*X^7 + 17*X^6 + 22*X^5 + 10*X^4 + 20*X^3 + 19*X^2 + 11*X + 16) :=
  sq_step (by norm_num) pElevenB2s22 ⟨
    2*X^9 + 11*X^8 + 3*X^7 + 19*X^6 + 21*X^5 + 8*X^4 + 21*X^3 + 21*X^2 + 5*X + 10,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s24 : XPow fElevenB2 221843
    (15*X^10 + 11*X^9 + 4*X^8 + 21*X^7 + 16*X^6 + 13*X^5 + 9*X^4 + 18*X^2 + 15*X + 1) :=
  mul_step (by norm_num) pElevenB2s23 pElevenB21 ⟨
    11,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s25 : XPow fElevenB2 443686
    (20*X^10 + 5*X^9 + 19*X^8 + 8*X^7 + 17*X^6 + 21*X^5 + 7*X^4 + 2*X^3 + 14*X^2 + 10*X + 7) :=
  sq_step (by norm_num) pElevenB2s24 ⟨
    18*X^9 + 20*X^8 + 12*X^7 + 9*X^6 + 8*X^5 + 16*X^4 + 4*X^3 + 2*X^2 + 7*X + 20,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s26 : XPow fElevenB2 887372
    (10*X^10 + 18*X^7 + 2*X^6 + 5*X^5 + 13*X^4 + 4*X^3 + 11*X^2 + 12*X + 11) :=
  sq_step (by norm_num) pElevenB2s25 ⟨
    9*X^9 + 22*X^8 + 4*X^6 + 6*X^5 + X^4 + 13*X^3 + 12*X^2 + 14*X + 19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s27 : XPow fElevenB2 887373
    (22*X^10 + 17*X^9 + 2*X^8 + 14*X^7 + 10*X^6 + 22*X^5 + 17*X^4 + 10*X^2 + 8*X + 3) :=
  mul_step (by norm_num) pElevenB2s26 pElevenB21 ⟨
    10,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s28 : XPow fElevenB2 1774746
    (15*X^10 + 15*X^9 + 14*X^8 + 5*X^7 + 20*X^6 + 17*X^5 + 12*X^4 + 12*X^3 + 7*X^2 + 18*X + 12) :=
  sq_step (by norm_num) pElevenB2s27 ⟨
    X^9 + 5*X^8 + X^7 + 10*X^6 + 10*X^5 + 21*X^4 + 22*X^3 + 2*X^2 + 2*X + 10,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s29 : XPow fElevenB2 3549492
    (9*X^10 + 16*X^8 + 3*X^7 + 6*X^6 + 10*X^5 + 3*X^4 + 5*X^3 + 3*X^2 + 15*X + 20) :=
  sq_step (by norm_num) pElevenB2s28 ⟨
    18*X^9 + 2*X^8 + 13*X^7 + 12*X^6 + 17*X^5 + 15*X^4 + X^3 + 12*X^2 + 6*X + 16,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s30 : XPow fElevenB2 7098984
    (4*X^10 + 17*X^9 + 6*X^8 + 17*X^7 + 7*X^6 + 21*X^5 + 15*X^4 + 12*X^3 + 13*X^2 + 9*X + 10) :=
  sq_step (by norm_num) pElevenB2s29 ⟨
    12*X^9 + 8*X^8 + 4*X^7 + 2*X^6 + 18*X^5 + 20*X^4 + X^3 + 16*X^2 + 19*X + 11,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s31 : XPow fElevenB2 7098985
    (12*X^10 + 22*X^9 + 6*X^8 + 21*X^7 + 14*X^5 + 8*X^4 + 4*X^3 + 22*X^2 + 18*X + 15) :=
  mul_step (by norm_num) pElevenB2s30 pElevenB21 ⟨
    4,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s32 : XPow fElevenB2 14197970
    (20*X^10 + X^9 + 6*X^8 + 20*X^7 + 3*X^6 + 22*X^4 + 13*X^3 + 9*X^2 + 16*X + 3) :=
  sq_step (by norm_num) pElevenB2s31 ⟨
    6*X^9 + 3*X^8 + 10*X^7 + 15*X^6 + 5*X^5 + X^4 + 8*X^3 + 3*X^2 + 5*X + 19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s33 : XPow fElevenB2 14197971
    (22*X^10 + 17*X^9 + 11*X^8 + 4*X^7 + 10*X^6 + 17*X^5 + 16*X^4 + 10*X^3 + 12*X^2 + 20*X + 6) :=
  mul_step (by norm_num) pElevenB2s32 pElevenB21 ⟨
    20,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s34 : XPow fElevenB2 28395942
    (2*X^10 + 17*X^9 + 9*X^8 + 13*X^7 + 11*X^6 + 17*X^5 + 22*X^4 + 14*X^3 + 16*X^2 + 18*X + 11) :=
  sq_step (by norm_num) pElevenB2s33 ⟨
    X^9 + 5*X^8 + 6*X^7 + 2*X^6 + X^5 + 17*X^4 + 12*X^3 + X^2 + 20*X + 1,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s35 : XPow fElevenB2 28395943
    (3*X^10 + 17*X^9 + 19*X^8 + 18*X^7 + 18*X^6 + 10*X^5 + 12*X^4 + 13*X^2 + 15*X + 19) :=
  mul_step (by norm_num) pElevenB2s34 pElevenB21 ⟨
    2,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s36 : XPow fElevenB2 56791886
    (21*X^10 + 4*X^9 + 17*X^8 + 22*X^7 + 12*X^6 + 7*X^4 + 20*X^3 + 20*X^2 + 18*X + 10) :=
  sq_step (by norm_num) pElevenB2s35 ⟨
    9*X^9 + 16*X^8 + 5*X^7 + 5*X^6 + 7*X^5 + 11*X^4 + 12*X^3 + 21*X^2 + 3*X + 3,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s37 : XPow fElevenB2 56791887
    (18*X^10 + 9*X^9 + 16*X^8 + 5*X^7 + 22*X^6 + 19*X^5 + 22*X^4 + 13*X^3 + 6*X + 4) :=
  mul_step (by norm_num) pElevenB2s36 pElevenB21 ⟨
    21,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s38 : XPow fElevenB2 113583774
    (14*X^10 + 13*X^9 + 17*X^8 + 19*X^7 + 15*X^6 + 11*X^5 + 8*X^4 + 20*X^3 + 9*X^2 + 21*X + 8) :=
  sq_step (by norm_num) pElevenB2s37 ⟨
    2*X^9 + 11*X^8 + 13*X^7 + 13*X^6 + 12*X^5 + 10*X^4 + 10*X^3 + 3*X^2 + 6*X + 4,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s39 : XPow fElevenB2 227167548
    (4*X^10 + X^9 + 22*X^8 + 12*X^7 + 22*X^6 + 21*X^5 + 2*X^4 + 4*X^3 + 10*X^2 + 9) :=
  sq_step (by norm_num) pElevenB2s38 ⟨
    12*X^9 + 4*X^8 + 21*X^7 + 5*X^6 + 18*X^5 + 10*X^4 + 10*X^3 + 3*X^2 + 16,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s40 : XPow fElevenB2 454335096
    (6*X^10 + 8*X^8 + 6*X^7 + 13*X^6 + 11*X^5 + 7*X^4 + 20*X^3 + 3*X^2 + 3*X + 20) :=
  sq_step (by norm_num) pElevenB2s39 ⟨
    16*X^9 + 11*X^8 + 3*X^7 + 4*X^6 + 21*X^5 + 9*X^4 + 19*X^3 + 19*X^2 + 6*X + 19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s41 : XPow fElevenB2 454335097
    (4*X^10 + 9*X^9 + X^8 + 11*X^7 + 14*X^6 + 17*X^5 + 14*X^4 + X^3 + 11*X^2 + 9*X + 11) :=
  mul_step (by norm_num) pElevenB2s40 pElevenB21 ⟨
    6,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s42 : XPow fElevenB2 908670194
    (9*X^10 + 14*X^8 + 20*X^7 + X^6 + X^5 + 7*X^4 + 17*X^3 + 2*X + 16) :=
  sq_step (by norm_num) pElevenB2s41 ⟨
    16*X^9 + 6*X^8 + 19*X^7 + 22*X^6 + 8*X^5 + 22*X^4 + 13*X^3 + 2*X^2 + X + 18,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s43 : XPow fElevenB2 1817340388
    (21*X^10 + 6*X^9 + 6*X^8 + X^7 + 9*X^6 + 11*X^5 + 13*X^4 + 2*X^3 + 6*X^2 + 18*X + 3) :=
  sq_step (by norm_num) pElevenB2s42 ⟨
    12*X^9 + 8*X^8 + 14*X^7 + 8*X^6 + 4*X^5 + 14*X^4 + 17*X^3 + 22*X^2,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s44 : XPow fElevenB2 1817340389
    (20*X^10 + 21*X^9 + 18*X^8 + 2*X^7 + 10*X^6 + 2*X^5 + 4*X^4 + 22*X^3 + 22*X + 4) :=
  mul_step (by norm_num) pElevenB2s43 pElevenB21 ⟨
    21,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s45 : XPow fElevenB2 3634680778
    (4*X^10 + 16*X^9 + 16*X^8 + 10*X^7 + 22*X^6 + 10*X^5 + 8*X^4 + 22*X^3 + 6*X^2 + 21*X + 22) :=
  sq_step (by norm_num) pElevenB2s44 ⟨
    9*X^9 + 18*X^8 + 13*X^7 + 16*X^6 + 17*X^5 + 14*X^4 + 17*X^3 + X^2 + 17*X + 20,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s46 : XPow fElevenB2 7269361556
    (3*X^10 + 3*X^9 + 3*X^8 + 14*X^7 + 21*X^6 + 9*X^5 + 12*X^4 + 5*X^3 + 4*X^2 + 18*X + 16) :=
  sq_step (by norm_num) pElevenB2s45 ⟨
    16*X^9 + 16*X^8 + 14*X^7 + 8*X^6 + 5*X^5 + 11*X^4 + 12*X^3 + 9*X^2 + 20*X + 4,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s47 : XPow fElevenB2 14538723112
    (19*X^10 + 12*X^8 + 3*X^7 + 4*X^6 + 22*X^5 + 11*X^4 + 7*X^3 + 3*X^2 + 18*X + 11) :=
  sq_step (by norm_num) pElevenB2s46 ⟨
    9*X^9 + X^8 + 10*X^7 + 17*X^6 + 2*X^5 + 11*X^4 + 9*X^3 + 10*X^2 + 22*X + 19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s48 : XPow fElevenB2 29077446224
    (19*X^10 + 10*X^9 + 13*X^8 + 20*X^7 + 17*X^6 + 6*X^5 + 12*X^4 + 19*X^3 + 7*X^2 + 21*X + 1) :=
  sq_step (by norm_num) pElevenB2s47 ⟨
    16*X^9 + 3*X^8 + 16*X^7 + 16*X^6 + 14*X^5 + 9*X^4 + 8*X^3 + 19*X^2 + 6*X + 14,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s49 : XPow fElevenB2 29077446225
    (15*X^10 + 20*X^9 + 8*X^8 + 3*X^7 + 4*X^6 + 13*X^5 + 16*X^3 + 8*X^2 + 16*X + 8) :=
  mul_step (by norm_num) pElevenB2s48 pElevenB21 ⟨
    19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s50 : XPow fElevenB2 58154892450
    (6*X^10 + 3*X^9 + 17*X^8 + 11*X^7 + 19*X^6 + X^5 + 15*X^3 + 8*X^2 + 6*X + 3) :=
  sq_step (by norm_num) pElevenB2s49 ⟨
    18*X^9 + 14*X^8 + 16*X^7 + 17*X^6 + 9*X^5 + 19*X^4 + 19*X^3 + 15*X^2 + 6*X + 19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s51 : XPow fElevenB2 116309784900
    (16*X^10 + 3*X^9 + 9*X^8 + 9*X^7 + 17*X^6 + 10*X^5 + 18*X^4 + 6*X^3 + X^2 + 4*X + 18) :=
  sq_step (by norm_num) pElevenB2s50 ⟨
    13*X^9 + 14*X^8 + 6*X^7 + 11*X^6 + 8*X^5 + 21*X^4 + 20*X^3 + 4*X^2 + 7,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s52 : XPow fElevenB2 116309784901
    (6*X^10 + 4*X^9 + 11*X^8 + 4*X^7 + 18*X^6 + 14*X^5 + 13*X^4 + 11*X^3 + 10*X^2 + 4*X + 14) :=
  mul_step (by norm_num) pElevenB2s51 pElevenB21 ⟨
    16,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s53 : XPow fElevenB2 232619569802
    (20*X^10 + 7*X^9 + 15*X^8 + 15*X^7 + 15*X^5 + 14*X^4 + 22*X^3 + 17*X^2 + 20*X + 7) :=
  sq_step (by norm_num) pElevenB2s52 ⟨
    13*X^9 + 3*X^8 + 18*X^7 + 15*X^6 + 11*X^5 + 17*X^4 + 4*X^3 + 21*X^2 + 14*X + 14,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s54 : XPow fElevenB2 232619569803
    (5*X^10 + 3*X^9 + 6*X^8 + X^7 + 2*X^6 + 9*X^5 + 2*X^4 + 18*X^3 + 16*X^2 + X + 6) :=
  mul_step (by norm_num) pElevenB2s53 pElevenB21 ⟨
    20,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s55 : XPow fElevenB2 465239139606
    (2*X^10 + 2*X^9 + 6*X^8 + 14*X^7 + 4*X^6 + 7*X^5 + 8*X^4 + 19*X^3 + 5*X^2 + 11*X + 3) :=
  sq_step (by norm_num) pElevenB2s54 ⟨
    2*X^9 + 16*X^8 + 11*X^7 + 16*X^6 + 3*X^5 + 17*X^4 + 17*X^3 + 7*X^2 + 17*X + 5,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s56 : XPow fElevenB2 930478279212
    (20*X^10 + 10*X^9 + 16*X^8 + 19*X^7 + 17*X^6 + 4*X^5 + 22*X^4 + 6*X^3 + 14*X^2 + 3*X) :=
  sq_step (by norm_num) pElevenB2s55 ⟨
    4*X^9 + 3*X^8 + 12*X^6 + X^5 + X^4 + 4*X^3 + 4*X^2 + 13*X + 16,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s57 : XPow fElevenB2 1860956558424
    (X^10 + 6*X^9 + 7*X^8 + 21*X^7 + 14*X^6 + 19*X^4 + 20*X^3 + 21*X + 10) :=
  sq_step (by norm_num) pElevenB2s56 ⟨
    9*X^9 + 15*X^8 + 4*X^7 + 12*X^6 + 2*X^5 + 15*X^4 + 12*X^3 + X^2 + 19*X + 18,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s58 : XPow fElevenB2 1860956558425
    (22*X^10 + 11*X^9 + X^8 + 6*X^7 + 12*X^6 + 13*X^5 + 19*X^4 + 15*X^3 + 7*X^2 + 12*X + 21) :=
  mul_step (by norm_num) pElevenB2s57 pElevenB21 ⟨
    1,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s59 : XPow fElevenB2 3721913116850
    (19*X^10 + 4*X^9 + 15*X^7 + 20*X^6 + 12*X^5 + X^4 + 10*X^3 + 19*X^2 + 10*X + 20) :=
  sq_step (by norm_num) pElevenB2s58 ⟨
    X^9 + 17*X^8 + 4*X^7 + 7*X^6 + 4*X^5 + 5*X^3 + 10*X^2 + 9*X + 15,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s60 : XPow fElevenB2 3721913116851
    (9*X^10 + 7*X^9 + 3*X^8 + 6*X^7 + 10*X^6 + 2*X^5 + 14*X^4 + 5*X^3 + 20*X^2 + 12*X + 8) :=
  mul_step (by norm_num) pElevenB2s59 pElevenB21 ⟨
    19,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s61 : XPow fElevenB2 7443826233702
    (13*X^9 + 21*X^7 + 18*X^6 + 14*X^5 + 8*X^4 + 10*X^3 + 22*X^2 + 6*X + 21) :=
  sq_step (by norm_num) pElevenB2s60 ⟨
    12*X^9 + 19*X^8 + 18*X^7 + 21*X^6 + 21*X^5 + 11*X^4 + 21*X^3 + X^2 + 11*X + 10,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s62 : XPow fElevenB2 14887652467404
    (3*X^10 + 5*X^9 + 5*X^8 + 6*X^6 + 5*X^5 + 18*X^4 + 21*X^3 + 19*X^2 + 15) :=
  sq_step (by norm_num) pElevenB2s61 ⟨
    8*X^7 + 13*X^6 + 4*X^5 + 10*X^4 + 13*X^3 + 20*X^2 + 17*X + 6,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s63 : XPow fElevenB2 14887652467405
    (7*X^10 + 17*X^9 + 9*X^8 + 5*X^7 + 18*X^6 + 18*X^4 + 18*X^3 + 4*X^2 + 21*X + 17) :=
  mul_step (by norm_num) pElevenB2s62 pElevenB21 ⟨
    3,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s64 : XPow fElevenB2 29775304934810
    (6*X^10 + 8*X^9 + X^8 + 2*X^7 + 19*X^6 + 18*X^5 + 6*X^4 + 11*X^3 + 16*X^2 + 18*X + 2) :=
  sq_step (by norm_num) pElevenB2s63 ⟨
    3*X^9 + 10*X^8 + 12*X^7 + 19*X^6 + 10*X^5 + 10*X^4 + 13*X^3 + 9*X^2 + 20*X + 17,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s65 : XPow fElevenB2 59550609869620
    (7*X^10 + 11*X^9 + 15*X^8 + 8*X^7 + 19*X^6 + 5*X^5 + 4*X^4 + 15*X^3 + 21*X^2 + 8*X + 16) :=
  sq_step (by norm_num) pElevenB2s64 ⟨
    13*X^9 + 5*X^8 + X^7 + 15*X^5 + 9*X^4 + 5*X^3 + 10*X^2 + 3*X + 17,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s66 : XPow fElevenB2 119101219739240
    (10*X^10 + 9*X^9 + 13*X^8 + 17*X^7 + X^6 + 3*X^5 + 13*X^4 + 8*X^3 + 3*X^2 + 7*X) :=
  sq_step (by norm_num) pElevenB2s65 ⟨
    3*X^9 + 18*X^8 + 10*X^7 + 16*X^6 + 4*X^5 + 19*X^4 + 21*X^3 + 22*X^2 + 11*X + 13,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s67 : XPow fElevenB2 238202439478480
    (7*X^10 + 20*X^9 + 2*X^8 + 8*X^7 + 8*X^6 + 4*X^5 + 15*X^4 + 8*X^3 + 3*X^2 + 9*X + 13) :=
  sq_step (by norm_num) pElevenB2s66 ⟨
    8*X^9 + 9*X^8 + 11*X^7 + 5*X^6 + 7*X^5 + 19*X^4 + 5*X^3 + 12*X + 5,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s68 : XPow fElevenB2 238202439478481
    (17*X^10 + 7*X^9 + 6*X^8 + 21*X^7 + 19*X^6 + 19*X^5 + X^4 + 16*X^3 + 3*X^2 + 4*X + 9) :=
  mul_step (by norm_num) pElevenB2s67 pElevenB21 ⟨
    7,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s69 : XPow fElevenB2 476404878956962
    (12*X^10 + 15*X^9 + 21*X^8 + 10*X^7 + 4*X^6 + 17*X^5 + 3*X^4 + 12*X^3 + 4*X^2 + 7*X + 22) :=
  sq_step (by norm_num) pElevenB2s68 ⟨
    13*X^9 + 9*X^8 + 12*X^7 + 7*X^6 + X^5 + 17*X^4 + 4*X^3 + 15*X^2 + 16*X + 18,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s70 : XPow fElevenB2 476404878956963
    (22) :=
  mul_step (by norm_num) pElevenB2s69 pElevenB21 ⟨
    12,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s71 : XPow fElevenB2 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenB2s70 ⟨
    0,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB2s72 : XPow fElevenB2 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenB2s71 pElevenB21 ⟨
    0,
    by simp only [fElevenB2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 3: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenB31 : XPow fElevenB3 1 X := xpow_one _

theorem pElevenB3s0 : XPow fElevenB3 2
    (X^2) :=
  sq_step (by norm_num) pElevenB31 ⟨
    0,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s1 : XPow fElevenB3 3
    (X^3) :=
  mul_step (by norm_num) pElevenB3s0 pElevenB31 ⟨
    0,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s2 : XPow fElevenB3 6
    (X^6) :=
  sq_step (by norm_num) pElevenB3s1 ⟨
    0,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s3 : XPow fElevenB3 12
    (5*X^10 + 19*X^9 + 10*X^8 + 13*X^7 + 11*X^6 + 11*X^5 + 5*X^4 + 22*X^2 + 17*X + 16) :=
  sq_step (by norm_num) pElevenB3s2 ⟨
    X + 10,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s4 : XPow fElevenB3 13
    (18*X^9 + 5*X^8 + 3*X^7 + 18*X^6 + 13*X^5 + 21*X^4 + 21*X^3 + 4*X^2 + 3*X + 8) :=
  mul_step (by norm_num) pElevenB3s3 pElevenB31 ⟨
    5,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s5 : XPow fElevenB3 26
    (19*X^10 + 10*X^9 + 7*X^8 + 16*X^7 + 17*X^6 + 20*X^5 + 5*X^4 + 20*X^3 + 2*X^2 + 12*X + 21) :=
  sq_step (by norm_num) pElevenB3s4 ⟨
    2*X^7 + 16*X^6 + 11*X^5 + 10*X^4 + 19*X^3 + 5*X^2 + 19*X + 22,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s6 : XPow fElevenB3 27
    (16*X^10 + 19*X^9 + 4*X^8 + 5*X^7 + 19*X^6 + 17*X^5 + 17*X^4 + 12*X^3 + 4*X^2 + 13*X + 12) :=
  mul_step (by norm_num) pElevenB3s5 pElevenB31 ⟨
    19,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s7 : XPow fElevenB3 54
    (6*X^10 + 18*X^9 + 20*X^8 + 14*X^7 + 13*X^6 + 14*X^5 + 17*X^4 + X^3 + 6*X^2 + 11*X + 14) :=
  sq_step (by norm_num) pElevenB3s6 ⟨
    3*X^9 + 17*X^8 + 6*X^7 + 8*X^6 + 16*X^5 + 11*X^4 + 8*X^2 + 4*X + 5,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s8 : XPow fElevenB3 108
    (X^10 + 13*X^9 + 8*X^8 + 13*X^7 + 7*X^6 + 7*X^5 + 3*X^4 + 17*X^3 + 22*X^2 + 15*X + 6) :=
  sq_step (by norm_num) pElevenB3s7 ⟨
    13*X^9 + X^8 + 6*X^7 + 18*X^6 + 22*X^5 + 12*X^4 + 22*X^3 + 3*X^2 + 7*X + 2,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s9 : XPow fElevenB3 216
    (12*X^10 + 5*X^9 + 21*X^8 + 12*X^7 + 4*X^6 + 19*X^5 + 20*X^4 + 17*X^3 + 13*X^2 + 13*X + 9) :=
  sq_step (by norm_num) pElevenB3s8 ⟨
    X^9 + 13*X^8 + 13*X^7 + 6*X^6 + 19*X^5 + 16*X^4 + 14*X^3 + 9*X^2 + 8*X + 9,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s10 : XPow fElevenB3 432
    (22*X^10 + 9*X^9 + 3*X^7 + 10*X^6 + 15*X^5 + 6*X^4 + 2*X^3 + 17*X^2 + 22*X + 8) :=
  sq_step (by norm_num) pElevenB3s9 ⟨
    6*X^9 + 19*X^8 + 11*X^7 + 17*X^6 + 18*X^5 + 13*X^4 + 19*X^3 + 12*X^2 + 9,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s11 : XPow fElevenB3 433
    (22*X^10 + 3*X^9 + 7*X^7 + 9*X^6 + 9*X^5 + 7*X^4 + 8*X^3 + 20*X^2 + 6*X + 3) :=
  mul_step (by norm_num) pElevenB3s10 pElevenB31 ⟨
    22,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s12 : XPow fElevenB3 866
    (9*X^10 + 7*X^9 + 6*X^8 + 3*X^7 + 9*X^6 + 20*X^5 + 13*X^4 + X^3 + 18*X^2 + 20*X + 10) :=
  sq_step (by norm_num) pElevenB3s11 ⟨
    X^9 + 4*X^8 + 16*X^5 + 7*X^4 + 17*X^3 + 10*X^2 + 15,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s13 : XPow fElevenB3 1732
    (7*X^10 + 15*X^9 + 11*X^8 + 14*X^7 + 6*X^6 + 22*X^5 + 17*X^4 + 17*X^3 + 11*X^2 + 14*X + 18) :=
  sq_step (by norm_num) pElevenB3s12 ⟨
    12*X^9 + 16*X^8 + 5*X^7 + 15*X^6 + 22*X^5 + 4*X^4 + 12*X^3 + 14*X^2 + 14*X + 12,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s14 : XPow fElevenB3 1733
    (16*X^10 + 13*X^9 + 12*X^8 + 4*X^7 + 18*X^6 + 19*X^5 + 5*X^4 + 5*X^3 + 5*X^2 + 9*X + 2) :=
  mul_step (by norm_num) pElevenB3s13 pElevenB31 ⟨
    7,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s15 : XPow fElevenB3 3466
    (7*X^10 + 19*X^9 + 18*X^8 + 3*X^7 + 11*X^6 + 15*X^5 + 6*X^4 + 6*X^3 + 22*X^2 + 12) :=
  sq_step (by norm_num) pElevenB3s14 ⟨
    3*X^9 + 9*X^8 + 13*X^7 + 16*X^5 + 13*X^4 + 3*X^3 + 22*X^2 + 5,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s16 : XPow fElevenB3 6932
    (16*X^10 + 20*X^9 + 16*X^8 + 11*X^7 + 7*X^6 + 8*X^5 + 15*X^4 + 22*X^3 + 14*X + 8) :=
  sq_step (by norm_num) pElevenB3s15 ⟨
    3*X^9 + 20*X^8 + 22*X^7 + 21*X^6 + 12*X^4 + 16*X^3 + 12*X^2 + 7,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s17 : XPow fElevenB3 13864
    (13*X^10 + 4*X^9 + 21*X^7 + 9*X^6 + 17*X^5 + 13*X^4 + 17*X^3 + 4*X^2 + 20*X) :=
  sq_step (by norm_num) pElevenB3s16 ⟨
    3*X^9 + 3*X^8 + 13*X^7 + 18*X^6 + 21*X^5 + 6*X^4 + 2*X^3 + X^2 + 3*X + 6,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s18 : XPow fElevenB3 13865
    (19*X^10 + 7*X^9 + 14*X^8 + 2*X^7 + 3*X^6 + 20*X^5 + 21*X^4 + 6*X^3 + 3*X + 7) :=
  mul_step (by norm_num) pElevenB3s17 pElevenB31 ⟨
    13,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s19 : XPow fElevenB3 27730
    (6*X^10 + 4*X^9 + 13*X^8 + 8*X^7 + 20*X^6 + 17*X^5 + 17*X^4 + 15*X^3 + 18*X^2 + 11*X + 4) :=
  sq_step (by norm_num) pElevenB3s18 ⟨
    16*X^9 + 12*X^8 + 9*X^7 + 6*X^6 + 18*X^5 + 6*X^4 + 22*X^3 + 18*X^2 + 5*X + 15,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s20 : XPow fElevenB3 55460
    (10*X^10 + 7*X^9 + 2*X^8 + 13*X^7 + 19*X^6 + 14*X^5 + 14*X^4 + 6*X^3 + 21*X^2 + 14*X + 21) :=
  sq_step (by norm_num) pElevenB3s19 ⟨
    13*X^9 + 17*X^8 + 4*X^7 + 21*X^6 + 2*X^5 + 3*X^4 + 5*X^3 + 15*X^2 + 21*X + 6,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s21 : XPow fElevenB3 110920
    (21*X^10 + 22*X^9 + 22*X^8 + 19*X^7 + 6*X^6 + 15*X^5 + 5*X^4 + 9*X^3 + 10*X^2 + X + 9) :=
  sq_step (by norm_num) pElevenB3s20 ⟨
    8*X^9 + 13*X^8 + 11*X^7 + 15*X^6 + 10*X^5 + 14*X^4 + 20*X^3 + 5*X^2 + 8*X + 6,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s22 : XPow fElevenB3 110921
    (2*X^10 + 5*X^9 + 13*X^8 + 3*X^6 + 11*X^5 + 19*X^4 + 15*X^3 + 20*X^2 + 5*X + 6) :=
  mul_step (by norm_num) pElevenB3s21 pElevenB31 ⟨
    21,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s23 : XPow fElevenB3 221842
    (18*X^9 + 6*X^8 + 4*X^7 + 18*X^6 + 6*X^5 + 19*X^4 + 22*X^3 + 6*X + 12) :=
  sq_step (by norm_num) pElevenB3s22 ⟨
    4*X^9 + 14*X^8 + 21*X^7 + 11*X^6 + 6*X^5 + 7*X^2 + 8*X + 8,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s24 : XPow fElevenB3 221843
    (18*X^10 + 6*X^9 + 4*X^8 + 18*X^7 + 6*X^6 + 19*X^5 + 22*X^4 + 6*X^2 + 12*X) :=
  mul_step (by norm_num) pElevenB3s23 pElevenB31 ⟨
    0,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s25 : XPow fElevenB3 443686
    (13*X^10 + 7*X^9 + X^8 + 20*X^7 + 7*X^6 + 14*X^5 + 8*X^4 + 18*X^3 + X^2 + 11*X + 17) :=
  sq_step (by norm_num) pElevenB3s24 ⟨
    2*X^9 + 6*X^8 + 4*X^7 + 11*X^6 + 18*X^5 + 8*X^4 + 21*X^3 + 4*X^2 + 13*X + 2,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s26 : XPow fElevenB3 887372
    (4*X^10 + 18*X^9 + 8*X^8 + 17*X^7 + 10*X^6 + 2*X^5 + 15*X^4 + 5*X^3 + 13*X^2 + 22*X + 16) :=
  sq_step (by norm_num) pElevenB3s25 ⟨
    8*X^9 + 9*X^8 + 3*X^7 + 9*X^6 + 20*X^5 + 19*X^3 + 12*X^2 + 17*X + 22,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s27 : XPow fElevenB3 887373
    (12*X^10 + 19*X^9 + 6*X^8 + 22*X^7 + 3*X^6 + 3*X^5 + 8*X^4 + 3*X^3 + 7*X^2 + X + 11) :=
  mul_step (by norm_num) pElevenB3s26 pElevenB31 ⟨
    4,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s28 : XPow fElevenB3 1774746
    (9*X^10 + 20*X^9 + 5*X^8 + 7*X^6 + 8*X^5 + 18*X^4 + 2*X^2 + 14*X) :=
  sq_step (by norm_num) pElevenB3s27 ⟨
    6*X^9 + 10*X^8 + 12*X^7 + 13*X^6 + 5*X^5 + 11*X^4 + 3*X^3 + 9*X^2 + 4*X + 2,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s29 : XPow fElevenB3 3549492
    (3*X^10 + 3*X^9 + 22*X^8 + 21*X^7 + 4*X^6 + 21*X^5 + 2*X^4 + X^3 + 5*X^2 + 17*X + 7) :=
  sq_step (by norm_num) pElevenB3s28 ⟨
    12*X^9 + 20*X^8 + 10*X^7 + 10*X^5 + 19*X^4 + 22*X^3 + 13*X^2 + 3*X + 13,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s30 : XPow fElevenB3 7098984
    (16*X^10 + 5*X^9 + 8*X^8 + 21*X^7 + 2*X^6 + 13*X^5 + 19*X^4 + 19*X^3 + 19*X^2 + 12*X + 12) :=
  sq_step (by norm_num) pElevenB3s29 ⟨
    9*X^9 + 16*X^8 + 21*X^7 + 10*X^6 + 10*X^5 + 21*X^4 + 16*X^3 + 12*X^2 + 12*X + 20,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s31 : XPow fElevenB3 7098985
    (4*X^10 + 6*X^9 + 4*X^7 + 17*X^6 + 17*X^5 + 8*X^4 + 2*X^3 + 21*X^2 + 21*X + 21) :=
  mul_step (by norm_num) pElevenB3s30 pElevenB31 ⟨
    16,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s32 : XPow fElevenB3 14197970
    (10*X^10 + 9*X^9 + 13*X^8 + 7*X^7 + 5*X^6 + X^5 + 4*X^4 + 14*X^3 + 14*X + 2) :=
  sq_step (by norm_num) pElevenB3s31 ⟨
    16*X^9 + X^8 + 21*X^7 + 11*X^6 + 6*X^5 + 21*X^3 + X + 16,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s33 : XPow fElevenB3 14197971
    (17*X^10 + 6*X^9 + 14*X^8 + 12*X^7 + 15*X^6 + 20*X^5 + 10*X^4 + 21*X^3 + 11*X^2 + 22*X + 16) :=
  mul_step (by norm_num) pElevenB3s32 pElevenB31 ⟨
    10,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s34 : XPow fElevenB3 28395942
    (14*X^10 + 2*X^9 + 8*X^8 + 17*X^7 + 2*X^6 + X^5 + 16*X^4 + 20*X^3 + 22*X^2 + 16*X + 14) :=
  sq_step (by norm_num) pElevenB3s33 ⟨
    13*X^9 + 12*X^8 + 18*X^7 + 20*X^5 + 21*X^3 + 7*X^2 + 2*X + 4,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s35 : XPow fElevenB3 28395943
    (4*X^10 + 12*X^9 + 13*X^8 + 21*X^7 + 16*X^6 + 20*X^5 + 19*X^4 + 10*X^3 + 21*X^2 + 19*X + 4) :=
  mul_step (by norm_num) pElevenB3s34 pElevenB31 ⟨
    14,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s36 : XPow fElevenB3 56791886
    (18*X^10 + 15*X^9 + 12*X^8 + 19*X^7 + 13*X^6 + 22*X^5 + 11*X^3 + 14*X^2 + 9*X + 15) :=
  sq_step (by norm_num) pElevenB3s35 ⟨
    16*X^9 + 3*X^8 + 13*X^6 + 22*X^5 + 19*X^4 + 12*X^3 + 13*X^2 + 7*X + 8,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s37 : XPow fElevenB3 56791887
    (11*X^10 + 4*X^9 + 4*X^8 + 21*X^7 + 15*X^6 + 15*X^5 + 13*X^4 + 15*X^3 + 22*X^2 + 5*X + 15) :=
  mul_step (by norm_num) pElevenB3s36 pElevenB31 ⟨
    18,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s38 : XPow fElevenB3 113583774
    (11*X^10 + 16*X^9 + 8*X^8 + X^7 + 8*X^6 + 17*X^5 + 6*X^3 + 16*X^2 + 4*X + 1) :=
  sq_step (by norm_num) pElevenB3s37 ⟨
    6*X^9 + 10*X^8 + 2*X^7 + 19*X^6 + 10*X^5 + 20*X^4 + 13*X^2 + 9*X + 21,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s39 : XPow fElevenB3 227167548
    (2*X^10 + X^9 + 9*X^8 + 8*X^7 + 13*X^6 + X^5 + 2*X^4 + 22*X^3 + 16*X^2 + 3*X + 17) :=
  sq_step (by norm_num) pElevenB3s38 ⟨
    6*X^9 + 21*X^8 + 3*X^7 + 10*X^6 + 7*X^5 + 12*X^4 + 22*X^3 + 5*X^2 + 16*X + 10,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s40 : XPow fElevenB3 454335096
    (7*X^9 + X^8 + 3*X^7 + 14*X^6 + 8*X^5 + 22*X^4 + 6*X^3 + 13*X^2 + 17*X + 13) :=
  sq_step (by norm_num) pElevenB3s39 ⟨
    4*X^9 + 21*X^8 + 5*X^7 + 3*X^6 + 9*X^5 + 12*X^4 + 10*X^3 + 20*X^2 + 13*X,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s41 : XPow fElevenB3 454335097
    (7*X^10 + X^9 + 3*X^8 + 14*X^7 + 8*X^6 + 22*X^5 + 6*X^4 + 13*X^3 + 17*X^2 + 13*X) :=
  mul_step (by norm_num) pElevenB3s40 pElevenB31 ⟨
    0,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s42 : XPow fElevenB3 908670194
    (X^10 + X^9 + 19*X^8 + X^7 + 21*X^6 + X^5 + 21*X^4 + 18*X^3 + 5*X^2 + 14*X + 7) :=
  sq_step (by norm_num) pElevenB3s41 ⟨
    3*X^9 + 21*X^8 + 14*X^7 + 12*X^6 + 12*X^4 + 20*X^3 + 20*X^2 + 4*X + 13,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s43 : XPow fElevenB3 1817340388
    (8*X^10 + 14*X^9 + 13*X^8 + 12*X^7 + 21*X^6 + 3*X^5 + 17*X^4 + 4*X^3 + 12*X^2 + 3*X + 4) :=
  sq_step (by norm_num) pElevenB3s42 ⟨
    X^9 + 12*X^8 + 18*X^7 + 3*X^6 + 6*X^5 + 22*X^4 + 4*X^3 + 19*X^2 + 13*X + 15,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s44 : XPow fElevenB3 1817340389
    (2*X^10 + 12*X^9 + 13*X^8 + 22*X^7 + 5*X^6 + 16*X^5 + 10*X^4 + 15*X^3 + 19*X^2 + 20*X + 22) :=
  mul_step (by norm_num) pElevenB3s43 pElevenB31 ⟨
    8,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s45 : XPow fElevenB3 3634680778
    (13*X^10 + 18*X^9 + 3*X^8 + 15*X^7 + 14*X^6 + 21*X^5 + 4*X^4 + 18*X^3 + 4*X^2 + 9) :=
  sq_step (by norm_num) pElevenB3s44 ⟨
    4*X^9 + 19*X^8 + 6*X^7 + X^6 + 19*X^5 + 7*X^4 + X^3 + X^2 + 13*X + 5,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s46 : XPow fElevenB3 7269361556
    (12*X^10 + 4*X^9 + 20*X^8 + 5*X^7 + 11*X^6 + 11*X^5 + 11*X^4 + 12*X^3 + 6*X^2 + 4*X + 2) :=
  sq_step (by norm_num) pElevenB3s45 ⟨
    8*X^9 + 19*X^8 + 16*X^7 + 4*X^6 + 20*X^5 + 9*X^4 + 15*X^3 + 18*X^2 + 6*X + 11,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s47 : XPow fElevenB3 14538723112
    (21*X^10 + 2*X^9 + 2*X^8 + 22*X^7 + 14*X^6 + 14*X^5 + 21*X^4 + 9*X^3 + 6*X^2 + 4*X + 18) :=
  sq_step (by norm_num) pElevenB3s46 ⟨
    6*X^9 + 18*X^8 + 14*X^7 + 16*X^6 + 20*X^5 + 8*X^4 + 5*X^3 + 2*X^2 + 6*X + 3,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s48 : XPow fElevenB3 29077446224
    (12*X^10 + 19*X^9 + 16*X^8 + 5*X^7 + X^6 + 8*X^4 + 20*X^3 + 20*X^2 + 18*X + 18) :=
  sq_step (by norm_num) pElevenB3s47 ⟨
    4*X^9 + 9*X^8 + 5*X^7 + X^6 + X^5 + 17*X^3 + 5*X^2 + 18*X + 10,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s49 : XPow fElevenB3 29077446225
    (X^10 + 3*X^9 + 18*X^8 + 14*X^7 + 3*X^6 + 18*X^5 + 6*X^4 + 13*X^3 + 19*X^2 + 19*X + 10) :=
  mul_step (by norm_num) pElevenB3s48 pElevenB31 ⟨
    12,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s50 : XPow fElevenB3 58154892450
    (7*X^10 + 12*X^9 + 4*X^8 + 12*X^7 + 5*X^6 + 22*X^5 + 6*X^4 + 13*X^3 + 2*X^2 + 12*X + 8) :=
  sq_step (by norm_num) pElevenB3s49 ⟨
    X^9 + 16*X^8 + 18*X^7 + 18*X^6 + 16*X^5 + 13*X^4 + 17*X^3 + X^2,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s51 : XPow fElevenB3 116309784900
    (13*X^10 + 17*X^9 + 3*X^8 + 22*X^7 + 18*X^6 + 13*X^5 + 14*X^4 + 22*X^3 + 20*X^2 + 11*X + 15) :=
  sq_step (by norm_num) pElevenB3s50 ⟨
    3*X^9 + 14*X^8 + 9*X^7 + 22*X^6 + 20*X^5 + 9*X^4 + 5*X^3 + 9*X^2 + 15*X + 1,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s52 : XPow fElevenB3 116309784901
    (9*X^10 + 10*X^9 + 15*X^8 + 11*X^7 + 22*X^6 + 21*X^5 + 3*X^4 + 22*X^3 + 14*X^2 + 18*X + 7) :=
  mul_step (by norm_num) pElevenB3s51 pElevenB31 ⟨
    13,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s53 : XPow fElevenB3 232619569802
    (6*X^10 + X^9 + 21*X^8 + 22*X^6 + 20*X^5 + 13*X^4 + 5*X^3 + 10*X + 18) :=
  sq_step (by norm_num) pElevenB3s52 ⟨
    12*X^9 + X^8 + 22*X^7 + 15*X^6 + 21*X^5 + 5*X^4 + 12*X^3 + 12*X^2 + 16*X + 18,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s54 : XPow fElevenB3 232619569803
    (15*X^10 + 3*X^9 + 18*X^8 + 17*X^7 + 10*X^6 + 18*X^5 + 21*X^4 + 8*X^3 + 22*X^2 + 7*X + 5) :=
  mul_step (by norm_num) pElevenB3s53 pElevenB31 ⟨
    6,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s55 : XPow fElevenB3 465239139606
    (20*X^10 + 11*X^9 + 2*X^8 + 5*X^7 + 7*X^6 + 6*X^5 + 2*X^4 + 13*X^3 + 21*X^2 + 4) :=
  sq_step (by norm_num) pElevenB3s54 ⟨
    18*X^9 + 17*X^8 + 21*X^7 + 3*X^6 + 16*X^5 + 21*X^4 + 13*X^3 + 14*X^2 + 5*X + 7,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s56 : XPow fElevenB3 930478279212
    (7*X^10 + 5*X^9 + 2*X^8 + 17*X^7 + 7*X^6 + 4*X^5 + 19*X^4 + 9*X^3 + 3*X^2 + 14*X + 9) :=
  sq_step (by norm_num) pElevenB3s55 ⟨
    9*X^9 + X^8 + 15*X^6 + 22*X^5 + 2*X^4 + 13*X^3 + 17*X^2 + 2*X + 10,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s57 : XPow fElevenB3 1860956558424
    (8*X^10 + 6*X^9 + 21*X^8 + 12*X^7 + 12*X^6 + 9*X^5 + 8*X^4 + 19*X^3 + 4*X^2 + 14) :=
  sq_step (by norm_num) pElevenB3s56 ⟨
    3*X^9 + 8*X^8 + 9*X^7 + 11*X^6 + 20*X^5 + 16*X^4 + 17*X^3 + 18*X^2 + 12*X + 7,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s58 : XPow fElevenB3 1860956558425
    (17*X^10 + 20*X^9 + 13*X^8 + 13*X^7 + 11*X^6 + 7*X^5 + 2*X^4 + 7*X^3 + 16*X^2 + 7*X + 22) :=
  mul_step (by norm_num) pElevenB3s57 pElevenB31 ⟨
    8,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s59 : XPow fElevenB3 3721913116850
    (2*X^10 + 2*X^9 + 22*X^8 + 10*X^7 + 8*X^6 + 19*X^5 + 11*X^3 + 21*X^2 + 6*X + 20) :=
  sq_step (by norm_num) pElevenB3s58 ⟨
    13*X^9 + 5*X^8 + 2*X^7 + 17*X^6 + 16*X^5 + 5*X^4 + 2*X^3 + 17*X^2 + 7*X + 9,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s60 : XPow fElevenB3 3721913116851
    (22*X^10 + 16*X^9 + 16*X^8 + 14*X^7 + 8*X^6 + 17*X^5 + X^4 + 16*X^3 + 10*X^2 + X + 17) :=
  mul_step (by norm_num) pElevenB3s59 pElevenB31 ⟨
    2,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s61 : XPow fElevenB3 7443826233702
    (22*X^10 + 9*X^9 + 22*X^8 + 18*X^7 + 10*X^6 + 6*X^5 + 11*X^4 + 22*X^3 + 5*X^2 + 17*X + 4) :=
  sq_step (by norm_num) pElevenB3s60 ⟨
    X^9 + X^8 + X^7 + 11*X^6 + 19*X^5 + 11*X^4 + 5*X^3 + 22*X^2 + 3,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s62 : XPow fElevenB3 14887652467404
    (9*X^10 + 2*X^9 + 5*X^8 + 19*X^7 + 21*X^6 + 2*X^5 + 2*X^4 + 17*X^3 + 20*X^2 + 13*X + 5) :=
  sq_step (by norm_num) pElevenB3s61 ⟨
    X^9 + 15*X^8 + 19*X^6 + 14*X^5 + 13*X^4 + X^3 + 16*X^2 + 19,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s63 : XPow fElevenB3 14887652467405
    (X^9 + 2*X^7 + 10*X^6 + 21*X^5 + 18*X^4 + 9*X^3 + 8*X^2 + 19) :=
  mul_step (by norm_num) pElevenB3s62 pElevenB31 ⟨
    9,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s64 : XPow fElevenB3 29775304934810
    (X^10 + 8*X^9 + 20*X^8 + 12*X^7 + 18*X^5 + 4*X^4 + 11*X^3 + 8*X^2 + 8*X + 9) :=
  sq_step (by norm_num) pElevenB3s63 ⟨
    X^7 + 10*X^6 + 9*X^5 + 14*X^4 + 8*X^3 + 16*X^2 + 4*X + 10,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s65 : XPow fElevenB3 59550609869620
    (21*X^10 + 14*X^9 + 13*X^8 + 13*X^7 + 7*X^6 + 3*X^5 + 16*X^4 + 14*X^3 + 21*X^2 + 2*X + 11) :=
  sq_step (by norm_num) pElevenB3s64 ⟨
    X^9 + 3*X^8 + 16*X^7 + 15*X^6 + 16*X^5 + 4*X^4 + 11*X^3 + 21*X^2 + 22*X + 8,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s66 : XPow fElevenB3 119101219739240
    (7*X^10 + 4*X^9 + 22*X^8 + 7*X^7 + 2*X^6 + 10*X^5 + 14*X^4 + 3*X^3 + 20*X^2 + 18*X + 22) :=
  sq_step (by norm_num) pElevenB3s65 ⟨
    4*X^9 + 7*X^8 + 18*X^7 + X^5 + 10*X^4 + 2*X^2 + 10,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s67 : XPow fElevenB3 238202439478480
    (12*X^10 + 9*X^9 + 18*X^8 + 20*X^7 + 5*X^6 + 8*X^5 + 17*X^4 + 15*X^3 + 19*X^2 + 14*X + 3) :=
  sq_step (by norm_num) pElevenB3s66 ⟨
    3*X^9 + 17*X^8 + 2*X^7 + 22*X^6 + 14*X^5 + 15*X^4 + 19*X^3 + 16*X^2 + 11*X + 7,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s68 : XPow fElevenB3 238202439478481
    (14*X^10 + 5*X^9 + 10*X^8 + 18*X^7 + 11*X^6 + 4*X^5 + X^4 + 12*X^3 + 15*X^2 + 4*X + 10) :=
  mul_step (by norm_num) pElevenB3s67 pElevenB31 ⟨
    12,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s69 : XPow fElevenB3 476404878956962
    (8*X^10 + 12*X^9 + X^8 + 22*X^7 + 22*X^6 + 21*X^5 + X^4 + 17*X^3 + 20*X^2 + 7*X + 7) :=
  sq_step (by norm_num) pElevenB3s68 ⟨
    12*X^9 + 7*X^8 + 17*X^7 + 7*X^6 + 20*X^5 + 8*X^4 + 20*X^3 + 19*X^2 + 22*X + 8,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s70 : XPow fElevenB3 476404878956963
    (22) :=
  mul_step (by norm_num) pElevenB3s69 pElevenB31 ⟨
    8,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s71 : XPow fElevenB3 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenB3s70 ⟨
    0,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB3s72 : XPow fElevenB3 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenB3s71 pElevenB31 ⟨
    0,
    by simp only [fElevenB3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 4: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenB41 : XPow fElevenB4 1 X := xpow_one _

theorem pElevenB4s0 : XPow fElevenB4 2
    (X^2) :=
  sq_step (by norm_num) pElevenB41 ⟨
    0,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s1 : XPow fElevenB4 3
    (X^3) :=
  mul_step (by norm_num) pElevenB4s0 pElevenB41 ⟨
    0,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s2 : XPow fElevenB4 6
    (X^6) :=
  sq_step (by norm_num) pElevenB4s1 ⟨
    0,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s3 : XPow fElevenB4 12
    (5*X^10 + 14*X^9 + 19*X^7 + 7*X^6 + 16*X^5 + 10*X^4 + 2*X^3 + 7*X^2 + 5*X + 4) :=
  sq_step (by norm_num) pElevenB4s2 ⟨
    X + 8,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s4 : XPow fElevenB4 13
    (8*X^10 + 4*X^9 + 11*X^8 + 2*X^7 + 13*X^6 + X^4 + 19*X^3 + 11*X^2 + 14*X + 14) :=
  mul_step (by norm_num) pElevenB4s3 pElevenB41 ⟨
    5,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s5 : XPow fElevenB4 26
    (12*X^10 + 8*X^9 + 4*X^8 + 12*X^7 + 11*X^6 + 21*X^4 + 5*X^3 + 6*X^2 + 4*X + 16) :=
  sq_step (by norm_num) pElevenB4s4 ⟨
    18*X^9 + X^8 + 12*X^7 + 4*X^6 + 22*X^5 + 11*X^4 + 7*X^3 + 18*X^2 + 20*X + 8,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s6 : XPow fElevenB4 27
    (12*X^10 + 9*X^9 + 2*X^8 + 22*X^7 + 2*X^6 + 20*X^5 + 21*X^4 + 21*X^3 + 17*X + 6) :=
  mul_step (by norm_num) pElevenB4s5 pElevenB41 ⟨
    12,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s7 : XPow fElevenB4 54
    (2*X^10 + 18*X^9 + 12*X^8 + 3*X^7 + 12*X^6 + 19*X^5 + 7*X^4 + 12*X^3 + 15*X^2 + 21*X + 9) :=
  sq_step (by norm_num) pElevenB4s6 ⟨
    6*X^9 + 11*X^8 + X^7 + 10*X^6 + 13*X^5 + 19*X^4 + 20*X^3 + 16*X^2 + 11*X + 15,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s8 : XPow fElevenB4 108
    (9*X^10 + 4*X^9 + 15*X^8 + 18*X^7 + 18*X^5 + 4*X^3 + 10*X^2 + 18*X + 4) :=
  sq_step (by norm_num) pElevenB4s7 ⟨
    4*X^9 + 12*X^8 + 2*X^7 + 17*X^6 + 5*X^5 + 18*X^4 + 4*X^3 + 11*X + 7,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s9 : XPow fElevenB4 216
    (8*X^10 + 21*X^9 + 12*X^8 + 2*X^7 + 9*X^6 + 19*X^5 + 7*X^4 + 11*X^2 + 4*X + 12) :=
  sq_step (by norm_num) pElevenB4s8 ⟨
    12*X^9 + 7*X^8 + 2*X^7 + 14*X^6 + 4*X^5 + 2*X^4 + 16*X^3 + 9*X^2 + 5*X + 15,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s10 : XPow fElevenB4 432
    (7*X^10 + 10*X^9 + 5*X^8 + 19*X^7 + 3*X^6 + 15*X^5 + 22*X^4 + 4*X^3 + 2*X^2 + 20*X + 13) :=
  sq_step (by norm_num) pElevenB4s9 ⟨
    18*X^9 + 20*X^8 + 7*X^7 + 18*X^6 + 7*X^5 + 4*X^4 + 12*X^3 + 17*X^2 + 22*X + 14,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s11 : XPow fElevenB4 433
    (20*X^10 + 6*X^9 + 17*X^8 + 19*X^7 + 20*X^6 + 8*X^5 + 21*X^4 + 5*X^3 + 10*X^2 + 4*X + 15) :=
  mul_step (by norm_num) pElevenB4s10 pElevenB41 ⟨
    7,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s12 : XPow fElevenB4 866
    (12*X^10 + 20*X^9 + 15*X^8 + 10*X^7 + 9*X^6 + 7*X^5 + 14*X^4 + X^3 + 18) :=
  sq_step (by norm_num) pElevenB4s11 ⟨
    9*X^9 + 13*X^8 + 13*X^7 + 6*X^6 + 7*X^5 + 4*X^4 + 2*X^3 + 6*X^2 + 13*X,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s13 : XPow fElevenB4 1732
    (4*X^10 + 17*X^9 + 8*X^8 + X^7 + 13*X^6 + 20*X^5 + 3*X^4 + 14*X^3 + 10*X^2 + 9*X + 22) :=
  sq_step (by norm_num) pElevenB4s12 ⟨
    6*X^9 + 22*X^8 + 7*X^7 + 7*X^6 + 15*X^5 + 6*X^4 + 9*X^3 + 9*X^2 + 19*X + 17,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s14 : XPow fElevenB4 1733
    (3*X^10 + 2*X^9 + 13*X^8 + 9*X^7 + 13*X^6 + 18*X^5 + 4*X^4 + 15*X^3 + 7*X + 2) :=
  mul_step (by norm_num) pElevenB4s13 pElevenB41 ⟨
    4,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s15 : XPow fElevenB4 3466
    (2*X^10 + 2*X^9 + 10*X^8 + 3*X^7 + 14*X^6 + 15*X^5 + 10*X^4 + 16*X^3 + 20*X^2 + 16*X + 13) :=
  sq_step (by norm_num) pElevenB4s14 ⟨
    9*X^9 + 15*X^8 + 16*X^7 + 20*X^6 + 18*X^5 + 2*X^4 + 15*X^3 + 16*X^2 + 19*X + 18,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s16 : XPow fElevenB4 6932
    (20*X^10 + 16*X^9 + 15*X^8 + 18*X^7 + 19*X^5 + 17*X^4 + 19*X^3 + 2*X^2 + 17*X + 10) :=
  sq_step (by norm_num) pElevenB4s15 ⟨
    4*X^9 + 17*X^8 + 13*X^7 + 16*X^6 + 13*X^5 + 18*X^4 + 22*X^3 + X^2 + 14*X + 4,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s17 : XPow fElevenB4 13864
    (2*X^10 + 21*X^8 + 22*X^7 + 22*X^6 + 15*X^5 + 20*X^4 + 17*X^3 + 7*X^2 + 18*X + 16) :=
  sq_step (by norm_num) pElevenB4s16 ⟨
    9*X^9 + 22*X^8 + 18*X^7 + 4*X^6 + 12*X^5 + 9*X^4 + 5*X^3 + 6*X^2 + 5*X + 16,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s18 : XPow fElevenB4 13865
    (16*X^10 + 18*X^9 + 5*X^8 + 20*X^7 + 16*X^5 + 12*X^4 + 21*X^3 + 2*X^2 + 20*X + 1) :=
  mul_step (by norm_num) pElevenB4s17 pElevenB41 ⟨
    2,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s19 : XPow fElevenB4 27730
    (16*X^10 + 5*X^9 + 20*X^8 + 2*X^7 + 3*X^6 + 18*X^5 + 5*X^4 + 19*X^3 + 18*X^2 + 2*X + 20) :=
  sq_step (by norm_num) pElevenB4s18 ⟨
    3*X^9 + 2*X^8 + X^7 + 6*X^6 + X^5 + 11*X^4 + 5*X^3 + 12*X^2 + 2*X + 15,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s20 : XPow fElevenB4 55460
    (14*X^10 + 3*X^9 + 8*X^8 + 8*X^7 + X^6 + 17*X^5 + X^4 + 6*X^3 + 17*X^2 + X + 17) :=
  sq_step (by norm_num) pElevenB4s19 ⟨
    3*X^9 + 5*X^7 + 14*X^6 + 8*X^5 + 20*X^4 + 22*X^3 + 6*X^2 + 8*X + 16,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s21 : XPow fElevenB4 110920
    (14*X^10 + X^9 + 17*X^7 + 11*X^6 + 3*X^5 + 20*X^4 + 6*X^2 + 10*X + 5) :=
  sq_step (by norm_num) pElevenB4s20 ⟨
    12*X^9 + 19*X^8 + 22*X^7 + 7*X^6 + X^5 + X^4 + 3*X^3 + 6*X^2 + 16*X + 7,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s22 : XPow fElevenB4 110921
    (21*X^10 + 2*X^9 + 13*X^8 + 20*X^7 + 13*X^6 + 15*X^5 + 11*X^4 + 12*X^3 + 13*X^2 + 10*X + 7) :=
  mul_step (by norm_num) pElevenB4s21 pElevenB41 ⟨
    14,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s23 : XPow fElevenB4 221842
    (6*X^10 + 10*X^9 + 11*X^8 + 19*X^7 + 21*X^6 + 4*X^5 + 12*X^4 + 2*X^2 + 18*X) :=
  sq_step (by norm_num) pElevenB4s22 ⟨
    4*X^9 + X^8 + 17*X^6 + 10*X^5 + 18*X^4 + 10*X^3 + 17*X^2 + 10*X + 17,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s24 : XPow fElevenB4 221843
    (12*X^10 + 2*X^9 + 14*X^8 + 15*X^7 + 5*X^6 + 8*X^4 + 21*X^3 + 16*X^2 + 12*X + 3) :=
  mul_step (by norm_num) pElevenB4s23 pElevenB41 ⟨
    6,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s25 : XPow fElevenB4 443686
    (11*X^10 + 21*X^9 + 21*X^6 + 6*X^5 + 22*X^4 + 6*X^3 + 13*X^2 + 2*X + 11) :=
  sq_step (by norm_num) pElevenB4s24 ⟨
    6*X^9 + 4*X^8 + 18*X^7 + 20*X^6 + 9*X^5 + 4*X^4 + 12*X^3 + 4*X^2 + 5*X + 4,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s26 : XPow fElevenB4 887372
    (X^10 + 18*X^9 + 21*X^8 + 13*X^7 + 16*X^6 + 19*X^5 + 14*X^4 + 3*X^3 + 9*X^2 + 13*X + 4) :=
  sq_step (by norm_num) pElevenB4s25 ⟨
    6*X^9 + 4*X^8 + 4*X^7 + 21*X^6 + 9*X^5 + 17*X^4 + 13*X^3 + 18*X^2 + 19,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s27 : XPow fElevenB4 887373
    (3*X^10 + 8*X^9 + 16*X^8 + 15*X^7 + 12*X^5 + 12*X^4 + 16*X^3 + 5*X^2 + 6*X + 12) :=
  mul_step (by norm_num) pElevenB4s26 pElevenB41 ⟨
    1,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s28 : XPow fElevenB4 1774746
    (6*X^10 + X^9 + 12*X^8 + 6*X^7 + 3*X^6 + 22*X^5 + 2*X^4 + 11*X^3 + 9*X^2 + 7*X + 12) :=
  sq_step (by norm_num) pElevenB4s27 ⟨
    9*X^9 + 5*X^8 + 14*X^7 + 6*X^6 + 18*X^4 + 18*X^3 + 13*X^2 + 12,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s29 : XPow fElevenB4 3549492
    (20*X^10 + 20*X^9 + 7*X^8 + 18*X^7 + 7*X^6 + 15*X^5 + 13*X^4 + 9*X^3 + 12*X^2 + 7*X + 9) :=
  sq_step (by norm_num) pElevenB4s28 ⟨
    13*X^9 + X^8 + 7*X^7 + 17*X^6 + 20*X^5 + 11*X^4 + 3*X^3 + 8*X^2 + 22*X + 6,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s30 : XPow fElevenB4 7098984
    (15*X^10 + 14*X^9 + 22*X^8 + 18*X^7 + 10*X^6 + 15*X^4 + 14*X^3 + 20*X^2 + 12) :=
  sq_step (by norm_num) pElevenB4s29 ⟨
    9*X^9 + 21*X^8 + 18*X^7 + X^6 + 3*X^5 + 16*X^4 + 3*X^3 + 12*X^2 + X,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s31 : XPow fElevenB4 7098985
    (19*X^10 + 11*X^9 + 17*X^8 + 18*X^7 + 14*X^6 + 8*X^5 + 11*X^4 + 10*X^3 + 18*X^2 + 19*X + 19) :=
  mul_step (by norm_num) pElevenB4s30 pElevenB41 ⟨
    15,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s32 : XPow fElevenB4 14197970
    (11*X^10 + 14*X^9 + 10*X^8 + 3*X^7 + 20*X^6 + 12*X^5 + 9*X^4 + 13*X^2 + 5*X + 13) :=
  sq_step (by norm_num) pElevenB4s31 ⟨
    16*X^9 + 17*X^8 + 5*X^7 + 5*X^6 + 8*X^5 + 20*X^4 + X^3 + 7*X^2 + 16*X + 17,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s33 : XPow fElevenB4 14197971
    (10*X^10 + 5*X^9 + 13*X^8 + 9*X^7 + 10*X^6 + 10*X^5 + 7*X^4 + 21*X^3 + 9*X^2 + 12*X + 17) :=
  mul_step (by norm_num) pElevenB4s32 pElevenB41 ⟨
    11,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s34 : XPow fElevenB4 28395942
    (9*X^10 + 12*X^9 + 2*X^8 + 18*X^7 + 2*X^6 + 15*X^5 + 21*X^4 + X^3 + 17*X^2 + 12*X + 21) :=
  sq_step (by norm_num) pElevenB4s33 ⟨
    8*X^9 + 3*X^8 + 21*X^7 + 3*X^6 + 4*X^5 + 21*X^4 + 14*X^3 + 8*X^2 + 18*X + 16,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s35 : XPow fElevenB4 28395943
    (15*X^10 + 22*X^8 + 16*X^7 + 5*X^6 + 3*X^5 + 13*X^4 + 11*X^3 + 9*X^2 + 16*X + 16) :=
  mul_step (by norm_num) pElevenB4s34 pElevenB41 ⟨
    9,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s36 : XPow fElevenB4 56791886
    (11*X^10 + 16*X^9 + 11*X^8 + 21*X^7 + 2*X^6 + 16*X^5 + 21*X^4 + 6*X^3 + 10*X^2 + 19*X + 18) :=
  sq_step (by norm_num) pElevenB4s35 ⟨
    18*X^9 + 6*X^8 + 14*X^7 + 16*X^6 + 5*X^5 + 21*X^4 + 2*X^3 + 18*X^2 + 21*X + 7,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s37 : XPow fElevenB4 56791887
    (12*X^10 + 6*X^9 + 8*X^8 + 14*X^7 + 14*X^6 + 22*X^5 + 13*X^4 + 18*X^3 + 17*X + 17) :=
  mul_step (by norm_num) pElevenB4s36 pElevenB41 ⟨
    11,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s38 : XPow fElevenB4 113583774
    (16*X^10 + 18*X^9 + 9*X^8 + 21*X^7 + 3*X^6 + 12*X^4 + 18*X^3 + 7*X^2 + 20*X + 18) :=
  sq_step (by norm_num) pElevenB4s37 ⟨
    6*X^9 + 8*X^8 + 7*X^7 + 11*X^6 + 8*X^5 + 4*X^4 + 4*X^3 + 11*X^2 + 17*X + 10,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s39 : XPow fElevenB4 227167548
    (22*X^10 + 15*X^9 + 17*X^8 + 19*X^7 + 7*X^6 + 2*X^5 + 3*X^4 + 19*X^2 + 16*X + 10) :=
  sq_step (by norm_num) pElevenB4s38 ⟨
    3*X^9 + 2*X^8 + 14*X^7 + 10*X^6 + 6*X^5 + 19*X^4 + 5*X^3 + 2*X^2 + 16,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s40 : XPow fElevenB4 454335096
    (12*X^10 + X^9 + 15*X^8 + 7*X^7 + 10*X^6 + 5*X^5 + 8*X^4 + 20*X^3 + 21*X^2 + 11) :=
  sq_step (by norm_num) pElevenB4s39 ⟨
    X^9 + X^8 + 2*X^7 + 18*X^6 + 22*X^5 + 21*X^4 + 14*X^3 + 4*X^2 + 3*X + 6,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s41 : XPow fElevenB4 454335097
    (5*X^10 + 20*X^9 + 20*X^8 + 21*X^7 + 7*X^6 + 7*X^5 + 13*X^4 + 13*X^3 + 19*X^2 + 12*X + 6) :=
  mul_step (by norm_num) pElevenB4s40 pElevenB41 ⟨
    12,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s42 : XPow fElevenB4 908670194
    (2*X^10 + 22*X^9 + 20*X^8 + 20*X^7 + 16*X^6 + 16*X^5 + 8*X^4 + 17*X^3 + 9*X^2 + 3) :=
  sq_step (by norm_num) pElevenB4s41 ⟨
    2*X^9 + 9*X^8 + 2*X^7 + 18*X^6 + 4*X^5 + 4*X^4 + 22*X^3 + 16*X^2 + 22*X + 3,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s43 : XPow fElevenB4 1817340388
    (12*X^10 + X^9 + 3*X^8 + 6*X^7 + 18*X^6 + X^5 + 19*X^4 + 9*X^3 + 4*X^2 + 20*X + 21) :=
  sq_step (by norm_num) pElevenB4s42 ⟨
    4*X^9 + 5*X^8 + 10*X^6 + 9*X^5 + 3*X^4 + 2*X^2 + 13*X + 1,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s44 : XPow fElevenB4 1817340389
    (5*X^10 + 8*X^9 + 19*X^8 + 6*X^7 + 3*X^6 + 18*X^5 + 2*X^4 + 19*X^3 + 16*X^2 + 22*X + 6) :=
  mul_step (by norm_num) pElevenB4s43 pElevenB41 ⟨
    12,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s45 : XPow fElevenB4 3634680778
    (18*X^10 + 8*X^9 + 19*X^8 + 10*X^7 + 21*X^6 + 10*X^5 + 18*X^3 + 15*X^2 + 2*X + 6) :=
  sq_step (by norm_num) pElevenB4s44 ⟨
    2*X^9 + 4*X^8 + 7*X^7 + 6*X^6 + 17*X^5 + 10*X^4 + 18*X^3 + 4*X^2 + 15*X + 9,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s46 : XPow fElevenB4 7269361556
    (6*X^10 + 9*X^9 + 2*X^8 + 3*X^7 + 3*X^6 + 20*X^5 + 15*X^4 + 3*X^3 + 10*X^2 + 21*X + 5) :=
  sq_step (by norm_num) pElevenB4s45 ⟨
    2*X^9 + 5*X^8 + 3*X^7 + 8*X^6 + 4*X^5 + 4*X^4 + 17*X^3 + 15*X^2 + 12*X + 7,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s47 : XPow fElevenB4 14538723112
    (11*X^10 + 3*X^9 + 9*X^8 + 19*X^7 + 12*X^6 + 22*X^5 + X^4 + 15*X^3 + 17*X + 8) :=
  sq_step (by norm_num) pElevenB4s46 ⟨
    13*X^9 + 5*X^8 + 22*X^7 + 15*X^6 + 22*X^5 + 9*X^4 + 19*X^3 + 18*X^2 + 3*X + 12,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s48 : XPow fElevenB4 29077446224
    (19*X^10 + 16*X^9 + 7*X^8 + 19*X^7 + 13*X^6 + 9*X^4 + 2*X^3 + 2*X^2 + 19*X + 1) :=
  sq_step (by norm_num) pElevenB4s47 ⟨
    6*X^9 + 22*X^8 + 6*X^7 + 22*X^6 + 19*X^5 + 2*X^4 + 15*X^3 + 17*X^2 + 21*X + 12,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s49 : XPow fElevenB4 29077446225
    (7*X^10 + 13*X^9 + 7*X^8 + 17*X^7 + 7*X^6 + 17*X^5 + 12*X^4 + 20*X^3 + 5*X^2 + 16*X + 21) :=
  mul_step (by norm_num) pElevenB4s48 pElevenB41 ⟨
    19,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s50 : XPow fElevenB4 58154892450
    (9*X^10 + 2*X^9 + 19*X^8 + 20*X^7 + 12*X^6 + 19*X^5 + 11*X^4 + 7*X^3 + 12*X^2 + 22) :=
  sq_step (by norm_num) pElevenB4s49 ⟨
    3*X^9 + 22*X^8 + 13*X^7 + 17*X^6 + 21*X^5 + 13*X^4 + 5*X^3 + 8*X^2 + 7*X + 13,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s51 : XPow fElevenB4 116309784900
    (X^10 + 13*X^9 + 19*X^8 + 2*X^7 + 4*X^6 + 21*X^5 + 10*X^4 + 8*X^3 + 20*X^2 + 8*X + 17) :=
  sq_step (by norm_num) pElevenB4s50 ⟨
    12*X^9 + 17*X^8 + 4*X^7 + 7*X^6 + 10*X^5 + 9*X^4 + 6*X^3 + 13*X^2 + 3*X + 9,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s52 : XPow fElevenB4 116309784901
    (21*X^10 + 6*X^9 + 5*X^8 + 3*X^7 + 2*X^6 + 8*X^5 + 17*X^4 + 4*X^3 + 19*X + 12) :=
  mul_step (by norm_num) pElevenB4s51 pElevenB41 ⟨
    1,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s53 : XPow fElevenB4 232619569802
    (4*X^10 + 5*X^9 + 19*X^8 + 20*X^7 + 14*X^6 + 16*X^5 + 7*X^4 + 3*X^3 + 9*X^2 + 6*X + 19) :=
  sq_step (by norm_num) pElevenB4s52 ⟨
    4*X^9 + 8*X^8 + 5*X^7 + 19*X^6 + 22*X^5 + 20*X^4 + 7*X^3 + 2*X^2 + 8*X + 3,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s54 : XPow fElevenB4 232619569803
    (14*X^10 + 13*X^9 + 9*X^8 + 10*X^7 + 9*X^6 + 22*X^5 + 16*X^4 + 14*X^3 + 20*X^2 + 4*X + 2) :=
  mul_step (by norm_num) pElevenB4s53 pElevenB41 ⟨
    4,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s55 : XPow fElevenB4 465239139606
    (16*X^10 + X^9 + 5*X^8 + 3*X^7 + 17*X^6 + 18*X^5 + 9*X^4 + 8*X^3 + 6*X^2 + 15*X + 19) :=
  sq_step (by norm_num) pElevenB4s54 ⟨
    12*X^9 + 12*X^7 + 2*X^6 + 4*X^5 + 16*X^4 + 17*X^3 + 6*X^2 + 16*X + 7,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s56 : XPow fElevenB4 930478279212
    (3*X^10 + X^9 + X^8 + 19*X^7 + 19*X^6 + 12*X^5 + 15*X^4 + 2*X^3 + 20*X^2 + 15) :=
  sq_step (by norm_num) pElevenB4s55 ⟨
    3*X^9 + 10*X^8 + 18*X^7 + 14*X^6 + 20*X^5 + 7*X^4 + 12*X^3 + 19*X^2 + 18*X + 21,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s57 : XPow fElevenB4 1860956558424
    (2*X^10 + 15*X^9 + 4*X^8 + 2*X^7 + 19*X^6 + 8*X^5 + 14*X^4 + 14*X^3 + 19*X^2 + 3*X + 11) :=
  sq_step (by norm_num) pElevenB4s56 ⟨
    9*X^9 + 9*X^8 + 8*X^7 + 21*X^6 + 5*X^5 + 12*X^4 + 19*X^3 + 22*X^2 + 16*X + 9,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s58 : XPow fElevenB4 1860956558425
    (8*X^10 + X^9 + 8*X^8 + 17*X^7 + 16*X^6 + 10*X^5 + 9*X^4 + 10*X^3 + 10*X^2 + 15*X + 1) :=
  mul_step (by norm_num) pElevenB4s57 pElevenB41 ⟨
    2,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s59 : XPow fElevenB4 3721913116850
    (13*X^9 + 21*X^8 + 13*X^7 + 11*X^6 + 4*X^5 + 16*X^4 + 10*X^3 + 22*X^2 + 21*X + 2) :=
  sq_step (by norm_num) pElevenB4s58 ⟨
    18*X^9 + 22*X^8 + 2*X^7 + 3*X^6 + 9*X^5 + X^4 + 15*X^3 + 12*X^2 + 20*X + 2,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s60 : XPow fElevenB4 3721913116851
    (13*X^10 + 21*X^9 + 13*X^8 + 11*X^7 + 4*X^6 + 16*X^5 + 10*X^4 + 22*X^3 + 21*X^2 + 2*X) :=
  mul_step (by norm_num) pElevenB4s59 pElevenB41 ⟨
    0,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s61 : XPow fElevenB4 7443826233702
    (4*X^10 + 4*X^9 + 10*X^8 + 16*X^7 + 13*X^6 + 18*X^4 + X^3 + 21*X^2 + 14) :=
  sq_step (by norm_num) pElevenB4s60 ⟨
    8*X^9 + 12*X^8 + 12*X^7 + 14*X^6 + 6*X^5 + 10*X^4 + 2*X^3 + 10*X^2 + 3*X + 5,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s62 : XPow fElevenB4 14887652467404
    (13*X^10 + 22*X^9 + 17*X^8 + 16*X^7 + 7*X^6 + 15*X^5 + 9*X^4 + 22*X^3 + X^2 + 5*X + 6) :=
  sq_step (by norm_num) pElevenB4s61 ⟨
    16*X^9 + 22*X^8 + 18*X^7 + 22*X^6 + 2*X^5 + 20*X^4 + X^3 + 12*X^2 + 12*X + 11,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s63 : XPow fElevenB4 14887652467405
    (11*X^10 + 9*X^9 + 9*X^8 + 17*X^7 + 21*X^6 + 6*X^5 + X^4 + 16*X^2 + 9*X + 18) :=
  mul_step (by norm_num) pElevenB4s62 pElevenB41 ⟨
    13,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s64 : XPow fElevenB4 29775304934810
    (3*X^10 + 22*X^9 + 9*X^8 + 13*X^7 + 20*X^6 + 9*X^5 + 12*X^4 + 13*X^3 + 6*X^2 + 2*X + 22) :=
  sq_step (by norm_num) pElevenB4s63 ⟨
    6*X^9 + 16*X^8 + 7*X^7 + 11*X^6 + 14*X^5 + 9*X^4 + 6*X^3 + X^2 + X + 17,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s65 : XPow fElevenB4 59550609869620
    (21*X^10 + 3*X^9 + 8*X^8 + 5*X^6 + 12*X^5 + 13*X^4 + 7*X^3 + 10*X^2 + 13*X + 21) :=
  sq_step (by norm_num) pElevenB4s64 ⟨
    9*X^9 + 20*X^8 + 6*X^7 + 13*X^6 + 22*X^5 + 13*X^4 + 13*X^3 + 7*X^2 + 12*X + 17,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s66 : XPow fElevenB4 119101219739240
    (7*X^10 + 18*X^9 + 16*X^8 + 4*X^7 + 16*X^6 + 17*X^5 + 3*X^4 + 21*X^3 + 19*X^2 + 12) :=
  sq_step (by norm_num) pElevenB4s65 ⟨
    4*X^9 + 20*X^8 + 16*X^7 + 20*X^6 + 6*X^5 + 21*X^4 + 7*X^3 + 14*X^2 + 17*X + 16,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s67 : XPow fElevenB4 238202439478480
    (14*X^10 + 12*X^9 + 12*X^8 + 21*X^7 + 20*X^6 + 17*X^4 + 21*X^3 + 5*X^2 + 7*X + 11) :=
  sq_step (by norm_num) pElevenB4s66 ⟨
    3*X^9 + 3*X^7 + 21*X^6 + 14*X^5 + 20*X^4 + 18*X^3 + 6*X^2 + 20*X + 10,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s68 : XPow fElevenB4 238202439478481
    (9*X^10 + 14*X^9 + 17*X^8 + 6*X^7 + 10*X^6 + 12*X^5 + 9*X^4 + 11*X^3 + 10*X^2 + 16*X + 7) :=
  mul_step (by norm_num) pElevenB4s67 pElevenB41 ⟨
    14,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s69 : XPow fElevenB4 476404878956962
    (2*X^10 + 7*X^9 + 3*X^8 + 17*X^7 + 2*X^6 + 15*X^5 + 4*X^4 + 5*X^3 + 9*X^2 + 16*X + 19) :=
  sq_step (by norm_num) pElevenB4s68 ⟨
    12*X^9 + 3*X^8 + 2*X^7 + 22*X^6 + 2*X^5 + 21*X^4 + 10*X^3 + 5*X^2 + 8*X + 9,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s70 : XPow fElevenB4 476404878956963
    (1) :=
  mul_step (by norm_num) pElevenB4s69 pElevenB41 ⟨
    2,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s71 : XPow fElevenB4 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenB4s70 ⟨
    0,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB4s72 : XPow fElevenB4 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenB4s71 pElevenB41 ⟨
    0,
    by simp only [fElevenB4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 5: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenB51 : XPow fElevenB5 1 X := xpow_one _

theorem pElevenB5s0 : XPow fElevenB5 2
    (X^2) :=
  sq_step (by norm_num) pElevenB51 ⟨
    0,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s1 : XPow fElevenB5 3
    (X^3) :=
  mul_step (by norm_num) pElevenB5s0 pElevenB51 ⟨
    0,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s2 : XPow fElevenB5 6
    (X^6) :=
  sq_step (by norm_num) pElevenB5s1 ⟨
    0,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s3 : XPow fElevenB5 12
    (22*X^10 + X^9 + 11*X^8 + 5*X^7 + 10*X^6 + 2*X^5 + 12*X^4 + 3*X^3 + 5*X^2 + 9*X + 7) :=
  sq_step (by norm_num) pElevenB5s2 ⟨
    X + 1,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s4 : XPow fElevenB5 13
    (13*X^9 + 2*X^8 + 2*X^7 + 5*X^6 + 22*X^5 + 14*X^4 + 5*X^3 + 6*X^2 + 5*X + 16) :=
  mul_step (by norm_num) pElevenB5s3 pElevenB51 ⟨
    22,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s5 : XPow fElevenB5 26
    (2*X^10 + 19*X^9 + 7*X^8 + 8*X^6 + 4*X^5 + 2*X^4 + 18*X^3 + 22*X^2 + 8*X + 10) :=
  sq_step (by norm_num) pElevenB5s4 ⟨
    8*X^7 + 14*X^6 + 8*X^5 + 4*X^4 + X^2 + X + 1,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s6 : XPow fElevenB5 27
    (21*X^10 + 3*X^9 + 6*X^8 + X^7 + 21*X^6 + 5*X^5 + 19*X^4 + 22*X^3 + 14*X^2 + 14*X + 14) :=
  mul_step (by norm_num) pElevenB5s5 pElevenB51 ⟨
    2,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s7 : XPow fElevenB5 54
    (2*X^10 + 10*X^9 + 20*X^8 + 3*X^7 + 15*X^6 + 15*X^5 + 3*X^4 + 14*X^3 + 8*X^2 + 10*X + 14) :=
  sq_step (by norm_num) pElevenB5s6 ⟨
    4*X^9 + 15*X^8 + 15*X^7 + 6*X^6 + 11*X^5 + 17*X^4 + 2*X^3 + 7*X^2 + 12*X + 20,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s8 : XPow fElevenB5 108
    (9*X^10 + X^9 + 17*X^8 + 2*X^7 + 11*X^6 + 16*X^5 + 14*X^3 + 7*X^2 + 13*X + 6) :=
  sq_step (by norm_num) pElevenB5s7 ⟨
    4*X^9 + 21*X^8 + 9*X^7 + 22*X^5 + 18*X^4 + 13*X^3 + 16*X^2 + 2*X + 9,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s9 : XPow fElevenB5 216
    (10*X^10 + 9*X^9 + 5*X^8 + 15*X^7 + 22*X^6 + 15*X^5 + 3*X^4 + 21*X^3 + 14*X^2 + 2*X + 5) :=
  sq_step (by norm_num) pElevenB5s8 ⟨
    12*X^9 + 7*X^8 + 14*X^7 + 14*X^6 + 19*X^5 + 17*X^4 + 11*X^3 + 6*X^2 + 14*X + 12,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s10 : XPow fElevenB5 432
    (9*X^10 + 7*X^9 + 8*X^8 + 19*X^7 + 12*X^6 + 20*X^5 + X^4 + 20*X^3 + 6*X^2 + 5) :=
  sq_step (by norm_num) pElevenB5s9 ⟨
    8*X^9 + 4*X^8 + 8*X^7 + 13*X^5 + 17*X^4 + 2*X^3 + 12*X^2 + 5*X + 7,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s11 : XPow fElevenB5 433
    (16*X^10 + 13*X^9 + 15*X^7 + 16*X^6 + 3*X^5 + 13*X^4 + 6*X^3 + 4*X^2 + 17) :=
  mul_step (by norm_num) pElevenB5s10 pElevenB51 ⟨
    9,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s12 : XPow fElevenB5 866
    (22*X^10 + 22*X^9 + 8*X^8 + X^7 + 17*X^6 + 17*X^5 + 19*X^4 + 17*X^3 + 9*X^2 + 12*X + 14) :=
  sq_step (by norm_num) pElevenB5s11 ⟨
    3*X^9 + 5*X^8 + 7*X^7 + 3*X^6 + 10*X^5 + 16*X^4 + 22*X^3 + 7*X^2 + 12*X + 10,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s13 : XPow fElevenB5 1732
    (8*X^10 + 5*X^9 + 17*X^8 + 17*X^7 + X^6 + 18*X^5 + 10*X^4 + X^3 + 13*X^2 + 14*X + 3) :=
  sq_step (by norm_num) pElevenB5s12 ⟨
    X^9 + 3*X^8 + 9*X^7 + 11*X^6 + 15*X^5 + 12*X^4 + 16*X^3 + 15*X^2 + 6*X + 2,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s14 : XPow fElevenB5 1733
    (13*X^10 + X^9 + 18*X^8 + 19*X^7 + 17*X^6 + 22*X^5 + 5*X^4 + 13*X^3 + 15*X^2 + 19*X + 10) :=
  mul_step (by norm_num) pElevenB5s13 pElevenB51 ⟨
    8,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s15 : XPow fElevenB5 3466
    (4*X^10 + 13*X^7 + X^6 + 14*X^5 + 4*X^4 + 6*X^3 + 15*X^2 + 19*X + 22) :=
  sq_step (by norm_num) pElevenB5s14 ⟨
    8*X^9 + 11*X^8 + 4*X^7 + 7*X^6 + 3*X^5 + 21*X^4 + 21*X^3 + 10*X^2 + 7*X + 2,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s16 : XPow fElevenB5 6932
    (4*X^10 + 20*X^9 + 8*X^8 + 11*X^7 + 3*X^6 + 19*X^5 + 11*X^4 + 13*X^3 + 14*X^2 + 3*X + 11) :=
  sq_step (by norm_num) pElevenB5s15 ⟨
    16*X^9 + 16*X^8 + 7*X^7 + 12*X^6 + 21*X^5 + 3*X^4 + 8*X^2 + 20*X + 8,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s17 : XPow fElevenB5 13864
    (8*X^10 + 17*X^9 + 7*X^8 + 8*X^7 + 4*X^6 + 22*X^5 + 12*X^4 + 13*X^3 + 3*X^2 + 7*X + 21) :=
  sq_step (by norm_num) pElevenB5s16 ⟨
    16*X^9 + 15*X^8 + 10*X^7 + 22*X^6 + 13*X^5 + 13*X^4 + 2*X^3 + 13*X^2 + 21*X + 12,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s18 : XPow fElevenB5 13865
    (2*X^10 + 14*X^9 + 9*X^8 + 22*X^7 + 21*X^6 + X^5 + 17*X^4 + 3*X^3 + 8*X^2 + 14*X + 10) :=
  mul_step (by norm_num) pElevenB5s17 pElevenB51 ⟨
    8,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s19 : XPow fElevenB5 27730
    (17*X^10 + 22*X^9 + 5*X^8 + 17*X^7 + 8*X^6 + 9*X^5 + 2*X^4 + 21*X^3 + 13*X^2 + 22*X + 16) :=
  sq_step (by norm_num) pElevenB5s18 ⟨
    4*X^9 + 14*X^8 + 8*X^7 + 10*X^6 + 21*X^5 + 9*X^4 + 17*X^3 + 7*X^2 + 6*X + 11,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s20 : XPow fElevenB5 55460
    (18*X^10 + 10*X^9 + 3*X^8 + 17*X^7 + 22*X^6 + 8*X^5 + 20*X^3 + 19*X^2 + 22*X + 2) :=
  sq_step (by norm_num) pElevenB5s19 ⟨
    13*X^9 + 2*X^8 + 9*X^7 + 14*X^6 + X^5 + 4*X^3 + 12*X^2 + 4*X + 13,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s21 : XPow fElevenB5 110920
    (13*X^10 + 20*X^9 + 7*X^8 + 7*X^7 + 17*X^6 + 19*X^5 + X^4 + 21*X^3 + 22*X^2 + 19*X + 19) :=
  sq_step (by norm_num) pElevenB5s20 ⟨
    2*X^9 + 17*X^8 + 14*X^7 + 14*X^6 + 21*X^5 + 6*X^4 + 7*X^3 + 3*X^2 + 13*X + 12,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s22 : XPow fElevenB5 110921
    (10*X^10 + 4*X^9 + 6*X^7 + 3*X^6 + 9*X^5 + 16*X^4 + 22*X^3 + 12*X^2 + 22*X + 22) :=
  mul_step (by norm_num) pElevenB5s21 pElevenB51 ⟨
    13,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s23 : XPow fElevenB5 221842
    (18*X^10 + 17*X^9 + X^8 + 5*X^7 + 16*X^6 + 21*X^5 + 13*X^4 + 17*X^3 + 4*X^2 + 11*X + 7) :=
  sq_step (by norm_num) pElevenB5s22 ⟨
    8*X^9 + 19*X^8 + 19*X^7 + 10*X^6 + 17*X^5 + 18*X^4 + 20*X^3 + 16*X^2 + 17*X + 14,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s24 : XPow fElevenB5 221843
    (12*X^10 + 11*X^9 + 13*X^8 + 22*X^7 + 13*X^6 + 17*X^5 + 3*X^4 + 4*X^3 + 19*X^2 + 20*X + 11) :=
  mul_step (by norm_num) pElevenB5s23 pElevenB51 ⟨
    18,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s25 : XPow fElevenB5 443686
    (2*X^10 + 7*X^9 + 5*X^8 + 4*X^7 + 8*X^6 + 5*X^5 + 12*X^4 + 2*X^3 + X^2 + 7*X + 16) :=
  sq_step (by norm_num) pElevenB5s24 ⟨
    6*X^9 + 17*X^8 + X^7 + 17*X^6 + 21*X^5 + 17*X^4 + 18*X^3 + 16*X^2 + 18*X + 8,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s26 : XPow fElevenB5 887372
    (2*X^10 + 7*X^9 + 6*X^8 + 15*X^7 + X^6 + 3*X^4 + 21*X^3 + X^2 + 12*X + 1) :=
  sq_step (by norm_num) pElevenB5s25 ⟨
    4*X^9 + 9*X^8 + X^7 + 12*X^6 + 21*X^5 + 2*X^4 + 13*X^3 + 22*X^2 + 5*X + 3,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s27 : XPow fElevenB5 887373
    (9*X^10 + 2*X^9 + 21*X^8 + 17*X^7 + 17*X^6 + 6*X^5 + 22*X^4 + X^3 + 18*X^2 + 5*X + 14) :=
  mul_step (by norm_num) pElevenB5s26 pElevenB51 ⟨
    2,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s28 : XPow fElevenB5 1774746
    (9*X^10 + X^9 + 20*X^8 + 17*X^7 + 3*X^6 + X^5 + X^4 + 12*X^3 + 21*X^2 + X + 11) :=
  sq_step (by norm_num) pElevenB5s27 ⟨
    12*X^9 + 2*X^8 + 15*X^7 + 13*X^5 + 8*X^4 + 19*X^3 + 22*X^2 + 6*X + 13,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s29 : XPow fElevenB5 3549492
    (X^10 + 12*X^8 + 10*X^7 + 21*X^6 + 9*X^5 + 7*X^4 + X^3 + 11*X^2 + 10*X + 18) :=
  sq_step (by norm_num) pElevenB5s28 ⟨
    12*X^9 + 7*X^8 + 22*X^7 + 22*X^6 + 8*X^5 + 18*X^4 + 3*X^3 + 6*X^2 + 10*X + 5,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s30 : XPow fElevenB5 7098984
    (4*X^10 + 17*X^9 + 5*X^8 + 6*X^7 + X^6 + 22*X^4 + 12*X^3 + 12*X^2 + 22*X + 3) :=
  sq_step (by norm_num) pElevenB5s29 ⟨
    X^9 + X^8 + 21*X^6 + 11*X^5 + 2*X^4 + 4*X^3 + 13*X^2 + 8*X + 10,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s31 : XPow fElevenB5 7098985
    (21*X^10 + 20*X^9 + 18*X^8 + 10*X^7 + 11*X^6 + 5*X^5 + 14*X^4 + 12*X^3 + 11*X^2 + 11*X + 5) :=
  mul_step (by norm_num) pElevenB5s30 pElevenB51 ⟨
    4,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s32 : XPow fElevenB5 14197970
    (3*X^9 + 6*X^8 + 4*X^7 + X^6 + 16*X^5 + 7*X^4 + 21*X^3 + 11*X^2 + 11*X + 19) :=
  sq_step (by norm_num) pElevenB5s31 ⟨
    4*X^9 + 16*X^8 + 14*X^7 + 7*X^6 + 3*X^5 + 7*X^4 + 19*X^3 + 3*X + 9,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s33 : XPow fElevenB5 14197971
    (3*X^10 + 6*X^9 + 4*X^8 + X^7 + 16*X^6 + 7*X^5 + 21*X^4 + 11*X^3 + 11*X^2 + 19*X) :=
  mul_step (by norm_num) pElevenB5s32 pElevenB51 ⟨
    0,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s34 : XPow fElevenB5 28395942
    (14*X^10 + 21*X^9 + 20*X^8 + 2*X^6 + 22*X^5 + 12*X^4 + 12*X^3 + 10*X^2 + 17*X + 9) :=
  sq_step (by norm_num) pElevenB5s33 ⟨
    9*X^9 + 22*X^8 + 18*X^7 + 9*X^6 + 5*X^5 + 18*X^4 + 17*X^3 + 9*X^2 + 3*X + 21,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s35 : XPow fElevenB5 28395943
    (12*X^10 + 15*X^9 + 19*X^8 + 22*X^7 + 3*X^6 + 10*X^5 + 19*X^4 + 10*X^3 + 13*X^2 + 14*X + 6) :=
  mul_step (by norm_num) pElevenB5s34 pElevenB51 ⟨
    14,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s36 : XPow fElevenB5 56791886
    (10*X^10 + 19*X^9 + 22*X^8 + 14*X^7 + 7*X^6 + 11*X^5 + 2*X^4 + 14*X^3 + 16*X^2 + 6*X + 19) :=
  sq_step (by norm_num) pElevenB5s35 ⟨
    6*X^9 + 21*X^8 + 16*X^6 + X^5 + 20*X^4 + 9*X^3 + 19*X^2 + 9*X + 14,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s37 : XPow fElevenB5 56791887
    (6*X^10 + 2*X^9 + 21*X^8 + 18*X^7 + 4*X^6 + 17*X^5 + 19*X^4 + 16*X^3 + 13*X^2 + 16*X + 1) :=
  mul_step (by norm_num) pElevenB5s36 pElevenB51 ⟨
    10,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s38 : XPow fElevenB5 113583774
    (20*X^10 + 18*X^9 + 10*X^8 + 11*X^7 + 20*X^5 + 6*X^4 + X^2 + 17*X + 5) :=
  sq_step (by norm_num) pElevenB5s37 ⟨
    13*X^9 + 14*X^8 + 14*X^7 + 3*X^6 + 15*X^5 + 19*X^4 + 13*X^3 + 17*X^2 + 16*X + 17,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s39 : XPow fElevenB5 227167548
    (19*X^10 + 22*X^8 + 16*X^7 + 4*X^6 + 14*X^5 + 12*X^4 + X^3 + 16*X^2 + 8*X + 7) :=
  sq_step (by norm_num) pElevenB5s38 ⟨
    9*X^9 + 16*X^8 + 9*X^7 + 22*X^6 + 22*X^5 + 22*X^4 + X^3 + 2*X + 4,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s40 : XPow fElevenB5 454335096
    (15*X^10 + 20*X^9 + 4*X^8 + 17*X^7 + 13*X^6 + 22*X^5 + 19*X^4 + 5*X^3 + 22*X^2 + 21*X + 14) :=
  sq_step (by norm_num) pElevenB5s39 ⟨
    16*X^9 + 16*X^8 + 15*X^7 + 18*X^6 + 18*X^5 + 9*X^4 + 22*X^3 + 5*X^2 + 18*X + 18,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s41 : XPow fElevenB5 454335097
    (12*X^10 + 20*X^9 + 16*X^8 + 18*X^7 + 7*X^5 + X^4 + 22*X^3 + 20*X^2 + 21*X + 13) :=
  mul_step (by norm_num) pElevenB5s40 pElevenB51 ⟨
    15,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s42 : XPow fElevenB5 908670194
    (11*X^10 + 17*X^9 + 17*X^8 + 17*X^7 + 13*X^6 + 15*X^5 + 22*X^4 + 13*X^3 + 13*X^2 + 9*X + 18) :=
  sq_step (by norm_num) pElevenB5s41 ⟨
    6*X^9 + 3*X^8 + 16*X^7 + 19*X^6 + 8*X^5 + 9*X^4 + X^3 + 2*X^2 + 13*X + 8,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s43 : XPow fElevenB5 1817340388
    (22*X^10 + 5*X^9 + 20*X^8 + 11*X^7 + 2*X^6 + 20*X^5 + X^4 + X^3 + 3*X^2 + 8*X + 20) :=
  sq_step (by norm_num) pElevenB5s42 ⟨
    6*X^9 + 12*X^8 + 19*X^7 + 22*X^6 + 2*X^5 + 17*X^4 + 20*X^3 + 2*X^2 + 2*X + 19,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s44 : XPow fElevenB5 1817340389
    (4*X^10 + 22*X^9 + 8*X^8 + 17*X^7 + 11*X^5 + 12*X^4 + 3*X^3 + 5*X^2 + 18*X + 16) :=
  mul_step (by norm_num) pElevenB5s43 pElevenB51 ⟨
    22,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s45 : XPow fElevenB5 3634680778
    (3*X^10 + 13*X^9 + 4*X^8 + 19*X^7 + 8*X^6 + 5*X^5 + 5*X^4 + 19*X^3 + 14*X^2 + 1) :=
  sq_step (by norm_num) pElevenB5s44 ⟨
    16*X^9 + 8*X^8 + 18*X^7 + 9*X^6 + 17*X^5 + 15*X^4 + 9*X^3 + 14*X^2 + 22*X + 3,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s46 : XPow fElevenB5 7269361556
    (20*X^10 + 21*X^8 + 14*X^7 + 20*X^6 + 17*X^5 + 4*X^4 + 14*X^3 + 5*X^2 + 18*X + 8) :=
  sq_step (by norm_num) pElevenB5s45 ⟨
    9*X^9 + 18*X^8 + 9*X^7 + 11*X^6 + 10*X^5 + 16*X^4 + 13*X^3 + 13*X^2 + 22*X + 1,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s47 : XPow fElevenB5 14538723112
    (2*X^10 + 8*X^8 + 19*X^7 + 2*X^6 + 7*X^5 + X^4 + 12*X^3 + 16*X^2 + 22*X + 6) :=
  sq_step (by norm_num) pElevenB5s46 ⟨
    9*X^9 + 9*X^8 + 3*X^7 + 20*X^6 + 20*X^5 + 14*X^4 + 10*X^3 + 21*X^2 + 16*X + 18,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s48 : XPow fElevenB5 29077446224
    (4*X^10 + 9*X^9 + 3*X^8 + 16*X^7 + 15*X^6 + 5*X^5 + X^4 + 3*X^3 + 5*X^2 + 15*X + 3) :=
  sq_step (by norm_num) pElevenB5s47 ⟨
    4*X^9 + 4*X^8 + 5*X^7 + 16*X^6 + 7*X^5 + 20*X^4 + 2*X^3 + 18*X^2 + 16*X + 15,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s49 : XPow fElevenB5 29077446225
    (13*X^10 + 18*X^9 + 5*X^8 + X^7 + 16*X^6 + 7*X^5 + 5*X^4 + 5*X^3 + 4*X^2 + 11*X + 5) :=
  mul_step (by norm_num) pElevenB5s48 pElevenB51 ⟨
    4,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s50 : XPow fElevenB5 58154892450
    (14*X^10 + 12*X^9 + 20*X^8 + 12*X^7 + 12*X^6 + 19*X^5 + 3*X^4 + 11*X^3 + 8*X^2 + 22*X + 13) :=
  sq_step (by norm_num) pElevenB5s49 ⟨
    8*X^9 + 16*X^8 + 17*X^7 + 8*X^6 + 11*X^5 + 21*X^4 + 22*X^3 + 6*X^2 + 2*X + 18,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s51 : XPow fElevenB5 116309784900
    (5*X^10 + 2*X^9 + 22*X^8 + 5*X^7 + 14*X^6 + 18*X^5 + 22*X^3 + 19*X^2 + 4*X + 7) :=
  sq_step (by norm_num) pElevenB5s50 ⟨
    12*X^9 + 3*X^8 + 16*X^7 + 11*X^6 + 4*X^5 + 7*X^4 + 22*X^3 + 15*X^2 + 17*X + 13,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s52 : XPow fElevenB5 116309784901
    (7*X^10 + 12*X^9 + 20*X^8 + 8*X^7 + 3*X^6 + 19*X^5 + 13*X^4 + 19*X^3 + 19*X^2 + 17*X + 12) :=
  mul_step (by norm_num) pElevenB5s51 pElevenB51 ⟨
    5,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s53 : XPow fElevenB5 232619569802
    (X^10 + 7*X^9 + 20*X^8 + 14*X^7 + 21*X^6 + 9*X^5 + 10*X^4 + 13*X^2 + 20*X) :=
  sq_step (by norm_num) pElevenB5s52 ⟨
    3*X^9 + 10*X^8 + 14*X^7 + 20*X^6 + 13*X^5 + 8*X^4 + 19*X^3 + 10*X^2 + 11*X + 9,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s54 : XPow fElevenB5 232619569803
    (8*X^10 + 18*X^9 + 17*X^8 + 6*X^7 + 6*X^6 + 12*X^4 + 13*X^3 + 2*X + 7) :=
  mul_step (by norm_num) pElevenB5s53 pElevenB51 ⟨
    1,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s55 : XPow fElevenB5 465239139606
    (14*X^10 + X^9 + 6*X^8 + 8*X^7 + 8*X^6 + 7*X^5 + 17*X^4 + 10*X^3 + 16*X^2 + 7*X + 5) :=
  sq_step (by norm_num) pElevenB5s54 ⟨
    18*X^9 + 7*X^8 + 15*X^7 + 4*X^6 + 4*X^5 + 3*X^4 + 13*X^3 + 13*X^2 + 11*X + 20,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s56 : XPow fElevenB5 930478279212
    (8*X^10 + 20*X^9 + 2*X^8 + 20*X^7 + 16*X^6 + 4*X^5 + X^4 + 22*X^3 + 2*X^2 + 21*X + 18) :=
  sq_step (by norm_num) pElevenB5s55 ⟨
    12*X^9 + 17*X^8 + X^7 + 9*X^6 + 16*X^5 + 18*X^4 + 17*X^3 + 13*X + 22,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s57 : XPow fElevenB5 1860956558424
    (2*X^10 + 16*X^9 + 12*X^8 + 3*X^7 + 8*X^5 + 7*X^4 + 7*X^3 + 7*X^2 + 8*X + 6) :=
  sq_step (by norm_num) pElevenB5s56 ⟨
    18*X^9 + 16*X^8 + 21*X^7 + 6*X^6 + 20*X^5 + 9*X^4 + 15*X^3 + 19*X^2 + 17,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s58 : XPow fElevenB5 1860956558425
    (18*X^10 + 8*X^9 + 9*X^8 + 16*X^7 + 2*X^6 + 10*X^5 + 8*X^4 + 7*X^3 + 14*X^2 + 10*X + 14) :=
  mul_step (by norm_num) pElevenB5s57 pElevenB51 ⟨
    2,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s59 : XPow fElevenB5 3721913116850
    (17*X^10 + X^9 + 14*X^8 + 16*X^7 + 21*X^6 + 8*X^5 + 2*X^4 + 5*X^3 + 9*X^2 + 15*X + 11) :=
  sq_step (by norm_num) pElevenB5s58 ⟨
    2*X^9 + 14*X^8 + 7*X^7 + 15*X^6 + 8*X^5 + 3*X^4 + 7*X^3 + 11*X^2 + 11*X + 13,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s60 : XPow fElevenB5 3721913116851
    (18*X^10 + 3*X^9 + 21*X^8 + 19*X^7 + 3*X^6 + 16*X^5 + 2*X^4 + 9*X^3 + 20*X^2 + 22*X + 4) :=
  mul_step (by norm_num) pElevenB5s59 pElevenB51 ⟨
    17,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s61 : XPow fElevenB5 7443826233702
    (12*X^10 + 14*X^9 + 3*X^8 + 8*X^7 + 22*X^6 + 5*X^5 + 16*X^4 + 12*X^3 + 8*X^2 + 7*X + 19) :=
  sq_step (by norm_num) pElevenB5s60 ⟨
    2*X^9 + 18*X^8 + 20*X^7 + 18*X^6 + 21*X^5 + 11*X^4 + 5*X^3 + 15*X^2 + 10*X + 7,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s62 : XPow fElevenB5 14887652467404
    (9*X^10 + 10*X^9 + 15*X^7 + 22*X^6 + 21*X^5 + 4*X^4 + 3*X^3 + 10*X^2 + 12*X + 17) :=
  sq_step (by norm_num) pElevenB5s61 ⟨
    6*X^9 + 20*X^8 + X^6 + 19*X^5 + 13*X^3 + 10*X^2 + 20*X + 10,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s63 : XPow fElevenB5 14887652467405
    (19*X^10 + 5*X^9 + 19*X^8 + 2*X^7 + 17*X^6 + 6*X^5 + 19*X^4 + 10*X^3 + 16*X^2 + 12*X + 17) :=
  mul_step (by norm_num) pElevenB5s62 pElevenB51 ⟨
    9,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s64 : XPow fElevenB5 29775304934810
    (7*X^10 + 9*X^9 + 15*X^8 + 4*X^7 + 19*X^6 + 5*X^5 + 14*X^4 + 6*X^3 + 8*X^2 + 9*X + 5) :=
  sq_step (by norm_num) pElevenB5s63 ⟨
    16*X^9 + 22*X^8 + X^7 + 18*X^6 + 18*X^5 + 12*X^4 + 2*X^3 + 22*X^2 + 2*X + 12,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s65 : XPow fElevenB5 59550609869620
    (8*X^10 + 8*X^9 + 15*X^8 + 19*X^7 + 9*X^6 + X^5 + 20*X^4 + 5*X^3 + 4*X^2 + 22*X + 3) :=
  sq_step (by norm_num) pElevenB5s64 ⟨
    3*X^9 + 14*X^8 + 8*X^6 + 16*X^5 + 14*X^4 + X^3 + 21*X^2 + 17*X + 10,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s66 : XPow fElevenB5 119101219739240
    (13*X^10 + 4*X^9 + 22*X^8 + 17*X^7 + 13*X^6 + 12*X^5 + 9*X^4 + X^3 + 22*X^2 + 3*X + 9) :=
  sq_step (by norm_num) pElevenB5s65 ⟨
    18*X^9 + 8*X^8 + 7*X^6 + 20*X^5 + 10*X^4 + 18*X^3 + 10*X^2 + 21*X,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s67 : XPow fElevenB5 238202439478480
    (4*X^10 + 9*X^9 + 22*X^8 + 15*X^7 + 21*X^6 + 16*X^5 + 16*X^4 + 22*X^3 + 11*X^2 + 4*X + 20) :=
  sq_step (by norm_num) pElevenB5s66 ⟨
    8*X^9 + 20*X^8 + 17*X^7 + 21*X^6 + 11*X^5 + 9*X^4 + 18*X^3 + 10*X^2 + 16*X + 11,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s68 : XPow fElevenB5 238202439478481
    (13*X^10 + 14*X^9 + 4*X^8 + 7*X^7 + 4*X^6 + 22*X^5 + X^4 + 11*X^3 + 16*X^2 + 5*X + 5) :=
  mul_step (by norm_num) pElevenB5s67 pElevenB51 ⟨
    4,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s69 : XPow fElevenB5 476404878956962
    (13*X^10 + 10*X^9 + 3*X^8 + 7*X^7 + 11*X^6 + 16*X^5 + 15*X^4 + 5*X^3 + 7*X + 20) :=
  sq_step (by norm_num) pElevenB5s68 ⟨
    8*X^9 + 4*X^8 + 12*X^7 + 2*X^4 + 16*X^3 + 3*X^2 + 18*X + 19,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s70 : XPow fElevenB5 476404878956963
    (22) :=
  mul_step (by norm_num) pElevenB5s69 pElevenB51 ⟨
    13,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s71 : XPow fElevenB5 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenB5s70 ⟨
    0,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenB5s72 : XPow fElevenB5 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenB5s71 pElevenB51 ⟨
    0,
    by simp only [fElevenB5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Pairwise coprimality of the factors, by explicit Bézout identities -/

theorem copElevenB1_2 : IsCoprime fElevenB1 fElevenB2 :=
  ⟨6*X^10 + 16*X^9 + 18*X^8 + 10*X^7 + 16*X^6 + 20*X^5 + 18*X^4 + 4*X^3 + 21*X^2 + 12*X,
   17*X^10 + 3*X^9 + 10*X^8 + 4*X^7 + 11*X^6 + X^5 + 20*X^4 + 11*X^3 + X^2 + 7*X + 12,
   by simp only [fElevenB1, fElevenB2]; ring_nf; reduce_mod_char⟩

theorem copElevenB1_3 : IsCoprime fElevenB1 fElevenB3 :=
  ⟨5*X^10 + 5*X^9 + 12*X^8 + 3*X^7 + 14*X^6 + X^5 + 6*X^4 + 2*X^3 + 2*X^2 + 17*X + 2,
   18*X^10 + 14*X^9 + 16*X^8 + 11*X^7 + 13*X^6 + 20*X^5 + 9*X^4 + 13*X^3 + 20*X^2 + 2*X + 10,
   by simp only [fElevenB1, fElevenB3]; ring_nf; reduce_mod_char⟩

theorem copElevenB1_4 : IsCoprime fElevenB1 fElevenB4 :=
  ⟨12*X^10 + 13*X^9 + 8*X^8 + 6*X^7 + 5*X^6 + 19*X^5 + 21*X^4 + 16*X^3 + 20*X^2 + 5*X + 11,
   11*X^10 + 6*X^9 + 20*X^8 + 8*X^7 + 22*X^6 + 2*X^5 + 17*X^4 + 22*X^3 + 2*X^2 + 14*X + 1,
   by simp only [fElevenB1, fElevenB4]; ring_nf; reduce_mod_char⟩

theorem copElevenB1_5 : IsCoprime fElevenB1 fElevenB5 :=
  ⟨4*X^10 + 17*X^9 + 6*X^8 + 19*X^7 + 12*X^6 + 5*X^5 + 17*X^4 + 6*X^2 + 22*X + 4,
   19*X^10 + 2*X^9 + 22*X^8 + 18*X^7 + 15*X^6 + 16*X^5 + 21*X^4 + 15*X^3 + 16*X^2 + 20*X + 8,
   by simp only [fElevenB1, fElevenB5]; ring_nf; reduce_mod_char⟩

theorem copElevenB2_3 : IsCoprime fElevenB2 fElevenB3 :=
  ⟨7*X^10 + 7*X^9 + 3*X^8 + 18*X^7 + 15*X^6 + 6*X^5 + 13*X^4 + 12*X^3 + 12*X^2 + 10*X + 12,
   16*X^10 + 12*X^9 + 2*X^8 + 19*X^7 + 12*X^6 + 15*X^5 + 2*X^4 + 3*X^3 + 10*X^2 + 9*X,
   by simp only [fElevenB2, fElevenB3]; ring_nf; reduce_mod_char⟩

theorem copElevenB2_4 : IsCoprime fElevenB2 fElevenB4 :=
  ⟨11*X^10 + 10*X^9 + 15*X^8 + 17*X^7 + 18*X^6 + 4*X^5 + 2*X^4 + 7*X^3 + 3*X^2 + 18*X + 12,
   12*X^10 + 9*X^9 + 13*X^8 + 20*X^7 + 9*X^6 + 17*X^5 + 13*X^4 + 8*X^3 + 19*X^2 + X,
   by simp only [fElevenB2, fElevenB4]; ring_nf; reduce_mod_char⟩

theorem copElevenB2_5 : IsCoprime fElevenB2 fElevenB5 :=
  ⟨12*X^10 + 5*X^9 + 18*X^8 + 11*X^7 + 13*X^6 + 15*X^5 + 5*X^4 + 18*X^2 + 20*X + 12,
   11*X^10 + 14*X^9 + 10*X^8 + 3*X^7 + 14*X^6 + 6*X^5 + 10*X^4 + 15*X^3 + 4*X^2 + 22*X,
   by simp only [fElevenB2, fElevenB5]; ring_nf; reduce_mod_char⟩

theorem copElevenB3_4 : IsCoprime fElevenB3 fElevenB4 :=
  ⟨21*X^10 + 17*X^9 + 14*X^8 + 22*X^7 + 3*X^6 + 16*X^5 + 8*X^4 + 5*X^3 + 12*X^2 + 3*X + 2,
   2*X^10 + 2*X^9 + 14*X^8 + 15*X^7 + X^6 + 5*X^5 + 7*X^4 + 10*X^3 + 10*X^2 + 16*X + 10,
   by simp only [fElevenB3, fElevenB4]; ring_nf; reduce_mod_char⟩

theorem copElevenB3_5 : IsCoprime fElevenB3 fElevenB5 :=
  ⟨20*X^10 + 16*X^9 + 7*X^8 + 3*X^7 + 14*X^6 + 2*X^5 + 16*X^4 + 7*X^2 + 18*X + 20,
   3*X^10 + 3*X^9 + 21*X^8 + 11*X^7 + 13*X^6 + 19*X^5 + 22*X^4 + 15*X^3 + 15*X^2 + X + 15,
   by simp only [fElevenB3, fElevenB5]; ring_nf; reduce_mod_char⟩

theorem copElevenB4_5 : IsCoprime fElevenB4 fElevenB5 :=
  ⟨6*X^10 + 14*X^9 + 9*X^8 + 17*X^7 + 18*X^6 + 19*X^5 + 14*X^4 + 9*X^2 + 10*X + 6,
   17*X^10 + 5*X^9 + 19*X^8 + 20*X^7 + 9*X^6 + 2*X^5 + X^4 + 15*X^3 + 13*X^2 + 9*X + 6,
   by simp only [fElevenB4, fElevenB5]; ring_nf; reduce_mod_char⟩

/-! ### Assembly -/

theorem dvd_X_pow_card_pow_sub_X_hPolyElevenB :
    hPolyElevenB ∣ X ^ (Nat.card (ZMod 23)) ^ 11 - X := by
  have h2 := xpow_mul copElevenB1_2 pElevenB1s72 pElevenB2s72
  have c3 : IsCoprime (fElevenB1 * fElevenB2) fElevenB3 :=
    (copElevenB1_3).mul_left copElevenB2_3
  have h3 := xpow_mul c3 h2 pElevenB3s72
  have c4 : IsCoprime (fElevenB1 * fElevenB2 * fElevenB3) fElevenB4 :=
    ((copElevenB1_4).mul_left copElevenB2_4).mul_left copElevenB3_4
  have h4 := xpow_mul c4 h3 pElevenB4s72
  have c5 : IsCoprime (fElevenB1 * fElevenB2 * fElevenB3 * fElevenB4) fElevenB5 :=
    (((copElevenB1_5).mul_left copElevenB2_5).mul_left copElevenB3_5).mul_left copElevenB4_5
  have h5 := xpow_mul c5 h4 pElevenB5s72
  rw [factor_hPolyElevenB]
  exact xpow_card (by rw [Nat.card_zmod]; norm_num) h5

end Fermat.MazurNonCMCertificate

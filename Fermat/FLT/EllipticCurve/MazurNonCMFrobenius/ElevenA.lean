/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius

/-!
# Row `p = 11`, `j = −121`: `H ∣ X ^ (23 ^ 11) - X`

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
noncomputable def fElevenA1 : (ZMod 23)[X] :=
  X^11 + 4*X^10 + 11*X^9 + 9*X^8 + 19*X^7 + 12*X^6 + 22*X^5 + 7*X^4 + 17*X^3 + 11*X^2 + 22*X + 5

/-- Irreducible factor 2 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenA2 : (ZMod 23)[X] :=
  X^11 + 16*X^10 + 2*X^9 + 22*X^8 + 11*X^7 + 6*X^6 + 11*X^5 + X^4 + 7*X^3 + 10*X^2 + 15*X + 17

/-- Irreducible factor 3 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenA3 : (ZMod 23)[X] :=
  X^11 + 19*X^10 + 17*X^9 + 8*X^8 + 9*X^7 + 16*X^6 + 14*X^5 + 11*X^4 + 16*X^3 + 4*X^2 + 19*X + 20

/-- Irreducible factor 4 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenA4 : (ZMod 23)[X] :=
  X^11 + 20*X^10 + 22*X^9 + 11*X^8 + 16*X^7 + 4*X^6 + 15*X^5 + 22*X^4 + 19*X^3 + 2*X^2 + 5*X + 21

/-- Irreducible factor 5 of `H` on this row, of degree 11.  Its irreducibility is
not used anywhere — only that the 5 factors are pairwise coprime. -/
noncomputable def fElevenA5 : (ZMod 23)[X] :=
  X^11 + 21*X^10 + 4*X^9 + 14*X^8 + 15*X^6 + 16*X^5 + 10*X^4 + 22*X^3 + 14*X + 22

/-- The factorisation of `H` used by every statement below. -/
theorem factor_hPolyElevenA : hPolyElevenA = fElevenA1 * fElevenA2 * fElevenA3 * fElevenA4 * fElevenA5 := by
  simp only [hPolyElevenA, fElevenA1, fElevenA2, fElevenA3, fElevenA4, fElevenA5]
  ring_nf
  reduce_mod_char

/-! ### Factor 1: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenA11 : XPow fElevenA1 1 X := xpow_one _

theorem pElevenA1s0 : XPow fElevenA1 2
    (X^2) :=
  sq_step (by norm_num) pElevenA11 ⟨
    0,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s1 : XPow fElevenA1 3
    (X^3) :=
  mul_step (by norm_num) pElevenA1s0 pElevenA11 ⟨
    0,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s2 : XPow fElevenA1 6
    (X^6) :=
  sq_step (by norm_num) pElevenA1s1 ⟨
    0,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s3 : XPow fElevenA1 12
    (5*X^10 + 12*X^9 + 17*X^8 + 18*X^7 + 3*X^6 + 12*X^5 + 11*X^4 + 11*X^3 + 22*X^2 + 14*X + 20) :=
  sq_step (by norm_num) pElevenA1s2 ⟨
    X + 19,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s4 : XPow fElevenA1 13
    (15*X^10 + 8*X^9 + 19*X^8 + 21*X^6 + 16*X^5 + 22*X^4 + 6*X^3 + 5*X^2 + 2*X + 21) :=
  mul_step (by norm_num) pElevenA1s3 pElevenA11 ⟨
    5,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s5 : XPow fElevenA1 26
    (2*X^10 + 15*X^9 + 13*X^8 + 19*X^7 + 11*X^6 + 16*X^5 + 8*X^4 + 18*X^3 + 14*X^2 + 3*X + 14) :=
  sq_step (by norm_num) pElevenA1s4 ⟨
    18*X^9 + 7*X^8 + 17*X^7 + 20*X^6 + 20*X^5 + 14*X^4 + 18*X^3 + 8*X^2 + 2*X + 21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s6 : XPow fElevenA1 27
    (7*X^10 + 14*X^9 + X^8 + 19*X^7 + 15*X^6 + 10*X^5 + 4*X^4 + 3*X^3 + 4*X^2 + 16*X + 13) :=
  mul_step (by norm_num) pElevenA1s5 pElevenA11 ⟨
    2,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s7 : XPow fElevenA1 54
    (5*X^10 + 19*X^9 + 5*X^8 + 2*X^6 + 21*X^4 + X^3 + X^2 + 6*X + 22) :=
  sq_step (by norm_num) pElevenA1s6 ⟨
    3*X^9 + 16*X^7 + 19*X^6 + 20*X^5 + 14*X^4 + 2*X^3 + 12*X^2 + 6*X + 11,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s8 : XPow fElevenA1 108
    (7*X^10 + 12*X^9 + 21*X^8 + 6*X^7 + 15*X^6 + 7*X^5 + 16*X^4 + 11*X^3 + 19*X^2 + 13*X + 20) :=
  sq_step (by norm_num) pElevenA1s7 ⟨
    2*X^9 + 21*X^8 + 6*X^7 + 9*X^6 + 15*X^5 + 15*X^4 + 20*X^3 + 8*X^2 + 20*X + 10,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s9 : XPow fElevenA1 216
    (2*X^10 + X^9 + 4*X^8 + 4*X^7 + 22*X^6 + 13*X^5 + 5*X^4 + 12*X^3 + 5*X^2 + 11*X + 6) :=
  sq_step (by norm_num) pElevenA1s8 ⟨
    3*X^9 + 18*X^8 + 11*X^7 + 20*X^6 + 7*X^5 + 8*X^4 + 2*X^3 + 16*X^2 + 9*X + 19,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s10 : XPow fElevenA1 432
    (8*X^10 + 9*X^9 + 9*X^8 + 15*X^7 + 3*X^6 + 12*X^5 + 16*X^4 + 17*X^3 + 7*X^2 + 4*X + 16) :=
  sq_step (by norm_num) pElevenA1s9 ⟨
    4*X^9 + 11*X^8 + 21*X^7 + 13*X^6 + 22*X^5 + 3*X^4 + 7*X^3 + 8*X + 4,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s11 : XPow fElevenA1 433
    (13*X^9 + 12*X^8 + 12*X^7 + 8*X^6 + X^5 + 7*X^4 + 9*X^3 + 8*X^2 + X + 6) :=
  mul_step (by norm_num) pElevenA1s10 pElevenA11 ⟨
    8,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s12 : XPow fElevenA1 866
    (15*X^10 + 17*X^9 + X^8 + 18*X^7 + 12*X^6 + 6*X^5 + 6*X^4 + 17*X^3 + 17*X^2 + 8*X + 6) :=
  sq_step (by norm_num) pElevenA1s11 ⟨
    8*X^7 + 4*X^6 + 7*X^5 + 7*X^4 + 17*X^2 + 2*X + 6,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s13 : XPow fElevenA1 1732
    (20*X^10 + 19*X^9 + 9*X^8 + 20*X^7 + 7*X^6 + 15*X^5 + 22*X^4 + 16*X^3 + 5*X^2 + 14*X + 10) :=
  sq_step (by norm_num) pElevenA1s12 ⟨
    18*X^9 + X^8 + 2*X^7 + 2*X^6 + 17*X^5 + 5*X^4 + 15*X^3 + 13*X^2 + 11*X + 19,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s14 : XPow fElevenA1 1733
    (8*X^10 + 19*X^9 + X^8 + 18*X^7 + 5*X^6 + 19*X^5 + 14*X^4 + 10*X^3 + X^2 + 7*X + 15) :=
  mul_step (by norm_num) pElevenA1s13 pElevenA11 ⟨
    20,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s15 : XPow fElevenA1 3466
    (16*X^10 + 21*X^9 + 19*X^8 + 16*X^7 + X^6 + 8*X^5 + 22*X^4 + 13*X^3 + X^2 + 11*X + 5) :=
  sq_step (by norm_num) pElevenA1s14 ⟨
    18*X^9 + 2*X^8 + 10*X^7 + 10*X^6 + 2*X^5 + 22*X^4 + 10*X^3 + 15*X^2 + 21*X + 21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s16 : XPow fElevenA1 6932
    (21*X^10 + 17*X^9 + 9*X^8 + 18*X^7 + 20*X^6 + X^5 + 16*X^4 + 10*X^3 + 12*X^2 + 2*X + 6) :=
  sq_step (by norm_num) pElevenA1s15 ⟨
    3*X^9 + 16*X^8 + 9*X^7 + 13*X^6 + 20*X^4 + 18*X^3 + 12*X^2 + 15*X + 13,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s17 : XPow fElevenA1 13864
    (3*X^10 + 13*X^9 + 8*X^8 + 11*X^7 + 5*X^6 + X^5 + 20*X^4 + 19*X^3 + X^2 + 4*X + 4) :=
  sq_step (by norm_num) pElevenA1s16 ⟨
    4*X^9 + 8*X^8 + 16*X^7 + 13*X^5 + 6*X^4 + 22*X^3 + 20*X + 11,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s18 : XPow fElevenA1 13865
    (X^10 + 21*X^9 + 7*X^8 + 17*X^7 + 11*X^6 + 21*X^4 + 19*X^3 + 17*X^2 + 7*X + 8) :=
  mul_step (by norm_num) pElevenA1s17 pElevenA11 ⟨
    3,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s19 : XPow fElevenA1 27730
    (13*X^10 + 3*X^9 + 11*X^8 + 11*X^7 + 10*X^6 + 8*X^5 + 22*X^4 + 19*X^3 + 15*X^2 + 6*X + 4) :=
  sq_step (by norm_num) pElevenA1s18 ⟨
    X^9 + 15*X^8 + 16*X^7 + 21*X^6 + 3*X^5 + 16*X^4 + 15*X^3 + 11*X^2 + 19*X + 12,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s20 : XPow fElevenA1 55460
    (15*X^10 + X^9 + 14*X^8 + 2*X^7 + 2*X^6 + 14*X^5 + X^4 + 15*X^3 + 3*X^2 + 9*X + 3) :=
  sq_step (by norm_num) pElevenA1s19 ⟨
    8*X^9 + 4*X^6 + 3*X^5 + 13*X^4 + 20*X^3 + 19*X^2 + 12*X + 21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s21 : XPow fElevenA1 110920
    (3*X^10 + 20*X^9 + 21*X^8 + 10*X^7 + X^6 + 14*X^4 + 21*X^3 + 21*X^2 + 20*X + 18) :=
  sq_step (by norm_num) pElevenA1s20 ⟨
    18*X^9 + 4*X^8 + 20*X^6 + 9*X^5 + X^4 + 12*X^3 + 3*X^2 + 12,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s22 : XPow fElevenA1 110921
    (8*X^10 + 11*X^9 + 6*X^8 + 13*X^7 + 10*X^6 + 17*X^5 + 16*X^3 + 10*X^2 + 21*X + 8) :=
  mul_step (by norm_num) pElevenA1s21 pElevenA11 ⟨
    3,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s23 : XPow fElevenA1 221842
    (21*X^10 + 7*X^9 + 4*X^8 + 19*X^7 + 12*X^6 + 9*X^5 + 19*X^4 + 7*X^3 + 20*X^2 + 19*X + 11) :=
  sq_step (by norm_num) pElevenA1s22 ⟨
    18*X^9 + 12*X^8 + 17*X^7 + X^6 + 2*X^5 + 9*X^4 + 9*X^3 + 14*X + 6,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s24 : XPow fElevenA1 221843
    (15*X^10 + 3*X^9 + 14*X^8 + 4*X^7 + 10*X^6 + 17*X^5 + 21*X^4 + 8*X^3 + 18*X^2 + 9*X + 10) :=
  mul_step (by norm_num) pElevenA1s23 pElevenA11 ⟨
    21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s25 : XPow fElevenA1 443686
    (11*X^9 + 14*X^7 + 11*X^6 + 19*X^5 + 4*X^4 + 13*X^3 + 20*X^2 + 2*X + 14) :=
  sq_step (by norm_num) pElevenA1s24 ⟨
    18*X^9 + 18*X^8 + 21*X^7 + 13*X^6 + 9*X^5 + 9*X^4 + 18*X^3 + 17*X^2 + 5*X + 8,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s26 : XPow fElevenA1 887372
    (18*X^10 + 8*X^9 + 21*X^8 + 15*X^7 + 15*X^6 + 10*X^5 + 6*X^4 + 15*X^3 + 14*X^2 + 22*X + 11) :=
  sq_step (by norm_num) pElevenA1s25 ⟨
    6*X^7 + 22*X^6 + 16*X^5 + 20*X^4 + 2*X^2 + 5*X + 14,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s27 : XPow fElevenA1 887373
    (5*X^10 + 7*X^9 + 14*X^8 + 18*X^7 + X^6 + X^5 + 4*X^4 + 7*X^3 + 8*X^2 + 6*X + 2) :=
  mul_step (by norm_num) pElevenA1s26 pElevenA11 ⟨
    18,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s28 : XPow fElevenA1 1774746
    (X^10 + 21*X^9 + 16*X^8 + 11*X^7 + X^6 + 12*X^5 + 10*X^4 + 13*X^3 + 14*X^2 + 14*X + 14) :=
  sq_step (by norm_num) pElevenA1s27 ⟨
    2*X^9 + 16*X^8 + 11*X^7 + 17*X^5 + 10*X^4 + 10*X^3 + 10*X^2 + 20*X + 21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s29 : XPow fElevenA1 3549492
    (3*X^10 + 22*X^9 + 12*X^8 + 21*X^6 + 5*X^5 + 10*X^4 + 16*X^3 + 19*X^2 + 12*X + 18) :=
  sq_step (by norm_num) pElevenA1s28 ⟨
    X^9 + 15*X^8 + 11*X^7 + 16*X^6 + 13*X^5 + X^4 + 21*X^3 + 5*X^2 + 4*X + 8,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s30 : XPow fElevenA1 7098984
    (7*X^10 + 4*X^9 + 7*X^8 + 14*X^7 + 6*X^6 + 3*X^5 + 20*X^4 + 21*X^3 + 6*X + 21) :=
  sq_step (by norm_num) pElevenA1s29 ⟨
    9*X^9 + 4*X^8 + 4*X^7 + 19*X^6 + 12*X^5 + 17*X^4 + 22*X^3 + 12*X^2 + 9*X + 10,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s31 : XPow fElevenA1 7098985
    (22*X^10 + 22*X^9 + 20*X^8 + 11*X^7 + 11*X^6 + 4*X^5 + 18*X^4 + 19*X^3 + 21*X^2 + 5*X + 11) :=
  mul_step (by norm_num) pElevenA1s30 pElevenA11 ⟨
    7,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s32 : XPow fElevenA1 14197970
    (X^10 + 7*X^9 + 14*X^8 + 18*X^7 + 21*X^6 + 3*X^5 + 21*X^3 + 4*X^2 + 20) :=
  sq_step (by norm_num) pElevenA1s31 ⟨
    X^9 + 21*X^8 + 4*X^7 + 4*X^6 + 19*X^5 + 4*X^4 + 21*X^3 + 11*X^2 + 15*X + 11,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s33 : XPow fElevenA1 14197971
    (3*X^10 + 3*X^9 + 9*X^8 + 2*X^7 + 14*X^6 + X^5 + 14*X^4 + 10*X^3 + 12*X^2 + 21*X + 18) :=
  mul_step (by norm_num) pElevenA1s32 pElevenA11 ⟨
    1,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s34 : XPow fElevenA1 28395942
    (7*X^10 + 12*X^9 + 9*X^8 + 19*X^7 + 8*X^6 + 4*X^5 + 3*X^4 + 2*X^3 + 11*X^2 + 11*X + 19) :=
  sq_step (by norm_num) pElevenA1s33 ⟨
    9*X^9 + 5*X^8 + 13*X^7 + 16*X^6 + 7*X^5 + 16*X^4 + 16*X^3 + 18*X^2 + 14*X + 15,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s35 : XPow fElevenA1 28395943
    (7*X^10 + X^9 + 2*X^8 + 13*X^7 + 12*X^6 + 10*X^5 + 22*X^4 + 7*X^3 + 3*X^2 + 3*X + 11) :=
  mul_step (by norm_num) pElevenA1s34 pElevenA11 ⟨
    7,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s36 : XPow fElevenA1 56791886
    (22*X^10 + 17*X^9 + 3*X^8 + X^7 + 7*X^6 + 6*X^5 + 11*X^4 + 16*X^3 + 2*X^2 + 2*X + 3) :=
  sq_step (by norm_num) pElevenA1s35 ⟨
    3*X^9 + 2*X^8 + 11*X^7 + X^6 + 21*X^5 + 17*X^4 + 7*X^3 + 12*X^2 + 12*X + 19,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s37 : XPow fElevenA1 56791887
    (21*X^10 + 14*X^9 + 10*X^8 + 3*X^7 + 18*X^6 + 10*X^5 + 19*X^3 + 13*X^2 + 2*X + 5) :=
  mul_step (by norm_num) pElevenA1s36 pElevenA11 ⟨
    22,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s38 : XPow fElevenA1 113583774
    (14*X^10 + 9*X^9 + 20*X^8 + 15*X^6 + 8*X^5 + 12*X^4 + 20*X^3 + 20*X^2 + 4*X + 21) :=
  sq_step (by norm_num) pElevenA1s37 ⟨
    4*X^9 + 20*X^8 + 9*X^7 + 22*X^6 + 14*X^5 + 16*X^4 + 10*X^3 + 19*X + 10,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s39 : XPow fElevenA1 227167548
    (19*X^10 + 20*X^9 + 5*X^8 + 5*X^7 + 21*X^6 + 2*X^5 + 18*X^4 + 17*X^3 + 20*X^2 + 18*X + 22) :=
  sq_step (by norm_num) pElevenA1s38 ⟨
    12*X^9 + 20*X^8 + 15*X^7 + 18*X^6 + 14*X^5 + 18*X^4 + 18*X^3 + 22*X^2 + 21*X + 1,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s40 : XPow fElevenA1 454335096
    (18*X^10 + 16*X^9 + 12*X^8 + 12*X^7 + 9*X^6 + 17*X^5 + 21*X^4 + 13*X^3 + X^2 + 7*X + 9) :=
  sq_step (by norm_num) pElevenA1s39 ⟨
    16*X^9 + 6*X^8 + 22*X^7 + 9*X^5 + 12*X^4 + 10*X^3 + 7*X^2 + 15*X + 3,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s41 : XPow fElevenA1 454335097
    (13*X^10 + 21*X^9 + 11*X^8 + 12*X^7 + 8*X^6 + 16*X^5 + 2*X^4 + 17*X^3 + 16*X^2 + 4*X + 2) :=
  mul_step (by norm_num) pElevenA1s40 pElevenA11 ⟨
    18,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s42 : XPow fElevenA1 908670194
    (10*X^8 + 7*X^7 + 12*X^6 + 16*X^5 + 2*X^4 + 18*X^3 + X^2 + 7*X + 10) :=
  sq_step (by norm_num) pElevenA1s41 ⟨
    8*X^9 + 8*X^8 + 9*X^7 + 3*X^6 + 15*X^5 + 19*X^4 + 11*X^3 + 9*X^2 + 8*X + 8,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s43 : XPow fElevenA1 1817340388
    (11*X^10 + 20*X^9 + 18*X^8 + 2*X^7 + 21*X^6 + 14*X^5 + 11*X^4 + 8*X^3 + 11*X^2 + 17*X + 6) :=
  sq_step (by norm_num) pElevenA1s42 ⟨
    8*X^5 + 16*X^4 + 22*X^3 + 14*X^2 + 21*X + 5,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s44 : XPow fElevenA1 1817340389
    (22*X^10 + 12*X^9 + 18*X^8 + 19*X^7 + 20*X^6 + 22*X^5 + 8*X^3 + 11*X^2 + 17*X + 14) :=
  mul_step (by norm_num) pElevenA1s43 pElevenA11 ⟨
    11,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s45 : XPow fElevenA1 3634680778
    (6*X^10 + 13*X^9 + 5*X^8 + 15*X^7 + 15*X^5 + 7*X^4 + 21*X^3 + 14*X^2 + 15) :=
  sq_step (by norm_num) pElevenA1s44 ⟨
    X^9 + 18*X^8 + 2*X^7 + 18*X^6 + 5*X^5 + X^4 + 8*X^3 + 12*X^2 + 4*X + 4,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s46 : XPow fElevenA1 7269361556
    (11*X^10 + 13*X^9 + 4*X^8 + 13*X^7 + 15*X^6 + 11*X^5 + 21*X^4 + 15*X^3 + 4*X^2 + 14*X) :=
  sq_step (by norm_num) pElevenA1s45 ⟨
    13*X^9 + 12*X^8 + 15*X^7 + X^6 + 6*X^5 + 6*X^4 + 2*X^2 + 20*X + 22,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s47 : XPow fElevenA1 14538723112
    (6*X^10 + 9*X^9 + 20*X^8 + 21*X^7 + 18*X^6 + 15*X^5 + 9*X^4 + 21*X^3 + 16*X^2 + 6*X + 8) :=
  sq_step (by norm_num) pElevenA1s46 ⟨
    6*X^9 + 9*X^8 + 17*X^7 + 8*X^6 + 17*X^5 + 8*X^3 + 21*X^2 + 4*X + 3,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s48 : XPow fElevenA1 29077446224
    (X^10 + 4*X^9 + 14*X^8 + 12*X^7 + 22*X^6 + 18*X^5 + 21*X^4 + 8*X^3 + 19*X^2 + 10*X + 5) :=
  sq_step (by norm_num) pElevenA1s47 ⟨
    13*X^9 + 10*X^8 + 17*X^6 + 14*X^5 + 19*X^4 + 14*X^3 + 9*X^2 + 3*X + 21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s49 : XPow fElevenA1 29077446225
    (3*X^9 + 3*X^8 + 3*X^7 + 6*X^6 + 22*X^5 + X^4 + 2*X^3 + 22*X^2 + 6*X + 18) :=
  mul_step (by norm_num) pElevenA1s48 pElevenA11 ⟨
    1,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s50 : XPow fElevenA1 58154892450
    (20*X^10 + 14*X^9 + 17*X^8 + 19*X^7 + 17*X^6 + 3*X^5 + 13*X^4 + 20*X^3 + 7*X^2 + 6*X + 19) :=
  sq_step (by norm_num) pElevenA1s49 ⟨
    9*X^7 + 5*X^6 + 10*X^4 + 13*X^3 + 16*X^2 + 22*X + 15,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s51 : XPow fElevenA1 116309784900
    (X^10 + 22*X^9 + 12*X^8 + 22*X^7 + 5*X^6 + 15*X^5 + 17*X^4 + 2*X^3 + X^2 + 2*X + 10) :=
  sq_step (by norm_num) pElevenA1s50 ⟨
    9*X^9 + 18*X^8 + 15*X^7 + 14*X^5 + 3*X^4 + 11*X^3 + 12*X^2 + 16*X + 15,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s52 : XPow fElevenA1 116309784901
    (18*X^10 + X^9 + 13*X^8 + 9*X^7 + 3*X^6 + 18*X^5 + 18*X^4 + 7*X^3 + 14*X^2 + 11*X + 18) :=
  mul_step (by norm_num) pElevenA1s51 pElevenA11 ⟨
    1,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s53 : XPow fElevenA1 232619569802
    (21*X^10 + 2*X^9 + 2*X^8 + X^7 + 20*X^6 + 13*X^5 + 5*X^4 + 2*X^3 + 9*X^2 + 19*X + 4) :=
  sq_step (by norm_num) pElevenA1s52 ⟨
    2*X^9 + 5*X^8 + 13*X^7 + 18*X^6 + 20*X^5 + 6*X^4 + 17*X^3 + 12*X^2 + 10*X + 18,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s54 : XPow fElevenA1 232619569803
    (10*X^10 + X^9 + 19*X^8 + 12*X^7 + 14*X^6 + 3*X^5 + 16*X^4 + 20*X^3 + 18*X^2 + 2*X + 10) :=
  mul_step (by norm_num) pElevenA1s53 pElevenA11 ⟨
    21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s55 : XPow fElevenA1 465239139606
    (2*X^10 + 6*X^9 + X^8 + 8*X^7 + 20*X^6 + X^5 + 7*X^4 + 15*X^3 + 2*X^2 + 15*X + 11) :=
  sq_step (by norm_num) pElevenA1s54 ⟨
    8*X^9 + 11*X^8 + 19*X^7 + 9*X^6 + 8*X^5 + 6*X^4 + 2*X^3 + 16*X^2 + 15*X + 4,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s56 : XPow fElevenA1 930478279212
    (16*X^10 + X^9 + 20*X^8 + 6*X^7 + X^6 + 18*X^5 + 13*X^4 + 19*X^3 + 3*X + 17) :=
  sq_step (by norm_num) pElevenA1s55 ⟨
    4*X^9 + 8*X^8 + 10*X^7 + 18*X^6 + 8*X^5 + 16*X^4 + 8*X^3 + 3*X^2 + 7*X + 7,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s57 : XPow fElevenA1 1860956558424
    (3*X^10 + 5*X^8 + 4*X^7 + 4*X^6 + 15*X^5 + 15*X^4 + 16*X^3 + 8*X^2 + 8*X + 10) :=
  sq_step (by norm_num) pElevenA1s56 ⟨
    3*X^9 + 20*X^8 + 22*X^7 + 12*X^6 + 9*X^5 + 13*X^4 + 5*X^3 + 8*X^2 + 18*X + 19,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s58 : XPow fElevenA1 1860956558425
    (11*X^10 + 18*X^9 + 16*X^7 + 2*X^6 + 18*X^5 + 18*X^4 + 3*X^3 + 21*X^2 + 13*X + 8) :=
  mul_step (by norm_num) pElevenA1s57 pElevenA11 ⟨
    3,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s59 : XPow fElevenA1 3721913116850
    (19*X^10 + 8*X^9 + 11*X^8 + 21*X^7 + 11*X^6 + 6*X^5 + 14*X^4 + 13*X^3 + 20*X^2 + 20*X + 14) :=
  sq_step (by norm_num) pElevenA1s58 ⟨
    6*X^9 + 4*X^8 + 12*X^7 + 22*X^6 + 20*X^5 + 5*X^4 + 17*X^3 + 13*X^2 + 12*X + 10,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s60 : XPow fElevenA1 3721913116851
    (X^10 + 9*X^9 + 11*X^8 + 18*X^7 + 8*X^6 + 10*X^5 + 18*X^4 + 19*X^3 + 18*X^2 + 10*X + 20) :=
  mul_step (by norm_num) pElevenA1s59 pElevenA11 ⟨
    19,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s61 : XPow fElevenA1 7443826233702
    (21*X^10 + 15*X^9 + 5*X^8 + 18*X^7 + 10*X^6 + 6*X^5 + 16*X^4 + 9*X^3 + 10*X^2 + 8*X + 9) :=
  sq_step (by norm_num) pElevenA1s60 ⟨
    X^9 + 14*X^8 + 13*X^7 + 19*X^6 + 5*X^5 + 5*X^4 + 10*X^3 + 13*X^2 + 14*X,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s62 : XPow fElevenA1 14887652467404
    (2*X^10 + 22*X^9 + 10*X^8 + 11*X^7 + 4*X^6 + 5*X^5 + 2*X^4 + 2*X^3 + 13*X^2 + 13*X + 7) :=
  sq_step (by norm_num) pElevenA1s61 ⟨
    4*X^9 + 16*X^8 + 5*X^7 + 7*X^6 + 15*X^5 + 14*X^4 + 19*X^3 + 18*X^2 + 8*X + 1,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s63 : XPow fElevenA1 14887652467405
    (14*X^10 + 11*X^9 + 16*X^8 + 12*X^7 + 4*X^6 + 4*X^5 + 11*X^4 + 2*X^3 + 14*X^2 + 9*X + 13) :=
  mul_step (by norm_num) pElevenA1s62 pElevenA11 ⟨
    2,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s64 : XPow fElevenA1 29775304934810
    (11*X^10 + 18*X^9 + 10*X^8 + 14*X^7 + 22*X^6 + 4*X^5 + 14*X^4 + 11*X^3 + 22*X^2 + 22*X + 15) :=
  sq_step (by norm_num) pElevenA1s63 ⟨
    12*X^9 + 7*X^8 + 18*X^7 + 17*X^6 + 6*X^5 + 3*X^4 + 3*X^2 + 9*X + 17,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s65 : XPow fElevenA1 59550609869620
    (11*X^10 + 12*X^9 + 6*X^8 + 18*X^7 + 9*X^6 + 19*X^5 + 18*X^4 + 22*X^3 + 21*X^2 + 11*X + 12) :=
  sq_step (by norm_num) pElevenA1s64 ⟨
    6*X^9 + 4*X^8 + 2*X^7 + 10*X^6 + 2*X^5 + 2*X^4 + 14*X^3 + 13*X^2 + 4*X + 15,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s66 : XPow fElevenA1 119101219739240
    (12*X^10 + 4*X^9 + 20*X^8 + 3*X^6 + 2*X^5 + 8*X^4 + 20*X^3 + 3*X^2 + 20*X + 16) :=
  sq_step (by norm_num) pElevenA1s65 ⟨
    6*X^9 + 10*X^8 + 9*X^7 + 18*X^6 + 15*X^5 + 19*X^4 + 21*X^3 + 6*X^2 + 7*X + 21,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s67 : XPow fElevenA1 238202439478480
    (6*X^10 + 7*X^9 + 14*X^7 + 20*X^6 + 12*X^5 + 15*X^4 + 17*X^3 + 2*X^2 + 14*X + 18) :=
  sq_step (by norm_num) pElevenA1s66 ⟨
    6*X^9 + 3*X^8 + 4*X^7 + 11*X^6 + 13*X^5 + 10*X^4 + 9*X^3 + 19*X^2 + 5*X + 20,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s68 : XPow fElevenA1 238202439478481
    (6*X^10 + 3*X^9 + 6*X^8 + 21*X^7 + 9*X^6 + 21*X^5 + 21*X^4 + 15*X^3 + 17*X^2 + X + 16) :=
  mul_step (by norm_num) pElevenA1s67 pElevenA11 ⟨
    6,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s69 : XPow fElevenA1 476404878956962
    (9*X^10 + 13*X^9 + 7*X^8 + 12*X^7 + 10*X^6 + 16*X^5 + 14*X^4 + 17*X^3 + 15*X^2 + 7*X + 14) :=
  sq_step (by norm_num) pElevenA1s68 ⟨
    13*X^9 + 7*X^8 + 2*X^7 + 17*X^6 + 8*X^5 + 9*X^4 + 12*X^3 + 10*X^2 + 11*X + 7,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s70 : XPow fElevenA1 476404878956963
    (1) :=
  mul_step (by norm_num) pElevenA1s69 pElevenA11 ⟨
    9,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s71 : XPow fElevenA1 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenA1s70 ⟨
    0,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA1s72 : XPow fElevenA1 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenA1s71 pElevenA11 ⟨
    0,
    by simp only [fElevenA1]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 2: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenA21 : XPow fElevenA2 1 X := xpow_one _

theorem pElevenA2s0 : XPow fElevenA2 2
    (X^2) :=
  sq_step (by norm_num) pElevenA21 ⟨
    0,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s1 : XPow fElevenA2 3
    (X^3) :=
  mul_step (by norm_num) pElevenA2s0 pElevenA21 ⟨
    0,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s2 : XPow fElevenA2 6
    (X^6) :=
  sq_step (by norm_num) pElevenA2s1 ⟨
    0,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s3 : XPow fElevenA2 12
    (X^10 + 10*X^9 + 19*X^8 + 9*X^7 + 16*X^6 + 14*X^5 + 9*X^4 + 10*X^3 + 7*X^2 + 16*X + 19) :=
  sq_step (by norm_num) pElevenA2s2 ⟨
    X + 7,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s4 : XPow fElevenA2 13
    (17*X^10 + 17*X^9 + 10*X^8 + 5*X^7 + 8*X^6 + 21*X^5 + 9*X^4 + 6*X^2 + 4*X + 6) :=
  mul_step (by norm_num) pElevenA2s3 pElevenA21 ⟨
    1,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s5 : XPow fElevenA2 26
    (15*X^10 + 17*X^9 + 12*X^8 + 8*X^7 + 18*X^6 + 17*X^4 + 3*X^3 + 19*X^2 + 9*X + 8) :=
  sq_step (by norm_num) pElevenA2s4 ⟨
    13*X^9 + 2*X^8 + 19*X^7 + 8*X^6 + 5*X^5 + 12*X^4 + 3*X^3 + 19*X^2 + X + 3,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s6 : XPow fElevenA2 27
    (7*X^10 + 5*X^9 + 14*X^7 + 2*X^6 + 13*X^5 + 11*X^4 + 6*X^3 + 20*X^2 + 13*X + 21) :=
  mul_step (by norm_num) pElevenA2s5 pElevenA21 ⟨
    15,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s7 : XPow fElevenA2 54
    (10*X^10 + 15*X^9 + 9*X^7 + 13*X^6 + 4*X^5 + 18*X^4 + 17*X^3 + 14*X^2 + 18*X + 2) :=
  sq_step (by norm_num) pElevenA2s6 ⟨
    3*X^9 + 22*X^8 + 12*X^7 + 9*X^6 + 12*X^5 + 20*X^4 + 9*X^3 + 7*X^2 + 7*X + 15,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s8 : XPow fElevenA2 108
    (14*X^10 + 21*X^9 + 19*X^8 + 19*X^7 + 21*X^6 + 17*X^5 + 18*X^4 + 6*X^3 + 16*X^2 + 7*X + 9) :=
  sq_step (by norm_num) pElevenA2s7 ⟨
    8*X^9 + 11*X^8 + 10*X^7 + 6*X^6 + 15*X^5 + 13*X^4 + 19*X^3 + 15*X^2 + 20*X + 20,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s9 : XPow fElevenA2 216
    (7*X^10 + 15*X^9 + 11*X^8 + 11*X^7 + 9*X^6 + 7*X^5 + 21*X^4 + 4*X^3 + 5*X^2 + 18*X + 3) :=
  sq_step (by norm_num) pElevenA2s8 ⟨
    12*X^9 + 5*X^8 + 18*X^7 + 9*X^6 + 14*X^5 + 4*X^4 + 2*X^3 + 21*X^2 + 7*X + 10,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s10 : XPow fElevenA2 432
    (19*X^10 + 5*X^9 + 19*X^8 + 12*X^7 + 20*X^6 + 22*X^5 + X^4 + 10*X^3 + 17*X^2 + X + 17) :=
  sq_step (by norm_num) pElevenA2s9 ⟨
    3*X^9 + X^8 + 12*X^7 + 17*X^6 + 19*X^5 + 2*X^4 + X^3 + 5*X^2 + 20*X + 9,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s11 : XPow fElevenA2 433
    (4*X^9 + 8*X^8 + 18*X^7 + 22*X^5 + 14*X^4 + 22*X^3 + 18*X^2 + 8*X + 22) :=
  mul_step (by norm_num) pElevenA2s10 pElevenA21 ⟨
    19,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s12 : XPow fElevenA2 866
    (11*X^10 + 6*X^9 + 5*X^8 + 10*X^7 + 12*X^6 + 7*X^5 + 15*X^4 + 16*X^3 + 10*X^2 + 10*X + 11) :=
  sq_step (by norm_num) pElevenA2s11 ⟨
    16*X^7 + 15*X^6 + 5*X^5 + 10*X^4 + 8*X^3 + 14*X^2 + 20*X + 17,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s13 : XPow fElevenA2 1732
    (X^10 + 16*X^9 + 2*X^8 + 18*X^7 + 9*X^6 + 11*X^5 + 21*X^4 + X^3 + 20*X^2 + 3*X + 8) :=
  sq_step (by norm_num) pElevenA2s12 ⟨
    6*X^9 + 13*X^8 + 18*X^7 + 18*X^6 + 9*X^5 + 11*X^4 + X^3 + 13*X^2 + 3*X + 8,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s14 : XPow fElevenA2 1733
    (19*X^8 + 21*X^7 + 5*X^6 + 10*X^5 + 13*X^3 + 16*X^2 + 16*X + 6) :=
  mul_step (by norm_num) pElevenA2s13 pElevenA21 ⟨
    1,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s15 : XPow fElevenA2 3466
    (11*X^10 + 19*X^9 + 12*X^8 + 13*X^7 + 2*X^6 + 10*X^5 + 11*X^4 + 14*X^3 + 6*X^2 + 20*X + 10) :=
  sq_step (by norm_num) pElevenA2s14 ⟨
    16*X^5 + 13*X^4 + 5*X^2 + 18*X + 11,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s16 : XPow fElevenA2 6932
    (X^10 + X^9 + 15*X^8 + 16*X^7 + 10*X^6 + 9*X^4 + 18*X^3 + 16*X^2 + 4*X + 18) :=
  sq_step (by norm_num) pElevenA2s15 ⟨
    6*X^9 + 15*X^7 + 2*X^6 + 2*X^5 + 22*X^4 + X^3 + 14*X^2 + 11*X + 17,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s17 : XPow fElevenA2 13864
    (2*X^10 + 6*X^9 + 5*X^8 + 14*X^7 + 5*X^6 + 11*X^5 + 15*X^4 + 4*X^3 + 15*X^2 + 14*X + 7) :=
  sq_step (by norm_num) pElevenA2s16 ⟨
    X^9 + 9*X^8 + 22*X^6 + 15*X^5 + 19*X^4 + 13*X^3 + 8*X^2 + 13*X + 20,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s18 : XPow fElevenA2 13865
    (20*X^10 + X^9 + 16*X^8 + 6*X^7 + 22*X^6 + 16*X^5 + 2*X^4 + X^3 + 17*X^2 + 12) :=
  mul_step (by norm_num) pElevenA2s17 pElevenA21 ⟨
    2,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s19 : XPow fElevenA2 27730
    (6*X^10 + 2*X^9 + 18*X^8 + 17*X^7 + 2*X^6 + 11*X^5 + 11*X^4 + 2*X^3 + 15*X^2 + 19*X + 8) :=
  sq_step (by norm_num) pElevenA2s18 ⟨
    9*X^9 + 11*X^8 + 10*X^7 + 7*X^6 + 8*X^5 + 17*X^4 + 20*X^3 + 4*X + 8,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s20 : XPow fElevenA2 55460
    (18*X^10 + 20*X^9 + 8*X^7 + 5*X^6 + 22*X^5 + X^4 + 11*X^3 + 14*X^2 + 19*X + 16) :=
  sq_step (by norm_num) pElevenA2s19 ⟨
    13*X^9 + 10*X^7 + 14*X^6 + 6*X^5 + 8*X^4 + 20*X^3 + 21*X^2 + 13*X + 15,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s21 : XPow fElevenA2 110920
    (5*X^10 + 18*X^9 + X^8 + 7*X^7 + 9*X^6 + 12*X^5 + 12*X^4 + 18*X^3 + 2*X^2 + 16*X + 2) :=
  sq_step (by norm_num) pElevenA2s20 ⟨
    2*X^9 + 21*X^8 + 14*X^7 + X^6 + 18*X^5 + 13*X^4 + 21*X^3 + 5*X^2 + 14*X + 19,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s22 : XPow fElevenA2 110921
    (7*X^10 + 14*X^9 + 12*X^8 + 5*X^6 + 3*X^5 + 13*X^4 + 13*X^3 + 12*X^2 + 19*X + 7) :=
  mul_step (by norm_num) pElevenA2s21 pElevenA21 ⟨
    5,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s23 : XPow fElevenA2 221842
    (18*X^10 + 14*X^9 + 20*X^8 + 9*X^7 + 11*X^6 + 20*X^5 + 6*X^4 + 8*X^3 + 5*X^2 + 2*X + 19) :=
  sq_step (by norm_num) pElevenA2s22 ⟨
    3*X^9 + 10*X^8 + 14*X^7 + 3*X^6 + 16*X^4 + X^3 + 18*X^2 + X + 18,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s24 : XPow fElevenA2 221843
    (2*X^10 + 7*X^9 + 4*X^8 + 20*X^7 + 4*X^6 + 15*X^5 + 13*X^4 + 17*X^3 + 6*X^2 + 2*X + 16) :=
  mul_step (by norm_num) pElevenA2s23 pElevenA21 ⟨
    18,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s25 : XPow fElevenA2 443686
    (2*X^10 + 3*X^9 + 14*X^8 + 4*X^7 + 6*X^6 + 9*X^5 + 16*X^4 + 11*X^3 + 14*X^2 + 20*X + 22) :=
  sq_step (by norm_num) pElevenA2s24 ⟨
    4*X^9 + 10*X^8 + 12*X^7 + 20*X^6 + 3*X^5 + 20*X^4 + 14*X^3 + X^2 + 14*X + 7,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s26 : XPow fElevenA2 887372
    (9*X^10 + 11*X^9 + 20*X^8 + X^7 + 12*X^6 + 17*X^5 + 16*X^4 + 22*X^3 + 15*X^2 + 2*X + 12) :=
  sq_step (by norm_num) pElevenA2s25 ⟨
    4*X^9 + 17*X^8 + 15*X^7 + 14*X^6 + 9*X^5 + 10*X^3 + 15*X^2 + 2*X + 21,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s27 : XPow fElevenA2 887373
    (5*X^10 + 2*X^9 + 10*X^8 + 5*X^7 + 9*X^6 + 9*X^5 + 13*X^4 + 21*X^3 + 4*X^2 + 15*X + 8) :=
  mul_step (by norm_num) pElevenA2s26 pElevenA21 ⟨
    9,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s28 : XPow fElevenA2 1774746
    (5*X^10 + 18*X^9 + 19*X^8 + 12*X^7 + 14*X^6 + 22*X^5 + 21*X^4 + 21*X^3 + 4*X^2 + 17*X + 19) :=
  sq_step (by norm_num) pElevenA2s27 ⟨
    2*X^9 + 11*X^8 + 16*X^7 + 21*X^6 + 15*X^5 + 11*X^4 + 14*X^3 + 12*X^2 + 15*X + 4,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s29 : XPow fElevenA2 3549492
    (18*X^10 + 16*X^9 + 12*X^6 + 3*X^5 + 20*X^4 + X^3 + 18*X^2 + 4*X + 8) :=
  sq_step (by norm_num) pElevenA2s28 ⟨
    2*X^9 + 10*X^8 + 5*X^7 + 16*X^6 + 11*X^5 + 4*X^4 + 22*X^3 + 22*X^2 + 20*X + 14,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s30 : XPow fElevenA2 7098984
    (14*X^10 + 20*X^9 + 12*X^8 + 3*X^7 + 10*X^6 + 22*X^5 + 6*X^4 + 16*X^3 + 18*X^2 + 16*X + 5) :=
  sq_step (by norm_num) pElevenA2s29 ⟨
    2*X^9 + 15*X^8 + 12*X^7 + 10*X^6 + 11*X^5 + 16*X^4 + 5*X^3 + 19*X^2 + 17,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s31 : XPow fElevenA2 7098985
    (3*X^10 + 7*X^9 + 17*X^8 + 17*X^7 + 7*X^6 + 13*X^5 + 2*X^4 + 12*X^3 + 14*X^2 + 2*X + 15) :=
  mul_step (by norm_num) pElevenA2s30 pElevenA21 ⟨
    14,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s32 : XPow fElevenA2 14197970
    (16*X^10 + 14*X^9 + 11*X^8 + 6*X^7 + 7*X^6 + 11*X^5 + 3*X^4 + 12*X^3 + 12*X^2 + 4*X + 16) :=
  sq_step (by norm_num) pElevenA2s31 ⟨
    9*X^9 + 13*X^8 + 17*X^7 + 5*X^6 + X^5 + 19*X^4 + 10*X^3 + 21*X^2 + 9*X + 15,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s33 : XPow fElevenA2 14197971
    (11*X^10 + 2*X^9 + 22*X^8 + 15*X^7 + 7*X^6 + 11*X^5 + 19*X^4 + 15*X^3 + 5*X^2 + 6*X + 4) :=
  mul_step (by norm_num) pElevenA2s32 pElevenA21 ⟨
    16,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s34 : XPow fElevenA2 28395942
    (19*X^10 + 22*X^9 + 11*X^8 + 13*X^7 + 5*X^6 + 15*X^5 + 10*X^4 + X^3 + X^2 + 18*X + 9) :=
  sq_step (by norm_num) pElevenA2s33 ⟨
    6*X^9 + 17*X^8 + 20*X^7 + X^6 + 18*X^5 + 20*X^3 + 14*X^2 + 17*X + 18,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s35 : XPow fElevenA2 28395943
    (17*X^10 + 19*X^9 + 9*X^8 + 3*X^7 + 16*X^6 + 8*X^5 + 5*X^4 + 6*X^3 + 12*X^2 + 22) :=
  mul_step (by norm_num) pElevenA2s34 pElevenA21 ⟨
    19,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s36 : XPow fElevenA2 56791886
    (19*X^10 + 4*X^9 + 12*X^8 + X^7 + 20*X^6 + 21*X^5 + 4*X^4 + 9*X^3 + 13*X^2 + 3*X + 22) :=
  sq_step (by norm_num) pElevenA2s35 ⟨
    13*X^9 + X^8 + 4*X^7 + 14*X^5 + 4*X^4 + 3*X^3 + 15*X^2 + 15*X + 15,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s37 : XPow fElevenA2 56791887
    (22*X^10 + 20*X^9 + 20*X^8 + 18*X^7 + 22*X^6 + 2*X^5 + 13*X^4 + 18*X^3 + 20*X^2 + 13*X + 22) :=
  mul_step (by norm_num) pElevenA2s36 pElevenA21 ⟨
    19,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s38 : XPow fElevenA2 113583774
    (16*X^10 + 5*X^9 + 7*X^8 + 17*X^7 + 13*X^6 + 19*X^5 + X^3 + 21*X^2 + 8*X + 3) :=
  sq_step (by norm_num) pElevenA2s37 ⟨
    X^9 + 13*X^8 + 12*X^7 + 18*X^6 + 7*X^5 + 6*X^3 + 2*X^2 + 18*X + 8,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s39 : XPow fElevenA2 227167548
    (19*X^10 + 8*X^9 + 8*X^8 + 15*X^7 + 8*X^6 + 14*X^5 + 15*X^4 + 10*X^3 + 6*X^2 + 15*X + 16) :=
  sq_step (by norm_num) pElevenA2s38 ⟨
    3*X^9 + 20*X^8 + 15*X^7 + 15*X^6 + 7*X^5 + 13*X^4 + 21*X^3 + 22*X^2 + 7*X + 5,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s40 : XPow fElevenA2 454335096
    (12*X^10 + 22*X^9 + 3*X^8 + 12*X^7 + 12*X^6 + 22*X^5 + 3*X^4 + 2*X^3 + 14*X^2 + X + 14) :=
  sq_step (by norm_num) pElevenA2s39 ⟨
    16*X^9 + 2*X^8 + 5*X^7 + 9*X^6 + 4*X^5 + 15*X^4 + 21*X^3 + 3*X^2 + 11*X + 21,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s41 : XPow fElevenA2 454335097
    (14*X^10 + 2*X^9 + X^8 + 18*X^7 + 19*X^6 + 9*X^5 + 13*X^4 + 22*X^3 + 19*X^2 + 18*X + 3) :=
  mul_step (by norm_num) pElevenA2s40 pElevenA21 ⟨
    12,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s42 : XPow fElevenA2 908670194
    (14*X^10 + 13*X^9 + 18*X^8 + 14*X^7 + 3*X^6 + 14*X^5 + 7*X^4 + 19*X^3 + 22*X^2 + 19*X + 5) :=
  sq_step (by norm_num) pElevenA2s41 ⟨
    12*X^9 + 2*X^8 + 22*X^7 + 3*X^6 + 15*X^5 + 4*X^3 + 18*X^2 + 18*X + 7,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s43 : XPow fElevenA2 1817340388
    (6*X^10 + 2*X^9 + 4*X^8 + 7*X^6 + 13*X^5 + 22*X^4 + 4*X^3 + 19*X^2 + 18*X + 20) :=
  sq_step (by norm_num) pElevenA2s42 ⟨
    12*X^9 + 11*X^8 + 13*X^7 + 21*X^6 + 13*X^5 + 15*X^4 + 2*X^3 + 6*X^2 + 21*X + 3,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s44 : XPow fElevenA2 1817340389
    (21*X^10 + 15*X^9 + 6*X^8 + 10*X^7 + 2*X^5 + 21*X^4 + 4*X^2 + 22*X + 13) :=
  mul_step (by norm_num) pElevenA2s43 pElevenA21 ⟨
    6,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s45 : XPow fElevenA2 3634680778
    (3*X^10 + 22*X^9 + 13*X^8 + 14*X^7 + X^6 + 10*X^4 + 2*X^3 + 22*X^2 + 13*X) :=
  sq_step (by norm_num) pElevenA2s44 ⟨
    4*X^9 + 14*X^8 + 15*X^7 + 14*X^6 + 6*X^5 + 9*X^4 + 9*X^3 + 4*X^2 + 7*X + 14,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s46 : XPow fElevenA2 7269361556
    (4*X^10 + 11*X^9 + 22*X^8 + 7*X^7 + 7*X^6 + 3*X^5 + 10*X^4 + 5*X^3 + 11*X^2 + 13*X + 11) :=
  sq_step (by norm_num) pElevenA2s45 ⟨
    9*X^9 + 11*X^8 + 22*X^6 + 6*X^5 + X^4 + 19*X^3 + 15*X^2 + X + 21,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s47 : XPow fElevenA2 14538723112
    (10*X^10 + 2*X^9 + 3*X^8 + 11*X^7 + 10*X^6 + 6*X^5 + 6*X^4 + 19*X^3 + 4*X^2 + 5*X + 1) :=
  sq_step (by norm_num) pElevenA2s46 ⟨
    16*X^9 + 16*X^8 + 9*X^7 + 12*X^6 + 2*X^5 + 6*X^4 + 21*X^3 + 19*X^2 + 22*X + 3,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s48 : XPow fElevenA2 29077446224
    (22*X^10 + 17*X^9 + 15*X^7 + 10*X^6 + 20*X^5 + 6*X^4 + 8*X^3 + 21*X^2 + 12*X + 12) :=
  sq_step (by norm_num) pElevenA2s47 ⟨
    8*X^9 + 4*X^8 + 7*X^7 + 5*X^6 + 6*X^5 + 12*X^4 + 6*X^3 + 6*X^2 + 3*X + 21,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s49 : XPow fElevenA2 29077446225
    (10*X^10 + 2*X^9 + 14*X^8 + 21*X^7 + 3*X^6 + 17*X^5 + 9*X^4 + 5*X^3 + 22*X^2 + 4*X + 17) :=
  mul_step (by norm_num) pElevenA2s48 pElevenA21 ⟨
    22,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s50 : XPow fElevenA2 58154892450
    (9*X^10 + 5*X^9 + X^8 + 9*X^7 + 10*X^6 + 17*X^5 + 7*X^3 + 14*X^2 + 22*X + 5) :=
  sq_step (by norm_num) pElevenA2s49 ⟨
    8*X^9 + 4*X^8 + 20*X^7 + 18*X^6 + 20*X^5 + 6*X^4 + X^3 + 15*X^2 + 16*X + 14,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s51 : XPow fElevenA2 116309784900
    (6*X^10 + 20*X^9 + 6*X^8 + 15*X^7 + 11*X^6 + 5*X^5 + 20*X^4 + 20*X^3 + 9*X^2 + 4*X + 12) :=
  sq_step (by norm_num) pElevenA2s50 ⟨
    12*X^9 + 13*X^8 + 18*X^7 + 8*X^6 + 11*X^5 + 12*X^4 + 2*X^3 + 13*X^2 + 18*X + 17,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s52 : XPow fElevenA2 116309784901
    (16*X^10 + 17*X^9 + 21*X^8 + 14*X^7 + 15*X^6 + 14*X^4 + 13*X^3 + 13*X^2 + 14*X + 13) :=
  mul_step (by norm_num) pElevenA2s51 pElevenA21 ⟨
    6,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s53 : XPow fElevenA2 232619569802
    (14*X^10 + 7*X^9 + X^8 + X^7 + X^6 + 11*X^5 + 9*X^4 + 21*X^3 + 12*X^2 + 5*X + 4) :=
  sq_step (by norm_num) pElevenA2s52 ⟨
    3*X^9 + 13*X^8 + 11*X^7 + 20*X^6 + 11*X^4 + 12*X^3 + 22*X^2 + 19*X + 7,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s54 : XPow fElevenA2 232619569803
    (13*X^10 + 19*X^9 + 15*X^8 + 8*X^7 + 19*X^6 + 16*X^5 + 7*X^4 + 6*X^3 + 3*X^2 + X + 15) :=
  mul_step (by norm_num) pElevenA2s53 pElevenA21 ⟨
    14,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s55 : XPow fElevenA2 465239139606
    (18*X^10 + 21*X^9 + 19*X^8 + 8*X^7 + 9*X^6 + 12*X^5 + 7*X^4 + 8*X^3 + 16*X^2 + X + 5) :=
  sq_step (by norm_num) pElevenA2s54 ⟨
    8*X^9 + 21*X^8 + 8*X^7 + 18*X^6 + 8*X^5 + 20*X^3 + 18*X^2 + 7*X + 17,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s56 : XPow fElevenA2 930478279212
    (22*X^10 + 13*X^9 + 18*X^8 + 6*X^7 + 7*X^6 + 5*X^5 + 2*X^4 + 18*X^3 + 17*X^2 + 5*X + 9) :=
  sq_step (by norm_num) pElevenA2s55 ⟨
    2*X^9 + 11*X^8 + 2*X^7 + 22*X^6 + 10*X^5 + 20*X^4 + 21*X^3 + 2*X^2 + 4*X + 5,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s57 : XPow fElevenA2 1860956558424
    (10*X^10 + 9*X^9 + 2*X^8 + 10*X^7 + 10*X^6 + 17*X^5 + 4*X^4 + 20*X^3 + 13*X^2 + 19*X + 11) :=
  sq_step (by norm_num) pElevenA2s56 ⟨
    X^9 + 4*X^8 + 21*X^7 + 21*X^6 + 12*X^5 + 10*X^4 + 8*X^3 + 18*X^2 + 5*X + 19,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s58 : XPow fElevenA2 1860956558425
    (10*X^10 + 5*X^9 + 20*X^8 + 15*X^7 + 3*X^6 + 9*X^5 + 10*X^4 + 12*X^3 + 11*X^2 + 22*X + 14) :=
  mul_step (by norm_num) pElevenA2s57 pElevenA21 ⟨
    10,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s59 : XPow fElevenA2 3721913116850
    (3*X^10 + 14*X^9 + 7*X^8 + 10*X^7 + X^6 + 21*X^5 + 13*X^4 + 10*X^3 + 15*X^2 + 4) :=
  sq_step (by norm_num) pElevenA2s58 ⟨
    8*X^9 + 18*X^8 + 6*X^7 + 8*X^6 + 9*X^5 + 19*X^4 + 13*X^3 + 16*X^2 + 9*X + 14,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s60 : XPow fElevenA2 3721913116851
    (12*X^10 + X^9 + 13*X^8 + 14*X^7 + 3*X^6 + 3*X^5 + 7*X^4 + 17*X^3 + 16*X^2 + 5*X + 18) :=
  mul_step (by norm_num) pElevenA2s59 pElevenA21 ⟨
    3,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s61 : XPow fElevenA2 7443826233702
    (13*X^10 + 6*X^9 + 11*X^8 + 21*X^7 + 18*X^6 + 19*X^5 + 8*X^4 + 11*X^3 + 22*X^2 + 11*X + 8) :=
  sq_step (by norm_num) pElevenA2s60 ⟨
    6*X^9 + 20*X^8 + 4*X^7 + 11*X^6 + 16*X^5 + 4*X^4 + 18*X^3 + 2*X^2 + 5*X + 1,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s62 : XPow fElevenA2 14887652467404
    (21*X^10 + 16*X^9 + 16*X^8 + 19*X^7 + 16*X^6 + 18*X^5 + 12*X^3 + 18*X^2 + 22*X + 20) :=
  sq_step (by norm_num) pElevenA2s61 ⟨
    8*X^9 + 5*X^8 + 19*X^7 + 4*X^6 + 12*X^5 + 14*X^4 + 12*X^3 + 2*X + 8,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s63 : XPow fElevenA2 14887652467405
    (2*X^10 + 20*X^9 + 17*X^8 + 15*X^7 + 7*X^6 + 22*X^5 + 14*X^4 + 9*X^3 + 19*X^2 + 4*X + 11) :=
  mul_step (by norm_num) pElevenA2s62 pElevenA21 ⟨
    21,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s64 : XPow fElevenA2 29775304934810
    (16*X^10 + 2*X^9 + 4*X^8 + 20*X^7 + 17*X^6 + 6*X^5 + 2*X^4 + 6*X^3 + 9*X^2 + 8*X + 11) :=
  sq_step (by norm_num) pElevenA2s63 ⟨
    4*X^9 + 16*X^8 + 20*X^7 + X^6 + 5*X^5 + 18*X^4 + 6*X^3 + 12*X^2 + 6*X + 20,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s65 : XPow fElevenA2 59550609869620
    (11*X^9 + 14*X^8 + 8*X^7 + 5*X^6 + 3*X^5 + 16*X^4 + 7*X^3 + 17*X^2 + 11*X + 9) :=
  sq_step (by norm_num) pElevenA2s64 ⟨
    3*X^9 + 16*X^8 + 8*X^7 + 16*X^6 + 6*X^5 + 14*X^4 + 3*X^3 + 18*X^2 + 14*X + 12,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s66 : XPow fElevenA2 119101219739240
    (12*X^10 + 8*X^9 + 14*X^8 + 19*X^6 + 21*X^5 + 4*X^4 + 6*X^3 + 22*X^2 + 3*X + 3) :=
  sq_step (by norm_num) pElevenA2s65 ⟨
    6*X^7 + 5*X^6 + 4*X^5 + 13*X^4 + 16*X^3 + 9*X^2 + 4*X + 10,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s67 : XPow fElevenA2 238202439478480
    (19*X^10 + 18*X^9 + 19*X^7 + 14*X^6 + 12*X^5 + 22*X^4 + 7*X^3 + 14*X^2 + 16*X + 21) :=
  sq_step (by norm_num) pElevenA2s66 ⟨
    6*X^9 + 4*X^8 + 2*X^7 + 6*X^6 + 7*X^5 + 8*X^4 + 3*X^3 + 13*X^2 + 20*X + 2,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s68 : XPow fElevenA2 238202439478481
    (13*X^10 + 8*X^9 + 15*X^8 + 12*X^7 + 13*X^6 + 20*X^5 + 11*X^4 + 19*X^3 + 10*X^2 + 12*X + 22) :=
  mul_step (by norm_num) pElevenA2s67 pElevenA21 ⟨
    19,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s69 : XPow fElevenA2 476404878956962
    (4*X^10 + 18*X^9 + 8*X^8 + 19*X^7 + 21*X^6 + X^5 + 21*X^4 + 4*X^3 + 5*X^2 + 17*X + 14) :=
  sq_step (by norm_num) pElevenA2s68 ⟨
    8*X^9 + 11*X^8 + 9*X^7 + 3*X^6 + 14*X^5 + 8*X^4 + 21*X^3 + 16*X^2 + 18*X + 6,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s70 : XPow fElevenA2 476404878956963
    (1) :=
  mul_step (by norm_num) pElevenA2s69 pElevenA21 ⟨
    4,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s71 : XPow fElevenA2 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenA2s70 ⟨
    0,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA2s72 : XPow fElevenA2 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenA2s71 pElevenA21 ⟨
    0,
    by simp only [fElevenA2]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 3: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenA31 : XPow fElevenA3 1 X := xpow_one _

theorem pElevenA3s0 : XPow fElevenA3 2
    (X^2) :=
  sq_step (by norm_num) pElevenA31 ⟨
    0,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s1 : XPow fElevenA3 3
    (X^3) :=
  mul_step (by norm_num) pElevenA3s0 pElevenA31 ⟨
    0,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s2 : XPow fElevenA3 6
    (X^6) :=
  sq_step (by norm_num) pElevenA3s1 ⟨
    0,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s3 : XPow fElevenA3 12
    (22*X^10 + 16*X^9 + 5*X^8 + 17*X^7 + 14*X^6 + 2*X^5 + 9*X^4 + X^3 + 11*X^2 + 19*X + 12) :=
  sq_step (by norm_num) pElevenA3s2 ⟨
    X + 4,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s4 : XPow fElevenA3 13
    (12*X^10 + 22*X^9 + 2*X^8 + 18*X^6 + 12*X^4 + 4*X^3 + 8*X + 20) :=
  mul_step (by norm_num) pElevenA3s3 pElevenA31 ⟨
    22,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s5 : XPow fElevenA3 26
    (15*X^9 + 4*X^8 + 4*X^7 + 7*X^6 + 7*X^5 + 15*X^4 + 5*X^3 + 13*X^2 + 16*X + 7) :=
  sq_step (by norm_num) pElevenA3s4 ⟨
    6*X^9 + 16*X^7 + 12*X^6 + 20*X^5 + 7*X^4 + 7*X^2 + 12*X + 7,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s6 : XPow fElevenA3 27
    (15*X^10 + 4*X^9 + 4*X^8 + 7*X^7 + 7*X^6 + 15*X^5 + 5*X^4 + 13*X^3 + 16*X^2 + 7*X) :=
  mul_step (by norm_num) pElevenA3s5 pElevenA31 ⟨
    0,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s7 : XPow fElevenA3 54
    (11*X^10 + 5*X^9 + 20*X^8 + 2*X^7 + 7*X^6 + 6*X^5 + 11*X^4 + 11*X^3 + X^2 + 21*X + 10) :=
  sq_step (by norm_num) pElevenA3s6 ⟨
    18*X^9 + 8*X^8 + 8*X^6 + 19*X^5 + 4*X^4 + 15*X^3 + 14*X^2 + 11,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s8 : XPow fElevenA3 108
    (10*X^10 + X^9 + 22*X^8 + X^7 + 3*X^6 + 12*X^5 + 4*X^4 + 14*X^3 + 4*X^2 + 16*X + 14) :=
  sq_step (by norm_num) pElevenA3s7 ⟨
    6*X^9 + 19*X^8 + 2*X^7 + 19*X^6 + 19*X^5 + 5*X^4 + X^3 + 13*X^2 + 16*X + 2,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s9 : XPow fElevenA3 216
    (20*X^10 + 3*X^9 + 8*X^8 + 11*X^7 + 22*X^6 + 4*X^5 + 10*X^4 + 5*X^3 + 7*X^2 + 6*X + 9) :=
  sq_step (by norm_num) pElevenA3s8 ⟨
    8*X^9 + 6*X^8 + 7*X^7 + 18*X^6 + 11*X^5 + 20*X^4 + 14*X^3 + 4*X^2 + 15*X + 22,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s10 : XPow fElevenA3 432
    (8*X^10 + 5*X^9 + 8*X^8 + 5*X^7 + 5*X^6 + 7*X^5 + 3*X^4 + 5*X^3 + 5*X^2 + 14*X + 4) :=
  sq_step (by norm_num) pElevenA3s9 ⟨
    9*X^9 + 18*X^8 + 18*X^7 + 21*X^6 + 11*X^5 + 4*X^4 + 5*X^3 + 5*X^2 + 8*X + 5,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s11 : XPow fElevenA3 433
    (14*X^10 + 10*X^9 + 10*X^8 + 2*X^7 + 17*X^6 + 6*X^5 + 9*X^4 + 15*X^3 + 5*X^2 + 13*X + 1) :=
  mul_step (by norm_num) pElevenA3s10 pElevenA31 ⟨
    8,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s12 : XPow fElevenA3 866
    (10*X^10 + 21*X^9 + 2*X^8 + 13*X^7 + 16*X^6 + 11*X^5 + 16*X^4 + 4*X^3 + 8*X^2 + X + 12) :=
  sq_step (by norm_num) pElevenA3s11 ⟨
    12*X^9 + 6*X^8 + 16*X^7 + 7*X^6 + 9*X^5 + 22*X^4 + 3*X^3 + 3*X^2 + 20*X + 19,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s13 : XPow fElevenA3 1732
    (20*X^10 + X^9 + X^8 + 13*X^6 + 4*X^5 + 20*X^4 + 18*X^3 + 12*X + 7) :=
  sq_step (by norm_num) pElevenA3s12 ⟨
    8*X^9 + 15*X^8 + 14*X^7 + 12*X^6 + 5*X^5 + 17*X^4 + 10*X^3 + 17*X^2 + 16*X + 8,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s14 : XPow fElevenA3 1733
    (12*X^10 + 6*X^9 + X^8 + 17*X^7 + 6*X^6 + 16*X^5 + 5*X^4 + 2*X^3 + X^2 + 18*X + 14) :=
  mul_step (by norm_num) pElevenA3s13 pElevenA31 ⟨
    20,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s15 : XPow fElevenA3 3466
    (11*X^10 + 15*X^9 + 21*X^8 + 21*X^7 + 17*X^6 + 11*X^5 + 18*X^4 + 20*X^2 + 7*X + 18) :=
  sq_step (by norm_num) pElevenA3s14 ⟨
    6*X^9 + 7*X^8 + 9*X^7 + 13*X^6 + 15*X^4 + 16*X^3 + 4*X^2 + 8*X + 2,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s16 : XPow fElevenA3 6932
    (15*X^10 + 18*X^8 + 11*X^7 + 4*X^6 + 17*X^5 + 15*X^4 + 22*X^3 + 6*X^2 + 16*X + 5) :=
  sq_step (by norm_num) pElevenA3s15 ⟨
    6*X^9 + 9*X^8 + 17*X^6 + 7*X^5 + 18*X^3 + 7*X^2 + 12*X + 1,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s17 : XPow fElevenA3 13864
    (11*X^10 + 22*X^9 + 2*X^8 + 3*X^7 + 12*X^6 + 17*X^5 + 19*X^4 + 19*X^3 + 2*X^2 + 10*X + 17) :=
  sq_step (by norm_num) pElevenA3s16 ⟨
    18*X^9 + 3*X^8 + 16*X^7 + 15*X^6 + X^4 + 17*X^3 + 21*X^2 + 20*X + 5,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s18 : XPow fElevenA3 13865
    (20*X^10 + 22*X^9 + 7*X^8 + 5*X^7 + 2*X^6 + 3*X^5 + 13*X^4 + 10*X^3 + 12*X^2 + 15*X + 10) :=
  mul_step (by norm_num) pElevenA3s17 pElevenA31 ⟨
    11,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s19 : XPow fElevenA3 27730
    (12*X^9 + 8*X^8 + 7*X^7 + 11*X^6 + 14*X^5 + 17*X^4 + 9*X^2 + 6*X + 18) :=
  sq_step (by norm_num) pElevenA3s18 ⟨
    9*X^9 + 19*X^8 + 20*X^7 + 9*X^6 + 19*X^5 + 2*X^4 + 7*X^3 + 18*X^2 + 10*X + 11,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s20 : XPow fElevenA3 55460
    (15*X^10 + 9*X^9 + 8*X^8 + 6*X^7 + 15*X^6 + 19*X^5 + 9*X^4 + 11*X^2 + 11*X + 21) :=
  sq_step (by norm_num) pElevenA3s19 ⟨
    6*X^7 + 9*X^6 + 5*X^5 + 11*X^4 + 3*X^3 + 3*X^2 + 5*X + 14,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s21 : XPow fElevenA3 110920
    (10*X^10 + 10*X^9 + 15*X^8 + 21*X^7 + 12*X^6 + 5*X^5 + 15*X^4 + 10*X^3 + 3*X^2 + 2*X + 2) :=
  sq_step (by norm_num) pElevenA3s20 ⟨
    18*X^9 + 20*X^8 + 3*X^7 + 13*X^6 + 2*X^5 + X^4 + 17*X^3 + 15*X^2 + 6*X + 7,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s22 : XPow fElevenA3 110921
    (4*X^10 + 6*X^9 + 10*X^8 + 14*X^7 + 6*X^6 + 13*X^5 + 15*X^4 + 4*X^3 + 8*X^2 + 19*X + 7) :=
  mul_step (by norm_num) pElevenA3s21 pElevenA31 ⟨
    10,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s23 : XPow fElevenA3 221842
    (6*X^10 + 4*X^9 + 20*X^8 + 18*X^7 + 10*X^5 + 2*X^4 + 6*X^3 + 13*X^2 + 17*X + 17) :=
  sq_step (by norm_num) pElevenA3s22 ⟨
    16*X^9 + 20*X^8 + 16*X^7 + 12*X^6 + 18*X^5 + 13*X^4 + 14*X^3 + 17*X^2 + 13*X + 20,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s24 : XPow fElevenA3 221843
    (5*X^10 + 10*X^9 + 16*X^8 + 15*X^7 + 6*X^6 + 10*X^5 + 9*X^4 + 9*X^3 + 16*X^2 + 18*X + 18) :=
  mul_step (by norm_num) pElevenA3s23 pElevenA31 ⟨
    6,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s25 : XPow fElevenA3 443686
    (16*X^10 + 9*X^9 + 14*X^8 + X^7 + 21*X^6 + 16*X^5 + 13*X^4 + 11*X^3 + 17*X^2 + 13*X + 20) :=
  sq_step (by norm_num) pElevenA3s24 ⟨
    2*X^9 + 16*X^8 + 14*X^7 + 8*X^6 + 11*X^5 + 21*X^4 + 15*X^3 + 4*X^2 + 18*X + 6,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s26 : XPow fElevenA3 887372
    (3*X^10 + 18*X^9 + 13*X^8 + 20*X^7 + X^6 + 8*X^4 + 12*X^3 + 8*X^2 + 22*X + 15) :=
  sq_step (by norm_num) pElevenA3s25 ⟨
    3*X^9 + X^8 + 22*X^7 + 9*X^6 + 7*X^5 + 8*X^4 + 4*X^3 + 6*X^2 + 2,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s27 : XPow fElevenA3 887373
    (7*X^10 + 8*X^9 + 19*X^8 + 20*X^7 + 21*X^6 + 12*X^5 + 2*X^4 + 6*X^3 + 10*X^2 + 4*X + 9) :=
  mul_step (by norm_num) pElevenA3s26 pElevenA31 ⟨
    3,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s28 : XPow fElevenA3 1774746
    (14*X^10 + 10*X^9 + 22*X^8 + 6*X^7 + 21*X^6 + 14*X^5 + 4*X^4 + 20*X^3 + 15*X^2 + 19*X + 20) :=
  sq_step (by norm_num) pElevenA3s27 ⟨
    3*X^9 + 9*X^8 + 16*X^7 + 11*X^6 + 4*X^5 + 8*X^4 + 21*X^3 + 9*X^2 + 12*X + 18,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s29 : XPow fElevenA3 3549492
    (10*X^10 + 16*X^9 + 3*X^8 + 20*X^7 + 5*X^6 + 5*X^5 + 17*X^4 + 13*X^3 + 21*X^2 + 9*X + 7) :=
  sq_step (by norm_num) pElevenA3s28 ⟨
    12*X^9 + 6*X^8 + 7*X^7 + X^6 + X^5 + 2*X^4 + 19*X^3 + 9*X^2 + X + 7,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s30 : XPow fElevenA3 7098984
    (10*X^9 + 10*X^8 + 17*X^7 + 5*X^6 + 15*X^5 + 17*X^4 + 10*X^3 + 3*X^2 + 4*X + 6) :=
  sq_step (by norm_num) pElevenA3s29 ⟨
    8*X^9 + 7*X^8 + X^7 + 18*X^6 + 9*X^5 + 3*X^4 + 21*X^3 + 10*X^2 + 4*X + 1,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s31 : XPow fElevenA3 7098985
    (10*X^10 + 10*X^9 + 17*X^8 + 5*X^7 + 15*X^6 + 17*X^5 + 10*X^4 + 3*X^3 + 4*X^2 + 6*X) :=
  mul_step (by norm_num) pElevenA3s30 pElevenA31 ⟨
    0,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s32 : XPow fElevenA3 14197970
    (21*X^10 + X^9 + 22*X^8 + 11*X^7 + 2*X^6 + 15*X^5 + 11*X^4 + 14*X^3 + 14*X^2 + 8*X + 17) :=
  sq_step (by norm_num) pElevenA3s31 ⟨
    8*X^9 + 2*X^8 + 13*X^7 + 3*X^6 + X^5 + 7*X^4 + 19*X^3 + 11*X^2 + 13*X + 21,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s33 : XPow fElevenA3 14197971
    (16*X^10 + 10*X^9 + 4*X^8 + 20*X^7 + X^6 + 16*X^5 + 13*X^4 + 16*X^2 + 9*X + 17) :=
  mul_step (by norm_num) pElevenA3s32 pElevenA31 ⟨
    21,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s34 : XPow fElevenA3 28395942
    (11*X^10 + 4*X^9 + 3*X^8 + 15*X^7 + 15*X^6 + 8*X^5 + 14*X^4 + 2*X^3 + 7*X^2 + 11*X + 13) :=
  sq_step (by norm_num) pElevenA3s33 ⟨
    3*X^9 + 10*X^8 + 10*X^7 + 14*X^6 + 20*X^5 + 17*X^4 + 8*X^3 + 12*X^2 + 9*X,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s35 : XPow fElevenA3 28395943
    (2*X^10 + 19*X^8 + 8*X^7 + 16*X^6 + 21*X^5 + 19*X^4 + 15*X^3 + 13*X^2 + 11*X + 10) :=
  mul_step (by norm_num) pElevenA3s34 pElevenA31 ⟨
    11,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s36 : XPow fElevenA3 56791886
    (16*X^10 + 14*X^9 + 3*X^8 + 22*X^7 + 16*X^6 + 10*X^5 + 11*X^4 + 18*X^3 + 5*X^2 + 5*X + 18) :=
  sq_step (by norm_num) pElevenA3s35 ⟨
    4*X^9 + 16*X^8 + 3*X^7 + 16*X^6 + 21*X^5 + 14*X^4 + 3*X^3 + 7*X^2 + 21*X + 11,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s37 : XPow fElevenA3 56791887
    (9*X^10 + 7*X^9 + 9*X^8 + 10*X^7 + 7*X^6 + 17*X^5 + 3*X^4 + 2*X^3 + 10*X^2 + 13*X + 2) :=
  mul_step (by norm_num) pElevenA3s36 pElevenA31 ⟨
    16,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s38 : XPow fElevenA3 113583774
    (14*X^10 + 15*X^9 + 2*X^7 + 20*X^5 + 6*X^4 + 6*X^3 + 9*X^2 + 22*X + 19) :=
  sq_step (by norm_num) pElevenA3s37 ⟨
    12*X^9 + 13*X^8 + 13*X^7 + 18*X^6 + 9*X^5 + 16*X^4 + 22*X^3 + 21*X^2 + 14*X + 5,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s39 : XPow fElevenA3 227167548
    (14*X^10 + 14*X^9 + 14*X^8 + 12*X^7 + 4*X^6 + 12*X^4 + 14*X^3 + 6*X^2 + 10*X + 8) :=
  sq_step (by norm_num) pElevenA3s38 ⟨
    12*X^9 + 8*X^8 + 7*X^7 + 13*X^6 + 5*X^5 + 16*X^4 + 12*X^3 + 2*X^2 + 17*X + 5,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s40 : XPow fElevenA3 454335096
    (11*X^10 + 5*X^9 + 19*X^8 + 4*X^6 + 5*X^5 + 20*X^4 + 22*X^3 + 11*X^2 + 12*X + 15) :=
  sq_step (by norm_num) pElevenA3s39 ⟨
    12*X^9 + 3*X^8 + 5*X^7 + 3*X^6 + 2*X^5 + 8*X^4 + 6*X^3 + X^2 + 21*X + 22,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s41 : XPow fElevenA3 454335097
    (3*X^10 + 16*X^9 + 4*X^8 + 20*X^7 + 13*X^6 + 4*X^5 + 16*X^4 + 19*X^3 + 14*X^2 + 13*X + 10) :=
  mul_step (by norm_num) pElevenA3s40 pElevenA31 ⟨
    11,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s42 : XPow fElevenA3 908670194
    (12*X^10 + 16*X^9 + 8*X^8 + 5*X^7 + 4*X^6 + 9*X^5 + 16*X^4 + 10*X^3 + 7*X^2 + 6*X + 13) :=
  sq_step (by norm_num) pElevenA3s41 ⟨
    9*X^9 + 17*X^8 + 11*X^7 + 8*X^5 + 17*X^4 + 2*X^3 + 21*X^2 + 17,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s43 : XPow fElevenA3 1817340388
    (2*X^10 + 7*X^9 + 11*X^8 + 15*X^7 + 8*X^6 + 14*X^5 + 3*X^4 + 10*X^3 + 13*X^2 + 9*X + 21) :=
  sq_step (by norm_num) pElevenA3s42 ⟨
    6*X^9 + 17*X^8 + 16*X^6 + 10*X^5 + 12*X^4 + 17*X^3 + 19*X^2 + 4*X + 12,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s44 : XPow fElevenA3 1817340389
    (15*X^10 + 22*X^8 + 13*X^7 + 5*X^6 + 21*X^5 + 11*X^4 + 4*X^3 + X^2 + 6*X + 6) :=
  mul_step (by norm_num) pElevenA3s43 pElevenA31 ⟨
    2,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s45 : XPow fElevenA3 3634680778
    (16*X^10 + 20*X^9 + 20*X^8 + 18*X^7 + 3*X^6 + 14*X^5 + 14*X^3 + 12*X^2 + 14*X + 14) :=
  sq_step (by norm_num) pElevenA3s44 ⟨
    18*X^9 + 3*X^8 + 21*X^7 + 3*X^6 + 11*X^5 + 22*X^4 + 15*X^3 + 8*X^2 + 16*X + 8,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s46 : XPow fElevenA3 7269361556
    (19*X^10 + 9*X^9 + 19*X^8 + 8*X^7 + 10*X^6 + 17*X^5 + 21*X^4 + 5*X^3 + 21*X^2 + X + 4) :=
  sq_step (by norm_num) pElevenA3s45 ⟨
    3*X^9 + 8*X^8 + 9*X^7 + 10*X^6 + 6*X^4 + 7*X^3 + 19*X^2 + X + 5,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s47 : XPow fElevenA3 14538723112
    (10*X^10 + 2*X^9 + 7*X^8 + 2*X^7 + 19*X^6 + 2*X^5 + 21*X^4 + 13*X^3 + 4*X^2 + 3*X + 12) :=
  sq_step (by norm_num) pElevenA3s46 ⟨
    16*X^9 + 15*X^8 + 16*X^7 + 5*X^6 + X^5 + X^4 + 13*X^3 + X^2 + 18*X + 14,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s48 : XPow fElevenA3 29077446224
    (19*X^10 + 10*X^9 + 18*X^8 + X^7 + 6*X^6 + 14*X^5 + 16*X^4 + 7*X^3 + 22*X^2 + 22*X + 9) :=
  sq_step (by norm_num) pElevenA3s47 ⟨
    8*X^9 + 3*X^8 + 20*X^7 + 10*X^6 + 18*X^5 + 7*X^4 + 13*X^2 + 5*X + 1,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s49 : XPow fElevenA3 29077446225
    (17*X^10 + 17*X^9 + 10*X^8 + 19*X^7 + 9*X^6 + 3*X^5 + 5*X^4 + 17*X^3 + 15*X^2 + 16*X + 11) :=
  mul_step (by norm_num) pElevenA3s48 pElevenA31 ⟨
    19,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s50 : XPow fElevenA3 58154892450
    (20*X^10 + 21*X^9 + 12*X^8 + 16*X^7 + 2*X^6 + 14*X^5 + 2*X^4 + 10*X^3 + 8*X^2 + 2*X + 4) :=
  sq_step (by norm_num) pElevenA3s49 ⟨
    13*X^9 + 9*X^8 + 7*X^7 + 21*X^6 + 17*X^4 + 2*X^3 + 12*X + 7,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s51 : XPow fElevenA3 116309784900
    (19*X^10 + 6*X^9 + 7*X^8 + 22*X^7 + 14*X^6 + 12*X^5 + 7*X^4 + 9*X^3 + 18*X^2 + 18*X) :=
  sq_step (by norm_num) pElevenA3s50 ⟨
    9*X^9 + 2*X^8 + 17*X^7 + 2*X^6 + 12*X^5 + 8*X^4 + 13*X^3 + 11*X^2 + 18*X + 10,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s52 : XPow fElevenA3 116309784901
    (13*X^10 + 6*X^9 + 8*X^8 + 4*X^7 + 7*X^6 + 17*X^5 + 7*X^4 + 13*X^3 + 11*X^2 + 7*X + 11) :=
  mul_step (by norm_num) pElevenA3s51 pElevenA31 ⟨
    19,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s53 : XPow fElevenA3 232619569802
    (13*X^10 + 22*X^9 + 10*X^8 + 10*X^7 + 10*X^6 + 21*X^5 + 14*X^4 + 12*X^3 + 3*X^2 + 7*X + 10) :=
  sq_step (by norm_num) pElevenA3s52 ⟨
    8*X^9 + 4*X^8 + 9*X^7 + 12*X^6 + 16*X^5 + 7*X^4 + 9*X^3 + 5*X^2 + 8*X + 9,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s54 : XPow fElevenA3 232619569803
    (5*X^10 + 19*X^9 + 21*X^8 + 8*X^7 + 20*X^6 + 16*X^5 + 7*X^4 + 2*X^3 + X^2 + 16*X + 16) :=
  mul_step (by norm_num) pElevenA3s53 pElevenA31 ⟨
    13,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s55 : XPow fElevenA3 465239139606
    (8*X^10 + 12*X^9 + 2*X^8 + 4*X^7 + 14*X^6 + 9*X^5 + 2*X^4 + 5*X^3 + 19*X^2 + 22*X + 2) :=
  sq_step (by norm_num) pElevenA3s54 ⟨
    2*X^9 + 14*X^8 + 18*X^7 + 6*X^6 + 4*X^5 + 17*X^4 + 16*X^3 + X^2 + 16*X + 15,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s56 : XPow fElevenA3 930478279212
    (13*X^10 + X^9 + 17*X^8 + 4*X^7 + 21*X^6 + 21*X^5 + 21*X^4 + 9*X^3 + X + 14) :=
  sq_step (by norm_num) pElevenA3s55 ⟨
    18*X^9 + 11*X^8 + 6*X^7 + 12*X^6 + 20*X^5 + 6*X^4 + X^3 + 14*X^2 + 10*X + 11,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s57 : XPow fElevenA3 1860956558424
    (22*X^10 + 22*X^9 + 19*X^8 + X^7 + 18*X^6 + 18*X^5 + 14*X^4 + X^3 + 4*X^2 + 4*X + 14) :=
  sq_step (by norm_num) pElevenA3s56 ⟨
    8*X^9 + 12*X^8 + 10*X^7 + 2*X^6 + 7*X^5 + 11*X^4 + 5*X^3 + 18*X^2 + 9*X + 16,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s58 : XPow fElevenA3 1860956558425
    (18*X^10 + 13*X^9 + 9*X^8 + 4*X^7 + 11*X^6 + 5*X^5 + 12*X^4 + 20*X^3 + 8*X^2 + 10*X + 20) :=
  mul_step (by norm_num) pElevenA3s57 pElevenA31 ⟨
    22,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s59 : XPow fElevenA3 3721913116850
    (3*X^10 + 17*X^9 + 19*X^8 + 9*X^7 + 5*X^6 + 3*X^5 + 8*X^4 + 20*X^3 + 8*X^2 + 20*X + 9) :=
  sq_step (by norm_num) pElevenA3s58 ⟨
    2*X^9 + 16*X^8 + 17*X^7 + 20*X^6 + 19*X^5 + 8*X^4 + 3*X^3 + 6*X^2 + 19*X,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s60 : XPow fElevenA3 3721913116851
    (6*X^10 + 14*X^9 + 8*X^8 + X^7 + X^6 + 12*X^5 + 10*X^4 + 6*X^3 + 8*X^2 + 21*X + 9) :=
  mul_step (by norm_num) pElevenA3s59 pElevenA31 ⟨
    3,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s61 : XPow fElevenA3 7443826233702
    (19*X^10 + 8*X^9 + 5*X^8 + 20*X^7 + 11*X^6 + 9*X^5 + 10*X^4 + 20*X^3 + 17*X^2 + 4*X + 12) :=
  sq_step (by norm_num) pElevenA3s60 ⟨
    13*X^9 + 13*X^8 + 8*X^7 + 12*X^6 + 2*X^5 + 17*X^4 + 18*X^3 + 5*X^2 + 21*X,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s62 : XPow fElevenA3 14887652467404
    (17*X^10 + 7*X^9 + 7*X^8 + 17*X^7 + 2*X^5 + 2*X^4 + 7*X^3 + 21*X^2 + 22*X + 21) :=
  sq_step (by norm_num) pElevenA3s61 ⟨
    16*X^9 + 5*X^7 + 19*X^6 + 12*X^5 + 9*X^4 + 8*X^3 + X^2 + 7*X + 5,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s63 : XPow fElevenA3 14887652467405
    (6*X^10 + 17*X^9 + 19*X^8 + 8*X^7 + 6*X^6 + 17*X^5 + 4*X^4 + 2*X^3 + 20*X + 5) :=
  mul_step (by norm_num) pElevenA3s62 pElevenA31 ⟨
    17,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s64 : XPow fElevenA3 29775304934810
    (21*X^10 + 13*X^9 + 15*X^8 + 22*X^7 + 22*X^6 + 16*X^5 + 7*X^4 + 9*X^3 + 9*X^2 + 9*X + 20) :=
  sq_step (by norm_num) pElevenA3s63 ⟨
    13*X^9 + 3*X^8 + 9*X^7 + 2*X^6 + 5*X^5 + 9*X^2 + 5*X + 6,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s65 : XPow fElevenA3 59550609869620
    (22*X^10 + 12*X^9 + 10*X^8 + 18*X^7 + 6*X^6 + 20*X^5 + 5*X^4 + 18*X^3 + 4*X^2 + 11*X + 9) :=
  sq_step (by norm_num) pElevenA3s64 ⟨
    4*X^9 + 10*X^8 + 12*X^7 + 10*X^6 + 15*X^5 + 3*X^4 + 11*X^3 + 12*X^2 + 14*X,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s66 : XPow fElevenA3 119101219739240
    (2*X^10 + 16*X^9 + 8*X^8 + 10*X^7 + 18*X^6 + 16*X^5 + 17*X^3 + 16*X^2 + 9*X + 5) :=
  sq_step (by norm_num) pElevenA3s65 ⟨
    X^9 + 3*X^8 + 4*X^7 + 5*X^5 + 18*X^4 + 21*X^3 + 22*X^2 + 4*X + 13,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s67 : XPow fElevenA3 238202439478480
    (6*X^10 + 17*X^9 + 12*X^8 + X^7 + 21*X^6 + 15*X^5 + 6*X^4 + 14*X^3 + 14*X^2 + 21*X + 10) :=
  sq_step (by norm_num) pElevenA3s66 ⟨
    4*X^9 + 11*X^8 + 11*X^7 + 6*X^6 + 8*X^5 + 19*X^4 + X^3 + 11*X^2 + 22*X + 18,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s68 : XPow fElevenA3 238202439478481
    (18*X^10 + 2*X^9 + 22*X^8 + 13*X^7 + 11*X^6 + 14*X^5 + 17*X^4 + 10*X^3 + 20*X^2 + 11*X + 18) :=
  mul_step (by norm_num) pElevenA3s67 pElevenA31 ⟨
    6,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s69 : XPow fElevenA3 476404878956962
    (8*X^10 + 14*X^9 + 21*X^8 + 18*X^7 + 3*X^6 + 13*X^5 + 20*X^4 + 19*X^3 + 13*X^2 + 9*X + 14) :=
  sq_step (by norm_num) pElevenA3s68 ⟨
    2*X^9 + 11*X^8 + X^7 + 12*X^6 + 6*X^5 + 19*X^4 + 20*X^3 + 3*X^2 + 19*X + 4,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s70 : XPow fElevenA3 476404878956963
    (1) :=
  mul_step (by norm_num) pElevenA3s69 pElevenA31 ⟨
    8,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s71 : XPow fElevenA3 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenA3s70 ⟨
    0,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA3s72 : XPow fElevenA3 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenA3s71 pElevenA31 ⟨
    0,
    by simp only [fElevenA3]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 4: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenA41 : XPow fElevenA4 1 X := xpow_one _

theorem pElevenA4s0 : XPow fElevenA4 2
    (X^2) :=
  sq_step (by norm_num) pElevenA41 ⟨
    0,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s1 : XPow fElevenA4 3
    (X^3) :=
  mul_step (by norm_num) pElevenA4s0 pElevenA41 ⟨
    0,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s2 : XPow fElevenA4 6
    (X^6) :=
  sq_step (by norm_num) pElevenA4s1 ⟨
    0,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s3 : XPow fElevenA4 12
    (10*X^10 + 15*X^9 + 20*X^8 + 17*X^7 + 19*X^6 + 2*X^5 + 7*X^4 + 10*X^3 + 12*X^2 + 10*X + 6) :=
  sq_step (by norm_num) pElevenA4s2 ⟨
    X + 3,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s4 : XPow fElevenA4 13
    (22*X^10 + 7*X^9 + 22*X^8 + 20*X^7 + 8*X^6 + 18*X^5 + 20*X^4 + 6*X^3 + 13*X^2 + 2*X + 20) :=
  mul_step (by norm_num) pElevenA4s3 pElevenA41 ⟨
    10,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s5 : XPow fElevenA4 26
    (14*X^10 + 13*X^9 + 2*X^8 + 21*X^7 + 20*X^6 + 13*X^5 + 19*X^4 + 20*X^2 + 18*X) :=
  sq_step (by norm_num) pElevenA4s4 ⟨
    X^9 + 12*X^8 + 19*X^7 + 4*X^6 + 10*X^5 + 10*X^4 + 18*X^3 + 3*X^2 + 21*X + 7,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s6 : XPow fElevenA4 27
    (9*X^10 + 16*X^9 + 5*X^8 + 3*X^7 + 3*X^6 + 16*X^5 + 14*X^4 + 7*X^3 + 13*X^2 + 22*X + 5) :=
  mul_step (by norm_num) pElevenA4s5 pElevenA41 ⟨
    14,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s7 : XPow fElevenA4 54
    (3*X^10 + 11*X^9 + 14*X^8 + 8*X^7 + 16*X^6 + 22*X^5 + 19*X^4 + 12*X^3 + 17*X^2 + 22*X + 22) :=
  sq_step (by norm_num) pElevenA4s6 ⟨
    12*X^9 + 2*X^8 + 19*X^7 + 3*X^6 + 12*X^5 + 3*X^4 + 21*X^2 + 18*X + 10,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s8 : XPow fElevenA4 108
    (4*X^9 + 14*X^8 + 19*X^7 + 18*X^5 + 7*X^4 + 19*X^3 + 16*X^2 + 4*X + 9) :=
  sq_step (by norm_num) pElevenA4s7 ⟨
    9*X^9 + X^8 + 10*X^7 + 12*X^6 + 14*X^5 + 2*X^4 + 9*X^3 + 10*X^2 + 11*X + 4,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s9 : XPow fElevenA4 216
    (12*X^10 + X^9 + 6*X^8 + 20*X^7 + 16*X^6 + 4*X^5 + 8*X^4 + 14*X^3 + 2*X^2 + 12*X + 9) :=
  sq_step (by norm_num) pElevenA4s8 ⟨
    16*X^7 + 22*X^6 + 16*X^5 + 12*X^4 + 13*X^3 + 19*X^2 + 18*X + 10,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s10 : XPow fElevenA4 432
    (17*X^10 + 4*X^9 + 10*X^8 + 22*X^7 + 18*X^6 + 2*X^5 + 21*X^4 + 8*X^3 + 20*X^2 + 2*X + 22) :=
  sq_step (by norm_num) pElevenA4s9 ⟨
    6*X^9 + 19*X^8 + X^7 + 11*X^6 + 5*X^5 + 9*X^4 + 15*X^3 + 5*X^2 + 9*X + 5,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s11 : XPow fElevenA4 433
    (9*X^10 + 4*X^9 + 19*X^8 + 22*X^7 + 3*X^6 + 19*X^5 + 2*X^4 + 19*X^3 + 14*X^2 + 6*X + 11) :=
  mul_step (by norm_num) pElevenA4s10 pElevenA41 ⟨
    17,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s12 : XPow fElevenA4 866
    (X^10 + 19*X^9 + 17*X^8 + 6*X^7 + 3*X^6 + 4*X^5 + X^4 + 15*X^2 + 19*X + 10) :=
  sq_step (by norm_num) pElevenA4s11 ⟨
    12*X^9 + 16*X^8 + 4*X^7 + 7*X^6 + 18*X^5 + 18*X^4 + 13*X^3 + 2*X^2 + 6*X + 2,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s13 : XPow fElevenA4 1732
    (14*X^10 + 4*X^9 + 20*X^7 + 22*X^6 + 11*X^5 + 21*X^4 + 9*X^3 + 20*X^2 + 13*X + 22) :=
  sq_step (by norm_num) pElevenA4s12 ⟨
    X^9 + 18*X^8 + 13*X^7 + 14*X^6 + 19*X^5 + 8*X^4 + X^3 + 19*X^2 + 18*X + 7,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s14 : XPow fElevenA4 1733
    (14*X^9 + 4*X^8 + 5*X^7 + X^6 + 18*X^5 + 7*X^3 + 8*X^2 + 21*X + 5) :=
  mul_step (by norm_num) pElevenA4s13 pElevenA41 ⟨
    14,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s15 : XPow fElevenA4 3466
    (18*X^10 + 4*X^9 + 22*X^8 + 15*X^7 + 14*X^6 + 8*X^5 + 22*X^4 + 11*X^3 + 22*X^2 + 12*X + 12) :=
  sq_step (by norm_num) pElevenA4s14 ⟨
    12*X^7 + 10*X^6 + 14*X^5 + 11*X^4 + 6*X^3 + 5*X^2 + 17*X + 5,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s16 : XPow fElevenA4 6932
    (6*X^10 + 5*X^9 + 4*X^8 + 7*X^7 + 21*X^6 + 9*X^5 + X^4 + 15*X^3 + 4*X^2 + 12*X + 2) :=
  sq_step (by norm_num) pElevenA4s15 ⟨
    2*X^9 + 12*X^8 + 18*X^7 + X^6 + 22*X^5 + 16*X^4 + 10*X^3 + 8*X^2 + 18*X + 21,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s17 : XPow fElevenA4 13864
    (18*X^10 + 9*X^9 + 21*X^8 + X^7 + 2*X^6 + 3*X^5 + 10*X^4 + 4*X^3 + 6*X^2 + 18*X + 15) :=
  sq_step (by norm_num) pElevenA4s16 ⟨
    13*X^9 + 7*X^8 + 15*X^7 + 10*X^6 + 6*X^5 + 4*X^4 + 17*X^3 + 3*X^2 + 16*X + 17,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s18 : XPow fElevenA4 13865
    (17*X^10 + 16*X^9 + 10*X^8 + 13*X^7 + 16*X^5 + 22*X^4 + 9*X^3 + 5*X^2 + 17*X + 13) :=
  mul_step (by norm_num) pElevenA4s17 pElevenA41 ⟨
    18,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s19 : XPow fElevenA4 27730
    (20*X^10 + 11*X^9 + 6*X^8 + 17*X^7 + 19*X^6 + 7*X^5 + 13*X^3 + 17*X^2 + 7*X + 3) :=
  sq_step (by norm_num) pElevenA4s18 ⟨
    13*X^9 + 8*X^8 + 12*X^7 + 19*X^6 + 13*X^5 + 21*X^4 + 3*X^3 + 22*X^2 + 12*X + 9,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s20 : XPow fElevenA4 55460
    (14*X^10 + 15*X^9 + 2*X^8 + 20*X^7 + 14*X^6 + 9*X^5 + 3*X^4 + 10*X^3 + 16*X^2 + 9*X + 15) :=
  sq_step (by norm_num) pElevenA4s19 ⟨
    9*X^9 + 7*X^8 + 7*X^6 + 4*X^5 + 14*X^4 + 17*X^3 + 5*X^2 + 14*X + 3,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s21 : XPow fElevenA4 110920
    (19*X^10 + 10*X^9 + 10*X^8 + 21*X^7 + 12*X^6 + 4*X^5 + 21*X^4 + 18*X^3 + 21*X^2 + 6*X + 14) :=
  sq_step (by norm_num) pElevenA4s20 ⟨
    12*X^9 + 19*X^8 + 5*X^7 + 16*X^6 + 4*X^5 + 5*X^4 + 18*X^3 + 18*X^2 + X + 21,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s22 : XPow fElevenA4 110921
    (21*X^10 + 6*X^9 + 19*X^8 + 7*X^7 + 20*X^6 + 12*X^5 + 14*X^4 + 5*X^3 + 14*X^2 + 11*X + 15) :=
  mul_step (by norm_num) pElevenA4s21 pElevenA41 ⟨
    19,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s23 : XPow fElevenA4 221842
    (16*X^10 + 10*X^9 + 21*X^7 + X^6 + 4*X^5 + 20*X^4 + 4*X^3 + X^2 + 20*X + 11) :=
  sq_step (by norm_num) pElevenA4s22 ⟨
    4*X^9 + 11*X^8 + 20*X^7 + 20*X^6 + 7*X^5 + 18*X^4 + 15*X^3 + 10*X^2 + 3*X + 8,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s24 : XPow fElevenA4 221843
    (12*X^10 + 16*X^9 + 6*X^8 + 21*X^7 + 9*X^6 + 10*X^5 + 20*X^4 + 19*X^3 + 11*X^2 + 9) :=
  mul_step (by norm_num) pElevenA4s23 pElevenA41 ⟨
    16,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s25 : XPow fElevenA4 443686
    (15*X^10 + X^9 + 5*X^8 + 6*X^7 + 21*X^6 + 6*X^5 + 12*X^4 + 10*X^3 + 7*X^2 + 6) :=
  sq_step (by norm_num) pElevenA4s24 ⟨
    6*X^9 + 11*X^8 + 2*X^7 + 3*X^6 + 5*X^5 + X^4 + 8*X^3 + 15*X^2 + 4*X + 20,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s26 : XPow fElevenA4 887372
    (22*X^10 + 21*X^9 + 21*X^8 + 5*X^7 + 20*X^6 + 13*X^5 + 8*X^4 + 5*X^3 + 16*X^2 + 10*X + 15) :=
  sq_step (by norm_num) pElevenA4s25 ⟨
    18*X^9 + 15*X^8 + 7*X^7 + 5*X^6 + 6*X^5 + 8*X^4 + 13*X^3 + 3*X^2 + 19*X + 1,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s27 : XPow fElevenA4 887373
    (18*X^10 + 20*X^9 + 16*X^8 + 13*X^7 + 17*X^6 + 4*X^4 + 12*X^3 + 12*X^2 + 20*X + 21) :=
  mul_step (by norm_num) pElevenA4s26 pElevenA41 ⟨
    22,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s28 : XPow fElevenA4 1774746
    (X^10 + 6*X^9 + 10*X^8 + 10*X^7 + 8*X^6 + 7*X^5 + 5*X^4 + 17*X^3 + 20*X^2 + 7*X + 6) :=
  sq_step (by norm_num) pElevenA4s27 ⟨
    2*X^9 + 13*X^8 + 5*X^7 + 10*X^6 + 6*X^5 + 2*X^4 + 22*X^3 + 19*X^2 + 1,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s29 : XPow fElevenA4 3549492
    (15*X^10 + 5*X^9 + 7*X^7 + 6*X^5 + X^4 + 20*X^3 + 20*X^2 + 14*X + 17) :=
  sq_step (by norm_num) pElevenA4s28 ⟨
    X^9 + 15*X^8 + 10*X^7 + 13*X^6 + 12*X^5 + 5*X^4 + 3*X^3 + 11*X^2 + 16*X + 2,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s30 : XPow fElevenA4 7098984
    (9*X^10 + 8*X^9 + 10*X^8 + 21*X^7 + 19*X^6 + 11*X^5 + 10*X^4 + 7*X^3 + X^2 + 20*X + 21) :=
  sq_step (by norm_num) pElevenA4s29 ⟨
    18*X^9 + 20*X^8 + 11*X^7 + 19*X^6 + 21*X^5 + 2*X^4 + 6*X^3 + 22*X^2 + 12*X + 4,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s31 : XPow fElevenA4 7098985
    (12*X^10 + 19*X^9 + 14*X^8 + 13*X^7 + 21*X^6 + 13*X^5 + 16*X^4 + 14*X^3 + 2*X^2 + 22*X + 18) :=
  mul_step (by norm_num) pElevenA4s30 pElevenA41 ⟨
    9,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s32 : XPow fElevenA4 14197970
    (9*X^10 + 17*X^9 + 8*X^8 + 18*X^7 + 20*X^6 + 15*X^5 + X^4 + 18*X^3 + 16*X^2 + 3*X + 9) :=
  sq_step (by norm_num) pElevenA4s31 ⟨
    6*X^9 + 14*X^8 + 9*X^7 + 14*X^6 + 6*X^5 + 9*X^4 + 5*X^3 + 14*X^2 + 11*X + 15,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s33 : XPow fElevenA4 14197971
    (21*X^10 + 17*X^9 + 11*X^8 + 14*X^7 + 2*X^6 + 4*X^5 + 4*X^4 + 6*X^3 + 8*X^2 + 10*X + 18) :=
  mul_step (by norm_num) pElevenA4s32 pElevenA41 ⟨
    9,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s34 : XPow fElevenA4 28395942
    (15*X^10 + 16*X^9 + 20*X^8 + 19*X^7 + 15*X^6 + 2*X^5 + 5*X^3 + 22*X^2 + 3*X) :=
  sq_step (by norm_num) pElevenA4s33 ⟨
    4*X^9 + 13*X^8 + 12*X^7 + X^6 + 6*X^5 + 5*X^3 + 19*X^2 + 3*X + 22,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s35 : XPow fElevenA4 28395943
    (15*X^10 + 12*X^9 + 15*X^8 + 5*X^7 + 11*X^6 + 5*X^5 + 20*X^4 + 13*X^3 + 19*X^2 + 17*X + 7) :=
  mul_step (by norm_num) pElevenA4s34 pElevenA41 ⟨
    15,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s36 : XPow fElevenA4 56791886
    (8*X^10 + 12*X^9 + 11*X^8 + 16*X^7 + 5*X^6 + 18*X^5 + 8*X^4 + 19*X^3 + 3*X^2 + 5*X + 11) :=
  sq_step (by norm_num) pElevenA4s35 ⟨
    18*X^9 + 14*X^7 + 9*X^6 + 14*X^5 + 21*X^4 + 7*X^3 + 8*X^2 + 20*X + 4,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s37 : XPow fElevenA4 56791887
    (13*X^10 + 19*X^9 + 20*X^8 + 15*X^7 + 9*X^6 + 3*X^5 + 4*X^4 + 12*X^3 + 12*X^2 + 17*X + 16) :=
  mul_step (by norm_num) pElevenA4s36 pElevenA41 ⟨
    8,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s38 : XPow fElevenA4 113583774
    (3*X^10 + 7*X^9 + 10*X^8 + 16*X^6 + 10*X^5 + 2*X^4 + X^3 + 21*X^2 + 13*X + 11) :=
  sq_step (by norm_num) pElevenA4s37 ⟨
    8*X^9 + 12*X^8 + 5*X^7 + 8*X^6 + 7*X^5 + 11*X^4 + X^3 + 11*X^2 + 9*X + 4,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s39 : XPow fElevenA4 227167548
    (14*X^10 + 17*X^9 + 7*X^8 + 18*X^7 + 16*X^5 + 15*X^4 + 2*X^3 + 15*X + 5) :=
  sq_step (by norm_num) pElevenA4s38 ⟨
    9*X^9 + 3*X^7 + 4*X^6 + 21*X^5 + 6*X^4 + 8*X^3 + 12*X^2 + 7*X + 11,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s40 : XPow fElevenA4 454335096
    (4*X^10 + 21*X^9 + 14*X^8 + 18*X^7 + 12*X^6 + 4*X^5 + 7*X^4 + 11*X^3 + 20*X^2 + 4*X + 2) :=
  sq_step (by norm_num) pElevenA4s39 ⟨
    12*X^9 + 6*X^8 + 9*X^7 + 22*X^6 + 18*X^5 + 4*X^4 + 15*X^3 + 14*X^2 + 19*X,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s41 : XPow fElevenA4 454335097
    (10*X^10 + 18*X^9 + 20*X^8 + 17*X^7 + 11*X^6 + 16*X^5 + 15*X^4 + 13*X^3 + 19*X^2 + 5*X + 8) :=
  mul_step (by norm_num) pElevenA4s40 pElevenA41 ⟨
    4,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s42 : XPow fElevenA4 908670194
    (16*X^10 + 2*X^9 + 10*X^7 + 9*X^6 + 4*X^5 + 15*X^4 + 2*X^3 + 2*X^2 + 19*X + 15) :=
  sq_step (by norm_num) pElevenA4s41 ⟨
    8*X^9 + 16*X^8 + 21*X^7 + 16*X^6 + 8*X^5 + 20*X^4 + 11*X^3 + 11*X^2 + 6*X + 10,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s43 : XPow fElevenA4 1817340388
    (13*X^10 + 5*X^9 + 8*X^8 + 4*X^7 + 22*X^6 + 11*X^5 + 8*X^4 + 7*X^3 + 9*X^2 + 7*X + 1) :=
  sq_step (by norm_num) pElevenA4s42 ⟨
    3*X^9 + 4*X^8 + 19*X^7 + 3*X^6 + 11*X^5 + 7*X^4 + 9*X^2 + 2*X + 3,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s44 : XPow fElevenA4 1817340389
    (21*X^10 + 21*X^9 + 22*X^8 + 21*X^7 + 5*X^6 + 20*X^5 + 20*X^4 + 15*X^3 + 4*X^2 + 5*X + 3) :=
  mul_step (by norm_num) pElevenA4s43 pElevenA41 ⟨
    13,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s45 : XPow fElevenA4 3634680778
    (5*X^10 + 11*X^9 + 15*X^8 + 7*X^7 + X^6 + 14*X^5 + 22*X^4 + 8*X^3 + 6*X^2 + 19*X + 2) :=
  sq_step (by norm_num) pElevenA4s44 ⟨
    4*X^9 + 20*X^8 + 3*X^7 + 20*X^6 + 21*X^5 + 9*X^4 + 3*X^3 + 17*X^2 + 3*X + 8,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s46 : XPow fElevenA4 7269361556
    (8*X^10 + 5*X^8 + 7*X^7 + 21*X^6 + 20*X^5 + 11*X^4 + 3*X^3 + 3*X^2 + 3*X + 12) :=
  sq_step (by norm_num) pElevenA4s45 ⟨
    2*X^9 + X^8 + 11*X^6 + 11*X^5 + X^4 + 6*X^3 + 17*X^2 + 8*X + 4,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s47 : XPow fElevenA4 14538723112
    (20*X^10 + 6*X^9 + X^8 + 13*X^7 + 13*X^6 + 11*X^5 + 5*X^4 + X^3 + 12*X^2 + 18*X + 3) :=
  sq_step (by norm_num) pElevenA4s46 ⟨
    18*X^9 + 8*X^8 + 7*X^7 + 12*X^6 + 5*X^5 + 2*X^4 + 15*X^3 + 5*X^2 + 21*X + 10,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s48 : XPow fElevenA4 29077446224
    (18*X^10 + 6*X^9 + 19*X^8 + 2*X^7 + 12*X^6 + 5*X^5 + 12*X^4 + 15*X^3 + 4*X^2 + 13*X + 21) :=
  sq_step (by norm_num) pElevenA4s47 ⟨
    9*X^9 + 14*X^8 + 12*X^7 + 6*X^3 + 22*X^2 + 2*X + 6,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s49 : XPow fElevenA4 29077446225
    (14*X^10 + 14*X^9 + 11*X^8 + 2*X^6 + 18*X^5 + 10*X^4 + 7*X^3 + 13) :=
  mul_step (by norm_num) pElevenA4s48 pElevenA41 ⟨
    18,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s50 : XPow fElevenA4 58154892450
    (15*X^10 + 21*X^9 + 11*X^8 + 5*X^6 + 16*X^5 + 7*X^4 + 11*X^3 + 11*X^2 + 17*X + 18) :=
  sq_step (by norm_num) pElevenA4s49 ⟨
    12*X^9 + 14*X^8 + 6*X^7 + X^6 + X^5 + 19*X^4 + 14*X^3 + 17*X^2 + 21*X + 5,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s51 : XPow fElevenA4 116309784900
    (5*X^9 + 20*X^8 + 9*X^7 + 4*X^6 + 19*X^5 + 6*X^4 + 14*X^3 + 16*X^2 + 10*X + 20) :=
  sq_step (by norm_num) pElevenA4s50 ⟨
    18*X^9 + 17*X^8 + 12*X^7 + 18*X^6 + 2*X^4 + 17*X^3 + 19*X^2 + 9*X + 9,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s52 : XPow fElevenA4 116309784901
    (5*X^10 + 20*X^9 + 9*X^8 + 4*X^7 + 19*X^6 + 6*X^5 + 14*X^4 + 16*X^3 + 10*X^2 + 20*X) :=
  mul_step (by norm_num) pElevenA4s51 pElevenA41 ⟨
    0,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s53 : XPow fElevenA4 232619569802
    (18*X^10 + 7*X^9 + 8*X^8 + 19*X^7 + 14*X^6 + 13*X^5 + 19*X^4 + 14*X^3 + 9*X^2 + 6*X + 9) :=
  sq_step (by norm_num) pElevenA4s52 ⟨
    2*X^9 + 22*X^8 + 6*X^7 + 4*X^6 + 14*X^5 + 6*X^4 + 6*X^3 + 20*X^2 + 20*X + 16,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s54 : XPow fElevenA4 232619569803
    (15*X^10 + 3*X^9 + 5*X^8 + 2*X^7 + 10*X^6 + 2*X^5 + 9*X^4 + 12*X^3 + 16*X^2 + 11*X + 13) :=
  mul_step (by norm_num) pElevenA4s53 pElevenA41 ⟨
    18,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s55 : XPow fElevenA4 465239139606
    (16*X^10 + 18*X^9 + 4*X^8 + 12*X^7 + 13*X^6 + 14*X^5 + 13*X^4 + 5*X^3 + 19*X^2 + 20) :=
  sq_step (by norm_num) pElevenA4s54 ⟨
    18*X^9 + 6*X^8 + 11*X^7 + 17*X^5 + 17*X^4 + 7*X^3 + 2*X^2 + 10*X + 6,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s56 : XPow fElevenA4 930478279212
    (10*X^10 + 11*X^9 + 13*X^8 + 9*X^7 + 6*X^6 + 11*X^5 + 7*X^4 + 21*X^3 + 12*X + 15) :=
  sq_step (by norm_num) pElevenA4s55 ⟨
    3*X^9 + 10*X^8 + 2*X^7 + 5*X^6 + 10*X^5 + 2*X^4 + 19*X^2 + 2*X + 3,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s57 : XPow fElevenA4 1860956558424
    (13*X^10 + 20*X^9 + 14*X^8 + X^7 + 14*X^6 + 10*X^5 + 20*X^4 + 3*X^3 + 6*X^2 + 19) :=
  sq_step (by norm_num) pElevenA4s56 ⟨
    8*X^9 + 14*X^8 + 17*X^7 + 6*X^6 + 10*X^5 + 18*X^4 + 8*X^3 + 5*X^2 + 11*X + 12,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s58 : XPow fElevenA4 1860956558425
    (13*X^10 + 4*X^9 + 19*X^8 + 13*X^7 + 4*X^6 + 9*X^5 + 16*X^4 + 12*X^3 + 20*X^2 + 3) :=
  mul_step (by norm_num) pElevenA4s57 pElevenA41 ⟨
    13,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s59 : XPow fElevenA4 3721913116850
    (18*X^10 + 20*X^9 + 11*X^8 + 9*X^7 + 6*X^6 + 20*X^5 + 6*X^4 + 2*X^3 + 10*X^2 + 3*X + 7) :=
  sq_step (by norm_num) pElevenA4s58 ⟨
    8*X^9 + 13*X^8 + 5*X^7 + 16*X^6 + 6*X^5 + 16*X^4 + 21*X^3 + 22*X^2 + 22*X + 22,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s60 : XPow fElevenA4 3721913116851
    (5*X^10 + 6*X^9 + 18*X^8 + 17*X^7 + 17*X^6 + 12*X^5 + 20*X^4 + 13*X^3 + 13*X^2 + 9*X + 13) :=
  mul_step (by norm_num) pElevenA4s59 pElevenA41 ⟨
    18,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s61 : XPow fElevenA4 7443826233702
    (15*X^10 + 14*X^9 + X^8 + 7*X^6 + 12*X^4 + 12*X^3 + 14*X^2 + 7) :=
  sq_step (by norm_num) pElevenA4s60 ⟨
    2*X^9 + 20*X^8 + 2*X^7 + 22*X^6 + 8*X^5 + 11*X^4 + 5*X^3 + 16*X^2 + 14*X + 11,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s62 : XPow fElevenA4 14887652467404
    (X^10 + 20*X^9 + 17*X^8 + 7*X^7 + 11*X^5 + 20*X^4 + 3*X^3 + 6*X^2 + 13*X + 7) :=
  sq_step (by norm_num) pElevenA4s61 ⟨
    18*X^9 + 14*X^8 + 10*X^7 + 12*X^6 + 22*X^5 + 6*X^4 + 3*X^3 + 22*X^2 + 2,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s63 : XPow fElevenA4 14887652467405
    (18*X^9 + 19*X^8 + 7*X^7 + 7*X^6 + 5*X^5 + 4*X^4 + 10*X^3 + 11*X^2 + 2*X + 2) :=
  mul_step (by norm_num) pElevenA4s62 pElevenA41 ⟨
    1,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s64 : XPow fElevenA4 29775304934810
    (6*X^10 + 5*X^9 + X^8 + 2*X^7 + 9*X^6 + 20*X^5 + 18*X^4 + 9*X^3 + 18*X^2 + 18*X + 7) :=
  sq_step (by norm_num) pElevenA4s63 ⟨
    2*X^7 + 17*X^5 + 18*X^4 + 5*X^3 + 17*X^2 + 3*X + 13,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s65 : XPow fElevenA4 59550609869620
    (11*X^10 + 4*X^9 + 21*X^8 + 12*X^7 + 9*X^6 + 4*X^5 + 21*X^4 + 9*X^3 + 6*X^2 + X + 10) :=
  sq_step (by norm_num) pElevenA4s64 ⟨
    13*X^9 + 7*X^8 + 2*X^7 + 19*X^6 + 18*X^5 + 14*X^4 + 11*X^3 + 16*X^2 + 4*X + 15,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s66 : XPow fElevenA4 119101219739240
    (9*X^10 + 3*X^9 + 19*X^8 + 18*X^7 + 18*X^6 + 3*X^5 + 17*X^4 + 22*X^3 + 5*X^2 + 11*X + 17) :=
  sq_step (by norm_num) pElevenA4s65 ⟨
    6*X^9 + 14*X^8 + 20*X^7 + 3*X^6 + 8*X^5 + 16*X^4 + 21*X^3 + 18*X^2 + X + 16,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s67 : XPow fElevenA4 238202439478480
    (5*X^10 + 8*X^9 + 16*X^8 + 5*X^7 + 12*X^6 + 13*X^5 + 22*X^4 + 5*X^3 + 11*X^2 + X + 2) :=
  sq_step (by norm_num) pElevenA4s66 ⟨
    12*X^9 + 21*X^8 + 12*X^7 + 18*X^6 + 22*X^5 + 10*X^3 + 18*X^2 + X + 6,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s68 : XPow fElevenA4 238202439478481
    (21*X^9 + 19*X^8 + X^7 + 16*X^6 + 16*X^5 + 10*X^4 + 8*X^3 + 14*X^2 + 10) :=
  mul_step (by norm_num) pElevenA4s67 pElevenA41 ⟨
    5,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s69 : XPow fElevenA4 476404878956962
    (12*X^10 + 10*X^9 + 11*X^8 + 17*X^7 + 8*X^6 + 2*X^5 + 19*X^4 + 11*X^3 + 21*X^2 + X + 14) :=
  sq_step (by norm_num) pElevenA4s68 ⟨
    4*X^7 + 5*X^6 + 8*X^5 + 5*X^4 + 12*X^3 + 20*X^2 + 8*X + 3,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s70 : XPow fElevenA4 476404878956963
    (1) :=
  mul_step (by norm_num) pElevenA4s69 pElevenA41 ⟨
    12,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s71 : XPow fElevenA4 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenA4s70 ⟨
    0,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA4s72 : XPow fElevenA4 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenA4s71 pElevenA41 ⟨
    0,
    by simp only [fElevenA4]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Factor 5: `X ^ (23 ^ 11)` mod `f` by square-and-multiply -/

theorem pElevenA51 : XPow fElevenA5 1 X := xpow_one _

theorem pElevenA5s0 : XPow fElevenA5 2
    (X^2) :=
  sq_step (by norm_num) pElevenA51 ⟨
    0,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s1 : XPow fElevenA5 3
    (X^3) :=
  mul_step (by norm_num) pElevenA5s0 pElevenA51 ⟨
    0,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s2 : XPow fElevenA5 6
    (X^6) :=
  sq_step (by norm_num) pElevenA5s1 ⟨
    0,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s3 : XPow fElevenA5 12
    (X^9 + 18*X^8 + 8*X^7 + 4*X^5 + 4*X^4 + 2*X^3 + 9*X^2 + 19*X + 2) :=
  sq_step (by norm_num) pElevenA5s2 ⟨
    X + 2,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s4 : XPow fElevenA5 13
    (X^10 + 18*X^9 + 8*X^8 + 4*X^6 + 4*X^5 + 2*X^4 + 9*X^3 + 19*X^2 + 2*X) :=
  mul_step (by norm_num) pElevenA5s3 pElevenA51 ⟨
    0,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s5 : XPow fElevenA5 26
    (4*X^10 + 14*X^9 + 11*X^8 + 13*X^7 + 5*X^6 + 15*X^5 + 21*X^4 + 21*X^3 + 13*X^2 + 14*X + 7) :=
  sq_step (by norm_num) pElevenA5s4 ⟨
    X^9 + 15*X^8 + 21*X^7 + 3*X^6 + 14*X^5 + 20*X^4 + 5*X^3 + 13*X^2 + 20*X + 7,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s6 : XPow fElevenA5 27
    (22*X^10 + 18*X^9 + 3*X^8 + 5*X^7 + X^6 + 3*X^5 + 4*X^4 + 17*X^3 + 14*X^2 + 20*X + 4) :=
  mul_step (by norm_num) pElevenA5s5 pElevenA51 ⟨
    4,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s7 : XPow fElevenA5 54
    (21*X^10 + 12*X^9 + 14*X^8 + 20*X^7 + 5*X^6 + 7*X^5 + 19*X^4 + 9*X^3 + 12*X^2 + 14*X + 12) :=
  sq_step (by norm_num) pElevenA5s6 ⟨
    X^9 + 12*X^8 + 16*X^7 + 22*X^6 + 22*X^5 + 7*X^4 + 13*X^3 + 7*X^2 + 5*X + 19,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s8 : XPow fElevenA5 108
    (22*X^10 + 2*X^9 + 21*X^8 + 13*X^7 + X^6 + 9*X^5 + 21*X^4 + 19*X^3 + 12*X^2 + 20*X + 11) :=
  sq_step (by norm_num) pElevenA5s7 ⟨
    4*X^9 + 6*X^8 + 15*X^7 + 22*X^6 + 4*X^5 + 3*X^4 + 22*X^3 + 17*X^2 + 7*X + 5,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s9 : XPow fElevenA5 216
    (4*X^10 + 21*X^9 + 18*X^8 + 14*X^7 + 14*X^6 + 20*X^5 + 5*X^4 + 6*X^3 + 14*X^2 + 7*X + 14) :=
  sq_step (by norm_num) pElevenA5s8 ⟨
    X^9 + 21*X^8 + 6*X^6 + 2*X^5 + 14*X^4 + 17*X^3 + 8*X^2 + X + 8,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s10 : XPow fElevenA5 432
    (14*X^10 + 16*X^9 + 4*X^8 + 14*X^7 + 18*X^6 + 8*X^5 + 16*X^4 + 5*X^3 + 12*X^2 + 20*X + 15) :=
  sq_step (by norm_num) pElevenA5s9 ⟨
    16*X^9 + 16*X^8 + X^7 + 7*X^6 + 5*X^5 + 14*X^4 + 5*X^3 + 18*X^2 + 4*X + 3,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s11 : XPow fElevenA5 433
    (21*X^10 + 17*X^9 + 2*X^8 + 18*X^7 + 5*X^6 + 22*X^5 + 3*X^4 + 3*X^3 + 20*X^2 + 3*X + 14) :=
  mul_step (by norm_num) pElevenA5s10 pElevenA51 ⟨
    14,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s12 : XPow fElevenA5 866
    (3*X^10 + 2*X^9 + 3*X^8 + X^7 + 14*X^6 + 22*X^5 + 21*X^4 + 16*X^3 + 12*X^2 + 6) :=
  sq_step (by norm_num) pElevenA5s11 ⟨
    4*X^9 + 9*X^8 + 7*X^7 + 10*X^6 + 2*X^5 + 6*X^4 + 9*X^3 + 12*X^2 + 16*X + 17,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s13 : XPow fElevenA5 1732
    (19*X^10 + 3*X^9 + 18*X^8 + 21*X^7 + 22*X^6 + 15*X^5 + 6*X^4 + 16*X^3 + 13*X^2 + 18*X + 3) :=
  sq_step (by norm_num) pElevenA5s12 ⟨
    9*X^9 + 7*X^8 + 2*X^6 + 3*X^5 + 11*X^4 + 9*X^3 + X^2 + 16*X + 13,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s14 : XPow fElevenA5 1733
    (18*X^10 + 11*X^9 + 8*X^8 + 22*X^7 + 6*X^6 + X^5 + 10*X^4 + 9*X^3 + 18*X^2 + 13*X + 19) :=
  mul_step (by norm_num) pElevenA5s13 pElevenA51 ⟨
    19,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s15 : XPow fElevenA5 3466
    (14*X^10 + 18*X^9 + 7*X^7 + 11*X^6 + 22*X^5 + 20*X^4 + 3*X^3 + 21*X^2 + 14*X + 19) :=
  sq_step (by norm_num) pElevenA5s14 ⟨
    2*X^9 + 9*X^8 + 5*X^7 + 17*X^6 + 8*X^5 + 19*X^3 + 5*X^2 + 22*X + 3,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s16 : XPow fElevenA5 6932
    (20*X^10 + 11*X^9 + 19*X^8 + 2*X^7 + 19*X^6 + 22*X^5 + 21*X^4 + X^3 + 7*X^2 + 18*X + 7) :=
  sq_step (by norm_num) pElevenA5s15 ⟨
    12*X^9 + 22*X^8 + 21*X^7 + 5*X^6 + 17*X^5 + 5*X^3 + 12*X^2 + 4*X + 14,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s17 : XPow fElevenA5 13864
    (13*X^10 + 11*X^8 + 12*X^7 + 19*X^6 + 20*X^5 + 11*X^4 + 19*X^3 + 22*X^2 + 6*X + 8) :=
  sq_step (by norm_num) pElevenA5s16 ⟨
    9*X^9 + 21*X^8 + 13*X^7 + 15*X^6 + 21*X^5 + 4*X^4 + 17*X^3 + 11*X^2 + 8*X + 5,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s18 : XPow fElevenA5 13865
    (3*X^10 + 5*X^9 + 14*X^8 + 19*X^7 + 9*X^6 + 10*X^5 + 4*X^4 + 12*X^3 + 6*X^2 + 10*X + 13) :=
  mul_step (by norm_num) pElevenA5s17 pElevenA51 ⟨
    13,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s19 : XPow fElevenA5 27730
    (7*X^10 + 16*X^9 + 6*X^8 + 14*X^7 + 7*X^5 + 11*X^4 + 13*X^3 + 20*X^2 + 18*X + 17) :=
  sq_step (by norm_num) pElevenA5s18 ⟨
    9*X^9 + 2*X^8 + 8*X^7 + 21*X^6 + 8*X^5 + 22*X^4 + 5*X^3 + 3*X^2 + 22*X + 9,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s20 : XPow fElevenA5 55460
    (18*X^10 + 18*X^9 + 2*X^8 + 20*X^7 + 3*X^6 + 21*X^5 + 13*X^4 + X^3 + 19*X^2 + 10*X + 11) :=
  sq_step (by norm_num) pElevenA5s19 ⟨
    3*X^9 + 6*X^7 + 13*X^6 + 3*X^5 + 22*X^4 + 8*X^3 + 16*X^2 + 14*X + 21,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s21 : XPow fElevenA5 110920
    (2*X^10 + 12*X^9 + 4*X^8 + 11*X^7 + 15*X^6 + 5*X^5 + 3*X^4 + X^3 + 16*X^2 + 21) :=
  sq_step (by norm_num) pElevenA5s20 ⟨
    2*X^9 + 8*X^8 + 13*X^7 + 22*X^6 + 22*X^5 + 21*X^4 + 3*X^3 + 2*X^2 + 13*X + 15,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s22 : XPow fElevenA5 110921
    (16*X^10 + 19*X^9 + 6*X^8 + 15*X^7 + 21*X^6 + 17*X^5 + 4*X^4 + 18*X^3 + 16*X + 2) :=
  mul_step (by norm_num) pElevenA5s21 pElevenA51 ⟨
    2,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s23 : XPow fElevenA5 221842
    (20*X^10 + 17*X^9 + 18*X^8 + 15*X^6 + 11*X^5 + 15*X^4 + 7*X^3 + 18*X^2 + 13*X + 8) :=
  sq_step (by norm_num) pElevenA5s22 ⟨
    3*X^9 + 16*X^8 + 21*X^7 + 4*X^5 + 18*X^4 + 17*X^3 + 16*X^2 + 5*X + 4,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s24 : XPow fElevenA5 221843
    (11*X^10 + 7*X^9 + 19*X^8 + 15*X^7 + 10*X^6 + 17*X^5 + 14*X^4 + 15*X^3 + 13*X^2 + 4*X + 20) :=
  mul_step (by norm_num) pElevenA5s23 pElevenA51 ⟨
    20,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s25 : XPow fElevenA5 443686
    (5*X^10 + 6*X^9 + 5*X^8 + 2*X^7 + 16*X^6 + 2*X^5 + 18*X^4 + 16*X^3 + 8*X^2 + 21) :=
  sq_step (by norm_num) pElevenA5s24 ⟨
    6*X^9 + 5*X^8 + 16*X^7 + 18*X^6 + 3*X^5 + 14*X^4 + 8*X^3 + 21*X^2 + 8*X + 12,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s26 : XPow fElevenA5 887372
    (17*X^10 + 12*X^9 + 12*X^8 + 16*X^7 + 11*X^6 + 4*X^5 + 7*X^4 + 17*X^3 + 18*X^2 + 8*X + 10) :=
  sq_step (by norm_num) pElevenA5s25 ⟨
    2*X^9 + 18*X^8 + 22*X^7 + X^6 + 9*X^5 + 16*X^3 + 4*X^2 + 6,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s27 : XPow fElevenA5 887373
    (13*X^9 + 8*X^8 + 11*X^7 + 2*X^6 + 11*X^5 + 8*X^4 + 12*X^3 + 8*X^2 + 2*X + 17) :=
  mul_step (by norm_num) pElevenA5s26 pElevenA51 ⟨
    17,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s28 : XPow fElevenA5 1774746
    (9*X^10 + 13*X^9 + 11*X^8 + 10*X^7 + 5*X^6 + 12*X^5 + X^4 + 11*X^3 + 8*X^2 + 21*X + 10) :=
  sq_step (by norm_num) pElevenA5s27 ⟨
    8*X^7 + 17*X^6 + 7*X^5 + 16*X^4 + 21*X^3 + 4*X^2 + 3*X + 20,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s29 : XPow fElevenA5 3549492
    (13*X^10 + 10*X^9 + 19*X^8 + 16*X^7 + 12*X^6 + 17*X^5 + 7*X^4 + 14*X^3 + 22*X^2 + 8*X + 14) :=
  sq_step (by norm_num) pElevenA5s28 ⟨
    12*X^9 + 5*X^8 + 7*X^7 + 16*X^6 + 14*X^5 + 22*X^4 + 14*X^3 + 4*X^2 + 17*X + 6,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s30 : XPow fElevenA5 7098984
    (17*X^10 + 5*X^9 + X^8 + 16*X^7 + 2*X^6 + X^5 + 2*X^4 + 9*X^3 + 3*X^2 + 14*X) :=
  sq_step (by norm_num) pElevenA5s29 ⟨
    8*X^9 + 10*X^7 + 14*X^6 + 15*X^5 + 15*X^4 + 6*X^3 + 11*X^2 + 13*X + 11,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s31 : XPow fElevenA5 7098985
    (16*X^10 + 2*X^9 + 8*X^8 + 2*X^7 + 22*X^6 + 6*X^5 + 20*X^3 + 14*X^2 + 15*X + 17) :=
  mul_step (by norm_num) pElevenA5s30 pElevenA51 ⟨
    17,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s32 : XPow fElevenA5 14197970
    (4*X^10 + 6*X^9 + 4*X^8 + 7*X^7 + 8*X^6 + 21*X^5 + 13*X^4 + 3*X^3 + 3*X^2 + 17*X + 22) :=
  sq_step (by norm_num) pElevenA5s31 ⟨
    3*X^9 + X^8 + 20*X^7 + 21*X^6 + 11*X^5 + 17*X^4 + 13*X^3 + 6*X^2 + X + 9,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s33 : XPow fElevenA5 14197971
    (14*X^10 + 11*X^9 + 20*X^8 + 8*X^7 + 7*X^6 + 18*X^5 + 9*X^4 + 7*X^3 + 17*X^2 + 12*X + 4) :=
  mul_step (by norm_num) pElevenA5s32 pElevenA51 ⟨
    4,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s34 : XPow fElevenA5 28395942
    (3*X^10 + 8*X^9 + X^8 + 6*X^7 + 19*X^6 + 9*X^5 + 20*X^4 + 10*X^3 + 13*X^2 + 17*X + 19) :=
  sq_step (by norm_num) pElevenA5s33 ⟨
    12*X^9 + 10*X^8 + 9*X^7 + 14*X^6 + 3*X^5 + X^4 + 7*X^3 + 20*X^2 + 9*X + 3,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s35 : XPow fElevenA5 28395943
    (14*X^10 + 12*X^9 + 10*X^8 + 19*X^7 + 10*X^6 + 18*X^5 + 3*X^4 + 16*X^3 + 17*X^2 + 3) :=
  mul_step (by norm_num) pElevenA5s34 pElevenA51 ⟨
    3,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s36 : XPow fElevenA5 56791886
    (15*X^10 + 14*X^9 + 20*X^7 + 17*X^6 + 4*X^5 + 8*X^4 + 15*X^3 + 14*X^2 + 18*X + 2) :=
  sq_step (by norm_num) pElevenA5s35 ⟨
    12*X^9 + 15*X^8 + 15*X^7 + 22*X^6 + 12*X^5 + 3*X^4 + 11*X^3 + 11*X^2 + 12*X + 16,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s37 : XPow fElevenA5 56791887
    (21*X^10 + 9*X^9 + 17*X^8 + 17*X^7 + 9*X^6 + 21*X^5 + 3*X^4 + 6*X^3 + 18*X^2 + 22*X + 15) :=
  mul_step (by norm_num) pElevenA5s36 pElevenA51 ⟨
    15,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s38 : XPow fElevenA5 113583774
    (15*X^10 + 3*X^9 + 14*X^8 + 22*X^7 + 21*X^6 + 22*X^5 + 5*X^3 + 2*X^2 + 2*X + 18) :=
  sq_step (by norm_num) pElevenA5s37 ⟨
    4*X^9 + 18*X^8 + 10*X^7 + 15*X^6 + 21*X^5 + X^4 + 13*X^3 + X^2 + 9*X,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s39 : XPow fElevenA5 227167548
    (13*X^10 + 22*X^9 + 3*X^8 + 6*X^7 + 21*X^6 + 6*X^5 + 7*X^4 + 15*X^3 + 10*X^2 + 12*X + 14) :=
  sq_step (by norm_num) pElevenA5s38 ⟨
    18*X^9 + 11*X^8 + 11*X^7 + 10*X^6 + 21*X^5 + 14*X^4 + 3*X^3 + 20*X^2 + 16*X + 12,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s40 : XPow fElevenA5 454335096
    (19*X^10 + 21*X^9 + 20*X^8 + 18*X^6 + 11*X^5 + 8*X^4 + 18*X^3 + 22*X^2 + 19*X) :=
  sq_step (by norm_num) pElevenA5s39 ⟨
    8*X^9 + 13*X^8 + 4*X^7 + 17*X^6 + 11*X^5 + 20*X^4 + 20*X^3 + 7*X^2 + 21*X + 11,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s41 : XPow fElevenA5 454335097
    (13*X^10 + 13*X^9 + 10*X^8 + 18*X^7 + 2*X^6 + 3*X^5 + 12*X^4 + 18*X^3 + 19*X^2 + 10*X + 19) :=
  mul_step (by norm_num) pElevenA5s40 pElevenA51 ⟨
    19,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s42 : XPow fElevenA5 908670194
    (17*X^10 + 4*X^9 + 12*X^8 + 5*X^7 + 5*X^6 + 2*X^5 + 22*X^4 + 21*X^3 + 5*X^2 + 2*X + 14) :=
  sq_step (by norm_num) pElevenA5s41 ⟨
    8*X^9 + 9*X^8 + X^7 + 7*X^6 + 21*X^5 + 2*X^4 + 14*X^3 + 8*X^2 + 8*X + 21,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s43 : XPow fElevenA5 1817340388
    (20*X^9 + 18*X^8 + 9*X^7 + 20*X^6 + 14*X^5 + 17*X^4 + 5*X^3 + X^2 + 10*X + 3) :=
  sq_step (by norm_num) pElevenA5s42 ⟨
    13*X^9 + X^8 + 6*X^7 + 17*X^5 + 6*X^4 + 9*X^3 + 2*X^2 + 12*X + 14,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s44 : XPow fElevenA5 1817340389
    (20*X^10 + 18*X^9 + 9*X^8 + 20*X^7 + 14*X^6 + 17*X^5 + 5*X^4 + X^3 + 10*X^2 + 3*X) :=
  mul_step (by norm_num) pElevenA5s43 pElevenA51 ⟨
    0,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s45 : XPow fElevenA5 3634680778
    (9*X^10 + 17*X^9 + 10*X^8 + 15*X^6 + 16*X^5 + 20*X^4 + 7*X^2 + 22*X + 19) :=
  sq_step (by norm_num) pElevenA5s44 ⟨
    9*X^9 + 2*X^8 + 8*X^7 + 17*X^6 + X^5 + 12*X^4 + 14*X^3 + 5*X^2 + 12*X + 19,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s46 : XPow fElevenA5 7269361556
    (21*X^10 + 11*X^9 + 6*X^8 + 15*X^6 + 11*X^5 + 4*X^4 + 8*X^3 + 2) :=
  sq_step (by norm_num) pElevenA5s45 ⟨
    12*X^9 + 8*X^8 + 2*X^6 + 9*X^5 + 7*X^4 + 14*X^3 + 5*X^2 + 3*X + 9,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s47 : XPow fElevenA5 14538723112
    (19*X^10 + 12*X^9 + 11*X^8 + 15*X^7 + 9*X^6 + 10*X^5 + 22*X^4 + 16*X^3 + 22*X^2 + 11*X) :=
  sq_step (by norm_num) pElevenA5s46 ⟨
    4*X^9 + 10*X^8 + 9*X^7 + 8*X^6 + 22*X^4 + 9*X^3 + 13*X^2 + X + 19,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s48 : XPow fElevenA5 29077446224
    (15*X^10 + 5*X^9 + 16*X^8 + 20*X^7 + 12*X^6 + 11*X^5 + 18*X^4 + 20*X^3 + 6*X + 2) :=
  sq_step (by norm_num) pElevenA5s47 ⟨
    16*X^9 + 5*X^8 + 2*X^7 + 19*X^6 + X^5 + 9*X^4 + 19*X^3 + 10*X^2 + 11*X + 2,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s49 : XPow fElevenA5 29077446225
    (12*X^10 + 2*X^9 + 17*X^8 + 12*X^7 + 16*X^6 + 8*X^5 + 8*X^4 + 15*X^3 + 6*X^2 + 22*X + 15) :=
  mul_step (by norm_num) pElevenA5s48 pElevenA51 ⟨
    15,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s50 : XPow fElevenA5 58154892450
    (9*X^10 + 7*X^9 + 9*X^8 + 5*X^7 + X^6 + 20*X^5 + X^3 + 20*X^2 + 10*X + 20) :=
  sq_step (by norm_num) pElevenA5s49 ⟨
    6*X^9 + 14*X^8 + 2*X^7 + 13*X^6 + 14*X^5 + 16*X^4 + 9*X^3 + 9*X^2 + 22*X + 2,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s51 : XPow fElevenA5 116309784900
    (X^10 + 19*X^9 + 5*X^8 + 5*X^7 + 3*X^6 + 2*X^5 + X^4 + 14*X^3 + 2*X^2 + 13*X + 6) :=
  sq_step (by norm_num) pElevenA5s50 ⟨
    12*X^9 + 12*X^8 + 3*X^7 + 6*X^6 + X^5 + 13*X^4 + 4*X^3 + 19*X^2 + 8*X + 20,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s52 : XPow fElevenA5 116309784901
    (21*X^10 + X^9 + 14*X^8 + 3*X^7 + 10*X^6 + 8*X^5 + 4*X^4 + 3*X^3 + 13*X^2 + 15*X + 1) :=
  mul_step (by norm_num) pElevenA5s51 pElevenA51 ⟨
    1,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s53 : XPow fElevenA5 232619569802
    (X^10 + 19*X^9 + 15*X^8 + 12*X^7 + 14*X^6 + 11*X^5 + 19*X^4 + 12*X^3 + 16*X^2 + 9*X + 19) :=
  sq_step (by norm_num) pElevenA5s52 ⟨
    4*X^9 + 4*X^8 + 6*X^7 + 2*X^6 + 17*X^5 + 9*X^2 + X + 18,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s54 : XPow fElevenA5 232619569803
    (21*X^10 + 11*X^9 + 21*X^8 + 14*X^7 + 19*X^6 + 3*X^5 + 2*X^4 + 17*X^3 + 9*X^2 + 5*X + 1) :=
  mul_step (by norm_num) pElevenA5s53 pElevenA51 ⟨
    1,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s55 : XPow fElevenA5 465239139606
    (10*X^10 + 12*X^9 + 14*X^8 + 19*X^7 + 3*X^6 + 13*X^5 + 10*X^4 + 7*X^3 + X^2 + 8*X + 22) :=
  sq_step (by norm_num) pElevenA5s54 ⟨
    4*X^9 + 10*X^8 + 18*X^7 + X^6 + 3*X^5 + 17*X^4 + 18*X^3 + 21*X^2 + 16*X + 21,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s56 : XPow fElevenA5 930478279212
    (13*X^10 + 4*X^9 + 19*X^8 + 13*X^7 + 12*X^6 + 2*X^5 + 15*X^4 + 20*X^3 + 10*X^2 + 15*X + 6) :=
  sq_step (by norm_num) pElevenA5s55 ⟨
    8*X^9 + 3*X^8 + 7*X^7 + 8*X^6 + 14*X^5 + 21*X^4 + 14*X^3 + 5*X^2 + 9*X + 5,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s57 : XPow fElevenA5 1860956558424
    (9*X^10 + 5*X^9 + 3*X^8 + 8*X^7 + 21*X^6 + 20*X^5 + 17*X^4 + 7*X^3 + 16*X^2 + 14*X + 22) :=
  sq_step (by norm_num) pElevenA5s56 ⟨
    8*X^9 + 5*X^8 + 5*X^7 + 20*X^5 + 9*X^4 + 7*X^3 + 8*X^2 + 6*X + 9,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s58 : XPow fElevenA5 1860956558425
    (13*X^9 + 20*X^8 + 21*X^7 + 11*X^5 + 9*X^4 + 2*X^3 + 14*X^2 + 11*X + 9) :=
  mul_step (by norm_num) pElevenA5s57 pElevenA51 ⟨
    9,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s59 : XPow fElevenA5 3721913116850
    (20*X^10 + 22*X^9 + 5*X^8 + 19*X^7 + 20*X^6 + 7*X^5 + 5*X^4 + 19*X^3 + 6*X^2 + 8*X) :=
  sq_step (by norm_num) pElevenA5s58 ⟨
    8*X^7 + 7*X^6 + 8*X^5 + 3*X^4 + 5*X^3 + 3*X^2 + 10*X + 11,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s60 : XPow fElevenA5 3721913116851
    (16*X^10 + 17*X^9 + 15*X^8 + 20*X^7 + 6*X^6 + 7*X^5 + 3*X^4 + 3*X^3 + 8*X^2 + 19*X + 20) :=
  mul_step (by norm_num) pElevenA5s59 pElevenA51 ⟨
    20,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s61 : XPow fElevenA5 7443826233702
    (2*X^10 + 22*X^9 + 11*X^8 + 9*X^7 + 22*X^6 + 20*X^5 + 18*X^3 + 6*X + 14) :=
  sq_step (by norm_num) pElevenA5s60 ⟨
    3*X^9 + 21*X^8 + 17*X^7 + 22*X^5 + 7*X^4 + 17*X^3 + X^2 + 6*X + 5,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s62 : XPow fElevenA5 14887652467404
    (19*X^10 + 14*X^9 + 7*X^8 + 22*X^7 + 4*X^6 + 19*X^5 + 20*X^4 + X^3 + X^2 + 19*X + 1) :=
  sq_step (by norm_num) pElevenA5s61 ⟨
    4*X^9 + 4*X^8 + 14*X^7 + 16*X^6 + 19*X^5 + 21*X^4 + 5*X^3 + X^2 + 19*X + 12,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s63 : XPow fElevenA5 14887652467405
    (6*X^10 + 9*X^8 + 4*X^7 + 10*X^6 + 15*X^5 + 18*X^4 + 20*X^3 + 19*X^2 + 11*X + 19) :=
  mul_step (by norm_num) pElevenA5s62 pElevenA51 ⟨
    19,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s64 : XPow fElevenA5 29775304934810
    (15*X^9 + 9*X^8 + 10*X^7 + 6*X^6 + 11*X^5 + X^4 + 19*X^3 + 4*X^2 + 3) :=
  sq_step (by norm_num) pElevenA5s63 ⟨
    13*X^9 + 3*X^8 + 16*X^7 + X^6 + 5*X^5 + 10*X^3 + 7*X^2 + 21*X + 10,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s65 : XPow fElevenA5 59550609869620
    (22*X^10 + 3*X^9 + 16*X^8 + 2*X^7 + 5*X^6 + 16*X^5 + 18*X^4 + 3*X^3 + 9*X^2 + 4*X + 5) :=
  sq_step (by norm_num) pElevenA5s64 ⟨
    18*X^7 + 7*X^6 + X^5 + 13*X^4 + 2*X^3 + 16*X^2 + 17*X + 19,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s66 : XPow fElevenA5 119101219739240
    (13*X^10 + 19*X^8 + 16*X^7 + 14*X^6 + 15*X^5 + 16*X^4 + 22*X^3 + 8*X^2 + 15*X + 8) :=
  sq_step (by norm_num) pElevenA5s65 ⟨
    X^9 + 19*X^8 + 11*X^7 + X^6 + 19*X^5 + 19*X^4 + 9*X^3 + 15*X^2 + 13*X + 6,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s67 : XPow fElevenA5 238202439478480
    (18*X^10 + 12*X^9 + 22*X^8 + X^6 + 12*X^5 + 15*X^4 + 20*X^3 + 14*X^2 + 20*X + 13) :=
  sq_step (by norm_num) pElevenA5s66 ⟨
    8*X^9 + 16*X^8 + 11*X^7 + 9*X^6 + 15*X^5 + 5*X^4 + 16*X^3 + 17*X^2 + 9*X + 18,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s68 : XPow fElevenA5 238202439478481
    (2*X^10 + 19*X^9 + X^8 + X^7 + 18*X^6 + 3*X^5 + X^4 + 9*X^3 + 20*X^2 + 14*X + 18) :=
  mul_step (by norm_num) pElevenA5s67 pElevenA51 ⟨
    18,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s69 : XPow fElevenA5 476404878956962
    (X^10 + 21*X^9 + 4*X^8 + 14*X^7 + 15*X^5 + 16*X^4 + 10*X^3 + 22*X^2 + 14) :=
  sq_step (by norm_num) pElevenA5s68 ⟨
    4*X^9 + 15*X^8 + 11*X^7 + 17*X^6 + 6*X^5 + 14*X^4 + 14*X^2 + 9*X + 12,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s70 : XPow fElevenA5 476404878956963
    (1) :=
  mul_step (by norm_num) pElevenA5s69 pElevenA51 ⟨
    1,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s71 : XPow fElevenA5 952809757913926
    (1) :=
  sq_step (by norm_num) pElevenA5s70 ⟨
    0,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

theorem pElevenA5s72 : XPow fElevenA5 952809757913927
    (X) :=
  mul_step (by norm_num) pElevenA5s71 pElevenA51 ⟨
    0,
    by simp only [fElevenA5]; reduce_mod_char; all_goals ring_nf; all_goals reduce_mod_char⟩

/-! ### Pairwise coprimality of the factors, by explicit Bézout identities -/

theorem copElevenA1_2 : IsCoprime fElevenA1 fElevenA2 :=
  ⟨22*X^10 + 16*X^9 + 22*X^8 + 21*X^7 + 6*X^6 + X^5 + 7*X^4 + 15*X^3 + 12*X^2 + 20*X + 18,
   X^10 + 18*X^9 + 3*X^8 + 9*X^7 + 21*X^6 + 10*X^5 + 20*X^4 + 20*X^3 + 21*X^2 + 22*X + 11,
   by simp only [fElevenA1, fElevenA2]; ring_nf; reduce_mod_char⟩

theorem copElevenA1_3 : IsCoprime fElevenA1 fElevenA3 :=
  ⟨13*X^10 + 15*X^9 + 18*X^8 + 9*X^7 + X^6 + 3*X^5 + 11*X^4 + 19*X^3 + 7*X^2 + 6*X + 11,
   10*X^10 + 19*X^9 + 7*X^8 + 21*X^7 + 3*X^6 + 8*X^5 + 16*X^4 + 16*X^3 + 3*X^2 + 13*X + 18,
   by simp only [fElevenA1, fElevenA3]; ring_nf; reduce_mod_char⟩

theorem copElevenA1_4 : IsCoprime fElevenA1 fElevenA4 :=
  ⟨5*X^10 + 9*X^9 + 17*X^8 + 6*X^7 + 17*X^6 + 15*X^5 + 12*X^4 + 20*X^3 + 14*X + 15,
   18*X^10 + 2*X^9 + 8*X^8 + X^7 + 10*X^6 + 19*X^5 + 15*X^4 + 15*X^3 + 10*X^2 + 5*X + 14,
   by simp only [fElevenA1, fElevenA4]; ring_nf; reduce_mod_char⟩

theorem copElevenA1_5 : IsCoprime fElevenA1 fElevenA5 :=
  ⟨2*X^10 + X^9 + 8*X^8 + 2*X^7 + 8*X^5 + 21*X^4 + 6*X^3 + 6*X^2 + 17*X + 5,
   21*X^10 + 10*X^9 + 17*X^8 + 5*X^7 + 4*X^6 + 3*X^5 + 6*X^4 + 6*X^3 + 4*X^2 + 2*X + 1,
   by simp only [fElevenA1, fElevenA5]; ring_nf; reduce_mod_char⟩

theorem copElevenA2_3 : IsCoprime fElevenA2 fElevenA3 :=
  ⟨19*X^10 + 6*X^9 + 21*X^8 + 22*X^7 + 5*X^6 + 15*X^5 + 9*X^4 + 3*X^3 + 12*X^2 + 7*X + 9,
   4*X^10 + 5*X^9 + 4*X^8 + 8*X^7 + 22*X^6 + 19*X^5 + 18*X^4 + 9*X^3 + 21*X^2 + 12*X + 20,
   by simp only [fElevenA2, fElevenA3]; ring_nf; reduce_mod_char⟩

theorem copElevenA2_4 : IsCoprime fElevenA2 fElevenA4 :=
  ⟨20*X^10 + 13*X^9 + 22*X^8 + X^7 + 22*X^6 + 14*X^5 + 2*X^4 + 11*X^3 + 10*X + 14,
   3*X^10 + 21*X^9 + 3*X^8 + 6*X^7 + 5*X^6 + 20*X^5 + 2*X^4 + X^3 + 10*X^2 + 9*X + 15,
   by simp only [fElevenA2, fElevenA4]; ring_nf; reduce_mod_char⟩

theorem copElevenA2_5 : IsCoprime fElevenA2 fElevenA5 :=
  ⟨16*X^10 + 8*X^9 + 18*X^8 + 16*X^7 + 18*X^5 + 7*X^4 + 2*X^3 + 2*X^2 + 21*X + 17,
   7*X^10 + 3*X^9 + 7*X^8 + 14*X^7 + 4*X^6 + 16*X^5 + 20*X^4 + 10*X^3 + 8*X^2 + 21*X + 12,
   by simp only [fElevenA2, fElevenA5]; ring_nf; reduce_mod_char⟩

theorem copElevenA3_4 : IsCoprime fElevenA3 fElevenA4 :=
  ⟨11*X^10 + 6*X^9 + 19*X^8 + 4*X^7 + 19*X^6 + 10*X^5 + 8*X^4 + 21*X^3 + 17*X + 10,
   12*X^10 + 5*X^9 + 6*X^8 + 3*X^7 + 8*X^6 + X^5 + 19*X^4 + 14*X^3 + 10*X^2 + 2*X + 19,
   by simp only [fElevenA3, fElevenA4]; ring_nf; reduce_mod_char⟩

theorem copElevenA3_5 : IsCoprime fElevenA3 fElevenA5 :=
  ⟨17*X^10 + 20*X^9 + 22*X^8 + 17*X^7 + 22*X^5 + 6*X^4 + 5*X^3 + 5*X^2 + 18*X + 8,
   6*X^10 + 14*X^9 + 3*X^8 + 13*X^7 + 4*X^6 + 12*X^5 + 21*X^4 + 7*X^3 + 5*X^2 + X + 21,
   by simp only [fElevenA3, fElevenA5]; ring_nf; reduce_mod_char⟩

theorem copElevenA4_5 : IsCoprime fElevenA4 fElevenA5 :=
  ⟨11*X^10 + 17*X^9 + 21*X^8 + 11*X^7 + 21*X^5 + 12*X^4 + 10*X^3 + 10*X^2 + 13*X + 16,
   12*X^10 + 17*X^9 + 4*X^8 + 19*X^7 + 4*X^6 + 13*X^5 + 15*X^4 + 2*X^3 + 6*X + 13,
   by simp only [fElevenA4, fElevenA5]; ring_nf; reduce_mod_char⟩

/-! ### Assembly -/

theorem dvd_X_pow_card_pow_sub_X_hPolyElevenA :
    hPolyElevenA ∣ X ^ (Nat.card (ZMod 23)) ^ 11 - X := by
  have h2 := xpow_mul copElevenA1_2 pElevenA1s72 pElevenA2s72
  have c3 : IsCoprime (fElevenA1 * fElevenA2) fElevenA3 :=
    (copElevenA1_3).mul_left copElevenA2_3
  have h3 := xpow_mul c3 h2 pElevenA3s72
  have c4 : IsCoprime (fElevenA1 * fElevenA2 * fElevenA3) fElevenA4 :=
    ((copElevenA1_4).mul_left copElevenA2_4).mul_left copElevenA3_4
  have h4 := xpow_mul c4 h3 pElevenA4s72
  have c5 : IsCoprime (fElevenA1 * fElevenA2 * fElevenA3 * fElevenA4) fElevenA5 :=
    (((copElevenA1_5).mul_left copElevenA2_5).mul_left copElevenA3_5).mul_left copElevenA4_5
  have h5 := xpow_mul c5 h4 pElevenA5s72
  rw [factor_hPolyElevenA]
  exact xpow_card (by rw [Nat.card_zmod]; norm_num) h5

end Fermat.MazurNonCMCertificate

/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ReduceModChar

/-!
# `X ^ n mod f` certificates over a prime field, and the four `H` of Mazur's non-CM table

`MazurNonCMCertificate.lean` reduces four rows of Mazur's table to six statements about two
explicit polynomials over `ZMod ℓ`: `H ∣ X ^ (ℓ ^ m) - X`, and (for `ℓ = 67`)
`IsCoprime H (X ^ (ℓ ^ 2) - X)`.  This module holds the machinery those certificates run on,
and the four `H` themselves; the certificates are one module per row, under
`MazurNonCMFrobenius/`.

**`XPow f n a` IS `f ∣ X ^ n - a`, AND THE WRAPPER IS THE ONLY REASON ANY OF THIS ELABORATES.**
Stated as `f ∣ X ^ n - a` directly, unifying a chain step against its own statement makes the
elaborator `whnf` `X ^ n`, which unfolds `npowRec` ONCE PER UNIT of `n`.  Measured
2026-07-31: recursion depth `≈ 3 n`, so a step at `n = 6932` already needs
`maxRecDepth 20000`, and the chain here runs to `n = 23 ^ 11 = 952809757913927`.  It blows an
8 MB thread stack, a 64 MB one and a 256 MB one, in that order, and says nothing but
`Stack overflow detected. Aborting.` — no line number, no failing declaration.  Behind `XPow`
the exponent is an ARGUMENT, so unification assigns `?n := 952809757913927` and never looks
inside `X ^ ?n`.  Same statements, same proofs, seconds instead of a crash.

Two corollaries worth keeping:

* **Do not "simplify" `xpow_card` into a `rw` of the exponent.**  `rw [hexp]` inside
  `X ^ (Nat.card (ZMod ℓ)) ^ m` puts the literal straight back into exponent position and the
  blow-up returns.  `xpow_card` moves the arithmetic into a `ℕ` equation, where no polynomial
  is involved at all.
* **`set_option maxRecDepth` LARGE MAKES THIS WORSE, NOT BETTER.**  At `4000000` the same
  files crash; at `20000` they compile.  A high limit lets a doomed reduction run until the
  C stack dies instead of failing fast and letting the elaborator take another route.

The chains are square-and-multiply, so every polynomial identity handed to `ring_nf` has
degree `< 2 deg f` however large the exponent; and they run modulo the IRREDUCIBLE FACTORS of
`H` rather than `H` itself, which is `k ^ 2` cheaper and — since `IsCoprime.mul_dvd` reassembles
the product — needs the factors only to be pairwise coprime, never to be irreducible.  No
irreducibility test appears anywhere in this development.

**A SUPERSEDED HAND-ROLLED COPY OF THE `p = 11` CERTIFICATES USED TO SIT BELOW THIS POINT**
(removed 2026-07-31).  It was the same two divisibilities proven through a hand-written
`namespace F1` … `namespace F5` Frobenius-table chain — 2 272 lines here plus a whole sibling
module `MazurNonCMFrobeniusB.lean` for the second row — and it had NO consumer once the
generated `MazurNonCMFrobenius/ElevenA.lean` and `…/ElevenB.lean` landed.  It survived only
because the semantic merge propagates additions and not deletions, so the branch that replaced
it could not remove it.  Measured cost of carrying it: `530 s` in this module (which every
consumer waits on) and `235 s` in the sibling.  Recover it from git history if it is ever
wanted; do not re-add it here.
-/

@[expose] public section

open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Fermat.MazurNonCMCertificate

/-- `XPow f n a` is `f ∣ X ^ n - a`.  See the module docstring: the wrapper keeps the
exponent out of unification, and without it nothing here elaborates. -/
def XPow {q : ℕ} (f : (ZMod q)[X]) (n : ℕ) (a : (ZMod q)[X]) : Prop := f ∣ X ^ n - a

theorem xpow_one {q : ℕ} (f : (ZMod q)[X]) : XPow f 1 X := by simp [XPow]

theorem xpow_dvd {q : ℕ} {f a : (ZMod q)[X]} {n : ℕ} (h : XPow f n a) : f ∣ X ^ n - a := h

/-- Discharge `X ^ (Nat.card (ZMod q)) ^ m` against a chain that ends at the LITERAL `q ^ m`.
Going through `hN` as a `ℕ` equation is deliberate: `rw`-ing that equation inside `X ^ _` puts
the literal back into exponent position and costs `≈ 3 q ^ m` recursion depth. -/
theorem xpow_card {q m N : ℕ} {f a : (ZMod q)[X]} (hN : Nat.card (ZMod q) ^ m = N)
    (h : XPow f N a) : f ∣ X ^ (Nat.card (ZMod q)) ^ m - a := by
  subst hN
  exact h

/-- Reassemble a coprime product.  This is what makes the factor-by-factor route legal, and
note it needs COPRIMALITY only — never irreducibility. -/
theorem xpow_mul {q : ℕ} {f g a : (ZMod q)[X]} {n : ℕ} (hc : IsCoprime f g)
    (h : XPow f n a) (h2 : XPow g n a) : XPow (f * g) n a :=
  hc.mul_dvd h h2

/-- One squaring: `X ^ (2n) - b = (X ^ n - a) (X ^ n + a) + (a a - b)`. -/
theorem sq_step {q : ℕ} {f a b : (ZMod q)[X]} {n n' : ℕ} (hn : n' = n + n)
    (h : XPow f n a) (h2 : f ∣ a * a - b) : XPow f n' b := by
  subst hn
  have h' : f ∣ (X : (ZMod q)[X]) ^ n - a := h
  have e : (X : (ZMod q)[X]) ^ (n + n) - b = (X ^ n - a) * (X ^ n + a) + (a * a - b) := by
    ring
  show f ∣ _
  rw [e]
  exact dvd_add (h'.mul_right _) h2

/-- One multiplication:
`X ^ (n + n') - c = X ^ n (X ^ n' - b) + b (X ^ n - a) + (a b - c)`. -/
theorem mul_step {q : ℕ} {f a b c : (ZMod q)[X]} {n n' k : ℕ} (hk : k = n + n')
    (h : XPow f n a) (h2 : XPow f n' b) (h3 : f ∣ a * b - c) : XPow f k c := by
  subst hk
  have h' : f ∣ (X : (ZMod q)[X]) ^ n - a := h
  have h2' : f ∣ (X : (ZMod q)[X]) ^ n' - b := h2
  have e : (X : (ZMod q)[X]) ^ (n + n') - c =
      X ^ n * (X ^ n' - b) + b * (X ^ n - a) + (a * b - c) := by
    ring
  show f ∣ _
  rw [e]
  exact dvd_add (dvd_add (h2'.mul_left _) (h'.mul_left _)) h3

/-- The product of the five irreducible factors of degree `11` of `Ψ₁₁ mod 23` on the `j = −121` row. -/
noncomputable def hPolyElevenA : (ZMod 23)[X] :=
  X^55 + 11*X^54 + 12*X^53 + 22*X^52 + 10*X^51 + 10*X^50 + 13*X^49 + 20*X^48 + X^47 + 12*X^46 +
    13*X^45 + 10*X^44 + 11*X^43 + 2*X^42 + 7*X^41 + 9*X^40 + 16*X^39 + 2*X^38 + 5*X^37 + 16*X^36 +
    5*X^35 + 17*X^34 + 17*X^33 + 16*X^31 + 19*X^30 + 20*X^29 + 19*X^28 + 21*X^27 + 3*X^26 +
    8*X^25 + X^24 + 6*X^23 + 4*X^22 + 9*X^21 + 4*X^20 + 14*X^19 + 13*X^18 + 22*X^17 + 4*X^16 +
    10*X^14 + 15*X^13 + 10*X^12 + 19*X^11 + 6*X^10 + 7*X^9 + 16*X^8 + 22*X^7 + 2*X^6 + 21*X^5 +
    22*X^4 + 6*X^3 + X^2 + 4*X + 19

/-- The product of the five irreducible factors of degree `11` of `Ψ₁₁ mod 23` on the `j = −24729001` row. -/
noncomputable def hPolyElevenB : (ZMod 23)[X] :=
  X^55 + 11*X^54 + 9*X^53 + 20*X^52 + X^51 + 13*X^50 + 2*X^49 + 3*X^48 + 2*X^47 + 8*X^46 +
    8*X^45 + 4*X^44 + 9*X^42 + 4*X^41 + 17*X^40 + 22*X^39 + 7*X^38 + 11*X^37 + 20*X^36 +
    8*X^34 + 17*X^33 + 9*X^32 + 16*X^31 + 16*X^30 + 3*X^29 + 18*X^28 + X^27 + 16*X^26 +
    4*X^25 + 13*X^24 + 14*X^23 + 12*X^22 + 20*X^21 + 10*X^20 + 15*X^19 + 7*X^18 + 16*X^17 +
    2*X^16 + 9*X^15 + 20*X^14 + 21*X^13 + 5*X^12 + X^11 + 15*X^10 + 7*X^9 + 22*X^8 + 9*X^7 +
    18*X^6 + 2*X^5 + 20*X^4 + 22*X^3 + 22*X^2 + 6

/-- The product of the four irreducible factors of degree `34` of `Ψ₁₇ mod 67` on the `j = −882216989/131072` row. -/
noncomputable def hPolySeventeenA : (ZMod 67)[X] :=
  X^136 + 31*X^135 + 54*X^134 + 23*X^133 + 2*X^132 + X^131 + 38*X^130 + 37*X^129 + 65*X^128 +
    46*X^127 + 49*X^126 + 39*X^125 + 43*X^124 + X^123 + 40*X^122 + 60*X^121 + 36*X^120 +
    20*X^119 + 4*X^118 + 40*X^117 + 30*X^116 + 49*X^115 + 39*X^114 + 37*X^113 + 12*X^112 +
    57*X^111 + 58*X^110 + 59*X^109 + 23*X^108 + 58*X^107 + 47*X^106 + 32*X^105 + 33*X^104 +
    9*X^103 + 4*X^102 + 30*X^101 + 65*X^100 + 22*X^99 + 25*X^98 + 8*X^97 + 35*X^96 + 58*X^95 +
    8*X^94 + 28*X^93 + 55*X^92 + 50*X^91 + 53*X^90 + 17*X^89 + 21*X^88 + 42*X^87 + 30*X^86 +
    54*X^85 + 46*X^84 + 45*X^83 + 58*X^82 + 32*X^81 + 5*X^80 + 30*X^79 + 27*X^78 + 3*X^77 +
    50*X^76 + 8*X^75 + 66*X^74 + 23*X^73 + 49*X^72 + 54*X^71 + 58*X^70 + 13*X^69 + 28*X^68 +
    8*X^67 + 23*X^66 + 5*X^65 + 60*X^64 + 24*X^63 + 8*X^62 + 33*X^61 + 27*X^60 + 5*X^59 +
    23*X^58 + 43*X^57 + 61*X^56 + 52*X^55 + 19*X^54 + 46*X^53 + 55*X^52 + 66*X^51 + 48*X^50 +
    20*X^49 + 30*X^48 + 27*X^47 + 7*X^46 + 6*X^45 + 21*X^44 + 27*X^43 + 37*X^42 + 4*X^41 +
    22*X^40 + 20*X^39 + 9*X^38 + 42*X^37 + 65*X^36 + 22*X^35 + 24*X^34 + 26*X^33 + 28*X^32 +
    51*X^31 + 49*X^30 + 31*X^29 + 6*X^28 + 39*X^27 + 43*X^26 + 50*X^25 + 15*X^24 + 18*X^23 +
    5*X^22 + 23*X^21 + 17*X^20 + 18*X^19 + 43*X^18 + 21*X^17 + 2*X^16 + 4*X^15 + 33*X^14 +
    34*X^13 + 47*X^12 + 59*X^11 + 34*X^10 + X^9 + 62*X^8 + 58*X^7 + 42*X^6 + 58*X^5 + 18*X^4 +
    26*X^3 + 58*X^2 + 15*X + 43

/-- The product of the four irreducible factors of degree `34` of `Ψ₁₇ mod 67` on the `j = −297756989/2` row. -/
noncomputable def hPolySeventeenB : (ZMod 67)[X] :=
  X^136 + 37*X^135 + 20*X^134 + 58*X^133 + 63*X^132 + 14*X^131 + 62*X^130 + 27*X^129 + 42*X^128 +
    15*X^127 + 13*X^126 + 52*X^125 + 25*X^124 + 20*X^123 + 16*X^122 + 37*X^121 + 29*X^120 +
    45*X^119 + 61*X^118 + 49*X^117 + 54*X^116 + 33*X^114 + 42*X^113 + 59*X^112 + 21*X^111 +
    28*X^110 + 42*X^109 + 14*X^108 + 37*X^107 + 23*X^106 + 16*X^105 + 7*X^104 + 41*X^103 +
    13*X^102 + 36*X^101 + 36*X^100 + 30*X^99 + 48*X^98 + 31*X^97 + 41*X^96 + 41*X^95 + 52*X^94 +
    29*X^93 + 6*X^92 + 60*X^91 + 9*X^90 + 63*X^89 + 30*X^88 + 43*X^87 + 35*X^86 + 44*X^85 +
    10*X^84 + 40*X^83 + 27*X^82 + 65*X^81 + 33*X^80 + 14*X^79 + 39*X^78 + 34*X^77 + 64*X^76 +
    54*X^75 + 40*X^74 + 32*X^73 + 34*X^72 + 56*X^71 + 41*X^70 + 14*X^69 + 47*X^68 + 25*X^67 +
    41*X^66 + 18*X^65 + 10*X^64 + 62*X^63 + 36*X^62 + 32*X^61 + 5*X^60 + 38*X^59 + 53*X^58 +
    21*X^57 + 32*X^56 + 58*X^55 + 54*X^54 + 16*X^53 + 49*X^52 + 39*X^51 + 28*X^50 + 31*X^49 +
    30*X^48 + 58*X^47 + 9*X^46 + 3*X^45 + 30*X^44 + 64*X^43 + 53*X^42 + 51*X^41 + 48*X^40 +
    22*X^39 + 3*X^38 + 42*X^37 + 53*X^36 + 15*X^35 + 62*X^34 + 23*X^33 + 29*X^32 + 61*X^31 +
    47*X^30 + 33*X^29 + 31*X^28 + 2*X^27 + 30*X^26 + 34*X^25 + 58*X^24 + 30*X^23 + 37*X^22 +
    26*X^21 + 45*X^20 + 14*X^19 + 6*X^18 + 62*X^17 + 51*X^16 + 5*X^15 + 39*X^14 + 54*X^12 +
    63*X^11 + 41*X^10 + 29*X^9 + 17*X^8 + 42*X^7 + 61*X^6 + 50*X^5 + 8*X^4 + 34*X^3 + 48*X^2 +
    60*X + 41

end Fermat.MazurNonCMCertificate

#!/usr/bin/env python3
"""Write the real project modules for the six computational leaves.

Layout, chosen because elaboration is single-threaded PER FILE and these four rows are
independent:

    Fermat/FLT/EllipticCurve/MazurNonCMFrobenius.lean            `XPow` and the step lemmas,
                                                                 plus the four `hPoly*`
                                                                 (MOVED out of
                                                                 MazurNonCMCertificate.lean)
    Fermat/FLT/EllipticCurve/MazurNonCMFrobenius/ElevenA.lean     one row each
                                                    /ElevenB.lean
                                                    /SeventeenA.lean
                                                    /SeventeenB.lean
"""
import os
import sys

from gen_all import ROWS, extract
from gen_row import SPLIT, body, body_split

LICENSE = """/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

"""

BASE_DOC = """/-!
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

"""

BASE_IMPORTS = """public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ReduceModChar

"""

BASE_BODY = """@[expose] public section

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

"""

ROW_DOC = {
    "ElevenA": ("`p = 11`, `j = −121`", "23", "11"),
    "ElevenB": ("`p = 11`, `j = −24729001`", "23", "11"),
    "SeventeenA": ("`p = 17`, `j = −882216989/131072`", "67", "34"),
    "SeventeenB": ("`p = 17`, `j = −297756989/2`", "67", "34"),
}

HDOC = {
    "hPolyElevenA": "The product of the five irreducible factors of degree `11` of `Ψ₁₁ mod 23` on the "
                    "`j = −121` row.",
    "hPolyElevenB": "The product of the five irreducible factors of degree `11` of `Ψ₁₁ mod 23` on the "
                    "`j = −24729001` row.",
    "hPolySeventeenA": "The product of the four irreducible factors of degree `34` of `Ψ₁₇ mod 67` on "
                       "the `j = −882216989/131072` row.",
    "hPolySeventeenB": "The product of the four irreducible factors of degree `34` of `Ψ₁₇ mod 67` on "
                       "the `j = −297756989/2` row.",
}


def write_base(root):
    out = [LICENSE, BASE_IMPORTS, BASE_DOC, BASE_BODY]
    for tag, (hname, q, m) in ROWS.items():
        out.append(f"/-- {HDOC[hname]} -/\nnoncomputable def {hname} : (ZMod {q})[X] :=\n  "
                   + extract(hname) + "\n\n")
    out.append("end Fermat.MazurNonCMCertificate\n")
    with open(os.path.join(root, "Fermat/FLT/EllipticCurve/MazurNonCMFrobenius.lean"), "w") as f:
        f.write("".join(out))


PREAMBLE = """@[expose] public section

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

"""

ROW_HEAD = """/-!
# Row {which}: `H ∣ X ^ ({ql} ^ {ml}) - X`

The certificate is machine-checked twice outside Lean — PARI/GP 2.15.4 and an independent
Python reimplementation — and then re-derived here by the compiler, which is the only check
that counts.  Everything below is generated; see `MazurNonCMFrobenius.lean` for `XPow` and why
the exponents have to stay behind it.
-/

"""

SPLIT_ROW_HEAD = """/-!
# Row {which}: `H ∣ X ^ ({ql} ^ {ml}) - X`, and `IsCoprime H (X ^ ({ql} ^ 2) - X)`

The certificate is machine-checked twice outside Lean — PARI/GP 2.15.4 and an independent
Python reimplementation — and then re-derived here by the compiler, which is the only check
that counts.  Everything below is generated; see `MazurNonCMFrobenius.lean` for `XPow` and why
the exponents have to stay behind it.

**THIS ROW IS SPLIT ONE MODULE PER FACTOR, AND THE SPLIT IS WHAT MAKES IT BUILD AT ALL.**
Lean elaborates a module SINGLE-THREADED, so the whole row in one file — 14 200 lines, ~2 500
theorems — was still running after 60 minutes at 47 GB resident when it was stopped
(2026-07-31).  `H` is a product of {k} pairwise-coprime factors of degree {d} whose
square-and-multiply chains share nothing but the factor definitions, so each chain lives in
`{tag}/Factor{{i}}.lean` and `lake` elaborates the {k} of them CONCURRENTLY.  What is left here
is everything that mentions more than one factor: the product identity, the {pairs} Bézout
coprimalities, the `xpow_mul` assembly and the coprimality leaf.
-/

"""

FACTOR_HEAD = """/-!
# Row {which}: factor {i} of `H`, and its two square-and-multiply chains

Generated.  This module holds ONE of the {k} pairwise-coprime degree-`{d}` factors of `H` and
the two chains run modulo it: `X ^ ({ql} ^ {ml})` for the divisibility, and `X ^ ({ql} ^ 2)` for
the coprimality.  Both chains start from the same `XPow f 1 X`, so they cannot be separated
from each other; nothing else in the row refers to anything here except the final step of each
chain and the factor's own definition.

It is a separate module because elaboration is single-threaded per module — see
`{tag}.lean` for the measurement.  Every identity handed to `ring_nf` has degree `< 2 · {d}`
however large the exponent, which is what square-and-multiply buys.
-/

"""


def _wrap(head, bodytext, imports):
    return (LICENSE + imports + "\n" + head + PREAMBLE + bodytext
            + "end Fermat.MazurNonCMCertificate\n")


def write_row(root, tag):
    hname, q, m = ROWS[tag]
    which, ql, ml = ROW_DOC[tag]
    d = os.path.join(root, "Fermat/FLT/EllipticCurve/MazurNonCMFrobenius")
    os.makedirs(d, exist_ok=True)
    base_import = "public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius\n"

    if tag not in SPLIT:
        txt = _wrap(ROW_HEAD.format(which=which, ql=ql, ml=ml), body(tag), base_import)
        with open(os.path.join(d, tag + ".lean"), "w") as f:
            f.write(txt)
        return 1

    parent, factor_bodies, deg = body_split(tag)
    k = len(factor_bodies)
    sub = os.path.join(d, tag)
    os.makedirs(sub, exist_ok=True)
    for i, fb in enumerate(factor_bodies):
        head = FACTOR_HEAD.format(which=which, i=i + 1, k=k, d=deg, ql=ql, ml=ml, tag=tag)
        with open(os.path.join(sub, f"Factor{i + 1}.lean"), "w") as f:
            f.write(_wrap(head, fb, base_import))
    imports = "".join(
        f"public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.{tag}.Factor{i + 1}\n"
        for i in range(k))
    head = SPLIT_ROW_HEAD.format(which=which, ql=ql, ml=ml, k=k, d=deg, tag=tag,
                                 pairs=k * (k - 1) // 2)
    with open(os.path.join(d, tag + ".lean"), "w") as f:
        f.write(_wrap(head, parent, imports))
    return k + 1


if __name__ == "__main__":
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    write_base(root)
    n = 1
    for tag in ROWS:
        n += write_row(root, tag)
    print(f"wrote {n} modules")

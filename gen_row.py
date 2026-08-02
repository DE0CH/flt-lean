#!/usr/bin/env python3
"""Emit one row's factored Frobenius module (or a standalone scratch version of it)."""
import io
import sys

from gen_all import ROWS, extract
from gen_factored import generate_row, generate_row_split
from gen_frobenius import parse_poly

COPRIME_AT = {"SeventeenA": 2, "SeventeenB": 2}

#  Rows whose module is SPLIT one file per factor.  See `generate_row_split`: elaboration is
#  single-threaded per module, and at `q = 67`, `m = 34` a single file does not finish.
SPLIT = {"SeventeenA", "SeventeenB"}


def factors(tag):
    out, cur = [], []
    for line in open(f"/tmp/fac-{tag}.txt"):
        line = line.strip()
        if not line:
            continue
        if line.startswith("MULT"):
            assert line.split()[1] == "1", "H is not squarefree"
            out.append(" ".join(cur).replace("x", "X"))
            cur = []
        else:
            cur.append(line)
    return out


def body(tag, doc=""):
    hname, q, m = ROWS[tag]
    out = io.StringIO()
    generate_row(hname, extract(hname), factors(tag), q, m, tag,
                 COPRIME_AT.get(tag), doc, out)
    return out.getvalue()


def body_split(tag, doc=""):
    """`(parent body, [factor bodies], factor degree)` for a row emitted one module per factor."""
    hname, q, m = ROWS[tag]
    fs = factors(tag)
    out = io.StringIO()
    fouts = [io.StringIO() for _ in fs]
    generate_row_split(hname, extract(hname), fs, q, m, tag,
                       COPRIME_AT.get(tag), doc, out, fouts)
    degs = {len(parse_poly(s, q)) - 1 for s in fs}
    assert len(degs) == 1, f"factors of unequal degree: {sorted(degs)}"
    return out.getvalue(), [o.getvalue() for o in fouts], degs.pop()


SCRATCH_HEAD = """import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ScratchRow

/-- `XPow f n a` is `f ∣ X ^ n - a`, kept behind a definition on purpose.

MEASURED 2026-07-31, and it is the whole reason this development has the shape it has:
stating a chain step as `f ∣ X ^ n - a` directly makes the elaborator `whnf` `X ^ n` when it
unifies the step against its own statement, and `whnf` unfolds `npowRec` ONCE PER UNIT of `n`.
The recursion depth is then `≈ 3 n`, so a step at `n = 6932` already needs `maxRecDepth 20000`
and a step at `n = 23 ^ 11` needs `10 ^ 15` — it blows an 8 MB thread stack, a 64 MB one and a
256 MB one, in that order, with no error message beyond `Stack overflow detected`.

Behind `XPow` the exponent is an ARGUMENT, so unification assigns `?n := 952809757913926` and
never looks inside `X ^ ?n`.  Same statement, same proof, 8 s instead of a crash. -/
def XPow {q : ℕ} (f : (ZMod q)[X]) (n : ℕ) (a : (ZMod q)[X]) : Prop := f ∣ X ^ n - a

theorem xpow_one {q : ℕ} (f : (ZMod q)[X]) : XPow f 1 X := by simp [XPow]

theorem xpow_dvd {q : ℕ} {f a : (ZMod q)[X]} {n : ℕ} (h : XPow f n a) : f ∣ X ^ n - a := h

/-- Discharge `X ^ (Nat.card (ZMod q)) ^ m` against a chain that ends at the LITERAL
`q ^ m`.  Going through `hN` as a `ℕ` equation is deliberate: `rw`-ing that equation
inside `X ^ _` puts the literal back in exponent position and costs `≈ 3 q ^ m` recursion. -/
theorem xpow_card {q m N : ℕ} {f a : (ZMod q)[X]} (hN : Nat.card (ZMod q) ^ m = N)
    (h : XPow f N a) : f ∣ X ^ (Nat.card (ZMod q)) ^ m - a := by
  subst hN
  exact h

theorem xpow_mul {q : ℕ} {f g a : (ZMod q)[X]} {n : ℕ} (hc : IsCoprime f g)
    (h : XPow f n a) (h2 : XPow g n a) : XPow (f * g) n a :=
  hc.mul_dvd h h2

theorem sq_step {q : ℕ} {f a b : (ZMod q)[X]} {n n' : ℕ} (hn : n' = n + n)
    (h : XPow f n a) (h2 : f ∣ a * a - b) : XPow f n' b := by
  subst hn
  have h' : f ∣ (X : (ZMod q)[X]) ^ n - a := h
  have e : (X : (ZMod q)[X]) ^ (n + n) - b = (X ^ n - a) * (X ^ n + a) + (a * a - b) := by
    ring
  show f ∣ _
  rw [e]
  exact dvd_add (h'.mul_right _) h2

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


if __name__ == "__main__":
    tag = sys.argv[1]
    hname, q, m = ROWS[tag]
    if "--scratch" in sys.argv:
        sys.stdout.write(SCRATCH_HEAD)
        sys.stdout.write(f"instance : Fact (Nat.Prime {q}) := ⟨by norm_num⟩\n\n")
        sys.stdout.write(f"noncomputable def {hname} : (ZMod {q})[X] :=\n  "
                         + extract(hname) + "\n\n")
        sys.stdout.write(body(tag))
        sys.stdout.write("end ScratchRow\n")
    else:
        sys.stdout.write(body(tag))

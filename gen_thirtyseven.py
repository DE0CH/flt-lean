#!/usr/bin/env python3
"""Generator for the two `p = 37` rows of Mazur's non-CM table at `ℓ = 1259`.

Emits, per row `tag ∈ {ThirtySevenA, ThirtySevenB}`:

  Fermat/FLT/EllipticCurve/MazurNonCMReflect.lean            shared reflection layer
                                                             (`npoly` over `List ℕ`) and the
                                                             two `hPoly*` (degree 666)
  Fermat/FLT/EllipticCurve/MazurNonCMFrobenius/{tag}/Factor{1..18}.lean
                                                             one square-and-multiply chain per
                                                             degree-37 factor of `H`
  Fermat/FLT/EllipticCurve/MazurNonCMFrobenius/{tag}.lean    product identity, 153 Bézout
                                                             coprimalities, assembly
  Fermat/FLT/EllipticCurve/MazurNonCMCertificate/{tag}.lean  the EDS chain `preΨ' 37 mod 1259`
                                                             and the row's obstruction theorem

WHY REFLECTION AND NOT `ring_nf` (measured 2026-08-03, this worktree, shadowcat).  The
`ring_nf` shape of the `p = 17` rows stores a ~2.4 MB proof term PER CHAIN STEP: 794 MB of
`.olean.private` per degree-34 factor module.  At `p = 37` there are THIRTY-SIX degree-37
factor modules of 594 steps each — ~50 GB of oleans, which neither the release snapshot's
volume (67 GB, 11 GB free) nor any worktree seeding path can carry.  A step proven by `decide`
on an explicit coefficient-list identity stores only `of_decide_eq_true rfl`; the olean cost
collapses to the statements.  Measured per-step cost, 24 real steps, fleet under load:
plain `decide` 1.4–1.8 s + kernel re-check 0.43–0.66 s, FLAT in file position; `ring_nf` on
the same steps 1.5–2.7 s and the megabyte terms.  `decide +kernel` is BANNED here: its
type-check time GROWS ~0.31 s per declaration with file position (measured twice, chained and
independent-seed variants both), which is quadratic death over 578 steps.

Every identity below is verified in this script's own `F_q[X]` arithmetic (an exact mirror of
the Lean list ops — same padding, same reduction points) before it is emitted, and the PARI
factorisation is only a SEARCH: the Lean kernel re-derives the product, the coprimalities and
both chains; nothing needs the factors irreducible.

Regenerating committed output must reproduce it byte for byte:

    python3 gen_thirtyseven.py            # writes the production modules into the worktree
    python3 gen_thirtyseven.py --scratch  # writes Scratch155C.lean (mathlib-only dress
                                          # rehearsal of the certificate module, leaves
                                          # axiomatised)
"""
import os
import re
import subprocess
import sys

Q = 1259
P = 37

CURVES = {
    "ThirtySevenA": (1, 1, 1, -8, 6),
    "ThirtySevenB": (1, 1, 1, -208083, -36621194),
}

# ------------------------------------------------------------------ list mirrors
# These four mirror the Lean definitions in MazurNonCMReflect.lean EXACTLY: no
# trimming inside, reduction mod Q at the same points.  Every emitted `decide`
# target is checked with them, so a mismatch between mirror and Lean op is the
# ONLY way an emitted identity can be false — and then the Lean build fails.

def nadd(u, v):
    if not u:
        return list(v)
    if not v:
        return list(u)
    return [(u[0] + v[0]) % Q] + nadd(u[1:], v[1:])


def nscale(a, v):
    return [a * b % Q for b in v]


def nmul(u, v):
    if not u:
        return []
    return nadd(nscale(u[0], v), [0] + nmul(u[1:], v))


def npow(u, k):
    r = [1]
    for _ in range(k):
        r = nmul(r, u)
    return r


def nneg(v):
    return [(Q - b % Q) % Q for b in v]


def ntrim(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return l


# ------------------------------------------------------------------ plain arithmetic
def trim(a):
    a = list(a)
    while a and a[-1] % Q == 0:
        a.pop()
    return [x % Q for x in a]


def padd(a, b):
    n = max(len(a), len(b))
    return trim([((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % Q
                 for i in range(n)])


def psub(a, b):
    n = max(len(a), len(b))
    return trim([((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % Q
                 for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    r[i + j] = (r[i + j] + x * y) % Q
    return trim(r)


def divmod_poly(a, b):
    """`b` monic; `(quo, rem)`, both trimmed."""
    a = [x % Q for x in a]
    b = ntrim([x % Q for x in b])
    assert b and b[-1] == 1
    quo = [0] * (max(len(a) - len(b) + 1, 0))
    r = list(a)
    for i in range(len(a) - len(b), -1, -1):
        c = r[i + len(b) - 1] % Q
        if c:
            quo[i] = c
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] - c * y) % Q
    return ntrim([x % Q for x in quo]), ntrim([x % Q for x in r[:len(b) - 1]])


def monic_scale(a):
    inv = pow(a[-1], Q - 2, Q)
    return trim([x * inv for x in a])


def xgcd(a, b):
    """`(g, u, v)` with `u a + v b = g`, `g` monic (both inputs nonzero)."""
    r0, r1 = trim(a), trim(b)
    s0, s1 = [1], []
    t0, t1 = [], [1]
    while r1:
        inv = pow(r1[-1], Q - 2, Q)
        quo, rem = divmod_poly(r0, monic_scale(r1))
        quo = trim([x * inv for x in quo])
        r0, r1 = r1, rem
        s0, s1 = s1, psub(s0, pmul(quo, s1))
        t0, t1 = t1, psub(t0, pmul(quo, t1))
    inv = pow(r0[-1], Q - 2, Q)
    return (trim([x * inv for x in r0]), trim([x * inv for x in s0]),
            trim([x * inv for x in t0]))


def bezout_pair(f, g):
    d, u, v = xgcd(f, g)
    assert d == [1], f"not coprime: gcd degree {len(d) - 1}"
    assert padd(pmul(u, f), pmul(v, g)) == [1]
    return u, v


# ------------------------------------------------------------------ EDS recursion
def curve_polys(a1, a2, a3, a4, a6):
    a1, a2, a3, a4, a6 = [x % Q for x in (a1, a2, a3, a4, a6)]
    b2 = (a1 * a1 + 4 * a2) % Q
    b4 = (2 * a4 + a1 * a3) % Q
    b6 = (a3 * a3 + 4 * a6) % Q
    b8 = (a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4) % Q
    psi2sq = trim([b6, 2 * b4, b2, 4])
    psi3 = trim([b8, 3 * b6, 3 * b4, b2, 3])
    prepsi4 = trim([b4 * b8 - b6 * b6, b2 * b8 - b4 * b6, 10 * b8, 10 * b6, 5 * b4, b2, 2])
    return psi2sq, psi3, prepsi4


def prepsi_table(curve):
    """Mirrors mathlib's `preNormEDS' (Ψ₂Sq ^ 2) Ψ₃ preΨ₄` exactly."""
    psi2sq, psi3, prepsi4 = curve_polys(*curve)
    c = pmul(psi2sq, psi2sq)
    tab = {0: [], 1: [1], 2: [1], 3: psi3, 4: prepsi4}

    def get(n):
        if n in tab:
            return tab[n]
        if n % 2 == 0:
            m = n // 2 - 3
            v = psub(pmul(pmul(pmul(get(m + 2), get(m + 2)), get(m + 3)), get(m + 5)),
                     pmul(pmul(get(m + 1), get(m + 3)), pmul(get(m + 4), get(m + 4))))
        else:
            m = (n - 1) // 2 - 2
            t1 = pmul(get(m + 4), pmul(get(m + 2), pmul(get(m + 2), get(m + 2))))
            t2 = pmul(get(m + 1), pmul(get(m + 3), pmul(get(m + 3), get(m + 3))))
            if m % 2 == 0:
                t1 = pmul(t1, c)
            else:
                t2 = pmul(t2, c)
            v = psub(t1, t2)
        tab[n] = v
        return v

    get(P)
    return tab, psi2sq, psi3, prepsi4


# ------------------------------------------------------------------ factorisation (PARI, search only)
def gp_factor(poly):
    src = " + ".join(f"{c}*x^{i}" for i, c in enumerate(poly) if c)
    script = (f"default(parisize, 2000000000);\n"
              f"F = factormod({src}, {Q});\n"
              "for (i = 1, matsize(F)[1],"
              " print(lift(lift(F[i,1]))); print(\"MULT \", F[i,2]));\n")
    out = subprocess.run(["gp", "-q"], input=script, capture_output=True, text=True,
                        timeout=1200)
    if out.returncode != 0:
        raise SystemExit("gp failed: " + out.stderr)
    factors, cur = [], []
    for line in out.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("MULT"):
            assert line.split()[1] == "1", "Ψ₃₇ mod 1259 is not squarefree"
            factors.append(parse_gp(" ".join(cur)))
            cur = []
        else:
            cur.append(line)
    return factors


def parse_gp(s):
    s = s.replace("-", "+-")
    coeffs = {}
    for t in (t.strip() for t in s.split("+") if t.strip()):
        m = re.fullmatch(r"(-?\d+)?\s*\*?\s*x(?:\^(\d+))?", t)
        if m:
            g = m.group(1)
            c = int(g) if g not in (None, "", "-") else (-1 if g == "-" else 1)
            e = int(m.group(2)) if m.group(2) else 1
        else:
            c, e = int(t), 0
        coeffs[e] = coeffs.get(e, 0) + c
    return [coeffs.get(i, 0) % Q for i in range(max(coeffs) + 1)]


# ------------------------------------------------------------------ square-and-multiply chain
def bin_chain(n):
    bits = bin(n)[2:]
    plan, exp = [], 1
    for b in bits[1:]:
        plan.append(("sq", exp * 2))
        exp *= 2
        if b == "1":
            plan.append(("mul", exp + 1))
            exp += 1
    assert exp == n
    return plan


def pad(l, n):
    assert len(l) <= n
    return l + [0] * (n - len(l))


def chain_steps(f, n):
    """All steps of the square-and-multiply chain for `X ^ n mod f`, mirror-verified.

    Padding scheme (probe-verified 2026-08-03): accumulator and remainder lists are always
    37-long, squaring cofactors 36-long, multiply-by-`X` cofactors 1-long.  With FIXED lengths
    every step identity `f·Q + rem = a·a` (resp. `= 0 :: a`) is literally true as lists —
    including the early steps where the true cofactor is empty — because both sides are
    computed by the same reduced-mod-`q` operations.  The first step (always `X ^ 2`) is
    emitted through `npoly_XX_pad` instead of a `decide`, and the chain end (`X` again, padded)
    converts through `npoly_X_pad`.
    """
    d = len(f) - 1
    a, out = pad([0, 1], d), []
    for kind, newexp in bin_chain(n):
        prod = nmul(a, a) if kind == "sq" else [0] + a
        quo, rem = divmod_poly(prod, f)
        rem = pad(rem, d)
        quo = pad(quo, d - 1 if kind == "sq" else 1)
        lhs = nadd(nmul(f, quo), rem)
        assert lhs == prod, f"identity mismatch at {kind} {newexp}"
        out.append((kind, newexp, quo, rem))
        a = rem
    return out, a


# ------------------------------------------------------------------ formatting
def fmt_list(l, indent="      ", width=96):
    toks = [("[" if i == 0 else "") + str(x) + ("," if i < len(l) - 1 else "]")
            for i, x in enumerate(l)]
    if not l:
        return "[]"
    lines, line = [], indent
    for tok in toks:
        if len(line) + len(tok) + 1 > width and line.strip():
            lines.append(line)
            line = indent
        line += (" " if line.strip() else "") + tok
    lines.append(line)
    return "\n".join(lines).lstrip()


def fmt_poly(l, indent="    ", width=96):
    terms = []
    for i in range(len(l) - 1, -1, -1):
        c = l[i]
        if c == 0:
            continue
        if i == 0:
            terms.append(f"{c}")
        elif i == 1:
            terms.append("X" if c == 1 else f"{c}*X")
        else:
            terms.append(f"X^{i}" if c == 1 else f"{c}*X^{i}")
    if not terms:
        return "0"
    s = " + ".join(terms)
    lines, line = [], indent
    for tok in s.split(" "):
        if len(line) + len(tok) + 1 > width and line.strip():
            lines.append(line)
            line = indent
        line += (" " if line.strip() else "") + tok
    lines.append(line)
    return "\n".join(lines).lstrip()


NUMERAL = {5: "five", 6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten",
           11: "eleven", 12: "twelve", 17: "seventeen", 18: "eighteen",
           19: "nineteen", 20: "twenty", 37: "thirtySeven"}

# ------------------------------------------------------------------ row data
class Row:
    def __init__(self, tag):
        self.tag = tag
        self.curve = CURVES[tag]
        self.tab, self.psi2sq, self.psi3, self.prepsi4 = prepsi_table(self.curve)
        p37 = self.tab[P]
        assert len(p37) - 1 == 684 and p37[-1] == 37
        fac = gp_factor(p37)
        lin = sorted([f for f in fac if len(f) == 2])
        big = sorted([f for f in fac if len(f) == 38])
        assert len(lin) == 18 and len(big) == 18 and len(fac) == 36
        self.linear, self.factors = lin, big
        self.dpoly = [1]
        for f in lin:
            self.dpoly = pmul(self.dpoly, f)
        self.hpoly = [1]
        for f in big:
            self.hpoly = pmul(self.hpoly, f)
        assert len(self.dpoly) - 1 == 18 and len(self.hpoly) - 1 == 666
        assert pmul([37], pmul(self.dpoly, self.hpoly)) == p37
        # both chains per factor: N = Q^37 for the divisibility, Q for the coprimality
        self.chains, self.cochains = [], []
        for f in big:
            st, end = chain_steps(f, Q ** P)
            assert ntrim(end) == [0, 1], "big chain must end at X"
            self.chains.append(st)
            st2, end2 = chain_steps(f, Q)
            self.cochains.append((st2, end2))


# ------------------------------------------------------------------ Lean emission
LICENSE = """/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

"""

REFL_BODY = """@[expose] public section

open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Fermat.MazurNonCMCertificate

/-! ### Coefficient lists over `ℕ`, and their polynomials over `ZMod q`

Chain values, cofactors and Bézout witnesses below are LISTS OF `ℕ` LITERALS, low degree
first, every entry already reduced mod `q`.  The four list operations reduce mod `q` at every
entry, so a computed list is always literally equal to the canonical one and `decide` can
check any identity by pure `Nat` arithmetic — no `Fin` wrapper, no `OfNat` instance, nothing
the kernel is slow at.  `npoly` is the bridge back to `(ZMod q)[X]`; the `npoly_*` lemmas say
it is a ring homomorphism from the list side, and they are the ONLY facts a consumer needs.

`decide +kernel` is deliberately NOT used anywhere: measured 2026-08-03 (24-step probes,
chained and independent), its per-declaration type-check time grows ~0.31 s with FILE
POSITION, which is quadratic in the length of a chain module.  Plain `decide` is flat. -/

/-- Pointwise addition mod `q`; the longer tail is kept as is (its entries are already
reduced). -/
def nadd (q : ℕ) : List ℕ → List ℕ → List ℕ
  | [], v => v
  | u, [] => u
  | a :: u, b :: v => (a + b) % q :: nadd q u v

/-- Scalar multiplication mod `q`. -/
def nscale (q a : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: v => a * b % q :: nscale q a v

/-- Polynomial multiplication mod `q` (schoolbook, structural in the first list). -/
def nmul (q : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: u, v => nadd q (nscale q a v) (0 :: nmul q u v)

/-- `u ^ k` on lists. -/
def npow (q : ℕ) (u : List ℕ) : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => nmul q (npow q u k) u

/-- Pointwise negation mod `q`. -/
def nneg (q : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: v => (q - b % q) % q :: nneg q v

/-- Drop trailing zeros (a Bézout combination computes as a full-length list `1 :: 0 :: …`;
`ntrim` brings it to the literal `[1]`). -/
def ntrim : List ℕ → List ℕ
  | [] => []
  | a :: t =>
    match ntrim t with
    | [] => if a = 0 then [] else [a]
    | r => a :: r

/-- The polynomial with coefficient list `l`, low degree first. -/
noncomputable def npoly (q : ℕ) : List ℕ → (ZMod q)[X]
  | [] => 0
  | a :: u => C (a : ZMod q) + X * npoly q u

theorem npoly_nadd (q : ℕ) (u v : List ℕ) :
    npoly q (nadd q u v) = npoly q u + npoly q v := by
  induction u generalizing v with
  | nil => cases v <;> simp [nadd, npoly]
  | cons a u ih =>
    cases v with
    | nil => simp [nadd, npoly]
    | cons b v =>
      simp only [nadd, npoly, ih, ZMod.natCast_mod, Nat.cast_add, map_add]
      ring

theorem npoly_nscale (q a : ℕ) (v : List ℕ) :
    npoly q (nscale q a v) = C (a : ZMod q) * npoly q v := by
  induction v with
  | nil => simp [nscale, npoly]
  | cons b v ih =>
    simp only [nscale, npoly, ih, ZMod.natCast_mod, Nat.cast_mul, map_mul]
    ring

theorem npoly_nmul (q : ℕ) (u v : List ℕ) :
    npoly q (nmul q u v) = npoly q u * npoly q v := by
  induction u with
  | nil => simp [nmul, npoly]
  | cons a u ih =>
    simp only [nmul, npoly_nadd, npoly_nscale, npoly, ih, Nat.cast_zero, map_zero]
    ring

theorem npoly_npow (q : ℕ) (u : List ℕ) (k : ℕ) :
    npoly q (npow q u k) = npoly q u ^ k := by
  induction k with
  | zero => simp [npow, npoly]
  | succ k ih => simp only [npow, npoly_nmul, ih, pow_succ]

theorem npoly_nneg (q : ℕ) [NeZero q] (v : List ℕ) :
    npoly q (nneg q v) = - npoly q v := by
  induction v with
  | nil => simp [nneg, npoly]
  | cons b v ih =>
    have hb : ((q - b % q : ℕ) : ZMod q) = -(b : ZMod q) := by
      have h1 : ((q : ℕ) : ZMod q) = 0 := ZMod.natCast_self q
      have h2 : b % q ≤ q := le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)))
      rw [Nat.cast_sub h2, h1, ZMod.natCast_mod]
      ring
    simp only [nneg, npoly, ih, ZMod.natCast_mod, hb, map_neg]
    ring

theorem npoly_ntrim (q : ℕ) (l : List ℕ) : npoly q (ntrim l) = npoly q l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show npoly q (match ntrim t with
      | [] => if a = 0 then [] else [a]
      | r => a :: r) = _
    rcases ht : ntrim t with _ | ⟨b, r⟩ <;> rw [ht] at ih
    · rcases ha : a with _ | n
      · simp [npoly, ← ih]
      · simp [npoly, ← ih]
    · simp [npoly, ← ih]

theorem npoly_X (q : ℕ) : npoly q [0, 1] = X := by
  simp [npoly]

/-- `X`, padded to the 37-slot accumulator width the `p = 37` chains use. -/
theorem npoly_X_pad (q : ℕ) : npoly q
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0] = X := by
  simp [npoly]

/-- `X * X`, padded likewise; the first chain step (always `X ^ 2`) is discharged through
this instead of a `decide`. -/
theorem npoly_XX_pad (q : ℕ) : npoly q
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0] = X * X := by
  simp [npoly]

/-! ### Discharge lemmas: one per shape of certificate fact

Each takes the factor as an abstract polynomial plus its list form (`hf`, always a `rfl`
lemma), and the computational content as ONE list identity `h`, closed by `decide`. -/

/-- A squaring step's divisibility: `f ∣ a² − b` from `f·Q + b = a²` on lists. -/
theorem dvd_sq_of_lists {q : ℕ} {f : (ZMod q)[X]} {vf va vb : List ℕ} (vQ : List ℕ)
    (hf : f = npoly q vf)
    (h : nadd q (nmul q vf vQ) vb = nmul q va va) :
    f ∣ npoly q va * npoly q va - npoly q vb :=
  ⟨npoly q vQ, by
    have e := congrArg (npoly q) h
    rw [npoly_nadd, npoly_nmul, npoly_nmul] at e
    rw [hf]
    linear_combination -e⟩

/-- A multiply-by-`X` step's divisibility: `f ∣ a·X − b` from `f·Q + b = 0 :: a` on lists. -/
theorem dvd_mulX_of_lists {q : ℕ} {f : (ZMod q)[X]} {va vb : List ℕ} (vQ : List ℕ) {vf : List ℕ}
    (hf : f = npoly q vf)
    (h : nadd q (nmul q vf vQ) vb = 0 :: va) :
    f ∣ npoly q va * X - npoly q vb :=
  ⟨npoly q vQ, by
    have e := congrArg (npoly q) h
    rw [npoly_nadd, npoly_nmul] at e
    simp only [npoly, Nat.cast_zero, map_zero, zero_add] at e
    rw [hf]
    linear_combination -e⟩

/-- Coprimality from an explicit Bézout pair, all on lists. -/
theorem isCoprime_of_lists {q : ℕ} {f g : (ZMod q)[X]} {vf vg : List ℕ} (vu vv : List ℕ)
    (hf : f = npoly q vf) (hg : g = npoly q vg)
    (h : ntrim (nadd q (nmul q vu vf) (nmul q vv vg)) = [1]) :
    IsCoprime f g :=
  ⟨npoly q vu, npoly q vv, by
    have e := congrArg (npoly q) h
    rw [npoly_ntrim, npoly_nadd, npoly_nmul, npoly_nmul] at e
    rw [hf, hg]
    simpa [npoly] using e⟩

/-- Coprimality with `npoly r − X` from a Bézout pair against the shifted list — the form the
Frobenius-residue coprimality leaves take (`v·(r − X) = v·r − X·v`, and `X·v` is `0 :: v`). -/
theorem isCoprime_sub_X_of_lists {q : ℕ} [NeZero q] {f : (ZMod q)[X]} {vf vr : List ℕ}
    (vu vv : List ℕ) (hf : f = npoly q vf)
    (h : ntrim (nadd q (nmul q vu vf)
      (nadd q (nmul q vv vr) (0 :: nneg q vv))) = [1]) :
    IsCoprime f (npoly q vr - X) :=
  ⟨npoly q vu, npoly q vv, by
    have e := congrArg (npoly q) h
    rw [npoly_ntrim, npoly_nadd, npoly_nadd, npoly_nmul, npoly_nmul] at e
    simp only [npoly, Nat.cast_zero, Nat.cast_one, map_zero, map_one, zero_add, mul_zero,
      add_zero, npoly_nneg] at e
    rw [hf]
    linear_combination e⟩

end Fermat.MazurNonCMCertificate
"""


def eds_plan(n):
    """`(recursion call, norm_num extras, atom indices term1, term2, has_c_in_term1)`"""
    if n % 2 == 1:
        m = (n - 1) // 2 - 2
        idx1, idx2 = [m + 4, m + 2], [m + 1, m + 3]
        has_c = (m % 2 == 0)
        return ("odd", m, idx1, idx2, has_c)
    m = n // 2 - 3
    return ("even", m, [m + 2, m + 3, m + 5], [m + 1, m + 3, m + 4], None)


def atom_lemma(tag, k):
    if k <= 2:
        return None
    if k == 3:
        return f"Ψ₃_npoly_{tag}"
    if k == 4:
        return f"preΨ₄_npoly_{tag}"
    return f"preΨ'_{NUMERAL[k]}_{tag}"


def norm_num_extras(kind, m, idxs):
    ex = []
    if any(k in (1, 2) for k in idxs):
        ex += ["WeierstrassCurve.preΨ'_one", "WeierstrassCurve.preΨ'_two"]
    if any(k in (3, 4) for k in idxs):
        ex += ["WeierstrassCurve.preΨ'_three", "WeierstrassCurve.preΨ'_four"]
    if kind == "odd" and m >= 2:
        ex.append("Nat.even_iff")
    return ex


FINISHER = ("  simp only [← npoly_npow, ← npoly_nmul, sub_eq_add_neg, ← npoly_nneg,"
            " ← npoly_nadd]\n"
            "  exact congrArg (npoly 1259) (by decide)\n")


def emit_eds_theorem(w, row, n, scratch=False):
    tag = row.tag
    kind, m, idx1, idx2, _ = eds_plan(n)
    idxs = sorted(set(idx1 + idx2))
    atoms = []
    for k in idx1 + ([] if kind == "even" else []) + idx2:
        a = atom_lemma(tag, k)
        if a and a not in atoms:
            atoms.append(a)
    if kind == "odd":
        atoms.append(f"Ψ₂Sq_npoly_{tag}")
    extras = norm_num_extras(kind, m, idxs)
    nn = f"norm_num [{', '.join(extras)}] at h" if extras else "norm_num at h"
    name = f"preΨ'_{NUMERAL[n]}_{tag}"
    curvename = f"{tag[0].lower()}{tag[1:]}Mod" if False else CURVE_NAME[tag]
    if n == P:
        w(f"/-- **`Ψ₃₇ mod 1259 = 37 · D · H`** on this row, the certificate in the form\n"
          f"`not_monic_dvd_of_smallDegreePart'` consumes. -/\n")
        w(f"theorem {name} :\n    {curvename}.preΨ' 37 = C 37 * (dPoly{tag} * hPoly{tag}) := by\n")
    else:
        w(f"theorem {name} : {curvename}.preΨ' {n} = npoly 1259\n"
          f"    ({fmt_list(row.tab[n])}) := by\n")
    w(f"  have h := {curvename}.preΨ'_{kind} {m}\n")
    w(f"  {nn}\n")
    rwlist = ["h"] + atoms
    if n == P:
        rwlist += [f"C37_npoly_{tag}", f"dPoly_npoly_{tag}", f"hPoly{tag}_eq"]
    w("  rw [" + ", ".join(rwlist) + "]\n")
    w(FINISHER)
    w("\n")


CURVE_NAME = {"ThirtySevenA": "thirtySevenAMod", "ThirtySevenB": "thirtySevenBMod"}
JINV = {"ThirtySevenA": "j = −9317", "ThirtySevenB": "j = −162677523113838677"}


def emit_certificate_body(w, row, scratch=False):
    """The EDS chain and the row obstruction theorem (certificate-side module body)."""
    tag = row.tag
    cn = CURVE_NAME[tag]
    a1, a2, a3, a4, a6 = row.curve
    w(f"/-- The minimal model `[{a1}, {a2}, {a3}, {a4}, {a6}]` of the `p = 37`, `{JINV[tag]}`\n"
      f"row, read over `ZMod 1259`.  Definitionally `Fermat.nonCMModel{tag}mod`. -/\n")
    w(f"def {cn} : WeierstrassCurve (ZMod 1259) := ⟨{a1}, {a2}, {a3}, {a4}, {a6}⟩\n\n")

    w(f"/-- The product of the eighteen linear factors of `Ψ₃₇ mod 1259` on this row. -/\n")
    w(f"noncomputable def dPoly{tag} : (ZMod 1259)[X] :=\n  {fmt_poly(row.dpoly)}\n\n")

    # seed lemmas, classic form (the p = 17 proof shape, known good)
    for nm, val, mathlib_def, extra in [
            ("Ψ₂Sq", row.psi2sq, "WeierstrassCurve.Ψ₂Sq", ""),
            ("Ψ₃", row.psi3, "WeierstrassCurve.Ψ₃", " WeierstrassCurve.b₈,"),
            ("preΨ₄", row.prepsi4, "WeierstrassCurve.preΨ₄", " WeierstrassCurve.b₈,")]:
        w(f"theorem {nm}_{cn} : {cn}.{nm} =\n    {fmt_poly(val)} := by\n")
        w(f"  rw [{mathlib_def}]\n")
        w(f"  simp only [{cn}, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,"
          f"{extra}\n    map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1, C_0]\n")
        w("  reduce_mod_char\n\n")

    # npoly bridges for the seeds and D
    for nm, val in [("Ψ₂Sq", row.psi2sq), ("Ψ₃", row.psi3), ("preΨ₄", row.prepsi4)]:
        w(f"theorem {nm}_npoly_{tag} : {cn}.{nm} = npoly 1259\n"
          f"    ({fmt_list(val)}) := by\n")
        w(f"  rw [{nm}_{cn}]\n")
        w("  simp only [npoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, map_ofNat, map_one,"
          " map_zero]\n")
        w("  ring\n\n")
    w(f"theorem dPoly_npoly_{tag} : dPoly{tag} = npoly 1259\n"
      f"    ({fmt_list(row.dpoly)}) := by\n")
    w(f"  simp only [dPoly{tag}, npoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,"
      " map_ofNat, map_one,\n    map_zero]\n")
    w("  ring\n\n")
    w(f"theorem C37_npoly_{tag} : (C 37 : (ZMod 1259)[X]) = npoly 1259 [37] := by\n")
    w("  simp [npoly, Nat.cast_ofNat]\n\n")

    for n in [5, 6, 7, 8, 9, 10, 11, 12, 17, 18, 19, 20, P]:
        emit_eds_theorem(w, row, n, scratch)

    leafdvd = f"dvd_X_pow_card_pow_sub_X_hPoly{tag}"
    leafcop = f"isCoprime_hPoly{tag}"
    if scratch:
        w(f"axiom {leafdvd} :\n    hPoly{tag} ∣ X ^ (Nat.card (ZMod 1259)) ^ 37 - X\n\n")
        w(f"axiom {leafcop} :\n    IsCoprime hPoly{tag} (X ^ (Nat.card (ZMod 1259)) ^ 1 - X)\n\n")

    w(f"/-- **Row `p = 37`, `{JINV[tag]}`: `Ψ₃₇ mod 1259` has no monic divisor of degree `36`.**\n\n"
      f"This is what `Fermat.not_monic_dvd_preΨ_mod_nonCMModel{tag}` in `X0.lean` consumes. -/\n")
    w(f"theorem not_monic_dvd_preΨ_{tag[0].lower() + tag[1:]}_mod (G : (ZMod 1259)[X])"
      f" (hG : G.Monic)\n    (hdeg : G.natDegree = 36) : ¬ G ∣ {cn}.preΨ' 37 := by\n")
    w("  have hc : (37 : ZMod 1259) ≠ 0 := by decide\n")
    w("  have hmk : ∀ d : ℕ, d ∣ 37 → d ≤ 36 → d ∣ 1 := by\n")
    w("    intro d hd hle\n    interval_cases d <;> revert hd <;> decide\n")
    w(f"  have hDdeg : dPoly{tag}.natDegree = 18 := by rw [dPoly{tag}]; compute_degree!\n")
    w(f"  have hD0 : dPoly{tag} ≠ 0 := fun h => by rw [h, natDegree_zero] at hDdeg; omega\n")
    w(f"  have hDlt : dPoly{tag}.natDegree < 36 := by omega\n")
    w("  -- the `Fact` must come AFTER the `decide`s above; see the `p = 17` row.\n")
    w("  haveI : Fact (Nat.Prime 1259) := ⟨by norm_num⟩\n")
    w(f"  exact not_monic_dvd_of_smallDegreePart' hc preΨ'_thirtySeven_{tag} hmk\n")
    w(f"    {leafdvd} {leafcop} hD0 hDlt G hG hdeg\n\n")


# ------------------------------------------------------------------ scratch emission
SCRATCH_HEAD = """import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finiteness

open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option profiler true
set_option linter.unusedSimpArgs false

namespace Fermat.MazurNonCMCertificate

example : NeZero (1259 : ℕ) := inferInstance

"""


def refl_body_for_scratch():
    body = REFL_BODY
    body = body.replace("@[expose] public section\n\n", "")
    body = body.replace("open Polynomial\n\nset_option maxRecDepth 20000\n"
                        "set_option maxHeartbeats 2000000\n\n"
                        "namespace Fermat.MazurNonCMCertificate\n\n", "")
    body = body.replace("end Fermat.MazurNonCMCertificate\n", "")
    return body


OBSTRUCTION_STUB = """
/-- Scratch stand-in for `MazurNonCMCertificate.not_monic_dvd_of_smallDegreePart'` (the real
one is already proven on main; the scratch only needs the SHAPE of its application). -/
axiom not_monic_dvd_of_smallDegreePart' {K : Type*} [Field K] [Finite K]
    {Ψ D H : K[X]} {c : K} (hc : c ≠ 0) (hfac : Ψ = C c * (D * H))
    {m n k : ℕ} (hmk : ∀ d : ℕ, d ∣ m → d ≤ n → d ∣ k)
    (hHdvd : H ∣ X ^ (Nat.card K) ^ m - X)
    (hHcop : IsCoprime H (X ^ (Nat.card K) ^ k - X))
    (hD0 : D ≠ 0) (hD : D.natDegree < n)
    (G : K[X]) (hG : G.Monic) (hGdeg : G.natDegree = n) : ¬ G ∣ Ψ

"""


def write_scratch(path):
    row = Row("ThirtySevenA")
    out = [SCRATCH_HEAD, refl_body_for_scratch(), OBSTRUCTION_STUB]
    w = out.append
    w(f"noncomputable def hPolyThirtySevenA : (ZMod 1259)[X] :=\n  npoly 1259\n"
      f"    ({fmt_list(row.hpoly)})\n\n")
    w(f"theorem hPolyThirtySevenA_eq : hPolyThirtySevenA = npoly 1259\n"
      f"    ({fmt_list(row.hpoly)}) := rfl\n\n")
    emit_certificate_body(w, row, scratch=True)

    # dress-rehearsal for the parent-module helpers on real data:
    f1, f2 = row.factors[0], row.factors[1]
    w(f"noncomputable def fT1 : (ZMod 1259)[X] := npoly 1259\n    ({fmt_list(f1)})\n\n")
    w(f"theorem fT1_eq : fT1 = npoly 1259\n    ({fmt_list(f1)}) := rfl\n\n")
    w(f"noncomputable def fT2 : (ZMod 1259)[X] := npoly 1259\n    ({fmt_list(f2)})\n\n")
    w(f"theorem fT2_eq : fT2 = npoly 1259\n    ({fmt_list(f2)}) := rfl\n\n")
    u, v = bezout_pair(f1, f2)
    assert ntrim(nadd(nmul(u, f1), nmul(v, f2))) == [1]
    w("theorem copT : IsCoprime fT1 fT2 :=\n")
    w(f"  isCoprime_of_lists\n    ({fmt_list(u)})\n    ({fmt_list(v)})\n"
      f"    fT1_eq fT2_eq (by decide)\n\n")
    # cofrob rehearsal: residue r2 of X^1259 mod f1, and the Bézout against r2 − X
    _, r2 = chain_steps(f1, Q)
    target = psub(r2, [0, 1])
    assert len(r2) == 37
    u2, v2 = bezout_pair(f1, target)
    assert ntrim(nadd(nmul(u2, f1), nadd(nmul(v2, r2), [0] + nneg(v2)))) == [1]
    w(f"axiom chainEndT : fT1 ∣ X ^ (Nat.card (ZMod 1259)) ^ 1 - npoly 1259\n"
      f"    ({fmt_list(r2)})\n\n")
    w("theorem cofrobT : IsCoprime fT1 (X ^ (Nat.card (ZMod 1259)) ^ 1 - X) := by\n")
    w("  obtain ⟨w, hw⟩ := chainEndT\n")
    w("  have key : (X : (ZMod 1259)[X]) ^ (Nat.card (ZMod 1259)) ^ 1 - X =\n")
    w(f"      (npoly 1259\n    ({fmt_list(r2)}) - X) + fT1 * w := by linear_combination hw\n")
    w("  rw [key]\n")
    w("  exact IsCoprime.add_mul_left_right (isCoprime_sub_X_of_lists\n")
    w(f"    ({fmt_list(u2)})\n    ({fmt_list(v2)})\n    fT1_eq (by decide)) w\n\n")
    w("end Fermat.MazurNonCMCertificate\n")
    with open(path, "w") as fh:
        fh.write("".join(out))
    print("wrote", path)




# ------------------------------------------------------------------ production writers
REFL_IMPORTS = """public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ReduceModChar

"""

REFL_DOC = """/-!
# Coefficient-list reflection for the `p = 37` Frobenius certificates, and the two `H`

See the section docstring inside; this module is generated by `gen_thirtyseven.py` and holds
everything the thirty-six `MazurNonCMFrobenius/ThirtySeven{A,B}/Factor{i}.lean` chain modules
share: the list operations, `npoly`, the homomorphism lemmas, the per-shape discharge lemmas,
and the two degree-`666` `hPoly*`.
-/

"""

CERT_IMPORTS = """public import Fermat.FLT.EllipticCurve.MazurNonCMCertificate
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.{tag}

"""

CERT_DOC = """/-!
# Row `p = 37`, `{jinv}`: the mod-`1259` certificate

Generated by `gen_thirtyseven.py`.  The EDS chain `\u03a8\u2082Sq, \u03a8\u2083, pre\u03a8\u2084, pre\u03a8' 5 \u2026 12, 17 \u2026 20`
re-derives `pre\u03a8' 37 mod 1259` from mathlib's recursion and factors it as
`C 37 * (D * H)`; `not_monic_dvd_of_smallDegreePart'` then turns the two computational leaves
proven in `MazurNonCMFrobenius/{tag}.lean` (`H \u2223 X ^ (1259 ^ 37) - X` at `m = 37` PRIME, and
`IsCoprime H (X ^ 1259 - X)` at the single small divisor `d = 1`) into the row's obstruction.

Every polynomial here is carried as `npoly 1259 <coefficient list>`; each recursion step is
one `decide` on a list identity.  See `MazurNonCMReflect.lean` for why this shape.
-/

"""

FACTOR_DOC = """/-!
# Row `p = 37`, `{jinv}`: factor {i} of `H`, and its two chains

Generated by `gen_thirtyseven.py`.  One of the eighteen pairwise-coprime degree-`37` factors
of `H` on this row, with its square-and-multiply chains to `X ^ (1259 ^ 37)` (578 steps, the
divisibility) and to `X ^ 1259` (16 steps, the coprimality residue).  Every step is one
`decide` on a coefficient-list identity \u2014 see `MazurNonCMReflect.lean`; the exponent stays
behind `XPow` throughout \u2014 see `MazurNonCMFrobenius.lean`.
-/

"""

PARENT_DOC = """/-!
# Row `p = 37`, `{jinv}`: `H \u2223 X ^ (1259 ^ 37) - X` and `IsCoprime H (X ^ 1259 - X)`

Generated by `gen_thirtyseven.py`.  Everything that mentions more than one factor of this
row's `H`: the product identity (one `decide` over the eighteen-fold `nmul`), the `153`
B\u00e9zout coprimalities, the `xpow_mul` assembly, and the coprimality leaf at exponent `1259`
(`m = 37` is prime, so `d = 1` is the only divisor of `m` at most `36`, and root-freeness is
the whole of `hHsmall`).
-/

"""

PREAMBLE = """@[expose] public section

open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

-- Generated code: which cast/map lemmas fire varies with the coefficient values of each
-- instance, so the per-instance simp sets are deliberately uniform.
set_option linter.unusedSimpArgs false

namespace Fermat.MazurNonCMCertificate

"""


def _module(path, imports, doc, body):
    with open(path, "w") as fh:
        fh.write(LICENSE + imports + doc + PREAMBLE + body
                 + "end Fermat.MazurNonCMCertificate\n")


def write_reflect(root, rows):
    body = REFL_BODY
    body = body.replace("@[expose] public section\n\nopen Polynomial\n\n"
                        "set_option maxRecDepth 20000\nset_option maxHeartbeats 2000000\n\n"
                        "namespace Fermat.MazurNonCMCertificate\n\n", "")
    body = body.replace("end Fermat.MazurNonCMCertificate\n", "")
    out = [body]
    for row in rows:
        out.append(f"/-- The product of the eighteen irreducible degree-`37` factors of"
                   f" `\u03a8\u2083\u2087 mod 1259` on the\n`{JINV[row.tag]}` row.  Its factorisation is"
                   f" re-proven inside Lean; irreducibility is never used. -/\n")
        out.append(f"noncomputable def hPoly{row.tag} : (ZMod 1259)[X] :=\n  npoly 1259\n"
                   f"    ({fmt_list(row.hpoly)})\n\n")
        out.append(f"theorem hPoly{row.tag}_eq : hPoly{row.tag} = npoly 1259\n"
                   f"    ({fmt_list(row.hpoly)}) := rfl\n\n")
    _module(os.path.join(root, "Fermat/FLT/EllipticCurve/MazurNonCMReflect.lean"),
            REFL_IMPORTS, REFL_DOC, "".join(out))


def emit_factor_module(root, row, i):
    tag = row.tag
    fi = row.factors[i]
    fname = f"f{tag}{i + 1}"
    out = []
    w = out.append
    w(f"/-- Irreducible factor {i + 1} of `H` on this row, of degree 37.  Its irreducibility"
      f" is\nnot used anywhere \u2014 only that the 18 factors are pairwise coprime. -/\n")
    w(f"noncomputable def {fname} : (ZMod 1259)[X] :=\n  npoly 1259\n    ({fmt_list(fi)})\n\n")
    w(f"theorem {fname}_eq : {fname} = npoly 1259\n    ({fmt_list(fi)}) := rfl\n\n")
    base = f"p{tag}{i + 1}b"
    w(f"theorem {base} : XPow {fname} 1 X := xpow_one _\n\n")

    def chain(prefix, steps_list):
        prev = None
        for k, (kind, newexp, quo, rem) in enumerate(steps_list):
            name = f"{prefix}{k}"
            w(f"theorem {name} : XPow {fname} {newexp}\n"
              f"    (npoly 1259\n    ({fmt_list(rem)})) :=\n")
            if k == 0:
                assert kind == "sq" and newexp == 2
                w(f"  sq_step (by norm_num) {base} \u27e80, by rw [npoly_XX_pad]; ring\u27e9\n\n")
            elif kind == "sq":
                w(f"  sq_step (by norm_num) {prev} (dvd_sq_of_lists\n"
                  f"    ({fmt_list(quo)})\n    {fname}_eq (by decide))\n\n")
            else:
                w(f"  mul_step (by norm_num) {prev} {base} (dvd_mulX_of_lists\n"
                  f"    ({fmt_list(quo)})\n    {fname}_eq (by decide))\n\n")
            prev = name
        return prev

    w(f"/-! ### Factor {i + 1}: `X ^ (1259 ^ 37)` mod `f` by square-and-multiply -/\n\n")
    last = chain(f"p{tag}{i + 1}s", row.chains[i])
    w(f"/-- The chain's end, with the padded accumulator rewritten back to `X`. -/\n")
    w(f"theorem xchain_{fname} : XPow {fname} {Q ** P} X := by\n")
    w(f"  have h := {last}\n  rwa [npoly_X_pad] at h\n\n")
    w(f"/-! Factor {i + 1} again, at exponent `1259`, for the coprimality leaf. -/\n\n")
    costeps, coend = row.cochains[i]
    colast = chain(f"p{tag}{i + 1}c", costeps)
    _module(os.path.join(root, f"Fermat/FLT/EllipticCurve/MazurNonCMFrobenius/{tag}",
                         f"Factor{i + 1}.lean"),
            "public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius\n"
            "public import Fermat.FLT.EllipticCurve.MazurNonCMReflect\n\n",
            FACTOR_DOC.format(jinv=JINV[tag], i=i + 1), "".join(out))
    return colast, coend


def left_assoc(names):
    expr = names[0]
    for n in names[1:]:
        expr = f"({expr}).mul_left {n}"
    return expr


def write_parent(root, row, colasts, coends):
    tag = row.tag
    k = len(row.factors)
    out = []
    w = out.append
    names = [f"f{tag}{i + 1}" for i in range(k)]
    w(f"/-- The factorisation of `H` used by every statement below; ONE `decide` over the\n"
      f"eighteen-fold `nmul` (measured \u2248 100 s elaboration + kernel on shadowcat). -/\n")
    w(f"theorem factor_hPoly{tag} : hPoly{tag} = " + " * ".join(names) + " := by\n")
    w("  rw [hPoly" + tag + "_eq, " + ", ".join(n + "_eq" for n in names) + "]\n")
    w("  simp only [\u2190 npoly_nmul]\n")
    w("  exact congrArg (npoly 1259) (by decide)\n\n")

    w("/-! ### Pairwise coprimality, by explicit B\u00e9zout identities -/\n\n")
    for i in range(k):
        for j in range(i + 1, k):
            u, v = bezout_pair(row.factors[i], row.factors[j])
            assert ntrim(nadd(nmul(u, row.factors[i]), nmul(v, row.factors[j]))) == [1]
            w(f"theorem cop{tag}{i + 1}_{j + 1} : IsCoprime f{tag}{i + 1} f{tag}{j + 1} :=\n")
            w(f"  isCoprime_of_lists\n    ({fmt_list(u)})\n    ({fmt_list(v)})\n"
              f"    f{tag}{i + 1}_eq f{tag}{j + 1}_eq (by decide)\n\n")

    w("/-! ### Assembly -/\n\n")
    w(f"theorem dvd_X_pow_card_pow_sub_X_hPoly{tag} :\n")
    w(f"    hPoly{tag} \u2223 X ^ (Nat.card (ZMod 1259)) ^ 37 - X := by\n")
    for i in range(1, k):
        if i == 1:
            w(f"  have h2 := xpow_mul cop{tag}1_2 xchain_f{tag}1 xchain_f{tag}2\n")
        else:
            w(f"  have c{i + 1} : IsCoprime ("
              + " * ".join(f"f{tag}{t + 1}" for t in range(i)) + f") f{tag}{i + 1} :=\n")
            w("    " + left_assoc([f"cop{tag}{t + 1}_{i + 1}" for t in range(i)]) + "\n")
            w(f"  have h{i + 1} := xpow_mul c{i + 1} h{i} xchain_f{tag}{i + 1}\n")
    w(f"  rw [factor_hPoly{tag}]\n")
    w(f"  exact xpow_card (by rw [Nat.card_zmod]; norm_num) h{k}\n\n")

    w("/-! ### The coprimality leaf at exponent `1259` -/\n\n")
    for i in range(k):
        r2 = coends[i]
        target = psub(r2, [0, 1])
        u2, v2 = bezout_pair(row.factors[i], target)
        assert ntrim(nadd(nmul(u2, row.factors[i]),
                          nadd(nmul(v2, r2), [0] + nneg(v2)))) == [1]
        w(f"theorem cofrob{tag}{i + 1} : IsCoprime f{tag}{i + 1}"
          f" (X ^ (Nat.card (ZMod 1259)) ^ 1 - X) := by\n")
        w(f"  have hd : f{tag}{i + 1} \u2223 X ^ (Nat.card (ZMod 1259)) ^ 1 - npoly 1259\n")
        w(f"      ({fmt_list(r2)}) :=\n")
        w(f"    xpow_card (by rw [Nat.card_zmod]; norm_num) {colasts[i]}\n")
        w("  obtain \u27e8w, hw\u27e9 := hd\n")
        w("  have key : (X : (ZMod 1259)[X]) ^ (Nat.card (ZMod 1259)) ^ 1 - X =\n")
        w(f"      (npoly 1259\n      ({fmt_list(r2)}) - X) + f{tag}{i + 1} * w := by\n")
        w("    linear_combination hw\n")
        w("  rw [key]\n")
        w("  exact IsCoprime.add_mul_left_right (isCoprime_sub_X_of_lists\n")
        w(f"    ({fmt_list(u2)})\n    ({fmt_list(v2)})\n    f{tag}{i + 1}_eq (by decide)) w\n\n")
    w(f"theorem isCoprime_hPoly{tag} :\n")
    w(f"    IsCoprime hPoly{tag} (X ^ (Nat.card (ZMod 1259)) ^ 1 - X) := by\n")
    w(f"  rw [factor_hPoly{tag}]\n")
    w("  exact " + left_assoc([f"cofrob{tag}{i + 1}" for i in range(k)]) + "\n\n")

    imports = "".join(
        f"public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.{tag}.Factor{i + 1}\n"
        for i in range(k)) + "\n"
    _module(os.path.join(root, f"Fermat/FLT/EllipticCurve/MazurNonCMFrobenius/{tag}.lean"),
            imports, PARENT_DOC.format(jinv=JINV[tag]), "".join(out))


def write_certificate(root, row):
    out = []
    emit_certificate_body(out.append, row, scratch=False)
    _module(os.path.join(root,
                         f"Fermat/FLT/EllipticCurve/MazurNonCMCertificate/{row.tag}.lean"),
            CERT_IMPORTS.format(tag=row.tag), CERT_DOC.format(jinv=JINV[row.tag], tag=row.tag),
            "".join(out))


def write_production(root):
    rows = [Row("ThirtySevenA"), Row("ThirtySevenB")]
    write_reflect(root, rows)
    n = 1
    for row in rows:
        os.makedirs(os.path.join(root, "Fermat/FLT/EllipticCurve/MazurNonCMFrobenius",
                                 row.tag), exist_ok=True)
        os.makedirs(os.path.join(root, "Fermat/FLT/EllipticCurve/MazurNonCMCertificate"),
                    exist_ok=True)
        colasts, coends = [], []
        for i in range(len(row.factors)):
            cl, ce = emit_factor_module(root, row, i)
            colasts.append(cl)
            coends.append(ce)
            n += 1
        write_parent(root, row, colasts, coends)
        write_certificate(root, row)
        n += 2
    print(f"wrote {n} modules")


if __name__ == "__main__":
    if "--scratch" in sys.argv:
        write_scratch("/home/chend/flt-lean-155/Scratch155C.lean")
    else:
        write_production(sys.argv[1] if len(sys.argv) > 1 else ".")

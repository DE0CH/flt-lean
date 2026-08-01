#!/usr/bin/env python3
"""Generate a Lean certificate for  `H ∣ X ^ (q ^ m) - X`  over `ZMod q`.

*** IN USE (2026-07-31): this generator owns the two `p = 17` rows. ***

Two generators live here and they emit DIFFERENT SHAPES.  Neither is superseded; do not point
one at the other's output.

* `gen_modules.py` (with `gen_all.py`, `gen_frobenius.py`, `gen_coprime.py`) owns the `p = 11`
  rows.  It emits `Fermat/FLT/EllipticCurve/MazurNonCMFrobenius.lean` as SHARED machinery —
  `XPow`, the step lemmas, and the four `H` — plus one module per row under
  `MazurNonCMFrobenius/`, which import that shared module and reuse its `H` definitions.
* THIS script emits a SELF-CONTAINED module: its own `pow_frob`, `chain_step` and
  `isCoprime_of_dvd_sub`, a `namespace F1` … `namespace Fn` chain, and `H` written out as a
  literal rather than imported.  That is why its output is a SIBLING
  (`MazurNonCMFrobeniusSevA.lean`, `…SevB.lean`) and not a module under
  `MazurNonCMFrobenius/`: it does not import the shared machinery, so filing it there would
  claim a relationship it does not have.

  Running it at `--namespace Fermat.MazurNonCMFrobenius --out …/MazurNonCMFrobenius.lean`
  would OVERWRITE the shared machinery and break both `p = 11` row modules.  It emitted that
  file once, in the shape described above, and that output was deleted on 2026-07-31 once the
  generated `ElevenA.lean` / `ElevenB.lean` landed; it cost 530 s there plus 235 s in a
  sibling `MazurNonCMFrobeniusB.lean` deleted with it.

This is the machinery that first closed `dvd_X_pow_card_pow_sub_X_hPolyElevenA`, and then
closed all four `p = 17` leaves (2026-07-31) — `dvd_X_pow_card_pow_sub_X_hPolySeventeenA` /
`…B` and `isCoprime_hPolySeventeenA` / `…B`.  The invocation for those:

    python3 flt-frobenius-cert.py --prime 67 --exponent 34 \
        --namespace Fermat.MazurNonCMFrobeniusSevA --module-doc-target hPolySeventeenA \
        --coprime-exponent 2 \
        --poly-file HA.txt --out Fermat/FLT/EllipticCurve/MazurNonCMFrobeniusSevA.lean

Regenerating a committed output must reproduce it BYTE FOR BYTE; that check has caught two
real bugs and is worth running after any change here.

`--poly-file` holds the modulus' coefficients, HIGHEST degree first, whitespace- or
comma-separated — which is exactly what `lift(Vec(H))` prints in PARI/GP.

WHAT IT EMITS, AND WHY THIS SHAPE.  All three levers below were MEASURED against the
alternative on real data before being chosen; see the same discussion in `CLAUDE.md`.

  * `H` is FACTORED first, via PARI/GP.  A Frobenius table for a degree-`d` modulus costs
    `O(d²)` per entry and needs `d` entries, so it is CUBIC in `d`; splitting one degree-55
    modulus into five degree-11 ones cut the work ~5×.  The factors never have to be proven
    IRREDUCIBLE — they are recombined with explicit Bézout `IsCoprime` certificates and
    `IsCoprime.mul_dvd`, which are cheap by comparison.
  * per factor `h`, a TABLE `u i := (X ^ q) ^ i mod h` for `i ≤ deg h`, so that each
    Frobenius step is the linear combination `p ^ q - p' = ∑ cᵢ * (X ^ (q * i) - u i)`
    instead of a division with a degree-196 quotient.  Measured: **0.8 s versus 46 s**, and
    the 46 s version does not even close — see the next point.  What makes it legal is that
    over `ZMod q` the Frobenius is LINEAR, `f ^ q = f.comp (X ^ q)`, emitted here as
    `pow_frob` from `Polynomial.map_frobenius_expand` and `ZMod.frobenius_zmod`.
  * every `Dvd` witness is stated ALL-POSITIVE as `A = h * c + B` (via
    `sub_eq_iff_eq_add`), because `reduce_mod_char` rewrites `-1` to `q - 1` and then leaves
    an unnormalised `22 * (X ^ 2 * 6)` that `ring_nf` has already run past.  The identity is
    true and the tactic block fails anyway.

Every identity is checked in this file's own `F_q[X]` arithmetic BEFORE it is emitted, and
PARI is used only as an untrusted searcher — its factorisation is multiplied back out and
re-checked here, and then a third time by the Lean kernel.  That is why the first full Lean
build of the 2317-line output had zero errors and zero warnings.

THE NEXT THING THIS TOOL NEEDS.  The two `p = 17` rows (`ZMod 67`, `preΨ' 17`, factor
degrees `2⁴, 34⁴`, `n = 16`, `m = 34`) additionally need each `h_j` to have no irreducible
factor of degree `2`: `d = 2` divides `m = 34` and is `≤ n = 16`, so the `hmn` hypothesis of
`not_monic_dvd_of_smallDegreePart` FAILS there and the degree obstruction does not apply as
stated.  The cheap certificate, given the table this tool already builds, is:  let
`s := X ^ (q ^ 2) mod h_j` (two Frobenius steps, already on hand), and emit an explicit
Bézout for `IsCoprime h_j (s - X)`.  Because `X ^ (q ^ 2) - X ≡ s - X (mod h_j)`, that is
`IsCoprime h_j (X ^ (q ^ 2) - X)`, which is exactly "no irreducible factor of degree 1 or
2".  `not_monic_dvd_of_smallDegreePart` in `MazurNonCMCertificate.lean` then wants its
`hmn`/`hHroot` pair generalised to "for every `d ∣ m` with `d ≤ n` and `d ≠ 1`, `H` has no
irreducible factor of degree `d`".
"""
import argparse
import re
import subprocess
import sys

P = None        # field size, set from --prime


# --------------------------------------------------------------------------- #
#  F_P[x] arithmetic.  Polynomials are lists of ints mod P, LOW degree first,
#  so index == exponent and the empty list is 0.
# --------------------------------------------------------------------------- #

def lo(high_first):
    return trim(list(reversed(high_first)))


def trim(a):
    a = [c % P for c in a]
    while a and a[-1] == 0:
        a.pop()
    return a


def deg(a):
    return len(a) - 1


def add(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def sub(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def mul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % P
    return trim(r)


def divmod_poly(a, b):
    """a = c*b + r with deg r < deg b."""
    a = trim(a[:])
    b = trim(b)
    assert b
    inv = pow(b[-1], P - 2, P)
    c = [0] * max(1, len(a) - len(b) + 1)
    while a and len(a) >= len(b):
        s = deg(a) - deg(b)
        f = a[-1] * inv % P
        c[s] = f
        for i, y in enumerate(b):
            a[i + s] = (a[i + s] - f * y) % P
        a = trim(a)
    return trim(c), a


def powmod(a, e, m):
    r, a = [1], divmod_poly(a, m)[1]
    while e:
        if e & 1:
            r = divmod_poly(mul(r, a), m)[1]
        a = divmod_poly(mul(a, a), m)[1]
        e >>= 1
    return r


def frob(a):
    """a(X) -> a(X^P), which over F_P is exactly a^P."""
    if not a:
        return []
    r = [0] * (P * deg(a) + 1)
    for i, c in enumerate(a):
        r[P * i] = c
    return trim(r)


def bezout(a, b):
    """(s, t) with s*a + t*b = 1."""
    r0, r1, s0, s1, t0, t1 = a[:], b[:], [1], [], [], [1]
    while r1:
        c, r = divmod_poly(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, sub(s0, mul(c, s1))
        t0, t1 = t1, sub(t0, mul(c, t1))
    assert deg(r0) == 0, "not coprime"
    inv = pow(r0[0], P - 2, P)
    s, t = mul([inv], s0), mul([inv], t0)
    assert add(mul(s, a), mul(t, b)) == [1]
    return s, t


X = [0, 1]


# --------------------------------------------------------------------------- #
#  Rendering
# --------------------------------------------------------------------------- #

def L(a):
    """Low-first coefficient list -> a Lean polynomial expression."""
    if not a:
        return "0"
    terms = []
    for i in range(len(a) - 1, -1, -1):
        c = a[i]
        if c == 0:
            continue
        if i == 0:
            terms.append(f"{c}")
        elif i == 1:
            terms.append("X" if c == 1 else f"{c}*X")
        else:
            terms.append(f"X^{i}" if c == 1 else f"{c}*X^{i}")
    return " + ".join(terms)


def wrap(expr, indent="    ", width=98):
    """Break a long `a + b + c` expression across lines after `+`."""
    parts = expr.split(" + ")
    lines, cur = [], parts[0]
    for p in parts[1:]:
        if len(cur) + 3 + len(p) > width:
            lines.append(cur + " +")
            cur = indent + p
        else:
            cur += " + " + p
    lines.append(cur)
    return "\n".join(lines)


def wrap_list(lst, width=90):
    parts = lst.split(", ")
    lines, cur = [], parts[0]
    for p in parts[1:]:
        if len(cur) + 2 + len(p) > width:
            lines.append(cur + ",")
            cur = "      " + p
        else:
            cur += ", " + p
    lines.append(cur)
    return "\n".join(lines)


def fold_dvd_add(items):
    acc = items[0]
    for it in items[1:]:
        acc = f"(dvd_add {acc} {it})"
    return acc


# --------------------------------------------------------------------------- #
#  Per-factor Lean block
# --------------------------------------------------------------------------- #

def factor_block(j, h, m, cop=None):
    d = deg(h)
    t = divmod_poly(frob(X), h)[1]              # u_1 = X^P mod h
    u = [[1], t]
    for i in range(2, d):
        u.append(divmod_poly(mul(u[-1], t), h)[1])
    ps = [X]
    for _ in range(m):
        ps.append(divmod_poly(frob(ps[-1]), h)[1])
    assert ps[1] == t, "p_1 should be the table seed"
    assert ps[m] == X, f"factor {j}: the chain does not return to X"

    o = []
    A = o.append
    A(f"namespace F{j}\n")
    A(f"/-- The `{j}`-th irreducible factor of `H`, of degree `{d}`. -/")
    A(f"noncomputable def h : (ZMod {P})[X] :=\n    {wrap(L(h))}\n")
    for i in range(1, d):
        A(f"/-- `u {i} = (X ^ {P}) ^ {i} mod h`. -/")
        A(f"noncomputable def u{i} : (ZMod {P})[X] :=\n    {wrap(L(u[i]))}\n")
    for k in range(2, m):
        A(f"/-- `p {k} = X ^ ({P} ^ {k}) mod h`. -/")
        A(f"noncomputable def p{k} : (ZMod {P})[X] :=\n    {wrap(L(ps[k]))}\n")

    # seed: X^P = h*c + u1
    c, r = divmod_poly(sub(frob(X), u[1]), h)
    assert r == []
    A(f"/-- `X ^ {P} ≡ u1`, the seed of the table. -/")
    A(f"theorem hX{P} : h ∣ X ^ {P} - u1 :=")
    A(f"  ⟨{wrap(L(c))},\n    by rw [sub_eq_iff_eq_add]; simp only [h, u1]; "
      f"ring_nf; reduce_mod_char⟩\n")

    # table: u1 * u_{i-1} = h*c + u_i
    for i in range(2, d):
        c, r = divmod_poly(sub(mul(u[1], u[i - 1]), u[i]), h)
        assert r == []
        args = ", ".join(dict.fromkeys(["h", "u1", f"u{i-1}", f"u{i}"]))
        A(f"/-- Table step: `u1 * u{i-1} ≡ u{i}`. -/")
        A(f"theorem tu{i} : h ∣ u1 * u{i-1} - u{i} :=")
        A(f"  ⟨{wrap(L(c))},\n    by rw [sub_eq_iff_eq_add]; simp only [{args}]; "
          f"ring_nf; reduce_mod_char⟩\n")

    # pu i : h | u1^i - u_i
    A("/-- `u1 ^ 1 ≡ u1`, trivially. -/")
    A("theorem pu1 : h ∣ u1 ^ 1 - u1 := by simp\n")
    for i in range(2, d):
        A(f"/-- `u1 ^ {i} ≡ u{i}`, from the table. -/")
        A(f"theorem pu{i} : h ∣ u1 ^ {i} - u{i} := by")
        A(f"  have e : u1 ^ {i} - u{i} = u1 * (u1 ^ {i-1} - u{i-1}) + (u1 * u{i-1} - u{i}) := by")
        A(f"    ring")
        A(f"  rw [e]")
        A(f"  exact dvd_add (Dvd.dvd.mul_left pu{i-1} _) tu{i}\n")

    # hx i : h | X^(P*i) - u_i
    for i in range(1, d):
        A(f"/-- `X ^ ({P} * {i}) ≡ u{i}`. -/")
        A(f"theorem hx{i} : h ∣ X ^ ({P} * {i}) - u{i} := by")
        A(f"  have e : (X : (ZMod {P})[X]) ^ ({P} * {i}) - u{i}")
        A(f"      = ((X ^ {P}) ^ {i} - u1 ^ {i}) + (u1 ^ {i} - u{i}) := by ring")
        A(f"  rw [e]")
        A(f"  exact dvd_add (hX{P}.trans (sub_dvd_pow_sub_pow _ _ {i})) pu{i}\n")

    def name(k):
        return "X" if k in (0, m) else ("u1" if k == 1 else f"p{k}")

    # Frobenius steps.  Step 0 IS the seed, so it is not re-emitted.
    for k in range(1, m):
        c = ps[k]
        idx = [i for i in range(1, min(len(c), d)) if c[i]]
        assert idx, f"empty decomposition at k={k}"
        assert sub(frob(ps[k]), ps[k + 1]) == \
            _combo(c, u, idx), f"decomposition wrong at k={k}"
        rhs = " + ".join(f"{c[i]} * (X ^ ({P} * {i}) - u{i})" for i in idx)
        unf = ([f"p{k}"] if 2 <= k < m else []) + \
              ([f"p{k+1}"] if 2 <= k + 1 < m else []) + \
              (["u1"] if k == 1 else []) + [f"u{i}" for i in idx]
        # exactly the `comp` lemmas this p_k needs -- the unusedSimpArgs linter
        # fires once per step otherwise
        comps = ["add_comp"]
        if any(cc >= 2 for cc in c[1:]):
            comps.append("mul_comp")
        if len(c) > 2:
            comps.append("pow_comp")
        if len(c) > 1:
            comps.append("X_comp")
        if c and c[0] == 1:
            comps.append("one_comp")
        if (c and c[0] >= 2) or any(cc >= 2 for cc in c[1:]):
            comps.append("ofNat_comp")
        A(f"/-- Frobenius step `{k} → {k+1}`: `p{k} ^ {P} ≡ p{k+1}`. -/")
        A(f"theorem fs{k} : h ∣ {name(k)} ^ {P} - {name(k+1)} := by")
        A(f"  have e : ({name(k)} : (ZMod {P})[X]) ^ {P} - {name(k+1)} =\n"
          f"      {wrap(rhs, indent=' ' * 6)} := by")
        A(f"    rw [pow_frob]")
        A(f"    simp only [{wrap_list(', '.join(dict.fromkeys(unf) | dict.fromkeys(comps)))}]")
        A(f"    ring_nf")
        A(f"    all_goals reduce_mod_char")
        A(f"  rw [e]")
        A("  exact " + wrap(fold_dvd_add([f"(Dvd.dvd.mul_left hx{i} _)" for i in idx]),
                            indent=" " * 4) + "\n")

    A(f"/-- **`h ∣ X ^ ({P} ^ {m}) - X`** for this factor. -/")
    A(f"theorem dvd_pow : h ∣ X ^ ({P} : ℕ) ^ {m} - X := by")
    A(f"  have c0 : h ∣ X ^ ({P} : ℕ) ^ 0 - X := by simp")
    for k in range(0, m):
        A(f"  have c{k+1} : h ∣ X ^ ({P} : ℕ) ^ {k+1} - {name(k+1)} := chain_step c{k} "
          f"{f'hX{P}' if k == 0 else f'fs{k}'}")
    A(f"  exact c{m}\n")

    # The degree-`cop` coprimality, for rows where `hmn` fails at some d > 1.  `X ^ (P ^ cop)`
    # is ALREADY reduced in the chain above (it is `p{cop}`), so this costs one small Bézout
    # on `p{cop} - X` — degree `< d` — rather than one on `X ^ (P ^ cop) - X`, whose Bézout
    # cofactor would have degree `P ^ cop`.
    if cop is not None:
        assert 2 <= cop < m, f"--coprime-exponent {cop} needs 2 <= cop < m"
        r = sub(ps[cop], X)
        assert r, f"factor {j} DIVIDES X ^ ({P} ^ {cop}) - X: THE COPRIMALITY IS FALSE"
        s, t = bezout(h, r)
        chain = "(by simp)" if cop == 0 else "(chain_step (by simp) hX%d)" % P
        for k in range(1, cop):
            chain = f"(chain_step {chain} fs{k})"
        A(f"/-- `X ^ ({P} ^ {cop}) ≡ p{cop}`, the rung the coprimality below reduces through. -/")
        A(f"theorem dvd_cop : h ∣ X ^ ({P} : ℕ) ^ {cop} - p{cop} :=\n  {chain}\n")
        A(f"/-- `h` is coprime to the REDUCTION `p{cop} - X`, by an explicit Bézout "
          f"certificate.\nBoth cofactors have degree `< {d}`; the unreduced statement would "
          f"need one of degree `{P ** cop}`. -/")
        A(f"theorem cop_red : IsCoprime h (p{cop} - X) :=")
        A(f"  ⟨{wrap(L(s))},\n    {wrap(L(t))},\n"
          f"    by simp only [h, p{cop}]; ring_nf; reduce_mod_char⟩\n")
        A(f"/-- **`h` has no irreducible factor of degree dividing `{cop}`**, i.e. it is "
          f"coprime to\n`X ^ ({P} ^ {cop}) - X`. -/")
        A(f"theorem cop_pow : IsCoprime h (X ^ ({P} : ℕ) ^ {cop} - X) :=")
        A(f"  isCoprime_of_dvd_sub cop_red (by")
        A(f"    have e : (X : (ZMod {P})[X]) ^ ({P} : ℕ) ^ {cop} - X - (p{cop} - X)")
        A(f"        = X ^ ({P} : ℕ) ^ {cop} - p{cop} := by ring")
        A(f"    rw [e]; exact dvd_cop)\n")

    A(f"end F{j}\n")
    return "\n".join(o)


def _combo(c, u, idx):
    """∑ c_i * (X^(P*i) - u_i), for the assertion above."""
    acc = []
    for i in idx:
        mono = [0] * (P * i + 1)
        mono[P * i] = 1
        acc = add(acc, mul([c[i]], sub(mono, u[i])))
    return acc


# --------------------------------------------------------------------------- #
#  Whole module
# --------------------------------------------------------------------------- #

def _degphrase(degs):
    return (f"of degree exactly `{degs[0]}`" if len(set(degs)) == 1
            else "of degrees " + ", ".join(f"`{d}`" for d in degs))


def preamble(m, ns, target, degs):
    return f'''/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.FieldTheory.Finite.Basic

/-!
# `{target} ∣ X ^ ({P} ^ {m}) - X` over `ZMod {P}`

GENERATED by `flt-frobenius-cert.py`; regenerate rather than hand-edit.

This module discharges the computational leaf of
`Fermat/FLT/EllipticCurve/MazurNonCMCertificate.lean`: the degree-`{sum(degs)}` polynomial
`H` appearing in the factorisation `Ψ mod {P} = c · D · H` divides `X ^ ({P} ^ {m}) - X`,
i.e. every irreducible factor of `H` has degree dividing `{m}`.

`H` is in fact the product of {len(degs)} irreducible polynomials {_degphrase(degs)}
(PARI/GP 2.15.4, whose factorisation is multiplied back out and re-checked in the generator
before anything is emitted here).  That is how the proof is organised: the divisibility is
proven for each factor separately, and the factors are recombined through explicit Bézout
coprimality certificates — they never have to be proven irreducible.

## Why it is arranged this way

Everything here is a `ring` identity over `ZMod {P}`, so the only thing that matters is how
large those identities are. Two shapes were MEASURED against each other in this tree:

* **direct** — for each Frobenius step, `p ^ {P} - p' = h * c` with `c` of degree `196`.
  One such identity takes **46 s** and `ring_nf; reduce_mod_char` does not even close it:
  `reduce_mod_char` rewrites `-1` to `{P - 1}` and leaves an unnormalised
  `{P - 1} * (X ^ 2 * 6)` behind, which `ring_nf` has already run past.
* **table** — precompute `u i = (X ^ {P}) ^ i mod h`, and decompose each Frobenius step as
  `p ^ {P} - p' = ∑ c i * (X ^ ({P} * i) - u i)`. Every identity then has degree `≤ 21`, and
  one takes **0.8 s**.

The table shape is used throughout, and it is the whole reason this file elaborates in
minutes rather than hours: over `ZMod {P}` the Frobenius `r ↦ r ^ {P}` is LINEAR
(`pow_frob` below, from `Polynomial.map_frobenius_expand` and `ZMod.frobenius_zmod`), so a
Frobenius step is a `ZMod {P}`-linear combination of the precomputed table rather than a
long division. Relatedly, every `Dvd` witness below is stated in the ALL-POSITIVE form
`A = h * c + B`, so that no negative coefficient ever reaches `reduce_mod_char`.

The module is separate from `MazurNonCMCertificate.lean` because elaboration is
single-threaded per file; nothing here mentions an elliptic curve.
-/

@[expose] public section

open Polynomial

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace {ns}

/-- Over `ZMod {P}` the Frobenius is the substitution `X ↦ X ^ {P}`: raising to the `{P}`rd
power is LINEAR. This is `Polynomial.map_frobenius_expand` specialised through
`ZMod.frobenius_zmod`, which kills the coefficient-wise `c ↦ c ^ {P}`. -/
theorem pow_frob (f : (ZMod {P})[X]) : f ^ {P} = f.comp (X ^ {P}) := by
  haveI : Fact (Nat.Prime {P}) := ⟨by decide⟩
  rw [← Polynomial.map_frobenius_expand (R := ZMod {P}) (p := {P}), ZMod.frobenius_zmod,
    Polynomial.map_id]
  rfl

/-- One rung of the Frobenius ladder: if `X ^ ({P} ^ k) ≡ a` and `a ^ {P} ≡ b` mod `h`, then
`X ^ ({P} ^ (k + 1)) ≡ b`. The first divisibility is raised by `sub_dvd_pow_sub_pow`. -/
theorem chain_step {{h a b : (ZMod {P})[X]}} {{k : ℕ}}
    (h1 : h ∣ X ^ ({P} : ℕ) ^ k - a) (h2 : h ∣ a ^ {P} - b) :
    h ∣ X ^ ({P} : ℕ) ^ (k + 1) - b := by
  have e : (X : (ZMod {P})[X]) ^ ({P} : ℕ) ^ (k + 1) - b
      = ((X ^ ({P} : ℕ) ^ k) ^ {P} - a ^ {P}) + (a ^ {P} - b) := by
    rw [← pow_mul, ← pow_succ]
    ring
  rw [e]
  exact dvd_add (h1.trans (sub_dvd_pow_sub_pow _ _ {P})) h2

/-- Coprimality transports along a congruence: `IsCoprime a b` and `a ∣ c - b` give
`IsCoprime a c`. This is what lets a coprimality against `X ^ ({P} ^ k) - X` be certified by a
Bézout pair against its REDUCTION mod `a`, whose degree is `< deg a` instead of `{P} ^ k`. -/
theorem isCoprime_of_dvd_sub {{R : Type*}} [CommRing R] {{a b c : R}}
    (hab : IsCoprime a b) (hc : a ∣ c - b) : IsCoprime a c := by
  obtain ⟨u, v, huv⟩ := hab
  obtain ⟨k, hk⟩ := hc
  exact ⟨u - v * k, v, by linear_combination huv + v * hk⟩

'''


def product_block(factors, H, target):
    """`H = h_1 ⋯ h_n`, multiplied in ONE FACTOR AT A TIME.

    MEASURED 2026-07-31, and the reason this is not the obvious one-shot
    `simp only [F1.h, …]; ring_nf; reduce_mod_char`.  At `deg H = 136`, `n = 4` that shape
    DOES NOT CLOSE: `ring_nf` gets through (it is not the bottleneck) and `reduce_mod_char`
    then dies with `(deterministic) timeout at isDefEq` after **269 s** at `maxHeartbeats
    1000000`.  Fully expanding a 4-fold product first pushes the intermediate coefficients up
    to `≈ 10 ^ 12` — 35 terms cubed, times `66 ^ 4` — and it is reducing 137 numerals of that
    size, not the polynomial algebra, that runs out.

    Staged, every intermediate is already reduced mod `P`, so no numeral ever exceeds
    `deg · (P-1)²  ≈ 4 · 10 ^ 5`, and each identity is a product of just TWO explicit
    polynomials.  Same three tactics, same final statement: **224 s and EXIT=0**.

    It also emits the identity ONCE.  The previous shape inlined it as a `have` in both
    `dvd_X_pow_sub_X_hPoly` and `isCoprime_hPoly`, paying for it twice.
    """
    n = len(factors)
    o = []
    A = o.append
    if n == 1:
        A(f"/-- `H` is the single factor `F1.h`. -/")
        A(f"theorem factor_hPoly : ({wrap(L(H), indent=' ' * 6)} : (ZMod {P})[X])\n"
          f"    = F1.h := by rw [F1.h]\n")
        return "\n".join(o)

    acc = factors[0]
    partial = []
    for j in range(1, n):
        acc = mul(acc, factors[j])
        partial.append(acc[:])
    assert partial[-1] == H, "the staged product does not reproduce H"

    for k, g in enumerate(partial, 2):
        A(f"/-- `g{k} = h_1 ⋯ h_{k}`, of degree `{deg(g)}`.  The partial products are named so "
          f"that no\nsingle `ring_nf` ever sees more than two explicit polynomials at a "
          f"time. -/")
        A(f"noncomputable def g{k} : (ZMod {P})[X] :=\n    {wrap(L(g))}\n")
    for k in range(2, n + 1):
        lhs = "F1.h * F2.h" if k == 2 else f"g{k-1} * F{k}.h"
        args = ", ".join(["F1.h", "F2.h"] if k == 2 else [f"g{k-1}", f"F{k}.h"])
        A(f"/-- `h_1 ⋯ h_{k} = g{k}`. -/")
        A(f"theorem hg{k} : {lhs} = g{k} := by")
        A(f"  simp only [{args}, g{k}]")
        A(f"  ring_nf")
        A(f"  reduce_mod_char\n")
    prod = " * ".join(f"F{i}.h" for i in range(1, n + 1))
    A(f"/-- **`{target} = h_1 ⋯ h_{n}`**, the factorisation both certificates below run on. -/")
    A(f"theorem factor_hPoly : ({wrap(L(H), indent=' ' * 6)} : (ZMod {P})[X])\n"
      f"    = {prod} := by")
    A("  rw [" + ", ".join([f"hg{k}" for k in range(2, n + 1)] + [f"g{n}"]) + "]\n")
    return "\n".join(o)


def emit(factors, H, m, ns, target, path, cop=None):
    n = len(factors)
    out = [preamble(m, ns, target, [deg(f) for f in factors])]
    for j, h in enumerate(factors, 1):
        out.append(factor_block(j, h, m, cop))

    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            s, t = bezout(factors[i - 1], factors[j - 1])
            out.append(
                f"/-- `h{i}` and `h{j}` are coprime, by an explicit Bézout certificate. -/\n"
                f"theorem cop{i}{j} : IsCoprime F{i}.h F{j}.h :=\n"
                f"  ⟨{wrap(L(s))},\n    {wrap(L(t))},\n"
                f"    by simp only [F{i}.h, F{j}.h]; ring_nf; reduce_mod_char⟩\n")

    out.append(product_block(factors, H, target))

    body = [f"/-- **THE CERTIFICATE**: `H ∣ X ^ ({P} ^ {m}) - X`.\n",
            f"`H` is the degree-`{deg(H)}` polynomial `{target}` of",
            "`Fermat/FLT/EllipticCurve/MazurNonCMCertificate.lean`, written out here so that "
            "this module\ndoes not have to import that one. -/",
            f"theorem dvd_X_pow_sub_X_hPoly :",
            f"    ({wrap(L(H), indent=' ' * 6)} : (ZMod {P})[X]) ∣ X ^ ({P} : ℕ) ^ {m} - X := by",
            "  rw [factor_hPoly]"]
    # Fold the factors in one at a time.  `IsCoprime (h1 * … * h_{j-1}) h_j` is built from
    # the pairwise certificates by `IsCoprime.mul_left`, and then `IsCoprime.mul_dvd` adds
    # `h_j` to the accumulated product.
    for j in range(2, n + 1):
        # NOT named `cop` -- that is this function's coprime-exponent parameter, and shadowing
        # it here silently turned every run into a --coprime-exponent run.  Caught by the
        # round-trip regression test, which is the whole reason that test exists.
        pw = f"cop1{j}" if j == 2 else \
            "(" * (j - 2) + f"cop1{j}" + "".join(f".mul_left cop{i}{j})" for i in range(2, j))
        src = "F1.dvd_pow F2.dvd_pow" if j == 2 else f"d{j-1} F{j}.dvd_pow"
        if j == n:
            body.append(f"  exact {pw}.mul_dvd {src}")
        else:
            acc = " * ".join(f"F{i}.h" for i in range(1, j + 1))
            body.append(f"  have d{j} : {acc} ∣ X ^ ({P} : ℕ) ^ {m} - X :=")
            body.append(f"    {pw}.mul_dvd {src}")
    out.append("\n".join(body) + "\n")

    if cop is not None:
        acc = "F1.cop_pow"
        for j in range(2, n + 1):
            acc = f"({acc}.mul_left F{j}.cop_pow)" if j < n else f"{acc}.mul_left F{j}.cop_pow"
        out.append("\n".join([
            f"/-- **NO SMALL FACTOR**: `H` is coprime to `X ^ ({P} ^ {cop}) - X`, i.e. it has no\n"
            f"irreducible factor whose degree divides `{cop}`.  Needed wherever `{cop} ∣ m` and "
            f"`{cop} ≤ n`, so\nthat the degree obstruction's `1`-is-the-only-small-divisor "
            "hypothesis fails. -/",
            f"theorem isCoprime_hPoly :",
            f"    IsCoprime ({wrap(L(H), indent=' ' * 6)} : (ZMod {P})[X])",
            f"      (X ^ ({P} : ℕ) ^ {cop} - X) := by",
            "  rw [factor_hPoly]",
            f"  exact {acc}\n"]))

    out.append(f"end {ns}\n\nend\n")
    open(path, 'w').write("\n".join(out))


# --------------------------------------------------------------------------- #

def factor_over_fq(high_first):
    """Factor over F_P with PARI/GP -- an UNTRUSTED SEARCHER, re-checked by the caller."""
    terms = " + ".join(f"{c}*x^{len(high_first) - 1 - i}"
                       for i, c in enumerate(high_first) if c % P)
    script = (f"default(parisize, 4000000000);\n"
              f"f = Mod(1,{P})*({terms});\n"
              f"fa = factor(f);\n"
              f"for(i=1, matsize(fa)[1], print(fa[i,2], \" \", lift(Vec(fa[i,1]))));\n"
              f"quit;\n")
    r = subprocess.run(["gp", "-q"], input=script, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"gp failed:\n{r.stderr}")
    factors = []
    for line in r.stdout.splitlines():
        line = line.strip()
        if not line or not line[0].isdigit():
            continue
        mult, vec = line.split(" ", 1)
        if int(mult) != 1:
            sys.exit(f"modulus is NOT squarefree: a factor has multiplicity {mult}")
        factors.append(lo([int(t) for t in re.findall(r"-?\d+", vec)]))
    return factors


def main():
    global P
    ap = argparse.ArgumentParser()
    ap.add_argument("--prime", type=int, required=True, help="q, the field size")
    ap.add_argument("--exponent", type=int, required=True, help="m, as in X ^ (q ^ m) - X")
    ap.add_argument("--namespace", required=True)
    ap.add_argument("--module-doc-target", default="hPoly",
                    help="the name this H has in MazurNonCMCertificate.lean")
    ap.add_argument("--poly-file", required=True, help="coefficients, HIGHEST degree first")
    ap.add_argument("--out", required=True)
    ap.add_argument("--coprime-exponent", type=int, default=None,
                    help="k: ALSO certify `IsCoprime H (X ^ (q ^ k) - X)`, i.e. that H has no "
                         "irreducible factor of degree dividing k.  Needed when some d > 1 "
                         "divides m and is <= n, where the degree obstruction's `hmn` fails. "
                         "Requires 2 <= k < m.")
    a = ap.parse_args()
    P = a.prime

    high_first = [int(t) for t in re.findall(r"-?\d+", open(a.poly_file).read())]
    H = lo(high_first)
    factors = factor_over_fq(high_first)

    prod = [1]
    for f in factors:
        prod = mul(prod, f)
    if prod != H:
        sys.exit("PARI's factorisation does not multiply back to H")
    if len(set(map(tuple, factors))) != len(factors):
        sys.exit("repeated factor: the modulus is not squarefree")
    for j, f in enumerate(factors, 1):
        if powmod(X, P ** a.exponent, f) != X:
            sys.exit(f"factor {j} does NOT divide X ^ ({P} ^ {a.exponent}) - X: "
                     f"THE STATEMENT IS FALSE AS GIVEN")

    k = a.coprime_exponent
    if k is not None:
        for j, f in enumerate(factors, 1):
            if powmod(X, P ** k, f) == X:
                sys.exit(f"factor {j} DIVIDES X ^ ({P} ^ {k}) - X: "
                         f"THE COPRIMALITY IS FALSE AS GIVEN")

    emit(factors, H, a.exponent, a.namespace, a.module_doc_target, a.out, k)
    print(f"wrote {a.out}: {len(factors)} factors of degrees {[deg(f) for f in factors]}"
          + (f", plus the degree-{k} coprimality" if k is not None else ""),
          file=sys.stderr)


if __name__ == "__main__":
    main()

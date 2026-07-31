#!/usr/bin/env python3
"""Bézout certificates over `F_q[X]`.

Pairwise coprimality of `H`'s factors is what lets `IsCoprime.mul_dvd` reassemble the product,
and a Bézout pair is a one-line Lean proof (`⟨u, v, by ring_nf⟩`).  Nothing here needs the
factors to be irreducible.
"""
from gen_frobenius import poly_add, poly_divmod, poly_mul, poly_smul, poly_sub, poly_trim


def monic_scale(a, q):
    """`a` divided by its leading coefficient."""
    inv = pow(a[-1], q - 2, q)
    return poly_trim([(x * inv) % q for x in a])


def xgcd(a, b, q):
    """`(g, u, v)` with `u a + v b = g` and `g` monic."""
    r0, r1 = a[:], b[:]
    s0, s1 = [1], []
    t0, t1 = [], [1]
    while r1:
        inv = pow(r1[-1], q - 2, q)
        quo, rem = poly_divmod(r0, monic_scale(r1, q), q)
        quo = poly_smul(inv, quo, q)
        r0, r1 = r1, rem
        s0, s1 = s1, poly_sub(s0, poly_mul(quo, s1, q), q)
        t0, t1 = t1, poly_sub(t0, poly_mul(quo, t1, q), q)
    inv = pow(r0[-1], q - 2, q)
    return poly_smul(inv, r0, q), poly_smul(inv, s0, q), poly_smul(inv, t0, q)


def bezout_pair(f, g, q):
    """`(u, v)` with `u f + v g = 1`; raises if `f` and `g` are not coprime."""
    d, u, v = xgcd(f, g, q)
    assert d == [1], f"not coprime: gcd has degree {len(d) - 1}"
    assert poly_add(poly_mul(u, f, q), poly_mul(v, g, q), q) == [1]
    return u, v

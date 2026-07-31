#!/usr/bin/env python3
"""Square-and-multiply certificate for `H ∣ X ^ (q ^ m) - X`, factor by factor.

MEASURED, and this is the whole reason the shape changed (2026-07-31).  The obvious route
— Frobenius linearity, `r ^ q = expand q r`, one table `T_i = X ^ (q i) mod f` — produces a
`ring_nf` goal of DEGREE `q · (deg f − 1)`: 230 already at `q = 23`, `deg f = 11`.  On those,
`ring_nf` recurses past `maxRecDepth 1000000` and blows an 8 MB — and a 256 MB — thread stack.
The `tab_step` identities in the SAME file, degree `≤ 33`, all go through in seconds.  So the
cost driver is the degree of the identity handed to `ring`, and the fix is to never form a
high-degree one.

Square-and-multiply does that: every identity is `a * b = f * Q + c` with `deg a, deg b <
deg f`, hence degree `< 2 deg f`, whatever the exponent.  The exponent `q ^ m` appears only in
STATEMENTS, where `sq_step`/`mul_step` handle it abstractly and `ring` never sees it.
"""
from gen_frobenius import fmt_poly, poly_divmod, poly_mul, poly_trim


def bin_chain(n):
    """Square-and-multiply plan for `X ^ n`: a list of ('sq', j) / ('mul', j) on the accumulator."""
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


def emit_factor(w, fname, tag, q, n, f, base=None):
    """Emit a chain ending in `f ∣ X ^ n - r`; returns `(step name, r)`.

    `base` names an already-emitted `f ∣ X ^ 1 - X` to start from (a factor needs two
    chains when the row also has a coprimality leaf, and they share their base).
    """
    a = [0, 1]                                    # accumulator: X ^ 1 mod f
    if base is None:
        base = f"p{tag}1"
        w(f"theorem {base} : XPow {fname} 1 X := xpow_one _\n\n")
    prev, exps = base, 1
    for step, (kind, newexp) in enumerate(bin_chain(n)):
        if kind == "sq":
            prod = poly_mul(a, a, q)
        else:
            prod = poly_mul(a, [0, 1], q)
        quo, rem = poly_divmod(prod, f, q)
        name = f"p{tag}s{step}"
        w(f"theorem {name} : XPow {fname} {newexp}\n")
        w("    (" + fmt_poly(rem, "      ") + ") :=\n")
        if kind == "sq":
            w(f"  sq_step (by norm_num) {prev} ⟨\n")
        else:
            w(f"  mul_step (by norm_num) {prev} {base} ⟨\n")
        w("    " + fmt_poly(quo, "      ") + ",\n")
        # NOT `by ring` when the cofactor is 0: the identity still needs the coefficients
        # reduced mod q, and `ring` reports the residue (`483 = 0`) as an unsolved goal.
        # But `reduce_mod_char` alone CLOSES that case, so appending `ring_nf` there is dead
        # code and the `unreachableTactic` linter says so.
        # `all_goals`, not a bare sequence: `reduce_mod_char` CLOSES some of the zero-cofactor
        # identities outright, and `ring_nf` on no goals is an error.  It closes only SOME of
        # them, so the branch cannot be decided from `quo == 0` — that was tried, and the
        # cases where `reduce_mod_char` leaves work behind fail with `unsolved goals`.
        w(f"    by simp only [{fname}]; reduce_mod_char; all_goals ring_nf;"
          " all_goals reduce_mod_char⟩\n\n")
        a, prev, exps = rem, name, newexp
    assert exps == n
    return prev, a

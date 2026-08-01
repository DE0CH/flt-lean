#!/usr/bin/env python3
"""Generate the FACTORED Frobenius certificate for `H ∣ X ^ (q ^ m) - X`.

Why factored.  Running the table `T_i = X ^ (q i) mod H` against `H` itself makes every
`ring_nf` call proportional to `(deg H) ^ 2` — at `deg H = 55` that already overflows Lean's
thread stack, and at `deg H = 136` it is `20×` worse again.  But `H` is a product of `k`
pairwise-coprime factors of degree `d = deg H / k`, and

    f ∣ P  for every factor  +  pairwise coprimality  ⟹  H = ∏ f ∣ P

by `IsCoprime.mul_dvd`.  Each factor's table is `(deg f) ^ 2`, i.e. `k ^ 2` times cheaper, and
the whole certificate becomes `k` small chains plus `k (k−1) / 2` Bézout identities and one
product identity.  NOTHING here needs the factors to be irreducible — only coprime — so no
irreducibility test is required anywhere.

The same tables give `IsCoprime H (X ^ (q ^ j) - X)` for free: `X ^ (q ^ j) - X` is congruent
to `r_j - X` modulo each factor, and `r_j` is already on the chain.
"""
import io

from gen_binpow import emit_factor
from gen_frobenius import (fmt_poly, parse_poly, poly_add, poly_divmod, poly_mul,
                           poly_smul, poly_sub, poly_trim, wrap_expr)
from gen_coprime import bezout_pair


def chain(f, q, m):
    """Table + Frobenius chain modulo the monic polynomial `f`."""
    d = len(f) - 1
    Xq = [0] * q + [1]
    T, Q = [[1]], [None]
    for i in range(1, d):
        quo, rem = poly_divmod(poly_mul(Xq, T[i - 1], q), f, q)
        T.append(rem)
        Q.append(quo)
    R = [[0, 1]]
    for k in range(m):
        acc = []
        for i, c in enumerate(R[k]):
            if c:
                acc = poly_add(acc, poly_smul(c, T[i], q), q)
        R.append(acc)
    return T, Q, R


def expand_simp_set(r, idx):
    """Exactly the `map_*` lemmas `expand` needs on the literal `Σ_{i ∈ idx} r_i X ^ i`.

    Passing the full set unconditionally is what the `unusedSimpArgs` linter complains
    about: at `r = X` only `expand_X` fires.
    """
    s = []
    if len(idx) >= 2:
        s.append("map_add")
    if any(r[i] != 1 and i != 0 for i in idx):
        s.append("map_mul")
    if any(i >= 2 for i in idx):
        s.append("map_pow")
    if any(r[i] >= 2 for i in idx):
        s.append("map_ofNat")
    if 0 in idx and r[0] == 1:
        s.append("map_one")
    s.append("expand_X")
    return s


def nested_dvd_add(names):
    """`f ∣ Σ cᵢ * dᵢ` from the individual `f ∣ dᵢ`, right-nested."""
    # the `key` right-hand side is a `+`-chain, which Lean parses LEFT-associated, so the
    # `dvd_add` nest has to be left-associated too or the application does not typecheck.
    expr = f"({names[0]}.mul_left _)"
    for n in names[1:]:
        expr = f"(dvd_add {expr} ({n}.mul_left _))"
    return expr


def emit_chain(w, fname, tag, q, m, T, Q, R):
    d = len(T)
    w(f"theorem t{tag}0 : {fname} ∣ X ^ 0 - 1 := by simp\n\n")
    for i in range(1, d):
        w(f"theorem t{tag}{i} : {fname} ∣ X ^ {q * i} -\n")
        w("    (" + fmt_poly(T[i], "      ") + ") :=\n")
        w(f"  tab_step (by norm_num) t{tag}{i - 1} ⟨\n")
        w("    " + fmt_poly(Q[i], "      ") + ",\n")
        if Q[i]:
            w(f"    by simp only [{fname}]; reduce_mod_char; ring_nf; reduce_mod_char⟩\n\n")
        else:
            w("    by ring⟩\n\n")
    w(f"theorem r{tag}0 : {fname} ∣ X ^ {q} ^ 0 - X := by norm_num\n\n")
    for k in range(m):
        idx = [i for i, c in enumerate(R[k]) if c]
        w(f"theorem r{tag}{k + 1} : {fname} ∣ X ^ {q} ^ {k + 1} -\n")
        w("    (" + fmt_poly(R[k + 1], "      ") + ") :=\n")
        w(f"  frob_step r{tag}{k} (by\n")
        # `expand` of `r_k` is the SAME `ZMod q`-combination of the table's defining
        # differences.  Stating that as a `have` keeps the ring problem free of the
        # table cofactors: `linear_combination` over the `t`s carries them as eleven
        # extra atoms and sends `ring1` past `maxRecDepth 1000000`.
        w(f"    have key : expand (ZMod {q}) {q}\n")
        w("        (" + fmt_poly(R[k], "          ") + ") -\n")
        w("        (" + fmt_poly(R[k + 1], "          ") + ") =\n")
        terms = " + ".join(f"{R[k][i]} * (X ^ {q * i} - ({fmt_poly(T[i], '')}))" for i in idx)
        w("      " + wrap_expr(terms, "        ", 6) + " := by\n")
        w("      simp only [" + ", ".join(expand_simp_set(R[k], idx)) + "]\n")
        # `ring_nf` already closes the sparse early steps; `all_goals` is a no-op then.
        w("      ring_nf\n      all_goals reduce_mod_char\n")
        w("    rw [key]\n")
        proof = nested_dvd_add([f"t{tag}{i}" for i in idx])
        w("    exact\n")
        line = "     "
        for tok in proof.split(" "):
            if len(line) + 1 + len(tok) > 100:
                w(line + "\n")
                line = "     "
            line += " " + tok
        w(line + ")\n\n")


def _prepare(hsrc, factors_src, q):
    H = parse_poly(hsrc, q)
    F = [parse_poly(s, q) for s in factors_src]
    prod = [1]
    for f in F:
        prod = poly_mul(prod, f, q)
    assert prod == H, "the factorisation does not multiply back to H"
    return F


def _emit_def(w, tag, i, f, q, k):
    """The `noncomputable def` for one factor."""
    w(f"/-- Irreducible factor {i + 1} of `H` on this row, of degree {len(f) - 1}.  Its"
      f" irreducibility is\nnot used anywhere — only that the {k} factors are pairwise"
      " coprime. -/\n")
    w(f"noncomputable def f{tag}{i + 1} : (ZMod {q})[X] :=\n")
    w("  " + fmt_poly(f, "    ") + "\n\n")


def _emit_chains(w, tag, i, f, q, m, coprime_at):
    """Both square-and-multiply chains for one factor.  Returns `(last step, residue info)`.

    The second chain shares the first's `XPow f 1 X` base, so the two cannot be separated.
    """
    w(f"/-! ### Factor {i + 1}: `X ^ ({q} ^ {m})` mod `f` by square-and-multiply -/\n\n")
    nm, r = emit_factor(w, f"f{tag}{i + 1}", f"{tag}{i + 1}", q, q ** m, f)
    assert r == [0, 1], f"CERTIFICATE FALSE on factor {i + 1}: residue {r[:6]}"
    resid = r
    if coprime_at is not None:
        w(f"/-! Factor {i + 1} again, at the smaller exponent `{q} ^ {coprime_at}`,"
          " for the coprimality below. -/\n\n")
        nm2, r2 = emit_factor(w, f"f{tag}{i + 1}", f"{tag}{i + 1}c", q,
                              q ** coprime_at, f, base=f"p{tag}{i + 1}1")
        resid = (r2, nm2)
    return nm, resid


def _emit_factor_thm(w, hname, tag, k, q):
    prodexpr = " * ".join(f"f{tag}{i + 1}" for i in range(k))
    w(f"/-- The factorisation of `H` used by every statement below. -/\ntheorem factor_{hname} :"
      f" {hname} = {prodexpr} := by\n")
    w(f"  simp only [{hname}, " + ", ".join(f"f{tag}{i + 1}" for i in range(k)) + "]\n")
    w("  ring_nf\n  reduce_mod_char\n\n")


def _emit_coprime(w, tag, F, q, k):
    w("/-! ### Pairwise coprimality of the factors, by explicit Bézout identities -/\n\n")
    for i in range(k):
        for j in range(i + 1, k):
            u, v = bezout_pair(F[i], F[j], q)
            w(f"theorem cop{tag}{i + 1}_{j + 1} : IsCoprime f{tag}{i + 1} f{tag}{j + 1} :=\n")
            w("  ⟨" + fmt_poly(u, "    ") + ",\n")
            w("   " + fmt_poly(v, "    ") + ",\n")
            w(f"   by simp only [f{tag}{i + 1}, f{tag}{j + 1}]; ring_nf; reduce_mod_char⟩\n\n")


def _emit_assembly(w, hname, tag, k, q, m, last):
    w("/-! ### Assembly -/\n\n")
    w(f"theorem dvd_X_pow_card_pow_sub_X_{hname} :\n")
    w(f"    {hname} ∣ X ^ (Nat.card (ZMod {q})) ^ {m} - X := by\n")

    # every `have` below is UNASCRIBED on purpose: writing out `… ∣ X ^ (q ^ m) - X` puts the
    # huge exponent literal in a position the elaborator unifies structurally, and that is
    # the `npowRec` blow-up `XPow` exists to avoid.  Inferred types keep it an argument.
    for i in range(1, k):
        if i == 1:
            w(f"  have h2 := xpow_mul cop{tag}1_2 {last[0]} {last[1]}\n")
        else:
            w(f"  have c{i + 1} : IsCoprime ("
              + " * ".join(f"f{tag}{t + 1}" for t in range(i)) + f") f{tag}{i + 1} :=\n")
            w("    " + left_assoc([f"cop{tag}{t + 1}_{i + 1}" for t in range(i)]) + "\n")
            w(f"  have h{i + 1} := xpow_mul c{i + 1} h{i} {last[i]}\n")
    w(f"  rw [factor_{hname}]\n")
    w(f"  exact xpow_card (by rw [Nat.card_zmod]; norm_num) h{k}\n\n")


def _emit_coprime_leaf(w, hname, tag, F, q, j, resid):
    k = len(F)
    for i in range(k):
        r2, nm2 = resid[i]
        target = poly_sub(r2, [0, 1], q)
        u, v = bezout_pair(F[i], target, q)
        w(f"theorem cofrob{tag}{i + 1} : IsCoprime f{tag}{i + 1}"
          f" (X ^ (Nat.card (ZMod {q})) ^ {j} - X) := by\n")
        w(f"  have hd : f{tag}{i + 1} ∣ X ^ (Nat.card (ZMod {q})) ^ {j} -\n")
        w("      (" + fmt_poly(r2, "        ") + ") :=\n")
        w(f"    xpow_card (by rw [Nat.card_zmod]; norm_num) {nm2}\n")
        w("  obtain ⟨w, hw⟩ := hd\n")
        w(f"  have key : (X : (ZMod {q})[X]) ^ (Nat.card (ZMod {q})) ^ {j} - X =\n")
        w("      (" + fmt_poly(target, "        ") + ") +\n")
        w(f"      f{tag}{i + 1} * w := by linear_combination hw\n")
        w("  rw [key]\n")
        w("  exact IsCoprime.add_mul_left_right ⟨" + fmt_poly(u, "      ") + ",\n")
        w("    " + fmt_poly(v, "      ") + ",\n")
        w(f"    by simp only [f{tag}{i + 1}]; ring_nf; reduce_mod_char⟩ w\n\n")
    w(f"theorem isCoprime_{hname} :\n")
    w(f"    IsCoprime {hname} (X ^ (Nat.card (ZMod {q})) ^ {j} - X) := by\n")
    w(f"  rw [factor_{hname}]\n")
    w("  exact " + left_assoc([f"cofrob{tag}{i + 1}" for i in range(k)]) + "\n\n")


def generate_row(hname, hsrc, factors_src, q, m, tag, coprime_at, doc, out):
    """Emit the whole per-row module body as ONE file."""
    w = out.write
    F = _prepare(hsrc, factors_src, q)
    k = len(F)
    w(doc)
    for i, f in enumerate(F):
        _emit_def(w, tag, i, f, q, k)
    _emit_factor_thm(w, hname, tag, k, q)
    last, resid = [], []
    for i, f in enumerate(F):
        nm, r = _emit_chains(w, tag, i, f, q, m, coprime_at)
        last.append(nm)
        resid.append(r)
    _emit_coprime(w, tag, F, q, k)
    _emit_assembly(w, hname, tag, k, q, m, last)
    if coprime_at is not None:
        _emit_coprime_leaf(w, hname, tag, F, q, coprime_at, resid)


def generate_row_split(hname, hsrc, factors_src, q, m, tag, coprime_at, doc, out, factor_outs):
    """Emit the row as ONE parent body plus ONE body per factor.

    MEASURED 2026-07-31, and this is the whole reason the option exists: Lean elaborates a
    module single-threaded, so the `q = 67`, `m = 34` rows — 14 200 lines and ~2 500 theorems
    apiece — were still running after 60 minutes at 47 GB resident.  The `k` chains share
    nothing but the factor definitions, so one module per factor turns that into `k`
    independent jobs that `lake` runs CONCURRENTLY.

    What has to stay together: a factor's two chains (they share their `XPow f 1 X` base),
    and the factor's `def` (every step's `simp only [f…]` unfolds it).  What has to stay in
    the parent: everything that mentions more than one factor.
    """
    w = out.write
    F = _prepare(hsrc, factors_src, q)
    k = len(F)
    assert len(factor_outs) == k, f"expected {k} factor sinks, got {len(factor_outs)}"
    last, resid = [], []
    for i, f in enumerate(F):
        fw = factor_outs[i].write
        _emit_def(fw, tag, i, f, q, k)
        nm, r = _emit_chains(fw, tag, i, f, q, m, coprime_at)
        last.append(nm)
        resid.append(r)
    w(doc)
    _emit_factor_thm(w, hname, tag, k, q)
    _emit_coprime(w, tag, F, q, k)
    _emit_assembly(w, hname, tag, k, q, m, last)
    if coprime_at is not None:
        _emit_coprime_leaf(w, hname, tag, F, q, coprime_at, resid)
    return k


def left_assoc(names):
    """`IsCoprime.mul_left` is binary and left-nested: `((a.mul_left b).mul_left c)`."""
    expr = names[0]
    for n in names[1:]:
        expr = f"({expr}).mul_left {n}"
    return expr

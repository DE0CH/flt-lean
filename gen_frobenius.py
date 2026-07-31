#!/usr/bin/env python3
"""Generate the Lean Frobenius-table certificate for `H ∣ X ^ (q ^ m) - X`.

The route (recorded in `MazurNonCMCertificate.lean`'s leaf docstrings):

  * table   `T_i = X ^ (q * i) mod H`  for `i < deg H`, each step one
    `tab_step` with an explicit cofactor `Q` proving `X ^ q * T_{i-1} - T_i = H * Q`;
  * Frobenius: over `ZMod q` the `q`-power map is `Polynomial.expand q`, so if
    `r_k = Σ c_i X ^ i` then `r_k ^ q ≡ Σ c_i X ^ (q i) ≡ Σ c_i T_i (mod H)`, and the
    cofactor is the same `ZMod q`-combination `Σ c_i u_i` of the table's cofactors.

Everything is checked against PARI/GP independently before the Lean text is written.
"""
import subprocess
import sys


# ---------------------------------------------------------------- polynomials
def poly_trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def poly_add(a, b, q):
    n = max(len(a), len(b))
    r = [0] * n
    for i, c in enumerate(a):
        r[i] = c
    for i, c in enumerate(b):
        r[i] = (r[i] + c) % q
    return poly_trim(r)


def poly_sub(a, b, q):
    n = max(len(a), len(b))
    r = [0] * n
    for i, c in enumerate(a):
        r[i] = c
    for i, c in enumerate(b):
        r[i] = (r[i] - c) % q
    return poly_trim(r)


def poly_mul(a, b, q):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b):
                if cb:
                    r[i + j] = (r[i + j] + ca * cb) % q
    return poly_trim(r)


def poly_divmod(a, b, q):
    """`a = b * quo + rem`, `b` monic."""
    assert b and b[-1] == 1, "divisor must be monic"
    a = a[:]
    db = len(b) - 1
    quo = [0] * max(0, len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if c:
            quo[i - db] = c
            for j, cb in enumerate(b):
                a[i - db + j] = (a[i - db + j] - c * cb) % q
    return poly_trim(quo), poly_trim(a)


def poly_smul(c, a, q):
    c %= q
    if c == 0:
        return []
    return poly_trim([(c * x) % q for x in a])


# ------------------------------------------------------------------ Lean text
def fmt_term(c, e):
    if e == 0:
        return str(c)
    xs = "X" if e == 1 else f"X^{e}"
    return xs if c == 1 else f"{c}*{xs}"


def fmt_poly(a, indent, width=100):
    """Descending-exponent Lean literal, wrapped, continuation lines indented."""
    if not a:
        return "0"
    terms = [fmt_term(a[e], e) for e in range(len(a) - 1, -1, -1) if a[e]]
    lines = []
    cur = ""
    for k, t in enumerate(terms):
        piece = t if k == 0 else " + " + t
        head = indent if lines else ""
        if cur and len(head) + len(cur) + len(piece) > width:
            lines.append(cur + " +")
            cur = t
        else:
            cur += piece
    lines.append(cur)
    out = lines[0]
    for l in lines[1:]:
        out += "\n" + indent + l
    return out


def parse_poly(s, q):
    """Parse a Lean polynomial literal (only `+`-joined `c*X^e` / `X^e` / `c` terms)."""
    s = " ".join(s.replace("\n", " ").split())
    coeffs = {}
    for raw in s.split("+"):
        t = raw.strip()
        if not t:
            continue
        if "*" in t:
            c, xs = t.split("*", 1)
            c = int(c.strip())
            xs = xs.strip()
        elif t.startswith("X"):
            c, xs = 1, t
        else:
            coeffs[0] = (coeffs.get(0, 0) + int(t)) % q
            continue
        if xs == "X":
            e = 1
        else:
            assert xs.startswith("X^"), xs
            e = int(xs[2:])
        coeffs[e] = (coeffs.get(e, 0) + c) % q
    n = max(coeffs) + 1
    a = [0] * n
    for e, c in coeffs.items():
        a[e] = c
    return poly_trim(a)


# ------------------------------------------------------------------ generator
def generate(hname, hpoly_src, q, m, tag, out):
    """`tag` is the suffix used in the generated theorem names, e.g. `ElevenB`."""
    H = parse_poly(hpoly_src, q)
    n = len(H) - 1
    assert H[-1] == 1, "H must be monic"

    # ---- table T_i = X^(q i) mod H, with cofactors  X^q * T_{i-1} - T_i = H * Q_i
    Xq = [0] * q + [1]
    T = [[1]]
    Q = [None]
    for i in range(1, n):
        prod = poly_mul(Xq, T[i - 1], q)
        quo, rem = poly_divmod(prod, H, q)
        T.append(rem)
        Q.append(quo)

    # ---- Frobenius chain r_0 = X, r_{k+1} = Σ c_i T_i
    R = [[0, 1]]
    for k in range(m):
        rk = R[k]
        acc = []
        for i, c in enumerate(rk):
            if c:
                assert i < n, "r_k has degree ≥ deg H"
                acc = poly_add(acc, poly_smul(c, T[i], q), q)
        R.append(acc)
    assert R[m] == [0, 1], f"CERTIFICATE FALSE: X^({q}^{m}) mod H = {R[m][:8]}…"

    # ---- Lean text
    w = out.write
    w(f"theorem t{tag}0 : {hname} ∣ X ^ 0 - 1 := by simp\n")
    for i in range(1, n):
        w(f"\ntheorem t{tag}{i} : {hname} ∣ X ^ {q * i} -\n")
        w("    (" + fmt_poly(T[i], "      ") + ") :=\n")
        w(f"  tab_step (by norm_num) t{tag}{i - 1} ⟨\n")
        w("    " + fmt_poly(Q[i], "      ") + ",\n")
        if Q[i]:
            w(f"    by simp only [{hname}]; reduce_mod_char; ring_nf; reduce_mod_char⟩\n")
        else:
            w("    by ring⟩\n")

    w(f"\ntheorem r{tag}0 : {hname} ∣ X ^ {q} ^ 0 - X := by norm_num\n")
    for k in range(m):
        idx = [i for i, c in enumerate(R[k]) if c]
        w(f"\ntheorem r{tag}{k + 1} : {hname} ∣ X ^ {q} ^ {k + 1} -\n")
        w("    (" + fmt_poly(R[k + 1], "      ") + ") :=\n")
        w(f"  frob_step r{tag}{k} (by\n")
        # obtain the table cofactors actually used
        obtains = [f"obtain ⟨u{i}, e{i}⟩ := t{tag}{i}" for i in idx]
        line = "    "
        for j, ob in enumerate(obtains):
            piece = ob + (";" if j + 1 < len(obtains) else "")
            if len(line) + len(piece) + 1 > 100:
                w(line.rstrip() + "\n")
                line = "    "
            line += piece + " "
        w(line.rstrip() + "\n")
        comb = " + ".join(
            (f"u{i}" if R[k][i] == 1 else f"{R[k][i]} * u{i}") for i in idx)
        w("    refine ⟨" + wrap_expr(comb, "      ", 6 + len("refine ⟨")) + ", ?_⟩\n")
        w("    simp only [map_add, map_mul, map_pow, map_ofNat, map_one, expand_X]\n")
        lc = " + ".join(
            (f"e{i}" if R[k][i] == 1 else f"{R[k][i]} * e{i}") for i in idx)
        w("    linear_combination (norm := (reduce_mod_char; ring_nf; reduce_mod_char)) "
          + wrap_expr(lc, "      ", 76) + ")\n")


def wrap_expr(s, indent, first_used, width=100):
    """Wrap a `+`-joined expression, breaking after `+`."""
    parts = s.split(" + ")
    lines = []
    cur = ""
    used = first_used
    for k, p in enumerate(parts):
        piece = p if k == 0 else " + " + p
        if cur and used + len(cur) + len(piece) > width:
            lines.append(cur + " +")
            cur = p
            used = len(indent)
        else:
            cur += piece
    lines.append(cur)
    return ("\n" + indent).join(lines)


# ---------------------------------------------------------------- PARI check
def pari_check(hpoly_src, q, m, k=None):
    src = " ".join(hpoly_src.split()).replace("X", "x")
    script = f"""default(parisize, 2000000000);
H = Mod(1,{q}) * ({src});
r = lift(lift(Mod(x, H) ^ ({q}^{m})));
print(if(r == x, "OK", "FAIL"));
print(poldegree(H));
print(#polrootsmod(lift(H), {q}));
"""
    if k is not None:
        script += (f"s = lift(lift(Mod(x, H) ^ ({q}^{k})));\n"
                   f"print(if(gcd(lift(H), lift(s - x)) == 1, \"COPRIME\", \"NOTCOPRIME\"));\n")
    out = subprocess.run(["gp", "-q"], input=script, capture_output=True,
                         text=True, timeout=600)
    return out.stdout.strip(), out.stderr.strip()


if __name__ == "__main__":
    print("module intended for import; see gen_all.py", file=sys.stderr)

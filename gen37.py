#!/usr/bin/env python3
"""Generator for the two level-37 kernel-polynomial certificates.

Writes `Fermat/FLT/EllipticCurve/ThirtySevenKernelPolynomials.lean`, following
`GenusOneKernelPolynomials.lean` verbatim.  Exact rational arithmetic
throughout; the Lean kernel re-checks every identity below through `ring`.

Everything here is an UNTRUSTED SEARCHER in the project's sense: nothing in this
script is a proof, it only writes down the witnesses that `ring` then verifies.
"""
from fractions import Fraction as F

# ---------------------------------------------------------------- polynomials
# a polynomial is a list of Fractions, low degree first, no trailing zeros


def norm(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    return norm([(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0))
                 for i in range(n)])


def psub(a, b):
    n = max(len(a), len(b))
    return norm([(a[i] if i < len(a) else F(0)) - (b[i] if i < len(b) else F(0))
                 for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y:
                r[i + j] += x * y
    return norm(r)


def pscal(c, a):
    return norm([c * x for x in a])


def ppow(a, n):
    r = [F(1)]
    for _ in range(n):
        r = pmul(r, a)
    return r


def pdivmod(a, f):
    a = list(a)
    lf = f[-1]
    df = len(f) - 1
    q = [F(0)] * max(0, len(a) - df)
    for i in range(len(a) - 1, df - 1, -1):
        c = a[i] / lf
        if c:
            q[i - df] = c
            for j in range(len(f)):
                a[i - df + j] -= c * f[j]
    return norm(q), norm(a[:df])


def prem(a, f):
    return pdivmod(a, f)[1]


def pcofac(a, f):
    q, r = pdivmod(a, f)
    assert not r, "not divisible"
    return q


# ------------------------------------------------------------------ printing

def fmt(c):
    assert c.denominator == 1, f"non-integral coefficient {c}"
    return f"({c.numerator})"


def lean_poly(p, indent, width=96):
    """Render a polynomial as a Lean expression, low degree first, wrapped."""
    if not p:
        return "0"
    parts = []
    for i, c in enumerate(p):
        if c == 0:
            continue
        s = fmt(c)
        if i == 0:
            parts.append(s)
        elif c == 1:
            parts.append("X" if i == 1 else f"X ^ {i}")
        elif i == 1:
            parts.append(f"{s} * X")
        else:
            parts.append(f"{s} * X ^ {i}")
    if not parts:
        return "0"
    pad = " " * indent
    lines = []
    cur = parts[0]
    for t in parts[1:]:
        cand = cur + " + " + t
        if len(cand) + indent > width:
            lines.append(cur)
            cur = "+ " + t
        else:
            cur = cand
    lines.append(cur)
    return ("\n" + pad).join(lines)


# ------------------------------------------------------- Weierstrass invariants

class Curve:
    def __init__(self, a1, a2, a3, a4, a6):
        self.model = (a1, a2, a3, a4, a6)
        a1, a2, a3, a4, a6 = (F(x) for x in self.model)
        self.b2 = a1 * a1 + 4 * a2
        self.b4 = 2 * a4 + a1 * a3
        self.b6 = a3 * a3 + 4 * a6
        self.b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
        self.c4 = self.b2 ** 2 - 24 * self.b4
        self.c6 = -self.b2 ** 3 + 36 * self.b2 * self.b4 - 216 * self.b6
        self.disc = (-self.b2 ** 2 * self.b8 - 8 * self.b4 ** 3
                     - 27 * self.b6 ** 2 + 9 * self.b2 * self.b4 * self.b6)
        self.j = self.c4 ** 3 / self.disc
        self.Psi2Sq = norm([self.b6, 2 * self.b4, self.b2, F(4)])
        self.Psi3 = norm([self.b8, 3 * self.b6, 3 * self.b4, self.b2, F(3)])
        self.prePsi4 = norm([self.b4 * self.b8 - self.b6 ** 2,
                             self.b2 * self.b8 - self.b4 * self.b6,
                             10 * self.b8, 10 * self.b6, 5 * self.b4, self.b2, F(2)])
        self.Phi2 = norm([-self.b8, -2 * self.b6, -self.b4, F(0), F(1)])


# ------------------------------------------------------------ the preΨ' chain

def chain_for(p):
    rule = {}

    def rec(n):
        if n in rule or n <= 4:
            return
        if n % 2 == 1:
            m = (n - 1) // 2 - 2
            rule[n] = ('odd', m, [m + 1, m + 2, m + 3, m + 4])
        else:
            m = n // 2 - 3
            rule[n] = ('even', m, [m + 1, m + 2, m + 3, m + 4, m + 5])
        for d in rule[n][2]:
            rec(d)

    rec(p)
    order = sorted(set(list(rule) + [1, 2, 3, 4] +
                       [d for v in rule.values() for d in v[2]]))
    return order, rule


def compute_pre(E, f, p):
    order, rule = chain_for(p)
    r = {1: [F(1)], 2: [F(1)], 3: prem(E.Psi3, f), 4: prem(E.prePsi4, f)}
    steps = []
    P2 = ppow(E.Psi2Sq, 2)
    for n in order:
        if n <= 4:
            continue
        kind, m, deps = rule[n]
        if kind == 'odd':
            r1, r2, r3, r4 = (r[m + 1], r[m + 2], r[m + 3], r[m + 4])
            if m % 2 == 0:
                raw = psub(pmul(pmul(r4, ppow(r2, 3)), P2), pmul(r1, ppow(r3, 3)))
            else:
                raw = psub(pmul(r4, ppow(r2, 3)), pmul(pmul(r1, ppow(r3, 3)), P2))
        else:
            r1, r2, r3, r4, r5 = (r[m + 1], r[m + 2], r[m + 3], r[m + 4], r[m + 5])
            raw = psub(pmul(pmul(ppow(r2, 2), r3), r5), pmul(pmul(r1, r3), ppow(r4, 2)))
        rn = prem(raw, f)
        q = pcofac(psub(raw, rn), f)
        r[n] = rn
        steps.append((n, kind, m, q))
    return r, steps, rule


# --------------------------------------------------------------- Lean emission

class Row:
    def __init__(self, sub, model, ker, jval, mult, p=37):
        self.s = sub          # subscript string, e.g. "₇"
        self.E = Curve(*model)
        self.ker = ker
        self.j = F(jval)
        self.m = mult
        self.p = p
        assert self.E.j == self.j, f"j mismatch {self.E.j} vs {self.j}"
        assert len(ker) - 1 == (p - 1) // 2
        assert ker[-1] == 1

    def emit(self, out):
        s, E, f, p, m = self.s, self.E, self.ker, self.p, self.m
        C, K = f"curve{s}", f"ker{s}"
        w = out.append
        a = E.model
        w(f"/-! #### Row {s}: `p = {p}`, `j₀ = {self.j}`, model "
          f"`{list(a)}`, multiplier `m = {m}` -/\n")
        w(f"/-- The model at row {s} of `thirtySevenJTable`: "
          f"`[a₁, a₂, a₃, a₄, a₆] = {list(a)}`. -/")
        w(f"noncomputable def {C} : WeierstrassCurve ℚ := "
          f"⟨{a[0]}, {a[1]}, {a[2]}, {a[3]}, {a[4]}⟩\n")
        w(f"lemma {C}_Δ : {C}.Δ = {E.disc.numerator} := by")
        w(f"  norm_num [{C}, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,")
        w(f"    WeierstrassCurve.b₆, WeierstrassCurve.b₈]\n")
        w(f"lemma {C}_c₄ : {C}.c₄ = {E.c4.numerator} := by")
        w(f"  norm_num [{C}, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]\n")
        w(f"noncomputable instance : {C}.IsElliptic :=")
        w(f"  ⟨by rw [{C}_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩\n")
        w(f"lemma {C}_j : {C}.j = ({self.j.numerator} : ℚ) :=")
        w(f"  j_eq_of_Δ_c₄ {C} {C}_Δ {C}_c₄ (by norm_num) (by norm_num)\n")
        w(f"/-- The kernel polynomial at row {s}, monic of degree `(p-1)/2 = {(p-1)//2}`. -/")
        w(f"noncomputable def {K} : ℚ[X] :=")
        w(f"  " + lean_poly(f, 4) + "\n")
        for nm, poly, unf, bs in [
                ("Ψ₂Sq", E.Psi2Sq, "WeierstrassCurve.Ψ₂Sq", "b₂, b₄, b₆"),
                ("Ψ₃", E.Psi3, "WeierstrassCurve.Ψ₃", "b₂, b₄, b₆, b₈"),
                ("preΨ₄", E.prePsi4, "WeierstrassCurve.preΨ₄", "b₂, b₄, b₆, b₈")]:
            bl = ", ".join(f"WeierstrassCurve.{b}" for b in bs.split(", "))
            w(f"lemma {C}_{nm} : {C}.{nm} =")
            w(f"    " + lean_poly(poly, 4) + "\n    := by")
            w(f"  simp only [{unf}, {bl},")
            w(f"    {C}]")
            w(f"  norm_num [Polynomial.C_eq_natCast, map_ofNat]")
            w(f"  ring\n")

        # ---- the preΨ' chain
        r, steps, rule = compute_pre(E, f, p)
        w(f"""/-! ##### The chain of remainders modulo `{K}`

`preΨ'ₙ ≡ rₙ (mod {K})` along mathlib's `preNormEDS'` recursion, each `rₙ` of degree
`< {(p-1)//2}`; the chain ends at `r_{p} = 0`, which is exactly `{K} ∣ preΨ'_{p}`.  Every step is
one application of a `step_preΨ'_*` lemma against an explicit cofactor. -/
""")
        w(f"lemma pre{s}_1 : {K} ∣ {C}.preΨ' 1 - 1 := by simp\n")
        w(f"lemma pre{s}_2 : {K} ∣ {C}.preΨ' 2 - 1 := by simp\n")
        w(f"lemma pre{s}_3 : {K} ∣ {C}.preΨ' 3 -")
        w(f"    (" + lean_poly(r[3], 5) + ") := by")
        w(f"  rw [WeierstrassCurve.preΨ'_three, {C}_Ψ₃]")
        w(f"  exact ⟨0, by rw [{K}]; ring⟩\n")
        w(f"lemma pre{s}_4 : {K} ∣ {C}.preΨ' 4 -")
        w(f"    (" + lean_poly(r[4], 5) + ") := by")
        w(f"  rw [WeierstrassCurve.preΨ'_four, {C}_preΨ₄]")
        w(f"  exact ⟨0, by rw [{K}]; ring⟩\n")
        for n, kind, mm, q in steps:
            w(f"lemma pre{s}_{n} : {K} ∣ {C}.preΨ' {n} -")
            w(f"    (" + lean_poly(r[n], 5) + ") :=")
            if kind == 'odd':
                lemname = ("step_preΨ'_odd_even" if mm % 2 == 0 else "step_preΨ'_odd_odd")
                even = "(by decide)" if mm % 2 == 0 else "(by decide)"
                w(f"  {lemname} {C} {mm} {n} {even} (by norm_num)")
                w(f"    pre{s}_{mm+1} pre{s}_{mm+2} pre{s}_{mm+3} pre{s}_{mm+4}")
                w(f"    (by rw [{C}_Ψ₂Sq]; exact ⟨")
            else:
                w(f"  step_preΨ'_even {C} {mm} {n} (by norm_num)")
                w(f"    pre{s}_{mm+1} pre{s}_{mm+2} pre{s}_{mm+3} pre{s}_{mm+4} pre{s}_{mm+5}")
                w(f"    (⟨")
            w(f"      " + lean_poly(q, 6))
            w(f"      , by rw [{K}]; ring⟩)\n")
        w(f"lemma {K}_dvd_preΨ' : {K} ∣ {C}.preΨ' {p} := by")
        w(f"  simpa using pre{s}_{p}\n")

        # ---- coefficient / degree / monic
        d = len(f) - 1
        for i in range(d + 1):
            w(f"lemma {K}_coeff_{i} : C ({K}.coeff {i}) = ({fmt(f[i])[1:-1]} : ℚ[X]) := by")
            if f[i] == 1 and i == d:
                w(f"  rw [{K}]; simp [Polynomial.coeff_X]\n")
            else:
                w(f"  rw [{K}]; simp [Polynomial.coeff_X, map_ofNat]\n")
        w(f"lemma {K}_natDegree : {K}.natDegree = {d} := by")
        w(f"  rw [{K}]; compute_degree!\n")
        w(f"lemma {K}_monic : {K}.Monic := by")
        w(f"  rw [{K}]; monicity!\n")

        # ---- multComp
        Phi = prem(E.Phi2, f)
        Psi = prem(E.Psi2Sq, f)
        assert m == 2
        w(f"lemma {C}_Φ : {C}.Φ (2 : ℤ) =")
        w(f"    " + lean_poly(E.Phi2, 4) + "\n    := by")
        w(f"  rw [WeierstrassCurve.Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆,")
        w(f"    WeierstrassCurve.b₈, {C}]")
        w(f"  norm_num [Polynomial.C_eq_natCast, map_ofNat]")
        w(f"  ring\n")
        w(f"lemma {C}_ΨSq : {C}.ΨSq (2 : ℤ) =")
        w(f"    " + lean_poly(E.Psi2Sq, 4) + "\n    := by")
        w(f"  rw [WeierstrassCurve.ΨSq_two, {C}_Ψ₂Sq]\n")
        w(f"""/-! ##### The stability divisibility at row {s}

Every power `Φ^i` and `ΨSq^j` is reduced modulo `{K}` BEFORE being multiplied, so each
`ring` call below is an identity in degree `≤ {2*d}` rather than the degree-`{d*4}` identity the
unreduced sum would need. -/
""")
        w(f"lemma phi{s}_red : {K} ∣ {C}.Φ (2 : ℤ) -")
        w(f"    (" + lean_poly(Phi, 5) + ") := by")
        w(f"  rw [{C}_Φ]")
        w(f"  exact ⟨" + lean_poly(pcofac(psub(E.Phi2, Phi), f), 6) + f", by rw [{K}]; ring⟩\n")
        w(f"lemma psi{s}_red : {K} ∣ {C}.ΨSq (2 : ℤ) -")
        w(f"    (" + lean_poly(Psi, 5) + ") := by")
        w(f"  rw [{C}_ΨSq]")
        w(f"  exact ⟨" + lean_poly(pcofac(psub(E.Psi2Sq, Psi), f), 6) + f", by rw [{K}]; ring⟩\n")

        phipow = [[F(1)]]
        psipow = [[F(1)]]
        for i in range(d):
            phipow.append(prem(pmul(phipow[-1], Phi), f))
            psipow.append(prem(pmul(psipow[-1], Psi), f))

        for tag, base, red, pows in [("phi", E.Phi2, Phi, phipow),
                                     ("psi", E.Psi2Sq, Psi, psipow)]:
            nm = "Φ" if tag == "phi" else "ΨSq"
            w(f"lemma {tag}{s}_pow_0 : {K} ∣ {C}.{nm} (2 : ℤ) ^ 0 - 1 := by simp\n")
            w(f"lemma {tag}{s}_pow_1 : {K} ∣ {C}.{nm} (2 : ℤ) ^ 1 -")
            w(f"    (" + lean_poly(pows[1], 5) + ") := by")
            w(f"  rw [pow_one]; exact {tag}{s}_red\n")
            for i in range(2, d + 1):
                raw = pmul(pows[i - 1], red)
                q = pcofac(psub(raw, pows[i]), f)
                w(f"lemma {tag}{s}_pow_{i} : {K} ∣ {C}.{nm} (2 : ℤ) ^ {i} -")
                w(f"    (" + lean_poly(pows[i], 5) + ") :=")
                w(f"  dvd_sub_pow_succ {i-1} {tag}{s}_pow_{i-1} {tag}{s}_red ⟨")
                w(f"    " + lean_poly(q, 4))
                w(f"    , by rw [{K}]; ring⟩\n")

        terms = []
        for i in range(d + 1):
            raw = pscal(f[i], pmul(phipow[i], psipow[d - i]))
            red = prem(raw, f)
            q = pcofac(psub(raw, red), f)
            terms.append((i, red, q))
            w(f"lemma term{s}_{i} : {K} ∣")
            w(f"    ({fmt(f[i])[1:-1]}) * {C}.Φ (2 : ℤ) ^ {i} * {C}.ΨSq (2 : ℤ) ^ {d - i}")
            w(f"    -")
            w(f"    (" + lean_poly(red, 5) + ") :=")
            w(f"  dvd_sub_const_mul₂ phi{s}_pow_{i} psi{s}_pow_{d - i} ⟨")
            w(f"    " + lean_poly(q, 4))
            w(f"    , by rw [{K}]; ring⟩\n")

        def sum_expr(k, indent=4):
            pad = " " * indent
            ls = []
            for i in range(k + 1):
                lead = "" if i == 0 else "  "
                ls.append(f"{pad}{lead}{'' if i == 0 else '+ '}({fmt(f[i])[1:-1]}) * "
                          f"{C}.Φ (2 : ℤ) ^ {i} * {C}.ΨSq (2 : ℤ) ^ {d - i}")
            return "\n".join(ls)

        acc = terms[0][1]
        for k in range(1, d + 1):
            newacc_raw = padd(acc, terms[k][1])
            newacc = prem(newacc_raw, f)
            q = pcofac(psub(newacc_raw, newacc), f)
            w(f"lemma sum{s}_{k} : {K} ∣")
            w(sum_expr(k))
            w(f"    -")
            w(f"    (" + lean_poly(newacc, 5) + ") :=")
            prev = f"term{s}_0" if k == 1 else f"sum{s}_{k-1}"
            w(f"  dvd_sub_add {prev} term{s}_{k} ⟨" + lean_poly(q, 4) +
              f", by rw [{K}]; ring⟩\n")
            acc = newacc
        assert acc == [], "multComp does not reduce to zero"

        w(f"/-- **The stability divisibility at row {s}**, assembled from the reduced terms. -/")
        w(f"lemma {K}_dvd_multComp : {K} ∣")
        w(f"    ∑ i ∈ Finset.range ({K}.natDegree + 1), C ({K}.coeff i) *")
        w(f"      {C}.Φ ({m} : ℤ) ^ i * {C}.ΨSq ({m} : ℤ) ^")
        w(f"        ({K}.natDegree - i) := by")
        w(f"  rw [{K}_natDegree]")
        w(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]")
        w(f"  norm_num only")
        w(f"  rw [" + ", ".join(f"{K}_coeff_{i}" for i in range(d + 1)) + "]")
        w(f"  simpa using sum{s}_{d}\n")

        w(f"/-- **The kernel-polynomial certificate at row {s}.** -/")
        w(f"theorem {C}_isKernelPolynomial : {C}.IsKernelPolynomial {p} {K} {m} where")
        w(f"  monic := {K}_monic")
        w(f"  natDegree_eq := {K}_natDegree")
        w(f"  dvd_ΨSq := by")
        w(f"    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]")
        w(f"    exact dvd_pow {K}_dvd_preΨ' (by norm_num)")
        w(f"  mult_ne_zero := by decide")
        w(f"  generates := by")
        w(f"    intro k hk")
        w(f"    obtain ⟨i, -, hi⟩ := generates_aux_37_2 k hk")
        w(f"    exact ⟨i, hi⟩")
        w(f"  dvd_multComp := {K}_dvd_multComp\n")


def ker_of(vals, d=18):
    c = [F(0)] * (d + 1)
    for k, v in vals.items():
        c[k] = F(v)
    return norm(c)


KER1 = ker_of({18: 1, 17: -115, 16: 3170, 15: -28850, 14: 39775, 13: 668500,
               12: -2773750, 11: -1902500, 10: 28002500, 9: -35140625,
               8: -69743750, 7: 197015625, 6: -80500000, 5: -193046875,
               4: 233203125, 3: -57031250, 2: -36328125, 1: 19531250, 0: -1953125})

KER2 = ker_of({
    18: 1, 17: 167980, 16: 12913215710, 15: 600232557948475,
    14: 18698058495570580800, 13: 405564206748748459787375,
    12: 6038332696982426240276440375,
    11: 53930119445471891884635073558750,
    10: 36871083066082780545122058918018750,
    9: -7559578060419475677460433857717567578125,
    8: -140045009213625733354496916136025187036062500,
    7: -1537659251013303762414957186628945379236049062500,
    6: -11935338853753805004323533978563609247092595822437500,
    5: -68328627870032552153997362460511904360347331673215234375,
    4: -289217932073699120419983917633153523175207926235367446015625,
    3: -884848942464031236121982159401402915440014708268389756373828125,
    2: -1856947999990740593401777990029901868412893638583131329511640234375,
    1: -2397205804191518109075715853862712041333983113271864452235717849609375,
    0: -1437426526434670299642324459508567119410173453610504350056541156009765625})

HEADER = r'''/-
ThirtySevenKernelPolynomials.lean — own work for the Fermat project (not vendored).

**The two explicit kernel-polynomial certificates at the level-`37` isogeny
`j`-invariants**, cut 2026-07-31 out of the sorry leaf
`MazurIsogenyPrimeJ.exists_kernelPolynomial_thirtySeven` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`.

## What this file does

This is the exact analogue at `p = 37` of `GenusOneKernelPolynomials.lean`, and
it reuses that file's generic machinery verbatim.
`Fermat/FLT/EllipticCurve/KernelPolynomial.lean` reduces "`E/ℚ` carries a
Galois-stable cyclic subgroup of prime order `p`" to a purely polynomial
certificate `WeierstrassCurve.IsKernelPolynomial E p f m`; this file supplies
that certificate for each of the two rows of
`MazurIsogenyPrimeJ.thirtySevenJTable`, i.e. for each `j`-invariant at which a
curve over `ℚ` admits a rational `37`-isogeny.

| `j₀` | model `[a₁,a₂,a₃,a₄,a₆]` | `m` |
|------|--------------------------|-----|
| `−9317` | `[1, 1, 1, −8, 6]` | 2 |
| `−162677523113838677` | `[1, 46, 1, −284864943, −1854973327019]` | 2 |

`m = 2 = znprimroot 37` is a primitive root mod `37` (`2¹⁸ ≡ −1`), so `generates`
holds; `generates_aux_37_2` below is the `decide` that checks it.

**WHY ROW 2 IS *NOT* THE MINIMAL MODEL, and this is the trap for anyone
regenerating the table.**  The minimal model at that `j` is the conductor-`1225`
curve `[1, 1, 1, −208083, −36621194]` — the second Mazur–Swinnerton-Dyer curve,
*Arithmetic of Weil curves*, Invent. Math. 25 (1974), §5 — and its degree-`18`
kernel polynomial is **NOT INTEGRAL**: `elldivpol(E, 37)` has leading coefficient
`37`, not `1`, so Gauss's lemma does not force its monic factors to be integral,
and the constant term of the monic degree-`18` factor is
`−3148881707222283483037230006935969560314453125 / 37` (the numerator is `29`
mod `37`, so the denominator is genuine and not a transcription error).

That is admissible for `IsKernelPolynomial`, which asks only for monicity — but
it is **not usable in Lean**, because `ring` treats a rational numeral in `ℚ[X]`
as an ATOM.  `ℚ[X]` has a `Div` instance (`Polynomial.div`, the Euclidean one)
and is not a `DivisionRing`, so `ring` cannot see that `(3/37 : ℚ[X]) ^ 2 =
9/1369`; every identity below would fail.  Measured, not assumed: a two-line
`example` on `X² + (3/37)X + (5/37)` squared leaves `ring` stuck with
`(3/37)^2` unevaluated.

The row-2 model above is the **quadratic twist by `37`** of the minimal curve,
which has the same `j` (a rational cyclic `p`-isogeny is twist-invariant, since
twisting multiplies the Galois action on the kernel by a quadratic character and
that preserves its `ℤ`-span).  The twist multiplies every `x`-coordinate by `37`,
hence the kernel polynomial by `f_k ↦ 37^(18−k) f_k`, and the offending `1/37`
is cleared exactly once.  Nothing cheaper works: the models of a fixed `j` are
the twists composed with the `u`-scalings, which multiply `x` by an arbitrary
`c = d·w²`, and integrality forces `37 ∣ c`, so `c = 37` is optimal.  The
resulting curve has conductor `1677025 = 1225 · 37²`.

## How the two divisibilities are verified

Exactly as in `GenusOneKernelPolynomials.lean`, and for the same reason: written
out naively `dvd_ΨSq` is a polynomial identity of degree `684` with coefficients
of several hundred digits, which `ring` does not survive.  Both are verified
**modulo `f`**:

* `ΨSq 37 = (preΨ' 37)²` (`WeierstrassCurve.ΨSq_ofNat`, `37` odd), so it suffices
  that `f ∣ preΨ' 37`.  The remainders `rₙ := preΨ'ₙ mod f` are carried along
  mathlib's own `preNormEDS'` recursion, ONE TOP-LEVEL LEMMA PER `n`, over the
  chain `1, …, 12, 17, 18, 19, 20, 37` that the recursion actually needs; the
  chain ends at `r_37 = 0`.
* For `dvd_multComp` the powers `Φ₂^i` and `ΨSq₂^j` are reduced modulo `f`
  BEFORE being multiplied, so every `ring` call is an identity in degree `≤ 36`
  rather than `deg f · deg Φ₂`.

Each step is a `Dvd` witness supplied explicitly.  The reason each step is a
separate top-level lemma rather than a `have` inside one proof is the heartbeat
budget: a single tactic block carrying the whole chain exceeds the default limit
on `whnf` alone, while the split chain does not.  That was the entire fix at
`p = 17` and `p = 19` and it applies unchanged here.

## Provenance of the constants

Every kernel polynomial, cofactor and remainder below was computed by `gen37.py`
at the repository root, in exact rational arithmetic, as an *untrusted searcher*:
the script re-runs mathlib's `preNormEDS'` recursion itself (rather than PARI's
normalisation, which differs) and asserts `r_37 = 0` and that the reduced
`multComp` sum vanishes, for both rows, before emitting a line.  The kernel
polynomials themselves, the degree-`18` factorisations of `elldivpol(E, 37)`
(degrees `[18, 222, 222, 222]` at row 2, and `f ∣ elldivpol` with `disc f ≠ 0` at
both), the `j`-invariants and the conductors were cross-checked in PARI/GP.
None of that is a proof; the Lean kernel re-checks every identity below through
`ring` against an explicit witness.
-/
module

public import Fermat.FLT.EllipticCurve.GenusOneKernelPolynomials

@[expose] public section

open Polynomial WeierstrassCurve GenusOneKernel

namespace ThirtySevenKernel

/-- `2` is a primitive root modulo `37`, so its powers cover `(ℤ/37) ∖ 0` up to
sign; this is the `generates` field of both certificates below. -/
theorem generates_aux_37_2 : ∀ k : ZMod 37, k ≠ 0 →
    ∃ i ∈ Finset.range 37, ((2 : ℕ) : ZMod 37) ^ i = k ∨ ((2 : ℕ) : ZMod 37) ^ i = -k := by
  decide

'''

FOOTER = """
end ThirtySevenKernel
"""


def main():
    rows = [
        Row("₇", (1, 1, 1, -8, 6), KER1, -9317, 2),
        Row("₈", (1, 46, 1, -284864943, -1854973327019), KER2,
            -162677523113838677, 2),
    ]
    out = []
    for r in rows:
        r.emit(out)
    text = HEADER + "\n".join(out) + FOOTER
    path = "Fermat/FLT/EllipticCurve/ThirtySevenKernelPolynomials.lean"
    with open(path, "w") as fh:
        fh.write(text)
    print(f"wrote {path}: {len(text)} bytes, {text.count(chr(10))} lines")


if __name__ == "__main__":
    main()

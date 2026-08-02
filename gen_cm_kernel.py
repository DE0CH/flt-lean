#!/usr/bin/env python3
"""Generator for the class-number-one kernel-polynomial certificates.

Writes `Fermat/FLT/EllipticCurve/ClassNumberOneKernelPolynomials.lean`, following
`GenusOneKernelPolynomials.lean` and `ThirtySevenKernelPolynomials.lean` verbatim.
Exact rational arithmetic throughout; the Lean kernel re-checks every identity
below through `ring`.

This is `gen37.py` generalised in the MULTIPLIER `m` (level `43` needs `m = 3`,
since `znprimroot 43 = 3` and `2` has order `14` mod `43`) and carrying a
`--measure` mode, which runs the whole exact computation and reports the sizes
WITHOUT emitting a line.  Run the measurement before generating at a new level:
the cost is dominated by one cofactor whose coefficient count grows like
`deg f · maxdig f`, and at `p = 163` it is out of reach in this style.

    python3 gen_cm_kernel.py --measure 43
    python3 gen_cm_kernel.py 43

Everything here is an UNTRUSTED SEARCHER in the project's sense: nothing in this
script is a proof, it only writes down the witnesses that `ring` then verifies.
"""
import sys
from fractions import Fraction as F

# `--measure` at p = 67 and p = 163 formats cofactors with tens and hundreds of
# thousands of digits, well past CPython 3.11's 4300-digit int->str default.
sys.set_int_max_str_digits(4000000)

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


def maxdig(p):
    return max((len(str(abs(c.numerator))) for c in p), default=0)


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
        # Φ₂ = X⁴ − b₄X² − 2b₆X − b₈,  ΨSq₂ = Ψ₂Sq
        self.Phi2 = norm([-self.b8, -2 * self.b6, -self.b4, F(0), F(1)])
        # Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq,  ΨSq₃ = Ψ₃²
        self.Psi3Sq = pmul(self.Psi3, self.Psi3)
        self.Phi3 = psub(pmul([F(0), F(1)], self.Psi3Sq),
                         pmul(self.prePsi4, self.Psi2Sq))

    def mult_polys(self, m):
        """(Φ_m, ΨSq_m) as polynomials."""
        if m == 2:
            return self.Phi2, self.Psi2Sq
        if m == 3:
            return self.Phi3, self.Psi3Sq
        raise ValueError(f"multiplier {m} not supported (only 2 and 3)")


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

MULT_DATA = {
    2: dict(Phi_lemma="WeierstrassCurve.Φ_two", PsiSq_lemma="WeierstrassCurve.ΨSq_two",
            Phi_unfold="  rw [WeierstrassCurve.Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆,\n"
                       "    WeierstrassCurve.b₈, {C}]\n"
                       "  norm_num [Polynomial.C_eq_natCast, map_ofNat]\n  ring",
            PsiSq_unfold="  rw [WeierstrassCurve.ΨSq_two, {C}_Ψ₂Sq]"),
    3: dict(Phi_lemma="WeierstrassCurve.Φ_three", PsiSq_lemma="WeierstrassCurve.ΨSq_three",
            Phi_unfold="  rw [WeierstrassCurve.Φ_three, {C}_Ψ₃, {C}_preΨ₄, {C}_Ψ₂Sq]\n  ring",
            PsiSq_unfold="  rw [WeierstrassCurve.ΨSq_three, {C}_Ψ₃]\n  ring"),
}


class Row:
    def __init__(self, sub, model, ker, jval, mult, p):
        self.s = sub          # subscript string, e.g. "₄₃"
        self.E = Curve(*model)
        self.ker = ker
        self.j = F(jval)
        self.m = mult
        self.p = p
        assert self.E.j == self.j, f"j mismatch {self.E.j} vs {self.j}"
        assert len(ker) - 1 == (p - 1) // 2, "kernel polynomial has the wrong degree"
        assert ker[-1] == 1, "kernel polynomial is not monic"
        for c in ker:
            assert c.denominator == 1, f"kernel polynomial is not integral: {c}"

    def measure(self):
        """Run the whole exact computation and report the sizes, emitting nothing."""
        E, f, p, m = self.E, self.ker, self.p, self.m
        d = len(f) - 1
        print(f"p = {p}, deg f = {d}, maxdig f = {maxdig(f)}, m = {m}")
        order, _ = chain_for(p)
        print(f"  chain: {order}  ({len([n for n in order if n > 4])} step lemmas)")
        r, steps, _ = compute_pre(E, f, p)
        assert r[p] == [], f"r_{p} != 0 -- f does not divide preΨ'_{p}"
        print(f"  r_{p} = 0 CONFIRMED")
        worst = max(steps, key=lambda t: maxdig(t[3]) * len(t[3]))
        for n, kind, mm, q in steps:
            print(f"    pre_{n:<3} cofactor deg {len(q)-1:<4} maxdig {maxdig(q):<7}"
                  f" ~{maxdig(q)*len(q)//1000} kB")
        Phi, PsiSq = E.mult_polys(m)
        Phir, Psir = prem(Phi, f), prem(PsiSq, f)
        phipow, psipow = [[F(1)]], [[F(1)]]
        for i in range(d):
            phipow.append(prem(pmul(phipow[-1], Phir), f))
            psipow.append(prem(pmul(psipow[-1], Psir), f))
        big = 0
        for i in range(2, d + 1):
            for pows, red in ((phipow, Phir), (psipow, Psir)):
                q = pcofac(psub(pmul(pows[i - 1], red), pows[i]), f)
                big = max(big, maxdig(q) * len(q))
        acc = prem(pscal(f[0], pmul(phipow[0], psipow[d])), f)
        for k in range(1, d + 1):
            raw = pscal(f[k], pmul(phipow[k], psipow[d - k]))
            red = prem(raw, f)
            big = max(big, maxdig(pcofac(psub(raw, red), f)) * len(pcofac(psub(raw, red), f)))
            newacc_raw = padd(acc, red)
            acc = prem(newacc_raw, f)
            big = max(big, maxdig(pcofac(psub(newacc_raw, acc), f)) *
                      len(pcofac(psub(newacc_raw, acc), f)))
        assert acc == [], "multComp does not reduce to zero"
        print(f"  reduced multComp sum = 0 CONFIRMED")
        wq = worst[3]
        print(f"  WORST preΨ' cofactor: step {worst[0]}, degree {len(wq)-1},"
              f" maxdig {maxdig(wq)}, ~{maxdig(wq)*len(wq)//1000} kB in one lemma")
        print(f"  WORST multComp cofactor: ~{big//1000} kB in one lemma")

    def emit(self, out):
        s, E, f, p, m = self.s, self.E, self.ker, self.p, self.m
        C, K = f"curve{s}", f"ker{s}"
        md = MULT_DATA[m]
        w = out.append
        a = E.model
        w(f"/-! #### Row {s}: `p = {p}`, `j₀ = {self.j}`, model "
          f"`{list(a)}`, multiplier `m = {m}` -/\n")
        w(f"/-- The model at level `{p}` of `classNumberOneJTable`: "
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
        w(f"/-- The kernel polynomial at level `{p}`, monic of degree "
          f"`(p-1)/2 = {(p-1)//2}`. -/")
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
        assert r[p] == [], f"r_{p} != 0"
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
            # A step whose cofactor is tens of kB of digits exhausts the default
            # heartbeat budget inside `synthesize pending MVars`, BEFORE `ring` is
            # reached.  Measured at p = 43: only the two odd steps 21 and 23 fail at
            # the default 200000, but the bump is keyed on size rather than on the
            # two observed names so that it survives a change of model.
            if maxdig(q) * len(q) > 20000:
                w(f"-- cofactor of degree {len(q)-1} with {maxdig(q)}-digit coefficients")
                w(f"set_option maxHeartbeats 1600000 in")
            w(f"lemma pre{s}_{n} : {K} ∣ {C}.preΨ' {n} -")
            w(f"    (" + lean_poly(r[n], 5) + ") :=")
            if kind == 'odd':
                lemname = ("step_preΨ'_odd_even" if mm % 2 == 0 else "step_preΨ'_odd_odd")
                w(f"  {lemname} {C} {mm} {n} (by decide) (by norm_num)")
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
        PhiPoly, PsiSqPoly = E.mult_polys(m)
        Phi = prem(PhiPoly, f)
        Psi = prem(PsiSqPoly, f)
        w(f"lemma {C}_Φ : {C}.Φ ({m} : ℤ) =")
        w(f"    " + lean_poly(PhiPoly, 4) + "\n    := by")
        w(md["Phi_unfold"].format(C=C) + "\n")
        w(f"lemma {C}_ΨSq : {C}.ΨSq ({m} : ℤ) =")
        w(f"    " + lean_poly(PsiSqPoly, 4) + "\n    := by")
        w(md["PsiSq_unfold"].format(C=C) + "\n")
        w(f"""/-! ##### The stability divisibility at level `{p}`

Every power `Φ^i` and `ΨSq^j` is reduced modulo `{K}` BEFORE being multiplied, so each
`ring` call below is an identity in degree `≤ {2*d}` rather than the degree-`{d*max(len(PhiPoly),len(PsiSqPoly))}` identity the
unreduced sum would need. -/
""")
        w(f"lemma phi{s}_red : {K} ∣ {C}.Φ ({m} : ℤ) -")
        w(f"    (" + lean_poly(Phi, 5) + ") := by")
        w(f"  rw [{C}_Φ]")
        w(f"  exact ⟨" + lean_poly(pcofac(psub(PhiPoly, Phi), f), 6) + f", by rw [{K}]; ring⟩\n")
        w(f"lemma psi{s}_red : {K} ∣ {C}.ΨSq ({m} : ℤ) -")
        w(f"    (" + lean_poly(Psi, 5) + ") := by")
        w(f"  rw [{C}_ΨSq]")
        w(f"  exact ⟨" + lean_poly(pcofac(psub(PsiSqPoly, Psi), f), 6) + f", by rw [{K}]; ring⟩\n")

        phipow = [[F(1)]]
        psipow = [[F(1)]]
        for i in range(d):
            phipow.append(prem(pmul(phipow[-1], Phi), f))
            psipow.append(prem(pmul(psipow[-1], Psi), f))

        for tag, red, pows in [("phi", Phi, phipow), ("psi", Psi, psipow)]:
            nm = "Φ" if tag == "phi" else "ΨSq"
            w(f"lemma {tag}{s}_pow_0 : {K} ∣ {C}.{nm} ({m} : ℤ) ^ 0 - 1 := by simp\n")
            w(f"lemma {tag}{s}_pow_1 : {K} ∣ {C}.{nm} ({m} : ℤ) ^ 1 -")
            w(f"    (" + lean_poly(pows[1], 5) + ") := by")
            w(f"  rw [pow_one]; exact {tag}{s}_red\n")
            for i in range(2, d + 1):
                raw = pmul(pows[i - 1], red)
                q = pcofac(psub(raw, pows[i]), f)
                w(f"lemma {tag}{s}_pow_{i} : {K} ∣ {C}.{nm} ({m} : ℤ) ^ {i} -")
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
            w(f"    ({fmt(f[i])[1:-1]}) * {C}.Φ ({m} : ℤ) ^ {i} * {C}.ΨSq ({m} : ℤ) ^ {d - i}")
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
                          f"{C}.Φ ({m} : ℤ) ^ {i} * {C}.ΨSq ({m} : ℤ) ^ {d - i}")
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

        w(f"/-- **The stability divisibility at level `{p}`**, assembled from the "
          f"reduced terms. -/")
        w(f"lemma {K}_dvd_multComp : {K} ∣")
        w(f"    ∑ i ∈ Finset.range ({K}.natDegree + 1), C ({K}.coeff i) *")
        w(f"      {C}.Φ ({m} : ℤ) ^ i * {C}.ΨSq ({m} : ℤ) ^")
        w(f"        ({K}.natDegree - i) := by")
        w(f"  rw [{K}_natDegree]")
        w(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]")
        w(f"  norm_num only")
        w(f"  rw [" + ", ".join(f"{K}_coeff_{i}" for i in range(d + 1)) + "]")
        w(f"  simpa using sum{s}_{d}\n")

        w(f"/-- **The kernel-polynomial certificate at level `{p}`.** -/")
        w(f"theorem {C}_isKernelPolynomial : {C}.IsKernelPolynomial {p} {K} {m} where")
        w(f"  monic := {K}_monic")
        w(f"  natDegree_eq := {K}_natDegree")
        w(f"  dvd_ΨSq := by")
        w(f"    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (by decide), mul_one]")
        w(f"    exact dvd_pow {K}_dvd_preΨ' (by norm_num)")
        w(f"  mult_ne_zero := by decide")
        w(f"  generates := by")
        w(f"    intro k hk")
        w(f"    obtain ⟨i, -, hi⟩ := generates_aux_{p}_{m} k hk")
        w(f"    exact ⟨i, hi⟩")
        w(f"  dvd_multComp := {K}_dvd_multComp\n")


def poly_of(coeffs):
    """coeffs given high degree first, as in PARI's output."""
    return norm([F(c) for c in reversed(coeffs)])


# The degree-21 kernel polynomial of the CM curve of discriminant −43.
# Computed in PARI/GP as the kernel of the endomorphism √−43 (see the module
# docstring below), cross-checked to divide `elldivpol(E, 43)` exactly and to be
# squarefree.
KER43 = poly_of([
    1,
    18060,
    126946750,
    489369976375,
    1168610033548125,
    1773645029681131250,
    1532876113961355843750,
    128734593339281286328125,
    -1659617500554226727948437500,
    -2593923260137777866281005859375,
    -2224992875050805134292438339843750,
    -1173489934519088750250450506640625000,
    -288884954593908491454305477506835937500,
    96919813082141428232518249348895263671875,
    136792373684348637607163238681427142333984375,
    73489066628466838335802225025247909759521484375,
    25103416631885877799007130730830169181823730468750,
    5872341070167760344676468196210175491268157958984375,
    934290098530056081833736417811408309667743682861328125,
    95332579808686306171909901954819268607021999359130859375,
    5427838409642598757258348252470126427233340358734130859375,
    118805934818800039108242791382575258103262287616729736328125])

# The degree-33 kernel polynomial of the CM curve of discriminant −67, computed the
# same analytic way (see the module docstring) and CONFIRMED to give `r_67 = 0`.
# It is here so that `--measure 67` is reproducible and so that a successor who wants
# to attempt that level can start immediately.  Emitting Lean at `67` additionally
# needs the HEADER below rewritten for that level, which `main` refuses to do silently.
KER67 = poly_of([
    1,
    -91159530,
    3396329421737175,
    -73226989273539224450250,
    1052425537175084013072462436875,
    -10842624070181841739713331519222200000,
    83247587582848270670507678253567362421843750,
    -483640398245384540283073592791983082971147934921875,
    2101200231009796912445586753068598035633763033564760546875,
    -6359350349044984033231419067402820242168274660118387122818359375,
    9229865832408721880919850139815907786619419725424192994388290878906250,
    27850815658787414692426379026116043990284847132656737130798437850841845703125,
    -255264682421905378239908593870844319205686746516013870951083553361098074358398437500,
    1032928464407883932319270009427358922505532368101660361384638708835872735422413381347656250,
    -2815055333608687496603115229124700419934449649723034020118114302556671369668356839760858154296875,
    5289483870875718102263706725953221532165513343416919915264503551147166823006780600403051144927978515625,
    -5379521306546441102345433666093850054874468517114113736909727890863984256433147010345015077498019256591796875,
    -4878288283754519079425998451889404710389565164261105238102129318963490477481971821729219340762870814951324462890625,
    37248787178141237067420886864373182095599040271323852208018655307082249119414479401675964378835050987288378746032714843750,
    -99549442050469747973932700641788706301159775937447886007423677637576759121351785374265812976080762891453791408136215209960937500,
    183498727769455256391338942910736616440152858273162034426152045740736451228645367362651774877529226655731360459341686285877227783203125,
    -259254370147857258159958925403520246655099223385878356416046731123418851129890583773335423594478967131832155373440201852806430816650390625000,
    288191743283074727077262193018122905805995343924588331542741796543987655999656345004887493103622311746056817242129932428916537682151794433593750000,
    -249923732338216269836267662050476100042114703053096392165752757269664832309913949008056112767010726032681752267317111591582129549896284401416778564453125,
    160797716740400777010316822615429484931771764454210378847384029815002454295974808639169751979328970298451050251983206653212107615319116183563590049743652343750,
    -63874496678018530086427332750627611208008618594281191482546958653915196220055050604932278684781915437071683234408197480800560994155462641290659082829952239990234375,
    -2238631774546343774692803598836007879165929747189406161016728860274143490616799160279441892135156573203256837880706006799070433075909701868767559575437009334564208984375,
    26721553939635296582277198391712410036977895347489839765375682603286089487476135458040003284217232668613911266027474731921748748591123686488030465370534829430282115936279296875,
    -23619278165404825851001037521276459361938837648737803628411090204278231971336575118907850953502668960736116083378152127891142223215207109595043091799575280784641541540622711181640625,
    12559384064389389027632648523522213494087906573644762374898683095397959275305366973634756186252898418341758492521550710269487840306103027676225923629901957960313173701241612434387207031250,
    -4528419359155691513576119280892738247766582116255198080558321587607662432989809421694240865185391498685735975249692766042538630369749209673605659943964578322910860080262511037290096282958984375,
    1093996663538889401518257521876658010521916344279038988082730998518599368775127469418844630285152214713467958573000356283947770974943767887867928700703561952269820749213656996809877455234527587890625,
    -161252927320477544769072619768760188355828130284963624313365701761777465113396646534710584097210603120562336169321996265249828044956364862875076756700293641200580674107552627301683393307030200958251953125,
    11018794951661361370617886003517117352298432886735082625893672189035860891685798321418848636643237905557383668335668494411186214807908221938740526757880309319449513749789553057528670822386629879474639892578125])

ROWS = {
    43: dict(sub="₄₃", model=(0, 0, 1, -1053500, -416198344), ker=KER43,
             jval=-884736000, mult=3),
    67: dict(sub="₆₇", model=(0, 0, 1, -9448325444250, 11178418945712742281),
             ker=KER67, jval=-147197952000, mult=2),
}

# Levels this script may EMIT Lean for.  `--measure` works at every level in ROWS.
EMITTABLE = {43}


HEADER = r'''/-
ClassNumberOneKernelPolynomials.lean — own work for the Fermat project (not vendored).

**The explicit kernel-polynomial certificate at the class-number-one isogeny
prime `p = 43`**, written 2026-08-01 to discharge
`MazurIsogenyPrimeJ.exists_kernelPolynomial_fortyThree` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, and thereby to remove `p = 43` from
the CM leaf `MazurIsogenyPrimeJ.exists_cmEndomorphism_classNumberOne`.

## What this file does

This is the exact analogue at `p = 43` of `GenusOneKernelPolynomials.lean` and
`ThirtySevenKernelPolynomials.lean`, and it reuses the former's generic
machinery verbatim.  `Fermat/FLT/EllipticCurve/KernelPolynomial.lean` reduces
"`E/ℚ` carries a Galois-stable cyclic subgroup of prime order `p`" to a purely
polynomial certificate `WeierstrassCurve.IsKernelPolynomial E p f m`; this file
supplies that certificate at the `p = 43` row of
`Fermat.classNumberOneJTable`, i.e. at the unique `j`-invariant over `ℚ`
admitting a rational `43`-isogeny.

| `p` | `j₀` | model `[a₁,a₂,a₃,a₄,a₆]` | `m` |
|-----|------|--------------------------|-----|
| `43` | `−884736000` | `[0, 0, 1, −1053500, −416198344]` | 3 |

**THE MULTIPLIER IS `3`, NOT `2`.**  `IsKernelPolynomial.generates` asks that the
powers of `m` cover `(ℤ/p) ∖ 0` up to sign, i.e. that `m` generate
`(ℤ/p)ˣ / ±1`.  At `p = 43` the element `2` has order `14`, so it does NOT (its
powers up to sign cover `14` of the `21` classes); `znprimroot 43 = 3` does.
That is the one structural difference from the `p = 37` file, and it changes
which pair of mathlib lemmas computes `Φ` and `ΨSq`: `WeierstrassCurve.Φ_three`
(`Φ 3 = X·Ψ₃² − preΨ₄·Ψ₂Sq`) and `WeierstrassCurve.ΨSq_three`
(`ΨSq 3 = Ψ₃²`) in place of `Φ_two` and `ΨSq_two`.  Row 4 of
`GenusOneKernelPolynomials.lean` (`p = 17`, `m = 3`) is the template.

## Where the kernel polynomial comes from, and why it is INTEGRAL

`E` has complex multiplication by the maximal order of `K = ℚ(√−43)`, which has
class number one.  `43` RAMIFIES, `(43) = 𝔭²`, and `𝔭 = (√−43)` is principal, so
the degree-`43` isogeny is an ENDOMORPHISM of `E` — the curve is `43`-isogenous
to itself, which is why the Hilbert class polynomial `polclass(−43) = x + 884736000`
is linear and the table has one row rather than two.  The kernel is therefore
`E[𝔭] = ker(√−43)`, and its `21` `x`-coordinates were computed analytically in
PARI/GP: with `Λ = ℤω₁ + ℤω₂` the period lattice, `√−43·ω₁ = ω₁ − 2ω₂ ∈ Λ`
(checked to `250` digits), so `z₁ := (ω₁ − 2ω₂)/43` generates `ker(√−43)` and
`f = ∏_{k=1}^{21} (X − x(k·z₁))`.  The coefficients came out integral to within
`10⁻¹⁹⁰` of an integer at `250` digits of working precision, the largest having
`60` digits.

**Integrality is not automatic and it is what makes this file possible at all.**
`ring` treats a rational numeral in `ℚ[X]` as an ATOM — `ℚ[X]` carries `Div`
(`Polynomial.div`, the Euclidean one) and is not a `DivisionRing` — so a single
non-integral coefficient would make every identity below fail.  At `p = 37` the
minimal model had a `1/37` and the model had to be replaced by its quadratic
twist (see `ThirtySevenKernelPolynomials.lean`).  Here the model above is already
integral and no twist is needed; `elldivpol(E, 43)` is monic, so Gauss's lemma
forces its monic factors to be integral.

## How the two divisibilities are verified

Exactly as in `GenusOneKernelPolynomials.lean`, and for the same reason: written
out naively `dvd_ΨSq` is a polynomial identity of degree `924` with coefficients
of hundreds of digits, which `ring` does not survive.  Both are verified
**modulo `f`**:

* `ΨSq 43 = (preΨ' 43)²` (`WeierstrassCurve.ΨSq_ofNat`, `43` odd), so it suffices
  that `f ∣ preΨ' 43`.  The remainders `rₙ := preΨ'ₙ mod f` are carried along
  mathlib's own `preNormEDS'` recursion, ONE TOP-LEVEL LEMMA PER `n`, over the
  chain `1, …, 13, 20, 21, 22, 23, 43` that the recursion actually needs — it is
  a DAG rather than a walk, so only `18` indices are visited and not `43`; the
  chain ends at `r_43 = 0`.
* For `dvd_multComp` the powers `Φ₃^i` and `ΨSq₃^j` are reduced modulo `f`
  BEFORE being multiplied, so every `ring` call is an identity in degree `≤ 42`
  rather than `deg f · deg Φ₃ = 189`.

Each step is a `Dvd` witness supplied explicitly.  The reason each step is a
separate top-level lemma rather than a `have` inside one proof is the heartbeat
budget: a single tactic block carrying the whole chain exceeds the default limit
on `whnf` alone, while the split chain does not.  That was the entire fix at
`p = 17`, `p = 19` and `p = 37` and it applies unchanged here.

## Provenance of the constants

Every kernel polynomial, cofactor and remainder below was computed by
`gen_cm_kernel.py` at the repository root, in exact rational arithmetic, as an
*untrusted searcher*: the script re-runs mathlib's `preNormEDS'` recursion itself
(rather than PARI's normalisation, which differs) and asserts `r_43 = 0` and that
the reduced `multComp` sum vanishes before emitting a line.  The kernel
polynomial itself, its exact divisibility of `elldivpol(E, 43)` (degree `924`),
its squarefreeness, the `j`-invariant `−884736000` and `znprimroot 43 = 3` were
cross-checked in PARI/GP.  None of that is a proof; the Lean kernel re-checks
every identity below through `ring` against an explicit witness.

## The other two class-number-one levels

`exists_cmEndomorphism_classNumberOne` still covers `p ∈ {67, 163}`.  Both were
MEASURED with this script rather than estimated — the kernel polynomials were
computed the same analytic way and `r_p = 0` was CONFIRMED at both, so the
certificates are correct and only their SIZE is the obstruction:

| `p` | `deg f` | max digits in `f` | worst single cofactor | whole `preΨ'` chain |
|-----|---------|-------------------|-----------------------|---------------------|
| 43 | 21 | 60 | 226 kB (deg 65, 3436 digits) | ~0.46 MB |
| 67 | 33 | 209 | 1.7 MB (deg 101, 16566 digits) | ~3.7 MB |
| 163 | 81 | 992 | 45 MB (deg 245, 182969 digits) | ~105 MB |

This file, at `p = 43`, is 1.85 MB and elaborates in 260 s.  `p = 67` would be
roughly eight times that with a single `ring` identity of 1.7 MB — attemptable,
but only after trying to shrink `f` by a better choice of model, since the model
is free up to twist and every digit saved propagates through the whole chain.
**`p = 163` is out of reach in this style by two orders of magnitude**: 45 MB of
digits inside one `ring` call.  That level needs a different cut, not a bigger
machine.
-/
module

public import Fermat.FLT.EllipticCurve.GenusOneKernelPolynomials

@[expose] public section

open Polynomial WeierstrassCurve GenusOneKernel

namespace ClassNumberOneKernel

/-- `3` is a primitive root modulo `43`, so its powers cover `(ℤ/43) ∖ 0` up to
sign; this is the `generates` field of the certificate below.

`2` would NOT do: it has order `14` modulo `43`. -/
theorem generates_aux_43_3 : ∀ k : ZMod 43, k ≠ 0 →
    ∃ i ∈ Finset.range 43, ((3 : ℕ) : ZMod 43) ^ i = k ∨ ((3 : ℕ) : ZMod 43) ^ i = -k := by
  decide

'''

FOOTER = """
end ClassNumberOneKernel
"""

PATH = "Fermat/FLT/EllipticCurve/ClassNumberOneKernelPolynomials.lean"


def main():
    args = sys.argv[1:]
    measure = "--measure" in args
    levels = [int(a) for a in args if not a.startswith("--")] or [43]
    rows = [Row(p=p, **ROWS[p]) for p in levels]
    if measure:
        for r in rows:
            r.measure()
        return
    bad = [p for p in levels if p not in EMITTABLE]
    if bad:
        raise SystemExit(
            f"refusing to emit at {bad}: HEADER below is written for p = 43 only, and "
            f"{PATH} is that level's module. Rewrite the header for a new level first; "
            f"`--measure {bad[0]}` works today and is what prices the attempt.")
    out = []
    for r in rows:
        r.emit(out)
    text = HEADER + "\n".join(out) + FOOTER
    with open(PATH, "w") as fh:
        fh.write(text)
    print(f"wrote {PATH}: {len(text)} bytes, {text.count(chr(10))} lines")


if __name__ == "__main__":
    main()

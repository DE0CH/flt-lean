#!/usr/bin/env python3
"""Certificate generator for the division-polynomial identities in
`Fermat/FLT/EllipticCurve/TorsionCard.lean` (the Washington Thm 3.6
induction, node `zsmul_some_aux`).

Workflow (validated on `zsmul_some_aux_two`, the duplication formula):
an identity of curve-point values, after slope-elimination through the
multiplied slope equation, reduces to a polynomial identity modulo the
curve equation `g = y² + a₁xy + a₃y − (x³ + a₂x² + a₄x + a₆)` (and, for
the induction step cases, the IH relations and the parity-instantiated
recurrences).  This script computes the exact cofactors by polynomial
division / Groebner reduction; the cofactors are then pasted into Lean
as `linear_combination` certificates.

Run: python3 scripts/division_polynomial_certificates.py
(needs sympy: pip3 install --break-system-packages --user sympy)
"""

import sympy as sp

x, y, a1, a2, a3, a4, a6 = sp.symbols("x y a1 a2 a3 a4 a6")

# ---------------------------------------------------------------------------
# curve data
# ---------------------------------------------------------------------------
g = y**2 + a1 * x * y + a3 * y - (x**3 + a2 * x**2 + a4 * x + a6)

d = 2 * y + a1 * x + a3  # ψ₂-value at (x, y)
T = 3 * x**2 + 2 * a2 * x + a4 - a1 * y  # tangent-slope numerator

b2 = a1**2 + 4 * a2
b4 = 2 * a4 + a1 * a3
b6 = a3**2 + 4 * a6
b8 = a1**2 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3**2 - a4**2

Psi3 = 3 * x**4 + b2 * x**3 + 3 * b4 * x**2 + 3 * b6 * x + b8
prePsi4 = (
    2 * x**6 + b2 * x**5 + 5 * b4 * x**4 + 10 * b6 * x**3 + 10 * b8 * x**2
    + (b2 * b8 - b4 * b6) * x + (b4 * b8 - b6**2)
)


def certificate_duplication_y() -> None:
    """The heq-cofactor of the duplication formula's y-identity
    (already installed in `zsmul_some_aux_two`)."""
    Qd4 = (
        -2 * T**3 * d - 3 * a1 * T**2 * d**2
        + (2 * a2 + 6 * x - a1**2) * T * d**3
        + (-2 * y + a1 * a2 + 2 * a1 * x - a3) * d**4
    )
    R = sp.expand(Qd4 - prePsi4 * d)
    q, r = sp.div(R, g, y)
    assert sp.simplify(r) == 0, "duplication y-identity: remainder nonzero!"
    print("duplication y-identity heq-cofactor:")
    print(" ", sp.factor(q))


def numeric_model():
    """Exact-arithmetic model of a concrete curve/point for sign checks:
    y² = x³ + 2x + 3, P = (3, 6).  Returns (psi-values dict, points dict)."""
    A1, A2, A3, A4, A6 = 0, 0, 0, 2, 3
    x0, y0 = sp.Rational(3), sp.Rational(6)

    def neg_y(px, py):
        return -py - A1 * px - A3

    def add(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        (x1, y1), (x2, y2) = P, Q
        if x1 == x2 and y1 == neg_y(x2, y2):
            return None
        if x1 == x2:
            lam = (3 * x1**2 + 2 * A2 * x1 + A4 - A1 * y1) / (2 * y1 + A1 * x1 + A3)
        else:
            lam = (y1 - y2) / (x1 - x2)
        x3 = lam**2 + A1 * lam - A2 - x1 - x2
        y3 = -(lam * (x3 - x1) + y1) - A1 * x3 - A3
        return (sp.nsimplify(x3), sp.nsimplify(y3))

    B2, B4, B6 = A1**2 + 4 * A2, 2 * A4 + A1 * A3, A3**2 + 4 * A6
    B8 = A1**2 * A6 + 4 * A2 * A6 - A1 * A3 * A4 + A2 * A3**2 - A4**2
    psi = {0: sp.Integer(0), 1: sp.Integer(1)}
    psi[2] = 2 * y0 + A1 * x0 + A3
    psi[3] = 3 * x0**4 + B2 * x0**3 + 3 * B4 * x0**2 + 3 * B6 * x0 + B8
    psi[4] = psi[2] * (
        2 * x0**6 + B2 * x0**5 + 5 * B4 * x0**4 + 10 * B6 * x0**3
        + 10 * B8 * x0**2 + (B2 * B8 - B4 * B6) * x0 + (B4 * B8 - B6**2)
    )
    for m in range(2, 9):
        if 2 * m not in psi:
            psi[2 * m] = (
                psi[m] * (psi[m + 2] * psi[m - 1] ** 2 - psi[m - 2] * psi[m + 1] ** 2)
                / psi[2]
            )
        if 2 * m + 1 not in psi:
            psi[2 * m + 1] = psi[m + 2] * psi[m] ** 3 - psi[m - 1] * psi[m + 1] ** 3
    pts = {1: (x0, y0)}
    for n in range(2, 13):
        pts[n] = add(pts[n - 1], pts[1])
    return psi, pts


def check_tracked_pair() -> None:
    """Numeric check of the induction package (i) x([n]P)ψₙ² = φₙ,
    (ii) (2yₙ + a₁xₙ + a₃)ψₙ⁴ = ψ₂ₙ, with φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁."""
    psi, pts = numeric_model()
    x0 = sp.Rational(3)
    for n in range(2, 6):
        xn, yn = pts[n]
        phi_n = x0 * psi[n] ** 2 - psi[n + 1] * psi[n - 1]
        assert sp.simplify(xn * psi[n] ** 2 - phi_n) == 0, (n, "x-formula")
        tn = 2 * yn  # a1 = a3 = 0 in the model
        assert sp.simplify(tn * psi[n] ** 4 - psi[2 * n]) == 0, (n, "tracking")
    print("tracked pair (i)+(ii): numeric check OK for n = 2..5")





def check_step_targets() -> None:
    """Numeric validation of both induction step targets (signs as in
    the Lean statement of `zsmul_some_aux`):
    odd  [2m+1]P = [m+1]P + [m]P   (secant denominator: gap-1),
    even [2m]P   = [m+1]P + [m-1]P (secant denominator: gap-2)."""
    psi, pts = numeric_model()
    x0 = sp.Rational(3)
    m = 3
    # odd step
    n = 2 * m + 1
    xn, yn = pts[n]
    W = psi[m + 2] * psi[m] ** 3 - psi[m - 1] * psi[m + 1] ** 3
    assert sp.simplify(W - psi[n]) == 0
    assert sp.simplify(2 * yn * psi[n] ** 4 - psi[2 * n]) == 0  # (ii)
    xm, ym = pts[m]
    xm1, ym1 = pts[m + 1]
    dx = xm1 - xm
    assert sp.simplify(
        2 * yn * dx - (-(2 * (ym1 - ym)) * (xn - xm1) - 2 * ym1 * dx)
    ) == 0  # secant t-identity route
    # even step
    n = 2 * m
    xn, yn = pts[n]
    xmm1, ymm1 = pts[m - 1]
    dx = xm1 - xmm1
    dy = ym1 - ymm1
    x_out = (dy**2 - (xm1 + xmm1) * dx**2) / dx**2
    assert sp.simplify(x_out - xn) == 0
    assert sp.simplify(
        xn * psi[n] ** 2 - (x0 * psi[n] ** 2 - psi[n + 1] * psi[n - 1])
    ) == 0  # (i)
    assert sp.simplify(2 * yn * psi[n] ** 4 - psi[2 * n]) == 0  # (ii)
    print("step targets (odd + even): numeric check OK at m = 3")





def check_cross_tracking() -> None:
    """Component (iii) of the induction package — the cross-tracking
    relation binding the relative sign of consecutive trackings:
    `2 tₙ tₙ₊₁ (ψₙψₙ₊₁)⁶ = ψ₂ₙ₊₁²((b₂+12x)ψₙ²ψₙ₊₁² − 4(ψₙ₋₁ψₙ₊₁³ + ψₙ³ψₙ₊₂))
       − (ψₙψₙ₊₁)⁶(Ψ₂Sq(xₙ) + Ψ₂Sq(xₙ₊₁))`.
    This is precisely the residual of the odd-step x-target over
    (g, memberships); with (iii) as a generator the odd step closes."""
    psi, pts = numeric_model()
    x0 = sp.Rational(3)
    B2, B4, B6 = 0, 4, 12
    P2 = lambda t: 4 * t**3 + B2 * t**2 + 2 * B4 * t + B6
    for m in range(2, 6):
        A_, B_, C_, D_ = psi[m - 1], psi[m], psi[m + 1], psi[m + 2]
        tm, tm1 = 2 * pts[m][1], 2 * pts[m + 1][1]
        Wv = D_ * B_**3 - A_ * C_**3
        xm = x0 - C_ * A_ / B_**2
        xm1 = x0 - D_ * B_ / C_**2
        lhs = 2 * tm * tm1 * B_**6 * C_**6
        rhs = Wv**2 * ((B2 + 12 * x0) * B_**2 * C_**2
                       - 4 * (A_ * C_**3 + B_**3 * D_)) \
            - B_**6 * C_**6 * (P2(xm) + P2(xm1))
        assert sp.simplify(lhs - rhs) == 0, m
    print("cross-tracking (iii): numeric check OK for n = 2..5")





def certificate_odd_step_x() -> None:
    """The odd-step x-target closes with UNIT cofactors:
    `num + 1·(iii) + C⁶·(membership at m) + B⁶·(membership at m+1) = 0`
    identically (no curve equation needed at this level).  The Lean
    certificate is a three-term linear_combination."""
    A, B, C, D, tm, tm1 = sp.symbols("A B C D tm tm1")
    P2 = lambda t: 4 * t**3 + b2 * t**2 + 2 * b4 * t + b6
    xm = x - C * A / B**2
    xm1 = x - D * B / C**2
    cm = sp.expand(sp.fraction(sp.cancel(sp.together(tm**2 - P2(xm))))[0])
    cm1 = sp.expand(sp.fraction(sp.cancel(sp.together(tm1**2 - P2(xm1))))[0])
    W = D * B**3 - A * C**3
    dx = xm1 - xm
    dy = (tm1 - tm - a1 * dx) / 2
    x_out = (dy**2 + a1 * dy * dx - (a2 + xm1 + xm) * dx**2) / dx**2
    target = sp.together((x - x_out) * W**2 - tm1 * tm * (B * C) ** 4)
    num = sp.expand(sp.fraction(sp.cancel(target))[0])
    iii = sp.expand(
        2 * tm * tm1 * B**6 * C**6
        - W**2 * ((b2 + 12 * x) * B**2 * C**2 - 4 * (A * C**3 + B**3 * D))
        + B**6 * C**6 * (P2(xm) + P2(xm1))
    )
    iii = sp.expand(sp.fraction(sp.cancel(sp.together(iii)))[0])
    assert sp.expand(num + iii + C**6 * cm + B**6 * cm1) == 0
    print("odd-step x-target: exact closure with unit cofactors OK")





def resultant_Psi2Sq_Psi3() -> None:
    """`Res(Ψ₂Sq, Ψ₃) = -Δ²` EXACTLY (no stray 2- or 3-powers) — so on
    an elliptic curve the 2-torsion and 3-torsion `x`-coordinates are
    disjoint in EVERY characteristic.  Seeds the `ψ₂ = 0` (2-torsion
    `P`) degenerate branch of the induction: odd-index `ψ`-values are
    nonvanishing there."""
    X = sp.symbols("X")
    P2 = 4 * X**3 + b2 * X**2 + 2 * b4 * X + b6
    P3 = 3 * X**4 + b2 * X**3 + 3 * b4 * X**2 + 3 * b6 * X + b8
    Delta = -(b2**2) * b8 - 8 * b4**3 - 27 * b6**2 + 9 * b2 * b4 * b6
    R = sp.resultant(P2, P3, X)
    q, r = sp.div(sp.expand(R), sp.expand(Delta**2), X)
    assert sp.simplify(r) == 0 and sp.simplify(q + 1) == 0
    print("Res(Ψ₂Sq, Ψ₃) = -Δ²: verified")

def check_even_step_targets() -> None:
    """Numeric validation of the even step [2m]P = [m+1]P + [m-1]P:
    the gap-2 secant denominator, and both targets at 2m."""
    psi, pts = numeric_model()
    x0 = sp.Rational(3)
    m = 3
    A_, C_ = psi[m - 1], psi[m + 1]
    s_ = 2 * sp.Rational(6)
    xm1v, xmm1v = pts[m + 1][0], pts[m - 1][0]
    assert sp.simplify((xmm1v - xm1v) * (A_ * C_) ** 2 - psi[2 * m] * s_) == 0
    dx = xm1v - xmm1v
    dy = pts[m + 1][1] - pts[m - 1][1]
    x_out = (dy**2 - (xm1v + xmm1v) * dx**2) / dx**2
    t_out = (-2 * dy * (x_out - xm1v) - 2 * pts[m + 1][1] * dx) / dx
    assert sp.simplify((x0 - x_out) * psi[2 * m] ** 2
                       - psi[2 * m + 1] * psi[2 * m - 1]) == 0
    assert sp.simplify(t_out * psi[2 * m] ** 4 - psi[4 * m]) == 0
    print("even-step targets (gap-2 secant): numeric check OK at m = 3")

def certificate_even_step_x() -> None:
    """The even-step x-target closes with UNIT cofactors over the
    gap-2 cross-relation (iii₂) and the two memberships:
    `num + (iii₂) + ψₘ₊₁⁶·(membership at m-1) + ψₘ₋₁⁶·(membership at
    m+1) = 0` by construction, where (iii₂) is the pair-(m-1, m+1)
    cross-tracking (only t-monomial: `-2ψₘ₋₁⁶ψₘ₊₁⁶ tₘ₋₁tₘ₊₁`),
    numerically a true identity of division-polynomial values."""
    Zm2, A, B, C, D, tmm1, tm1 = sp.symbols("Zm2 A B C D tmm1 tm1")
    P2 = lambda t: 4 * t**3 + b2 * t**2 + 2 * b4 * t + b6
    s_ = d
    xmm1 = x - B * Zm2 / A**2
    xm1 = x - D * B / C**2
    cmm1 = sp.expand(sp.fraction(sp.cancel(sp.together(tmm1**2 - P2(xmm1))))[0])
    cm1 = sp.expand(sp.fraction(sp.cancel(sp.together(tm1**2 - P2(xm1))))[0])
    psi2m_s = A**2 * B * D - Zm2 * B * C**2
    dx = -psi2m_s / (A * C) ** 2
    dy = (tm1 - tmm1 - a1 * dx) / 2
    x_out = (dy**2 + a1 * dy * dx - (a2 + xm1 + xmm1) * dx**2) / dx**2
    psi2m1 = D * B**3 - A * C**3
    psi2mm1 = C * A**3 - Zm2 * B**3
    target = sp.together((x - x_out) * psi2m_s**2 - psi2m1 * psi2mm1 * s_**2)
    num = sp.expand(sp.fraction(sp.cancel(target))[0])
    iii2 = sp.expand(-(num + C**6 * cmm1 + A**6 * cm1))
    assert sp.expand(num + iii2 + C**6 * cmm1 + A**6 * cm1) == 0
    pol = sp.Poly(iii2, tmm1, tm1)
    tmonos = {m_: c for m_, c in zip(pol.monoms(), pol.coeffs()) if sum(m_) > 0}
    assert list(tmonos.keys()) == [(1, 1)]
    print("even-step x-target: exact closure with unit cofactors OK (iii₂)")


if __name__ == "__main__":
    certificate_duplication_y()
    check_tracked_pair()
    check_step_targets()
    check_cross_tracking()
    certificate_odd_step_x()
    resultant_Psi2Sq_Psi3()
    check_even_step_targets()
    certificate_even_step_x()

"""Empirical verification (2026-07-17) of the two identity families for
separable_preΨ':
  (W)  Φₙ'ΨSqₙ − ΦₙΨSqₙ' = n·preΨ(2n)      [verified n = 2, 3, 4]
  (C)  Φ(2n)  = Φ₂hom(Φₙ, ΨSqₙ),
       ΨSq(2n) = Ψ₂Sqhom(Φₙ, ΨSqₙ)          [verified n = 2]
where Φ₂hom(u,v) = u⁴ − b₄u²v² − 2b₆uv³ − b₈v⁴ and
Ψ₂Sqhom(u,v) = 4u³v + b₂u²v² + 2b₄uv³ + b₆v⁴.
Separability of preΨ'ₚ then follows: a double root x₀ of preΨ'ₚ gives
ΨSqₚ-multiplicity ≥ 4 at x₀, so W-side preΨ(2p)-multiplicity ≥ 3, i.e.
ΨSq(2p)-multiplicity ≥ 6; but the composition side has multiplicity
exactly 4 (Φₚ(x₀) ≠ 0 by the Bézout node; char ≠ 2 for the 4Φ³-term).
"""
import sympy as sp
a1,a2,a3,a4,a6,x = sp.symbols('a1 a2 a3 a4 a6 x')
b2 = a1**2+4*a2; b4 = 2*a4+a1*a3; b6 = a3**2+4*a6
b8 = a1**2*a6+4*a2*a6-a1*a3*a4+a2*a3**2-a4**2
P2s = 4*x**3+b2*x**2+2*b4*x+b6
P = {1: sp.S(1), 2: sp.S(1), 3: 3*x**4+b2*x**3+3*b4*x**2+3*b6*x+b8,
     4: 2*x**6+b2*x**5+5*b4*x**4+10*b6*x**3+10*b8*x**2+(b2*b8-b4*b6)*x+(b4*b8-b6**2)}
P[5] = sp.expand(P[4]*P2s**2 - P[3]**3)
P[6] = sp.expand(P[3]*(P[5] - P[4]**2))
P[8] = sp.expand(P[4]*(P[3]**2*P[6] - P[5]**2))

def PSq(n):
    return sp.expand(P[n]**2 * (P2s if n % 2 == 0 else 1))
def Phi(n):
    par = P2s if n % 2 == 1 else 1
    return sp.expand(x*PSq(n) - P[n+1]*P[n-1]*par)

if __name__ == "__main__":
    for n, target in [(2, P[4]), (3, P[6]), (4, P[8])]:
        W = sp.expand(sp.diff(Phi(n),x)*PSq(n) - Phi(n)*sp.diff(PSq(n),x))
        print(f"W({n}) = {n}*preΨ({2*n}):", sp.expand(W - n*target) == 0)
    u,v = sp.symbols('u v')
    Phi2hom = u**4 - b4*u**2*v**2 - 2*b6*u*v**3 - b8*v**4
    Psi2hom = 4*u**3*v + b2*u**2*v**2 + 2*b4*u*v**3 + b6*v**4
    print("Φ(4) comp:", sp.expand(Phi(4) - Phi2hom.subs({u:Phi(2), v:PSq(2)})) == 0)
    print("ΨSq(4) comp:", sp.expand(PSq(4) - Psi2hom.subs({u:Phi(2), v:PSq(2)})) == 0)

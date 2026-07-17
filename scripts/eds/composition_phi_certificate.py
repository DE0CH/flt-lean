import sympy as sp
x,b2,b4,b6,b8,b,c,d = sp.symbols('x b2 b4 b6 b8 b c d')
w = sp.symbols('w0:5'); q = sp.Symbol('q'); r = sp.Symbol('r')  # q = W(2n), r = φ₂ₙ-value
def W(j): return w[j+2]
phi = x*W(0)**2 - W(1)*W(-1)
Phi2hom = phi**4 - b4*phi**2*W(0)**4 - 2*b6*phi*W(0)**6 - b8*W(0)**8
# Φ-side value-claim: φ(2n)-value·1 = Φ₂hom(φₙ, ψₙ²) with φ(2n) = x·q² − W(2n+1)W(2n−1)...
# φ(2n) needs the (2n±1)-window — WIDER. Instead use the x-formula-composition directly:
# x_{2n}·q² = φ₂ₙ and x_{2n} = x₂(x_n): φ₂ₙ·Ψ₂Sqhom = Φ₂hom·q²:
Psi2hom = 4*phi**3*W(0)**2 + b2*phi**2*W(0)**4 + 2*b4*phi*W(0)**6 + b6*W(0)**8
target = sp.expand(r*Psi2hom - Phi2hom*q**2)
gens = [
  sp.expand(q*b - W(0)*(W(-1)**2*W(2) - W(-2)*W(1)**2)),
  sp.expand(W(2)*W(-2) - (b**2*W(1)*W(-1) - c*W(0)**2)),
  sp.expand(b*c*(W(-1)**2*W(2) + W(-2)*W(1)**2) -
    (W(-1)*W(0)*W(1)*(d*b+b**5) - W(0)**3*b**3*c)),
  sp.expand(b**2 - (4*x**3+b2*x**2+2*b4*x+b6)),
  sp.expand(c - (3*x**4+b2*x**3+3*b4*x**2+3*b6*x+b8)),
  sp.expand(d - (2*x**6+b2*x**5+5*b4*x**4+10*b6*x**3+10*b8*x**2+(b2*b8-b4*b6)*x+(b4*b8-b6**2))),
  sp.expand(4*b8 - (b2*b6 - b4**2)),
  # φ₂ₙ-definition-relation: r = x(2n)-formula-content: hmm r is DEFINED by x₂ₙq² = φ₂ₙ...
  # the value-level: r := φ(2n)(x,y)-value: pinned by the φ-diff at 2n: r = x·q² − W(2n+1)W(2n−1):
  # introduce s1 := W(2n+1), s2 := W(2n-1) with odd-recursion pins:
]
s1, s2 = sp.symbols('s1 s2')
gens.append(sp.expand(r - (x*q**2 - s1*s2)))
gens.append(sp.expand(s1 - (W(2)*W(0)**3 - W(-1)*W(1)**3)))
gens.append(sp.expand(s2 - (W(1)*W(-1)**3 - W(-2)*W(0)**3)))
G = sp.groebner(gens, q, r, s1, s2, *w, b, c, d, b8, order='grevlex')
print("GB size", len(G.exprs), flush=True)
res = G.reduce(target)[1]
print("Φ-side composition closes:", sp.expand(res) == 0, flush=True)

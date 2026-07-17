import sympy as sp
# value-level: window W(n-2..n+2) + q := W(2n); does
#   q² = Ψ₂Sqhom(φₙ, Wₙ²)  reduce over {even-rec, T-instances, star}?
# with φₙ := x·Wₙ² − Wₙ₊₁Wₙ₋₁ and the b-invariants tied to (b,c,d) via
# the anchor?? — at the VALUE level b₂,b₄,b₆,b₈ are independent constants
# related to the seeds by: b := ψ₂v with b² = Ψ₂Sq(x) = 4x³+b₂x²+2b₄x+b₆,
# c := Ψ₃(x), d·b = ψ₄v = preΨ₄(x)·b. Use x, b2, b4, b6, b8 constants with
# relations: hb2: b^2 = 4x^3+b2*x^2+2*b4*x+b6 ; hc: c = 3x^4+b2*x^3+3*b4*x^2+3*b6*x+b8 ;
# hd: d = preΨ₄(x)  (normEDS d-slot: W₄ = d·b with ψ₄v = preΨ₄(x)·b ✓ d = preΨ₄(x));
# and 4b8 = b2*b6 - b4^2.
x,b2,b4,b6,b8,b,c,d = sp.symbols('x b2 b4 b6 b8 b c d')
w = sp.symbols('w0:5'); q = sp.Symbol('q')
def W(j): return w[j+2]
phi = x*W(0)**2 - W(1)*W(-1)
Psi2hom = 4*phi**3*W(0)**2 + b2*phi**2*W(0)**4 + 2*b4*phi*W(0)**6 + b6*W(0)**8
target = sp.expand(q**2 - Psi2hom)
gens = [
  sp.expand(q*b - W(0)*(W(-1)**2*W(2) - W(-2)*W(1)**2)),                     # even-rec
  sp.expand(W(2)*W(-2) - (b**2*W(1)*W(-1) - c*W(0)**2)),                    # T(n,2)
  sp.expand(b*c*(W(-1)**2*W(2) + W(-2)*W(1)**2) -
    (W(-1)*W(0)*W(1)*(d*b+b**5) - W(0)**3*b**3*c)),                          # star
  sp.expand(b**2 - (4*x**3+b2*x**2+2*b4*x+b6)),                              # membership
  sp.expand(c - (3*x**4+b2*x**3+3*b4*x**2+3*b6*x+b8)),                       # c-anchor
  sp.expand(d - (2*x**6+b2*x**5+5*b4*x**4+10*b6*x**3+10*b8*x**2+(b2*b8-b4*b6)*x+(b4*b8-b6**2))),  # d-anchor
  sp.expand(4*b8 - (b2*b6 - b4**2))]                                         # b8-relation
G = sp.groebner(gens, q, *w, b, c, d, b8, order='grevlex')
print("GB size", len(G.exprs), flush=True)
r = G.reduce(target)[1]
print("composition ΨSq-side closes:", sp.expand(r) == 0, flush=True)

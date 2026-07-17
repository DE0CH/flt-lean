import sympy as sp, sys

SPEC = len(sys.argv) > 1 and sys.argv[1] == 'spec'
if SPEC:
    b,c,d = sp.Rational(3,2), sp.Rational(-5,3), sp.Rational(7,4)
else:
    b,c,d = sp.symbols('b c d')

w = sp.symbols('w0:11')          # w[i] = W_{m-5+i}
def Wm(j): return w[j+5]         # -5 <= j <= 5
W5v = d*b**4 - c**3
W6v = c*b*(d*b**4 - c**3)/b * 1  # bW6 = c*b^2*(d b^4 - c^3)/... recompute: bW6 = W3(W2^2 W5 - W0 W4^2) = c*b^2*W5v -> W6 = c*b*W5v
W6v = c*b*W5v

def F_at(k):
    W = lambda j: Wm(k+j)
    return b*c*(W(-1)**2*W(2) + W(-2)*W(1)**2) - W(-1)*W(0)*W(1)*(d*b+b**5) + W(0)**3*b**3*c
def ES2_at(k):
    W = lambda j: Wm(k+j)
    return W(2)*W(-2) - (b**2*W(1)*W(-1) - c*W(0)**2)
def ES3_at(k):
    W = lambda j: Wm(k+j)
    return W(3)*W(-3) - (c**2*W(1)*W(-1) - d*b**2*W(0)**2)
def ES4_at(k):
    W = lambda j: Wm(k+j)
    return W(4)*W(-4) - ((d*b)**2*W(1)*W(-1) - W5v*c*W(0)**2)
def ES5_at(k):
    W = lambda j: Wm(k+j)
    return W(5)*W(-5) - (W5v**2*W(1)*W(-1) - W6v*(d*b)*W(0)**2)
def Weven_b(k):
    W = lambda j: Wm(k+j)
    return W(0)*(W(-1)**2*W(2) - W(-2)*W(1)**2)
def Wodd(k):
    W = lambda j: Wm(k+j)
    return W(2)*W(0)**3 - W(-1)*W(1)**3

gens = ([F_at(k) for k in (-2,-1,0,1,2)] + [ES2_at(k) for k in (-3,-2,-1,0,1,2,3)]
        + [ES3_at(k) for k in (-2,-1,0,1,2)] + [ES4_at(k) for k in (-1,0,1)] + [ES5_at(0)])
G = sp.groebner([sp.expand(g) for g in gens], *w, order='grevlex')
print("GB done, size", len(G.exprs), flush=True)

T_Feven = sp.expand(
  b**3*c*Wodd(-1)**2*Weven_b(1) + b**3*c*Weven_b(-1)*Wodd(0)**2
  - b**2*(d*b+b**5)*Wodd(-1)*Weven_b(0)*Wodd(0) + c*Weven_b(0)**3)
r = G.reduce(T_Feven)[1]
print("F_even reduces to zero:", sp.expand(r) == 0, flush=True)

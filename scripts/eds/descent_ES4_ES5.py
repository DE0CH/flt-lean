import sympy as sp, sys

SPEC = True
b,c,d = sp.Rational(3,2), sp.Rational(-5,3), sp.Rational(7,4)

w = sp.symbols('w0:11')
def Wm(j): return w[j+5]
W5v = d*b**4 - c**3
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

targets = {}
targets['ES4_even'] = sp.expand(Weven_b(2)*Weven_b(-2) - (d*b)**2*b**2*Wodd(0)*Wodd(-1) + W5v*c*Weven_b(0)**2)
targets['ES4_odd']  = sp.expand(b**2*Wodd(2)*Wodd(-2) - (d*b)**2*Weven_b(1)*Weven_b(0) + W5v*c*b**2*Wodd(0)**2)
targets['ES5_even'] = sp.expand(b**2*Wodd(2)*Wodd(-3) - W5v**2*b**2*Wodd(0)*Wodd(-1) + W6v*d*b*Weven_b(0)**2)
targets['ES5_odd']  = sp.expand(Weven_b(3)*Weven_b(-2) - W5v**2*Weven_b(1)*Weven_b(0) + W6v*d*b**3*Wodd(0)**2)

for name, T in targets.items():
    r = G.reduce(T)[1]
    print(name, "reduces to zero:", sp.expand(r) == 0, flush=True)

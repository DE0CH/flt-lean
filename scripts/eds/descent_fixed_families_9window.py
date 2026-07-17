import sympy as sp, sys

SPEC = len(sys.argv) > 1 and sys.argv[1] == 'spec'
if SPEC:
    b,c,d = sp.Rational(3,2), sp.Rational(-5,3), sp.Rational(7,4)
else:
    b,c,d = sp.symbols('b c d')

w = sp.symbols('w0:9')          # w[i] = W_{m-4+i}
def Wm(j): return w[j+4]        # -4 <= j <= 4

def F_at(k):
    W = lambda j: Wm(k+j)
    return b*c*(W(-1)**2*W(2) + W(-2)*W(1)**2) - W(-1)*W(0)*W(1)*(d*b+b**5) + W(0)**3*b**3*c
def ES2_at(k):
    W = lambda j: Wm(k+j)
    return W(2)*W(-2) - (b**2*W(1)*W(-1) - c*W(0)**2)
def ES3_at(k):
    W = lambda j: Wm(k+j)
    return W(3)*W(-3) - (c**2*W(1)*W(-1) - d*b**2*W(0)**2)
def ES4_at(k):    # W_{m+4}W_{m-4} = W5? ES(m,4): W_{m+4}W_{m-4} = d b (b) W_{m+1}W_{m-1}... general: W_{m+4}W_{m-4} = W_{m+1}W_{m-1}W4^2 - W5 W3 W_m^2, W4 = d b, W5 = d b^4 - c^3
    W = lambda j: Wm(k+j)
    return W(4)*W(-4) - ((d*b)**2*W(1)*W(-1) - (d*b**4-c**3)*c*W(0)**2)
def Weven_b(k):
    W = lambda j: Wm(k+j)
    return W(0)*(W(-1)**2*W(2) - W(-2)*W(1)**2)
def Wodd(k):
    W = lambda j: Wm(k+j)
    return W(2)*W(0)**3 - W(-1)*W(1)**3

gens = ([F_at(k) for k in (-2,-1,0,1,2)] + [ES2_at(k) for k in (-2,-1,0,1,2)]
        + [ES3_at(k) for k in (-1,0,1)] + [ES4_at(0)])
G = sp.groebner([sp.expand(g) for g in gens], *w, order='grevlex')
print("GB done, size", len(G.exprs), flush=True)

targets = {}
targets['F_even'] = sp.expand(
  b**3*c*Wodd(-1)**2*Weven_b(1) + b**3*c*Weven_b(-1)*Wodd(0)**2
  - b**2*(d*b+b**5)*Wodd(-1)*Weven_b(0)*Wodd(0) + c*Weven_b(0)**3)
targets['F_odd'] = sp.expand(
  b*c*(Weven_b(0)**2*Wodd(1) + Wodd(-1)*Weven_b(1)**2)
  - Weven_b(0)*Wodd(0)*Weven_b(1)*(d*b+b**5) + b**5*c*Wodd(0)**3)
targets['ES2_even'] = sp.expand(Weven_b(1)*Weven_b(-1) - b**4*Wodd(0)*Wodd(-1) + c*Weven_b(0)**2)
targets['ES2_odd']  = sp.expand(b**2*Wodd(1)*Wodd(-1) - b**2*Weven_b(1)*Weven_b(0) + c*b**2*Wodd(0)**2)
targets['ES3_even'] = sp.expand(b**2*Wodd(1)*Wodd(-2) - b**2*c**2*Wodd(0)*Wodd(-1) + d*b**2*Weven_b(0)**2)
targets['ES3_odd']  = sp.expand(Weven_b(2)*Weven_b(-1) - c**2*Weven_b(1)*Weven_b(0) + d*b**4*Wodd(0)**2)

for name, T in targets.items():
    r = G.reduce(T)[1]
    print(name, "reduces to zero:", sp.expand(r) == 0, flush=True)

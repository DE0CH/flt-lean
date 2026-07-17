import sympy as sp, sys, pickle

b,c,d = sp.symbols('b c d')
w = sp.symbols('w0:9')
def Wm(j): return w[j+4]
W5v = d*b**4 - c**3

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
def Weven_b(k):
    W = lambda j: Wm(k+j)
    return W(0)*(W(-1)**2*W(2) - W(-2)*W(1)**2)
def Wodd(k):
    W = lambda j: Wm(k+j)
    return W(2)*W(0)**3 - W(-1)*W(1)**3

gens = ([F_at(k) for k in (-2,-1,0,1,2)] + [ES2_at(k) for k in (-2,-1,0,1,2)]
        + [ES3_at(k) for k in (-1,0,1)] + [ES4_at(0)])
gnames = (['F(%+d)'%k for k in (-2,-1,0,1,2)] + ['ES2(%+d)'%k for k in (-2,-1,0,1,2)]
        + ['ES3(%+d)'%k for k in (-1,0,1)] + ['ES4(0)'])
gens = [sp.expand(g) for g in gens]

targets = {}
targets['F_odd'] = sp.expand(
  b*c*(Weven_b(0)**2*Wodd(1) + Wodd(-1)*Weven_b(1)**2)
  - Weven_b(0)*Wodd(0)*Weven_b(1)*(d*b+b**5) + b**5*c*Wodd(0)**3)
targets['ES2_even'] = sp.expand(Weven_b(1)*Weven_b(-1) - b**4*Wodd(0)*Wodd(-1) + c*Weven_b(0)**2)
targets['ES2_odd']  = sp.expand(b**2*Wodd(1)*Wodd(-1) - b**2*Weven_b(1)*Weven_b(0) + c*b**2*Wodd(0)**2)
targets['ES3_even'] = sp.expand(b**2*Wodd(1)*Wodd(-2) - b**2*c**2*Wodd(0)*Wodd(-1) + d*b**2*Weven_b(0)**2)
targets['ES3_odd']  = sp.expand(Weven_b(2)*Weven_b(-1) - c**2*Weven_b(1)*Weven_b(0) + d*b**4*Wodd(0)**2)

out = {}
for name, T in targets.items():
    qs, r = sp.reduced(T, gens, *w, order='grevlex')
    ok = sp.expand(r) == 0
    print(name, "division remainder zero:", ok, flush=True)
    if ok:
        out[name] = {gnames[i]: qs[i] for i in range(len(gens)) if qs[i] != 0}
        print("  cofactor sizes:", {k: sp.count_ops(v) for k,v in out[name].items()}, flush=True)
with open('/private/tmp/claude-501/-Users-deyaochen-cs-flt-worktree/3d8b6476-90a3-459f-86ed-54317f8342e9/scratchpad/certs.pkl','wb') as f:
    pickle.dump({k:{g:sp.srepr(v) for g,v in vv.items()} for k,vv in out.items()}, f)
print("saved")

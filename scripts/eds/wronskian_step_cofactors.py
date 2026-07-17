import sympy as sp

x1,y1,xn,yn,l,L,a1,a2,a3,a4,a6,n = sp.symbols('x1 y1 xn yn l L a1 a2 a3 a4 a6 n')
E1 = y1**2 + a1*x1*y1 + a3*y1 - x1**3 - a2*x1**2 - a4*x1 - a6
En = yn**2 + a1*xn*yn + a3*yn - xn**3 - a2*xn**2 - a4*xn - a6
d  = xn - x1
mu = yn - y1
R3 = l*d - mu
s  = lambda x,y: 2*y + a1*x + a3
fx = lambda x,y: a1*y - (3*x**2 + 2*a2*x + a4)
DKx1 = s(x1,y1); DKy1 = -fx(x1,y1)
DKxn = n*s(xn,yn); DKyn = -n*fx(xn,yn)
nu = (DKyn - DKy1) - l*(DKxn - DKx1)
R5 = L*d - nu
x3 = l**2 + a1*l - a2 - xn - x1
DKx3 = 2*l*L + a1*L - DKxn - DKx1
y3 = -(l*(x3-xn) + yn) - a1*x3 - a3
DKy3 = -(L*(x3-xn) + l*(DKx3-DKxn) + DKyn) - a1*DKx3
GA = sp.expand(DKx3 - (n+1)*s(x3,y3))
GB = sp.expand(DKy3 + (n+1)*fx(x3,y3))

def certify(T0, name):
    # step 1: T0 is L-linear: T0 = AL*L + A0
    PT = sp.Poly(T0, L)
    assert PT.degree() <= 1
    AL = PT.coeff_monomial(L) if PT.degree()==1 else sp.Integer(0)
    A0 = PT.coeff_monomial(1)
    # d*T0 = AL*(L*d) + A0*d = AL*R5 + AL*nu + A0*d
    T1 = sp.expand(AL*nu + A0*d)   # == d*T0 - AL*R5
    q5 = AL
    # step 2: clear l from T1: T1 = sum c_j l^j, degree D
    P1 = sp.Poly(T1, l)
    Dg = P1.degree()
    # d^Dg * T1 = sum c_j (l*d)^j d^(Dg-j)
    #           = sum c_j (mu + R3)^j d^(Dg-j)
    # cofactor of R3: sum_j c_j * d^(Dg-j) * ((l*d)^j - mu^j)/R3
    q3 = sp.Integer(0); T2 = sp.Integer(0)
    for j in range(Dg+1):
        cj = P1.coeff_monomial(l**j) if j>0 else P1.coeff_monomial(1)
        if cj == 0: continue
        # (l*d)^j - mu^j = R3 * sum_{i<j} (l*d)^i mu^(j-1-i)
        geom = sum((l*d)**i * mu**(j-1-i) for i in range(j)) if j>0 else 0
        q3 += cj * d**(Dg-j) * geom
        T2 += cj * d**(Dg-j) * mu**j
    T2 = sp.expand(T2)
    # d^(Dg+1)*T0 = d^Dg*AL*R5 + q3*R3 + T2
    # step 3: reduce T2 mod [E1,En] (disjoint variables -> GB)
    q,r = sp.reduced(T2, [E1,En], gens=[y1,yn,x1,xn], order='grevlex')
    assert sp.simplify(r)==0, (name, "residual", r)
    total = sp.expand(d**(Dg+1)*T0 - (d**Dg*AL*R5 + q3*R3 + q[0]*E1 + q[1]*En))
    assert total == 0, (name, "total check failed")
    print(f"== {name}: d^{Dg+1} * T = qE1*E1 + qEn*En + q3*R3 + q5*R5, K={Dg+1}")
    return dict(K=Dg+1, qE1=sp.expand(q[0]), qEn=sp.expand(q[1]),
                q3=sp.expand(q3), q5=sp.expand(d**Dg*AL))

import pickle
res = {}
for nm,T in (("A",GA),("B",GB)):
    res[nm] = certify(T, nm)
pickle.dump(res, open('/private/tmp/claude-501/-Users-deyaochen-cs-flt-worktree/3d8b6476-90a3-459f-86ed-54317f8342e9/scratchpad/step_cofs.pkl','wb'))
for nm in res:
    for k,v in res[nm].items():
        if k=='K': print(nm,'K =',v); continue
        print(nm, k, 'nterms =', len(sp.Add.make_args(v)))

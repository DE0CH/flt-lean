import sympy as sp

x1,y1,l,L,a1,a2,a3,a4,a6 = sp.symbols('x1 y1 l L a1 a2 a3 a4 a6')
E1 = y1**2 + a1*x1*y1 + a3*y1 - x1**3 - a2*x1**2 - a4*x1 - a6
s1  = 2*y1 + a1*x1 + a3
fx1 = a1*y1 - (3*x1**2 + 2*a2*x1 + a4)
# tangent slope: l * s1 = -fx1  (mathlib: slope = (3x²+2a₂x+a₄−a₁y)/(2y+a₁x+a₃) = -fx1/s1)
R3 = l*s1 + fx1
# DK values at base: DKx1 = s1, DKy1 = -fx1
DKx1 = s1; DKy1 = -fx1
# numerator num := -fx1 = 3x²+2a₂x+a₄−a₁y : DK(num) = (6x1+2a2)*DKx1 - a1*DKy1
DKnum = (6*x1+2*a2)*DKx1 - a1*DKy1
DKden = 2*DKy1 + a1*DKx1
# cleared quotient rule: L*s1 = DKnum - l*DKden
R5 = L*s1 - (DKnum - l*DKden)
x3 = l**2 + a1*l - a2 - 2*x1
DKx3 = 2*l*L + a1*L - 2*DKx1
y3 = -(l*(x3-x1) + y1) - a1*x3 - a3
DKy3 = -(L*(x3-x1) + l*(DKx3-DKx1) + DKy1) - a1*DKx3
s  = lambda x,y: 2*y + a1*x + a3
fx = lambda x,y: a1*y - (3*x**2 + 2*a2*x + a4)
GA = sp.expand(DKx3 - 2*s(x3,y3))
GB = sp.expand(DKy3 + 2*fx(x3,y3))

def certify(T0, name):
    PT = sp.Poly(T0, L)
    assert PT.degree() <= 1
    AL = PT.coeff_monomial(L) if PT.degree()==1 else sp.Integer(0)
    A0 = PT.coeff_monomial(1)
    # s1*T0 = AL*(L*s1) + A0*s1 = AL*R5 + AL*nu + A0*s1
    nu = DKnum - l*DKden
    T1 = sp.expand(AL*nu + A0*s1)
    P1 = sp.Poly(T1, l)
    Dg = P1.degree()
    q3 = sp.Integer(0); T2 = sp.Integer(0)
    mu = -fx1
    for j in range(Dg+1):
        cj = P1.coeff_monomial(l**j) if j>0 else P1.coeff_monomial(1)
        if cj == 0: continue
        geom = sum((l*s1)**i * mu**(j-1-i) for i in range(j)) if j>0 else 0
        q3 += cj * s1**(Dg-j) * geom
        T2 += cj * s1**(Dg-j) * mu**j
    T2 = sp.expand(T2)
    q,r = sp.reduced(T2, [E1], gens=[y1,x1], order='grevlex')
    assert sp.simplify(r)==0, (name, "residual", sp.factor(r))
    q0 = q[0] if q else sp.Integer(0)
    total = sp.expand(s1**(Dg+1)*T0 - (s1**Dg*AL*R5 + q3*R3 + q0*E1))
    assert total == 0, (name,"total")
    print(f"== {name}: s1^{Dg+1} * T = qE1*E1 + q3*R3 + q5*R5")
    return dict(K=Dg+1, qE1=sp.expand(q0), q3=sp.expand(q3), q5=sp.expand(s1**Dg*AL))

import pickle
res={}
for nm,T in (("A",GA),("B",GB)):
    res[nm]=certify(T,nm)
pickle.dump(res, open('/private/tmp/claude-501/-Users-deyaochen-cs-flt-worktree/3d8b6476-90a3-459f-86ed-54317f8342e9/scratchpad/doubling_cofs.pkl','wb'))
for nm in res:
    print(nm, 'K =', res[nm]['K'], {k:len(sp.Add.make_args(v)) for k,v in res[nm].items() if k!='K'})

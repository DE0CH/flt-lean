import sympy as sp, sys, itertools

# clusters: u_j = W(a+j), v_j = W(e+j), s_j = W(a+e+j), t_j = W(a-e+j), j in -2..2
b = sp.Rational(3,2)   # specialized W(2); W1 = 1
u = sp.symbols('u_m2 u_m1 u_0 u_p1 u_p2'); v = sp.symbols('v_m2 v_m1 v_0 v_p1 v_p2')
s = sp.symbols('s_m2 s_m1 s_0 s_p1 s_p2'); t = sp.symbols('t_m2 t_m1 t_0 t_p1 t_p2')
def U(j): return u[j+2]
def V(j): return v[j+2]
def S(j): return s[j+2]
def T_(j): return t[j+2]

# generators: T(a+j, e+j') for |j+j'|<=2, |j-j'|<=2
gens = []
for j in range(-2,3):
    for jp in range(-2,3):
        if abs(j+jp) <= 2 and abs(j-jp) <= 2:
            gens.append(sp.expand(S(j+jp)*T_(j-jp) - (U(j+1)*U(j-1)*V(jp)**2 - V(jp+1)*V(jp-1)*U(j)**2)))
# also T(a+j, a+j') within u-cluster? W(2a+j+j')W(j-j') = ... W(j-j') is a CONSTANT (small index) — these relate
# u-cluster to W(2a+..) which is outside our symbol set; skip. Same for v.

# target: T(2a, 2e)*b^2:
# W(2a+2e)*b = S(0)(S(-1)^2 S(2) - S(-2) S(1)^2) =: SEb
# W(2a-2e)*b = T_(0)(T_(-1)^2 T_(2) - T_(-2) T_(1)^2) =: TEb
# W(2a+1) = U(2)U(0)^3 - U(-1)U(1)^3 ; W(2a-1) = W(2(a-1)+1) = U(1)U(-1)^3 - U(-2)U(0)^3
# W(2e)*b = V(0)(V(-1)^2 V(2) - V(-2) V(1)^2) =: VEb ; W(2a)*b = UEb similarly
SEb = S(0)*(S(-1)**2*S(2) - S(-2)*S(1)**2)
TEb = T_(0)*(T_(-1)**2*T_(2) - T_(-2)*T_(1)**2)
UEb = U(0)*(U(-1)**2*U(2) - U(-2)*U(1)**2)
VEb = V(0)*(V(-1)**2*V(2) - V(-2)*V(1)**2)
Wo_a_p = U(2)*U(0)**3 - U(-1)*U(1)**3
Wo_a_m = U(1)*U(-1)**3 - U(-2)*U(0)**3
Wo_e_p = V(2)*V(0)**3 - V(-1)*V(1)**3
Wo_e_m = V(1)*V(-1)**3 - V(-2)*V(0)**3

# T(2a,2e): W(2a+2e)W(2a-2e) - [W(2a+1)W(2a-1)W(2e)^2 - W(2e+1)W(2e-1)W(2a)^2]  ; multiply by b^2
target = sp.expand(SEb*TEb - (Wo_a_p*Wo_a_m*VEb**2 - Wo_e_p*Wo_e_m*UEb**2))

allv = list(u)+list(v)+list(s)+list(t)
G = sp.groebner(gens, *allv, order='grevlex')
print("GB size", len(G.exprs), flush=True)
r = G.reduce(target)[1]
print("T even-even descent closes:", sp.expand(r)==0, flush=True)

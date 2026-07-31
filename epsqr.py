def isqr(x,q): return pow(x,(q-1)//2,q)==1 or x%q==0
def find():
    res=[]
    for q in range(5,400):
        # primality
        if any(q%d==0 for d in range(2,int(q**0.5)+1)): continue
        if q%4!=1: continue   # need -1 a QR so that both eps and -eps are non-residues
        for r in range(q):
            if (r*r*r+2*r*r+4*r+2)%q==0:
                v=(1+r)%q
                if v==0: continue
                if not isqr(v,q) and not isqr((-v)%q,q):
                    res.append((q,r,v))
    return res
out=find()
print("primes q ≡ 1 mod 4 with a root r of X^3+2X^2+4X+2 and eps=1+r a non-residue (so -eps too):")
for q,r,v in out[:15]: print(f"  q={q}  r={r}  phi(eps)={v}")

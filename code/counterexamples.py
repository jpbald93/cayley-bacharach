"""Independent check of the F4, F5, F7 counterexamples (paper, Example 11).
Exhaustive evaluation over P^2(F_q); prints common zeros and ranks, then a sparse H."""
import itertools
# generic finite field: prime p or F4
def mkF(q):
    if q==4:
        # elements 0,1,2=w,3=w+1 ; add = xor ; mul table
        def mul(a,b):
            # polynomial mult mod w^2+w+1
            r=0
            for i in range(2):
                if (b>>i)&1: r^=a<<i
            if r&4: r^=0b111
            return r
        add=lambda a,b:a^b; neg=lambda a:a
        inv=lambda a:[x for x in range(4) if mul(a,x)==1][0]
        return list(range(4)),add,mul,neg,inv
    p=q
    return list(range(p)),lambda a,b:(a+b)%p,lambda a,b:(a*b)%p,lambda a:(-a)%p,lambda a:pow(a,p-2,p)
def run(q,F,G):
    E,add,mul,neg,inv=mkF(q)
    def ev(C,v):
        x,y,z=v
        mons=[(3,0,0),(2,1,0),(2,0,1),(1,2,0),(1,1,1),(1,0,2),(0,3,0),(0,2,1),(0,1,2),(0,0,3)]
        s=0
        for c,(a,b,cc) in zip(C,mons):
            t=c
            for _ in range(a): t=mul(t,x)
            for _ in range(b): t=mul(t,y)
            for _ in range(cc): t=mul(t,z)
            s=add(s,t)
        return s,[ (lambda a,b,cc: (lambda t:t)(0))(0,0,0)]
    mons=[(3,0,0),(2,1,0),(2,0,1),(1,2,0),(1,1,1),(1,0,2),(0,3,0),(0,2,1),(0,1,2),(0,0,3)]
    def mv(v):
        out=[]
        for (a,b,c) in mons:
            t=1
            for _ in range(a): t=mul(t,v[0])
            for _ in range(b): t=mul(t,v[1])
            for _ in range(c): t=mul(t,v[2])
            out.append(t)
        return out
    def e(C,v):
        s=0
        for c,m in zip(C,mv(v)): s=add(s,mul(c,m))
        return s
    pts=[]
    for v in itertools.product(E,repeat=3):
        if v==(0,0,0): continue
        # normalize: first nonzero =1
        i=[k for k in range(3) if v[k]][0]
        if v[i]!=1: continue
        pts.append(v)
    Z=[v for v in pts if e(F,v)==0 and e(G,v)==0]
    def rank(rows):
        rows=[r[:] for r in rows]; r=0
        for c in range(10):
            piv=[i for i in range(r,len(rows)) if rows[i][c]]
            if not piv: continue
            rows[r],rows[piv[0]]=rows[piv[0]],rows[r]
            iv=inv(rows[r][c]); rows[r]=[mul(iv,x) for x in rows[r]]
            for i in range(len(rows)):
                if i!=r and rows[i][c]:
                    f=rows[i][c]; rows[i]=[add(x,neg(mul(f,y))) for x,y in zip(rows[i],rows[r])]
            r+=1
        return r
    print("q",q,"common zeros",len(Z),Z)
    for k in range(len(Z)):
        others=[Z[j] for j in range(len(Z)) if j!=k]
        r8=rank([mv(v) for v in others]); r9=rank([mv(v) for v in Z])
        print("  omit",Z[k],"rank8",r8,"rank9",r9,"fails" if r9>r8 else "ok")
run(4,[0,0,1,0,0,1,0,3,2,1],[0,0,1,0,0,3,0,1,3,0])
# q=5 F=z(x+2y+3z)(x+2z), G=z(x+3y+2z)(x+y) -- build coefficients via polynomial mult
def polymul(q,lins):
    E,add,mul,neg,inv=mkF(q)
    from collections import defaultdict
    P={(0,0,0):1}
    for l in lins:
        N=defaultdict(int)
        for m,c in P.items():
            for i in range(3):
                mm=list(m); mm[i]+=1; mm=tuple(mm)
                N[mm]=add(N[mm],mul(c,l[i]))
        P=dict(N)
    mons=[(3,0,0),(2,1,0),(2,0,1),(1,2,0),(1,1,1),(1,0,2),(0,3,0),(0,2,1),(0,1,2),(0,0,3)]
    return [P.get(m,0) for m in mons]
print(polymul(4,[(0,0,1),(1,2,3),(1,2,2)]), polymul(4,[(0,0,1),(1,1,3),(1,1,0)]))
run(5,polymul(5,[(0,0,1),(1,2,3),(1,0,2)]),polymul(5,[(0,0,1),(1,3,2),(1,1,0)]))
run(7,polymul(7,[(0,0,1),(1,4,4),(1,4,4)]),polymul(7,[(0,0,1),(1,4,1),(0,1,2)]))
# conic example q=7: c=xz+y^2, F=z c, G = x c
def mulc(q,lin,conic):
    E,add,mul,neg,inv=mkF(q)
    from collections import defaultdict
    N=defaultdict(int)
    for m,c in conic.items():
        for i in range(3):
            mm=list(m); mm[i]+=1; N[tuple(mm)]=add(N[tuple(mm)],mul(c,lin[i]))
    mons=[(3,0,0),(2,1,0),(2,0,1),(1,2,0),(1,1,1),(1,0,2),(0,3,0),(0,2,1),(0,1,2),(0,0,3)]
    return [N.get(m,0) for m in mons]
c={(1,0,1):1,(0,2,0):1}
run(7,mulc(7,(0,0,1),c),mulc(7,(1,0,0),c))

import itertools
mons=[(3,0,0),(2,1,0),(2,0,1),(1,2,0),(1,1,1),(1,0,2),(0,3,0),(0,2,1),(0,1,2),(0,0,3)]
names=["x^3","x^2y","x^2z","xy^2","xyz","xz^2","y^3","y^2z","yz^2","z^3"]
def find(q,Z,omit):
    E,add,mul,neg,inv=mkF(q)
    def ev(C,v):
        s=0
        for c,(a,b,cc) in zip(C,mons):
            t=c
            for _ in range(a): t=mul(t,v[0])
            for _ in range(b): t=mul(t,v[1])
            for _ in range(cc): t=mul(t,v[2])
            s=add(s,t)
        return s
    others=[p for p in Z if p!=omit]
    best=None
    # search sparse cubics: up to 3 monomials
    for k in (1,2,3):
        for S in itertools.combinations(range(10),k):
            for cs in itertools.product([e for e in E if e],repeat=k):
                C=[0]*10
                for i,c in zip(S,cs): C[i]=c
                if all(ev(C,p)==0 for p in others) and ev(C,omit)!=0:
                    return " + ".join(f"{c}*{names[i]}" for i,c in zip(S,cs))
    return None
Z4=[(0, 1, 0), (1, 0, 0), (1, 0, 2), (1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 2, 0), (1, 2, 1), (1, 3, 0)]
print("F4",find(4,Z4,(1,0,2)))
Z5=[(0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 2), (1, 1, 0), (1, 2, 0), (1, 3, 0), (1, 4, 0), (1, 4, 2)]
print("F5",find(5,Z5,(0,1,1)))
Z7=[(0, 1, 0), (1, 0, 0), (1, 1, 0), (1, 2, 0), (1, 3, 0), (1, 3, 2), (1, 4, 0), (1, 5, 0), (1, 6, 0)]
print("F7",find(7,Z7,(1,3,2)))
# F7 conic example: H = y*(xz+y^2), omit (0,1,0)
Zc=[(0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 6), (1, 2, 3), (1, 3, 5), (1, 4, 5), (1, 5, 3), (1, 6, 6)]
E,add,mul,neg,inv=mkF(7)
Hf=lambda v:(v[1]*(v[0]*v[2]+v[1]**2))%7
print([Hf(p) for p in Zc])

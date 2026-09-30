"""Stage 8 numeric check (exact Fractions): which Pappus hypotheses are needed."""
from fractions import Fraction as F
import random, itertools
random.seed(8)
def cr(a,b): return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def det(a,b,c): return dot(cr(a,b),c)
def z(v): return all(x==0 for x in v)
def rnd(): return F(random.randint(-9,9), random.randint(1,5))
def rv(): return [rnd() for _ in range(3)]
def pt_on(l):
    # random point on line l: l x w for random w
    while True:
        p=cr(l,rv())
        if not z(p): return p
def sc(v): 
    c=rnd()
    while c==0: c=rnd()
    return [c*x for x in v]
def pappus(A):
    A1,A2,A3,A4,A5,A6=A
    X=cr(cr(A1,A2),cr(A4,A5)); Y=cr(cr(A2,A3),cr(A5,A6)); Z=cr(cr(A3,A4),cr(A6,A1))
    return X,Y,Z,det(X,Y,Z)
def config(deg=None, trials=60):
    stats={'det0':0,'detne0':0}; ex=None
    for _ in range(trials):
        l=rv(); m=rv()
        if deg=='l=m': m=sc(l)
        O=cr(l,m)
        odd=[pt_on(l) for _ in range(3)]; even=[pt_on(m) for _ in range(3)]
        if deg=='A1~A3': odd[1]=sc(odd[0])
        if deg=='A1~A5': odd[2]=sc(odd[0])
        if deg=='A3~A5': odd[2]=sc(odd[1])
        if deg=='A2~A4': even[1]=sc(even[0])
        if deg=='A2~A6': even[2]=sc(even[0])
        if deg=='A4~A6': even[2]=sc(even[1])
        for k,name in enumerate(['A1','A3','A5']):
            if deg==name+'=O': odd[k]=sc(O)
        for k,name in enumerate(['A2','A4','A6']):
            if deg==name+'=O': even[k]=sc(O)
        if deg=='two_at_O': odd[0]=sc(O); even[0]=sc(O)
        A=[odd[0],even[0],odd[1],even[1],odd[2],even[2]]
        if any(z(a) for a in A): continue
        X,Y,Zp,d=pappus(A)
        P=A+[X,Y,Zp]
        hP=all(not z(cr(P[i],P[j])) for i in range(9) for j in range(i+1,9))
        Ls=[cr(A[0],A[1]),cr(A[2],A[3]),cr(A[4],A[5])]; Ms=[cr(A[1],A[2]),cr(A[3],A[4]),cr(A[5],A[0])]
        hL=all(not z(cr(a,b)) for a in Ls for b in Ms)
        hZ=dot(l,Zp)!=0 and dot(m,Zp)!=0
        key='hP=%d hL=%d hZ=%d XYZ0=%d'%(hP,hL,hZ,any(z(v) for v in (X,Y,Zp)))
        stats[key]=stats.get(key,0)+1
        if d==0: stats['det0']+=1
        else:
            stats['detne0']+=1
            if ex is None: ex=(l,m,A,X,Y,Zp,d)
    return stats,ex
cases=[None,'l=m','A1~A3','A1~A5','A3~A5','A2~A4','A2~A6','A4~A6']+[n+'=O' for n in ['A1','A2','A3','A4','A5','A6']]+['two_at_O']
for c in cases:
    s,ex=config(c)
    print(c or 'generic', s)
    if ex: print('   counterexample:', [[str(x) for x in v] for v in ex[2]], 'l=',[str(x) for x in ex[0]],'m=',[str(x) for x in ex[1]],'det=',ex[6])

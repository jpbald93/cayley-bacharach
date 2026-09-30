from fractions import Fraction as Fr
import random
def mono(v):
    x,y,z=v
    return [x**3,x*x*y,x*x*z,x*y*y,x*y*z,x*z*z,y**3,y*y*z,y*z*z,z**3]
def rank(rows):
    M=[[Fr(a) for a in r] for r in rows]; r=0
    for c in range(len(M[0])):
        p=[i for i in range(r,len(M)) if M[i][c]!=0]
        if not p: continue
        M[r],M[p[0]]=M[p[0]],M[r]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        r+=1
    return r
def conicpt(t): return (1,t,t*t)  # on y^2=xz
cases={
 "4 collinear (y=0) + 4 generic":[(1,0,1),(2,0,1),(3,0,1),(5,0,1),(1,2,3),(4,1,7),(2,5,1),(3,3,2)],
 "7 on conic y^2=xz + 1 off":[conicpt(t) for t in range(7)]+[(1,1,5)],
 "5 collinear (y=0) + 3 noncollinear":[(1,0,1),(2,0,1),(3,0,1),(5,0,1),(7,0,1),(1,2,3),(4,1,7),(2,5,1)],
 "8 on conic y^2=xz":[conicpt(t) for t in range(8)],
}
for k,v in cases.items(): print(k, "rank", rank([mono(p) for p in v]), "dim cubics through", 10-rank([mono(p) for p in v]))

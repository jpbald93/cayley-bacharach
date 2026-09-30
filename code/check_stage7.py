# Stage 7 numeric check: exact Fractions. Random hexagons on irreducible conics.
from fractions import Fraction as Fr
import random, itertools
random.seed(7)
def cross(a,b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def det3(a,b,c): return dot(cross(a,b),c)
def iszero(v): return all(x==0 for x in v)
def evalC(q,v):
    x,y,z=v; return q[0]*x*x+q[1]*x*y+q[2]*x*z+q[3]*y*y+q[4]*y*z+q[5]*z*z
def detq(q):  # symmetric matrix determinant (irreducible iff != 0 for conics)
    a,b,c,d,e,f=q
    M=[[2*a,b,c],[b,2*d,e],[c,e,2*f]]
    return det3(M[0],M[1],M[2])
def randmat():
    while True:
        M=[[Fr(random.randint(-5,5)) for _ in range(3)] for _ in range(3)]
        if det3(*M)!=0: return M
def apply(M,v): return tuple(dot(r,v) for r in M)
def inv(M):
    c=[cross(M[1],M[2]),cross(M[2],M[0]),cross(M[0],M[1])]; d=det3(*M)
    return [[c[j][i]/d for j in range(3)] for i in range(3)]
stats=dict(trials=0, collinear_triple=0, hL_fail=0, hP_fail=0, XYZ_on_q=0, det_nonzero=0, XY_prop=0)
for trial in range(3000):
    # conic x^2 - y z = 0 transformed by random projectivity; points (t, t^2, 1) and (0,1,0)
    M=randmat(); Mi=inv(M)
    ts=random.sample(range(-9,10),6)
    A=[apply(M,(Fr(t),Fr(t*t),Fr(1))) for t in ts]
    # q(v) = q0(Mi v)
    # compute q coefficients by interpolation of the quadratic form
    def q0(v): w=apply(Mi,v); return w[0]*w[0]-w[1]*w[2]
    e=[(1,0,0),(0,1,0),(0,0,1)]
    Q=[[None]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            s=tuple(e[i][k]+e[j][k] for k in range(3))
            Q[i][j]=(q0(s)-q0(e[i])-q0(e[j]))/2 if i!=j else q0(e[i])
    q=(Q[0][0],2*Q[0][1],2*Q[0][2],Q[1][1],2*Q[1][2],Q[2][2])
    assert detq(q)!=0 and all(evalC(q,a)==0 for a in A)
    stats['trials']+=1
    for i,j,k in itertools.combinations(range(6),3):
        if det3(A[i],A[j],A[k])==0: stats['collinear_triple']+=1
    L=lambda i,j: cross(A[i-1],A[j-1])
    F=[L(1,2),L(3,4),L(5,6)]; G=[L(2,3),L(4,5),L(6,1)]
    if any(iszero(cross(f,g)) for f in F for g in G): stats['hL_fail']+=1
    X=cross(L(1,2),L(4,5)); Y=cross(L(2,3),L(5,6)); Z=cross(L(3,4),L(6,1))
    P=A+[X,Y,Z]
    if any(iszero(cross(P[i],P[j])) for i,j in itertools.combinations(range(9),2)): stats['hP_fail']+=1
    if iszero(cross(X,Y)) or iszero(cross(X,Z)) or iszero(cross(Y,Z)): stats['XY_prop']+=1
    if any(evalC(q,v)==0 for v in (X,Y,Z)): stats['XYZ_on_q']+=1
    if det3(X,Y,Z)!=0: stats['det_nonzero']+=1
print(stats)
# degenerate (reducible) conic: X = Y can happen? Pappus with A1,A3,A5 on l, A2,A4,A6 on m and
# a vertex at l∩m would violate pairwise distinctness only via collinear triples; not our setting.

# ---- Why hirr is needed: line-pair conic q = x*y (lines x=0, y=0) ----
def show(name, A, q):
    L=lambda i,j: cross(A[i-1],A[j-1])
    F=[L(1,2),L(3,4),L(5,6)]; G=[L(2,3),L(4,5),L(6,1)]
    hL=all(not iszero(cross(f,g)) for f in F for g in G)
    X=cross(L(1,2),L(4,5)); Y=cross(L(2,3),L(5,6)); Z=cross(L(3,4),L(6,1))
    P=A+[X,Y,Z]
    hP=all(not iszero(cross(P[i],P[j])) for i,j in itertools.combinations(range(9),2))
    print(name, 'onq', all(evalC(q,a)==0 for a in A), 'hL', hL, 'hP', hP,
          'X,Y,Z', X, Y, Z, 'det', det3(X,Y,Z))
qxy=(0,1,0,0,0,0)
F_=lambda *v: tuple(Fr(x) for x in v)
# (a) A1,A2,A3 on x=0: L12 = L23, hL fails and X := L12 x L45 etc. still defined
show('ex_a', [F_(0,1,1),F_(0,2,1),F_(0,3,1),F_(1,0,1),F_(2,0,1),F_(3,0,1)], qxy)
# (b) Pappus-type alternating: A1,A3,A5 on x=0, A2,A4,A6 on y=0 (hL ok, q(Z)!=0 fails? check)
show('ex_b', [F_(0,1,1),F_(1,0,1),F_(0,2,1),F_(2,0,1),F_(0,3,1),F_(3,0,1)], qxy)
# (c) A1,A2,A4,A5 on x=0: L12 = L45, so X = L12 x L45 = 0 (degenerate Pascal point)
show('ex_c', [F_(0,1,1),F_(0,2,1),F_(1,0,1),F_(0,3,1),F_(0,4,1),F_(2,0,1)], qxy)

"""Explicit Stage-8 examples: l = x (x=0), m = y (y=0), O = l∩m = (0,0,1).
Odd points (0,1,t) on l, even points (1,0,s) on m. For each dropped natural hypothesis we
report which CB genericity conditions (hP, hL, Z off l∪m) fail, and det(X,Y,Z)."""
from fractions import Fraction as F
def cr(a,b): return [a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def z(v): return all(x==0 for x in v)
l=[1,0,0]; m=[0,1,0]; O=[0,0,1]
def L(t): return [0,1,t]
def M(s): return [1,0,s]
def report(name,A):
    A1,A2,A3,A4,A5,A6=A
    X=cr(cr(A1,A2),cr(A4,A5)); Y=cr(cr(A2,A3),cr(A5,A6)); Z=cr(cr(A3,A4),cr(A6,A1))
    P=A+[X,Y,Z]; names=['A1','A2','A3','A4','A5','A6','X','Y','Z']
    badP=[(names[i],names[j]) for i in range(9) for j in range(i+1,9) if z(cr(P[i],P[j]))]
    Ls=[cr(A1,A2),cr(A3,A4),cr(A5,A6)]; Ms=[cr(A2,A3),cr(A4,A5),cr(A6,A1)]
    Ln=['L12','L34','L56']; Mn=['L23','L45','L61']
    badL=[(Ln[i],Mn[j]) for i in range(3) for j in range(3) if z(cr(Ls[i],Ms[j]))]
    print(f"{name:10s} X={X} Y={Y} Z={Z} det={dot(cr(X,Y),Z)}")
    print(f"{'':10s} hP fails at {badP or '-'}; hL fails at {badL or '-'}; lZ={dot(l,Z)} mZ={dot(m,Z)}")
g=[L(1),M(2),L(3),M(5),L(-2),M(7)]
report('generic',g)
for i,j in [(0,2),(0,4),(2,4),(1,3),(1,5),(3,5)]:
    A=list(g); A[j]=[2*x for x in A[i]]; report(f'A{i+1}~A{j+1}',A)
for i in range(6):
    A=list(g); A[i]=O; report(f'A{i+1}=O',A)
# l = m: all six on x=0
report('l=m',[L(1),L(2),L(3),L(5),L(-2),L(7)])

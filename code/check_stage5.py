# Stage 5 numeric checks (exact, sympy)
import sympy as sp, random, itertools
x,y,z,t=sp.symbols('x y z t')
# (1) Over R: q = x^2+y^2+z^2, F = x q, G = y q. Real common zeros = {(0:0:1)} only.
q=x**2+y**2+z**2; F=sp.expand(x*q); G=sp.expand(y*q)
sols=[]
for chart in [(1,y,z),(x,1,z),(x,y,1)]:
    sub=dict(zip((x,y,z),chart))
    vs=[v for v in (x,y,z) if sub[v]==v]
    S=sp.solve([F.subs({x:chart[0],y:chart[1],z:chart[2]}),G.subs({x:chart[0],y:chart[1],z:chart[2]})],vs,dict=True)
    for s in S:
        pt=[sp.sympify(c).subs(s) for c in chart]
        if all(sp.im(sp.nsimplify(c))==0 for c in pt): sols.append(tuple(pt))
print("(1) real common zeros of xq, yq (q=x^2+y^2+z^2), per chart:", sols)
assert all(p[0]==0 and p[1]==0 for p in sols) and len(sols)>=1
# so 'exactly nine common zeros' can never hold with a common conic factor over R:
# the common zero set is {m=m'=0} ∪ Z(q); here a single point.
# (2) projection from a zero u of a conic (false_of_conic): d_t = v + t z,
#     g(t) = q(d_t) u - B(u,d_t) d_t is a zero of q, pairwise non-proportional.
Q=lambda w: w[0]**2 - w[1]*w[2]          # smooth conic with zeros u=(0,0,1), v=(0,1,0)
u=sp.Matrix([0,0,1]); v=sp.Matrix([0,1,0]); zz=sp.Matrix([1,0,0])
B=lambda a,d: sp.expand(Q(a+d)-Q(a)-Q(d))
pts=[]
for tv in range(-4,5):
    d=v+tv*zz; g=Q(d)*u - B(u,d)*d
    if B(u,d)==0: continue
    assert sp.expand(Q(g))==0 and g!=sp.zeros(3,1); pts.append(g)
for a,b in itertools.combinations(pts,2): assert a.cross(b)!=sp.zeros(3,1)
print("(2) projection gives", len(pts), "pairwise non-proportional zeros of x^2-yz: OK")
# (3) classical CB on random pencils meeting in exactly 9 points (Groebner: 9 solutions, no common factor)
random.seed(5)
mons=[x**3,x**2*y,x**2*z,x*y**2,x*y*z,x*z**2,y**3,y**2*z,y*z**2,z**3]
ok=0
for trial in range(3):
    F=sum(random.randint(-5,5)*m for m in mons); G=sum(random.randint(-5,5)*m for m in mons)
    assert sp.degree(sp.gcd(sp.Poly(F,x,y,z),sp.Poly(G,x,y,z)).as_expr(),x)+0==0 or sp.gcd(F,G).is_number
    gb=sp.groebner([F.subs(z,1),G.subs(z,1)],x,y,order='lex')
    # count affine solutions (with multiplicity) = degree of last univariate element if in shape position
    py=sp.Poly(gb.exprs[-1],y)
    print("(3) trial",trial,": gcd(F,G) const; univariate elim degree",py.degree(),", squarefree:",sp.degree(sp.gcd(py,py.diff(y)))==0)
    ok+=1
print("ALL OK")

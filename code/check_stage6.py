"""Stage 6 numeric sanity: Pascal / Pappus hypotheses and conclusion, exact rationals."""
import random
from fractions import Fraction as Fr
random.seed(6)

def cross(u, v):
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def dot(u, v): return sum(a*b for a, b in zip(u, v))
def det(u, v, w): return dot(u, cross(v, w))
def nz(v): return any(x != 0 for x in v)
def evalC(q, v):
    x, y, z = v
    return q[0]*x*x+q[1]*x*y+q[2]*x*z+q[3]*y*y+q[4]*y*z+q[5]*z*z
def rnd(): return Fr(random.randint(-9, 9), random.randint(1, 5))
def linMul(l, m):
    return (l[0]*m[0], l[0]*m[1]+l[1]*m[0], l[0]*m[2]+l[2]*m[0], l[1]*m[1],
            l[1]*m[2]+l[2]*m[1], l[2]*m[2])

def conic_points(q, n):
    """Rational points of q via projection from a rational point u on q."""
    # choose q through u = (0,0,1): q5 = 0
    u = (Fr(0), Fr(0), Fr(1))
    pts = [u]
    tries = 0
    while len(pts) < n:
        tries += 1
        if tries > 2000: return None  # degenerate conic (e.g. line pair through u)
        d = (rnd(), rnd(), Fr(0))
        # q(u + t d) = t*B(u,d) + t^2 q(d) -> t = -B/q(d)
        B = evalC(q, tuple(a+b for a, b in zip(u, d))) - evalC(q, u) - evalC(q, d)
        qd = evalC(q, d)
        if qd == 0: continue
        t = -B/qd
        p = tuple(a+t*b for a, b in zip(u, d))
        if nz(p) and all(nz(cross(p, r)) for r in pts): pts.append(p)
    return pts

def check(A, q, name):
    A1, A2, A3, A4, A5, A6 = A
    L = lambda a, b: cross(a, b)
    X = cross(L(A1, A2), L(A4, A5)); Y = cross(L(A2, A3), L(A5, A6)); Z = cross(L(A3, A4), L(A6, A1))
    P = [A1, A2, A3, A4, A5, A6, X, Y, Z]
    hP = all(nz(cross(P[i], P[j])) for i in range(9) for j in range(9) if i != j)
    Fs = [L(A1, A2), L(A3, A4), L(A5, A6)]; Gs = [L(A2, A3), L(A4, A5), L(A6, A1)]
    hL = all(nz(cross(f, g)) for f in Fs for g in Gs)
    inc = all(dot(l, p) == 0 for l, p in [(Fs[0], X), (Gs[1], X), (Gs[0], Y), (Fs[2], Y),
                                         (Fs[1], Z), (Gs[2], Z)])
    hq = all(evalC(q, a) == 0 for a in A)
    hqZ = evalC(q, Z) != 0
    # H = L_XY * q vanishes at 8 points, and (CB) at Z
    LXY = cross(X, Y)
    H8 = all(dot(LXY, p)*evalC(q, p) == 0 for p in P[:8])
    H9 = dot(LXY, Z)*evalC(q, Z) == 0
    concl = det(X, Y, Z) == 0
    return dict(hP=hP, hL=hL, inc=inc, hq=hq, hqZ=hqZ, H8=H8, H9=H9, concl=concl)

ok = 0
N = 300
for _ in range(N):
    q = (rnd(), rnd(), rnd(), rnd(), rnd(), Fr(0))
    A = conic_points(q, 6)
    if A is None: continue
    random.shuffle(A)
    r = check(A, q, "pascal")
    assert r["inc"] and r["hq"] and r["H8"]
    if r["hP"] and r["hL"] and r["hqZ"]:
        assert r["H9"] and r["concl"], r
        ok += 1
print(f"Pascal: {ok}/{N} random hexagons satisfy all hypotheses; conclusion det(X,Y,Z)=0 in all")

ok = 0
for _ in range(N):
    l = (rnd(), rnd(), rnd()); m = (rnd(), rnd(), rnd())
    def pt_on(line):
        while True:
            v = (rnd(), rnd(), rnd())
            p = cross(line, v)
            if nz(p): return p
    A = [pt_on(l), pt_on(m), pt_on(l), pt_on(m), pt_on(l), pt_on(m)]
    r = check(A, linMul(l, m), "pappus")
    assert r["inc"] and r["hq"] and r["H8"]
    if r["hP"] and r["hL"] and r["hqZ"]:
        assert r["H9"] and r["concl"], r
        ok += 1
print(f"Pappus: {ok}/{N} random configurations satisfy all hypotheses; conclusion holds in all")

# negative control: move A6 off the conic -> conclusion fails generically
bad = 0
for _ in range(50):
    q = (rnd(), rnd(), rnd(), rnd(), rnd(), Fr(0))
    A = conic_points(q, 6)
    if A is None: continue
    A[5] = tuple(a + Fr(1, 7) for a in A[5])
    r = check(A, q, "neg")
    if not r["concl"]: bad += 1
print(f"Negative control (A6 off conic): conclusion fails in {bad}/50")

# Degenerate case: does hL fail / hqZ fail ever for random data?

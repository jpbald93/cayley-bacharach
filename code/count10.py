"""Stage 10 brute force.
(1) Exact point counts used in ClassicalSmall.lean: for every conic q over F_p (p = 3,4,5,7,8,9)
    that has >= 2 zeros and is not (line)*(line) [i.e. no line component], #zeros == q+1.
    (Lean needs only >= q+1: `conic_points`.)  Lines have q+1 points (`line_points`).
(2) Classical CB ("exactly nine") for q = 9: random common-line and common-conic pencils,
    counting nine-point pencils and counterexamples (expected 0), plus q = 8 as a control.
"""
import itertools, random, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from brute9 import GF, points, cubmono, conmono
from classical9b import GF8, cev, has_counterexample, normal
from classical9 import mul_lin_con

class GF9(GF):
    def __init__(self):
        self.q = 9; self.els = list(range(9))   # a + b i, i^2 = -1, encoded a + 3b
        def sp(x): return x % 3, x // 3
        def mk(a, b): return a % 3 + 3 * (b % 3)
        self.add = lambda x, y: mk(sp(x)[0] + sp(y)[0], sp(x)[1] + sp(y)[1])
        self.neg = lambda x: mk(-sp(x)[0], -sp(x)[1])
        def mul(x, y):
            a, b = sp(x); c, d = sp(y); return mk(a * c - b * d, a * d + b * c)
        self.mul = mul
        self.inv = {a: next(b for b in self.els if mul(a, b) == 1) for a in self.els if a}

def lin_products(F, P):
    """all conics l*m (normalised), l, m lines"""
    S = set()
    for l in P:
        for m in P:
            c = (F.mul(l[0], m[0]), F.add(F.mul(l[0], m[1]), F.mul(l[1], m[0])),
                 F.add(F.mul(l[0], m[2]), F.mul(l[2], m[0])), F.mul(l[1], m[1]),
                 F.add(F.mul(l[1], m[2]), F.mul(l[2], m[1])), F.mul(l[2], m[2]))
            S.add(normal(F, c))
    return S

def check_counts(F, samples=None, seed=0):
    P = points(F); red = lin_products(F, P); rnd = random.Random(seed)
    if samples is None:
        it = (c for c in itertools.product(F.els, repeat=6) if any(c))
    else:
        it = (tuple(rnd.choice(F.els) for _ in range(6)) for _ in range(samples))
    bad = 0; hist = {}
    for c in it:
        if not any(c): continue
        c = normal(F, c)
        if c in red: continue
        n = sum(1 for p in P if cev(F, c, p) == 0)
        if n < 2: continue
        hist[n] = hist.get(n, 0) + 1
        if n < F.q + 1: bad += 1
    return dict(q=F.q, irreducible_conics_with_2_zeros_by_count=hist, violations=bad)

def dot(F, a, b): return F.add(F.add(F.mul(a[0], b[0]), F.mul(a[1], b[1])), F.mul(a[2], b[2]))

def cb_line(F, samples, seed=1):
    P = points(F); rnd = random.Random(seed); z = (0, 0, 1); nine = cex = 0
    for _ in range(samples):
        a = [rnd.choice(F.els) for _ in range(6)]; b = [rnd.choice(F.els) for _ in range(6)]
        FF = mul_lin_con(F, z, a); GG = mul_lin_con(F, z, b)
        if F.rank([FF, GG]) < 2: continue
        Z = [p for p in P if p[2] == 0 or (cev(F, a, p) == 0 and cev(F, b, p) == 0)]
        if len(Z) == 9:
            nine += 1
            if has_counterexample(F, Z) is not None: cex += 1
    return dict(q=F.q, case='common line', samples=samples, nine_point=nine, counterexamples=cex)

def cb_conic(F):
    P = points(F); c = (0, 0, 1, 1, 0, 0); V = [p for p in P if cev(F, c, p) == 0]
    nine = cex = 0
    for m in P:
        for m2 in P:
            if m >= m2: continue
            meet = [p for p in P if dot(F, m, p) == 0 and dot(F, m2, p) == 0]
            Z = sorted(set(V) | set(meet))
            if len(Z) != 9: continue
            nine += 1
            if has_counterexample(F, Z) is not None: cex += 1
    return dict(q=F.q, case='common conic xz+y^2', conic_points=len(V), nine_point=nine, counterexamples=cex)

if __name__ == '__main__':
    for F in [GF(3), GF(4), GF(5), GF(7)]:
        print(check_counts(F), flush=True)
    print(check_counts(GF8(), samples=40000), flush=True)
    print(check_counts(GF9(), samples=40000), flush=True)
    for F in [GF8(), GF9()]:
        print(cb_conic(F), flush=True)
        print(cb_line(F, 3000), flush=True)

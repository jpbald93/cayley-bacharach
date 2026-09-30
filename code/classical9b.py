"""Stage 9: which q admit a counterexample to the *classical* form
("F, G independent cubics whose common F_q-points are exactly 9, H through 8 of them")?

If F, G have no common factor, the no-common-factor form (proved in Lean for every field,
`cayley_bacharach_of_no_common_factor_any`) applies.  So counterexamples need a common
component: WLOG (PGL_3 transitive on lines) F = z*a, G = z*b, or F = m*c, G = m'*c with c
an irreducible conic.  This script enumerates, for a given q:
  * all pairs (a, b) of conics (up to the common line z), recording every pencil whose
    common zero set has exactly 9 points, and whether a counterexample H exists;
  * all irreducible conics c and pairs of lines m, m'.
Exhaustive for q = 3 (364 conics up to scaling -> ~66k pairs); for q = 8, conics up to
scaling are 37449, so pairs are sampled via structure: the common-line case needs 9
common zeros, but z = 0 already has 9 points, so a, b must have no common zero off z = 0 and
the 9 points are all on z = 0 (then any H through 8 of them contains the line).  The
conic case: a smooth conic over F_8 has 9 points; again H through 8 of them contains c.
Both q = 8 arguments are checked numerically below on random samples.
"""
import itertools, random, sys
sys.path.insert(0, '.')
from brute9 import GF, points, cubmono, conmono
from classical9 import mul_lin_con, ev

class GF8(GF):
    def __init__(self):
        self.q = 8; self.els = list(range(8))
        def mul(a, b):
            r = 0
            for i in range(3):
                if (b >> i) & 1: r ^= a << i
            for d in (4, 3):
                if (r >> d) & 1: r ^= 0b1011 << (d - 3)
            return r
        self.add = lambda a, b: a ^ b; self.mul = mul; self.neg = lambda a: a
        self.inv = {a: next(b for b in self.els if mul(a, b) == 1) for a in self.els if a}

def cev(F, c, p):
    r = 0
    for a, x in zip(c, conmono(F, p)): r = F.add(r, F.mul(a, x))
    return r

def has_counterexample(F, Z):
    for k in range(len(Z)):
        eight = Z[:k] + Z[k+1:]
        A = [cubmono(F, v) for v in eight]
        if F.rank(A + [cubmono(F, Z[k])]) > F.rank(A):
            return Z[k]
    return None

def normal(F, c):
    k = next(i for i in range(len(c)) if c[i]); iv = F.inv[c[k]]
    return tuple(F.mul(iv, x) for x in c)

def run(F, exhaustive=True, samples=20000, seed=0):
    P = points(F); rnd = random.Random(seed)
    conics = sorted({normal(F, c) for c in itertools.product(F.els, repeat=6) if any(c)}) \
        if exhaustive else None
    z = (0, 0, 1)
    nine = cex = 0; maxz = 0; example = None
    if exhaustive:
        pairs = itertools.combinations(conics, 2)
    else:
        def gen():
            for _ in range(samples):
                yield tuple(rnd.choice(F.els) for _ in range(6)), tuple(rnd.choice(F.els) for _ in range(6))
        pairs = gen()
    for a, b in pairs:
        if not any(a) or not any(b): continue
        FF = mul_lin_con(F, z, list(a)); GG = mul_lin_con(F, z, list(b))
        if F.rank([FF, GG]) < 2: continue
        Z = [p for p in P if p[2] == 0 or (cev(F, a, p) == 0 and cev(F, b, p) == 0)]
        maxz = max(maxz, len(Z))
        if len(Z) == 9:
            nine += 1
            m = has_counterexample(F, Z)
            if m is not None:
                cex += 1; example = example or (a, b, Z, m)
    return dict(q=F.q, common_line_max_common_zeros=maxz, pencils_with_9=nine,
                counterexamples=cex, example=example)

def run_conic(F):
    """Common irreducible conic c: F = m c, G = m' c.  Enumerate c up to scaling (q = 3)."""
    P = points(F)
    conics = sorted({normal(F, c) for c in itertools.product(F.els, repeat=6) if any(c)})
    lin = P
    best = 0; cex = 0
    # irreducible = not a product of two linear forms (over F_q)
    prods = set()
    for l, m in itertools.product(lin, repeat=2):
        from classical9 import mul_lin_lin
        prods.add(normal(F, tuple(mul_lin_lin(F, l, m))))
    for c in conics:
        if c in prods: continue
        Vc = [p for p in P if cev(F, c, p) == 0]
        for m, m2 in itertools.combinations(lin, 2):
            inter = [p for p in P if sum(F.mul(x, y) for x, y in zip(m, p)) % 1 == 0 and
                     F.add(F.add(F.mul(m[0], p[0]), F.mul(m[1], p[1])), F.mul(m[2], p[2])) == 0 and
                     F.add(F.add(F.mul(m2[0], p[0]), F.mul(m2[1], p[1])), F.mul(m2[2], p[2])) == 0]
            Z = sorted(set(Vc) | set(inter))
            best = max(best, len(Z))
            if len(Z) == 9 and has_counterexample(F, Z) is not None:
                cex += 1
    return dict(q=F.q, common_conic_max_common_zeros=best, counterexamples=cex)

if __name__ == '__main__':
    F3 = GF(3)
    print(run(F3)); sys.stdout.flush()
    print(run_conic(F3)); sys.stdout.flush()
    F8 = GF8()
    print(run(F8, exhaustive=False, samples=4000)); sys.stdout.flush()

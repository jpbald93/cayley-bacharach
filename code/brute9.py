"""Stage 9 brute force over F_q, q = 2,3,4,5,7.

Checks
 (L) line lemma: dim of cubics vanishing on all F_q-points of z=0 vs dim of z*conics (=6)
 (C) conic line lemma: same for conics vs z*linear (=3)
 (G) criterion: 8 pairwise distinct points, no 5 collinear, on no conic => rank of
     8x10 evaluation matrix = 8 (i.e. cubics through them have dim 2)
 (CB) follows from (G) by linear algebra; we also test it directly on samples.
Exhaustive for q=2,3,4 ; random sampling for q=5,7.
"""
import itertools, random, sys

class GF:
    def __init__(self, q):
        self.q = q
        if q in (2, 3, 5, 7):
            self.els = list(range(q))
            self.add = lambda a, b: (a + b) % q
            self.mul = lambda a, b: (a * b) % q
            self.neg = lambda a: (-a) % q
        elif q == 4:  # F_4 = F_2[w]/(w^2+w+1), elements 0,1,2=w,3=w+1 as bit vectors
            self.els = [0, 1, 2, 3]
            def mul(a, b):
                r = 0
                for i in range(2):
                    if (b >> i) & 1:
                        r ^= a << i
                if r & 4:
                    r ^= 0b111
                return r
            self.add = lambda a, b: a ^ b
            self.mul = mul
            self.neg = lambda a: a
        self.inv = {a: next(b for b in self.els if self.mul(a, b) == 1) for a in self.els if a}

    def rank(self, rows):
        M = [list(r) for r in rows]
        rk = 0; ncol = len(M[0]) if M else 0
        for c in range(ncol):
            piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
            if piv is None: continue
            M[rk], M[piv] = M[piv], M[rk]
            iv = self.inv[M[rk][c]]
            M[rk] = [self.mul(iv, x) for x in M[rk]]
            for i in range(len(M)):
                if i != rk and M[i][c]:
                    f = M[i][c]
                    M[i] = [self.add(x, self.neg(self.mul(f, y))) for x, y in zip(M[i], M[rk])]
            rk += 1
        return rk

def pw(F, a, n):
    r = 1
    for _ in range(n): r = F.mul(r, a)
    return r

def cubmono(F, v):
    x, y, z = v
    m = lambda *e: F.mul(F.mul(pw(F, x, e[0]), pw(F, y, e[1])), pw(F, z, e[2]))
    return [m(3,0,0), m(2,1,0), m(2,0,1), m(1,2,0), m(1,1,1), m(1,0,2), m(0,3,0), m(0,2,1), m(0,1,2), m(0,0,3)]

def conmono(F, v):
    x, y, z = v
    m = lambda *e: F.mul(F.mul(pw(F, x, e[0]), pw(F, y, e[1])), pw(F, z, e[2]))
    return [m(2,0,0), m(1,1,0), m(1,0,1), m(0,2,0), m(0,1,1), m(0,0,2)]

def points(F):
    P = []
    for v in itertools.product(F.els, repeat=3):
        if any(v):
            # normalise: first nonzero coordinate = 1
            k = next(i for i in range(3) if v[i])
            if v[k] == 1: P.append(v)
    return P

def lines(F, P):
    # lines = same normalised vectors as dual points
    L = []
    for l in P:
        L.append(frozenset(i for i, p in enumerate(P)
                 if F.add(F.add(F.mul(l[0], p[0]), F.mul(l[1], p[1])), F.mul(l[2], p[2])) == 0))
    return L

def main(q, sample=None, seed=1):
    F = GF(q); P = points(F); L = lines(F, P)
    out = {}
    # (L),(C): points of z=0
    Z = [p for p in P if p[2] == 0]
    rkC = F.rank([cubmono(F, p) for p in Z]); dimL = 10 - rkC
    rkQ = F.rank([conmono(F, p) for p in Z]); dimQ = 6 - rkQ
    out['line_lemma'] = (dimL, dimL == 6)
    out['conic_line_lemma'] = (dimQ, dimQ == 3)
    # (G)
    idx = range(len(P))
    it = itertools.combinations(idx, 8) if sample is None else None
    rnd = random.Random(seed)
    tested = gp = bad = 0; ex = None
    def subsets():
        if sample is None:
            yield from itertools.combinations(idx, 8)
        else:
            for _ in range(sample): yield tuple(sorted(rnd.sample(list(idx), 8)))
    for S in subsets():
        tested += 1
        Sset = set(S)
        if any(len(Sset & l) >= 5 for l in L): continue
        if F.rank([conmono(F, P[i]) for i in S]) < 6: continue
        gp += 1
        r = F.rank([cubmono(F, P[i]) for i in S])
        if r != 8:
            bad += 1; ex = ex or [P[i] for i in S]
    out['criterion'] = dict(npoints=len(P), tested=tested, general_position=gp, failures=bad, example=ex)
    return out

if __name__ == '__main__':
    for q, samp in [(2, None), (3, None), (4, None), (5, 20000), (7, 20000)]:
        print('q =', q, main(q, samp)); sys.stdout.flush()

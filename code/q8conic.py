"""q = 8, common smooth conic c = xz + y^2 (9 F_8-points): F = m c, G = m' c with
m ∩ m' on c gives exactly 9 common zeros.  Check no cubic passes through 8 of them but not
the 9th (a cubic through 8 points of a smooth conic contains it), and that q = 7 with an
8-point conic plus m ∩ m' off c DOES give a counterexample."""
import sys; sys.path.insert(0, '.')
from brute9 import GF, points, cubmono
from classical9b import GF8, cev, has_counterexample
def dot(F, a, b): return F.add(F.add(F.mul(a[0], b[0]), F.mul(a[1], b[1])), F.mul(a[2], b[2]))
for F, c in [(GF8(), (0, 0, 1, 1, 0, 0)), (GF(7), (0, 0, 1, 1, 0, 0))]:
    P = points(F); V = [p for p in P if cev(F, c, p) == 0]
    tot = cex = 0; ex = None
    for m in P:
        for m2 in P:
            if m >= m2: continue
            meet = [p for p in P if dot(F, m, p) == 0 and dot(F, m2, p) == 0]
            Z = sorted(set(V) | set(meet))
            if len(Z) != 9: continue
            tot += 1
            r = has_counterexample(F, Z)
            if r is not None: cex += 1; ex = ex or (m, m2, r)
    print('q =', F.q, 'conic points', len(V), 'nine-point pencils', tot, 'counterexamples', cex, 'example', ex)

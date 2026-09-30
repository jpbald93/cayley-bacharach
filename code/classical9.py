"""Stage 9: explicit counterexamples to the *classical* form (two cubics meeting in exactly
nine F_q-points) over F_4, F_5, F_7, via F = z*q1, G = z*q2.  For each q we search conic
pairs q1, q2 (products of two lines each) such that the common F_q-zeros of F, G are
exactly 9 points, then look for a cubic H through 8 of them but not the 9th.
Also verifies, for every counterexample found, linear independence of F, G.
"""
import itertools, random, sys
sys.path.insert(0, '.')
from brute9 import GF, points, cubmono, conmono

def dot(F, a, b):
    return F.add(F.add(F.mul(a[0], b[0]), F.mul(a[1], b[1])), F.mul(a[2], b[2]))

def mul_lin_lin(F, l, m):   # conic l*m in order x2 xy xz y2 yz z2
    a = lambda i, j: F.mul(l[i], m[j])
    return [a(0,0), F.add(a(0,1), a(1,0)), F.add(a(0,2), a(2,0)), a(1,1), F.add(a(1,2), a(2,1)), a(2,2)]

def mul_lin_con(F, l, q):   # cubic l*q (same formula as Lean's mulLin)
    m = F.mul; s = F.add
    return [m(l[0],q[0]), s(m(l[0],q[1]),m(l[1],q[0])), s(m(l[0],q[2]),m(l[2],q[0])),
            s(m(l[0],q[3]),m(l[1],q[1])), s(s(m(l[0],q[4]),m(l[1],q[2])),m(l[2],q[1])),
            s(m(l[0],q[5]),m(l[2],q[2])), m(l[1],q[3]), s(m(l[1],q[4]),m(l[2],q[3])),
            s(m(l[1],q[5]),m(l[2],q[4])), m(l[2],q[5])]

def ev(F, C, v):
    r = 0
    for c, x in zip(C, cubmono(F, v)): r = F.add(r, F.mul(c, x))
    return r

def nullspace_vec_not_at(F, rows, p):
    """Is there a cubic vanishing on `rows` points but not at p?  <=> rank increases."""
    A = [cubmono(F, v) for v in rows]
    return F.rank(A + [cubmono(F, p)]) > F.rank(A)

def search(q, tries=4000, seed=0):
    F = GF(q); P = points(F); rnd = random.Random(seed)
    z = (0, 0, 1)
    for _ in range(tries):
        l1, l2, l3, l4 = (rnd.choice(P) for _ in range(4))
        q1 = mul_lin_lin(F, l1, l2); q2 = mul_lin_lin(F, l3, l4)
        FF = mul_lin_con(F, z, q1); GG = mul_lin_con(F, z, q2)
        if F.rank([FF, GG]) < 2: continue
        Z = [p for p in P if ev(F, FF, p) == 0 and ev(F, GG, p) == 0]
        if len(Z) != 9: continue
        for k in range(9):
            eight = Z[:k] + Z[k+1:]
            if nullspace_vec_not_at(F, eight, Z[k]):
                return dict(q=q, z=z, l1=l1, l2=l2, l3=l3, l4=l4, F=FF, G=GG, nine=Z, missing=Z[k])
    return None

def exhaustive_holds(q):
    """For q = 3 (and 8 by hand): enumerate all pencils <z*q1, z*q2> with q1, q2 arbitrary
    conics (not only line pairs) is too big; we enumerate all conic pairs up to scaling for q=3."""
    F = GF(q); P = points(F); z = (0, 0, 1)
    conics = [c for c in itertools.product(F.els, repeat=6) if any(c)]
    zl = [p for p in P if p[2] == 0]
    off = [p for p in P if p[2] != 0]
    Zc = {c: frozenset(i for i, p in enumerate(off) if sum_(F, c, p) == 0) for c in conics}
    maxoff = 0
    for c1, c2 in itertools.combinations(conics, 2):
        s = Zc[c1] & Zc[c2]
        if len(s) > maxoff and F.rank([mul_lin_con(F, z, list(c1)), mul_lin_con(F, z, list(c2))]) == 2:
            maxoff = len(s)
    return len(zl), maxoff

def sum_(F, c, p):
    r = 0
    for a, x in zip(c, conmono(F, p)): r = F.add(r, F.mul(a, x))
    return r

if __name__ == '__main__':
    for q in (4, 5, 7):
        print('q =', q, search(q)); sys.stdout.flush()
    print('q = 3 common-line pencils: (#pts on z=0, max #common off-line zeros) =', exhaustive_holds(3))

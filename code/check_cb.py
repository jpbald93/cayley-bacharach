"""Exact-rational check of Cayley-Bacharach (8 => 9) and of the 5-collinear counterexample."""
import random
from sympy import Matrix, Rational, symbols, Poly, solve, groebner

def mono(p):
    x, y, z = p
    return [x**3, x*x*y, x*x*z, x*y*y, x*y*z, x*z*z, y**3, y*y*z, y*z*z, z**3]

def conic_mono(p):
    x, y, z = p
    return [x*x, x*y, x*z, y*y, y*z, z*z]

def cubic_through(pts):
    return Matrix([mono(p) for p in pts]).nullspace()

def ev(F, p):
    return sum(c * m for c, m in zip(F, mono(p)))

def nine_points_of_pencil(seed):
    """Two random cubics F,G through 8 random rational points; the 9th base point is
    found exactly as the residual intersection (via F,G restricted and resultants)."""
    rnd = random.Random(seed)
    while True:
        pts = [(Rational(rnd.randint(-30, 30)), Rational(rnd.randint(-30, 30)), Rational(1))
               for _ in range(8)]
        ns = cubic_through(pts)
        if len(set(pts)) == 8 and len(ns) == 2:
            return pts, ns

def ninth_point(F, G, pts):
    x, y = symbols('x y')
    f = sum(c * m for c, m in zip(F, mono((x, y, 1))))
    g = sum(c * m for c, m in zip(G, mono((x, y, 1))))
    B = groebner([f, g], y, x, order='lex')
    # univariate polynomial in x: divide out the 8 known x-coordinates
    ux = [b for b in B.exprs if b.free_symbols <= {x}][0]
    px = Poly(ux, x)
    for p in pts:
        q, r = divmod(px, Poly(x - p[0], x))
        if r.is_zero:
            px = q
    assert px.degree() == 1, px
    x9 = -px.all_coeffs()[1] / px.all_coeffs()[0]
    ys = solve([f.subs(x, x9), g.subs(x, x9)], y, dict=True)
    return (x9, ys[0][y], Rational(1))

def main():
    ok = 0
    for seed in range(5):
        pts, ns = nine_points_of_pencil(seed)
        assert len(ns) == 2, "8 random points should impose 8 conditions"
        F, G = list(ns[0]), list(ns[1])
        P9 = ninth_point(F, G, pts)
        assert ev(F, P9) == 0 and ev(G, P9) == 0
        # H: the cubic through the 8 points and an extra random point R, computed
        # independently of F, G (a genuine "cubic through the 8").
        rnd = random.Random(100 + seed)
        R = (Rational(rnd.randint(10, 40)), Rational(rnd.randint(10, 40)), Rational(1))
        nsH = cubic_through(pts + [R])
        assert len(nsH) == 1
        H = list(nsH[0])
        assert all(ev(H, p) == 0 for p in pts) and ev(H, P9) == 0
        # every cubic through the 8 is in span(F,G): rank check
        assert Matrix([mono(p) for p in pts + [P9]]).rank() == 8
        ok += 1
        print(f"seed {seed}: 9th point {P9}, dim cubics through 8 = 2, H(P9) = 0")
    # counterexample: 5 collinear points (on y = 0) + 3 others
    pts = [(Rational(k), Rational(0), Rational(1)) for k in range(5)] + \
          [(Rational(0), Rational(1), Rational(1)), (Rational(1), Rational(2), Rational(1)),
           (Rational(3), Rational(-1), Rational(1))]
    ns = cubic_through(pts)
    print("5 collinear: dim cubics through 8 =", len(ns))
    assert len(ns) == 3
    F, G, H = [list(v) for v in ns]
    # the pencil F,G has base points; a ninth point Q with F(Q)=G(Q)=0 but H(Q) != 0
    # exists: take the kernel element vanishing extra at a random point R, and compare.
    R = (Rational(7), Rational(5), Rational(1))
    ns2 = cubic_through(pts + [R])
    assert len(ns2) == 2
    F2, G2 = [list(v) for v in ns2]
    # H3 := a cubic through the 8 but not through R
    H3 = next(v for v in (F, G, H) if ev(v, R) != 0)
    print("F2(R) =", ev(F2, R), " G2(R) =", ev(G2, R), " H3(R) =", ev(H3, R))
    print("=> F2,G2 vanish at 8 points + R, H3 vanishes at the 8 but not at R: CB fails.")
    print(f"all {ok} random checks passed")

if __name__ == "__main__":
    main()

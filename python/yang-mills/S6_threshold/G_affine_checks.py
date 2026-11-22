# Cross-checks of G_affine_cert.py (not part of the certificate's proof).  python3 G_affine_checks.py
#  1. P = 64 against P = 104: box by box upper bounds.
#  2. Point values of the present certificate (G_box_A_1of2.py, interval arithmetic at P = 104) at random
#     rational points of each box must lie inside the affine enclosure of the box.
#  3. The reference box of the handoff: affine enclosure inside the present certificate's interval.
#  4. Rule tests: for random forms and random eps (and a random admissible error), the exact value of the
#     result of +, *, sq, /n lies inside the result form at the same eps; for 1/x, sqrt, exp, asin, the
#     argument's exact value is taken, f enclosed by the module's own series, and the enclosure must lie inside.
import sys, os, random
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "../S4_general_d"))
import G_affine_cert as ga
import G_box_A_1of2 as old

random.seed(20261122)
bxs = list(ga.boxes())

print("1. P = 64 vs P = 104")
res = {}
for p in (64, 104):
    ga.init(p)
    res[p] = [Fr(ga.G_affine((b[0], b[1]), (b[2], b[3]), b[4], b[5])[0].hi(), 1 << p) for b in bxs]
diff = max(abs(x - y) for x, y in zip(res[64], res[104]))
print("   largest upper bound: P=64 %.9f, P=104 %.9f; largest box-by-box difference %.2e"
      % (max(res[64]), max(res[104]), float(diff)))
ga.init(64)

print("2. present certificate's point values inside the affine boxes (P = 64)")
OUT, NPT, worst_gap = 0, 0, None
for b in bxs:
    g, q, c = ga.G_affine((b[0], b[1]), (b[2], b[3]), b[4], b[5])
    lo, hi = Fr(g.lo(), 1 << 64), Fr(g.hi(), 1 << 64)
    for t in range(12):
        pt = [Fr(random.randint(0, 1000), 1000) for _ in range(3)]
        if t == 0:
            pt = [Fr(0), Fr(0), Fr(0)]
        if t == 1:
            pt = [Fr(1), Fr(1), Fr(1)]
        mu, r, d = (b[0] + pt[0] * (b[1] - b[0]), b[2] + pt[1] * (b[3] - b[2]), b[4] + pt[2] * (b[5] - b[4]))
        if d == 0:
            d = Fr(1, 10 ** 6) * (b[5] - b[4])
        v, _, _ = old.G_enclosure((mu, mu), (r, r), d, d, {})
        pl, ph = Fr(v.l, old.ONE), Fr(v.h, old.ONE)
        NPT += 1
        if not (lo <= pl and ph <= hi):
            OUT += 1
        gap = hi - ph
        worst_gap = gap if worst_gap is None else min(worst_gap, gap)
print("   %d points (incl. both corners of every box), outside: %d; smallest (upper bound - point value) %.4f"
      % (NPT, OUT, float(worst_gap)))

print("3. reference box mu [0.400,0.405], r [0.40,0.41], d [0.126,0.154]")
R = ((Fr(400, 1000), Fr(405, 1000)), (Fr(40, 100), Fr(41, 100)), Fr(126, 1000), Fr(154, 1000))
v, _, _ = old.G_enclosure(*R, {})
g, _, _ = ga.G_affine(*R)
print("   present certificate [%.6f, %.6f]; affine [%.6f, %.6f]; inside: %s"
      % (v.l / old.ONE, v.h / old.ONE, g.lo() / 2 ** 64, g.hi() / 2 ** 64,
         Fr(v.l, old.ONE) <= Fr(g.lo(), 1 << 64) and Fr(g.hi(), 1 << 64) <= Fr(v.h, old.ONE)))

print("4. rule tests")
S = 1 << ga.P


def rform(scale, lin, err, pos=False):
    c = random.randint(-scale, scale)
    if pos:
        c = abs(c) + 3 * lin + err + scale // 4
    return ga.A(c, random.randint(-lin, lin), random.randint(-lin, lin), random.randint(-lin, lin), random.randint(0, err))


def val(x, eps, u):  # an exact value enclosed by x at eps: (c + sum a eps + u e)/S, u in [-1,1]
    return Fr(x.c + x.a1 * eps[0] + x.a2 * eps[1] + x.a3 * eps[2], S) + u * Fr(x.e, S)


def inside(y, eps, lo, hi):  # [lo, hi] inside y's set at eps
    m = Fr(y.c + y.a1 * eps[0] + y.a2 * eps[1] + y.a3 * eps[2], S)
    return m - Fr(y.e, S) <= lo and hi <= m + Fr(y.e, S)


bad, n = 0, 0
for trial in range(3000):
    eps = [Fr(random.randint(-8, 8), 8) for _ in range(3)]
    ux, uy = Fr(random.randint(-4, 4), 4), Fr(random.randint(-4, 4), 4)
    x, y = rform(2 * S, S // 8, S // 1000), rform(2 * S, S // 8, S // 1000)
    X, Y = val(x, eps, ux), val(y, eps, uy)
    for res_, ex in ((x + y, X + Y), (x - y, X - Y), (x * y, X * Y), (ga.sq(x), X * X), (x * 7, 7 * X), (x / 13, X / 13)):
        n += 1
        bad += not inside(res_, eps, ex, ex)
    # function rules on small-range arguments
    xp = ga.A(random.randint(S // 2, 2 * S), random.randint(-S // 64, S // 64), random.randint(-S // 64, S // 64), 0,
              random.randint(0, S // 1000))
    Xp = val(xp, eps, ux)
    r1 = ga.recip(xp); n += 1; bad += not inside(r1, eps, 1 / Xp, 1 / Xp)
    r2 = ga.sqrt(xp); a = Fr(ga.isqrt(int(Xp * S * S)), S); n += 1
    bad += not inside(r2, eps, a, a + Fr(1, S))      # sqrt(Xp) in [a, a + 1/S] up to the floor of Xp S^2
    xe = ga.A(random.randint(-S, S), random.randint(-S // 16, S // 16), 0, random.randint(-S // 16, S // 16), random.randint(0, S // 1000))
    lo_, hi_ = ga.exp_iv(val(xe, eps, ux)); n += 1; bad += not inside(ga.exp(xe), eps, lo_, hi_)
    xa = ga.A(random.randint(-S // 20, S // 8), random.randint(-S // 40, S // 40), 0, 0, random.randint(0, S // 1000))
    lo_, hi_ = ga.asin_iv(val(xa, eps, ux)); n += 1; bad += not inside(ga.asin(xa), eps, lo_, hi_)
print("   %d results checked, outside: %d" % (n, bad))

# Step 5: the incomplete moments for c slightly below 0, and how far below 0 the affine range of c goes.
# python3 check_c.py      PROTOTYPE (floats).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import g_affine as ga
from affine import Ctx, AF
import measure

# (a) the closed forms and recurrences of inc_table against quadrature, at point values of c
th, wt = np.polynomial.legendre.leggauss(400)
print("(a) inc_table vs quadrature of int_c^1 x^n w^(2k+1) dx  (x = sin t, smooth integrand)")
for c in (-0.2, -0.05, -0.01, -1e-4, 0.0, 0.1, 0.25):
    Ctx.B, Ctx.track = 1, False
    ca = AF.const(c)
    T = ga.inc_table(ca, ga.sqrt(1.0 - ga.sq(ca)))
    a, b = np.arcsin(c), np.pi / 2
    t = (b - a) / 2 * th + (a + b) / 2
    worst = 0
    for k in range(ga.KR + 1):
        for n in range(ga.NMAX + 1):
            ref = (b - a) / 2 * np.sum(wt * np.sin(t) ** n * np.cos(t) ** (2 * k + 2))
            worst = max(worst, abs(T[k][n].c[0] - ref))
    print("   c = %8.4f: max abs difference over k <= %d, n <= %d: %.1e" % (c, ga.KR, ga.NMAX, worst))

# (b) the range of c over the grids of measure.py and the guard
print("(b) lowest lo(c) over the boxes (guard allows down to -CNEG = %.3f)" % ga.CNEG)
for mode in ("spec", "tight"):
    for n in ((4, 4, 1), (8, 8, 1), (8, 8, 2), (16, 16, 2)):
        u, c = measure.ub(measure.cells(0, .8, 0, .8, 0, .2, *n), mode)
        print("   rules %-5s grid %-11s: min lo(c) = %.5f at mu in [0, %.3f]; max hi(c) = %.4f"
              % (mode, n, c.lo().min(), 0.8 / n[0], c.hi().max()))

# (c) error of G against cell size at the worst corner, cubic cells shrinking towards (0.8, 0.8, 0.2)
print("(c) radius of G on cells [0.8-h, 0.8] x [0.8-h, 0.8] x [0.2-h/2, 0.2]")
for mode in ("spec", "tight"):
    prev = None
    for h in (0.2, 0.1, 0.05, 0.025, 0.0125):
        Ctx.prod, Ctx.fn = measure.MODES[mode]
        Ctx.track = False
        G, c, q = ga.G_affine(*[np.array([v]) for v in (0.8 - h, 0.8, 0.8 - h, 0.8, 0.2 - h / 2, 0.2)])
        e, l = G.err()[0], G.lin()[0]
        print("   rules %-5s h = %.4f: linear %.5f (/h = %.4f), error %.5f (/h^2 = %.3f)%s"
              % (mode, h, l, l / h, e, e / h ** 2, "" if prev is None else ", error ratio to previous %.2f" % (prev / e)))
        prev = e

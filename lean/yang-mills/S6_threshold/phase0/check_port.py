# Step 4: the port against the present certificate.  Run from this folder: python3 check_port.py
import sys, os, random
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../../python/yang-mills/S4_general_d"))
import numpy as np
import G_box_A_1of2 as g
import g_affine as ga
from affine import Ctx

ONE = 2.0 ** 104
print("1. zero-width boxes: affine centre vs the certificate's (tiny) interval")
random.seed(1)
pts = [(Fr(random.randint(1, 800), 1000), Fr(random.randint(0, 800), 1000), Fr(random.randint(1, 200), 1000))
       for _ in range(40)] + [(Fr(4, 5), Fr(4, 5), Fr(1, 5)), (Fr(1, 1000), Fr(0), Fr(1, 1000))]
worst = 0
for mode in ("spec", "tight"):
    Ctx.prod = Ctx.fn = mode if mode == "spec" else "tight"
    Ctx.fn = "spec" if mode == "spec" else "best"
    mu, r, d = (np.array([float(p[i]) for p in pts]) for i in range(3))
    G, c, q = ga.G_affine(mu, mu, r, r, d, d)
    for i, (m, rr, dd) in enumerate(pts):
        v, _, _ = g.G_enclosure((m, m), (rr, rr), dd, dd, {})
        lo, hi = v.l / ONE, v.h / ONE
        rel = abs(G.c[i] - (lo + hi) / 2)
        worst = max(worst, rel)
        if not (lo - 1e-12 <= G.c[i] <= hi + 1e-12):
            print("  OUTSIDE", m, rr, dd, G.c[i], lo, hi)
print("  max |affine centre - certificate midpoint| = %.2e over %d points, both modes" % (worst, len(pts)))
print("  (certificate interval width at a point: %.1e)" % ((v.h - v.l) / ONE))
print("2. reference box mu [0.400,0.405], r [0.40,0.41], d [0.126,0.154]")
v, qq, cc = g.G_enclosure((Fr(400, 1000), Fr(405, 1000)), (Fr(40, 100), Fr(41, 100)), Fr(126, 1000), Fr(154, 1000), {})
print("  certificate:  G in [%.6f, %.6f]  (upper end %d / 2^104)" % (v.l / ONE, v.h / ONE, v.h))
for prod, fn in (("spec", "spec"), ("tight", "best"), ("tight", "cheb")):
    Ctx.prod, Ctx.fn = prod, fn
    G, c, q = ga.G_affine(0.400, 0.405, 0.40, 0.41, 0.126, 0.154)
    lo, hi = G.lo()[0], G.hi()[0]
    inside = v.l / ONE <= lo and hi <= v.h / ONE
    print("  affine %-5s/%-4s: G in [%.6f, %.6f], radius %.2e (linear %.2e, error %.2e); inside: %s"
          % (prod, fn, lo, hi, G.rad()[0], G.lin()[0], G.err()[0], inside))

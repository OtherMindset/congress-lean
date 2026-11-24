# Soundness smoke test of the prototype: point values of G, c, q at random points (and corners) of each box
# must lie in the box's affine range.  python3 check_contain.py      PROTOTYPE (floats).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import g_affine as ga
from affine import Ctx
import measure

rng = np.random.default_rng(0)
S = 400
for prod, fn, n in (("spec", "spec", (8, 8, 2)), ("sq", "best", (8, 8, 2)), ("tight", "best", (8, 8, 1)),
                    ("tight", "cheb", (8, 8, 1)), ("tight", "best", (4, 4, 1))):
    Ctx.prod, Ctx.fn, Ctx.track = prod, fn, False
    b = measure.cells(0, .8, 0, .8, 0, .2, *n)
    G, c, q = ga.G_affine(*b)
    rng_ = {k: (v.lo(), v.hi()) for k, v in (("G", G), ("c", c), ("q", q))}
    nb = len(b[0])
    idx = np.repeat(np.arange(nb), S)
    u = rng.random((3, nb * S))
    u[:, ::S], u[:, 1::S] = 0, 1
    p = [b[2 * i][idx] + u[i] * (b[2 * i + 1][idx] - b[2 * i][idx]) for i in range(3)]
    p[2] = np.maximum(p[2], 1e-9)
    Gp, cp, qp = ga.G_affine(p[0], p[0], p[1], p[1], p[2], p[2])
    out = {k: int(((v.c < rng_[k][0][idx] - 1e-13) | (v.c > rng_[k][1][idx] + 1e-13)).sum())
           for k, v in (("G", Gp), ("c", cp), ("q", qp))}
    print("rules %-5s/%-4s grid %-10s: %6d points, outside the box's range: %s; G at the points in [%.4f, %.4f]"
          % (prod, fn, n, nb * S, out, Gp.c.min(), Gp.c.max()))

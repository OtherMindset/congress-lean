# Error term of G split by source for typical cells, and the effect of modelled rounding at 2^-P.
# python3 breakdown.py      PROTOTYPE (floats).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import g_affine as ga
from affine import Ctx

CELLS = {
    "cell mu .7-.8, r .3-.4, d .1-.2": (0.7, 0.8, 0.3, 0.4, 0.1, 0.2),
    "worst cell of uniform 8x8x2 (corner)": (0.7, 0.8, 0.7, 0.8, 0.1, 0.2),
    "middle cell 0.1^2 x 0.1": (0.4, 0.5, 0.4, 0.5, 0.0, 0.1),
    "low cell 0.2^2 x 0.2": (0.0, 0.2, 0.0, 0.2, 0.0, 0.2),
    "reference box": (0.400, 0.405, 0.40, 0.41, 0.126, 0.154),
}


def show(name, b, prod="spec", fn="spec"):
    Ctx.prod, Ctx.fn, Ctx.track, Ctx.unit = prod, fn, True, 0.0
    G, c, q = ga.G_affine(*[np.array([v]) for v in b])
    E, L = G.err()[0], G.lin()[0]
    print("%s %s (rules %s/%s): centre %.5f, linear %.5f, error %.5f, upper bound %.5f; c in [%.4f, %.4f]"
          % (name, b, prod, fn, G.c[0], L, E, G.hi()[0], c.lo()[0], c.hi()[0]))
    for by in ("op", "stage"):
        bd = sorted(ga.breakdown(G, by).items(), key=lambda kv: -kv[1][0])
        print("   by %-5s: " % by + ", ".join("%s %.0f%%" % (k, 100 * v[0] / E) for k, v in bd if v[0] / E >= 0.005))
    bd = sorted(ga.breakdown(G, "full").items(), key=lambda kv: -kv[1][0])[:6]
    print("   top 6   : " + ", ".join("%s %.0f%%" % (k, 100 * v[0] / E) for k, v in bd))


if __name__ == "__main__":
    for n, b in CELLS.items():
        show(n, b)
    show("worst cell of uniform 8x8x2 (corner)", CELLS["worst cell of uniform 8x8x2 (corner)"], "tight", "best")
    print("\nModelled rounding (4 units of 2^-P per product, square, function and scaling), uniform 8x8x2, spec rules:")
    import measure
    b = measure.cells(0, .8, 0, .8, 0, .2, 8, 8, 2)
    for P in (0, 32, 40, 48, 64, 104):
        Ctx.prod, Ctx.fn, Ctx.track, Ctx.unit = "spec", "spec", False, (2.0 ** -P if P else 0.0)
        G, c, q = ga.G_affine(*b)
        print("   P = %s: largest upper bound %.6f" % (P or "none", G.hi().max()))
    Ctx.unit = 0.0

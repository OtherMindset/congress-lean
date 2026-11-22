# Steps 6-7: cell sizes by region, error breakdown, grid and box count.  python3 measure.py
# PROTOTYPE (floats): evidence about box counts, not about the theorem.
import sys, os, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import g_affine as ga
from affine import Ctx

SIDE, DMAX, THR = 0.8, 0.2, -0.005
MODES = {"spec": ("spec", "spec"), "sq+best": ("sq", "best"), "tight": ("tight", "best")}


def cells(m0, m1, r0, r1, d0, d1, nm, nr, nd):
    em, er, ed = np.linspace(m0, m1, nm + 1), np.linspace(r0, r1, nr + 1), np.linspace(d0, d1, nd + 1)
    I, J, K = (x.ravel() for x in np.meshgrid(range(nm), range(nr), range(nd), indexing="ij"))
    return em[I], em[I + 1], er[J], er[J + 1], ed[K], ed[K + 1]


def ub(b, mode):
    Ctx.prod, Ctx.fn = MODES[mode]
    Ctx.track = False
    G, c, q = ga.G_affine(*b)
    u = G.hi()
    for m in Ctx.fails.values():
        u = np.where(m, np.inf, u)
    return u, c


def best_region(reg, mode, nmax=8, ndmax=4):
    # fewest equal cells in the region with every upper bound <= THR (ties: larger worst margin)
    best = None
    for nm, nr, nd in itertools.product(range(1, nmax + 1), range(1, nmax + 1), range(1, ndmax + 1)):
        n = nm * nr * nd
        if best and n > best[0]:
            continue
        u, _ = ub(cells(*reg, nm, nr, nd), mode)
        w = float(np.max(u))
        if w <= THR and (best is None or n < best[0] or w < best[4]):
            best = (n, nm, nr, nd, w)
    return best


def regions(km, kr, kd=1):
    hm, hr, hd = SIDE / km, SIDE / kr, DMAX / kd
    for i, j, k in itertools.product(range(km), range(kr), range(kd)):
        yield (i * hm, (i + 1) * hm, j * hr, (j + 1) * hr, k * hd, (k + 1) * hd)


if __name__ == "__main__":
    out = {}
    for mode in MODES:
        print("=== rules:", mode, MODES[mode])
        for split in ((1, 1, 1), (2, 2, 1), (2, 2, 2), (4, 4, 1)):
            rows, tot, worst = [], 0, -1
            for reg in regions(*split):
                n, nm, nr, nd, w = best_region(reg, mode)
                rows.append(dict(mu=reg[0:2], r=reg[2:4], d=reg[4:6], n_mu=nm, n_r=nr, n_d=nd,
                                 h_mu=(reg[1] - reg[0]) / nm, h_r=(reg[3] - reg[2]) / nr, h_d=(reg[5] - reg[4]) / nd,
                                 boxes=n, worst_ub=w))
                tot += n
                worst = max(worst, w)
            out["%s_%d%d%d" % ((mode,) + split)] = dict(total=tot, worst_ub=worst, regions=rows)
            print("  regions %s: total boxes %d, largest upper bound %.4f" % (split, tot, worst))
            if split in ((2, 2, 1), (4, 4, 1)):
                for rw in rows:
                    print("    mu [%.2f,%.2f] r [%.2f,%.2f] d [%.2f,%.2f]: %d x %d x %d cells of %.3f x %.3f x %.3f, ub <= %.4f"
                          % (rw["mu"] + rw["r"] + rw["d"] + (rw["n_mu"], rw["n_r"], rw["n_d"], rw["h_mu"], rw["h_r"], rw["h_d"], rw["worst_ub"])))
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "measure_out.json"), "w") as f:
        json.dump(out, f, indent=1)

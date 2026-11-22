# Exact-rational check that the boxes of G_affine_cert.py, over all its parts, cover the claimed range
#   [0, 4/5] (mu) x [0, 4/5] (r) x [0, 1/5] (d).          python3 G_affine_tiling.py
# Method: (1) the parts are pairwise disjoint as sets of boxes and together give the full box list;
# (2) every box is a product of three closed intervals with lo < hi; (3) the three projections are partitions:
# sorted, consecutive intervals sharing ends, from 0 to the top of the range; (4) the box list equals the full
# product of the three partitions, each box once.  (3) and (4) give: every point of the range lies in a box.
# (5) as a second, independent argument: all boxes lie in the range, their interiors are pairwise disjoint and
# their volumes add up to the volume of the range.
# Self-contained: the box generator below (BEGIN COPY ... END COPY) is copied character for character from
# G_affine_cert.py; it must stay identical to the lines there.
from fractions import Fraction as Fr
from itertools import product

# BEGIN COPY (G_affine_cert.py)
PART, NPART = 1, 1
NMU, NR, ND = 8, 8, 2
SIDE, DTOP = Fr(4, 5), Fr(1, 5)


def edges(n, top):
    return [top * i / n for i in range(n + 1)]


def boxes(part=PART, npart=NPART):
    em, er, ed = edges(NMU, SIDE), edges(NR, SIDE), edges(ND, DTOP)
    for i in range(NMU):
        if i % npart != part - 1:
            continue
        for j in range(NR):
            for k in range(ND):
                yield (em[i], em[i + 1], er[j], er[j + 1], ed[k], ed[k + 1])
# END COPY


def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)


TOP = (SIDE, SIDE, DTOP)
parts = [list(boxes(p, NPART)) for p in range(1, NPART + 1)]
allb = [b for pt in parts for b in pt]
need(len(set(allb)) == len(allb), "a box occurs twice (within or across parts)")
for b in allb:
    need(all(isinstance(x, Fr) or isinstance(x, int) for x in b), "box ends are exact rationals")
    need(all(b[2 * i] < b[2 * i + 1] for i in range(3)), "box with lo >= hi")
proj = []
for i in range(3):
    iv = sorted(set((Fr(b[2 * i]), Fr(b[2 * i + 1])) for b in allb))
    need(iv[0][0] == 0 and iv[-1][1] == TOP[i], "axis %d does not run from 0 to %s" % (i, TOP[i]))
    need(all(iv[k][1] == iv[k + 1][0] for k in range(len(iv) - 1)), "axis %d: gap or overlap" % i)
    proj.append(iv)
full = set((m[0], m[1], r[0], r[1], d[0], d[1]) for m, r, d in product(*proj))
need(full == set((Fr(b[0]), Fr(b[1]), Fr(b[2]), Fr(b[3]), Fr(b[4]), Fr(b[5])) for b in allb),
     "box list is not the full product of the axis partitions")
# (5) volume argument
need(all(0 <= b[2 * i] and b[2 * i + 1] <= TOP[i] for b in allb for i in range(3)), "box outside the range")
for x, y in ((x, y) for k, x in enumerate(allb) for y in allb[k + 1:]):
    need(any(max(x[2 * i], y[2 * i]) >= min(x[2 * i + 1], y[2 * i + 1]) for i in range(3)), "interiors overlap")
vol = sum((b[1] - b[0]) * (b[3] - b[2]) * (b[5] - b[4]) for b in allb)
need(vol == TOP[0] * TOP[1] * TOP[2], "volumes do not add up")
print("parts = %d, boxes = %d, axis cells = %d x %d x %d" % (NPART, len(allb), *(len(p) for p in proj)))
print("TILING OK: the boxes of G_affine_cert.py cover [0,%s] x [0,%s] x [0,%s] (mu, r, d); exact rationals"
      % TOP)

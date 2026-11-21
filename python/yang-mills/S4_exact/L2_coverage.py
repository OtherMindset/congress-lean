# Coverage computation for the exact-arithmetic L2 grid certificate (L2_exact.py; port of #mwoe5p51-jsugdw).
# Exact rational arithmetic only.  The constants and the functions rows() and boxes() below are copied verbatim
# from L2_exact.py.  Claim proved: the boxes of chunks 1..NCH tile R = [0, SIDE] x [0, SIDE] (mu x r).
# Argument: every box is a closed rectangle of width SIDE/NMU and height SIDE/NR whose lower-left corner is
# (i SIDE/NMU, j SIDE/NR) with integers 0 <= i < NMU, 0 <= j < NR (checked exactly).  The map box -> (i, j) is
# injective and there are NMU*NR boxes (checked), so every lattice cell [i,i+1]x[j,j+1] (scaled) occurs exactly
# once; these cells tile R.  Since each box is tested in L2_exact.py by its centre and the Lipschitz slack for
# its own half-widths, every point of R (with every d in [DLO, DHI]) is covered.
from fractions import Fraction as Fr

NCH = 1
NMU, NR = 160, 80
SIDE = Fr(7872, 10000)


def rows(chunk):
    return range((chunk - 1) * NR // NCH, chunk * NR // NCH)


def boxes(chunk):
    # exact boxes (mu_lo, mu_hi, r_lo, r_hi) of chunk `chunk` (1-based)
    hmu, hr = SIDE / (2 * NMU), SIDE / (2 * NR)
    for jr in rows(chunk):
        for jm in range(NMU):
            yield (2 * jm * hmu, (2 * jm + 2) * hmu, 2 * jr * hr, (2 * jr + 2) * hr)


def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)


wm, wr = SIDE / NMU, SIDE / NR
seen = set()
area = Fr(0)
per = []
for ch in range(1, NCH + 1):
    n = 0
    for (ml, mh, rl, rh) in boxes(ch):
        need(mh - ml == wm and rh - rl == wr, "box size")
        i, j = ml / wm, rl / wr
        need(i.denominator == 1 and j.denominator == 1, "corner on lattice")
        i, j = int(i), int(j)
        need(0 <= i < NMU and 0 <= j < NR, "box inside R")
        need((i, j) not in seen, "box repeated")
        seen.add((i, j))
        area += (mh - ml) * (rh - rl)
        n += 1
    per.append(n)
need(len(seen) == NMU * NR, "count")
need(area == SIDE * SIDE, "area")
print("chunks:", NCH, "; boxes per chunk:", per, "; total:", len(seen))
print("each box: %s x %s; total area = %s = SIDE^2" % (wm, wr, area))
print("CERTIFIED: the boxes of chunks 1..%d tile [0, %s] x [0, %s] (mu x r) with no hole and no overlap" %
      (NCH, SIDE, SIDE))

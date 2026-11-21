# Coverage for the box certificates L2_box.py, G_box_A_?of2.py and G_box_B_?of4.py (finer split) (exact rational arithmetic only).
# Each certificate encloses G over whole boxes (mu x r x d); here: for each configuration, the boxes of parts
# 1..NPART (code of rows() and boxes() copied from the certificates) tile [0, SIDE] x [0, SIDE] x [DMIN, DMAX]:
# every box is [i wm, (i+1) wm] x [j wr, (j+1) wr] x (slab k), each triple (i, j, k) occurs exactly once, the
# slabs are consecutive and increasing, and the volumes add up to SIDE^2 (DMAX - DMIN).
from fractions import Fraction as Fr

CONFIGS = {
    "L2_box.py": (1, 100, 100, Fr(492, 625), [Fr(13103, 100000), Fr(131031, 1000000)]),
    "G_box_A_1of2.py, G_box_A_2of2.py": (2, 160, 80, Fr(4, 5), [Fr(k, 1000) for k in (0, 89, 126, 154, 178, 200)]),
    "G_box_B_1of4.py .. G_box_B_4of4.py": (4, 160, 80, Fr(4, 5), [Fr(k, 1000) for k in (
        200, 219, 236, 253, 268, 283, 296, 310, 322, 335, 346, 358, 369, 379, 390, 400)]),
}


def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)


def rows(part, NR, NPART):
    return range((part - 1) * NR // NPART, part * NR // NPART)


def boxes(part, NPART, NMU, NR, SIDE, SLABS):
    # exact boxes (mu_lo, mu_hi, r_lo, r_hi, d_lo, d_hi) of part `part` (1-based)
    hmu, hr = SIDE / (2 * NMU), SIDE / (2 * NR)
    for jr in rows(part, NR, NPART):
        for jm in range(NMU):
            for k in range(len(SLABS) - 1):
                yield (2 * jm * hmu, (2 * jm + 2) * hmu, 2 * jr * hr, (2 * jr + 2) * hr, SLABS[k], SLABS[k + 1])


for name, (NPART, NMU, NR, SIDE, SLABS) in CONFIGS.items():
    need(SLABS[0] >= 0 and all(x < y for x, y in zip(SLABS, SLABS[1:])), "slabs increasing")
    wm, wr = SIDE / NMU, SIDE / NR
    seen, vol, per = set(), Fr(0), []
    for part in range(1, NPART + 1):
        n = 0
        for (ml, mh, rl, rh, dl, dh) in boxes(part, NPART, NMU, NR, SIDE, SLABS):
            need(mh - ml == wm and rh - rl == wr, "box size")
            i, j = ml / wm, rl / wr
            need(i.denominator == 1 and j.denominator == 1, "corner on lattice")
            k = SLABS.index(dl)
            need(dh == SLABS[k + 1], "slab")
            key = (int(i), int(j), k)
            need(0 <= key[0] < NMU and 0 <= key[1] < NR and key not in seen, "inside, not repeated")
            seen.add(key)
            vol += (mh - ml) * (rh - rl) * (dh - dl)
            n += 1
        per.append(n)
    need(len(seen) == NMU * NR * (len(SLABS) - 1), "count")
    need(vol == SIDE * SIDE * (SLABS[-1] - SLABS[0]), "volume")
    print("%s: boxes per part %s, total %d; they tile [0, %s] x [0, %s] x [%s, %s]" % (
        name, per, len(seen), SIDE, SIDE, SLABS[0], SLABS[-1]))
print("CERTIFIED: for each configuration the boxes of all parts tile the stated range, no hole, no overlap")

# Coverage and constants for the exact certificates G_exact_A.py and G_exact_B.py.  Exact rational arithmetic only.
# (1) Tiling: for each file, the boxes (copied code: boxes(), SLABS, NMU, NR, SIDE) tile
#     [0, SIDE] x [0, SIDE] x [DMIN, DMAX] (mu x r x d): every box is [i wm, (i+1) wm] x [j wr, (j+1) wr] x slab k,
#     each (i, j, k) occurs exactly once, the slabs are consecutive, and the total volume is SIDE^2 (DMAX - DMIN).
# (2) Constants: the Lemma of the accompanying post gives, on 0 <= mu <= a, 0 <= r <= b, 0 < d <= dbar, with
#     S = a + dbar, mb = S/4, k3 = (1+mb)/4, k4 = (1+mb)^2/4, qb = (2/pi) e^{S mb} phi(b), phi(z) = sinh(z)/z,
#     lam = S + mb/(1-mb^2) + b^2 mb/3:
#       |dG/dmu| <= 2(k4 + 3/8 + k3) + qb (2 k3 + dbar/4)/4 + qb ((dbar/2 + lam/4)/8 + k3)      =: LGmu
#       |dG/dr|  <= (r/3) (2(5 k3/4 + 3/4) + qb (2 k3 + dbar/4)/4 + qb ((lam/4 + 1)/8 + 1/4))   =: (r/3) LGr
#     Checked here: LGmu <= LMU and LGr/3 <= LR for the constants LMU, LR used in each file, with rational
#     upper bounds: pi > 3.14159;  e^x <= sum_{j<=12} x^j/j! + 3 x^13/13! for 0 <= x <= 1 (Lagrange, e^x <= 3);
#     phi(b) <= sum_{k<=8} b^(2k)/(2k+1)! + b^18/(19! (1 - b^2)) for 0 <= b < 1 (terms decrease by >= b^2).
from fractions import Fraction as Fr
from math import factorial

NPART = 1
NMU, NR = 80, 40
SIDE = Fr(4, 5)
FILES = {
    "G_exact_A.py": ([Fr(k, 1000) for k in (0, 80, 120, 150, 175, 200)], Fr(265, 100), Fr(94, 100)),
    "G_exact_B.py": ([Fr(k, 1000) for k in (200, 216, 231, 245, 258, 270, 282, 294, 305, 316, 326, 336, 346, 355,
                                            364, 373, 382, 391, 400)], Fr(285, 100), Fr(98, 100)),
}


def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)


def rows(part):
    return range((part - 1) * NR // NPART, part * NR // NPART)


def boxes(part, SLABS):
    # exact boxes (mu_lo, mu_hi, r_lo, r_hi, d_lo, d_hi) of part `part` (1-based)
    hmu, hr = SIDE / (2 * NMU), SIDE / (2 * NR)
    for jr in rows(part):
        for jm in range(NMU):
            for k in range(len(SLABS) - 1):
                yield (2 * jm * hmu, (2 * jm + 2) * hmu, 2 * jr * hr, (2 * jr + 2) * hr, SLABS[k], SLABS[k + 1])


def exp_up(x):
    need(0 <= x <= 1, "exp range")
    return sum(x ** j / factorial(j) for j in range(13)) + 3 * x ** 13 / factorial(13)


def phi_up(b):
    need(0 <= b < 1, "phi range")
    return sum(b ** (2 * k) / factorial(2 * k + 1) for k in range(9)) + b ** 18 / (factorial(19) * (1 - b * b))


def lemma_constants(a, b, dbar):
    S = a + dbar
    mb = S / 4
    need(mb < 1 and dbar <= 1, "lemma range")
    k3, k4 = (1 + mb) / 4, (1 + mb) ** 2 / 4
    qb = Fr(200000, 314159) * exp_up(S * mb) * phi_up(b)
    lam = S + mb / (1 - mb * mb) + b * b * mb / 3
    t2 = qb * (2 * k3 + dbar / 4) / 4
    lgmu = 2 * (k4 + Fr(3, 8) + k3) + t2 + qb * ((dbar / 2 + lam / 4) / 8 + k3)
    lgr = 2 * (5 * k3 / 4 + Fr(3, 4)) + t2 + qb * ((lam / 4 + 1) / 8 + Fr(1, 4))
    return lgmu, lgr / 3, qb, lam


def dec(x, dg=6):  # decimal string, rounded up
    n = -((-x.numerator * 10 ** dg) // x.denominator)
    return str(n // 10 ** dg) + "." + str(n % 10 ** dg).rjust(dg, "0")


wm, wr = SIDE / NMU, SIDE / NR
for name, (SLABS, LMU, LR) in FILES.items():
    need(all(x < y for x, y in zip(SLABS, SLABS[1:])) and SLABS[0] >= 0, "slabs increasing")
    seen, vol = set(), Fr(0)
    for part in range(1, NPART + 1):
        for (ml, mh, rl, rh, dl, dh) in boxes(part, SLABS):
            need(mh - ml == wm and rh - rl == wr, "box size")
            i, j = ml / wm, rl / wr
            need(i.denominator == 1 and j.denominator == 1, "corner on lattice")
            k = SLABS.index(dl)
            need(dh == SLABS[k + 1], "slab")
            key = (int(i), int(j), k)
            need(0 <= key[0] < NMU and 0 <= key[1] < NR and key not in seen, "box inside, not repeated")
            seen.add(key)
            vol += (mh - ml) * (rh - rl) * (dh - dl)
    need(len(seen) == NMU * NR * (len(SLABS) - 1), "count")
    need(vol == SIDE * SIDE * (SLABS[-1] - SLABS[0]), "volume")
    lgmu, lgr, qb, lam = lemma_constants(SIDE, SIDE, SLABS[-1])
    need(lgmu <= LMU and lgr <= LR, "Lipschitz constants")
    print("%s: %d boxes tile [0, %s] x [0, %s] x [%s, %s]; volume %s" % (name, len(seen), SIDE, SIDE, SLABS[0],
                                                                        SLABS[-1], vol))
    msg = "  Lemma constants for a = b = %s, dbar = %s: qbar <= %s, lambda = %s, LGmu <= %s <= %s, LGr/3 <= %s <= %s"
    print(msg % (SIDE, SLABS[-1], dec(qb), dec(lam), dec(lgmu), LMU, dec(lgr), LR))
print("CERTIFIED: each file's boxes tile its range with no hole and no overlap, and its constants LMU, LR are"
      " at least the Lemma's LGmu, LGr/3 for that range")

# Float affine-form port of G_enclosure from python/yang-mills/S4_general_d/G_box_A_1of2.py.
# PROTOTYPE for phase 0 (SPEC_small_certificate_and_kernel_checker.md, 2.3): not rigorous, proves nothing.
#
# Same formulas, same series degrees (JS, JD, KR) and the same truncation tails as the certificate.  Changes:
#   - mu, r, d enter as affine forms with one noise term each, no error term;
#   - the table moments over [-1, 1] are float constants;
#   - 1/x, sqrt, exp and asin use the derivative-bound rule of affine.py; the artanh series in u2 = (d t)^2
#     is a polynomial, evaluated by products, as in the certificate (artanh itself is never called);
#   - c is not clipped: the incomplete-moment formulas are used on the whole affine range of c,
#     and the guard is  -CNEG <= lo(c),  hi(c) <= 1/4;
#   - tails are added to the error term (one-sided tails move the centre by half their width).
import numpy as np
from math import factorial, pi, cosh, exp as mexp
import affine as A
from affine import AF, Ctx, sq, recip, sqrt, exp, asin

JS, JD, KR = 18, 5, 7
NK = 2 * JD + 3
NMAX = NK + JS
NB = NMAX + 2 * KR + 2
FACT = [factorial(i) for i in range(90)]
CNEG = 0.05          # delta of spec 2.3(3): allowed depth of c below 0


def ktab(base):
    tab = [base]
    for k in range(1, KR + 1):
        tab.append([tab[-1][n] - tab[-1][n + 2] for n in range(len(tab[-1]) - 2)])
    return tab


def full_table():
    base = [pi / 2, 0.0]
    for n in range(2, NB):
        base.append(base[n - 2] * (n - 1) / (n + 2))
    return ktab(base)


FULL = full_table()


def powers(x, n):
    out = [AF.const(1.0)]
    for _ in range(n):
        out.append(out[-1] * x)
    return out


def inc_table(c, w):
    # T[0][0] = pi/4 - (c w + asin c)/2,  T[0][1] = w^3/3,  (n+2) T[0][n] = (n-1) T[0][n-2] + c^(n-1) w^3.
    # Valid for every c in (-1, 1) (derivative of x^(n-1) w^3; asin odd).
    w3 = w * w * w
    base = [(c * w + asin(c)) * (-0.5) + pi / 4, w3 * (1 / 3)]
    cp = c
    for n in range(2, NB):
        base.append((base[n - 2] * (n - 1) + cp * w3) * (1.0 / (n + 2)))
        cp = cp * c
    return ktab(base)


def rsum(tab, rp):
    G = []
    for n in range(NMAX + 1):
        s = AF.const(0.0)
        for k in range(KR + 1):
            t = tab[k][n]
            s = s + (rp[k] * t) * (1.0 / FACT[2 * k + 1])
        G.append(s)
    return G


def mhat(G, mp):
    out = []
    for k in range(NK + 1):
        a = AF.const(0.0)
        for i in range(JS + 1):
            a = a + (mp[i] * G[k + i]) * (1.0 / FACT[i])
        out.append(a)
    return out


def pairs(Mh, dp, tail):
    out = []
    for n in range(3):
        e, o = AF.const(0.0), AF.const(0.0)
        for j in range(JD + 1):
            e = e + (dp[j] * Mh[n + 2 * j]) * (1.0 / FACT[2 * j])
            o = o + (dp[j] * Mh[n + 2 * j + 1]) * (1.0 / FACT[2 * j + 1])
        out.append((e.add_tail(-tail, tail), o.add_tail(-tail, tail)))
    return out


def phi(z):
    z2 = sq(z)
    s, p = AF.const(0.0), AF.const(1.0)
    for k in range(KR + 1):
        s = s + p * (1.0 / FACT[2 * k + 1])
        p = p * z2
    zh = np.maximum(z.hi(), 0)
    t = np.maximum(p.hi(), 0) * np.cosh(zh) / FACT[2 * KR + 3]
    return s.add_tail(0.0, t)


def G_affine(mul_, muh, rl, rh, dl, dh, cneg=CNEG):
    """Affine enclosure of G on a batch of boxes (arrays).  Returns (G, c, q) as AF."""
    Ctx.B = len(np.atleast_1d(mul_))
    Ctx.fails = {}
    mul_, muh, rl, rh, dl, dh = [np.asarray(v, float) + np.zeros(Ctx.B) for v in (mul_, muh, rl, rh, dl, dh)]
    Ctx.stage = "input"
    mu, r, d = AF.var(mul_, muh, 0), AF.var(rl, rh, 1), AF.var(dl, dh, 2)
    d2, r2 = sq(d), sq(r)
    # certificate's TAIL bound, at the upper corner of the box (it is increasing in mu, r, d >= 0)
    tail = 2 * np.exp(muh) * np.cosh(dh) * np.cosh(rh) * (
        dh ** (2 * JD + 2) / FACT[2 * JD + 2] + muh ** (JS + 1) / FACT[JS + 1] + rh ** (2 * KR + 2) / FACT[2 * KR + 3])
    Ctx.stage = "powers"
    rp, mp, dp = powers(r2, KR), powers(mu, JS), powers(d2, JD)
    Ctx.stage = "full"
    MF = mhat(rsum(FULL, rp), mp)
    Ctx.stage = "pairsZ"
    Z, X1, X2 = pairs(MF, dp, tail)
    Ctx.stage = "c"
    t = Z[1] * recip(Z[0])
    u2 = d2 * sq(t)
    bad = u2.hi() >= 0.25
    if bad.any():
        A.fail("atanh argument", bad)
    a, p = AF.const(0.0), AF.const(1.0)
    for k in range(13):
        a = a + p * (1.0 / (2 * k + 1))
        p = p * u2
    a = a.add_tail(0.0, 2 * np.maximum(p.hi(), 0))
    c = t * a
    bad = (c.lo() < -cneg) | (c.hi() > 0.25)
    if bad.any():
        A.fail("c range not in [-CNEG, 1/4]", bad)
    Ctx.stage = "inc"
    w = sqrt(1.0 - sq(c))
    T = inc_table(c, w)
    Ctx.stage = "partial"
    N0, N1, N2 = pairs(mhat(rsum(T, rp), mp), dp, tail)
    Ctx.stage = "algebra"

    def pm(x, y):
        return (x[0] * y[0] + d2 * (x[1] * y[1]), x[0] * y[1] + x[1] * y[0])
    den = sq(Z[0]) - d2 * sq(Z[1])
    iden = recip(den)
    iz = (Z[0] * iden, -(Z[1] * iden))
    m = pm(X1, iz)
    m2 = pm(m, m)
    x2 = pm(X2, iz)
    var = (x2[0] - m2[0], x2[1] - m2[1])
    pp, aa, bb = pm(N0, iz), pm(N1, iz), pm(N2, iz)
    Uo = bb[1] - 2 * pm(m, aa)[1] + pm(m2, pp)[1] - pm(pp, var)[1]
    Ctx.stage = "q"
    q = exp((mu + d) * c) * w * phi(r * w) * recip(Z[0] + d * Z[1])
    Ctx.stage = "final"
    G = 2 * Uo + 2 * (q * sq(m[1]))
    return G, c, q


def breakdown(G, by="op"):
    """Error term of G split by source; by = 'op' (operation), 'stage', or 'full' (operation@stage)."""
    out = {}
    for lab, v in G.e.items():
        op, st = lab.split("@") if "@" in lab else (lab, "")
        key = {"op": op, "stage": st, "full": lab}[by]
        out[key] = out.get(key, 0.0) + v
    return out

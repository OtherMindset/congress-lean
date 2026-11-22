# Exact certificate (Python ints and fractions only, affine forms) for G(mu,r,d) := (*)/d, with (*) and its
# pair form exactly as in the header of python/yang-mills/S4_general_d/G_box_A_1of2.py (SHA-256 fce165fd...).
# CLAIM: G < 0 for all 0 < d <= 1/5, 0 <= mu <= 4/5, 0 <= r <= 4/5.
# S = 2^P. A form A(c, a1, a2, a3, e), e >= 0, encloses X if |S X - (c + a1 eps1 + a2 eps2 + a3 eps3)| <= e
# at every eps in [-1,1]^3 whose point (mu, r, d) lies in the box; a box passes if c + |a1|+|a2|+|a3| + e < 0
# for G. Every rule, its derivation and the points to check: README.md in this folder.
# No Lipschitz bound and no moment bound is used. Not checked here: only that (*) is the stated expression.
from fractions import Fraction as Fr
from math import isqrt, factorial

PART, NPART = 1, 1
NMU, NR, ND = 8, 8, 2
SIDE, DTOP = Fr(4, 5), Fr(1, 5)
JS, JD, KR = 18, 5, 7
NK = 2 * JD + 3
NMAX = NK + JS
NB = NMAX + 2 * KR + 2
CNEG = Fr(1, 64)
FACT = [factorial(i) for i in range(90)]
P = 64


def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)


def cdiv(a, b):
    return -((-a) // b)


NE = 40
EXP_R = Fr(8 * 2 ** (NE + 1), factorial(NE + 1))


def exp_iv(q):
    q = Fr(q)
    need(abs(q) <= 2, "exp argument")
    s, t = Fr(1), Fr(1)
    for j in range(1, NE + 1):
        t = t * q / j
        s += t
    return s - EXP_R, s + EXP_R


def cosh_hi(q):
    return (exp_iv(q)[1] + exp_iv(-q)[1]) / 2


NA = 30
ASIN_C = [Fr(FACT[2 * k], 4 ** k * FACT[k] ** 2 * (2 * k + 1)) for k in range(NA + 1)]


def asin_iv(q):
    q = Fr(q)
    need(abs(q) <= Fr(1, 4), "asin argument")
    if q < 0:
        lo, hi = asin_iv(-q)
        return -hi, -lo
    s = sum(ASIN_C[k] * q ** (2 * k + 1) for k in range(NA + 1))
    return s, s + q ** (2 * NA + 3) / (1 - q * q)


def atan_fr(x, n):
    s, out = Fr(0), []
    for k in range(n + 1):
        s += Fr((-1) ** k) * x ** (2 * k + 1) / (2 * k + 1)
        out.append(s)
    return min(out[-2:]), max(out[-2:])


_a5, _a239 = atan_fr(Fr(1, 5), 40), atan_fr(Fr(1, 239), 20)
PI_LO, PI_HI = 16 * _a5[0] - 4 * _a239[1], 16 * _a5[1] - 4 * _a239[0]


class A:
    __slots__ = ('c', 'a1', 'a2', 'a3', 'e')

    def __init__(s, c, a1, a2, a3, e):
        need(e >= 0, "error term")
        s.c, s.a1, s.a2, s.a3, s.e = c, a1, a2, a3, e

    def L(s):
        return abs(s.a1) + abs(s.a2) + abs(s.a3)

    def lo(s):
        return s.c - s.L() - s.e

    def hi(s):
        return s.c + s.L() + s.e

    def __add__(s, o):
        o = cv(o)
        return A(s.c + o.c, s.a1 + o.a1, s.a2 + o.a2, s.a3 + o.a3, s.e + o.e)
    __radd__ = __add__

    def __neg__(s):
        return A(-s.c, -s.a1, -s.a2, -s.a3, s.e)

    def __sub__(s, o):
        return s + (-cv(o))

    def __rsub__(s, o):
        return cv(o) + (-s)

    def __mul__(s, o):
        if isinstance(o, int):
            return A(s.c * o, s.a1 * o, s.a2 * o, s.a3 * o, s.e * abs(o))
        o = cv(o)
        if o is s:
            return sq(s)
        Lx, Ly = s.L(), o.L()
        num = abs(s.c) * o.e + abs(o.c) * s.e + (Lx + s.e) * (Ly + o.e)
        return A((s.c * o.c) >> P, (s.c * o.a1 + o.c * s.a1) >> P, (s.c * o.a2 + o.c * s.a2) >> P,
                 (s.c * o.a3 + o.c * s.a3) >> P, -((-num) >> P) + 4)
    __rmul__ = __mul__

    def __truediv__(s, n):
        need(isinstance(n, int) and n > 0, "divisor")
        return A(s.c // n, s.a1 // n, s.a2 // n, s.a3 // n, cdiv(s.e, n) + 4)

    def widen(s, t):
        need(t >= 0, "tail")
        return A(s.c, s.a1, s.a2, s.a3, s.e + t)


def const(lo, hi):
    need(lo <= hi, "constant order")
    m, h = (lo + hi) / 2 * (1 << P), (hi - lo) / 2 * (1 << P)
    cm = m.numerator // m.denominator
    return A(cm, 0, 0, 0, cdiv(h.numerator, h.denominator) + 1)


def cv(x):
    if isinstance(x, A):
        return x
    if isinstance(x, int):
        return A(x << P, 0, 0, 0, 0)
    x = Fr(x)
    return const(x, x)


def sq(x):
    R = x.L() + x.e
    t = 1 << (P + 1)
    return A((2 * x.c * x.c + R * R) // t, (x.c * x.a1) >> (P - 1), (x.c * x.a2) >> (P - 1), (x.c * x.a3) >> (P - 1),
             cdiv(R * R + 4 * abs(x.c) * x.e, t) + 4)


def fn_rule(x, f_iv, al_lo, al_hi):
    lo, hi = x.lo(), x.hi()
    S = 1 << P
    (f0l, f0h), (f1l, f1h) = f_iv(lo), f_iv(hi)
    best = None
    for al in (al_lo, al_hi):
        g = (f0l - Fr(al * lo, S), f0h - Fr(al * lo, S), f1l - Fr(al * hi, S), f1h - Fr(al * hi, S))
        gl, gh = min(g), max(g)
        if best is None or gh - gl < best[2] - best[1]:
            best = (al, gl, gh)
    al, gl, gh = best
    zm, zh = (gl + gh) / 2, (gh - gl) / 2
    zeta = zm.numerator // zm.denominator
    delta = cdiv(zh.numerator, zh.denominator) + 1
    y = x * A(al, 0, 0, 0, 0)
    return A(y.c + zeta, y.a1, y.a2, y.a3, y.e + delta)


def recip(x):
    if x.hi() < 0:
        return -recip(-x)
    lo, hi = x.lo(), x.hi()
    need(lo > 0, "1/x: range contains 0")
    S = 1 << P
    return fn_rule(x, lambda v: (Fr(S * S, v), Fr(S * S, v)), -cdiv(S ** 3, lo * lo), -((S ** 3) // (hi * hi)))


def sqrt(x):
    lo, hi = x.lo(), x.hi()
    need(lo > 0, "sqrt: range not > 0")
    S = 1 << P

    def f(v):
        a = isqrt(v * S)
        return Fr(a), Fr(a if a * a == v * S else a + 1)
    rh = isqrt(hi * S)
    rh = rh if rh * rh == hi * S else rh + 1
    rl = isqrt(lo * S)
    need(rl > 0, "sqrt argument")
    return fn_rule(x, f, (S * S) // (2 * rh), cdiv(S * S, 2 * rl))


def exp(x):
    lo, hi = x.lo(), x.hi()
    S = 1 << P

    def f(v):
        a, b = exp_iv(Fr(v, S))
        return a * S, b * S
    a_lo, a_hi = exp_iv(Fr(lo, S))[0] * S, exp_iv(Fr(hi, S))[1] * S
    return fn_rule(x, f, a_lo.numerator // a_lo.denominator, cdiv(a_hi.numerator, a_hi.denominator))


def asin(x):
    lo, hi = x.lo(), x.hi()
    S = 1 << P
    need(-S // 4 <= lo and hi <= S // 4, "asin range")

    def f(v):
        a, b = asin_iv(Fr(v, S))
        return a * S, b * S
    m = 0 if lo <= 0 <= hi else min(abs(lo), abs(hi))
    M = max(abs(lo), abs(hi))
    ym, yM = S * S - m * m, S * S - M * M
    sm = isqrt(ym)
    sm = sm if sm * sm == ym else sm + 1
    sM = isqrt(yM)
    return fn_rule(x, f, (S * S) // sm, cdiv(S * S, sM))


def ktab(base):
    tab = [base]
    for k in range(1, KR + 1):
        tab.append([tab[-1][n] - tab[-1][n + 2] for n in range(len(tab[-1]) - 2)])
    return tab


def full_coeffs():
    base = [Fr(1, 2), Fr(0)]
    for n in range(2, NB):
        base.append(base[n - 2] * (n - 1) / (n + 2))
    return ktab(base)


QFULL = full_coeffs()
FULLC = None


def init(p):
    global P, FULLC, PI4
    P = p
    FULLC = [[const(*sorted((q * PI_LO / FACT[2 * k + 1], q * PI_HI / FACT[2 * k + 1]))) for q in row]
             for k, row in enumerate(QFULL)]
    PI4 = const(PI_LO / 4, PI_HI / 4)


init(P)


def powers(x, n):
    out = [cv(1)]
    for _ in range(n):
        out.append(out[-1] * x)
    return out


def inc_table(c, w):
    w3 = w * w * w
    base = [PI4 - (c * w + asin(c)) / 2, w3 / 3]
    cp = c
    for n in range(2, NB):
        base.append((base[n - 2] * (n - 1) + cp * w3) / (n + 2))
        cp = cp * c
    return ktab(base)


def rsum_full(rp):
    return [sum((rp[k] * FULLC[k][n] for k in range(KR + 1)), cv(0)) for n in range(NMAX + 1)]


def rsum(tab, rp):
    return [sum(((rp[k] * tab[k][n]) / FACT[2 * k + 1] for k in range(KR + 1)), cv(0)) for n in range(NMAX + 1)]


def mhat(G, mp):
    return [sum(((mp[i] * G[k + i]) / FACT[i] for i in range(JS + 1)), cv(0)) for k in range(NK + 1)]


def pairs(Mh, dp, tail):
    out = []
    for n in range(3):
        e = sum(((dp[j] * Mh[n + 2 * j]) / FACT[2 * j] for j in range(JD + 1)), cv(0))
        o = sum(((dp[j] * Mh[n + 2 * j + 1]) / FACT[2 * j + 1] for j in range(JD + 1)), cv(0))
        out.append((e.widen(tail), o.widen(tail)))
    return out


def ceil_units(q):
    q = Fr(q) * (1 << P)
    return cdiv(q.numerator, q.denominator)


def phi(z):
    z2 = sq(z)
    s, p = cv(0), cv(1)
    for k in range(KR + 1):
        s = s + p / FACT[2 * k + 1]
        p = p * z2
    zh, z2h = Fr(max(z.hi(), 0), 1 << P), Fr(max(z2.hi(), 0), 1 << P)
    return s.widen(ceil_units(z2h ** (KR + 1) * cosh_hi(zh) / FACT[2 * KR + 3]))


def var(lo, hi, i):
    m, h = (lo + hi) / 2 * (1 << P), (hi - lo) / 2 * (1 << P)
    cm = m.numerator // m.denominator
    a = cdiv(h.numerator, h.denominator) + 1
    co = [0, 0, 0]
    co[i] = a
    return A(cm, co[0], co[1], co[2], 0)


def G_affine(mu, r, dlo, dhi):
    m, rr, dv = var(mu[0], mu[1], 0), var(r[0], r[1], 1), var(dlo, dhi, 2)
    d2, r2 = sq(dv), sq(rr)
    muh, rh, dh = Fr(mu[1]), Fr(r[1]), Fr(dhi)
    tail = ceil_units(2 * exp_iv(muh)[1] * cosh_hi(dh) * cosh_hi(rh) * (
        dh ** (2 * JD + 2) / FACT[2 * JD + 2] + muh ** (JS + 1) / FACT[JS + 1] + rh ** (2 * KR + 2) / FACT[2 * KR + 3]))
    rp, mp, dp = powers(r2, KR), powers(m, JS), powers(d2, JD)
    Z, X1, X2 = pairs(mhat(rsum_full(rp), mp), dp, tail)
    t = Z[1] * recip(Z[0])
    u2 = d2 * sq(t)
    S = 1 << P
    need(u2.hi() < S // 4, "atanh argument")
    a, p = cv(0), cv(1)
    for k in range(13):
        a = a + p / (2 * k + 1)
        p = p * u2
    a = a.widen(ceil_units(2 * Fr(max(u2.hi(), 0), S) ** 13))
    c = t * a
    need(c.lo() >= -(CNEG * S) and c.hi() <= S // 4, "c not in [-1/64, 1/4]")
    w = sqrt(1 - sq(c))
    N0, N1, N2 = pairs(mhat(rsum(inc_table(c, w), rp), mp), dp, tail)

    def mul(x, y):
        return (x[0] * y[0] + d2 * (x[1] * y[1]), x[0] * y[1] + x[1] * y[0])
    den = sq(Z[0]) - d2 * sq(Z[1])
    iden = recip(den)
    iz = (Z[0] * iden, -(Z[1] * iden))
    mm = mul(X1, iz)
    m2 = mul(mm, mm)
    x2 = mul(X2, iz)
    vv = (x2[0] - m2[0], x2[1] - m2[1])
    pp, aa, bb = mul(N0, iz), mul(N1, iz), mul(N2, iz)
    Uo = bb[1] - 2 * mul(mm, aa)[1] + mul(m2, pp)[1] - mul(pp, vv)[1]
    q = exp((m + dv) * c) * w * phi(rr * w) * recip(Z[0] + dv * Z[1])
    return 2 * Uo + 2 * (q * sq(mm[1])), q, c


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


def up_dec(x, dg):
    n = -((-x.numerator * 10 ** dg) // x.denominator)
    sg = "-" if n < 0 else ""
    n = abs(n)
    return sg + str(n // 10 ** dg) + "." + str(n % 10 ** dg).rjust(dg, "0")


if __name__ == "__main__":
    cnt, worst, qmax, cmin, cmax = 0, None, None, None, None
    for (ml, mh, rl, rh, dl, dh) in boxes():
        g, q, c = G_affine((ml, mh), (rl, rh), dl, dh)
        ub = g.hi()
        need(ub < 0, "box %s" % ((ml, mh, rl, rh, dl, dh),))
        cnt += 1
        worst = ub if worst is None else max(worst, ub)
        qmax = q.hi() if qmax is None else max(qmax, q.hi())
        cmin = c.lo() if cmin is None else min(cmin, c.lo())
        cmax = c.hi() if cmax is None else max(cmax, c.hi())
    need(cnt == sum(1 for i in range(NMU) if i % NPART == PART - 1) * NR * ND, "box count")
    S = 1 << P
    print("part %d of %d; P = %d; uniform grid %d x %d x %d (mu x r x d) on [0,%s]^2 x [0,%s]"
          % (PART, NPART, P, NMU, NR, ND, SIDE, DTOP))
    print("boxes checked =", cnt, "(affine enclosure of G over the whole box < 0)")
    print("largest box upper bound of G <=", up_dec(Fr(worst, S), 6))
    print("max q <=", up_dec(Fr(qmax, S), 6), "; c in [", up_dec(Fr(cmin, S), 6), ",", up_dec(Fr(cmax, S), 6), "]")
    print("CERTIFIED (part %d of %d): (*)/d < 0, hence (*) < 0, for all d > 0 with d <= %s, 0 <= mu <= %s,"
          " 0 <= r <= %s, on the mu-columns of this part; no Lipschitz or moment bound is assumed;"
          " (*) is the expression in the header" % (PART, NPART, DTOP, SIDE, SIDE))

# Exact-arithmetic port of computation #mwoe5p51-jsugdw (grid certificate, Theorem L2 #mwoe82ar-5qx8aa step 5).
# No numerical library: Python ints and fractions only.  Each real is an interval [l/2^P, h/2^P] (l, h ints),
# all rounding directed outward, so each computed interval contains the exact real value.
# Notation (post): Q_s(dx) ~ e^{sx} nu_r(x) dx on [-1,1], nu_r(x) = w phi(r w), w = sqrt(1-x^2),
# phi(z) = sinh(z)/z, s1 = mu-d, s2 = mu+d, Z(s) = int e^{sx} nu_r, m_s = E_s X, c = log(Z(s2)/Z(s1))/(2d),
#   (*) = U(s2) - U(s1) + q (m_{s2}-m_{s1})^2/(2d),  U(s) = Cov_s(1_{X>c},(X-m_s)^2),  q = e^{s2 c} nu_r(c)/Z(s2).
# CLAIM of the certificate: (*) < 0 for d in [0.13103, 0.131031], 0 <= mu, r <= 0.7872.
# This file checks the r-rows of chunk CHUNK (of NCH); L2_coverage.py checks that the chunks tile.
# Inputs NOT checked here: formula (*) (post step 3); Lipschitz bounds (post step 5) |d(*)/dmu| <= LMU = 1.17,
#   |d(*)/dr| <= LR*r = 0.474 r on the range.
# Box test (as in the original): enclosure of (*) at the box centre, d as an interval, plus
#   LMU*h_mu + LR*(r_c+h_r)*h_r  (mean value theorem; on the box r <= r_c + h_r).  Must be < 0.
from fractions import Fraction as Fr
from math import isqrt, factorial

CHUNK, NCH = 1, 1            # chunk CHUNK of NCH (rows of r); one chunk suffices
NMU, NR = 160, 80
JS, KR = 18, 7               # series degrees (as in the original)
NMAX = JS + 2
DLO, DHI = Fr(13103, 100000), Fr(131031, 1000000)
SIDE = Fr(7872, 10000)
LMU, LR = Fr(117, 100), Fr(474, 1000)
P = 104
ONE = 1 << P

def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)

def fl(q):  # floor(q*2^P) for a Fraction q
    q = Fr(q)
    return (q.numerator << P) // q.denominator

def ce(q):  # ceil(q*2^P)
    q = Fr(q)
    return -((-q.numerator << P) // q.denominator)

class V:
    # closed interval [l/2^P, h/2^P]; operations round outward (floor l, ceil h)
    __slots__ = ('l', 'h')

    def __init__(s, l, h):
        need(l <= h, "interval order")
        s.l, s.h = l, h

    def __add__(s, o): o = cv(o); return V(s.l + o.l, s.h + o.h)
    __radd__ = __add__
    def __sub__(s, o): o = cv(o); return V(s.l - o.h, s.h - o.l)
    def __rsub__(s, o): return cv(o) - s
    def __rtruediv__(s, o): return cv(o) / s
    def __neg__(s): return V(-s.h, -s.l)

    def __mul__(s, o):
        if isinstance(o, int):  # exact: integer times dyadic
            return V(s.l * o, s.h * o) if o >= 0 else V(s.h * o, s.l * o)
        o = cv(o)
        p = (s.l * o.l, s.l * o.h, s.h * o.l, s.h * o.h)
        return V(min(p) >> P, -((-max(p)) >> P))  # >> is floor division by 2^P
    __rmul__ = __mul__

    def __truediv__(s, o):
        if isinstance(o, int):
            need(o > 0, "divisor")
            return V(s.l // o, -((-s.h) // o))
        o = cv(o)
        if o.h < 0:
            return -(s / -o)
        need(o.l > 0, "division by 0")
        # 1/o in [floor(2^2P/o.h), ceil(2^2P/o.l)]/2^P, since 1/x is decreasing for x > 0
        return s * V((ONE * ONE) // o.h, -((-ONE * ONE) // o.l))

    def sq(s):  # tight square: range of x^2 over [l,h]
        a, b = s.l * s.l, s.h * s.h
        return V((0 if s.l <= 0 <= s.h else min(a, b)) >> P, -((-max(a, b)) >> P))

def cv(x):
    if isinstance(x, V):
        return x
    if isinstance(x, int):
        return V(x << P, x << P)
    return V(fl(x), ce(x))

def isq(x):
    # sqrt is increasing on [0,inf): [floor(sqrt(l 2^P)), ceil(sqrt(h 2^P))] / 2^P
    need(x.l >= 0, "sqrt of negative")
    lo = isqrt(x.l << P)
    hi = isqrt(x.h << P)
    if hi * hi < (x.h << P):
        hi += 1
    return V(lo, hi)

def pw(x, n):
    r = cv(1)
    for _ in range(n):
        r = r * x
    return r

NE = 50
EXP_R = ce(Fr(8 * 2 ** (NE + 1), factorial(NE + 1)))

def iexp(x):
    # For |a| <= 2: e^a = sum_{j<=NE} a^j/j! + R, R = e^xi a^(NE+1)/(NE+1)! (Lagrange, xi between 0 and a),
    # so |R| <= e^2 2^(NE+1)/(NE+1)! < 8*2^(NE+1)/(NE+1)! = EXP_R.  e^x is increasing, so the range over
    # [x.l, x.h] is [e^{x.l}, e^{x.h}]: evaluate the series at each endpoint and widen by EXP_R.
    need(-2 * ONE <= x.l and x.h <= 2 * ONE, "exp argument")

    def ser(a):
        a, s, t = V(a, a), cv(1), cv(1)
        for j in range(1, NE + 1):
            t = t * a / j; s = s + t
        return s
    return V(ser(x.l).l - EXP_R, ser(x.h).h + EXP_R)

NL = 40
LOG_R = ce(Fr(2 * 9, 8 * (2 * NL + 3) * 3 ** (2 * NL + 3)))

def ilog(y):
    # For 1/2 <= a <= 2: t = (a-1)/(a+1) has |t| <= 1/3 and log a = 2 sum_{k>=0} t^(2k+1)/(2k+1).
    # Tail after k = NL: |2 sum_{k>NL} t^(2k+1)/(2k+1)| <= 2|t|^(2NL+3)/((2NL+3)(1-t^2))
    #   <= 2 (1/3)^(2NL+3) (9/8)/(2NL+3) = LOG_R.  log is increasing: evaluate at the endpoints.
    need(ONE // 2 <= y.l and y.h <= 2 * ONE, "log argument")

    def ser(a):
        a = V(a, a); t = (a - 1) / (a + 1); t2, s, p = t.sq(), cv(0), t
        for k in range(NL + 1):
            s = s + p / (2 * k + 1); p = p * t2
        return s * 2
    return V(ser(y.l).l - LOG_R, ser(y.h).h + LOG_R)

def atan_fr(x, n):
    # 0 < x < 1: atan x = sum (-1)^k x^(2k+1)/(2k+1), alternating, terms decreasing: atan x lies between
    # consecutive partial sums.
    s, out = Fr(0), []
    for k in range(n + 1):
        s += Fr((-1) ** k) * x ** (2 * k + 1) / (2 * k + 1)
        out.append(s)
    return min(out[-2:]), max(out[-2:])


# Machin: pi = 16 atan(1/5) - 4 atan(1/239)
_a5, _a239 = atan_fr(Fr(1, 5), 40), atan_fr(Fr(1, 239), 20)
PI = V(fl(16 * _a5[0] - 4 * _a239[1]), ce(16 * _a5[1] - 4 * _a239[0]))
FACT = [factorial(i) for i in range(90)]
NA = 40
ASIN_C = [Fr(FACT[2 * k], 4 ** k * FACT[k] ** 2 * (2 * k + 1)) for k in range(NA + 1)]

def iasin(c):
    # 0 <= c <= 1/4: asin c = sum_k a_k c^(2k+1), a_k = (2k)!/(4^k k!^2 (2k+1)) in (0,1].  All terms are
    # >= 0 and increasing in c, so interval evaluation on [c.l, c.h] encloses the partial sum; the tail
    # sum_{k>NA} a_k c^(2k+1) is in [0, c^(2NA+3)/(1-c^2)] <= [0, (1/4)^(2NA+3)*16/15].
    need(c.l >= 0 and c.h <= ONE // 4, "asin argument")
    c2 = c.sq()
    s, p = cv(0), c
    for k in range(NA + 1):
        s = s + p * cv(ASIN_C[k]); p = p * c2
    return s + V(0, ce(Fr(16, 15 * 4 ** (2 * NA + 3))))

D = V(fl(DLO), ce(DHI))

def ktab(base):  # row k from row k-1: T[k][n] = T[k-1][n] - T[k-1][n+2], as w^2 = 1 - x^2
    tab = [base]
    for k in range(1, KR + 1):
        tab.append([tab[-1][n] - tab[-1][n + 2] for n in range(len(tab[-1]) - 2)])
    return tab

def full_table():
    # F[k][n] = int_{-1}^1 x^n w^(2k+1) dx.  F[0][0] = pi/2, F[0][1] = 0, (n+2)F[0][n] = (n-1)F[0][n-2]
    # (integration by parts), F[k][n] = F[k-1][n] - F[k-1][n+2] (w^2 = 1 - x^2).  All exact identities.
    base = [PI / 2, cv(0)]
    for n in range(2, NMAX + 2 * KR + 2):
        base.append(base[n - 2] * (n - 1) / (n + 2))
    return ktab(base)

FULL = full_table()

def inc_table(c):
    # T[k][n] = int_c^1 x^n w^(2k+1) dx (exact identities, valid for every c in [0,1/4]):
    # T[0][0] = pi/4 - (c w_c + asin c)/2, T[0][1] = w_c^3/3, (n+2)T[0][n] = (n-1)T[0][n-2] + c^(n-1) w_c^3,
    # T[k][n] = T[k-1][n] - T[k-1][n+2].  Evaluated on the interval c: inclusion-isotone, so it encloses
    # the value at the true crossing point.
    w = isq(1 - c.sq())
    w3 = w * w * w
    base = [PI / 4 - (c * w + iasin(c)) / 2, w3 / 3]
    cp = c
    for n in range(2, NMAX + 2 * KR + 2):
        base.append(((n - 1) * base[n - 2] + cp * w3) / (n + 2))
        cp = cp * c
    return ktab(base)

def rsum(tab, r2):
    # G[n] = sum_{k<=KR} r^(2k)/(2k+1)! tab[k][n]  (= integral of x^n w P_K(rw), P_K = truncated phi)
    G = []
    for n in range(NMAX + 1):
        s, p = cv(0), cv(1)
        for k in range(KR + 1):
            s = s + p * tab[k][n] / FACT[2 * k + 1]; p = p * r2
        G.append(s)
    return G

def moments(G, s, tail):
    # int_S x^n e^{sx} nu_r(x) dx, n = 0,1,2, S = [-1,1] or [c,1]: truncated double series
    # sum_{j<=JS} s^j/j! G[n+j] plus [-tail, tail] (tail justified in second_derivative).
    out = []
    for n in range(3):
        a, p = cv(0), cv(1)
        for j in range(JS + 1):
            a = a + p * G[n + j] / FACT[j]; p = p * s
        out.append(a + V(-tail, tail))
    return out

def phi_iv(z):
    # z >= 0: phi(z) = sum_k z^(2k)/(2k+1)!; tail sum_{k>KR} in [0, z^(2KR+2) cosh(z)/(2KR+3)!]
    # because (2KR+3+2j)! >= (2KR+3)! (2j)!.
    z2 = z.sq()
    s, p = cv(0), cv(1)
    for k in range(KR + 1):
        s = s + p / FACT[2 * k + 1]; p = p * z2
    e = iexp(z)
    return s + V(0, (p * (e + 1 / e) / 2 / FACT[2 * KR + 3]).h)

def second_derivative(mu, r, cache):
    mu_i, r_i = cv(mu), cv(r)
    r2 = r_i.sq()
    s2, s1 = mu_i + D, mu_i - D
    er = iexp(r_i)
    chr_ = (er + 1 / er) / 2
    smax = s2                       # mu >= 0, so |s1| <= s2
    es = iexp(smax)
    # TAIL. On [-1,1]: e^{sx} = P_J(sx)+R1, |R1| <= |s|^(J+1)e^|s|/(J+1)! (Lagrange); phi(rw) = P_K(rw)+R2,
    # 0 <= R2 <= r^(2K+2)cosh(r)/(2K+3)! (phi_iv, rw <= r). |x^n w(e^{sx}phi - P_J P_K)| = |x^n w(e^{sx}R2 + R1 P_K)|
    # <= e^|s| R2max + |R1|max cosh r (0 <= P_K <= phi(r) <= cosh r); the set has length <= 2.
    tail = (2 * (es * pw(r_i, 2 * KR + 2) * chr_ / FACT[2 * KR + 3]
                 + pw(smax, JS + 1) * es * chr_ / FACT[JS + 1])).h
    if r not in cache:
        cache.clear()
        cache[r] = rsum(FULL, r2)
    GF = cache[r]
    Z2 = moments(GF, s2, tail)
    Z1 = moments(GF, s1, tail)
    c = ilog(Z2[0] / Z1[0]) / (2 * D)
    need(c.l >= 0 and c.h <= ONE // 4, "c not in [0,1/4]")
    GI = rsum(inc_table(c), r2)
    res = []
    for s, Zs in ((s2, Z2), (s1, Z1)):
        N = moments(GI, s, tail)
        m = Zs[1] / Zs[0]
        var = Zs[2] / Zs[0] - m.sq()
        p, a, b = N[0] / Zs[0], N[1] / Zs[0], N[2] / Zs[0]
        # U(s) = E[1(X-m)^2] - p Var
        res.append((b - 2 * (m * a) + m.sq() * p - p * var, m, Zs[0]))
    w = isq(1 - c.sq())
    q = iexp(s2 * c) * w * phi_iv(r_i * w) / res[0][2]
    dm = res[0][1] - res[1][1]
    return res[0][0] - res[1][0] + q * dm.sq() / (2 * D), q, c

def rows(chunk):
    return range((chunk - 1) * NR // NCH, chunk * NR // NCH)

def boxes(chunk):
    # exact boxes (mu_lo, mu_hi, r_lo, r_hi) of chunk `chunk` (1-based)
    hmu, hr = SIDE / (2 * NMU), SIDE / (2 * NR)
    for jr in rows(chunk):
        for jm in range(NMU):
            yield (2 * jm * hmu, (2 * jm + 2) * hmu, 2 * jr * hr, (2 * jr + 2) * hr)

def up_dec(x, dg, down=False):  # decimal string >= Fraction x (<= x if down)
    n = (x.numerator * 10 ** dg) // x.denominator if down else -((-x.numerator * 10 ** dg) // x.denominator)
    sg = "-" if n < 0 else ""
    n = abs(n)
    return sg + str(n // 10 ** dg) + "." + str(n % 10 ** dg).rjust(dg, "0")

if __name__ == "__main__":
    need(cv(SIDE).l > (D * 6).h, "SIDE > 6 d")
    cache = {}
    cnt, worst, qmax, cmax, rlo, rhi = 0, -ONE, 0, 0, SIDE, 0
    for (ml, mh, rl, rh) in boxes(CHUNK):
        hmu, hr = (mh - ml) / 2, (rh - rl) / 2
        muc, rc = ml + hmu, rl + hr
        val, q, c = second_derivative(muc, rc, cache)
        ub = (val + cv(LMU * hmu + LR * (rc + hr) * hr)).h
        need(ub < 0, "box %s" % ((ml, mh, rl, rh),))
        cnt += 1
        worst, qmax, cmax = max(worst, ub), max(qmax, q.h), max(cmax, c.h)
        rlo, rhi = min(rlo, rl), max(rhi, rh)
    print("chunk %d of %d; pi in [%s, %s]" % (CHUNK, NCH, up_dec(Fr(PI.l, ONE), 15, True), up_dec(Fr(PI.h, ONE), 15)))
    print("d in [%s, %s], mu in [0, %s], r in [%s, %s]" % (DLO, DHI, SIDE, rlo, rhi))
    print("boxes checked =", cnt, "(centre enclosure + Lipschitz slack < 0)")
    print("largest box upper bound of (*) <=", up_dec(Fr(worst, ONE), 8))
    print("max q at centres <=", up_dec(Fr(qmax, ONE), 6), "; max c <=", up_dec(Fr(cmax, ONE), 6))
    print("CERTIFIED: (*) < 0 for all d in [%s, %s], mu in [0, %s], r in [%s, %s], given the Lipschitz bounds"
          " |d(*)/dmu| <= %s, |d(*)/dr| <= %s r of #mwoe82ar-5qx8aa step 5" % (DLO, DHI, SIDE, rlo, rhi, LMU, LR))

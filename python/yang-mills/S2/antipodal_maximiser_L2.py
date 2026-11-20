# Computer-assisted step of: "the antipodal pair maximises the single-link TV coefficient",
# 4D SU(2) Wilson, weight exp((beta/2) sum tr U_p).  Python 3 + mpmath interval arithmetic (iv) only.
#
# Reduction (proved in the post).  TV(vMF(m+delta), vMF(m-delta)) on S^3 = W(mu, r, d), where
# d = |delta|, mu = <m, delta>/d, r = |m - mu delta/d|, and W is the total variation distance of
# Q_{mu+d}, Q_{mu-d} in the one-dimensional family Q_s(dx) ~ e^{s x} nu_r(x) dx on [-1,1],
# nu_r(x) = w phi(r w), w = sqrt(1-x^2), phi(z) = sinh(z)/z.  With s1 = mu-d, s2 = mu+d,
# Z(s) = int e^{sx} nu_r, m_s = E_s X, c = log(Z(s2)/Z(s1))/(2d):  W = Q_{s2}(X>c) - Q_{s1}(X>c),
#   d^2 W / d mu^2 = U(s2) - U(s1) + q_{s2}(c) (m_{s2} - m_{s1})^2 / (2d),      (*)
#   U(s) = Cov_s(1_{X>c}, (X - m_s)^2),  q_s(c) = e^{sc} nu_r(c)/Z(s).
# THIS PROGRAM CERTIFIES: (*) < 0 for all d in [0.13103, 0.131031], 0 <= mu, r <= 0.7872 (> 6*0.131031).
# Method: point enclosure of (*) at box centres (d kept as an interval) plus Lipschitz bounds
# proved in the post:  |d(*)/d mu| <= LMU = 1.17,  |d(*)/d r| <= 0.474 r.
# Point enclosure: e^{sx} = sum_{j<=JS} (sx)^j/j! + R1, phi(z) = sum_{k<=KR} z^{2k}/(2k+1)! + R2,
# |R1| <= |s|^(JS+1) e^|s|/(JS+1)!, 0 <= R2 <= r^(2KR+2) cosh(r)/(2KR+3)!, and the moments
#   T[n][k] = int_c^1 x^n w^(2k+1) dx,  F[n][k] = int_{-1}^1 x^n w^(2k+1) dx  by the exact recurrences
#   T[0][0] = pi/4 - (c w_c + asin c)/2, T[1][0] = w_c^3/3, (n+2) T[n][0] = (n-1) T[n-2][0] + c^(n-1) w_c^3,
#   T[n][k] = T[n][k-1] - T[n+2][k-1]  (same for F with c = -1: F[0][0] = pi/2, F[1][0] = 0),
# asin c by its Taylor series with geometric tail (0 <= c <= 1/4 is asserted).
# Every integral over a subset of [-1,1] of the truncated series differs from the true one by at most TAIL.
from fractions import Fraction as F
from mpmath import iv

iv.prec = 80
JS, KR = 18, 7
NMAX = JS + 2
DLO, DHI = F(13103, 100000), F(131031, 1000000)
SIDE = F(7872, 10000)
LMU = F(117, 100)
LR = F(474, 1000)          # |d(*)/dr| <= LR * r


def Q(f):
    f = F(f)
    return iv.mpf(f.numerator) / f.denominator


D = iv.mpf([Q(DLO).a, Q(DHI).b])
FACT = [1]
for i in range(1, 90):
    FACT.append(FACT[-1] * i)


def full_table():
    n0 = NMAX + 2 * KR + 1
    base = [iv.pi / 2, iv.mpf(0)]
    for n in range(2, n0 + 1):
        base.append(base[n - 2] * (n - 1) / (n + 2))
    tab = [base]
    for k in range(1, KR + 1):
        prev = tab[-1]
        tab.append([prev[n] - prev[n + 2] for n in range(len(prev) - 2)])
    return tab


FULL = full_table()


def asin_iv(c):
    # 0 <= c <= 1/4
    s = iv.mpf(0)
    t = c
    for k in range(40):
        s += t * FACT[2 * k] / (4 ** k * FACT[k] ** 2 * (2 * k + 1))
        t = t * c * c
    return s + iv.mpf([0, (t / (1 - c * c)).b])


def inc_table(c):
    n0 = NMAX + 2 * KR + 1
    w = iv.sqrt(1 - c * c)
    w3 = w * w * w
    base = [iv.pi / 4 - (c * w + asin_iv(c)) / 2, w3 / 3]
    cp = c
    for n in range(2, n0 + 1):
        base.append(((n - 1) * base[n - 2] + cp * w3) / (n + 2))
        cp = cp * c
    tab = [base]
    for k in range(1, KR + 1):
        prev = tab[-1]
        tab.append([prev[n] - prev[n + 2] for n in range(len(prev) - 2)])
    return tab


def rsum(tab, r2):
    # G[n] = sum_k r^(2k)/(2k+1)! * tab[k][n], n = 0..NMAX
    G = []
    for n in range(NMAX + 1):
        s = iv.mpf(0)
        p = iv.mpf(1)
        for k in range(KR + 1):
            s += p * tab[k][n] / FACT[2 * k + 1]
            p = p * r2
        G.append(s)
    return G


def moments(G, s, tail):
    # [int x^n e^{sx} nu_r over the set], n = 0,1,2
    out = []
    for n in range(3):
        a = iv.mpf(0)
        p = iv.mpf(1)
        for j in range(JS + 1):
            a += p * G[n + j] / FACT[j]
            p = p * s
        out.append(a + iv.mpf([-tail.b, tail.b]))
    return out


def phi_iv(z):
    s = iv.mpf(0)
    p = iv.mpf(1)
    for k in range(KR + 1):
        s += p / FACT[2 * k + 1]
        p = p * z * z
    e = iv.exp(abs(z))
    return s + iv.mpf([0, (p * (e + 1 / e) / 2 / FACT[2 * KR + 3]).b])


def second_derivative(mu, r, GF_cache):
    """Enclosure of (*) at the exact rational point (mu, r), for all d in [DLO, DHI]."""
    mu_i, r_i = Q(mu), Q(r)
    r2 = r_i * r_i
    s2, s1 = mu_i + D, mu_i - D
    er = iv.exp(r_i)
    chr_ = (er + 1 / er) / 2
    smax = abs(s2)
    es = iv.exp(smax)
    tail = 2 * (es * r_i ** (2 * KR + 2) * chr_ / FACT[2 * KR + 3]
                + smax ** (JS + 1) * es * chr_ / FACT[JS + 1])
    if r not in GF_cache:
        GF_cache.clear()
        GF_cache[r] = rsum(FULL, r2)
    GF = GF_cache[r]
    Z2 = moments(GF, s2, tail)
    Z1 = moments(GF, s1, tail)
    c = iv.log(Z2[0] / Z1[0]) / (2 * D)
    if not (c.a >= 0 and c.b <= 0.25):
        raise ValueError("c out of range")
    GI = rsum(inc_table(c), r2)
    res = []
    for s, Zs in ((s2, Z2), (s1, Z1)):
        N = moments(GI, s, tail)
        m = Zs[1] / Zs[0]
        var = Zs[2] / Zs[0] - m * m
        p, a, b = N[0] / Zs[0], N[1] / Zs[0], N[2] / Zs[0]
        res.append((b - 2 * m * a + m * m * p - p * var, m, Zs[0]))
    w = iv.sqrt(1 - c * c)
    q = iv.exp(s2 * c) * w * phi_iv(r_i * w) / res[0][2]
    dm = res[0][1] - res[1][1]
    return res[0][0] - res[1][0] + q * dm * dm / (2 * D), q, c


def certify(r_lo, r_hi, nmu, nr):
    assert Q(SIDE).a > (6 * D).b
    cache = {}
    hmu = SIDE / (2 * nmu)
    hr = (r_hi - r_lo) / (2 * nr)
    worst = None
    qmax = None
    cmax = None
    count = 0
    for jr in range(nr):
        rc = r_lo + (2 * jr + 1) * hr
        slack = Q(LMU * hmu + LR * (rc + hr) * hr)
        for jm in range(nmu):
            muc = (2 * jm + 1) * hmu
            val, q, c = second_derivative(muc, rc, cache)
            ub = val + slack
            if not ub.b < 0:
                raise AssertionError("FAILED at box centre mu = " + str(muc) + ", r = " + str(rc))
            count += 1
            if worst is None or ub.b > worst:
                worst = ub.b
            if qmax is None or q.b > qmax:
                qmax = q.b
            if cmax is None or c.b > cmax:
                cmax = c.b
    return count, worst, qmax, cmax


if __name__ == "__main__":
    part = 0   # whole range in one computation
    NMU, NR, PARTS = 160, 80, 1
    lo = SIDE * (part - 1) / PARTS if part else F(0)
    hi = SIDE * part / PARTS if part else SIDE
    nr = NR // PARTS if part else NR
    count, worst, qmax, cmax = certify(lo, hi, NMU, nr)
    def ceil_dec(x, digits):
        # decimal string >= x (x a binary float taken exactly), rounded up at the given digit
        f = F(float(x)) * 10 ** digits
        n = -((-f.numerator) // f.denominator)
        sign = "-" if n < 0 else ""
        n = abs(n)
        return sign + str(n // 10 ** digits) + "." + str(n % 10 ** digits).rjust(digits, "0")

    print("d in [0.13103, 0.131031], mu in [0, 0.7872], r in [%s, %s]" % ("%.4f" % float(lo), "%.4f" % float(hi)))
    print("boxes checked =", count, " (all passed: point enclosure + Lipschitz slack < 0)")
    print("largest box upper bound of d2W/dmu2 <=", ceil_dec(worst, 8))
    print("largest q(c) at centres <=", ceil_dec(qmax, 6), "; largest c <=", ceil_dec(cmax, 6))
    print("CERTIFIED: d2W/dmu2 < 0 on this range")

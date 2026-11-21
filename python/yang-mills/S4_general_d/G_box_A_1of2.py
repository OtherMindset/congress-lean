# Exact-arithmetic certificate (Python ints and fractions only) for the rescaled second derivative
#   G(mu,r,d) := (*)/d,  (*) = d^2 W/d mu^2 as in #mwoe82ar-5qx8aa step 3,
# CLAIM: G < 0 for all DMIN <= d <= DMAX with d > 0, 0 <= mu <= SIDE, 0 <= r <= SIDE.
# Each real is an interval [l/2^P, h/2^P], rounding outward (interval core of the audited L2_exact.py).
# Notation: nu_r(x) = w phi(r w), w = sqrt(1-x^2), phi(z) = sinh(z)/z, s2 = mu+d, s1 = mu-d,
#   M_n(s) = int_{-1}^1 x^n e^{sx} nu_r dx, N_n(s) = int_c^1 (same), Z = M_0, m_s = M_1/Z, Var_s = M_2/Z - m_s^2,
#   c = log(Z(s2)/Z(s1))/(2d), U(s) = (N_2 - 2 m_s N_1 + m_s^2 N_0)/Z - (N_0/Z) Var_s, q = e^{s2 c} nu_r(c)/Z(s2),
#   (*) = U(s2) - U(s1) + q (m_{s2} - m_{s1})^2/(2d).
# Form without division by d: a PAIR (fe, fo) stands for f(s2) = fe + d fo, f(s1) = fe - d fo.
#   e^{(mu+-d)x} = e^{mu x}(cosh(dx) +- sinh(dx)), so M_n is the pair (E_n, O_n),
#     E_n = sum_j d^(2j) M_{n+2j}(mu)/(2j)!,  O_n = sum_j d^(2j) M_{n+2j+1}(mu)/(2j+1)!   (same for N_n).
#   Pairs: (a,b)(c,e) = (ac + d^2 be, ae + bc);  1/(a,b) = (a,-b)/(a^2 - d^2 b^2).
#   c = atanh(d t)/d = t sum_k (d t)^(2k)/(2k+1), t = O_0/E_0.
#   U is a pair (Ue, Uo), m a pair (me, mo): U(s2)-U(s1) = 2 d Uo, m_{s2}-m_{s1} = 2 d mo, hence
#     G = 2 Uo + 2 q mo^2.
# Box test: G is enclosed over the WHOLE box (mu, r and d all intervals; every operation below is an interval
#   extension, so the result contains G at every point of the box); the upper end must be < 0.
#   No Lipschitz bound and no moment bound is used.  Not checked here: only that (*) is the stated expression.
from fractions import Fraction as Fr
from math import isqrt, factorial

PART, NPART = 1, 2           # r-rows of part PART of NPART
NMU, NR = 160, 80
JS, JD, KR = 18, 5, 7        # series degrees: mu, d^2, r^2
NK = 2 * JD + 3              # M_0..M_NK(mu) are needed
NMAX = NK + JS
SIDE = Fr(4, 5)
SLABS = [Fr(k, 1000) for k in (0, 89, 126, 154, 178, 200)]   # slab ends in d
DMIN, DMAX = SLABS[0], SLABS[-1]
P = 104
ONE = 1 << P

def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)

def fl(q):
    q = Fr(q)
    return (q.numerator << P) // q.denominator

def ce(q):
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
        if isinstance(o, int):
            return V(s.l * o, s.h * o) if o >= 0 else V(s.h * o, s.l * o)
        o = cv(o)
        p = (s.l * o.l, s.l * o.h, s.h * o.l, s.h * o.h)
        return V(min(p) >> P, -((-max(p)) >> P))
    __rmul__ = __mul__

    def __truediv__(s, o):
        if isinstance(o, int):
            need(o > 0, "divisor")
            return V(s.l // o, -((-s.h) // o))
        o = cv(o)
        if o.h < 0:
            return -(s / -o)
        need(o.l > 0, "division by 0")
        return s * V((ONE * ONE) // o.h, -((-ONE * ONE) // o.l))

    def sq(s):
        a, b = s.l * s.l, s.h * s.h
        return V((0 if s.l <= 0 <= s.h else min(a, b)) >> P, -((-max(a, b)) >> P))

def cv(x):  # int or Fraction -> interval containing it
    if isinstance(x, V):
        return x
    if isinstance(x, int):
        return V(x << P, x << P)
    return V(fl(x), ce(x))

def isq(x):
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
    # |a| <= 2: e^a = sum_{j<=NE} a^j/j! + R, |R| <= e^2 2^(NE+1)/(NE+1)! < EXP_R; e^x increasing.
    need(-2 * ONE <= x.l and x.h <= 2 * ONE, "exp argument")

    def ser(a):
        a, s, t = V(a, a), cv(1), cv(1)
        for j in range(1, NE + 1):
            t = t * a / j; s = s + t
        return s
    return V(ser(x.l).l - EXP_R, ser(x.h).h + EXP_R)

def atan_fr(x, n):
    # 0 < x < 1: alternating series, atan x lies between consecutive partial sums
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
    # 0 <= c <= 1/4: asin c = sum a_k c^(2k+1), a_k in (0,1], terms increasing in c;
    # tail after NA in [0, c^(2NA+3)/(1-c^2)] <= [0, (1/4)^(2NA+3) 16/15]
    need(c.l >= 0 and c.h <= ONE // 4, "asin argument")
    c2 = c.sq()
    s, p = cv(0), c
    for k in range(NA + 1):
        s = s + p * cv(ASIN_C[k]); p = p * c2
    return s + V(0, ce(Fr(16, 15 * 4 ** (2 * NA + 3))))

NB = NMAX + 2 * KR + 2

def ktab(base):  # T[k][n] = T[k-1][n] - T[k-1][n+2]  (w^2 = 1 - x^2)
    tab = [base]
    for k in range(1, KR + 1):
        tab.append([tab[-1][n] - tab[-1][n + 2] for n in range(len(tab[-1]) - 2)])
    return tab

def full_table():
    # F[k][n] = int_{-1}^1 x^n w^(2k+1) dx: F[0][0] = pi/2, F[0][1] = 0, (n+2)F[0][n] = (n-1)F[0][n-2]
    base = [PI / 2, cv(0)]
    for n in range(2, NB):
        base.append(base[n - 2] * (n - 1) / (n + 2))
    return ktab(base)

FULL = full_table()

def inc_table(c):
    # T[k][n] = int_c^1 x^n w^(2k+1) dx, 0 <= c <= 1/4: T[0][0] = pi/4 - (c w_c + asin c)/2,
    # T[0][1] = w_c^3/3, (n+2)T[0][n] = (n-1)T[0][n-2] + c^(n-1) w_c^3.  Inclusion-isotone in the interval c.
    w = isq(1 - c.sq())
    w3 = w * w * w
    base = [PI / 4 - (c * w + iasin(c)) / 2, w3 / 3]
    cp = c
    for n in range(2, NB):
        base.append(((n - 1) * base[n - 2] + cp * w3) / (n + 2))
        cp = cp * c
    return ktab(base)

def rsum(tab, r2):
    # G[n] = sum_{k<=KR} r^(2k)/(2k+1)! tab[k][n] = int x^n w P_K(r w), P_K = truncated phi
    G = []
    for n in range(NMAX + 1):
        s, p = cv(0), cv(1)
        for k in range(KR + 1):
            s = s + p * tab[k][n] / FACT[2 * k + 1]; p = p * r2
        G.append(s)
    return G

def mhat(G, mu):
    # Mh[k] = sum_{i<=JS} mu^i G[k+i]/i! = int x^k P_J(mu x) w P_K(r w), k = 0..NK
    out = []
    for k in range(NK + 1):
        a, p = cv(0), cv(1)
        for i in range(JS + 1):
            a = a + p * G[k + i] / FACT[i]; p = p * mu
        out.append(a)
    return out

def pairs(Mh, d2, tail):
    # (E_n, O_n), n = 0,1,2, truncated at d^(2JD), widened by the truncation bound `tail`
    out = []
    for n in range(3):
        e, o, p = cv(0), cv(0), cv(1)
        for j in range(JD + 1):
            e = e + p * Mh[n + 2 * j] / FACT[2 * j]
            o = o + p * Mh[n + 2 * j + 1] / FACT[2 * j + 1]; p = p * d2
        out.append((e + V(-tail, tail), o + V(-tail, tail)))
    return out

def phi_iv(z):
    # z >= 0: phi(z) = sum z^(2k)/(2k+1)!; tail after KR in [0, z^(2KR+2) cosh(z)/(2KR+3)!]
    z2 = z.sq()
    s, p = cv(0), cv(1)
    for k in range(KR + 1):
        s = s + p / FACT[2 * k + 1]; p = p * z2
    e = iexp(z)
    return s + V(0, (p * (e + 1 / e) / 2 / FACT[2 * KR + 3]).h)

def G_enclosure(mu, r, dlo, dhi, cache):
    # mu = (mu_lo, mu_hi), r = (r_lo, r_hi), 0 <= mu_lo, 0 <= r_lo: encloses G on the box, for d > 0
    mu_i, r_i, dv = V(fl(mu[0]), ce(mu[1])), V(fl(r[0]), ce(r[1])), V(fl(dlo), ce(dhi))
    d2 = dv.sq()
    if cache.get('key') != (mu, r):
        er, em = iexp(r_i), iexp(mu_i)
        cache.update(key=(mu, r), r2=r_i.sq(), ch=(er + 1 / er) / 2, em=em)
        if cache.get('r') != r:
            cache.update(r=r, GF=rsum(FULL, cache['r2']))
        cache['MF'] = mhat(cache['GF'], mu_i)
    r2, chr_, em = cache['r2'], cache['ch'], cache['em']
    ed = iexp(cv(dhi))
    # TAIL. On [-1,1], with Cd = cosh(dx) or sinh(dx)/d and Cd_J its truncation (|Cd|, |Cd_J| <= cosh d,
    # |Cd - Cd_J| <= d^(2JD+2) cosh(d)/(2JD+2)!), |e^{mu x} - P_J| <= mu^(JS+1) e^mu/(JS+1)!, |P_J| <= e^mu,
    # 0 <= phi - P_K <= r^(2KR+2) cosh(r)/(2KR+3)!, 0 <= P_K <= phi(rw) <= cosh r:
    # |x^n w (Cd e^{mu x} phi - Cd_J P_J P_K)| <= e^mu cosh(d) cosh(r) (sum of the three ratios); length <= 2.
    # (the bound is increasing in mu, r, d >= 0; its interval evaluation's upper end is used)
    tail = (2 * em * (ed + 1 / ed) / 2 * chr_ * (pw(cv(dhi), 2 * JD + 2) / FACT[2 * JD + 2]
            + pw(mu_i, JS + 1) / FACT[JS + 1] + pw(r_i, 2 * KR + 2) / FACT[2 * KR + 3])).h
    Z, X1, X2 = pairs(cache['MF'], d2, tail)
    t = Z[1] / Z[0]
    u2 = d2 * t.sq()
    need(u2.h < ONE // 4, "atanh argument")
    a, p = cv(0), cv(1)
    for k in range(13):
        a = a + p / (2 * k + 1); p = p * u2
    c = t * (a + V(0, 2 * p.h))      # tail sum_{k>=13} u2^k/(2k+1) <= u2^13/(1-u2) <= 2 u2^13
    # c >= 0 when mu >= 0: Z(s2) - Z(s1) = 4 int_0^1 sinh(dx) sinh(mu x) nu_r dx >= 0 (nu_r even).
    need(c.h >= 0 and c.h <= ONE // 4, "c not in [0,1/4]")
    c = V(max(c.l, 0), c.h)
    N0, N1, N2 = pairs(mhat(rsum(inc_table(c), r2), mu_i), d2, tail)

    def mul(x, y):
        return (x[0] * y[0] + d2 * (x[1] * y[1]), x[0] * y[1] + x[1] * y[0])
    den = Z[0].sq() - d2 * Z[1].sq()
    iz = (Z[0] / den, -(Z[1] / den))
    m = mul(X1, iz)
    m2 = mul(m, m)
    x2 = mul(X2, iz)
    var = (x2[0] - m2[0], x2[1] - m2[1])
    pp, aa, bb = mul(N0, iz), mul(N1, iz), mul(N2, iz)
    Uo = bb[1] - 2 * mul(m, aa)[1] + mul(m2, pp)[1] - mul(pp, var)[1]
    w = isq(1 - c.sq())
    q = iexp((mu_i + dv) * c) * w * phi_iv(r_i * w) / (Z[0] + dv * Z[1])
    return 2 * Uo + 2 * (q * m[1].sq()), q, c

def rows(part):
    return range((part - 1) * NR // NPART, part * NR // NPART)

def boxes(part):
    # exact boxes (mu_lo, mu_hi, r_lo, r_hi, d_lo, d_hi) of part `part` (1-based)
    hmu, hr = SIDE / (2 * NMU), SIDE / (2 * NR)
    for jr in rows(part):
        for jm in range(NMU):
            for k in range(len(SLABS) - 1):
                yield (2 * jm * hmu, (2 * jm + 2) * hmu, 2 * jr * hr, (2 * jr + 2) * hr, SLABS[k], SLABS[k + 1])

def up_dec(x, dg):  # decimal string >= Fraction x
    n = -((-x.numerator * 10 ** dg) // x.denominator)
    sg = "-" if n < 0 else ""
    n = abs(n)
    return sg + str(n // 10 ** dg) + "." + str(n % 10 ** dg).rjust(dg, "0")

if __name__ == "__main__":
    need(DMIN >= 0 and all(x < y for x, y in zip(SLABS, SLABS[1:])), "slabs")
    cache = {}
    cnt, worst, qmax, cmax = 0, -ONE, 0, 0
    for (ml, mh, rl, rh, dl, dh) in boxes(PART):
        val, q, c = G_enclosure((ml, mh), (rl, rh), dl, dh, cache)
        ub = val.h
        need(ub < 0, "box %s" % ((ml, mh, rl, rh, dl, dh),))
        cnt += 1
        worst, qmax, cmax = max(worst, ub), max(qmax, q.h), max(cmax, c.h)
    print("part %d of %d; grid %d x %d (mu x r), %d slabs in d: %s" % (PART, NPART, NMU, NR, len(SLABS) - 1,
          ", ".join(str(x) for x in SLABS)))
    print("boxes checked =", cnt, "(interval enclosure of G over the whole box < 0)")
    print("largest box upper bound of G <=", up_dec(Fr(worst, ONE), 6))
    print("max q <=", up_dec(Fr(qmax, ONE), 6), "; max c <=", up_dec(Fr(cmax, ONE), 6))
    rr = [b for b in boxes(PART)]
    msg = ("CERTIFIED (part %d of %d): (*)/d < 0, hence (*) < 0, for all d > 0 with %s <= d <= %s, 0 <= mu <= %s,"
           " %s <= r <= %s; no Lipschitz or moment bound is assumed; (*) is the expression in the header")
    print(msg % (PART, NPART, DMIN, DMAX, SIDE, rr[0][2], rr[-1][3]))

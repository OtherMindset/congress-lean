# Exact-arithmetic certificate (Python ints and fractions only), with AFFINE FORMS, for the rescaled
# second derivative
#   G(mu,r,d) := (*)/d,  (*) = d^2 W/d mu^2 as in #mwoe82ar-5qx8aa step 3,
# CLAIM: G < 0 for all 0 < d <= 1/5, 0 <= mu <= 4/5, 0 <= r <= 4/5.
# The expression is the one of python/yang-mills/S4_general_d/G_box_A_1of2.py, whose header is repeated here:
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
#
# ARITHMETIC (SPEC_small_certificate_and_kernel_checker.md 2.2, with the phase 0 additions).  S = 2^P.
# An affine form A = (c, a1, a2, a3, e) of integers, e >= 0, encloses a quantity X(eps) depending on the
# point eps = (eps1, eps2, eps3) in [-1,1]^3 of the box if, for every eps,
#     | S X(eps) - (c + a1 eps1 + a2 eps2 + a3 eps3) | <= e.                                         (ENC)
# Write L = |a1|+|a2|+|a3|, R = L + e, lo = c - R, hi = c + R; then S X(eps) lies in [lo, hi] for every eps.
# The three inputs are mu = c + a1 eps1 (a2 = a3 = e = 0), likewise r (a2) and d (a3), chosen so that
# eps -> (mu, r, d) maps [-1,1]^3 ONTO a set containing the box (INPUT below).  Every operation maps forms
# satisfying (ENC) for X, Y to a form satisfying (ENC) for the result, at the same eps, with floor rounding of
# each of the four coefficients and +1 to e per rounded coefficient:
#   X + Y, X - Y, k X (integer k): coefficientwise and exact.
#   X / n (integer n > 0): coefficients floored (4 roundings), e -> ceil(e/n) + 4.
#   X Y (MUL): S^2 XY = (cx + Ax + ux)(cy + Ay + uy), A = linear part, |u| <= e, so
#     S XY = [cx cy + cx Ay + cy Ax] / S + [cx uy + cy ux + (Ax + ux)(Ay + uy)] / S,
#     second bracket <= |cx| ey + |cy| ex + (Lx + ex)(Ly + ey):  e = ceil(that / S) + 4.
#   X^2 (SQ): S^2 X^2 = cx^2 + 2 cx Ax + 2 cx ux + (Ax + ux)^2, last term in [0, Rx^2]:
#     centre floor((2 cx^2 + Rx^2) / (2S)), linear floor(2 cx a_i / S), e = ceil((Rx^2 + 4|cx| ex) / (2S)) + 4.
#   f(X) for f = 1/x, sqrt, exp, asin (FN): if alpha is a lower bound of f' on [lo/S, hi/S], g = f - alpha id is
#     nondecreasing there; if an upper bound, nonincreasing.  Either way g(X) lies between g(lo/S) and g(hi/S),
#     enclosed from enclosures of f at the two ends; f(X) = alpha X + g(X).  alpha = al/S with an integer al
#     rounded so that it remains a lower (resp. upper) bound.  Both choices are formed; the one with the smaller
#     enclosure of g is kept (either is sound).
#   A value tail t >= 0 (the true quantity is within t/S of what the form encloses, at every eps): e += ceil(t).
# Box test: hi(G) < 0, i.e. c + L + e < 0 for the form of G.  Then G < 0 at every point of the box.
# Series degrees, truncation tails, the table moments and the incomplete-moment formulas are those of
# G_box_A_1of2.py, except that c is NOT clipped to c >= 0: the closed forms for int_c^1 hold for every c in
# (-1, 1) (asin is odd), and the guard is -1/64 <= lo(c), hi(c) <= 1/4.
# No Lipschitz bound and no moment bound is used.  Not checked here: only that (*) is the stated expression.
from fractions import Fraction as Fr
from math import isqrt, factorial

PART, NPART = 1, 1
NMU, NR, ND = 8, 8, 2         # uniform grid: cells 1/10 x 1/10 x 1/10
SIDE, DTOP = Fr(4, 5), Fr(1, 5)
JS, JD, KR = 18, 5, 7         # series degrees: mu, d^2, r^2 (as G_box_A_1of2.py)
NK = 2 * JD + 3
NMAX = NK + JS
NB = NMAX + 2 * KR + 2
CNEG = Fr(1, 64)              # allowed depth of c below 0
FACT = [factorial(i) for i in range(90)]
P = 64


def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)


def cdiv(a, b):  # ceil(a / b), b > 0
    return -((-a) // b)


# ---------- elementary functions on rationals: enclosures [lo, hi] (Fractions) ----------
NE = 40
EXP_R = Fr(8 * 2 ** (NE + 1), factorial(NE + 1))


def exp_iv(q):
    # |q| <= 2: e^q = sum_{j<=NE} q^j/j! + R, |R| <= e^2 2^(NE+1)/(NE+1)! < EXP_R
    q = Fr(q)
    need(abs(q) <= 2, "exp argument")
    s, t = Fr(1), Fr(1)
    for j in range(1, NE + 1):
        t = t * q / j
        s += t
    return s - EXP_R, s + EXP_R


def cosh_hi(q):  # upper bound of cosh q, |q| <= 2
    return (exp_iv(q)[1] + exp_iv(-q)[1]) / 2


NA = 30
ASIN_C = [Fr(FACT[2 * k], 4 ** k * FACT[k] ** 2 * (2 * k + 1)) for k in range(NA + 1)]


def asin_iv(q):
    # |q| <= 1/4; for q >= 0: asin q = sum a_k q^(2k+1) + tail, tail in [0, q^(2NA+3)/(1-q^2)] (a_k <= 1);
    # q < 0 by oddness
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
PI_LO, PI_HI = 16 * _a5[0] - 4 * _a239[1], 16 * _a5[1] - 4 * _a239[0]   # Machin


# ---------- affine forms ----------
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

    def widen(s, t):  # add a value tail t >= 0 (in units of 1/S)
        need(t >= 0, "tail")
        return A(s.c, s.a1, s.a2, s.a3, s.e + t)


def const(lo, hi):
    # a constant known to lie in [lo, hi] (Fractions): centre floor(S mid), e = ceil(S half-width) + 1
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
    # f_iv(v) encloses S f(v/S) (Fractions); al_lo / al_hi: integers with al_lo/S <= f' <= al_hi/S on [lo/S, hi/S]
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
    zeta = zm.numerator // zm.denominator                      # floor: |g - zeta| <= zh + 1
    delta = cdiv(zh.numerator, zh.denominator) + 1
    y = x * A(al, 0, 0, 0, 0)                                  # (al/S) X, by MUL with an exact constant
    return A(y.c + zeta, y.a1, y.a2, y.a3, y.e + delta)


def recip(x):
    if x.hi() < 0:
        return -recip(-x)
    lo, hi = x.lo(), x.hi()
    need(lo > 0, "1/x: range contains 0")
    S = 1 << P
    # f = 1/x: S f(v/S) = S^2/v;  S f'(v/S) = -S^3/v^2, increasing in v
    return fn_rule(x, lambda v: (Fr(S * S, v), Fr(S * S, v)), -cdiv(S ** 3, lo * lo), -((S ** 3) // (hi * hi)))


def sqrt(x):
    lo, hi = x.lo(), x.hi()
    need(lo > 0, "sqrt: range not > 0")
    S = 1 << P

    def f(v):  # S sqrt(v/S) = sqrt(v S)
        a = isqrt(v * S)
        return Fr(a), Fr(a if a * a == v * S else a + 1)
    # S f'(v/S) = S^2 / (2 sqrt(v S)), decreasing in v
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
    a_lo, a_hi = exp_iv(Fr(lo, S))[0] * S, exp_iv(Fr(hi, S))[1] * S      # f' = f, increasing
    return fn_rule(x, f, a_lo.numerator // a_lo.denominator, cdiv(a_hi.numerator, a_hi.denominator))


def asin(x):
    lo, hi = x.lo(), x.hi()
    S = 1 << P
    need(-S // 4 <= lo and hi <= S // 4, "asin range")

    def f(v):
        a, b = asin_iv(Fr(v, S))
        return a * S, b * S
    # f'(y) = 1/sqrt(1 - y^2): even, increasing in |y|; m = min |y|, M = max |y| on the range
    m = 0 if lo <= 0 <= hi else min(abs(lo), abs(hi))
    M = max(abs(lo), abs(hi))
    ym, yM = S * S - m * m, S * S - M * M                     # S^2 (1 - y^2) at m and M
    sm = isqrt(ym)
    sm = sm if sm * sm == ym else sm + 1                       # >= S sqrt(1 - m^2)
    sM = isqrt(yM)                                             # <= S sqrt(1 - M^2)
    return fn_rule(x, f, (S * S) // sm, cdiv(S * S, sM))


# ---------- the evaluator (as G_box_A_1of2.py, in affine forms) ----------
def ktab(base):
    tab = [base]
    for k in range(1, KR + 1):
        tab.append([tab[-1][n] - tab[-1][n + 2] for n in range(len(tab[-1]) - 2)])
    return tab


def full_coeffs():
    # F[k][n] = int_{-1}^1 x^n w^(2k+1) dx = pi * Q[k][n] with Q rational:
    # F[0][0] = pi/2, F[0][1] = 0, (n+2) F[0][n] = (n-1) F[0][n-2];  F[k][n] = F[k-1][n] - F[k-1][n+2]
    base = [Fr(1, 2), Fr(0)]
    for n in range(2, NB):
        base.append(base[n - 2] * (n - 1) / (n + 2))
    return ktab(base)


QFULL = full_coeffs()
FULLC = None   # FULLC[k][n]: constant form enclosing F[k][n]/(2k+1)!; built by init()


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
    # T[k][n] = int_c^1 x^n w^(2k+1) dx, -1 < c < 1: T[0][0] = pi/4 - (c w_c + asin c)/2, T[0][1] = w_c^3/3,
    # (n+2) T[0][n] = (n-1) T[0][n-2] + c^(n-1) w_c^3  (from d/dx(x^(n-1) w^3) = (n-1) x^(n-2) w^3 - 3 x^n w).
    w3 = w * w * w
    base = [PI4 - (c * w + asin(c)) / 2, w3 / 3]
    cp = c
    for n in range(2, NB):
        base.append((base[n - 2] * (n - 1) + cp * w3) / (n + 2))
        cp = cp * c
    return ktab(base)


def rsum_full(rp):
    # G[n] = sum_{k<=KR} r^(2k) F[k][n]/(2k+1)!
    return [sum((rp[k] * FULLC[k][n] for k in range(KR + 1)), cv(0)) for n in range(NMAX + 1)]


def rsum(tab, rp):
    return [sum(((rp[k] * tab[k][n]) / FACT[2 * k + 1] for k in range(KR + 1)), cv(0)) for n in range(NMAX + 1)]


def mhat(G, mp):
    # Mh[k] = sum_{i<=JS} mu^i G[k+i]/i!
    return [sum(((mp[i] * G[k + i]) / FACT[i] for i in range(JS + 1)), cv(0)) for k in range(NK + 1)]


def pairs(Mh, dp, tail):
    out = []
    for n in range(3):
        e = sum(((dp[j] * Mh[n + 2 * j]) / FACT[2 * j] for j in range(JD + 1)), cv(0))
        o = sum(((dp[j] * Mh[n + 2 * j + 1]) / FACT[2 * j + 1] for j in range(JD + 1)), cv(0))
        out.append((e.widen(tail), o.widen(tail)))
    return out


def ceil_units(q):  # ceil(S q) for a Fraction q >= 0
    q = Fr(q) * (1 << P)
    return cdiv(q.numerator, q.denominator)


def phi(z):
    # z >= 0: phi(z) = sum_{k<=KR} z^(2k)/(2k+1)! + tail, tail in [0, z^(2KR+2) cosh(z)/(2KR+3)!]
    z2 = sq(z)
    s, p = cv(0), cv(1)
    for k in range(KR + 1):
        s = s + p / FACT[2 * k + 1]
        p = p * z2
    zh, z2h = Fr(max(z.hi(), 0), 1 << P), Fr(max(z2.hi(), 0), 1 << P)
    return s.widen(ceil_units(z2h ** (KR + 1) * cosh_hi(zh) / FACT[2 * KR + 3]))


def var(lo, hi, i):
    # INPUT: centre floor(S mid), coefficient ceil(S half-width) + 1, so c - a < S lo and c + a > S hi
    m, h = (lo + hi) / 2 * (1 << P), (hi - lo) / 2 * (1 << P)
    cm = m.numerator // m.denominator
    a = cdiv(h.numerator, h.denominator) + 1
    co = [0, 0, 0]
    co[i] = a
    return A(cm, co[0], co[1], co[2], 0)


def G_affine(mu, r, dlo, dhi):
    # mu = (mu_lo, mu_hi), r = (r_lo, r_hi) Fractions with 0 <= mu_lo, 0 <= r_lo, 0 <= dlo: encloses G on the box
    m, rr, dv = var(mu[0], mu[1], 0), var(r[0], r[1], 1), var(dlo, dhi, 2)
    d2, r2 = sq(dv), sq(rr)
    muh, rh, dh = Fr(mu[1]), Fr(r[1]), Fr(dhi)
    # TAIL of G_box_A_1of2.py (increasing in mu, r, d >= 0, evaluated at the upper corner): on [-1, 1] and on
    # [c, 1] (length <= 2) every E_n, O_n, and its incomplete version, is within this of its truncated series.
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
    # tail sum_{k>=13} u^k/(2k+1) in [0, u^13/(1-u)] <= [0, 2 hi(u2)^13] (0 <= u <= hi(u2) < 1/4)
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


# ---------- boxes ----------
def edges(n, top):
    return [top * i / n for i in range(n + 1)]


def boxes(part=PART, npart=NPART):
    # all cells of the uniform grid; part `part` of `npart` takes the mu-columns with index = part-1 mod npart
    em, er, ed = edges(NMU, SIDE), edges(NR, SIDE), edges(ND, DTOP)
    for i in range(NMU):
        if i % npart != part - 1:
            continue
        for j in range(NR):
            for k in range(ND):
                yield (em[i], em[i + 1], er[j], er[j + 1], ed[k], ed[k + 1])


def up_dec(x, dg):  # decimal string >= Fraction x
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
    S = 1 << P
    print("part %d of %d; P = %d; uniform grid %d x %d x %d (mu x r x d) on [0,%s]^2 x [0,%s]"
          % (PART, NPART, P, NMU, NR, ND, SIDE, DTOP))
    print("boxes checked =", cnt, "(affine enclosure of G over the whole box < 0)")
    print("largest box upper bound of G <=", up_dec(Fr(worst, S), 6))
    print("max q <=", up_dec(Fr(qmax, S), 6), "; c in [", up_dec(Fr(cmin, S), 6), ",", up_dec(Fr(cmax, S), 6), "]")
    print("CERTIFIED (part %d of %d): (*)/d < 0, hence (*) < 0, for all d > 0 with d <= %s, 0 <= mu <= %s,"
          " 0 <= r <= %s, on the mu-columns of this part; no Lipschitz or moment bound is assumed;"
          " (*) is the expression in the header" % (PART, NPART, DTOP, SIDE, SIDE))

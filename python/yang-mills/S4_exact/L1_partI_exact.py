# Exact-arithmetic port of PART I of computation #mwoe2xiu-7djqq1 (Theorem L1, #mwoe7gvj-dios46, Lemma E).
# The original used sympy for exact algebra in Q[pi, a] and mpmath iv for one inequality.  Here: polynomials
# are dicts {(deg_u, deg_a, deg_pi): Fraction} (exact), and the inequality uses outward-rounded dyadic intervals.
# Checks: (a) alpha_n = int_0^1 u w_n, beta_n = int_0^1 w_n, w_n = sqrt(1-u^2) Q_n,
#   Q_n = sum_{j+2m=n} (a u)^j (b^2 (1-u^2))^m / (j! (2m+1)!), b^2 = 1 - a^2, are (exactly)
#   alpha_0..3 = 1/3, pi a/16, (1+a^2)/30, pi a/192 and beta_0..2 = pi/4, a/3, pi/32; the k^1 and k^3
#   coefficients alpha_1 - (a/4) beta_0 and alpha_3 - (a/4) beta_2 + (a/96) beta_0 vanish; and
#   D_2 = (4/3)/8 - 4 (alpha_2 - (a/4) beta_1 + a^2/32) = (4+9a^2)/120.
#   Moments: int_0^1 u^k sqrt(1-u^2) du = 1/3 * prod_{j=3,5..k} (j-1)/(j+2) (k odd), pi/4 * prod_{j=2,4..k}
#   (j-1)/(j+2) (k even) (integration by parts, (k+2) m_k = (k-1) m_{k-2}).
# (b) 1/30 - 4 K0^2 C(K0) > 0, K0 = 23/128, C = e^s/18 + 1/128 + e^s/32 + 1/288 + pi k/3072 + sqrt2 pi e^s/48,
#   s = sqrt2 k.  With Lemma E (#mwoe7gvj-dios46, proof in the post; NOT checked here) this gives
#   M(k,q) < 4/(3pi) for 0 < k <= 23/128 and all unit q.
from fractions import Fraction as Fr
from math import isqrt, factorial
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

def padd(p, q, c=1):
    r = dict(p)
    for m, v in q.items():
        r[m] = r.get(m, 0) + c * v
    return {m: v for m, v in r.items() if v != 0}

def pmul(p, q):
    r = {}
    for (a1, b1, c1), v in p.items():
        for (a2, b2, c2), w in q.items():
            m = (a1 + a2, b1 + b2, c1 + c2)
            r[m] = r.get(m, 0) + v * w
    return {m: v for m, v in r.items() if v != 0}

def ppow(p, n):
    r = {(0, 0, 0): Fr(1)}
    for _ in range(n):
        r = pmul(r, p)
    return r

def mom(k):  # int_0^1 u^k sqrt(1-u^2) du as a polynomial in pi
    if k % 2:
        r = Fr(1, 3)
        for j in range(3, k + 1, 2):
            r *= Fr(j - 1, j + 2)
        return {(0, 0, 0): r}
    r = Fr(1, 4)
    for j in range(2, k + 1, 2):
        r *= Fr(j - 1, j + 2)
    return {(0, 0, 1): r}

def integ(p):  # int_0^1 sqrt(1-u^2) p(u) du; result has no u
    r = {}
    for (eu, ea, ep), v in p.items():
        for (_, _, mp), w in mom(eu).items():
            m = (0, ea, ep + mp)
            r[m] = r.get(m, 0) + v * w
    return {m: v for m, v in r.items() if v != 0}

U, A_, PI_ = {(1, 0, 0): Fr(1)}, {(0, 1, 0): Fr(1)}, {(0, 0, 1): Fr(1)}
ONE_ = {(0, 0, 0): Fr(1)}
def cst(c, p=ONE_): return {m: c * v for m, v in p.items()}

B2 = padd(ONE_, pmul(A_, A_), -1)                 # b^2 = 1 - a^2
W2 = padd(ONE_, pmul(U, U), -1)                   # 1 - u^2
Qs = []
for n in range(4):
    q = {}
    for j in range(n + 1):
        if (n - j) % 2 == 0:
            m = (n - j) // 2
            t = pmul(ppow(pmul(A_, U), j), ppow(pmul(B2, W2), m))
            q = padd(q, cst(Fr(1, factorial(j) * factorial(2 * m + 1)), t))
    Qs.append(q)
al = [integ(pmul(U, q)) for q in Qs]
be = [integ(q) for q in Qs[:3]]
ea = [cst(Fr(1, 3)), cst(Fr(1, 16), pmul(PI_, A_)), cst(Fr(1, 30), padd(ONE_, pmul(A_, A_))),
      cst(Fr(1, 192), pmul(PI_, A_))]
eb = [cst(Fr(1, 4), PI_), cst(Fr(1, 3), A_), cst(Fr(1, 32), PI_)]
need(all(padd(x, y, -1) == {} for x, y in zip(al + be, ea + eb)), "alpha/beta")
print("alpha_0..3 = 1/3, pi a/16, (1+a^2)/30, pi a/192 ; beta_0..2 = pi/4, a/3, pi/32 (exact, checked)")
c1 = cst(Fr(1, 4), A_)
k1 = padd(al[1], pmul(c1, be[0]), -1)
k3 = padd(padd(al[3], pmul(c1, be[2]), -1), pmul(cst(Fr(1, 96), A_), be[0]))
D2 = padd(cst(Fr(1, 6)), cst(-4, padd(padd(al[2], pmul(c1, be[1]), -1), cst(Fr(1, 32), pmul(A_, A_)))))
need(k1 == {} and k3 == {} and padd(D2, cst(Fr(1, 120), padd(cst(4), cst(9, pmul(A_, A_)))), -1) == {}, "k1,k3,D2")
print("k^1 coefficient = 0, k^3 coefficient = 0, D_2 = (4+9a^2)/120 (exact, checked)")

def dec(x, dg, up):
    n = -((-x.numerator * 10 ** dg) // x.denominator) if up else (x.numerator * 10 ** dg) // x.denominator
    return str(n // 10 ** dg) + "." + str(n % 10 ** dg).rjust(dg, "0")

K0 = Fr(23, 128)
k = cv(K0)
r2 = isq(cv(2))
e = iexp(r2 * k)
C = e / 18 + cv(Fr(1, 128)) + e / 32 + cv(Fr(1, 288)) + PI * k / 3072 + r2 * PI * e / 48
g = cv(Fr(1, 30)) - 4 * (k.sq() * C)
print("C(K0) <=", dec(Fr(C.h, ONE), 6, 1), "; 1/30 - 4 K0^2 C(K0) >=", dec(Fr(g.l, ONE), 6, 0))
need(g.l > 0, "Part I inequality")
print("CERTIFIED: the Lemma E coefficient identities hold exactly and 1/30 - 4 K0^2 C(K0) > 0 for K0 = 23/128;"
      " with Lemma E (#mwoe7gvj-dios46) M(k,q) < 4/(3pi) for 0 < k <= 23/128, all unit q")

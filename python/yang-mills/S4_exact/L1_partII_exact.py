# Exact-arithmetic port of PART II of computation #mwoe2xiu-7djqq1 (Theorem L1, #mwoe7gvj-dios46: M* = 4/(3pi)),
# including the point enclosure of M taken from #mwo53bqy-nzojc8 (functions bessel_ZA, Mval, Gk, Gp there).
# No numerical library: Python ints and fractions only.  Each real is an interval [l/2^P, h/2^P] (l, h ints),
# all rounding directed outward, so each computed interval contains the exact real value.
# M(k,phi) = E_k |<U - EU, q>|, U ~ vMF on S^3 with density ~ exp(k U_1), q = (cos phi, sin phi, 0, 0).
# CLAIM: M(k,phi) < 4/(3pi) for all k in [23/128, 805/1024], phi in [0, 1609/1024] (> pi/2; M depends on
#   |cos phi| only, so this covers every unit q).
# Inputs NOT checked here: (i) the 1D reduction (#mwgwy6p5-r99mia, re-derived in #mwo6ggkf-xb5ojn [R]):
#   Z M = int_{-1}^1 e^{kx} w H(a(x-A), b w) dx, w = sqrt(1-x^2), a = |cos phi|, b = sin phi, Z = pi I1(k)/k,
#   A = I2/I1, H(t,s) = |t| if |t| >= s, (t^2+s^2)/(2s) if |t| < s; the band |t| < s is u- < x < u+,
#   u+- = a^2 A +- b sqrt(1 - a^2 A^2).  (ii) Lemma K |dM/dk| <= k Gk(k), Gk increasing, and Lemma P
#   |dM/dphi| <= k^2 Gp(k)  (#mwo6ggkf-xb5ojn).  Box bound (as in the original): M(kc,pc) + hk*kh*Gk(kh)
#   + hp*kc^2*Gp(kc) (move in phi at k = kc, then in k), required < 4/(3pi).  Same bisection rule as the
#   original; coverage of the rectangle by the accepted boxes is proved separately by L1_coverage.py, which
#   decodes the split tree whose fingerprint this file prints.
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
NT = 60
TRIG_R = ce(Fr(2 ** (NT + 1), FACT[NT + 1]))
ATAN_R = ce(Fr(4, 3 * 2 ** (2 * NT + 3)))

def icos_sin(x):
    # 0 <= x <= 2, x a Fraction: cos x = sum_{k} (-1)^k x^(2k)/(2k)!, sin x likewise; Taylor polynomial of
    # degree NT plus Lagrange remainder |R| <= |x|^(NT+1)/(NT+1)! <= 2^(NT+1)/(NT+1)! = TRIG_R (|cos^(n)|, |sin^(n)| <= 1)
    need(0 <= x <= 2, "trig argument")
    xv = cv(x)
    c, s, t = cv(0), cv(0), cv(1)
    for n in range(NT + 1):
        if n % 4 == 0: c = c + t
        elif n % 4 == 1: s = s + t
        elif n % 4 == 2: c = c - t
        else: s = s - t
        t = t * xv / (n + 1)
    return c + V(-TRIG_R, TRIG_R), s + V(-TRIG_R, TRIG_R)

def iasin(u):
    # -1 <= u <= 1.  asin u = 2 atan(y), y = u/(1+sqrt(1-u^2)) (tan(t/2) = sin t/(1+cos t), cos(asin u) >= 0),
    # |y| <= 1; atan y = 2 atan(z), z = y/(1+sqrt(1+y^2)) (same identity), |z| <= tan(pi/8) < 1/2.
    # atan z = sum_{k<=NT} (-1)^k z^(2k+1)/(2k+1) + R, |R| <= sum_{k>NT} |z|^(2k+1) <= (1/2)^(2NT+3)(4/3) = ATAN_R.
    # asin is increasing: evaluate at both endpoints of u.
    need(-ONE <= u.l and u.h <= ONE, "asin argument")

    def pt(a):
        a = V(a, a)
        y = a / (1 + isq(1 - a.sq()))
        z = y / (1 + isq(1 + y.sq()))
        need(-ONE // 2 <= z.l and z.h <= ONE // 2, "z range")
        z2, s, p = z.sq(), cv(0), z
        for k in range(NT + 1):
            s = s + p / (2 * k + 1) if k % 2 == 0 else s - p / (2 * k + 1)
            p = p * z2
        return (s + V(-ATAN_R, ATAN_R)) * 4
    return V(pt(u.l).l, pt(u.h).h)

NS = 22
T0 = 4 / (3 * PI)

def bessel_ZA(k):
    # y = k^2/4 <= 1/6.  Z/pi = I1(k)/k = sum_m y^m/(2 m!(m+1)!), I2(k) = sum_m y^(m+1)/(m!(m+2)!) (positive
    # series).  Both terms with index m are <= y^m/(m!)^2, and sum_{m>=16} y^m/(m!)^2 <= 2 y^16/(16!)^2 (ratio
    # y/(m+1)^2 <= 1/2).  Hence tails in [0, 2 y^16/(16!)^2].  Returns Z = pi I1/k and A = I2/I1.
    y = k.sq() / 4
    need(y.h <= ONE // 6, "y <= 1/6")
    s1, s2, t = cv(0), cv(0), cv(1)
    for m in range(16):
        s1 = s1 + t / (2 * (m + 1))
        s2 = s2 + y * t / ((m + 1) * (m + 2))
        t = t * y / ((m + 1) ** 2)
    tb = V(0, (t * 2).h)
    s1, s2 = s1 + tb, s2 + tb
    return PI * s1, s2 / (k * s1)

def Mval(kc, ph):
    # Z M = sum_{n<=NS} k^n/n! int x^n w H + R: outside the band H w = a|x-A| w, inside it H w =
    # (a^2(x-A)^2 + b^2(1-x^2))/(2b) (a polynomial); |R| <= (k^(NS+1) e^k/(NS+1)!) int w H <= that * 5, since
    # e^{kx} - P_NS(kx) is bounded by Lagrange and int w H <= 3 int w = 3pi/2 < 5 (H <= |t| + s <= 3).
    k = cv(kc)
    ca, b = icos_sin(ph)
    a = ca if ca.l > 0 else -ca
    need(a.l > 0 and b.l > 0, "a,b")
    Z, A = bessel_ZA(k)
    r = isq(1 - (a * A).sq())
    up = a.sq() * A + b * r
    um = a.sq() * A - b * r
    N = NS + 3

    def Jall(u):
        # J_n(u) = int_{-1}^u x^n w dx: J_0 = (u w_u + pi/2 + asin u)/2, J_1 = -w_u^3/3,
        # (n+2) J_n = (n-1) J_{n-2} - u^(n-1) w_u^3 (integration by parts); exact identities
        w = isq(1 - u.sq())
        w3 = w * w * w
        J = [(u * w + PI / 2 + iasin(u)) / 2, -(w3 / 3)]
        un = cv(1)
        for n in range(2, N + 1):
            J.append(((n - 1) * J[n - 2] - un * u * w3) / (n + 2))
            un = un * u
        return J
    Jp, Jm = Jall(up), Jall(um)
    J1 = [cv(0)] * (N + 1)  # J_n(1): pi/2, 0, (n+2) J_n(1) = (n-1) J_{n-2}(1)
    J1[0] = PI / 2
    for n in range(2, N + 1, 2):
        J1[n] = J1[n - 2] * (n - 1) / (n + 2)
    # int_{u-}^{u+} x^m dx/(2b) = r S_m/(m+1), S_m = sum_j u+^j u-^(m-j), as u+ - u- = 2 b r
    S, upw = [cv(1)], cv(1)
    for j in range(1, N + 1):
        upw = upw * up
        S.append(upw + um * S[-1])
    c2 = a.sq() - b.sq()
    c1 = -2 * (a.sq() * A)
    c0 = (a * A).sq() + b.sq()
    tot, kn = cv(0), cv(1)
    for n in range(NS + 1):
        out = a * ((J1[n + 1] - Jp[n + 1]) - A * (J1[n] - Jp[n]) - Jm[n + 1] + A * Jm[n])
        band = r * (c2 * S[n + 2] / (n + 3) + c1 * S[n + 1] / (n + 2) + c0 * S[n] / (n + 1))
        tot = tot + kn * (out + band)
        kn = kn * k / (n + 1)
    tb = (kn * iexp(k) * 5).h
    return (tot + V(-tb, tb)) / Z

def Gk(k):
    k = cv(k); e = iexp(k); ch = (e + 1 / e) / 2
    return ch * isq(e) / 8 + e / 4 + (e / 4) * (4 * ch / (3 * PI) + e * ch / PI)

def Gp(k):
    k = cv(k); e = iexp(k); ch = (e + 1 / e) / 2
    return (ch / (3 * PI) + 4 * e / (15 * PI) + k * e * ch / 48
            + (ch / 4) * (4 * ch / (3 * PI) + e * ch / PI))


def part_two(k0, kmax, pmax):
    # same depth-first bisection as the original; fp = base-3 fingerprint mod 2^61-1 of the symbol sequence
    # (0 accept, 1 split k, 2 split phi) in pop order, compared with L1_coverage.py
    T = T0.l
    stack = [(Fr(k0), kmax, Fr(0), pmax)]
    acc = ev = fp = 0
    worst, area = None, Fr(0)
    while stack:
        kl, kh, pl, ph = stack.pop()
        hk, hp = (kh - kl) / 2, (ph - pl) / 2
        kc, pc = kl + hk, pl + hp
        m = Mval(kc, pc)
        ev += 1
        ekI = cv(hk * kh) * Gk(kh)
        epI = cv(hp * kc * kc) * Gp(kc)
        ub = (m + ekI + epI).h
        if ub < T:
            sym, acc = 0, acc + 1
            area += (kh - kl) * (ph - pl)
            worst = ub if worst is None else max(worst, ub)
        elif ekI.h >= epI.h:
            sym = 1
            need(hk > Fr(1, 2 ** 40), "too deep")
            stack += [(kl, kc, pl, ph), (kc, kh, pl, ph)]
        else:
            sym = 2
            need(hp > Fr(1, 2 ** 40), "too deep")
            stack += [(kl, kh, pl, pc), (kl, kh, pc, ph)]
        fp = (fp * 3 + sym) % ((1 << 61) - 1)
    return acc, ev, worst, fp, area

def dec(x, dg, up):  # decimal string of the Fraction x, rounded up or down
    n = -((-x.numerator * 10 ** dg) // x.denominator) if up else (x.numerator * 10 ** dg) // x.denominator
    return str(n // 10 ** dg) + "." + str(n % 10 ** dg).rjust(dg, "0")

if __name__ == "__main__":
    K0, KMAX, PMAX = Fr(23, 128), Fr(805, 1024), Fr(1609, 1024)
    need(cv(KMAX).l > (PI / 4).h and cv(PMAX).l > (PI / 2).h, "range")
    print("pi in [%s, %s]; 4/(3pi) in [%s, %s]" % (dec(Fr(PI.l, ONE), 15, 0), dec(Fr(PI.h, ONE), 15, 1),
          dec(Fr(T0.l, ONE), 12, 0), dec(Fr(T0.h, ONE), 12, 1)))
    acc, ev, worst, fp, area = part_two(K0, KMAX, PMAX)
    need(area == (KMAX - K0) * PMAX, "area of accepted boxes")
    print("rectangle [23/128, 805/1024] x [0, 1609/1024]: boxes accepted =", acc, "; evaluations =", ev)
    print("exact total area of accepted boxes = area of the rectangle =", area)
    print("split-tree fingerprint =", fp)
    print("max box upper bound <=", dec(Fr(worst, ONE), 10, 1), "< 4/(3pi) >=", dec(Fr(T0.l, ONE), 10, 0))
    print("CERTIFIED: M(k,q) < 4/(3pi) for all k in [23/128, 805/1024] and all unit q, given the reduction of"
          " #mwgwy6p5-r99mia and Lemmas K, P of #mwo6ggkf-xb5ojn")

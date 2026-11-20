# M* = 4/(3pi) EXACTLY: E_k|<U-EU,q>| <= 4/(3pi) for all k in [0, 805/1024] (> pi/4) and all unit q,
# U ~ vMF on S^3 with density ~ exp(k U_1).  Hence single-link Dobrushin for 4D SU(2) Wilson LGT
# (weight exp((beta/2) sum tr U_p)) holds for every beta < pi/24, and pi/24 is the exact limit of the
# M-method (M = 4/(3pi) at k = 0).  Claude Yang-Mills team (Claude Opus 5.5), Session 2, target L1.
# Python 3 + mpmath iv + sympy (exact polynomial algebra only); no files, no randomness, no timings.
#
# PART I (k in [0, K0], K0 = 23/128), Lemma E (proof in README / post):
#   With a = |q_1|, b^2 = 1 - a^2, the law of S = <U,q> has density F/Z_B on [-1,1],
#   F(u) = 2 sqrt(1-u^2) e^{kau} Sh(k^2 b^2 (1-u^2)), Sh(z) = sum z^m/(2m+1)!, Z_B = pi sum q^m/(m!(m+1)!),
#   q = k^2/4, c = <EU,q> = a A, A = I2/I1.  M = (2/Z_B) int_c^1 (u-c) F du.  Writing
#   e^{kau} Sh(..) = sum_n k^n Q_n(u), w_n = sqrt(1-u^2) Q_n, alpha_n = int_0^1 u w_n, beta_n = int_0^1 w_n:
#   D := Z_B (4/(3pi) - M) >= k^2 [ (4+9a^2)/120 - 4 k^2 C(k) ],
#   C(k) = e^s/18 + 1/128 + e^s/32 + 1/288 + pi k/3072 + sqrt2 pi e^s/48,  s = sqrt2 k.
#   This code checks (a) the exact coefficients alpha_0..3, beta_0..2, the vanishing of the k^1 and k^3
#   coefficients and D_2 = (4+9a^2)/120 (exact algebra in Q[pi, a]); (b) 1/30 - 4 K0^2 C(K0) > 0.
#   Then D > 0, i.e. M < 4/(3pi), for 0 < k <= K0, all a; M = 4/(3pi) at k = 0.
# PART II (k in [K0, 805/1024], phi in [0, 1609/1024]): rigorous point enclosure of M (Session 1
#   certificate #mwo53bqy-nzojc8) + Lemmas K, P; every box bound must be < 4/(3pi) (strict).
from fractions import Fraction as F
import mpmath as mpm
from mpmath import iv, mpf

iv.prec = 80
PI = iv.pi
T0 = 4 / (3 * PI)
NS = 22


def Q(f):
    f = F(f)
    return iv.mpf(f.numerator) / f.denominator


def frac(x):
    m, e = mpf(x).man_exp
    return F(m) * F(2) ** e if e >= 0 else F(m, 2 ** (-e))


def dec(x, d, up):
    f = frac(x.b if up else x.a) * 10 ** d
    n = -((-f.numerator) // f.denominator) if up else f.numerator // f.denominator
    s = str(n).rjust(d + 1, "0")
    return s[:-d] + "." + s[-d:]


def encl(x, d=10):
    return "[" + dec(x, d, False) + ", " + dec(x, d, True) + "]"


def ivacos(u):
    m = max(mpf(-1), min(mpf(1), mpf(u.mid)))
    k = int(mpm.nint(mpm.acos(m) * 2 ** 44))  # deterministic software guess, verified below
    tl = Q(F(k - 16, 2 ** 44))
    th = Q(F(k + 16, 2 ** 44))
    if not (tl.a >= 0 and iv.cos(tl).a >= u.b and iv.cos(th).b <= u.a and th.b < PI.a):
        raise ValueError("acos enclosure failed")
    return iv.mpf([tl.a, th.b])


def bessel_ZA(k):
    # Z/pi = I1(k)/k = sum y^m/(2 m!(m+1)!), I2(k) = sum y^(m+1)/(m!(m+2)!), y = k^2/4 <= 1/6
    y = (k / 2) ** 2
    s1 = iv.mpf(0)
    s2 = iv.mpf(0)
    t = iv.mpf(1)
    for m in range(16):
        s1 += t / (2 * (m + 1))
        s2 += y * t / ((m + 1) * (m + 2))
        t = t * y / (m + 1) ** 2
    tb = 2 * t  # both tails <= sum_{m>=16} y^m/(m!)^2 <= 2 y^16/(16!)^2
    s1 = s1 + iv.mpf([0, tb.b])
    s2 = s2 + iv.mpf([0, tb.b])
    return PI * s1, s2 / (k * s1)


def Mval(kc, ph):
    k = Q(kc)
    p = Q(ph)
    a = abs(iv.cos(p))
    b = iv.sin(p)
    if not (a.a > 0 and b.a > 0):
        raise ValueError("a,b")
    Z, A = bessel_ZA(k)
    r = iv.sqrt(1 - a * a * A * A)
    up = a * a * A + b * r
    um = a * a * A - b * r
    N = NS + 3

    def Jall(u):
        w = iv.sqrt(1 - u * u)
        w3 = w * w * w
        J = [(u * w + PI - ivacos(u)) / 2, -w3 / 3]
        un = iv.mpf(1)
        for n in range(2, N + 1):
            J.append(((n - 1) * J[n - 2] - un * u * w3) / (n + 2))
            un = un * u
        return J

    Jp = Jall(up)
    Jm = Jall(um)
    J1 = [iv.mpf(0)] * (N + 1)
    J1[0] = PI / 2
    for n in range(2, N + 1, 2):
        J1[n] = J1[n - 2] * (n - 1) / (n + 2)
    S = [iv.mpf(1)]
    upw = iv.mpf(1)
    for j in range(1, N + 1):
        upw = upw * up
        S.append(upw + um * S[-1])
    c2 = a * a - b * b
    c1 = -2 * a * a * A
    c0 = a * a * A * A + b * b
    tot = iv.mpf(0)
    kn = iv.mpf(1)
    for n in range(NS + 1):
        out = a * ((J1[n + 1] - Jp[n + 1]) - A * (J1[n] - Jp[n]) - Jm[n + 1] + A * Jm[n])
        band = r * (c2 * S[n + 2] / (n + 3) + c1 * S[n + 1] / (n + 2) + c0 * S[n] / (n + 1))
        tot += kn * (out + band)
        kn = kn * k / (n + 1)
    tb = kn * iv.exp(k) * 5
    tot = tot + iv.mpf([-tb.b, tb.b])
    return tot / Z


def Gk(k):
    k = Q(k)
    e = iv.exp(k)
    ch = (e + 1 / e) / 2
    return ch * iv.sqrt(e) / 8 + e / 4 + (e / 4) * (4 * ch / (3 * PI) + e * ch / PI)


def Gp(k):
    k = Q(k)
    e = iv.exp(k)
    ch = (e + 1 / e) / 2
    return (ch / (3 * PI) + 4 * e / (15 * PI) + k * e * ch / 48
            + (ch / 4) * (4 * ch / (3 * PI) + e * ch / PI))



import sympy as sp


def part_one(K0):
    u, a, P = sp.symbols('u a P')  # P stands for pi
    b2 = 1 - a ** 2

    def mom(k):  # int_0^1 u^k sqrt(1-u^2) du, exact in Q[P]
        if k % 2:
            r = sp.Rational(1, 3)
            for j in range(3, k + 1, 2):
                r = r * sp.Rational(j - 1, j + 2)
            return r
        r = P / 4
        for j in range(2, k + 1, 2):
            r = r * sp.Rational(j - 1, j + 2)
        return r

    def integ(poly):  # int_0^1 sqrt(1-u^2) poly(u) du
        p = sp.Poly(sp.expand(poly), u)
        return sp.expand(sum(cf * mom(mon[0]) for mon, cf in zip(p.monoms(), p.coeffs())))

    Qs = []
    for n in range(4):
        Qs.append(sum((a * u) ** j / sp.factorial(j) * (b2 * (1 - u ** 2)) ** ((n - j) // 2)
                      / sp.factorial(n - j + 1) for j in range(n + 1) if (n - j) % 2 == 0))
    al = [sp.factor(integ(u * Qn)) for Qn in Qs]
    be = [sp.factor(integ(Qn)) for Qn in Qs[:3]]
    ea = [sp.Rational(1, 3), P * a / 16, (1 + a ** 2) / 30, P * a / 192]
    eb = [P / 4, a / 3, P / 32]
    assert all(sp.expand(x - y) == 0 for x, y in zip(al + be, ea + eb))
    print("alpha_0..3 = 1/3, pi a/16, (1+a^2)/30, pi a/192 ; beta_0..2 = pi/4, a/3, pi/32 (exact, asserted)")
    c1 = a / 4
    c3 = -a / 96
    k1 = sp.expand(al[1] - c1 * be[0])
    k3 = sp.expand(al[3] - c1 * be[2] - c3 * be[0])
    D2 = sp.factor(sp.Rational(4, 3) / 8 - 4 * (al[2] - c1 * be[1] + a ** 2 / 32))
    assert k1 == 0 and k3 == 0 and sp.expand(D2 - (4 + 9 * a ** 2) / 120) == 0
    print("k^1 coefficient = 0, k^3 coefficient = 0, D_2 = (4+9a^2)/120 (exact, asserted)")
    k = Q(K0)
    s = iv.sqrt(2) * k
    e = iv.exp(s)
    C = e / 18 + Q(F(1, 128)) + e / 32 + Q(F(1, 288)) + PI * k / 3072 + iv.sqrt(2) * PI * e / 48
    g = Q(F(1, 30)) - 4 * k * k * C
    print("C(K0) <=", dec(C, 6, True), "; 1/30 - 4 K0^2 C(K0) >=", dec(g, 6, False))
    assert g.a > 0
    print("PART I CERTIFIED: M(k,q) < 4/(3pi) for 0 < k <= %s, all unit q" % K0)


def part_two(k0, kmax, pmax):
    T = T0
    stack = [(F(k0), kmax, F(0), pmax)]
    acc = 0
    ev = 0
    worst = None
    while stack:
        kl, kh, pl, ph = stack.pop()
        hk = (kh - kl) / 2
        hp = (ph - pl) / 2
        kc = kl + hk
        pc = pl + hp
        m = Mval(kc, pc)
        ev += 1
        ekI = Q(hk * kh) * Gk(kh)
        epI = Q(hp * kc * kc) * Gp(kc)
        ub = m + ekI + epI
        if ub.b < T.a:
            acc += 1
            if worst is None or ub.b > worst.b:
                worst = ub
        elif ekI.b >= epI.b:
            km = kl + hk
            stack += [(kl, km, pl, ph), (km, kh, pl, ph)]
        else:
            pm = pl + hp
            stack += [(kl, kh, pl, pm), (kl, kh, pm, ph)]
    return acc, ev, worst


if __name__ == "__main__":
    K0 = F(23, 128)
    KMAX = F(805, 1024)
    PMAX = F(1609, 1024)
    assert Q(KMAX).a > (PI / 4).b and Q(PMAX).a > (PI / 2).b
    print("4/(3pi) in", encl(T0, 12))
    part_one(K0)
    for (k, p) in [(F(1, 100), F(1, 1000)), (F(1, 100), F(157, 100))]:
        Mk = Mval(k, p)
        kk = Q(k)
        Zb = 2 * bessel_ZA(kk)[0]
        print("check: Z_B(4/(3pi)-M)/k^2 at (k,phi)=(%s,%s) in %s" % (k, p, encl(Zb * (T0 - Mk) / (kk * kk), 4)))
    acc, ev, worst = part_two(K0, KMAX, PMAX)
    print("PART II: rectangle [23/128, 805/1024] x [0, 1609/1024]: boxes =", acc, " evaluations =", ev)
    print("  max box upper bound <=", dec(worst, 10, True), " < 4/(3pi) >=", dec(T0, 10, False))
    print("PART II CERTIFIED: M(k,q) < 4/(3pi) for 23/128 <= k <= 805/1024, all unit q")
    print("THEOREM: M* = sup_{k in [0,pi/4], |q|=1} M = 4/(3pi) (attained at k = 0)")
    beta = PI / 24
    print("single-link Dobrushin row sum 18 beta M* = 24 beta/pi < 1 for all beta < pi/24 =", dec(beta, 9, False) + "...;",
          "6 pi/24 = pi/4 <= 805/1024:", (6 * beta).b <= Q(KMAX).a)

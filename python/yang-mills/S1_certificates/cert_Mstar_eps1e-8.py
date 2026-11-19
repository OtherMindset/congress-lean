# RIGOROUS BOUND M* <= 4/(3pi) + 1e-8 FOR THE SINGLE-LINK DOBRUSHIN CONSTANT, 4D SU(2) WILSON LGT
# Claude council, route lead A (Claude Opus 5.5), 19 Nov 2026: runner-compatible repair of #mwgxxt58-i27s3c.
# Pure Python 3 + mpmath interval arithmetic (mpmath.iv); no python-flint, no files, no randomness.
#
# M(k,phi) = E_k |<U - EU, q>|, U ~ vMF on S^3, density ~ exp(k U_1), q = (cos phi, sin phi, 0, 0).
# M* = sup over k in [0, 805/1024] (> pi/4), phi in [0, 1609/1024] (> pi/2); M depends on |cos phi| only.
#
# (1) Point enclosure (exact 1D reduction of #mwgwy6p5-r99mia, x = U_1, a = |cos phi|, b = sin phi):
#   Z M = int_{-1}^{1} e^{kx} h(x) dx,  h = sqrt(1-x^2) H(a(x-A), b sqrt(1-x^2)),
#   H(t,s) = |t| (|t|>=s), (t^2+s^2)/(2s) (|t|<s); band |t|<s is u- < x < u+,
#   u+- = a^2 A +- b r, r = sqrt(1 - a^2 A^2).  Z = pi I1(k)/k, A = I2(k)/I1(k) by their
#   power series (positive terms, explicit geometric tail).  Expand e^{kx} = sum_{n<=22} (kx)^n/n! + R,
#   |R| <= k^23 e^k/23!, int|h| <= 3pi/2 < 5.  Moments are closed forms:
#   J_n(u) = int_{-1}^u x^n sqrt(1-x^2) dx:  J_0 = (u sqrt(1-u^2) + pi - acos u)/2,
#   J_1 = -(1-u^2)^{3/2}/3,  (n+2) J_n = (n-1) J_{n-2} - u^{n-1} (1-u^2)^{3/2};
#   band: int_{u-}^{u+} x^n (a^2(x-A)^2 + b^2(1-x^2))/(2b) dx, with
#   int_{u-}^{u+} x^m dx /(2b) = r S_m/(m+1), S_m = sum_j u+^j u-^(m-j) (no cancellation).
#   acos is enclosed by verifying cos at two dyadic points (guess from mpmath.acos) with interval cos (cos decreasing on [0,pi]).
# (2) Derivative lemmas (proofs in the companion attempt post; self-contained, no Amos bounds needed):
#   Lemma K: |dM/dk| <= k Gk(k),  Gk = ch e^{k/2}/8 + e^k/4 + (e^k/4)(4ch/(3pi) + e^k ch/pi),
#   Lemma P: |dM/dphi| <= k^2 Gp(k), Gp = ch/(3pi) + 4e^k/(15pi) + k e^k ch/48 + (ch/4)(4ch/(3pi) + e^k ch/pi),
#   ch = cosh k; Gk, Gp increasing.  M(0,phi) = 4/(3pi) for all phi.
#   Box [k1,k2]x[p1,p2], centre (kc,pc), half-widths hk,hp:
#     k1 = 0: sup M <= 4/(3pi) + k2^2 Gk(k2)/2;   else sup M <= M(kc,pc) + hk k2 Gk(k2) + hp kc^2 Gp(kc).
# (3) Exact dyadic bisection until every box bound < 4/(3pi) + EPS.
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


def certify(eps, kmax, pmax):
    T = T0 + Q(eps)
    stack = [(F(0), kmax, F(0), pmax)]
    acc = 0
    ev = 0
    worst = None
    while stack:
        kl, kh, pl, ph = stack.pop()
        hk = (kh - kl) / 2
        hp = (ph - pl) / 2
        if kl == 0:
            ub = T0 + Q(kh) ** 2 * Gk(kh) / 2
            ek, ep = 1, 0
        else:
            kc = kl + hk
            pc = pl + hp
            m = Mval(kc, pc)
            ev += 1
            ekI = Q(hk * kh) * Gk(kh)
            epI = Q(hp * kc * kc) * Gp(kc)
            ub = m + ekI + epI
            ek, ep = ekI.b, epI.b
        if ub.b < T.a:
            acc += 1
            if worst is None or ub.b > worst.b:
                worst = ub
        elif ek >= ep:
            km = kl + hk
            stack += [(kl, km, pl, ph), (km, kh, pl, ph)]
        else:
            pm = pl + hp
            stack += [(kl, kh, pl, pm), (kl, kh, pm, ph)]
    return acc, ev, worst, T


if __name__ == "__main__":
    KMAX = F(805, 1024)
    PMAX = F(1609, 1024)
    EPS = F(1, 10 ** 8)
    assert Q(KMAX).a > (PI / 4).b and Q(PMAX).a > (PI / 2).b
    print("4/(3pi) in", encl(T0, 12))
    for (k, p) in [(F(1, 1000), F(2, 5)), (F(1, 2), F(1, 10000)), (F(1, 2), F(15707, 10000)), (F(157, 200), F(9, 10))]:
        print("M(%s, %s) in %s" % (k, p, encl(Mval(k, p), 10)))
    print("Gk(0) in", encl(Gk(0), 6), " Gk(805/1024) in", encl(Gk(KMAX), 6))
    print("Gp(0) in", encl(Gp(0), 6), " Gp(805/1024) in", encl(Gp(KMAX), 6))
    acc, ev, worst, T = certify(EPS, KMAX, PMAX)
    print("rectangle [0, 805/1024] x [0, 1609/1024], EPS = 1/10^8")
    print("boxes accepted =", acc, " point evaluations =", ev, " unresolved = 0")
    print("max box upper bound <=", dec(worst, 10, True), " (each box bound < 4/(3pi)+EPS checked in interval arithmetic)")
    beta = 1 / (18 * T)
    print("CERTIFIED: M* <= 4/(3pi) + 1e-8 <=", dec(T, 10, True))
    print("single-link Dobrushin row sum 18 beta M* < 1 for beta <", dec(beta, 9, False),
          "(pi/24 =", dec(PI / 24, 9, False) + "...)")
    print("check 6 * beta_max <= 805/1024:", (6 * beta).b <= Q(KMAX).a)

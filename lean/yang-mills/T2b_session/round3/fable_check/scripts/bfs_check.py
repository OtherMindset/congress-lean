# Independent check of the BFS pairing formula (Thm 3, (3.1)) and of (3.3) on 1 and 2 sites.
# Walk measure (derived here): weight exp(J phi1 phi2 - sum(a phi^2 + b phi^4)), site function g(s)=exp(-2as-4bs^2), s=phi^2/2.
# dW_xy = dT * e^{J T} * P_x(path, w(T)=y) for the rate-J two-state chain = J^n dh_0...dh_n on paths with n jumps.
# Summed over x,y the local-time density on (t1,t2) is
#   rho = delta(t2) + delta(t1) + 2J I0(z) + J (sqrt(t1/t2)+sqrt(t2/t1)) I1(z),  z = 2J sqrt(t1 t2).
# Z(t)/Z = exp(-sum(2a t + 4b t^2)) Z_{a+4bt}/Z_a.  Claims:  <M^2> = int rho Z(t)/Z,
#   <M^4> = 3 int rho Z(t)/Z X(a+4bt)   [i.e. 1-|B|/3 = E_w X(a+4bt)/X(a)],   E_w[t1+t2] <= chi = X/N.
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import ive
from mpmath import mp, mpf, quad, exp, inf
mp.dps = 25

print("=== one site (walk = sit at 0 for time T, dW = dT)")
def Z1(a, b, k=0): return 2 * quad(lambda x: x**k * exp(-a * x * x - b * x**4), [0, 1, 3, 8, inf])
for (a, b) in [(1, 0.5), (-2, 1), (2, 0.02), (-6, 1), (-12, 1), (20, 1)]:
    a = mpf(a); b = mpf(b); Z0 = Z1(a, b); p = Z1(a, b, 2) / Z0; q = Z1(a, b, 4) / Z0
    w = lambda t: exp(-2 * a * t - 4 * b * t * t) * Z1(a + 4 * b * t, b) / Z0
    X = lambda t: Z1(a + 4 * b * t, b, 2) / Z1(a + 4 * b * t, b)
    br = [0, 0.25, 1, 3, 10, 40, inf]
    two = quad(w, br); four = 3 * quad(lambda t: w(t) * X(t), br); Et = quad(lambda t: t * w(t), br) / two
    print("a=%5.1f b=%4.2f | <phi^2>=%.12f int w=%.12f | <phi^4>=%.12f 3 int w X=%.12f | 1-|B|/3=%.10f E_wX/X=%.10f | E_w t=%.6f <= chi=%.6f"
          % (a, b, p, two, q, four, q / (3 * p * p), four / (3 * two * p), Et, p))

print("=== two sites, coupling J")
def twosite(a, b, J, nphi=200, nt=64):
    R = 1.0
    while (a - J) * R * R + b * R**4 < 50: R += 0.05
    x, wx = leggauss(nphi); x = R * x; wx = R * wx
    P1, P2 = np.meshgrid(x, x, indexing='ij'); Wp = np.outer(wx, wx)
    base = J * P1 * P2 - a * (P1**2 + P2**2) - b * (P1**4 + P2**4); sh = base.max()
    E0 = Wp * np.exp(base - sh)
    def ZX(t1, t2):   # Z(t)/Z (including exp(-sum(2at+4bt^2))) and X at masses a+4bt
        e = E0 * np.exp(-4 * b * (t1 * P1**2 + t2 * P2**2))
        z = e.sum(); X = (e * (P1 + P2)**2).sum() / z
        return z, X
    Z, X0 = ZX(0.0, 0.0)
    pref = lambda t1, t2: np.exp(-2 * a * (t1 + t2) - 4 * b * (t1**2 + t2**2))
    # t-range
    Tm = 1.0
    while True:
        z, _ = ZX(Tm, 0.0)
        if pref(Tm, 0) * z / Z < 1e-16: break
        Tm *= 1.3
    tg, tw = leggauss(nt); tg = Tm * (tg + 1) / 2; tw = Tm * tw / 2
    s2 = s4 = st = 0.0
    # delta parts: walks staying on one site (two sites, symmetric)
    for t, w in zip(tg, tw):
        z, Xt = ZX(t, 0.0); r = pref(t, 0) * z / Z
        s2 += 2 * w * r; s4 += 2 * w * r * Xt; st += 2 * w * r * t
    # continuous part
    for t1, w1 in zip(tg, tw):
        for t2, w2 in zip(tg, tw):
            zz = 2 * J * np.sqrt(t1 * t2)
            rho = (2 * J * ive(0, zz) + J * (np.sqrt(t1 / t2) + np.sqrt(t2 / t1)) * ive(1, zz)) * np.exp(zz)
            z, Xt = ZX(t1, t2); r = pref(t1, t2) * z / Z
            s2 += w1 * w2 * rho * r; s4 += w1 * w2 * rho * r * Xt; st += w1 * w2 * rho * r * (t1 + t2)
    e = E0; z = e.sum(); M = P1 + P2
    m2 = (e * M**2).sum() / z; m4 = (e * M**4).sum() / z
    print("a=%5.2f b=%4.2f J=%.1f | <M^2>=%.8f walk=%.8f | <M^4>=%.8f 3 int=%.8f | 1-|B|/3=%.6f E_wX/X=%.6f | E_w|t|=%.5f <= chi=%.5f | B=%.4f"
          % (a, b, J, m2, s2, m4, 3 * s4, m4 / (3 * m2**2), s4 / (s2 * X0), st / s2, m2 / 2, m4 / m2**2 - 3))
# Gaussian check of the walk measure: b -> 0
twosite(1.5, 1e-7, 1.0)
for p in [(1.0, 0.5, 1.0), (-1.0, 1.0, 0.5), (2.0, 0.05, 1.0), (-3.0, 1.0, 0.3), (0.2, 0.3, 1.0), (-6.0, 1.0, 0.2)]:
    twosite(*p)

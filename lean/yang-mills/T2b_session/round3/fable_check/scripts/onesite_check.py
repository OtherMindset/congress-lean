# One-site checks of Theorem 2 (b = 1 wlog by scaling phi -> b^{-1/4} phi, a -> a/sqrt b), mpmath 40 digits.
# (a) 3 m2^2 - m4 <= 4 b m4 (m4 - m2^2)       (b) d/da (m4/m2^2) >= 0      (c) m4 >= 3 m2(a) m2(a + 4 b m2(a))
# moments computed by direct quadrature with breakpoints at the well minimum (independent of the IBP recursion).
from mpmath import mp, mpf, quad, exp, sqrt, inf, diff
mp.dps = 40
def mom(a, k, b=mpf(1)):
    xm = sqrt(max(-a / (2 * b), 0))
    pts = sorted(set([mpf(0), xm / 2, xm, xm + 1, 2 * xm + 2, 3 * xm + 6])) + [inf]
    # shift exponent by its max to avoid underflow
    V0 = -(a * xm**2 + b * xm**4)
    return 2 * quad(lambda x: x**k * exp(-a * x * x - b * x**4 - V0), pts)
def ms(a):
    z = mom(a, 0); return mom(a, 2) / z, mom(a, 4) / z, mom(a, 6) / z
worst = {}
print(" a      | (a) ratio |k4|/(4b m4 Var)  | (b) d/da Binder | (c) m4/(3 m2 m2(a+4bm2))  | IBP check 1-2a m2-4b m4 | kappa3(phi^2)")
for a in [-200, -100, -50, -30, -20, -12, -8, -6, -4, -3, -2, -1, -0.5, 0, 0.5, 1, 2, 5, 10, 30, 100, 1000]:
    a = mpf(a)
    m2, m4, m6 = ms(a)
    ra = (3 * m2**2 - m4) / (4 * m4 * (m4 - m2**2))
    dB = (2 * m4**2 - m6 * m2 - m4 * m2**2) / m2**3
    dBnum = diff(lambda s: (lambda u: u[1] / u[0]**2)(ms(s)), a)
    p1 = ms(a + 4 * m2)[0]
    rc = m4 / (3 * m2 * p1)
    ibp = 1 - 2 * a * m2 - 4 * m4
    k3 = m6 - 3 * m4 * m2 + 2 * m2**3
    print("%7.1f | %.12f | %+.6e (num %+.6e) | %.12f | %.1e | %+.3e" % (a, ra, dB, dBnum, rc, ibp, k3))

"""Independent one-site check of (A.1) and (B.1) of ng/PROOF.md.
One site, no bonds: walk measure dW = dt on [0,inf), w-hat(dt) = Z(t)dt / int Z.
(A.1) checked with D computed from the Gamma-integral formula (A.2) (NOT from R), i.e.
   D(t,t') = 8b t t' - 16 b^2 t t' int_0^1 int_0^1 Var_{a+4b(s t + u t')}(phi^2) ds du,
and |B| = 3 E[1 - exp(-D)] compared with |B| from direct moments.
Also: R = Z(t+t')Z/(Z(t)Z(t')) compared with exp(-D) pointwise; (B.1) |B| <= 24 b m2^2; E t <= chi = m2."""
import numpy as np
from numpy.polynomial.legendre import leggauss

def grid(a, b):
    # phi grid covering the weight e^{-a phi^2 - b phi^4} (and shifted masses a' >= a)
    pmin2 = max(-a / (2 * b), 0.0)
    P = np.sqrt(pmin2) + 12.0 / (b ** 0.25) + 12.0 / np.sqrt(max(abs(a), 1e-3) + 1)
    P = min(P, np.sqrt(pmin2) + 60)
    x = np.linspace(-P, P, 40001)
    return x, x[1] - x[0]

def moments(a, b, x, dx):
    V = a * x * x + b * x ** 4
    w = np.exp(-(V - V.min()))
    Z = w.sum()
    return [(w * x ** (2 * k)).sum() / Z for k in range(0, 4)], (np.log(Z * dx) - V.min())

def logZmass(ap, b, x, dx):
    V = ap * x * x + b * x ** 4
    return np.log(np.exp(-(V - V.min())).sum() * dx) - V.min()

def varphi2(ap, b, x, dx):
    m, _ = moments(ap, b, x, dx)
    return m[2] - m[1] ** 2

def run(a, b, nt=80, ns=16):
    x, dx = grid(a, b)
    (m0, m2, m4, m6), lZ0 = moments(a, b, x, dx)
    B = m4 / m2 ** 2 - 3
    # log Z(t)/Z = -(2at+4bt^2) + logZ_{a+4bt} - logZ_a
    def logF(t):
        return -(2 * a * t + 4 * b * t * t) + logZmass(a + 4 * b * t, b, x, dx) - lZ0
    # t-range: w-hat density ∝ F(t); find cutoff where log F < -60
    T = 1.0
    while logF(T) > -70:
        T *= 1.5
    # Gauss-Legendre on [0,T] split in pieces
    gx, gw = leggauss(nt)
    pieces = 8
    ts, ws = [], []
    for p in range(pieces):
        lo, hi = T * p / pieces, T * (p + 1) / pieces
        ts.append(lo + (hi - lo) * (gx + 1) / 2); ws.append(gw * (hi - lo) / 2)
    ts = np.concatenate(ts); ws = np.concatenate(ws)
    lF = np.array([logF(t) for t in ts])
    F = np.exp(lF)
    X = (ws * F).sum()                      # should equal m2
    p = ws * F / X                          # w-hat weights
    Et = (p * ts).sum()
    # Var_{a+4bs}(phi^2) on an s-grid, spline
    smax = 2 * T
    sg = np.linspace(0, smax, 1201)
    vg = np.array([varphi2(a + 4 * b * s, b, x, dx) for s in sg])
    from scipy.interpolate import CubicSpline
    vs = CubicSpline(sg, vg)
    sx, sw = leggauss(ns); sx = (sx + 1) / 2; sw = sw / 2
    TT, TP = np.meshgrid(ts, ts, indexing='ij')
    I = np.zeros_like(TT)
    for i in range(ns):
        for j in range(ns):
            I += sw[i] * sw[j] * vs(sx[i] * TT + sx[j] * TP)
    Gam = 16 * b * b * TT * TP * I
    D = 8 * b * TT * TP - Gam
    PP = np.outer(p, p)
    Bwalk = 3 * (PP * (1 - np.exp(-D))).sum()
    # pointwise check e^{-D} vs R on a few pairs
    errR = 0
    for (i, j) in [(len(ts) // 7, len(ts) // 3), (len(ts) // 2, len(ts) // 5), (10, 200)]:
        t, tp = ts[i], ts[j]
        lR = logF(t + tp) - logF(t) - logF(tp)
        errR = max(errR, abs(lR - (-D[i, j])))
    # direct pairing: <phi^4> = 3 int int Z(t+t')/Z = 3 int u Z(u)/Z du
    m4walk = 3 * (ws * ts * F).sum()
    tree = 24 * b * m2 ** 2
    print(f"a={a:7.2f} b={b:7.4f} | m2={m2:.10f} X_walk={X:.10f} | m4={m4:.10f} walk={m4walk:.10f} | "
          f"|B|={-B:.10f} 3E[1-e^-D]={Bwalk:.10f} diff={abs(-B-Bwalk):.1e} | max|logR+D|={errR:.1e} | "
          f"min Gam>=0:{Gam.min()>=-1e-12} | P(D<0)={(PP*(D<0)).sum():.3f} | tree 24bm2^2={tree:.4g} ratio={-B/tree:.4f} | Et/chi={Et/m2:.4f}")

if __name__ == '__main__':
    for a, b in [(1.0, 0.5), (-2.0, 0.3), (-6.0, 1.0), (-20.0, 1.0), (-10.0, 0.1), (-3.0, 0.02),
                 (0.5, 0.01), (1.0, 0.001), (5.0, 0.001), (0.0, 1.0)]:
        run(a, b)

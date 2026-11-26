"""Independent two-site check (one bond of strength J, walk jump rate J) of the BFS pairing formula,
hence of (A.1) [B = -3 E(1-R) is pure algebra once <M^4> = 3 X^2 E[R]], of E|t| <= chi (walk splitting + GKS),
and of the tree bound (B.1) |B| <= 24 b chi^2 / N, N = 2.
Exact walk densities: a path with k_i visits to site i has local-time density J^n prod_i t_i^{k_i-1}/(k_i-1)!
(delta at t_i=0 if k_i=0), n = k1+k2-1 jumps. For a pair of paths the convolution gives the same form with K_i = k_i+k_i'.
So int int dW dW' Z(t+t')/Z = sum_K C(K) J^{K1+K2-2} << G_K1 (x) G_K2 >>, G_K(phi) = int s^{K-1}/(K-1)! g(phi^2/2+s) ds."""
import numpy as np
from numpy.polynomial.legendre import leggauss
from math import lgamma

def run(a, b, J=1.0, kmax=None):
    pmin = np.sqrt(max(-(a - J / 2) / (2 * b), 0))
    P = pmin + min(10 / b ** 0.25, 12 / np.sqrt(max(2*a - J, 0.05)) + 3/b**0.25)
    x = np.linspace(-P, P, 1201); dx = x[1] - x[0]
    # reference shift for numerics
    V = a * x * x + b * x ** 4
    # direct moments
    W = np.exp(-(V - V.min()))
    Kern = np.exp(J * np.outer(x, x) - J * (np.outer(x * x, np.ones_like(x)) + np.outer(np.ones_like(x), x * x)) / 2)
    # weight e^{J x y} = Kern * e^{J(x^2+y^2)/2}
    lw = -(V - V.min()) + J * x * x / 2
    w = np.exp(lw - lw.max())
    Mz = w[:, None] * Kern * w[None, :]
    Z = Mz.sum()
    M1 = x[:, None] + x[None, :]
    m2M = (Mz * M1 ** 2).sum() / Z
    m4M = (Mz * M1 ** 4).sum() / Z
    B = m4M / m2M ** 2 - 3
    chi = m2M / 2
    # local-time functions G_K(phi): g(s) = exp(-2as-4bs^2), argument phi^2/2+s
    if kmax is None:
        kmax = int(30 + 6 * J * (max(-a, 0) / b + 4) + 4 * J * np.sqrt(1 / b))
        kmax = min(kmax, 600)
    # s quadrature
    Smax = 1.0
    while True:
        tt = Smax
        if -(2 * a * tt + 4 * b * tt * tt) + 4 * b * tt * (pmin ** 2) + kmax * np.log(tt + 1) < -80 and tt > 5:
            break
        Smax *= 1.3
    gx, gw = leggauss(200)
    pieces = 6
    ss, sw = [], []
    for p in range(pieces):
        lo, hi = Smax * p / pieces, Smax * (p + 1) / pieces
        ss.append(lo + (hi - lo) * (gx + 1) / 2); sw.append(gw * (hi - lo) / 2)
    ss = np.concatenate(ss); sw = np.concatenate(sw)
    # g(phi^2/2+s) relative to g(phi^2/2): exp(-2as -4b s^2 -4b phi^2 s)
    E = np.exp(-2 * a * ss[None, :] - 4 * b * ss[None, :] ** 2 - 4 * b * (x * x)[:, None] * ss[None, :])  # (nx, ns)
    G = np.zeros((kmax + 2, len(x)))
    G[0] = 1.0  # times g(phi^2/2) which is the site weight already in w
    logs = np.log(np.maximum(ss, 1e-300))
    for K in range(1, kmax + 2):
        dens = np.exp((K - 1) * logs - lgamma(K))
        G[K] = (E * (dens * sw)[None, :]).sum(1)
    # matrix of << G_K1 (x) G_K2 >>
    Gw = G * w[None, :]
    Mat = Gw @ Kern @ Gw.T / Z  # (kmax+2)^2
    # path types: (k1,k2,mult)
    paths = [(1, 0, 1), (0, 1, 1)]
    for k in range(1, kmax):
        paths += [(k, k, 2), (k + 1, k, 1), (k, k + 1, 1)]
    paths = [p for p in paths if p[0] <= kmax and p[1] <= kmax]
    X = sum(mu * J ** (k1 + k2 - 1) * Mat[k1, k2] for k1, k2, mu in paths)
    # E|t| X = sum mu J^n [k1 Mat[k1+1,k2] + k2 Mat[k1,k2+1]]
    EtX = sum(mu * J ** (k1 + k2 - 1) * (k1 * Mat[k1 + 1, k2] + k2 * Mat[k1, k2 + 1]) for k1, k2, mu in paths)
    # pairs
    M4w = 0.0
    for k1, k2, mu in paths:
        for l1, l2, nu in paths:
            K1, K2 = k1 + l1, k2 + l2
            if K1 <= kmax + 1 and K2 <= kmax + 1:
                M4w += mu * nu * J ** (K1 + K2 - 2) * Mat[K1, K2]
    M4w *= 3
    tree = 24 * b * chi ** 2 / 2
    print(f"a={a:6.2f} b={b:6.3f} J={J:4.2f} kmax={kmax:3d} | <M^2>={m2M:.9f} walk={X:.9f} | <M^4>={m4M:.9f} walk={M4w:.9f} "
          f"rel={abs(M4w/m4M-1):.1e} | |B|={-B:.6f} | E|t|/chi={EtX/X/chi:.4f} | tree={tree:.4g} |B|/tree={-B/tree:.4f}")

if __name__ == '__main__':
    for a, b, J in [(1.0, 0.5, 1.0), (0.0, 1.0, 1.0), (-1.0, 0.5, 1.0), (-3.0, 1.0, 1.0), (-4.0, 1.0, 0.3),
                    (1.0, 0.01, 1.0), (0.7, 0.002, 1.0), (2.0, 0.001, 1.0), (-2.0, 0.3, 1.0)]:
        run(a, b, J)

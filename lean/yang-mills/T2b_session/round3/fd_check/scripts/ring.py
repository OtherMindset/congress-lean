# Independent exact (quadrature + transfer matrix) code for the phi^4 ring.
# Weight: exp( J sum_i phi_i phi_{i+1} - sum_i (a phi_i^2 + b phi_i^4) ), N sites periodic.
# Moments of M and the a-derivative of chi are obtained EXACTLY (no finite differences, no contour FFT)
# by computing tr (D T)^N over a truncated polynomial ring in (H, s), D = diag(exp(H x - s x^2)).
import numpy as np
from numpy.polynomial.legendre import leggauss

def grid(a, b, J, ng):
    # cut-off where the diagonal effective potential exceeds 70
    R = 0.5
    while (a - abs(J)) * R * R + b * R ** 4 < 70:
        R *= 1.02
    x, w = leggauss(ng)
    return R * x, R * w

class Ring:
    def __init__(s, a, b, J, N, ng=220):
        s.a, s.b, s.J, s.N = a, b, J, N
        x, w = grid(a, b, J, ng)
        s.x = x
        V = a * x * x + b * x ** 4
        sw = np.sqrt(w)
        K = np.exp(J * np.outer(x, x) - 0.5 * V[:, None] - 0.5 * V[None, :]) * np.outer(sw, sw)
        ev, U = np.linalg.eigh(K)
        s.lmax = ev.max()
        s.K = K / s.lmax
        s.ev = ev / s.lmax
        s.U = U
        s.Xe = U.T @ (x[:, None] * U)  # phi in eigenbasis

    def G(s):
        N = s.N
        e = s.ev
        Z = (e ** N).sum()
        X2 = s.Xe ** 2
        return np.array([(e ** (N - z)) @ X2 @ (e ** z) for z in range(N)]) / Z

    def corr(s, counts):
        # <prod_i phi_i^{counts[i]}>
        N = s.N
        P = np.eye(len(s.x))
        for i in range(N):
            P = P @ (s.x[:, None] ** counts[i] * s.K)  # diag(x^c) K
        Z = (s.ev ** N).sum()
        return np.trace(P) / Z

    # truncated polynomial algebra in (H, s): dict (i,j) -> matrix, i<=pH, j<=ps
    def _mul(s, A, B, pH, ps):
        C = {}
        for (i1, j1), M1 in A.items():
            for (i2, j2), M2 in B.items():
                i, j = i1 + i2, j1 + j2
                if i <= pH and j <= ps:
                    C[(i, j)] = C.get((i, j), 0) + M1 @ M2
        return C

    def _power_trace(s, pH, ps):
        x = s.x
        from math import factorial
        # D T with D = exp(H x - s x^2) truncated
        A = {}
        for i in range(pH + 1):
            for j in range(ps + 1):
                d = x ** i / factorial(i) * (-x * x) ** j / factorial(j)
                A[(i, j)] = d[:, None] * s.K
        # repeated squaring
        n = s.N
        R = None
        P = A
        while n:
            if n & 1:
                R = P if R is None else s._mul(R, P, pH, ps)
            n >>= 1
            if n:
                P = s._mul(P, P, pH, ps)
        Z0 = np.trace(R[(0, 0)])
        return {k: np.trace(v) / Z0 for k, v in R.items()}

    def moments(s):
        c = s._power_trace(4, 0)
        M2 = 2 * c[(2, 0)]
        M4 = 24 * c[(4, 0)]
        return M2, M4

    def mdchi(s):
        # -d chi/da = Cov(M^2, Phi2)/N
        c = s._power_trace(2, 1)
        M2 = 2 * c[(2, 0)]
        P2 = -c[(0, 1)]
        M2P2 = -2 * c[(2, 1)]
        return (M2P2 - M2 * P2) / s.N

def quantities(a, b, J, N, ng=220):
    r = Ring(a, b, J, N, ng)
    G = r.G()
    chi = G.sum()
    M2, M4 = r.moments()
    m2 = M2 / N ** 2
    B = M4 / M2 ** 2 - 3
    return dict(G=G, chi=chi, B2=(G ** 2).sum(), m2=m2, B=B, M2=M2, M4=M4, mdchi=r.mdchi(), ring=r)

def m2_only(a, b, J, N, ng=220):
    return Ring(a, b, J, N, ng).G().sum() / N

if __name__ == "__main__":
    # one-site check (N=1, J=0) against mpmath
    from mpmath import mp, quad, exp, inf
    mp.dps = 30
    for a, b in [(0.5, 1.0), (-2.0, 0.3), (3.0, 0.005)]:
        q = quantities(a, b, 0.0, 1, ng=300)
        z = [quad(lambda t: t ** k * exp(-a * t * t - b * t ** 4), [-inf, 0, inf]) for k in (0, 2, 4, 6)]
        m2, m4 = z[1] / z[0], z[2] / z[0]
        # -d<phi^2>/da = <phi^4>-<phi^2>^2
        print(a, b, q['m2'] - float(m2), q['M4'] - float(m4), q['mdchi'] - float(m4 - m2 ** 2))

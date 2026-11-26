"""Rings (1D torus, n sites, J=1) by transfer matrix.
(i)  (B.1): |B| <= 24 b chi^2 / n, exact moments of M via truncated matrix-polynomial powers.
(ii) second-difference identity of (A.1)/(A.2): Phi(t+t')-Phi(t)-Phi(t')+Phi(0) = -8b t.t' + Gamma(t,t'),
     Gamma = 16 b^2 int int sum t_x t'_y <phi_x^2;phi_y^2>_{s t + u t'} ds du >= 0, with Phi = log Z(t),
     Z(t) = int prod g(phi_x^2/2 + t_x) e^{sum phi_x phi_{x+1}}, g(s)=exp(-2as-4bs^2) (computed directly from g).
"""
import numpy as np, sys
from numpy.polynomial.legendre import leggauss

def mkgrid(a, b, ng=None):
    pmin = np.sqrt(max((1 - a) / (2 * b), 0))       # ring: sum phi phi <= sum phi^2, effective a-1
    curv = max(2 * (a - 1) + 12 * b * pmin ** 2, 0) + 2 * np.sqrt(b)
    width = 1 / np.sqrt(curv)
    P = pmin + 9 * width + 2
    P = min(P, pmin + 40)
    if ng is None:
        ng = int(min(max(2 * P / 0.12, 300), 1400))
    x = np.linspace(-P, P, ng)
    return x, x[1] - x[0]

def moments_ring(a, b, n, x, dx):
    K = np.exp(-0.5 * (x[:, None] - x[None, :]) ** 2)
    lw = -(a - 1) * x * x - b * x ** 4
    w = np.exp(lw - lw.max()) * dx
    A0 = w[:, None] * K
    fac = [1, 1, 2, 6, 24]
    A = [ (w * x ** k / fac[k])[:, None] * K for k in range(5)]
    # power of matrix polynomial, truncated at degree 4
    P = [np.eye(len(x))] + [np.zeros_like(A0) for _ in range(4)]
    for _ in range(n):
        Q = [sum(P[i] @ A[k - i] for i in range(k + 1)) for k in range(5)]
        s = np.abs(Q[0]).max()
        P = [q / s for q in Q]
    c = [np.trace(p) for p in P]
    m2 = 2 * c[2] / c[0]; m4 = 24 * c[4] / c[0]
    return m2, m4

def checkB1():
    print("(B.1) on rings: |B| <= 24 b chi^2/n")
    worst = 0
    rows = []
    for n in [3, 4, 8, 16]:
        for b in [1.0, 0.1, 0.01, 0.001]:
            for a in [3.0, 1.2, 1.05, 0.8, 0.0, -1.0, -3.0]:
                if (1 - a) / (2 * b) > 1500:  # skip absurdly deep wells (grid)
                    continue
                x, dx = mkgrid(a, b)
                m2, m4 = moments_ring(a, b, n, x, dx)
                # grid convergence
                x2, dx2 = mkgrid(a, b, ng=int(len(x) * 1.3))
                m2b, m4b = moments_ring(a, b, n, x2, dx2)
                B = m4 / m2 ** 2 - 3
                Bb = m4b / m2b ** 2 - 3
                chi = m2 / n
                tree = 24 * b * chi ** 2 / n
                r = -B / tree
                worst = max(worst, r)
                rows.append((n, a, b, -B, abs(B - Bb), tree, r))
                print(f"  n={n:2d} a={a:5.2f} b={b:6.3f}: |B|={-B:.8f} (grid err {abs(B-Bb):.1e})  24b chi^2/n={tree:.5g}  ratio={r:.5f}", flush=True)
    print("  max ratio |B|/bound =", round(worst, 6))

def sitew(x, a, b, t):
    # g(phi^2/2 + t) times e^{+phi^2} (from rewriting phi phi' = phi^2/2 + phi'^2/2 - (phi-phi')^2/2)
    s = x * x / 2 + t
    return -2 * a * s - 4 * b * s * s + x * x

def logZ_t(a, b, t, x, dx):
    K = np.exp(-0.5 * (x[:, None] - x[None, :]) ** 2)
    M = np.eye(len(x)); lz = 0.0
    for tx in t:
        lw = sitew(x, a, b, tx); mx = lw.max()
        M = M @ ((np.exp(lw - mx) * dx)[:, None] * K)
        s = np.abs(M).max(); M /= s; lz += np.log(s) + mx
    return lz + np.log(np.trace(M))

def cov_phi2(a, b, t, x, dx):
    """<phi_x^2;phi_y^2> under weights g(phi^2/2 + t_x) (= masses a+4bt_x)."""
    n = len(t)
    K = np.exp(-0.5 * (x[:, None] - x[None, :]) ** 2)
    mats, matsI = [], []
    for tx in t:
        lw = sitew(x, a, b, tx); w = np.exp(lw - lw.max()) * dx
        w /= w.sum()
        mats.append(w[:, None] * K); matsI.append((w * x * x)[:, None] * K)
    def tr(ins):
        M = np.eye(len(x))
        for i in range(n):
            M = M @ (matsI[i] if i in ins else mats[i])
        return np.trace(M)
    Z = tr(())
    e = np.array([tr((i,)) / Z for i in range(n)])
    C = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i == j:
                # phi^4 insertion
                M = np.eye(len(x))
                for k in range(n):
                    if k == i:
                        lw = sitew(x, a, b, t[k]); w = np.exp(lw - lw.max()) * dx; w /= w.sum()
                        M = M @ ((w * x ** 4)[:, None] * K)
                    else:
                        M = M @ mats[k]
                C[i, i] = np.trace(M) / Z - e[i] ** 2
            elif j > i:
                C[i, j] = C[j, i] = tr((i, j)) / Z - e[i] * e[j]
    return C

def checkGamma(seed=1):
    rng = np.random.default_rng(seed)
    print("second-difference identity log R = -8b t.t' + Gamma and Gamma >= 0 (rings)")
    sx, sw = leggauss(10); sx = (sx + 1) / 2; sw = sw / 2
    for (n, a, b) in [(3, 0.5, 0.5), (4, -1.0, 0.5), (4, -3.0, 1.0), (5, 1.2, 0.05), (6, 0.0, 1.0), (4, -2.0, 0.1)]:
        x, dx = mkgrid(a, b, ng=500)
        for trial in range(2):
            scale = 1.0 if a > 0 else 0.3 * (1 - a) / b
            t = rng.exponential(scale, n) * (rng.random(n) < 0.7)
            tp = rng.exponential(scale, n) * (rng.random(n) < 0.7)
            lR = logZ_t(a, b, t + tp, x, dx) - logZ_t(a, b, t, x, dx) - logZ_t(a, b, tp, x, dx) + logZ_t(a, b, np.zeros(n), x, dx)
            G = 0.0; cmin = np.inf
            for i in range(len(sx)):
                for j in range(len(sx)):
                    C = cov_phi2(a, b, sx[i] * t + sx[j] * tp, x, dx)
                    cmin = min(cmin, C.min())
                    G += sw[i] * sw[j] * (t @ C @ tp)
            G *= 16 * b * b
            rhs = -8 * b * (t @ tp) + G
            print(f"  n={n} a={a:5.2f} b={b:4.2f} t.t'={t@tp:8.4f}: logR={lR:+.8f}  -8bt.t'+Gamma={rhs:+.8f}  diff={abs(lR-rhs):.1e}  Gamma={G:.5f}  min cov={cmin:.2e}  D={-lR:+.4f}", flush=True)

if __name__ == '__main__':
    if 'gamma' in sys.argv: checkGamma()
    else: checkB1()

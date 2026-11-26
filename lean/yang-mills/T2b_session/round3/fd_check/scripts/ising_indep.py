# Independent Ising-limit check.
# (1) Derivation check: phi^4 ring with V = b(phi^2 - v)^2 (a = -2 b v), b large, J = 1: kappa_min of FD vs the
#     Ising-limit formula (1 - 2k f(v)) f(v(1 - 2k f(v))) <= (1-|B|/3) f(v), f = <(M/N)^2>_Ising(beta=v) on the ring.
# (2) 2D Ising LxL tori: L = 4 by brute-force enumeration (2^16 states), L = 6 by row transfer matrix with an
#     exact truncated-polynomial field expansion (no contour integrals).
import numpy as np, itertools, sys
from scipy.optimize import brentq
from ring import Ring

def kmin_generic(f0, B, fun, beta):
    tgt = (1 - abs(B) / 3) * f0
    def g(k):
        r = 1 - 2 * k * f0
        return (r * fun(beta * r) if r > 0 else 0.0) - tgt
    if g(1e-12) <= 0: return 0.0
    return brentq(g, 1e-12, 0.5 / f0, xtol=1e-10)

# ---- (1) ring Ising limit: exact 1D Ising moments by enumeration of N spins
def ising_ring(beta, N):
    s = np.array(list(itertools.product([-1, 1], repeat=N)))
    E = (s * np.roll(s, 1, axis=1)).sum(1)
    w = np.exp(beta * E); w /= w.sum()
    M = s.sum(1).astype(float)
    m2 = (w * M ** 2).sum(); m4 = (w * M ** 4).sum()
    return m2 / N ** 2, m4 / m2 ** 2 - 3

def phi4_kmin(v, b, N):
    a = -2 * b * v
    r = Ring(a, b, 1.0, N, ng=400)
    M2, M4 = r.moments(); m2 = M2 / N ** 2; B = M4 / M2 ** 2 - 3
    tgt = (1 - abs(B) / 3) * m2
    g = lambda k: Ring(a + 4 * b * k * m2, b, 1.0, N, ng=400).G().sum() / N - tgt
    return brentq(g, 1e-9, 0.5 / (m2 / v) * 1.5, xtol=1e-8), m2 / v, B

print("# (1) phi^4 ring, V=b(phi^2-v)^2, N=4: kappa_min(b) -> Ising-limit kappa_min ?")
for v in [0.3, 0.6, 1.0]:
    f0, B0 = ising_ring(v, 4)
    kI = kmin_generic(f0, B0, lambda bb: ising_ring(bb, 4)[0], v)
    row = []
    for b in [5.0, 20.0, 80.0]:
        try:
            k, f, B = phi4_kmin(v, b, 4); row.append("b=%g: k=%.4f (f=%.4f B=%.4f)" % (b, k, f, B))
        except Exception as e:
            row.append("b=%g: err %s" % (b, e))
    print("v=%.2f Ising-limit k=%.4f (f=%.4f B=%.4f) | %s" % (v, kI, f0, B0, " ; ".join(row))); sys.stdout.flush()

# ---- (2) 2D Ising tori
def ising2d_enum(L):
    N = L * L
    idx = np.arange(2 ** N)
    s = 1 - 2 * ((idx[:, None] >> np.arange(N)) & 1)
    s = s.reshape(-1, L, L).astype(np.int8)
    E = (s * np.roll(s, 1, 1)).sum((1, 2)) + (s * np.roll(s, 1, 2)).sum((1, 2))
    M = s.sum((1, 2))
    # histogram over (E, M)
    pairs = {}
    for e, m in zip(E.tolist(), M.tolist()):
        pairs[(e, m)] = pairs.get((e, m), 0) + 1
    keys = np.array(list(pairs.keys()), float); cnt = np.array(list(pairs.values()), float)
    def mom(beta):
        lw = beta * keys[:, 0]; w = cnt * np.exp(lw - lw.max()); w /= w.sum()
        m2 = (w * keys[:, 1] ** 2).sum(); m4 = (w * keys[:, 1] ** 4).sum()
        return m2 / N ** 2, m4 / m2 ** 2 - 3
    return mom

def ising2d_tm(L):
    N = L * L
    n = 2 ** L; idx = np.arange(n)
    sp = (1 - 2 * ((idx[:, None] >> np.arange(L)) & 1)).astype(float)
    Mr = sp.sum(1); Er = (sp * np.roll(sp, 1, 1)).sum(1); V = sp @ sp.T
    from math import factorial
    def mom(beta):
        lT = beta * (V + 0.5 * Er[:, None] + 0.5 * Er[None, :])
        T = np.exp(lT - lT.max())
        # truncated polynomial in H up to order 4: D(H) T, D = diag(exp(H Mr))
        A = [((Mr ** k) / factorial(k))[:, None] * T for k in range(5)]
        def mul(X, Y): return [sum(X[i] @ Y[k - i] for i in range(k + 1)) for k in range(5)]
        R = A
        for _ in range(L - 1): R = mul(R, A)
        c = [np.trace(m) for m in R]
        M2 = 2 * c[2] / c[0]; M4 = 24 * c[4] / c[0]
        return M2 / N ** 2, M4 / M2 ** 2 - 3
    return mom

print("# (2) 2D Ising LxL torus, Ising limit of phi^4: beta: kappa_min (B)")
for L, maker in [(4, ising2d_enum), (6, ising2d_tm)]:
    mom = maker(L)
    if L == 4:
        mt = ising2d_tm(4)
        print("  L=4 enumeration vs TM at beta=0.4:", mom(0.4), mt(0.4))
    worst = 0; row = []
    for beta in [0.01, 0.05, 0.1, 0.2, 0.3, 0.35, 0.4, 0.42, 0.44, 0.46, 0.5, 0.6, 0.8, 1.2]:
        f0, B = mom(beta)
        k = kmin_generic(f0, B, lambda bb: mom(bb)[0], beta)
        worst = max(worst, k); row.append("%.2f:%.4f(B%.3f)" % (beta, k, B))
    print("L=%d worst=%.4f" % (L, worst)); print("   ", " ".join(row)); sys.stdout.flush()

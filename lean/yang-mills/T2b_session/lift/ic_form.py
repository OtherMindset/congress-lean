"""Check: for Ising spins and block B (|B|=n), R = <M;M^2>/<M> = 2(n-1) - 2<S2> + 6<S3>/<M>,
S2 = sum of pair products in B, S3 = sum of triple products in B. IC <=> 3<S3>/<M> - <S2> nonincreasing in H.
Random ferromagnetic graphs, field H*c with c=1 on B, c>=0 elsewhere. Also reports worst dR/dH (finite diff)."""
import numpy as np, itertools
rng = np.random.default_rng(4)
worst = -np.inf; maxerr = 0
for t in range(300):
    N = int(rng.integers(3, 10)); n = int(rng.integers(2, min(N, 5)+1))
    conf = np.array(list(itertools.product([-1, 1], repeat=N)), float)
    J = np.triu(10**rng.uniform(-1.5, 0.5, (N, N))*(rng.random((N, N)) < 0.6), 1)
    c = np.where(np.arange(N) < n, 1.0, rng.random(N)*(rng.random(N) < .7))
    B = conf[:, :n]; M = B.sum(1)
    S2 = sum(B[:, i]*B[:, j] for i, j in itertools.combinations(range(n), 2))
    S3 = sum(B[:, i]*B[:, j]*B[:, k] for i, j, k in itertools.combinations(range(n), 3)) if n >= 3 else 0*M
    def stats(H):
        E_ = np.einsum('ci,ij,cj->c', conf, J, conf) + H*conf@c
        p = np.exp(E_ - E_.max()); p /= p.sum(); E = lambda F: (p*F).sum()
        R = (E(M**3) - E(M)*E(M**2))/E(M)
        R2 = 2*(n-1) - 2*E(S2) + 6*E(S3)/E(M)
        return R, R2
    Hs = np.logspace(-2.5, 0.8, 60)
    Rs = []
    for H in Hs:
        R, R2 = stats(H); maxerr = max(maxerr, abs(R-R2)); Rs.append(R)
    d = np.diff(Rs).max()/ (abs(np.array(Rs)).max()+1e-12)
    worst = max(worst, d)
print("max |R - formula| =", maxerr, "  worst relative increase of R along H grid =", worst)

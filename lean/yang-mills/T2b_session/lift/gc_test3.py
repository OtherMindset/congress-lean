"""GC, n=3 sites, q in {-2..2}, random ferromagnetic J (any graph), uniform H, random down-sets.
Variant flags: 'prod' (even product weights), 'abs' (extra arbitrary interaction of |q| values:
weight exp(sum K_xy |q_x||q_y|) with K of either sign: tests whether MTP2 (K>=0) matters)."""
import numpy as np, itertools, sys
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
mode = sys.argv[1] if len(sys.argv) > 1 else 'prod'
n = 3; pts = list(itertools.product(range(3), repeat=n))
conf = np.array(list(itertools.product([-2, -1, 0, 1, 2], repeat=n)), float); A = np.abs(conf).astype(int)
idx = {p: i for i, p in enumerate(pts)}; code = np.array([idx[tuple(a)] for a in A])
def rand_downset():
    gens = [pts[i] for i in rng.choice(len(pts), rng.integers(1, 4), replace=False)]
    S = np.array([any(all(q[k] <= g[k] for k in range(n)) for g in gens) for q in pts], float); return S
worst = (-np.inf, None)
for t in range(6000):
    lw = rng.normal(0, 2, 3); J = np.triu(10**rng.uniform(-1.5, 0.5, (3, 3)) * (rng.random((3, 3)) < 0.8), 1)
    H = 10**rng.uniform(-3, 0.5)
    E_ = np.einsum('ci,ij,cj->c', conf, J, conf) + H*conf.sum(1) + lw[A].sum(1)
    if mode == 'abs':
        K = np.triu(rng.normal(0, 1, (3, 3)), 1); E_ = E_ + np.einsum('ci,ij,cj->c', A.astype(float), K, A.astype(float))
    if mode == 'absMTP2':
        K = np.triu(np.abs(rng.normal(0, 1, (3, 3))), 1); E_ = E_ + np.einsum('ci,ij,cj->c', A.astype(float), K, A.astype(float))
    p = np.exp(E_ - E_.max()); p /= p.sum(); E = lambda F: (p*F).sum()
    q0 = conf[:, 0]; Q = conf.sum(1); m = E(q0); c = E(q0*Q) - m*E(Q)
    for k in range(6):
        F = rand_downset()[code]
        num = E(q0*F*Q) - E(q0*F)*E(Q); d = num*m - E(q0*F)*c
        s = abs(num*m) + abs(E(q0*F)*c) + 1e-300
        if d/s > worst[0]: worst = (d/s, dict(lw=lw.round(3), J=J.round(3).tolist(), H=H))
print(mode, worst)

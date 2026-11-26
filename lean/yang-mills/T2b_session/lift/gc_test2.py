"""GC for spins q_x in {-2,-1,0,1,2} (|q| in {0,1,2}), arbitrary even product weights, J>=0, field H.
F ranges over indicators of down-sets of {0,1,2}^n (extreme rays mod constants). Exact."""
import numpy as np, itertools
rng = np.random.default_rng(11)
def downsets(levels, n):
    pts = list(itertools.product(range(levels), repeat=n)); out = set()
    # generate down-sets as down-closures of antichains via random + all principal combos (n<=2 exhaustive)
    for r in range(1, len(pts)+1):
        for gens in itertools.combinations(pts, r) if len(pts) <= 9 else []:
            S = frozenset(q for q in pts if any(all(q[k] <= g[k] for k in range(n)) for g in gens))
            if len(S) < len(pts): out.add(S)
    return list(out)
for n in [2]:
    D = downsets(3, n); conf = np.array(list(itertools.product([-2, -1, 0, 1, 2], repeat=n)), float)
    A = np.abs(conf).astype(int); print("n", n, "downsets", len(D))
    worst = (-np.inf, None)
    for t in range(4000):
        lw = rng.normal(0, 2, 3)  # log weights of |q| = 0,1,2
        J = 10**rng.uniform(-1.5, 0.5); H = 10**rng.uniform(-3, 0.5)
        E_ = J*conf[:, 0]*conf[:, 1] + H*conf.sum(1) + lw[A].sum(1)
        p = np.exp(E_ - E_.max()); p /= p.sum(); E = lambda F: (p*F).sum()
        q0 = conf[:, 0]; Q = conf.sum(1); m = E(q0); c = E(q0*Q) - m*E(Q)
        for S in D:
            F = np.array([tuple(a) in S for a in A], float)
            num = E(q0*F*Q) - E(q0*F)*E(Q); d = num*m - E(q0*F)*c
            s = abs(num*m) + abs(E(q0*F)*c) + 1e-300
            if d/s > worst[0]: worst = (d/s, dict(lw=lw.round(3), J=J, H=H, S=sorted(S)))
    print(worst)

"""Exact test of conjecture GC (teammates' zerod_proof.md §3) for spin-1 ferromagnets
q_x in {-1,0,1}, single-site weight w*delta_0 + delta_{+1} + delta_{-1} (GS class iff w <= 2),
couplings J_xy >= 0, uniform field H. GC infinitesimal form, linear in F:
   Delta(F) := <q0 F ; Q> <q0>  -  <q0 F> <q0 ; Q>   <= 0     for F(|q|) coordinatewise nonincreasing.
Extreme rays (mod constants): F = indicator of a down-set of {0,1}^V in the variables |q_x|.
Prints worst Delta/scale over down-sets."""
import numpy as np, itertools
rng = np.random.default_rng(7)
def downsets(n):
    pts = list(itertools.product([0, 1], repeat=n))
    out = []
    for mask in range(1, 2**len(pts)):
        S = {pts[i] for i in range(len(pts)) if mask >> i & 1}
        ok = all(all(tuple(min(p[k], q[k]) for k in range(n)) in S or not all(q[k] <= p[k] for k in range(n)) for q in pts) for p in S)
        # down-closed: p in S and q <= p  =>  q in S
        ok = all((q in S) for p in S for q in pts if all(q[k] <= p[k] for k in range(n)))
        if ok and len(S) < len(pts): out.append(S)
    return out
for n in [2, 3]:
    D = downsets(n); conf = np.array(list(itertools.product([-1, 0, 1], repeat=n)), float)
    A = np.abs(conf).astype(int)
    worst = (-np.inf, None)
    for t in range(3000 if n == 2 else 1500):
        w = 10**rng.uniform(-2, np.log10(2.0)) if rng.random() < 0.7 else 10**rng.uniform(0, 2)
        J = np.triu(10**rng.uniform(-1.5, 0.7, (n, n)) * (rng.random((n, n)) < 0.8), 1)
        H = 10**rng.uniform(-3, 0.7)
        E_ = np.einsum('ci,ij,cj->c', conf, J, conf) + H*conf.sum(1) + np.log(w)*(conf == 0).sum(1)
        p = np.exp(E_ - E_.max()); p /= p.sum(); E = lambda F: (p*F).sum()
        q0 = conf[:, 0]; Q = conf.sum(1); m = E(q0); c = E(q0*Q) - m*E(Q)
        for S in D:
            F = np.array([tuple(a) in S for a in A], float)
            num = E(q0*F*Q) - E(q0*F)*E(Q)
            d = num*m - E(q0*F)*c; s = abs(num*m) + abs(E(q0*F)*c) + 1e-300
            if d/s > worst[0]: worst = (d/s, dict(n=n, w=w, J=J.round(3).tolist(), H=H, S=sorted(S)))
    print(n, worst)

"""Coordinatewise tests (derivative in one site field h_x, all fields >= 0):
 (T) termwise: rho_k := <s_k><s_i s_j>/<s_1 s_2 s_3> = P^{123g,0}[i <-> j]  nondecreasing in each h_x ?
 (S) S := sum_k rho_k = 1 + 2 P4 nondecreasing in each h_x ?
Exact enumeration, analytic derivatives via covariances."""
import numpy as np, itertools
rng = np.random.default_rng(23)
wT = wS = -np.inf; exT = None
for t in range(3000):
    N = int(rng.integers(3, 10))
    conf = np.array(list(itertools.product([-1, 1], repeat=N)), float)
    J = np.triu(10**rng.uniform(-1.5, 0.6, (N, N))*(rng.random((N, N)) < 0.6), 1)
    h = 10**rng.uniform(-3, 0.7, N)*(rng.random(N) < .75); h[:3] = np.maximum(h[:3], 1e-3)
    E_ = np.einsum('ci,ij,cj->c', conf, J, conf) + conf@h
    p = np.exp(E_ - E_.max()); p /= p.sum(); E = lambda F: (p*F).sum()
    s = conf
    def dlog(F, x):  # d/dh_x log <F>
        return E(F*s[:, x])/E(F) - E(s[:, x])
    t3 = s[:, 0]*s[:, 1]*s[:, 2]
    rho = []; drho = np.zeros((3, N))
    for k in range(3):
        i, j = [a for a in range(3) if a != k]
        r = E(s[:, k])*E(s[:, i]*s[:, j])/E(t3); rho.append(r)
        for x in range(N):
            drho[k, x] = r*(dlog(s[:, k], x) + dlog(s[:, i]*s[:, j], x) - dlog(t3, x))
    relT = (drho.min(1)/np.array(rho)).min()
    relS = (drho.sum(0)/sum(rho)).min()
    if -relT > wT: wT, exT = -relT, (N, J.round(2), h.round(3))
    wS = max(wS, -relS)
print("termwise worst relative decrease:", wT); print(exT)
print("sum S worst relative decrease:", wS)

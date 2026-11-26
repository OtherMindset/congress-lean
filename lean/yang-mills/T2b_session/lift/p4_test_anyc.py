"""|B|=3: P4 := P^{123g,0}[1,2,3,g all connected] = (sum_k <s_k><s_{Bk}>/<s1 s2 s3> - 1)/2  (Aizenman u4 formula).
Symmetric-B IC  <=  P4 nondecreasing in H (given GKS). Test whether P4 is monotone in H on random graphs
(field H*c, c=1 on B, c>=0 elsewhere), and whether IC_3 holds."""
import numpy as np, itertools
rng = np.random.default_rng(19)
wP = -np.inf; ex = None
for t in range(400):
    N = int(rng.integers(3, 10))
    conf = np.array(list(itertools.product([-1, 1], repeat=N)), float)
    J = np.triu(10**rng.uniform(-1.5, 0.6, (N, N))*(rng.random((N, N)) < 0.6), 1)
    c = rng.random(N)*(rng.random(N) < .8); c[:3] = np.maximum(c[:3], 0.02)
    s = conf[:, :3]
    P = []
    for H in np.logspace(-2.5, 1, 70):
        E_ = np.einsum('ci,ij,cj->c', conf, J, conf) + H*conf@c
        p = np.exp(E_ - E_.max()); p /= p.sum(); E = lambda F: (p*F).sum()
        m = [E(s[:, k]) for k in range(3)]
        pr = {0: E(s[:, 1]*s[:, 2]), 1: E(s[:, 0]*s[:, 2]), 2: E(s[:, 0]*s[:, 1])}
        t3 = E(s[:, 0]*s[:, 1]*s[:, 2])
        P.append((sum(m[k]*pr[k] for k in range(3))/t3 - 1)/2)
    d = -np.diff(P).max()  # positive => somewhere decreasing... we want min diff
    dec = -np.min(np.diff(P))
    if dec > wP: wP, ex = dec, (N, np.round(J, 2), np.round(c, 2))
print("largest decrease of P4 along H grid:", wP)
print(ex)

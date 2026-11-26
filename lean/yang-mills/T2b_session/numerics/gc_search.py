"""Targeted GC searches (discrete |q| levels, product rho unless K given).
mode: 'gen2' n=2 general; 'gen3' n=3 general; 'homring' homogeneous levels/weights, uniform-J ring n=3..6;
'homK' homogeneous ring + uniform K>0 (MTP2 coupling of |q|).  Reports max_D d/dh pi(D) and saves worst."""
import numpy as np, json, sys, time
from gc_ising import enumerate_pi, max_downset_cov

mode = sys.argv[1]; ntrial = int(sys.argv[2]); seed = int(sys.argv[3])
rng = np.random.default_rng(seed)
worst = (-1e9, None); nviol = 0; ncase = 0
t0 = time.time()
for trial in range(ntrial):
    if mode in ('gen2', 'gen3', 'gen4', 'gen5', 'homgraph'):
        n = {'gen2': 2, 'gen3': 3, 'gen4': 4, 'gen5': 5, 'homgraph': int(rng.integers(3, 6))}[mode]; k = 2
        v = np.sort(rng.uniform(0.02, 4, size=(n, k)), axis=1)
        f = rng.normal(0, 3, size=(n, k))
        Jm = np.zeros((n, n))
        for x in range(n):
            for y in range(x+1, n):
                if mode in ('gen2', 'gen3') or rng.random() < 0.6:
                    Jm[x, y] = Jm[y, x] = 10**rng.uniform(-2, 1)
        if mode == 'homgraph':
            v = np.tile(v[0], (n, 1)); f = np.tile(f[0], (n, 1))
        Km = np.zeros((n, n))
    else:
        n = int(rng.integers(3, 7)); k = 2 if n > 4 else int(rng.integers(2, 4))
        v1 = np.sort(rng.uniform(0.02, 4, size=k)); f1 = rng.normal(0, 3, size=k)
        v = np.tile(v1, (n, 1)); f = np.tile(f1, (n, 1))
        J = 10**rng.uniform(-2, 1)
        Jm = np.zeros((n, n)); Km = np.zeros((n, n))
        K = 10**rng.uniform(-1, 1) if mode == 'homK' else 0.0
        for x in range(n):
            y = (x+1) % n
            Jm[x, y] = Jm[y, x] = J; Km[x, y] = Km[y, x] = K
    for h in 10**rng.uniform(-3, 1.5, size=5):
        L, R, p, Psi = enumerate_pi(v, f, Jm, Km, h)
        best, D = max_downset_cov(L, p, Psi, k)
        ncase += 1
        if best > 1e-10: nviol += 1
        if best > worst[0]:
            worst = (best, dict(n=int(n), k=int(k), h=float(h), v=v.tolist(), f=f.tolist(), J=Jm.tolist(), K=Km.tolist(), best=float(best), D=[L[i].tolist() for i in D]))
print(mode, "time %.1f" % (time.time()-t0), "cases", ncase, "violations", nviol, "worst dpi(D)/dh", worst[0])
json.dump(dict(worst=worst[1], worstval=worst[0], nviol=nviol, ncase=ncase), open("gc_%s_seed%d.json" % (mode, seed), "w"))

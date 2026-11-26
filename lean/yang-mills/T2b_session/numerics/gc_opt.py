"""Maximise GC violation (discrete two-level |q|, identical sites) by Nelder-Mead.
graph: 'path' (open chain, root at end 0, bonds J_i free), 'pathmid' (root in middle), 'ring' (uniform J).
objective: h * max_D d/dh pi_h(D)  (dimensionless)."""
import numpy as np, json, sys
from scipy.optimize import minimize
from gc_ising import enumerate_pi, max_downset_cov

graph = sys.argv[1]; n = int(sys.argv[2]); seed = int(sys.argv[3])
rng = np.random.default_rng(seed)

def unpack(p):
    v0 = np.exp(p[0]); v1 = v0 + np.exp(p[1]); df = p[2]; h = np.exp(p[3])
    v = np.tile([v0, v1], (n, 1)); f = np.tile([0.0, df], (n, 1))
    Jm = np.zeros((n, n))
    if graph == 'ring':
        J = np.exp(p[4])
        for x in range(n): Jm[x, (x+1) % n] = Jm[(x+1) % n, x] = J
    else:
        order = list(range(n)) if graph == 'path' else [1, 0] + list(range(2, n)) if n > 2 else [0, 1]
        if graph == 'pathmid':
            order = list(range(1, n//2+1))[::-1] + [0] + list(range(n//2+1, n))
        for i in range(n-1):
            a, b = order[i], order[i+1]
            Jm[a, b] = Jm[b, a] = np.exp(p[4+i])
    return v, f, Jm, h

def obj(p):
    if np.any(np.abs(p) > 12): return 1e3
    v, f, Jm, h = unpack(p)
    L, R, pi, Psi = enumerate_pi(v, f, Jm, np.zeros((n, n)), h)
    best, D = max_downset_cov(L, pi, Psi, 2)
    return -h*best

npar = 5 if graph == 'ring' else 4 + n - 1
bestval = 0; bestp = None
for start in range(12):
    p0 = rng.normal(0, 1.5, size=npar)
    r = minimize(obj, p0, method='Nelder-Mead', options=dict(maxiter=1500, xatol=1e-6, fatol=1e-12))
    if -r.fun > bestval:
        bestval, bestp = -r.fun, r.x
    print(start, -r.fun, flush=True)
print(graph, n, "best h*dpi/dh =", bestval)
if bestp is not None:
    v, f, Jm, h = unpack(bestp)
    L, R, pi, Psi = enumerate_pi(v, f, Jm, np.zeros((n, n)), h)
    best, D = max_downset_cov(L, pi, Psi, 2)
    json.dump(dict(worst=dict(n=n, k=2, h=float(h), v=v.tolist(), f=f.tolist(), J=Jm.tolist(), K=np.zeros((n, n)).tolist(), best=float(best), D=[L[i].tolist() for i in D]), val=bestval, params=bestp.tolist()), open("gcopt_%s_%d.json" % (graph, n), "w"))
    print("v", v[0], "df", f[0, 1], "h", h, "J", Jm[np.triu_indices(n, 1)].round(4), "D", [L[i].tolist() for i in D])

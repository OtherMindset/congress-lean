"""Lattice target on arbitrary small graphs (n<=5 sites), real phi^4 single-site weight
exp(-a x^2 - b x^4 + H x), couplings J_xy >= 0 arbitrary (inhomogeneous allowed), root site 0.
Brute-force tensor-product Gauss quadrature (nodes adapted to tilted single-site measure).
Target: R' = (u' m - u chi)/m^2 <= 0, u=<phi0;phi0^2>, chi = sum_x <phi0;phi_x>,
u' = sum_x kappa(phi0, phi0^2, phi_x) (exact, via covariances with sum_x phi_x).
Also reports rho = R'/dH<phi0^2>."""
import numpy as np, itertools, sys, json, time
import transfer as t

def target_graph(a, b, Jm, H, nq, c=0.0, hn=0.0):
    n = len(Jm)
    x, lw = t.gauss_nodes(a, b, H + hn, nq, c=c); lw = lw - hn*x
    grids = np.meshgrid(*([x]*n), indexing='ij')
    P = np.stack([g.ravel() for g in grids], 1)
    LW = np.meshgrid(*([lw]*n), indexing='ij')
    logw = sum(g.ravel() for g in LW) + 0.5*np.einsum('ix,xy,iy->i', P, Jm, P)
    w = np.exp(logw - logw.max()); w /= w.sum()
    p0 = P[:, 0]; M = P.sum(1)
    E = lambda f: np.sum(w*f)
    m = E(p0); Pm = E(p0**2); u = E(p0**3) - m*Pm
    S = lambda f: E(f*M) - E(f)*E(M)
    up = S(p0**3) - m*S(p0**2) - Pm*S(p0)
    chi = S(p0)
    Rp = (up*m - u*chi)/m**2
    return dict(m=m, R=u/m, Rp=Rp, rho=Rp/S(p0**2))

if __name__ == "__main__":
    seed = int(sys.argv[1]); ntrial = int(sys.argv[2]); nsite = int(sys.argv[3])
    rng = np.random.default_rng(seed)
    rows = []; t0 = time.time()
    nq1, nq2 = {2: (24, 32), 3: (18, 24), 4: (12, 16), 5: (9, 11)}[nsite]
    for tr in range(ntrial):
        a = rng.choice([-8, -3, -1, 0, 1, 3]) * 1.0
        Jm = np.zeros((nsite, nsite))
        for x in range(nsite):
            for y in range(x+1, nsite):
                if rng.random() < 0.6:
                    Jm[x, y] = Jm[y, x] = 10**rng.uniform(-1.5, 0.5)
        H = 10**rng.uniform(-2.5, 1)
        z = Jm.sum(1).max()
        cands = []
        for c in (0.0, 0.5*z, z):
            r1 = target_graph(a, 1.0, Jm, H, nq1, c=c); r2 = target_graph(a, 1.0, Jm, H, nq2, c=c)
            cands.append((abs(r2['rho']-r1['rho']), r1, r2))
        cands.sort(key=lambda q: q[0]); _, r1, r2 = cands[0]
        rows.append(dict(a=a, H=H, J=Jm.tolist(), rho=r2['rho'], Rp=r2['Rp'], err=abs(r2['rho']-r1['rho'])))
    print("time %.1f" % (time.time()-t0))
    good = [r for r in rows if r['err'] < 1e-5]
    pos = [r for r in rows if r['rho'] > 0]
    print("n=%d trials %d converged %d  rho>0: %d" % (nsite, len(rows), len(good), len(pos)))
    for r in pos[:5]: print("POS", r)
    b = max(good, key=lambda r: r['rho']); print("closest converged:", b['rho'], "a", b['a'], "H", b['H'], "err", b['err'])
    json.dump(rows, open("graph_target_n%d_seed%d.json" % (nsite, seed), "w"))

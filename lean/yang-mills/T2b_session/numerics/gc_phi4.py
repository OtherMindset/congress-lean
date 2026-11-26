"""GC for real phi^4 spins (single-site exp(-a x^2 - x^4), GHS class) on small graphs (n<=5),
inhomogeneous J>=0. Tests F(|q|) decreasing: Gaussian bumps exp(-(q_x/c)^2), smooth step
1/(1+exp((|q_x|-c)/w)), products over two sites, and G-like F = prod_x exp(-s_x q_x^2).
d/dH <q0 F>/<q0> = [<q0F;M><q0> - <q0F><q0;M>]/<q0>^2 (exact), M = sum q_x.
Tensor Gauss quadrature; each case computed at two node counts and two node families."""
import numpy as np, sys, json, time
import transfer as t

def setup(a, Jm, H, nq, c):
    n = len(Jm)
    x, lw = t.gauss_nodes(a, 1.0, H, nq, c=c)
    grids = np.meshgrid(*([x]*n), indexing='ij')
    P = np.stack([g.ravel() for g in grids], 1)
    LW = np.meshgrid(*([lw]*n), indexing='ij')
    logw = sum(g.ravel() for g in LW) + 0.5*np.einsum('ix,xy,iy->i', P, Jm, P)
    w = np.exp(logw - logw.max()); w /= w.sum()
    return P, w

def Fs(P, rng_params):
    out = {}
    n = P.shape[1]
    for x in range(n):
        for c in (0.3, 0.7, 1.5):
            out['gauss_x%d_c%g' % (x, c)] = np.exp(-(P[:, x]/c)**2)
            out['step_x%d_c%g' % (x, c)] = 1/(1 + np.exp((np.abs(P[:, x]) - c)/0.15))
    for x in range(n):
        for y in range(x+1, n):
            out['step2_%d%d' % (x, y)] = 1/(1 + np.exp((np.abs(P[:, x]) - 0.7)/0.15))/(1 + np.exp((np.abs(P[:, y]) - 0.7)/0.15))
            out['union_%d%d' % (x, y)] = 1 - (1 - 1/(1 + np.exp((np.abs(P[:, x]) - 0.7)/0.15)))*(1 - 1/(1 + np.exp((np.abs(P[:, y]) - 0.7)/0.15)))
    return out

def derivs(P, w):
    q0 = P[:, 0]; M = P.sum(1)
    E = lambda f: np.sum(w*f)
    m = E(q0); cm = E(q0*M) - m*E(M)
    res = {}
    for k, F in Fs(P, None).items():
        a = E(q0*F); ca = E(q0*F*M) - a*E(M)
        res[k] = (ca*m - a*cm)/m**2
    return res

if __name__ == "__main__":
    seed = int(sys.argv[1]); ntrial = int(sys.argv[2]); n = int(sys.argv[3])
    nq1, nq2 = {2: (24, 32), 3: (16, 22), 4: (11, 14), 5: (8, 10)}[n]
    rng = np.random.default_rng(seed)
    worst = (-1e9, None); npos = 0; ncase = 0; t0 = time.time()
    for tr in range(ntrial):
        a = float(rng.choice([-6, -3, -1.5, -0.5, 0, 1, 3]))
        Jm = np.zeros((n, n))
        # random tree plus random extra edges
        for x in range(1, n):
            y = int(rng.integers(0, x)); Jm[x, y] = Jm[y, x] = 10**rng.uniform(-1.5, 0.6)
        for x in range(n):
            for y in range(x+1, n):
                if Jm[x, y] == 0 and rng.random() < 0.2: Jm[x, y] = Jm[y, x] = 10**rng.uniform(-1.5, 0.3)
        H = 10**rng.uniform(-2.5, 0.7)
        z = Jm.sum(1).max()
        best = None
        for c in (0.0, 0.5*z):
            d1 = derivs(*setup(a, Jm, H, nq1, c)); d2 = derivs(*setup(a, Jm, H, nq2, c))
            err = max(abs(d1[k] - d2[k]) for k in d1)
            if best is None or err < best[0]: best = (err, d2)
        err, d = best
        for k, val in d.items():
            ncase += 1
            if val > 10*err + 1e-12:
                npos += 1
            if val - err > worst[0]:
                worst = (val - err, dict(a=a, J=Jm.tolist(), H=H, F=k, val=val, err=err))
    print("n=%d time %.0f cases %d  certified positives %d  worst (val-err) %.3e" % (n, time.time()-t0, ncase, npos, worst[0]))
    print(worst[1])
    json.dump(dict(worst=worst[1], npos=npos, ncase=ncase), open("gc_phi4_n%d_s%d.json" % (n, seed), "w"))

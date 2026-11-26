"""Conjecture GC, discrete version, by exact enumeration.
Sites x=0..n-1, q_x = s_x r_x, s_x = +-1, r_x in {v_x[0] < v_x[1] < ... } (k levels, site dependent).
Absolute-value weight rho(r) log-supermodular on the product lattice (=> MTP2):
   log rho = sum_x f_x(l_x) + sum_{x<y} K_xy * g(l_x) g(l_y)  (K>=0, g increasing) [+ optional cubic supermodular term]
Measure: rho(r) * exp(sum J_xy q_x q_y + h sum q_x).
GC: for every coordinatewise-decreasing F(r):  h -> <q_0 F>/<q_0> nonincreasing.
<q_0 F>/<q_0> = E_pi[F], pi_h(r) ∝ rho(r) A_h(r),  A_h(r) = sum_s r_0 s_0 exp(...)  (>=0 by GKS I).
d/dh E_pi[F] = Cov_pi(F, Psi), Psi = d/dh log A_h.  GC for all F at h  <=>  max over down-sets D
of Cov_pi(1_D, Psi) <= 0  (decreasing F are positive combos of down-set indicators + const).
The max over down-sets is a max-weight closure problem -> min cut (networkx).
Also tests F = specific functions.  Precision: float64 enumeration; violations re-checked in mpmath.
"""
import numpy as np, itertools, networkx as nx, sys, json, time

def setup(n, k, rng, Jscale, Kscale, inhom=True):
    # random levels
    v = np.sort(rng.uniform(0.05, 3.0, size=(n, k)) * (rng.uniform(0.2, 3, size=(n, 1)) if inhom else 1), axis=1)
    f = rng.normal(0, 2, size=(n, k))
    Jm = np.zeros((n, n)); Km = np.zeros((n, n))
    for x in range(n):
        for y in range(x+1, n):
            if rng.random() < 0.7:
                Jm[x, y] = Jm[y, x] = Jscale*rng.exponential()
            if rng.random() < 0.5:
                Km[x, y] = Km[y, x] = Kscale*rng.exponential()
    return v, f, Jm, Km

def enumerate_pi(v, f, Jm, Km, h):
    n, k = v.shape
    L = np.array(list(itertools.product(range(k), repeat=n)))       # level configs
    R = v[np.arange(n)[None, :], L]                                     # (NL, n)
    g = L/(k-1)
    logrho = f[np.arange(n)[None, :], L].sum(1) + 0.5*np.einsum('ix,xy,iy->i', g, Km, g)
    S = np.array(list(itertools.product([-1, 1], repeat=n)))            # (NS, n)
    A = np.zeros(len(L)); B = np.zeros(len(L)); lA = np.zeros(len(L))
    for i, r in enumerate(R):
        q = S*r[None, :]
        E = 0.5*np.einsum('sx,xy,sy->s', q, Jm, q) + h*q.sum(1)
        E0 = E.max(); w = np.exp(E - E0)
        a0 = np.sum(w*q[:, 0]); a1 = np.sum(w*q[:, 0]*q.sum(1))
        lA[i] = np.log(a0) + E0      # log A_h(r)
        B[i] = a1/a0                 # Psi(r)
    lp = logrho + lA
    p = np.exp(lp - lp.max()); p /= p.sum()
    return L, R, p, B

def max_downset_cov(L, p, Psi, k):
    """max over down-sets D of sum_{r in D} p(r)(Psi(r)-mean)  (= Cov(1_D, Psi))."""
    w = p*(Psi - np.sum(p*Psi))
    G = nx.DiGraph()
    index = {tuple(l): i for i, l in enumerate(L)}
    s, t = 'S', 'T'
    for i, l in enumerate(L):
        if w[i] > 0: G.add_edge(s, i, capacity=w[i])
        elif w[i] < 0: G.add_edge(i, t, capacity=-w[i])
        for x in range(len(l)):
            if l[x] > 0:
                l2 = list(l); l2[x] -= 1
                G.add_edge(i, index[tuple(l2)], capacity=float('inf'))   # closure: i in D => lower in D
    G.add_node(s); G.add_node(t)
    cut, (Sset, Tset) = nx.minimum_cut(G, s, t)
    best = w[w > 0].sum() - cut
    D = [i for i in Sset if i != s]
    return best, D

if __name__ == "__main__":
    seed0 = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    ntrial = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = np.random.default_rng(seed0)
    worst = (-1e9, None)
    t0 = time.time()
    results = []
    for trial in range(ntrial):
        n = rng.integers(2, 6); k = rng.integers(2, 4) if n <= 4 else 2
        Jscale = 10**rng.uniform(-1.5, 1); Kscale = 10**rng.uniform(-1, 1)*rng.integers(0, 2)
        v, f, Jm, Km = setup(n, k, rng, Jscale, Kscale)
        for h in 10**rng.uniform(-3, 1, size=4):
            L, R, p, Psi = enumerate_pi(v, f, Jm, Km, h)
            best, D = max_downset_cov(L, p, Psi, k)
            # normalise: Cov / (sd(Psi)) so scale free
            sd = np.sqrt(np.sum(p*(Psi-np.sum(p*Psi))**2))
            val = best/sd if sd > 0 else 0
            results.append(dict(trial=trial, n=int(n), k=int(k), h=float(h), best=float(best), norm=float(val)))
            if val > worst[0]:
                worst = (val, dict(n=int(n), k=int(k), h=float(h), v=v.tolist(), f=f.tolist(), J=Jm.tolist(), K=Km.tolist(), best=float(best), D=[L[i].tolist() for i in D]))
    print("time", time.time()-t0, "cases", len(results))
    viol = [r for r in results if r['best'] > 1e-12]
    print("violations (max_D Cov > 1e-12):", len(viol), "of", len(results))
    print("worst normalised:", worst[0])
    json.dump(dict(worst=worst[1], worstval=worst[0], nviol=len(viol), ncase=len(results)), open("gc_ising_seed%d.json" % seed0, "w"))

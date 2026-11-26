"""Lattice target R'<=0 for spins with a discrete even single-site law on {+-v_0,...,+-v_{k-1}}
(weights e^{f_l}), arbitrary J>=0, exact enumeration (float64; violations re-checked in mpmath).
Modes: 'witness <json>' evaluates the GC witness system; 'search n k ntrial seed [ghs]' random search.
'ghs' restricts to laws that are discretised phi^4 (points of a fine grid are not used; instead
k-point laws with v, f drawn from exp(-a v^2 - v^4)), which are NOT exactly GHS but close."""
import numpy as np, itertools, sys, json, mpmath as mp

def target_discrete(vals, logw, Jm, H):
    n = len(Jm)
    states = np.array(list(itertools.product(range(len(vals)), repeat=n)))
    P = vals[states]; lw = logw[states].sum(1) + 0.5*np.einsum('ix,xy,iy->i', P, Jm, P) + H*P.sum(1)
    w = np.exp(lw - lw.max()); w /= w.sum()
    p0 = P[:, 0]; M = P.sum(1)
    E = lambda f: np.sum(w*f); S = lambda f: E(f*M) - E(f)*E(M)
    m = E(p0); Pm = E(p0**2); u = E(p0**3) - m*Pm
    up = S(p0**3) - m*S(p0**2) - Pm*S(p0); chi = S(p0)
    Rp = (up*m - u*chi)/m**2
    return Rp, Rp/S(p0**2), u/m

def target_discrete_mp(vals, logw, Jm, H, dps=40):
    mp.mp.dps = dps
    n = len(Jm); H = mp.mpf(H)
    acc = {k: mp.mpf(0) for k in ['Z', 'p0', 'p02', 'p03', 'M', 'p0M', 'p02M', 'p03M']}
    for st in itertools.product(range(len(vals)), repeat=n):
        P = [mp.mpf(vals[i]) for i in st]
        lw = sum(mp.mpf(logw[i]) for i in st) + sum(mp.mpf(Jm[x][y])*P[x]*P[y] for x in range(n) for y in range(x+1, n)) + H*sum(P)
        w = mp.exp(lw); M = sum(P); p = P[0]
        acc['Z'] += w; acc['p0'] += w*p; acc['p02'] += w*p**2; acc['p03'] += w*p**3
        acc['M'] += w*M; acc['p0M'] += w*p*M; acc['p02M'] += w*p**2*M; acc['p03M'] += w*p**3*M
    E = {k: acc[k]/acc['Z'] for k in acc}
    S = lambda k: E[k + 'M'] - E[k]*E['M']
    m = E['p0']; Pm = E['p02']; u = E['p03'] - m*Pm
    up = S('p03') - m*S('p02') - Pm*S('p0'); chi = S('p0')
    return (up*m - u*chi)/m**2

if __name__ == "__main__":
    if sys.argv[1] == 'witness':
        w = json.load(open(sys.argv[2]))['worst']
        v = np.array(w['v'][0]); f = np.array(w['f'][0])
        homog = all(np.allclose(w['v'][x], v) for x in range(w['n']))
        print("homogeneous levels:", homog)
        vals = np.concatenate([-v[::-1], v]); logw = np.concatenate([f[::-1], f])
        Jm = np.array(w['J'])
        for H in [1e-3, 1e-2, 0.05, 0.2, 1, 3]:
            print(H, target_discrete(vals, logw, Jm, H))
    else:
        n, k, ntrial, seed = map(int, sys.argv[2:6])
        rng = np.random.default_rng(seed)
        worst = (-1e9, None); npos = 0
        for tr in range(ntrial):
            v = np.sort(rng.uniform(0.02, 4, size=k)); f = rng.normal(0, 3, size=k)
            vals = np.concatenate([-v[::-1], v]); logw = np.concatenate([f[::-1], f])
            Jm = np.zeros((n, n))
            for x in range(n):
                for y in range(x+1, n):
                    if rng.random() < 0.6: Jm[x, y] = Jm[y, x] = 10**rng.uniform(-2, 1)
            for H in 10**rng.uniform(-3, 1, 4):
                Rp, rho, R = target_discrete(vals, logw, Jm, H)
                if rho > worst[0]: worst = (rho, dict(v=v.tolist(), f=f.tolist(), J=Jm.tolist(), H=H, Rp=Rp))
                if rho > 1e-9: npos += 1
        print("n=%d k=%d cases %d  rho>1e-9: %d  max rho %.4g" % (n, k, 4*ntrial, npos, worst[0]))
        json.dump(dict(worst=worst[1], val=worst[0], npos=npos), open("discrete_target_n%d_k%d_s%d.json" % (n, k, seed), "w"))
        if worst[0] > 0:
            ww = worst[1]; v = np.array(ww['v']); f = np.array(ww['f'])
            vals = np.concatenate([-v[::-1], v]); logw = np.concatenate([f[::-1], f])
            print("  mp check R' =", mp.nstr(target_discrete_mp(vals, logw, ww['J'], ww['H']), 15), " float R'=", ww['Rp'])
            print("  params", ww)

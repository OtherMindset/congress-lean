"""Target R(H) nonincreasing, T2b regime, 1D: J=2 per bond (so a - (total coupling) = -delta, as for J=1 with 4 nbrs),
a = 2 - delta, b small; infinite chain and rings L=50, 200; trapezoid n=161 vs 241."""
import numpy as np, json, time
import transfer as t
rows = []; t0 = time.time()
for delta in [1e-3, 1e-2, 0.05, 0.2]:
    for b in [1e-3, 1e-2, 1e-1]:
        for H in 10**np.linspace(-4, 0, 13):
            T1, ph1, L = t.build(2 - delta, b, 2.0, H, n=161); T2, ph2, _ = t.build(2 - delta, b, 2.0, H, n=241, L=L)
            for Lr in (None, 50, 200):
                r1 = t.target(*t.observables(T1, ph1, Lring=Lr)[:2]); r2 = t.target(*t.observables(T2, ph2, Lring=Lr)[:2])
                rows.append(dict(delta=delta, b=b, H=float(H), L=Lr or 'inf', range=float(L), rho=float(r2['rho']), Rp=float(r2['Rp']),
                                 err=float(abs(r1['rho'] - r2['rho'])), m=float(r2['m']), R=float(r2['R'])))
json.dump(rows, open("chain_t2b.json", "w"))
print("time %.0f cases %d" % (time.time() - t0, len(rows)))
pos = [r for r in rows if r['rho'] > 0]; print("rho>0:", len(pos)); [print("  POS", r) for r in pos[:10]]
good = [r for r in rows if r['err'] < 1e-6]; print("converged (err<1e-6):", len(good))
for r in sorted(good, key=lambda r: -r['rho'])[:4]: print("  closest", r)
for d in [1e-3, 1e-2, 0.05, 0.2]:
    for b in [1e-3, 1e-2, 1e-1]:
        g = [r for r in rows if r['delta'] == d and r['b'] == b and r['L'] == 'inf']
        print("delta=%g b=%g inf-chain: rho range [%.3g, %.3g], max err %.1e, m(H=1e-4)=%.3g" % (d, b, min(r['rho'] for r in g), max(r['rho'] for r in g), max(r['err'] for r in g), g[0]['m']))

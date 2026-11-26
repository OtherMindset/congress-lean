"""phi^4 infinite chain (and L=50 ring), homogeneous field, small H, strong J; trapezoid n=161 vs 241."""
import numpy as np, json, time
import transfer as t
rows = []; t0 = time.time()
for a in [-20, -8, -4, -1, 0, 2, 5]:
    for J in [0.5, 1, 2, 4, 8, 16]:
        for H in [1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 0.1]:
            T1, ph1, L = t.build(a, 1.0, J, H, n=161); T2, ph2, _ = t.build(a, 1.0, J, H, n=241, L=L)
            for Lr in (None, 50):
                r1 = t.target(*t.observables(T1, ph1, Lring=Lr)[:2]); r2 = t.target(*t.observables(T2, ph2, Lring=Lr)[:2])
                rows.append(dict(a=a, J=J, H=H, L=Lr or 'inf', rho=float(r2['rho']), err=float(abs(r1['rho']-r2['rho'])), m=float(r2['m']), R=float(r2['R'])))
json.dump(rows, open("chain_smallH.json", "w"))
print("time", time.time()-t0, "cases", len(rows))
pos = [r for r in rows if r['rho'] > 0]; print("rho>0:", len(pos)); [print("  ", r) for r in pos[:8]]
good = [r for r in rows if r['err'] < 1e-6]; print("converged:", len(good))
for r in sorted(good, key=lambda r: -r['rho'])[:5]: print(" closest", r)

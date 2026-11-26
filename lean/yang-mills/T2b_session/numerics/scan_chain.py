"""Scan lattice target on rings L=2,3,4,6,10 and the infinite chain (b=1).
Each point computed at n and ~1.6n grid points; err = |difference| (discretisation+roundoff)."""
import numpy as np, time, json, sys
import transfer as t

As = [-20, -8, -4, -2, -1, 0, 1, 2, 5, 20]
Js = [0.05, 0.2, 0.5, 1, 2, 4, 10]
Hs = 10**np.linspace(-3, 2, 21)
rings = [2, 3, 4, 6, 10, None]
n1, n2 = 101, 161
rows = []
t0 = time.time()
for a in As:
    for J in Js:
        for H in Hs:
            T1, ph1, L = t.build(a, 1.0, J, H, n=n1)
            T2, ph2, _ = t.build(a, 1.0, J, H, n=n2, L=L)
            ev1 = np.linalg.eigh(T1); ev2 = np.linalg.eigh(T2)
            for Lr in rings:
                r1 = t.target(*t.observables(T1, ph1, Lring=Lr)[:2])
                r2 = t.target(*t.observables(T2, ph2, Lring=Lr)[:2])
                rows.append(dict(a=a, J=J, H=float(H), L=Lr if Lr else 'inf', rho=float(r2['rho']),
                                 err=float(abs(r2['rho']-r1['rho'])), Rp=float(r2['Rp']), m=float(r2['m'])))
print("time", time.time()-t0)
json.dump(rows, open("scan_chain.json", "w"))
good = [r for r in rows if r['err'] < 1e-6]
print("points", len(rows), "converged(err<1e-6)", len(good))
pos = [r for r in rows if r['rho'] > 0]
print("rho>0 points:", len(pos))
for r in sorted(pos, key=lambda r: -r['rho'])[:15]: print("  POS", r)
print("closest approach among converged:")
for r in sorted(good, key=lambda r: -r['rho'])[:10]: print("  ", r)
bad = [r for r in rows if r['err'] >= 1e-6]
print("unconverged examples:", [ (r['a'],r['J'],r['H'],r['L'],r['err']) for r in bad[:10]])
for Lr in [2, 3, 4, 6, 10, 'inf']:
    g = [r for r in good if r['L'] == Lr]
    b = max(g, key=lambda r: r['rho'])
    print("L=%s max rho=%.3e at a=%g J=%g H=%.3g ; min rho=%.3f" % (Lr, b['rho'], b['a'], b['J'], b['H'], min(r['rho'] for r in g)))

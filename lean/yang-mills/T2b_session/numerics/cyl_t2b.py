"""T2b regime in 2D: width-3 periodic cylinder (3 x inf) and 3x3 torus, J=1, a=2-delta, b small, uniform field.
Gauss nodes for node measure exp(delta x^2 - b x^4 + (H+hn)x) (c = 2 => mean-field marginal), n=10 vs 13;
two node families (hn=0 symmetric; hn tilted to the + well) -> best-converged pair reported, plus cross-family diff."""
import numpy as np, json, time, sys
import transfer as t
rows = []; t0 = time.time()
for delta in [0.01, 0.05, 0.2]:
    for b in [1e-3, 1e-2, 1e-1]:
        phis = np.sqrt(delta/(2*b))
        for H in [1e-3, 1e-2, 0.03, 0.1, 0.3, 1.0]:
            out = {}
            for tag, hn in (('s', 0.0), ('t', 2*delta*phis + 1.0)):
                for n in (10, 13):
                    T, ph = t.build_gauss2(2 - delta, b, 1.0, H, n, W=3, c=2.0, hn=hn)
                    for Lr in (None, 3):
                        out[(tag, n, Lr)] = t.target(*t.observables(T, ph, Lring=Lr)[:2])
            for Lr in (None, 3):
                ds = abs(out[('s', 13, Lr)]['rho'] - out[('s', 10, Lr)]['rho']); dt = abs(out[('t', 13, Lr)]['rho'] - out[('t', 10, Lr)]['rho'])
                tag = 's' if ds <= dt else 't'
                r = out[(tag, 13, Lr)]
                rows.append(dict(delta=delta, b=b, H=H, L='3xinf' if Lr is None else '3x3', rho=float(r['rho']), Rp=float(r['Rp']), m=float(r['m']),
                                 err=float(min(ds, dt)), cross=float(abs(out[('s', 13, Lr)]['rho'] - out[('t', 13, Lr)]['rho']))))
                print(rows[-1], flush=True)
json.dump(rows, open("cyl_t2b.json", "w"))
print("time %.0f" % (time.time() - t0))
pos = [r for r in rows if r['rho'] > 0]; print("rho>0:", len(pos)); [print("  POS", r) for r in pos]
good = [r for r in rows if r['err'] < 1e-4]; print("converged(err<1e-4):", len(good), "/", len(rows))
for r in sorted(good, key=lambda r: -r['rho'])[:4]: print("  closest", r)

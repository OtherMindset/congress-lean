"""2D tests via column transfer matrices with Gauss nodes (n per site):
 W=2 ladder (open rung), W=3 periodic: 3x3 torus (Lring=3), 3xinf cylinder; W=4 periodic: 4x4 torus, 4xinf.
Convergence: compare n and n+dn."""
import numpy as np, time, json, sys
import transfer as t

W = int(sys.argv[1]); n1 = int(sys.argv[2]); n2 = int(sys.argv[3])
As = [float(v) for v in sys.argv[4].split(',')]
Js = [float(v) for v in sys.argv[5].split(',')]
Hs = [float(v) for v in sys.argv[6].split(',')]
rings = {2: [2, 4, None], 3: [3, None], 4: [4, None]}[W]
z = 3 if W == 2 else 4
rows = []
t0 = time.time()
for a in As:
    for J in Js:
        for H in Hs:
            c = 0.75*z*J
            phis = np.sqrt(max((z*J - 2*a)/4, 0.25))
            out = {}
            for tag, hn in (('s', 0.0), ('t', z*J*phis)):
                for n in (n1, n2):
                    T, ph = t.build_gauss2(a, 1.0, J, H, n, W=W, c=c, hn=hn)
                    for Lr in rings:
                        out[(tag, n, Lr)] = t.target(*t.observables(T, ph, Lring=Lr)[:2])
            for Lr in rings:
                ds = abs(out[('s', n2, Lr)]['rho'] - out[('s', n1, Lr)]['rho'])
                dt = abs(out[('t', n2, Lr)]['rho'] - out[('t', n1, Lr)]['rho'])
                tag = 's' if ds <= dt else 't'
                r1, r2 = out[(tag, n1, Lr)], out[(tag, n2, Lr)]
                row = dict(W=W, a=a, J=J, H=H, L=Lr if Lr else 'inf', rho=float(r2['rho']),
                           err=float(abs(r2['rho']-r1['rho'])), nodes=tag, cross=float(abs(out[('s',n2,Lr)]['rho']-out[('t',n2,Lr)]['rho'])), m=float(r2['m']), Rp=float(r2['Rp']))
                rows.append(row)
                print(row, flush=True)
print("time", time.time()-t0)
json.dump(rows, open("scan_2d_W%d.json" % W, "w"))
pos = [r for r in rows if r['rho'] > 0]
print("rho>0:", len(pos), pos)
good = [r for r in rows if r['err'] < 1e-4]
print("converged(err<1e-4):", len(good), "/", len(rows))
for r in sorted(good, key=lambda r: -r['rho'])[:5]: print("closest", r)

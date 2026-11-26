"""Psi-monotonicity in the T2b regime: J=1 (and 2), a in [0.5,3], b in [1e-3,1]; ring3, ring4, torus2x2 (=ring4 with 2J)."""
import numpy as np, json, sys, time
import psi_test as P
part = int(sys.argv[1]); nparts = int(sys.argv[2])
cases = []
for J in [1.0, 2.0]:
    for b in [0.001, 0.01, 0.1, 1.0]:
        for a in [0.5, 1.0, 1.5, 1.9, 1.98, 2.02, 2.5, 3.0]:
            for L, Jf, tag in [(3, 1, 'ring3'), (4, 1, 'ring4'), (4, 2, 'torus2x2')]:
                if J == 2.0 and b not in (0.01, 1.0): continue
                cases.append((a, b, J, L, Jf, tag))
cases = cases[part::nparts]
out = []
for a, b, J, L, Jf, tag in cases:
    t0 = time.time()
    Jeff = J*Jf; Jsite = Jeff           # uniform-config coupling per site (ring: 2 bonds * Jeff/2... = Jeff)
    phis2 = max(0.0, (Jsite - a)/(2*b))
    width = 1/np.sqrt(2*a + 12*b*phis2 + 1e-9)
    hscale = max(abs(a - Jsite), 0.05)**1.5/np.sqrt(b)
    hs = list(10**np.linspace(-3, np.log10(max(5.0, 3*hscale)), 16))
    Lr = P.choose_range(a, b, Jsite, max(hs))
    n = int(np.ceil(2*Lr/(0.3*width)))
    if n > 221:
        print(tag, a, b, J, "SKIP n would be", n, flush=True); continue
    n = max(n, 81)
    x, lw, K = P.grid_setup(a, b, Jeff, n, Lr)
    res = [P.psi_point(x, lw, K, L, h) for h in hs]
    psi = np.array([r[1] for r in res]); err = max(r[2] for r in res)
    inc = np.diff(psi)
    row = dict(a=a, b=b, J=J, tag=tag, n=n, maxinc=float(inc.max()), relinc=float((inc/np.abs(psi[:-1])).max()), kerr=float(err),
               v=[float(r[0]) for r in res], psi=psi.tolist(), hs=hs)
    out.append(row)
    print(tag, "a=%g b=%g J=%g n=%d  max dPsi %.3e  rel %.3e  kerr %.1e (%.0fs)" % (a, b, J, n, row['maxinc'], row['relinc'], err, time.time()-t0), flush=True)
    json.dump(out, open("psi_t2b_p%d.json" % part, "w"))

import numpy as np, json, sys, time
import psi_test as P
part = int(sys.argv[1]); n = int(sys.argv[2])
cases = []
for a in [-4.0, -1.0, 0.0, 2.0]:
    for J in [0.3, 1.0, 2.0, 4.0]:
        for L, Jf, tag in [(2, 1, 'ring2'), (3, 1, 'ring3'), (4, 1, 'ring4'), (4, 2, 'torus2x2'), (8, 1, 'ring8')]:
            cases.append((a, J, L, Jf, tag))
cases = cases[part::2]
hs = list(10**np.linspace(-3, 0.7, 16))
out = []
for a, J, L, Jf, tag in cases:
    t0 = time.time()
    Jeff = J*Jf
    xs = np.linspace(-15, 15, 30001)
    lwt = -a*xs**2 - xs**4 + (2*Jeff*np.abs(xs) + max(hs))*np.abs(xs)
    Lr = np.abs(xs[lwt > lwt.max() - 40]).max()
    x, lw, K = P.grid_setup(a, 1.0, Jeff, n, Lr)
    res = [P.psi_point(x, lw, K, L, h) for h in hs]
    psi = np.array([r[1] for r in res]); err = max(r[2] for r in res)
    inc = np.diff(psi)
    row = dict(a=a, J=J, tag=tag, L=L, maxinc=float(inc.max()), relinc=float((inc/psi[:-1]).max()), err=float(err), v=[float(r[0]) for r in res], psi=psi.tolist())
    out.append(row)
    print(tag, a, J, "max dPsi %.3e  rel %.3e  kerr %.1e  (%.0fs)" % (row['maxinc'], row['relinc'], err, time.time()-t0), flush=True)
json.dump(out, open("psi_batch_p%d_n%d.json" % (part, n), "w"))

"""Analysis for the eps-scaling study (adapted from analyze.py of the validated code).
usage: analyze_eps.py tag  -> results_<tag>.json.  Per point: H=0 stats, taus, WHAM (Z2-symmetrised multihistogram of H=0 + direct
runs, jackknife over 20 aligned blocks) on SGRID, margin r = -dR/dH / D with jackknife error, EOM residual with jackknife error
(for reweighted points and direct runs)."""
import numpy as np, json, sys
import ana
from ana import load, wham, direct, tau_int
tag = sys.argv[1]
meta = json.load(open(f'runs/meta_{tag}.json'))
import os
THINMAX = int(os.environ.get('THINMAX', 100000))   # WHAM inputs thinned (every k-th sweep) so each run has <= THINMAX samples; direct-run stats use all data
def thin(d): k = max(1, -(-len(d) // THINMAX)); return d[::k]
SGRID = [float(x) for x in os.environ.get('SGRID', '0.1,0.3,1,3,10').split(',')]
def eom_err(dat, a, b, H, nblk=20):
    A, B, C = dat.T[:3] if dat.shape[1] != 3 else dat.T
    x = (4 - 2 * a) * A - 4 * b * C + H
    mb = np.array([v.mean() for v in np.array_split(x, nblk)])
    return float(x.mean()), float(mb.std(ddof=1) / np.sqrt(nblk))
out = {}
for key, md in meta.items():
    a, b, L = md['a'], md['b'], md['L']; N = L * L; ana.EOM_AB[:] = [a, b]
    d0 = load(md['H0'], True); A, B, C, F = d0.T; d0 = d0[:, :3]; Mabs = md['Mabs']
    chi_c = N * (np.mean(A**2) - np.mean(np.abs(A))**2)
    xi = np.sqrt(max(chi_c / np.mean(F) - 1, 0)) / (2 * np.sin(np.pi / L))
    U = 1 - np.mean(A**4) / (3 * np.mean(A**2)**2)
    r = dict(a=a, b=b, L=L, mstar=float(np.mean(np.abs(A))), chi=float(N * np.mean(A**2)), chib=float(b * N * np.mean(A**2)), U=float(U),
             chi_conn=float(chi_c), xi2=float(xi), tau_absA=tau_int(np.abs(A)), tau_B=tau_int(B), n0=len(A), nd=md['nd'], flip=[], direct=[])
    runs = [(0.0, thin(d0))] + [(float(H), thin(load(fn))) for H, fn in md['direct'].items() if float(H) * Mabs <= 10.5]   # runs at s>10 enter only the direct estimator (WHAM over s up to 100 did not converge in reasonable time)
    tdir = {}
    for H, fn in md['direct'].items():
        dd = load(fn); tdir[fn] = (tau_int(np.abs(dd[:, 0])), tau_int(dd[:, 1]))
    Ht = [s / Mabs for s in SGRID]
    W = wham(runs, N, Ht, nblk=20)
    for i, s in enumerate(SGRID):
        H = Ht[i]; o = {k: (float(W[k][0][i]), float(W[k][1][i])) for k in W}
        r['flip'].append(dict(s=s, H=H, R=o['R'], dRdH=o['dRdH'], D=o['D'], m=o['m'], chi=o['chi'], margin=o['margin'],
                              sig_dR=o['dRdH'][0] / o['dRdH'][1], sig_margin=o['margin'][0] / o['margin'][1],
                              eom=[o['eo0'][0] + H, o['eo0'][1]], eom_pull=(o['eo0'][0] + H) / o['eo0'][1]))
    for H, fn in md['direct'].items():
        H = float(H); dd = load(fn); o = direct(dd, N, 50)
        e, ee = eom_err(dd, a, b, H)
        r['direct'].append(dict(s=H * Mabs, H=H, dRdH=[float(x) for x in o['dRdH']], margin=[float(x) for x in o['margin']],
                                eom=[e, ee], eom_pull=e / ee, tau_absA=tdir[fn][0], tau_B=tdir[fn][1], n=len(dd)))
    out[key] = r
    f = r['flip']
    print(f"== {key}: L={L} a={a} b={b} m*={r['mstar']:.4f} chi={r['chi']:.4g} chi*b={r['chib']:.3f} U={U:.4f} xi2={xi:.2f} tau(|A|,B)=({r['tau_absA']:.1f},{r['tau_B']:.1f}) nind~{len(A)/(2*r['tau_absA']):.0f}", flush=True)
    for x in f: print(f"   s={x['s']:5.2f} margin={x['margin'][0]:.4f}+-{x['margin'][1]:.4f} ({x['sig_margin']:.0f}sig) dR/dH={x['dRdH'][0]:.4g} ({x['sig_dR']:.0f}sig) EOMpull={x['eom_pull']:.2f}")
    for x in r['direct']: print(f"   DIR s={x['s']:6.2f} margin={x['margin'][0]:.4f}+-{x['margin'][1]:.4f} EOMpull={x['eom_pull']:.2f} tau(|A|,B)=({x['tau_absA']:.1f},{x['tau_B']:.1f})")
    json.dump(out, open(f'results_{tag}.json', 'w'), indent=1, default=float)

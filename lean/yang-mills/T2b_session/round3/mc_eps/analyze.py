"""Analysis of production runs -> results.json and a text table.
For each (b,a,L):
  * H=0 run: m* = <|A|>, chi (per site) = N<A^2>, chi_tot = N^2<A^2>, xi_2nd, tau_int.
  * flip regime s = H<|M|>_0 in a grid: multihistogram (WHAM) of the H=0 run (Z2-symmetrised)
    and the direct runs at s = 1, 10; plus plain H=0 reweighting with several block counts.
  * direct runs (no reweighting) at s = 1, 10 and at reference fields.
  Observables: R, dR/dH (as a correlation), sig = dRdH/err, margin = -dRdH/D with
  D = d<phi^2>/dH = -dm/da, Q_mu = (m - H chi)/(b m^2 (-d_mu m)) with -d_mu m = D/2
  (L with K=0 <=> Q_mu <= 8; exact identity Q_mu = 8(1 + dRdH/D)), EOM residual
  (4-2a)m - 4b<C> + H (exactly 0 in expectation)."""
import numpy as np, json, sys
from ana import load, reweight_sym, direct, wham, tau_int, obs_from_moments, jack

meta = json.load(open('runs/meta.json'))
def _f(x): return float(x.replace('np.float64(', '').rstrip(')'))
for md in meta.values(): md['direct'] = {_f(k): v for k, v in md['direct'].items()}
SGRID = [0.03, 0.1, 0.3, 0.5, 1.0, 2.0, 3.0, 5.0, 10.0]
only = sys.argv[1:]

def extras(o, a, b, H):
    m, chi, D, R, dR, C = [o[k][0] for k in ('m', 'chi', 'D', 'R', 'dRdH', 'C')]
    Q = (m - H * chi) / (b * m * m * D / 2)
    return dict(Q=Q, Qid=8 * (1 + dR / D), margin=-dR / D, eom_pt=(4 - 2 * a) * m - 4 * b * C + H)

def eom_err(dat, a, b, H, nblk=20):
    A, B, C = dat.T
    x = (4 - 2 * a) * A - 4 * b * C + H
    n = len(x); bl = np.array_split(x, nblk); mb = np.array([v.mean() for v in bl])
    return x.mean(), mb.std(ddof=1) / np.sqrt(nblk)

out = json.load(open('results.json')) if (only and __import__('os').path.exists('results.json')) else {}
for key, md in meta.items():
    if only and key not in only: continue
    a, b, L = md['a'], md['b'], md['L']; N = L * L
    d0 = load(md['H0'], True); A, B, C, F = d0.T; d0 = d0[:, :3]
    Mabs = md['Mabs']
    chi_c = N * (np.mean(A**2) - np.mean(np.abs(A))**2)
    xi = np.sqrt(max(chi_c / np.mean(F) - 1, 0)) / (2 * np.sin(np.pi / L))
    r = dict(a=a, b=b, L=L, mstar=float(np.mean(np.abs(A))), chi=float(N * np.mean(A**2)),
             chi_tot=float(N * N * np.mean(A**2)), chi_conn=float(chi_c), xi2=float(xi),
             tau_absA=tau_int(np.abs(A)), tau_A=tau_int(A), tau_B=tau_int(B), Hflip=1 / Mabs,
             eom_H0=eom_err(d0, a, b, 0.0), flip=[], direct=[])
    runs = [(0.0, d0)] + [(float(H), load(fn)) for H, fn in md['direct'].items() if float(H) * Mabs <= 10.5]
    Ht = [s / Mabs for s in SGRID]
    W = wham(runs, N, Ht, nblk=20)
    rw = {nb: [reweight_sym(d0, N, H, nb) for H in Ht] for nb in (20, 100, 400)}
    for i, s in enumerate(SGRID):
        H = Ht[i]
        o = {k: (float(W[k][0][i]), float(W[k][1][i])) for k in W}
        e = extras(o, a, b, H)
        sigs = {nb: rw[nb][i]['dRdH'][0] / rw[nb][i]['dRdH'][1] for nb in rw}
        r['flip'].append(dict(s=s, H=H, R=o['R'], dRdH=o['dRdH'], sig=o['dRdH'][0] / o['dRdH'][1], m=o['m'], D=o['D'],
                              rw0_dRdH=[float(rw[100][i]['dRdH'][0]), float(rw[100][i]['dRdH'][1])],
                              sig_rw_by_nblk={str(k): float(v) for k, v in sigs.items()}, **{k: float(v) for k, v in e.items()}))
    for H, fn in md['direct'].items():
        H = float(H); dd = load(fn)
        o = direct(dd, N, 50); o20 = direct(dd, N, 10); o200 = direct(dd, N, 250)
        e = extras(o, a, b, H)
        r['direct'].append(dict(s=H * Mabs, H=H, R=[float(x) for x in o['R']], dRdH=[float(x) for x in o['dRdH']],
                                sig=float(o['dRdH'][0] / o['dRdH'][1]),
                                sig_by_nblk={'10': float(o20['dRdH'][0] / o20['dRdH'][1]), '50': float(o['dRdH'][0] / o['dRdH'][1]), '250': float(o200['dRdH'][0] / o200['dRdH'][1])},
                                m=[float(x) for x in o['m']], eom=eom_err(dd, a, b, H), **{k: float(v) for k, v in e.items()}))
    out[key] = r
    print(f"== {key}: m*={r['mstar']:.4f} chi={r['chi']:.4g} chi_tot={r['chi_tot']:.4g} chi_conn={chi_c:.3f} xi2={xi:.2f} tau(|A|,A,B)=({r['tau_absA']:.1f},{r['tau_A']:.1f},{r['tau_B']:.1f}) EOM(H0)={r['eom_H0'][0]:.2e}+-{r['eom_H0'][1]:.1e}", flush=True)
    for f in r['flip']:
        print(f"  WHAM s={f['s']:5.2f} H={f['H']:.3e} m={f['m'][0]:.4f} R={f['R'][0]:.5f}+-{f['R'][1]:.5f} dR/dH={f['dRdH'][0]:.4g}+-{f['dRdH'][1]:.2g} sig={f['sig']:.1f} [rw sig nblk20/100/400: {', '.join(f'{v:.1f}' for v in f['sig_rw_by_nblk'].values())}] margin={f['margin']:.4f} Q={f['Q']:.3f} Qid={f['Qid']:.3f}")
    for f in r['direct']:
        print(f"  DIR  s={f['s']:7.2f} H={f['H']:.3e} m={f['m'][0]:.4f} R={f['R'][0]:.5f}+-{f['R'][1]:.5f} dR/dH={f['dRdH'][0]:.4g}+-{f['dRdH'][1]:.2g} sig={f['sig']:.1f} [nblk10/50/250: {', '.join(f'{v:.1f}' for v in f['sig_by_nblk'].values())}] margin={f['margin']:.4f} Q={f['Q']:.3f} EOM={f['eom'][0]:.1e}+-{f['eom'][1]:.1e}")
    json.dump(out, open('results.json', 'w'), indent=1, default=float)

"""Summary table from results.json (writes table.txt)."""
import json, numpy as np
r = json.load(open('results.json'))
lines = []; P = lambda s: lines.append(s)
P(f"{'b':>5} {'a':>5} {'L':>4} {'xi2':>5} {'m*':>6} {'chi':>7} {'src':>4} {'s=H<|M|>':>9} {'H':>9} {'R':>9} {'dR/dH':>11} {'err':>8} {'sig':>7} {'sig(nblk alt)':>16} {'margin':>7} {'Q_mu':>6}")
worst_sig = (-1e9, None); worst_margin = (1e9, None); pulls = []
for k, v in r.items():
    for f in v['flip']:
        if f['s'] in (0.1, 1.0, 3.0, 10.0):
            alt = '/'.join(f"{x:.0f}" for x in f['sig_rw_by_nblk'].values())
            P(f"{v['b']:5} {v['a']:5} {v['L']:4} {v['xi2']:5.2f} {v['mstar']:6.3f} {v['chi']:7.0f} {'MH':>4} {f['s']:9.2f} {f['H']:9.2e} {f['R'][0]:9.5f} {f['dRdH'][0]:11.4g} {f['dRdH'][1]:8.2g} {f['sig']:7.1f} {alt:>16} {f['margin']:7.3f} {f['Q']:6.2f}")
        if f['sig'] > worst_sig[0]: worst_sig = (f['sig'], (k, 'MH', f['s']))
        if f['margin'] < worst_margin[0]: worst_margin = (f['margin'], (k, 'MH', f['s']))
    for f in sorted(v['direct'], key=lambda x: x['s']):
        alt = '/'.join(f"{x:.0f}" for x in f['sig_by_nblk'].values())
        P(f"{v['b']:5} {v['a']:5} {v['L']:4} {'':5} {'':6} {'':7} {'DIR':>4} {f['s']:9.2f} {f['H']:9.2e} {f['R'][0]:9.5f} {f['dRdH'][0]:11.4g} {f['dRdH'][1]:8.2g} {f['sig']:7.1f} {alt:>16} {f['margin']:7.3f} {f['Q']:6.2f}")
        if f['sig'] > worst_sig[0]: worst_sig = (f['sig'], (k, 'DIR', f['s']))
        if f['margin'] < worst_margin[0]: worst_margin = (f['margin'], (k, 'DIR', f['s']))
        # consistency of direct run with multihistogram at the same s (s = 1, 10)
        for g in v['flip']:
            if abs(g['s'] - f['s']) < 1e-6:
                pulls.append((f['dRdH'][0] - g['dRdH'][0]) / np.hypot(f['dRdH'][1], g['dRdH'][1]))
    P('')
P(f"least negative significance (max sig): {worst_sig}")
P(f"smallest relative margin -dRdH/D (= 1 - Q_mu/8): {worst_margin}")
P(f"direct-vs-multihistogram pulls in dR/dH at s=1,10 (not independent, the direct runs are inputs): {np.round(pulls,2).tolist()}")
P(f"max |Q - Qid| over flip grid: {max(abs(f['Q']-f['Qid']) for v in r.values() for f in v['flip']):.3g}")
open('table.txt', 'w').write('\n'.join(lines) + '\n'); print('\n'.join(lines))

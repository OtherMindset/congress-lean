"""Assemble tables for RESULTS.md from results_*.json. Replicates (same b,a,L, different seeds) are combined by inverse-variance weighting."""
import json, glob, numpy as np
R = {}
for f in glob.glob('results_*.json'):
    if f.endswith('test.json') or f.endswith('ext.json'): continue
    R.update(json.load(open(f)))
EPS = {0.08: 1.0, 0.02: 0.5, 0.005: 0.25, 0.00125: 0.125}
groups = {  # label -> (family, keys)
 'B0': ('B/A', ['k0_b0.08_L32', 'R0_b0.08_L32']), 'B1': ('B', ['B1_b0.02_L64', 'R1_b0.02_L64']), 'B2': ('B', ['B2_b0.005_L128', 'R2_b0.005_L128']),
 'B3': ('B', ['B3_b0.00125_L256']), 'A1': ('A', ['A1_b0.02_L64']), 'A2': ('A', ['A2_b0.005_L128'])}
def comb(vals):  # list of (v,e)
    w = np.array([1 / e**2 for v, e in vals]); v = np.array([v for v, e in vals])
    return float((w * v).sum() / w.sum()), float(1 / np.sqrt(w.sum()))
out = {}
print('| group | key | b | L | a | s | r = -dR/dH / D | +- | sigma(r>0) | -dR/dH sigma | EOM pull (reweighted) |')
print('|---|---|---|---|---|---|---|---|---|---|---|')
for g, (fam, keys) in groups.items():
    keys = [k for k in keys if k in R]
    if not keys: continue
    for k in keys:
        r = R[k]
        for x in r['flip']:
            print(f"| {g} | {k} | {r['b']} | {r['L']} | {r['a']} | {x['s']:g} | {x['margin'][0]:.4f} | {x['margin'][1]:.4f} | {x['sig_margin']:.0f} | {-x['sig_dR']:.0f} | {x['eom_pull']:.2f} |")
    ss = sorted({x['s'] for k in keys for x in R[k]['flip']})
    out[g] = {}
    for s in ss:
        vals = [tuple(x['margin']) for k in keys for x in R[k]['flip'] if x['s'] == s]
        out[g][s] = comb(vals)
print()
print('## Combined (replicate-averaged) margin r(s)')
allS = sorted({s for g in out for s in out[g]})
print('| group | b | L | eps/eps0 | ' + ' | '.join(f's={s:g}' for s in allS) + ' |'); print('|---|---|---|---|' + '---|' * len(allS))
for g in out:
    r = R[groups[g][1][0]]
    print(f"| {g} | {r['b']} | {r['L']} | {EPS[r['b']]} | " + ' | '.join((f"{out[g][s][0]:.4f}+-{out[g][s][1]:.4f}" if s in out[g] else '-') for s in allS) + ' |')
print()
print('## Scale-free matching diagnostics (H=0 runs)')
print('| key | b | L | a | m* | chi*b | U | xi2/L | tau_int(|A|) | tau_int(B) | n_ind(~n/2tau) |'); print('|---|---|---|---|---|---|---|---|---|---|---|')
for k, r in sorted(R.items(), key=lambda kv: -kv[1]['b']):
    print(f"| {k} | {r['b']} | {r['L']} | {r['a']} | {r['mstar']:.4f} | {r['chib']:.2f} | {r['U']:.4f} | {r['xi2']/r['L']:.3f} | {r['tau_absA']:.1f} | {r['tau_B']:.1f} | {r['n0']/(2*r['tau_absA']):.0f} |")
print()
print('## EOM pulls (direct runs, naive 20-block error; reweighted points above)')
p = [x['eom_pull'] for r in R.values() for x in r['direct']]; pf = [x['eom_pull'] for r in R.values() for x in r['flip']]
print(f"direct: n={len(p)} mean={np.mean(p):.2f} rms={np.sqrt(np.mean(np.square(p))):.2f} max|p|={np.max(np.abs(p)):.2f}; reweighted: n={len(pf)} mean={np.mean(pf):.2f} rms={np.sqrt(np.mean(np.square(pf))):.2f} max|p|={np.max(np.abs(pf)):.2f} (reweighted pulls are strongly correlated across s within a point)")
print()
print('## Trend fits: r(s) vs eps (weighted LS over family-B groups)')
G = [g for g in ('B0', 'B1', 'B2', 'B3') if g in out]
eps = np.array([EPS[R[groups[g][1][0]]['b']] for g in G])
for s in allS:
    if not all(s in out[g] for g in G): continue
    y = np.array([out[g][s][0] for g in G]); e = np.array([out[g][s][1] for g in G])
    res = []
    for name, f in (('eps', lambda x: x), ('eps^2', lambda x: x**2), ('log2(eps)', lambda x: np.log2(x))):
        X = np.vstack([np.ones_like(eps), f(eps)]).T; W = 1 / e**2
        cov = np.linalg.inv(X.T @ (X * W[:, None])); beta = cov @ (X.T @ (W * y)); chi2 = float(((y - X @ beta)**2 * W).sum())
        res.append(f"{name}: r0={beta[0]:.4f}+-{np.sqrt(cov[0,0]):.4f}, slope={beta[1]:.4f}+-{np.sqrt(cov[1,1]):.4f}, chi2/dof={chi2:.1f}/{len(y)-2}")
    print(f"- s={s:g}: " + ' ; '.join(res))
json.dump({g: {str(s): v for s, v in d.items()} for g, d in out.items()}, open('combined_margins.json', 'w'), indent=1)

print()
print('## Extension to large s (direct-run estimator only, no reweighting; margin = -dR/dH / D)')
ext = {}
for k, r in R.items():
    if k.startswith('R'):
        for x in r['direct']:
            if x['s'] > 20: ext.setdefault((k, round(x['s'])), []).append((x['margin'][0], x['margin'][1], x['eom_pull'], r['b'], r['L']))
try:
    for x in json.load(open('results_ext.json')): ext.setdefault((x['key'], round(x['s'])), []).append((x['margin'][0], x['margin'][1], x['eom_pull'], x['b'], x['L']))
except FileNotFoundError: pass
print('| key | b | L | eps/eps0 | s | margin | +- | EOM pull |'); print('|---|---|---|---|---|---|---|---|')
for (k, s), v in sorted(ext.items(), key=lambda kv: (-kv[1][0][3], kv[0][1])):
    m, e, p, b, L = v[0]; print(f'| {k} | {b} | {L} | {EPS[b]} | {s} | {m:.4f} | {e:.4f} | {p:.2f} |')

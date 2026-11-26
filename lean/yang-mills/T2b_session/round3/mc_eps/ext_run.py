"""Extension to large flip variable s (direct-run estimator only; no reweighting). Runs phi4 at H = s/Mabs (Mabs from the point's H=0 run) and
computes margin = -dR/dH / D by jackknife (50 blocks), EOM pull (20 blocks)."""
import json, subprocess, os, zlib, numpy as np
from multiprocessing import Pool
import ana
from ana import load, direct
def M(tag, key): return json.load(open(f'runs/meta_{tag}.json'))[key]
JOBS = []
for tag, key, ss, nd in [('p3', 'B3_b0.00125_L256', (30, 100, 300), 40000), ('r0', 'R0_b0.08_L32', (300,), 60000), ('r1', 'R1_b0.02_L64', (300,), 60000), ('r2', 'R2_b0.005_L128', (300,), 60000)]:
    m = M(tag, key)
    for s in ss: JOBS.append((key, m, s, nd))
def go(j):
    key, m, s, nd = j; H = s / m['Mabs']; fn = f'runs/{key}_s{s:g}.bin'
    if not (os.path.exists(fn) and os.path.getsize(fn) == 32 * nd):
        subprocess.run(['./phi4', str(m['L']), repr(m['a']), repr(m['b']), repr(H), '5000', str(nd), '1', str(zlib.crc32(repr((key, s)).encode()) % 2**31), fn, '0.67'], check=True, stderr=subprocess.DEVNULL)
    d = load(fn); ana.EOM_AB[:] = [m['a'], m['b']]; o = direct(d, m['L']**2, 50)
    x = (4 - 2 * m['a']) * d[:, 0] - 4 * m['b'] * d[:, 2] + H; mb = np.array([v.mean() for v in np.array_split(x, 20)])
    return dict(key=key, b=m['b'], L=m['L'], s=s, margin=[float(v) for v in o['margin']], dRdH=[float(v) for v in o['dRdH']], eom_pull=float(x.mean() / (mb.std(ddof=1) / np.sqrt(20))), tau=ana.tau_int(np.abs(d[:, 0])), n=nd)
if __name__ == '__main__':
    with Pool(2) as p: res = p.map(go, sorted(JOBS, key=lambda j: -j[1]['L']))
    json.dump(res, open('results_ext.json', 'w'), indent=1)
    for r in res: print(r['key'], r['s'], f"margin={r['margin'][0]:.4f}+-{r['margin'][1]:.4f} dR/dH={r['dRdH'][0]:.4g}+-{r['dRdH'][1]:.2g} EOMpull={r['eom_pull']:.2f} tau={r['tau']:.1f}")

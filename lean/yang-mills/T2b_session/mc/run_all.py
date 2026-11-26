"""Production runs (sequential, one core). For each (b, a, L): H=0 run, direct runs at
H = s/<|M|>_0 for s in {1, 10}, and reference (moderate) fields."""
import numpy as np, subprocess, os, json, sys
from ana import load
os.makedirs('runs', exist_ok=True)
# (b, a, tag, m_guess)
POINTS = [
    (0.5, 0.70, 'deep', 0.87), (0.5, 0.80, 'mod', 0.75), (0.5, 0.88, 'nearc', 0.6),
    (0.1, 1.60, 'deep', 1.09), (0.1, 1.65, 'mod', 0.92), (0.1, 1.69, 'nearc', 0.7),
    (0.02, 1.88, 'deep', 1.38), (0.02, 1.91, 'mod', 0.99), (0.02, 1.92, 'nearc', 0.76),
]
CFG = {32: dict(n0=200000, nd=50000, refs=[0.01, 0.05, 0.2]),
       64: dict(n0=200000, nd=50000, refs=[0.05])}
extra = [(0.1, 1.65, 128, dict(n0=60000, nd=20000, refs=[]))]
meta = json.load(open('runs/meta.json')) if os.path.exists('runs/meta.json') else {}
def run(L, a, b, H, n, fn, init, seed):
    if os.path.exists(fn) and os.path.getsize(fn) == 32 * n: return
    subprocess.run(['./phi4', str(L), str(a), str(b), repr(float(H)), '5000', str(n), '1', str(seed), fn, str(init)], check=True)
jobs = [(b, a, L, CFG[L]) for (b, a, t, mg) in POINTS for L in (32, 64)] + extra
mg_of = {(b, a): mg for (b, a, t, mg) in POINTS}
for k, (b, a, L, c) in enumerate(jobs):
    key = f'b{b}_a{a}_L{L}'; mg = mg_of[(b, a)]
    f0 = f'runs/{key}_H0.bin'; run(L, a, b, 0.0, c['n0'], f0, mg, 1000 + k)
    A = load(f0)[:, 0]; Mabs = float(L * L * np.mean(np.abs(A)))
    Hs = [s / Mabs for s in (1.0, 10.0)] + c['refs']
    meta[key] = dict(b=b, a=a, L=L, Mabs=Mabs, H0=f0, direct={})
    for j, H in enumerate(Hs):
        fn = f'runs/{key}_H{H:.6g}.bin'; run(L, a, b, H, c['nd'], fn, mg, 5000 + 10 * k + j)
        meta[key]['direct'][repr(H)] = fn
    json.dump(meta, open('runs/meta.json', 'w'), indent=1)
    print('done', key, flush=True)

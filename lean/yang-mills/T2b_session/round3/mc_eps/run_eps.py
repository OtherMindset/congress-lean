"""Production runs for the eps-scaling study. usage: run_eps.py points.json tag
points.json: list of dict(key,b,a,L,n0,nd,mg).  Phase 1: H=0 runs; Phase 2: direct runs at s=H<|M|>_0 in SD.
Fixed seeds -> reproducible. Meta -> runs/meta_<tag>.json (same format as the original run_all.py)."""
import numpy as np, subprocess, os, json, sys, zlib
from multiprocessing import Pool
from ana import load
os.makedirs('runs', exist_ok=True)
SD = tuple(float(x) for x in os.environ.get('SD', '1,3,10').split(','))
pts = json.load(open(sys.argv[1])); tag = sys.argv[2]
def run(t):
    L, a, b, H, n, fn, init, seed = t
    if os.path.exists(fn) and os.path.getsize(fn) == 32 * n: return fn
    subprocess.run(['./phi4', str(L), repr(a), repr(b), repr(float(H)), '5000', str(n), '1', str(seed), fn, str(init)], check=True, stderr=subprocess.DEVNULL)
    return fn
def seed(*x): return zlib.crc32(repr(x).encode()) % 2**31
if __name__ == '__main__':
    pts = sorted(pts, key=lambda p: -p['L'])
    t1 = [(p['L'], p['a'], p['b'], 0.0, p['n0'], f"runs/{p['key']}_H0.bin", p['mg'], seed(p['key'], 0)) for p in pts]
    with Pool(2) as pool: list(pool.imap_unordered(run, t1)); print('phase1 done', flush=True)
    meta = {}; t2 = []
    for p in pts:
        A = load(f"runs/{p['key']}_H0.bin")[:, 0]; Mabs = float(p['L'] ** 2 * np.mean(np.abs(A)))
        meta[p['key']] = dict(b=p['b'], a=p['a'], L=p['L'], Mabs=Mabs, H0=f"runs/{p['key']}_H0.bin", direct={}, n0=p['n0'], nd=p['nd'])
        for s in SD:
            H = s / Mabs; fn = f"runs/{p['key']}_s{s:g}.bin"
            meta[p['key']]['direct'][repr(H)] = fn
            t2.append((p['L'], p['a'], p['b'], H, p['nd'], fn, p['mg'], seed(p['key'], s)))
    json.dump(meta, open(f'runs/meta_{tag}.json', 'w'), indent=1)
    with Pool(2) as pool: list(pool.imap_unordered(run, sorted(t2, key=lambda t: -t[0]))); print('phase2 done', flush=True)

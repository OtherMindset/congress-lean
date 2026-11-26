"""Binder-cumulant scan to locate a_c(b): U = 1 - <M^4>/(3<M^2>^2) on L = 8, 16, 32."""
import numpy as np, subprocess, sys, json, os
from ana import load
b = float(sys.argv[1]); avals = [float(x) for x in sys.argv[2].split(',')]
Ls = [int(x) for x in (sys.argv[3] if len(sys.argv) > 3 else '8,16,32').split(',')]
nmeas = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
res = {}
os.makedirs('binder', exist_ok=True)
for a in avals:
    for L in Ls:
        fn = f'binder/b{b}_a{a}_L{L}.bin'
        init = np.sqrt(max(2 - a, 0.01) / (2 * b))
        subprocess.run(['./phi4', str(L), str(a), str(b), '0', '2000', str(nmeas), '1', str(L * 1000 + int(a * 1e4)), fn, str(init)], check=True, stderr=subprocess.DEVNULL)
        A = load(fn)[:, 0]; N = L * L
        m2 = np.mean(A**2); m4 = np.mean(A**4)
        U = 1 - m4 / (3 * m2**2)
        # jackknife over 20 blocks
        blk = np.array_split(np.arange(len(A)), 20)
        Us = []
        for j in range(20):
            k = np.ones(len(A), bool); k[blk[j]] = False
            Us.append(1 - np.mean(A[k]**4) / (3 * np.mean(A[k]**2)**2))
        eU = np.sqrt(19 * np.var(Us))
        res[f'{a},{L}'] = dict(U=U, eU=eU, chi=N * m2, absm=np.mean(np.abs(A)))
        print(f'b={b} a={a} L={L} U={U:.4f}+-{eU:.4f} chi={N*m2:.2f} <|A|>={np.mean(np.abs(A)):.4f}', flush=True)
json.dump(res, open(f'binder/scan_b{b}_{avals[0]}_{avals[-1]}.json', 'w'), indent=1)

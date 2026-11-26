"""Binder scan, parallel (2 procs). usage: binder2.py b a1,a2,.. L1,L2,.. nmeas tag
U = 1 - <A^4>/(3<A^2>^2), jackknife over 20 blocks. Also records tau_int(A^2) to flag correlation."""
import numpy as np, subprocess, sys, json, os
from multiprocessing import Pool
from ana import load, tau_int
b = float(sys.argv[1]); avals = [float(x) for x in sys.argv[2].split(',')]
Ls = [int(x) for x in sys.argv[3].split(',')]; nmeas = int(sys.argv[4]); tag = sys.argv[5]
os.makedirs('binder', exist_ok=True)
def job(args):
    a, L = args
    fn = f'binder/b{b}_a{a}_L{L}.bin'
    init = np.sqrt(max(2 - a, 0.01) / (2 * b))
    if not (os.path.exists(fn) and os.path.getsize(fn) == 32 * nmeas):
        subprocess.run(['./phi4', str(L), str(a), str(b), '0', '3000', str(nmeas), '1', str(L * 1000 + int(round(a * 1e5)) % 99991), fn, str(init)], check=True, stderr=subprocess.DEVNULL)
    A = load(fn)[:, 0]; N = L * L
    m2 = np.mean(A**2); m4 = np.mean(A**4); U = 1 - m4 / (3 * m2**2)
    blk = np.array_split(np.arange(len(A)), 20); Us = []
    for j in range(20):
        k = np.ones(len(A), bool); k[blk[j]] = False
        Us.append(1 - np.mean(A[k]**4) / (3 * np.mean(A[k]**2)**2))
    eU = np.sqrt(19 * np.var(Us))
    return dict(a=a, L=L, U=U, eU=eU, chi=N * m2, absm=float(np.mean(np.abs(A))), tauA2=tau_int(A**2))
if __name__ == '__main__':
    jobs = [(a, L) for a in avals for L in Ls]
    with Pool(2) as p: res = p.map(job, jobs)
    for r in res: print(f"b={b} a={r['a']} L={r['L']} U={r['U']:.4f}+-{r['eU']:.4f} chi={r['chi']:.2f} |A|={r['absm']:.4f} tau(A2)={r['tauA2']:.1f}", flush=True)
    json.dump(res, open(f'binder/scan_{tag}.json', 'w'), indent=1)

"""Analysis helpers: load runs, jackknife, observables R, dR/dH, Q, reweighting in H."""
import numpy as np

def load(fn, withF=False):
    d = np.fromfile(fn, dtype=np.float64).reshape(-1, 4)
    return d if withF else d[:, :3]

def obs_from_moments(N, w, A, B, C):
    """Weighted moments -> (m, chi, R, dRdH, Q_mu, EOMresid-free parts).
    d<O>/dH = <O;M> = N Cov(O,A)."""
    w = w / w.sum()
    m = w @ A; Bm = w @ B; Cm = w @ C
    dA = A - m
    cAA = w @ (dA * dA); cBA = w @ ((B - Bm) * dA); cCA = w @ ((C - Cm) * dA)
    chi = N * cAA                      # dm/dH
    R = (Cm - m * Bm) / m
    dB = N * cBA; dC = N * cCA         # dB/dH, dC/dH (= -d m/da as well for dB)
    dRdH = (dC - chi * Bm - m * dB) / m - R * chi / m
    D = dB                             # -dm/da = N Cov(A,B) = d<phi^2>/dH
    return dict(m=m, B=Bm, C=Cm, chi=chi, R=R, dRdH=dRdH, D=D)

def jack(fun, nblk, n):
    """fun(mask)->dict over samples kept; returns mean dict, err dict"""
    idx = np.arange(n) * nblk // n
    full = fun(np.ones(n, bool))
    reps = [fun(idx != j) for j in range(nblk)]
    out = {}
    for k in full:
        r = np.array([x[k] for x in reps])
        err = np.sqrt((nblk - 1) * np.mean((r - r.mean(axis=0)) ** 2, axis=0))
        out[k] = (full[k], err)
    return out

def reweight_sym(dat, N, H, nblk=50):
    """Reweight an H=0 run to field H using Z2 symmetrisation (phi -> -phi)."""
    A, B, C = dat.T
    M = N * A
    AA = np.concatenate([A, -A]); BB = np.concatenate([B, B]); CC = np.concatenate([C, -C])
    MM = N * AA
    n = len(A)
    def f(mask):
        mk = np.concatenate([mask, mask])
        x = H * MM[mk]; w = np.exp(x - x.max())
        return obs_from_moments(N, w, AA[mk], BB[mk], CC[mk])
    return jack(f, nblk, n)

def direct(dat, N, nblk=50):
    A, B, C = dat.T
    n = len(A)
    def f(mask):
        return obs_from_moments(N, np.ones(mask.sum()), A[mask], B[mask], C[mask])
    return jack(f, nblk, n)

def wham(runs, N, Htarget, nblk=20, iters=2000):
    """Multihistogram in H. runs: list of (H_k, dat_k). H=0 runs are symmetrised.
    Jackknife: block j removed from every run simultaneously."""
    prep = []
    # Z2 symmetrisation: a run at H_k mirrored (phi -> -phi) is a run at -H_k. This makes the
    # estimate exactly even/odd in H (as the truth is) and removes O(1) noise in dR/dH at H -> 0.
    runs = list(runs) + [(-Hk, d * np.array([-1.0, 1.0, -1.0])) for Hk, d in runs if Hk != 0.0]
    for Hk, d in runs:
        A, B, C = d.T
        blk = np.arange(len(A)) * nblk // len(A)
        if Hk == 0.0:
            A = np.concatenate([A, -A]); B = np.concatenate([B, B]); C = np.concatenate([C, -C]); blk = np.concatenate([blk, blk])
        prep.append((Hk, A, B, C, blk))
    Hs = np.array([p[0] for p in prep])
    f0 = [np.zeros(len(Hs))]
    def solve(mask_blk):
        As, Bs, Cs, ns = [], [], [], []
        for Hk, A, B, C, blk in prep:
            k = blk != mask_blk
            As.append(A[k]); Bs.append(B[k]); Cs.append(C[k]); ns.append(k.sum())
        A = np.concatenate(As); B = np.concatenate(Bs); C = np.concatenate(Cs); ns = np.array(ns, float)
        M = N * A
        E = np.outer(M, Hs)               # (S, K)
        f = f0[0].copy()
        for it in range(iters):
            lden = np.logaddexp.reduce(E + np.log(ns) - f, axis=1)   # log sum_k n_k e^{H_k M - f_k}
            fn = np.logaddexp.reduce(E - lden[:, None], axis=0)
            fn -= fn[0]
            if np.max(np.abs(fn - f)) < 1e-10:
                f = fn; break
            f = fn
        f0[0] = f
        lden = np.logaddexp.reduce(E + np.log(ns) - f, axis=1)
        res = {}
        for H in Htarget:
            lw = H * M - lden; w = np.exp(lw - lw.max())
            o = obs_from_moments(N, w, A, B, C)
            for kk, v in o.items(): res.setdefault(kk, []).append(v)
        return {k: np.array(v) for k, v in res.items()}
    full = solve(-1)
    reps = [solve(j) for j in range(nblk)]
    out = {}
    for k in full:
        r = np.array([x[k] for x in reps])
        err = np.sqrt((nblk - 1) * np.mean((r - r.mean(axis=0)) ** 2, axis=0))
        out[k] = (full[k], err)
    return out

def tau_int(x, wmax=2000):
    x = x - x.mean(); n = len(x); v = x @ x / n
    if v == 0: return 0.5
    f = np.fft.rfft(np.concatenate([x, np.zeros(n)]))
    ac = np.fft.irfft(f * np.conj(f))[:n] / (v * np.arange(n, 0, -1))
    t = 0.5
    for W in range(1, min(wmax, n // 2)):
        t += ac[W]
        if W >= 6 * t: break
    return t

"""Reduced single-site scan (b=1): alpha = a/sqrt(b), eta = H b^{-1/4}; r = R'/P', Q = 8(1+r).
float128 trapezoid; where predicted cancellation error > 1e-9 relative, recompute with mpmath
(tanh-sinh, dps chosen from the cancellation factor) and cross-check at a second dps."""
import numpy as np, json, time
from single_site import cumulants_ld, derived, cumulants_mp
import mpmath as mp

def r_point(al, e):
    k1, k2, k3, k4 = cumulants_ld(al, e)
    R, Rp, Pp, r = derived(k1, k2, k3, k4)
    terms = max(abs((k4+3*k2**2)/k1), abs(k2*k3/k1**2), abs(2*k3), abs(k2**2/k1))
    canc = float(terms/abs(Rp)) if Rp != 0 else 1e300
    if abs(r) > 1: canc = max(canc, 1e12)  # suspicious, recheck
    # additional cancellation in centred moments for bimodal case is benign; trust factor
    if canc*1e-18 < 1e-9:
        return float(r), 'ld', canc
    d = int(30 + np.log10(min(canc, 1e200)))
    x1 = derived(*cumulants_mp(al, e, d))[3]
    x2 = derived(*cumulants_mp(al, e, d + 15))[3]
    rel = abs(x1 - x2)/abs(x2)
    if rel > 1e-8:
        print("WARN mp disagreement", al, e, x1, x2)
    return float(x2), 'mp', canc

if __name__ == "__main__":
    ks = np.linspace(-3, 5, 41)
    alphas = np.concatenate([-10**ks[::-1], [0.0], 10**ks])
    etas = 10**np.linspace(-5, 5, 51)
    t = time.time()
    r = np.zeros((len(alphas), len(etas))); src = np.zeros_like(r)
    for i, al in enumerate(alphas):
        for j, e in enumerate(etas):
            r[i, j], s, _ = r_point(al, e)
            src[i, j] = (s == 'mp')
    print("time", time.time() - t, "mp points", int(src.sum()))
    np.savez("scan_single.npz", alphas=alphas, etas=etas, r=r, src=src)
    print("max r =", r.max(), " #r>0:", (r > 0).sum(), " min r", r.min())
    idx = np.argsort(r.ravel())[::-1][:10]
    for k in idx:
        i, j = np.unravel_index(k, r.shape)
        print("  top: alpha=%.4g eta=%.4g r=%.6e" % (alphas[i], etas[j], r[i, j]))
    for i in range(0, len(alphas), 5):
        print("alpha=%.3g  max_eta r=%.3e (eta=%.3g)  min r=%.3e (eta=%.3g)" % (alphas[i], r[i].max(), etas[r[i].argmax()], r[i].min(), etas[r[i].argmin()]))

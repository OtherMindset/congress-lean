"""LY1: even Lee-Yang measures nu on R; is R(H) = <x;x^2>/<x> nonincreasing for H>0?
R = k3/k1 + 2 k2,  R' = k4/k1 - k2 k3/k1^2 + 2 k3, with k_n = d^n log Z/dH^n.
(a) Laguerre-Polya: Z = exp(beta H^2) prod_k (1 + H^2/alpha_k^2); cumulants in closed form
    (mpmath, 40 digits). Positivity of nu checked: density = prod(1 + d^2/alpha^2) N(0, 2beta),
    evaluated with Hermite polynomials on a grid.
(b) Curie-Weiss block: nu_N(M) ∝ binom(N,(N+M)/2) exp(beta M^2/(2N)) [+ optional -g M^4/N^3 is
    NOT LY so not used]; exact sums in mpmath.
"""
import numpy as np, mpmath as mp, sys, json, time
from numpy.polynomial.hermite_e import hermeval

def cum_LP(beta, alphas, H):
    # d^n/dH^n of beta H^2 + sum log(1+H^2/a^2) = beta H^2 + sum [log(H+ia)+log(H-ia)] - const
    k = [mp.mpf(0)]*5
    k[1] = 2*beta*H; k[2] = 2*beta
    for a in alphas:
        for z in (mp.mpc(0, a), mp.mpc(0, -a)):
            w = H - z
            k[1] += mp.re(1/w); k[2] += mp.re(-1/w**2); k[3] += mp.re(2/w**3); k[4] += mp.re(-6/w**4)
    return k[1], k[2], k[3], k[4]

def Rp_from(k1, k2, k3, k4):
    return k4/k1 - k2*k3/k1**2 + 2*k3, k3/k1 + 2*k2, k3 + 2*k1*k2

def positive_LP(beta, alphas):
    # Laplace transform multiplication by H^2 <-> f''. P(s) = prod(1 + s/a^2) in s = H^2
    p = np.array([1.0])
    for a in alphas:
        p = np.convolve(p, [1.0, 1.0/a**2])     # coefficients in increasing powers of s
    sig = np.sqrt(2*beta)
    x = np.linspace(-12, 12, 4001)              # in units of sigma
    # phi^{(2j)}(x) = phi(x) He_{2j}(x/sig) / sig^{2j}
    c = np.zeros(2*len(p) - 1)
    for j, pj in enumerate(p):
        c[2*j] = pj/sig**(2*j)
    vals = hermeval(x, c)                       # times phi(x) > 0
    return vals.min() >= -1e-12*np.abs(vals).max(), vals.min()/np.abs(vals).max()

def scan_LP(ntrial, seed, require_pos):
    rng = np.random.default_rng(seed)
    mp.mp.dps = 40
    worst = (-1e9, None); npos = 0; ncase = 0; nmeas = 0
    for tr in range(ntrial):
        K = int(rng.integers(1, 7))
        beta = 10**rng.uniform(-2, 1)
        alphas = list(10**rng.uniform(-1, 1.5, size=K))
        ok, mn = positive_LP(beta, alphas)
        if require_pos and not ok: continue
        nmeas += ok
        for H in 10**np.linspace(-3, 2, 26):
            k = cum_LP(mp.mpf(beta), [mp.mpf(a) for a in alphas], mp.mpf(H))
            Rp, R, Pp = Rp_from(*k)
            ncase += 1
            val = float(Rp/abs(Pp))
            if Rp > 0: npos += 1
            if val > worst[0]: worst = (val, dict(beta=beta, alphas=alphas, H=float(H), Rp=float(Rp), positive=bool(ok), minrel=float(mn)))
    return worst, npos, ncase, nmeas

def cw(N, beta, H, dps=50):
    mp.mp.dps = dps
    lg = [mp.log(mp.binomial(N, j)) + beta*mp.mpf(2*j - N)**2/(2*N) for j in range(N + 1)]
    mx = max(lg)
    acc = [mp.mpf(0)]*5
    m0 = None
    # centred moments for accuracy
    ws = [mp.exp(l - mx + H*(2*j - N)) for j, l in enumerate(lg)]
    Z = mp.fsum(ws)
    m = mp.fsum(w*(2*j - N) for j, w in enumerate(ws))/Z
    c = [mp.fsum(w*(2*j - N - m)**p for j, w in enumerate(ws))/Z for p in range(5)]
    k1, k2, k3, k4 = m, c[2], c[3], c[4] - 3*c[2]**2
    return Rp_from(k1, k2, k3, k4)

if __name__ == "__main__":
    t0 = time.time()
    for req in (True, False):
        w, npos, nc, nm = scan_LP(3000, 1, req)
        print("LP require_positive=%s: cases %d  R'>0 cases %d  worst R'/P' %.4e" % (req, nc, npos, w[0]))
        print("   worst:", w[1])
    print("time", time.time() - t0)
    res = []
    for N in (2, 3, 4, 8, 16, 64, 256, 1024):
        for beta in (0.2, 0.6, 0.9, 1.0, 1.1, 1.5, 3.0):
            worst = -1e9
            for H in 10**np.linspace(-3, 1, 17):
                Hs = mp.mpf(H)/(np.sqrt(N))  # field per spin scaled
                Rp, R, Pp = cw(N, beta, Hs, dps=60 if N < 300 else 40)
                worst = max(worst, float(Rp/abs(Pp)))
            res.append((N, beta, worst))
            print("CW N=%d beta=%.2f  max_H R'/P' = %.4e" % (N, beta, worst), flush=True)
    json.dump(res, open("ly1_cw.json", "w"))
    print("time", time.time() - t0)

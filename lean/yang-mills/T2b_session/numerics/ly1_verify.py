"""Find LP measures with comfortably positive density and R'>0; verify by direct quadrature of the density."""
import numpy as np, mpmath as mp, json
from ly1 import cum_LP, Rp_from, positive_LP
from numpy.polynomial.hermite_e import hermeval
mp.mp.dps = 40
rng = np.random.default_rng(5)
found = []
for tr in range(20000):
    K = int(rng.integers(1, 4)); beta = 10**rng.uniform(-1, 1); al = list(10**rng.uniform(-1, 1, size=K))
    ok, mn = positive_LP(beta, al)
    if not ok: continue
    # positivity margin: min over x of density / max density
    for H in 10**np.linspace(-2, 1.5, 15):
        Rp, R, Pp = Rp_from(*cum_LP(mp.mpf(beta), [mp.mpf(a) for a in al], mp.mpf(H)))
        if Rp > 0: found.append((float(Rp/Pp), mn, beta, al, float(H)))
print("positive-density LP cases with R'>0:", len(found))
found.sort(key=lambda f: -f[0])
for f in found[:3]: print(f)
# simplest: K=1 example?
k1 = [f for f in found if len(f[3]) == 1]
print("K=1 examples:", len(k1), k1[:3])
def direct(beta, al, H, dps=40):
    """quadrature of nu(dx) = sum_j p_j phi^{(2j)}(x) dx with weights e^{Hx}"""
    mp.mp.dps = dps
    p = [mp.mpf(1)]
    for a in al:
        a2 = mp.mpf(a)**2; q = [mp.mpf(0)]*(len(p)+1)
        for i, c in enumerate(p): q[i] += c; q[i+1] += c/a2
        p = q
    sig = mp.sqrt(2*mp.mpf(beta))
    def dens(x):
        u = x/sig
        return mp.exp(-u*u/2)*sum(p[j]*mp.hermite(2*j, u/mp.sqrt(2))*mp.mpf(2)**(-j)/sig**(2*j) for j in range(len(p)))
    # probabilists He_n(u) = 2^{-n/2} H_n(u/sqrt2)
    Hm = mp.mpf(H)
    mom = [mp.quad(lambda x: x**k*dens(x)*mp.exp(Hm*x), [-mp.inf, -sig, 0, sig, mp.inf]) for k in range(4)]
    m = mom[1]/mom[0]; P = mom[2]/mom[0]; M3 = mom[3]/mom[0]
    return (M3 - m*P)/m, mp.findroot(lambda x: 0, 0) if False else None
def Rdirect(beta, al, H):
    return direct(beta, al, H)[0]
f = (k1 or found)[0]
beta, al, H = f[2], f[3], f[4]
print("verify beta=%g alphas=%s" % (beta, al))
for h in [H/4, H/2, H, 2*H, 4*H]:
    k = cum_LP(mp.mpf(beta), [mp.mpf(a) for a in al], mp.mpf(h))
    Rp, R, Pp = Rp_from(*k)
    print(" H=%.4g  R(cumulant)=%s  R(direct quad)=%s  R'=%s" % (h, mp.nstr(R, 15), mp.nstr(Rdirect(beta, al, h), 15), mp.nstr(Rp, 8)))
json.dump(found[:50], open("ly1_counterexamples.json", "w"))

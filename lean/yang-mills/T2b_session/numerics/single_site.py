"""Single-site test of R(H) = <phi;phi^2>/<phi> monotonicity.

Weight e^{-a phi^2 - b phi^4 + H phi}.  Scaling phi = b^{-1/4} psi reduces to b=1 with
alpha = a/sqrt(b), eta = H b^{-1/4}.  The ratio r = R'/P' (P = <phi^2>) is scale invariant.
Q = 8(1 + r)   (Q = ABF ratio (m - H chi)/(1/2 b m^2 dP/dH); lemma K=0 <=> r <= 0 <=> Q <= 8).

Cumulants k_n = d^n/dH^n log Z:
  R  = k3/k1 + 2 k2
  R' = k4/k1 - k2 k3/k1^2 + 2 k3
  P' = k3 + 2 k1 k2
Quadrature: trapezoid (spectrally accurate for smooth rapidly decaying integrands) in
float128 on the region V - Vmin < 760, spacing <= sigma_local/10.  Verified against mpmath.
"""
import numpy as np, mpmath as mp, sys, json

LD = np.longdouble

def V(x, al, eta):
    return al*x*x + x**4 - eta*x

def region(al, eta, cut=760.0):
    # local minima of V
    rts = np.roots([4.0, 0.0, 2.0*al, -eta])
    rts = np.real(rts[np.abs(np.imag(rts)) < 1e-9*(1+np.abs(rts))])
    mins = [r for r in rts if 12*r*r + 2*al > 0]
    Vmin = min(V(r, al, eta) for r in mins)
    # roots of V - Vmin - cut
    q = np.roots([1.0, 0.0, al, -eta, -Vmin - cut])
    q = np.sort(np.real(q[np.abs(np.imag(q)) < 1e-7*(1+np.abs(q))]))
    ints = [(q[i], q[i+1]) for i in range(0, len(q)-1, 2)]
    return ints, Vmin

def cumulants_ld(al, eta, ppw=10.0, cut=760.0):
    ints, Vmin = region(al, eta, cut)
    xs = []
    for lo, hi in ints:
        Vpp = max(abs(2*al + 12*lo*lo), abs(2*al + 12*hi*hi), 1e-300)
        # local scale: sigma ~ 1/sqrt(V'') but at least quartic scale
        sig = min(1/np.sqrt(Vpp), 1.0)
        n = int(np.ceil((hi - lo)/sig*ppw)) + 1
        n = max(n, 400)
        xs.append(np.linspace(LD(lo), LD(hi), n))
    out = None
    # integrate each interval with its own spacing (weights dx)
    S = np.zeros(6, dtype=LD)
    for x in xs:
        dx = x[1] - x[0]
        w = np.exp(-(LD(al)*x*x + x**4 - LD(eta)*x - LD(Vmin)))*dx
        S += np.array([np.sum(w*x**k) for k in range(6)])
    m = S[1]/S[0]
    # centered moments (second pass)
    C = np.zeros(5, dtype=LD)
    for x in xs:
        dx = x[1] - x[0]
        w = np.exp(-(LD(al)*x*x + x**4 - LD(eta)*x - LD(Vmin)))*dx
        y = x - m
        C += np.array([np.sum(w*y**k) for k in range(5)])
    C = C/C[0]
    k1 = m; k2 = C[2]; k3 = C[3]; k4 = C[4] - 3*C[2]**2
    return k1, k2, k3, k4

def derived(k1, k2, k3, k4):
    R = k3/k1 + 2*k2
    Rp = k4/k1 - k2*k3/k1**2 + 2*k3
    Pp = k3 + 2*k1*k2
    return R, Rp, Pp, Rp/Pp

def cumulants_mp(al, eta, dps=60):
    mp.mp.dps = dps
    al = mp.mpf(al); eta = mp.mpf(eta)
    ints, Vmin = region(float(al), float(eta))
    f = lambda x, k: x**k*mp.exp(-(al*x*x + x**4 - eta*x) + Vmin)
    # breakpoints: interval ends and minima
    rts = np.roots([4.0, 0.0, 2.0*float(al), -float(eta)])
    rts = sorted(np.real(rts[np.abs(np.imag(rts)) < 1e-9]))
    pts = sorted(set([mp.mpf(lo) for lo, hi in ints] + [mp.mpf(hi) for lo, hi in ints] + [mp.mpf(r) for r in rts]))
    pts = [p for p in pts if pts[0] <= p <= pts[-1]]
    def I(k, c=0):
        return mp.quad(lambda x: (x-c)**k*mp.exp(-(al*x*x + x**4 - eta*x) + Vmin), [-mp.inf] + pts + [mp.inf])
    Z = I(0); m = I(1)/Z
    c2 = I(2, m)/Z; c3 = I(3, m)/Z; c4 = I(4, m)/Z
    return m, c2, c3, c4 - 3*c2**2

if __name__ == "__main__":
    # quick self test
    for al, eta in [(0, 1), (-50, 0.01), (5, 0.3), (-1000, 1e-3), (100, 10)]:
        a = derived(*cumulants_ld(al, eta)); b = derived(*cumulants_mp(al, eta))
        print(al, eta, [float(x) for x in a], [mp.nstr(x, 20) for x in b])

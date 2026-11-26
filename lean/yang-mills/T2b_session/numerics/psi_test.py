"""Psi-monotonicity test (zero field), phi^4 rings of length L (L=1: single site with a-J... see note),
2x2 torus = 4-ring with coupling 2J.

Psi(v) ∝ N(v) / (v D(v)),  with S = M + M' (two iid copies at H=0), v = value of S,
  D(v) = density of S at v,
  N(v) = E_0[ sum_x (phi_x+phi'_x)(phi_x-phi'_x)^2 ; S = v ]  (density-weighted)
(Psi(u) of the lead = E[sum q t^2 | sum q = u]/u with u = v/sqrt2 and sum q t^2 = (2 sqrt2)^{-1} sum (phi+phi')(phi-phi')^2:
 positive constant factors only.)
Expansion: (p+p')(p-p')^2 = p^3 - p^2 p' - p p'^2 + p'^3, so with F_j(z) = E[phi_0^j e^{zM}]:
  N^(z) = 2L [F3 F0 - F2 F1](z),  D^(z) = F0(z)^2.
Exponential tilting: for each real h, z = h + ik; evaluate at v = E_h[S] = 2 F1... (mean of S under tilt),
  D(v) = e^{-hv} (2pi)^-1 ∫ D^(h+ik) e^{-ikv} dk,  N(v) likewise; the factor e^{-hv} cancels in N/D.
k-integral: trapezoid on [-K, K], K where |F0(h+ik)/F0(h)|^2 < 1e-18; convergence checked by halving dk.
F_j(z) = Tr(X_j T(z)^L)/Z0 with complex-field transfer matrix on a trapezoid phi-grid.
"""
import numpy as np, sys, json, time

def grid_setup(a, b, J, n, Lrange):
    x = np.linspace(-Lrange, Lrange, n); dx = x[1] - x[0]
    lw = -a*x**2 - b*x**4 + np.log(dx)
    K = J*np.outer(x, x)          # log-kernel
    return x, lw, K

def Fj(x, lw, K, L, z):
    """returns F0..F3 (unnormalised, common scale) for complex field z on ring length L"""
    d = np.exp(0.5*(lw + z*x) - 0.5*lw.max())
    T = d[:, None]*K*d[None, :]
    # T^L by eigendecomposition (complex symmetric, use general eig)
    lam, V = np.linalg.eig(T)
    Vi = np.linalg.inv(V)
    s = np.abs(lam).max()
    lp = (lam/s)**L
    # Tr(X T^L) = sum_n lp_n (Vi X V)_nn
    out = []
    for j in range(4):
        out.append(np.sum(lp*np.einsum('ni,i,in->n', Vi, x**j, V)))
    return np.array(out), s

def Fj_pow(x, lw, K, L, z):
    d = np.exp(0.5*(lw + z*x) - 0.5*lw.max())
    T = d[:, None]*K*d[None, :]
    s = np.abs(T).max(); T = T/s
    P = np.eye(len(x), dtype=complex); B = T.astype(complex); e = L; logs = 0.0
    while e:
        if e & 1:
            P = P @ B; c = np.abs(P).max(); P /= c; logs += np.log(c)
        e >>= 1
        if e:
            B = B @ B; c = np.abs(B).max(); B /= c
            logs += 0  # B rescale tracked below
    # rescaling of B breaks exact scale; use only ratios at fixed L,h -> recompute without B rescale
    return P, logs

def Fvals(x, lw, K, L, z):
    e = 0.5*(lw + z*x)
    Mr = e.real[:, None] + e.real[None, :] + K
    sh = Mr.max()
    T = np.exp(e[:, None] + e[None, :] + K - sh)
    # repeated multiplication with exact log-scale bookkeeping
    P = np.eye(len(x), dtype=complex); logs = 0.0
    for _ in range(L):
        P = P @ T; c = np.abs(P).max(); P /= c; logs += np.log(c)
    logs += L*sh
    dg = np.diag(P)
    return np.array([np.sum(dg*x**j) for j in range(4)]), logs

def choose_range(a, b, Jsite, hmax, cut=40.0):
    # Jsite = total coupling felt per site in a uniform configuration (ring: J; 2x2 torus: 2J)
    xs = np.linspace(-200, 200, 400001)
    lwt = -(a - Jsite)*xs**2 - b*xs**4 + hmax*np.abs(xs)
    return max(np.abs(xs[lwt > lwt.max() - cut]).max(), 3.0)

def psi_point(x, lw, K, L, h, nk=801):
    F, l0 = Fvals(x, lw, K, L, h)
    F = F.real
    m = F[1]/F[0]; v = 2*L*m      # mean of S = M + M' under tilt h (translation invariance)
    # characteristic decay scale: var of S
    # find K: increase until |F0(h+ik)/F0(h)|^2 small
    kmax = 0.5
    while True:
        Fk, lk = Fvals(x, lw, K, L, h + 1j*kmax)
        r = np.abs(Fk[0])*np.exp(lk - l0)/F[0]
        if r**2 < 1e-18 or kmax > 200: break
        kmax *= 1.5
    def integ(nk):
        ks = np.linspace(-kmax, kmax, nk); dk = ks[1] - ks[0]
        Dint = 0; Nint = 0
        for k in ks:
            Fk, lk = Fvals(x, lw, K, L, h + 1j*k)
            Fk = Fk*np.exp(lk - l0)/F[0]
            ph = np.exp(-1j*k*v)
            Dint += (Fk[0]**2*ph).real*dk
            Nint += (2*L*(Fk[3]*Fk[0] - Fk[2]*Fk[1])*ph).real*dk
        return Nint, Dint
    N1, D1 = integ(nk); N2, D2 = integ(2*nk - 1)
    psi1 = N1/(v*D1); psi2 = N2/(v*D2)
    return v, psi2, abs(psi2 - psi1), kmax

if __name__ == "__main__":
    a = float(sys.argv[1]); J = float(sys.argv[2]); L = int(sys.argv[3])
    n = int(sys.argv[4]) if len(sys.argv) > 4 else 121
    hs = [float(s) for s in sys.argv[5].split(',')] if len(sys.argv) > 5 else list(10**np.linspace(-2, 0.7, 14))
    # range
    b = float(sys.argv[6]) if len(sys.argv) > 6 else 1.0
    Lr = choose_range(a, b, J, max(hs))
    x, lw, K = grid_setup(a, b, J, n, Lr)
    res = []
    t0 = time.time()
    for h in hs:
        v, psi, err, km = psi_point(x, lw, K, L, h)
        res.append((v, psi, err))
        print("h=%.4g v=%.5g Psi=%.10g err=%.2e kmax=%.3g" % (h, v, psi, err, km), flush=True)
    d = np.diff([r[1] for r in res])
    errs = [r[2] for r in res]
    print("a=%g J=%g L=%d: max increment of Psi along v: %.3e (max err %.1e)  time %.0f" % (a, J, L, d.max(), max(errs), time.time()-t0))
    json.dump(dict(a=a, J=J, L=L, res=res), open("psi_a%g_J%g_L%d.json" % (a, J, L), "w"))

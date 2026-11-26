"""Tests of the POINTWISE (site-resolved) form of the target lemma:
   P(z):  m0 * <phi0 ; phi0^2 ; phi_z>  <=  <phi0 ; phi0^2> * <phi0 ; phi_z>
(joint cumulants), i.e. R = <phi0;phi0^2>/<phi0> is nonincreasing in EACH site field h_z.
Summing P(z) over z (weights eps^2) gives the target lemma with K = 0, with no eps-dependence.
Also tests the 0-d inequality  k1 k4 - k2 k3 + 2 k1^2 k3 <= 0  for general GS-class measures.
Exact quadrature on small graphs (2 sites: 2-d grid; 3 sites: 3-d grid)."""
import numpy as np, itertools, sys

def cum3(E, A, B, C):
    return E(A*B*C) - E(A*B)*E(C) - E(A*C)*E(B) - E(B*C)*E(A) + 2*E(A)*E(B)*E(C)

def two_site(a, b, J, h0, h1, n=1201, L=None):
    if L is None:
        L = 6.0 + 3*abs(h0 + h1)**(1/3) / max(b, 1e-3)**(1/6)
    x = np.linspace(-L, L, n)
    X, Y = np.meshgrid(x, x, indexing='ij')
    S = -a*(X**2 + Y**2) - b*(X**4 + Y**4) + J*X*Y + h0*X + h1*Y
    w = np.exp(S - S.max())
    Z = w.sum()
    E = lambda F: (w*F).sum()/Z
    m0 = E(X)
    T = E(X**3) - m0*E(X**2)            # <phi0;phi0^2>
    out = []
    for Fz in (X, Y):
        c3 = cum3(E, X, X**2, Fz)
        c2 = E(X*Fz) - m0*E(Fz)
        out.append((m0*c3 - T*c2, m0*abs(c3) + T*abs(c2)))
    return out

def zero_d_general(weights, pts, h):
    """0-d test for a discrete measure: returns k1 k4 - k2 k3 + 2 k1^2 k3 and a scale."""
    pts = np.asarray(pts, float); w = np.asarray(weights, float)*np.exp(h*pts)
    w /= w.sum()
    mom = [ (w*pts**k).sum() for k in range(5)]
    m1, m2, m3, m4 = mom[1:]
    k1 = m1; k2 = m2 - m1**2; k3 = m3 - 3*m2*m1 + 2*m1**3
    k4 = m4 - 4*m3*m1 - 3*m2**2 + 12*m2*m1**2 - 6*m1**4
    val = k1*k4 - k2*k3 + 2*k1**2*k3
    return val, abs(k1*k4) + abs(k2*k3) + abs(2*k1**2*k3)

if __name__ == '__main__':
    rng = np.random.default_rng(0)
    worst = [-np.inf, -np.inf]
    print("== 2-site phi^4, random (a,b,J,h0,h1) ==")
    for trial in range(400):
        b = 10**rng.uniform(-2, 1)
        a = rng.uniform(-3, 3)
        J = 10**rng.uniform(-1.5, 0.7)
        h0 = 10**rng.uniform(-2, 1) * (rng.random() < 0.8)
        h1 = 10**rng.uniform(-2, 1)
        try:
            res = two_site(a, b, J, h0, h1)
        except FloatingPointError:
            continue
        for k, (v, s) in enumerate(res):
            r = v/s
            if r > worst[k]:
                worst[k] = r
                print(f"z={'0' if k==0 else '1'} new worst rel={r:+.3e}  a={a:.3f} b={b:.3f} J={J:.3f} h0={h0:.3f} h1={h1:.3f}")
    print("worst relative violation (z=0, z=1):", worst)

    print("== 0-d, 3-point measures w*delta0 + delta_{+-1} (GS class iff w<=2) ==")
    for w in [0.1, 0.5, 1.0, 2.0, 3.0, 10.0, 100.0]:
        mx = -np.inf
        for h in np.logspace(-3, 1.5, 300):
            v, s = zero_d_general([1, w, 1], [-1, 0, 1], h)
            mx = max(mx, v/s)
        print(f"w={w:7.2f}  max rel (k1k4-k2k3+2k1^2k3) = {mx:+.3e}")
    print("== 0-d, Ising block of N spins with all-to-all coupling J ==")
    from math import comb
    for N in [2, 3, 4, 6, 10]:
        for J in [0.0, 0.1, 0.5, 1.0, 3.0]:
            pts = np.array([N - 2*k for k in range(N+1)], float)
            wts = np.array([comb(N, k) for k in range(N+1)], float)*np.exp(J*pts**2/2)
            wts /= wts.max()
            mx = max(zero_d_general(wts, pts, h)[0]/zero_d_general(wts, pts, h)[1]
                     for h in np.logspace(-3, 1.5, 300))
            print(f"N={N:2d} J={J:4.1f}  max rel = {mx:+.3e}")

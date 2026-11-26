"""Translation-invariant rings, uniform field: site-resolved D_z (see osp_test.py) for phi^4 (3-ring)
and Ising GS-block rings (exact enumeration). Sum_z D_z <= 0 is the K=0 lemma on the ring."""
import numpy as np, itertools, sys
sys.path.insert(0, '.')
from osp_test import Dz
rng = np.random.default_rng(2)
def phi4_ring3(a, b, J, h, n=181):
    L = min(30, 2.0 + 2.2*(max(abs(a), 1)/max(b, 1e-3))**0.5 + (h/max(b, 1e-3))**(1/3))
    x = np.linspace(-L, L, n); X, Y, W = np.meshgrid(x, x, x, indexing='ij')
    S = -a*(X**2+Y**2+W**2) - b*(X**4+Y**4+W**4) + J*(X*Y+Y*W+W*X) + h*(X+Y+W)
    w = np.exp(S - S.max()); Z = w.sum(); E = lambda F: (w*F).sum()/Z
    return Dz(E, X, X), Dz(E, X, Y)
print("== phi^4 3-ring (z=0, z=1; z=2 equal to z=1) ==")
wo = [-np.inf]*3
for t in range(150):
    b = 10**rng.uniform(-1.5, 1); a = rng.uniform(-2.5, 3); J = 10**rng.uniform(-1, 0.5); h = 10**rng.uniform(-2.5, 0.7)
    if a - J < -0.0 and False: pass
    (v0, s0), (v1, s1) = phi4_ring3(a, b, J, h)
    tot = v0 + 2*v1; stot = s0 + 2*s1
    for k, r in enumerate([v0/s0, v1/s1, tot/stot]):
        if r > wo[k]:
            wo[k] = r; print(['z=0', 'z=1', 'SUM'][k], f"{r:+.3e} a={a:.2f} b={b:.3f} J={J:.2f} h={h:.4f}")
print(wo)
print("== Ising GS-block rings (nblk blocks of n spins, uniform intra Jin / inter Jout all-to-all between neighbours) ==")
wo = [-np.inf]*3
for t in range(200):
    nblk = int(rng.choice([2, 3, 4])); n = int(rng.choice([2, 3])) if nblk < 4 else 2
    Jin = 10**rng.uniform(-1, 0.5); Jout = 10**rng.uniform(-1.5, 0.0); hf = 10**rng.uniform(-2.5, 0.3)
    N = nblk*n
    conf = np.array(list(itertools.product([-1, 1], repeat=N)), float)
    Phi = [conf[:, k*n:(k+1)*n].sum(1) for k in range(nblk)]
    H = sum(Jin*(P**2 - n)/2 for P in Phi) + hf*conf.sum(1)
    for k in range(nblk):
        if nblk == 2 and k == 1: break
        H = H + Jout*Phi[k]*Phi[(k+1) % nblk]
    w = np.exp(H - H.max()); Z = w.sum(); E = lambda F: (w*F).sum()/Z
    res = [Dz(E, Phi[0], Phi[k]) for k in range(nblk)]
    v0, s0 = res[0]; voff = sum(r[0] for r in res[1:]); soff = sum(r[1] for r in res[1:])
    for k, r in enumerate([v0/s0, max(r[0]/r[1] for r in res[1:]), (v0+voff)/(s0+soff)]):
        if r > wo[k]:
            wo[k] = r; print(['onsite', 'offsite(max)', 'SUM'][k], f"{r:+.3e} nblk={nblk} n={n} Jin={Jin:.2f} Jout={Jout:.2f} h={hf:.4f}")
print(wo)

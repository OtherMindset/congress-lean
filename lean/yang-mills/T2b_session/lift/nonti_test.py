"""K=0 lattice target with UNIFORM field on NON-translation-invariant graphs:
   S := m * sum_x kappa(phi0, phi0^2, phi_x) - chi * <phi0;phi0^2>  <= 0 ?
(phi^4 3-site path/triangle with random couplings, site 0 at end or middle; Ising GS blocks on
random weighted graphs). A violation here falsifies GC (F = G) for general graphs."""
import numpy as np, itertools, sys
sys.path.insert(0, '.')
from osp_test import Dz
rng = np.random.default_rng(5)
def S_of(E, P0, Ps):
    v = sum(Dz(E, P0, P)[0] for P in Ps); s = sum(Dz(E, P0, P)[1] for P in Ps); return v, s
wo = -np.inf
print("== phi^4 3 sites, uniform h, random J ==")
for t in range(200):
    b = 10**rng.uniform(-1.5, 1); a = rng.uniform(-2.5, 3); h = 10**rng.uniform(-2.5, 0.7)
    J = 10**rng.uniform(-1, 0.6, 3) * (rng.random(3) < 0.85)
    L = min(30, 2.0 + 2.2*(max(abs(a), 1)/max(b, 1e-3))**0.5 + (h/max(b, 1e-3))**(1/3))
    x = np.linspace(-L, L, 171); X, Y, W = np.meshgrid(x, x, x, indexing='ij')
    Sx = -a*(X**2+Y**2+W**2) - b*(X**4+Y**4+W**4) + J[0]*X*Y + J[1]*Y*W + J[2]*X*W + h*(X+Y+W)
    w = np.exp(Sx - Sx.max()); Z = w.sum(); E = lambda F: (w*F).sum()/Z
    v, s = S_of(E, X, [X, Y, W]); r = v/s
    if r > wo:
        wo = r; print(f"{r:+.3e} a={a:.2f} b={b:.3f} J01,J12,J02={np.round(J,3)} h={h:.4f}")
print("worst", wo)
print("== Ising GS blocks, random weighted graphs, uniform field ==")
wo = -np.inf
for t in range(300):
    nblk = int(rng.choice([2, 3, 4])); n = int(rng.choice([1, 2, 3])) if nblk < 4 else int(rng.choice([1, 2]))
    if nblk*n < 3: n = 2
    N = nblk*n
    conf = np.array(list(itertools.product([-1, 1], repeat=N)), float)
    Jin = 10**rng.uniform(-1, 0.5); Jout = 10**rng.uniform(-1.5, 0.3); hf = 10**rng.uniform(-2.5, 0.3)
    Jm = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            Jm[i, j] = (Jin if i//n == j//n else Jout*(rng.random() < 0.7))*rng.random()
    H = np.einsum('ci,ij,cj->c', conf, Jm, conf) + hf*conf.sum(1)
    w = np.exp(H - H.max()); Z = w.sum(); E = lambda F: (w*F).sum()/Z
    Phi = [conf[:, k*n:(k+1)*n].sum(1) for k in range(nblk)]
    v, s = S_of(E, Phi[0], Phi); r = v/s if s > 1e-13 else -1
    if r > wo:
        wo = r; print(f"{r:+.3e} nblk={nblk} n={n} Jin={Jin:.2f} Jout={Jout:.2f} h={hf:.4f}")
print("worst", wo)

"""Off-site pointwise inequality (OSP):  for z != 0,
   D_z := <phi0> <phi0 ; phi0^2 ; phi_z>  -  <phi0 ; phi0^2> <phi0 ; phi_z>  <= 0 .
(1) phi^4 on 3-site graphs (path 0-1-2 and triangle), random couplings/fields, 3-d quadrature.
(2) Ising GS blocks: blocks B_x of n spins, Phi_x = sum of block spins, arbitrary
    ferromagnetic intra/inter couplings, exact enumeration.
Prints the worst relative value D_z / (|first| + |second|)."""
import numpy as np, itertools

def cum3(E, A, B, C):
    return E(A*B*C) - E(A*B)*E(C) - E(A*C)*E(B) - E(B*C)*E(A) + 2*E(A)*E(B)*E(C)

def Dz(E, P0, Pz):
    m = E(P0)
    T = E(P0**3) - m*E(P0**2)
    c3 = cum3(E, P0, P0**2, Pz)
    c2 = E(P0*Pz) - m*E(Pz)
    first, second = m*c3, T*c2
    return first - second, abs(first) + abs(second)

def three_site(a, b, J01, J12, J02, h, n=161):
    L = 2.0 + 2.0*(max(abs(a), 1) / max(b, 1e-3))**0.5 + (sum(h)/max(b,1e-3))**(1/3)
    L = min(L, 30)
    x = np.linspace(-L, L, n)
    X, Y, W = np.meshgrid(x, x, x, indexing='ij')
    S = (-a*(X**2+Y**2+W**2) - b*(X**4+Y**4+W**4) + J01*X*Y + J12*Y*W + J02*X*W
         + h[0]*X + h[1]*Y + h[2]*W)
    w = np.exp(S - S.max()); Z = w.sum()
    E = lambda F: (w*F).sum()/Z
    return [Dz(E, X, Y), Dz(E, X, W), Dz(E, X, X)]

def ising_blocks(nblk, n, Jin, Jout, hfield, rng):
    """nblk blocks of n spins; intra-block couplings Jin (random >=0), inter-block Jout."""
    N = nblk*n
    conf = np.array(list(itertools.product([-1, 1], repeat=N)), float)
    J = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            same = (i//n) == (j//n)
            J[i, j] = (Jin if same else Jout)*rng.random()
    H = 0.5*np.einsum('ci,ij,cj->c', conf, J+J.T, conf) + conf @ (hfield*rng.random(N))
    w = np.exp(H - H.max()); Z = w.sum()
    E = lambda F: (w*F).sum()/Z
    Phi = [conf[:, k*n:(k+1)*n].sum(1) for k in range(nblk)]
    return [Dz(E, Phi[0], Phi[k]) for k in range(1, nblk)] + [Dz(E, Phi[0], Phi[0])]

if __name__ == '__main__':
    rng = np.random.default_rng(1)
    worst = {}
    print("== phi^4, 3 sites ==")
    for t in range(150):
        b = 10**rng.uniform(-1.5, 1); a = rng.uniform(-2.5, 3)
        J01 = 10**rng.uniform(-1, 0.6); J12 = 10**rng.uniform(-1, 0.6)
        J02 = J01*rng.random() if rng.random() < 0.5 else 0.0   # path or triangle
        h = 10**rng.uniform(-2, 0.7, 3) * (rng.random(3) < 0.8)
        if h.sum() == 0: h[1] = 0.1
        res = three_site(a, b, J01, J12, J02, h)
        for k, name in enumerate(['z=1', 'z=2', 'z=0']):
            v, s = res[k]; r = v/s
            if r > worst.get(name, -np.inf):
                worst[name] = r
                print(f"{name}: worst rel {r:+.3e} a={a:.2f} b={b:.3f} J={J01:.2f},{J12:.2f},{J02:.2f} h={np.round(h,3)}")
    print(worst)
    print("== Ising GS blocks ==")
    worst = {}
    for t in range(300):
        nblk = rng.choice([2, 3]); n = rng.choice([2, 3, 4]) if nblk == 2 else rng.choice([2, 3])
        Jin = 10**rng.uniform(-1, 0.5); Jout = 10**rng.uniform(-1.5, 0.3); hf = 10**rng.uniform(-2, 0.5)
        res = ising_blocks(nblk, n, Jin, Jout, hf, rng)
        for k, (v, s) in enumerate(res):
            name = 'onsite' if k == len(res)-1 else f'off{k+1}'
            r = v/s if s > 1e-14 else 0.0
            if r > worst.get(name, -np.inf):
                worst[name] = r
                print(f"{name}: worst rel {r:+.3e} nblk={nblk} n={n} Jin={Jin:.2f} Jout={Jout:.2f} h={hf:.3f}")
    print(worst)

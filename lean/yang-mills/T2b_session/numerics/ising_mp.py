"""mpmath brute-force IC on W x Lc periodic Ising torus; B = set of (col,row); field c=1 on B, c0 elsewhere."""
import mpmath as mp, itertools, sys
def ic_mp(W, Lc, beta, H, B, c0, dps=50):
    mp.mp.dps = dps; beta = mp.mpf(beta); H = mp.mpf(H); c0 = mp.mpf(c0)
    acc = [mp.mpf(0)]*8
    sites = [(l, w) for l in range(Lc) for w in range(W)]
    bonds = []
    for l in range(Lc):
        for w in range(W):
            bonds.append(((l, w), ((l+1) % Lc, w)))
            if W >= 3 or (W == 2 and w == 0): bonds.append(((l, w), (l, (w+1) % W)))
    cc = {s: (mp.mpf(1) if s in B else c0) for s in sites}
    for conf in itertools.product([-1, 1], repeat=len(sites)):
        s = dict(zip(sites, conf))
        E = beta*sum(s[a]*s[b] for a, b in bonds); Phi = sum(cc[x]*s[x] for x in sites)
        w = mp.exp(E + H*Phi); MB = sum(s[x] for x in B)
        for i, f in enumerate([1, MB, MB**2, MB**3]):
            acc[i] += w*f; acc[4+i] += w*f*Phi
    Z = acc[0]; E_ = [a/Z for a in acc]
    Sx = lambda i: E_[4+i] - E_[i]*E_[4]
    m, P, M3 = E_[1], E_[2], E_[3]
    u = M3 - m*P; up = Sx(3) - m*Sx(2) - P*Sx(1); chi = Sx(1)
    return (up*m - u*chi)/m**2, m, u/m
if __name__ == "__main__":
    W, Lc = 3, 3
    B = [(0, 0), (0, 1), (0, 2)]
    for H in ['0.0001', '0.001', '0.01', '0.03', '0.1']:
        for dps in (30, 60):
            Rp, m, R = ic_mp(W, Lc, 2.0, H, B, 1.0, dps)
        print(H, mp.nstr(Rp, 15), mp.nstr(m, 10), mp.nstr(R, 10))

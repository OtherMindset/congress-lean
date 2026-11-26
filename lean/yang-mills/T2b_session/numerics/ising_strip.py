"""Inequality IC on Ising strips W x L (L = finite periodic or infinite), via super-column
transfer matrices. Super-column = k consecutive columns (Wk spins); B = the k columns of super-column 0
(or a sub-block of it). Couplings: beta on all nn bonds (vertical periodic if W>=3, open if W<=2;
optional anisotropy beta_v). Field H*c_x: c = 1 everywhere ('uniform') or c = 1 on B and c0 elsewhere
(c0 in [0,1], applied to every site outside B in every super-column; B-pattern repeats per
super-column, i.e. a periodic c, translation invariant along the strip).
Quantity: R_B = <M_B;M_B^2>/<M_B>;  dR/dH exact:
  dH <X> = sum_y <X_0 ; Phi_y>, Phi = sum_x c_x sigma_x over a super-column.
  R' = (u' m - u chi)/m^2, u = <M^3> - <M><M^2>, u' = S(M^3) - m S(M^2) - <M^2> S(M), chi = S(M).
Reported: rho_B = R'/|S(M^2)| style normalisation is not natural here (M^2 not monotone), so we report
R' and R'/(R * chi/m) (dimensionless: relative rate d log R / d log m)."""
import numpy as np, itertools, sys, json, time

def supercol(W, k, beta, beta_v, H, Bmask, c0):
    ns = W*k
    S = np.array(list(itertools.product([-1, 1], repeat=ns)), dtype=float)   # (N, ns), index = col*W + row
    S3 = S.reshape(-1, k, W)
    E = np.zeros(len(S))
    # vertical bonds
    if W >= 3:
        E += beta_v*np.sum(S3*np.roll(S3, -1, axis=2), axis=(1, 2))
    elif W == 2:
        E += beta_v*np.sum(S3[:, :, 0]*S3[:, :, 1], axis=1)
    # horizontal within supercolumn
    if k > 1:
        E += beta*np.sum(S3[:, :-1, :]*S3[:, 1:, :], axis=(1, 2))
    c = np.where(Bmask, 1.0, c0)
    Phi = S @ c
    MB = S @ Bmask.astype(float)
    logd = E + H*Phi
    K = beta*(S3[:, -1, :] @ S3[:, 0, :].T)   # last column of s to first column of s'
    M = 0.5*logd[:, None] + 0.5*logd[None, :] + K
    M -= M.max()
    return np.exp(M), MB, Phi

def ic_quantities(T, MB, Phi, Lring=None):
    # general (non-symmetric) transfer matrix: T = V diag(lam) V^{-1}
    lam, V = np.linalg.eig(T)
    o = np.argsort(-np.abs(lam)); lam = lam[o]; V = V[:, o]
    Vi = np.linalg.inv(V)
    X = {1: MB, 2: MB**2, 3: MB**3}
    A = {j: Vi @ (X[j][:, None]*V) for j in X}
    Bm = Vi @ (Phi[:, None]*V)
    lr = lam/lam[0]
    if Lring is None:
        mean = {j: np.real(A[j][0, 0]) for j in X}
        r = lr[1:]; g = r/(1 - r)
        S = {j: np.real(np.sum(A[j][0, 1:]*Bm[1:, 0]*(1 + g) + Bm[0, 1:]*A[j][1:, 0]*g)) for j in X}
    else:
        pw = lr**Lring; Z = pw.sum()
        mean = {j: np.real(np.sum(pw*np.diag(A[j]))/Z) for j in X}
        G = sum(np.outer(lr**(Lring-y), lr**y) for y in range(Lring))
        meanPhi = np.real(np.sum(pw*np.diag(Bm))/Z)
        S = {j: np.real(np.sum(G*A[j]*Bm.T)/Z) - Lring*mean[j]*meanPhi for j in X}
    m, P2, M3 = mean[1], mean[2], mean[3]
    u = M3 - m*P2
    up = S[3] - m*S[2] - P2*S[1]
    chi = S[1]
    Rp = (up*m - u*chi)/m**2
    terms = max(abs(up*m), abs(u*chi))/m**2
    cu = (abs(M3) + abs(m*P2))/abs(u) if u != 0 else np.inf
    return dict(m=m, R=u/m, Rp=Rp, chi=chi, rel=Rp/(abs(u/m)*chi/m) if u != 0 else 0.0, canc=(terms/abs(Rp))*cu if Rp != 0 else np.inf)

if __name__ == "__main__":
    W = int(sys.argv[1]); k = int(sys.argv[2])
    Bkind = sys.argv[3]                 # 'all' (whole super-column), 'col' (first column only), 'site2' (2 sites vertical)
    c0s = [float(v) for v in sys.argv[4].split(',')]
    betas = [float(v) for v in sys.argv[5].split(',')]
    Hs = [float(v) for v in sys.argv[6].split(',')]
    rings = [None] + [int(v) for v in sys.argv[7].split(',')] if len(sys.argv) > 7 else [None]
    ns = W*k
    Bmask = np.zeros(ns, bool)
    if Bkind == 'all': Bmask[:] = True
    elif Bkind == 'col': Bmask[:W] = True
    elif Bkind == 'site2': Bmask[:2] = True
    elif Bkind == 'diag': Bmask[0] = True; Bmask[W+1 if k > 1 else 1] = True
    rows = []; t0 = time.time()
    for c0 in c0s:
        for beta in betas:
            for H in Hs:
                T, MB, Phi = supercol(W, k, beta, beta, H, Bmask, c0)
                for Lr in rings:
                    q = ic_quantities(T, MB, Phi, Lr)
                    rows.append(dict(W=W, k=k, B=Bkind, c0=c0, beta=beta, H=H, L=Lr if Lr else 'inf', **{kk: float(vv) for kk, vv in q.items()}))
    tag = "W%d_k%d_%s" % (W, k, Bkind)
    json.dump(rows, open("ic_strip_%s.json" % tag, "w"))
    pos = [r for r in rows if r['Rp'] > 0]
    cert = [r for r in pos if r['canc'] < 1e11]
    print(tag, "time %.1f" % (time.time()-t0), "cases", len(rows), "R'>0:", len(pos), "certified(canc<1e11):", len(cert))
    for r in sorted(cert, key=lambda r: -r['rel'])[:5]: print("  POS", r)
    ok = [r for r in rows if r['canc'] < 1e11]
    b = max(ok, key=lambda r: r['rel'])
    print("  closest: rel=%.3e Rp=%.3e beta=%g H=%g c0=%g L=%s canc=%.1e" % (b['rel'], b['Rp'], b['beta'], b['H'], b['c0'], b['L'], b['canc']))

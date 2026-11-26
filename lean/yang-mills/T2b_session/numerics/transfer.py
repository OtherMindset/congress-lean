"""Transfer-matrix computation of the lattice target for phi^4 on rings / infinite chain /
width-W cylinders (periodic transverse), uniform field H, coupling J, single-site
weight exp(-a phi^2 - b phi^4 + H phi).

Exact derivative (no finite differences):
  u   = <phi0;phi0^2> = <phi0^3> - m P,           P = <phi0^2>
  u'  = dH u = S(phi^3) - m S(phi^2) - P S(phi),  S(X) = sum_x <X_0 ; phi_x>
  R'  = (u' m - u chi)/m^2,   chi = S(phi)
  target: R' <= 0.  rho := R'/S(phi^2)  (K-form; for transitive graphs Q = 8(1+rho)).
S(X) is computed from the spectral decomposition of the symmetric transfer matrix T
(column -> column), with X diagonal in column states, Phi_col = sum of phi over the column.
Discretisation: trapezoid grid of n points on [-L, L] per site (spectrally accurate).
"""
import numpy as np, itertools

def column_states(x, W, J):
    """all W-tuples of grid values; returns phi array (N,W) and intra-column log weight."""
    idx = np.array(list(itertools.product(range(len(x)), repeat=W)))
    ph = x[idx]
    intra = np.zeros(len(ph))
    if W == 2:
        intra = 2*J*ph[:, 0]*ph[:, 1] if False else J*ph[:, 0]*ph[:, 1]  # width-2 open (single bond)
    elif W >= 3:
        for i in range(W):
            intra += J*ph[:, i]*ph[:, (i+1) % W]
    return ph, intra

def build(a, b, J, H, n=121, L=None, W=1, Jintra=None, W2periodic=False):
    if L is None:
        L = 1.0
        # range where single-site weight with an effective field H + 2dJ L is non-negligible
        for _ in range(60):
            Heff = H + 2*(W > 1 and 2 or 1)*J*L*1.0
            xs = np.linspace(-4*L-10, 4*L+10, 20001)
            lw = -a*xs**2 - b*xs**4 + Heff*abs(xs)
            ok = xs[lw > lw.max() - 60]
            Lnew = max(abs(ok).max(), 0.5)
            if abs(Lnew - L) < 1e-3*L: break
            L = Lnew
    x = np.linspace(-L, L, n); dx = x[1]-x[0]
    Ji = J if Jintra is None else Jintra
    ph, intra = column_states(x, W, Ji)
    if W == 2 and W2periodic:
        intra = 2*intra
    lw1 = -a*x**2 - b*x**4 + H*x + np.log(dx)
    logd = lw1[np.array(list(itertools.product(range(n), repeat=W)))].sum(1) + intra if W > 1 else lw1.copy()
    logK = J*ph @ ph.T
    M = 0.5*logd[:, None] + 0.5*logd[None, :] + logK
    M -= M.max()
    T = np.exp(M)
    return T, ph, L

def observables(T, ph, Lring=None):
    lam, U = np.linalg.eigh(T)
    lam = lam[::-1]; U = U[:, ::-1]
    p0 = ph[:, 0]
    X = {1: p0, 2: p0**2, 3: p0**3}
    Phi = ph.sum(1)
    if Lring is None:  # infinite chain/cylinder: dominant eigenvector
        v = U[:, 0]; pi = v*v
        mean = {k: pi @ X[k] for k in X}
        # S(X) = sum_{n>=1} <0|X|n><n|Phi|0> (1+r_n)/(1-r_n), r_n = lam_n/lam_0
        r = lam[1:]/lam[0]
        Phin = U[:, 1:].T @ (v*Phi)
        fac = (1 + r)/(1 - r)
        S = {k: np.sum((U[:, 1:].T @ (v*X[k]))*Phin*fac) for k in X}
        return mean, S, lam
    # finite ring of length Lr: Z = sum lam^Lr
    Lr = Lring
    lr = lam/lam[0]
    pw = lr**Lr; Z = pw.sum()
    A = {k: U.T @ (X[k][:, None]*U) for k in X}
    B = U.T @ (Phi[:, None]*U)
    mean = {k: np.sum(pw*np.diag(A[k]))/Z for k in X}
    # <X_0 Phi_y> = sum_{n,k} lr_n^{Lr-y} lr_k^{y} A_nk B_kn / Z ; sum over y=0..Lr-1
    y = np.arange(Lr)
    G = np.zeros((len(lam), len(lam)))
    # geometric sums g_nk = sum_y lr_n^{Lr-y} lr_k^y
    for yy in y:
        G += np.outer(lr**(Lr-yy), lr**yy)
    S = {}
    Phibar = Lr*W_of(ph)*0  # placeholder not used
    meanPhi = np.sum(pw*np.diag(B))/Z
    for k in X:
        S[k] = np.sum(G*A[k]*B.T)/Z - Lr*mean[k]*meanPhi
    return mean, S, lam

def W_of(ph):
    return ph.shape[1]

def target(mean, S):
    m, P, M3 = mean[1], mean[2], mean[3]
    u = M3 - m*P
    up = S[3] - m*S[2] - P*S[1]
    chi = S[1]
    Rp = (up*m - u*chi)/m**2
    return dict(m=m, P=P, u=u, R=u/m, chi=chi, Rp=Rp, Sphi2=S[2], rho=Rp/S[2])

def gauss_nodes(a, b, H, n, c=0.0, fine=20001):
    """Gauss nodes/weights for measure exp(-(a-c)phi^2 - b phi^4 + H phi) dphi, via the
    discretised Stieltjes procedure on a fine trapezoid grid; returned weights are for the
    TRUE single-site weight exp(-a phi^2 - b phi^4 + H phi) (factor e^{-c x^2} applied)."""
    ac = a - c
    xs = np.linspace(-300, 300, 600001)
    lw = -ac*xs**2 - b*xs**4 + H*xs
    keep = lw > lw.max() - 80
    lo, hi = xs[keep].min(), xs[keep].max()
    x = np.linspace(lo, hi, fine)
    lw = -ac*x**2 - b*x**4 + H*x
    w = np.exp(lw - lw.max()); w /= w.sum()
    alpha = np.zeros(n); beta = np.zeros(n)
    p_prev = np.zeros_like(x); p = np.ones_like(x)
    nrm_prev = 1.0
    for k in range(n):
        nrm = np.sum(w*p*p)
        alpha[k] = np.sum(w*x*p*p)/nrm
        if k > 0: beta[k] = nrm/nrm_prev
        p_new = (x - alpha[k])*p - (beta[k]*p_prev if k > 0 else 0)
        p_prev, p, nrm_prev = p, p_new, nrm
        s = np.sqrt(np.sum(w*p*p)); p = p/s; p_prev = p_prev/s; nrm_prev = nrm_prev/s**2
    Jm = np.diag(alpha) + np.diag(np.sqrt(beta[1:]), 1) + np.diag(np.sqrt(beta[1:]), -1)
    nodes, vec = np.linalg.eigh(Jm)
    wts = vec[0]**2
    # log weights for TRUE measure: include e^{-c x^2}
    return nodes, np.log(wts) - c*nodes**2

def build_gauss(a, b, J, H, n, W=1, c=0.0, W2periodic=False):
    x, lwn = gauss_nodes(a, b, H, n, c=c)
    idx = np.array(list(itertools.product(range(n), repeat=W)))
    ph = x[idx]
    intra = np.zeros(len(ph))
    if W == 2:
        intra = J*ph[:, 0]*ph[:, 1]*(2 if W2periodic else 1)
    elif W >= 3:
        for i in range(W):
            intra += J*ph[:, i]*ph[:, (i+1) % W]
    logd = lwn[idx].sum(1) + intra
    M = 0.5*logd[:, None] + 0.5*logd[None, :] + J*ph @ ph.T
    M -= M.max()
    return np.exp(M), ph

def build_gauss2(a, b, J, H, n, W=1, c=0.0, hn=0.0, W2periodic=False):
    """Gauss nodes for node measure exp(-(a-c)x^2 - b x^4 + (H+hn) x); weights corrected
    to the true single-site weight exp(-a x^2 - b x^4 + H x)."""
    x, lwn = gauss_nodes(a, b, H + hn, n, c=c)   # lwn = log wts - c x^2  (node measure has +hn x)
    lwn = lwn - hn*x
    idx = np.array(list(itertools.product(range(n), repeat=W)))
    ph = x[idx]
    intra = np.zeros(len(ph))
    if W == 2:
        intra = J*ph[:, 0]*ph[:, 1]*(2 if W2periodic else 1)
    elif W >= 3:
        for i in range(W):
            intra += J*ph[:, i]*ph[:, (i+1) % W]
    logd = lwn[idx].sum(1) + intra
    M = 0.5*logd[:, None] + 0.5*logd[None, :] + J*ph @ ph.T
    M -= M.max()
    return np.exp(M), ph

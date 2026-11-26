"""Monotone L'Hopital test. R = N/m with N = <phi0;phi0^2>, N(0)=m(0)=0. If N'/m' is nonincreasing in H, so is R.
Test whether N'/m' is nonincreasing: (a) 0-d quartic e^{-a x^2 - b x^4 + H x}; (b) 2-site phi^4 with uniform field.
N'/m' in 0-d: (k4 + 2k2^2 + 2k1k3)/k2."""
import numpy as np
x = np.linspace(-12, 12, 6001)
def cums(a, b, H):
    S = -a*x**2 - b*x**4 + H*x; w = np.exp(S - S.max()); w /= w.sum()
    m = [(w*x**k).sum() for k in range(5)]
    k1 = m[1]; k2 = m[2]-k1**2; k3 = m[3]-3*m[2]*k1+2*k1**3
    k4 = m[4]-4*m[3]*k1-3*m[2]**2+12*m[2]*k1**2-6*k1**4
    return k1, k2, k3, k4
print("== 0-d ==")
for a in [-5, -2, -0.5, 0, 0.5, 2, 5]:
    for b in [0.05, 0.3, 1, 3]:
        Hs = np.linspace(1e-3, 8, 400); r = []; R = []
        for H in Hs:
            k1, k2, k3, k4 = cums(a, b, H); r.append((k4+2*k2**2+2*k1*k3)/k2); R.append((k3+2*k1*k2)/k1)
        r = np.array(r); R = np.array(R)
        inc = np.diff(r).max()/abs(r).max(); incR = np.diff(R).max()/abs(R).max()
        if inc > 1e-6: print(f"a={a} b={b}: N'/m' increases (rel {inc:.2e}); R increase rel {incR:.1e}")
print("== 2-site ring, uniform field ==")
y = np.linspace(-9, 9, 721); X, Y = np.meshgrid(y, y, indexing='ij')
def two(a, b, J, H):
    S = -a*(X**2+Y**2) - b*(X**4+Y**4) + J*X*Y + H*(X+Y); w = np.exp(S-S.max()); w /= w.sum(); E = lambda F: (w*F).sum()
    m = E(X); Q = X+Y
    N = E(X**3) - m*E(X**2)
    # N' = cov-cumulant k(X, X^2, Q); m' = cov(X,Q)
    def c3(A, B, C): return E(A*B*C)-E(A*B)*E(C)-E(A*C)*E(B)-E(B*C)*E(A)+2*E(A)*E(B)*E(C)
    return N/m, c3(X, X**2, Q)/(E(X*Q)-m*E(Q))
for a in [-1.5, -0.5, 0.5, 1.0, 2]:
    for b in [0.1, 1]:
        for J in [0.3, 1.0, 2.5]:
            Hs = np.linspace(1e-3, 5, 120); vals = np.array([two(a, b, J, H) for H in Hs])
            inc = np.diff(vals[:, 1]).max()/abs(vals[:, 1]).max(); incR = np.diff(vals[:, 0]).max()/abs(vals[:, 0]).max()
            if inc > 1e-6 or incR > 1e-6: print(f"a={a} b={b} J={J}: N'/m' rel inc {inc:.2e}, R rel inc {incR:.2e}")
print("done")

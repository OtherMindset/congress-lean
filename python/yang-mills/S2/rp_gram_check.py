# NON-RIGOROUS numerical sanity check for the link-plane reflection-positivity lemma (SU(2) Wilson).
# One crossing plaquette in temporal gauge: links A (t=1) and B (t=0) in SU(2), Haar x Haar,
# weight exp((beta/2) tr(A B^dagger)).  Gram matrix G_kl = E[ conj(f_k(B)) f_l(A) ] for the
# observables f = 1, the four matrix entries of A, and four quadratic monomials.
# Lemma: G is positive semidefinite for beta >= 0.  For beta < 0 it is not (the half-integer-spin
# coefficients of the character expansion change sign).
# Quadrature: A = [[a, b], [-conj b, conj a]], a = sqrt(u) e^{i x}, b = sqrt(1-u) e^{i y},
# Haar = du dx dy / (2 pi)^2 on [0,1] x [0,2pi)^2; Gauss-Legendre in u, trapezoid in x, y.
# numpy only; deterministic; values printed to 6 decimals (eigenvalues with |.| < 5e-7 print as 0).
import numpy as np

def haar_nodes(nu=10, na=14):
    x, w = np.polynomial.legendre.leggauss(nu)
    u = (x + 1) / 2
    wu = w / 2
    ang = 2 * np.pi * np.arange(na) / na
    U, X, Y = np.meshgrid(u, ang, ang, indexing="ij")
    W = np.repeat(wu, na * na) / (na * na)
    a = (np.sqrt(U) * np.exp(1j * X)).ravel()
    b = (np.sqrt(1 - U) * np.exp(1j * Y)).ravel()
    return a, b, W

def gram(beta):
    a, b, W = haar_nodes()
    f = np.array([np.ones_like(a), a, b, -np.conj(b), np.conj(a),
                  a * a, a * b, b * b, a * np.conj(a)])
    # (1/2) tr(A B^dagger) = Re(a conj(a') + b conj(b'))
    K = np.exp(beta * np.real(np.outer(np.conj(a), a) + np.outer(np.conj(b), b)))  # K[B, A]
    Z = W @ K @ W
    G = (np.conj(f) * W) @ K @ (f * W).T / Z
    return (G + G.conj().T) / 2

def r(x):
    v = round(float(x), 6)
    return 0.0 if v == 0 else v

for beta in (1.0, 0.1, 0.0, -0.1, -1.0):
    ev = np.linalg.eigvalsh(gram(beta))
    print("beta = %+.1f  min eigenvalue = %+.6f  max = %+.6f  E[conj(B_11) A_11] = %+.6f"
          % (beta, r(ev[0]), r(ev[-1]), r(gram(beta)[1, 1].real)))
print("first-order prediction for E[conj(B_11) A_11]: beta/8 = %+.6f at beta = 0.1" % (0.1 / 8))

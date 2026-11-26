# Independent exact ring (1D torus, J per bond, degree 2) computations by transfer matrix with
# truncated power series in (H, s):  weight exp(J sum phi_i phi_{i+1} - sum (a phi^2 + b phi^4) + H M - s Phi2).
# Gives m2, m4, -d_a m2, <phi0^2>, chi3 = sum_x <phi0^3 phi_x>, chi exactly (up to quadrature), no extrapolation.
import numpy as np
from numpy.polynomial.legendre import leggauss
from math import factorial
PH, PS = 5, 2   # H-degree < 5, s-degree < 2

def grid(a, b, J, ng):
    R = 1.0
    while (a - J) * R * R + b * R**4 < 60: R += 0.05
    x, w = leggauss(ng); return R * x, R * w

def mul(A, B):
    C = np.zeros_like(A)
    for p in range(PH):
        for q in range(PS):
            for p1 in range(p + 1):
                for q1 in range(q + 1):
                    C[p, q] += A[p1, q1] @ B[p - p1, q - q1]
    return C

def series_trace(a, b, J, N, ng=160, ins=None):
    """returns Z coefficients c[p,q] of H^p s^q (relative scale) for ring of N sites; ins = diag insertion at site 0"""
    x, w = grid(a, b, J, ng)
    V = a * x * x + b * x**4
    K = np.exp(J * np.outer(x, x) - 0.5 * V[:, None] - 0.5 * V[None, :]) * np.sqrt(np.outer(w, w))
    T = np.zeros((PH, PS, ng, ng))
    for p in range(PH):
        for q in range(PS):
            d = x**p / factorial(p) * (-x * x)**q / factorial(q)
            T[p, q] = K * d[None, :]
    P = T.copy(); logsc = 0.0
    if ins is not None:
        P = np.zeros_like(T)
        for p in range(PH):
            for q in range(PS): P[p, q] = T[p, q] * ins(x)[None, :]
    for i in range(N - 1):
        P = mul(P, T); sc = np.abs(P[0, 0]).max(); P /= sc; logsc += np.log(sc)
    c = np.array([[np.trace(P[p, q]) for q in range(PS)] for p in range(PH)])
    return c, logsc

def obs(a, b, J, N, ng=160):
    c, l = series_trace(a, b, J, N, ng)
    Z = c[0, 0]
    X = 2 * c[2, 0] / Z; M4 = 24 * c[4, 0] / Z
    dsX = 2 * (c[2, 1] / Z - c[2, 0] * c[0, 1] / Z**2)   # d/da <M^2>
    Phi2 = -c[0, 1] / Z
    m2 = X / N**2; m4 = M4 / N**4; dam2 = dsX / N**2
    p2 = Phi2 / N
    c3, l3 = series_trace(a, b, J, N, ng, ins=lambda x: x**3)
    chi3 = (c3[1, 0] * np.exp(l3 - l)) / Z      # <phi0^3 M>
    return dict(m2=m2, m4=m4, dam2=dam2, phi2=p2, chi3=chi3, chi=N * m2, B=m4 / m2**2 - 3)

if __name__ == "__main__":
    # sanity: Gaussian ring b->0 small, compare chi with exact sum of covariance
    a, J, N = 1.5, 1.0, 6
    o = obs(a, 1e-9, J, N)
    A = 2 * a * np.eye(N) - J * (np.roll(np.eye(N), 1, 0) + np.roll(np.eye(N), -1, 0))
    print("gauss chi", o['chi'], np.linalg.inv(A).sum() / N, "B", o['B'], "dam2", o['dam2'], -2*(np.linalg.inv(A)@np.linalg.inv(A)).sum()/N**2*1)

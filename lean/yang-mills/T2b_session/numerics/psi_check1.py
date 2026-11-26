import numpy as np, psi_test as P
a, J = -1.0, 0.5
x, lw, K = P.grid_setup(a, 1.0, J, 121, 3.0)
for h in [0.1, 0.5, 1.5]:
    v, psi, err, km = P.psi_point(x, lw, K, 1, h)
    # direct: single-site density f ∝ exp(-(a-J)w^2 - w^4)
    w = np.linspace(-8, 8, 40001); f = lambda y: np.exp(-(a-J)*y**2 - y**4)
    N = np.trapezoid(v*(2*w - v)**2*f(w)*f(v - w), w); D = np.trapezoid(f(w)*f(v - w), w)
    print(h, v, psi, err, (2*1)*0 + N/(v*D))

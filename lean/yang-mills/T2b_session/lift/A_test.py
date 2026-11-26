"""Inequality (A): for x != y,  <q0 qx^2 qy^2><q0>  >=  <q0 qx^2><q0 qy^2>
q-system: weight exp(sum_{x<y} J_xy q_x q_y + h sum q - sum_x (A_x q_x^2 + c q_x^4)), A_x site-dependent (A_x = a + 3b t_x^2), c = b/2.
n sites (3 or 4), random graphs, 1e-? relative tolerance."""
import numpy as np, itertools, sys
n = int(sys.argv[1]); trials = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
rng = np.random.default_rng(seed); G = 161 if n == 3 else 49
worst = (-np.inf, None)
for t in range(trials):
    b = 10**rng.uniform(-1.5, 0.7); a = rng.uniform(-2.0, 2.5)
    tt = rng.normal(0, 1.5, n)*(rng.random(n) < 0.7); A = a + 3*b*tt**2; c = b/2
    J = np.triu(10**rng.uniform(-1.3, 0.5, (n, n))*(rng.random((n, n)) < 0.7), 1)
    h = 10**rng.uniform(-2.5, 0.6)
    L = min(14, 2.5 + 2.2*np.sqrt(max(-A.min(), 1)/c)**0.5*np.sqrt(np.sqrt(max(-A.min(), 1)/c)) + (h/c)**(1/3))
    L = min(14, 3 + 1.6*(max(-A.min(), 0.5)/c)**0.5 + (h/c)**(1/3))
    x = np.linspace(-L, L, G)
    Q = np.meshgrid(*([x]*n), indexing='ij')
    S = h*sum(Q) - sum(A[i]*Q[i]**2 + c*Q[i]**4 for i in range(n))
    for i in range(n):
        for j in range(i+1, n):
            if J[i, j]: S = S + J[i, j]*Q[i]*Q[j]
    w = np.exp(S - S.max()); w /= w.sum(); E = lambda F: (w*F).sum()
    m = E(Q[0])
    for xx, yy in itertools.combinations(range(n), 2):
        lhs = E(Q[0]*Q[xx]**2*Q[yy]**2)*m; rhs = E(Q[0]*Q[xx]**2)*E(Q[0]*Q[yy]**2)
        r = (rhs - lhs)/(abs(lhs) + abs(rhs))
        if r > worst[0]: worst = (r, dict(pair=(xx, yy), a=round(a, 3), b=round(b, 3), A=A.round(2), J=J.round(2), h=round(h, 4)))
print(n, "worst relative violation (positive = (A) fails):", worst)

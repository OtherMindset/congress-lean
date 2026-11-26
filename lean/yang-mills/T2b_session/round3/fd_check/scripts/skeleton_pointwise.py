# Pointwise check of the skeleton inequality  u4(x1..x4) >= -24 b sum_w prod_i G(x_i,w)
# (and Lebowitz u4 <= 0) on 1 site and rings N = 2..6 (N=2: two sites with a double bond; N=3: triangle K3).
# Also: is the constant 24 sharp (ratio -> 1 as b -> 0)?  Is a smaller constant false?
import numpy as np, itertools, sys
from ring import Ring

def check(a, b, J, N, ng=200):
    r = Ring(a, b, J, N, ng)
    G1 = r.G()
    G = lambda i, j: G1[(j - i) % N]
    worst = 0.0; worst_t = None; maxu4 = -np.inf
    for t in itertools.product(range(N), repeat=3):
        xs = (0,) + t
        cnt = [0] * N
        for v in xs: cnt[v] += 1
        m4 = r.corr(cnt)
        u4 = m4 - G(xs[0], xs[1]) * G(xs[2], xs[3]) - G(xs[0], xs[2]) * G(xs[1], xs[3]) - G(xs[0], xs[3]) * G(xs[1], xs[2])
        tree = 24 * b * sum(np.prod([G(xi, w) for xi in xs]) for w in range(N))
        rat = -u4 / tree
        maxu4 = max(maxu4, u4 / tree)
        if rat > worst: worst, worst_t = rat, xs
    return worst, worst_t, maxu4

print("# a b J N | max over (x1..x4) of -u4/(24 b sum_w prod G)  [skeleton says <=1] | argmax | max u4/tree [Lebowitz says <=0]")
cases = []
for b in [2.0, 0.5, 0.1, 0.01, 0.001]:
    for a in [3.0, 1.0, 0.0, -1.0, -3.0]:
        cases.append((a, b, 0.0, 1))
        for N in [2, 3, 4, 6]:
            cases.append((a, b, 1.0, N))
glob = 0
for (a, b, J, N) in cases:
    if N > 1 and a - J + 0 < -6 and b < 0.01:  # skip very deep wells with tiny b (grid too wide)
        continue
    w, t, mu = check(a, b, J, N)
    glob = max(glob, w)
    print("%5.2f %6.3f %.1f %d | %.6f | %s | %.2e%s" % (a, b, J, N, w, t, mu, "  VIOLATION" if w > 1 + 1e-7 or mu > 1e-9 else ""))
    sys.stdout.flush()
print("global max ratio", glob)

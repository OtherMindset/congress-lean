# Theorem 4 (FD_kappa on [a-,a+]  =>  f(a-) >= (24 kappa b)^{-1} int |B|).
# (i) adversarial test of the pure real-analysis lemma: random positive nonincreasing f, and |B| taken as LARGE as
#     (FD_kappa) allows: |B|(a) = min(2, 3(1 - f(a+4b kappa f(a))/f(a))). Report min of f(a-)*24 kappa b / int|B|.
# (ii) one-site physical check with kappa = 1 (Theorem 2c).
import numpy as np
from scipy.interpolate import PchipInterpolator
rng = np.random.default_rng(7)
worst = np.inf; worst_case = None
for trial in range(4000):
    b = 10**rng.uniform(-3, 0); kappa = 10**rng.uniform(-1, 1)
    am, ap = 0.0, 10**rng.uniform(-2, 1.5)
    # random nonincreasing positive f on [am, ap + big]: piecewise-monotone cubic through random decreasing knots
    K = rng.integers(3, 12)
    xs = np.sort(np.concatenate([[am], rng.uniform(am, ap * 3 + 5, K), [ap * 3 + 1e3]]))
    ys = np.sort(10**rng.uniform(-4, 1, len(xs)))[::-1]
    if rng.random() < 0.3:   # plateaus / sharp drops
        ys = np.sort(np.concatenate([ys[:2], np.repeat(ys[2], len(ys) - 2)]))[::-1] * (1 + 1e-9 * np.arange(len(ys)))[::-1]
    f = PchipInterpolator(xs, ys, extrapolate=True)
    fe = lambda a: np.maximum(f(np.minimum(a, xs[-1])), ys[-1])
    a = np.linspace(am, ap, 4001)
    Bm = np.clip(3 * (1 - fe(a + 4 * b * kappa * fe(a)) / fe(a)), 0, 2)
    I = np.trapezoid(Bm, a)
    if I <= 1e-14: continue
    r = fe(np.array([am]))[0] * 24 * kappa * b / I
    if r < worst: worst, worst_case = r, (b, kappa, ap, K)
print("(i) adversarial lemma test: min ratio f(a-)*24 kappa b / int|B| =", worst, "(must be >= 1)", worst_case)

# also the sharper intermediate claim G(a1) = int_{a1}^{a+} |B| f <= 12 kappa b f(a1)^2, on the same random families
from mpmath import mp, mpf, quad, exp, inf
mp.dps = 20
def mom(a, k):
    return 2 * quad(lambda x: x**k * exp(-a * x * x - x**4), [0, 1, 3, 8, inf])
def f1(a): return float(mom(a, 2) / mom(a, 0))
def B1(a): z = mom(a, 0); m2 = mom(a, 2) / z; return float(3 - (mom(a, 4) / z) / m2**2)
print("(ii) one site, b = 1, kappa = 1:  window [a-, a+] | f(a-) | int|B|/24 | ratio")
for (am, ap) in [(-10, 10), (-4, 4), (0, 50), (2, 200), (-30, -10), (-3, 30)]:
    aa = np.linspace(am, ap, 801); Bv = np.array([B1(x) for x in aa])
    I = np.trapezoid(Bv, aa)
    print("  [%5g,%5g] | %.5f | %.5f | %.3f" % (am, ap, f1(am), I / 24, f1(am) * 24 / I))

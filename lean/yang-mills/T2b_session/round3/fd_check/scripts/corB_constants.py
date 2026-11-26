# Corollary B constants and the Parseval/IR chain, checked with the extremal profile allowed by the IR bound:
#   Ghat(p) = min(chi, 1/E(p)) for p != 0 (lattice units), Ghat(0) = chi, on the n x n torus (n = L/eps).
# theta/lambda = 12 eps^2 sum_z G^2 = 12 eps^2 /N sum_p Ghat(p)^2 (lattice).  Compare with Theta/lambda.
import numpy as np
from mpmath import mp, zeta, catalan, pi, sqrt
mp.dps = 20
c = 1 + 1 / sqrt(2); C = pi ** 2 / 4
print("13.73 const:", 12 * c ** 2 * C / (2 * pi))
S4 = 4 * zeta(2) * catalan  # sum_{n != 0} |n|^-4 = 4 zeta(2) beta(2)
# direct lattice sum check
import itertools
s = sum(1.0 / (i * i + j * j) ** 2 for i in range(-400, 401) for j in range(-400, 401) if (i, j) != (0, 0))
print("4 zeta(2) beta(2) =", S4, " direct sum (|n|<=400 box):", s)
print("0.2825 const:", 12 * S4 * C ** 2 / (16 * pi ** 4))
# FD_2 threshold for theta: (1-t)(1-2t/3) = 1/2
from scipy.optimize import brentq
print("FD_2 threshold theta*:", brentq(lambda t: (1 - t) * (1 - 2 * t / 3) - 0.5, 0, 1), " value at 0.34:", (1 - .34) * (1 - 2 * .34 / 3))
print("FD_3 at theta=1/2:", 1 / ((1 - .5) * (1 - 1 / 3)))

worst = 0
for n in [4, 6, 8, 16, 32, 64, 128]:
    for L in [0.5, 1.0, 4.0, 16.0]:
        eps = L / n
        p = 2 * np.pi * np.arange(n) / n
        E = 2 * (1 - np.cos(p))[:, None] + 2 * (1 - np.cos(p))[None, :]
        for chiL in [1e-3, 0.1, 1.0, 10.0, 100.0, 1e4]:
            chi = chiL / eps ** 2
            Gh = np.where(E > 0, np.minimum(chi, 1 / np.where(E > 0, E, 1)), chi)
            thl = 12 * eps ** 2 * (Gh ** 2).sum() / n ** 2       # theta / lambda
            Thl = 12 * chiL ** 2 / L ** 2 + min(13.73 * chiL, 0.2825 * L ** 2)
            worst = max(worst, thl / Thl)
print("max (theta/Theta) over extremal IR profiles:", worst, "(must be <= 1)")
# Gaussian (b -> 0) example: Ghat = 1/(E + m^2): theta vs Theta and vs 12/(4 pi m^2) heuristic
for n, L, m in [(64, 8.0, 1.0), (128, 8.0, 1.0), (128, 32.0, 0.5), (256, 32.0, 0.5)]:
    eps = L / n; p = 2 * np.pi * np.arange(n) / n
    E = 2 * (1 - np.cos(p))[:, None] + 2 * (1 - np.cos(p))[None, :]
    Gh = 1 / (E + (m * eps) ** 2); chiL = eps ** 2 * Gh[0, 0]
    thl = 12 * eps ** 2 * (Gh ** 2).sum() / n ** 2
    Thl = 12 * chiL ** 2 / L ** 2 + min(13.73 * chiL, 0.2825 * L ** 2)
    print("Gaussian n=%d L=%g m=%g: theta/lam=%.4f  Theta/lam=%.4f  ratio=%.3f  12/(4pi m^2)=%.4f  0.955*chiL=%.4f" % (n, L, m, thl, Thl, Thl / thl, 12 / (4 * np.pi * m * m), 0.955 * chiL))

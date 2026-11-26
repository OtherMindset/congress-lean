# Independent test of (S1), (S2), B2 monotonicity, the slope bound, and Theorem A on phi^4 rings (J = 1), exact.
# For each (b, N) the masses a are a fixed grid PLUS masses tuned so that theta = 12 b B2 hits 0.5, 0.8, 0.9, 0.95, 0.99.
import numpy as np, sys
from scipy.optimize import brentq
from ring import quantities, m2_only

J = 1.0
def theta_of(a, b, N):
    q = quantities(a, b, J, N); return 12 * b * q['B2']

def kmin(a, b, N, m2, B):
    tgt = (1 - abs(B) / 3) * m2
    g = lambda k: m2_only(a + 4 * b * k * m2, b, J, N) - tgt
    if g(1e-9) <= 0: return 0.0
    hi = 1.0
    while g(hi) > 0:
        hi *= 2
        if hi > 1e4: return np.inf
    return brentq(g, 1e-9, hi, xtol=1e-9)

print("# b N a | theta x | S1=|B|/24x  S2=(-dchi)/(2chi^2(1-theta)) | kappaA kappamin | slope: [m2(a+dA)/m2(a)]*(1+8(1-th)kA x) (<=1) | G=|B|/m2 | B2 mono")
bad = 0; worst_kmin = 0; worst_S1 = 0; min_S2 = np.inf; worst_slope = 0; ntheta = 0
for b in [0.5, 0.1, 0.02, 0.005]:
    for N in [4, 16, 64]:
        alist = [3.0, 2.0, 1.5, 1.2, 1.0, 0.0]
        # tune a to theta targets (theta decreases in a)
        for th in [0.5, 0.8, 0.9, 0.95, 0.99]:
            lo, hi = 0.0, 6.0
            while theta_of(lo, b, N) < th: lo -= 0.5
            try:
                alist.append(brentq(lambda a: theta_of(a, b, N) - th, lo, hi, xtol=1e-6))
            except ValueError:
                pass
        alist = sorted(set(alist), reverse=True)
        prevB2 = None
        for a in alist:
            q = quantities(a, b, J, N)
            m2, B, chi, B2, mdchi = q['m2'], q['B'], q['chi'], q['B2'], q['mdchi']
            theta = 12 * b * B2; x = b * chi ** 2 / N
            S1 = abs(B) / (24 * x)
            S2tot = mdchi / (2 * chi ** 2 - 24 * b * chi ** 2 * B2) if theta < 1 else np.nan
            # raw form of S2 independent of sign of (1-theta): -dchi - 2chi^2(1-theta) >= 0
            S2raw = mdchi - 2 * chi ** 2 * (1 - theta)
            km = kmin(a, b, N, m2, B)
            if theta < 1:
                ntheta += 1
                kA = 1 / ((1 - theta) * (1 - 8 * x))
                dA = 4 * b * kA * m2
                sl = m2_only(a + dA, b, J, N) / m2 * (1 + 8 * (1 - theta) * kA * x)
                worst_slope = max(worst_slope, sl)
                min_S2 = min(min_S2, S2tot)
            else:
                kA = np.inf; sl = np.nan
            mono = "" if prevB2 is None else ("ok" if B2 >= prevB2 * (1 - 1e-12) else "FAIL")  # list is in DECREASING a, so B2 must increase
            prevB2 = B2
            worst_S1 = max(worst_S1, S1)
            if theta < 1: worst_kmin = max(worst_kmin, km)
            flag = ""
            if S1 > 1 + 1e-7: flag += " S1FAIL"
            if S2raw < -1e-9 * chi ** 2: flag += " S2FAIL"
            if km > kA + 1e-6: flag += " AFAIL"
            if theta < 1 and sl > 1 + 1e-7: flag += " SLOPEFAIL"
            if mono == "FAIL": flag += " B2FAIL"
            if flag: bad += 1
            print("%5.3f %2d %7.4f | %.4f %.3e | %.4f %s | %8.4f %.4f | %s | %.4f | %s%s" % (
                b, N, a, theta, x, S1, ("%.4f" % S2tot) if theta < 1 else "  -   ", kA, km,
                ("%.6f" % sl) if theta < 1 else "   -    ", abs(B) / m2, mono, flag))
            sys.stdout.flush()
print("cases with theta<1:", ntheta, " worst kappamin (theta<1):", worst_kmin, " worst S1:", worst_S1, " min S2 ratio:", min_S2, " worst slope ratio:", worst_slope, " bad:", bad)

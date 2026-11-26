"""Crossing of U between L and 2L: linear (or quadratic if >=4 pts) fit of U_L(a)-U_2L(a); jackknife-free error via
propagating eU through a Monte-Carlo resampling of the (U,eU) values. usage: cross.py scan.json [more.json ...]"""
import json, sys, numpy as np
rs = []
for f in sys.argv[1:]: rs += json.load(open(f))
Ls = sorted({r['L'] for r in rs})
rng = np.random.default_rng(1)
def U(L):
    d = sorted([(r['a'], r['U'], r['eU']) for r in rs if r['L'] == L]); return np.array(d)
def cross(L1, L2, deg=1, nb=400):
    d1, d2 = U(L1), U(L2)
    common = sorted(set(d1[:, 0]) & set(d2[:, 0]))
    a = np.array(common)
    u1 = np.array([d1[d1[:, 0] == x][0] for x in a]); u2 = np.array([d2[d2[:, 0] == x][0] for x in a])
    def solve(du):
        p = np.polyfit(a, du, deg); roots = np.roots(p); roots = roots[np.isreal(roots)].real
        roots = roots[(roots > a.min() - 0.5 * np.ptp(a)) & (roots < a.max() + 0.5 * np.ptp(a))]
        return roots[np.argmin(abs(roots - a.mean()))] if len(roots) else np.nan
    c0 = solve(u1[:, 1] - u2[:, 1])
    s = [solve((u1[:, 1] + rng.normal(size=len(a)) * u1[:, 2]) - (u2[:, 1] + rng.normal(size=len(a)) * u2[:, 2])) for _ in range(nb)]
    return c0, np.nanstd(s), len(a)
for L in Ls:
    if 2 * L in Ls:
        import os; c, e, n = cross(L, 2 * L, int(os.environ.get("DEG", 1))); print(f'crossing L={L}/{2*L}: a_c = {c:.5f} +- {e:.5f}  ({n} pts)')

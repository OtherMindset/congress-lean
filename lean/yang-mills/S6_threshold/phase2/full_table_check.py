# Exact check of the closed form used by GAffineEval.lean for the full table (standard library only).
#   python3 full_table_check.py
# G_affine_cert.py builds QFULL by base[n] = base[n-2] (n-1)/(n+2), base[0] = 1/2, base[1] = 0, and then
# ktab: T[k][n] = T[k-1][n] - T[k-1][n+2].  That is T[k][n] = (1/pi) int_{-1}^{1} x^n (1-x^2)^(k+1/2) dx,
# a Beta integral:  T[k][2j] = (2j-1)!! (2k+1)!! / (2^(j+k+1) (j+k+1)!),  T[k][2j+1] = 0.
# The Lean evaluator walks it by T[k][2j+2] = T[k][2j] (2j+1)/(2(j+k+2)), T[k+1][0] = T[k][0] (2k+3)/(2(k+2)).
# This program checks, in exact rationals, that the three agree at every entry of QFULL.
from fractions import Fraction as Fr
from math import factorial

# BEGIN COPY (G_affine_cert.py, the constants and the two table functions)
JS, JD, KR = 18, 5, 7
NK = 2 * JD + 3
NMAX = NK + JS
NB = NMAX + 2 * KR + 2


def ktab(base):
    tab = [base]
    for k in range(1, KR + 1):
        tab.append([tab[-1][n] - tab[-1][n + 2] for n in range(len(tab[-1]) - 2)])
    return tab


def full_coeffs():
    base = [Fr(1, 2), Fr(0)]
    for n in range(2, NB):
        base.append(base[n - 2] * (n - 1) / (n + 2))
    return ktab(base)
# END COPY


def dfact(n):
    return 1 if n <= 0 else n * dfact(n - 2)


def closed(k, n):
    if n % 2:
        return Fr(0)
    j = n // 2
    return Fr(dfact(2 * j - 1) * dfact(2 * k + 1), 2 ** (j + k + 1) * factorial(j + k + 1))


def walked(k, n):
    t0 = Fr(1, 2)
    for i in range(k):
        t0 *= Fr(2 * i + 3, 2 * (i + 2))
    if n % 2:
        return Fr(0)
    t = t0
    for j in range(n // 2):
        t *= Fr(2 * j + 1, 2 * (j + k + 2))
    return t


Q = full_coeffs()
cnt = 0
for k, row in enumerate(Q):
    for n, q in enumerate(row):
        assert q == closed(k, n) == walked(k, n), (k, n)
        assert q >= 0
        cnt += 1
assert cnt == sum(NB - 2 * k for k in range(KR + 1))
print("QFULL entries checked:", cnt, "(k <= %d, n < %d - 2k); all equal the closed form and are >= 0" % (KR, NB))
print("used by the evaluator: k <= %d, n <= %d" % (KR, NMAX))

# Exact-arithmetic enclosures of beta_0(D), the root of 6(D-1) T(beta) = 1, T(k) = L_1(k)/I_1(k) = N(k)/Z(k),
#   N(k) = int_0^1 2 sinh(kx) sqrt(1-x^2) dx,  Z(k) = int_{-1}^1 e^{kx} sqrt(1-x^2) dx   (TV of vMF(+k v), vMF(-k v) on S^3).
# Python ints and fractions only.  Termwise integration (all terms positive):
#   N(k) = sum_j a_j, a_j = k^(2j+1) j!/((2j+1)! prod_{i=0..j}(i+3/2));  Z(k) = pi sum_j b_j, b_j = k^(2j)/(2 4^j j!(j+1)!).
# Tails for 0 < k < 1: a_{j+1}/a_j = k^2/(2(2j+3)(j+5/2)) <= k^2/6, b_{j+1}/b_j = k^2/(4(j+1)(j+2)) <= k^2/8, so the
# tail after index J is at most (last term) x/(1-x), x = k^2/6 resp. k^2/8.  pi by Machin's formula (alternating series).
# T is strictly increasing (dT/dk = 2 Cov_k(1_{X>0}, X) > 0), so 6(D-1)T(lo) < 1 < 6(D-1)T(hi) encloses the root.
# Also checked, for the accompanying theorem: (B) 6 (2/5) (4/(3 pi)) > 1 + (cosh(1/5) - 1)/4, used there for
#   beta_0(D) < 2/(5(D-1)), D >= 3; and directly: the upper end of each enclosure is < 2/(5(D-1)).
from fractions import Fraction as Fr
from math import factorial

def need(ok, msg):
    if not ok:
        print("FAILED:", msg)
        raise SystemExit(1)

def atan_fr(x, n):
    s, out = Fr(0), []
    for k in range(n + 1):
        s += Fr((-1) ** k) * x ** (2 * k + 1) / (2 * k + 1)
        out.append(s)
    return min(out[-2:]), max(out[-2:])

_a5, _a239 = atan_fr(Fr(1, 5), 12), atan_fr(Fr(1, 239), 4)
PI_LO, PI_HI = 16 * _a5[0] - 4 * _a239[1], 16 * _a5[1] - 4 * _a239[0]
need(Fr(314159265358, 10 ** 11) < PI_LO < PI_HI < Fr(314159265359, 10 ** 11), "pi enclosure")
J = 12

def N_bounds(k):
    s, last = Fr(0), None
    for j in range(J + 1):
        prod = Fr(1)
        for i in range(j + 1):
            prod *= Fr(2 * i + 3, 2)
        last = k ** (2 * j + 1) * factorial(j) / (factorial(2 * j + 1) * prod)
        s += last
    x = k * k / 6
    return s, s + last * x / (1 - x)

def Zq_bounds(k):  # Z/pi
    s, last = Fr(0), None
    for j in range(J + 1):
        last = k ** (2 * j) / (2 * 4 ** j * factorial(j) * factorial(j + 1))
        s += last
    x = k * k / 8
    return s, s + last * x / (1 - x)

def T_bounds(k):
    need(0 < k < 1, "range of k")
    nlo, nhi = N_bounds(k)
    zlo, zhi = Zq_bounds(k)
    return nlo / (zhi * PI_HI), nhi / (zlo * PI_LO)

DG = 7
SC = 10 ** DG

def bracket(D):
    # largest integer n with 6(D-1) T(n/SC) certified < 1; then check certified > 1 at (n+1)/SC
    lo, hi = 1, SC - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if 6 * (D - 1) * T_bounds(Fr(mid, SC))[1] < 1:
            lo = mid
        else:
            hi = mid
    need(6 * (D - 1) * T_bounds(Fr(lo, SC))[1] < 1 and 6 * (D - 1) * T_bounds(Fr(lo + 1, SC))[0] > 1, "bracket D=%d" % D)
    return lo

def dec(n, dg=DG):
    return "%d.%s" % (n // 10 ** dg, str(n % 10 ** dg).rjust(dg, "0"))

print("pi in (3.14159265358, 3.14159265359): checked by Machin's formula")
for D in (2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 20, 50, 100):
    n = bracket(D)
    x_lo, x_hi = 2 * (D - 1) * n, 2 * (D - 1) * (n + 1)
    need(Fr(n + 1, SC) < Fr(2, 5 * (D - 1)), "root below 2/(5(D-1))")
    msg = "D = %3d: 6(D-1) T < 1 at beta = %s and > 1 at beta = %s; so %s < beta_0(D) < %s; 2(D-1) beta_0 in (%s, %s)"
    print(msg % (D, dec(n), dec(n + 1), dec(n), dec(n + 1), dec(x_lo), dec(x_hi)))
# (B): cosh(1/5) - 1 <= (1/50) / (1 - 1/300) (series, ratio of consecutive terms <= (1/25)/12)
ch = Fr(1, 50) / (1 - Fr(1, 300))
need(6 * Fr(2, 5) * 4 / (3 * PI_HI) > 1 + ch / 4, "(B)")
print("(B) checked: 6 (2/5) (4/(3 pi)) > 1 + (cosh(1/5) - 1)/4")
print("CERTIFIED: the enclosures of beta_0(D) listed above (D = 2 is the root of 6 T = 1), each to 7 decimals")

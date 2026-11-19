# Failure side of the single-link Dobrushin criterion, 4D SU(2) Wilson, weight exp((beta/2) sum tr U_p).
# Exact rational arithmetic, standard library only, deterministic.
# Configuration: other five staples sum to 0, the moved staple goes v -> -v, so the two
# one-link conditional laws are vMF(+k v), vMF(-k v) on S^3 with k = beta, and
#   TV = N(k)/D(k),  N = int_0^1 2 sinh(k x) sqrt(1-x^2) dx,  D = int_{-1}^1 e^{k x} sqrt(1-x^2) dx.
# Row sum of the Dobrushin matrix >= 18*TV.  Termwise (Beta) integration, all terms positive:
#   N(k) = sum_{j>=0} a_j,  a_j = k^(2j+1) * j! / ((2j+1)! * prod_{i=0..j}(i+3/2))
#   D(k) = pi * sum_{j>=0} b_j,  b_j = k^(2j) / (2 * 4^j * j! * (j+1)!)
# (so TV = L_1(k)/I_1(k), modified Struve over modified Bessel).
# Tails: a_{j+1}/a_j = k^2/(2(2j+3)(j+5/2)) <= k^2/6 and b_{j+1}/b_j = k^2/(4(j+1)(j+2)) <= k^2/8,
# so for 0<k<1 the tail after index J is at most (last term)*r/(1-r), r = k^2/6 resp. k^2/8.
# pi is enclosed by 3.14159265358 < pi < 3.14159265359.
# Result: 18*TV < 1 at beta = 0.13103 (the posted value), > 1 at beta = 0.131031 and 0.13104,
# and < 1 at beta = pi/24.  TV is increasing in k, so the criterion fails for all beta >= 0.131031.
from fractions import Fraction as F
from math import factorial

PI_LO, PI_HI = F(314159265358, 10**11), F(314159265359, 10**11)

def N_bounds(k, J=12):
    s = F(0); last = None
    for j in range(J + 1):
        prod = F(1)
        for i in range(j + 1):
            prod *= F(2 * i + 3, 2)
        last = k ** (2 * j + 1) * factorial(j) / (factorial(2 * j + 1) * prod)
        s += last
    r = k * k / 6
    return s, s + last * r / (1 - r)

def Dq_bounds(k, J=12):  # D/pi
    s = F(0); last = None
    for j in range(J + 1):
        last = k ** (2 * j) / (2 * 4 ** j * factorial(j) * factorial(j + 1))
        s += last
    r = k * k / 8
    return s, s + last * r / (1 - r)

def tv_bounds(klo, khi):
    # TV is increasing in k (d/dk E_k[sign x] = Cov_k(sign x, x) >= 0), so
    # lower bound uses klo, upper bound uses khi.
    nlo, _ = N_bounds(klo); _, dhi = Dq_bounds(klo)
    _, nhi = N_bounds(khi); dlo, _ = Dq_bounds(khi)
    return nlo / (dhi * PI_HI), nhi / (dlo * PI_LO)

def show(x, up):
    # 12-digit decimal, rounded down (up=False) or up (up=True)
    q = x * 10 ** 12
    n = q.numerator // q.denominator
    if up and n != q: n += 1
    return "%d.%012d" % (n // 10 ** 12, n % 10 ** 12)

k = F(13103, 100000)
lo, hi = tv_bounds(k, k)
print("beta = 0.13103: 18*TV in [%s, %s]" % (show(18 * lo, False), show(18 * hi, True)))
print("certified 18*TV < 1 at beta = 0.13103:", 18 * hi < 1)

for num, den, name in ((131031, 10**6, "0.131031"), (13104, 10**5, "0.13104")):
    k2 = F(num, den)
    lo2, hi2 = tv_bounds(k2, k2)
    print("beta = %s: 18*TV in [%s, %s]" % (name, show(18 * lo2, False), show(18 * hi2, True)))
    print("certified 18*TV > 1 at beta = %s:" % name, 18 * lo2 > 1)

# pi/24 enclosed in [PI_LO/24, PI_HI/24]
lo3, hi3 = tv_bounds(PI_LO / 24, PI_HI / 24)
print("beta = pi/24  : 18*TV in [%s, %s]" % (show(18 * lo3, False), show(18 * hi3, True)))
print("certified 18*TV < 1 at beta = pi/24 (antipodal pair):", 18 * hi3 < 1)

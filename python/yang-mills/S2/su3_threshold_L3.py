# L3 certificate: single-link Dobrushin row sum for 4D SU(3) Wilson LGT,
# weight exp((beta/3) sum_p Re tr U_p).  Exact rational arithmetic, standard library only,
# deterministic output, no timing.
#
# Proved bound (l3_post.md): row sum <= R(beta) := 9*beta*sqrt(B(beta)), where
#   B(beta) = 1/6 + beta/6 + (9/8) beta^2 g(6 beta),   g(x) = (e^x - 1 - x)/x^2 = sum_{k>=2} x^(k-2)/k!.
# Dobrushin's condition holds iff R < 1, i.e. iff P(beta) := 81 beta^2 B(beta) < 1.
# P is increasing in beta >= 0 (every term is), so P(b0) < 1 gives the condition on [0, b0].
from fractions import Fraction as F

def exp_bounds(x, K=40):
    # 0 < x < 2: partial sum is a lower bound; tail <= t_{K+1} / (1 - x/(K+2)).
    s = F(0); t = F(1)
    for k in range(K + 1):
        if k > 0:
            t = t * x / k
        s += t
    t_next = t * x / (K + 1)
    return s, s + t_next / (1 - x / (K + 2))

def P_bounds(b):
    x = 6 * b
    elo, ehi = exp_bounds(x)
    glo, ghi = (elo - 1 - x) / (x * x), (ehi - 1 - x) / (x * x)
    Blo = F(1, 6) + b / 6 + F(9, 8) * b * b * glo
    Bhi = F(1, 6) + b / 6 + F(9, 8) * b * b * ghi
    return 81 * b * b * Blo, 81 * b * b * Bhi

def dec(q, up):
    n = (q.numerator * 10**9) // q.denominator
    if up and n * q.denominator != q.numerator * 10**9:
        n += 1
    return "%d.%09d" % (n // 10**9, n % 10**9)

print("SU(3) single-link Dobrushin, bound P(beta) = 81 beta^2 B(beta) = (row-sum bound)^2")
for name, b in (("3/16 (SZZ, beta_prior)", F(3, 16)), ("0.2", F(2, 10)),
                ("0.2224", F(2224, 10000)), ("0.2225", F(2225, 10000))):
    lo, hi = P_bounds(b)
    print("beta = %-24s P in [%s, %s]   P < 1 certified: %s   P > 1 certified: %s" % (
          name, dec(lo, False), dec(hi, True), hi < 1, lo > 1))
lo, hi = P_bounds(F(2224, 10000))
print("certified: row sum < 1 for all 0 <= beta <= 0.2224:", hi < 1)
print("(at beta = 0.2225 this bound exceeds 1: the method's limit, not a statement about the criterion)")

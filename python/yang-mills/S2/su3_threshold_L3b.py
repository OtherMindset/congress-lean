# L3b certificate: improved single-link Dobrushin bound for 4D SU(3) Wilson LGT,
# weight exp((beta/3) sum_p Re tr U_p).  Rigorous interval arithmetic (mpmath.iv, outward rounding),
# deterministic, no timing.  Proof of every inequality: l3b_post.md.
#
# For a unit D (|D|_HS = 1) and a tilt theta with r = |theta|_HS^2 <= 12 beta^2, tau = ||theta||_op <= min(2 beta, sqrt r),
# rho = Re tr(theta^* D) in [0, sqrt r] (w.l.o.g.), H = sqrt(3 r) >= |Re tr(U theta)|:
#   Var_theta(Re tr UD) <= F := Snum/Zlo - (max(0, mnum)/Zup)^2, with
#   Snum = 1/6 + tau/12 + Q g(H),  Q = 5 rho^2/96 + r/32,  g(H) = sum_{k>=2} H^(k-2)/k!,
#   Zlo  = 1 + r/12 - tau^3/24,
#   mnum = rho/6 - sqrt(3) tau^2/24 + ((3/32) rho r - tau^2 sqrt(r)/32)/6 - t4(H) sqrt(Q r/6),
#   Zup  = 1 + r/12 + tau^3/24 + (r/6) t4(H),  t4(H) = sum_{k>=4} H^(k-2)/k!.
# tau = min(2 beta, sqrt r) is used; every term is bounded at its own worst cell endpoint.  The row sum is <= 9 beta sqrt(sup F).
# The box [0,1]^2 of (u, v), r = 12 beta^2 u, rho = sqrt(r) v, is covered by an N x N grid; on each cell
# every term is replaced by its worst endpoint (each term is monotone in r and in rho; see l3b_post.md).
from math import factorial
from mpmath import iv, mpf

iv.prec = 80

def series_hi(H, start):
    # upper bound of sum_{k>=start} H^(k-2)/k! for 0 <= H <= 2 (41 terms + geometric tail)
    t = H ** (start - 2) / factorial(start)
    s = t
    K = start + 40
    for k in range(start + 1, K + 1):
        t = t * H / k
        s = s + t
    tail = t * H / (K + 1) / (1 - H / (K + 2))
    return (s + tail).b

def sup_F(beta, N):
    beta = iv.mpf(beta)
    rmax = 12 * beta ** 2
    s3 = iv.sqrt(3)
    worst = None
    for i in range(N):
        r_lo = rmax * i / N
        r_hi = rmax * (i + 1) / N
        sr_lo, sr_hi = iv.sqrt(r_lo), iv.sqrt(r_hi)
        tau_hi = iv.mpf(min((2 * beta).b, sr_hi.b))      # tau <= min(2 beta, sqrt r)
        H_hi = iv.sqrt(3 * r_hi)
        g_hi = iv.mpf(series_hi(H_hi, 2))
        t4_hi = iv.mpf(series_hi(H_hi, 4))
        Zlo = (1 + r_lo / 12 - tau_hi ** 3 / 24).a
        Zup = (1 + r_hi / 12 + tau_hi ** 3 / 24 + (r_hi / 6) * t4_hi).b
        for j in range(N):
            rho_lo = sr_lo * j / N
            rho_hi = sr_hi * (j + 1) / N
            Q_hi = 5 * rho_hi ** 2 / 96 + r_hi / 32
            S = (iv.mpf(1) / 6 + tau_hi / 12 + Q_hi * g_hi) / Zlo
            mnum = (rho_lo / 6 - s3 * tau_hi ** 2 / 24 + ((iv.mpf(3) / 32) * rho_lo * r_lo - tau_hi ** 2 * sr_hi / 32) / 6
                    - t4_hi * iv.sqrt(Q_hi * r_hi / 6)).a
            if mnum > 0:
                m_lo = (iv.mpf(mnum) / Zup).a
                Fup = (S - iv.mpf(m_lo) ** 2).b
            else:
                Fup = S.b
            if worst is None or Fup > worst:
                worst = Fup
    return worst

for name, b, N in (("0.2224 (l3 result)", "0.2224", 60), ("0.2328", "0.2328", 480)):
    Fsup = sup_F(b, N)
    P = (81 * iv.mpf(b) ** 2 * iv.mpf(Fsup)).b
    msg = "beta = {:<20s} grid {}x{}: sup F <= {} ; (row-sum bound)^2 = 81 beta^2 sup F <= {} ; < 1: {}"
    print(msg.format(name, N, N, iv.nstr(iv.mpf(Fsup), 10), iv.nstr(iv.mpf(P), 10), P < 1))

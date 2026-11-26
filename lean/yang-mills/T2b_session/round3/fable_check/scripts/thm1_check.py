# Check of Theorem 1 (zero-mode Bogoliubov inequality) on d-regular graphs with uniform coupling J:
#   c = 2a - J d,  Var(G0) = 1 + chi mH2 + 12 b (-d_a m2),  Var(Y^2) Var(G0) >= 4 m2^2,
#   1 = c chi + 4 b chi3,   chi mH2 - 1 = 4 b sum_x |u4(0,0,0,x)|,
#   (1.2): 12 b (-d_a m2) >= 2|B|/(2-|B|) - (chi mH2 - 1).
# (i) brute-force quadrature on K2 (d=1), K3 (d=2), K4 (d=3) computing G0 directly;
# (ii) exact transfer matrix on rings N = 4..24 (d=2).
import numpy as np, itertools, sys
from numpy.polynomial.legendre import leggauss
from ring_exact import obs

def brute(a, b, J, N, n):
    d = N - 1  # complete graph K_N
    R = 1.0
    while (a - J * d / 2 * 0 - J * d) * R * R + b * R**4 < 40: R += 0.05
    x, w = leggauss(n); x = R * x; w = R * w
    G = np.meshgrid(*([x] * N), indexing='ij'); W = np.meshgrid(*([w] * N), indexing='ij')
    S = sum(a * g**2 + b * g**4 for g in G) - J * sum(G[i] * G[j] for i, j in itertools.combinations(range(N), 2))
    wt = np.prod(W, axis=0) * np.exp(-(S - S.min())); wt /= wt.sum()
    E = lambda f: (wt * f).sum(); cov = lambda f, g: E(f * g) - E(f) * E(g)
    M = sum(G); Y = M / N; P2 = sum(g**2 for g in G); P3 = sum(g**3 for g in G)
    c = 2 * a - J * d
    G0 = Y * (c * M + 4 * b * P3)
    m2 = E(Y**2); m4 = E(Y**4); chi = N * m2; p2 = E(G[0]**2)
    mH2 = c + 12 * b * p2
    D = cov(Y**2, P2)    # = -d_a m2
    chi3 = E(G[0]**3 * M)
    u4 = [E(G[0]**3 * G[k]) - 3 * p2 * E(G[0] * G[k]) for k in range(N)]
    B = m4 / m2**2 - 3
    out = dict(EG0=E(G0), covY2G0=cov(Y**2, G0), twom2=2 * m2, VG0=cov(G0, G0),
               VG0formula=1 + chi * mH2 + 12 * b * D, CS=cov(Y**2, Y**2) * cov(G0, G0) / (4 * m2**2),
               ibp=c * chi + 4 * b * chi3, defect=chi * mH2 - 1, defect2=-4 * b * sum(u4), u4max=max(u4),
               lhs=12 * b * D, rhs=2 * abs(B) / (2 - abs(B)) - (chi * mH2 - 1), B=B)
    return out

if __name__ == "__main__":
    print("=== brute force, complete graphs (G0 computed directly)")
    for (N, n) in [(2, 400), (3, 140), (4, 48)]:
        for (a, b, J) in [(1.5, 0.05, 1.0), (0.3, 0.5, 1.0), (-2.0, 1.0, 0.5), (-6.0, 1.0, 0.3), (3.0, 0.01, 1.0), (-1.0, 0.2, 1.0)]:
            o = brute(a, b, J, N, n)
            print("N=%d a=%5.2f b=%5.2f J=%.1f | EG0=%.6f Cov(Y2,G0)/2m2=%.6f VG0=%.6f formula=%.6f | CSratio=%.4f | ibp=%.6f | defect=%.5f vs 4b sum|u4|=%.5f max u4=%.2e | 12b(-dam2)=%.5f >= %.5f  B=%.4f"
                  % (N, a, b, J, o['EG0'], o['covY2G0'] / o['twom2'], o['VG0'], o['VG0formula'], o['CS'], o['ibp'], o['defect'], o['defect2'], o['u4max'], o['lhs'], o['rhs'], o['B']))
    print("=== rings (exact transfer matrix), check 1 = c chi + 4 b chi3 and (1.2)")
    worst = 1e9
    for N in [4, 8, 16, 24]:
        for (a, b) in [(1.2, 0.1), (1.0, 0.1), (0.9, 0.1), (0.5, 0.5), (-1.0, 0.5), (-3.0, 0.5), (0.95, 0.02), (0.7, 0.02), (3.0, 0.01), (-6.0, 1.0)]:
            J = 1.0
            o = obs(a, b, J, N)
            c = 2 * a - 2 * J
            mH2 = c + 12 * b * o['phi2']
            ibp = c * o['chi'] + 4 * b * o['chi3']
            lhs = 12 * b * (-o['dam2']); B = abs(o['B'])
            defect = o['chi'] * mH2 - 1
            rhs = 2 * B / (2 - B) - defect
            worst = min(worst, lhs - rhs)
            print("N=%2d a=%5.2f b=%4.2f | ibp=%.6f | |B|=%.4f defect=%.4f | 12b(-dam2)=%.5f  rhs=%.5f  margin=%.2e  (P0-ratio |B|/(12b(-dam2))=%.3f)"
                  % (N, a, b, ibp, B, defect, lhs, rhs, lhs - rhs, B / lhs))
    print("worst margin", worst)

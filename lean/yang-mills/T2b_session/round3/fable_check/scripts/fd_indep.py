# Independent check of (FD_1): m2(a + 4 b kappa m2(a)) <= (1-|B(a)|/3) m2(a); report kappa_min.
# Rings: exact truncated-series transfer matrix (ring_exact.series_trace), not the author's H-extrapolation.
# Curie-Weiss: exact law of M by FFT convolution of the one-site density, reweighted by exp(J M^2/(2N)).
import numpy as np, sys
from scipy.optimize import brentq
import ring_exact as RE
RE.PS = 1
def ring_m24(a, b, J, N, ng=140):
    c, _ = RE.series_trace(a, b, J, N, ng); Z = c[0, 0]
    return 2 * c[2, 0] / Z / N**2, 24 * c[4, 0] / Z / N**4
def cw_m24(a, b, J, N, nz=3001):
    # Hubbard-Stratonovich, but via conditional iid cumulants (independent of the author's moment inversion):
    # nu(z) ~ exp(-N z^2/(2J)) Z1(z)^N; given z sites iid with tilt e^{z phi};
    # E[Y^4|z] = k1^4 + 6 k1^2 k2/N + (4 k1 k3 + 3 k2^2)/N^2 + k4/N^3.
    from numpy.polynomial.legendre import leggauss
    R = 1.0
    while (a - J) * R * R + b * R**4 < 45: R += 0.05
    R *= 1.5
    xg, wg = leggauss(300); x = R * xg; w = R * wg
    def site(z):
        e = -a * x * x - b * x**4 + np.outer(z, x); mx = e.max(1, keepdims=True); p = w * np.exp(e - mx)
        Z = p.sum(1); mom = [(p * x**k).sum(1) / Z for k in range(1, 5)]
        return np.log(Z) + mx[:, 0], mom
    zs = np.linspace(-3 * J * R, 3 * J * R, 20001)
    lz, _ = site(zs); f = N * (-zs**2 / (2 * J) + lz); keep = zs[f - f.max() > -80]
    zs = np.linspace(keep.min(), keep.max(), nz)
    lz, (r1, r2, r3, r4) = site(zs); f = N * (-zs**2 / (2 * J) + lz); wt = np.exp(f - f.max()); wt /= wt.sum()
    k1 = r1; k2 = r2 - r1**2; k3 = r3 - 3 * r2 * r1 + 2 * r1**3; k4 = r4 - 4 * r3 * r1 - 3 * r2**2 + 12 * r2 * r1**2 - 6 * r1**4
    EY2 = k1**2 + k2 / N
    EY4 = k1**4 + 6 * k1**2 * k2 / N + (4 * k1 * k3 + 3 * k2**2) / N**2 + k4 / N**3
    return (wt * EY2).sum(), (wt * EY4).sum()
def kmin(fn, a, b, J, N):
    m2, m4 = fn(a, b, J, N); tgt = m4 / (3 * m2); B = m4 / m2**2 - 3
    g = lambda k: fn(a + 4 * b * k * m2, b, J, N)[0] - tgt
    hi = 1.0
    while g(hi) > 0:
        hi *= 2
        if hi > 64: return np.inf, B
    return brentq(g, 1e-9, hi, xtol=1e-5), B
if __name__ == "__main__":
    which = sys.argv[1]
    worst = 0
    if which == "ring":
        for b in [0.5, 0.1, 0.02]:
            for a in [1.2, 1.0, 0.9, 0.7, 0.5, 0.0, -1.0, -3.0]:
                for N in [4, 16]:
                    k, B = kmin(ring_m24, a, b, 1.0, N); worst = max(worst, k)
                    print("ring a=%5.2f b=%4.2f N=%2d kmin=%.4f B=%.4f" % (a, b, N, k, B), flush=True)
    else:
        # CW in the author's normalisation: J=4, critical a from J<phi^2>_1site = 1
        from mpmath import quad, exp, inf, findroot, mpf
        for b in [1.0, 0.1, 0.02]:
            J = 4.0
            crit = lambda a: J * float(quad(lambda x: x * x * exp(-a * x * x - b * x**4), [-inf, 0, inf]) / quad(lambda x: exp(-a * x * x - b * x**4), [-inf, 0, inf])) - 1
            ac = brentq(crit, -5, J)
            for N in [64, 1024, 16384]:
                for da in [-0.5, -0.2, -0.05, 0, 0.05, 0.2, 0.5, 2.0]:
                    a = ac + da * max(b, 0.05)**0.5
                    k, B = kmin(lambda a_, b_, J_, N_: cw_m24(a_, b_, J_, N_), a, b, J, N); worst = max(worst, k)
                    print("CW b=%4.2f a_c=%.4f N=%4d a=%.4f kmin=%.4f B=%.4f" % (b, ac, N, a, k, B), flush=True)
    print("worst kmin", worst)

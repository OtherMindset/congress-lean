# (FD_1) kappa_min at near-Gaussian ring points (small b, various masses incl. near-massless), exact transfer matrix.
from fd_indep import kmin, ring_m24
for b in [0.01, 0.001]:
    for a in [1.005, 1.02, 1.1, 1.5, 3.0, 10.0]:
        for N in [2, 4, 16]:
            try:
                k, B = kmin(ring_m24, a, b, 1.0, N)
                print("ring b=%g a=%.3f N=%2d kmin=%.5f B=%.3e" % (b, a, N, k, B), flush=True)
            except Exception as e:
                print("ring b=%g a=%.3f N=%2d ERR %s" % (b, a, N, e), flush=True)

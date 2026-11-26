"""At the parameters where (A) fails, check R(H) = <phi0;phi0^2>/<phi0> monotone for the ORIGINAL phi^4 system
(weight exp(sum J_xy phi_x phi_y + H sum phi - sum (a_x phi^2 + b phi^4))), 3-site path 1-0-2.
Mapping: q-system site weight e^{-(a+3b t^2) q^2 - b q^4/2}, couplings J, field h_q = sqrt2 H; t = 0 gives a_x = a."""
import numpy as np
def R_of(a, b, J01, J02, H, G=181, L=9.0):
    x = np.linspace(-L, L, G); P0, P1, P2 = np.meshgrid(x, x, x, indexing='ij')
    S = J01*P0*P1 + J02*P0*P2 + H*(P0+P1+P2) - sum(a[i]*P**2 + b*P**4 for i, P in enumerate((P0, P1, P2)))
    w = np.exp(S-S.max()); w /= w.sum(); E = lambda F: (w*F).sum()
    m = E(P0); return (E(P0**3) - m*E(P0**2))/m
cases = {"mine (A fails +1.7%)": ((1.057,)*3, 0.052, 0.46, 0.42, 0.0201/np.sqrt(2)),
         "Sonnet (A fails 3.2%)": ((1.839, 2.054, 2.043), 0.162, 0.684, 1.007, 0.031/np.sqrt(2))}
for name, (a, b, J01, J02, H0) in cases.items():
    L = 9.0 if b > 0.1 else 12.0
    Hs = H0*np.array([0.25, 0.5, 1, 2, 4, 8, 32, 128])
    Rs = [R_of(a, b, J01, J02, H, L=L) for H in Hs]
    print(name, "R(H):", np.round(Rs, 7), " monotone nonincreasing:", bool(np.all(np.diff(Rs) <= 1e-9)))

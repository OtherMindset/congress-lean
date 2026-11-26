# Convexity of M_tot in the masses: numerical test (26 Nov 2026)
VERDICT: convexity (local <M;phi_z^2;phi_w^2> >= 0 and uniform d^2M_tot/da^2 >= 0) is FALSE in general, already for ONE site.
Convention: kappa = <M;Phi2;Phi2> = d^2 M_tot/da^2 (Phi2 = sum phi^2). "norm" = kappa/(sd(M) sd(phi_z^2) sd(phi_w^2)).
Scripts: exact.py (grid, rings n=1..4), scan.py, chain.py (infinite 1D chain, transfer operator, 5-pt stencil in a), keff.py, mc3.py (2D MC), cw3.py (CW). Data: scan*.npy, chain_1.npy, mc3.pkl.
## 1. Exact
- 1 site (quadrature, converged 1500..3000 pts): norm = -0.2086 at a=-1.89611722, b=0.33582423, H=1.49270288 (J irrelevant). 27% of 3000 random points in a in[-4,4], b in[.02,2], H in[.01,3] negative; all negative points have a < -0.18 (a>=0: no violation seen in 1 site).
- 2 sites (bond J): a=-1, b=0.1, J=1, H=0.1: <M;phi_1^2;phi_1^2> = -0.00671 norm, <M;phi_1^2;phi_2^2> = -0.00373, uniform -0.00895 (stable for ng=100..800, box 6..9). Scan: 37% local, 34% uniform negative; negatives up to a=1.12 (worst local -0.175 at a=.231,b=.042,J=1.676,H=.473; worst uniform -0.213 at a=-.426,b=.0208,J=.123,H=.489).
- Ring 3 (converged only ng 120->180: a=-1.032,b=.0247,J=2.656,H=.197 gives local -0.0058..-0.0065, uniform -0.0144 (about 2% grid change)). Ring 4 (ng 56 vs 72 agree to 1e-6): a=-3.01847472,b=1.47423873,J=1.02429595,H=1.09801004: ALL local cumulants and the uniform one negative: min local -0.1008, uniform -0.1826. Also a=-2.1415,b=.6288,J=.893,H=.6278: local -0.0851, unif -0.1534; a=-1.6104,b=.4416,J=.197,H=2.156: -0.0763 / -0.0948.
- Caveat: scan fractions for n=3,4 (ng=70,36) are contaminated by grid errors at small b / large J (some spurious values like -2.7); only the converged points above are claimed. Positivity is not restored by small H: negatives occur at H=0.01.
## 2. 1D chain (infinite, transfer operator, ng=200, converged to 1e-12 in ng; stencil step 0.04->0.02 changes 0.2%)
- 300 random points: 42% have d^2 m/da^2 < 0 (per site = kappa/N); negatives up to a=2.17. Worst: a=0.35376, b=0.11172, J=1.28290, H=0.02120: d^2m/da^2=-14.1 (dm/da=-2.29, m=1.82), ratio -6.2.
- K_eff (uniform shift secant/tangent, Delta in {.03,.1,.3,1,3}): K>1 at 30% of single-site and 45% of chain samples; max 1.67 (1 site, a=-2.71,b=.0226,H=.409, Delta=3) and 2.53 (chain a=-3.14,b=.865,J=2.316,H=.0178, Delta=3); maxima sit at the Delta=3 edge of the grid (sup over Delta not located). Small-Delta K approx 1 +- mild; K>1 is generic wherever m(a) has an inflection (sigmoidal drop = concave start).
## 3. 2D MC (mc/runs, N=L^2, kappa/N = N^2 Cov3(A,B,B), 50-block jackknife; 'rew' = Z2-symmetrised reweighting of the H=0 run to s=H<|M|>_0)
- Direct runs (74 at H>0): 69 negative, 25 below -3 sigma, 0 above +3 (max +2.2 sigma, b=.5,a=.7). Worst -8.7 sigma (b=.1,a=1.69,L=32,H=.00144: -325+-37).
- Reweighted (76): 75 negative, 63 below -3 sigma, none positive significant; worst -26.7 sigma (b=.02,a=1.92,L=32,s=1: -1484+-56).
- Magnitude grows with proximity to critical point and L: b=.02,a=1.92: -1484 (L32), -3792+-224 (L64) at s=1; b=.5,a=.88: -59 (L32), -187 (L64) ; b=.1,a=1.69: -264, -557. Deep points (b=.5,a=.7) -2.8+-0.5 at s=1. L=128 (b=.1,a=1.65) consistent with L64 (-44+-37) but not significant. Negative at s=0.3,1,3 alike.
## 4. Curie-Weiss (exact HS, J=4, h in 1e-6..1 24 points, d^2m/da^2 per site)
- a=1.9,b=.02: negative at 24/24 h, N=64,256,1024: worst -126 (N=64), -104 (256), -96.5 (1024) at h~N^-1; ratio kappa/|dm/da| about -9.
- a=1.5,b=.1: 24/24 negative, worst -3.94,-3.95,-3.86 (ratio -1.8). a=0,b=.5: 24/24 negative, worst -0.236,-0.249,-0.250.
- control a=1,b=.1,J=2 (disordered): N=64 all 24 h positive (kappa/N>=5e-5). (N=256,1024 not finished: timeout.)

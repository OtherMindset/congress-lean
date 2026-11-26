# Independent check of /home/claude/t2b/fd/PROOF.md (Opus referee, 26 Nov 2026)

Recorded by the lead from the referee's final message (the referee's file write was refused). Scripts and outputs: `scripts/` (ring.py, skeleton_pointwise.py, thmA_indep.py, thmA_small.py, corB_constants.py, ising_indep.py, ir_ring.py, each with .out). Moments and -d_a chi computed exactly; match mpmath on one site to 1e-15.

All six claims CORRECT, minor fixes only.

1. (S1)/(S2), skeleton consequences: CORRECT. Skeleton constant 24b holds pointwise for all (x1..x4) on 1 and 2 sites, the triangle and rings N=4,6, b from 2 to 0.001; worst ratio 0.9990 at (0,0,0,0), -> 1 as b -> 0 (24 sharp); u4 <= 0. BFS steps verified (g-identity, FKG for |phi| via MTP2 from GKS II, 1-e^{-u} <= u, split identity). Summed forms on 141 ring cases: S1 <= 0.9941, S2 ratio >= 1.00001.
2. Bubble monotonicity: CORRECT (G >= 0 by GKS I, d_a G(0,z) <= 0 by GKS II, uniform mass increase).
3. Theorem A: CORRECT. delta = 4b kappa m2 is Fable's lattice shift (mu' = mu + 8 kappa lambda M_L^2); theta(u) <= theta(a) on the interval; K(1-8x) >= 1 algebra right; FD_2 threshold theta* = 0.3486; FD_3 at theta = 1/2 exact. 118 ring + 146 tiny-graph cases, 0 violations; worst kappa_min 0.9967 vs kappa_A 1.0026. Near theta = 1 the bound is loose (kappa_A ~ 100-290 vs kappa_min ~ 0.6; S2 off by up to 65x), not an error.
4. Corollary B: CORRECT. Constants 13.7329 and 0.28251 (4 zeta(2) beta(2) = 6.02681); IR-limit profiles give theta/Theta <= 1 - 1e-11; Gaussian test Theta/theta ~ 14.4. Even side needed (reflection positivity), correctly required.
5. Proposition C: CORRECT; constant 1.5 ln 3 = 1.6479. Monotonicity hypothesis fails in the disordered phase (confirmed).
6. Numerics reproduced: ring values to 4 digits; 2D Ising-limit tori (L=4 enumeration, L=6 transfer matrix) match.

Fixes: rename Prop C's G (clashes with two-point function); state (P0_kappa) in lattice and continuum form (K = 24 kappa lambda); NOTES "kappa_min <= 0.331" should read "<= 0.334, -> 1/3" (L=4, beta=0.01 gives 0.3337); label "(I1),(I2) hold for O(n)" unverified; add a line on the FKG/MTP2 step; the author's script has an unused extra kappa_A branch not in PROOF.md (never binds).

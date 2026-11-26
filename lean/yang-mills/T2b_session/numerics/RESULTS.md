# T2b numerics: results summary (scripts in this directory; raw data in *.json / *.log)
Normalisation: rho = R'/dH<phi0^2>;  Q = 8(1+rho) on vertex-transitive graphs (Q <= 8 <=> rho <= 0). b=1 unless stated.
1. Single site (scan_single.py, scan_single.npz/.log): 82x51 grid in (alpha=a/sqrt b, eta=H b^-1/4), |alpha|<=1e5, eta in [1e-5,1e5];
   float128 + mpmath(>=2 dps cross-check) where cancellation flagged. max rho = -1.49e-10 (alpha=-1e5, eta=1e5). No violation.
2. Rings L=2,3,4,6,10, infinite chain (scan_chain.py): 8820 pts, a in[-20,20], J in[0.05,10], H in[1e-3,100]; no rho>0; closest -1.08e-3 (a=-2,J=10,H=100).
   chain_smallH.py: H down to 1e-4, J up to 16: closest -8.2e-4.  chain_t2b.py (a=2-delta, b in[1e-3,0.1], J=2 per bond): no rho>0, closest -4.1e-3 (delta=0.2,b=1e-3,H=1).
3. Ladders / 3-wide cylinders and 3x3 torus (scan_2d.py, b=1, W=2 and partial W=3): no rho>0 among converged; closest ~ -2.6e-3 (a=-8,J=4,H=30).
   cyl_t2b.py (b small, a=2-delta): Gauss-node discretisation NOT converged (err ~ |rho|) -> no conclusion.
4. Random small graphs n=2..4 (graph_target.py, inhomogeneous J, homogeneous field): 790 converged cases, no rho>0, closest -0.0104.
5. GC (discrete two-level |q|, product weight): FALSE. Witness gc_ising_seed0.json (n=5 tree), 50-digit check gc_verify.py:
   E_pi[1_D] = 0.967992 (h=1e-4) -> 0.973630 (h=0.3). Homogeneous-site witness on a 5-path: gc_homgraph_seed2.json (d/dh = +7.05e-7, 50 digits).
   None found on n<=4 or on rings n=3..6 (7500 cases). Discrete laws are non-GHS (the 0-d target itself fails for generic 2-level laws: discrete_target.py).
6. IC on Ising strips (ising_strip.py): W=2..5, k=1..3 column blocks, beta in[0.05,2], c0 in {0,0.3,1}: no certified violation;
   all float "positives" (beta=0.05 or 2, H=1e-4) are roundoff -- mpmath brute force (ising_mp.py) gives R'<0.
7. LY1 FALSE (ly1.py, ly1_verify.py, ly1_family.py): nu_s(dx) ∝ (x^2+s)e^{-x^2/2}dx, s>=0 (Lee-Yang, positive) has R'>0 for H > H_s
   (s=0: H>1.6, max R'/P' = 0.039 at H=2). Verified by direct quadrature of the density to 15 digits.
   Curie-Weiss block laws N<=1024: max R'/P' ≈ -2/N (small N) -> 0^- ; no violation.
8. Psi-monotonicity (psi_test.py; L=1 validated against direct quadrature to 1e-15): b=1, a=-4, J=0.3: Psi increases (rings 2,3,4,8) --
   consistent with the lead's report that Psi fails for deep double wells at weak coupling. T2b-regime Psi runs not completed.

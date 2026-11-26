# FAILED.md — FD session (26 Nov 2026). Do not repeat. (Fable's F1–F9 not repeated.)

D1. Extending Theorem A past the Ginzburg region. Both inputs fail there, independently (HEUR, scaling):
  a slope bound d_a(1/chi) >= c > 0 is false near any critical point with gamma > 1 (2D Ising gamma = 7/4);
  the tree bound |u4bar| <= 24 b chi^4 overshoots by ~ lambda chi^2/xi^2. Finite-order improvements of the skeleton inequality do not help.

D2. Interpolating the tree bound (has the factor b, no screening) with Aizenman–Graham (screened, no b):
  min(24 b chi^4, C chi^2 (-d_a chi)) <= sqrt of the product still requires -d_a chi >= C chi^2/(6 b kappa^2): loses 1/b (= O1). Dead.

D3. Proposition C route "(P0) + monotonicity of G = |B|/m2 => FD": the monotonicity is false on the disordered side
  (CN rings: G = 1.80, 2.28, 2.57 at a = 3, 2, 1.5, b = 0.5, N = 64; HEUR: G ~ g xi^eta, or 24 lambda chi at tree level, decreases with a).

D4. Zero-mode tilt comparison: write m2(a+delta) = E[Y^2 e^{-delta N Y^2} r(Y)]/E[e^{-delta N Y^2} r(Y)], r(y) = E[e^{-delta sum psi^2} | Y = y].
  A bound m2(a+delta) <= pure tilt would need r nonincreasing in |y|. In the flip regime r is INCREASING in |y| (Y ~ 0 means interfaces,
  sum psi^2 ~ N M_+^2) (HEUR). Wrong direction: the whole drop in the flip regime comes from r, not from the tilt.

D5. Using Thm 1 (Bogoliubov) at shifted masses: it bounds -d_u m2 below by |B(u)| - D(u), so an FD proof needs a LOWER bound on |B| at
  larger mass, i.e. an upper bound on E_w X(a+4bt): the hard direction again. Circular. (Its defect obeys D <= 96 b^2 chi sum_w G(0,w)^3
  by the skeleton inequality — eps-uniform but large in flip regimes.)

D6. Counterexample search: none. Ising-limit 2D tori (kappa_min <= 0.331), rings (<= 0.9967), Fable's CW (<= 0.995). The only place where
  kappa_min approaches 1 is the near-Gaussian limit, where Theorem A proves FD.

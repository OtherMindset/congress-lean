# FD session notes (26 Nov 2026) — two-mass inequality (FD_kappa) for lattice phi^4_2

Verdict: (FD_kappa) is NOT proved in general. PROVED: (FD_kappa) with kappa = 1 + O(theta), uniformly in eps and L, in the tree-level
("bubble") regime theta := 12 lambda ||G_L||_2^2 < 1 (Theorem A), with an explicit verifiable version in terms of chi_L alone (Corollary B).
No counterexample: every exact test has kappa_min < 1.
Labels: PROVED / CN / HEUR / CITED (= CITED-NOT-READ this session).

Read: fable/{PROOF,NOTES,FAILED}.md, fable_check/REPORT.md, paper body.tex §§2,4,7,8, vehl/NOTES.md, r2/B, r2/C, theta2 NOTES.

## 1. Results (details in PROOF.md)
- Theorem A (PROVED from the BFS skeleton inequality + GKS): if theta < 1 then (FD_kappa) holds for kappa >= 1/((1-theta)(1-8x)),
  x = lambda chi_L^2/L^2 <= theta/12. (FD_2) for theta <= 0.34. Sharp as theta -> 0 (kappa -> 1 = first-order saturation).
  Mechanism: tree bound |B| <= 24x plus "1/chi grows at slope >= 2(1-theta)" (skeleton bound on -d_a chi, bubble monotone in the mass).
- Corollary B (PROVED given the infrared bound): theta <= 12 lambda chi_L^2/L^2 + min(13.73 lambda chi_L, 0.2825 lambda L^2).
  So FD holds on {lambda chi_L small and lambda chi_L^2/L^2 small}, eps- and L-uniformly, with explicit constants.
- Proposition C (PROVED, elementary): (P0_kappa) on [a, a+delta] + "|B|/m2 nondecreasing in a" => (FD_{1.65 kappa}). Converse of Fable's Thm 4,
  but the monotonicity hypothesis fails on the disordered side (CN), so only useful in ordered regimes.

## 2. What Theorem A is and is not
- It is O(n)-blind (inputs hold for O(n) phi^4), hence necessarily perturbative: it cannot pass the Ginzburg region lambda chi ~ 1, and it is
  void in every flip regime (theta >= 12x, x = lambda L^2 M_L^4 large) and in the KT phase. Consistent with (O3).
- Complementary to Fable's Thm 1 (zero-mode Bogoliubov): Thm 1 is non-vacuous only on small/near-Gaussian tori; Theorem A covers the
  infinite-volume symmetric phase at weak coupling, where Thm 1 is vacuous.
- Why it stops (HEUR, both ingredients fail near criticality, independently):
  (i) slope of 1/chi -> 0 whenever the susceptibility exponent gamma > 1 (2D Ising gamma = 7/4), so no fixed-gamma slope bound exists;
  (ii) the tree bound overestimates |u4bar| ~ g* chi^2 xi^2 by lambda chi^2/xi^2 -> infinity.
  Near criticality FD itself has large room (drop/|B| ~ lambda xi^{3/4}, HEUR scaling); the loss is in the method, not in FD.

## 3. Numerics (all exact: Gauss–Legendre quadrature + transfer matrix; scripts/)
- ringtm.py: ring transfer matrix, G(0,z), chi, B2, and <M^2>, <M^4> via a Cauchy-circle FFT in H (agrees with Fable's ring.py to 1e-6;
  one-site check to 13 digits).
- thmA_test.py -> thmA_test.out: 108 cases (b = 0.5, 0.1, 0.02, 0.005; N = 4, 16, 64; a from 3 to -1; J = 1).
  (S1) |B|/(24x) in [0.0000, 0.994] (never > 1); (S2) ratio >= 1.000 always; theta < 1 in 59 cases, all with kappa_min <= kappa_A;
  overall worst kappa_min = 0.9967 (b = 0.005, a = 3, near-Gaussian), consistent with kappa = 1 saturation.
- ir_check.py: IR bound Ghat(k)E(k) <= 0.945 on even rings; B2 strictly decreasing in a (GKS).
- ising_limit.py: Ising limit b -> inf of phi^4 (well phi^2 = v, Ising at beta = v): FD_kappa becomes
  (1 - 2 kappa f(beta)) f(beta(1 - 2 kappa f)) <= (1 - |B|/3) f,  f = <(M/N)^2>_Ising. 2D Ising tori L = 4, 6, 8 exact, beta in [0.05, 0.8]:
  kappa_min <= 0.331 everywhere (-> 1/3 at beta -> 0, = one-site deep-well value; minimum ~0.12 near beta_c). The strong-coupling corner has a
  factor-3 margin; the tight corner is weak coupling (kappa -> 1), which is exactly where Theorem A applies. (L = 10 run did not finish.)
- G = |B|/m2 along a (from thmA_test.out, b = 0.5, N = 64): 1.80 (a=3), 2.28 (a=2), 2.57 (a=1.5) ... : decreasing in a on the disordered side.

## 4. Best next step
The open part of FD is now exactly the non-perturbative region: (a) disordered side beyond Ginzburg, where FD is equivalent to the
infinite-volume mass-AG inequality |u4bar| <= 12 kappa b chi^2 (-d_a chi) (lattice units; the b is the whole difficulty, O1/O7); and
(b) flip regime, where FD is equivalent to the eps-uniform Landau/ABF bound M_+^2(mu + 8 kappa lambda M_+^2) <= M_+^2(mu)/3.
Concrete suggestion: run Theorem A at each scale of a renormalisation-group / multiscale scheme (the bubble condition is a "small effective
coupling" condition, lambda_eff chi_eff < 1), i.e. prove FD for a block-spin effective model whose effective lambda chi stays small — this is
where a one-component input (e.g. Ising-class hyperscaling-type bounds g_R <= C, which are false for O(2) in the KT phase) has to enter.

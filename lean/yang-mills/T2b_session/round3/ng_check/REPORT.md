# Referee check of /home/claude/t2b/ng/PROOF.md (Opus, 26 Nov 2026)

Recorded by the lead from the referee's final message (file write refused). Scripts and outputs: `scripts/`, `*_out.txt`.

No mathematical errors; every PROVED item holds under its stated inputs; five items need small fixes.

Numerics (referee's own code): one site, D from the Gamma integral: 3E[1-e^{-D}] = |B| to <= 6e-7 in 10 cases (near-Gaussian to deep wells, |B| up to 1.998); Gamma >= 0; in deep wells D < 0 with prob ~0.22. Two sites (exact walk densities): <M^2>, <M^4> from walks match quadrature to 1e-13; E|t|/chi <= 0.9994. Rings n=3–16: (B.1) holds at 108 points (worst 0.9988); log R = -8b t.t' + Gamma to <= 2e-6; all <phi_x^2;phi_y^2> > 0. Lee–Yang one site (40 zeros, 4 cases): sum alpha^-4 = -kappa4/12 to 2e-6, sum alpha^-2 = kappa2/2 to 2e-3; 3w1^2 <= |B| <= 3w1 in all four (a near-Gaussian case unfinished).

Verdicts:
- A, B.1, B.2: CORRECT.
- B.3: CORRECT; the "cannot follow from the definition of mu_c" clause is HEUR.
- B.4: CORRECT conditional on the cited skeleton form; cap 6/C informative only for C > 3.
- C.1–C.3: CORRECT.
- C.4: CORRECT; add the integrated form (Cauchy–Schwarz: int|B| >= 3c^2/|W|).
- C.5: CORRECT-WITH-FIXES: extend (I2) to h < 0 by evenness; add chi_L(mu) > 0.
- T1 side remark: CORRECT-WITH-FIXES: state (G) uniform in cutoff, convergence in law, sup<:phi^2:> < inf; label conditional.
- D.1, D.3, D.4: CORRECT (D.4 re-derived from paper Thm 4.1(4) at order H^3).
- D.2: overstated/mislabelled: needed is NG on [mu, mu_+] for some mu_+ < mu_c (equivalent only under Mon); HEUR.
- D.5: NS equivalent to the D.1 (limsup along a sequence) form of NG, not the liminf target; weak-coupling sentence HEUR.
Other labels correct.

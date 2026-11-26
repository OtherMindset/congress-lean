# Cross-check of /home/claude/t2b/fable/PROOF.md (Opus referee, 26 Nov 2026)

Recorded by the lead from the referee's final message (the referee's file write was refused). Scripts: `scripts/`; outputs: `*.txt` in this directory.

All four claims: CORRECT, with presentational fixes only.

1. Thm 1 (zero-mode Bogoliubov): CORRECT. IBP, Var G0 = 1 + chi m_H^2 + 12b(-d_a m2), Cauchy–Schwarz, defect identity chi m_H^2 - 1 = -4b sum u4 (exact; Lebowitz fixes sign), continuum conversion to 24 lambda all verified. Side result: m_H^2 >= 1/chi > 0. Checked on complete graphs (2–4 sites) and rings N=4–24 to 6 digits; never fails; near-saturated at the Gaussian point. Fixes: state for any d-regular graph (c = 2a - Jd); author's verify_Z.py prints Var(G0)/2 under the label Var(G0) (PROOF.md itself right); label flip-regime remarks heuristic.
2. One-site results: CORRECT for a/sqrt(b) in [-200, 1000]; ratio in (a) lies in [0.59, 1), sharp at both ends. Fix: cite the general-graph Thm 1 with N=1 or give the direct 3-line proof.
3. FD_kappa => integrated (P0): CORRECT. Uses only monotonicity of m2 in a and continuity of |B| m2; no derivatives, no convexity. Random stress test (4000 cases) never violated (worst ratio 1.63 >= 1). Fix: write out the case delta > a_+ - a_1. Integration loses a factor 2 vs the infinitesimal constant 24 kappa lambda (not an error).
4. BFS pairing formula 1 - |B|/3 = E_w[X(a+4b t)]/X(a): CORRECT. Closed-form (Bessel) local-time density on 2 sites; matches to 10–12 digits (1 site), 8 digits (2 sites), deep wells included; E|t| <= chi. Fix: state the walk-measure convention.

FD_1 evidence reproduced (Curie–Weiss and rings): independent worst kappa_min 0.981 (CW), 0.8285 (rings); kappa_min < 1 at near-Gaussian points; no counterexample. 2D Monte Carlo not re-run.

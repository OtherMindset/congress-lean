# Referee check of v1 results not formalised in Lean (Opus, 26 Nov 2026)

Recorded by the lead from the referee's final message (file write refused). Scripts: `scripts/`.

One real error (Prop 7.2 normalisation); everything else CORRECT or CORRECT-WITH-FIXES; every quoted number reproduced.

- Prop 7.2: CORRECT-WITH-FIXES. Walk measure w_0 has total mass m, not m/H (1 site: 0.1231604 = m; 2 sites: 0.1006659 = m). With m/H, HT <= m^2 is false (Gaussian 1 site: HT = m^2/H). With mass m, (1) and (3) exact on 1–2 sites, HT <= m^2, (2) holds (8bHT^2/(m - H chi) = 1.024 at (2,.02,.5), >= 1 in 8 cases). Fix: "Its total mass is m"; define T_c := eps^2 T.
- (O5): fix. <phi;phi^2;phi^2> = -0.1475 at the quoted point confirmed, but a negative cumulant does not imply K_eff > 1. Direct example: K_eff = 1.383 on one site at (a,b,H) = (-2.71, .0226, .409). Quote that.
- (O4): wording. (d_H R)/R = +0.264 confirmed at the site WITHOUT the extra field, single bond; d_H R / d_H<phi0^2> = +0.279, so only K < 0.279 is refuted.
- (O6): CORRECT. FKG margin -2.8% to -3.5% for J in [0.7,1.0], a ~ 1.8–2.2, quartic 0.162 or 0.081, eta = 0.031, x,y the leaves of path 1–0–2; state the q-weight convention. Psi non-monotone on rings 2–8 (rises from ~0 at u~1.5 to ~0.5 at u~2.6), exact and resolution-stable.
- Thm 7.1 and §7.2: CORRECT (Thm 7.1 vs direct R < 1%; §7.2 identities to 6 digits). Rename the Phi in §7.2 (clashes with the Dini primitive).
- Thm 6.1: CORRECT-WITH-FIXES. Define Phi(s) = int_0^s F/r in (P) (needs Phi(0+) = 0); L must allow L/eps in N (restrict chi, mu_c, (I3) to dyadic/integer L); pressure step needs only d_h p = m, not convexity.
- Cor 6.2: add K > -1; s0, K independent of mu_+.
- §5: C = 8 lambda (K + s0^{2-theta}) needs theta <= 2; "theta > 2 fails at weak coupling" is first-order perturbative: label heuristic.
- Prop 5.3: CORRECT; write psi_delta out explicitly.
- Lee–Yang remark: CORRECT (sympy), threshold 3^{1/4}.
- (P0), K = 3C/s0^{2-theta}: CORRECT to leading order; add validity condition s0^2 |B_L| / M_L^2 << 1; edge m = s0 is worst only for theta < 2.
- Prop 7.3: constants (1-t)^2/3, 1/6 correct; assume (I1) too, or define M_L via liminf over eps. "15% CW" claim not checked.
- Lean statements: Thm 3.1 matches. Thm 5.1 matches; (iii) general case needs 0 < S <= s0. Thm 4.1: Maxwell and (star) proved for translation-invariant couplings (EOM for general symmetric finite graphs); continuum form of (star) and the Wick form of the EOM are not in Lean (lead's note: eom_continuum covers mu_b m + 4 lambda <phi^3> = h; star_nn is the lattice form). Theorem counts 46/65/10 match the source; README lists different counts.

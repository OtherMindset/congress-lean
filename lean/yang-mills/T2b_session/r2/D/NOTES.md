# D notes (literature, novelty, verification) — 26 Nov 2026

Access: arXiv abs/pdf via WebFetch OK; curl to arXiv/semantic scholar/inspire blocked (403); Project Euclid blocked (Incapsula); Google Scholar/ADS robots-blocked. So no citation search possible; only web search + direct reads. Everything below "READ" = read via WebFetch (model summary of PDF text, sometimes OCR).

## 1. Prior art for the open input (M+ > 0 on all mu < mu_c in continuum phi^4_2, or cutoff-uniform ABF/mean-field bound)

READ, verdict = none of these proves it or claims spacing-uniformity:
- BDW arXiv:2504.08606 (v1 only, 11 Apr 2025; no journal ref). Uniqueness up to mu_c. Low-T half not claimed.
- Panagiotis–Veitch 2605.31344 (1 Jun 2026) "Subcritical sharpness for real-valued spin models": general transitive graph, fixed single-site measure (super-Gaussian), exp decay for beta<beta_c via OSSS extension; Thm 6.1 mean-field lower bound for the *random-cluster* density only. No lattice spacing / continuum.
- Gunaratnam–Krachun–Panagiotis–Panis–Severo 2608.18045 "Supercritical sharpness for the random cluster representation...": Z^d, local uniqueness of macroscopic clusters for beta>beta_c, surface-order LD. No spacing, no mean-field bound on m*.
- van Engelenburg–Heeney–Lis 2609.01362 (1 Sep 2026) "Double cluster swapping": sharpness for EMN class on transitive graphs: chi<inf for beta<beta_c and <phi_o>+ >= c(beta-beta_c)/beta (LINEAR, not sqrt), c unspecified, fixed graph; no continuum.
- Abdelghani–Bauerschmidt–Bodineau–Dagallier 2609.08980 (22 Sep 2026) and F.-H. Ho 2609.10528: Ding–Song–Sun inequality m_o(g+h)-m_o(g-h) <= 2 m_o(h) (h>=0) for EMN/GHS class, finite graphs; Cor: Cov_g <= Cov_0. No continuum, no sharpness, no magnetisation lower bound.
- Gunaratnam–Panagiotis–Panis–Severo 2211.00319 (JEMS): lattice, Gibbs-measure structure and m*(beta_c)=0 for d>=3; no continuum statement.
- Chandra–Gunaratnam–Weber 2006.15933 (CMP 2022): continuum phi^4_3 (and 2D remark), surface-order LD for beta > beta_0 large only (Peierls). GJS75 is deep-region only.
- Duch–Hairer–Yi–Zhao 2508.07776: high-T Phi^4_3; Remark 1.5/1.6 credits BDW for phi^4_2 to the critical point; says low-T "would also be interesting".
- 2611.17119 (fractional Phi^4_2 mass gap): high-T only.
- Classical: McBryan–Rosen CMP 51 (1976) (read via Rosen's homepage PDF): show the gap closes at sigma_c; explicitly CANNOT rule out an interval below sigma_c in the single-phase region, or m discontinuous; they *expect* sigma_0 = sigma_c as in 2D Ising. Glimm–Jaffe AIHP 22 (1975) 109 "On the approach to the critical point" define sigma_c^+ and sigma_c^- (the two ends) — the T2b open half is exactly "sigma_c^- = sigma_c^+" in their language. Not resolved in anything I found.
- FFS book (1992) Table 13.x: ABF (12.161)/(12.162) for Ising/GS class; Fröhlich–Sokal (12.156); none lambda-weighted, none continuum.
Verdict: open half NOT FOUND proved or claimed (searched arXiv listings by ID, web, author page of Bauerschmidt (lists nothing 2026), citations of BDW via web search only).

## 2. Novelty
(see final report; details below as derived)

## 3. Verification
(in progress)

## 2. Novelty (searched: EMN 1976, Ellis–Newman 1978, DSS 2107.09243 + 2609.08980/2609.10528, FFS book ch.9-13 (read via WebFetch at offsets 300k-600k), GJ AIHP 1975 x2, McBryan–Rosen 1976; BFS 1982 only via IHES preprint OCR; Project Euclid/Springer blocked)
- one-site R(h): NOT FOUND. Method = EMN-type duplication + MLR; DSS/EMN/Ellis–Newman contain no even-observable ratio statement.
- theta-1 Lemma A: CLOSE TO KNOWN: ABF 1987 characteristics; Dini generalisation + sharpness example not found.
- RW1: CLOSE TO KNOWN. Key step = FFS (11.30) Z(t+t')>=Z(t)Z(t')exp(-2 lambda t.t') (their g=exp(-(lambda/4)phi^4), shift phi^2+2t; identical to 8b t1.t2 here), refs [213,28,97] there; m = H sum A = FFS (12.125). FFS sect 12.4 field inequalities (Fröhlich–Sokal 12.156, ABF 12.161/2) carry no lambda. The lambda-weighted m - h chi bound itself not found.
- Thm 7.1: NOT FOUND.
- B's W1/W2 (HT <= m^2): not found; W2 is sharper than theta-2's HT <= m^2/(1-kappa).
- C's (P0): |u4bar| <= K chi0^2 (-d_mu chi0) = Aizenman–Graham summed form (FFS 12.42, with beta d/dbeta) with d_beta -> -d_mu; already noted in theta-1 STATEMENT Form IV at theta=2.
- C's Paley–Zygmund step: KNOWN in substance: Griffiths 1966 mu_SM >= mu_LRO (Ising), extended by Koma–Tasaki; PZ+Lebowitz variant fine.
- A1/C sect 3 (XY no-go): same result, found independently by A and C.

## 3. Verification
- Lemma A, Lemma B, Thm C: re-derived line by line, correct. CW end-to-end test (lemmaB_cw.py; b=1,J=4,N=256,a0=0.6,theta=1,s0=0.1): conclusion holds (not tight).
- Dini counterexample: correct (equality, chi=inf, M+=0). Gap: only an infinite-volume profile. Fix: h = m exp(mu+psi(m)) with psi smooth, 0 <= m psi' <= F, psi = Phi~ for m >= delta, constant below: finite chi_delta -> inf, (P) holds, m_delta -> m, so M+ = 0 in the limit too.
- RW0-RW3 + corollary K = k0(2-k0)/(1-k0)^2: correct. One site (mpmath, rw1hp.py): ratio 8bHT^2/(m-H chi) = 1.024, 1.023, 1.032, 1.153, 1.515; m_walk = m to 1e-10; T >= S/2. (A float-grid run gave 0.83 at (2,.02,.5): artefact, gone at high precision.) FKG factorisation on 2 sites with J,H>0, 300 random cases: min ratio - 1 = +1.2e-3 (fkg2.py).
- B W1-W4: correct (walk splitting at a local-time point; reversal A_y0=A_0y; mass-shift g(s+r) ~ g_{(r)}). W1 and W2 checked one site (w1.py) to 10 digits.
- B ERROR 1: "L <= K_eff HT/m^2 <= 2" — by (I), L <=> K_eff*HT/m^2 <= 1.
- B ERROR 2: sufficient condition <M;phi^2;phi^2> >= 0 is FALSE in the needed regime: CW (conv.py) d2m/da2 < 0 at h chi0 = 0.3..3 (a0=0.4,0.6), and already at hchi0=0.1 for a0=0.4; one site double wells (-2,1,H=2): -0.0097, (-4,1,1): -0.043. Ising energy-direction analogue false rigorously: finite-volume convexity of m in beta would survive limits, contradicting Yang's M ~ (beta-beta_c)^{1/8}.
- XY transfer of W1-W5: BFS rep is valid for N-component models in a field (FFS ch.10); mass-shift identity needs soft O(2) phi^4; W2 needs <phi^1_0;|phi_z|^2> >= 0 for O(2) (not verified). A1 is for T, not mass. So "K_eff blows up for XY" is HEUR.
- A1 logic: correct (negation of Thm C hypothesis along any sequence).
- C (P0): Taylor algebra correct; it is a leading-order (s0^2 G << 1) necessary/equivalent form at m = s0, not an exact equivalence. PZ step correct.

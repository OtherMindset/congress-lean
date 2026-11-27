# Referee report: final read of the changed mathematics (Zenodo preprint)

Scope: Thm 6.1 + Cor 6.2, Prop 7.2, Thm 8.1, Prop 8.2, Thm 8.3 + infrared corollary; Section 12.4; declarations.tex (AI-use statement); abstract.tex.
Sources: body.tex (64105 bytes, 2026-11-27 18:22), zenodo.pdf (built 18:25; pdftotext matches the source in the passages checked), and the Long Table posts listed in the task, with their threads and ledger entries l-mwzlzy4r-zob2io (8.3) and l-mwzlzvsz-bnlmd9 (7.2). Read-only. Nothing was posted or changed.

## Verdict
No mathematical error. Every proof in scope holds as written, given its cited inputs. The checked corrections were carried over correctly:
- 8.3 now uses Lebowitz for B <= 0.
- The corollary constants are rounded outward.
- 7.2 makes no pointwise-sign claim, and its lower bound comes from (3) and GKS.

The findings below are imprecisions and nits. They are mostly places where the paper says a little more or less than the checked posts, or where Section 12.4 is incomplete.

## 1. Comparison with the checked posts

### Theorem 8.3 (thm:FDbubble, l.373-381) vs post mwziu7xt-7jygdd
Correct:
- Hypothesis theta < 1.
- kappa >= 1/((1-theta)(1-8x)).
- x <= theta/12.
- (FD_2) for theta <= 0.34, a weaker form of the post's 0.3486.
- The continuum forms of theta and x.
- Proof (l.378): B >= -24x from the skeleton inequality, B <= 0 from Lebowitz [Leb74, SG73], hence |B| <= 24x. Then -d_a chi >= 2chi^2(1-12bB_2), with the bubble nonincreasing by GKS, and the slope integration.

The paper states less than the post (it omits FD_3 and kappa_A -> 1). That is fine.

Corollary (l.381): the constants are 13.74 and 0.2826, matching the post.

Findings:
- F1 (imprecision, l.381). The infrared criterion is stated with no proof or sketch, and the kappa consequence is not stated. It is the only result in scope with no argument in the paper.
  Fix: add a 3-line sketch. Parseval gives int G_L^2 = L^-2 sum_k Ghat_c(k)^2. The FSS bound with sin^2(u/2) >= u^2/pi^2 gives Ghat_c(k) <= min(chi_L, pi^2/(4|k|^2)). The cell comparison uses c = 1 + 1/sqrt2. The lattice sum is sum_{n!=0} |n|^-4 = 4 zeta(2) beta(2). Give the exact values (3pi/2)(3/2+sqrt2) = 13.73291... and 3 zeta(2) beta(2)/16 = 0.282507..., rounded outward to 13.74 and 0.2826.
- F2 (nit, l.378). u is not defined in "d_u(1/chi)". Write "for every uniform mass u in [a, a+delta]".

### Proposition 7.2 (prop:walk, l.292-307) vs post mwzircx2-dp977k
Correct:
- Items (1)-(3) match the post.
- The continuum form 8 lambda h T_c^2 is correct.
- The sketch (l.306) uses the factorisation only as an upper bound on the integrand, and says the integrand "need not be nonnegative". No claim of pointwise nonnegativity remains.
- m - H chi >= 0 is obtained from (3) and GKS mass monotonicity. This is valid: the numerator of K_eff is H^-1 times the (W3) quantity, which GKS makes nonnegative, and HT, S > 0.

Findings:
- F3 (imprecision, l.302). The paper says more than the checked post. "(P) with F = C m^theta follows from K_eff <= C' m^(theta-2)" is not in the corrected post mwzircx2, nor in ledger entry l-mwzlzvsz-bnlmd9. The GPT check of the original post said explicitly that it was unchecked.
  I checked it myself and it is correct: m - H chi = 4 K_eff b (HT) S <= 4 C' b m^theta S, using HT <= m^2 and K_eff >= 0. In continuum units 4bS = 8 lambda (-d_mu m), so (P) holds with C = 8 lambda C'.
  Fix: either add this one-line proof, or mark the clause as not cross-checked.
- F4 (imprecision, l.292-302). The post and the ledger state the result for H > 0. The paper does not. At H = 0, K_eff is 0/0.
  Fix: "(uniform field H > 0)" in the proposition.
- F5 (imprecision, l.306). The factorisation is presented as "[FFS92, (11.30)] in our normalisation". The checked proof derives it from FKG for the MTP2 |phi|-marginal (GKS II), and the ledger lists that as a separate input.
  Fix: "which follows from FKG for the |phi|-marginal, which is MTP2 by GKS II (cf. [FFS92, (11.30)])".

### Theorem 6.1 + Corollary 6.2 (l.221-247) vs post mwzfyk6n-7vf6aa
Statements, hypotheses (I1)-(I3), H_F with h_max = 3 s0/chi_{eps,L}(mu_+), and the constants (theta = 2, C = 8(1+K) lambda, giving (mu_c - mu)/(4(1+K) lambda)) all match the post. The proof is correct.
- F6 (nit, l.234). The proof does not verify the hypothesis m(mu_+, h)/h -> chi_0 in (0, inf) of Thm 5.1(b). The post's step (2) does: m is smooth and odd in h on a finite torus.
  Fix: add half a sentence.

### Theorem 8.1 (thm:zeromode, l.334-347) vs post mwzg06k8-2nmi18
Correct:
- The identities Var(G_0) = 1 + chi m_H^2 + 12b(-d_a m_2) and chi m_H^2 - 1 = 4b sum |u4|.
- The continuum conversion: 12 lambda eps^2 * 2 eps^-2 = 24 lambda, and 4 lambda S_L.
- K = 24 lambda in (P0).
- F7 (imprecision, l.330/335). m_H^2 = 2a - 4 + ..., and "1 = (2a-4) chi + ..." needs a 4-regular graph. Section 8 says only "finite vertex-transitive graph". The post works with degree d and c = 2a - d.
  Fix: "4-regular vertex-transitive (the torus with side >= 3)", or write 2a - d.
- F8 (nit). The symbol T is used for sum_x d_x S here and for the walk local time in Section 7. S is used for the action here and for -d_a m in Section 7.

### Proposition 8.2 (prop:FD, l.363-369) vs post mwzg0mj8-bskmht
The statement, the constants 24 kappa b and 48 kappa lambda, and the continuum shift 8 kappa lambda M_L^2 all match. The proof is correct.
- F9 (nit, l.368). "For a >= a_1" should read "for a in [a_1, a_+]". (FD_kappa) is assumed only on the window, while monotonicity is used beyond a_+. The G = 0 case is not handled.
  Fix: one clause.

## 2. Independent rederivation
- Thm 8.3. I rederived (S1)-(S3), the slope integration (the bubble stays below its value at a, by GKS II) and the final algebra: (1 + 8Kx)(1 - 8x) >= 1 iff 8x(K(1 - 8x) - 1) >= 0. Using 8x <= 2 theta/3 gives q(0.34) = 0.5104 >= 1/2, so (FD_2) holds for theta <= 0.34. The exact root is (5 - sqrt13)/4 = 0.3486122.
- Corollary. C = pi^2/4. The B parameter is C L^2/(4 pi^2) = L^2/16. int_{R^2} min(A, D/r^2)^2 = 2 pi A D.
  - (3pi/2)(3/2 + sqrt2) = 13.7329078778 <= 13.74.
  - 4 zeta(2) beta(2) = 6.0268120397. Direct lattice sum to |n_i| <= 3000: 6.0268118, plus a tail of about 3.5e-7.
  - 3 * 6.0268120397/64 = 0.2825068144 <= 0.2826.
  - Both roundings are outward and correct.
  - I also checked the normalisations: theta = 12 lambda ||G_L||^2 and x = lambda chi_L^2/L^2 with chi_L = eps^2 chi, and FSS with beta = 1 for exp(sum phi_x phi_y).
- Prop 7.2, item (2). The integrand is Z(t1)Z(t2) - Z(t1+t2)Z. Z(t1+t2)/Z = e^{-8b<t1,t2>} <E1 E2> with E_t decreasing in |phi|. FKG gives an upper bound of 8b<t1,t2> Z(t1)Z(t2), whatever the sign of the integrand. Integrating, with sum_x tau_x(z) = T, gives 8bHT^2. The lower bound comes from (W3) and m_y^(r) <= m.
  One-site check: m - H chi = H^3 (I0^2 - I1) = H(m^2 - HT), and (W3) gives the same expression.

## 3. Section 12.4, declarations, abstract
Accurate:
- The post ids, and the hard "holds" from both families on 6.1/6.2, 8.1, 8.2 and on both corrected reposts (mwziu7xt, mwzircx2, all rederived).
- The GPT gap on 8.3: B <= 0 missing, constants rounded down.
- The GPT "unsure" on 7.2, with its counterexample, and the statement being unaffected.
- The ledger level: both 7.2 and 8.3 are CONDITIONAL.
- The renumbering note.
- The declarations' list of models: OpenAI (GPT-6 Sol, GPT-6 Astra) and Google (Gemini 4 Argon).

Findings:
- F10 (imprecision, l.509). "now input (I4) of the proof". The paper has no (I4). (I1)-(I3) are the continuum-limit inputs of Section 6, and (I4) is the post's own label.
  Fix: "which the proof now cites".
- F11 (imprecision, l.509). The account is incomplete. The GPT family later superseded its gap check with a hard "holds" on the original post as amended by the answer (mwzi533b-wwrj8g), before the repost was checked. It would also help to give the ids of the gap check (mwzhu97n-c9b9pm) and the answer (mwzhzicp-77nzmz).
  Fix: add one sentence giving these ids.
- F12 (imprecision, l.505). "Each was checked by GPT-6 Astra and by Gemini 4 Argon" is not quite right:
  - Gemini checked only the corrected reposts of 7.2 and 8.3, not the originals.
  - Each GPT check was a GPT-6 Sol first pass plus a GPT-6 Astra second pass, as Section 12.3 says.
  Fix: "by OpenAI models (GPT-6 Sol, then GPT-6 Astra) and by Gemini 4 Argon; for 7.2 and 8.3, Gemini checked the corrected versions".
- F13 (imprecision, l.505). "the statements are those of the present text" is false for 7.2, because the paper adds the (P) clause and omits H > 0 (F3, F4). It is also loose for 8.3, where the post states more (0.3486, FD_3).
  Fix: "the statements agree with the present text except as noted", and note F3/F4.
- F14 (nit, l.510). "a claim in the proof sketch". The false claim was in the posted proof (mwzfz4vz). The answer mwzhziqc says the paper text never stated it. The check also framed itself as "the proposed gap is not confirmed".
  Fix: "in the posted proof".
- F15 (imprecision, l.512). "[the cited inputs] are among those listed below as not read". GKS/Ginibre, FKG/MTP2 for the |phi|-marginal and the lattice-sum identity 4 zeta(2) beta(2) were relied on but are not in the list in Section 12.5.
  Fix: "most of which are listed below; the others (GKS/Ginibre, FKG for the |phi|-marginal, the lattice sum) are standard and were not read either".
- F16 (nit, l.492). Item (b) says the Claude referee found Thm 8.3 "correct, with minor fixes". It does not say that the cross-family check later found two gaps that referee had missed.
  Fix: add a cross-reference to Section 12.4.
- F17 (imprecision, abstract). "whose work was recorded on a public workspace" overstates. Section 12.1 says that only the Lean files and the five results were posted at the Long Table, and the rest is in the public GitHub repository.
  Fix: "recorded in a public repository, with the Lean files and five key results posted and cross-checked on a public workspace".

The AI-use paragraph in declarations.tex is otherwise accurate given Section 12.

No errors found. Severity summary: imprecision F1, F3, F4, F5, F7, F10, F11, F12, F13, F15, F17; nit F2, F6, F8, F9, F14, F16.

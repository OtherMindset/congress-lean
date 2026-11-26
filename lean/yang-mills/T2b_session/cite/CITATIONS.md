# Citation check: steps 7 and 8 of T2b_conditional v2 (26 Nov 2026)

How each source was read:
- **Read (automated fetch, not by eye):** BDW arXiv:2504.08606v1; BD arXiv:2202.02295; Chandra–Gunaratnam–Weber (CGW) arXiv:2006.15933; Gubinelli–Hofmanová arXiv:1810.01700; GRS, Ann. IHP A 25 (1976) 231–334, from the numdam scan (https://www.numdam.org/item/AIHPA_1976__25_3_231_0.pdf). The GRS scan is OCR'd, and several displayed formulas were lost in the OCR.
- **Not read:** BFS CMP 91 (1983) (Project Euclid blocked the fetch; Springer is paywalled); GRS Ann. Math. 101 (1975); the Glimm–Jaffe book; Simon's P(φ)₂ book. For the two books I saw only the tables of contents.

## Table

| Input | Reference | Location | Covers our hypotheses? | Gap |
|---|---|---|---|---|
| 7: χ_{ε,L}→χ_L | BDW 2504.08606 | Proof of Thm 2.9 (§2.7), eqs (2.63)–(2.67): "It is well known that ν_L is the weak limit of ν_{ε,L}"; "(φ,f)² is uniformly integrable under ν_{ε,L} as ε→0, see [9, Section 8]"; "Thus E_{ν_{ε,L}}[(1,φ)²] → E_{ν_L}[(1,φ)²]" | Periodic: yes. All λ>0, all μ: yes, stated with no restriction. h=0 only. Convention: A=−Δ+1, λ/4·φ⁴, μ/2·φ², counterterm a_ε(λ), Wick constants independent of L | They assert it and cite BFS [9] §8, which I could not read. It is the exact statement we need (same χ). |
| 7 | GRS Ann. IHP 1976 | Thm IX.5 (§IX.1, p. 309 ff.): for X = P (periodic) or N, the lattice Schwinger functions S^δ_{X,Λ}(h₁,…,h_r) converge to the continuum ones as δ=1/(2j+1)→0 | Periodic: yes. P semibounded in §IX.1 (no extra restriction stated), so any λ, μ, h. The h_i are bounded, supported in Λ, a.e. continuous (Lemma IX.3); per the fetch, indicators are allowed, so h₁=h₂=1_Λ gives E[(φ,1)²]. Wick ordering is with respect to the periodic lattice covariance at bare mass m₀>0 (L-dependent) | The hypothesis on the h_i was lost in the OCR; check by eye. The proof goes through L^p convergence of e^{−U_δ} plus Hölder. GRS themselves call the periodic case "similar" to Ann. Math. 1975 [29]. |
| 8: ε→0, fixed L | GRS 1976 Thm IX.5 proof; BDW (5.37) | Thm IX.5 proof: e^{−U_δ}→e^{−U} in L^p. BDW (5.37): log E[e^{−V}] = O(L²) via Nelson [47, Lemma V.6, Thm V.7] | Z_δ→Z is the case F=1 of the proof, but it is **not stated** | Small (see below). |
| 8: L→∞ | GRS 1976 | Thm 1.1 and Thm VI.1 (§VI.1, "Convergence of the periodic pressure"): for any semibounded polynomial P, α_P(Λ) → α_∞, the same limit as for D/N/free b.c. | Periodic: yes. Any semibounded P, so the −hφ term (every h∈ℝ) and any λ>0, μ∈ℝ are covered. Continuum only. Wick ordering is with respect to the periodic covariance G^P_Λ at mass m₀ (a variant with free G₀ ordering is in Thm VI.7) | The normalisation of α was lost in the OCR (standard: |Λ|⁻¹ log ∫e^{−U}dφ_C). |
| χ = sup_L χ_L | BDW (1.2) | Definition only. Thm 2.9 assumes χ_L<χ̄. BD §1(iv): χ is decreasing in **μ** (GKS II), with counterterms independent of μ | No monotonicity in L is stated anywhere I read | — |
| μ_c finite | BDW §1 | "It is known that μ_c(λ) ∈ (−∞,∞) for every λ>0, see [10,17]". [17] = Glimm–Jaffe–Spencer, Ann. Math. 100 (1974); [10] = CGW. BD §1(ii)–(iii) cite GJS Bull. AMS 82 (1976) for μ<μ₁ (d=2) | Yes, stated for all λ | CGW prove d=3 and only remark that the analysis "can be simplified" to 2D. The 2D lower bound really rests on GJS (Peierls). Neither was read. |

## Answers

**Step 7** is stated in exactly the form we need: BDW, proof of Thm 2.9, with the same χ_L and periodic tori at any λ>0 and μ. It rests on BFS §8, which I did not read. GRS 1976 Thm IX.5 gives an independent classical source, also periodic. Cite both, and re-check BFS §8 and the IX.5 hypotheses by eye.

**Step 8.** No single reference states the iterated lattice limit of the pressure. Only h-differences are needed: p_{ε,L}(h) − p_{ε,L}(0) = |T_L|⁻¹ log E_{ν_{ε,L}}[e^{h(φ,1)}]. This removes the divergent Gaussian normalisation, and h-independent constants drop out. Then:
- (a) ε→0 at fixed L. This is the GRS IX.5 argument with P including −hφ: L^p convergence of e^{−U_δ+h(φ,1)}. It follows from the proof, though it is not stated as a theorem. A one-paragraph remark suffices.
- (b) L→∞. This is GRS Thm 1.1 / VI.1, applied to α(P_h) − α(P_0).
- **Remaining gap: easy.**

**Wick convention.** Every difference is a μ-shift. Write c' for the Wick constant used by the reference (periodic lattice covariance at mass m₀ for GRS; BDW's L-independent constant for BDW). Then
- :φ⁴:_c = :φ⁴:_{c'} + 6(c'−c):φ²: + const, and :φ²:_c = :φ²:_{c'} + (c'−c);
- so μ ↦ μ − 12λ(c_ε − c') (from μ − 12λc_ε = μ' − 12λc'), plus an h-independent constant in the action.

The size of the shift depends on the reference:
- **GRS (periodic, mass m₀).** c_ε − C^P_{ε,L,m₀}(0,0) → κ + δ_L. Here κ is finite, and δ_L = G^∞_{m₀}(0) − G^P_{L,m₀}(0) = O(e^{−m₀L}) by the method of images (exponentially small, not O(1/L²)). It vanishes as L→∞.
- **Limits along shifted μ.** Passing to the limit with ε- or L-dependent μ uses convexity of the pressure in the :φ²: coupling and locally uniform bounds (Hölder, GRS §VIII.1). This is easy.

**Draft issues found.**
1. c_ε is never defined. The massless infinite-lattice Green function diverges in 2D (infrared), so it must be specified, e.g. c_ε = (−Δ_ε+m₀²)^{-1}(0,0) on εℤ², with m₀>0 fixed and independent of μ.
2. "μ_c as in BDW" needs an explicit map from BDW's convention (λ_BDW = 4λ; μ_BDW = μ − 1 − 12λκ', with κ' the finite limit of c_ε minus BDW's constant). Otherwise "μ_c − μ" in the bound mixes conventions. (Check the factor once BDW's a_ε(λ) is read by eye.)
3. Choosing L_j→∞ needs sup_{L≤L₀} χ_L < ∞ (Fable item 2). I found no source for this. Heuristically χ_L → 0 as L→0. Proving it is moderate: Nelson bounds uniform for L in compacts. Alternatively, restrict L to integers if BDW's sup is over integers (unchecked).

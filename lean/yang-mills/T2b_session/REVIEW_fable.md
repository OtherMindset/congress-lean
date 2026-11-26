# Independent review of "T2b as a conditional theorem" (Claude Fable, 26 Nov 2026)

Verdict: the one-site theorem, Theorem 7.1, the conditioning-on-t identity, identity (★) and its constants, and the ABF step are correct. "Conditional theorem" is a fair description only after three repairs to the statement (items 1–3). Lemma L is the whole difficulty and is untested where the argument uses it.

Labels: WRONG / GAP / OVERCLAIM / FINE.

## 1. WRONG — "L needed only for h ≥ h_min(L), h_min(L) → 0" (T2b_conditional §1; not in the audit)

The per-torus argument uses the PDE exactly at the smallest fields. I re-derived step 6: along dh/dτ = h, dμ/dτ = −a m², the PDE gives d(m/h)/dτ ≥ 0 and dm/dτ ≥ m, so the μ-shift is ≤ a s²/2 and m reaches s at some h* ≤ 2s/X. The characteristic starts at h₁ with m(μ₀,h₁)/h₁ ≥ X/2 and lives in h ∈ [h₁, 2s/X_j], a window that shrinks to 0 as χ → ∞.

- If h_min(L_j) lies above that window, one must start at h_min and needs m_j(μ₀,h_min)/h_min → ∞. That is the exchange of h ↓ 0 with (ε,L) that §2 says is "not needed".
- Fix: state L for all h > 0 (the torus is smooth, so this costs nothing), or require h_min(ε,L) ≤ c/χ_{ε,L}(μ,0).
- Consequence for evidence: L is used on large tori with huge χ, at h ≲ s/χ, μ ∈ [μ₀ − a s²/2, μ₀], i.e. in the finite-volume phase-flipping regime. None of the ~10,000 cases (rings, chains, small graphs) probes this.

## 2. GAP — threshold and the sequence (steps 7, §1)

- Bauerschmidt–Dagallier–Weber (arXiv:2504.08606v1, eqs. 1.2–1.3 as fetched) define χ = sup_L E_{ν_L}[(φ,1)²]/|T_L| on continuum tori and μ_c = inf{μ : χ < ∞}. There is no sup over ε. The draft relates μ_c^♯ only to the Bauerschmidt–Dagallier lattice-uniform threshold.
- Given χ_L = lim_ε χ_{ε,L} at fixed L (standard), μ_c^BDW ≤ μ_c^♯ ≤ μ_c^χ. So the theorem as stated does cover the half BDW call open, but the draft does not say so, and "sharpness" at μ_c^♯ has no matching uniqueness half unless T2a is redone at μ_c^♯.
- "L_j → ∞ may be assumed" is labelled "proved". It needs sup over L ≤ L₀ and small ε of χ_{ε,L} < ∞, uniform in L on compacts, including small L. Plausible, not shown; label it standard-to-check. Without L_j → ∞ the conclusion says nothing about infinite volume.
- Recommended restatement: use BDW's μ_c. For μ₀ < μ_c pick L_j with χ_{L_j} ≥ 2X_j, then ε_j as small as wanted. This gives L_j → ∞, matches the literature's half exactly, and removes the joint-limit problem of item 3.
- Non-vacuity (μ_c > −∞) is from the literature (BDW cite it); say so.

## 3. GAP — step 8 is not "standard modulo two citations"

- The sequence (ε_j, L_j) is dictated by divergence of χ, so the draft needs joint convergence of the periodic Wick-ordered pressure, uniformly in L as ε → 0. I know no reference stating this; classical results are iterated (ε → 0 at fixed volume, then volume → ∞, Guerra–Rosen–Simon). With the restatement in item 2, ε_j is free and iterated limits suffice.
- Lee–Yang / differentiability is not needed. From m_j ≥ 0 and m_j(μ,h) ≥ s for h ≥ 4s/X_j: p_j(h′) − p_j(0) ≥ s(h′ − 4s/X_j), so p(h′) − p(0) ≥ s h′ and ∂_h⁺p(μ,0) ≥ s by convexity alone.
- Define M⁺ := ∂_h⁺p(μ,0) in the statement. The draft says "the continuum plus state has spontaneous magnetisation" without defining it; identifying ∂_h⁺p with the one-point density of a state obtained as h ↓ 0 is a further (standard) step. BDW phrase the open half as two ergodic invariant measures of the SPDE; that is one more step away.

## 4. FINE — one-site theorem (zerod_proof.md §2)

Checked every step: duplication identity and R = 2E[t²q]/E[q]; ∂_q∂_tW = ½[V″(x) − V″(|y|)] ≥ 0 with x ≥ |y| on the positive quadrant; MLR ⇒ g nonincreasing in |q|; g independent of H (field couples to q only); symmetrisation to π_h ∝ q sinh(hq)ρ(q); x coth x increasing ⇒ MLR in h. Correct and complete under the stated hypotheses.

- OVERCLAIM (minor): "constant iff V is quadratic" (draft §3.1). Only "if" is proved.
- Novelty: Step 2 is the Ellis–Monroe–Newman / Sylvester mechanism (q and t negatively associated). The monotonicity of the ratio in H is not of the form ⟨q^A t^B⟩ ≤ ⟨q^A⟩⟨t^B⟩ and I did not find it in a brief search (EMN CMP 46; Ellis–Newman TAMS 1978 came up, neither with this statement). "New as far as we found" is acceptable; "elementary corollary of the EMN duplication" is the honest framing.

## 5. FINE — Theorem 7.1 and the conditioning-on-t identity

- Theorem 7.1: global q ↦ −q symmetry at zero field, translation invariance, tower property, evenness. Correct. Ψ may be negative; harmless.
- ∂_h(R/2) = Cov_{π_h}(t₀², Φ): correct. It does not need quartic V (any even V with ferromagnetic coupling gives N ≥ 0); "quartic" is only needed for the later (A)/(B) analysis.
- Lattice identity "E[t_x²|q] coordinatewise nonincreasing": correct; the write-up should state that log Z_q(r) is also supermodular (GKS II with field), which the MTP2 claim uses.

## 6. FINE — (★), Maxwell, constants, ABF

Re-derived: μ_b m + 4λ⟨φ₀³⟩ = h; Wick shift gives μm + 4λ⟨:φ₀³:⟩ = h; T/m = R + ⟨φ₀²⟩ − 3c_ε; −∂_μm = ½∂_h⟨φ₀²⟩ on the torus (needs c_ε independent of μ, h); hence m − hχ = 4λm²∂_hR + 8λm²(−∂_μm), a = 8(1+K)λ, M² ≥ 2Δ/a = Δ/(4(1+K)λ). Landau check correct. The per-torus argument uses only divergence of χ, no rate, no GHS. The localised Lean version is correctly flagged as missing. K may depend on the μ-window.

Consistency check not in the draft: in the flip regime L reduces to −∂_μ(M⁺)² ≥ 1/(4(1+K)λ) in the ordered phase. One loop at μ → −∞ gives 4λM² = −μ + (3λ/π)log(−2μ/m₀²), so −∂_μ(4λM²) = 1 + 3λ/(π|μ|) > 1: K = 0 is consistent, with margin O(λ/|μ|).

## 7. New numerical evidence (mine; /tmp/rev/cw2.py, not kept in the project)

Curie–Weiss φ⁴ (complete graph, Hubbard–Stratonovich, exact quadrature): (a,b) ∈ {(2,0.1), (2,1), (0.5,1), (−1,1), (1.9,0.02)}, J ∈ {2,…,20}, N ∈ {4,…,1024}, h ∈ [10⁻³, 3], including broken-phase cases with m/h up to 10⁴. R was decreasing in all 125 cases (max dlogR/dlog h between −4·10⁻⁸ and −9·10⁻³). This is the first test in the regime of item 1, but mean-field only. The 2D Monte Carlo must target large tori below μ_c at h ~ 1/χ, not moderate h.

## 8. Internal inconsistencies / stale statements

- numerics/RESULTS.md item 5: conjecture GC is FALSE (50-digit witness, 5-site tree). AUDIT §B1 says GC "appears to be a general theorem" and STATUS lists GC as a supported sufficient condition. Reconcile; the draft rightly omits GC.
- RESULTS item 3: the small-b cylinder runs did not converge. The draft's "2D ladders and 3-wide cylinders" bullet should say b = 1 only.
- "about 10,000 cases": nearly all 1D or ≤ 4 sites.

## 9. Openness and literature wording (§1, §7)

- Supported: BDW v1 says for μ < μ_c "we expect" two ergodic invariant measures, that such results are established on the lattice "but so far not in the continuum limit", and that their result "answers half of the sharpness question". arXiv still lists v1 only (checked today).
- §7 wording is suitably cautious. Add: the μ_c definition quoted from BDW; that non-uniqueness for μ ≪ 0 is classical (Glimm–Jaffe–Spencer), so the open part is the interval up to μ_c; that one web search today found only lattice results (e.g. arXiv:2605.31344, 2501.05353).
- I read BD and BDW through an automated fetch of the PDFs, not by eye; equation numbers should be re-checked.

## 10. Overall grade and route

- Fair description: "an exact reduction of continuum φ⁴₂ sharpness (with mean-field bound) to one lattice inequality, plus a proof of that inequality at one site". The reduction is real and clean; Lemma L is the entire problem. All classical tools (GKS/GHS/Lebowitz/FKG/Lee–Yang/convexity) are shown insufficient by the team's own counterexamples, and no mechanism for d > 0 exists. Value if delivered: high (completes sharpness for a continuum QFT, publishable at CMP/PTRF level). Distance: far; I would not call it close. "Target, not result" is the right grade.
- Route the team missed: for qualitative sharpness (M⁺ > 0), L is far stronger than needed. The characteristic argument works for any PDE m ≤ hχ + C m^θ(−∂_μm) with θ > 0, valid only on {m ≤ s₀}: the μ-shift is ≤ C s^θ/θ and M⁺ ≥ (θΔ/C)^{1/θ}. Equivalently ∂_hR ≤ K m^{θ−2}∂_h⟨φ₀²⟩ for small m. This asks for any power gain over the trivial termwise size O(χ/m), not an exact sign saturated at first order in λ, so non-sharp tools (skeleton/BFS bounds, Polchinski-flow estimates as in BD) get a chance. Combine with Theorem 7.1: both ∂_hR and ∂_h⟨φ₀²⟩ = √2⟨q₀t₀Σ_xt_x⟩-type quantities are one-dimensional integrals against u sinh(hu)P₀(du), so the slack can be used integrated in u, which avoids the site-wise objection of AUDIT §B2.
- Before any post: fix items 1–3, run the Monte Carlo in the flip regime, restate with BDW's μ_c.

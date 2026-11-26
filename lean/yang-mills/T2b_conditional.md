# T2b as a conditional theorem — draft for operator review (v2, after Fable review)

26 November 2026. P(φ)₂ direction, Session 13 (lead Claude Opus 5.5; seats Claude Opus 5.5 ×3; helpers Claude Sonnet 5.5; independent review Claude Fable 5.2, `T2b_session/REVIEW_fable.md`).
Nothing here is posted on the Long Table. Nothing here is in Lean except where marked.

v2 changes, following the Fable review:
- Lemma L is now required for all h > 0. v1 said only h ≥ h_min(L) was needed; that was wrong, since the argument uses L at h ~ 1/χ.
- The threshold is now Bauerschmidt–Dagallier–Weber's μ_c, and the volume L is chosen before the spacing ε, so iterated limits suffice.
- M⁺ is defined as ∂_h⁺p(μ,0), and the continuum step uses convexity only.
- Two labels and the evidence statements are corrected.
- The θ-route is added to §6.

## 1. Statement

**Lattice.** Lattice φ⁴₂ on the torus Λ_{ε,L} = εℤ²/Lℤ², with weight exp(Σ_{⟨xy⟩}φ_xφ_y + ε²hΣ_xφ_x − Σ_x(aφ_x² + bφ_x⁴)), where:
- a = 2 + ½ε²μ_bare, b = λε², μ_bare = μ − 12λc_ε;
- c_ε is the Wick constant, independent of μ and h;
- in continuum normalisation the action is ε²Σ[½|∇_εφ|² + ½μ:φ²: + λ:φ⁴: − hφ].

Write m = ⟨φ_0⟩, χ = ∂_h m, R(h) = ⟨φ_0;φ_0²⟩/⟨φ_0⟩, and p_{ε,L}(μ,h) for the pressure.

**Threshold.** μ_c is as in Bauerschmidt–Dagallier–Weber, arXiv:2504.08606v1, eqs. (1.2)–(1.3), on continuum tori: χ(μ) = sup_L E_{ν_L}[(φ,1)²]/|T_L|, and μ_c = inf{μ : χ(μ) < ∞}. There is no sup over ε. μ_c > −∞ is from the literature (BDW cite it). Non-uniqueness for μ ≪ 0 is classical (Glimm–Jaffe–Spencer), so the open part is the interval up to μ_c.

**Lemma L (open).** There is K ≥ 0 (it may depend on a compact μ-window) such that for all small ε, all L, μ in the window and **all h > 0**:
  ∂_h R ≤ K·∂_h⟨φ_0²⟩.
K = 0 means that R is nonincreasing in h. The argument uses L at the smallest fields, h ~ s/χ_{ε,L}, on large tori with huge χ: the finite-volume phase-flipping regime.

**Theorem (conditional on L).** For μ < μ_c, the continuum pressure p(μ,h) = lim_L lim_ε p_{ε,L} (iterated limits) satisfies
  M⁺(μ) := ∂_h⁺p(μ,0) ≥ s for every s with 4(1+K)λs² < μ_c − μ, i.e. M⁺(μ)² ≥ (μ_c − μ)/(4(1+K)λ).
With K = 0 this is exactly the Landau (mean-field) bound.

This is the half of sharpness that BDW leave open. Their introduction says they answer half of the question, and that for μ < μ_c "we expect" two ergodic invariant measures, known on the lattice "but so far not in the continuum limit". This was read through the site (read:r-mwx43hva-v8uye7) and re-checked by the reviewer. Two further steps would turn ∂_h⁺p > 0 into BDW's phrasing (two distinct ergodic invariant measures of the SPDE): identifying ∂_h⁺p with the one-point density of the h ↓ 0 state, and the Gibbs/invariant-measure correspondence. Both are standard in spirit but not done here.

## 2. Proof of the theorem from Lemma L

| Step | Content | Status |
|---|---|---|
| 1 | Equation of motion on the torus: μm + 4λ⟨:φ_0³:⟩ = h, exactly | proved |
| 2 | Identity (★): m − hχ = 4λm²∂_h(⟨:φ_0³:⟩/m) | proved |
| 3 | Maxwell relation on the torus: −∂_μ m = ½∂_h⟨φ_0²⟩ (uses that c_ε is independent of μ, h) | proved |
| 4 | Steps 1–3 combined: m − hχ = 4λm²∂_hR + 8λm²(−∂_μ m). So L ⟺ m ≤ h∂_hm + 8(1+K)λm²(−∂_μ m) | proved; constants re-derived by the reviewer |
| 5 | ABF integration along characteristics | in Lean (PP2ABF.lean) |
| 6 | Per-torus form: if χ_{ε,L}(μ₀,0) ≥ X, then m_{ε,L}(μ,h′) ≥ s whenever 4(1+K)λs² < μ₀ − μ and h′ ≥ 4s/X, uniformly in (ε,L). The characteristic runs through h ∈ [h₁, 2s/X], from m/h₁ ≥ X/2. It uses only divergence of χ, no rate and no GHS. | proved (re-derived by the reviewer); localised version not in Lean |
| 7 | For μ₀ < μ_c: choose L_j → ∞ with χ_{L_j}(μ₀) ≥ 2X_j, X_j → ∞, then ε_j small enough that χ_{ε_j,L_j}(μ₀) ≥ X_j | standard: needs χ_{ε,L} → χ_L as ε → 0 at fixed L, the convergence of the lattice approximation on a fixed torus |
| 8 | Continuum step by convexity only: p_j is convex in h, with m_j = ∂_hp_j ≥ 0, and m_j ≥ s for h ≥ 4s/X_j. So p_j(h′) − p_j(0) ≥ s(h′ − 4s/X_j), hence p(h′) − p(0) ≥ sh′ and ∂_h⁺p(μ,0) ≥ s. No Lee–Yang input is needed. | standard: needs iterated convergence of the Wick-ordered periodic pressure at h ≥ 0 (ε → 0 at fixed L, then L → ∞; Guerra–Rosen–Simon). Citation to be checked. |
| 9 | GKS I/II, GHS for lattice φ⁴ (Ellis–Monroe–Newman) | standard |

**Not needed:**
- the infinite-volume lattice plus state;
- clustering at h > 0;
- rates for χ;
- joint (ε,L) limits;
- Lee–Yang.

**Consistency check** (reviewer). In the ordered phase, L at the flip scale amounts to −∂_μ(M⁺)² ≥ 1/(4(1+K)λ). One loop at μ → −∞ gives −∂_μ(4λM²) = 1 + 3λ/(π|μ|) > 1. So K = 0 is consistent, with margin O(λ/|μ|).

Full audit: `T2b_session/lift/AUDIT_AND_LIFT.md` §A. Note that its A4 threshold μ_c^♯ is superseded by the BDW threshold above.

## 3. What is proved about Lemma L

1. **One site, the whole GHS class** (new as far as we found; the honest framing is an elementary corollary of the Ellis–Monroe–Newman duplication).
   - Hypotheses: V even and C², V″ nondecreasing on [0,∞), ∫e^{c|φ|−V} < ∞ for all c.
   - Then for dμ ∝ e^{−V+Hφ}dφ, R(H) is nonincreasing on H > 0, and constant if V is quadratic.
   - Proof: q = (φ+φ′)/√2, t = (φ−φ′)/√2, so R = 2E[t²q]/E[q]. Then ∂_q∂_tW ≥ 0 on the positive quadrant, so g(q) = E[t²|q] is nonincreasing in |q| and independent of the field. Finally R = 2∫g dπ_h with π_h ∝ q sinh(hq)ρ(q) MLR-increasing in h.
   - Files: `T2b_session/zerod/zerod_proof.md`. Checked line by line by the lead and by the Fable reviewer.
2. **Lattice identities** (any graph, even site weight).
   - R = 2⟨t_0²q_0⟩/⟨q_0⟩.
   - E[t_x²|q] is coordinatewise nonincreasing in |q|. This uses GKS plus MTP2, including supermodularity of log Z_q(r) by GKS II with field.
3. **Theorem 7.1** (torus, translation invariance, uniform field): R/2 = ∫Ψ(u)·u sinh(hu) P₀(du) / ∫u sinh(hu) P₀(du), with Ψ(u) = E₀[Σ_x q_x t_x² | Σ_x q_x = u]/u at zero field. So Ψ nonincreasing implies L with K = 0. Checked by the lead and the reviewer.
4. **Conditioning on t** (any even V, ferromagnetic coupling, uniform field): ∂_h(R/2) = Cov_{π_h}(t_0², Φ), exactly. Checked by the lead and the reviewer.
5. **Equivalent forms of L with K = 0:**
   - C = 8 in the ABF-type bound;
   - m Σ_x u₄(000x) + 2m² Σ_x u₃(00x) ≤ χ·u₃(000);
   - a random-current form (checked to 1e−11 on about 600 instances).

## 4. Evidence for Lemma L

No certified violation was found. Almost all of it is 1D or at most 4 sites:
- one site, over the full parameter range;
- rings of 2–10 sites and the infinite chain, 8,820 points;
- the 1D analogue of the T2b regime (a = 2 − δ, b small), 468 cases;
- random small graphs, 790 cases;
- 2D ladders and 3-wide cylinders, at b = 1 only;
- **Curie–Weiss φ⁴** (complete graph, N up to 1024, exact quadrature; reviewer): 125 cases, including broken-phase cases with m/h up to 10⁴ — the first test in the flip regime, but mean-field only.

At first order in λ, ∂_hR = −48λmχΣ_wG(0w)² + O(λ²) < 0, with C = 8 saturated at first order.

**Not tested:**
- 2D tori in the true T2b regime: the small-b cylinder runs did not converge;
- the phase-flipping regime on large 2D tori below μ_c at h ~ 1/χ, which is where the argument uses L.

The needed test is Monte Carlo in that regime, not at moderate h.

## 5. Why Lemma L is hard: verified obstructions

Each item is a counterexample to a sufficient condition, not to L:
- **Field homogeneity is essential.** L fails for non-uniform fields (+26%), so GKS/FKG/GHS/Lebowitz/EMN alone cannot prove it.
- **Lee–Yang is not enough.** ν ∝ x²e^{−x²/2} has Lee–Yang zeros, yet R increases for H > 3^{1/4} (exact).
- **The action is not convex in the T2b regime**, since ε²μ_bare < 0. So Brascamp–Lieb, Helffer–Sjöstrand and Bakry–Émery do not apply.
- **Weak coupling cannot reach μ_c**, because λ/|μ| = O(1) there.
- **Pointwise and termwise versions fail:** Holley/MTP2, coordinatewise, site-resolved, and the monotone L'Hôpital rule.
- **Ψ fails** for deep double wells and for finite Ising Griffiths–Simon blocks.
- **Conjecture GC is false in general** (50-digit witness on a 5-site tree; the witness is outside the GHS class).
- **(A) is false** on 3 sites (−3.2%), and (B) fails slightly with double-well neighbours.

Full list: `T2b_session/zerod/STATUS.md`. Note that AUDIT §B1's remark that GC "appears to be a general theorem" is superseded by the counterexample.

## 6. Routes to Lemma L, or to something weaker that suffices

1. **The θ-route (reviewer's; derived by hand, not checked by the team).** For qualitative sharpness (M⁺ > 0), L is stronger than needed.
   - The characteristic argument works for any m ≤ hχ + C m^θ(−∂_μm) with θ > 0, holding only on {m ≤ s₀}: the μ-shift is ≤ C s^θ/θ, and M⁺ ≥ (θΔ/C)^{1/θ}.
   - Equivalently ∂_hR ≤ K m^{θ−2}∂_h⟨φ_0²⟩ for small m: any power gain over the trivial size O(χ/m), not an exact sign saturated at first order.
   - Non-sharp tools (skeleton/BFS bounds, Polchinski-flow estimates) then get a chance.
   - With Theorem 7.1 the slack can be used integrated in u, which avoids the site-wise objection.
   - **This is the most promising next step.**
2. **Ψ nonincreasing** at zero field, for single-well strongly coupled φ⁴. On 2 sites it follows from two sub-lemmas, (C1) and (C2).
3. **Cov_{π_h}(t_0², Φ) ≤ 0** directly.
4. **The Ising/Griffiths–Simon route via IC.**
   - |B| ≤ 2 is proved.
   - |B| = 3 reduces to P4↑ along rays (about 1,000 sweeps, false coordinatewise).
   - In the GS limit it becomes κ(δ − 3) nonincreasing.

## 7. Literature checks this session

Sonnet helpers did these; the reviewer re-checked BDW.
- The open half in the continuum: not found proved or claimed, April 2025 to November 2026. arXiv:2504.08606 is still v1 (checked 26 Nov). One web search found only lattice results (e.g. arXiv:2605.31344, 2501.05353). A citation search was not possible.
- Lemma L, identity (★), or an ABF-type φ⁴ inequality with the coupling prefactor: not found.
- T2a priority: the fixed-spacing lattice version is Aizenman–Barsky–Fernández (1987). A cutoff-uniform continuum version was not found. Yang (JFA 1988) and the Glimm–Jaffe book were not opened.
- BD and BDW were read through automated PDF fetches; equation numbers should be re-checked by eye.

## 8. Recommendation

- **Present as:** "an exact reduction of continuum φ⁴₂ sharpness, with the mean-field bound, to one lattice inequality, plus a proof of that inequality at one site".
- **Grade it as a target.** Value if delivered is high (the reviewer suggests CMP/PTRF level). The reviewer judges the distance to delivery as far.
- **Before any post:**
  - check the step-7/8 citations (lattice approximation of the periodic pressure);
  - run a 2D Monte Carlo test of L in the flip regime;
  - get a cross-family check of the one-site theorem, which could then be posted on its own.
- **Next research step:** the θ-route (§6.1).

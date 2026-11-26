# T2b as a conditional theorem — draft for operator review

26 November 2026. P(φ)₂ direction, Session 13 (lead Claude Opus 5.5; seats Claude Opus 5.5 ×3, helpers Claude Sonnet 5.5).
Nothing here is posted on the Long Table. Nothing here is in Lean except where marked.

## 1. Statement

Setting: lattice φ⁴₂ on the torus Λ_{ε,L} = εℤ²/Lℤ². Weight exp(Σ_{⟨xy⟩}φ_xφ_y + ε²hΣ_xφ_x − Σ_x(aφ_x² + bφ_x⁴)), with
- a = 2 + ½ε²μ_bare and b = λε²;
- μ_bare = μ − 12λc_ε, where c_ε is the Wick constant (~ (2π)⁻¹ log ε⁻¹).

This is the continuum normalisation ε²Σ[½|∇_εφ|² + ½μ:φ²: + λ:φ⁴: − hφ].

Write m = ⟨φ_0⟩, χ = ∂_h m, and R(h) = ⟨φ_0;φ_0²⟩/⟨φ_0⟩.

Threshold: **μ_c^♯ := inf{μ : limsup_{ε→0} sup_L χ_{ε,L}(μ, h=0) < ∞}**. This satisfies μ_c^♯ ≤ μ_c^χ, the threshold of Bauerschmidt–Dagallier. Equality holds unless their sup is attained on coarse lattices.

**Lemma L (open).** There is K ≥ 0 such that, for all small ε, all L, μ in compact windows and h ≥ h_min(L), where h_min(L) → 0:
  ∂_h R ≤ K·∂_h⟨φ_0²⟩.
K = 0 means that R is nonincreasing in h.

**Theorem (conditional on L).** For μ < μ_c^♯, the continuum plus state has spontaneous magnetisation
  M⁺(μ)² ≥ (μ_c^♯ − μ) / (4(1+K)λ).
With K = 0 this is exactly the Landau (mean-field) bound. This is the open half of sharpness for continuum φ⁴₂. Bauerschmidt–Dagallier–Weber, arXiv:2504.08606v1 (introduction, lines 136–140, read through the site, read:r-mwx43hva-v8uye7), prove the other half and state this one is open in the continuum.

## 2. Proof of the theorem from Lemma L

| Step | Content | Status |
|---|---|---|
| 1 | Equation of motion on the torus: μm + 4λ⟨:φ_0³:⟩ = h, exactly | proved (integration by parts at one site, translation invariance) |
| 2 | Identity (★): m − hχ = 4λm²∂_h(⟨:φ_0³:⟩/m) | proved |
| 3 | Maxwell relation on the torus: −∂_μ m = ½∂_h⟨φ_0²⟩ | proved |
| 4 | Steps 1–3 combined: m − hχ = 4λm²∂_hR + 8λm²(−∂_μ m). So L ⟺ m ≤ h∂_hm + 8(1+K)λm²(−∂_μ m) | proved |
| 5 | ABF integration along characteristics | in Lean (PP2ABF.lean) |
| 6 | Per-torus form of step 5: if χ_{ε,L}(μ₀,0) ≥ X, then m_{ε,L}(μ,h′) ≥ s whenever 4(1+K)λs² < μ₀ − μ and h′ ≥ 4s/X, uniformly in (ε,L). Uses only divergence of χ, never a rate. | proved; localised version not yet in Lean |
| 7 | Choose a sequence (ε_j, L_j) with ε_j → 0 and χ → ∞ (definition of μ_c^♯; L_j → ∞ may be assumed) | proved |
| 8 | Passage to the continuum at fixed h > 0, then h ↓ 0: Griffiths' convexity lemma (m = ∂_h p, p convex) | standard; needs two citation checks: joint (ε,L) convergence of the Wick-renormalised pressure at h ≠ 0, and continuum Lee–Yang (Simon–Griffiths 1973) |
| 9 | GKS I/II, GHS for lattice φ⁴ (Ellis–Monroe–Newman) | standard |

Not needed: the infinite-volume lattice plus state, clustering at h > 0, rates for χ, any exchange of the limits h ↓ 0 and ε → 0.

Full audit: `T2b_session/lift/AUDIT_AND_LIFT.md` §A.

## 3. What is proved about Lemma L

1. **One site, the whole GHS class (new, as far as we found).** Assume V even and C², V″ nondecreasing on [0,∞), and ∫e^{c|φ|−V} < ∞ for all c. Then for dμ ∝ e^{−V+Hφ}dφ, R(H) is nonincreasing on H > 0 (constant iff V is quadratic). The proof:
   - take two independent copies and set q = (φ+φ′)/√2, t = (φ−φ′)/√2, so R = 2E[t²q]/E[q];
   - ∂_q∂_t W ≥ 0 on the positive quadrant, so g(q) = E[t²|q] is nonincreasing in |q| and does not depend on the field;
   - R = 2∫g dπ_h, where π_h ∝ q·sinh(hq)·ρ(q) on (0,∞) is stochastically increasing in h (since x coth x is increasing).

   No Lee–Yang input is used. File: `T2b_session/zerod/zerod_proof.md`. Checked line by line by the lead.
2. **Lattice identities (any graph, even site weight).** R = 2⟨t_0²q_0⟩/⟨q_0⟩, and E[t_x²|q] is coordinatewise nonincreasing in |q| (GKS plus MTP2).
3. **Theorem 7.1 (torus, translation invariance, uniform field).** The field dependence is handled exactly:
   R/2 = ∫Ψ(u)·u sinh(hu) P₀(du) / ∫u sinh(hu) P₀(du), with Ψ(u) = E₀[Σ_x q_x t_x² | Σ_x q_x = u]/u at zero field.
   So Ψ nonincreasing implies L with K = 0. Checked by the lead.
4. **Conditioning on t (quartic V, any graph, uniform field).** ∂_h(R/2) = Cov_{π_h}(t_0², Φ), an exact identity. Checked by the lead.
5. **Equivalent forms of L with K = 0:**
   - C = 8 in the ABF-type bound;
   - m Σ_x u₄(000x) + 2m² Σ_x u₃(00x) ≤ χ·u₃(000);
   - a random-current form comparing ghost-edge counts (checked to 1e−11 on about 600 instances).

## 4. Evidence for Lemma L

- No certified violation of R nonincreasing under a uniform field, across about 10,000 cases:
  - one site, over the full parameter range;
  - rings of 2–10 sites and the infinite chain (transfer operator, agrees with quadrature to 1e−11), 8,820 points;
  - the 1D analogue of the T2b regime (a = 2 − δ, b small), 468 cases, closest margin about −0.5%;
  - random small graphs, 790 cases;
  - 2D ladders and 3-wide cylinders.
- First order in λ: ∂_hR = −48λmχΣ_wG(0w)² + O(λ²) < 0. C = 8 is saturated at first order, so the margin is O(λ²) around the Gaussian equality case.
- **Not tested:** 2D tori in the true T2b regime. The exact methods did not converge on the available machine; Monte Carlo with reweighting is needed.

## 5. Why Lemma L is hard: verified obstructions

Every one of these is a verified counterexample to a sufficient condition, not to L:
- **Field homogeneity is essential.** L fails for non-uniform fields (2-site φ⁴, +26%), while GKS, FKG, GHS, Lebowitz and EMN all hold for arbitrary nonnegative fields. So no proof can go through those inequalities alone.
- **Lee–Yang is not enough.** ν ∝ x²e^{−x²/2} has Lee–Yang zeros, and R increases for H > 3^{1/4} (exact).
- **Convexity tools do not apply.** The action is not convex in the T2b regime: the Hessian on the constant mode is ε²μ_bare < 0. So Brascamp–Lieb, Helffer–Sjöstrand and Bakry–Émery fail.
- **Weak coupling cannot reach μ_c**, because the transition sits at λ/|μ| = O(1).
- **Pointwise and termwise versions fail:** Holley and MTP2 lemmas; coordinatewise monotonicity; site-resolved splits; the monotone L'Hôpital rule.
- **Ψ is not monotone in general.** It fails for deep double wells at weak coupling and for finite Ising Griffiths–Simon blocks. It holds in every single-well, strongly coupled case tested.
- **FKG after conditioning on t fails.** Inequality (A) is false on 3 sites with homogeneous masses (−3.2%). Inequality (B) fails slightly with double-well neighbours.

Full list: `T2b_session/zerod/STATUS.md`.

## 6. Sharpest open targets

1. **Ψ nonincreasing** at zero field, for single-well, strongly coupled φ⁴ on the torus. On 2 sites, two sub-lemmas suffice:
   - (C1) N⁻¹E[Σt_x² | Q = u] is decreasing;
   - (C2) |T2′| ≤ |T1′|.
2. **Cov_{π_h}(t_0², Φ) ≤ 0** directly. This is L restated, but in a form where only one covariance sign is needed.
3. **The Ising/Griffiths–Simon route:** IC (⟨M_B;M_B²⟩/⟨M_B⟩ nonincreasing along uniform rays).
   - Proved for |B| ≤ 2 (GKS II).
   - For |B| = 3 it reduces to P4↑, which held in about 1,000 sweeps and is false coordinatewise.
   - In the Griffiths–Simon limit it is equivalent to κ(δ − 3) being nonincreasing ("tangling at least as strong as Wick").

## 7. Literature checks done this session (Sonnet helpers; abstracts and PDFs as stated in their reports)

- **The open half of sharpness in the continuum:** not found proved or claimed, April 2025 to November 2026. arXiv:2504.08606 is still at v1. A citation search was not possible.
- **Lemma L, identity (★), or an ABF-type φ⁴ inequality with the coupling prefactor:** not found.
- **T2a priority:** the fixed-spacing lattice version (finite χ implies decay; β_c = β_m) is Aizenman–Barsky–Fernández, J. Stat. Phys. 47 (1987). A cutoff-uniform continuum version was not found. Yang, JFA 77 (1988) and the Glimm–Jaffe book could not be opened.

## 8. Recommendation

- **Present T2b as a conditional theorem:** the statement in §1, the proof in §2, Lemma L as the one open input, with the evidence of §3–4 and the obstructions of §5.
- **Grade it as a target, not as a result.**
- **Before any post,** do two checks: the two citations in step 8, and a 2D Monte Carlo test of L in the true regime.
- **The one-site theorem could be posted on its own** as an attempt or result once it has been checked by another model family.

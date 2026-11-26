# NOTES.md — non-Gaussianity (NG) of the torus magnetisation, φ⁴₂ (26 Nov 2026)

Target: liminf_L (ε → 0 first) ∫_W |B_L(μ)| dμ > 0, W = [μ_−, μ_+], μ_+ < μ_c.
Labels: PROVED / CN / HEUR / CNR. Proofs in PROOF.md; dead routes in FAILED.md; script scripts/check.py
(output scripts/check_out.txt).
Read: paper/body.tex §§2, 6, 7 (+5, 8); TARGETS.md (Rounds 11–12); PP7 README; PP2Lebowitz2 statement of
UniformQuarticNegativity; PP3 posts/R3_BFS_route.md; PP1 posts/D4_tree.md; fable/PROOF.md, fable/NOTES.md,
fable_check/REPORT.md; MC data in mc_eps/binder, mc_eps/an_*.log, fable/mc2d/ANALYSIS.txt, mc/RESULTS.md.

## 0. Verdict
NG is NOT proved. It is a separate hard problem: finite-size hyperscaling for φ⁴₂, uniform in ε, near and below μ_c.
- PROVED: |B_L| = −ū4/(χ_L²L²) is the renormalised coupling at length scale L (PROOF B.2), and
  |B_L| ≤ 24λχ_L²/L² (B.1). So NG forces χ_L ≳ L (B.3): it is strictly stronger than sup_Lχ_L = ∞.
- PROVED: exact walk formula |B| = 3E_{ŵ⊗ŵ}[1 − e^{−(8b t·t′ − Γ)}] (A.1). NG ⟺ "no complete screening" (NS, D.5):
  the direct contact interaction of two independent two-point walks is not cancelled by the energy-mediated
  attraction Γ. At weak coupling this is the BFS skeleton bound; in W it is non-perturbative.
- PROVED (given Lee–Yang, CNR): B = −3Σw_j² over Lee–Yang zeros; B < 0 strictly at every finite cutoff;
  NG ⟺ the first Lee–Yang zero carries a fixed fraction of κ2 (C.4).
- No known theorem gives it. The nearest results (Aizenman's planar bound |U4| ≥ S13S24 for nearest-neighbour 2D
  Ising, ADTW emergent planarity at β_c for finite-range Ising, BFS weak-coupling nontriviality, GJS deep-ordered
  phase transition) are either fixed-lattice and Ising-only, critical-point-only, or perturbative (FAILED.md).
- Every inequality used so far (GKS, Lebowitz, GHS, Lee–Yang, tree bound, Simon–Lieb ≥ 1, Bogoliubov)
  also holds for the Gaussian family with covariance (−Δ + L^{−2})^{−1} on T_L. That family has χ_L = L² → ∞ and
  B_L ≡ 0 (HEUR as an obstruction: it is not a φ⁴ family at fixed μ, but it shows that NG needs a quantitative
  use of λ > 0 at the torus scale, i.e. of the contact term in (A.1)).

## 1. Q1: is the statement plausibly true on W?
- HEUR, strongly supported by CN: yes. For fixed μ < μ_c and L → ∞ we are in the finite-size ordered regime L ≫ ξ(μ),
  and B_L → −2 if sharpness holds. At μ_c itself B_L should tend to the 2D Ising torus value. CNR: Salas–Sokal
  give U* = 1 − m4/(3m2²) ≈ 0.6107, i.e. |B*| ≈ 1.83. W lies strictly below μ_c, so the critical value is never
  needed, only "no dip to 0 as L → ∞".
- Circularity: NG is implied by order. HEUR chain: M⁺ > 0, torus limit points are ± mixtures, ergodic theorem,
  so B_L → −2. And NG + (P0) gives order (paper §7). So sharpness ⟺ NG ∧ (P0), modulo standard steps.
  NG is weaker than order only in that it also holds at criticality.
- In the wrong order of limits it is CNR-true. At fixed ε, lattice sharpness holds for the Griffiths–Simon class
  (ABF 1987, CNR), and translation-invariant Gibbs states are ± mixtures (GPPS, JEMS, CNR for d = 2). So for
  μ < μ_c(ε), lim_L B_{ε,L}(μ) = −2. Also liminf_ε μ_c(ε) ≥ μ_c (HEUR, via (I1) plus torus ≤ C·infinite-volume χ).
  The obstruction is exactly the interchange lim_L lim_ε.
- Small tori (HEUR): as L → 0 the zero mode is a one-site quartic with |a|/√b → 0, so B_L → −0.81 (pure x⁴).
  So |B_L| is O(1) at both ends of L.

## 2. Q2: known bounds and the ratio needed
- The ratio for the zero mode is g_L = |B_L| = −ū4/(χ_L² L²) (B.2). The infinite-volume analogue is
  g_R = −ū4/(χ²ξ²).
- Upper bounds on |u4| (wrong direction for NG): the tree bound / BFS (1.3) (Lean `tree_bound_box`), giving
  |B_L| ≤ 24λχ_L²/L²; Aizenman–Graham (CNR); the Glimm–Jaffe bound g_R ≤ const (CNR).
- Lower bounds:
  (i) The BFS upper skeleton inequality (CNR, CMP 91 (1.4)): u4 ≤ −24λΣΠS·(1 − O(λ·bubble)). It is useful only
      when λ·Bub_L is small. PROVED (B.4): any bound of that form certifies at most |B_L| ≤ 6/C, and in W one
      expects λBub_L → ∞ (HEUR: ordered Bub ≈ M⁴L², critical ~ L^{2−2η}).
  (ii) BFS/GJ weak-coupling nontriviality in d = 2, 3: perturbative, disordered phase, infinite volume.
  (iii) Aizenman 1982 (CNR, via the survey arXiv:2112.04248 eq. (6.7)): for planar 2D Ising,
      |U4(x1..x4)| ≥ ⟨σ1σ3⟩⟨σ2σ4⟩ at square-vertex configurations, for all β. It needs nearest-neighbour planarity.
      Under the Griffiths–Simon construction φ⁴ is not planar, and the "intersection ⇒ connection" probability
      at one site is O(b) → 0. ADTW (arXiv:1801.04960, abstract and theorems read) give emergent planarity only
      at β_c for finite-range Ising; the GS-class extension is a conjecture (survey, Conjecture 1).
  So no lower bound on g_R or g_L is known that is uniform in ε near criticality or on the ordered side
  (we found none).

## 3. Q3: finite-size / one-site / monotonicity
- At fixed physical L: B_L(μ) < 0 strictly (PROOF C.5, given (I2) and a growth input (G)). It is not uniform in L.
  A fixed-L statement can only help together with an RG-type finite-size criterion of the form "|B_L| ≥ g* and
  (not disordered) ⇒ |B_{2L}| ≥ g*". None is known (HEUR; FAILED F7).
- One-site comparison: Fable's one-site |κ4| ≤ 4b m4(m4 − m2²) is an upper bound on |κ4|, so it points the wrong way.
  The one-site lower bound |B| ≥ F(b m2²) has no torus analogue because the zero-mode effective potential is not known.
- Monotonicity of B_L in μ: PROVED on one site (Fable 2b). CN on 2D tori: in every scan of mc_eps/binder and
  fable/mc2d, |B_L| is monotone decreasing in a at fixed L (to within error).
  It helps only downward: (Mon) reduces NG to pointwise NG at each μ′ < μ_c (D.3). Deep-ordered information cannot be
  transported up to μ_+ (D.2).

## 4. Q4: numerics (read only, plus a 1-minute check script)
- mc_eps/binder (|B| = 3U), fixed ε, L = 16…256:
  - ordered side: |B_L| increases with L towards 2. Examples: b = 0.08, a = 1.72: 1.914, 1.975, 1.994 (L = 16, 32, 64);
    b = 0.005, a = 1.9766: 1.948 → 1.984 (L = 128 → 256).
  - disordered side: |B_L| → 0 with L.
  - crossing values: |B| ≈ 1.78 (b = 0.08, a ≈ 1.752) and ≈ 1.80–1.82 (b = 0.02, a ≈ 1.924), close to 1.83 (Ising).
- ε → 0 at a fixed physical point (λL² = 81.9, with a tuned to keep χb ≈ 38): U = 0.624 / 0.629 / 0.636 at
  b = 0.02 / 0.005 / 0.00125 (L = 64 / 128 / 256), so |B| = 1.87 / 1.89 / 1.91 (an_p1.log, an_p3.log). This is stable
  under ε → 0 at fixed physical L (CN).
- Crossing points in continuum units: (2 − a_c)/b = 3.1, 3.79, ≈ 4.42 for b = 0.08, 0.02, 0.005. The increments
  0.69 and 0.63 match the Wick shift 6·log2/(2π) = 0.662 per halving of ε, consistent with μ_c(ε) converging (CN, rough).
- (B.1) checked on all scan points; the largest (|B| − 2σ)/bound is 0.47 (scripts/check.py).
- None of this tests "L → ∞ after ε → 0" near μ_c: the lattice points have correlation length ≲ 40 sites.

## 5. Most promising concrete step
Prove (NS) in a planar form for the continuum walk representation, which is the uniform-in-ε analogue of Aizenman's
square-vertex bound:
 (a) two independent ŵ-walks with endpoints at alternating corners of a square of side ≍ L cross topologically
     with probability ≥ p (planarity of continuous paths);
 (b) given a crossing, D = 8λ∫ℓℓ′ − Γ ≥ δ with probability ≥ p′, uniformly in ε. This is the hard,
     non-perturbative part: an upper bound on energy–energy screening along the crossing;
 (c) for μ < μ_c, a positive fraction of the weight Σ S(x1,x3)S(x2,x4) sits on such configurations at scale L.
     (c) needs χ_L ≳ L (B.3), which itself is not known.
(b) must use one-component structure only if it is also to give (P0). For NG alone, (O3) is no obstruction:
2D XY magnetisation is non-Gaussian too (HEUR).

## Memory-worthy (from this session's reading, not from memory)
- The non-Gaussianity of the T1 limit points (UniformQuarticNegativity in PP2Lebowitz2) can be reduced to a uniform
  sub-Gaussian-order MGF bound (G), with no skeleton inequality needed (PROOF.md §C side remark).

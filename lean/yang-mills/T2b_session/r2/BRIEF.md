# Round 2 brief (shared by all four members) — read first

Goal: prove the one open input of T2b (continuum φ⁴₂ sharpness, the μ < μ_c half), with novelty and elegance.
T2b stays a target until this is proved; do not overclaim.

Required reading (in order):
1. /home/claude/t2b/T2b_conditional.md: v3, §§1–2, 9–13.
2. /home/claude/t2b/theta1/STATEMENT.md and theta1/PROOF.md: the weakened input (P), its five equivalent forms, and the sharpness counterexample.
3. /home/claude/t2b/theta2/NOTES.md: why ABF, termwise inequalities and random walks fail, with quantified losses; RW0–RW3.
4. /home/claude/t2b/theta3/NOTES.md: the one-variable reduction, (Σ_θ), and why two-phase and Polchinski arguments are circular.
5. /home/claude/t2b/zerod/STATUS.md: the proved one-site theorem, Theorem 7.1, and the list of counterexamples.

THE OPEN INPUT
(P): on {m ≤ s₀, 0 < h ≤ 3s₀/χ₀}, uniformly in small ε, all L, and μ in a window,
  m ≤ h∂_h m + F(m)(−∂_μ m),
for some F with ∫₀ F(r)/r dr < ∞ (e.g. F = C m^θ, θ > 0).
Setting: lattice φ⁴₂ on the torus εℤ²/Lℤ², continuum normalisation, uniform field.
Equivalent one-variable form (Σ_θ): N·Cov_{ν_H}(σ(Y), Y) ≥ c₀ m^{−θ}(m − Hχ).

KEY LESSONS (do not repeat these failures)
- Pressure-only properties cannot suffice. θ-1's explicit m satisfies monotonicity, concavity in h and everything else that was listed, yet has M⁺ ≡ 0. A proof must use a property that excludes it.
- Termwise cumulant bounds lose a volume factor in the flip regime: the terms are O(|T|) and cancel to O(1).
- ABF's lattice inequality has constants blind to b, and loses a factor 1/(λε²).
- Random walks lose to screening in the flip regime.
- Large-deviation and two-phase arguments are circular, because they presuppose M₊ > 0.
- Polchinski/log-Sobolev constants degrade as χ → ∞.
- Field homogeneity is essential: the statement fails for non-uniform fields.

EVIDENCE
- 2D Monte Carlo: Lemma L (K = 0) holds with margin ≥ 13% in the flip regime (/home/claude/t2b/mc/RESULTS.md).
- One site: L is proved for the whole GHS/EMN class.

STANDARDS
- Give complete proofs, and label every step PROVED / STANDARD (with a citation you read) / HEURISTIC.
- Check numerically wherever cheap (Curie–Weiss, 1D transfer operator, small lattices; scripts exist in /home/claude/t2b/*).
- The machine has 2 cores shared by four agents: keep runs short.
- Use web search and arXiv freely. Report only what you read.
- Write into your own directory /home/claude/t2b/r2/<X>/.
- Read teammates' NOTES.md files there as they appear.
- Other members: A = thermodynamic structure; B = φ⁴-specific currents; C = exponent and analytic routes; D = literature, novelty and verification.
- If you find a proof of (P) or (Σ_θ), write it to /home/claude/t2b/r2/<X>/PROOF.md immediately, then keep stress-testing it.

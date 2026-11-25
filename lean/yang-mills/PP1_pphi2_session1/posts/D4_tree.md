Dependency plan (D4), P(φ)₂ direction, Session 1, for the model of D3 (weakly coupled λ:φ⁴:₂, lattice-regularised; target `PhiFourTwoWeakCouplingGap` of the D5 file). Status: E = exists as a theorem (where), A = exists only as someone's axiom, M = missing. Estimates in sessions (one session ≈ a 4-hour council); ∥ = can run in parallel in a congress.

T. Target: Zlat converges, limit non-Gaussian, uniform-rate clustering. Then T′ (Hamiltonian form): σ(H) ⊆ {0} ∪ [m, ∞).
N1 Lattice measure well-defined (weight integrable, normalisable). E in pphi2 (InteractingMeasure, Lean 4.30): port to 4.35/our pin. 2 ∥
N2 Lattice free field: covariance, Wick constant c_ε ≈ (2π)⁻¹ log ε⁻¹, decay of the lattice covariance uniform in ε, Dirichlet-decoupled covariances. Partly E (pphi2, gaussian-field; springoxn/pphi2-clean-finite-lattice); decay and decoupling M. 3 ∥
N3 Gaussian integration by parts, Wick theorem, Hermite identities for :φᵏ:. Partly E (pphi2 GaussianHermiteMean). 1 ∥
N4 Local estimates uniform in ε (Nelson-type bound on ∫exp(−λ ε²Σ_Δ :φ⁴:) per unit square, with derivatives). A/M (pphi2's Nelson layer; one Nelson axiom withdrawn as false). 4 ∥
N5 The cluster expansion, convergent for λ < λ₀ uniformly in ε and L. M.
  N5a forest (BKAR) interpolation formula, abstract. M. 3 ∥
  N5b tree/polymer summation with exponential tree decay. M (Kotecký–Preiss in Lean for lattice U(1), Zenodo 20547755). 2 ∥
  N5c per-tree bounds uniform in the UV cutoff: resolvent/vertex bounds, renormalised tadpoles over scales. M. 10–14
  N5d truncated correlations decay at one rate m, with n-point bounds. M. 2
N6 Convergence of Zlat as n → ∞ (Cauchy from N5's uniformity). M. 3
N7 Non-Gaussianity of the limit (first-order u₄ ≠ 0 plus N5 remainder). Partly E on the torus (pphi2, axiom-free by its README). 2 ∥
N8 Uniform clustering of Z from N5d. M. 2
— T done here (≈ 34–38).
N9 Reflection positivity of the lattice measures and of the limit. Partly E/A (pphi2 OS3 files; gaussian_rp_cov_perfect_square is an axiom). 3 ∥
N10 OS Hilbert space and transfer semigroup T(t) = e^{−tH}, self-adjoint, from N9 in 1+1. E in 4D only (P3r0o0, MIT); M in 2D. 4 ∥
N11 Gap from clustering: E (`PP2Gap.semigroup_gap`, this session, D6) + density of the exp(iφ(f)) vectors. 1
N12 Bridge to a d-parametric Wightman interface (MG1 forms in 1+1). M. 2 ∥
— T′ adds ≈ 10.

Total ≈ 44–48 sessions (T alone ≈ 34–38). This is more than about 40, so the operator chooses (summary post). Not trimmed.
Hardest node: N5c, the UV-uniform per-tree bounds. Route in the literature: Rivasseau–Wang arXiv:1104.3443v1 (multiscale loop vertex expansion for φ⁴₂, open); Glimm–Jaffe–Spencer 1974 and Glimm–Jaffe ch. 18 (paywalled). Fallback: Duch–Gubinelli arXiv:2611.17119 for N5–N8, which would replace N5a–N5c by SDE machinery (estimate not made).
Serial spine: N2 → N4 → N5c → N5d → N6/N8. Everything marked ∥ can start at once.

# M5 plan (Fable route review, round 6) — ends at SmallBoundarySum and RegionSusceptibility

Notation: B = physBall n k x l (always a rectangle of box sites, also when cut by the box edge),
C_B = ε⁻²·regOp⁻¹ (free region covariance), regOp B = (dirOp n k m₀).submatrix (↑) (↑)
(already defined as `regionOp` / `regionGreen` in PP2FreeVar2.lean, with `fv2_regionGreen_le_dirGreen`).

Free-field lemmas
- F1 `regOp_posDef`, `dirAction_zeroExt`: dirAction (zeroExt B ψ) = ε² ψ ⬝ᵥ regOp *ᵥ ψ; `regionTwoPt n k m₀ 0 B x y = C_B x y`;
  C_B ≥ 0 entrywise; rectangle equivalence {z // z ∈ physBall} ≃ Fin N₁ × Fin N₂ and sine diagonalisation. 1–2 sessions.
- F2 `exit_le`: for h ≥ 0 with (dirOp m₀ h)(w) ≥ 0 on B: Σ_{u∈B,v∉B} bondJ u v · C_B y u · h v ≤ h y.
  h ≡ 1 gives exit weight b ≤ 1. With h(w) = (cosh a(i−iₓ) + cosh a(j−jₓ))/cosh(a(L+1)), 2cosh a − 2 = ε²m₀², L = ⌊l/ε⌋:
  `free_boundary_le : b(x) ≤ 2 / cosh(κ·l)`, κ = 0.96·min(1, m₀), all n, k, x. 1–2 sessions, low risk.
- F3 `Lp_green`: ε²Σ_y C_B(x,y)^p ≤ K_p(m₀) for p ≤ 8; rough part C_r = ε⁻²Σ_K (1−e^{−tλ_K})/λ_K e_K e_Kᵀ:
  ε²Σ_y C_r(x,y)^p ≤ K_p·t. From `heat1_le`/`heatK_diag_le`, Cauchy–Schwarz off-diagonal, row sum ≤ 1, Hölder, Minkowski in t.
  Also ε²Σ_y C_B(x,y) ≤ m₀⁻². 2 sessions.
- F4 `deltaC_Lp`: 0 ≤ δc(y) := freeVar − C_B(y,y) ≤ K·log(1 + 1/(m₀ d(y))) (largely done: `fv2_wick_defect_le` for the box;
  needs the region version via `fv2_regionGreen_le_dirGreen`-type monotonicity), hence ε²Σ_{y∈B} δc^p ≤ D_p(m₀,l).

Gaussian machinery
- G1 `region_gauss_modes`: normalised density exp(−½ε² ψ·regOp ψ)dψ is the law of ψ = ε⁻¹ Σ_K λ_K^{−1/2} ξ_K e_K,
  ξ ~ Measure.pi (gaussianReal 0 1); per-mode split ξ_K = α_K ξˢ_K + β_K ξʳ_K, α_K² = e^{−tλ_K}. 2 sessions, medium risk.
- G2 chaos: PP2Chaos2 has ‖F‖_{2m+2} ≤ ρ_m^{−d}‖F‖₂; remaining: tail bound, writing V_r as F_c. 1–2 sessions.
- G3 `wick_cov_misordered`: E₀[:φ_y^j:_c :φ_{y'}^k:_c] as explicit polynomial in C(y,y'), δc(y), δc(y') for j,k ≤ 4,
  from `wickPow_add_binomial` and `wickPow_cross_cov`. 1 session.
- G4 `nelson_region`: ∃ N(m₀,l), ∀ n k x: ∫ exp(−2V_B) dμ⁰_B ≤ N, V_B = ε²Σ_{y∈B} wickPow freeVar 4 (ψ y).
  Split c₁ = c_s + δc, c₂ = c_r; smooth part ≥ −6ε²Σ(c_s+δc)²; remainder ‖R_t‖₂² ≤ K t^δ; tails by G2;
  conclude with `lintegral_expSq_neg_le_of_tail`. 3–4 sessions; riskiest. For λ ≤ 1: E e^{−2λV} ≤ max(1,N) by Jensen.
- G5 `Z_lower`: ∫ e^{−λV_B} dμ⁰ ≥ exp(−3λ ε²Σδc²). ½ session.

Interacting chain (BFS (7.5)–(7.7), summed form)
- I1 `double_ibp`: for t : B → ℝ, g := C_B t:
  Σ_u t u · regionTwoPt λ B x u = g x − 12λ ε²Σ_z g(z) C_B(x,z) ⟨:φ_z²:⟩_λ + 16λ² ⟨F₁ F_g⟩_λ,
  F₁ = ε²Σ_z C_B(x,z):φ_z³:, F_g = ε²Σ_z g(z):φ_z³: (two uses of gauss_ibp; (wickPow c k)' = k·wickPow c (k−1)). 1–2 sessions.
  (Check the constants 12, 16 against the λ normalisation of dweight: weight exp(−dirAction/2 − λε²Σ wickPoly).)
- I2 `correction_le`: for 0 ≤ g ≤ Γ, 0 ≤ λ ≤ 1: |last two terms| ≤ λ Γ K(m₀,l), Schwarz in μ⁰. 1–2 sessions.
- Conclusions: boundary t(u) = Σ_{v∉B} bondJ u v ⇒ sum ≤ 2/cosh(κl) + λK; susceptibility t ≡ ε² ⇒ A = m₀⁻²(1+K).

Final: ∀ m₀ > 0, ∃ l ≥ 0, ∃ lam₀ > 0, ∃ A ≥ 0, ∀ lam, 0 ≤ lam → lam < lam₀ →
  SmallBoundarySum m₀ lam l (3/4) ∧ RegionSusceptibility m₀ lam l A.
Parallel: F1→F2; F3; F4; G2; G3; I1. Serial tail: G1 → G4 → I2 → conclusions.

## To-do added after the BFS §7 page-image checks (#mwwsp58f-heli3s, #mwwsvkj2; correction #mwwsz098-qhd5o7)
- SmallBoundarySum is the BOND sum of (7.3). BFS's printed per-site target (7.5) < 1/(4l) gives only bond sum < 1 + δ/l
  (4q boundary sites, 4q+4 crossing bonds). Any route through (7.5) needs a per-site bound with margin, e.g. < 1/[4(l+δ)].
  Our route (PP2Region `free_boundary_le` + PP2M5Final `m5f_boundary_le`) bounds the bond sum directly and does not use (7.5).

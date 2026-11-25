# P(φ)₂ parallel tracks, rounds 1–4 (25 Nov 2026)

Seventeen Lean files from parallel seats (Opus 5.5: medium effort for routine nodes, high for M3; second passes by Sonnet; route reviews by Fable). All build on Lean 4.35.0 / Mathlib 56a00585 with axioms propext, Classical.choice, Quot.sound only. Imports use local module names (`LongTable.PP2Green` etc.); for site posting they must be rewritten to posted `P_<id>` modules.

| File | Node | Content |
|---|---|---|
| PP2Green | M1 | dirOp = ε⁻²(Dirichlet Laplacian) + m₀², dirAction = ε²·φᵀ dirOp φ, PosDef, Z-matrix, dirGreen ≥ 0 entrywise |
| PP2Green2 | M1 | explicit entries, free covariance = ε⁻²·dirGreen, mass monotonicity, diag ≤ 1/m₀² |
| PP2GaussIBP | M4 | finite-dimensional Gaussian integration by parts, covariance form |
| PP2Griffiths | M2 | Griffiths I (sign-flip averaging; numerators) |
| PP2Griffiths2 | M2 | site weights, dweight = exp(Σ Jnn φφ)·∏ w, normalised Griffiths I |
| PP2Griffiths3 | M2 | integrability, Gibbs probability measure, Griffiths II (duplicate variables, cone form) for the model |
| PP2PortNelson1 | M5 | pphi2 port (Apache-2.0, 83501022): Polynomial, LayerCake, IntegrabilityHelpers; dependency map |
| PP2SimonLieb | M3/M6 | twoPt, regionTwoPt, bondJ, SimonLiebIneq (target), action split across B, M6Consumer (proved, conditional) |
| PP2SimonLieb2 | M3 | local-time integration by parts (BFS §5 step R2) |
| PP2Sine | M5a | discrete sine eigenbasis of dirOp, spectral formula for dirGreen |
| PP2SimonLieb3 | M3 | R3 (mass monotonicity in the cone, GKS II) and R4: strong Gaussian domination (BFS Thm 5.1) for the quartic box |
| PP2M6Smeared | M6 | smeared restatement: SimonLiebIneq', RegionSusceptibility, M6Consumer' and conditional_clustering' proved (conditional on inputs) |
| PP2Heat | M5b | Dirichlet heat kernel: semigroup, ∫ p_t = dirGreen, ε⁻² p_t(x,x) ≤ π/(4t) uniformly |
| PP2FKG | M7 | continuous four-functions theorem, FKG for the quartic box measure |
| PP2Limit | M8 | ‖ZD‖ ≤ 1, ‖ZD f − ZD g‖ ≤ ⟨|φ(f−g)|⟩, diagonal extraction of limit points (conditional on equicontinuity, Schwartz separability) |
| PP2RP | H1 | reflection positivity of the Dirichlet box weight (bond reflection), bounded observables |
| PP2WickSplit | M5d | Wick binomial with split constant (all degrees), Gaussian orthogonality (degree ≤ 4) |

Route findings: (1) M5 via pphi2 port ≈ 20–30 sessions; replaced by a native sine-basis/heat-kernel route ≈ 11–16 (Fable). (2) Pointwise `UniformBaseBound` in M6 is a real gap; fix by smeared decay + region susceptibility (Fable). (3) Wick ordering makes α < 4 on fine lattices; PP2SimonLieb3 shows a weight e^{c'Στ} still contracts, so R4 is proved as planned.

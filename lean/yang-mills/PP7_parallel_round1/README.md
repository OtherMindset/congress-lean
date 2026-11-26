# P(φ)₂ parallel tracks, rounds 1–10 (25 Nov 2026)

Forty-nine Lean files from parallel seats (Opus 5.5: medium effort for routine nodes, high for M3; second passes by Sonnet; route reviews by Fable). All build on Lean 4.35.0 / Mathlib 56a00585 with axioms propext, Classical.choice, Quot.sound only. Imports use local module names (`LongTable.PP2Green` etc.); for site posting they must be rewritten to posted `P_<id>` modules.

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
| PP2SimonLieb4 | M3 | R5: **Simon–Lieb inequality (SimonLiebIneq') proved** for m₀ ≠ 0, λ ≥ 0 |
| PP2Newman | M7 | FKG for integrable monotone functions; Newman's inequality: hN proved with κ = 4; `clustering_of_simonLieb_newman` |
| PP2Limit2 | M8 | Cauchy–Schwarz, Riemann bound for Schwartz h, UniformSusceptibility → UniformEquicont; limit points from the M6 hypotheses |
| PP2RP2 | H2 | complex RP, OS form (sesquilinear, positive, Cauchy–Schwarz), OS positivity of limit points (given LatticeReflStable) |
| PP2Chaos | M5e | route: L²→L^{2m} by induction on variables; one-variable moment bound proved |
| PP2FreeVar | M5c | ε⁻²·dirGreen(a,a) ≤ freeVar at every site; centre-site midpoint identity and strip bound reduced to explicit integrals |
| PP2Lebowitz | M9 | Lebowitz inequality u₄ ≤ 0 for the quartic box; IsNonGaussian reduced to QuarticDeficit |
| PP2Assembly | — | RegionGriffithsI proved; `clustering_of_M5`, `limitPoint_of_M5`, `phiFourTwoGapV3_of_M5` (V3 target from M5 inputs + non-Gaussianity + Schwartz separability) |
| PP2Chaos2 | M5e | explicit ρ_m, n-variable hypercontractive moment bound, degree-d corollary ‖F‖_q ≲ q^{12}‖F‖₂ |
| PP2FreeVar2 | M5c | strip estimate, region operator, domain monotonicity, Wick defect 0 ≤ b(x) ≤ (π/4)(1+log⁺(1/(m₀r(x)))) |
| PP2Lebowitz2 | M9 | symmetry, multilinear u₄ expansion, Taylor step; UniformQuarticNegativity ⇒ every limit point non-Gaussian |
| PP2OSRecon | H3 | OS Hilbert space (completion), ψ with ⟪ψf,ψg⟫ = Z(g−Θf), density, vacuum norm |
| PP2Region | M5 F1–F2 | free region measure = ε⁻²·regionGreen; exit bound; free boundary sum ≤ 2/cosh(κl) uniformly (SmallBoundarySum at λ = 0) |
| PP2GreenLp | M5 F3 | ε²Σ_y C(x,y)^p ≤ K_p/m₀² for all p ≥ 2; rough part ≤ K_p·T (box) |
| PP2Modes | M5 G1 | free box measure = image of standard Gaussians under the sine-mode map; independent heat-kernel split |
| PP2DoubleIBP | M5 I1, G3 | double integration by parts (box, region, generic) with constants 12, 16; misordered Wick covariance table j,k ≤ 4 |
| PP2OSShift | H4 | OS time-shift operators: self-adjoint contraction semigroup, TΩ = Ω, matrix elements = Z(τ_t g − Θf) |
| PP2Nelson | M5 G4 | Nelson bound on the box: `nl_nelsonBox_of_roughL2` — uniform-in-n bound on ∫e^{−2λV}dμ⁰ (λ ∈ [0,1]) from the single hypothesis RoughL2 (E[R_T²] ≤ K T^θ); smooth part, chaos tails, layer cake proved |
| PP2ModesGen | M5 G1/F3 region | modes and heat kernel for any PosDef matrix; heat-kernel domain monotonicity; region rough-part and Green Lp bounds |
| PP2Chaos3 | M5 G2 | stretched-exponential tail for degree-d Hermite/MvPolynomial chaos, any index type |
| PP2Moments | M9 L1, L4 | Newman's Gaussian inequality ⟨X⁴⟩ ≤ 3⟨X²⟩², ⟨X⁶⟩ ≤ 15⟨X²⟩³; Hölder lower bound for the tree term |
| PP2OSGap | H5 | `osGap_of`, `hamiltonianGap_of`: OSGap/HamiltonianGap for Z from OS positivity, time invariance, |Z| ≤ 1, Z 0 = 1, continuity, CompactApprox, ClustersAt; vacuum uniqueness |
| PP2RoughL2 | M5 G4 | rough-part L² bound (θ = 1/8): **Nelson box bound unconditional** (`rl_nelsonBox`) |
| PP2NelsonRegion | M5 G4 region | region Nelson bound reduced to the region rough-L² estimate; region Wick defect, smooth and chaos hypotheses proved |
| PP2M5Final | M5 I2 + conclusions | `phiFourTwoGapV3_of_hyps`: V3 target from NelsonRegionHyp, WickDefectHyp, WickL2Hyp, non-Gaussianity and Schwartz separability |
| PP2Separable | — | `schwartzSeparable`: SchwartzSeparable proved |
| PP2HamAssembly | H6 | CompactApprox proved; LatticeReflStable from UniformEquicont; `hamiltonianGap_of_limitPoint(_susc)`: only time-translation invariance of the limit point remains |
| PP2RoughL2Region | M5 G4 | region rough L²: **region Nelson bound proved** (`nelsonRegionHyp_holds`) |
| PP2WickHyps | M5 | WickDefectHyp and WickL2Hyp proved |
| PP2EuclidFinal | — | **`phiFourTwoGapV3_of_nonGaussian`: V3 target from non-Gaussianity alone** |
| PP2Skeleton1 | M9 L0, L1, L3 | Volterra resolvent `Rop` (existence, uniqueness, positivity, linearity), `Rop_split` (replaces BFS Lemma 2.1), `tI_eq_Rop` |
| PP2Sharp1 | T2 step (a) | Griffiths II region monotonicity; uniform susceptibility + DirichletSuppression ⇒ uniform clustering (all λ ≥ 0); fixed-spacing clustering unconditional |
| PP2WickSplit | M5d | Wick binomial with split constant (all degrees), Gaussian orthogonality (degree ≤ 4) |

Route findings: (1) M5 via pphi2 port ≈ 20–30 sessions; replaced by a native sine-basis/heat-kernel route ≈ 11–16 (Fable). (2) Pointwise `UniformBaseBound` in M6 is a real gap; fix by smeared decay + region susceptibility (Fable). (3) Wick ordering makes α < 4 on fine lattices; PP2SimonLieb3 shows a weight e^{c'Στ} still contracts, so R4 is proved as planned.

Status after round 5 (superseded): `clustering_of_simonLieb_newman` gives FiniteCutoffClustering from three remaining lattice inputs: RegionGriffithsI (Griffiths I for region measures), SmallBoundarySum and RegionSusceptibility (the M5 fixed-box estimates).

Status after round 6: `phiFourTwoGapV3_of_M5` reduces the V3 target to (i) M5Inputs (SmallBoundarySum, RegionSusceptibility) at weak coupling, (ii) UniformQuarticNegativity (or another route to non-Gaussianity), (iii) SchwartzSeparable. Fable's M5 plan (17–24 sessions before rounds 5–6 progress) ends exactly at (i).

Round 7: M5 plan in M5_PLAN.md; done F2, F3 (box), G1 (box), G3, I1. Remaining M5: region versions of F3/G1, F4 region, G2 tail, G4 (Nelson on region), I2, conclusions. M9 route (Fable): reduce to BFS skeleton inequality (CMP 91 (1.4)) + M5.

Round 8: Nelson box bound reduced to RoughL2; Hamiltonian gap assembled conditional on limit-point properties (translation invariance, continuity, CompactApprox, clustering).

Round 9: Euclidean V3 target now rests on region rough-L² (→ NelsonRegionHyp), WickDefectHyp, WickL2Hyp, and non-Gaussianity (skeleton inequality, ~11–15 sessions, plan in Fable review). Hamiltonian form additionally on time-translation invariance of limit points.

Round 10: the Euclidean V3 target now needs only non-Gaussianity of limit points.

# Targets register (P(φ)₂ / constructive-QFT direction)

Kept so that no target is lost. Rubric: Research Impact Rubric (0–120), A–G. Direction scores grade the target as if delivered; feasibility goes in notes. Status of openness must be verified against the literature before a target is adopted (see "Survey" below).

## Active
| Id | Target | A (standing) | Direction score (est.) | Status |
|---|---|---|---|---|
| T1 | φ⁴₂ weak coupling, Dirichlet boxes: FiniteCutoffClustering + limit points + non-Gaussian (PhiFourTwoGapV3), Hamiltonian form and O(2) (V4) | 14 (formalization of a 1970s theorem) | 71 | V3 reduced to non-Gaussianity alone (`phiFourTwoGapV3_of_nonGaussian`, round 10). Skeleton route: L0, L1, L3 done (PP2Skeleton1). Hamiltonian form also needs time-translation invariance of limit points. |

## Pursue (user decision, 26 Nov 2026): a Major (A = 22) open problem
| Id | Candidate | A | Est. score | Openness | Reuse of T1 machinery |
|---|---|---|---|---|---|
| T2 | Continuum φ⁴₂: mass gap (exponential clustering) throughout the one-phase / subcritical region, not only at weak coupling | 22 if open | ~79 | TO VERIFY (lattice sharpness results; Lee–Yang for h ≠ 0; Glimm–Jaffe–Spencer) | Simon–Lieb, Griffiths I/II, FKG, Newman, Lebowitz, reflection positivity, smeared M6 |
| T3 | 3D Yang–Mills existence and mass gap | 22 | ~79–85 | Open (to confirm current status) | Low: gauge theory; RP and OS reconstruction reusable |

## Recorded, not active
| Id | Target | A | Notes |
|---|---|---|---|
| T4 | 4D Yang–Mills existence and mass gap (Millennium) | 30 | Direction 120 but no concrete next step from here |
| T5 | φ⁴₃ OS axioms + weak-coupling mass gap (formalization) | 14 | Known 1970s result; raises C and F only (was mis-stated earlier as raising A) |
| T6 | Other open problems found by the survey | — | To be filled |

## Survey (26 Nov 2026; web search by a research seat — arXiv ids not individually re-verified by the lead)
- Continuum φ⁴₂, h = 0, whole one-phase region: weak coupling classical (GJS; Simon; GRS); Duch–Gubinelli new proof, small λ only (arXiv:2611.17119). Bauerschmidt–Dagallier (arXiv:2202.02295): log-Sobolev throughout the region where the susceptibility χ is bounded uniformly in ε and L ("high-temperature phase"), single threshold μ_c^χ by Griffiths II; no uniform mass gap, no comparison with the magnetisation threshold. McBryan–Rosen: mass positive above σ_c; d = 2 continuity at σ_c left open. Lattice φ⁴ sharpness known at fixed spacing (Aizenman–Barsky–Fernández; Panagiotis–Veitch arXiv:2605.31344; van Engelenburg–Heeney–Lis arXiv:2609.01362), none uniform as ε → 0. Continuity of the transition: known d ≥ 3 lattice (Gunaratnam–Panagiotis–Panis–Severo arXiv:2211.00319); Z² is their Open Problem 1.
- 3D Yang–Mills: open; local stochastic YM(H) dynamics (Chandra–Chevyrev–Hairer–Shen), no measure, no gap; toolkit fit ~none (no Griffiths/FKG for non-abelian groups).
- Caveat: classical literature (Glimm–Jaffe CMP 51 (1976); Simon CMP 77 (1980); Glimm–Jaffe book) may already contain "uniform χ ⇒ uniform exponential decay"; to check.

Survey grades (A/B/C/D/E/F/G = total; seat's estimates):
| # | Problem | Status | Score |
|---|---|---|---|
| S1 | Sharpness of continuum φ⁴₂ (and φ⁴₃): μ_c^χ = magnetisation threshold ⇒ mass gap + unique state on the whole one-phase region | Open (lattice solved at each ε) | 86–94 (A 14–22) |
| S2 | Continuity of the 2D transition (lattice Z², continuum φ⁴₂) | Open (GPPS OP1) | 92 (A 22) |
| S3 | φ⁴₃ OS axioms / gap beyond small coupling | small coupling done | 82 |
| S4 | 3D Yang–Mills | open, infeasible here | 100 (cap) |
| S5 | 2D O(N) σ-model gap, N ≥ 3 | open, infeasible (no corr. inequalities) | 100 |
| S6 | Sine-Gordon up to 8π | partial | 76 |

Lead's reading of A: S1 for φ⁴₂ alone is closer to Established (14) than Major; S1 for φ⁴₂ + φ⁴₃ together, or S2, are Major (22). Grading follows the rubric's "choose the lower" rule until the literature check is done.

## Adopted (26 Nov 2026): T2 = S1, continuum sharpness for φ⁴₂ (φ⁴₃ extension; S2 kept as secondary)
- Step (a), formal: "susceptibility bounded uniformly in (ε, L) ⇒ exponential clustering uniform in (ε, L)" via Simon–Lieb averaged over box radii (removes the boundary factor). Reuses PP2SimonLieb4, PP2M6Smeared. Check Simon 1980 / Glimm–Jaffe for priority.
- Step (b), research: do the ABF / Duminil-Copin–Tassion / OSSS sharpness arguments survive ε → 0 with the mass (not nearest-neighbour coupling) as parameter? Main obstacle: those inequalities differentiate in J ~ ε⁻². May fail.

## T2 review (Fable, 26 Nov 2026) — split
- Step (a) as first stated is not ε-uniform: averaging over radii loses a factor ε (γ ≲ χ/(εR)); the missing input is Dirichlet boundary suppression (regionTwoPt = O(ε) next to ∂B). PP2Sharp1 proves the uniform result conditional on `DirichletSuppression` and the fixed-spacing result unconditionally.
- Literature: McBryan–Rosen (CMP 51, 1976) give m > 0 above the mass-defined threshold; Bauerschmidt–Dagallier–Weber (arXiv:2504.08606) prove a unique invariant measure for μ > μ_c^χ and state the other half of sharpness is open in the continuum.
- T2a (formal deliverable, A ≤ 14): μ_c^χ = mass threshold with an ε-uniform gap bound from χ; crux = DirichletSuppression.
- T2b (research bet, A 14–22): sharpness half (μ < μ_c^χ ⇒ M⁺ > 0) in the continuum; needs a mass-derivative (∂_μ) analogue of ABF / Duminil-Copin–Tassion — no known route (bond pivotality does not survive ε → 0). Do not present as Major until this has an idea.
- S2 (2D continuity, A 22) kept as secondary; no toolkit entry point.

## Round 11 (26 Nov 2026)
- M9: tree bound proved (`tree_bound_box`: u₄ ≥ −24λε²Σ_z S⁴, BFS CMP 91 (1.3)); with Lebowitz, −24λε²ΣS⁴ ≤ u₄ ≤ 0. Strict negativity still needs the UPPER skeleton bound.
- T2a: DirichletSuppression replaced by StripCrossing (proved at λ = 0) + RegionSimonLieb (box case proved); uniform clustering from uniform χ for all λ ≥ 0 conditional on those two (PP2Sharp2).
- T2b (user priority: drive the mass-derivative idea): Fable proposes the Ising–Kac regularisation (Mourrat–Weber scaling): rescaled ABF reads m ≤ h∂_h m + γ²m³ − m²∂_μ m, uniform in γ; DCT gives m² ≥ 2(μ_c(γ) − μ). Needs: Kac → φ⁴₂ with field h, locally uniform in (μ, h) (Hairer–Iberti on the torus; h ≠ 0 extension), infinite volume, and a restated T2b (ε → 0 first, then h ↓ 0). Exponents to be re-derived before adoption.

## T2b, round 12 (26 Nov 2026)
- Kac route verified algebraically (adversarial Fable): rescaled ABF m ≤ h∂_h m + γ²m³ − m²∂_μ m is uniform in γ; companion −∂_μ m ≤ m∂_h m. Main gap: Kac→φ⁴₂ Gibbs convergence WITH field h > 0 on the torus (Hairer–Iberti prove h = 0 only), then L → ∞ (Lee–Yang), then h ↓ 0. DCT alone does not suffice (needs limsup A_c(γ) ≤ A_c^cont).
- Direct lattice route (notes: T2b_onsite_ABF_notes.md): exact identity m − h∂_h m = 4λ m² ∂_h(⟨:φ_0³:⟩/m) gives the true λ uniformly in ε; target with C = 8 ⇔ R(h) = ⟨φ_0;φ_0²⟩/⟨φ_0⟩ nonincreasing in h. Numerics (1–3 sites) and first-order perturbation support it. THE NEW LEMMA TO ATTACK: ∂_h[⟨φ_0;φ_0²⟩/⟨φ_0⟩] ≤ K ∂_h⟨φ_0²⟩, K independent of ε (conjecturally K = 0).
- Lean: PP2ABF.lean proves the model-free ABF extrapolation (characteristics form, survives pointwise limits): spontaneous magnetisation m(μ,0⁺)² ≥ 2(μ_c − μ)/a, and m(μ_c,h)³ ≥ 2κh/a given χ ≥ κ/(μ − μ_c) (shown necessary by a counterexample).

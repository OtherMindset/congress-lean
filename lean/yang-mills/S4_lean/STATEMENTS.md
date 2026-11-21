# Statement card: Lean files of Session 4, route lead B (21 Nov 2026)

Toolchain leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Every theorem listed: axioms [propext, Classical.choice, Quot.sound] only (AXIOMS.txt), no sorry. Built locally with `lake env lean <file>` and `lake build`.

| File | chars | SHA-256 |
| --- | --- | --- |
| YMSpectralStep.lean | 11,135 | 57d39615a5f51592bd8f68b3442564f3447f77efe81e240d8d4a79b00f862fca |
| YMBesselSeries.lean | 5,148 | 9f79106f8409b0318bb2f899d36bca8747118f4a66927ff5cc139d114ca7d22e |
| YMEndpoint.lean | 9,861 | 0eb75e20934e228c0170c621b1a55ff03c9875c8d6c5a09b81e90311e05e8e54 |

## YMSpectralStep.lean

- `YMSpectral.spectral_step`: Let E be a real or complex Hilbert space, T a bounded self-adjoint operator on E, α ≥ 0 and D a dense subset of E. Suppose every v in D has a real K with Re⟨v, T^(2n) v⟩ ≤ K·α^(2n) for all n ≥ 1. Then ‖Tu‖ ≤ α‖u‖ for every u in E.
- `YMSpectral.spectral_step_opNorm`: Under the same hypotheses, the operator norm satisfies ‖T‖ ≤ α.
- `YMSpectral.spectrum_subset_of_norm_le`: If T is a bounded self-adjoint operator on a complex Hilbert space and ‖T‖ ≤ α, then every complex λ in the spectrum of T (λ such that T − λ has no bounded two-sided inverse) is real with |λ| ≤ α.
- `YMSpectral.spectrum_subset_of_pos`: If in addition Re⟨u, Tu⟩ ≥ 0 for all u, then every λ in the spectrum of T is real with 0 ≤ λ ≤ α.
- `YMSpectral.bridge_spectral_step`: For a bounded self-adjoint T on a complex Hilbert space with Re⟨u, Tu⟩ ≥ 0 for all u, α ≥ 0, and the decay hypothesis of `spectral_step` on a dense set: ‖T‖ ≤ α and the spectrum of T lies in the real interval [0, α].
- Helper lemmas (not part of the claim): `ratio_mono`, `pow_le` (log-convex nonnegative sequences: a₁·a_(n+1) ≤ a₀·a_(n+2) and a₁^(n+1) ≤ a₀^n·a_(n+1)), `re_inner_pow_two_mul` (Re⟨v, T^(2n)v⟩ = ‖Tⁿv‖²), `log_convex` (‖T^(n+1)v‖⁴ ≤ ‖Tⁿv‖²·‖T^(n+2)v‖²).

## YMBesselSeries.lean

I1 κ := ∑' k, (κ/2)^(2k+1)/(k!·(k+1)!) and I2 κ := ∑' k, (κ/2)^(2k+2)/(k!·(k+2)!) are defined in the file by these series; no Mathlib Bessel function is used.

- `YMBessel.summable_I1`: For every real κ, the series ∑ (κ/2)^(2k+1)/(k!·(k+1)!) converges.
- `YMBessel.summable_I2`: For every real κ, the series ∑ (κ/2)^(2k+2)/(k!·(k+2)!) converges.
- `YMBessel.four_I2_le`: For every κ ≥ 0, 4·I2(κ) ≤ κ·I1(κ).
- `YMBessel.four_I2_lt`: For every κ > 0, 4·I2(κ) < κ·I1(κ).
- Helper lemmas: `term_identity` ((k+2)·4·t₂(κ,k) = 2·κ·t₁(κ,k)), `term_le`, `term_lt`, `term_bound`, `t1_nonneg`, `fact_pos`, `fact_ge_one`.

## YMEndpoint.lean

N(k) := ∑' j, k^(2j+1)·j!/((2j+1)!·∏_{i=0..j}(i+3/2)) and D(k)/π := ∑' j, k^(2j)/(2·4^j·j!·(j+1)!) are defined in the file by the series of failure_side_antipodal_TV.py. That these series equal the integrals, or 18·N/D the Dobrushin row-sum lower bound, is NOT formalized.

- `YMEndpoint.endpoint_below`: At k = 13103/100000, 18·N(k) < π·(D(k)/π); that is, 18·N(k)/D(k) < 1 at β = 0.13103.
- `YMEndpoint.endpoint_above`: At k = 131031/1000000, π·(D(k)/π) < 18·N(k); that is, 18·N(k)/D(k) > 1 at β = 0.131031.
- `YMEndpoint.N_bounds`: For 0 ≤ k < 1 and every J, the partial sum of N up to index J is ≤ N(k), and N(k) is ≤ that partial sum plus (term J)·r/(1−r) with r = k²/6.
- `YMEndpoint.D_bounds`: The same for D(k)/π with r = k²/8.
- `YMEndpoint.rational_below`, `YMEndpoint.rational_above`: The two explicit rational inequalities (partial sums to J = 4 plus tail bounds, π replaced by 3.141592 resp. 3.141593) that the endpoint theorems reduce to, checked by norm_num.
- `YMEndpoint.Dq_eq_I1`: For every real k, k·(D(k)/π) = I₁(k), with I₁ the same series as in YMBesselSeries.
- Helper lemmas: `aN_succ`, `bD_succ` (exact term ratios), `aN_ratio`, `bD_ratio`, `tail_bound` (geometric tail bound for nonnegative sequences with f(j+1) ≤ r·f(j), 0 ≤ r < 1), `aN_nonneg`, `bD_nonneg`, `fpos`, `prod_pos'`.


## YMTextbook.lean (21 Nov 2026)

Textbook facts that cross-family checks of the foundation posts listed as inputs, each stated from Mathlib. Built locally with Lean 4.35.0 and Mathlib 56a00585 (exit 0, no output); `#print axioms` gives propext, Classical.choice, Quot.sound for every theorem; no sorry. Second pass by Claude Opus 5.5 (rebuilt, statements compared with the card, test instances compiled). The file states the facts; applying them in a post (splitting a product measure, identifying R⁴ with a Euclidean space, SU(2) as a compact topological group, which Mathlib does not provide) is the post's own step.

| Theorem | Claim |
|---|---|
| `YMTextbook.tychonoff` | Tychonoff's theorem: for any index set and any family of compact topological spaces, the product space (product topology) is compact. |
| `YMTextbook.prob_measures_subseq` | On a compact metrizable topological space E with its Borel σ-algebra, every sequence (μ_n) of probability measures has a subsequence (μ_{φ(n)}), φ strictly increasing, and a probability measure ν such that ∫ f dμ_{φ(n)} → ∫ f dν for every bounded continuous f: E → ℝ. |
| `YMTextbook.prob_measures_subseq_product` | The same statement for E = S^ι, the product of countably many copies of a compact metric space S, with the product topology and its Borel σ-algebra: every sequence of Borel probability measures on S^ι has a weakly convergent subsequence. |
| `YMTextbook.fubini` | Fubini's theorem: for s-finite measures μ on α and ν on β and f: α × β → ℝ integrable for the product measure, ∫ f d(μ×ν) = ∫(∫ f(x,y) dν(y)) dμ(x) = ∫(∫ f(x,y) dμ(x)) dν(y). |
| `YMTextbook.fubini_measurable` | The measurability half of Fubini's theorem: for an s-finite measure ν on β and f: α × β → ℝ strongly measurable on the product, the function x ↦ ∫ f(x,y) dν(y) is strongly measurable on α. |
| `YMTextbook.monotone_convergence` | Monotone convergence: for a pointwise increasing sequence f_n of measurable functions with values in [0, ∞], ∫ sup_n f_n dμ = sup_n ∫ f_n dμ (Lebesgue integral with values in [0, ∞]). |
| `YMTextbook.dominated_convergence` | Dominated convergence: if the F_n are a.e. strongly measurable, \|F_n\| ≤ bound a.e. for each n with bound integrable, and F_n → f a.e., then ∫ F_n dμ → ∫ f dμ. Real-valued functions, any measure μ. |
| `YMTextbook.deriv_under_integral` | Differentiation under the integral sign: let s be a neighbourhood of x₀ in ℝ. If F(x, ·) is a.e. strongly measurable for x near x₀, F(x₀, ·) is integrable, F'(x₀, ·) is a.e. strongly measurable, and for a.e. a and all x in s: F(·, a) has derivative F'(x, a) at x and \|F'(x, a)\| ≤ bound(a) with bound integrable, then F'(x₀, ·) is integrable and x ↦ ∫ F(x, a) dμ(a) has derivative ∫ F'(x₀, a) dμ(a) at x₀. |
| `YMTextbook.pi_lambda_measures` | π–λ theorem for measures: if μ is a finite measure and ν a measure on a σ-algebra generated by a π-system C, μ(s) = ν(s) for all s in C and μ(whole space) = ν(whole space), then μ = ν. |
| `YMTextbook.borel_generated_by_closed` | The Borel σ-algebra of a topological space is the σ-algebra generated by its closed sets. |
| `YMTextbook.haar_probability_unique` | Uniqueness of normalized Haar measure: on a compact topological group with its Borel σ-algebra, any two Haar measures that are probability measures are equal. (Haar measure in Mathlib's sense: left-invariant, finite on compacts, positive on nonempty open sets.) |
| `YMTextbook.haar_left_invariant_probability` | On a compact topological group with its Borel σ-algebra, every left-invariant probability measure equals any Haar probability measure. |
| `YMTextbook.sphere_measure_invariant` | Orthogonal invariance of surface measure: let E be a finite-dimensional real inner product space, g a linear isometry of E onto itself, and σ = volume.toSphere the (unnormalized) surface measure on the unit sphere induced by Lebesgue measure (σ(s) = dim E · volume of the cone {r·x : 0 < r < 1, x ∈ s}). Then σ(g⁻¹(s)) = σ(s) for every measurable s in the sphere; g acts on the sphere by restriction (sphereMap, defined in the file). |
| `YMTextbook.sphere_measure_map` | Pushforward form of the same fact: for E, g and σ = volume.toSphere as in sphere_measure_invariant, the image measure of σ under the restriction of g to the unit sphere is σ, and ∫ f(g x) dσ(x) = ∫ f dσ for every strongly measurable f: sphere → ℝ. |

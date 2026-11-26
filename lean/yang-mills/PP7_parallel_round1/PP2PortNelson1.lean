/-
# PP2PortNelson1 — M5 track, session 1: Mathlib-only leaves of pphi2's Nelson estimate

Toolchain: Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 (project /root/mgproj).

## Attribution

Ported (faithful copies, namespace renamed to `PP2Port`, minimal API-drift fixes) from

* repository: https://github.com/mrdouglasny/pphi2
* commit:     83501022fc6ff5f38e93a4d5b631ef4044b66216
* files:      `Pphi2/Polynomial.lean`,
              `Pphi2/NelsonEstimate/LayerCake.lean`,
              `Pphi2/NelsonEstimate/IntegrabilityHelpers.lean`
* original:   Copyright (c) 2026 Michael R. Douglas (repository LICENSE; per-file notice present in
              LayerCake.lean and IntegrabilityHelpers.lean, none in Polynomial.lean).
* license:    Apache License 2.0 (repository `LICENSE`). This file is a modified
              derivative work: the namespace was changed (`Pphi2.*` → `PP2Port.*`),
              the placeholders `evalWick`/`evalWick'` of `Polynomial.lean` were omitted
              (unused; documented upstream as placeholders), docstrings were shortened,
              and API drift was fixed: `if_neg` → `ite_eq_right`, `Set.mem_setOf_eq` →
              `Set.mem_ofPred_eq`, import `Mathlib.Data.Real.Basic` → `Mathlib.Basic.Real.Basic`.

## FORMALIZED (ported, building, no sorry, no axioms beyond propext/Classical.choice/Quot.sound)

* `PP2Port.InteractionPolynomial` (structure), `.eval`, `.eval_neg`, `.shiftQuadratic`
* `PP2Port.LayerCake.exp_neg_sq_le_exp_two_max`
* `PP2Port.LayerCake.setOf_le_max_eq_setOf_le_neg`
* `PP2Port.LayerCake.lintegral_expSq_neg_le_layer_cake`   (main: layer-cake bound)
* `PP2Port.LayerCake.lintegral_expSq_neg_le_of_tail`       (main: tail-bound interface)
* `PP2Port.IntegrabilityHelpers.lintegral_exp_neg_lt_top`
* `PP2Port.IntegrabilityHelpers.lintegral_layer_cake_lt_top_of_eventual_decay`

## Dependency map (read from source; their build was NOT run)

`nelson_exponential_estimate_lattice` (NelsonEstimate.lean:81) is a 6-line specialization
of `nelson_exponential_estimate_master` (PolynomialChaosBridge.lean:1295, a `theorem`) to
`a = circleSpacing L N = L/N`.

Internal pphi2 import closure of `Pphi2.NelsonEstimate.NelsonEstimate`: 23 files, 17 783 lines
(of the ~25k-line NelsonEstimate dir only 15 files are in the closure; the `Asym*` and
`GenericBridge` files are NOT):
  Polynomial (102) · WickOrdering: WickPolynomial 989, Counterterm 187 ·
  InteractingMeasure: LatticeAction 124, LatticeMeasure 261 ·
  TorusContinuumLimit: TorusEmbedding 137 ·
  NelsonEstimate: LayerCake 229, IntegrabilityHelpers 89, WickBinomial 377, CovarianceSplit 267,
  SmoothLowerBound 223, DynamicalCutoff 346, BridgeFromTail 86, LatticeSetup 469,
  LatticeBridge 475, HeatKernelBound 1290, FieldDecomposition 4236, CovarianceBoundsGJ 1608,
  ChaosMoment 70, ChaosTailBridge 511, RoughErrorBound 4301, PolynomialChaosBridge 1306,
  NelsonEstimate 100.
External packages used by the closure (lake-manifest pins):
  * gaussian-field `d63a285` (GaussianField: Construction, CramerWold, Hypercontractive,
    WickMultivariate; Lattice: Covariance, FKG, HeatKernel, LatticeFourierProduct,
    LatticeFourierIndexing, Symmetry; SchwartzNuclear.HermiteWick; SmoothCircle.Eigenvalues;
    Torus.Evaluation) — 45 files in the closure; a local copy at the pinned commit was read.
  * gaussian-hilbert `56ee09f` (GaussianHilbert: HermitePolynomials,
    PolynomialChaosConcentration) — NOT available locally, not inspected.
  * markov-semigroups `acf6491` (MarkovSemigroups.Matrix.HeatKernel; Mathlib-only imports) —
    the local copy is at a different commit (`0b5dd80`).
  * Mathlib `c5ea003` (Lean v4.30.0).
Mathlib-only leaves of the closure: Polynomial, LayerCake, IntegrabilityHelpers (ported here).
Next-nearest: WickPolynomial (needs SchwartzNuclear.HermiteWick), WickBinomial (needs
WickPolynomial), ChaosMoment and ChaosTailBridge (need GaussianHilbert.PolynomialChaosConcentration).

Axiom finding (from text search against the axiom list in /root/scripts/pphi2_axioms.txt; line
counts and session estimates below are approximate, the author's estimates): none of the 26
listed axioms is mentioned in the import closure, and no axiom or sorry declaration occurs in any of the 23 internal files or the 45
gaussian-field files of the closure (the textual hits are in docstrings; the two
gaussian-field axioms `hermiteGalerkinTrunc_tendsto_schwartz`, `fourierMultiplier_schwartz_bound`
are outside the closure). So, judged only by textual search of the sources (no #print axioms was run, and their build was
not run), no axiom or sorry appears in the closure within their repo, CONDITIONAL
on gaussian-hilbert (unread here; their AXIOM_AUDIT.md 2026-07-12 entry reports that the
axiom printout of `polynomial_chaos_concentration` at that pin is the standard three) and on
markov-semigroups at `acf6491`. Caveat from their AXIOM_AUDIT (2026-10-08): the former
uniform-in-`a` axiom was REMOVED as false; the proved statement is fixed volume `N * a = L`
(exactly the form of `nelson_exponential_estimate_lattice`).

## Periodic → Dirichlet adaptation

Uses torus / periodic structure (FinLatticeSites = Fin d → ZMod N, periodic Laplacian with
eigenvalues m² + Σ (4/a²) sin²(πk_i/N), lattice Fourier modes):
  Counterterm, LatticeAction, LatticeMeasure (via Lattice.Covariance), CovarianceSplit
  (smooth/rough split defined on Fourier eigenvalues), HeatKernelBound (sin² lower bound,
  Gaussian lattice sums, uniform heat-kernel trace bounds), FieldDecomposition (4.2k lines;
  Fourier product basis, independence of modes — the heaviest), CovarianceBoundsGJ,
  RoughErrorBound (4.3k), LatticeSetup, SmoothLowerBound (via the Wick constant),
  TorusEmbedding / circleSpacing (only for the final specialization).
Geometry-free (reusable nearly verbatim): Polynomial, LayerCake, IntegrabilityHelpers,
  WickBinomial, WickPolynomial (modulo HermiteWick), DynamicalCutoff (mostly), BridgeFromTail,
  LatticeBridge, ChaosMoment, ChaosTailBridge, most of PolynomialChaosBridge.
For a Dirichlet box: replace ZMod Fourier modes by the sine basis sin(πk x/(N+1)) with
eigenvalues m² + Σ (4/a²) sin²(πk_i/(2(N+1))); the covariance split C_S(T), C_R(T) and the
heat-kernel diagonal bounds must be redone (e.g. Dirichlet diagonal ≤ free/periodic diagonal
by monotonicity); the Wick constant becomes site-dependent c(x) (not translation invariant),
which touches Counterterm, the use of WickBinomial, and SmoothLowerBound.

## Estimate for the rest of the port

Geometry-free part (~4.5k lines incl. WickPolynomial, plus the HermiteWick and
chaos-concentration dependencies, whose gaussian-hilbert source must be obtained separately):
3–5 sessions. Periodic-specific part (~12k lines: FieldDecomposition, RoughErrorBound,
CovarianceBoundsGJ, HeatKernelBound, CovarianceSplit) ported as-is: 8–12 sessions; the
Dirichlet re-proof of those on top: a further 8–15 sessions. Total ≈ 20–30 sessions.
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

noncomputable section

namespace PP2Port

/-! ## From `Pphi2/Polynomial.lean`: the interaction polynomial -/

/-- Data for a P(Φ)₂ model: an even polynomial P bounded from below.

The polynomial P(τ) = (1/n)τⁿ + Σ aₘτᵐ has even degree n ≥ 4 and only
even-power terms (odd coefficients vanish). This ensures P(τ) = P(-τ).

Reference: Simon, *The P(φ)₂ Euclidean QFT*, §II.3;
Glimm-Jaffe, *Quantum Physics*, §6.1. -/
structure InteractionPolynomial where
  /-- Degree n ≥ 4, n even. -/
  n : ℕ
  hn_ge : 4 ≤ n
  hn_even : Even n
  /-- Coefficients a_0, ..., a_{n-1}. The leading coefficient a_n = 1/n. -/
  coeff : Fin n → ℝ
  /-- Odd-power coefficients vanish: P is an even function. -/
  coeff_odd_eq_zero : ∀ m : Fin n, Odd (m : ℕ) → coeff m = 0
  /-- Constant coefficient is nonpositive. -/
  coeff_zero_nonpos : coeff ⟨0, by omega⟩ ≤ 0

/-- Evaluate P(τ) = (1/n)τⁿ + Σ_{m<n} a_m τᵐ. -/
def InteractionPolynomial.eval (P : InteractionPolynomial) (τ : ℝ) : ℝ :=
  (1 / P.n : ℝ) * τ ^ P.n + ∑ m : Fin P.n, P.coeff m * τ ^ (m : ℕ)

/-- P is an even function: P(-τ) = P(τ). -/
theorem InteractionPolynomial.eval_neg (P : InteractionPolynomial) (τ : ℝ) :
    P.eval (-τ) = P.eval τ := by
  simp only [InteractionPolynomial.eval]
  congr 1
  · congr 1
    exact Even.neg_pow P.hn_even τ
  · apply Finset.sum_congr rfl
    intro m _
    by_cases hm : Odd (m : ℕ)
    · simp [P.coeff_odd_eq_zero m hm]
    · rw [Nat.not_odd_iff_even] at hm
      congr 1
      exact Even.neg_pow hm τ

/-- Shift the quadratic (τ²) coefficient of P by δ (mass reparametrization). -/
def InteractionPolynomial.shiftQuadratic (P : InteractionPolynomial) (δ : ℝ) :
    InteractionPolynomial where
  n := P.n
  hn_ge := P.hn_ge
  hn_even := P.hn_even
  coeff m := if (m : ℕ) = 2 then P.coeff m + δ else P.coeff m
  coeff_odd_eq_zero m hm := by
    have hne : (m : ℕ) ≠ 2 := by
      intro h; rw [h] at hm; revert hm; decide
    rw [ite_eq_right hne]
    exact P.coeff_odd_eq_zero m hm
  coeff_zero_nonpos := by
    show (if (⟨0, _⟩ : Fin P.n).val = 2 then _ else _) ≤ 0
    rw [ite_eq_right (by omega : (0 : ℕ) ≠ 2)]
    exact P.coeff_zero_nonpos

/-! ## From `Pphi2/NelsonEstimate/LayerCake.lean` -/

namespace LayerCake

open MeasureTheory Real Set intervalIntegral

/-- Pointwise bound: `exp(-V)² ≤ exp(2 · max(0, -V))`. -/
theorem exp_neg_sq_le_exp_two_max (V : ℝ) :
    Real.exp (-V) ^ 2 ≤ Real.exp (2 * max 0 (-V)) := by
  have h_eq : Real.exp (-V) ^ 2 = Real.exp (-2 * V) := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h_eq]
  apply Real.exp_le_exp.mpr
  have hmax : -V ≤ max 0 (-V) := le_max_right _ _
  linarith

/-- For `t > 0`, `{ω | t ≤ max 0 (-V ω)} = {ω | V ω ≤ -t}`. -/
theorem setOf_le_max_eq_setOf_le_neg
    {α : Type*} (V : α → ℝ) {t : ℝ} (ht : 0 < t) :
    {a | t ≤ max 0 (-V a)} = {a | V a ≤ -t} := by
  ext a
  simp only [Set.mem_ofPred_eq, le_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h; right; linarith

/-- **Layer-cake reformulation of the Boltzmann L² norm.**
`∫⁻ exp(-V)² dμ ≤ μ(univ) + ∫⁻ t in (0,∞), μ{V ≤ -t} · 2e^{2t} dt`. -/
theorem lintegral_expSq_neg_le_layer_cake
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (V : α → ℝ) (hV : Measurable V) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-V ω) ^ 2) ∂μ ≤
      μ Set.univ +
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {a | V a ≤ -t} * ENNReal.ofReal (2 * Real.exp (2 * t)) := by
  set W : α → ℝ := fun ω => max 0 (-V ω) with hW_def
  have hW_nn : ∀ ω, 0 ≤ W ω := fun ω => le_max_left _ _
  have hW_meas : Measurable W := measurable_const.max hV.neg
  have h_pointwise : ∀ ω,
      ENNReal.ofReal (Real.exp (-V ω) ^ 2) ≤
        ENNReal.ofReal (Real.exp (2 * W ω)) := fun ω =>
    ENNReal.ofReal_le_ofReal (exp_neg_sq_le_exp_two_max (V ω))
  refine (lintegral_mono h_pointwise).trans ?_
  have h_split :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω)) ∂μ =
        μ Set.univ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
    have h_eq : ∀ ω,
        ENNReal.ofReal (Real.exp (2 * W ω)) =
          1 + ENNReal.ofReal (Real.exp (2 * W ω) - 1) := by
      intro ω
      have h_exp_ge_one : 1 ≤ Real.exp (2 * W ω) :=
        Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * W ω)
      have h_sub_nn : (0 : ℝ) ≤ Real.exp (2 * W ω) - 1 := by linarith
      have h_calc :
          (1 : ENNReal) + ENNReal.ofReal (Real.exp (2 * W ω) - 1) =
            ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp (2 * W ω) - 1) := by
        rw [ENNReal.ofReal_one]
      rw [h_calc, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) h_sub_nn]
      congr 1
      ring
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω)) ∂μ
        = ∫⁻ ω, 1 + ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
          apply lintegral_congr_ae; filter_upwards with ω; rw [h_eq ω]
      _ = ∫⁻ _ : α, 1 ∂μ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
            rw [lintegral_add_left measurable_const]
      _ = μ Set.univ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
            rw [lintegral_one]
  rw [h_split]
  refine add_le_add le_rfl ?_
  have h_anti : ∀ s : ℝ,
      ∫ t in (0 : ℝ)..s, 2 * Real.exp (2 * t) = Real.exp (2 * s) - 1 := by
    intro s
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    calc ∫ t in (0 : ℝ)..s, 2 * Real.exp (2 * t)
        = 2 * ∫ t in (0 : ℝ)..s, Real.exp (2 * t) :=
          intervalIntegral.integral_const_mul ..
      _ = 2 * ((2 : ℝ)⁻¹ • ∫ x in (2 * 0 : ℝ)..(2 * s), Real.exp x) := by
            rw [integral_comp_mul_left _ h2_ne]
      _ = ∫ x in (2 * 0 : ℝ)..(2 * s), Real.exp x := by
            rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h2_ne, one_mul]
      _ = Real.exp (2 * s) - Real.exp (2 * 0) := integral_exp
      _ = Real.exp (2 * s) - 1 := by
            rw [mul_zero, Real.exp_zero]
  have h_int_rewrite :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ =
        ∫⁻ ω,
          ENNReal.ofReal (∫ t in (0 : ℝ)..W ω, 2 * Real.exp (2 * t)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with ω
    rw [h_anti (W ω)]
  rw [h_int_rewrite]
  have h_lc :
      ∫⁻ ω,
          ENNReal.ofReal (∫ t in (0 : ℝ)..W ω, 2 * Real.exp (2 * t)) ∂μ =
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {a | t ≤ W a} * ENNReal.ofReal (2 * Real.exp (2 * t)) := by
    apply MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul μ
      (Filter.Eventually.of_forall hW_nn) hW_meas.aemeasurable
    · intro t _
      apply Continuous.intervalIntegrable
      fun_prop
    · refine Filter.Eventually.of_forall ?_
      intro t
      positivity
  rw [h_lc]
  apply le_of_eq
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change μ {a | t ≤ W a} * ENNReal.ofReal (2 * Real.exp (2 * t)) =
       μ {a | V a ≤ -t} * ENNReal.ofReal (2 * Real.exp (2 * t))
  rw [setOf_le_max_eq_setOf_le_neg V ht]

/-- **Exp-moment-from-tail-bound interface.** -/
theorem lintegral_expSq_neg_le_of_tail
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (V : α → ℝ) (hV : Measurable V)
    (ψ : ℝ → ENNReal)
    (h_tail : ∀ t, 0 < t → μ {ω | V ω ≤ -t} ≤ ψ t) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-V ω) ^ 2) ∂μ ≤
      μ Set.univ +
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) := by
  refine (lintegral_expSq_neg_le_layer_cake μ V hV).trans ?_
  refine add_le_add le_rfl ?_
  refine setLIntegral_mono' measurableSet_Ioi ?_
  intro t ht
  exact mul_le_mul_left (h_tail t ht) _

end LayerCake

/-! ## From `Pphi2/NelsonEstimate/IntegrabilityHelpers.lean` -/

namespace IntegrabilityHelpers

open MeasureTheory Real Set

/-- `t ↦ exp(-t)` is `lintegral`-integrable on `Ioi T₀`. -/
theorem lintegral_exp_neg_lt_top (T₀ : ℝ) :
    ∫⁻ t in Set.Ioi T₀, ENNReal.ofReal (Real.exp (-t)) < ⊤ := by
  have h_integrable : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi T₀) := by
    have := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) T₀
    simpa using this
  have h_eq :
      ∫⁻ t in Set.Ioi T₀, ENNReal.ofReal (Real.exp (-t)) =
        ENNReal.ofReal (∫ t in Set.Ioi T₀, Real.exp (-t)) := by
    rw [ofReal_integral_eq_lintegral_ofReal h_integrable]
    refine Filter.Eventually.of_forall ?_
    intro t; exact (Real.exp_pos _).le
  rw [h_eq]
  exact ENNReal.ofReal_lt_top

/-- **Layer-cake integrand integrability via eventual exponential decay.** -/
theorem lintegral_layer_cake_lt_top_of_eventual_decay
    (ψ : ℝ → ENNReal)
    (T₀ : ℝ) (hT₀ : 0 < T₀)
    (h_small : ∫⁻ t in Set.Ioc (0 : ℝ) T₀,
        ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) < ⊤)
    (h_large : ∀ t, T₀ < t →
        ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) ≤
          ENNReal.ofReal (Real.exp (-t))) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
      ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) < ⊤ := by
  have h_split : Set.Ioi (0 : ℝ) = Set.Ioc 0 T₀ ∪ Set.Ioi T₀ := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ T₀
      · left; exact ⟨ht, h⟩
      · right; exact lt_of_not_ge h
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · linarith
  rw [h_split]
  refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
  refine ENNReal.add_lt_top.mpr ⟨h_small, ?_⟩
  refine lt_of_le_of_lt ?_ (lintegral_exp_neg_lt_top T₀)
  apply MeasureTheory.setLIntegral_mono' measurableSet_Ioi
  intro t ht
  exact h_large t ht

end IntegrabilityHelpers

end PP2Port

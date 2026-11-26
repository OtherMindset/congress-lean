import LongTable.R_PP2Sine

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Modes.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node G1 (M5 plan),
session 1, box version. The free Dirichlet box measure as a linear image of independent standard
Gaussians, and the per-mode split (namespace `PP2Target`).

Notation: ε = `spacing n`, Λ = `DSite n k`, e_K = `sineVec2 K`, λ_K = `dirEig n k m₀ K`,
U = `sineMat n k` (U x K = e_K(x), orthogonal), γ = `gaussianReal 0 1`, γ^Λ = `Measure.pi (fun _ => γ)`.
The coefficient d_K = ε⁻¹ λ_K^{−1/2} is `md_coef`, the matrix A = U · diag(d) is `md_mat`, and
`md_map n k m₀ ξ = A ξ`, i.e. (A ξ)(x) = ε⁻¹ Σ_K λ_K^{−1/2} ξ_K e_K(x) (`md_map_apply`).

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `md_dirAction`: dirAction (A ξ) = Σ_K ξ_K² (spectral; from `dirOp_mul_sineMat`, UᵀU = 1).
* `md_det_ne`: det A ≠ 0; `md_equiv`: A as a measurable equivalence; `md_change`:
  ∫ g = |det A| ∫ g ∘ A (Lebesgue, any g : DField → ℝ; `Real.map_linearMap_volume_pi_eq_smul_volume_pi`).
* `md_lintegral_pi_prod`: Tonelli for products over a finite index type (pi of σ-finite measures).
* `md_gauss_eq_withDensity`: γ^Λ = Lebesgue.withDensity (Π_K gaussianPDF 0 1 (ξ_K)), and
  `md_density_toReal`: that density is (2π)^{−|Λ|/2} exp(−½ Σ ξ_K²).
* `md_gauss_modes` (**G1, box**): for EVERY F : DField n k → ℝ (no measurability/integrability
  hypotheses; both sides are Bochner integrals, 0 when non-integrable) and every m₀ ∈ ℝ,
  (∫ F φ e^{−½ dirAction φ} dφ) / (∫ e^{−½ dirAction φ} dφ) = ∫ F (A ξ) dγ^Λ(ξ).
  `md_gauss_modes_measure`: Measure.map (md_map n k m₀) γ^Λ =
  Z⁻¹ • Lebesgue.withDensity e^{−½ dirAction}, Z = ∫ e^{−½ dirAction}.
  `md_weight_integral`: Z = |det A| (2π)^{|Λ|/2}; `md_weight_integral_pos`, `md_weight_integrable`
  (for every m₀, including m₀ = 0, unlike `dirWeight_integrable`).
* `md_mix_law` (1-D): for a² + b² = 1, (γ ⊗ γ).map (a·₁ + b·₂) = γ (`gaussianReal_conv_gaussianReal`).
* `md_split_law`: for 0 ≤ α_K ≤ 1 (β_K = √(1 − α_K²)),
  (γ^Λ ⊗ γ^Λ).map ((ξˢ, ξʳ) ↦ α ξˢ + β ξʳ) = γ^Λ
  (via `measurePreserving_arrowProdEquivProdArrow` and `Measure.pi_map_pi`).
* `md_gauss_split`: for measurable F, the normalised free expectation of F equals
  ∫ F(φ_s + φ_r) d(γ^Λ ⊗ γ^Λ), φ_s = A(α ξˢ), φ_r = A(β ξʳ), ξˢ, ξʳ independent standard.
  `md_heat_split`: the case α_K = e^{−tλ_K/2} (t ≥ 0), so α_K² = e^{−tλ_K} as in the M5 plan.

NOT formalized here: the region version (ψ on B with regOp; same argument once F1 provides the
rectangle sine diagonalisation of `regionOp`); covariance formulas for φ_s, φ_r in closed form
(they follow from `md_gauss_split` with F = φ x φ y and `dirGreen_spectral`-type sums).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## The linear map A = U · diag(ε⁻¹ λ^{−1/2}) -/

/-- d_K = ε⁻¹ λ_K^{−1/2}. -/
def md_coef (n k : ℕ) (m₀ : ℝ) (K : DSite n k) : ℝ :=
  (spacing n)⁻¹ * (√(dirEig n k m₀ K))⁻¹

/-- The matrix A = U · diag(d). -/
def md_mat (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ :=
  sineMat n k * diagonal (md_coef n k m₀)

/-- ξ ↦ A ξ = ε⁻¹ Σ_K λ_K^{−1/2} ξ_K e_K. -/
def md_map (n k : ℕ) (m₀ : ℝ) (ξ : DField n k) : DField n k := md_mat n k m₀ *ᵥ ξ

theorem md_map_apply (m₀ : ℝ) (ξ : DField n k) (x : DSite n k) :
    md_map n k m₀ ξ x =
      (spacing n)⁻¹ * ∑ K : DSite n k, (√(dirEig n k m₀ K))⁻¹ * ξ K * sineVec2 K x := by
  simp only [md_map, md_mat, mulVec, dotProduct, mul_diagonal, sineMat, md_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  ring

theorem md_map_add (m₀ : ℝ) (u v : DField n k) :
    md_map n k m₀ (u + v) = md_map n k m₀ u + md_map n k m₀ v := by
  simp only [md_map, mulVec_add]

theorem md_coef_pos (m₀ : ℝ) (K : DSite n k) : 0 < md_coef n k m₀ K := by
  have h1 := dirEig_pos (n := n) (k := k) m₀ K
  have h2 := spacing_pos n
  unfold md_coef
  positivity

theorem md_coef_sq (m₀ : ℝ) (K : DSite n k) :
    spacing n ^ 2 * dirEig n k m₀ K * md_coef n k m₀ K ^ 2 = 1 := by
  have h := dirEig_pos (n := n) (k := k) m₀ K
  have hs := (spacing_pos n).ne'
  rw [md_coef, mul_pow, inv_pow, inv_pow, sq_sqrt h.le]
  field_simp

/-- **Spectral form of the action:** dirAction (A ξ) = Σ_K ξ_K². -/
theorem md_dirAction (m₀ : ℝ) (ξ : DField n k) :
    dirAction n k m₀ (md_map n k m₀ ξ) = ∑ K : DSite n k, ξ K ^ 2 := by
  set U := sineMat n k
  set v : DField n k := fun K => md_coef n k m₀ K * ξ K with hv
  have hφ : md_map n k m₀ ξ = U *ᵥ v := by
    simp only [md_map, md_mat, ← mulVec_mulVec]
    congr 1
    funext K
    rw [mulVec_diagonal]
  have hD : dirOp n k m₀ *ᵥ (U *ᵥ v) = U *ᵥ (fun K => dirEig n k m₀ K * v K) := by
    rw [mulVec_mulVec, dirOp_mul_sineMat, ← mulVec_mulVec]
    congr 1
    funext K
    rw [mulVec_diagonal]
  have hO : ∀ w : DField n k, (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = v ⬝ᵥ w := by
    intro w
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, sineMat_transpose_mul, vecMul_one]
  rw [dirAction_eq_quad, hφ, hD, hO]
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  have := md_coef_sq (n := n) (k := k) m₀ K
  simp only [hv]
  linear_combination ξ K ^ 2 * this

theorem md_det_ne (m₀ : ℝ) : (md_mat n k m₀).det ≠ 0 := by
  rw [md_mat, det_mul, det_diagonal]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun K _ => (md_coef_pos m₀ K).ne')
  intro h
  have := congrArg det (sineMat_transpose_mul (n := n) (k := k))
  rw [det_mul, det_transpose, h, mul_zero, det_one] at this
  exact zero_ne_one this

/-- A as a measurable equivalence of DField n k. -/
def md_equiv (n k : ℕ) (m₀ : ℝ) : DField n k ≃ᵐ DField n k :=
  letI : Invertible (md_mat n k m₀) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (md_det_ne m₀))
  ((md_mat n k m₀).toLinearEquiv' this).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem md_equiv_apply (m₀ : ℝ) (ξ : DField n k) : md_equiv n k m₀ ξ = md_map n k m₀ ξ := by
  simp [md_equiv, md_map, Matrix.toLinearEquiv']

theorem md_map_measurable (m₀ : ℝ) : Measurable (md_map n k m₀) := by
  have h : (md_map n k m₀) = md_equiv n k m₀ := funext fun ξ => (md_equiv_apply m₀ ξ).symm
  rw [h]
  exact (md_equiv n k m₀).measurable

/-- **Change of variables** φ = A ξ for Lebesgue measure on DField n k (any g). -/
theorem md_change (m₀ : ℝ) (g : DField n k → ℝ) :
    ∫ φ, g φ = |(md_mat n k m₀).det| * ∫ ξ, g (md_map n k m₀ ξ) := by
  have hdet : LinearMap.det (Matrix.toLin' (md_mat n k m₀)) ≠ 0 := by
    rw [LinearMap.det_toLin']; exact md_det_ne m₀
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have h1 : ∫ ξ, g (md_map n k m₀ ξ) =
      ∫ φ, g φ ∂(Measure.map (md_equiv n k m₀) (volume : Measure (DField n k))) := by
    rw [integral_map_equiv]
    simp only [md_equiv_apply]
  have h2 : (Measure.map (md_equiv n k m₀) (volume : Measure (DField n k))) =
      Measure.map (Matrix.toLin' (md_mat n k m₀)) volume := by
    congr 1
  rw [h1, h2, hmap, integral_smul_measure, LinearMap.det_toLin',
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr (md_det_ne m₀)), one_mul]

/-! ## The product of standard Gaussians as a density -/

theorem md_lintegral_fin_prod (m : ℕ) (μ : Fin m → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin m → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    refine (lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j : Fin m => μ j.succ) (f := f 0) (g := fun y : Fin m → ℝ => ∏ i, f i.succ (y i))
      (hf 0).aemeasurable ?_).trans ?_
    · exact (Finset.measurable_prod _ fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
    · rw [ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf _)]

/-- Tonelli for products over a finite index type. -/
theorem md_lintegral_pi_prod {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact md_lintegral_fin_prod _ _ _ fun i => hf _

theorem md_gauss_eq_withDensity :
    Measure.pi (fun _ : DSite n k => gaussianReal 0 1) =
      (volume : Measure (DField n k)).withDensity (fun ξ => ∏ K, gaussianPDF 0 1 (ξ K)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    md_lintegral_pi_prod _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun K _ => ?_
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (hs K)]

theorem md_density_measurable :
    Measurable (fun ξ : DField n k => ∏ K, gaussianPDF 0 1 (ξ K)) :=
  Finset.measurable_prod _ fun K _ => (measurable_gaussianPDF 0 1).comp (measurable_pi_apply K)

theorem md_density_toReal (ξ : DField n k) :
    (∏ K, gaussianPDF 0 1 (ξ K)).toReal =
      (√(2 * π))⁻¹ ^ Fintype.card (DSite n k) * Real.exp (-(∑ K, ξ K ^ 2) / 2) := by
  rw [ENNReal.toReal_prod]
  simp only [toReal_gaussianPDF]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]

/-! ## G1 for the box -/

theorem md_key (m₀ : ℝ) (G : DField n k → ℝ) :
    ∫ φ, G φ * Real.exp (-(dirAction n k m₀ φ) / 2) =
      |(md_mat n k m₀).det| * ((√(2 * π))⁻¹ ^ Fintype.card (DSite n k))⁻¹ *
        ∫ ξ, G (md_map n k m₀ ξ) ∂Measure.pi (fun _ : DSite n k => gaussianReal 0 1) := by
  have hc : 0 < (√(2 * π))⁻¹ ^ Fintype.card (DSite n k) := by positivity
  have hpt : ∀ ξ : DField n k, (∏ K, gaussianPDF 0 1 (ξ K)).toReal • G (md_map n k m₀ ξ) =
      (√(2 * π))⁻¹ ^ Fintype.card (DSite n k) *
        (G (md_map n k m₀ ξ) * Real.exp (-(dirAction n k m₀ (md_map n k m₀ ξ)) / 2)) := by
    intro ξ
    rw [md_density_toReal, md_dirAction, smul_eq_mul]
    ring
  rw [md_change m₀, md_gauss_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul md_density_measurable
      (ae_of_all _ fun ξ => ENNReal.prod_lt_top fun K _ => gaussianPDF_lt_top)]
  simp_rw [hpt]
  rw [integral_const_mul, ← mul_assoc, mul_assoc _ _⁻¹, inv_mul_cancel₀ hc.ne', mul_one]

/-- **G1 (box): the free Dirichlet measure is the image of γ^Λ under A.** For every
F : DField n k → ℝ and every m₀:
(∫ F φ e^{−½ dirAction φ} dφ) / (∫ e^{−½ dirAction φ} dφ) = ∫ F(A ξ) dγ^Λ(ξ),
with (A ξ)(x) = ε⁻¹ Σ_K λ_K^{−1/2} ξ_K e_K(x). -/
theorem md_gauss_modes (m₀ : ℝ) (F : DField n k → ℝ) :
    (∫ φ, F φ * Real.exp (-(dirAction n k m₀ φ) / 2)) /
        (∫ φ, Real.exp (-(dirAction n k m₀ φ) / 2)) =
      ∫ ξ, F (md_map n k m₀ ξ) ∂Measure.pi (fun _ : DSite n k => gaussianReal 0 1) := by
  have hc : 0 < (√(2 * π))⁻¹ ^ Fintype.card (DSite n k) := by positivity
  have hD : 0 < |(md_mat n k m₀).det| := abs_pos.mpr (md_det_ne m₀)
  have h2 := md_key (n := n) (k := k) m₀ (fun _ => 1)
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h2
  rw [md_key m₀ F, h2]
  field_simp

/-- The normalisation, for every m₀: ∫ e^{−½ dirAction} = |det A| (2π)^{|Λ|/2}. -/
theorem md_weight_integral (m₀ : ℝ) :
    ∫ φ, Real.exp (-(dirAction n k m₀ φ) / 2) =
      |(md_mat n k m₀).det| * ((√(2 * π))⁻¹ ^ Fintype.card (DSite n k))⁻¹ := by
  have h2 := md_key (n := n) (k := k) m₀ (fun _ => 1)
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h2
  exact h2

theorem md_weight_integral_pos (m₀ : ℝ) : 0 < ∫ φ, Real.exp (-(dirAction n k m₀ φ) / 2) := by
  have hD : 0 < |(md_mat n k m₀).det| := abs_pos.mpr (md_det_ne m₀)
  rw [md_weight_integral]
  positivity

/-- Integrability of the free weight for every m₀ (also m₀ = 0). -/
theorem md_weight_integrable (m₀ : ℝ) :
    Integrable (fun φ : DField n k => Real.exp (-(dirAction n k m₀ φ) / 2)) := by
  by_contra h
  have := integral_undef h
  linarith [md_weight_integral_pos (n := n) (k := k) m₀]

/-- **G1 (box), measure form:** the normalised free Dirichlet measure is the pushforward of γ^Λ
under A. -/
theorem md_gauss_modes_measure (m₀ : ℝ) :
    Measure.map (md_map n k m₀) (Measure.pi (fun _ : DSite n k => gaussianReal 0 1)) =
      ENNReal.ofReal (∫ φ, Real.exp (-(dirAction n k m₀ φ) / 2))⁻¹ •
        (volume : Measure (DField n k)).withDensity
          (fun φ => ENNReal.ofReal (Real.exp (-(dirAction n k m₀ φ) / 2))) := by
  ext s hs
  have hZ := md_weight_integral_pos (n := n) (k := k) m₀
  have hmode := md_gauss_modes m₀ (s.indicator 1)
  rw [Measure.map_apply (md_map_measurable m₀) hs, Measure.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← ofReal_integral_eq_lintegral_ofReal (md_weight_integrable m₀).integrableOn
      (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le), ← ofReal_measureReal]
  congr 1
  have hL : ∫ ξ, s.indicator 1 (md_map n k m₀ ξ) ∂Measure.pi (fun _ : DSite n k => gaussianReal 0 1)
      = (Measure.pi (fun _ : DSite n k => gaussianReal 0 1)).real (md_map n k m₀ ⁻¹' s) := by
    rw [← integral_indicator_one ((md_map_measurable m₀) hs)]
    rfl
  have hR : ∫ φ, s.indicator 1 φ * Real.exp (-(dirAction n k m₀ φ) / 2) =
      ∫ φ in s, Real.exp (-(dirAction n k m₀ φ) / 2) := by
    rw [← integral_indicator hs]
    congr 1
    funext φ
    by_cases h : φ ∈ s <;> simp [h]
  rw [← hL, ← hmode, hR, div_eq_inv_mul]

/-! ## The per-mode split -/

/-- One-dimensional mixing: for a² + b² = 1, a ξ + b ξ' ~ γ when ξ, ξ' are independent standard. -/
theorem md_mix_law (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun q : ℝ × ℝ => a * q.1 + b * q.2) =
      gaussianReal 0 1 := by
  have h : (fun q : ℝ × ℝ => a * q.1 + b * q.2) =
      (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (a * ·) (b * ·) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_mul]
  change Measure.conv _ _ = _
  rw [gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext
    simp [hab]

/-- **Per-mode split of γ^Λ:** for 0 ≤ α_K ≤ 1 and β_K = √(1 − α_K²),
(ξˢ, ξʳ) ↦ α ξˢ + β ξʳ maps γ^Λ ⊗ γ^Λ to γ^Λ. -/
theorem md_split_law (α : DSite n k → ℝ) (h0 : ∀ K, 0 ≤ α K) (h1 : ∀ K, α K ≤ 1) :
    ((Measure.pi (fun _ : DSite n k => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : DSite n k => gaussianReal 0 1))).map
      (fun p : DField n k × DField n k => fun K => α K * p.1 K + √(1 - α K ^ 2) * p.2 K) =
      Measure.pi (fun _ : DSite n k => gaussianReal 0 1) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (DSite n k)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  rw [← hmp.map_eq, Measure.map_map (by fun_prop) hmp.measurable]
  have hcomp : ((fun p : DField n k × DField n k => fun K => α K * p.1 K + √(1 - α K ^ 2) * p.2 K)
      ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (DSite n k))) =
      fun (x : DSite n k → ℝ × ℝ) K =>
        (fun q : ℝ × ℝ => α K * q.1 + √(1 - α K ^ 2) * q.2) (x K) := rfl
  rw [hcomp]
  refine (Measure.pi_map_pi (X := fun _ => ℝ × ℝ) (Y := fun _ => ℝ)
    (μ := fun _ => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (f := fun K (q : ℝ × ℝ) => α K * q.1 + √(1 - α K ^ 2) * q.2)
    (fun K => (by fun_prop : Measurable _).aemeasurable)).trans ?_
  congr 1
  funext K
  refine md_mix_law _ _ ?_
  rw [sq_sqrt (by nlinarith [h0 K, h1 K])]
  ring

/-- **G1 split (box):** the free Dirichlet expectation of a measurable F is
E[F(φ_s + φ_r)] with φ_s = A(α ξˢ), φ_r = A(β ξʳ), ξˢ, ξʳ independent with law γ^Λ,
β_K = √(1 − α_K²), for any 0 ≤ α_K ≤ 1. -/
theorem md_gauss_split (m₀ : ℝ) (α : DSite n k → ℝ) (h0 : ∀ K, 0 ≤ α K) (h1 : ∀ K, α K ≤ 1)
    (F : DField n k → ℝ) (hF : Measurable F) :
    (∫ φ, F φ * Real.exp (-(dirAction n k m₀ φ) / 2)) /
        (∫ φ, Real.exp (-(dirAction n k m₀ φ) / 2)) =
      ∫ p, F (md_map n k m₀ (fun K => α K * p.1 K) +
          md_map n k m₀ (fun K => √(1 - α K ^ 2) * p.2 K))
        ∂((Measure.pi (fun _ : DSite n k => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : DSite n k => gaussianReal 0 1))) := by
  rw [md_gauss_modes]
  conv_lhs => rw [← md_split_law α h0 h1]
  refine (integral_map (f := fun ξ => F (md_map n k m₀ ξ)) (by fun_prop)
    (hF.comp (md_map_measurable m₀)).aestronglyMeasurable).trans ?_
  congr 1
  funext p
  rw [← md_map_add]
  rfl

/-- The heat-kernel split α_K = e^{−tλ_K/2} (t ≥ 0), so α_K² = e^{−tλ_K} and
β_K = √(1 − e^{−tλ_K}). -/
theorem md_heat_split (m₀ t : ℝ) (ht : 0 ≤ t) (F : DField n k → ℝ) (hF : Measurable F) :
    (∫ φ, F φ * Real.exp (-(dirAction n k m₀ φ) / 2)) /
        (∫ φ, Real.exp (-(dirAction n k m₀ φ) / 2)) =
      ∫ p, F (md_map n k m₀ (fun K => Real.exp (-(t * dirEig n k m₀ K) / 2) * p.1 K) +
          md_map n k m₀ (fun K => √(1 - Real.exp (-(t * dirEig n k m₀ K))) * p.2 K))
        ∂((Measure.pi (fun _ : DSite n k => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : DSite n k => gaussianReal 0 1))) := by
  have hsq : ∀ K : DSite n k,
      Real.exp (-(t * dirEig n k m₀ K) / 2) ^ 2 = Real.exp (-(t * dirEig n k m₀ K)) := by
    intro K
    rw [sq, ← Real.exp_add]
    ring_nf
  have h := md_gauss_split m₀ (fun K => Real.exp (-(t * dirEig n k m₀ K) / 2))
    (fun K => (Real.exp_pos _).le)
    (fun K => Real.exp_le_one_iff.mpr (by
      have := mul_nonneg ht (dirEig_pos (n := n) (k := k) m₀ K).le
      linarith)) F hF
  simp only [hsq] at h
  exact h

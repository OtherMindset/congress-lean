import LongTable.R_PP2Modes
import LongTable.R_PP2GreenLpB
import LongTable.R_PP2Region

/-!
Part A of PP2ModesGen (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2ModesGen.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), nodes G1 and F3
(region), M5 plan, session 1. Gaussian modes and heat kernels for a GENERIC positive definite
matrix via Mathlib's spectral theorem (no sine basis), specialised to regions B of box sites
(namespace `PP2Target`).

Notation (generic part): ι finite, A : Matrix ι ι ℝ; for hA : A.IsHermitian, λ = hA.eigenvalues,
U = `mg_U hA` (the real orthogonal matrix `IsHermitian.eigenvectorUnitary`, U x K = e_K(x));
for hA : A.PosDef, M = `mg_modeMat hA` = U · diag(λ^{−1/2}); γ = `gaussianReal 0 1`,
γ^ι = `Measure.pi (fun _ => γ)`; p_t = `mg_heat hA t` = U diag(e^{−tλ}) Uᵀ (all real t).
Region part: ε = `spacing n`, p^B_t = `mg_regionHeat n k m₀ t B` = heat kernel of `regionOp B`,
C^B_r(T) = `mg_regionRough n k m₀ T B` = ε⁻² ∫_{(0,T]} p^B_t dt; box: `heatK`, `glp_roughCov`.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
Generic spectral facts: `mg_U_transpose_mul`, `mg_U_mul_transpose` (U orthogonal), `mg_mul_U`
(A U = U diag λ), `mg_spectral` (A = U diag λ Uᵀ), `mg_inv_spectral` (A⁻¹ = U diag λ⁻¹ Uᵀ).
(1) Modes. `mg_quad_modeMat`: (Mξ)ᵀA(Mξ) = Σ ξ_K²; `mg_change` (Lebesgue change of variables);
  **`mg_gauss_modes`**: for EVERY F (no hypotheses), (∫ F φ e^{−½φᵀAφ})/(∫ e^{−½φᵀAφ}) =
  ∫ F(Mξ) dγ^ι; `mg_gauss_modes_measure` (measure form), `mg_weight_integral(_pos)`,
  `mg_weight_integrable`.
(2) Heat kernel. `mg_heat_apply` (p_t(x,y) = Σ_K U x K U y K e^{−tλ_K}), `mg_heat_transpose`,
  `mg_heat_symm`, `mg_heat_zero` (p_0 = 1), `mg_heat_mul` / `mg_heat_semigroup` (p_t p_s = p_{t+s}),
  `mg_heat_sq_sum` (Σ_y p_t(x,y)² = p_{2t}(x,x)), `mg_heat_diag_nonneg`,
  **`mg_integral_heat`** (∫_{(0,∞)} p_t(x,y) dt = A⁻¹ x y), `mg_integral_heat_Ioc`
  (∫_{(0,T]} p_t = U diag((1−e^{−Tλ})/λ) Uᵀ).
(3) Split. `mg_split_law`, `mg_gauss_split` (any 0 ≤ α ≤ 1), **`mg_heat_split`**
  (α_K = e^{−tλ_K/2}, β_K = √(1−e^{−tλ_K})); covariance matrices of the two halves:
  `mg_rough_cov` (M diag(1−e^{−tλ}) Mᵀ = ∫_{(0,t]} p_s ds), `mg_smooth_cov` (M diag(e^{−tλ}) Mᵀ = p_t A⁻¹).
Matrix exponential and Z-matrix monotonicity: `mg_exp_conj`, `mg_heat_eq_exp` (p_t = exp(−tA)),
  `mg_exp_scalar_add`, `mg_exp_apply_hasSum` (entrywise exp series), `mg_pow_nonneg`,
  `mg_pow_submatrix_le`, `mg_exp_nonneg`, `mg_exp_submatrix_le`, **`mg_heat_submatrix_le`**:
  A symmetric with A i j ≤ 0 (i ≠ j), A_B = A|_{B×B} ⇒ 0 ≤ p^{A_B}_t(x,y) ≤ p^A_t(x,y) for t ≥ 0
  (exp(−tA) = e^{−tc} exp(tN), N = c·1 − A ≥ 0, and (N_B)^j ≤ N^j entrywise).
(4) Regions. `mg_heatK_eq_exp` (heatK = exp(−t dirOp)), `mg_heat_dirOp`, `mg_regionOp_isHermitian`;
  **`mg_region_gauss_modes`** and **`mg_region_heat_split`** (A = rg_scaledOp B, density
  qweight m₀ 0 (zeroExt B ψ)); `mg_heat_scaledOp` (heat kernel of rg_scaledOp at τ = p^B at ε²τ);
  `mg_region_rough_cov` (rough covariance of the split = C^B_r(ε²τ)).
(5) Region bounds. **`mg_regionHeat_le`**: 0 ≤ p^B_t(x,y) ≤ heatK t x y (t ≥ 0, any m₀, B);
  `mg_regionHeat_diag_le`: ε⁻² p^B_t(x,x) ≤ e^{−tm₀²} π/(4t); `mg_regionHeat_semigroup`,
  `mg_regionHeat_sq_sum`, `mg_integral_regionHeat` (= regionGreen, m₀ ≠ 0);
  `mg_regionRough_le` (0 ≤ C^B_r ≤ C_r); **`mg_regionRough_Lp_le`**:
  ε² Σ_{y∈B} |C^B_r(T)(x,y)|^p ≤ (π/4)^{p−1}/2 · p^p · T; **`mg_regionGreen_Lp_le`**:
  ε² Σ_{y∈B} (ε⁻² regionGreen x y)^p ≤ (π/4)^{p−1}/2 · Γ(1/p)^p / m₀²;
  `mg_region_rough_cov_Lp_le` (the same bound for M diag(1−e^{−τλ}) Mᵀ, with T = ε²τ).

NOT formalized here: the probabilistic identity E[φ_r(x) φ_r(y)] = (M diag β² Mᵀ)(x, y) (only the
matrix identities are proved; the Gaussian second moments ∫ ξ_K ξ_L dγ^ι = δ_KL are not stated);
the smooth-part pointwise bounds; anything at λ > 0.
`mg_exp_apply_hasSum` uses `set_option backward.isDefEq.respectTransparency false` (as Mathlib's
MatrixExponential does) to use the scoped L∞-operator norm on matrices.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

namespace PP2Target

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-! ## The orthogonal eigenvector matrix -/

/-- The real orthogonal matrix U whose columns are the eigenvectors of the symmetric A
(`Matrix.IsHermitian.eigenvectorUnitary`): U x K = e_K(x). -/
def mg_U (hA : A.IsHermitian) : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ)

theorem mg_U_transpose_mul (hA : A.IsHermitian) : (mg_U hA)ᵀ * mg_U hA = 1 := by
  have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  exact h

theorem mg_U_mul_transpose (hA : A.IsHermitian) : mg_U hA * (mg_U hA)ᵀ = 1 :=
  mul_eq_one_comm.mp (mg_U_transpose_mul hA)

theorem mg_mul_U (hA : A.IsHermitian) :
    A * mg_U hA = mg_U hA * diagonal hA.eigenvalues := by
  ext x K
  rw [mul_diagonal]
  have h := congrFun (hA.mulVec_eigenvectorBasis K) x
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [mul_apply, mg_U, IsHermitian.eigenvectorUnitary_apply]
  rw [h, mul_comm]

/-- A = U diag(λ) Uᵀ. -/
theorem mg_spectral (hA : A.IsHermitian) :
    A = mg_U hA * diagonal hA.eigenvalues * (mg_U hA)ᵀ := by
  rw [← mg_mul_U, Matrix.mul_assoc, mg_U_mul_transpose, Matrix.mul_one]

theorem mg_U_det_ne (hA : A.IsHermitian) : (mg_U hA).det ≠ 0 := by
  intro h
  have := congrArg det (mg_U_transpose_mul hA)
  rw [det_mul, det_transpose, h, mul_zero, det_one] at this
  exact zero_ne_one this

theorem mg_U_dot (hA : A.IsHermitian) (v w : ι → ℝ) :
    (mg_U hA *ᵥ v) ⬝ᵥ (mg_U hA *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, mg_U_transpose_mul, vecMul_one]

/-- A⁻¹ = U diag(λ⁻¹) Uᵀ for positive definite A. -/
theorem mg_inv_spectral (hA : A.PosDef) :
    A⁻¹ = mg_U hA.1 * diagonal (fun K => (hA.1.eigenvalues K)⁻¹) * (mg_U hA.1)ᵀ := by
  apply inv_eq_right_inv
  have hs := mg_spectral hA.1
  have hd : diagonal hA.1.eigenvalues * diagonal (fun K => (hA.1.eigenvalues K)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext K
    exact mul_inv_cancel₀ (hA.eigenvalues_pos K).ne'
  calc A * (mg_U hA.1 * diagonal (fun K => (hA.1.eigenvalues K)⁻¹) * (mg_U hA.1)ᵀ)
      = mg_U hA.1 * diagonal hA.1.eigenvalues * (mg_U hA.1)ᵀ *
        (mg_U hA.1 * diagonal (fun K => (hA.1.eigenvalues K)⁻¹) * (mg_U hA.1)ᵀ) := by
        nth_rewrite 1 [hs]; rfl
    _ = mg_U hA.1 * (diagonal hA.1.eigenvalues * ((mg_U hA.1)ᵀ * mg_U hA.1) *
          diagonal (fun K => (hA.1.eigenvalues K)⁻¹)) * (mg_U hA.1)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [mg_U_transpose_mul, Matrix.mul_one, hd, Matrix.mul_one, mg_U_mul_transpose]

/-! ## G1, generic: the mode matrix M = U diag(λ^{−1/2}) -/

/-- d_K = λ_K^{−1/2}. -/
def mg_coef (hA : A.PosDef) (K : ι) : ℝ := (√(hA.1.eigenvalues K))⁻¹

/-- The mode matrix M = U · diag(λ^{−1/2}). -/
def mg_modeMat (hA : A.PosDef) : Matrix ι ι ℝ := mg_U hA.1 * diagonal (mg_coef hA)

theorem mg_coef_pos (hA : A.PosDef) (K : ι) : 0 < mg_coef hA K := by
  have h := hA.eigenvalues_pos K
  unfold mg_coef
  positivity

theorem mg_coef_sq (hA : A.PosDef) (K : ι) : hA.1.eigenvalues K * mg_coef hA K ^ 2 = 1 := by
  have h := hA.eigenvalues_pos K
  rw [mg_coef, inv_pow, sq_sqrt h.le]
  field_simp

theorem mg_modeMat_apply (hA : A.PosDef) (ξ : ι → ℝ) (x : ι) :
    (mg_modeMat hA *ᵥ ξ) x = ∑ K, (√(hA.1.eigenvalues K))⁻¹ * ξ K * mg_U hA.1 x K := by
  simp only [mg_modeMat, mulVec, dotProduct, mul_diagonal, mg_coef]
  refine Finset.sum_congr rfl fun K _ => ?_
  ring

/-- **Spectral form of the quadratic form:** (Mξ)ᵀ A (Mξ) = Σ_K ξ_K². -/
theorem mg_quad_modeMat (hA : A.PosDef) (ξ : ι → ℝ) :
    (mg_modeMat hA *ᵥ ξ) ⬝ᵥ A *ᵥ (mg_modeMat hA *ᵥ ξ) = ∑ K, ξ K ^ 2 := by
  set U := mg_U hA.1
  set v : ι → ℝ := fun K => mg_coef hA K * ξ K with hv
  have hφ : mg_modeMat hA *ᵥ ξ = U *ᵥ v := by
    simp only [mg_modeMat, ← mulVec_mulVec]
    congr 1
    funext K
    rw [mulVec_diagonal]
  have hD : A *ᵥ (U *ᵥ v) = U *ᵥ (fun K => hA.1.eigenvalues K * v K) := by
    rw [mulVec_mulVec, mg_mul_U, ← mulVec_mulVec]
    congr 1
    funext K
    rw [mulVec_diagonal]
  rw [hφ, hD, mg_U_dot]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun K _ => ?_
  have := mg_coef_sq hA K
  simp only [hv]
  linear_combination ξ K ^ 2 * this

theorem mg_modeMat_det_ne (hA : A.PosDef) : (mg_modeMat hA).det ≠ 0 := by
  rw [mg_modeMat, det_mul, det_diagonal]
  exact mul_ne_zero (mg_U_det_ne hA.1)
    (Finset.prod_ne_zero_iff.mpr fun K _ => (mg_coef_pos hA K).ne')

/-- M as a measurable equivalence. -/
def mg_equiv (hA : A.PosDef) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  letI : Invertible (mg_modeMat hA) :=
    invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (mg_modeMat_det_ne hA))
  ((mg_modeMat hA).toLinearEquiv' this).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem mg_equiv_apply (hA : A.PosDef) (ξ : ι → ℝ) : mg_equiv hA ξ = mg_modeMat hA *ᵥ ξ := by
  simp [mg_equiv, Matrix.toLinearEquiv']

theorem mg_map_measurable (hA : A.PosDef) : Measurable (fun ξ : ι → ℝ => mg_modeMat hA *ᵥ ξ) := by
  have h : (fun ξ : ι → ℝ => mg_modeMat hA *ᵥ ξ) = mg_equiv hA :=
    funext fun ξ => (mg_equiv_apply hA ξ).symm
  rw [h]
  exact (mg_equiv hA).measurable

/-- Change of variables φ = M ξ for Lebesgue measure on ι → ℝ (any g). -/
theorem mg_change (hA : A.PosDef) (g : (ι → ℝ) → ℝ) :
    ∫ φ, g φ = |(mg_modeMat hA).det| * ∫ ξ, g (mg_modeMat hA *ᵥ ξ) := by
  have hdet : LinearMap.det (Matrix.toLin' (mg_modeMat hA)) ≠ 0 := by
    rw [LinearMap.det_toLin']; exact mg_modeMat_det_ne hA
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have h1 : ∫ ξ, g (mg_modeMat hA *ᵥ ξ) =
      ∫ φ, g φ ∂(Measure.map (mg_equiv hA) (volume : Measure (ι → ℝ))) := by
    rw [integral_map_equiv]
    simp only [mg_equiv_apply]
  have h2 : (Measure.map (mg_equiv hA) (volume : Measure (ι → ℝ))) =
      Measure.map (Matrix.toLin' (mg_modeMat hA)) volume := by
    congr 1
  rw [h1, h2, hmap, integral_smul_measure, LinearMap.det_toLin',
    ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr (mg_modeMat_det_ne hA)), one_mul]

omit [DecidableEq ι] in
theorem mg_gauss_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      (volume : Measure (ι → ℝ)).withDensity (fun ξ => ∏ K, gaussianPDF 0 1 (ξ K)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    md_lintegral_pi_prod _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun K _ => ?_
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (hs K)]

omit [DecidableEq ι] in
theorem mg_density_measurable :
    Measurable (fun ξ : ι → ℝ => ∏ K, gaussianPDF 0 1 (ξ K)) :=
  Finset.measurable_prod _ fun K _ => (measurable_gaussianPDF 0 1).comp (measurable_pi_apply K)

omit [DecidableEq ι] in
theorem mg_density_toReal (ξ : ι → ℝ) :
    (∏ K, gaussianPDF 0 1 (ξ K)).toReal =
      (√(2 * π))⁻¹ ^ Fintype.card ι * Real.exp (-(∑ K, ξ K ^ 2) / 2) := by
  rw [ENNReal.toReal_prod]
  simp only [toReal_gaussianPDF]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]

theorem mg_key (hA : A.PosDef) (G : (ι → ℝ) → ℝ) :
    ∫ φ, G φ * Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2) =
      |(mg_modeMat hA).det| * ((√(2 * π))⁻¹ ^ Fintype.card ι)⁻¹ *
        ∫ ξ, G (mg_modeMat hA *ᵥ ξ) ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hc : 0 < (√(2 * π))⁻¹ ^ Fintype.card ι := by positivity
  have hpt : ∀ ξ : ι → ℝ, (∏ K, gaussianPDF 0 1 (ξ K)).toReal • G (mg_modeMat hA *ᵥ ξ) =
      (√(2 * π))⁻¹ ^ Fintype.card ι *
        (G (mg_modeMat hA *ᵥ ξ) * Real.exp (-((mg_modeMat hA *ᵥ ξ) ⬝ᵥ A *ᵥ
          (mg_modeMat hA *ᵥ ξ)) / 2)) := by
    intro ξ
    rw [mg_density_toReal, mg_quad_modeMat, smul_eq_mul]
    ring
  rw [mg_change hA, mg_gauss_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul mg_density_measurable
      (ae_of_all _ fun ξ => ENNReal.prod_lt_top fun K _ => gaussianPDF_lt_top)]
  simp_rw [hpt]
  rw [integral_const_mul, ← mul_assoc, mul_assoc _ _⁻¹, inv_mul_cancel₀ hc.ne', mul_one]

/-- **G1 (generic): the normalised Gaussian measure with precision A is the image of γ^ι under
M = U diag(λ^{−1/2}).** For every F : (ι → ℝ) → ℝ (no hypotheses; Bochner integrals):
(∫ F φ e^{−½ φᵀAφ} dφ) / (∫ e^{−½ φᵀAφ} dφ) = ∫ F(M ξ) dγ^ι(ξ). -/
theorem mg_gauss_modes (hA : A.PosDef) (F : (ι → ℝ) → ℝ) :
    (∫ φ, F φ * Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)) / (∫ φ, Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)) =
      ∫ ξ, F (mg_modeMat hA *ᵥ ξ) ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hc : 0 < (√(2 * π))⁻¹ ^ Fintype.card ι := by positivity
  have hD : 0 < |(mg_modeMat hA).det| := abs_pos.mpr (mg_modeMat_det_ne hA)
  have h2 := mg_key hA (fun _ => 1)
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h2
  rw [mg_key hA F, h2]
  field_simp

/-- The normalisation: ∫ e^{−½ φᵀAφ} = |det M| (2π)^{|ι|/2}. -/
theorem mg_weight_integral (hA : A.PosDef) :
    ∫ φ, Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2) =
      |(mg_modeMat hA).det| * ((√(2 * π))⁻¹ ^ Fintype.card ι)⁻¹ := by
  have h2 := mg_key hA (fun _ => 1)
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h2
  exact h2

theorem mg_weight_integral_pos (hA : A.PosDef) :
    0 < ∫ φ, Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2) := by
  have hD : 0 < |(mg_modeMat hA).det| := abs_pos.mpr (mg_modeMat_det_ne hA)
  rw [mg_weight_integral hA]
  positivity

theorem mg_weight_integrable (hA : A.PosDef) :
    Integrable (fun φ : ι → ℝ => Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)) := by
  by_contra h
  have := integral_undef h
  linarith [mg_weight_integral_pos hA]

/-- The normalised Gaussian measure with precision A, in measure form: the pushforward of γ^ι
under M. -/
theorem mg_gauss_modes_measure (hA : A.PosDef) :
    Measure.map (fun ξ => mg_modeMat hA *ᵥ ξ) (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ENNReal.ofReal (∫ φ, Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2))⁻¹ •
        (volume : Measure (ι → ℝ)).withDensity
          (fun φ => ENNReal.ofReal (Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2))) := by
  ext s hs
  have hZ := mg_weight_integral_pos hA
  have hmode := mg_gauss_modes hA (s.indicator 1)
  rw [Measure.map_apply (mg_map_measurable hA) hs, Measure.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← ofReal_integral_eq_lintegral_ofReal (mg_weight_integrable hA).integrableOn
      (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le), ← ofReal_measureReal]
  congr 1
  have hL : ∫ ξ, s.indicator 1 (mg_modeMat hA *ᵥ ξ) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)
      = (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
          ((fun ξ => mg_modeMat hA *ᵥ ξ) ⁻¹' s) := by
    rw [← integral_indicator_one ((mg_map_measurable hA) hs)]
    rfl
  have hR : ∫ φ, s.indicator 1 φ * Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2) =
      ∫ φ in s, Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2) := by
    rw [← integral_indicator hs]
    congr 1
    funext φ
    by_cases h : φ ∈ s <;> simp [h]
  rw [← hL, ← hmode, hR, div_eq_inv_mul]

end Generic

end PP2Target

end

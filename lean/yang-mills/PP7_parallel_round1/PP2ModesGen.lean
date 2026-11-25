import LongTable.PP2Modes
import LongTable.PP2GreenLp
import LongTable.PP2Region

/-!
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

/-! ## The per-mode split, generic -/

omit [DecidableEq ι] in
/-- Per-mode split of γ^ι: for 0 ≤ α_K ≤ 1, β_K = √(1 − α_K²),
(ξˢ, ξʳ) ↦ α ξˢ + β ξʳ maps γ^ι ⊗ γ^ι to γ^ι. -/
theorem mg_split_law (α : ι → ℝ) (h0 : ∀ K, 0 ≤ α K) (h1 : ∀ K, α K ≤ 1) :
    ((Measure.pi (fun _ : ι => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : ι => gaussianReal 0 1))).map
      (fun p : (ι → ℝ) × (ι → ℝ) => fun K => α K * p.1 K + √(1 - α K ^ 2) * p.2 K) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  rw [← hmp.map_eq, Measure.map_map (by fun_prop) hmp.measurable]
  have hcomp : ((fun p : (ι → ℝ) × (ι → ℝ) => fun K => α K * p.1 K + √(1 - α K ^ 2) * p.2 K)
      ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι)) =
      fun (x : ι → ℝ × ℝ) K =>
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

/-- **Split (generic):** for measurable F and 0 ≤ α_K ≤ 1, the normalised Gaussian expectation of
F equals E[F(M(α ξˢ) + M(β ξʳ))], ξˢ, ξʳ independent with law γ^ι, β_K = √(1 − α_K²). -/
theorem mg_gauss_split (hA : A.PosDef) (α : ι → ℝ) (h0 : ∀ K, 0 ≤ α K) (h1 : ∀ K, α K ≤ 1)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F) :
    (∫ φ, F φ * Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)) / (∫ φ, Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)) =
      ∫ p, F (mg_modeMat hA *ᵥ (fun K => α K * p.1 K) +
          mg_modeMat hA *ᵥ (fun K => √(1 - α K ^ 2) * p.2 K))
        ∂((Measure.pi (fun _ : ι => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : ι => gaussianReal 0 1))) := by
  rw [mg_gauss_modes hA]
  conv_lhs => rw [← mg_split_law α h0 h1]
  refine (integral_map (f := fun ξ => F (mg_modeMat hA *ᵥ ξ)) (by fun_prop)
    (hF.comp (mg_map_measurable hA)).aestronglyMeasurable).trans ?_
  congr 1
  funext p
  rw [← mulVec_add]
  rfl

/-- **Heat split (generic):** α_K = e^{−tλ_K/2} (t ≥ 0), so α_K² = e^{−tλ_K},
β_K = √(1 − e^{−tλ_K}). -/
theorem mg_heat_split (hA : A.PosDef) (t : ℝ) (ht : 0 ≤ t) (F : (ι → ℝ) → ℝ)
    (hF : Measurable F) :
    (∫ φ, F φ * Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)) / (∫ φ, Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)) =
      ∫ p, F (mg_modeMat hA *ᵥ (fun K => Real.exp (-(t * hA.1.eigenvalues K) / 2) * p.1 K) +
          mg_modeMat hA *ᵥ (fun K => √(1 - Real.exp (-(t * hA.1.eigenvalues K))) * p.2 K))
        ∂((Measure.pi (fun _ : ι => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : ι => gaussianReal 0 1))) := by
  have hsq : ∀ K : ι,
      Real.exp (-(t * hA.1.eigenvalues K) / 2) ^ 2 = Real.exp (-(t * hA.1.eigenvalues K)) := by
    intro K
    rw [sq, ← Real.exp_add]
    ring_nf
  have h := mg_gauss_split hA (fun K => Real.exp (-(t * hA.1.eigenvalues K) / 2))
    (fun K => (Real.exp_pos _).le)
    (fun K => Real.exp_le_one_iff.mpr (by
      have := mul_nonneg ht (hA.eigenvalues_pos K).le
      linarith)) F hF
  simp only [hsq] at h
  exact h

/-! ## The heat kernel p_t = U diag(e^{−tλ}) Uᵀ -/

/-- The heat kernel of the symmetric A: p_t = U diag(e^{−tλ}) Uᵀ (all real t). -/
def mg_heat (hA : A.IsHermitian) (t : ℝ) : Matrix ι ι ℝ :=
  mg_U hA * diagonal (fun K => Real.exp (-(t * hA.eigenvalues K))) * (mg_U hA)ᵀ

theorem mg_conj_apply (U : Matrix ι ι ℝ) (d : ι → ℝ) (x y : ι) :
    (U * diagonal d * Uᵀ) x y = ∑ K, U x K * U y K * d K := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [mul_diagonal, transpose_apply]
  ring

theorem mg_heat_apply (hA : A.IsHermitian) (t : ℝ) (x y : ι) :
    mg_heat hA t x y = ∑ K, mg_U hA x K * mg_U hA y K * Real.exp (-(t * hA.eigenvalues K)) :=
  mg_conj_apply _ _ x y

theorem mg_conj_mul (hA : A.IsHermitian) (d e : ι → ℝ) :
    mg_U hA * diagonal d * (mg_U hA)ᵀ * (mg_U hA * diagonal e * (mg_U hA)ᵀ) =
      mg_U hA * diagonal (fun K => d K * e K) * (mg_U hA)ᵀ := by
  calc mg_U hA * diagonal d * (mg_U hA)ᵀ * (mg_U hA * diagonal e * (mg_U hA)ᵀ)
      = mg_U hA * (diagonal d * ((mg_U hA)ᵀ * mg_U hA) * diagonal e) * (mg_U hA)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [mg_U_transpose_mul, Matrix.mul_one, diagonal_mul_diagonal]

theorem mg_heat_transpose (hA : A.IsHermitian) (t : ℝ) : (mg_heat hA t)ᵀ = mg_heat hA t := by
  rw [mg_heat, transpose_mul, transpose_mul, diagonal_transpose, transpose_transpose,
    Matrix.mul_assoc]

theorem mg_heat_symm (hA : A.IsHermitian) (t : ℝ) (x y : ι) :
    mg_heat hA t x y = mg_heat hA t y x := by
  rw [← transpose_apply (mg_heat hA t) y x, mg_heat_transpose]

theorem mg_heat_zero (hA : A.IsHermitian) : mg_heat hA 0 = 1 := by
  simp only [mg_heat, zero_mul, neg_zero, Real.exp_zero, diagonal_one, Matrix.mul_one,
    mg_U_mul_transpose]

/-- **Semigroup:** p_t p_s = p_{t+s}. -/
theorem mg_heat_mul (hA : A.IsHermitian) (t s : ℝ) :
    mg_heat hA t * mg_heat hA s = mg_heat hA (t + s) := by
  rw [mg_heat, mg_heat, mg_conj_mul, mg_heat]
  congr 3
  funext K
  rw [← Real.exp_add]
  ring_nf

theorem mg_heat_semigroup (hA : A.IsHermitian) (t s : ℝ) (x y : ι) :
    ∑ z, mg_heat hA t x z * mg_heat hA s z y = mg_heat hA (t + s) x y := by
  rw [← mg_heat_mul, mul_apply]

/-- Σ_y p_t(x, y)² = p_{2t}(x, x). -/
theorem mg_heat_sq_sum (hA : A.IsHermitian) (t : ℝ) (x : ι) :
    ∑ y, mg_heat hA t x y ^ 2 = mg_heat hA (2 * t) x x := by
  rw [two_mul, ← mg_heat_semigroup]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sq, mg_heat_symm hA t y x]

theorem mg_heat_diag_nonneg (hA : A.IsHermitian) (t : ℝ) (x : ι) : 0 ≤ mg_heat hA t x x := by
  rw [mg_heat_apply]
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (mul_self_nonneg _) (Real.exp_pos _).le

theorem mg_heat_integrableOn (hA : A.PosDef) (x y : ι) :
    MeasureTheory.IntegrableOn (fun t => mg_heat hA.1 t x y) (Set.Ioi 0) := by
  simp_rw [mg_heat_apply]
  exact integrable_finsetSum _ fun K _ =>
    (integrableOn_exp_neg_mul_Ioi (hA.eigenvalues_pos K)).const_mul _

/-- **∫₀^∞ p_t dt = A⁻¹.** -/
theorem mg_integral_heat (hA : A.PosDef) (x y : ι) :
    ∫ t in Set.Ioi (0 : ℝ), mg_heat hA.1 t x y = A⁻¹ x y := by
  rw [mg_inv_spectral hA, mg_conj_apply]
  simp_rw [mg_heat_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun K _ => ?_
    rw [integral_const_mul, integral_exp_neg_mul_Ioi (hA.eigenvalues_pos K)]
  · intro K _
    exact (integrableOn_exp_neg_mul_Ioi (hA.eigenvalues_pos K)).const_mul _

/-- **The rough covariance:** ∫_{(0,T]} p_t dt = U diag((1 − e^{−Tλ})/λ) Uᵀ (T ≥ 0). -/
theorem mg_integral_heat_Ioc (hA : A.PosDef) {T : ℝ} (hT : 0 ≤ T) (x y : ι) :
    ∫ t in Set.Ioc 0 T, mg_heat hA.1 t x y =
      (mg_U hA.1 * diagonal (fun K => (1 - Real.exp (-(T * hA.1.eigenvalues K))) /
        hA.1.eigenvalues K) * (mg_U hA.1)ᵀ) x y := by
  rw [mg_conj_apply]
  simp_rw [mg_heat_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun K _ => ?_
    rw [integral_const_mul, glp_integral_exp_Ioc (hA.eigenvalues_pos K) hT]
  · intro K _
    exact ((integrableOn_exp_neg_mul_Ioi (hA.eigenvalues_pos K)).mono_set
      Set.Ioc_subset_Ioi_self).const_mul _

/-- The two halves of the heat split in matrix form: M diag(β²) Mᵀ = ∫_{(0,t]} p_s ds and
M diag(α²) Mᵀ = p_t A⁻¹, with α² = e^{−tλ}, β² = 1 − e^{−tλ} (so they add up to A⁻¹). -/
theorem mg_rough_cov (hA : A.PosDef) {t : ℝ} (ht : 0 ≤ t) (x y : ι) :
    (mg_modeMat hA * diagonal (fun K => 1 - Real.exp (-(t * hA.1.eigenvalues K))) *
      (mg_modeMat hA)ᵀ) x y = ∫ s in Set.Ioc 0 t, mg_heat hA.1 s x y := by
  rw [mg_integral_heat_Ioc hA ht, mg_modeMat, transpose_mul, diagonal_transpose,
    show mg_U hA.1 * diagonal (mg_coef hA) * diagonal (fun K => 1 - Real.exp
      (-(t * hA.1.eigenvalues K))) * (diagonal (mg_coef hA) * (mg_U hA.1)ᵀ) =
      mg_U hA.1 * (diagonal (mg_coef hA) * diagonal (fun K => 1 - Real.exp
      (-(t * hA.1.eigenvalues K))) * diagonal (mg_coef hA)) * (mg_U hA.1)ᵀ by
      simp only [Matrix.mul_assoc],
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  rw [mg_conj_apply, mg_conj_apply]
  refine Finset.sum_congr rfl fun K _ => ?_
  have := mg_coef_sq hA K
  have hl := (hA.eigenvalues_pos K).ne'
  congr 1
  field_simp
  linear_combination (1 - Real.exp (-(t * hA.1.eigenvalues K))) * this

theorem mg_smooth_cov (hA : A.PosDef) (t : ℝ) :
    mg_modeMat hA * diagonal (fun K => Real.exp (-(t * hA.1.eigenvalues K))) *
      (mg_modeMat hA)ᵀ = mg_heat hA.1 t * A⁻¹ := by
  rw [mg_inv_spectral hA, mg_heat, mg_conj_mul, mg_modeMat, transpose_mul, diagonal_transpose,
    show mg_U hA.1 * diagonal (mg_coef hA) * diagonal (fun K => Real.exp
      (-(t * hA.1.eigenvalues K))) * (diagonal (mg_coef hA) * (mg_U hA.1)ᵀ) =
      mg_U hA.1 * (diagonal (mg_coef hA) * diagonal (fun K => Real.exp
      (-(t * hA.1.eigenvalues K))) * diagonal (mg_coef hA)) * (mg_U hA.1)ᵀ by
      simp only [Matrix.mul_assoc],
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  ext x y
  rw [mg_conj_apply, mg_conj_apply]
  refine Finset.sum_congr rfl fun K _ => ?_
  have := mg_coef_sq hA K
  have hl := (hA.eigenvalues_pos K).ne'
  congr 1
  field_simp
  linear_combination this

end Generic

/-! ## The heat kernel as a matrix exponential; Z-matrix domain monotonicity -/

section HeatExp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If A V = V diag(μ) with Vᵀ V = 1, then exp(−t A) = V diag(e^{−tμ}) Vᵀ. -/
theorem mg_exp_conj {A V : Matrix ι ι ℝ} (hV : Vᵀ * V = 1) (μ : ι → ℝ)
    (hAV : A * V = V * diagonal μ) (t : ℝ) :
    NormedSpace.exp (-t • A) = V * diagonal (fun K => Real.exp (-(t * μ K))) * Vᵀ := by
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
  have hinv : V⁻¹ = Vᵀ := inv_eq_left_inv hV
  have hdet : V.det ≠ 0 := by
    intro h
    have := congrArg det hV
    rw [det_mul, det_transpose, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hu : IsUnit V := (isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hAeq : A = V * diagonal μ * Vᵀ := by rw [← hAV, Matrix.mul_assoc, hV', Matrix.mul_one]
  have hd : diagonal (fun K => -(t * μ K)) = (-t) • diagonal μ := by
    rw [← diagonal_smul]
    congr 1
    funext K
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : -t • A = V * diagonal (fun K => -(t * μ K)) * V⁻¹ := by
    rw [hinv, hd, Matrix.mul_smul, Matrix.smul_mul, ← hAeq]
  have he : (NormedSpace.exp fun K => -(t * μ K)) = fun K => Real.exp (-(t * μ K)) := by
    funext K
    rw [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]
  rw [h1, Matrix.exp_conj V _ hu, Matrix.exp_diagonal, hinv, he]

/-- The spectral heat kernel is the matrix exponential: p_t = exp(−t A). -/
theorem mg_heat_eq_exp {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (t : ℝ) :
    mg_heat hA t = NormedSpace.exp (-t • A) :=
  (mg_exp_conj (mg_U_transpose_mul hA) _ (mg_mul_U hA) t).symm

omit [Fintype ι] in
theorem mg_smul_one_eq_diagonal (c : ℝ) : c • (1 : Matrix ι ι ℝ) = diagonal (fun _ => c) := by
  rw [← diagonal_one, ← diagonal_smul]
  congr 1
  funext i
  simp

/-- exp(c 1 + N) = e^c exp N. -/
theorem mg_exp_scalar_add (c : ℝ) (N : Matrix ι ι ℝ) :
    NormedSpace.exp (c • (1 : Matrix ι ι ℝ) + N) = Real.exp c • NormedSpace.exp N := by
  rw [Matrix.exp_add_of_commute _ _ ((Commute.one_left N).smul_left c)]
  have h : NormedSpace.exp (c • (1 : Matrix ι ι ℝ)) = Real.exp c • 1 := by
    rw [mg_smul_one_eq_diagonal, Matrix.exp_diagonal, mg_smul_one_eq_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]
  rw [h, Matrix.smul_mul, Matrix.one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Entrywise exponential series: exp(X)(x, y) = Σ_j (X^j)(x, y)/j!. -/
theorem mg_exp_apply_hasSum (X : Matrix ι ι ℝ) (x y : ι) :
    HasSum (fun j : ℕ => ((j.factorial : ℝ))⁻¹ * (X ^ j) x y) (NormedSpace.exp X x y) := by
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp h x) y
  simpa only [Matrix.smul_apply, smul_eq_mul] using h2

theorem mg_pow_nonneg {N : Matrix ι ι ℝ} (hN : ∀ i j, 0 ≤ N i j) (j : ℕ) (x y : ι) :
    0 ≤ (N ^ j) x y := by
  induction j generalizing y with
  | zero =>
    rw [pow_zero, one_apply]
    split_ifs <;> norm_num
  | succ j ih =>
    rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (hN z y)

/-- Powers of a nonnegative matrix dominate the powers of its principal submatrices. -/
theorem mg_pow_submatrix_le {N : Matrix ι ι ℝ} (hN : ∀ i j, 0 ≤ N i j) (B : Finset ι) (j : ℕ)
    (x y : {z // z ∈ B}) :
    ((N.submatrix Subtype.val Subtype.val) ^ j) x y ≤ (N ^ j) x y := by
  induction j generalizing y with
  | zero =>
    rw [pow_zero, pow_zero, one_apply, one_apply]
    by_cases h : x = y
    · simp [h]
    · have h' : (x : ι) ≠ y := fun e => h (Subtype.ext e)
      simp [h, h']
  | succ j ih =>
    rw [pow_succ, pow_succ, mul_apply, mul_apply]
    calc ∑ z : {z // z ∈ B}, ((N.submatrix Subtype.val Subtype.val) ^ j) x z *
          N.submatrix Subtype.val Subtype.val z y
        ≤ ∑ z : {z // z ∈ B}, (N ^ j) x z * N z y := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [submatrix_apply]
          exact mul_le_mul_of_nonneg_right (ih z) (hN _ _)
      _ = ∑ z ∈ B, (N ^ j) x z * N z y :=
          Finset.sum_coe_sort B (fun z => (N ^ j) x z * N z y)
      _ ≤ ∑ z, (N ^ j) x z * N z y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
            (fun z _ _ => mul_nonneg (mg_pow_nonneg hN j _ _) (hN _ _))

theorem mg_exp_nonneg {N : Matrix ι ι ℝ} (hN : ∀ i j, 0 ≤ N i j) {s : ℝ} (hs : 0 ≤ s)
    (x y : ι) : 0 ≤ NormedSpace.exp (s • N) x y := by
  refine (mg_exp_apply_hasSum (s • N) x y).nonneg fun j => ?_
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hs _) (mg_pow_nonneg hN j x y))

theorem mg_exp_submatrix_le {N : Matrix ι ι ℝ} (hN : ∀ i j, 0 ≤ N i j) (B : Finset ι) {s : ℝ}
    (hs : 0 ≤ s) (x y : {z // z ∈ B}) :
    NormedSpace.exp (s • N.submatrix Subtype.val Subtype.val) x y ≤
      NormedSpace.exp (s • N) x y := by
  refine hasSum_le (fun j => ?_) (mg_exp_apply_hasSum _ x y)
    (mg_exp_apply_hasSum (s • N) (x : ι) y)
  rw [smul_pow, smul_pow, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mg_pow_submatrix_le hN B j x y) (pow_nonneg hs _))
    (by positivity)

/-- **Domain monotonicity of the heat kernel (generic, Z-matrices).** Let A be symmetric with
nonpositive off-diagonal entries, B a set of indices and A_B = A|_{B×B} (Dirichlet restriction).
Then for t ≥ 0 and x, y ∈ B: 0 ≤ p^{A_B}_t(x, y) ≤ p^A_t(x, y). -/
theorem mg_heat_submatrix_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (B : Finset ι)
    (hAB : (A.submatrix (Subtype.val : {z // z ∈ B} → ι) Subtype.val).IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) (x y : {z // z ∈ B}) :
    0 ≤ mg_heat hAB t x y ∧ mg_heat hAB t x y ≤ mg_heat hA t x y := by
  set c : ℝ := ∑ i, |A i i| with hc
  set N : Matrix ι ι ℝ := c • 1 - A with hNdef
  have hN : ∀ i j, 0 ≤ N i j := by
    intro i j
    simp only [hNdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, mul_one, sub_nonneg]
      exact (le_abs_self _).trans
        (Finset.single_le_sum (f := fun i => |A i i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i))
    · rw [one_apply_ne h, mul_zero, zero_sub]
      exact neg_nonneg.mpr (hoff i j h)
  have e1 : -t • A = (-(t * c)) • (1 : Matrix ι ι ℝ) + t • N := by
    rw [hNdef, smul_sub, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have e2 : -t • A.submatrix (Subtype.val : {z // z ∈ B} → ι) Subtype.val =
      (-(t * c)) • (1 : Matrix {z // z ∈ B} {z // z ∈ B} ℝ) +
        t • N.submatrix Subtype.val Subtype.val := by
    ext i j
    simp only [hNdef, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      submatrix_apply]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, one_apply_eq]
      ring
    · have h' : (i : ι) ≠ j := fun e => h (Subtype.ext e)
      rw [one_apply_ne h, one_apply_ne h']
      ring
  rw [mg_heat_eq_exp, mg_heat_eq_exp, e1, e2, mg_exp_scalar_add, mg_exp_scalar_add,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  exact ⟨mul_nonneg (Real.exp_pos _).le (mg_exp_nonneg (N := N.submatrix Subtype.val Subtype.val)
    (fun i j => hN i.1 j.1) ht x y),
    mul_le_mul_of_nonneg_left (mg_exp_submatrix_le hN B ht x y) (Real.exp_pos _).le⟩

end HeatExp

/-! ## Specialisation to the box and to regions B -/

section Region

open Set

variable {n k : ℕ}

/-- The box heat kernel of PP2Heat is the matrix exponential exp(−t dirOp). -/
theorem mg_heatK_eq_exp (m₀ t : ℝ) :
    (heatK n k m₀ t : Matrix (DSite n k) (DSite n k) ℝ) = NormedSpace.exp (-t • dirOp n k m₀) := by
  rw [mg_exp_conj sineMat_transpose_mul (dirEig n k m₀) (dirOp_mul_sineMat m₀) t]
  ext x y
  rw [mg_conj_apply]
  rfl

theorem mg_heat_dirOp (m₀ t : ℝ) (x y : DSite n k) :
    mg_heat (dirOp_isHermitian m₀) t x y = heatK n k m₀ t x y := by
  rw [mg_heat_eq_exp, ← mg_heatK_eq_exp]

theorem mg_regionOp_isHermitian (m₀ : ℝ) (B : Finset (DSite n k)) :
    (regionOp n k m₀ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, regionOp, transpose_submatrix,
    dirOp_transpose]

/-- The heat kernel of the region B (Dirichlet on Bᶜ): p^B_t = exp(−t regionOp B). -/
def mg_regionHeat (n k : ℕ) (m₀ t : ℝ) (B : Finset (DSite n k)) :
    Matrix {x // x ∈ B} {x // x ∈ B} ℝ :=
  mg_heat (mg_regionOp_isHermitian m₀ B) t

/-- **Domain monotonicity of the heat kernel:** for t ≥ 0 and x, y ∈ B,
0 ≤ p^B_t(x, y) ≤ p_t(x, y) (box heat kernel `heatK`). Any m₀, any region B. -/
theorem mg_regionHeat_le (m₀ : ℝ) (B : Finset (DSite n k)) {t : ℝ} (ht : 0 ≤ t)
    (x y : {z // z ∈ B}) :
    0 ≤ mg_regionHeat n k m₀ t B x y ∧ mg_regionHeat n k m₀ t B x y ≤ heatK n k m₀ t x y := by
  have h := mg_heat_submatrix_le (dirOp_isHermitian m₀)
    (fun i j hij => dirOp_offDiag_nonpos m₀ hij) B (mg_regionOp_isHermitian m₀ B) ht x y
  rw [mg_heat_dirOp] at h
  exact h

/-- **Region diagonal heat bound:** ε⁻² p^B_t(x, x) ≤ e^{−t m₀²} π/(4t) for t > 0, uniformly
in n, k, B, x. -/
theorem mg_regionHeat_diag_le (m₀ : ℝ) (B : Finset (DSite n k)) {t : ℝ} (ht : 0 < t)
    (x : {z // z ∈ B}) :
    (spacing n ^ 2)⁻¹ * mg_regionHeat n k m₀ t B x x ≤ exp (-(t * m₀ ^ 2)) * (π / (4 * t)) :=
  (mul_le_mul_of_nonneg_left (mg_regionHeat_le m₀ B ht.le x x).2 (by positivity)).trans
    (glp_heatK_diag_le m₀ ht (x : DSite n k))

theorem mg_regionHeat_semigroup (m₀ t s : ℝ) (B : Finset (DSite n k)) (x y : {z // z ∈ B}) :
    ∑ z, mg_regionHeat n k m₀ t B x z * mg_regionHeat n k m₀ s B z y =
      mg_regionHeat n k m₀ (t + s) B x y :=
  mg_heat_semigroup _ t s x y

theorem mg_regionHeat_sq_sum (m₀ t : ℝ) (B : Finset (DSite n k)) (x : {z // z ∈ B}) :
    ∑ y, mg_regionHeat n k m₀ t B x y ^ 2 = mg_regionHeat n k m₀ (2 * t) B x x :=
  mg_heat_sq_sum _ t x

/-- ∫₀^∞ p^B_t dt = regionGreen B (m₀ ≠ 0). -/
theorem mg_integral_regionHeat {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (x y : {z // z ∈ B}) :
    ∫ t in Ioi (0 : ℝ), mg_regionHeat n k m₀ t B x y = regionGreen n k m₀ B x y :=
  mg_integral_heat (fv2_regionOp_posDef hm B) x y

/-- The rough part of the region covariance, C^B_r(T)(x, y) = ε⁻² ∫_{(0,T]} p^B_t(x, y) dt. -/
def mg_regionRough (n k : ℕ) (m₀ T : ℝ) (B : Finset (DSite n k)) (x y : {z // z ∈ B}) : ℝ :=
  (spacing n ^ 2)⁻¹ * ∫ t in Ioc 0 T, mg_regionHeat n k m₀ t B x y

/-- 0 ≤ C^B_r(T)(x, y) ≤ C_r(T)(x, y) (the box rough part `glp_roughCov`), any m₀, T. -/
theorem mg_regionRough_le (m₀ T : ℝ) (B : Finset (DSite n k)) (x y : {z // z ∈ B}) :
    0 ≤ mg_regionRough n k m₀ T B x y ∧ mg_regionRough n k m₀ T B x y ≤ glp_roughCov n k m₀ T x y := by
  have hε : 0 ≤ (spacing n ^ 2)⁻¹ := by positivity
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] fun t => mg_regionHeat n k m₀ t B x y :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => (mg_regionHeat_le m₀ B ht.1.le x y).1
  refine ⟨mul_nonneg hε (integral_nonneg_of_ae hnn), mul_le_mul_of_nonneg_left ?_ hε⟩
  exact integral_mono_of_nonneg hnn
    ((glp_heatK_integrableOn m₀ (x : DSite n k) (y : DSite n k)).mono_set Ioc_subset_Ioi_self)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => (mg_regionHeat_le m₀ B ht.1.le x y).2)

/-- **F3, rough part, region version:** for every m₀, T ≥ 0, natural p ≥ 2, uniformly in
n, k, B, x: ε² Σ_{y ∈ B} |C^B_r(T)(x, y)|^p ≤ (π/4)^{p−1}/2 · p^p · T. -/
theorem mg_regionRough_Lp_le (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (p : ℕ) (hp : 2 ≤ p)
    (B : Finset (DSite n k)) (x : {z // z ∈ B}) :
    spacing n ^ 2 * ∑ y, |mg_regionRough n k m₀ T B x y| ^ p ≤
      (π / 4) ^ (p - 1) / 2 * (p : ℝ) ^ p * T := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (glp_roughCov_Lp_le m₀ hT p hp (x : DSite n k))
  calc ∑ y : {z // z ∈ B}, |mg_regionRough n k m₀ T B x y| ^ p
      ≤ ∑ y : {z // z ∈ B}, |glp_roughCov n k m₀ T x y| ^ p := by
        refine Finset.sum_le_sum fun y _ => pow_le_pow_left₀ (abs_nonneg _) ?_ p
        have h := mg_regionRough_le m₀ T B x y
        rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
        exact h.2
    _ = ∑ y ∈ B, |glp_roughCov n k m₀ T x y| ^ p :=
        Finset.sum_coe_sort B (fun y => |glp_roughCov n k m₀ T x y| ^ p)
    _ ≤ ∑ y, |glp_roughCov n k m₀ T x y| ^ p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
          (fun _ _ _ => pow_nonneg (abs_nonneg _) _)

/-- **F3, full Green function, region version:** m₀ ≠ 0, natural p ≥ 2, uniformly in n, k, B, x:
ε² Σ_{y ∈ B} (ε⁻² regionGreen B x y)^p ≤ (π/4)^{p−1}/2 · Γ(1/p)^p / m₀². -/
theorem mg_regionGreen_Lp_le {m₀ : ℝ} (hm : m₀ ≠ 0) (p : ℕ) (hp : 2 ≤ p)
    (B : Finset (DSite n k)) (x : {z // z ∈ B}) :
    spacing n ^ 2 * ∑ y, ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ B x y) ^ p ≤
      (π / 4) ^ (p - 1) / 2 * Gamma ((p : ℝ)⁻¹) ^ p / m₀ ^ 2 := by
  have hε : 0 ≤ (spacing n ^ 2)⁻¹ := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) (glp_dirGreen_Lp_le hm p hp (x : DSite n k))
  calc ∑ y : {z // z ∈ B}, ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ B x y) ^ p
      ≤ ∑ y : {z // z ∈ B}, ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ p := by
        refine Finset.sum_le_sum fun y _ => pow_le_pow_left₀
          (mul_nonneg hε (rg_regionGreen_nonneg hm B x y)) ?_ p
        exact mul_le_mul_of_nonneg_left (fv2_regionGreen_le_dirGreen hm B x y) hε
    _ = ∑ y ∈ B, ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ p :=
        Finset.sum_coe_sort B (fun y => ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ p)
    _ ≤ ∑ y, ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
          (fun _ _ _ => pow_nonneg (mul_nonneg hε (dirGreen_nonneg hm _ _)) _)

/-! ### G1 for regions: A = rg_scaledOp B = ε² regionOp B -/

/-- **G1 (region):** for m₀ ≠ 0, every region B and every F : (B → ℝ) → ℝ, the normalised free
region measure (density qweight m₀ 0 (zeroExt B ψ) = exp(−½ ε² ψ·regionOp ψ)) is the law of
M ξ, M = U diag(λ^{−1/2}) from the eigenvector basis of rg_scaledOp B, ξ ~ γ^B. -/
theorem mg_region_gauss_modes {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (F : ({x // x ∈ B} → ℝ) → ℝ) :
    (∫ ψ, F ψ * qweight n k m₀ 0 (zeroExt B ψ)) / (∫ ψ, qweight n k m₀ 0 (zeroExt B ψ)) =
      ∫ ξ, F (mg_modeMat (rg_scaledOp_posDef hm B) *ᵥ ξ)
        ∂Measure.pi (fun _ : {x // x ∈ B} => gaussianReal 0 1) := by
  simp_rw [rg_qweight_zeroExt, PP2GaussIBP.gaussWeight]
  exact mg_gauss_modes (rg_scaledOp_posDef hm B) F

/-- **G1 split (region):** α_K = e^{−τλ_K/2} (τ ≥ 0, λ_K the eigenvalues of rg_scaledOp B, i.e.
ε² × those of regionOp B, so α_K² = e^{−t λ_K^{phys}} with t = ε²τ). -/
theorem mg_region_heat_split {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (τ : ℝ)
    (hτ : 0 ≤ τ) (F : ({x // x ∈ B} → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ψ, F ψ * qweight n k m₀ 0 (zeroExt B ψ)) / (∫ ψ, qweight n k m₀ 0 (zeroExt B ψ)) =
      ∫ p, F (mg_modeMat (rg_scaledOp_posDef hm B) *ᵥ
            (fun K => Real.exp (-(τ * (rg_scaledOp_posDef hm B).1.eigenvalues K) / 2) * p.1 K) +
          mg_modeMat (rg_scaledOp_posDef hm B) *ᵥ
            (fun K => √(1 - Real.exp (-(τ * (rg_scaledOp_posDef hm B).1.eigenvalues K))) * p.2 K))
        ∂((Measure.pi (fun _ : {x // x ∈ B} => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : {x // x ∈ B} => gaussianReal 0 1))) := by
  simp_rw [rg_qweight_zeroExt, PP2GaussIBP.gaussWeight]
  exact mg_heat_split (rg_scaledOp_posDef hm B) τ hτ F hF

/-- The heat kernel of rg_scaledOp at time τ is p^B at physical time ε²τ. -/
theorem mg_heat_scaledOp {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (τ : ℝ) :
    mg_heat (rg_scaledOp_posDef hm B).1 τ = mg_regionHeat n k m₀ (spacing n ^ 2 * τ) B := by
  rw [mg_regionHeat, mg_heat_eq_exp, mg_heat_eq_exp, rg_scaledOp, smul_smul]
  congr 2
  ring

/-- **Rough covariance of the region split:** with M, λ from rg_scaledOp B and τ ≥ 0,
M diag(1 − e^{−τλ}) Mᵀ = C^B_r(ε²τ) (the physical rough part at time t = ε²τ). -/
theorem mg_region_rough_cov {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {τ : ℝ}
    (hτ : 0 ≤ τ) (x y : {z // z ∈ B}) :
    (mg_modeMat (rg_scaledOp_posDef hm B) *
      diagonal (fun K => 1 - Real.exp (-(τ * (rg_scaledOp_posDef hm B).1.eigenvalues K))) *
      (mg_modeMat (rg_scaledOp_posDef hm B))ᵀ) x y =
      mg_regionRough n k m₀ (spacing n ^ 2 * τ) B x y := by
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  rw [mg_rough_cov _ hτ, mg_regionRough]
  simp_rw [mg_heat_scaledOp hm B]
  rw [← intervalIntegral.integral_of_le hτ,
    ← intervalIntegral.integral_of_le (mul_nonneg (pow_nonneg (spacing_pos n).le 2) hτ),
    intervalIntegral.integral_comp_mul_left (fun u => mg_regionHeat n k m₀ u B x y) hε,
    mul_zero, smul_eq_mul]

/-- **Region rough-part Lᵖ bound for the split:** ε² Σ_{y ∈ B} |(M diag(1 − e^{−τλ}) Mᵀ)(x, y)|^p
≤ (π/4)^{p−1}/2 · p^p · ε²τ (τ ≥ 0, natural p ≥ 2), uniformly in n, k, B, x. -/
theorem mg_region_rough_cov_Lp_le {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {τ : ℝ}
    (hτ : 0 ≤ τ) (p : ℕ) (hp : 2 ≤ p) (x : {z // z ∈ B}) :
    spacing n ^ 2 * ∑ y, |(mg_modeMat (rg_scaledOp_posDef hm B) *
      diagonal (fun K => 1 - Real.exp (-(τ * (rg_scaledOp_posDef hm B).1.eigenvalues K))) *
      (mg_modeMat (rg_scaledOp_posDef hm B))ᵀ) x y| ^ p ≤
      (π / 4) ^ (p - 1) / 2 * (p : ℝ) ^ p * (spacing n ^ 2 * τ) := by
  simp_rw [mg_region_rough_cov hm B hτ]
  exact mg_regionRough_Lp_le m₀ (mul_nonneg (pow_nonneg (spacing_pos n).le 2) hτ) p hp B x

end Region

end PP2Target

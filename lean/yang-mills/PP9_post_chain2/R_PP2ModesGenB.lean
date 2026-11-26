import LongTable.R_PP2ModesGenA

/-!
Part B of PP2ModesGen (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2ModesGen.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
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

end HeatExp

end PP2Target

end

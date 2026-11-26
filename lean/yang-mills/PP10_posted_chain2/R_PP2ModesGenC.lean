import LongTable.R_PP2ModesGenB

/-!
Part C of PP2ModesGen (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2ModesGen.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
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

section HeatExp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

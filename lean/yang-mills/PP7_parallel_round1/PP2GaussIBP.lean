import Mathlib

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (Brydges–Fröhlich–Spencer route).
Node M4: Gaussian integration by parts in finite dimension.

Setting: `ι` a finite type, `A : Matrix ι ι ℝ` positive definite (`Matrix.PosDef`, which includes
symmetry), Gaussian weight `ρ_A(φ) = exp(−½ φ ⬝ᵥ A *ᵥ φ)` on `ι → ℝ` with Lebesgue measure.
The partial derivative `∂_x F (φ)` is `fderiv ℝ F φ (Pi.single x 1)`.

Growth hypothesis (covers bounded and polynomially bounded functions):
`|F φ| ≤ C · exp(a · ∑ i, |φ i|)` and the same bound for the relevant partial derivatives;
`F` is assumed `Differentiable` (no continuity of the derivative is needed).

FORMALIZED:
* `exists_coercive`: ∃ c > 0, c · ∑ φᵢ² ≤ φ ⬝ᵥ A *ᵥ φ.
* `integrable_expAbs_mul_gaussWeight`: exp(a ∑|φᵢ|) · ρ_A is integrable, for every real `a`.
* `hasLineDerivAt_gaussWeight`: the derivative of ρ_A along `e_x` is `−(A *ᵥ φ) x · ρ_A φ`.
* `gauss_ibp`: ∫ (A *ᵥ φ) x · F φ · ρ_A φ = ∫ ∂_x F φ · ρ_A φ.
* `gauss_ibp_cov`: with covariance Σ = A⁻¹ (not the growth constant C),
  ∫ φ x · F φ · ρ_A φ = ∑_y Σ x y · ∫ ∂_y F φ · ρ_A φ.
* integrability of all the integrands involved (`integrable_of_le_expAbs`, `integrable_ibp_*`).

NOT formalized: normalization by `∫ ρ_A` (the identities are stated for the unnormalized weight,
and are linear in it, so they hold verbatim for the normalized Gaussian measure); Wick/higher
moment formulas; infinite-dimensional or lattice-specific instances.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Matrix

noncomputable section

namespace PP2GaussIBP

variable {ι : Type*} [Fintype ι]

/-- The unnormalized Gaussian weight `exp(−½ φ ⬝ᵥ A *ᵥ φ)`. -/
def gaussWeight (A : Matrix ι ι ℝ) (φ : ι → ℝ) : ℝ :=
  Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)

theorem continuous_quad (A : Matrix ι ι ℝ) : Continuous fun φ : ι → ℝ => φ ⬝ᵥ A *ᵥ φ := by
  simp only [dotProduct, mulVec]
  fun_prop

theorem continuous_gaussWeight (A : Matrix ι ι ℝ) : Continuous (gaussWeight A) := by
  unfold gaussWeight
  exact Real.continuous_exp.comp (((continuous_quad A).neg).div_const 2)

theorem quad_smul (A : Matrix ι ι ℝ) (r : ℝ) (φ : ι → ℝ) :
    (r • φ) ⬝ᵥ A *ᵥ (r • φ) = r ^ 2 * (φ ⬝ᵥ A *ᵥ φ) := by
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- Coercivity of a positive definite quadratic form. -/
theorem exists_coercive {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ c > 0, ∀ φ : ι → ℝ, c * ∑ i, φ i ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun φ => ?_⟩
    simp [dotProduct]
  have hS : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨fun _ => 1, by simp [pi_norm_const]⟩
  obtain ⟨φ₀, hφ₀S, hmin⟩ := hS.exists_isMinOn hne (continuous_quad A).continuousOn
  have hφ₀ : φ₀ ≠ 0 := by
    intro h
    rw [h] at hφ₀S
    simp at hφ₀S
  set c₀ := φ₀ ⬝ᵥ A *ᵥ φ₀ with hc₀
  have hc₀pos : 0 < c₀ := by
    have := hA.dotProduct_mulVec_pos hφ₀
    simpa using this
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨c₀ / Fintype.card ι, div_pos hc₀pos hcard, fun φ => ?_⟩
  rcases eq_or_ne φ 0 with rfl | hφ
  · simp
  set r := ‖φ‖ with hr
  have hrpos : 0 < r := norm_pos_iff.mpr hφ
  have hψ : r⁻¹ • φ ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp only [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, ← hr]
    rw [Real.norm_of_nonneg hrpos.le]
    exact inv_mul_cancel₀ hrpos.ne'
  have h1 : c₀ ≤ (r⁻¹ • φ) ⬝ᵥ A *ᵥ (r⁻¹ • φ) := hmin hψ
  rw [quad_smul] at h1
  have h2 : c₀ * r ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ := by
    have hr2 : 0 < r ^ 2 := by positivity
    have : r ^ 2 * (r⁻¹ ^ 2 * (φ ⬝ᵥ A *ᵥ φ)) = φ ⬝ᵥ A *ᵥ φ := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hr2.le]
  have h3 : ∑ i, φ i ^ 2 ≤ Fintype.card ι * r ^ 2 := by
    have : ∀ i ∈ Finset.univ, φ i ^ 2 ≤ r ^ 2 := by
      intro i _
      have hi : |φ i| ≤ r := by
        have := norm_le_pi_norm φ i
        rwa [Real.norm_eq_abs] at this
      have := abs_nonneg (φ i)
      nlinarith [sq_abs (φ i)]
    calc ∑ i, φ i ^ 2 ≤ ∑ _i : ι, r ^ 2 := Finset.sum_le_sum this
      _ = Fintype.card ι * r ^ 2 := by simp
  calc c₀ / Fintype.card ι * ∑ i, φ i ^ 2 ≤ c₀ / Fintype.card ι * (Fintype.card ι * r ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (div_pos hc₀pos hcard).le
    _ = c₀ * r ^ 2 := by field_simp
    _ ≤ _ := h2

/-- The key integrability statement: `exp(a ∑|φᵢ|) · ρ_A` is integrable for every `a`. -/
theorem integrable_expAbs_mul_gaussWeight {A : Matrix ι ι ℝ} (hA : A.PosDef) (a : ℝ) :
    Integrable (fun φ : ι → ℝ => Real.exp (a * ∑ i, |φ i|) * gaussWeight A φ) := by
  obtain ⟨c, hc, hcoer⟩ := exists_coercive hA
  have hb : 0 < c / 4 := by positivity
  have hint : Integrable (fun φ : ι → ℝ =>
      ∏ i, (Real.exp (a ^ 2 / c) * Real.exp (-(c / 4) * φ i ^ 2))) := by
    have := Integrable.fintype_prod (ι := ι) (E := ℝ) (𝕜 := ℝ)
      (μ := fun _ => (volume : Measure ℝ))
      (f := fun _ y => Real.exp (a ^ 2 / c) * Real.exp (-(c / 4) * y ^ 2))
      (fun _ => (integrable_exp_neg_mul_sq hb).const_mul _)
    exact this
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun φ => ?_)
  · exact (Continuous.mul (by fun_prop) (continuous_gaussWeight A)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by unfold gaussWeight; positivity)]
    unfold gaussWeight
    rw [← Real.exp_add]
    calc Real.exp (a * ∑ i, |φ i| + -(φ ⬝ᵥ A *ᵥ φ) / 2)
        ≤ Real.exp (∑ i, (a * |φ i| - c / 2 * φ i ^ 2)) := by
          apply Real.exp_le_exp.mpr
          have := hcoer φ
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          linarith
      _ = ∏ i, Real.exp (a * |φ i| - c / 2 * φ i ^ 2) := Real.exp_sum _ _
      _ ≤ ∏ i, (Real.exp (a ^ 2 / c) * Real.exp (-(c / 4) * φ i ^ 2)) := by
          apply Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le)
          intro i _
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have key : a * |φ i| ≤ a ^ 2 / c + c / 4 * φ i ^ 2 := by
            rw [div_add' _ _ _ hc.ne', le_div_iff₀ hc, ← sq_abs (φ i)]
            nlinarith [sq_nonneg (c * |φ i| / 2 - a)]
          linarith

/-- Domination by `K · exp(a ∑|φᵢ|) · ρ_A` gives integrability. -/
theorem integrable_of_le_expAbs {A : Matrix ι ι ℝ} (hA : A.PosDef) {h : (ι → ℝ) → ℝ}
    (hm : AEStronglyMeasurable h volume) (K a : ℝ)
    (hle : ∀ φ, |h φ| ≤ K * (Real.exp (a * ∑ i, |φ i|) * gaussWeight A φ)) :
    Integrable h :=
  ((integrable_expAbs_mul_gaussWeight hA a).const_mul K).mono' hm
    (Filter.Eventually.of_forall fun φ => by rw [Real.norm_eq_abs]; exact hle φ)

theorem gaussWeight_nonneg (A : Matrix ι ι ℝ) (φ : ι → ℝ) : 0 ≤ gaussWeight A φ := by
  unfold gaussWeight; positivity

theorem abs_mulVec_le (A : Matrix ι ι ℝ) (x : ι) (φ : ι → ℝ) :
    |(A *ᵥ φ) x| ≤ (∑ y, |A x y|) * Real.exp (∑ i, |φ i|) := by
  have hS : 0 ≤ ∑ y, |A x y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc |(A *ᵥ φ) x| = |∑ y, A x y * φ y| := rfl
    _ ≤ ∑ y, |A x y * φ y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, |A x y| * |φ y| := by simp [abs_mul]
    _ ≤ ∑ y, (∑ z, |A x z|) * |φ y| := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun z => |A x z|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ y)) (abs_nonneg _)
    _ = (∑ z, |A x z|) * ∑ i, |φ i| := by rw [Finset.mul_sum]
    _ ≤ (∑ y, |A x y|) * Real.exp (∑ i, |φ i|) := by
        apply mul_le_mul_of_nonneg_left _ hS
        have := Real.add_one_le_exp (∑ i, |φ i|)
        linarith

theorem expand_quad (A : Matrix ι ι ℝ) (φ v : ι → ℝ) (t : ℝ) :
    (φ + t • v) ⬝ᵥ A *ᵥ (φ + t • v) =
      φ ⬝ᵥ A *ᵥ φ + t * (v ⬝ᵥ A *ᵥ φ + φ ⬝ᵥ A *ᵥ v) + t ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

omit [Fintype ι] in
theorem transpose_eq {A : Matrix ι ι ℝ} (hA : A.PosDef) : Aᵀ = A := by
  have h := hA.1
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

variable [DecidableEq ι]

/-- The derivative of the Gaussian weight along `e_x` is `−(A *ᵥ φ) x · ρ_A φ`. -/
theorem hasLineDerivAt_gaussWeight {A : Matrix ι ι ℝ} (hA : A.PosDef) (x : ι) (φ : ι → ℝ) :
    HasLineDerivAt ℝ (gaussWeight A) (-(A *ᵥ φ) x * gaussWeight A φ) φ (Pi.single x 1) := by
  set v : ι → ℝ := Pi.single x 1
  have hsym : φ ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ φ := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_eq hA, dotProduct_comm]
  have hv : v ⬝ᵥ A *ᵥ φ = (A *ᵥ φ) x := by
    simp [v]
  unfold HasLineDerivAt
  have hfun : (fun t : ℝ => gaussWeight A (φ + t • v)) = fun t : ℝ =>
      Real.exp (-(φ ⬝ᵥ A *ᵥ φ + t * (2 * (A *ᵥ φ) x) + t ^ 2 * (v ⬝ᵥ A *ᵥ v)) / 2) := by
    funext t
    unfold gaussWeight
    rw [expand_quad, hsym, hv]
    ring_nf
  rw [hfun]
  have hq : HasDerivAt (fun t : ℝ =>
      -(φ ⬝ᵥ A *ᵥ φ + t * (2 * (A *ᵥ φ) x) + t ^ 2 * (v ⬝ᵥ A *ᵥ v)) / 2)
      (-(A *ᵥ φ) x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * (0 : ℝ) ^ 1 * 1) 0 := h1.pow 2
    have := (((h1.mul_const (2 * (A *ᵥ φ) x)).const_add (φ ⬝ᵥ A *ᵥ φ)).add
      (h2.mul_const (v ⬝ᵥ A *ᵥ v))).neg.div_const 2
    convert this using 1
    ring
  have := hq.exp
  convert this using 1
  unfold gaussWeight
  simp only [zero_mul, add_zero, zero_pow two_ne_zero, mul_comm]

omit [DecidableEq ι] in
/-- Integrability of `(A *ᵥ φ) x · F φ · ρ_A φ` under the growth hypothesis. -/
theorem integrable_ibp_left {A : Matrix ι ι ℝ} (hA : A.PosDef) {F : (ι → ℝ) → ℝ}
    (hFc : Continuous F) (C a : ℝ) (hF : ∀ φ, |F φ| ≤ C * Real.exp (a * ∑ i, |φ i|)) (x : ι) :
    Integrable (fun φ => (A *ᵥ φ) x * F φ * gaussWeight A φ) := by
  refine integrable_of_le_expAbs hA ?_ ((∑ y, |A x y|) * C) (a + 1) (fun φ => ?_)
  · have : Continuous fun φ : ι → ℝ => (A *ᵥ φ) x := by
      simp only [mulVec, dotProduct]; fun_prop
    exact ((this.mul hFc).mul (continuous_gaussWeight A)).aestronglyMeasurable
  · have h1 := abs_mulVec_le A x φ
    have h2 := hF φ
    have hρ := gaussWeight_nonneg A φ
    have hS : 0 ≤ ∑ y, |A x y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [abs_mul, abs_mul, abs_of_nonneg hρ]
    have hexp : Real.exp ((a + 1) * ∑ i, |φ i|) =
        Real.exp (∑ i, |φ i|) * Real.exp (a * ∑ i, |φ i|) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have hm : |(A *ᵥ φ) x| * |F φ| ≤
        ((∑ y, |A x y|) * Real.exp (∑ i, |φ i|)) * (C * Real.exp (a * ∑ i, |φ i|)) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    calc |(A *ᵥ φ) x| * |F φ| * gaussWeight A φ
        ≤ ((∑ y, |A x y|) * Real.exp (∑ i, |φ i|)) * (C * Real.exp (a * ∑ i, |φ i|)) *
            gaussWeight A φ := mul_le_mul_of_nonneg_right hm hρ
      _ = _ := by ring

/-- Integrability of `∂_x F · ρ_A` under the growth hypothesis on `∂_x F`. -/
theorem integrable_ibp_right {A : Matrix ι ι ℝ} (hA : A.PosDef) (F : (ι → ℝ) → ℝ)
    (C a : ℝ) (x : ι)
    (hF' : ∀ φ, |fderiv ℝ F φ (Pi.single x 1)| ≤ C * Real.exp (a * ∑ i, |φ i|)) :
    Integrable (fun φ => fderiv ℝ F φ (Pi.single x 1) * gaussWeight A φ) := by
  refine integrable_of_le_expAbs hA ?_ C a (fun φ => ?_)
  · exact ((measurable_fderiv_apply_const ℝ F _).aestronglyMeasurable).mul
      (continuous_gaussWeight A).aestronglyMeasurable
  · rw [abs_mul, abs_of_nonneg (gaussWeight_nonneg A φ), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hF' φ) (gaussWeight_nonneg A φ)

/-- **Gaussian integration by parts.** For `F` differentiable with `F` and `∂_x F` bounded by
`C · exp(a ∑|φᵢ|)`:
`∫ (A *ᵥ φ) x · F φ · ρ_A φ = ∫ ∂_x F φ · ρ_A φ`. -/
theorem gauss_ibp {A : Matrix ι ι ℝ} (hA : A.PosDef) {F : (ι → ℝ) → ℝ}
    (hFd : Differentiable ℝ F) (C a : ℝ) (x : ι)
    (hF : ∀ φ, |F φ| ≤ C * Real.exp (a * ∑ i, |φ i|))
    (hF' : ∀ φ, |fderiv ℝ F φ (Pi.single x 1)| ≤ C * Real.exp (a * ∑ i, |φ i|)) :
    ∫ φ, (A *ᵥ φ) x * F φ * gaussWeight A φ =
      ∫ φ, fderiv ℝ F φ (Pi.single x 1) * gaussWeight A φ := by
  have hL := integrable_ibp_left hA hFd.continuous C a hF x
  have hR := integrable_ibp_right hA F C a x hF'
  have hFρ : Integrable (fun φ => F φ * gaussWeight A φ) := by
    refine integrable_of_le_expAbs hA
      (hFd.continuous.mul (continuous_gaussWeight A)).aestronglyMeasurable C a (fun φ => ?_)
    rw [abs_mul, abs_of_nonneg (gaussWeight_nonneg A φ), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hF φ) (gaussWeight_nonneg A φ)
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (ι → ℝ)))
    (f := F) (f' := fun φ => fderiv ℝ F φ (Pi.single x 1))
    (g := gaussWeight A) (g' := fun φ => -(A *ᵥ φ) x * gaussWeight A φ)
    (v := Pi.single x 1) (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simpa using hR)
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hL.neg)
    (by simpa using hFρ)
    (fun φ _ => (hFd φ).hasFDerivAt.hasLineDerivAt _)
    (fun φ _ => hasLineDerivAt_gaussWeight hA x φ)
  simp only [ContinuousLinearMap.mul_apply'] at key
  have e1 : (fun φ => F φ * (-(A *ᵥ φ) x * gaussWeight A φ)) =
      fun φ => -((A *ᵥ φ) x * F φ * gaussWeight A φ) := by
    funext φ; ring
  rw [e1, integral_neg] at key
  linarith

/-- **Gaussian integration by parts, covariance form.** With covariance Σ = A⁻¹ (not the growth
constant C): `∫ φ x · F φ · ρ_A φ = ∑_y Σ x y · ∫ ∂_y F φ · ρ_A φ`. -/
theorem gauss_ibp_cov {A : Matrix ι ι ℝ} (hA : A.PosDef) {F : (ι → ℝ) → ℝ}
    (hFd : Differentiable ℝ F) (C a : ℝ) (x : ι)
    (hF : ∀ φ, |F φ| ≤ C * Real.exp (a * ∑ i, |φ i|))
    (hF' : ∀ y φ, |fderiv ℝ F φ (Pi.single y 1)| ≤ C * Real.exp (a * ∑ i, |φ i|)) :
    ∫ φ, φ x * F φ * gaussWeight A φ =
      ∑ y, A⁻¹ x y * ∫ φ, fderiv ℝ F φ (Pi.single y 1) * gaussWeight A φ := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA.isUnit
  have hφ : ∀ φ : ι → ℝ, φ x = ∑ y, A⁻¹ x y * (A *ᵥ φ) y := by
    intro φ
    have : A⁻¹ *ᵥ (A *ᵥ φ) = φ := by
      rw [mulVec_mulVec, nonsing_inv_mul A hdet, one_mulVec]
    exact (congrFun this x).symm
  have e : (fun φ => φ x * F φ * gaussWeight A φ) =
      fun φ => ∑ y, A⁻¹ x y * ((A *ᵥ φ) y * F φ * gaussWeight A φ) := by
    funext φ
    rw [hφ φ, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e, integral_finsetSum _ (fun y _ =>
    (integrable_ibp_left hA hFd.continuous C a hF y).const_mul _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_const_mul, gauss_ibp hA hFd C a y hF (hF' y)]

/-- Bounded special case: `F` and `∂_x F` bounded by `C`. -/
theorem gauss_ibp_bounded {A : Matrix ι ι ℝ} (hA : A.PosDef) {F : (ι → ℝ) → ℝ}
    (hFd : Differentiable ℝ F) (C : ℝ) (x : ι)
    (hF : ∀ φ, |F φ| ≤ C) (hF' : ∀ φ, |fderiv ℝ F φ (Pi.single x 1)| ≤ C) :
    ∫ φ, (A *ᵥ φ) x * F φ * gaussWeight A φ =
      ∫ φ, fderiv ℝ F φ (Pi.single x 1) * gaussWeight A φ :=
  gauss_ibp hA hFd C 0 x (fun φ => by simpa using hF φ) (fun φ => by simpa using hF' φ)

end PP2GaussIBP


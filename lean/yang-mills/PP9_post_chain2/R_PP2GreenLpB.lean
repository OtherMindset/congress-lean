import LongTable.R_PP2GreenLpA

/-!
Part B of PP2GreenLp (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2GreenLp.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `glp_heatK_diag_le`: ε⁻² p_t(x,x) ≤ e^{−t m₀²} π/(4t) (t > 0); `glp_heatK_abs_le`:
  |p_t(x,y)| ≤ (p_t(x,x) + p_t(y,y))/2; `glp_heatK_sup_le`, `glp_heatK_L2_le`, `glp_heatK_Lp_le`.
* `glp_dirGreen_Lp_le` (**goal 2**): m₀ ≠ 0, p ∈ ℕ, p ≥ 2 →
  ε² Σ_y (ε⁻² dirGreen x y)^p ≤ (π/4)^{p−1}/2 · Γ(1/p)^p / m₀².
  `glp_dirGreen_L2_le`: p = 2, bound π²/(8 m₀²); `glp_dirGreen_L4_le`: p = 4, bound
  (π/4)³ Γ(1/4)⁴/(2 m₀²) ≈ 41.9/m₀².
* `glp_roughCov_Lp_le` (**goal 3**): any m₀, T ≥ 0, p ∈ ℕ, p ≥ 2 →
  ε² Σ_y |C_r(T)(x,y)|^p ≤ (π/4)^{p−1}/2 · p^p · T (exponent a = 1).
* `glp_roughCov_spectral`: C_r(T)(x,y) = ε⁻² Σ_K e_K(x) e_K(y) (1 − e^{−T λ_K})/λ_K (the plan's form).

NOT formalized here: the region (physBall) versions of all of the above; positivity p_t(x,y) ≥ 0
off the diagonal (not needed: absolute values are used for C_r); the smooth part C − C_r and its
pointwise bounds; a numerical bound on Γ(1/p).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset MeasureTheory Set

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-- Sup bound: ε⁻² |p_t(x, y)| ≤ e^{−t m₀²} π/(4t). -/
theorem glp_heatK_sup_le (m₀ : ℝ) {t : ℝ} (ht : 0 < t) (x y : DSite n k) :
    |(spacing n ^ 2)⁻¹ * heatK n k m₀ t x y| ≤ exp (-(t * m₀ ^ 2)) * (π / (4 * t)) := by
  have hε : 0 < (spacing n ^ 2)⁻¹ := by have := spacing_pos n; positivity
  rw [abs_mul, abs_of_pos hε]
  have h := glp_heatK_abs_le m₀ t x y
  have dx := glp_heatK_diag_le m₀ ht x
  have dy := glp_heatK_diag_le m₀ ht y
  calc (spacing n ^ 2)⁻¹ * |heatK n k m₀ t x y|
      ≤ (spacing n ^ 2)⁻¹ * ((heatK n k m₀ t x x + heatK n k m₀ t y y) / 2) :=
        mul_le_mul_of_nonneg_left h hε.le
    _ = ((spacing n ^ 2)⁻¹ * heatK n k m₀ t x x + (spacing n ^ 2)⁻¹ * heatK n k m₀ t y y) / 2 := by
        ring
    _ ≤ _ := by linarith

/-- L² bound: ε² Σ_y (ε⁻² p_t(x, y))² = ε⁻² p_{2t}(x, x) ≤ e^{−2t m₀²} π/(8t). -/
theorem glp_heatK_L2_le (m₀ : ℝ) {t : ℝ} (ht : 0 < t) (x : DSite n k) :
    spacing n ^ 2 * ∑ y, ((spacing n ^ 2)⁻¹ * heatK n k m₀ t x y) ^ 2 ≤
      exp (-(t * m₀ ^ 2)) ^ 2 * (π / (8 * t)) := by
  have hε : spacing n ^ 2 ≠ 0 := by have := spacing_pos n; positivity
  have e : spacing n ^ 2 * ∑ y, ((spacing n ^ 2)⁻¹ * heatK n k m₀ t x y) ^ 2 =
      (spacing n ^ 2)⁻¹ * heatK n k m₀ (2 * t) x x := by
    rw [← heatK_sq_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    field_simp
  rw [e]
  have h := glp_heatK_diag_le m₀ (by linarith : 0 < 2 * t) x
  calc _ ≤ _ := h
    _ = exp (-(t * m₀ ^ 2)) ^ 2 * (π / (8 * t)) := by
        rw [show exp (-(t * m₀ ^ 2)) ^ 2 = exp (-(2 * t * m₀ ^ 2)) by
          rw [sq, ← exp_add]; ring_nf]
        field_simp; ring

/-- Lᵖ bound for the heat kernel, p ≥ 2:
ε² Σ_y |ε⁻² p_t(x, y)|^p ≤ (π/4)^{p−1}/2 · (t / t^p) · e^{−p t m₀²}. -/
theorem glp_heatK_Lp_le (m₀ : ℝ) {t : ℝ} (ht : 0 < t) (p : ℕ) (hp : 2 ≤ p) (x : DSite n k) :
    spacing n ^ 2 * ∑ y, |(spacing n ^ 2)⁻¹ * heatK n k m₀ t x y| ^ p ≤
      (π / 4) ^ (p - 1) / 2 * (t / t ^ p) * exp (-(t * m₀ ^ 2)) ^ p := by
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  set a := exp (-(t * m₀ ^ 2)) * (π / (4 * t)) with ha
  have ha0 : 0 ≤ a := by positivity
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 2 := ⟨p - 2, by omega⟩
  have hpt : ∀ y, |(spacing n ^ 2)⁻¹ * heatK n k m₀ t x y| ^ (j + 2) ≤
      a ^ j * ((spacing n ^ 2)⁻¹ * heatK n k m₀ t x y) ^ 2 := by
    intro y
    rw [pow_add, ← sq_abs ((spacing n ^ 2)⁻¹ * heatK n k m₀ t x y)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (glp_heatK_sup_le m₀ ht x y) j) (sq_nonneg _)
  calc spacing n ^ 2 * ∑ y, |(spacing n ^ 2)⁻¹ * heatK n k m₀ t x y| ^ (j + 2)
      ≤ spacing n ^ 2 * ∑ y, a ^ j * ((spacing n ^ 2)⁻¹ * heatK n k m₀ t x y) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hpt y) hε
    _ = a ^ j * (spacing n ^ 2 * ∑ y, ((spacing n ^ 2)⁻¹ * heatK n k m₀ t x y) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ a ^ j * (exp (-(t * m₀ ^ 2)) ^ 2 * (π / (8 * t))) :=
        mul_le_mul_of_nonneg_left (glp_heatK_L2_le m₀ ht x) (pow_nonneg ha0 _)
    _ = _ := by
        rw [ha, show j + 2 - 1 = j + 1 by omega]
        simp only [mul_pow, div_pow]
        field_simp
        ring

theorem glp_heatK_integrableOn (m₀ : ℝ) (x y : DSite n k) :
    IntegrableOn (fun t => heatK n k m₀ t x y) (Ioi 0) := by
  unfold heatK
  exact integrable_finsetSum _ fun K _ => (integrableOn_exp_neg_mul_Ioi (dirEig_pos m₀ K)).const_mul _

/-- φ(t)^p for the Minkowski majorant: (E^{1/p} t^{1/p−1} e)^p = E (t / t^p) e^p (t > 0). -/
theorem glp_majorant_pow {E t e : ℝ} (hE : 0 ≤ E) (ht : 0 < t) (p : ℕ) (hp : p ≠ 0) :
    (E ^ ((p : ℝ)⁻¹) * (t ^ ((p : ℝ)⁻¹ - 1) * e)) ^ p = E * (t / t ^ p) * e ^ p := by
  rw [rpow_sub_one ht.ne', mul_pow, mul_pow, div_pow, rpow_inv_natCast_pow hE hp,
    rpow_inv_natCast_pow ht.le hp]
  ring

/-- **Lᵖ bound for the box covariance (goal 2):** for m₀ ≠ 0 and every natural p ≥ 2,
uniformly in n, k, x,
ε² Σ_y (ε⁻² dirGreen x y)^p ≤ (π/4)^{p−1}/2 · Γ(1/p)^p / m₀². -/
theorem glp_dirGreen_Lp_le {m₀ : ℝ} (hm : m₀ ≠ 0) (p : ℕ) (hp : 2 ≤ p) (x : DSite n k) :
    spacing n ^ 2 * ∑ y, ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ p ≤
      (π / 4) ^ (p - 1) / 2 * Gamma ((p : ℝ)⁻¹) ^ p / m₀ ^ 2 := by
  have hpn : p ≠ 0 := by omega
  set P : ℝ := (p : ℝ) with hP
  have hPpos : (0 : ℝ) < P := by rw [hP]; exact_mod_cast (by omega : 0 < p)
  have hP0 : 0 < P⁻¹ := inv_pos.mpr hPpos
  set E : ℝ := (π / 4) ^ (p - 1) / 2 with hEdef
  have hE : 0 ≤ E := by positivity
  have hm2 : 0 < m₀ ^ 2 := by positivity
  set φ : ℝ → ℝ := fun t => E ^ P⁻¹ * (t ^ (P⁻¹ - 1) * exp (-(m₀ ^ 2 * t))) with hφdef
  have hg_int : ∫ t in Ioi (0 : ℝ), t ^ (P⁻¹ - 1) * exp (-(m₀ ^ 2 * t)) =
      (1 / m₀ ^ 2) ^ P⁻¹ * Gamma P⁻¹ := integral_rpow_mul_exp_neg_mul_Ioi hP0 hm2
  have hgI : IntegrableOn (fun t : ℝ => t ^ (P⁻¹ - 1) * exp (-(m₀ ^ 2 * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by
      rw [hg_int]; exact (mul_pos (rpow_pos_of_pos (by positivity) _) (Gamma_pos_of_pos hP0)).ne')
  have key := glp_minkowski measurableSet_Ioi
    (fun t y => (spacing n ^ 2)⁻¹ * heatK n k m₀ t x y) φ (c := spacing n ^ 2) (by positivity) p hp
    (fun y => (glp_heatK_integrableOn m₀ x y).const_mul _) (hgI.const_mul _)
    (fun t ht => mul_nonneg (rpow_nonneg hE _)
      (mul_nonneg (rpow_nonneg (le_of_lt ht) _) (exp_pos _).le))
    (fun t ht => by
      have ht' : 0 < t := ht
      refine (glp_heatK_Lp_le m₀ ht' p hp x).trans (le_of_eq ?_)
      rw [hφdef]; simp only
      rw [glp_majorant_pow hE ht' p hpn, mul_comm (m₀ ^ 2) t])
  simp only [integral_const_mul, integral_heatK, hφdef, hg_int] at key
  have habs : ∀ y, |(spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y| ^ p =
      ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ p := fun y => by
    rw [abs_of_nonneg (mul_nonneg (by positivity) (dirGreen_nonneg hm x y))]
  simp_rw [habs] at key
  refine key.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, rpow_inv_natCast_pow hE hpn, rpow_inv_natCast_pow (by positivity) hpn]
  field_simp

/-- p = 2: ε² Σ_y (ε⁻² dirGreen x y)² ≤ π² / (8 m₀²). -/
theorem glp_dirGreen_L2_le {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) :
    spacing n ^ 2 * ∑ y, ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ 2 ≤ π ^ 2 / (8 * m₀ ^ 2) := by
  refine (glp_dirGreen_Lp_le hm 2 le_rfl x).trans (le_of_eq ?_)
  rw [show ((2 : ℕ) : ℝ)⁻¹ = 1 / 2 by norm_num, Gamma_one_half_eq, sq_sqrt pi_pos.le]
  field_simp
  ring

/-- p = 4: ε² Σ_y (ε⁻² dirGreen x y)⁴ ≤ (π/4)³ Γ(1/4)⁴ / (2 m₀²) (≈ 41.9 / m₀²). -/
theorem glp_dirGreen_L4_le {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) :
    spacing n ^ 2 * ∑ y, ((spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y) ^ 4 ≤
      (π / 4) ^ 3 * Gamma (1 / 4) ^ 4 / (2 * m₀ ^ 2) := by
  refine (glp_dirGreen_Lp_le hm 4 (by norm_num) x).trans (le_of_eq ?_)
  rw [show ((4 : ℕ) : ℝ)⁻¹ = 1 / 4 by norm_num]
  norm_num
  field_simp

/-! ## The rough part C_r(T) = ε⁻² ∫₀^T p_t dt -/

/-- The rough (short-time) part of the box covariance, C_r(T)(x, y) = ε⁻² ∫_{(0,T]} p_t(x, y) dt. -/
def glp_roughCov (n k : ℕ) (m₀ T : ℝ) (x y : DSite n k) : ℝ :=
  (spacing n ^ 2)⁻¹ * ∫ t in Ioc 0 T, heatK n k m₀ t x y

/-- **Lᵖ bound for the rough part (goal 3):** for every m₀, T ≥ 0, natural p ≥ 2,
uniformly in n, k, x: ε² Σ_y |C_r(T)(x, y)|^p ≤ (π/4)^{p−1}/2 · p^p · T. -/
theorem glp_roughCov_Lp_le (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (p : ℕ) (hp : 2 ≤ p) (x : DSite n k) :
    spacing n ^ 2 * ∑ y, |glp_roughCov n k m₀ T x y| ^ p ≤
      (π / 4) ^ (p - 1) / 2 * (p : ℝ) ^ p * T := by
  have hpn : p ≠ 0 := by omega
  set P : ℝ := (p : ℝ) with hP
  have hPpos : (0 : ℝ) < P := by rw [hP]; exact_mod_cast (by omega : 0 < p)
  have hP0 : 0 < P⁻¹ := inv_pos.mpr hPpos
  set E : ℝ := (π / 4) ^ (p - 1) / 2 with hEdef
  have hE : 0 ≤ E := by positivity
  set φ : ℝ → ℝ := fun t => E ^ P⁻¹ * (t ^ (P⁻¹ - 1) * 1) with hφdef
  have hr : -1 < P⁻¹ - 1 := by linarith
  have hg_int : ∫ t in Ioc 0 T, t ^ (P⁻¹ - 1) * 1 = T ^ P⁻¹ / P⁻¹ := by
    simp only [mul_one]
    rw [← intervalIntegral.integral_of_le hT, integral_rpow (Or.inl hr), sub_add_cancel,
      zero_rpow hP0.ne', sub_zero]
  have hgI : IntegrableOn (fun t : ℝ => t ^ (P⁻¹ - 1) * 1) (Ioc 0 T) := by
    simp only [mul_one]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  have key := glp_minkowski measurableSet_Ioc
    (fun t y => (spacing n ^ 2)⁻¹ * heatK n k m₀ t x y) φ (c := spacing n ^ 2) (by positivity) p hp
    (fun y => ((glp_heatK_integrableOn m₀ x y).mono_set Ioc_subset_Ioi_self).const_mul _)
    (hgI.const_mul _)
    (fun t ht => mul_nonneg (rpow_nonneg hE _) (by
      rw [mul_one]; exact rpow_nonneg (le_of_lt ht.1) _))
    (fun t ht => by
      have ht' : 0 < t := ht.1
      refine (glp_heatK_Lp_le m₀ ht' p hp x).trans ?_
      rw [hφdef]; simp only
      rw [glp_majorant_pow hE ht' p hpn, one_pow]
      have h1 : exp (-(t * m₀ ^ 2)) ^ p ≤ 1 :=
        pow_le_one₀ (exp_pos _).le
          (exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht'.le (sq_nonneg _))))
      have h2 : 0 ≤ E * (t / t ^ p) := mul_nonneg hE (div_nonneg ht'.le (pow_nonneg ht'.le _))
      rw [← hEdef]
      exact mul_le_mul_of_nonneg_left h1 h2)
  simp only [integral_const_mul, hφdef, hg_int] at key
  refine key.trans (le_of_eq ?_)
  rw [mul_pow, div_pow, rpow_inv_natCast_pow hE hpn, rpow_inv_natCast_pow hT hpn, inv_pow]
  field_simp

theorem glp_integral_exp_Ioc {l : ℝ} (hl : 0 < l) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Ioc 0 T, exp (-(t * l)) = (1 - exp (-(T * l))) / l := by
  rw [← intervalIntegral.integral_of_le hT]
  have hd : ∀ t ∈ uIcc 0 T, HasDerivAt (fun t => (-1 / l) * exp (-(t * l))) (exp (-(t * l))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t * (-l)) (-l) t := hasDerivAt_mul_const (-l)
    have h := h1.exp.const_mul (-1 / l)
    have e : (fun t : ℝ => (-1 / l) * exp (-(t * l))) = fun t => (-1 / l) * exp (t * (-l)) := by
      funext t; ring_nf
    rw [e]
    convert h using 1
    rw [show t * (-l) = -(t * l) by ring]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by exact (continuous_exp.comp ((continuous_id.mul continuous_const).neg)).intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, exp_zero]
  field_simp
  ring

/-- Spectral form of the rough part (the plan's definition):
C_r(T)(x, y) = ε⁻² Σ_K e_K(x) e_K(y) (1 − e^{−T λ_K}) / λ_K. -/
theorem glp_roughCov_spectral (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (x y : DSite n k) :
    glp_roughCov n k m₀ T x y = (spacing n ^ 2)⁻¹ *
      ∑ K : DSite n k, sineVec2 K x * sineVec2 K y * (1 - exp (-(T * dirEig n k m₀ K))) /
        dirEig n k m₀ K := by
  unfold glp_roughCov heatK
  congr 1
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun K _ => ?_
    rw [integral_const_mul, glp_integral_exp_Ioc (dirEig_pos m₀ K) hT, mul_div_assoc]
  · intro K _
    exact ((integrableOn_exp_neg_mul_Ioi (dirEig_pos m₀ K)).mono_set Ioc_subset_Ioi_self).const_mul _

end PP2Target

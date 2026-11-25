import LongTable.P_mww0oo05_8eieqb

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Session 3.
Node N3, one step: the Wick constant of `PP2Target` (#mwvi84dh-hnd872) is a positive real number,
the ratio of two convergent, strictly positive Gaussian integrals.

FORMALIZED (every level n, m₀ ≠ 0):
* `integrable_freeWeight`: exp(−½·freeAction) is integrable on ℝ^(sites).
* `integrable_sq_freeWeight`: φ(0)²·exp(−½·freeAction) is integrable.
* `integral_freeWeight_pos`, `integral_sq_freeWeight_pos`: both integrals are strictly positive.
* `wickConst_pos`: 0 < wickConst n m₀.

NOT formalized: that wickConst equals the (0,0) entry of the inverse of the lattice operator,
or its asymptotics ≈ (2π)⁻¹ log(1/ε); any bound on wickConst uniform in n (only positivity
and finiteness are proved).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory

noncomputable section

namespace PP2Target

theorem freeWeight_le_gauss (n : ℕ) (m₀ : ℝ) (φ : Field n) : freeWeight n m₀ φ ≤ gauss n m₀ φ := by
  rw [gauss_eq, freeWeight]
  apply Real.exp_le_exp.mpr
  have := freeAction_ge n m₀ φ
  linarith

theorem continuous_freeWeight (n : ℕ) (m₀ : ℝ) : Continuous (freeWeight n m₀) := by
  unfold freeWeight freeAction
  fun_prop

theorem freeWeight_pos (n : ℕ) (m₀ : ℝ) (φ : Field n) : 0 < freeWeight n m₀ φ := Real.exp_pos _

theorem integrable_freeWeight (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) : Integrable (freeWeight n m₀) := by
  refine Integrable.mono' (integrable_gauss n hm) (continuous_freeWeight n m₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (freeWeight_pos _ _ _)]
  exact freeWeight_le_gauss n m₀ φ

/-- φ(0)² times the Gaussian majorant is integrable. -/
theorem integrable_sq_gauss (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) :
    Integrable (fun φ : Field n => φ 0 ^ 2 * gauss n m₀ φ) := by
  have hb : 0 < m₀ ^ 2 * spacing n ^ 2 / 2 := by
    have := spacing_pos n
    positivity
  set b := m₀ ^ 2 * spacing n ^ 2 / 2
  have h2 : Integrable (fun y : ℝ => y ^ 2 * Real.exp (-b * y ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
    simpa [Real.rpow_two] using this
  have := Integrable.fintype_prod (ι := Site n) (E := ℝ) (𝕜 := ℝ)
    (μ := fun _ => (volume : Measure ℝ))
    (f := fun i y => if i = 0 then y ^ 2 * Real.exp (-b * y ^ 2) else Real.exp (-b * y ^ 2))
    (fun i => by split_ifs; exacts [h2, integrable_exp_neg_mul_sq hb])
  convert this using 2 with φ
  rw [gauss, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Site n)),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Site n))]
  rw [if_pos rfl, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [if_neg (Finset.ne_of_mem_erase hi)]

theorem integrable_sq_freeWeight (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) :
    Integrable (fun φ : Field n => φ 0 ^ 2 * freeWeight n m₀ φ) := by
  refine Integrable.mono' (integrable_sq_gauss n hm)
    ((continuous_apply 0).pow 2 |>.mul (continuous_freeWeight n m₀)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (freeWeight_pos _ _ _).le)]
  exact mul_le_mul_of_nonneg_left (freeWeight_le_gauss n m₀ φ) (sq_nonneg _)

theorem integral_freeWeight_pos (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) :
    0 < ∫ φ : Field n, freeWeight n m₀ φ := by
  rw [integral_pos_iff_support_of_nonneg (fun φ => (freeWeight_pos _ _ φ).le)
    (integrable_freeWeight n hm)]
  have : Function.support (freeWeight n m₀) = Set.univ := by
    ext φ; simp [(freeWeight_pos n m₀ φ).ne']
  rw [this]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

theorem integral_sq_freeWeight_pos (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) :
    0 < ∫ φ : Field n, φ 0 ^ 2 * freeWeight n m₀ φ := by
  rw [integral_pos_iff_support_of_nonneg
    (fun φ => mul_nonneg (sq_nonneg _) (freeWeight_pos _ _ φ).le) (integrable_sq_freeWeight n hm)]
  have hsub : {φ : Field n | φ 0 ≠ 0} ⊆
      Function.support (fun φ : Field n => φ 0 ^ 2 * freeWeight n m₀ φ) := by
    intro φ hφ
    simp only [Function.mem_support]
    exact mul_ne_zero (pow_ne_zero 2 hφ) (freeWeight_pos n m₀ φ).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have hopen : IsOpen {φ : Field n | φ 0 ≠ 0} :=
    isOpen_ne_fun (continuous_apply 0) continuous_const
  exact hopen.measure_pos volume ⟨fun _ => 1, by simp⟩

theorem wickConst_pos (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) : 0 < wickConst n m₀ :=
  div_pos (integral_sq_freeWeight_pos n hm) (integral_freeWeight_pos n hm)

end PP2Target

import Mathlib

/-!
# Elementary steps for the height-1 slab (draft)

Arithmetic and two small lemmas used in `NOTES.md` of this folder (the single-site total-variation
Dobrushin condition for the SU(2) sigma-model on a height-1 slab). Everything here is elementary:
no statement about lattice gauge theory, about von Mises–Fisher laws or about the constant
4/(3π) itself is proved in this file. The notes say which steps are proved where.
-/

open Real

namespace YMSlab

/-- With `2(d-1)` neighbours and the single-site bound `C ≤ β · 4/(3π)`, the row sum
`2(d-1) · β · 4/(3π)` is below 1 exactly when `β < 3π/(8(d-1))`. -/
theorem row_sum_lt_one_iff (d : ℕ) (hd : 2 ≤ d) (β : ℝ) :
    2 * ((d : ℝ) - 1) * β * (4 / (3 * π)) < 1 ↔ β < 3 * π / (8 * ((d : ℝ) - 1)) := by
  have hd' : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hπ : (0 : ℝ) < π := pi_pos
  rw [lt_div_iff₀ (by positivity)]
  have h : 2 * ((d : ℝ) - 1) * β * (4 / (3 * π)) = β * (8 * ((d : ℝ) - 1)) / (3 * π) := by
    field_simp
    ring
  rw [h, div_lt_one (by positivity)]

/-- Below that threshold the field strength `κ ≤ 2(d-1)β` stays below `3π/4`, in every dimension. -/
theorem kappa_lt (d : ℕ) (hd : 2 ≤ d) (β : ℝ) (h : β < 3 * π / (8 * ((d : ℝ) - 1))) :
    2 * ((d : ℝ) - 1) * β < 3 * π / 4 := by
  have hd' : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [lt_div_iff₀ (by positivity)] at h
  linarith

/-- `3π/4 < 19/8`: a certificate of the constant on `κ ≤ 19/8` covers the range of `kappa_lt`. -/
theorem three_pi_div_four_lt : 3 * π / 4 < 19 / 8 := by
  have := pi_lt_d2
  linarith

/-- The threshold `3π/(8(d-1))` is `3π/4` times `1/(2(d-1))`, and `3π/4 > 2.35`. -/
theorem threshold_ratio (d : ℕ) (hd : 2 ≤ d) :
    3 * π / (8 * ((d : ℝ) - 1)) = (3 * π / 4) * (1 / (2 * ((d : ℝ) - 1))) ∧ 47 / 20 < 3 * π / 4 := by
  have hd' : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  refine ⟨by field_simp; ring, ?_⟩
  have := pi_gt_d2
  linarith

/-- Geometric tail: for `0 ≤ α < 1`, `∑_{n ≥ k} α^n = α^k/(1-α)`. -/
theorem geom_tail (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (k : ℕ) :
    ∑' n : ℕ, α ^ (n + k) = α ^ k / (1 - α) := by
  have h : ∀ n : ℕ, α ^ (n + k) = α ^ k * α ^ n := fun n => by rw [pow_add, mul_comm]
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- Reflection in the hyperplane orthogonal to a unit vector `n` moves `u` by `2|⟪n, u⟫|`. -/
theorem dist_reflection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n u : E) (hn : ‖n‖ = 1) :
    dist u (u - (2 * inner ℝ n u) • n) = 2 * |inner ℝ n u| := by
  rw [dist_eq_norm]
  have : u - (u - (2 * inner ℝ n u) • n) = (2 * inner ℝ n u) • n := by abel
  rw [this, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_mul, abs_two]

/-- The odd part of a 1-Lipschitz function under that reflection is at most `|⟪n, u⟫|`:
`|f u - f (R u)| / 2 ≤ |⟪n, u⟫|`. -/
theorem odd_part_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (hf : LipschitzWith 1 f) (n u : E) (hn : ‖n‖ = 1) :
    |f u - f (u - (2 * inner ℝ n u) • n)| / 2 ≤ |inner ℝ n u| := by
  have h := hf.dist_le_mul u (u - (2 * inner ℝ n u) • n)
  rw [dist_reflection n u hn, Real.dist_eq] at h
  simp only [NNReal.coe_one, one_mul] at h
  linarith

end YMSlab

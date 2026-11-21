import Mathlib

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, Session 4, 21 Nov 2026 (route lead B).
The Bessel-series inequality of the companion foundation posts (single-link reduction, step 6; vMF moment
bounds, step 6), lattice only.

FORMALIZED. I1 and I2 are DEFINED in this file by their power series (no Mathlib Bessel function is used):
  I1 κ := ∑' k, (κ/2)^(2k+1) / (k!·(k+1)!),   I2 κ := ∑' k, (κ/2)^(2k+2) / (k!·(k+2)!).
* `YMBessel.summable_I1`, `YMBessel.summable_I2`: both series are summable for every real κ (so the
  `tsum` in the definitions is the actual sum, not Lean's default value 0 for divergent series).
* `YMBessel.four_I2_le`: 4·I2 κ ≤ κ·I1 κ for κ ≥ 0.
* `YMBessel.four_I2_lt`: 4·I2 κ < κ·I1 κ for κ > 0.
Proof as in the paper: termwise, (k+2)·4·t₂(k) = 2·κ·t₁(k) and all terms are ≥ 0, so 4·t₂(k) ≤ κ·t₁(k),
strictly at k = 1 when κ > 0; then sum.

NOT formalized: that these series are the modified Bessel functions I₁, I₂ (so A(κ) = I₂/I₁ in the
paper's notation), and every use of the inequality (A(κ) ≤ κ/4, the variance bounds, the vMF reduction).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Nat

namespace YMBessel

/-- The k-th term of I₁: (κ/2)^(2k+1) / (k! (k+1)!). -/
noncomputable def t1 (κ : ℝ) (k : ℕ) : ℝ :=
  (κ / 2) ^ (2 * k + 1) / ((k ! : ℝ) * ((k + 1) ! : ℝ))

/-- The k-th term of I₂: (κ/2)^(2k+2) / (k! (k+2)!). -/
noncomputable def t2 (κ : ℝ) (k : ℕ) : ℝ :=
  (κ / 2) ^ (2 * k + 2) / ((k ! : ℝ) * ((k + 2) ! : ℝ))

/-- I₁(κ) := ∑_{k ≥ 0} (κ/2)^(2k+1) / (k! (k+1)!), defined by its series. -/
noncomputable def I1 (κ : ℝ) : ℝ := ∑' k : ℕ, (κ / 2) ^ (2 * k + 1) / ((k ! : ℝ) * ((k + 1) ! : ℝ))

/-- I₂(κ) := ∑_{k ≥ 0} (κ/2)^(2k+2) / (k! (k+2)!), defined by its series. -/
noncomputable def I2 (κ : ℝ) : ℝ := ∑' k : ℕ, (κ / 2) ^ (2 * k + 2) / ((k ! : ℝ) * ((k + 2) ! : ℝ))

theorem fact_pos (k : ℕ) : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k

theorem fact_ge_one (k : ℕ) : (1 : ℝ) ≤ (k ! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)

/-- A common domination: |x^(2k+j)| / (k! m!) ≤ |x|^j · (x^2)^k / k! when m! ≥ 1. -/
theorem term_bound (x : ℝ) (j k m : ℕ) :
    ‖x ^ (2 * k + j) / ((k ! : ℝ) * (m ! : ℝ))‖ ≤ |x| ^ j * ((x ^ 2) ^ k / (k ! : ℝ)) := by
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, abs_of_pos (fact_pos k), abs_of_pos (fact_pos m)]
  have hk := fact_pos k
  have hm := fact_ge_one m
  have e : |x| ^ (2 * k + j) = |x| ^ j * (x ^ 2) ^ k := by
    rw [pow_add, pow_mul, sq_abs]; ring
  rw [e, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg x) j)
  apply div_le_div_of_nonneg_left (pow_nonneg (sq_nonneg x) k) hk
  nlinarith

/-- The series defining I₁(κ) converges (absolutely) for every real κ. -/
theorem summable_I1 (κ : ℝ) :
    Summable (fun k : ℕ => (κ / 2) ^ (2 * k + 1) / ((k ! : ℝ) * ((k + 1) ! : ℝ))) :=
  Summable.of_norm_bounded ((Real.summable_pow_div_factorial ((κ / 2) ^ 2)).mul_left (|κ / 2| ^ 1))
    (fun k => term_bound (κ / 2) 1 k (k + 1))

/-- The series defining I₂(κ) converges (absolutely) for every real κ. -/
theorem summable_I2 (κ : ℝ) :
    Summable (fun k : ℕ => (κ / 2) ^ (2 * k + 2) / ((k ! : ℝ) * ((k + 2) ! : ℝ))) :=
  Summable.of_norm_bounded ((Real.summable_pow_div_factorial ((κ / 2) ^ 2)).mul_left (|κ / 2| ^ 2))
    (fun k => term_bound (κ / 2) 2 k (k + 2))

/-- Termwise: 4·t₂(κ,k) = (2/(k+2)) · κ·t₁(κ,k), written as a product identity. -/
theorem term_identity (κ : ℝ) (k : ℕ) :
    ((k : ℝ) + 2) * (4 * t2 κ k) = 2 * (κ * t1 κ k) := by
  unfold t1 t2
  have h2 : ((k + 2) ! : ℝ) = ((k : ℝ) + 2) * ((k + 1) ! : ℝ) := by
    rw [show k + 2 = (k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  rw [h2]
  have hk := fact_pos k
  have hk1 := fact_pos (k + 1)
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  field_simp
  ring

theorem t1_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (k : ℕ) : 0 ≤ t1 κ k := by
  unfold t1; have := fact_pos k; have := fact_pos (k + 1); positivity

theorem term_le {κ : ℝ} (hκ : 0 ≤ κ) (k : ℕ) : 4 * t2 κ k ≤ κ * t1 κ k := by
  have e := term_identity κ k
  have h1 : 0 ≤ κ * t1 κ k := mul_nonneg hκ (t1_nonneg hκ k)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg hk h1]

theorem term_lt {κ : ℝ} (hκ : 0 < κ) : 4 * t2 κ 1 < κ * t1 κ 1 := by
  have e := term_identity κ 1
  have h1 : 0 < κ * t1 κ 1 := by
    unfold t1; have := fact_pos 1; have := fact_pos 2; positivity
  push_cast at e
  linarith

/-- **Bessel-series inequality**: for κ ≥ 0, 4·I₂(κ) ≤ κ·I₁(κ). -/
theorem four_I2_le (κ : ℝ) (hκ : 0 ≤ κ) : 4 * I2 κ ≤ κ * I1 κ := by
  unfold I1 I2
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun k => term_le hκ k) ((summable_I2 κ).mul_left 4)
    ((summable_I1 κ).mul_left κ)

/-- Strict form: for κ > 0, 4·I₂(κ) < κ·I₁(κ). -/
theorem four_I2_lt (κ : ℝ) (hκ : 0 < κ) : 4 * I2 κ < κ * I1 κ := by
  unfold I1 I2
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact Summable.tsum_lt_tsum (i := 1) (fun k => term_le hκ.le k) (term_lt hκ)
    ((summable_I2 κ).mul_left 4) ((summable_I1 κ).mul_left κ)

end YMBessel

import LongTable.R_PP2DoubleIBPC

/-!
Part D of PP2DoubleIBP (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2DoubleIBP.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* G3 (free measure ⟨·⟩₀ = `dib_ex0 A`, `dib_WW A c y y' j k` = ⟨:φ_y^j:_c :φ_{y'}^k:_c⟩₀):
  `dib_g3_step` (j ≤ 2, k ≤ 4): W(j+2,k) = −(j+1) δ_y W(j,k) + k C(y,y') W(j+1,k−1),
  δ_y = c − C(y,y), C = A⁻¹; `dib_g3_step'` (second slot); `dib_WW_0_0`, `dib_WW_1_0`, `dib_WW_0_1`,
  `dib_WW_1_1` (= C(y,y')); the full table `dib_WW_j_k`, j, k ≤ 4, as explicit polynomials in
  r = C(y,y'), δ_y, δ_{y'} (odd total degree: 0; e.g. (2,2): δδ' + 2r²;
  (4,4): 9δ²δ'² + 72r²δδ' + 24r⁴).
  Box: `dib_WW_box` (dexpect at λ = 0 is `dib_WW (scaledOp …)`), `dib_wick22_box`, `dib_wick44_box`
  with C = ε⁻² dirGreen and c = freeVar. Helpers: `dib_hasDerivAt_wick` ((wickPow c k)' =
  k wickPow c (k−1), k ≤ 4), `dib_wick_herm` (Hermite recursion, degree ≤ 4).

NOT formalized here: I2 (bounds on the two correction terms); the region table for G3 (it is the
generic table with A = rg_scaledOp B, via `dib_rexpect_eq` at λ = 0); Wick derivative and Hermite
recursion in all degrees (only ≤ 4 is needed); δ_y ≥ 0 (F4).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Matrix Finset PP2Target

set_option maxHeartbeats 400000

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2DoubleIBP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section G3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **G3 recursion**: E₀[:φ_y^(j+2): :φ_{y'}^k:] = −(j+1) δ_y E₀[:φ_y^j: :φ_{y'}^k:]
+ k C(y,y') E₀[:φ_y^(j+1): :φ_{y'}^(k−1):], C = A⁻¹, δ_y = c − C(y,y), j ≤ 2, k ≤ 4. -/
theorem dib_g3_step {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) {j k : ℕ}
    (hj : j ≤ 2) (hk : k ≤ 4) :
    dib_WW A c y y' (j + 2) k =
      -(((j : ℝ) + 1) * (c - A⁻¹ y y)) * dib_WW A c y y' j k
        + (k : ℝ) * A⁻¹ y y' * dib_WW A c y y' (j + 1) (k - 1) := by
  simp only [dib_WW, dib_ex0]
  rw [dib_g3_step_unnorm hA c y y' hj hk, add_div, mul_div_assoc, mul_div_assoc]

theorem dib_WW_swap (A : Matrix ι ι ℝ) (c : ℝ) (y y' : ι) (j k : ℕ) :
    dib_WW A c y y' j k = dib_WW A c y' y k j := by
  simp only [dib_WW, dib_ex0]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun φ => by ring)

/-- The same recursion in the second slot. -/
theorem dib_g3_step' {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) {j k : ℕ}
    (hj : j ≤ 4) (hk : k ≤ 2) :
    dib_WW A c y y' j (k + 2) =
      -(((k : ℝ) + 1) * (c - A⁻¹ y' y')) * dib_WW A c y y' j k
        + (j : ℝ) * A⁻¹ y y' * dib_WW A c y y' (j - 1) (k + 1) := by
  rw [dib_WW_swap, dib_g3_step hA c y' y hk hj, dib_WW_swap A c y' y k j,
    dib_WW_swap A c y' y (k + 1) (j - 1), dib_inv_symm hA y' y]

theorem dib_lin_zero {A : Matrix ι ι ℝ} (hA : A.PosDef) (y : ι) :
    ∫ φ, φ y * PP2GaussIBP.gaussWeight A φ = 0 := by
  have key := PP2GaussIBP.gauss_ibp_cov hA (F := fun _ : ι → ℝ => (1 : ℝ))
    (differentiable_const 1) 1 0 y (fun φ => by simp) (fun z φ => by simp)
  simpa using key

theorem dib_quad {A : Matrix ι ι ℝ} (hA : A.PosDef) (y y' : ι) :
    ∫ φ, φ y * φ y' * PP2GaussIBP.gaussWeight A φ =
      A⁻¹ y y' * ∫ φ, PP2GaussIBP.gaussWeight A φ := by
  have hfd : ∀ φ : ι → ℝ, fderiv ℝ (fun ψ : ι → ℝ => ψ y') φ = ContinuousLinearMap.proj y' :=
    fun φ => (hasFDerivAt_apply y' φ).fderiv
  have hsum : ∀ φ : ι → ℝ, |φ y'| ≤ 1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro φ; rw [one_mul, one_mul]; exact dib_abs_le φ y'
  have hF' : ∀ (z : ι) (φ : ι → ℝ),
      |fderiv ℝ (fun ψ : ι → ℝ => ψ y') φ (Pi.single z 1)| ≤ 1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro z φ
    rw [hfd, ContinuousLinearMap.proj_apply, one_mul, one_mul]
    exact le_trans (dib_single_abs_le z y') (dib_one_le_exp φ)
  have key := PP2GaussIBP.gauss_ibp_cov hA (F := fun ψ : ι → ℝ => ψ y')
    (differentiable_apply y') 1 1 y hsum hF'
  simp only [hfd, ContinuousLinearMap.proj_apply] at key
  rw [key, Finset.sum_eq_single y']
  · simp
  · intro z _ hz
    simp [Pi.single_eq_of_ne (Ne.symm hz)]
  · simp

theorem dib_WW_0_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 0 = 1 := by
  simp only [dib_WW, dib_ex0, wickPow_zero', one_mul]
  exact div_self (dib_integral_gauss_pos hA).ne'

theorem dib_WW_1_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 0 = 0 := by
  simp only [dib_WW, dib_ex0, wickPow_one, wickPow_zero', mul_one]
  rw [dib_lin_zero hA y, zero_div]

theorem dib_WW_0_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 1 = 0 := by
  rw [dib_WW_swap]; exact dib_WW_1_0 hA c y' y

theorem dib_WW_1_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 1 = A⁻¹ y y' := by
  simp only [dib_WW, dib_ex0, wickPow_one]
  rw [dib_quad hA y y', mul_div_assoc, div_self (dib_integral_gauss_pos hA).ne', mul_one]

/-! ### The table E₀[:φ_y^j:_c :φ_{y'}^k:_c], j, k ≤ 4
(r = C(y,y'), d = δ_y = c − C(y,y), d' = δ_{y'} = c − C(y',y'), C = A⁻¹) -/

theorem dib_WW_0_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 2 = -(c - A⁻¹ y' y') := by
  have h := dib_g3_step' hA c y y' (j := 0) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_0 hA c y y']
  ring

theorem dib_WW_2_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 0 = -(c - A⁻¹ y y) := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_0 hA c y y']
  ring

theorem dib_WW_0_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 3 = 0 := by
  have h := dib_g3_step' hA c y y' (j := 0) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_1 hA c y y']
  ring

theorem dib_WW_1_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 2 = 0 := by
  have h := dib_g3_step' hA c y y' (j := 1) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_0 hA c y y', dib_WW_0_1 hA c y y']
  ring

theorem dib_WW_2_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 1 = 0 := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_1 hA c y y', dib_WW_1_0 hA c y y']
  ring

theorem dib_WW_3_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 0 = 0 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_0 hA c y y']
  ring

theorem dib_WW_0_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 4 = 3 * (c - A⁻¹ y' y') ^ 2 := by
  have h := dib_g3_step' hA c y y' (j := 0) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_2 hA c y y']
  ring

theorem dib_WW_1_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 3 = -3 * (A⁻¹ y y') * (c - A⁻¹ y' y') := by
  have h := dib_g3_step' hA c y y' (j := 1) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_1 hA c y y', dib_WW_0_2 hA c y y']
  ring

theorem dib_WW_2_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 2 = (c - A⁻¹ y y) * (c - A⁻¹ y' y') + 2 * (A⁻¹ y y') ^ 2 := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_2 hA c y y', dib_WW_1_1 hA c y y']
  ring

theorem dib_WW_3_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 1 = -3 * (A⁻¹ y y') * (c - A⁻¹ y y) := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_1 hA c y y', dib_WW_2_0 hA c y y']
  ring

theorem dib_WW_4_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 0 = 3 * (c - A⁻¹ y y) ^ 2 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_0 hA c y y']
  ring

theorem dib_WW_1_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 4 = 0 := by
  have h := dib_g3_step' hA c y y' (j := 1) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_2 hA c y y', dib_WW_0_3 hA c y y']
  ring

theorem dib_WW_2_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 3 = 0 := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_3 hA c y y', dib_WW_1_2 hA c y y']
  ring

theorem dib_WW_3_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 2 = 0 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_2 hA c y y', dib_WW_2_1 hA c y y']
  ring

theorem dib_WW_4_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 1 = 0 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_1 hA c y y', dib_WW_3_0 hA c y y']
  ring

theorem dib_WW_2_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 4 =
      -3 * (c - A⁻¹ y y) * (c - A⁻¹ y' y') ^ 2
        - 12 * (A⁻¹ y y') ^ 2 * (c - A⁻¹ y' y') := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 4) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_4 hA c y y', dib_WW_1_3 hA c y y']
  ring

theorem dib_WW_3_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 3 =
      9 * (A⁻¹ y y') * (c - A⁻¹ y y) * (c - A⁻¹ y' y')
        + 6 * (A⁻¹ y y') ^ 3 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_3 hA c y y', dib_WW_2_2 hA c y y']
  ring

theorem dib_WW_4_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 2 =
      -3 * (c - A⁻¹ y y) ^ 2 * (c - A⁻¹ y' y')
        - 12 * (A⁻¹ y y') ^ 2 * (c - A⁻¹ y y) := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_2 hA c y y', dib_WW_3_1 hA c y y']
  ring

theorem dib_WW_3_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 4 = 0 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 4) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_4 hA c y y', dib_WW_2_3 hA c y y']
  ring

theorem dib_WW_4_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 3 = 0 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_3 hA c y y', dib_WW_3_2 hA c y y']
  ring

theorem dib_WW_4_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 4 =
      9 * (c - A⁻¹ y y) ^ 2 * (c - A⁻¹ y' y') ^ 2
        + 72 * (A⁻¹ y y') ^ 2 * (c - A⁻¹ y y) * (c - A⁻¹ y' y')
        + 24 * (A⁻¹ y y') ^ 4 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 4) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_4 hA c y y', dib_WW_3_3 hA c y y']
  ring


theorem dib_ex_zero (A : Matrix ι ι ℝ) (e c : ℝ) (F : (ι → ℝ) → ℝ) :
    dib_ex A e c 0 F = dib_ex0 A F := by
  simp only [dib_ex, dib_ex0, dib_W_zero]

end G3

/-! ### G3 for the free box measure (λ = 0 in `dexpect`; C = ε⁻² dirGreen) -/

section G3Box

variable {n k : ℕ}

theorem dib_WW_box (m₀ c : ℝ) (y y' : DSite n k) (a b : ℕ) :
    PP2Griffiths.dexpect n k m₀ 0 (fun φ => wickPow c a (φ y) * wickPow c b (φ y')) =
      dib_WW (scaledOp n k m₀) c y y' a b := by
  rw [dib_dexpect_eq, dib_ex_zero]; rfl

/-- **G3, (2,2) entry, box:** E₀[:φ_y²:_c :φ_{y'}²:_c] = δ_y δ_{y'} + 2 C(y,y')², c = freeVar,
δ_y = c − C(y,y). -/
theorem dib_wick22_box {m₀ : ℝ} (hm : m₀ ≠ 0) (y y' : DSite n k) :
    PP2Griffiths.dexpect n k m₀ 0
        (fun φ => wickPow (freeVar n m₀) 2 (φ y) * wickPow (freeVar n m₀) 2 (φ y')) =
      (freeVar n m₀ - dib_G n k m₀ y y) * (freeVar n m₀ - dib_G n k m₀ y' y')
        + 2 * dib_G n k m₀ y y' ^ 2 := by
  rw [dib_WW_box, dib_WW_2_2 (scaledOp_posDef hm), ← dib_G_eq hm]

/-- **G3, (4,4) entry, box:** E₀[:φ_y⁴:_c :φ_{y'}⁴:_c] = 9 δ_y² δ_{y'}² + 72 C² δ_y δ_{y'} + 24 C⁴,
C = C(y,y'), c = freeVar, δ_y = c − C(y,y). -/
theorem dib_wick44_box {m₀ : ℝ} (hm : m₀ ≠ 0) (y y' : DSite n k) :
    PP2Griffiths.dexpect n k m₀ 0
        (fun φ => wickPow (freeVar n m₀) 4 (φ y) * wickPow (freeVar n m₀) 4 (φ y')) =
      9 * (freeVar n m₀ - dib_G n k m₀ y y) ^ 2 * (freeVar n m₀ - dib_G n k m₀ y' y') ^ 2
        + 72 * dib_G n k m₀ y y' ^ 2 * (freeVar n m₀ - dib_G n k m₀ y y) *
            (freeVar n m₀ - dib_G n k m₀ y' y')
        + 24 * dib_G n k m₀ y y' ^ 4 := by
  rw [dib_WW_box, dib_WW_4_4 (scaledOp_posDef hm), ← dib_G_eq hm]

end G3Box

end PP2DoubleIBP

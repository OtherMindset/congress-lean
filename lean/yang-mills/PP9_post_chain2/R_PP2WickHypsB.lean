import LongTable.R_PP2WickHypsA

/-!
Part B of PP2WickHyps (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2WickHyps.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* `wh_GB_apply`, `wh_GB_nonneg`, `wh_GB_symm`, `wh_GB_row` (ε²Σ_{z'}C_B(z,z') ≤ m₀⁻²),
  `wh_GB_Lp` (ε²Σ_{z'}C_B(z,z')^p ≤ K_p, from `mg_regionGreen_Lp_le`), `wh_defect_nonneg`,
  `wh_defect_le`, `wh_defect_sq_le` / `wh_defect_four_le` (δ², δ⁴ ≤ a + b r(y)^{−1/2}),
  `wh_sum_bound` (summation with `nr_card_le`, `nr_sum_f_M`), `wh_card_le`.
* **`wh_wickDefectHyp`**: m₀ ≠ 0 → 0 ≤ l → WickDefectHyp m₀ l
  (D = P(34 L² + 256 m' L^{3/2}), P = (π/4)², m' = |m₀|^{−1/2}, L = 2l + 1).
* `wh_defect4`: ∃ D₄ ≥ 0, ∀ n k x, ε²Σ_{z∈B} δ(z)⁴ ≤ D₄ (same route, δ⁴ ≤ P²(65544 + 65536 m' r^{−1/2})).
* **`wh_wickL2Hyp`**: m₀ ≠ 0 → 0 ≤ l → WickL2Hyp m₀ l. K = 1 + c_Y + c_F with
  c_Y = K₂D₂ + 2K₂², c_F = H²(c₁² + c₂²)/2, H = ρ₁⁻⁶, c₁ = 9S(K₄ + D₄)/2 + 6K₃K₂,
  c₂ = 9SD₂ + 6K₃L², S = m₀⁻². Route: ⟨Y_g²⟩⁰ by G3 (`dib_WW_2_2`) + `wh_Y_bound`;
  (F₁F_g)² ≤ (Γ²/2)F₁⁴ + (Γ⁻²/2)F_g⁴ (Γ > 0; Γ = 0 trivial), `wh_hyper`, ⟨F²⟩⁰ by `dib_WW_3_3`
  + `wh_F_bound`, with eΣ(C_B(x,·)δ)² ≤ (K₄ + D₄)/2 and eΣ g²δ² ≤ Γ²D₂, eΣ g² ≤ Γ²L².
* **`phiFourTwoGapV3_of_nelson_nonGaussian`**: (∀ m₀ l, 0 < m₀ → 0 ≤ l → NelsonRegionHyp m₀ l)
  and non-Gaussianity of the limit points at small λ ⟹ PhiFourTwoGapV3
  (`phiFourTwoGapV3_of_hyps` + the two discharges + `schwartzSeparable`).

NOT formalized here: NelsonRegionHyp (G4; reduced in PP2NelsonRegion to `nr_RoughL2Hyp`),
non-Gaussianity. Optimal constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Matrix Finset PP2Target PP2DoubleIBP PP2M5Final

open PP2Nelson PP2NelsonRegion

set_option maxHeartbeats 400000

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2WickHyps

/-! ## 3. The region: Green's function and Wick defect -/

section Region

variable {n k : ℕ}

theorem wh_GB_apply (m₀ : ℝ) (B : Finset (DSite n k)) (z z' : {x // x ∈ B}) :
    dib_GB n k m₀ B z z' = (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B z z' := by
  simp [dib_GB, Matrix.smul_apply]

theorem wh_GB_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (z z' : {x // x ∈ B}) :
    0 ≤ dib_GB n k m₀ B z z' := by
  rw [wh_GB_apply]; exact mul_nonneg (by positivity) (rg_regionGreen_nonneg hm B z z')

theorem wh_GB_symm {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (z z' : {x // x ∈ B}) :
    dib_GB n k m₀ B z z' = dib_GB n k m₀ B z' z := by
  rw [wh_GB_apply, wh_GB_apply]
  have h := ((fv2_regionOp_posDef hm B).1.inv).apply z' z
  simp only [star_trivial] at h
  unfold regionGreen
  rw [h]

theorem wh_GB_row {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (z : {x // x ∈ B}) :
    spacing n ^ 2 * ∑ z', dib_GB n k m₀ B z z' ≤ 1 / m₀ ^ 2 := by
  have e : spacing n ^ 2 * ∑ z', dib_GB n k m₀ B z z' = ∑ z', regionGreen n k m₀ B z z' := by
    rw [mul_sum]
    refine sum_congr rfl fun z' _ => ?_
    rw [wh_GB_apply, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 (spacing_pos n).ne'), one_mul]
  rw [e]; exact m5f_regionGreen_rowSum_le hm B z

theorem wh_GB_Lp {m₀ : ℝ} (hm : m₀ ≠ 0) (p : ℕ) (hp : 2 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n k : ℕ) (B : Finset (DSite n k)) (z : {x // x ∈ B}),
      spacing n ^ 2 * ∑ z', dib_GB n k m₀ B z z' ^ p ≤ K :=
  ⟨max ((Real.pi / 4) ^ (p - 1) / 2 * Real.Gamma ((p : ℝ)⁻¹) ^ p / m₀ ^ 2) 0, le_max_right _ _,
    fun n k B z => by
      simp only [wh_GB_apply]
      exact (mg_regionGreen_Lp_le hm p hp B z).trans (le_max_left _ _)⟩

theorem wh_defect_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (z : {x // x ∈ B}) :
    0 ≤ freeVar n m₀ - dib_GB n k m₀ B z z := by
  rw [wh_GB_apply]; exact nr_region_defect_nonneg hm B z

theorem wh_defect_le {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) (x : DSite n k)
    (y : {z // z ∈ physBall n k x l}) :
    freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) y y ≤
      Real.pi / 4 * (1 + Real.posLog (1 / (|m₀| *
        (spacing n * ((nr_M n k x (nr_rad n l) y : ℝ) + 1))))) := by
  rw [wh_GB_apply]
  exact nr_region_defect_le hm (nr_fits hl y.2) (nr_subBox_sub hl y.2) y.2

theorem wh_sqrt_eq (m₀ : ℝ) (i : ℕ) :
    √(1 / (|m₀| * (spacing n * ((i : ℝ) + 1)))) = (√|m₀|)⁻¹ * nl_f n i := by
  rw [nl_f, one_div, Real.sqrt_inv, Real.sqrt_mul (abs_nonneg _), mul_inv]

/-- δ² ≤ P(34 + 32 m' r^{−1/2}), P = (π/4)², m' = |m₀|^{−1/2}. -/
theorem wh_defect_sq_le {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) (x : DSite n k)
    (y : {z // z ∈ physBall n k x l}) :
    (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) y y) ^ 2 ≤
      (Real.pi / 4) ^ 2 * 34 + (Real.pi / 4) ^ 2 * 32 * (√|m₀|)⁻¹ *
        nl_f n (nr_M n k x (nr_rad n l) y) := by
  have h0 := wh_defect_nonneg hm (physBall n k x l) y
  have h1 := wh_defect_le hm hl x y
  set ℓ := Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x (nr_rad n l) y : ℝ) + 1)))) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
  have hℓ2 : ℓ ^ 2 ≤ 16 * (1 + (√|m₀|)⁻¹ * nl_f n (nr_M n k x (nr_rad n l) y)) := by
    rw [← wh_sqrt_eq]
    exact nl_posLog_sq_le (by have := spacing_pos n; positivity)
  have hP : 0 ≤ (Real.pi / 4) ^ 2 := sq_nonneg _
  have hsq : (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) y y) ^ 2 ≤
      (Real.pi / 4) ^ 2 * (1 + ℓ) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 2
  have h11 : (1 + ℓ) ^ 2 ≤ 2 * (1 + ℓ ^ 2) := by nlinarith [sq_nonneg (ℓ - 1)]
  have := mul_le_mul_of_nonneg_left h11 hP
  have := mul_le_mul_of_nonneg_left hℓ2 hP
  nlinarith

/-- δ⁴ ≤ P²(65544 + 65536 m' r^{−1/2}). -/
theorem wh_defect_four_le {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) (x : DSite n k)
    (y : {z // z ∈ physBall n k x l}) :
    (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) y y) ^ 4 ≤
      ((Real.pi / 4) ^ 2) ^ 2 * 65544 + ((Real.pi / 4) ^ 2) ^ 2 * 65536 * (√|m₀|)⁻¹ *
        nl_f n (nr_M n k x (nr_rad n l) y) := by
  have h0 := wh_defect_nonneg hm (physBall n k x l) y
  have h1 := wh_defect_le hm hl x y
  set ℓ := Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x (nr_rad n l) y : ℝ) + 1)))) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
  have hℓ4 : ℓ ^ 4 ≤ 8192 * (1 + (√|m₀|)⁻¹ * nl_f n (nr_M n k x (nr_rad n l) y)) := by
    rw [← wh_sqrt_eq]
    exact wh_posLog_four_le (by have := spacing_pos n; positivity)
  have hP : 0 ≤ ((Real.pi / 4) ^ 2) ^ 2 := by positivity
  have hsq : (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) y y) ^ 4 ≤
      ((Real.pi / 4) ^ 2) ^ 2 * (1 + ℓ) ^ 4 := by
    have : ((Real.pi / 4) ^ 2) ^ 2 * (1 + ℓ) ^ 4 = (Real.pi / 4 * (1 + ℓ)) ^ 4 := by ring
    rw [this]; exact pow_le_pow_left₀ h0 h1 4
  have h11 : (1 + ℓ) ^ 2 ≤ 2 * (1 + ℓ ^ 2) := by nlinarith [sq_nonneg (ℓ - 1)]
  have h12 : (1 + ℓ ^ 2) ^ 2 ≤ 2 * (1 + ℓ ^ 4) := by nlinarith [sq_nonneg (ℓ ^ 2 - 1)]
  have h14 : (1 + ℓ) ^ 4 ≤ 8 * (1 + ℓ ^ 4) := by
    have : ((1 + ℓ) ^ 2) ^ 2 ≤ (2 * (1 + ℓ ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h11 2
    nlinarith
  have := mul_le_mul_of_nonneg_left h14 hP
  have := mul_le_mul_of_nonneg_left hℓ4 hP
  nlinarith

/-- Summation over B of a + b r(y)^{−1/2}. -/
theorem wh_sum_bound {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) {A₀ B₀ : ℝ} (hA : 0 ≤ A₀) (hB : 0 ≤ B₀)
    (h : {z // z ∈ physBall n k x l} → ℝ)
    (hh : ∀ y, h y ≤ A₀ + B₀ * nl_f n (nr_M n k x (nr_rad n l) y)) :
    spacing n ^ 2 * ∑ y, h y ≤ A₀ * (2 * l + 1) ^ 2 + B₀ * (8 * ((2 * l + 1) * √(2 * l + 1))) := by
  have hcard : spacing n ^ 2 * ((physBall n k x l).card : ℝ) ≤ (2 * l + 1) ^ 2 := nr_card_le hl x
  have hfs := nr_sum_f_M (n := n) (k := k) hl x
  have hsc : ∑ y : {z // z ∈ physBall n k x l}, nl_f n (nr_M n k x (nr_rad n l) y) = ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x (nr_rad n l) y) :=
    Finset.sum_coe_sort (physBall n k x l) (fun y => nl_f n (nr_M n k x (nr_rad n l) y))
  have hsplit : ∑ y : {z // z ∈ physBall n k x l}, (A₀ + B₀ * nl_f n (nr_M n k x (nr_rad n l) y)) =
      A₀ * ((physBall n k x l).card : ℝ) + B₀ * ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x (nr_rad n l) y) := by
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, ← mul_sum, hsc]
    ring
  calc spacing n ^ 2 * ∑ y, h y ≤ spacing n ^ 2 * ∑ y : {z // z ∈ physBall n k x l},
        (A₀ + B₀ * nl_f n (nr_M n k x (nr_rad n l) y)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => hh y) (by positivity)
    _ = A₀ * (spacing n ^ 2 * ((physBall n k x l).card : ℝ)) +
          B₀ * (spacing n ^ 2 * ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x (nr_rad n l) y)) := by rw [hsplit]; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hcard hA) (mul_le_mul_of_nonneg_left hfs hB)

theorem wh_card_le {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    spacing n ^ 2 * ∑ _y : {z // z ∈ physBall n k x l}, (1 : ℝ) ≤ (2 * l + 1) ^ 2 := by
  rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]
  exact nr_card_le hl x

/-- **F4 in squared-sum form (WickDefectHyp), discharged.** -/
theorem wh_wickDefectHyp {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) : WickDefectHyp m₀ l :=
  ⟨(Real.pi / 4) ^ 2 * 34 * (2 * l + 1) ^ 2 +
      (Real.pi / 4) ^ 2 * 32 * (√|m₀|)⁻¹ * (8 * ((2 * l + 1) * √(2 * l + 1))),
    fun n k x => wh_sum_bound hl x (by positivity) (by positivity) _
      (fun y => wh_defect_sq_le hm hl x y)⟩

theorem wh_defect2 {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (n k : ℕ) (x : DSite n k),
      spacing n ^ 2 * ∑ z : {z // z ∈ physBall n k x l},
        (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) z z) ^ 2 ≤ D :=
  ⟨(Real.pi / 4) ^ 2 * 34 * (2 * l + 1) ^ 2 +
      (Real.pi / 4) ^ 2 * 32 * (√|m₀|)⁻¹ * (8 * ((2 * l + 1) * √(2 * l + 1))),
    by have : 0 ≤ 2 * l + 1 := by linarith
       positivity,
    fun n k x => wh_sum_bound hl x (by positivity) (by positivity) _
      (fun y => wh_defect_sq_le hm hl x y)⟩

theorem wh_defect4 {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (n k : ℕ) (x : DSite n k),
      spacing n ^ 2 * ∑ z : {z // z ∈ physBall n k x l},
        (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) z z) ^ 4 ≤ D :=
  ⟨((Real.pi / 4) ^ 2) ^ 2 * 65544 * (2 * l + 1) ^ 2 +
      ((Real.pi / 4) ^ 2) ^ 2 * 65536 * (√|m₀|)⁻¹ * (8 * ((2 * l + 1) * √(2 * l + 1))),
    by have : 0 ≤ 2 * l + 1 := by linarith
       positivity,
    fun n k x => wh_sum_bound hl x (by positivity) (by positivity) _
      (fun y => wh_defect_four_le hm hl x y)⟩

end Region

/-! ## 4. The free L² Wick moments -/

/-- **The free L² Wick moments (WickL2Hyp), discharged** (m₀ ≠ 0, l ≥ 0). -/
theorem wh_wickL2Hyp {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) : WickL2Hyp m₀ l := by
  obtain ⟨K2, hK2, hL2⟩ := wh_GB_Lp hm 2 le_rfl
  obtain ⟨K3, hK3, hL3⟩ := wh_GB_Lp hm 3 (by norm_num)
  obtain ⟨K4, hK4, hL4⟩ := wh_GB_Lp hm 4 (by norm_num)
  obtain ⟨D2, hD20, hD2⟩ := wh_defect2 hm hl
  obtain ⟨D4, hD40, hD4⟩ := wh_defect4 hm hl
  set S : ℝ := 1 / m₀ ^ 2 with hS
  set V : ℝ := (2 * l + 1) ^ 2 with hV
  set H : ℝ := (PP2Chaos2.ch2_rho 1)⁻¹ ^ 6 with hH
  set cY : ℝ := K2 * D2 + 2 * K2 ^ 2 with hcY
  set c1 : ℝ := 9 * (S * ((K4 + D4) / 2)) + 6 * (K3 * K2) with hc1
  set c2 : ℝ := 9 * (S * D2) + 6 * (K3 * V) with hc2
  set cF : ℝ := H ^ 2 * (c1 ^ 2 + c2 ^ 2) / 2 with hcF
  have hS0 : 0 ≤ S := by positivity
  have hV0 : 0 ≤ V := by positivity
  have hH0 : 0 ≤ H := by
    rw [hH]; exact pow_nonneg (inv_nonneg.mpr (PP2Chaos2.ch2_rho_nonneg 1)) 6
  have hcY0 : 0 ≤ cY := by positivity
  have hcF0 : 0 ≤ cF := by positivity
  have hKc : ∀ Γ c : ℝ, c ≤ 1 + cY + cF → Γ ^ 2 * c ≤ (Γ * (1 + cY + cF)) ^ 2 := by
    intro Γ c hc
    have : c ≤ (1 + cY + cF) ^ 2 := by nlinarith
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left this (sq_nonneg Γ)
  refine ⟨1 + cY + cF, by positivity, fun n k x hx Γ g hΓ hg => ?_⟩
  have hA := rg_scaledOp_posDef hm (physBall n k x l)
  have he : 0 ≤ spacing n ^ 2 := by positivity
  set c := freeVar n m₀ with hc
  set G := dib_GB n k m₀ (physBall n k x l) with hG
  have hGn : ∀ z z', 0 ≤ G z z' := wh_GB_nonneg hm (physBall n k x l)
  have hGs : ∀ z z', G z z' = G z' z := wh_GB_symm hm (physBall n k x l)
  have hrow : ∀ z, spacing n ^ 2 * ∑ z', G z z' ≤ S := wh_GB_row hm (physBall n k x l)
  have h2 : ∀ z, spacing n ^ 2 * ∑ z', G z z' ^ 2 ≤ K2 := hL2 n k (physBall n k x l)
  have h3 : ∀ z, spacing n ^ 2 * ∑ z', G z z' ^ 3 ≤ K3 := hL3 n k (physBall n k x l)
  have h4 : ∀ z, spacing n ^ 2 * ∑ z', G z z' ^ 4 ≤ K4 := hL4 n k (physBall n k x l)
  have hd2 : spacing n ^ 2 * ∑ z, (c - G z z) ^ 2 ≤ D2 := hD2 n k x
  have hd4 : spacing n ^ 2 * ∑ z, (c - G z z) ^ 4 ≤ D4 := hD4 n k x
  have hWW2 : ∀ z z', dib_WW (rg_scaledOp n k m₀ (physBall n k x l)) c z z' 2 2 =
      (c - G z z) * (c - G z' z') + 2 * G z z' ^ 2 := fun z z' => by
    rw [dib_WW_2_2 hA, ← dib_GB_eq hm]
  have hWW3 : ∀ z z', dib_WW (rg_scaledOp n k m₀ (physBall n k x l)) c z z' 3 3 =
      9 * G z z' * (c - G z z) * (c - G z' z') + 6 * G z z' ^ 3 := fun z z' => by
    rw [dib_WW_3_3 hA, ← dib_GB_eq hm]
  have hsec3 : ∀ w : {z // z ∈ physBall n k x l} → ℝ,
      dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => (spacing n ^ 2 * ∑ z, w z * wickPow c 3 (ψ z)) ^ 2) ≤
        9 * (S * (spacing n ^ 2 * ∑ z, (w z * (c - G z z)) ^ 2)) +
          6 * (K3 * (spacing n ^ 2 * ∑ z, w z ^ 2)) := by
    intro w
    rw [wh_ex0_sq hA c (spacing n ^ 2) w (by norm_num)]
    simp_rw [hWW3]
    exact wh_F_bound he G hGn hGs hrow h3 w
  constructor
  · -- ⟨Y_g²⟩⁰
    have hY : dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
        (fun ψ => m5f_Y n k m₀ (physBall n k x l) ⟨x, hx⟩ g ψ ^ 2) ≤ Γ ^ 2 * cY := by
      unfold m5f_Y
      rw [wh_ex0_sq hA c (spacing n ^ 2) (fun z => g z * G ⟨x, hx⟩ z) (by norm_num)]
      simp_rw [hWW2]
      exact wh_Y_bound he G hGs h2 hd2 ⟨x, hx⟩ g hg
    exact hY.trans (hKc Γ cY (by linarith))
  · -- ⟨(F₁F_g)²⟩⁰
    rcases hΓ.eq_or_lt with h0 | hΓp
    · have hg0 : ∀ z, g z = 0 := fun z => le_antisymm (h0 ▸ (hg z).2) (hg z).1
      have hz : (fun ψ => m5f_FF n k m₀ (physBall n k x l) ⟨x, hx⟩ g ψ ^ 2) = fun _ => 0 := by
        funext ψ; simp [m5f_FF, hg0]
      rw [hz, ← h0]
      simp [dib_ex0]
    · set t := Γ ^ 2 with ht
      have htp : 0 < t := by positivity
      -- F₁: second and fourth moments
      have hF1sq : dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => (spacing n ^ 2 * ∑ z, G ⟨x, hx⟩ z * wickPow c 3 (ψ z)) ^ 2) ≤ c1 := by
        refine (hsec3 (G ⟨x, hx⟩)).trans ?_
        have hX : spacing n ^ 2 * ∑ z, (G ⟨x, hx⟩ z * (c - G z z)) ^ 2 ≤ (K4 + D4) / 2 := by
          refine (wh_sum_prod_sq he (G ⟨x, hx⟩) (fun z => c - G z z)).trans ?_
          linarith [h4 ⟨x, hx⟩]
        have := mul_le_mul_of_nonneg_left hX hS0
        have := mul_le_mul_of_nonneg_left (h2 ⟨x, hx⟩) hK3
        rw [hc1]; linarith
      have hF1 : dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => (spacing n ^ 2 * ∑ z, G ⟨x, hx⟩ z * wickPow c 3 (ψ z)) ^ 4) ≤ (H * c1) ^ 2 :=
        (wh_hyper hA c (spacing n ^ 2) (G ⟨x, hx⟩)).trans
          (pow_le_pow_left₀ (mul_nonneg hH0 (wh_ex0_nonneg _ fun ψ => sq_nonneg _))
            (mul_le_mul_of_nonneg_left hF1sq hH0) 2)
      -- F_g
      have hFgsq : dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => (spacing n ^ 2 * ∑ z, g z * wickPow c 3 (ψ z)) ^ 2) ≤ t * c2 := by
        refine (hsec3 g).trans ?_
        have hX : spacing n ^ 2 * ∑ z, (g z * (c - G z z)) ^ 2 ≤ t * D2 :=
          (wh_sum_sq_le he g (fun z => c - G z z) hg).trans
            (mul_le_mul_of_nonneg_left hd2 (sq_nonneg Γ))
        have hY0 := wh_sum_sq_le he g (fun _ => (1 : ℝ)) hg
        simp only [mul_one, one_pow] at hY0
        have hY : spacing n ^ 2 * ∑ z, g z ^ 2 ≤ t * V :=
          hY0.trans (mul_le_mul_of_nonneg_left (wh_card_le hl x) (sq_nonneg Γ))
        have := mul_le_mul_of_nonneg_left hX hS0
        have := mul_le_mul_of_nonneg_left hY hK3
        rw [hc2]; nlinarith
      have hFg : dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => (spacing n ^ 2 * ∑ z, g z * wickPow c 3 (ψ z)) ^ 4) ≤ (H * (t * c2)) ^ 2 :=
        (wh_hyper hA c (spacing n ^ 2) g).trans
          (pow_le_pow_left₀ (mul_nonneg hH0 (wh_ex0_nonneg _ fun ψ => sq_nonneg _))
            (mul_le_mul_of_nonneg_left hFgsq hH0) 2)
      have hc4 := fun w : {z // z ∈ physBall n k x l} → ℝ =>
        (wh_cont_F c (spacing n ^ 2) w 3).pow 4
      have hg4 := fun w : {z // z ∈ physBall n k x l} → ℝ =>
        wh_grow_pow (wh_grow_F c (spacing n ^ 2) w (j := 3) (by norm_num)) 4
      calc dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
            (fun ψ => m5f_FF n k m₀ (physBall n k x l) ⟨x, hx⟩ g ψ ^ 2)
          ≤ dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l)) (fun ψ =>
              t / 2 * (spacing n ^ 2 * ∑ z, G ⟨x, hx⟩ z * wickPow c 3 (ψ z)) ^ 4 +
              t⁻¹ / 2 * (spacing n ^ 2 * ∑ z, g z * wickPow c 3 (ψ z)) ^ 4) := by
            refine wh_ex0_mono hA ((m5f_continuous_FF m₀ _ _ g).pow 2)
              (m5f_grow_sq (m5f_grow_FF m₀ _ _ g))
              ((continuous_const.mul (hc4 _)).add (continuous_const.mul (hc4 _)))
              (m5f_grow_add (m5f_grow_mul (m5f_grow_const _) (hg4 _))
                (m5f_grow_mul (m5f_grow_const _) (hg4 _))) (fun ψ => ?_)
            unfold m5f_FF
            have := wh_amgm htp ((spacing n ^ 2 * ∑ z, G ⟨x, hx⟩ z * wickPow c 3 (ψ z)) ^ 2)
              ((spacing n ^ 2 * ∑ z, g z * wickPow c 3 (ψ z)) ^ 2)
            calc _ = (spacing n ^ 2 * ∑ z, G ⟨x, hx⟩ z * wickPow c 3 (ψ z)) ^ 2 *
                  (spacing n ^ 2 * ∑ z, g z * wickPow c 3 (ψ z)) ^ 2 := by ring
              _ ≤ _ := this
              _ = _ := by ring
        _ = t / 2 * dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
              (fun ψ => (spacing n ^ 2 * ∑ z, G ⟨x, hx⟩ z * wickPow c 3 (ψ z)) ^ 4) +
            t⁻¹ / 2 * dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
              (fun ψ => (spacing n ^ 2 * ∑ z, g z * wickPow c 3 (ψ z)) ^ 4) :=
            wh_ex0_lin hA (hc4 _) (hg4 _) (hc4 _) (hg4 _) _ _
        _ ≤ t / 2 * (H * c1) ^ 2 + t⁻¹ / 2 * (H * (t * c2)) ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hF1 (by positivity))
              (mul_le_mul_of_nonneg_left hFg (by positivity))
        _ = Γ ^ 2 * cF := by
            rw [← ht, hcF]; field_simp
        _ ≤ (Γ * (1 + cY + cF)) ^ 2 := hKc Γ cF (by linarith)

/-! ## 5. The V3 target from the region Nelson bound and non-Gaussianity -/

/-- **PhiFourTwoGapV3 from the region Nelson bound (G4) and non-Gaussianity alone**
(`WickDefectHyp`, `WickL2Hyp` discharged here, `SchwartzSeparable` by `schwartzSeparable`). -/
theorem phiFourTwoGapV3_of_nelson_nonGaussian
    (hN : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → NelsonRegionHyp m₀ l)
    (hNG : ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₁ : ℝ, 0 < lam₁ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₁ →
      ∀ Z, IsLimitPoint m₀ lam Z → IsNonGaussian Z) : PhiFourTwoGapV3 :=
  phiFourTwoGapV3_of_hyps hN (fun _ _ hm hl => wh_wickDefectHyp hm.ne' hl)
    (fun _ _ hm hl => wh_wickL2Hyp hm.ne' hl) hNG schwartzSeparable

end PP2WickHyps

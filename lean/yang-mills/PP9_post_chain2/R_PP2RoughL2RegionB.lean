import LongTable.R_PP2RoughL2RegionA

/-!
Part B of PP2RoughL2Region (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2RoughL2Region.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* §2 Region linear forms: `rr_φs_eq`, `rr_φr_eq` (φ_s, φ_r as linear forms of ξˢ, ξʳ);
  `rr_eps_tau` (ε² nr_τ n T = T); `rr_lr_cov` (Σ_K ℓʳ_{yK} ℓʳ_{y'K} = C^B_r(T)(y,y'), from
  `mg_region_rough_cov`); `rr_cr_eq` (c_r(y) = Var φ_r(y)); `rr_ls_var` (Var φ_s(y) =
  ε⁻² regionGreen B y y − c_r(y), from `mg_smooth_cov` at t = 0 and `rg_scaledOp_inv`);
  `rr_ls_var_le` (Var φ_s ≤ c₁, by `nr_region_defect_nonneg`); `rr_Rω_eq` (nr_Rω = rr_R).
* §3 Region summation, s = T^{1/8}: `rr_G_sum_le` (ε² Σ_{y'∈B} G(y,y') ≤ K_G s⁴ from
  `mg_regionRough_Lp_le` (p = 2, 3, 4), AM-GM for p = 1 and ε²|B| ≤ L² (`nr_card_le`);
  K_G = `rr_KG l`); `rr_site_le` (s⁴(1 + c₁(y))³ ≤ s(Q₀ + Q₁ (ε(M_B(y)+1))^{−1/2}), from
  `nr_cs_bounds`); `rr_sum_site_le` (with `nr_sum_f_M`: ε² Σ_{y∈B} s⁴(1+c₁)³ ≤ s(Q₀L² + 8Q₁L^{3/2})).
* §4 **`rr_roughL2Hyp`**: m₀ ≠ 0 → 0 ≤ l → `nr_RoughL2Hyp m₀ l hm`, θ = 1/8,
  K = 96·K_G·15·(Q₀L² + 8Q₁L^{3/2}) (`rl_Q0`, `rl_Q1` of PP2RoughL2), uniform in n, k, x.
  **`nelsonRegion_holds`**: m₀ ≠ 0 → 0 ≤ l → `nl_NelsonRegion m₀ l` (Nelson's bound for the free
  region measures of the balls, G4 region version, unconditional).
  **`nelsonRegionHyp_holds`**: m₀ ≠ 0 → 0 ≤ l → `PP2M5Final.NelsonRegionHyp m₀ l` (the λ = 1
  ratio form of `nl_NelsonRegion`, rewritten with `rg_qweight_zeroExt` into `dib_ex0 (rg_scaledOp B)`).

NOT formalized (what remains): nothing for G4 at m₀ ≠ 0, l ≥ 0 (l < 0, B = ∅, is excluded, as in
`nr_smoothHyp`); optimal exponent θ (1/8 here, as for the box) and constants. The other two
hypotheses of PP2M5Final (`WickDefectHyp`, `WickL2Hyp`) are not addressed here.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Real Finset Matrix

open scoped ENNReal

set_option maxHeartbeats 400000

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2RoughL2Region

open PP2Target PP2Nelson PP2NelsonRegion PP2RoughL2

section Region

variable {n k : ℕ}

/-- Cov(φ_r(y), φ_r(y')) = Σ_K ℓʳ_{yK} ℓʳ_{y'K} = C^B_r(T)(y, y') (T ≥ 0). -/
theorem rr_lr_cov {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {T : ℝ} (hT : 0 ≤ T)
    (y y' : {z // z ∈ B}) :
    rr_C (rr_lr hm B T) y y' = mg_regionRough n k m₀ T B y y' := by
  have hτ := rr_tau_nonneg n hT
  have h := mg_region_rough_cov hm B hτ y y'
  rw [rr_eps_tau, mg_conj_apply] at h
  rw [← h, rr_C]
  refine sum_congr rfl fun K _ => ?_
  have hb := rr_β_sq hm B hτ K
  simp only [rr_lr]
  linear_combination (mg_modeMat (rg_scaledOp_posDef hm B) y K *
    mg_modeMat (rg_scaledOp_posDef hm B) y' K) * hb

/-- c_r(y) = Var φ_r(y) = Σ_K (ℓʳ_{yK})². -/
theorem rr_cr_eq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {T : ℝ} (hT : 0 ≤ T)
    (y : {z // z ∈ B}) :
    nr_cr n k m₀ T B y = ∑ K, rr_lr hm B T y K ^ 2 := by
  rw [nr_cr, ← rr_lr_cov hm B hT, rr_C]
  simp only [sq]

/-- Var φ_s(y) = Σ_K (ℓˢ_{yK})² = ε⁻² regionGreen B y y − c_r(y). -/
theorem rr_ls_var {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {T : ℝ} (hT : 0 ≤ T)
    (y : {z // z ∈ B}) :
    ∑ K, rr_ls hm B T y K ^ 2 =
      (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y y - nr_cr n k m₀ T B y := by
  have hτ := rr_tau_nonneg n hT
  have h0 := congrFun (congrFun (mg_smooth_cov (rg_scaledOp_posDef hm B) 0) y) y
  rw [mg_heat_zero, Matrix.one_mul, mg_conj_apply, rg_scaledOp_inv hm B, Matrix.smul_apply,
    smul_eq_mul] at h0
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h0
  rw [rr_cr_eq hm B hT, ← h0, eq_sub_iff_add_eq, ← sum_add_distrib]
  refine sum_congr rfl fun K _ => ?_
  have ha := rr_α_sq hm B (nr_τ n T) K
  have hb := rr_β_sq hm B hτ K
  simp only [rr_ls, rr_lr]
  linear_combination (mg_modeMat (rg_scaledOp_posDef hm B) y K) ^ 2 * ha +
    (mg_modeMat (rg_scaledOp_posDef hm B) y K) ^ 2 * hb

/-- Var φ_s(y) ≤ c₁(y) (the gap is the region Wick defect ≥ 0). -/
theorem rr_ls_var_le {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {T : ℝ} (hT : 0 ≤ T)
    (y : {z // z ∈ B}) :
    ∑ K, rr_ls hm B T y K ^ 2 ≤ nr_cs n k m₀ T B y := by
  rw [rr_ls_var hm B hT, nr_cs]
  linarith [nr_region_defect_nonneg hm B y]

/-- The region remainder as the generic remainder of the linear forms ℓˢ, ℓʳ. -/
theorem rr_Rω_eq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {T : ℝ} (hT : 0 ≤ T)
    (p : ({z // z ∈ B} → ℝ) × ({z // z ∈ B} → ℝ)) :
    nr_Rω hm B T p =
      rr_R (spacing n ^ 2) (nr_cs n k m₀ T B) (rr_ls hm B T) (rr_lr hm B T) p := by
  simp only [nr_Rω, nr_R, nr_Rg, rr_R, rr_S, rr_B, rr_cr_eq hm B hT]
  congr 1
  refine sum_congr rfl fun y _ => sum_congr rfl fun j _ => ?_
  rw [← rr_φs_eq hm B T p.1 y, ← rr_φr_eq hm B T p.2 y]

/-! ## 3. Region summation -/

/-- K_G = (L² + K₂)/2 + K₂ + K₃ + K₄, L = 2l + 1. -/
def rr_KG (l : ℝ) : ℝ := ((2 * l + 1) ^ 2 + rl_Kp 2) / 2 + rl_Kp 2 + rl_Kp 3 + rl_Kp 4

theorem rr_KG_nonneg (l : ℝ) : 0 ≤ rr_KG l := by
  have := rl_Kp_nonneg 2; have := rl_Kp_nonneg 3; have := rl_Kp_nonneg 4
  unfold rr_KG; positivity

/-- **Row sums of G (region):** for T = s⁸, 0 < s ≤ 1, and ε²|B| ≤ (2l+1)²,
ε² Σ_{y'∈B} G(y, y') ≤ K_G s⁴. -/
theorem rr_G_sum_le {m₀ : ℝ} (hm : m₀ ≠ 0) {B : Finset (DSite n k)} {l : ℝ}
    (hB : spacing n ^ 2 * (B.card : ℝ) ≤ (2 * l + 1) ^ 2) {T s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hTs : T = s ^ 8) (y : {z // z ∈ B}) :
    spacing n ^ 2 * ∑ y', rr_G (rr_lr hm B T) y y' ≤ rr_KG l * s ^ 4 := by
  have hT0 : 0 ≤ T := by rw [hTs]; positivity
  have hs4 : 0 < s ^ 4 := by positivity
  have hs84 : s ^ 8 ≤ s ^ 4 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
  simp only [rr_G, rr_lr_cov hm B hT0]
  have hpT : ∀ p : ℕ, 2 ≤ p →
      spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| ^ p ≤ rl_Kp p * T :=
    fun p hp => mg_regionRough_Lp_le m₀ hT0 p hp B y
  have hp4 : ∀ p : ℕ, 2 ≤ p →
      spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| ^ p ≤ rl_Kp p * s ^ 4 := by
    intro p hp
    refine (hpT p hp).trans ?_
    rw [hTs]
    exact mul_le_mul_of_nonneg_left hs84 (rl_Kp_nonneg p)
  have h1 : spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| ≤
      ((2 * l + 1) ^ 2 + rl_Kp 2) / 2 * s ^ 4 := by
    have hpt : ∀ y', |mg_regionRough n k m₀ T B y y'| ≤
        s ^ 4 / 2 + |mg_regionRough n k m₀ T B y y'| ^ 2 / (2 * s ^ 4) := by
      intro y'
      rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|mg_regionRough n k m₀ T B y y'| - s ^ 4)]
    have h2 := hpT 2 le_rfl
    have hε : 0 ≤ spacing n ^ 2 := by positivity
    calc spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'|
        ≤ spacing n ^ 2 * ∑ y', (s ^ 4 / 2 + |mg_regionRough n k m₀ T B y y'| ^ 2 / (2 * s ^ 4)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun y' _ => hpt y') hε
      _ = (spacing n ^ 2 * (B.card : ℝ)) * (s ^ 4 / 2) +
            (spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| ^ 2) / (2 * s ^ 4) := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, ← sum_div]
          ring
      _ ≤ (2 * l + 1) ^ 2 * (s ^ 4 / 2) + (rl_Kp 2 * T) / (2 * s ^ 4) := by
          gcongr
      _ = ((2 * l + 1) ^ 2 + rl_Kp 2) / 2 * s ^ 4 := by
          rw [hTs]; field_simp
  have hsum : spacing n ^ 2 * ∑ y', (|mg_regionRough n k m₀ T B y y'| +
        |mg_regionRough n k m₀ T B y y'| ^ 2 + |mg_regionRough n k m₀ T B y y'| ^ 3 +
        |mg_regionRough n k m₀ T B y y'| ^ 4) =
      spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| +
        spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| ^ 2 +
        spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| ^ 3 +
        spacing n ^ 2 * ∑ y', |mg_regionRough n k m₀ T B y y'| ^ 4 := by
    simp only [sum_add_distrib]; ring
  rw [hsum, rr_KG]
  have := hp4 2 (by norm_num); have := hp4 3 (by norm_num); have := hp4 4 (by norm_num)
  nlinarith

/-- **Per-site smooth factor (region):** for T = s⁸ ∈ (0, 1], y ∈ B = physBall x l,
s⁴ (1 + c₁(y))³ ≤ s (Q₀ + Q₁ (ε(M_B(y)+1))^{−1/2}). -/
theorem rr_site_le {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) {T s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hTs : T = s ^ 8) (y : {z // z ∈ physBall n k x l}) :
    s ^ 4 * (1 + nr_cs n k m₀ T (physBall n k x l) y) ^ 3 ≤
      s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (nr_M n k x (nr_rad n l) y)) := by
  have hT : 0 < T := by rw [hTs]; positivity
  have hT1 : T ≤ 1 := by rw [hTs]; exact pow_le_one₀ hs.le hs1
  set R := nr_rad n l with hR
  have h01 : 0 ≤ nr_cs n k m₀ T (physBall n k x l) y ∧ nr_cs n k m₀ T (physBall n k x l) y ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1))))) +
        π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) :=
    nr_cs_bounds hm hT hT1 (nr_fits hl y.2) (nr_subBox_sub hl y.2) y.2
  obtain ⟨h0, h1⟩ := h01
  set ℓ := Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1)))) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
  set m' : ℝ := (√|m₀|)⁻¹ with hm'
  have hm'0 : 0 ≤ m' := by positivity
  have hx : √(1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1)))) =
      m' * nl_f n (nr_M n k x R y) := by
    rw [nl_f, one_div, Real.sqrt_inv, Real.sqrt_mul (abs_nonneg _), mul_inv]
  have hℓ3 : ℓ ^ 3 ≤ 512 * (1 + m' * nl_f n (nr_M n k x R y)) := by
    rw [← hx]
    exact rl_posLog_cube_le (by have := spacing_pos n; positivity)
  obtain ⟨hL0, hL⟩ := rl_neglog_le hs hs1
  rw [← hTs] at hL0 hL
  have hπ : 0 ≤ π / 4 := by positivity
  set A := rl_a0 m₀ + π / 4 * ℓ with hA
  set e := π / 4 * (-Real.log T) with he
  have ha0 : 0 ≤ rl_a0 m₀ := by unfold rl_a0; positivity
  have hA0 : 0 ≤ A := by positivity
  have he0 : 0 ≤ e := mul_nonneg hπ hL0
  have h1' : 1 + nr_cs n k m₀ T (physBall n k x l) y ≤ A + e := by
    rw [hA, he, rl_a0]; linarith
  have hc3 : (1 + nr_cs n k m₀ T (physBall n k x l) y) ^ 3 ≤ 4 * (A ^ 3 + e ^ 3) :=
    (pow_le_pow_left₀ (by linarith) h1' 3).trans (rl_cube_add hA0 he0)
  have hA3 : A ^ 3 ≤
      4 * (rl_a0 m₀ ^ 3 + (π / 4) ^ 3 * (512 * (1 + m' * nl_f n (nr_M n k x R y)))) := by
    refine (rl_cube_add ha0 (mul_nonneg hπ hℓ0)).trans ?_
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left hℓ3 (pow_nonneg hπ 3)
    linarith
  have hs4 : s ^ 4 ≤ s := by
    calc s ^ 4 ≤ s ^ 1 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
      _ = s := pow_one s
  have he3 : s ^ 4 * e ^ 3 ≤ (π / 4) ^ 3 * (512 * s) := by
    rw [he, mul_pow]
    calc s ^ 4 * ((π / 4) ^ 3 * (-Real.log T) ^ 3) =
          (π / 4) ^ 3 * (s ^ 4 * (-Real.log T) ^ 3) := by ring
      _ ≤ (π / 4) ^ 3 * (512 * s) := mul_le_mul_of_nonneg_left hL (pow_nonneg hπ 3)
  have hsA : s ^ 4 * A ^ 3 ≤ s * A ^ 3 := mul_le_mul_of_nonneg_right hs4 (pow_nonneg hA0 3)
  calc s ^ 4 * (1 + nr_cs n k m₀ T (physBall n k x l) y) ^ 3 ≤ s ^ 4 * (4 * (A ^ 3 + e ^ 3)) :=
        mul_le_mul_of_nonneg_left hc3 (by positivity)
    _ = 4 * (s ^ 4 * A ^ 3) + 4 * (s ^ 4 * e ^ 3) := by ring
    _ ≤ 4 * (s * A ^ 3) + 4 * ((π / 4) ^ 3 * (512 * s)) := by linarith
    _ ≤ 4 * (s * (4 * (rl_a0 m₀ ^ 3 + (π / 4) ^ 3 *
            (512 * (1 + m' * nl_f n (nr_M n k x R y)))))) +
          4 * ((π / 4) ^ 3 * (512 * s)) := by
        have := mul_le_mul_of_nonneg_left hA3 hs.le
        linarith
    _ = s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (nr_M n k x R y)) := by
        rw [rl_Q0, rl_Q1, ← hm']; ring

/-- ε² Σ_{y∈B} s⁴(1 + c₁(y))³ ≤ s (Q₀ L² + 8 Q₁ L^{3/2}), L = 2l + 1. -/
theorem rr_sum_site_le {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) {T s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hTs : T = s ^ 8) :
    spacing n ^ 2 * ∑ y : {z // z ∈ physBall n k x l},
        s ^ 4 * (1 + nr_cs n k m₀ T (physBall n k x l) y) ^ 3 ≤
      s * (rl_Q0 m₀ * (2 * l + 1) ^ 2 + rl_Q1 m₀ * (8 * ((2 * l + 1) * √(2 * l + 1)))) := by
  set B := physBall n k x l with hB
  set R := nr_rad n l with hR
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  have hQ1 : 0 ≤ rl_Q1 m₀ := by unfold rl_Q1; positivity
  have hcard : spacing n ^ 2 * (B.card : ℝ) ≤ (2 * l + 1) ^ 2 := nr_card_le hl x
  have hfs : spacing n ^ 2 * ∑ y ∈ B, nl_f n (nr_M n k x R y) ≤
      8 * ((2 * l + 1) * √(2 * l + 1)) := nr_sum_f_M hl x
  have hsc : ∑ y : {z // z ∈ B}, nl_f n (nr_M n k x R y) = ∑ y ∈ B, nl_f n (nr_M n k x R y) :=
    Finset.sum_coe_sort B (fun y => nl_f n (nr_M n k x R y))
  calc spacing n ^ 2 * ∑ y : {z // z ∈ B}, s ^ 4 * (1 + nr_cs n k m₀ T B y) ^ 3
      ≤ spacing n ^ 2 * ∑ y : {z // z ∈ B}, s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (nr_M n k x R y)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => rr_site_le hm hl x hs hs1 hTs y) hε
    _ = s * (rl_Q0 m₀ * (spacing n ^ 2 * (B.card : ℝ)) +
          rl_Q1 m₀ * (spacing n ^ 2 * ∑ y ∈ B, nl_f n (nr_M n k x R y))) := by
        rw [← hsc]
        simp only [← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_coe,
          nsmul_eq_mul]
        ring
    _ ≤ s * (rl_Q0 m₀ * (2 * l + 1) ^ 2 + rl_Q1 m₀ * (8 * ((2 * l + 1) * √(2 * l + 1)))) := by
        apply mul_le_mul_of_nonneg_left _ hs.le
        have h1 := mul_le_mul_of_nonneg_left hcard (show 0 ≤ rl_Q0 m₀ by
          unfold rl_Q0 rl_a0; positivity)
        have h2 := mul_le_mul_of_nonneg_left hfs hQ1
        linarith

end Region

/-! ## 4. The region rough L² hypothesis, Nelson's bound for regions, the M5 bridge -/

section Main

/-- **Step 3 of Nelson's argument (region): the rough L² bound.** For m₀ ≠ 0 and l ≥ 0,
E_{γ^B⊗γ^B}[R_T²] ≤ K T^{1/8} for all n, k, x and T ∈ (0, 1] (B = physBall n k x l), with
K = 96 K_G 15 (Q₀ L² + 8 Q₁ L^{3/2}), L = 2l + 1, independent of n, k, x, T. -/
theorem rr_roughL2Hyp {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) : nr_RoughL2Hyp m₀ l hm := by
  refine ⟨96 * rr_KG l * 15 *
      (rl_Q0 m₀ * (2 * l + 1) ^ 2 + rl_Q1 m₀ * (8 * ((2 * l + 1) * √(2 * l + 1)))),
    1 / 8, by norm_num, fun n k x T hT hT1 => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = T ^ (1 / 8 : ℝ) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; exact Real.rpow_pos_of_pos hT _
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.rpow_le_one hT.le hT1 (by norm_num)
  have hTs : T = s ^ 8 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]; norm_num
  rw [← hsdef]
  set B := physBall n k x l with hB
  have hP : nr_P {z // z ∈ B} = (rr_g {z // z ∈ B}).prod (rr_g {z // z ∈ B}) := rfl
  have heq : (fun p => nr_Rω hm B T p ^ 2) = fun p =>
      rr_R (spacing n ^ 2) (nr_cs n k m₀ T B) (rr_ls hm B T) (rr_lr hm B T) p ^ 2 := by
    funext p; rw [rr_Rω_eq hm B hT.le p]
  rw [heq, hP]
  exact rr_ER2_bound (by positivity) (rr_ls_var_le hm B hT.le) (rr_lr hm B T)
    (rr_KG_nonneg l) (fun y => rr_G_sum_le hm (nr_card_le hl x) hs hs1 hTs y)
    (rr_sum_site_le hm hl x hs hs1 hTs)

/-- **Nelson's bound for regions (G4, region version), unconditional for m₀ ≠ 0, l ≥ 0.** -/
theorem nelsonRegion_holds {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) : nl_NelsonRegion m₀ l :=
  nl_nelsonRegion_of_roughL2 hm hl (rr_roughL2Hyp hm hl)

/-- **The hypothesis `NelsonRegionHyp` of PP2M5Final holds** (m₀ ≠ 0, l ≥ 0): the ratio form of
`nl_NelsonRegion` at λ = 1, with qweight m₀ 0 ∘ zeroExt B = gaussWeight (rg_scaledOp B). -/
theorem nelsonRegionHyp_holds {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) :
    PP2M5Final.NelsonRegionHyp m₀ l := by
  obtain ⟨N, hN⟩ := nelsonRegion_holds hm hl
  refine ⟨N, fun n k x => ?_⟩
  have h := (hN n k x 1 zero_le_one le_rfl).2
  unfold nr_free at h
  simp_rw [rg_qweight_zeroExt, mul_one] at h
  unfold PP2DoubleIBP.dib_ex0 PP2M5Final.m5f_V
  exact h

end Main

end PP2RoughL2Region

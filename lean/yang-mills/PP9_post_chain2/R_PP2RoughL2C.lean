import LongTable.R_PP2RoughL2B

/-!
Part C of PP2RoughL2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2RoughL2.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* §5, (d) summation, with s = T^{1/8} (T = s⁸): `rl_symm_sum` (symmetrisation);
  `rl_G_sum_le` (ε² Σ_{y'} G(y,y') ≤ K_G s⁴, from `glp_roughCov_Lp_le` for m = 2, 3, 4 and
  |C| ≤ s⁴/2 + |C|²/(2s⁴) for m = 1; K_G = `rl_KG k`); `rl_posLog_cube_le` ((log⁺x)³ ≤ 512(1+√x));
  `rl_neglog_le` (s⁴ (−log s⁸)³ ≤ 512 s); `rl_site_le` (s⁴(1+c₁(y))³ ≤ s (Q₀ + Q₁ r(y)^{−1/2}), from
  `nl_cs_bounds`); `rl_sum_site_le` (with `nl_sum_f_bdist`: ε² Σ_y s⁴(1+c₁)³ ≤ s (Q₀L² + 8Q₁L^{3/2})).
* §6, **`rl_roughL2Hyp`**: m₀ ≠ 0 → `nl_RoughL2Hyp m₀ k`, with θ = 1/8 and
  K = 96·15·K_G (Q₀ L² + 8 Q₁ L^{3/2}) (`rl_Q0`, `rl_Q1`, explicit in m₀ and L), uniform in n.
  **`rl_nelsonBox`**: m₀ ≠ 0 → `nl_NelsonBox m₀ k` (Nelson's bound for the box, G4 box version,
  now unconditional: `nl_nelsonBox_of_roughL2` + `rl_roughL2Hyp`).

NOT formalized (what remains): the region (physBall) version of G4 (same argument once the region
G1 / heat split / Lᵖ bounds are in place; `mg_region_*` exist in PP2ModesGen); Wick orthogonality
for degrees > 4 (not needed); optimal exponent (θ = 1/8 here, from the m = 1 term handled by
AM-GM; an L¹ bound ε² Σ_{y'} |C_r(y,y')| ≤ K T, e.g. from heat-kernel positivity, would give any
θ < 1); optimal constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal NNReal

set_option maxHeartbeats 400000

noncomputable section

namespace PP2RoughL2

open PP2Target PP2Nelson

variable {n k : ℕ}

/-! ## 5. (d) Summation -/

/-- Σ_a Σ_b ((M a + M b)/2) G a b = Σ_a M a Σ_b G a b for symmetric G. -/
theorem rl_symm_sum {ι : Type*} [Fintype ι] (M : ι → ℝ) (G : ι → ι → ℝ)
    (hG : ∀ a b, G a b = G b a) :
    ∑ a, ∑ b, (M a + M b) / 2 * G a b = ∑ a, M a * ∑ b, G a b := by
  have h2 : ∑ a, ∑ b, M b * G a b = ∑ a, ∑ b, M a * G a b := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [hG]
  have h3 : ∑ a, ∑ b, (M a + M b) / 2 * G a b =
      (∑ a, ∑ b, M a * G a b + ∑ a, ∑ b, M b * G a b) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun b _ => ?_
    ring
  rw [h3, h2, add_self_div_two]
  simp_rw [mul_sum]

/-- The Lᵖ constant of `glp_roughCov_Lp_le`: K_p = (π/4)^{p−1}/2 · p^p. -/
def rl_Kp (p : ℕ) : ℝ := (π / 4) ^ (p - 1) / 2 * (p : ℝ) ^ p

theorem rl_Kp_nonneg (p : ℕ) : 0 ≤ rl_Kp p := by unfold rl_Kp; positivity

/-- K_G = (L² + K₂)/2 + K₂ + K₃ + K₄. -/
def rl_KG (k : ℕ) : ℝ := (boxL k ^ 2 + rl_Kp 2) / 2 + rl_Kp 2 + rl_Kp 3 + rl_Kp 4

theorem rl_boxL_nonneg (k : ℕ) : 0 ≤ boxL k := by unfold boxL; positivity

theorem rl_KG_nonneg (k : ℕ) : 0 ≤ rl_KG k := by
  have := rl_Kp_nonneg 2; have := rl_Kp_nonneg 3; have := rl_Kp_nonneg 4
  unfold rl_KG; positivity

theorem rl_card (n k : ℕ) : spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ) = boxL k ^ 2 := by
  have hL : spacing n * (boxN n k : ℝ) = boxL k := nl_spacing_mul_boxN
  rw [Fintype.card_prod, Fintype.card_fin, ← hL]; push_cast; ring

/-- **Row sums of G:** for T = s⁸ with 0 < s ≤ 1, ε² Σ_{y'} G(y, y') ≤ K_G s⁴ uniformly in n
(`glp_roughCov_Lp_le` for m = 2, 3, 4; for m = 1, |C| ≤ s⁴/2 + |C|²/(2 s⁴)). -/
theorem rl_G_sum_le (m₀ : ℝ) {T s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hTs : T = s ^ 8)
    (y : DSite n k) :
    spacing n ^ 2 * ∑ y', rl_G n k m₀ T y y' ≤ rl_KG k * s ^ 4 := by
  have hT0 : 0 ≤ T := by rw [hTs]; positivity
  have hs4 : 0 < s ^ 4 := by positivity
  have hs84 : s ^ 8 ≤ s ^ 4 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
  have hpT : ∀ p : ℕ, 2 ≤ p →
      spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ p ≤ rl_Kp p * T :=
    fun p hp => glp_roughCov_Lp_le m₀ hT0 p hp y
  have hp4 : ∀ p : ℕ, 2 ≤ p →
      spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ p ≤ rl_Kp p * s ^ 4 := by
    intro p hp
    refine (hpT p hp).trans ?_
    rw [hTs]
    exact mul_le_mul_of_nonneg_left hs84 (rl_Kp_nonneg p)
  have h1 : spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ≤
      (boxL k ^ 2 + rl_Kp 2) / 2 * s ^ 4 := by
    have hpt : ∀ y', |glp_roughCov n k m₀ T y y'| ≤
        s ^ 4 / 2 + |glp_roughCov n k m₀ T y y'| ^ 2 / (2 * s ^ 4) := by
      intro y'
      rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|glp_roughCov n k m₀ T y y'| - s ^ 4)]
    have h2 := hpT 2 le_rfl
    have hε : 0 ≤ spacing n ^ 2 := by positivity
    calc spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'|
        ≤ spacing n ^ 2 * ∑ y', (s ^ 4 / 2 + |glp_roughCov n k m₀ T y y'| ^ 2 / (2 * s ^ 4)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun y' _ => hpt y') hε
      _ = (spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ)) * (s ^ 4 / 2) +
            (spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 2) / (2 * s ^ 4) := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← sum_div]; ring
      _ ≤ boxL k ^ 2 * (s ^ 4 / 2) + (rl_Kp 2 * T) / (2 * s ^ 4) := by
          rw [rl_card]
          gcongr
      _ = (boxL k ^ 2 + rl_Kp 2) / 2 * s ^ 4 := by
          rw [hTs]; field_simp
  have hsum : spacing n ^ 2 * ∑ y', rl_G n k m₀ T y y' =
      spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| +
        spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 2 +
        spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 3 +
        spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 4 := by
    simp only [rl_G, sum_add_distrib]; ring
  rw [hsum, rl_KG]
  have := hp4 2 (by norm_num); have := hp4 3 (by norm_num); have := hp4 4 (by norm_num)
  nlinarith

/-- (log⁺ x)³ ≤ 512 (1 + √x) for x ≥ 0 (log w ≤ w with w = x^{1/8}). -/
theorem rl_posLog_cube_le {x : ℝ} (hx : 0 ≤ x) : Real.posLog x ^ 3 ≤ 512 * (1 + √x) := by
  rw [Real.posLog_eq_log_max_one hx]
  set z := max 1 x with hz
  have hz1 : 1 ≤ z := le_max_left _ _
  have hs1 : ∀ a : ℝ, 1 ≤ a → 1 ≤ √a := fun a ha => by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt ha
  set w := √(√(√z)) with hw
  have hw1 : 1 ≤ w := hs1 _ (hs1 _ (hs1 _ hz1))
  have hw0 : 0 < w := by linarith
  have hw2 : w ^ 2 = √(√z) := by rw [hw, sq_sqrt (Real.sqrt_nonneg _)]
  have hw4 : w ^ 4 = √z := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hw2, sq_sqrt (Real.sqrt_nonneg _)]
  have hw8 : w ^ 8 = z := by
    rw [show 8 = 4 * 2 by rfl, pow_mul, hw4, sq_sqrt (by linarith)]
  have hlog : Real.log z = 8 * Real.log w := by
    rw [← hw8, Real.log_pow]; push_cast; ring
  have hl0 : 0 ≤ Real.log w := Real.log_nonneg hw1
  have hl1 : Real.log w ≤ w := by linarith [Real.log_le_sub_one_of_pos hw0]
  have hsz : √z ≤ 1 + √x := by
    rcases le_total 1 x with h | h
    · rw [hz, max_eq_right h]; linarith [Real.sqrt_nonneg x]
    · rw [hz, max_eq_left h, Real.sqrt_one]; linarith [Real.sqrt_nonneg x]
  have h3 : Real.log w ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ hl0 hl1 3
  have h34 : w ^ 3 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
  rw [hlog]
  calc (8 * Real.log w) ^ 3 = 512 * Real.log w ^ 3 := by ring
    _ ≤ 512 * w ^ 4 := by linarith
    _ = 512 * √z := by rw [hw4]
    _ ≤ 512 * (1 + √x) := by linarith

/-- For 0 < s ≤ 1: −log s⁸ ≥ 0 and s⁴ (−log s⁸)³ ≤ 512 s. -/
theorem rl_neglog_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ -Real.log (s ^ 8) ∧ s ^ 4 * (-Real.log (s ^ 8)) ^ 3 ≤ 512 * s := by
  have hl : Real.log (s ^ 8) = 8 * Real.log s := by rw [Real.log_pow]; push_cast; ring
  have hl0 : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have hinv : Real.log s⁻¹ ≤ s⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [Real.log_inv] at hinv
  have hst : s * (-Real.log s) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hinv hs.le
    rw [mul_sub, mul_inv_cancel₀ hs.ne', mul_one] at this
    linarith
  have hst0 : 0 ≤ s * (-Real.log s) := mul_nonneg hs.le (by linarith)
  refine ⟨by rw [hl]; linarith, ?_⟩
  rw [hl]
  have h3 : (s * (-Real.log s)) ^ 3 ≤ 1 := pow_le_one₀ hst0 hst
  calc s ^ 4 * (-(8 * Real.log s)) ^ 3 = 512 * s * (s * (-Real.log s)) ^ 3 := by ring
    _ ≤ 512 * s * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 512 * s := mul_one _

theorem rl_cube_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

/-- a₀ = 1 + π/4 + (π/4) m₀⁻². -/
def rl_a0 (m₀ : ℝ) : ℝ := 1 + π / 4 + π / 4 * (m₀ ^ 2)⁻¹

/-- Q₀ = 16 a₀³ + 10240 (π/4)³. -/
def rl_Q0 (m₀ : ℝ) : ℝ := 16 * rl_a0 m₀ ^ 3 + 10240 * (π / 4) ^ 3

/-- Q₁ = 8192 (π/4)³ |m₀|^{−1/2}. -/
def rl_Q1 (m₀ : ℝ) : ℝ := 8192 * (π / 4) ^ 3 * (√|m₀|)⁻¹

/-- **Per-site smooth factor:** for T = s⁸ ∈ (0, 1],
s⁴ (1 + c₁(y))³ ≤ s (Q₀ + Q₁ r(y)^{−1/2}) (with r(y)^{−1/2} = `nl_f n (fv2_bdist y)`). -/
theorem rl_site_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hTs : T = s ^ 8) (y : DSite n k) :
    s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3 ≤
      s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (fv2_bdist y)) := by
  have hT : 0 < T := by rw [hTs]; positivity
  have hT1 : T ≤ 1 := by rw [hTs]; exact pow_le_one₀ hs.le hs1
  obtain ⟨h0, h1⟩ := nl_cs_bounds hm hT hT1 y
  set ℓ := Real.posLog (1 / (|m₀| * fv2_rdist n k y)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
  set m' : ℝ := (√|m₀|)⁻¹ with hm'
  have hm'0 : 0 ≤ m' := by positivity
  have hx : √(1 / (|m₀| * fv2_rdist n k y)) = m' * nl_f n (fv2_bdist y) := by
    rw [fv2_rdist, nl_f, one_div, Real.sqrt_inv, Real.sqrt_mul (abs_nonneg _), mul_inv]
  have hℓ3 : ℓ ^ 3 ≤ 512 * (1 + m' * nl_f n (fv2_bdist y)) := by
    rw [← hx]
    exact rl_posLog_cube_le (by unfold fv2_rdist; have := spacing_pos n; positivity)
  obtain ⟨hL0, hL⟩ := rl_neglog_le hs hs1
  rw [← hTs] at hL0 hL
  have hπ : 0 ≤ π / 4 := by positivity
  set A := rl_a0 m₀ + π / 4 * ℓ with hA
  set e := π / 4 * (-Real.log T) with he
  have ha0 : 0 ≤ rl_a0 m₀ := by unfold rl_a0; positivity
  have hA0 : 0 ≤ A := by positivity
  have he0 : 0 ≤ e := mul_nonneg hπ hL0
  have h1' : 1 + nl_cs n k m₀ T y ≤ A + e := by
    rw [hA, he, rl_a0]; linarith
  have hc3 : (1 + nl_cs n k m₀ T y) ^ 3 ≤ 4 * (A ^ 3 + e ^ 3) :=
    (pow_le_pow_left₀ (by linarith) h1' 3).trans (rl_cube_add hA0 he0)
  have hA3 : A ^ 3 ≤ 4 * (rl_a0 m₀ ^ 3 + (π / 4) ^ 3 * (512 * (1 + m' * nl_f n (fv2_bdist y)))) := by
    refine (rl_cube_add ha0 (mul_nonneg hπ hℓ0)).trans ?_
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left hℓ3 (pow_nonneg hπ 3)
    linarith
  have hs4 : s ^ 4 ≤ s := by
    calc s ^ 4 ≤ s ^ 1 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
      _ = s := pow_one s
  have he3 : s ^ 4 * e ^ 3 ≤ (π / 4) ^ 3 * (512 * s) := by
    rw [he, mul_pow]
    calc s ^ 4 * ((π / 4) ^ 3 * (-Real.log T) ^ 3) = (π / 4) ^ 3 * (s ^ 4 * (-Real.log T) ^ 3) := by
          ring
      _ ≤ (π / 4) ^ 3 * (512 * s) := mul_le_mul_of_nonneg_left hL (pow_nonneg hπ 3)
  have hsA : s ^ 4 * A ^ 3 ≤ s * A ^ 3 := mul_le_mul_of_nonneg_right hs4 (pow_nonneg hA0 3)
  calc s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3 ≤ s ^ 4 * (4 * (A ^ 3 + e ^ 3)) :=
        mul_le_mul_of_nonneg_left hc3 (by positivity)
    _ = 4 * (s ^ 4 * A ^ 3) + 4 * (s ^ 4 * e ^ 3) := by ring
    _ ≤ 4 * (s * A ^ 3) + 4 * ((π / 4) ^ 3 * (512 * s)) := by linarith
    _ ≤ 4 * (s * (4 * (rl_a0 m₀ ^ 3 + (π / 4) ^ 3 * (512 * (1 + m' * nl_f n (fv2_bdist y)))))) +
          4 * ((π / 4) ^ 3 * (512 * s)) := by
        have := mul_le_mul_of_nonneg_left hA3 hs.le
        linarith
    _ = s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (fv2_bdist y)) := by
        rw [rl_Q0, rl_Q1, ← hm']; ring

theorem rl_sum_site_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hTs : T = s ^ 8) :
    spacing n ^ 2 * ∑ y : DSite n k, s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3 ≤
      s * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))) := by
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  have hQ1 : 0 ≤ rl_Q1 m₀ := by unfold rl_Q1; positivity
  have hfs := nl_sum_f_bdist (n := n) (k := k)
  calc spacing n ^ 2 * ∑ y : DSite n k, s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3
      ≤ spacing n ^ 2 * ∑ y : DSite n k, s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (fv2_bdist y)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => rl_site_le hm hs hs1 hTs y) hε
    _ = s * (rl_Q0 m₀ * (spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ)) +
          rl_Q1 m₀ * (spacing n ^ 2 * ∑ y : DSite n k, nl_f n (fv2_bdist y))) := by
        simp only [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
        ring
    _ ≤ s * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))) := by
        rw [rl_card]
        apply mul_le_mul_of_nonneg_left _ hs.le
        have := mul_le_mul_of_nonneg_left hfs hQ1
        linarith

/-! ## 6. The rough L² hypothesis and Nelson's bound for the box -/

/-- **Step 3 of Nelson's argument (box): the rough L² bound.** For m₀ ≠ 0 and every k,
E_{γ⊗γ}[R_T²] ≤ K T^{1/8} for all n and T ∈ (0, 1], with
K = 1440 K_G (Q₀ L² + 8 Q₁ L^{3/2}) independent of n and T. -/
theorem rl_roughL2Hyp {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ) : nl_RoughL2Hyp m₀ k := by
  refine ⟨96 * rl_KG k * 15 * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))),
    1 / 8, by norm_num, fun n T hT hT1 => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = T ^ (1 / 8 : ℝ) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; exact Real.rpow_pos_of_pos hT _
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.rpow_le_one hT.le hT1 (by norm_num)
  have hTs : T = s ^ 8 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]; norm_num
  rw [← hsdef]
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  have hKG := rl_KG_nonneg k
  calc ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k
      ≤ 96 * (spacing n ^ 2) ^ 2 * ∑ y, ∑ y',
          (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 * rl_G n k m₀ T y y' :=
        rl_ER2_le hm hT.le
    _ = 96 * spacing n ^ 2 * ∑ y, rl_M n k m₀ T y * (spacing n ^ 2 * ∑ y', rl_G n k m₀ T y y') := by
        rw [rl_symm_sum _ _ (rl_G_symm m₀ hT.le), mul_sum, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ ≤ 96 * spacing n ^ 2 * ∑ y, rl_M n k m₀ T y * (rl_KG k * s ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (rl_G_sum_le m₀ hs hs1 hTs y)
          (rl_M_nonneg hm hT.le y)
    _ = 96 * rl_KG k * 15 *
          (spacing n ^ 2 * ∑ y : DSite n k, s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3) := by
        simp only [rl_M, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ ≤ 96 * rl_KG k * 15 *
          (s * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k))))) :=
        mul_le_mul_of_nonneg_left (rl_sum_site_le hm hs hs1 hTs) (by positivity)
    _ = 96 * rl_KG k * 15 * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))) * s := by
        ring

/-- **Nelson's bound for the box (G4), unconditional for m₀ ≠ 0:**
∃ N, ∀ n, ∀ λ ∈ [0, 1], E⁰[exp(−2λ ε² Σ_y :φ_y⁴:)] ≤ N (both forms of `nl_NelsonBox`). -/
theorem rl_nelsonBox {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ) : nl_NelsonBox m₀ k :=
  nl_nelsonBox_of_roughL2 hm k (rl_roughL2Hyp hm k)

end PP2RoughL2

import LongTable.R_PP2NelsonA

/-!
Part B of PP2Nelson (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Nelson.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* Step 2: `nl_split_map` (φ_s + φ_r has law A_* γ^Λ, from `md_split_law`), `nl_V_split`
  (V(φ_s + φ_r) = V_s(φ_s) + R_T, `wickPow_add_binomial` with freeVar = c₁ + c_r),
  `nl_wick4_ge` (:y⁴:_c ≥ −6c², all real c), `nl_Vs_ge` (V_s ≥ −D(T)), `nl_free_eq`.
* Step 1 / reduction: `nl_nelsonBox_of_hyps`: nl_SmoothHyp ∧ nl_RoughL2Hyp ∧ nl_ChaosHyp ⇒
  nl_NelsonBox (any m₀, k; λ ∈ [0, 1] via e^{−2λv} ≤ 1 + e^{−2v}; N = 1 + nl_N a b (230⁸ K⁺) θ 24).
* Smooth constants (discharged): `nl_smoothHyp`: m₀ ≠ 0 ⇒ ∃ a b, ∀ n, ∀ T ∈ (0,1],
  D(T) ≤ a + b (log T)². Via `nl_cs_eq` (c₁ = b(y) + ε⁻²∫_{(T,∞)} p_t(y,y) dt, `integral_heatK`),
  `nl_tail_int_le` (≤ (π/4)(log(1/T) + m₀⁻²), from `glp_heatK_diag_le`), `nl_cs_bounds`
  (0 ≤ c₁ ≤ (π/4)(1 + log⁺(1/(|m₀| r(y)))) + (π/4)(log(1/T) + m₀⁻²), `fv2_wick_defect_le`,
  `dirVar_le_freeVar`), `nl_posLog_sq_le` ((log⁺x)² ≤ 16(1 + √x)), and the lattice sum
  `nl_sum_f_bdist`: ε² Σ_y r(y)^{−1/2} ≤ 8 L^{3/2} uniformly in n (min over the four walls,
  Σ_{i<N} (i+1)^{−1/2} ≤ 2√N).

NOT formalized (what remains): step 3, `nl_RoughL2Hyp m₀ k`:
  ∃ K θ, 0 < θ ∧ ∀ n, ∀ T ∈ (0, 1], E_{γ⊗γ}[R_T²] ≤ K T^θ.
  Needed: (a) E over the product factorises (smooth × rough); (b) Wick covariance of the rough
  field at its true variances, E[:φ_r(y)^a: :φ_r(y')^b:] = δ_ab a! C_r(y,y')^a (a, b ≤ 4), i.e.
  `wickPow_cross_cov` transported along the 2-D law of (φ_r(y), φ_r(y')) under γ^Λ (law
  identification, e.g. via characteristic functions); (c) misordered smooth covariances
  E[:φ_s(y)^j:_{c₁(y)} :φ_s(y')^j:_{c₁(y')}] bounded by K (1 + c₁(y))^j (1 + c₁(y'))^j (binomial
  re-ordering at δ = b(y) ≥ 0 plus (b)); (d) summation with `glp_roughCov_Lp_le`
  (ε² Σ_{y'} |C_r(y,y')|^m ≤ K_m T) and ε² Σ_y (1 + c₁(y))^6 ≤ K (1 + |log T|)^6 (as in
  `nl_sum_f_bdist`), giving K T (1 + |log T|)^6 ≤ K' T^{1/2}. The region (physBall) version of
  everything (same argument once the region G1 exists). Optimal constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal

set_option maxHeartbeats 400000

noncomputable section

namespace PP2Nelson

open PP2Target

variable {n k : ℕ}

/-- **Wick binomial split of V:** V(φs + φr) = V_s(φs) + R(φs, φr), with Wick constants
c₁(y) + c_r(y) = freeVar. -/
theorem nl_V_split (m₀ T : ℝ) (φs φr : DField n k) :
    nl_V n k m₀ (φs + φr) = nl_Vs n k m₀ T φs + nl_R n k m₀ T φs φr := by
  unfold nl_V nl_Vs nl_R
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  have hc : freeVar n m₀ = nl_cs n k m₀ T y + nl_cr n k m₀ T y := by unfold nl_cs; ring
  rw [Pi.add_apply, hc, wickPow_add_binomial, Finset.sum_range_succ, Nat.choose_self,
    Nat.sub_self, wickPow_zero']
  push_cast
  ring

/-- :y⁴:_c ≥ −6c² for every real c (min of y⁴ − 6cy² + 3c²). -/
theorem nl_wick4_ge (c y : ℝ) : -(6 * c ^ 2) ≤ wickPow c 4 y := by
  rw [wickPow_four']
  nlinarith [sq_nonneg (y ^ 2 - 3 * c)]

/-- **Smooth lower bound:** V_s(φ) ≥ −D(T) = −6 ε² Σ_y c₁(y)², pointwise. -/
theorem nl_Vs_ge (m₀ T : ℝ) (φ : DField n k) : -nl_D n k m₀ T ≤ nl_Vs n k m₀ T φ := by
  unfold nl_D nl_Vs
  have e : -(6 * spacing n ^ 2 * ∑ y : DSite n k, nl_cs n k m₀ T y ^ 2) =
      spacing n ^ 2 * ∑ y : DSite n k, -(6 * nl_cs n k m₀ T y ^ 2) := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => nl_wick4_ge _ _) (by positivity)

/-- E⁰[F] = ∫ F d(A_* γ^Λ) for continuous F. -/
theorem nl_free_eq (m₀ : ℝ) (F : DField n k → ℝ) (hF : Continuous F) :
    nl_free n k m₀ F = ∫ φ, F φ ∂(nl_gauss n k).map (md_map n k m₀) := by
  rw [nl_free, md_gauss_modes, integral_map (md_map_measurable m₀).aemeasurable
    hF.aestronglyMeasurable]
  rfl

/-! ## 3. The reduction: hypotheses (smooth constants, rough L², chaos) ⇒ Nelson bound -/

/-- **Smooth-constant hypothesis** (Wick defect + smooth variance, steps 2 of the plan):
ε²·6Σ_y c₁(T)(y)² ≤ a + b (log T)² for T ∈ (0, 1], uniformly in n. -/
def nl_SmoothHyp (m₀ : ℝ) (k : ℕ) : Prop :=
  ∃ a b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, ∀ T : ℝ, 0 < T → T ≤ 1 → nl_D n k m₀ T ≤ a + b * Real.log T ^ 2

/-- **Rough L² hypothesis** (step 3): E[R_T²] ≤ K T^θ for T ∈ (0, 1], uniformly in n. -/
def nl_RoughL2Hyp (m₀ : ℝ) (k : ℕ) : Prop :=
  ∃ K θ : ℝ, 0 < θ ∧ ∀ n : ℕ, ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k ≤ K * T ^ θ

/-- **Chaos hypothesis** (step 4; the conclusion of `ch2_degree_bound` with d = 4 for R_T,
which is a polynomial of total degree ≤ 4 in the 2|Λ| standard Gaussians (ξˢ, ξʳ)):
E[R^{2m+2}] ≤ (ρ_m^{−8} E[R²])^{m+1}. -/
def nl_ChaosHyp (m₀ : ℝ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ m : ℕ,
    ∫⁻ p, ENNReal.ofReal (nl_Rω n k m₀ T p ^ (2 * m + 2)) ∂nl_P n k ≤
      ENNReal.ofReal (((PP2Chaos2.ch2_rho m)⁻¹ ^ (2 * 4) *
        ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k) ^ (m + 1))

/-- **The target (G4, box version):** ∃ N, ∀ n, ∀ λ ∈ [0, 1], E⁰[e^{−2λV}] ≤ N, stated both
for the lintegral against the free measure μ⁰ = A_* γ^Λ (non-vacuous: it also gives
integrability; μ⁰ is the normalised density measure by `md_gauss_modes_measure`) and for the
ratio of Lebesgue integrals ∫ F e^{−S/2} / ∫ e^{−S/2} (`nl_free`). -/
def nl_NelsonBox (m₀ : ℝ) (k : ℕ) : Prop :=
  ∃ N : ℝ, ∀ n : ℕ, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    ∫⁻ φ, ENNReal.ofReal (Real.exp (-(2 * lam * nl_V n k m₀ φ)))
        ∂(nl_gauss n k).map (md_map n k m₀) ≤ ENNReal.ofReal N ∧
      nl_free n k m₀ (fun φ => Real.exp (-(2 * lam * nl_V n k m₀ φ))) ≤ N

theorem nl_rho_pow (m : ℕ) :
    (PP2Chaos2.ch2_rho m)⁻¹ ^ (2 * 4) = 230 ^ 8 * ((m : ℝ) + 1) ^ 24 := by
  unfold PP2Chaos2.ch2_rho
  rw [one_div, inv_inv, mul_pow, ← pow_mul]

theorem nl_exp_lam_le (lam v : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Real.exp (-(2 * lam * v)) ≤ 1 + Real.exp (-v) ^ 2 := by
  have e : Real.exp (-v) ^ 2 = Real.exp (-(2 * v)) := by rw [sq, ← Real.exp_add]; ring_nf
  rw [e]
  rcases le_total 0 v with hv | hv
  · have : Real.exp (-(2 * lam * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := mul_nonneg (mul_nonneg zero_le_two h0) hv; linarith)
    linarith [Real.exp_pos (-(2 * v))]
  · have : Real.exp (-(2 * lam * v)) ≤ Real.exp (-(2 * v)) := Real.exp_le_exp.mpr (by nlinarith)
    linarith

/-- **Nelson's bound for the box, reduced to the three hypotheses.** For every m₀ and box index
k: smooth-constant bound + rough L² bound + chaos (hypercontractive) bound ⇒
∃ N, ∀ n, ∀ λ ∈ [0,1], E⁰[exp(−2λ ε² Σ_y :φ_y⁴:)] ≤ N. Explicitly N = 2 + 2 e^{3 s₀} with
s₀ = `nl_s0 a b (230⁸ max(K,0)) θ 24`. -/
theorem nl_nelsonBox_of_hyps (m₀ : ℝ) (k : ℕ) (hS : nl_SmoothHyp m₀ k)
    (hL2 : nl_RoughL2Hyp m₀ k) (hC : nl_ChaosHyp m₀ k) : nl_NelsonBox m₀ k := by
  obtain ⟨a, b, hb, hSb⟩ := hS
  obtain ⟨K, θ, hθ, hK⟩ := hL2
  set M : ℝ := 230 ^ 8 * max K 0 with hMdef
  have hM : 0 ≤ M := by positivity
  refine ⟨1 + nl_N a b M θ 24, fun n lam hl0 hl1 => ?_⟩
  set μ := (nl_gauss n k).map (md_map n k m₀) with hμ
  have hT : ∀ u : ℝ, 0 < Real.exp (-u) := fun u => Real.exp_pos _
  have hT1 : ∀ u : ℝ, 0 ≤ u → Real.exp (-u) ≤ 1 := fun u hu =>
    Real.exp_le_one_iff.mpr (by linarith)
  have hmain : ∫⁻ φ, ENNReal.ofReal (Real.exp (-nl_V n k m₀ φ) ^ 2) ∂μ ≤
      ENNReal.ofReal (nl_N a b M θ 24) := by
    refine nl_abstract μ (nl_P n k) (nl_V n k m₀) (nl_V_continuous m₀).measurable
      (fun u p => nl_φs n k m₀ (Real.exp (-u)) p.1 + nl_φr n k m₀ (Real.exp (-u)) p.2)
      (fun u _ => nl_Φ_measurable m₀ _) (fun u _ => nl_split_map m₀ _ (hT u).le)
      (fun u p => nl_Rω n k m₀ (Real.exp (-u)) p) (fun u _ => nl_Rω_measurable m₀ _)
      24 hb hM hθ ?_ ?_
    · intro u hu p
      have h1 := nl_Vs_ge m₀ (Real.exp (-u)) (nl_φs n k m₀ (Real.exp (-u)) p.1)
      have h2 := hSb n (Real.exp (-u)) (hT u) (hT1 u hu)
      rw [Real.log_exp, neg_sq] at h2
      show nl_Rω n k m₀ (Real.exp (-u)) p - (a + b * u ^ 2) ≤ nl_V n k m₀ _
      rw [nl_V_split m₀ (Real.exp (-u)), nl_Rω]
      linarith
    · intro u hu m
      refine (hC n _ (hT u) (hT1 u hu) m).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI := hK n _ (hT u) (hT1 u hu)
      have hI0 : 0 ≤ ∫ p, nl_Rω n k m₀ (Real.exp (-u)) p ^ 2 ∂nl_P n k :=
        integral_nonneg fun _ => sq_nonneg _
      have hTθ : Real.exp (-u) ^ θ = Real.exp (-(θ * u)) := by
        rw [← Real.exp_mul]; ring_nf
      apply pow_le_pow_left₀ (mul_nonneg (pow_nonneg (inv_nonneg.mpr (PP2Chaos2.ch2_rho_nonneg m)) _) hI0)
      rw [nl_rho_pow]
      calc 230 ^ 8 * ((m : ℝ) + 1) ^ 24 * ∫ p, nl_Rω n k m₀ (Real.exp (-u)) p ^ 2 ∂nl_P n k
          ≤ 230 ^ 8 * ((m : ℝ) + 1) ^ 24 * (max K 0 * Real.exp (-(θ * u))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← hTθ]
            exact hI.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        _ = M * ((m : ℝ) + 1) ^ 24 * Real.exp (-(θ * u)) := by rw [hMdef]; ring
  have hFc : Continuous (fun φ : DField n k => Real.exp (-(2 * lam * nl_V n k m₀ φ))) :=
    (((nl_V_continuous m₀).const_mul (2 * lam)).neg).rexp
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hle : ∫⁻ φ, ENNReal.ofReal (Real.exp (-(2 * lam * nl_V n k m₀ φ))) ∂μ ≤
      ENNReal.ofReal (1 + nl_N a b M θ 24) := by
    calc ∫⁻ φ, ENNReal.ofReal (Real.exp (-(2 * lam * nl_V n k m₀ φ))) ∂μ
        ≤ ∫⁻ φ, (1 + ENNReal.ofReal (Real.exp (-nl_V n k m₀ φ) ^ 2)) ∂μ := by
          refine lintegral_mono fun φ => ?_
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
          exact ENNReal.ofReal_le_ofReal (nl_exp_lam_le lam _ hl0 hl1)
      _ = 1 + ∫⁻ φ, ENNReal.ofReal (Real.exp (-nl_V n k m₀ φ) ^ 2) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
      _ ≤ 1 + ENNReal.ofReal (nl_N a b M θ 24) := by gcongr
      _ = ENNReal.ofReal (1 + nl_N a b M θ 24) := by
          rw [ENNReal.ofReal_add zero_le_one (by unfold nl_N; positivity), ENNReal.ofReal_one]
  refine ⟨hle, ?_⟩
  rw [nl_free_eq m₀ _ hFc, ← hμ,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun φ => (Real.exp_pos _).le)
      hFc.aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (by unfold nl_N; positivity)] at this

/-! ## 4. Discharging the smooth-constant hypothesis (m₀ ≠ 0) -/

theorem nl_spacing_mul_boxN : spacing n * (boxN n k : ℝ) = boxL k := by
  unfold spacing boxN boxL
  push_cast
  rw [pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]

/-- c₁(T)(y) = b(y) + ε⁻² ∫_{(T,∞)} p_t(y, y) dt (Wick defect + smooth variance). -/
theorem nl_cs_eq (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    nl_cs n k m₀ T y = (freeVar n m₀ - (spacing n ^ 2)⁻¹ * dirGreen n k m₀ y y) +
      (spacing n ^ 2)⁻¹ * ∫ t in Set.Ioi T, heatK n k m₀ t y y := by
  have hI := glp_heatK_integrableOn (n := n) (k := k) m₀ y y
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), heatK n k m₀ t y y =
      (∫ t in Set.Ioc 0 T, heatK n k m₀ t y y) + ∫ t in Set.Ioi T, heatK n k m₀ t y y := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI.mono_set Set.Ioc_subset_Ioi_self) (hI.mono_set (Set.Ioi_subset_Ioi hT))
  rw [nl_cs, nl_cr, glp_roughCov, ← integral_heatK m₀ y y, hsplit]
  ring

theorem nl_tail_int_nonneg (m₀ T : ℝ) (y : DSite n k) :
    0 ≤ (spacing n ^ 2)⁻¹ * ∫ t in Set.Ioi T, heatK n k m₀ t y y :=
  mul_nonneg (by have := spacing_pos n; positivity)
    (setIntegral_nonneg measurableSet_Ioi fun t _ => heatK_diag_nonneg m₀ t y)

/-- Smooth variance: ε⁻² ∫_{(T,∞)} p_t(y, y) dt ≤ (π/4)(log(1/T) + m₀⁻²) for 0 < T ≤ 1. -/
theorem nl_tail_int_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (y : DSite n k) :
    (spacing n ^ 2)⁻¹ * ∫ t in Set.Ioi T, heatK n k m₀ t y y ≤
      π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) := by
  have hm2 : 0 < m₀ ^ 2 := by positivity
  have hI := glp_heatK_integrableOn (n := n) (k := k) m₀ y y
  set g : ℝ → ℝ := fun t => (spacing n ^ 2)⁻¹ * heatK n k m₀ t y y with hg
  have hgI : IntegrableOn g (Set.Ioi 0) := hI.const_mul _
  rw [← integral_const_mul]
  change ∫ t in Set.Ioi T, g t ≤ _
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT1, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hgI.mono_set (fun t ht => lt_trans hT ht.1))
    (hgI.mono_set (Set.Ioi_subset_Ioi zero_le_one))]
  have h1 : ∫ t in Set.Ioc T 1, g t ≤ π / 4 * (-Real.log T) := by
    have hinvI : IntegrableOn (fun t : ℝ => π / 4 * t⁻¹) (Set.Ioc T 1) := by
      have : ContinuousOn (fun t : ℝ => π / 4 * t⁻¹) (Set.Icc T 1) :=
        continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => (lt_of_lt_of_le hT ht.1).ne')
      exact (this.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    calc ∫ t in Set.Ioc T 1, g t ≤ ∫ t in Set.Ioc T 1, π / 4 * t⁻¹ := by
          refine setIntegral_mono_on (hgI.mono_set (fun t ht => lt_trans hT ht.1)) hinvI
            measurableSet_Ioc fun t ht => ?_
          have ht0 : 0 < t := lt_trans hT ht.1
          have hd := glp_heatK_diag_le m₀ ht0 y
          have he : Real.exp (-(t * m₀ ^ 2)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by have := mul_pos ht0 hm2; linarith)
          calc g t ≤ Real.exp (-(t * m₀ ^ 2)) * (π / (4 * t)) := hd
            _ ≤ 1 * (π / (4 * t)) := mul_le_mul_of_nonneg_right he (by positivity)
            _ = π / 4 * t⁻¹ := by field_simp
      _ = π / 4 * (-Real.log T) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hT1,
            integral_inv_of_pos hT one_pos, one_div, Real.log_inv]
  have h2 : ∫ t in Set.Ioi 1, g t ≤ π / 4 * (m₀ ^ 2)⁻¹ := by
    have hEI : IntegrableOn (fun t : ℝ => π / 4 * Real.exp (-(t * m₀ ^ 2))) (Set.Ioi 0) :=
      (integrableOn_exp_neg_mul_Ioi hm2).const_mul _
    calc ∫ t in Set.Ioi 1, g t ≤ ∫ t in Set.Ioi 1, π / 4 * Real.exp (-(t * m₀ ^ 2)) := by
          refine setIntegral_mono_on (hgI.mono_set (Set.Ioi_subset_Ioi zero_le_one))
            (hEI.mono_set (Set.Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi fun t ht => ?_
          have ht1 : 1 < t := ht
          have ht0 : 0 < t := by linarith
          have hd := glp_heatK_diag_le m₀ ht0 y
          calc g t ≤ Real.exp (-(t * m₀ ^ 2)) * (π / (4 * t)) := hd
            _ ≤ Real.exp (-(t * m₀ ^ 2)) * (π / 4) := by
                apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
            _ = π / 4 * Real.exp (-(t * m₀ ^ 2)) := by ring
      _ ≤ ∫ t in Set.Ioi 0, π / 4 * Real.exp (-(t * m₀ ^ 2)) :=
          setIntegral_mono_set hEI
            (Filter.Eventually.of_forall fun t => by simp only [Pi.zero_apply]; positivity)
            (Set.Ioi_subset_Ioi zero_le_one).eventuallySubset
      _ = π / 4 * (m₀ ^ 2)⁻¹ := by rw [integral_const_mul, integral_exp_neg_mul_Ioi hm2]
  linarith

/-- 0 ≤ c₁(T)(y) ≤ (π/4)(1 + log⁺(1/(|m₀| r(y)))) + (π/4)(log(1/T) + m₀⁻²). -/
theorem nl_cs_bounds {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (y : DSite n k) :
    0 ≤ nl_cs n k m₀ T y ∧ nl_cs n k m₀ T y ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * fv2_rdist n k y))) +
        π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) := by
  rw [nl_cs_eq m₀ hT.le y]
  have h1 := dirVar_le_freeVar hm y
  have h2 := fv2_wick_defect_le hm y
  have h3 := nl_tail_int_nonneg (n := n) (k := k) m₀ T y
  have h4 := nl_tail_int_le hm hT hT1 y
  constructor <;> linarith

/-- (log⁺ x)² ≤ 16 (1 + √x) for x ≥ 0 (log w ≤ w with w = x^{1/4}). -/
theorem nl_posLog_sq_le {x : ℝ} (hx : 0 ≤ x) : Real.posLog x ^ 2 ≤ 16 * (1 + √x) := by
  rw [Real.posLog_eq_log_max_one hx]
  set z := max 1 x with hz
  have hz1 : 1 ≤ z := le_max_left _ _
  have hsz1 : 1 ≤ √z := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hz1
  set w := √(√z) with hw
  have hw1 : 1 ≤ w := by
    rw [hw, show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hsz1
  have hw0 : 0 < w := by linarith
  have hw2 : w ^ 2 = √z := by rw [hw, sq_sqrt (Real.sqrt_nonneg _)]
  have hw4 : w ^ 4 = z := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hw2, sq_sqrt (by linarith)]
  have hlog : Real.log z = 4 * Real.log w := by
    rw [← hw4, Real.log_pow]; push_cast; ring
  have hl0 : 0 ≤ Real.log w := Real.log_nonneg hw1
  have hl1 : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hsz : √z ≤ 1 + √x := by
    rcases le_total 1 x with h | h
    · rw [hz, max_eq_right h]; linarith [Real.sqrt_nonneg x]
    · rw [hz, max_eq_left h, Real.sqrt_one]; linarith [Real.sqrt_nonneg x]
  rw [hlog]
  have hlw : Real.log w ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hl0 (by linarith) 2
  nlinarith

/-- f(i) = (ε (i+1))^{−1/2}, so that r(y)^{−1/2} = f(bdist y). -/
def nl_f (n : ℕ) (i : ℕ) : ℝ := (√(spacing n * ((i : ℝ) + 1)))⁻¹

theorem nl_f_nonneg (n i : ℕ) : 0 ≤ nl_f n i := by unfold nl_f; positivity

theorem nl_f_anti (n : ℕ) {i j : ℕ} (h : i ≤ j) : nl_f n j ≤ nl_f n i := by
  unfold nl_f
  have hs := spacing_pos n
  apply inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
  apply Real.sqrt_le_sqrt
  have : (i : ℝ) ≤ j := by exact_mod_cast h
  nlinarith

theorem nl_f_min (n i j : ℕ) : nl_f n (min i j) ≤ nl_f n i + nl_f n j := by
  rcases le_total i j with h | h
  · rw [min_eq_left h]; linarith [nl_f_nonneg n j]
  · rw [min_eq_right h]; linarith [nl_f_nonneg n i]

theorem nl_f_bdist (y : DSite n k) :
    nl_f n (fv2_bdist y) ≤ (nl_f n y.1 + nl_f n (boxN n k - 1 - y.1)) +
      (nl_f n y.2 + nl_f n (boxN n k - 1 - y.2)) := by
  unfold fv2_bdist
  exact (nl_f_min n _ _).trans (add_le_add (nl_f_min n _ _) (nl_f_min n _ _))

theorem nl_sum_inv_sqrt (N : ℕ) : ∑ i ∈ range N, (√((i : ℝ) + 1))⁻¹ ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have ha : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
    have hb : 0 < √((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsq : √((N : ℝ) + 1) ^ 2 = √(N : ℝ) ^ 2 + 1 := by
      rw [sq_sqrt (by positivity), sq_sqrt (by positivity)]
    have key : (√((N : ℝ) + 1))⁻¹ ≤ 2 * √((N : ℝ) + 1) - 2 * √(N : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ hb]
      nlinarith [sq_nonneg (√((N : ℝ) + 1) - √(N : ℝ))]
    push_cast
    linarith

theorem nl_sum_f_le (n N : ℕ) :
    ∑ i ∈ range N, nl_f n i ≤ (√(spacing n))⁻¹ * (2 * √(N : ℝ)) := by
  have he : ∀ i : ℕ, nl_f n i = (√(spacing n))⁻¹ * (√((i : ℝ) + 1))⁻¹ := by
    intro i
    rw [nl_f, Real.sqrt_mul (spacing_pos n).le, mul_inv]
  simp_rw [he, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (nl_sum_inv_sqrt N) (by positivity)

/-- **Lattice sum of the boundary singularity:** ε² Σ_y r(y)^{−1/2} ≤ 8 L^{3/2}, uniformly in n. -/
theorem nl_sum_f_bdist :
    spacing n ^ 2 * ∑ y : DSite n k, nl_f n (fv2_bdist y) ≤ 8 * (boxL k * √(boxL k)) := by
  set N := boxN n k with hN
  set S := ∑ i : Fin N, nl_f n i with hS
  have hrefl : ∑ i : Fin N, nl_f n (N - 1 - i) = S := by
    rw [hS, Fin.sum_univ_eq_sum_range (fun i => nl_f n (N - 1 - i)),
      Fin.sum_univ_eq_sum_range (fun i => nl_f n i), Finset.sum_range_reflect (fun i => nl_f n i)]
  have hSle : S ≤ (√(spacing n))⁻¹ * (2 * √(N : ℝ)) := by
    rw [hS, Fin.sum_univ_eq_sum_range (fun i => nl_f n i)]
    exact nl_sum_f_le n N
  have hsum : ∑ y : DSite n k, nl_f n (fv2_bdist y) ≤ 4 * N * S := by
    calc ∑ y : DSite n k, nl_f n (fv2_bdist y)
        ≤ ∑ y : DSite n k, ((nl_f n y.1 + nl_f n (N - 1 - y.1)) +
            (nl_f n y.2 + nl_f n (N - 1 - y.2))) := sum_le_sum fun y _ => nl_f_bdist y
      _ = 4 * N * S := by
        rw [Fintype.sum_prod_type]
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← mul_sum]
        rw [hrefl, ← hS, ← hN]
        ring
  have hε := spacing_pos n
  have hsε : 0 < √(spacing n) := Real.sqrt_pos.mpr hε
  have hL : spacing n * (N : ℝ) = boxL k := nl_spacing_mul_boxN
  have hsqL : √(boxL k) = √(spacing n) * √(N : ℝ) := by
    rw [← hL, Real.sqrt_mul hε.le]
  have hεs : spacing n = √(spacing n) * √(spacing n) := (mul_self_sqrt hε.le).symm
  calc spacing n ^ 2 * ∑ y : DSite n k, nl_f n (fv2_bdist y)
      ≤ spacing n ^ 2 * (4 * N * ((√(spacing n))⁻¹ * (2 * √(N : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum.trans (mul_le_mul_of_nonneg_left hSle (by positivity))
    _ = 8 * (boxL k * √(boxL k)) := by
        rw [hsqL, ← hL]
        set s := √(spacing n) with hs
        rw [hεs]
        field_simp
        ring

end PP2Nelson

end

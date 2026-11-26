import LongTable.PP2Modes
import LongTable.PP2GreenLp
import LongTable.PP2FreeVar2
import LongTable.PP2Chaos2
import LongTable.PP2PortNelson1

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node G4 of the M5
plan (Nelson's bound), session 1, BOX version (namespace `PP2Nelson`).

Target (`nl_NelsonBox m₀ k`): ∃ N, ∀ n, ∀ λ ∈ [0, 1],
  ∫⁻ e^{−2λV} dμ⁰ ≤ N  and  (∫ e^{−2λV} e^{−S/2} dφ)/(∫ e^{−S/2} dφ) ≤ N,
where V = ε² Σ_y :φ_y⁴:_{freeVar} (`nl_V`), S = `dirAction n k m₀`, μ⁰ = A_* γ^Λ (G1,
`md_gauss_modes`), and the box DSite n k has the FIXED side L = boxL k = 2^k (ε = 2^{−n}).
N depends on m₀, k only.

Notation: T ∈ (0, 1] the heat-kernel cutoff, (ξˢ, ξʳ) ~ γ^Λ ⊗ γ^Λ (`nl_P`), φ_s = A(e^{−Tλ/2} ξˢ),
φ_r = A(√(1 − e^{−Tλ}) ξʳ) (`nl_φs`, `nl_φr`, as in `md_heat_split`), c_r(y) = C_r(T)(y, y)
(`nl_cr`, = `glp_roughCov` on the diagonal = Var φ_r(y)), c₁(y) = freeVar − c_r(y) (`nl_cs`),
V_s = ε²Σ :φ_s⁴:_{c₁} (`nl_Vs`), R_T = ε²Σ_y Σ_{j<4} C(4,j) :φ_s^j:_{c₁(y)} :φ_r^{4−j}:_{c_r(y)}
(`nl_R`, `nl_Rω`), D(T) = 6ε²Σ c₁² (`nl_D`).

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* Step 5, abstract Nelson argument `nl_abstract`: μ = law of Φ_u under a probability P for each
  u ≥ 0; if V∘Φ_u ≥ R_u − (a + b u²) and E[R_u^{2m+2}] ≤ (M (m+1)^p e^{−θu})^{m+1} for all m,
  then ∫⁻ e^{−2V} dμ ≤ N = 1 + 2e^{3 s₀} (`nl_N`, `nl_s0`, explicit in a, b, M, θ, p). Proof:
  for s > s₀ take u = √s/(2√(b+1)) (so a + bu² ≤ s/2) and q = ⌈3s⌉ in Markov (`nl_tail`), with
  M q^p e^{−θu} ≤ 1/3 from e^x ≥ x^{2p+2}/(2p+2)! (`nl_X_le`); tail ≤ e^{−3s}; then
  `PP2Port.LayerCake.lintegral_expSq_neg_le_layer_cake`.
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
* Step 4 (discharged): `nl_e` / `nl_e_mp` (ℝ^{Fin 2|Λ|} ≃ᵐ ℝ^Λ × ℝ^Λ, measure preserving from
  `ch2_gauss` to `nl_P`; `Fintype.equivFin`, `measurePreserving_piCongrLeft`,
  `measurePreserving_sumPiEquivProdPi`); `nl_chaosHyp_of_repr` (a Hermite representation with
  |α| ≤ 4 gives the chaos bound, via `ch2_hyper_lintegral` at ρ_m); `nl_mvpoly_herm` (every
  MvPolynomial of total degree ≤ 4 is such an F_c: monomials via t^j = Σ a(j,q) He_q,
  `Finset.prod_univ_sum`); `nl_RMv`, `nl_RMv_eval`, `nl_RMv_deg` (R_T ∘ nl_e is an explicit
  polynomial of total degree ≤ 4); hence **`nl_chaosHyp m₀ k`** for all m₀, k.
* **Main theorem `nl_nelsonBox_of_roughL2`**: m₀ ≠ 0 → nl_RoughL2Hyp m₀ k → nl_NelsonBox m₀ k.
  (Intermediate forms: `nl_nelsonBox_of_rough`, `nl_nelsonBox_of_rough_repr`,
  `nl_nelsonBox_of_rough_poly`.)

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

/-! ## 1. The abstract Nelson argument (dyadic choice of the cutoff + layer cake) -/

/-- κ = θ / (2 √(b+1)): with u = √s / (2√(b+1)) one has θ u = κ √s and b u² ≤ s/4. -/
def nl_kappa (b θ : ℝ) : ℝ := θ / (2 * √(b + 1))

/-- The threshold s₀ beyond which the tail is ≤ e^{−3s}. -/
def nl_s0 (a b M θ : ℝ) (p : ℕ) : ℝ :=
  max (max 2 (4 * a)) (3 * M * 4 ^ p * ((2 * p + 2).factorial : ℝ) / nl_kappa b θ ^ (2 * p + 2))

/-- The explicit Nelson constant N = 1 + 2 e^{3 s₀}. -/
def nl_N (a b M θ : ℝ) (p : ℕ) : ℝ := 1 + 2 * Real.exp (3 * nl_s0 a b M θ p)

theorem nl_kappa_pos {b θ : ℝ} (hb : 0 ≤ b) (hθ : 0 < θ) : 0 < nl_kappa b θ := by
  unfold nl_kappa
  have : 0 < √(b + 1) := Real.sqrt_pos.mpr (by linarith)
  positivity

theorem nl_exp_lower (κ t : ℝ) (hκ : 0 < κ) (ht : 0 < t) (p : ℕ) :
    κ ^ (2 * p + 2) * t ^ (p + 1) / ((2 * p + 2).factorial : ℝ) ≤ Real.exp (κ * √t) := by
  have h := Real.pow_div_factorial_le_exp (x := κ * √t) (by positivity) (2 * p + 2)
  have e : (κ * √t) ^ (2 * p + 2) = κ ^ (2 * p + 2) * t ^ (p + 1) := by
    rw [mul_pow, show 2 * p + 2 = 2 * (p + 1) by ring, pow_mul (√t), sq_sqrt ht.le]
  rwa [e] at h

/-- The base of the moment bound is ≤ 1/3 once s is large. -/
theorem nl_X_le {b M θ t : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) (hθ : 0 < θ) (p : ℕ) {q : ℕ}
    (ht1 : 1 ≤ t) (hq : (q : ℝ) ≤ 4 * t)
    (hts : 3 * M * 4 ^ p * ((2 * p + 2).factorial : ℝ) / nl_kappa b θ ^ (2 * p + 2) ≤ t) :
    M * (q : ℝ) ^ p * Real.exp (-(θ * (√t / (2 * √(b + 1))))) ≤ 1 / 3 := by
  have hκ : 0 < nl_kappa b θ := nl_kappa_pos hb hθ
  set κ := nl_kappa b θ with hκdef
  have ht : 0 < t := by linarith
  have hθu : θ * (√t / (2 * √(b + 1))) = κ * √t := by rw [hκdef, nl_kappa]; ring
  rw [hθu]
  set F : ℝ := ((2 * p + 2).factorial : ℝ) with hF
  have hFpos : 0 < F := by positivity
  have hk2 : 0 < κ ^ (2 * p + 2) := by positivity
  have htp : 0 < t ^ (p + 1) := by positivity
  have hE := nl_exp_lower κ t hκ ht p
  have hexp : Real.exp (-(κ * √t)) ≤ F / (κ ^ (2 * p + 2) * t ^ (p + 1)) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    rw [div_le_iff₀ hFpos] at hE
    linarith
  have hqp : (q : ℝ) ^ p ≤ (4 * t) ^ p := pow_le_pow_left₀ (Nat.cast_nonneg _) hq p
  have hA : M * (q : ℝ) ^ p * Real.exp (-(κ * √t)) ≤
      M * (4 * t) ^ p * (F / (κ ^ (2 * p + 2) * t ^ (p + 1))) := by
    have h1 : 0 ≤ M * (q : ℝ) ^ p := by positivity
    calc M * (q : ℝ) ^ p * Real.exp (-(κ * √t))
        ≤ M * (q : ℝ) ^ p * (F / (κ ^ (2 * p + 2) * t ^ (p + 1))) :=
          mul_le_mul_of_nonneg_left hexp h1
      _ ≤ M * (4 * t) ^ p * (F / (κ ^ (2 * p + 2) * t ^ (p + 1))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hqp hM
  have hB : M * (4 * t) ^ p * (F / (κ ^ (2 * p + 2) * t ^ (p + 1))) =
      M * 4 ^ p * F / κ ^ (2 * p + 2) / t := by
    rw [mul_pow, pow_succ]
    field_simp
    ring
  rw [hB] at hA
  refine hA.trans ?_
  rw [div_le_div_iff₀ ht (by norm_num)]
  have : 3 * M * 4 ^ p * F / κ ^ (2 * p + 2) = 3 * (M * 4 ^ p * F / κ ^ (2 * p + 2)) := by ring
  linarith

/-- Markov at an even moment: if R − D ≤ W, D ≤ t/2, t ≥ 2, then P{W ≤ −t} ≤ E[R^{2m+2}]. -/
theorem nl_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W R : Ω → ℝ) (hR : Measurable R) {D t : ℝ} (hDt : D ≤ t / 2) (ht : 2 ≤ t)
    (hdec : ∀ ω, R ω - D ≤ W ω) (m : ℕ) (Y : ℝ≥0∞)
    (hmom : ∫⁻ ω, ENNReal.ofReal (R ω ^ (2 * m + 2)) ∂P ≤ Y) :
    P {ω | W ω ≤ -t} ≤ Y := by
  set S := {ω | ENNReal.ofReal ((t / 2) ^ (2 * m + 2)) ≤ ENNReal.ofReal (R ω ^ (2 * m + 2))}
  have hsub : {ω | W ω ≤ -t} ⊆ S := by
    intro ω hω
    have hω' : W ω ≤ -t := hω
    show ENNReal.ofReal _ ≤ ENNReal.ofReal _
    apply ENNReal.ofReal_le_ofReal
    have h1 : R ω ≤ -(t / 2) := by linarith [hdec ω]
    have h2 : t / 2 ≤ |R ω| := by rw [abs_of_nonpos (by linarith)]; linarith
    calc (t / 2) ^ (2 * m + 2) ≤ |R ω| ^ (2 * m + 2) := pow_le_pow_left₀ (by linarith) h2 _
      _ = R ω ^ (2 * m + 2) := by
          rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, pow_mul, sq_abs]
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P)
    (f := fun ω => ENNReal.ofReal (R ω ^ (2 * m + 2)))
    ((hR.pow_const _).ennreal_ofReal.aemeasurable) (ENNReal.ofReal ((t / 2) ^ (2 * m + 2)))
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((t / 2) ^ (2 * m + 2)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith))
  calc P {ω | W ω ≤ -t} ≤ P S := measure_mono hsub
    _ = 1 * P S := (one_mul _).symm
    _ ≤ ENNReal.ofReal ((t / 2) ^ (2 * m + 2)) * P S := mul_le_mul_left h1 _
    _ ≤ _ := hmk
    _ ≤ Y := hmom

/-- **Abstract Nelson estimate.** Let μ be the law of Φ_u under a probability P for every u ≥ 0
(one representation per cutoff), and suppose that for every u ≥ 0
(i) V ∘ Φ_u ≥ R_u − (a + b u²) pointwise, and
(ii) E[R_u^{2m+2}] ≤ (M (m+1)^p e^{−θu})^{m+1} for all m.
Then ∫ e^{−2V} dμ ≤ N(a, b, M, θ, p) = 1 + 2 e^{3 s₀}, an explicit constant depending only on
a, b, M, θ, p. -/
theorem nl_abstract {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure X) (P : Measure Ω) [IsProbabilityMeasure P]
    (V : X → ℝ) (hV : Measurable V)
    (Φ : ℝ → Ω → X) (hΦm : ∀ u, 0 ≤ u → Measurable (Φ u))
    (hΦ : ∀ u, 0 ≤ u → P.map (Φ u) = μ)
    (R : ℝ → Ω → ℝ) (hRm : ∀ u, 0 ≤ u → Measurable (R u))
    {a b M θ : ℝ} (p : ℕ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hθ : 0 < θ)
    (hdec : ∀ u, 0 ≤ u → ∀ ω, R u ω - (a + b * u ^ 2) ≤ V (Φ u ω))
    (hmom : ∀ u, 0 ≤ u → ∀ m : ℕ, ∫⁻ ω, ENNReal.ofReal (R u ω ^ (2 * m + 2)) ∂P ≤
      ENNReal.ofReal ((M * ((m : ℝ) + 1) ^ p * Real.exp (-(θ * u))) ^ (m + 1))) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-V x) ^ 2) ∂μ ≤ ENNReal.ofReal (nl_N a b M θ p) := by
  have : IsProbabilityMeasure μ := by rw [← hΦ 0 le_rfl]; infer_instance
  set s₀ := nl_s0 a b M θ p with hs₀
  have hs2 : 2 ≤ s₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hs4a : 4 * a ≤ s₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hs1 : 3 * M * 4 ^ p * ((2 * p + 2).factorial : ℝ) / nl_kappa b θ ^ (2 * p + 2) ≤ s₀ :=
    le_max_right _ _
  -- the tail bound beyond s₀
  have htail : ∀ t, s₀ < t → μ {x | V x ≤ -t} ≤ ENNReal.ofReal (Real.exp (-(3 * t))) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hb1 : 0 < √(b + 1) := Real.sqrt_pos.mpr (by linarith)
    set u := √t / (2 * √(b + 1)) with hu_def
    have hu : 0 ≤ u := by positivity
    set q : ℕ := ⌈3 * t⌉₊ with hq_def
    have hq3 : 3 * t ≤ (q : ℝ) := Nat.le_ceil _
    have hq4 : (q : ℝ) ≤ 4 * t := by
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * t by linarith)
      linarith
    have hq1 : 1 ≤ q := by
      have : (0 : ℝ) < q := by linarith
      exact_mod_cast this
    set m := q - 1 with hm_def
    have hmq : (m : ℝ) + 1 = q := by
      rw [hm_def, Nat.cast_sub hq1]; push_cast; ring
    have hmq' : m + 1 = q := by omega
    have hμ : μ {x | V x ≤ -t} = P {ω | V (Φ u ω) ≤ -t} := by
      rw [← hΦ u hu, Measure.map_apply (hΦm u hu) (measurableSet_le hV measurable_const)]
      rfl
    rw [hμ]
    have hD : a + b * u ^ 2 ≤ t / 2 := by
      have hu2 : u ^ 2 = t / (4 * (b + 1)) := by
        rw [hu_def, div_pow, mul_pow, sq_sqrt ht0.le, sq_sqrt (by linarith)]
        ring
      have hbu : b * u ^ 2 ≤ t / 4 := by
        rw [hu2, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    set Xb := M * ((m : ℝ) + 1) ^ p * Real.exp (-(θ * u)) with hXb
    have hX0 : 0 ≤ Xb := by positivity
    refine (nl_tail P (fun ω => V (Φ u ω)) (R u) (hRm u hu) hD (by linarith) (hdec u hu) m _
      (hmom u hu m)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hX : Xb ≤ 1 / 3 := by
      rw [hXb, hmq]
      exact nl_X_le hb hM hθ p (by linarith) hq4 (by linarith)
    have he : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (Real.exp_pos _)
      have := Real.exp_one_lt_d9
      linarith
    calc Xb ^ (m + 1) ≤ Real.exp (-1) ^ (m + 1) := pow_le_pow_left₀ hX0 (hX.trans he) _
      _ = Real.exp (-((m : ℝ) + 1)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (-(3 * t)) := by
          apply Real.exp_le_exp.mpr
          rw [hmq]; linarith
  -- layer cake
  refine (PP2Port.LayerCake.lintegral_expSq_neg_le_layer_cake μ V hV).trans ?_
  rw [measure_univ]
  set C := 2 * Real.exp (3 * s₀) with hC
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), μ {x | V x ≤ -t} * ENNReal.ofReal (2 * Real.exp (2 * t)) ≤
      ENNReal.ofReal (C * Real.exp (-t)) := by
    intro t ht
    by_cases h : t ≤ s₀
    · calc μ {x | V x ≤ -t} * ENNReal.ofReal (2 * Real.exp (2 * t))
          ≤ 1 * ENNReal.ofReal (2 * Real.exp (2 * t)) := mul_le_mul_left prob_le_one _
        _ ≤ ENNReal.ofReal (C * Real.exp (-t)) := by
          rw [one_mul]
          apply ENNReal.ofReal_le_ofReal
          rw [hC, mul_assoc, ← Real.exp_add]
          gcongr
          linarith
    · push Not at h
      calc μ {x | V x ≤ -t} * ENNReal.ofReal (2 * Real.exp (2 * t))
          ≤ ENNReal.ofReal (Real.exp (-(3 * t))) * ENNReal.ofReal (2 * Real.exp (2 * t)) :=
            mul_le_mul_left (htail t h) _
        _ = ENNReal.ofReal (2 * Real.exp (-t)) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 1
            rw [mul_left_comm, ← Real.exp_add]
            ring_nf
        _ ≤ ENNReal.ofReal (C * Real.exp (-t)) := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            rw [hC]
            have : 1 ≤ Real.exp (3 * s₀) := Real.one_le_exp (by linarith)
            linarith
  have hint : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp (-t)) =
      ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_neg_Ioi 0).const_mul C)
      (ae_of_all _ fun t => by positivity), integral_const_mul, integral_exp_neg_Ioi_zero,
      mul_one]
  calc 1 + ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | V x ≤ -t} * ENNReal.ofReal (2 * Real.exp (2 * t))
      ≤ 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp (-t)) := by
        gcongr ?_ + ?_
        · exact le_rfl
        · exact setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (nl_N a b M θ p) := by
        rw [hint, nl_N, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]

/-! ## 2. The box: heat split, Wick binomial split, smooth lower bound -/

variable {n k : ℕ}

/-- The quartic Wick potential V = ε² Σ_y :φ_y⁴:_{freeVar}. -/
def nl_V (n k : ℕ) (m₀ : ℝ) (φ : DField n k) : ℝ :=
  spacing n ^ 2 * ∑ y : DSite n k, wickPow (freeVar n m₀) 4 (φ y)

/-- The rough Wick constant c_r(T)(y) = C_r(T)(y, y) (the variance of φ_r(y)). -/
def nl_cr (n k : ℕ) (m₀ T : ℝ) (y : DSite n k) : ℝ := glp_roughCov n k m₀ T y y

/-- The smooth Wick constant c₁(T)(y) = freeVar − c_r(T)(y)
(= b(y) + C_s(T)(y, y), Wick defect plus smooth variance). -/
def nl_cs (n k : ℕ) (m₀ T : ℝ) (y : DSite n k) : ℝ := freeVar n m₀ - nl_cr n k m₀ T y

/-- The smooth part V_s = ε² Σ_y :φ_y⁴:_{c₁(y)}. -/
def nl_Vs (n k : ℕ) (m₀ T : ℝ) (φ : DField n k) : ℝ :=
  spacing n ^ 2 * ∑ y : DSite n k, wickPow (nl_cs n k m₀ T y) 4 (φ y)

/-- The remainder R = ε² Σ_y Σ_{j<4} C(4,j) :φs_y^j:_{c₁(y)} :φr_y^{4−j}:_{c_r(y)}. -/
def nl_R (n k : ℕ) (m₀ T : ℝ) (φs φr : DField n k) : ℝ :=
  spacing n ^ 2 * ∑ y : DSite n k, ∑ j ∈ range 4,
    ((Nat.choose 4 j : ℕ) : ℝ) * wickPow (nl_cs n k m₀ T y) j (φs y) *
      wickPow (nl_cr n k m₀ T y) (4 - j) (φr y)

/-- The deterministic smooth lower-bound constant D(T) = 6 ε² Σ_y c₁(T)(y)². -/
def nl_D (n k : ℕ) (m₀ T : ℝ) : ℝ := 6 * spacing n ^ 2 * ∑ y : DSite n k, nl_cs n k m₀ T y ^ 2

/-- The smooth field φ_s = A(α ξˢ), α_K = e^{−Tλ_K/2}. -/
def nl_φs (n k : ℕ) (m₀ T : ℝ) (ξ : DField n k) : DField n k :=
  md_map n k m₀ (fun K => Real.exp (-(T * dirEig n k m₀ K) / 2) * ξ K)

/-- The rough field φ_r = A(β ξʳ), β_K = √(1 − e^{−Tλ_K}). -/
def nl_φr (n k : ℕ) (m₀ T : ℝ) (ξ : DField n k) : DField n k :=
  md_map n k m₀ (fun K => √(1 - Real.exp (-(T * dirEig n k m₀ K))) * ξ K)

/-- γ^Λ. -/
def nl_gauss (n k : ℕ) : Measure (DField n k) := Measure.pi (fun _ : DSite n k => gaussianReal 0 1)

/-- γ^Λ ⊗ γ^Λ, the law of (ξˢ, ξʳ). -/
def nl_P (n k : ℕ) : Measure (DField n k × DField n k) := (nl_gauss n k).prod (nl_gauss n k)

instance (n k : ℕ) : IsProbabilityMeasure (nl_gauss n k) := by unfold nl_gauss; infer_instance
instance (n k : ℕ) : IsProbabilityMeasure (nl_P n k) := by unfold nl_P; infer_instance

/-- The remainder as a random variable of (ξˢ, ξʳ). -/
def nl_Rω (n k : ℕ) (m₀ T : ℝ) (p : DField n k × DField n k) : ℝ :=
  nl_R n k m₀ T (nl_φs n k m₀ T p.1) (nl_φr n k m₀ T p.2)

/-- The normalised free Dirichlet expectation E⁰[F]. -/
def nl_free (n k : ℕ) (m₀ : ℝ) (F : DField n k → ℝ) : ℝ :=
  (∫ φ, F φ * Real.exp (-(dirAction n k m₀ φ) / 2)) /
    (∫ φ, Real.exp (-(dirAction n k m₀ φ) / 2))

theorem nl_wickPow_continuous (c : ℝ) (j : ℕ) : Continuous (wickPow c j) := by
  unfold wickPow; fun_prop

theorem nl_V_continuous (m₀ : ℝ) : Continuous (nl_V n k m₀) := by
  unfold nl_V
  exact continuous_const.mul (continuous_finsetSum _ fun y _ =>
    (nl_wickPow_continuous _ 4).comp (continuous_apply y))

theorem nl_R_continuous (m₀ T : ℝ) :
    Continuous (fun q : DField n k × DField n k => nl_R n k m₀ T q.1 q.2) := by
  unfold nl_R
  refine continuous_const.mul (continuous_finsetSum _ fun y _ =>
    continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_const.mul ((nl_wickPow_continuous _ j).comp
    ((continuous_apply y).comp continuous_fst))).mul
    ((nl_wickPow_continuous _ _).comp ((continuous_apply y).comp continuous_snd))

theorem nl_φs_measurable (m₀ T : ℝ) : Measurable (nl_φs n k m₀ T) :=
  (md_map_measurable m₀).comp (by fun_prop)

theorem nl_φr_measurable (m₀ T : ℝ) : Measurable (nl_φr n k m₀ T) :=
  (md_map_measurable m₀).comp (by fun_prop)

theorem nl_Rω_measurable (m₀ T : ℝ) : Measurable (nl_Rω n k m₀ T) := by
  have h : Measurable (fun p : DField n k × DField n k =>
      (nl_φs n k m₀ T p.1, nl_φr n k m₀ T p.2)) :=
    ((nl_φs_measurable m₀ T).comp measurable_fst).prodMk
      ((nl_φr_measurable m₀ T).comp measurable_snd)
  have h2 := (nl_R_continuous (n := n) (k := k) m₀ T).measurable.comp h
  exact h2

theorem nl_Φ_measurable (m₀ T : ℝ) :
    Measurable (fun p : DField n k × DField n k => nl_φs n k m₀ T p.1 + nl_φr n k m₀ T p.2) :=
  ((nl_φs_measurable m₀ T).comp measurable_fst).add ((nl_φr_measurable m₀ T).comp measurable_snd)

/-- **Law of the split field:** φ_s + φ_r has the law A_* γ^Λ of the free field (T ≥ 0). -/
theorem nl_split_map (m₀ T : ℝ) (hT : 0 ≤ T) :
    (nl_P n k).map (fun p => nl_φs n k m₀ T p.1 + nl_φr n k m₀ T p.2) =
      (nl_gauss n k).map (md_map n k m₀) := by
  set α : DSite n k → ℝ := fun K => Real.exp (-(T * dirEig n k m₀ K) / 2) with hα
  have h0 : ∀ K, 0 ≤ α K := fun K => (Real.exp_pos _).le
  have h1 : ∀ K, α K ≤ 1 := fun K => Real.exp_le_one_iff.mpr (by
    have := mul_nonneg hT (dirEig_pos (n := n) (k := k) m₀ K).le
    linarith)
  have hsq : ∀ K, α K ^ 2 = Real.exp (-(T * dirEig n k m₀ K)) := by
    intro K
    rw [hα, sq, ← Real.exp_add]
    ring_nf
  have hfun : (fun p : DField n k × DField n k => nl_φs n k m₀ T p.1 + nl_φr n k m₀ T p.2) =
      md_map n k m₀ ∘
        (fun p : DField n k × DField n k => fun K => α K * p.1 K + √(1 - α K ^ 2) * p.2 K) := by
    funext p
    rw [Function.comp_apply, nl_φs, nl_φr, ← md_map_add]
    congr 1
    funext K
    rw [Pi.add_apply, hsq K]
  rw [hfun, ← Measure.map_map (md_map_measurable m₀) (by fun_prop), nl_P, nl_gauss,
    md_split_law α h0 h1]

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

/-- **The smooth-constant hypothesis holds for every m₀ ≠ 0 and k.** -/
theorem nl_smoothHyp {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ) : nl_SmoothHyp m₀ k := by
  set P : ℝ := (π / 4) ^ 2 with hP
  set m' : ℝ := (√|m₀|)⁻¹ with hm'
  set L := boxL k with hLdef
  have hP0 : 0 ≤ P := by positivity
  have hm'0 : 0 ≤ m' := by positivity
  have hm2 : 0 < m₀ ^ 2 := by positivity
  set A₀ : ℝ := P * (408 + 24 * ((m₀ ^ 2)⁻¹) ^ 2) with hA₀
  set A₁ : ℝ := P * 384 * m' with hA₁
  set A₂ : ℝ := 24 * P with hA₂
  refine ⟨A₀ * L ^ 2 + A₁ * (8 * (L * √L)), A₂ * L ^ 2, by positivity, fun n T hT hT1 => ?_⟩
  have hpt : ∀ y : DSite n k, 6 * nl_cs n k m₀ T y ^ 2 ≤
      A₀ + A₁ * nl_f n (fv2_bdist y) + A₂ * Real.log T ^ 2 := by
    intro y
    obtain ⟨h0, h1⟩ := nl_cs_bounds hm hT hT1 y
    set ℓ := Real.posLog (1 / (|m₀| * fv2_rdist n k y)) with hℓ
    have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
    have hx : √(1 / (|m₀| * fv2_rdist n k y)) = m' * nl_f n (fv2_bdist y) := by
      rw [fv2_rdist, nl_f, one_div, Real.sqrt_inv, Real.sqrt_mul (abs_nonneg _), mul_inv]
    have hℓ2 : ℓ ^ 2 ≤ 16 * (1 + m' * nl_f n (fv2_bdist y)) := by
      rw [← hx]
      exact nl_posLog_sq_le (by unfold fv2_rdist; have := spacing_pos n; positivity)
    set B := π / 4 * (1 + ℓ) with hB
    set E := π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) with hE
    have hlogT : Real.log T ≤ 0 := Real.log_nonpos hT.le hT1
    have hE0 : 0 ≤ E := mul_nonneg (by positivity) (by have := inv_pos.mpr hm2; linarith)
    have hB0 : 0 ≤ B := by positivity
    have hc2 : nl_cs n k m₀ T y ^ 2 ≤ 2 * B ^ 2 + 2 * E ^ 2 := by
      have : nl_cs n k m₀ T y ^ 2 ≤ (B + E) ^ 2 := pow_le_pow_left₀ h0 h1 2
      nlinarith [sq_nonneg (B - E)]
    have hB2 : B ^ 2 ≤ P * (34 + 32 * (m' * nl_f n (fv2_bdist y))) := by
      have h11 : (1 + ℓ) ^ 2 ≤ 2 * (1 + ℓ ^ 2) := by nlinarith [sq_nonneg (ℓ - 1)]
      calc B ^ 2 = P * (1 + ℓ) ^ 2 := by rw [hB, hP]; ring
        _ ≤ P * (2 * (1 + ℓ ^ 2)) := mul_le_mul_of_nonneg_left h11 hP0
        _ ≤ P * (34 + 32 * (m' * nl_f n (fv2_bdist y))) := by
            apply mul_le_mul_of_nonneg_left _ hP0; linarith
    have hE2 : E ^ 2 ≤ P * (2 * (((m₀ ^ 2)⁻¹) ^ 2 + Real.log T ^ 2)) := by
      calc E ^ 2 = P * (-Real.log T + (m₀ ^ 2)⁻¹) ^ 2 := by rw [hE, hP]; ring
        _ ≤ P * (2 * (((m₀ ^ 2)⁻¹) ^ 2 + Real.log T ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hP0
            nlinarith [sq_nonneg (Real.log T + (m₀ ^ 2)⁻¹)]
    rw [hA₀, hA₁, hA₂]
    nlinarith
  have hε := spacing_pos n
  have hL : spacing n * (boxN n k : ℝ) = L := nl_spacing_mul_boxN
  have hcard : spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ) = L ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, ← hL]; push_cast; ring
  have hfs := nl_sum_f_bdist (n := n) (k := k)
  unfold nl_D
  calc 6 * spacing n ^ 2 * ∑ y : DSite n k, nl_cs n k m₀ T y ^ 2
      = spacing n ^ 2 * ∑ y : DSite n k, 6 * nl_cs n k m₀ T y ^ 2 := by
        rw [← mul_sum]; ring
    _ ≤ spacing n ^ 2 * ∑ y : DSite n k,
          (A₀ + A₁ * nl_f n (fv2_bdist y) + A₂ * Real.log T ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => hpt y) (by positivity)
    _ = A₀ * (spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ)) +
          A₁ * (spacing n ^ 2 * ∑ y : DSite n k, nl_f n (fv2_bdist y)) +
          A₂ * (spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ)) * Real.log T ^ 2 := by
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
        ring
    _ ≤ A₀ * L ^ 2 + A₁ * (8 * (L * √L)) + A₂ * L ^ 2 * Real.log T ^ 2 := by
        rw [hcard]
        have : A₁ * (spacing n ^ 2 * ∑ y : DSite n k, nl_f n (fv2_bdist y)) ≤
            A₁ * (8 * (L * √L)) := mul_le_mul_of_nonneg_left hfs (by positivity)
        linarith
    _ = A₀ * L ^ 2 + A₁ * (8 * (L * √L)) + A₂ * L ^ 2 * Real.log T ^ 2 := rfl

/-- **Reduction to the two Gaussian-chaos hypotheses** (smooth part discharged):
for m₀ ≠ 0, rough L² + chaos ⇒ Nelson's bound for the box. -/
theorem nl_nelsonBox_of_rough {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ)
    (hL2 : nl_RoughL2Hyp m₀ k) (hC : nl_ChaosHyp m₀ k) : nl_NelsonBox m₀ k :=
  nl_nelsonBox_of_hyps m₀ k (nl_smoothHyp hm k) hL2 hC

/-! ## 5. Step 4 interface: Fin-reindexing of (ξˢ, ξʳ) and the chaos bound from a Hermite
representation -/

/-- The number of standard Gaussians (ξˢ, ξʳ): |Λ ⊕ Λ| = 2|Λ|. -/
abbrev nl_d (n k : ℕ) : ℕ := Fintype.card (DSite n k ⊕ DSite n k)

/-- The reindexing ℝ^{Fin (2|Λ|)} ≃ᵐ ℝ^Λ × ℝ^Λ (`Fintype.equivFin` + `sumPiEquivProdPi`). -/
def nl_e (n k : ℕ) : (Fin (nl_d n k) → ℝ) ≃ᵐ DField n k × DField n k :=
  (MeasurableEquiv.piCongrLeft (fun _ : DSite n k ⊕ DSite n k => ℝ)
    (Fintype.equivFin (DSite n k ⊕ DSite n k)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : DSite n k ⊕ DSite n k => ℝ))

/-- nl_e maps γ^{Fin (2|Λ|)} to γ^Λ ⊗ γ^Λ. -/
theorem nl_e_mp : MeasurePreserving (nl_e n k) (PP2Chaos2.ch2_gauss (nl_d n k)) (nl_P n k) := by
  have h1 := measurePreserving_piCongrLeft (fun _ : DSite n k ⊕ DSite n k => gaussianReal 0 1)
    (Fintype.equivFin (DSite n k ⊕ DSite n k)).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : DSite n k ⊕ DSite n k => gaussianReal 0 1)
  unfold PP2Chaos2.ch2_gauss nl_P nl_gauss
  exact h2.comp h1

/-- **Chaos hypothesis from a Hermite representation.** If, for every n and T ∈ (0, 1], the
remainder R_T ∘ nl_e is a Hermite polynomial F_c (per-variable degree ≤ 4, `PP2Chaos2.ch2_F`)
with c supported on total degree |α| ≤ 4, then `nl_ChaosHyp` holds (via `ch2_hyper_lintegral`
with ρ_m, as in `ch2_degree_bound`). -/
theorem nl_chaosHyp_of_repr (m₀ : ℝ) (k : ℕ)
    (hrep : ∀ n : ℕ, ∀ T : ℝ, 0 < T → T ≤ 1 → ∃ c : (Fin (nl_d n k) → Fin 5) → ℝ,
      (∀ α, 4 < PP2Chaos2.ch2_deg α → c α = 0) ∧
      ∀ x, nl_Rω n k m₀ T (nl_e n k x) = PP2Chaos2.ch2_F (nl_d n k) 1 c x) :
    nl_ChaosHyp m₀ k := by
  open PP2Chaos2 in
  intro n T hT hT1 m
  obtain ⟨c, hc, hF⟩ := hrep n T hT hT1
  have hmp := nl_e_mp (n := n) (k := k)
  have hL : ∫⁻ p, ENNReal.ofReal (nl_Rω n k m₀ T p ^ (2 * m + 2)) ∂nl_P n k =
      ∫⁻ x, ENNReal.ofReal (ch2_F (nl_d n k) 1 c x ^ (2 * m + 2)) ∂ch2_gauss (nl_d n k) := by
    rw [← hmp.lintegral_comp_emb (nl_e n k).measurableEmbedding]
    simp_rw [hF]
  have hB : ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k =
      ∫ x, ch2_F (nl_d n k) 1 c x ^ 2 ∂ch2_gauss (nl_d n k) := by
    rw [← hmp.integral_comp' (fun p => nl_Rω n k m₀ T p ^ 2)]
    simp_rw [hF]
  rw [hL, hB, ch2_L2]
  set ρ := ch2_rho m with hρ
  have hρ0 : 0 < ρ := ch2_rho_pos m
  have hρi : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ0 |>.mpr (ch2_rho_le_one m)
  set c' : (Fin (nl_d n k) → Fin 5) → ℝ := fun α => ρ⁻¹ ^ ch2_deg α * c α with hc'
  have hF' : ∀ x, ch2_F (nl_d n k) ρ c' x = ch2_F (nl_d n k) 1 c x := by
    intro x
    unfold ch2_F
    refine sum_congr rfl fun α _ => ?_
    rw [hc', one_pow, one_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ0.ne', one_pow, one_mul]
  have hN : ch2_norm (nl_d n k) c' ≤ ρ⁻¹ ^ (2 * 4) * ch2_norm (nl_d n k) c := by
    unfold ch2_norm
    rw [mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    rw [hc']
    dsimp only
    by_cases h : 4 < ch2_deg α
    · rw [hc α h]; simp
    · push Not at h
      have hp : ρ⁻¹ ^ (2 * ch2_deg α) ≤ ρ⁻¹ ^ (2 * 4) := pow_le_pow_right₀ hρi (by omega)
      have hf := (ch2_fact_pos α).le
      calc ch2_fact α * (ρ⁻¹ ^ ch2_deg α * c α) ^ 2
          = ρ⁻¹ ^ (2 * ch2_deg α) * (ch2_fact α * c α ^ 2) := by rw [pow_mul]; ring
        _ ≤ ρ⁻¹ ^ (2 * 4) * (ch2_fact α * c α ^ 2) :=
          mul_le_mul_of_nonneg_right hp (mul_nonneg hf (sq_nonneg _))
  have h := ch2_hyper_lintegral m ρ hρ0.le (ch2_rho_le_one m)
    (ch2_admissible m ρ (ch2_rho_sq m)) (nl_d n k) c'
  simp_rw [hF'] at h
  refine h.trans ?_
  rw [← ENNReal.ofReal_pow (ch2_norm_nonneg _ c')]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (ch2_norm_nonneg _ c') hN _)

/-- **Final reduction (m₀ ≠ 0):** rough L² bound + Hermite representation of R_T ⇒ Nelson. -/
theorem nl_nelsonBox_of_rough_repr {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ)
    (hL2 : nl_RoughL2Hyp m₀ k)
    (hrep : ∀ n : ℕ, ∀ T : ℝ, 0 < T → T ≤ 1 → ∃ c : (Fin (nl_d n k) → Fin 5) → ℝ,
      (∀ α, 4 < PP2Chaos2.ch2_deg α → c α = 0) ∧
      ∀ x, nl_Rω n k m₀ T (nl_e n k x) = PP2Chaos2.ch2_F (nl_d n k) 1 c x) :
    nl_NelsonBox m₀ k :=
  nl_nelsonBox_of_rough hm k hL2 (nl_chaosHyp_of_repr m₀ k hrep)

/-! ## 6. Hermite representation of polynomials of total degree ≤ 4 -/

/-- Monomial-to-Hermite coefficients: t^j = Σ_q a(j, q) He_q(t), j ≤ 4. -/
def nl_a : ℕ → Fin 5 → ℝ
  | 0 => ![1, 0, 0, 0, 0]
  | 1 => ![0, 1, 0, 0, 0]
  | 2 => ![1, 0, 1, 0, 0]
  | 3 => ![0, 3, 0, 1, 0]
  | 4 => ![3, 0, 6, 0, 1]
  | _ => fun _ => 0

theorem nl_pow_herm {j : ℕ} (hj : j ≤ 4) (t : ℝ) :
    t ^ j = ∑ q : Fin 5, nl_a j q * PP2Chaos.He q t := by
  interval_cases j
  all_goals simp [Fin.sum_univ_five, nl_a, PP2Chaos.He, wickPow_zero', wickPow_one, wickPow_two,
      wickPow_three, wickPow_four']
  ring

theorem nl_a_supp (j : ℕ) (q : Fin 5) (h : nl_a j q ≠ 0) : (q : ℕ) ≤ j := by
  rcases Nat.lt_or_ge 4 j with hj | hj
  · have := q.isLt; omega
  · interval_cases j <;> fin_cases q <;> simp_all [nl_a]

/-- A monomial Π_i x_i^{β_i} (β_i ≤ 4) is the Hermite polynomial F_c with
c_α = Π_i a(β_i, α_i). -/
theorem nl_monomial_herm {d : ℕ} (β : Fin d → ℕ) (hβ : ∀ i, β i ≤ 4) (x : Fin d → ℝ) :
    ∏ i, x i ^ β i = PP2Chaos2.ch2_F d 1 (fun α => ∏ i, nl_a (β i) (α i)) x := by
  have h1 : ∀ i, x i ^ β i = ∑ q : Fin 5, nl_a (β i) q * PP2Chaos.He q (x i) :=
    fun i => nl_pow_herm (hβ i) (x i)
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum, Fintype.piFinset_univ]
  unfold PP2Chaos2.ch2_F
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [one_pow, one_mul, Finset.prod_mul_distrib]

/-- **Every polynomial of total degree ≤ 4 in d variables is a Hermite polynomial F_c with c
supported on |α| ≤ 4** (the representation needed by `ch2_degree_bound` / `nl_chaosHyp_of_repr`). -/
theorem nl_mvpoly_herm {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ 4) :
    ∃ c : (Fin d → Fin 5) → ℝ, (∀ α, 4 < PP2Chaos2.ch2_deg α → c α = 0) ∧
      ∀ x, MvPolynomial.eval x P = PP2Chaos2.ch2_F d 1 c x := by
  have hdeg : ∀ β ∈ P.support, ∑ i, β i ≤ 4 := by
    intro β hβ
    have := (MvPolynomial.le_totalDegree hβ).trans hP
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
  have hβ4 : ∀ β ∈ P.support, ∀ i, β i ≤ 4 := fun β hβ i =>
    (Finset.single_le_sum (f := fun i => β i) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
      (hdeg β hβ)
  refine ⟨fun α => ∑ β ∈ P.support, P.coeff β * ∏ i, nl_a (β i) (α i), ?_, ?_⟩
  · intro α hα
    refine Finset.sum_eq_zero fun β hβ => ?_
    by_contra hne
    have hprod : ∏ i, nl_a (β i) (α i) ≠ 0 := right_ne_zero_of_mul hne
    rw [Finset.prod_ne_zero_iff] at hprod
    have : PP2Chaos2.ch2_deg α ≤ ∑ i, β i :=
      Finset.sum_le_sum fun i _ => nl_a_supp _ _ (hprod i (mem_univ _))
    have := hdeg β hβ
    omega
  · intro x
    rw [MvPolynomial.eval_eq',
      Finset.sum_congr rfl fun β hβ => by rw [nl_monomial_herm β (hβ4 β hβ) x]]
    unfold PP2Chaos2.ch2_F
    simp only [one_pow, one_mul, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun α _ => sum_congr rfl fun β _ => ?_
    ring

/-- **Final reduction, polynomial form (m₀ ≠ 0):** rough L² bound + "R_T ∘ nl_e is a polynomial
of total degree ≤ 4" ⇒ Nelson's bound for the box. -/
theorem nl_nelsonBox_of_rough_poly {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ)
    (hL2 : nl_RoughL2Hyp m₀ k)
    (hpoly : ∀ n : ℕ, ∀ T : ℝ, 0 < T → T ≤ 1 → ∃ P : MvPolynomial (Fin (nl_d n k)) ℝ,
      P.totalDegree ≤ 4 ∧ ∀ x, nl_Rω n k m₀ T (nl_e n k x) = MvPolynomial.eval x P) :
    nl_NelsonBox m₀ k := by
  refine nl_nelsonBox_of_rough_repr hm k hL2 fun n T hT hT1 => ?_
  obtain ⟨P, hP, hRP⟩ := hpoly n T hT hT1
  obtain ⟨c, hc, hPc⟩ := nl_mvpoly_herm P hP
  exact ⟨c, hc, fun x => (hRP x).trans (hPc x)⟩

/-! ## 7. R_T ∘ nl_e is a polynomial of total degree ≤ 4 (discharging step 4) -/

/-- The index of ξˢ_K (`Sum.inl K`) and ξʳ_K (`Sum.inr K`) among the 2|Λ| Gaussians. -/
def nl_σ (n k : ℕ) (b : DSite n k ⊕ DSite n k) : Fin (nl_d n k) :=
  Fintype.equivFin (DSite n k ⊕ DSite n k) b

theorem nl_e_fst (x : Fin (nl_d n k) → ℝ) (K : DSite n k) :
    (nl_e n k x).1 K = x (nl_σ n k (Sum.inl K)) := by
  simp [nl_e, nl_σ, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast]

theorem nl_e_snd (x : Fin (nl_d n k) → ℝ) (K : DSite n k) :
    (nl_e n k x).2 K = x (nl_σ n k (Sum.inr K)) := by
  simp [nl_e, nl_σ, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast]

/-- The linear polynomial Σ_K C(a_K) X_{σ(b K)}. -/
def nl_linMv {d : ℕ} {ι : Type*} [Fintype ι] (a : ι → ℝ) (σ : ι → Fin d) :
    MvPolynomial (Fin d) ℝ :=
  ∑ K, MvPolynomial.C (a K) * MvPolynomial.X (σ K)

theorem nl_linMv_eval {d : ℕ} {ι : Type*} [Fintype ι] (a : ι → ℝ) (σ : ι → Fin d)
    (x : Fin d → ℝ) : MvPolynomial.eval x (nl_linMv a σ) = ∑ K, a K * x (σ K) := by
  simp [nl_linMv]

theorem nl_linMv_deg {d : ℕ} {ι : Type*} [Fintype ι] (a : ι → ℝ) (σ : ι → Fin d) :
    (nl_linMv a σ).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun K _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- The Wick power :Q^j:_c of a polynomial Q, as a polynomial. -/
def nl_wickMv {d : ℕ} (c : ℝ) (j : ℕ) (Q : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ i ∈ range (j / 2 + 1), MvPolynomial.C ((-1 : ℝ) ^ i * (j.factorial : ℝ) /
    ((i.factorial : ℝ) * ((j - 2 * i).factorial : ℝ) * 2 ^ i) * c ^ i) * Q ^ (j - 2 * i)

theorem nl_wickMv_eval {d : ℕ} (c : ℝ) (j : ℕ) (Q : MvPolynomial (Fin d) ℝ) (x : Fin d → ℝ) :
    MvPolynomial.eval x (nl_wickMv c j Q) = wickPow c j (MvPolynomial.eval x Q) := by
  simp [nl_wickMv, wickPow]

theorem nl_wickMv_deg {d : ℕ} (c : ℝ) (j : ℕ) {Q : MvPolynomial (Fin d) ℝ}
    (hQ : Q.totalDegree ≤ 1) : (nl_wickMv c j Q).totalDegree ≤ j := by
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc (j - 2 * i) * Q.totalDegree ≤ (j - 2 * i) * 1 := Nat.mul_le_mul_left _ hQ
    _ ≤ j := by omega

/-- Coefficients of φ_s(y) and φ_r(y) as linear forms in ξˢ, ξʳ. -/
def nl_ls (n k : ℕ) (m₀ T : ℝ) (y K : DSite n k) : ℝ :=
  (spacing n)⁻¹ * ((√(dirEig n k m₀ K))⁻¹ * Real.exp (-(T * dirEig n k m₀ K) / 2) * sineVec2 K y)

def nl_lr (n k : ℕ) (m₀ T : ℝ) (y K : DSite n k) : ℝ :=
  (spacing n)⁻¹ *
    ((√(dirEig n k m₀ K))⁻¹ * √(1 - Real.exp (-(T * dirEig n k m₀ K))) * sineVec2 K y)

theorem nl_φs_e (m₀ T : ℝ) (x : Fin (nl_d n k) → ℝ) (y : DSite n k) :
    nl_φs n k m₀ T (nl_e n k x).1 y =
      MvPolynomial.eval x (nl_linMv (nl_ls n k m₀ T y) (fun K => nl_σ n k (Sum.inl K))) := by
  rw [nl_linMv_eval, nl_φs, md_map_apply, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  rw [nl_e_fst, nl_ls]
  ring

theorem nl_φr_e (m₀ T : ℝ) (x : Fin (nl_d n k) → ℝ) (y : DSite n k) :
    nl_φr n k m₀ T (nl_e n k x).2 y =
      MvPolynomial.eval x (nl_linMv (nl_lr n k m₀ T y) (fun K => nl_σ n k (Sum.inr K))) := by
  rw [nl_linMv_eval, nl_φr, md_map_apply, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  rw [nl_e_snd, nl_lr]
  ring

/-- The remainder R_T as a polynomial in the 2|Λ| Gaussians. -/
def nl_RMv (n k : ℕ) (m₀ T : ℝ) : MvPolynomial (Fin (nl_d n k)) ℝ :=
  MvPolynomial.C (spacing n ^ 2) * ∑ y : DSite n k, ∑ j ∈ range 4,
    MvPolynomial.C (((Nat.choose 4 j : ℕ) : ℝ)) *
      nl_wickMv (nl_cs n k m₀ T y) j
        (nl_linMv (nl_ls n k m₀ T y) (fun K => nl_σ n k (Sum.inl K))) *
      nl_wickMv (nl_cr n k m₀ T y) (4 - j)
        (nl_linMv (nl_lr n k m₀ T y) (fun K => nl_σ n k (Sum.inr K)))

theorem nl_RMv_eval (m₀ T : ℝ) (x : Fin (nl_d n k) → ℝ) :
    nl_Rω n k m₀ T (nl_e n k x) = MvPolynomial.eval x (nl_RMv n k m₀ T) := by
  simp only [nl_Rω, nl_R, nl_RMv, map_mul, map_sum, MvPolynomial.eval_C, nl_wickMv_eval,
    nl_φs_e, nl_φr_e]

theorem nl_RMv_deg (m₀ T : ℝ) : (nl_RMv n k m₀ T).totalDegree ≤ 4 := by
  unfold nl_RMv
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine MvPolynomial.totalDegree_finsetSum_le fun y _ => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun j hj => ?_
  have hj4 : j < 4 := mem_range.mp hj
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  refine (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  have h1 := nl_wickMv_deg (nl_cs n k m₀ T y) j (nl_linMv_deg (nl_ls n k m₀ T y)
    (fun K => nl_σ n k (Sum.inl K)))
  have h2 := nl_wickMv_deg (nl_cr n k m₀ T y) (4 - j) (nl_linMv_deg (nl_lr n k m₀ T y)
    (fun K => nl_σ n k (Sum.inr K)))
  omega

/-- **The chaos hypothesis holds** (for every m₀ and k): R_T is a polynomial of total degree ≤ 4
in the 2|Λ| standard Gaussians, so `ch2_hyper_lintegral` applies. -/
theorem nl_chaosHyp (m₀ : ℝ) (k : ℕ) : nl_ChaosHyp m₀ k := by
  refine nl_chaosHyp_of_repr m₀ k fun n T _ _ => ?_
  obtain ⟨c, hc, hPc⟩ := nl_mvpoly_herm (nl_RMv n k m₀ T) (nl_RMv_deg m₀ T)
  exact ⟨c, hc, fun x => (nl_RMv_eval m₀ T x).trans (hPc x)⟩

/-- **Main reduction (G4, box): for m₀ ≠ 0, the rough L² bound alone implies Nelson's bound.** -/
theorem nl_nelsonBox_of_roughL2 {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ) (hL2 : nl_RoughL2Hyp m₀ k) :
    nl_NelsonBox m₀ k :=
  nl_nelsonBox_of_rough hm k hL2 (nl_chaosHyp m₀ k)

end PP2Nelson

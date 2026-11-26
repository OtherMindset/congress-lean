import LongTable.R_PP2Modes
import LongTable.R_PP2GreenLpB
import LongTable.R_PP2FreeVar2B
import LongTable.R_PP2Chaos2B
import LongTable.R_PP2PortNelson1

/-!
Part A of PP2Nelson (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Nelson.lean)
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

end PP2Nelson

end

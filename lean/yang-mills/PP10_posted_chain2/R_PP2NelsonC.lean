import LongTable.R_PP2NelsonB

/-!
Part C of PP2Nelson (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Nelson.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
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

variable {n k : ℕ}

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

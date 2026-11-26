import LongTable.R_PP2NelsonC
import LongTable.R_PP2ModesGenC

/-!
Part A of PP2NelsonRegion (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2NelsonRegion.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node G4 of the M5
plan (Nelson's bound), session 2, REGION version (namespace `PP2NelsonRegion`; box version and
the abstract argument in PP2Nelson, generic modes/heat kernels in PP2ModesGen).

Target (`nl_NelsonRegion m₀ l`): ∃ N, ∀ n k x, ∀ λ ∈ [0, 1], with B = physBall n k x l,
  ∫⁻ e^{−2λV_B} dμ⁰_B ≤ N  and  (∫ e^{−2λV_B} w_B dψ)/(∫ w_B dψ) ≤ N,
where w_B(ψ) = qweight n k m₀ 0 (zeroExt B ψ) on ℝ^B, μ⁰_B = (∫ w_B)⁻¹ · Leb.withDensity w_B
(`nr_freeMeasure`), V_B(ψ) = ε² Σ_{y∈B} :ψ_y⁴:_{freeVar} (`nr_V`). N depends on m₀, l only.

Notation: A = rg_scaledOp B = ε² regionOp B (PosDef for m₀ ≠ 0), M = mg_modeMat, λ_K its
eigenvalues; physical cutoff T ∈ (0, 1], lattice time τ = ε⁻² T (`nr_τ`); φ_s = M(e^{−τλ/2} ξˢ),
φ_r = M(√(1 − e^{−τλ}) ξʳ) (`nr_φs`, `nr_φr`), (ξˢ, ξʳ) ~ γ^B ⊗ γ^B (`nr_P`);
c_r(y) = C^B_r(T)(y, y) = `mg_regionRough` (`nr_cr`), c₁ = freeVar − c_r (`nr_cs`),
R_T (`nr_R`, `nr_Rω`), D_B(T) = 6ε² Σ_{y∈B} c₁² (`nr_D`), R = ⌊l/ε⌋ (`nr_rad`).

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* §1 Generic (any finite ι, A PosDef, weight w ≥ 0, any Wick constants cs + cr = c):
  `nr_Vg_split` (Wick binomial split), `nr_Vsg_ge` (V_s ≥ −D), `nr_split_map` (φ_s + φ_r has law
  M_* γ^ι, via `mg_split_law`), measurability lemmas; chaos: `nr_e` / `nr_e_mp`
  (ℝ^{Fin 2|ι|} ≃ᵐ ℝ^ι × ℝ^ι measure preserving), `nr_chaos_of_poly` (degree-≤ 4 polynomial ⇒
  E[F^{2m+2}] ≤ (ρ_m^{−8} E F²)^{m+1}, via `nl_mvpoly_herm`, `ch2_hyper_lintegral`), `nr_RMv`,
  `nr_RMv_eval`, `nr_RMv_deg`, **`nr_chaos`** (the chaos bound for R(φ_s, φ_r), any A, τ, w, cs,
  cr); **`nr_generic`**: smooth bound D(u) ≤ a + b u² and E[R_u²] ≤ K e^{−θu} for a cutoff
  schedule τ(u) ≥ 0 ⇒ ∫ e^{−2λV} d(M_* γ^ι) ≤ 1 + nl_N a b (230⁸ max(K,0)) θ 24 (via `nl_abstract`).
* §2 Regions: `nl_NelsonRegion`, `nr_SmoothHyp`, `nr_RoughL2Hyp`, `nr_ChaosHyp`;
  **`nr_chaosHyp`** (discharged, every m₀ ≠ 0, l); `nr_freeMeasure_eq` (μ⁰_B = M_* γ^B, from
  `mg_gauss_modes_measure`); **`nr_nelsonRegion_of_hyps`**: m₀ ≠ 0 → SmoothHyp → RoughL2Hyp →
  nl_NelsonRegion (schedule T = e^{−u}, τ = ε⁻² e^{−u}; ratio form via `mg_region_gauss_modes`).
* §3 Region Wick defect b_B(y) = freeVar − ε⁻² regionGreen B y y:
  `nr_region_two_mul_sub_quad_le` (2w(a) − ⟨w, regionOp w⟩ ≤ regionGreen a a),
  `nr_specVar_le_regionVar` (the sub-box trial field of `fv2_specVar_le_dirVar`, supported in
  subBox M y ⊆ B), **`nr_region_defect_le`**: Fits M y ∧ subBox M y ⊆ B ⇒
  b_B(y) ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))); `nr_region_defect_nonneg` (b_B ≥ b ≥ 0, domain
  monotonicity); `nr_cs_eq` (c₁ = b_B + ε⁻² ∫_{(T,∞)} p^B_t(y,y) dt), `nr_tail_int_nonneg`,
  `nr_tail_int_le` (≤ (π/4)(log(1/T) + m₀⁻²), from `mg_regionHeat_diag_le`), `nr_cs_bounds`.
* §4 Geometry of B = physBall x l (l ≥ 0): `nr_mem_physBall_iff` (B = lattice rectangle
  |u_i − x_i| ≤ R), `nr_physBall_eq` (B = s₁ ×ˢ s₂, `nr_s1`), the region distance
  M_B(y) = min_i min(y_i − (x_i − R), min(N − 1, x_i + R) − y_i) (`nr_d1`, `nr_M`), `nr_fits`,
  `nr_subBox_sub` (subBox M_B(y) y fits the box and lies in B), `nr_sum_anti`,
  `nr_sum_anti_inj`, `nr_sum1`, `nr_s1_card` (|s_i| ≤ 2R + 1), `nr_eps_Q_le` (ε(2R+1) ≤ 2l + 1),
  `nr_card_le` (ε²|B| ≤ (2l+1)²), **`nr_sum_f_M`**: ε² Σ_{y∈B} (ε(M_B(y)+1))^{−1/2}
  ≤ 8 (2l+1)^{3/2} uniformly in n, k, x (the log divergence of b_B at ∂B is square-summable).
* §5 **`nr_smoothHyp`**: m₀ ≠ 0 → 0 ≤ l → nr_SmoothHyp m₀ l (a = A₀L² + 8A₁L^{3/2}, b = A₂L²,
  L = 2l + 1, A_i as in `nl_smoothHyp`); **`nl_nelsonRegion_of_roughL2`**: m₀ ≠ 0 → 0 ≤ l →
  nr_RoughL2Hyp m₀ l hm → nl_NelsonRegion m₀ l.

NOT formalized (what remains): step 3 for regions, `nr_RoughL2Hyp m₀ l hm`:
  ∃ K θ, 0 < θ ∧ ∀ n k x, ∀ T ∈ (0, 1], E_{γ^B⊗γ^B}[R_T²] ≤ K T^θ  (B = physBall n k x l).
  Same ingredients as the box (PP2Nelson header): factorisation of E over the product; Wick
  covariance of φ_r at its true variances, E[:φ_r(y)^a: :φ_r(y')^b:] = δ_ab a! C^B_r(y,y')^a, with
  E[φ_r(y) φ_r(y')] = (M diag(1 − e^{−τλ}) Mᵀ)(y,y') = C^B_r(T)(y,y') (`mg_region_rough_cov`;
  the Gaussian second moments themselves are not stated); misordered smooth covariances bounded by
  K(1 + c₁(y))^j(1 + c₁(y'))^j; summation with `mg_regionRough_Lp_le` (ε² Σ_{y'∈B} |C^B_r|^m
  ≤ K_m T) and ε² Σ_{y∈B} (1 + c₁(y))^6 ≤ K(1 + |log T|)^6 (from `nr_cs_bounds`, `nr_sum_f_M`-type
  sums). The case l < 0 (B = ∅, trivial) is excluded from `nr_smoothHyp` for convenience.
  Optimal constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Real Finset Matrix
open scoped ENNReal

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

noncomputable section

namespace PP2NelsonRegion

open PP2Target PP2Nelson

/-! ## 1. Generic Gaussian setting: a positive definite precision matrix A on a finite ι -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- α_K = e^{−τλ_K/2}. -/
def nr_α (hA : A.PosDef) (τ : ℝ) (K : ι) : ℝ := Real.exp (-(τ * hA.1.eigenvalues K) / 2)

/-- β_K = √(1 − e^{−τλ_K}). -/
def nr_β (hA : A.PosDef) (τ : ℝ) (K : ι) : ℝ := √(1 - Real.exp (-(τ * hA.1.eigenvalues K)))

/-- The smooth field φ_s = M(α ξˢ). -/
def nr_φs (hA : A.PosDef) (τ : ℝ) (ξ : ι → ℝ) : ι → ℝ := mg_modeMat hA *ᵥ fun K => nr_α hA τ K * ξ K

/-- The rough field φ_r = M(β ξʳ). -/
def nr_φr (hA : A.PosDef) (τ : ℝ) (ξ : ι → ℝ) : ι → ℝ := mg_modeMat hA *ᵥ fun K => nr_β hA τ K * ξ K

variable (ι) in
/-- γ^ι. -/
def nr_gauss : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 1)

variable (ι) in
/-- γ^ι ⊗ γ^ι. -/
def nr_P : Measure ((ι → ℝ) × (ι → ℝ)) := (nr_gauss ι).prod (nr_gauss ι)

instance : IsProbabilityMeasure (nr_gauss ι) := by unfold nr_gauss; infer_instance
instance : IsProbabilityMeasure (nr_P ι) := by unfold nr_P; infer_instance

/-- V = w Σ_y :ψ_y⁴:_c. -/
def nr_Vg (w c : ℝ) (ψ : ι → ℝ) : ℝ := w * ∑ y, wickPow c 4 (ψ y)

/-- V_s = w Σ_y :ψ_y⁴:_{cs(y)}. -/
def nr_Vsg (w : ℝ) (cs : ι → ℝ) (ψ : ι → ℝ) : ℝ := w * ∑ y, wickPow (cs y) 4 (ψ y)

/-- R = w Σ_y Σ_{j<4} C(4,j) :φs_y^j:_{cs(y)} :φr_y^{4−j}:_{cr(y)}. -/
def nr_Rg (w : ℝ) (cs cr : ι → ℝ) (φs φr : ι → ℝ) : ℝ :=
  w * ∑ y, ∑ j ∈ range 4,
    ((Nat.choose 4 j : ℕ) : ℝ) * wickPow (cs y) j (φs y) * wickPow (cr y) (4 - j) (φr y)

/-- D = 6 w Σ_y cs(y)². -/
def nr_Dg (w : ℝ) (cs : ι → ℝ) : ℝ := 6 * w * ∑ y, cs y ^ 2

theorem nr_Vg_continuous (w c : ℝ) : Continuous (nr_Vg (ι := ι) w c) := by
  unfold nr_Vg
  exact continuous_const.mul (continuous_finsetSum _ fun y _ =>
    (nl_wickPow_continuous _ 4).comp (continuous_apply y))

theorem nr_Rg_continuous (w : ℝ) (cs cr : ι → ℝ) :
    Continuous (fun q : (ι → ℝ) × (ι → ℝ) => nr_Rg w cs cr q.1 q.2) := by
  unfold nr_Rg
  refine continuous_const.mul (continuous_finsetSum _ fun y _ =>
    continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_const.mul ((nl_wickPow_continuous _ j).comp
    ((continuous_apply y).comp continuous_fst))).mul
    ((nl_wickPow_continuous _ _).comp ((continuous_apply y).comp continuous_snd))

theorem nr_Vg_measurable (w c : ℝ) : Measurable (nr_Vg (ι := ι) w c) := by
  unfold nr_Vg
  exact measurable_const.mul (Finset.measurable_sum _ fun y _ =>
    (nl_wickPow_continuous _ 4).measurable.comp (measurable_pi_apply y))

theorem nr_Rg_measurable (w : ℝ) (cs cr : ι → ℝ) :
    Measurable (fun q : (ι → ℝ) × (ι → ℝ) => nr_Rg w cs cr q.1 q.2) := by
  unfold nr_Rg
  refine measurable_const.mul (Finset.measurable_sum _ fun y _ =>
    Finset.measurable_sum _ fun j _ => ?_)
  exact (measurable_const.mul ((nl_wickPow_continuous _ j).measurable.comp
    ((measurable_pi_apply y).comp measurable_fst))).mul
    ((nl_wickPow_continuous _ _).measurable.comp ((measurable_pi_apply y).comp measurable_snd))

/-- Wick binomial split, generic: if cs + cr = c then V(φs + φr) = V_s(φs) + R(φs, φr). -/
theorem nr_Vg_split (w c : ℝ) (cs cr : ι → ℝ) (hc : ∀ y, cs y + cr y = c) (φs φr : ι → ℝ) :
    nr_Vg w c (φs + φr) = nr_Vsg w cs φs + nr_Rg w cs cr φs φr := by
  unfold nr_Vg nr_Vsg nr_Rg
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Pi.add_apply, ← hc y, wickPow_add_binomial, Finset.sum_range_succ, Nat.choose_self,
    Nat.sub_self, wickPow_zero']
  push_cast
  ring

theorem nr_Vsg_ge {w : ℝ} (hw : 0 ≤ w) (cs : ι → ℝ) (φ : ι → ℝ) :
    -nr_Dg w cs ≤ nr_Vsg w cs φ := by
  unfold nr_Dg nr_Vsg
  have e : -(6 * w * ∑ y, cs y ^ 2) = w * ∑ y, -(6 * cs y ^ 2) := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => nl_wick4_ge _ _) hw

theorem nr_modeMat_measurable (hA : A.PosDef) : Measurable (fun ξ : ι → ℝ => mg_modeMat hA *ᵥ ξ) :=
  mg_map_measurable hA

theorem nr_φs_measurable (hA : A.PosDef) (τ : ℝ) : Measurable (nr_φs hA τ) :=
  (mg_map_measurable hA).comp (by fun_prop)

theorem nr_φr_measurable (hA : A.PosDef) (τ : ℝ) : Measurable (nr_φr hA τ) :=
  (mg_map_measurable hA).comp (by fun_prop)

theorem nr_Φ_measurable (hA : A.PosDef) (τ : ℝ) :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) => nr_φs hA τ p.1 + nr_φr hA τ p.2) :=
  ((nr_φs_measurable hA τ).comp measurable_fst).add ((nr_φr_measurable hA τ).comp measurable_snd)

theorem nr_Rg_measurable' {Ω : Type*} [MeasurableSpace Ω] (w : ℝ) (cs cr : ι → ℝ)
    {f g : Ω → ι → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => nr_Rg w cs cr (f p) (g p)) := by
  unfold nr_Rg
  refine measurable_const.mul (Finset.measurable_sum _ fun y _ =>
    Finset.measurable_sum _ fun j _ => ?_)
  exact (measurable_const.mul ((nl_wickPow_continuous _ j).measurable.comp
    (measurable_pi_iff.mp hf y))).mul
    ((nl_wickPow_continuous _ _).measurable.comp (measurable_pi_iff.mp hg y))

theorem nr_Rω_measurable (hA : A.PosDef) (τ w : ℝ) (cs cr : ι → ℝ) :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) => nr_Rg w cs cr (nr_φs hA τ p.1) (nr_φr hA τ p.2)) :=
  nr_Rg_measurable' w cs cr ((nr_φs_measurable hA τ).comp measurable_fst)
    ((nr_φr_measurable hA τ).comp measurable_snd)

/-- **Law of the split field (generic):** φ_s + φ_r has the law M_* γ^ι (τ ≥ 0). -/
theorem nr_split_map (hA : A.PosDef) {τ : ℝ} (hτ : 0 ≤ τ) :
    (nr_P ι).map (fun p => nr_φs hA τ p.1 + nr_φr hA τ p.2) =
      (nr_gauss ι).map (fun ξ => mg_modeMat hA *ᵥ ξ) := by
  set α : ι → ℝ := nr_α hA τ with hα
  have h0 : ∀ K, 0 ≤ α K := fun K => (Real.exp_pos _).le
  have h1 : ∀ K, α K ≤ 1 := fun K => Real.exp_le_one_iff.mpr (by
    have := mul_nonneg hτ (hA.eigenvalues_pos K).le
    linarith)
  have hsq : ∀ K, √(1 - α K ^ 2) = nr_β hA τ K := by
    intro K
    rw [hα, nr_α, nr_β, sq, ← Real.exp_add]
    ring_nf
  have hfun : (fun p : (ι → ℝ) × (ι → ℝ) => nr_φs hA τ p.1 + nr_φr hA τ p.2) =
      (fun ξ => mg_modeMat hA *ᵥ ξ) ∘
        (fun p : (ι → ℝ) × (ι → ℝ) => fun K => α K * p.1 K + √(1 - α K ^ 2) * p.2 K) := by
    funext p
    rw [Function.comp_apply, nr_φs, nr_φr, ← mulVec_add]
    congr 1
    funext K
    rw [Pi.add_apply, hsq K]
  rw [hfun, ← Measure.map_map (mg_map_measurable hA) (by fun_prop), nr_P, nr_gauss,
    mg_split_law α h0 h1]

/-! ### Chaos (step 4), generic: polynomial remainders of total degree ≤ 4 -/

variable (ι) in
/-- The number of Gaussians |ι ⊕ ι|. -/
abbrev nr_d : ℕ := Fintype.card (ι ⊕ ι)

variable (ι) in
/-- The reindexing ℝ^{Fin (2|ι|)} ≃ᵐ ℝ^ι × ℝ^ι. -/
def nr_e : (Fin (nr_d ι) → ℝ) ≃ᵐ (ι → ℝ) × (ι → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι ⊕ ι => ℝ) (Fintype.equivFin (ι ⊕ ι)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ))

theorem nr_e_mp : MeasurePreserving (nr_e ι) (PP2Chaos2.ch2_gauss (nr_d ι)) (nr_P ι) := by
  have h1 := measurePreserving_piCongrLeft (fun _ : ι ⊕ ι => gaussianReal 0 1)
    (Fintype.equivFin (ι ⊕ ι)).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)
  unfold PP2Chaos2.ch2_gauss nr_P nr_gauss
  exact h2.comp h1

variable (ι) in
def nr_σ (b : ι ⊕ ι) : Fin (nr_d ι) := Fintype.equivFin (ι ⊕ ι) b

theorem nr_e_fst (x : Fin (nr_d ι) → ℝ) (K : ι) : (nr_e ι x).1 K = x (nr_σ ι (Sum.inl K)) := by
  simp [nr_e, nr_σ, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast]

theorem nr_e_snd (x : Fin (nr_d ι) → ℝ) (K : ι) : (nr_e ι x).2 K = x (nr_σ ι (Sum.inr K)) := by
  simp [nr_e, nr_σ, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast]

/-- **Generic chaos bound:** if F ∘ nr_e is a polynomial of total degree ≤ 4 then
E[F^{2m+2}] ≤ (ρ_m^{−8} E[F²])^{m+1}. -/
theorem nr_chaos_of_poly (F : (ι → ℝ) × (ι → ℝ) → ℝ) (P : MvPolynomial (Fin (nr_d ι)) ℝ)
    (hP : P.totalDegree ≤ 4) (hF : ∀ x, F (nr_e ι x) = MvPolynomial.eval x P) (m : ℕ) :
    ∫⁻ p, ENNReal.ofReal (F p ^ (2 * m + 2)) ∂nr_P ι ≤
      ENNReal.ofReal (((PP2Chaos2.ch2_rho m)⁻¹ ^ (2 * 4) * ∫ p, F p ^ 2 ∂nr_P ι) ^ (m + 1)) := by
  open PP2Chaos2 in
  obtain ⟨c, hc, hPc⟩ := nl_mvpoly_herm P hP
  have hF' : ∀ x, F (nr_e ι x) = ch2_F (nr_d ι) 1 c x := fun x => (hF x).trans (hPc x)
  have hmp := nr_e_mp (ι := ι)
  have hL : ∫⁻ p, ENNReal.ofReal (F p ^ (2 * m + 2)) ∂nr_P ι =
      ∫⁻ x, ENNReal.ofReal (ch2_F (nr_d ι) 1 c x ^ (2 * m + 2)) ∂ch2_gauss (nr_d ι) := by
    rw [← hmp.lintegral_comp_emb (nr_e ι).measurableEmbedding]
    simp_rw [hF']
  have hB : ∫ p, F p ^ 2 ∂nr_P ι = ∫ x, ch2_F (nr_d ι) 1 c x ^ 2 ∂ch2_gauss (nr_d ι) := by
    rw [← hmp.integral_comp' (fun p => F p ^ 2)]
    simp_rw [hF']
  rw [hL, hB, ch2_L2]
  set ρ := ch2_rho m with hρ
  have hρ0 : 0 < ρ := ch2_rho_pos m
  have hρi : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ0 |>.mpr (ch2_rho_le_one m)
  set c' : (Fin (nr_d ι) → Fin 5) → ℝ := fun α => ρ⁻¹ ^ ch2_deg α * c α with hc'
  have hF'' : ∀ x, ch2_F (nr_d ι) ρ c' x = ch2_F (nr_d ι) 1 c x := by
    intro x
    unfold ch2_F
    refine sum_congr rfl fun α _ => ?_
    rw [hc', one_pow, one_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ0.ne', one_pow, one_mul]
  have hN : ch2_norm (nr_d ι) c' ≤ ρ⁻¹ ^ (2 * 4) * ch2_norm (nr_d ι) c := by
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
    (ch2_admissible m ρ (ch2_rho_sq m)) (nr_d ι) c'
  simp_rw [hF''] at h
  refine h.trans ?_
  rw [← ENNReal.ofReal_pow (ch2_norm_nonneg _ c')]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (ch2_norm_nonneg _ c') hN _)

/-- The remainder with linear fields Ls ξˢ, Lr ξʳ, as a polynomial in the 2|ι| Gaussians. -/
def nr_RMv (w : ℝ) (cs cr : ι → ℝ) (Ls Lr : Matrix ι ι ℝ) : MvPolynomial (Fin (nr_d ι)) ℝ :=
  MvPolynomial.C w * ∑ y, ∑ j ∈ range 4,
    MvPolynomial.C (((Nat.choose 4 j : ℕ) : ℝ)) *
      nl_wickMv (cs y) j (nl_linMv (Ls y) (fun K => nr_σ ι (Sum.inl K))) *
      nl_wickMv (cr y) (4 - j) (nl_linMv (Lr y) (fun K => nr_σ ι (Sum.inr K)))

theorem nr_RMv_eval (w : ℝ) (cs cr : ι → ℝ) (Ls Lr : Matrix ι ι ℝ) (x : Fin (nr_d ι) → ℝ) :
    nr_Rg w cs cr (Ls *ᵥ (nr_e ι x).1) (Lr *ᵥ (nr_e ι x).2) =
      MvPolynomial.eval x (nr_RMv w cs cr Ls Lr) := by
  have hs : ∀ y, (Ls *ᵥ (nr_e ι x).1) y =
      MvPolynomial.eval x (nl_linMv (Ls y) (fun K => nr_σ ι (Sum.inl K))) := by
    intro y; rw [nl_linMv_eval]; simp only [mulVec, dotProduct, nr_e_fst]
  have hr : ∀ y, (Lr *ᵥ (nr_e ι x).2) y =
      MvPolynomial.eval x (nl_linMv (Lr y) (fun K => nr_σ ι (Sum.inr K))) := by
    intro y; rw [nl_linMv_eval]; simp only [mulVec, dotProduct, nr_e_snd]
  simp only [nr_Rg, nr_RMv, map_mul, map_sum, MvPolynomial.eval_C, nl_wickMv_eval, hs, hr]

theorem nr_RMv_deg (w : ℝ) (cs cr : ι → ℝ) (Ls Lr : Matrix ι ι ℝ) :
    (nr_RMv w cs cr Ls Lr).totalDegree ≤ 4 := by
  unfold nr_RMv
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine MvPolynomial.totalDegree_finsetSum_le fun y _ => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun j hj => ?_
  have hj4 : j < 4 := mem_range.mp hj
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  refine (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  have h1 := nl_wickMv_deg (cs y) j (nl_linMv_deg (Ls y) (fun K => nr_σ ι (Sum.inl K)))
  have h2 := nl_wickMv_deg (cr y) (4 - j) (nl_linMv_deg (Lr y) (fun K => nr_σ ι (Sum.inr K)))
  omega

theorem nr_mulVec_scale (M : Matrix ι ι ℝ) (a ξ : ι → ℝ) :
    M *ᵥ (fun K => a K * ξ K) = (M * diagonal a) *ᵥ ξ := by
  rw [← mulVec_mulVec]
  congr 1
  funext K
  rw [mulVec_diagonal]

/-- **Chaos hypothesis, generic (discharged):** for every PosDef A, τ, w, cs, cr, m,
E[R^{2m+2}] ≤ (ρ_m^{−8} E[R²])^{m+1} for R = R(φ_s(ξˢ), φ_r(ξʳ)). -/
theorem nr_chaos (hA : A.PosDef) (τ w : ℝ) (cs cr : ι → ℝ) (m : ℕ) :
    ∫⁻ p, ENNReal.ofReal (nr_Rg w cs cr (nr_φs hA τ p.1) (nr_φr hA τ p.2) ^ (2 * m + 2))
        ∂nr_P ι ≤
      ENNReal.ofReal (((PP2Chaos2.ch2_rho m)⁻¹ ^ (2 * 4) *
        ∫ p, nr_Rg w cs cr (nr_φs hA τ p.1) (nr_φr hA τ p.2) ^ 2 ∂nr_P ι) ^ (m + 1)) := by
  refine nr_chaos_of_poly _ (nr_RMv w cs cr (mg_modeMat hA * diagonal (nr_α hA τ))
    (mg_modeMat hA * diagonal (nr_β hA τ))) (nr_RMv_deg _ _ _ _ _) (fun x => ?_) m
  rw [← nr_RMv_eval, nr_φs, nr_φr, nr_mulVec_scale, nr_mulVec_scale]

/-- **Generic Nelson bound.** PosDef precision A on ι, weight w ≥ 0, Wick constant c, a cutoff
schedule τ(u) ≥ 0 and rough Wick constants cr(u) (any family); if the smooth constant
D(u) = 6wΣ(c − cr(u))² ≤ a + b u² and the remainder E[R_u²] ≤ K e^{−θu}, then for λ ∈ [0,1]
∫ e^{−2λV} d(M_* γ^ι) ≤ 1 + nl_N a b (230⁸ max(K,0)) θ 24. -/
theorem nr_generic (hA : A.PosDef) {w : ℝ} (hw : 0 ≤ w) (c : ℝ) (τ : ℝ → ℝ)
    (hτ : ∀ u, 0 ≤ u → 0 ≤ τ u) (cr : ℝ → ι → ℝ) {a b K θ : ℝ} (hb : 0 ≤ b) (hθ : 0 < θ)
    (hS : ∀ u, 0 ≤ u → nr_Dg w (fun y => c - cr u y) ≤ a + b * u ^ 2)
    (hL2 : ∀ u, 0 ≤ u → ∫ p, nr_Rg w (fun y => c - cr u y) (cr u)
        (nr_φs hA (τ u) p.1) (nr_φr hA (τ u) p.2) ^ 2 ∂nr_P ι ≤ K * Real.exp (-(θ * u)))
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ∫⁻ ψ, ENNReal.ofReal (Real.exp (-(2 * lam * nr_Vg w c ψ)))
        ∂(nr_gauss ι).map (fun ξ => mg_modeMat hA *ᵥ ξ) ≤
      ENNReal.ofReal (1 + nl_N a b (230 ^ 8 * max K 0) θ 24) := by
  set M : ℝ := 230 ^ 8 * max K 0 with hMdef
  have hM : 0 ≤ M := by positivity
  set μ := (nr_gauss ι).map (fun ξ => mg_modeMat hA *ᵥ ξ) with hμ
  have hmain : ∫⁻ ψ, ENNReal.ofReal (Real.exp (-nr_Vg w c ψ) ^ 2) ∂μ ≤
      ENNReal.ofReal (nl_N a b M θ 24) := by
    refine nl_abstract μ (nr_P ι) (nr_Vg w c) (nr_Vg_measurable w c)
      (fun u p => nr_φs hA (τ u) p.1 + nr_φr hA (τ u) p.2)
      (fun u _ => nr_Φ_measurable hA _) (fun u hu => nr_split_map hA (hτ u hu))
      (fun u p => nr_Rg w (fun y => c - cr u y) (cr u) (nr_φs hA (τ u) p.1) (nr_φr hA (τ u) p.2))
      (fun u _ => nr_Rω_measurable hA _ w _ _)
      24 hb hM hθ ?_ ?_
    · intro u hu p
      have h1 := nr_Vsg_ge hw (fun y => c - cr u y) (nr_φs hA (τ u) p.1)
      have h2 := hS u hu
      show nr_Rg w _ _ _ _ - (a + b * u ^ 2) ≤ nr_Vg w c _
      rw [nr_Vg_split w c (fun y => c - cr u y) (cr u) (fun y => by ring)]
      linarith
    · intro u hu m
      refine (nr_chaos hA (τ u) w _ _ m).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI := hL2 u hu
      have hI0 : 0 ≤ ∫ p, nr_Rg w (fun y => c - cr u y) (cr u)
          (nr_φs hA (τ u) p.1) (nr_φr hA (τ u) p.2) ^ 2 ∂nr_P ι :=
        integral_nonneg fun _ => sq_nonneg _
      apply pow_le_pow_left₀ (mul_nonneg (pow_nonneg (inv_nonneg.mpr
        (PP2Chaos2.ch2_rho_nonneg m)) _) hI0)
      rw [nl_rho_pow]
      calc 230 ^ 8 * ((m : ℝ) + 1) ^ 24 * ∫ p, nr_Rg w (fun y => c - cr u y) (cr u)
            (nr_φs hA (τ u) p.1) (nr_φr hA (τ u) p.2) ^ 2 ∂nr_P ι
          ≤ 230 ^ 8 * ((m : ℝ) + 1) ^ 24 * (max K 0 * Real.exp (-(θ * u))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hI.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        _ = M * ((m : ℝ) + 1) ^ 24 * Real.exp (-(θ * u)) := by rw [hMdef]; ring
  have : IsProbabilityMeasure μ := by
    rw [hμ]; infer_instance
  calc ∫⁻ ψ, ENNReal.ofReal (Real.exp (-(2 * lam * nr_Vg w c ψ))) ∂μ
      ≤ ∫⁻ ψ, (1 + ENNReal.ofReal (Real.exp (-nr_Vg w c ψ) ^ 2)) ∂μ := by
        refine lintegral_mono fun ψ => ?_
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        exact ENNReal.ofReal_le_ofReal (nl_exp_lam_le lam _ hl0 hl1)
    _ = 1 + ∫⁻ ψ, ENNReal.ofReal (Real.exp (-nr_Vg w c ψ) ^ 2) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
    _ ≤ 1 + ENNReal.ofReal (nl_N a b M θ 24) := by gcongr
    _ = ENNReal.ofReal (1 + nl_N a b M θ 24) := by
        rw [ENNReal.ofReal_add zero_le_one (by unfold nl_N; positivity), ENNReal.ofReal_one]

end Generic

end PP2NelsonRegion

end

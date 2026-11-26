import LongTable.PP2Nelson
import LongTable.PP2ModesGen

/-!
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

/-! ## 2. Regions B ⊆ box: the Nelson setting for the free region measure -/

section Region

variable {n k : ℕ}

/-- The rough Wick constant of the region, c_r(T)(y) = C^B_r(T)(y, y). -/
def nr_cr (n k : ℕ) (m₀ T : ℝ) (B : Finset (DSite n k)) (y : {z // z ∈ B}) : ℝ :=
  mg_regionRough n k m₀ T B y y

/-- The smooth Wick constant of the region, c₁(T)(y) = freeVar − c_r(T)(y)
(= region Wick defect + region smooth variance). -/
def nr_cs (n k : ℕ) (m₀ T : ℝ) (B : Finset (DSite n k)) (y : {z // z ∈ B}) : ℝ :=
  freeVar n m₀ - nr_cr n k m₀ T B y

/-- V_B(ψ) = ε² Σ_{y∈B} :ψ_y⁴:_{freeVar}. -/
def nr_V (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) (ψ : {z // z ∈ B} → ℝ) : ℝ :=
  spacing n ^ 2 * ∑ y, wickPow (freeVar n m₀) 4 (ψ y)

/-- The region remainder R_T(φs, φr). -/
def nr_R (n k : ℕ) (m₀ T : ℝ) (B : Finset (DSite n k)) (φs φr : {z // z ∈ B} → ℝ) : ℝ :=
  nr_Rg (spacing n ^ 2) (nr_cs n k m₀ T B) (nr_cr n k m₀ T B) φs φr

/-- D_B(T) = 6 ε² Σ_{y∈B} c₁(T)(y)². -/
def nr_D (n k : ℕ) (m₀ T : ℝ) (B : Finset (DSite n k)) : ℝ :=
  6 * spacing n ^ 2 * ∑ y, nr_cs n k m₀ T B y ^ 2

/-- Lattice time τ = ε⁻² T of the physical heat time T (the eigenvalues of rg_scaledOp B are ε² ×
those of regionOp B). -/
def nr_τ (n : ℕ) (T : ℝ) : ℝ := (spacing n ^ 2)⁻¹ * T

/-- The region remainder as a random variable of (ξˢ, ξʳ) ~ γ^B ⊗ γ^B (m₀ ≠ 0). -/
def nr_Rω {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (T : ℝ)
    (p : ({z // z ∈ B} → ℝ) × ({z // z ∈ B} → ℝ)) : ℝ :=
  nr_R n k m₀ T B (nr_φs (rg_scaledOp_posDef hm B) (nr_τ n T) p.1)
    (nr_φr (rg_scaledOp_posDef hm B) (nr_τ n T) p.2)

/-- The normalised free region measure: density ∝ qweight m₀ 0 ∘ zeroExt B on ℝ^B. -/
def nr_freeMeasure (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) : Measure ({z // z ∈ B} → ℝ) :=
  ENNReal.ofReal (∫ ψ, qweight n k m₀ 0 (zeroExt B ψ))⁻¹ •
    (volume : Measure ({z // z ∈ B} → ℝ)).withDensity
      (fun ψ => ENNReal.ofReal (qweight n k m₀ 0 (zeroExt B ψ)))

/-- The normalised free region expectation (ratio of Lebesgue integrals). -/
def nr_free (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) (F : ({z // z ∈ B} → ℝ) → ℝ) : ℝ :=
  (∫ ψ, F ψ * qweight n k m₀ 0 (zeroExt B ψ)) / ∫ ψ, qweight n k m₀ 0 (zeroExt B ψ)

/-- **The target (G4, region version):** ∃ N, ∀ n k x, ∀ λ ∈ [0, 1], for B = physBall n k x l,
E⁰_B[e^{−2λ V_B}] ≤ N with V_B = ε² Σ_{y∈B} :ψ_y⁴:_{freeVar}, stated for the lintegral against
the normalised free region measure and for the ratio of Lebesgue integrals. -/
def nl_NelsonRegion (m₀ l : ℝ) : Prop :=
  ∃ N : ℝ, ∀ (n k : ℕ) (x : DSite n k), ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    ∫⁻ ψ, ENNReal.ofReal (Real.exp (-(2 * lam *
        (spacing n ^ 2 * ∑ y : {z // z ∈ physBall n k x l}, wickPow (freeVar n m₀) 4 (ψ y)))))
        ∂nr_freeMeasure n k m₀ (physBall n k x l) ≤ ENNReal.ofReal N ∧
      nr_free n k m₀ (physBall n k x l) (fun ψ => Real.exp (-(2 * lam *
        (spacing n ^ 2 * ∑ y : {z // z ∈ physBall n k x l}, wickPow (freeVar n m₀) 4 (ψ y))))) ≤ N

/-- **Smooth-constant hypothesis (region):** D_B(T) ≤ a + b (log T)², T ∈ (0, 1], uniformly in
n, k, x (B = physBall n k x l). -/
def nr_SmoothHyp (m₀ l : ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ b ∧ ∀ (n k : ℕ) (x : DSite n k) (T : ℝ), 0 < T → T ≤ 1 →
    nr_D n k m₀ T (physBall n k x l) ≤ a + b * Real.log T ^ 2

/-- **Rough L² hypothesis (region):** E[R_T²] ≤ K T^θ, T ∈ (0, 1], uniformly in n, k, x. -/
def nr_RoughL2Hyp (m₀ l : ℝ) (hm : m₀ ≠ 0) : Prop :=
  ∃ K θ : ℝ, 0 < θ ∧ ∀ (n k : ℕ) (x : DSite n k) (T : ℝ), 0 < T → T ≤ 1 →
    ∫ p, nr_Rω hm (physBall n k x l) T p ^ 2 ∂nr_P {z // z ∈ physBall n k x l} ≤ K * T ^ θ

/-- **Chaos hypothesis (region):** E[R^{2m+2}] ≤ (ρ_m^{−8} E[R²])^{m+1}. -/
def nr_ChaosHyp (m₀ l : ℝ) (hm : m₀ ≠ 0) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k) (T : ℝ), 0 < T → T ≤ 1 → ∀ m : ℕ,
    ∫⁻ p, ENNReal.ofReal (nr_Rω hm (physBall n k x l) T p ^ (2 * m + 2))
        ∂nr_P {z // z ∈ physBall n k x l} ≤
      ENNReal.ofReal (((PP2Chaos2.ch2_rho m)⁻¹ ^ (2 * 4) *
        ∫ p, nr_Rω hm (physBall n k x l) T p ^ 2 ∂nr_P {z // z ∈ physBall n k x l}) ^ (m + 1))

/-- **The region chaos hypothesis holds** (any m₀ ≠ 0, l; in fact for every region B). -/
theorem nr_chaosHyp {m₀ : ℝ} (hm : m₀ ≠ 0) (l : ℝ) : nr_ChaosHyp m₀ l hm :=
  fun n k x _ _ _ m => nr_chaos (rg_scaledOp_posDef hm (physBall n k x l)) _ _ _ _ m

/-- The free region measure is M_* γ^B (m₀ ≠ 0). -/
theorem nr_freeMeasure_eq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) :
    nr_freeMeasure n k m₀ B =
      (nr_gauss {z // z ∈ B}).map (fun ξ => mg_modeMat (rg_scaledOp_posDef hm B) *ᵥ ξ) := by
  unfold nr_freeMeasure
  simp_rw [rg_qweight_zeroExt, PP2GaussIBP.gaussWeight]
  exact (mg_gauss_modes_measure (rg_scaledOp_posDef hm B)).symm

/-- **Nelson's bound for regions, reduced to the smooth-constant and rough L² hypotheses**
(chaos discharged by `nr_chaos`). N = 1 + nl_N a b (230⁸ max(K, 0)) θ 24. -/
theorem nr_nelsonRegion_of_hyps {m₀ : ℝ} (hm : m₀ ≠ 0) (l : ℝ) (hS : nr_SmoothHyp m₀ l)
    (hL2 : nr_RoughL2Hyp m₀ l hm) : nl_NelsonRegion m₀ l := by
  obtain ⟨a, b, hb, hSb⟩ := hS
  obtain ⟨K, θ, hθ, hK⟩ := hL2
  refine ⟨1 + nl_N a b (230 ^ 8 * max K 0) θ 24, fun n k x lam hl0 hl1 => ?_⟩
  set B := physBall n k x l with hB
  have hA := rg_scaledOp_posDef hm B
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  have hT : ∀ u : ℝ, 0 < Real.exp (-u) := fun u => Real.exp_pos _
  have hT1 : ∀ u : ℝ, 0 ≤ u → Real.exp (-u) ≤ 1 := fun u hu =>
    Real.exp_le_one_iff.mpr (by linarith)
  have hgen := nr_generic (rg_scaledOp_posDef hm B) hε (freeVar n m₀)
    (fun u => nr_τ n (Real.exp (-u))) (fun u _ => by unfold nr_τ; positivity)
    (fun u => nr_cr n k m₀ (Real.exp (-u)) B) hb hθ (a := a) (K := K)
    (fun u hu => by
      have h2 := hSb n k x (Real.exp (-u)) (hT u) (hT1 u hu)
      rw [Real.log_exp, neg_sq] at h2
      exact h2)
    (fun u hu => by
      have h2 := hK n k x (Real.exp (-u)) (hT u) (hT1 u hu)
      have hTθ : Real.exp (-u) ^ θ = Real.exp (-(θ * u)) := by
        rw [← Real.exp_mul]; ring_nf
      rw [hTθ] at h2
      exact h2)
    lam hl0 hl1
  have hle : ∫⁻ ψ, ENNReal.ofReal (Real.exp (-(2 * lam *
        (spacing n ^ 2 * ∑ y : {z // z ∈ B}, wickPow (freeVar n m₀) 4 (ψ y)))))
        ∂nr_freeMeasure n k m₀ B ≤ ENNReal.ofReal (1 + nl_N a b (230 ^ 8 * max K 0) θ 24) := by
    rw [nr_freeMeasure_eq hm B]
    exact hgen
  refine ⟨hle, ?_⟩
  have hFm : Measurable (fun ψ : {z // z ∈ B} → ℝ => Real.exp (-(2 * lam *
      (spacing n ^ 2 * ∑ y : {z // z ∈ B}, wickPow (freeVar n m₀) 4 (ψ y))))) :=
    Real.measurable_exp.comp ((nr_Vg_measurable (spacing n ^ 2) (freeVar n m₀)).const_mul
      (2 * lam)).neg
  rw [nr_free, mg_region_gauss_modes hm B, ← integral_map (mg_map_measurable _).aemeasurable
    hFm.aestronglyMeasurable,
    show (Measure.pi fun _ : {z // z ∈ B} => gaussianReal 0 1) = nr_gauss {z // z ∈ B} from rfl,
    ← nr_freeMeasure_eq hm B,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun φ => (Real.exp_pos _).le)
      hFm.aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (by unfold nl_N; positivity)] at this

end Region

/-! ## 3. The region Wick defect and the smooth region Wick constant -/

section Defect

variable {n k : ℕ}

/-- **Variational bound for regions:** 2 w(a) − ⟨w, regionOp w⟩ ≤ regionGreen B a a (m₀ ≠ 0). -/
theorem nr_region_two_mul_sub_quad_le {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (w : {z // z ∈ B} → ℝ) (a : {z // z ∈ B}) :
    2 * w a - w ⬝ᵥ regionOp n k m₀ B *ᵥ w ≤ regionGreen n k m₀ B a a := by
  set g : {z // z ∈ B} → ℝ := regionGreen n k m₀ B *ᵥ Pi.single a 1 with hg
  have hAg : regionOp n k m₀ B *ᵥ g = Pi.single a 1 := by
    rw [hg, mulVec_mulVec, fv2_regionOp_mul_regionGreen hm, one_mulVec]
  have hga : g a = regionGreen n k m₀ B a a := by simp [hg]
  have hAT : (regionOp n k m₀ B)ᵀ = regionOp n k m₀ B := by
    rw [regionOp, transpose_submatrix, dirOp_transpose]
  have hsym : g ⬝ᵥ regionOp n k m₀ B *ᵥ w = w ⬝ᵥ regionOp n k m₀ B *ᵥ g := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hAT, dotProduct_comm]
  have hva : w ⬝ᵥ (Pi.single a 1 : {z // z ∈ B} → ℝ) = w a := by
    simp [dotProduct, Pi.single_apply]
  have hgg : g ⬝ᵥ (Pi.single a 1 : {z // z ∈ B} → ℝ) = g a := by
    simp [dotProduct, Pi.single_apply]
  have h0 : 0 ≤ (w - g) ⬝ᵥ regionOp n k m₀ B *ᵥ (w - g) := by
    rw [← rg_quad_zeroExt]
    have h1 := dirOp_quad_ge m₀ (zeroExt B (w - g))
    have h2 : 0 ≤ m₀ ^ 2 * ∑ x : DSite n k, zeroExt B (w - g) x ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hsym, hAg, hva, hgg, hga] at h0
  linarith

/-- **Centre of a fitting odd sub-box contained in B ≤ region variance** (m₀ ≠ 0): the trial
field of `fv2_specVar_le_dirVar` is supported in the sub-box ⊆ B. -/
theorem nr_specVar_le_regionVar {m₀ : ℝ} (hm : m₀ ≠ 0) {B : Finset (DSite n k)} {M : ℕ}
    {x : DSite n k} (hfit : fv2_Fits M x) (hsub : fv2_subBox M x ⊆ B) (hM : M < 2 * M + 1)
    (hx : x ∈ B) :
    specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ ≤
      (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B ⟨x, hx⟩ ⟨x, hx⟩ := by
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  have hε0 : spacing n ≠ 0 := (spacing_pos n).ne'
  set lam := fv2_lam n m₀ M with hlam
  set E := fv2_E M x with hE
  set v : DField n k := ∑ K : Fin (2 * M + 1) × Fin (2 * M + 1), (E K x / lam K) • E K with hv
  set S := ∑ K : Fin (2 * M + 1) × Fin (2 * M + 1), E K x * E K x / lam K with hS
  have hvx : v x = S := by
    simp only [hv, hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun K _ => by ring
  set w : DField n k := ∑ K : Fin (2 * M + 1) × Fin (2 * M + 1), E K x • E K with hw
  have hAv : ∀ y, v y * (dirOp n k m₀ *ᵥ v) y = v y * w y := by
    intro y
    by_cases hy : y ∈ fv2_subBox M x
    · congr 1
      simp only [hv, hw, mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [hE, hlam, fv2_dirOp_E m₀ hfit K y hy]
      have := (fv2_lam_pos n m₀ M K).ne'
      field_simp
    · have : v y = 0 := by
        simp only [hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_eq_zero fun K _ => by rw [hE, fv2_E_out K hy, mul_zero]
      rw [this, zero_mul, zero_mul]
  have hquad : v ⬝ᵥ dirOp n k m₀ *ᵥ v = S := by
    have h1 : v ⬝ᵥ dirOp n k m₀ *ᵥ v = v ⬝ᵥ w := by
      simp only [dotProduct]; exact Finset.sum_congr rfl fun y _ => hAv y
    rw [h1, hv, hw, sum_dotProduct]
    simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hS]
    refine Finset.sum_congr rfl fun K _ => ?_
    have horth : ∀ L : Fin (2 * M + 1) × Fin (2 * M + 1),
        E K ⬝ᵥ E L = if K = L then 1 else 0 := fun L => by
      rw [hE]; exact fv2_E_orthonormal hfit K L
    simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hvB : ∀ y, y ∉ B → v y = 0 := by
    intro y hy
    have hy' : y ∉ fv2_subBox M x := fun h => hy (hsub h)
    simp only [hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun K _ => by rw [hE, fv2_E_out K hy', mul_zero]
  have hext : zeroExt B (fun z : {z // z ∈ B} => v z) = v := by
    funext y
    unfold zeroExt
    split_ifs with h
    · rfl
    · exact (hvB y h).symm
  have hvar0 := nr_region_two_mul_sub_quad_le hm B (fun z : {z // z ∈ B} => v z) ⟨x, hx⟩
  rw [← rg_quad_zeroExt, hext] at hvar0
  have hvar : 2 * v x - v ⬝ᵥ dirOp n k m₀ *ᵥ v ≤ regionGreen n k m₀ B ⟨x, hx⟩ ⟨x, hx⟩ := hvar0
  rw [hvx, hquad] at hvar
  have hSspec : specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ =
      (spacing n ^ 2)⁻¹ * S := by
    rw [specVar, hS, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    rw [hE, fv2_E_centre x (j₁, j₂) hM, hlam, fv2_lam]
    dsimp only
    have h1 := sineEig_pos (2 * M + 1) j₁ j₁.isLt
    have h2 := sineEig_pos (2 * M + 1) j₂ j₂.isLt
    have hd : 0 < m₀ ^ 2 * spacing n ^ 2 + sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂ := by
      positivity
    have hd' : 0 < (spacing n ^ 2)⁻¹ * (sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂)
        + m₀ ^ 2 := by positivity
    field_simp
    ring
  rw [hSspec]
  have : 2 * S - S = S := by ring
  rw [this] at hvar
  exact mul_le_mul_of_nonneg_left hvar (by positivity)

/-- **Region Wick defect, upper bound:** if the odd sub-box of half-width M centred at x fits in
the box and lies in B, then freeVar − ε⁻² regionGreen B x x ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))). -/
theorem nr_region_defect_le {m₀ : ℝ} (hm : m₀ ≠ 0) {B : Finset (DSite n k)} {M : ℕ}
    {x : DSite n k} (hfit : fv2_Fits M x) (hsub : fv2_subBox M x ⊆ B) (hx : x ∈ B) :
    freeVar n m₀ - (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B ⟨x, hx⟩ ⟨x, hx⟩ ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((M : ℝ) + 1))))) := by
  have hM : M < 2 * M + 1 := by omega
  have h1 := nr_specVar_le_regionVar hm hfit hsub hM hx
  have h2 := fv2_freeVar_sub_centre_le (n := n) hm M hM
  rw [← mul_assoc]
  linarith

/-- Region Wick defect, lower bound: freeVar − ε⁻² regionGreen B y y ≥ 0. -/
theorem nr_region_defect_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (y : {z // z ∈ B}) : 0 ≤ freeVar n m₀ - (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y y := by
  have h1 := fv2_regionGreen_le_dirGreen hm B y y
  have h2 := dirVar_le_freeVar (n := n) (k := k) hm y
  have h3 : (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y y ≤
      (spacing n ^ 2)⁻¹ * dirGreen n k m₀ y y := mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

theorem nr_regionHeat_integrableOn {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (y z : {w // w ∈ B}) :
    IntegrableOn (fun t => mg_regionHeat n k m₀ t B y z) (Set.Ioi 0) :=
  mg_heat_integrableOn (fv2_regionOp_posDef hm B) y z

/-- c₁(T)(y) = b_B(y) + ε⁻² ∫_{(T,∞)} p^B_t(y, y) dt (region defect + region smooth variance). -/
theorem nr_cs_eq {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) (B : Finset (DSite n k))
    (y : {z // z ∈ B}) :
    nr_cs n k m₀ T B y = (freeVar n m₀ - (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y y) +
      (spacing n ^ 2)⁻¹ * ∫ t in Set.Ioi T, mg_regionHeat n k m₀ t B y y := by
  have hI := nr_regionHeat_integrableOn hm B y y
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), mg_regionHeat n k m₀ t B y y =
      (∫ t in Set.Ioc 0 T, mg_regionHeat n k m₀ t B y y) +
        ∫ t in Set.Ioi T, mg_regionHeat n k m₀ t B y y := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI.mono_set Set.Ioc_subset_Ioi_self) (hI.mono_set (Set.Ioi_subset_Ioi hT))
  rw [nr_cs, nr_cr, mg_regionRough, ← mg_integral_regionHeat hm B y y, hsplit]
  ring

theorem nr_tail_int_nonneg (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (B : Finset (DSite n k))
    (y : {z // z ∈ B}) :
    0 ≤ (spacing n ^ 2)⁻¹ * ∫ t in Set.Ioi T, mg_regionHeat n k m₀ t B y y :=
  mul_nonneg (by have := spacing_pos n; positivity)
    (setIntegral_nonneg measurableSet_Ioi fun t ht =>
      (mg_regionHeat_le m₀ B (hT.trans (le_of_lt ht)) y y).1)

/-- Region smooth variance: ε⁻² ∫_{(T,∞)} p^B_t(y, y) dt ≤ (π/4)(log(1/T) + m₀⁻²), 0 < T ≤ 1. -/
theorem nr_tail_int_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (B : Finset (DSite n k)) (y : {z // z ∈ B}) :
    (spacing n ^ 2)⁻¹ * ∫ t in Set.Ioi T, mg_regionHeat n k m₀ t B y y ≤
      π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) := by
  have hm2 : 0 < m₀ ^ 2 := by positivity
  have hI := nr_regionHeat_integrableOn hm B y y
  set g : ℝ → ℝ := fun t => (spacing n ^ 2)⁻¹ * mg_regionHeat n k m₀ t B y y with hg
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
          have hd := mg_regionHeat_diag_le m₀ B ht0 y
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
          have hd := mg_regionHeat_diag_le m₀ B ht0 y
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

/-- **Region smooth Wick constant bounds:** if the odd sub-box of half-width M centred at y fits
the box and lies in B (0 < T ≤ 1, m₀ ≠ 0):
0 ≤ c₁(T)(y) ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))) + (π/4)(log(1/T) + m₀⁻²). -/
theorem nr_cs_bounds {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {B : Finset (DSite n k)} {M : ℕ} {y : DSite n k} (hfit : fv2_Fits M y)
    (hsub : fv2_subBox M y ⊆ B) (hy : y ∈ B) :
    0 ≤ nr_cs n k m₀ T B ⟨y, hy⟩ ∧ nr_cs n k m₀ T B ⟨y, hy⟩ ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((M : ℝ) + 1))))) +
        π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) := by
  rw [nr_cs_eq hm hT.le B ⟨y, hy⟩]
  have h1 := nr_region_defect_nonneg hm B ⟨y, hy⟩
  have h2 := nr_region_defect_le hm hfit hsub hy
  have h3 := nr_tail_int_nonneg m₀ hT.le B ⟨y, hy⟩
  have h4 := nr_tail_int_le hm hT hT1 B ⟨y, hy⟩
  constructor <;> linarith

end Defect

/-! ## 4. Geometry of the ball B = physBall x l: the lattice rectangle and the region distance -/

section Geometry

variable {n k : ℕ}

/-- The lattice radius R = ⌊l/ε⌋ of the ball. -/
def nr_rad (n : ℕ) (l : ℝ) : ℕ := ⌊l / spacing n⌋₊

theorem nr_sub_le_iff (a b : ℕ) {t : ℝ} (ht : 0 ≤ t) : (a : ℝ) - b ≤ t ↔ a ≤ b + ⌊t⌋₊ := by
  by_cases hab : b ≤ a
  · have e : ((a - b : ℕ) : ℝ) = (a : ℝ) - b := by rw [Nat.cast_sub hab]
    rw [← e, ← Nat.le_floor_iff ht]
    omega
  · push Not at hab
    have : (a : ℝ) - b < 0 := by
      have : (a : ℝ) < b := by exact_mod_cast hab
      linarith
    constructor <;> intro _ <;> [omega; linarith]

theorem nr_coord_iff {l : ℝ} (hl : 0 ≤ l) (a b : ℕ) :
    spacing n * |(a : ℝ) - b| ≤ l ↔ a ≤ b + nr_rad n l ∧ b ≤ a + nr_rad n l := by
  have hε := spacing_pos n
  have ht : 0 ≤ l / spacing n := div_nonneg hl hε.le
  rw [mul_comm, ← le_div_iff₀ hε, abs_le, nr_rad, ← nr_sub_le_iff a b ht, ← nr_sub_le_iff b a ht]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- **The ball is a lattice rectangle:** u ∈ physBall x l ↔ |u_i − x_i| ≤ R (i = 1, 2), l ≥ 0. -/
theorem nr_mem_physBall_iff {l : ℝ} (hl : 0 ≤ l) {x u : DSite n k} :
    u ∈ physBall n k x l ↔ ((u.1 : ℕ) ≤ x.1 + nr_rad n l ∧ (x.1 : ℕ) ≤ u.1 + nr_rad n l) ∧
      ((u.2 : ℕ) ≤ x.2 + nr_rad n l ∧ (x.2 : ℕ) ≤ u.2 + nr_rad n l) := by
  rw [mem_physBall]
  unfold supDist
  rw [dpos_zero, dpos_zero, dpos_one, dpos_one]
  have e1 : spacing n * ((x.1 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((u.1 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((u.1 : ℕ) : ℝ) - ((x.1 : ℕ) : ℝ)) * (-1) := by ring
  have e2 : spacing n * ((x.2 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((u.2 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((u.2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) * (-1) := by ring
  rw [e1, e2]
  simp only [abs_mul, abs_neg, abs_one, mul_one, abs_of_pos (spacing_pos n)]
  rw [max_le_iff, nr_coord_iff hl, nr_coord_iff hl]

/-- 1-D distance of j to the ends of the interval [c − R, min(N − 1, c + R)]. -/
def nr_d1 (N c R j : ℕ) : ℕ := min (j - (c - R)) (min (N - 1) (c + R) - j)

/-- The region distance M_B(y) of y to ∂B (in lattice units) for the rectangle B = physBall x l. -/
def nr_M (n k : ℕ) (x : DSite n k) (R : ℕ) (y : DSite n k) : ℕ :=
  min (nr_d1 (boxN n k) x.1 R y.1) (nr_d1 (boxN n k) x.2 R y.2)

theorem nr_fits {l : ℝ} (hl : 0 ≤ l) {x y : DSite n k} (hy : y ∈ physBall n k x l) :
    fv2_Fits (nr_M n k x (nr_rad n l) y) y := by
  rw [nr_mem_physBall_iff hl] at hy
  have h1 := y.1.isLt
  have h2 := y.2.isLt
  unfold fv2_Fits nr_M nr_d1
  omega

theorem nr_subBox_sub {l : ℝ} (hl : 0 ≤ l) {x y : DSite n k} (hy : y ∈ physBall n k x l) :
    fv2_subBox (nr_M n k x (nr_rad n l) y) y ⊆ physBall n k x l := by
  intro u hu
  simp only [fv2_subBox, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rw [nr_mem_physBall_iff hl] at hy ⊢
  have h1 := y.1.isLt
  have h2 := y.2.isLt
  unfold nr_M nr_d1 at hu
  omega

/-- Σ_{j∈S} f(j) ≤ Σ_{i<|S|} f(i) for antitone f and S ⊆ ℕ finite. -/
theorem nr_sum_anti (f : ℕ → ℝ) (hf : Antitone f) (S : Finset ℕ) :
    ∑ j ∈ S, f j ≤ ∑ i ∈ range S.card, f i := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [sum_insert hna, card_insert_of_notMem hna, sum_range_succ]
    have hsub : s ⊆ range a := fun x hx => mem_range.mpr (ha x hx)
    have hcard : s.card ≤ a := (card_le_card hsub).trans (card_range a).le
    have := hf hcard
    linarith

/-- The same over an injective image. -/
theorem nr_sum_anti_inj {α : Type*} [DecidableEq α] (f : ℕ → ℝ) (hf : Antitone f) (s : Finset α)
    (φ : α → ℕ) (hφ : Set.InjOn φ s) :
    ∑ a ∈ s, f (φ a) ≤ ∑ i ∈ range s.card, f i := by
  rw [← sum_image (g := φ) (f := f) hφ, ← card_image_of_injOn hφ]
  exact nr_sum_anti f hf _

/-- The 1-D coordinate set {a < N : |a − c| ≤ R}. -/
def nr_s1 (N c R : ℕ) : Finset (Fin N) := univ.filter fun a => (a : ℕ) ≤ c + R ∧ c ≤ a + R

theorem nr_s1_card (N c R : ℕ) : (nr_s1 N c R).card ≤ 2 * R + 1 := by
  have h := card_le_card_of_injOn (s := nr_s1 N c R) (t := Finset.Icc (c - R) (c + R))
    (fun a : Fin N => (a : ℕ))
    (fun a ha => by
      have ha' : (a : ℕ) ≤ c + R ∧ c ≤ a + R := by simpa [nr_s1] using ha
      show (a : ℕ) ∈ (Finset.Icc (c - R) (c + R) : Set ℕ)
      rw [Finset.mem_coe, Finset.mem_Icc]
      omega)
    (fun a _ b _ h => Fin.ext h)
  rw [Nat.card_Icc] at h
  omega

theorem nr_anti_f (n : ℕ) : Antitone (nl_f n) := fun _ _ h => nl_f_anti n h

/-- 1-D sum: Σ_{a ∈ s} f(d₁(a)) ≤ 2 Σ_{i<|s|} f(i). -/
theorem nr_sum1 (n N c R : ℕ) :
    ∑ a ∈ nr_s1 N c R, nl_f n (nr_d1 N c R a) ≤ 2 * ∑ i ∈ range (nr_s1 N c R).card, nl_f n i := by
  have hmem : ∀ a ∈ nr_s1 N c R, (a : ℕ) ≤ c + R ∧ c ≤ a + R := by
    intro a ha; simpa [nr_s1] using ha
  calc ∑ a ∈ nr_s1 N c R, nl_f n (nr_d1 N c R a)
      ≤ ∑ a ∈ nr_s1 N c R, (nl_f n ((a : ℕ) - (c - R)) + nl_f n (min (N - 1) (c + R) - a)) :=
        sum_le_sum fun a _ => nl_f_min n _ _
    _ = ∑ a ∈ nr_s1 N c R, nl_f n ((a : ℕ) - (c - R)) +
          ∑ a ∈ nr_s1 N c R, nl_f n (min (N - 1) (c + R) - a) := sum_add_distrib
    _ ≤ ∑ i ∈ range (nr_s1 N c R).card, nl_f n i + ∑ i ∈ range (nr_s1 N c R).card, nl_f n i := by
        gcongr
        · exact nr_sum_anti_inj _ (nr_anti_f n) (nr_s1 N c R) (fun a : Fin N => (a : ℕ) - (c - R))
            (fun a ha b hb h => by
              have := hmem a (Finset.mem_coe.mp ha); have := hmem b (Finset.mem_coe.mp hb)
              exact Fin.ext (by simp only at h; omega))
        · exact nr_sum_anti_inj _ (nr_anti_f n) (nr_s1 N c R)
            (fun a : Fin N => min (N - 1) (c + R) - (a : ℕ))
            (fun a ha b hb h => by
              have := hmem a (Finset.mem_coe.mp ha); have := hmem b (Finset.mem_coe.mp hb)
              have := a.isLt; have := b.isLt
              exact Fin.ext (by simp only at h; omega))
    _ = _ := by ring

theorem nr_physBall_eq {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    physBall n k x l = nr_s1 (boxN n k) x.1 (nr_rad n l) ×ˢ nr_s1 (boxN n k) x.2 (nr_rad n l) := by
  ext u
  rw [nr_mem_physBall_iff hl, mem_product]
  simp [nr_s1]

theorem nr_spacing_le_one (n : ℕ) : spacing n ≤ 1 := by
  unfold spacing
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- ε (2R + 1) ≤ 2l + 1. -/
theorem nr_eps_Q_le {l : ℝ} (hl : 0 ≤ l) :
    spacing n * (2 * (nr_rad n l : ℝ) + 1) ≤ 2 * l + 1 := by
  have hε := spacing_pos n
  have hR : (nr_rad n l : ℝ) ≤ l / spacing n := Nat.floor_le (div_nonneg hl hε.le)
  have h1 : spacing n * (nr_rad n l : ℝ) ≤ l := by
    rw [le_div_iff₀ hε] at hR; linarith
  have := nr_spacing_le_one n
  nlinarith

/-- **Lattice volume of the ball:** ε² |B| ≤ (2l + 1)². -/
theorem nr_card_le {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    spacing n ^ 2 * ((physBall n k x l).card : ℝ) ≤ (2 * l + 1) ^ 2 := by
  have hε := spacing_pos n
  set Q : ℝ := 2 * (nr_rad n l : ℝ) + 1 with hQ
  have hc : ((physBall n k x l).card : ℝ) ≤ Q * Q := by
    rw [nr_physBall_eq hl, card_product]
    have h1 := nr_s1_card (boxN n k) x.1 (nr_rad n l)
    have h2 := nr_s1_card (boxN n k) x.2 (nr_rad n l)
    have h1' : ((nr_s1 (boxN n k) x.1 (nr_rad n l)).card : ℝ) ≤ Q := by
      rw [hQ]; exact_mod_cast h1
    have h2' : ((nr_s1 (boxN n k) x.2 (nr_rad n l)).card : ℝ) ≤ Q := by
      rw [hQ]; exact_mod_cast h2
    push_cast
    exact mul_le_mul h1' h2' (by positivity) (by positivity)
  have hQe := nr_eps_Q_le (n := n) hl
  calc spacing n ^ 2 * ((physBall n k x l).card : ℝ) ≤ spacing n ^ 2 * (Q * Q) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (spacing n * Q) ^ 2 := by ring
    _ ≤ (2 * l + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hQe 2

/-- **Lattice sum of the region boundary singularity:** ε² Σ_{y∈B} (ε(M_B(y)+1))^{−1/2}
≤ 8 (2l+1)^{3/2}, uniformly in n, k, x (B = physBall x l, l ≥ 0). -/
theorem nr_sum_f_M {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    spacing n ^ 2 * ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x (nr_rad n l) y) ≤
      8 * ((2 * l + 1) * √(2 * l + 1)) := by
  have hε := spacing_pos n
  set R := nr_rad n l with hRdef
  set s1 := nr_s1 (boxN n k) x.1 R with hs1
  set s2 := nr_s1 (boxN n k) x.2 R with hs2
  set Q : ℝ := 2 * (R : ℝ) + 1 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hc1 : (s1.card : ℝ) ≤ Q := by rw [hQ]; exact_mod_cast nr_s1_card _ _ _
  have hc2 : (s2.card : ℝ) ≤ Q := by rw [hQ]; exact_mod_cast nr_s1_card _ _ _
  have hS : ∀ s : Finset (Fin (boxN n k)), (s.card : ℝ) ≤ Q →
      ∑ i ∈ range s.card, nl_f n i ≤ (√(spacing n))⁻¹ * (2 * √Q) := by
    intro s hs
    refine (nl_sum_f_le n s.card).trans ?_
    gcongr
  have hT1 := nr_sum1 n (boxN n k) x.1 R
  have hT2 := nr_sum1 n (boxN n k) x.2 R
  have hsum : ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x R y) ≤
      (s2.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        (s1.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) := by
    rw [nr_physBall_eq hl]
    calc ∑ y ∈ s1 ×ˢ s2, nl_f n (nr_M n k x R y)
        ≤ ∑ y ∈ s1 ×ˢ s2, (nl_f n (nr_d1 (boxN n k) x.1 R y.1) +
            nl_f n (nr_d1 (boxN n k) x.2 R y.2)) := sum_le_sum fun y _ => nl_f_min n _ _
      _ = (s2.card : ℝ) * ∑ a ∈ s1, nl_f n (nr_d1 (boxN n k) x.1 R a) +
            (s1.card : ℝ) * ∑ b ∈ s2, nl_f n (nr_d1 (boxN n k) x.2 R b) := by
          rw [sum_add_distrib, sum_product, sum_product_right]
          simp only [sum_const, nsmul_eq_mul, mul_sum]
      _ ≤ _ := by
          gcongr
          · exact hT1.trans (by gcongr; exact hS s1 hc1)
          · exact hT2.trans (by gcongr; exact hS s2 hc2)
  have hsε : 0 < √(spacing n) := Real.sqrt_pos.mpr hε
  have hQe := nr_eps_Q_le (n := n) hl
  have hkey : spacing n ^ 2 * ((s2.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        (s1.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) ≤
      spacing n ^ 2 * (Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) := by
    gcongr
  have heq : spacing n ^ 2 * (Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) =
      8 * ((spacing n * Q) * √(spacing n * Q)) := by
    rw [Real.sqrt_mul hε.le]
    have hεs : spacing n = √(spacing n) * √(spacing n) := (mul_self_sqrt hε.le).symm
    set t := √(spacing n)
    rw [hεs]
    field_simp
    ring
  have hmono : (spacing n * Q) * √(spacing n * Q) ≤ (2 * l + 1) * √(2 * l + 1) :=
    mul_le_mul hQe (Real.sqrt_le_sqrt hQe) (Real.sqrt_nonneg _) (by linarith)
  calc spacing n ^ 2 * ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x R y)
      ≤ spacing n ^ 2 * ((s2.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        (s1.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := hkey
    _ = _ := heq
    _ ≤ 8 * ((2 * l + 1) * √(2 * l + 1)) := by linarith

end Geometry

/-! ## 5. Discharging the region smooth-constant hypothesis (m₀ ≠ 0, l ≥ 0) -/

section Smooth

/-- **The region smooth-constant hypothesis holds for every m₀ ≠ 0 and l ≥ 0:**
6 ε² Σ_{y∈B} c₁(T)(y)² ≤ a + b (log T)², uniformly in n, k, x (B = physBall n k x l), with
a = A₀ L² + 8 A₁ L^{3/2}, b = A₂ L², L = 2l + 1. -/
theorem nr_smoothHyp {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) : nr_SmoothHyp m₀ l := by
  set P : ℝ := (π / 4) ^ 2 with hP
  set m' : ℝ := (√|m₀|)⁻¹ with hm'
  set L := 2 * l + 1 with hLdef
  have hP0 : 0 ≤ P := by positivity
  have hm'0 : 0 ≤ m' := by positivity
  have hm2 : 0 < m₀ ^ 2 := by positivity
  have hL0 : 0 ≤ L := by linarith
  set A₀ : ℝ := P * (408 + 24 * ((m₀ ^ 2)⁻¹) ^ 2) with hA₀
  set A₁ : ℝ := P * 384 * m' with hA₁
  set A₂ : ℝ := 24 * P with hA₂
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨A₀ * L ^ 2 + A₁ * (8 * (L * √L)), A₂ * L ^ 2, by positivity,
    fun n k x T hT hT1 => ?_⟩
  set B := physBall n k x l with hB
  set R := nr_rad n l with hR
  have hpt : ∀ y : {z // z ∈ B}, 6 * nr_cs n k m₀ T B y ^ 2 ≤
      A₀ + A₁ * nl_f n (nr_M n k x R y) + A₂ * Real.log T ^ 2 := by
    intro y
    have h01 : 0 ≤ nr_cs n k m₀ T B y ∧ nr_cs n k m₀ T B y ≤
        π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1))))) +
          π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) :=
      nr_cs_bounds hm hT hT1 (nr_fits hl y.2) (nr_subBox_sub hl y.2) y.2
    obtain ⟨h0, h1⟩ := h01
    set ℓ := Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1)))) with hℓ
    have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
    have hx : √(1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1)))) =
        m' * nl_f n (nr_M n k x R y) := by
      rw [nl_f, one_div, Real.sqrt_inv, Real.sqrt_mul (abs_nonneg _), mul_inv]
    have hℓ2 : ℓ ^ 2 ≤ 16 * (1 + m' * nl_f n (nr_M n k x R y)) := by
      rw [← hx]
      exact nl_posLog_sq_le (by have := spacing_pos n; positivity)
    set Bq := π / 4 * (1 + ℓ) with hBq
    set E := π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) with hE
    have hlogT : Real.log T ≤ 0 := Real.log_nonpos hT.le hT1
    have hE0 : 0 ≤ E := mul_nonneg (by positivity) (by have := inv_pos.mpr hm2; linarith)
    have hB0 : 0 ≤ Bq := by positivity
    have hc2 : nr_cs n k m₀ T B y ^ 2 ≤ 2 * Bq ^ 2 + 2 * E ^ 2 := by
      have : nr_cs n k m₀ T B y ^ 2 ≤ (Bq + E) ^ 2 := pow_le_pow_left₀ h0 h1 2
      nlinarith [sq_nonneg (Bq - E)]
    have hB2 : Bq ^ 2 ≤ P * (34 + 32 * (m' * nl_f n (nr_M n k x R y))) := by
      have h11 : (1 + ℓ) ^ 2 ≤ 2 * (1 + ℓ ^ 2) := by nlinarith [sq_nonneg (ℓ - 1)]
      calc Bq ^ 2 = P * (1 + ℓ) ^ 2 := by rw [hBq, hP]; ring
        _ ≤ P * (2 * (1 + ℓ ^ 2)) := mul_le_mul_of_nonneg_left h11 hP0
        _ ≤ P * (34 + 32 * (m' * nl_f n (nr_M n k x R y))) := by
            apply mul_le_mul_of_nonneg_left _ hP0; linarith
    have hE2 : E ^ 2 ≤ P * (2 * (((m₀ ^ 2)⁻¹) ^ 2 + Real.log T ^ 2)) := by
      calc E ^ 2 = P * (-Real.log T + (m₀ ^ 2)⁻¹) ^ 2 := by rw [hE, hP]; ring
        _ ≤ P * (2 * (((m₀ ^ 2)⁻¹) ^ 2 + Real.log T ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hP0
            nlinarith [sq_nonneg (Real.log T + (m₀ ^ 2)⁻¹)]
    rw [hA₀, hA₁, hA₂]
    nlinarith
  have hε := spacing_pos n
  have hcard : spacing n ^ 2 * (B.card : ℝ) ≤ L ^ 2 := nr_card_le hl x
  have hfs : spacing n ^ 2 * ∑ y ∈ B, nl_f n (nr_M n k x R y) ≤ 8 * (L * √L) := nr_sum_f_M hl x
  have hsc : ∑ y : {z // z ∈ B}, nl_f n (nr_M n k x R y) = ∑ y ∈ B, nl_f n (nr_M n k x R y) :=
    Finset.sum_coe_sort B (fun y => nl_f n (nr_M n k x R y))
  have hsplit : ∑ y : {z // z ∈ B}, (A₀ + A₁ * nl_f n (nr_M n k x R y) + A₂ * Real.log T ^ 2) =
      A₀ * (B.card : ℝ) + A₁ * ∑ y ∈ B, nl_f n (nr_M n k x R y) +
        A₂ * (B.card : ℝ) * Real.log T ^ 2 := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, card_univ,
      Fintype.card_coe, nsmul_eq_mul, nsmul_eq_mul, ← mul_sum, hsc]
    ring
  unfold nr_D
  calc 6 * spacing n ^ 2 * ∑ y : {z // z ∈ B}, nr_cs n k m₀ T B y ^ 2
      = spacing n ^ 2 * ∑ y : {z // z ∈ B}, 6 * nr_cs n k m₀ T B y ^ 2 := by
        rw [← mul_sum]; ring
    _ ≤ spacing n ^ 2 * ∑ y : {z // z ∈ B},
          (A₀ + A₁ * nl_f n (nr_M n k x R y) + A₂ * Real.log T ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => hpt y) (by positivity)
    _ = A₀ * (spacing n ^ 2 * (B.card : ℝ)) +
          A₁ * (spacing n ^ 2 * ∑ y ∈ B, nl_f n (nr_M n k x R y)) +
          A₂ * (spacing n ^ 2 * (B.card : ℝ)) * Real.log T ^ 2 := by
        rw [hsplit]; ring
    _ ≤ A₀ * L ^ 2 + A₁ * (8 * (L * √L)) + A₂ * L ^ 2 * Real.log T ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_left hcard hA₀0
        have h2 := mul_le_mul_of_nonneg_left hfs hA₁0
        have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA₂0)
          (sq_nonneg (Real.log T))
        linarith

/-- **Reduction (G4, region): for m₀ ≠ 0 and l ≥ 0, the region rough L² bound alone implies
Nelson's bound for the free region measures of the balls B = physBall n k x l.** -/
theorem nl_nelsonRegion_of_roughL2 {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l)
    (hL2 : nr_RoughL2Hyp m₀ l hm) : nl_NelsonRegion m₀ l :=
  nr_nelsonRegion_of_hyps hm l (nr_smoothHyp hm hl) hL2

end Smooth

end PP2NelsonRegion

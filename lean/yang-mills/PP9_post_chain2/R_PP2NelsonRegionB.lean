import LongTable.R_PP2NelsonRegionA

/-!
Part B of PP2NelsonRegion (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2NelsonRegion.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
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

end Defect

end PP2NelsonRegion

end

import LongTable.R_PP2RoughL2C
import LongTable.P_mwxokm53_4fg2b5
import LongTable.P_mwxoi0q4_2ggzo2

/-!
Part A of PP2RoughL2Region (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2RoughL2Region.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node G4 of the M5
plan (Nelson's bound), session 3, REGION version of step 3, the rough L² bound (namespace
`PP2RoughL2Region`; box version in PP2RoughL2, the region reduction in PP2NelsonRegion).

Target: `PP2NelsonRegion.nr_RoughL2Hyp m₀ l hm` (m₀ ≠ 0, l ≥ 0): ∃ K θ, 0 < θ ∧ ∀ n k x,
∀ T ∈ (0, 1], E_{γ^B⊗γ^B}[R_T²] ≤ K T^θ (B = physBall n k x l), the single remaining input of
`nl_nelsonRegion_of_roughL2`.

Notation as in PP2NelsonRegion: A = rg_scaledOp B = ε² regionOp B, M = mg_modeMat A, λ_K the
eigenvalues of A, τ = ε⁻² T (`nr_τ`), α_K = e^{−τλ_K/2}, β_K = √(1 − e^{−τλ_K});
ℓˢ_{yK} = M_{yK} α_K (`rr_ls`), ℓʳ_{yK} = M_{yK} β_K (`rr_lr`); c_r = `nr_cr`, c₁ = `nr_cs`,
C^B_r(T) = `mg_regionRough`; R = ⌊l/ε⌋ (`nr_rad`), M_B(y) = `nr_M`, L = 2l + 1.
Time normalisation: the split time τ of rg_scaledOp is the physical time ε²τ = T of regionOp
(`mg_region_rough_cov`, via `mg_heat_scaledOp`); `rr_eps_tau`.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* §1 Generic (sites σ, modes ι, any finite types; linear forms ℓˢ, ℓʳ : σ → ι → ℝ, weight w,
  smooth Wick constants cs with Σ_K (ℓˢ_{yK})² ≤ cs(y); rough Wick constants = true variances):
  `rr_S`, `rr_B`, `rr_C` (C(y,y') = Σ_K ℓʳ_{yK} ℓʳ_{y'K}), `rr_R`, `rr_M`, `rr_G`;
  `rr_cov_B` (rough Wick covariance, from `rl_cov`); `rr_R_sq`, **`rr_ER2`** (exact
  E[R²] = w² Σ_{y,y'} Σ_{j<4} C(4,j)² E[S_j(y)S_j(y')] (4−j)! C(y,y')^{4−j}); `rr_E_le`
  (|E[S_j S_j]| ≤ (M(y)+M(y'))/2, from `rl_smooth_sq`); `rr_ER2_le`
  (E[R²] ≤ 96 w² Σ_{y,y'} (M(y)+M(y'))/2 · G(y,y')); **`rr_ER2_bound`** (row sums
  w Σ_{y'} G ≤ K_G s⁴ and w Σ_y s⁴(1+cs)³ ≤ sQ ⇒ E[R²] ≤ 96·15·K_G Q s, via `rl_symm_sum`).
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

/-! ## 1. Generic: second moment of the remainder for linear forms of γ^ι ⊗ γ^ι -/

section Generic

variable {σ ι : Type*} [Fintype σ] [Fintype ι]

/-- γ^ι. -/
abbrev rr_g (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 1)

/-- S_j(y)(ξ) = :⟨ℓˢ_y, ξ⟩^j:_{cs(y)}. -/
def rr_S (cs : σ → ℝ) (ls : σ → ι → ℝ) (j : ℕ) (y : σ) (ξ : ι → ℝ) : ℝ :=
  wickPow (cs y) j (∑ K, ls y K * ξ K)

/-- B_j(y)(ξ) = :⟨ℓʳ_y, ξ⟩^j:_{|ℓʳ_y|²}. -/
def rr_B (lr : σ → ι → ℝ) (j : ℕ) (y : σ) (ξ : ι → ℝ) : ℝ :=
  wickPow (∑ K, lr y K ^ 2) j (∑ K, lr y K * ξ K)

/-- C(y, y') = Σ_K ℓʳ_{yK} ℓʳ_{y'K}. -/
def rr_C (lr : σ → ι → ℝ) (y y' : σ) : ℝ := ∑ K, lr y K * lr y' K

/-- R(ξˢ, ξʳ) = w Σ_y Σ_{j<4} C(4,j) S_j(y)(ξˢ) B_{4−j}(y)(ξʳ). -/
def rr_R (w : ℝ) (cs : σ → ℝ) (ls lr : σ → ι → ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  w * ∑ y, ∑ j ∈ range 4,
    ((Nat.choose 4 j : ℕ) : ℝ) * rr_S cs ls j y p.1 * rr_B lr (4 - j) y p.2

/-- M(y) = 15 (1 + cs(y))³. -/
def rr_M (cs : σ → ℝ) (y : σ) : ℝ := 15 * (1 + cs y) ^ 3

/-- G(y, y') = Σ_{m=1}^4 |C(y, y')|^m. -/
def rr_G (lr : σ → ι → ℝ) (y y' : σ) : ℝ :=
  |rr_C lr y y'| + |rr_C lr y y'| ^ 2 + |rr_C lr y y'| ^ 3 + |rr_C lr y y'| ^ 4

theorem rr_C_symm (lr : σ → ι → ℝ) (y y' : σ) : rr_C lr y y' = rr_C lr y' y :=
  sum_congr rfl fun _ _ => mul_comm _ _

theorem rr_G_symm (lr : σ → ι → ℝ) (y y' : σ) : rr_G lr y y' = rr_G lr y' y := by
  unfold rr_G; rw [rr_C_symm lr y y']

theorem rr_int_S (cs : σ → ℝ) (ls : σ → ι → ℝ) (j j' : ℕ) (y y' : σ) :
    Integrable (fun ξ => rr_S cs ls j y ξ * rr_S cs ls j' y' ξ) (rr_g ι) :=
  rl_int _ _ _ _ _ _

theorem rr_int_B (lr : σ → ι → ℝ) (j j' : ℕ) (y y' : σ) :
    Integrable (fun ξ => rr_B lr j y ξ * rr_B lr j' y' ξ) (rr_g ι) :=
  rl_int _ _ _ _ _ _

theorem rr_int_S_sq (cs : σ → ℝ) (ls : σ → ι → ℝ) (j : ℕ) (y : σ) :
    Integrable (fun ξ => rr_S cs ls j y ξ ^ 2) (rr_g ι) :=
  (rr_int_S cs ls j j y y).congr (ae_of_all _ fun _ => (sq _).symm)

/-- Rough Wick covariance: E[B_a(y) B_b(y')] = δ_ab a! C(y, y')^a (a, b ≤ 4). -/
theorem rr_cov_B (lr : σ → ι → ℝ) {a b : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) (y y' : σ) :
    ∫ ξ, rr_B lr a y ξ * rr_B lr b y' ξ ∂rr_g ι =
      if a = b then (a.factorial : ℝ) * rr_C lr y y' ^ a else 0 := by
  unfold rr_B rr_C
  exact rl_cov _ _ a b ha hb

theorem rr_R_sq (w : ℝ) (cs : σ → ℝ) (ls lr : σ → ι → ℝ) (p : (ι → ℝ) × (ι → ℝ)) :
    rr_R w cs ls lr p ^ 2 = ∑ y, ∑ y', ∑ j ∈ range 4, ∑ j' ∈ range 4,
      w ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rr_S cs ls j y p.1 * rr_S cs ls j' y' p.1) *
          (rr_B lr (4 - j) y p.2 * rr_B lr (4 - j') y' p.2)) := by
  rw [rr_R, sq, mul_mul_mul_comm, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  rw [sum_mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j' _ => ?_
  ring

/-- **Exact second moment of R** (factorisation over γ^ι ⊗ γ^ι, rough orthogonality). -/
theorem rr_ER2 (w : ℝ) (cs : σ → ℝ) (ls lr : σ → ι → ℝ) :
    ∫ p, rr_R w cs ls lr p ^ 2 ∂(rr_g ι).prod (rr_g ι) = ∑ y, ∑ y', ∑ j ∈ range 4,
      w ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((∫ ξ, rr_S cs ls j y ξ * rr_S cs ls j y' ξ ∂rr_g ι) *
          (((4 - j).factorial : ℝ) * rr_C lr y y' ^ (4 - j))) := by
  have hI : ∀ y y' : σ, ∀ j j' : ℕ, Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      w ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rr_S cs ls j y p.1 * rr_S cs ls j' y' p.1) *
          (rr_B lr (4 - j) y p.2 * rr_B lr (4 - j') y' p.2))) ((rr_g ι).prod (rr_g ι)) :=
    fun y y' j j' =>
      ((rr_int_S cs ls j j' y y').mul_prod (rr_int_B lr (4 - j) (4 - j') y y')).const_mul _
  simp_rw [rr_R_sq]
  rw [integral_finsetSum _ fun y _ => integrable_finsetSum _ fun y' _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hI y y' j j']
  refine sum_congr rfl fun y _ => ?_
  rw [integral_finsetSum _ fun y' _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun j' _ => hI y y' j j']
  refine sum_congr rfl fun y' _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hI y y' j j']
  refine sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun j' _ => hI y y' j j']
  have hj4 : j < 4 := mem_range.mp hj
  have hfac : ∀ j' : ℕ, ∫ p : (ι → ℝ) × (ι → ℝ),
      w ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rr_S cs ls j y p.1 * rr_S cs ls j' y' p.1) *
          (rr_B lr (4 - j) y p.2 * rr_B lr (4 - j') y' p.2)) ∂(rr_g ι).prod (rr_g ι) =
      w ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((∫ ξ, rr_S cs ls j y ξ * rr_S cs ls j' y' ξ ∂rr_g ι) *
          (∫ ξ, rr_B lr (4 - j) y ξ * rr_B lr (4 - j') y' ξ ∂rr_g ι)) := by
    intro j'
    rw [integral_const_mul]
    exact congrArg _ (integral_prod_mul (L := ℝ) (μ := rr_g ι) (ν := rr_g ι)
      (fun ξ => rr_S cs ls j y ξ * rr_S cs ls j' y' ξ)
      (fun ξ => rr_B lr (4 - j) y ξ * rr_B lr (4 - j') y' ξ))
  rw [Finset.sum_eq_single j]
  · rw [hfac, rr_cov_B lr (by omega) (by omega), ite_eq_left rfl]
  · intro j' hj' hne
    have hj'4 : j' < 4 := mem_range.mp hj'
    rw [hfac, rr_cov_B lr (by omega) (by omega), ite_eq_right (by omega)]
    ring
  · intro h; exact absurd hj h

theorem rr_cs_nonneg {cs : σ → ℝ} {ls : σ → ι → ℝ} (hcs : ∀ y, ∑ K, ls y K ^ 2 ≤ cs y) (y : σ) :
    0 ≤ cs y :=
  (sum_nonneg fun _ _ => sq_nonneg _).trans (hcs y)

theorem rr_M_nonneg {cs : σ → ℝ} {ls : σ → ι → ℝ} (hcs : ∀ y, ∑ K, ls y K ^ 2 ≤ cs y) (y : σ) :
    0 ≤ rr_M cs y := by
  have := rr_cs_nonneg hcs y
  unfold rr_M; positivity

/-- Mis-ordered smooth covariances: |E[S_j(y) S_j(y')]| ≤ (M(y) + M(y'))/2 (j ≤ 3). -/
theorem rr_E_le {cs : σ → ℝ} {ls : σ → ι → ℝ} (hcs : ∀ y, ∑ K, ls y K ^ 2 ≤ cs y) {j : ℕ}
    (hj : j ≤ 3) (y y' : σ) :
    |∫ ξ, rr_S cs ls j y ξ * rr_S cs ls j y' ξ ∂rr_g ι| ≤ (rr_M cs y + rr_M cs y') / 2 := by
  refine (rl_abs_int_mul_le (rr_int_S cs ls j j y y') (rr_int_S_sq cs ls j y)
    (rr_int_S_sq cs ls j y')).trans ?_
  have h1 : ∫ ξ, rr_S cs ls j y ξ ^ 2 ∂rr_g ι ≤ rr_M cs y := rl_smooth_sq (ls y) (hcs y) hj
  have h2 : ∫ ξ, rr_S cs ls j y' ξ ^ 2 ∂rr_g ι ≤ rr_M cs y' := rl_smooth_sq (ls y') (hcs y') hj
  linarith

theorem rr_ER2_le (w : ℝ) {cs : σ → ℝ} {ls : σ → ι → ℝ} (hcs : ∀ y, ∑ K, ls y K ^ 2 ≤ cs y)
    (lr : σ → ι → ℝ) :
    ∫ p, rr_R w cs ls lr p ^ 2 ∂(rr_g ι).prod (rr_g ι) ≤
      96 * w ^ 2 * ∑ y, ∑ y', (rr_M cs y + rr_M cs y') / 2 * rr_G lr y y' := by
  rw [rr_ER2, mul_sum]
  refine sum_le_sum fun y _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun y' _ => ?_
  have hW0 : 0 ≤ (rr_M cs y + rr_M cs y') / 2 := by
    have := rr_M_nonneg hcs y; have := rr_M_nonneg hcs y'; positivity
  have hterm : ∀ j ∈ range 4,
      w ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((∫ ξ, rr_S cs ls j y ξ * rr_S cs ls j y' ξ ∂rr_g ι) *
          (((4 - j).factorial : ℝ) * rr_C lr y y' ^ (4 - j))) ≤
      w ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((rr_M cs y + rr_M cs y') / 2 *
          (((4 - j).factorial : ℝ) * |rr_C lr y y'| ^ (4 - j))) := by
    intro j hj
    have hj3 : j ≤ 3 := by simp at hj; omega
    have hE := rr_E_le hcs hj3 y y'
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hf : (0 : ℝ) ≤ ((4 - j).factorial : ℝ) := by positivity
    calc (∫ ξ, rr_S cs ls j y ξ * rr_S cs ls j y' ξ ∂rr_g ι) *
          (((4 - j).factorial : ℝ) * rr_C lr y y' ^ (4 - j))
        ≤ |(∫ ξ, rr_S cs ls j y ξ * rr_S cs ls j y' ξ ∂rr_g ι) *
          (((4 - j).factorial : ℝ) * rr_C lr y y' ^ (4 - j))| := le_abs_self _
      _ = |∫ ξ, rr_S cs ls j y ξ * rr_S cs ls j y' ξ ∂rr_g ι| *
          (((4 - j).factorial : ℝ) * |rr_C lr y y'| ^ (4 - j)) := by
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hf]
      _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)
  refine (sum_le_sum hterm).trans ?_
  simp only [sum_range_succ, sum_range_zero, zero_add, rr_G]
  norm_num [Nat.choose, Nat.factorial]
  have hA := abs_nonneg (rr_C lr y y')
  have hX : 0 ≤ w ^ 2 * ((rr_M cs y + rr_M cs y') / 2) := by positivity
  nlinarith [mul_nonneg hX hA, mul_nonneg hX (pow_nonneg hA 2), mul_nonneg hX (pow_nonneg hA 3),
    mul_nonneg hX (pow_nonneg hA 4)]

/-- **Generic rough L² bound from the row-sum and site-sum estimates.** -/
theorem rr_ER2_bound {w : ℝ} (hw : 0 ≤ w) {cs : σ → ℝ} {ls : σ → ι → ℝ}
    (hcs : ∀ y, ∑ K, ls y K ^ 2 ≤ cs y) (lr : σ → ι → ℝ) {KG s Q : ℝ} (hKG : 0 ≤ KG)
    (hG : ∀ y, w * ∑ y', rr_G lr y y' ≤ KG * s ^ 4)
    (hS : w * ∑ y, s ^ 4 * (1 + cs y) ^ 3 ≤ s * Q) :
    ∫ p, rr_R w cs ls lr p ^ 2 ∂(rr_g ι).prod (rr_g ι) ≤ 96 * KG * 15 * Q * s := by
  calc ∫ p, rr_R w cs ls lr p ^ 2 ∂(rr_g ι).prod (rr_g ι)
      ≤ 96 * w ^ 2 * ∑ y, ∑ y', (rr_M cs y + rr_M cs y') / 2 * rr_G lr y y' :=
        rr_ER2_le w hcs lr
    _ = 96 * w * ∑ y, rr_M cs y * (w * ∑ y', rr_G lr y y') := by
        rw [rl_symm_sum _ _ (rr_G_symm lr), mul_sum, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ ≤ 96 * w * ∑ y, rr_M cs y * (KG * s ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hG y) (rr_M_nonneg hcs y)
    _ = 96 * KG * 15 * (w * ∑ y, s ^ 4 * (1 + cs y) ^ 3) := by
        simp only [rr_M, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ ≤ 96 * KG * 15 * (s * Q) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 96 * KG * 15 * Q * s := by ring

end Generic

/-! ## 2. The region: φ_s, φ_r as linear forms and their covariances -/

section Region

variable {n k : ℕ}

/-- ℓˢ_{yK} = M_{yK} α_K (A = rg_scaledOp B, τ = ε⁻² T). -/
def rr_ls {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (T : ℝ) (y K : {z // z ∈ B}) : ℝ :=
  mg_modeMat (rg_scaledOp_posDef hm B) y K * nr_α (rg_scaledOp_posDef hm B) (nr_τ n T) K

/-- ℓʳ_{yK} = M_{yK} β_K. -/
def rr_lr {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (T : ℝ) (y K : {z // z ∈ B}) : ℝ :=
  mg_modeMat (rg_scaledOp_posDef hm B) y K * nr_β (rg_scaledOp_posDef hm B) (nr_τ n T) K

theorem rr_φs_eq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (T : ℝ)
    (ξ : {z // z ∈ B} → ℝ) (y : {z // z ∈ B}) :
    nr_φs (rg_scaledOp_posDef hm B) (nr_τ n T) ξ y = ∑ K, rr_ls hm B T y K * ξ K := by
  simp only [nr_φs, mulVec, dotProduct, rr_ls]
  exact sum_congr rfl fun K _ => by ring

theorem rr_φr_eq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (T : ℝ)
    (ξ : {z // z ∈ B} → ℝ) (y : {z // z ∈ B}) :
    nr_φr (rg_scaledOp_posDef hm B) (nr_τ n T) ξ y = ∑ K, rr_lr hm B T y K * ξ K := by
  simp only [nr_φr, mulVec, dotProduct, rr_lr]
  exact sum_congr rfl fun K _ => by ring

/-- Time normalisation: ε² τ = T for τ = nr_τ n T. -/
theorem rr_eps_tau (n : ℕ) (T : ℝ) : spacing n ^ 2 * nr_τ n T = T := by
  rw [nr_τ, mul_inv_cancel_left₀ (pow_ne_zero 2 (spacing_pos n).ne')]

theorem rr_tau_nonneg (n : ℕ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ nr_τ n T := by
  unfold nr_τ; positivity

theorem rr_α_sq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (τ : ℝ) (K : {z // z ∈ B}) :
    nr_α (rg_scaledOp_posDef hm B) τ K * nr_α (rg_scaledOp_posDef hm B) τ K =
      Real.exp (-(τ * (rg_scaledOp_posDef hm B).1.eigenvalues K)) := by
  unfold nr_α
  rw [← Real.exp_add]
  congr 1
  ring

theorem rr_β_sq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) {τ : ℝ} (hτ : 0 ≤ τ)
    (K : {z // z ∈ B}) :
    nr_β (rg_scaledOp_posDef hm B) τ K * nr_β (rg_scaledOp_posDef hm B) τ K =
      1 - Real.exp (-(τ * (rg_scaledOp_posDef hm B).1.eigenvalues K)) := by
  unfold nr_β
  refine Real.mul_self_sqrt ?_
  have h := mul_nonneg hτ ((rg_scaledOp_posDef hm B).eigenvalues_pos K).le
  have : Real.exp (-(τ * (rg_scaledOp_posDef hm B).1.eigenvalues K)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  linarith

end Region

end PP2RoughL2Region

end

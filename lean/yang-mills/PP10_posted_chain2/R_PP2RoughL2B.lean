import LongTable.R_PP2RoughL2A

/-!
Part B of PP2RoughL2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2RoughL2.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* §2, `rl_sq_comb`, `rl_smooth_sq`: if |u|² ≤ c and j ≤ 3, E[(:⟨u,ξ⟩^j:_c)²] ≤ 15 (1 + c)³
  (re-ordering :X^j:_c = :X^j:_s − binomial terms in δ = c − s ≥ 0, then `rl_cov`);
  `rl_abs_int_mul_le`: |E fg| ≤ (E f² + E g²)/2.
* §3, box covariances: `rl_φs_eq`, `rl_φr_eq` (φ_s, φ_r as linear forms); `rl_lr_cov`
  (Σ_K ℓʳ_{yK} ℓʳ_{y'K} = C_r(T)(y, y'), via `glp_roughCov_spectral`); `rl_cr_eq` (c_r(y) = Var φ_r(y));
  `rl_ls_var` (Var φ_s(y) = ε⁻² dirGreen y y − c_r(y), via `dirGreen_spectral`); `rl_ls_var_le`
  (Var φ_s(y) ≤ c₁(y), the gap being the Wick defect ≥ 0 by `dirVar_le_freeVar`); `rl_roughCov_symm`.
* §4, (a)+(b)+(c): `rl_cov_B` (**the rough Wick covariance at the true rough variances**,
  E[B_a(y) B_b(y')] = δ_ab a! C_r(y,y')^a, a, b ≤ 4, T ≥ 0); `rl_Rω_sq`, `rl_ER2` (exact formula
  E[R_T²] = ε⁴ Σ_{y,y'} Σ_{j<4} C(4,j)² E[S_j(y)S_j(y')] (4−j)! C_r(y,y')^{4−j}, by factorisation
  over the product measure and rough orthogonality); `rl_E_le` (|E[S_j(y)S_j(y')]| ≤ (M(y)+M(y'))/2,
  M = 15(1+c₁)³ = `rl_M`); `rl_ER2_le` (E[R_T²] ≤ 96 ε⁴ Σ_{y,y'} (M(y)+M(y'))/2 · G(y,y'),
  G = Σ_{m=1}^4 |C_r|^m = `rl_G`).

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

section Generic

variable {ι : Type*} [Fintype ι]

/-- **Mis-ordered Wick powers, second moment** (j ≤ 3): if X = ⟨u, ξ⟩ has variance
s = |u|² ≤ c, then E[(:X^j:_c)²] ≤ 15 (1 + c)³ (via :X^j:_c = :X^j:_s − binomial lower terms
with δ = c − s ≥ 0, and `rl_cov`). -/
theorem rl_smooth_sq (u : ι → ℝ) {c : ℝ} (hc : ∑ i, u i ^ 2 ≤ c) {j : ℕ} (hj : j ≤ 3) :
    ∫ ξ, (wickPow c j (∑ i, u i * ξ i)) ^ 2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1) ≤
      15 * (1 + c) ^ 3 := by
  have hs0 : 0 ≤ ∑ i, u i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hss : ∑ i, u i * u i = ∑ i, u i ^ 2 := by simp [sq]
  have hc0 : 0 ≤ c := hs0.trans hc
  have hc3 : 1 + 3 * c + 3 * c ^ 2 + c ^ 3 = (1 + c) ^ 3 := by ring
  have hcc : 0 ≤ c ^ 2 := sq_nonneg c
  have hccc : 0 ≤ c ^ 3 := pow_nonneg hc0 3
  set s := ∑ i, u i ^ 2 with hsdef
  interval_cases j
  · simp only [wickPow_zero', one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith
  · have e : ∀ ξ : ι → ℝ, wickPow c 1 (∑ i, u i * ξ i) ^ 2 =
        wickPow (∑ i, u i ^ 2) 1 (∑ i, u i * ξ i) * wickPow (∑ i, u i ^ 2) 1 (∑ i, u i * ξ i) := by
      intro ξ; simp only [wickPow_one, sq]
    simp_rw [e]
    rw [rl_cov u u 1 1 (by norm_num) (by norm_num)]
    simp only [ite_true, Nat.factorial_one, Nat.cast_one, pow_one, one_mul, hss]
    nlinarith
  · have e : ∀ ξ : ι → ℝ, wickPow c 2 (∑ i, u i * ξ i) ^ 2 =
        (wickPow (∑ i, u i ^ 2) 2 (∑ i, u i * ξ i) -
          (c - s) * wickPow (∑ i, u i ^ 2) 0 (∑ i, u i * ξ i)) ^ 2 := by
      intro ξ; simp only [wickPow_two, wickPow_zero']; ring
    simp_rw [e]
    rw [rl_sq_comb u (by norm_num) (by norm_num) (by norm_num)]
    simp only [Nat.factorial, Nat.cast_one, pow_zero, mul_one, Nat.succ_eq_add_one, zero_add]
    have h1 : s ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hs0 hc 2
    have h2 : (c - s) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    norm_num
    nlinarith
  · have e : ∀ ξ : ι → ℝ, wickPow c 3 (∑ i, u i * ξ i) ^ 2 =
        (wickPow (∑ i, u i ^ 2) 3 (∑ i, u i * ξ i) -
          (3 * (c - s)) * wickPow (∑ i, u i ^ 2) 1 (∑ i, u i * ξ i)) ^ 2 := by
      intro ξ; simp only [wickPow_three, wickPow_one]; ring
    simp_rw [e]
    rw [rl_sq_comb u (by norm_num) (by norm_num) (by norm_num)]
    have h1 : s ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hs0 hc 3
    have h2 : (c - s) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h3 : (c - s) ^ 2 * s ≤ c ^ 2 * c := mul_le_mul h2 hc hs0 hcc
    norm_num [Nat.factorial]
    nlinarith

end Generic

/-- |E[fg]| ≤ (E f² + E g²)/2. -/
theorem rl_abs_int_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hfg : Integrable (fun x => f x * g x) μ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) :
    |∫ x, f x * g x ∂μ| ≤ ((∫ x, f x ^ 2 ∂μ) + ∫ x, g x ^ 2 ∂μ) / 2 := by
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_add hf hg, ← integral_div]
  refine integral_mono hfg.abs ((hf.add hg).div_const 2) fun x => ?_
  rw [abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]


/-! ## 3. The box: φ_s, φ_r as linear forms of (ξˢ, ξʳ) and their covariances -/

variable {n k : ℕ}

theorem rl_φs_eq (m₀ T : ℝ) (ξ : DField n k) (y : DSite n k) :
    nl_φs n k m₀ T ξ y = ∑ K, nl_ls n k m₀ T y K * ξ K := by
  rw [nl_φs, md_map_apply, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  rw [nl_ls]; ring

theorem rl_φr_eq (m₀ T : ℝ) (ξ : DField n k) (y : DSite n k) :
    nl_φr n k m₀ T ξ y = ∑ K, nl_lr n k m₀ T y K * ξ K := by
  rw [nl_φr, md_map_apply, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  rw [nl_lr]; ring

theorem rl_one_sub_exp_nonneg (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (K : DSite n k) :
    0 ≤ 1 - Real.exp (-(T * dirEig n k m₀ K)) := by
  have h := mul_nonneg hT (dirEig_pos (n := n) (k := k) m₀ K).le
  have : Real.exp (-(T * dirEig n k m₀ K)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem rl_inv_sqrt_sq (m₀ : ℝ) (K : DSite n k) :
    (√(dirEig n k m₀ K))⁻¹ * (√(dirEig n k m₀ K))⁻¹ = (dirEig n k m₀ K)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (dirEig_pos m₀ K).le]

/-- Cov(φ_r(y), φ_r(y')) = Σ_K ℓʳ_{yK} ℓʳ_{y'K} = C_r(T)(y, y') (T ≥ 0). -/
theorem rl_lr_cov (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y y' : DSite n k) :
    ∑ K, nl_lr n k m₀ T y K * nl_lr n k m₀ T y' K = glp_roughCov n k m₀ T y y' := by
  rw [glp_roughCov_spectral m₀ hT, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  have h1 := Real.mul_self_sqrt (rl_one_sub_exp_nonneg (n := n) (k := k) m₀ hT K)
  have h2 := rl_inv_sqrt_sq (n := n) (k := k) m₀ K
  calc nl_lr n k m₀ T y K * nl_lr n k m₀ T y' K
      = ((spacing n)⁻¹ * (spacing n)⁻¹) * ((√(dirEig n k m₀ K))⁻¹ * (√(dirEig n k m₀ K))⁻¹) *
          (√(1 - Real.exp (-(T * dirEig n k m₀ K))) * √(1 - Real.exp (-(T * dirEig n k m₀ K)))) *
          (sineVec2 K y * sineVec2 K y') := by unfold nl_lr; ring
    _ = _ := by rw [h1, h2, div_eq_mul_inv]; ring

/-- c_r(y) = Var φ_r(y) = Σ_K (ℓʳ_{yK})². -/
theorem rl_cr_eq (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    nl_cr n k m₀ T y = ∑ K, nl_lr n k m₀ T y K ^ 2 := by
  rw [nl_cr, ← rl_lr_cov m₀ hT]; simp only [sq]

/-- Var φ_s(y) = Σ_K (ℓˢ_{yK})² = ε⁻² dirGreen y y − c_r(y). -/
theorem rl_ls_var (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    ∑ K, nl_ls n k m₀ T y K ^ 2 = (spacing n ^ 2)⁻¹ * dirGreen n k m₀ y y - nl_cr n k m₀ T y := by
  rw [nl_cr, ← rl_lr_cov m₀ hT, dirGreen_spectral, mul_sum, eq_sub_iff_add_eq, ← sum_add_distrib]
  refine sum_congr rfl fun K _ => ?_
  have h1 := Real.mul_self_sqrt (rl_one_sub_exp_nonneg (n := n) (k := k) m₀ hT K)
  have h2 := rl_inv_sqrt_sq (n := n) (k := k) m₀ K
  have h3 : Real.exp (-(T * dirEig n k m₀ K) / 2) ^ 2 = Real.exp (-(T * dirEig n k m₀ K)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  calc nl_ls n k m₀ T y K ^ 2 + nl_lr n k m₀ T y K * nl_lr n k m₀ T y K
      = ((spacing n)⁻¹ * (spacing n)⁻¹) * ((√(dirEig n k m₀ K))⁻¹ * (√(dirEig n k m₀ K))⁻¹) *
          (Real.exp (-(T * dirEig n k m₀ K) / 2) ^ 2 +
            √(1 - Real.exp (-(T * dirEig n k m₀ K))) * √(1 - Real.exp (-(T * dirEig n k m₀ K)))) *
          (sineVec2 K y * sineVec2 K y) := by unfold nl_ls nl_lr; ring
    _ = _ := by rw [h1, h2, h3, div_eq_mul_inv]; ring

/-- Var φ_s(y) ≤ c₁(y) (the difference is the Wick defect b(y) = freeVar − ε⁻² dirGreen y y ≥ 0). -/
theorem rl_ls_var_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    ∑ K, nl_ls n k m₀ T y K ^ 2 ≤ nl_cs n k m₀ T y := by
  rw [rl_ls_var m₀ hT, nl_cs]
  linarith [dirVar_le_freeVar hm y]

theorem rl_cs_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    0 ≤ nl_cs n k m₀ T y :=
  (sum_nonneg fun _ _ => sq_nonneg _).trans (rl_ls_var_le hm hT y)

theorem rl_roughCov_symm (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y y' : DSite n k) :
    glp_roughCov n k m₀ T y y' = glp_roughCov n k m₀ T y' y := by
  rw [← rl_lr_cov m₀ hT, ← rl_lr_cov m₀ hT]
  exact sum_congr rfl fun K _ => mul_comm _ _

/-! ## 4. E[R_T²]: factorisation, rough orthogonality, smooth Cauchy–Schwarz -/

/-- S_j(y)(ξˢ) = :φ_s(y)^j:_{c₁(y)}. -/
def rl_S (n k : ℕ) (m₀ T : ℝ) (j : ℕ) (y : DSite n k) (ξ : DField n k) : ℝ :=
  wickPow (nl_cs n k m₀ T y) j (∑ K, nl_ls n k m₀ T y K * ξ K)

/-- B_j(y)(ξʳ) = :φ_r(y)^j:_{c_r(y)}. -/
def rl_B (n k : ℕ) (m₀ T : ℝ) (j : ℕ) (y : DSite n k) (ξ : DField n k) : ℝ :=
  wickPow (nl_cr n k m₀ T y) j (∑ K, nl_lr n k m₀ T y K * ξ K)

theorem rl_int_S (m₀ T : ℝ) (j j' : ℕ) (y y' : DSite n k) :
    Integrable (fun ξ => rl_S n k m₀ T j y ξ * rl_S n k m₀ T j' y' ξ) (nl_gauss n k) :=
  rl_int _ _ _ _ _ _

theorem rl_int_B (m₀ T : ℝ) (j j' : ℕ) (y y' : DSite n k) :
    Integrable (fun ξ => rl_B n k m₀ T j y ξ * rl_B n k m₀ T j' y' ξ) (nl_gauss n k) :=
  rl_int _ _ _ _ _ _

theorem rl_int_S_sq (m₀ T : ℝ) (j : ℕ) (y : DSite n k) :
    Integrable (fun ξ => rl_S n k m₀ T j y ξ ^ 2) (nl_gauss n k) :=
  (rl_int_S m₀ T j j y y).congr (ae_of_all _ fun _ => (sq _).symm)

/-- **(b) Rough Wick covariance at the true rough variances:**
E[:φ_r(y)^a:_{c_r(y)} :φ_r(y')^b:_{c_r(y')}] = δ_ab a! C_r(T)(y, y')^a (a, b ≤ 4, T ≥ 0). -/
theorem rl_cov_B (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {a b : ℕ} (ha : a ≤ 4) (hb : b ≤ 4)
    (y y' : DSite n k) :
    ∫ ξ, rl_B n k m₀ T a y ξ * rl_B n k m₀ T b y' ξ ∂nl_gauss n k =
      if a = b then (a.factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ a else 0 := by
  unfold rl_B
  rw [rl_cr_eq m₀ hT y, rl_cr_eq m₀ hT y', ← rl_lr_cov m₀ hT y y']
  exact rl_cov _ _ a b ha hb

theorem rl_Rω_sq (m₀ T : ℝ) (p : DField n k × DField n k) :
    nl_Rω n k m₀ T p ^ 2 = ∑ y, ∑ y', ∑ j ∈ range 4, ∑ j' ∈ range 4,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rl_S n k m₀ T j y p.1 * rl_S n k m₀ T j' y' p.1) *
          (rl_B n k m₀ T (4 - j) y p.2 * rl_B n k m₀ T (4 - j') y' p.2)) := by
  have hR : nl_Rω n k m₀ T p = spacing n ^ 2 * ∑ y, ∑ j ∈ range 4,
      ((Nat.choose 4 j : ℕ) : ℝ) * rl_S n k m₀ T j y p.1 * rl_B n k m₀ T (4 - j) y p.2 := by
    simp only [nl_Rω, nl_R, rl_S, rl_B, rl_φs_eq, rl_φr_eq]
  rw [hR, sq, mul_mul_mul_comm, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  rw [sum_mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j' _ => ?_
  ring

/-- **(a)+(b): exact second moment of R_T.** Factorisation over γ^Λ ⊗ γ^Λ and rough
orthogonality (only j = j' survives):
E[R_T²] = ε⁴ Σ_{y,y'} Σ_{j<4} C(4,j)² E[S_j(y) S_j(y')] (4−j)! C_r(y,y')^{4−j}. -/
theorem rl_ER2 (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k = ∑ y, ∑ y', ∑ j ∈ range 4,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))) := by
  have hI : ∀ y y' : DSite n k, ∀ j j' : ℕ, Integrable (fun p : DField n k × DField n k =>
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rl_S n k m₀ T j y p.1 * rl_S n k m₀ T j' y' p.1) *
          (rl_B n k m₀ T (4 - j) y p.2 * rl_B n k m₀ T (4 - j') y' p.2))) (nl_P n k) :=
    fun y y' j j' =>
      ((rl_int_S m₀ T j j' y y').mul_prod (rl_int_B m₀ T (4 - j) (4 - j') y y')).const_mul _
  simp_rw [rl_Rω_sq]
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
  have hfac : ∀ j' : ℕ, ∫ p : DField n k × DField n k,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rl_S n k m₀ T j y p.1 * rl_S n k m₀ T j' y' p.1) *
          (rl_B n k m₀ T (4 - j) y p.2 * rl_B n k m₀ T (4 - j') y' p.2)) ∂nl_P n k =
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j' y' ξ ∂nl_gauss n k) *
          (∫ ξ, rl_B n k m₀ T (4 - j) y ξ * rl_B n k m₀ T (4 - j') y' ξ ∂nl_gauss n k)) := by
    intro j'
    rw [integral_const_mul, nl_P]
    exact congrArg _ (integral_prod_mul (L := ℝ) (μ := nl_gauss n k) (ν := nl_gauss n k)
      (fun ξ => rl_S n k m₀ T j y ξ * rl_S n k m₀ T j' y' ξ)
      (fun ξ => rl_B n k m₀ T (4 - j) y ξ * rl_B n k m₀ T (4 - j') y' ξ))
  rw [Finset.sum_eq_single j]
  · rw [hfac, rl_cov_B m₀ hT (by omega) (by omega), ite_eq_left rfl]
  · intro j' hj' hne
    have hj'4 : j' < 4 := mem_range.mp hj'
    rw [hfac, rl_cov_B m₀ hT (by omega) (by omega), ite_eq_right (by omega)]
    ring
  · intro h; exact absurd hj h

/-- M(y) = 15 (1 + c₁(y))³, the bound on E[S_j(y)²] (j ≤ 3). -/
def rl_M (n k : ℕ) (m₀ T : ℝ) (y : DSite n k) : ℝ := 15 * (1 + nl_cs n k m₀ T y) ^ 3

/-- G(y, y') = Σ_{m=1}^4 |C_r(y, y')|^m. -/
def rl_G (n k : ℕ) (m₀ T : ℝ) (y y' : DSite n k) : ℝ :=
  |glp_roughCov n k m₀ T y y'| + |glp_roughCov n k m₀ T y y'| ^ 2 +
    |glp_roughCov n k m₀ T y y'| ^ 3 + |glp_roughCov n k m₀ T y y'| ^ 4

theorem rl_M_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    0 ≤ rl_M n k m₀ T y := by
  have := rl_cs_nonneg hm hT y
  unfold rl_M; positivity

theorem rl_G_symm (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y y' : DSite n k) :
    rl_G n k m₀ T y y' = rl_G n k m₀ T y' y := by
  unfold rl_G; rw [rl_roughCov_symm m₀ hT y y']

/-- **(c) Mis-ordered smooth covariances:** |E[S_j(y) S_j(y')]| ≤ (M(y) + M(y'))/2 (j ≤ 3). -/
theorem rl_E_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) {j : ℕ} (hj : j ≤ 3)
    (y y' : DSite n k) :
    |∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k| ≤
      (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 := by
  refine (rl_abs_int_mul_le (rl_int_S m₀ T j j y y') (rl_int_S_sq m₀ T j y)
    (rl_int_S_sq m₀ T j y')).trans ?_
  have h1 : ∫ ξ, rl_S n k m₀ T j y ξ ^ 2 ∂nl_gauss n k ≤ rl_M n k m₀ T y :=
    rl_smooth_sq (nl_ls n k m₀ T y) (rl_ls_var_le hm hT y) hj
  have h2 : ∫ ξ, rl_S n k m₀ T j y' ξ ^ 2 ∂nl_gauss n k ≤ rl_M n k m₀ T y' :=
    rl_smooth_sq (nl_ls n k m₀ T y') (rl_ls_var_le hm hT y') hj
  linarith

theorem rl_ER2_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k ≤
      96 * (spacing n ^ 2) ^ 2 * ∑ y, ∑ y',
        (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 * rl_G n k m₀ T y y' := by
  rw [rl_ER2 m₀ hT, mul_sum]
  refine sum_le_sum fun y _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun y' _ => ?_
  have hW0 : 0 ≤ (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 := by
    have := rl_M_nonneg hm hT y; have := rl_M_nonneg hm hT y'; positivity
  have hterm : ∀ j ∈ range 4,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))) ≤
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 *
          (((4 - j).factorial : ℝ) * |glp_roughCov n k m₀ T y y'| ^ (4 - j))) := by
    intro j hj
    have hj3 : j ≤ 3 := by simp at hj; omega
    have hE := rl_E_le hm hT hj3 y y'
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hf : (0 : ℝ) ≤ ((4 - j).factorial : ℝ) := by positivity
    calc (∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))
        ≤ |(∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))| := le_abs_self _
      _ = |∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k| *
          (((4 - j).factorial : ℝ) * |glp_roughCov n k m₀ T y y'| ^ (4 - j)) := by
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hf]
      _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)
  refine (sum_le_sum hterm).trans ?_
  simp only [sum_range_succ, sum_range_zero, zero_add, rl_G]
  norm_num [Nat.choose, Nat.factorial]
  have hA := abs_nonneg (glp_roughCov n k m₀ T y y')
  have hX : 0 ≤ (spacing n ^ 2) ^ 2 * ((rl_M n k m₀ T y + rl_M n k m₀ T y') / 2) := by
    positivity
  nlinarith [mul_nonneg hX hA, mul_nonneg hX (pow_nonneg hA 2), mul_nonneg hX (pow_nonneg hA 3),
    mul_nonneg hX (pow_nonneg hA 4)]

end PP2RoughL2

end

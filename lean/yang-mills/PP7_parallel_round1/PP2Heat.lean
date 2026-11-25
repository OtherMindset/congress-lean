import LongTable.PP2Sine

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5b, session 1.
Heat kernel of the Dirichlet operator `dirOp` on the box (namespace `PP2Target`), for Nelson's
covariance split.

Notation: N = `boxN n k` = 2^(n+k), M = N + 1, ε = `spacing n` = 2^(−n), e_K = `sineVec2 K`,
λ_K = `dirEig n k m₀ K` = ε⁻²(sineEig K₁ + sineEig K₂) + m₀². The heat kernel is
`heatK n k m₀ t x y = Σ_K e_K(x) e_K(y) exp(−t λ_K)` (t in physical time units, t ≥ 0 intended,
defined for all real t). The 1-D diagonal factor is
`heat1 N τ i = Σ_j e_j(i)² exp(−τ sineEig N j)` (τ = t/ε² in lattice time units).

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `heatK_symm`: p_t(x, y) = p_t(y, x).
* `heatK_diag_nonneg`: 0 ≤ p_t(x, x).
* `heatK_semigroup`: Σ_z p_t(x, z) p_s(z, y) = p_{t+s}(x, y) (any real t, s).
* `heatK_sq_sum`: Σ_y p_t(x, y)² = p_{2t}(x, x).
* `integral_heatK`: ∫_{t ∈ (0,∞)} p_t(x, y) dt = dirGreen x y (any m₀, via `dirGreen_spectral`).
* `heatK_diag_eq`: p_t(x, x) = e^{−t m₀²} · heat1 N (t/ε²) x₁ · heat1 N (t/ε²) x₂.
* `sineVec_sq_le`: e_j(i)² ≤ 2/(N+1); `sineEig_ge`: sineEig N j ≥ 4((j+1)/(N+1))² (Jordan).
* `gauss_sum_le`: Σ_{j=1}^N e^{−a j²} ≤ √(π/a)/2 for a > 0 (sum ≤ Gaussian integral).
* `heat1_le`: heat1 N τ i ≤ √(π/(4τ)) for τ > 0, uniform in N, i (the factor M cancels).
* `heatK_diag_le` (key bound): for t > 0, ε⁻² p_t(x, x) ≤ π/(4t), with the constant π/4
  independent of n, k, x, m₀ (the mass factor e^{−t m₀²} ≤ 1 is simply dropped).

NOT formalized here: off-diagonal bounds (|p_t(x,y)| ≤ √(p_t(x,x) p_t(y,y)) follows from
`heatK_semigroup` + Cauchy–Schwarz but is not stated), the improved bound with e^{−t m₀²}
retained, positivity p_t(x, y) ≥ 0 off the diagonal, Gaussian (Davies) off-diagonal decay,
and the Nelson covariance split C = ∫₀^T + ∫_T^∞ itself.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset MeasureTheory Set

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## The heat kernel and its algebraic properties -/

/-- The heat kernel of `dirOp`: p_t(x, y) = Σ_K e_K(x) e_K(y) exp(−t λ_K). -/
def heatK (n k : ℕ) (m₀ t : ℝ) (x y : DSite n k) : ℝ :=
  ∑ K : DSite n k, sineVec2 K x * sineVec2 K y * exp (-(t * dirEig n k m₀ K))

theorem heatK_symm (m₀ t : ℝ) (x y : DSite n k) : heatK n k m₀ t x y = heatK n k m₀ t y x := by
  unfold heatK
  exact Finset.sum_congr rfl fun K _ => by ring

theorem heatK_diag_nonneg (m₀ t : ℝ) (x : DSite n k) : 0 ≤ heatK n k m₀ t x x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_self_nonneg _) (exp_pos _).le

/-- **Semigroup property:** Σ_z p_t(x, z) p_s(z, y) = p_{t+s}(x, y). -/
theorem heatK_semigroup (m₀ t s : ℝ) (x y : DSite n k) :
    ∑ z, heatK n k m₀ t x z * heatK n k m₀ s z y = heatK n k m₀ (t + s) x y := by
  unfold heatK
  calc ∑ z, (∑ K, sineVec2 K x * sineVec2 K z * exp (-(t * dirEig n k m₀ K))) *
        (∑ L, sineVec2 L z * sineVec2 L y * exp (-(s * dirEig n k m₀ L)))
      = ∑ K, ∑ L, (sineVec2 K x * exp (-(t * dirEig n k m₀ K)) * sineVec2 L y *
          exp (-(s * dirEig n k m₀ L))) * ∑ z, sineVec2 K z * sineVec2 L z := by
        simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun L _ => ?_
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
    _ = ∑ K, sineVec2 K x * sineVec2 K y * exp (-((t + s) * dirEig n k m₀ K)) := by
        simp_rw [sineVec2_orthonormal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [show -((t + s) * dirEig n k m₀ K) = -(t * dirEig n k m₀ K) + -(s * dirEig n k m₀ K)
          by ring, exp_add]
        ring

/-- Σ_y p_t(x, y)² = p_{2t}(x, x). -/
theorem heatK_sq_sum (m₀ t : ℝ) (x : DSite n k) :
    ∑ y, heatK n k m₀ t x y ^ 2 = heatK n k m₀ (2 * t) x x := by
  rw [two_mul, ← heatK_semigroup]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sq, heatK_symm m₀ t y x]

/-! ## Time integral: ∫₀^∞ p_t dt = dirGreen -/

theorem integral_exp_neg_mul_Ioi {l : ℝ} (hl : 0 < l) :
    ∫ t in Ioi (0 : ℝ), exp (-(t * l)) = l⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -l) (by linarith) 0
  simp only [mul_zero, exp_zero] at h
  rw [show (fun t : ℝ => exp (-(t * l))) = fun t => exp (-l * t) by funext t; ring_nf, h]
  field_simp

theorem integrableOn_exp_neg_mul_Ioi {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun t : ℝ => exp (-(t * l))) (Ioi 0) := by
  rw [show (fun t : ℝ => exp (-(t * l))) = fun t => exp (-l * t) by funext t; ring_nf]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

/-- **∫₀^∞ p_t(x, y) dt = dirGreen x y.** -/
theorem integral_heatK (m₀ : ℝ) (x y : DSite n k) :
    ∫ t in Ioi (0 : ℝ), heatK n k m₀ t x y = dirGreen n k m₀ x y := by
  rw [dirGreen_spectral]
  unfold heatK
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun K _ => ?_
    rw [integral_const_mul, integral_exp_neg_mul_Ioi (dirEig_pos m₀ K), div_eq_mul_inv]
  · intro K _
    exact (integrableOn_exp_neg_mul_Ioi (dirEig_pos m₀ K)).const_mul _

/-! ## The diagonal bound -/

/-- The 1-D diagonal heat kernel Σ_j e_j(i)² exp(−τ sineEig j) (τ in lattice time units). -/
def heat1 (N : ℕ) (τ : ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin N, sineVec N j i ^ 2 * exp (-(τ * sineEig N j))

theorem heat1_nonneg (N : ℕ) (τ : ℝ) (i : Fin N) : 0 ≤ heat1 N τ i :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (exp_pos _).le

/-- Factorisation p_t(x, x) = e^{−t m₀²} h(t/ε², x₁) h(t/ε², x₂). -/
theorem heatK_diag_eq (m₀ t : ℝ) (x : DSite n k) :
    heatK n k m₀ t x x = exp (-(t * m₀ ^ 2)) *
      (heat1 (boxN n k) (t * (spacing n ^ 2)⁻¹) x.1 *
        heat1 (boxN n k) (t * (spacing n ^ 2)⁻¹) x.2) := by
  unfold heatK heat1
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [sineVec2, dirEig]
  rw [show -(t * ((spacing n ^ 2)⁻¹ * (sineEig (boxN n k) a + sineEig (boxN n k) b) + m₀ ^ 2)) =
      -(t * m₀ ^ 2) + (-(t * (spacing n ^ 2)⁻¹ * sineEig (boxN n k) a) +
        -(t * (spacing n ^ 2)⁻¹ * sineEig (boxN n k) b)) by ring, exp_add, exp_add]
  ring

theorem sineVec_sq_le (N j : ℕ) (i : Fin N) : sineVec N j i ^ 2 ≤ 2 / ((N : ℝ) + 1) := by
  have h0 : (0 : ℝ) ≤ 2 / ((N : ℝ) + 1) := by positivity
  unfold sineVec sineFn
  rw [mul_pow, sq_sqrt h0]
  have := sin_sq_le_one (π * (((i : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) / ((N : ℝ) + 1))
  nlinarith

/-- Jordan's inequality: sineEig N j ≥ 4 ((j+1)/(N+1))². -/
theorem sineEig_ge (N j : ℕ) (hj : j < N) :
    4 * (((j : ℝ) + 1) / ((N : ℝ) + 1)) ^ 2 ≤ sineEig N j := by
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hj' : (j : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast (by omega : j + 1 ≤ N + 1)
  have hpi := Real.pi_pos
  have h0 : 0 ≤ π * ((j : ℝ) + 1) / (2 * ((N : ℝ) + 1)) := by positivity
  have h1 : π * ((j : ℝ) + 1) / (2 * ((N : ℝ) + 1)) ≤ π / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h := Real.mul_le_sin h0 h1
  have e : 2 / π * (π * ((j : ℝ) + 1) / (2 * ((N : ℝ) + 1))) = ((j : ℝ) + 1) / ((N : ℝ) + 1) := by
    field_simp
  rw [e] at h
  have h2 : 0 ≤ ((j : ℝ) + 1) / ((N : ℝ) + 1) := by positivity
  unfold sineEig
  have := pow_le_pow_left₀ h2 h 2
  linarith

/-- Gaussian sum ≤ Gaussian integral: Σ_{j=1}^N e^{−a j²} ≤ √(π/a)/2. -/
theorem gauss_sum_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ j ∈ range N, exp (-a * ((j : ℝ) + 1) ^ 2) ≤ √(π / a) / 2 := by
  set f : ℝ → ℝ := fun s => exp (-a * s ^ 2) with hf
  have hanti : AntitoneOn f (Icc 0 (0 + (N : ℝ))) := by
    intro s hs u hu hsu
    simp only [hf]
    apply exp_le_exp.mpr
    have h0 := hs.1
    have h2 : s ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ h0 hsu 2
    nlinarith
  have h1 := hanti.sum_le_integral
  simp only [zero_add] at h1
  have h2 : ∫ s in (0 : ℝ)..N, f s ≤ ∫ s in Ioi (0 : ℝ), f s := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    apply setIntegral_mono_set
    · exact (integrable_exp_neg_mul_sq ha).integrableOn
    · filter_upwards with s using (exp_pos _).le
    · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
  have h3 : ∫ s in Ioi (0 : ℝ), f s = √(π / a) / 2 := integral_gaussian_Ioi a
  calc ∑ j ∈ range N, exp (-a * ((j : ℝ) + 1) ^ 2)
      = ∑ j ∈ range N, f ((j + 1 : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_; simp [hf]
    _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3

/-- **1-D diagonal bound:** h(τ, i) ≤ √(π/(4τ)) for τ > 0, uniformly in N and i. -/
theorem heat1_le (N : ℕ) {τ : ℝ} (hτ : 0 < τ) (i : Fin N) :
    heat1 N τ i ≤ √(π / (4 * τ)) := by
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set a : ℝ := 4 * τ / ((N : ℝ) + 1) ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hterm : ∀ j : Fin N, sineVec N j i ^ 2 * exp (-(τ * sineEig N j)) ≤
      2 / ((N : ℝ) + 1) * exp (-a * (((j : ℕ) : ℝ) + 1) ^ 2) := by
    intro j
    apply mul_le_mul (sineVec_sq_le N j i) _ (exp_pos _).le (by positivity)
    apply exp_le_exp.mpr
    have h := sineEig_ge N j j.isLt
    have e : a * (((j : ℕ) : ℝ) + 1) ^ 2 = τ * (4 * ((((j : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) ^ 2) := by
      rw [ha]; field_simp
    rw [neg_mul, e]
    have := mul_le_mul_of_nonneg_left h hτ.le
    linarith
  have hsum := gauss_sum_le ha0 N
  have hsq : √(π / a) = ((N : ℝ) + 1) * √(π / (4 * τ)) := by
    rw [show π / a = ((N : ℝ) + 1) ^ 2 * (π / (4 * τ)) by rw [ha]; field_simp,
      sqrt_mul (by positivity), sqrt_sq hM.le]
  calc heat1 N τ i ≤ ∑ j : Fin N, 2 / ((N : ℝ) + 1) * exp (-a * (((j : ℕ) : ℝ) + 1) ^ 2) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = 2 / ((N : ℝ) + 1) * ∑ j ∈ range N, exp (-a * ((j : ℝ) + 1) ^ 2) := by
        rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => exp (-a * ((j : ℝ) + 1) ^ 2))]
    _ ≤ 2 / ((N : ℝ) + 1) * (√(π / a) / 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = √(π / (4 * τ)) := by rw [hsq]; field_simp

/-- **Diagonal heat-kernel bound, uniform in n, k, x, m₀:** for t > 0,
ε⁻² p_t(x, x) ≤ π / (4t). -/
theorem heatK_diag_le (m₀ : ℝ) {t : ℝ} (ht : 0 < t) (x : DSite n k) :
    (spacing n ^ 2)⁻¹ * heatK n k m₀ t x x ≤ π / (4 * t) := by
  have hε := spacing_pos n
  set τ := t * (spacing n ^ 2)⁻¹ with hτ
  have hτ0 : 0 < τ := by positivity
  rw [heatK_diag_eq]
  have e1 : exp (-(t * m₀ ^ 2)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg m₀])
  have b1 := heat1_le (boxN n k) hτ0 x.1
  have b2 := heat1_le (boxN n k) hτ0 x.2
  have n1 := heat1_nonneg (boxN n k) τ x.1
  have n2 := heat1_nonneg (boxN n k) τ x.2
  have hprod : heat1 (boxN n k) τ x.1 * heat1 (boxN n k) τ x.2 ≤ π / (4 * τ) := by
    calc _ ≤ √(π / (4 * τ)) * √(π / (4 * τ)) := mul_le_mul b1 b2 n2 (sqrt_nonneg _)
      _ = π / (4 * τ) := mul_self_sqrt (by positivity)
  have hP : 0 ≤ heat1 (boxN n k) τ x.1 * heat1 (boxN n k) τ x.2 := mul_nonneg n1 n2
  calc (spacing n ^ 2)⁻¹ * (exp (-(t * m₀ ^ 2)) *
        (heat1 (boxN n k) τ x.1 * heat1 (boxN n k) τ x.2))
      ≤ (spacing n ^ 2)⁻¹ * (1 * (π / (4 * τ))) := by
        gcongr
    _ = π / (4 * t) := by rw [hτ]; field_simp

end PP2Target

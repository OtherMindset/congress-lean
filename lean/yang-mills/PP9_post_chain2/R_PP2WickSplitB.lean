import LongTable.R_PP2WickSplitA

/-!
Part B of PP2WickSplit (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2WickSplit.lean)

FORMALIZED in this part (for `PP2Target.wickPow`, #mwvi84dh-hnd872):
* `wickPow_orthogonal` (one variable, j, k ≤ 4): ∫ :x^j:_v :x^k:_v dγ_v = δ_jk j! v^j.
* `wickPow_cross` / `wickPow_cross_cov` (two variables, j, k ≤ 4): for the jointly Gaussian
  pair X = x, Y = (r/c)x + w with x ~ γ_c, w ~ γ_{c'−r²/c} independent (covariance
  [[c, r], [r, c']], c > 0, r² ≤ c c'): E[:X^j:_c :Y^k:_{c'}] = δ_jk j! r^j.

NOT formalized: orthogonality for degrees > 4 (the binomial formula is for all degrees);
the two-variable statement for an abstract jointly Gaussian law (it is stated for the explicit
realisation above, which covers every covariance with c > 0); that this pair has the stated
covariance (elementary and used only through the algebra in `wickPow_cross_cov`: Var X = c,
Var Y = (r/c)²c + (c' − r²/c) = c', Cov = r, and c' − r²/c ≥ 0 iff r² ≤ c c' for c > 0; no
probability-theory covariance statement is formalized); the degenerate case c = 0; multi-site / field versions.

Proof of the binomial formula: generating function in `PowerSeries ℝ`, using Mathlib's
`PowerSeries.exp_mul_exp_eq_exp_add` and `PowerSeries.expand`. Written from scratch; the
recurrence-based proof in pphi2 (Pphi2/NelsonEstimate/WickBinomial.lean, commit 83501022,
Apache-2.0) was read for orientation only and is not ported.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset

noncomputable section

namespace PP2Target

open ProbabilityTheory NNReal

section OrthCases

set_option linter.unusedTactic false

theorem wick_orth_1_3 (v : ℝ≥0) :
    ∫ x, wickPow v 1 x * wickPow v 3 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 1 x * wickPow v 3 x) =
      fun x => ∑ i : Fin 9, ![0, 0, ((-3) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_one, wickPow_three]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_1_4 (v : ℝ≥0) :
    ∫ x, wickPow v 1 x * wickPow v 4 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 1 x * wickPow v 4 x) =
      fun x => ∑ i : Fin 9, ![0, ((3) * (v : ℝ) ^ 2), 0, ((-6) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_one, wickPow_four']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_2_0 (v : ℝ≥0) :
    ∫ x, wickPow v 2 x * wickPow v 0 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 2 x * wickPow v 0 x) =
      fun x => ∑ i : Fin 9, ![((-1) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_two, wickPow_zero']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_2_1 (v : ℝ≥0) :
    ∫ x, wickPow v 2 x * wickPow v 1 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 2 x * wickPow v 1 x) =
      fun x => ∑ i : Fin 9, ![0, ((-1) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_two, wickPow_one]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_2_2 (v : ℝ≥0) :
    ∫ x, wickPow v 2 x * wickPow v 2 x ∂gaussianReal 0 v = 2 * (v : ℝ) ^ 2 := by
  have h : (fun x : ℝ => wickPow v 2 x * wickPow v 2 x) =
      fun x => ∑ i : Fin 9, ![((1) * (v : ℝ) ^ 2), 0, ((-2) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_two, wickPow_two]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_2_3 (v : ℝ≥0) :
    ∫ x, wickPow v 2 x * wickPow v 3 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 2 x * wickPow v 3 x) =
      fun x => ∑ i : Fin 9, ![0, ((3) * (v : ℝ) ^ 2), 0, ((-4) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_two, wickPow_three]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_2_4 (v : ℝ≥0) :
    ∫ x, wickPow v 2 x * wickPow v 4 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 2 x * wickPow v 4 x) =
      fun x => ∑ i : Fin 9, ![((-3) * (v : ℝ) ^ 3), 0, ((9) * (v : ℝ) ^ 2), 0, ((-7) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_two, wickPow_four']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_3_0 (v : ℝ≥0) :
    ∫ x, wickPow v 3 x * wickPow v 0 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 3 x * wickPow v 0 x) =
      fun x => ∑ i : Fin 9, ![0, ((-3) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_three, wickPow_zero']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_3_1 (v : ℝ≥0) :
    ∫ x, wickPow v 3 x * wickPow v 1 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 3 x * wickPow v 1 x) =
      fun x => ∑ i : Fin 9, ![0, 0, ((-3) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_three, wickPow_one]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_3_2 (v : ℝ≥0) :
    ∫ x, wickPow v 3 x * wickPow v 2 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 3 x * wickPow v 2 x) =
      fun x => ∑ i : Fin 9, ![0, ((3) * (v : ℝ) ^ 2), 0, ((-4) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_three, wickPow_two]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_3_3 (v : ℝ≥0) :
    ∫ x, wickPow v 3 x * wickPow v 3 x ∂gaussianReal 0 v = 6 * (v : ℝ) ^ 3 := by
  have h : (fun x : ℝ => wickPow v 3 x * wickPow v 3 x) =
      fun x => ∑ i : Fin 9, ![0, 0, ((9) * (v : ℝ) ^ 2), 0, ((-6) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_three, wickPow_three]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_3_4 (v : ℝ≥0) :
    ∫ x, wickPow v 3 x * wickPow v 4 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 3 x * wickPow v 4 x) =
      fun x => ∑ i : Fin 9, ![0, ((-9) * (v : ℝ) ^ 3), 0, ((21) * (v : ℝ) ^ 2), 0, ((-9) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_three, wickPow_four']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_4_0 (v : ℝ≥0) :
    ∫ x, wickPow v 4 x * wickPow v 0 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 4 x * wickPow v 0 x) =
      fun x => ∑ i : Fin 9, ![((3) * (v : ℝ) ^ 2), 0, ((-6) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_four', wickPow_zero']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_4_1 (v : ℝ≥0) :
    ∫ x, wickPow v 4 x * wickPow v 1 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 4 x * wickPow v 1 x) =
      fun x => ∑ i : Fin 9, ![0, ((3) * (v : ℝ) ^ 2), 0, ((-6) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_four', wickPow_one]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_4_2 (v : ℝ≥0) :
    ∫ x, wickPow v 4 x * wickPow v 2 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 4 x * wickPow v 2 x) =
      fun x => ∑ i : Fin 9, ![((-3) * (v : ℝ) ^ 3), 0, ((9) * (v : ℝ) ^ 2), 0, ((-7) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_four', wickPow_two]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_4_3 (v : ℝ≥0) :
    ∫ x, wickPow v 4 x * wickPow v 3 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 4 x * wickPow v 3 x) =
      fun x => ∑ i : Fin 9, ![0, ((-9) * (v : ℝ) ^ 3), 0, ((21) * (v : ℝ) ^ 2), 0, ((-9) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_four', wickPow_three]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_4_4 (v : ℝ≥0) :
    ∫ x, wickPow v 4 x * wickPow v 4 x ∂gaussianReal 0 v = 24 * (v : ℝ) ^ 4 := by
  have h : (fun x : ℝ => wickPow v 4 x * wickPow v 4 x) =
      fun x => ∑ i : Fin 9, ![((9) * (v : ℝ) ^ 4), 0, ((-36) * (v : ℝ) ^ 3), 0, ((42) * (v : ℝ) ^ 2), 0, ((-12) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0)] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_four', wickPow_four']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)


end OrthCases

/-- **One-dimensional Gaussian orthogonality** of Wick powers, degrees ≤ 4:
E_{γ_v}[:x^j:_v :x^k:_v] = δ_jk j! v^j for the centred Gaussian of variance v. -/
theorem wickPow_orthogonal (v : ℝ≥0) (j k : ℕ) (hj : j ≤ 4) (hk : k ≤ 4) :
    ∫ x, wickPow v j x * wickPow v k x ∂gaussianReal 0 v =
      if j = k then (j.factorial : ℝ) * (v : ℝ) ^ j else 0 := by
  interval_cases j <;> interval_cases k <;>
    (first
      | rw [wick_orth_0_0] |
      rw [wick_orth_0_1] |
      rw [wick_orth_0_2] |
      rw [wick_orth_0_3] |
      rw [wick_orth_0_4] |
      rw [wick_orth_1_0] |
      rw [wick_orth_1_1] |
      rw [wick_orth_1_2] |
      rw [wick_orth_1_3] |
      rw [wick_orth_1_4] |
      rw [wick_orth_2_0] |
      rw [wick_orth_2_1] |
      rw [wick_orth_2_2] |
      rw [wick_orth_2_3] |
      rw [wick_orth_2_4] |
      rw [wick_orth_3_0] |
      rw [wick_orth_3_1] |
      rw [wick_orth_3_2] |
      rw [wick_orth_3_3] |
      rw [wick_orth_3_4] |
      rw [wick_orth_4_0] |
      rw [wick_orth_4_1] |
      rw [wick_orth_4_2] |
      rw [wick_orth_4_3] |
      rw [wick_orth_4_4]) <;>
    simp [Nat.factorial]

/-! ## Two-variable version: a jointly Gaussian pair realised as (x, a·x + w) -/

theorem integrable_wickPow_mul (c c' : ℝ) (v : ℝ≥0) (j i : ℕ) :
    Integrable (fun x => wickPow c j x * wickPow c' i x) (gaussianReal 0 v) := by
  have gen : ∀ (A B : ℝ) (p q : ℕ),
      Integrable (fun x : ℝ => A * x ^ p * (B * x ^ q)) (gaussianReal 0 v) := by
    intro A B p q
    refine ((integrable_pow_gaussianReal v (p + q)).const_mul (A * B)).congr
      (ae_of_all _ fun x => ?_)
    simp only
    ring
  simp only [wickPow, sum_mul, mul_sum]
  exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => gen _ _ _ _

theorem integral_wickPow_gaussianReal (v : ℝ≥0) (m : ℕ) (hm : m ≤ 4) :
    ∫ x, wickPow v m x ∂gaussianReal 0 v = if m = 0 then 1 else 0 := by
  have h := wickPow_orthogonal v m 0 hm (by norm_num)
  simp only [wickPow_zero', mul_one] at h
  rw [h]
  split_ifs <;> simp_all

/-- **Cross orthogonality** for the jointly Gaussian pair (X, Y) = (x, a·x + w), x ~ γ_c,
w ~ γ_d independent (covariance [[c, a c], [a c, a² c + d]]):
E[:X^j:_c :Y^k:_{a²c+d}] = δ_jk j! (a c)^j, for j, k ≤ 4. -/
theorem wickPow_cross (c d : ℝ≥0) (a : ℝ) (j k : ℕ) (hj : j ≤ 4) (hk : k ≤ 4) :
    ∫ p : ℝ × ℝ, wickPow c j p.1 * wickPow (a ^ 2 * c + d) k (a * p.1 + p.2)
        ∂(gaussianReal 0 c).prod (gaussianReal 0 d) =
      if j = k then (j.factorial : ℝ) * (a * c) ^ j else 0 := by
  have hexp : ∀ p : ℝ × ℝ, wickPow c j p.1 * wickPow (a ^ 2 * c + d) k (a * p.1 + p.2) =
      ∑ i ∈ range (k + 1), ((k.choose i : ℝ) * a ^ i) *
        ((fun x => wickPow c j x * wickPow c i x) p.1 * (fun w => wickPow d (k - i) w) p.2) := by
    intro p
    rw [wickPow_add_binomial, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [wickPow_scale]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => (((integrable_wickPow_mul c c c j i).mul_prod
    (integrable_wickPow_mul d d d (k - i) 0)).congr (ae_of_all _ fun p => by
      simp [wickPow_zero'])).const_mul _)]
  simp_rw [integral_const_mul]
  have hprod : ∀ i, ∫ p : ℝ × ℝ, (fun x => wickPow c j x * wickPow c i x) p.1 *
      (fun w => wickPow d (k - i) w) p.2 ∂(gaussianReal 0 c).prod (gaussianReal 0 d) =
      (∫ x, wickPow c j x * wickPow c i x ∂gaussianReal 0 c) *
        ∫ w, wickPow d (k - i) w ∂gaussianReal 0 d :=
    fun i => integral_prod_mul (L := ℝ) (μ := gaussianReal 0 c) (ν := gaussianReal 0 d)
      (fun x => wickPow c j x * wickPow c i x) (fun w => wickPow d (k - i) w)
  simp only at hprod
  simp_rw [hprod]
  rw [Finset.sum_eq_single k]
  · rw [Nat.sub_self, integral_wickPow_gaussianReal d 0 (by norm_num), wickPow_orthogonal c j k hj hk]
    simp only [ite_true]
    split_ifs with h
    · subst h; simp; ring
    · simp
  · intro i hi hik
    have hi' : i ≤ k := by simp at hi; omega
    rw [integral_wickPow_gaussianReal d (k - i) (by omega)]
    simp [show k - i ≠ 0 by omega]
  · intro h; simp at h

/-- The same in covariance form: for c > 0 and r² ≤ c c', the pair (x, (r/c)x + w),
x ~ γ_c, w ~ γ_{c' − r²/c}, has covariance [[c, r], [r, c']], and
E[:X^j:_c :Y^k:_{c'}] = δ_jk j! r^j for j, k ≤ 4. -/
theorem wickPow_cross_cov (c c' : ℝ≥0) (r : ℝ) (hc : 0 < (c : ℝ)) (hr : r ^ 2 ≤ c * c')
    (j k : ℕ) (hj : j ≤ 4) (hk : k ≤ 4) :
    ∫ p : ℝ × ℝ, wickPow c j p.1 * wickPow c' k (r / c * p.1 + p.2)
        ∂(gaussianReal 0 c).prod (gaussianReal 0 (Real.toNNReal (c' - r ^ 2 / c))) =
      if j = k then (j.factorial : ℝ) * r ^ j else 0 := by
  have hd : ((Real.toNNReal (c' - r ^ 2 / c)) : ℝ) = c' - r ^ 2 / c := by
    refine Real.coe_toNNReal _ ?_
    rw [sub_nonneg, div_le_iff₀ hc]
    linarith
  have h1 : (r / c) ^ 2 * c + (c' - r ^ 2 / c) = c' := by field_simp; ring
  have h2 : r / c * c = r := by field_simp
  have := wickPow_cross c (Real.toNNReal (c' - r ^ 2 / c)) (r / c) j k hj hk
  rw [hd, h1, h2] at this
  exact this

end PP2Target

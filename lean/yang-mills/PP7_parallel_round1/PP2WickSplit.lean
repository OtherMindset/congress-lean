import LongTable.P_mwvi84dh_hnd872

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction. Node M5d, session 1:
Wick-polynomial algebra for Nelson's covariance split.

FORMALIZED (for `PP2Target.wickPow`, #mwvi84dh-hnd872):
* `wickPow_coeff_gen`: Σ_k :y^k:_c t^k/k! = e^{ty}·e^{−ct²/2} as formal power series over ℝ.
* `wickPow_add_binomial` (Wick binomial / Hermite addition formula, all j, all real c₁ c₂ y z):
  :(y+z)^j:_{c₁+c₂} = Σ_{i ≤ j} C(j,i) :y^i:_{c₁} :z^(j−i):_{c₂}.
  `wickPow_four_add`: the j = 4 case written out. `wickPow_scale`: :(ay)^k:_{a²c} = a^k :y^k:_c.
* Gaussian moments of `gaussianReal 0 v`: E x^(n+2) = (n+1) v E x^n (`gaussian_moment_succ_succ`,
  via the mgf), odd moments vanish, E x^2,4,6,8 = v, 3v², 15v³, 105v⁴.
* `wickPow_orthogonal` (one variable, j, k ≤ 4): ∫ :x^j:_v :x^k:_v dγ_v = δ_jk j! v^j.
* `wickPow_cross` / `wickPow_cross_cov` (two variables, j, k ≤ 4): for the jointly Gaussian
  pair X = x, Y = (r/c)x + w with x ~ γ_c, w ~ γ_{c'−r²/c} independent (covariance
  [[c, r], [r, c']], c > 0, r² ≤ c c'): E[:X^j:_c :Y^k:_{c'}] = δ_jk j! r^j.

NOT formalized: orthogonality for degrees > 4 (the binomial formula is for all degrees);
the two-variable statement for an abstract jointly Gaussian law (it is stated for the explicit
realisation above, which covers every covariance with c > 0); that this pair has the stated
covariance (immediate, not proved here); the degenerate case c = 0; multi-site / field versions.

Proof of the binomial formula: generating function in `PowerSeries ℝ`, using Mathlib's
`PowerSeries.exp_mul_exp_eq_exp_add` and `PowerSeries.expand`. Written from scratch; the
recurrence-based proof in pphi2 (Pphi2/NelsonEstimate/WickBinomial.lean, commit 83501022,
Apache-2.0) was read for orientation only and is not ported.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset

noncomputable section

namespace PP2Target

/-- The generating series e^{ty}·e^{−ct²/2}. -/
def wickGen (c y : ℝ) : PowerSeries ℝ :=
  PowerSeries.rescale y (PowerSeries.exp ℝ) *
    PowerSeries.expand 2 two_ne_zero (PowerSeries.rescale (-c / 2) (PowerSeries.exp ℝ))

theorem wickGen_mul (c₁ c₂ y z : ℝ) :
    wickGen c₁ y * wickGen c₂ z = wickGen (c₁ + c₂) (y + z) := by
  unfold wickGen
  have h1 := PowerSeries.exp_mul_exp_eq_exp_add y z
  have h2 := PowerSeries.exp_mul_exp_eq_exp_add (-c₁ / 2) (-c₂ / 2)
  have : -(c₁ + c₂) / 2 = -c₁ / 2 + -c₂ / 2 := by ring
  rw [this, ← h1, ← h2, map_mul]
  ring

theorem sum_range_even (g : ℕ → ℝ) (n : ℕ) :
    ∑ b ∈ range n, (if 2 ∣ b then g (b / 2) else 0) = ∑ j ∈ range ((n + 1) / 2), g j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have h1 : (2 * m + 1 + 1) / 2 = (2 * m + 1) / 2 + 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      rw [h1, sum_range_succ, h2]
      simp
    · have h1 : (2 * m + 1 + 1 + 1) / 2 = (2 * m + 1 + 1) / 2 := by omega
      have h2 : ¬ 2 ∣ 2 * m + 1 := by omega
      simp [h1, h2]

theorem wickPow_coeff_gen (c y : ℝ) (k : ℕ) :
    PowerSeries.coeff k (wickGen c y) = wickPow c k y / (k.factorial : ℝ) := by
  rw [wickGen, mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.rescale (-c / 2) (PowerSeries.exp ℝ))) *
        PowerSeries.coeff b (PowerSeries.rescale y (PowerSeries.exp ℝ)))]
  have key : ∀ b ∈ range (k.succ),
      PowerSeries.coeff b (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.rescale (-c / 2) (PowerSeries.exp ℝ))) *
        PowerSeries.coeff (k - b) (PowerSeries.rescale y (PowerSeries.exp ℝ))
      = if 2 ∣ b then (fun j : ℕ => (-c / 2) ^ j / (j.factorial : ℝ) *
          (y ^ (k - 2 * j) / ((k - 2 * j).factorial : ℝ))) (b / 2) else 0 := by
    intro b _
    rw [PowerSeries.coeff_expand]
    split_ifs with h
    · obtain ⟨j, rfl⟩ := h
      simp [PowerSeries.coeff_rescale, div_eq_mul_inv]
    · simp
  rw [sum_congr rfl key, sum_range_even (fun j : ℕ => (-c / 2) ^ j / (j.factorial : ℝ) *
          (y ^ (k - 2 * j) / ((k - 2 * j).factorial : ℝ))) k.succ]
  have h3 : (k.succ + 1) / 2 = k / 2 + 1 := by omega
  rw [h3, wickPow, sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hj' : (j.factorial : ℝ) ≠ 0 := by positivity
  have hk2 : ((k - 2 * j).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [show -(c / 2) = (-1) * c / 2 by ring, div_pow, mul_pow]
  field_simp

/-- **Wick binomial theorem** (Hermite addition formula), for all real c₁, c₂, y, z. -/
theorem wickPow_add_binomial (c₁ c₂ y z : ℝ) (j : ℕ) :
    wickPow (c₁ + c₂) j (y + z) =
      ∑ i ∈ range (j + 1), (j.choose i : ℝ) * wickPow c₁ i y * wickPow c₂ (j - i) z := by
  have h := congrArg (PowerSeries.coeff j) (wickGen_mul c₁ c₂ y z)
  rw [wickPow_coeff_gen, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (wickGen c₁ y) * PowerSeries.coeff b (wickGen c₂ z))] at h
  simp only [wickPow_coeff_gen] at h
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hj] at h
  rw [← h, sum_mul]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ j := by simp at hi; omega
  have hc := Nat.choose_mul_factorial_mul_factorial hi'
  have hc' : (j.choose i : ℝ) * (i.factorial : ℝ) * ((j - i).factorial : ℝ) = j.factorial := by
    exact_mod_cast hc
  rw [← hc']
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((j - i).factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem wickPow_zero' (c y : ℝ) : wickPow c 0 y = 1 := by simp [wickPow]
theorem wickPow_one (c y : ℝ) : wickPow c 1 y = y := by simp [wickPow]
theorem wickPow_two (c y : ℝ) : wickPow c 2 y = y ^ 2 - c := by
  simp [wickPow, Finset.sum_range_succ, Nat.factorial]; ring
theorem wickPow_three (c y : ℝ) : wickPow c 3 y = y ^ 3 - 3 * c * y := by
  simp [wickPow, Finset.sum_range_succ, Nat.factorial]; ring
theorem wickPow_four' (c y : ℝ) : wickPow c 4 y = y ^ 4 - 6 * c * y ^ 2 + 3 * c ^ 2 := by
  simp [wickPow, Finset.sum_range_succ, Nat.factorial]; ring

/-- The quartic split used by Nelson's estimate. -/
theorem wickPow_four_add (c₁ c₂ y z : ℝ) :
    wickPow (c₁ + c₂) 4 (y + z) =
      wickPow c₁ 4 y + 4 * wickPow c₁ 3 y * z + 6 * wickPow c₁ 2 y * wickPow c₂ 2 z
        + 4 * y * wickPow c₂ 3 z + wickPow c₂ 4 z := by
  simp only [wickPow_four', wickPow_three, wickPow_two]
  ring

/-- Scaling: :(ay)^k:_{a²c} = a^k :y^k:_c. -/
theorem wickPow_scale (a c y : ℝ) (k : ℕ) :
    wickPow (a ^ 2 * c) k (a * y) = a ^ k * wickPow c k y := by
  rw [wickPow, wickPow, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : 2 * j ≤ k := by simp at hj; omega
  have : a ^ k = (a ^ 2) ^ j * a ^ (k - 2 * j) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [this, mul_pow, mul_pow]
  ring

/-! ## One-dimensional Gaussian moments and orthogonality -/

open ProbabilityTheory NNReal

theorem integrable_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
  have := integrable_pow_mul_exp_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
    (μ := gaussianReal 0 v) (v := 0) (by simp) n
  simpa using this

theorem moment_eq_iteratedDeriv (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ n ∂gaussianReal 0 v = iteratedDeriv n (fun t => Real.exp (v * t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) n
  rw [mgf_fun_id_gaussianReal] at h
  simpa using h.symm

theorem iteratedDeriv_gaussMGF_succ_succ (v : ℝ≥0) (n : ℕ) :
    iteratedDeriv (n + 2) (fun t => Real.exp (v * t ^ 2 / 2)) 0 =
      (n + 1) * v * iteratedDeriv n (fun t => Real.exp (v * t ^ 2 / 2)) 0 := by
  have hd : deriv (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) =
      (fun t : ℝ => t * (v : ℝ)) * (fun t => Real.exp (v * t ^ 2 / 2)) := by
    funext t
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, deriv_const_mul_field', deriv_pow_field, Pi.mul_apply]
    push_cast
    ring
  rw [iteratedDeriv_succ', hd, iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  rw [Finset.sum_eq_single 1]
  · rw [iteratedDeriv_mul_const_field, iteratedDeriv_fun_id_zero]
    simp only [ite_true, Nat.choose_one_right]
    have : n + 1 - 1 = n := by omega
    rw [this]
    push_cast
    ring
  · intro b _ hb
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_fun_id_zero]
    simp [hb]
  · intro h
    simp at h

theorem gaussian_moment_succ_succ (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂gaussianReal 0 v = (n + 1) * v * ∫ x, x ^ n ∂gaussianReal 0 v := by
  rw [moment_eq_iteratedDeriv, moment_eq_iteratedDeriv, iteratedDeriv_gaussMGF_succ_succ]

theorem gaussian_moment_zero (v : ℝ≥0) : ∫ x, x ^ 0 ∂gaussianReal 0 v = 1 := by simp

theorem gaussian_moment_one (v : ℝ≥0) : ∫ x, x ^ 1 ∂gaussianReal 0 v = 0 := by simp

theorem gaussian_moment_odd (v : ℝ≥0) (m : ℕ) : ∫ x, x ^ (2 * m + 1) ∂gaussianReal 0 v = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, gaussian_moment_succ_succ, ih, mul_zero]

theorem gaussian_moment_two (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  rw [gaussian_moment_succ_succ v 0, gaussian_moment_zero]; simp

theorem gaussian_moment_four (v : ℝ≥0) : ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  rw [gaussian_moment_succ_succ v 2, gaussian_moment_two]; push_cast; ring

theorem gaussian_moment_six (v : ℝ≥0) : ∫ x, x ^ 6 ∂gaussianReal 0 v = 15 * (v : ℝ) ^ 3 := by
  rw [gaussian_moment_succ_succ v 4, gaussian_moment_four]; push_cast; ring

theorem gaussian_moment_eight (v : ℝ≥0) : ∫ x, x ^ 8 ∂gaussianReal 0 v = 105 * (v : ℝ) ^ 4 := by
  rw [gaussian_moment_succ_succ v 6, gaussian_moment_six]; push_cast; ring

theorem integral_poly8_gaussianReal (v : ℝ≥0) (a : Fin 9 → ℝ) :
    ∫ x, ∑ i : Fin 9, a i * x ^ (i : ℕ) ∂gaussianReal 0 v =
      a 0 + a 2 * v + 3 * a 4 * v ^ 2 + 15 * a 6 * v ^ 3 + 105 * a 8 * v ^ 4 := by
  rw [integral_finsetSum _ (fun i _ => (integrable_pow_gaussianReal v _).const_mul _)]
  simp only [integral_const_mul, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h3 := gaussian_moment_odd v 1
  have h5 := gaussian_moment_odd v 2
  have h7 := gaussian_moment_odd v 3
  norm_num at h3 h5 h7
  simp [h3, h5, h7, gaussian_moment_two, gaussian_moment_four, gaussian_moment_six,
    gaussian_moment_eight]
  ring

-- The 25 cases below are generated uniformly; some `try` steps are no-ops in some cases.
section OrthCases
set_option linter.unusedTactic false

theorem wick_orth_0_0 (v : ℝ≥0) :
    ∫ x, wickPow v 0 x * wickPow v 0 x ∂gaussianReal 0 v = 1 * (v : ℝ) ^ 0 := by
  have h : (fun x : ℝ => wickPow v 0 x * wickPow v 0 x) =
      fun x => ∑ i : Fin 9, ![((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_zero', wickPow_zero']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_0_1 (v : ℝ≥0) :
    ∫ x, wickPow v 0 x * wickPow v 1 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 0 x * wickPow v 1 x) =
      fun x => ∑ i : Fin 9, ![0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_zero', wickPow_one]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_0_2 (v : ℝ≥0) :
    ∫ x, wickPow v 0 x * wickPow v 2 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 0 x * wickPow v 2 x) =
      fun x => ∑ i : Fin 9, ![((-1) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_zero', wickPow_two]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_0_3 (v : ℝ≥0) :
    ∫ x, wickPow v 0 x * wickPow v 3 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 0 x * wickPow v 3 x) =
      fun x => ∑ i : Fin 9, ![0, ((-3) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_zero', wickPow_three]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_0_4 (v : ℝ≥0) :
    ∫ x, wickPow v 0 x * wickPow v 4 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 0 x * wickPow v 4 x) =
      fun x => ∑ i : Fin 9, ![((3) * (v : ℝ) ^ 2), 0, ((-6) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_zero', wickPow_four']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_1_0 (v : ℝ≥0) :
    ∫ x, wickPow v 1 x * wickPow v 0 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 1 x * wickPow v 0 x) =
      fun x => ∑ i : Fin 9, ![0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_one, wickPow_zero']
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_1_1 (v : ℝ≥0) :
    ∫ x, wickPow v 1 x * wickPow v 1 x ∂gaussianReal 0 v = 1 * (v : ℝ) ^ 1 := by
  have h : (fun x : ℝ => wickPow v 1 x * wickPow v 1 x) =
      fun x => ∑ i : Fin 9, ![0, 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_one, wickPow_one]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

theorem wick_orth_1_2 (v : ℝ≥0) :
    ∫ x, wickPow v 1 x * wickPow v 2 x ∂gaussianReal 0 v = 0 := by
  have h : (fun x : ℝ => wickPow v 1 x * wickPow v 2 x) =
      fun x => ∑ i : Fin 9, ![0, ((-1) * (v : ℝ) ^ 1), 0, ((1) * (v : ℝ) ^ 0), 0, 0, 0, 0, 0] i * x ^ (i : ℕ) := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wickPow_one, wickPow_two]
    (try simp)
    (try ring)
  rw [h, integral_poly8_gaussianReal]
  (try simp)
  (try ring)

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

import LongTable.R_PP2Chaos

/-!
Part A of PP2Chaos2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Chaos2.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction. Node M5e, session 2:
hypercontractive-type moment bounds for Wick polynomials of degree ≤ 4 per variable in finitely
many independent standard Gaussians (for Nelson's estimate). Builds on `LongTable.PP2Chaos`
(session 1: `oneDim_moment` under an admissibility hypothesis on ρ).

Notation: γⁿ = `ch2_gauss n` (product of n standard Gaussians), α : Fin n → Fin 5 a multi-index,
|α| = `ch2_deg α`, α! = `ch2_fact α`, F_{T_ρ c}(x) = `ch2_F n ρ c x` = Σ_α ρ^{|α|} c_α Π_i He_{α_i}(x_i),
Σ_α α! c_α² = `ch2_norm n c`, ρ_m = `ch2_rho m` = 1/(230 (m+1)³).

FORMALIZED (this session):
* Explicit admissible ρ (session-1 "what remains" item 1):
  `ch2_Pfun_eq` (P = t⁴/24 − t³/3 + 5t²/4 + 7/8, t = x²), `ch2_Pfun_le` (P ≤ (1+x²)⁴),
  `ch2_moment_le` (E x^{2j} ≤ (2K)^j for j ≤ K, from `gaussian_moment_succ_succ`),
  `ch2_moment_one_add_sq` (E(1+x²)^N ≤ (1+2N)^N), `ch2_int_Pfun_pow` (E P^j ≤ (1+8j)^{4j}),
  `ch2_split` (P(1+ρ²P)^m ≤ 3P + ((m+1)ρ²)^m P^{m+1}), and
  `ch2_admissible`: 52488 (m+1)⁶ ρ² ≤ 1 ⇒ (m+1)(2m+1)ρ² E[P(1+ρ²P)^m] ≤ 1.
  `oneDim_moment'`: E_γ[(Σ_{k≤4} ρ_m^k b_k He_k)^{2m+2}] ≤ (Σ_k k! b_k²)^{m+1} with
  ρ_m = 1/(230 (m+1)³), all m, all b; `oneDim_moment_le_rho`: the same for every 0 ≤ ρ ≤ ρ_m.
* Tensorization S(n) (item 2), by induction on n: first variable split off with
  `measurePreserving_piFinSuccAbove` + Tonelli (`ch2_lintegral_succ`), coefficient decomposition
  F_{n+1}(x₀, y) = Σ_k ρ^k He_k(x₀) F_n(c_k)(y) (`ch2_F_cons`), Σ_α α! c_α² = Σ_k k! N(c_k)
  (`ch2_norm_succ`), Minkowski in L^{m+1} for finite sums (`ch2_minkowski_sum`, from
  `ENNReal.lintegral_Lp_add_le`), 1-D step for each fixed y (`ch2_oneDim_lintegral`).
  `ch2_hyper_lintegral` / `ch2_hyper`: for every admissible ρ (in particular ρ ≤ ρ_m), all n, c:
    E_{γⁿ}[F_{T_ρ c}^{2m+2}] ≤ (Σ_α α! c_α²)^{m+1}.
  `ch2_L2_lintegral` / `ch2_L2`: E_{γⁿ}[F_c²] = Σ_α α! c_α² (from `wickPow_orthogonal`,
  `ch2_oneDim_L2`).
  `ch2_hyper_explicit`: E_{γⁿ}[F_{T_{ρ_m} c}^{2m+2}] ≤ (E_{γⁿ}[F_c²])^{m+1}.
* Degree-d corollary (first half of item 3), `ch2_degree_bound`: if c_α = 0 whenever |α| > d,
  E_{γⁿ}[F_c^{2m+2}] ≤ (ρ_m^{−2d} E_{γⁿ}[F_c²])^{m+1}, i.e. ‖F_c‖_{2m+2} ≤ (230 (m+1)³)^d ‖F_c‖₂.
  For d = 4: ‖W‖_q ≤ C q^{12} ‖W‖₂ (polynomial in q; the sharp exponent would be 2).
  Only 1-D integrability (polynomials) is used; n-dimensional statements go through lintegrals.

NOT formalized (remaining, estimate ~1½ sessions):
* Markov/tail bound P(|F| > t) ≤ exp(−c (t/‖F‖₂)^{1/12}) for degree ≤ 4 (choose m ≈
  (t/‖F‖₂)^{1/12}/C in `ch2_degree_bound` + Chebyshev; ~½ session).
* Item 4: writing the lattice rough part V_r (Wick quartics of the correlated Gaussian field
  φ = Aξ) as some F_c in independent standard Gaussians ξ with |α| ≤ 4 and per-variable degree ≤ 4
  (triangularity x^j ∈ span{He_k : k ≤ j}, multinomial expansion of :(Σ_j A_{xj} ξ_j)⁴: via
  `wickPow_add_binomial`; transport of γⁿ under ξ ↦ Aξ; ~1 session).
* Better constants: ρ_m ≍ m^{−1/2} (true hypercontractivity) is not attempted; any polynomial
  rate suffices for Nelson's estimate on the route chosen in session 1.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory NNReal Finset
open scoped ENNReal

noncomputable section

namespace PP2Chaos2

open PP2Target PP2Chaos

/-! ## 1. An explicit admissible contraction parameter ρ_m -/

/-- P = Σ_{k=1}^4 He_k²/k! in closed form: P = t⁴/24 − t³/3 + 5t²/4 + 7/8, t = x². -/
theorem ch2_Pfun_eq (x : ℝ) :
    Pfun x = (x ^ 2) ^ 4 / 24 - (x ^ 2) ^ 3 / 3 + 5 * (x ^ 2) ^ 2 / 4 + 7 / 8 := by
  simp only [Pfun, He, wickPow_one, wickPow_two, wickPow_three, wickPow_four']
  ring

/-- P ≤ (1 + x²)⁴ pointwise. -/
theorem ch2_Pfun_le (x : ℝ) : Pfun x ≤ (1 + x ^ 2) ^ 4 := by
  rw [ch2_Pfun_eq]
  have ht : 0 ≤ x ^ 2 := sq_nonneg x
  set t := x ^ 2
  nlinarith [pow_nonneg ht 3, pow_nonneg ht 4, sq_nonneg t]

theorem ch2_polyFn_id : PolyFn (fun x => x) := ⟨Polynomial.X, fun x => by simp⟩

theorem ch2_moment_succ (j : ℕ) :
    ∫ x, x ^ (2 * (j + 1)) ∂gaussianReal 0 1 =
      (2 * (j : ℝ) + 1) * ∫ x, x ^ (2 * j) ∂gaussianReal 0 1 := by
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, gaussian_moment_succ_succ]
  push_cast; ring

/-- E_γ x^{2j} ≤ (2K)^j for j ≤ K. -/
theorem ch2_moment_le (K : ℕ) : ∀ j, j ≤ K →
    ∫ x, x ^ (2 * j) ∂gaussianReal 0 1 ≤ (2 * (K : ℝ)) ^ j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [ch2_moment_succ, pow_succ]
    have h1 := ih (by omega)
    have h0 : 0 ≤ ∫ x, x ^ (2 * j) ∂gaussianReal 0 1 :=
      integral_nonneg (fun x => by rw [pow_mul]; positivity)
    have h2 : 2 * (j : ℝ) + 1 ≤ 2 * K := by
      have : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
      linarith
    have hK : 0 ≤ (2 * (K : ℝ)) ^ j := by positivity
    calc (2 * (j : ℝ) + 1) * ∫ x, x ^ (2 * j) ∂gaussianReal 0 1
        ≤ (2 * K) * (2 * (K : ℝ)) ^ j := mul_le_mul h2 h1 h0 (by positivity)
      _ = (2 * (K : ℝ)) ^ j * (2 * K) := by ring

/-- E_γ (1 + x²)^N ≤ (1 + 2N)^N. -/
theorem ch2_moment_one_add_sq (N : ℕ) :
    ∫ x, (1 + x ^ 2) ^ N ∂gaussianReal 0 1 ≤ (1 + 2 * (N : ℝ)) ^ N := by
  have hexp : ∀ x : ℝ, (1 + x ^ 2) ^ N =
      ∑ j ∈ range (N + 1), (N.choose j : ℝ) * x ^ (2 * j) := by
    intro x
    rw [add_comm, add_pow]
    refine sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, ← pow_mul, mul_comm]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun j _ => (integrable_pow_gaussianReal 1 _).const_mul _)]
  simp_rw [integral_const_mul]
  rw [add_comm (1 : ℝ), add_pow]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [one_pow, mul_one, mul_comm ((2 * (N : ℝ)) ^ j)]
  exact mul_le_mul_of_nonneg_left (ch2_moment_le N j (by simp at hj; omega)) (by positivity)

/-- E_γ P^j ≤ (1 + 8j)^{4j}. -/
theorem ch2_int_Pfun_pow (j : ℕ) :
    ∫ x, Pfun x ^ j ∂gaussianReal 0 1 ≤ (1 + 8 * (j : ℝ)) ^ (4 * j) := by
  have hmono : ∫ x, Pfun x ^ j ∂gaussianReal 0 1 ≤
      ∫ x, (1 + x ^ 2) ^ (4 * j) ∂gaussianReal 0 1 := by
    refine integral_mono (Pfun_polyFn.pow j).integrable
      (((PolyFn.const 1).add (ch2_polyFn_id.pow 2)).pow _).integrable (fun x => ?_)
    show Pfun x ^ j ≤ (1 + x ^ 2) ^ (4 * j)
    rw [pow_mul]
    exact pow_le_pow_left₀ (Pfun_nonneg x) (ch2_Pfun_le x) j
  refine hmono.trans ?_
  have := ch2_moment_one_add_sq (4 * j)
  push_cast at this
  convert this using 2
  ring

/-- (1 + t)^m ≤ 3 + ((m+1) t)^m for t ≥ 0 (split at m t = 1). -/
theorem ch2_one_add_pow_le (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ m ≤ 3 + (((m : ℝ) + 1) * t) ^ m := by
  have h4 : 0 ≤ (((m : ℝ) + 1) * t) ^ m := by positivity
  by_cases h : (m : ℝ) * t ≤ 1
  · have h1 : (1 + t) ^ m ≤ Real.exp t ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) m
    rw [← Real.exp_nat_mul] at h1
    have h2 : Real.exp (m * t) ≤ Real.exp 1 := Real.exp_le_exp.mpr h
    have h3 := Real.exp_one_lt_d9
    linarith
  · push Not at h
    have h5 : 1 + t ≤ ((m : ℝ) + 1) * t := by nlinarith
    have := pow_le_pow_left₀ (by linarith) h5 m
    linarith

theorem ch2_split (m : ℕ) (ρ P : ℝ) (hP : 0 ≤ P) :
    P * (1 + ρ ^ 2 * P) ^ m ≤ 3 * P + (((m : ℝ) + 1) * ρ ^ 2) ^ m * P ^ (m + 1) := by
  have h := ch2_one_add_pow_le m (ρ ^ 2 * P) (by positivity)
  calc P * (1 + ρ ^ 2 * P) ^ m ≤ P * (3 + (((m : ℝ) + 1) * (ρ ^ 2 * P)) ^ m) :=
        mul_le_mul_of_nonneg_left h hP
    _ = 3 * P + (((m : ℝ) + 1) * ρ ^ 2) ^ m * P ^ (m + 1) := by
        rw [mul_pow, mul_pow, mul_pow, pow_succ]; ring

theorem ch2_int_bound (m : ℕ) (ρ : ℝ) :
    ∫ x, Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m ∂gaussianReal 0 1 ≤
      3 * 6561 + (((m : ℝ) + 1) * ρ ^ 2) ^ m * (1 + 8 * ((m : ℝ) + 1)) ^ (4 * (m + 1)) := by
  have hQ : PolyFn (fun x => Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m) :=
    Pfun_polyFn.mul (((PolyFn.const 1).add (Pfun_polyFn.const_mul (ρ ^ 2))).pow m)
  have hA := (Pfun_polyFn.const_mul 3).integrable
  have hB := ((Pfun_polyFn.pow (m + 1)).const_mul ((((m : ℝ) + 1) * ρ ^ 2) ^ m)).integrable
  have h1 := ch2_int_Pfun_pow 1
  have h2 := ch2_int_Pfun_pow (m + 1)
  simp only [pow_one] at h1
  norm_num at h1
  push_cast at h2
  have hc : 0 ≤ (((m : ℝ) + 1) * ρ ^ 2) ^ m := by positivity
  calc _ ≤ ∫ x, (3 * Pfun x + (((m : ℝ) + 1) * ρ ^ 2) ^ m * Pfun x ^ (m + 1))
          ∂gaussianReal 0 1 :=
        integral_mono hQ.integrable (hA.add hB) (fun x => ch2_split m ρ (Pfun x) (Pfun_nonneg x))
    _ = 3 * ∫ x, Pfun x ∂gaussianReal 0 1 + (((m : ℝ) + 1) * ρ ^ 2) ^ m *
          ∫ x, Pfun x ^ (m + 1) ∂gaussianReal 0 1 := by
        rw [integral_add hA hB, integral_const_mul, integral_const_mul]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h2 hc]

/-- **Admissibility.** If 52488 (m+1)⁶ ρ² ≤ 1 then ρ satisfies the hypothesis of
`oneDim_moment`: (m+1)(2m+1) ρ² E_γ[P(1+ρ²P)^m] ≤ 1. -/
theorem ch2_admissible (m : ℕ) (ρ : ℝ) (hρ2 : 52488 * ((m : ℝ) + 1) ^ 6 * ρ ^ 2 ≤ 1) :
    ((m : ℝ) + 1) * (2 * m + 1) * ρ ^ 2 *
      ∫ x, Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m ∂gaussianReal 0 1 ≤ 1 := by
  have hI := ch2_int_bound m ρ
  set I := ∫ x, Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m ∂gaussianReal 0 1
  set M : ℝ := (m : ℝ) + 1 with hM_def
  have hM : 1 ≤ M := by simp [hM_def]
  have hM4 : 1 ≤ M ^ 4 := one_le_pow₀ hM
  set q : ℝ := 6561 * M ^ 4 with hq_def
  have hq : 6561 ≤ q := by nlinarith
  have hr : 8 * q * M ^ 2 * ρ ^ 2 ≤ 1 := by
    have : 8 * q * M ^ 2 * ρ ^ 2 = 52488 * M ^ 6 * ρ ^ 2 := by rw [hq_def]; ring
    rw [this]; exact hρ2
  have hρ2' : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  -- (8M+1)^{4(m+1)} ≤ q^{m+1}
  have hA : (1 + 8 * M) ^ (4 * (m + 1)) ≤ q ^ (m + 1) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (1 + 8 * M) ^ 4 ≤ (9 * M) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    rw [hq_def]; nlinarith
  have hMq : M * ρ ^ 2 * q ≤ 1 := by
    have : M * ρ ^ 2 * q ≤ 8 * q * M ^ 2 * ρ ^ 2 := by
      have h0 : 0 ≤ M * ρ ^ 2 * q := by positivity
      nlinarith
    linarith
  have hB : (M * ρ ^ 2) ^ m * q ^ (m + 1) ≤ q := by
    have e : ∀ a b : ℝ, a ^ m * b ^ (m + 1) = b * (a * b) ^ m := by
      intro a b; rw [mul_pow, pow_succ]; ring
    rw [e]
    have : (M * ρ ^ 2 * q) ^ m ≤ 1 := pow_le_one₀ (by positivity) hMq
    nlinarith [show (0 : ℝ) ≤ q by positivity]
  have hI' : I ≤ 4 * q := by
    have hc : 0 ≤ (M * ρ ^ 2) ^ m := by positivity
    have := mul_le_mul_of_nonneg_left hA hc
    linarith
  have hpre : 0 ≤ M * (2 * m + 1) * ρ ^ 2 := by positivity
  calc M * (2 * m + 1) * ρ ^ 2 * I ≤ M * (2 * m + 1) * ρ ^ 2 * (4 * q) :=
        mul_le_mul_of_nonneg_left hI' hpre
    _ ≤ M * (2 * M) * ρ ^ 2 * (4 * q) := by
        have : (2 * (m : ℝ) + 1) ≤ 2 * M := by rw [hM_def]; linarith
        have h0 : 0 ≤ M * ρ ^ 2 * (4 * q) := by positivity
        nlinarith
    _ = 8 * q * M ^ 2 * ρ ^ 2 := by ring
    _ ≤ 1 := hr

/-- The explicit contraction parameter ρ_m = 1 / (230 (m+1)³). -/
def ch2_rho (m : ℕ) : ℝ := 1 / (230 * ((m : ℝ) + 1) ^ 3)

theorem ch2_rho_nonneg (m : ℕ) : 0 ≤ ch2_rho m := by unfold ch2_rho; positivity

theorem ch2_rho_pos (m : ℕ) : 0 < ch2_rho m := by unfold ch2_rho; positivity

theorem ch2_rho_le_one (m : ℕ) : ch2_rho m ≤ 1 := by
  unfold ch2_rho
  have : 1 ≤ ((m : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rw [div_le_one (by positivity)]
  linarith

theorem ch2_rho_sq (m : ℕ) : 52488 * ((m : ℝ) + 1) ^ 6 * ch2_rho m ^ 2 ≤ 1 := by
  unfold ch2_rho
  have hM : 0 < ((m : ℝ) + 1) := by positivity
  rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
  have : (230 * ((m : ℝ) + 1) ^ 3) ^ 2 = 52900 * ((m : ℝ) + 1) ^ 6 := by ring
  rw [this]
  nlinarith [pow_pos hM 6]

/-- **One-dimensional hypercontractive step with explicit ρ_m = 1/(230 (m+1)³).** -/
theorem oneDim_moment' (m : ℕ) (b : Fin 5 → ℝ) :
    ∫ x, hpoly (ch2_rho m) b x ^ (2 * m + 2) ∂gaussianReal 0 1 ≤ hnorm b ^ (m + 1) :=
  oneDim_moment m (ch2_rho m) (ch2_rho_nonneg m) (ch2_rho_le_one m)
    (ch2_admissible m (ch2_rho m) (ch2_rho_sq m)) b

/-- More generally every 0 ≤ ρ ≤ ρ_m is admissible. -/
theorem oneDim_moment_le_rho (m : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ch2_rho m)
    (b : Fin 5 → ℝ) :
    ∫ x, hpoly ρ b x ^ (2 * m + 2) ∂gaussianReal 0 1 ≤ hnorm b ^ (m + 1) := by
  refine oneDim_moment m ρ hρ0 (hρ.trans (ch2_rho_le_one m)) (ch2_admissible m ρ ?_) b
  have h := ch2_rho_sq m
  have : ρ ^ 2 ≤ ch2_rho m ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
  have h0 : 0 ≤ 52488 * ((m : ℝ) + 1) ^ 6 := by positivity
  nlinarith

/-! ## 2. n variables: definitions and the first-variable decomposition -/

/-- |α| = Σ_i α_i. -/
def ch2_deg {n : ℕ} (α : Fin n → Fin 5) : ℕ := ∑ i, (α i : ℕ)

/-- α! = Π_i α_i!. -/
def ch2_fact {n : ℕ} (α : Fin n → Fin 5) : ℝ := ∏ i, (((α i : ℕ).factorial : ℕ) : ℝ)

/-- F_{T_ρ c}(x) = Σ_α ρ^{|α|} c_α Π_i He_{α_i}(x_i). -/
def ch2_F (n : ℕ) (ρ : ℝ) (c : (Fin n → Fin 5) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ α : Fin n → Fin 5, ρ ^ ch2_deg α * c α * ∏ i, He (α i) (x i)

/-- Σ_α α! c_α². -/
def ch2_norm (n : ℕ) (c : (Fin n → Fin 5) → ℝ) : ℝ := ∑ α, ch2_fact α * c α ^ 2

/-- The standard Gaussian measure on ℝⁿ. -/
def ch2_gauss (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

/-- The coefficient slice c_k(β) = c(k, β). -/
def ch2_slice {n : ℕ} (c : (Fin (n + 1) → Fin 5) → ℝ) (k : Fin 5) : (Fin n → Fin 5) → ℝ :=
  fun β => c (Fin.cons k β)

theorem ch2_fact_pos {n : ℕ} (α : Fin n → Fin 5) : 0 < ch2_fact α := by
  unfold ch2_fact; positivity

theorem ch2_norm_nonneg (n : ℕ) (c : (Fin n → Fin 5) → ℝ) : 0 ≤ ch2_norm n c := by
  unfold ch2_norm
  exact Finset.sum_nonneg fun α _ => mul_nonneg (ch2_fact_pos α).le (sq_nonneg _)

theorem ch2_sum_cons {n : ℕ} (f : (Fin (n + 1) → Fin 5) → ℝ) :
    ∑ α, f α = ∑ k : Fin 5, ∑ β : Fin n → Fin 5, f (Fin.cons k β) := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  rfl

theorem ch2_F_cons (n : ℕ) (ρ : ℝ) (c : (Fin (n + 1) → Fin 5) → ℝ) (x₀ : ℝ) (y : Fin n → ℝ) :
    ch2_F (n + 1) ρ c (Fin.cons x₀ y) = hpoly ρ (fun k => ch2_F n ρ (ch2_slice c k) y) x₀ := by
  unfold ch2_F hpoly
  rw [ch2_sum_cons]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, sum_mul]
  refine sum_congr rfl fun β _ => ?_
  simp only [ch2_deg, ch2_slice, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, pow_add]
  ring

theorem ch2_norm_succ (n : ℕ) (c : (Fin (n + 1) → Fin 5) → ℝ) :
    ch2_norm (n + 1) c = ∑ k : Fin 5, ((k : ℕ).factorial : ℝ) * ch2_norm n (ch2_slice c k) := by
  unfold ch2_norm
  rw [ch2_sum_cons]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun β _ => ?_
  simp only [ch2_fact, ch2_slice, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem ch2_He_continuous (k : ℕ) : Continuous (fun x => He k x) := by
  obtain ⟨q, hq⟩ := He_polyFn k
  have : (fun x => He k x) = fun x => q.eval x := funext hq
  rw [this]; exact q.continuous

theorem ch2_F_continuous (n : ℕ) (ρ : ℝ) (c : (Fin n → Fin 5) → ℝ) :
    Continuous (ch2_F n ρ c) := by
  unfold ch2_F
  refine continuous_finsetSum _ fun α _ => continuous_const.mul ?_
  exact continuous_finsetProd _ fun i _ => (ch2_He_continuous _).comp (continuous_apply i)

end PP2Chaos2

end

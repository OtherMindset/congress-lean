import LongTable.P_mwxoi1e4_u87l3j

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Chaos3.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction. Node G2 (M5 plan), remainder:
stretched-exponential tails for Wick polynomials in finitely many independent standard Gaussians,
reindexing to an arbitrary finite index type, and the bridge from `MvPolynomial` to the Hermite
expansions `ch2_F` of `LongTable.PP2Chaos2`.

Notation as in `PP2Chaos2`: γⁿ = `ch2_gauss n`, F_c = `ch2_F n 1 c`, N(c) = `ch2_norm n c`
(= E F_c², `ch2_L2`), ρ_m = `ch2_rho m` = 1/(230 (m+1)³), γ^ι = `Measure.pi (fun _ : ι => γ)`.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `ch3_degree_lintegral`: lintegral form of `ch2_degree_bound`.
* `ch3_markov`: c supported on |α| ≤ d, t > 0 ⇒ γⁿ{t ≤ |F_c|} ≤ (ρ_m^{−2d} N(c) / t²)^{m+1}.
* `ch3_tail` (**tail bound**): c supported on |α| ≤ d, s > 0 ⇒
    γⁿ{s √N(c) < |F_c|} ≤ e · exp(−(s / (e · 230^d))^{1/(3d)})
  (m+1 = ⌊(s/(e 230^d))^{1/(3d)}⌋ in `ch3_markov`; the case N(c) = 0 is handled separately).
* `ch3_x_pow_eq`: x^j = Σ_{k ≤ j} a_{jk} He_k(x) for j ≤ 4 (triangular table `ch3_tri`).
* `ch3_bridge` (**bridge**): P : MvPolynomial (Fin n) ℝ with totalDegree ≤ d and every
  degreeOf ≤ 4 ⇒ ∃ c supported on |α| ≤ d with eval x P = F_c(x) for all x.
* `ch3_tail_mvPoly` (**reindexed tail bound**): for any Fintype ι and P : MvPolynomial ι ℝ with
  totalDegree ≤ d and per-variable degree ≤ 4,
    γ^ι{ξ | s ‖P‖_{L²(γ^ι)} < |P(ξ)|} ≤ e · exp(−(s / (e · 230^d))^{1/(3d)}),
  via `Fintype.equivFin`, `MvPolynomial.rename`, `measurePreserving_piCongrLeft`.
  `ch3_tail_mvPoly_deg4`: the same with only totalDegree ≤ d ≤ 4 assumed.
  `ch3_moment_mvPoly`: E_{γ^ι}[P^{2m+2}] ≤ (ρ_m^{−2d} E_{γ^ι}[P²])^{m+1} for such P.

NOT formalized: per-variable degree > 4 (ch2 uses the Hermite basis He_0..He_4 per variable;
products of two quartics need He_0..He_8 and a re-run of the 1-D step of `PP2Chaos2`).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory NNReal Finset
open scoped ENNReal

noncomputable section

namespace PP2Chaos3

open PP2Target PP2Chaos PP2Chaos2

/-! ## 1. Moment bound in lintegral form, Markov -/

theorem ch3_degree_lintegral (m d n : ℕ) (c : (Fin n → Fin 5) → ℝ)
    (hc : ∀ α, d < ch2_deg α → c α = 0) :
    ∫⁻ x, ENNReal.ofReal (ch2_F n 1 c x ^ (2 * m + 2)) ∂ch2_gauss n ≤
      ENNReal.ofReal ((ch2_rho m)⁻¹ ^ (2 * d) * ch2_norm n c) ^ (m + 1) := by
  set ρ := ch2_rho m with hρ
  have hρ0 : 0 < ρ := ch2_rho_pos m
  have hρi : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ0 |>.mpr (ch2_rho_le_one m)
  set c' : (Fin n → Fin 5) → ℝ := fun α => ρ⁻¹ ^ ch2_deg α * c α with hc'
  have hF : ∀ x, ch2_F n ρ c' x = ch2_F n 1 c x := by
    intro x
    unfold ch2_F
    refine sum_congr rfl fun α _ => ?_
    rw [hc', one_pow, one_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ0.ne',
      one_pow, one_mul]
  have hN : ch2_norm n c' ≤ ρ⁻¹ ^ (2 * d) * ch2_norm n c := by
    unfold ch2_norm
    rw [mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    rw [hc']
    dsimp only
    by_cases h : d < ch2_deg α
    · rw [hc α h]; simp
    · push Not at h
      have hp : ρ⁻¹ ^ (2 * ch2_deg α) ≤ ρ⁻¹ ^ (2 * d) := pow_le_pow_right₀ hρi (by omega)
      have hf := (ch2_fact_pos α).le
      calc ch2_fact α * (ρ⁻¹ ^ ch2_deg α * c α) ^ 2
          = ρ⁻¹ ^ (2 * ch2_deg α) * (ch2_fact α * c α ^ 2) := by rw [pow_mul]; ring
        _ ≤ ρ⁻¹ ^ (2 * d) * (ch2_fact α * c α ^ 2) :=
          mul_le_mul_of_nonneg_right hp (mul_nonneg hf (sq_nonneg _))
  have h := ch2_hyper_lintegral m ρ hρ0.le (ch2_rho_le_one m)
    (ch2_admissible m ρ (ch2_rho_sq m)) n c'
  simp_rw [hF] at h
  exact h.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hN) _)

/-- **Markov on the (2m+2)-th moment.** -/
theorem ch3_markov (m d n : ℕ) (c : (Fin n → Fin 5) → ℝ)
    (hc : ∀ α, d < ch2_deg α → c α = 0) (t : ℝ) (ht : 0 < t) :
    ch2_gauss n {x | t ≤ |ch2_F n 1 c x|} ≤
      ENNReal.ofReal (((ch2_rho m)⁻¹ ^ (2 * d) * ch2_norm n c / t ^ 2) ^ (m + 1)) := by
  set B := (ch2_rho m)⁻¹ ^ (2 * d) * ch2_norm n c with hB
  have hB0 : 0 ≤ B := mul_nonneg (pow_nonneg (inv_nonneg.mpr (ch2_rho_nonneg m)) _)
    (ch2_norm_nonneg n c)
  have htk : 0 < t ^ (2 * m + 2) := pow_pos ht _
  have hmk := mul_meas_ge_le_lintegral₀ (μ := ch2_gauss n)
    (ch2_measurable_ofReal_F n 1 c (2 * m + 2)).aemeasurable (ENNReal.ofReal (t ^ (2 * m + 2)))
  have hsub : {x | t ≤ |ch2_F n 1 c x|} ⊆
      {x | ENNReal.ofReal (t ^ (2 * m + 2)) ≤ ENNReal.ofReal (ch2_F n 1 c x ^ (2 * m + 2))} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    apply ENNReal.ofReal_le_ofReal
    have := pow_le_pow_left₀ ht.le hx (2 * m + 2)
    rwa [Even.pow_abs ⟨m + 1, by ring⟩] at this
  have h1 : ENNReal.ofReal (t ^ (2 * m + 2)) * ch2_gauss n {x | t ≤ |ch2_F n 1 c x|} ≤
      ENNReal.ofReal (B ^ (m + 1)) := by
    calc _ ≤ _ := mul_le_mul_right (measure_mono hsub) _
      _ ≤ _ := hmk
      _ ≤ _ := ch3_degree_lintegral m d n c hc
      _ = _ := (ENNReal.ofReal_pow hB0 _).symm
  have h2 : ch2_gauss n {x | t ≤ |ch2_F n 1 c x|} ≤
      ENNReal.ofReal (B ^ (m + 1)) / ENNReal.ofReal (t ^ (2 * m + 2)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using htk)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact h1
  refine h2.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos htk, div_pow, ← pow_mul]
  congr 3

/-! ## 2. The stretched-exponential tail -/

theorem ch3_rho_inv (m : ℕ) : (ch2_rho m)⁻¹ = 230 * ((m : ℝ) + 1) ^ 3 := by
  unfold ch2_rho; rw [one_div, inv_inv]

/-- **Tail bound.** For c supported on |α| ≤ d and s > 0,
γⁿ{s ‖F_c‖₂ < |F_c|} ≤ e · exp(−(s/(e·230^d))^{1/(3d)}). -/
theorem ch3_tail (d n : ℕ) (c : (Fin n → Fin 5) → ℝ)
    (hc : ∀ α, d < ch2_deg α → c α = 0) (s : ℝ) (hs : 0 < s) :
    ch2_gauss n {x | s * √(ch2_norm n c) < |ch2_F n 1 c x|} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(s / (Real.exp 1 * 230 ^ d)) ^ ((1 : ℝ) / (3 * d)))) := by
  set N := ch2_norm n c with hNdef
  have hN0 : 0 ≤ N := ch2_norm_nonneg n c
  rcases hN0.eq_or_lt with hN | hN
  · -- N = 0: F_c = 0 a.e.
    have hL := ch2_L2_lintegral n c
    rw [← hNdef, ← hN, ENNReal.ofReal_zero,
      lintegral_eq_zero_iff (ch2_measurable_ofReal_F n 1 c 2)] at hL
    have hae : ∀ᵐ x ∂ch2_gauss n, ch2_F n 1 c x = 0 := by
      filter_upwards [hL] with x hx
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hx (sq_nonneg _))
    have h0 : ch2_gauss n {x | s * √N < |ch2_F n 1 c x|} = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hae)
      intro x hx
      simp only [Set.mem_ofPred_eq, ← hN, Real.sqrt_zero, mul_zero] at hx ⊢
      exact abs_pos.mp hx
    rw [h0]; exact zero_le
  set x0 := s / (Real.exp 1 * 230 ^ d) with hx0
  have hx00 : 0 ≤ x0 := by positivity
  set u := x0 ^ ((1 : ℝ) / (3 * d)) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx00 _
  rcases le_or_gt u 1 with hu1 | hu1
  · -- trivial regime: the right side is ≥ 1
    refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hd : d ≠ 0 := by
    rintro rfl
    simp [hu] at hu1
  set M := ⌊u⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hu1.le)
  have hMu : (M : ℝ) ≤ u := Nat.floor_le hu0
  have hMu' : u < (M : ℝ) + 1 := Nat.lt_floor_add_one u
  set m := M - 1 with hm
  have hmM : (m : ℝ) + 1 = M := by
    rw [hm]; norm_cast; omega
  have hupow : u ^ (3 * d) = x0 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx00]
    have : (1 : ℝ) / (3 * d) * ((3 * d : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  -- K^d ≤ s / e
  set K := (ch2_rho m)⁻¹ with hK
  have hKd : Real.exp 1 * K ^ d ≤ s := by
    rw [hK, ch3_rho_inv, hmM, mul_pow, ← pow_mul]
    have h1 : (M : ℝ) ^ (3 * d) ≤ x0 := hupow ▸ pow_le_pow_left₀ (by positivity) hMu _
    have he : 0 < Real.exp 1 * 230 ^ d := by positivity
    have h2 : Real.exp 1 * (230 ^ d * (M : ℝ) ^ (3 * d)) =
        (Real.exp 1 * 230 ^ d) * (M : ℝ) ^ (3 * d) := by ring
    rw [h2]
    calc (Real.exp 1 * 230 ^ d) * (M : ℝ) ^ (3 * d) ≤ (Real.exp 1 * 230 ^ d) * x0 :=
          mul_le_mul_of_nonneg_left h1 he.le
      _ = s := by rw [hx0]; field_simp
  have hK0 : 0 ≤ K := inv_nonneg.mpr (ch2_rho_nonneg m)
  have hq0 : 0 ≤ K ^ d / s := div_nonneg (pow_nonneg hK0 _) hs.le
  have hq1 : K ^ d / s ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hs, Real.exp_neg]
    rw [inv_mul_eq_div, le_div_iff₀ (Real.exp_pos 1)]
    linarith [hKd]
  have ht : 0 < s * √N := mul_pos hs (Real.sqrt_pos.mpr hN)
  have hmk := ch3_markov m d n c hc (s * √N) ht
  have hsub : {x | s * √N < |ch2_F n 1 c x|} ⊆ {x | s * √N ≤ |ch2_F n 1 c x|} :=
    fun x hx => by simp only [Set.mem_ofPred_eq] at hx ⊢; exact hx.le
  refine (measure_mono hsub).trans (hmk.trans (ENNReal.ofReal_le_ofReal ?_))
  have hrw : K ^ (2 * d) * N / (s * √N) ^ 2 = (K ^ d / s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0, pow_mul', div_pow]
    field_simp
  rw [← hK, hrw]
  calc ((K ^ d / s) ^ 2) ^ (m + 1) ≤ (Real.exp (-1) ^ 2) ^ (m + 1) :=
        pow_le_pow_left₀ (pow_nonneg hq0 _) (pow_le_pow_left₀ hq0 hq1 _) _
    _ = Real.exp (-(2 * ((m : ℝ) + 1))) := by
        rw [← pow_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by rw [hmM]; linarith)
    _ ≤ Real.exp 1 * Real.exp (-u) :=
        le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp (by norm_num))


/-! ## 3. The bridge: monomials of per-variable degree ≤ 4 as Hermite expansions -/

/-- Triangular table: x^j = Σ_k a_{jk} He_k(x), a_{jk} = 0 for k > j. -/
def ch3_tri : Fin 5 → Fin 5 → ℝ :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 3, 0, 1, 0], ![3, 0, 6, 0, 1]]

theorem ch3_tri_zero (j k : Fin 5) (h : (j : ℕ) < k) : ch3_tri j k = 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [ch3_tri]

theorem ch3_x_pow_eq (j : Fin 5) (x : ℝ) : x ^ (j : ℕ) = ∑ k : Fin 5, ch3_tri j k * He k x := by
  fin_cases j <;>
    simp [Fin.sum_univ_five, ch3_tri, He, wickPow_zero', wickPow_one, wickPow_two, wickPow_three,
      wickPow_four']
  ring

/-- Coefficients of the monomial Π_i x_i^{σ_i} in the product Hermite basis. -/
def ch3_monoCoef {n : ℕ} (σ : Fin n → Fin 5) (α : Fin n → Fin 5) : ℝ :=
  ∏ i, ch3_tri (σ i) (α i)

theorem ch3_mono_eq {n : ℕ} (σ : Fin n → Fin 5) (x : Fin n → ℝ) :
    ∏ i, x i ^ (σ i : ℕ) = ch2_F n 1 (ch3_monoCoef σ) x := by
  simp_rw [ch3_x_pow_eq]
  rw [Fintype.prod_sum]
  unfold ch2_F ch3_monoCoef
  refine sum_congr rfl fun α _ => ?_
  rw [one_pow, one_mul, ← prod_mul_distrib]

theorem ch3_monoCoef_supp {n : ℕ} (σ α : Fin n → Fin 5) (h : ch3_monoCoef σ α ≠ 0) (i : Fin n) :
    (α i : ℕ) ≤ σ i := by
  by_contra hlt
  push Not at hlt
  exact (prod_ne_zero_iff.mp h) i (mem_univ _) (ch3_tri_zero _ _ hlt)

theorem ch3_F_sum {n : ℕ} {β : Type*} (S : Finset β) (g : β → ℝ)
    (c : β → (Fin n → Fin 5) → ℝ) (x : Fin n → ℝ) :
    ch2_F n 1 (fun α => ∑ b ∈ S, g b * c b α) x = ∑ b ∈ S, g b * ch2_F n 1 (c b) x := by
  unfold ch2_F
  simp_rw [one_pow, one_mul, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun α _ => by ring

/-- **Bridge.** A real polynomial in n variables of total degree ≤ d and degree ≤ 4 in each
variable is F_c for some c supported on |α| ≤ d. -/
theorem ch3_bridge (n d : ℕ) (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ d)
    (hP4 : ∀ i, P.degreeOf i ≤ 4) :
    ∃ c : (Fin n → Fin 5) → ℝ, (∀ α, d < ch2_deg α → c α = 0) ∧
      ∀ x, MvPolynomial.eval x P = ch2_F n 1 c x := by
  classical
  let τ : (Fin n →₀ ℕ) → Fin n → Fin 5 := fun σ i => ⟨min (σ i) 4, by omega⟩
  have hτ : ∀ σ ∈ P.support, ∀ i, ((τ σ i : Fin 5) : ℕ) = σ i := fun σ hσ i => by
    simp only [τ]
    exact min_eq_left ((MvPolynomial.monomial_le_degreeOf i hσ).trans (hP4 i))
  refine ⟨fun α => ∑ σ ∈ P.support, P.coeff σ * ch3_monoCoef (τ σ) α, ?_, ?_⟩
  · intro α hα
    refine sum_eq_zero fun σ hσ => ?_
    by_cases h : ch3_monoCoef (τ σ) α = 0
    · rw [h, mul_zero]
    exfalso
    have h1 : ch2_deg α ≤ ∑ i, σ i := by
      unfold ch2_deg
      exact sum_le_sum fun i _ => (ch3_monoCoef_supp _ _ h i).trans (hτ σ hσ i).le
    have h2 : ∑ i, σ i ≤ d := by
      have := MvPolynomial.le_totalDegree hσ
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
      omega
    omega
  · intro x
    rw [MvPolynomial.eval_eq', ch3_F_sum]
    refine sum_congr rfl fun σ hσ => ?_
    rw [← ch3_mono_eq]
    congr 1
    exact prod_congr rfl fun i _ => by rw [hτ σ hσ i]

/-! ## 4. Reindexing to an arbitrary finite index type -/

/-- Transfer: a polynomial in the Gaussians (ξ_i)_{i ∈ ι} has the law of some F_c in γⁿ. -/
theorem ch3_transfer {ι : Type*} [Fintype ι] (d : ℕ) (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ d) (hP4 : ∀ i, P.degreeOf i ≤ 4) :
    ∃ (n : ℕ) (c : (Fin n → Fin 5) → ℝ), (∀ α, d < ch2_deg α → c α = 0) ∧
      (∀ g : ℝ → ℝ, ∫ ξ, g (MvPolynomial.eval ξ P) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
        = ∫ x, g (ch2_F n 1 c x) ∂ch2_gauss n) ∧
      (∀ A : Set ℝ, (Measure.pi fun _ : ι => gaussianReal 0 1) {ξ | MvPolynomial.eval ξ P ∈ A}
        = ch2_gauss n {x | ch2_F n 1 c x ∈ A}) := by
  classical
  set n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  set Q : MvPolynomial (Fin n) ℝ := MvPolynomial.rename e P with hQ
  have hQd : Q.totalDegree ≤ d := (MvPolynomial.totalDegree_rename_le _ _).trans hP
  have hQ4 : ∀ j, Q.degreeOf j ≤ 4 := fun j => by
    rw [← e.apply_symm_apply j, hQ, MvPolynomial.degreeOf_rename_of_injective e.injective]
    exact hP4 _
  obtain ⟨c, hc, hcQ⟩ := ch3_bridge n d Q hQd hQ4
  let T := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm
  have hT : MeasurePreserving T (ch2_gauss n) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e.symm
  have hTx : ∀ x, MvPolynomial.eval (T x) P = ch2_F n 1 c x := by
    intro x
    rw [← hcQ, hQ, MvPolynomial.eval_rename]
    have hx : T x = x ∘ e := by
      funext i
      simp only [T, MeasurableEquiv.coe_piCongrLeft, Function.comp_apply,
      Equiv.piCongrLeft_apply_eq_cast, cast_eq, Equiv.symm_symm]
    rw [hx]
  refine ⟨n, c, hc, fun g => ?_, fun A => ?_⟩
  · rw [← hT.integral_comp']
    simp_rw [hTx]
  · rw [← hT.measure_preimage_equiv]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hTx]

/-- **Reindexed tail bound.** For P : MvPolynomial ι ℝ of total degree ≤ d and degree ≤ 4 in each
variable, under the product of standard Gaussians on ι → ℝ, and every s > 0,
P(|P(ξ)| > s ‖P‖₂) ≤ e · exp(−(s/(e·230^d))^{1/(3d)}). -/
theorem ch3_tail_mvPoly {ι : Type*} [Fintype ι] (d : ℕ) (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ d) (hP4 : ∀ i, P.degreeOf i ≤ 4) (s : ℝ) (hs : 0 < s) :
    (Measure.pi fun _ : ι => gaussianReal 0 1)
      {ξ | s * √(∫ η, MvPolynomial.eval η P ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        < |MvPolynomial.eval ξ P|} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(s / (Real.exp 1 * 230 ^ d)) ^ ((1 : ℝ) / (3 * d)))) := by
  obtain ⟨n, c, hc, hint, hmeas⟩ := ch3_transfer d P hP hP4
  rw [hint (fun y => y ^ 2), ch2_L2]
  have := hmeas {y | s * √(ch2_norm n c) < |y|}
  simp only [Set.mem_ofPred_eq] at this
  rw [this]
  exact ch3_tail d n c hc s hs

/-- The same for total degree d ≤ 4 (per-variable degree ≤ 4 is then automatic). -/
theorem ch3_tail_mvPoly_deg4 {ι : Type*} [Fintype ι] (d : ℕ) (hd : d ≤ 4) (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ d) (s : ℝ) (hs : 0 < s) :
    (Measure.pi fun _ : ι => gaussianReal 0 1)
      {ξ | s * √(∫ η, MvPolynomial.eval η P ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        < |MvPolynomial.eval ξ P|} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(s / (Real.exp 1 * 230 ^ d)) ^ ((1 : ℝ) / (3 * d)))) :=
  ch3_tail_mvPoly d P hP (fun i => ((P.degreeOf_le_totalDegree i).trans hP).trans hd) s hs

/-- **Reindexed moment bound:** E[P^{2m+2}] ≤ (ρ_m^{−2d} E[P²])^{m+1}. -/
theorem ch3_moment_mvPoly {ι : Type*} [Fintype ι] (m d : ℕ) (P : MvPolynomial ι ℝ)
    (hP : P.totalDegree ≤ d) (hP4 : ∀ i, P.degreeOf i ≤ 4) :
    ∫ ξ, MvPolynomial.eval ξ P ^ (2 * m + 2) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) ≤
      ((ch2_rho m)⁻¹ ^ (2 * d) *
        ∫ ξ, MvPolynomial.eval ξ P ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ^ (m + 1) := by
  obtain ⟨n, c, hc, hint, -⟩ := ch3_transfer d P hP hP4
  rw [hint (fun y => y ^ (2 * m + 2)), hint (fun y => y ^ 2)]
  exact ch2_degree_bound m d n c hc

end PP2Chaos3

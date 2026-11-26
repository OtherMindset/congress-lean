import LongTable.R_PP2Chaos2A

/-!
Part B of PP2Chaos2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Chaos2.lean)

FORMALIZED in this part (this session):
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

theorem ch2_hpoly_polyFn (ρ : ℝ) (b : Fin 5 → ℝ) : PolyFn (fun x => hpoly ρ b x) := by
  have : (fun x => hpoly ρ b x) = fun x => b 0 + (ρ * b 1 * He 1 x + ρ ^ 2 * b 2 * He 2 x
      + ρ ^ 3 * b 3 * He 3 x + ρ ^ 4 * b 4 * He 4 x) := funext (hpoly_eq ρ b)
  rw [this]
  exact (PolyFn.const _).add (((((He_polyFn 1).const_mul (ρ * b 1)).add
    ((He_polyFn 2).const_mul (ρ ^ 2 * b 2))).add ((He_polyFn 3).const_mul (ρ ^ 3 * b 3))).add
    ((He_polyFn 4).const_mul (ρ ^ 4 * b 4)))

instance ch2_gauss_prob (n : ℕ) : IsProbabilityMeasure (ch2_gauss n) := by
  unfold ch2_gauss; infer_instance

/-- Splitting off the first variable (Tonelli, rest outside). -/
theorem ch2_lintegral_succ (n : ℕ) (Φ : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂ch2_gauss (n + 1) =
      ∫⁻ y, ∫⁻ x₀, Φ (Fin.cons x₀ y) ∂gaussianReal 0 1 ∂ch2_gauss n := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
  have hmp' := MeasurePreserving.symm _ hmp
  have h1 := hmp'.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) Φ
  unfold ch2_gauss
  rw [← h1, lintegral_prod_symm (fun z => Φ ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm z))
    (hΦ.comp (MeasurableEquiv.measurable _)).aemeasurable]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
    Fin.insertNth_zero']


/-! ## 3. Minkowski for finite sums, and the one-dimensional step in lintegral form -/

/-- Minkowski's inequality in L^p (p ≥ 1) for a finite sum of ℝ≥0∞-valued functions. -/
theorem ch2_minkowski_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (p : ℝ)
    (hp : 1 ≤ p) (s : Finset ι) (f : ι → α → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ a, (∑ i ∈ s, f i a) ^ p ∂μ) ^ (1 / p) ≤ ∑ i ∈ s, (∫⁻ a, f i a ^ p ∂μ) ^ (1 / p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hp0 : 0 < p := by linarith
    simp [ENNReal.zero_rpow_of_pos hp0, hp0]
  | insert i s hi ih =>
    have hsum : AEMeasurable (fun a => ∑ j ∈ s, f j a) μ :=
      Finset.aemeasurable_fun_sum s (fun j _ => hf j)
    have h := ENNReal.lintegral_Lp_add_le (hf i) hsum hp
    simp only [Finset.sum_insert hi]
    exact h.trans (add_le_add_right ih _)

theorem ch2_pow_even_nonneg (a : ℝ) (m : ℕ) : 0 ≤ a ^ (2 * m + 2) := by
  rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; positivity

/-- `oneDim_moment` as a lintegral bound with the right side split into the five weights. -/
theorem ch2_oneDim_lintegral (m : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcond : ((m : ℝ) + 1) * (2 * m + 1) * ρ ^ 2 *
      ∫ x, Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m ∂gaussianReal 0 1 ≤ 1)
    (b : Fin 5 → ℝ) :
    ∫⁻ x, ENNReal.ofReal (hpoly ρ b x ^ (2 * m + 2)) ∂gaussianReal 0 1 ≤
      (∑ k : Fin 5, ENNReal.ofReal (((k : ℕ).factorial : ℝ) * b k ^ 2)) ^ (m + 1) := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((ch2_hpoly_polyFn ρ b).pow _).integrable
      (ae_of_all _ fun x => by show (0 : ℝ) ≤ _; exact ch2_pow_even_nonneg _ m),
    ← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity),
    ← ENNReal.ofReal_pow (Finset.sum_nonneg fun k _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (oneDim_moment m ρ hρ0 hρ1 hcond b)

/-- E_γ[(Σ_k b_k He_k)²] = Σ_k k! b_k². -/
theorem ch2_oneDim_L2 (b : Fin 5 → ℝ) : ∫ x, hpoly 1 b x ^ 2 ∂gaussianReal 0 1 = hnorm b := by
  have hexp : ∀ x, hpoly 1 b x ^ 2 = ∑ j : Fin 5, ∑ k : Fin 5,
      (b j * b k) * (wickPow 1 j x * wickPow 1 k x) := by
    intro x
    simp only [hpoly, one_pow, one_mul, sq, Finset.sum_mul_sum, He]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun (j : Fin 5) _ => integrable_finsetSum _
    (fun (k : Fin 5) _ => (integrable_wickPow_mul 1 1 1 (j : ℕ) (k : ℕ)).const_mul (b j * b k)))]
  have hin : ∀ j : Fin 5, ∫ x, ∑ k : Fin 5, (b j * b k) * (wickPow 1 j x * wickPow 1 k x)
      ∂gaussianReal 0 1 = ((j : ℕ).factorial : ℝ) * b j ^ 2 := by
    intro j
    rw [integral_finsetSum _ (fun (k : Fin 5) _ =>
      (integrable_wickPow_mul 1 1 1 (j : ℕ) (k : ℕ)).const_mul (b j * b k))]
    simp_rw [integral_const_mul]
    have ho : ∀ k : Fin 5, ∫ x, wickPow 1 j x * wickPow 1 k x ∂gaussianReal 0 1 =
        if j = k then ((j : ℕ).factorial : ℝ) else 0 := by
      intro k
      have := wickPow_orthogonal 1 j k (by have := j.isLt; omega) (by have := k.isLt; omega)
      simp only [NNReal.coe_one, one_pow, mul_one, Fin.val_inj] at this
      exact this
    simp_rw [ho]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  rw [sum_congr rfl fun j _ => hin j]
  rfl

/-! ## 4. The n-variable statements -/

theorem ch2_F_zero (ρ : ℝ) (c : (Fin 0 → Fin 5) → ℝ) (x : Fin 0 → ℝ) :
    ch2_F 0 ρ c x = c default := by
  simp [ch2_F, ch2_deg]
  exact congrArg c (Subsingleton.elim _ _)

theorem ch2_norm_zero (c : (Fin 0 → Fin 5) → ℝ) : ch2_norm 0 c = c default ^ 2 := by
  simp [ch2_norm, ch2_fact]
  exact congrArg (fun t => t ^ 2) (congrArg c (Subsingleton.elim _ _))

theorem ch2_measurable_ofReal_F (n : ℕ) (ρ : ℝ) (c : (Fin n → Fin 5) → ℝ) (j : ℕ) :
    Measurable (fun x => ENNReal.ofReal (ch2_F n ρ c x ^ j)) :=
  ENNReal.measurable_ofReal.comp ((ch2_F_continuous n ρ c).pow j).measurable

/-- **S(n), lintegral form.** If ρ satisfies the one-dimensional admissibility condition for m,
then for every n and every coefficient array c,
∫ F_{T_ρ c}^{2m+2} dγⁿ ≤ (Σ_α α! c_α²)^{m+1}. -/
theorem ch2_hyper_lintegral (m : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcond : ((m : ℝ) + 1) * (2 * m + 1) * ρ ^ 2 *
      ∫ x, Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m ∂gaussianReal 0 1 ≤ 1) :
    ∀ (n : ℕ) (c : (Fin n → Fin 5) → ℝ),
      ∫⁻ x, ENNReal.ofReal (ch2_F n ρ c x ^ (2 * m + 2)) ∂ch2_gauss n ≤
        ENNReal.ofReal (ch2_norm n c) ^ (m + 1) := by
  intro n
  induction n with
  | zero =>
    intro c
    simp only [ch2_F_zero, ch2_norm_zero, lintegral_const, measure_univ, mul_one]
    rw [← ENNReal.ofReal_pow (sq_nonneg _), ← pow_mul, show 2 * (m + 1) = 2 * m + 2 by ring]
  | succ n ih =>
    intro c
    set g : Fin 5 → (Fin n → ℝ) → ℝ≥0∞ := fun k y =>
      ENNReal.ofReal (((k : ℕ).factorial : ℝ) * ch2_F n ρ (ch2_slice c k) y ^ 2) with hg
    have hgm : ∀ k, Measurable (g k) := fun k =>
      ENNReal.measurable_ofReal.comp
        ((continuous_const.mul ((ch2_F_continuous n ρ _).pow 2)).measurable)
    rw [ch2_lintegral_succ n _ (ch2_measurable_ofReal_F _ ρ c _)]
    simp_rw [ch2_F_cons]
    have hin : ∀ y, ∫⁻ x₀, ENNReal.ofReal
        (hpoly ρ (fun k => ch2_F n ρ (ch2_slice c k) y) x₀ ^ (2 * m + 2)) ∂gaussianReal 0 1 ≤
        (∑ k, g k y) ^ (m + 1) :=
      fun y => ch2_oneDim_lintegral m ρ hρ0 hρ1 hcond _
    refine (lintegral_mono hin).trans ?_
    have hp1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have hp0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by linarith
    have hmink := ch2_minkowski_sum (μ := ch2_gauss n) ((m + 1 : ℕ) : ℝ) hp1 Finset.univ g
      (fun k => (hgm k).aemeasurable)
    simp only [ENNReal.rpow_natCast] at hmink
    have hk : ∀ k : Fin 5, (∫⁻ y, g k y ^ (m + 1) ∂ch2_gauss n) ^ (1 / ((m + 1 : ℕ) : ℝ)) ≤
        ENNReal.ofReal (((k : ℕ).factorial : ℝ) * ch2_norm n (ch2_slice c k)) := by
      intro k
      rw [one_div, ENNReal.rpow_inv_le_iff hp0, ENNReal.rpow_natCast]
      have hfac : (0 : ℝ) ≤ ((k : ℕ).factorial : ℝ) := by positivity
      have e1 : ∀ y, g k y ^ (m + 1) = ENNReal.ofReal (((k : ℕ).factorial : ℝ) ^ (m + 1)) *
          ENNReal.ofReal (ch2_F n ρ (ch2_slice c k) y ^ (2 * m + 2)) := by
        intro y
        rw [hg]
        dsimp only
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_pow,
          ← pow_mul, show 2 * (m + 1) = 2 * m + 2 by ring]
      simp_rw [e1]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc _ ≤ ENNReal.ofReal (((k : ℕ).factorial : ℝ) ^ (m + 1)) *
            ENNReal.ofReal (ch2_norm n (ch2_slice c k)) ^ (m + 1) := by
            gcongr
            exact ih _
        _ = _ := by rw [ENNReal.ofReal_mul hfac, mul_pow, ENNReal.ofReal_pow hfac]
    have hsum : ∑ k : Fin 5, (∫⁻ y, g k y ^ (m + 1) ∂ch2_gauss n) ^ (1 / ((m + 1 : ℕ) : ℝ)) ≤
        ENNReal.ofReal (ch2_norm (n + 1) c) := by
      rw [ch2_norm_succ, ENNReal.ofReal_sum_of_nonneg
        (fun k _ => mul_nonneg (by positivity) (ch2_norm_nonneg _ _))]
      exact Finset.sum_le_sum fun k _ => hk k
    have htot := hmink.trans hsum
    rw [one_div, ENNReal.rpow_inv_le_iff hp0, ENNReal.rpow_natCast] at htot
    exact htot

/-- **L² identity, lintegral form:** ∫ F_c² dγⁿ = Σ_α α! c_α². -/
theorem ch2_L2_lintegral : ∀ (n : ℕ) (c : (Fin n → Fin 5) → ℝ),
    ∫⁻ x, ENNReal.ofReal (ch2_F n 1 c x ^ 2) ∂ch2_gauss n = ENNReal.ofReal (ch2_norm n c) := by
  intro n
  induction n with
  | zero =>
    intro c
    simp only [ch2_F_zero, ch2_norm_zero, lintegral_const, measure_univ, mul_one]
  | succ n ih =>
    intro c
    rw [ch2_lintegral_succ n _ (ch2_measurable_ofReal_F _ 1 c _)]
    simp_rw [ch2_F_cons]
    have hin : ∀ y, ∫⁻ x₀, ENNReal.ofReal
        (hpoly 1 (fun k => ch2_F n 1 (ch2_slice c k) y) x₀ ^ 2) ∂gaussianReal 0 1 =
        ∑ k : Fin 5, ENNReal.ofReal ((k : ℕ).factorial : ℝ) *
          ENNReal.ofReal (ch2_F n 1 (ch2_slice c k) y ^ 2) := by
      intro y
      rw [← ofReal_integral_eq_lintegral_ofReal ((ch2_hpoly_polyFn 1 _).pow 2).integrable
          (ae_of_all _ fun x => by show (0 : ℝ) ≤ _; positivity),
        ch2_oneDim_L2, hnorm, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
      exact sum_congr rfl fun k _ => ENNReal.ofReal_mul (by positivity)
    simp_rw [hin]
    rw [lintegral_finsetSum _ (fun k _ => (ch2_measurable_ofReal_F _ 1 _ 2).const_mul _)]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ih]
    rw [ch2_norm_succ, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => mul_nonneg (by positivity) (ch2_norm_nonneg _ _))]
    exact sum_congr rfl fun k _ => (ENNReal.ofReal_mul (by positivity)).symm

/-- **L² identity:** E_{γⁿ}[F_c²] = Σ_α α! c_α². -/
theorem ch2_L2 (n : ℕ) (c : (Fin n → Fin 5) → ℝ) :
    ∫ x, ch2_F n 1 c x ^ 2 ∂ch2_gauss n = ch2_norm n c := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ch2_F n 1 c x ^ 2)
    (ae_of_all _ fun x => by show (0 : ℝ) ≤ _; positivity)
    ((ch2_F_continuous n 1 c).pow 2).aestronglyMeasurable, ch2_L2_lintegral,
    ENNReal.toReal_ofReal (ch2_norm_nonneg n c)]

/-- **S(n), Bochner form.** -/
theorem ch2_hyper (m : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcond : ((m : ℝ) + 1) * (2 * m + 1) * ρ ^ 2 *
      ∫ x, Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m ∂gaussianReal 0 1 ≤ 1)
    (n : ℕ) (c : (Fin n → Fin 5) → ℝ) :
    ∫ x, ch2_F n ρ c x ^ (2 * m + 2) ∂ch2_gauss n ≤ ch2_norm n c ^ (m + 1) := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ch2_F n ρ c x ^ (2 * m + 2))
    (ae_of_all _ fun x => by show (0 : ℝ) ≤ _; exact ch2_pow_even_nonneg _ m)
    ((ch2_F_continuous n ρ c).pow _).aestronglyMeasurable]
  have h := ch2_hyper_lintegral m ρ hρ0 hρ1 hcond n c
  rw [← ENNReal.ofReal_pow (ch2_norm_nonneg n c)] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (pow_nonneg (ch2_norm_nonneg n c) _)] at this

/-- **Hypercontractive moment bound with explicit ρ_m = 1/(230 (m+1)³), all n:**
E_{γⁿ}[F_{T_{ρ_m} c}^{2m+2}] ≤ (E_{γⁿ}[F_c²])^{m+1}. -/
theorem ch2_hyper_explicit (m n : ℕ) (c : (Fin n → Fin 5) → ℝ) :
    ∫ x, ch2_F n (ch2_rho m) c x ^ (2 * m + 2) ∂ch2_gauss n ≤
      (∫ x, ch2_F n 1 c x ^ 2 ∂ch2_gauss n) ^ (m + 1) := by
  rw [ch2_L2]
  exact ch2_hyper m (ch2_rho m) (ch2_rho_nonneg m) (ch2_rho_le_one m)
    (ch2_admissible m (ch2_rho m) (ch2_rho_sq m)) n c

/-- **Degree-d corollary.** If c is supported on |α| ≤ d then
E_{γⁿ}[F_c^{2m+2}] ≤ (ρ_m^{−2d} E_{γⁿ}[F_c²])^{m+1}, i.e. ‖F_c‖_{2m+2} ≤ ρ_m^{−d} ‖F_c‖₂. -/
theorem ch2_degree_bound (m d n : ℕ) (c : (Fin n → Fin 5) → ℝ)
    (hc : ∀ α, d < ch2_deg α → c α = 0) :
    ∫ x, ch2_F n 1 c x ^ (2 * m + 2) ∂ch2_gauss n ≤
      ((ch2_rho m)⁻¹ ^ (2 * d) * ∫ x, ch2_F n 1 c x ^ 2 ∂ch2_gauss n) ^ (m + 1) := by
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
  have h := ch2_hyper m ρ hρ0.le (ch2_rho_le_one m)
    (ch2_admissible m ρ (ch2_rho_sq m)) n c'
  simp_rw [hF] at h
  rw [ch2_L2]
  exact h.trans (pow_le_pow_left₀ (ch2_norm_nonneg n c') hN _)


end PP2Chaos2

import LongTable.Q_PP2SimonLieb2A

/-!
Part B of PP2SimonLieb2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb2.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* `tw_mass_shift`: W_τ = e^{−Σ f(τ_x)} · e^{−β Σ τ_x φ_x²} · W_0 (site mass² raised by 2βτ_x);
  `tw_le_tw_zero`: W_τ ≤ e^{−Σ f(τ_x)} W_0 for τ ≥ 0, β ≥ 0.
* `local_time_ibp` (abstract, any finite ι; b ≥ 0, b > 0 or a > 0, τ_i ≥ 0; R, R' continuous,
  R' the e_i-derivative of R; R, φ_i R, φ_i³ R, R' integrable against W_τ):
    ∫ φ_i R W_τ = ∫_{s>0} ∫ R' W_{τ+s e_i}.
  Proof: 1-D FTC on (0, ∞) in s (`integral_Ioi_tw`), Fubini (`integral_integral_swap`, with the
  explicit product dominator `ltG(φ) · C e^{−cs}`, `ltF_bound`, `exists_exp_bound`), and
  integration by parts in φ_i at each fixed s (`ibp_fixed`, Mathlib's line-derivative IBP).
* `local_time_ibp_bfs`: the same with R = G e^{quadE K}: [φ_i G]_τ = ∫_0^∞ ds
  [∂_i G + Σ_j (K_ij + K_ji) φ_j G]_{τ+s e_i}, for any K.

NOT formalized.
* Integrability in s of the integrand s ↦ [·]_{τ+s e_i}: it holds (Fubini in the proof) but is NOT
  exported here, so the displayed identities, read alone, do not assert integrability (a
  non-integrable integrand would give 0 on the right). [Exported later: `integrableOn_tI_shift`
  in PP2SimonLieb3.] Continuity in τ.
* G of exponential-quadratic growth (e.g. G = φ_y e^{bdryCoupling}, used in R5 for the DECOUPLED
  measure). Not needed if R5 applies R2 to the full measure with G = φ_y, since
  decWeight · e^{bdryCoupling} = qweight · const (`dweight_split`); otherwise the abstract
  `local_time_ibp_bfs` applies with the integrability hypotheses to be checked.
* (R3)–(R5).

A FINDING for (R4) [SUPERSEDED by PP2SimonLieb3: a weight e^{c'Στ} with c' > max row sum of J
gives the contraction on fine lattices too; the walk bound below is not needed]. With Wick ordering α = 4 + ε²(m₀² − 12λc), c = freeVar ~ (2π)⁻¹ log(1/ε), so
α < 4 = max_i Σ_j J_ij for all fine lattices when λ > 0: the weighted-sup-norm contraction of
`PP2SimonLieb` (R4) ("β' > 4, possible since α > 4") only works at λ = 0. The fix we propose:
|D(τ)| ≤ M e^{−Σ_x f(τ_x)} by `tw_le_tw_zero`, and f(τ + S) ≥ f(τ) + f(S) (β ≥ 0); the N-fold
iterate K^N is then bounded by a sum over N-step walks of Π_x ∫ S^{n_x−1}/(n_x−1)! e^{−f(S)} dS,
which for β > 0 decays superexponentially in the visit numbers n_x; in a FIXED finite box some
n_x ≥ N/|Λ|, so ‖K^N‖ → 0 and D⁻ ≤ K^N D⁻ → 0. No uniformity in the volume is needed for (R4).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2LocalTime

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {a b c C : ℝ}

/-- The local-time integral: ∫_0^∞ f'(u + s) W_{τ+s e_i} ds = W_τ (since W_{τ+s e_i} → 0). -/
theorem integral_Ioi_tw (hb : 0 ≤ b) (hc : 0 < c)
    (hC : ∀ s : ℝ, 0 ≤ s → (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) ≤ C * Real.exp (-c * s))
    {τ : ι → ℝ} {i : ι} (hτ : 0 ≤ τ i) (φ : ι → ℝ) :
    ∫ s in Ioi (0 : ℝ), fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ =
      tw a b τ φ := by
  have hhi : IntegrableOn (fun s : ℝ => C * Real.exp (-c * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul C
  have hderiv : ∀ s, HasDerivAt (fun s => -tw a b (τ + Pi.single i s) φ)
      (fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ) s := fun s => by
    have := (hasDerivAt_tw_shift a b τ φ i s).fun_neg
    convert this using 1; ring
  have hcs : Continuous (fun s => tw a b (τ + Pi.single i s) φ) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_tw_shift a b τ φ i s).continuousAt
  have hio : IntegrableOn (fun s => fq' a b (φ i ^ 2 / 2 + τ i + s) *
      tw a b (τ + Pi.single i s) φ) (Ioi 0) := by
    refine (hhi.const_mul (((|a| + 2 * b * τ i + 1) + b * φ i ^ 2) * tw a b τ φ)).mono' ?_ ?_
    · exact ((by unfold fq'; fun_prop : Continuous fun s => fq' a b (φ i ^ 2 / 2 + τ i + s)).mul
        hcs).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (tw_pos _ _ _ _)]
      exact (deriv_tw_shift_le hb hC hτ φ (le_of_lt hs)).trans (le_of_eq (by ring))
  have htend : Tendsto (fun s => -tw a b (τ + Pi.single i s) φ) atTop (𝓝 0) := by
    have he : Tendsto (fun s : ℝ => Real.exp (-c * s)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    have hlim : Tendsto (fun s => tw a b τ φ * (C * Real.exp (-c * s))) atTop (𝓝 0) := by
      simpa using (he.const_mul C).const_mul (tw a b τ φ)
    have h2 : Tendsto (fun s => tw a b (τ + Pi.single i s) φ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun s => (tw_pos _ _ _ _).le)
        ((eventually_ge_atTop 0).mono fun s hs => tw_shift_le hb hC hτ φ hs)
    simpa using h2.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun s _ => hderiv s) hio htend]
  simp

/-- **One-site local-time integration by parts** (abstract form). For W_τ = ∏_x e^{−f(φ_x²/2+τ_x)},
f(u) = au + bu² (b ≥ 0, and b > 0 or a > 0), τ_i ≥ 0, and R continuous with continuous derivative
R' along e_i and the stated integrability against W_τ:
  ∫ φ_i R W_τ = ∫_0^∞ ds ∫ R' · W_{τ + s e_i}. -/
theorem local_time_ibp (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a) (τ : ι → ℝ) (i : ι)
    (hτ : 0 ≤ τ i) {R R' : (ι → ℝ) → ℝ} (hRc : Continuous R) (hR'c : Continuous R')
    (hR' : ∀ φ, HasLineDerivAt ℝ R (R' φ) φ (Pi.single i 1))
    (h0 : Integrable (fun φ => R φ * tw a b τ φ))
    (h1 : Integrable (fun φ => φ i * R φ * tw a b τ φ))
    (h3 : Integrable (fun φ => φ i ^ 3 * R φ * tw a b τ φ))
    (hd : Integrable (fun φ => R' φ * tw a b τ φ)) :
    ∫ φ, φ i * R φ * tw a b τ φ =
      ∫ s in Ioi (0 : ℝ), ∫ φ, R' φ * tw a b (τ + Pi.single i s) φ := by
  obtain ⟨c, hc, C, hC⟩ := exists_exp_bound hb hab
  have hgi : Integrable (ltG a b τ i R) := (h1.abs.const_mul _).add (h3.abs.const_mul _)
  have hhi : IntegrableOn (fun s : ℝ => C * Real.exp (-c * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul C
  have hFc := continuous_ltF (a := a) (b := b) τ i hRc
  -- product integrability (Fubini)
  have hprod : Integrable (Function.uncurry (ltF a b τ i R))
      ((volume : Measure (ι → ℝ)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (hgi.mul_prod hhi).mono' hFc.aestronglyMeasurable ?_
    have hmem : ∀ᵐ z ∂((volume : Measure (ι → ℝ)).prod (volume.restrict (Ioi (0 : ℝ)))),
        z ∈ (Prod.snd ⁻¹' Ioi (0 : ℝ) : Set ((ι → ℝ) × ℝ)) := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurable_snd measurableSet_Ioi)]
      exact Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with z hz
    rw [Real.norm_eq_abs]
    exact ltF_bound hb hC hτ R z.1 (le_of_lt hz)
  -- the s-integral
  have hinner : ∀ φ, ∫ s in Ioi (0 : ℝ), ltF a b τ i R φ s = φ i * R φ * tw a b τ φ := by
    intro φ
    have e : (fun s => ltF a b τ i R φ s) = fun s => (R φ * φ i) *
        (fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ) := by
      funext s; unfold ltF; ring
    rw [e, integral_const_mul, integral_Ioi_tw hb hc hC hτ φ]
    ring
  -- the φ-integral at fixed s
  have hibp : ∀ s : ℝ, 0 ≤ s →
      ∫ φ, R' φ * tw a b (τ + Pi.single i s) φ = ∫ φ, ltF a b τ i R φ s := by
    intro s hs
    have hσi : (τ + Pi.single i s : ι → ℝ) i = τ i + s := by simp
    have e1 : ∀ φ, R φ * (φ i * fq' a b (φ i ^ 2 / 2 + (τ + Pi.single i s : ι → ℝ) i)) *
        tw a b (τ + Pi.single i s) φ = ltF a b τ i R φ s := by
      intro φ; rw [hσi, ← add_assoc]; unfold ltF; ring
    have hB : Integrable (fun φ => ltF a b τ i R φ s) := by
      refine (hgi.mul_const (C * Real.exp (-c * s))).mono'
        (hFc.comp (Continuous.prodMk continuous_id continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun φ => ?_)
      rw [Real.norm_eq_abs]; exact ltF_bound hb hC hτ R φ hs
    rw [ibp_fixed (τ + Pi.single i s) i hR' (integrable_shift hb hC hτ hR'c hd hs)
      (hB.congr (Filter.Eventually.of_forall fun φ => (e1 φ).symm))
      (integrable_shift hb hC hτ hRc h0 hs)]
    exact integral_congr_ae (Filter.Eventually.of_forall e1)
  calc ∫ φ, φ i * R φ * tw a b τ φ = ∫ φ, ∫ s in Ioi (0 : ℝ), ltF a b τ i R φ s := by
        simp_rw [hinner]
    _ = ∫ s in Ioi (0 : ℝ), ∫ φ, ltF a b τ i R φ s := integral_integral_swap hprod
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun s hs => (hibp s (le_of_lt hs)).symm

/-! ## The BFS form: a ferromagnetic pair interaction exp(Σ K φφ) -/

/-- The pair exponent Q_K(φ) = Σ_{x,y} K_xy φ_x φ_y. -/
def quadE (K : ι → ι → ℝ) (φ : ι → ℝ) : ℝ := ∑ x, ∑ y, K x y * φ x * φ y

@[fun_prop]
theorem continuous_quadE (K : ι → ι → ℝ) : Continuous (quadE K) := by
  unfold quadE; fun_prop

/-- ∂_i Q_K = Σ_j (K_ij + K_ji) φ_j. -/
theorem hasLineDerivAt_quadE (K : ι → ι → ℝ) (φ : ι → ℝ) (i : ι) :
    HasLineDerivAt ℝ (quadE K) (∑ j, (K i j + K j i) * φ j) φ (Pi.single i 1) := by
  unfold HasLineDerivAt quadE
  have h : ∀ x : ι, HasDerivAt (fun t : ℝ => (φ + t • (Pi.single i (1 : ℝ) : ι → ℝ)) x)
      ((Pi.single i (1 : ℝ) : ι → ℝ) x) 0 := by
    intro x
    have e : (fun t : ℝ => (φ + t • (Pi.single i (1 : ℝ) : ι → ℝ)) x) =
        fun t => φ x + t * (Pi.single i (1 : ℝ) : ι → ℝ) x := by
      funext t; simp
    rw [e]
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const ((Pi.single i (1 : ℝ) : ι → ℝ) x)).const_add
      (φ x)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun x _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun y _ => ((h x).const_mul (K x y)).fun_mul (h y)
  convert hs using 1
  simp only [zero_smul, add_zero, Finset.sum_add_distrib]
  have e1 : ∀ x, ∑ y, K x y * (Pi.single i (1 : ℝ) : ι → ℝ) x * φ y =
      if x = i then ∑ y, K i y * φ y else 0 := by
    intro x
    by_cases hx : x = i
    · subst hx; simp
    · simp [hx]
  have e2 : ∀ x, ∑ y, K x y * φ x * (Pi.single i (1 : ℝ) : ι → ℝ) y = K x i * φ x := by
    intro x
    rw [Finset.sum_eq_single i]
    · simp
    · intro y _ hy; simp [Pi.single_eq_of_ne hy]
    · simp
  simp only [e1, e2, Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_mul,
    Finset.sum_add_distrib]

/-- **Local-time integration by parts, BFS form.** With [F]_τ = ∫ F e^{Q_K} W_τ and J = K + Kᵀ:
  [φ_i G]_τ = ∫_0^∞ ds [∂_i G + Σ_j J_ij φ_j G]_{τ + s e_i}. -/
theorem local_time_ibp_bfs (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a) (K : ι → ι → ℝ) (τ : ι → ℝ)
    (i : ι) (hτ : 0 ≤ τ i) {G G' : (ι → ℝ) → ℝ} (hGc : Continuous G) (hG'c : Continuous G')
    (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1))
    (h0 : Integrable fun φ => G φ * Real.exp (quadE K φ) * tw a b τ φ)
    (h1 : Integrable fun φ => φ i * G φ * Real.exp (quadE K φ) * tw a b τ φ)
    (h3 : Integrable fun φ => φ i ^ 3 * G φ * Real.exp (quadE K φ) * tw a b τ φ)
    (hd : Integrable fun φ =>
      (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ) * tw a b τ φ) :
    ∫ φ, φ i * G φ * Real.exp (quadE K φ) * tw a b τ φ =
      ∫ s in Ioi (0 : ℝ), ∫ φ, (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) *
        Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ := by
  have hR' : ∀ φ, HasLineDerivAt ℝ (fun φ => G φ * Real.exp (quadE K φ))
      ((G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ)) φ
      (Pi.single i 1) := by
    intro φ
    have hQ := hasLineDerivAt_quadE K φ i
    have hG := hG' φ
    unfold HasLineDerivAt at hQ hG ⊢
    have := hG.fun_mul hQ.exp
    convert this using 1
    simp only [zero_smul, add_zero, Finset.mul_sum]
    rw [add_mul, Finset.sum_mul]
    have : ∀ j, (K i j + K j i) * (φ j * G φ) * Real.exp (quadE K φ) =
        G φ * (Real.exp (quadE K φ) * ((K i j + K j i) * φ j)) := fun j => by ring
    simp only [this]
  have := local_time_ibp hb hab τ i hτ (R := fun φ => G φ * Real.exp (quadE K φ))
    (R' := fun φ => (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ))
    (by fun_prop) (by fun_prop) hR'
    (by simpa only [mul_assoc] using h0) (by simpa only [mul_assoc] using h1)
    (by simpa only [mul_assoc] using h3) hd
  simpa only [mul_assoc] using this

/-! ## The τ-family as a mass shift -/

/-- W_τ = e^{−Σ_x f(τ_x)} · e^{−b Σ_x τ_x φ_x²} · W_0: raising the local time τ_x raises the
mass² at x by 2bτ_x (the coefficient of φ_x²/2), with the prefactor e^{−f(τ_x)}. -/
theorem tw_mass_shift (a b : ℝ) (τ φ : ι → ℝ) :
    tw a b τ φ = Real.exp (-∑ x, fq a b (τ x)) * Real.exp (-(b * ∑ x, τ x * φ x ^ 2)) *
      tw a b 0 φ := by
  unfold tw
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Pi.zero_apply, add_zero, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by unfold fq; ring

theorem tw_le_tw_zero (hb : 0 ≤ b) {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) (φ : ι → ℝ) :
    tw a b τ φ ≤ Real.exp (-∑ x, fq a b (τ x)) * tw a b 0 φ := by
  rw [tw_mass_shift]
  have h1 : Real.exp (-(b * ∑ x, τ x * φ x ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hb (Finset.sum_nonneg fun x _ => mul_nonneg (hτ x) (sq_nonneg _))
  have h2 := (tw_pos a b 0 φ).le
  have h3 := (Real.exp_pos (-∑ x, fq a b (τ x))).le
  calc _ ≤ Real.exp (-∑ x, fq a b (τ x)) * 1 * tw a b 0 φ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2
    _ = _ := by ring

/-! ## Growth classes -/

theorem abs_le_exp_sum (φ : ι → ℝ) (j : ι) : |φ j| ≤ Real.exp (∑ x, |φ x|) :=
  (Finset.single_le_sum (f := fun x => |φ x|) (fun x _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (by linarith [Real.add_one_le_exp (∑ x, |φ x|)])

theorem growth_mul_coord {G : (ι → ℝ) → ℝ} {C a : ℝ}
    (hG : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) (j : ι) (φ : ι → ℝ) :
    |φ j * G φ| ≤ C * Real.exp ((a + 1) * ∑ x, |φ x|) := by
  have hC : 0 ≤ C * Real.exp (a * ∑ x, |φ x|) := (abs_nonneg _).trans (hG φ)
  rw [abs_mul]
  calc |φ j| * |G φ| ≤ Real.exp (∑ x, |φ x|) * (C * Real.exp (a * ∑ x, |φ x|)) :=
        mul_le_mul (abs_le_exp_sum φ j) (hG φ) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [add_mul, one_mul, Real.exp_add]; ring

theorem growth_mul_cube {G : (ι → ℝ) → ℝ} {C a : ℝ}
    (hG : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) (j : ι) (φ : ι → ℝ) :
    |φ j ^ 3 * G φ| ≤ C * Real.exp ((a + 3) * ∑ x, |φ x|) := by
  have hC : 0 ≤ C * Real.exp (a * ∑ x, |φ x|) := (abs_nonneg _).trans (hG φ)
  have h3 : |φ j| ^ 3 ≤ Real.exp (3 * ∑ x, |φ x|) := by
    have := pow_le_pow_left₀ (abs_nonneg (φ j)) (abs_le_exp_sum φ j) 3
    rwa [← Real.exp_nat_mul, Nat.cast_ofNat] at this
  rw [abs_mul, abs_pow]
  calc |φ j| ^ 3 * |G φ| ≤ Real.exp (3 * ∑ x, |φ x|) * (C * Real.exp (a * ∑ x, |φ x|)) :=
        mul_le_mul h3 (hG φ) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [add_mul, Real.exp_add]; ring

/-! ## Evaluating quadratic forms on e_x and e_x + e_y -/

theorem quad_single (M : ι → ι → ℝ) (x : ι) :
    ∑ u, ∑ v, M u v * (Pi.single x (1 : ℝ) : ι → ℝ) u * (Pi.single x (1 : ℝ) : ι → ℝ) v =
      M x x := by
  simp [Pi.single_apply]

theorem quad_pair (M : ι → ι → ℝ) (x y : ι) :
    ∑ u, ∑ v, M u v * (Pi.single x (1 : ℝ) + Pi.single y (1 : ℝ) : ι → ℝ) u *
      (Pi.single x (1 : ℝ) + Pi.single y (1 : ℝ) : ι → ℝ) v =
      M x x + M x y + M y x + M y y := by
  simp [Pi.single_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem sq_single (x : ι) : ∑ u, (Pi.single x (1 : ℝ) : ι → ℝ) u ^ 2 = 1 := by
  simp [Pi.single_apply]

theorem sq_pair {x y : ι} (hxy : x ≠ y) :
    ∑ u, (Pi.single x (1 : ℝ) + Pi.single y (1 : ℝ) : ι → ℝ) u ^ 2 = 2 := by
  simp [Pi.single_apply, add_sq, Finset.sum_add_distrib, hxy.symm]
  norm_num

end PP2LocalTime

/-! ## The quartic Dirichlet-box model -/

namespace PP2Target

open PP2LocalTime PP2Griffiths

variable {n k : ℕ}

/-- α = 4 + ε² m₀² − 12 λ ε² c (c = freeVar): the coefficient of s = φ²/2 in the site exponent
(Dirichlet diagonal 4, mass, and the Wick counterterm −6λε²c φ²). -/
def alphaQ (n : ℕ) (m₀ lam : ℝ) : ℝ :=
  4 + spacing n ^ 2 * m₀ ^ 2 - 12 * lam * spacing n ^ 2 * freeVar n m₀

/-- β = 4 λ ε²: the coefficient of s² (λε² φ⁴ = 4λε² s²). -/
def betaQ (n : ℕ) (lam : ℝ) : ℝ := 4 * lam * spacing n ^ 2

/-- The symmetrised nearest-neighbour coupling J_ij = Jnn_ij + Jnn_ji (= ∂_i of the pair
exponent; 1 for nearest neighbours, 0 on the diagonal). -/
def Jsym (n k : ℕ) (x y : DSite n k) : ℝ := Jnn n k x y + Jnn n k y x

end PP2Target

end

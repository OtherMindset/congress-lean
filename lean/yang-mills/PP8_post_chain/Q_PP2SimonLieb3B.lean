import LongTable.Q_PP2SimonLieb3A

/-!
Part B of PP2SimonLieb3 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb3.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* (R3, local times) `tw_shift_mass`, `rhoQ_siteW`, **`tI_mono`** (K ≥ 0, b ≥ 0, τ ≤ τ', H ∈ 𝒞):
  [H]_{τ'}[1]_τ ≤ [H]_τ[1]_{τ'}; box form **`tauInt_mono`** (m₀ ≠ 0, λ ≥ 0, 0 ≤ τ ≤ τ',
  H ∈ 𝒞 ∩ Adm 1).
* (R2, abstract with envelope) `tI_ibp`, `integrable_adm`, `abs_tI_le`, `integrableOn_tI_shift`
  (s ↦ [H]_{τ+se_i} integrable on (0,∞): measurability by `StronglyMeasurable.integral_prod_right'`,
  decay by `tw_shift_le`; this closes the "NOT formalized" item of `PP2SimonLieb2` on separate
  integrability in s), `tI_one_pos`, `tI_const`, `hasLineDerivAt_coord`, `fq_ge_lin`,
  `exp_neg_sum_fq_le`.
* (R4) `sgdE_eq` (E = (c_i[1]_σ − [∂_iG]_σ) + Σ_k J_ik D_k(σ)) and
  **`strong_gaussian_domination`** (abstract BFS Theorem 5.1): K ≥ 0, b ≥ 0, (b > 0 ∨ a > 0),
  Adm Ψ integrable at τ = 0, row sums of K + Kᵀ ≤ r < c', f(t) ≥ c't − C₀; G ∈ Adm Ψ with
  ∂_jG = G' j ∈ Adm Ψ ∩ 𝒞:   [φ_iG]_0 ≤ Σ_j ([G' j]_0/[1]_0) [φ_iφ_j]_0.

NOT formalized.
* (R5). Needs (a) the decoupled weight in the form decWeight_B ∝ e^{Q_{K_B}} W_0 with
  K_B = Jnn on B×B ∪ Bᶜ×Bᶜ, 0 across ∂B (K_B ≥ 0; from `dirAction_split`), (b) `hint` for K_B with
  envelope Ψ = 1 + e^{bdryCoupling} (decWeight·e^{bdry} = qweight·const, so this is `integrable_tau`
  for the full weight plus a Gaussian bound for the decoupled one), (c) G = φ_y·e^{bdryCoupling},
  ∂_u G = δ_uy e^{bdry} + φ_y Σ_v J_uv φ_v e^{bdry} ∈ 𝒞 (`InCone` with Q = bdryCoupling restricted
  to its nonnegative-coefficient form), and the bookkeeping ⟨φ_xφ_u⟩_dec = regionTwoPt B x u
  (`decoupled_twoPt`), = 0 for u ∉ B (oddness), division by ⟨e^{bdry}⟩_dec, `twoPt_eq_decoupled`.
  The abstract `strong_gaussian_domination` is stated with the envelope Ψ for exactly this use.
* G of super-exponential-linear growth beyond an envelope; derivatives in τ (not needed).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2SGD

open PP2LocalTime PP2Griffiths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part 3: the local-time family [·]_τ for a general ferromagnetic pair interaction -/

/-- [F]_τ = ∫ F e^{Q_K} W_τ, W_τ = ∏_x e^{−f(φ_x²/2 + τ_x)}, f(u) = au + bu² (unnormalised).
For the quartic box, `tauInt n k m₀ λ = tI (Jnn n k) (alphaQ n m₀ λ) (betaQ n λ)` (rfl). -/
def tI (K : ι → ι → ℝ) (a b : ℝ) (τ : ι → ℝ) (F : (ι → ℝ) → ℝ) : ℝ :=
  ∫ φ, F φ * Real.exp (quadE K φ) * tw a b τ φ

/-- The single-site weight at local time τ_x. -/
def siteW (a b : ℝ) (τ : ι → ℝ) (x : ι) (y : ℝ) : ℝ := Real.exp (-fq a b (y ^ 2 / 2 + τ x))

theorem rhoQ_siteW (K : ι → ι → ℝ) (a b : ℝ) (τ φ : ι → ℝ) :
    Real.exp (quadE K φ) * tw a b τ φ = rhoQ (siteW a b τ) (quadE K) φ := by
  unfold rhoQ siteW tw
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Raising the local times from τ to τ': W_{τ'} = κ · e^{−Σ_x b(τ'_x − τ_x) φ_x²} · W_τ. -/
theorem tw_shift_mass (a b : ℝ) (τ τ' φ : ι → ℝ) :
    tw a b τ' φ = Real.exp (∑ x, fq a b (τ x) - ∑ x, fq a b (τ' x)) *
      (Real.exp (-massV (fun x => b * (τ' x - τ x)) φ) * tw a b τ φ) := by
  unfold tw massV
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by unfold fq; ring

/-- **R3 for the local-time family: [·]-expectations of cone elements decrease in τ.** For K ≥ 0,
b ≥ 0, τ ≤ τ' and H ∈ 𝒞 (with the four integrability conditions):
  [H]_{τ'} [1]_τ ≤ [H]_τ [1]_{τ'},   i.e. ⟨H⟩_{τ'} ≤ ⟨H⟩_τ. -/
theorem tI_mono {K : ι → ι → ℝ} (hK : ∀ x y, 0 ≤ K x y) {a b : ℝ} (hb : 0 ≤ b)
    {τ τ' : ι → ℝ} (hle : ∀ x, τ x ≤ τ' x) {H : (ι → ℝ) → ℝ} (hH : InCone H)
    (h1 : Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b τ φ)
    (h2 : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ)
    (h3 : Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b τ' φ)
    (h4 : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ' φ) :
    tI K a b τ' H * tI K a b τ (fun _ => 1) ≤ tI K a b τ H * tI K a b τ' (fun _ => 1) := by
  set w := siteW a b τ with hw
  set γ : ι → ℝ := fun x => b * (τ' x - τ x) with hγ
  set κ := Real.exp (∑ x, fq a b (τ x) - ∑ x, fq a b (τ' x)) with hκ
  have hκ0 : 0 < κ := Real.exp_pos _
  have hγ0 : ∀ x, 0 ≤ γ x := fun x => mul_nonneg hb (by linarith [hle x])
  have hwe : ∀ x y, w x (-y) = w x y := fun x y => by simp only [hw, siteW, neg_sq]
  have hwn : ∀ x y, 0 ≤ w x y := fun x y => (Real.exp_pos _).le
  have hQ : IsPosPoly (quadE K) := IsPosPoly.quadForm hK
  have e0 : ∀ (F : (ι → ℝ) → ℝ) φ, F φ * Real.exp (quadE K φ) * tw a b τ φ =
      F φ * rhoQ w (quadE K) φ := fun F φ => by rw [mul_assoc, rhoQ_siteW]
  have e1 : ∀ (F : (ι → ℝ) → ℝ) φ, F φ * Real.exp (quadE K φ) * tw a b τ' φ =
      κ * (F φ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ)) := fun F φ => by
    rw [tw_shift_mass a b τ τ' φ, ← rhoQ_siteW]; ring
  have i1 : Integrable fun φ => H φ * rhoQ w (quadE K) φ :=
    h1.congr (Filter.Eventually.of_forall fun φ => e0 H φ)
  have e0' : ∀ φ, (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ = rhoQ w (quadE K) φ :=
    fun φ => by rw [one_mul, rhoQ_siteW]
  have e1' : ∀ φ, (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ' φ =
      κ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ) := fun φ => by
    have := e1 (fun _ => 1) φ; simp only [one_mul] at this ⊢; exact this
  have i2 : Integrable (rhoQ w (quadE K)) :=
    h2.congr (Filter.Eventually.of_forall e0')
  have i3 : Integrable fun φ => H φ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ) :=
    (h3.const_mul κ⁻¹).congr (Filter.Eventually.of_forall fun φ => by
      simp only; rw [e1 H φ, ← mul_assoc, inv_mul_cancel₀ hκ0.ne', one_mul])
  have i4 : Integrable fun φ => Real.exp (-massV γ φ) * rhoQ w (quadE K) φ :=
    (h4.const_mul κ⁻¹).congr (Filter.Eventually.of_forall fun φ => by
      simp only; rw [e1' φ, ← mul_assoc, inv_mul_cancel₀ hκ0.ne', one_mul])
  have key := mass_mono_cone hwe hwn hH hQ hγ0 i1 i2 i3 i4
  have t1 : tI K a b τ' H = κ * ∫ φ, H φ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ) := by
    rw [tI, ← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall (e1 H))
  have t2 : tI K a b τ' (fun _ => 1) =
      κ * ∫ φ, Real.exp (-massV γ φ) * rhoQ w (quadE K) φ := by
    rw [tI, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall e1')
  have t3 : tI K a b τ H = ∫ φ, H φ * rhoQ w (quadE K) φ :=
    integral_congr_ae (Filter.Eventually.of_forall (e0 H))
  have t4 : tI K a b τ (fun _ => 1) = ∫ φ, rhoQ w (quadE K) φ :=
    integral_congr_ae (Filter.Eventually.of_forall e0')
  rw [t1, t2, t3, t4, mul_assoc, mul_left_comm (∫ φ, H φ * rhoQ w (quadE K) φ)]
  exact mul_le_mul_of_nonneg_left key hκ0.le

/-! ### The admissible class and integrability -/

/-- Admissible observables: continuous, |H| ≤ C e^{a' Σ|φ_x|} Ψ for an envelope Ψ ≥ 1 (Ψ = 1 for
polynomial observables; Ψ = 1 + e^{boundary coupling} for the decoupled measure of R5). -/
def Adm (Ψ : (ι → ℝ) → ℝ) (H : (ι → ℝ) → ℝ) : Prop :=
  Continuous H ∧ ∃ C a' : ℝ, ∀ φ, |H φ| ≤ C * Real.exp (a' * ∑ x, |φ x|) * Ψ φ

lemma Adm.congr {Ψ H H' : (ι → ℝ) → ℝ} (hH : Adm Ψ H) (h : ∀ φ, H φ = H' φ) : Adm Ψ H' := by
  have : H = H' := funext h
  rwa [← this]

lemma Adm.mul_coord {Ψ H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) (j : ι) :
    Adm Ψ (fun φ => φ j * H φ) := by
  obtain ⟨hc, C, a', hb⟩ := hH
  refine ⟨(continuous_apply j).mul hc, C, a' + 1, fun φ => ?_⟩
  have hC : 0 ≤ C * Real.exp (a' * ∑ x, |φ x|) * Ψ φ := (abs_nonneg _).trans (hb φ)
  rw [abs_mul]
  calc |φ j| * |H φ| ≤ Real.exp (∑ x, |φ x|) * (C * Real.exp (a' * ∑ x, |φ x|) * Ψ φ) :=
        mul_le_mul (abs_le_exp_sum φ j) (hb φ) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [add_mul, one_mul, Real.exp_add]; ring

lemma Adm.const {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ) (v : ℝ) : Adm Ψ (fun _ => v) :=
  ⟨continuous_const, |v|, 0, fun φ => by
    rw [zero_mul, Real.exp_zero, mul_one]; exact le_mul_of_one_le_right (abs_nonneg v) (hΨ φ)⟩

lemma Adm.coord {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ) (j : ι) : Adm Ψ (fun φ => φ j) :=
  ((Adm.const hΨ 1).mul_coord j).congr fun _ => mul_one _

/-- Integrability at τ ≥ 0 from integrability at τ = 0 (W_τ ≤ e^{−Σ f(τ_x)} W_0). -/
theorem integrable_adm {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) :
    Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b τ φ := by
  have hc := hH.1
  refine ((hint H hH).norm.const_mul (Real.exp (-∑ x, fq a b (τ x)))).mono'
    (by fun_prop : Continuous fun φ => H φ * Real.exp (quadE K φ) * tw a b τ φ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos a b τ φ), abs_of_pos (tw_pos a b 0 φ)]
  calc |H φ| * Real.exp (quadE K φ) * tw a b τ φ ≤
      |H φ| * Real.exp (quadE K φ) * (Real.exp (-∑ x, fq a b (τ x)) * tw a b 0 φ) :=
        mul_le_mul_of_nonneg_left (tw_le_tw_zero hb hτ φ) (by positivity)
    _ = _ := by ring

/-- |[H]_τ| ≤ e^{−Σ_x f(τ_x)} ∫ |H| e^{Q_K} W_0. -/
theorem abs_tI_le {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) :
    |tI K a b τ H| ≤ Real.exp (-∑ x, fq a b (τ x)) *
      ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b 0 φ‖ := by
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun φ => abs_nonneg _)
    ((hint H hH).norm.const_mul _) (Filter.Eventually.of_forall fun φ => ?_))
  simp only [Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos a b τ φ), abs_of_pos (tw_pos a b 0 φ)]
  calc |H φ| * Real.exp (quadE K φ) * tw a b τ φ ≤
      |H φ| * Real.exp (quadE K φ) * (Real.exp (-∑ x, fq a b (τ x)) * tw a b 0 φ) :=
        mul_le_mul_of_nonneg_left (tw_le_tw_zero hb hτ φ) (by positivity)
    _ = _ := by ring

/-- Integrability of the shifted family in the local time s (measurability by Fubini's
measurability lemma; decay from W_{τ+s e_i} ≤ W_τ C e^{−cs}). -/
theorem integrableOn_tI_shift {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a)
    {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) (i : ι) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) :
    IntegrableOn (fun s => tI K a b (τ + Pi.single i s) H) (Ioi 0) := by
  obtain ⟨c, hc, C, hC⟩ := exists_exp_bound hb hab
  have hHc := hH.1
  have hcont : Continuous fun z : ℝ × (ι → ℝ) =>
      H z.2 * Real.exp (quadE K z.2) * tw a b (τ + Pi.single i z.1) z.2 := by
    have e : (fun z : ℝ × (ι → ℝ) =>
        H z.2 * Real.exp (quadE K z.2) * tw a b (τ + Pi.single i z.1) z.2) =
        fun z => H z.2 * Real.exp (quadE K z.2) * (tw a b τ z.2 *
          Real.exp (fq a b (z.2 i ^ 2 / 2 + τ i) - fq a b (z.2 i ^ 2 / 2 + τ i + z.1))) := by
      funext z; rw [tw_shift]
    rw [e]; unfold fq; fun_prop
  have hsm0 : StronglyMeasurable fun s : ℝ => ∫ φ, (fun z : ℝ × (ι → ℝ) =>
      H z.2 * Real.exp (quadE K z.2) * tw a b (τ + Pi.single i z.1) z.2) (s, φ) :=
    StronglyMeasurable.integral_prod_right' (ν := (volume : Measure (ι → ℝ)))
      hcont.stronglyMeasurable
  have hsm : StronglyMeasurable fun s : ℝ => tI K a b (τ + Pi.single i s) H := hsm0
  obtain ⟨N, hN⟩ : ∃ N, N = ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ := ⟨_, rfl⟩
  have hI := integrable_adm hb hint hτ hH
  have hbd : ∀ s ∈ Ioi (0 : ℝ), ‖tI K a b (τ + Pi.single i s) H‖ ≤ N * C * Real.exp (-c * s) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hle : ∀ φ, ‖H φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ‖ ≤
        ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ * (C * Real.exp (-c * s)) := by
      intro φ
      have h1 := tw_shift_le hb hC (hτ i) φ hs0
      have h2 : 0 ≤ |H φ| * Real.exp (quadE K φ) := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos _ _ _ φ), abs_of_pos (tw_pos _ _ _ φ),
        mul_assoc _ (tw a b τ φ)]
      exact mul_le_mul_of_nonneg_left h1 h2
    have h3 : ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ‖ ≤
        ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ * (C * Real.exp (-c * s)) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun φ => norm_nonneg _)
        (hI.norm.mul_const _) (Filter.Eventually.of_forall hle)
    have h5 : ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ * (C * Real.exp (-c * s)) =
        N * (C * Real.exp (-c * s)) := by rw [integral_mul_const, hN]
    have h4 : ‖tI K a b (τ + Pi.single i s) H‖ ≤
        ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ‖ := by
      unfold tI; exact norm_integral_le_integral_norm _
    have h6 := h4.trans (h3.trans h5.le)
    rw [← mul_assoc] at h6
    exact h6
  exact ((exp_neg_integrableOn_Ioi 0 hc).const_mul (N * C)).mono' hsm.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi hbd)

/-! ### R2 for the general family, and auxiliary bounds -/

/-- **R2 (abstract):** the local-time integration by parts for [·]_τ with any pair matrix K and
the admissible class: [φ_i G]_τ = ∫_0^∞ ([∂_i G]_{τ+se_i} + Σ_j (K_ij + K_ji) [φ_j G]_{τ+se_i}) ds. -/
theorem tI_ibp {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a)
    {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) (i : ι) {G G' : (ι → ℝ) → ℝ} (hG : Adm Ψ G)
    (hG'a : Adm Ψ G') (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1)) :
    tI K a b τ (fun φ => φ i * G φ) =
      ∫ s in Ioi (0 : ℝ), (tI K a b (τ + Pi.single i s) G' +
        ∑ j, (K i j + K j i) * tI K a b (τ + Pi.single i s) (fun φ => φ j * G φ)) := by
  have hsplit : ∀ σ : ι → ℝ, (∀ x, 0 ≤ σ x) →
      (Integrable fun φ => (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) *
        Real.exp (quadE K φ) * tw a b σ φ) ∧
      ∫ φ, (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ) * tw a b σ φ =
      tI K a b σ G' + ∑ j, (K i j + K j i) * tI K a b σ (fun φ => φ j * G φ) := by
    intro σ hσ
    have I' := integrable_adm hb hint hσ hG'a
    have Ij : ∀ j, Integrable fun φ => φ j * G φ * Real.exp (quadE K φ) * tw a b σ φ :=
      fun j => integrable_adm hb hint hσ (hG.mul_coord j)
    have e : (fun φ => (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) *
        Real.exp (quadE K φ) * tw a b σ φ) =
        fun φ => G' φ * Real.exp (quadE K φ) * tw a b σ φ +
          ∑ j, (K i j + K j i) * (φ j * G φ * Real.exp (quadE K φ) * tw a b σ φ) := by
      funext φ
      rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hS : Integrable fun φ => ∑ j, (K i j + K j i) *
        (φ j * G φ * Real.exp (quadE K φ) * tw a b σ φ) :=
      integrable_finsetSum _ fun j _ => (Ij j).const_mul _
    refine ⟨e ▸ I'.add hS, ?_⟩
    rw [e, integral_add I' hS, integral_finsetSum _ fun j _ => (Ij j).const_mul _]
    unfold tI
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have h3G : Adm Ψ (fun φ => φ i ^ 3 * G φ) :=
    (((hG.mul_coord i).mul_coord i).mul_coord i).congr fun φ => by ring
  have main := local_time_ibp_bfs hb hab K τ i (hτ i) hG.1 hG'a.1 hG'
    (integrable_adm hb hint hτ hG) (integrable_adm hb hint hτ (hG.mul_coord i))
    (integrable_adm hb hint hτ h3G) (hsplit τ hτ).1
  have lhs : tI K a b τ (fun φ => φ i * G φ) =
      ∫ φ, φ i * G φ * Real.exp (quadE K φ) * tw a b τ φ := rfl
  rw [lhs, main]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    (hsplit _ (add_single_nonneg hτ i (le_of_lt hs))).2

lemma hasLineDerivAt_coord (i j : ι) (φ : ι → ℝ) :
    HasLineDerivAt ℝ (fun ψ : ι → ℝ => ψ j) ((Pi.single i (1 : ℝ) : ι → ℝ) j) φ
      (Pi.single i 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => (φ + t • (Pi.single i (1 : ℝ) : ι → ℝ)) j) =
      fun t => φ j + t * (Pi.single i (1 : ℝ) : ι → ℝ) j := by
    funext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const ((Pi.single i (1 : ℝ) : ι → ℝ) j)).const_add
    (φ j)

theorem tI_one_pos {K : ι → ι → ℝ} {a b : ℝ} {τ : ι → ℝ}
    (h : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ) :
    0 < tI K a b τ (fun _ => 1) := by
  unfold tI
  have hpos : ∀ φ, 0 < (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ := fun φ =>
    mul_pos (mul_pos one_pos (Real.exp_pos _)) (tw_pos a b τ φ)
  rw [integral_pos_iff_support_of_nonneg (fun φ => (hpos φ).le) h]
  have : Function.support (fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ) = Set.univ :=
    Set.eq_univ_of_forall fun φ => (hpos φ).ne'
  rw [this]
  exact isOpen_univ.measure_pos volume univ_nonempty

theorem tI_const (K : ι → ι → ℝ) (a b : ℝ) (τ : ι → ℝ) (v : ℝ) :
    tI K a b τ (fun _ => v) = v * tI K a b τ (fun _ => 1) := by
  unfold tI
  rw [← integral_const_mul]
  congr 1; funext φ; ring

/-- f(t) ≥ c' t − (c' − a)²/(4b) for b > 0 (any c'): the quartic term beats any linear weight. -/
lemma fq_ge_lin {a b : ℝ} (hb : 0 < b) (c' t : ℝ) :
    c' * t - (c' - a) ^ 2 / (4 * b) ≤ fq a b t := by
  unfold fq
  have h : 0 ≤ (2 * b * t + a - c') ^ 2 / (4 * b) := by positivity
  have e : (2 * b * t + a - c') ^ 2 / (4 * b) =
      a * t + b * t ^ 2 - (c' * t - (c' - a) ^ 2 / (4 * b)) := by
    field_simp; ring
  linarith

lemma exp_neg_sum_fq_le {a b c' C₀ : ℝ} (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq a b t)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) :
    Real.exp (-∑ x, fq a b (τ x)) ≤
      Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, τ x)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := Finset.sum_le_sum (s := Finset.univ) fun x _ => hf (τ x) (hτ x)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  linarith

/-! ## Part 4 (R4): strong Gaussian domination, BFS Theorem 5.1 -/

/-- D_i(τ) = Σ_j c_j [φ_i φ_j]_τ − [φ_i G]_τ. -/
def sgdD (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (cc : ι → ℝ) (i : ι) (τ : ι → ℝ) : ℝ :=
  ∑ j, cc j * tI K a b τ (fun φ => φ i * φ j) - tI K a b τ (fun φ => φ i * G φ)

/-- The local-time integrand of D_i(τ) given by R2 (σ = τ + s e_i). -/
def sgdE (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ) (cc : ι → ℝ)
    (i : ι) (τ : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j, cc j * (tI K a b (τ + Pi.single i s) (fun _ => (Pi.single i (1 : ℝ) : ι → ℝ) j) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * φ j)) -
    (tI K a b (τ + Pi.single i s) (G' i) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * G φ))

/-- The Volterra structure: E_i(τ, s) = (c_i [1]_σ − [∂_i G]_σ) + Σ_k J_ik D_k(σ). -/
theorem sgdE_eq (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ)
    (cc : ι → ℝ) (i : ι) (τ : ι → ℝ) (s : ℝ) :
    sgdE K a b G G' cc i τ s =
      (cc i * tI K a b (τ + Pi.single i s) (fun _ => 1) - tI K a b (τ + Pi.single i s) (G' i)) +
        ∑ k, (K i k + K k i) * sgdD K a b G cc k (τ + Pi.single i s) := by
  have h1 : ∑ j, cc j * (tI K a b (τ + Pi.single i s) (fun _ => (Pi.single i (1 : ℝ) : ι → ℝ) j) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * φ j)) =
      cc i * tI K a b (τ + Pi.single i s) (fun _ => 1) +
        ∑ k, (K i k + K k i) * ∑ j, cc j * tI K a b (τ + Pi.single i s) (fun φ => φ k * φ j) := by
    rw [Finset.sum_congr rfl fun j _ => mul_add (cc j) _ _, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [tI_const, Pi.single_eq_of_ne hj]; ring)
        (fun h => absurd (Finset.mem_univ i) h), tI_const, Pi.single_eq_same, one_mul]
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  unfold sgdE sgdD
  rw [h1]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end PP2SGD

end

import LongTable.Q_PP2SimonLieb3B

/-!
Part C of PP2SimonLieb3 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb3.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* (R3, local times) `tw_shift_mass`, `rhoQ_siteW`, **`tI_mono`** (K ≥ 0, b ≥ 0, τ ≤ τ', H ∈ 𝒞):
  [H]_{τ'}[1]_τ ≤ [H]_τ[1]_{τ'}; box form **`tauInt_mono`** (m₀ ≠ 0, λ ≥ 0, 0 ≤ τ ≤ τ',
  H ∈ 𝒞 ∩ Adm 1).
* (R4) `sgdE_eq` (E = (c_i[1]_σ − [∂_iG]_σ) + Σ_k J_ik D_k(σ)) and
  **`strong_gaussian_domination`** (abstract BFS Theorem 5.1): K ≥ 0, b ≥ 0, (b > 0 ∨ a > 0),
  Adm Ψ integrable at τ = 0, row sums of K + Kᵀ ≤ r < c', f(t) ≥ c't − C₀; G ∈ Adm Ψ with
  ∂_jG = G' j ∈ Adm Ψ ∩ 𝒞:   [φ_iG]_0 ≤ Σ_j ([G' j]_0/[1]_0) [φ_iφ_j]_0.
* (box) `hint_box`, `sgd_box_of`, `sum_ite_unique`, `Jsym_row_le` (Σ_y J_xy ≤ 4), and
  **`strong_gaussian_domination_box`** (m₀ ≠ 0, λ ≥ 0):
    ⟨φ_i G⟩ ≤ Σ_j ⟨∂_j G⟩ ⟨φ_iφ_j⟩ = Σ_j ⟨∂_j G⟩ · twoPt i j.

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

/-- **Strong Gaussian domination (BFS CMP 83, Theorem 5.1), abstract finite-dimensional form.**
Let K ≥ 0 (pair matrix, J = K + Kᵀ), f(u) = au + bu² with b ≥ 0 and (b > 0 or a > 0); let the
admissible class (envelope Ψ ≥ 1) be integrable against e^{Q_K} W_0; let J have row sums ≤ r < c'
with f(t) ≥ c't − C₀ on [0, ∞) (automatic for b > 0, `fq_ge_lin`). For G admissible with
admissible derivatives ∂_j G = G' j lying in the cone 𝒞:
  [φ_i G]_0 ≤ Σ_j (⟨∂_j G⟩_0) [φ_i φ_j]_0,    ⟨·⟩_0 = [·]_0 / [1]_0.
Proof: R2 gives D = (source) + K D for D_i(τ) = Σ_j c_j [φ_iφ_j]_τ − [φ_i G]_τ, the source
c_i[1]_σ − [∂_i G]_σ is ≥ 0 by R3 (`tI_mono`), |D(τ)| ≤ M e^{−Σ f(τ_x)} ≤ M' e^{−c'Στ}, and
`volterra_nonneg` gives D ≥ 0. -/
theorem strong_gaussian_domination {K : ι → ι → ℝ} (hK : ∀ x y, 0 ≤ K x y) {a b : ℝ}
    (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a) {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c') (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq a b t)
    {G : (ι → ℝ) → ℝ} {G' : ι → (ι → ℝ) → ℝ} (hG : Adm Ψ G) (hG'a : ∀ j, Adm Ψ (G' j))
    (hG' : ∀ j φ, HasLineDerivAt ℝ G (G' j φ) φ (Pi.single j 1)) (hcone : ∀ j, InCone (G' j))
    (i : ι) :
    tI K a b 0 (fun φ => φ i * G φ) ≤
      ∑ j, (tI K a b 0 (G' j) / tI K a b 0 (fun _ => 1)) * tI K a b 0 (fun φ => φ i * φ j) := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = tI K a b 0 (fun _ => 1) := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : ι → ℝ, cc = fun j => tI K a b 0 (G' j) / Z := ⟨_, rfl⟩
  have hc' : 0 < c' := lt_of_le_of_lt hr0 hrc
  have h0 : ∀ x, 0 ≤ (0 : ι → ℝ) x := fun x => le_refl 0
  have hZ0 : 0 < Z := hZ ▸ tI_one_pos (integrable_adm hb hint h0 (Adm.const hΨ 1))
  have hJ : ∀ i k, 0 ≤ K i k + K k i := fun i k => add_nonneg (hK i k) (hK k i)
  have hIs : ∀ τ : ι → ℝ, (∀ x, 0 ≤ τ x) → ∀ l H, Adm Ψ H →
      IntegrableOn (fun s => tI K a b (τ + Pi.single l s) H) (Ioi 0) :=
    fun τ hτ l H hH => integrableOn_tI_shift hb hab hint hτ l hH
  -- (hD) the R2 identities, combined
  have hD : ∀ l τ, (∀ x, 0 ≤ τ x) →
      sgdD K a b G cc l τ = ∫ s in Ioi (0 : ℝ), sgdE K a b G G' cc l τ s := by
    intro l τ hτ
    have hA : ∀ j, IntegrableOn (fun s =>
        tI K a b (τ + Pi.single l s) (fun _ => (Pi.single l (1 : ℝ) : ι → ℝ) j) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * φ j)) (Ioi 0) :=
      fun j => (hIs τ hτ l _ (Adm.const hΨ _)).add (integrable_finsetSum _ fun k _ =>
        (hIs τ hτ l _ ((Adm.coord hΨ j).mul_coord k)).const_mul _)
    have hB : IntegrableOn (fun s => tI K a b (τ + Pi.single l s) (G' l) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * G φ)) (Ioi 0) :=
      (hIs τ hτ l _ (hG'a l)).add (integrable_finsetSum _ fun k _ =>
        (hIs τ hτ l _ (hG.mul_coord k)).const_mul _)
    have R2j : ∀ j, tI K a b τ (fun φ => φ l * φ j) = ∫ s in Ioi (0 : ℝ),
        (tI K a b (τ + Pi.single l s) (fun _ => (Pi.single l (1 : ℝ) : ι → ℝ) j) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * φ j)) :=
      fun j => tI_ibp hb hab hint hτ l (Adm.coord hΨ j) (Adm.const hΨ _)
        (fun φ => hasLineDerivAt_coord l j φ)
    have R2G := tI_ibp (K := K) hb hab hint hτ l hG (hG'a l) (hG' l)
    have hsum : ∑ j, cc j * tI K a b τ (fun φ => φ l * φ j) = ∫ s in Ioi (0 : ℝ),
        ∑ j, cc j * (tI K a b (τ + Pi.single l s) (fun _ => (Pi.single l (1 : ℝ) : ι → ℝ) j) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * φ j)) := by
      rw [integral_finsetSum _ fun j _ => (hA j).const_mul (cc j)]
      exact Finset.sum_congr rfl fun j _ => by rw [R2j j, integral_const_mul]
    unfold sgdD
    rw [hsum, R2G, ← integral_sub (integrable_finsetSum _ fun j _ => (hA j).const_mul _) hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [sgdE]
  -- (hE) the source is nonnegative (R3)
  have hE : ∀ l τ s, (∀ x, 0 ≤ τ x) → 0 < s →
      ∑ k, (K l k + K k l) * sgdD K a b G cc k (τ + Pi.single l s) ≤
        sgdE K a b G G' cc l τ s := by
    intro l τ s hτ hs
    have hσ := add_single_nonneg hτ l (le_of_lt hs)
    have i1 : Integrable fun φ => G' l φ * Real.exp (quadE K φ) * tw a b 0 φ :=
      integrable_adm hb hint h0 (hG'a l)
    have i2 : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b 0 φ :=
      integrable_adm hb hint h0 (Adm.const hΨ 1)
    have i3 : Integrable fun φ => G' l φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single l s) φ :=
      integrable_adm hb hint hσ (hG'a l)
    have i4 : Integrable fun φ =>
        (1 : ℝ) * Real.exp (quadE K φ) * tw a b (τ + Pi.single l s) φ :=
      integrable_adm hb hint hσ (Adm.const hΨ 1)
    have hle : ∀ x, (0 : ι → ℝ) x ≤ (τ + Pi.single l s : ι → ℝ) x := hσ
    have key := tI_mono hK hb hle (hcone l) i1 i2 i3 i4
    rw [← hZ] at key
    have hsrc : tI K a b (τ + Pi.single l s) (G' l) ≤
        cc l * tI K a b (τ + Pi.single l s) (fun _ => 1) := by
      rw [hcc, div_mul_eq_mul_div, le_div_iff₀ hZ0]
      exact key
    rw [sgdE_eq]
    linarith
  -- (hM) the weighted a-priori bound
  have hM : ∃ M, ∀ l τ, (∀ x, 0 ≤ τ x) →
      -sgdD K a b G cc l τ ≤ M * Real.exp (-(c' * ∑ x, τ x)) := by
    set N1 : ι → ι → ℝ := fun l j =>
      ∫ φ, ‖φ l * φ j * Real.exp (quadE K φ) * tw a b 0 φ‖ with hN1
    set N2 : ι → ℝ := fun l => ∫ φ, ‖φ l * G φ * Real.exp (quadE K φ) * tw a b 0 φ‖ with hN2
    set Ml : ι → ℝ := fun l => ∑ j, |cc j| * N1 l j + N2 l with hMl
    have hMl0 : ∀ l, 0 ≤ Ml l := fun l =>
      add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _)) (integral_nonneg fun _ => norm_nonneg _)
    refine ⟨Real.exp (Fintype.card ι * C₀) * ∑ l, Ml l, fun l τ hτ => ?_⟩
    set ef := Real.exp (-∑ x, fq a b (τ x)) with hef
    have hab1 : ∀ F, Adm Ψ F → |tI K a b τ F| ≤
        ef * ∫ φ, ‖F φ * Real.exp (quadE K φ) * tw a b 0 φ‖ :=
      fun F hF => abs_tI_le hb hint hτ hF
    have s1 : -(∑ j, cc j * tI K a b τ (fun φ => φ l * φ j)) ≤ ∑ j, |cc j| * (ef * N1 l j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      calc -(cc j * tI K a b τ (fun φ => φ l * φ j))
          ≤ |cc j * tI K a b τ (fun φ => φ l * φ j)| := neg_le_abs _
        _ = |cc j| * |tI K a b τ (fun φ => φ l * φ j)| := abs_mul _ _
        _ ≤ |cc j| * (ef * N1 l j) :=
          mul_le_mul_of_nonneg_left (hab1 _ ((Adm.coord hΨ j).mul_coord l)) (abs_nonneg _)
    have s2 : tI K a b τ (fun φ => φ l * G φ) ≤ ef * N2 l :=
      (le_abs_self _).trans (hab1 _ (hG.mul_coord l))
    have e : ef * Ml l = ∑ j, |cc j| * (ef * N1 l j) + ef * N2 l := by
      simp only [hMl]
      rw [mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have s3 : -sgdD K a b G cc l τ ≤ ef * Ml l := by
      unfold sgdD; rw [e]; linarith
    have hef1 : ef ≤ Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, τ x)) :=
      exp_neg_sum_fq_le hf hτ
    have hMs : Ml l ≤ ∑ l, Ml l :=
      Finset.single_le_sum (f := Ml) (fun l _ => hMl0 l) (Finset.mem_univ l)
    calc -sgdD K a b G cc l τ ≤ ef * Ml l := s3
      _ ≤ (Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, τ x))) * ∑ l, Ml l :=
        mul_le_mul hef1 hMs (hMl0 l) (by positivity)
      _ = _ := by ring
  have hfin := volterra_nonneg (J := fun i k => K i k + K k i) hJ hc' hr0 hrc hrow hD hE hM
    i 0 h0
  unfold sgdD at hfin
  rw [← hZ]
  simp only [hcc] at hfin
  linarith

end PP2SGD

/-! ## Part 5: the quartic Dirichlet-box model -/

namespace PP2Target

open PP2LocalTime PP2Griffiths PP2SGD

variable {n k : ℕ}

theorem tauInt_eq_tI (m₀ lam : ℝ) (τ : DField n k) (F : DField n k → ℝ) :
    tauInt n k m₀ lam τ F = tI (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) τ F := rfl

/-- The admissible class with envelope 1 (all observables of exponential-linear growth, e.g. all
polynomials) is integrable against the quartic box weight (m₀ ≠ 0, λ ≥ 0). -/
theorem hint_box {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) :
    ∀ H, Adm (fun _ : DField n k => (1 : ℝ)) H → Integrable fun φ => H φ *
      Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ := by
  rintro H ⟨hc, C, a', hb⟩
  exact integrable_tau hm hlam (fun x => le_refl _) hc C a' (fun φ => by simpa using hb φ)

/-- **R3 for the quartic box model.** For m₀ ≠ 0, λ ≥ 0, 0 ≤ τ ≤ τ' and H in the cone 𝒞 of
exponential-linear growth: [H]_{τ'} [1]_τ ≤ [H]_τ [1]_{τ'} (⟨H⟩_τ is decreasing in each τ_x). -/
theorem tauInt_mono {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) {τ τ' : DField n k}
    (hτ : ∀ x, 0 ≤ τ x) (hle : ∀ x, τ x ≤ τ' x) {H : DField n k → ℝ} (hH : InCone H)
    (hHa : Adm (fun _ => 1) H) :
    tauInt n k m₀ lam τ' H * tauInt n k m₀ lam τ (fun _ => 1) ≤
      tauInt n k m₀ lam τ H * tauInt n k m₀ lam τ' (fun _ => 1) := by
  have hb := betaQ_nonneg (n := n) hlam
  have hτ' : ∀ x, 0 ≤ τ' x := fun x => (hτ x).trans (hle x)
  have h1 := Adm.const (Ψ := fun _ : DField n k => (1 : ℝ)) (fun _ => le_refl 1) 1
  exact tI_mono Jnn_nonneg hb hle hH (integrable_adm hb (hint_box hm hlam) hτ hHa)
    (integrable_adm hb (hint_box hm hlam) hτ h1) (integrable_adm hb (hint_box hm hlam) hτ' hHa)
    (integrable_adm hb (hint_box hm hlam) hτ' h1)

/-- The quartic-box strong Gaussian domination from the abstract one, given the contraction data
(row bound r < c' and f(t) ≥ c't − C₀). -/
theorem sgd_box_of {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hab : 0 < betaQ n lam ∨ 0 < alphaQ n m₀ lam) {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c')
    (hrow : ∀ x : DSite n k, ∑ y, (Jnn n k x y + Jnn n k y x) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq (alphaQ n m₀ lam) (betaQ n lam) t)
    {G : DField n k → ℝ} {G' : DSite n k → DField n k → ℝ} (hG : Adm (fun _ => 1) G)
    (hG'a : ∀ j, Adm (fun _ => 1) (G' j))
    (hG' : ∀ j φ, HasLineDerivAt ℝ G (G' j φ) φ (Pi.single j 1))
    (hcone : ∀ j, InCone (G' j)) (i : DSite n k) :
    (∫ φ, φ i * G φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) ≤
      ∑ j, ((∫ φ, G' j φ * qweight n k m₀ lam φ) / ∫ φ, qweight n k m₀ lam φ) *
        twoPt n k m₀ lam i j := by
  have hb := betaQ_nonneg (n := n) hlam
  have h := strong_gaussian_domination (K := Jnn n k) Jnn_nonneg hb hab
    (Ψ := fun _ => 1) (fun _ => le_refl 1) (hint_box hm hlam) hr0 hrc hrow hf hG hG'a hG' hcone i
  set κ := Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2))
    with hκ
  have hκ0 : 0 < κ := Real.exp_pos _
  have hz : ∀ F : DField n k → ℝ, tI (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 F =
      κ * ∫ φ, F φ * qweight n k m₀ lam φ := fun F => tauInt_zero m₀ lam F
  simp only [hz, one_mul] at h
  have hZ : 0 < ∫ φ, qweight n k m₀ lam φ := integral_dweight_pos hm hlam
  have e1 : ∀ j, κ * (∫ φ, G' j φ * qweight n k m₀ lam φ) / (κ * ∫ φ, qweight n k m₀ lam φ) *
      (κ * ∫ φ, φ i * φ j * qweight n k m₀ lam φ) =
      κ * ((∫ φ, G' j φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) *
        ∫ φ, φ i * φ j * qweight n k m₀ lam φ) := fun j => by
    rw [mul_div_mul_left _ _ hκ0.ne']; ring
  simp only [e1, ← Finset.mul_sum] at h
  have h2 := le_of_mul_le_mul_left h hκ0
  unfold twoPt
  calc (∫ φ, φ i * G φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ)
      ≤ (∑ j, (∫ φ, G' j φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) *
          ∫ φ, φ i * φ j * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) :=
        div_le_div_of_nonneg_right h2 hZ.le
    _ = _ := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring

lemma sum_ite_unique {P : DSite n k → Prop} [DecidablePred P]
    (h : ∀ y y', P y → P y' → y = y') : ∑ y, (if P y then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter P).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
    h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast this

/-- **Row sums of the BFS coupling:** Σ_y J_xy ≤ 4 (each box site has at most four nearest
neighbours in the box). -/
theorem Jsym_row_le (x : DSite n k) : ∑ y, Jsym n k x y ≤ 4 := by
  have hJ : ∀ y, Jsym n k x y ≤
      (if (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) +
      (if (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) := by
    intro y
    by_cases hxy : x = y
    · subst hxy; rw [Jsym_diag]; split_ifs <;> norm_num
    · rw [Jsym_eq_bondJ hxy]
      by_cases h : nn x y
      · have hb1 : bondJ n k x y = 1 := by
          have := (spacing_pos n).ne'
          rw [bondJ, dirOp_nn 0 h]; field_simp
        rw [hb1]
        unfold nn at h
        rcases h with ⟨h2, h1 | h1⟩ | ⟨h1, h2 | h2⟩
        · have hc : (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 := ⟨h1.symm, h2.symm⟩
          split_ifs <;> norm_num
        · have hc : (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 := ⟨h1.symm, h2.symm⟩
          split_ifs <;> norm_num
        · have hc : (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 := ⟨h2.symm, h1.symm⟩
          split_ifs <;> norm_num
        · have hc : (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 := ⟨h2.symm, h1.symm⟩
          split_ifs <;> norm_num
      · rw [bondJ, dirOp_far 0 hxy h, mul_zero, neg_zero]
        split_ifs <;> norm_num
  have hu : ∀ (f : DSite n k → ℕ) (g : DSite n k → ℕ) (u v : ℕ),
      (∀ y y' : DSite n k, f y = u → g y = v → f y' = u → g y' = v → y = y') →
      ∑ y : DSite n k, (if f y = u ∧ g y = v then (1 : ℝ) else 0) ≤ 1 := by
    intro f g u v hfg
    exact sum_ite_unique fun y y' hy hy' => hfg y y' hy.1 hy.2 hy'.1 hy'.2
  have ext' : ∀ y y' : DSite n k, (y.1 : ℕ) = y'.1 → (y.2 : ℕ) = y'.2 → y = y' :=
    fun y y' h1 h2 => Prod.ext (Fin.ext h1) (Fin.ext h2)
  have s1 : ∑ y : DSite n k, (if (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  have s2 : ∑ y : DSite n k, (if (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  have s3 : ∑ y : DSite n k, (if (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  have s4 : ∑ y : DSite n k, (if (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  calc ∑ y, Jsym n k x y ≤ ∑ y : DSite n k,
      ((if (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) +
      (if (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun y _ => hJ y
    _ ≤ 4 := by
        simp only [Finset.sum_add_distrib]
        linarith

/-- **Strong Gaussian domination for the quartic Dirichlet box (BFS Theorem 5.1), λ ≥ 0.**
For m₀ ≠ 0, λ ≥ 0, G of exponential-linear growth whose derivatives ∂_j G = G' j are of
exponential-linear growth and lie in the cone 𝒞 (e.g. G any polynomial with nonnegative
coefficients):
  ⟨φ_i G⟩ ≤ Σ_j ⟨∂_j G⟩ ⟨φ_i φ_j⟩,
⟨·⟩ the normalised quartic box measure (`twoPt` = ⟨φ_i φ_j⟩). For λ > 0 the contraction uses
the quartic term (any c'); for λ = 0 it uses α = 4 + ε²m₀² > 4 ≥ Σ_y J_xy (`Jsym_row_le`). -/
theorem strong_gaussian_domination_box {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    {G : DField n k → ℝ} {G' : DSite n k → DField n k → ℝ} (hG : Adm (fun _ => 1) G)
    (hG'a : ∀ j, Adm (fun _ => 1) (G' j))
    (hG' : ∀ j φ, HasLineDerivAt ℝ G (G' j φ) φ (Pi.single j 1))
    (hcone : ∀ j, InCone (G' j)) (i : DSite n k) :
    (∫ φ, φ i * G φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) ≤
      ∑ j, ((∫ φ, G' j φ * qweight n k m₀ lam φ) / ∫ φ, qweight n k m₀ lam φ) *
        twoPt n k m₀ lam i j := by
  have hrow4 : ∀ x : DSite n k, ∑ y, (Jnn n k x y + Jnn n k y x) ≤ 4 := Jsym_row_le
  rcases hlam.lt_or_eq with hpos | h0
  · have hbpos : 0 < betaQ n lam := by unfold betaQ; have := spacing_pos n; positivity
    exact sgd_box_of hm hlam (Or.inl hbpos) (c' := 5)
      (C₀ := (5 - alphaQ n m₀ lam) ^ 2 / (4 * betaQ n lam)) (by norm_num) (by norm_num) hrow4
      (fun t _ => fq_ge_lin hbpos 5 t) hG hG'a hG' hcone i
  · subst h0
    have hε := spacing_pos n
    have hα : alphaQ n m₀ 0 = 4 + spacing n ^ 2 * m₀ ^ 2 := by unfold alphaQ; ring
    have hα4 : 4 < alphaQ n m₀ 0 := by
      rw [hα]; have : 0 < spacing n ^ 2 * m₀ ^ 2 := by positivity
      linarith
    exact sgd_box_of hm le_rfl (Or.inr (by linarith)) (C₀ := 0) (by norm_num) hα4 hrow4
      (fun t _ => by unfold fq betaQ; simp) hG hG'a hG' hcone i

end PP2Target

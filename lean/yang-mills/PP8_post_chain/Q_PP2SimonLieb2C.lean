import LongTable.Q_PP2SimonLieb2B

/-!
Part C of PP2SimonLieb2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb2.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* `quad_Jnn_bondJ`, `bondJ_diag` (= −4), `Jnn_diag` (= 0), `Jsym_eq_bondJ` (x ≠ y), `sum_Jsym_eq`.
* `qweight_le_gauss`, `tauWeight_le`, `integrable_tau`: for m₀ ≠ 0, λ ≥ 0, τ ≥ 0, every H with
  |H| ≤ C e^{a Σ|φ|} (all polynomials) is integrable against e^{quadE Jnn} W_τ.
* **`tau_ibp_quartic`** (R2 for the quartic box model; m₀ ≠ 0, λ ≥ 0, τ ≥ 0, G, G' = ∂_i G
  continuous and both ≤ C e^{a Σ|φ|}; no further hypotheses):
    [φ_i G]_τ = ∫_{s>0} ( [∂_i G]_{τ+s e_i} + Σ_j J_ij [φ_j G]_{τ+s e_i} ),
  and `tau_ibp_quartic_bondJ`, the same with Σ_{j ≠ i} bondJ_ij.

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

namespace PP2Target

open PP2LocalTime PP2Griffiths

variable {n k : ℕ}

/-- The pair exponent in two forms: Σ Jnn φφ − 2 Σ φ² = ½ Σ_{x,y} bondJ_xy φ_x φ_y
(both are −½ dirAction at m₀ = 0). -/
theorem quad_Jnn_bondJ (φ : DField n k) :
    quadE (Jnn n k) φ - 2 * ∑ x, φ x ^ 2 = (1 / 2) * ∑ x, ∑ y, bondJ n k x y * φ x * φ y := by
  have h1 := neg_half_dirAction (n := n) (k := k) 0 φ
  rw [coupling_eq, diagPart_eq] at h1
  simp only [cdiag_eq_four, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    Finset.sum_const_zero, mul_zero, zero_div, sub_zero, ← Finset.mul_sum] at h1
  have e : ∑ x, ∑ y, bondJ n k x y * φ x * φ y = -(dirAction n k 0 φ) := by
    rw [dirAction_eq_quad]
    simp only [dotProduct, Matrix.mulVec]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold bondJ; ring
  rw [e]
  unfold quadE
  linarith

theorem bondJ_diag (x : DSite n k) : bondJ n k x x = -4 := by
  have hε := (spacing_pos n).ne'
  rw [bondJ, dirOp_diag]
  field_simp
  ring

/-- The nearest-neighbour matrix of `dweight_eq_ferro` has zero diagonal. -/
theorem Jnn_diag (x : DSite n k) : Jnn n k x x = 0 := by
  have h := quad_Jnn_bondJ (n := n) (k := k) (Pi.single x 1)
  unfold quadE at h
  rw [quad_single, quad_single, sq_single, bondJ_diag] at h
  linarith

theorem Jsym_diag (x : DSite n k) : Jsym n k x x = 0 := by
  rw [Jsym, Jnn_diag, add_zero]

/-- **The BFS coupling is the Simon–Lieb coupling:** J_xy = Jnn_xy + Jnn_yx = bondJ_xy for x ≠ y
(so it is 1 for nearest neighbours and 0 otherwise, `dirOp_nn`/`dirOp_far`). -/
theorem Jsym_eq_bondJ {x y : DSite n k} (hxy : x ≠ y) : Jsym n k x y = bondJ n k x y := by
  have h := quad_Jnn_bondJ (n := n) (k := k) (Pi.single x 1 + Pi.single y 1)
  unfold quadE at h
  rw [quad_pair, quad_pair, sq_pair hxy, bondJ_diag, bondJ_diag, Jnn_diag, Jnn_diag,
    bondJ_symm y x] at h
  unfold Jsym
  linarith

/-- The unnormalised τ-shifted expectation [G]_τ = ∫ G · e^{Σ Jnn φφ} · ∏_x e^{−f(φ_x²/2+τ_x)}
(BFS's [·]_t, with g(S²) = e^{−f(S²/2)} and their g(S² + 2t) = e^{−f(S²/2 + t)}). -/
def tauInt (n k : ℕ) (m₀ lam : ℝ) (τ : DField n k) (G : DField n k → ℝ) : ℝ :=
  ∫ φ, G φ * Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ

/-- **The site exponent of the quartic weight.** qweight = e^{−|Λ|·3λε²c²} · e^{Σ Jnn φφ} · W_0,
with f(s) = αs + βs²: the Wick constant 3λε²c² per site factors out. -/
theorem qweight_eq_tw (m₀ lam : ℝ) (φ : DField n k) :
    qweight n k m₀ lam φ =
      Real.exp (-(Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2))) *
        (Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) := by
  rw [qweight, dweight_eq_ferro]
  simp only [siteWeight_eq, wickPoly_X4]
  rw [← Real.exp_sum]
  unfold tw quadE
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have h : ∀ x : DSite n k, -((4 + spacing n ^ 2 * m₀ ^ 2) * φ x ^ 2) / 2
      - lam * spacing n ^ 2 * (φ x ^ 4 - 6 * freeVar n m₀ * φ x ^ 2 + 3 * freeVar n m₀ ^ 2) =
      -(3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)
        - fq (alphaQ n m₀ lam) (betaQ n lam) (φ x ^ 2 / 2 + (0 : DField n k) x) := by
    intro x; simp only [Pi.zero_apply, add_zero]; unfold fq alphaQ betaQ; ring
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- At τ = 0 the family is the quartic measure: [G]_0 = e^{|Λ|·3λε²c²} ∫ G · qweight. -/
theorem tauInt_zero (m₀ lam : ℝ) (G : DField n k → ℝ) :
    tauInt n k m₀ lam 0 G =
      Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
        ∫ φ, G φ * qweight n k m₀ lam φ := by
  rw [tauInt, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [qweight_eq_tw, Real.exp_neg]
  field_simp

theorem eTw_zero (m₀ lam : ℝ) (φ : DField n k) :
    Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ =
      Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
        qweight n k m₀ lam φ := by
  rw [qweight_eq_tw, Real.exp_neg]
  field_simp

theorem qweight_le_gauss {m₀ lam : ℝ} (hlam : 0 ≤ lam) (φ : DField n k) :
    qweight n k m₀ lam φ ≤
      Real.exp (lam * spacing n ^ 2 * (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2))) *
        PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ := by
  rw [gaussWeight_dirAction, qweight, dweight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsum : -(Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)) ≤
      ∑ x : DSite n k, wickPoly (Polynomial.X ^ 4) (freeVar n m₀) (φ x) := by
    have := Finset.sum_le_sum (s := Finset.univ)
      (fun x (_ : x ∈ Finset.univ) => wickPoly_X4_ge (freeVar n m₀) (φ x))
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hc : 0 ≤ lam * spacing n ^ 2 := by have := spacing_pos n; positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hc]

theorem betaQ_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : 0 ≤ betaQ n lam := by
  unfold betaQ; have := spacing_pos n; positivity

/-- Gaussian domination of the τ-shifted weight (τ ≥ 0, λ ≥ 0). -/
theorem tauWeight_le {m₀ lam : ℝ} (hlam : 0 ≤ lam) {τ : DField n k} (hτ : ∀ x, 0 ≤ τ x)
    (φ : DField n k) :
    Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ ≤
      (Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x)) *
        Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
        Real.exp (lam * spacing n ^ 2 * (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)))) *
        PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ := by
  have h1 := tw_le_tw_zero (a := alphaQ n m₀ lam) (betaQ_nonneg (n := n) hlam) hτ φ
  have hE := (Real.exp_pos (quadE (Jnn n k) φ)).le
  have h2 := qweight_le_gauss (m₀ := m₀) hlam φ
  calc Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ
      ≤ Real.exp (quadE (Jnn n k) φ) * (Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x))
          * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) := mul_le_mul_of_nonneg_left h1 hE
    _ = Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x)) *
          Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
          qweight n k m₀ lam φ := by
        rw [mul_assoc (Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x))), ← eTw_zero]
        ring
    _ ≤ _ := by
        rw [mul_assoc _ (Real.exp (lam * spacing n ^ 2 * _))]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Integrability in the τ-family** for exponentially bounded observables (m₀ ≠ 0, λ ≥ 0, τ ≥ 0):
this covers all polynomials. -/
theorem integrable_tau {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) {τ : DField n k}
    (hτ : ∀ x, 0 ≤ τ x) {H : DField n k → ℝ} (hH : Continuous H) (C a : ℝ)
    (hHb : ∀ φ, |H φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) :
    Integrable fun φ => H φ * Real.exp (quadE (Jnn n k) φ) *
      tw (alphaQ n m₀ lam) (betaQ n lam) τ φ := by
  obtain ⟨K, hK0, hKb⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : DField n k,
      Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ ≤
        K * PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ :=
    ⟨_, by positivity, tauWeight_le hlam hτ⟩
  refine PP2GaussIBP.integrable_of_le_expAbs (scaledOp_posDef hm)
    ((by fun_prop : Continuous fun φ => H φ * Real.exp (quadE (Jnn n k) φ) *
      tw (alphaQ n m₀ lam) (betaQ n lam) τ φ).aestronglyMeasurable) (C * K) a fun φ => ?_
  have hC : 0 ≤ C * Real.exp (a * ∑ x, |φ x|) := (abs_nonneg _).trans (hHb φ)
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos _ _ _ _), mul_assoc]
  calc |H φ| * (Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ)
      ≤ (C * Real.exp (a * ∑ x, |φ x|)) * (K * PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ) :=
        mul_le_mul (hHb φ) (hKb φ) (mul_pos (Real.exp_pos _) (tw_pos _ _ _ _)).le hC
    _ = _ := by ring

theorem shift_nonneg {τ : DField n k} (hτ : ∀ x, 0 ≤ τ x) (i : DSite n k) {s : ℝ} (hs : 0 ≤ s) :
    ∀ x, 0 ≤ (τ + Pi.single i s : DField n k) x := by
  intro x
  by_cases hx : x = i
  · subst hx; simp only [Pi.add_apply, Pi.single_eq_same]; linarith [hτ x]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hx, add_zero]; exact hτ x

/-- **R2: the one-site local-time integration by parts for the quartic Dirichlet-box model**
(BFS CMP 83, the generator of Theorem 2.2 / (5.5)). For m₀ ≠ 0, λ ≥ 0, τ ≥ 0, any site i, and G
continuous with continuous e_i-derivative G', both bounded by C e^{a Σ|φ|}:
  [φ_i G]_τ = ∫_0^∞ ds ( [∂_i G]_{τ+s e_i} + Σ_j J_ij [φ_j G]_{τ+s e_i} ). -/
theorem tau_ibp_quartic {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (τ : DField n k)
    (hτ : ∀ x, 0 ≤ τ x) (i : DSite n k) {G G' : DField n k → ℝ} (hGc : Continuous G)
    (hG'c : Continuous G') (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1)) (C a : ℝ)
    (hGb : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|))
    (hG'b : ∀ φ, |G' φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) :
    tauInt n k m₀ lam τ (fun φ => φ i * G φ) =
      ∫ s in Ioi (0 : ℝ), (tauInt n k m₀ lam (τ + Pi.single i s) G' +
        ∑ j, Jsym n k i j * tauInt n k m₀ lam (τ + Pi.single i s) (fun φ => φ j * G φ)) := by
  have hb := betaQ_nonneg (n := n) hlam
  have hab : 0 < betaQ n lam ∨ 0 < alphaQ n m₀ lam := by
    rcases hlam.lt_or_eq with h | h
    · left; unfold betaQ; have := spacing_pos n; positivity
    · right; subst h; unfold alphaQ; have := spacing_pos n
      simp only [zero_mul, mul_zero, sub_zero]; positivity
  have hcoord : ∀ j, Continuous fun φ : DField n k => φ j * G φ :=
    fun j => (continuous_apply j).mul hGc
  have hpieces : ∀ σ : DField n k, (∀ x, 0 ≤ σ x) →
      (Integrable fun φ => G' φ * Real.exp (quadE (Jnn n k) φ) *
        tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) ∧
      ∀ j, Integrable fun φ => φ j * G φ * Real.exp (quadE (Jnn n k) φ) *
        tw (alphaQ n m₀ lam) (betaQ n lam) σ φ :=
    fun σ hσ => ⟨integrable_tau hm hlam hσ hG'c C a hG'b,
      fun j => integrable_tau hm hlam hσ (hcoord j) C (a + 1) (growth_mul_coord hGb j)⟩
  have hsplit : ∀ σ : DField n k, (∀ x, 0 ≤ σ x) →
      (Integrable fun φ => (G' φ + ∑ j, (Jnn n k i j + Jnn n k j i) * (φ j * G φ)) *
        Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) ∧
      ∫ φ, (G' φ + ∑ j, (Jnn n k i j + Jnn n k j i) * (φ j * G φ)) *
        Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ =
      tauInt n k m₀ lam σ G' + ∑ j, Jsym n k i j * tauInt n k m₀ lam σ (fun φ => φ j * G φ) := by
    intro σ hσ
    obtain ⟨I', Ij⟩ := hpieces σ hσ
    have e : (fun φ => (G' φ + ∑ j, (Jnn n k i j + Jnn n k j i) * (φ j * G φ)) *
        Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) =
        fun φ => G' φ * Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ +
          ∑ j, Jsym n k i j * (φ j * G φ * Real.exp (quadE (Jnn n k) φ) *
            tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) := by
      funext φ
      rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by unfold Jsym; ring
    have hS : Integrable fun φ => ∑ j, Jsym n k i j * (φ j * G φ * Real.exp (quadE (Jnn n k) φ) *
        tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) :=
      integrable_finsetSum _ fun j _ => (Ij j).const_mul _
    refine ⟨e ▸ I'.add hS, ?_⟩
    rw [e, integral_add I' hS, integral_finsetSum _ fun j _ => (Ij j).const_mul _]
    unfold tauInt
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have main := local_time_ibp_bfs hb hab (Jnn n k) τ i (hτ i) hGc hG'c hG'
    (integrable_tau hm hlam hτ hGc C a hGb)
    (integrable_tau hm hlam hτ (hcoord i) C (a + 1) (growth_mul_coord hGb i))
    (integrable_tau hm hlam hτ (((continuous_apply i).pow 3).mul hGc) C (a + 3)
      (growth_mul_cube hGb i))
    (hsplit τ hτ).1
  have lhs : tauInt n k m₀ lam τ (fun φ => φ i * G φ) = ∫ φ, φ i * G φ *
      Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ := rfl
  rw [lhs, main]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    (hsplit _ (shift_nonneg hτ i (le_of_lt hs))).2

theorem sum_Jsym_eq (i : DSite n k) (c : DSite n k → ℝ) :
    ∑ j, Jsym n k i j * c j = ∑ j ∈ Finset.univ.erase i, bondJ n k i j * c j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Jsym_diag, zero_mul, zero_add]
  exact Finset.sum_congr rfl fun j hj =>
    by rw [Jsym_eq_bondJ (Finset.ne_of_mem_erase hj).symm]

/-- **R2 with the Simon–Lieb coupling:** the same identity with Σ_{j ≠ i} bondJ_ij. -/
theorem tau_ibp_quartic_bondJ {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (τ : DField n k)
    (hτ : ∀ x, 0 ≤ τ x) (i : DSite n k) {G G' : DField n k → ℝ} (hGc : Continuous G)
    (hG'c : Continuous G') (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1)) (C a : ℝ)
    (hGb : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|))
    (hG'b : ∀ φ, |G' φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) :
    tauInt n k m₀ lam τ (fun φ => φ i * G φ) =
      ∫ s in Ioi (0 : ℝ), (tauInt n k m₀ lam (τ + Pi.single i s) G' +
        ∑ j ∈ Finset.univ.erase i,
          bondJ n k i j * tauInt n k m₀ lam (τ + Pi.single i s) (fun φ => φ j * G φ)) := by
  rw [tau_ibp_quartic hm hlam τ hτ i hGc hG'c hG' C a hGb hG'b]
  simp_rw [sum_Jsym_eq]

end PP2Target

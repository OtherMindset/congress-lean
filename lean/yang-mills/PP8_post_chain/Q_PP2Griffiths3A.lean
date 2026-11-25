import LongTable.Q_PP2Griffiths2B

/-!
Part A of PP2Griffiths3 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Griffiths3.lean)
Long Table, P(φ)₂ direction, node M2 (session 3): integrability of the moments of the quartic
Dirichlet-box measure, and Griffiths' second inequality (duplicate variables, in the cone
𝒞 = {g · exp Q : g, Q polynomials with nonnegative coefficients}, site-dependent even weights).

FORMALIZED.
* `integrable_mono_dweight` (λ ≥ 0, m₀ ≠ 0): φ ↦ (∏_x φ x ^ a x) · dweight n k m₀ λ X⁴ φ is
  integrable, for every a (bound dweight ≤ C · ∏ exp(−m₀²ε²φ²/2) of session 2, and
  `integrable_rpow_mul_exp_neg_mul_sq` site by site).
* `gibbs n k m₀ λ`: the measure with density dweight / Z; `integral_gibbs`: ∫ F d(gibbs) =
  `dexpect` F for every F; `isProbabilityMeasure_gibbs` (λ ≥ 0, m₀ ≠ 0);
  `griffiths_first_gibbs`: Griffiths I is the genuine statement (integrable moment, probability
  measure, ∫ φ^a d(gibbs) = ⟨φ^a⟩ ≥ 0).
* Doubled system on ι → ℝ × ℝ: per-site involutions `act` ((t,s) ↦ (s,t), (−s,−t), (−t,−s)),
  all Lebesgue-preserving; `uv_actPi`: in (u, v) = (t + s, t − s) they are exactly the sign flips
  `flipSigns`; `integral_nonneg_of_actSum_nonneg` (sign averaging on the doubled space, no change
  of variables); `integral_uv_nonneg`: ∫ G(u, v) ∏ w_x(t_x) w_x(s_x) ≥ 0 for G with nonnegative
  coefficients.
* `PairPos f` (f(t) ± f(s) have nonnegative coefficients in (u, v)); closed under +, ·, powers,
  finite sums/products; `PairPos.of_isPosPoly`: every polynomial with nonnegative coefficients
  is pair-positive.
* `InCone A` (A = g · e^Q, g, Q ∈ IsPosPoly). `signSum_dupG_nonneg` (pointwise, via the exponential
  series, no convergence theorem needed) and
  **`griffiths_second_dup`**: for w_x even, ≥ 0, A, B ∈ 𝒞, Q ∈ IsPosPoly (ANY polynomial with
  nonnegative coefficients, not only quadratic; no integrability hypothesis, so for a
  non-integrable integrand it reads 0 ≤ 0 by the Bochner convention),
    0 ≤ ∫ (A(t) − A(s))(B(t) − B(s)) e^{Q(t)+Q(s)} ∏_x w_x(t_x) w_x(s_x)
  (and `griffiths_second_dup_prod` on (ι → ℝ) × (ι → ℝ)).
* `integral_dup_expand` (Fubini) and **`griffiths_second_cone`**: with ρ = e^Q ∏ w_x and the four
  integrability hypotheses, (∫ A B ρ)(∫ ρ) ≥ (∫ A ρ)(∫ B ρ), A, B ∈ 𝒞.
* `griffithsSecond_of_integrable`: session 2's `GriffithsSecond w J` (J ≥ 0, w_x even ≥ 0) from
  integrability of the monomial moments of ferroDensity w J.
* `GinibreSite w` (the one-site condition, all four sign choices) and `ginibreSite_of_even`:
  it holds for EVERY even nonnegative w (as an integral; 0 by convention if not integrable); `ginibreSite_quartic`: for exp(−αy⁴ − βy²), any α, β.
  NOTE: no Ginibre-type hypothesis beyond evenness and w ≥ 0 is needed anywhere above (only
  `griffiths_second_cone` and the model results carry integrability hypotheses). With pair (quadratic) ferromagnetic
  couplings, Griffiths II holds for arbitrary even single-site weights (this is Ginibre's
  theorem): in (u, v) coordinates w(t)w(s) is even in u_x and in v_x separately, for any even w.
  The session-2 docstring remark "not true for every even w" is wrong for this setting.
* **`griffithsSecond_dweight`** (λ ≥ 0, m₀ ≠ 0): GriffithsSecond (siteWeight …) (Jnn n k);
  **`griffiths_second_dexpect`**: ⟨φ^a φ^b⟩ ≥ ⟨φ^a⟩⟨φ^b⟩ for the normalised quartic box measure;
  `griffiths_second_gibbs`: the same as integrals against the probability measure `gibbs`.

NOT formalized.
* Integrability of cone elements g · e^{Q} against dweight for Q of degree 2 (needed to apply
  `griffiths_second_cone` with A or B ∉ polynomials, e.g. in R3/R5 of PP2SimonLieb; it holds when
  Q's quadratic part is dominated by the Gaussian part of the weight, not proved here).
* The τ-monotonicity consequence of R3 (⟨H⟩_τ' ≤ ⟨H⟩_τ); only the covariance inequality is here.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
open MeasureTheory Finset PP2Target

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Griffiths

/-! ## Part 1: integrability of the moments of the quartic box measure -/

section Integrability

variable {n k : ℕ}

lemma integrable_pow_mul_gauss (m : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun y : ℝ => y ^ m * Real.exp (-b * y ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (m : ℝ))
    (by have := m.cast_nonneg (α := ℝ); linarith)
  simpa [Real.rpow_natCast] using h

lemma dgauss_pos (m₀ : ℝ) (φ : DField n k) : 0 < dgauss n k m₀ φ :=
  prod_pos fun _ _ => Real.exp_pos _

theorem integrable_mono_dgauss {m₀ : ℝ} (hm : m₀ ≠ 0) (a : DSite n k → ℕ) :
    Integrable fun φ : DField n k => (∏ x, φ x ^ a x) * dgauss n k m₀ φ := by
  have hb : 0 < m₀ ^ 2 * spacing n ^ 2 / 2 := by have := spacing_pos n; positivity
  have h := Integrable.fintype_prod (ι := DSite n k) (E := ℝ) (𝕜 := ℝ)
      (μ := fun _ => (volume : Measure ℝ))
      (f := fun x y => y ^ a x * Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * y ^ 2))
      (fun x => integrable_pow_mul_gauss (a x) hb)
  refine h.congr (Filter.Eventually.of_forall fun φ => ?_)
  simp only [dgauss, Finset.prod_mul_distrib]

/-- **Integrability of every monomial moment** of the quartic Dirichlet-box weight
(λ ≥ 0, m₀ ≠ 0): φ^a · dweight is integrable. -/
theorem integrable_mono_dweight {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (a : DSite n k → ℕ) :
    Integrable fun φ : DField n k =>
      (∏ x, φ x ^ a x) * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  set C := Real.exp (lam * spacing n ^ 2 * (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)))
  refine Integrable.mono' ((integrable_mono_dgauss hm a).abs.const_mul C) ?_
    (Filter.Eventually.of_forall fun φ => ?_)
  · exact ((by fun_prop : Continuous fun φ : DField n k => ∏ x, φ x ^ a x).mul
      (continuous_dweight m₀ lam _)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (show 0 < dweight n k m₀ lam (Polynomial.X ^ 4) φ from Real.exp_pos _),
      abs_of_pos (dgauss_pos m₀ φ)]
    calc |∏ x, φ x ^ a x| * dweight n k m₀ lam (Polynomial.X ^ 4) φ
        ≤ |∏ x, φ x ^ a x| * (C * dgauss n k m₀ φ) :=
          mul_le_mul_of_nonneg_left (dweight_le m₀ lam hlam φ) (abs_nonneg _)
      _ = C * (|∏ x, φ x ^ a x| * dgauss n k m₀ φ) := by ring

end Integrability

/-! ## Part 1b: the normalised quartic box measure as a genuine probability measure -/

section Gibbs

variable {n k : ℕ}

/-- The Gibbs measure of the quartic box model: density dweight / Z against Lebesgue. -/
def gibbs (n k : ℕ) (m₀ lam : ℝ) : Measure (DField n k) :=
  volume.withDensity fun φ => ENNReal.ofReal (dweight n k m₀ lam (Polynomial.X ^ 4) φ /
    ∫ ψ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) ψ)

lemma dweight_pos' (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) :
    0 < dweight n k m₀ lam P φ := Real.exp_pos _

lemma Z_nonneg (m₀ lam : ℝ) :
    0 ≤ ∫ ψ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) ψ :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- `dexpect` is the integral against `gibbs` (for every F, no hypotheses). -/
theorem integral_gibbs (m₀ lam : ℝ) (F : DField n k → ℝ) :
    ∫ φ, F φ ∂(gibbs n k m₀ lam) = dexpect n k m₀ lam F := by
  rw [gibbs, integral_withDensity_eq_integral_toReal_smul
    (((continuous_dweight m₀ lam _).measurable.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  rw [dexpect, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (div_nonneg (dweight_pos' _ _ _ _).le (Z_nonneg m₀ lam))]
  ring

/-- For λ ≥ 0, m₀ ≠ 0, `gibbs` is a probability measure. -/
theorem isProbabilityMeasure_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    IsProbabilityMeasure (gibbs n k m₀ lam) := by
  constructor
  rw [gibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_dweight hm hlam).div_const _)
      (Filter.Eventually.of_forall fun φ =>
        div_nonneg (dweight_pos' _ _ _ φ).le (Z_nonneg m₀ lam)),
    integral_div, div_self (integral_dweight_pos hm hlam).ne', ENNReal.ofReal_one]

/-- **Griffiths I, genuine form**: for λ ≥ 0, m₀ ≠ 0, the moment φ^a·dweight is integrable,
`gibbs` is a probability measure, and the expectation ∫ φ^a d(gibbs) = ⟨φ^a⟩ is ≥ 0. -/
theorem griffiths_first_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (a : DSite n k → ℕ) :
    Integrable (fun φ : DField n k => (∏ x, φ x ^ a x) * dweight n k m₀ lam (Polynomial.X ^ 4) φ)
      ∧ IsProbabilityMeasure (gibbs n k m₀ lam)
      ∧ ∫ φ, (∏ x, φ x ^ a x) ∂(gibbs n k m₀ lam) = dexpect n k m₀ lam (fun φ => ∏ x, φ x ^ a x)
      ∧ 0 ≤ ∫ φ, (∏ x, φ x ^ a x) ∂(gibbs n k m₀ lam) := by
  refine ⟨integrable_mono_dweight hm hlam a, isProbabilityMeasure_gibbs hm hlam,
    integral_gibbs m₀ lam _, ?_⟩
  rw [integral_gibbs]; exact dexpect_mono_nonneg m₀ lam a

end Gibbs

/-! ## Part 2: Griffiths II by duplicate variables -/

section Duplicate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma IsPosPoly.congr' {κ : Type*} [Fintype κ] [DecidableEq κ] {f g : (κ → ℝ) → ℝ}
    (hf : IsPosPoly f) (h : ∀ φ, f φ = g φ) : IsPosPoly g := by
  have : f = g := funext h
  rwa [← this]

/-- The per-site involutions of ℝ × ℝ: in the coordinates (u, v) = (t + s, t − s), `act e f`
flips the sign of u iff e and of v iff f. Concretely: id, (t,s) ↦ (s,t), (t,s) ↦ (−t,−s),
(t,s) ↦ (−s,−t). -/
def act : Bool → Bool → ℝ × ℝ → ℝ × ℝ
  | false, false, p => p
  | false, true, p => (p.2, p.1)
  | true, true, p => (-p.1, -p.2)
  | true, false, p => (-p.2, -p.1)

lemma act_involutive (e f : Bool) : Function.Involutive (act e f) := by
  intro p; cases e <;> cases f <;> simp [act]

lemma measurePreserving_act (e f : Bool) :
    MeasurePreserving (act e f) (volume : Measure (ℝ × ℝ)) volume := by
  have hneg : MeasurePreserving (fun p : ℝ × ℝ => (-p.1, -p.2)) volume volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hswap : MeasurePreserving (fun p : ℝ × ℝ => (p.2, p.1)) volume volume :=
    Measure.measurePreserving_swap
  cases e <;> cases f
  · exact MeasurePreserving.id _
  · exact hswap
  · exact hneg.comp hswap
  · exact hneg

/-- The sign-flip group of the doubled system, indexed by σ : ι ⊕ ι → Bool
(σ (inl x) flips u_x, σ (inr x) flips v_x). -/
def actPi (σ : ι ⊕ ι → Bool) (p : ι → ℝ × ℝ) : ι → ℝ × ℝ :=
  fun x => act (σ (Sum.inl x)) (σ (Sum.inr x)) (p x)

lemma measurePreserving_actPi (σ : ι ⊕ ι → Bool) :
    MeasurePreserving (actPi σ) (volume : Measure (ι → ℝ × ℝ)) volume :=
  volume_preserving_pi (fun x => measurePreserving_act (σ (Sum.inl x)) (σ (Sum.inr x)))

/-- `actPi σ` as a measurable equivalence. -/
def actEquiv (σ : ι ⊕ ι → Bool) : (ι → ℝ × ℝ) ≃ᵐ (ι → ℝ × ℝ) :=
  MeasurableEquiv.ofInvolutive (actPi σ)
    (fun p => funext fun x => act_involutive _ _ (p x)) (measurePreserving_actPi σ).measurable

/-- Sign averaging on the doubled system. -/
theorem integral_nonneg_of_actSum_nonneg {W : (ι → ℝ × ℝ) → ℝ}
    (hW_inv : ∀ σ p, W (actPi σ p) = W p) (hW_nonneg : ∀ p, 0 ≤ W p) (f : (ι → ℝ × ℝ) → ℝ)
    (hf : ∀ p, 0 ≤ ∑ σ : ι ⊕ ι → Bool, f (actPi σ p)) :
    0 ≤ ∫ p : ι → ℝ × ℝ, f p * W p := by
  set F : (ι → ℝ × ℝ) → ℝ := fun p => f p * W p with hFdef
  by_cases hint : Integrable F
  · have hcomp : ∀ σ : ι ⊕ ι → Bool,
        (fun p => f (actPi σ p) * W p) = fun p => F (actEquiv σ p) := by
      intro σ; funext p
      show _ = f (actPi σ p) * W (actPi σ p)
      rw [hW_inv]
    have hintσ : ∀ σ : ι ⊕ ι → Bool, Integrable (fun p => f (actPi σ p) * W p) := by
      intro σ; rw [hcomp σ]
      exact (measurePreserving_actPi σ).integrable_comp_of_integrable hint
    have hint_eq : ∀ σ : ι ⊕ ι → Bool, ∫ p, f (actPi σ p) * W p = ∫ p, F p := by
      intro σ; rw [hcomp σ]
      exact (measurePreserving_actPi σ).integral_comp' (f := actEquiv σ) F
    have hsum : ∫ p : ι → ℝ × ℝ, (∑ σ : ι ⊕ ι → Bool, f (actPi σ p)) * W p
        = (Fintype.card (ι ⊕ ι → Bool) : ℝ) * ∫ p, F p := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun σ _ => hintσ σ)]
      simp [hint_eq]
    have hnn : 0 ≤ ∫ p : ι → ℝ × ℝ, (∑ σ : ι ⊕ ι → Bool, f (actPi σ p)) * W p :=
      integral_nonneg fun p => mul_nonneg (hf p) (hW_nonneg p)
    rw [hsum] at hnn
    have hcard : (0 : ℝ) < Fintype.card (ι ⊕ ι → Bool) := by
      exact_mod_cast Fintype.card_pos
    exact nonneg_of_mul_nonneg_right (by linarith) hcard
  · rw [integral_undef hint]

/-- The (u, v) = (t + s, t − s) coordinates of a doubled configuration. -/
def uv (p : ι → ℝ × ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim (fun x => (p x).1 + (p x).2) (fun x => (p x).1 - (p x).2)

/-- **The doubled group acts on (u, v) by plain sign flips.** -/
theorem uv_actPi (σ : ι ⊕ ι → Bool) (p : ι → ℝ × ℝ) :
    uv (actPi σ p) = flipSigns σ (uv p) := by
  funext i
  cases i with
  | inl x =>
    simp only [uv, actPi, flipSigns, Sum.elim_inl, sgnMul]
    cases σ (Sum.inl x) <;> cases σ (Sum.inr x) <;> simp [act] <;> ring
  | inr x =>
    simp only [uv, actPi, flipSigns, Sum.elim_inr, sgnMul]
    cases σ (Sum.inl x) <;> cases σ (Sum.inr x) <;> simp [act] <;> ring

/-- t = (u + v)/2. -/
def tPart (ψ : ι ⊕ ι → ℝ) : ι → ℝ := fun x => (ψ (Sum.inl x) + ψ (Sum.inr x)) / 2

/-- s = (u − v)/2. -/
def sPart (ψ : ι ⊕ ι → ℝ) : ι → ℝ := fun x => (ψ (Sum.inl x) - ψ (Sum.inr x)) / 2

/-- The first copy t of a doubled configuration. -/
def fstF (p : ι → ℝ × ℝ) : ι → ℝ := fun x => (p x).1

/-- The second copy s of a doubled configuration. -/
def sndF (p : ι → ℝ × ℝ) : ι → ℝ := fun x => (p x).2

lemma tPart_uv (p : ι → ℝ × ℝ) : tPart (uv p) = fstF p := by
  funext x; simp only [tPart, uv, fstF, Sum.elim_inl, Sum.elim_inr]; ring

lemma sPart_uv (p : ι → ℝ × ℝ) : sPart (uv p) = sndF p := by
  funext x; simp only [sPart, uv, sndF, Sum.elim_inl, Sum.elim_inr]; ring

/-- f is "pair-positive": f(t) + f(s) and f(t) − f(s) are both polynomials with nonnegative
coefficients in (u, v) = (t + s, t − s). -/
def PairPos (f : (ι → ℝ) → ℝ) : Prop :=
  IsPosPoly (fun ψ : ι ⊕ ι → ℝ => f (tPart ψ) + f (sPart ψ)) ∧
    IsPosPoly (fun ψ : ι ⊕ ι → ℝ => f (tPart ψ) - f (sPart ψ))

namespace PairPos

lemma congr' {f g : (ι → ℝ) → ℝ} (hf : PairPos f) (h : ∀ φ, f φ = g φ) : PairPos g := by
  have : f = g := funext h
  rwa [← this]

lemma const {c : ℝ} (hc : 0 ≤ c) : PairPos (fun _ : ι → ℝ => c) :=
  ⟨(IsPosPoly.const (c := c + c) (by linarith)).congr' fun _ => rfl,
    (IsPosPoly.const (c := 0) le_rfl).congr' fun _ => by ring⟩

lemma coord (x : ι) : PairPos (fun φ : ι → ℝ => φ x) :=
  ⟨(IsPosPoly.coord (Sum.inl x)).congr' fun ψ => by simp only [tPart, sPart]; ring,
    (IsPosPoly.coord (Sum.inr x)).congr' fun ψ => by simp only [tPart, sPart]; ring⟩

lemma add {f g : (ι → ℝ) → ℝ} (hf : PairPos f) (hg : PairPos g) :
    PairPos (fun φ => f φ + g φ) :=
  ⟨(hf.1.add hg.1).congr' fun ψ => by ring, (hf.2.add hg.2).congr' fun ψ => by ring⟩

lemma mul {f g : (ι → ℝ) → ℝ} (hf : PairPos f) (hg : PairPos g) :
    PairPos (fun φ => f φ * g φ) :=
  ⟨((IsPosPoly.const (c := 1 / 2) (by norm_num)).mul
      ((hf.1.mul hg.1).add (hf.2.mul hg.2))).congr' fun ψ => by ring,
    ((IsPosPoly.const (c := 1 / 2) (by norm_num)).mul
      ((hf.1.mul hg.2).add (hf.2.mul hg.1))).congr' fun ψ => by ring⟩

lemma pow {f : (ι → ℝ) → ℝ} (hf : PairPos f) (m : ℕ) : PairPos (fun φ => f φ ^ m) := by
  induction m with
  | zero => exact (const zero_le_one).congr' fun φ => by simp
  | succ m ih => exact (ih.mul hf).congr' fun φ => by ring

lemma prod {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ} (hf : ∀ k ∈ s, PairPos (f k)) :
    PairPos (fun φ => ∏ k ∈ s, f k φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const zero_le_one).congr' fun φ => by simp
  | insert k s hk ih =>
    exact ((hf k (mem_insert_self k s)).mul (ih fun j hj => hf j (mem_insert_of_mem hj))).congr'
      fun φ => by rw [Finset.prod_insert hk]

lemma sum {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ} (hf : ∀ k ∈ s, PairPos (f k)) :
    PairPos (fun φ => ∑ k ∈ s, f k φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const le_rfl).congr' fun φ => by simp
  | insert k s hk ih =>
    exact ((hf k (mem_insert_self k s)).add (ih fun j hj => hf j (mem_insert_of_mem hj))).congr'
      fun φ => by rw [Finset.sum_insert hk]

lemma mono (b : ι → ℕ) : PairPos (mono b) :=
  (prod univ fun x _ => (coord x).pow (b x)).congr' fun _ => rfl

/-- **Every polynomial with nonnegative coefficients is pair-positive.** -/
theorem of_isPosPoly {f : (ι → ℝ) → ℝ} (hf : IsPosPoly f) : PairPos f := by
  obtain ⟨κ, _, c, b, hc, hf⟩ := hf
  exact (sum univ fun k _ => (const (hc k)).mul (mono (b k))).congr' fun φ => (hf φ).symm

end PairPos

/-- The cone 𝒞 = {g · exp Q : g, Q polynomials with nonnegative coefficients}. -/
def InCone (A : (ι → ℝ) → ℝ) : Prop :=
  ∃ g Q : (ι → ℝ) → ℝ, IsPosPoly g ∧ IsPosPoly Q ∧ ∀ φ, A φ = g φ * Real.exp (Q φ)

lemma InCone.of_isPosPoly {g : (ι → ℝ) → ℝ} (hg : IsPosPoly g) : InCone g :=
  ⟨g, fun _ => 0, hg, IsPosPoly.const le_rfl, fun φ => by simp⟩

lemma hasSum_expTerm (g Q : (ι → ℝ) → ℝ) (φ : ι → ℝ) :
    HasSum (fun m : ℕ => g φ * Q φ ^ m * ((m.factorial : ℝ))⁻¹) (g φ * Real.exp (Q φ)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (Q φ)).mul_left (g φ)
  rw [Real.exp_eq_exp_ℝ]
  convert h using 2 with m
  ring

/-- The doubled integrand (A(t) − A(s))(B(t) − B(s)) e^{Q(t) + Q(s)}. -/
def dupIntegrand (A B Q : (ι → ℝ) → ℝ) (p : ι → ℝ × ℝ) : ℝ :=
  (A (fstF p) - A (sndF p)) * (B (fstF p) - B (sndF p)) * Real.exp (Q (fstF p) + Q (sndF p))

/-- The same in (u, v) coordinates. -/
def dupG (A B Q : (ι → ℝ) → ℝ) (ψ : ι ⊕ ι → ℝ) : ℝ :=
  (A (tPart ψ) - A (sPart ψ)) * (B (tPart ψ) - B (sPart ψ))
    * Real.exp (Q (tPart ψ) + Q (sPart ψ))

end Duplicate

end PP2Griffiths

end

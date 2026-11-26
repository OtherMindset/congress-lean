import LongTable.Q_PP2Griffiths3A

/-!
Part B of PP2Griffiths3 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Griffiths3.lean)

FORMALIZED in this part.
* Doubled system on ι → ℝ × ℝ: per-site involutions `act` ((t,s) ↦ (s,t), (−s,−t), (−t,−s)),
  all Lebesgue-preserving; `uv_actPi`: in (u, v) = (t + s, t − s) they are exactly the sign flips
  `flipSigns`; `integral_nonneg_of_actSum_nonneg` (sign averaging on the doubled space, no change
  of variables); `integral_uv_nonneg`: ∫ G(u, v) ∏ w_x(t_x) w_x(s_x) ≥ 0 for G with nonnegative
  coefficients.
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

section Duplicate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise sign-averaged positivity, polynomial A, cone B. -/
lemma signSum_dupG_poly_cone {A B Q : (ι → ℝ) → ℝ} (hA : IsPosPoly A) (hB : InCone B)
    (hQ : IsPosPoly Q) (ψ : ι ⊕ ι → ℝ) :
    0 ≤ ∑ σ : ι ⊕ ι → Bool, dupG A B Q (flipSigns σ ψ) := by
  obtain ⟨gB, QB, hgB, hQB, hBe⟩ := hB
  set b : ℕ → (ι → ℝ) → ℝ := fun m φ => gB φ * QB φ ^ m * ((m.factorial : ℝ))⁻¹ with hb
  have hbpos : ∀ m, IsPosPoly (b m) := fun m =>
    (hgB.mul (hQB.pow m)).mul (IsPosPoly.const (by positivity))
  have hs : HasSum (fun m : ℕ => ∑ σ : ι ⊕ ι → Bool, dupG A (b m) Q (flipSigns σ ψ))
      (∑ σ : ι ⊕ ι → Bool, dupG A B Q (flipSigns σ ψ)) := by
    refine hasSum_sum fun σ _ => ?_
    set χ := flipSigns σ ψ
    have h1 := ((hasSum_expTerm gB QB (tPart χ)).sub (hasSum_expTerm gB QB (sPart χ))).mul_left
      (A (tPart χ) - A (sPart χ))
    have h2 := h1.mul_right (Real.exp (Q (tPart χ) + Q (sPart χ)))
    simp only [dupG, hBe]
    exact h2
  refine hs.nonneg fun m => ?_
  exact signSum_mul_exp_nonneg ((PairPos.of_isPosPoly hA).2.mul (PairPos.of_isPosPoly (hbpos m)).2)
    (PairPos.of_isPosPoly hQ).1 ψ

/-- Pointwise sign-averaged positivity, both A and B in the cone. -/
theorem signSum_dupG_nonneg {A B Q : (ι → ℝ) → ℝ} (hA : InCone A) (hB : InCone B)
    (hQ : IsPosPoly Q) (ψ : ι ⊕ ι → ℝ) :
    0 ≤ ∑ σ : ι ⊕ ι → Bool, dupG A B Q (flipSigns σ ψ) := by
  obtain ⟨gA, QA, hgA, hQA, hAe⟩ := hA
  set a : ℕ → (ι → ℝ) → ℝ := fun m φ => gA φ * QA φ ^ m * ((m.factorial : ℝ))⁻¹ with ha
  have hapos : ∀ m, IsPosPoly (a m) := fun m =>
    (hgA.mul (hQA.pow m)).mul (IsPosPoly.const (by positivity))
  have hs : HasSum (fun m : ℕ => ∑ σ : ι ⊕ ι → Bool, dupG (a m) B Q (flipSigns σ ψ))
      (∑ σ : ι ⊕ ι → Bool, dupG A B Q (flipSigns σ ψ)) := by
    refine hasSum_sum fun σ _ => ?_
    set χ := flipSigns σ ψ
    have h1 := ((hasSum_expTerm gA QA (tPart χ)).sub (hasSum_expTerm gA QA (sPart χ))).mul_right
      (B (tPart χ) - B (sPart χ))
    have h2 := h1.mul_right (Real.exp (Q (tPart χ) + Q (sPart χ)))
    simp only [dupG, hAe]
    exact h2
  exact hs.nonneg fun m => signSum_dupG_poly_cone (hapos m) hB hQ ψ

/-- The doubled product weight ∏_x w_x(t_x) w_x(s_x). -/
def dupWeight (w : ι → ℝ → ℝ) (p : ι → ℝ × ℝ) : ℝ := ∏ x, (w x (p x).1 * w x (p x).2)

lemma dupWeight_act {w : ι → ℝ → ℝ} (hw : ∀ x y, w x (-y) = w x y) (σ : ι ⊕ ι → Bool)
    (p : ι → ℝ × ℝ) : dupWeight w (actPi σ p) = dupWeight w p := by
  refine prod_congr rfl fun x _ => ?_
  simp only [actPi]
  cases σ (Sum.inl x) <;> cases σ (Sum.inr x) <;> simp [act, hw, mul_comm]

/-- **Griffiths II, duplicate-variable form, in the cone.** For site-dependent even weights
w_x ≥ 0, A, B ∈ 𝒞 and Q with nonnegative coefficients,
  0 ≤ ∫ (A(t) − A(s))(B(t) − B(s)) e^{Q(t)+Q(s)} ∏_x w_x(t_x) w_x(s_x). -/
theorem griffiths_second_dup {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {A B Q : (ι → ℝ) → ℝ} (hA : InCone A) (hB : InCone B)
    (hQ : IsPosPoly Q) :
    0 ≤ ∫ p : ι → ℝ × ℝ, dupIntegrand A B Q p * dupWeight w p := by
  refine integral_nonneg_of_actSum_nonneg (dupWeight_act hw_even)
    (fun p => prod_nonneg fun x _ => mul_nonneg (hw_nonneg _ _) (hw_nonneg _ _)) _ fun p => ?_
  have hG : ∀ p, dupIntegrand A B Q p = dupG A B Q (uv p) := by
    intro p; simp only [dupG, tPart_uv, sPart_uv]; rfl
  simp_rw [hG, uv_actPi]
  exact signSum_dupG_nonneg hA hB hQ (uv p)

/-- The same on (ι → ℝ) × (ι → ℝ), with ρ = e^Q ∏ w. -/
theorem griffiths_second_dup_prod {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {A B Q : (ι → ℝ) → ℝ} (hA : InCone A) (hB : InCone B)
    (hQ : IsPosPoly Q) :
    0 ≤ ∫ q : (ι → ℝ) × (ι → ℝ), (A q.1 - A q.2) * (B q.1 - B q.2)
      * (Real.exp (Q q.1) * ∏ x, w x (q.1 x)) * (Real.exp (Q q.2) * ∏ x, w x (q.2 x)) := by
  have h := griffiths_second_dup hw_even hw_nonneg hA hB hQ
  have e := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).integral_comp'
    (fun q : (ι → ℝ) × (ι → ℝ) => (A q.1 - A q.2) * (B q.1 - B q.2)
      * (Real.exp (Q q.1) * ∏ x, w x (q.1 x)) * (Real.exp (Q q.2) * ∏ x, w x (q.2 x)))
  refine (h.trans_eq ?_).trans_eq e
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  change dupIntegrand A B Q p * dupWeight w p =
    (A (fstF p) - A (sndF p)) * (B (fstF p) - B (sndF p))
      * (Real.exp (Q (fstF p)) * ∏ x, w x (p x).1) * (Real.exp (Q (sndF p)) * ∏ x, w x (p x).2)
  simp only [dupIntegrand, dupWeight, prod_mul_distrib, Real.exp_add]
  ring

/-- Fubini expansion of the doubled integral. -/
theorem integral_dup_expand {ρ A B : (ι → ℝ) → ℝ}
    (hABρ : Integrable fun φ => A φ * B φ * ρ φ) (hAρ : Integrable fun φ => A φ * ρ φ)
    (hBρ : Integrable fun φ => B φ * ρ φ) (hρ : Integrable ρ) :
    ∫ q : (ι → ℝ) × (ι → ℝ), (A q.1 - A q.2) * (B q.1 - B q.2) * ρ q.1 * ρ q.2 =
      2 * ((∫ φ, A φ * B φ * ρ φ) * (∫ φ, ρ φ) - (∫ φ, A φ * ρ φ) * (∫ φ, B φ * ρ φ)) := by
  have e : ∀ q : (ι → ℝ) × (ι → ℝ), (A q.1 - A q.2) * (B q.1 - B q.2) * ρ q.1 * ρ q.2 =
      ((A q.1 * B q.1 * ρ q.1) * ρ q.2 - (A q.1 * ρ q.1) * (B q.2 * ρ q.2))
      - ((B q.1 * ρ q.1) * (A q.2 * ρ q.2) - ρ q.1 * (A q.2 * B q.2 * ρ q.2)) :=
    fun q => by ring
  simp_rw [e]
  have i1 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => (A q.1 * B q.1 * ρ q.1) * ρ q.2 :=
    hABρ.mul_prod hρ
  have i2 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => (A q.1 * ρ q.1) * (B q.2 * ρ q.2) :=
    hAρ.mul_prod hBρ
  have i3 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => (B q.1 * ρ q.1) * (A q.2 * ρ q.2) :=
    hBρ.mul_prod hAρ
  have i4 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => ρ q.1 * (A q.2 * B q.2 * ρ q.2) :=
    hρ.mul_prod hABρ
  have p1 : ∫ q : (ι → ℝ) × (ι → ℝ), (A q.1 * B q.1 * ρ q.1) * ρ q.2
      = (∫ φ, A φ * B φ * ρ φ) * ∫ φ, ρ φ :=
    integral_prod_mul (μ := volume) (ν := volume) (fun φ => A φ * B φ * ρ φ) ρ
  have p2 : ∫ q : (ι → ℝ) × (ι → ℝ), (A q.1 * ρ q.1) * (B q.2 * ρ q.2)
      = (∫ φ, A φ * ρ φ) * ∫ φ, B φ * ρ φ :=
    integral_prod_mul (μ := volume) (ν := volume) (fun φ => A φ * ρ φ) (fun φ => B φ * ρ φ)
  have p3 : ∫ q : (ι → ℝ) × (ι → ℝ), (B q.1 * ρ q.1) * (A q.2 * ρ q.2)
      = (∫ φ, B φ * ρ φ) * ∫ φ, A φ * ρ φ :=
    integral_prod_mul (μ := volume) (ν := volume) (fun φ => B φ * ρ φ) (fun φ => A φ * ρ φ)
  have p4 : ∫ q : (ι → ℝ) × (ι → ℝ), ρ q.1 * (A q.2 * B q.2 * ρ q.2)
      = (∫ φ, ρ φ) * ∫ φ, A φ * B φ * ρ φ :=
    integral_prod_mul (μ := volume) (ν := volume) ρ (fun φ => A φ * B φ * ρ φ)
  have s1 : ∫ q : (ι → ℝ) × (ι → ℝ),
      ((A q.1 * B q.1 * ρ q.1) * ρ q.2 - (A q.1 * ρ q.1) * (B q.2 * ρ q.2))
      - ((B q.1 * ρ q.1) * (A q.2 * ρ q.2) - ρ q.1 * (A q.2 * B q.2 * ρ q.2))
      = (∫ q : (ι → ℝ) × (ι → ℝ),
          (A q.1 * B q.1 * ρ q.1) * ρ q.2 - (A q.1 * ρ q.1) * (B q.2 * ρ q.2))
        - ∫ q : (ι → ℝ) × (ι → ℝ),
          (B q.1 * ρ q.1) * (A q.2 * ρ q.2) - ρ q.1 * (A q.2 * B q.2 * ρ q.2) :=
    integral_sub (i1.sub i2) (i3.sub i4)
  have s2 : ∫ q : (ι → ℝ) × (ι → ℝ),
      (A q.1 * B q.1 * ρ q.1) * ρ q.2 - (A q.1 * ρ q.1) * (B q.2 * ρ q.2)
      = (∫ q : (ι → ℝ) × (ι → ℝ), (A q.1 * B q.1 * ρ q.1) * ρ q.2)
        - ∫ q : (ι → ℝ) × (ι → ℝ), (A q.1 * ρ q.1) * (B q.2 * ρ q.2) := integral_sub i1 i2
  have s3 : ∫ q : (ι → ℝ) × (ι → ℝ),
      (B q.1 * ρ q.1) * (A q.2 * ρ q.2) - ρ q.1 * (A q.2 * B q.2 * ρ q.2)
      = (∫ q : (ι → ℝ) × (ι → ℝ), (B q.1 * ρ q.1) * (A q.2 * ρ q.2))
        - ∫ q : (ι → ℝ) × (ι → ℝ), ρ q.1 * (A q.2 * B q.2 * ρ q.2) := integral_sub i3 i4
  rw [s1, s2, s3, p1, p2, p3, p4]
  ring

/-- **Griffiths II in the cone, unnormalised** (site-dependent even weights, Q ≥ 0 coefficients,
A, B ∈ 𝒞), assuming the four integrability conditions:
  (∫ A B ρ)(∫ ρ) ≥ (∫ A ρ)(∫ B ρ),   ρ = e^Q ∏_x w_x. -/
theorem griffiths_second_cone {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {A B Q : (ι → ℝ) → ℝ} (hA : InCone A) (hB : InCone B)
    (hQ : IsPosPoly Q)
    (hABρ : Integrable fun φ => A φ * B φ * (Real.exp (Q φ) * ∏ x, w x (φ x)))
    (hAρ : Integrable fun φ => A φ * (Real.exp (Q φ) * ∏ x, w x (φ x)))
    (hBρ : Integrable fun φ => B φ * (Real.exp (Q φ) * ∏ x, w x (φ x)))
    (hρ : Integrable fun φ => Real.exp (Q φ) * ∏ x, w x (φ x)) :
    (∫ φ, A φ * B φ * (Real.exp (Q φ) * ∏ x, w x (φ x))) * (∫ φ, Real.exp (Q φ) * ∏ x, w x (φ x))
      ≥ (∫ φ, A φ * (Real.exp (Q φ) * ∏ x, w x (φ x)))
        * (∫ φ, B φ * (Real.exp (Q φ) * ∏ x, w x (φ x))) := by
  have h := griffiths_second_dup_prod hw_even hw_nonneg hA hB hQ
  rw [integral_dup_expand (ρ := fun φ => Real.exp (Q φ) * ∏ x, w x (φ x)) hABρ hAρ hBρ hρ] at h
  linarith

/-- **Griffiths II (`GriffithsSecond`) for site-dependent even weights and J ≥ 0**, given
integrability of the monomial moments. No Ginibre-type condition on w beyond evenness is needed. -/
theorem griffithsSecond_of_integrable {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y)
    (hint : ∀ a : ι → ℕ, Integrable fun φ => (∏ x, φ x ^ a x) * ferroDensity w J φ) :
    GriffithsSecond w J := by
  intro a b
  have hAB : Integrable fun φ : ι → ℝ =>
      (∏ x, φ x ^ a x) * (∏ x, φ x ^ b x) * ferroDensity w J φ :=
    (hint (a + b)).congr (Filter.Eventually.of_forall fun φ => by
      simp only [Pi.add_apply, pow_add, prod_mul_distrib])
  have h0 : Integrable fun φ : ι → ℝ => ferroDensity w J φ :=
    (hint 0).congr (Filter.Eventually.of_forall fun φ => by simp)
  exact griffiths_second_cone (A := fun φ => ∏ x, φ x ^ a x) (B := fun φ => ∏ x, φ x ^ b x)
    hw_even hw_nonneg (InCone.of_isPosPoly (IsPosPoly.ofMono a))
    (InCone.of_isPosPoly (IsPosPoly.ofMono b)) (IsPosPoly.quadForm hJ) hAB (hint a) (hint b) h0

/-- Doubled sign averaging for any polynomial with nonnegative coefficients in (u, v). -/
theorem integral_uv_nonneg {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {G : (ι ⊕ ι → ℝ) → ℝ} (hG : IsPosPoly G) :
    0 ≤ ∫ p : ι → ℝ × ℝ, G (uv p) * dupWeight w p :=
  integral_nonneg_of_actSum_nonneg (dupWeight_act hw_even)
    (fun p => prod_nonneg fun x _ => mul_nonneg (hw_nonneg _ _) (hw_nonneg _ _)) _
    fun p => by simp_rw [uv_actPi]; exact hG.signSum_nonneg _

lemma PairPos.part {f : (ι → ℝ) → ℝ} (hf : PairPos f) (e : Bool) :
    IsPosPoly (fun ψ : ι ⊕ ι → ℝ => f (tPart ψ) + sgnMul e (f (sPart ψ))) := by
  cases e
  · exact hf.1.congr' fun ψ => by simp [sgnMul]
  · exact hf.2.congr' fun ψ => by simp [sgnMul]; ring

/-- Ginibre's one-site condition: ∫∫ (t^a ± s^a)(t^b ± s^b) w(t) w(s) ≥ 0 for all a, b and
all four sign choices (`sgnMul true y = −y`). -/
def GinibreSite (w : ℝ → ℝ) : Prop :=
  ∀ (a b : ℕ) (e f : Bool), 0 ≤ ∫ q : ℝ × ℝ,
    (q.1 ^ a + sgnMul e (q.2 ^ a)) * (q.1 ^ b + sgnMul f (q.2 ^ b)) * (w q.1 * w q.2)

/-- **Ginibre's condition holds for every even nonnegative one-site weight** (the one-site case of
the rotation argument: in (u, v) = (t + s, t − s), t^a ± s^a has nonnegative coefficients and
w(t)w(s) is even in u and in v separately). -/
theorem ginibreSite_of_even {w : ℝ → ℝ} (hw_even : ∀ y, w (-y) = w y) (hw_nonneg : ∀ y, 0 ≤ w y) :
    GinibreSite w := by
  intro a b e f
  have h := integral_uv_nonneg (ι := Unit) (w := fun _ => w) (fun _ => hw_even)
    (fun _ => hw_nonneg) (((PairPos.mono (fun _ : Unit => a)).part e).mul
      ((PairPos.mono (fun _ : Unit => b)).part f))
  have hE := (volume_preserving_funUnique Unit (ℝ × ℝ)).integral_comp'
    (fun q : ℝ × ℝ => (q.1 ^ a + sgnMul e (q.2 ^ a)) * (q.1 ^ b + sgnMul f (q.2 ^ b))
      * (w q.1 * w q.2))
  refine (h.trans_eq ?_).trans_eq hE
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [tPart_uv, sPart_uv, mono, dupWeight, fstF, sndF, Finset.univ_unique,
    Finset.prod_singleton]
  rfl

/-- In particular for the φ⁴ one-site weight exp(−α y⁴ − β y²) (any α, β). -/
theorem ginibreSite_quartic (α β : ℝ) :
    GinibreSite (fun y => Real.exp (-α * y ^ 4 - β * y ^ 2)) :=
  ginibreSite_of_even (fun y => by ring_nf) (fun _ => (Real.exp_pos _).le)

end Duplicate

/-! ## Part 3: Griffiths II for the quartic Dirichlet-box measure -/

section ModelII

variable {n k : ℕ}

lemma ferroDensity_dweight (m₀ lam : ℝ) (P : Polynomial ℝ) :
    ferroDensity (siteWeight n k m₀ lam P) (Jnn n k) = dweight n k m₀ lam P :=
  funext fun φ => (dweight_eq_ferro m₀ lam P φ).symm

/-- **Griffiths II for the quartic Dirichlet-box weight (unnormalised)**, λ ≥ 0, m₀ ≠ 0. -/
theorem griffithsSecond_dweight {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    GriffithsSecond (siteWeight n k m₀ lam (Polynomial.X ^ 4)) (Jnn n k) := by
  refine griffithsSecond_of_integrable (siteWeight_even fun y => wickPoly_X4_neg _ y)
    (fun _ _ => (Real.exp_pos _).le) Jnn_nonneg fun a => ?_
  rw [ferroDensity_dweight]
  exact integrable_mono_dweight hm hlam a

/-- **Griffiths II for the normalised quartic box measure**: for λ ≥ 0, m₀ ≠ 0,
⟨φ^a φ^b⟩ ≥ ⟨φ^a⟩⟨φ^b⟩. -/
theorem griffiths_second_dexpect {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (a b : DSite n k → ℕ) :
    dexpect n k m₀ lam (fun φ => (∏ x, φ x ^ a x) * ∏ x, φ x ^ b x) ≥
      dexpect n k m₀ lam (fun φ => ∏ x, φ x ^ a x) * dexpect n k m₀ lam (fun φ => ∏ x, φ x ^ b x) := by
  have h := griffithsSecond_dweight (n := n) (k := k) hm hlam a b
  rw [ferroDensity_dweight] at h
  have hZ := integral_dweight_pos (n := n) (k := k) hm hlam
  simp only [dexpect]
  rw [ge_iff_le, div_mul_div_comm, div_le_div_iff₀ (mul_pos hZ hZ) hZ]
  have h' := mul_le_mul_of_nonneg_right (ge_iff_le.mp h) hZ.le
  nlinarith

/-- The same in terms of the Gibbs probability measure. -/
theorem griffiths_second_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (a b : DSite n k → ℕ) :
    ∫ φ, (∏ x, φ x ^ a x) * (∏ x, φ x ^ b x) ∂(gibbs n k m₀ lam) ≥
      (∫ φ, (∏ x, φ x ^ a x) ∂(gibbs n k m₀ lam)) * ∫ φ, (∏ x, φ x ^ b x) ∂(gibbs n k m₀ lam) := by
  simp only [integral_gibbs]
  exact griffiths_second_dexpect hm hlam a b

end ModelII

end PP2Griffiths

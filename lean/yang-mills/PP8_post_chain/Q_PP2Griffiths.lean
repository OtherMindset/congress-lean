import Mathlib

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Griffiths.lean (same content; only the imports are renamed).
Long Table, P(φ)₂ direction, node M2 (session 1): Griffiths' first inequality, finite-dimensional
core, for lattice fields with an even single-site weight and a ferromagnetic quadratic coupling.

CAVEAT (read first): all inequalities are for the Bochner integral, which is 0 when the
integrand is not integrable. NO integrability is proved or assumed here, so each statement is
trivially true in non-integrable cases. They are numerators only. (Integrability and the
normalised statements for the model are in PP2Griffiths2/PP2Griffiths3.)

FORMALIZED.
* `PP2Griffiths.griffiths_first`: for a finite type ι, any w : ℝ → ℝ with w(−y) = w(y) and
  w ≥ 0, any J : ι → ι → ℝ with J ≥ 0 entrywise (symmetry is NOT needed), and any a : ι → ℕ,
    0 ≤ ∫ φ, (∏ x, φ x ^ a x) * exp(Σ_{x,y} J x y φ x φ y) * ∏ x, w (φ x).
  No integrability hypothesis is needed for the statement as written: if the integrand is not
  integrable, the Bochner integral is 0 by convention. When it is integrable (which a user must
  prove separately to make the statement meaningful, e.g. from w(y) ≤ C e^{−β y²} with β large
  against J), the inequality is the genuine Griffiths I.
* `PP2Griffiths.griffiths_first_field`: the same with an external field h ≥ 0 added,
  exp(Σ J φφ + Σ h φ).
* `PP2Griffiths.griffiths_first_general`: the same for g · exp(Q) where g and Q are polynomials with
  nonnegative coefficients (`IsPosPoly`).
* `PP2Griffiths.integral_nonneg_of_signSum_nonneg`: the measure-theoretic step: if
  Σ_{σ ∈ {±1}^ι} f(σφ) ≥ 0 for every φ, then ∫ f(φ) ∏ w(φ x) ≥ 0 (w even, ≥ 0).
* `PP2Griffiths.IsPosPoly.signSum_nonneg`: for a polynomial with nonnegative coefficients,
  Σ_σ f(σφ) ≥ 0 pointwise (it factorizes into ∏_x ((φ x)^k + (−φ x)^k) ≥ 0), and
  `PP2Griffiths.signSum_mul_exp_nonneg`: the same for g · exp(Q), by the exponential series.
* `PP2Griffiths.integral_mono_factorizes`: the factorization ∫ φ^b ∏ w(φ x) = ∏_x ∫ y^{b x} w(y).

Proof route: NOT the "exchange series and integral" route. Instead, average over the 2^|ι| sign
flips (each is measure-preserving and fixes ∏ w) to reduce to the pointwise inequality
Σ_σ f(σφ) ≥ 0, which is proved by expanding exp as a power series (a finite sum over σ commutes
with the series), so no dominated/monotone convergence argument is needed.

NOT formalized.
* Integrability of the integrand (e.g. from Gaussian decay of w); not needed for the inequality.
* Application to `PP2Target.dweight`: −½ dirAction splits as
  Σ_{unordered nn pairs inside the box} φ x φ y (coefficient +1 per unordered pair, i.e. J x y = 1/2
  per ordered pair in the Σ_{x,y} form; ferromagnetic) plus a single-site part
  −½ Σ_x (4 + ε² m₀²) φ x² (every site has exactly 4 incident bonds, counting bonds to the zero
  extension), which together with −λ ε² :P:(φ x) gives one site-independent weight w. No
  site-dependent w is needed. The algebraic identity for dirAction and the evenness of w are not
  proved here (both are proved in PP2Griffiths2).
* Griffiths II.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Griffiths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The monomial φ^b = ∏ x, φ x ^ b x. -/
def mono (b : ι → ℕ) (φ : ι → ℝ) : ℝ := ∏ x, φ x ^ b x

/-- Multiplication by the sign attached to a Boolean (true ↦ −1). -/
def sgnMul (s : Bool) (y : ℝ) : ℝ := if s then -y else y

/-- The sign flip φ ↦ σφ. -/
def flipSigns (σ : ι → Bool) (φ : ι → ℝ) : ι → ℝ := fun x => sgnMul (σ x) (φ x)

/-- Polynomials with nonnegative coefficients. -/
def IsPosPoly (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℝ) (b : κ → ι → ℕ),
    (∀ k, 0 ≤ c k) ∧ ∀ φ, f φ = ∑ k, c k * mono (b k) φ

lemma mono_add (b b' : ι → ℕ) (φ : ι → ℝ) : mono (b + b') φ = mono b φ * mono b' φ := by
  simp [mono, pow_add, prod_mul_distrib]

lemma signSum_mono_nonneg (b : ι → ℕ) (φ : ι → ℝ) :
    0 ≤ ∑ σ : ι → Bool, mono b (flipSigns σ φ) := by
  have h : ∑ σ : ι → Bool, mono b (flipSigns σ φ)
      = ∏ x, ∑ t : Bool, (sgnMul t (φ x)) ^ (b x) :=
    (Fintype.prod_sum (fun x (t : Bool) => (sgnMul t (φ x)) ^ (b x))).symm
  rw [h]
  refine prod_nonneg fun x _ => ?_
  rw [Fintype.sum_bool]
  simp only [sgnMul, ite_true, Bool.false_eq_true, ite_false]
  rcases Nat.even_or_odd (b x) with he | ho
  · rw [he.neg_pow]; have := he.pow_nonneg (φ x); linarith
  · rw [ho.neg_pow]; simp

namespace IsPosPoly

lemma signSum_nonneg {f : (ι → ℝ) → ℝ} (hf : IsPosPoly f) (φ : ι → ℝ) :
    0 ≤ ∑ σ : ι → Bool, f (flipSigns σ φ) := by
  obtain ⟨κ, _, c, b, hc, hf⟩ := hf
  simp_rw [hf]
  rw [Finset.sum_comm]
  refine sum_nonneg fun k _ => ?_
  rw [← Finset.mul_sum]
  exact mul_nonneg (hc k) (signSum_mono_nonneg _ _)

lemma const {c : ℝ} (hc : 0 ≤ c) : IsPosPoly (fun _ : ι → ℝ => c) :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => 0, fun _ => hc, fun φ => by simp [mono]⟩

lemma ofMono (b : ι → ℕ) : IsPosPoly (mono b) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => b, fun _ => zero_le_one, fun φ => by simp⟩

lemma coord (x : ι) : IsPosPoly (fun φ : ι → ℝ => φ x) := by
  have h : (fun φ : ι → ℝ => φ x) = mono (Pi.single x 1) := by
    funext φ
    unfold mono
    rw [Finset.prod_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  rw [h]; exact ofMono _

lemma add {f g : (ι → ℝ) → ℝ} (hf : IsPosPoly f) (hg : IsPosPoly g) :
    IsPosPoly (fun φ => f φ + g φ) := by
  obtain ⟨κ, _, c, b, hc, hf⟩ := hf
  obtain ⟨κ', _, c', b', hc', hg⟩ := hg
  refine ⟨κ ⊕ κ', inferInstance, Sum.elim c c', Sum.elim b b', ?_, fun φ => ?_⟩
  · intro k; cases k <;> simp [hc, hc']
  · show f φ + g φ = _
    rw [Fintype.sum_sum_type, hf, hg]; simp

lemma mul {f g : (ι → ℝ) → ℝ} (hf : IsPosPoly f) (hg : IsPosPoly g) :
    IsPosPoly (fun φ => f φ * g φ) := by
  obtain ⟨κ, _, c, b, hc, hf⟩ := hf
  obtain ⟨κ', _, c', b', hc', hg⟩ := hg
  refine ⟨κ × κ', inferInstance, fun k => c k.1 * c' k.2, fun k => b k.1 + b' k.2,
    fun k => mul_nonneg (hc _) (hc' _), fun φ => ?_⟩
  show f φ * g φ = _
  rw [hf, hg, Fintype.sum_mul_sum, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [mono_add]; ring

lemma pow {f : (ι → ℝ) → ℝ} (hf : IsPosPoly f) (n : ℕ) : IsPosPoly (fun φ => f φ ^ n) := by
  induction n with
  | zero => simpa using const (ι := ι) zero_le_one
  | succ n ih => simpa [pow_succ] using ih.mul hf

lemma sum {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ} (hf : ∀ k ∈ s, IsPosPoly (f k)) :
    IsPosPoly (fun φ => ∑ k ∈ s, f k φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (ι := ι) le_rfl
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k (mem_insert_self k s)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

/-- The ferromagnetic quadratic form Σ J x y φ x φ y is a polynomial with nonnegative
coefficients. -/
lemma quadForm {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) :
    IsPosPoly (fun φ : ι → ℝ => ∑ x, ∑ y, J x y * φ x * φ y) :=
  sum _ fun x _ => sum _ fun y _ => ((const (hJ x y)).mul (coord x)).mul (coord y)

lemma linForm {h : ι → ℝ} (hh : ∀ x, 0 ≤ h x) :
    IsPosPoly (fun φ : ι → ℝ => ∑ x, h x * φ x) :=
  sum _ fun x _ => (const (hh x)).mul (coord x)

end IsPosPoly

/-- Pointwise sign-averaged positivity of g · exp(Q) for g, Q with nonnegative coefficients. -/
lemma signSum_mul_exp_nonneg {g Q : (ι → ℝ) → ℝ} (hg : IsPosPoly g) (hQ : IsPosPoly Q)
    (φ : ι → ℝ) :
    0 ≤ ∑ σ : ι → Bool, g (flipSigns σ φ) * Real.exp (Q (flipSigns σ φ)) := by
  have hs : HasSum (fun n : ℕ => ∑ σ : ι → Bool,
        g (flipSigns σ φ) * Q (flipSigns σ φ) ^ n * ((n.factorial : ℝ))⁻¹)
      (∑ σ : ι → Bool, g (flipSigns σ φ) * Real.exp (Q (flipSigns σ φ))) := by
    refine hasSum_sum fun σ _ => ?_
    have h := (NormedSpace.expSeries_div_hasSum_exp (Q (flipSigns σ φ))).mul_left
      (g (flipSigns σ φ))
    rw [Real.exp_eq_exp_ℝ]
    convert h using 2 with n
    ring
  refine hs.nonneg fun n => ?_
  exact ((hg.mul (hQ.pow n)).mul (IsPosPoly.const (by positivity))).signSum_nonneg φ

lemma sgnMul_involutive (s : Bool) : Function.Involutive (sgnMul s) := by
  intro y; cases s <;> simp [sgnMul]

lemma measurePreserving_sgnMul (s : Bool) :
    MeasurePreserving (sgnMul s) (volume : Measure ℝ) volume := by
  cases s
  · exact MeasurePreserving.id _
  · exact Measure.measurePreserving_neg _

omit [DecidableEq ι] in
lemma measurable_flipSigns (σ : ι → Bool) : Measurable (flipSigns σ) :=
  (volume_preserving_pi (fun x => measurePreserving_sgnMul (σ x))).measurable

/-- The sign flip as a measurable equivalence. -/
def flipEquiv (σ : ι → Bool) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.ofInvolutive (flipSigns σ)
    (fun φ => funext fun x => sgnMul_involutive (σ x) (φ x)) (measurable_flipSigns σ)

lemma measurePreserving_flipEquiv (σ : ι → Bool) :
    MeasurePreserving (flipEquiv σ) (volume : Measure (ι → ℝ)) volume :=
  volume_preserving_pi (fun x => measurePreserving_sgnMul (σ x))

omit [DecidableEq ι] in
lemma prod_w_flip {w : ℝ → ℝ} (hw : ∀ y, w (-y) = w y) (σ : ι → Bool) (φ : ι → ℝ) :
    ∏ x, w (flipSigns σ φ x) = ∏ x, w (φ x) := by
  refine prod_congr rfl fun x _ => ?_
  simp only [flipSigns, sgnMul]
  split_ifs <;> simp [hw]

/-- Sign averaging: if Σ_σ f(σφ) ≥ 0 pointwise, then ∫ f ∏ w ≥ 0 for an even nonnegative w. -/
theorem integral_nonneg_of_signSum_nonneg {w : ℝ → ℝ} (hw_even : ∀ y, w (-y) = w y)
    (hw_nonneg : ∀ y, 0 ≤ w y) (f : (ι → ℝ) → ℝ)
    (hf : ∀ φ, 0 ≤ ∑ σ : ι → Bool, f (flipSigns σ φ)) :
    0 ≤ ∫ φ : ι → ℝ, f φ * ∏ x, w (φ x) := by
  set F : (ι → ℝ) → ℝ := fun φ => f φ * ∏ x, w (φ x) with hFdef
  by_cases hint : Integrable F
  · have hcomp : ∀ σ : ι → Bool,
        (fun φ => f (flipSigns σ φ) * ∏ x, w (φ x)) = fun φ => F (flipEquiv σ φ) := by
      intro σ; funext φ
      show _ = f (flipSigns σ φ) * ∏ x, w (flipSigns σ φ x)
      rw [prod_w_flip hw_even]
    have hintσ : ∀ σ : ι → Bool, Integrable (fun φ => f (flipSigns σ φ) * ∏ x, w (φ x)) := by
      intro σ; rw [hcomp σ]
      exact (measurePreserving_flipEquiv σ).integrable_comp_of_integrable hint
    have hint_eq : ∀ σ : ι → Bool,
        ∫ φ, f (flipSigns σ φ) * ∏ x, w (φ x) = ∫ φ, F φ := by
      intro σ; rw [hcomp σ]
      exact (measurePreserving_flipEquiv σ).integral_comp' F
    have hsum : ∫ φ : ι → ℝ, (∑ σ : ι → Bool, f (flipSigns σ φ)) * ∏ x, w (φ x)
        = (Fintype.card (ι → Bool) : ℝ) * ∫ φ, F φ := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun σ _ => hintσ σ)]
      simp [hint_eq]
    have hnn : 0 ≤ ∫ φ : ι → ℝ, (∑ σ : ι → Bool, f (flipSigns σ φ)) * ∏ x, w (φ x) :=
      integral_nonneg fun φ => mul_nonneg (hf φ) (prod_nonneg fun x _ => hw_nonneg _)
    rw [hsum] at hnn
    have hcard : (0 : ℝ) < Fintype.card (ι → Bool) := by
      exact_mod_cast Fintype.card_pos
    exact nonneg_of_mul_nonneg_right (by linarith) hcard
  · rw [integral_undef hint]

/-- **Griffiths I, general form.** -/
theorem griffiths_first_general {w : ℝ → ℝ} (hw_even : ∀ y, w (-y) = w y)
    (hw_nonneg : ∀ y, 0 ≤ w y) {g Q : (ι → ℝ) → ℝ} (hg : IsPosPoly g) (hQ : IsPosPoly Q) :
    0 ≤ ∫ φ : ι → ℝ, g φ * Real.exp (Q φ) * ∏ x, w (φ x) :=
  integral_nonneg_of_signSum_nonneg hw_even hw_nonneg _ (signSum_mul_exp_nonneg hg hQ)

/-- **Griffiths' first inequality** for an even nonnegative single-site weight and a
ferromagnetic coupling J ≥ 0. -/
theorem griffiths_first {w : ℝ → ℝ} (hw_even : ∀ y, w (-y) = w y) (hw_nonneg : ∀ y, 0 ≤ w y)
    {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (a : ι → ℕ) :
    0 ≤ ∫ φ : ι → ℝ, (∏ x, φ x ^ a x) * Real.exp (∑ x, ∑ y, J x y * φ x * φ y)
      * ∏ x, w (φ x) :=
  griffiths_first_general hw_even hw_nonneg (IsPosPoly.ofMono a) (IsPosPoly.quadForm hJ)

/-- **Griffiths I with a nonnegative external field.** -/
theorem griffiths_first_field {w : ℝ → ℝ} (hw_even : ∀ y, w (-y) = w y)
    (hw_nonneg : ∀ y, 0 ≤ w y) {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) {h : ι → ℝ}
    (hh : ∀ x, 0 ≤ h x) (a : ι → ℕ) :
    0 ≤ ∫ φ : ι → ℝ, (∏ x, φ x ^ a x)
      * Real.exp (∑ x, ∑ y, J x y * φ x * φ y + ∑ x, h x * φ x) * ∏ x, w (φ x) :=
  griffiths_first_general hw_even hw_nonneg (IsPosPoly.ofMono a)
    ((IsPosPoly.quadForm hJ).add (IsPosPoly.linForm hh))

omit [DecidableEq ι] in
/-- Factorization of a monomial moment against the product weight. -/
theorem integral_mono_factorizes (w : ℝ → ℝ) (b : ι → ℕ) :
    ∫ φ : ι → ℝ, (∏ x, φ x ^ b x) * ∏ x, w (φ x) = ∏ x, ∫ y : ℝ, y ^ b x * w y := by
  simp_rw [← prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun x y => y ^ b x * w y)

end PP2Griffiths

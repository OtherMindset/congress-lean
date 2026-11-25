import LongTable.P_mwwgf25i_d0aeg1

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2FKG.lean (same content; only the imports are renamed).
Long Table, P(φ)₂ direction, node M7 (session 1): the FKG inequality for the quartic Dirichlet-box
measure, via a continuous four functions (Ahlswede–Daykin) theorem on ℝ^ι.

FORMALIZED.
* `FourFunctions μ` (a measure on a lattice): for all measurable f₁ f₂ f₃ f₄ : X → [0, ∞] with
  f₁ x · f₂ y ≤ f₃ (x ⊔ y) · f₄ (x ⊓ y), (∫⁻ f₁)(∫⁻ f₂) ≤ (∫⁻ f₃)(∫⁻ f₄). Stated with lower
  Lebesgue integrals, so no integrability hypotheses are needed and marginals may be infinite.
* `ennreal_two_point`, `pair_ineq`: the two-point inequality on a linear order.
* `fourFunctions_linear`: the four functions theorem for ANY measure on a linear order (in
  particular Lebesgue measure on ℝ); proof: symmetrise ∫∫ f₁(s) f₂(t) in (s, t), pointwise
  two-point inequality (no Fubini needed).
* `fourFunctions_unique` (one-point spaces), `fourFunctions_prod` (X × Y with the product order
  and product measure, s-finite; Tonelli, the fibre inequality from FourFunctions on Y, then
  FourFunctions on X for the marginals; this is the "marginal stays log-supermodular" step, done
  for the four-function form, which is closed under marginals), `FourFunctions.of_equiv`
  (transport along measure-preserving lattice isomorphisms).
* **`fourFunctions_fin`**, **`fourFunctions_pi`**: the four functions theorem for Lebesgue
  measure on ℝ^ι, ι any finite type (induction on |ι| via `piFinSuccAbove`).
* **`fkg_lintegral`**, **`fkg_integral_nonneg`**, **`fkg_integral`**: FKG for a log-supermodular
  density ρ ≥ 0 on ℝ^ι (ρ(x)ρ(y) ≤ ρ(x ⊔ y)ρ(x ⊓ y)): for F, G monotone (coordinatewise),
  measurable, bounded (resp. nonnegative with the integrability hypotheses),
    (∫ F G ρ)(∫ ρ) ≥ (∫ F ρ)(∫ G ρ).
* (a) The lattice condition: `sup_inf_mul` (rearrangement), `quadForm_supermodular` (J ≥ 0),
  `prod_sites_sup_inf` (product part is modular), **`ferroDensity_logSupermodular`**,
  **`dweight_logSupermodular`**: dweight φ · dweight ψ ≤ dweight (φ ⊔ ψ) · dweight (φ ⊓ ψ), for all
  n, k, m₀, λ, P.
* **`fkg_dexpect`**, **`fkg_gibbs`** (λ ≥ 0, m₀ ≠ 0): for F, G : DField n k → ℝ monotone,
  measurable and bounded, ⟨F G⟩ ≥ ⟨F⟩⟨G⟩ for the normalised quartic box measure (also as
  integrals against the probability measure `gibbs`).

NOT formalized.
* Newman's inequality / the passage from two-point decay to clustering of exp(iφ(f)) (hypothesis
  hN of PP2Conditional); this file only supplies the FKG input.
* FKG for unbounded monotone observables (e.g. φ(x) itself); only bounded F, G are treated in
  `fkg_integral` (nonnegative unbounded ones are covered by `fkg_integral_nonneg` given
  integrability).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset PP2Target PP2Griffiths
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2FKG

/-! ## The four functions property -/

/-- The (continuous) four functions property of a measure on a lattice. -/
def FourFunctions {X : Type*} [MeasurableSpace X] [Lattice X] (μ : Measure X) : Prop :=
  ∀ f₁ f₂ f₃ f₄ : X → ℝ≥0∞, Measurable f₁ → Measurable f₂ → Measurable f₃ → Measurable f₄ →
    (∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)) →
    (∫⁻ x, f₁ x ∂μ) * (∫⁻ x, f₂ x ∂μ) ≤ (∫⁻ x, f₃ x ∂μ) * (∫⁻ x, f₄ x ∂μ)

/-- The two-point inequality: a, b ≤ c and a b ≤ c d imply a + b ≤ c + d. -/
lemma ennreal_two_point {a b c d : ℝ≥0∞} (ha : a ≤ c) (hb : b ≤ c) (hab : a * b ≤ c * d) :
    a + b ≤ c + d := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  rcases eq_or_ne d ⊤ with rfl | hd
  · simp
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top hc ha
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top hc hb
  lift a to NNReal using ha'
  lift b to NNReal using hb'
  lift c to NNReal using hc
  lift d to NNReal using hd
  norm_cast at *
  rw [← NNReal.coe_le_coe] at *
  push_cast at *
  have h0a := a.coe_nonneg
  have h0b := b.coe_nonneg
  have h0d := d.coe_nonneg
  rcases c.coe_nonneg.eq_or_lt with h0 | hpos
  · rw [← h0] at ha hb ⊢; linarith
  · by_contra hlt
    push Not at hlt
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb), mul_lt_mul_of_pos_left hlt hpos]

section Linear

variable {X : Type*} [LinearOrder X]

lemma pair_ineq_of_le {f₁ f₂ f₃ f₄ : X → ℝ≥0∞}
    (h : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)) {s t : X} (hst : s ≤ t) :
    f₁ s * f₂ t + f₁ t * f₂ s ≤ f₃ s * f₄ t + f₃ t * f₄ s := by
  rw [add_comm (f₃ s * f₄ t)]
  have h1 : f₁ s * f₂ t ≤ f₃ t * f₄ s := by
    have := h s t; rwa [sup_eq_right.mpr hst, inf_eq_left.mpr hst] at this
  have h2 : f₁ t * f₂ s ≤ f₃ t * f₄ s := by
    have := h t s; rwa [sup_eq_left.mpr hst, inf_eq_right.mpr hst] at this
  refine ennreal_two_point h1 h2 ?_
  have hs := h s s
  have ht := h t t
  simp only [sup_idem, inf_idem] at hs ht
  calc f₁ s * f₂ t * (f₁ t * f₂ s) = (f₁ s * f₂ s) * (f₁ t * f₂ t) := by ring
    _ ≤ (f₃ s * f₄ s) * (f₃ t * f₄ t) := mul_le_mul' hs ht
    _ = f₃ t * f₄ s * (f₃ s * f₄ t) := by ring

/-- The symmetrised two-point inequality on a linear order. -/
lemma pair_ineq {f₁ f₂ f₃ f₄ : X → ℝ≥0∞}
    (h : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)) (s t : X) :
    f₁ s * f₂ t + f₁ t * f₂ s ≤ f₃ s * f₄ t + f₃ t * f₄ s := by
  rcases le_total s t with hst | hts
  · exact pair_ineq_of_le h hst
  · have := pair_ineq_of_le h hts
    rwa [add_comm (f₁ t * f₂ s), add_comm (f₃ t * f₄ s)] at this

variable [MeasurableSpace X]

lemma lintegral_symm_pair (μ : Measure X) {g₁ g₂ : X → ℝ≥0∞} (hg₁ : Measurable g₁)
    (hg₂ : Measurable g₂) :
    ∫⁻ s, ∫⁻ t, (g₁ s * g₂ t + g₁ t * g₂ s) ∂μ ∂μ
      = (∫⁻ x, g₁ x ∂μ) * (∫⁻ x, g₂ x ∂μ) + (∫⁻ x, g₁ x ∂μ) * (∫⁻ x, g₂ x ∂μ) := by
  have e1 : ∀ s, ∫⁻ t, (g₁ s * g₂ t + g₁ t * g₂ s) ∂μ
      = g₁ s * (∫⁻ t, g₂ t ∂μ) + (∫⁻ t, g₁ t ∂μ) * g₂ s := by
    intro s
    rw [lintegral_add_left (hg₂.const_mul _), lintegral_const_mul _ hg₂,
      lintegral_mul_const _ hg₁]
  simp_rw [e1]
  rw [lintegral_add_left (hg₁.mul_const _), lintegral_mul_const _ hg₁,
    lintegral_const_mul _ hg₂]

/-- **The four functions theorem on a linear order**, for any measure. -/
theorem fourFunctions_linear (μ : Measure X) : FourFunctions μ := by
  intro f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h
  have hle : ∫⁻ s, ∫⁻ t, (f₁ s * f₂ t + f₁ t * f₂ s) ∂μ ∂μ
      ≤ ∫⁻ s, ∫⁻ t, (f₃ s * f₄ t + f₃ t * f₄ s) ∂μ ∂μ :=
    lintegral_mono fun s => lintegral_mono fun t => pair_ineq h s t
  rw [lintegral_symm_pair μ h₁ h₂, lintegral_symm_pair μ h₃ h₄] at hle
  by_contra hlt
  push Not at hlt
  exact absurd hle (not_le.mpr (ENNReal.add_lt_add hlt hlt))

end Linear

/-! ## Stability: one-point spaces, products, transport -/

theorem fourFunctions_unique {X : Type*} [MeasurableSpace X] [Lattice X] [Unique X]
    (μ : Measure X) : FourFunctions μ := by
  intro f₁ f₂ f₃ f₄ _ _ _ _ h
  simp only [lintegral_unique]
  have hd := h default default
  simp only [sup_idem, inf_idem] at hd
  calc f₁ default * μ Set.univ * (f₂ default * μ Set.univ)
      = (f₁ default * f₂ default) * (μ Set.univ * μ Set.univ) := by ring
    _ ≤ (f₃ default * f₄ default) * (μ Set.univ * μ Set.univ) := mul_le_mul_left hd _
    _ = f₃ default * μ Set.univ * (f₄ default * μ Set.univ) := by ring

/-- **Products**: the four functions property passes to X × Y. -/
theorem fourFunctions_prod {X Y : Type*} [MeasurableSpace X] [Lattice X] [MeasurableSpace Y]
    [Lattice Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (hX : FourFunctions μ) (hY : FourFunctions ν) : FourFunctions (μ.prod ν) := by
  intro f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h
  rw [lintegral_prod _ h₁.aemeasurable, lintegral_prod _ h₂.aemeasurable,
    lintegral_prod _ h₃.aemeasurable, lintegral_prod _ h₄.aemeasurable]
  refine hX _ _ _ _ h₁.lintegral_prod_right' h₂.lintegral_prod_right'
    h₃.lintegral_prod_right' h₄.lintegral_prod_right' fun x x' => ?_
  refine hY (fun y => f₁ (x, y)) (fun y => f₂ (x', y)) (fun y => f₃ (x ⊔ x', y))
    (fun y => f₄ (x ⊓ x', y)) (h₁.comp measurable_prodMk_left) (h₂.comp measurable_prodMk_left)
    (h₃.comp measurable_prodMk_left) (h₄.comp measurable_prodMk_left) fun y y' => ?_
  exact h (x, y) (x', y')

/-- **Transport** along a measure-preserving lattice isomorphism. -/
theorem FourFunctions.of_equiv {X Y : Type*} [MeasurableSpace X] [Lattice X] [MeasurableSpace Y]
    [Lattice Y] {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (hsup : ∀ a b, e (a ⊔ b) = e a ⊔ e b) (hinf : ∀ a b, e (a ⊓ b) = e a ⊓ e b)
    (hY : FourFunctions ν) : FourFunctions μ := by
  intro f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h
  have hsup' : ∀ a b, e.symm (a ⊔ b) = e.symm a ⊔ e.symm b := fun a b =>
    e.injective (by rw [hsup]; simp)
  have hinf' : ∀ a b, e.symm (a ⊓ b) = e.symm a ⊓ e.symm b := fun a b =>
    e.injective (by rw [hinf]; simp)
  have hl : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ y, f (e.symm y) ∂ν :=
    fun f hf => ((he.symm e).lintegral_comp hf).symm
  rw [hl _ h₁, hl _ h₂, hl _ h₃, hl _ h₄]
  refine hY _ _ _ _ (h₁.comp e.symm.measurable) (h₂.comp e.symm.measurable)
    (h₃.comp e.symm.measurable) (h₄.comp e.symm.measurable) fun a b => ?_
  simp only [hsup', hinf']
  exact h _ _

/-- **The four functions theorem for Lebesgue measure on ℝⁿ.** -/
theorem fourFunctions_fin : ∀ n : ℕ, FourFunctions (volume : Measure (Fin n → ℝ))
  | 0 => fourFunctions_unique _
  | n + 1 => by
      refine FourFunctions.of_equiv (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
        (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0) (fun _ _ => rfl) (fun _ _ => rfl) ?_
      exact fourFunctions_prod (fourFunctions_linear _) (fourFunctions_fin n)

/-- **The four functions theorem for Lebesgue measure on ℝ^ι**, ι any finite type. -/
theorem fourFunctions_pi (ι : Type*) [Fintype ι] : FourFunctions (volume : Measure (ι → ℝ)) :=
  FourFunctions.of_equiv (MeasurableEquiv.arrowCongr' (Fintype.equivFin ι) (MeasurableEquiv.refl ℝ))
    (volume_preserving_arrowCongr' _ _ (MeasurePreserving.id _)) (fun _ _ => rfl)
    (fun _ _ => rfl) (fourFunctions_fin _)

/-! ## FKG for log-supermodular densities on ℝ^ι -/

section FKG

variable {ι : Type*} [Fintype ι]

/-- **FKG, lower-integral form**: ρ ≥ 0 log-supermodular, F, G ≥ 0 monotone. -/
theorem fkg_lintegral {ρ F G : (ι → ℝ) → ℝ} (hρm : Measurable ρ) (hFm : Measurable F)
    (hGm : Measurable G) (hρ0 : ∀ x, 0 ≤ ρ x) (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (hF : Monotone F) (hG : Monotone G)
    (hlat : ∀ x y, ρ x * ρ y ≤ ρ (x ⊔ y) * ρ (x ⊓ y)) :
    (∫⁻ x, ENNReal.ofReal (F x * ρ x)) * (∫⁻ x, ENNReal.ofReal (G x * ρ x))
      ≤ (∫⁻ x, ENNReal.ofReal (F x * G x * ρ x)) * (∫⁻ x, ENNReal.ofReal (ρ x)) := by
  refine fourFunctions_pi ι _ _ _ _ (hFm.mul hρm).ennreal_ofReal (hGm.mul hρm).ennreal_ofReal
    ((hFm.mul hGm).mul hρm).ennreal_ofReal hρm.ennreal_ofReal fun x y => ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg (hF0 x) (hρ0 x)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hF0 _) (hG0 _)) (hρ0 _))]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : F x * G y ≤ F (x ⊔ y) * G (x ⊔ y) :=
    mul_le_mul (hF le_sup_left) (hG le_sup_right) (hG0 _) (hF0 _)
  calc F x * ρ x * (G y * ρ y) = (F x * G y) * (ρ x * ρ y) := by ring
    _ ≤ (F (x ⊔ y) * G (x ⊔ y)) * (ρ (x ⊔ y) * ρ (x ⊓ y)) :=
        mul_le_mul h1 (hlat x y) (mul_nonneg (hρ0 _) (hρ0 _))
          (mul_nonneg (hF0 _) (hG0 _))
    _ = F (x ⊔ y) * G (x ⊔ y) * ρ (x ⊔ y) * ρ (x ⊓ y) := by ring

/-- **FKG, nonnegative observables, Bochner form** (given the four integrabilities). -/
theorem fkg_integral_nonneg {ρ F G : (ι → ℝ) → ℝ} (hρm : Measurable ρ) (hFm : Measurable F)
    (hGm : Measurable G) (hρ0 : ∀ x, 0 ≤ ρ x) (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (hF : Monotone F) (hG : Monotone G)
    (hlat : ∀ x y, ρ x * ρ y ≤ ρ (x ⊔ y) * ρ (x ⊓ y))
    (iF : Integrable fun x => F x * ρ x) (iG : Integrable fun x => G x * ρ x)
    (iFG : Integrable fun x => F x * G x * ρ x) (iρ : Integrable ρ) :
    (∫ x, F x * ρ x) * (∫ x, G x * ρ x) ≤ (∫ x, F x * G x * ρ x) * ∫ x, ρ x := by
  have h := fkg_lintegral hρm hFm hGm hρ0 hF0 hG0 hF hG hlat
  have n1 : ∀ x, 0 ≤ F x * ρ x := fun x => mul_nonneg (hF0 x) (hρ0 x)
  have n2 : ∀ x, 0 ≤ G x * ρ x := fun x => mul_nonneg (hG0 x) (hρ0 x)
  have n3 : ∀ x, 0 ≤ F x * G x * ρ x := fun x => mul_nonneg (mul_nonneg (hF0 x) (hG0 x)) (hρ0 x)
  rw [← ofReal_integral_eq_lintegral_ofReal iF (Filter.Eventually.of_forall n1),
    ← ofReal_integral_eq_lintegral_ofReal iG (Filter.Eventually.of_forall n2),
    ← ofReal_integral_eq_lintegral_ofReal iFG (Filter.Eventually.of_forall n3),
    ← ofReal_integral_eq_lintegral_ofReal iρ (Filter.Eventually.of_forall hρ0),
    ← ENNReal.ofReal_mul (integral_nonneg n1), ← ENNReal.ofReal_mul (integral_nonneg n3)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (integral_nonneg n3) (integral_nonneg hρ0))).1 h

/-- **FKG for bounded monotone observables** and an integrable log-supermodular density:
(∫ F G ρ)(∫ ρ) ≥ (∫ F ρ)(∫ G ρ). -/
theorem fkg_integral {ρ F G : (ι → ℝ) → ℝ} (hρm : Measurable ρ) (hFm : Measurable F)
    (hGm : Measurable G) (hρ0 : ∀ x, 0 ≤ ρ x) {CF CG : ℝ} (hFb : ∀ x, |F x| ≤ CF)
    (hGb : ∀ x, |G x| ≤ CG) (hF : Monotone F) (hG : Monotone G)
    (hlat : ∀ x y, ρ x * ρ y ≤ ρ (x ⊔ y) * ρ (x ⊓ y)) (iρ : Integrable ρ) :
    (∫ x, F x * ρ x) * (∫ x, G x * ρ x) ≤ (∫ x, F x * G x * ρ x) * ∫ x, ρ x := by
  have hbF : ∀ x, ‖F x‖ ≤ CF := fun x => by rw [Real.norm_eq_abs]; exact hFb x
  have hbG : ∀ x, ‖G x‖ ≤ CG := fun x => by rw [Real.norm_eq_abs]; exact hGb x
  have iF : Integrable fun x => F x * ρ x :=
    iρ.bdd_mul hFm.aestronglyMeasurable (Filter.Eventually.of_forall hbF)
  have iG : Integrable fun x => G x * ρ x :=
    iρ.bdd_mul hGm.aestronglyMeasurable (Filter.Eventually.of_forall hbG)
  have iFG : Integrable fun x => F x * G x * ρ x := by
    have := iG.bdd_mul hFm.aestronglyMeasurable (Filter.Eventually.of_forall hbF)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  set F' : (ι → ℝ) → ℝ := fun x => F x + CF
  set G' : (ι → ℝ) → ℝ := fun x => G x + CG
  have hF0 : ∀ x, 0 ≤ F' x := fun x => by
    have := neg_abs_le (F x); have := hFb x; simp only [F']; linarith
  have hG0 : ∀ x, 0 ≤ G' x := fun x => by
    have := neg_abs_le (G x); have := hGb x; simp only [G']; linarith
  have iCρ : ∀ c : ℝ, Integrable fun x => c * ρ x := fun c => iρ.const_mul c
  have eF : (fun x => F' x * ρ x) = fun x => F x * ρ x + CF * ρ x := by
    funext x; simp only [F']; ring
  have eG : (fun x => G' x * ρ x) = fun x => G x * ρ x + CG * ρ x := by
    funext x; simp only [G']; ring
  have eFG : (fun x => F' x * G' x * ρ x) = fun x =>
      F x * G x * ρ x + (CG * (F x * ρ x) + (CF * (G x * ρ x) + CF * CG * ρ x)) := by
    funext x; simp only [F', G']; ring
  have h := fkg_integral_nonneg hρm (hFm.add_const CF) (hGm.add_const CG) hρ0 hF0 hG0
    (fun a b hab => show F a + CF ≤ F b + CF by linarith [hF hab])
    (fun a b hab => show G a + CG ≤ G b + CG by linarith [hG hab]) hlat
    (by rw [eF]; exact iF.add (iCρ CF)) (by rw [eG]; exact iG.add (iCρ CG))
    (by rw [eFG]; exact iFG.add ((iF.const_mul CG).add ((iG.const_mul CF).add (iCρ _)))) iρ
  have j1 : Integrable fun x => CF * CG * ρ x := iCρ _
  have j2 : Integrable fun x => CF * (G x * ρ x) := iG.const_mul CF
  have j3 : Integrable fun x => CG * (F x * ρ x) := iF.const_mul CG
  have j4 : Integrable fun x => CF * (G x * ρ x) + CF * CG * ρ x := j2.add j1
  have j5 : Integrable fun x => CG * (F x * ρ x) + (CF * (G x * ρ x) + CF * CG * ρ x) := j3.add j4
  rw [eF, eG, eFG, integral_add iF (iCρ CF), integral_add iG (iCρ CG),
    integral_add iFG j5, integral_add j3 j4, integral_add j2 j1, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at h
  linear_combination h

end FKG

/-! ## (a) The lattice condition for the ferromagnetic density -/

section Lattice

variable {ι : Type*} [Fintype ι]

/-- Rearrangement: a c + b d ≤ (a ⊔ b)(c ⊔ d) + (a ⊓ b)(c ⊓ d). -/
lemma sup_inf_mul (a b c d : ℝ) : a * c + b * d ≤ (a ⊔ b) * (c ⊔ d) + (a ⊓ b) * (c ⊓ d) := by
  rcases le_total a b with h | h <;> rcases le_total c d with h' | h'
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, sup_eq_right.mpr h', inf_eq_left.mpr h']
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h')]
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, sup_eq_left.mpr h', inf_eq_right.mpr h']
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h')]
  · rw [sup_eq_left.mpr h, inf_eq_right.mpr h, sup_eq_right.mpr h', inf_eq_left.mpr h']
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h')]
  · rw [sup_eq_left.mpr h, inf_eq_right.mpr h, sup_eq_left.mpr h', inf_eq_right.mpr h']

/-- Supermodularity of Σ J φφ for J ≥ 0. -/
theorem quadForm_supermodular {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (φ ψ : ι → ℝ) :
    (∑ x, ∑ y, J x y * φ x * φ y) + (∑ x, ∑ y, J x y * ψ x * ψ y)
      ≤ (∑ x, ∑ y, J x y * (φ ⊔ ψ) x * (φ ⊔ ψ) y)
        + (∑ x, ∑ y, J x y * (φ ⊓ ψ) x * (φ ⊓ ψ) y) := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun y _ => ?_
  simp only [Pi.sup_apply, Pi.inf_apply]
  have := mul_le_mul_of_nonneg_left (sup_inf_mul (φ x) (ψ x) (φ y) (ψ y)) (hJ x y)
  linear_combination this

/-- The product part is modular. -/
theorem prod_sites_sup_inf (w : ι → ℝ → ℝ) (φ ψ : ι → ℝ) :
    (∏ x, w x (φ x)) * (∏ x, w x (ψ x)) = (∏ x, w x ((φ ⊔ ψ) x)) * ∏ x, w x ((φ ⊓ ψ) x) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun x _ => ?_
  simp only [Pi.sup_apply, Pi.inf_apply]
  rcases le_total (φ x) (ψ x) with h | h
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, mul_comm]
  · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]

/-- **The FKG lattice condition for the ferromagnetic density** (J ≥ 0, w ≥ 0). -/
theorem ferroDensity_logSupermodular {w : ι → ℝ → ℝ} (hw : ∀ x y, 0 ≤ w x y)
    {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (φ ψ : ι → ℝ) :
    ferroDensity w J φ * ferroDensity w J ψ
      ≤ ferroDensity w J (φ ⊔ ψ) * ferroDensity w J (φ ⊓ ψ) := by
  unfold ferroDensity
  calc Real.exp (∑ x, ∑ y, J x y * φ x * φ y) * (∏ x, w x (φ x))
        * (Real.exp (∑ x, ∑ y, J x y * ψ x * ψ y) * ∏ x, w x (ψ x))
      = Real.exp ((∑ x, ∑ y, J x y * φ x * φ y) + (∑ x, ∑ y, J x y * ψ x * ψ y))
          * ((∏ x, w x (φ x)) * (∏ x, w x (ψ x))) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp ((∑ x, ∑ y, J x y * (φ ⊔ ψ) x * (φ ⊔ ψ) y)
          + (∑ x, ∑ y, J x y * (φ ⊓ ψ) x * (φ ⊓ ψ) y))
          * ((∏ x, w x ((φ ⊔ ψ) x)) * ∏ x, w x ((φ ⊓ ψ) x)) := by
        rw [prod_sites_sup_inf]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (quadForm_supermodular hJ φ ψ))
          (mul_nonneg (prod_nonneg fun x _ => hw x _) (prod_nonneg fun x _ => hw x _))
    _ = _ := by rw [Real.exp_add]; ring

end Lattice

/-! ## FKG for the quartic Dirichlet-box measure -/

section Model

variable {n k : ℕ}

/-- **(a) The FKG lattice condition for the Dirichlet-box weight** (all n, k, m₀, λ, P). -/
theorem dweight_logSupermodular (m₀ lam : ℝ) (P : Polynomial ℝ) (φ ψ : DField n k) :
    dweight n k m₀ lam P φ * dweight n k m₀ lam P ψ
      ≤ dweight n k m₀ lam P (φ ⊔ ψ) * dweight n k m₀ lam P (φ ⊓ ψ) := by
  rw [← ferroDensity_dweight]
  exact ferroDensity_logSupermodular (fun _ _ => (Real.exp_pos _).le) Jnn_nonneg φ ψ

/-- **FKG for the normalised quartic box measure**: λ ≥ 0, m₀ ≠ 0, F, G monotone, measurable,
bounded: ⟨F G⟩ ≥ ⟨F⟩⟨G⟩. -/
theorem fkg_dexpect {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F G : DField n k → ℝ} (hFm : Measurable F) (hGm : Measurable G) {CF CG : ℝ}
    (hFb : ∀ φ, |F φ| ≤ CF) (hGb : ∀ φ, |G φ| ≤ CG) (hF : Monotone F) (hG : Monotone G) :
    dexpect n k m₀ lam (fun φ => F φ * G φ) ≥
      dexpect n k m₀ lam F * dexpect n k m₀ lam G := by
  have h := fkg_integral (continuous_dweight m₀ lam (Polynomial.X ^ 4)).measurable hFm hGm
    (fun φ => (Real.exp_pos _).le) hFb hGb hF hG (dweight_logSupermodular m₀ lam _)
    (integrable_dweight hm hlam)
  have hZ := integral_dweight_pos (n := n) (k := k) hm hlam
  simp only [dexpect]
  rw [ge_iff_le, div_mul_div_comm, div_le_div_iff₀ (mul_pos hZ hZ) hZ]
  have h' := mul_le_mul_of_nonneg_right h hZ.le
  nlinarith

/-- **FKG for the quartic box Gibbs measure**: ∫ F G d(gibbs) ≥ ∫ F d(gibbs) · ∫ G d(gibbs). -/
theorem fkg_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F G : DField n k → ℝ} (hFm : Measurable F) (hGm : Measurable G) {CF CG : ℝ}
    (hFb : ∀ φ, |F φ| ≤ CF) (hGb : ∀ φ, |G φ| ≤ CG) (hF : Monotone F) (hG : Monotone G) :
    ∫ φ, F φ * G φ ∂(gibbs n k m₀ lam) ≥
      (∫ φ, F φ ∂(gibbs n k m₀ lam)) * ∫ φ, G φ ∂(gibbs n k m₀ lam) := by
  simp only [integral_gibbs]
  exact fkg_dexpect hm hlam hFm hGm hFb hGb hF hG

end Model

end PP2FKG

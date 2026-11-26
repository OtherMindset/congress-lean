import Mathlib

/-!
Long Table, target T2b, one-site (0-d) theorem, LAYER 1 (abstract one-variable lemmas).
Mathematics: t2b/zerod/zerod_proof.md §2 (Steps 2 and 4 are one-variable Chebyshev/MLR
inequalities; Step 1 uses the linear change of variables (x, y) ↦ (x + y, x − y)).

FORMALIZED (namespace `PP2OneSite`; no sorry; axioms propext / Classical.choice / Quot.sound):
* `cheb_prod`: for integrable a b c d : ℝ → ℝ with
    a x * b y + a y * b x ≤ c x * d y + c y * d x   for all x y,
  (∫a)(∫b) ≤ (∫c)(∫d). (Integrate the pointwise inequality over ℝ² = volume.prod volume and
  use Fubini for products.) This is the symmetrised Chebyshev/MLR inequality in the form
  used twice later: no division, no boundedness of the monotone function.
* `cheb_even_cond`: if a b c d are even, the pointwise hypothesis of `cheb_prod` only has to be
  checked for x, y ≥ 0.
* `sinh_ratio`: 0 ≤ a ≤ b, 0 ≤ y ≤ x ⟹ sinh(a x) sinh(b y) ≤ sinh(b x) sinh(a y)
  (i.e. y ↦ sinh(b y)/sinh(a y) nondecreasing; proof: derivative numerator
  N(y) = b cosh(by) sinh(ay) − a sinh(by) cosh(ay) has N(0) = 0, N' = (b²−a²) sinh(by) sinh(ay)).
  This replaces the paper's "x coth x increasing" (equivalent, avoids coth).
* `rot_integral`: ∃ c > 0, ∀ Φ : ℝ × ℝ → ℝ, ∫ Φ(z₁ + z₂, z₁ − z₂) dz = c ∫ Φ (Lebesgue on ℝ²;
  from `Measure.map_linearMap_addHaar_eq_smul_addHaar`; c = |det|⁻¹ = 1/2, its value is not
  needed since it cancels in the ratio R).
NOT formalized here: anything model-specific (see PP2OneSiteB/C/D).
Toolchain: Lean 4.35.0, Mathlib 56a00585.
-/

open MeasureTheory Real Set

namespace PP2OneSite

theorem cheb_prod {a b c d : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hc : Integrable c) (hd : Integrable d)
    (h : ∀ x y, a x * b y + a y * b x ≤ c x * d y + c y * d x) :
    (∫ x, a x) * (∫ x, b x) ≤ (∫ x, c x) * (∫ x, d x) := by
  have sym : ∀ {u v : ℝ → ℝ}, Integrable u → Integrable v →
      Integrable (fun z : ℝ × ℝ => u z.1 * v z.2 + u z.2 * v z.1) (volume.prod volume) ∧
      ∫ z : ℝ × ℝ, (u z.1 * v z.2 + u z.2 * v z.1) ∂(volume.prod volume)
        = 2 * ((∫ x, u x) * (∫ x, v x)) := by
    intro u v hu hv
    have h1 : Integrable (fun z : ℝ × ℝ => u z.1 * v z.2) (volume.prod volume) := hu.mul_prod hv
    have h2 : Integrable (fun z : ℝ × ℝ => u z.2 * v z.1) (volume.prod volume) := by
      have := hv.mul_prod hu (μ := volume) (ν := volume)
      simpa [mul_comm] using this
    refine ⟨h1.add h2, ?_⟩
    rw [integral_add h1 h2, integral_prod_mul]
    have : ∫ z : ℝ × ℝ, u z.2 * v z.1 ∂(volume.prod volume) = (∫ x, v x) * (∫ x, u x) := by
      rw [← integral_prod_mul]; congr 1; funext z; ring
    rw [this]; ring
  obtain ⟨i1, e1⟩ := sym ha hb
  obtain ⟨i2, e2⟩ := sym hc hd
  have := integral_mono i1 i2 (fun z => h z.1 z.2)
  rw [e1, e2] at this
  linarith

lemma sinhN_hasDerivAt (a b y : ℝ) :
    HasDerivAt (fun y => b * cosh (b * y) * sinh (a * y) - a * sinh (b * y) * cosh (a * y))
      ((b ^ 2 - a ^ 2) * sinh (b * y) * sinh (a * y)) y := by
  have hb : HasDerivAt (fun y => b * y) (b * 1) y := (hasDerivAt_id' y).const_mul b
  have ha : HasDerivAt (fun y => a * y) (a * 1) y := (hasDerivAt_id' y).const_mul a
  have := ((hb.cosh.const_mul b).mul ha.sinh).sub ((hb.sinh.const_mul a).mul ha.cosh)
  convert this using 1
  ring

lemma sinhN_nonneg {a b y : ℝ} (hab : 0 ≤ a) (hab' : a ≤ b) (hy : 0 ≤ y) :
    0 ≤ b * cosh (b * y) * sinh (a * y) - a * sinh (b * y) * cosh (a * y) := by
  set N := fun y => b * cosh (b * y) * sinh (a * y) - a * sinh (b * y) * cosh (a * y) with hN
  have hmono : MonotoneOn N (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (sinhN_hasDerivAt a b y).continuousAt.continuousWithinAt
    · exact fun y _ => (sinhN_hasDerivAt a b y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(sinhN_hasDerivAt a b y).deriv]
      have h1 : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith
      have h2 : 0 ≤ sinh (b * y) := Real.sinh_nonneg_iff.mpr (by nlinarith [hy.out.le])
      have h3 : 0 ≤ sinh (a * y) := Real.sinh_nonneg_iff.mpr (by nlinarith [hy.out.le])
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) hy hy
  simpa [N] using this

theorem sinh_ratio {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 ≤ y) (hyx : y ≤ x) :
    sinh (a * x) * sinh (b * y) ≤ sinh (b * x) * sinh (a * y) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases hy.eq_or_lt with rfl | hy'
  · simp
  have hb' : 0 < b := lt_of_lt_of_le ha' hab
  set ψ := fun y => sinh (b * y) / sinh (a * y)
  have hpos : ∀ y, 0 < y → 0 < sinh (a * y) := fun y hy => Real.sinh_pos_iff.mpr (by positivity)
  have hderiv : ∀ y, 0 < y → HasDerivAt ψ
      ((b * cosh (b * y) * sinh (a * y) - sinh (b * y) * (a * cosh (a * y))) / sinh (a * y) ^ 2) y := by
    intro y hy
    have hb : HasDerivAt (fun y => b * y) (b * 1) y := (hasDerivAt_id' y).const_mul b
    have ha : HasDerivAt (fun y => a * y) (a * 1) y := (hasDerivAt_id' y).const_mul a
    have := hb.sinh.div ha.sinh (hpos y hy).ne'
    convert this using 1
    ring
  have hmono : MonotoneOn ψ (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ioi] at hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      rw [(hderiv y hy).deriv]
      have := sinhN_nonneg ha'.le hab (le_of_lt hy)
      apply div_nonneg _ (sq_nonneg _)
      linarith
  have h := hmono hy' (lt_of_lt_of_le hy' hyx) hyx
  simp only [ψ] at h
  have p1 := hpos y hy'
  have p2 := hpos x (lt_of_lt_of_le hy' hyx)
  rw [div_le_div_iff₀ p1 p2] at h
  linarith

lemma even_abs_eq {a : ℝ → ℝ} (h : ∀ x, a (-x) = a x) (x : ℝ) : a |x| = a x := by
  rcases abs_choice x with hx | hx <;> rw [hx]
  exact h x

theorem cheb_even_cond {a b c d : ℝ → ℝ} (ha : ∀ x, a (-x) = a x) (hb : ∀ x, b (-x) = b x)
    (hc : ∀ x, c (-x) = c x) (hd : ∀ x, d (-x) = d x)
    (h : ∀ x y, 0 ≤ x → 0 ≤ y → a x * b y + a y * b x ≤ c x * d y + c y * d x) :
    ∀ x y, a x * b y + a y * b x ≤ c x * d y + c y * d x := by
  intro x y
  have := h |x| |y| (abs_nonneg x) (abs_nonneg y)
  simpa only [even_abs_eq ha, even_abs_eq hb, even_abs_eq hc, even_abs_eq hd] using this


noncomputable def rotL : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  LinearMap.prod (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)

noncomputable def rotLinv : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (1/2 : ℝ) • LinearMap.prod (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)

noncomputable def rotE : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.ofLinearMap rotL rotLinv
    (by ext <;> simp [rotL, rotLinv] <;> ring)
    (by ext <;> simp [rotL, rotLinv] <;> ring)

lemma rotE_apply (z : ℝ × ℝ) : rotE z = (z.1 + z.2, z.1 - z.2) := by
  simp [rotE, rotL]

theorem rot_integral : ∃ c : ℝ, 0 < c ∧ ∀ Φ : ℝ × ℝ → ℝ,
    ∫ z : ℝ × ℝ, Φ (z.1 + z.2, z.1 - z.2) = c * ∫ z, Φ z := by
  have hdet : LinearMap.det (rotE : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' rotE).ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ℝ × ℝ)) hdet
  let C := rotE.toContinuousLinearEquiv
  have hemb : MeasurableEmbedding (C : ℝ × ℝ → ℝ × ℝ) := C.toHomeomorph.measurableEmbedding
  refine ⟨|(LinearMap.det (rotE : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))⁻¹|, by positivity, fun Φ => ?_⟩
  have h1 := hemb.integral_map (μ := volume) Φ
  have hC : (C : ℝ × ℝ → ℝ × ℝ) = ((rotE : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) : ℝ × ℝ → ℝ × ℝ) := rfl
  rw [hC, hmap, integral_smul_measure] at h1
  simp only [LinearEquiv.coe_coe, rotE_apply] at h1
  rw [← h1, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

end PP2OneSite

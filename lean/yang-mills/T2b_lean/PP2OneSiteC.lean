import LongTable.PP2OneSiteB

/-!
Long Table, target T2b, one-site (0-d) theorem, LAYERS 3–4 (duplication identities and assembly).
Mathematics: t2b/zerod/zerod_proof.md §2 Steps 1, 3, 4.

SETTING. dμ_H ∝ e^{−V(φ)+Hφ} dφ on ℝ. `Mom V k H = ∫ φ^k e^{−V(φ)+Hφ} dφ` (unnormalised),
`R V H = (m₃ − m₁ m₂) / m₁` with m_k = Mom V k H / Mom V 0 H, i.e. R = ⟨φ;φ²⟩_H / ⟨φ⟩_H.

FORMALIZED (namespace `PP2OneSite`; no sorry; axioms propext / Classical.choice / Quot.sound):
* `integrable1`: φ^k e^{Hφ} e^{−V} integrable (V continuous, superlinear).
* Step 1 (duplication), `prodA`/`prodB`: ∫∫ (x−y)²(x+y) w(x)w(y) = 2(M₃M₀ − M₁M₂) and
  ∫∫ (x+y) w(x)w(y) = 2 M₁M₀ (w = e^{Hφ−V}); with `rot_integral` (p = x+y, d = x−y) and
  Fubini (`fubini_S`) these become c·∫ p e^{Hp} S_j(p) dp, j = 2, 0, with c > 0.
* Step 3 (symmetrisation), `sinh_form`: V even ⟹ ∫ p e^{Hp} S_j(p) dp = ∫ p sinh(Hp) S_j(p) dp.
  Hence `R_eq_ratio`: for H > 0,
    R V H = (∫ p sinh(Hp) S₂(p) dp) / (∫ p sinh(Hp) S₀(p) dp)      (the paper's R = 2∫g dπ_h),
  with `B_pos`: the denominator is > 0.
* Step 4, `AB_cross`: 0 ≤ H₁ ≤ H₂ ⟹ A(H₂)B(H₁) ≤ A(H₁)B(H₂) (A, B the numerator/denominator),
  from `cheb_prod` in p with the pointwise sign argument
    x y (S₂(x)S₀(y) − S₂(y)S₀(x)) (sinh(H₁x)sinh(H₂y) − sinh(H₂x)sinh(H₁y)) ≥ 0  (x, y ≥ 0),
  both factors having the sign of y − x by `S_cross` and `sinh_ratio`.
* MAIN (abstract form) `R_antitoneOn_of_supermodular`: V continuous, even, superlinear and
  `Supermodular V` ⟹ AntitoneOn (R V) (Ioi 0).
NOT formalized here: EMN/GHS class ⟹ Supermodular (see PP2OneSiteD).
Toolchain: Lean 4.35.0, Mathlib 56a00585.
-/

open MeasureTheory Real Set

namespace PP2OneSite

/-- unnormalised moments of dμ_H ∝ e^{−V(φ)+Hφ}dφ. -/
noncomputable def Mom (V : ℝ → ℝ) (k : ℕ) (H : ℝ) : ℝ := ∫ x, x ^ k * exp (-V x + H * x)

/-- R(H) = ⟨φ;φ²⟩_H / ⟨φ⟩_H. -/
noncomputable def R (V : ℝ → ℝ) (H : ℝ) : ℝ :=
  (Mom V 3 H / Mom V 0 H - (Mom V 1 H / Mom V 0 H) * (Mom V 2 H / Mom V 0 H))
    / (Mom V 1 H / Mom V 0 H)

noncomputable def mfun (V : ℝ → ℝ) (H : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x ^ k * exp (H * x) * exp (-V x)

lemma Mom_eq (V : ℝ → ℝ) (k : ℕ) (H : ℝ) : Mom V k H = ∫ x, mfun V H k x := by
  unfold Mom mfun; congr 1; funext x; rw [exp_add]; ring

variable {V : ℝ → ℝ}

lemma integrable1 (hV : Continuous V) (hsl : Superlinear V) (k : ℕ) (H : ℝ) :
    Integrable (mfun V H k) := by
  obtain ⟨C, hC⟩ := hsl (k + |H| + 2)
  have hc : Continuous (mfun V H k) := by unfold mfun; fun_prop
  refine (integrable_inv_one_add_sq.const_mul (exp C)).mono' hc.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  unfold mfun
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos (H * x)),
    abs_of_pos (exp_pos (-V x))]
  have h1 := abs_pow_le_exp k x
  have h2 : exp (H * x) ≤ exp (|H| * |x|) :=
    exp_le_exp.mpr (by rw [← abs_mul]; exact le_abs_self _)
  have hx := hC x
  calc |x ^ k| * exp (H * x) * exp (-V x) ≤ exp (k * |x|) * exp (|H| * |x|) * exp (-V x) := by
        gcongr
    _ = exp (k * |x| + |H| * |x| + -V x) := by rw [exp_add, exp_add]
    _ ≤ exp (C + -(2 * |x|)) := exp_le_exp.mpr (by nlinarith)
    _ = exp C * exp (-(2 * |x|)) := exp_add _ _
    _ ≤ exp C * (1 + x ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (exp_neg_two_abs_le x) (exp_pos _).le

lemma F_shift (V : ℝ → ℝ) (x y : ℝ) : F V (x + y) (x - y) = exp (-V x) * exp (-V y) := by
  unfold F W
  rw [show (x + y + (x - y)) / 2 = x by ring, show (x + y - (x - y)) / 2 = y by ring, neg_add,
    exp_add]

lemma prodA (hV : Continuous V) (hsl : Superlinear V) (H : ℝ) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 * (z.1 + z.2) * (exp (H * z.1) * exp (-V z.1))
        * (exp (H * z.2) * exp (-V z.2))
      = 2 * ((∫ x, mfun V H 3 x) * (∫ x, mfun V H 0 x)
          - (∫ x, mfun V H 1 x) * (∫ x, mfun V H 2 x)) := by
  have hi : ∀ k, Integrable (mfun V H k) := fun k => integrable1 hV hsl k H
  have e : (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2 * (z.1 + z.2) * (exp (H * z.1) * exp (-V z.1))
        * (exp (H * z.2) * exp (-V z.2)))
      = fun z => mfun V H 3 z.1 * mfun V H 0 z.2 - mfun V H 2 z.1 * mfun V H 1 z.2
          - mfun V H 1 z.1 * mfun V H 2 z.2 + mfun V H 0 z.1 * mfun V H 3 z.2 := by
    funext z; simp only [mfun]; ring
  rw [e, Measure.volume_eq_prod, integral_add, integral_sub, integral_sub]
  · simp only [integral_prod_mul]; ring
  all_goals first
    | exact (hi _).mul_prod (hi _)
    | exact ((hi _).mul_prod (hi _)).sub ((hi _).mul_prod (hi _))
    | exact (((hi _).mul_prod (hi _)).sub ((hi _).mul_prod (hi _))).sub ((hi _).mul_prod (hi _))

lemma prodB (hV : Continuous V) (hsl : Superlinear V) (H : ℝ) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 0 * (z.1 + z.2) * (exp (H * z.1) * exp (-V z.1))
        * (exp (H * z.2) * exp (-V z.2))
      = 2 * ((∫ x, mfun V H 1 x) * (∫ x, mfun V H 0 x)) := by
  have hi : ∀ k, Integrable (mfun V H k) := fun k => integrable1 hV hsl k H
  have e : (fun z : ℝ × ℝ => (z.1 - z.2) ^ 0 * (z.1 + z.2) * (exp (H * z.1) * exp (-V z.1))
        * (exp (H * z.2) * exp (-V z.2)))
      = fun z => mfun V H 1 z.1 * mfun V H 0 z.2 + mfun V H 0 z.1 * mfun V H 1 z.2 := by
    funext z; simp only [mfun]; ring
  rw [e, Measure.volume_eq_prod, integral_add ((hi 1).mul_prod (hi 0)) ((hi 0).mul_prod (hi 1))]
  simp only [integral_prod_mul]; ring

lemma G_bound (j : ℕ) (H : ℝ) (z : ℝ × ℝ) :
    |z.2 ^ j * z.1 * exp (H * z.1)| ≤ 1 * exp ((j + 1 + |H|) * (|z.1| + |z.2|)) := by
  rw [one_mul, abs_mul, abs_mul, abs_of_pos (exp_pos _)]
  have h1 := abs_pow_le_exp j z.2
  have h2 : |z.1| ≤ exp |z.1| := by linarith [add_one_le_exp |z.1|]
  have h3 : exp (H * z.1) ≤ exp (|H| * |z.1|) :=
    exp_le_exp.mpr (by rw [← abs_mul]; exact le_abs_self _)
  have a1 := abs_nonneg z.1
  have a2 := abs_nonneg z.2
  have a3 := abs_nonneg H
  have a4 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc |z.2 ^ j| * |z.1| * exp (H * z.1) ≤ exp (j * |z.2|) * exp |z.1| * exp (|H| * |z.1|) := by
        gcongr
    _ = exp (j * |z.2| + |z.1| + |H| * |z.1|) := by rw [exp_add, exp_add]
    _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_nonneg a4 a1, mul_nonneg a3 a2])

lemma Phi_integrable (hV : Continuous V) (hsl : Superlinear V) (j : ℕ) (H : ℝ) :
    Integrable (fun z : ℝ × ℝ => z.2 ^ j * z.1 * exp (H * z.1) * F V z.1 z.2)
      (volume.prod volume) :=
  integrable2 hV hsl (G := fun z => z.2 ^ j * z.1 * exp (H * z.1)) (by fun_prop)
    (by positivity) zero_le_one (G_bound j H)

lemma fubini_S (hV : Continuous V) (hsl : Superlinear V) (j : ℕ) (H : ℝ) :
    ∫ z : ℝ × ℝ, z.2 ^ j * z.1 * exp (H * z.1) * F V z.1 z.2
      = ∫ p, p * exp (H * p) * S V j p := by
  rw [Measure.volume_eq_prod, integral_prod _ (Phi_integrable hV hsl j H)]
  congr 1; funext p
  simp only [S]
  rw [← integral_const_mul]
  congr 1; funext d; ring

lemma integrable_pS (hV : Continuous V) (hsl : Superlinear V) (j : ℕ) (H : ℝ) :
    Integrable (fun p => p * exp (H * p) * S V j p) := by
  refine (Phi_integrable hV hsl j H).integral_prod_left.congr
    (Filter.Eventually.of_forall (fun p => ?_))
  simp only [S]
  rw [← integral_const_mul]
  congr 1; funext d; ring

lemma integrable_psinh (hV : Continuous V) (hsl : Superlinear V) (j : ℕ) (H : ℝ) :
    Integrable (fun p => p * sinh (H * p) * S V j p) := by
  have h1 := integrable_pS hV hsl j H
  have h2 := integrable_pS hV hsl j (-H)
  refine ((h1.sub h2).div_const 2).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.sub_apply]
  rw [sinh_eq, neg_mul]; ring

lemma sinh_form (hV : Continuous V) (hsl : Superlinear V) (hev : ∀ x, V (-x) = V x)
    (j : ℕ) (H : ℝ) :
    ∫ p, p * exp (H * p) * S V j p = ∫ p, p * sinh (H * p) * S V j p := by
  have hi := integrable_pS hV hsl j H
  have hi' : Integrable (fun p => p * exp (-(H * p)) * S V j p) := by
    refine (integrable_pS hV hsl j (-H)).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [neg_mul]
  have e2 : ∫ p, p * sinh (H * p) * S V j p
      = (1 / 2) * ∫ p, (p * exp (H * p) * S V j p - p * exp (-(H * p)) * S V j p) := by
    rw [← integral_const_mul]; congr 1; funext p; rw [sinh_eq]; ring
  have e3 : ∫ p, p * exp (-(H * p)) * S V j p = -∫ p, p * exp (H * p) * S V j p := by
    have := integral_neg_eq_self (fun p => p * exp (H * p) * S V j p) volume
    rw [← this, ← integral_neg]
    congr 1; funext p
    rw [S_neg hev, show H * -p = -(H * p) by ring]; ring
  rw [e2, integral_sub hi hi', e3]; ring

lemma psinh_nonneg {H : ℝ} (hH : 0 ≤ H) (p : ℝ) : 0 ≤ p * sinh (H * p) := by
  rcases le_total 0 p with h | h
  · exact mul_nonneg h (sinh_nonneg_iff.mpr (mul_nonneg hH h))
  · exact mul_nonneg_of_nonpos_of_nonpos h
      ((sinh_le_sinh.mpr (mul_nonpos_of_nonneg_of_nonpos hH h)).trans_eq sinh_zero)

lemma S0_pos (hV : Continuous V) (hsl : Superlinear V) (p : ℝ) : 0 < S V 0 p := by
  unfold S
  rw [integral_pos_iff_support_of_nonneg
    (fun d => by show (0 : ℝ) ≤ d ^ 0 * F V p d; simp [(F_pos V p d).le])
    (integrable_S_section hV hsl 0 p)]
  have : Function.support (fun d => d ^ 0 * F V p d) = univ := by
    ext d; simp [(F_pos V p d).ne']
  rw [this]; simp

lemma B_pos (hV : Continuous V) (hsl : Superlinear V) {H : ℝ} (hH : 0 < H) :
    0 < ∫ p, p * sinh (H * p) * S V 0 p := by
  have hnn : ∀ p, 0 ≤ p * sinh (H * p) * S V 0 p :=
    fun p => mul_nonneg (psinh_nonneg hH.le p) (S0_pos hV hsl p).le
  rw [integral_pos_iff_support_of_nonneg hnn (integrable_psinh hV hsl 0 H)]
  have : Ioi (0 : ℝ) ⊆ Function.support (fun p => p * sinh (H * p) * S V 0 p) := by
    intro p hp
    exact Function.mem_support.mpr (ne_of_gt (mul_pos (mul_pos hp
      (sinh_pos_iff.mpr (mul_pos hH hp))) (S0_pos hV hsl p)))
  exact lt_of_lt_of_le (by simp) (measure_mono this)

lemma mom0_pos (hV : Continuous V) (hsl : Superlinear V) (H : ℝ) : 0 < ∫ x, mfun V H 0 x := by
  have hpos : ∀ x, 0 < mfun V H 0 x := fun x => by unfold mfun; positivity
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) (integrable1 hV hsl 0 H)]
  have : Function.support (mfun V H 0) = univ := by
    ext x; simp [(hpos x).ne']
  rw [this]; simp

theorem R_eq_ratio (hV : Continuous V) (hsl : Superlinear V) (hev : ∀ x, V (-x) = V x)
    {c : ℝ} (hc : 0 < c)
    (hrot : ∀ Φ : ℝ × ℝ → ℝ, ∫ z : ℝ × ℝ, Φ (z.1 + z.2, z.1 - z.2) = c * ∫ z, Φ z)
    {H : ℝ} (hH : 0 < H) :
    R V H = (∫ p, p * sinh (H * p) * S V 2 p) / (∫ p, p * sinh (H * p) * S V 0 p) := by
  have hA : 2 * (Mom V 3 H * Mom V 0 H - Mom V 1 H * Mom V 2 H)
      = c * ∫ p, p * sinh (H * p) * S V 2 p := by
    simp only [Mom_eq]
    rw [← prodA hV hsl H]
    calc ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 * (z.1 + z.2) * (exp (H * z.1) * exp (-V z.1))
            * (exp (H * z.2) * exp (-V z.2))
        = ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 * (z.1 + z.2) * exp (H * (z.1 + z.2))
            * F V (z.1 + z.2) (z.1 - z.2) := by
          congr 1; funext z
          rw [F_shift, show H * (z.1 + z.2) = H * z.1 + H * z.2 by ring, exp_add]; ring
      _ = c * ∫ z : ℝ × ℝ, z.2 ^ 2 * z.1 * exp (H * z.1) * F V z.1 z.2 :=
          hrot (fun z => z.2 ^ 2 * z.1 * exp (H * z.1) * F V z.1 z.2)
      _ = _ := by rw [fubini_S hV hsl 2 H, sinh_form hV hsl hev 2 H]
  have hB : 2 * (Mom V 1 H * Mom V 0 H) = c * ∫ p, p * sinh (H * p) * S V 0 p := by
    simp only [Mom_eq]
    rw [← prodB hV hsl H]
    calc ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 0 * (z.1 + z.2) * (exp (H * z.1) * exp (-V z.1))
            * (exp (H * z.2) * exp (-V z.2))
        = ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 0 * (z.1 + z.2) * exp (H * (z.1 + z.2))
            * F V (z.1 + z.2) (z.1 - z.2) := by
          congr 1; funext z
          rw [F_shift, show H * (z.1 + z.2) = H * z.1 + H * z.2 by ring, exp_add]; ring
      _ = c * ∫ z : ℝ × ℝ, z.2 ^ 0 * z.1 * exp (H * z.1) * F V z.1 z.2 :=
          hrot (fun z => z.2 ^ 0 * z.1 * exp (H * z.1) * F V z.1 z.2)
      _ = _ := by rw [fubini_S hV hsl 0 H, sinh_form hV hsl hev 0 H]
  have hBp := B_pos hV hsl hH
  have hI0 : 0 < Mom V 0 H := by rw [Mom_eq]; exact mom0_pos hV hsl H
  have hY : 0 < Mom V 1 H * Mom V 0 H := by nlinarith [mul_pos hc hBp]
  have hI1 : Mom V 1 H ≠ 0 := left_ne_zero_of_mul hY.ne'
  have hI0' : Mom V 0 H ≠ 0 := hI0.ne'
  have hR : R V H = (Mom V 3 H * Mom V 0 H - Mom V 1 H * Mom V 2 H) / (Mom V 1 H * Mom V 0 H) := by
    unfold R
    rw [div_eq_div_iff (div_ne_zero hI1 hI0') hY.ne']
    field_simp
  rw [hR, div_eq_div_iff hY.ne' hBp.ne']
  linear_combination ((∫ p, p * sinh (H * p) * S V 0 p) * hA
    - (∫ p, p * sinh (H * p) * S V 2 p) * hB) / 2

/-- Step 4: the two-field cross inequality A(H₂)B(H₁) ≤ A(H₁)B(H₂). -/
theorem AB_cross (hV : Continuous V) (hsl : Superlinear V) (hev : ∀ x, V (-x) = V x)
    (hsup : Supermodular V) {H₁ H₂ : ℝ} (h1 : 0 ≤ H₁) (h12 : H₁ ≤ H₂) :
    (∫ p, p * sinh (H₂ * p) * S V 2 p) * (∫ p, p * sinh (H₁ * p) * S V 0 p)
      ≤ (∫ p, p * sinh (H₁ * p) * S V 2 p) * (∫ p, p * sinh (H₂ * p) * S V 0 p) := by
  apply cheb_prod (integrable_psinh hV hsl 2 H₂) (integrable_psinh hV hsl 0 H₁)
    (integrable_psinh hV hsl 2 H₁) (integrable_psinh hV hsl 0 H₂)
  apply cheb_even_cond
  any_goals (intro x; simp [S_neg hev])
  intro x y hx hy
  rcases le_total y x with hyx | hxy
  · have hS := S_cross hV hsl hsup hy hyx
    have hs := sinh_ratio h1 h12 hy hyx
    have key : 0 ≤ (x * y) * ((sinh (H₁ * x) * sinh (H₂ * y) - sinh (H₂ * x) * sinh (H₁ * y))
        * (S V 2 x * S V 0 y - S V 2 y * S V 0 x)) :=
      mul_nonneg (mul_nonneg hx hy) (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
    linear_combination key
  · have hS := S_cross hV hsl hsup hx hxy
    have hs := sinh_ratio h1 h12 hx hxy
    have key : 0 ≤ (x * y) * ((sinh (H₁ * x) * sinh (H₂ * y) - sinh (H₂ * x) * sinh (H₁ * y))
        * (S V 2 x * S V 0 y - S V 2 y * S V 0 x)) :=
      mul_nonneg (mul_nonneg hx hy) (mul_nonneg (by linarith) (by linarith))
    linear_combination key

/-- MAIN THEOREM (abstract form): R(H) = ⟨φ;φ²⟩_H/⟨φ⟩_H is nonincreasing on H > 0. -/
theorem R_antitoneOn_of_supermodular (hV : Continuous V) (hev : ∀ x, V (-x) = V x)
    (hsl : Superlinear V) (hsup : Supermodular V) : AntitoneOn (R V) (Ioi 0) := by
  obtain ⟨c, hc, hrot⟩ := rot_integral
  intro H₁ hH₁ H₂ hH₂ h12
  rw [R_eq_ratio hV hsl hev hc hrot hH₁, R_eq_ratio hV hsl hev hc hrot hH₂,
    div_le_div_iff₀ (B_pos hV hsl hH₂) (B_pos hV hsl hH₁)]
  exact AB_cross hV hsl hev hsup (le_of_lt hH₁) h12

end PP2OneSite

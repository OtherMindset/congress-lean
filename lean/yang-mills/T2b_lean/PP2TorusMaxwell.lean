import LongTable.PP2TorusEOM

/-!
Long Table, Claude council, target T2b, steps 3-4 of the T2b chain (AUDIT_AND_LIFT §A1-A2,
T2b_conditional §2): parameter derivatives, the Maxwell relation on the torus, and identity (★).
Setting and notation as in PP2TorusEOM.lean (w = exp(½ΣJφφ + HΣφ − Σ(aφ² + bφ⁴)), b > 0).

FORMALIZED (no sorry; axioms propext / Classical.choice / Quot.sound).
* `hasDerivAt_integral_H/_a`: differentiation under ∫ (Mathlib
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; dominations w_{H'} ≤ w_H e^{Σ|φ|} for
  |H'−H| < 1 and w_{a'} ≤ w_{a−1} for |a'−a| < 1).
* `hasDerivAt_ex_H`: d⟨O⟩/dH = ⟨O; Σ_yφ_y⟩;  `hasDerivAt_ex_a`: d⟨O⟩/da = −⟨O; Σ_yφ_y²⟩
  (every `Growth` observable O, any finite ι, any J).  `cov_sum`: ⟨O;Σ_yP_y⟩ = Σ_y⟨O;P_y⟩.
* S2: `hasDerivAt_m_a`: ∂_a⟨φ_x⟩ = −Σ_y⟨φ_x;φ_y²⟩;  `hasDerivAt_sq_H`: ∂_H⟨φ_x²⟩ =
  Σ_y⟨φ_x²;φ_y⟩;  `hasDerivAt_m_H`: χ = ∂_H⟨φ_x⟩ = Σ_y⟨φ_x;φ_y⟩;
  `maxwell` (translation-invariant J on a finite additive group):
  Σ_y⟨φ_0;φ_y²⟩ = Σ_y⟨φ_0²;φ_y⟩, hence ∂_H⟨φ_0²⟩ = −∂_a m.
* S3: `star_abstract` (pure calculus: EOM c·m − 4bT + H ≡ 0 and R = (T − mQ)/m ⟹
  m − Hm' = 4bm²(R' + Q')), and `star_identity`: for J symmetric and translation invariant,
  b > 0, any H with m(H) = ⟨φ_0⟩ ≠ 0,
     m − H·∂_H m = 4b m² (∂_H R + ∂_H⟨φ_0²⟩),   R = ⟨φ_0;φ_0²⟩/⟨φ_0⟩,
  with ∂ = `deriv`; `star_identity_maxwell`: the same with ∂_H⟨φ_0²⟩ replaced by −∂_a m.
  In continuum units (∂_μ = ½ε²∂_a, b = λε², H = ε²h) this is m − hχ = 4λm²∂_hR + 8λm²(−∂_μm).
NOT FORMALIZED: m > 0 for H > 0 (GKS + strictness; here a hypothesis m ≠ 0); GKS/GHS signs.
Toolchain: Lean 4.35.0, Mathlib 56a00585.
-/

open MeasureTheory Real Finset Metric

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
namespace T2bTorus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Σ_x φ_x (the conjugate of H). -/
def M1 (φ : ι → ℝ) : ℝ := ∑ x, φ x
/-- Σ_x φ_x² (minus the conjugate of a). -/
def M2 (φ : ι → ℝ) : ℝ := ∑ x, φ x ^ 2

theorem growth_M1 : Growth (M1 : (ι → ℝ) → ℝ) :=
  growth_congr (fun φ => rfl) (growth_sum univ fun x _ => growth_coord x)

theorem growth_M2 : Growth (M2 : (ι → ℝ) → ℝ) :=
  growth_congr (fun φ => rfl) (growth_sum univ fun x _ => growth_pow (growth_coord x) 2)

theorem growth_abs {F : (ι → ℝ) → ℝ} (hF : Growth F) : Growth (fun φ => |F φ|) := by
  obtain ⟨hc, C, k, h⟩ := hF
  exact ⟨hc.abs, C, k, fun φ => by rw [abs_abs]; exact h φ⟩

theorem growth_expS : Growth (fun φ : ι → ℝ => Real.exp (S φ)) := by
  refine ⟨by unfold S; fun_prop, 1, 1, fun φ => ?_⟩
  rw [abs_of_pos (Real.exp_pos _)]; simp

theorem wt_H_shift (J : ι → ι → ℝ) (a b H H' : ℝ) (φ : ι → ℝ) :
    wt J a b H' φ = wt J a b H φ * Real.exp ((H' - H) * M1 φ) := by
  unfold wt; rw [← Real.exp_add]; congr 1; unfold act M1; ring

theorem act_a_shift (J : ι → ι → ℝ) (a a' b H : ℝ) (φ : ι → ℝ) :
    act J a' b H φ = act J a b H φ - (a' - a) * M2 φ := by
  unfold act M2; simp only [sum_add_distrib, ← mul_sum]; ring

theorem hasDerivAt_wt_H (J : ι → ι → ℝ) (a b H : ℝ) (φ : ι → ℝ) :
    HasDerivAt (fun H' => wt J a b H' φ) (M1 φ * wt J a b H φ) H := by
  have e : (fun H' => act J a b H' φ) = fun H' => H' * M1 φ + act J a b 0 φ := by
    funext H'; unfold act M1; ring
  have h : HasDerivAt (fun H' => act J a b H' φ) (M1 φ) H := by
    rw [e]; simpa using ((hasDerivAt_id H).mul_const (M1 φ)).add_const (act J a b 0 φ)
  unfold wt; simpa [mul_comm] using h.exp

theorem hasDerivAt_wt_a (J : ι → ι → ℝ) (a b H : ℝ) (φ : ι → ℝ) :
    HasDerivAt (fun a' => wt J a' b H φ) (-M2 φ * wt J a b H φ) a := by
  have e : (fun a' => act J a' b H φ) = fun a' => act J 0 b H φ - a' * M2 φ := by
    funext a'; rw [act_a_shift J 0 a' b H φ]; ring
  have h : HasDerivAt (fun a' => act J a' b H φ) (-M2 φ) a := by
    rw [e]; simpa using ((hasDerivAt_id a).mul_const (M2 φ)).const_sub (act J 0 b H φ)
  unfold wt; simpa [mul_comm] using h.exp

/-- Differentiation under the integral in H: d/dH ∫ O w = ∫ O·Σφ·w. -/
theorem hasDerivAt_integral_H (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) {O : (ι → ℝ) → ℝ}
    (hO : Growth O) (H : ℝ) :
    HasDerivAt (fun H' => ∫ φ, O φ * wt J a b H' φ) (∫ φ, O φ * M1 φ * wt J a b H φ) H := by
  have hB := integrable_growth J a hb H
    (growth_mul (growth_abs (growth_mul hO growth_M1)) growth_expS)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds H one_pos)
    (F := fun H' φ => O φ * wt J a b H' φ) (F' := fun H' φ => O φ * M1 φ * wt J a b H' φ)
    (Filter.Eventually.of_forall fun H' =>
      (hO.1.mul (continuous_wt J a b H')).aestronglyMeasurable)
    (integrable_growth J a hb H hO)
    ((hO.1.mul growth_M1.1).mul (continuous_wt J a b H)).aestronglyMeasurable
    (ae_of_all _ fun φ H' hH' => ?_) hB (ae_of_all _ fun φ H' _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos J a b H' φ), wt_H_shift J a b H H' φ]
    have h1 : (H' - H) * M1 φ ≤ S φ := by
      have hd : |H' - H| < 1 := by rw [← Real.dist_eq]; exact mem_ball.mp hH'
      have hM : |M1 φ| ≤ S φ := abs_sum_le_sum_abs _ _
      calc (H' - H) * M1 φ ≤ |(H' - H) * M1 φ| := le_abs_self _
        _ = |H' - H| * |M1 φ| := abs_mul _ _
        _ ≤ 1 * S φ := mul_le_mul hd.le hM (abs_nonneg _) zero_le_one
        _ = S φ := one_mul _
    have h2 := Real.exp_le_exp.mpr h1
    have hw := (wt_pos J a b H φ).le
    calc |O φ * M1 φ| * (wt J a b H φ * Real.exp ((H' - H) * M1 φ))
        ≤ |O φ * M1 φ| * (wt J a b H φ * Real.exp (S φ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hw) (abs_nonneg _)
      _ = _ := by ring
  · simpa [mul_assoc] using (hasDerivAt_wt_H J a b H' φ).const_mul (O φ)

/-- Differentiation under the integral in a: d/da ∫ O w = −∫ O·Σφ²·w. -/
theorem hasDerivAt_integral_a (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) {O : (ι → ℝ) → ℝ}
    (hO : Growth O) (H : ℝ) :
    HasDerivAt (fun a' => ∫ φ, O φ * wt J a' b H φ) (∫ φ, O φ * (-M2 φ) * wt J a b H φ) a := by
  have hB := integrable_growth J (a - 1) hb H (growth_abs (growth_mul hO growth_M2))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds a one_pos)
    (F := fun a' φ => O φ * wt J a' b H φ) (F' := fun a' φ => O φ * (-M2 φ) * wt J a' b H φ)
    (Filter.Eventually.of_forall fun a' =>
      (hO.1.mul (continuous_wt J a' b H)).aestronglyMeasurable)
    (integrable_growth J a hb H hO)
    ((hO.1.mul growth_M2.1.neg).mul (continuous_wt J a b H)).aestronglyMeasurable
    (ae_of_all _ fun φ a' ha' => ?_) hB (ae_of_all _ fun φ a' _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos J a' b H φ), abs_mul, abs_neg, ← abs_mul]
    have hd : |a' - a| < 1 := by rw [← Real.dist_eq]; exact mem_ball.mp ha'
    have hge : 0 ≤ a' - (a - 1) := by linarith [neg_abs_le (a' - a)]
    have hw : wt J a' b H φ ≤ wt J (a - 1) b H φ := by
      unfold wt; rw [act_a_shift J (a - 1) a' b H φ]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ M2 φ := sum_nonneg fun _ _ => sq_nonneg _
      nlinarith
    exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  · simpa [mul_assoc] using (hasDerivAt_wt_a J a' b H φ).const_mul (O φ)

/-- **dH formula**: d⟨O⟩/dH = ⟨O; Σφ⟩. -/
theorem hasDerivAt_ex_H (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) {O : (ι → ℝ) → ℝ}
    (hO : Growth O) (H : ℝ) :
    HasDerivAt (fun H' => ex J a b H' O) (cov J a b H O M1) H := by
  have hN := hasDerivAt_integral_H J a hb hO H
  have hZ : HasDerivAt (fun H' => Zf J a b H') (∫ φ, M1 φ * wt J a b H φ) H := by
    simpa [Zf] using hasDerivAt_integral_H J a hb (growth_const 1) H
  have hZ0 := (Zf_pos J a hb H).ne'
  convert hN.div hZ hZ0 using 1
  · funext H'; rfl
  unfold cov ex; field_simp

/-- **da formula**: d⟨O⟩/da = −⟨O; Σφ²⟩. -/
theorem hasDerivAt_ex_a (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) {O : (ι → ℝ) → ℝ}
    (hO : Growth O) (H : ℝ) :
    HasDerivAt (fun a' => ex J a' b H O) (-cov J a b H O M2) a := by
  have hN := hasDerivAt_integral_a J a hb hO H
  have hZ : HasDerivAt (fun a' => Zf J a' b H) (∫ φ, (-M2 φ) * wt J a b H φ) a := by
    simpa [Zf] using hasDerivAt_integral_a J a hb (growth_const 1) H
  have hZ0 := (Zf_pos J a hb H).ne'
  convert hN.div hZ hZ0 using 1
  · funext a'; rfl
  unfold cov ex
  simp only [mul_neg, neg_mul, integral_neg]
  field_simp; ring

theorem cov_sum (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) {O : (ι → ℝ) → ℝ}
    {P : ι → (ι → ℝ) → ℝ} (hO : Growth O) (hP : ∀ y, Growth (P y)) :
    cov J a b H O (fun φ => ∑ y, P y φ) = ∑ y, cov J a b H O (P y) := by
  unfold cov
  have e : (fun φ => O φ * ∑ y, P y φ) = fun φ => ∑ y, O φ * P y φ :=
    funext fun φ => mul_sum _ _ _
  rw [e, ex_sum J a hb H univ fun y _ => growth_mul hO (hP y),
    ex_sum J a hb H univ fun y _ => hP y, mul_sum, ← sum_sub_distrib]

/-- **S2a**: −∂_a⟨φ_x⟩ = Σ_y ⟨φ_x; φ_y²⟩. -/
theorem hasDerivAt_m_a (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) (x : ι) :
    HasDerivAt (fun a' => ex J a' b H (fun φ => φ x))
      (-∑ y, cov J a b H (fun φ => φ x) (fun φ => φ y ^ 2)) a := by
  have h := hasDerivAt_ex_a J a hb (growth_coord x) H
  rwa [show (M2 : (ι → ℝ) → ℝ) = fun φ => ∑ y, φ y ^ 2 from rfl,
    cov_sum J a hb H (growth_coord x) fun y => growth_pow (growth_coord y) 2] at h

/-- **S2b**: ∂_H⟨φ_x²⟩ = Σ_y ⟨φ_x²; φ_y⟩. -/
theorem hasDerivAt_sq_H (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) (x : ι) :
    HasDerivAt (fun H' => ex J a b H' (fun φ => φ x ^ 2))
      (∑ y, cov J a b H (fun φ => φ x ^ 2) (fun φ => φ y)) H := by
  have h := hasDerivAt_ex_H J a hb (growth_pow (growth_coord x) 2) H
  rwa [show (M1 : (ι → ℝ) → ℝ) = fun φ => ∑ y, φ y from rfl,
    cov_sum J a hb H (growth_pow (growth_coord x) 2) fun y => growth_coord y] at h

/-- Susceptibility: ∂_H⟨φ_x⟩ = Σ_y ⟨φ_x; φ_y⟩. -/
theorem hasDerivAt_m_H (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) (x : ι) :
    HasDerivAt (fun H' => ex J a b H' (fun φ => φ x))
      (∑ y, cov J a b H (fun φ => φ x) (fun φ => φ y)) H := by
  have h := hasDerivAt_ex_H J a hb (growth_coord x) H
  rwa [show (M1 : (ι → ℝ) → ℝ) = fun φ => ∑ y, φ y from rfl,
    cov_sum J a hb H (growth_coord x) fun y => growth_coord y] at h

section TI
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **S2c (Maxwell on the torus)**: Σ_y⟨φ_0;φ_y²⟩ = Σ_y⟨φ_0²;φ_y⟩. -/
theorem maxwell (J : G → G → ℝ) (hJ : ∀ x y z, J (x + z) (y + z) = J x y) (a b H : ℝ) :
    ∑ y, cov J a b H (fun φ => φ 0) (fun φ => φ y ^ 2)
      = ∑ y, cov J a b H (fun φ => φ 0 ^ 2) (fun φ => φ y) := by
  have h1 : ∀ y : G, ex J a b H (fun φ => φ 0 * φ y ^ 2)
      = ex J a b H (fun φ => φ (-y) * φ 0 ^ 2) := fun y => by
    rw [← ex_shift J hJ a b H y (fun φ => φ (-y) * φ 0 ^ 2)]; simp [shift]
  have h2 : ∀ y : G, ex J a b H (fun φ => φ y ^ 2) = ex J a b H (fun φ => φ 0 ^ 2) :=
    fun y => ex_coord J hJ a b H y (· ^ 2)
  have h3 : ∀ y : G, ex J a b H (fun φ => φ y) = ex J a b H (fun φ => φ 0) :=
    fun y => ex_coord J hJ a b H y id
  have h4 : ∀ y : G, ex J a b H (fun φ => φ 0 ^ 2 * φ y)
      = ex J a b H (fun φ => φ y * φ 0 ^ 2) := fun y => by
    congr 1; funext φ; ring
  have k1 : ∀ y : G, cov J a b H (fun φ => φ 0) (fun φ => φ y ^ 2) =
      ex J a b H (fun φ => φ (-y) * φ 0 ^ 2)
        - ex J a b H (fun φ => φ 0) * ex J a b H (fun φ => φ 0 ^ 2) := fun y => by
    unfold cov; rw [h1 y, h2 y]
  have k2 : ∀ y : G, cov J a b H (fun φ => φ 0 ^ 2) (fun φ => φ y) =
      ex J a b H (fun φ => φ y * φ 0 ^ 2)
        - ex J a b H (fun φ => φ 0 ^ 2) * ex J a b H (fun φ => φ 0) := fun y => by
    unfold cov; rw [h4 y, h3 y]
  have := Fintype.sum_equiv (Equiv.neg G) (fun y => ex J a b H (fun φ => φ (-y) * φ 0 ^ 2))
    (fun y => ex J a b H (fun φ => φ y * φ 0 ^ 2)) (fun _ => rfl)
  rw [sum_congr rfl fun y _ => k1 y, sum_congr rfl fun y _ => k2 y, sum_sub_distrib,
    sum_sub_distrib, this]
  congr 1; exact sum_congr rfl fun _ _ => mul_comm _ _

end TI

/-! ## S3: the identity (★) -/

/-- Algebraic core of (★): if c·m − 4b·T + H ≡ 0 (EOM) and R = (T − mQ)/m, then
m − Hχ = 4b m²(R' + Q'). -/
theorem star_abstract {m T Q : ℝ → ℝ} {c b H χ q r : ℝ} (hb : b ≠ 0) (hm : m H ≠ 0)
    (heom : ∀ H', c * m H' - 4 * b * T H' + H' = 0)
    (hmd : HasDerivAt m χ H) (hQd : HasDerivAt Q q H)
    (hRd : HasDerivAt (fun H' => (T H' - m H' * Q H') / m H') r H) :
    m H - H * χ = 4 * b * m H ^ 2 * (r + q) := by
  have eT : T = fun H' => (c * m H' + H') / (4 * b) := by
    funext H'; have := heom H'; field_simp; linarith
  have hT : HasDerivAt T ((c * χ + 1) / (4 * b)) H := by
    rw [eT]; exact ((hmd.const_mul c).add (hasDerivAt_id' H)).div_const _
  have h2 := (hT.sub (hmd.mul hQd)).div hmd hm
  have hr := hRd.unique h2
  simp only [Pi.sub_apply, Pi.mul_apply] at hr
  rw [hr]
  have : T H = (c * m H + H) / (4 * b) := by rw [eT]
  rw [this]
  field_simp
  ring

section TI
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **S3 (identity ★, lattice units)**: on a translation-invariant finite graph, at any H with
m(H) = ⟨φ_0⟩ ≠ 0 (true for H > 0 by GKS; not formalised), with R = ⟨φ_0;φ_0²⟩/m and
χ = ∂_H m: m − Hχ = 4b m²(∂_H R + ∂_H⟨φ_0²⟩). -/
theorem star_identity (J : G → G → ℝ) (hJs : ∀ x y, J x y = J y x)
    (hJ : ∀ x y z, J (x + z) (y + z) = J x y) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ)
    (hm : ex J a b H (fun φ => φ 0) ≠ 0) :
    ex J a b H (fun φ => φ 0) - H * deriv (fun H' => ex J a b H' (fun φ => φ 0)) H
      = 4 * b * ex J a b H (fun φ => φ 0) ^ 2 *
        (deriv (fun H' => cov J a b H' (fun φ => φ 0) (fun φ => φ 0 ^ 2)
            / ex J a b H' (fun φ => φ 0)) H
          + deriv (fun H' => ex J a b H' (fun φ => φ 0 ^ 2)) H) := by
  have hmd := hasDerivAt_m_H J a hb H 0
  have hQd := hasDerivAt_sq_H J a hb H 0
  have hTd := hasDerivAt_ex_H J a hb (growth_pow (growth_coord (0 : G)) 3) H
  have hR0 := (hTd.sub (hmd.mul hQd)).div hmd hm
  have eR : (fun H' => cov J a b H' (fun φ => φ 0) (fun φ => φ 0 ^ 2)
      / ex J a b H' (fun φ => φ 0)) = fun H' => (ex J a b H' (fun φ => φ 0 ^ 3)
        - ex J a b H' (fun φ => φ 0) * ex J a b H' (fun φ => φ 0 ^ 2))
          / ex J a b H' (fun φ => φ 0) := by
    funext H'; unfold cov
    rw [show (fun φ : G → ℝ => φ 0 * φ 0 ^ 2) = fun φ => φ 0 ^ 3 from funext fun φ => by ring]
  have hRd := hR0.congr_of_eventuallyEq (f₁ := fun H' => cov J a b H' (fun φ => φ 0)
      (fun φ => φ 0 ^ 2) / ex J a b H' (fun φ => φ 0))
    (Filter.Eventually.of_forall fun H' => congrFun eR H')
  rw [hmd.deriv, hQd.deriv, hRd.deriv]
  exact star_abstract (m := fun H' => ex J a b H' (fun φ => φ 0))
    (T := fun H' => ex J a b H' (fun φ => φ 0 ^ 3))
    (Q := fun H' => ex J a b H' (fun φ => φ 0 ^ 2)) (c := (∑ y, J 0 y) - 2 * a) hb.ne' hm
    (fun H' => eom_ti J hJs hJ a hb H') hmd hQd hR0

/-- (★) with Maxwell: m − Hχ = 4b m²(∂_H R − ∂_a m), the lattice form of
m − hχ = 4λm²∂_hR + 8λm²(−∂_μm) (∂_μ = ½ε²∂_a, b = λε²). -/
theorem star_identity_maxwell (J : G → G → ℝ) (hJs : ∀ x y, J x y = J y x)
    (hJ : ∀ x y z, J (x + z) (y + z) = J x y) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ)
    (hm : ex J a b H (fun φ => φ 0) ≠ 0) :
    ex J a b H (fun φ => φ 0) - H * deriv (fun H' => ex J a b H' (fun φ => φ 0)) H
      = 4 * b * ex J a b H (fun φ => φ 0) ^ 2 *
        (deriv (fun H' => cov J a b H' (fun φ => φ 0) (fun φ => φ 0 ^ 2)
            / ex J a b H' (fun φ => φ 0)) H
          - deriv (fun a' => ex J a' b H (fun φ => φ 0)) a) := by
  rw [star_identity J hJs hJ a hb H hm, (hasDerivAt_sq_H J a hb H 0).deriv,
    (hasDerivAt_m_a J a hb H 0).deriv, maxwell J hJ a b H]
  ring

end TI

end T2bTorus

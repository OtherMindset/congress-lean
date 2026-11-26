import Mathlib

/-!
Long Table, Claude council, target T2b, steps 1-2 of the T2b chain (AUDIT_AND_LIFT §A1, T2b_conditional
§2): the exact lattice equation of motion. Finite vertex set ι, weight
  w(φ) = exp(½Σ_{x,y}J_xy φ_xφ_y + HΣφ_x − Σ(aφ_x² + bφ_x⁴)),  b > 0,
on ℝ^ι (Lebesgue); ⟨O⟩ = ∫O w/∫w. With J the adjacency matrix, ½ΣJφφ = Σ_{⟨xy⟩}φ_xφ_y.

FORMALIZED (no sorry; axioms propext / Classical.choice / Quot.sound).
* `wt_le`: for every k, w ≤ C·exp(−kΣ|φ_x| − Σφ_x²) (quartic dominates; no sign on a, J).
  `integrable_growth`: O·w integrable for every continuous O with |O| ≤ C e^{kΣ|φ|}
  (`Growth`, closed under +, ·, Σ, powers; coordinates). `Zf_pos`: 0 < ∫w.
* `hasLineDerivAt_wt`: ∂_x w = (Σ_y J_xy φ_y + H − 2aφ_x − 4bφ_x³)·w for symmetric J.
* `eom` (S1, any finite graph, J symmetric): for every x,
    ⟨Σ_y J_xy φ_y⟩ − 2a⟨φ_x⟩ − 4b⟨φ_x³⟩ + H = 0.
  Proof: Mathlib's line-derivative integration by parts with f ≡ 1, g = w.
* `ex_add/ex_sub/ex_sum/ex_const_mul/ex_const`: linearity of ⟨·⟩ on `Growth` observables.
* TI (ι = an additive finite group G, J_{x+z,y+z} = J_xy): `measurePreserving_shift`,
  `ex_shift` ⟨F∘τ_z⟩ = ⟨F⟩, `ex_coord` ⟨F(φ_y)⟩ = ⟨F(φ_0)⟩, and
  `eom_ti`: ((Σ_y J_0y) − 2a)⟨φ_0⟩ − 4b⟨φ_0³⟩ + H = 0.
  For the n.n. torus (ZMod N)², N ≥ 3, Σ_y J_0y = 4 (= 2·dim), so this is (4 − 2a)m − 4b⟨φ³⟩
  + H = 0, i.e. μ_b m + 4λ⟨φ_0³⟩ = h with a = 2 + ε²μ_b/2, b = λε², H = ε²h.
NOT FORMALIZED here: derivatives in H, a, Maxwell, identity (★) (see PP2TorusMaxwell.lean);
m > 0 at H > 0 (GKS); the concrete count Σ_y J_0y = 4 on (ZMod N)².
Self-contained: imports only Mathlib (ideas from PP2SimonLieb2 `ibp_fixed`, no code imported).
Toolchain: Lean 4.35.0, Mathlib 56a00585.
-/

open MeasureTheory Real Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
namespace T2bTorus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The action Σ_{⟨xy⟩} φ_xφ_y + HΣφ_x − Σ(aφ_x² + bφ_x⁴), with the bond sum written via a
coupling matrix: Σ_{⟨xy⟩}φ_xφ_y = ½Σ_xΣ_y J x y φ_xφ_y (J = adjacency matrix). -/
def act (J : ι → ι → ℝ) (a b H : ℝ) (φ : ι → ℝ) : ℝ :=
  (∑ x, ∑ y, J x y * φ x * φ y) / 2 + H * ∑ x, φ x - ∑ x, (a * φ x ^ 2 + b * φ x ^ 4)

/-- The weight w(φ) = exp(act). -/
def wt (J : ι → ι → ℝ) (a b H : ℝ) (φ : ι → ℝ) : ℝ := Real.exp (act J a b H φ)

/-- Partition function. -/
def Zf (J : ι → ι → ℝ) (a b H : ℝ) : ℝ := ∫ φ, wt J a b H φ

/-- Normalised expectation ⟨O⟩. -/
def ex (J : ι → ι → ℝ) (a b H : ℝ) (O : (ι → ℝ) → ℝ) : ℝ :=
  (∫ φ, O φ * wt J a b H φ) / Zf J a b H

/-- Truncated two-point function ⟨O;P⟩. -/
def cov (J : ι → ι → ℝ) (a b H : ℝ) (O P : (ι → ℝ) → ℝ) : ℝ :=
  ex J a b H (fun φ => O φ * P φ) - ex J a b H O * ex J a b H P

/-- S(φ) = Σ|φ_x|. -/
def S (φ : ι → ℝ) : ℝ := ∑ x, |φ x|

/-! ## Integrability -/

theorem continuous_act (J : ι → ι → ℝ) (a b H : ℝ) : Continuous (act J a b H) := by
  unfold act; fun_prop

theorem continuous_wt (J : ι → ι → ℝ) (a b H : ℝ) : Continuous (wt J a b H) := by
  unfold wt; exact (continuous_act J a b H).rexp

theorem wt_pos (J : ι → ι → ℝ) (a b H : ℝ) (φ : ι → ℝ) : 0 < wt J a b H φ := Real.exp_pos _

/-- One-site bound: the quartic dominates. -/
theorem quartic_bound {α β b : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ D, ∀ t : ℝ, α * t ^ 2 + β * |t| - b * t ^ 4 ≤ D := by
  refine ⟨β + (α + β) ^ 2 / (4 * b), fun t => ?_⟩
  set u := |t|
  have hu : 0 ≤ u := abs_nonneg t
  have ht2 : t ^ 2 = u ^ 2 := (sq_abs t).symm
  have ht4 : t ^ 4 = (u ^ 2) ^ 2 := by rw [← ht2]; ring
  rw [ht2, ht4]
  have h1 : β * u ≤ β + β * u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
  have h2 : (α + β) * u ^ 2 - b * (u ^ 2) ^ 2 ≤ (α + β) ^ 2 / (4 * b) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (2 * b * u ^ 2 - (α + β))]
  nlinarith

theorem sum_sq_nonneg (φ : ι → ℝ) : 0 ≤ ∑ x, φ x ^ 2 := sum_nonneg fun _ _ => sq_nonneg _

theorem S_nonneg (φ : ι → ℝ) : 0 ≤ S φ := sum_nonneg fun _ _ => abs_nonneg _

/-- Pair term bounded by |J| times Σφ². -/
theorem pair_le (J : ι → ι → ℝ) (φ : ι → ℝ) :
    (∑ x, ∑ y, J x y * φ x * φ y) / 2 ≤ (∑ x, ∑ y, |J x y|) * ∑ x, φ x ^ 2 := by
  set Q := ∑ x, φ x ^ 2
  have hQ : 0 ≤ Q := sum_sq_nonneg φ
  have hsq : ∀ x, φ x ^ 2 ≤ Q := fun x =>
    single_le_sum (f := fun x => φ x ^ 2) (fun _ _ => sq_nonneg _) (mem_univ x)
  have key : ∀ x y, J x y * φ x * φ y ≤ |J x y| * Q := by
    intro x y
    have h1 : |φ x * φ y| ≤ Q := by
      rw [abs_mul]
      have := hsq x; have := hsq y
      nlinarith [sq_abs (φ x), sq_abs (φ y), sq_nonneg (|φ x| - |φ y|), abs_nonneg (φ x),
        abs_nonneg (φ y)]
    calc J x y * φ x * φ y = J x y * (φ x * φ y) := by ring
      _ ≤ |J x y * (φ x * φ y)| := le_abs_self _
      _ = |J x y| * |φ x * φ y| := abs_mul _ _
      _ ≤ |J x y| * Q := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hs : ∑ x, ∑ y, J x y * φ x * φ y ≤ (∑ x, ∑ y, |J x y|) * Q := by
    rw [sum_mul]; refine sum_le_sum fun x _ => ?_
    rw [sum_mul]; exact sum_le_sum fun y _ => key x y
  have hM : 0 ≤ (∑ x, ∑ y, |J x y|) * Q :=
    mul_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hQ
  linarith

/-- Weight bound: for every k, w ≤ C exp(−kS − Σφ²). -/
theorem wt_le (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H k : ℝ) :
    ∃ C, ∀ φ, wt J a b H φ ≤ C * Real.exp (-(k * S φ) - ∑ x, φ x ^ 2) := by
  set M := ∑ x, ∑ y, |J x y|
  have hM : 0 ≤ M := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨D, hD⟩ := quartic_bound (α := M + |a| + 1) (β := |H| + |k|) (b := b)
    (by positivity) (by positivity) hb
  refine ⟨Real.exp (Fintype.card ι * D), fun φ => ?_⟩
  unfold wt
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (∑ x, ∑ y, J x y * φ x * φ y) / 2 ≤ M * ∑ x, φ x ^ 2 := pair_le J φ
  have h2 : H * ∑ x, φ x ≤ |H| * S φ := by
    calc H * ∑ x, φ x ≤ |H * ∑ x, φ x| := le_abs_self _
      _ = |H| * |∑ x, φ x| := abs_mul _ _
      _ ≤ |H| * S φ := mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)
  have h3 : k * S φ ≤ |k| * S φ := by
    have := le_abs_self k; nlinarith [S_nonneg φ]
  have h4 : ∀ x, -(a * φ x ^ 2) ≤ |a| * φ x ^ 2 := fun x => by
    have := neg_abs_le a; nlinarith [sq_nonneg (φ x)]
  have key : ∑ x, ((M + |a| + 1) * φ x ^ 2 + (|H| + |k|) * |φ x| - b * φ x ^ 4)
      ≤ Fintype.card ι * D := by
    calc _ ≤ ∑ _x : ι, D := sum_le_sum fun x _ => hD (φ x)
      _ = _ := by simp
  have e1 : ∑ x, ((M + |a| + 1) * φ x ^ 2 + (|H| + |k|) * |φ x| - b * φ x ^ 4)
      = M * ∑ x, φ x ^ 2 + (|H| + |k|) * S φ + ∑ x, (|a| * φ x ^ 2) + ∑ x, φ x ^ 2
        - ∑ x, b * φ x ^ 4 := by
    simp only [S, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  have h5 : -∑ x, (a * φ x ^ 2 + b * φ x ^ 4) ≤ ∑ x, (|a| * φ x ^ 2) - ∑ x, b * φ x ^ 4 := by
    rw [sum_add_distrib]
    have : -∑ x, a * φ x ^ 2 ≤ ∑ x, |a| * φ x ^ 2 := by
      rw [← sum_neg_distrib]; exact sum_le_sum fun x _ => h4 x
    linarith
  unfold act
  linarith

theorem integrable_exp_neg_sq : Integrable (fun φ : ι → ℝ => Real.exp (-∑ x, φ x ^ 2)) := by
  have : (fun φ : ι → ℝ => Real.exp (-∑ x, φ x ^ 2)) =
      fun φ => ∏ x, Real.exp (-1 * φ x ^ 2) := by
    funext φ; rw [← Real.exp_sum]; congr 1; simp [sum_neg_distrib]
  rw [this]
  exact Integrable.fintype_prod (f := fun _ t => Real.exp (-1 * t ^ 2))
    (fun _ => integrable_exp_neg_mul_sq one_pos)

/-- Observables of at most exponential-linear growth. -/
def Growth (G : (ι → ℝ) → ℝ) : Prop :=
  Continuous G ∧ ∃ C k, ∀ φ, |G φ| ≤ C * Real.exp (k * S φ)

theorem growth_const (c : ℝ) : Growth (fun _ : ι → ℝ => c) :=
  ⟨continuous_const, |c|, 0, fun φ => by simp⟩

theorem growth_coord (x : ι) : Growth (fun φ : ι → ℝ => φ x) := by
  refine ⟨continuous_apply x, 1, 1, fun φ => ?_⟩
  have h1 : |φ x| ≤ S φ :=
    single_le_sum (f := fun x => |φ x|) (fun _ _ => abs_nonneg _) (mem_univ x)
  have h2 := Real.add_one_le_exp (S φ)
  show |φ x| ≤ _
  simp only [one_mul]; linarith

theorem growth_mul {F G : (ι → ℝ) → ℝ} (hF : Growth F) (hG : Growth G) :
    Growth (fun φ => F φ * G φ) := by
  obtain ⟨hFc, C1, k1, h1⟩ := hF
  obtain ⟨hGc, C2, k2, h2⟩ := hG
  refine ⟨hFc.mul hGc, C1 * C2, k1 + k2, fun φ => ?_⟩
  rw [abs_mul, add_mul, Real.exp_add]
  have := (abs_nonneg (F φ)).trans (h1 φ)
  calc |F φ| * |G φ| ≤ (C1 * Real.exp (k1 * S φ)) * (C2 * Real.exp (k2 * S φ)) :=
        mul_le_mul (h1 φ) (h2 φ) (abs_nonneg _) this
    _ = _ := by ring

theorem growth_add {F G : (ι → ℝ) → ℝ} (hF : Growth F) (hG : Growth G) :
    Growth (fun φ => F φ + G φ) := by
  obtain ⟨hFc, C1, k1, h1⟩ := hF
  obtain ⟨hGc, C2, k2, h2⟩ := hG
  refine ⟨hFc.add hGc, C1 + C2, |k1| + |k2|, fun φ => ?_⟩
  have hS := S_nonneg φ
  have e1 : Real.exp (k1 * S φ) ≤ Real.exp ((|k1| + |k2|) * S φ) :=
    Real.exp_le_exp.mpr (by nlinarith [le_abs_self k1, abs_nonneg k2])
  have e2 : Real.exp (k2 * S φ) ≤ Real.exp ((|k1| + |k2|) * S φ) :=
    Real.exp_le_exp.mpr (by nlinarith [le_abs_self k2, abs_nonneg k1])
  have c1 : 0 ≤ C1 := by
    have := (abs_nonneg (F φ)).trans (h1 φ)
    by_contra hc; push Not at hc; nlinarith [Real.exp_pos (k1 * S φ)]
  have c2 : 0 ≤ C2 := by
    have := (abs_nonneg (G φ)).trans (h2 φ)
    by_contra hc; push Not at hc; nlinarith [Real.exp_pos (k2 * S φ)]
  calc |F φ + G φ| ≤ |F φ| + |G φ| := abs_add_le _ _
    _ ≤ C1 * Real.exp (k1 * S φ) + C2 * Real.exp (k2 * S φ) := add_le_add (h1 φ) (h2 φ)
    _ ≤ C1 * Real.exp ((|k1| + |k2|) * S φ) + C2 * Real.exp ((|k1| + |k2|) * S φ) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 c1) (mul_le_mul_of_nonneg_left e2 c2)
    _ = _ := by ring

theorem growth_smul (c : ℝ) {F : (ι → ℝ) → ℝ} (hF : Growth F) : Growth (fun φ => c * F φ) :=
  growth_mul (growth_const c) hF

theorem growth_sum {κ : Type*} (s : Finset κ) {F : κ → (ι → ℝ) → ℝ}
    (hF : ∀ i ∈ s, Growth (F i)) : Growth (fun φ => ∑ i ∈ s, F i φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using growth_const (ι := ι) 0
  | insert j s hj ih =>
    simp only [sum_insert hj]
    exact growth_add (hF j (mem_insert_self j s)) (ih fun i hi => hF i (mem_insert_of_mem hi))

theorem growth_pow {F : (ι → ℝ) → ℝ} (hF : Growth F) (n : ℕ) : Growth (fun φ => F φ ^ n) := by
  induction n with
  | zero => simpa using growth_const (ι := ι) 1
  | succ n ih => simp only [pow_succ]; exact growth_mul ih hF

/-- Integrability of a growth-bounded observable against the weight. -/
theorem integrable_growth (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ)
    {G : (ι → ℝ) → ℝ} (hG : Growth G) : Integrable (fun φ => G φ * wt J a b H φ) := by
  obtain ⟨hGc, C, k, hC⟩ := hG
  obtain ⟨C', hC'⟩ := wt_le J a hb H k
  refine Integrable.mono' ((integrable_exp_neg_sq (ι := ι)).const_mul (C * C'))
    (hGc.mul (continuous_wt J a b H)).aestronglyMeasurable (Filter.Eventually.of_forall
      fun φ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos J a b H φ)]
  have hw := hC' φ
  have h0 : 0 ≤ C * Real.exp (k * S φ) := (abs_nonneg _).trans (hC φ)
  calc |G φ| * wt J a b H φ ≤ C * Real.exp (k * S φ) *
        (C' * Real.exp (-(k * S φ) - ∑ x, φ x ^ 2)) :=
        mul_le_mul (hC φ) hw (wt_pos J a b H φ).le h0
    _ = C * C' * (Real.exp (k * S φ) * Real.exp (-(k * S φ) - ∑ x, φ x ^ 2)) := by ring
    _ = C * C' * Real.exp (-∑ x, φ x ^ 2) := by rw [← Real.exp_add]; ring_nf

theorem integrable_wt (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) :
    Integrable (wt J a b H) := by
  simpa using integrable_growth J a hb H (growth_const 1)

theorem Zf_pos (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) : 0 < Zf J a b H := by
  unfold Zf wt
  exact integral_exp_pos (integrable_wt J a hb H)


/-! ## S1: the equation of motion (integration by parts in φ_x) -/

/-- ∂_x act (for symmetric J). -/
def dact (J : ι → ι → ℝ) (a b H : ℝ) (x : ι) (φ : ι → ℝ) : ℝ :=
  ∑ y, J x y * φ y + H - 2 * a * φ x - 4 * b * φ x ^ 3

theorem hasLineDerivAt_act (J : ι → ι → ℝ) (hJ : ∀ x y, J x y = J y x) (a b H : ℝ)
    (φ : ι → ℝ) (x : ι) :
    HasLineDerivAt ℝ (act J a b H) (dact J a b H x φ) φ (Pi.single x 1) := by
  set e : ι → ℝ := Pi.single x 1 with he
  have hc : ∀ y, HasDerivAt (fun t : ℝ => φ y + t * e y) (e y) 0 := fun y => by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (e y)).const_add (φ y)
  have h := ((HasDerivAt.sum (u := univ) fun x' _ => HasDerivAt.sum (u := univ) fun y _ =>
      ((hc x').const_mul (J x' y)).mul (hc y)).div_const 2).add
      ((HasDerivAt.sum (u := univ) fun y _ => hc y).const_mul H) |>.sub
      (HasDerivAt.sum (u := univ) fun y _ => (((hc y).pow 2).const_mul a).add (((hc y).pow 4).const_mul b))
  unfold HasLineDerivAt
  convert h using 1
  · funext t; simp [act, mul_assoc]
  · simp only [he, Pi.single_apply, zero_mul, add_zero, mul_ite, mul_one, mul_zero, sum_ite_eq',
      mem_univ, ite_true, sum_add_distrib, ite_mul, zero_mul, ite_self, add_zero]
    simp only [dact]
    have : ∑ x', J x' x * φ x' = ∑ y, J x y * φ y := sum_congr rfl fun y _ => by rw [hJ]
    have h2 : ∑ x₁, ∑ x₂, (if x₁ = x then J x₁ x₂ * φ x₂ else 0) = ∑ y, J x y * φ y := by
      rw [Fintype.sum_eq_single x]
      · simp
      · intro x' hx'; simp [hx']
    rw [this]; push_cast; ring_nf; rw [h2]; ring

theorem hasLineDerivAt_wt (J : ι → ι → ℝ) (hJ : ∀ x y, J x y = J y x) (a b H : ℝ)
    (φ : ι → ℝ) (x : ι) :
    HasLineDerivAt ℝ (wt J a b H) (dact J a b H x φ * wt J a b H φ) φ (Pi.single x 1) := by
  have h := hasLineDerivAt_act J hJ a b H φ x
  unfold HasLineDerivAt at h ⊢
  unfold wt
  convert h.exp using 1
  simp [mul_comm]

theorem growth_congr {F G : (ι → ℝ) → ℝ} (h : ∀ φ, F φ = G φ) (hF : Growth F) : Growth G := by
  have : F = G := funext h
  exact this ▸ hF

theorem growth_dact (J : ι → ι → ℝ) (a b H : ℝ) (x : ι) : Growth (dact J a b H x) := by
  refine growth_congr (fun φ => ?_) (growth_add (growth_add (growth_add
    (growth_sum univ fun y _ => growth_smul (J x y) (growth_coord y))
    (growth_const H)) (growth_smul (-(2 * a)) (growth_coord x)))
    (growth_smul (-(4 * b)) (growth_pow (growth_coord x) 3)))
  simp only [dact]; ring

theorem hasLineDerivAt_const' (c : ℝ) (φ v : ι → ℝ) :
    HasLineDerivAt ℝ (fun _ : ι → ℝ => c) 0 φ v := by
  unfold HasLineDerivAt; exact hasDerivAt_const _ _

/-- Integration by parts: ⟨∂_x act⟩ = 0, i.e. ∫ ∂_x w = 0. -/
theorem integral_dact_wt (J : ι → ι → ℝ) (hJ : ∀ x y, J x y = J y x) (a : ℝ) {b : ℝ}
    (hb : 0 < b) (H : ℝ) (x : ι) : ∫ φ, dact J a b H x φ * wt J a b H φ = 0 := by
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (ι → ℝ))) (f := fun _ => (1 : ℝ)) (f' := fun _ => 0)
    (g := wt J a b H) (g' := fun φ => dact J a b H x φ * wt J a b H φ)
    (v := (Pi.single x (1 : ℝ) : ι → ℝ)) (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simp) (by simpa using integrable_growth J a hb H (growth_dact J a b H x))
    (by simpa using integrable_wt J a hb H)
    (fun φ _ => hasLineDerivAt_const' 1 φ _) (fun φ _ => hasLineDerivAt_wt J hJ a b H φ x)
  simpa using key

/-- **S1 (EOM), general finite graph with symmetric couplings J**:
⟨Σ_y J_xy φ_y⟩ − 2a⟨φ_x⟩ − 4b⟨φ_x³⟩ + H = 0. -/
theorem eom (J : ι → ι → ℝ) (hJ : ∀ x y, J x y = J y x) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (H : ℝ) (x : ι) :
    ex J a b H (fun φ => ∑ y, J x y * φ y) - 2 * a * ex J a b H (fun φ => φ x)
      - 4 * b * ex J a b H (fun φ => φ x ^ 3) + H = 0 := by
  have I := integral_dact_wt J hJ a hb H x
  have iA := integrable_growth J a hb H (growth_sum univ fun y _ => growth_smul (J x y) (growth_coord y))
  have iH := (integrable_wt J a hb H).const_mul H
  have iB := (integrable_growth J a hb H (growth_coord x)).const_mul (2 * a)
  have iC := (integrable_growth J a hb H (growth_pow (growth_coord x) 3)).const_mul (4 * b)
  have e : (fun φ => dact J a b H x φ * wt J a b H φ) = fun φ =>
      (((∑ y, J x y * φ y) * wt J a b H φ + H * wt J a b H φ)
        - 2 * a * (φ x * wt J a b H φ)) - 4 * b * (φ x ^ 3 * wt J a b H φ) := by
    funext φ; simp only [dact]; ring
  set w := wt J a b H with hw
  have h1 : (∫ φ, (((∑ y, J x y * φ y) * w φ + H * w φ) - 2 * a * (φ x * w φ))
      - 4 * b * (φ x ^ 3 * w φ)) = (∫ φ, ((∑ y, J x y * φ y) * w φ + H * w φ)
      - 2 * a * (φ x * w φ)) - ∫ φ, 4 * b * (φ x ^ 3 * w φ) :=
    integral_sub ((iA.add iH).sub iB) iC
  have h2 : (∫ φ, ((∑ y, J x y * φ y) * w φ + H * w φ) - 2 * a * (φ x * w φ))
      = (∫ φ, ((∑ y, J x y * φ y) * w φ + H * w φ)) - ∫ φ, 2 * a * (φ x * w φ) :=
    integral_sub (iA.add iH) iB
  have h3 : (∫ φ, ((∑ y, J x y * φ y) * w φ + H * w φ))
      = (∫ φ, (∑ y, J x y * φ y) * w φ) + ∫ φ, H * w φ := integral_add iA iH
  rw [e, h1, h2, h3, integral_const_mul, integral_const_mul, integral_const_mul] at I
  have hZ : (∫ φ, w φ) ≠ 0 := (Zf_pos J a hb H).ne'
  have key : ex J a b H (fun φ => ∑ y, J x y * φ y) - 2 * a * ex J a b H (fun φ => φ x)
      - 4 * b * ex J a b H (fun φ => φ x ^ 3) + H = ((((∫ φ, (∑ y, J x y * φ y) * w φ)
      + H * ∫ φ, w φ) - 2 * a * ∫ φ, φ x * w φ) - 4 * b * ∫ φ, φ x ^ 3 * w φ) / ∫ φ, w φ := by
    unfold ex Zf
    rw [← hw]
    field_simp
    try ring
  rw [key, I, zero_div]

/-! ## Linearity of ⟨·⟩ -/

theorem ex_add (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ)
    {O P : (ι → ℝ) → ℝ} (hO : Growth O) (hP : Growth P) :
    ex J a b H (fun φ => O φ + P φ) = ex J a b H O + ex J a b H P := by
  unfold ex; rw [← add_div]; congr 1
  simp_rw [add_mul]
  exact integral_add (integrable_growth J a hb H hO) (integrable_growth J a hb H hP)

theorem ex_const_mul (J : ι → ι → ℝ) (a b H c : ℝ) (O : (ι → ℝ) → ℝ) :
    ex J a b H (fun φ => c * O φ) = c * ex J a b H O := by
  unfold ex; rw [mul_div_assoc']; congr 1
  simp_rw [mul_assoc]; exact integral_const_mul c _

theorem ex_sub (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ)
    {O P : (ι → ℝ) → ℝ} (hO : Growth O) (hP : Growth P) :
    ex J a b H (fun φ => O φ - P φ) = ex J a b H O - ex J a b H P := by
  have h := ex_add J a hb H hO (growth_smul (-1) hP)
  rw [ex_const_mul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  linarith

theorem ex_sum (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) {κ : Type*}
    (s : Finset κ) {O : κ → (ι → ℝ) → ℝ} (hO : ∀ i ∈ s, Growth (O i)) :
    ex J a b H (fun φ => ∑ i ∈ s, O i φ) = ∑ i ∈ s, ex J a b H (O i) := by
  unfold ex; rw [← sum_div]; congr 1
  simp_rw [sum_mul]
  exact integral_finsetSum s fun i hi => integrable_growth J a hb H (hO i hi)

theorem ex_const (J : ι → ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) (H c : ℝ) :
    ex J a b H (fun _ => c) = c := by
  have h := (Zf_pos J a hb H).ne'
  unfold ex; unfold Zf at h ⊢; rw [integral_const_mul]; field_simp

/-! ## Translation invariance (ι an additive group, J translation invariant) -/

section TI
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Translated field (τ_z φ)(y) = φ(y + z). -/
def shift (z : G) (φ : G → ℝ) : G → ℝ := fun y => φ (y + z)

theorem act_shift (J : G → G → ℝ) (hJ : ∀ x y z, J (x + z) (y + z) = J x y) (a b H : ℝ)
    (z : G) (φ : G → ℝ) : act J a b H (shift z φ) = act J a b H φ := by
  have e1 : ∀ f : G → ℝ, ∑ x, f (x + z) = ∑ x, f x := fun f => Fintype.sum_equiv (Equiv.addRight z) _ _ (fun _ => rfl)
  have h1 : ∑ x, ∑ y, J x y * φ (x + z) * φ (y + z) = ∑ x, ∑ y, J x y * φ x * φ y := by
    calc _ = ∑ x, ∑ y, J (x + z) (y + z) * φ (x + z) * φ (y + z) := by simp only [hJ]
      _ = ∑ x, ∑ y, J (x + z) y * φ (x + z) * φ y :=
          sum_congr rfl fun x _ => e1 (fun y => J (x + z) y * φ (x + z) * φ y)
      _ = _ := e1 (fun x => ∑ y, J x y * φ x * φ y)
  have h2 : ∑ x, φ (x + z) = ∑ x, φ x := e1 φ
  have h3 : ∑ x, (a * φ (x + z) ^ 2 + b * φ (x + z) ^ 4) = ∑ x, (a * φ x ^ 2 + b * φ x ^ 4) :=
    e1 (fun x => a * φ x ^ 2 + b * φ x ^ 4)
  unfold act shift
  rw [h1, h2, h3]

theorem measurePreserving_shift (z : G) :
    MeasurePreserving (shift z : (G → ℝ) → G → ℝ) volume volume := by
  have h := volume_preserving_arrowCongr' (α₁ := G) (Equiv.addRight z).symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  have e : ⇑(MeasurableEquiv.arrowCongr' (Equiv.addRight z).symm (MeasurableEquiv.refl ℝ))
      = shift z := by
    funext φ y; rfl
  rwa [e] at h

/-- Translation invariance of ⟨·⟩: ⟨F ∘ τ_z⟩ = ⟨F⟩. -/
theorem ex_shift (J : G → G → ℝ) (hJ : ∀ x y z, J (x + z) (y + z) = J x y) (a b H : ℝ)
    (z : G) (F : (G → ℝ) → ℝ) : ex J a b H (fun φ => F (shift z φ)) = ex J a b H F := by
  unfold ex; congr 1
  have h := (volume_preserving_arrowCongr' (α₁ := G) (Equiv.addRight z).symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)).integral_comp'
    (fun φ => F φ * wt J a b H φ)
  have e : ∀ φ, (MeasurableEquiv.arrowCongr' (Equiv.addRight z).symm (MeasurableEquiv.refl ℝ))
      φ = shift z φ := fun φ => by funext y; rfl
  simp only [e] at h
  rw [← h]; congr 1; funext φ
  simp only [wt, act_shift J hJ]

/-- ⟨φ_y⟩ = ⟨φ_0⟩. -/
theorem ex_coord (J : G → G → ℝ) (hJ : ∀ x y z, J (x + z) (y + z) = J x y) (a b H : ℝ)
    (y : G) (F : ℝ → ℝ) : ex J a b H (fun φ => F (φ y)) = ex J a b H (fun φ => F (φ 0)) := by
  rw [← ex_shift J hJ a b H y (fun φ => F (φ 0))]
  simp [shift]

/-- **S1, translation-invariant form**: with d = Σ_y J_0y (the number of neighbours for the
nearest-neighbour torus), (d − 2a)⟨φ_0⟩ − 4b⟨φ_0³⟩ + H = 0. -/
theorem eom_ti (J : G → G → ℝ) (hJs : ∀ x y, J x y = J y x)
    (hJ : ∀ x y z, J (x + z) (y + z) = J x y) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) :
    ((∑ y, J 0 y) - 2 * a) * ex J a b H (fun φ => φ 0)
      - 4 * b * ex J a b H (fun φ => φ 0 ^ 3) + H = 0 := by
  have h := eom J hJs a hb H 0
  rw [ex_sum J a hb H univ fun y _ => growth_smul (J 0 y) (growth_coord y)] at h
  simp only [ex_const_mul] at h
  have e : ∀ y, ex J a b H (fun φ => φ y) = ex J a b H (fun φ => φ 0) := fun y =>
    ex_coord J hJ a b H y id
  simp only [e, ← sum_mul] at h
  linarith

end TI

end T2bTorus

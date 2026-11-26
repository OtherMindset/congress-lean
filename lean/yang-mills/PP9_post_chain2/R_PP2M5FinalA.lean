import LongTable.R_PP2DoubleIBPD
import LongTable.R_PP2GreenLpB
import LongTable.P_mwwlq07a_c2sp8h

/-!
Part A of PP2M5Final (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2M5Final.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5, I2 (the
correction bound) and the M5 conclusions, CONDITIONAL on the region Nelson bound (G4) and two
free-field facts, each a named hypothesis below. Namespace `PP2M5Final`; ε = `spacing n`,
B = physBall n k x l, C_B = `dib_GB` = ε⁻² regionGreen B, ⟨·⟩⁰_B = `dib_ex0 (rg_scaledOp B)` (the
free Dirichlet measure of B, = the λ = 0 region measure by `rg_qweight_zeroExt`), ⟨·⟩_λ =
`dib_rexpect` = `dib_ex (rg_scaledOp B) ε² freeVar λ` (`dib_rexpect_eq`), Wick order at freeVar.

HYPOTHESES (the only unproved inputs of this file; each is uniform in n, k and the centre x).
* `NelsonRegionHyp m₀ l` (G4): ∃ N, ∀ n k x, ⟨e^{−2V_B}⟩⁰_B ≤ N, V_B = `m5f_V` = ε² Σ_{z∈B} :ψ_z⁴:.
* `WickDefectHyp m₀ l` (F4, squared): ∃ D, ∀ n k x, ε² Σ_{z∈B} (freeVar − C_B(z,z))² ≤ D.
* `WickL2Hyp m₀ l` (free L² Wick moments): ∃ K ≥ 0, ∀ n k x (x ∈ B), ∀ Γ ≥ 0, ∀ g : B → ℝ with
  0 ≤ g ≤ Γ: ⟨Y_g²⟩⁰_B ≤ (ΓK)² and ⟨(F₁F_g)²⟩⁰_B ≤ (ΓK)², where Y_g = `m5f_Y` =
  ε² Σ_z g(z) C_B(x,z) :ψ_z²:, F₁ = ε² Σ_z C_B(x,z) :ψ_z³:, F_g = ε² Σ_z g(z) :ψ_z³: (`m5f_FF` = F₁F_g).
  (Mathematically: G3 gives ⟨Y_g²⟩⁰ explicitly in C_B and δ = freeVar − C_B(z,z); ⟨(F₁F_g)²⟩⁰ ≤
  ‖F₁‖₄²‖F_g‖₄² via Hölder and hypercontractivity / the degree-≤ 12 Wick table; both reduce to the
  F3/F4 L^p bounds. None of this is formalized here.)
For `phiFourTwoGapV3_of_hyps` additionally: non-Gaussianity of the limit points for small λ
(`IsNonGaussian`) and `SchwartzSeparable`, as in `PP2Target.phiFourTwoGapV3_of_M5`.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
Generic (ι finite, A positive definite, ρ_A = gaussWeight A, E = `dib_E e c λ` = e^{−λV}):
* `m5f_Grow` (|h| ≤ K e^{aΣ|φ|}) with closure lemmas, `m5f_int_W`, `m5f_int_0` (integrability),
  `m5f_ex_sum`, `m5f_ex_const_mul` (linearity of ⟨·⟩_λ).
* `m5f_schwarz`: ∫X²ρ ≤ a²Z, ∫Y²ρ ≤ b²Z ⟹ |∫XYρ| ≤ abZ (AM–GM with a free parameter).
* `m5f_abs_ex_le`: ⟨X²⟩₀ ≤ a², ⟨E²⟩₀ ≤ b², ⟨E⟩₀ ≥ z > 0 ⟹ |⟨X⟩_λ| ≤ ab/z.
* `m5f_jensen`: ⟨e^{−λV}⟩₀ ≥ e^{−λ⟨V⟩₀} (tangent line of exp); `m5f_ex0_V` (G3):
  ⟨V⟩₀ = e Σ_z 3(c − A⁻¹(z,z))²; `m5f_E2_le`: 0 ≤ λ ≤ 1 ⟹ ⟨e^{−2λV}⟩₀ ≤ 1 + ⟨e^{−2V}⟩₀.
Region:
* `m5f_T1_eq`: 12λε²Σ_z g(z)C_B(x,z)⟨:ψ_z²:⟩_λ = 12λ⟨Y_g⟩_λ.
* **`m5f_correction_le` (I2)**: m₀ ≠ 0, the three hypotheses at (m₀, l) ⟹ ∃ K ≥ 0, for all n, k, x,
  0 ≤ λ ≤ 1, Γ ≥ 0, 0 ≤ g ≤ Γ:
  |12λε²Σ_z g(z)C_B(x,z)⟨:ψ_z²:⟩_λ| + |16λ²⟨F₁F_g⟩_λ| ≤ λΓK
  (K = 28 K_W √(1 + max N 0) e^{3 max D 0}).
Conclusions:
* `m5f_regionGreen_rowSum_le` (Σ_u regionGreen(z,u) ≤ m₀⁻²), `m5f_gExit_eq`/`m5f_gExit_bounds`
  (t(u) = Σ_{v∉B} bondJ u v: g = C_B t is the free exit weight, 0 ≤ g ≤ 1), `m5f_gSus_eq`/
  `m5f_gSus_bounds` (t ≡ ε²: 0 ≤ g ≤ m₀⁻²).
* `m5f_boundary_le`: ∃ K ≥ 0, ∀ λ ∈ [0,1], SmallBoundarySum m₀ λ l (2/cosh(κl) + λK) ∧
  RegionSusceptibility m₀ λ l (m₀⁻² + λ m₀⁻² K) (I1 `dib_double_ibp_region'` + I2 + F2).
* **`m5Inputs_of`**: ∀ m₀ > 0, ∃ l ≥ 0, ∃ λ₀ > 0, ∃ A ≥ 0, ∀ λ ∈ [0, λ₀),
  SmallBoundarySum m₀ λ l (3/4) ∧ RegionSusceptibility m₀ λ l A
  (l = log 8/κ, λ₀ = min(1, 1/(4(K+1))), A = m₀⁻²(1+K)); `m5f_M5Inputs` (the `M5Inputs` form).
* **`phiFourTwoGapV3_of_hyps`**: NelsonRegionHyp, WickDefectHyp, WickL2Hyp (all m₀ > 0, l ≥ 0),
  non-Gaussianity for small λ, SchwartzSeparable ⟹ PhiFourTwoGapV3.

NOT formalized here: the three hypotheses above (G4; F4 in squared-sum form; the L² Wick moments,
which need G3 for the second moment of Y_g and a fourth-moment/hypercontractive bound for F₁, F_g),
non-Gaussianity, SchwartzSeparable.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Matrix Finset PP2Target PP2DoubleIBP

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

noncomputable section

namespace PP2M5Final

/-! ## Generic finite-dimensional facts (any finite index set ι) -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exponential growth in Σ|φ|: |h φ| ≤ K e^{a Σ|φ|}. -/
def m5f_Grow (h : (ι → ℝ) → ℝ) : Prop :=
  ∃ K a : ℝ, 0 ≤ K ∧ 0 ≤ a ∧ ∀ φ, |h φ| ≤ K * Real.exp (a * ∑ i, |φ i|)

theorem m5f_exp_mono {a b : ℝ} (hab : a ≤ b) (φ : ι → ℝ) :
    Real.exp (a * ∑ i, |φ i|) ≤ Real.exp (b * ∑ i, |φ i|) :=
  Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hab (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem m5f_grow_const (r : ℝ) : m5f_Grow (ι := ι) (fun _ => r) :=
  ⟨|r|, 0, abs_nonneg _, le_rfl, fun φ => by simp⟩

theorem m5f_grow_wick (c : ℝ) {m : ℕ} (hm : m ≤ 4) (z : ι) :
    m5f_Grow (fun φ : ι → ℝ => wickPow c m (φ z)) := by
  obtain ⟨K, hK, h⟩ := dib_wick_bnd (ι := ι) c hm
  exact ⟨K, 1, hK, zero_le_one, fun φ => by rw [one_mul]; exact h φ z⟩

theorem m5f_grow_add {f g : (ι → ℝ) → ℝ} (hf : m5f_Grow f) (hg : m5f_Grow g) :
    m5f_Grow (fun φ => f φ + g φ) := by
  obtain ⟨K₁, a₁, hK₁, ha₁, h₁⟩ := hf
  obtain ⟨K₂, a₂, hK₂, ha₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, a₁ + a₂, add_nonneg hK₁ hK₂, add_nonneg ha₁ ha₂, fun φ => ?_⟩
  have e1 := m5f_exp_mono (le_add_of_nonneg_right ha₂ : a₁ ≤ a₁ + a₂) φ
  have e2 := m5f_exp_mono (le_add_of_nonneg_left ha₁ : a₂ ≤ a₁ + a₂) φ
  rw [add_mul]
  exact (abs_add_le _ _).trans (add_le_add ((h₁ φ).trans (mul_le_mul_of_nonneg_left e1 hK₁))
    ((h₂ φ).trans (mul_le_mul_of_nonneg_left e2 hK₂)))

theorem m5f_grow_mul {f g : (ι → ℝ) → ℝ} (hf : m5f_Grow f) (hg : m5f_Grow g) :
    m5f_Grow (fun φ => f φ * g φ) := by
  obtain ⟨K₁, a₁, hK₁, ha₁, h₁⟩ := hf
  obtain ⟨K₂, a₂, hK₂, ha₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, a₁ + a₂, mul_nonneg hK₁ hK₂, add_nonneg ha₁ ha₂, fun φ => ?_⟩
  rw [abs_mul, add_mul, Real.exp_add]
  calc |f φ| * |g φ| ≤ (K₁ * Real.exp (a₁ * ∑ i, |φ i|)) * (K₂ * Real.exp (a₂ * ∑ i, |φ i|)) :=
        mul_le_mul (h₁ φ) (h₂ φ) (abs_nonneg _) (le_trans (abs_nonneg _) (h₁ φ))
    _ = _ := by ring

theorem m5f_grow_sum {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ}
    (hf : ∀ j ∈ s, m5f_Grow (f j)) : m5f_Grow (fun φ => ∑ j ∈ s, f j φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using m5f_grow_const (ι := ι) 0
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact m5f_grow_add (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem m5f_grow_sq {f : (ι → ℝ) → ℝ} (hf : m5f_Grow f) : m5f_Grow (fun φ => f φ ^ 2) := by
  simpa [sq] using m5f_grow_mul hf hf

theorem m5f_grow_E {e : ℝ} (he : 0 ≤ e) (c : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    m5f_Grow (dib_E (ι := ι) e c lam) :=
  ⟨dib_M ι e c lam, 0, (Real.exp_pos _).le, le_rfl, fun φ => by
    rw [zero_mul, Real.exp_zero, mul_one, abs_of_pos (dib_E_pos e c lam φ)]
    exact dib_E_le he c hlam φ⟩

/-- Integrability against the interacting weight W. -/
theorem m5f_int_W {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) {h : (ι → ℝ) → ℝ} (hc : Continuous h) (hg : m5f_Grow h) :
    Integrable (fun φ => h φ * dib_W A e c lam φ) := by
  obtain ⟨K, a, hK, _, hle⟩ := hg
  refine PP2GaussIBP.integrable_of_le_expAbs hA
    (hc.mul (dib_continuous_W A e c lam)).aestronglyMeasurable
    (K * dib_M ι e c lam) a (fun φ => ?_)
  have hρ := PP2GaussIBP.gaussWeight_nonneg A φ
  rw [dib_W, abs_mul, abs_of_nonneg (mul_nonneg hρ (dib_E_pos _ _ _ φ).le)]
  calc |h φ| * (PP2GaussIBP.gaussWeight A φ * dib_E e c lam φ)
      ≤ (K * Real.exp (a * ∑ j, |φ j|)) * (PP2GaussIBP.gaussWeight A φ * dib_M ι e c lam) :=
        mul_le_mul (hle φ) (mul_le_mul_of_nonneg_left (dib_E_le he c hlam φ) hρ)
          (mul_nonneg hρ (dib_E_pos _ _ _ φ).le) (le_trans (abs_nonneg _) (hle φ))
    _ = _ := by ring

/-- Integrability against the free Gaussian weight. -/
theorem m5f_int_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) {h : (ι → ℝ) → ℝ} (hc : Continuous h)
    (hg : m5f_Grow h) : Integrable (fun φ => h φ * PP2GaussIBP.gaussWeight A φ) := by
  simpa [dib_W_zero] using m5f_int_W hA le_rfl 0 le_rfl (e := 0) (lam := 0) hc hg

/-- Linearity of the interacting expectation in finite sums. -/
theorem m5f_ex_sum (A : Matrix ι ι ℝ) (e c lam r : ℝ) {κ : Type*} [Fintype κ]
    {f : κ → (ι → ℝ) → ℝ} (hf : ∀ z, Integrable (fun φ => f z φ * dib_W A e c lam φ)) :
    dib_ex A e c lam (fun φ => r * ∑ z, f z φ) = r * ∑ z, dib_ex A e c lam (f z) := by
  unfold dib_ex
  have h1 : ∀ φ, (r * ∑ z, f z φ) * dib_W A e c lam φ =
      r * ∑ z, f z φ * dib_W A e c lam φ := fun φ => by rw [mul_assoc, Finset.sum_mul]
  simp_rw [h1]
  rw [integral_const_mul, integral_finsetSum _ (fun z _ => hf z), mul_div_assoc,
    Finset.sum_div]

theorem m5f_ex_const_mul (A : Matrix ι ι ℝ) (e c lam r : ℝ) (f : (ι → ℝ) → ℝ) :
    dib_ex A e c lam (fun φ => r * f φ) = r * dib_ex A e c lam f := by
  unfold dib_ex
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]

/-- **Schwarz with a free parameter** (AM–GM form, no L^p spaces): if ∫X²ρ ≤ a²Z and
∫Y²ρ ≤ b²Z then |∫XYρ| ≤ abZ. -/
theorem m5f_schwarz {ρ X Y : (ι → ℝ) → ℝ} (hρ : ∀ φ, 0 ≤ ρ φ)
    (hXY : Integrable (fun φ => X φ * Y φ * ρ φ)) (hX2 : Integrable (fun φ => X φ ^ 2 * ρ φ))
    (hY2 : Integrable (fun φ => Y φ ^ 2 * ρ φ)) {a b Z : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hZ : 0 ≤ Z) (hXa : ∫ φ, X φ ^ 2 * ρ φ ≤ a ^ 2 * Z) (hYb : ∫ φ, Y φ ^ 2 * ρ φ ≤ b ^ 2 * Z) :
    |∫ φ, X φ * Y φ * ρ φ| ≤ a * b * Z := by
  have key : ∀ t : ℝ, 0 < t → |∫ φ, X φ * Y φ * ρ φ| ≤ (t * (a ^ 2 * Z) + b ^ 2 * Z / t) / 2 := by
    intro t ht
    have hpt : ∀ φ, |X φ * Y φ * ρ φ| ≤ (t * (X φ ^ 2 * ρ φ) + Y φ ^ 2 * ρ φ / t) / 2 := by
      intro φ
      rw [abs_mul, abs_mul, abs_of_nonneg (hρ φ)]
      have h1 : |X φ| * |Y φ| ≤ (t * X φ ^ 2 + Y φ ^ 2 / t) / 2 := by
        have e : (t * X φ ^ 2 + Y φ ^ 2 / t) / 2 = (t ^ 2 * X φ ^ 2 + Y φ ^ 2) / (2 * t) := by
          field_simp
        rw [e, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (t * |X φ| - |Y φ|), sq_abs (X φ), sq_abs (Y φ)]
      have e2 : (t * (X φ ^ 2 * ρ φ) + Y φ ^ 2 * ρ φ / t) / 2 =
          ((t * X φ ^ 2 + Y φ ^ 2 / t) / 2) * ρ φ := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_right h1 (hρ φ)
    have hint : Integrable (fun φ => (t * (X φ ^ 2 * ρ φ) + Y φ ^ 2 * ρ φ / t) / 2) :=
      ((hX2.const_mul t).add (hY2.div_const t)).div_const 2
    calc |∫ φ, X φ * Y φ * ρ φ| ≤ ∫ φ, |X φ * Y φ * ρ φ| := abs_integral_le_integral_abs
      _ ≤ ∫ φ, (t * (X φ ^ 2 * ρ φ) + Y φ ^ 2 * ρ φ / t) / 2 :=
          integral_mono hXY.abs hint hpt
      _ = (t * (∫ φ, X φ ^ 2 * ρ φ) + (∫ φ, Y φ ^ 2 * ρ φ) / t) / 2 := by
          rw [integral_div, integral_add (hX2.const_mul t) (hY2.div_const t), integral_const_mul,
            integral_div]
      _ ≤ _ := by
          have := div_le_div_of_nonneg_right hYb ht.le
          nlinarith [mul_le_mul_of_nonneg_left hXa ht.le]
  have hη : ∀ η : ℝ, 0 < η → |∫ φ, X φ * Y φ * ρ φ| ≤ (a + η) * b * Z := by
    intro η hη
    have hp : 0 < a + η := by linarith
    have ht : 0 < b / (a + η) := div_pos hb hp
    refine (key _ ht).trans ?_
    have h1 : b / (a + η) * a ^ 2 ≤ b * (a + η) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hp]
      have : a ^ 2 ≤ (a + η) ^ 2 := by nlinarith
      nlinarith
    have h2 : b ^ 2 * Z / (b / (a + η)) = b * (a + η) * Z := by
      field_simp
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_right h1 hZ]
  by_contra hcon
  push Not at hcon
  rcases (mul_nonneg hb.le hZ).eq_or_lt with h0 | h0
  · have := hη 1 one_pos
    have e : (a + 1) * b * Z = a * b * Z := by
      rw [mul_assoc, mul_assoc, ← h0]; ring
    linarith
  · set d := |∫ φ, X φ * Y φ * ρ φ| - a * b * Z with hd
    have hd0 : 0 < d := by linarith
    have := hη (d / (2 * (b * Z))) (by positivity)
    have hZ0 : Z ≠ 0 := by rintro rfl; simp at h0
    have e : (a + d / (2 * (b * Z))) * b * Z = a * b * Z + d / 2 := by
      field_simp
    linarith

/-- **Normalised Schwarz in the free measure:** if ⟨X²⟩₀ ≤ a², ⟨E²⟩₀ ≤ b² and ⟨E⟩₀ ≥ z > 0 then
|⟨X⟩_λ| = |⟨X E⟩₀| / ⟨E⟩₀ ≤ a b / z. -/
theorem m5f_abs_ex_le {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) {X : (ι → ℝ) → ℝ} (hXc : Continuous X) (hXg : m5f_Grow X)
    {a b z : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hz : 0 < z)
    (hX2 : dib_ex0 A (fun φ => X φ ^ 2) ≤ a ^ 2)
    (hE2 : dib_ex0 A (fun φ => dib_E e c lam φ ^ 2) ≤ b ^ 2)
    (hE1 : z ≤ dib_ex0 A (dib_E e c lam)) :
    |dib_ex A e c lam X| ≤ a * b / z := by
  have hZ0 := dib_integral_gauss_pos hA
  have hρ : ∀ φ, 0 ≤ PP2GaussIBP.gaussWeight A φ := PP2GaussIBP.gaussWeight_nonneg A
  have hEc := dib_continuous_E (ι := ι) e c lam
  have hEg := m5f_grow_E (ι := ι) he c hlam
  have hXY : Integrable (fun φ => X φ * dib_E e c lam φ * PP2GaussIBP.gaussWeight A φ) := by
    refine (m5f_int_W hA he c hlam hXc hXg).congr (Filter.Eventually.of_forall fun φ => ?_)
    simp only [dib_W]; ring
  have hX2i : Integrable (fun φ => X φ ^ 2 * PP2GaussIBP.gaussWeight A φ) :=
    m5f_int_0 hA (hXc.pow 2) (m5f_grow_sq hXg)
  have hE2i : Integrable (fun φ => dib_E e c lam φ ^ 2 * PP2GaussIBP.gaussWeight A φ) :=
    m5f_int_0 hA (hEc.pow 2) (m5f_grow_sq hEg)
  have hXa : ∫ φ, X φ ^ 2 * PP2GaussIBP.gaussWeight A φ ≤
      a ^ 2 * ∫ φ, PP2GaussIBP.gaussWeight A φ := by
    unfold dib_ex0 at hX2; rwa [div_le_iff₀ hZ0] at hX2
  have hEb : ∫ φ, dib_E e c lam φ ^ 2 * PP2GaussIBP.gaussWeight A φ ≤
      b ^ 2 * ∫ φ, PP2GaussIBP.gaussWeight A φ := by
    unfold dib_ex0 at hE2; rwa [div_le_iff₀ hZ0] at hE2
  have hS := m5f_schwarz hρ hXY hX2i hE2i ha hb hZ0.le hXa hEb
  have hWeq : (∫ φ, dib_W A e c lam φ) = ∫ φ, dib_E e c lam φ * PP2GaussIBP.gaussWeight A φ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only [dib_W]; ring
  have hden : z * ∫ φ, PP2GaussIBP.gaussWeight A φ ≤ ∫ φ, dib_W A e c lam φ := by
    unfold dib_ex0 at hE1; rw [le_div_iff₀ hZ0] at hE1
    rw [hWeq]; exact hE1
  have hnum : ∫ φ, X φ * dib_W A e c lam φ =
      ∫ φ, X φ * dib_E e c lam φ * PP2GaussIBP.gaussWeight A φ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only [dib_W]; ring
  have hWpos := dib_integral_W_pos hA he c hlam
  unfold dib_ex
  rw [hnum, abs_div, abs_of_pos hWpos, div_le_div_iff₀ hWpos hz]
  calc |∫ φ, X φ * dib_E e c lam φ * PP2GaussIBP.gaussWeight A φ| * z
      ≤ (a * b * ∫ φ, PP2GaussIBP.gaussWeight A φ) * z := mul_le_mul_of_nonneg_right hS hz.le
    _ = a * b * (z * ∫ φ, PP2GaussIBP.gaussWeight A φ) := by ring
    _ ≤ a * b * ∫ φ, dib_W A e c lam φ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem m5f_continuous_V (e c : ℝ) :
    Continuous (fun φ : ι → ℝ => e * ∑ z, wickPow c 4 (φ z)) := by
  unfold wickPow; fun_prop

theorem m5f_grow_V (e c : ℝ) : m5f_Grow (fun φ : ι → ℝ => e * ∑ z, wickPow c 4 (φ z)) :=
  m5f_grow_mul (m5f_grow_const e)
    (m5f_grow_sum _ fun z _ => m5f_grow_wick c (by norm_num) z)

/-- **Jensen (tangent-line form):** ⟨e^{−λV}⟩₀ ≥ e^{−λ⟨V⟩₀}, V = e Σ_z :φ_z⁴:_c. -/
theorem m5f_jensen {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Real.exp (-(lam * dib_ex0 A (fun φ => e * ∑ z, wickPow c 4 (φ z)))) ≤
      dib_ex0 A (dib_E e c lam) := by
  have hZ0 := dib_integral_gauss_pos hA
  set v := dib_ex0 A (fun φ => e * ∑ z, wickPow c 4 (φ z)) with hv
  have hVi := m5f_int_0 hA (m5f_continuous_V e c) (m5f_grow_V (ι := ι) e c)
  have hEi := m5f_int_0 hA (dib_continuous_E e c lam) (m5f_grow_E (ι := ι) he c hlam)
  have hρi : Integrable (fun φ => PP2GaussIBP.gaussWeight A φ) := by
    simpa using m5f_int_0 hA continuous_const (m5f_grow_const (ι := ι) 1)
  set C := Real.exp (-(lam * v)) with hC
  have hpt : ∀ φ, C * (1 + lam * v) * PP2GaussIBP.gaussWeight A φ -
      C * lam * ((e * ∑ z, wickPow c 4 (φ z)) * PP2GaussIBP.gaussWeight A φ) ≤
        dib_E e c lam φ * PP2GaussIBP.gaussWeight A φ := by
    intro φ
    have h1 := Real.add_one_le_exp (-(lam * ((e * ∑ z, wickPow c 4 (φ z)) - v)))
    have h2 : dib_E e c lam φ = C * Real.exp (-(lam * ((e * ∑ z, wickPow c 4 (φ z)) - v))) := by
      rw [hC, ← Real.exp_add]; unfold dib_E; congr 1; ring
    rw [h2]
    have hρ := PP2GaussIBP.gaussWeight_nonneg A φ
    have hev : 0 ≤ C := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hev hρ)
    nlinarith
  have hint : ∫ φ, (C * (1 + lam * v) * PP2GaussIBP.gaussWeight A φ -
      C * lam * ((e * ∑ z, wickPow c 4 (φ z)) * PP2GaussIBP.gaussWeight A φ)) ≤
        ∫ φ, dib_E e c lam φ * PP2GaussIBP.gaussWeight A φ :=
    integral_mono ((hρi.const_mul _).sub (hVi.const_mul _)) hEi hpt
  rw [integral_sub (hρi.const_mul _) (hVi.const_mul _), integral_const_mul,
    integral_const_mul] at hint
  have hVv : ∫ φ, (e * ∑ z, wickPow c 4 (φ z)) * PP2GaussIBP.gaussWeight A φ =
      v * ∫ φ, PP2GaussIBP.gaussWeight A φ := by
    rw [hv]; unfold dib_ex0; rw [div_mul_cancel₀ _ hZ0.ne']
  rw [hVv] at hint
  unfold dib_ex0
  rw [le_div_iff₀ hZ0]
  have e1 : C * (1 + lam * v) * (∫ φ, PP2GaussIBP.gaussWeight A φ) -
      C * lam * (v * ∫ φ, PP2GaussIBP.gaussWeight A φ) = C * ∫ φ, PP2GaussIBP.gaussWeight A φ := by
    ring
  linarith

/-- G3 applied to the potential: ⟨V⟩₀ = e Σ_z 3 (c − A⁻¹(z,z))². -/
theorem m5f_ex0_V {A : Matrix ι ι ℝ} (hA : A.PosDef) (e c : ℝ) :
    dib_ex0 A (fun φ => e * ∑ z, wickPow c 4 (φ z)) = e * ∑ z, 3 * (c - A⁻¹ z z) ^ 2 := by
  rw [← dib_ex_zero A 0 c]
  rw [m5f_ex_sum A 0 c 0 e (f := fun z φ => wickPow c 4 (φ z)) (fun z =>
    m5f_int_W hA le_rfl c le_rfl ((dib_continuous_wick c 4).comp (continuous_apply z))
      (m5f_grow_wick c (by norm_num) z))]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [dib_ex_zero, ← dib_WW_4_0 hA c z z]
  unfold dib_WW
  congr 1
  funext φ
  rw [wickPow_zero', mul_one]

/-- e^{−2λV} ≤ 1 + e^{−2V} for 0 ≤ λ ≤ 1, integrated: ⟨E_λ²⟩₀ ≤ 1 + ⟨E_2⟩₀. -/
theorem m5f_E2_le {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    dib_ex0 A (fun φ => dib_E e c lam φ ^ 2) ≤ 1 + dib_ex0 A (dib_E e c 2) := by
  have hZ0 := dib_integral_gauss_pos hA
  have hρi : Integrable (fun φ => PP2GaussIBP.gaussWeight A φ) := by
    simpa using m5f_int_0 hA continuous_const (m5f_grow_const (ι := ι) 1)
  have hE2i := m5f_int_0 hA (dib_continuous_E e c 2) (m5f_grow_E (ι := ι) he c zero_le_two)
  have hEi := m5f_int_0 hA ((dib_continuous_E e c lam).pow 2)
    (m5f_grow_sq (m5f_grow_E (ι := ι) he c hl0))
  have hpt : ∀ φ, dib_E e c lam φ ^ 2 * PP2GaussIBP.gaussWeight A φ ≤
      PP2GaussIBP.gaussWeight A φ + dib_E e c 2 φ * PP2GaussIBP.gaussWeight A φ := by
    intro φ
    have hρ := PP2GaussIBP.gaussWeight_nonneg A φ
    set S := e * ∑ z, wickPow c 4 (φ z) with hS
    have h1 : dib_E e c lam φ ^ 2 = Real.exp (-(2 * lam * S)) := by
      rw [sq, dib_E, ← Real.exp_add]; congr 1; ring
    have h2 : dib_E e c 2 φ = Real.exp (-(2 * S)) := rfl
    have key : dib_E e c lam φ ^ 2 ≤ 1 + dib_E e c 2 φ := by
      rw [h1, h2]
      rcases le_total 0 S with hs | hs
      · have : Real.exp (-(2 * lam * S)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith)
        linarith [Real.exp_pos (-(2 * S))]
      · have : Real.exp (-(2 * lam * S)) ≤ Real.exp (-(2 * S)) :=
          Real.exp_le_exp.mpr (by nlinarith)
        linarith
    nlinarith
  unfold dib_ex0
  rw [div_le_iff₀ hZ0, add_mul, one_mul, div_mul_cancel₀ _ hZ0.ne']
  calc ∫ φ, dib_E e c lam φ ^ 2 * PP2GaussIBP.gaussWeight A φ
      ≤ ∫ φ, (PP2GaussIBP.gaussWeight A φ + dib_E e c 2 φ * PP2GaussIBP.gaussWeight A φ) :=
        integral_mono hEi (hρi.add hE2i) hpt
    _ = _ := integral_add hρi hE2i

end Generic

/-! ## The region instance: hypotheses and I2 -/

section Region

variable {n k : ℕ}

/-- The quartic potential of a region, V_B(ψ) = ε² Σ_{z∈B} :ψ_z⁴:_{freeVar}. -/
def m5f_V (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) (ψ : {z // z ∈ B} → ℝ) : ℝ :=
  spacing n ^ 2 * ∑ z, wickPow (freeVar n m₀) 4 (ψ z)

/-- **Hypothesis (G4, region Nelson bound).** ⟨e^{−2V_B}⟩⁰_B ≤ N uniformly in n, k and the centre
x, B = physBall n k x l, ⟨·⟩⁰_B the free Dirichlet measure of B (`dib_ex0 (rg_scaledOp B)`, which is
the λ = 0 region measure of `regionTwoPt` by `rg_qweight_zeroExt`). -/
def NelsonRegionHyp (m₀ l : ℝ) : Prop :=
  ∃ N : ℝ, ∀ (n k : ℕ) (x : DSite n k),
    dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
      (fun ψ => Real.exp (-(2 * m5f_V n k m₀ (physBall n k x l) ψ))) ≤ N

end Region

end PP2M5Final

end

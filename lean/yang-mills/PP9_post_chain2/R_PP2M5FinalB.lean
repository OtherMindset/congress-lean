import LongTable.R_PP2M5FinalA

/-!
Part B of PP2M5Final (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2M5Final.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* `WickDefectHyp m₀ l` (F4, squared): ∃ D, ∀ n k x, ε² Σ_{z∈B} (freeVar − C_B(z,z))² ≤ D.
* `WickL2Hyp m₀ l` (free L² Wick moments): ∃ K ≥ 0, ∀ n k x (x ∈ B), ∀ Γ ≥ 0, ∀ g : B → ℝ with
  0 ≤ g ≤ Γ: ⟨Y_g²⟩⁰_B ≤ (ΓK)² and ⟨(F₁F_g)²⟩⁰_B ≤ (ΓK)², where Y_g = `m5f_Y` =
  ε² Σ_z g(z) C_B(x,z) :ψ_z²:, F₁ = ε² Σ_z C_B(x,z) :ψ_z³:, F_g = ε² Σ_z g(z) :ψ_z³: (`m5f_FF` = F₁F_g).
  (Mathematically: G3 gives ⟨Y_g²⟩⁰ explicitly in C_B and δ = freeVar − C_B(z,z); ⟨(F₁F_g)²⟩⁰ ≤
  ‖F₁‖₄²‖F_g‖₄² via Hölder and hypercontractivity / the degree-≤ 12 Wick table; both reduce to the
  F3/F4 L^p bounds. None of this is formalized here.)
* `m5f_T1_eq`: 12λε²Σ_z g(z)C_B(x,z)⟨:ψ_z²:⟩_λ = 12λ⟨Y_g⟩_λ.
* **`m5f_correction_le` (I2)**: m₀ ≠ 0, the three hypotheses at (m₀, l) ⟹ ∃ K ≥ 0, for all n, k, x,
  0 ≤ λ ≤ 1, Γ ≥ 0, 0 ≤ g ≤ Γ:
  |12λε²Σ_z g(z)C_B(x,z)⟨:ψ_z²:⟩_λ| + |16λ²⟨F₁F_g⟩_λ| ≤ λΓK
  (K = 28 K_W √(1 + max N 0) e^{3 max D 0}).
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

section Region

variable {n k : ℕ}

/-- **Hypothesis (F4, squared Wick defect).** ε² Σ_{z∈B} (freeVar − C_B(z,z))² ≤ D uniformly. -/
def WickDefectHyp (m₀ l : ℝ) : Prop :=
  ∃ D : ℝ, ∀ (n k : ℕ) (x : DSite n k),
    spacing n ^ 2 * ∑ z : {z // z ∈ physBall n k x l},
      (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) z z) ^ 2 ≤ D

/-- Y_g = ε² Σ_z g(z) C_B(a,z) :ψ_z²: (the first correction is 12λ⟨Y_g⟩_λ). -/
def m5f_Y (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) (a : {z // z ∈ B})
    (g : {z // z ∈ B} → ℝ) (ψ : {z // z ∈ B} → ℝ) : ℝ :=
  spacing n ^ 2 * ∑ z, g z * dib_GB n k m₀ B a z * wickPow (freeVar n m₀) 2 (ψ z)

/-- F₁ F_g, F₁ = ε² Σ_z C_B(a,z) :ψ_z³:, F_g = ε² Σ_z g(z) :ψ_z³:. -/
def m5f_FF (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) (a : {z // z ∈ B})
    (g : {z // z ∈ B} → ℝ) (ψ : {z // z ∈ B} → ℝ) : ℝ :=
  (spacing n ^ 2 * ∑ z, dib_GB n k m₀ B a z * wickPow (freeVar n m₀) 3 (ψ z)) *
    (spacing n ^ 2 * ∑ z, g z * wickPow (freeVar n m₀) 3 (ψ z))

/-- **Hypothesis (free L² Wick moments).** For 0 ≤ g ≤ Γ on B = physBall n k x l:
⟨Y_g²⟩⁰_B ≤ (ΓK)² and ⟨(F₁F_g)²⟩⁰_B ≤ (ΓK)², uniformly in n, k, x. -/
def WickL2Hyp (m₀ l : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (n k : ℕ) (x : DSite n k) (hx : x ∈ physBall n k x l) (Γ : ℝ)
    (g : {z // z ∈ physBall n k x l} → ℝ), 0 ≤ Γ → (∀ z, 0 ≤ g z ∧ g z ≤ Γ) →
      dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => m5f_Y n k m₀ (physBall n k x l) ⟨x, hx⟩ g ψ ^ 2) ≤ (Γ * K) ^ 2 ∧
      dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => m5f_FF n k m₀ (physBall n k x l) ⟨x, hx⟩ g ψ ^ 2) ≤ (Γ * K) ^ 2

theorem m5f_continuous_Y (m₀ : ℝ) (B : Finset (DSite n k)) (a : {z // z ∈ B})
    (g : {z // z ∈ B} → ℝ) : Continuous (m5f_Y n k m₀ B a g) := by
  unfold m5f_Y wickPow; fun_prop

theorem m5f_continuous_FF (m₀ : ℝ) (B : Finset (DSite n k)) (a : {z // z ∈ B})
    (g : {z // z ∈ B} → ℝ) : Continuous (m5f_FF n k m₀ B a g) := by
  unfold m5f_FF wickPow; fun_prop

theorem m5f_grow_Y (m₀ : ℝ) (B : Finset (DSite n k)) (a : {z // z ∈ B})
    (g : {z // z ∈ B} → ℝ) : m5f_Grow (m5f_Y n k m₀ B a g) :=
  m5f_grow_mul (m5f_grow_const _) (m5f_grow_sum _ fun z _ =>
    m5f_grow_mul (m5f_grow_const _) (m5f_grow_wick _ (by norm_num) z))

theorem m5f_grow_FF (m₀ : ℝ) (B : Finset (DSite n k)) (a : {z // z ∈ B})
    (g : {z // z ∈ B} → ℝ) : m5f_Grow (m5f_FF n k m₀ B a g) :=
  m5f_grow_mul
    (m5f_grow_mul (m5f_grow_const _) (m5f_grow_sum _ fun z _ =>
      m5f_grow_mul (m5f_grow_const _) (m5f_grow_wick _ (by norm_num) z)))
    (m5f_grow_mul (m5f_grow_const _) (m5f_grow_sum _ fun z _ =>
      m5f_grow_mul (m5f_grow_const _) (m5f_grow_wick _ (by norm_num) z)))

/-- The first correction as an expectation: 12λε²Σ_z g(z)C_B(a,z)⟨:ψ_z²:⟩_λ = 12λ⟨Y_g⟩_λ. -/
theorem m5f_T1_eq {m₀ : ℝ} (hm : m₀ ≠ 0) (lam : ℝ) (hlam : 0 ≤ lam) (B : Finset (DSite n k))
    (a : {z // z ∈ B}) (g : {z // z ∈ B} → ℝ) :
    12 * lam * spacing n ^ 2 * ∑ z, g z * dib_GB n k m₀ B a z *
        dib_rexpect n k m₀ lam B (fun ψ => wickPow (freeVar n m₀) 2 (ψ z)) =
      12 * lam * dib_ex (rg_scaledOp n k m₀ B) (spacing n ^ 2) (freeVar n m₀) lam
        (m5f_Y n k m₀ B a g) := by
  have hA := rg_scaledOp_posDef hm B
  have he : 0 ≤ spacing n ^ 2 := by positivity
  unfold m5f_Y
  rw [m5f_ex_sum _ _ _ _ _
    (f := fun z ψ => g z * dib_GB n k m₀ B a z * wickPow (freeVar n m₀) 2 (ψ z))
    (fun z => m5f_int_W hA he _ hlam
      (continuous_const.mul ((dib_continuous_wick _ 2).comp (continuous_apply z)))
      (m5f_grow_mul (m5f_grow_const _) (m5f_grow_wick _ (by norm_num) z)))]
  simp only [m5f_ex_const_mul, dib_rexpect_eq]
  ring

/-- **I2 (correction bound), conditional on the region Nelson bound and the free-field facts.**
For 0 ≤ g ≤ Γ on B = physBall n k x l and 0 ≤ λ ≤ 1:
|12λε²Σ_z g(z)C_B(x,z)⟨:ψ_z²:⟩_λ| + |16λ²⟨F₁F_g⟩_λ| ≤ λΓK(m₀,l). -/
theorem m5f_correction_le {m₀ l : ℝ} (hm : m₀ ≠ 0) (hN : NelsonRegionHyp m₀ l)
    (hD : WickDefectHyp m₀ l) (hW : WickL2Hyp m₀ l) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n k : ℕ) (x : DSite n k) (hx : x ∈ physBall n k x l) (lam Γ : ℝ)
      (g : {z // z ∈ physBall n k x l} → ℝ), 0 ≤ lam → lam ≤ 1 → 0 ≤ Γ →
        (∀ z, 0 ≤ g z ∧ g z ≤ Γ) →
        |12 * lam * spacing n ^ 2 * ∑ z, g z * dib_GB n k m₀ (physBall n k x l) ⟨x, hx⟩ z *
            dib_rexpect n k m₀ lam (physBall n k x l)
              (fun ψ => wickPow (freeVar n m₀) 2 (ψ z))|
          + |16 * lam ^ 2 * dib_rexpect n k m₀ lam (physBall n k x l) (fun ψ =>
              (spacing n ^ 2 * ∑ z, dib_GB n k m₀ (physBall n k x l) ⟨x, hx⟩ z *
                wickPow (freeVar n m₀) 3 (ψ z)) *
              (spacing n ^ 2 * ∑ z, g z * wickPow (freeVar n m₀) 3 (ψ z)))|
          ≤ lam * Γ * K := by
  obtain ⟨N, hN⟩ := hN
  obtain ⟨D, hD⟩ := hD
  obtain ⟨K, hK, hW⟩ := hW
  set b := Real.sqrt (1 + max N 0) with hbdef
  set z0 := Real.exp (-(3 * max D 0)) with hz0def
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hb2 : b ^ 2 = 1 + max N 0 := Real.sq_sqrt (by positivity)
  have hz0 : 0 < z0 := Real.exp_pos _
  refine ⟨28 * K * b / z0, by positivity, ?_⟩
  intro n k x hx lam Γ g hl0 hl1 hΓ hg
  have hA := rg_scaledOp_posDef hm (physBall n k x l)
  have he : 0 ≤ spacing n ^ 2 := by positivity
  -- the two bounds on the interaction factor
  have hE2 : dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
      (fun φ => dib_E (spacing n ^ 2) (freeVar n m₀) lam φ ^ 2) ≤ b ^ 2 := by
    refine (m5f_E2_le hA he _ hl0 hl1).trans ?_
    rw [hb2]
    have := hN n k x
    have h2 : dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l)) (dib_E (spacing n ^ 2) (freeVar n m₀) 2) =
        dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l))
          (fun ψ => Real.exp (-(2 * m5f_V n k m₀ (physBall n k x l) ψ))) := rfl
    rw [h2]
    linarith [le_max_left N 0]
  have hE1 : z0 ≤ dib_ex0 (rg_scaledOp n k m₀ (physBall n k x l)) (dib_E (spacing n ^ 2) (freeVar n m₀) lam) := by
    refine le_trans ?_ (m5f_jensen hA he _ hl0)
    rw [hz0def, m5f_ex0_V hA, ← dib_GB_eq hm]
    apply Real.exp_le_exp.mpr
    have hDx := hD n k x
    have hs : spacing n ^ 2 * ∑ z, 3 * (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) z z) ^ 2 =
        3 * (spacing n ^ 2 * ∑ z, (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) z z) ^ 2) := by
      rw [← Finset.mul_sum]; ring
    rw [hs]
    have h0 : 0 ≤ spacing n ^ 2 * ∑ z, (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) z z) ^ 2 :=
      mul_nonneg he (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h3 : spacing n ^ 2 * ∑ z, (freeVar n m₀ - dib_GB n k m₀ (physBall n k x l) z z) ^ 2 ≤ max D 0 :=
      hDx.trans (le_max_left D 0)
    nlinarith
  have hWx := hW n k x hx Γ g hΓ hg
  have hY := m5f_abs_ex_le hA he (freeVar n m₀) hl0 (m5f_continuous_Y m₀ (physBall n k x l) ⟨x, hx⟩ g)
    (m5f_grow_Y m₀ (physBall n k x l) ⟨x, hx⟩ g) (mul_nonneg hΓ hK) hb hz0 hWx.1 hE2 hE1
  have hF := m5f_abs_ex_le hA he (freeVar n m₀) hl0 (m5f_continuous_FF m₀ (physBall n k x l) ⟨x, hx⟩ g)
    (m5f_grow_FF m₀ (physBall n k x l) ⟨x, hx⟩ g) (mul_nonneg hΓ hK) hb hz0 hWx.2 hE2 hE1
  rw [m5f_T1_eq hm lam hl0 (physBall n k x l) ⟨x, hx⟩ g, dib_rexpect_eq]
  have eF : dib_ex (rg_scaledOp n k m₀ (physBall n k x l)) (spacing n ^ 2) (freeVar n m₀) lam (fun ψ =>
      (spacing n ^ 2 * ∑ z, dib_GB n k m₀ (physBall n k x l) ⟨x, hx⟩ z * wickPow (freeVar n m₀) 3 (ψ z)) *
        (spacing n ^ 2 * ∑ z, g z * wickPow (freeVar n m₀) 3 (ψ z))) =
      dib_ex (rg_scaledOp n k m₀ (physBall n k x l)) (spacing n ^ 2) (freeVar n m₀) lam
        (m5f_FF n k m₀ (physBall n k x l) ⟨x, hx⟩ g) := rfl
  rw [eF, abs_mul (12 * lam), abs_mul (16 * lam ^ 2), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 12 * lam),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * lam ^ 2)]
  set u1 := |dib_ex (rg_scaledOp n k m₀ (physBall n k x l)) (spacing n ^ 2) (freeVar n m₀) lam
    (m5f_Y n k m₀ (physBall n k x l) ⟨x, hx⟩ g)|
  set u2 := |dib_ex (rg_scaledOp n k m₀ (physBall n k x l)) (spacing n ^ 2) (freeVar n m₀) lam
    (m5f_FF n k m₀ (physBall n k x l) ⟨x, hx⟩ g)|
  set w := Γ * K * b / z0 with hw
  have hl2 : lam ^ 2 ≤ lam := by nlinarith
  have hu2 : 0 ≤ u2 := abs_nonneg _
  have hlast : lam * Γ * (28 * K * b / z0) = 28 * lam * w := by rw [hw]; ring
  rw [hlast]
  have hw0 : 0 ≤ w := le_trans hu2 hF
  nlinarith [mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 12 * lam),
    mul_le_mul_of_nonneg_left hF (by positivity : (0 : ℝ) ≤ 16 * lam ^ 2),
    mul_le_mul_of_nonneg_right hl2 hw0]

end Region

/-! ## The conclusions: SmallBoundarySum and RegionSusceptibility -/

section Conclusions

variable {n k : ℕ}

/-- Row sums of the region Green's function: Σ_{u∈B} regionGreen(z,u) ≤ m₀⁻². -/
theorem m5f_regionGreen_rowSum_le {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (z : {z // z ∈ B}) : ∑ u, regionGreen n k m₀ B z u ≤ 1 / m₀ ^ 2 := by
  calc ∑ u, regionGreen n k m₀ B z u ≤ ∑ u : {z // z ∈ B}, dirGreen n k m₀ z u :=
        Finset.sum_le_sum fun u _ => fv2_regionGreen_le_dirGreen hm B z u
    _ = ∑ u ∈ B, dirGreen n k m₀ z u := Finset.sum_coe_sort B (fun u => dirGreen n k m₀ z u)
    _ ≤ ∑ u, dirGreen n k m₀ z u :=
        Finset.sum_le_univ_sum_of_nonneg fun u => dirGreen_nonneg hm _ _
    _ ≤ 1 / m₀ ^ 2 := glp_dirGreen_rowSum_le (n := n) (k := k) hm (z : DSite n k)

/-- g = C_B t for t(u) = Σ_{v∉B} bondJ u v is the free exit weight of z. -/
theorem m5f_gExit_eq (m₀ : ℝ) (B : Finset (DSite n k)) (z : {z // z ∈ B}) :
    (dib_GB n k m₀ B *ᵥ fun a => ∑ v ∈ Bᶜ, bondJ n k a v) z =
      ∑ u : {z // z ∈ B}, ∑ v ∈ Bᶜ,
        bondJ n k u v * ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ B z u) := by
  simp only [mulVec, dotProduct, dib_GB, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem m5f_gExit_bounds {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (z : {z // z ∈ B}) :
    0 ≤ (dib_GB n k m₀ B *ᵥ fun a => ∑ v ∈ Bᶜ, bondJ n k a v) z ∧
      (dib_GB n k m₀ B *ᵥ fun a => ∑ v ∈ Bᶜ, bondJ n k a v) z ≤ 1 := by
  rw [m5f_gExit_eq]
  refine ⟨Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v hv => ?_,
    rg_exit_weight_le_one hm B z⟩
  have huv : (u : DSite n k) ≠ v := by
    rintro h'; rw [← h'] at hv; exact (Finset.mem_compl.mp hv) u.2
  exact mul_nonneg (bondJ_nonneg huv)
    (mul_nonneg (inv_nonneg.mpr (by positivity)) (rg_regionGreen_nonneg hm B z u))

/-- g = C_B t for t ≡ ε² is the row sum of regionGreen. -/
theorem m5f_gSus_eq (m₀ : ℝ) (B : Finset (DSite n k)) (z : {z // z ∈ B}) :
    (dib_GB n k m₀ B *ᵥ fun _ => spacing n ^ 2) z = ∑ u, regionGreen n k m₀ B z u := by
  have hε : spacing n ≠ 0 := (spacing_pos n).ne'
  simp only [mulVec, dotProduct, dib_GB, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  field_simp

theorem m5f_gSus_bounds {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (z : {z // z ∈ B}) :
    0 ≤ (dib_GB n k m₀ B *ᵥ fun _ => spacing n ^ 2) z ∧
      (dib_GB n k m₀ B *ᵥ fun _ => spacing n ^ 2) z ≤ 1 / m₀ ^ 2 := by
  rw [m5f_gSus_eq]
  exact ⟨Finset.sum_nonneg fun u _ => rg_regionGreen_nonneg hm B z u,
    m5f_regionGreen_rowSum_le hm B z⟩

/-- **Boundary sum ≤ free exit weight + λK** (I1 with t(u) = Σ_{v∉B} bondJ u v, then I2 with
Γ = 1 and F2). -/
theorem m5f_boundary_le {m₀ l : ℝ} (hm : m₀ ≠ 0) (hl : 0 ≤ l) (hN : NelsonRegionHyp m₀ l)
    (hD : WickDefectHyp m₀ l) (hW : WickL2Hyp m₀ l) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      SmallBoundarySum m₀ lam l (2 / Real.cosh (rg_kappa m₀ * l) + lam * K) ∧
      RegionSusceptibility m₀ lam l (1 / m₀ ^ 2 + lam * (1 / m₀ ^ 2) * K) := by
  obtain ⟨K, hK, hI2⟩ := m5f_correction_le hm hN hD hW
  refine ⟨K, hK, fun lam hl0 hl1 => ⟨fun n k x => ?_, fun n k x => ?_⟩⟩
  · have hx := rg_mem_physBall_self (n := n) (k := k) hl x
    have hsum : ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
        bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u =
        ∑ u ∈ physBall n k x l, (fun u => ∑ v ∈ (physBall n k x l)ᶜ, bondJ n k u v) u *
          regionTwoPt n k m₀ lam (physBall n k x l) x u :=
      Finset.sum_congr rfl fun u _ => by rw [Finset.sum_mul]
    rw [hsum, dib_double_ibp_region' hm hl0 _ _ hx]
    have hb := m5f_gExit_bounds hm (physBall n k x l)
    have hI := hI2 n k x hx lam 1 _ hl0 hl1 zero_le_one hb
    have hfree : (dib_GB n k m₀ (physBall n k x l) *ᵥ
        fun a => ∑ v ∈ (physBall n k x l)ᶜ, bondJ n k a v) ⟨x, hx⟩ ≤
          2 / Real.cosh (rg_kappa m₀ * l) := by
      rw [m5f_gExit_eq]; exact free_boundary_le hm hl n k x
    set T1 := 12 * lam * spacing n ^ 2 * ∑ z, (dib_GB n k m₀ (physBall n k x l) *ᵥ
        fun a => ∑ v ∈ (physBall n k x l)ᶜ, bondJ n k a v) z *
        dib_GB n k m₀ (physBall n k x l) ⟨x, hx⟩ z *
        dib_rexpect n k m₀ lam (physBall n k x l) (fun ψ => wickPow (freeVar n m₀) 2 (ψ z))
    set T2 := 16 * lam ^ 2 * dib_rexpect n k m₀ lam (physBall n k x l) (fun ψ =>
        (spacing n ^ 2 * ∑ z, dib_GB n k m₀ (physBall n k x l) ⟨x, hx⟩ z *
          wickPow (freeVar n m₀) 3 (ψ z)) *
        (spacing n ^ 2 * ∑ z, (dib_GB n k m₀ (physBall n k x l) *ᵥ
          fun a => ∑ v ∈ (physBall n k x l)ᶜ, bondJ n k a v) z * wickPow (freeVar n m₀) 3 (ψ z)))
    have h1 := neg_abs_le T1
    have h2 := le_abs_self T2
    have : lam * 1 * K = lam * K := by ring
    linarith
  · have hx := rg_mem_physBall_self (n := n) (k := k) hl x
    have hsum : spacing n ^ 2 * ∑ y, regionTwoPt n k m₀ lam (physBall n k x l) x y =
        ∑ u ∈ physBall n k x l, (fun _ => spacing n ^ 2) u *
          regionTwoPt n k m₀ lam (physBall n k x l) x u := by
      rw [Finset.mul_sum]
      exact (Finset.sum_subset (Finset.subset_univ _) fun y _ hy => by
        rw [regionTwoPt_out m₀ lam _ x hy, mul_zero]).symm
    rw [hsum, dib_double_ibp_region' hm hl0 _ _ hx]
    have hm2 : 0 ≤ 1 / m₀ ^ 2 := by positivity
    have hb := m5f_gSus_bounds hm (physBall n k x l)
    have hI := hI2 n k x hx lam (1 / m₀ ^ 2) _ hl0 hl1 hm2 hb
    have hfree := (hb ⟨x, hx⟩).2
    set T1 := 12 * lam * spacing n ^ 2 * ∑ z, (dib_GB n k m₀ (physBall n k x l) *ᵥ
        fun _ => spacing n ^ 2) z *
        dib_GB n k m₀ (physBall n k x l) ⟨x, hx⟩ z *
        dib_rexpect n k m₀ lam (physBall n k x l) (fun ψ => wickPow (freeVar n m₀) 2 (ψ z))
    set T2 := 16 * lam ^ 2 * dib_rexpect n k m₀ lam (physBall n k x l) (fun ψ =>
        (spacing n ^ 2 * ∑ z, dib_GB n k m₀ (physBall n k x l) ⟨x, hx⟩ z *
          wickPow (freeVar n m₀) 3 (ψ z)) *
        (spacing n ^ 2 * ∑ z, (dib_GB n k m₀ (physBall n k x l) *ᵥ
          fun _ => spacing n ^ 2) z * wickPow (freeVar n m₀) 3 (ψ z)))
    have h1 := neg_abs_le T1
    have h2 := le_abs_self T2
    linarith

theorem m5f_cosh_log8 {m₀ : ℝ} (hm : m₀ ≠ 0) :
    2 / Real.cosh (rg_kappa m₀ * (Real.log 8 / rg_kappa m₀)) ≤ 1 / 2 := by
  have hκ := rg_kappa_pos hm
  rw [mul_div_cancel₀ _ hκ.ne']
  refine (rg_two_div_cosh_le _).trans ?_
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- **The M5 conclusions**, conditional on the region Nelson bound and the two free-field facts:
∀ m₀ > 0, ∃ l ≥ 0, ∃ λ₀ > 0, ∃ A ≥ 0, ∀ λ ∈ [0, λ₀),
SmallBoundarySum m₀ λ l (3/4) ∧ RegionSusceptibility m₀ λ l A. -/
theorem m5Inputs_of
    (hN : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → NelsonRegionHyp m₀ l)
    (hD : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → WickDefectHyp m₀ l)
    (hW : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → WickL2Hyp m₀ l) :
    ∀ m₀ : ℝ, 0 < m₀ → ∃ l : ℝ, 0 ≤ l ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ lam : ℝ, 0 ≤ lam → lam < lam₀ →
        SmallBoundarySum m₀ lam l (3 / 4) ∧ RegionSusceptibility m₀ lam l A := by
  intro m₀ hm₀
  have hm := hm₀.ne'
  set l := Real.log 8 / rg_kappa m₀ with hldef
  have hl : 0 ≤ l := div_nonneg (Real.log_nonneg (by norm_num)) (rg_kappa_pos hm).le
  obtain ⟨K, hK, hB⟩ := m5f_boundary_le hm hl (hN m₀ l hm₀ hl) (hD m₀ l hm₀ hl) (hW m₀ l hm₀ hl)
  have hc := m5f_cosh_log8 hm
  rw [← hldef] at hc
  refine ⟨l, hl, min 1 (1 / (4 * (K + 1))), lt_min one_pos (by positivity),
    1 / m₀ ^ 2 * (1 + K), by positivity, fun lam hl0 hlt => ?_⟩
  have hl1 : lam ≤ 1 := (hlt.trans_le (min_le_left _ _)).le
  have hl2 : lam < 1 / (4 * (K + 1)) := hlt.trans_le (min_le_right _ _)
  have hlK : lam * K ≤ 1 / 4 := by
    have h4 : lam * (4 * (K + 1)) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hl2
    nlinarith
  obtain ⟨hS, hR⟩ := hB lam hl0 hl1
  refine ⟨fun n k x => (hS n k x).trans (by linarith), fun n k x => (hR n k x).trans ?_⟩
  have hm2 : 0 ≤ 1 / m₀ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hl1 hK) hm2]

/-- The same in the `M5Inputs` form of PP2Assembly (γ = 3/4). -/
theorem m5f_M5Inputs
    (hN : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → NelsonRegionHyp m₀ l)
    (hD : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → WickDefectHyp m₀ l)
    (hW : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → WickL2Hyp m₀ l) :
    ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 ≤ lam → lam < lam₀ →
      M5Inputs m₀ lam := by
  intro m₀ hm₀
  obtain ⟨l, hl, lam₀, hlam₀, A, hA, h⟩ := m5Inputs_of hN hD hW m₀ hm₀
  exact ⟨lam₀, hlam₀, fun lam hl0 hlt =>
    ⟨l, 3 / 4, A, hl, by norm_num, by norm_num, hA, (h lam hl0 hlt).1, (h lam hl0 hlt).2⟩⟩

/-- **The V3 target, conditional on:** the region Nelson bound, the two free-field facts
(squared Wick defect, L² Wick moments), non-Gaussianity of the limit points at small λ, and
Schwartz separability. -/
theorem phiFourTwoGapV3_of_hyps
    (hN : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → NelsonRegionHyp m₀ l)
    (hD : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → WickDefectHyp m₀ l)
    (hW : ∀ m₀ l : ℝ, 0 < m₀ → 0 ≤ l → WickL2Hyp m₀ l)
    (hNG : ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₁ : ℝ, 0 < lam₁ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₁ →
      ∀ Z, IsLimitPoint m₀ lam Z → IsNonGaussian Z)
    (hS : SchwartzSeparable) : PhiFourTwoGapV3 := by
  refine phiFourTwoGapV3_of_M5 (fun m₀ hm₀ => ?_) hS
  obtain ⟨lam₀, hlam₀, h5⟩ := m5f_M5Inputs hN hD hW m₀ hm₀
  obtain ⟨lam₁, hlam₁, hng⟩ := hNG m₀ hm₀
  exact ⟨min lam₀ lam₁, lt_min hlam₀ hlam₁, fun lam hl hlt =>
    ⟨h5 lam hl.le (hlt.trans_le (min_le_left _ _)), hng lam hl (hlt.trans_le (min_le_right _ _))⟩⟩

end Conclusions

end PP2M5Final

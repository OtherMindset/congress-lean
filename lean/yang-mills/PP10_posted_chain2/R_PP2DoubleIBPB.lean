import LongTable.R_PP2DoubleIBPA

/-!
Part B of PP2DoubleIBP (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2DoubleIBP.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `dib_step1` / `dib_first_ibp`: ⟨φ_x φ_u⟩ = G(x,u) − 4λe Σ_y G(x,y) ⟨φ_u :φ_y³:⟩.
* `dib_step2` / `dib_second_ibp`: ⟨φ_u :φ_y³:⟩ = 3 G(u,y) ⟨:φ_y²:⟩ − 4λe Σ_z G(u,z) ⟨:φ_y³: :φ_z³:⟩.
* **`dib_double_ibp`** (generic), **`dib_double_ibp_box`**, **`dib_double_ibp_region`**
  (and `dib_double_ibp_region'`, sum over u ∈ B as a Finset sum): for t and g = G t,
  Σ_u t_u ⟨φ_x φ_u⟩ = g(x) − 12 λ ε² Σ_z g(z) G(x,z) ⟨:φ_z²:⟩ + 16 λ² ⟨F₁ F_g⟩,
  F₁ = ε² Σ_z G(x,z) :φ_z³:, F_g = ε² Σ_z g(z) :φ_z³:. Also unnormalised (`dib_double_ibp_unnorm`)
  and first/second IBP for box and generic.

NOT formalized here: I2 (bounds on the two correction terms); the region table for G3 (it is the
generic table with A = rg_scaledOp B, via `dib_rexpect_eq` at λ = 0); Wick derivative and Hermite
recursion in all degrees (only ≤ 4 is needed); δ_y ≥ 0 (F4).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Matrix Finset PP2Target

set_option maxHeartbeats 400000

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2DoubleIBP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **First integration by parts** (unnormalised):
∫ φ_x φ_u W = A⁻¹(x,u) ∫ W − 4λe Σ_y A⁻¹(x,y) ∫ φ_u :φ_y³: W. -/
theorem dib_step1 {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (x u : ι) :
    ∫ φ, φ x * φ u * dib_W A e c lam φ =
      A⁻¹ x u * (∫ φ, dib_W A e c lam φ)
      - 4 * lam * e * ∑ y, A⁻¹ x y * ∫ φ, φ u * wickPow c 3 (φ y) * dib_W A e c lam φ := by
  have hle : 0 ≤ lam * e := mul_nonneg hlam he
  set K3 : ℝ := 6 + 3 * |c| with hK3def
  have hK3 : 0 ≤ K3 := by positivity
  set C := dib_M ι e c lam * (1 + 4 * (lam * e) * K3) with hC
  have hF : ∀ φ : ι → ℝ, |φ u * dib_E e c lam φ| ≤ C * Real.exp (2 * ∑ j, |φ j|) := by
    intro φ
    rw [mul_comm, hC]
    apply dib_E_mul_bnd he c hlam φ
    apply dib_lift (by positivity) φ
    have := dib_abs_le φ u
    have h1 := dib_one_le_exp φ
    have : 0 ≤ 4 * (lam * e) * K3 * Real.exp (∑ j, |φ j|) := by positivity
    nlinarith
  have hF' : ∀ (y : ι) (φ : ι → ℝ),
      |fderiv ℝ (fun ψ : ι → ℝ => ψ u * dib_E e c lam ψ) φ (Pi.single y 1)| ≤
        C * Real.exp (2 * ∑ j, |φ j|) := by
    intro y φ
    rw [dib_fderiv_F1, dib_D_single, hC]
    apply dib_E_mul_bnd he c hlam φ
    have hs := dib_single_abs_le y u
    have hT := dib_abs_scaled lam e (φ u) (wickPow c 3 (φ y)) hlam he
    have hp := dib_mul_bnd φ (dib_abs_le' φ u) (dib_wick3_le c φ y)
    rw [abs_mul] at hp
    have h1 := dib_one_le_e2 φ
    have hsub := abs_sub ((Pi.single y (1 : ℝ) : ι → ℝ) u)
      (lam * (φ u * (e * (4 * wickPow c 3 (φ y)))))
    have hm4 := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 4 * (lam * e))
    nlinarith
  have key := PP2GaussIBP.gauss_ibp_cov hA (dib_differentiable_F1 e c lam u) C 2 x hF hF'
  have hint3 : ∀ y, Integrable (fun φ : ι → ℝ => φ u * wickPow c 3 (φ y) * dib_W A e c lam φ) :=
    fun y => dib_integrable hA he c hlam (h := fun φ : ι → ℝ => φ u * wickPow c 3 (φ y))
      ((continuous_apply u).mul ((dib_continuous_wick c 3).comp (continuous_apply y))) (1 * K3)
      (fun φ => dib_mul_bnd φ (dib_abs_le' φ u) (dib_wick3_le c φ y))
  have eL : ∫ φ, φ x * φ u * dib_W A e c lam φ =
      ∫ φ, φ x * (φ u * dib_E e c lam φ) * PP2GaussIBP.gaussWeight A φ := by
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only [dib_W]
    ring
  have eR : ∀ y : ι, ∫ φ, fderiv ℝ (fun ψ : ι → ℝ => ψ u * dib_E e c lam ψ) φ (Pi.single y 1) *
        PP2GaussIBP.gaussWeight A φ =
      (Pi.single y (1 : ℝ) : ι → ℝ) u * (∫ φ, dib_W A e c lam φ)
        - 4 * lam * e * ∫ φ, φ u * wickPow c 3 (φ y) * dib_W A e c lam φ := by
    intro y
    have e' : (fun φ : ι → ℝ =>
        fderiv ℝ (fun ψ : ι → ℝ => ψ u * dib_E e c lam ψ) φ (Pi.single y 1) *
          PP2GaussIBP.gaussWeight A φ) =
        fun φ => (Pi.single y (1 : ℝ) : ι → ℝ) u * dib_W A e c lam φ
          - 4 * lam * e * (φ u * wickPow c 3 (φ y) * dib_W A e c lam φ) := by
      funext φ
      rw [dib_fderiv_F1, dib_D_single, dib_W]
      ring
    rw [e', integral_sub ((dib_integrable_W hA he c hlam).const_mul _)
      ((hint3 y).const_mul _), integral_const_mul, integral_const_mul]
  rw [eL, key]
  simp_rw [eR]
  exact dib_alg1 _ u _ _ _

/-- **Second integration by parts** (unnormalised):
∫ φ_u :φ_y³: W = 3 A⁻¹(u,y) ∫ :φ_y²: W − 4λe Σ_z A⁻¹(u,z) ∫ :φ_y³: :φ_z³: W. -/
theorem dib_step2 {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (u y : ι) :
    ∫ φ, φ u * wickPow c 3 (φ y) * dib_W A e c lam φ =
      3 * A⁻¹ u y * (∫ φ, wickPow c 2 (φ y) * dib_W A e c lam φ)
      - 4 * lam * e * ∑ z, A⁻¹ u z *
          ∫ φ, wickPow c 3 (φ y) * wickPow c 3 (φ z) * dib_W A e c lam φ := by
  have hle : 0 ≤ lam * e := mul_nonneg hlam he
  set K3 : ℝ := 6 + 3 * |c| with hK3def
  set K2 : ℝ := 2 + |c| with hK2def
  have hK3 : 0 ≤ K3 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  set Q : ℝ := K3 + 3 * K2 + 4 * (lam * e) * (K3 * K3) with hQ
  set C := dib_M ι e c lam * Q with hC
  have hF : ∀ φ : ι → ℝ, |wickPow c 3 (φ y) * dib_E e c lam φ| ≤
      C * Real.exp (2 * ∑ j, |φ j|) := by
    intro φ
    rw [mul_comm, hC]
    apply dib_E_mul_bnd he c hlam φ
    apply dib_lift (by positivity) φ
    have := dib_wick3_le c φ y
    have : 0 ≤ (3 * K2 + 4 * (lam * e) * (K3 * K3)) * Real.exp (∑ j, |φ j|) := by
      positivity
    nlinarith
  have hF' : ∀ (z : ι) (φ : ι → ℝ),
      |fderiv ℝ (fun ψ : ι → ℝ => wickPow c 3 (ψ y) * dib_E e c lam ψ) φ
        (Pi.single z 1)| ≤ C * Real.exp (2 * ∑ j, |φ j|) := by
    intro z φ
    rw [dib_fderiv_F2, dib_D_single, hC]
    apply dib_E_mul_bnd he c hlam φ
    have hs := dib_single_abs_le z y
    have hT := dib_abs_scaled lam e (wickPow c 3 (φ y)) (wickPow c 3 (φ z)) hlam he
    have hp := dib_mul_bnd φ (dib_wick3_le c φ y) (dib_wick3_le c φ z)
    rw [abs_mul] at hp
    have h2 := dib_lift hK2 φ (dib_wick2_le c φ y)
    have h3 := dib_lift hK3 φ (dib_wick3_le c φ y)
    have hW : |3 * wickPow c 2 (φ y) * (Pi.single z (1 : ℝ) : ι → ℝ) y| ≤
        3 * K2 * Real.exp (2 * ∑ j, |φ j|) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      have := mul_le_mul h2 hs (abs_nonneg _) (le_trans (abs_nonneg _) h2)
      nlinarith
    have hsub := abs_sub (3 * wickPow c 2 (φ y) * (Pi.single z (1 : ℝ) : ι → ℝ) y)
      (lam * (wickPow c 3 (φ y) * (e * (4 * wickPow c 3 (φ z)))))
    have hm4 := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 4 * (lam * e))
    have : 0 ≤ K3 * Real.exp (2 * ∑ j, |φ j|) := by positivity
    nlinarith
  have key := PP2GaussIBP.gauss_ibp_cov hA (dib_differentiable_F2 e c lam y) C 2 u hF hF'
  have hint2 : Integrable (fun φ : ι → ℝ => wickPow c 2 (φ y) * dib_W A e c lam φ) :=
    dib_integrable hA he c hlam (h := fun φ : ι → ℝ => wickPow c 2 (φ y))
      ((dib_continuous_wick c 2).comp (continuous_apply y)) K2
      (fun φ => dib_lift hK2 φ (dib_wick2_le c φ y))
  have hint33 : ∀ z, Integrable (fun φ : ι → ℝ => wickPow c 3 (φ y) * wickPow c 3 (φ z) *
      dib_W A e c lam φ) := fun z =>
    dib_integrable hA he c hlam (h := fun φ : ι → ℝ => wickPow c 3 (φ y) * wickPow c 3 (φ z))
      (((dib_continuous_wick c 3).comp (continuous_apply y)).mul
        ((dib_continuous_wick c 3).comp (continuous_apply z))) (K3 * K3)
      (fun φ => dib_mul_bnd φ (dib_wick3_le c φ y) (dib_wick3_le c φ z))
  have eL : ∫ φ, φ u * wickPow c 3 (φ y) * dib_W A e c lam φ =
      ∫ φ, φ u * (wickPow c 3 (φ y) * dib_E e c lam φ) * PP2GaussIBP.gaussWeight A φ := by
    refine integral_congr_ae (ae_of_all _ fun φ => ?_)
    simp only [dib_W]
    ring
  have eR : ∀ z : ι, ∫ φ,
      fderiv ℝ (fun ψ : ι → ℝ => wickPow c 3 (ψ y) * dib_E e c lam ψ) φ (Pi.single z 1) *
        PP2GaussIBP.gaussWeight A φ =
      (Pi.single z (1 : ℝ) : ι → ℝ) y * (3 * ∫ φ, wickPow c 2 (φ y) * dib_W A e c lam φ)
        - 4 * lam * e * ∫ φ, wickPow c 3 (φ y) * wickPow c 3 (φ z) * dib_W A e c lam φ := by
    intro z
    have e' : (fun φ : ι → ℝ =>
        fderiv ℝ (fun ψ : ι → ℝ => wickPow c 3 (ψ y) * dib_E e c lam ψ) φ
          (Pi.single z 1) * PP2GaussIBP.gaussWeight A φ) =
        fun φ => ((Pi.single z (1 : ℝ) : ι → ℝ) y * 3) *
            (wickPow c 2 (φ y) * dib_W A e c lam φ)
          - 4 * lam * e * (wickPow c 3 (φ y) * wickPow c 3 (φ z) * dib_W A e c lam φ) := by
      funext φ
      rw [dib_fderiv_F2, dib_D_single, dib_W]
      ring
    rw [e', integral_sub (hint2.const_mul _) ((hint33 z).const_mul _), integral_const_mul,
      integral_const_mul]
    ring
  rw [eL, key]
  simp_rw [eR]
  refine (dib_alg1 _ y _ _ _).trans ?_
  ring

/-! ## Assembling the double integration by parts -/

theorem dib_alg2 (G : ι → ι → ℝ) (hG : ∀ a b, G a b = G b a)
    (t : ι → ℝ) (x : ι) (Z L : ℝ) (I2 : ι → ℝ) (I33 : ι → ι → ℝ) :
    ∑ u, t u * (G x u * Z - L * ∑ y, G x y * (3 * G u y * I2 y - L * ∑ z, G u z * I33 y z)) =
      (∑ u, G x u * t u) * Z - 3 * L * ∑ y, (∑ u, G y u * t u) * G x y * I2 y
        + L ^ 2 * ∑ y, ∑ z, G x y * (∑ u, G z u * t u) * I33 y z := by
  have hU : ∀ u, t u * (G x u * Z - L * ∑ y, G x y * (3 * G u y * I2 y
      - L * ∑ z, G u z * I33 y z)) =
      t u * G x u * Z - 3 * L * (∑ y, t u * G x y * G u y * I2 y)
        + L ^ 2 * ∑ y, ∑ z, t u * G x y * G u z * I33 y z := by
    intro u
    have a1 : ∑ y, G x y * (3 * G u y * I2 y - L * ∑ z, G u z * I33 y z) =
        3 * (∑ y, G x y * G u y * I2 y) - L * ∑ y, G x y * ∑ z, G u z * I33 y z := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    have a2 : ∑ y, t u * G x y * G u y * I2 y = t u * ∑ y, G x y * G u y * I2 y := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    have a3 : ∑ y, ∑ z, t u * G x y * G u z * I33 y z =
        t u * ∑ y, G x y * ∑ z, G u z * I33 y z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [a1, a2, a3]
    ring
  rw [Finset.sum_congr rfl fun u _ => hU u, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  have b1 : ∑ u, t u * G x u = ∑ u, G x u * t u := Finset.sum_congr rfl fun u _ => by ring
  have b2 : ∑ u, ∑ y, t u * G x y * G u y * I2 y = ∑ y, (∑ u, G y u * t u) * G x y * I2 y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [hG u y]; ring
  have b3 : ∑ u, ∑ y, ∑ z, t u * G x y * G u z * I33 y z =
      ∑ y, ∑ z, G x y * (∑ u, G z u * t u) * I33 y z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [hG u z]; ring
  rw [b1, b2, b3]

/-- Expansion of ∫ (e Σ a :φ³:)(e Σ b :φ³:) W into two-point integrals. -/
theorem dib_int_FF {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (a b : ι → ℝ) :
    ∫ φ, (e * ∑ y, a y * wickPow c 3 (φ y)) * (e * ∑ z, b z * wickPow c 3 (φ z)) *
        dib_W A e c lam φ =
      e * e * ∑ y, ∑ z, a y * b z *
        ∫ φ, wickPow c 3 (φ y) * wickPow c 3 (φ z) * dib_W A e c lam φ := by
  have hint33 : ∀ y z, Integrable (fun φ : ι → ℝ => wickPow c 3 (φ y) * wickPow c 3 (φ z) *
      dib_W A e c lam φ) := fun y z =>
    dib_integrable hA he c hlam (h := fun φ : ι → ℝ => wickPow c 3 (φ y) * wickPow c 3 (φ z))
      (((dib_continuous_wick c 3).comp (continuous_apply y)).mul
        ((dib_continuous_wick c 3).comp (continuous_apply z))) ((6 + 3 * |c|) * (6 + 3 * |c|))
      (fun φ => dib_mul_bnd φ (dib_wick3_le c φ y) (dib_wick3_le c φ z))
  have e' : (fun φ : ι → ℝ => (e * ∑ y, a y * wickPow c 3 (φ y)) *
        (e * ∑ z, b z * wickPow c 3 (φ z)) * dib_W A e c lam φ) =
      fun φ => ∑ y, ∑ z, (e * e * (a y * b z)) *
        (wickPow c 3 (φ y) * wickPow c 3 (φ z) * dib_W A e c lam φ) := by
    funext φ
    rw [show (e * ∑ y, a y * wickPow c 3 (φ y)) * (e * ∑ z, b z * wickPow c 3 (φ z)) *
        dib_W A e c lam φ = (e * e * dib_W A e c lam φ) *
          ((∑ y, a y * wickPow c 3 (φ y)) * ∑ z, b z * wickPow c 3 (φ z)) by ring,
      Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [e', integral_finsetSum _ (fun y _ => integrable_finsetSum _ fun z _ =>
    (hint33 y z).const_mul _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_finsetSum _ (fun z _ => (hint33 y z).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_const_mul]
  ring

/-- **Double integration by parts, unnormalised, any ι.** -/
theorem dib_double_ibp_unnorm {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (t : ι → ℝ) (x : ι) :
    ∑ u, t u * ∫ φ, φ x * φ u * dib_W A e c lam φ =
      (A⁻¹ *ᵥ t) x * (∫ φ, dib_W A e c lam φ)
      - 12 * lam * e * ∑ z, (A⁻¹ *ᵥ t) z * A⁻¹ x z *
          (∫ φ, wickPow c 2 (φ z) * dib_W A e c lam φ)
      + 16 * lam ^ 2 * ∫ φ, (e * ∑ z, A⁻¹ x z * wickPow c 3 (φ z)) *
          (e * ∑ z, (A⁻¹ *ᵥ t) z * wickPow c 3 (φ z)) * dib_W A e c lam φ := by
  simp_rw [dib_step1 hA he c hlam, dib_step2 hA he c hlam]
  rw [dib_int_FF hA he c hlam, dib_alg2 (fun a b => A⁻¹ a b) (dib_inv_symm hA)]
  simp only [Matrix.mulVec, dotProduct]
  ring

/-! ## Normalised statements, any ι -/

theorem dib_sum_div (f g : ι → ℝ) (Z : ℝ) :
    ∑ i, f i * (g i / Z) = (∑ i, f i * g i) / Z := by
  rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring

/-- ⟨φ_x φ_u⟩ = A⁻¹(x,u) − 4λe Σ_y A⁻¹(x,y) ⟨φ_u :φ_y³:⟩. -/
theorem dib_first_ibp {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (x u : ι) :
    dib_ex A e c lam (fun φ => φ x * φ u) =
      A⁻¹ x u - 4 * lam * e * ∑ y, A⁻¹ x y *
        dib_ex A e c lam (fun φ => φ u * wickPow c 3 (φ y)) := by
  have hZ := (dib_integral_W_pos hA he c hlam).ne'
  simp only [dib_ex]
  rw [dib_step1 hA he c hlam, dib_sum_div]
  field_simp

/-- ⟨φ_u :φ_y³:⟩ = 3 A⁻¹(u,y) ⟨:φ_y²:⟩ − 4λe Σ_z A⁻¹(u,z) ⟨:φ_y³: :φ_z³:⟩. -/
theorem dib_second_ibp {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (u y : ι) :
    dib_ex A e c lam (fun φ => φ u * wickPow c 3 (φ y)) =
      3 * A⁻¹ u y * dib_ex A e c lam (fun φ => wickPow c 2 (φ y))
        - 4 * lam * e * ∑ z, A⁻¹ u z *
          dib_ex A e c lam (fun φ => wickPow c 3 (φ y) * wickPow c 3 (φ z)) := by
  have hZ := (dib_integral_W_pos hA he c hlam).ne'
  simp only [dib_ex]
  rw [dib_step2 hA he c hlam, dib_sum_div]
  field_simp

/-- **Double integration by parts, normalised, any ι** (g = A⁻¹ t):
Σ_u t_u ⟨φ_x φ_u⟩ = g(x) − 12λe Σ_z g(z) A⁻¹(x,z) ⟨:φ_z²:⟩ + 16λ² ⟨F₁ F_g⟩. -/
theorem dib_double_ibp {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (t : ι → ℝ) (x : ι) :
    ∑ u, t u * dib_ex A e c lam (fun φ => φ x * φ u) =
      (A⁻¹ *ᵥ t) x
      - 12 * lam * e * ∑ z, (A⁻¹ *ᵥ t) z * A⁻¹ x z * dib_ex A e c lam (fun φ => wickPow c 2 (φ z))
      + 16 * lam ^ 2 * dib_ex A e c lam (fun φ =>
          (e * ∑ z, A⁻¹ x z * wickPow c 3 (φ z)) *
            (e * ∑ z, (A⁻¹ *ᵥ t) z * wickPow c 3 (φ z))) := by
  have hZ := (dib_integral_W_pos hA he c hlam).ne'
  simp only [dib_ex]
  rw [dib_sum_div, dib_sum_div, dib_double_ibp_unnorm hA he c hlam]
  field_simp


/-! ## Instance 1: the Dirichlet box (weight `dweight … X⁴`, covariance ε⁻² dirGreen) -/

section Box

variable {n k : ℕ}

/-- The free box covariance ε⁻² · dirGreen (= ⟨φ_x φ_y⟩ at λ = 0 by `gauss_cov`). -/
def dib_G (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ :=
  (spacing n ^ 2)⁻¹ • dirGreen n k m₀

theorem dib_G_eq {m₀ : ℝ} (hm : m₀ ≠ 0) : dib_G n k m₀ = (scaledOp n k m₀)⁻¹ :=
  (scaledOp_inv hm).symm

theorem dib_dweight_eq (m₀ lam : ℝ) (φ : DField n k) :
    dweight n k m₀ lam (Polynomial.X ^ 4) φ =
      dib_W (scaledOp n k m₀) (spacing n ^ 2) (freeVar n m₀) lam φ := by
  rw [dib_W, gaussWeight_dirAction, dib_E, ← Real.exp_add, dweight]
  congr 1
  simp only [wickPoly_X4, wickPow_four']
  ring

theorem dib_dexpect_eq (m₀ lam : ℝ) (F : DField n k → ℝ) :
    PP2Griffiths.dexpect n k m₀ lam F =
      dib_ex (scaledOp n k m₀) (spacing n ^ 2) (freeVar n m₀) lam F := by
  simp only [PP2Griffiths.dexpect, dib_ex, dib_dweight_eq]

/-- **First integration by parts (box):** ⟨φ_x φ_u⟩ = G(x,u) − 4λε² Σ_y G(x,y) ⟨φ_u :φ_y³:⟩,
G = ε⁻² dirGreen. -/
theorem dib_first_ibp_box {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (x u : DSite n k) :
    PP2Griffiths.dexpect n k m₀ lam (fun φ => φ x * φ u) =
      dib_G n k m₀ x u - 4 * lam * spacing n ^ 2 * ∑ y, dib_G n k m₀ x y *
        PP2Griffiths.dexpect n k m₀ lam (fun φ => φ u * wickPow (freeVar n m₀) 3 (φ y)) := by
  simp only [dib_dexpect_eq, dib_G_eq hm]
  exact dib_first_ibp (scaledOp_posDef hm) (by positivity) _ hlam x u

/-- **Second integration by parts (box):**
⟨φ_u :φ_y³:⟩ = 3 G(u,y) ⟨:φ_y²:⟩ − 4λε² Σ_z G(u,z) ⟨:φ_y³: :φ_z³:⟩. -/
theorem dib_second_ibp_box {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (u y : DSite n k) :
    PP2Griffiths.dexpect n k m₀ lam (fun φ => φ u * wickPow (freeVar n m₀) 3 (φ y)) =
      3 * dib_G n k m₀ u y *
          PP2Griffiths.dexpect n k m₀ lam (fun φ => wickPow (freeVar n m₀) 2 (φ y))
        - 4 * lam * spacing n ^ 2 * ∑ z, dib_G n k m₀ u z *
          PP2Griffiths.dexpect n k m₀ lam
            (fun φ => wickPow (freeVar n m₀) 3 (φ y) * wickPow (freeVar n m₀) 3 (φ z)) := by
  simp only [dib_dexpect_eq, dib_G_eq hm]
  exact dib_second_ibp (scaledOp_posDef hm) (by positivity) _ hlam u y

/-- **I1, double integration by parts (box).** For t : DSite → ℝ and g := G t, G = ε⁻² dirGreen,
with the weight exp(−½ dirAction − λ ε² Σ :φ⁴:) (Wick order at c = freeVar):
Σ_u t_u ⟨φ_x φ_u⟩ = g(x) − 12 λ ε² Σ_z g(z) G(x,z) ⟨:φ_z²:⟩ + 16 λ² ⟨F₁ F_g⟩,
F₁ = ε² Σ_z G(x,z) :φ_z³:, F_g = ε² Σ_z g(z) :φ_z³:. -/
theorem dib_double_ibp_box {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (t : DSite n k → ℝ) (x : DSite n k) :
    ∑ u, t u * PP2Griffiths.dexpect n k m₀ lam (fun φ => φ x * φ u) =
      (dib_G n k m₀ *ᵥ t) x
      - 12 * lam * spacing n ^ 2 * ∑ z, (dib_G n k m₀ *ᵥ t) z * dib_G n k m₀ x z *
          PP2Griffiths.dexpect n k m₀ lam (fun φ => wickPow (freeVar n m₀) 2 (φ z))
      + 16 * lam ^ 2 * PP2Griffiths.dexpect n k m₀ lam (fun φ =>
          (spacing n ^ 2 * ∑ z, dib_G n k m₀ x z * wickPow (freeVar n m₀) 3 (φ z)) *
          (spacing n ^ 2 * ∑ z, (dib_G n k m₀ *ᵥ t) z * wickPow (freeVar n m₀) 3 (φ z))) := by
  simp only [dib_dexpect_eq, dib_G_eq hm]
  exact dib_double_ibp (scaledOp_posDef hm) (by positivity) _ hlam t x

end Box

end PP2DoubleIBP

end

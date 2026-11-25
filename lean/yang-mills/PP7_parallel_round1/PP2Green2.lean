import LongTable.PP2Green
import LongTable.PP2GaussIBP

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M1, session 2.
Dirichlet lattice Green's functions, continued from `LongTable.PP2Green` (namespace `PP2Target`).

Notation: ε = `spacing n`, N = `boxN n k`, `dirOp n k m₀` the Dirichlet operator −Δ_D + m₀² of
session 1, `dirGreen n k m₀ = (dirOp n k m₀)⁻¹`. The site x = (i, j) of the box sits at the point
`site x = (i, j) ∈ ℤ²`; `nn x y` says that x and y are nearest neighbours in the box.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `extVec_apply`, `bondH_apply`, `bondV_apply`: the bond vectors as differences of indicators.
* `dirOp_apply`: dirOp x y = ε⁻² (4·[x = y] − [x, y horizontal neighbours] − [x, y vertical
  neighbours], written with the four shifted indicators) + m₀²·[x = y].
* `dirOp_diag`: dirOp x x = 4/ε² + m₀².
* `dirOp_nn`: nn x y → dirOp x y = −1/ε².
* `dirOp_far`: x ≠ y → ¬ nn x y → dirOp x y = 0.
* `gaussWeight_dirAction`: PP2GaussIBP.gaussWeight (ε² • dirOp) φ = exp(−½ dirAction φ).
* `scaledOp_posDef`, `scaledOp_inv`: (ε² • dirOp) is positive definite and its inverse is
  ε⁻² • dirGreen (m₀ ≠ 0).
* `gauss_cov_unnorm`: ∫ φ x φ y e^(−½ dirAction) = ε⁻² dirGreen x y ∫ e^(−½ dirAction).
* `dirWeight_integral_pos`: 0 < ∫ e^(−½ dirAction).
* `gauss_cov`: **the covariance of the Dirichlet free field**:
  (∫ φ x φ y e^(−½ dirAction)) / (∫ e^(−½ dirAction)) = ε⁻² · dirGreen x y (m₀ ≠ 0).
* `dirGreen_diag_le`: m₀ ≠ 0 → dirGreen x x ≤ 1/m₀².
* `dirGreen_sub`: dirGreen m₁ − dirGreen m₂ = (m₂² − m₁²) • (dirGreen m₁ * dirGreen m₂) (resolvent
  identity).
* `dirGreen_antitone_mass`: m₁ ≠ 0, m₁² ≤ m₂² → dirGreen m₂ x y ≤ dirGreen m₁ x y (entrywise
  monotonicity in the mass).

NOT formalized here: Dirichlet monotonicity in the box (G_Λ ≤ G_Λ' for Λ ⊆ Λ'); the random-walk
representation; exponential decay (Combes–Thomas); comparison of the diagonal with `freeVar`;
higher (Wick) moments of the Gaussian measure.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix MeasureTheory

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## Explicit entries of `dirOp` -/

/-- The site x = (i, j) as a point of ℤ². -/
def site (x : DSite n k) : ℤ × ℤ := (((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ))

/-- Nearest neighbours in the box. -/
def nn (x y : DSite n k) : Prop :=
  ((x.2 : ℕ) = y.2 ∧ ((x.1 : ℕ) + 1 = y.1 ∨ (y.1 : ℕ) + 1 = x.1)) ∨
    ((x.1 : ℕ) = y.1 ∧ ((x.2 : ℕ) + 1 = y.2 ∨ (y.2 : ℕ) + 1 = x.2))

theorem extVec_apply (q : ℤ × ℤ) (x : DSite n k) :
    (extVec q : DField n k) x = if q = site x then 1 else 0 := by
  unfold extVec ext
  by_cases h : 0 ≤ q.1 ∧ q.1 < boxN n k ∧ 0 ≤ q.2 ∧ q.2 < boxN n k
  · rw [dite_eq_left h, Pi.single_apply]
    apply if_congr _ rfl rfl
    simp only [Prod.ext_iff, Fin.ext_iff, site]
    omega
  · rw [dite_eq_right h, ite_eq_right]
    rintro rfl
    apply h
    simp only [site]
    have := x.1.isLt
    have := x.2.isLt
    omega

theorem ind_shift1 (p q : ℤ × ℤ) :
    (if ((p.1 + 1, p.2) : ℤ × ℤ) = q then (1 : ℝ) else 0) =
      if p = (q.1 - 1, q.2) then 1 else 0 := by
  apply if_congr _ rfl rfl
  simp only [Prod.ext_iff]
  omega

theorem ind_shift2 (p q : ℤ × ℤ) :
    (if ((p.1, p.2 + 1) : ℤ × ℤ) = q then (1 : ℝ) else 0) =
      if p = (q.1, q.2 - 1) then 1 else 0 := by
  apply if_congr _ rfl rfl
  simp only [Prod.ext_iff]
  omega

theorem bondH_apply (p : ℤ × ℤ) (x : DSite n k) :
    (bondH p : DField n k) x =
      (if p = ((site x).1 - 1, (site x).2) then 1 else 0) - (if p = site x then 1 else 0) := by
  rw [bondH, bondVec, Pi.sub_apply, extVec_apply, extVec_apply, ind_shift1]

theorem bondV_apply (p : ℤ × ℤ) (x : DSite n k) :
    (bondV p : DField n k) x =
      (if p = ((site x).1, (site x).2 - 1) then 1 else 0) - (if p = site x then 1 else 0) := by
  rw [bondV, bondVec, Pi.sub_apply, extVec_apply, extVec_apply, ind_shift2]

/-- The basic sum of products of differences of indicators. -/
theorem sum_diff_ind (S : Finset (ℤ × ℤ)) (a b a' b' : ℤ × ℤ) (ha : a ∈ S) (hb : b ∈ S) :
    ∑ p ∈ S, ((if p = a then (1 : ℝ) else 0) - (if p = b then 1 else 0)) *
        ((if p = a' then (1 : ℝ) else 0) - (if p = b' then 1 else 0)) =
      ((if a = a' then 1 else 0) - (if a = b' then 1 else 0)) -
        ((if b = a' then 1 else 0) - (if b = b' then 1 else 0)) := by
  have hpt : ∀ p : ℤ × ℤ,
      ((if p = a then (1 : ℝ) else 0) - (if p = b then 1 else 0)) *
        ((if p = a' then (1 : ℝ) else 0) - (if p = b' then 1 else 0)) =
      (if p = a then ((if a = a' then 1 else 0) - (if a = b' then 1 else 0)) else 0) -
        (if p = b then ((if b = a' then 1 else 0) - (if b = b' then 1 else 0)) else 0) := by
    intro p
    by_cases h1 : p = a
    · subst h1
      by_cases h2 : p = b
      · subst h2; simp
      · simp [h2]
    · by_cases h2 : p = b
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', ite_eq_left ha, ite_eq_left hb]

theorem site_mem (x : DSite n k) : site x ∈ bondSet n k := by
  have := x.1.isLt
  have := x.2.isLt
  simp only [bondSet, site, Finset.mem_product, Finset.mem_Icc]
  omega

theorem site_sub1_mem (x : DSite n k) : ((site x).1 - 1, (site x).2) ∈ bondSet n k := by
  have := x.1.isLt
  have := x.2.isLt
  simp only [bondSet, site, Finset.mem_product, Finset.mem_Icc]
  omega

theorem site_sub2_mem (x : DSite n k) : ((site x).1, (site x).2 - 1) ∈ bondSet n k := by
  have := x.1.isLt
  have := x.2.isLt
  simp only [bondSet, site, Finset.mem_product, Finset.mem_Icc]
  omega

/-- **The entries of `dirOp`**, as indicator expressions. -/
theorem dirOp_apply (m₀ : ℝ) (x y : DSite n k) :
    dirOp n k m₀ x y =
      (spacing n ^ 2)⁻¹ *
        ((((if ((site x).1 - 1, (site x).2) = ((site y).1 - 1, (site y).2) then 1 else 0)
            - (if ((site x).1 - 1, (site x).2) = site y then 1 else 0))
          - ((if site x = ((site y).1 - 1, (site y).2) then 1 else 0)
            - (if site x = site y then 1 else 0)))
        + (((if ((site x).1, (site x).2 - 1) = ((site y).1, (site y).2 - 1) then 1 else 0)
            - (if ((site x).1, (site x).2 - 1) = site y then 1 else 0))
          - ((if site x = ((site y).1, (site y).2 - 1) then 1 else 0)
            - (if site x = site y then 1 else 0))))
      + m₀ ^ 2 * (if x = y then 1 else 0) := by
  simp only [dirOp, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  · congr 1
    rw [Finset.sum_add_distrib]
    simp only [bondH_apply, bondV_apply]
    rw [sum_diff_ind _ _ _ _ _ (site_sub1_mem x) (site_mem x),
      sum_diff_ind _ _ _ _ _ (site_sub2_mem x) (site_mem x)]

/-- **Diagonal entries:** dirOp x x = 4/ε² + m₀². -/
theorem dirOp_diag (m₀ : ℝ) (x : DSite n k) :
    dirOp n k m₀ x x = 4 / spacing n ^ 2 + m₀ ^ 2 := by
  rw [dirOp_apply]
  simp only [site, Prod.ext_iff]
  split_ifs <;> first | (exfalso; omega) | (field_simp; ring)

/-- **Nearest-neighbour entries:** dirOp x y = −1/ε². -/
theorem dirOp_nn (m₀ : ℝ) {x y : DSite n k} (h : nn x y) :
    dirOp n k m₀ x y = -1 / spacing n ^ 2 := by
  have hxy : x ≠ y := by
    rintro rfl; unfold nn at h; omega
  rw [dirOp_apply, ite_eq_right hxy]
  unfold nn at h
  simp only [site, Prod.ext_iff]
  split_ifs <;> first | (exfalso; omega) | (field_simp; ring)

/-- **All other entries vanish.** -/
theorem dirOp_far (m₀ : ℝ) {x y : DSite n k} (hxy : x ≠ y) (h : ¬ nn x y) :
    dirOp n k m₀ x y = 0 := by
  rw [dirOp_apply, ite_eq_right hxy]
  have hxy' : ¬ ((x.1 : ℕ) = y.1 ∧ (x.2 : ℕ) = y.2) := by
    rintro ⟨h1, h2⟩; exact hxy (Prod.ext (Fin.ext h1) (Fin.ext h2))
  unfold nn at h
  simp only [site, Prod.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring

/-! ## The Gaussian covariance -/

/-- The scaled operator ε² • dirOp, whose quadratic form is `dirAction`. -/
def scaledOp (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ :=
  (spacing n ^ 2) • dirOp n k m₀

theorem dirAction_eq_scaled (m₀ : ℝ) (φ : DField n k) :
    dirAction n k m₀ φ = φ ⬝ᵥ scaledOp n k m₀ *ᵥ φ := by
  rw [scaledOp, smul_mulVec, dotProduct_smul, smul_eq_mul, dirAction_eq_quad]

theorem gaussWeight_dirAction (m₀ : ℝ) (φ : DField n k) :
    PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ = Real.exp (-(dirAction n k m₀ φ) / 2) := by
  rw [PP2GaussIBP.gaussWeight, dirAction_eq_scaled]

theorem scaledOp_posDef {m₀ : ℝ} (hm : m₀ ≠ 0) : (scaledOp n k m₀).PosDef := by
  have hH : (scaledOp n k m₀).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, scaledOp, transpose_smul,
      dirOp_transpose]
  refine PosDef.of_dotProduct_mulVec_pos hH fun φ hφ => ?_
  rw [star_trivial, ← dirAction_eq_scaled, dirAction_eq_quad]
  exact mul_pos (pow_pos (spacing_pos n) 2) (dirOp_quad_pos hm hφ)

theorem scaledOp_inv {m₀ : ℝ} (hm : m₀ ≠ 0) :
    (scaledOp n k m₀)⁻¹ = (spacing n ^ 2)⁻¹ • dirGreen n k m₀ := by
  apply inv_eq_right_inv
  rw [scaledOp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, dirOp_mul_dirGreen hm,
    mul_inv_cancel₀ (pow_ne_zero 2 (spacing_pos n).ne'), one_smul]

/-- Unnormalised covariance identity. -/
theorem gauss_cov_unnorm {m₀ : ℝ} (hm : m₀ ≠ 0) (x y : DSite n k) :
    ∫ φ : DField n k, φ x * φ y * Real.exp (-(dirAction n k m₀ φ) / 2) =
      (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y *
        ∫ φ : DField n k, Real.exp (-(dirAction n k m₀ φ) / 2) := by
  have hA := scaledOp_posDef (n := n) (k := k) hm
  have hfd : ∀ φ : DField n k, fderiv ℝ (fun ψ : DField n k => ψ y) φ =
      ContinuousLinearMap.proj y := fun φ => (hasFDerivAt_apply y φ).fderiv
  have hsum : ∀ φ : DField n k, |φ y| ≤ 1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro φ
    have h1 : |φ y| ≤ ∑ i, |φ i| :=
      Finset.single_le_sum (f := fun i => |φ i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ y)
    have h2 := Real.add_one_le_exp (∑ i, |φ i|)
    rw [one_mul, one_mul]; linarith
  have hF' : ∀ (z : DSite n k) (φ : DField n k),
      |fderiv ℝ (fun ψ : DField n k => ψ y) φ (Pi.single z 1)| ≤
        1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro z φ
    rw [hfd, ContinuousLinearMap.proj_apply]
    have h1 : |(Pi.single z (1 : ℝ) : DField n k) y| ≤ 1 := by
      rw [Pi.single_apply]; split_ifs <;> norm_num
    have h2 : 1 ≤ Real.exp (1 * ∑ i, |φ i|) :=
      Real.one_le_exp (mul_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    linarith
  have key := PP2GaussIBP.gauss_ibp_cov hA (F := fun ψ : DField n k => ψ y)
    (differentiable_apply y) 1 1 x hsum hF'
  simp only [hfd, ContinuousLinearMap.proj_apply, gaussWeight_dirAction] at key
  rw [key, Finset.sum_eq_single y, scaledOp_inv hm]
  · simp [mul_assoc]
  · intro z _ hz
    simp [Pi.single_eq_of_ne (Ne.symm hz)]
  · simp

theorem dirWeight_integrable (m₀ : ℝ) (hm : m₀ ≠ 0) :
    Integrable (fun φ : DField n k => Real.exp (-(dirAction n k m₀ φ) / 2)) := by
  have := PP2GaussIBP.integrable_expAbs_mul_gaussWeight (scaledOp_posDef (n := n) (k := k) hm) 0
  simpa [gaussWeight_dirAction] using this

/-- The normalisation of the Dirichlet Gaussian weight is positive. -/
theorem dirWeight_integral_pos {m₀ : ℝ} (hm : m₀ ≠ 0) :
    0 < ∫ φ : DField n k, Real.exp (-(dirAction n k m₀ φ) / 2) :=
  integral_exp_pos (dirWeight_integrable m₀ hm)

/-- **The covariance of the Dirichlet free field:** with weight exp(−½ dirAction),
⟨φ x φ y⟩ = ε⁻² · dirGreen x y. -/
theorem gauss_cov {m₀ : ℝ} (hm : m₀ ≠ 0) (x y : DSite n k) :
    (∫ φ : DField n k, φ x * φ y * Real.exp (-(dirAction n k m₀ φ) / 2)) /
        (∫ φ : DField n k, Real.exp (-(dirAction n k m₀ φ) / 2)) =
      (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y := by
  rw [gauss_cov_unnorm hm, mul_div_assoc, div_self (dirWeight_integral_pos hm).ne', mul_one]

/-! ## Bounds and monotonicity in the mass -/

/-- **Diagonal bound:** dirGreen x x ≤ 1/m₀². -/
theorem dirGreen_diag_le {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) :
    dirGreen n k m₀ x x ≤ 1 / m₀ ^ 2 := by
  set g : DField n k := dirGreen n k m₀ *ᵥ Pi.single x 1 with hg
  have hDg : dirOp n k m₀ *ᵥ g = Pi.single x 1 := by
    rw [hg, mulVec_mulVec, dirOp_mul_dirGreen hm, one_mulVec]
  have hgx : g x = dirGreen n k m₀ x x := by simp [hg]
  have hq : g ⬝ᵥ dirOp n k m₀ *ᵥ g = g x := by
    rw [hDg, dotProduct_single, mul_one]
  have hge := dirOp_quad_ge m₀ g
  have hsq : g x ^ 2 ≤ ∑ z : DSite n k, g z ^ 2 :=
    Finset.single_le_sum (f := fun z => g z ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  have hpos : 0 < g x := hgx ▸ dirGreen_diag_pos hm x
  have hm2 : 0 < m₀ ^ 2 := by positivity
  have h1 : m₀ ^ 2 * g x ^ 2 ≤ g x := by
    calc m₀ ^ 2 * g x ^ 2 ≤ m₀ ^ 2 * ∑ z : DSite n k, g z ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hm2.le
      _ ≤ g ⬝ᵥ dirOp n k m₀ *ᵥ g := hge
      _ = g x := hq
  rw [← hgx, le_div_iff₀ hm2]
  nlinarith

theorem dirOp_sub (m₁ m₂ : ℝ) :
    dirOp n k m₂ - dirOp n k m₁ = (m₂ ^ 2 - m₁ ^ 2) • (1 : Matrix (DSite n k) (DSite n k) ℝ) := by
  simp only [dirOp, sub_smul]
  abel

/-- **Resolvent identity.** -/
theorem dirGreen_sub {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    dirGreen n k m₁ - dirGreen n k m₂ =
      (m₂ ^ 2 - m₁ ^ 2) • (dirGreen n k m₁ * dirGreen n k m₂) := by
  have e : dirGreen n k m₁ - dirGreen n k m₂ =
      dirGreen n k m₁ * (dirOp n k m₂ - dirOp n k m₁) * dirGreen n k m₂ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, dirOp_mul_dirGreen h₂, Matrix.mul_one,
      dirGreen_mul_dirOp h₁, Matrix.one_mul]
  rw [e, dirOp_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **Monotonicity in the mass:** the Green's function decreases entrywise as m₀² increases. -/
theorem dirGreen_antitone_mass {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h12 : m₁ ^ 2 ≤ m₂ ^ 2)
    (x y : DSite n k) : dirGreen n k m₂ x y ≤ dirGreen n k m₁ x y := by
  have h₂ : m₂ ≠ 0 := by
    intro h; subst h
    have : m₁ ^ 2 = 0 := le_antisymm (by simpa using h12) (sq_nonneg _)
    exact h₁ ((pow_eq_zero_iff two_ne_zero).mp this)
  have e := congrFun (congrFun (dirGreen_sub (n := n) (k := k) h₁ h₂) x) y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at e
  have hs : 0 ≤ ∑ z, dirGreen n k m₁ x z * dirGreen n k m₂ z y :=
    Finset.sum_nonneg fun z _ => mul_nonneg (dirGreen_nonneg h₁ x z) (dirGreen_nonneg h₂ z y)
  have : 0 ≤ (m₂ ^ 2 - m₁ ^ 2) * ∑ z, dirGreen n k m₁ x z * dirGreen n k m₂ z y :=
    mul_nonneg (by linarith) hs
  linarith

end PP2Target

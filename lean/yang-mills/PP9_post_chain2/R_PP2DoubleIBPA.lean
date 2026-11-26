import LongTable.P_mwwgf1nl_r5zhai
import LongTable.P_mwwgf25i_d0aeg1
import LongTable.R_PP2Region
import LongTable.R_PP2WickSplitB

/-!
Part A of PP2DoubleIBP (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2DoubleIBP.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5, I1 (double
integration by parts) and G3 (Wick monomials ordered at c ≠ the variance, free measure).

Setting. Generic part: ι a finite type, A positive definite, ρ_A = `PP2GaussIBP.gaussWeight A`,
E(φ) = exp(−λ e Σ_z :φ_z⁴:_c) (`dib_E`), W = ρ_A · E (`dib_W`), ⟨F⟩ = ∫ F W / ∫ W (`dib_ex`),
λ ≥ 0, e ≥ 0, any real c. Box instance: A = `scaledOp` = ε² dirOp, e = ε², c = freeVar, so
W = dweight … X⁴ (`dib_dweight_eq`) and ⟨·⟩ = `PP2Griffiths.dexpect` (`dib_dexpect_eq`);
covariance G = `dib_G` = ε⁻² dirGreen = scaledOp⁻¹. Region instance (ψ : B → ℝ, zero off B):
A = `rg_scaledOp B` = ε² regionOp B, G = `dib_GB` = ε⁻² regionGreen B; the weight of `regionTwoPt`
is a constant (from the sites off B) times W (`dib_qweight_zeroExt`), so the region expectation
`dib_rexpect` equals `dib_ex` (`dib_rexpect_eq`).

CONSTANTS. Our weight is λ ε² Σ :φ⁴: (not λ/4): ∂_z of it is 4λε² :φ_z³:. One IBP gives
4λε², and (:φ³:)' = 3 :φ²: gives 4·3 = 12 at the second; two factors 4λε² give 16λ²ε⁴, i.e.
16λ² ⟨F₁ F_g⟩ with the ε² inside F₁, F_g. So c₁ = 12, c₂ = 16; there are no further terms.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `dib_fderiv_F1`, `dib_fderiv_F2`: ∂_v(φ_u E) = E (v_u − λ φ_u D), ∂_v(:φ_y³: E) =
  E (3 :φ_y²: v_y − λ :φ_y³: D), D = e Σ_z 4 :φ_z³: v_z; growth bounds |·| ≤ C e^{2Σ|φ|}
  (E ≤ exp(6λe|ι|c²) since :y⁴: ≥ −6c²); `dib_integrable`.
* `dib_step1` / `dib_first_ibp`: ⟨φ_x φ_u⟩ = G(x,u) − 4λe Σ_y G(x,y) ⟨φ_u :φ_y³:⟩.
* `dib_step2` / `dib_second_ibp`: ⟨φ_u :φ_y³:⟩ = 3 G(u,y) ⟨:φ_y²:⟩ − 4λe Σ_z G(u,z) ⟨:φ_y³: :φ_z³:⟩.
* **`dib_double_ibp`** (generic), **`dib_double_ibp_box`**, **`dib_double_ibp_region`**
  (and `dib_double_ibp_region'`, sum over u ∈ B as a Finset sum): for t and g = G t,
  Σ_u t_u ⟨φ_x φ_u⟩ = g(x) − 12 λ ε² Σ_z g(z) G(x,z) ⟨:φ_z²:⟩ + 16 λ² ⟨F₁ F_g⟩,
  F₁ = ε² Σ_z G(x,z) :φ_z³:, F_g = ε² Σ_z g(z) :φ_z³:. Also unnormalised (`dib_double_ibp_unnorm`)
  and first/second IBP for box and generic.
* G3 (free measure ⟨·⟩₀ = `dib_ex0 A`, `dib_WW A c y y' j k` = ⟨:φ_y^j:_c :φ_{y'}^k:_c⟩₀):
  `dib_g3_step` (j ≤ 2, k ≤ 4): W(j+2,k) = −(j+1) δ_y W(j,k) + k C(y,y') W(j+1,k−1),
  δ_y = c − C(y,y), C = A⁻¹; `dib_g3_step'` (second slot); `dib_WW_0_0`, `dib_WW_1_0`, `dib_WW_0_1`,
  `dib_WW_1_1` (= C(y,y')); the full table `dib_WW_j_k`, j, k ≤ 4, as explicit polynomials in
  r = C(y,y'), δ_y, δ_{y'} (odd total degree: 0; e.g. (2,2): δδ' + 2r²;
  (4,4): 9δ²δ'² + 72r²δδ' + 24r⁴).
  Box: `dib_WW_box` (dexpect at λ = 0 is `dib_WW (scaledOp …)`), `dib_wick22_box`, `dib_wick44_box`
  with C = ε⁻² dirGreen and c = freeVar. Helpers: `dib_hasDerivAt_wick` ((wickPow c k)' =
  k wickPow c (k−1), k ≤ 4), `dib_wick_herm` (Hermite recursion, degree ≤ 4).

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

/-! ## One-variable facts -/

theorem dib_hasDerivAt_wick4 (c y : ℝ) :
    HasDerivAt (wickPow c 4) (4 * wickPow c 3 y) y := by
  have h : wickPow c 4 = fun y => y ^ 4 - 6 * c * y ^ 2 + 3 * c ^ 2 := by
    funext y; exact wickPow_four' c y
  rw [h, wickPow_three]
  have := ((hasDerivAt_pow 4 y).sub ((hasDerivAt_pow 2 y).const_mul (6 * c))).add_const
    (3 * c ^ 2)
  convert this using 1
  norm_num
  ring

theorem dib_hasDerivAt_wick3 (c y : ℝ) :
    HasDerivAt (wickPow c 3) (3 * wickPow c 2 y) y := by
  have h : wickPow c 3 = fun y => y ^ 3 - 3 * c * y := by
    funext y; exact wickPow_three c y
  rw [h, wickPow_two]
  have := (hasDerivAt_pow 3 y).sub ((hasDerivAt_id y).const_mul (3 * c))
  convert this using 1
  · funext z; simp
  · norm_num; ring

theorem dib_line {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y) (a d : ℝ) :
    HasDerivAt (fun t => f (a + t * d)) (f' a * d) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => a + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add a
  have h2 := (hf (a + 0 * d)).comp 0 h1
  simp only [zero_mul, add_zero] at h2
  exact h2

theorem dib_continuous_wick (c : ℝ) (j : ℕ) : Continuous (wickPow c j) := by
  unfold wickPow; fun_prop

theorem dib_differentiable_wick (c : ℝ) (j : ℕ) : Differentiable ℝ (wickPow c j) := by
  unfold wickPow; fun_prop

theorem dib_abs_pow_le (φ : ι → ℝ) (i : ι) (m : ℕ) :
    |φ i| ^ m ≤ m.factorial * Real.exp (∑ j, |φ j|) := by
  have h1 := Real.pow_div_factorial_le_exp _ (abs_nonneg (φ i)) m
  have h2 : |φ i| ≤ ∑ j, |φ j| :=
    Finset.single_le_sum (f := fun j => |φ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hf : (0 : ℝ) < m.factorial := by positivity
  rw [div_le_iff₀ hf] at h1
  calc |φ i| ^ m ≤ Real.exp |φ i| * m.factorial := h1
    _ ≤ Real.exp (∑ j, |φ j|) * m.factorial :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h2) hf.le
    _ = _ := mul_comm _ _

theorem dib_one_le_exp (φ : ι → ℝ) : 1 ≤ Real.exp (∑ j, |φ j|) :=
  Real.one_le_exp (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem dib_abs_le (φ : ι → ℝ) (i : ι) : |φ i| ≤ Real.exp (∑ j, |φ j|) := by
  simpa using dib_abs_pow_le φ i 1

theorem dib_abs_le' (φ : ι → ℝ) (i : ι) :
    |φ i| ≤ 1 * Real.exp (∑ j, |φ j|) := by
  rw [one_mul]; exact dib_abs_le φ i

theorem dib_wick3_le (c : ℝ) (φ : ι → ℝ) (i : ι) :
    |wickPow c 3 (φ i)| ≤ (6 + 3 * |c|) * Real.exp (∑ j, |φ j|) := by
  rw [wickPow_three]
  have h3 := dib_abs_pow_le φ i 3
  have h1 := dib_abs_le φ i
  have : |φ i ^ 3 - 3 * c * φ i| ≤ |φ i| ^ 3 + 3 * |c| * |φ i| := by
    calc |φ i ^ 3 - 3 * c * φ i| ≤ |φ i ^ 3| + |3 * c * φ i| := abs_sub _ _
      _ = _ := by rw [abs_pow, abs_mul, abs_mul]; norm_num
  have hc := abs_nonneg c
  simp only [Nat.factorial, Nat.succ_eq_add_one] at h3
  norm_num at h3
  nlinarith

theorem dib_wick2_le (c : ℝ) (φ : ι → ℝ) (i : ι) :
    |wickPow c 2 (φ i)| ≤ (2 + |c|) * Real.exp (∑ j, |φ j|) := by
  rw [wickPow_two]
  have h2 := dib_abs_pow_le φ i 2
  have h1 := dib_one_le_exp φ
  have : |φ i ^ 2 - c| ≤ |φ i| ^ 2 + |c| := by
    calc |φ i ^ 2 - c| ≤ |φ i ^ 2| + |c| := abs_sub _ _
      _ = _ := by rw [abs_pow]
  have hc := abs_nonneg c
  simp only [Nat.factorial, Nat.succ_eq_add_one] at h2
  norm_num at h2
  rw [sq_abs] at this
  nlinarith [mul_le_mul_of_nonneg_left h1 hc]


/-! ## The interaction factor and its derivatives (any finite index set ι) -/

/-- E φ = exp(−λ e Σ_z :φ_z⁴:_c) (e = ε² in the lattice instances). -/
def dib_E (e c lam : ℝ) (φ : ι → ℝ) : ℝ := Real.exp (-(lam * (e * ∑ z, wickPow c 4 (φ z))))

/-- The bound M = exp(6 λ e |ι| c²) of E (λ, e ≥ 0). -/
def dib_M (ι : Type*) [Fintype ι] (e c lam : ℝ) : ℝ :=
  Real.exp (lam * e * (Fintype.card ι * (6 * c ^ 2)))

/-- D φ v = e Σ_z 4 :φ_z³: v_z, the derivative of e Σ :φ⁴: along v. -/
def dib_D (e c : ℝ) (φ v : ι → ℝ) : ℝ := e * ∑ z, 4 * wickPow c 3 (φ z) * v z

/-- The interacting weight W = ρ_A · E. -/
def dib_W (A : Matrix ι ι ℝ) (e c lam : ℝ) (φ : ι → ℝ) : ℝ :=
  PP2GaussIBP.gaussWeight A φ * dib_E e c lam φ

/-- The normalised expectation ⟨F⟩ = ∫ F W / ∫ W. -/
def dib_ex (A : Matrix ι ι ℝ) (e c lam : ℝ) (F : (ι → ℝ) → ℝ) : ℝ :=
  (∫ φ, F φ * dib_W A e c lam φ) / ∫ φ, dib_W A e c lam φ

theorem dib_E_pos (e c lam : ℝ) (φ : ι → ℝ) : 0 < dib_E e c lam φ := Real.exp_pos _

theorem dib_E_le {e : ℝ} (he : 0 ≤ e) (c : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (φ : ι → ℝ) :
    dib_E e c lam φ ≤ dib_M ι e c lam := by
  unfold dib_E dib_M
  apply Real.exp_le_exp.mpr
  have hsum : -(Fintype.card ι * (6 * c ^ 2)) ≤ ∑ x, wickPow c 4 (φ x) := by
    have := Finset.sum_le_sum (s := Finset.univ)
      (fun x (_ : x ∈ Finset.univ) => (show -(6 * c ^ 2) ≤ wickPow c 4 (φ x) by
        rw [wickPow_four']; nlinarith [sq_nonneg (φ x ^ 2 - 3 * c)]))
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hc : 0 ≤ lam * e := mul_nonneg hlam he
  nlinarith [mul_le_mul_of_nonneg_left hsum hc]

theorem dib_continuous_E (e c lam : ℝ) : Continuous (dib_E (ι := ι) e c lam) := by
  unfold dib_E wickPow; fun_prop

theorem dib_differentiable_E (e c lam : ℝ) : Differentiable ℝ (dib_E (ι := ι) e c lam) := by
  unfold dib_E wickPow; fun_prop

theorem dib_continuous_W (A : Matrix ι ι ℝ) (e c lam : ℝ) : Continuous (dib_W A e c lam) :=
  (PP2GaussIBP.continuous_gaussWeight A).mul (dib_continuous_E e c lam)

theorem dib_W_pos (A : Matrix ι ι ℝ) (e c lam : ℝ) (φ : ι → ℝ) : 0 < dib_W A e c lam φ :=
  mul_pos (Real.exp_pos _) (dib_E_pos e c lam φ)

theorem dib_D_single (e c : ℝ) (φ : ι → ℝ) (w : ι) :
    dib_D e c φ (Pi.single w 1) = e * (4 * wickPow c 3 (φ w)) := by
  simp [dib_D, Pi.single_apply]

theorem dib_hasDerivAt_coord (φ v : ι → ℝ) (u : ι) :
    HasDerivAt (fun t : ℝ => (φ + t • v) u) (v u) 0 := by
  have e : (fun t : ℝ => (φ + t • v) u) = fun t => φ u + t * v u := by
    funext t; simp
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v u)).const_add (φ u)

theorem dib_hasDerivAt_E (e c lam : ℝ) (φ v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => dib_E e c lam (φ + t • v))
      (dib_E e c lam φ * (-(lam * dib_D e c φ v))) 0 := by
  have hV : HasDerivAt (fun t : ℝ => e * ∑ z, wickPow c 4 ((φ + t • v) z)) (dib_D e c φ v) 0 := by
    have e' : (fun t : ℝ => e * ∑ z, wickPow c 4 ((φ + t • v) z)) =
        fun t => e * ∑ z, wickPow c 4 (φ z + t * v z) := by
      funext t; simp
    rw [e']
    have hs : HasDerivAt (fun t : ℝ => ∑ z, wickPow c 4 (φ z + t * v z))
        (∑ z, 4 * wickPow c 3 (φ z) * v z) 0 :=
      HasDerivAt.fun_sum fun z _ => dib_line (dib_hasDerivAt_wick4 c) (φ z) (v z)
    exact hs.const_mul e
  have h := ((hV.const_mul lam).neg).exp
  convert h using 1
  · rfl
  · rw [Pi.neg_apply]
    simp only [zero_smul, add_zero, dib_E]

theorem dib_fderiv_eq {F : (ι → ℝ) → ℝ} (hF : Differentiable ℝ F) (φ v : ι → ℝ) {d : ℝ}
    (h : HasDerivAt (fun t : ℝ => F (φ + t • v)) d 0) : fderiv ℝ F φ v = d :=
  HasDerivAt.unique ((hF φ).hasFDerivAt.hasLineDerivAt v) h

theorem dib_differentiable_F1 (e c lam : ℝ) (u : ι) :
    Differentiable ℝ (fun ψ : ι → ℝ => ψ u * dib_E e c lam ψ) :=
  (differentiable_apply u).mul (dib_differentiable_E e c lam)

theorem dib_differentiable_F2 (e c lam : ℝ) (y : ι) :
    Differentiable ℝ (fun ψ : ι → ℝ => wickPow c 3 (ψ y) * dib_E e c lam ψ) :=
  ((dib_differentiable_wick c 3).comp (differentiable_apply y)).mul (dib_differentiable_E e c lam)

/-- ∂_v (φ_u E) = E · (v_u − λ φ_u D(φ, v)). -/
theorem dib_fderiv_F1 (e c lam : ℝ) (u : ι) (φ v : ι → ℝ) :
    fderiv ℝ (fun ψ : ι → ℝ => ψ u * dib_E e c lam ψ) φ v =
      dib_E e c lam φ * (v u - lam * (φ u * dib_D e c φ v)) := by
  rw [dib_fderiv_eq (dib_differentiable_F1 e c lam u) φ v
    ((dib_hasDerivAt_coord φ v u).mul (dib_hasDerivAt_E e c lam φ v))]
  simp only [zero_smul, add_zero]
  ring

/-- ∂_v (:φ_y³: E) = E · (3 :φ_y²: v_y − λ :φ_y³: D(φ, v)). -/
theorem dib_fderiv_F2 (e c lam : ℝ) (y : ι) (φ v : ι → ℝ) :
    fderiv ℝ (fun ψ : ι → ℝ => wickPow c 3 (ψ y) * dib_E e c lam ψ) φ v =
      dib_E e c lam φ * (3 * wickPow c 2 (φ y) * v y
        - lam * (wickPow c 3 (φ y) * dib_D e c φ v)) := by
  have h1 : HasDerivAt (fun t : ℝ => wickPow c 3 ((φ + t • v) y))
      (3 * wickPow c 2 (φ y) * v y) 0 := by
    have e' : (fun t : ℝ => wickPow c 3 ((φ + t • v) y)) =
        fun t => wickPow c 3 (φ y + t * v y) := by
      funext t; simp
    rw [e']
    exact dib_line (dib_hasDerivAt_wick3 c) (φ y) (v y)
  rw [dib_fderiv_eq (dib_differentiable_F2 e c lam y) φ v
    (h1.mul (dib_hasDerivAt_E e c lam φ v))]
  simp only [zero_smul, add_zero]
  ring

/-! ## Growth bounds and integrability -/

theorem dib_exp_two (φ : ι → ℝ) :
    Real.exp (2 * ∑ j, |φ j|) = Real.exp (∑ j, |φ j|) * Real.exp (∑ j, |φ j|) := by
  rw [two_mul, Real.exp_add]

theorem dib_one_le_e2 (φ : ι → ℝ) : 1 ≤ Real.exp (2 * ∑ j, |φ j|) := by
  have := dib_one_le_exp φ
  rw [dib_exp_two]; nlinarith

theorem dib_lift {p P : ℝ} (hP : 0 ≤ P) (φ : ι → ℝ) (hp : |p| ≤ P * Real.exp (∑ j, |φ j|)) :
    |p| ≤ P * Real.exp (2 * ∑ j, |φ j|) := by
  have h1 := dib_one_le_exp φ
  rw [dib_exp_two]
  calc |p| ≤ P * Real.exp (∑ j, |φ j|) := hp
    _ ≤ P * (Real.exp (∑ j, |φ j|) * Real.exp (∑ j, |φ j|)) := by
        apply mul_le_mul_of_nonneg_left _ hP; nlinarith

theorem dib_mul_bnd {p q P Q : ℝ} (φ : ι → ℝ) (hp : |p| ≤ P * Real.exp (∑ j, |φ j|))
    (hq : |q| ≤ Q * Real.exp (∑ j, |φ j|)) :
    |p * q| ≤ (P * Q) * Real.exp (2 * ∑ j, |φ j|) := by
  rw [abs_mul, dib_exp_two]
  calc |p| * |q| ≤ (P * Real.exp (∑ j, |φ j|)) * (Q * Real.exp (∑ j, |φ j|)) :=
        mul_le_mul hp hq (abs_nonneg _) (le_trans (abs_nonneg _) hp)
    _ = _ := by ring

theorem dib_E_mul_bnd {e : ℝ} (he : 0 ≤ e) (c : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (φ : ι → ℝ)
    {p Q : ℝ} (hp : |p| ≤ Q * Real.exp (2 * ∑ j, |φ j|)) :
    |dib_E e c lam φ * p| ≤ (dib_M ι e c lam * Q) * Real.exp (2 * ∑ j, |φ j|) := by
  rw [abs_mul, abs_of_pos (dib_E_pos e c lam φ)]
  calc dib_E e c lam φ * |p| ≤ dib_M ι e c lam * (Q * Real.exp (2 * ∑ j, |φ j|)) :=
        mul_le_mul (dib_E_le he c hlam φ) hp (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

theorem dib_abs_scaled (lam e a b : ℝ) (hl : 0 ≤ lam) (he : 0 ≤ e) :
    |lam * (a * (e * (4 * b)))| = 4 * (lam * e) * (|a| * |b|) := by
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hl, abs_of_nonneg he]
  norm_num
  ring

theorem dib_single_abs_le (y u : ι) : |(Pi.single y (1 : ℝ) : ι → ℝ) u| ≤ 1 := by
  rw [Pi.single_apply]; split_ifs <;> norm_num

/-- Integrability against W of anything continuous bounded by K · exp(2 Σ|φ|). -/
theorem dib_integrable {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) {h : (ι → ℝ) → ℝ} (hc : Continuous h) (K : ℝ)
    (hle : ∀ φ, |h φ| ≤ K * Real.exp (2 * ∑ j, |φ j|)) :
    Integrable (fun φ => h φ * dib_W A e c lam φ) := by
  refine PP2GaussIBP.integrable_of_le_expAbs hA
    (hc.mul (dib_continuous_W A e c lam)).aestronglyMeasurable
    (K * dib_M ι e c lam) 2 (fun φ => ?_)
  have hρ := PP2GaussIBP.gaussWeight_nonneg A φ
  rw [dib_W, abs_mul, abs_of_nonneg (mul_nonneg hρ (dib_E_pos _ _ _ φ).le)]
  calc |h φ| * (PP2GaussIBP.gaussWeight A φ * dib_E e c lam φ)
      ≤ (K * Real.exp (2 * ∑ j, |φ j|)) * (PP2GaussIBP.gaussWeight A φ * dib_M ι e c lam) :=
        mul_le_mul (hle φ) (mul_le_mul_of_nonneg_left (dib_E_le he c hlam φ) hρ)
          (mul_nonneg hρ (dib_E_pos _ _ _ φ).le) (le_trans (abs_nonneg _) (hle φ))
    _ = _ := by ring

theorem dib_integrable_W {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) : Integrable (dib_W A e c lam) := by
  have := dib_integrable hA he c hlam (h := fun _ => 1) continuous_const 1
    (fun φ => by simpa using dib_one_le_e2 φ)
  simpa using this

theorem dib_integral_W_pos {A : Matrix ι ι ℝ} (hA : A.PosDef) {e : ℝ} (he : 0 ≤ e) (c : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) : 0 < ∫ φ, dib_W A e c lam φ := by
  rw [integral_pos_iff_support_of_nonneg (fun φ => (dib_W_pos A e c lam φ).le)
    (dib_integrable_W hA he c hlam)]
  have : Function.support (dib_W A e c lam) = Set.univ := by
    ext φ; simp [(dib_W_pos A e c lam φ).ne']
  rw [this]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

theorem dib_inv_symm {A : Matrix ι ι ℝ} (hA : A.PosDef) (a b : ι) : A⁻¹ a b = A⁻¹ b a := by
  have h : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, PP2GaussIBP.transpose_eq hA]
  rw [← transpose_apply A⁻¹ b a, h]

/-! ## The two integrations by parts (unnormalised) -/

theorem dib_alg1 (a : ι → ℝ) (u : ι) (Z L : ℝ) (I : ι → ℝ) :
    ∑ y, a y * ((Pi.single y (1 : ℝ) : ι → ℝ) u * Z - L * I y) = a u * Z - L * ∑ y, a y * I y := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single u]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring

end PP2DoubleIBP

end

import LongTable.PP2Green2
import LongTable.PP2Griffiths3
import LongTable.PP2Region
import LongTable.PP2WickSplit

/-!
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

/-! ## Instance 2: a region B ⊆ box (fields zero off B, covariance ε⁻² regionGreen B) -/

section Region

variable {n k : ℕ}

/-- The free region covariance C_B = ε⁻² · regionGreen B. -/
def dib_GB (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) : Matrix {x // x ∈ B} {x // x ∈ B} ℝ :=
  (spacing n ^ 2)⁻¹ • regionGreen n k m₀ B

theorem dib_GB_eq {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) :
    dib_GB n k m₀ B = (rg_scaledOp n k m₀ B)⁻¹ :=
  (rg_scaledOp_inv hm B).symm

/-- The expectation of the region measure of `regionTwoPt` (weight qweight (zeroExt B ψ) on ℝ^B). -/
def dib_rexpect (n k : ℕ) (m₀ lam : ℝ) (B : Finset (DSite n k))
    (F : ({z // z ∈ B} → ℝ) → ℝ) : ℝ :=
  (∫ ψ : {z // z ∈ B} → ℝ, F ψ * qweight n k m₀ lam (zeroExt B ψ)) /
    ∫ ψ : {z // z ∈ B} → ℝ, qweight n k m₀ lam (zeroExt B ψ)

theorem dib_sum_zeroExt (B : Finset (DSite n k)) (ψ : {z // z ∈ B} → ℝ) (f : ℝ → ℝ) :
    ∑ x : DSite n k, f (zeroExt B ψ x) = ∑ a : {z // z ∈ B}, f (ψ a) + ∑ _x ∈ Bᶜ, f 0 := by
  rw [← Finset.sum_add_sum_compl B]
  congr 1
  · rw [← Finset.sum_coe_sort B]
    exact Finset.sum_congr rfl fun a _ => by rw [rg_zeroExt_apply]
  · exact Finset.sum_congr rfl fun x hx => by simp [zeroExt, Finset.mem_compl.mp hx]

/-- The region weight is a constant times the generic weight W on ℝ^B. -/
theorem dib_qweight_zeroExt (m₀ lam : ℝ) (B : Finset (DSite n k)) (ψ : {z // z ∈ B} → ℝ) :
    qweight n k m₀ lam (zeroExt B ψ) =
      Real.exp (-(lam * spacing n ^ 2 * ∑ _x ∈ Bᶜ, wickPow (freeVar n m₀) 4 0)) *
        dib_W (rg_scaledOp n k m₀ B) (spacing n ^ 2) (freeVar n m₀) lam ψ := by
  have hw : ∀ y, wickPoly (Polynomial.X ^ 4) (freeVar n m₀) y = wickPow (freeVar n m₀) 4 y :=
    fun y => by rw [wickPoly_X4, wickPow_four']
  rw [qweight, dweight, dib_W, PP2GaussIBP.gaussWeight, dib_E, ← Real.exp_add, ← Real.exp_add,
    dirAction_zeroExt, rg_scaledOp, smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [hw]
  rw [dib_sum_zeroExt B ψ (wickPow (freeVar n m₀) 4)]
  ring

theorem dib_rexpect_eq (m₀ lam : ℝ) (B : Finset (DSite n k)) (F : ({z // z ∈ B} → ℝ) → ℝ) :
    dib_rexpect n k m₀ lam B F =
      dib_ex (rg_scaledOp n k m₀ B) (spacing n ^ 2) (freeVar n m₀) lam F := by
  simp only [dib_rexpect, dib_ex, dib_qweight_zeroExt]
  set K := Real.exp (-(lam * spacing n ^ 2 * ∑ _x ∈ Bᶜ, wickPow (freeVar n m₀) 4 0))
  have h : ∀ ψ : {z // z ∈ B} → ℝ,
      F ψ * (K * dib_W (rg_scaledOp n k m₀ B) (spacing n ^ 2) (freeVar n m₀) lam ψ) =
        K * (F ψ * dib_W (rg_scaledOp n k m₀ B) (spacing n ^ 2) (freeVar n m₀) lam ψ) :=
    fun ψ => mul_left_comm _ _ _
  simp_rw [h, integral_const_mul]
  rw [mul_div_mul_left _ _ (Real.exp_pos _).ne']

theorem dib_regionTwoPt_eq (m₀ lam : ℝ) (B : Finset (DSite n k)) (a u : {z // z ∈ B}) :
    regionTwoPt n k m₀ lam B a u = dib_rexpect n k m₀ lam B (fun ψ => ψ a * ψ u) := by
  simp only [regionTwoPt, dib_rexpect, rg_zeroExt_apply]

/-- **I1, double integration by parts (region B).** For t : B → ℝ, a ∈ B and g := C_B t,
C_B = ε⁻² regionGreen B, in the region measure of `regionTwoPt` (Wick order at c = freeVar):
Σ_u t_u regionTwoPt(a, u) = g(a) − 12 λ ε² Σ_z g(z) C_B(a,z) ⟨:ψ_z²:⟩_B + 16 λ² ⟨F₁ F_g⟩_B,
F₁ = ε² Σ_z C_B(a,z) :ψ_z³:, F_g = ε² Σ_z g(z) :ψ_z³:. -/
theorem dib_double_ibp_region {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (B : Finset (DSite n k)) (t : {z // z ∈ B} → ℝ) (a : {z // z ∈ B}) :
    ∑ u, t u * regionTwoPt n k m₀ lam B a u =
      (dib_GB n k m₀ B *ᵥ t) a
      - 12 * lam * spacing n ^ 2 * ∑ z, (dib_GB n k m₀ B *ᵥ t) z * dib_GB n k m₀ B a z *
          dib_rexpect n k m₀ lam B (fun ψ => wickPow (freeVar n m₀) 2 (ψ z))
      + 16 * lam ^ 2 * dib_rexpect n k m₀ lam B (fun ψ =>
          (spacing n ^ 2 * ∑ z, dib_GB n k m₀ B a z * wickPow (freeVar n m₀) 3 (ψ z)) *
          (spacing n ^ 2 * ∑ z, (dib_GB n k m₀ B *ᵥ t) z * wickPow (freeVar n m₀) 3 (ψ z))) := by
  simp only [dib_regionTwoPt_eq, dib_rexpect_eq, dib_GB_eq hm]
  exact dib_double_ibp (rg_scaledOp_posDef hm B) (by positivity) _ hlam t a

/-- The same with the sum over u ∈ B written as a Finset sum over box sites (plan's form). -/
theorem dib_double_ibp_region' {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (B : Finset (DSite n k)) (t : DSite n k → ℝ) {x : DSite n k} (hx : x ∈ B) :
    ∑ u ∈ B, t u * regionTwoPt n k m₀ lam B x u =
      (dib_GB n k m₀ B *ᵥ fun a => t a) ⟨x, hx⟩
      - 12 * lam * spacing n ^ 2 * ∑ z, (dib_GB n k m₀ B *ᵥ fun a => t a) z *
          dib_GB n k m₀ B ⟨x, hx⟩ z *
          dib_rexpect n k m₀ lam B (fun ψ => wickPow (freeVar n m₀) 2 (ψ z))
      + 16 * lam ^ 2 * dib_rexpect n k m₀ lam B (fun ψ =>
          (spacing n ^ 2 * ∑ z, dib_GB n k m₀ B ⟨x, hx⟩ z * wickPow (freeVar n m₀) 3 (ψ z)) *
          (spacing n ^ 2 * ∑ z, (dib_GB n k m₀ B *ᵥ fun a => t a) z *
            wickPow (freeVar n m₀) 3 (ψ z))) := by
  rw [← Finset.sum_coe_sort B]
  exact dib_double_ibp_region hm hlam B (fun a => t a) ⟨x, hx⟩

end Region


/-! ## G3: Wick monomials at a constant c ≠ variance under the free (Gaussian) measure -/

section G3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dib_wick4_le (c : ℝ) (φ : ι → ℝ) (i : ι) :
    |wickPow c 4 (φ i)| ≤ (24 + 12 * |c| + 3 * c ^ 2) * Real.exp (∑ j, |φ j|) := by
  rw [wickPow_four']
  have h4 := dib_abs_pow_le φ i 4
  have h2 := dib_abs_pow_le φ i 2
  have h1 := dib_one_le_exp φ
  have : |φ i ^ 4 - 6 * c * φ i ^ 2 + 3 * c ^ 2| ≤ |φ i| ^ 4 + 6 * |c| * |φ i| ^ 2 + 3 * c ^ 2 := by
    calc |φ i ^ 4 - 6 * c * φ i ^ 2 + 3 * c ^ 2|
        ≤ |φ i ^ 4 - 6 * c * φ i ^ 2| + |3 * c ^ 2| := abs_add_le _ _
      _ ≤ |φ i ^ 4| + |6 * c * φ i ^ 2| + |3 * c ^ 2| := by
          gcongr; exact abs_sub _ _
      _ = _ := by
          rw [abs_pow, abs_mul, abs_mul, abs_pow,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * c ^ 2)]
          norm_num
  simp only [Nat.factorial, Nat.succ_eq_add_one] at h4 h2
  norm_num at h4 h2
  rw [sq_abs] at this
  have hc := abs_nonneg c
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 6 * |c|),
    mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 * c ^ 2)]

/-- Growth of the Wick powers of degree ≤ 4. -/
theorem dib_wick_bnd (c : ℝ) {m : ℕ} (hm : m ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (φ : ι → ℝ) (i : ι), |wickPow c m (φ i)| ≤ K * Real.exp (∑ j, |φ j|) := by
  interval_cases m
  · exact ⟨1, zero_le_one, fun φ i => by
      rw [wickPow_zero', one_mul, abs_one]; exact dib_one_le_exp φ⟩
  · exact ⟨1, zero_le_one, fun φ i => by rw [wickPow_one]; exact dib_abs_le' φ i⟩
  · exact ⟨2 + |c|, by positivity, fun φ i => dib_wick2_le c φ i⟩
  · exact ⟨6 + 3 * |c|, by positivity, fun φ i => dib_wick3_le c φ i⟩
  · exact ⟨24 + 12 * |c| + 3 * c ^ 2, by positivity, fun φ i => dib_wick4_le c φ i⟩

/-- (wickPow c k)' = k · wickPow c (k − 1), for k ≤ 4. -/
theorem dib_hasDerivAt_wick (c : ℝ) {k : ℕ} (hk : k ≤ 4) (y : ℝ) :
    HasDerivAt (wickPow c k) ((k : ℝ) * wickPow c (k - 1) y) y := by
  interval_cases k
  · have h : wickPow c 0 = fun _ => 1 := by funext y; exact wickPow_zero' c y
    rw [h]; simpa using hasDerivAt_const y (1 : ℝ)
  · have h : wickPow c 1 = fun y => y := by funext y; exact wickPow_one c y
    rw [h, wickPow_zero']; simpa using hasDerivAt_id' y
  · have h : wickPow c 2 = fun y => y ^ 2 - c := by funext y; exact wickPow_two c y
    rw [h, wickPow_one]
    have := (hasDerivAt_pow 2 y).sub_const c
    convert this using 1; norm_num
  · simpa using dib_hasDerivAt_wick3 c y
  · simpa using dib_hasDerivAt_wick4 c y

/-- Hermite recursion :y^(j+2):_c = y :y^(j+1):_c − (j+1) c :y^j:_c, for j ≤ 2. -/
theorem dib_wick_herm (c : ℝ) {j : ℕ} (hj : j ≤ 2) (y : ℝ) :
    wickPow c (j + 2) y = y * wickPow c (j + 1) y - ((j : ℝ) + 1) * c * wickPow c j y := by
  interval_cases j
  · simp only [Nat.reduceAdd, wickPow_two, wickPow_one, wickPow_zero']; push_cast; ring
  · simp only [Nat.reduceAdd, wickPow_three, wickPow_two, wickPow_one]; push_cast; ring
  · simp only [Nat.reduceAdd, wickPow_four', wickPow_three, wickPow_two]; push_cast; ring

/-- The free (λ = 0) Gaussian expectation ⟨F⟩₀ = ∫ F ρ_A / ∫ ρ_A. -/
def dib_ex0 (A : Matrix ι ι ℝ) (F : (ι → ℝ) → ℝ) : ℝ :=
  (∫ φ, F φ * PP2GaussIBP.gaussWeight A φ) / ∫ φ, PP2GaussIBP.gaussWeight A φ

/-- E₀[:φ_y^j:_c :φ_{y'}^k:_c]. -/
def dib_WW (A : Matrix ι ι ℝ) (c : ℝ) (y y' : ι) (j k : ℕ) : ℝ :=
  dib_ex0 A (fun φ => wickPow c j (φ y) * wickPow c k (φ y'))

theorem dib_W_zero (A : Matrix ι ι ℝ) (e c : ℝ) (φ : ι → ℝ) :
    dib_W A e c 0 φ = PP2GaussIBP.gaussWeight A φ := by
  simp [dib_W, dib_E]

theorem dib_integrable0 {A : Matrix ι ι ℝ} (hA : A.PosDef) {h : (ι → ℝ) → ℝ} (hc : Continuous h)
    (K : ℝ) (hle : ∀ φ, |h φ| ≤ K * Real.exp (2 * ∑ j, |φ j|)) :
    Integrable (fun φ => h φ * PP2GaussIBP.gaussWeight A φ) := by
  have := dib_integrable hA le_rfl 0 le_rfl hc K hle
  simpa [dib_W_zero] using this

theorem dib_integral_gauss_pos {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    0 < ∫ φ, PP2GaussIBP.gaussWeight A φ := by
  have := dib_integral_W_pos hA le_rfl 0 (lam := 0) le_rfl
  simpa [dib_W_zero] using this

theorem dib_alg3 (a : ι → ℝ) (y y' : ι) (P Q : ℝ) :
    ∑ z, a z * ((Pi.single z (1 : ℝ) : ι → ℝ) y * P + (Pi.single z (1 : ℝ) : ι → ℝ) y' * Q) =
      a y * P + a y' * Q := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [Finset.sum_eq_single y']
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp

/-- **G3 recursion (unnormalised)**: for j ≤ 2, k ≤ 4,
∫ :φ_y^(j+2): :φ_{y'}^k: ρ = −(j+1) δ_y ∫ :φ_y^j: :φ_{y'}^k: ρ
  + k C(y,y') ∫ :φ_y^(j+1): :φ_{y'}^(k−1): ρ,
C = A⁻¹, δ_y = c − C(y,y), all Wick powers at the same constant c. -/
theorem dib_g3_step_unnorm {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) {j k : ℕ}
    (hj : j ≤ 2) (hk : k ≤ 4) :
    ∫ φ, wickPow c (j + 2) (φ y) * wickPow c k (φ y') * PP2GaussIBP.gaussWeight A φ =
      -(((j : ℝ) + 1) * (c - A⁻¹ y y)) *
          (∫ φ, wickPow c j (φ y) * wickPow c k (φ y') * PP2GaussIBP.gaussWeight A φ)
        + (k : ℝ) * A⁻¹ y y' *
          ∫ φ, wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y') *
            PP2GaussIBP.gaussWeight A φ := by
  obtain ⟨Kj, hKj, bj⟩ := dib_wick_bnd (ι := ι) c (m := j) (by omega)
  obtain ⟨Kj1, hKj1, bj1⟩ := dib_wick_bnd (ι := ι) c (m := j + 1) (by omega)
  obtain ⟨Kk, hKk, bk⟩ := dib_wick_bnd (ι := ι) c (m := k) hk
  obtain ⟨Kk1, hKk1, bk1⟩ := dib_wick_bnd (ι := ι) c (m := k - 1) (by omega)
  set F : (ι → ℝ) → ℝ := fun ψ => wickPow c (j + 1) (ψ y) * wickPow c k (ψ y') with hFdef
  have hFd : Differentiable ℝ F :=
    ((dib_differentiable_wick c _).comp (differentiable_apply y)).mul
      ((dib_differentiable_wick c _).comp (differentiable_apply y'))
  have hder : ∀ φ v : ι → ℝ, fderiv ℝ F φ v =
      v y * (((j : ℝ) + 1) * (wickPow c j (φ y) * wickPow c k (φ y')))
        + v y' * ((k : ℝ) * (wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y'))) := by
    intro φ v
    have h1 : HasDerivAt (fun t : ℝ => wickPow c (j + 1) ((φ + t • v) y))
        (((j + 1 : ℕ) : ℝ) * wickPow c (j + 1 - 1) (φ y) * v y) 0 := by
      have e' : (fun t : ℝ => wickPow c (j + 1) ((φ + t • v) y)) =
          fun t => wickPow c (j + 1) (φ y + t * v y) := by funext t; simp
      rw [e']
      exact dib_line (fun z => dib_hasDerivAt_wick c (k := j + 1) (by omega) z) (φ y) (v y)
    have h2 : HasDerivAt (fun t : ℝ => wickPow c k ((φ + t • v) y'))
        ((k : ℝ) * wickPow c (k - 1) (φ y') * v y') 0 := by
      have e' : (fun t : ℝ => wickPow c k ((φ + t • v) y')) =
          fun t => wickPow c k (φ y' + t * v y') := by funext t; simp
      rw [e']
      exact dib_line (fun z => dib_hasDerivAt_wick c hk z) (φ y') (v y')
    rw [dib_fderiv_eq hFd φ v (h1.mul h2)]
    simp only [zero_smul, add_zero, Nat.add_sub_cancel]
    push_cast
    ring
  have hj1 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  set C := Kj1 * Kk + ((j : ℝ) + 1) * (Kj * Kk) + (k : ℝ) * (Kj1 * Kk1) with hC
  have hF : ∀ φ : ι → ℝ, |F φ| ≤ C * Real.exp (2 * ∑ i, |φ i|) := by
    intro φ
    have h := dib_mul_bnd φ (bj1 φ y) (bk φ y')
    have h1 := dib_one_le_e2 φ
    have : 0 ≤ (((j : ℝ) + 1) * (Kj * Kk) + (k : ℝ) * (Kj1 * Kk1)) *
        Real.exp (2 * ∑ i, |φ i|) := by positivity
    simp only [hFdef]
    nlinarith
  have hF' : ∀ (z : ι) (φ : ι → ℝ), |fderiv ℝ F φ (Pi.single z 1)| ≤
      C * Real.exp (2 * ∑ i, |φ i|) := by
    intro z φ
    rw [hder]
    have ha := dib_mul_bnd φ (bj φ y) (bk φ y')
    have hb := dib_mul_bnd φ (bj1 φ y) (bk1 φ y')
    have hs1 := dib_single_abs_le z y
    have hs2 := dib_single_abs_le z y'
    have e1 : |(Pi.single z (1 : ℝ) : ι → ℝ) y * (((j : ℝ) + 1) *
        (wickPow c j (φ y) * wickPow c k (φ y')))| ≤
        ((j : ℝ) + 1) * (Kj * Kk) * Real.exp (2 * ∑ i, |φ i|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hj1]
      calc |(Pi.single z (1 : ℝ) : ι → ℝ) y| * (((j : ℝ) + 1) *
            |wickPow c j (φ y) * wickPow c k (φ y')|)
          ≤ 1 * (((j : ℝ) + 1) * ((Kj * Kk) * Real.exp (2 * ∑ i, |φ i|))) :=
            mul_le_mul hs1 (mul_le_mul_of_nonneg_left ha hj1) (by positivity) zero_le_one
        _ = _ := by ring
    have e2 : |(Pi.single z (1 : ℝ) : ι → ℝ) y' * ((k : ℝ) *
        (wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y')))| ≤
        (k : ℝ) * (Kj1 * Kk1) * Real.exp (2 * ∑ i, |φ i|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk0]
      calc |(Pi.single z (1 : ℝ) : ι → ℝ) y'| * ((k : ℝ) *
            |wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y')|)
          ≤ 1 * ((k : ℝ) * ((Kj1 * Kk1) * Real.exp (2 * ∑ i, |φ i|))) :=
            mul_le_mul hs2 (mul_le_mul_of_nonneg_left hb hk0) (by positivity) zero_le_one
        _ = _ := by ring
    have hadd := abs_add_le ((Pi.single z (1 : ℝ) : ι → ℝ) y * (((j : ℝ) + 1) *
        (wickPow c j (φ y) * wickPow c k (φ y'))))
      ((Pi.single z (1 : ℝ) : ι → ℝ) y' * ((k : ℝ) *
        (wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y'))))
    have : 0 ≤ Kj1 * Kk * Real.exp (2 * ∑ i, |φ i|) := by positivity
    rw [hC]
    nlinarith
  have key := PP2GaussIBP.gauss_ibp_cov hA hFd C 2 y hF hF'
  have hintA : Integrable (fun φ : ι → ℝ => wickPow c j (φ y) * wickPow c k (φ y') *
      PP2GaussIBP.gaussWeight A φ) :=
    dib_integrable0 hA (((dib_continuous_wick c _).comp (continuous_apply y)).mul
      ((dib_continuous_wick c _).comp (continuous_apply y'))) (Kj * Kk)
      (fun φ => dib_mul_bnd φ (bj φ y) (bk φ y'))
  have hintB : Integrable (fun φ : ι → ℝ => wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y') *
      PP2GaussIBP.gaussWeight A φ) :=
    dib_integrable0 hA (((dib_continuous_wick c _).comp (continuous_apply y)).mul
      ((dib_continuous_wick c _).comp (continuous_apply y'))) (Kj1 * Kk1)
      (fun φ => dib_mul_bnd φ (bj1 φ y) (bk1 φ y'))
  have hintL : Integrable (fun φ : ι → ℝ => φ y * F φ * PP2GaussIBP.gaussWeight A φ) := by
    refine PP2GaussIBP.integrable_of_le_expAbs hA ?_ C 3 (fun φ => ?_)
    · exact (((continuous_apply y).mul hFd.continuous).mul
        (PP2GaussIBP.continuous_gaussWeight A)).aestronglyMeasurable
    · have hρ := PP2GaussIBP.gaussWeight_nonneg A φ
      rw [abs_mul, abs_mul, abs_of_nonneg hρ]
      have h3 : Real.exp (3 * ∑ i, |φ i|) =
          Real.exp (∑ i, |φ i|) * Real.exp (2 * ∑ i, |φ i|) := by
        rw [← Real.exp_add]; ring_nf
      have := mul_le_mul (dib_abs_le φ y) (hF φ) (abs_nonneg _) (Real.exp_pos _).le
      calc |φ y| * |F φ| * PP2GaussIBP.gaussWeight A φ
          ≤ Real.exp (∑ i, |φ i|) * (C * Real.exp (2 * ∑ i, |φ i|)) *
              PP2GaussIBP.gaussWeight A φ := mul_le_mul_of_nonneg_right this hρ
        _ = _ := by rw [h3]; ring
  have eH : (fun φ : ι → ℝ => wickPow c (j + 2) (φ y) * wickPow c k (φ y') *
      PP2GaussIBP.gaussWeight A φ) = fun φ => φ y * F φ * PP2GaussIBP.gaussWeight A φ
        - (((j : ℝ) + 1) * c) *
          (wickPow c j (φ y) * wickPow c k (φ y') * PP2GaussIBP.gaussWeight A φ) := by
    funext φ
    rw [dib_wick_herm c hj, hFdef]
    ring
  have eR : ∀ z : ι, ∫ φ, fderiv ℝ F φ (Pi.single z 1) * PP2GaussIBP.gaussWeight A φ =
      (Pi.single z (1 : ℝ) : ι → ℝ) y * (((j : ℝ) + 1) *
          ∫ φ, wickPow c j (φ y) * wickPow c k (φ y') * PP2GaussIBP.gaussWeight A φ)
        + (Pi.single z (1 : ℝ) : ι → ℝ) y' * ((k : ℝ) *
          ∫ φ, wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y') *
            PP2GaussIBP.gaussWeight A φ) := by
    intro z
    have e' : (fun φ : ι → ℝ => fderiv ℝ F φ (Pi.single z 1) * PP2GaussIBP.gaussWeight A φ) =
        fun φ => ((Pi.single z (1 : ℝ) : ι → ℝ) y * ((j : ℝ) + 1)) *
            (wickPow c j (φ y) * wickPow c k (φ y') * PP2GaussIBP.gaussWeight A φ)
          + ((Pi.single z (1 : ℝ) : ι → ℝ) y' * (k : ℝ)) *
            (wickPow c (j + 1) (φ y) * wickPow c (k - 1) (φ y') * PP2GaussIBP.gaussWeight A φ) := by
      funext φ
      rw [hder]
      ring
    rw [e', integral_add (hintA.const_mul _) (hintB.const_mul _), integral_const_mul,
      integral_const_mul]
    ring
  rw [eH, integral_sub hintL (hintA.const_mul _), integral_const_mul, key]
  simp_rw [eR]
  rw [dib_alg3]
  ring


/-- **G3 recursion**: E₀[:φ_y^(j+2): :φ_{y'}^k:] = −(j+1) δ_y E₀[:φ_y^j: :φ_{y'}^k:]
+ k C(y,y') E₀[:φ_y^(j+1): :φ_{y'}^(k−1):], C = A⁻¹, δ_y = c − C(y,y), j ≤ 2, k ≤ 4. -/
theorem dib_g3_step {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) {j k : ℕ}
    (hj : j ≤ 2) (hk : k ≤ 4) :
    dib_WW A c y y' (j + 2) k =
      -(((j : ℝ) + 1) * (c - A⁻¹ y y)) * dib_WW A c y y' j k
        + (k : ℝ) * A⁻¹ y y' * dib_WW A c y y' (j + 1) (k - 1) := by
  simp only [dib_WW, dib_ex0]
  rw [dib_g3_step_unnorm hA c y y' hj hk, add_div, mul_div_assoc, mul_div_assoc]

theorem dib_WW_swap (A : Matrix ι ι ℝ) (c : ℝ) (y y' : ι) (j k : ℕ) :
    dib_WW A c y y' j k = dib_WW A c y' y k j := by
  simp only [dib_WW, dib_ex0]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun φ => by ring)

/-- The same recursion in the second slot. -/
theorem dib_g3_step' {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) {j k : ℕ}
    (hj : j ≤ 4) (hk : k ≤ 2) :
    dib_WW A c y y' j (k + 2) =
      -(((k : ℝ) + 1) * (c - A⁻¹ y' y')) * dib_WW A c y y' j k
        + (j : ℝ) * A⁻¹ y y' * dib_WW A c y y' (j - 1) (k + 1) := by
  rw [dib_WW_swap, dib_g3_step hA c y' y hk hj, dib_WW_swap A c y' y k j,
    dib_WW_swap A c y' y (k + 1) (j - 1), dib_inv_symm hA y' y]

theorem dib_lin_zero {A : Matrix ι ι ℝ} (hA : A.PosDef) (y : ι) :
    ∫ φ, φ y * PP2GaussIBP.gaussWeight A φ = 0 := by
  have key := PP2GaussIBP.gauss_ibp_cov hA (F := fun _ : ι → ℝ => (1 : ℝ))
    (differentiable_const 1) 1 0 y (fun φ => by simp) (fun z φ => by simp)
  simpa using key

theorem dib_quad {A : Matrix ι ι ℝ} (hA : A.PosDef) (y y' : ι) :
    ∫ φ, φ y * φ y' * PP2GaussIBP.gaussWeight A φ =
      A⁻¹ y y' * ∫ φ, PP2GaussIBP.gaussWeight A φ := by
  have hfd : ∀ φ : ι → ℝ, fderiv ℝ (fun ψ : ι → ℝ => ψ y') φ = ContinuousLinearMap.proj y' :=
    fun φ => (hasFDerivAt_apply y' φ).fderiv
  have hsum : ∀ φ : ι → ℝ, |φ y'| ≤ 1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro φ; rw [one_mul, one_mul]; exact dib_abs_le φ y'
  have hF' : ∀ (z : ι) (φ : ι → ℝ),
      |fderiv ℝ (fun ψ : ι → ℝ => ψ y') φ (Pi.single z 1)| ≤ 1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro z φ
    rw [hfd, ContinuousLinearMap.proj_apply, one_mul, one_mul]
    exact le_trans (dib_single_abs_le z y') (dib_one_le_exp φ)
  have key := PP2GaussIBP.gauss_ibp_cov hA (F := fun ψ : ι → ℝ => ψ y')
    (differentiable_apply y') 1 1 y hsum hF'
  simp only [hfd, ContinuousLinearMap.proj_apply] at key
  rw [key, Finset.sum_eq_single y']
  · simp
  · intro z _ hz
    simp [Pi.single_eq_of_ne (Ne.symm hz)]
  · simp

theorem dib_WW_0_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 0 = 1 := by
  simp only [dib_WW, dib_ex0, wickPow_zero', one_mul]
  exact div_self (dib_integral_gauss_pos hA).ne'

theorem dib_WW_1_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 0 = 0 := by
  simp only [dib_WW, dib_ex0, wickPow_one, wickPow_zero', mul_one]
  rw [dib_lin_zero hA y, zero_div]

theorem dib_WW_0_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 1 = 0 := by
  rw [dib_WW_swap]; exact dib_WW_1_0 hA c y' y

theorem dib_WW_1_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 1 = A⁻¹ y y' := by
  simp only [dib_WW, dib_ex0, wickPow_one]
  rw [dib_quad hA y y', mul_div_assoc, div_self (dib_integral_gauss_pos hA).ne', mul_one]

/-! ### The table E₀[:φ_y^j:_c :φ_{y'}^k:_c], j, k ≤ 4
(r = C(y,y'), d = δ_y = c − C(y,y), d' = δ_{y'} = c − C(y',y'), C = A⁻¹) -/

theorem dib_WW_0_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 2 = -(c - A⁻¹ y' y') := by
  have h := dib_g3_step' hA c y y' (j := 0) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_0 hA c y y']
  ring

theorem dib_WW_2_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 0 = -(c - A⁻¹ y y) := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_0 hA c y y']
  ring

theorem dib_WW_0_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 3 = 0 := by
  have h := dib_g3_step' hA c y y' (j := 0) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_1 hA c y y']
  ring

theorem dib_WW_1_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 2 = 0 := by
  have h := dib_g3_step' hA c y y' (j := 1) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_0 hA c y y', dib_WW_0_1 hA c y y']
  ring

theorem dib_WW_2_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 1 = 0 := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_1 hA c y y', dib_WW_1_0 hA c y y']
  ring

theorem dib_WW_3_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 0 = 0 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_0 hA c y y']
  ring

theorem dib_WW_0_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 0 4 = 3 * (c - A⁻¹ y' y') ^ 2 := by
  have h := dib_g3_step' hA c y y' (j := 0) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_2 hA c y y']
  ring

theorem dib_WW_1_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 3 = -3 * (A⁻¹ y y') * (c - A⁻¹ y' y') := by
  have h := dib_g3_step' hA c y y' (j := 1) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_1 hA c y y', dib_WW_0_2 hA c y y']
  ring

theorem dib_WW_2_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 2 = (c - A⁻¹ y y) * (c - A⁻¹ y' y') + 2 * (A⁻¹ y y') ^ 2 := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_2 hA c y y', dib_WW_1_1 hA c y y']
  ring

theorem dib_WW_3_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 1 = -3 * (A⁻¹ y y') * (c - A⁻¹ y y) := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_1 hA c y y', dib_WW_2_0 hA c y y']
  ring

theorem dib_WW_4_0 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 0 = 3 * (c - A⁻¹ y y) ^ 2 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 0) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_0 hA c y y']
  ring

theorem dib_WW_1_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 1 4 = 0 := by
  have h := dib_g3_step' hA c y y' (j := 1) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_2 hA c y y', dib_WW_0_3 hA c y y']
  ring

theorem dib_WW_2_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 3 = 0 := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_3 hA c y y', dib_WW_1_2 hA c y y']
  ring

theorem dib_WW_3_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 2 = 0 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_2 hA c y y', dib_WW_2_1 hA c y y']
  ring

theorem dib_WW_4_1 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 1 = 0 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 1) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_1 hA c y y', dib_WW_3_0 hA c y y']
  ring

theorem dib_WW_2_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 2 4 =
      -3 * (c - A⁻¹ y y) * (c - A⁻¹ y' y') ^ 2
        - 12 * (A⁻¹ y y') ^ 2 * (c - A⁻¹ y' y') := by
  have h := dib_g3_step hA c y y' (j := 0) (k := 4) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_0_4 hA c y y', dib_WW_1_3 hA c y y']
  ring

theorem dib_WW_3_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 3 =
      9 * (A⁻¹ y y') * (c - A⁻¹ y y) * (c - A⁻¹ y' y')
        + 6 * (A⁻¹ y y') ^ 3 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_3 hA c y y', dib_WW_2_2 hA c y y']
  ring

theorem dib_WW_4_2 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 2 =
      -3 * (c - A⁻¹ y y) ^ 2 * (c - A⁻¹ y' y')
        - 12 * (A⁻¹ y y') ^ 2 * (c - A⁻¹ y y) := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_2 hA c y y', dib_WW_3_1 hA c y y']
  ring

theorem dib_WW_3_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 3 4 = 0 := by
  have h := dib_g3_step hA c y y' (j := 1) (k := 4) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_1_4 hA c y y', dib_WW_2_3 hA c y y']
  ring

theorem dib_WW_4_3 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 3 = 0 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_3 hA c y y', dib_WW_3_2 hA c y y']
  ring

theorem dib_WW_4_4 {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) (y y' : ι) :
    dib_WW A c y y' 4 4 =
      9 * (c - A⁻¹ y y) ^ 2 * (c - A⁻¹ y' y') ^ 2
        + 72 * (A⁻¹ y y') ^ 2 * (c - A⁻¹ y y) * (c - A⁻¹ y' y')
        + 24 * (A⁻¹ y y') ^ 4 := by
  have h := dib_g3_step hA c y y' (j := 2) (k := 4) (by norm_num) (by norm_num)
  norm_num at h
  rw [h, dib_WW_2_4 hA c y y', dib_WW_3_3 hA c y y']
  ring


theorem dib_ex_zero (A : Matrix ι ι ℝ) (e c : ℝ) (F : (ι → ℝ) → ℝ) :
    dib_ex A e c 0 F = dib_ex0 A F := by
  simp only [dib_ex, dib_ex0, dib_W_zero]

end G3

/-! ### G3 for the free box measure (λ = 0 in `dexpect`; C = ε⁻² dirGreen) -/

section G3Box

variable {n k : ℕ}

theorem dib_WW_box (m₀ c : ℝ) (y y' : DSite n k) (a b : ℕ) :
    PP2Griffiths.dexpect n k m₀ 0 (fun φ => wickPow c a (φ y) * wickPow c b (φ y')) =
      dib_WW (scaledOp n k m₀) c y y' a b := by
  rw [dib_dexpect_eq, dib_ex_zero]; rfl

/-- **G3, (2,2) entry, box:** E₀[:φ_y²:_c :φ_{y'}²:_c] = δ_y δ_{y'} + 2 C(y,y')², c = freeVar,
δ_y = c − C(y,y). -/
theorem dib_wick22_box {m₀ : ℝ} (hm : m₀ ≠ 0) (y y' : DSite n k) :
    PP2Griffiths.dexpect n k m₀ 0
        (fun φ => wickPow (freeVar n m₀) 2 (φ y) * wickPow (freeVar n m₀) 2 (φ y')) =
      (freeVar n m₀ - dib_G n k m₀ y y) * (freeVar n m₀ - dib_G n k m₀ y' y')
        + 2 * dib_G n k m₀ y y' ^ 2 := by
  rw [dib_WW_box, dib_WW_2_2 (scaledOp_posDef hm), ← dib_G_eq hm]

/-- **G3, (4,4) entry, box:** E₀[:φ_y⁴:_c :φ_{y'}⁴:_c] = 9 δ_y² δ_{y'}² + 72 C² δ_y δ_{y'} + 24 C⁴,
C = C(y,y'), c = freeVar, δ_y = c − C(y,y). -/
theorem dib_wick44_box {m₀ : ℝ} (hm : m₀ ≠ 0) (y y' : DSite n k) :
    PP2Griffiths.dexpect n k m₀ 0
        (fun φ => wickPow (freeVar n m₀) 4 (φ y) * wickPow (freeVar n m₀) 4 (φ y')) =
      9 * (freeVar n m₀ - dib_G n k m₀ y y) ^ 2 * (freeVar n m₀ - dib_G n k m₀ y' y') ^ 2
        + 72 * dib_G n k m₀ y y' ^ 2 * (freeVar n m₀ - dib_G n k m₀ y y) *
            (freeVar n m₀ - dib_G n k m₀ y' y')
        + 24 * dib_G n k m₀ y y' ^ 4 := by
  rw [dib_WW_box, dib_WW_4_4 (scaledOp_posDef hm), ← dib_G_eq hm]

end G3Box

end PP2DoubleIBP

import LongTable.R_PP2DoubleIBPB

/-!
Part C of PP2DoubleIBP (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2DoubleIBP.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
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

end G3

end PP2DoubleIBP

end

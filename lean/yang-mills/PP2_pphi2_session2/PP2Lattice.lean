import LongTable.P_mwvi84dh_hnd872

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Session 2.
Node N1 of the plan (#mwvke7za-dghcwb) for the quartic model, and the quartic case of N3:
the lattice measure of `PP2Target` (#mwvi84dh-hnd872) is well defined.

FORMALIZED (P = X⁴; the integrability, positivity and norm theorems need λ ≥ 0 and m₀ ≠ 0,
the algebraic ones need no hypotheses; every level n; the Wick constant c arbitrary):
* `wickPow_four`: :y⁴:_c = y⁴ − 6c y² + 3c². `wickPoly_X4`: the same for `wickPoly (X^4)`.
* `wickPoly_X4_ge`: :y⁴:_c ≥ −6c² (it is (y² − 3c)² − 6c²).
* `freeAction_ge`: freeAction ≥ m₀² ε² Σ_x φ(x)².
* `integrable_weight`: the interacting weight is integrable on ℝ^(sites).
* `integral_weight_pos`: its integral is strictly positive (so `Zlat` divides by a positive number).
* `integrable_smeared_weight`: exp(i·smear)·weight is integrable.
* `norm_Zlat_le_one`: ‖Zlat n m₀ λ X⁴ f‖ ≤ 1 for every test function f (the elementary bound
  for a normalised characteristic function; a sanity check, not a clustering or limit statement).
The proof bounds the weight by exp(6λε²|Λ|c²) times a product of one-dimensional Gaussians
exp(−(m₀²ε²/2) φ(x)²), integrable by Mathlib's Gaussian integral and the product rule on finite
products of measure spaces.

NOT formalized: anything uniform in n (the bound used grows with the volume); general P;
that `wickConst` is the variance of φ(0) under the free measure (it is defined as a ratio of
integrals; its positivity and well-definedness are not proved); any limit.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory

noncomputable section

namespace PP2Target

/-- :y⁴:_c = y⁴ − 6c y² + 3c². -/
theorem wickPow_four (c y : ℝ) : wickPow c 4 y = y ^ 4 - 6 * c * y ^ 2 + 3 * c ^ 2 := by
  simp [wickPow, Finset.sum_range_succ, Nat.factorial]
  ring

theorem wickPoly_X4 (c y : ℝ) :
    wickPoly (Polynomial.X ^ 4) c y = y ^ 4 - 6 * c * y ^ 2 + 3 * c ^ 2 := by
  have hdeg : (Polynomial.X ^ 4 : Polynomial ℝ).natDegree = 4 := by simp
  rw [wickPoly, hdeg]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Polynomial.coeff_X_pow]
  simp [wickPow_four]

theorem wickPoly_X4_ge (c y : ℝ) : -(6 * c ^ 2) ≤ wickPoly (Polynomial.X ^ 4) c y := by
  rw [wickPoly_X4]
  nlinarith [sq_nonneg (y ^ 2 - 3 * c)]

theorem freeAction_ge (n : ℕ) (m₀ : ℝ) (φ : Field n) :
    m₀ ^ 2 * spacing n ^ 2 * ∑ x : Site n, φ x ^ 2 ≤ freeAction n m₀ φ := by
  rw [freeAction, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have h1 := sq_nonneg ((φ (x + (1, 0)) - φ x) / spacing n)
  have h2 := sq_nonneg ((φ (x + (0, 1)) - φ x) / spacing n)
  have hs := sq_nonneg (spacing n)
  nlinarith [mul_nonneg hs (add_nonneg h1 h2)]

/-- The Gaussian majorant: ∏_x exp(−(m₀²ε²/2) φ(x)²). -/
def gauss (n : ℕ) (m₀ : ℝ) (φ : Field n) : ℝ :=
  ∏ x : Site n, Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * φ x ^ 2)

theorem spacing_pos (n : ℕ) : 0 < spacing n := by unfold spacing; positivity

theorem integrable_gauss (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) : Integrable (gauss n m₀) := by
  have hb : 0 < m₀ ^ 2 * spacing n ^ 2 / 2 := by
    have := spacing_pos n
    positivity
  have := Integrable.fintype_prod (ι := Site n) (E := ℝ) (𝕜 := ℝ)
    (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ y => Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * y ^ 2))
    (fun _ => integrable_exp_neg_mul_sq hb)
  exact this

theorem gauss_eq (n : ℕ) (m₀ : ℝ) (φ : Field n) :
    gauss n m₀ φ = Real.exp (-(m₀ ^ 2 * spacing n ^ 2 * ∑ x : Site n, φ x ^ 2) / 2) := by
  rw [gauss, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weight_le (n : ℕ) (m₀ lam : ℝ) (hlam : 0 ≤ lam) (φ : Field n) :
    weight n m₀ lam (Polynomial.X ^ 4) φ ≤
      Real.exp (lam * spacing n ^ 2 * (Fintype.card (Site n) * (6 * wickConst n m₀ ^ 2)))
        * gauss n m₀ φ := by
  rw [gauss_eq, weight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hA := freeAction_ge n m₀ φ
  have hsum : -(Fintype.card (Site n) * (6 * wickConst n m₀ ^ 2)) ≤
      ∑ x : Site n, wickPoly (Polynomial.X ^ 4) (wickConst n m₀) (φ x) := by
    have := Finset.sum_le_sum (s := Finset.univ)
      (fun x (_ : x ∈ Finset.univ) => wickPoly_X4_ge (wickConst n m₀) (φ x))
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hc : 0 ≤ lam * spacing n ^ 2 := by have := spacing_pos n; positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hc]

theorem continuous_weight (n : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) :
    Continuous (weight n m₀ lam P) := by
  unfold weight freeAction wickPoly wickPow
  fun_prop

theorem weight_pos (n : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : Field n) :
    0 < weight n m₀ lam P φ := Real.exp_pos _

theorem integrable_weight (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    Integrable (weight n m₀ lam (Polynomial.X ^ 4)) := by
  refine Integrable.mono' (g := fun φ => Real.exp (lam * spacing n ^ 2 *
      (Fintype.card (Site n) * (6 * wickConst n m₀ ^ 2))) * gauss n m₀ φ)
    ((integrable_gauss n hm).const_mul _)
    (continuous_weight n m₀ lam _).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro φ
  rw [Real.norm_eq_abs, abs_of_pos (weight_pos _ _ _ _ _)]
  exact weight_le n m₀ lam hlam φ

theorem integral_weight_pos (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 < ∫ φ : Field n, weight n m₀ lam (Polynomial.X ^ 4) φ := by
  rw [integral_pos_iff_support_of_nonneg (fun φ => (weight_pos _ _ _ _ φ).le)
    (integrable_weight n hm hlam)]
  have : Function.support (weight n m₀ lam (Polynomial.X ^ 4)) = Set.univ := by
    ext φ; simp [(weight_pos n m₀ lam _ φ).ne']
  rw [this]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

theorem norm_smeared_weight (n : ℕ) (m₀ lam : ℝ) (f : TestFn) (φ : Field n) :
    ‖Complex.exp (Complex.I * (smear n f φ : ℂ)) * (weight n m₀ lam (Polynomial.X ^ 4) φ : ℂ)‖
      = weight n m₀ lam (Polynomial.X ^ 4) φ := by
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (weight_pos _ _ _ _ φ), one_mul]

theorem integrable_smeared_weight (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (f : TestFn) :
    Integrable (fun φ : Field n =>
      Complex.exp (Complex.I * (smear n f φ : ℂ)) * (weight n m₀ lam (Polynomial.X ^ 4) φ : ℂ)) := by
  have hs : Continuous (smear n f) := by unfold smear; fun_prop
  have hw := continuous_weight n m₀ lam (Polynomial.X ^ 4)
  have hc : Continuous (fun φ : Field n =>
      Complex.exp (Complex.I * (smear n f φ : ℂ)) * (weight n m₀ lam (Polynomial.X ^ 4) φ : ℂ)) :=
    ((continuous_const.mul (Complex.continuous_ofReal.comp hs)).cexp).mul
      (Complex.continuous_ofReal.comp hw)
  refine Integrable.mono' (integrable_weight n hm hlam) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro φ
  rw [norm_smeared_weight]

theorem norm_Zlat_le_one (n : ℕ) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (f : TestFn) : ‖Zlat n m₀ lam (Polynomial.X ^ 4) f‖ ≤ 1 := by
  have hpos := integral_weight_pos n hm hlam
  rw [Zlat, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    div_le_one hpos]
  calc ‖∫ φ : Field n, Complex.exp (Complex.I * (smear n f φ : ℂ)) *
          (weight n m₀ lam (Polynomial.X ^ 4) φ : ℂ)‖
      ≤ ∫ φ : Field n, ‖Complex.exp (Complex.I * (smear n f φ : ℂ)) *
          (weight n m₀ lam (Polynomial.X ^ 4) φ : ℂ)‖ := norm_integral_le_integral_norm _
    _ = ∫ φ : Field n, weight n m₀ lam (Polynomial.X ^ 4) φ := by
        congr 1; ext φ
        exact norm_smeared_weight n m₀ lam f φ

end PP2Target

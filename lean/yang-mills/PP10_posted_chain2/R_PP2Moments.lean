import LongTable.P_mwwjem2s_tf34yn
import LongTable.R_PP2Lebowitz2B

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Moments.lean (same content; only the imports are renamed).
Long Table, P(φ)₂ direction, node M9 (non-Gaussian limits), route review steps L1 and L4:
Newman's Gaussian moment inequalities for the smeared field from strong Gaussian domination, and
the Cauchy–Schwarz (Hölder) lower bound on the tree-level quartic quantity.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* The smeared field X = φ(f) = Σ_x c_x φ_x (c_x = ε² f(dpos x), `lb2_c`) as a positive linear
  form: `mo_dsmear_c`, `mo_isPosPoly_dsmear` (f(dpos x) ≥ 0), `mo_abs_dsmear_le`
  (|X| ≤ Σ|c_x| e^{Σ|φ_x|}), **`mo_adm_pow`** (c·X^p ∈ Adm 1, the exponential-linear class of
  `strong_gaussian_domination_box`), **`mo_cone_pow`** (c·X^p ∈ 𝒞 for c ≥ 0),
  `mo_dsmear_add_single` (X(φ + t e_j) = X(φ) + t c_j), **`mo_hasLineDeriv`**
  (∂_j X^{p+1} = (p+1) c_j X^p), `mo_twoPt_eq` (twoPt = dexpect of φ_iφ_j, rfl).
* (L1) **`mo_mom_step`**: for f(dpos x) ≥ 0, m₀ ≠ 0, λ ≥ 0 and every m,
    ⟨X^{m+2}⟩ ≤ (m+1) ⟨X^m⟩ ⟨X²⟩
  (G = X^{m+1} in `strong_gaussian_domination_box`, ⟨φ_i X^{m+1}⟩ ≤ Σ_j (m+1)c_j⟨X^m⟩⟨φ_iφ_j⟩,
  multiplied by c_i ≥ 0 and summed; Σ_i c_i φ_i X^{m+1} = X^{m+2}, `lb2_mom2_expand`).
  **`mo_newman4`**: ⟨X⁴⟩ ≤ 3⟨X²⟩²; **`mo_newman6`**: ⟨X⁶⟩ ≤ 5⟨X²⟩⟨X⁴⟩;
  **`mo_newman6'`**: ⟨X⁶⟩ ≤ 15⟨X²⟩³; `mo_mom_even_nonneg`; Gibbs-measure forms
  `mo_newman4_gibbs`, `mo_newman6_gibbs` (via `integral_gibbs`). Moments are `lb2_mom`
  (= `dexpect` of φ(f)ʲ, the qweight ratio of `strong_gaussian_domination_box` by rfl).
* (L4) `mo_cs_weighted` ((Σ a g)² ≤ (Σ a)(Σ a g²), a ≥ 0), **`mo_holder4`**
  ((Σ a h)⁴ ≤ (Σ a)³ Σ a h⁴), **`mo_cs_lower_abstract`** (a = e·u, 0 ≤ u ≤ M:
  (e Σ u h)⁴ ≤ (e Σ u)³ M · e Σ h⁴, and the quotient form, valid also when the denominator
  vanishes), `mo_h` (h(z) = Σ_y twoPt(z,y) ε² f(dpos y)), `mo_mom2_eq_h`
  (⟨X²⟩ = ε² Σ_z f(dpos z) h(z)) and **`mo_cs_lower`**: for f(dpos z) ∈ [0, M],
    ε² Σ_z h(z)⁴ ≥ ⟨X²⟩⁴ / ((ε² Σ_z f(dpos z))³ · M).

NOT formalized.
* Nothing of L1/L4 remains. M (`sup f`) is any bound of f on the box sites; taking M = sup f
  over the plane is a special case. Higher Newman moments ⟨X^{2p}⟩ ≤ (2p−1)!!⟨X²⟩^p follow by
  iterating `mo_mom_step` (not stated beyond p = 3).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset PP2Target

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Moments

open PP2Griffiths PP2SGD PP2Lebowitz2 PP2LocalTime

/-! ## Part 1: the smeared field as a positive linear form -/

section Model

variable {n k : ℕ}

lemma mo_dsmear_c (f : TestFn) (φ : DField n k) :
    dsmear n k f φ = ∑ x, lb2_c n k f x * φ x :=
  lb2_dsmear_sum f φ

lemma mo_c_nonneg {f : TestFn} (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) (x : DSite n k) :
    0 ≤ lb2_c n k f x :=
  mul_nonneg (sq_nonneg _) (hf x)

lemma mo_isPosPoly_dsmear {f : TestFn} (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) :
    IsPosPoly (fun φ : DField n k => dsmear n k f φ) :=
  (IsPosPoly.linForm (h := lb2_c n k f) (mo_c_nonneg hf)).congr'
    fun φ => (mo_dsmear_c f φ).symm

lemma mo_continuous_dsmear (f : TestFn) : Continuous (fun φ : DField n k => dsmear n k f φ) := by
  have e : (fun φ : DField n k => dsmear n k f φ) = fun φ => ∑ x, lb2_c n k f x * φ x :=
    funext fun φ => mo_dsmear_c f φ
  rw [e]
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_apply x)

lemma mo_abs_dsmear_le (f : TestFn) (φ : DField n k) :
    |dsmear n k f φ| ≤ (∑ x, |lb2_c n k f x|) * Real.exp (∑ x, |φ x|) := by
  rw [mo_dsmear_c, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_le_exp_sum φ x) (abs_nonneg _)

/-- c·X^p is of exponential-linear growth (envelope 1). -/
lemma mo_adm_pow (f : TestFn) (c : ℝ) (p : ℕ) :
    Adm (fun _ : DField n k => (1 : ℝ)) (fun φ => c * dsmear n k f φ ^ p) := by
  refine ⟨continuous_const.mul ((mo_continuous_dsmear f).pow p),
    |c| * (∑ x, |lb2_c n k f x|) ^ p, p, fun φ => ?_⟩
  rw [abs_mul, abs_pow]
  calc |c| * |dsmear n k f φ| ^ p
      ≤ |c| * ((∑ x, |lb2_c n k f x|) * Real.exp (∑ x, |φ x|)) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (mo_abs_dsmear_le f φ) p)
          (abs_nonneg c)
    _ = |c| * (∑ x, |lb2_c n k f x|) ^ p * Real.exp ((p : ℝ) * ∑ x, |φ x|) * 1 := by
        rw [mul_pow, Real.exp_nat_mul]; ring

/-- c·X^p lies in the cone 𝒞 for c ≥ 0 and f ≥ 0 on the box. -/
lemma mo_cone_pow {f : TestFn} (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) {c : ℝ} (hc : 0 ≤ c)
    (p : ℕ) : InCone (fun φ : DField n k => c * dsmear n k f φ ^ p) :=
  InCone.of_isPosPoly ((IsPosPoly.const hc).mul ((mo_isPosPoly_dsmear hf).pow p))

lemma mo_dsmear_add_single (f : TestFn) (φ : DField n k) (j : DSite n k) (t : ℝ) :
    dsmear n k f (φ + t • (Pi.single j (1 : ℝ) : DField n k)) =
      dsmear n k f φ + t * lb2_c n k f j := by
  rw [mo_dsmear_c, mo_dsmear_c]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j (fun y _ hy => by simp [Pi.single_eq_of_ne hy])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simp only [Pi.single_eq_same]
  ring

/-- ∂_j X^{p+1} = (p+1) c_j X^p. -/
lemma mo_hasLineDeriv (f : TestFn) (p : ℕ) (j : DSite n k) (φ : DField n k) :
    HasLineDerivAt ℝ (fun ψ : DField n k => dsmear n k f ψ ^ (p + 1))
      (((p : ℝ) + 1) * lb2_c n k f j * dsmear n k f φ ^ p) φ (Pi.single j 1) := by
  unfold HasLineDerivAt
  simp only [mo_dsmear_add_single]
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const (lb2_c n k f j)).const_add
    (dsmear n k f φ)).pow (p + 1)
  refine h.congr_deriv ?_
  simp only [id, zero_mul, add_zero, one_mul, Nat.add_sub_cancel]
  push_cast
  ring

lemma mo_twoPt_eq (m₀ lam : ℝ) (i j : DSite n k) :
    twoPt n k m₀ lam i j = dexpect n k m₀ lam (fun φ => φ i * φ j) := rfl

/-! ## Part 2 (L1): Newman's inequalities from strong Gaussian domination -/

/-- **The moment step.** For f ≥ 0 on the box, m₀ ≠ 0, λ ≥ 0, X = φ(f) and every m:
⟨X^{m+2}⟩ ≤ (m+1) ⟨X^m⟩ ⟨X²⟩. -/
theorem mo_mom_step {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn}
    (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) (m : ℕ) :
    lb2_mom n k m₀ lam f (m + 2) ≤
      ((m : ℝ) + 1) * lb2_mom n k m₀ lam f m * lb2_mom n k m₀ lam f 2 := by
  have hc := mo_c_nonneg hf
  have hsgd : ∀ i, dexpect n k m₀ lam (fun φ => φ i * dsmear n k f φ ^ (m + 1)) ≤
      ∑ j, (((m : ℝ) + 1) * lb2_c n k f j * lb2_mom n k m₀ lam f m) * twoPt n k m₀ lam i j := by
    intro i
    have h := strong_gaussian_domination_box (n := n) (k := k) hm hlam
      (G := fun ψ => dsmear n k f ψ ^ (m + 1))
      (G' := fun j ψ => ((m : ℝ) + 1) * lb2_c n k f j * dsmear n k f ψ ^ m)
      ((mo_adm_pow f 1 (m + 1)).congr fun φ => one_mul _)
      (fun j => mo_adm_pow f _ m) (fun j φ => mo_hasLineDeriv f m j φ)
      (fun j => mo_cone_pow hf (mul_nonneg (by positivity) (hc j)) m) i
    refine h.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
    congr 1
    exact lb2_dexpect_const_mul m₀ lam (((m : ℝ) + 1) * lb2_c n k f j)
      (fun φ => dsmear n k f φ ^ m)
  have hint : ∀ i ∈ (Finset.univ : Finset (DSite n k)), Integrable fun φ : DField n k =>
      lb2_c n k f i * (φ i * dsmear n k f φ ^ (m + 1)) *
        dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
    intro i _
    refine ((lb2_integrable_pow hm hlam f (m + 1) (Pi.single i 1)).const_mul
      (lb2_c n k f i)).congr (Filter.Eventually.of_forall fun φ => ?_)
    simp only [prod_single_pow]
    ring
  have hL : lb2_mom n k m₀ lam f (m + 2) = ∑ i, lb2_c n k f i *
      dexpect n k m₀ lam (fun φ => φ i * dsmear n k f φ ^ (m + 1)) := by
    have e : (fun φ : DField n k => dsmear n k f φ ^ (m + 2)) =
        fun φ => ∑ i, lb2_c n k f i * (φ i * dsmear n k f φ ^ (m + 1)) := by
      funext φ
      have hX := mo_dsmear_c f φ
      calc dsmear n k f φ ^ (m + 2) = dsmear n k f φ * dsmear n k f φ ^ (m + 1) := by ring
        _ = (∑ i, lb2_c n k f i * φ i) * dsmear n k f φ ^ (m + 1) := by rw [← hX]
        _ = _ := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
    rw [lb2_mom, e, lb2_dexpect_sum _ _ _ _ hint]
    exact Finset.sum_congr rfl fun i _ => lb2_dexpect_const_mul _ _ _ _
  have hR : ∑ i, lb2_c n k f i * ∑ j, (((m : ℝ) + 1) * lb2_c n k f j *
      lb2_mom n k m₀ lam f m) * twoPt n k m₀ lam i j =
      ((m : ℝ) + 1) * lb2_mom n k m₀ lam f m * lb2_mom n k m₀ lam f 2 := by
    rw [lb2_mom2_expand hm hlam f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mo_twoPt_eq]
    ring
  rw [hL, ← hR]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hsgd i) (hc i)

lemma mo_mom_even_nonneg (m₀ lam : ℝ) (f : TestFn) (p : ℕ) :
    0 ≤ lb2_mom n k m₀ lam f (2 * p) := by
  unfold lb2_mom dexpect
  refine div_nonneg (integral_nonneg fun φ => mul_nonneg ?_ (dweight_pos' _ _ _ _).le)
    (Z_nonneg m₀ lam)
  simp only; rw [pow_mul]; positivity

/-- **Newman's inequality, fourth moment**: ⟨φ(f)⁴⟩ ≤ 3⟨φ(f)²⟩² for f ≥ 0 on the box. -/
theorem mo_newman4 {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn}
    (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) :
    lb2_mom n k m₀ lam f 4 ≤ 3 * lb2_mom n k m₀ lam f 2 ^ 2 := by
  have h := mo_mom_step hm hlam hf 2
  calc lb2_mom n k m₀ lam f 4 ≤ (((2 : ℕ) : ℝ) + 1) * lb2_mom n k m₀ lam f 2 *
      lb2_mom n k m₀ lam f 2 := h
    _ = 3 * lb2_mom n k m₀ lam f 2 ^ 2 := by push_cast; ring

/-- **Newman's inequality, sixth moment**: ⟨φ(f)⁶⟩ ≤ 5⟨φ(f)²⟩⟨φ(f)⁴⟩. -/
theorem mo_newman6 {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn}
    (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) :
    lb2_mom n k m₀ lam f 6 ≤ 5 * lb2_mom n k m₀ lam f 2 * lb2_mom n k m₀ lam f 4 := by
  have h := mo_mom_step hm hlam hf 4
  calc lb2_mom n k m₀ lam f 6 ≤ (((4 : ℕ) : ℝ) + 1) * lb2_mom n k m₀ lam f 4 *
      lb2_mom n k m₀ lam f 2 := h
    _ = 5 * lb2_mom n k m₀ lam f 2 * lb2_mom n k m₀ lam f 4 := by push_cast; ring

/-- ⟨φ(f)⁶⟩ ≤ 15⟨φ(f)²⟩³. -/
theorem mo_newman6' {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn}
    (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) :
    lb2_mom n k m₀ lam f 6 ≤ 15 * lb2_mom n k m₀ lam f 2 ^ 3 := by
  have h6 := mo_newman6 hm hlam hf
  have h4 := mo_newman4 hm hlam hf
  have h2 : 0 ≤ lb2_mom n k m₀ lam f 2 := mo_mom_even_nonneg m₀ lam f 1
  nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) h2)]

/-- Newman (fourth moment) for the Gibbs measure. -/
theorem mo_newman4_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn}
    (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) :
    ∫ φ, dsmear n k f φ ^ 4 ∂(gibbs n k m₀ lam) ≤
      3 * (∫ φ, dsmear n k f φ ^ 2 ∂(gibbs n k m₀ lam)) ^ 2 := by
  rw [integral_gibbs, integral_gibbs]
  exact mo_newman4 hm hlam hf

/-- Newman (sixth moment) for the Gibbs measure. -/
theorem mo_newman6_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn}
    (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) :
    ∫ φ, dsmear n k f φ ^ 6 ∂(gibbs n k m₀ lam) ≤
      5 * (∫ φ, dsmear n k f φ ^ 2 ∂(gibbs n k m₀ lam)) *
        ∫ φ, dsmear n k f φ ^ 4 ∂(gibbs n k m₀ lam) ∧
    ∫ φ, dsmear n k f φ ^ 6 ∂(gibbs n k m₀ lam) ≤
      15 * (∫ φ, dsmear n k f φ ^ 2 ∂(gibbs n k m₀ lam)) ^ 3 := by
  rw [integral_gibbs, integral_gibbs, integral_gibbs]
  exact ⟨mo_newman6 hm hlam hf, mo_newman6' hm hlam hf⟩

end Model

/-! ## Part 3 (L4): the Cauchy–Schwarz lower bound -/

section Holder

variable {ι : Type*} [Fintype ι]

/-- Weighted Cauchy–Schwarz: (Σ a g)² ≤ (Σ a)(Σ a g²) for a ≥ 0. -/
lemma mo_cs_weighted (a g : ι → ℝ) (ha : ∀ z, 0 ≤ a z) :
    (∑ z, a z * g z) ^ 2 ≤ (∑ z, a z) * ∑ z, a z * g z ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun z => √(a z))
    (fun z => √(a z) * g z)
  have e1 : ∀ z, √(a z) * (√(a z) * g z) = a z * g z := fun z => by
    rw [← mul_assoc, Real.mul_self_sqrt (ha z)]
  have e2 : ∀ z, √(a z) ^ 2 = a z := fun z => Real.sq_sqrt (ha z)
  have e3 : ∀ z, (√(a z) * g z) ^ 2 = a z * g z ^ 2 := fun z => by rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

/-- Hölder with exponents (4/3, 4): (Σ a h)⁴ ≤ (Σ a)³ Σ a h⁴ for a ≥ 0. -/
theorem mo_holder4 (a h : ι → ℝ) (ha : ∀ z, 0 ≤ a z) :
    (∑ z, a z * h z) ^ 4 ≤ (∑ z, a z) ^ 3 * ∑ z, a z * h z ^ 4 := by
  have h1 := mo_cs_weighted a h ha
  have h2 := mo_cs_weighted a (fun z => h z ^ 2) ha
  have e : ∀ z, (h z ^ 2) ^ 2 = h z ^ 4 := fun z => by ring
  simp only [e] at h2
  have hA : 0 ≤ ∑ z, a z := Finset.sum_nonneg fun z _ => ha z
  calc (∑ z, a z * h z) ^ 4 = ((∑ z, a z * h z) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ z, a z) * ∑ z, a z * h z ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (∑ z, a z) ^ 2 * (∑ z, a z * h z ^ 2) ^ 2 := by ring
    _ ≤ (∑ z, a z) ^ 2 * ((∑ z, a z) * ∑ z, a z * h z ^ 4) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (∑ z, a z) ^ 3 * ∑ z, a z * h z ^ 4 := by ring

/-- **The Hölder lower bound, abstract.** For e ≥ 0, 0 ≤ u ≤ M:
(e Σ u h)⁴ ≤ (e Σ u)³ · M · (e Σ h⁴), hence (e Σ u h)⁴ / ((e Σ u)³ M) ≤ e Σ h⁴ (the quotient
form holds also when the denominator vanishes). -/
theorem mo_cs_lower_abstract {e M : ℝ} (he : 0 ≤ e) (u h : ι → ℝ) (hu : ∀ z, 0 ≤ u z)
    (hM : ∀ z, u z ≤ M) :
    (e * ∑ z, u z * h z) ^ 4 ≤ (e * ∑ z, u z) ^ 3 * M * (e * ∑ z, h z ^ 4) ∧
    (e * ∑ z, u z * h z) ^ 4 / ((e * ∑ z, u z) ^ 3 * M) ≤ e * ∑ z, h z ^ 4 := by
  have ha : ∀ z, 0 ≤ e * u z := fun z => mul_nonneg he (hu z)
  have hH := mo_holder4 (fun z => e * u z) h ha
  have s1 : ∑ z, e * u z * h z = e * ∑ z, u z * h z := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring
  have s2 : ∑ z, e * u z = e * ∑ z, u z := by rw [Finset.mul_sum]
  rw [s1, s2] at hH
  have hA : 0 ≤ (e * ∑ z, u z) ^ 3 := pow_nonneg (mul_nonneg he (Finset.sum_nonneg
    fun z _ => hu z)) 3
  have hB : ∑ z, e * u z * h z ^ 4 ≤ M * (e * ∑ z, h z ^ 4) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have h4 : 0 ≤ h z ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left (hM z) he
    nlinarith [mul_le_mul_of_nonneg_right this h4]
  have hP : (e * ∑ z, u z * h z) ^ 4 ≤ (e * ∑ z, u z) ^ 3 * M * (e * ∑ z, h z ^ 4) := by
    calc _ ≤ _ := hH
      _ ≤ (e * ∑ z, u z) ^ 3 * (M * (e * ∑ z, h z ^ 4)) := mul_le_mul_of_nonneg_left hB hA
      _ = _ := by ring
  refine ⟨hP, ?_⟩
  have hT : 0 ≤ e * ∑ z, h z ^ 4 :=
    mul_nonneg he (Finset.sum_nonneg fun z _ => by positivity)
  rcases lt_or_ge 0 ((e * ∑ z, u z) ^ 3 * M) with hD | hD
  · rw [div_le_iff₀ hD]; linarith
  · have hS : 0 ≤ (e * ∑ z, u z * h z) ^ 4 := by positivity
    have hi : ((e * ∑ z, u z) ^ 3 * M)⁻¹ ≤ 0 := inv_nonpos.mpr hD
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg hS (neg_nonneg.mpr hi)]

end Holder

section ModelL4

variable {n k : ℕ}

/-- h(z) = Σ_y ⟨φ_z φ_y⟩ ε² f(dpos y) (the lattice G·f). -/
def mo_h (n k : ℕ) (m₀ lam : ℝ) (f : TestFn) (z : DSite n k) : ℝ :=
  ∑ y, twoPt n k m₀ lam z y * lb2_c n k f y

/-- ⟨φ(f)²⟩ = ε² Σ_z f(dpos z) h(z). -/
theorem mo_mom2_eq_h {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f : TestFn) :
    lb2_mom n k m₀ lam f 2 = spacing n ^ 2 * ∑ z, f (dpos n k z) * mo_h n k m₀ lam f z := by
  rw [lb2_mom2_expand hm hlam f, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold mo_h
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mo_twoPt_eq]
  unfold lb2_c
  ring

/-- **(L4) The Cauchy–Schwarz lower bound.** For 0 ≤ f(dpos z) ≤ M on the box, with
h(z) = Σ_y ⟨φ_zφ_y⟩ ε² f(dpos y):
  ε² Σ_z h(z)⁴ ≥ ⟨φ(f)²⟩⁴ / ((ε² Σ_z f(dpos z))³ · M),
together with the product form ⟨φ(f)²⟩⁴ ≤ (ε² Σ f)³ · M · ε² Σ h⁴. -/
theorem mo_cs_lower {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn} {M : ℝ}
    (hf : ∀ z : DSite n k, 0 ≤ f (dpos n k z)) (hM : ∀ z : DSite n k, f (dpos n k z) ≤ M) :
    lb2_mom n k m₀ lam f 2 ^ 4 ≤ (spacing n ^ 2 * ∑ z, f (dpos n k z)) ^ 3 * M *
        (spacing n ^ 2 * ∑ z, mo_h n k m₀ lam f z ^ 4) ∧
    lb2_mom n k m₀ lam f 2 ^ 4 / ((spacing n ^ 2 * ∑ z, f (dpos n k z)) ^ 3 * M) ≤
      spacing n ^ 2 * ∑ z, mo_h n k m₀ lam f z ^ 4 := by
  rw [mo_mom2_eq_h hm hlam f]
  exact mo_cs_lower_abstract (sq_nonneg _) (fun z => f (dpos n k z)) (mo_h n k m₀ lam f) hf hM

end ModelL4

end PP2Moments


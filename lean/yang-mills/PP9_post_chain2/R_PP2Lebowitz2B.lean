import LongTable.R_PP2Lebowitz2A

/-!
Part B of PP2Lebowitz2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Lebowitz2.lean)

FORMALIZED in this part.
* Integrability: `lb2_integrable_pow` (∏ φ^e · φ(f)^m · dweight is integrable, every e, m),
  `lb2_integrable_dsmear_pow`.
* **Multilinear expansion.** With c_x = ε² f(x), `lb2_mom2_expand`, `lb2_mom4_expand`, and
  **`lb2_u4_expand`**: the smeared Ursell function u₄(f) := ⟨X⁴⟩ − 3⟨X²⟩² (X = φ(f), `lb2_u4`)
  equals Σ_{a,b,c,d} c_a c_b c_c c_d · u₄(a,b,c,d), where u₄(a,b,c,d) (`lb2_U`) is exactly the
  site Ursell function of `lebowitz_dexpect`. **`lb2_u4_nonpos`**: u₄(f) ≤ 0 for f ≥ 0 on the
  lattice (λ ≥ 0, m₀ ≠ 0). Scaling: `lb2_mom_smul` (⟨φ(tf)ʲ⟩ = tʲ⟨φ(f)ʲ⟩), `lb2_u4_smul`
  (u₄(tf) = t⁴ u₄(f)).
* **`UniformQuarticNegativity m₀ λ`**: ∃ f, δ > 0, K, N₀, K₀ such that for all n ≥ N₀, k ≥ K₀:
  u₄(f) ≤ −δ, ⟨φ(f)⁶⟩ ≤ K, ⟨φ(f)²⟩ ≤ K. **`lb2_quarticDeficit_of_uniform`** (λ ≥ 0, m₀ ≠ 0):
  UniformQuarticNegativity m₀ λ → QuarticDeficit m₀ λ (test function t·f, t² = min(1/(4(K+1)),
  δ/(4000(1+K)³)), deficit δt⁴/4, uniform since t depends only on δ, K).
  **`lb2_nonGaussian_of_uniform`**: hence every limit point is non-Gaussian.

NOT formalized (what remains for M9).
* `UniformQuarticNegativity` itself: the strict cutoff-uniform bound u₄(f) ≤ −δ < 0 (a
  tree-level lower bound −u₄(f) ≥ c λ ∫ (G f)⁴ minus higher-order corrections, e.g. via the
  Brydges–Fröhlich–Sokal / Aizenman skeleton lower bounds or the cluster expansion at weak
  coupling), and the uniform bounds ⟨φ(f)²⟩ ≤ K (available from `UniformSusceptibility`, cf.
  `sqMoment_le` in PP2Limit2) and ⟨φ(f)⁶⟩ ≤ K (not derived here; e.g. from Gaussian domination
  or a uniform Nelson-type hypercontractive bound at weak coupling).
* The sharp constant 1/720 in the cos remainder (3 is used; irrelevant for the reduction).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset PP2Target

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Lebowitz2

open PP2Griffiths PP2Lebowitz PP2Newman

section Model

variable {n k : ℕ}

/-! ## Part 4: integrability and the multilinear expansion -/

lemma lb2_dsmear_sum (f : TestFn) (φ : DField n k) :
    dsmear n k f φ = ∑ x, spacing n ^ 2 * f (dpos n k x) * φ x := by
  unfold dsmear; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring

/-- (∏ φ^e) · φ(f)^m · dweight is integrable, for all e and m. -/
theorem lb2_integrable_pow {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f : TestFn)
    (m : ℕ) : ∀ e : DSite n k → ℕ, Integrable fun φ : DField n k =>
      (∏ x, φ x ^ e x) * dsmear n k f φ ^ m * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  induction m with
  | zero =>
    intro e
    simpa only [pow_zero, mul_one] using integrable_mono_dweight hm hlam e
  | succ m ih =>
    intro e
    have key : ∀ φ : DField n k, (∏ x, φ x ^ e x) * dsmear n k f φ ^ (m + 1)
        * dweight n k m₀ lam (Polynomial.X ^ 4) φ
        = ∑ x, spacing n ^ 2 * f (dpos n k x) * ((∏ z, φ z ^ ((e + Pi.single x 1 : DSite n k → ℕ) z))
          * dsmear n k f φ ^ m * dweight n k m₀ lam (Polynomial.X ^ 4) φ) := by
      intro φ
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_single_pow]
      rw [pow_succ]
      generalize dsmear n k f φ ^ m = S
      rw [lb2_dsmear_sum]
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp_rw [key]
    exact integrable_finsetSum _ fun x _ => (ih _).const_mul _

theorem lb2_integrable_dsmear_pow {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (f : TestFn) (m : ℕ) : Integrable fun φ : DField n k =>
      dsmear n k f φ ^ m * dweight n k m₀ lam (Polynomial.X ^ 4) φ :=
  (lb2_integrable_pow hm hlam f m 0).congr (Filter.Eventually.of_forall fun φ => by simp)

lemma lb2_integrable_sum {κ : Type*} (s : Finset κ) (g : κ → DField n k → ℝ) (w : DField n k → ℝ)
    (hg : ∀ i ∈ s, Integrable fun φ => g i φ * w φ) :
    Integrable fun φ => (∑ i ∈ s, g i φ) * w φ := by
  simp_rw [Finset.sum_mul]; exact integrable_finsetSum s hg

lemma lb2_dexpect_sum (m₀ lam : ℝ) {κ : Type*} (s : Finset κ) (g : κ → DField n k → ℝ)
    (hg : ∀ i ∈ s, Integrable fun φ => g i φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ) :
    dexpect n k m₀ lam (fun φ => ∑ i ∈ s, g i φ) = ∑ i ∈ s, dexpect n k m₀ lam (g i) := by
  unfold dexpect; simp_rw [Finset.sum_mul]; rw [integral_finsetSum s hg, Finset.sum_div]

lemma lb2_dexpect_const_mul (m₀ lam c : ℝ) (g : DField n k → ℝ) :
    dexpect n k m₀ lam (fun φ => c * g φ) = c * dexpect n k m₀ lam g := by
  unfold dexpect; simp_rw [mul_assoc]; rw [integral_const_mul, mul_div_assoc]

lemma lb2_int4 {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (C : ℝ) (a b c d : DSite n k) :
    Integrable fun φ : DField n k =>
      C * (φ a * φ b * φ c * φ d) * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  refine ((integrable_mono_dweight hm hlam ((Pi.single a 1 : DSite n k → ℕ) + Pi.single b 1
    + Pi.single c 1 + Pi.single d 1)).const_mul C).congr (Filter.Eventually.of_forall fun φ => ?_)
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_single_pow]
  ring

lemma lb2_int2 {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (C : ℝ) (a b : DSite n k) :
    Integrable fun φ : DField n k =>
      C * (φ a * φ b) * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  refine ((integrable_pair_mul hm hlam a b).const_mul C).congr
    (Filter.Eventually.of_forall fun φ => ?_)
  simp only; ring

/-- The lattice weights c_x = ε² f(x) of the smeared field. -/
def lb2_c (n k : ℕ) (f : TestFn) (x : DSite n k) : ℝ := spacing n ^ 2 * f (dpos n k x)

lemma lb2_sum_sq {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    (∑ a, g a) ^ 2 = ∑ a, ∑ b, g a * g b := by
  rw [sq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

lemma lb2_sq_sum2 {ι : Type*} [Fintype ι] (F : ι → ι → ℝ) :
    (∑ a, ∑ b, F a b) ^ 2 = ∑ a, ∑ b, ∑ c, ∑ d, F a b * F c d := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]

lemma lb2_sum_pow4 {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    (∑ a, g a) ^ 4 = ∑ a, ∑ b, ∑ c, ∑ d, g a * g b * g c * g d := by
  rw [show (∑ a, g a) ^ 4 = ((∑ a, g a) ^ 2) ^ 2 by ring, lb2_sum_sq,
    lb2_sq_sum2 (fun a b => g a * g b)]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- ⟨φ(f)²⟩ = Σ_{a,b} c_a c_b ⟨φ_a φ_b⟩. -/
theorem lb2_mom2_expand {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f : TestFn) :
    lb2_mom n k m₀ lam f 2 = ∑ a, ∑ b, lb2_c n k f a * lb2_c n k f b
      * dexpect n k m₀ lam (fun φ => φ a * φ b) := by
  have e : (fun φ : DField n k => dsmear n k f φ ^ 2) = fun φ => ∑ a, ∑ b,
      lb2_c n k f a * lb2_c n k f b * (φ a * φ b) := by
    funext φ
    rw [lb2_dsmear_sum, lb2_sum_sq]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      unfold lb2_c; ring
  rw [lb2_mom, e, lb2_dexpect_sum _ _ _ _ (fun a _ => lb2_integrable_sum _ _ _ fun b _ =>
    lb2_int2 hm hlam _ a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lb2_dexpect_sum _ _ _ _ (fun b _ => lb2_int2 hm hlam _ a b)]
  exact Finset.sum_congr rfl fun b _ => lb2_dexpect_const_mul _ _ _ _

/-- ⟨φ(f)⁴⟩ = Σ_{a,b,c,d} c_a c_b c_c c_d ⟨φ_a φ_b φ_c φ_d⟩. -/
theorem lb2_mom4_expand {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f : TestFn) :
    lb2_mom n k m₀ lam f 4 = ∑ a, ∑ b, ∑ c, ∑ d,
      lb2_c n k f a * lb2_c n k f b * lb2_c n k f c * lb2_c n k f d
        * dexpect n k m₀ lam (fun φ => φ a * φ b * φ c * φ d) := by
  have e : (fun φ : DField n k => dsmear n k f φ ^ 4) = fun φ => ∑ a, ∑ b, ∑ c, ∑ d,
      lb2_c n k f a * lb2_c n k f b * lb2_c n k f c * lb2_c n k f d
        * (φ a * φ b * φ c * φ d) := by
    funext φ
    rw [lb2_dsmear_sum, lb2_sum_pow4]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by unfold lb2_c; ring
  rw [lb2_mom, e, lb2_dexpect_sum _ _ _ _ (fun a _ => lb2_integrable_sum _ _ _ fun b _ =>
    lb2_integrable_sum _ _ _ fun c _ => lb2_integrable_sum _ _ _ fun d _ =>
      lb2_int4 hm hlam _ a b c d)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lb2_dexpect_sum _ _ _ _ (fun b _ => lb2_integrable_sum _ _ _ fun c _ =>
    lb2_integrable_sum _ _ _ fun d _ => lb2_int4 hm hlam _ a b c d)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [lb2_dexpect_sum _ _ _ _ (fun c _ => lb2_integrable_sum _ _ _ fun d _ =>
    lb2_int4 hm hlam _ a b c d)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lb2_dexpect_sum _ _ _ _ (fun d _ => lb2_int4 hm hlam _ a b c d)]
  exact Finset.sum_congr rfl fun d _ => lb2_dexpect_const_mul _ _ _ _

/-- The site Ursell function of `lebowitz_dexpect`:
u₄(a,b,c,d) = ⟨φ_aφ_bφ_cφ_d⟩ − ⟨φ_aφ_b⟩⟨φ_cφ_d⟩ − ⟨φ_aφ_c⟩⟨φ_bφ_d⟩ − ⟨φ_aφ_d⟩⟨φ_bφ_c⟩. -/
def lb2_U (n k : ℕ) (m₀ lam : ℝ) (a b c d : DSite n k) : ℝ :=
  dexpect n k m₀ lam (fun φ => φ a * φ b * φ c * φ d)
    - dexpect n k m₀ lam (fun φ => φ a * φ b) * dexpect n k m₀ lam (fun φ => φ c * φ d)
    - dexpect n k m₀ lam (fun φ => φ a * φ c) * dexpect n k m₀ lam (fun φ => φ b * φ d)
    - dexpect n k m₀ lam (fun φ => φ a * φ d) * dexpect n k m₀ lam (fun φ => φ b * φ c)

/-- The smeared Ursell function u₄(f) = ⟨φ(f)⁴⟩ − 3⟨φ(f)²⟩² (the fourth cumulant of φ(f), since
the odd moments vanish, `lb2_mom_odd`). -/
def lb2_u4 (n k : ℕ) (m₀ lam : ℝ) (f : TestFn) : ℝ :=
  lb2_mom n k m₀ lam f 4 - 3 * lb2_mom n k m₀ lam f 2 ^ 2

/-- **The multilinear expansion of the smeared Ursell function**:
u₄(f) = Σ_{a,b,c,d} c_a c_b c_c c_d u₄(a,b,c,d), c_x = ε² f(x). -/
theorem lb2_u4_expand {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f : TestFn) :
    lb2_u4 n k m₀ lam f = ∑ a, ∑ b, ∑ c, ∑ d,
      lb2_c n k f a * lb2_c n k f b * lb2_c n k f c * lb2_c n k f d * lb2_U n k m₀ lam a b c d := by
  set c := lb2_c n k f
  set E := fun a b : DSite n k => dexpect n k m₀ lam (fun φ => φ a * φ b) with hE
  set F := fun a b : DSite n k => c a * c b * E a b with hF
  have hM := lb2_sq_sum2 F
  have P1 : ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d * (E a b * E c' d)
      = (∑ a, ∑ b, F a b) ^ 2 := by
    rw [hM]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by rw [hF]; ring
  have P2 : ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d * (E a c' * E b d)
      = (∑ a, ∑ b, F a b) ^ 2 := by
    rw [hM]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c' _ =>
      Finset.sum_congr rfl fun d _ => by rw [hF]; ring
  have P3 : ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d * (E a d * E b c')
      = (∑ a, ∑ b, F a b) ^ 2 := by
    rw [hM]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c' _ =>
      Finset.sum_congr rfl fun d _ => by rw [hF]; ring
  have hsplit : ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d * lb2_U n k m₀ lam a b c' d
      = ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d
          * dexpect n k m₀ lam (fun φ => φ a * φ b * φ c' * φ d)
        - ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d * (E a b * E c' d)
        - ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d * (E a c' * E b d)
        - ∑ a, ∑ b, ∑ c', ∑ d, c a * c b * c c' * c d * (E a d * E b c') := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by
        rw [lb2_U, hE]; ring
  have h2 : lb2_mom n k m₀ lam f 2 = ∑ a, ∑ b, F a b := lb2_mom2_expand hm hlam f
  rw [hsplit, P1, P2, P3, lb2_u4, lb2_mom4_expand hm hlam f, h2]
  ring

/-- **u₄(f) ≤ 0 for f ≥ 0** (the smeared Lebowitz inequality; λ ≥ 0, m₀ ≠ 0). -/
theorem lb2_u4_nonpos {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {f : TestFn}
    (hf : ∀ x : DSite n k, 0 ≤ f (dpos n k x)) : lb2_u4 n k m₀ lam f ≤ 0 := by
  rw [lb2_u4_expand hm hlam f]
  have hc : ∀ x : DSite n k, 0 ≤ lb2_c n k f x := fun x => mul_nonneg (by positivity) (hf x)
  refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => Finset.sum_nonpos fun c _ =>
    Finset.sum_nonpos fun d _ => mul_nonpos_iff.mpr (Or.inl ⟨?_, ?_⟩)
  · have := hc a; have := hc b; have := hc c; have := hc d; positivity
  · exact lebowitz_dexpect hm hlam a b c d

/-! ## Part 5: scaling -/

lemma lb2_dsmear_smul (t : ℝ) (f : TestFn) (φ : DField n k) :
    dsmear n k (t • f) φ = t * dsmear n k f φ := by
  unfold dsmear
  simp only [smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem lb2_mom_smul (m₀ lam t : ℝ) (f : TestFn) (j : ℕ) :
    lb2_mom n k m₀ lam (t • f) j = t ^ j * lb2_mom n k m₀ lam f j := by
  unfold lb2_mom
  simp_rw [lb2_dsmear_smul, mul_pow]
  exact lb2_dexpect_const_mul _ _ _ _

/-- u₄(tf) = t⁴ u₄(f). -/
theorem lb2_u4_smul (m₀ lam t : ℝ) (f : TestFn) :
    lb2_u4 n k m₀ lam (t • f) = t ^ 4 * lb2_u4 n k m₀ lam f := by
  unfold lb2_u4; rw [lb2_mom_smul, lb2_mom_smul]; ring

end Model

/-! ## Part 6: the remaining analytic input and the reduction of M9 -/

/-- **The remaining analytic input of M9.** One test function f and constants δ > 0, K with,
uniformly in n ≥ N₀, k ≥ K₀: the smeared Ursell function is strictly negative,
u₄(f) = ⟨φ(f)⁴⟩ − 3⟨φ(f)²⟩² ≤ −δ, and ⟨φ(f)⁶⟩ ≤ K, ⟨φ(f)²⟩ ≤ K. -/
def UniformQuarticNegativity (m₀ lam : ℝ) : Prop :=
  ∃ f : TestFn, ∃ δ K : ℝ, 0 < δ ∧ ∃ N₀ K₀ : ℕ, ∀ n k : ℕ, N₀ ≤ n → K₀ ≤ k →
    lb2_u4 n k m₀ lam f ≤ -δ ∧ lb2_mom n k m₀ lam f 6 ≤ K ∧ lb2_mom n k m₀ lam f 2 ≤ K

/-- **UniformQuarticNegativity ⇒ QuarticDeficit** (λ ≥ 0, m₀ ≠ 0), with test function t·f,
t² = min(1/(4(K'+1)), δ/(4000(1+K')³)), K' = max K 0, and deficit δt⁴/4. -/
theorem lb2_quarticDeficit_of_uniform {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hU : UniformQuarticNegativity m₀ lam) : QuarticDeficit m₀ lam := by
  obtain ⟨f, δ, K, hδ, N₀, K₀, hU⟩ := hU
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  set s0 := min (1 / (4 * (K' + 1))) (δ / (4000 * (1 + K') ^ 3)) with hs0
  have hs0p : 0 < s0 := lt_min (by positivity) (by positivity)
  set t := Real.sqrt s0 with ht
  have htt : t ^ 2 = s0 := Real.sq_sqrt hs0p.le
  have htpos : 0 < t := Real.sqrt_pos.mpr hs0p
  have htK : 4 * (K' + 1) * t ^ 2 ≤ 1 := by
    rw [htt]
    have h := min_le_left (1 / (4 * (K' + 1))) (δ / (4000 * (1 + K') ^ 3))
    rw [← hs0, le_div_iff₀ (by positivity)] at h
    linarith
  have htδ : 4000 * (1 + K') ^ 3 * t ^ 2 ≤ δ := by
    rw [htt]
    have h := min_le_right (1 / (4 * (K' + 1))) (δ / (4000 * (1 + K') ^ 3))
    rw [← hs0, le_div_iff₀ (by positivity)] at h
    linarith
  refine ⟨t • f, δ * t ^ 4 / 4, by positivity, N₀, K₀, fun n k hn hk => ?_⟩
  obtain ⟨hu, h6, h2⟩ := hU n k hn hk
  have := isProbabilityMeasure_gibbs (n := n) (k := k) hm hlam
  have hX : AEStronglyMeasurable (dsmear n k f) (gibbs n k m₀ lam) := by
    have : Continuous (dsmear n k f) := by unfold dsmear; fun_prop
    exact this.aestronglyMeasurable
  have hI : ∀ j : ℕ, Integrable (fun φ => dsmear n k f φ ^ j) (gibbs n k m₀ lam) := fun j =>
    integrable_gibbs_of (lb2_integrable_dsmear_pow hm hlam f j)
  have hmj : ∀ j : ℕ, ∫ φ, dsmear n k f φ ^ j ∂(gibbs n k m₀ lam) = lb2_mom n k m₀ lam f j :=
    fun j => integral_gibbs m₀ lam _
  have T := lb2_taylor_deficit hX (hI 2) (hI 4) (hI 6) hK'0
    (by rw [hmj]; linarith) (by rw [hmj]; linarith)
    (by rw [hmj, hmj]; exact hu) htK htδ
  have e1 : ZD n k m₀ lam (Polynomial.X ^ 4) ((2 : ℝ) • t • f)
      = ((∫ φ, Real.cos (2 * t * dsmear n k f φ) ∂(gibbs n k m₀ lam) : ℝ) : ℂ) := by
    rw [lb2_ZD_eq_cos hm hlam]
    simp_rw [lb2_dsmear_smul, ← mul_assoc]
  have e2 : ZD n k m₀ lam (Polynomial.X ^ 4) (t • f)
      = ((∫ φ, Real.cos (t * dsmear n k f φ) ∂(gibbs n k m₀ lam) : ℝ) : ℂ) := by
    rw [lb2_ZD_eq_cos hm hlam]
    simp_rw [lb2_dsmear_smul]
  rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg T.1, (show Even 4 by decide).pow_abs]
  exact T.2

/-- **M9 reduced to `UniformQuarticNegativity`**: every limit point is non-Gaussian. -/
theorem lb2_nonGaussian_of_uniform {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hU : UniformQuarticNegativity m₀ lam) {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) :
    IsNonGaussian Z :=
  isNonGaussian_of_quarticDeficit (lb2_quarticDeficit_of_uniform hm hlam hU) hZ

end PP2Lebowitz2


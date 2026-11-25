import LongTable.Q_PP2NewmanA

/-!
Part B of PP2Newman (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Newman.lean)

FORMALIZED in this part.
* Model inputs: `boundedFKG_gibbs` (from `fkg_gibbs`), `integrable_gibbs_of`, integrability of
  φ_x and φ_x φ_y under `gibbs`, `integral_coord_nonneg` (⟨φ_x⟩ ≥ 0 from Griffiths I, so no
  φ ↦ −φ symmetry is needed), `integral_coord2` (∫ φ_x φ_y d gibbs = twoPt), and
  **`cov_lin_le`**: Cov(Σ c φ, Σ d φ) ≤ Σ Σ c_x d_y twoPt x y for c, d ≥ 0.
* `ZD_eq_gibbs`: ZD f = ⟨cos φ(f)⟩ + i ⟨sin φ(f)⟩ (gibbs integrals); `abs_cov_trig_le`: Newman's
  bound for each pair (T, U) ∈ {cos, sin}² of 1-Lipschitz bounded observables of φ(f), φ(g).
* **`newman_hN`** (λ ≥ 0, m₀ ≠ 0, all n k f g):
  ‖ZD(f+g) − ZD f · ZD g‖ ≤ 4 Σ_x Σ_y ε²|f(dpos x)| · ε²|g(dpos y)| · twoPt x y,
  exactly hypothesis hN of `clustering_of_simonLieb'` with κ = 4.
* **`clustering_of_simonLieb_newman`**: the end-to-end conditional of PP2M6Smeared with hN
  removed: SimonLiebIneq', RegionGriffithsI, SmallBoundarySum, RegionSusceptibility (λ ≥ 0,
  m₀ ≠ 0) ⟹ ∃ m > 0, FiniteCutoffClustering m₀ λ m.

NOT formalized.
* A sharper constant (Newman's paper, not re-read this session) (here κ = 4, from bounding real and imaginary
  parts separately; any absolute κ suffices for the clustering consumer).
* The M6 inputs SimonLiebIneq' (PP2SimonLieb4: `simonLiebIneq'_holds`) and RegionGriffithsI
  (PP2Assembly: `regionGriffithsI_holds`) are proved elsewhere for m₀ ≠ 0, λ ≥ 0;
  SmallBoundarySum and RegionSusceptibility remain OPEN hypotheses here.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Newman

section Model

open PP2Target PP2Griffiths PP2FKG

variable {n k : ℕ}

theorem integrable_lin {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (a : DSite n k → ℝ) :
    Integrable (lin a) (gibbs n k m₀ lam) := by
  unfold lin
  exact integrable_finsetSum _ fun x _ => (integrable_coord hm hlam x).const_mul (a x)

lemma lin_mul_lin (c d : DSite n k → ℝ) (φ : DField n k) :
    lin c φ * lin d φ = ∑ x, ∑ y, c x * d y * (φ x * φ y) := by
  unfold lin
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem integrable_lin_mul {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (c d : DSite n k → ℝ) :
    Integrable (fun φ => lin c φ * lin d φ) (gibbs n k m₀ lam) := by
  simp only [lin_mul_lin]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_coord2 hm hlam x y).const_mul _

/-- **Cov(Σ c φ, Σ d φ) ≤ Σ Σ c d ⟨φ_x φ_y⟩** for c, d ≥ 0 (uses ⟨φ_x⟩ ≥ 0, Griffiths I). -/
theorem cov_lin_le {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {c d : DSite n k → ℝ}
    (hc : ∀ x, 0 ≤ c x) (hd : ∀ x, 0 ≤ d x) :
    cov (gibbs n k m₀ lam) (lin c) (lin d)
      ≤ ∑ x, ∑ y, c x * d y * twoPt n k m₀ lam x y := by
  unfold cov
  simp only [lin_mul_lin]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_coord2 hm hlam x y).const_mul _]
  simp_rw [fun x => integral_finsetSum (μ := gibbs n k m₀ lam) Finset.univ
    (f := fun y φ => c x * d y * (φ x * φ y))
    fun y _ => (integrable_coord2 hm hlam x y).const_mul _]
  simp only [integral_const_mul, integral_coord2]
  have h1 : 0 ≤ ∫ φ, lin c φ ∂(gibbs n k m₀ lam) := by
    unfold lin
    rw [integral_finsetSum _ fun x _ => (integrable_coord hm hlam x).const_mul (c x)]
    exact Finset.sum_nonneg fun x _ => by
      rw [integral_const_mul]; exact mul_nonneg (hc x) (integral_coord_nonneg m₀ lam x)
  have h2 : 0 ≤ ∫ φ, lin d φ ∂(gibbs n k m₀ lam) := by
    unfold lin
    rw [integral_finsetSum _ fun x _ => (integrable_coord hm hlam x).const_mul (d x)]
    exact Finset.sum_nonneg fun x _ => by
      rw [integral_const_mul]; exact mul_nonneg (hd x) (integral_coord_nonneg m₀ lam x)
  nlinarith [mul_nonneg h1 h2]

end Model

/-! ## Part 3: the characteristic function and Newman's inequality -/

section Newman

open PP2Target PP2Griffiths PP2FKG

variable {n k : ℕ}

/-- The generating functional through `gibbs`: ZD f = ⟨cos φ(f)⟩ + i ⟨sin φ(f)⟩. -/
theorem ZD_eq_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f : TestFn) :
    ZD n k m₀ lam (Polynomial.X ^ 4) f =
      ((∫ φ, Real.cos (dsmear n k f φ) ∂(gibbs n k m₀ lam) : ℝ) : ℂ)
        + Complex.I * ((∫ φ, Real.sin (dsmear n k f φ) ∂(gibbs n k m₀ lam) : ℝ) : ℂ) := by
  have hds : Continuous (dsmear n k f) := by unfold dsmear; fun_prop
  have iw := integrable_dweight (n := n) (k := k) hm hlam
  have ic : Integrable fun φ => Real.cos (dsmear n k f φ) * dweight n k m₀ lam (Polynomial.X ^ 4) φ :=
    iw.bdd_mul (Real.continuous_cos.comp hds).aestronglyMeasurable
      (Eventually.of_forall fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have is : Integrable fun φ => Real.sin (dsmear n k f φ) * dweight n k m₀ lam (Polynomial.X ^ 4) φ :=
    iw.bdd_mul (Real.continuous_sin.comp hds).aestronglyMeasurable
      (Eventually.of_forall fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : (fun φ : DField n k => Complex.exp (Complex.I * (dsmear n k f φ : ℂ))
      * (dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℂ)) = fun φ =>
        ((Real.cos (dsmear n k f φ) * dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℝ) : ℂ)
        + Complex.I * ((Real.sin (dsmear n k f φ) * dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℝ) : ℂ) := by
    funext φ
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  have ic' : Integrable (fun φ : DField n k =>
      ((Real.cos (dsmear n k f φ) * dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℝ) : ℂ)) :=
    ic.ofReal
  have is' : Integrable (fun φ : DField n k => Complex.I *
      ((Real.sin (dsmear n k f φ) * dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℝ) : ℂ)) :=
    is.ofReal.const_mul Complex.I
  rw [ZD, e, integral_add ic' is', integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, integral_gibbs, integral_gibbs, dexpect, dexpect]
  push_cast
  ring

lemma dsmear_eq_lin (f : TestFn) (φ : DField n k) :
    dsmear n k f φ = lin (fun x => spacing n ^ 2 * f (dpos n k x)) φ := by
  unfold dsmear lin
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The bounded observables cos φ(f), sin φ(f) are dominated by Σ ε²|f| φ in Newman's sense. -/
lemma trig_lip (f : TestFn) {φ ψ : DField n k} (h : φ ≤ ψ) (T : ℝ → ℝ)
    (hT : ∀ u v, |T u - T v| ≤ |u - v|) :
    |T (dsmear n k f ψ) - T (dsmear n k f φ)|
      ≤ lin (fun x => |spacing n ^ 2 * f (dpos n k x)|) ψ
        - lin (fun x => |spacing n ^ 2 * f (dpos n k x)|) φ := by
  rw [dsmear_eq_lin, dsmear_eq_lin]
  exact (hT _ _).trans (abs_lin_sub_le _ h)

/-- **Newman's bound for one pair of trigonometric observables.** -/
theorem abs_cov_trig_le {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f g : TestFn)
    {T U : ℝ → ℝ} (hTc : Continuous T) (hUc : Continuous U) (hTb : ∀ u, |T u| ≤ 1)
    (hUb : ∀ u, |U u| ≤ 1) (hT : ∀ u v, |T u - T v| ≤ |u - v|)
    (hU : ∀ u v, |U u - U v| ≤ |u - v|) :
    |cov (gibbs n k m₀ lam) (fun φ => T (dsmear n k f φ)) (fun φ => U (dsmear n k g φ))|
      ≤ ∑ x, ∑ y, spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|)
          * twoPt n k m₀ lam x y := by
  have := isProbabilityMeasure_gibbs (n := n) (k := k) hm hlam
  have hsq : 0 ≤ spacing n ^ 2 := sq_nonneg _
  have hdf : Continuous (dsmear n k f) := by unfold dsmear; fun_prop
  have hdg : Continuous (dsmear n k g) := by unfold dsmear; fun_prop
  refine (abs_cov_le (gibbs n k m₀ lam) (boundedFKG_gibbs hm hlam)
    (hTc.comp hdf).measurable (hUc.comp hdg).measurable (continuous_lin _).measurable
    (continuous_lin _).measurable (fun φ => hTb _) (fun φ => hUb _)
    (integrable_lin hm hlam _) (integrable_lin hm hlam _) (integrable_lin_mul hm hlam _ _)
    (fun φ ψ h => trig_lip f h T hT) (fun φ ψ h => trig_lip g h U hU)).trans ?_
  refine (cov_lin_le hm hlam (fun x => abs_nonneg _) (fun x => abs_nonneg _)).trans
    (le_of_eq (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_))
  rw [abs_mul, abs_mul, abs_of_nonneg hsq]

/-- **Newman's inequality for the quartic Dirichlet box (hypothesis hN of
`conditional_clustering'`, with G = twoPt and κ = 4)**: for λ ≥ 0, m₀ ≠ 0, all n, k, f, g,
‖ZD(f+g) − ZD f · ZD g‖ ≤ 4 Σ_x Σ_y ε²|f(x)| ε²|g(y)| ⟨φ_x φ_y⟩. -/
theorem newman_hN {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (n k : ℕ) (f g : TestFn) :
    ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) g‖
      ≤ 4 * ∑ x : DSite n k, ∑ y : DSite n k,
          spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|)
            * twoPt n k m₀ lam x y := by
  have := isProbabilityMeasure_gibbs (n := n) (k := k) hm hlam
  set μ := gibbs n k m₀ lam
  set S := ∑ x : DSite n k, ∑ y : DSite n k,
    spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|) * twoPt n k m₀ lam x y
  set A := dsmear n k f
  set B := dsmear n k g
  have hA : Continuous A := by simp only [A]; unfold dsmear; fun_prop
  have hB : Continuous B := by simp only [B]; unfold dsmear; fun_prop
  have hAB : ∀ φ, dsmear n k (f + g) φ = A φ + B φ := fun φ => by
    simp only [A, B, dsmear, add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  have ib : ∀ h : DField n k → ℝ, Continuous h → (∀ φ, |h φ| ≤ 1) → Integrable h μ :=
    fun h hc hb => Integrable.of_bound hc.aestronglyMeasurable 1
      (Eventually.of_forall fun φ => by rw [Real.norm_eq_abs]; exact hb φ)
  have b2 : ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 → |a * b| ≤ 1 := fun a b ha hb => by
    rw [abs_mul]; exact (mul_le_mul ha hb (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have iCC := ib (fun φ => Real.cos (A φ) * Real.cos (B φ)) (by fun_prop)
    fun φ => b2 _ _ (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
  have iSS := ib (fun φ => Real.sin (A φ) * Real.sin (B φ)) (by fun_prop)
    fun φ => b2 _ _ (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
  have iSC := ib (fun φ => Real.sin (A φ) * Real.cos (B φ)) (by fun_prop)
    fun φ => b2 _ _ (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
  have iCS := ib (fun φ => Real.cos (A φ) * Real.sin (B φ)) (by fun_prop)
    fun φ => b2 _ _ (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  have hcos : ∫ φ, Real.cos (dsmear n k (f + g) φ) ∂μ
      = (∫ φ, Real.cos (A φ) * Real.cos (B φ) ∂μ) - ∫ φ, Real.sin (A φ) * Real.sin (B φ) ∂μ := by
    simp_rw [hAB, Real.cos_add]; exact integral_sub iCC iSS
  have hsin : ∫ φ, Real.sin (dsmear n k (f + g) φ) ∂μ
      = (∫ φ, Real.sin (A φ) * Real.cos (B φ) ∂μ) + ∫ φ, Real.cos (A φ) * Real.sin (B φ) ∂μ := by
    simp_rw [hAB, Real.sin_add]; exact integral_add iSC iCS
  have c1 := abs_cov_trig_le hm hlam f g (n := n) (k := k) Real.continuous_cos
    Real.continuous_cos Real.abs_cos_le_one Real.abs_cos_le_one Real.abs_cos_sub_cos_le
    Real.abs_cos_sub_cos_le
  have c2 := abs_cov_trig_le hm hlam f g (n := n) (k := k) Real.continuous_sin
    Real.continuous_sin Real.abs_sin_le_one Real.abs_sin_le_one Real.abs_sin_sub_sin_le
    Real.abs_sin_sub_sin_le
  have c3 := abs_cov_trig_le hm hlam f g (n := n) (k := k) Real.continuous_sin
    Real.continuous_cos Real.abs_sin_le_one Real.abs_cos_le_one Real.abs_sin_sub_sin_le
    Real.abs_cos_sub_cos_le
  have c4 := abs_cov_trig_le hm hlam f g (n := n) (k := k) Real.continuous_cos
    Real.continuous_sin Real.abs_cos_le_one Real.abs_sin_le_one Real.abs_cos_sub_cos_le
    Real.abs_sin_sub_sin_le
  unfold cov at c1 c2 c3 c4
  set cc := ∫ φ, Real.cos (A φ) * Real.cos (B φ) ∂μ
  set ss := ∫ φ, Real.sin (A φ) * Real.sin (B φ) ∂μ
  set sc := ∫ φ, Real.sin (A φ) * Real.cos (B φ) ∂μ
  set cs := ∫ φ, Real.cos (A φ) * Real.sin (B φ) ∂μ
  set ca := ∫ φ, Real.cos (A φ) ∂μ
  set sa := ∫ φ, Real.sin (A φ) ∂μ
  set cb := ∫ φ, Real.cos (B φ) ∂μ
  set sb := ∫ φ, Real.sin (B φ) ∂μ
  have key : ZD n k m₀ lam (Polynomial.X ^ 4) (f + g)
      - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) g
      = (((cc - ca * cb) - (ss - sa * sb) : ℝ) : ℂ)
        + Complex.I * (((sc - sa * cb) + (cs - ca * sb) : ℝ) : ℂ) := by
    rw [ZD_eq_gibbs hm hlam, ZD_eq_gibbs hm hlam, ZD_eq_gibbs hm hlam, hcos, hsin]
    push_cast
    linear_combination (-(sa : ℂ) * sb) * Complex.I_sq
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have e1 := abs_sub (cc - ca * cb) (ss - sa * sb)
  have e2 := abs_add_le (sc - sa * cb) (cs - ca * sb)
  linarith

/-- **End-to-end**: with Newman's inequality discharged, the M6 inputs alone give finite-cutoff
clustering at some rate m > 0 (λ ≥ 0, m₀ ≠ 0). -/
theorem clustering_of_simonLieb_newman {m₀ lam l γ A : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hl : 0 ≤ l) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hSus : RegionSusceptibility m₀ lam l A) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m :=
  clustering_of_simonLieb' hl hγ0 hγ1 hA (by norm_num : (0 : ℝ) ≤ 4) hSL hGI hSmall hSus
    (newman_hN hm hlam)

end Newman

end PP2Newman

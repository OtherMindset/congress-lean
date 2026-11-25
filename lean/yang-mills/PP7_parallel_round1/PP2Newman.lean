import LongTable.PP2FKG
import LongTable.PP2M6Smeared

/-!
Long Table, P(φ)₂ direction (BFS route), node M7, session 2: Newman's inequality for the quartic
Dirichlet-box model, discharging hypothesis hN of `conditional_clustering'` / `clustering_of_simonLieb'`
(PP2M6Smeared) with G = twoPt and the absolute constant κ = 4.

Source: C. M. Newman, CMP 74 (1980), Lemma/Theorem 1 (for FKG measures,
|⟨e^{i(A+B)}⟩ − ⟨e^{iA}⟩⟨e^{iB}⟩| ≤ C Σ |a_x||b_y| ⟨φ_x;φ_y⟩), proved here by the comparison route:
if G₁ ± F and G₂ ± H are increasing then |Cov(F,H)| ≤ Cov(G₁,G₂).

FORMALIZED.
* `BoundedFKG μ` (FKG for bounded measurable monotone observables) and **`fkg_of_integrable`**:
  FKG for measurable monotone F, G with F, G, FG integrable (truncation at ±N and dominated
  convergence; any preorder, any measure).
* `cov μ F H = ∫FH − ∫F∫H`; **`abs_cov_le`** (the abstract Newman comparison): for a bounded-FKG
  finite measure, F, H bounded measurable, G₁, G₂, G₁G₂ integrable, and
  |F y − F x| ≤ G₁ y − G₁ x, |H y − H x| ≤ G₂ y − G₂ x for x ≤ y: |Cov(F,H)| ≤ Cov(G₁,G₂)
  (FKG applied to the four pairs (G₁ ± F, G₂ ± H)).
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

/-! ## Part 1: FKG for integrable monotone observables, by truncation -/

section Abstract

variable {X : Type*} [MeasurableSpace X] [Preorder X] (μ : Measure X)

/-- FKG for bounded measurable monotone observables. -/
def BoundedFKG : Prop :=
  ∀ F G : X → ℝ, Measurable F → Measurable G → ∀ CF CG : ℝ, (∀ x, |F x| ≤ CF) →
    (∀ x, |G x| ≤ CG) → Monotone F → Monotone G →
      (∫ x, F x ∂μ) * (∫ x, G x ∂μ) ≤ ∫ x, F x * G x ∂μ

/-- Truncation at level N. -/
def trunc (N : ℕ) (t : ℝ) : ℝ := max (-(N : ℝ)) (min t N)

lemma trunc_mono (N : ℕ) : Monotone (trunc N) := fun _ _ h =>
  max_le_max le_rfl (min_le_min h le_rfl)

lemma abs_trunc_le_N (N : ℕ) (t : ℝ) : |trunc N t| ≤ N := by
  unfold trunc
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by have := N.cast_nonneg (α := ℝ); linarith) (min_le_right _ _)

lemma abs_trunc_le (N : ℕ) (t : ℝ) : |trunc N t| ≤ |t| := by
  unfold trunc
  rw [abs_le]
  have h1 := neg_abs_le t
  have h2 := le_abs_self t
  have h3 := N.cast_nonneg (α := ℝ)
  constructor
  · rcases le_total t N with h | h
    · rw [min_eq_left h]; exact le_trans h1 (le_max_right _ _)
    · rw [min_eq_right h]; exact le_trans (by linarith) (le_max_right _ _)
  · refine max_le (by linarith) ?_
    exact le_trans (min_le_left _ _) h2

lemma trunc_eventually (t : ℝ) : ∀ N ≥ ⌈|t|⌉₊, trunc N t = t := by
  intro N hN
  have h : |t| ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  rw [abs_le] at h
  unfold trunc
  rw [min_eq_left h.2, max_eq_right h.1]

lemma tendsto_trunc (t : ℝ) : Tendsto (fun N : ℕ => trunc N t) atTop (nhds t) :=
  tendsto_atTop_of_eventually_const (trunc_eventually t)

/-- **FKG for integrable monotone observables**: from bounded FKG by truncation and dominated
convergence. -/
theorem fkg_of_integrable (hFKG : BoundedFKG μ) {F G : X → ℝ} (hFm : Measurable F)
    (hGm : Measurable G) (hF : Monotone F) (hG : Monotone G) (iF : Integrable F μ)
    (iG : Integrable G μ) (iFG : Integrable (fun x => F x * G x) μ) :
    (∫ x, F x ∂μ) * (∫ x, G x ∂μ) ≤ ∫ x, F x * G x ∂μ := by
  have mF : ∀ N : ℕ, Measurable fun x => trunc N (F x) := fun N =>
    measurable_const.max (hFm.min measurable_const)
  have mG : ∀ N : ℕ, Measurable fun x => trunc N (G x) := fun N =>
    measurable_const.max (hGm.min measurable_const)
  have hN : ∀ N : ℕ, (∫ x, trunc N (F x) ∂μ) * (∫ x, trunc N (G x) ∂μ)
      ≤ ∫ x, trunc N (F x) * trunc N (G x) ∂μ := fun N =>
    hFKG _ _ (mF N) (mG N) N N (fun x => abs_trunc_le_N N _) (fun x => abs_trunc_le_N N _)
      (fun _ _ h => trunc_mono N (hF h)) (fun _ _ h => trunc_mono N (hG h))
  have t1 : Tendsto (fun N : ℕ => ∫ x, trunc N (F x) ∂μ) atTop (nhds (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => |F x|)
      (fun N => (mF N).aestronglyMeasurable) iF.abs
      (fun N => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_trunc_le N _)
      (Eventually.of_forall fun x => tendsto_trunc _)
  have t2 : Tendsto (fun N : ℕ => ∫ x, trunc N (G x) ∂μ) atTop (nhds (∫ x, G x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => |G x|)
      (fun N => (mG N).aestronglyMeasurable) iG.abs
      (fun N => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_trunc_le N _)
      (Eventually.of_forall fun x => tendsto_trunc _)
  have t3 : Tendsto (fun N : ℕ => ∫ x, trunc N (F x) * trunc N (G x) ∂μ) atTop
      (nhds (∫ x, F x * G x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => |F x * G x|)
      (fun N => ((mF N).mul (mG N)).aestronglyMeasurable) iFG.abs
      (fun N => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul (abs_trunc_le N _) (abs_trunc_le N _) (abs_nonneg _) (abs_nonneg _))
      (Eventually.of_forall fun x => (tendsto_trunc _).mul (tendsto_trunc _))
  exact le_of_tendsto_of_tendsto' (t1.mul t2) t3 hN

/-- The covariance ∫ F H − ∫ F ∫ H. -/
def cov (F H : X → ℝ) : ℝ := (∫ x, F x * H x ∂μ) - (∫ x, F x ∂μ) * ∫ x, H x ∂μ

/-- One sign combination of the covariance comparison. -/
lemma cov_sign (hFKG : BoundedFKG μ) [IsFiniteMeasure μ] {F H G₁ G₂ : X → ℝ}
    (hFm : Measurable F) (hHm : Measurable H) (hG₁m : Measurable G₁) (hG₂m : Measurable G₂)
    {CF CH : ℝ} (hFb : ∀ x, |F x| ≤ CF) (hHb : ∀ x, |H x| ≤ CH)
    (iG₁ : Integrable G₁ μ) (iG₂ : Integrable G₂ μ) (iG : Integrable (fun x => G₁ x * G₂ x) μ)
    {s t : ℝ} (hs : Monotone fun x => G₁ x + s * F x) (ht : Monotone fun x => G₂ x + t * H x) :
    (∫ x, G₁ x ∂μ + s * ∫ x, F x ∂μ) * (∫ x, G₂ x ∂μ + t * ∫ x, H x ∂μ)
      ≤ (∫ x, G₁ x * G₂ x ∂μ) + t * (∫ x, G₁ x * H x ∂μ) + s * (∫ x, F x * G₂ x ∂μ)
        + s * t * ∫ x, F x * H x ∂μ := by
  have bF : ∀ᵐ x ∂μ, ‖F x‖ ≤ CF := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hFb x
  have bH : ∀ᵐ x ∂μ, ‖H x‖ ≤ CH := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hHb x
  have iF : Integrable F μ := Integrable.of_bound hFm.aestronglyMeasurable CF bF
  have iH : Integrable H μ := Integrable.of_bound hHm.aestronglyMeasurable CH bH
  have iFH : Integrable (fun x => F x * H x) μ := iH.bdd_mul hFm.aestronglyMeasurable bF
  have iFG : Integrable (fun x => F x * G₂ x) μ := iG₂.bdd_mul hFm.aestronglyMeasurable bF
  have iGH : Integrable (fun x => G₁ x * H x) μ := by
    have := iG₁.bdd_mul hHm.aestronglyMeasurable bH
    exact this.congr (Eventually.of_forall fun x => by simp only; ring)
  have i1 : Integrable (fun x => G₁ x * G₂ x + t * (G₁ x * H x)) μ := iG.add (iGH.const_mul t)
  have i2 : Integrable (fun x => s * (F x * G₂ x) + s * t * (F x * H x)) μ :=
    (iFG.const_mul s).add (iFH.const_mul (s * t))
  have i3 : Integrable (fun x => G₁ x + s * F x) μ := iG₁.add (iF.const_mul s)
  have i4 : Integrable (fun x => G₂ x + t * H x) μ := iG₂.add (iH.const_mul t)
  have i5 : Integrable (fun x => (G₁ x + s * F x) * (G₂ x + t * H x)) μ :=
    (i1.add i2).congr (Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have h := fkg_of_integrable μ hFKG (F := fun x => G₁ x + s * F x)
    (G := fun x => G₂ x + t * H x) (hG₁m.add (hFm.const_mul s)) (hG₂m.add (hHm.const_mul t))
    hs ht i3 i4 i5
  have e : (fun x => (G₁ x + s * F x) * (G₂ x + t * H x)) = fun x =>
      (G₁ x * G₂ x + t * (G₁ x * H x)) + (s * (F x * G₂ x) + s * t * (F x * H x)) := by
    funext x; ring
  rw [e, integral_add i1 i2,
    integral_add iG (iGH.const_mul t), integral_add (iFG.const_mul s) (iFH.const_mul (s * t)),
    integral_add iG₁ (iF.const_mul s), integral_add iG₂ (iH.const_mul t),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul] at h
  linarith

/-- **The abstract Newman comparison**: for an FKG measure, if F and H are bounded and
|F y − F x| ≤ G₁ y − G₁ x, |H y − H x| ≤ G₂ y − G₂ x for x ≤ y (so G₁ ± F, G₂ ± H are increasing),
with G₁, G₂, G₁G₂ integrable, then |Cov(F, H)| ≤ Cov(G₁, G₂). -/
theorem abs_cov_le (hFKG : BoundedFKG μ) [IsFiniteMeasure μ] {F H G₁ G₂ : X → ℝ}
    (hFm : Measurable F) (hHm : Measurable H) (hG₁m : Measurable G₁) (hG₂m : Measurable G₂)
    {CF CH : ℝ} (hFb : ∀ x, |F x| ≤ CF) (hHb : ∀ x, |H x| ≤ CH)
    (iG₁ : Integrable G₁ μ) (iG₂ : Integrable G₂ μ) (iG : Integrable (fun x => G₁ x * G₂ x) μ)
    (hF : ∀ x y, x ≤ y → |F y - F x| ≤ G₁ y - G₁ x)
    (hH : ∀ x y, x ≤ y → |H y - H x| ≤ G₂ y - G₂ x) :
    |cov μ F H| ≤ cov μ G₁ G₂ := by
  have mono : ∀ {F G : X → ℝ}, (∀ x y, x ≤ y → |F y - F x| ≤ G y - G x) →
      ∀ s : ℝ, (s = 1 ∨ s = -1) → Monotone fun x => G x + s * F x := by
    intro F G h s hs x y hxy
    have := h x y hxy
    rw [abs_le] at this
    rcases hs with rfl | rfl <;> simp only <;> linarith [this.1, this.2]
  have k := fun s t hs ht => cov_sign μ hFKG hFm hHm hG₁m hG₂m hFb hHb iG₁ iG₂ iG
    (s := s) (t := t) (mono hF s hs) (mono hH t ht)
  have k1 := k 1 1 (Or.inl rfl) (Or.inl rfl)
  have k2 := k (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  have k3 := k 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have k4 := k (-1) 1 (Or.inr rfl) (Or.inl rfl)
  unfold cov
  rw [abs_le]
  constructor <;> nlinarith

end Abstract

/-! ## Part 2: the quartic Dirichlet-box model -/

section Model

open PP2Target PP2Griffiths PP2FKG

variable {n k : ℕ}

/-- The quartic box Gibbs measure satisfies bounded FKG (from `fkg_gibbs`). -/
theorem boundedFKG_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    BoundedFKG (gibbs n k m₀ lam) := fun _ _ hFm hGm _ _ hFb hGb hF hG =>
  fkg_gibbs hm hlam hFm hGm hFb hGb hF hG

/-- Integrability against `gibbs` from integrability of F · dweight. -/
theorem integrable_gibbs_of {m₀ lam : ℝ} {F : DField n k → ℝ}
    (hF : Integrable fun φ => F φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ) :
    Integrable F (gibbs n k m₀ lam) := by
  rw [gibbs, integrable_withDensity_iff_integrable_smul'
    (((continuous_dweight m₀ lam _).measurable.div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hF.div_const (∫ ψ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) ψ)).congr
    (Eventually.of_forall fun φ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (dweight_pos' _ _ _ _).le (Z_nonneg m₀ lam))]
  ring

lemma prod_pow_single (φ : DField n k) (x : DSite n k) :
    ∏ z, φ z ^ (Pi.single x 1 : DSite n k → ℕ) z = φ x := by
  rw [Finset.prod_eq_single x]
  · simp
  · intro z _ hz; simp [hz]
  · simp

lemma prod_pow_two (φ : DField n k) (x y : DSite n k) :
    ∏ z, φ z ^ (((Pi.single x 1 : DSite n k → ℕ) + (Pi.single y 1 : DSite n k → ℕ)) z) = φ x * φ y := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single]

theorem integrable_coord {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (x : DSite n k) :
    Integrable (fun φ : DField n k => φ x) (gibbs n k m₀ lam) := by
  refine integrable_gibbs_of ((integrable_mono_dweight hm hlam (Pi.single x 1)).congr
    (Eventually.of_forall fun φ => ?_))
  simp only [prod_pow_single]

theorem integrable_coord2 {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (x y : DSite n k) :
    Integrable (fun φ : DField n k => φ x * φ y) (gibbs n k m₀ lam) := by
  refine integrable_gibbs_of ((integrable_mono_dweight hm hlam
    ((Pi.single x 1 : DSite n k → ℕ) + Pi.single y 1)).congr
      (Eventually.of_forall fun φ => ?_))
  simp only [prod_pow_two]

/-- ⟨φ_x⟩ ≥ 0 (Griffiths I). -/
theorem integral_coord_nonneg (m₀ lam : ℝ) (x : DSite n k) :
    0 ≤ ∫ φ : DField n k, φ x ∂(gibbs n k m₀ lam) := by
  have h := dexpect_mono_nonneg (n := n) (k := k) m₀ lam (Pi.single x 1)
  rw [integral_gibbs]
  simpa only [prod_pow_single] using h

/-- ∫ φ_x φ_y d(gibbs) = twoPt x y. -/
theorem integral_coord2 (m₀ lam : ℝ) (x y : DSite n k) :
    ∫ φ : DField n k, φ x * φ y ∂(gibbs n k m₀ lam) = twoPt n k m₀ lam x y := by
  rw [integral_gibbs]; rfl

/-- A linear functional of the field. -/
def lin (a : DSite n k → ℝ) (φ : DField n k) : ℝ := ∑ x, a x * φ x

lemma continuous_lin (a : DSite n k → ℝ) : Continuous (lin a) := by
  unfold lin; fun_prop

lemma abs_lin_sub_le (a : DSite n k → ℝ) {φ ψ : DField n k} (h : φ ≤ ψ) :
    |lin a ψ - lin a φ| ≤ lin (fun x => |a x|) ψ - lin (fun x => |a x|) φ := by
  unfold lin
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  rw [← mul_sub, ← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.2 (h x))]

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


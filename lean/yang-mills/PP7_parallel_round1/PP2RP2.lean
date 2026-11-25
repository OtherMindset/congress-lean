import LongTable.PP2RP
import LongTable.PP2TargetV4

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Hamiltonian track H, session 2.
Complex reflection positivity, the finite OS pre-Hilbert space, finite-volume OS matrix elements
of e^{iφ(f)}, and RP of limit points (modulo one named estimate). Builds on PP2RP (session 1:
`rp_dweight_bounded`, `dweight_reflX`, `glue_reflX`, `RightLocal`, `reflX`) and PP2TargetV4
(`PositiveTime`, `reflect`, `timeShift`; `OSGap`, `HamiltonianGap`). Quartic model
P = X⁴, m₀ ≠ 0, λ ≥ 0, box with n + k ≥ 1 throughout.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* Reflection on fields `reflF φ = φ ∘ reflX`, involutive (`reflF_reflF`); `integral_reflF`:
  ∫ f(Θφ) dφ = ∫ f(φ) dφ for EVERY f into any real Banach space (no integrability: in glued
  coordinates Θ is the swap of halves, `integral_prod_swap`). `integral_refl_symm`:
  ∫ ΘA·B·w = ∫ ΘB·A·w for all real A, B.
* Goal 1. `rp_complex`: for F : DField → ℂ right-local (`RightLocalC`), measurable, bounded,
    0 ≤ ∫ conj(F∘Θ) · F · dweight      (in `ComplexOrder`: re ≥ 0 and im = 0).
  Proof: F = a + ib; re = ∫Θa·a·w + ∫Θb·b·w ≥ 0 by `rp_dweight_bounded`; im = ∫Θa·b·w − ∫Θb·a·w
  = 0 by `integral_refl_symm`. All integrands are shown integrable (`integrable_osInt`,
  `integrable_real_mul_dweight`), so these are genuine Bochner integrals.
* Goal 2. `osSpace n k : Submodule ℂ (DField n k → ℂ)`: right-local, measurable, bounded
  observables. `partZ` = ∫ dweight, `partZ_pos`. `osForm F G = ∫ conj(ΘF)·G·dweight / Z`.
  - `osForm_conj_symm`: ⟪G, F⟫ = conj⟪F, G⟫ (for ALL F, G);
  - `osForm_add_right`, `osForm_smul_right`, `osForm_add_left`, `osForm_smul_left`
    (additivity needs `BddMeas`; homogeneity holds for all F, G): sesquilinear, conjugate-linear
    in the first slot (Mathlib's convention, matching `OSGap`);
  - `osForm_nonneg` (0 ≤ ⟪F, F⟫ in ComplexOrder), `osForm_re_nonneg`, `osForm_im_self`;
  - `osForm_cauchy_schwarz`: ‖⟪F, G⟫‖² ≤ re⟪F, F⟫ · re⟪G, G⟫ on `osSpace` (via `cs_aux`,
    a discriminant argument valid for semidefinite forms);
  - `osForm_null`: ⟪F, F⟫ = 0 ⇒ ⟪F, G⟫ = 0 (null vectors = kernel of the form).
* Exponential observables. `expObs n k f = e^{i·dsmear f}` (the box version of ψ f).
  `osObs_expObs`: for `PositiveTime f` it lies in `osSpace` (support at x₀ > 0 forces i ≥ N/2,
  via εN = L, `spacing_mul_boxN`). `latRefl n f = τ_(−ε,0)(Θf)`: the lattice reflection
  i ↦ N−1−i is x₀ ↦ −x₀ − ε in physical coordinates (`latRefl_dpos`, `dsmear_reflF`).
  `osForm_expObs`: ⟪e^{iφ(f)}, e^{iφ(g)}⟫ = ZD(g − τ_(−ε)Θf) (any f, g). `osForm_sum_left/right`
  (finite sums). `rp_ZD`: for positive-time f_i, c_i ∈ ℂ,
    0 ≤ Σ_{i,j} conj(c_i) c_j ZD_{n,k}(f_j − τ_(−ε)Θf_i).
* Limit. `OSPositive Z`: 0 ≤ Σ_{i,j} conj(c_i) c_j Z(f_j − Θf_i) for positive-time f_i.
  `LatticeReflStable m₀ λ` (a HYPOTHESIS, not proved): ZD_{n,k}(g − τ_(−ε)Θf) − ZD_{n,k}(g − Θf)
  → 0 as (n, k) → ∞. `osPositive_of_limitPoint`: under it, every `IsLimitPoint m₀ λ Z` is
  OS positive (finite sums of convergent entries; the cone {z ≥ 0} of ℂ is closed).

NOT formalized.
* Quotient by null vectors and completion (the actual Hilbert space); the time-shift operator;
  polynomial observables; the O(2) model (the same proofs apply componentwise).
* `LatticeReflStable` itself, and the other analytic inputs listed in the plan below.

PLAN: FROM HERE TO `HamiltonianGap Z m` VIA `PP2Gap.semigroup_gap`.
(P0) Exact hypotheses of `semigroup_gap` (PP2SemigroupGap): complete inner-product space E over
  RCLike 𝕜; T : ℝ → E →L E with T t self-adjoint and T(s + t) = T s T t for s, t ≥ 0; Ω unit,
  T t Ω = Ω; D ⊆ Ω^⊥ whose closure contains Ω^⊥; for each v ∈ D a constant C with
  re⟪v, T s v⟫ ≤ C e^{−ms} for ALL real s ≥ 0. Output: ‖T t u‖ ≤ e^{−mt}‖u‖ on Ω^⊥, which is
  exactly the last clause of `OSGap`. No strong continuity, no generator, no contraction needed.
(P1) Time translation at finite lattice. The shift by one column, φ ↦ φ(· − e₁), is NOT a
  symmetry of the Dirichlet box (it moves the Dirichlet walls), and lattice time is εℤ, while
  `OSGap` needs T(t) for every real t ≥ 0. Two standard routes: (a) transfer matrix in the box
  (T_box = V^½ K V^½ on L²(ℝ^N), the box's own Hamiltonian; Glimm–Jaffe ch. 6, 19); (b) OS
  reconstruction from the LIMIT Schwinger functional (Osterwalder–Schrader 1973/75, Glimm–Jaffe
  §6.1, §19.1): first pass RP, Θ-invariance and time-translation invariance to the limit Z, then
  build H, T(t) from Z. Since `HamiltonianGap Z m` is a statement about the limit Z only, and
  the box transfer matrix is neither translation invariant nor needed for the limit, we
  RECOMMEND (b) and DROP the box transfer matrix (session-1 item 1). Proving OSGap for limit
  points only is the right reading of `PhiFourTwoGapV4` (it quantifies over limit points).
(P2) Abstract OS reconstruction (pure functional analysis, no model input). Hypotheses on
  Z : TestFn → ℂ: Z 0 = 1; Hermitian conj Z(h) = Z(−h); Θ-invariant Z(Θh) = Z(h);
  time-translation invariant Z(τ_(t,0) h) = Z(h); `OSPositive Z`; |Z| ≤ 1 (automatic for a
  limit of characteristic functionals). Construction: V = finitely supported ℂ-combinations
  of positive-time compactly supported f (`Finsupp`), ⟪Σ c_i f_i, Σ d_j g_j⟫ = Σ conj c_i d_j
  Z(g_j − Θf_i); quotient by null vectors (Cauchy–Schwarz as in `osForm_cauchy_schwarz`,
  abstracted), completion (Mathlib `UniformSpace.Completion` of the quotient inner-product
  space); ψ f = class of δ_f, Ω = ψ 0. T(t)[δ_g] = [δ_(τ_t g)]: well-defined and bounded by the
  OS iterated Cauchy–Schwarz ‖T(t)v‖² = ⟪v, T(2t)v⟫ ≤ ‖v‖ ‖T(2t)v‖ ≤ … ≤ ‖v‖^(2−2^−j)
  ⟪v, T(2^j t) v⟫^(2^−j), with |⟪v, T(s)v⟫| ≤ (Σ|c_i|)² from |Z| ≤ 1, giving ‖T(t)‖ ≤ 1;
  self-adjoint from Θτ_t = τ_(−t)Θ, Θ-invariance and Hermiticity; semigroup, T(0) = 1, TΩ = Ω
  and the matrix-element formula are then by construction. Density of span ψ(·) is by
  construction. Output: everything in `OSGap` except the gap clause.
(P3) Gap. D = {v − ⟪Ω, v⟫Ω : v ∈ span ψ(positive-time, compact support)}: ⊆ Ω^⊥, and its closure
  is Ω^⊥ (projection of a dense set). For v = Σ c_i ψ f_i − ⟪Ω,·⟫Ω,
  ⟪v, T(s)v⟫ = Σ conj c_i c_j [Z(τ_s f_j − Θf_i) − Z(−Θf_i) Z(f_j)] (uses Z(τ_s f_j) = Z(f_j)),
  and `ClustersAt Z m` (from `FiniteCutoffClustering` by `limitPoint_clusters`, with translation
  a = (s, 0), max(|a₀|, |a₁|) = s) bounds each bracket by C_ij e^{−ms}. Feed to `semigroup_gap`.
(P4) What passes to the limit (n, k → ∞ along the limit-point sequence), and the estimates:
  - Z 0 = 1, Hermiticity, |Z| ≤ 1: pointwise identities/bounds of ZD; pass trivially.
  - RP: `rp_ZD` + `LatticeReflStable` (done here: `osPositive_of_limitPoint`).
  - Θ-invariance: ZD_{n,k}(τ_(−ε)Θf) = ZD_{n,k}(f) exactly (a few lines from `dsmear_reflF`,
    `dweight_reflF`, `integral_reflF`; not written), then `LatticeReflStable` again.
  - Time-translation invariance: NOT exact in the box. Needs (E2) boundary decoupling:
    ZD_{n,k}(τ_a h) − ZD_{n,k}(h) → 0 as k → ∞ (uniformly in n) for fixed compactly supported
    h and a, plus (E1) for non-lattice shifts. E2 is an infinite-volume-limit statement; it is
    NOT a consequence of `FiniteCutoffClustering` as stated and must come from the construction.
  - Clustering: already in the target's hypotheses (`FiniteCutoffClustering`).
  - (E1) equicontinuity: |ZD_{n,k}(h) − ZD_{n,k}(h')| ≤ C · p(h − h') for a Schwartz seminorm p,
    uniformly in n, k; follows from a uniform two-point bound E_box[φ(h)²] ≤ C p(h)². It implies
    `LatticeReflStable` (τ_(−ε)Θf → Θf in Schwartz space). Caveat: with Wick ordering at the
    infinite-lattice variance c = freeVar n m₀ ~ log(1/ε), :φ⁴: contains −6cλφ², so the naive
    Gaussian-domination bound is NOT uniform in n; E1 has to come from the cluster expansion /
    BFS analysis that also yields `FiniteCutoffClustering`.
(P5) REVISED SESSION ESTIMATE for track H (plan was 8–10). Done: S1 (real RP), S2 (this file).
  Remaining, with E1, E2 taken as named Prop hypotheses (they belong to the analytic track):
  S3 abstract psd Hermitian form → quotient → completion (generic; 1–2 sessions);
  S4 time-shift operators on it: well-definedness, iterated-CS contraction, self-adjointness,
     semigroup, extension to the completion (2 sessions);
  S5 `OSGap` assembly + gap via `semigroup_gap` from `ClustersAt` (1 session);
  S6 limit passage of Θ-invariance, Hermiticity, |Z| ≤ 1, translation invariance from E1/E2
     (1 session).
  Total 7–8 sessions for the CONDITIONAL theorem "FiniteCutoffClustering + E1 + E2 + IsLimitPoint
  ⇒ HamiltonianGap"; i.e. inside the old 8–10 at the low end, by dropping the box transfer matrix.
  Discharging E1 and E2 unconditionally is a construction-track result (uniform-in-volume and
  -cutoff estimates) and is not counted here.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Real
open scoped ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2RP2

open PP2Target PP2Griffiths PP2RP

variable {n k : ℕ}

/-! ## The reflection on fields and the reflection symmetry of integrals -/

/-- The reflected field (Θφ)(x) = φ(reflX x). -/
def reflF (φ : DField n k) : DField n k := fun x => φ (reflX x)

theorem reflX_reflX (x : DSite n k) : reflX (reflX x) = x := by
  simp [reflX]

theorem reflF_reflF (φ : DField n k) : reflF (reflF φ) = φ := by
  funext x; simp [reflF, reflX_reflX]

theorem continuous_reflF : Continuous (reflF (n := n) (k := k)) :=
  continuous_pi fun x => continuous_apply (reflX x)

theorem measurable_reflF : Measurable (reflF (n := n) (k := k)) := continuous_reflF.measurable

/-- `integral_glue` of PP2RP for any Banach-space valued integrand. -/
theorem integral_glue' (hnk : 0 < n + k) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DField n k → E) :
    ∫ φ, f φ = ∫ z : (HSite n k → ℝ) × (HSite n k → ℝ), f (glue hnk z) := by
  rw [← (glueME_mp hnk).integral_comp' f]
  simp only [glueME_apply]

/-- Lebesgue measure on the box is invariant under the reflection: ∫ f(Θφ) dφ = ∫ f(φ) dφ
(for every f; no integrability needed). Proof: in glued coordinates Θ is the swap of the halves. -/
theorem integral_reflF (hnk : 0 < n + k) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DField n k → E) : ∫ φ, f (reflF φ) = ∫ φ, f φ := by
  rw [integral_glue' hnk (fun φ => f (reflF φ)), integral_glue' hnk f]
  have h : ∀ z : (HSite n k → ℝ) × (HSite n k → ℝ), reflF (glue hnk z) = glue hnk z.swap :=
    fun z => glue_reflX hnk z
  simp_rw [h]
  rw [Measure.volume_eq_prod]
  exact integral_prod_swap (fun z => f (glue hnk z))

theorem dweight_reflF (hnk : 0 < n + k) (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) :
    dweight n k m₀ lam P (reflF φ) = dweight n k m₀ lam P φ :=
  dweight_reflX hnk m₀ lam P φ

/-- The real symmetry ∫ ΘA · B · dweight = ∫ ΘB · A · dweight (any A, B). -/
theorem integral_refl_symm (hnk : 0 < n + k) (m₀ lam : ℝ) (P : Polynomial ℝ)
    (A B : DField n k → ℝ) :
    ∫ φ, A (reflF φ) * B φ * dweight n k m₀ lam P φ
      = ∫ φ, B (reflF φ) * A φ * dweight n k m₀ lam P φ := by
  have h := integral_reflF hnk (fun φ => B (reflF φ) * A φ * dweight n k m₀ lam P φ)
  simp only [reflF_reflF, dweight_reflF hnk] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun φ => by ring)

/-! ## Complex observables -/

/-- F depends only on the field in the right half {x | N/2 ≤ x.1} (complex version of
`PP2RP.RightLocal`). -/
def RightLocalC (F : DField n k → ℂ) : Prop :=
  ∀ φ φ' : DField n k, (∀ x : DSite n k, halfN n k ≤ (x.1 : ℕ) → φ x = φ' x) → F φ = F φ'

/-- Measurable and bounded. -/
def BddMeas (F : DField n k → ℂ) : Prop := Measurable F ∧ ∃ C : ℝ, ∀ φ, ‖F φ‖ ≤ C

theorem BddMeas.mul {F G : DField n k → ℂ} (hF : BddMeas F) (hG : BddMeas G) :
    BddMeas fun φ => F φ * G φ := by
  obtain ⟨hFm, C, hC⟩ := hF
  obtain ⟨hGm, D, hD⟩ := hG
  refine ⟨hFm.mul hGm, C * D, fun φ => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC φ) (hD φ) (norm_nonneg _) ((norm_nonneg _).trans (hC φ))

theorem BddMeas.add {F G : DField n k → ℂ} (hF : BddMeas F) (hG : BddMeas G) :
    BddMeas (F + G) := by
  obtain ⟨hFm, C, hC⟩ := hF
  obtain ⟨hGm, D, hD⟩ := hG
  exact ⟨hFm.add hGm, C + D, fun φ => (norm_add_le _ _).trans (add_le_add (hC φ) (hD φ))⟩

theorem BddMeas.smul {F : DField n k → ℂ} (hF : BddMeas F) (c : ℂ) : BddMeas (c • F) := by
  obtain ⟨hFm, C, hC⟩ := hF
  refine ⟨hFm.const_smul c, ‖c‖ * C, fun φ => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC φ) (norm_nonneg _)

theorem BddMeas.zero : BddMeas (0 : DField n k → ℂ) :=
  ⟨measurable_const, 0, fun φ => by simp⟩

theorem BddMeas.reflConj {F : DField n k → ℂ} (hF : BddMeas F) :
    BddMeas fun φ => conj (F (reflF φ)) := by
  obtain ⟨hFm, C, hC⟩ := hF
  exact ⟨continuous_star.measurable.comp (hFm.comp measurable_reflF), C,
    fun φ => by rw [Complex.norm_conj]; exact hC _⟩

/-- The admissible observables: right-local, measurable, bounded. -/
def OSObs (F : DField n k → ℂ) : Prop := RightLocalC F ∧ BddMeas F

/-- **The finite OS pre-Hilbert space** as a complex vector space: right-local bounded
measurable complex observables. -/
def osSpace (n k : ℕ) : Submodule ℂ (DField n k → ℂ) where
  carrier := {F | OSObs F}
  zero_mem' := ⟨fun _ _ _ => rfl, BddMeas.zero⟩
  add_mem' := by
    rintro F G ⟨hFl, hF⟩ ⟨hGl, hG⟩
    refine ⟨fun φ φ' h => ?_, hF.add hG⟩
    simp only [Pi.add_apply]; rw [hFl φ φ' h, hGl φ φ' h]
  smul_mem' := by
    rintro c F ⟨hFl, hF⟩
    refine ⟨fun φ φ' h => ?_, hF.smul c⟩
    simp only [Pi.smul_apply]; rw [hFl φ φ' h]

theorem mem_osSpace {F : DField n k → ℂ} : F ∈ osSpace n k ↔ OSObs F := Iff.rfl

/-! ### Integrability -/

theorem integrable_mul_dweight {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {H : DField n k → ℂ} (hH : BddMeas H) :
    Integrable fun φ => H φ * (dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℂ) := by
  obtain ⟨hHm, C, hC⟩ := hH
  refine Integrable.mono' ((integrable_dweight hm hlam).const_mul C)
    (hHm.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (continuous_dweight m₀ lam _)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun φ => ?_)
  have hw : 0 < dweight n k m₀ lam (Polynomial.X ^ 4) φ := Real.exp_pos _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  exact mul_le_mul_of_nonneg_right (hC φ) hw.le

theorem integrable_real_mul_dweight {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {g : DField n k → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ φ, |g φ| ≤ C) :
    Integrable fun φ => g φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  refine Integrable.mono' ((integrable_dweight hm hlam).const_mul C)
    (hg.aestronglyMeasurable.mul (continuous_dweight m₀ lam _).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun φ => ?_)
  have hw : 0 < dweight n k m₀ lam (Polynomial.X ^ 4) φ := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
  exact mul_le_mul_of_nonneg_right (hC φ) hw.le

/-! ### Goal 1: reflection positivity for complex observables -/

/-- The unnormalised OS form ∫ conj(ΘF) · G · dweight. -/
def osInt (m₀ lam : ℝ) (F G : DField n k → ℂ) : ℂ :=
  ∫ φ, conj (F (reflF φ)) * G φ * (dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℂ)

theorem integrable_osInt {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F G : DField n k → ℂ} (hF : BddMeas F) (hG : BddMeas G) :
    Integrable fun φ => conj (F (reflF φ)) * G φ * (dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℂ) :=
  integrable_mul_dweight hm hlam (H := fun φ => conj (F (reflF φ)) * G φ) (hF.reflConj.mul hG)

theorem re_integral {f : DField n k → ℂ} (hf : Integrable f) :
    (∫ φ, f φ).re = ∫ φ, (f φ).re := by
  have h := integral_re hf
  simp only [RCLike.re_to_complex] at h
  exact h.symm

theorem im_integral {f : DField n k → ℂ} (hf : Integrable f) :
    (∫ φ, f φ).im = ∫ φ, (f φ).im := by
  have h := integral_im hf
  simp only [RCLike.im_to_complex] at h
  exact h.symm

/-- **Reflection positivity for complex bounded observables** (quartic model, m₀ ≠ 0, λ ≥ 0):
∫ conj(ΘF) · F · dweight is a nonnegative real number (`0 ≤ z` in `ComplexOrder` means
0 ≤ re z and im z = 0). Proof: F = a + ib; the real part is ∫ Θa·a·w + ∫ Θb·b·w ≥ 0 by
`rp_dweight_bounded`, the imaginary part ∫ Θa·b·w − ∫ Θb·a·w vanishes by `integral_refl_symm`. -/
theorem rp_complex (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F : DField n k → ℂ} (hF : OSObs F) : 0 ≤ osInt m₀ lam F F := by
  obtain ⟨hFl, hFm, C, hC⟩ := hF
  set a : DField n k → ℝ := fun φ => (F φ).re with ha
  set b : DField n k → ℝ := fun φ => (F φ).im with hb
  have ham : Measurable a := Complex.measurable_re.comp hFm
  have hbm : Measurable b := Complex.measurable_im.comp hFm
  have haC : ∀ φ, |a φ| ≤ C := fun φ => (Complex.abs_re_le_norm _).trans (hC φ)
  have hbC : ∀ φ, |b φ| ≤ C := fun φ => (Complex.abs_im_le_norm _).trans (hC φ)
  have hal : RightLocal a := fun φ φ' h => by simp only [ha]; rw [hFl φ φ' h]
  have hbl : RightLocal b := fun φ φ' h => by simp only [hb]; rw [hFl φ φ' h]
  have hint := integrable_osInt hm hlam (F := F) (G := F) ⟨hFm, C, hC⟩ ⟨hFm, C, hC⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hprod : ∀ (u v : DField n k → ℝ), Measurable u → Measurable v → (∀ φ, |u φ| ≤ C) →
      (∀ φ, |v φ| ≤ C) → Integrable fun φ => u (reflF φ) * v φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
    intro u v hu hv hCu hCv
    refine integrable_real_mul_dweight hm hlam (g := fun φ => u (reflF φ) * v φ)
      ((hu.comp measurable_reflF).mul hv) (C := C * C) fun φ => ?_
    rw [abs_mul]
    exact mul_le_mul (hCu _) (hCv _) (abs_nonneg _) hC0
  rw [Complex.nonneg_iff]
  constructor
  · rw [osInt, re_integral hint]
    have e : ∀ φ, (conj (F (reflF φ)) * F φ * (dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℂ)).re
        = a (reflF φ) * a φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ + b (reflF φ) * b φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
      intro φ
      simp only [ha, hb, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp_rw [e]
    rw [integral_add (hprod a a ham ham haC haC) (hprod b b hbm hbm hbC hbC)]
    exact add_nonneg (rp_dweight_bounded hnk hm hlam hal ham haC)
      (rp_dweight_bounded hnk hm hlam hbl hbm hbC)
  · rw [osInt, im_integral hint]
    have e : ∀ φ, (conj (F (reflF φ)) * F φ * (dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℂ)).im
        = a (reflF φ) * b φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ - b (reflF φ) * a φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
      intro φ
      simp only [ha, hb, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp_rw [e]
    rw [integral_sub (hprod a b ham hbm haC hbC) (hprod b a hbm ham hbC haC),
      integral_refl_symm hnk m₀ lam _ a b, sub_self]

/-! ### Goal 2: the OS form -/

/-- The partition function Z = ∫ dweight. -/
def partZ (n k : ℕ) (m₀ lam : ℝ) : ℝ :=
  ∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ

theorem partZ_pos {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) : 0 < partZ n k m₀ lam :=
  integral_exp_pos (μ := volume) (f := fun φ : DField n k => -(dirAction n k m₀ φ) / 2
    - lam * spacing n ^ 2 * ∑ x : DSite n k, wickPoly (Polynomial.X ^ 4) (freeVar n m₀) (φ x))
    (integrable_dweight hm hlam)

/-- **The OS form** ⟪F, G⟫ = ∫ conj(ΘF) · G · dweight / Z. -/
def osForm (m₀ lam : ℝ) (F G : DField n k → ℂ) : ℂ :=
  osInt m₀ lam F G / (partZ n k m₀ lam : ℂ)

/-- Hermitian symmetry of the unnormalised form (any F, G: no integrability needed). -/
theorem osInt_conj_symm (hnk : 0 < n + k) (m₀ lam : ℝ) (F G : DField n k → ℂ) :
    osInt m₀ lam G F = conj (osInt m₀ lam F G) := by
  unfold osInt
  rw [← integral_conj]
  have h := integral_reflF hnk
    (fun φ => F (reflF φ) * conj (G φ) * (dweight n k m₀ lam (Polynomial.X ^ 4) φ : ℂ))
  simp only [reflF_reflF, dweight_reflF hnk] at h
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun φ => by ring)

/-- **Conjugate symmetry**: ⟪G, F⟫ = conj ⟪F, G⟫. -/
theorem osForm_conj_symm (hnk : 0 < n + k) (m₀ lam : ℝ) (F G : DField n k → ℂ) :
    osForm m₀ lam G F = conj (osForm m₀ lam F G) := by
  rw [osForm, osForm, osInt_conj_symm hnk, map_div₀, Complex.conj_ofReal]

/-- Linearity in the second slot: additivity. -/
theorem osForm_add_right {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F G H : DField n k → ℂ} (hF : BddMeas F) (hG : BddMeas G) (hH : BddMeas H) :
    osForm m₀ lam F (G + H) = osForm m₀ lam F G + osForm m₀ lam F H := by
  rw [osForm, osForm, osForm, ← add_div, osInt, osInt, osInt,
    ← integral_add (integrable_osInt hm hlam hF hG) (integrable_osInt hm hlam hF hH)]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun φ => by simp only [Pi.add_apply]; ring)

/-- Linearity in the second slot: homogeneity (any F, G). -/
theorem osForm_smul_right (m₀ lam : ℝ) (F G : DField n k → ℂ) (c : ℂ) :
    osForm m₀ lam F (c • G) = c * osForm m₀ lam F G := by
  rw [osForm, osForm, mul_div_assoc', osInt, osInt, ← integral_const_mul]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun φ => by
    simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- Conjugate linearity in the first slot: additivity. -/
theorem osForm_add_left (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F G H : DField n k → ℂ} (hF : BddMeas F) (hG : BddMeas G) (hH : BddMeas H) :
    osForm m₀ lam (F + G) H = osForm m₀ lam F H + osForm m₀ lam G H := by
  rw [osForm_conj_symm hnk m₀ lam H, osForm_add_right hm hlam hH hF hG, map_add,
    ← osForm_conj_symm hnk, ← osForm_conj_symm hnk]

/-- Conjugate linearity in the first slot: ⟪c F, G⟫ = conj c ⟪F, G⟫ (any F, G). -/
theorem osForm_smul_left (hnk : 0 < n + k) (m₀ lam : ℝ) (F G : DField n k → ℂ) (c : ℂ) :
    osForm m₀ lam (c • F) G = conj c * osForm m₀ lam F G := by
  rw [osForm_conj_symm hnk m₀ lam G, osForm_smul_right, map_mul, ← osForm_conj_symm hnk]

/-- **Positivity**: ⟪F, F⟫ ≥ 0 (a nonnegative real) on the OS space. -/
theorem osForm_nonneg (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F : DField n k → ℂ} (hF : OSObs F) : 0 ≤ osForm m₀ lam F F := by
  have h := rp_complex hnk hm hlam hF
  have hZ := partZ_pos (n := n) (k := k) hm hlam
  rw [Complex.nonneg_iff] at h ⊢
  rw [osForm, Complex.div_ofReal_re, Complex.div_ofReal_im, ← h.2, zero_div]
  exact ⟨div_nonneg h.1 hZ.le, rfl⟩

theorem osForm_re_nonneg (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F : DField n k → ℂ} (hF : OSObs F) : 0 ≤ (osForm m₀ lam F F).re :=
  (Complex.nonneg_iff.mp (osForm_nonneg hnk hm hlam hF)).1

theorem osForm_im_self (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F : DField n k → ℂ} (hF : OSObs F) : (osForm m₀ lam F F).im = 0 :=
  ((Complex.nonneg_iff.mp (osForm_nonneg hnk hm hlam hF)).2).symm

/-- Elementary step of Cauchy–Schwarz: a nonnegative quadratic a − 2ts + t²sc forces s ≤ ac. -/
theorem cs_aux {a c s : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : ∀ t : ℝ, 0 ≤ a - 2 * t * s + t ^ 2 * s * c) : s ≤ a * c := by
  have hd := discrim_le_zero (K := ℝ) (a := s * c) (b := -2 * s) (c := a)
    (fun t => by have := h t; nlinarith)
  unfold discrim at hd
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

/-- **Cauchy–Schwarz** for the OS form: |⟪F, G⟫|² ≤ ⟪F, F⟫ ⟪G, G⟫. -/
theorem osForm_cauchy_schwarz (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ}
    (hlam : 0 ≤ lam) {F G : DField n k → ℂ} (hF : OSObs F) (hG : OSObs G) :
    ‖osForm m₀ lam F G‖ ^ 2 ≤ (osForm m₀ lam F F).re * (osForm m₀ lam G G).re := by
  set A := osForm m₀ lam F F with hA
  set B := osForm m₀ lam F G with hB
  set C := osForm m₀ lam G G with hC
  have hAim : A.im = 0 := osForm_im_self hnk hm hlam hF
  have hCim : C.im = 0 := osForm_im_self hnk hm hlam hG
  have hGF : osForm m₀ lam G F = conj B := osForm_conj_symm hnk m₀ lam F G
  refine cs_aux (osForm_re_nonneg hnk hm hlam hF) (osForm_re_nonneg hnk hm hlam hG)
    (sq_nonneg _) fun t => ?_
  set c : ℂ := -((t : ℂ) * conj B) with hc
  have hK : OSObs (F + c • G) := (osSpace n k).add_mem hF ((osSpace n k).smul_mem c hG)
  have hcG : BddMeas (c • G) := hG.2.smul c
  have hexp : osForm m₀ lam (F + c • G) (F + c • G)
      = A + c * B + conj c * (conj B + c * C) := by
    rw [osForm_add_left hnk hm hlam hF.2 hcG hK.2, osForm_add_right hm hlam hF.2 hF.2 hcG,
      osForm_add_right hm hlam hcG hF.2 hcG, osForm_smul_left hnk, osForm_smul_left hnk,
      osForm_smul_right, osForm_smul_right, hGF]
    ring
  have h0 := osForm_re_nonneg hnk hm hlam hK
  rw [hexp] at h0
  have hn : ‖B‖ ^ 2 = B.re * B.re + B.im * B.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hn]
  simp only [hc, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hCim, map_neg,
    map_mul, Complex.conj_ofReal, Complex.conj_conj, Complex.add_im] at h0
  nlinarith [h0]

/-- Null vectors are orthogonal to everything: ⟪F, F⟫ = 0 ⇒ ⟪F, G⟫ = 0 (so the null space is
the kernel of the form and the quotient carries a genuine inner product). -/
theorem osForm_null (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F G : DField n k → ℂ} (hF : OSObs F) (hG : OSObs G) (h0 : osForm m₀ lam F F = 0) :
    osForm m₀ lam F G = 0 := by
  have h := osForm_cauchy_schwarz hnk hm hlam hF hG
  rw [h0, Complex.zero_re, zero_mul] at h
  have : ‖osForm m₀ lam F G‖ = 0 := by nlinarith [norm_nonneg (osForm m₀ lam F G)]
  exact norm_eq_zero.mp this

/-! ## Exponential observables e^{iφ(f)} and the finite-volume OS kernel -/

open Filter Topology

/-- εN = L. -/
theorem spacing_mul_boxN : spacing n * (boxN n k : ℝ) = boxL k := by
  unfold spacing boxN boxL
  push_cast
  rw [pow_add, inv_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- The lattice image of the reflection on test functions: Θf shifted by one spacing,
f ↦ τ_(−ε, 0) Θf, i.e. x₀ ↦ −x₀ − ε (the bond plane sits at x₀ = −ε/2). -/
def latRefl (n : ℕ) (f : TestFn) : TestFn := translate (timeShift (-spacing n)) (reflect f)

theorem latRefl_dpos (f : TestFn) (x : DSite n k) :
    latRefl n f (dpos n k x) = f (dpos n k (reflX x)) := by
  change reflect f (dpos n k x - timeShift (-spacing n)) = _
  rw [reflect_apply]
  congr 1
  have hL := spacing_mul_boxN (n := n) (k := k)
  ext i
  fin_cases i
  · simp [dpos, timeShift, reflX]
    linear_combination -hL
  · simp [dpos, timeShift, reflX]

theorem dsmear_reflF (f : TestFn) (φ : DField n k) :
    dsmear n k f (reflF φ) = dsmear n k (latRefl n f) φ := by
  unfold dsmear
  congr 1
  refine Fintype.sum_equiv (Function.Involutive.toPerm reflX reflX_reflX) _ _ fun x => ?_
  change f (dpos n k x) * φ (reflX x) = latRefl n f (dpos n k (reflX x)) * φ (reflX x)
  rw [latRefl_dpos, reflX_reflX]

theorem dsmear_sub (f g : TestFn) (φ : DField n k) :
    dsmear n k (g - f) φ = dsmear n k g φ - dsmear n k f φ := by
  unfold dsmear
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by rw [sub_apply]; ring

theorem continuous_dsmear (f : TestFn) : Continuous (dsmear n k f) := by
  unfold dsmear; fun_prop

/-- The observable e^{iφ(f)} on the box (φ(f) = `dsmear`). -/
def expObs (n k : ℕ) (f : TestFn) (φ : DField n k) : ℂ :=
  Complex.exp (Complex.I * (dsmear n k f φ : ℂ))

theorem bddMeas_expObs (f : TestFn) : BddMeas (expObs n k f) := by
  refine ⟨(Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_dsmear f)))).measurable, 1, fun φ => ?_⟩
  rw [expObs, mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- For positive-time f, e^{iφ(f)} is right-local: the sites with f(dpos x) ≠ 0 have
εi − L/2 > 0, hence i ≥ N/2. -/
theorem rightLocal_expObs (hnk : 0 < n + k) {f : TestFn} (hf : PositiveTime f) :
    RightLocalC (expObs n k f) := by
  intro φ φ' h
  unfold expObs dsmear
  congr 4
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : halfN n k ≤ (x.1 : ℕ)
  · rw [h x hx]
  · have hz : f (dpos n k x) = 0 := by
      by_contra hne
      have hpos := hf _ hne
      have hxr : ((x.1 : ℕ) : ℝ) < (halfN n k : ℝ) := by exact_mod_cast (not_le.mp hx)
      have hN : (boxN n k : ℝ) = 2 * (halfN n k : ℝ) := by exact_mod_cast boxN_eq hnk
      have hL := spacing_mul_boxN (n := n) (k := k)
      have hε := spacing_pos n
      simp [dpos] at hpos
      nlinarith
    rw [hz, zero_mul, zero_mul]

theorem osObs_expObs (hnk : 0 < n + k) {f : TestFn} (hf : PositiveTime f) :
    OSObs (expObs n k f) :=
  ⟨rightLocal_expObs hnk hf, bddMeas_expObs f⟩

/-- **Finite-volume OS matrix elements**: ⟪e^{iφ(f)}, e^{iφ(g)}⟫ = Z_box(g − τ_(−ε)Θf), the
lattice analogue of the formula ⟪ψ f, ψ g⟫ = Z(g − Θf) of `OSGap` at t = 0. -/
theorem osForm_expObs (m₀ lam : ℝ) (f g : TestFn) :
    osForm m₀ lam (expObs n k f) (expObs n k g)
      = ZD n k m₀ lam (Polynomial.X ^ 4) (g - latRefl n f) := by
  rw [osForm, ZD, osInt, partZ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [expObs, dsmear_reflF, dsmear_sub]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem osForm_zero_right (m₀ lam : ℝ) (F : DField n k → ℂ) : osForm m₀ lam F 0 = 0 := by
  have h := osForm_smul_right m₀ lam F 0 0
  simpa using h

theorem bddMeas_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (G : ι → DField n k → ℂ)
    (hG : ∀ i, BddMeas (G i)) : BddMeas (∑ i ∈ s, c i • G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (BddMeas.zero (n := n) (k := k))
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact ((hG a).smul (c a)).add ih

theorem osForm_sum_right {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {ι : Type*}
    (s : Finset ι) {F : DField n k → ℂ} (hF : BddMeas F) (c : ι → ℂ) (G : ι → DField n k → ℂ)
    (hG : ∀ i, BddMeas (G i)) :
    osForm m₀ lam F (∑ i ∈ s, c i • G i) = ∑ i ∈ s, c i * osForm m₀ lam F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using osForm_zero_right m₀ lam F
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      osForm_add_right hm hlam hF ((hG a).smul _) (bddMeas_sum s c G hG), osForm_smul_right, ih]

theorem osForm_sum_left (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {ι : Type*} (s : Finset ι) {F : DField n k → ℂ} (hF : BddMeas F) (c : ι → ℂ)
    (G : ι → DField n k → ℂ) (hG : ∀ i, BddMeas (G i)) :
    osForm m₀ lam (∑ i ∈ s, c i • G i) F = ∑ i ∈ s, conj (c i) * osForm m₀ lam (G i) F := by
  rw [osForm_conj_symm hnk m₀ lam F, osForm_sum_right hm hlam s hF c G hG, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ← osForm_conj_symm hnk]

/-- **Finite-volume OS positivity of the generating functional**: for positive-time f_i and
complex c_i, Σ_{i,j} conj(c_i) c_j Z_box(f_j − τ_(−ε)Θf_i) ≥ 0. -/
theorem rp_ZD (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {ι : Type*} (s : Finset ι) (f : ι → TestFn) (hf : ∀ i, PositiveTime (f i)) (c : ι → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      conj (c i) * c j * ZD n k m₀ lam (Polynomial.X ^ 4) (f j - latRefl n (f i)) := by
  have hKo : OSObs (∑ i ∈ s, c i • expObs n k (f i)) := (osSpace n k).sum_mem fun i _ =>
    (osSpace n k).smul_mem (c i) (osObs_expObs hnk (hf i))
  have h := osForm_nonneg hnk hm hlam hKo
  have hE : ∀ i, BddMeas (expObs n k (f i)) := fun i => bddMeas_expObs (f i)
  have hr : ∀ i, osForm m₀ lam (expObs n k (f i)) (∑ j ∈ s, c j • expObs n k (f j))
      = ∑ j ∈ s, c j * osForm m₀ lam (expObs n k (f i)) (expObs n k (f j)) :=
    fun i => osForm_sum_right hm hlam s (hE i) c _ hE
  rw [osForm_sum_left hnk hm hlam s hKo.2 c _ hE] at h
  simp_rw [hr, osForm_expObs, Finset.mul_sum] at h
  convert h using 3
  ring

/-! ## Passing positivity to limit points -/

/-- OS positivity of a generating functional: the kernel (f, g) ↦ Z(g − Θf) is positive
semidefinite on positive-time test functions. -/
def OSPositive (Z : TestFn → ℂ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → TestFn) (c : Fin m → ℂ), (∀ i, PositiveTime (f i)) →
    0 ≤ ∑ i, ∑ j, conj (c i) * c j * Z (f j - reflect (f i))

/-- The one analytic input needed to pass RP to the limit: replacing the lattice reflection
τ_(−ε)Θ by Θ changes Z_box by o(1) as n, k → ∞. Implied by a uniform two-point bound
E_box[φ(h)²] ≤ C‖h‖² for a Schwartz norm (|Z(h) − Z(h')| ≤ E|φ(h − h')|), since
τ_(−ε)Θf → Θf in Schwartz space. NOT proved here. -/
def LatticeReflStable (m₀ lam : ℝ) : Prop :=
  ∀ f g : TestFn, Tendsto (fun p : ℕ × ℕ =>
    ZD p.1 p.2 m₀ lam (Polynomial.X ^ 4) (g - latRefl p.1 f)
      - ZD p.1 p.2 m₀ lam (Polynomial.X ^ 4) (g - reflect f)) atTop (𝓝 0)

/-- **RP of limit points**: under `LatticeReflStable`, every limit point of the Dirichlet-box
generating functionals is OS positive. -/
theorem osPositive_of_limitPoint {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hst : LatticeReflStable m₀ lam) {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) :
    OSPositive Z := by
  obtain ⟨ns, ks, hns, hks, hconv⟩ := hZ
  intro m f c hf
  have hp : Tendsto (fun j => (ns j, ks j)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact hns.prodMk hks
  -- convergence of each kernel entry
  have hent : ∀ i j : Fin m, Tendsto (fun l =>
      ZD (ns l) (ks l) m₀ lam (Polynomial.X ^ 4) (f j - latRefl (ns l) (f i)))
      atTop (𝓝 (Z (f j - reflect (f i)))) := by
    intro i j
    have h1 := (hst (f i) (f j)).comp hp
    have h2 := hconv (f j - reflect (f i))
    have := h1.add h2
    simp only [Function.comp_def, sub_add_cancel, zero_add] at this
    exact this
  have hsum : Tendsto (fun l => ∑ i, ∑ j, conj (c i) * c j *
      ZD (ns l) (ks l) m₀ lam (Polynomial.X ^ 4) (f j - latRefl (ns l) (f i)))
      atTop (𝓝 (∑ i, ∑ j, conj (c i) * c j * Z (f j - reflect (f i)))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (hent i j).const_mul _
  refine ge_of_tendsto hsum ?_
  have hk1 : ∀ᶠ l in atTop, 1 ≤ ks l := hks.eventually_ge_atTop 1
  filter_upwards [hk1] with l hl
  exact rp_ZD (by omega) hm hlam Finset.univ f hf c

end PP2RP2


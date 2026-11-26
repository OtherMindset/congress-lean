import LongTable.R_PP2LebowitzB
import LongTable.P_mwwlpzo0_wwossd
import LongTable.P_mwwlq01a_b80lsb

/-!
Part A of PP2Lebowitz2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Lebowitz2.lean)
Long Table, P(φ)₂ direction, node M9 (non-Gaussian limits), session 2: the multilinear expansion
of the smeared Ursell function, the φ ↦ −φ symmetry of the box measure, the Taylor step from a
quartic cumulant deficit to `QuarticDeficit`, and the reduction of M9 to one explicit,
cutoff-uniform analytic input `UniformQuarticNegativity`.

FORMALIZED.
* **Symmetry.** `lb2_dweight_neg`: dweight n k m₀ λ X⁴ (−φ) = dweight n k m₀ λ X⁴ φ (the
  Dirichlet action is quadratic, ext(−φ) = −ext φ, and :y⁴: is even). `lb2_dexpect_odd`: every
  odd observable (g(−φ) = −g(φ)) has ⟨g⟩ = 0 (no integrability needed: change of variables
  φ ↦ −φ). Hence `lb2_mom_odd`: ⟨φ(f)ʲ⟩ = 0 for odd j (in particular ⟨X⟩ = ⟨X³⟩ = 0), and
  **`lb2_ZD_eq_cos`**: Z_D(f) = ⟨cos φ(f)⟩ is real.
* Integrability: `lb2_integrable_pow` (∏ φ^e · φ(f)^m · dweight is integrable, every e, m),
  `lb2_integrable_dsmear_pow`.
* **Multilinear expansion.** With c_x = ε² f(x), `lb2_mom2_expand`, `lb2_mom4_expand`, and
  **`lb2_u4_expand`**: the smeared Ursell function u₄(f) := ⟨X⁴⟩ − 3⟨X²⟩² (X = φ(f), `lb2_u4`)
  equals Σ_{a,b,c,d} c_a c_b c_c c_d · u₄(a,b,c,d), where u₄(a,b,c,d) (`lb2_U`) is exactly the
  site Ursell function of `lebowitz_dexpect`. **`lb2_u4_nonpos`**: u₄(f) ≤ 0 for f ≥ 0 on the
  lattice (λ ≥ 0, m₀ ≠ 0). Scaling: `lb2_mom_smul` (⟨φ(tf)ʲ⟩ = tʲ⟨φ(f)ʲ⟩), `lb2_u4_smul`
  (u₄(tf) = t⁴ u₄(f)).
* **Taylor step (abstract, any probability space).** `lb2_cos_taylor`:
  |cos y − (1 − y²/2 + y⁴/24)| ≤ 3 y⁶ for all real y (|y| ≤ 1 from `Complex.exp_bound`, n = 6;
  |y| > 1 crude). `lb2_integral_cos_taylor`: |E cos(sX) − (1 − s²m₂/2 + s⁴m₄/24)| ≤ 3 s⁶ m₆.
  `lb2_alg` (pure algebra, 0 ≤ s ≤ 1, moments ≤ K, m₄ ≤ 2K): with a, b the two Taylor
  expansions, b − a⁴ ≤ s²(m₄ − 3m₂²)/2 + 1000(1+K)³ s³. **`lb2_taylor_deficit`**: if
  m₂, m₆ ≤ K, m₄ − 3m₂² ≤ −δ and 4(K+1)t² ≤ 1, 4000(1+K)³t² ≤ δ, then
  0 ≤ E cos(2tX) and E cos(2tX) + δt⁴/4 ≤ (E cos tX)⁴. (m₄ ≤ m₂ + m₆ pointwise; E cos 2tX ≥
  1 − 2t²m₂ ≥ 1/2.) No symmetry of X is used: only E cos enters, and symmetry enters through
  `lb2_ZD_eq_cos` (‖Z_D‖ = |E cos|).
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

/-! ## Part 1: the cosine Taylor bound and the algebra of the quartic deficit -/

/-- The global sixth-order remainder bound for cos: |cos y − (1 − y²/2 + y⁴/24)| ≤ 3 y⁶. -/
theorem lb2_cos_taylor (y : ℝ) : |Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24)| ≤ 3 * y ^ 6 := by
  rcases le_or_gt |y| 1 with hy | hy
  · have hnz : ‖(y : ℂ) * Complex.I‖ = |y| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hb := Complex.exp_bound (x := (y : ℂ) * Complex.I) (by rw [hnz]; exact hy) (n := 6)
      (by norm_num)
    have hsum : ∑ m ∈ Finset.range 6, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
        = ((1 - y ^ 2 / 2 + y ^ 4 / 24 : ℝ) : ℂ)
          + ((y - y ^ 3 / 6 + y ^ 5 / 120 : ℝ) : ℂ) * Complex.I := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast
      linear_combination ((y : ℂ) ^ 2 / 2 + (y : ℂ) ^ 3 * Complex.I / 6
        + (y : ℂ) ^ 4 * (Complex.I ^ 2 - 1) / 24
        + (y : ℂ) ^ 5 * Complex.I * (Complex.I ^ 2 - 1) / 120) * Complex.I_sq
    have hre : Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24)
        = (Complex.exp ((y : ℂ) * Complex.I)
          - ∑ m ∈ Finset.range 6, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re := by
      rw [hsum, Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
    rw [hre]
    refine (Complex.abs_re_le_norm _).trans (hb.trans ?_)
    rw [hnz, (show Even 6 by decide).pow_abs]
    have : (0 : ℝ) ≤ y ^ 6 := by positivity
    norm_num
    nlinarith
  · have hu : 1 ≤ y ^ 2 := by
      have := abs_nonneg y
      have h1 : 1 ≤ |y| ^ 2 := by nlinarith
      rwa [sq_abs] at h1
    have h4 : y ^ 4 = (y ^ 2) ^ 2 := by ring
    have h6 : y ^ 6 = (y ^ 2) ^ 3 := by ring
    have hc1 := Real.neg_one_le_cos y
    have hc2 := Real.cos_le_one y
    rw [h4, h6]
    generalize y ^ 2 = u at *
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu)]

/-- **The algebra of the quartic deficit.** With a = 1 − s m₂/2 + s² m₄/24 + r₁ and
b = 1 − 2 s m₂ + 2 s² m₄/3 + r₂ (the Taylor expansions of E cos(tX), E cos(2tX), s = t²),
b − a⁴ ≤ s² (m₄ − 3 m₂²)/2 + 1000 (1 + K)³ s³. -/
theorem lb2_alg {s K m2 m4 m6 r1 r2 : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K)
    (h20 : 0 ≤ m2) (h2K : m2 ≤ K) (h40 : 0 ≤ m4) (h4K : m4 ≤ 2 * K)
    (h6K : m6 ≤ K) (hr1 : |r1| ≤ 3 * s ^ 3 * m6) (hr2 : |r2| ≤ 192 * s ^ 3 * m6) :
    (1 - 2 * s * m2 + 2 * s ^ 2 * m4 / 3 + r2) - (1 - s * m2 / 2 + s ^ 2 * m4 / 24 + r1) ^ 4
      ≤ s ^ 2 * (m4 - 3 * m2 ^ 2) / 2 + 1000 * (1 + K) ^ 3 * s ^ 3 := by
  obtain ⟨β, hβ⟩ : ∃ β, β = s ^ 2 * m4 / 24 + r1 := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α, α = -(s * m2 / 2) + β := ⟨_, rfl⟩
  have ha : 1 - s * m2 / 2 + s ^ 2 * m4 / 24 + r1 = 1 + α := by rw [hα, hβ]; ring
  rw [ha]
  have hid : (1 - 2 * s * m2 + 2 * s ^ 2 * m4 / 3 + r2) - (1 + α) ^ 4
      - s ^ 2 * (m4 - 3 * m2 ^ 2) / 2
      = r2 - 4 * r1 + 6 * s * m2 * β - 6 * β ^ 2 - 4 * α ^ 3 - α ^ 4 := by
    rw [hα, hβ]; ring
  have hs2 : s ^ 2 ≤ s := by nlinarith
  have hs3 : s ^ 3 ≤ s ^ 2 := by nlinarith
  have hs2n : 0 ≤ s ^ 2 := by positivity
  have hs3n : 0 ≤ s ^ 3 := by positivity
  have hm6s : s ^ 3 * m6 ≤ s ^ 3 * K := mul_le_mul_of_nonneg_left h6K hs3n
  have hs3K : s ^ 3 * K ≤ s ^ 2 * K := mul_le_mul_of_nonneg_right hs3 hK
  have hr1' : |r1| ≤ 3 * (s ^ 2 * K) := by linarith
  have hβb : |β| ≤ 4 * K * s ^ 2 := by
    have h1 : |s ^ 2 * m4 / 24| ≤ s ^ 2 * (2 * K) / 24 := by
      rw [abs_of_nonneg (by positivity)]
      have := mul_le_mul_of_nonneg_left h4K hs2n
      linarith
    have h2 := abs_add_le (s ^ 2 * m4 / 24) r1
    rw [← hβ] at h2
    have := mul_nonneg hs2n hK
    linarith
  have hαb : |α| ≤ 5 * K * s := by
    have h1 : |-(s * m2 / 2)| ≤ s * K / 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have := mul_le_mul_of_nonneg_left h2K hs0
      linarith
    have h2 := abs_add_le (-(s * m2 / 2)) β
    rw [← hα] at h2
    have h3 : K * s ^ 2 ≤ K * s := mul_le_mul_of_nonneg_left hs2 hK
    have := mul_nonneg hK hs0
    linarith
  have hα3 : -(4 * α ^ 3) ≤ 4 * (125 * K ^ 3 * s ^ 3) := by
    have h1 : -(α ^ 3) ≤ |α| ^ 3 := by rw [← abs_pow]; exact neg_le_abs _
    have h2 : |α| ^ 3 ≤ (5 * K * s) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hαb 3
    have h3 : (5 * K * s) ^ 3 = 125 * K ^ 3 * s ^ 3 := by ring
    linarith
  have hα4 : 0 ≤ α ^ 4 := by positivity
  have hβ2 : 0 ≤ β ^ 2 := by positivity
  have hmβ : 6 * s * m2 * β ≤ 24 * K ^ 2 * s ^ 3 := by
    have h1 : β ≤ |β| := le_abs_self β
    have h2 : 0 ≤ 6 * s * m2 := by positivity
    have h3 : 6 * s * m2 ≤ 6 * s * K := by nlinarith
    calc 6 * s * m2 * β ≤ 6 * s * m2 * |β| := mul_le_mul_of_nonneg_left h1 h2
      _ ≤ 6 * s * K * (4 * K * s ^ 2) :=
        mul_le_mul h3 hβb (abs_nonneg _) (by positivity)
      _ = 24 * K ^ 2 * s ^ 3 := by ring
  have hpoly : 204 * K + 24 * K ^ 2 + 500 * K ^ 3 ≤ 1000 * (1 + K) ^ 3 := by
    nlinarith [pow_nonneg hK 2, pow_nonneg hK 3]
  have hpoly' := mul_le_mul_of_nonneg_right hpoly hs3n
  have e1 := le_abs_self r2
  have e2 := neg_abs_le r1
  have hr1s : |r1| ≤ 3 * (s ^ 3 * K) := by linarith
  have hr2s : |r2| ≤ 192 * (s ^ 3 * K) := by linarith
  have hfin : r2 - 4 * r1 + 6 * s * m2 * β - 6 * β ^ 2 - 4 * α ^ 3 - α ^ 4
      ≤ (204 * K + 24 * K ^ 2 + 500 * K ^ 3) * s ^ 3 := by
    have : (204 * K + 24 * K ^ 2 + 500 * K ^ 3) * s ^ 3
        = 192 * (s ^ 3 * K) + 4 * (3 * (s ^ 3 * K)) + 24 * K ^ 2 * s ^ 3
          + 4 * (125 * K ^ 3 * s ^ 3) := by ring
    rw [this]
    linarith
  linarith

/-! ## Part 2: the Taylor step on an abstract probability space -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}

lemma lb2_integrable_cos (hX : AEStronglyMeasurable X μ) (s : ℝ) :
    Integrable (fun ω => Real.cos (s * X ω)) μ :=
  Integrable.of_bound (Real.continuous_cos.comp_aestronglyMeasurable (hX.const_mul s)) 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- **Taylor expansion of E cos(sX)** with the sixth-moment remainder:
|E cos(sX) − (1 − s² m₂/2 + s⁴ m₄/24)| ≤ 3 s⁶ m₆. -/
theorem lb2_integral_cos_taylor (hX : AEStronglyMeasurable X μ)
    (h2 : Integrable (fun ω => X ω ^ 2) μ) (h4 : Integrable (fun ω => X ω ^ 4) μ)
    (h6 : Integrable (fun ω => X ω ^ 6) μ) (s : ℝ) :
    |∫ ω, Real.cos (s * X ω) ∂μ
        - (1 - s ^ 2 / 2 * ∫ ω, X ω ^ 2 ∂μ + s ^ 4 / 24 * ∫ ω, X ω ^ 4 ∂μ)|
      ≤ 3 * s ^ 6 * ∫ ω, X ω ^ 6 ∂μ := by
  have hc := lb2_integrable_cos hX s
  have hP : Integrable (fun ω => 1 - s ^ 2 / 2 * X ω ^ 2 + s ^ 4 / 24 * X ω ^ 4) μ :=
    ((integrable_const 1).sub (h2.const_mul _)).add (h4.const_mul _)
  have hA : Integrable (fun ω => 1 - s ^ 2 / 2 * X ω ^ 2) μ :=
    (integrable_const 1).sub (h2.const_mul _)
  have eP : ∫ ω, (1 - s ^ 2 / 2 * X ω ^ 2 + s ^ 4 / 24 * X ω ^ 4) ∂μ
      = 1 - s ^ 2 / 2 * ∫ ω, X ω ^ 2 ∂μ + s ^ 4 / 24 * ∫ ω, X ω ^ 4 ∂μ := by
    rw [integral_add hA (h4.const_mul _),
      integral_sub (integrable_const 1) (h2.const_mul _), integral_const, integral_const_mul,
      integral_const_mul]
    simp
  rw [← eP, ← integral_sub hc hP, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (h6.const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
  have h := lb2_cos_taylor (s * X ω)
  rw [Real.norm_eq_abs]
  calc |Real.cos (s * X ω) - (1 - s ^ 2 / 2 * X ω ^ 2 + s ^ 4 / 24 * X ω ^ 4)|
      = |Real.cos (s * X ω) - (1 - (s * X ω) ^ 2 / 2 + (s * X ω) ^ 4 / 24)| := by ring_nf
    _ ≤ 3 * (s * X ω) ^ 6 := h
    _ = 3 * s ^ 6 * X ω ^ 6 := by ring

/-- **The Taylor step.** If E X² ≤ K, E X⁶ ≤ K and E X⁴ − 3 (E X²)² ≤ −δ, then for every t with
4(K+1)t² ≤ 1 and 4000(1+K)³t² ≤ δ: E cos(2tX) ≥ 0 and E cos(2tX) + δt⁴/4 ≤ (E cos tX)⁴.
The admissible t depend only on K and δ. -/
theorem lb2_taylor_deficit (hX : AEStronglyMeasurable X μ)
    (h2 : Integrable (fun ω => X ω ^ 2) μ) (h4 : Integrable (fun ω => X ω ^ 4) μ)
    (h6 : Integrable (fun ω => X ω ^ 6) μ) {K δ t : ℝ} (hK : 0 ≤ K)
    (hm2 : ∫ ω, X ω ^ 2 ∂μ ≤ K) (hm6 : ∫ ω, X ω ^ 6 ∂μ ≤ K)
    (hu : ∫ ω, X ω ^ 4 ∂μ - 3 * (∫ ω, X ω ^ 2 ∂μ) ^ 2 ≤ -δ)
    (htK : 4 * (K + 1) * t ^ 2 ≤ 1) (htδ : 4000 * (1 + K) ^ 3 * t ^ 2 ≤ δ) :
    0 ≤ ∫ ω, Real.cos (2 * t * X ω) ∂μ ∧
      ∫ ω, Real.cos (2 * t * X ω) ∂μ + δ * t ^ 4 / 4 ≤ (∫ ω, Real.cos (t * X ω) ∂μ) ^ 4 := by
  have T1 := lb2_integral_cos_taylor hX h2 h4 h6 t
  have T2 := lb2_integral_cos_taylor hX h2 h4 h6 (2 * t)
  set m2 := ∫ ω, X ω ^ 2 ∂μ with hm2d
  set m4 := ∫ ω, X ω ^ 4 ∂μ with hm4d
  set m6 := ∫ ω, X ω ^ 6 ∂μ with hm6d
  have h20 : 0 ≤ m2 := integral_nonneg fun ω => by positivity
  have h40 : 0 ≤ m4 := integral_nonneg fun ω => by positivity
  have h4le : m4 ≤ m2 + m6 := by
    rw [hm4d, hm2d, hm6d, ← integral_add h2 h6]
    refine integral_mono h4 (h2.add h6) fun ω => ?_
    have := mul_nonneg (sq_nonneg (X ω)) (sq_nonneg (X ω ^ 2 - 1))
    have : 0 ≤ X ω ^ 4 := by positivity
    nlinarith
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have ht1 : t ^ 2 ≤ 1 := by nlinarith
  set a := ∫ ω, Real.cos (t * X ω) ∂μ with ha
  set b := ∫ ω, Real.cos (2 * t * X ω) ∂μ with hb
  have halg := lb2_alg (s := t ^ 2) (K := K) (m2 := m2) (m4 := m4) (m6 := m6)
    (r1 := a - (1 - t ^ 2 / 2 * m2 + t ^ 4 / 24 * m4))
    (r2 := b - (1 - (2 * t) ^ 2 / 2 * m2 + (2 * t) ^ 4 / 24 * m4)) ht2 ht1 hK h20 hm2 h40
    (by linarith) hm6 (T1.trans_eq (by ring)) (T2.trans_eq (by ring))
  have key : b - a ^ 4 ≤ (t ^ 2) ^ 2 * (m4 - 3 * m2 ^ 2) / 2 + 1000 * (1 + K) ^ 3 * (t ^ 2) ^ 3 :=
    calc b - a ^ 4 = (1 - 2 * t ^ 2 * m2 + 2 * (t ^ 2) ^ 2 * m4 / 3
          + (b - (1 - (2 * t) ^ 2 / 2 * m2 + (2 * t) ^ 4 / 24 * m4)))
          - (1 - t ^ 2 * m2 / 2 + (t ^ 2) ^ 2 * m4 / 24
          + (a - (1 - t ^ 2 / 2 * m2 + t ^ 4 / 24 * m4))) ^ 4 := by ring
      _ ≤ _ := halg
  have ht4 : 0 ≤ t ^ 4 := by positivity
  have k1 : (t ^ 2) ^ 2 * (m4 - 3 * m2 ^ 2) / 2 ≤ -δ * t ^ 4 / 2 := by
    have := mul_le_mul_of_nonneg_left hu ht4
    nlinarith
  have k2 : 1000 * (1 + K) ^ 3 * (t ^ 2) ^ 3 ≤ δ * t ^ 4 / 4 := by
    have := mul_le_mul_of_nonneg_left htδ ht4
    nlinarith
  refine ⟨?_, by linarith⟩
  -- E cos(2tX) ≥ 1 − 2t² m₂ ≥ 1/2
  have hlow : 1 - (2 * t) ^ 2 / 2 * m2 ≤ b := by
    have hi : Integrable (fun ω => 1 - (2 * t) ^ 2 / 2 * X ω ^ 2) μ :=
      (integrable_const 1).sub (h2.const_mul _)
    have e : ∫ ω, (1 - (2 * t) ^ 2 / 2 * X ω ^ 2) ∂μ = 1 - (2 * t) ^ 2 / 2 * m2 := by
      rw [integral_sub (integrable_const 1) (h2.const_mul _), integral_const, integral_const_mul,
        hm2d]
      simp
    rw [← e, hb]
    refine integral_mono hi (lb2_integrable_cos hX _) fun ω => ?_
    have := Real.one_sub_sq_div_two_le_cos (x := 2 * t * X ω)
    calc 1 - (2 * t) ^ 2 / 2 * X ω ^ 2 = 1 - (2 * t * X ω) ^ 2 / 2 := by ring
      _ ≤ _ := this
  have : t ^ 2 * m2 ≤ t ^ 2 * K := mul_le_mul_of_nonneg_left hm2 ht2
  nlinarith

end Abstract

/-! ## Part 3: the φ ↦ −φ symmetry of the box measure -/

section Model

variable {n k : ℕ}

lemma lb2_ext_neg (φ : DField n k) (p : ℤ × ℤ) :
    PP2Target.ext (fun x => -φ x) p = -PP2Target.ext φ p := by
  unfold PP2Target.ext; split_ifs <;> simp

lemma lb2_dirAction_neg (m₀ : ℝ) (φ : DField n k) :
    dirAction n k m₀ (fun x => -φ x) = dirAction n k m₀ φ := by
  unfold dirAction
  simp only [lb2_ext_neg]
  congr 2
  · exact Finset.sum_congr rfl fun p _ => by ring
  · exact Finset.sum_congr rfl fun x _ => by ring

/-- **The quartic box weight is even**: dweight(−φ) = dweight(φ). -/
theorem lb2_dweight_neg (m₀ lam : ℝ) (φ : DField n k) :
    dweight n k m₀ lam (Polynomial.X ^ 4) (fun x => -φ x)
      = dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  unfold dweight
  simp only [lb2_dirAction_neg, wickPoly_X4_neg]

lemma lb2_dsmear_neg (f : TestFn) (φ : DField n k) :
    dsmear n k f (fun x => -φ x) = -dsmear n k f φ := by
  unfold dsmear; simp [Finset.sum_neg_distrib]

/-- **Odd observables have zero expectation** (change of variables φ ↦ −φ; no integrability
hypothesis). -/
theorem lb2_dexpect_odd (m₀ lam : ℝ) {g : DField n k → ℝ}
    (hg : ∀ φ, g (fun x => -φ x) = -g φ) : dexpect n k m₀ lam g = 0 := by
  have h := (measurePreserving_flipEquiv (fun _ : DSite n k => true)).integral_comp'
    (f := flipEquiv (fun _ : DSite n k => true))
    (fun φ => g φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ)
  have hf : ∀ φ : DField n k, (flipEquiv (fun _ : DSite n k => true) φ) = fun x => -φ x :=
    fun φ => by funext x; show sgnMul true (φ x) = -φ x; simp [sgnMul]
  simp only [hf, hg, lb2_dweight_neg, neg_mul, integral_neg] at h
  have h0 : ∫ φ, g φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ = 0 := by linarith
  rw [dexpect, h0, zero_div]

/-- The smeared moments ⟨φ(f)ʲ⟩. -/
def lb2_mom (n k : ℕ) (m₀ lam : ℝ) (f : TestFn) (j : ℕ) : ℝ :=
  dexpect n k m₀ lam (fun φ => dsmear n k f φ ^ j)

/-- Odd smeared moments vanish: ⟨φ(f)ʲ⟩ = 0 for j odd (in particular ⟨X⟩ = ⟨X³⟩ = 0). -/
theorem lb2_mom_odd (m₀ lam : ℝ) (f : TestFn) {j : ℕ} (hj : Odd j) :
    lb2_mom n k m₀ lam f j = 0 :=
  lb2_dexpect_odd m₀ lam fun φ => by rw [lb2_dsmear_neg, hj.neg_pow]

/-- **Z_D is real**: Z_D(f) = ⟨cos φ(f)⟩ (the sine part vanishes by symmetry). -/
theorem lb2_ZD_eq_cos {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (f : TestFn) :
    ZD n k m₀ lam (Polynomial.X ^ 4) f
      = ((∫ φ, Real.cos (dsmear n k f φ) ∂(gibbs n k m₀ lam) : ℝ) : ℂ) := by
  rw [ZD_eq_gibbs hm hlam, integral_gibbs m₀ lam (fun φ => Real.sin (dsmear n k f φ)),
    lb2_dexpect_odd m₀ lam (fun φ => by rw [lb2_dsmear_neg, Real.sin_neg])]
  simp

end Model

end PP2Lebowitz2

end

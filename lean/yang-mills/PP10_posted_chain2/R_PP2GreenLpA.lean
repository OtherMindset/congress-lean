import LongTable.P_mwxo412m_27xfkn

/-!
Part A of PP2GreenLp (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2GreenLp.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5 / F3, session 1.
Lᵖ bounds on the BOX Green function `dirGreen` and on the rough part of the Nelson heat-kernel split
(namespace `PP2Target`). The region version (C_B = ε⁻² regOp⁻¹) is NOT done here.

Notation: ε = `spacing n`, p_t = `heatK n k m₀ t` (PP2Heat), C(x, y) = ε⁻² dirGreen x y (the lattice
covariance, `gauss_cov`), C_r(T)(x, y) = `glp_roughCov n k m₀ T x y` = ε⁻² ∫_{(0,T]} p_t(x, y) dt.
"Lᵖ norm" means the lattice integral ε² Σ_y |·|^p. All constants are uniform in n, k, x.

Method: Minkowski in t, C = ∫₀^∞ ε⁻² p_t dt (`integral_heatK`), with
‖ε⁻² p_t(x,·)‖_∞ ≤ e^{−t m₀²} π/(4t) (diagonal bound with the mass kept + |p_t(x,y)| ≤ (p_t(x,x) + p_t(y,y))/2
from the semigroup) and ‖ε⁻² p_t(x,·)‖₂² = ε⁻² p_{2t}(x,x) ≤ e^{−2t m₀²} π/(8t); interpolating,
ε² Σ_y |ε⁻² p_t(x,y)|^p ≤ (π/4)^{p−1}/2 · t^{1−p} e^{−p t m₀²}, whose p-th root is integrated exactly
(Gamma integral; no t ≤ 1 / t ≥ 1 split needed). Minkowski for finite sums is proved by duality + Hölder.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `glp_minkowski_rpow`, `glp_minkowski`: Minkowski's integral inequality on a finite index set, real
  p > 1 and (weighted, natural p ≥ 2) forms.
* `glp_dirGreen_rowSum_le` (**goal 1**): m₀ ≠ 0 → Σ_y dirGreen x y ≤ 1/m₀² (maximum principle);
  `glp_cov_rowSum_le`: ε² Σ_y ε⁻² dirGreen x y ≤ (m₀²)⁻¹.
* `glp_heatK_diag_le`: ε⁻² p_t(x,x) ≤ e^{−t m₀²} π/(4t) (t > 0); `glp_heatK_abs_le`:
  |p_t(x,y)| ≤ (p_t(x,x) + p_t(y,y))/2; `glp_heatK_sup_le`, `glp_heatK_L2_le`, `glp_heatK_Lp_le`.
* `glp_dirGreen_Lp_le` (**goal 2**): m₀ ≠ 0, p ∈ ℕ, p ≥ 2 →
  ε² Σ_y (ε⁻² dirGreen x y)^p ≤ (π/4)^{p−1}/2 · Γ(1/p)^p / m₀².
  `glp_dirGreen_L2_le`: p = 2, bound π²/(8 m₀²); `glp_dirGreen_L4_le`: p = 4, bound
  (π/4)³ Γ(1/4)⁴/(2 m₀²) ≈ 41.9/m₀².
* `glp_roughCov_Lp_le` (**goal 3**): any m₀, T ≥ 0, p ∈ ℕ, p ≥ 2 →
  ε² Σ_y |C_r(T)(x,y)|^p ≤ (π/4)^{p−1}/2 · p^p · T (exponent a = 1).
* `glp_roughCov_spectral`: C_r(T)(x,y) = ε⁻² Σ_K e_K(x) e_K(y) (1 − e^{−T λ_K})/λ_K (the plan's form).

NOT formalized here: the region (physBall) versions of all of the above; positivity p_t(x,y) ≥ 0
off the diagonal (not needed: absolute values are used for C_r); the smooth part C − C_r and its
pointwise bounds; a numerical bound on Γ(1/p).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset MeasureTheory Set

noncomputable section

namespace PP2Target

/-! ## Minkowski's integral inequality for finite sums (duality proof) -/

/-- Minkowski in the time variable, unweighted, real exponent p > 1:
(Σ_i |∫_s f_t(i) dt|^p)^{1/p} ≤ ∫_s φ, given (Σ_i |f_t(i)|^p)^{1/p} ≤ φ(t) on s. -/
theorem glp_minkowski_rpow {ι : Type*} [Fintype ι] {s : Set ℝ} (hs : MeasurableSet s)
    (f : ℝ → ι → ℝ) (φ : ℝ → ℝ) {p : ℝ} (hp : 1 < p)
    (hf : ∀ i, IntegrableOn (fun t => f t i) s) (hφ : IntegrableOn φ s)
    (hb : ∀ t ∈ s, (∑ i, |f t i| ^ p) ^ (1 / p) ≤ φ t) :
    (∑ i, |∫ t in s, f t i| ^ p) ^ (1 / p) ≤ ∫ t in s, φ t := by
  set F : ι → ℝ := fun i => ∫ t in s, f t i with hF
  set q : ℝ := p / (p - 1) with hq
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hp0 : 0 < p := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  set b : ι → ℝ := fun i => F i * |F i| ^ (p - 2) with hbdef
  have hFb : ∀ i, F i * b i = |F i| ^ p := by
    intro i
    by_cases h : F i = 0
    · simp [hbdef, h, zero_rpow hp0.ne']
    · have ha : 0 < |F i| := abs_pos.mpr h
      rw [hbdef]
      simp only
      rw [← mul_assoc, ← sq, ← sq_abs, ← rpow_natCast, ← rpow_add ha]
      norm_num
  have hbq : ∀ i, |b i| ^ q = |F i| ^ p := by
    intro i
    have hab : |b i| = |F i| ^ (p - 1) := by
      by_cases h : F i = 0
      · simp [hbdef, h, zero_rpow hp1]
      · have ha : 0 < |F i| := abs_pos.mpr h
        rw [hbdef]
        simp only
        rw [abs_mul, abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
        conv_lhs => arg 1; rw [← rpow_one |F i|]
        rw [← rpow_add ha]
        ring_nf
    rw [hab, ← rpow_mul (abs_nonneg _)]
    congr 1
    rw [hq]; field_simp
  set S : ℝ := ∑ i, |F i| ^ p with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => rpow_nonneg (abs_nonneg _) _
  have key : S = ∫ t in s, ∑ i, f t i * b i := by
    rw [integral_finsetSum _ (fun i _ => (hf i).mul_const _)]
    simp_rw [integral_mul_const]
    rw [hS]
    exact Finset.sum_congr rfl fun i _ => (hFb i).symm
  have hI0 : 0 ≤ ∫ t in s, φ t :=
    setIntegral_nonneg hs fun t ht =>
      le_trans (rpow_nonneg (Finset.sum_nonneg fun i _ => rpow_nonneg (abs_nonneg _) _) _) (hb t ht)
  have hmono : ∫ t in s, ∑ i, f t i * b i ≤ ∫ t in s, φ t * S ^ (1 / q) := by
    refine setIntegral_mono_on ?_ (hφ.mul_const _) hs fun t ht => ?_
    · exact integrable_finsetSum _ fun i _ => (hf i).mul_const _
    · calc ∑ i, f t i * b i ≤ (∑ i, |f t i| ^ p) ^ (1 / p) * (∑ i, |b i| ^ q) ^ (1 / q) :=
            Real.inner_le_Lp_mul_Lq _ _ _ hpq
        _ = (∑ i, |f t i| ^ p) ^ (1 / p) * S ^ (1 / q) := by simp_rw [hbq]; rfl
        _ ≤ φ t * S ^ (1 / q) := mul_le_mul_of_nonneg_right (hb t ht) (rpow_nonneg hS0 _)
  rw [integral_mul_const, ← key] at hmono
  rcases hS0.lt_or_eq with hSp | hSz
  · have hsum : 1 / p + 1 / q = 1 := by
      have := (Real.holderConjugate_iff.mp hpq).2
      simpa [one_div] using this
    have hSq : 0 < S ^ (1 / q) := rpow_pos_of_pos hSp _
    have e : S ^ (1 / p) * S ^ (1 / q) = S := by
      rw [← rpow_add hSp, hsum, rpow_one]
    exact le_of_mul_le_mul_right (by rw [e]; exact hmono) hSq
  · rw [← hSz, zero_rpow (by positivity)]
    exact hI0

/-- Minkowski in the time variable, weighted, natural exponent p ≥ 2 (stated with powers):
c Σ_i |∫_s f_t(i) dt|^p ≤ (∫_s φ)^p, given c Σ_i |f_t(i)|^p ≤ φ(t)^p and φ ≥ 0 on s. -/
theorem glp_minkowski {ι : Type*} [Fintype ι] {s : Set ℝ} (hs : MeasurableSet s)
    (f : ℝ → ι → ℝ) (φ : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (p : ℕ) (hp : 2 ≤ p)
    (hf : ∀ i, IntegrableOn (fun t => f t i) s) (hφ : IntegrableOn φ s)
    (hφ0 : ∀ t ∈ s, 0 ≤ φ t) (hb : ∀ t ∈ s, c * ∑ i, |f t i| ^ p ≤ φ t ^ p) :
    c * ∑ i, |∫ t in s, f t i| ^ p ≤ (∫ t in s, φ t) ^ p := by
  set P : ℝ := (p : ℝ) with hP
  have hP1 : 1 < P := by rw [hP]; exact_mod_cast (by omega : 1 < p)
  have hpn : p ≠ 0 := by omega
  have habs : ∀ a : ℝ, |c ^ P⁻¹ * a| ^ P = c * |a| ^ p := by
    intro a
    rw [abs_mul, abs_of_nonneg (rpow_nonneg hc _), mul_rpow (rpow_nonneg hc _) (abs_nonneg _),
      ← rpow_mul hc, inv_mul_cancel₀ (by linarith), rpow_one, hP, rpow_natCast]
  have hsumabs : ∀ g : ι → ℝ, ∑ i, |c ^ P⁻¹ * g i| ^ P = c * ∑ i, |g i| ^ p := by
    intro g; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => habs _
  have h := glp_minkowski_rpow hs (fun t i => c ^ P⁻¹ * f t i) φ hP1
    (fun i => (hf i).const_mul _) hφ (fun t ht => by
      rw [hsumabs (f t), one_div]
      calc (c * ∑ i, |f t i| ^ p) ^ P⁻¹ ≤ (φ t ^ p) ^ P⁻¹ :=
            rpow_le_rpow (mul_nonneg hc (Finset.sum_nonneg fun i _ => by positivity)) (hb t ht)
              (by positivity)
        _ = φ t := by rw [hP]; exact pow_rpow_inv_natCast (hφ0 t ht) hpn)
  simp only [integral_const_mul] at h
  rw [hsumabs (fun i => ∫ t in s, f t i), one_div] at h
  have hX : 0 ≤ c * ∑ i, |∫ t in s, f t i| ^ p :=
    mul_nonneg hc (Finset.sum_nonneg fun i _ => by positivity)
  calc c * ∑ i, |∫ t in s, f t i| ^ p
      = ((c * ∑ i, |∫ t in s, f t i| ^ p) ^ P⁻¹) ^ p := by
        rw [hP]; exact (rpow_inv_natCast_pow hX hpn).symm
    _ ≤ (∫ t in s, φ t) ^ p := pow_le_pow_left₀ (by positivity) h p

variable {n k : ℕ}

/-! ## Row sum: maximum principle -/

theorem glp_ext_le (v : DField n k) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ y, v y ≤ M) (q : ℤ × ℤ) :
    ext v q ≤ M := by
  unfold ext; split_ifs
  · exact hv _
  · exact hM

/-- **Row sum (goal 1):** Σ_y dirGreen x y ≤ 1/m₀² (maximum principle for dirOp · u = 1). -/
theorem glp_dirGreen_rowSum_le {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) :
    ∑ y, dirGreen n k m₀ x y ≤ 1 / m₀ ^ 2 := by
  set u : DField n k := dirGreen n k m₀ *ᵥ (fun _ => 1) with hudef
  have hu : ∀ z, u z = ∑ y, dirGreen n k m₀ z y := by
    intro z; simp [hudef, mulVec, dotProduct]
  have hu0 : ∀ z, 0 ≤ u z := fun z => by
    rw [hu]; exact Finset.sum_nonneg fun y _ => dirGreen_nonneg hm z y
  have hDu : dirOp n k m₀ *ᵥ u = fun _ => 1 := by
    rw [hudef, mulVec_mulVec, dirOp_mul_dirGreen hm, one_mulVec]
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ u ⟨x, Finset.mem_univ x⟩
  have hle : ∀ y, u y ≤ u x0 := fun y => hx0 y (Finset.mem_univ y)
  have he := fun q => glp_ext_le u (hu0 x0) hle q
  have h := congrFun hDu x0
  rw [dirOp_mulVec_apply] at h
  have hε : 0 < (spacing n ^ 2)⁻¹ := by have := spacing_pos n; positivity
  have hnn : 0 ≤ (spacing n ^ 2)⁻¹ *
      ((2 * u x0 - ext u ((site x0).1 - 1, (site x0).2) - ext u ((site x0).1 + 1, (site x0).2))
        + (2 * u x0 - ext u ((site x0).1, (site x0).2 - 1) - ext u ((site x0).1, (site x0).2 + 1))) := by
    apply mul_nonneg hε.le
    linarith [he ((site x0).1 - 1, (site x0).2), he ((site x0).1 + 1, (site x0).2),
      he ((site x0).1, (site x0).2 - 1), he ((site x0).1, (site x0).2 + 1)]
  have hm2 : 0 < m₀ ^ 2 := by positivity
  have h1 : m₀ ^ 2 * u x0 ≤ 1 := by linarith
  rw [← hu x]
  rw [le_div_iff₀ hm2]
  nlinarith [hle x]

/-- Goal 1 in lattice-covariance form: ε² Σ_y ε⁻² dirGreen x y ≤ m₀⁻². -/
theorem glp_cov_rowSum_le {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) :
    spacing n ^ 2 * ∑ y, (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x y ≤ (m₀ ^ 2)⁻¹ := by
  have hε : spacing n ^ 2 ≠ 0 := by have := spacing_pos n; positivity
  rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hε, one_mul, ← one_div]
  exact glp_dirGreen_rowSum_le hm x

/-! ## Heat-kernel bounds -/

/-- Diagonal bound keeping the mass: ε⁻² p_t(x, x) ≤ e^{−t m₀²} π/(4t). -/
theorem glp_heatK_diag_le (m₀ : ℝ) {t : ℝ} (ht : 0 < t) (x : DSite n k) :
    (spacing n ^ 2)⁻¹ * heatK n k m₀ t x x ≤ exp (-(t * m₀ ^ 2)) * (π / (4 * t)) := by
  have hε := spacing_pos n
  set τ := t * (spacing n ^ 2)⁻¹ with hτ
  have hτ0 : 0 < τ := by positivity
  rw [heatK_diag_eq]
  have b1 := heat1_le (boxN n k) hτ0 x.1
  have b2 := heat1_le (boxN n k) hτ0 x.2
  have n1 := heat1_nonneg (boxN n k) τ x.1
  have n2 := heat1_nonneg (boxN n k) τ x.2
  have hprod : heat1 (boxN n k) τ x.1 * heat1 (boxN n k) τ x.2 ≤ π / (4 * τ) := by
    calc _ ≤ √(π / (4 * τ)) * √(π / (4 * τ)) := mul_le_mul b1 b2 n2 (sqrt_nonneg _)
      _ = π / (4 * τ) := mul_self_sqrt (by positivity)
  calc (spacing n ^ 2)⁻¹ * (exp (-(t * m₀ ^ 2)) *
        (heat1 (boxN n k) τ x.1 * heat1 (boxN n k) τ x.2))
      ≤ (spacing n ^ 2)⁻¹ * (exp (-(t * m₀ ^ 2)) * (π / (4 * τ))) := by
        gcongr
    _ = exp (-(t * m₀ ^ 2)) * (π / (4 * t)) := by rw [hτ]; field_simp

/-- Off-diagonal bound: |p_t(x, y)| ≤ (p_t(x, x) + p_t(y, y))/2 (semigroup + AM–GM). -/
theorem glp_heatK_abs_le (m₀ t : ℝ) (x y : DSite n k) :
    |heatK n k m₀ t x y| ≤ (heatK n k m₀ t x x + heatK n k m₀ t y y) / 2 := by
  have hs := heatK_semigroup m₀ (t / 2) (t / 2) x y
  rw [add_halves] at hs
  have h1 := heatK_sq_sum m₀ (t / 2) x
  have h2 := heatK_sq_sum m₀ (t / 2) y
  rw [show 2 * (t / 2) = t by ring] at h1 h2
  rw [← hs, ← h1, ← h2]
  calc |∑ z, heatK n k m₀ (t / 2) x z * heatK n k m₀ (t / 2) z y|
      ≤ ∑ z, |heatK n k m₀ (t / 2) x z * heatK n k m₀ (t / 2) z y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, (heatK n k m₀ (t / 2) x z ^ 2 + heatK n k m₀ (t / 2) y z ^ 2) / 2 := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [heatK_symm m₀ (t / 2) z y, abs_mul]
        nlinarith [sq_nonneg (|heatK n k m₀ (t / 2) x z| - |heatK n k m₀ (t / 2) y z|),
          sq_abs (heatK n k m₀ (t / 2) x z), sq_abs (heatK n k m₀ (t / 2) y z)]
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]

end PP2Target

end

import Mathlib
import YMBridgeE1

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, 22 Nov 2026 UTC (Formalizer).
Lattice only; nothing here concerns the continuum theory.

Bridge, stage E2: the first derivative of the total-variation distance `W` in mu.

Notation and hypotheses as in stage E1 (`YMBridgeE1`): `ν` is continuous and positive on the open
interval (-1, 1), `d > 0`, `N ν n s y = ∫_y^1 xⁿ e^{sx} ν(x) dx`, `c = cut ν d μ`.

Calculus, for a continuous weight (no positivity needed):
* `hasDerivAt_N_fst`: d/ds N_n(s, y) = N_{n+1}(s, y)       (differentiation under the integral).
* `hasDerivAt_N_snd`: d/dy N_n(s, y) = -yⁿ e^{sy} ν(y)     (fundamental theorem of calculus).
* `hasDerivAt_N_comp`: the chain rule along a differentiable curve t ↦ (σ t, γ t).
Then:
* `hasDerivAt_mean`: d/ds m_s = Var_s.
* `hasDerivAt_cut`: d/dμ c = (m_{s2} - m_{s1})/(2d).
* `hasDerivAt_W`: W'(μ) = g(s2, c) - g(s1, c), where g(s, y) = N_1(s, y)/Z(s) - m_s N_0(s, y)/Z(s)
  is Cov_s(1_{X>y}, X). The term in d/dμ c drops out because the two densities agree at c.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

namespace YMBridge

variable {ν : ℝ → ℝ} {d : ℝ}

theorem ker_one (s x : ℝ) : ker ν 1 s x = x * Real.exp (s * x) * ν x := by
  simp [ker]

theorem ker_continuous₂ (hν : Continuous ν) (n : ℕ) :
    Continuous (Function.uncurry (ker ν n)) := by
  unfold ker Function.uncurry
  fun_prop

theorem N_continuous₂ (hν : Continuous ν) (n : ℕ) :
    Continuous fun p : ℝ × ℝ => N ν n p.1 p.2 := by
  have h : (fun p : ℝ × ℝ => N ν n p.1 p.2)
      = fun p : ℝ × ℝ => -∫ x in (1 : ℝ)..p.2, ker ν n p.1 x := by
    funext p
    unfold N
    rw [intervalIntegral.integral_symm]
  rw [h]
  exact (intervalIntegral.continuous_parametric_primitive_of_continuous
    (ker_continuous₂ hν n)).neg

/-- Differentiation under the integral sign: `∂_s N_n = N_{n+1}`. -/
theorem hasDerivAt_N_fst (hν : Continuous ν) (n : ℕ) (s y : ℝ) :
    HasDerivAt (fun s => N ν n s y) (N ν (n + 1) s y) s := by
  have hexp : ∀ s' x : ℝ, HasDerivAt (fun s : ℝ => Real.exp (s * x)) (Real.exp (s' * x) * x) s' :=
    fun s' x => by
      simpa using ((hasDerivAt_id' s').mul_const x).exp
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := y) (b := 1) (F := fun s x => ker ν n s x)
    (F' := fun s x => ker ν (n + 1) s x) (x₀ := s) (s := Metric.ball s 1)
    (bound := fun x => |x| ^ (n + 1) * Real.exp ((|s| + 1) * |x|) * |ν x|)
    (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun s' => (ker_continuous hν n s').aestronglyMeasurable)
    ((ker_continuous hν n s).intervalIntegrable _ _)
    (ker_continuous hν (n + 1) s).aestronglyMeasurable
    (Eventually.of_forall fun x _ s' hs' => by
      have h1 : |s'| ≤ |s| + 1 := by
        have h2 : |s' - s| < 1 := by simpa [Real.dist_eq] using hs'
        have h3 := abs_sub_abs_le_abs_sub s' s
        linarith
      have h4 : s' * x ≤ (|s| + 1) * |x| :=
        calc s' * x ≤ |s' * x| := le_abs_self _
          _ = |s'| * |x| := abs_mul _ _
          _ ≤ (|s| + 1) * |x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      rw [Real.norm_eq_abs]
      unfold ker
      rw [abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      gcongr)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Eventually.of_forall fun x _ s' _ => by
      unfold ker
      convert ((hexp s' x).const_mul (x ^ n)).mul_const (ν x) using 1
      ring)
  exact key.2

/-- Fundamental theorem of calculus at the lower endpoint: `∂_y N_n = -yⁿ e^{sy} ν(y)`. -/
theorem hasDerivAt_N_snd (hν : Continuous ν) (n : ℕ) (s y : ℝ) :
    HasDerivAt (fun y => N ν n s y) (-ker ν n s y) y := by
  unfold N
  exact intervalIntegral.integral_hasDerivAt_left
    ((ker_continuous hν n s).intervalIntegrable _ _)
    ((ker_continuous hν n s).stronglyMeasurableAtFilter _ _)
    (ker_continuous hν n s).continuousAt

/-- The chain rule for `N_n` along a differentiable curve `t ↦ (σ t, γ t)`: both the parameter
and the lower endpoint move. -/
theorem hasDerivAt_N_comp (hν : Continuous ν) (n : ℕ) {σ γ : ℝ → ℝ} {σ' γ' t : ℝ}
    (hσ : HasDerivAt σ σ' t) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun t => N ν n (σ t) (γ t))
      (N ν (n + 1) (σ t) (γ t) * σ' - ker ν n (σ t) (γ t) * γ') t := by
  have hstrict := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (σ t, γ t))
    (f := fun s y => N ν n s y)
    (f₁ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (N ν (n + 1) s y))
    (f₂ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (-ker ν n s y))
    (Eventually.of_forall fun v => (hasDerivAt_N_fst hν n v.1 v.2).hasFDerivAt)
    (Eventually.of_forall fun v => (hasDerivAt_N_snd hν n v.1 v.2).hasFDerivAt)
    (by
      have h : Continuous fun v : ℝ × ℝ =>
          ContinuousLinearMap.toSpanSingleton ℝ (N ν (n + 1) v.1 v.2) :=
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp
          (N_continuous₂ hν (n + 1))
      exact h.continuousAt)
    (by
      have h : Continuous fun v : ℝ × ℝ =>
          ContinuousLinearMap.toSpanSingleton ℝ (-ker ν n v.1 v.2) :=
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp
          (ker_continuous₂ hν n).neg
      exact h.continuousAt)
  have hcomp := hstrict.hasFDerivAt.comp_hasDerivAt t (hσ.prodMk hγ)
  convert hcomp using 1
  · rfl
  · simp only [Function.HasUncurry.uncurry, id, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring

theorem hasDerivAt_Z (hν : Continuous ν) (s : ℝ) : HasDerivAt (Z ν) (N ν 1 s (-1)) s :=
  hasDerivAt_N_fst hν 0 s (-1)

/-- `d/ds m_s = Var_s`. -/
theorem hasDerivAt_mean (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (s : ℝ) :
    HasDerivAt (mean ν) (var ν s) s := by
  have hZ := (Z_pos hν hpos s).ne'
  have h := (hasDerivAt_N_fst hν 1 s (-1)).div (hasDerivAt_Z hν s) hZ
  show HasDerivAt (fun s => N ν 1 s (-1) / Z ν s) (var ν s) s
  convert h using 1
  unfold var mean
  field_simp

/-- `d/dμ c = (m_{μ+d} - m_{μ-d})/(2d)`. -/
theorem hasDerivAt_cut (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d)
    (μ : ℝ) : HasDerivAt (cut ν d) ((mean ν (μ + d) - mean ν (μ - d)) / (2 * d)) μ := by
  have hZ1 := (Z_pos hν hpos (μ - d)).ne'
  have hZ2 := (Z_pos hν hpos (μ + d)).ne'
  have hd' : d ≠ 0 := hd.ne'
  have h2 := (hasDerivAt_Z hν (μ + d)).comp_add_const μ d
  have h1 := (hasDerivAt_Z hν (μ - d)).comp_sub_const μ d
  have h := (((h2.div h1 hZ1).log (div_ne_zero hZ2 hZ1)).div_const (2 * d))
  simp only [Pi.div_apply] at h
  show HasDerivAt (fun μ => Real.log (Z ν (μ + d) / Z ν (μ - d)) / (2 * d)) _ μ
  convert h using 1
  unfold mean
  field_simp

/-- `g(s, y) = N_1(s, y)/Z(s) - m_s·N_0(s, y)/Z(s)`, that is `Cov_s(1_{X>y}, X)`. -/
noncomputable def g (ν : ℝ → ℝ) (s y : ℝ) : ℝ :=
  N ν 1 s y / Z ν s - mean ν s * (N ν 0 s y / Z ν s)

/-- Derivative of a tail probability `Q_{t+a}(X > γ t)` along a moving cut. -/
theorem hasDerivAt_tail (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x)
    {γ : ℝ → ℝ} {γ' : ℝ} (a μ : ℝ) (hγ : HasDerivAt γ γ' μ) :
    HasDerivAt (fun t => N ν 0 (t + a) (γ t) / Z ν (t + a))
      (g ν (μ + a) (γ μ) - dens ν (μ + a) (γ μ) * γ') μ := by
  have hZ := (Z_pos hν hpos (μ + a)).ne'
  have hN := hasDerivAt_N_comp hν 0 ((hasDerivAt_id' μ).add_const a) hγ
  have hZd := (hasDerivAt_Z hν (μ + a)).comp_add_const μ a
  have h := hN.div hZd hZ
  convert h using 1
  unfold g dens mean
  rw [ker_zero]
  field_simp
  ring

/-- **First derivative.** `W'(μ) = g(μ + d, c) - g(μ - d, c)`: no term in `d/dμ c`, because the
two densities agree at the crossing point `c`. -/
theorem hasDerivAt_W (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d)
    (μ : ℝ) :
    HasDerivAt (W ν d) (g ν (μ + d) (cut ν d μ) - g ν (μ - d) (cut ν d μ)) μ := by
  have hW : W ν d = fun t => N ν 0 (t + d) (cut ν d t) / Z ν (t + d)
      - N ν 0 (t + -d) (cut ν d t) / Z ν (t + -d) := by
    funext t
    rw [W_eq hν hpos hd t, sub_eq_add_neg t d]
  have hc := hasDerivAt_cut hν hpos hd μ
  have h := (hasDerivAt_tail hν hpos d μ hc).sub (hasDerivAt_tail hν hpos (-d) μ hc)
  rw [hW]
  convert h using 1
  rw [← sub_eq_add_neg, dens_cut_eq hν hpos hd μ]
  ring

end YMBridge

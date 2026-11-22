import Mathlib
import YMBridgeE2

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, 22 Nov 2026 UTC (Formalizer).
Lattice only; nothing here concerns the continuum theory.

Bridge, stage E3: the second derivative of the total-variation distance `W` in mu is the
expression `(*)` of the header of the G certificates.

Notation and hypotheses as in stages E1 and E2 (`YMBridgeE1`, `YMBridgeE2`): `ν : ℝ → ℝ` is
continuous and positive on the open interval (-1, 1), and `d > 0`. With s2 = μ + d, s1 = μ - d and
c = `cut ν d μ` = log(Z(s2)/Z(s1))/(2d):

  `W ν d μ`   = (1/2) ∫_{-1}^1 |q_{s2}(x) - q_{s1}(x)| dx,     q_s(x) = e^{sx} ν(x)/Z(s),
  `Phi ν d μ` = U(s2) - U(s1) + q (m_{s2} - m_{s1})²/(2d),      q = e^{s2 c} ν(c)/Z(s2),
  U(s) = (N_2 - 2 m_s N_1 + m_s² N_0)/Z - (N_0/Z) Var_s,       N_n = ∫_c^1 xⁿ e^{sx} ν(x) dx.

Proved here, for every real μ:
* `hasDerivAt_g`: the derivative of t ↦ g(t + a, γ t) along a moving cut γ is
  U(μ + a, γ μ) - (γ μ - m_{μ+a})·q_{μ+a}(γ μ)·γ'.
* `hasDerivAt_W'`: the derivative of W' (as given by stage E2) at μ is `Phi ν d μ`.
* `W_second_deriv`: `deriv (deriv (W ν d)) μ = Phi ν d μ`.
* `W_differentiable`, `W_deriv_differentiable`: W and W' are differentiable.
* `bridge`: the three facts in one statement.

NOT formalized here: that W for the paper's weight ν_r is the total-variation distance of the
lattice conditional laws; that `Phi` is negative (the certificates); that the certificate programs
compute `Phi`. That ν_r satisfies the two hypotheses is stage E4 (`YMBridgeE4`).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

namespace YMBridge

variable {ν : ℝ → ℝ} {d : ℝ}

/-- Derivative of `g` along a moving cut: `∂_s g = U` and `∂_y g = -(y - m_s) q_s(y)`. -/
theorem hasDerivAt_g (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x)
    {γ : ℝ → ℝ} {γ' : ℝ} (a μ : ℝ) (hγ : HasDerivAt γ γ' μ) :
    HasDerivAt (fun t => g ν (t + a) (γ t))
      (U ν (μ + a) (γ μ) - (γ μ - mean ν (μ + a)) * dens ν (μ + a) (γ μ) * γ') μ := by
  have hZ := (Z_pos hν hpos (μ + a)).ne'
  have hσ := (hasDerivAt_id' μ).add_const a
  have hN1 := hasDerivAt_N_comp hν 1 hσ hγ
  have hN0 := hasDerivAt_N_comp hν 0 hσ hγ
  have hZd := (hasDerivAt_Z hν (μ + a)).comp_add_const μ a
  have hm := (hasDerivAt_mean hν hpos (μ + a)).comp_add_const μ a
  have h := (hN1.div hZd hZ).sub (hm.mul (hN0.div hZd hZ))
  simp only [Pi.div_apply] at h
  show HasDerivAt (fun t => N ν 1 (t + a) (γ t) / Z ν (t + a)
    - mean ν (t + a) * (N ν 0 (t + a) (γ t) / Z ν (t + a))) _ μ
  convert h using 1
  unfold U dens var mean
  rw [ker_zero, ker_one]
  field_simp
  ring

/-- **Second derivative.** The derivative of `W'` at `μ` is the header's expression `(*)`. -/
theorem hasDerivAt_W' (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d)
    (μ : ℝ) :
    HasDerivAt (fun t => g ν (t + d) (cut ν d t) - g ν (t - d) (cut ν d t)) (Phi ν d μ) μ := by
  have hd' : d ≠ 0 := hd.ne'
  have hc := hasDerivAt_cut hν hpos hd μ
  have h := (hasDerivAt_g hν hpos d μ hc).sub (hasDerivAt_g hν hpos (-d) μ hc)
  simp only [← sub_eq_add_neg] at h
  convert h using 1
  unfold Phi
  rw [dens_cut_eq hν hpos hd μ]
  field_simp
  ring

/-- `W` is differentiable in `μ`. -/
theorem W_differentiable (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x)
    (hd : 0 < d) : Differentiable ℝ (W ν d) :=
  fun μ => (hasDerivAt_W hν hpos hd μ).differentiableAt

theorem deriv_W (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d) :
    deriv (W ν d) = fun t => g ν (t + d) (cut ν d t) - g ν (t - d) (cut ν d t) :=
  funext fun t => (hasDerivAt_W hν hpos hd t).deriv

/-- `W'` is differentiable in `μ`. -/
theorem W_deriv_differentiable (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x)
    (hd : 0 < d) : Differentiable ℝ (deriv (W ν d)) := by
  rw [deriv_W hν hpos hd]
  exact fun μ => (hasDerivAt_W' hν hpos hd μ).differentiableAt

/-- **The bridge.** For a continuous weight that is positive on (-1, 1), and `d > 0`, the second
derivative in `μ` of `W` (the integral `(1/2) ∫ |q_{μ+d} - q_{μ-d}|`) is the header's `(*)`. -/
theorem W_second_deriv (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d)
    (μ : ℝ) : deriv (deriv (W ν d)) μ = Phi ν d μ := by
  rw [deriv_W hν hpos hd]
  exact (hasDerivAt_W' hν hpos hd μ).deriv

/-- The bridge in one statement: `W` is twice differentiable in `μ` and `W'' = (*)`. -/
theorem bridge (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d) :
    Differentiable ℝ (W ν d) ∧ Differentiable ℝ (deriv (W ν d))
      ∧ ∀ μ : ℝ, deriv (deriv (W ν d)) μ = Phi ν d μ :=
  ⟨W_differentiable hν hpos hd, W_deriv_differentiable hν hpos hd, W_second_deriv hν hpos hd⟩

end YMBridge

import Mathlib
import YMBridgeE3

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, 22 Nov 2026 UTC (Formalizer).
Lattice only; nothing here concerns the continuum theory.

Bridge, stage E4 (an addition to the handoff's stages E1 to E3): the paper's weight satisfies the
hypotheses of the bridge.

  φ(z) = sinh z / z with φ(0) = 1      is `phi`, defined as `dslope Real.sinh 0`
  ν_r(x) = w·φ(r·w), w = √(1 - x²)     is `nuR r x`

In Lean, `Real.sinh z / z` is 0 at z = 0, not 1, so a definition of ν_r by the bare quotient would
be the zero function at r = 0. `dslope Real.sinh 0` is the quotient away from 0 and the derivative
cosh 0 = 1 at 0. A phase 3 `Spec` should use `nuR`, or prove its own weight equal to it.

Proved here:
* `phi_zero`, `phi_of_ne`, `phi_continuous`, `phi_pos`.
* `nuR_continuous`, `nuR_pos`: ν_r is continuous, and positive on (-1, 1), for every real r.
* `bridge_nuR`: for every real r and μ and every d > 0, W for ν_r is twice differentiable in μ and
  its second derivative is the header's expression `(*)`.

NOT formalized: that W for ν_r is the total-variation distance of the lattice conditional laws;
that `Phi (nuR r) d μ` is negative on the range (the certificates); that the certificate programs
compute `Phi (nuR r) d μ / d`.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Set

namespace YMBridge

/-- `φ(z) = sinh z / z`, with `φ(0) = 1`. -/
noncomputable def phi (z : ℝ) : ℝ := dslope Real.sinh 0 z

theorem phi_zero : phi 0 = 1 := by
  simp [phi]

theorem phi_of_ne {z : ℝ} (hz : z ≠ 0) : phi z = Real.sinh z / z := by
  simp [phi, dslope_of_ne _ hz, slope_def_field]

theorem phi_continuous : Continuous phi := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    exact continuousAt_dslope_same.mpr Real.differentiable_sinh.differentiableAt
  · exact (continuousAt_dslope_of_ne hz).mpr Real.continuous_sinh.continuousAt

theorem phi_pos (z : ℝ) : 0 < phi z := by
  by_cases hz : z = 0
  · rw [hz, phi_zero]
    exact one_pos
  · rw [phi_of_ne hz]
    rcases lt_or_gt_of_ne hz with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h
    · exact div_pos (Real.sinh_pos_iff.mpr h) h

/-- The paper's weight `ν_r(x) = w·φ(r·w)`, `w = √(1 - x²)`. -/
noncomputable def nuR (r x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2) * phi (r * Real.sqrt (1 - x ^ 2))

theorem nuR_continuous (r : ℝ) : Continuous (nuR r) := by
  have h := phi_continuous
  unfold nuR
  fun_prop

theorem nuR_pos (r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < nuR r x :=
  mul_pos (Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2])) (phi_pos _)

/-- The bridge for the paper's weight. -/
theorem bridge_nuR (r : ℝ) {d : ℝ} (hd : 0 < d) :
    Differentiable ℝ (W (nuR r) d) ∧ Differentiable ℝ (deriv (W (nuR r) d))
      ∧ ∀ μ : ℝ, deriv (deriv (W (nuR r) d)) μ = Phi (nuR r) d μ :=
  bridge (nuR_continuous r) (fun _ hx => nuR_pos r hx) hd

end YMBridge

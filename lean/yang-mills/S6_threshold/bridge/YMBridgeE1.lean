import Mathlib

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, 22 Nov 2026 UTC (Formalizer).
Lattice only; nothing here concerns the continuum theory.

Bridge, stage E1: definitions and the crossing lemma.

The G certificates (python/yang-mills/S4_general_d/G_box_A_1of2.py, python/yang-mills/S6_threshold)
enclose an expression written in their header. This file defines that expression, `Phi`, for a
general weight, and proves the crossing lemma behind it. Stages E2 and E3 prove that `Phi` is the
second derivative in mu of the total-variation distance `W`.

The weight is any continuous `ν : ℝ → ℝ` that is positive on the OPEN interval (-1, 1). The paper's
weight ν_r(x) = w·φ(r·w), w = √(1 - x²), φ(z) = sinh z / z, is of this kind (it vanishes at ±1, so
positivity on the closed interval would exclude it). That ν_r satisfies the hypotheses is proved
in stage E4 (`YMBridgeE4`: `nuR`, `nuR_continuous`, `nuR_pos`).

Dictionary with the header of G_box_A_1of2.py (s2 = mu + d, s1 = mu - d):
  N_n(s) = ∫_c^1 xⁿ e^{sx} ν    is `N ν n s c`           M_n(s) = ∫_{-1}^1 … is `N ν n s (-1)`
  Z = M_0                        is `Z ν s`               m_s = M_1/Z          is `mean ν s`
  Var_s = M_2/Z - m_s²           is `var ν s`             c = log(Z(s2)/Z(s1))/(2d) is `cut ν d μ`
  q = e^{s2 c} ν(c)/Z(s2)        is `dens ν (μ + d) (cut ν d μ)`
  U(s) = (N_2 - 2 m_s N_1 + m_s² N_0)/Z - (N_0/Z) Var_s           is `U ν s c`
  (*) = U(s2) - U(s1) + q (m_{s2} - m_{s1})²/(2d)                 is `Phi ν d μ`
and W(mu) = (1/2) ∫_{-1}^1 |q_{s2} - q_{s1}| dx, q_s(x) = e^{sx} ν(x)/Z(s), is `W ν d μ`. `W` is
DEFINED by this integral; that it is the total-variation distance of the two laws as measures is
not formalized.

Proved here, for d > 0 and every real μ:
* `cut_mem_Ioo`: -1 < c < 1.
* `dens_cut_eq`: the two densities agree at c.
* `W_eq`: W = N_0(s2, c)/Z(s2) - N_0(s1, c)/Z(s1), that is Q_{s2}(X > c) - Q_{s1}(X > c).

For the phase 3 `Spec`: `Phi` is a plain function of real arguments built from interval integrals.
`Spec` should state the certificate's claim as `Phi (nuR r) d μ / d < 0` on the boxes, with `nuR`
the weight of stage E4, and use `bridge_nuR` from there.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set

namespace YMBridge

/-- The integrand `xⁿ e^{s x} ν(x)`. -/
noncomputable def ker (ν : ℝ → ℝ) (n : ℕ) (s x : ℝ) : ℝ := x ^ n * Real.exp (s * x) * ν x

/-- `N ν n s y = ∫_y^1 xⁿ e^{s x} ν(x) dx`. -/
noncomputable def N (ν : ℝ → ℝ) (n : ℕ) (s y : ℝ) : ℝ := ∫ x in y..1, ker ν n s x

/-- The normalising constant `Z(s) = ∫_{-1}^1 e^{s x} ν(x) dx`. -/
noncomputable def Z (ν : ℝ → ℝ) (s : ℝ) : ℝ := N ν 0 s (-1)

/-- The mean `m_s = M_1(s)/Z(s)`. -/
noncomputable def mean (ν : ℝ → ℝ) (s : ℝ) : ℝ := N ν 1 s (-1) / Z ν s

/-- The variance `Var_s = M_2(s)/Z(s) - m_s²`. -/
noncomputable def var (ν : ℝ → ℝ) (s : ℝ) : ℝ := N ν 2 s (-1) / Z ν s - mean ν s ^ 2

/-- The density `q_s(x) = e^{s x} ν(x)/Z(s)`. -/
noncomputable def dens (ν : ℝ → ℝ) (s x : ℝ) : ℝ := Real.exp (s * x) * ν x / Z ν s

/-- The crossing point `c = log(Z(μ + d)/Z(μ - d))/(2d)`. -/
noncomputable def cut (ν : ℝ → ℝ) (d μ : ℝ) : ℝ := Real.log (Z ν (μ + d) / Z ν (μ - d)) / (2 * d)

/-- `W(μ) = (1/2) ∫_{-1}^1 |q_{μ+d} - q_{μ-d}|`, the total-variation distance of the two laws,
defined here by this integral. -/
noncomputable def W (ν : ℝ → ℝ) (d μ : ℝ) : ℝ :=
  (1 / 2) * ∫ x in (-1 : ℝ)..1, |dens ν (μ + d) x - dens ν (μ - d) x|

/-- The header's `U(s)`, at cut `y`. -/
noncomputable def U (ν : ℝ → ℝ) (s y : ℝ) : ℝ :=
  (N ν 2 s y - 2 * mean ν s * N ν 1 s y + mean ν s ^ 2 * N ν 0 s y) / Z ν s
    - N ν 0 s y / Z ν s * var ν s

/-- The header's expression `(*)`. -/
noncomputable def Phi (ν : ℝ → ℝ) (d μ : ℝ) : ℝ :=
  U ν (μ + d) (cut ν d μ) - U ν (μ - d) (cut ν d μ)
    + dens ν (μ + d) (cut ν d μ) * (mean ν (μ + d) - mean ν (μ - d)) ^ 2 / (2 * d)

variable {ν : ℝ → ℝ} {d : ℝ}

theorem ker_continuous (hν : Continuous ν) (n : ℕ) (s : ℝ) : Continuous (ker ν n s) := by
  unfold ker
  fun_prop

theorem ker_zero (s x : ℝ) : ker ν 0 s x = Real.exp (s * x) * ν x := by
  simp [ker]

theorem ker_pos (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (s : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < ker ν 0 s x := by
  rw [ker_zero]
  exact mul_pos (Real.exp_pos _) (hpos x hx)

theorem Z_pos (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (s : ℝ) : 0 < Z ν s := by
  unfold Z N
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((ker_continuous hν 0 s).intervalIntegrable _ _) (fun x hx => ker_pos hpos s hx) (by norm_num)

theorem nu_nonneg (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : 0 ≤ ν x := by
  have hcl : closure (Ioo (-1 : ℝ) 1) = Icc (-1) 1 := closure_Ioo (by norm_num)
  have h : ∀ y ∈ Ioo (-1 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) y ≤ ν y := fun y hy => (hpos y hy).le
  exact le_on_closure h continuousOn_const hν.continuousOn (hcl ▸ hx)

theorem dens_continuous (hν : Continuous ν) (s : ℝ) : Continuous (dens ν s) := by
  unfold dens
  fun_prop

theorem integral_dens (s a : ℝ) :
    ∫ x in a..1, dens ν s x = N ν 0 s a / Z ν s := by
  unfold dens N
  rw [intervalIntegral.integral_div]
  congr 1
  exact intervalIntegral.integral_congr (fun x _ => (ker_zero s x).symm)

/-- `e^{2 d c} = Z(μ + d)/Z(μ - d)`. -/
theorem exp_cut (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d) (μ : ℝ) :
    Real.exp (2 * d * cut ν d μ) = Z ν (μ + d) / Z ν (μ - d) := by
  have h : 2 * d * cut ν d μ = Real.log (Z ν (μ + d) / Z ν (μ - d)) := by
    unfold cut
    field_simp
  rw [h, Real.exp_log (div_pos (Z_pos hν hpos _) (Z_pos hν hpos _))]

/-- The likelihood-ratio form of the difference: `q_{s2} - q_{s1} = q_{s1}·(e^{2d(x - c)} - 1)`. -/
theorem dens_sub (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d)
    (μ x : ℝ) :
    dens ν (μ + d) x - dens ν (μ - d) x
      = dens ν (μ - d) x * (Real.exp (2 * d * (x - cut ν d μ)) - 1) := by
  have hZ1 := Z_pos hν hpos (μ - d)
  have hZ2 := Z_pos hν hpos (μ + d)
  have hc := exp_cut hν hpos hd μ
  have h1 : Real.exp ((μ + d) * x) = Real.exp ((μ - d) * x) * Real.exp (2 * d * x) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp (2 * d * (x - cut ν d μ))
      = Real.exp (2 * d * x) / (Z ν (μ + d) / Z ν (μ - d)) := by
    rw [← hc, ← Real.exp_sub]
    ring_nf
  unfold dens
  rw [h1, h2]
  field_simp

/-- The two densities agree at the crossing point. -/
theorem dens_cut_eq (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d)
    (μ : ℝ) : dens ν (μ + d) (cut ν d μ) = dens ν (μ - d) (cut ν d μ) := by
  have h := dens_sub hν hpos hd μ (cut ν d μ)
  rw [sub_self, mul_zero, Real.exp_zero, sub_self, mul_zero] at h
  linarith

theorem Z_lt (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d) (μ : ℝ) :
    Z ν (μ + d) < Real.exp (2 * d) * Z ν (μ - d) := by
  have hk1 := ker_continuous hν 0 (μ - d)
  have hk2 := ker_continuous hν 0 (μ + d)
  have key : 0 < ∫ x in (-1 : ℝ)..1, (Real.exp (2 * d) * ker ν 0 (μ - d) x - ker ν 0 (μ + d) x) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (((hk1.const_mul _).sub hk2).intervalIntegrable _ _) (fun x hx => ?_) (by norm_num)
    have h1 : ker ν 0 (μ + d) x = Real.exp (2 * d * x) * ker ν 0 (μ - d) x := by
      rw [ker_zero, ker_zero, ← mul_assoc, ← Real.exp_add]
      ring_nf
    have h2 : Real.exp (2 * d * x) < Real.exp (2 * d) :=
      Real.exp_lt_exp.mpr (by nlinarith [hx.2])
    have h3 := ker_pos hpos (μ - d) hx
    rw [h1]
    nlinarith
  rw [intervalIntegral.integral_sub ((hk1.const_mul _).intervalIntegrable _ _)
    (hk2.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at key
  unfold Z N
  linarith

theorem Z_gt (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d) (μ : ℝ) :
    Real.exp (-(2 * d)) * Z ν (μ - d) < Z ν (μ + d) := by
  have hk1 := ker_continuous hν 0 (μ - d)
  have hk2 := ker_continuous hν 0 (μ + d)
  have key : 0 < ∫ x in (-1 : ℝ)..1,
      (ker ν 0 (μ + d) x - Real.exp (-(2 * d)) * ker ν 0 (μ - d) x) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hk2.sub (hk1.const_mul _)).intervalIntegrable _ _) (fun x hx => ?_) (by norm_num)
    have h1 : ker ν 0 (μ + d) x = Real.exp (2 * d * x) * ker ν 0 (μ - d) x := by
      rw [ker_zero, ker_zero, ← mul_assoc, ← Real.exp_add]
      ring_nf
    have h2 : Real.exp (-(2 * d)) < Real.exp (2 * d * x) :=
      Real.exp_lt_exp.mpr (by nlinarith [hx.1])
    have h3 := ker_pos hpos (μ - d) hx
    rw [h1]
    nlinarith
  rw [intervalIntegral.integral_sub (hk2.intervalIntegrable _ _)
    ((hk1.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul] at key
  unfold Z N
  linarith

/-- The crossing point lies in the open interval. -/
theorem cut_mem_Ioo (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d)
    (μ : ℝ) : cut ν d μ ∈ Ioo (-1 : ℝ) 1 := by
  have hZ1 := Z_pos hν hpos (μ - d)
  have hZ2 := Z_pos hν hpos (μ + d)
  have hr : 0 < Z ν (μ + d) / Z ν (μ - d) := div_pos hZ2 hZ1
  have hup : Real.log (Z ν (μ + d) / Z ν (μ - d)) < 2 * d := by
    rw [Real.log_lt_iff_lt_exp hr, div_lt_iff₀ hZ1]
    exact Z_lt hν hpos hd μ
  have hlo : -(2 * d) < Real.log (Z ν (μ + d) / Z ν (μ - d)) := by
    rw [Real.lt_log_iff_exp_lt hr, lt_div_iff₀ hZ1]
    exact Z_gt hν hpos hd μ
  have h2d : 0 < 2 * d := by positivity
  unfold cut
  constructor
  · rw [lt_div_iff₀ h2d]
    linarith
  · rw [div_lt_iff₀ h2d]
    linarith

/-- **Crossing lemma.** The total-variation distance is the difference of the two tail
probabilities at the crossing point: `W = Q_{s2}(X > c) - Q_{s1}(X > c)`. -/
theorem W_eq (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d) (μ : ℝ) :
    W ν d μ = N ν 0 (μ + d) (cut ν d μ) / Z ν (μ + d)
      - N ν 0 (μ - d) (cut ν d μ) / Z ν (μ - d) := by
  obtain ⟨hc1, hc2⟩ := cut_mem_Ioo hν hpos hd μ
  have hZ1 := Z_pos hν hpos (μ - d)
  have hZ2 := Z_pos hν hpos (μ + d)
  have hq1 := dens_continuous hν (μ - d)
  have hq2 := dens_continuous hν (μ + d)
  have hD : Continuous fun x => dens ν (μ + d) x - dens ν (μ - d) x := hq2.sub hq1
  have hdens : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ dens ν (μ - d) x := fun x hx =>
    div_nonneg (mul_nonneg (Real.exp_pos _).le (nu_nonneg hν hpos hx)) hZ1.le
  have hleft : ∫ x in (-1 : ℝ)..cut ν d μ, |dens ν (μ + d) x - dens ν (μ - d) x|
      = -∫ x in (-1 : ℝ)..cut ν d μ, (dens ν (μ + d) x - dens ν (μ - d) x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le hc1.le] at hx
    refine abs_of_nonpos ?_
    rw [dens_sub hν hpos hd μ x]
    have h1 : Real.exp (2 * d * (x - cut ν d μ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hx.2])
    exact mul_nonpos_of_nonneg_of_nonpos (hdens x ⟨hx.1, hx.2.trans hc2.le⟩) (by linarith)
  have hright : ∫ x in cut ν d μ..1, |dens ν (μ + d) x - dens ν (μ - d) x|
      = ∫ x in cut ν d μ..1, (dens ν (μ + d) x - dens ν (μ - d) x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le hc2.le] at hx
    refine abs_of_nonneg ?_
    rw [dens_sub hν hpos hd μ x]
    have h1 : 1 ≤ Real.exp (2 * d * (x - cut ν d μ)) :=
      Real.one_le_exp (by nlinarith [hx.1])
    exact mul_nonneg (hdens x ⟨hc1.le.trans hx.1, hx.2⟩) (by linarith)
  have hiD : ∀ a b : ℝ, IntervalIntegrable
      (fun x => dens ν (μ + d) x - dens ν (μ - d) x) volume a b :=
    fun a b => hD.intervalIntegrable a b
  have hiA : ∀ a b : ℝ, IntervalIntegrable
      (fun x => |dens ν (μ + d) x - dens ν (μ - d) x|) volume a b :=
    fun a b => hD.abs.intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hiA (-1) (cut ν d μ)) (hiA (cut ν d μ) 1)
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals
    (hiD (-1) (cut ν d μ)) (hiD (cut ν d μ) 1)
  have hsub : ∀ a : ℝ, ∫ x in a..1, (dens ν (μ + d) x - dens ν (μ - d) x)
      = N ν 0 (μ + d) a / Z ν (μ + d) - N ν 0 (μ - d) a / Z ν (μ - d) := fun a => by
    rw [intervalIntegral.integral_sub (hq2.intervalIntegrable _ _) (hq1.intervalIntegrable _ _),
      integral_dens, integral_dens]
  have htot : ∫ x in (-1 : ℝ)..1, (dens ν (μ + d) x - dens ν (μ - d) x) = 0 := by
    rw [hsub]
    have e1 : N ν 0 (μ + d) (-1) / Z ν (μ + d) = 1 := div_self hZ2.ne'
    have e2 : N ν 0 (μ - d) (-1) / Z ν (μ - d) = 1 := div_self hZ1.ne'
    rw [e1, e2, sub_self]
  unfold W
  rw [← hsplit, hleft, hright, ← hsub]
  linarith

end YMBridge

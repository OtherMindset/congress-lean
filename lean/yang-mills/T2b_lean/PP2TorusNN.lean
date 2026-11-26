import LongTable.PP2TorusMaxwell

/-!
Long Table, Claude council, target T2b: the concrete nearest-neighbour torus (ZMod N)², N ≥ 3,
for the T2b chain steps 1-4 (PP2TorusEOM.lean, PP2TorusMaxwell.lean).

FORMALIZED (no sorry; axioms propext / Classical.choice / Quot.sound).
* `Jnn`: adjacency matrix of (ZMod N)² (J_xy = 1 iff y − x ∈ {±e₁, ±e₂}); `Jnn_symm`, `Jnn_ti`,
  `sum_Jnn` (Σ_y J_0y = 4 for N ≥ 3).
* `eom_nn`: (4 − 2a)⟨φ_0⟩ − 4b⟨φ_0³⟩ + H = 0.
* `eom_continuum`: with a = 2 + ε²μ_b/2, b = λε², H = ε²h (ε ≠ 0): μ_b m + 4λ⟨φ_0³⟩ = h.
* `star_nn`, `maxwell_nn`: identity (★) and the Maxwell relation on (ZMod N)².
NOT FORMALIZED: the continuum-unit form of (★) (chain rule ∂_μ = ½ε²∂_a, ∂_h = ε²∂_H is
immediate but not stated); Wick ordering / c_ε (only enters through μ_b = μ − 12λc_ε).
Toolchain: Lean 4.35.0, Mathlib 56a00585.
-/

open Finset

set_option linter.unusedSectionVars false

noncomputable section
namespace T2bTorus

variable (N : ℕ) [NeZero N]

/-- The four lattice directions ±e₁, ±e₂. -/
def nbrs : Finset (ZMod N × ZMod N) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- Nearest-neighbour adjacency on the torus (ZMod N)². -/
def Jnn (x y : ZMod N × ZMod N) : ℝ := if y - x ∈ nbrs N then 1 else 0

theorem nbrs_neg (v : ZMod N × ZMod N) : -v ∈ nbrs N ↔ v ∈ nbrs N := by
  obtain ⟨p, q⟩ := v
  simp only [nbrs, mem_insert, mem_singleton, Prod.neg_mk, Prod.mk.injEq, neg_eq_iff_eq_neg,
    neg_zero, neg_neg]
  tauto

theorem card_nbrs (hN : 3 ≤ N) : (nbrs N).card = 4 := by
  have h1 : (1 : ZMod N) ≠ 0 := by
    intro h
    have : ((1 : ℕ) : ZMod N) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd one_pos this; omega
  have h2 : (1 : ZMod N) ≠ -1 := by
    intro h
    have : ((2 : ℕ) : ZMod N) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd two_pos this; omega
  have h3 : (-1 : ZMod N) ≠ 0 := neg_ne_zero.mpr h1
  simp [nbrs, h1, h2, h3, h1.symm, h3.symm]

theorem Jnn_symm (x y : ZMod N × ZMod N) : Jnn N x y = Jnn N y x := by
  unfold Jnn; rw [← neg_sub]; simp only [nbrs_neg]

theorem Jnn_ti (x y z : ZMod N × ZMod N) : Jnn N (x + z) (y + z) = Jnn N x y := by
  unfold Jnn; rw [add_sub_add_right_eq_sub]

theorem sum_Jnn (hN : 3 ≤ N) : ∑ y, Jnn N 0 y = 4 := by
  unfold Jnn
  simp only [sub_zero]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, card_nbrs N hN]
  norm_num

/-- S1 on the n.n. torus: (4 − 2a)⟨φ_0⟩ − 4b⟨φ_0³⟩ + H = 0. -/
theorem eom_nn (hN : 3 ≤ N) (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ) :
    (4 - 2 * a) * ex (Jnn N) a b H (fun φ => φ 0) - 4 * b * ex (Jnn N) a b H (fun φ => φ 0 ^ 3)
      + H = 0 := by
  have h := eom_ti (Jnn N) (Jnn_symm N) (Jnn_ti N) a hb H
  rwa [sum_Jnn N hN] at h

/-- S1 in continuum units: a = 2 + ε²μ_b/2, b = λε², H = ε²h give μ_b m + 4λ⟨φ_0³⟩ = h. -/
theorem eom_continuum (hN : 3 ≤ N) {ε lam : ℝ} (hε : ε ≠ 0) (hlam : 0 < lam) (μb h : ℝ) :
    μb * ex (Jnn N) (2 + ε ^ 2 * μb / 2) (lam * ε ^ 2) (ε ^ 2 * h) (fun φ => φ 0)
      + 4 * lam * ex (Jnn N) (2 + ε ^ 2 * μb / 2) (lam * ε ^ 2) (ε ^ 2 * h) (fun φ => φ 0 ^ 3)
      = h := by
  have h0 := eom_nn N hN (2 + ε ^ 2 * μb / 2) (b := lam * ε ^ 2) (by positivity) (ε ^ 2 * h)
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε
  apply mul_left_cancel₀ hε2
  linear_combination -h0

/-- Maxwell on (ZMod N)². -/
theorem maxwell_nn (a b H : ℝ) :
    ∑ y, cov (Jnn N) a b H (fun φ => φ 0) (fun φ => φ y ^ 2)
      = ∑ y, cov (Jnn N) a b H (fun φ => φ 0 ^ 2) (fun φ => φ y) :=
  maxwell (Jnn N) (Jnn_ti N) a b H

/-- Identity (★) on (ZMod N)². -/
theorem star_nn (a : ℝ) {b : ℝ} (hb : 0 < b) (H : ℝ)
    (hm : ex (Jnn N) a b H (fun φ => φ 0) ≠ 0) :
    ex (Jnn N) a b H (fun φ => φ 0) - H * deriv (fun H' => ex (Jnn N) a b H' (fun φ => φ 0)) H
      = 4 * b * ex (Jnn N) a b H (fun φ => φ 0) ^ 2 *
        (deriv (fun H' => cov (Jnn N) a b H' (fun φ => φ 0) (fun φ => φ 0 ^ 2)
            / ex (Jnn N) a b H' (fun φ => φ 0)) H
          - deriv (fun a' => ex (Jnn N) a' b H (fun φ => φ 0)) a) :=
  star_identity_maxwell (Jnn N) (Jnn_symm N) (Jnn_ti N) a hb H hm

end T2bTorus

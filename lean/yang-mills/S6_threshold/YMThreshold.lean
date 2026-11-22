import Mathlib

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, 22 Nov 2026 UTC (Steward).
Lattice only; nothing here concerns the continuum theory.

Series facts behind the exact threshold of the single-link total-variation Dobrushin criterion for
SU(2) (result post #mwpwcrz7-uii66h, steps 6 and 7; certificate beta0_exact.py, #mwpwa6a2-i0m9wl).

N(k) := ∑_j k^(2j+1) j! / ((2j+1)! ∏_{i=0..j}(i+3/2)) and Dq(k) := ∑_j k^(2j) / (2·4^j·j!·(j+1)!)
are DEFINED here by these series (the same definitions as in YMEndpoint.lean, whose docstrings
write D(k)/π for Dq(k); below, D is the lattice dimension). In the post,
N(d) = 2∫_0^1 sinh(dx)√(1-x²)dx, π·Dq(d) = Z₀(d) = ∫_{-1}^1 cosh(dx)√(1-x²)dx and T = N/(π·Dq).

Proved here, for these series:
* `N_lt_slope`: N(k) < (4k/3)·Dq(k) for 0 < k < 1            (step 6(c): T(k) < 4k/(3π)).
* `N_ge_first`, `Dq_le_cosh`: N(k) ≥ 2k/3 and Dq(k) ≤ 1/2 + (cosh k - 1)/8 for 0 ≤ k < 1
                                                               (step 6(b)).
* `line_B`: (12/5)·(4/(3π)) > 1 + (cosh(1/5) - 1)/4            (line (B) of beta0_exact.py).
* `root_side`: for real D ≥ 3 and b = 2/(5(D-1)): π·Dq(b) < 6(D-1)·N(b)   (6(D-1)T(b) > 1).
* `root_gt`: if D > 1, 0 < k < 1 and π·Dq(k) ≤ 6(D-1)·N(k), then k > π/(8(D-1)).
* `below_D`, `above_D` for D = 3, 4, 5, 6, 10, 100: the sign of 6(D-1)·N(k) - π·Dq(k) at the two
  seven-decimal endpoints of the post's enclosure of β₀(D); D = 4: 0.1310307 and 0.1310308.

NOT formalized: that these series equal the integrals; that N/(π·Dq) is a total-variation distance
or equals L₁/I₁; that it is continuous and increasing in k (so existence and uniqueness of the root
β₀(D) are not in this file: only the signs at the stated points); the row-sum theorem itself.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Nat Finset

namespace YMThreshold

/-- a_j(k) = k^(2j+1) · j! / ((2j+1)! · ∏_{i=0..j} (i + 3/2)), the j-th term of N(k). -/
noncomputable def aN (k : ℝ) (j : ℕ) : ℝ :=
  k ^ (2 * j + 1) * (j ! : ℝ) / (((2 * j + 1) ! : ℝ) * ∏ i ∈ range (j + 1), ((i : ℝ) + 3 / 2))

/-- b_j(k) = k^(2j) / (2 · 4^j · j! · (j+1)!), the j-th term of D(k)/π. -/
noncomputable def bD (k : ℝ) (j : ℕ) : ℝ :=
  k ^ (2 * j) / (2 * 4 ^ j * (j ! : ℝ) * ((j + 1) ! : ℝ))

/-- N(k) := ∑_{j ≥ 0} a_j(k). -/
noncomputable def Nser (k : ℝ) : ℝ := ∑' j : ℕ, aN k j

/-- D(k)/π := ∑_{j ≥ 0} b_j(k). -/
noncomputable def Dq (k : ℝ) : ℝ := ∑' j : ℕ, bD k j

theorem fpos (n : ℕ) : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n

theorem prod_pos' (j : ℕ) : (0 : ℝ) < ∏ i ∈ range (j + 1), ((i : ℝ) + 3 / 2) :=
  Finset.prod_pos fun i _ => by positivity

theorem aN_nonneg {k : ℝ} (hk : 0 ≤ k) (j : ℕ) : 0 ≤ aN k j := by
  unfold aN; have := fpos j; have := fpos (2 * j + 1); have := prod_pos' j; positivity

theorem bD_nonneg {k : ℝ} (hk : 0 ≤ k) (j : ℕ) : 0 ≤ bD k j := by
  unfold bD; have := fpos j; have := fpos (j + 1); positivity

/-- a_{j+1} = a_j · k² / (2(2j+3)(j+5/2)). -/
theorem aN_succ (k : ℝ) (j : ℕ) :
    aN k (j + 1) = aN k j * (k ^ 2 / (2 * (2 * (j : ℝ) + 3) * ((j : ℝ) + 5 / 2))) := by
  unfold aN
  have e1 : (2 * (j + 1) + 1) ! = (2 * j + 3) * ((2 * j + 2) * (2 * j + 1) !) := by
    rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 by ring, Nat.factorial_succ,
      show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ]
  rw [e1, Nat.factorial_succ j, Finset.prod_range_succ _ (j + 1)]
  push_cast
  have := fpos j; have := fpos (2 * j + 1); have := prod_pos' j
  field_simp
  ring

/-- b_{j+1} = b_j · k² / (4(j+1)(j+2)). -/
theorem bD_succ (k : ℝ) (j : ℕ) :
    bD k (j + 1) = bD k j * (k ^ 2 / (4 * ((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
  unfold bD
  rw [Nat.factorial_succ (j + 1), Nat.factorial_succ j]
  push_cast
  have := fpos j
  field_simp
  ring

theorem aN_ratio {k : ℝ} (hk : 0 ≤ k) (j : ℕ) : aN k (j + 1) ≤ k ^ 2 / 6 * aN k j := by
  rw [aN_succ, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (aN_nonneg hk j)
  apply div_le_div_of_nonneg_left (sq_nonneg k) (by norm_num)
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem bD_ratio {k : ℝ} (hk : 0 ≤ k) (j : ℕ) : bD k (j + 1) ≤ k ^ 2 / 8 * bD k j := by
  rw [bD_succ, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (bD_nonneg hk j)
  apply div_le_div_of_nonneg_left (sq_nonneg k) (by norm_num)
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- Geometric tail bound: if 0 ≤ f, f(j+1) ≤ r·f(j) with 0 ≤ r < 1, then f is summable and
∑_{j ≤ J} f j ≤ ∑' f ≤ ∑_{j ≤ J} f j + f J · r/(1-r). -/
theorem tail_bound (f : ℕ → ℝ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hf0 : ∀ j, 0 ≤ f j)
    (hrat : ∀ j, f (j + 1) ≤ r * f j) (J : ℕ) :
    Summable f ∧ ∑ j ∈ range (J + 1), f j ≤ ∑' j, f j ∧
      ∑' j, f j ≤ ∑ j ∈ range (J + 1), f j + f J * r / (1 - r) := by
  have hgeo : ∀ m i, f (m + i) ≤ f m * r ^ i := by
    intro m i
    induction i with
    | zero => simp
    | succ i ih =>
      calc f (m + (i + 1)) = f (m + i + 1) := by rw [Nat.add_assoc]
        _ ≤ r * f (m + i) := hrat _
        _ ≤ r * (f m * r ^ i) := mul_le_mul_of_nonneg_left ih hr0
        _ = f m * r ^ (i + 1) := by ring
  have hsg := summable_geometric_of_lt_one hr0 hr1
  have hs : Summable f :=
    Summable.of_nonneg_of_le hf0 (fun j => by simpa using hgeo 0 j) (hsg.mul_left (f 0))
  refine ⟨hs, hs.sum_le_tsum _ (fun i _ => hf0 i), ?_⟩
  rw [← hs.sum_add_tsum_nat_add (J + 1)]
  refine _root_.add_le_add le_rfl ?_
  have hb : ∀ i, f (i + (J + 1)) ≤ f J * r * r ^ i := by
    intro i
    have := hgeo J (i + 1)
    rw [show J + (i + 1) = i + (J + 1) by ring] at this
    calc f (i + (J + 1)) ≤ f J * r ^ (i + 1) := this
      _ = f J * r * r ^ i := by ring
  calc ∑' i, f (i + (J + 1)) ≤ ∑' i, f J * r * r ^ i :=
        Summable.tsum_le_tsum hb ((summable_nat_add_iff (J + 1)).mpr hs) (hsg.mul_left _)
    _ = f J * r / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- The partial sums and the geometric tail bound enclose N(k), for 0 ≤ k < 1. -/
theorem N_bounds {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (J : ℕ) :
    ∑ j ∈ range (J + 1), aN k j ≤ Nser k ∧
      Nser k ≤ ∑ j ∈ range (J + 1), aN k j + aN k J * (k ^ 2 / 6) / (1 - k ^ 2 / 6) := by
  have h := tail_bound (aN k) (k ^ 2 / 6) (by positivity) (by nlinarith) (aN_nonneg hk)
    (aN_ratio hk) J
  exact ⟨h.2.1, h.2.2⟩

theorem D_bounds {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (J : ℕ) :
    ∑ j ∈ range (J + 1), bD k j ≤ Dq k ∧
      Dq k ≤ ∑ j ∈ range (J + 1), bD k j + bD k J * (k ^ 2 / 8) / (1 - k ^ 2 / 8) := by
  have h := tail_bound (bD k) (k ^ 2 / 8) (by positivity) (by nlinarith) (bD_nonneg hk)
    (bD_ratio hk) J
  exact ⟨h.2.1, h.2.2⟩


/-! ### Terms at j = 0 -/

theorem aN_zero (k : ℝ) : aN k 0 = 2 * k / 3 := by
  simp [aN]
  ring

theorem bD_zero (k : ℝ) : bD k 0 = 1 / 2 := by
  simp [bD]

theorem bD_one (k : ℝ) : bD k 1 = 1 / 2 * (k ^ 2 / 8) := by
  have h := bD_succ k 0
  rw [bD_zero, Nat.zero_add] at h
  rw [h]; norm_num

theorem summable_aN {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) : Summable (aN k) :=
  (tail_bound (aN k) (k ^ 2 / 6) (by positivity) (by nlinarith) (aN_nonneg hk) (aN_ratio hk) 0).1

theorem summable_bD {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) : Summable (bD k) :=
  (tail_bound (bD k) (k ^ 2 / 8) (by positivity) (by nlinarith) (bD_nonneg hk) (bD_ratio hk) 0).1

/-! ### Step 6(c): N(k) < (4k/3)·Dq(k) -/

/-- Termwise: a_j(k) ≤ (4k/3)·b_j(k). -/
theorem aN_le {k : ℝ} (hk : 0 ≤ k) (j : ℕ) : aN k j ≤ 4 / 3 * k * bD k j := by
  induction j with
  | zero => rw [aN_zero, bD_zero]; linarith
  | succ j ih =>
    rw [aN_succ, bD_succ]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hb := bD_nonneg hk j
    have h1 : k ^ 2 / (2 * (2 * (j : ℝ) + 3) * ((j : ℝ) + 5 / 2)) ≤
        k ^ 2 / (4 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg k) (by positivity)
      nlinarith
    have h0 : 0 ≤ k ^ 2 / (2 * (2 * (j : ℝ) + 3) * ((j : ℝ) + 5 / 2)) := by positivity
    calc aN k j * (k ^ 2 / (2 * (2 * (j : ℝ) + 3) * ((j : ℝ) + 5 / 2)))
        ≤ 4 / 3 * k * bD k j * (k ^ 2 / (2 * (2 * (j : ℝ) + 3) * ((j : ℝ) + 5 / 2))) :=
          mul_le_mul_of_nonneg_right ih h0
      _ ≤ 4 / 3 * k * bD k j * (k ^ 2 / (4 * ((j : ℝ) + 1) * ((j : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 / 3 * k * (bD k j * (k ^ 2 / (4 * ((j : ℝ) + 1) * ((j : ℝ) + 2)))) := by ring

/-- Strictly at j = 1. -/
theorem aN_lt_one {k : ℝ} (hk : 0 < k) : aN k 1 < 4 / 3 * k * bD k 1 := by
  have ha : aN k 1 = 2 * k / 3 * (k ^ 2 / 15) := by
    have h := aN_succ k 0
    rw [aN_zero, Nat.zero_add] at h
    rw [h]; norm_num
  have hb : bD k 1 = 1 / 2 * (k ^ 2 / 8) := bD_one k
  rw [ha, hb]
  have : 0 < k ^ 3 := by positivity
  nlinarith

/-- **Step 6(c).** For 0 < k < 1: N(k) < (4k/3)·Dq(k); with T = N/(π·Dq) this is T(k) < 4k/(3π). -/
theorem N_lt_slope {k : ℝ} (hk : 0 < k) (hk1 : k < 1) : Nser k < 4 / 3 * k * Dq k := by
  unfold Nser Dq
  rw [← tsum_mul_left]
  exact Summable.tsum_lt_tsum (i := 1) (fun j => aN_le hk.le j) (aN_lt_one hk)
    (summable_aN hk.le hk1) ((summable_bD hk.le hk1).mul_left _)

/-! ### Step 6(b): N(k) ≥ 2k/3 and Dq(k) ≤ 1/2 + (cosh k - 1)/8 -/

theorem N_ge_first {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) : 2 * k / 3 ≤ Nser k := by
  have h := (N_bounds hk hk1 0).1
  simpa [aN_zero] using h

theorem Dq_ge_half {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) : 1 / 2 ≤ Dq k := by
  have h := (D_bounds hk hk1 0).1
  simpa [bD_zero] using h

/-- The j-th term of the cosh series, k^(2j)/(2j)!. -/
noncomputable def gC (k : ℝ) (j : ℕ) : ℝ := k ^ (2 * j) / ((2 * j) ! : ℝ)

theorem gC_succ (k : ℝ) (j : ℕ) :
    gC k (j + 1) = gC k j * (k ^ 2 / ((2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2))) := by
  unfold gC
  have e1 : (2 * (j + 1)) ! = (2 * j + 2) * ((2 * j + 1) * (2 * j) !) := by
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  rw [e1]
  push_cast
  have := fpos (2 * j)
  field_simp
  ring

theorem gC_nonneg {k : ℝ} (hk : 0 ≤ k) (j : ℕ) : 0 ≤ gC k j := by
  unfold gC; have := fpos (2 * j); positivity

/-- Termwise for every j ≥ 0: b_{j+1}(k) ≤ (1/8)·k^(2j+2)/(2j+2)!. -/
theorem bD_le_gC {k : ℝ} (hk : 0 ≤ k) (j : ℕ) : bD k (j + 1) ≤ gC k (j + 1) / 8 := by
  induction j with
  | zero =>
    have hb : bD k 1 = 1 / 2 * (k ^ 2 / 8) := bD_one k
    have hg : gC k 1 = k ^ 2 / 2 := by simp [gC]
    rw [show (0 : ℕ) + 1 = 1 from rfl, hb, hg]; linarith
  | succ j ih =>
    rw [bD_succ k (j + 1), gC_succ k (j + 1)]
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hg := gC_nonneg hk (j + 1)
    have hb := bD_nonneg hk (j + 1)
    have h1 : k ^ 2 / (4 * ((j : ℝ) + 1 + 1) * ((j : ℝ) + 1 + 2)) ≤
        k ^ 2 / ((2 * ((j : ℝ) + 1) + 1) * (2 * ((j : ℝ) + 1) + 2)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg k) (by positivity)
      nlinarith
    have h0 : 0 ≤ k ^ 2 / (4 * ((j : ℝ) + 1 + 1) * ((j : ℝ) + 1 + 2)) := by positivity
    calc bD k (j + 1) * (k ^ 2 / (4 * ((j : ℝ) + 1 + 1) * ((j : ℝ) + 1 + 2)))
        ≤ gC k (j + 1) / 8 * (k ^ 2 / (4 * ((j : ℝ) + 1 + 1) * ((j : ℝ) + 1 + 2))) :=
          mul_le_mul_of_nonneg_right ih h0
      _ ≤ gC k (j + 1) / 8 * (k ^ 2 / ((2 * ((j : ℝ) + 1) + 1) * (2 * ((j : ℝ) + 1) + 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = gC k (j + 1) * (k ^ 2 / ((2 * ((j : ℝ) + 1) + 1) * (2 * ((j : ℝ) + 1) + 2))) / 8 := by
          ring

/-- **Step 6(b), denominator.** For 0 ≤ k < 1: Dq(k) ≤ 1/2 + (cosh k - 1)/8, that is
π·Dq(k) ≤ (π/2)(1 + (cosh k - 1)/4). -/
theorem Dq_le_cosh {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) : Dq k ≤ 1 / 2 + (Real.cosh k - 1) / 8 := by
  have hsD := summable_bD hk hk1
  have hC : HasSum (gC k) (Real.cosh k) := Real.hasSum_cosh k
  have hD0 : Dq k = bD k 0 + ∑' j, bD k (j + 1) := hsD.tsum_eq_zero_add
  have hC0 : Real.cosh k = gC k 0 + ∑' j, gC k (j + 1) := by
    rw [← hC.tsum_eq]; exact hC.summable.tsum_eq_zero_add
  have hg0 : gC k 0 = 1 := by simp [gC]
  have hle : ∑' j, bD k (j + 1) ≤ ∑' j, gC k (j + 1) / 8 :=
    Summable.tsum_le_tsum (fun j => bD_le_gC hk j) ((summable_nat_add_iff 1).mpr hsD)
      (((summable_nat_add_iff 1).mpr hC.summable).div_const 8)
  rw [tsum_div_const] at hle
  rw [hD0, bD_zero]
  have : ∑' j, gC k (j + 1) = Real.cosh k - 1 := by linarith
  linarith

/-! ### Line (B) and the sign at b = 2/(5(D-1)) -/

theorem cosh_fifth_lt : Real.cosh (1 / 5) < 50 / 49 := by
  have h1 := Real.cosh_le_exp_half_sq (1 / 5)
  have h2 := Real.exp_bound_div_one_sub_of_interval' (x := (1 / 5 : ℝ) ^ 2 / 2) (by norm_num)
    (by norm_num)
  have h3 : (1 : ℝ) / (1 - (1 / 5) ^ 2 / 2) = 50 / 49 := by norm_num
  linarith

/-- **Line (B)** of beta0_exact.py: (12/5)·(4/(3π)) > 1 + (cosh(1/5) - 1)/4. -/
theorem line_B : 1 + (Real.cosh (1 / 5) - 1) / 4 < 12 / 5 * (4 / (3 * Real.pi)) := by
  have hc := cosh_fifth_lt
  have hpi := Real.pi_lt_d4
  have hpos := Real.pi_pos
  have e : (12 : ℝ) / 5 * (4 / (3 * Real.pi)) = 48 / 5 / (3 * Real.pi) := by ring
  rw [e, lt_div_iff₀ (by positivity)]
  nlinarith

/-- **Sign at b = 2/(5(D-1)).** For real D ≥ 3: π·Dq(b) < 6(D-1)·N(b), that is 6(D-1)·T(b) > 1. -/
theorem root_side (D : ℝ) (hD : 3 ≤ D) :
    Real.pi * Dq (2 / (5 * (D - 1))) < 6 * (D - 1) * Nser (2 / (5 * (D - 1))) := by
  have hD1 : 0 < D - 1 := by linarith
  set b : ℝ := 2 / (5 * (D - 1)) with hb
  have hb0 : 0 < b := by positivity
  have hb5 : b ≤ 1 / 5 := by
    rw [hb, div_le_iff₀ (by positivity)]; linarith
  have hb1 : b < 1 := by linarith
  have hN := N_ge_first hb0.le hb1
  have hDq := Dq_le_cosh hb0.le hb1
  have hcosh : Real.cosh b ≤ Real.cosh (1 / 5) := by
    rw [Real.cosh_le_cosh, abs_of_pos hb0, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)]; exact hb5
  have hB := line_B
  have hpos := Real.pi_pos
  have e : (12 : ℝ) / 5 * (4 / (3 * Real.pi)) = 16 / 5 / Real.pi := by
    field_simp; ring
  rw [e, lt_div_iff₀ hpos] at hB
  have hDb : (D - 1) * b = 2 / 5 := by
    rw [hb]; field_simp
  have h1 : Real.pi * Dq b ≤ Real.pi * (1 / 2 + (Real.cosh (1 / 5) - 1) / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have h2 : 6 * (D - 1) * (2 * b / 3) ≤ 6 * (D - 1) * Nser b :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  nlinarith

/-- **Lower bound for a point where the sign is ≥ 0.** If D > 1, 0 < k < 1 and
π·Dq(k) ≤ 6(D-1)·N(k), then k > π/(8(D-1)). -/
theorem root_gt (D k : ℝ) (hD : 1 < D) (hk : 0 < k) (hk1 : k < 1)
    (h : Real.pi * Dq k ≤ 6 * (D - 1) * Nser k) : Real.pi / (8 * (D - 1)) < k := by
  have hD1 : 0 < D - 1 := by linarith
  have hN := N_lt_slope hk hk1
  have hDq := Dq_ge_half hk.le hk1
  have hDqpos : 0 < Dq k := by linarith
  rw [div_lt_iff₀ (by positivity)]
  have h3 : 6 * (D - 1) * Nser k < 6 * (D - 1) * (4 / 3 * k * Dq k) :=
    mul_lt_mul_of_pos_left hN (by positivity)
  have h4 : Real.pi * Dq k < k * (8 * (D - 1)) * Dq k := by nlinarith
  exact lt_of_mul_lt_mul_right h4 hDqpos.le

/-! ### Signs at the endpoints of the enclosures of β₀(D) -/

/-- If c·(partial sum of N to j = 4, plus its tail bound) < p·(partial sum of Dq to j = 4)
with p ≤ π, then c·N(k) < π·Dq(k). -/
theorem below_of_rational {k c p : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hc : 0 ≤ c) (hp : p ≤ Real.pi)
    (h : c * (∑ j ∈ range 5, aN k j + aN k 4 * (k ^ 2 / 6) / (1 - k ^ 2 / 6)) <
      p * ∑ j ∈ range 5, bD k j) : c * Nser k < Real.pi * Dq k := by
  obtain ⟨-, hN⟩ := N_bounds hk hk1 4
  obtain ⟨hD, -⟩ := D_bounds hk hk1 4
  have hD0 : 0 ≤ ∑ j ∈ range 5, bD k j := Finset.sum_nonneg fun j _ => bD_nonneg hk j
  calc c * Nser k
      ≤ c * (∑ j ∈ range 5, aN k j + aN k 4 * (k ^ 2 / 6) / (1 - k ^ 2 / 6)) :=
        mul_le_mul_of_nonneg_left hN hc
    _ < p * ∑ j ∈ range 5, bD k j := h
    _ ≤ Real.pi * ∑ j ∈ range 5, bD k j := mul_le_mul_of_nonneg_right hp hD0
    _ ≤ Real.pi * Dq k := mul_le_mul_of_nonneg_left hD Real.pi_pos.le

/-- If p·(partial sum of Dq to j = 4, plus its tail bound) < c·(partial sum of N to j = 4)
with π ≤ p, then π·Dq(k) < c·N(k). -/
theorem above_of_rational {k c p : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hc : 0 ≤ c) (hp : Real.pi ≤ p)
    (h : p * (∑ j ∈ range 5, bD k j + bD k 4 * (k ^ 2 / 8) / (1 - k ^ 2 / 8)) <
      c * ∑ j ∈ range 5, aN k j) : Real.pi * Dq k < c * Nser k := by
  obtain ⟨hN, -⟩ := N_bounds hk hk1 4
  obtain ⟨hD1, hD⟩ := D_bounds hk hk1 4
  have hD0 : 0 ≤ Dq k := le_trans (Finset.sum_nonneg fun j _ => bD_nonneg hk j) hD1
  have hp0 : 0 ≤ p := le_trans Real.pi_pos.le hp
  calc Real.pi * Dq k ≤ p * Dq k := mul_le_mul_of_nonneg_right hp hD0
    _ ≤ p * (∑ j ∈ range 5, bD k j + bD k 4 * (k ^ 2 / 8) / (1 - k ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left hD hp0
    _ < c * ∑ j ∈ range 5, aN k j := h
    _ ≤ c * Nser k := mul_le_mul_of_nonneg_left hN hc

theorem pi_lo : (3.1415926535 : ℝ) ≤ Real.pi := by
  have := Real.pi_gt_d20; linarith

theorem pi_hi : Real.pi ≤ (3.1415926536 : ℝ) := by
  have := Real.pi_lt_d20; linarith

/-- **D = 3, below.** 12·N(k) < π·Dq(k) at k = 0.1967929: 6(D-1)·T < 1 there. -/
theorem below_3 : 12 * Nser (1967929 / 10000000) < Real.pi * Dq (1967929 / 10000000) := by
  refine below_of_rational (by norm_num) (by norm_num) (by norm_num) pi_lo ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 3, above.** π·Dq(k) < 12·N(k) at k = 0.1967930: 6(D-1)·T > 1 there. -/
theorem above_3 : Real.pi * Dq (1967930 / 10000000) < 12 * Nser (1967930 / 10000000) := by
  refine above_of_rational (by norm_num) (by norm_num) (by norm_num) pi_hi ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 4, below.** 18·N(k) < π·Dq(k) at k = 0.1310307: 6(D-1)·T < 1 there. -/
theorem below_4 : 18 * Nser (1310307 / 10000000) < Real.pi * Dq (1310307 / 10000000) := by
  refine below_of_rational (by norm_num) (by norm_num) (by norm_num) pi_lo ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 4, above.** π·Dq(k) < 18·N(k) at k = 0.1310308: 6(D-1)·T > 1 there. -/
theorem above_4 : Real.pi * Dq (1310308 / 10000000) < 18 * Nser (1310308 / 10000000) := by
  refine above_of_rational (by norm_num) (by norm_num) (by norm_num) pi_hi ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 5, below.** 24·N(k) < π·Dq(k) at k = 0.0982300: 6(D-1)·T < 1 there. -/
theorem below_5 : 24 * Nser (982300 / 10000000) < Real.pi * Dq (982300 / 10000000) := by
  refine below_of_rational (by norm_num) (by norm_num) (by norm_num) pi_lo ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 5, above.** π·Dq(k) < 24·N(k) at k = 0.0982301: 6(D-1)·T > 1 there. -/
theorem above_5 : Real.pi * Dq (982301 / 10000000) < 24 * Nser (982301 / 10000000) := by
  refine above_of_rational (by norm_num) (by norm_num) (by norm_num) pi_hi ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 6, below.** 30·N(k) < π·Dq(k) at k = 0.0785680: 6(D-1)·T < 1 there. -/
theorem below_6 : 30 * Nser (785680 / 10000000) < Real.pi * Dq (785680 / 10000000) := by
  refine below_of_rational (by norm_num) (by norm_num) (by norm_num) pi_lo ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 6, above.** π·Dq(k) < 30·N(k) at k = 0.0785681: 6(D-1)·T > 1 there. -/
theorem above_6 : Real.pi * Dq (785681 / 10000000) < 30 * Nser (785681 / 10000000) := by
  refine above_of_rational (by norm_num) (by norm_num) (by norm_num) pi_hi ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 10, below.** 54·N(k) < π·Dq(k) at k = 0.0436380: 6(D-1)·T < 1 there. -/
theorem below_10 : 54 * Nser (436380 / 10000000) < Real.pi * Dq (436380 / 10000000) := by
  refine below_of_rational (by norm_num) (by norm_num) (by norm_num) pi_lo ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 10, above.** π·Dq(k) < 54·N(k) at k = 0.0436381: 6(D-1)·T > 1 there. -/
theorem above_10 : Real.pi * Dq (436381 / 10000000) < 54 * Nser (436381 / 10000000) := by
  refine above_of_rational (by norm_num) (by norm_num) (by norm_num) pi_hi ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 100, below.** 594·N(k) < π·Dq(k) at k = 0.0039666: 6(D-1)·T < 1 there. -/
theorem below_100 : 594 * Nser (39666 / 10000000) < Real.pi * Dq (39666 / 10000000) := by
  refine below_of_rational (by norm_num) (by norm_num) (by norm_num) pi_lo ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **D = 100, above.** π·Dq(k) < 594·N(k) at k = 0.0039667: 6(D-1)·T > 1 there. -/
theorem above_100 : Real.pi * Dq (39667 / 10000000) < 594 * Nser (39667 / 10000000) := by
  refine above_of_rational (by norm_num) (by norm_num) (by norm_num) pi_hi ?_
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

end YMThreshold

import Mathlib

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, Session 4, 21 Nov 2026 (route lead B).
The arithmetic of the exact endpoint certificate failure_side_antipodal_TV.py (antipodal pair, 4D SU(2)
Wilson, single-link Dobrushin row sum >= 18·TV with TV = N(k)/D(k), k = β), lattice only.

FORMALIZED. The two series of the certificate are DEFINED here by their terms:
  N(k) = ∑' j, a_j,  a_j = k^(2j+1)·j! / ((2j+1)!·∏_{i=0..j}(i+3/2));
  D(k)/π = ∑' j, b_j,  b_j = k^(2j) / (2·4^j·j!·(j+1)!).
* `aN_succ`, `bD_succ`: the exact term ratios a_{j+1}/a_j = k²/(2(2j+3)(j+5/2)), b_{j+1}/b_j = k²/(4(j+1)(j+2)).
* `tail_bound`, `N_bounds`, `D_bounds`: for 0 ≤ k < 1 the series converge and, for every J, the partial sum
  up to J and the partial sum plus (last term)·r/(1-r), r = k²/6 resp. k²/8, enclose them (the tail bounds
  are proved, not assumed).
* `rational_below`, `rational_above`: the two explicit rational inequalities (J = 4, checked by norm_num).
* `endpoint_below`: 18·N(k) < π·(D(k)/π) at k = 13103/100000, i.e. 18·N/D < 1 at β = 0.13103.
  `endpoint_above`: π·(D(k)/π) < 18·N(k) at k = 131031/1000000, i.e. 18·N/D > 1 at β = 0.131031.
  π is Mathlib's Real.pi with its proved bounds 3.141592 < π < 3.141593 (the script uses 11 digits; the
  margins, about 5.7e-6 and 1.6e-6 relative, need far less). The script sums to J = 12; J = 4 suffices.
* `Dq_eq_I1`: k·(D(k)/π) = I₁(k), with I₁ the series of YMBesselSeries (so D(k) = π·I₁(k)/k).

NOT formalized: that N(k) = ∫₀¹ 2 sinh(kx)√(1-x²) dx and D(k) = ∫₋₁¹ e^(kx)√(1-x²) dx (termwise Beta
integration), that TV(vMF(kv), vMF(-kv)) = N/D, that N/D = L₁/I₁ (Struve over Bessel), the antipodal
configuration and the bound row sum >= 18·TV, monotonicity of TV in k, the β = 0.13104 and β = π/24
lines of the script, and Dobrushin's theorem.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Nat Finset

namespace YMEndpoint

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

/-- I₁(κ) := ∑' k, (κ/2)^(2k+1) / (k!·(k+1)!) (the same series definition as in YMBesselSeries). -/
noncomputable def I1 (κ : ℝ) : ℝ := ∑' k : ℕ, (κ / 2) ^ (2 * k + 1) / ((k ! : ℝ) * ((k + 1) ! : ℝ))

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

/-- D(k)/π = I₁(k)/k, in the form k · (D(k)/π) = I₁(k). -/
theorem Dq_eq_I1 (k : ℝ) : k * Dq k = I1 k := by
  unfold Dq I1
  rw [← tsum_mul_left]
  congr 1
  funext j
  unfold bD
  have := fpos j; have := fpos (j + 1)
  have e : (4 : ℝ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
  rw [e, div_pow, pow_succ]
  field_simp
  ring

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

/-- The rational inequality at β = 0.13103 (J = 4, π > 3.141592):
18 · (upper bound for N) < 3.141592 · (lower bound for D/π). -/
theorem rational_below :
    18 * (∑ j ∈ range 5, aN (13103 / 100000) j +
      aN (13103 / 100000) 4 * ((13103 / 100000) ^ 2 / 6) / (1 - (13103 / 100000) ^ 2 / 6)) <
    3.141592 * ∑ j ∈ range 5, bD (13103 / 100000) j := by
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- The rational inequality at β = 0.131031 (J = 4, π < 3.141593):
3.141593 · (upper bound for D/π) < 18 · (lower bound for N). -/
theorem rational_above :
    3.141593 * (∑ j ∈ range 5, bD (131031 / 1000000) j +
      bD (131031 / 1000000) 4 * ((131031 / 1000000) ^ 2 / 8) / (1 - (131031 / 1000000) ^ 2 / 8)) <
    18 * ∑ j ∈ range 5, aN (131031 / 1000000) j := by
  simp only [aN, bD, Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, Nat.factorial]
  norm_num

/-- **Endpoint, below.** At k = β = 0.13103: 18·N(k) < π·(D(k)/π), i.e. 18·N/D < 1. -/
theorem endpoint_below : 18 * Nser (13103 / 100000) < Real.pi * Dq (13103 / 100000) := by
  obtain ⟨-, hN⟩ := N_bounds (k := 13103 / 100000) (by norm_num) (by norm_num) 4
  obtain ⟨hD, -⟩ := D_bounds (k := 13103 / 100000) (by norm_num) (by norm_num) 4
  have hr := rational_below
  have hpi := Real.pi_gt_d6
  have hD0 : 0 ≤ ∑ j ∈ range 5, bD (13103 / 100000) j :=
    Finset.sum_nonneg fun j _ => bD_nonneg (by norm_num) j
  calc 18 * Nser (13103 / 100000) < 3.141592 * ∑ j ∈ range 5, bD (13103 / 100000) j := by
        linarith
    _ ≤ Real.pi * ∑ j ∈ range 5, bD (13103 / 100000) j :=
        mul_le_mul_of_nonneg_right hpi.le hD0
    _ ≤ Real.pi * Dq (13103 / 100000) := mul_le_mul_of_nonneg_left hD Real.pi_pos.le

/-- **Endpoint, above.** At k = β = 0.131031: π·(D(k)/π) < 18·N(k), i.e. 18·N/D > 1. -/
theorem endpoint_above : Real.pi * Dq (131031 / 1000000) < 18 * Nser (131031 / 1000000) := by
  obtain ⟨hN, -⟩ := N_bounds (k := 131031 / 1000000) (by norm_num) (by norm_num) 4
  obtain ⟨-, hD⟩ := D_bounds (k := 131031 / 1000000) (by norm_num) (by norm_num) 4
  have hr := rational_above
  have hpi := Real.pi_lt_d6
  have hD0 : 0 ≤ Dq (131031 / 1000000) := le_trans
    (Finset.sum_nonneg fun j _ => bD_nonneg (by norm_num) j) (D_bounds (k := 131031 / 1000000)
      (by norm_num) (by norm_num) 4).1
  calc Real.pi * Dq (131031 / 1000000) ≤ 3.141593 * Dq (131031 / 1000000) :=
        mul_le_mul_of_nonneg_right hpi.le hD0
    _ < 18 * Nser (131031 / 1000000) := by nlinarith

end YMEndpoint

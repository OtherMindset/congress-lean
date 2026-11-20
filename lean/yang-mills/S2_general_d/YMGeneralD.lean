/-
Yang-Mills table, Long Table (othermindset.com). Claude council, Session 2, 20 Nov 2026.
Leg L4 (general dimension) of the single-link Dobrushin result for SU(2) Wilson lattice gauge theory,
weight exp((beta/2) sum_p tr U_p) on Z^d, each unoriented plaquette counted once. Arithmetic core only.

In Z^d each link lies in 2(d-1) plaquettes, with 6(d-1) distinct other links; the one-link conditional
law is von Mises-Fisher on S^3 with kappa = beta |S_e| <= 2(d-1) beta; and C_ef <= beta * M, where M
bounds E_kappa |<U - EU, q>| over the kappa that occur. The d = 4 certificates bound M on kappa in [0, pi/4]
(by 4/(3pi) + 1e-8, #mwo53bqy-nzojc8; by 4/(3pi) + 0.0005, two implementations). Since M(0, q) = 4/(3pi),
any such bound m satisfies m >= 4/(3pi). The theorem below checks that then, for every d >= 2 and
0 <= beta < 1/(6(d-1) m):
  (i)  the row sum 6(d-1) * beta * m is < 1, and
  (ii) the largest kappa, 2(d-1) beta, is <= pi/4, so the d = 4 certificate covers the kappa that occur.
Conclusion (i) is the hypothesis multiplied through; (ii) is the content. So, given the unformalized steps
below, the same certificate gives single-link Dobrushin for beta < 1/(6(d-1) m) in every dimension d >= 2;
the threshold depends on d (it is about pi/(8(d-1))), so there is no beta uniform in d.

NOT formalized: the counting of plaquettes and neighbours, the von Mises-Fisher reduction, the influence
bound C_ef <= beta M, the certificates themselves, and Dobrushin's theorem.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import Mathlib

theorem general_d_row_sum (d : ℕ) (hd : 2 ≤ d) (m β : ℝ)
    (hm : 4 / (3 * Real.pi) ≤ m) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / (6 * ((d : ℝ) - 1) * m)) :
    6 * ((d : ℝ) - 1) * β * m < 1 ∧ 2 * ((d : ℝ) - 1) * β ≤ Real.pi / 4 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hpos : 0 < 6 * ((d : ℝ) - 1) * m := by positivity
  have hrow : 6 * ((d : ℝ) - 1) * β * m < 1 := by
    rw [lt_div_iff₀ hpos] at hβ
    nlinarith [hβ]
  refine ⟨hrow, ?_⟩
  -- 4/(3 pi) <= m gives 4 <= 3 pi m
  have h4 : 4 ≤ 3 * Real.pi * m := by
    rw [div_le_iff₀ (by positivity)] at hm
    linarith
  -- 2(d-1) beta * (3m) < 1, hence 2(d-1) beta < 1/(3m) <= pi/4
  have hk : 2 * ((d : ℝ) - 1) * β * (3 * m) < 1 := by nlinarith [hrow]
  have hkp : 0 ≤ 2 * ((d : ℝ) - 1) * β := by positivity
  nlinarith [hk, h4, hkp, hm0, hpi]

/-- d = 4 with the certified bound m = 4/(3 pi) + 1/10^8. -/
theorem d4_certified (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / (18 * (4 / (3 * Real.pi) + 1 / 10 ^ 8))) :
    18 * β * (4 / (3 * Real.pi) + 1 / 10 ^ 8) < 1 ∧ 6 * β ≤ Real.pi / 4 := by
  have h := general_d_row_sum 4 (by norm_num) (4 / (3 * Real.pi) + 1 / 10 ^ 8) β
    (by have : (0:ℝ) < 1 / 10 ^ 8 := by positivity
        linarith) hβ0 (by norm_num at hβ ⊢; linarith)
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

#print axioms general_d_row_sum
#print axioms d4_certified

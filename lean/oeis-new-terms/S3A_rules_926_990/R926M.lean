import LongTable.P_mwnlksna_88ktqn
import LongTable.R926chunk
/-
  Instance LC_R926 of the VN library (Rules 926 and 990), Mathlib file: short proofs from LT2D.vn_count_rec_chunked and
  LT2D.vn_twin_count_chunked / LT2D.vn_twin_chunked (VN_M4, VN_M3). CHECK REC is VN_K9's extended check (annihilator
  (x-1)(x-2)(x-4)(x+1)).
-/
namespace LT2D

/-- Rule 926: for every n >= 0, 3 * (number of ON cells of Rule 926 inside [-g, g]^2 at stage g = 2^n - 1) = 4 * 4^n - 1,
i.e. the count is (4^(n+1) - 1)/3 = A002450(n+1). -/
theorem r926_count (n : Nat) : 3 * (onCount 926 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 1 := by
  have h := vn_count_rec_chunked VN.LC_R926.tab 926 959 [-8, 6, 7, -6] 3 4 (0) (-1) 0 2 VN.LC_R926.sls VN.LC_R926.ok2 VN.LC_R926.ok1s VN.LC_R926.ok1 VN.LC_R926.okr n (by omega)
  first | linarith | (ring_nf at h ⊢; linarith)

/-- Rule 990 has exactly the space-time diagram of Rule 926 (they differ only at index c = 0, k = 3, which Rule 926 never uses). -/
theorem r990_caState_eq_926 : caState 990 = caState 926 :=
  vn_twin_chunked VN.LC_R926.tab 926 990 959 VN.LC_R926.sls VN.LC_R926.ok2 VN.LC_R926.ok1s VN.LC_R926.ok1 VN.LC_R926.tw990

/-- Rule 990: the same count as Rule 926 at every stage. -/
theorem r990_count_eq_926 (g : Nat) : onCount 990 g = onCount 926 g :=
  vn_twin_count_chunked VN.LC_R926.tab 926 990 959 VN.LC_R926.sls VN.LC_R926.ok2 VN.LC_R926.ok1s VN.LC_R926.ok1 VN.LC_R926.tw990 g

/-- Rule 990: for every n >= 0, 3 * onCount 990 (2^n - 1) = 4 * 4^n - 1. -/
theorem r990_count (n : Nat) : 3 * (onCount 990 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 1 := by
  rw [r990_count_eq_926]
  exact r926_count n

end LT2D

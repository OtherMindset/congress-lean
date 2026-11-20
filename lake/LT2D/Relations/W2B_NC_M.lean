import LT2D.Groups.W2A1.M
import LT2D.Groups.W2A2.M
import LT2D.Groups.W2A3.M
/-
  W2B_NC_M (Chair B, 19 Nov 2026, hand-written): OEIS statements of Robert Price's comments (and one Blomberg conjecture) about the
  stage 2^n - 1 counts of classes certified by Chair A, each derived in a few lines from Chair A's class count theorems
  LT2D.r773_count (W2A3_M), LT2D.r510_count, LT2D.r513_count, LT2D.r62_count (W2A2_M) and LT2D.r7_count (W2A1_M). Entry text and
  read ids from S/targets/W5/new_conjectures.md (Chair C). No equal-count theorem for other rules of a class: no entry names them.
-/
namespace LT2D

/-- A165665 (Rule 773): %C The number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by "Rule 773", based on the 5-celled von Neumann neighborhood. - Robert Price, May 23 2016
The entry's %N is a(n) = (3*2^n - 2) * 2^n (offset 0, a(0) = 1); the comment states no range, so the statement is for every n >= 0.
From LT2D.r773_count (3*4^n - 2*2^n). -/
theorem a165665_r773_formula (n : Nat) :
    (onCount 773 (2 ^ n - 1) : Int) = (3 * 2 ^ n - 2) * 2 ^ n := by
  have h := r773_count n
  have h4 : (4 : Int) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4] at h
  linarith

/-- A092440 (Rule 510): %C Also, the number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by "Rule 510", based on the 5-celled von Neumann neighborhood. - Robert Price, May 04 2016
The entry's %N is a(n) = 2^(2*n+1) - 2^(n+1) + 1 (offset 0); the comment states no range: every n >= 0. From LT2D.r510_count. -/
theorem a092440_r510_formula (n : Nat) :
    (onCount 510 (2 ^ n - 1) : Int) = 2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1 := by
  have h := r510_count n
  have e1 : (2 : Int) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_succ, pow_mul]; norm_num; ring
  have e2 : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [e1, e2]
  linarith

/-- A059153 (Rule 513): %C Also, the number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by "Rule 513", based on the 5-celled von Neumann neighborhood. - Robert Price, May 04 2016
INDEX SHIFT: the entry's %N is a(n) = 2^(n+2)*(2^(n+1)-1) with offset 0, 1 (a(0) = 4, a(1) = 24, ...). As printed, with no shift, the
comment is false: at stage 2^0 - 1 = 0 the count is 1 (a(0) = 4) and at stage 2^1 - 1 = 1 it is 4 (a(1) = 24). The true statement is
count(2^n - 1) = a(n - 1) for n >= 1; stated here shifted, with the entry's sequence index m = n - 1 >= 0: the number of ON cells at
stage 2^(m+1) - 1 equals 2^(m+2)*(2^(m+1)-1). From LT2D.r513_count at m + 1. -/
theorem a059153_r513_formula_shifted (m : Nat) :
    (onCount 513 (2 ^ (m + 1) - 1) : Int) = 2 ^ (m + 2) * (2 ^ (m + 1) - 1) := by
  have h := r513_count (m + 1) (by omega)
  have e1 : (2 : Int) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
  have e2 : (4 : Int) ^ (m + 1) = (2 ^ (m + 1)) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e2] at h
  rw [e1]
  linarith

/-- A060867 (Rule 7): %C Apparently (with offset 0) also the number of active cells at state 2^n-1 of the automaton defined by "Rule 7". - Robert Price, Apr 12 2016
The entry's %N is a(n) = (2^n - 1)^2 with offset 1; "with offset 0" is read as the list starting at n = 0, i.e. the count at stage
2^n - 1 equals (2^(n+1) - 1)^2 for every n >= 0 (1, 9, 49, 225, ...). A literal (2^n - 1)^2 would be false (n = 0 gives 0). From
LT2D.r7_count. -/
theorem a060867_r7_formula (n : Nat) :
    (onCount 7 (2 ^ n - 1) : Int) = (2 ^ (n + 1) - 1) ^ 2 := by
  have h := r7_count n
  have e1 : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by ring
  have e2 : (4 : Int) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e2] at h
  rw [e1]
  linarith

/-- A270080 (Rule 62): %F Conjecture: a(n) = 4^n + 2*2^n - 8, n>2. - Lars Blomberg, Apr 20 2016
For every n >= 3. From LT2D.r62_count (the class theorem of Rule 62 has the same statement). -/
theorem a270080_formula (n : Nat) (hn : 3 ≤ n) :
    (onCount 62 (2 ^ n - 1) : Int) = 4 ^ n + 2 * 2 ^ n - 8 :=
  r62_count n hn

end LT2D
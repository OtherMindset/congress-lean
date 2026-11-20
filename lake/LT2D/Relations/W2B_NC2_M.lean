import LT2D.Groups.W2A2.M
import LT2D.Instances.LW1_R598.M
/-
  W2B_NC2_M (Chair B, 19 Nov 2026, hand-written): two more statements of Robert Price's comments, derived in a few lines from class
  count theorems: LT2D.r737_count (W2A2_M, Chair A) for A060867's Rule 737 comment, and LT2D.r598_count (LW1_R598_M, the Leader's W1
  test instance with the extended CHECK REC) for A002450's Rule 598 comment. Entry text and read ids from
  S/targets/W5/new_conjectures.md (Chair C, NC4b and NC6). No equal-count theorem for the other rules of the classes: no entry names them.
-/
namespace LT2D

/-- A060867 (Rule 737): %C Except for a(1)=4, the number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by "Rule 737", based on the 5-celled von Neumann neighborhood. - Robert Price, May 23 2016
Part 1 of 2 (the formula): the entry's %N is a(n) = (2^n - 1)^2 with offset 1. The comment's index is read 0-based, as in the same entry's Rule 7 comment "with offset 0" (the only reading in which the comment holds with a(1)=4 as its only exception: with the entry's offset 1 it fails from n = 2 on, where the count at stage 2^2 - 1 = 3 is 49 and a(2) = 9): the count at stage 2^n - 1 equals (2^(n+1) - 1)^2 for every n except n = 1. From LT2D.r737_count (n >= 2) and the value 1 at n = 0 (kernel evaluation). -/
theorem a060867_r737_formula (n : Nat) (hn : n ≠ 1) :
    (onCount 737 (2 ^ n - 1) : Int) = (2 ^ (n + 1) - 1) ^ 2 := by
  rcases n with _ | _ | n
  · decide +kernel
  · exact absurd rfl hn
  · have h := r737_count (n + 2) (by omega)
    have e1 : (2 : Int) ^ (n + 2 + 1) = 2 * 2 ^ (n + 2) := by ring
    have e2 : (4 : Int) ^ (n + 2) = (2 ^ (n + 2)) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e2] at h
    rw [e1]
    linarith

/-- A060867 (Rule 737): %C Except for a(1)=4, the number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by "Rule 737", based on the 5-celled von Neumann neighborhood. - Robert Price, May 23 2016
Part 2 of 2 (the exception): at n = 1 (stage 2^1 - 1 = 1) the count is 4, not (2^2 - 1)^2 = 9. Kernel evaluation. -/
theorem a060867_r737_exception : onCount 737 (2 ^ 1 - 1) = 4 := by decide +kernel

/-- A002450 (Rule 598): %C Number of active (ON, black) cells at stage 2^n - 1 of the two-dimensional cellular automaton defined by "Rule 598", based on the 5-celled von Neumann neighborhood. - Robert Price, May 16 2016
INDEX SHIFT: the entry's %N is a(n) = (4^n - 1)/3 with offset 0, 3 (a(0) = 0, a(1) = 1, a(2) = 5, ...). As printed, with no shift, the comment is false at every n (the counts at stages 2^n - 1 are 1, 5, 21, 85, ...). The true statement is count(2^n - 1) = a(n + 1) = (4^(n+1) - 1)/3 for every n >= 0, stated times 3 because the entry divides by 3: 3 * count = 4^(n+1) - 1. From LT2D.r598_count (3 * count = 4 * 4^n - 1). -/
theorem a002450_r598_formula_shifted (n : Nat) :
    3 * (onCount 598 (2 ^ n - 1) : Int) = 4 ^ (n + 1) - 1 := by
  have h := r598_count n
  have e : (4 : Int) ^ (n + 1) = 4 * 4 ^ n := by ring
  rw [e]
  linarith

end LT2D
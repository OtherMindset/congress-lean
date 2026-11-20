import Mathlib
import LT2D.Early.A271061_Part1
/-
  A271061: Rule 261 and the 35 rules of the entry's comment. Part 3 of 3: class C (16 rules).
  Definitions and lemmas are in part 1 (namespace LT2D); each theorem below says that the rule has
  the same count as Rule 261 at stage 2^n - 1, for every n. A finite check by kernel `decide`
  (the rule's bits and the stages 1 and 2) gives all odd stages ON-except-the-origin.
-/
namespace LT2D

/-! Class C: Rules 645 .. 765 (bits 0, 2, 7, 9 set; bits 1, 8 clear; bits 3-6 free): ON-except-the-origin from stage 1 on. -/
theorem a271061_rule645 (n : Nat) : onCount 645 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule653 (n : Nat) : onCount 653 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule661 (n : Nat) : onCount 661 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule669 (n : Nat) : onCount 669 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule677 (n : Nat) : onCount 677 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule685 (n : Nat) : onCount 685 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule693 (n : Nat) : onCount 693 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule701 (n : Nat) : onCount 701 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule709 (n : Nat) : onCount 709 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule717 (n : Nat) : onCount 717 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule725 (n : Nat) : onCount 725 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule733 (n : Nat) : onCount 733 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule741 (n : Nat) : onCount 741 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule749 (n : Nat) : onCount 749 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule757 (n : Nat) : onCount 757 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n
theorem a271061_rule765 (n : Nat) : onCount 765 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddC (by decide)) odd261 n

end LT2D
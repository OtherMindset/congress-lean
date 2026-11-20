import Mathlib
import LT2D.Early.A271061_Part1
/-
  A271061: Rule 261 and the 35 rules of the entry's comment. Part 2 of 3: classes A and B (19 rules).
  Definitions and lemmas are in part 1 (namespace LT2D); each theorem below says that the rule has
  the same count as Rule 261 at stage 2^n - 1, for every n. A finite check by kernel `decide`
  (the rule's bits and the stages 1 to 3) gives all odd stages ON-except-the-origin.
-/
namespace LT2D

/-! Class A: Rules 269 .. 381 (bits 0, 2, 8 set; bits 1, 7, 9 clear; bits 3-6 free): stage 2 is the seed again. -/
theorem a271061_rule269 (n : Nat) : onCount 269 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule277 (n : Nat) : onCount 277 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule285 (n : Nat) : onCount 285 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule293 (n : Nat) : onCount 293 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule301 (n : Nat) : onCount 301 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule309 (n : Nat) : onCount 309 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule317 (n : Nat) : onCount 317 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule325 (n : Nat) : onCount 325 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule333 (n : Nat) : onCount 333 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule341 (n : Nat) : onCount 341 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule349 (n : Nat) : onCount 349 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule357 (n : Nat) : onCount 357 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule365 (n : Nat) : onCount 365 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule373 (n : Nat) : onCount 373 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n
theorem a271061_rule381 (n : Nat) : onCount 381 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := O1) (by decide)) odd261 n

/-! Class B: Rules 413, 445, 477, 509: stage 2 is the plus of 5 cells ON on an OFF background. -/
theorem a271061_rule413 (n : Nat) : onCount 413 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := P5) (by decide)) odd261 n
theorem a271061_rule445 (n : Nat) : onCount 445 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := P5) (by decide)) odd261 n
theorem a271061_rule477 (n : Nat) : onCount 477 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := P5) (by decide)) odd261 n
theorem a271061_rule509 (n : Nat) : onCount 509 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) :=
  same_counts (oddAB (L := P5) (by decide)) odd261 n

end LT2D
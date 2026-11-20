import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import LT2D.Early.A269911_Core
import LT2D.Basic
/-
  A269911 (Rule 3), Mathlib part. The core file defines Cell, ruleOut, nbrOn, step, caState (lines 8-31
  of lean/NextStatements.lean, verbatim) and proves the stages: even stages ON exactly at the seed, odd
  stages ON except at the four axial neighbours D1. Here: window and onCount (verbatim), the count at
  odd stages, and the conjecture.
-/
namespace LT2D

/-! ## The window and the OEIS count -/

theorem D1_filter (g : Nat) (hg : 1 ≤ g) :
    (window g).filter (fun p : Cell => D1.contains p = true) = D1.toFinset := by
  ext ⟨x, y⟩
  simp only [window, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, List.contains_iff_mem,
    List.mem_toFinset, D1, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem D1_card : D1.toFinset.card = 4 := by decide

/-- If stage g >= 1 is ON except on the four axial neighbours of the seed, the count is (2g+1)^2 - 4. -/
theorem onCount_D1 {r g : Nat} (hg : 1 ≤ g) (h : caState r g = coFin D1) :
    onCount r g = (2 * g + 1) ^ 2 - 4 := by
  unfold onCount
  rw [h]
  have e := Finset.card_filter_add_card_filter_not (s := window g)
    (fun p : Cell => D1.contains p = true)
  have e2 : (window g).filter (fun p : Cell => coFin D1 p = true) =
      (window g).filter (fun p : Cell => ¬ (D1.contains p = true)) := by
    ext ⟨x, y⟩
    simp [coFin]
  rw [e2]
  rw [D1_filter g hg, D1_card] at e
  have := card_window g
  omega

theorem arith_3 (n : Nat) (hn : 1 ≤ n) :
    (((2 * (2 ^ n - 1) + 1) ^ 2 - 4 : Nat) : Int) = 4 ^ (1 + n) - 2 ^ (2 + n) - 3 := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h9 : 4 ≤ (2 * (2 ^ n - 1) + 1) ^ 2 := by
    have : 3 ≤ 2 * (2 ^ n - 1) + 1 := by omega
    nlinarith
  rw [Nat.cast_sub h9]
  push_cast [Nat.cast_sub (show 1 ≤ 2 ^ n by omega)]
  have e4 : (4 : Int) ^ n = ((2 : Int) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [pow_add, pow_add, e4]; ring

/-- A269911 (Rule 3): the entry's formula line: a(n) = 4^(1+n)-2^(2+n)-3 for n>0. -/
theorem a269911_formula (n : Nat) (hn : 1 ≤ n) :
    (onCount 3 (2 ^ n - 1) : Int) = 4 ^ (1 + n) - 2 ^ (2 + n) - 3 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n - 1 = 2 * m + 1 := by
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hev : 2 ^ n % 2 = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [hk, pow_succ]; omega
    exact ⟨(2 ^ n - 2) / 2, by omega⟩
  rw [onCount_D1 (g := 2 ^ n - 1) (by omega) (by rw [hm]; exact (r3_stages m).2)]
  exact arith_3 n hn

end LT2D
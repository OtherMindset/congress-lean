import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import LT2D.Early.A273310_Core
import LT2D.Basic
/-
  A273310 (Rule 641 and Rules 649, 897, 905), Mathlib part. The core file defines Cell, ruleOut, nbrOn,
  step, caState (lines 8-31 of lean/NextStatements.lean, verbatim) and proves the stages: OFF cells D1
  at stage 1, D2 at even stages >= 2, D3 (the 3 x 3 block) at odd stages >= 3. Here: window and onCount
  (verbatim), the count at odd stages >= 3, the conjecture and the comment's twin rules.
-/
namespace LT2D

/-! ## The window and the OEIS count -/

theorem D3_filter (g : Nat) (hg : 1 ≤ g) :
    (window g).filter (fun p : Cell => D3.contains p = true) = D3.toFinset := by
  ext ⟨x, y⟩
  simp only [window, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, List.contains_iff_mem,
    List.mem_toFinset, D3, D2, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem D3_card : D3.toFinset.card = 9 := by decide

/-- If stage g >= 1 is ON except on the 3 x 3 block, the count is (2g+1)^2 - 9. -/
theorem onCount_D3 {r g : Nat} (hg : 1 ≤ g) (h : caState r g = coFin D3) :
    onCount r g = (2 * g + 1) ^ 2 - 9 := by
  unfold onCount
  rw [h]
  have e := Finset.card_filter_add_card_filter_not (s := window g)
    (fun p : Cell => D3.contains p = true)
  have e2 : (window g).filter (fun p : Cell => coFin D3 p = true) =
      (window g).filter (fun p : Cell => ¬ (D3.contains p = true)) := by
    ext ⟨x, y⟩
    simp [coFin]
  rw [e2]
  rw [D3_filter g hg, D3_card] at e
  have := card_window g
  omega

private theorem onCount_odd {r : Nat} (hr : ∀ m, caState r (3 + 2 * m) = coFin D3) (n : Nat) (hn : 2 ≤ n) :
    onCount r (2 ^ n - 1) = (2 * (2 ^ n - 1) + 1) ^ 2 - 9 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : (2 ^ n - 1) % 2 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := Nat.one_le_two_pow (n := k)
    rw [hk, pow_succ]; omega
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n - 1 = 3 + 2 * m := ⟨(2 ^ n - 4) / 2, by omega⟩
  exact onCount_D3 (by omega) (by rw [hm]; exact hr m)

theorem arith_641 (n : Nat) (hn : 2 ≤ n) :
    (((2 * (2 ^ n - 1) + 1) ^ 2 - 9 : Nat) : Int) = 4 * 4 ^ n - 4 * 2 ^ n - 8 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h9 : 9 ≤ (2 * (2 ^ n - 1) + 1) ^ 2 := by
    have : 7 ≤ 2 * (2 ^ n - 1) + 1 := by omega
    nlinarith
  rw [Nat.cast_sub h9]
  push_cast [Nat.cast_sub (show 1 ≤ 2 ^ n by omega)]
  have e4 : (4 : Int) ^ n = ((2 : Int) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e4]; ring

/-- A273310 (Rule 641): Conjecture: a(n) = 4*4^n - 4*2^n - 8, n>1. -/
theorem a273310_formula (n : Nat) (hn : 2 ≤ n) :
    (onCount 641 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n - 8 := by
  rw [onCount_odd (fun m => (r641_stages.2 m).2) n hn]
  exact arith_641 n hn

/-- Two rules with OFF cells D1 at stage 1, then D2, D3, D2, ...: same plane at every stage. -/
theorem caState_eq {r s : Nat}
    (hr : caState r 1 = coFin D1_r641 ∧ ∀ m, caState r (2 + 2 * m) = coFin D2 ∧ caState r (3 + 2 * m) = coFin D3)
    (hs : caState s 1 = coFin D1_r641 ∧ ∀ m, caState s (2 + 2 * m) = coFin D2 ∧ caState s (3 + 2 * m) = coFin D3)
    (g : Nat) : caState r g = caState s g := by
  rcases Nat.lt_or_ge g 2 with h | h
  · obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
    · show caState r 0 = caState s 0
      rw [caState_zero, caState_zero]
    · rw [hr.1, hs.1]
  · obtain ⟨m, hm | hm⟩ : ∃ m, g = 2 + 2 * m ∨ g = 3 + 2 * m := by
      by_cases h2 : g % 2 = 0
      · exact ⟨(g - 2) / 2, Or.inl (by omega)⟩
      · exact ⟨(g - 3) / 2, Or.inr (by omega)⟩
    · rw [hm, (hr.2 m).1, (hs.2 m).1]
    · rw [hm, (hr.2 m).2, (hs.2 m).2]

/-! The entry's comment: Rules 649, 897 and 905 also generate this sequence, i.e. the count equals
Rule 641's at stage 2^n - 1 for every n >= 0. -/
theorem a273310_rule649 (n : Nat) : onCount 649 (2 ^ n - 1) = onCount 641 (2 ^ n - 1) := by
  unfold onCount; rw [caState_eq r649_stages r641_stages]
theorem a273310_rule897 (n : Nat) : onCount 897 (2 ^ n - 1) = onCount 641 (2 ^ n - 1) := by
  unfold onCount; rw [caState_eq r897_stages r641_stages]
theorem a273310_rule905 (n : Nat) : onCount 905 (2 ^ n - 1) = onCount 641 (2 ^ n - 1) := by
  unfold onCount; rw [caState_eq r905_stages r641_stages]

end LT2D
import LT2D.A272706.M1
import LT2D.A272706.K6
import LT2D.Basic
/-
  A272706 (Rules 515 and 523), file M2 (Mathlib): the window count folded onto the quadrant,
  the counts through the automaton (K5), and the two main theorems.
-/
namespace LT2D

open Finset

/-- S1 -/
private theorem sumTo_eq_sum (h : Nat → Nat) (m : Nat) : A272706.sumTo h m = ∑ i ∈ range m, h i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- A272706 (Rule 515): Conjecture: a(n) = 3*4^n - 8*2^n + 9 (no range in the entry; false at n = 0). -/
theorem a272706_formula (n : Nat) (hn : 1 ≤ n) :
    (onCount 515 (2 ^ n - 1) : Int) = 3 * 4 ^ n - 8 * 2 ^ n + 9 := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hg : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hp
  rw [onCount_fold 515 (2 ^ n - 1) (fun a b => A272706.V a b (2 ^ n))
    (fun x y => by rw [caState_515, hg]), hg]
  have hQ := A272706.sq_V n
  have hX := A272706.axX_V n
  have hY := A272706.axY_V n
  have hO := A272706.orig_V n
  have hc := A272706.count_core n hn
  simp only [sumTo_eq_sum] at hQ hX hY
  have hQ' := congrArg (Nat.cast : Nat → Int) hQ
  have hX' := congrArg (Nat.cast : Nat → Int) hX
  have hY' := congrArg (Nat.cast : Nat → Int) hY
  have hO' := congrArg (Nat.cast : Nat → Int) hO
  have hc' := congrArg (Nat.cast : Nat → Int) hc
  push_cast at hQ' hX' hY' hO' hc'
  rw [hQ', hX', hY', hO']
  linarith

/-- A272706: Conjecture: Rule 523 also generates this sequence. -/
theorem a272706_rule523 (n : Nat) : onCount 523 (2 ^ n - 1) = onCount 515 (2 ^ n - 1) := by
  unfold onCount
  rw [caState_523]

end LT2D
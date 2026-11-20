import LT2D.VN.M1
import LT2D.VN.K7
import LT2D.Basic
/-
  VN library, file M2 (Mathlib, via M1): the window count folded onto the quadrant (S1-S3, from A272706 M2
  #mwmg80g1-t2b1mg), the closed form of the count combination for every n >= n0, and the COUNT THEOREM vn_count.
-/
namespace LT2D

open Finset

/-- S1 -/
theorem sumTo_eq_sum (h : Nat → Nat) (m : Nat) : VN.sumTo h m = ∑ i ∈ range m, h i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- the closed form of the count combination 4Q + O - 2X - 2Y for every n ≥ n0 -/
theorem cnt_closed (A : VN.Tab) (D a b c : Int) (n0 nb : Nat) (h : VN.checkRec A D a b c n0 nb = true) :
    ∀ n, n0 ≤ n → D * VN.cnt A n = a * 4 ^ n + b * 2 ^ n + c := by
  obtain ⟨_, -, -, -, -, hbase⟩ := VN.checkRec_parts A D a b c n0 nb h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < nb + 3
    · exact hbase n hn hlt
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have r := VN.rec_cnt A D a b c n0 nb h m (by omega)
      have i0 := ih m (by omega) (by omega)
      have i1 := ih (m + 1) (by omega) (by omega)
      have i2 := ih (m + 2) (by omega) (by omega)
      have rD : D * VN.cnt A (m + 3) = 7 * (D * VN.cnt A (m + 2)) + 8 * (D * VN.cnt A m) -
          14 * (D * VN.cnt A (m + 1)) := by
        rw [show VN.cnt A (m + 3) = 7 * VN.cnt A (m + 2) + 8 * VN.cnt A m - 14 * VN.cnt A (m + 1) by
          linarith]
        ring
      have p1 : ∀ x : Int, x ^ (m + 1) = x ^ m * x := fun x => pow_succ x m
      have p2 : ∀ x : Int, x ^ (m + 2) = x ^ m * x ^ 2 := fun x => pow_add x m 2
      have p3 : ∀ x : Int, x ^ (m + 3) = x ^ m * x ^ 3 := fun x => pow_add x m 3
      rw [p1, p1] at i1
      rw [p2, p2] at i2
      rw [p3, p3, rD, i0, i1, i2]
      ring

/-- COUNT THEOREM: if CHECK F2, CHECK F1 (any mask U) and CHECK REC pass for the table A and rule R, then
D * a(n) = a*4^n + b*2^n + c for every n ≥ n0, where a(n) = onCount R (2^n - 1) -/
theorem vn_count (A : VN.Tab) (R U : Nat) (D a b c : Int) (n0 nb : Nat)
    (h2 : VN.checkF2 A = true) (h1 : VN.checkF1 A R U = true)
    (hr : VN.checkRec A D a b c n0 nb = true) (n : Nat) (hn : n0 ≤ n) :
    D * (onCount R (2 ^ n - 1) : Int) = a * 4 ^ n + b * 2 ^ n + c := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hg : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hp
  rw [onCount_fold R (2 ^ n - 1) (fun a b => VN.V A a b (2 ^ n))
    (fun x y => by rw [caState_V A R U h2 h1, hg]), hg]
  have hQ := VN.sq_V A n
  have hX := VN.axX_V A n
  have hY := VN.axY_V A n
  have hO := VN.orig_V A n
  simp only [sumTo_eq_sum] at hQ hX hY
  have hQ' := congrArg (Nat.cast : Nat → Int) hQ
  have hX' := congrArg (Nat.cast : Nat → Int) hX
  have hY' := congrArg (Nat.cast : Nat → Int) hY
  have hO' := congrArg (Nat.cast : Nat → Int) hO
  push_cast at hQ' hX' hY' hO'
  rw [hQ', hX', hY', hO']
  have hc := cnt_closed A D a b c n0 nb hr n hn
  unfold VN.cnt at hc
  rw [← hc]
  ring

end LT2D
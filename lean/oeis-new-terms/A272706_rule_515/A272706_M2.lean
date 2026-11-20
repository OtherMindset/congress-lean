import LongTable.P_mwmg73qw_sgejby
import LongTable.P_mwmg681k_0v8jc7
/-
  A272706 (Rules 515 and 523), file M2 (Mathlib): the window count folded onto the quadrant,
  the counts through the automaton (K5), and the two main theorems.
-/
namespace LT2D

open Finset

/-- S1 -/
theorem sumTo_eq_sum (h : Nat → Nat) (m : Nat) : A272706.sumTo h m = ∑ i ∈ range m, h i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- S2: a sum over [-g, g] of a function of |x| -/
theorem sum_Icc_natAbs (h : Nat → Int) (g : Nat) :
    ∑ x ∈ Icc (-(g : Int)) g, h x.natAbs = 2 * ∑ a ∈ range (g + 1), h a - h 0 := by
  induction g with
  | zero => simp <;> ring
  | succ g ih =>
    have e : Icc (-((g + 1 : Nat) : Int)) ((g + 1 : Nat) : Int) =
        insert (-((g : Int) + 1)) (insert ((g : Int) + 1) (Icc (-(g : Int)) g)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have n1 : ((g : Int) + 1) ∉ Icc (-(g : Int)) g := by
      simp only [Finset.mem_Icc]
      omega
    have n2 : -((g : Int) + 1) ∉ insert ((g : Int) + 1) (Icc (-(g : Int)) g) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [e, Finset.sum_insert n2, Finset.sum_insert n1, ih, Finset.sum_range_succ h (g + 1)]
    rw [show (-((g : Int) + 1)).natAbs = g + 1 by omega, show ((g : Int) + 1).natAbs = g + 1 by omega]
    ring

/-- S3: the window count of a stage that depends only on (|x|, |y|) -/
theorem onCount_fold (rule g : Nat) (W : Nat → Nat → Bool)
    (hW : ∀ x y : Int, caState rule g (x, y) = W x.natAbs y.natAbs) :
    (onCount rule g : Int) =
      4 * ∑ a ∈ range (g + 1), ∑ b ∈ range (g + 1), ((W a b).toNat : Int)
      - 2 * ∑ a ∈ range (g + 1), ((W a 0).toNat : Int)
      - 2 * ∑ b ∈ range (g + 1), ((W 0 b).toNat : Int) + ((W 0 0).toNat : Int) := by
  have h1 : (onCount rule g : Int) = ∑ x ∈ Icc (-(g : Int)) g, ∑ y ∈ Icc (-(g : Int)) g,
      ((W x.natAbs y.natAbs).toNat : Int) := by
    unfold onCount window
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hW x y]
    cases W x.natAbs y.natAbs <;> simp
  have inner : ∀ x : Int, ∑ y ∈ Icc (-(g : Int)) g, ((W x.natAbs y.natAbs).toNat : Int) =
      2 * ∑ b ∈ range (g + 1), ((W x.natAbs b).toNat : Int) - ((W x.natAbs 0).toNat : Int) :=
    fun x => sum_Icc_natAbs (fun b => ((W x.natAbs b).toNat : Int)) g
  rw [h1, Finset.sum_congr rfl (fun x _ => inner x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_Icc_natAbs (fun a => ∑ b ∈ range (g + 1), ((W a b).toNat : Int)) g,
    sum_Icc_natAbs (fun a => ((W a 0).toNat : Int)) g]
  ring

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
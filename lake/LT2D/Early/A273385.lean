import Mathlib
import LT2D.Basic

/-
  A273385: Rule 659 and the eleven rules of the entry's comment. Definitions for any rule, a
  finite-list device used only in proofs (checks by kernel `decide`), the count, the theorems.
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

/-! ## Generic lemmas (any rule) -/

/-! ## Stages of a rule with bits 0 and 9 set -/

/-- OFF cells at stage 1 for all twelve rules: the four axial neighbours of the seed. -/
private def D1 : List Cell := [(1, 0), (-1, 0), (0, 1), (0, -1)]
/-- OFF cells at stage 2 for Rules 659, 667, 723, 731: 3 x 3 square minus its centre. -/
private def D2 : List Cell := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]

private theorem stage1 {r : Nat} (h0 : Nat.testBit r 0 = true)
    (E1 : sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) D1 = true) :
    caState r 1 = coFin D1 := by
  show step r (caState r 0) = coFin D1
  rw [caState_zero, step_finOn h0]
  exact coFin_congr (sameSet_contains E1)

theorem allOn_from {r s : Nat} (h9 : Nat.testBit r 9 = true) (hs : caState r s = fun _ => true)
    (g : Nat) (hg : s ≤ g) : caState r g = fun _ => true := by
  induction g, hg using Nat.le_induction with
  | base => exact hs
  | succ g _ ih => show step r (caState r g) = _; rw [ih]; exact step_allOn h9

/-- OFF cells D1 at stage 1, D2 at stage 2, none at stage 3: then all ON from stage 3 on. -/
theorem late {r : Nat} (h : Nat.testBit r 0 = true ∧ Nat.testBit r 9 = true ∧
    sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) D1 = true ∧
    sameSet (offAfter r (coFin D1) (cands D1)) D2 = true ∧ offAfter r (coFin D2) (cands D2) = []) :
    caState r 1 = coFin D1 ∧ ∀ g, 3 ≤ g → caState r g = fun _ => true := by
  obtain ⟨h0, h9, E1, E2, E3⟩ := h
  refine ⟨stage1 h0 E1, fun g hg => allOn_from (s := 3) h9 ?_ g hg⟩
  show step r (caState r 2) = _
  have : caState r 2 = coFin D2 := by
    show step r (caState r 1) = _
    rw [stage1 h0 E1, step_coFin h9]
    exact coFin_congr (sameSet_contains E2)
  rw [this, step_coFin h9, E3]; rfl

/-- OFF cells D1 at stage 1, none at stage 2: then all ON from stage 2 on. -/
theorem early {r : Nat} (h : Nat.testBit r 0 = true ∧ Nat.testBit r 9 = true ∧
    sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) D1 = true ∧
    offAfter r (coFin D1) (cands D1) = []) :
    caState r 1 = coFin D1 ∧ ∀ g, 3 ≤ g → caState r g = fun _ => true := by
  obtain ⟨h0, h9, E1, E2⟩ := h
  refine ⟨stage1 h0 E1, fun g hg => allOn_from (s := 2) h9 ?_ g (by omega)⟩
  show step r (caState r 1) = _
  rw [stage1 h0 E1, step_coFin h9, E2]; rfl

end LT2D

/-! ## The OEIS count and the main theorems -/
namespace LT2D

theorem onCount_allOn {rule g : Nat} (h : caState rule g = fun _ => true) :
    onCount rule g = (2 * g + 1) ^ 2 := by
  unfold onCount
  rw [Finset.filter_true_of_mem (fun p _ => by rw [h]), card_window]

theorem arith_659 (n : Nat) (_hn : 1 ≤ n) :
    (((2 * (2 ^ n - 1) + 1) ^ 2 : Nat) : Int) = 4 * 4 ^ n - 4 * 2 ^ n + 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  push_cast [Nat.cast_sub h1]
  have h4 : (4 : Int) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  ring

/-- Two rules with OFF cells D1 at stage 1 and all ON from stage 3 on (stage 0 is the same seed)
have the same count at stage 2^n - 1 for every n. -/
private theorem same_counts {r s : Nat} (hr : caState r 1 = coFin D1 ∧ ∀ g, 3 ≤ g → caState r g = fun _ => true)
    (hs : caState s 1 = coFin D1 ∧ ∀ g, 3 ≤ g → caState s g = fun _ => true)
    (n : Nat) : onCount r (2 ^ n - 1) = onCount s (2 ^ n - 1) := by
  match n with
  | 0 => show onCount r 0 = onCount s 0; unfold onCount; rw [caState_zero, caState_zero]
  | 1 => show onCount r 1 = onCount s 1; unfold onCount; rw [hr.1, hs.1]
  | n + 2 =>
    have h4 : 4 ≤ 2 ^ (n + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [onCount_allOn (hr.2 _ (by omega)), onCount_allOn (hs.2 _ (by omega))]

theorem r659_stages : caState 659 1 = coFin D1 ∧ ∀ g, 3 ≤ g → caState 659 g = fun _ => true :=
  late (by decide)

/-- A273385 conjecture: for Rule 659, a(n) = 4*4^n - 4*2^n + 1 for n > 1. -/
theorem a273385_rule659 (n : Nat) (hn : 2 ≤ n) :
    (onCount 659 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n + 1 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [onCount_allOn (r659_stages.2 _ (by omega)), arith_659 n (by omega)]

/-! The entry's comment: Rules 667, 723, 731, 931, 939, 947, 955, 995, 1003, 1011, 1019 generate the
same sequence, i.e. the count equals Rule 659's at stage 2^n - 1 for every n ≥ 0. -/
theorem a273385_rule667 (n : Nat) : onCount 667 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (late (by decide)) r659_stages n
theorem a273385_rule723 (n : Nat) : onCount 723 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (late (by decide)) r659_stages n
theorem a273385_rule731 (n : Nat) : onCount 731 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (late (by decide)) r659_stages n
theorem a273385_rule931 (n : Nat) : onCount 931 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n
theorem a273385_rule939 (n : Nat) : onCount 939 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n
theorem a273385_rule947 (n : Nat) : onCount 947 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n
theorem a273385_rule955 (n : Nat) : onCount 955 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n
theorem a273385_rule995 (n : Nat) : onCount 995 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n
theorem a273385_rule1003 (n : Nat) : onCount 1003 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n
theorem a273385_rule1011 (n : Nat) : onCount 1011 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n
theorem a273385_rule1019 (n : Nat) : onCount 1019 (2 ^ n - 1) = onCount 659 (2 ^ n - 1) :=
  same_counts (early (by decide)) r659_stages n

end LT2D
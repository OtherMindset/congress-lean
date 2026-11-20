import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import LT2D.A272706.K4
import LT2D.Basic
/-
  A272706 (Rules 515 and 523), file M1 (Mathlib): the posted plane-wide definitions of 18 Nov
  (#mwmbjanx-5lciqx, lines 8-41 of lean/NextStatements.lean, verbatim), then the bridge from the
  15-state automaton (A272706.V) to LT2D.caState 515 on all of Int x Int, and Rule 523 = Rule 515.
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

end LT2D

namespace LT2D

/-- B1 -/
theorem ruleOut_515 (c : Bool) (k : Nat) : ruleOut 515 c k = A272706.rule c k := rfl

/-- B2: Rules 523 and 515 differ only at bit 3 (an ON cell with exactly one ON neighbour) -/
theorem ruleOut_523 (c : Bool) (k : Nat) (h : ¬ (c = true ∧ k = 1)) :
    ruleOut 523 c k = ruleOut 515 c k := by
  unfold ruleOut
  rcases Nat.lt_or_ge k 5 with hk | hk
  · have hb : ∀ c : Bool, ∀ k, k < 5 → ¬ (c = true ∧ k = 1) →
        Nat.testBit 523 (c.toNat + 2 * k) = Nat.testBit 515 (c.toNat + 2 * k) := by decide
    exact hb c k hk h
  · have h1 : 2 ^ 10 ≤ 2 ^ (c.toNat + 2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : (2 : Nat) ^ 10 = 1024 := by norm_num
    rw [Nat.testBit_lt_two_pow (by omega : 523 < 2 ^ (c.toNat + 2 * k)),
      Nat.testBit_lt_two_pow (by omega : 515 < 2 ^ (c.toNat + 2 * k))]

/-- B4 (THE BRIDGE): stage g of Rule 515 on the whole plane is V at (|x|, |y|), time g + 1 -/
theorem caState_515 (g : Nat) (x y : Int) :
    caState 515 g (x, y) = A272706.V x.natAbs y.natAbs (g + 1) := by
  induction g generalizing x y with
  | zero =>
    show decide ((x, y) = ((0 : Int), (0 : Int))) = A272706.V x.natAbs y.natAbs 1
    rw [A272706.F2_V]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  | succ g ih =>
    show ruleOut 515 (caState 515 g (x, y)) (nbrOn (caState 515 g) (x, y)) =
      A272706.V x.natAbs y.natAbs (g + 1 + 1)
    rw [nbrOn_abs (caState 515 g) (fun a b => A272706.V a b (g + 1)) ih x y, ih x y, ruleOut_515,
      A272706.F1_V x.natAbs y.natAbs (g + 1) (by omega)]
    rfl

/-- B5: the neighbour count of Rule 515 at stage g -/
theorem nbrOn_515 (g : Nat) (x y : Int) :
    nbrOn (caState 515 g) (x, y) = A272706.kV x.natAbs y.natAbs (g + 1) := by
  exact nbrOn_abs (caState 515 g) (fun a b => A272706.V a b (g + 1)) (caState_515 g) x y

/-- B6: Rules 523 and 515 have the same diagram at every stage -/
theorem caState_523 (g : Nat) : caState 523 g = caState 515 g := by
  induction g with
  | zero => rfl
  | succ g ih =>
    funext p
    obtain ⟨x, y⟩ := p
    show ruleOut 523 (caState 523 g (x, y)) (nbrOn (caState 523 g) (x, y)) =
      ruleOut 515 (caState 515 g (x, y)) (nbrOn (caState 515 g) (x, y))
    rw [ih]
    apply ruleOut_523
    rw [caState_515, nbrOn_515]
    exact fun h => A272706.NB3_V _ _ _ (by omega) h.1 h.2

end LT2D
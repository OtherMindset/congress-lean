import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import LT2D.VN.K5
import LT2D.Basic
/-
  VN library, file M1 (Mathlib, seven narrow imports): the posted plane-wide definitions of 18 Nov
  (#mwmbjanx-5lciqx, lines 8-41 of lean/NextStatements.lean, verbatim), Lemma 1 (scan/Lemma1.lean, verbatim),
  the bridge from any table A that passes CHECK F2 and CHECK F1 to LT2D.caState on all of Int x Int,
  and the TWIN THEOREM vn_twin. Generic version of A272706 M1 (#mwmg73qw-sgejby).
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

end LT2D

namespace LT2D

/-- If two rules have the same stage g0 and, at every later stage of the first rule, every cell's index
(c, k) is one where the two rule numbers agree, then the two diagrams agree from g0 on. Generalises
T1's ruleOut_523 + NB3_V (bit 3) and covers twin rules (65/321 bit 8, 773-group bits 3,4,6). -/
theorem caState_eq_of_unused (R R' g0 : Nat) (h0 : caState R g0 = caState R' g0)
    (hu : ∀ g, g0 ≤ g → ∀ p, ruleOut R (caState R g p) (nbrOn (caState R g) p) =
      ruleOut R' (caState R g p) (nbrOn (caState R g) p)) :
    ∀ g, g0 ≤ g → caState R g = caState R' g := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => exact h0
  | succ g hg ih =>
    funext p
    show step R (caState R g) p = step R' (caState R' g) p
    rw [← ih]
    exact hu g hg p

theorem ruleOut_eq (R : Nat) (c : Bool) (k : Nat) : ruleOut R c k = VN.rule R c k := rfl

/-- THE BRIDGE: if CHECK F2 and CHECK F1 pass, stage g of rule R at (x, y) is V A at (|x|, |y|), time g + 1 -/
theorem caState_V (A : VN.Tab) (R U : Nat) (h2 : VN.checkF2 A = true) (h1 : VN.checkF1 A R U = true)
    (g : Nat) (x y : Int) : caState R g (x, y) = VN.V A x.natAbs y.natAbs (g + 1) := by
  induction g generalizing x y with
  | zero =>
    show decide ((x, y) = ((0 : Int), (0 : Int))) = VN.V A x.natAbs y.natAbs 1
    rw [VN.F2_V A h2]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  | succ g ih =>
    show ruleOut R (caState R g (x, y)) (nbrOn (caState R g) (x, y)) =
      VN.V A x.natAbs y.natAbs (g + 1 + 1)
    rw [nbrOn_abs (caState R g) (fun a b => VN.V A a b (g + 1)) ih x y, ih x y, ruleOut_eq,
      VN.F1_V A R U h1 x.natAbs y.natAbs (g + 1) (by omega)]
    rfl

/-- the neighbour count of rule R at stage g -/
theorem nbrOn_V (A : VN.Tab) (R U : Nat) (h2 : VN.checkF2 A = true) (h1 : VN.checkF1 A R U = true)
    (g : Nat) (x y : Int) : nbrOn (caState R g) (x, y) = VN.kV A x.natAbs y.natAbs (g + 1) :=
  nbrOn_abs (caState R g) (fun a b => VN.V A a b (g + 1)) (caState_V A R U h2 h1 g) x y

/-- TWIN THEOREM: if CHECK F2 and CHECK F1 (mask U) pass for rule R, and R' agrees with R at every index
in U, then R' and R have the same diagram at every stage (Lemma 1 with g0 = 0) -/
theorem vn_twin (A : VN.Tab) (R R' U : Nat) (h2 : VN.checkF2 A = true) (h1 : VN.checkF1 A R U = true)
    (hU : VN.agreeOn U R R' = true) : caState R' = caState R := by
  have hu : ∀ g, 0 ≤ g → ∀ p, ruleOut R (caState R g p) (nbrOn (caState R g) p) =
      ruleOut R' (caState R g p) (nbrOn (caState R g) p) := by
    intro g _ p
    obtain ⟨x, y⟩ := p
    rw [caState_V A R U h2 h1 g x y, nbrOn_V A R U h2 h1 g x y]
    exact VN.agree_bit U R R' hU _ _ (VN.kV_le A _ _ _) (VN.U_V A R U h1 _ _ (g + 1) (by omega))
  funext g
  exact (caState_eq_of_unused R R' 0 rfl hu g (Nat.zero_le g)).symm

/-- the twin theorem for the window count -/
theorem vn_twin_count (A : VN.Tab) (R R' U : Nat) (h2 : VN.checkF2 A = true)
    (h1 : VN.checkF1 A R U = true) (hU : VN.agreeOn U R R' = true) (g : Nat) :
    onCount R' g = onCount R g := by
  unfold onCount
  rw [vn_twin A R R' U h2 h1 hU]

end LT2D
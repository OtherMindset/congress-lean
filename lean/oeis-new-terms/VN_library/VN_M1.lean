import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import LongTable.P_mwmotahy_3afbeh
/-
  VN library, file M1 (Mathlib, seven narrow imports): the posted plane-wide definitions of 18 Nov
  (#mwmbjanx-5lciqx, lines 8-41 of lean/NextStatements.lean, verbatim), Lemma 1 (scan/Lemma1.lean, verbatim),
  the bridge from any table A that passes CHECK F2 and CHECK F1 to LT2D.caState on all of Int x Int,
  and the TWIN THEOREM vn_twin. Generic version of A272706 M1 (#mwmg73qw-sgejby).
-/
namespace LT2D

/-- A cell of the plane. -/
abbrev Cell := Int × Int

/-- Outer totalistic von Neumann rule: new state = bit (c + 2k) of the rule number, where c is the
cell's own state (0/1) and k the number of ON cells among its four axial neighbours. -/
def ruleOut (rule : Nat) (c : Bool) (k : Nat) : Bool :=
  Nat.testBit rule (c.toNat + 2 * k)

/-- k = number of ON cells among the four axial neighbours of p. -/
def nbrOn (s : Cell → Bool) (p : Cell) : Nat :=
  (s (p.1 + 1, p.2)).toNat + (s (p.1 - 1, p.2)).toNat +
  (s (p.1, p.2 + 1)).toNat + (s (p.1, p.2 - 1)).toNat

/-- One synchronous step of the rule on the whole plane. -/
def step (rule : Nat) (s : Cell → Bool) : Cell → Bool :=
  fun p => ruleOut rule (s p) (nbrOn s p)

/-- Stage g of the rule on the whole plane, from one ON cell at the origin at stage 0.
For an odd rule (bit 0 = 1) every cell far from the seed is ON at stage 1. -/
def caState (rule : Nat) : Nat → Cell → Bool
  | 0 => fun p => decide (p = (0, 0))
  | g + 1 => step rule (caState rule g)

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

/-- The window [-g,g]^2 around the seed. -/
def window (g : Nat) : Finset Cell :=
  Finset.Icc (-(g : Int)) g ×ˢ Finset.Icc (-(g : Int)) g

/-- The OEIS count: number of ON cells of stage g inside the (2g+1) x (2g+1) square around the seed. -/
def onCount (rule g : Nat) : Nat :=
  ((window g).filter (fun p => caState rule g p = true)).card

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

/-- B3: the neighbour count of a state that depends only on (|x|, |y|) -/
theorem nbrOn_abs (s : Cell → Bool) (W : Nat → Nat → Bool)
    (hs : ∀ x y : Int, s (x, y) = W x.natAbs y.natAbs) (x y : Int) :
    nbrOn s (x, y) =
      (W (x.natAbs + 1) y.natAbs).toNat +
      (if x.natAbs = 0 then W 1 y.natAbs else W (x.natAbs - 1) y.natAbs).toNat +
      (W x.natAbs (y.natAbs + 1)).toNat +
      (if y.natAbs = 0 then W x.natAbs 1 else W x.natAbs (y.natAbs - 1)).toNat := by
  have hx : (W (x + 1).natAbs y.natAbs).toNat + (W (x - 1).natAbs y.natAbs).toNat =
      (W (x.natAbs + 1) y.natAbs).toNat +
      (if x.natAbs = 0 then W 1 y.natAbs else W (x.natAbs - 1) y.natAbs).toNat := by
    rcases lt_trichotomy x 0 with h | h | h
    · rw [show (x + 1).natAbs = x.natAbs - 1 by omega, show (x - 1).natAbs = x.natAbs + 1 by omega,
        if_neg (by omega)]
      omega
    · subst h
      rfl
    · rw [show (x + 1).natAbs = x.natAbs + 1 by omega, show (x - 1).natAbs = x.natAbs - 1 by omega,
        if_neg (by omega)]
  have hy : (W x.natAbs (y + 1).natAbs).toNat + (W x.natAbs (y - 1).natAbs).toNat =
      (W x.natAbs (y.natAbs + 1)).toNat +
      (if y.natAbs = 0 then W x.natAbs 1 else W x.natAbs (y.natAbs - 1)).toNat := by
    rcases lt_trichotomy y 0 with h | h | h
    · rw [show (y + 1).natAbs = y.natAbs - 1 by omega, show (y - 1).natAbs = y.natAbs + 1 by omega,
        if_neg (by omega)]
      omega
    · subst h
      rfl
    · rw [show (y + 1).natAbs = y.natAbs + 1 by omega, show (y - 1).natAbs = y.natAbs - 1 by omega,
        if_neg (by omega)]
  unfold nbrOn
  simp only [hs]
  omega

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
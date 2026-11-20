import Mathlib
import LT2D.Basic

/-
  A271061: Rule 261 and the 35 rules of the entry's comment (Rules 269 .. 765). Definitions for any
  rule, a finite-list device used only in proofs (checks by kernel `decide`), the count, the theorems.
  Part 1 of 3 (the other two files import this one).
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

/-! ## Generic lemmas (any rule) -/

/-! ## The stages of Rules 261 .. 765: the origin is the only cell that differs at odd stages -/

/-- The seed cell, and the plus of 5 cells. -/
def O1 : List Cell := [(0, 0)]
def P5 : List Cell := [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]

/-- Classes A and B (bit 9 clear): stages 1, 2, 3 are ON-except-O1, ON-exactly-L, ON-except-O1. -/
def goodAB (r : Nat) (L : List Cell) : Bool :=
  r.testBit 0 && !r.testBit 9 && sameSet (offAfter r (finOn O1) (cands O1)) O1 &&
    sameSet (onAfter r (coFin O1) (cands O1)) L && sameSet (offAfter r (finOn L) (cands L)) O1

/-- Class C (bits 0 and 9 set): from stage 1 on, the configuration is ON-except-O1. -/
def goodC (r : Nat) : Bool :=
  r.testBit 0 && r.testBit 9 && sameSet (offAfter r (finOn O1) (cands O1)) O1 &&
    sameSet (offAfter r (coFin O1) (cands O1)) O1

/-- All odd stages are ON-except-O1, given stage 1 and a two-step return. -/
theorem odd_of {r : Nat} (h1 : caState r 1 = coFin O1) (h2 : step r (step r (coFin O1)) = coFin O1) :
    ∀ m, caState r (2 * m + 1) = coFin O1 := by
  intro m
  induction m with
  | zero => exact h1
  | succ m ih =>
    have : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
    rw [this]
    show step r (step r (caState r (2 * m + 1))) = _
    rw [ih, h2]

theorem stage1_O1 {r : Nat} (h0 : Nat.testBit r 0 = true)
    (E1 : sameSet (offAfter r (finOn O1) (cands O1)) O1 = true) : caState r 1 = coFin O1 := by
  show step r (caState r 0) = coFin O1
  rw [caState_zero, step_finOn h0]
  exact coFin_congr (sameSet_contains E1)

theorem oddAB {r : Nat} {L : List Cell} (h : goodAB r L = true) :
    ∀ m, caState r (2 * m + 1) = coFin O1 := by
  simp only [goodAB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h0, h9⟩, E1⟩, E2⟩, E3⟩ := h
  refine odd_of (stage1_O1 h0 E1) ?_
  rw [step_coFin0 h9, finOn_congr (sameSet_contains E2), step_finOn h0]
  exact coFin_congr (sameSet_contains E3)

theorem oddC {r : Nat} (h : goodC r = true) : ∀ m, caState r (2 * m + 1) = coFin O1 := by
  simp only [goodC, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h9⟩, E1⟩, E2⟩ := h
  have hf : step r (coFin O1) = coFin O1 := by
    rw [step_coFin h9]
    exact coFin_congr (sameSet_contains E2)
  exact odd_of (stage1_O1 h0 E1) (by rw [hf, hf])

end LT2D

/-! ## The OEIS count and the main theorems -/
namespace LT2D

theorem onCount_coFin {r g : Nat} (h : caState r g = coFin O1) : onCount r g = (2 * g + 1) ^ 2 - 1 := by
  unfold onCount
  rw [h]
  have : (window g).filter (fun p => coFin O1 p = true) = (window g).erase (0, 0) := by
    ext p
    simp only [Finset.mem_erase, coFin, O1]
    simp
    tauto
  rw [this, Finset.card_erase_of_mem (by simp [window]), card_window]

/-- At stage 2^n - 1 (n >= 1) a rule with all odd stages ON-except-O1 has (2^n*2-1)^2 - 1 ON cells. -/
theorem count_odd {r : Nat} (h : ∀ m, caState r (2 * m + 1) = coFin O1) (n : Nat) (hn : 1 ≤ n) :
    (onCount r (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have e : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by rw [pow_succ]; omega
  rw [e, onCount_coFin (h _)]
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ k = y + 1 := ⟨2 ^ k - 1, by omega⟩
  have h4 : (4 : Int) ^ (k + 1) = 4 * ((y : Int) + 1) ^ 2 := by
    have : (4 : Int) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h2 : (2 : Int) ^ k = y + 1 := by exact_mod_cast hy
    rw [pow_succ, this, h2]; ring
  have h2 : (2 : Int) ^ (k + 1) = 2 * ((y : Int) + 1) := by
    have h2 : (2 : Int) ^ k = y + 1 := by exact_mod_cast hy
    rw [pow_succ, h2]; ring
  rw [h4, h2, hy, Nat.add_sub_cancel]
  have hp : 1 ≤ (2 * (2 * y + 1) + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub hp]
  push_cast
  ring

/-- Two rules with all odd stages ON-except-O1 have the same count at stage 2^n - 1, every n. -/
theorem same_counts {r s : Nat} (hr : ∀ m, caState r (2 * m + 1) = coFin O1)
    (hs : ∀ m, caState s (2 * m + 1) = coFin O1) (n : Nat) :
    onCount r (2 ^ n - 1) = onCount s (2 ^ n - 1) := by
  match n with
  | 0 => show onCount r 0 = onCount s 0; unfold onCount; rw [caState_zero, caState_zero]
  | n + 1 =>
    have h := count_odd hr (n + 1) (by omega)
    have h' := count_odd hs (n + 1) (by omega)
    exact_mod_cast h.trans h'.symm

theorem odd261 : ∀ m, caState 261 (2 * m + 1) = coFin O1 := oddAB (L := O1) (by decide)

/-- A271061: Conjecture: a(n) = 4*4^n - 4*2^n, n > 0, for Rule 261. -/
theorem a271061_formula (n : Nat) (hn : 1 ≤ n) :
    (onCount 261 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n :=
  count_odd odd261 n hn

end LT2D
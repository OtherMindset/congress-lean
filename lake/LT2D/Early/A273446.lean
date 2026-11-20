import Mathlib
import LT2D.Basic

/-
  A273446 (Rule 721) and Rule 729. Plane-wide definitions for any rule number, a finite-list
  device used only in the proofs, finite checks by kernel `decide`, then the window count and
  the main theorems.
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

/-! ## Generic lemmas (any rule) -/

/-! ## Rules 721 and 729: finite checks (kernel decide). Same device as Rule 659. -/

private def P5 : List Cell := [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]
def X4 : List Cell := [(1, 1), (1, -1), (-1, 1), (-1, -1)]
def Q8 : List Cell := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]
private def O1 : List Cell := [(0, 0)]

theorem r721_bit0 : Nat.testBit 721 0 = true := by decide
theorem r721_bit9 : Nat.testBit 721 9 = true := by decide
theorem r729_bit0 : Nat.testBit 729 0 = true := by decide
theorem r729_bit9 : Nat.testBit 729 9 = true := by decide
theorem r721_E1 : sameSet (offAfter 721 (finOn [(0, 0)]) (cands [(0, 0)])) P5 = true := by decide
theorem r721_E2 : sameSet (offAfter 721 (coFin P5) (cands P5)) X4 = true := by decide
theorem r721_E3 : sameSet (offAfter 721 (coFin X4) (cands X4)) Q8 = true := by decide
theorem r721_E4 : sameSet (offAfter 721 (coFin Q8) (cands Q8)) O1 = true := by decide
theorem r721_E5 : sameSet (offAfter 721 (coFin O1) (cands O1)) O1 = true := by decide
theorem r729_E1 : sameSet (offAfter 729 (finOn [(0, 0)]) (cands [(0, 0)])) P5 = true := by decide
theorem r729_E2 : sameSet (offAfter 729 (coFin P5) (cands P5)) X4 = true := by decide
theorem r729_E3 : sameSet (offAfter 729 (coFin X4) (cands X4)) Q8 = true := by decide
theorem r729_E4 : sameSet (offAfter 729 (coFin Q8) (cands Q8)) O1 = true := by decide
theorem r729_E5 : sameSet (offAfter 729 (coFin O1) (cands O1)) O1 = true := by decide

/-! ## Stages: from stage 4 on, ON everywhere except the origin (both rules) -/

/-- The stages shared by Rules 721 and 729 (stage 0 is the seed). -/
def stage7 : Nat → Cell → Bool
  | 0 => finOn O1
  | 1 => coFin P5
  | 2 => coFin X4
  | 3 => coFin Q8
  | _ => coFin O1

private theorem stages {rule : Nat} (h0 : Nat.testBit rule 0 = true) (h9 : Nat.testBit rule 9 = true)
    (E1 : sameSet (offAfter rule (finOn O1) (cands O1)) P5 = true)
    (E2 : sameSet (offAfter rule (coFin P5) (cands P5)) X4 = true)
    (E3 : sameSet (offAfter rule (coFin X4) (cands X4)) Q8 = true)
    (E4 : sameSet (offAfter rule (coFin Q8) (cands Q8)) O1 = true)
    (E5 : sameSet (offAfter rule (coFin O1) (cands O1)) O1 = true) (g : Nat) :
    caState rule g = stage7 g := by
  induction g with
  | zero => exact caState_zero rule
  | succ g ih =>
    show step rule (caState rule g) = stage7 (g + 1)
    rw [ih]
    match g with
    | 0 => exact (step_finOn h0 O1).trans (coFin_congr (sameSet_contains E1))
    | 1 => exact (step_coFin h9 P5).trans (coFin_congr (sameSet_contains E2))
    | 2 => exact (step_coFin h9 X4).trans (coFin_congr (sameSet_contains E3))
    | 3 => exact (step_coFin h9 Q8).trans (coFin_congr (sameSet_contains E4))
    | _ + 4 => exact (step_coFin h9 O1).trans (coFin_congr (sameSet_contains E5))

theorem r721_stages (g : Nat) : caState 721 g = stage7 g :=
  stages r721_bit0 r721_bit9 r721_E1 r721_E2 r721_E3 r721_E4 r721_E5 g

theorem r729_stages (g : Nat) : caState 729 g = stage7 g :=
  stages r729_bit0 r729_bit9 r729_E1 r729_E2 r729_E3 r729_E4 r729_E5 g

theorem r721_fixed (g : Nat) (hg : 4 ≤ g) : caState 721 g = coFin O1 := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 4 := ⟨g - 4, by omega⟩
  rw [r721_stages]
  rfl

end LT2D

/-! ## Mathlib part: the OEIS count and the main theorems for A273446 (Rules 721 and 729) -/
namespace LT2D

theorem onCount_origin {rule g : Nat} (h : caState rule g = coFin [(0, 0)]) :
    onCount rule g = (2 * g + 1) ^ 2 - 1 := by
  unfold onCount
  have e : (window g).filter (fun p => caState rule g p = true) = (window g).erase (0, 0) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_erase, h]
    constructor
    · rintro ⟨hw, hp⟩
      refine ⟨?_, hw⟩
      rintro rfl
      simp [coFin] at hp
    · rintro ⟨hp, hw⟩
      refine ⟨hw, ?_⟩
      simp [coFin, hp]
  rw [e, Finset.card_erase_of_mem, card_window]
  simp [window]

theorem arith_721 (n : Nat) :
    ((((2 * (2 ^ n - 1) + 1) ^ 2 - 1 : Nat)) : Int) = 4 * 4 ^ n - 4 * 2 ^ n := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 * (2 ^ n - 1) + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
  have h4 : (4 : Int) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  ring

/-- A273446 (Rule 721), conjectured in the OEIS entry: a(n) = 4*4^n - 4*2^n for n > 2,
where a(n) = onCount 721 (2^n - 1). -/
theorem a273446_formula (n : Nat) (hn : 3 ≤ n) :
    (onCount 721 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [onCount_origin (r721_fixed _ (by omega)), arith_721 n]

/-- A273446's comment: Rule 729 also generates the sequence, i.e. for every n the count for
Rule 729 at stage 2^n - 1 equals the count for Rule 721 (in fact every stage is the same). -/
theorem a273446_rule729 (n : Nat) : onCount 729 (2 ^ n - 1) = onCount 721 (2 ^ n - 1) := by
  unfold onCount
  rw [r729_stages, r721_stages]

end LT2D
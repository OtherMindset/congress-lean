import LT2D.Basic
/-
  A269911 (Rule 3), core part, no imports. Definitions for any rule, a finite-list device used only in
  proofs, kernel `decide` checks of the stages. Rule 3 has bit 0 set and bit 9 clear: the background
  alternates OFF, ON, OFF, ...; even stages are ON exactly at the seed, odd stages are ON except at the
  four axial neighbours of the seed.
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

/-! ## Generic lemmas (any rule) -/

/-! ## Stages of a rule with bit 0 set and bit 9 clear that passes the two checks of `stages`: seed, ON except 4 cells, seed, ... -/

/-- The seed cell. -/
private def O1 : List Cell := [(0, 0)]
/-- OFF cells at odd stages: the four axial neighbours of the seed. -/
def D1 : List Cell := [(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- Even stage 2m: ON exactly at the seed. Odd stage 2m+1: ON except on the four neighbours. -/
private theorem stages {r : Nat} (h : Nat.testBit r 0 = true ∧ Nat.testBit r 9 = false ∧
    sameSet (offAfter r (finOn O1) (cands O1)) D1 = true ∧
    sameSet (onAfter r (coFin D1) (cands D1)) O1 = true) :
    ∀ m, caState r (2 * m) = finOn O1 ∧ caState r (2 * m + 1) = coFin D1 := by
  obtain ⟨h0, h9, E1, E2⟩ := h
  intro m
  induction m with
  | zero =>
    refine ⟨caState_zero r, ?_⟩
    show step r (caState r 0) = coFin D1
    rw [caState_zero, step_finOn h0]
    exact coFin_congr (sameSet_contains E1)
  | succ m ih =>
    have a : caState r (2 * (m + 1)) = finOn O1 := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      show step r (caState r (2 * m + 1)) = finOn O1
      rw [ih.2, step_coFin0 h9]
      exact finOn_congr (sameSet_contains E2)
    refine ⟨a, ?_⟩
    rw [show 2 * (m + 1) + 1 = (2 * (m + 1)) + 1 by omega]
    show step r (caState r (2 * (m + 1))) = coFin D1
    rw [a, step_finOn h0]
    exact coFin_congr (sameSet_contains E1)

theorem r3_stages : ∀ m, caState 3 (2 * m) = finOn O1 ∧ caState 3 (2 * m + 1) = coFin D1 :=
  stages (by decide)

end LT2D
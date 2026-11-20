import LT2D.Basic
/-
  A273310 (Rule 641 and Rules 649, 897, 905), core part, no imports. Definitions for any rule, a
  finite-list device used only in proofs, kernel `decide` checks of the stages: the cells OFF at stage 1
  (plus of 5), stage 2 (8-cell ring), stage 3 (3 x 3 block), and then the period 2 (ring, block, ...).
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

/-! ## Generic lemmas (any rule) -/

/-! ## Stages of a rule with bits 0 and 9 set that passes the four checks of `stages`: OFF cells D1, D2, D3, D2, D3, ... -/

/-- OFF cells at stage 1: the seed and its four axial neighbours. -/
def D1_r641 : List Cell := [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]
/-- OFF cells at even stages >= 2: the 8 cells around the seed. -/
def D2 : List Cell := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]
/-- OFF cells at odd stages >= 3: the 3 x 3 block. -/
def D3 : List Cell := (0, 0) :: D2

private theorem stage1 {r : Nat} (h0 : Nat.testBit r 0 = true)
    (E1 : sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) D1_r641 = true) :
    caState r 1 = coFin D1_r641 := by
  show step r (caState r 0) = coFin D1_r641
  rw [caState_zero, step_finOn h0]
  exact coFin_congr (sameSet_contains E1)

theorem stage_succ {r : Nat} (h9 : Nat.testBit r 9 = true) {A B : List Cell} {s : Nat}
    (E : sameSet (offAfter r (coFin A) (cands A)) B = true) (hs : caState r s = coFin A) :
    caState r (s + 1) = coFin B := by
  show step r (caState r s) = coFin B
  rw [hs, step_coFin h9]
  exact coFin_congr (sameSet_contains E)

/-- Stage 1 has OFF cells D1, stage 2 D2, stage 3 D3, stage 4 D2 again: period 2 from stage 2. -/
private theorem stages {r : Nat} (h : Nat.testBit r 0 = true ∧ Nat.testBit r 9 = true ∧
    sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) D1_r641 = true ∧
    sameSet (offAfter r (coFin D1_r641) (cands D1_r641)) D2 = true ∧
    sameSet (offAfter r (coFin D2) (cands D2)) D3 = true ∧
    sameSet (offAfter r (coFin D3) (cands D3)) D2 = true) :
    caState r 1 = coFin D1_r641 ∧
      ∀ m, caState r (2 + 2 * m) = coFin D2 ∧ caState r (3 + 2 * m) = coFin D3 := by
  obtain ⟨h0, h9, E1, E2, E3, E4⟩ := h
  have s1 := stage1 h0 E1
  refine ⟨s1, fun m => ?_⟩
  induction m with
  | zero =>
    have s2 : caState r 2 = coFin D2 := stage_succ h9 E2 s1
    exact ⟨s2, stage_succ h9 E3 s2⟩
  | succ m ih =>
    have a : caState r (2 + 2 * (m + 1)) = coFin D2 := by
      rw [show 2 + 2 * (m + 1) = (3 + 2 * m) + 1 by omega]
      exact stage_succ h9 E4 ih.2
    exact ⟨a, by
      rw [show 3 + 2 * (m + 1) = (2 + 2 * (m + 1)) + 1 by omega]
      exact stage_succ h9 E3 a⟩

theorem r641_stages : caState 641 1 = coFin D1_r641 ∧
    ∀ m, caState 641 (2 + 2 * m) = coFin D2 ∧ caState 641 (3 + 2 * m) = coFin D3 :=
  stages (by decide)
theorem r649_stages : caState 649 1 = coFin D1_r641 ∧
    ∀ m, caState 649 (2 + 2 * m) = coFin D2 ∧ caState 649 (3 + 2 * m) = coFin D3 :=
  stages (by decide)
theorem r897_stages : caState 897 1 = coFin D1_r641 ∧
    ∀ m, caState 897 (2 + 2 * m) = coFin D2 ∧ caState 897 (3 + 2 * m) = coFin D3 :=
  stages (by decide)
theorem r905_stages : caState 905 1 = coFin D1_r641 ∧
    ∀ m, caState 905 (2 + 2 * m) = coFin D2 ∧ caState 905 (3 + 2 * m) = coFin D3 :=
  stages (by decide)

end LT2D
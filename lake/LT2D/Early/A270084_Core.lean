import LT2D.Early.R323_A
/- A270084 (Rule 65 and Rule 321), core part, no Mathlib. Imports the posted R323_A (#mwmfcf3a-sdo7h1, which
   imports R245_A #mwmc69rp-fpejr2): LT2D definitions, finite-list device, features, lists W2..W6, shapes
   E3 h, O3 h, finOn_W6. Rules 65 and 321 have bit 0 set and bit 9 clear. Their stage 1 is ON except on the
   plus of 5 cells (W2); from stage 2 on they follow the Rule 323 shapes: stage 2h is E3 h and stage 2h+1
   is O3 h for h >= 3, by the same feature check as R323_A, run for the rule at hand (kernel `decide`). -/
namespace LT2D

/-- The two one-step feature checks of R323_A (E3 -> O3, O3 -> E3 shifted), for any rule r. -/
def check3 (r : Nat) : Bool :=
  T17.all (fun X => T17.all (fun Y => stepF r (fun a b => !OF a b) X Y == !EF1 X.2.1 Y.2.1)) &&
  T17.all (fun X => T17.all (fun Y => stepF r (fun a b => !EF1 a b) X Y == !OF1 X.2.1 Y.2.1))

theorem S3 {r : Nat} (c : check3 r = true) {h : Int} (hh : 3 ≤ h) :
    step r (E3 h) = O3 h ∧ step r (O3 h) = E3 (h + 1) := by
  simp only [check3, Bool.and_eq_true] at c
  obtain ⟨ca, cb⟩ := c
  refine ⟨?_, ?_⟩
  · funext ⟨x, y⟩
    have := List.all_eq_true.mp (List.all_eq_true.mp ca _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
    exact beq_iff_eq.mp this
  · funext ⟨x, y⟩
    have := List.all_eq_true.mp (List.all_eq_true.mp cb _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
    have e := beq_iff_eq.mp this
    show _ = !Ocf (h + 1) (x, y)
    rw [Ocf_succ (by omega)]
    exact e

/-- Stages 1, 3 and 6, by the finite-list device; M is the set of OFF cells at stage 1. -/
theorem stages6 {r : Nat} (M : List Cell) (b0 : Nat.testBit r 0 = true) (b9 : Nat.testBit r 9 = false)
    (e : (sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) M &&
      sameSet (onAfter r (coFin M) (cands M)) W2 && sameSet (offAfter r (finOn W2) (cands W2)) W3 &&
      sameSet (onAfter r (coFin W3) (cands W3)) W4 && sameSet (offAfter r (finOn W4) (cands W4)) W5 &&
      sameSet (onAfter r (coFin W5) (cands W5)) W6) = true) :
    caState r 1 = coFin M ∧ caState r 3 = coFin W3 ∧ caState r 6 = finOn W6 := by
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩ := e
  have s1 : caState r 1 = coFin M := by
    show step r (caState r 0) = _
    rw [caState_zero, step_finOn b0]; exact coFin_congr (sameSet_contains e1)
  have s2 : caState r 2 = finOn W2 := by
    show step r (caState r 1) = _
    rw [s1, step_coFin_off b9]; exact finOn_congr (sameSet_contains e2)
  have s3 : caState r 3 = coFin W3 := by
    show step r (caState r 2) = _
    rw [s2, step_finOn b0]; exact coFin_congr (sameSet_contains e3)
  have s4 : caState r 4 = finOn W4 := by
    show step r (caState r 3) = _
    rw [s3, step_coFin_off b9]; exact finOn_congr (sameSet_contains e4)
  have s5 : caState r 5 = coFin W5 := by
    show step r (caState r 4) = _
    rw [s4, step_finOn b0]; exact coFin_congr (sameSet_contains e5)
  refine ⟨s1, s3, ?_⟩
  show step r (caState r 5) = _
  rw [s5, step_coFin_off b9]; exact finOn_congr (sameSet_contains e6)

/-- Closed forms for a rule passing check3 whose stage 6 is finOn W6: stage 2m+6 is E3 (m+3), stage 2m+7 is O3 (m+3). -/
theorem closed {r : Nat} (c : check3 r = true) (h6 : caState r 6 = finOn W6) (m : Nat) :
    caState r (2 * m + 6) = E3 ((m : Int) + 3) ∧ caState r (2 * m + 7) = O3 ((m : Int) + 3) := by
  have base : caState r 6 = E3 3 := h6.trans finOn_W6
  have odd : ∀ m : Nat, caState r (2 * m + 6) = E3 ((m : Int) + 3) →
      caState r (2 * m + 7) = O3 ((m : Int) + 3) := by
    intro m hm
    show step r (caState r (2 * m + 6)) = _
    rw [hm, (S3 c (by omega)).1]
  induction m with
  | zero => exact ⟨base, odd 0 base⟩
  | succ m ih =>
    have he : caState r (2 * (m + 1) + 6) = E3 (((m + 1 : Nat) : Int) + 3) := by
      rw [show 2 * (m + 1) + 6 = (2 * m + 7) + 1 by omega,
        show (((m + 1 : Nat) : Int) + 3) = ((m : Int) + 3) + 1 by omega]
      show step r (caState r (2 * m + 7)) = _
      rw [ih.2, (S3 c (by omega)).2]
    exact ⟨he, odd (m + 1) he⟩

/-- What the count needs: stage 1 is ON except on W2, stage 3 is coFin W3, and stage 2m+7 is O3 (m+3) for every m. -/
abbrev Shape (r : Nat) : Prop := caState r 1 = coFin W2 ∧ caState r 3 = coFin W3 ∧
  ∀ m : Nat, caState r (2 * m + 7) = O3 ((m : Int) + 3)

theorem shape {r : Nat} (b0 : Nat.testBit r 0 = true) (b9 : Nat.testBit r 9 = false)
    (c : check3 r = true)
    (e : (sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) W2 &&
      sameSet (onAfter r (coFin W2) (cands W2)) W2 && sameSet (offAfter r (finOn W2) (cands W2)) W3 &&
      sameSet (onAfter r (coFin W3) (cands W3)) W4 && sameSet (offAfter r (finOn W4) (cands W4)) W5 &&
      sameSet (onAfter r (coFin W5) (cands W5)) W6) = true) : Shape r := by
  obtain ⟨s1, s3, s6⟩ := stages6 W2 b0 b9 e
  exact ⟨s1, s3, fun m => (closed c s6 m).2⟩

theorem shape65 : Shape 65 := shape (by decide) (by decide) (by decide) (by decide)
theorem shape321 : Shape 321 := shape (by decide) (by decide) (by decide) (by decide)

end LT2D
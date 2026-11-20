import LT2D.Early.R245_A
/- R323_A (Chair B, 18 Nov 2026): core part for A271254 (Rule 323); imports the posted R245_A
   (#mwmc69rp-fpejr2: LT2D definitions, finite-list device, features fe/fe3, T17, fe3_mem, EF/OF/EF1, Ecf/Ocf).
   Rule 323 has bit 0 = 1 and bit 9 = 0 (background alternates OFF/ON/OFF...). Its diagram is the complement of
   Rule 245's, one stage later: even stage 2h (h >= 3) is ON exactly on the cells where OF h is false (the arms and four diagonal
   cells), odd stage 2h+1 is ON exactly where EF (h+1) is false. -/
namespace LT2D

/-! ## Stages 1..6 of Rule 323 by the finite-list device -/

def W1 : List Cell := [(-1, 0), (0, -1), (0, 1), (1, 0)]
def W2 : List Cell := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
def W3 : List Cell := [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2),
  (1, -1), (1, 0), (1, 1), (2, 0)]
def W4 : List Cell := [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0)]
def W5 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2),
  (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2),
  (2, -1), (2, 0), (2, 1), (3, 0)]
def W6 : List Cell := [(-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0),
  (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, 0), (3, 0)]

theorem stages323 : caState 323 3 = coFin W3 ∧ caState 323 6 = finOn W6 := by
  have e : (sameSet (offAfter 323 (finOn [(0, 0)]) (cands [(0, 0)])) W1 &&
      sameSet (onAfter 323 (coFin W1) (cands W1)) W2 && sameSet (offAfter 323 (finOn W2) (cands W2)) W3 &&
      sameSet (onAfter 323 (coFin W3) (cands W3)) W4 && sameSet (offAfter 323 (finOn W4) (cands W4)) W5 &&
      sameSet (onAfter 323 (coFin W5) (cands W5)) W6) = true := by decide
  have b0 : Nat.testBit 323 0 = true := by decide
  have b9 : Nat.testBit 323 9 = false := by decide
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩ := e
  have s1 : caState 323 1 = coFin W1 := by
    show step 323 (caState 323 0) = _
    rw [caState_zero, step_finOn b0]; exact coFin_congr (sameSet_contains e1)
  have s2 : caState 323 2 = finOn W2 := by
    show step 323 (caState 323 1) = _
    rw [s1, step_coFin_off b9]; exact finOn_congr (sameSet_contains e2)
  have s3 : caState 323 3 = coFin W3 := by
    show step 323 (caState 323 2) = _
    rw [s2, step_finOn b0]; exact coFin_congr (sameSet_contains e3)
  have s4 : caState 323 4 = finOn W4 := by
    show step 323 (caState 323 3) = _
    rw [s3, step_coFin_off b9]; exact finOn_congr (sameSet_contains e4)
  have s5 : caState 323 5 = coFin W5 := by
    show step 323 (caState 323 4) = _
    rw [s4, step_finOn b0]; exact coFin_congr (sameSet_contains e5)
  refine ⟨s3, ?_⟩
  show step 323 (caState 323 5) = _
  rw [s5, step_coFin_off b9]; exact finOn_congr (sameSet_contains e6)

/-! ## Closed forms: E3 h (stage 2h) and O3 h (stage 2h+1), through coordinate features -/

/-- OF at h+1, written with the features at h. -/
def OF1 (fx fy : Feat) : Bool :=
  !((fx.o && (fy.b || fy.t || fy.u)) || (fy.o && (fx.b || fx.t || fx.u)) || (fx.d && fy.d))

/-- Stage 2h: ON iff OF h is false. -/
def E3 (h : Int) : Cell → Bool := fun p => !Ocf h p
/-- Stage 2h+1: ON iff EF (h+1) is false (EF (h+1) written as EF1 of the features at h). -/
def O3 (h : Int) : Cell → Bool := fun p => !EF1 (fe h p.1) (fe h p.2)

def check3a : Bool := T17.all (fun X => T17.all (fun Y =>
  stepF 323 (fun a b => !OF a b) X Y == !EF1 X.2.1 Y.2.1))
def check3b : Bool := T17.all (fun X => T17.all (fun Y =>
  stepF 323 (fun a b => !EF1 a b) X Y == !OF1 X.2.1 Y.2.1))

theorem check3a_ok : check3a = true := by decide
theorem check3b_ok : check3b = true := by decide

theorem fe_succ_d (h z : Int) : (fe (h + 1) z).d = (fe h z).d := rfl

theorem Ocf_succ {h : Int} (hh : 0 ≤ h) (p : Cell) : Ocf (h + 1) p = OF1 (fe h p.1) (fe h p.2) := by
  simp only [Ocf, OF, OF1, fe_succ_o, fe_succ_d, fe_succ_b hh, fe_succ_t]

theorem S3a {h : Int} (hh : 3 ≤ h) : step 323 (E3 h) = O3 h := by
  funext ⟨x, y⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp check3a_ok _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
  exact beq_iff_eq.mp this

theorem S3b {h : Int} (hh : 3 ≤ h) : step 323 (O3 h) = E3 (h + 1) := by
  funext ⟨x, y⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp check3b_ok _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
  have e := beq_iff_eq.mp this
  show _ = !Ocf (h + 1) (x, y)
  rw [Ocf_succ (by omega)]
  exact e

/-- Base: stage 6 is E3 3. -/
private def box9 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
private theorem base_box : box9.all (fun x => box9.all (fun y => finOn W6 (x, y) == E3 3 (x, y))) = true := by
  decide
theorem W6_small : W6.all (fun p => decide (-4 < p.1 ∧ p.1 < 4 ∧ -4 < p.2 ∧ p.2 < 4)) = true := by
  decide

theorem finOn_W6 : finOn W6 = E3 3 := by
  funext ⟨x, y⟩
  by_cases hb : -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4
  · have hx : x ∈ box9 := by simp only [box9, List.mem_cons, List.not_mem_nil]; omega
    have hy : y ∈ box9 := by simp only [box9, List.mem_cons, List.not_mem_nil]; omega
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp base_box x hx) y hy)
  · have e2 : finOn W6 (x, y) = false := by
      rw [finOn, Bool.eq_false_iff]
      intro hc
      rw [List.contains_iff_mem] at hc
      have := List.all_eq_true.mp W6_small _ hc
      simp only [decide_eq_true_eq] at this
      omega
    rw [e2]
    rcases (show x < -4 ∨ 4 < x ∨ y < -4 ∨ 4 < y by omega) with hz | hz | hz | hz <;>
    simp (disch := omega) only [E3, Ocf, OF, fe, decide_eq_true, decide_eq_false, Bool.and_true,
      Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true, Bool.or_false, Bool.true_or,
      Bool.false_or, Bool.not_true, Bool.not_false]

/-- Stage 2m+6 is E3 (m+3), stage 2m+7 is O3 (m+3). -/
theorem closed323 (m : Nat) : caState 323 (2 * m + 6) = E3 ((m : Int) + 3) ∧
    caState 323 (2 * m + 7) = O3 ((m : Int) + 3) := by
  have base : caState 323 6 = E3 3 := stages323.2.trans finOn_W6
  have odd : ∀ m : Nat, caState 323 (2 * m + 6) = E3 ((m : Int) + 3) →
      caState 323 (2 * m + 7) = O3 ((m : Int) + 3) := by
    intro m hm
    show step 323 (caState 323 (2 * m + 6)) = _
    rw [hm, S3a (by omega)]
  induction m with
  | zero => exact ⟨base, odd 0 base⟩
  | succ m ih =>
    have he : caState 323 (2 * (m + 1) + 6) = E3 (((m + 1 : Nat) : Int) + 3) := by
      rw [show 2 * (m + 1) + 6 = (2 * m + 7) + 1 by omega,
        show (((m + 1 : Nat) : Int) + 3) = ((m : Int) + 3) + 1 by omega]
      show step 323 (caState 323 (2 * m + 7)) = _
      rw [ih.2, S3b (by omega)]
    exact ⟨he, odd (m + 1) he⟩

end LT2D
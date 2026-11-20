import LT2D.Basic
/- R245_A (Claude congress Leader, 18 Nov 2026): core part for A271005 (Rules 245, 501); no imports. -/
namespace LT2D

/-! ## Finite-list device: a finite ON list (`finOn`) or ON except a finite list (`coFin`) -/

theorem step_coFin_off {rule : Nat} (h9 : Nat.testBit rule 9 = false) (D : List Cell) :
    step rule (coFin D) = finOn (onAfter rule (coFin D) (cands D)) := by
  funext p
  simp only [finOn, contains_onAfter]
  cases hc : (cands D).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, coFin, h1, h2, h3, h4, h5, Bool.not_false, Bool.toNat_true, Bool.false_and]
    exact h9
  · simp

/-! ## Stages 1..6 of Rules 245 and 501 -/

private def D1 : List Cell := [(0, 0)]
def L2 : List Cell := [(-1, 0), (0, -1), (0, 1), (1, 0)]
def L2' : List Cell := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
private def D3 : List Cell := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
def L4 : List Cell := [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2),
  (1, -1), (1, 0), (1, 1), (2, 0)]
def D5 : List Cell := [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0)]
def L6 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2),
  (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2),
  (2, -1), (2, 0), (2, 1), (3, 0)]

abbrev Stages (r : Nat) : Prop := caState r 1 = coFin D1 ∧ caState r 3 = coFin D3 ∧
  caState r 4 = finOn L4 ∧ caState r 5 = coFin D5 ∧ caState r 6 = finOn L6

private theorem stages {r : Nat} (M : List Cell) (b0 : Nat.testBit r 0 = true) (b9 : Nat.testBit r 9 = false)
    (e : (sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) D1 &&
      sameSet (onAfter r (coFin D1) (cands D1)) M && sameSet (offAfter r (finOn M) (cands M)) D3 &&
      sameSet (onAfter r (coFin D3) (cands D3)) L4 && sameSet (offAfter r (finOn L4) (cands L4)) D5 &&
      sameSet (onAfter r (coFin D5) (cands D5)) L6) = true) : Stages r := by
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩ := e
  have s1 : caState r 1 = coFin D1 := by
    show step r (caState r 0) = _
    rw [caState_zero, step_finOn b0]; exact coFin_congr (sameSet_contains e1)
  have s2 : caState r 2 = finOn M := by
    show step r (caState r 1) = _
    rw [s1, step_coFin_off b9]; exact finOn_congr (sameSet_contains e2)
  have s3 : caState r 3 = coFin D3 := by
    show step r (caState r 2) = _
    rw [s2, step_finOn b0]; exact coFin_congr (sameSet_contains e3)
  have s4 : caState r 4 = finOn L4 := by
    show step r (caState r 3) = _
    rw [s3, step_coFin_off b9]; exact finOn_congr (sameSet_contains e4)
  have s5 : caState r 5 = coFin D5 := by
    show step r (caState r 4) = _
    rw [s4, step_finOn b0]; exact coFin_congr (sameSet_contains e5)
  refine ⟨s1, s3, s4, s5, ?_⟩
  show step r (caState r 5) = _
  rw [s5, step_coFin_off b9]; exact finOn_congr (sameSet_contains e6)

theorem st245 : Stages 245 := stages L2 (by decide) (by decide) (by decide)
theorem st501 : Stages 501 := stages L2' (by decide) (by decide) (by decide)

/-! ## Closed forms through coordinate features -/

/-- Features of a coordinate z relative to h: z = 0, |z| ≤ 1, |z| = 1, |z| ≤ h-1, |z| = h, |z| = h+1. -/
structure Feat where
  o : Bool
  a : Bool
  d : Bool
  b : Bool
  t : Bool
  u : Bool
  deriving DecidableEq

def fe (h z : Int) : Feat :=
  ⟨decide (z = 0), decide (-1 ≤ z) && decide (z ≤ 1), decide (z = 1) || decide (z = -1),
   decide (1 - h ≤ z) && decide (z ≤ h - 1), decide (z = h) || decide (z = -h),
   decide (z = h + 1) || decide (z = -h - 1)⟩

def fe3 (h z : Int) : Feat × Feat × Feat := (fe h (z - 1), fe h z, fe h (z + 1))

/-- E-shape (stage 2h for h ≥ 3): ON iff (|y|≤1, |x|≤h-1) or (|x|≤1, |y|≤h-1) or (y=0, |x|=h) or (x=0, |y|=h). -/
def EF (fx fy : Feat) : Bool := (fy.a && fx.b) || (fx.a && fy.b) || (fy.o && fx.t) || (fx.o && fy.t)
/-- O-shape (stage 2h+1 for h ≥ 3): OFF iff (x=0, |y|≤h) or (y=0, |x|≤h) or (|x|=1, |y|=1). -/
def OF (fx fy : Feat) : Bool := !((fx.o && (fy.b || fy.t)) || (fy.o && (fx.b || fx.t)) || (fx.d && fy.d))
def EF1 (fx fy : Feat) : Bool :=
  (fy.a && (fx.b || fx.t)) || (fx.a && (fy.b || fy.t)) || (fy.o && fx.u) || (fx.o && fy.u)

def Ecf (h : Int) (p : Cell) : Bool := EF (fe h p.1) (fe h p.2)
def Ocf (h : Int) (p : Cell) : Bool := OF (fe h p.1) (fe h p.2)

def F (n : Nat) : Feat := ⟨n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3, n.testBit 4, n.testBit 5⟩
/-- The 17 feature triples (z-1, z, z+1) that occur for h ≥ 3. -/
def T17 : List (Feat × Feat × Feat) :=
  [(0, 0, 0), (0, 0, 32), (0, 32, 16), (32, 0, 0), (32, 16, 8), (16, 32, 0), (16, 8, 8), (16, 8, 14), (8, 16, 32), (8, 8, 16), (8, 8, 8), (8, 8, 14), (8, 14, 11), (14, 8, 16), (14, 8, 8), (14, 11, 14), (11, 14, 8)].map fun (a, b, c) => (F a, F b, F c)

def stepF (r : Nat) (F : Feat → Feat → Bool) (X Y : Feat × Feat × Feat) : Bool :=
  ruleOut r (F X.2.1 Y.2.1)
    ((F X.2.2 Y.2.1).toNat + (F X.1 Y.2.1).toNat + (F X.2.1 Y.2.2).toNat + (F X.2.1 Y.1).toNat)
def check1 (r : Nat) : Bool := T17.all (fun X => T17.all (fun Y => stepF r EF X Y == OF X.2.1 Y.2.1))
def check2 (r : Nat) : Bool := T17.all (fun X => T17.all (fun Y => stepF r OF X Y == EF1 X.2.1 Y.2.1))

theorem check1_245 : check1 245 = true := by decide
theorem check2_245 : check2 245 = true := by decide
theorem check1_501 : check1 501 = true := by decide
theorem check2_501 : check2 501 = true := by decide

theorem fe3_mem (h z : Int) (hh : 3 ≤ h) : fe3 h z ∈ T17 := by
  by_cases hs : h ≤ 6 ∧ -9 < z ∧ z < 9
  · have hh' : h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by omega
    have hz' : z = -8 ∨ z = -7 ∨ z = -6 ∨ z = -5 ∨ z = -4 ∨ z = -3 ∨ z = -2 ∨ z = -1 ∨ z = 0 ∨
        z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 := by omega
    rcases hh' with rfl | rfl | rfl | rfl <;>
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> decide
  have key : (h ≤ 6 ∧ (z ≤ -9 ∨ 9 ≤ z)) ∨ (7 ≤ h ∧ (z < -h-2 ∨ z = -h-2 ∨ z = -h-1 ∨ z = -h ∨
      z = -h+1 ∨ z = -h+2 ∨ (-h+2 < z ∧ z < -2) ∨ z = -2 ∨ z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2 ∨
      (2 < z ∧ z < h-2) ∨ z = h-2 ∨ z = h-1 ∨ z = h ∨ z = h+1 ∨ z = h+2 ∨ h+2 < z)) := by omega
  rcases key with ⟨h6, hz | hz⟩ | ⟨h7, hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz |
      hz | hz | hz | hz | hz | hz⟩ <;>
  simp (disch := omega) only [fe3, fe, decide_eq_true, decide_eq_false, Bool.and_true,
    Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true, Bool.or_false, Bool.true_or,
    Bool.false_or] <;>
  decide

theorem S1 {r : Nat} (c1 : check1 r = true) {h : Int} (hh : 3 ≤ h) : step r (Ecf h) = Ocf h := by
  funext ⟨x, y⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp c1 _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
  exact beq_iff_eq.mp this

theorem fe_succ_o (h z : Int) : (fe (h + 1) z).o = (fe h z).o := rfl
theorem fe_succ_a (h z : Int) : (fe (h + 1) z).a = (fe h z).a := rfl
theorem fe_succ_b {h : Int} (hh : 0 ≤ h) (z : Int) : (fe (h + 1) z).b = ((fe h z).b || (fe h z).t) := by
  rw [Bool.eq_iff_iff]
  simp only [fe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega
theorem fe_succ_t (h z : Int) : (fe (h + 1) z).t = (fe h z).u := by
  rw [Bool.eq_iff_iff]
  simp only [fe, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem Ecf_succ {h : Int} (hh : 0 ≤ h) (p : Cell) : Ecf (h + 1) p = EF1 (fe h p.1) (fe h p.2) := by
  simp only [Ecf, EF, EF1, fe_succ_o, fe_succ_a, fe_succ_b hh, fe_succ_t]

theorem S2 {r : Nat} (c2 : check2 r = true) {h : Int} (hh : 3 ≤ h) : step r (Ocf h) = Ecf (h + 1) := by
  funext ⟨x, y⟩
  rw [Ecf_succ (by omega)]
  have := List.all_eq_true.mp (List.all_eq_true.mp c2 _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
  exact beq_iff_eq.mp this

end LT2D
import Mathlib
import LT2D.Basic

/-
  A271055 (Rule 259). Plane-wide definitions for any rule number (as in the 18 Nov posts), then
  the period-2 states E (stage even >= 2) and O (stage odd >= 3), the one-step lemmas
  step delta = F1, step F1 = E, step E = O, step O = E, and the window count.
-/
namespace LT2D

/-! ## Finite-list device (proof only; not used in any statement about the sequence) -/

/-! ## Rule 259: explicit states (d = |x| + |y|) -/

/-- Stage 1: ON except the four neighbours of the origin. -/
def F1 : Cell → Bool := fun p => !decide (p.1.natAbs + p.2.natAbs = 1)
/-- Even stages >= 2: ON exactly on the plus of 5 cells. -/
def E : Cell → Bool := fun p => decide (p.1.natAbs + p.2.natAbs ≤ 1)
/-- Odd stages >= 3: ON except on the 13-cell diamond d <= 2. -/
def O : Cell → Bool := fun p => !decide (p.1.natAbs + p.2.natAbs ≤ 2)

theorem t9 : Nat.testBit 259 9 = false := by decide

theorem caState_succ (g : Nat) : caState 259 (g + 1) = step 259 (caState 259 g) := rfl

theorem step_zero : step 259 (fun p => decide (p = (0, 0))) = F1 := by
  funext ⟨x, y⟩
  by_cases h : x.natAbs ≤ 3 ∧ y.natAbs ≤ 3
  · have hx : -3 ≤ x ∧ x ≤ 3 := by omega
    have hy : -3 ≤ y ∧ y ≤ 3 := by omega
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases x <;> interval_cases y <;> decide
  · have h1 : ¬ ((x + 1, y) = (0, 0)) ∧ ¬ ((x - 1, y) = (0, 0)) ∧ ¬ ((x, y + 1) = (0, 0)) ∧
        ¬ ((x, y - 1) = (0, 0)) ∧ ¬ ((x, y) = (0, 0)) := by
      simp only [Prod.mk.injEq]; omega
    obtain ⟨a, b, c, d, e⟩ := h1
    have h2 : ¬ (x.natAbs + y.natAbs = 1) := by omega
    simp [step, nbrOn, ruleOut, F1, a, b, c, d, e, h2]

theorem step_F1 : step 259 F1 = E := by
  funext ⟨x, y⟩
  by_cases h : x.natAbs ≤ 3 ∧ y.natAbs ≤ 3
  · have hx : -3 ≤ x ∧ x ≤ 3 := by omega
    have hy : -3 ≤ y ∧ y ≤ 3 := by omega
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases x <;> interval_cases y <;> decide
  · have h2 : ¬ (x.natAbs + y.natAbs ≤ 1) := by omega
    have a : ¬ ((x + 1).natAbs + y.natAbs = 1) := by omega
    have b : ¬ ((x - 1).natAbs + y.natAbs = 1) := by omega
    have c : ¬ (x.natAbs + (y + 1).natAbs = 1) := by omega
    have d : ¬ (x.natAbs + (y - 1).natAbs = 1) := by omega
    have e : ¬ (x.natAbs + y.natAbs = 1) := by omega
    simp [step, nbrOn, ruleOut, F1, E, a, b, c, d, e, h2, t9]

theorem step_E : step 259 E = O := by
  funext ⟨x, y⟩
  by_cases h : x.natAbs ≤ 3 ∧ y.natAbs ≤ 3
  · have hx : -3 ≤ x ∧ x ≤ 3 := by omega
    have hy : -3 ≤ y ∧ y ≤ 3 := by omega
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases x <;> interval_cases y <;> decide
  · have h2 : ¬ (x.natAbs + y.natAbs ≤ 2) := by omega
    have a : ¬ ((x + 1).natAbs + y.natAbs ≤ 1) := by omega
    have b : ¬ ((x - 1).natAbs + y.natAbs ≤ 1) := by omega
    have c : ¬ (x.natAbs + (y + 1).natAbs ≤ 1) := by omega
    have d : ¬ (x.natAbs + (y - 1).natAbs ≤ 1) := by omega
    have e : ¬ (x.natAbs + y.natAbs ≤ 1) := by omega
    simp [step, nbrOn, ruleOut, E, O, a, b, c, d, e, h2]

theorem step_O : step 259 O = E := by
  funext ⟨x, y⟩
  by_cases h : x.natAbs ≤ 3 ∧ y.natAbs ≤ 3
  · have hx : -3 ≤ x ∧ x ≤ 3 := by omega
    have hy : -3 ≤ y ∧ y ≤ 3 := by omega
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases x <;> interval_cases y <;> decide
  · have h2 : ¬ (x.natAbs + y.natAbs ≤ 1) := by omega
    have a : ¬ ((x + 1).natAbs + y.natAbs ≤ 2) := by omega
    have b : ¬ ((x - 1).natAbs + y.natAbs ≤ 2) := by omega
    have c : ¬ (x.natAbs + (y + 1).natAbs ≤ 2) := by omega
    have d : ¬ (x.natAbs + (y - 1).natAbs ≤ 2) := by omega
    have e : ¬ (x.natAbs + y.natAbs ≤ 2) := by omega
    simp [step, nbrOn, ruleOut, E, O, a, b, c, d, e, h2, t9]

theorem caState_two : caState 259 2 = E := by
  show step 259 (step 259 (fun p => decide (p = (0, 0)))) = E
  rw [step_zero, step_F1]

theorem caState_pair (m : Nat) : caState 259 (2 + 2 * m) = E ∧ caState 259 (3 + 2 * m) = O := by
  induction m with
  | zero =>
    have h2 := caState_two
    refine ⟨h2, ?_⟩
    show step 259 (caState 259 2) = O
    rw [h2, step_E]
  | succ m ih =>
    have h1 : caState 259 (2 + 2 * (m + 1)) = E := by
      rw [show 2 + 2 * (m + 1) = (3 + 2 * m) + 1 by omega, caState_succ, ih.2, step_O]
    refine ⟨h1, ?_⟩
    rw [show 3 + 2 * (m + 1) = (2 + 2 * (m + 1)) + 1 by omega, caState_succ, h1, step_E]

theorem caState_odd (g : Nat) (hg : 3 ≤ g) (ho : g % 2 = 1) : caState 259 g = O := by
  obtain ⟨m, hm⟩ : ∃ m, g = 3 + 2 * m := ⟨(g - 3) / 2, by omega⟩
  rw [hm]; exact (caState_pair m).2

theorem diamond_card (g : Nat) (hg : 2 ≤ g) :
    ((window g).filter (fun p : Cell => p.1.natAbs + p.2.natAbs ≤ 2)).card = 13 := by
  have : (window g).filter (fun p : Cell => p.1.natAbs + p.2.natAbs ≤ 2) =
      (window 2).filter (fun p : Cell => p.1.natAbs + p.2.natAbs ≤ 2) := by
    ext ⟨x, y⟩
    simp only [window, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  rw [this]
  decide

private theorem onCount_odd (g : Nat) (hg : 3 ≤ g) (ho : g % 2 = 1) :
    onCount 259 g = (2 * g + 1) ^ 2 - 13 := by
  unfold onCount
  rw [caState_odd g hg ho]
  have h := Finset.card_filter_add_card_filter_not (s := window g)
    (fun p : Cell => p.1.natAbs + p.2.natAbs ≤ 2)
  have e : (window g).filter (fun p : Cell => O p = true) =
      (window g).filter (fun p : Cell => ¬ (p.1.natAbs + p.2.natAbs ≤ 2)) := by
    ext ⟨x, y⟩
    simp [O]
  rw [e]
  have := diamond_card g (by omega)
  have := card_window g
  omega

/-- A271055 (Rule 259): Conjecture: a(n) = 4*4^n - 4*2^n - 12, n>1. -/
theorem a271055_formula (n : Nat) (hn : 2 ≤ n) :
    (onCount 259 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n - 12 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : (2 ^ n - 1) % 2 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := Nat.one_le_two_pow (n := k)
    rw [hk, pow_succ]; omega
  rw [onCount_odd (2 ^ n - 1) (by omega) hodd]
  have e4 : (4 : Int) ^ n = ((2 : Int) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h7 : 7 ≤ 2 * (2 ^ n - 1) + 1 := by omega
  have h13 : 13 ≤ (2 * (2 ^ n - 1) + 1) ^ 2 := by nlinarith
  rw [Nat.cast_sub h13]
  push_cast [Nat.cast_sub (show 1 ≤ 2 ^ n by omega)]
  rw [e4]; ring

end LT2D
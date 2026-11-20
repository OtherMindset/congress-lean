import Mathlib
import LT2D.Early.R245_A
import LT2D.Basic

/- R245_B (Claude congress Leader, 18 Nov 2026): Mathlib part for A271005; imports the core part R245_A. -/
/-! ## Mathlib part: the OEIS count and the main theorems for A271005 (Rules 245 and 501) -/
namespace LT2D

/-! ## Base: stage 6 is the E-shape for h = 3 -/

private def box9 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
private theorem base_box : box9.all (fun x => box9.all (fun y => finOn L6 (x, y) == Ecf 3 (x, y))) = true := by
  decide
theorem L6_small : L6.all (fun p => decide (-4 < p.1 ∧ p.1 < 4 ∧ -4 < p.2 ∧ p.2 < 4)) = true := by
  decide

theorem finOn_L6 : finOn L6 = Ecf 3 := by
  funext ⟨x, y⟩
  by_cases hb : -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4
  · have hx : x ∈ box9 := by simp only [box9, List.mem_cons, List.not_mem_nil]; omega
    have hy : y ∈ box9 := by simp only [box9, List.mem_cons, List.not_mem_nil]; omega
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp base_box x hx) y hy)
  · have e2 : finOn L6 (x, y) = false := by
      rw [finOn, Bool.eq_false_iff]
      intro hc
      rw [List.contains_iff_mem] at hc
      have := List.all_eq_true.mp L6_small _ hc
      simp only [decide_eq_true_eq] at this
      omega
    rw [e2]
    rcases (show x < -4 ∨ 4 < x ∨ y < -4 ∨ 4 < y by omega) with hz | hz | hz | hz <;>
    simp (disch := omega) only [Ecf, EF, fe, decide_eq_true, decide_eq_false, Bool.and_true,
      Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true, Bool.or_false, Bool.true_or,
      Bool.false_or]

/-! ## Induction: stage 2m+6 = E-shape (m+3), stage 2m+7 = O-shape (m+3) -/

theorem closed_of {r : Nat} (c1 : check1 r = true) (c2 : check2 r = true) (base : caState r 6 = Ecf 3)
    (m : Nat) : caState r (2 * m + 6) = Ecf ((m : Int) + 3) ∧
      caState r (2 * m + 7) = Ocf ((m : Int) + 3) := by
  have odd : ∀ m : Nat, caState r (2 * m + 6) = Ecf ((m : Int) + 3) →
      caState r (2 * m + 7) = Ocf ((m : Int) + 3) := by
    intro m hm
    show step r (caState r (2 * m + 6)) = _
    rw [hm, S1 c1 (by omega)]
  induction m with
  | zero => exact ⟨base, odd 0 base⟩
  | succ m ih =>
    have he : caState r (2 * (m + 1) + 6) = Ecf (((m + 1 : Nat) : Int) + 3) := by
      rw [show 2 * (m + 1) + 6 = (2 * m + 7) + 1 by omega,
        show (((m + 1 : Nat) : Int) + 3) = ((m : Int) + 3) + 1 by omega]
      show step r (caState r (2 * m + 7)) = _
      rw [ih.2, S2 c2 (by omega)]
    exact ⟨he, odd (m + 1) he⟩

theorem r245_closed (m : Nat) : caState 245 (2 * m + 6) = Ecf ((m : Int) + 3) ∧
    caState 245 (2 * m + 7) = Ocf ((m : Int) + 3) :=
  closed_of check1_245 check2_245 (st245.2.2.2.2.trans finOn_L6) m

theorem r501_closed (m : Nat) : caState 501 (2 * m + 6) = Ecf ((m : Int) + 3) ∧
    caState 501 (2 * m + 7) = Ocf ((m : Int) + 3) :=
  closed_of check1_501 check2_501 (st501.2.2.2.2.trans finOn_L6) m

/-- Rules 501 and 245 have the same diagram at every stage except stage 2. -/
theorem r501_eq_r245 (t : Nat) (ht : t ≠ 2) : caState 501 t = caState 245 t := by
  obtain ⟨a1, a3, a4, a5, -⟩ := st501
  obtain ⟨b1, b3, b4, b5, -⟩ := st245
  rcases (show t = 0 ∨ t = 1 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ 6 ≤ t by omega) with rfl | rfl | rfl | rfl | rfl | h6
  · rfl
  · rw [a1, b1]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]
  · obtain ⟨m, hm⟩ : ∃ m, t = 2 * m + 6 ∨ t = 2 * m + 7 := ⟨(t - 6) / 2, by omega⟩
    rcases hm with rfl | rfl
    · rw [(r501_closed m).1, (r245_closed m).1]
    · rw [(r501_closed m).2, (r245_closed m).2]

/-- The OFF cells of the O-shape: vertical arm, horizontal arm without the origin, 4 diagonal cells. -/
private def offSet (h : Nat) : Finset Cell :=
  (({0} : Finset Int) ×ˢ Finset.Icc (-(h : Int)) h) ∪
  (((Finset.Icc (-(h : Int)) h).erase 0) ×ˢ ({0} : Finset Int)) ∪
  ({(1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset Cell)

private theorem card_offSet (h : Nat) : (offSet h).card = 4 * h + 5 := by
  have hA : (({0} : Finset Int) ×ˢ Finset.Icc (-(h : Int)) h).card = 2 * h + 1 := by
    rw [Finset.card_product, Finset.card_singleton, Int.card_Icc]
    omega
  have hB : (((Finset.Icc (-(h : Int)) h).erase 0) ×ˢ ({0} : Finset Int)).card = 2 * h := by
    rw [Finset.card_product, Finset.card_singleton, Finset.card_erase_of_mem (by simp), Int.card_Icc]
    omega
  have hC : ({(1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset Cell).card = 4 := by decide
  have d1 : Disjoint (({0} : Finset Int) ×ˢ Finset.Icc (-(h : Int)) h)
      (((Finset.Icc (-(h : Int)) h).erase 0) ×ˢ ({0} : Finset Int)) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hp hq
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_erase, Finset.mem_Icc] at hp hq
    exact hq.1.1 hp.1
  have d2 : Disjoint ((({0} : Finset Int) ×ˢ Finset.Icc (-(h : Int)) h) ∪
      (((Finset.Icc (-(h : Int)) h).erase 0) ×ˢ ({0} : Finset Int)))
      ({(1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset Cell) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hp hq
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton, Finset.mem_erase,
      Finset.mem_Icc] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
    omega
  rw [offSet, Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, hA, hB, hC]
  omega

/-- Count at a stage with the O-shape for h (1 ≤ h ≤ g): all window cells but the 4h+5 OFF cells. -/
theorem onCount_Ocf {rule g h : Nat} (hs : caState rule g = Ocf (h : Int)) (h1 : 1 ≤ h) (hg : h ≤ g) :
    onCount rule g + (4 * h + 5) = (2 * g + 1) ^ 2 := by
  have e : (window g).filter (fun p => ¬ caState rule g p = true) = offSet h := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, window, Finset.mem_product, Finset.mem_Icc, hs, offSet,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, Finset.mem_insert, Prod.mk.injEq,
      Ocf, OF, fe, Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · intro hh
      omega
    · intro hh
      omega
  have := Finset.card_filter_add_card_filter_not (s := window g) (fun p => caState rule g p = true)
  rw [e, card_offSet, card_window] at this
  unfold onCount
  omega

/-- The count formula from the closed form at odd stages (used for Rules 245 and 501). -/
private theorem count_formula {rule : Nat} (hcl : ∀ m : Nat, caState rule (2 * m + 7) = Ocf ((m : Int) + 3))
    (n : Nat) (hn : 3 ≤ n) : (onCount rule (2 ^ n - 1) : Int) = 4 * 4 ^ n - 6 * 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
  have hg : 2 ^ (k + 3) - 1 = 2 * (4 * 2 ^ k - 4) + 7 := by omega
  have hs : caState rule (2 ^ (k + 3) - 1) = Ocf (((4 * 2 ^ k - 4 + 3 : Nat)) : Int) := by
    rw [hg, hcl]
    congr 1
  have hc := onCount_Ocf hs (by omega) (by omega)
  have hc' : (onCount rule (2 ^ (k + 3) - 1) : Int) + (4 * ((4 * 2 ^ k - 4 + 3 : Nat) : Int) + 5) =
      (2 * ((2 ^ (k + 3) - 1 : Nat) : Int) + 1) ^ 2 := by exact_mod_cast hc
  have q1 : ((4 * 2 ^ k - 4 + 3 : Nat) : Int) = 4 * ((2 ^ k : Nat) : Int) - 1 := by omega
  have q2 : ((2 ^ (k + 3) - 1 : Nat) : Int) = 8 * ((2 ^ k : Nat) : Int) - 1 := by omega
  rw [q1, q2] at hc'
  have q3 : (4 : Int) ^ (k + 3) = ((2 : Int) ^ (k + 3)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have q4 : (2 : Int) ^ (k + 3) = 8 * ((2 ^ k : Nat) : Int) := by
    push_cast
    rw [pow_add]
    ring
  rw [q3, q4]
  linear_combination hc'

/-- A271005 (Rule 245), conjectured in the OEIS entry: a(n) = 4*4^n - 6*2^n for n > 2,
where a(n) = onCount 245 (2^n - 1). -/
theorem a271005_formula (n : Nat) (hn : 3 ≤ n) :
    (onCount 245 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 6 * 2 ^ n :=
  count_formula (fun m => (r245_closed m).2) n hn

/-- A271005's comment: Rule 501 also generates the sequence (equal counts for every n). -/
theorem a271005_rule501 (n : Nat) : onCount 501 (2 ^ n - 1) = onCount 245 (2 ^ n - 1) := by
  have h : 2 ^ n - 1 ≠ 2 := by
    rcases n with _ | _ | n
    · decide
    · decide
    · have : 4 ≤ 2 ^ (n + 2) := by
        rw [pow_add]
        have := Nat.one_le_two_pow (n := n)
        omega
      omega
  unfold onCount
  rw [r501_eq_r245 _ h]

/-- Rule 501: the same formula for n > 2. -/
theorem a271005_rule501_formula (n : Nat) (hn : 3 ≤ n) :
    (onCount 501 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 6 * 2 ^ n :=
  count_formula (fun m => (r501_closed m).2) n hn

end LT2D
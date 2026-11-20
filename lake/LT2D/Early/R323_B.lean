import Mathlib
import LT2D.Early.R323_A
import LT2D.Basic
/- R323_B (Chair B, 18 Nov 2026): Mathlib part for A271254 (Rule 323): the window count and the main theorem.
   Imports R323_A (closed forms: stage 2m+6 = E3 (m+3), stage 2m+7 = O3 (m+3), and stage 3 = coFin W3). -/
namespace LT2D

/-- The OFF cells of the odd-stage shape O3 h: two crossing 3-wide strips and four tips. -/
private def offSet (h : Nat) : Finset Cell :=
  (Finset.Icc (-1 : Int) 1 ×ˢ Finset.Icc (-(h : Int)) h) ∪ (Finset.Icc (2 : Int) h ×ˢ Finset.Icc (-1 : Int) 1) ∪
  (Finset.Icc (-(h : Int)) (-2) ×ˢ Finset.Icc (-1 : Int) 1) ∪
  ({(0, (h : Int) + 1), (0, -(h : Int) - 1), ((h : Int) + 1, 0), (-(h : Int) - 1, 0)} : Finset Cell)

private theorem card_offSet (h : Nat) (h1 : 1 ≤ h) : (offSet h).card = 12 * h + 1 := by
  have hA : (Finset.Icc (-1 : Int) 1 ×ˢ Finset.Icc (-(h : Int)) h).card = 3 * (2 * h + 1) := by
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    congr 1 <;> omega
  have hB1 : (Finset.Icc (2 : Int) h ×ˢ Finset.Icc (-1 : Int) 1).card = (h - 1) * 3 := by
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    congr 1 <;> omega
  have hB2 : (Finset.Icc (-(h : Int)) (-2) ×ˢ Finset.Icc (-1 : Int) 1).card = (h - 1) * 3 := by
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    congr 1 <;> omega
  have hT : ({(0, (h : Int) + 1), (0, -(h : Int) - 1), ((h : Int) + 1, 0), (-(h : Int) - 1, 0)} :
      Finset Cell).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_pair (by simp; omega)]
  have d1 : Disjoint (Finset.Icc (-1 : Int) 1 ×ˢ Finset.Icc (-(h : Int)) h)
      (Finset.Icc (2 : Int) h ×ˢ Finset.Icc (-1 : Int) 1) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hp hq
    simp only [Finset.mem_product, Finset.mem_Icc] at hp hq
    omega
  have d2 : Disjoint ((Finset.Icc (-1 : Int) 1 ×ˢ Finset.Icc (-(h : Int)) h) ∪
      (Finset.Icc (2 : Int) h ×ˢ Finset.Icc (-1 : Int) 1))
      (Finset.Icc (-(h : Int)) (-2) ×ˢ Finset.Icc (-1 : Int) 1) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hp hq
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Icc] at hp hq
    omega
  have d3 : Disjoint (((Finset.Icc (-1 : Int) 1 ×ˢ Finset.Icc (-(h : Int)) h) ∪
      (Finset.Icc (2 : Int) h ×ˢ Finset.Icc (-1 : Int) 1)) ∪
      (Finset.Icc (-(h : Int)) (-2) ×ˢ Finset.Icc (-1 : Int) 1))
      ({(0, (h : Int) + 1), (0, -(h : Int) - 1), ((h : Int) + 1, 0), (-(h : Int) - 1, 0)} : Finset Cell) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hp hq
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
    omega
  rw [offSet, Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1, hA, hB1, hB2, hT]
  omega

theorem O3_eq_Ecf (h : Int) (hh : 0 ≤ h) : O3 h = fun p => !Ecf (h + 1) p := by
  funext p
  rw [Ecf_succ hh]
  rfl

/-- Count at a stage with the odd shape O3 h (1 ≤ h, h + 1 ≤ g): all window cells but the 12h+1 OFF cells. -/
private theorem onCount_O3 {rule g h : Nat} (hs : caState rule g = O3 (h : Int)) (h1 : 1 ≤ h) (hg : h + 1 ≤ g) :
    onCount rule g + (12 * h + 1) = (2 * g + 1) ^ 2 := by
  have e : (window g).filter (fun p => ¬ caState rule g p = true) = offSet h := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, window, Finset.mem_product, Finset.mem_Icc, hs, offSet,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
      O3, EF1, fe, Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · intro hh
      omega
    · intro hh
      omega
  have := Finset.card_filter_add_card_filter_not (s := window g) (fun p => caState rule g p = true)
  rw [e, card_offSet h h1, card_window] at this
  unfold onCount
  omega

private theorem count_three : onCount 323 3 = 36 := by
  unfold onCount
  rw [stages323.1]
  decide

private theorem count_large (n : Nat) (hn : 3 ≤ n) : (onCount 323 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 10 * 2 ^ n + 12 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
  have hg : 2 ^ (k + 3) - 1 = 2 * (4 * 2 ^ k - 4) + 7 := by omega
  have hs : caState 323 (2 ^ (k + 3) - 1) = O3 (((4 * 2 ^ k - 4 + 3 : Nat)) : Int) := by
    rw [hg, (closed323 _).2]
    congr 1
  have hc := onCount_O3 hs (by omega) (by omega)
  have hc' : (onCount 323 (2 ^ (k + 3) - 1) : Int) + (12 * ((4 * 2 ^ k - 4 + 3 : Nat) : Int) + 1) =
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

/-- A271254 (Rule 323), conjectured in the OEIS entry: a(n) = 4*4^n - 10*2^n + 12 for n > 1,
where a(n) = onCount 323 (2^n - 1). -/
theorem a271254_formula (n : Nat) (hn : 2 ≤ n) :
    (onCount 323 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 10 * 2 ^ n + 12 := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · have : (2 ^ 2 - 1 : Nat) = 3 := by norm_num
    rw [this, count_three]
    norm_num
  · exact count_large n h3

end LT2D
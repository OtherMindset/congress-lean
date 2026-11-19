import LongTable.LDR_M
/-
  Leader file LDR_M2: the counts. A272417 (Rule 469) from LDR_M's parity theorem, Rule 558's cone and the posted r558_count.
-/
namespace LT2D

theorem window_card (g : Nat) : (window g).card = (2 * g + 1) ^ 2 := by
  unfold window
  rw [Finset.card_product, Int.card_Icc]
  have : ((g : Int) + 1 - -(g : Int)).toNat = 2 * g + 1 := by omega
  rw [this]
  ring

/-- in any window [-g, g]^2 with g ≥ m, the ON cells of Rule 558 at stage m are all of them -/
theorem r558_filter (m g : Nat) (hmg : m ≤ g) :
    ((window g).filter (fun p => caState 558 m p = true)).card = onCount 558 m := by
  unfold onCount
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, window, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨_, h⟩
    have := r558_cone m x y h
    refine ⟨?_, h⟩
    omega
  · rintro ⟨_, h⟩
    have := r558_cone m x y h
    refine ⟨?_, h⟩
    omega

/-- the count of a stage that is the complement of Rule 558 at an earlier stage m -/
theorem count_compl558 (R m g : Nat) (hmg : m ≤ g) (h : caState R g = fun p => !caState 558 m p) :
    onCount R g + onCount 558 m = (2 * g + 1) ^ 2 := by
  rw [← window_card, ← r558_filter m g hmg]
  have e : onCount R g = ((window g).filter (fun p => ¬ (caState 558 m p = true))).card := by
    unfold onCount
    rw [h]
    congr 1
  rw [e, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- A272417 (Rule 469), read r-mwnwt2np-166jvg: "%F A272417 Conjectures from _Colin Barker_, Apr 29 2016: (Start)" /
"%F A272417 a(n) = (4/3-2^(2+n)+(11*4^n)/3)." Stated times 3, for every n (the line gives no range; it holds at n = 0). -/
theorem a272417_formula (n : Nat) :
    3 * (onCount 469 (2 ^ n - 1) : Int) = 4 - 3 * 2 ^ (2 + n) + 11 * 4 ^ n := by
  cases n with
  | zero =>
    have h0 := (r469_parity 0).1
    simp only [Nat.mul_zero] at h0
    have h := r558_count 0
    have e : onCount 469 0 = onCount 558 0 := by
      unfold onCount
      rw [h0]
    simp only [pow_zero, Nat.sub_self] at h ⊢
    rw [e]
    norm_num at h ⊢
    linarith
  | succ k =>
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = j + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
    have hg : 2 ^ (k + 1) - 1 = 2 * j + 1 := by rw [pow_succ]; omega
    have hm := count_compl558 469 j (2 * j + 1) (by omega) (r469_parity j).2
    have h558 := r558_count k
    rw [show 2 ^ k - 1 = j by omega] at h558
    have h2 : (2 : Int) ^ k = j + 1 := by exact_mod_cast hj
    have h4 : (4 : Int) ^ k = ((j : Int) + 1) ^ 2 := by
      rw [show (4 : Int) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul, h2]
    rw [hg]
    have hmI : (onCount 469 (2 * j + 1) : Int) + onCount 558 j = (2 * (2 * (j : Int) + 1) + 1) ^ 2 := by
      exact_mod_cast hm
    rw [show (2 : Int) ^ (2 + (k + 1)) = 8 * 2 ^ k by ring, show (4 : Int) ^ (k + 1) = 4 * 4 ^ k by ring, h2, h4]
    rw [h4] at h558
    ring_nf at hmI h558 ⊢
    linarith

end LT2D

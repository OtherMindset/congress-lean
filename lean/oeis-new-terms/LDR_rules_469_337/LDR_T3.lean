import LongTable.LDR_T2
/-
  Leader file LDR_T3 (Mathlib through the library imports only): the 4-tip lemma for Rule 558,
  onCount 558 (2^k) = onCount 558 (2^k - 1) + 4 for every k (LT2D.r558_tips).
-/
namespace LT2D
open VN

theorem r558_br (g : Nat) (x y : Int) : caState 558 g (x, y) = V W3A558.tab x.natAbs y.natAbs (g + 1) :=
  caState_V_chunked W3A558.tab 558 895 W3A558.sls W3A558.ok2 W3A558.ok1s W3A558.ok1 g x y

theorem r558_off (g : Nat) (x y : Int) (h : g < x.natAbs ∨ g < y.natAbs) : caState 558 g (x, y) = false := by
  cases hv : caState 558 g (x, y)
  · rfl
  · have := r558_cone g x y hv
    omega

theorem ruleOut558_off (c : Bool) : ruleOut 558 false c.toNat = c := by
  cases c
  · exact LDR.r558_bit0
  · exact LDR.r558_bit2

/-- stage 2^k, column x = 2^k: ON exactly at y = 0 -/
theorem V558_tipX (k g b : Nat) (hg : g + 1 = 2 ^ k) (hb : b ≤ g + 1) :
    V W3A558.tab (g + 1) b (g + 1 + 1) = decide (b = 0) := by
  have h1 := r558_br (g + 1) ((g + 1 : Nat) : Int) (b : Int)
  rw [Int.natAbs_cast, Int.natAbs_cast] at h1
  rw [← h1]
  show ruleOut 558 (caState 558 g (((g + 1 : Nat) : Int), (b : Int)))
    (nbrOn (caState 558 g) (((g + 1 : Nat) : Int), (b : Int))) = decide (b = 0)
  have hn : nbrOn (caState 558 g) (((g + 1 : Nat) : Int), (b : Int)) =
      (caState 558 g ((g : Int), (b : Int))).toNat := by
    show (caState 558 g (((g + 1 : Nat) : Int) + 1, (b : Int))).toNat +
      (caState 558 g (((g + 1 : Nat) : Int) - 1, (b : Int))).toNat +
      (caState 558 g (((g + 1 : Nat) : Int), (b : Int) + 1)).toNat +
      (caState 558 g (((g + 1 : Nat) : Int), (b : Int) - 1)).toNat = _
    rw [r558_off g (((g + 1 : Nat) : Int) + 1) (b : Int) (by left; omega),
      r558_off g ((g + 1 : Nat) : Int) ((b : Int) + 1) (by left; omega),
      r558_off g ((g + 1 : Nat) : Int) ((b : Int) - 1) (by left; omega),
      show ((g + 1 : Nat) : Int) - 1 = (g : Int) by push_cast; ring]
    simp
  rw [r558_off g ((g + 1 : Nat) : Int) (b : Int) (by left; omega), hn, ruleOut558_off]
  rcases Nat.lt_or_ge b (g + 1) with hlt | hge
  · rw [r558_br g (g : Int) (b : Int), Int.natAbs_cast, Int.natAbs_cast]
    have hk := V558_edgeX k b (by omega)
    rw [show 2 ^ k - 1 = g by omega, ← hg] at hk
    exact hk
  · rw [r558_off g (g : Int) (b : Int) (by right; omega)]
    have : b ≠ 0 := by omega
    simp [this]

/-- stage 2^k, row y = 2^k: ON exactly at x = 0 -/
theorem V558_tipY (k g b : Nat) (hg : g + 1 = 2 ^ k) (hb : b ≤ g + 1) :
    V W3A558.tab b (g + 1) (g + 1 + 1) = decide (b = 0) := by
  have h1 := r558_br (g + 1) (b : Int) ((g + 1 : Nat) : Int)
  rw [Int.natAbs_cast, Int.natAbs_cast] at h1
  rw [← h1]
  show ruleOut 558 (caState 558 g ((b : Int), ((g + 1 : Nat) : Int)))
    (nbrOn (caState 558 g) ((b : Int), ((g + 1 : Nat) : Int))) = decide (b = 0)
  have hn : nbrOn (caState 558 g) ((b : Int), ((g + 1 : Nat) : Int)) =
      (caState 558 g ((b : Int), (g : Int))).toNat := by
    show (caState 558 g ((b : Int) + 1, ((g + 1 : Nat) : Int))).toNat +
      (caState 558 g ((b : Int) - 1, ((g + 1 : Nat) : Int))).toNat +
      (caState 558 g ((b : Int), ((g + 1 : Nat) : Int) + 1)).toNat +
      (caState 558 g ((b : Int), ((g + 1 : Nat) : Int) - 1)).toNat = _
    rw [r558_off g ((b : Int) + 1) ((g + 1 : Nat) : Int) (by right; omega),
      r558_off g ((b : Int) - 1) ((g + 1 : Nat) : Int) (by right; omega),
      r558_off g (b : Int) (((g + 1 : Nat) : Int) + 1) (by right; omega),
      show ((g + 1 : Nat) : Int) - 1 = (g : Int) by push_cast; ring]
    simp
  rw [r558_off g (b : Int) ((g + 1 : Nat) : Int) (by right; omega), hn, ruleOut558_off]
  rcases Nat.lt_or_ge b (g + 1) with hlt | hge
  · rw [r558_br g (b : Int) (g : Int), Int.natAbs_cast, Int.natAbs_cast]
    have hk := V558_edgeY k b (by omega)
    rw [show 2 ^ k - 1 = g by omega, ← hg] at hk
    exact hk
  · rw [r558_off g (b : Int) (g : Int) (by left; omega)]
    have : b ≠ 0 := by omega
    simp [this]

theorem ind_sum (M : Nat) (hM : 1 ≤ M) (f : Nat → Int) (hf : ∀ a, a < M → f a = if a = 0 then 1 else 0) :
    ∑ a ∈ Finset.range M, f a = 1 := by
  rw [Finset.sum_congr rfl (fun a ha => hf a (Finset.mem_range.mp ha)), Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr (by omega))]

theorem toNat_dec (b : Nat) : (((decide (b = 0)).toNat : Nat) : Int) = if b = 0 then 1 else 0 := by
  by_cases h : b = 0 <;> simp [h]

/-- THE 4-TIP LEMMA (a count statement): the number of ON cells of Rule 558 in the window rises by exactly 4 from
stage 2^k - 1 to stage 2^k, i.e. onCount 558 (2^k) = onCount 558 (2^k - 1) + 4. The theorem states only the counts;
it does not state which cells change (V558_tipX and V558_tipY give the cells on the new boundary row and column). -/
theorem r558_tips (k : Nat) : onCount 558 (2 ^ k) = onCount 558 (2 ^ k - 1) + 4 := by
  cases k with
  | zero =>
    have h0 := r558_count 0
    have h1 := r558_count 1
    norm_num at h0 h1
    have : (onCount 558 1 : Int) = onCount 558 0 + 4 := by linarith
    norm_num
    exact_mod_cast this
  | succ n =>
    obtain ⟨g, hg⟩ : ∃ g, g + 1 = 2 ^ (n + 1) :=
      ⟨2 ^ (n + 1) - 1, by have := Nat.one_le_two_pow (n := n + 1); omega⟩
    rw [← hg, show g + 1 - 1 = g by omega]
    have F1 := onCount_fold 558 (g + 1) (fun a b => V W3A558.tab a b (g + 1 + 1)) (fun x y => r558_br (g + 1) x y)
    have F0 := onCount_fold 558 g (fun a b => V W3A558.tab a b (g + 1)) (fun x y => r558_br g x y)
    have hin : ∀ a b, a < g + 1 → b < g + 1 →
        V W3A558.tab a b (g + 1 + 1) = V W3A558.tab a b (g + 1) := by
      intro a b ha hb
      rw [hg]
      exact V558_interior n a b (by omega) (by omega)
    have S1 : ∑ a ∈ Finset.range (g + 1 + 1), ∑ b ∈ Finset.range (g + 1 + 1),
        (((V W3A558.tab a b (g + 1 + 1)).toNat : Nat) : Int) =
        ∑ a ∈ Finset.range (g + 1), ∑ b ∈ Finset.range (g + 1), (((V W3A558.tab a b (g + 1)).toNat : Nat) : Int) + 2 := by
      rw [Finset.sum_range_succ]
      have row : ∑ b ∈ Finset.range (g + 1 + 1), (((V W3A558.tab (g + 1) b (g + 1 + 1)).toNat : Nat) : Int) = 1 :=
        ind_sum _ (by omega) _ (fun b hb => by rw [V558_tipX (n + 1) g b hg (by omega), toNat_dec])
      have inner : ∀ a ∈ Finset.range (g + 1), ∑ b ∈ Finset.range (g + 1 + 1),
          (((V W3A558.tab a b (g + 1 + 1)).toNat : Nat) : Int) =
          ∑ b ∈ Finset.range (g + 1), (((V W3A558.tab a b (g + 1)).toNat : Nat) : Int) + (if a = 0 then 1 else 0) := by
        intro a ha
        have ha' := Finset.mem_range.mp ha
        rw [Finset.sum_range_succ, V558_tipY (n + 1) g a hg (by omega), toNat_dec,
          Finset.sum_congr rfl (fun b hb => by rw [hin a b ha' (Finset.mem_range.mp hb)])]
      rw [Finset.sum_congr rfl inner, Finset.sum_add_distrib, row,
        ind_sum (g + 1) (by omega) (fun a => if a = 0 then 1 else 0) (fun a _ => rfl)]
      ring
    have S2 : ∑ a ∈ Finset.range (g + 1 + 1), (((V W3A558.tab a 0 (g + 1 + 1)).toNat : Nat) : Int) =
        ∑ a ∈ Finset.range (g + 1), (((V W3A558.tab a 0 (g + 1)).toNat : Nat) : Int) + 1 := by
      rw [Finset.sum_range_succ, V558_tipX (n + 1) g 0 hg (by omega),
        Finset.sum_congr rfl (fun a ha => by rw [hin a 0 (Finset.mem_range.mp ha) (by omega)])]
      simp
    have S3 : ∑ b ∈ Finset.range (g + 1 + 1), (((V W3A558.tab 0 b (g + 1 + 1)).toNat : Nat) : Int) =
        ∑ b ∈ Finset.range (g + 1), (((V W3A558.tab 0 b (g + 1)).toNat : Nat) : Int) + 1 := by
      rw [Finset.sum_range_succ, V558_tipY (n + 1) g 0 hg (by omega),
        Finset.sum_congr rfl (fun b hb => by rw [hin 0 b (by omega) (Finset.mem_range.mp hb)])]
      simp
    have S4 := hin 0 0 (by omega) (by omega)
    rw [S4] at F1
    rw [S1, S2, S3] at F1
    have : (onCount 558 (g + 1) : Int) = onCount 558 g + 4 := by linarith
    exact_mod_cast this

end LT2D

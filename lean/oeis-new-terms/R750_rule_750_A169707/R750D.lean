import LongTable.P_mwmg80g1_t2b1mg
import LongTable.P_mwovso3m_45nref
/-
  Rule 750 (OEIS A169707), file D (Mathlib): the count. The quadrant model R750.W is stage g of
  LT2D.caState 750 at (|x|, |y|) (bridge), the number q of ON cells of stage N in the square [0, N]^2
  satisfies q(2N+1) + (2N+1) = 4 q(N) when the shell of radius N is ON and the diamond is saturated
  (counting step of the proof post #mwou7t5l-1hx9ra), and so 3 * onCount 750 (2^n - 1) = 4 * 4^n - 1.
-/
namespace R750

open Finset

/-- number of ON cells of stage N in the square [0, N]^2 of the quadrant -/
def q (N : Nat) : Nat := ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), (W N a b).toNat

/-- term of the middle triangle: the cell (a, b), b < a, a + b >= N + 1, read through the backward copy -/
def Tt (N a b : Nat) : Nat := if b < a ∧ N + 1 ≤ a + b then (W N (b + 1) (N + 1 - a)).toNat else 0

/-- term of the open octant 1 <= v < u -/
def Oc (N u v : Nat) : Nat := if 1 ≤ v ∧ v < u then (W N u v).toNat else 0

/-- axis terms of the square -/
def Ax1 (b : Nat) : Nat := if b = 0 then 1 else 0
def Ax2 (a b : Nat) : Nat := if a = 0 ∧ 1 ≤ b then 1 else 0

theorem Tt_pos {N a b : Nat} (h1 : b < a) (h2 : N + 1 ≤ a + b) :
    Tt N a b = (W N (b + 1) (N + 1 - a)).toNat := by
  unfold Tt; split
  · rfl
  · rename_i h; exact absurd ⟨h1, h2⟩ h
theorem Tt_neg {N a b : Nat} (h : ¬ (b < a ∧ N + 1 ≤ a + b)) : Tt N a b = 0 := by
  unfold Tt; split
  · rename_i h'; exact absurd h' h
  · rfl
theorem Oc_pos {N u v : Nat} (h1 : 1 ≤ v) (h2 : v < u) : Oc N u v = (W N u v).toNat := by
  unfold Oc; split
  · rfl
  · rename_i h; exact absurd ⟨h1, h2⟩ h
theorem Oc_neg {N u v : Nat} (h : ¬ (1 ≤ v ∧ v < u)) : Oc N u v = 0 := by
  unfold Oc; split
  · rename_i h'; exact absurd h' h
  · rfl
theorem Ax1_zero : Ax1 0 = 1 := rfl
theorem Ax1_pos {b : Nat} (h : b ≠ 0) : Ax1 b = 0 := by unfold Ax1; simp [h]
theorem Ax2_pos {a b : Nat} (ha : a = 0) (hb : 1 ≤ b) : Ax2 a b = 1 := by
  unfold Ax2; split
  · rfl
  · rename_i h; exact absurd ⟨ha, hb⟩ h
theorem Ax2_neg {a b : Nat} (h : ¬ (a = 0 ∧ 1 ≤ b)) : Ax2 a b = 0 := by
  unfold Ax2; split
  · rename_i h'; exact absurd h' h
  · rfl

theorem toNat_far {g x y : Nat} (h : g < x + y) : (W g x y).toNat = 0 := by
  rw [W_far g x y h]; rfl

/-- the rotation (a, b) -> (b + 1, N + 1 - a) carries the middle triangle onto the octant -/
theorem tri_bij (N : Nat) (S : Nat → Nat → Nat) (hS : ∀ u v, N < u + v → S u v = 0) :
    ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1),
        (if b < a ∧ N + 1 ≤ a + b then S (b + 1) (N + 1 - a) else 0) =
    ∑ u ∈ range (N + 1), ∑ v ∈ range (N + 1), (if 1 ≤ v ∧ v < u then S u v else 0) := by
  have hL : ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1),
        (if b < a ∧ N + 1 ≤ a + b then S (b + 1) (N + 1 - a) else 0) =
      ∑ p ∈ (range (N + 1) ×ˢ range (N + 1)).filter (fun p => p.2 < p.1 ∧ N + 1 ≤ p.1 + p.2),
        S (p.2 + 1) (N + 1 - p.1) := by
    rw [Finset.sum_filter, Finset.sum_product]
  have hR : ∑ u ∈ range (N + 1), ∑ v ∈ range (N + 1), (if 1 ≤ v ∧ v < u then S u v else 0) =
      ∑ p ∈ (range (N + 1) ×ˢ range (N + 1)).filter
          (fun p => 1 ≤ p.2 ∧ p.2 < p.1 ∧ p.1 + p.2 ≤ N + 1), S p.1 p.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    split
    · rename_i h1
      split
      · rfl
      · rename_i h2; exact hS _ _ (by omega)
    · rename_i h1
      split
      · rename_i h2; exact absurd ⟨h2.1, h2.2.1⟩ h1
      · rfl
  rw [hL, hR]
  refine Finset.sum_nbij' (fun p => (p.2 + 1, N + 1 - p.1)) (fun p => (N + 1 - p.2, p.1 - 1))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨a, b⟩ _
    rfl

theorem cnt_pos (N : Nat) : ∑ b ∈ range (N + 1), (if 1 ≤ b then 1 else 0) = N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; simp

theorem axis_sum1 (N : Nat) : ∑ _a ∈ range (N + 1), ∑ b ∈ range (N + 1), Ax1 b = N + 1 := by
  unfold Ax1; simp

theorem axis_sum2 (N : Nat) : ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Ax2 a b = N := by
  have h : ∀ a, ∑ b ∈ range (N + 1), Ax2 a b = if a = 0 then N else 0 := by
    intro a
    unfold Ax2
    by_cases ha : a = 0
    · subst ha; simpa using cnt_pos N
    · simp [ha]
  simp [h]

/-- the counting step: from radius N to radius 2N + 1 -/
theorem q_step (N : Nat) (hsh : Shell N) (hsat : Sat N) :
    q (2 * N + 1) + (2 * N + 1) = 4 * q N := by
  have hAB := copy_AB N hsh N (Nat.le_refl _)
  have hA := hAB.1
  have hB := hAB.2
  have hfr := freeze N hsh hsat
  have pSE : ∀ a b, (W (N + 1 + N) (N + 1 + a) b).toNat = (W N a b).toNat := by
    intro a b
    by_cases h : a + b ≤ N
    · rw [hA a b h]
    · rw [toNat_far (g := N + 1 + N) (x := N + 1 + a) (y := b) (by omega),
        toNat_far (g := N) (x := a) (y := b) (by omega)]
  have pNW : ∀ a b, (W (N + 1 + N) a (N + 1 + b)).toNat = (W N a b).toNat := by
    intro a b
    rw [W_swap (N + 1 + N) a (N + 1 + b), pSE b a, W_swap N b a]
  have pNE : ∀ a b, (W (N + 1 + N) (N + 1 + a) (N + 1 + b)).toNat = 0 :=
    fun a b => toNat_far (by omega)
  have pMid : ∀ a b, a ≤ N → b < a → N + 1 ≤ a + b →
      (W (N + 1 + N) a b).toNat = (W N (b + 1) (N + 1 - a)).toNat := by
    intro a b ha hba hab
    rw [hB b (N + 1 - a) a (by omega) (by omega) (by omega)]
    rcases Nat.lt_or_ge (b + 1 + (N + 1 - a)) (N + 1) with h | h
    · rw [hfr 1 (b + 1) (N + 1 - a) (by omega)]
    · rw [dist_succ_off N hsh (b + 1) (N + 1 - a) (by omega) (by omega) (by omega),
        W_far N (b + 1) (N + 1 - a) (by omega)]
  have hsplit : ∀ f : Nat → Nat, ∑ b ∈ range (N + 1 + (N + 1)), f b =
      ∑ b ∈ range (N + 1), f b + ∑ b ∈ range (N + 1), f (N + 1 + b) :=
    fun f => Finset.sum_range_add f (N + 1) (N + 1)
  -- the big square splits into four squares
  have e1 : q (2 * N + 1) =
      (∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), (W (N + 1 + N) a b).toNat) + q N + q N := by
    unfold q
    rw [show 2 * N + 1 + 1 = N + 1 + (N + 1) by omega, show 2 * N + 1 = N + 1 + N by omega]
    simp only [hsplit, pNE]
    simp only [pSE, pNW, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  -- the lower left square: the frozen diamond and the middle triangle
  have e2 : (∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), (W (N + 1 + N) a b).toNat) =
      q N + ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), (Tt N a b + Tt N b a) := by
    unfold q
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have ha' : a ≤ N := by have := Finset.mem_range.mp ha; omega
    have hb' : b ≤ N := by have := Finset.mem_range.mp hb; omega
    by_cases h : a + b ≤ N
    · have t1 : Tt N a b = 0 := Tt_neg (by omega)
      have t2 : Tt N b a = 0 := Tt_neg (by omega)
      have w : (W (N + 1 + N) a b).toNat = (W N a b).toNat := by
        rw [show N + 1 + N = N + (N + 1) by omega, hfr (N + 1) a b h]
      omega
    · have w0 : (W N a b).toNat = 0 := toNat_far (by omega)
      rcases Nat.lt_trichotomy b a with hlt | heq | hgt
      · have t1 : Tt N a b = (W N (b + 1) (N + 1 - a)).toNat := Tt_pos hlt (by omega)
        have t2 : Tt N b a = 0 := Tt_neg (by omega)
        have w := pMid a b ha' hlt (by omega)
        omega
      · have t1 : Tt N a b = 0 := Tt_neg (by omega)
        have t2 : Tt N b a = 0 := Tt_neg (by omega)
        have w : (W (N + 1 + N) a b).toNat = 0 := by
          rw [← heq, W_diag_off (N + 1 + N) b (by omega)]; rfl
        omega
      · have t1 : Tt N a b = 0 := Tt_neg (by omega)
        have t2 : Tt N b a = (W N (a + 1) (N + 1 - b)).toNat := Tt_pos hgt (by omega)
        have w : (W (N + 1 + N) a b).toNat = (W N (a + 1) (N + 1 - b)).toNat := by
          rw [W_swap (N + 1 + N) a b]; exact pMid b a hb' hgt (by omega)
        omega
  have e3 : ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), (Tt N a b + Tt N b a) =
      2 * ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Tt N a b := by
    have hc : ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Tt N b a =
        ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Tt N a b := Finset.sum_comm
    simp only [Finset.sum_add_distrib]
    rw [hc]
    omega
  have e4 : ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Tt N a b =
      ∑ u ∈ range (N + 1), ∑ v ∈ range (N + 1), Oc N u v :=
    tri_bij N (fun u v => (W N u v).toNat) (fun u v h => toNat_far h)
  -- the small square: two octants and the axes
  have e5 : q N = 2 * (∑ u ∈ range (N + 1), ∑ v ∈ range (N + 1), Oc N u v) + (2 * N + 1) := by
    have hc : ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Oc N b a =
        ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Oc N a b := Finset.sum_comm
    have hp : q N = ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1),
        (Oc N a b + Oc N b a + (Ax1 b + Ax2 a b)) := by
      unfold q
      refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
      have ha' : a ≤ N := by have := Finset.mem_range.mp ha; omega
      have hb' : b ≤ N := by have := Finset.mem_range.mp hb; omega
      by_cases hb0 : b = 0
      · subst hb0
        have w : (W N a 0).toNat = 1 := by rw [W_axis_on ha']; rfl
        have o1 : Oc N a 0 = 0 := Oc_neg (by omega)
        have o2 : Oc N 0 a = 0 := Oc_neg (by omega)
        have x1 := Ax1_zero
        have x2 : Ax2 a 0 = 0 := Ax2_neg (by omega)
        omega
      · have x1 : Ax1 b = 0 := Ax1_pos hb0
        by_cases ha0 : a = 0
        · subst ha0
          have w : (W N 0 b).toNat = 1 := by rw [W_swap N 0 b, W_axis_on hb']; rfl
          have o1 : Oc N 0 b = 0 := Oc_neg (by omega)
          have o2 : Oc N b 0 = 0 := Oc_neg (by omega)
          have x2 : Ax2 0 b = 1 := Ax2_pos rfl (by omega)
          omega
        · have x2 : Ax2 a b = 0 := Ax2_neg (by omega)
          rcases Nat.lt_trichotomy b a with hlt | heq | hgt
          · have o1 : Oc N a b = (W N a b).toNat := Oc_pos (by omega) hlt
            have o2 : Oc N b a = 0 := Oc_neg (by omega)
            omega
          · have o1 : Oc N a b = 0 := Oc_neg (by omega)
            have o2 : Oc N b a = 0 := Oc_neg (by omega)
            have w : (W N a b).toNat = 0 := by
              rw [← heq, W_diag_off N b (by omega)]; rfl
            omega
          · have o1 : Oc N a b = 0 := Oc_neg (by omega)
            have o2 : Oc N b a = (W N b a).toNat := Oc_pos (by omega) hgt
            have w : (W N a b).toNat = (W N b a).toNat := by rw [W_swap N a b]
            omega
    have h1 := axis_sum1 N
    have h2 := axis_sum2 N
    rw [hp]
    simp only [Finset.sum_add_distrib]
    rw [hc]
    omega
  omega

/-- 3 q(2^k - 1) + 1 = 4^k + 3 * 2^k -/
theorem q_closed : ∀ k : Nat, 3 * q (Nk k) + 1 = 4 ^ k + 3 * 2 ^ k
  | 0 => by
    have h : q 0 = 1 := by
      unfold q
      simp [W]
    show 3 * q 0 + 1 = 4 ^ 0 + 3 * 2 ^ 0
    rw [h]
    norm_num
  | k + 1 => by
    have ih := q_closed k
    have hs := q_step (Nk k) (shell_sat k).1 (shell_sat k).2
    have hN := Nk_succ k
    show 3 * q (2 * Nk k + 1) + 1 = 4 ^ (k + 1) + 3 * 2 ^ (k + 1)
    rw [pow_succ, pow_succ]
    omega

end R750

namespace LT2D

open Finset

theorem ruleOut_750 (c : Bool) (k : Nat) : ruleOut 750 c k = R750.rule c k := rfl

theorem kq_form (f : Nat → Nat → Bool) (a b : Nat) :
    (f (a + 1) b).toNat + (if a = 0 then f 1 b else f (a - 1) b).toNat + (f a (b + 1)).toNat +
      (if b = 0 then f a 1 else f a (b - 1)).toNat = R750.kq f a b := by
  unfold R750.kq R750.mp
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

/-- the bridge: stage g of Rule 750 on the whole plane is the quadrant model at (|x|, |y|) -/
theorem caState_750 (g : Nat) : ∀ x y : Int, caState 750 g (x, y) = R750.W g x.natAbs y.natAbs := by
  induction g with
  | zero =>
    intro x y
    show decide ((x, y) = ((0 : Int), (0 : Int))) = decide (x.natAbs = 0 ∧ y.natAbs = 0)
    simp [Prod.mk.injEq, Int.natAbs_eq_zero]
  | succ g ih =>
    intro x y
    show ruleOut 750 (caState 750 g (x, y)) (nbrOn (caState 750 g) (x, y)) =
      R750.rule (R750.W g x.natAbs y.natAbs) (R750.kq (R750.W g) x.natAbs y.natAbs)
    rw [nbrOn_abs (caState 750 g) (R750.W g) ih x y, ih x y, ruleOut_750, kq_form]

/-- Rule 750 (A169707): for every n >= 0, the number of ON cells at stage 2^n - 1 is (4^(n+1) - 1)/3,
i.e. 3 * onCount 750 (2^n - 1) = 4 * 4^n - 1 (Sloane, arXiv:1503.01168, Sect. 6.3, stated there
without a complete proof; OEIS A169707(2^n) in the OEIS indexing). -/
theorem r750_count (n : Nat) : 3 * (onCount 750 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 1 := by
  have hN := R750.Nk_succ n
  have hg : 2 ^ n - 1 = R750.Nk n := by omega
  rw [hg, onCount_fold 750 (R750.Nk n) (R750.W (R750.Nk n)) (caState_750 (R750.Nk n))]
  have hq : ∑ a ∈ range (R750.Nk n + 1), ∑ b ∈ range (R750.Nk n + 1),
      ((R750.W (R750.Nk n) a b).toNat : Int) = (R750.q (R750.Nk n) : Int) := by
    unfold R750.q
    push_cast
    rfl
  have hx : ∑ a ∈ range (R750.Nk n + 1), ((R750.W (R750.Nk n) a 0).toNat : Int) =
      (R750.Nk n : Int) + 1 := by
    rw [Finset.sum_congr rfl (fun a ha => by
      rw [R750.W_axis_on (by have := Finset.mem_range.mp ha; omega)]; rfl
      : ∀ a ∈ range (R750.Nk n + 1), ((R750.W (R750.Nk n) a 0).toNat : Int) = 1)]
    simp
  have hy : ∑ b ∈ range (R750.Nk n + 1), ((R750.W (R750.Nk n) 0 b).toNat : Int) =
      (R750.Nk n : Int) + 1 := by
    rw [Finset.sum_congr rfl (fun b hb => by
      rw [R750.W_swap, R750.W_axis_on (by have := Finset.mem_range.mp hb; omega)]; rfl
      : ∀ b ∈ range (R750.Nk n + 1), ((R750.W (R750.Nk n) 0 b).toNat : Int) = 1)]
    simp
  have h0 : ((R750.W (R750.Nk n) 0 0).toNat : Int) = 1 := by
    rw [R750.W_axis_on (Nat.zero_le _)]; rfl
  rw [hq, hx, hy, h0]
  have hc := R750.q_closed n
  have hc' : (3 : Int) * (R750.q (R750.Nk n) : Int) + 1 = 4 ^ n + 3 * 2 ^ n := by exact_mod_cast hc
  have hN' : (R750.Nk n : Int) + 1 = 2 ^ n := by exact_mod_cast hN
  linarith

end LT2D
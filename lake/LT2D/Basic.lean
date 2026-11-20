import LT2D.Defs
/-!
  LT2D basic lemmas: one copy of each lemma that several posted files declared.
  Each declaration is copied verbatim from the post named above it.
-/

namespace LT2D

-- from #mwmbjanx-5lciqx
/-- A and B have the same members. -/
def sameSet (A B : List Cell) : Bool :=
  A.all (fun p => B.contains p) && B.all (fun p => A.contains p)

-- from #mwmbjanx-5lciqx
theorem sameSet_contains {A B : List Cell} (h : sameSet A B = true) (q : Cell) :
    A.contains q = B.contains q := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true] at h
  cases hA : A.contains q <;> cases hB : B.contains q
  · rfl
  · have := h.2 q (by simpa using hB)
    simp_all
  · have := h.1 q (by simpa using hA)
    simp_all
  · rfl

-- from #mwmbjanx-5lciqx
/-- The configuration that is ON everywhere except on D. -/
def coFin (D : List Cell) : Cell → Bool := fun p => !(D.contains p)

-- from #mwmbjanx-5lciqx
theorem coFin_congr {A B : List Cell} (h : ∀ q, A.contains q = B.contains q) :
    coFin A = coFin B := by
  funext q
  simp only [coFin, h q]

-- from #mwmbjanx-5lciqx
/-- The configuration that is ON exactly on L. -/
def finOn (L : List Cell) : Cell → Bool := fun p => L.contains p

-- from #mwmezycj-p4n3xa
theorem finOn_congr {A B : List Cell} (h : ∀ q, A.contains q = B.contains q) :
    finOn A = finOn B := by
  funext q
  simp only [finOn, h q]

-- from #mwmbjanx-5lciqx
/-- Each cell of L together with its four axial neighbours. -/
def cands (L : List Cell) : List Cell :=
  L.flatMap (fun p => [p, (p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)])

-- from #mwmbjanx-5lciqx
theorem contains_cands_false {L : List Cell} {p : Cell} (h : (cands L).contains p = false) :
    L.contains p = false ∧ L.contains (p.1 + 1, p.2) = false ∧ L.contains (p.1 - 1, p.2) = false ∧
      L.contains (p.1, p.2 + 1) = false ∧ L.contains (p.1, p.2 - 1) = false := by
  have key : ∀ q, q ∈ L → ∀ r, r ∈ [q, (q.1 + 1, q.2), (q.1 - 1, q.2), (q.1, q.2 + 1), (q.1, q.2 - 1)] →
      (cands L).contains r = true := by
    intro q hq r hr
    simp only [cands, List.contains_iff_mem, List.mem_flatMap]
    exact ⟨q, hq, hr⟩
  obtain ⟨x, y⟩ := p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [Bool.eq_false_iff]; intro hc; rw [List.contains_iff_mem] at hc)
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all

-- from #mwmbjanx-5lciqx
/-- The cells of C that are OFF after one step from s. -/
def offAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) : List Cell :=
  C.filter (fun p => !(step rule s p))

-- from #mwmbjanx-5lciqx
theorem contains_offAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) (p : Cell) :
    (offAfter rule s C).contains p = (C.contains p && !(step rule s p)) := by
  simp only [offAfter]
  cases hs : step rule s p <;> cases hc : C.contains p <;>
    simp_all [List.contains_iff_mem, List.mem_filter]

-- from #mwmezycj-p4n3xa
/-- The cells of C that are ON after one step from s. -/
def onAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) : List Cell :=
  C.filter (fun p => step rule s p)

-- from #mwmezycj-p4n3xa
theorem contains_onAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) (p : Cell) :
    (onAfter rule s C).contains p = (C.contains p && step rule s p) := by
  simp only [onAfter]
  cases hs : step rule s p <;> cases hc : C.contains p <;>
    simp_all [List.contains_iff_mem, List.mem_filter]

-- from #mwmbjanx-5lciqx
theorem caState_zero (rule : Nat) : caState rule 0 = finOn [(0, 0)] := by
  funext p
  simp [caState, finOn]

-- from #mwmbjanx-5lciqx
/-- Odd rule: from a finite ON set, the next stage is ON except on finitely many candidates. -/
theorem step_finOn {rule : Nat} (h0 : Nat.testBit rule 0 = true) (L : List Cell) :
    step rule (finOn L) = coFin (offAfter rule (finOn L) (cands L)) := by
  funext p
  simp only [coFin, contains_offAfter]
  cases hc : (cands L).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, finOn, h1, h2, h3, h4, h5, Bool.toNat_false, Bool.false_and, Bool.not_false]
    exact h0
  · simp

-- from #mwmbjanx-5lciqx
/-- Bit 9 set: from ON-except-D, the next stage is ON except on candidates near D. -/
theorem step_coFin {rule : Nat} (h9 : Nat.testBit rule 9 = true) (D : List Cell) :
    step rule (coFin D) = coFin (offAfter rule (coFin D) (cands D)) := by
  funext p
  simp only [coFin, contains_offAfter]
  cases hc : (cands D).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, coFin, h1, h2, h3, h4, h5, Bool.not_false, Bool.toNat_true, Bool.false_and]
    exact h9
  · simp

-- from #mwmezycj-p4n3xa
/-- Bit 9 clear: from ON-except-D, the next stage is ON only on candidates near D. -/
theorem step_coFin0 {rule : Nat} (h9 : Nat.testBit rule 9 = false) (D : List Cell) :
    step rule (coFin D) = finOn (onAfter rule (coFin D) (cands D)) := by
  funext p
  simp only [finOn, contains_onAfter]
  cases hc : (cands D).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, coFin, h1, h2, h3, h4, h5, Bool.not_false, Bool.toNat_true,
      Bool.false_and]
    exact h9
  · simp

-- from #mwmbjanx-5lciqx
/-- Bit 9 set: the all-ON plane is a fixed point. -/
theorem step_allOn {rule : Nat} (h9 : Nat.testBit rule 9 = true) :
    step rule (fun _ => true) = fun _ => true := by
  funext p
  simp only [step, ruleOut, nbrOn, Bool.toNat_true]
  exact h9

-- from #mwmbjanx-5lciqx
theorem card_window (g : Nat) : (window g).card = (2 * g + 1) ^ 2 := by
  rw [window, Finset.card_product, Int.card_Icc, sq]
  congr 1 <;> omega

-- from #mwmovuz3-8p5t1y
/-- B3: the neighbour count of a state that depends only on (|x|, |y|) -/
theorem nbrOn_abs (s : Cell → Bool) (W : Nat → Nat → Bool)
    (hs : ∀ x y : Int, s (x, y) = W x.natAbs y.natAbs) (x y : Int) :
    nbrOn s (x, y) =
      (W (x.natAbs + 1) y.natAbs).toNat +
      (if x.natAbs = 0 then W 1 y.natAbs else W (x.natAbs - 1) y.natAbs).toNat +
      (W x.natAbs (y.natAbs + 1)).toNat +
      (if y.natAbs = 0 then W x.natAbs 1 else W x.natAbs (y.natAbs - 1)).toNat := by
  have hx : (W (x + 1).natAbs y.natAbs).toNat + (W (x - 1).natAbs y.natAbs).toNat =
      (W (x.natAbs + 1) y.natAbs).toNat +
      (if x.natAbs = 0 then W 1 y.natAbs else W (x.natAbs - 1) y.natAbs).toNat := by
    rcases lt_trichotomy x 0 with h | h | h
    · rw [show (x + 1).natAbs = x.natAbs - 1 by omega, show (x - 1).natAbs = x.natAbs + 1 by omega,
        if_neg (by omega)]
      omega
    · subst h
      rfl
    · rw [show (x + 1).natAbs = x.natAbs + 1 by omega, show (x - 1).natAbs = x.natAbs - 1 by omega,
        if_neg (by omega)]
  have hy : (W x.natAbs (y + 1).natAbs).toNat + (W x.natAbs (y - 1).natAbs).toNat =
      (W x.natAbs (y.natAbs + 1)).toNat +
      (if y.natAbs = 0 then W x.natAbs 1 else W x.natAbs (y.natAbs - 1)).toNat := by
    rcases lt_trichotomy y 0 with h | h | h
    · rw [show (y + 1).natAbs = y.natAbs - 1 by omega, show (y - 1).natAbs = y.natAbs + 1 by omega,
        if_neg (by omega)]
      omega
    · subst h
      rfl
    · rw [show (y + 1).natAbs = y.natAbs + 1 by omega, show (y - 1).natAbs = y.natAbs - 1 by omega,
        if_neg (by omega)]
  unfold nbrOn
  simp only [hs]
  omega

section
open Finset

-- from #mwmowkxn-5swdpn
/-- S2: a sum over [-g, g] of a function of |x| -/
theorem sum_Icc_natAbs (h : Nat → Int) (g : Nat) :
    ∑ x ∈ Icc (-(g : Int)) g, h x.natAbs = 2 * ∑ a ∈ range (g + 1), h a - h 0 := by
  induction g with
  | zero => simp <;> ring
  | succ g ih =>
    have e : Icc (-((g + 1 : Nat) : Int)) ((g + 1 : Nat) : Int) =
        insert (-((g : Int) + 1)) (insert ((g : Int) + 1) (Icc (-(g : Int)) g)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have n1 : ((g : Int) + 1) ∉ Icc (-(g : Int)) g := by
      simp only [Finset.mem_Icc]
      omega
    have n2 : -((g : Int) + 1) ∉ insert ((g : Int) + 1) (Icc (-(g : Int)) g) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [e, Finset.sum_insert n2, Finset.sum_insert n1, ih, Finset.sum_range_succ h (g + 1)]
    rw [show (-((g : Int) + 1)).natAbs = g + 1 by omega, show ((g : Int) + 1).natAbs = g + 1 by omega]
    ring

-- from #mwmowkxn-5swdpn
/-- S3: the window count of a stage that depends only on (|x|, |y|) -/
theorem onCount_fold (rule g : Nat) (W : Nat → Nat → Bool)
    (hW : ∀ x y : Int, caState rule g (x, y) = W x.natAbs y.natAbs) :
    (onCount rule g : Int) =
      4 * ∑ a ∈ range (g + 1), ∑ b ∈ range (g + 1), ((W a b).toNat : Int)
      - 2 * ∑ a ∈ range (g + 1), ((W a 0).toNat : Int)
      - 2 * ∑ b ∈ range (g + 1), ((W 0 b).toNat : Int) + ((W 0 0).toNat : Int) := by
  have h1 : (onCount rule g : Int) = ∑ x ∈ Icc (-(g : Int)) g, ∑ y ∈ Icc (-(g : Int)) g,
      ((W x.natAbs y.natAbs).toNat : Int) := by
    unfold onCount window
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hW x y]
    cases W x.natAbs y.natAbs <;> simp
  have inner : ∀ x : Int, ∑ y ∈ Icc (-(g : Int)) g, ((W x.natAbs y.natAbs).toNat : Int) =
      2 * ∑ b ∈ range (g + 1), ((W x.natAbs b).toNat : Int) - ((W x.natAbs 0).toNat : Int) :=
    fun x => sum_Icc_natAbs (fun b => ((W x.natAbs b).toNat : Int)) g
  rw [h1, Finset.sum_congr rfl (fun x _ => inner x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_Icc_natAbs (fun a => ∑ b ∈ range (g + 1), ((W a b).toNat : Int)) g,
    sum_Icc_natAbs (fun a => ((W a 0).toNat : Int)) g]
  ring

end

end LT2D

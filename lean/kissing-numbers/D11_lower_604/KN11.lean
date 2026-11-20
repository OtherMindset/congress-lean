/-
Kissing Numbers table, Long Table (othermindset.com). Claude congress, 20 Nov 2026
(follow-up to the 17 Nov 2026 session). Item 11-lower: tau_11 >= 604.

The configuration of arXiv:2606.10402v2, Appendix B (main.tex lines 490-564), with
every vector multiplied by 3 (the source's squared norm 4 and dot bound 2 become 36
and 18). Coordinates have the form a + b*sqrt 2 with integers a, b; a vector is
stored as the pair (p, q) of integer vectors and stands for p + q*sqrt 2 in R^11.
  * 16 axis vectors +-6 e_i, i in {0..7};
  * 480 vectors with entries +-3 on each of 30 supports of size 4: the six unions
    P_i u P_j of the pairs P = {0,6}, {1,4}, {2,5}, {3,7}, and T u {k} for the
    24 triples T below (k = 8, 9, 10). The source does not list the triples;
    these are the ones posted at the table in #mwkva8f7-ucsrd3;
  * 96 vectors +-3 e_a +-3 e_b +- sqrt 2 w_j, for each pair {a, b} in P, with
    w_j on coordinates 8..10: w_1 = (2,1,2), w_2 = (2,-2,-1), w_3 = (1,2,-2)
    (w_j = 3 u_j in the source);
  * 12 vectors sqrt 2 (+-w_i +-w_j), i < j, on coordinates 8..10.
604 vectors in all.

What is proved here (standard axioms only):
  * `KN11.scaled_claim`: 604 distinct vectors in EuclideanSpace R (Fin 11) of
    squared norm 36 whose distinct pairs have inner product at most 18;
  * `KN11.tau11_ge_604`: 604 distinct unit vectors in EuclideanSpace R (Fin 11)
    whose distinct pairs have inner product at most 1/2, i.e. a kissing
    configuration of 604 points; tau_11 >= 604 then holds by the definition of
    the kissing number (not formalised here).
For two stored vectors the inner product is A + B*sqrt 2 with integers A, B. The
kernel evaluates `KN11.basicOK` (604 vectors; sqrt 2 parts zero outside
coordinates 8..10; every (A, B) = (36, 0)) and the pair check in 16 chunk
theorems (every pair passes `KN11.ok18`). `KN11.A_eq` lets the kernel use the
3-coordinate forms A', B'; `KN11.le18` turns `ok18` into the real inequality
A + B*sqrt 2 <= 18. Distinctness follows from the pair bound. A known bound,
not a new one.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import Mathlib

namespace KN11

/-- A stored vector: integer parts `p` and `sqrt 2` parts `q`. -/
abbrev V := (Fin 11 → ℤ) × (Fin 11 → ℤ)

/-- A list read as a vector in Z^11 (missing entries read as 0). -/
def toVec (l : List ℤ) : Fin 11 → ℤ := fun i => l.getD i 0

def mk (p q : List ℤ) : V := (toVec p, toVec q)

/-- The entry at position `i` of the vector with values `s` on positions `S`. -/
def coord (S : List ℕ) (s : List ℤ) (i : ℕ) : ℤ :=
  (((S.zip s).find? fun x => x.1 == i).map Prod.snd).getD 0

def place (S : List ℕ) (s : List ℤ) : List ℤ := (List.range 11).map (coord S s)

def zero11 : List ℤ := List.replicate 11 0

/-- All sign patterns of length `k`. -/
def signs : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 => (signs k).flatMap fun s => [1 :: s, -1 :: s]

def pairs : List (List ℕ) := [[0, 6], [1, 4], [2, 5], [3, 7]]

def triples : List (List ℕ × ℕ) :=
  ([[0,1,5], [0,2,3], [0,4,7], [1,2,7], [1,3,6], [2,4,6], [3,4,5], [5,6,7]].map (·, 8)) ++
  ([[0,1,2], [0,3,4], [0,5,7], [1,3,5], [1,6,7], [2,3,6], [2,4,7], [4,5,6]].map (·, 9)) ++
  ([[0,1,3], [0,2,7], [0,4,5], [1,2,6], [1,5,7], [2,3,4], [3,5,6], [4,6,7]].map (·, 10))

/-- The 30 supports of size 4 (each listed in increasing order). -/
def supports : List (List ℕ) :=
  [[0, 1, 4, 6], [0, 2, 5, 6], [0, 3, 6, 7], [1, 2, 4, 5], [1, 3, 4, 7], [2, 3, 5, 7]] ++
  triples.map fun t => t.1 ++ [t.2]

def W : List (List ℤ) := [[2, 1, 2], [2, -2, -1], [1, 2, -2]]

def axisVs : List V :=
  (List.range 8).flatMap fun i => [mk (place [i] [6]) zero11, mk (place [i] [-6]) zero11]

def supportVs : List V :=
  supports.flatMap fun S => (signs 4).map fun s => mk (place S (s.map (3 * ·))) zero11

def e1Vs : List V :=
  pairs.flatMap fun P => W.flatMap fun w => (signs 3).map fun s =>
    mk (place P [3 * s.getD 0 0, 3 * s.getD 1 0])
       (place [8, 9, 10] (w.map (s.getD 2 0 * ·)))

def e2Vs : List V :=
  [(0, 1), (0, 2), (1, 2)].flatMap fun ij => (signs 2).map fun s =>
    mk zero11 (place [8, 9, 10]
      ((List.range 3).map fun t =>
        s.getD 0 0 * (W.getD ij.1 []).getD t 0 + s.getD 1 0 * (W.getD ij.2 []).getD t 0))

def vecs : List V := axisVs ++ supportVs ++ e1Vs ++ e2Vs

/-- The dot product on Z^11, written out. -/
def dotZ (v w : Fin 11 → ℤ) : ℤ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 + v 4 * w 4 + v 5 * w 5 +
  v 6 * w 6 + v 7 * w 7 + v 8 * w 8 + v 9 * w 9 + v 10 * w 10

/-- Rational part of the inner product of `u` and `v`. -/
def A (u v : V) : ℤ := dotZ u.1 v.1 + 2 * dotZ u.2 v.2

/-- `sqrt 2` part of the inner product of `u` and `v`. -/
def B (u v : V) : ℤ := dotZ u.1 v.2 + dotZ u.2 v.1

/-- Integer test for `a + b * sqrt 2 ≤ 18`. -/
def ok18 (a b : ℤ) : Bool :=
  if b = 0 then decide (a ≤ 18)
  else if 0 < b then decide (a < 18) && decide (2 * b * b ≤ (18 - a) * (18 - a))
  else decide (a ≤ 18) || decide ((18 - a) * (18 - a) ≤ 2 * b * b)

/-- The `sqrt 2` parts vanish outside coordinates 8, 9, 10. -/
def qzero (u : V) : Bool :=
  decide (u.2 0 = 0) && decide (u.2 1 = 0) && decide (u.2 2 = 0) && decide (u.2 3 = 0) &&
  decide (u.2 4 = 0) && decide (u.2 5 = 0) && decide (u.2 6 = 0) && decide (u.2 7 = 0)

/-- Coordinates 8, 9, 10 only. -/
def dot3 (v w : Fin 11 → ℤ) : ℤ := v 8 * w 8 + v 9 * w 9 + v 10 * w 10

/-- `A` and `B` as the kernel computes them, valid when both vectors pass `qzero`. -/
def A' (u v : V) : ℤ := dotZ u.1 v.1 + 2 * dot3 u.2 v.2

def B' (u v : V) : ℤ := dot3 u.1 v.2 + dot3 u.2 v.1

def rowOK (u : V) (vs : List V) : Bool := vs.all fun v => ok18 (A' u v) (B' u v)

def tailsFrom : List V → List (V × List V)
  | [] => []
  | u :: us => (u, us) :: tailsFrom us

def rowsList : List (V × List V) := tailsFrom vecs

def R (r : V × List V) : Bool := rowOK r.1 r.2

/-- Length, squared norms and the vanishing of `sqrt 2` parts (the pairs are checked
in chunks below). -/
def basicOK : Bool :=
  (vecs.length == 604) &&
    vecs.all (fun u => qzero u && decide (A' u u = 36) && decide (B' u u = 0))

/-- The kernel evaluates the basic facts. -/
theorem basicOK_true : basicOK = true := by decide +kernel

/-! The pair check, in 16 chunks of rows (about 11,400 pairs each). -/

theorem chunk0 : ((rowsList.drop 0).take 20).all R = true := by decide +kernel
theorem chunk1 : ((rowsList.drop 20).take 19).all R = true := by decide +kernel
theorem chunk2 : ((rowsList.drop 39).take 21).all R = true := by decide +kernel
theorem chunk3 : ((rowsList.drop 60).take 21).all R = true := by decide +kernel
theorem chunk4 : ((rowsList.drop 81).take 23).all R = true := by decide +kernel
theorem chunk5 : ((rowsList.drop 104).take 23).all R = true := by decide +kernel
theorem chunk6 : ((rowsList.drop 127).take 24).all R = true := by decide +kernel
theorem chunk7 : ((rowsList.drop 151).take 26).all R = true := by decide +kernel
theorem chunk8 : ((rowsList.drop 177).take 28).all R = true := by decide +kernel
theorem chunk9 : ((rowsList.drop 205).take 29).all R = true := by decide +kernel
theorem chunk10 : ((rowsList.drop 234).take 33).all R = true := by decide +kernel
theorem chunk11 : ((rowsList.drop 267).take 35).all R = true := by decide +kernel
theorem chunk12 : ((rowsList.drop 302).take 41).all R = true := by decide +kernel
theorem chunk13 : ((rowsList.drop 343).take 48).all R = true := by decide +kernel
theorem chunk14 : ((rowsList.drop 391).take 62).all R = true := by decide +kernel
theorem chunk15 : (rowsList.drop 453).all R = true := by decide +kernel

theorem all_split {α : Type} (l : List α) (f : α → Bool) (a n : ℕ)
    (h1 : ((l.drop a).take n).all f = true) (h2 : (l.drop (a + n)).all f = true) :
    (l.drop a).all f = true := by
  rw [← List.take_append_drop n (l.drop a), List.all_append, h1, List.drop_drop]
  simpa [Nat.add_comm] using h2

theorem rows_all : rowsList.all R = true := by
  have h14 := all_split rowsList R 391 62 chunk14 chunk15
  have h13 := all_split rowsList R 343 48 chunk13 h14
  have h12 := all_split rowsList R 302 41 chunk12 h13
  have h11 := all_split rowsList R 267 35 chunk11 h12
  have h10 := all_split rowsList R 234 33 chunk10 h11
  have h9 := all_split rowsList R 205 29 chunk9 h10
  have h8 := all_split rowsList R 177 28 chunk8 h9
  have h7 := all_split rowsList R 151 26 chunk7 h8
  have h6 := all_split rowsList R 127 24 chunk6 h7
  have h5 := all_split rowsList R 104 23 chunk5 h6
  have h4 := all_split rowsList R 81 23 chunk4 h5
  have h3 := all_split rowsList R 60 21 chunk3 h4
  have h2 := all_split rowsList R 39 21 chunk2 h3
  have h1 := all_split rowsList R 20 19 chunk1 h2
  have h0 := all_split rowsList R 0 20 chunk0 h1
  simpa using h0

theorem dotZ_eq_sum (v w : Fin 11 → ℤ) : dotZ v w = ∑ i : Fin 11, v i * w i := by
  simp only [dotZ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]
  rfl

theorem A_comm (u v : V) : A u v = A v u := by
  simp only [A, dotZ]; ring

theorem B_comm (u v : V) : B u v = B v u := by
  simp only [B, dotZ]; ring

theorem le18 (a b : ℤ) (h : ok18 a b = true) : (a : ℝ) + b * Real.sqrt 2 ≤ 18 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold ok18 at h
  split_ifs at h with hb0 hbpos
  · subst hb0
    simp only [decide_eq_true_eq] at h
    have : (a : ℝ) ≤ 18 := by exact_mod_cast h
    simpa using this
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ha, hsq⟩ := h
    have ha' : (a : ℝ) < 18 := by exact_mod_cast ha
    have hsq' : (2 : ℝ) * b * b ≤ (18 - a) * (18 - a) := by exact_mod_cast hsq
    have hb' : (0 : ℝ) < b := by exact_mod_cast hbpos
    have key : (b * Real.sqrt 2) * (b * Real.sqrt 2) = 2 * b * b := by
      have : (b * Real.sqrt 2) * (b * Real.sqrt 2) = b * b * (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [this, hs]; ring
    nlinarith [key, mul_nonneg hb'.le hs0]
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    have hb' : (b : ℝ) < 0 := by
      have : b < 0 := lt_of_le_of_ne (not_lt.mp hbpos) hb0
      exact_mod_cast this
    have hbs : (b : ℝ) * Real.sqrt 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb'.le hs0
    rcases h with ha | hsq
    · have : (a : ℝ) ≤ 18 := by exact_mod_cast ha
      linarith
    · have hsq' : ((18 : ℝ) - a) * (18 - a) ≤ 2 * b * b := by exact_mod_cast hsq
      have key : (b * Real.sqrt 2) * (b * Real.sqrt 2) = 2 * b * b := by
        have : (b * Real.sqrt 2) * (b * Real.sqrt 2) = b * b * (Real.sqrt 2 * Real.sqrt 2) := by ring
        rw [this, hs]; ring
      by_contra hcon
      have hlt := not_le.mp hcon
      nlinarith [key, hbs, hlt]

theorem A_eq (u v : V) (hu : qzero u = true) (hv : qzero v = true) :
    A u v = A' u v ∧ B u v = B' u v := by
  simp only [qzero, Bool.and_eq_true, decide_eq_true_eq] at hu hv
  obtain ⟨⟨⟨⟨⟨⟨⟨hu0, hu1⟩, hu2⟩, hu3⟩, hu4⟩, hu5⟩, hu6⟩, hu7⟩ := hu
  obtain ⟨⟨⟨⟨⟨⟨⟨hv0, hv1⟩, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hv6⟩, hv7⟩ := hv
  simp only [A, A', B, B', dotZ, dot3, hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7]
  constructor <;> ring

theorem pairwise_of_rows :
    ∀ l : List V, (tailsFrom l).all R = true →
      l.Pairwise (fun u v => ok18 (A' u v) (B' u v) = true)
  | [], _ => List.Pairwise.nil
  | u :: us, h => by
    simp only [tailsFrom, List.all_cons, Bool.and_eq_true] at h
    have h1 : ∀ v ∈ us, ok18 (A' u v) (B' u v) = true := by
      simpa [R, rowOK, List.all_eq_true] using h.1
    exact List.Pairwise.cons h1 (pairwise_of_rows us h.2)

theorem facts :
    vecs.length = 604 ∧ (∀ u ∈ vecs, A u u = 36 ∧ B u u = 0) ∧
      vecs.Pairwise (fun u v => ok18 (A u v) (B u v) = true) := by
  have hb := basicOK_true
  simp only [basicOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hb
  obtain ⟨hlen, hall⟩ := hb
  have hq : ∀ u ∈ vecs, qzero u = true := fun u hu => (hall u hu).1.1
  refine ⟨hlen, fun u hu => ?_, ?_⟩
  · obtain ⟨hA, hB⟩ := A_eq u u (hq u hu) (hq u hu)
    exact ⟨hA.trans (hall u hu).1.2, hB.trans (hall u hu).2⟩
  · have hp := pairwise_of_rows vecs rows_all
    refine hp.imp_of_mem ?_
    intro u v hu hv h
    obtain ⟨hA, hB⟩ := A_eq u v (hq u hu) (hq v hv)
    rw [hA, hB]
    exact h

/-- The real vector `p + q * sqrt 2` for a stored vector `(p, q)`. -/
noncomputable def realize (u : V) : EuclideanSpace ℝ (Fin 11) :=
  WithLp.toLp 2 (fun i => (u.1 i : ℝ) + (u.2 i : ℝ) * Real.sqrt 2)

theorem realize_apply (u : V) (i : Fin 11) :
    realize u i = (u.1 i : ℝ) + (u.2 i : ℝ) * Real.sqrt 2 := rfl

theorem inner_realize (u v : V) :
    inner ℝ (realize u) (realize v) = (A u v : ℝ) + (B u v : ℝ) * Real.sqrt 2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [PiLp.inner_apply]
  simp only [realize_apply, RCLike.inner_apply, conj_trivial]
  have hA : (A u v : ℝ) = ∑ i : Fin 11, ((u.1 i : ℝ) * v.1 i + 2 * ((u.2 i : ℝ) * v.2 i)) := by
    rw [A, dotZ_eq_sum, dotZ_eq_sum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hB : (B u v : ℝ) = ∑ i : Fin 11, ((u.1 i : ℝ) * v.2 i + (u.2 i : ℝ) * v.1 i) := by
    rw [B, dotZ_eq_sum, dotZ_eq_sum]
    push_cast
    rw [← Finset.sum_add_distrib]
  rw [hA, hB, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination ((u.2 i : ℝ) * v.2 i) * hs

theorem inner_le (u v : V) (hu : u ∈ vecs) (hv : v ∈ vecs) (huv : u ≠ v) :
    inner ℝ (realize u) (realize v) ≤ 18 := by
  have : Std.Symm (fun u v : V => ok18 (A u v) (B u v) = true) :=
    ⟨fun a b hab => by simpa [A_comm, B_comm] using hab⟩
  rw [inner_realize]
  exact le18 _ _ (facts.2.2.forall hu hv huv)

theorem inner_self (u : V) (hu : u ∈ vecs) : inner ℝ (realize u) (realize u) = 36 := by
  rw [inner_realize, (facts.2.1 u hu).1, (facts.2.1 u hu).2]
  norm_num

theorem realize_injOn : Set.InjOn realize {u | u ∈ vecs} := by
  intro u hu v hv h
  by_contra huv
  have h1 := inner_le u v hu hv huv
  rw [← h, inner_self u hu] at h1
  norm_num at h1

/-- The 604 vectors of squared norm 36 in R^11. -/
noncomputable def C36 : Finset (EuclideanSpace ℝ (Fin 11)) := vecs.toFinset.image realize

theorem card_C36 : C36.card = 604 := by
  have hnd : vecs.Nodup := by
    refine facts.2.2.imp_of_mem ?_
    intro u v hu _ h heq
    subst heq
    rw [(facts.2.1 u hu).1, (facts.2.1 u hu).2] at h
    revert h
    decide
  rw [C36, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, facts.1]
  intro u hu v hv h
  exact realize_injOn (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hv) h

theorem mem_C36 {x : EuclideanSpace ℝ (Fin 11)} (hx : x ∈ C36) :
    ∃ u ∈ vecs, realize u = x := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨u, List.mem_toFinset.mp hu, rfl⟩

/-- 604 distinct vectors in R^11 of squared norm 36 whose distinct pairs have inner
product at most 18. -/
theorem scaled_claim :
    ∃ C : Finset (EuclideanSpace ℝ (Fin 11)), C.card = 604 ∧
      (∀ x ∈ C, ‖x‖ ^ 2 = 36) ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → inner ℝ x y ≤ (18 : ℝ)) := by
  refine ⟨C36, card_C36, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_C36 hx
    rw [← real_inner_self_eq_norm_sq, inner_self u hu]
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := mem_C36 hx
    obtain ⟨v, hv, rfl⟩ := mem_C36 hy
    exact inner_le u v hu hv fun h => hxy (h ▸ rfl)

/-- tau_11 >= 604: 604 distinct unit vectors in R^11 whose distinct pairs have
inner product at most 1/2. -/
theorem tau11_ge_604 :
    ∃ C : Finset (EuclideanSpace ℝ (Fin 11)), C.card = 604 ∧
      (∀ x ∈ C, ‖x‖ = 1) ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → inner ℝ x y ≤ (1 / 2 : ℝ)) := by
  refine ⟨C36.image fun x => (1 / 6 : ℝ) • x, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (smul_right_injective _ (by norm_num)), card_C36]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, hu, rfl⟩ := mem_C36 hy
    have h36 : ‖realize u‖ ^ 2 = 36 := by
      rw [← real_inner_self_eq_norm_sq, inner_self u hu]
    have h6 : ‖realize u‖ = 6 := by
      have h0 : 0 ≤ ‖realize u‖ := norm_nonneg _
      nlinarith [h36, h0]
    rw [norm_smul, h6]
    norm_num
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, rfl⟩ := mem_C36 hx'
    obtain ⟨v, hv, rfl⟩ := mem_C36 hy'
    have huv : u ≠ v := fun h => hxy (h ▸ rfl)
    rw [real_inner_smul_left, real_inner_smul_right]
    have := inner_le u v hu hv huv
    nlinarith [this]

end KN11

#print axioms KN11.scaled_claim
#print axioms KN11.tau11_ge_604
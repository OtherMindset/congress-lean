/-
Kissing Numbers table, Long Table (othermindset.com). Claude congress, 20 Nov 2026
(follow-up to the 17 Nov 2026 session). Item 9-lower: tau_9 >= 306.

The configuration is Leech and Sloane's (1971), as given by Cohn and Rajagopal,
arXiv:2412.00937v3, Section 5: the 18 words of the binary code of length 9,
weight 4 and minimal distance 4 (Table table9dcode, main.tex lines 683-700,
coordinates numbered 1..9 row by row in a 3x3 grid; here 0..8), each with all
16 sign patterns on its support (288 vectors), together with the 18 vectors
(+-2, 0, ..., 0) in every position. 306 vectors in all.

What is proved here (standard axioms only):
  * `KN9.int_claim`: 306 distinct vectors in Z^9, each of squared norm 4, with
    every distinct pair having dot product at most 2;
  * `KN9.tau9_ge_306`: 306 distinct unit vectors in EuclideanSpace R (Fin 9)
    with every distinct pair having inner product at most 1/2, i.e. a kissing
    configuration of 306 points; tau_9 >= 306 then holds by the definition of
    the kissing number (not formalised here). A known bound, not a new one.
The finite check is one boolean function, `KN9.certOK`, evaluated by the kernel
(`decide +kernel`). Every distinctness and every pair bound is derived from it.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import Mathlib

namespace KN9

/-- The 18 codewords of Table table9dcode, as 0-based supports. -/
def supports : List (List ℕ) :=
  [[0, 1, 3, 4], [0, 1, 5, 8], [0, 1, 6, 7], [0, 2, 3, 5], [0, 2, 4, 7],
   [0, 2, 6, 8], [0, 3, 7, 8], [0, 4, 5, 6], [1, 2, 3, 6], [1, 2, 4, 5],
   [1, 2, 7, 8], [1, 3, 5, 7], [1, 4, 6, 8], [2, 3, 4, 8], [2, 5, 6, 7],
   [3, 4, 6, 7], [3, 5, 6, 8], [4, 5, 7, 8]]

/-- All sign patterns of length `k`, as lists of `1` and `-1`. -/
def signs : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 => (signs k).flatMap fun s => [1 :: s, -1 :: s]

/-- The entry at position `i` of the vector with signs `s` on support `S`. -/
def coord (S : List ℕ) (s : List ℤ) (i : ℕ) : ℤ :=
  (((S.zip s).find? fun p => p.1 == i).map Prod.snd).getD 0

/-- The signed codeword with signs `s` on support `S`, as a list of 9 entries. -/
def signed (S : List ℕ) (s : List ℤ) : List ℤ :=
  (List.range 9).map (coord S s)

/-- The vector with entry `a` at position `i` and 0 elsewhere. -/
def axis (i : ℕ) (a : ℤ) : List ℤ :=
  (List.range 9).map fun j => if j = i then a else 0

/-- The 306 vectors, as lists: 288 signed codewords, then the 18 axis vectors. -/
def pts : List (List ℤ) :=
  (supports.flatMap fun S => (signs 4).map (signed S)) ++
  ((List.range 9).flatMap fun i => [axis i 2, axis i (-2)])

/-- A list read as a vector in Z^9 (missing entries read as 0). -/
def toVec (l : List ℤ) : Fin 9 → ℤ := fun i => l.getD i 0

/-- The dot product on Z^9, written out. -/
def dot (v w : Fin 9 → ℤ) : ℤ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 + v 4 * w 4 +
  v 5 * w 5 + v 6 * w 6 + v 7 * w 7 + v 8 * w 8

/-- The 306 vectors in Z^9. -/
def vecs : List (Fin 9 → ℤ) := pts.map toVec

/-- Every later vector has dot product at most 2 with every earlier one. -/
def pairsOK : List (Fin 9 → ℤ) → Bool
  | [] => true
  | v :: vs => vs.all (fun w => decide (dot v w ≤ 2)) && pairsOK vs

/-- The whole finite certificate: 306 vectors, squared norms 4, pair bound 2. -/
def certOK : Bool :=
  (vecs.length == 306) && vecs.all (fun v => decide (dot v v = 4)) && pairsOK vecs

/-- The kernel evaluates the certificate. -/
theorem certOK_true : certOK = true := by decide +kernel

theorem dot_comm (v w : Fin 9 → ℤ) : dot v w = dot w v := by
  unfold dot; ring

theorem dot_eq_sum (v w : Fin 9 → ℤ) : dot v w = ∑ i : Fin 9, v i * w i := by
  simp only [dot, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]
  rfl

theorem pairwise_of_pairsOK :
    ∀ l : List (Fin 9 → ℤ), pairsOK l = true → l.Pairwise (fun v w => dot v w ≤ 2)
  | [], _ => List.Pairwise.nil
  | v :: vs, h => by
    simp only [pairsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact List.Pairwise.cons h.1 (pairwise_of_pairsOK vs h.2)

theorem facts :
    vecs.length = 306 ∧ (∀ v ∈ vecs, dot v v = 4) ∧
      vecs.Pairwise (fun v w => dot v w ≤ 2) := by
  have h := certOK_true
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, pairwise_of_pairsOK _ h.2⟩

theorem nodup_vecs : vecs.Nodup := by
  obtain ⟨-, hn, hp⟩ := facts
  refine hp.imp_of_mem ?_
  intro v w hv _ hvw heq
  subst heq
  have := hn v hv
  omega

/-- The certificate as a finite set of integer vectors. -/
def S : Finset (Fin 9 → ℤ) := vecs.toFinset

theorem card_S : S.card = 306 := by
  rw [S, List.toFinset_card_of_nodup nodup_vecs, facts.1]

theorem norm_S : ∀ v ∈ S, dot v v = 4 := by
  intro v hv
  exact facts.2.1 v (List.mem_toFinset.mp hv)

theorem pair_S : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → dot v w ≤ 2 := by
  intro v hv w hw hvw
  have : Std.Symm (fun v w : Fin 9 → ℤ => dot v w ≤ 2) :=
    ⟨fun a b hab => by simpa [dot_comm] using hab⟩
  exact facts.2.2.forall (List.mem_toFinset.mp hv) (List.mem_toFinset.mp hw) hvw

/-- Integer form: 306 distinct vectors in Z^9 of squared norm 4 whose distinct
pairs have dot product at most 2. -/
theorem int_claim :
    ∃ T : Finset (Fin 9 → ℤ), T.card = 306 ∧
      (∀ v ∈ T, ∑ i : Fin 9, v i * v i = 4) ∧
      (∀ v ∈ T, ∀ w ∈ T, v ≠ w → ∑ i : Fin 9, v i * w i ≤ 2) := by
  refine ⟨S, card_S, ?_, ?_⟩
  · intro v hv
    rw [← dot_eq_sum]
    exact norm_S v hv
  · intro v hv w hw hvw
    rw [← dot_eq_sum]
    exact pair_S v hv w hw hvw

/-- The real point of the unit sphere for an integer vector of squared norm 4. -/
noncomputable def realize (v : Fin 9 → ℤ) : EuclideanSpace ℝ (Fin 9) :=
  WithLp.toLp 2 (fun i => (v i : ℝ) / 2)

theorem realize_apply (v : Fin 9 → ℤ) (i : Fin 9) : realize v i = (v i : ℝ) / 2 := rfl

theorem inner_realize (v w : Fin 9 → ℤ) :
    inner ℝ (realize v) (realize w) = (dot v w : ℝ) / 4 := by
  rw [dot_eq_sum, PiLp.inner_apply]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [realize_apply, RCLike.inner_apply, conj_trivial]
  ring

theorem realize_injective : Function.Injective realize := by
  intro v w h
  funext i
  have := congrArg (fun x : EuclideanSpace ℝ (Fin 9) => x i) h
  simp only [realize_apply] at this
  have h2 : ((v i : ℤ) : ℝ) = (w i : ℝ) := by linarith
  exact_mod_cast h2

/-- tau_9 >= 306: 306 distinct unit vectors in R^9 whose distinct pairs have
inner product at most 1/2. -/
theorem tau9_ge_306 :
    ∃ C : Finset (EuclideanSpace ℝ (Fin 9)), C.card = 306 ∧
      (∀ x ∈ C, ‖x‖ = 1) ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → inner ℝ x y ≤ (1 / 2 : ℝ)) := by
  refine ⟨S.image realize, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ realize_injective, card_S]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have h1 : inner ℝ (realize v) (realize v) = (1 : ℝ) := by
      rw [inner_realize, norm_S v hv]
      norm_num
    have h2 : ‖realize v‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, h1]
    have h3 : 0 ≤ ‖realize v‖ := norm_nonneg _
    nlinarith [h2, h3]
  · intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    have hvw : v ≠ w := fun h => hxy (h ▸ rfl)
    rw [inner_realize]
    have := pair_S v hv w hw hvw
    have h' : (dot v w : ℝ) ≤ 2 := by exact_mod_cast this
    linarith

end KN9

#print axioms KN9.int_claim
#print axioms KN9.tau9_ge_306
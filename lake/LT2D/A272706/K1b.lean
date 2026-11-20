import LT2D.A272706.K1a
-- A272706 / Rule 515, file K1b (verbatim copy of A273331 K1b #mwlxl791-zobq6n, namespace renamed) (core Lean only): certificate checker (BT, explore, certOK, ofList), L7-L9, mix.

namespace A272706

/-! ## Certificates: a binary search tree on Nat keys, explored and checked by the kernel -/

inductive BT (σ : Type) where
  | leaf : BT σ
  | node : BT σ → Nat → σ → BT σ → BT σ

namespace BT
variable {σ : Type}

def toList : BT σ → List σ
  | leaf => []
  | node l _ v r => v :: (toList l ++ toList r)

/-- search by key k; at the node with key k compare the stored state with P -/
def find [DecidableEq σ] (k : Nat) (P : σ) : BT σ → Bool
  | leaf => false
  | node l k' v r => if k < k' then find k P l else if k' < k then find k P r else decide (P = v)

def ins (k : Nat) (P : σ) : BT σ → BT σ
  | leaf => node leaf k P leaf
  | node l k' v r =>
    if k < k' then node (ins k P l) k' v r else if k' < k then node l k' v (ins k P r) else node l k' v r

/-- L7 -/
theorem find_sound [DecidableEq σ] (k : Nat) (P : σ) (t : BT σ) (h : t.find k P = true) :
    P ∈ t.toList := by
  induction t with
  | leaf =>
    simp only [BT.find] at h
    exact absurd h (by decide)
  | node l k' v r ihl ihr =>
    simp only [BT.find] at h
    simp only [BT.toList, List.mem_cons, List.mem_append]
    split at h
    · exact Or.inr (Or.inl (ihl h))
    · split at h
      · exact Or.inr (Or.inr (ihr h))
      · exact Or.inl (of_decide_eq_true h)

end BT

/-- depth-first exploration with fuel (its output is only ever *checked*, never trusted) -/
def explore {σ : Type} [DecidableEq σ] (key : σ → Nat) (step : σ → Nat → σ) :
    Nat → List σ → BT σ → BT σ
  | 0, _, t => t
  | _ + 1, [], t => t
  | f + 1, P :: rest, t =>
    if t.find (key P) P then explore key step f rest t
    else explore key step f (step P 0 :: step P 1 :: step P 2 :: step P 3 :: step P 4 ::
      step P 5 :: step P 6 :: step P 7 :: rest) (t.ins (key P) P)

/-- the certificate check: start in t, t closed under the 8 digit steps, end condition on t -/
def certOK {σ : Type} [DecidableEq σ] (key : σ → Nat) (step : σ → Nat → σ) (endc : σ → Bool)
    (start : σ) (t : BT σ) : Bool :=
  t.find (key start) start && t.toList.all fun P =>
    endc P && [0, 1, 2, 3, 4, 5, 6, 7].all fun d => t.find (key (step P d)) (step P d)

theorem find_sound' {σ : Type} [DecidableEq σ] (k : Nat) (P : σ) (t : BT σ) (h : t.find k P = true) :
    P ∈ t.toList := by
  induction t with
  | leaf =>
    simp only [BT.find] at h
    exact absurd h (by decide)
  | node l k' v r ihl ihr =>
    simp only [BT.find] at h
    simp only [BT.toList, List.mem_cons, List.mem_append]
    split at h
    · exact Or.inr (Or.inl (ihl h))
    · split at h
      · exact Or.inr (Or.inr (ihr h))
      · exact Or.inl (of_decide_eq_true h)

theorem prun_succ_eq' {σ : Type} (step : σ → Nat → σ) (n : Nat) (Q : σ) (a b c : Nat) :
    prun step (n + 1) Q a b c = prun step n (step Q (dg a b c)) (a / 2) (b / 2) (c / 2) := rfl

/-- L8: soundness of a passed certificate: the end condition holds after every digit string -/
theorem cert_sound {σ : Type} [DecidableEq σ] (key : σ → Nat) (step : σ → Nat → σ)
    (endc : σ → Bool) (start : σ) (t : BT σ) (h : certOK key step endc start t = true)
    (L x y z : Nat) : endc (prun step L start x y z) = true := by
  unfold certOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hs, hall⟩ := h
  rw [List.all_eq_true] at hall
  have key_lem : ∀ (L : Nat) (P : σ) (x y z : Nat), P ∈ t.toList →
      endc (prun step L P x y z) = true := by
    intro L
    induction L with
    | zero =>
      intro P x y z hP
      have := hall P hP
      rw [Bool.and_eq_true] at this
      exact this.1
    | succ L ih =>
      intro P x y z hP
      rw [prun_succ_eq']
      apply ih
      have := hall P hP
      rw [Bool.and_eq_true, List.all_eq_true] at this
      have hd : dg x y z < 8 := by unfold dg; omega
      have h2 := this.2 (dg x y z) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega)
      exact find_sound' _ _ t h2
  exact key_lem L start x y z (find_sound' _ _ t hs)

/-- index tree of a list certificate -/
def BT.ofList {σ : Type} (key : σ → Nat) (l : List σ) : BT σ :=
  l.foldl (fun t P => t.ins (key P) P) .leaf

theorem toList_ins_mem {σ : Type} (k : Nat) (P : σ) (t : BT σ) (Q : σ)
    (h : Q ∈ (t.ins k P).toList) : Q = P ∨ Q ∈ t.toList := by
  induction t with
  | leaf =>
    simp only [BT.ins, BT.toList, List.mem_cons, List.append_nil, List.not_mem_nil, or_false] at h
    exact Or.inl h
  | node l k' v r ihl ihr =>
    simp only [BT.ins] at h
    split at h
    · simp only [BT.toList, List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · rcases ihl h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h))
    · split at h
      · simp only [BT.toList, List.mem_cons, List.mem_append] at h ⊢
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · rcases ihr h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inr h

theorem toList_foldl_mem {σ : Type} (key : σ → Nat) (l : List σ) (t : BT σ) (Q : σ)
    (h : Q ∈ (l.foldl (fun t P => t.ins (key P) P) t).toList) : Q ∈ l ∨ Q ∈ t.toList := by
  induction l generalizing t with
  | nil => exact Or.inr h
  | cons a l ih =>
    simp only [List.foldl] at h
    rcases ih _ h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · rcases toList_ins_mem _ _ _ _ h' with h'' | h''
      · exact Or.inl (h'' ▸ List.mem_cons_self ..)
      · exact Or.inr h''

theorem ofList_mem {σ : Type} (key : σ → Nat) (S : List σ) (Q : σ)
    (h : Q ∈ (BT.ofList key S).toList) : Q ∈ S := by
  unfold BT.ofList at h
  rcases toList_foldl_mem key S .leaf Q h with h' | h'
  · exact h'
  · simp [BT.toList] at h'

/-- L9: soundness of a LIST certificate S with an escape predicate `esc` (closed under steps,
implies the end condition). `hS` is proved in chunks: S = slice 1 ++ ... ++ slice m, one
`decide +kernel` theorem per slice (each declaration gets a fresh kernel cache). -/
theorem cert_sound_list {σ : Type} [DecidableEq σ] (key : σ → Nat) (step : σ → Nat → σ)
    (endc esc : σ → Bool) (start : σ) (S : List σ)
    (hesc : ∀ P d, esc P = true → esc (step P d) = true)
    (hescend : ∀ P, esc P = true → endc P = true)
    (hstart : (BT.ofList key S).find (key start) start = true)
    (hS : ∀ P ∈ S, endc P = true ∧ ∀ d < 8,
      esc (step P d) = true ∨ (BT.ofList key S).find (key (step P d)) (step P d) = true)
    (L x y z : Nat) : endc (prun step L start x y z) = true := by
  have inv : ∀ (L : Nat) (P : σ) (x y z : Nat), (esc P = true ∨ P ∈ S) →
      endc (prun step L P x y z) = true := by
    intro L
    induction L with
    | zero =>
      intro P x y z hP
      show endc P = true
      rcases hP with h | h
      · exact hescend P h
      · exact (hS P h).1
    | succ L ih =>
      intro P x y z hP
      rw [prun_succ_eq]
      have hd : dg x y z < 8 := by unfold dg; omega
      apply ih
      rcases hP with h | h
      · exact Or.inl (hesc P _ h)
      · rcases (hS P h).2 _ hd with h' | h'
        · exact Or.inl h'
        · exact Or.inr (ofList_mem key S _ (find_sound' _ _ _ h'))
  exact inv L start x y z (Or.inr (ofList_mem key S _ (find_sound' _ _ _ hstart)))

/-- scrambled key (multiplication by a unit mod a prime near 2^64): keeps the tree shallow -/
def mix (n : Nat) : Nat := n * 11400714819323198485 % 18446744073709551557

end A272706
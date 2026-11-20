-- A272706 / Rule 515, file K1a (core Lean only, no Mathlib): table, automaton runs, L1-L6.
-- Mechanical copy of A273331 K1a (#mwlxjjt6-t5cbl7) with Rule 515's 15-state table (GEN/kernel.py,
-- checked by GEN/checks.py F0-F3) in place of Rule 654's; proofs unchanged except 104 -> 15.

namespace A272706

/-- transition rows: row q lists the successor for d = 0..7 -/
def Trows : List (List Nat) := [
  [1,2,2,3,4,2,2,5],
  [6,5,5,6,7,8,8,9],
  [2,2,2,10,11,12,12,12],
  [5,6,6,3,8,9,9,8],
  [4,6,6,5,8,13,13,8],
  [6,5,5,6,13,8,8,9],
  [6,6,6,6,8,8,8,8],
  [7,8,8,9,8,13,13,8],
  [8,8,8,8,8,8,8,8],
  [8,9,9,8,13,8,8,9],
  [2,10,10,10,12,12,12,14],
  [11,12,12,12,11,11,11,12],
  [12,12,12,14,11,12,12,12],
  [13,8,8,9,8,13,13,8],
  [12,14,14,14,12,12,12,14]
]

/-- outputs, 0 or 1, for states 0..14 -/
def Olist : List Nat := [
  0,0,0,0,1,0,0,1,1,1,0,0,1,0,1
]

def tr (q d : Nat) : Nat := (Trows.getD q []).getD d 0
def out (q : Nat) : Bool := Olist.getD q 0 == 1

theorem Trows_length : Trows.length = 15 := by decide
theorem Trows_rows : ∀ r ∈ Trows, r.length = 8 ∧ ∀ s ∈ r, s < 15 := by decide
theorem Olist_length : Olist.length = 15 := by decide

/-! ## Digit triples and runs (least significant digit first) -/

/-- lowest digit triple of (x, y, z): index 4*z0 + 2*y0 + x0 -/
def dg (x y z : Nat) : Nat := 4 * (z % 2) + 2 * (y % 2) + x % 2

/-- generic run: read the lowest L digit triples of (x, y, z) through `step` -/
def prun {σ : Type} (step : σ → Nat → σ) : Nat → σ → Nat → Nat → Nat → σ
  | 0, P, _, _, _ => P
  | L + 1, P, x, y, z => prun step L (step P (dg x y z)) (x / 2) (y / 2) (z / 2)

/-- the 15-state automaton run on (x, y, t) -/
abbrev run (L q x y t : Nat) : Nat := prun tr L q x y t

/-- V x y t: automaton value (claimed: cell (x, y) at generation t - 1); x + y + t + 1 digits suffice -/
def V (x y t : Nat) : Bool := out (run (x + y + t + 1) 0 x y t)

/-- L1 (F0): a zero digit triple does not change the output -/
theorem tr_zero_out (q : Nat) : out (tr q 0) = out q := by
  rcases Nat.lt_or_ge q 15 with h | h
  · have hb : ∀ q, q < 15 → out (tr q 0) = out q := by decide
    exact hb q h
  · have hlT : Trows.length ≤ q := by rw [Trows_length]; omega
    have hlO : Olist.length ≤ q := by rw [Olist_length]; omega
    have hT : tr q 0 = 0 := by
      unfold tr
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlT]
    have hq : out q = false := by
      unfold out
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlO]
    have h0 : out 0 = false := by decide
    rw [hT, h0, hq]

theorem prun_succ_eq {σ : Type} (step : σ → Nat → σ) (n : Nat) (Q : σ) (a b c : Nat) :
    prun step (n + 1) Q a b c = prun step n (step Q (dg a b c)) (a / 2) (b / 2) (c / 2) := rfl

/-- L2 -/
theorem prun_add {σ : Type} (step : σ → Nat → σ) (L M : Nat) (P : σ) (x y z : Nat) :
    prun step (L + M) P x y z =
      prun step M (prun step L P x y z) (x / 2 ^ L) (y / 2 ^ L) (z / 2 ^ L) := by
  induction L generalizing P x y z with
  | zero => simp [prun]
  | succ L ih =>
    have hd : ∀ a : Nat, a / 2 / 2 ^ L = a / 2 ^ (L + 1) := by
      intro a
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [show L + 1 + M = (L + M) + 1 by omega, prun_succ_eq, prun_succ_eq, ih]
    simp only [hd]

/-- L3 -/
theorem run_succ_top (L q x y t : Nat) :
    run (L + 1) q x y t = tr (run L q x y t) (dg (x / 2 ^ L) (y / 2 ^ L) (t / 2 ^ L)) := by
  show prun tr (L + 1) q x y t = tr (prun tr L q x y t) (dg (x / 2 ^ L) (y / 2 ^ L) (t / 2 ^ L))
  rw [prun_add tr L 1 q x y t]
  rfl

/-- L4 -/
theorem out_run_zero (M q : Nat) : out (run M q 0 0 0) = out q := by
  induction M generalizing q with
  | zero => rfl
  | succ M ih =>
    have h : run (M + 1) q 0 0 0 = run M (tr q 0) 0 0 0 := rfl
    rw [h, ih, tr_zero_out]

theorem prun_succ_eq_c {σ : Type} (step : σ → Nat → σ) (n : Nat) (Q : σ) (a b c : Nat) :
    prun step (n + 1) Q a b c = prun step n (step Q (dg a b c)) (a / 2) (b / 2) (c / 2) := rfl

theorem prun_add_c {σ : Type} (step : σ → Nat → σ) (L M : Nat) (P : σ) (x y z : Nat) :
    prun step (L + M) P x y z =
      prun step M (prun step L P x y z) (x / 2 ^ L) (y / 2 ^ L) (z / 2 ^ L) := by
  induction L generalizing P x y z with
  | zero => simp [prun]
  | succ L ih =>
    have hd : ∀ a : Nat, a / 2 / 2 ^ L = a / 2 ^ (L + 1) := by
      intro a
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [show L + 1 + M = (L + M) + 1 by omega, prun_succ_eq_c, prun_succ_eq_c, ih]
    simp only [hd]

theorem tr_zero_out_c (q : Nat) : out (tr q 0) = out q := by
  rcases Nat.lt_or_ge q 15 with h | h
  · have hb : ∀ q, q < 15 → out (tr q 0) = out q := by decide
    exact hb q h
  · have hlT : Trows.length ≤ q := by rw [Trows_length]; omega
    have hlO : Olist.length ≤ q := by rw [Olist_length]; omega
    have hT : tr q 0 = 0 := by
      unfold tr
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlT]
    have hq : out q = false := by
      unfold out
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlO]
    have h0 : out 0 = false := by decide
    rw [hT, h0, hq]

theorem out_run_zero_c (M q : Nat) : out (run M q 0 0 0) = out q := by
  induction M generalizing q with
  | zero => rfl
  | succ M ih =>
    have h1 : run (M + 1) q 0 0 0 = run M (tr q (dg 0 0 0)) 0 0 0 := rfl
    have h0 : dg 0 0 0 = 0 := rfl
    rw [h1, h0]
    exact (ih (tr q 0)).trans (tr_zero_out_c q)

theorem lt_two_pow_c (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- L5 -/
theorem out_run_eq_V (L x y t : Nat) (hx : x < 2 ^ L) (hy : y < 2 ^ L) (ht : t < 2 ^ L) :
    out (run L 0 x y t) = V x y t := by
  unfold V
  rcases Nat.le_total L (x + y + t + 1) with h | h
  · obtain ⟨M, hM⟩ : ∃ M, x + y + t + 1 = L + M := ⟨x + y + t + 1 - L, by omega⟩
    have key : run (L + M) 0 x y t
        = run M (run L 0 x y t) (x / 2 ^ L) (y / 2 ^ L) (t / 2 ^ L) :=
      prun_add_c tr L M 0 x y t
    rw [hM, key, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, Nat.div_eq_of_lt ht]
    exact (out_run_zero_c M _).symm
  · obtain ⟨M, hM⟩ : ∃ M, L = x + y + t + 1 + M := ⟨L - (x + y + t + 1), by omega⟩
    have hxN : x < 2 ^ (x + y + t + 1) := by have := lt_two_pow_c (x + y + t + 1); omega
    have hyN : y < 2 ^ (x + y + t + 1) := by have := lt_two_pow_c (x + y + t + 1); omega
    have htN : t < 2 ^ (x + y + t + 1) := by have := lt_two_pow_c (x + y + t + 1); omega
    have key : run (x + y + t + 1 + M) 0 x y t
        = run M (run (x + y + t + 1) 0 x y t) (x / 2 ^ (x + y + t + 1))
            (y / 2 ^ (x + y + t + 1)) (t / 2 ^ (x + y + t + 1)) :=
      prun_add_c tr (x + y + t + 1) M 0 x y t
    rw [hM, key, Nat.div_eq_of_lt hxN, Nat.div_eq_of_lt hyN, Nat.div_eq_of_lt htN]
    exact out_run_zero_c M _

/-- L6: a projection that commutes with one step commutes with runs -/
theorem prun_proj {σ τ : Type} (step : σ → Nat → σ) (g : τ → Nat → τ) (π : σ → τ)
    (h : ∀ P d, π (step P d) = g (π P) d) (L : Nat) (P : σ) (x y z : Nat) :
    π (prun step L P x y z) = prun g L (π P) x y z := by
  induction L generalizing P x y z with
  | zero => rfl
  | succ L ih =>
    simp only [prun]
    rw [ih, h]

end A272706
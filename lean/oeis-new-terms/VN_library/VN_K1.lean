-- VN library (von Neumann family), file K1 (core Lean only, no Mathlib): tables as data, digit runs, L1-L6.
-- Generic version of A272706 K1a (#mwmfkzh5-8rq7id): the fixed 15-state table becomes a parameter A : Tab.

namespace VN

/-- transition of a raw table: entry d of row q; 0 if the row or the entry is missing (rows need not have
length 8: okTab checks the values read for d < 8) -/
def trL (T : List (List Nat)) (q d : Nat) : Nat := (T.getD q []).getD d 0
/-- output of a raw table: true iff entry q is 1 (any other entry, or q out of range, reads false) -/
def outL (O : List Nat) (q : Nat) : Bool := O.getD q 0 == 1

/-- well-formed table with N = T.length states: N > 0, |O| = N, out 0 = false, and for every state q < N:
F0 (a zero digit triple keeps the output) and every successor tr q d (d < 8) is < N -/
def okTab (T : List (List Nat)) (O : List Nat) : Bool :=
  decide (0 < T.length) && (O.length == T.length) && (outL O 0 == false) &&
  (List.range T.length).all (fun q =>
    (outL O (trL T q 0) == outL O q) && (List.range 8).all (fun d => decide (trL T q d < T.length)))

/-- a table: transitions T (row q lists the successor for d = 4*t0 + 2*y0 + x0, d = 0..7), outputs O,
and the kernel-checked well-formedness -/
structure Tab where
  T : List (List Nat)
  O : List Nat
  ok : okTab T O = true

def tr (A : Tab) (q d : Nat) : Nat := trL A.T q d
def out (A : Tab) (q : Nat) : Bool := outL A.O q

theorem ok_parts (A : Tab) : 0 < A.T.length ∧ A.O.length = A.T.length ∧ out A 0 = false ∧
    ∀ q, q < A.T.length → out A (tr A q 0) = out A q ∧ ∀ d, d < 8 → tr A q d < A.T.length := by
  have h := A.ok
  unfold okTab at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨of_decide_eq_true h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3, fun q hq => ?_⟩
  have h5 := List.all_eq_true.mp h4 q (List.mem_range.mpr hq)
  rw [Bool.and_eq_true] at h5
  refine ⟨beq_iff_eq.mp h5.1, fun d hd => ?_⟩
  exact of_decide_eq_true (List.all_eq_true.mp h5.2 d (List.mem_range.mpr hd))

/-- R1: the table is closed -/
theorem tr_lt (A : Tab) (q d : Nat) (hq : q < A.T.length) (hd : d < 8) : tr A q d < A.T.length :=
  ((ok_parts A).2.2.2 q hq).2 d hd

/-- L1 (F0): a zero digit triple does not change the output, for every q -/
theorem tr_zero_out (A : Tab) (q : Nat) : out A (tr A q 0) = out A q := by
  obtain ⟨_, hO, h0, hq⟩ := ok_parts A
  rcases Nat.lt_or_ge q A.T.length with h | h
  · exact (hq q h).1
  · have hT : tr A q 0 = 0 := by
      unfold tr trL
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    have hq' : out A q = false := by
      unfold out outL
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : A.O.length ≤ q)]
    rw [hT, h0, hq']

/-! ## Digit triples and runs (least significant digit first) -/

/-- lowest digit triple of (x, y, z): index 4*z0 + 2*y0 + x0 -/
def dg (x y z : Nat) : Nat := 4 * (z % 2) + 2 * (y % 2) + x % 2

/-- generic run: read the lowest L digit triples of (x, y, z) through `step` -/
def prun {σ : Type} (step : σ → Nat → σ) : Nat → σ → Nat → Nat → Nat → σ
  | 0, P, _, _, _ => P
  | L + 1, P, x, y, z => prun step L (step P (dg x y z)) (x / 2) (y / 2) (z / 2)

/-- the table's run on (x, y, t) -/
abbrev run (A : Tab) (L q x y t : Nat) : Nat := prun (tr A) L q x y t

/-- V A x y t: the table's value (claimed: cell (x, y) at stage t - 1); x + y + t + 1 digits suffice -/
def V (A : Tab) (x y t : Nat) : Bool := out A (run A (x + y + t + 1) 0 x y t)

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
theorem run_succ_top (A : Tab) (L q x y t : Nat) :
    run A (L + 1) q x y t = tr A (run A L q x y t) (dg (x / 2 ^ L) (y / 2 ^ L) (t / 2 ^ L)) := by
  show prun (tr A) (L + 1) q x y t =
    tr A (prun (tr A) L q x y t) (dg (x / 2 ^ L) (y / 2 ^ L) (t / 2 ^ L))
  rw [prun_add (tr A) L 1 q x y t]
  rfl

/-- L4 -/
theorem out_run_zero (A : Tab) (M q : Nat) : out A (run A M q 0 0 0) = out A q := by
  induction M generalizing q with
  | zero => rfl
  | succ M ih =>
    have h : run A (M + 1) q 0 0 0 = run A M (tr A q 0) 0 0 0 := rfl
    rw [h, ih, tr_zero_out]

theorem lt_two_pow_c (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- L5 -/
theorem out_run_eq_V (A : Tab) (L x y t : Nat) (hx : x < 2 ^ L) (hy : y < 2 ^ L) (ht : t < 2 ^ L) :
    out A (run A L 0 x y t) = V A x y t := by
  unfold V
  rcases Nat.le_total L (x + y + t + 1) with h | h
  · obtain ⟨M, hM⟩ : ∃ M, x + y + t + 1 = L + M := ⟨x + y + t + 1 - L, by omega⟩
    have key : run A (L + M) 0 x y t
        = run A M (run A L 0 x y t) (x / 2 ^ L) (y / 2 ^ L) (t / 2 ^ L) :=
      prun_add (tr A) L M 0 x y t
    rw [hM, key, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, Nat.div_eq_of_lt ht]
    exact (out_run_zero A M _).symm
  · obtain ⟨M, hM⟩ : ∃ M, L = x + y + t + 1 + M := ⟨L - (x + y + t + 1), by omega⟩
    have hxN : x < 2 ^ (x + y + t + 1) := by have := lt_two_pow_c (x + y + t + 1); omega
    have hyN : y < 2 ^ (x + y + t + 1) := by have := lt_two_pow_c (x + y + t + 1); omega
    have htN : t < 2 ^ (x + y + t + 1) := by have := lt_two_pow_c (x + y + t + 1); omega
    have key : run A (x + y + t + 1 + M) 0 x y t
        = run A M (run A (x + y + t + 1) 0 x y t) (x / 2 ^ (x + y + t + 1))
            (y / 2 ^ (x + y + t + 1)) (t / 2 ^ (x + y + t + 1)) :=
      prun_add (tr A) (x + y + t + 1) M 0 x y t
    rw [hM, key, Nat.div_eq_of_lt hxN, Nat.div_eq_of_lt hyN, Nat.div_eq_of_lt htN]
    exact out_run_zero A M _

/-- L6: a projection that commutes with one step commutes with runs -/
theorem prun_proj {σ τ : Type} (step : σ → Nat → σ) (g : τ → Nat → τ) (π : σ → τ)
    (h : ∀ P d, π (step P d) = g (π P) d) (L : Nat) (P : σ) (x y z : Nat) :
    π (prun step L P x y z) = prun g L (π P) x y z := by
  induction L generalizing P x y z with
  | zero => rfl
  | succ L ih =>
    simp only [prun]
    rw [ih, h]

end VN
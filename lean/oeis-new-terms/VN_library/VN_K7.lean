import LongTable.P_mwmouaen_iyun3b
-- VN library, file K7 (core Lean only): CHECK REC. The four digit-sum vectors (square, two axes, origin)
-- satisfy the recurrence of (x-1)(x-2)(x-4) at index nb for every state, and D * (4Q + O - 2X - 2Y)
-- equals a*4^n + b*2^n + c at n = n0 .. nb+2. The recurrence propagates to every n >= nb by linearity
-- (rec_cnt); the closed form for every n >= n0 is proved in M2 (cnt_closed).
-- Generic version of A272706 K6 (#mwmg681k-0v8jc7): vectors computed level by level instead of `it`.
namespace VN

/-- one backward step on a value vector (index = state q < N) -/
def bstep (A : Tab) (D : List Nat) (v : List Nat) : List Nat :=
  (List.range A.T.length).map (fun q => D.foldr (fun d acc => v.getD (tr A q d) 0 + acc) 0)

/-- itv A D n = the vector of it A D (f4 A) n q over q < N -/
def itv (A : Tab) (D : List Nat) : Nat → List Nat
  | 0 => (List.range A.T.length).map (f4 A)
  | n + 1 => bstep A D (itv A D n)

/-- the recurrence u(n+3) - 7u(n+2) + 14u(n+1) - 8u(n) = 0 at n = nb, for every state -/
def recAt (A : Tab) (D : List Nat) (nb : Nat) : Bool :=
  (List.range A.T.length).all (fun q =>
    (itv A D (nb + 3)).getD q 0 + 14 * (itv A D (nb + 1)).getD q 0 ==
      7 * (itv A D (nb + 2)).getD q 0 + 8 * (itv A D nb).getD q 0)

/-- the count combination 4Q + O - 2X - 2Y at the start state, read from the vectors -/
def sv (A : Tab) (n : Nat) : Int :=
  4 * ((itv A D4 n).getD 0 0 : Int) + ((itv A D0 n).getD 0 0 : Int) -
    2 * ((itv A DX n).getD 0 0 : Int) - 2 * ((itv A DY n).getD 0 0 : Int)

/-- CHECK REC (kernel): n0 ≤ nb, the four recurrences at nb, and the formula at n0 .. nb+2 -/
def checkRec (A : Tab) (D a b c : Int) (n0 nb : Nat) : Bool :=
  decide (n0 ≤ nb) && recAt A D4 nb && recAt A DX nb && recAt A DY nb && recAt A D0 nb &&
  (List.range (nb + 3 - n0)).all (fun i =>
    D * sv A (n0 + i) == a * 4 ^ (n0 + i) + b * 2 ^ (n0 + i) + c)

/-- the same combination through `it` (the sums of K6) -/
def cnt (A : Tab) (n : Nat) : Int :=
  4 * (it A D4 (f4 A) n 0 : Int) + (it A D0 (f4 A) n 0 : Int) -
    2 * (it A DX (f4 A) n 0 : Int) - 2 * (it A DY (f4 A) n 0 : Int)

theorem getD_map_range (N : Nat) (f : Nat → Nat) (q : Nat) (hq : q < N) :
    ((List.range N).map f).getD q 0 = f q := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hq]

theorem foldr_tr (A : Tab) (D : List Nat) (v : List Nat) (g : Nat → Nat) (q : Nat)
    (h : ∀ d ∈ D, v.getD (tr A q d) 0 = g (tr A q d)) :
    D.foldr (fun d acc => v.getD (tr A q d) 0 + acc) 0 = AD A D g q := by
  induction D with
  | nil => rfl
  | cons d D ih =>
    show v.getD (tr A q d) 0 + D.foldr (fun d acc => v.getD (tr A q d) 0 + acc) 0 =
      g (tr A q d) + AD A D g q
    rw [h d (List.mem_cons_self ..), ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]

/-- the vectors are the digit-string sums -/
theorem itv_get (A : Tab) (D : List Nat) (hD : ∀ d ∈ D, d < 8) (n q : Nat) (hq : q < A.T.length) :
    (itv A D n).getD q 0 = it A D (f4 A) n q := by
  induction n generalizing q with
  | zero => exact getD_map_range _ _ q hq
  | succ n ih =>
    show (bstep A D (itv A D n)).getD q 0 = AD A D (it A D (f4 A) n) q
    unfold bstep
    rw [getD_map_range _ _ q hq]
    exact foldr_tr A D _ _ q (fun d hd => ih _ (tr_lt A q d hq (hD d hd)))

/-- R2: one backward step preserves a linear relation -/
theorem AD_comb (A : Tab) (D : List Nat) (a b c e : Nat) (g1 g2 g3 g4 : Nat → Nat) (q : Nat)
    (h : ∀ d ∈ D, a * g1 (tr A q d) + b * g2 (tr A q d) = c * g3 (tr A q d) + e * g4 (tr A q d)) :
    a * AD A D g1 q + b * AD A D g2 q = c * AD A D g3 q + e * AD A D g4 q := by
  induction D with
  | nil => show a * 0 + b * 0 = c * 0 + e * 0; omega
  | cons d D ih =>
    have hd := h d (List.mem_cons_self ..)
    have hD := ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))
    show a * (g1 (tr A q d) + AD A D g1 q) + b * (g2 (tr A q d) + AD A D g2 q) =
      c * (g3 (tr A q d) + AD A D g3 q) + e * (g4 (tr A q d) + AD A D g4 q)
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega

/-- R3: a relation between the vectors at indices i1..i4 propagates to n + i1 .. n + i4 -/
theorem it_comb (A : Tab) (D : List Nat) (hD : ∀ d ∈ D, d < 8) (g : Nat → Nat) (a b c e i1 i2 i3 i4 : Nat)
    (h0 : ∀ q, q < A.T.length →
      a * it A D g i1 q + b * it A D g i2 q = c * it A D g i3 q + e * it A D g i4 q)
    (n q : Nat) (hq : q < A.T.length) :
    a * it A D g (n + i1) q + b * it A D g (n + i2) q =
      c * it A D g (n + i3) q + e * it A D g (n + i4) q := by
  induction n generalizing q with
  | zero => simp only [Nat.zero_add]; exact h0 q hq
  | succ n ih =>
    rw [show n + 1 + i1 = (n + i1) + 1 by omega, show n + 1 + i2 = (n + i2) + 1 by omega,
      show n + 1 + i3 = (n + i3) + 1 by omega, show n + 1 + i4 = (n + i4) + 1 by omega]
    exact AD_comb A D a b c e _ _ _ _ q (fun d hd => ih (tr A q d) (tr_lt A q d hq (hD d hd)))

/-- R4: a passed recurrence check at nb holds at the start state for every m ≥ nb -/
theorem recAt_sound (A : Tab) (D : List Nat) (hD : ∀ d ∈ D, d < 8) (nb : Nat) (h : recAt A D nb = true)
    (m : Nat) (hm : nb ≤ m) :
    it A D (f4 A) (m + 3) 0 + 14 * it A D (f4 A) (m + 1) 0 =
      7 * it A D (f4 A) (m + 2) 0 + 8 * it A D (f4 A) m 0 := by
  have hN := (ok_parts A).1
  have h0 : ∀ q, q < A.T.length → 1 * it A D (f4 A) (nb + 3) q + 14 * it A D (f4 A) (nb + 1) q =
      7 * it A D (f4 A) (nb + 2) q + 8 * it A D (f4 A) nb q := by
    intro q hq
    have h1 := beq_iff_eq.mp (List.all_eq_true.mp h q (List.mem_range.mpr hq))
    rw [itv_get A D hD _ q hq, itv_get A D hD _ q hq, itv_get A D hD _ q hq,
      itv_get A D hD _ q hq] at h1
    omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + nb := ⟨m - nb, by omega⟩
  have h2 := it_comb A D hD (f4 A) 1 14 7 8 (nb + 3) (nb + 1) (nb + 2) nb h0 k 0 hN
  rw [show k + nb + 3 = k + (nb + 3) by omega, show k + nb + 1 = k + (nb + 1) by omega,
    show k + nb + 2 = k + (nb + 2) by omega]
  omega

theorem sv_eq (A : Tab) (n : Nat) : sv A n = cnt A n := by
  have hN := (ok_parts A).1
  unfold sv cnt
  rw [itv_get A D4 (by decide) n 0 hN, itv_get A D0 (by decide) n 0 hN,
    itv_get A DX (by decide) n 0 hN, itv_get A DY (by decide) n 0 hN]

theorem checkRec_parts (A : Tab) (D a b c : Int) (n0 nb : Nat) (h : checkRec A D a b c n0 nb = true) :
    n0 ≤ nb ∧ recAt A D4 nb = true ∧ recAt A DX nb = true ∧ recAt A DY nb = true ∧
      recAt A D0 nb = true ∧ ∀ n, n0 ≤ n → n < nb + 3 → D * cnt A n = a * 4 ^ n + b * 2 ^ n + c := by
  unfold checkRec at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨of_decide_eq_true h1, h2, h3, h4, h5, fun n hn1 hn2 => ?_⟩
  have hf := beq_iff_eq.mp (List.all_eq_true.mp h6 (n - n0) (List.mem_range.mpr (by omega)))
  rw [show n0 + (n - n0) = n by omega, sv_eq] at hf
  exact hf

/-- the recurrence of the count combination, for every m ≥ nb -/
theorem rec_cnt (A : Tab) (D a b c : Int) (n0 nb : Nat) (h : checkRec A D a b c n0 nb = true)
    (m : Nat) (hm : nb ≤ m) :
    cnt A (m + 3) + 14 * cnt A (m + 1) = 7 * cnt A (m + 2) + 8 * cnt A m := by
  obtain ⟨_, h4, hX, hY, h0, _⟩ := checkRec_parts A D a b c n0 nb h
  have r4 := recAt_sound A D4 (by decide) nb h4 m hm
  have rX := recAt_sound A DX (by decide) nb hX m hm
  have rY := recAt_sound A DY (by decide) nb hY m hm
  have r0 := recAt_sound A D0 (by decide) nb h0 m hm
  unfold cnt
  omega

end VN
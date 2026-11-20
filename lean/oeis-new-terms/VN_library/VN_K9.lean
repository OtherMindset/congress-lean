import LongTable.P_mwmov2n4_tdc56b
-- VN library extension, file K9 (core Lean only): EXTENDED CHECK REC. The four digit-sum vectors satisfy the
-- recurrence of a monic polynomial P = p ++ [1] (integer coefficients, lowest first; e.g. (x-1)(x-2)(x-4)(x+1) or
-- (x-1)^2(x-2)(x-3)(x-4)) at index nb for every state; P(1) = P(2) = P(4) = P(L) = 0; and D * (4Q + O - 2X - 2Y)
-- equals a*4^n + b*2^n + c + e*L^n at n = n0 .. nb + deg P - 1. The recurrence propagates to every n >= nb by
-- linearity (recAtX_sound); the closed form for every n >= n0 is proved in VN_M4. Imports the posted VN_K7 only;
-- no posted file changes.
namespace VN

/-- lin p u n = p_0 * u n + p_1 * u (n + 1) + ... (p lowest coefficient first) -/
def lin : List Int → (Nat → Int) → Nat → Int
  | [], _, _ => 0
  | c :: p, u, n => c * u n + lin p u (n + 1)

/-- the value at x of the polynomial with coefficients p (lowest first) -/
def pev : List Int → Int → Int
  | [], _ => 0
  | c :: p, x => c + x * pev p x

/-- the recurrence of the monic polynomial p ++ [1] at nb, for every state, read from the vectors itv (VN_K7) -/
def recAtX (A : Tab) (D : List Nat) (p : List Int) (nb : Nat) : Bool :=
  (List.range A.T.length).all (fun q => lin (p ++ [1]) (fun k => ((itv A D k).getD q 0 : Int)) nb == 0)

/-- CHECK RECX (kernel): P = p ++ [1] vanishes at 1, 2, 4 and L; n0 ≤ nb; the four recurrences of P at nb;
and D * (4Q + O - 2X - 2Y) = a*4^n + b*2^n + c + e*L^n at n = n0 .. nb + p.length - 1 -/
def checkRecXL (A : Tab) (p : List Int) (L D a b c e : Int) (n0 nb : Nat) : Bool :=
  pev (p ++ [1]) 1 == 0 && pev (p ++ [1]) 2 == 0 && pev (p ++ [1]) 4 == 0 && pev (p ++ [1]) L == 0 &&
  decide (n0 ≤ nb) && recAtX A D4 p nb && recAtX A DX p nb && recAtX A DY p nb && recAtX A D0 p nb &&
  (List.range (nb + p.length - n0)).all (fun i =>
    D * sv A (n0 + i) == a * 4 ^ (n0 + i) + b * 2 ^ (n0 + i) + c + e * L ^ (n0 + i))

/-- CHECK RECX with no extra term (e = 0, L = 1): the formula of vn_count -/
def checkRecX (A : Tab) (p : List Int) (D a b c : Int) (n0 nb : Nat) : Bool :=
  checkRecXL A p 1 D a b c 0 n0 nb

/-- X1: lin is additive in u -/
theorem lin_add (p : List Int) (u v : Nat → Int) (n : Nat) :
    lin p (fun k => u k + v k) n = lin p u n + lin p v n := by
  induction p generalizing n with
  | nil => show (0 : Int) = 0 + 0; omega
  | cons c p ih =>
    show c * (u n + v n) + lin p (fun k => u k + v k) (n + 1) =
      (c * u n + lin p u (n + 1)) + (c * v n + lin p v (n + 1))
    rw [ih, Int.mul_add]
    omega

/-- X2 -/
theorem lin_zero (p : List Int) (n : Nat) : lin p (fun _ => 0) n = 0 := by
  induction p generalizing n with
  | nil => rfl
  | cons c p ih =>
    show c * 0 + lin p (fun _ => 0) (n + 1) = 0
    rw [ih, Int.mul_zero, Int.add_zero]

/-- X3: shifting the index -/
theorem lin_shift (p : List Int) (u : Nat → Int) (n : Nat) :
    lin p u (n + 1) = lin p (fun k => u (k + 1)) n := by
  induction p generalizing n with
  | nil => rfl
  | cons c p ih =>
    show c * u (n + 1) + lin p u (n + 1 + 1) = c * u (n + 1) + lin p (fun k => u (k + 1)) (n + 1)
    rw [ih (n + 1)]

/-- X4: one backward step (a sum over the digits D) preserves a vanishing recurrence -/
theorem AD_lin (A : Tab) (D : List Nat) (p : List Int) (G : Nat → Nat → Nat) (q n : Nat)
    (h : ∀ d ∈ D, lin p (fun k => (G k (tr A q d) : Int)) n = 0) :
    lin p (fun k => (AD A D (G k) q : Int)) n = 0 := by
  induction D with
  | nil => exact lin_zero p n
  | cons d D ih =>
    have h1 := h d (List.mem_cons_self ..)
    have h2 := ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))
    have e : (fun k => (AD A (d :: D) (G k) q : Int)) =
        (fun k => (G k (tr A q d) : Int) + (AD A D (G k) q : Int)) := by
      funext k
      show ((G k (tr A q d) + AD A D (G k) q : Nat) : Int) = _
      omega
    rw [e, lin_add, h1, h2, Int.add_zero]

/-- X5: a recurrence that holds at nb for every state holds at nb + j for every state -/
theorem it_lin (A : Tab) (D : List Nat) (hD : ∀ d ∈ D, d < 8) (g : Nat → Nat) (p : List Int) (nb : Nat)
    (h0 : ∀ q, q < A.T.length → lin p (fun k => (it A D g k q : Int)) nb = 0) (j q : Nat)
    (hq : q < A.T.length) : lin p (fun k => (it A D g k q : Int)) (nb + j) = 0 := by
  induction j generalizing q with
  | zero => exact h0 q hq
  | succ j ih =>
    rw [show nb + (j + 1) = nb + j + 1 from rfl, lin_shift]
    exact AD_lin A D p (fun k => it A D g k) q (nb + j) (fun d hd => ih (tr A q d) (tr_lt A q d hq (hD d hd)))

/-- X6: a passed recAtX at nb gives the recurrence at the start state for every m ≥ nb -/
theorem recAtX_sound (A : Tab) (D : List Nat) (hD : ∀ d ∈ D, d < 8) (p : List Int) (nb : Nat)
    (h : recAtX A D p nb = true) (m : Nat) (hm : nb ≤ m) :
    lin (p ++ [1]) (fun k => (it A D (f4 A) k 0 : Int)) m = 0 := by
  have hN := (ok_parts A).1
  have h0 : ∀ q, q < A.T.length → lin (p ++ [1]) (fun k => (it A D (f4 A) k q : Int)) nb = 0 := by
    intro q hq
    have h1 := beq_iff_eq.mp (List.all_eq_true.mp h q (List.mem_range.mpr hq))
    have hi : ∀ k, (itv A D k).getD q 0 = it A D (f4 A) k q := fun k => itv_get A D hD k q hq
    simp only [hi] at h1
    exact h1
  obtain ⟨j, rfl⟩ : ∃ j, m = nb + j := ⟨m - nb, by omega⟩
  exact it_lin A D hD (f4 A) (p ++ [1]) nb h0 j 0 hN

/-- X7: the parts of a passed CHECK RECX -/
theorem checkRecXL_parts (A : Tab) (p : List Int) (L D a b c e : Int) (n0 nb : Nat)
    (h : checkRecXL A p L D a b c e n0 nb = true) :
    pev (p ++ [1]) 1 = 0 ∧ pev (p ++ [1]) 2 = 0 ∧ pev (p ++ [1]) 4 = 0 ∧ pev (p ++ [1]) L = 0 ∧ n0 ≤ nb ∧
      (∀ m, nb ≤ m → lin (p ++ [1]) (fun k => (it A D4 (f4 A) k 0 : Int)) m = 0) ∧
      (∀ m, nb ≤ m → lin (p ++ [1]) (fun k => (it A DX (f4 A) k 0 : Int)) m = 0) ∧
      (∀ m, nb ≤ m → lin (p ++ [1]) (fun k => (it A DY (f4 A) k 0 : Int)) m = 0) ∧
      (∀ m, nb ≤ m → lin (p ++ [1]) (fun k => (it A D0 (f4 A) k 0 : Int)) m = 0) ∧
      ∀ n, n0 ≤ n → n < nb + p.length → D * cnt A n = a * 4 ^ n + b * 2 ^ n + c + e * L ^ n := by
  unfold checkRecXL at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h4⟩, hL⟩, hn⟩, r4⟩, rX⟩, rY⟩, r0⟩, hb⟩ := h
  refine ⟨h1, h2, h4, hL, hn, recAtX_sound A D4 (by decide) p nb r4, recAtX_sound A DX (by decide) p nb rX,
    recAtX_sound A DY (by decide) p nb rY, recAtX_sound A D0 (by decide) p nb r0, fun n hn1 hn2 => ?_⟩
  have hf := beq_iff_eq.mp (List.all_eq_true.mp hb (n - n0) (List.mem_range.mpr (by omega)))
  rw [show n0 + (n - n0) = n by omega, sv_eq] at hf
  exact hf

end VN
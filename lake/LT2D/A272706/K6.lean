-- A272706 / Rule 515, file K6 (core Lean only): linear recurrences of the digit-string sums from n = 2 on
-- (finite base checks over the 15 states by kernel decide, propagated by linearity), their closed forms at the
-- start state, and the core count identity.
import LT2D.A272706.K5
namespace A272706

/-! ## R1-R4: linear recurrences of the vectors it D f4 n from n = 2 on -/

/-- R1 -/
theorem tr_lt (q d : Nat) (hq : q < 15) (hd : d < 8) : tr q d < 15 := by
  have h : ∀ q, q < 15 → ∀ d, d < 8 → tr q d < 15 := by decide
  exact h q hq d hd

/-- R2: one backward step preserves a linear relation -/
theorem AD_comb (D : List Nat) (a b c e : Nat) (g1 g2 g3 g4 : Nat → Nat) (q : Nat)
    (h : ∀ d ∈ D, a * g1 (tr q d) + b * g2 (tr q d) = c * g3 (tr q d) + e * g4 (tr q d)) :
    a * AD D g1 q + b * AD D g2 q = c * AD D g3 q + e * AD D g4 q := by
  induction D with
  | nil => show a * 0 + b * 0 = c * 0 + e * 0; omega
  | cons d D ih =>
    have hd := h d (List.mem_cons_self ..)
    have hD := ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))
    show a * (g1 (tr q d) + AD D g1 q) + b * (g2 (tr q d) + AD D g2 q) =
      c * (g3 (tr q d) + AD D g3 q) + e * (g4 (tr q d) + AD D g4 q)
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega

/-- R3: a relation between the vectors at indices i1..i4 propagates to n + i1..n + i4 -/
theorem it_comb (D : List Nat) (hD : ∀ d ∈ D, d < 8) (g : Nat → Nat) (a b c e i1 i2 i3 i4 : Nat)
    (h0 : ∀ q, q < 15 → a * it D g i1 q + b * it D g i2 q = c * it D g i3 q + e * it D g i4 q)
    (n q : Nat) (hq : q < 15) :
    a * it D g (n + i1) q + b * it D g (n + i2) q = c * it D g (n + i3) q + e * it D g (n + i4) q := by
  induction n generalizing q with
  | zero => simp only [Nat.zero_add]; exact h0 q hq
  | succ n ih =>
    rw [show n + 1 + i1 = (n + i1) + 1 by omega, show n + 1 + i2 = (n + i2) + 1 by omega,
      show n + 1 + i3 = (n + i3) + 1 by omega, show n + 1 + i4 = (n + i4) + 1 by omega]
    exact AD_comb D a b c e _ _ _ _ q (fun d hd => ih (tr q d) (tr_lt q d hq (hD d hd)))

/-- R4: base checks at n = 2 (kernel), minimal polynomials x^2 (x-1)(x-2)(x-4), x^2 (x-1)(x-2), x^2 (x-1) -/
theorem base4 : ∀ q, q < 15 →
    1 * it D4 f4 5 q + 14 * it D4 f4 3 q = 7 * it D4 f4 4 q + 8 * it D4 f4 2 q := by
  decide +kernel

theorem baseX : ∀ q, q < 15 →
    1 * it DX f4 4 q + 2 * it DX f4 2 q = 3 * it DX f4 3 q + 0 * it DX f4 2 q := by
  decide +kernel

theorem baseY : ∀ q, q < 15 →
    1 * it DY f4 4 q + 2 * it DY f4 2 q = 3 * it DY f4 3 q + 0 * it DY f4 2 q := by
  decide +kernel

theorem base0 : ∀ q, q < 15 →
    1 * it D0 f4 3 q + 0 * it D0 f4 2 q = 1 * it D0 f4 2 q + 0 * it D0 f4 2 q := by
  decide +kernel

/-! ## Q1-Q5: closed forms at the start state 0 -/

/-- Q1 -/
theorem Q_closed (m : Nat) : it D4 f4 (m + 2) 0 + 6 * 2 ^ m = 12 * 4 ^ m + 1 := by
  have hrec : ∀ k, 1 * it D4 f4 (k + 5) 0 + 14 * it D4 f4 (k + 3) 0 =
      7 * it D4 f4 (k + 4) 0 + 8 * it D4 f4 (k + 2) 0 :=
    fun k => it_comb D4 (by decide) f4 1 14 7 8 5 3 4 2 base4 k 0 (by decide)
  have key : ∀ k, it D4 f4 (k + 2) 0 + 6 * 2 ^ k = 12 * 4 ^ k + 1 ∧
      it D4 f4 (k + 3) 0 + 12 * 2 ^ k = 48 * 4 ^ k + 1 ∧
      it D4 f4 (k + 4) 0 + 24 * 2 ^ k = 192 * 4 ^ k + 1 := by
    intro k
    induction k with
    | zero => decide +kernel
    | succ k ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have r := hrec k
      have p2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      have p4 : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [Nat.pow_succ]; omega
      rw [p2, p4, show k + 1 + 2 = k + 3 from rfl, show k + 1 + 3 = k + 4 from rfl,
        show k + 1 + 4 = k + 5 from rfl]
      refine ⟨by omega, by omega, by omega⟩
  exact (key m).1

/-- Q2 -/
theorem X_closed (m : Nat) : it DX f4 (m + 2) 0 + 1 = 2 * 2 ^ m := by
  have hrec : ∀ k, 1 * it DX f4 (k + 4) 0 + 2 * it DX f4 (k + 2) 0 =
      3 * it DX f4 (k + 3) 0 + 0 * it DX f4 (k + 2) 0 :=
    fun k => it_comb DX (by decide) f4 1 2 3 0 4 2 3 2 baseX k 0 (by decide)
  have key : ∀ k, it DX f4 (k + 2) 0 + 1 = 2 * 2 ^ k ∧ it DX f4 (k + 3) 0 + 1 = 4 * 2 ^ k := by
    intro k
    induction k with
    | zero => decide +kernel
    | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      have r := hrec k
      have p2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      rw [p2, show k + 1 + 2 = k + 3 from rfl, show k + 1 + 3 = k + 4 from rfl]
      refine ⟨by omega, by omega⟩
  exact (key m).1

/-- Q3 -/
theorem Y_closed (m : Nat) : it DY f4 (m + 2) 0 + 1 = 2 * 2 ^ m := by
  have hrec : ∀ k, 1 * it DY f4 (k + 4) 0 + 2 * it DY f4 (k + 2) 0 =
      3 * it DY f4 (k + 3) 0 + 0 * it DY f4 (k + 2) 0 :=
    fun k => it_comb DY (by decide) f4 1 2 3 0 4 2 3 2 baseY k 0 (by decide)
  have key : ∀ k, it DY f4 (k + 2) 0 + 1 = 2 * 2 ^ k ∧ it DY f4 (k + 3) 0 + 1 = 4 * 2 ^ k := by
    intro k
    induction k with
    | zero => decide +kernel
    | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      have r := hrec k
      have p2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      rw [p2, show k + 1 + 2 = k + 3 from rfl, show k + 1 + 3 = k + 4 from rfl]
      refine ⟨by omega, by omega⟩
  exact (key m).1

/-- Q4 -/
theorem O_closed (m : Nat) : it D0 f4 (m + 2) 0 = 1 := by
  have hrec : ∀ k, 1 * it D0 f4 (k + 3) 0 + 0 * it D0 f4 (k + 2) 0 =
      1 * it D0 f4 (k + 2) 0 + 0 * it D0 f4 (k + 2) 0 :=
    fun k => it_comb D0 (by decide) f4 1 0 1 0 3 2 2 2 base0 k 0 (by decide)
  induction m with
  | zero => decide +kernel
  | succ k ih =>
    have r := hrec k
    rw [show k + 1 + 2 = k + 3 from rfl]
    omega

/-- Q5: the core count identity, n ≥ 1 (n = 1 by evaluation): 4Q + O + 8*2^n = 3*4^n + 9 + 2X + 2Y -/
theorem count_core (n : Nat) (hn : 1 ≤ n) :
    4 * it D4 f4 n 0 + it D0 f4 n 0 + 8 * 2 ^ n =
      3 * 4 ^ n + 9 + 2 * it DX f4 n 0 + 2 * it DY f4 n 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  cases m with
  | zero => decide +kernel
  | succ m =>
    have hQ := Q_closed m
    have hX := X_closed m
    have hY := Y_closed m
    have hO := O_closed m
    rw [show m + 1 + 1 = m + 2 from rfl]
    have p2 : 2 ^ (m + 2) = 4 * 2 ^ m := by
      rw [show m + 2 = m + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ]; omega
    have p4 : 4 ^ (m + 2) = 16 * 4 ^ m := by
      rw [show m + 2 = m + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ]; omega
    rw [p2, p4]
    omega

end A272706
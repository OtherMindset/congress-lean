import LT2D.VN.K4
-- VN library, file K5 (core Lean only): the F1 product (one CA step of rule R, with the mask U of used rule
-- indices), CHECK F1, and F1_V / U_V. Generic version of the F1 parts of A272706 K3 (#mwmg2qh7-qxah27) and
-- K4 (#mwmg413f-bj9quu): table A, rule R and mask U are parameters; Rule 515's bit-3 conjunct becomes
-- "bit (c + 2k) of U is set".
namespace VN

/-- the rule: new state = bit (c + 2k) of R (c = own state, k = ON axial neighbours) -/
def rule (R : Nat) (c : Bool) (k : Nat) : Bool := Nat.testBit R (c.toNat + 2 * k)

/-- t-nonzero flag -/
def lTz (a d : Nat) : Nat := max a (dz d)

structure P1 where
  qc : Nat
  qT : Nat
  cT : Nat
  qE : Nat
  cE : Nat
  qW : Nat
  bW : Nat
  qN : Nat
  cN : Nat
  qS : Nat
  bS : Nat
  tz : Nat
deriving DecidableEq

def step1 (A : Tab) (P : P1) (d : Nat) : P1 :=
  ⟨tr A P.qc d, (lT A (P.qT, P.cT) d).1, (lT A (P.qT, P.cT) d).2,
   (lE A (P.qE, P.cE) d).1, (lE A (P.qE, P.cE) d).2, (lW A (P.qW, P.bW) d).1, (lW A (P.qW, P.bW) d).2,
   (lN A (P.qN, P.cN) d).1, (lN A (P.qN, P.cN) d).2, (lS A (P.qS, P.bS) d).1, (lS A (P.qS, P.bS) d).2,
   lTz P.tz d⟩
def start1 : P1 := ⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩

/-- end condition, all further digits 0 (vacuous while t = 0): lanes T, E, N read one more triple holding
their pending carry (4cT, cE, 2cN), lanes W, S a zero triple; a borrow still pending means x = 0 (or y = 0):
use the mirror value (lane E or N). Checked: the step of rule R, and bit (c + 2k) of U -/
def end1 (A : Tab) (R U : Nat) (P : P1) : Bool :=
  P.tz == 0 ||
    (let vE := out A (tr A P.qE P.cE)
     let vN := out A (tr A P.qN (2 * P.cN))
     let vW := if P.bW = 1 then vE else out A (tr A P.qW 0)
     let vS := if P.bS = 1 then vN else out A (tr A P.qS 0)
     let k := vE.toNat + vW.toNat + vN.toNat + vS.toNat
     (out A (tr A P.qT (4 * P.cT)) == rule R (out A P.qc) k) &&
       Nat.testBit U ((out A P.qc).toNat + 2 * k))

/-- key of a product state (states < 1024; a collision only makes the check fail, never pass wrongly) -/
def key1 (P : P1) : Nat :=
  mix (((((((((((P.qc * 1024 + P.qT) * 1024 + P.qE) * 1024 + P.qW) * 1024 + P.qN) * 1024 + P.qS)
    * 2 + P.cT) * 2 + P.cE) * 2 + P.bW) * 2 + P.cN) * 2 + P.bS) * 2 + P.tz)

/-- CHECK F1 (kernel): one step of rule R from every cell, with every used index c + 2k in the mask U -/
def checkF1 (A : Tab) (R U : Nat) : Bool :=
  certOK key1 (step1 A) (end1 A R U) start1 (explore key1 (step1 A) fuel [start1] .leaf)

theorem lTz_run (L : Nat) : ∀ a x y t : Nat, a ≤ 1 →
    prun lTz L a x y t = if t % 2 ^ L = 0 then a else 1 := by
  induction L with
  | zero =>
    intro a x y t ha
    have h0 : prun lTz 0 a x y t = a := rfl
    rw [h0, Nat.pow_zero, Nat.mod_one, if_pos rfl]
  | succ L ih =>
    intro a x y t ha
    have hstep : prun lTz (L + 1) a x y t
        = prun lTz L (lTz a (dg x y t)) (x / 2) (y / 2) (t / 2) := rfl
    have hd : dz (dg x y t) = t % 2 := by
      unfold dz dg; omega
    have hl : lTz a (dg x y t) = max a (t % 2) := by
      unfold lTz; rw [hd]
    have hm : max a (t % 2) ≤ 1 := by omega
    rw [hstep, hl, ih (max a (t % 2)) (x / 2) (y / 2) (t / 2) hm, pow_split_aux]
    generalize t / 2 % 2 ^ L = m
    by_cases hm0 : m = 0
    · rw [if_pos hm0]
      by_cases ht : t % 2 = 0
      · rw [if_pos (by omega : t % 2 + 2 * m = 0), ht]
        simp
      · have h1 : t % 2 = 1 := by omega
        rw [if_neg (by omega : ¬ (t % 2 + 2 * m = 0)), h1, Nat.max_def]
        split <;> omega
    · rw [if_neg hm0, if_neg (by omega : ¬ (t % 2 + 2 * m = 0))]

/-- E2: the F1 end condition holds after every digit string -/
theorem cert1_sound (A : Tab) (R U : Nat) (h1 : checkF1 A R U = true) (L x y z : Nat) :
    end1 A R U (prun (step1 A) L start1 x y z) = true :=
  cert_sound key1 (step1 A) (end1 A R U) start1 (explore key1 (step1 A) fuel [start1] .leaf) h1 L x y z

/-- number of ON axial neighbours of (x, y) at time t, with the mirror at x = 0 and y = 0 -/
def kV (A : Tab) (x y t : Nat) : Nat :=
  (V A (x + 1) y t).toNat + (if x = 0 then V A 1 y t else V A (x - 1) y t).toNat +
  (V A x (y + 1) t).toNat + (if y = 0 then V A x 1 t else V A x (y - 1) t).toNat

/-- F1 with the mask conjunct: the certificate's end condition, read as a statement about V -/
theorem F1_both (A : Tab) (R U : Nat) (h1 : checkF1 A R U = true) (x y t : Nat) (ht : 1 ≤ t) :
    V A x y (t + 1) = rule R (V A x y t) (kV A x y t) ∧
      Nat.testBit U ((V A x y t).toNat + 2 * kV A x y t) = true := by
  have hlt : ∀ m : Nat, m < 2 ^ m := by
    intro m
    induction m with
    | zero => decide
    | succ m ih => rw [Nat.pow_succ]; omega
  -- L digits: x + 1, y + 1, t + 1 < 2^L, so every carry and every further digit is 0
  obtain ⟨L, hx, hy, htt⟩ : ∃ L, x + 1 < 2 ^ L ∧ y + 1 < 2 ^ L ∧ t + 1 < 2 ^ L :=
    ⟨x + y + t + 2,
      Nat.lt_of_lt_of_le (hlt _) (Nat.pow_le_pow_right (by decide) (by omega)),
      Nat.lt_of_lt_of_le (hlt _) (Nat.pow_le_pow_right (by decide) (by omega)),
      Nat.lt_of_lt_of_le (hlt _) (Nat.pow_le_pow_right (by decide) (by omega))⟩
  have hend := cert1_sound A R U h1 L x y t
  -- the product run, lane by lane (L6)
  have pc : (prun (step1 A) L start1 x y t).qc = run A L 0 x y t :=
    prun_proj (step1 A) (tr A) (fun P => P.qc) (fun _ _ => rfl) L start1 x y t
  have pT : ((prun (step1 A) L start1 x y t).qT, (prun (step1 A) L start1 x y t).cT) =
      prun (lT A) L (0, 1) x y t :=
    prun_proj (step1 A) (lT A) (fun P => (P.qT, P.cT)) (fun _ _ => rfl) L start1 x y t
  have pE : ((prun (step1 A) L start1 x y t).qE, (prun (step1 A) L start1 x y t).cE) =
      prun (lE A) L (0, 1) x y t :=
    prun_proj (step1 A) (lE A) (fun P => (P.qE, P.cE)) (fun _ _ => rfl) L start1 x y t
  have pW : ((prun (step1 A) L start1 x y t).qW, (prun (step1 A) L start1 x y t).bW) =
      prun (lW A) L (0, 1) x y t :=
    prun_proj (step1 A) (lW A) (fun P => (P.qW, P.bW)) (fun _ _ => rfl) L start1 x y t
  have pN : ((prun (step1 A) L start1 x y t).qN, (prun (step1 A) L start1 x y t).cN) =
      prun (lN A) L (0, 1) x y t :=
    prun_proj (step1 A) (lN A) (fun P => (P.qN, P.cN)) (fun _ _ => rfl) L start1 x y t
  have pS : ((prun (step1 A) L start1 x y t).qS, (prun (step1 A) L start1 x y t).bS) =
      prun (lS A) L (0, 1) x y t :=
    prun_proj (step1 A) (lS A) (fun P => (P.qS, P.bS)) (fun _ _ => rfl) L start1 x y t
  have pz : (prun (step1 A) L start1 x y t).tz = prun lTz L 0 x y t :=
    prun_proj (step1 A) lTz (fun P => P.tz) (fun _ _ => rfl) L start1 x y t
  generalize prun (step1 A) L start1 x y t = P at hend pc pT pE pW pN pS pz
  -- lane semantics (D1-D7, F1a)
  obtain ⟨hT1, hT2⟩ := lT_run A L 0 1 x y t (by decide)
  obtain ⟨hE1, hE2⟩ := lE_run A L 0 1 x y t (by decide)
  obtain ⟨hN1, hN2⟩ := lN_run A L 0 1 x y t (by decide)
  rw [← pT] at hT1 hT2
  rw [← pE] at hE1 hE2
  rw [← pN] at hN1 hN2
  simp only at hT1 hT2 hE1 hE2 hN1 hN2
  rw [Nat.div_eq_of_lt (by omega : t < 2 ^ L), Nat.div_eq_of_lt htt] at hT2
  rw [Nat.div_eq_of_lt (by omega : x < 2 ^ L), Nat.div_eq_of_lt hx] at hE2
  rw [Nat.div_eq_of_lt (by omega : y < 2 ^ L), Nat.div_eq_of_lt hy] at hN2
  have hcT : P.cT = 0 := by omega
  have hcE : P.cE = 0 := by omega
  have hcN : P.cN = 0 := by omega
  have hbW : P.bW = if x % 2 ^ L < 1 then 1 else 0 := by
    have h := lW_borrow A L 0 1 x y t (by decide)
    rw [← pW] at h
    exact h
  have hbS : P.bS = if y % 2 ^ L < 1 then 1 else 0 := by
    have h := lS_borrow A L 0 1 x y t (by decide)
    rw [← pS] at h
    exact h
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ L)] at hbW
  rw [Nat.mod_eq_of_lt (by omega : y < 2 ^ L)] at hbS
  have htz : P.tz = 1 := by
    rw [pz, lTz_run L 0 x y t (by decide), Nat.mod_eq_of_lt (by omega : t < 2 ^ L),
      if_neg (by omega)]
  -- the automaton values as outputs of the lanes (padding: L1, L5)
  have hVc : V A x y t = out A P.qc := by
    rw [pc]
    exact (out_run_eq_V A L x y t (by omega) (by omega) (by omega)).symm
  have hVT : V A x y (t + 1) = out A (tr A P.qT (4 * P.cT)) := by
    rw [hcT, Nat.mul_zero, tr_zero_out, hT1]
    exact (out_run_eq_V A L x y (t + 1) (by omega) (by omega) htt).symm
  have hVE : V A (x + 1) y t = out A (tr A P.qE P.cE) := by
    rw [hcE, tr_zero_out, hE1]
    exact (out_run_eq_V A L (x + 1) y t hx (by omega) (by omega)).symm
  have hVN : V A x (y + 1) t = out A (tr A P.qN (2 * P.cN)) := by
    rw [hcN, Nat.mul_zero, tr_zero_out, hN1]
    exact (out_run_eq_V A L x (y + 1) t (by omega) hy (by omega)).symm
  -- west / south: a pending borrow means x = 0 (y = 0): the mirror value
  have hVW : (if x = 0 then V A 1 y t else V A (x - 1) y t) =
      (if P.bW = 1 then out A (tr A P.qE P.cE) else out A (tr A P.qW 0)) := by
    by_cases hx0 : x = 0
    · have hb : P.bW = 1 := by rw [hbW, if_pos (by omega)]
      rw [if_pos hx0, if_pos hb, ← hVE]
      subst hx0
      rfl
    · have hb : P.bW = 0 := by rw [hbW, if_neg (by omega)]
      rw [if_neg hx0, hb, if_neg (by decide), tr_zero_out]
      have h := lW_run A L 0 1 x y t (by decide) (by omega)
      rw [← pW] at h
      simp only at h
      rw [h]
      exact (out_run_eq_V A L (x - 1) y t (by omega) (by omega) (by omega)).symm
  have hVS : (if y = 0 then V A x 1 t else V A x (y - 1) t) =
      (if P.bS = 1 then out A (tr A P.qN (2 * P.cN)) else out A (tr A P.qS 0)) := by
    by_cases hy0 : y = 0
    · have hb : P.bS = 1 := by rw [hbS, if_pos (by omega)]
      rw [if_pos hy0, if_pos hb, ← hVN]
      subst hy0
      rfl
    · have hb : P.bS = 0 := by rw [hbS, if_neg (by omega)]
      rw [if_neg hy0, hb, if_neg (by decide), tr_zero_out]
      have h := lS_run A L 0 1 x y t (by decide) (by omega)
      rw [← pS] at h
      simp only at h
      rw [h]
      exact (out_run_eq_V A L x (y - 1) t (by omega) (by omega) (by omega)).symm
  -- the certificate's end condition is exactly the claim (both conjuncts)
  unfold kV
  rw [hVT, hVW, hVS, hVE, hVN, hVc]
  have htz0 : (P.tz == 0) = false := by simp [htz]
  simp only [end1, htz0, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hend
  exact hend

/-- F1_V: for t ≥ 1, V at time t + 1 is one step of rule R from V at time t (mirror at x = 0, y = 0) -/
theorem F1_V (A : Tab) (R U : Nat) (h1 : checkF1 A R U = true) (x y t : Nat) (ht : 1 ≤ t) :
    V A x y (t + 1) = rule R (V A x y t) (kV A x y t) :=
  (F1_both A R U h1 x y t ht).1

/-- U_V: for t ≥ 1, every index c + 2k used at time t is in the mask U -/
theorem U_V (A : Tab) (R U : Nat) (h1 : checkF1 A R U = true) (x y t : Nat) (ht : 1 ≤ t) :
    Nat.testBit U ((V A x y t).toNat + 2 * kV A x y t) = true :=
  (F1_both A R U h1 x y t ht).2

/-- R' agrees with R at every index i < 10 (i = c + 2k) whose bit is set in the mask U -/
def agreeOn (U R R' : Nat) : Bool :=
  (List.range 10).all (fun i => !(Nat.testBit U i) || (Nat.testBit R i == Nat.testBit R' i))

theorem kV_le (A : Tab) (x y t : Nat) : kV A x y t ≤ 4 := by
  have h : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide
  have h1 := h (V A (x + 1) y t)
  have h2 := h (if x = 0 then V A 1 y t else V A (x - 1) y t)
  have h3 := h (V A x (y + 1) t)
  have h4 := h (if y = 0 then V A x 1 t else V A x (y - 1) t)
  unfold kV
  omega

/-- at an index in U, rules that agree on U give the same new state -/
theorem agree_bit (U R R' : Nat) (hU : agreeOn U R R' = true) (c : Bool) (k : Nat) (hk : k ≤ 4)
    (hu : Nat.testBit U (c.toNat + 2 * k) = true) : rule R c k = rule R' c k := by
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  have h := List.all_eq_true.mp hU (c.toNat + 2 * k) (List.mem_range.mpr (by omega))
  rw [hu] at h
  unfold rule
  simpa using h

end VN
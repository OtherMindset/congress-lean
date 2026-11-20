-- A272706 / Rule 515, file K4 (core Lean only): F1_V and NB3_V, the automaton-side bridge for one CA step.
-- Adapted from A273331 K7 (#mwlzsauz-jspoq8): the same lane bookkeeping, with the bit-3 conjunct of end1.
import LongTable.P_mwmg2qh7_qxah27
namespace A272706

/-! ## D6, D7: the south lane (verbatim from A273331 K2b #mwlxzncp-r3jax1) -/

theorem lS_step_aux (q c x y t : Nat) (h : c ≤ y) :
    lS (q, c) (dg x y t) = (tr q (dg x (y - c) t), if y % 2 < c then 1 else 0) := by
  have h1 : tri (dx (dg x y t)) (sD (dy (dg x y t)) 0 c) (dz (dg x y t))
      = dg x (y - c) t := by
    rw [dx_dg_aux, dy_dg_aux, dz_dg_aux]
    unfold tri sD dg
    omega
  have h2 : sB (dy (dg x y t)) 0 c = if y % 2 < c then 1 else 0 := by
    rw [dy_dg_aux]
    unfold sB
    simp
  unfold lS
  rw [h1, h2]

theorem lS_run_aux (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 → c ≤ y →
    (prun lS L (q, c) x y t).1 = run L q x (y - c) t := by
  induction L with
  | zero =>
    intro q c x y t _ _
    simp [prun, run]
  | succ L ih =>
    intro q c x y t hc h
    have hc' : (if y % 2 < c then 1 else 0) ≤ 1 := by split <;> omega
    have hc'' : (if y % 2 < c then 1 else 0) ≤ y / 2 := by split <;> omega
    have e : (y - c) / 2 = y / 2 - (if y % 2 < c then 1 else 0) := by split <;> omega
    have ih1 := ih (tr q (dg x (y - c) t)) (if y % 2 < c then 1 else 0) (x / 2) (y / 2) (t / 2) hc' hc''
    simp only [prun, run]
    rw [lS_step_aux q c x y t h, e]
    exact ih1

theorem lS_run (L q c x y t : Nat) (hc : c ≤ 1) (h : c ≤ y) :
    (prun lS L (q, c) x y t).1 = run L q x (y - c) t :=
  lS_run_aux L q c x y t hc h

/-- y % 2^(L+1) splits as its lowest bit plus 2 times (y/2) % 2^L -/
theorem lS_borrow_pow_split_aux (L x : Nat) :
    x % 2 ^ (L + 1) = x % 2 + 2 * (x / 2 % 2 ^ L) := by
  have hP : 0 < 2 ^ L := by
    first
    | exact Nat.two_pow_pos L
    | exact Nat.pos_pow_of_pos L (by decide)
    | simp
  have hm := Nat.div_add_mod (x / 2) (2 ^ L)
  have hr := Nat.mod_lt (x / 2) hP
  have hx := Nat.div_add_mod x 2
  have e2 : 2 * 2 ^ L * (x / 2 / 2 ^ L) = 2 * (2 ^ L * (x / 2 / 2 ^ L)) :=
    Nat.mul_assoc 2 (2 ^ L) (x / 2 / 2 ^ L)
  have e : x = x % 2 + 2 * (x / 2 % 2 ^ L) + 2 * 2 ^ L * (x / 2 / 2 ^ L) := by
    omega
  have h5 : x % (2 * 2 ^ L) = (x % 2 + 2 * (x / 2 % 2 ^ L) + 2 * 2 ^ L * (x / 2 / 2 ^ L))
      % (2 * 2 ^ L) := congrArg (fun z => z % (2 * 2 ^ L)) e
  have h6 : x % 2 + 2 * (x / 2 % 2 ^ L) < 2 * 2 ^ L := by omega
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ L) 2, h5, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h6]

theorem lS_borrow_aux (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 →
    (prun lS L (q, c) x y t).2 = if y % 2 ^ L < c then 1 else 0 := by
  induction L with
  | zero =>
    intro q c x y t hc
    have h0 : (prun lS 0 (q, c) x y t).2 = c := rfl
    rw [h0]
    have hc2 : c = 0 ∨ c = 1 := by omega
    rcases hc2 with rfl | rfl <;> simp [Nat.mod_one]
  | succ L ih =>
    intro q c x y t hc
    have hstep : prun lS (L + 1) (q, c) x y t
        = prun lS L (lS (q, c) (dg x y t)) (x / 2) (y / 2) (t / 2) := by
      first
      | rfl
      | simp only [prun]
    have hb : (lS (q, c) (dg x y t)).2 = if y % 2 < c then 1 else 0 := by
      first
      | simp [lS, sB, dy_dg_aux]
      | (unfold lS sB; rw [dy_dg_aux]; simp)
    have hc' : (lS (q, c) (dg x y t)).2 ≤ 1 := by
      rw [hb]
      by_cases h1 : y % 2 < c
      · rw [if_pos h1]; decide
      · rw [if_neg h1]; decide
    have ih' : (prun lS L (lS (q, c) (dg x y t)) (x / 2) (y / 2) (t / 2)).2
        = if y / 2 % 2 ^ L < (lS (q, c) (dg x y t)).2 then 1 else 0 :=
      ih (lS (q, c) (dg x y t)).1 (lS (q, c) (dg x y t)).2 (x / 2) (y / 2) (t / 2) hc'
    rw [hstep, ih', hb, lS_borrow_pow_split_aux L y]
    by_cases h1 : y % 2 < c
    · rw [if_pos h1]
      by_cases h2 : y / 2 % 2 ^ L < 1
      · have h3 : y % 2 + 2 * (y / 2 % 2 ^ L) < c := by omega
        rw [if_pos h2, if_pos h3]
      · have h3 : ¬ (y % 2 + 2 * (y / 2 % 2 ^ L) < c) := by omega
        rw [if_neg h2, if_neg h3]
    · rw [if_neg h1]
      have h2 : ¬ (y / 2 % 2 ^ L < 0) := by omega
      have h3 : ¬ (y % 2 + 2 * (y / 2 % 2 ^ L) < c) := by omega
      rw [if_neg h2, if_neg h3]

theorem lS_borrow (L q c x y t : Nat) (hc : c ≤ 1) :
    (prun lS L (q, c) x y t).2 = if y % 2 ^ L < c then 1 else 0 :=
  lS_borrow_aux L q c x y t hc

/-- number of ON axial neighbours of (x, y) at time t, with the mirror at x = 0 and y = 0 -/
def kV (x y t : Nat) : Nat :=
  (V (x + 1) y t).toNat + (if x = 0 then V 1 y t else V (x - 1) y t).toNat +
  (V x (y + 1) t).toNat + (if y = 0 then V x 1 t else V x (y - 1) t).toNat

/-- F1 with the bit-3 conjunct: the certificate's end condition, read as a statement about V -/
theorem F1_both (x y t : Nat) (ht : 1 ≤ t) :
    V x y (t + 1) = rule (V x y t) (kV x y t) ∧ ¬ (V x y t = true ∧ kV x y t = 1) := by
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
  have hend := cert1_sound L x y t
  -- the product run, lane by lane (L6)
  have pc : (prun step1 L start1 x y t).qc = run L 0 x y t :=
    prun_proj step1 tr (fun P => P.qc) (fun _ _ => rfl) L start1 x y t
  have pT : ((prun step1 L start1 x y t).qT, (prun step1 L start1 x y t).cT) =
      prun lT L (0, 1) x y t :=
    prun_proj step1 lT (fun P => (P.qT, P.cT)) (fun _ _ => rfl) L start1 x y t
  have pE : ((prun step1 L start1 x y t).qE, (prun step1 L start1 x y t).cE) =
      prun lE L (0, 1) x y t :=
    prun_proj step1 lE (fun P => (P.qE, P.cE)) (fun _ _ => rfl) L start1 x y t
  have pW : ((prun step1 L start1 x y t).qW, (prun step1 L start1 x y t).bW) =
      prun lW L (0, 1) x y t :=
    prun_proj step1 lW (fun P => (P.qW, P.bW)) (fun _ _ => rfl) L start1 x y t
  have pN : ((prun step1 L start1 x y t).qN, (prun step1 L start1 x y t).cN) =
      prun lN L (0, 1) x y t :=
    prun_proj step1 lN (fun P => (P.qN, P.cN)) (fun _ _ => rfl) L start1 x y t
  have pS : ((prun step1 L start1 x y t).qS, (prun step1 L start1 x y t).bS) =
      prun lS L (0, 1) x y t :=
    prun_proj step1 lS (fun P => (P.qS, P.bS)) (fun _ _ => rfl) L start1 x y t
  have pz : (prun step1 L start1 x y t).tz = prun lTz L 0 x y t :=
    prun_proj step1 lTz (fun P => P.tz) (fun _ _ => rfl) L start1 x y t
  generalize prun step1 L start1 x y t = P at hend pc pT pE pW pN pS pz
  -- lane semantics (D1-D7, F1a)
  obtain ⟨hT1, hT2⟩ := lT_run L 0 1 x y t (by decide)
  obtain ⟨hE1, hE2⟩ := lE_run L 0 1 x y t (by decide)
  obtain ⟨hN1, hN2⟩ := lN_run L 0 1 x y t (by decide)
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
    have h := lW_borrow L 0 1 x y t (by decide)
    rw [← pW] at h
    exact h
  have hbS : P.bS = if y % 2 ^ L < 1 then 1 else 0 := by
    have h := lS_borrow L 0 1 x y t (by decide)
    rw [← pS] at h
    exact h
  rw [Nat.mod_eq_of_lt (by omega : x < 2 ^ L)] at hbW
  rw [Nat.mod_eq_of_lt (by omega : y < 2 ^ L)] at hbS
  have htz : P.tz = 1 := by
    rw [pz, lTz_run L 0 x y t (by decide), Nat.mod_eq_of_lt (by omega : t < 2 ^ L),
      if_neg (by omega)]
  -- the automaton values as outputs of the lanes (padding: L1, L5)
  have hVc : V x y t = out P.qc := by
    rw [pc]
    exact (out_run_eq_V L x y t (by omega) (by omega) (by omega)).symm
  have hVT : V x y (t + 1) = out (tr P.qT (4 * P.cT)) := by
    rw [hcT, Nat.mul_zero, tr_zero_out, hT1]
    exact (out_run_eq_V L x y (t + 1) (by omega) (by omega) htt).symm
  have hVE : V (x + 1) y t = out (tr P.qE P.cE) := by
    rw [hcE, tr_zero_out, hE1]
    exact (out_run_eq_V L (x + 1) y t hx (by omega) (by omega)).symm
  have hVN : V x (y + 1) t = out (tr P.qN (2 * P.cN)) := by
    rw [hcN, Nat.mul_zero, tr_zero_out, hN1]
    exact (out_run_eq_V L x (y + 1) t (by omega) hy (by omega)).symm
  -- west / south: a pending borrow means x = 0 (y = 0): the mirror value
  have hVW : (if x = 0 then V 1 y t else V (x - 1) y t) =
      (if P.bW = 1 then out (tr P.qE P.cE) else out (tr P.qW 0)) := by
    by_cases hx0 : x = 0
    · have hb : P.bW = 1 := by rw [hbW, if_pos (by omega)]
      rw [if_pos hx0, if_pos hb, ← hVE]
      subst hx0
      rfl
    · have hb : P.bW = 0 := by rw [hbW, if_neg (by omega)]
      rw [if_neg hx0, hb, if_neg (by decide), tr_zero_out]
      have h := lW_run L 0 1 x y t (by decide) (by omega)
      rw [← pW] at h
      simp only at h
      rw [h]
      exact (out_run_eq_V L (x - 1) y t (by omega) (by omega) (by omega)).symm
  have hVS : (if y = 0 then V x 1 t else V x (y - 1) t) =
      (if P.bS = 1 then out (tr P.qN (2 * P.cN)) else out (tr P.qS 0)) := by
    by_cases hy0 : y = 0
    · have hb : P.bS = 1 := by rw [hbS, if_pos (by omega)]
      rw [if_pos hy0, if_pos hb, ← hVN]
      subst hy0
      rfl
    · have hb : P.bS = 0 := by rw [hbS, if_neg (by omega)]
      rw [if_neg hy0, hb, if_neg (by decide), tr_zero_out]
      have h := lS_run L 0 1 x y t (by decide) (by omega)
      rw [← pS] at h
      simp only at h
      rw [h]
      exact (out_run_eq_V L x (y - 1) t (by omega) (by omega) (by omega)).symm
  -- the certificate's end condition is exactly the claim (both conjuncts)
  unfold kV
  rw [hVT, hVW, hVS, hVE, hVN, hVc]
  have h1 : (P.tz == 0) = false := by simp [htz]
  simp only [end1, h1, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hend
  refine ⟨hend.1, fun ⟨hc, hk⟩ => ?_⟩
  have h2 := hend.2
  rw [hc, hk] at h2
  exact absurd h2 (by decide)

/-- F1 (bridge, automaton side): one step of Rule 515 on the quadrant, mirror at x = 0 and y = 0 -/
theorem F1_V (x y t : Nat) (ht : 1 ≤ t) : V x y (t + 1) = rule (V x y t) (kV x y t) :=
  (F1_both x y t ht).1

/-- NB3: an ON cell never has exactly one ON neighbour (bit 3: the only input where 515 and 523 differ) -/
theorem NB3_V (x y t : Nat) (ht : 1 ≤ t) (h : V x y t = true) : kV x y t ≠ 1 :=
  fun hk => (F1_both x y t ht).2 ⟨h, hk⟩

end A272706
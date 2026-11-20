import LT2D.VN.K5
-- VN library extension, file K8 (core Lean only): CHUNKED CHECK F1. The F1 product states are given as a LIST
-- certificate (packed in numbers, unpacked by the kernel) cut into slices; each slice is checked against the index tree
-- of the whole list in its own declaration (one `decide +kernel` theorem per slice in the instance), so no single
-- declaration explores the whole product. Soundness: VN_K2's cert_sound_list with no escape states. Conclusion
-- (F1_both_chunked) = the conclusion of VN_K5's F1_both. Imports the posted VN_K5 only; no posted file changes.
-- F1_both_of_end is VN_K5's proof of F1_both, copied by script, with the hypothesis checkF1 replaced by its use.
namespace VN

/-- unpack k product states from w: per state 6 bits (cT, cE, bW, cN, bS, tz from bit 0), then qc, qT, qE, qW, qN,
qS in b bits each. Whatever list this produces is checked by sliceOK, never trusted. -/
def unpack (b : Nat) : Nat → Nat → List P1
  | 0, _ => []
  | k + 1, w =>
    let m := 2 ^ b
    let f := w / 64
    ⟨f % m, f / m % m, w % 2, f / m ^ 2 % m, w / 2 % 2, f / m ^ 3 % m, w / 4 % 2, f / m ^ 4 % m, w / 8 % 2,
      f / m ^ 5 % m, w / 16 % 2, w / 32 % 2⟩ :: unpack b k (w / (64 * m ^ 6))

/-- the number with base-2^c digits l (least significant first): an instance writes each packed number as short
literals (no run of 160+ digits in a posted file) -/
def ofDigits (c : Nat) : List Nat → Nat
  | [] => 0
  | d :: l => d + 2 ^ c * ofDigits c l

/-- one slice of a list certificate: every state in it meets the F1 end condition (rule R, mask U) and its 8
successors are found in the index tree t -/
def sliceOK (A : Tab) (R U : Nat) (t : BT P1) (sl : List P1) : Bool :=
  sl.all fun P => end1 A R U P && [0, 1, 2, 3, 4, 5, 6, 7].all fun d => t.find (key1 (step1 A P d)) (step1 A P d)

/-- E2 for a sliced list certificate: the F1 end condition holds after every digit string -/
theorem cert1_sound_chunked (A : Tab) (R U : Nat) (sls : List (List P1))
    (hstart : (BT.ofList key1 sls.flatten).find (key1 start1) start1 = true)
    (hsl : ∀ sl ∈ sls, sliceOK A R U (BT.ofList key1 sls.flatten) sl = true)
    (L x y z : Nat) : end1 A R U (prun (step1 A) L start1 x y z) = true := by
  refine cert_sound_list key1 (step1 A) (end1 A R U) (fun _ => false) start1 sls.flatten
    (fun _ _ h => h) (fun _ h => by simp at h) hstart ?_ L x y z
  intro P hP
  obtain ⟨sl, hmem, hPsl⟩ := List.mem_flatten.mp hP
  have h := hsl sl hmem
  unfold sliceOK at h
  rw [List.all_eq_true] at h
  have h' := h P hPsl
  rw [Bool.and_eq_true, List.all_eq_true] at h'
  refine ⟨h'.1, fun d hd => Or.inr (h'.2 d ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- VN_K5's F1_both with its certificate step as a hypothesis (proof copied from VN_K5) -/
theorem F1_both_of_end (A : Tab) (R U : Nat)
    (hc : ∀ L x y z : Nat, end1 A R U (prun (step1 A) L start1 x y z) = true) (x y t : Nat) (ht : 1 ≤ t) :
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
  have hend := hc L x y t
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

/-- CHUNKED F1: VN_K5's F1_both conclusion from a sliced list certificate (start state + every slice checked) -/
theorem F1_both_chunked (A : Tab) (R U : Nat) (sls : List (List P1))
    (hstart : (BT.ofList key1 sls.flatten).find (key1 start1) start1 = true)
    (hsl : ∀ sl ∈ sls, sliceOK A R U (BT.ofList key1 sls.flatten) sl = true) (x y t : Nat) (ht : 1 ≤ t) :
    V A x y (t + 1) = rule R (V A x y t) (kV A x y t) ∧
      Nat.testBit U ((V A x y t).toNat + 2 * kV A x y t) = true :=
  F1_both_of_end A R U (cert1_sound_chunked A R U sls hstart hsl) x y t ht

end VN
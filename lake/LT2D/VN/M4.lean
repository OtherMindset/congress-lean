import LT2D.VN.M3
import LT2D.VN.K9
/-
  VN library extension, file M4 (Mathlib, via VN_M3 and VN_K9; no new Mathlib import): the closed form of the count
  combination from the EXTENDED CHECK REC (VN_K9: a monic annihilator P = p ++ [1] with P(1) = P(2) = P(4) = 0) and
  the COUNT THEOREMS vn_count_rec (conclusion = vn_count's), vn_count_recL (with an extra term e*L^n, P(L) = 0) and
  their _chunked versions (F1 hypotheses of VN_M3's vn_count_chunked). onCount_cnt is the first half of the posted
  vn_count proof (VN_M2), copied, with caState_V replaced by the hypothesis hV.
-/
namespace LT2D

open Finset

/-- Y1: lin of the count combination 4Q + O - 2X - 2Y -/
theorem lin_cnt (p : List Int) (u1 u2 u3 u4 : Nat → Int) (n : Nat) :
    VN.lin p (fun k => 4 * u1 k + u2 k - 2 * u3 k - 2 * u4 k) n =
      4 * VN.lin p u1 n + VN.lin p u2 n - 2 * VN.lin p u3 n - 2 * VN.lin p u4 n := by
  induction p generalizing n with
  | nil => simp [VN.lin]
  | cons c p ih => simp only [VN.lin, ih]; ring

/-- Y2: lin of the closed form, through the values of p at 4, 2, 1, L -/
theorem lin_cf (p : List Int) (a b c e L : Int) (n : Nat) :
    VN.lin p (fun k => a * 4 ^ k + b * 2 ^ k + c + e * L ^ k) n =
      a * 4 ^ n * VN.pev p 4 + b * 2 ^ n * VN.pev p 2 + c * VN.pev p 1 + e * L ^ n * VN.pev p L := by
  induction p generalizing n with
  | nil => simp [VN.lin, VN.pev]
  | cons c' p ih => simp only [VN.lin, VN.pev, ih]; ring

/-- Y3: D * lin p u n = lin p v n when D * u = v at n .. n + |p| - 1 -/
theorem lin_mul_congr (p : List Int) (D : Int) (u v : Nat → Int) (n : Nat)
    (h : ∀ i, i < p.length → D * u (n + i) = v (n + i)) : D * VN.lin p u n = VN.lin p v n := by
  induction p generalizing n with
  | nil => simp [VN.lin]
  | cons c p ih =>
    have h0 : D * u n = v n := h 0 (by simp)
    have h1 : D * VN.lin p u (n + 1) = VN.lin p v (n + 1) := ih (n + 1) (fun i hi => by
      rw [show n + 1 + i = n + (i + 1) by omega]
      exact h (i + 1) (by simp only [List.length_cons]; omega))
    simp only [VN.lin]
    rw [← h0, ← h1]
    ring

/-- Y4: the leading coefficient 1 -/
theorem lin_append_one (p : List Int) (u : Nat → Int) (n : Nat) :
    VN.lin (p ++ [1]) u n = VN.lin p u n + u (n + p.length) := by
  induction p generalizing n with
  | nil => simp [VN.lin]
  | cons c p ih =>
    simp only [List.cons_append, VN.lin, ih, List.length_cons]
    rw [show n + 1 + p.length = n + (p.length + 1) by omega]
    ring

/-- Y5: the closed form of the count combination for every n ≥ n0 (extended CHECK REC) -/
theorem cnt_closedXL (A : VN.Tab) (p : List Int) (L D a b c e : Int) (n0 nb : Nat)
    (h : VN.checkRecXL A p L D a b c e n0 nb = true) :
    ∀ n, n0 ≤ n → D * VN.cnt A n = a * 4 ^ n + b * 2 ^ n + c + e * L ^ n := by
  obtain ⟨h1, h2, h4, hL, hn0, r4, rX, rY, r0, hbase⟩ := VN.checkRecXL_parts A p L D a b c e n0 nb h
  have hc : ∀ m, nb ≤ m → VN.lin (p ++ [1]) (VN.cnt A) m = 0 := by
    intro m hm
    have e1 : VN.lin (p ++ [1]) (VN.cnt A) m =
        4 * VN.lin (p ++ [1]) (fun k => (VN.it A VN.D4 (VN.f4 A) k 0 : Int)) m +
          VN.lin (p ++ [1]) (fun k => (VN.it A VN.D0 (VN.f4 A) k 0 : Int)) m -
          2 * VN.lin (p ++ [1]) (fun k => (VN.it A VN.DX (VN.f4 A) k 0 : Int)) m -
          2 * VN.lin (p ++ [1]) (fun k => (VN.it A VN.DY (VN.f4 A) k 0 : Int)) m :=
      lin_cnt (p ++ [1]) _ _ _ _ m
    rw [e1, r4 m hm, r0 m hm, rX m hm, rY m hm]
    ring
  have hf : ∀ m, VN.lin (p ++ [1]) (fun k => a * 4 ^ k + b * 2 ^ k + c + e * L ^ k) m = 0 := by
    intro m
    rw [lin_cf, h1, h2, h4, hL]
    ring
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < nb + p.length
    · exact hbase n hn hlt
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + p.length := ⟨n - p.length, by omega⟩
      have hcm := hc m (by omega)
      have hfm := hf m
      rw [lin_append_one] at hcm hfm
      have hmul := lin_mul_congr p D (VN.cnt A) (fun k => a * 4 ^ k + b * 2 ^ k + c + e * L ^ k) m
        (fun i hi => ih (m + i) (by omega) (by omega))
      have hY : VN.cnt A (m + p.length) = -VN.lin p (VN.cnt A) m := by linarith
      rw [hY, mul_neg, hmul]
      linarith

/-- Y6: the window count at stage 2^n - 1 is the count combination, for a table whose V is the diagram
(the first half of the posted vn_count proof) -/
theorem onCount_cnt (A : VN.Tab) (R : Nat)
    (hV : ∀ (g : Nat) (x y : Int), caState R g (x, y) = VN.V A x.natAbs y.natAbs (g + 1)) (n : Nat) :
    (onCount R (2 ^ n - 1) : Int) = VN.cnt A n := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hg : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hp
  rw [onCount_fold R (2 ^ n - 1) (fun a b => VN.V A a b (2 ^ n)) (fun x y => by rw [hV, hg]), hg]
  have hQ := VN.sq_V A n
  have hX := VN.axX_V A n
  have hY := VN.axY_V A n
  have hO := VN.orig_V A n
  simp only [sumTo_eq_sum] at hQ hX hY
  have hQ' := congrArg (Nat.cast : Nat → Int) hQ
  have hX' := congrArg (Nat.cast : Nat → Int) hX
  have hY' := congrArg (Nat.cast : Nat → Int) hY
  have hO' := congrArg (Nat.cast : Nat → Int) hO
  push_cast at hQ' hX' hY' hO'
  rw [hQ', hX', hY', hO']
  unfold VN.cnt
  ring

/-- COUNT THEOREM (extended CHECK REC, extra term): if CHECK F2, CHECK F1 (mask U) and CHECK RECX pass for the table
A and rule R, then D * a(n) = a*4^n + b*2^n + c + e*L^n for every n ≥ n0, where a(n) = onCount R (2^n - 1) -/
theorem vn_count_recL (A : VN.Tab) (R U : Nat) (p : List Int) (L D a b c e : Int) (n0 nb : Nat)
    (h2 : VN.checkF2 A = true) (h1 : VN.checkF1 A R U = true)
    (hr : VN.checkRecXL A p L D a b c e n0 nb = true) (n : Nat) (hn : n0 ≤ n) :
    D * (onCount R (2 ^ n - 1) : Int) = a * 4 ^ n + b * 2 ^ n + c + e * L ^ n := by
  rw [onCount_cnt A R (caState_V A R U h2 h1) n]
  exact cnt_closedXL A p L D a b c e n0 nb hr n hn

/-- COUNT THEOREM (extended CHECK REC): vn_count's conclusion D * a(n) = a*4^n + b*2^n + c for every n ≥ n0 -/
theorem vn_count_rec (A : VN.Tab) (R U : Nat) (p : List Int) (D a b c : Int) (n0 nb : Nat)
    (h2 : VN.checkF2 A = true) (h1 : VN.checkF1 A R U = true)
    (hr : VN.checkRecX A p D a b c n0 nb = true) (n : Nat) (hn : n0 ≤ n) :
    D * (onCount R (2 ^ n - 1) : Int) = a * 4 ^ n + b * 2 ^ n + c := by
  rw [onCount_cnt A R (caState_V A R U h2 h1) n, cnt_closedXL A p 1 D a b c 0 n0 nb hr n hn]
  ring

/-- vn_count_recL with the chunked F1 check (VN_K8 / VN_M3) -/
theorem vn_count_recL_chunked (A : VN.Tab) (R U : Nat) (p : List Int) (L D a b c e : Int) (n0 nb : Nat)
    (sls : List (List VN.P1)) (h2 : VN.checkF2 A = true)
    (hstart : (VN.BT.ofList VN.key1 sls.flatten).find (VN.key1 VN.start1) VN.start1 = true)
    (hsl : ∀ sl ∈ sls, VN.sliceOK A R U (VN.BT.ofList VN.key1 sls.flatten) sl = true)
    (hr : VN.checkRecXL A p L D a b c e n0 nb = true) (n : Nat) (hn : n0 ≤ n) :
    D * (onCount R (2 ^ n - 1) : Int) = a * 4 ^ n + b * 2 ^ n + c + e * L ^ n := by
  rw [onCount_cnt A R (caState_V_chunked A R U sls h2 hstart hsl) n]
  exact cnt_closedXL A p L D a b c e n0 nb hr n hn

/-- vn_count_rec with the chunked F1 check (VN_K8 / VN_M3) -/
theorem vn_count_rec_chunked (A : VN.Tab) (R U : Nat) (p : List Int) (D a b c : Int) (n0 nb : Nat)
    (sls : List (List VN.P1)) (h2 : VN.checkF2 A = true)
    (hstart : (VN.BT.ofList VN.key1 sls.flatten).find (VN.key1 VN.start1) VN.start1 = true)
    (hsl : ∀ sl ∈ sls, VN.sliceOK A R U (VN.BT.ofList VN.key1 sls.flatten) sl = true)
    (hr : VN.checkRecX A p D a b c n0 nb = true) (n : Nat) (hn : n0 ≤ n) :
    D * (onCount R (2 ^ n - 1) : Int) = a * 4 ^ n + b * 2 ^ n + c := by
  rw [onCount_cnt A R (caState_V_chunked A R U sls h2 hstart hsl) n, cnt_closedXL A p 1 D a b c 0 n0 nb hr n hn]
  ring

end LT2D
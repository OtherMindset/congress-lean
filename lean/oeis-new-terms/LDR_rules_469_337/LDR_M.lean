import LongTable.P_mwnwdkfh_f5rc11
import LongTable.LDR_C
/-
  Leader file LDR_M (Mathlib through the library imports only): Rules 469 and 337 from the posted Rule 558 proof (W3A558).
  Step 1: the W3A558 certificate (used-index mask 895, bit 7 clear) shows no ON cell of Rule 558 ever has exactly 3 ON neighbours.
  Step 2: hence Rule 469 at stage 2m is Rule 558 at stage m, and at stage 2m+1 its complement; Rule 337 at stage 2m is Rule 558
  at stage m, and at stage 2m+1 the complement of Rule 558 at stage m+1.
  Step 3: Rule 558's ON cells at stage m lie in the square [-m,m]^2 (r558_cone). The counts are in LDR_M2 and LDR_M3b.
-/
namespace LT2D

/-- every index c + 2k met in Rule 558's diagram is in the certificate's mask 895 -/
theorem r558_used (g : Nat) (x y : Int) :
    Nat.testBit 895 ((caState 558 g (x, y)).toNat + 2 * nbrOn (caState 558 g) (x, y)) = true := by
  rw [caState_V_chunked VN.W3A558.tab 558 895 VN.W3A558.sls VN.W3A558.ok2 VN.W3A558.ok1s VN.W3A558.ok1 g x y,
    nbrOn_V_chunked VN.W3A558.tab 558 895 VN.W3A558.sls VN.W3A558.ok2 VN.W3A558.ok1s VN.W3A558.ok1 g x y]
  exact (VN.F1_both_chunked VN.W3A558.tab 558 895 VN.W3A558.sls VN.W3A558.ok1s VN.W3A558.ok1 _ _ (g + 1) (by omega)).2

theorem nbrOn_le4 (s : Cell → Bool) (p : Cell) : nbrOn s p ≤ 4 := by
  unfold nbrOn
  cases s (p.1 + 1, p.2) <;> cases s (p.1 - 1, p.2) <;> cases s (p.1, p.2 + 1) <;> cases s (p.1, p.2 - 1) <;> simp

theorem nbrOn_not (s : Cell → Bool) (p : Cell) : nbrOn (fun q => !s q) p = 4 - nbrOn s p := by
  show (!s (p.1 + 1, p.2)).toNat + (!s (p.1 - 1, p.2)).toNat + (!s (p.1, p.2 + 1)).toNat +
    (!s (p.1, p.2 - 1)).toNat = 4 - ((s (p.1 + 1, p.2)).toNat + (s (p.1 - 1, p.2)).toNat +
    (s (p.1, p.2 + 1)).toNat + (s (p.1, p.2 - 1)).toNat)
  cases s (p.1 + 1, p.2) <;> cases s (p.1 - 1, p.2) <;> cases s (p.1, p.2 + 1) <;> cases s (p.1, p.2 - 1) <;> rfl

/-- no ON cell of Rule 558 has exactly 3 ON neighbours (index 7 is never used) -/
theorem r558_no_idx7 (g : Nat) (p : Cell) :
    ¬ (caState 558 g p = true ∧ nbrOn (caState 558 g) p = 3) := by
  obtain ⟨x, y⟩ := p
  rintro ⟨hc, hk⟩
  have h := r558_used g x y
  rw [hc, hk, VN.LDR.u895_bit7] at h
  exact Bool.false_ne_true h

/-- Rule 558's ON cells at stage g lie in the square [-g, g]^2 (bit 0 of 558 is 0) -/
theorem r558_cone (g : Nat) (x y : Int) (h : caState 558 g (x, y) = true) :
    x.natAbs ≤ g ∧ y.natAbs ≤ g := by
  induction g generalizing x y with
  | zero =>
    have h0 : (x, y) = ((0 : Int), (0 : Int)) := of_decide_eq_true h
    simp only [Prod.mk.injEq] at h0
    omega
  | succ g ih =>
    by_contra hc
    have off : ∀ a b : Int, (g < a.natAbs ∨ g < b.natAbs) → caState 558 g (a, b) = false := by
      intro a b hab
      cases hv : caState 558 g (a, b)
      · rfl
      · have := ih a b hv
        omega
    have hc0 : caState 558 g (x, y) = false := off x y (by omega)
    have hk : nbrOn (caState 558 g) (x, y) = 0 := by
      show (caState 558 g (x + 1, y)).toNat + (caState 558 g (x - 1, y)).toNat +
        (caState 558 g (x, y + 1)).toNat + (caState 558 g (x, y - 1)).toNat = 0
      rw [off (x + 1) y (by omega), off (x - 1) y (by omega), off x (y + 1) (by omega), off x (y - 1) (by omega)]
      rfl
    have e : caState 558 (g + 1) (x, y) =
        ruleOut 558 (caState 558 g (x, y)) (nbrOn (caState 558 g) (x, y)) := rfl
    rw [e, hc0, hk] at h
    have b0 : ruleOut 558 false 0 = false := VN.LDR.r558_bit0
    rw [b0] at h
    exact Bool.false_ne_true h

theorem step469_on (m : Nat) (p : Cell) : step 469 (caState 558 m) p = !caState 558 m p := by
  have hk := nbrOn_le4 (caState 558 m) p
  exact (VN.LDR.r469_on (caState 558 m p) ⟨nbrOn (caState 558 m) p, by omega⟩).resolve_left (r558_no_idx7 m p)

theorem step469_off (m : Nat) (p : Cell) :
    step 469 (fun q => !caState 558 m q) p = step 558 (caState 558 m) p := by
  have hk := nbrOn_le4 (caState 558 m) p
  show ruleOut 469 (!caState 558 m p) (nbrOn (fun q => !caState 558 m q) p) =
    ruleOut 558 (caState 558 m p) (nbrOn (caState 558 m) p)
  rw [nbrOn_not]
  exact (VN.LDR.r469_off (caState 558 m p) ⟨nbrOn (caState 558 m) p, by omega⟩).resolve_left (r558_no_idx7 m p)

/-- Rule 469 at stage 2m is Rule 558 at stage m; at stage 2m+1 it is its complement -/
theorem r469_parity (m : Nat) :
    caState 469 (2 * m) = caState 558 m ∧
    caState 469 (2 * m + 1) = fun p => !caState 558 m p := by
  induction m with
  | zero =>
    have h0 : caState 469 (2 * 0) = caState 558 0 := rfl
    refine ⟨h0, ?_⟩
    show step 469 (caState 469 (2 * 0)) = _
    rw [h0]
    funext p
    exact step469_on 0 p
  | succ m ih =>
    have e : caState 469 (2 * (m + 1)) = caState 558 (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
      show step 469 (caState 469 (2 * m + 1)) = step 558 (caState 558 m)
      rw [ih.2]
      funext p
      exact step469_off m p
    refine ⟨e, ?_⟩
    show step 469 (caState 469 (2 * (m + 1))) = _
    rw [e]
    funext p
    exact step469_on (m + 1) p

theorem step337_on (m : Nat) (p : Cell) : step 337 (caState 558 m) p = !step 558 (caState 558 m) p := by
  have hk := nbrOn_le4 (caState 558 m) p
  exact (VN.LDR.r337_on (caState 558 m p) ⟨nbrOn (caState 558 m) p, by omega⟩).resolve_left (r558_no_idx7 m p)

theorem step337_off (m : Nat) (p : Cell) : step 337 (fun q => !caState 558 m q) p = caState 558 m p := by
  have hk := nbrOn_le4 (caState 558 m) p
  show ruleOut 337 (!caState 558 m p) (nbrOn (fun q => !caState 558 m q) p) = caState 558 m p
  rw [nbrOn_not]
  exact (VN.LDR.r337_off (caState 558 m p) ⟨nbrOn (caState 558 m) p, by omega⟩).resolve_left (r558_no_idx7 m p)

/-- Rule 337 at stage 2m is Rule 558 at stage m; at stage 2m+1 it is the complement of Rule 558 at stage m+1 -/
theorem r337_parity (m : Nat) :
    caState 337 (2 * m) = caState 558 m ∧
    caState 337 (2 * m + 1) = fun p => !caState 558 (m + 1) p := by
  induction m with
  | zero =>
    have h0 : caState 337 (2 * 0) = caState 558 0 := rfl
    refine ⟨h0, ?_⟩
    show step 337 (caState 337 (2 * 0)) = fun p => !step 558 (caState 558 0) p
    rw [h0]
    funext p
    exact step337_on 0 p
  | succ m ih =>
    have e : caState 337 (2 * (m + 1)) = caState 558 (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
      show step 337 (caState 337 (2 * m + 1)) = caState 558 (m + 1)
      rw [ih.2]
      funext p
      exact step337_off (m + 1) p
    refine ⟨e, ?_⟩
    show step 337 (caState 337 (2 * (m + 1))) = fun p => !step 558 (caState 558 (m + 1)) p
    rw [e]
    funext p
    exact step337_on (m + 1) p

end LT2D

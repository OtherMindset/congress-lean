/-
  Leader file LDR_C (core Lean only, no Mathlib, no imports): finite bit tables of the rule numbers 337, 469, 558, 895
  used by LDR_M (Rules 337 and 469 from the posted Rule 558 proof). Index i = c + 2k, new state = Nat.testBit R i.
  Two checks are single bits (u895_bit7, r558_bit0); the four tables run over c in Bool and k in 0..4 (Fin 5). All by kernel evaluation.
-/
namespace VN.LDR

/-- the used-index mask of the posted W3A558 certificate, 895, has bit 7 (c = 1, k = 3) clear -/
theorem u895_bit7 : Nat.testBit 895 (true.toNat + 2 * 3) = false := by decide +kernel

/-- Rule 558 keeps an OFF cell with no ON neighbour OFF (bit 0 of 558 is 0) -/
theorem r558_bit0 : Nat.testBit 558 (false.toNat + 2 * 0) = false := by decide +kernel

/-- Rule 469 on a state: new = not c, except at index 7 -/
theorem r469_on : ∀ c : Bool, ∀ k : Fin 5, (c = true ∧ k.val = 3) ∨
    Nat.testBit 469 (c.toNat + 2 * k.val) = !c := by decide +kernel

/-- Rule 469 on the complemented state: same as Rule 558 on the state, except at index 7 -/
theorem r469_off : ∀ c : Bool, ∀ k : Fin 5, (c = true ∧ k.val = 3) ∨
    Nat.testBit 469 ((!c).toNat + 2 * (4 - k.val)) = Nat.testBit 558 (c.toNat + 2 * k.val) := by decide +kernel

/-- Rule 337 on a state: the complement of Rule 558, except at index 7 -/
theorem r337_on : ∀ c : Bool, ∀ k : Fin 5, (c = true ∧ k.val = 3) ∨
    Nat.testBit 337 (c.toNat + 2 * k.val) = !Nat.testBit 558 (c.toNat + 2 * k.val) := by decide +kernel

/-- Rule 337 on the complemented state: new = c (the state comes back), except at index 7 -/
theorem r337_off : ∀ c : Bool, ∀ k : Fin 5, (c = true ∧ k.val = 3) ∨
    Nat.testBit 337 ((!c).toNat + 2 * (4 - k.val)) = c := by decide +kernel

end VN.LDR

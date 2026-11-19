import LongTable.P_mwmowkxn_5swdpn
import LongTable.P_mwmq4rm3_0e92a0
import LongTable.P_mwmqefff_czcc3e
import LongTable.NT_C
/-
  Group NT1, Mathlib file: equal-count statements between two rules of the OEIS entries' comparisons.
  Closed forms: LT2D.vn_count (library VN_M2) for the new instances NT_R641 and NT_R261 (file NT_C); the closed forms of
  Rules 1, 275, 657 (VBG1_M) and 221 (VBG2_M) are posted theorems. n = 0 and n = 1 by decide +kernel.
-/
namespace LT2D

/-- A270935 (Rule 221): %F Conjecture: a(n) = 4*4^n - 4*2^n - 4 = A269907(n), n>1. - Lars Blomberg, Jun 06 2016
(read id r-mwnv6he7-l1qohx). A269907 is the same count for Rule 1 (its %N, read id r-mwnv6hii-1a1snf). Here: for every n >= 2 the number of ON cells at stage 2^n - 1 is the same
for Rule 221 and Rule 1. (At n = 1 they differ: 8 and 4; at n = 0 both are 1.) -/
theorem a270935_eq_a269907 (n : Nat) (hn : 2 ≤ n) :
    onCount 221 (2 ^ n - 1) = onCount 1 (2 ^ n - 1) := by
  have h1 := a270935_formula n hn
  have h2 := a269907_formula n (by omega)
  have : (onCount 221 (2 ^ n - 1) : Int) = onCount 1 (2 ^ n - 1) := by linarith
  exact_mod_cast this

/-- Rule 641 (A273310): the closed form 4*4^n - 4*2^n - 8 for n >= 2; this is A273310's %F "Conjecture: a(n) = 4*4^n -
4*2^n - 8, n>1. - Lars Blomberg, Jul 17 2016" (read id r-mwnv6l6b-kxn3b1), used for the comparison with
A271092 (Rule 275). -/
theorem a273310_r641_formula (n : Nat) (hn : 2 ≤ n) :
    (onCount 641 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n - 8 := by
  have h := vn_count VN.NT_R641.tab 641 759 1 4 (-4) (-8) 2 2 VN.NT_R641.ok2 VN.NT_R641.ok1 VN.NT_R641.okr n (by omega)
  first | linarith | (ring_nf at h ⊢; linarith)

/-- A273310 (Rule 641): %C Seems to differ from A271092 only at n=1. - R. J. Mathar, Mar 27 2025
(read id r-mwnv6l6b-kxn3b1). A271092 is Rule 275 (its %N, read id r-mwnv9cz2-b0xoce). Here: the number of ON cells at stage 2^n - 1 is the same for Rule 641 and Rule 275
exactly when n is not 1 (n = 0: 1 and 1; n = 1: 4 and 5, by kernel evaluation; n >= 2 from the two closed forms). -/
theorem a273310_eq_a271092_iff (n : Nat) :
    onCount 641 (2 ^ n - 1) = onCount 275 (2 ^ n - 1) ↔ n ≠ 1 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · exact ⟨fun _ => by omega, fun _ => by decide +kernel⟩
  · exact ⟨fun h => absurd h (by decide +kernel), fun h => absurd rfl h⟩
  · refine ⟨fun _ => by omega, fun _ => ?_⟩
    have h1 := a273310_r641_formula n hn
    have h2 := a271092_formula n hn
    have : (onCount 641 (2 ^ n - 1) : Int) = onCount 275 (2 ^ n - 1) := by linarith
    exact_mod_cast this

/-- Rule 261 (A271061): %F Conjecture: a(n) = 4*4^n - 4*2^n, n>0. - Lars Blomberg, Jun 09 2016 (read id r-mwnv6hpx-vfbetp; n >= 1). -/
theorem a271061_r261_formula (n : Nat) (hn : 1 ≤ n) :
    (onCount 261 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 4 * 2 ^ n := by
  have h := vn_count VN.NT_R261.tab 261 903 1 4 (-4) (0) 1 1 VN.NT_R261.ok2 VN.NT_R261.ok1 VN.NT_R261.okr n (by omega)
  first | linarith | (ring_nf at h ⊢; linarith)

/-- A273335 (Rule 657): %C Seems to differ from A271061 only at n=1. - R. J. Mathar, Mar 27 2025
(read id r-mwnvb88x-vshesi). A271061 is Rule 261 (its %N, read id r-mwnv6hpx-vfbetp). Here: the number of ON cells at stage 2^n - 1 is the same for Rule 657 and Rule 261
exactly when n is not 1 (n = 0: 1 and 1; n = 1: 4 and 8, by kernel evaluation; n >= 2 from the two closed forms). -/
theorem a273335_eq_a271061_iff (n : Nat) :
    onCount 657 (2 ^ n - 1) = onCount 261 (2 ^ n - 1) ↔ n ≠ 1 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · exact ⟨fun _ => by omega, fun _ => by decide +kernel⟩
  · exact ⟨fun h => absurd h (by decide +kernel), fun h => absurd rfl h⟩
  · refine ⟨fun _ => by omega, fun _ => ?_⟩
    have h1 := a273335_formula n hn
    have h2 := a271061_r261_formula n (by omega)
    have e4 : (4 : Int) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    have e2 : (2 : Int) ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; ring
    have : (onCount 657 (2 ^ n - 1) : Int) = onCount 261 (2 ^ n - 1) := by
      rw [h1, h2, e2, e4]; ring
    exact_mod_cast this

end LT2D

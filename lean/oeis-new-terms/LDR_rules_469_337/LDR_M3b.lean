import LongTable.LDR_M2
import LongTable.LDR_T3
import LongTable.P_mwnvekt3_6yexo1
/-
  Leader file LDR_M3b: Rule 337 (A271286's own rule) from LDR_M's parity theorem and the 4-tip lemma LT2D.r558_tips
  (LDR_T3), and the comment's Rule 505 from the posted a271286_r505_formula (#mwnvekt3-6yexo1).
-/
namespace LT2D

/-- Rule 337 at stage 2m+1: count plus Rule 558's count at stage m+1 fills the square -/
theorem r337_count_odd (m : Nat) :
    onCount 337 (2 * m + 1) + onCount 558 (m + 1) = (2 * (2 * m + 1) + 1) ^ 2 :=
  count_compl558 337 (m + 1) (2 * m + 1) (by omega) (r337_parity m).2

/-- A271286 (main rule 337, its %N), read r-mwnv6huj-bhnjnz: Colin Barker's conjecture (May 04 2016)
"a(n) = (11*4^n)/3-8/3-2^(2+n) for n>0." Stated times 3, range n >= 1 as printed. -/
theorem a271286_r337_formula (n : Nat) (hn : 1 ≤ n) :
    3 * (onCount 337 (2 ^ n - 1) : Int) = 11 * 4 ^ n - 8 - 3 * 2 ^ (2 + n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = j + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hg : 2 ^ (k + 1) - 1 = 2 * j + 1 := by rw [pow_succ]; omega
  have hm := r337_count_odd j
  have ht := r558_tips k
  rw [hj, show j + 1 - 1 = j by omega] at ht
  have h558 := r558_count k
  rw [show 2 ^ k - 1 = j by omega] at h558
  have h2 : (2 : Int) ^ k = j + 1 := by exact_mod_cast hj
  have h4 : (4 : Int) ^ k = ((j : Int) + 1) ^ 2 := by
    rw [show (4 : Int) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul, h2]
  rw [hg]
  have hmI : (onCount 337 (2 * j + 1) : Int) + onCount 558 (j + 1) = (2 * (2 * (j : Int) + 1) + 1) ^ 2 := by
    exact_mod_cast hm
  have htI : (onCount 558 (j + 1) : Int) = onCount 558 j + 4 := by exact_mod_cast ht
  rw [show (2 : Int) ^ (2 + (k + 1)) = 8 * 2 ^ k by ring, show (4 : Int) ^ (k + 1) = 4 * 4 ^ k by ring, h2, h4]
  rw [h4] at h558
  ring_nf at hmI h558 htI ⊢
  linarith

/-- A271286, %C "It is conjectured that Rule 505 also produces this sequence.  It would be nice to have a proof."
(read r-mwnv6huj-bhnjnz): Rules 505 and 337 have the same count at every stage 2^n - 1, every n >= 0. -/
theorem a271286_r505_count_eq_337 (n : Nat) : onCount 505 (2 ^ n - 1) = onCount 337 (2 ^ n - 1) := by
  cases n with
  | zero => rfl
  | succ k =>
    have h1 := a271286_r337_formula (k + 1) (by omega)
    have h2 := a271286_r505_formula (k + 1) (by omega)
    have : (onCount 505 (2 ^ (k + 1) - 1) : Int) = onCount 337 (2 ^ (k + 1) - 1) := by linarith
    exact_mod_cast this

end LT2D

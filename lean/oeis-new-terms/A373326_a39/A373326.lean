-- toolchain: leanprover/lean4:v4.35.0
-- mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679
-- ITEM A373326. a(39) = 768, from the definition of the OEIS entry and its first 38 terms.
-- OEIS A373326: a(1) = 1, a(2) = 2. For n > 2, let i = a(n-2), j = a(n-1). Then a(n) is the least
-- novel k such that A007947(i*j*k) is the smallest possible primorial number, subject to no more than
-- two consecutive terms having the same number of distinct prime divisors.
-- Here i = a(37) = 1024 and j = a(38) = 648. The theorem `a39` says: 768 is admissible (positive,
-- not among a(1..38), and the omega rule holds) with rad(i*j*768) = 6, a primorial; every admissible
-- k has rad(i*j*k) >= 6, so 6 is the smallest primorial possible; and no admissible k < 768 has
-- rad(i*j*k) = 6. Together: a(39) = 768.
-- Built locally on Lean 4.34.1 with Mathlib d13f23b7 (no warnings; axioms propext, Classical.choice,
-- Quot.sound; about 20 s); the runner builds it on the toolchain above.
import Mathlib

namespace A373326

/-- A007947: the radical of n, the product of its distinct prime divisors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- A001221: the number of distinct prime divisors of n. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- A primorial number: the product of the primes up to some n (Mathlib's `primorial`). -/
def IsPrimorial (m : ℕ) : Prop := ∃ n, primorial n = m

/-- a(1), ..., a(38), as the OEIS entry lists them. -/
def prior : List ℕ :=
  [1, 2, 3, 6, 4, 8, 12, 9, 16, 18, 24, 27, 32, 36, 48, 64, 54, 72, 81, 96, 108, 128, 144, 162,
   243, 192, 216, 256, 288, 324, 512, 384, 432, 729, 486, 576, 1024, 648]

/-- k may be a(39): positive, novel, and not a third consecutive term with the omega of a(37), a(38). -/
def Admissible (k : ℕ) : Prop :=
  0 < k ∧ k ∉ prior ∧ ¬ (omega 1024 = omega 648 ∧ omega 648 = omega k)

theorem prior_length : prior.length = 38 := by decide

theorem prior_last_two : prior[36]? = some 1024 ∧ prior[37]? = some 648 := by decide

theorem pf_1024_648 : (1024 * 648).primeFactors = {2, 3} := by
  have h : (1024 * 648 : ℕ) = 2 ^ 13 * 3 ^ 4 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
  rfl

theorem omega_1024 : omega 1024 = 1 := by
  have h : (1024 : ℕ) = 2 ^ 10 := by norm_num
  rw [omega, h, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  rfl

theorem omega_648 : omega 648 = 2 := by
  have h : (648 : ℕ) = 2 ^ 3 * 3 ^ 4 := by norm_num
  rw [omega, h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
  rfl

theorem pf_mul (k : ℕ) (hk : 0 < k) :
    (1024 * 648 * k).primeFactors = {2, 3} ∪ k.primeFactors := by
  rw [Nat.primeFactors_mul (by norm_num) hk.ne', pf_1024_648]

theorem rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _p hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- Every admissible k (indeed every k > 0) has rad(1024*648*k) >= 6. -/
theorem six_le_rad (k : ℕ) (hk : 0 < k) : 6 ≤ rad (1024 * 648 * k) := by
  have hsub : ({2, 3} : Finset ℕ) ⊆ (1024 * 648 * k).primeFactors := by
    rw [pf_mul k hk]; exact Finset.subset_union_left
  have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub
  rw [Finset.prod_pair (by norm_num)] at hdvd
  exact Nat.le_of_dvd (rad_pos _) hdvd

/-- If rad(1024*648*k) = 6 then every prime divisor of k is 2 or 3. -/
theorem smooth_of_rad (k : ℕ) (hk : 0 < k) (h : rad (1024 * 648 * k) = 6) :
    k.primeFactors ⊆ {2, 3} := by
  intro p hp
  have hp' : p ∈ (1024 * 648 * k).primeFactors := by
    rw [pf_mul k hk]; exact Finset.mem_union_right _ hp
  have hd : p ∣ 6 := h ▸ Finset.dvd_prod_of_mem (fun q => q) hp'
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> simp_all (config := { decide := true })

/-- A k > 0 whose prime divisors are among 2 and 3 is 2^a * 3^b. -/
theorem eq_pow_mul_pow (k : ℕ) (hk : 0 < k) (hs : k.primeFactors ⊆ {2, 3}) :
    2 ^ k.factorization 2 * 3 ^ k.factorization 3 = k := by
  have h := Nat.prod_factorization_pow_eq_self hk.ne'
  rw [Finsupp.prod_of_support_subset _ (s := {2, 3}) (by rw [Nat.support_factorization]; exact hs)
    _ (by simp), Finset.prod_pair (by norm_num)] at h
  exact h

/-- The 3-smooth numbers below 768 are all among a(1..38). -/
theorem smooth_below : ∀ a < 10, ∀ b < 7, 2 ^ a * 3 ^ b < 768 → 2 ^ a * 3 ^ b ∈ prior := by
  decide

theorem a39 :
    (Admissible 768 ∧ rad (1024 * 648 * 768) = 6 ∧ IsPrimorial 6) ∧
    (∀ k, Admissible k → 6 ≤ rad (1024 * 648 * k)) ∧
    (∀ k, Admissible k → k < 768 → rad (1024 * 648 * k) ≠ 6) := by
  refine ⟨⟨⟨by norm_num, by decide, ?_⟩, ?_, ⟨3, by decide⟩⟩, ?_, ?_⟩
  · rw [omega_1024, omega_648]; omega
  · have h768 : (768 : ℕ).primeFactors = {2, 3} := by
      have h : (768 : ℕ) = 2 ^ 8 * 3 ^ 1 := by norm_num
      rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      rfl
    rw [rad, pf_mul 768 (by norm_num), h768, Finset.union_self, Finset.prod_pair (by norm_num)]
    norm_num
  · intro k hk; exact six_le_rad k hk.1
  · intro k hk hlt h
    have hs := smooth_of_rad k hk.1 h
    have he := eq_pow_mul_pow k hk.1 hs
    have ha : k.factorization 2 < 10 := by
      by_contra hc
      have h1 : 2 ^ 10 ≤ 2 ^ k.factorization 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ k.factorization 2 ≤ k := by
        have := Nat.le_mul_of_pos_right (2 ^ k.factorization 2) (pow_pos (by norm_num : 0 < 3) (k.factorization 3))
        rw [he] at this; exact this
      omega
    have hb : k.factorization 3 < 7 := by
      by_contra hc
      have h1 : 3 ^ 7 ≤ 3 ^ k.factorization 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 3 ^ k.factorization 3 ≤ k := by
        have := Nat.le_mul_of_pos_left (3 ^ k.factorization 3) (pow_pos (by norm_num : 0 < 2) (k.factorization 2))
        rw [he] at this; exact this
      omega
    have hmem := smooth_below _ ha _ hb (by rw [he]; exact hlt)
    rw [he] at hmem
    exact hk.2.1 hmem

end A373326

/- OEIS A281816, new term a(72) = 673.
A281816: a(n) = least k >= 1 such that phi(k) is the sum of two totient numbers (A002202) in exactly n ways,
or 0 if no such k exists
(unordered, positive summands; PARI c(x) = sum(j=1, x\2, istotient(j) && istotient(x-j))); OFFSET 0,2.
PROVED (kernel-checked, no sorry, no native_decide): theorem A281816.a72 :
  PairCount (phi 673) = 72  and  for all k with 1 <= k < 673, PairCount (phi k) <> 72,
where IsTotient x := exists m, phi m = x and PairCount x := #{j in [1, x/2] : IsTotient j and IsTotient (x-j)}.
So a(72) = 673 (such a k exists, so the "or 0" clause does not apply). IsTotient 0 holds (phi 0 = 0)
but is never used: 1 <= j <= x/2 gives x - j >= j >= 1, and x - j has no truncation.
NOT shown: any other term; nothing about a(n) for n <> 72.
Method: T := the bitmask with bit phi(w) set for each w in an explicit witness list W
 (204 totient values <= 671, plus 0 = phi 0; computed in the file, no encoded constant).
 (1) W.map phiC = the bits of T below 672, in order (decide +kernel), where
     phiC is a List-based copy of Nat.totient, proved equal to it by rfl (phiC_eq);
 (2) phi m <= 671 -> phi m in T, by induction over prime powers / coprime products
     (Nat.recOnPosPrimePosCoprime): T is closed under products <= 671 except 22*22 = 484, and
     phi a = 22 forces 23 | a, so 484 never arises from coprime a, b; prime-power factors
     p^k(p-1) <= 671 are checked by trial division (p <= 672 < 26^2);
 (3) PairCount then equals a bitmask count, evaluated by decide +kernel for x = 672 and all x < 672;
 (4) phi 673 = 672 (673 prime); phi k <= 671 for 1 <= k <= 672.
`set_option synthInstance.maxSize` only enlarges instance search for the Decidable instances.
Local build (2 CPUs): VERIFIED; axioms propext, Classical.choice, Quot.sound.
Lean 4.35.0 + Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
Credit: Claude congress (Claude Opus 5.5 Leader; Claude Sonnet 5.5 Chair B). -/
import Mathlib

open scoped Nat

namespace A281816

noncomputable def IsTotient (x : ℕ) : Prop := ∃ m : ℕ, Nat.totient m = x

open Classical in
noncomputable def PairCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 (x / 2)).filter (fun j => IsTotient j ∧ IsTotient (x - j))).card

/-- W[i] is a witness for the i-th set bit of T -/
def W : List ℕ := [
  0,1,3,5,7,15,11,13,17,19,25,23,35,29,31,51,37,41,43,69,
  47,65,53,81,87,59,61,85,67,71,73,79,123,83,129,89,141,97,101,103,
  159,107,109,121,113,177,143,127,255,131,161,137,139,213,185,149,151,157,187,163,
  249,167,203,173,267,179,181,235,191,193,197,199,275,309,265,211,321,247,253,223,
  339,227,229,233,239,241,251,301,257,393,263,299,269,271,289,277,281,283,323,293,
  343,447,341,307,311,313,317,425,489,415,331,501,337,361,519,347,349,353,537,359,
  403,367,705,373,379,573,383,485,389,591,397,401,409,795,419,421,535,431,433,439,
  575,443,669,449,681,457,461,463,699,467,553,717,479,527,487,491,581,499,625,503,
  551,529,509,771,521,523,789,623,807,541,685,547,611,557,725,563,849,569,571,577,
  649,879,587,1029,593,599,601,607,613,617,619,933,689,631,951,749,641,643,647,703,
  653,1245,659,661,835]

/-- a list-based copy of `Nat.totient`, definitionally equal to it, fast for the kernel -/
def phiC (m : ℕ) : ℕ := ((List.range m).filter (fun a => Nat.gcd m a == 1)).length

/-- the bitmask of the values phi(w), w in W; hW below shows these are exactly its bits below 672 -/
def T : ℕ := (W.map phiC).foldl (fun a y => a ||| (1 <<< y)) 0

theorem phiC_eq (m : ℕ) : Nat.totient m = phiC m := by
  unfold phiC Nat.totient
  rfl

theorem hW : W.map phiC = (List.range 672).filter (fun y => T.testBit y) := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hM : ∀ x < 672, T.testBit x = true → ∀ y < 671 / x + 1, T.testBit y = true →
    (T.testBit (x * y) = true ∨ x = 22 ∧ y = 22) ∧ (x * y = 22 → x = 22 ∨ y = 22) := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hP : ∀ p < 673, ∀ k < 10, p ^ k * (p - 1) ≤ 671 → (∀ d < 26, 1 < d → d < p → p % d ≠ 0) →
    T.testBit (p ^ k * (p - 1)) = true ∧ (p ^ k * (p - 1) = 22 → p = 23) := by
  decide +kernel

theorem pp (p k : ℕ) (hp : p.Prime) (h : p ^ k * (p - 1) ≤ 671) :
    T.testBit (p ^ k * (p - 1)) = true ∧ (p ^ k * (p - 1) = 22 → p = 23) := by
  have h2 := hp.two_le
  have h1 : p ^ k ≤ p ^ k * (p - 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : p - 1 ≤ p ^ k * (p - 1) := Nat.le_mul_of_pos_left _ (pow_pos (by omega) k)
  refine hP p (by omega) k ?_ h fun d _ hd hdp hm => ?_
  · by_contra hk
    have := (Nat.pow_le_pow_right (by norm_num : 2 > 0) (not_lt.1 hk)).trans (Nat.pow_le_pow_left h2 k)
    norm_num at this
    omega
  · have := hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hm)
    omega

theorem neg (m : ℕ) : φ m ≤ 671 → T.testBit (φ m) = true ∧ (φ m = 22 → 23 ∣ m) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    rw [Nat.totient_prime_pow hp hn]
    intro h
    obtain ⟨h1, h2⟩ := pp p (n - 1) hp h
    exact ⟨h1, fun e => by rw [h2 e]; exact dvd_pow_self 23 hn.ne'⟩
  | zero => decide +kernel
  | one => decide +kernel
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab]
    intro h
    have ha' : 0 < φ a := Nat.totient_pos.2 (by omega)
    have hb' : 0 < φ b := Nat.totient_pos.2 (by omega)
    have la : φ a ≤ 671 := le_trans (Nat.le_mul_of_pos_right _ hb') h
    have lb : φ b ≤ 671 := le_trans (Nat.le_mul_of_pos_left _ ha') h
    obtain ⟨ta, ea⟩ := iha la
    obtain ⟨tb, eb⟩ := ihb lb
    have hy : φ b < 671 / φ a + 1 :=
      Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le ha').2 (by rw [Nat.mul_comm]; exact h))
    obtain ⟨h1, h2⟩ := hM _ (by omega) ta _ hy tb
    refine ⟨h1.resolve_right fun e => ?_, fun e => ?_⟩
    · have := Nat.eq_one_of_dvd_coprimes hab (ea e.1) (eb e.2)
      omega
    · rcases h2 e with e | e
      · exact Dvd.dvd.mul_right (ea e) b
      · exact Dvd.dvd.mul_left (eb e) a

theorem tot_iff (y : ℕ) (hy : y < 672) : IsTotient y ↔ T.testBit y = true := by
  refine ⟨fun ⟨m, hm⟩ => by subst hm; exact (neg m (by omega)).1, fun h => ?_⟩
  have : y ∈ W.map phiC := by rw [hW]; simp [hy, h]
  obtain ⟨m, -, hm⟩ := List.mem_map.1 this
  exact ⟨m, (phiC_eq m).trans hm⟩

open Classical in
theorem pc_eq (x : ℕ) (hx : x ≤ 672) : PairCount x =
    ((Finset.Icc 1 (x / 2)).filter (fun j => T.testBit j = true ∧ T.testBit (x - j) = true)).card := by
  unfold PairCount
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [tot_iff j (by omega), tot_iff (x - j) (by omega)]

theorem c672 :
    ((Finset.Icc 1 (672 / 2)).filter (fun j => T.testBit j = true ∧ T.testBit (672 - j) = true)).card
      = 72 := by
  decide +kernel

theorem cle : ∀ x < 672,
    ((Finset.Icc 1 (x / 2)).filter (fun j => T.testBit j = true ∧ T.testBit (x - j) = true)).card
      ≠ 72 := by
  decide +kernel

theorem a72 : PairCount (Nat.totient 673) = 72 ∧
    ∀ k, 1 ≤ k → k < 673 → PairCount (Nat.totient k) ≠ 72 := by
  have h673 : φ 673 = 672 := Nat.totient_prime (by norm_num)
  refine ⟨by rw [h673, pc_eq 672 le_rfl]; exact c672, fun k hk1 hk2 => ?_⟩
  have hk : φ k < 672 := by
    rcases Nat.lt_or_ge 1 k with h | h
    · exact lt_of_lt_of_le (Nat.totient_lt k h) (by omega)
    · rw [show k = 1 by omega]; simp
  rw [pc_eq _ hk.le]
  exact cle _ hk

end A281816
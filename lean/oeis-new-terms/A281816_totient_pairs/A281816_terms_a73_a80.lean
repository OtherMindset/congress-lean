/- OEIS A281816: new terms a(73)=779, a(74)=701, a(75)=865, a(77)=773, a(78)=799,
a(79)=761, a(80)=829.
A281816: a(n) = least k >= 1 such that phi(k) is the sum of two totient numbers (A002202) in exactly n ways,
or 0 if no such k exists
(unordered, positive summands; PARI c(x) = sum(j=1, x\2, istotient(j) && istotient(x-j))); OFFSET 0,2.
PROVED (kernel-checked, no sorry, no native_decide): theorem A281816.terms, the conjunction over
(n, c) in {(73,779), (74,701), (75,865), (77,773), (78,799), (79,761), (80,829)} of
  PairCount (phi c) = n  and  for all k with 1 <= k < c, PairCount (phi k) <> n,
where IsTotient x := exists m, phi m = x and PairCount x := #{j in [1, x/2] : IsTotient j and IsTotient (x-j)}.
So a(n) = c for these seven n (such a k exists, so the "or 0" clause does not apply). IsTotient 0 holds
(phi 0 = 0) but is never used: 1 <= j <= x/2 gives x - j >= j >= 1, and x - j has no truncation.
NOT shown: a(76) (claimed 1257) or any other term.
Method (as in our a(72) file): V lists the 257 totient values <= 864 (plus 0 = phi 0); T is its bitmask,
computed from V (no encoded literal).
 (1) W.map phiC = the bits of T below 865, in order (decide +kernel), so each is phi of a witness, where
     phiC is a List-based copy of Nat.totient, proved equal to it by rfl (phiC_eq);
 (2) phi m <= 864 -> phi m in T, by induction over prime powers / coprime products
     (Nat.recOnPosPrimePosCoprime): T is closed under products <= 864 except 22*22 = 484, and
     phi a = 22 forces 23 | a, so 484 never arises from coprime a, b; prime-power factors
     p^k(p-1) <= 864 are checked by trial division (p <= 865 < 30^2);
 (3) PairCount x equals a bitmask count cnt x for x <= 865; the kernel evaluates cnt (phiC c) = n and
     cnt (phiC k) <> n for every 1 <= k < c (a full phi table below each c; split into five k-ranges
     hK1..hK5 only to bound kernel memory).
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
  653,1245,659,661,835,673,677,683,1083,865,691,1041,767,701,1059,709,895,1077,719,779,
  727,733,799,739,743,1119,751,757,761,1149,769,773,1167,869,985,787,851,797,1025,809,
  811,841,959,821,823,827,829,901,1257,839,899,1605,853,857,859,1293,863,949]

/-- a list-based copy of `Nat.totient`, definitionally equal to it, fast for the kernel -/
def phiC (m : ℕ) : ℕ := ((List.range m).filter (fun a => Nat.gcd m a == 1)).length

theorem phiC_eq (m : ℕ) : Nat.totient m = phiC m := by
  unfold phiC Nat.totient
  rfl

/-- the values φ(W[i]): all totient values ≤ 864, plus 0 = φ 0 -/
def V : List ℕ := [
  0,1,2,4,6,8,10,12,16,18,20,22,24,28,30,32,36,40,42,44,
  46,48,52,54,56,58,60,64,66,70,72,78,80,82,84,88,92,96,100,102,
  104,106,108,110,112,116,120,126,128,130,132,136,138,140,144,148,150,156,160,162,
  164,166,168,172,176,178,180,184,190,192,196,198,200,204,208,210,212,216,220,222,
  224,226,228,232,238,240,250,252,256,260,262,264,268,270,272,276,280,282,288,292,
  294,296,300,306,310,312,316,320,324,328,330,332,336,342,344,346,348,352,356,358,
  360,366,368,372,378,380,382,384,388,392,396,400,408,416,418,420,424,430,432,438,
  440,442,444,448,452,456,460,462,464,466,468,476,478,480,486,490,492,498,500,502,
  504,506,508,512,520,522,524,528,536,540,544,546,552,556,560,562,564,568,570,576,
  580,584,586,588,592,598,600,606,612,616,618,620,624,630,632,636,640,642,646,648,
  652,656,658,660,664,672,676,682,684,688,690,692,696,700,704,708,712,716,718,720,
  726,732,736,738,742,744,750,756,760,764,768,772,776,780,784,786,792,796,800,808,
  810,812,816,820,822,826,828,832,836,838,840,848,852,856,858,860,862,864]

/-- bit y of T is set iff y ∈ V -/
def T : ℕ := V.foldl (fun a y => a ||| 1 <<< y) 0

theorem hW : W.map phiC = (List.range 865).filter (fun y => T.testBit y) := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hM : ∀ x < 865, T.testBit x = true → ∀ y < 864 / x + 1, T.testBit y = true →
    (T.testBit (x * y) = true ∨ x = 22 ∧ y = 22) ∧ (x * y = 22 → x = 22 ∨ y = 22) := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hP : ∀ p < 866, ∀ k < 10, p ^ k * (p - 1) ≤ 864 → (∀ d < 30, 1 < d → d < p → p % d ≠ 0) →
    T.testBit (p ^ k * (p - 1)) = true ∧ (p ^ k * (p - 1) = 22 → p = 23) := by
  decide +kernel

theorem pp (p k : ℕ) (hp : p.Prime) (h : p ^ k * (p - 1) ≤ 864) :
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

theorem neg (m : ℕ) : φ m ≤ 864 → T.testBit (φ m) = true ∧ (φ m = 22 → 23 ∣ m) := by
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
    have la : φ a ≤ 864 := le_trans (Nat.le_mul_of_pos_right _ hb') h
    have lb : φ b ≤ 864 := le_trans (Nat.le_mul_of_pos_left _ ha') h
    obtain ⟨ta, ea⟩ := iha la
    obtain ⟨tb, eb⟩ := ihb lb
    have hy : φ b < 864 / φ a + 1 :=
      Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le ha').2 (by rw [Nat.mul_comm]; exact h))
    obtain ⟨h1, h2⟩ := hM _ (by omega) ta _ hy tb
    refine ⟨h1.resolve_right fun e => ?_, fun e => ?_⟩
    · have := Nat.eq_one_of_dvd_coprimes hab (ea e.1) (eb e.2)
      omega
    · rcases h2 e with e | e
      · exact Dvd.dvd.mul_right (ea e) b
      · exact Dvd.dvd.mul_left (eb e) a

theorem tot_iff (y : ℕ) (hy : y < 865) : IsTotient y ↔ T.testBit y = true := by
  refine ⟨fun ⟨m, hm⟩ => by subst hm; exact (neg m (by omega)).1, fun h => ?_⟩
  have : y ∈ W.map phiC := by rw [hW]; simp [hy, h]
  obtain ⟨m, -, hm⟩ := List.mem_map.1 this
  exact ⟨m, (phiC_eq m).trans hm⟩

/-- the bitmask pair count -/
def cnt (x : ℕ) : ℕ :=
  ((Finset.Icc 1 (x / 2)).filter (fun j => T.testBit j = true ∧ T.testBit (x - j) = true)).card

open Classical in
theorem pc_eq (x : ℕ) (hx : x ≤ 865) : PairCount x = cnt x := by
  unfold PairCount cnt
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [tot_iff j (by omega), tot_iff (x - j) (by omega)]

/-- the seven (n, a(n)) pairs -/
def L : List (ℕ × ℕ) := [(73, 779), (74, 701), (75, 865), (77, 773), (78, 799), (79, 761), (80, 829)]

theorem hL : ∀ p ∈ L, cnt (phiC p.2) = p.1 ∧ p.2 ≤ 865 := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hK1 : ∀ k, 1 ≤ k → k < 387 → ∀ p ∈ L, k < p.2 → cnt (phiC k) ≠ p.1 := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hK2 : ∀ k, 387 ≤ k → k < 547 → ∀ p ∈ L, k < p.2 → cnt (phiC k) ≠ p.1 := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hK3 : ∀ k, 547 ≤ k → k < 670 → ∀ p ∈ L, k < p.2 → cnt (phiC k) ≠ p.1 := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hK4 : ∀ k, 670 ≤ k → k < 774 → ∀ p ∈ L, k < p.2 → cnt (phiC k) ≠ p.1 := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
theorem hK5 : ∀ k, 774 ≤ k → k < 865 → ∀ p ∈ L, k < p.2 → cnt (phiC k) ≠ p.1 := by
  decide +kernel

theorem hK (k : ℕ) (h1 : 1 ≤ k) (h2 : k < 865) : ∀ p ∈ L, k < p.2 → cnt (phiC k) ≠ p.1 := by
  rcases Nat.lt_or_ge k 387 with a | a
  · exact hK1 k h1 a
  rcases Nat.lt_or_ge k 547 with b | b
  · exact hK2 k a b
  rcases Nat.lt_or_ge k 670 with c | c
  · exact hK3 k b c
  rcases Nat.lt_or_ge k 774 with d | d
  · exact hK4 k c d
  exact hK5 k d h2

theorem term (p : ℕ × ℕ) (hp : p ∈ L) : PairCount (Nat.totient p.2) = p.1 ∧
    ∀ k, 1 ≤ k → k < p.2 → PairCount (Nat.totient k) ≠ p.1 := by
  obtain ⟨h1, h2⟩ := hL p hp
  refine ⟨by rw [pc_eq _ ((Nat.totient_le _).trans h2), phiC_eq]; exact h1, fun k hk1 hk2 => ?_⟩
  rw [pc_eq _ ((Nat.totient_le k).trans (by omega)), phiC_eq]
  exact hK k hk1 (by omega) p hp hk2

theorem terms :
    (PairCount (Nat.totient 779) = 73 ∧ ∀ k, 1 ≤ k → k < 779 → PairCount (Nat.totient k) ≠ 73) ∧
    (PairCount (Nat.totient 701) = 74 ∧ ∀ k, 1 ≤ k → k < 701 → PairCount (Nat.totient k) ≠ 74) ∧
    (PairCount (Nat.totient 865) = 75 ∧ ∀ k, 1 ≤ k → k < 865 → PairCount (Nat.totient k) ≠ 75) ∧
    (PairCount (Nat.totient 773) = 77 ∧ ∀ k, 1 ≤ k → k < 773 → PairCount (Nat.totient k) ≠ 77) ∧
    (PairCount (Nat.totient 799) = 78 ∧ ∀ k, 1 ≤ k → k < 799 → PairCount (Nat.totient k) ≠ 78) ∧
    (PairCount (Nat.totient 761) = 79 ∧ ∀ k, 1 ≤ k → k < 761 → PairCount (Nat.totient k) ≠ 79) ∧
    (PairCount (Nat.totient 829) = 80 ∧ ∀ k, 1 ≤ k → k < 829 → PairCount (Nat.totient k) ≠ 80) :=
  ⟨term (73, 779) (by decide), term (74, 701) (by decide), term (75, 865) (by decide),
    term (77, 773) (by decide),
    term (78, 799) (by decide), term (79, 761) (by decide), term (80, 829) (by decide)⟩

end A281816
/- OEIS A281816: new term a(76) = 1257.
A281816: a(n) = least k >= 1 such that phi(k) is the sum of two totient numbers (A002202) in exactly n ways,
or 0 if no such k exists
(unordered, positive summands; PARI c(x) = sum(j=1, x\2, istotient(j) && istotient(x-j))); OFFSET 0,2.
PROVED (kernel-checked, no sorry, no native_decide): theorem A281816.a76 :
  PairCount (phi 1257) = 76  and  for all k with 1 <= k < 1257, PairCount (phi k) <> 76,
where IsTotient x := exists m, phi m = x and PairCount x := #{j in [1, x/2] : IsTotient j and IsTotient (x-j)}.
So a(76) = 1257 (such a k exists, so the "or 0" clause does not apply). IsTotient 0 holds
(phi 0 = 0) but is never used: 1 <= j <= x/2 gives x - j >= j >= 1, and x - j has no truncation.
NOT shown: any other term.
Method (as in our a(72) and a(73..80) files): V lists the 354 totient values <= 1256 (plus 0 = phi 0);
T is its bitmask, computed from V.
 (1) W.map phiC = the bits of T below 1257, in order (decide +kernel, two halves), so each is phi of a
     witness, where
     phiC is a List-based copy of Nat.totient, equal to it by rfl (phiC_eq);
 (2) phi m <= 1256 -> phi m in T and Q (phi m) | m, by induction over prime powers / coprime products
     (Nat.recOnPosPrimePosCoprime), with Q 22 = Q 44 = 23, Q 10 = Q 110 = 11, else Q = 1. T is closed
     under products <= 1256 except 484 = 22*22, 968 = 22*44, 1100 = 10*110, which need Q a = Q b <> 1,
     impossible for coprime a, b; prime-power factors p^k(p-1) <= 1256 by trial division (p <= 1257 < 36^2);
 (3) PairCount x = bitmask count cnt x for x <= 1257; the kernel checks cnt (phiC 1257) = 76 and
     cnt (phiC k) <> 76 for all k < 1257 (a full phi table, in 10 ranges to bound kernel memory).
`set_option synthInstance.maxSize` (file-wide) only enlarges instance search for the Decidable instances.
Local build (2 CPUs): VERIFIED; axioms propext, Classical.choice, Quot.sound.
Lean 4.35.0 + Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
Credit: Claude congress (Claude Opus 5.5 Leader; Claude Sonnet 5.5 Chair B). -/
import Mathlib

open scoped Nat

set_option synthInstance.maxSize 100000

namespace A281816

noncomputable def IsTotient (x : ℕ) : Prop := ∃ m : ℕ, Nat.totient m = x

open Classical in
noncomputable def PairCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 (x / 2)).filter (fun j => IsTotient j ∧ IsTotient (x - j))).card

/-- all totient values ≤ 1256, plus 0 = φ 0 -/
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
  810,812,816,820,822,826,828,832,836,838,840,848,852,856,858,860,862,864,876,880,
  882,884,886,888,896,900,904,906,910,912,918,920,924,928,930,932,936,940,946,952,
  956,960,966,970,972,976,980,982,984,990,996,1000,1004,1008,1012,1016,1018,1020,1024,1030,
  1032,1038,1040,1044,1048,1050,1056,1060,1062,1068,1072,1080,1086,1088,1090,1092,1096,1102,1104,1108,
  1112,1116,1120,1122,1124,1128,1136,1140,1144,1150,1152,1160,1162,1168,1170,1172,1176,1180,1184,1186,
  1188,1192,1196,1200,1210,1212,1216,1222,1224,1228,1230,1232,1236,1240,1248]

/-- W[i] is a witness for V[i] -/
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
  811,841,959,821,823,827,829,901,1257,839,899,1605,853,857,859,1293,863,949,877,881,
  883,1329,887,1043,1347,1057,1135,907,911,1145,919,1175,989,929,961,1401,937,941,947,953,
  1437,1037,967,971,1141,977,1473,983,1079,991,997,1111,1509,1009,1013,1527,1019,1021,1285,1031,
  1033,1039,1325,1121,1049,1051,1139,1061,1063,1069,1345,1147,1087,1445,1091,1093,1097,1103,1385,1109,
  1671,1117,1189,1123,1689,1129,1707,1337,1219,1151,1153,1475,1163,1465,1171,1761,1247,1181,1779,1187,
  1273,1193,1797,1201,1331,1213,1217,1223,1339,1229,1231,1851,1237,1555,1249]

def T : ℕ := V.foldl (fun a y => a ||| 1 <<< y) 0

def phiC (m : ℕ) : ℕ := ((List.range m).filter (fun a => Nat.gcd m a == 1)).length

theorem phiC_eq (m : ℕ) : Nat.totient m = phiC m := by
  unfold phiC Nat.totient
  rfl

theorem hW1 : (W.take 256).map phiC = ((List.range 1257).filter (fun y => T.testBit y)).take 256 := by
  decide +kernel

theorem hW2 : (W.drop 256).map phiC = ((List.range 1257).filter (fun y => T.testBit y)).drop 256 := by
  decide +kernel

theorem hW : W.map phiC = (List.range 1257).filter (fun y => T.testBit y) := by
  rw [← List.take_append_drop 256 W, List.map_append, hW1, hW2, List.take_append_drop]

def Q (v : ℕ) : ℕ := if v = 22 ∨ v = 44 then 23 else if v = 10 ∨ v = 110 then 11 else 1

theorem hM : ∀ x < 1257, T.testBit x = true → ∀ y < 1256 / x + 1, T.testBit y = true →
    (T.testBit (x * y) = true ∨ Q x = Q y ∧ Q x ≠ 1) ∧
      (Q (x * y) = Q x ∨ Q (x * y) = Q y ∨ Q (x * y) = 1) := by
  decide +kernel

theorem hP : ∀ p < 1258, ∀ k < 11, p ^ k * (p - 1) ≤ 1256 → (∀ d < 36, 1 < d → d < p → p % d ≠ 0) →
    T.testBit (p ^ k * (p - 1)) = true ∧ (Q (p ^ k * (p - 1)) = p ∨ Q (p ^ k * (p - 1)) = 1) := by
  decide +kernel

theorem pp (p k : ℕ) (hp : p.Prime) (h : p ^ k * (p - 1) ≤ 1256) :
    T.testBit (p ^ k * (p - 1)) = true ∧ (Q (p ^ k * (p - 1)) = p ∨ Q (p ^ k * (p - 1)) = 1) := by
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

theorem neg (m : ℕ) : φ m ≤ 1256 → T.testBit (φ m) = true ∧ Q (φ m) ∣ m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    rw [Nat.totient_prime_pow hp hn]
    intro h
    obtain ⟨h1, h2⟩ := pp p (n - 1) hp h
    refine ⟨h1, ?_⟩
    rcases h2 with e | e <;> rw [e]
    · exact dvd_pow_self p hn.ne'
    · exact one_dvd _
  | zero => decide +kernel
  | one => decide +kernel
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab]
    intro h
    have ha' : 0 < φ a := Nat.totient_pos.2 (by omega)
    have hb' : 0 < φ b := Nat.totient_pos.2 (by omega)
    have la : φ a ≤ 1256 := le_trans (Nat.le_mul_of_pos_right _ hb') h
    have lb : φ b ≤ 1256 := le_trans (Nat.le_mul_of_pos_left _ ha') h
    obtain ⟨ta, ea⟩ := iha la
    obtain ⟨tb, eb⟩ := ihb lb
    have hy : φ b < 1256 / φ a + 1 :=
      Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le ha').2 (by rw [Nat.mul_comm]; exact h))
    obtain ⟨h1, h2⟩ := hM _ (by omega) ta _ hy tb
    refine ⟨h1.resolve_right fun e => e.2 (Nat.eq_one_of_dvd_coprimes hab ea (by rw [e.1]; exact eb)), ?_⟩
    rcases h2 with e | e | e <;> rw [e]
    · exact Dvd.dvd.mul_right ea b
    · exact Dvd.dvd.mul_left eb a
    · exact one_dvd _

theorem tot_iff (y : ℕ) (hy : y < 1257) : IsTotient y ↔ T.testBit y = true := by
  refine ⟨fun ⟨m, hm⟩ => by subst hm; exact (neg m (by omega)).1, fun h => ?_⟩
  have : y ∈ W.map phiC := by rw [hW]; simp [hy, h]
  obtain ⟨m, -, hm⟩ := List.mem_map.1 this
  exact ⟨m, (phiC_eq m).trans hm⟩

/-- the bitmask pair count -/
def cnt (x : ℕ) : ℕ :=
  ((Finset.Icc 1 (x / 2)).filter (fun j => T.testBit j = true ∧ T.testBit (x - j) = true)).card

open Classical in
theorem pc_eq (x : ℕ) (hx : x ≤ 1257) : PairCount x = cnt x := by
  unfold PairCount cnt
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [tot_iff j (by omega), tot_iff (x - j) (by omega)]

theorem K0 : ∀ k < 396, cnt (phiC k) ≠ 76 := by decide +kernel
theorem K1 : ∀ k, 396 ≤ k → k < 561 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K2 : ∀ k, 561 ≤ k → k < 687 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K3 : ∀ k, 687 ≤ k → k < 794 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K4 : ∀ k, 794 ≤ k → k < 888 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K5 : ∀ k, 888 ≤ k → k < 973 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K6 : ∀ k, 973 ≤ k → k < 1052 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K7 : ∀ k, 1052 ≤ k → k < 1124 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K8 : ∀ k, 1124 ≤ k → k < 1193 → cnt (phiC k) ≠ 76 := by decide +kernel
theorem K9 : ∀ k, 1193 ≤ k → k < 1257 → cnt (phiC k) ≠ 76 := by decide +kernel

theorem K (k : ℕ) (h : k < 1257) : cnt (phiC k) ≠ 76 :=
  if a : k < 396 then K0 k a else if b : k < 561 then K1 k (by omega) b else
  if c : k < 687 then K2 k (by omega) c else if d : k < 794 then K3 k (by omega) d else
  if e : k < 888 then K4 k (by omega) e else if f : k < 973 then K5 k (by omega) f else
  if g : k < 1052 then K6 k (by omega) g else if i : k < 1124 then K7 k (by omega) i else
  if j : k < 1193 then K8 k (by omega) j else K9 k (by omega) h

theorem a76 : PairCount (Nat.totient 1257) = 76 ∧
    ∀ k, 1 ≤ k → k < 1257 → PairCount (Nat.totient k) ≠ 76 := by
  refine ⟨?_, fun k _ hk => ?_⟩
  · rw [pc_eq _ (Nat.totient_le 1257), phiC_eq]
    decide +kernel
  · rw [pc_eq _ ((Nat.totient_le k).trans hk.le), phiC_eq]
    exact K k hk

end A281816
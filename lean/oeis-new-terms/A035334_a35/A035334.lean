-- toolchain: leanprover/lean4:v4.35.0
-- ITEM A035334. Core Lean only (no Mathlib), no native_decide.
-- Same prior, IsSum and Claim as #mwkqlf9i. The two big checks use
-- `decide +kernel` on bitsets split by the three largest terms (no
-- numeral over about 47.5 million bits; shifts, never 2^n with large n).
-- Built locally on Lean 4.35.0 (commit eb6cafb7): about 8 s, 4.6 GB peak.
namespace A035334

def L : Nat := 41160719
def prior : List Nat :=
  [1,2,5,3,14,4,39,6,119,7,352,8,706,9,2104,10,4209,11,
   8419,12,24552,13,49106,15,188594,16,524494,17,1933822,18,
   5605163,19,15069555,20]

def IsSum : Nat → Nat → Prop
  | 0, n => n = 0
  | k+1, n => ∃ c ∈ prior, c ≤ n ∧ IsSum k (n-c)

def Claim : Prop :=
  (∀ x, 0 < x → x < L → x ∈ prior ∨ IsSum 20 x) ∧
  L ∉ prior ∧ ¬ IsSum 20 L

/-! A 20-term sum = some copies of the three large terms 1933822, 5605163,
15069555 plus a sum of terms ≤ 524494 ("low"). -/

def low : List Nat := prior.filter (· ≤ 524494)

def LowSum : Nat → Nat → Prop
  | 0, n => n = 0
  | k+1, n => ∃ c ∈ low, c ≤ n ∧ LowSum k (n-c)

def orShifts (coins : List Nat) (bits : Nat) : Nat :=
  coins.foldr (fun c acc => (bits <<< c) ||| acc) 0

def lowReach : Nat → Nat
  | 0 => 1
  | k+1 => orShifts low (lowReach k)

def highSum (a b c : Nat) : Nat := 1933822*a + 5605163*b + 15069555*c

/-- (number of large terms, their sum), for every choice with sum ≤ L. -/
def uppers : List (Nat × Nat) :=
  (List.range 21).flatMap fun a => (List.range (21-a)).flatMap fun b =>
    ((List.range (21-a-b)).map fun c => (a+b+c, highSum a b c)).filter
      fun p => p.2 ≤ L

def full : Nat :=
  uppers.foldr (fun p acc => (lowReach (20 - p.1) <<< p.2) ||| acc) 0

/-! Bitset lemmas. -/

theorem orShifts_testBit (coins : List Nat) (bits n : Nat) :
    (orShifts coins bits).testBit n = true ↔
      ∃ c ∈ coins, c ≤ n ∧ bits.testBit (n-c) = true := by
  induction coins with
  | nil => simp [orShifts]
  | cons c cs ih =>
      show ((bits <<< c) ||| orShifts cs bits).testBit n = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_shiftLeft]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons,
        exists_eq_or_imp, ge_iff_le]

theorem lowReach_testBit (k n : Nat) :
    (lowReach k).testBit n = true ↔ LowSum k n := by
  induction k generalizing n with
  | zero =>
      show (1 : Nat).testBit n = true ↔ n = 0
      exact Nat.testBit_one_eq_true_iff_self_eq_zero
  | succ k ih =>
      show (orShifts low (lowReach k)).testBit n = true ↔
        ∃ c ∈ low, c ≤ n ∧ LowSum k (n-c)
      rw [orShifts_testBit]
      simp only [ih]

theorem foldShift_testBit (ps : List (Nat × Nat)) (n : Nat) :
    (ps.foldr (fun p acc => (lowReach (20 - p.1) <<< p.2) ||| acc) 0).testBit n
        = true ↔
      ∃ p ∈ ps, p.2 ≤ n ∧ (lowReach (20 - p.1)).testBit (n - p.2) = true := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, ih,
        Nat.testBit_shiftLeft]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons,
        exists_eq_or_imp, ge_iff_le]

theorem full_testBit (n : Nat) :
    full.testBit n = true ↔
      ∃ p ∈ uppers, p.2 ≤ n ∧ LowSum (20 - p.1) (n - p.2) := by
  unfold full
  rw [foldShift_testBit]
  simp only [lowReach_testBit]

theorem mem_uppers {p : Nat × Nat} (h : p ∈ uppers) :
    ∃ a b c, a + b + c ≤ 20 ∧ p = (a+b+c, highSum a b c) := by
  simp only [uppers, List.mem_flatMap, List.mem_filter, List.mem_map,
    List.mem_range] at h
  obtain ⟨a, ha, b, hb, ⟨c, hc, rfl⟩, -⟩ := h
  exact ⟨a, b, c, by omega, rfl⟩

theorem mem_uppers_of (a b c : Nat) (h : a + b + c ≤ 20)
    (hs : highSum a b c ≤ L) : (a+b+c, highSum a b c) ∈ uppers := by
  simp only [uppers, List.mem_flatMap, List.mem_filter, List.mem_map,
    List.mem_range, decide_eq_true_eq]
  exact ⟨a, by omega, b, by omega, ⟨c, by omega, rfl⟩, hs⟩

/-! Sums. -/

theorem isSum_add : ∀ (k j u v : Nat), IsSum k u → IsSum j v →
    IsSum (k + j) (u + v)
  | 0, j, u, v, hu, hv => by
      have hu' : u = 0 := hu
      subst hu'
      simpa using hv
  | k+1, j, u, v, hu, hv => by
      obtain ⟨c, hc, hcu, hk⟩ := hu
      have ih := isSum_add k j (u - c) v hk hv
      rw [show k + 1 + j = (k + j) + 1 by omega]
      show ∃ d ∈ prior, d ≤ u + v ∧ IsSum (k + j) (u + v - d)
      exact ⟨c, hc, by omega, by rwa [show u + v - c = u - c + v by omega]⟩

theorem isSum_rep (c : Nat) (hc : c ∈ prior) : ∀ a, IsSum a (c * a)
  | 0 => show c * 0 = 0 from Nat.mul_zero c
  | a+1 => by
      show ∃ d ∈ prior, d ≤ c * (a+1) ∧ IsSum a (c * (a+1) - d)
      refine ⟨c, hc, ?_, ?_⟩
      · rw [Nat.mul_succ]; exact Nat.le_add_left c (c * a)
      · rw [Nat.mul_succ, Nat.add_sub_cancel]; exact isSum_rep c hc a

theorem isSum_high (a b c : Nat) : IsSum (a+b+c) (highSum a b c) :=
  isSum_add _ _ _ _
    (isSum_add _ _ _ _ (isSum_rep 1933822 (by decide) a)
      (isSum_rep 5605163 (by decide) b))
    (isSum_rep 15069555 (by decide) c)

theorem mem_low {c : Nat} (h : c ∈ low) : c ∈ prior := by
  simp only [low, List.mem_filter] at h
  exact h.1

theorem isSum_of_lowSum : ∀ k n, LowSum k n → IsSum k n
  | 0, _, h => h
  | k+1, n, h => by
      obtain ⟨c, hc, hcn, h⟩ := h
      exact ⟨c, mem_low hc, hcn, isSum_of_lowSum k (n-c) h⟩

theorem prior_split : ∀ c ∈ prior,
    c ∈ low ∨ c = 1933822 ∨ c = 5605163 ∨ c = 15069555 := by
  decide

theorem lowSum_add_one {m y c : Nat} (h : LowSum m y) (hc : c ∈ low) :
    LowSum (m+1) (y + c) := by
  show ∃ d ∈ low, d ≤ y + c ∧ LowSum m (y + c - d)
  exact ⟨c, hc, Nat.le_add_left c y, by rwa [Nat.add_sub_cancel]⟩

theorem high_a (a b c : Nat) : highSum (a+1) b c = highSum a b c + 1933822 := by
  unfold highSum; rw [Nat.mul_succ]; omega
theorem high_b (a b c : Nat) : highSum a (b+1) c = highSum a b c + 5605163 := by
  unfold highSum; rw [Nat.mul_succ]; omega
theorem high_c (a b c : Nat) : highSum a b (c+1) = highSum a b c + 15069555 := by
  unfold highSum; rw [Nat.mul_succ]; omega

/-- Every sum of k prior terms splits into large terms and low terms. -/
theorem split : ∀ k x, IsSum k x → ∃ a b c, a + b + c ≤ k ∧
    highSum a b c ≤ x ∧ LowSum (k - (a+b+c)) (x - highSum a b c)
  | 0, x, h => by
      have hx : x = 0 := h
      subst hx
      exact ⟨0, 0, 0, Nat.le_refl 0, Nat.le_refl 0, rfl⟩
  | k+1, x, h => by
      obtain ⟨d, hd, hdx, hk⟩ := h
      obtain ⟨a, b, c, habc, hs, hl⟩ := split k (x - d) hk
      rcases prior_split d hd with hlow | rfl | rfl | rfl
      · refine ⟨a, b, c, by omega, by omega, ?_⟩
        rw [show k + 1 - (a+b+c) = (k - (a+b+c)) + 1 by omega,
          show x - highSum a b c = (x - d - highSum a b c) + d by omega]
        exact lowSum_add_one hl hlow
      · refine ⟨a+1, b, c, by omega, by rw [high_a]; omega, ?_⟩
        rw [show k + 1 - (a+1+b+c) = k - (a+b+c) by omega, high_a,
          show x - (highSum a b c + 1933822) = x - 1933822 - highSum a b c by omega]
        exact hl
      · refine ⟨a, b+1, c, by omega, by rw [high_b]; omega, ?_⟩
        rw [show k + 1 - (a+(b+1)+c) = k - (a+b+c) by omega, high_b,
          show x - (highSum a b c + 5605163) = x - 5605163 - highSum a b c by omega]
        exact hl
      · refine ⟨a, b, c+1, by omega, by rw [high_c]; omega, ?_⟩
        rw [show k + 1 - (a+b+(c+1)) = k - (a+b+c) by omega, high_c,
          show x - (highSum a b c + 15069555) = x - 15069555 - highSum a b c by omega]
        exact hl

theorem isSum_of_full {x : Nat} (h : full.testBit x = true) : IsSum 20 x := by
  obtain ⟨p, hp, hpx, hl⟩ := (full_testBit x).mp h
  obtain ⟨a, b, c, habc, rfl⟩ := mem_uppers hp
  have := isSum_add _ _ _ _ (isSum_high a b c) (isSum_of_lowSum _ _ hl)
  rwa [show a+b+c + (20 - (a+b+c)) = 20 by omega,
    show highSum a b c + (x - highSum a b c) = x by omega] at this

theorem full_of_isSum {x : Nat} (hx : x ≤ L) (h : IsSum 20 x) :
    full.testBit x = true := by
  obtain ⟨a, b, c, habc, hs, hl⟩ := split 20 x h
  exact (full_testBit x).mpr
    ⟨_, mem_uppers_of a b c habc (Nat.le_trans hs hx), hs, hl⟩

/-! The two kernel computations (no native code). -/

theorem cover_bits :
    (full >>> 20) % (1 <<< (L-20)) = (1 <<< (L-20)) - 1 := by decide +kernel

theorem candidate_bit : full.testBit L = false := by decide +kernel

theorem cover_bit {x : Nat} (hx : 20 ≤ x) (hlt : x < L) :
    full.testBit x = true := by
  have h := congrArg (fun z => z.testBit (x - 20)) cover_bits
  simp only [Nat.one_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight] at h
  have hy : x - 20 < L - 20 := by omega
  rw [show 20 + (x - 20) = x by omega] at h
  simpa [hy] using h

theorem small_prior : ∀ x, x < 20 → 0 < x → x ∈ prior := by decide +kernel

theorem a35_claim : Claim := by
  refine ⟨fun x hx hlt => ?_, by decide, fun h => ?_⟩
  · by_cases hs : x < 20
    · exact Or.inl (small_prior x hs hx)
    · exact Or.inr (isSum_of_full (cover_bit (by omega) hlt))
  · have h1 := full_of_isSum (Nat.le_refl L) h
    rw [candidate_bit] at h1
    exact Bool.false_ne_true h1

#print axioms a35_claim

end A035334
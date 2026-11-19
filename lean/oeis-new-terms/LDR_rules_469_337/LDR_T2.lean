import LongTable.LDR_M
import LongTable.LDR_T1
/-
  Leader file LDR_T2 (Mathlib through the library imports only): lemmas on the posted W3A558 table for the "4 tips" lemma
  onCount 558 (2^k) = onCount 558 (2^k - 1) + 4, which LDR_T3 proves (LT2D.r558_tips), from LDR_T1's kernel checks.
  Interior (V558_interior): on [0, 2^k)^2 the table gives the same value at times 2^k + 1 and 2^k (pair check, k >= 1).
  Edge (V558_edgeX/Y): at time 2^k (stage 2^k - 1) the cells (2^k - 1, b) and (b, 2^k - 1), b < 2^k, are ON exactly at b = 0.
-/
namespace LT2D
open VN

theorem bisim_run (A : Tab) (S : List (Nat × Nat)) (h : LDR.bisimOK A S = true) :
    ∀ L p q x y, (p, q) ∈ S → (run A L p x y 0, run A L q x y 0) ∈ S := by
  intro L
  induction L with
  | zero => intro p q x y hpq; exact hpq
  | succ L ih =>
    intro p q x y hpq
    have hd : dg x y 0 < 4 := by unfold dg; omega
    have hS := List.all_eq_true.mp h (p, q) hpq
    rw [Bool.and_eq_true] at hS
    have hm : (tr A p (dg x y 0), tr A q (dg x y 0)) ∈ S :=
      of_decide_eq_true (List.all_eq_true.mp hS.2 (dg x y 0)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega))
    show (run A L (tr A p (dg x y 0)) (x / 2) (y / 2) 0, run A L (tr A q (dg x y 0)) (x / 2) (y / 2) 0) ∈ S
    exact ih _ _ (x / 2) (y / 2) hm

/-- interior: times 2^(n+1) + 1 and 2^(n+1) agree on [0, 2^(n+1))^2 -/
theorem V558_interior (n x y : Nat) (hx : x < 2 ^ (n + 1)) (hy : y < 2 ^ (n + 1)) :
    V W3A558.tab x y (2 ^ (n + 1) + 1) = V W3A558.tab x y (2 ^ (n + 1)) := by
  have hp1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  have hp2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [V_pow W3A558.tab (n + 1) x y hx hy,
    ← out_run_eq_V W3A558.tab (n + 1 + 1) x y (2 ^ (n + 1) + 1) (by omega) (by omega) (by omega),
    run_succ_top]
  have h1 : (2 ^ (n + 1) + 1) / 2 ^ (n + 1) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, h1]
  have e1 : run W3A558.tab (n + 1) 0 x y (2 ^ (n + 1) + 1) =
      run W3A558.tab n (tr W3A558.tab 0 (4 + dg x y 0)) (x / 2) (y / 2) 0 := by
    show prun (tr W3A558.tab) n (tr W3A558.tab 0 (dg x y (2 ^ (n + 1) + 1))) (x / 2) (y / 2)
      ((2 ^ (n + 1) + 1) / 2) = _
    have h2 : (2 ^ (n + 1) + 1) / 2 = 2 ^ n := by omega
    have h3 : dg x y (2 ^ (n + 1) + 1) = 4 + dg x y 0 := by unfold dg; omega
    rw [h2, h3, prun_t_pow]
  have e0 : run W3A558.tab (n + 1) 0 x y 0 = run W3A558.tab n (tr W3A558.tab 0 (dg x y 0)) (x / 2) (y / 2) 0 := rfl
  rw [e1, e0]
  have hd : dg x y 0 < 4 := by unfold dg; omega
  have hst : (tr W3A558.tab 0 (4 + dg x y 0), tr W3A558.tab 0 (dg x y 0)) ∈ LDR.S558 :=
    of_decide_eq_true (List.all_eq_true.mp LDR.start558 (dg x y 0)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega))
  have hm := bisim_run W3A558.tab LDR.S558 LDR.bisim558 n _ _ (x / 2) (y / 2) hst
  have hb := List.all_eq_true.mp LDR.bisim558 _ hm
  rw [Bool.and_eq_true] at hb
  exact beq_iff_eq.mp hb.1

theorem edgeX_run (S : List (Nat × Bool)) (h : LDR.edgeOK W3A558.tab 1 S = true) :
    ∀ L q f b, (q, f) ∈ S → b < 2 ^ L → (run W3A558.tab L q (2 ^ L - 1) b 0, f || decide (b ≠ 0)) ∈ S := by
  intro L
  induction L with
  | zero =>
    intro q f b hq hb
    have : b = 0 := by simp at hb; omega
    subst this
    show (q, f || decide (0 ≠ 0)) ∈ S
    simpa using hq
  | succ L ih =>
    intro q f b hq hb
    have hp : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ L := Nat.two_pow_pos L
    have hS := List.all_eq_true.mp h (q, f) hq
    simp only [Bool.and_eq_true] at hS
    obtain ⟨⟨_, h1⟩, h3⟩ := hS
    have hx2 : (2 ^ (L + 1) - 1) / 2 = 2 ^ L - 1 := by omega
    show (run W3A558.tab L (tr W3A558.tab q (dg (2 ^ (L + 1) - 1) b 0)) ((2 ^ (L + 1) - 1) / 2) (b / 2) (0 / 2),
      f || decide (b ≠ 0)) ∈ S
    rw [hx2, Nat.zero_div]
    rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · have hdg : dg (2 ^ (L + 1) - 1) b 0 = 1 := by unfold dg; omega
      rw [hdg]
      have := ih _ f (b / 2) (of_decide_eq_true h1) (by omega)
      have hf : decide (b / 2 ≠ 0) = decide (b ≠ 0) := by
        rw [decide_eq_decide]; constructor <;> intro <;> omega
      rwa [hf] at this
    · have hdg : dg (2 ^ (L + 1) - 1) b 0 = 3 := by unfold dg; omega
      rw [hdg]
      have := ih _ true (b / 2) (of_decide_eq_true h3) (by omega)
      have hf : (f || decide (b ≠ 0)) = true := by
        have : b ≠ 0 := by omega
        simp [this]
      rw [hf]
      simpa using this

theorem edgeY_run (S : List (Nat × Bool)) (h : LDR.edgeOK W3A558.tab 2 S = true) :
    ∀ L q f b, (q, f) ∈ S → b < 2 ^ L → (run W3A558.tab L q b (2 ^ L - 1) 0, f || decide (b ≠ 0)) ∈ S := by
  intro L
  induction L with
  | zero =>
    intro q f b hq hb
    have : b = 0 := by simp at hb; omega
    subst this
    show (q, f || decide (0 ≠ 0)) ∈ S
    simpa using hq
  | succ L ih =>
    intro q f b hq hb
    have hp : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ L := Nat.two_pow_pos L
    have hS := List.all_eq_true.mp h (q, f) hq
    simp only [Bool.and_eq_true] at hS
    obtain ⟨⟨_, h1⟩, h3⟩ := hS
    have hx2 : (2 ^ (L + 1) - 1) / 2 = 2 ^ L - 1 := by omega
    show (run W3A558.tab L (tr W3A558.tab q (dg b (2 ^ (L + 1) - 1) 0)) (b / 2) ((2 ^ (L + 1) - 1) / 2) (0 / 2),
      f || decide (b ≠ 0)) ∈ S
    rw [hx2, Nat.zero_div]
    rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · have hdg : dg b (2 ^ (L + 1) - 1) 0 = 2 := by unfold dg; omega
      rw [hdg]
      have := ih _ f (b / 2) (of_decide_eq_true h1) (by omega)
      have hf : decide (b / 2 ≠ 0) = decide (b ≠ 0) := by
        rw [decide_eq_decide]; constructor <;> intro <;> omega
      rwa [hf] at this
    · have hdg : dg b (2 ^ (L + 1) - 1) 0 = 3 := by unfold dg; omega
      rw [hdg]
      have := ih _ true (b / 2) (of_decide_eq_true h3) (by omega)
      have hf : (f || decide (b ≠ 0)) = true := by
        have : b ≠ 0 := by omega
        simp [this]
      rw [hf]
      simpa using this

/-- the edge x = 2^k - 1 at time 2^k: ON exactly at y = 0 -/
theorem V558_edgeX (k b : Nat) (hb : b < 2 ^ k) : V W3A558.tab (2 ^ k - 1) b (2 ^ k) = decide (b = 0) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [V_pow W3A558.tab k _ b (by omega) hb]
  have hm := edgeX_run LDR.EX558 LDR.edgeX558 k 0 false b (of_decide_eq_true LDR.edge0X) hb
  have hS := List.all_eq_true.mp LDR.edgeX558 _ hm
  simp only [Bool.and_eq_true] at hS
  rw [beq_iff_eq.mp hS.1.1]
  by_cases h0 : b = 0 <;> simp [h0]

theorem V558_edgeY (k b : Nat) (hb : b < 2 ^ k) : V W3A558.tab b (2 ^ k - 1) (2 ^ k) = decide (b = 0) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [V_pow W3A558.tab k b _ hb (by omega)]
  have hm := edgeY_run LDR.EY558 LDR.edgeY558 k 0 false b (of_decide_eq_true LDR.edge0Y) hb
  have hS := List.all_eq_true.mp LDR.edgeY558 _ hm
  simp only [Bool.and_eq_true] at hS
  rw [beq_iff_eq.mp hS.1.1]
  by_cases h0 : b = 0 <;> simp [h0]

end LT2D

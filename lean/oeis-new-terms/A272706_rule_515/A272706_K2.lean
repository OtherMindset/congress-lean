-- A272706 / Rule 515, file K2 (core Lean only; copy of A273331 K2a #mwlxycrx-omyz08 without the F4/F5 lanes): lanes = one automaton run fed with a number
-- computed on the fly (carry or borrow bit). Each lane is a step function on (state, bit).
-- Lemma numbering follows the congress plan (leader/a273331/sketch.md); every proof below is complete.
import LongTable.P_mwmflun2_e55jk4
namespace A272706

/-- the x, y, z digits of a digit triple d = 4*z + 2*y + x -/
def dx (d : Nat) : Nat := d % 2
def dy (d : Nat) : Nat := d / 2 % 2
def dz (d : Nat) : Nat := d / 4 % 2
def tri (x y z : Nat) : Nat := 4 * z + 2 * y + x

/-- digit of a + b + c (it is also the digit of a - b - c) -/
def sD (a b c : Nat) : Nat := (a + b + c) % 2
/-- carry of a + b + c -/
def aC (a b c : Nat) : Nat := (a + b + c) / 2
/-- borrow of a - b - c -/
def sB (a b c : Nat) : Nat := if a < b + c then 1 else 0

/-! ### F1 lanes, reading (x, y, t) -/
/-- reads (x, y, t + c) -/
def lT (p : Nat × Nat) (d : Nat) : Nat × Nat :=
  (tr p.1 (tri (dx d) (dy d) (sD (dz d) 0 p.2)), aC (dz d) 0 p.2)
/-- reads (x + c, y, t) -/
def lE (p : Nat × Nat) (d : Nat) : Nat × Nat :=
  (tr p.1 (tri (sD (dx d) 0 p.2) (dy d) (dz d)), aC (dx d) 0 p.2)
/-- reads (x - c, y, t) -/
def lW (p : Nat × Nat) (d : Nat) : Nat × Nat :=
  (tr p.1 (tri (sD (dx d) 0 p.2) (dy d) (dz d)), sB (dx d) 0 p.2)
/-- reads (x, y + c, t) -/
def lN (p : Nat × Nat) (d : Nat) : Nat × Nat :=
  (tr p.1 (tri (dx d) (sD (dy d) 0 p.2) (dz d)), aC (dy d) 0 p.2)
/-- reads (x, y - c, t) -/
def lS (p : Nat × Nat) (d : Nat) : Nat × Nat :=
  (tr p.1 (tri (dx d) (sD (dy d) 0 p.2) (dz d)), sB (dy d) 0 p.2)

/-! ### lane semantics (D1-D16) -/

theorem dg_parts (x y z : Nat) :
    dx (dg x y z) = x % 2 ∧ dy (dg x y z) = y % 2 ∧ dz (dg x y z) = z % 2 := by
  unfold dx dy dz dg
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem dx_dg_aux (x y z : Nat) : dx (dg x y z) = x % 2 := by
  unfold dx dg; omega

theorem dy_dg_aux (x y z : Nat) : dy (dg x y z) = y % 2 := by
  unfold dy dg; omega

theorem dz_dg_aux (x y z : Nat) : dz (dg x y z) = z % 2 := by
  unfold dz dg; omega

theorem lT_step_aux (q c x y t : Nat) :
    lT (q, c) (dg x y t) = (tr q (dg x y (t + c)), (t % 2 + c) / 2) := by
  have h1 : tri (dx (dg x y t)) (dy (dg x y t)) (sD (dz (dg x y t)) 0 c)
      = dg x y (t + c) := by
    rw [dx_dg_aux, dy_dg_aux, dz_dg_aux]
    unfold tri sD dg
    omega
  have h2 : aC (dz (dg x y t)) 0 c = (t % 2 + c) / 2 := by
    rw [dz_dg_aux]
    unfold aC
    omega
  unfold lT
  rw [h1, h2]

theorem lT_run_aux (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 →
    (prun lT L (q, c) x y t).1 = run L q x y (t + c) ∧
    t / 2 ^ L + (prun lT L (q, c) x y t).2 = (t + c) / 2 ^ L := by
  induction L with
  | zero =>
    intro q c x y t _
    simp [prun, run]
  | succ L ih =>
    intro q c x y t hc
    have hc' : (t % 2 + c) / 2 ≤ 1 := by omega
    obtain ⟨ih1, ih2⟩ := ih (tr q (dg x y (t + c))) ((t % 2 + c) / 2) (x / 2) (y / 2) (t / 2) hc'
    have ht : t / 2 + (t % 2 + c) / 2 = (t + c) / 2 := by omega
    have e1 : t / 2 ^ (L + 1) = t / 2 / 2 ^ L := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]
    have e2' : (t + c) / 2 ^ (L + 1) = (t + c) / 2 / 2 ^ L := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]
    have e2 : (t + c) / 2 ^ (L + 1) = (t / 2 + (t % 2 + c) / 2) / 2 ^ L := by
      rw [ht]; exact e2'
    simp only [prun, run]
    rw [lT_step_aux]
    constructor
    · rw [ih1, ht]
    · rw [e1, e2]
      exact ih2

theorem lT_run (L q c x y t : Nat) (hc : c ≤ 1) :
    (prun lT L (q, c) x y t).1 = run L q x y (t + c) ∧
    t / 2 ^ L + (prun lT L (q, c) x y t).2 = (t + c) / 2 ^ L := by
  exact lT_run_aux L q c x y t hc

theorem lE_step_aux (q c x y t : Nat) :
    lE (q, c) (dg x y t) = (tr q (dg (x + c) y t), (x % 2 + c) / 2) := by
  have h1 : tri (sD (dx (dg x y t)) 0 c) (dy (dg x y t)) (dz (dg x y t))
      = dg (x + c) y t := by
    rw [dx_dg_aux, dy_dg_aux, dz_dg_aux]
    unfold tri sD dg
    omega
  have h2 : aC (dx (dg x y t)) 0 c = (x % 2 + c) / 2 := by
    rw [dx_dg_aux]
    unfold aC
    omega
  unfold lE
  rw [h1, h2]

theorem lE_run_aux (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 →
    (prun lE L (q, c) x y t).1 = run L q (x + c) y t ∧
    x / 2 ^ L + (prun lE L (q, c) x y t).2 = (x + c) / 2 ^ L := by
  induction L with
  | zero =>
    intro q c x y t _
    simp [prun, run]
  | succ L ih =>
    intro q c x y t hc
    have hc' : (x % 2 + c) / 2 ≤ 1 := by omega
    obtain ⟨ih1, ih2⟩ := ih (tr q (dg (x + c) y t)) ((x % 2 + c) / 2) (x / 2) (y / 2) (t / 2) hc'
    have hx : x / 2 + (x % 2 + c) / 2 = (x + c) / 2 := by omega
    have e1 : x / 2 ^ (L + 1) = x / 2 / 2 ^ L := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]
    have e2' : (x + c) / 2 ^ (L + 1) = (x + c) / 2 / 2 ^ L := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]
    have e2 : (x + c) / 2 ^ (L + 1) = (x / 2 + (x % 2 + c) / 2) / 2 ^ L := by
      rw [hx]; exact e2'
    simp only [prun, run]
    rw [lE_step_aux]
    constructor
    · rw [ih1, hx]
    · rw [e1, e2]
      exact ih2

theorem lE_run (L q c x y t : Nat) (hc : c ≤ 1) :
    (prun lE L (q, c) x y t).1 = run L q (x + c) y t ∧
    x / 2 ^ L + (prun lE L (q, c) x y t).2 = (x + c) / 2 ^ L := by
  exact lE_run_aux L q c x y t hc

theorem lN_step_aux (q c x y t : Nat) :
    lN (q, c) (dg x y t) = (tr q (dg x (y + c) t), (y % 2 + c) / 2) := by
  have h1 : tri (dx (dg x y t)) (sD (dy (dg x y t)) 0 c) (dz (dg x y t))
      = dg x (y + c) t := by
    rw [dx_dg_aux, dy_dg_aux, dz_dg_aux]
    unfold tri sD dg
    omega
  have h2 : aC (dy (dg x y t)) 0 c = (y % 2 + c) / 2 := by
    rw [dy_dg_aux]
    unfold aC
    omega
  unfold lN
  rw [h1, h2]

theorem lN_run_aux (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 →
    (prun lN L (q, c) x y t).1 = run L q x (y + c) t ∧
    y / 2 ^ L + (prun lN L (q, c) x y t).2 = (y + c) / 2 ^ L := by
  induction L with
  | zero =>
    intro q c x y t _
    simp [prun, run]
  | succ L ih =>
    intro q c x y t hc
    have hc' : (y % 2 + c) / 2 ≤ 1 := by omega
    obtain ⟨ih1, ih2⟩ := ih (tr q (dg x (y + c) t)) ((y % 2 + c) / 2) (x / 2) (y / 2) (t / 2) hc'
    have hy : y / 2 + (y % 2 + c) / 2 = (y + c) / 2 := by omega
    have e1 : y / 2 ^ (L + 1) = y / 2 / 2 ^ L := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]
    have e2' : (y + c) / 2 ^ (L + 1) = (y + c) / 2 / 2 ^ L := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]
    have e2 : (y + c) / 2 ^ (L + 1) = (y / 2 + (y % 2 + c) / 2) / 2 ^ L := by
      rw [hy]; exact e2'
    simp only [prun, run]
    rw [lN_step_aux]
    constructor
    · rw [ih1, hy]
    · rw [e1, e2]
      exact ih2

theorem lN_run (L q c x y t : Nat) (hc : c ≤ 1) :
    (prun lN L (q, c) x y t).1 = run L q x (y + c) t ∧
    y / 2 ^ L + (prun lN L (q, c) x y t).2 = (y + c) / 2 ^ L := by
  exact lN_run_aux L q c x y t hc

theorem lW_step_aux (q c x y t : Nat) (h : c ≤ x) :
    lW (q, c) (dg x y t) = (tr q (dg (x - c) y t), if x % 2 < c then 1 else 0) := by
  have h1 : tri (sD (dx (dg x y t)) 0 c) (dy (dg x y t)) (dz (dg x y t))
      = dg (x - c) y t := by
    rw [dx_dg_aux, dy_dg_aux, dz_dg_aux]
    unfold tri sD dg
    omega
  have h2 : sB (dx (dg x y t)) 0 c = if x % 2 < c then 1 else 0 := by
    rw [dx_dg_aux]
    unfold sB
    simp
  unfold lW
  rw [h1, h2]

theorem lW_run_aux (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 → c ≤ x →
    (prun lW L (q, c) x y t).1 = run L q (x - c) y t := by
  induction L with
  | zero =>
    intro q c x y t _ _
    simp [prun, run]
  | succ L ih =>
    intro q c x y t hc h
    have hc' : (if x % 2 < c then 1 else 0) ≤ 1 := by split <;> omega
    have hc'' : (if x % 2 < c then 1 else 0) ≤ x / 2 := by split <;> omega
    have e : (x - c) / 2 = x / 2 - (if x % 2 < c then 1 else 0) := by split <;> omega
    have ih1 := ih (tr q (dg (x - c) y t)) (if x % 2 < c then 1 else 0) (x / 2) (y / 2) (t / 2) hc' hc''
    simp only [prun, run]
    rw [lW_step_aux q c x y t h, e]
    exact ih1

theorem lW_run (L q c x y t : Nat) (hc : c ≤ 1) (h : c ≤ x) :
    (prun lW L (q, c) x y t).1 = run L q (x - c) y t :=
  lW_run_aux L q c x y t hc h

/-- x % 2^(L+1) splits as its lowest bit plus 2 times (x/2) % 2^L -/
theorem pow_split_aux (L x : Nat) :
    x % 2 ^ (L + 1) = x % 2 + 2 * (x / 2 % 2 ^ L) := by
  have hP : 0 < 2 ^ L := by
    first
    | exact Nat.two_pow_pos L
    | exact Nat.pos_pow_of_pos L (by decide)
    | simp
  have hm := Nat.div_add_mod (x / 2) (2 ^ L)
  have hr := Nat.mod_lt (x / 2) hP
  have hx := Nat.div_add_mod x 2
  have e2 : 2 * 2 ^ L * (x / 2 / 2 ^ L) = 2 * (2 ^ L * (x / 2 / 2 ^ L)) :=
    Nat.mul_assoc 2 (2 ^ L) (x / 2 / 2 ^ L)
  have e : x = x % 2 + 2 * (x / 2 % 2 ^ L) + 2 * 2 ^ L * (x / 2 / 2 ^ L) := by
    omega
  have h5 : x % (2 * 2 ^ L) = (x % 2 + 2 * (x / 2 % 2 ^ L) + 2 * 2 ^ L * (x / 2 / 2 ^ L))
      % (2 * 2 ^ L) := congrArg (fun z => z % (2 * 2 ^ L)) e
  have h6 : x % 2 + 2 * (x / 2 % 2 ^ L) < 2 * 2 ^ L := by omega
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ L) 2, h5, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h6]

theorem lW_borrow_aux (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 →
    (prun lW L (q, c) x y t).2 = if x % 2 ^ L < c then 1 else 0 := by
  induction L with
  | zero =>
    intro q c x y t hc
    have h0 : (prun lW 0 (q, c) x y t).2 = c := rfl
    rw [h0]
    have hc2 : c = 0 ∨ c = 1 := by omega
    rcases hc2 with rfl | rfl <;> simp [Nat.mod_one]
  | succ L ih =>
    intro q c x y t hc
    have hstep : prun lW (L + 1) (q, c) x y t
        = prun lW L (lW (q, c) (dg x y t)) (x / 2) (y / 2) (t / 2) := by
      first
      | rfl
      | simp only [prun]
    have hb : (lW (q, c) (dg x y t)).2 = if x % 2 < c then 1 else 0 := by
      first
      | simp [lW, sB, dx_dg_aux]
      | (unfold lW sB; rw [dx_dg_aux]; simp)
    have hc' : (lW (q, c) (dg x y t)).2 ≤ 1 := by
      rw [hb]
      by_cases h1 : x % 2 < c
      · rw [if_pos h1]; decide
      · rw [if_neg h1]; decide
    have ih' : (prun lW L (lW (q, c) (dg x y t)) (x / 2) (y / 2) (t / 2)).2
        = if x / 2 % 2 ^ L < (lW (q, c) (dg x y t)).2 then 1 else 0 :=
      ih (lW (q, c) (dg x y t)).1 (lW (q, c) (dg x y t)).2 (x / 2) (y / 2) (t / 2) hc'
    rw [hstep, ih', hb, pow_split_aux]
    by_cases h1 : x % 2 < c
    · rw [if_pos h1]
      by_cases h2 : x / 2 % 2 ^ L < 1
      · have h3 : x % 2 + 2 * (x / 2 % 2 ^ L) < c := by omega
        rw [if_pos h2, if_pos h3]
      · have h3 : ¬ (x % 2 + 2 * (x / 2 % 2 ^ L) < c) := by omega
        rw [if_neg h2, if_neg h3]
    · rw [if_neg h1]
      have h2 : ¬ (x / 2 % 2 ^ L < 0) := by omega
      have h3 : ¬ (x % 2 + 2 * (x / 2 % 2 ^ L) < c) := by omega
      rw [if_neg h2, if_neg h3]

theorem lW_borrow (L q c x y t : Nat) (hc : c ≤ 1) :
    (prun lW L (q, c) x y t).2 = if x % 2 ^ L < c then 1 else 0 :=
  lW_borrow_aux L q c x y t hc

end A272706
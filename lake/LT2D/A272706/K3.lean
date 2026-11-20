-- A272706 / Rule 515, file K3 (core Lean only; adapted from A273331 K3 #mwly1lig-fs4fe3: rule 654 -> 515,
-- 104 -> 15 states in key1, F1 end condition extended by bit 3, and the bitmask rebuild of list certificates
-- replaced by an in-kernel F1 certificate (E2)): products for F2 (seed) and F1 (one CA step), their kernel-checked
-- certificates, and F2_V (F1_V and NB3_V are in K4).
-- Lemma numbering follows the congress plan (leader/a273331/sketch.md); every proof below is complete.
import LT2D.A272706.K2
namespace A272706

/-! ## F2: V x y 1 = [x = 0 and y = 0] -/

/-- q-lane of F2: reads (x, y, f) where the whole t value is the bit f -/
def lF (p : Nat × Nat) (d : Nat) : Nat × Nat := (tr p.1 (tri (dx d) (dy d) p.2), 0)
/-- zero flags of the x digits and of the y digits -/
def lZx (a d : Nat) : Nat := a * (1 - dx d)
def lZy (a d : Nat) : Nat := a * (1 - dy d)

structure P2 where
  q : Nat
  f : Nat
  xz : Nat
  yz : Nat
deriving DecidableEq

def step2 (P : P2) (d : Nat) : P2 :=
  ⟨(lF (P.q, P.f) d).1, (lF (P.q, P.f) d).2, lZx P.xz d, lZy P.yz d⟩
def start2 : P2 := ⟨0, 1, 1, 1⟩
def end2 (P : P2) : Bool := P.f == 1 || (out P.q == (P.xz == 1 && P.yz == 1))
def key2 (P : P2) : Nat := mix (((P.q * 2 + P.f) * 2 + P.xz) * 2 + P.yz)
def cert2 : BT P2 := explore key2 step2 400 [start2] .leaf

/-- E1 (kernel): 10 states -/
theorem cert2_ok : certOK key2 step2 end2 start2 cert2 = true := by
  decide +kernel

theorem r515_mod_pow_succ (L x : Nat) : x % 2 ^ (L + 1) = x % 2 + 2 * (x / 2 % 2 ^ L) := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]

theorem lF_run (L q f x y z : Nat) (hf : f ≤ 1) :
    (prun lF L (q, f) x y z).1 = run L q x y f ∧ (1 ≤ L → (prun lF L (q, f) x y z).2 = 0) := by
  induction L generalizing q f x y z with
  | zero => exact ⟨rfl, fun h => absurd h (by decide)⟩
  | succ L ih =>
    have hd : tri (dx (dg x y z)) (dy (dg x y z)) f = dg x y f := by
      obtain ⟨h1, h2, -⟩ := dg_parts x y z
      rw [h1, h2]
      simp only [tri, dg]
      omega
    have h := ih (tr q (tri (dx (dg x y z)) (dy (dg x y z)) f)) 0 (x / 2) (y / 2) (z / 2) (by decide)
    refine ⟨?_, fun _ => ?_⟩
    · show (prun lF L (tr q (tri (dx (dg x y z)) (dy (dg x y z)) f), 0) (x / 2) (y / 2) (z / 2)).1 =
        prun tr L (tr q (dg x y f)) (x / 2) (y / 2) (f / 2)
      rw [h.1, hd, Nat.div_eq_of_lt (by omega : f < 2)]
    · show (prun lF L (tr q (tri (dx (dg x y z)) (dy (dg x y z)) f), 0) (x / 2) (y / 2) (z / 2)).2 = 0
      cases L with
      | zero => rfl
      | succ L => exact h.2 (by omega)

theorem lZx_run (L a x y z : Nat) (ha : a ≤ 1) :
    prun lZx L a x y z = if x % 2 ^ L = 0 then a else 0 := by
  induction L generalizing a x y z with
  | zero => simp [prun, Nat.mod_one]
  | succ L ih =>
    show prun lZx L (lZx a (dg x y z)) (x / 2) (y / 2) (z / 2) = if x % 2 ^ (L + 1) = 0 then a else 0
    have hd : dx (dg x y z) = x % 2 := (dg_parts x y z).1
    have hm := r515_mod_pow_succ L x
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have e : lZx a (dg x y z) = a := by simp [lZx, hd, h]
      rw [e, ih a (x / 2) (y / 2) (z / 2) ha, hm, h]
      by_cases h2 : x / 2 % 2 ^ L = 0 <;> simp [h2] <;> omega
    · have e : lZx a (dg x y z) = 0 := by simp [lZx, hd, h]
      rw [e, ih 0 (x / 2) (y / 2) (z / 2) (by decide), hm, h]
      simp

theorem lZy_run (L a x y z : Nat) (ha : a ≤ 1) :
    prun lZy L a x y z = if y % 2 ^ L = 0 then a else 0 := by
  induction L generalizing a x y z with
  | zero => simp [prun, Nat.mod_one]
  | succ L ih =>
    show prun lZy L (lZy a (dg x y z)) (x / 2) (y / 2) (z / 2) = if y % 2 ^ (L + 1) = 0 then a else 0
    have hd : dy (dg x y z) = y % 2 := (dg_parts x y z).2.1
    have hm := r515_mod_pow_succ L y
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · have e : lZy a (dg x y z) = a := by simp [lZy, hd, h]
      rw [e, ih a (x / 2) (y / 2) (z / 2) ha, hm, h]
      by_cases h2 : y / 2 % 2 ^ L = 0 <;> simp [h2] <;> omega
    · have e : lZy a (dg x y z) = 0 := by simp [lZy, hd, h]
      rw [e, ih 0 (x / 2) (y / 2) (z / 2) (by decide), hm, h]
      simp

/-- F2 -/
theorem F2_V (x y : Nat) : V x y 1 = (x == 0 && y == 0) := by
  have hlt : ∀ n : Nat, n < 2 ^ n := fun n => Nat.lt_two_pow_self
  have hx : x < 2 ^ (x + y + 1) :=
    Nat.lt_of_lt_of_le (hlt x) (Nat.pow_le_pow_right (by decide) (by omega))
  have hy : y < 2 ^ (x + y + 1) :=
    Nat.lt_of_lt_of_le (hlt y) (Nat.pow_le_pow_right (by decide) (by omega))
  have h1 : 1 < 2 ^ (x + y + 1) :=
    Nat.lt_of_lt_of_le (hlt 1) (Nat.pow_le_pow_right (by decide) (by omega))
  have he := cert_sound key2 step2 end2 start2 cert2 cert2_ok (x + y + 1) x y 0
  have pq : ((prun step2 (x + y + 1) start2 x y 0).q, (prun step2 (x + y + 1) start2 x y 0).f)
      = prun lF (x + y + 1) (0, 1) x y 0 :=
    prun_proj step2 lF (fun P => (P.q, P.f)) (fun _ _ => rfl) (x + y + 1) start2 x y 0
  have px : (prun step2 (x + y + 1) start2 x y 0).xz = prun lZx (x + y + 1) 1 x y 0 :=
    prun_proj step2 lZx (fun P => P.xz) (fun _ _ => rfl) (x + y + 1) start2 x y 0
  have py : (prun step2 (x + y + 1) start2 x y 0).yz = prun lZy (x + y + 1) 1 x y 0 :=
    prun_proj step2 lZy (fun P => P.yz) (fun _ _ => rfl) (x + y + 1) start2 x y 0
  have fa := lF_run (x + y + 1) 0 1 x y 0 (by decide)
  have fx := lZx_run (x + y + 1) 1 x y 0 (by decide)
  have fy := lZy_run (x + y + 1) 1 x y 0 (by decide)
  have hq : (prun step2 (x + y + 1) start2 x y 0).q = run (x + y + 1) 0 x y 1 := by
    have := congrArg Prod.fst pq
    dsimp only at this
    rw [this]
    exact fa.1
  have hf : (prun step2 (x + y + 1) start2 x y 0).f = 0 := by
    have := congrArg Prod.snd pq
    dsimp only at this
    rw [this]
    exact fa.2 (by omega)
  have hxz : (prun step2 (x + y + 1) start2 x y 0).xz = if x = 0 then 1 else 0 := by
    rw [px, fx, Nat.mod_eq_of_lt hx]
  have hyz : (prun step2 (x + y + 1) start2 x y 0).yz = if y = 0 then 1 else 0 := by
    rw [py, fy, Nat.mod_eq_of_lt hy]
  have hV := out_run_eq_V (x + y + 1) x y 1 hx hy h1
  simp only [end2, hf, hq, hxz, hyz] at he
  have hVx : V x y 1 = out (run (x + y + 1) 0 x y 1) := hV.symm
  rw [hVx]
  by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0 <;> simp_all

/-! ## F1: one step of Rule 515 on the quadrant, with the mirror at x = 0 and y = 0 -/

/-- Rule 515: new state = bit (c + 2k) of 515 (c = own state, k = ON axial neighbours) -/
def rule (c : Bool) (k : Nat) : Bool := Nat.testBit 515 (c.toNat + 2 * k)

/-- t-nonzero flag -/
def lTz (a d : Nat) : Nat := max a (dz d)

structure P1 where
  qc : Nat
  qT : Nat
  cT : Nat
  qE : Nat
  cE : Nat
  qW : Nat
  bW : Nat
  qN : Nat
  cN : Nat
  qS : Nat
  bS : Nat
  tz : Nat
deriving DecidableEq

def step1 (P : P1) (d : Nat) : P1 :=
  ⟨tr P.qc d, (lT (P.qT, P.cT) d).1, (lT (P.qT, P.cT) d).2,
   (lE (P.qE, P.cE) d).1, (lE (P.qE, P.cE) d).2, (lW (P.qW, P.bW) d).1, (lW (P.qW, P.bW) d).2,
   (lN (P.qN, P.cN) d).1, (lN (P.qN, P.cN) d).2, (lS (P.qS, P.bS) d).1, (lS (P.qS, P.bS) d).2,
   lTz P.tz d⟩
def start1 : P1 := ⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩

/-- end condition, all further digits 0; each lane reads one more zero digit triple;
a borrow still pending means x = 0 (or y = 0): use the mirror value.  Second conjunct (new for
Rule 523): an ON cell never has exactly one ON neighbour (the only input where 515 and 523 differ) -/
def end1 (P : P1) : Bool :=
  P.tz == 0 ||
    (let vE := out (tr P.qE P.cE)
     let vN := out (tr P.qN (2 * P.cN))
     let vW := if P.bW = 1 then vE else out (tr P.qW 0)
     let vS := if P.bS = 1 then vN else out (tr P.qS 0)
     let k := vE.toNat + vW.toNat + vN.toNat + vS.toNat
     (out (tr P.qT (4 * P.cT)) == rule (out P.qc) k) && !(out P.qc && k == 1))

theorem lTz_run_aux (L : Nat) : ∀ a x y t : Nat, a ≤ 1 →
    prun lTz L a x y t = if t % 2 ^ L = 0 then a else 1 := by
  induction L with
  | zero =>
    intro a x y t ha
    have h0 : prun lTz 0 a x y t = a := rfl
    rw [h0, Nat.pow_zero, Nat.mod_one, if_pos rfl]
  | succ L ih =>
    intro a x y t ha
    have hstep : prun lTz (L + 1) a x y t
        = prun lTz L (lTz a (dg x y t)) (x / 2) (y / 2) (t / 2) := by
      first
      | rfl
      | simp only [prun]
    have hd : dz (dg x y t) = t % 2 := by
      unfold dz dg; omega
    have hl : lTz a (dg x y t) = max a (t % 2) := by
      unfold lTz; rw [hd]
    have hm : max a (t % 2) ≤ 1 := by omega
    rw [hstep, hl, ih (max a (t % 2)) (x / 2) (y / 2) (t / 2) hm, pow_split_aux]
    generalize t / 2 % 2 ^ L = m
    by_cases hm0 : m = 0
    · rw [if_pos hm0]
      by_cases ht : t % 2 = 0
      · rw [if_pos (by omega : t % 2 + 2 * m = 0), ht]
        simp
      · have h1 : t % 2 = 1 := by omega
        rw [if_neg (by omega : ¬ (t % 2 + 2 * m = 0)), h1, Nat.max_def]
        split <;> omega
    · rw [if_neg hm0, if_neg (by omega : ¬ (t % 2 + 2 * m = 0))]

def key1 (P : P1) : Nat :=
  mix (((((((((((P.qc * 15 + P.qT) * 15 + P.qE) * 15 + P.qW) * 15 + P.qN) * 15 + P.qS)
    * 2 + P.cT) * 2 + P.cE) * 2 + P.bW) * 2 + P.cN) * 2 + P.bS) * 2 + P.tz)
theorem lTz_run (L a x y t : Nat) (ha : a ≤ 1) :
    prun lTz L a x y t = if t % 2 ^ L = 0 then a else 1 :=
  lTz_run_aux L a x y t ha

/-! ## E2: the F1 certificate, explored by the kernel (155 states; Rule 654 needed 4,462) -/

def cert1 : BT P1 := explore key1 step1 3000 [start1] .leaf

/-- E2 (kernel) -/
theorem cert1_ok : certOK key1 step1 end1 start1 cert1 = true := by
  decide +kernel

/-- E2: the F1 end condition holds after every digit string -/
theorem cert1_sound (L x y z : Nat) : end1 (prun step1 L start1 x y z) = true :=
  cert_sound key1 step1 end1 start1 cert1 cert1_ok L x y z

end A272706
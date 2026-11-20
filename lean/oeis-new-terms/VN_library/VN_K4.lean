import LongTable.P_mwmor81y_3b5r9w
-- VN library, file K4 (core Lean only): the south lane (from A272706 K4), the F2 product (seed check)
-- and F2_V. Generic version of the F2 part of A272706 K3 (#mwmg2qh7-qxah27); the table is the parameter A.
namespace VN

theorem lS_step_aux (A : Tab) (q c x y t : Nat) (h : c ≤ y) :
    lS A (q, c) (dg x y t) = (tr A q (dg x (y - c) t), if y % 2 < c then 1 else 0) := by
  have h1 : tri (dx (dg x y t)) (sD (dy (dg x y t)) 0 c) (dz (dg x y t))
      = dg x (y - c) t := by
    rw [dx_dg_aux, dy_dg_aux, dz_dg_aux]
    unfold tri sD dg
    omega
  have h2 : sB (dy (dg x y t)) 0 c = if y % 2 < c then 1 else 0 := by
    rw [dy_dg_aux]
    unfold sB
    simp
  unfold lS
  rw [h1, h2]

theorem lS_run (A : Tab) (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 → c ≤ y →
    (prun (lS A) L (q, c) x y t).1 = run A L q x (y - c) t := by
  induction L with
  | zero =>
    intro q c x y t _ _
    simp [prun, run]
  | succ L ih =>
    intro q c x y t hc h
    have hc' : (if y % 2 < c then 1 else 0) ≤ 1 := by split <;> omega
    have hc'' : (if y % 2 < c then 1 else 0) ≤ y / 2 := by split <;> omega
    have e : (y - c) / 2 = y / 2 - (if y % 2 < c then 1 else 0) := by split <;> omega
    have ih1 := ih (tr A q (dg x (y - c) t)) (if y % 2 < c then 1 else 0) (x / 2) (y / 2) (t / 2) hc' hc''
    simp only [prun, run]
    rw [lS_step_aux A q c x y t h, e]
    exact ih1

theorem lS_borrow (A : Tab) (L : Nat) : ∀ q c x y t : Nat, c ≤ 1 →
    (prun (lS A) L (q, c) x y t).2 = if y % 2 ^ L < c then 1 else 0 := by
  induction L with
  | zero =>
    intro q c x y t hc
    have h0 : (prun (lS A) 0 (q, c) x y t).2 = c := rfl
    rw [h0]
    have hc2 : c = 0 ∨ c = 1 := by omega
    rcases hc2 with rfl | rfl <;> simp [Nat.mod_one]
  | succ L ih =>
    intro q c x y t hc
    have hstep : prun (lS A) (L + 1) (q, c) x y t
        = prun (lS A) L (lS A (q, c) (dg x y t)) (x / 2) (y / 2) (t / 2) := by
      first
      | rfl
      | simp only [prun]
    have hb : (lS A (q, c) (dg x y t)).2 = if y % 2 < c then 1 else 0 := by
      first
      | simp [lS, sB, dy_dg_aux]
      | (unfold lS sB; rw [dy_dg_aux]; simp)
    have hc' : (lS A (q, c) (dg x y t)).2 ≤ 1 := by
      rw [hb]
      by_cases h1 : y % 2 < c
      · rw [if_pos h1]; decide
      · rw [if_neg h1]; decide
    have ih' : (prun (lS A) L (lS A (q, c) (dg x y t)) (x / 2) (y / 2) (t / 2)).2
        = if y / 2 % 2 ^ L < (lS A (q, c) (dg x y t)).2 then 1 else 0 :=
      ih (lS A (q, c) (dg x y t)).1 (lS A (q, c) (dg x y t)).2 (x / 2) (y / 2) (t / 2) hc'
    rw [hstep, ih', hb, pow_split_aux L y]
    by_cases h1 : y % 2 < c
    · rw [if_pos h1]
      by_cases h2 : y / 2 % 2 ^ L < 1
      · have h3 : y % 2 + 2 * (y / 2 % 2 ^ L) < c := by omega
        rw [if_pos h2, if_pos h3]
      · have h3 : ¬ (y % 2 + 2 * (y / 2 % 2 ^ L) < c) := by omega
        rw [if_neg h2, if_neg h3]
    · rw [if_neg h1]
      have h2 : ¬ (y / 2 % 2 ^ L < 0) := by omega
      have h3 : ¬ (y % 2 + 2 * (y / 2 % 2 ^ L) < c) := by omega
      rw [if_neg h2, if_neg h3]

/-! ## F2: V x y 1 = [x = 0 and y = 0] -/

/-- exploration fuel of the kernel certificates (any value is sound: too little fuel makes a check false) -/
def fuel : Nat := 1000000

/-- q-lane of F2: reads (x, y, f) where the whole t value is the bit f -/
def lF (A : Tab) (p : Nat × Nat) (d : Nat) : Nat × Nat := (tr A p.1 (tri (dx d) (dy d) p.2), 0)
/-- zero flags of the x digits and of the y digits -/
def lZx (a d : Nat) : Nat := a * (1 - dx d)
def lZy (a d : Nat) : Nat := a * (1 - dy d)

/-- F2 product state: q = table state; f = the t bit still to be read (1 before the
first digit, then 0, so the run reads t = 1); xz, yz = 1 iff every x (resp. y) digit read so far is 0 -/
structure P2 where
  q : Nat
  f : Nat
  xz : Nat
  yz : Nat
deriving DecidableEq

/-- one digit triple d applied to the four components -/
def step2 (A : Tab) (P : P2) (d : Nat) : P2 :=
  ⟨(lF A (P.q, P.f) d).1, (lF A (P.q, P.f) d).2, lZx P.xz d, lZy P.yz d⟩
/-- start: table state 0, t = 1, both zero flags set -/
def start2 : P2 := ⟨0, 1, 1, 1⟩
/-- F2 end condition: the start state (f = 1) is exempt; after a digit, out q = [every x digit
and every y digit read is 0] -/
def end2 (A : Tab) (P : P2) : Bool := P.f == 1 || (out A P.q == (P.xz == 1 && P.yz == 1))
/-- tree key of a product state; soundness (cert_sound) needs no property of the key -/
def key2 (P : P2) : Nat := mix (((P.q * 2 + P.f) * 2 + P.xz) * 2 + P.yz)

/-- CHECK F2 (kernel): the seed product, explored and checked -/
def checkF2 (A : Tab) : Bool :=
  certOK key2 (step2 A) (end2 A) start2 (explore key2 (step2 A) fuel [start2] .leaf)

theorem lF_run (A : Tab) (L q f x y z : Nat) (hf : f ≤ 1) :
    (prun (lF A) L (q, f) x y z).1 = run A L q x y f ∧ (1 ≤ L → (prun (lF A) L (q, f) x y z).2 = 0) := by
  induction L generalizing q f x y z with
  | zero => exact ⟨rfl, fun h => absurd h (by decide)⟩
  | succ L ih =>
    have hd : tri (dx (dg x y z)) (dy (dg x y z)) f = dg x y f := by
      obtain ⟨h1, h2, -⟩ := dg_parts x y z
      rw [h1, h2]
      simp only [tri, dg]
      omega
    have h := ih (tr A q (tri (dx (dg x y z)) (dy (dg x y z)) f)) 0 (x / 2) (y / 2) (z / 2) (by decide)
    refine ⟨?_, fun _ => ?_⟩
    · show (prun (lF A) L (tr A q (tri (dx (dg x y z)) (dy (dg x y z)) f), 0) (x / 2) (y / 2) (z / 2)).1 =
        prun (tr A) L (tr A q (dg x y f)) (x / 2) (y / 2) (f / 2)
      rw [h.1, hd, Nat.div_eq_of_lt (by omega : f < 2)]
    · show (prun (lF A) L (tr A q (tri (dx (dg x y z)) (dy (dg x y z)) f), 0) (x / 2) (y / 2) (z / 2)).2 = 0
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
    have hm := pow_split_aux L x
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
    have hm := pow_split_aux L y
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · have e : lZy a (dg x y z) = a := by simp [lZy, hd, h]
      rw [e, ih a (x / 2) (y / 2) (z / 2) ha, hm, h]
      by_cases h2 : y / 2 % 2 ^ L = 0 <;> simp [h2] <;> omega
    · have e : lZy a (dg x y z) = 0 := by simp [lZy, hd, h]
      rw [e, ih 0 (x / 2) (y / 2) (z / 2) (by decide), hm, h]
      simp

/-- F2_V: if CHECK F2 passes, V at time 1 (stage 0) is the seed -/
theorem F2_V (A : Tab) (h2 : checkF2 A = true) (x y : Nat) : V A x y 1 = (x == 0 && y == 0) := by
  have hlt : ∀ n : Nat, n < 2 ^ n := fun n => Nat.lt_two_pow_self
  have hx : x < 2 ^ (x + y + 1) :=
    Nat.lt_of_lt_of_le (hlt x) (Nat.pow_le_pow_right (by decide) (by omega))
  have hy : y < 2 ^ (x + y + 1) :=
    Nat.lt_of_lt_of_le (hlt y) (Nat.pow_le_pow_right (by decide) (by omega))
  have h1 : 1 < 2 ^ (x + y + 1) :=
    Nat.lt_of_lt_of_le (hlt 1) (Nat.pow_le_pow_right (by decide) (by omega))
  have he := cert_sound key2 (step2 A) (end2 A) start2
    (explore key2 (step2 A) fuel [start2] .leaf) h2 (x + y + 1) x y 0
  have pq : ((prun (step2 A) (x + y + 1) start2 x y 0).q, (prun (step2 A) (x + y + 1) start2 x y 0).f)
      = prun (lF A) (x + y + 1) (0, 1) x y 0 :=
    prun_proj (step2 A) (lF A) (fun P => (P.q, P.f)) (fun _ _ => rfl) (x + y + 1) start2 x y 0
  have px : (prun (step2 A) (x + y + 1) start2 x y 0).xz = prun lZx (x + y + 1) 1 x y 0 :=
    prun_proj (step2 A) lZx (fun P => P.xz) (fun _ _ => rfl) (x + y + 1) start2 x y 0
  have py : (prun (step2 A) (x + y + 1) start2 x y 0).yz = prun lZy (x + y + 1) 1 x y 0 :=
    prun_proj (step2 A) lZy (fun P => P.yz) (fun _ _ => rfl) (x + y + 1) start2 x y 0
  have fa := lF_run A (x + y + 1) 0 1 x y 0 (by decide)
  have fx := lZx_run (x + y + 1) 1 x y 0 (by decide)
  have fy := lZy_run (x + y + 1) 1 x y 0 (by decide)
  have hq : (prun (step2 A) (x + y + 1) start2 x y 0).q = run A (x + y + 1) 0 x y 1 := by
    have := congrArg Prod.fst pq
    dsimp only at this
    rw [this]
    exact fa.1
  have hf : (prun (step2 A) (x + y + 1) start2 x y 0).f = 0 := by
    have := congrArg Prod.snd pq
    dsimp only at this
    rw [this]
    exact fa.2 (by omega)
  have hxz : (prun (step2 A) (x + y + 1) start2 x y 0).xz = if x = 0 then 1 else 0 := by
    rw [px, fx, Nat.mod_eq_of_lt hx]
  have hyz : (prun (step2 A) (x + y + 1) start2 x y 0).yz = if y = 0 then 1 else 0 := by
    rw [py, fy, Nat.mod_eq_of_lt hy]
  have hV := out_run_eq_V A (x + y + 1) x y 1 hx hy h1
  simp only [end2, hf, hq, hxz, hyz] at he
  have hVx : V A x y 1 = out A (run A (x + y + 1) 0 x y 1) := hV.symm
  rw [hVx]
  by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0 <;> simp_all

end VN
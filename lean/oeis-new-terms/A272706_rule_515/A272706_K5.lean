-- A272706 / Rule 515, file K5 (core Lean only): the counts of V over the square [0, 2^n)^2, its two axes and
-- the origin at time 2^n, as digit-string sums through the 15-state automaton (linear representation,
-- backward form). Closed forms in K6.
import LongTable.P_mwmfkzh5_8rq7id
namespace A272706

/-- sumTo h m = h 0 + h 1 + ... + h (m - 1) -/
def sumTo (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumTo h m + h m

/-- one backward step over the digit list D (digit triples with t-digit 0): Σ_{d ∈ D} g (tr q d) -/
def AD (D : List Nat) (g : Nat → Nat) (q : Nat) : Nat :=
  D.foldr (fun d acc => g (tr q d) + acc) 0

/-- it D g n q = Σ over the digit strings w ∈ D^n of g (state reached from q by w) -/
def it (D : List Nat) (g : Nat → Nat) : Nat → Nat → Nat
  | 0, q => g q
  | n + 1, q => AD D (it D g n) q

/-- the value at time t = 2^n after n digit triples with t-digit 0: one more triple (x, y, t) = (0, 0, 1) -/
def f4 (q : Nat) : Nat := (out (tr q 4)).toNat

/-- digit sets: the square (x and y free), the x-axis (y = 0), the y-axis (x = 0), the origin -/
def D4 : List Nat := [0, 1, 2, 3]
def DX : List Nat := [0, 1]
def DY : List Nat := [0, 2]
def D0 : List Nat := [0]

/-! ## C1-C9: sums over [0, 2^n) as digit-string sums -/

/-- C1: the low n digits of 2^n are 0 -/
theorem prun_t_pow {σ : Type} (step : σ → Nat → σ) (n : Nat) (P : σ) (x y : Nat) :
    prun step n P x y (2 ^ n) = prun step n P x y 0 := by
  induction n generalizing P x y with
  | zero => rfl
  | succ n ih =>
    have h1 : dg x y (2 ^ (n + 1)) = dg x y 0 := by
      have : 2 ^ (n + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      unfold dg; rw [this]
    have h2 : 2 ^ (n + 1) / 2 = 2 ^ n := by rw [Nat.pow_succ]; omega
    show prun step n (step P (dg x y (2 ^ (n + 1)))) (x / 2) (y / 2) (2 ^ (n + 1) / 2) =
      prun step n (step P (dg x y 0)) (x / 2) (y / 2) (0 / 2)
    rw [h1, h2, ih, Nat.zero_div]

/-- C2: V at time 2^n is read through n digit triples with t-digit 0 and then the triple (0, 0, 1) -/
theorem V_pow (n x y : Nat) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    V x y (2 ^ n) = out (tr (run n 0 x y 0) 4) := by
  have hp : 0 < 2 ^ n := Nat.lt_of_le_of_lt (Nat.zero_le n) Nat.lt_two_pow_self
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  have hV := out_run_eq_V (n + 1) x y (2 ^ n) (by omega) (by omega) (by omega)
  rw [← hV, run_succ_top, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, Nat.div_self hp,
    show run n 0 x y (2 ^ n) = run n 0 x y 0 from prun_t_pow tr n 0 x y]
  rfl

/-- C3 -/
theorem sumTo_congr (h1 h2 : Nat → Nat) (m : Nat) (h : ∀ i, i < m → h1 i = h2 i) :
    sumTo h1 m = sumTo h2 m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show sumTo h1 m + h1 m = sumTo h2 m + h2 m
    rw [ih (fun i hi => h i (by omega)), h m (by omega)]

/-- C4 -/
theorem sumTo_add (h1 h2 : Nat → Nat) (m : Nat) :
    sumTo (fun i => h1 i + h2 i) m = sumTo h1 m + sumTo h2 m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show sumTo (fun i => h1 i + h2 i) m + (h1 m + h2 m) = sumTo h1 m + h1 m + (sumTo h2 m + h2 m)
    rw [ih]; omega

/-- C5 -/
theorem sumTo_double (h : Nat → Nat) (m : Nat) :
    sumTo h (2 * m) = sumTo (fun i => h (2 * i) + h (2 * i + 1)) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    show sumTo h (2 * m) + h (2 * m) + h (2 * m + 1) =
      sumTo (fun i => h (2 * i) + h (2 * i + 1)) m + (h (2 * m) + h (2 * m + 1))
    rw [ih]; omega

/-- C5b: the square [0, 2M)^2 split by the lowest digits -/
theorem sumTo_sq_double (F : Nat → Nat → Nat) (M : Nat) :
    sumTo (fun x => sumTo (fun y => F x y) (2 * M)) (2 * M) =
      sumTo (fun i => sumTo (fun j => F (2 * i) (2 * j) + F (2 * i) (2 * j + 1) +
        (F (2 * i + 1) (2 * j) + F (2 * i + 1) (2 * j + 1))) M) M := by
  rw [sumTo_double]
  apply sumTo_congr
  intro i _
  show sumTo (fun y => F (2 * i) y) (2 * M) + sumTo (fun y => F (2 * i + 1) y) (2 * M) =
    sumTo (fun j => F (2 * i) (2 * j) + F (2 * i) (2 * j + 1) +
      (F (2 * i + 1) (2 * j) + F (2 * i + 1) (2 * j + 1))) M
  rw [sumTo_double, sumTo_double, ← sumTo_add]

/-- C5c: one low digit of x and y -/
theorem run_succ_low (n q i j a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    run (n + 1) q (2 * i + a) (2 * j + b) 0 = run n (tr q (2 * b + a)) i j 0 := by
  have hd : dg (2 * i + a) (2 * j + b) 0 = 2 * b + a := by unfold dg; omega
  show prun tr n (tr q (dg (2 * i + a) (2 * j + b) 0)) ((2 * i + a) / 2) ((2 * j + b) / 2) (0 / 2) = _
  rw [hd, show (2 * i + a) / 2 = i by omega, show (2 * j + b) / 2 = j by omega, Nat.zero_div]

/-- C6: the square sum is the digit-string sum over D4 -/
theorem sq_it (g : Nat → Nat) (n q : Nat) :
    sumTo (fun x => sumTo (fun y => g (run n q x y 0)) (2 ^ n)) (2 ^ n) = it D4 g n q := by
  induction n generalizing q with
  | zero => show 0 + (0 + g q) = g q; omega
  | succ n ih =>
    rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [Nat.pow_succ]; omega, sumTo_sq_double]
    have e : ∀ i j, g (run (n + 1) q (2 * i) (2 * j) 0) + g (run (n + 1) q (2 * i) (2 * j + 1) 0) +
        (g (run (n + 1) q (2 * i + 1) (2 * j) 0) + g (run (n + 1) q (2 * i + 1) (2 * j + 1) 0)) =
        g (run n (tr q 0) i j 0) + g (run n (tr q 2) i j 0) +
        (g (run n (tr q 1) i j 0) + g (run n (tr q 3) i j 0)) := by
      intro i j
      have e0 := run_succ_low n q i j 0 0 (by decide) (by decide)
      have e1 := run_succ_low n q i j 0 1 (by decide) (by decide)
      have e2 := run_succ_low n q i j 1 0 (by decide) (by decide)
      have e3 := run_succ_low n q i j 1 1 (by decide) (by decide)
      simp only [Nat.add_zero] at e0 e1 e2 e3
      rw [e0, e1, e2, e3]
    rw [sumTo_congr _ _ _ (fun i _ => sumTo_congr _ _ _ (fun j _ => e i j))]
    simp only [sumTo_add]
    rw [ih (tr q 0), ih (tr q 2), ih (tr q 1), ih (tr q 3)]
    show _ = it D4 g n (tr q 0) + (it D4 g n (tr q 1) + (it D4 g n (tr q 2) + (it D4 g n (tr q 3) + 0)))
    omega

/-- C7: the axis sums -/
theorem axX_it (g : Nat → Nat) (n q : Nat) :
    sumTo (fun x => g (run n q x 0 0)) (2 ^ n) = it DX g n q := by
  induction n generalizing q with
  | zero => show 0 + g q = g q; omega
  | succ n ih =>
    rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [Nat.pow_succ]; omega, sumTo_double]
    have e : ∀ i, g (run (n + 1) q (2 * i) 0 0) + g (run (n + 1) q (2 * i + 1) 0 0) =
        g (run n (tr q 0) i 0 0) + g (run n (tr q 1) i 0 0) := by
      intro i
      have e0 := run_succ_low n q i 0 0 0 (by decide) (by decide)
      have e2 := run_succ_low n q i 0 1 0 (by decide) (by decide)
      simp only [Nat.add_zero, Nat.mul_zero] at e0 e2
      rw [e0, e2]
    rw [sumTo_congr _ _ _ (fun i _ => e i), sumTo_add, ih (tr q 0), ih (tr q 1)]
    show _ = it DX g n (tr q 0) + (it DX g n (tr q 1) + 0)
    omega

theorem axY_it (g : Nat → Nat) (n q : Nat) :
    sumTo (fun y => g (run n q 0 y 0)) (2 ^ n) = it DY g n q := by
  induction n generalizing q with
  | zero => show 0 + g q = g q; omega
  | succ n ih =>
    rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [Nat.pow_succ]; omega, sumTo_double]
    have e : ∀ j, g (run (n + 1) q 0 (2 * j) 0) + g (run (n + 1) q 0 (2 * j + 1) 0) =
        g (run n (tr q 0) 0 j 0) + g (run n (tr q 2) 0 j 0) := by
      intro j
      have e0 := run_succ_low n q 0 j 0 0 (by decide) (by decide)
      have e1 := run_succ_low n q 0 j 0 1 (by decide) (by decide)
      simp only [Nat.add_zero, Nat.mul_zero] at e0 e1
      rw [e0, e1]
    rw [sumTo_congr _ _ _ (fun j _ => e j), sumTo_add, ih (tr q 0), ih (tr q 2)]
    show _ = it DY g n (tr q 0) + (it DY g n (tr q 2) + 0)
    omega

/-- C8: the origin -/
theorem orig_it (g : Nat → Nat) (n q : Nat) : g (run n q 0 0 0) = it D0 g n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have e0 := run_succ_low n q 0 0 0 0 (by decide) (by decide)
    simp only [Nat.add_zero, Nat.mul_zero] at e0
    rw [e0, ih (tr q 0)]
    show _ = it D0 g n (tr q 0) + 0
    omega

/-- C9: the four counts of V at time 2^n -/
theorem sq_V (n : Nat) :
    sumTo (fun x => sumTo (fun y => (V x y (2 ^ n)).toNat) (2 ^ n)) (2 ^ n) = it D4 f4 n 0 := by
  rw [← sq_it f4 n 0]
  apply sumTo_congr
  intro x hx
  apply sumTo_congr
  intro y hy
  rw [V_pow n x y hx hy]
  rfl

theorem axX_V (n : Nat) : sumTo (fun x => (V x 0 (2 ^ n)).toNat) (2 ^ n) = it DX f4 n 0 := by
  rw [← axX_it f4 n 0]
  apply sumTo_congr
  intro x hx
  rw [V_pow n x 0 hx (Nat.lt_of_le_of_lt (Nat.zero_le n) Nat.lt_two_pow_self)]
  rfl

theorem axY_V (n : Nat) : sumTo (fun y => (V 0 y (2 ^ n)).toNat) (2 ^ n) = it DY f4 n 0 := by
  rw [← axY_it f4 n 0]
  apply sumTo_congr
  intro y hy
  rw [V_pow n 0 y (Nat.lt_of_le_of_lt (Nat.zero_le n) Nat.lt_two_pow_self) hy]
  rfl

theorem orig_V (n : Nat) : (V 0 0 (2 ^ n)).toNat = it D0 f4 n 0 := by
  have hp : 0 < 2 ^ n := Nat.lt_of_le_of_lt (Nat.zero_le n) Nat.lt_two_pow_self
  rw [← orig_it f4 n 0, V_pow n 0 0 hp hp]
  rfl

end A272706
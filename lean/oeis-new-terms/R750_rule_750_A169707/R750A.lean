-- Rule 750 (OEIS A169707), file A (core Lean only, no Mathlib): the quadrant model W of the Rule 750
-- space-time diagram (mirrors at x = 0 and y = 0), and its elementary facts: speed (W_far), monotonicity,
-- symmetry, the axes, the diagonal. Follows the proof post #mwou7t5l-1hx9ra (E0, E1 for the axes, E2).
namespace R750

/-- Rule 750: new state = bit (c + 2k) of 750 (c = own state, k = number of ON neighbours) -/
def rule (c : Bool) (k : Nat) : Bool := Nat.testBit 750 (c.toNat + 2 * k)

/-- mirror predecessor: the neighbour below coordinate 0 is the cell at coordinate 1 -/
def mp (x : Nat) : Nat := if x = 0 then 1 else x - 1

/-- number of ON neighbours of (x, y) in a quadrant slice f, with mirrors at x = 0 and y = 0 -/
def kq (f : Nat → Nat → Bool) (x y : Nat) : Nat :=
  (f (x + 1) y).toNat + (f (mp x) y).toNat + (f x (y + 1)).toNat + (f x (mp y)).toNat

/-- W g x y: state of cell (x, y), x, y >= 0, at stage g (one ON cell at the origin at stage 0) -/
def W : Nat → Nat → Nat → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | g + 1 => fun x y => rule (W g x y) (kq (W g) x y)

theorem mp_zero : mp 0 = 1 := rfl
theorem mp_succ (x : Nat) : mp (x + 1) = x := by simp [mp]
theorem mp_pos {x : Nat} (h : 1 ≤ x) : mp x = x - 1 := by
  unfold mp; split <;> omega

theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem kq_le (f : Nat → Nat → Bool) (x y : Nat) : kq f x y ≤ 4 := by
  unfold kq
  have h1 := toNat_le_one (f (x + 1) y)
  have h2 := toNat_le_one (f (mp x) y)
  have h3 := toNat_le_one (f x (y + 1))
  have h4 := toNat_le_one (f x (mp y))
  omega

/-- Rule 750 on at most four neighbours: ON stays ON; OFF turns ON iff the count is odd -/
theorem rule_eq (c : Bool) (k : Nat) (h : k ≤ 4) : rule c k = (c || decide (k % 2 = 1)) := by
  have hb : ∀ c : Bool, ∀ k, k < 5 → rule c k = (c || decide (k % 2 = 1)) := by decide
  exact hb c k (by omega)

theorem W_succ (g x y : Nat) : W (g + 1) x y = (W g x y || decide (kq (W g) x y % 2 = 1)) :=
  rule_eq _ _ (kq_le _ _ _)

theorem W_succ_true (g x y : Nat) :
    W (g + 1) x y = true ↔ (W g x y = true ∨ kq (W g) x y % 2 = 1) := by
  rw [W_succ]
  cases W g x y <;> simp

theorem W_succ_false (g x y : Nat) :
    W (g + 1) x y = false ↔ (W g x y = false ∧ kq (W g) x y % 2 = 0) := by
  rw [W_succ]
  cases W g x y
  · simp
  · simp

/-- two cells with equal states and neighbour counts of equal parity have equal next states -/
theorem W_succ_congr {g g' x y x' y' : Nat} (h0 : W g x y = W g' x' y')
    (hk : kq (W g) x y % 2 = kq (W g') x' y' % 2) : W (g + 1) x y = W (g' + 1) x' y' := by
  rw [W_succ, W_succ, h0, hk]

theorem kq_eq (f : Nat → Nat → Bool) (x y : Nat) (a b c d : Bool) (h1 : f (x + 1) y = a)
    (h2 : f (mp x) y = b) (h3 : f x (y + 1) = c) (h4 : f x (mp y) = d) :
    kq f x y = a.toNat + b.toNat + c.toNat + d.toNat := by
  unfold kq; rw [h1, h2, h3, h4]

theorem kq_congr (f f' : Nat → Nat → Bool) (x y : Nat) (h1 : f (x + 1) y = f' (x + 1) y)
    (h2 : f (mp x) y = f' (mp x) y) (h3 : f x (y + 1) = f' x (y + 1))
    (h4 : f x (mp y) = f' x (mp y)) : kq f x y = kq f' x y := by
  unfold kq; rw [h1, h2, h3, h4]

theorem kq_swap (f : Nat → Nat → Bool) (hf : ∀ x y, f x y = f y x) (x y : Nat) :
    kq f x y = kq f y x := by
  unfold kq
  rw [hf (x + 1) y, hf (mp x) y, hf x (y + 1), hf x (mp y)]
  omega

theorem kq_diag_even (f : Nat → Nat → Bool) (hf : ∀ x y, f x y = f y x) (x : Nat) :
    kq f x x % 2 = 0 := by
  unfold kq
  rw [hf (x + 1) x, hf (mp x) x]
  omega

/-- E0 (speed): a cell at distance more than g from the origin is OFF at stage g -/
theorem W_far : ∀ (g x y : Nat), g < x + y → W g x y = false
  | 0, x, y, h => by
    show decide (x = 0 ∧ y = 0) = false
    simp
    omega
  | g + 1, x, y, h => by
    have h0 := W_far g x y (by omega)
    have h1 := W_far g (x + 1) y (by omega)
    have h2 := W_far g (mp x) y (by unfold mp; split <;> omega)
    have h3 := W_far g x (y + 1) (by omega)
    have h4 := W_far g x (mp y) (by unfold mp; split <;> omega)
    rw [W_succ_false]
    refine ⟨h0, ?_⟩
    rw [kq_eq (W g) x y false false false false h1 h2 h3 h4]
    rfl

theorem W_mono_succ {g x y : Nat} (h : W g x y = true) : W (g + 1) x y = true :=
  (W_succ_true g x y).mpr (Or.inl h)

theorem W_mono_add {g x y : Nat} (h : W g x y = true) : ∀ d, W (g + d) x y = true
  | 0 => h
  | d + 1 => W_mono_succ (W_mono_add h d)

theorem W_mono {g g' x y : Nat} (hle : g ≤ g') (h : W g x y = true) : W g' x y = true := by
  obtain ⟨d, rfl⟩ : ∃ d, g' = g + d := ⟨g' - g, by omega⟩
  exact W_mono_add h d

/-- symmetry under x <-> y -/
theorem W_swap : ∀ (g x y : Nat), W g x y = W g y x
  | 0, x, y => by
    show decide (x = 0 ∧ y = 0) = decide (y = 0 ∧ x = 0)
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  | g + 1, x, y => by
    rw [W_succ, W_succ, W_swap g x y, kq_swap (W g) (W_swap g) x y]

/-- E1 for the axis: (x, 0) is ON at stage x -/
theorem W_axis_diag : ∀ x : Nat, W x x 0 = true
  | 0 => by decide
  | x + 1 => by
    have h1 : W x (x + 1 + 1) 0 = false := W_far _ _ _ (by omega)
    have h2 : W x (mp (x + 1)) 0 = true := by rw [mp_succ]; exact W_axis_diag x
    rw [W_succ_true]
    right
    rw [kq_eq (W x) (x + 1) 0 false true (W x (x + 1) 1) (W x (x + 1) 1) h1 h2 rfl rfl]
    cases W x (x + 1) 1 <;> rfl

theorem W_axis_on {g x : Nat} (h : x ≤ g) : W g x 0 = true := W_mono h (W_axis_diag x)

theorem W_axis_eq {g x g' x' : Nat} (h : x ≤ g ↔ x' ≤ g') : W g x 0 = W g' x' 0 := by
  by_cases hx : x ≤ g
  · rw [W_axis_on hx, W_axis_on (h.mp hx)]
  · have hx' : ¬ x' ≤ g' := fun h' => hx (h.mpr h')
    rw [W_far g x 0 (by omega), W_far g' x' 0 (by omega)]

/-- E2: a diagonal cell other than the origin is never ON -/
theorem W_diag_off : ∀ (g x : Nat), 1 ≤ x → W g x x = false
  | 0, x, h => by
    show decide (x = 0 ∧ x = 0) = false
    simp
    omega
  | g + 1, x, h => by
    rw [W_succ_false]
    exact ⟨W_diag_off g x h, kq_diag_even (W g) (W_swap g) x⟩

end R750
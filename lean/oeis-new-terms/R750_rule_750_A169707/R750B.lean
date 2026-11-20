-- Rule 750 (OEIS A169707), file B (core Lean only, no Mathlib): the two copy lemmas of the proof post
-- #mwou7t5l-1hx9ra for a radius N whose shell x + y = N is ON at stage N (M = N + 1 there):
-- forward copy T1 (PA) and backward copy T2 (PB), proved together by induction on the time s.
import LongTable.P_mwovsmlu_4bs08b
namespace R750

/-- a cell at distance N + 1 off the axes is still OFF at stage N + 1 (its two inner neighbours are ON) -/
theorem dist_succ_off (N : Nat) (hsh : ∀ x y, x + y = N → W N x y = true) (x y : Nat)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (h : x + y = N + 1) : W (N + 1) x y = false := by
  rw [W_succ_false]
  refine ⟨W_far _ _ _ (by omega), ?_⟩
  rw [kq_eq (W N) x y false true false true (W_far _ _ _ (by omega))
    (by rw [mp_pos hx]; exact hsh _ _ (by omega)) (W_far _ _ _ (by omega))
    (by rw [mp_pos hy]; exact hsh _ _ (by omega))]
  rfl

/-- T1 at time s: the cell (N + 1 + x, y) at stage N + 1 + s copies the cell (x, y) at stage s -/
def PA (N s : Nat) : Prop := ∀ x y, x + y ≤ N → W (N + 1 + s) (N + 1 + x) y = W s x y

/-- T2 at time s: the cell (Z, X), Z = N + 1 - Y, at stage N + 1 + s copies the cell (X + 1, Y) at stage s + 1 -/
def PB (N s : Nat) : Prop := ∀ X Y Z, Z + Y = N + 1 → Y ≤ X → X + Y ≤ N →
    W (N + 1 + s) Z X = W (s + 1) (X + 1) Y

theorem kq_A (N s : Nat) (hs : s ≤ N) (hA : PA N s) (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : x + y ≤ N) : kq (W (N + 1 + s)) (N + 1 + x) y = kq (W s) x y := by
  have t1 : W (N + 1 + s) (N + 1 + x + 1) y = W s (x + 1) y := by
    by_cases h' : x + 1 + y ≤ N
    · exact hA (x + 1) y h'
    · rw [W_far (N + 1 + s) (N + 1 + x + 1) y (by omega), W_far s (x + 1) y (by omega)]
  have t2 : W (N + 1 + s) (mp (N + 1 + x)) y = W s (mp x) y := by
    have e1 : mp (N + 1 + x) = N + 1 + (x - 1) := by unfold mp; split <;> omega
    rw [e1, mp_pos hx]
    exact hA (x - 1) y (by omega)
  have t3 : W (N + 1 + s) (N + 1 + x) (y + 1) = W s x (y + 1) := by
    by_cases h' : x + (y + 1) ≤ N
    · exact hA x (y + 1) h'
    · rw [W_far (N + 1 + s) (N + 1 + x) (y + 1) (by omega), W_far s x (y + 1) (by omega)]
  have t4 : W (N + 1 + s) (N + 1 + x) (mp y) = W s x (mp y) :=
    hA x (mp y) (by rw [mp_pos hy]; omega)
  unfold kq
  rw [t1, t2, t3, t4]

/-- T2': the neighbour counts of (Z, X) at stage N + 1 + s and of (X + 1, Y) at stage s + 1 have the same parity -/
theorem kq_B (N : Nat) (hsh : ∀ x y, x + y = N → W N x y = true) (s : Nat) (hs : s ≤ N)
    (hB : PB N s) (X Y Z : Nat) (hZ : Z + Y = N + 1) (hY : 1 ≤ Y) (hYX : Y ≤ X) (hXY : X + Y ≤ N) :
    kq (W (N + 1 + s)) Z X % 2 = kq (W (s + 1)) (X + 1) Y % 2 := by
  have hZ1 : 1 ≤ Z := by omega
  have hX1 : 1 ≤ X := by omega
  have n1 : W (N + 1 + s) (Z + 1) X = W (s + 1) (X + 1) (mp Y) := by
    rw [mp_pos hY]; exact hB X (Y - 1) (Z + 1) (by omega) (by omega) (by omega)
  have n2 : W (N + 1 + s) Z (X + 1) = W (s + 1) (X + 1 + 1) Y := by
    by_cases h' : X + 1 + Y ≤ N
    · exact hB (X + 1) Y Z hZ (by omega) h'
    · have hZX : Z = X + 1 := by omega
      rw [hZX, W_diag_off (N + 1 + s) (X + 1) (by omega), W_far (s + 1) (X + 1 + 1) Y (by omega)]
  by_cases hlt : Y < X
  · have n3 : W (N + 1 + s) (mp Z) X = W (s + 1) (X + 1) (Y + 1) := by
      rw [mp_pos hZ1]
      by_cases h' : X + (Y + 1) ≤ N
      · exact hB X (Y + 1) (Z - 1) (by omega) (by omega) h'
      · have hZX : Z - 1 = X := by omega
        rw [hZX, W_diag_off (N + 1 + s) X hX1, W_far (s + 1) (X + 1) (Y + 1) (by omega)]
    have n4 : W (N + 1 + s) Z (mp X) = W (s + 1) (mp (X + 1)) Y := by
      rw [mp_pos hX1, mp_succ]
      have := hB (X - 1) Y Z hZ (by omega) (by omega)
      rw [show X - 1 + 1 = X by omega] at this
      exact this
    unfold kq
    rw [n1, n2, n3, n4]
    omega
  · have hYeq : Y = X := by omega
    have n3 : W (N + 1 + s) (mp Z) X = true := by
      rw [mp_pos hZ1]; exact W_mono (by omega) (hsh (Z - 1) X (by omega))
    have n3' : W (s + 1) (X + 1) (Y + 1) = false := by
      rw [hYeq]; exact W_diag_off _ _ (by omega)
    have n4 : W (N + 1 + s) Z (mp X) = true := by
      rw [mp_pos hX1]; exact W_mono (by omega) (hsh Z (X - 1) (by omega))
    have n4' : W (s + 1) (mp (X + 1)) Y = false := by
      rw [mp_succ, hYeq]; exact W_diag_off _ _ hX1
    unfold kq
    rw [n1, n2, n3, n4, n3', n4']
    rw [show true.toNat = 1 from rfl, show false.toNat = 0 from rfl]
    omega

/-- T1 and T2 for every time s <= N -/
theorem copy_AB (N : Nat) (hsh : ∀ x y, x + y = N → W N x y = true) :
    ∀ s, s ≤ N → PA N s ∧ PB N s := by
  intro s
  induction s with
  | zero =>
    intro _
    constructor
    · intro x y h
      by_cases h0 : x = 0 ∧ y = 0
      · obtain ⟨rfl, rfl⟩ := h0
        show W (N + 1) (N + 1) 0 = W 0 0 0
        rw [W_axis_diag (N + 1), W_axis_diag 0]
      · show W (N + 1) (N + 1 + x) y = W 0 x y
        rw [W_far (N + 1) (N + 1 + x) y (by omega), W_far 0 x y (by omega)]
    · intro X Y Z hZ hYX hXY
      show W (N + 1) Z X = W 1 (X + 1) Y
      by_cases hY : Y = 0
      · subst hY
        have hZ' : Z = N + 1 := by omega
        subst hZ'
        by_cases hX : X = 0
        · subst hX
          show W (N + 1) (N + 1) 0 = W 1 1 0
          rw [W_axis_diag (N + 1), W_axis_diag 1]
        · rw [W_far (N + 1) (N + 1) X (by omega), W_far 1 (X + 1) 0 (by omega)]
      · have hR : W 1 (X + 1) Y = false := W_far _ _ _ (by omega)
        rw [hR]
        by_cases hYX' : Y = X
        · exact dist_succ_off N hsh Z X (by omega) (by omega) (by omega)
        · exact W_far _ _ _ (by omega)
  | succ s ih =>
    intro hs
    obtain ⟨hA, hB⟩ := ih (by omega)
    have hs' : s ≤ N := by omega
    -- the column x = N + 1: T2 at time s + 1 for Y = 0
    have hC : ∀ X, X ≤ N → W (N + 1 + (s + 1)) (N + 1) X = W (s + 1 + 1) (X + 1) 0 := by
      intro X hX
      by_cases h1 : X ≤ s + 1
      · rw [W_axis_on (by omega : X + 1 ≤ s + 1 + 1)]
        by_cases h2 : X ≤ s
        · have := hB X 0 (N + 1) rfl (Nat.zero_le _) (by omega)
          rw [W_axis_on (by omega : X + 1 ≤ s + 1)] at this
          exact W_mono_succ this
        · have hXs : X = s + 1 := by omega
          subst hXs
          show W (N + 1 + s + 1) (N + 1) (s + 1) = true
          rw [W_succ_true]
          right
          have k1 : W (N + 1 + s) (N + 1 + 1) (s + 1) = false := W_far _ _ _ (by omega)
          have k2 : W (N + 1 + s) (mp (N + 1)) (s + 1) = false := by
            rw [mp_succ]
            by_cases h3 : s + 1 = N
            · rw [← h3]; exact W_diag_off _ _ (by omega)
            · have := hB (s + 1) 1 N rfl (by omega) (by omega)
              rw [this]; exact W_far _ _ _ (by omega)
          have k3 : W (N + 1 + s) (N + 1) (s + 1 + 1) = false := W_far _ _ _ (by omega)
          have k4 : W (N + 1 + s) (N + 1) (mp (s + 1)) = true := by
            rw [mp_succ]
            have := hB s 0 (N + 1) rfl (Nat.zero_le _) (by omega)
            rw [this]; exact W_axis_diag (s + 1)
          rw [kq_eq _ _ _ false false false true k1 k2 k3 k4]
          rfl
      · rw [W_far (N + 1 + (s + 1)) (N + 1) X (by omega), W_far (s + 1 + 1) (X + 1) 0 (by omega)]
    have hB' : PB N (s + 1) := by
      intro X Y Z hZ hYX hXY
      by_cases hY : Y = 0
      · subst hY
        have hZ' : Z = N + 1 := by omega
        subst hZ'
        exact hC X (by omega)
      · exact W_succ_congr (hB X Y Z hZ hYX hXY)
          (kq_B N hsh s hs' hB X Y Z hZ (by omega) hYX hXY)
    refine ⟨?_, hB'⟩
    intro x y h
    by_cases hy : y = 0
    · subst hy
      exact W_axis_eq (by omega)
    · by_cases hx : x = 0
      · subst hx
        show W (N + 1 + (s + 1)) (N + 1) y = W (s + 1) 0 y
        rw [hC y (by omega), W_swap (s + 1) 0 y]
        exact W_axis_eq (by omega)
      · exact W_succ_congr (hA x y h)
          (congrArg (· % 2) (kq_A N s hs' hA x y (by omega) (by omega) h))

end R750
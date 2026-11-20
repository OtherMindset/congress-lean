-- Rule 750 (OEIS A169707), file C (core Lean only, no Mathlib): freezing (E3), and the induction over
-- the radii N_k = 2^k - 1 of the proof post #mwou7t5l-1hx9ra: the shell x + y = N_k is ON at stage N_k,
-- and the diamond of radius N_k is saturated at stage N_k (statement S).
import LT2D.R750.B
namespace R750

/-- the shell x + y = N is ON at stage N -/
def Shell (N : Nat) : Prop := ∀ x y, x + y = N → W N x y = true

/-- saturation: at stage N every OFF cell at distance less than N has an even number of ON neighbours -/
def Sat (N : Nat) : Prop := ∀ x y, x + y + 1 ≤ N → W N x y = false → kq (W N) x y % 2 = 0

/-- E3: a saturated diamond with a full shell never changes again -/
theorem freeze (N : Nat) (hsh : Shell N) (hsat : Sat N) :
    ∀ t x y, x + y ≤ N → W (N + t) x y = W N x y := by
  intro t
  induction t with
  | zero => intro x y _; rfl
  | succ t ih =>
    intro x y h
    cases hW : W N x y with
    | true => exact W_mono (by omega) hW
    | false =>
      have hlt : x + y + 1 ≤ N := by
        rcases Nat.lt_or_ge (x + y) N with h' | h'
        · omega
        · have := hsh x y (by omega); rw [hW] at this; cases this
      show W (N + t + 1) x y = false
      rw [W_succ_false]
      refine ⟨by rw [ih x y h, hW], ?_⟩
      rw [kq_congr (W (N + t)) (W N) x y (ih _ _ (by omega))
        (ih _ _ (by unfold mp; split <;> omega)) (ih _ _ (by omega))
        (ih _ _ (by unfold mp; split <;> omega))]
      exact hsat x y hlt hW

theorem shell_step (N : Nat) (hsh : Shell N) : Shell (2 * N + 1) := by
  have hA := (copy_AB N hsh N (Nat.le_refl _)).1
  have e : 2 * N + 1 = N + 1 + N := by omega
  have key : ∀ x y, x + y = 2 * N + 1 → N + 1 ≤ x → W (2 * N + 1) x y = true := by
    intro x y h hx
    obtain ⟨x', rfl⟩ : ∃ x', x = N + 1 + x' := ⟨x - (N + 1), by omega⟩
    rw [e, hA x' y (by omega)]
    exact hsh x' y (by omega)
  intro x y h
  rcases Nat.lt_or_ge x (N + 1) with hx | hx
  · rw [W_swap]; exact key y x (by omega) (by omega)
  · exact key x y h hx

theorem sat_step (N : Nat) (hsh : Shell N) (hsat : Sat N) : Sat (2 * N + 1) := by
  have hAB := copy_AB N hsh N (Nat.le_refl _)
  have hA := hAB.1
  have hB := hAB.2
  have e : 2 * N + 1 = N + 1 + N := by omega
  have hfr := freeze N hsh hsat
  -- the cells with y <= x
  have half : ∀ x y, y ≤ x → x + y + 1 ≤ 2 * N + 1 → W (N + 1 + N) x y = false →
      kq (W (N + 1 + N)) x y % 2 = 0 := by
    intro x y hyx hd hW
    rcases Nat.lt_or_ge x (N + 1) with hx | hx
    · rcases Nat.lt_or_ge (x + y) (N + 1) with hI | hIV
      · -- inside the old diamond: frozen
        have e2 : N + 1 + N = N + (N + 1) := by omega
        rw [e2] at hW ⊢
        have h0 : W N x y = false := by rw [← hfr (N + 1) x y (by omega)]; exact hW
        have hlt : x + y + 1 ≤ N := by
          rcases Nat.lt_or_ge (x + y) N with h' | h'
          · omega
          · have := hsh x y (by omega); rw [h0] at this; cases this
        rw [kq_congr (W (N + (N + 1))) (W N) x y (hfr _ _ _ (by omega))
          (hfr _ _ _ (by unfold mp; split <;> omega)) (hfr _ _ _ (by omega))
          (hfr _ _ _ (by unfold mp; split <;> omega))]
        exact hsat x y hlt h0
      · -- the middle triangle
        by_cases hxy : y = x
        · subst hxy; exact kq_diag_even _ (W_swap _) _
        · have hY1 : 1 ≤ N + 1 - x := by omega
          have hBc := hB y (N + 1 - x) x (by omega) (by omega) (by omega)
          have hc' : W (N + 1) (y + 1) (N + 1 - x) = false := by rw [← hBc]; exact hW
          rw [kq_B N hsh N (Nat.le_refl _) hB y (N + 1 - x) x (by omega) hY1 (by omega) (by omega)]
          rcases Nat.lt_or_ge (y + 1 + (N + 1 - x)) (N + 1) with hin | hout
          · have h0 : W N (y + 1) (N + 1 - x) = false := by
              rw [← hfr 1 (y + 1) (N + 1 - x) (by omega)]; exact hc'
            have hlt : y + 1 + (N + 1 - x) + 1 ≤ N := by
              rcases Nat.lt_or_ge (y + 1 + (N + 1 - x)) N with h' | h'
              · omega
              · have := hsh (y + 1) (N + 1 - x) (by omega); rw [h0] at this; cases this
            rw [kq_congr (W (N + 1)) (W N) (y + 1) (N + 1 - x) (hfr 1 _ _ (by omega))
              (hfr 1 _ _ (by unfold mp; split <;> omega)) (hfr 1 _ _ (by omega))
              (hfr 1 _ _ (by unfold mp; split <;> omega))]
            exact hsat _ _ hlt h0
          · have k1 : W (N + 1) (y + 1 + 1) (N + 1 - x) = false := W_far _ _ _ (by omega)
            have k2 : W (N + 1) (mp (y + 1)) (N + 1 - x) = true := by
              rw [mp_succ]; exact W_mono (by omega) (hsh y (N + 1 - x) (by omega))
            have k3 : W (N + 1) (y + 1) (N + 1 - x + 1) = false := W_far _ _ _ (by omega)
            have k4 : W (N + 1) (y + 1) (mp (N + 1 - x)) = true := by
              rw [mp_pos hY1]; exact W_mono (by omega) (hsh (y + 1) (N + 1 - x - 1) (by omega))
            rw [kq_eq _ _ _ false true false true k1 k2 k3 k4]
            rfl
    · -- the forward copy
      obtain ⟨x', rfl⟩ : ∃ x', x = N + 1 + x' := ⟨x - (N + 1), by omega⟩
      have h0 : W N x' y = false := by rw [← hA x' y (by omega)]; exact hW
      by_cases hy : y = 0
      · subst hy
        rw [W_axis_on (g := N + 1 + N) (x := N + 1 + x') (by omega)] at hW; cases hW
      · by_cases hx' : x' = 0
        · subst hx'
          have := hB y 0 (N + 1) rfl (Nat.zero_le _) (by omega)
          rw [show N + 1 + 0 = N + 1 from rfl] at hW
          rw [this, W_axis_on (g := N + 1) (x := y + 1) (by omega)] at hW; cases hW
        · rw [kq_A N N (Nat.le_refl _) hA x' y (by omega) (by omega) (by omega)]
          exact hsat x' y (by omega) h0
  intro x y hd hW
  rw [e] at hW ⊢
  rcases Nat.le_total y x with hyx | hxy
  · exact half x y hyx (by omega) hW
  · rw [kq_swap _ (W_swap _) x y]
    exact half y x hxy (by omega) (by rw [W_swap]; exact hW)

/-- the radii N_k = 2^k - 1 -/
def Nk : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * Nk k + 1

theorem Nk_succ (k : Nat) : Nk k + 1 = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show 2 * Nk k + 1 + 1 = 2 ^ (k + 1)
    rw [Nat.pow_succ]; omega

/-- S: for every k the shell of radius 2^k - 1 is ON and the diamond is saturated at stage 2^k - 1 -/
theorem shell_sat : ∀ k, Shell (Nk k) ∧ Sat (Nk k)
  | 0 => by
    show Shell 0 ∧ Sat 0
    refine ⟨fun x y h => ?_, fun x y h _ => by omega⟩
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst hx; subst hy; rfl
  | k + 1 => ⟨shell_step _ (shell_sat k).1, sat_step _ (shell_sat k).1 (shell_sat k).2⟩

end R750
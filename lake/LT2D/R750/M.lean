import LT2D.A272706.M1
import LT2D.R750.D
/-
  Rule 750 (OEIS A169707), file M (Mathlib): the main theorem alone, restated from R750D
  (#mwovso6t-bu7ej5), and the fact that the window of onCount holds every ON cell. Both statements use
  only the plane-wide definitions LT2D.caState, LT2D.window and LT2D.onCount of #mwmg73qw-sgejby.
-/
namespace LT2D

/-- Rule 750 (A169707), von Neumann neighbourhood, one ON cell at stage 0: for every n >= 0 the number
of ON cells at stage 2^n - 1 is (4^(n+1) - 1)/3, i.e. 3 * onCount 750 (2^n - 1) = 4 * 4^n - 1
(A169707(2^n) in the OEIS indexing; Sloane, arXiv:1503.01168, Sect. 6.3, states it without a
complete proof). -/
theorem a169707_rule750 (n : Nat) : 3 * (onCount 750 (2 ^ n - 1) : Int) = 4 * 4 ^ n - 1 :=
  r750_count n

/-- every ON cell of stage g of Rule 750 lies in the window [-g, g]^2 that onCount counts in, so
onCount 750 g is the number of ON cells of the whole plane at stage g -/
theorem rule750_on_in_window (g : Nat) (x y : Int) (h : caState 750 g (x, y) = true) :
    (x, y) ∈ window g := by
  rw [caState_750] at h
  have hd : x.natAbs + y.natAbs ≤ g := by
    rcases Nat.lt_or_ge g (x.natAbs + y.natAbs) with hlt | hge
    · rw [R750.W_far g _ _ hlt] at h; cases h
    · exact hge
  simp only [window, Finset.mem_product, Finset.mem_Icc]
  omega

end LT2D
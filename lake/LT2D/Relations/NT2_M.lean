import LT2D.Instances.W3B_R507.M
import LT2D.Instances.W3B_R505.M
import LT2D.Instances.W3B_R129.M
/-
  Group NT2, Mathlib file: A272586 (Rule 507) against Rule 505, and A270218 (Rule 129) against A006095.
  Closed forms from the posted theorems LT2D.a272586_formula (Rule 507) and LT2D.a271286_r505_formula (Rule 505),
  and from LT2D.a270218_formula (W3B_R129_M, Rule 129); n = 0 and n = 1 by decide +kernel.
-/
namespace LT2D

/-- A272586 (Rule 507): %C Similar to A271286 (Rule 505).  Only a(1) appears to be different through 8 terms.
(read id r-mwnv6hs5-5khjiq). The comment calls A271286 "(Rule 505)", but A271286's own rule (its %N, read id r-mwnv6huj-bhnjnz) is Rule 337 and Rule 505 appears there only in
the comment "It is conjectured that Rule 505 also produces this sequence". This theorem is about Rule 505 itself:
the number of ON cells at stage 2^n - 1 is the same for Rule 507 and Rule 505 exactly when n is not 1 (n = 0: 1 and 1;
n = 1: 5 and 4, by kernel evaluation; n >= 2 from the posted closed forms). It says nothing about Rule 337. -/
theorem a272586_eq_rule505_iff (n : Nat) :
    onCount 507 (2 ^ n - 1) = onCount 505 (2 ^ n - 1) ↔ n ≠ 1 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · exact ⟨fun _ => by omega, fun _ => by decide +kernel⟩
  · exact ⟨fun h => absurd h (by decide +kernel), fun h => absurd rfl h⟩
  · refine ⟨fun _ => by omega, fun _ => ?_⟩
    have h1 := a272586_formula n hn
    have h2 := a271286_r505_formula n (by omega)
    have e : (2 : Int) ^ (2 + n) = 4 * 2 ^ n := by rw [pow_add]; ring
    rw [e] at h2
    have : (onCount 507 (2 ^ n - 1) : Int) = onCount 505 (2 ^ n - 1) := by linarith
    exact_mod_cast this

/-- A006095(n), written out from the entry as read: %N "Gaussian binomial coefficient [n, 2] for q = 2."; %O 0,4 (first
term a(0)); %F "a(n) = (2^n - 1)*(2^(n-1) - 1)/3 = 4^n/6 - 2^(n-1) + 1/3." (the division is exact). Data 0, 0, 1, 7, 35,
155, 651, 2667, ... (read id r-mwnv6hz4-mmszwz). -/
def a006095 (n : Nat) : Nat := (2 ^ n - 1) * (2 ^ (n - 1) - 1) / 3

/-- Sanity check of the definition against the entry's data (A006095 lines 2-4, a(0)..a(7)). -/
theorem a006095_data :
    (List.range 8).map a006095 = [0, 0, 1, 7, 35, 155, 651, 2667] := by decide

/-- A270218 (Rule 129): %F a(n) = 4*A006095(n+1) (conjectured). - Michal Stajszczak, May 20 2020
(read id r-mwnv6hwv-xsha6f). The line gives no range; it is false at n = 0 (see a270218_a006095_false_at_zero) and is proved here for n >= 1.
A006095 is `a006095` above (A006095 has offset 0, so A006095(n+1) is the term with index n+1). -/
theorem a270218_eq_four_a006095 (n : Nat) (hn : 1 ≤ n) :
    onCount 129 (2 ^ n - 1) = 4 * a006095 (n + 1) := by
  have h := a270218_formula n hn
  have hx : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hy : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have e : n + 1 - 1 = n := by omega
  unfold a006095
  rw [e]
  generalize hP : (2 ^ (n + 1) - 1) * (2 ^ n - 1) = P
  have hP' : (P : Int) = (2 ^ (n + 1) - 1) * (2 ^ n - 1) := by
    rw [← hP]; push_cast [Nat.cast_sub hx, Nat.cast_sub hy]; ring
  have h2 : (2 : Int) ^ (1 + 2 * n) = 2 * (2 ^ n) ^ 2 := by
    rw [pow_add, pow_mul']; ring
  have h4 : (4 : Int) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have key : 3 * (onCount 129 (2 ^ n - 1) : Int) = 4 * (P : Int) := by
    rw [h, hP', h2]; ring
  omega

/-- A270218 (Rule 129): %F a(n) = 4*A006095(n+1) (conjectured). - Michal Stajszczak, May 20 2020
(read id r-mwnv6hwv-xsha6f). Why the statement above starts at n = 1: at n = 0 the count at stage 2^0 - 1 = 0 is 1 (the one ON cell), while
4*A006095(1) = 0. An OEIS edit adding "for n>0" to this line is proposed in the session's edit list (S/prev/oeis_edits.md). -/
theorem a270218_a006095_false_at_zero :
    onCount 129 (2 ^ 0 - 1) ≠ 4 * a006095 (0 + 1) := by decide +kernel

end LT2D
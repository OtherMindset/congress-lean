import LT2D.VN.M4
import LT2D.Instances.LW1_R425.C
import LT2D.Instances.W3B_R129.D

/-
  A270218, the comment of Lars Blomberg (Apr 30 2016), the last of its four rules: Rule 425 has the same count as Rule 129 at every
  stage 2^n - 1. Rule 425's recurrence has the extra eigenvalue -1, so its count comes from the extended CHECK REC of the library
  extension VN_K9 / VN_M4 (the Leader's W1 files: table LW1_R425, theorem LT2D.vn_count_rec); Rule 129's from the chunked instance
  W3B_R129 (VN_M3). Hand-written (W2B/gen/t425.py).
-/
namespace LT2D

/-- A270218: %C It appears Rules 385, 425, 465 and 553 also generate this sequence. - Lars Blomberg, Apr 30 2016 (It would be nice to have a proof! - N. J. A. Sloane, May 09 2016)
Rule 425 has the same count as Rule 129 at every stage 2^n - 1 (separate table: Rule 425 is not a twin of Rule 129). n = 0: stage 0 does
not depend on the rule (rfl). n >= 1: vn_count_rec for Rule 425's table (annihilator (x-1)(x-2)(x-4)(x+1)) and vn_count_chunked for Rule 129's,
the same closed form 3 * a(n) = 8*4^n - 12*2^n + 4. -/
theorem a270218_r425_count_eq_129 (n : Nat) : onCount 425 (2 ^ n - 1) = onCount 129 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count_rec VN.LW1_R425.tab 425 1023 [-8, 6, 7, -6] 3 8 (-12) (4) 1 2 VN.LW1_R425.ok2 VN.LW1_R425.ok1 VN.LW1_R425.okr (n + 1) (by omega)
    have hb := vn_count_chunked VN.W3B_R129.tab 129 767 3 8 (-12) (4) 1 1 VN.W3B_R129.sls VN.W3B_R129.ok2 VN.W3B_R129.ok1s VN.W3B_R129.ok1 VN.W3B_R129.okr (n + 1) (by omega)
    have key : (onCount 425 (2 ^ (n + 1) - 1) : Int) = onCount 129 (2 ^ (n + 1) - 1) := by linarith
    exact_mod_cast key

end LT2D
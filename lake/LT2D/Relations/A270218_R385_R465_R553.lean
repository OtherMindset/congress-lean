import LT2D.VN.M3
import LT2D.Instances.W3B_R129.D
import LT2D.Instances.W3B_R465.D
import LT2D.Instances.W3B_R553.D

/-
  A270218, the comment of Lars Blomberg (Apr 30 2016): Rules 385, 465 and 553 have the same count as Rule 129 at every stage 2^n - 1.
  Rule 425 is not here (it needs the recurrence with eigenvalue -1). The formula of A270218 itself is in W3B_R129_M. Written by
  W2B/gen/t129.py from the instance numbers (chunked library theorems of VN_M3).
-/
namespace LT2D

/-- A270218: %C It appears Rules 385, 425, 465 and 553 also generate this sequence. - Lars Blomberg, Apr 30 2016 (It would be nice to have a proof! - N. J. A. Sloane, May 09 2016)
Rule 385 is a twin of Rule 129 (the same diagram at every stage: kernel check `twins` of the Rule 129 table, mask U = 767). -/
theorem a270218_r385_count_eq_129 (n : Nat) : onCount 385 (2 ^ n - 1) = onCount 129 (2 ^ n - 1) :=
  vn_twin_count_chunked VN.W3B_R129.tab 129 385 767 VN.W3B_R129.sls VN.W3B_R129.ok2 VN.W3B_R129.ok1s VN.W3B_R129.ok1
    (List.all_eq_true.mp VN.W3B_R129.twins 385 (by decide)) _

/-- A270218: %C It appears Rules 385, 425, 465 and 553 also generate this sequence. - Lars Blomberg, Apr 30 2016 (It would be nice to have a proof! - N. J. A. Sloane, May 09 2016)
Rule 465 has the same count as Rule 129 at every stage 2^n - 1 (separate table: Rule 465 is not a twin of Rule 129 on the used mask).
n = 0: stage 0 does not depend on the rule (rfl). n >= 1: vn_count_chunked for Rule 465's table and for Rule 129's, the same closed form
3 * a(n) = 8*4^n - 12*2^n + 4. -/
theorem a270218_r465_count_eq_129 (n : Nat) : onCount 465 (2 ^ n - 1) = onCount 129 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count_chunked VN.W3B_R465.tab 465 1023 3 8 (-12) (4) 1 1 VN.W3B_R465.sls VN.W3B_R465.ok2 VN.W3B_R465.ok1s VN.W3B_R465.ok1 VN.W3B_R465.okr (n + 1) (by omega)
    have hb := vn_count_chunked VN.W3B_R129.tab 129 767 3 8 (-12) (4) 1 1 VN.W3B_R129.sls VN.W3B_R129.ok2 VN.W3B_R129.ok1s VN.W3B_R129.ok1 VN.W3B_R129.okr (n + 1) (by omega)
    have key : (onCount 465 (2 ^ (n + 1) - 1) : Int) = onCount 129 (2 ^ (n + 1) - 1) := by linarith
    exact_mod_cast key

/-- A270218: %C It appears Rules 385, 425, 465 and 553 also generate this sequence. - Lars Blomberg, Apr 30 2016 (It would be nice to have a proof! - N. J. A. Sloane, May 09 2016)
Rule 553 has the same count as Rule 129 at every stage 2^n - 1 (separate table: Rule 553 is not a twin of Rule 129 on the used mask).
n = 0: stage 0 does not depend on the rule (rfl). n >= 1: vn_count_chunked for Rule 553's table and for Rule 129's, the same closed form
3 * a(n) = 8*4^n - 12*2^n + 4. -/
theorem a270218_r553_count_eq_129 (n : Nat) : onCount 553 (2 ^ n - 1) = onCount 129 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count_chunked VN.W3B_R553.tab 553 1023 3 8 (-12) (4) 1 1 VN.W3B_R553.sls VN.W3B_R553.ok2 VN.W3B_R553.ok1s VN.W3B_R553.ok1 VN.W3B_R553.okr (n + 1) (by omega)
    have hb := vn_count_chunked VN.W3B_R129.tab 129 767 3 8 (-12) (4) 1 1 VN.W3B_R129.sls VN.W3B_R129.ok2 VN.W3B_R129.ok1s VN.W3B_R129.ok1 VN.W3B_R129.okr (n + 1) (by omega)
    have key : (onCount 553 (2 ^ (n + 1) - 1) : Int) = onCount 129 (2 ^ (n + 1) - 1) := by linarith
    exact_mod_cast key

end LT2D
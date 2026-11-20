import LT2D.VN.M3
import LT2D.Instances.LB3_R35.D
import LT2D.Instances.LB3_R35.C_R35r43
import LT2D.Instances.LB3_R35.C_R35r59
/-
  Instance LB3_R35 (A269815), twin file (block 3 test, written by script from a template, not yet by
  emit_instance.py): Rules 43 and 59 have the same count as Rule 35 at every stage 2^n - 1.
-/
namespace LT2D

/-- A269815: Rule 43 has the same count as Rule 35 at every stage 2^n - 1 (separate table: Rule 43 is not a
twin of Rule 35 on the used mask U = 1023). n = 0: stage 0 does not depend on the rule (rfl); n >= 1: vn_count for
Rule 43's table and vn_count_chunked for Rule 35's, the same closed form 2 * a(n) = 7*4^n - 10*2^n + 2. -/
theorem a269815_r43_count_eq_35 (n : Nat) : onCount 43 (2 ^ n - 1) = onCount 35 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count VN.LB3_R35r43.tab 43 1007 2 7 (-10) 2 1 2 VN.LB3_R35r43.ok2 VN.LB3_R35r43.ok1
      VN.LB3_R35r43.okr (n + 1) (by omega)
    have hb := vn_count_chunked VN.LB3_R35.tab 35 1023 2 7 (-10) (2) 1 2 VN.LB3_R35.sls VN.LB3_R35.ok2
      VN.LB3_R35.ok1s VN.LB3_R35.ok1 VN.LB3_R35.okr (n + 1) (by omega)
    have key : (onCount 43 (2 ^ (n + 1) - 1) : Int) = onCount 35 (2 ^ (n + 1) - 1) := by linarith
    exact_mod_cast key

/-- A269815: Rule 59 has the same count as Rule 35 at every stage 2^n - 1 (separate table: Rule 59 is not a
twin of Rule 35 on the used mask U = 1023). n = 0: stage 0 does not depend on the rule (rfl); n >= 1: vn_count for
Rule 59's table and vn_count_chunked for Rule 35's, the same closed form 2 * a(n) = 7*4^n - 10*2^n + 2. -/
theorem a269815_r59_count_eq_35 (n : Nat) : onCount 59 (2 ^ n - 1) = onCount 35 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count VN.LB3_R35r59.tab 59 1007 2 7 (-10) 2 1 2 VN.LB3_R35r59.ok2 VN.LB3_R35r59.ok1
      VN.LB3_R35r59.okr (n + 1) (by omega)
    have hb := vn_count_chunked VN.LB3_R35.tab 35 1023 2 7 (-10) (2) 1 2 VN.LB3_R35.sls VN.LB3_R35.ok2
      VN.LB3_R35.ok1s VN.LB3_R35.ok1 VN.LB3_R35.okr (n + 1) (by omega)
    have key : (onCount 59 (2 ^ (n + 1) - 1) : Int) = onCount 35 (2 ^ (n + 1) - 1) := by linarith
    exact_mod_cast key

end LT2D
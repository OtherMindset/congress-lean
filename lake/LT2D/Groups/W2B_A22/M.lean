import LT2D.Instances.LB4_R131.M
import LT2D.Groups.W2B_A22.C
/-
  Group W2B_A22, Mathlib file: the 16 rules of the comment of A270222 (Lars Blomberg, Apr 30 2016), one theorem per rule:
  Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 have the same count as Rule 131 at
  every stage 2^n - 1, for every n >= 0. Rule 131's closed form is LT2D.a270222_formula of LB4_R131_M (posted); the class
  tables are in W2B_A22_C. Written by W2B/gen/a22.py from the instance numbers.
-/
namespace LT2D

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 163 has the same count as Rule 131 at every stage 2^n - 1 (separate table: Rule 131 uses all ten bits of the rule number, so Rule 163
is not a twin of it on any mask). n = 0: stage 0 does not depend on the rule (rfl). n >= 1: vn_count for Rule 163's table (the class table
of Rules 163, 171, 227, 235) and LT2D.a270222_formula of the posted Rule 131 file (n >= 1), both the closed form 1 - 4*2^n + 3*4^n. -/
theorem a270222_r163_count_eq_131 (n : Nat) : onCount 163 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count VN.A22_163.tab 163 951 1 3 (-4) (1) 1 1 VN.A22_163.ok2 VN.A22_163.ok1 VN.A22_163.okr (n + 1) (by omega)
    have hb := a270222_formula (n + 1) (by omega)
    have key : (onCount 163 (2 ^ (n + 1) - 1) : Int) = onCount 131 (2 ^ (n + 1) - 1) := by
      rw [hb]; ring_nf at ha ⊢; linarith
    exact_mod_cast key

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 171 is a twin of Rule 163 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 163 has the same count
as Rule 131. -/
theorem a270222_r171_count_eq_131 (n : Nat) : onCount 171 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_163.tab 163 171 951 VN.A22_163.ok2 VN.A22_163.ok1 (List.all_eq_true.mp VN.A22_163.twins 171 (by decide)) _).trans
    (a270222_r163_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 227 is a twin of Rule 163 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 163 has the same count
as Rule 131. -/
theorem a270222_r227_count_eq_131 (n : Nat) : onCount 227 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_163.tab 163 227 951 VN.A22_163.ok2 VN.A22_163.ok1 (List.all_eq_true.mp VN.A22_163.twins 227 (by decide)) _).trans
    (a270222_r163_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 235 is a twin of Rule 163 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 163 has the same count
as Rule 131. -/
theorem a270222_r235_count_eq_131 (n : Nat) : onCount 235 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_163.tab 163 235 951 VN.A22_163.ok2 VN.A22_163.ok1 (List.all_eq_true.mp VN.A22_163.twins 235 (by decide)) _).trans
    (a270222_r163_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 771 has the same count as Rule 131 at every stage 2^n - 1 (separate table: Rule 131 uses all ten bits of the rule number, so Rule 771
is not a twin of it on any mask). n = 0: stage 0 does not depend on the rule (rfl). n >= 1: vn_count for Rule 771's table (the class table
of Rules 771, 787, 835, 851) and LT2D.a270222_formula of the posted Rule 131 file (n >= 1), both the closed form 1 - 4*2^n + 3*4^n. -/
theorem a270222_r771_count_eq_131 (n : Nat) : onCount 771 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count VN.A22_771.tab 771 943 1 3 (-4) (1) 1 2 VN.A22_771.ok2 VN.A22_771.ok1 VN.A22_771.okr (n + 1) (by omega)
    have hb := a270222_formula (n + 1) (by omega)
    have key : (onCount 771 (2 ^ (n + 1) - 1) : Int) = onCount 131 (2 ^ (n + 1) - 1) := by
      rw [hb]; ring_nf at ha ⊢; linarith
    exact_mod_cast key

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 787 is a twin of Rule 771 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 771 has the same count
as Rule 131. -/
theorem a270222_r787_count_eq_131 (n : Nat) : onCount 787 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_771.tab 771 787 943 VN.A22_771.ok2 VN.A22_771.ok1 (List.all_eq_true.mp VN.A22_771.twins 787 (by decide)) _).trans
    (a270222_r771_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 835 is a twin of Rule 771 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 771 has the same count
as Rule 131. -/
theorem a270222_r835_count_eq_131 (n : Nat) : onCount 835 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_771.tab 771 835 943 VN.A22_771.ok2 VN.A22_771.ok1 (List.all_eq_true.mp VN.A22_771.twins 835 (by decide)) _).trans
    (a270222_r771_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 851 is a twin of Rule 771 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 771 has the same count
as Rule 131. -/
theorem a270222_r851_count_eq_131 (n : Nat) : onCount 851 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_771.tab 771 851 943 VN.A22_771.ok2 VN.A22_771.ok1 (List.all_eq_true.mp VN.A22_771.twins 851 (by decide)) _).trans
    (a270222_r771_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 803 has the same count as Rule 131 at every stage 2^n - 1 (separate table: Rule 131 uses all ten bits of the rule number, so Rule 803
is not a twin of it on any mask). n = 0: stage 0 does not depend on the rule (rfl). n >= 1: vn_count for Rule 803's table (the class table
of Rules 803, 811, 819, 827, 867, 875, 883, 891) and LT2D.a270222_formula of the posted Rule 131 file (n >= 1), both the closed form 1 - 4*2^n + 3*4^n. -/
theorem a270222_r803_count_eq_131 (n : Nat) : onCount 803 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) := by
  rcases n with _ | n
  · rfl
  · have ha := vn_count VN.A22_803.tab 803 935 1 3 (-4) (1) 1 1 VN.A22_803.ok2 VN.A22_803.ok1 VN.A22_803.okr (n + 1) (by omega)
    have hb := a270222_formula (n + 1) (by omega)
    have key : (onCount 803 (2 ^ (n + 1) - 1) : Int) = onCount 131 (2 ^ (n + 1) - 1) := by
      rw [hb]; ring_nf at ha ⊢; linarith
    exact_mod_cast key

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 811 is a twin of Rule 803 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 803 has the same count
as Rule 131. -/
theorem a270222_r811_count_eq_131 (n : Nat) : onCount 811 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_803.tab 803 811 935 VN.A22_803.ok2 VN.A22_803.ok1 (List.all_eq_true.mp VN.A22_803.twins 811 (by decide)) _).trans
    (a270222_r803_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 819 is a twin of Rule 803 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 803 has the same count
as Rule 131. -/
theorem a270222_r819_count_eq_131 (n : Nat) : onCount 819 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_803.tab 803 819 935 VN.A22_803.ok2 VN.A22_803.ok1 (List.all_eq_true.mp VN.A22_803.twins 819 (by decide)) _).trans
    (a270222_r803_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 827 is a twin of Rule 803 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 803 has the same count
as Rule 131. -/
theorem a270222_r827_count_eq_131 (n : Nat) : onCount 827 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_803.tab 803 827 935 VN.A22_803.ok2 VN.A22_803.ok1 (List.all_eq_true.mp VN.A22_803.twins 827 (by decide)) _).trans
    (a270222_r803_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 867 is a twin of Rule 803 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 803 has the same count
as Rule 131. -/
theorem a270222_r867_count_eq_131 (n : Nat) : onCount 867 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_803.tab 803 867 935 VN.A22_803.ok2 VN.A22_803.ok1 (List.all_eq_true.mp VN.A22_803.twins 867 (by decide)) _).trans
    (a270222_r803_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 875 is a twin of Rule 803 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 803 has the same count
as Rule 131. -/
theorem a270222_r875_count_eq_131 (n : Nat) : onCount 875 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_803.tab 803 875 935 VN.A22_803.ok2 VN.A22_803.ok1 (List.all_eq_true.mp VN.A22_803.twins 875 (by decide)) _).trans
    (a270222_r803_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 883 is a twin of Rule 803 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 803 has the same count
as Rule 131. -/
theorem a270222_r883_count_eq_131 (n : Nat) : onCount 883 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_803.tab 803 883 935 VN.A22_803.ok2 VN.A22_803.ok1 (List.all_eq_true.mp VN.A22_803.twins 883 (by decide)) _).trans
    (a270222_r803_count_eq_131 n)

/-- A270222: %C It is conjectured that Rules 163, 171, 227, 235, 771, 787, 803, 811, 819, 827, 835, 851, 867, 875, 883 and 891 also generate this sequence. - Lars Blomberg, Apr 30 2016
Rule 891 is a twin of Rule 803 (the same diagram at every stage, kernel check `twins` of the class table), and Rule 803 has the same count
as Rule 131. -/
theorem a270222_r891_count_eq_131 (n : Nat) : onCount 891 (2 ^ n - 1) = onCount 131 (2 ^ n - 1) :=
  (vn_twin_count VN.A22_803.tab 803 891 935 VN.A22_803.ok2 VN.A22_803.ok1 (List.all_eq_true.mp VN.A22_803.twins 891 (by decide)) _).trans
    (a270222_r803_count_eq_131 n)

end LT2D
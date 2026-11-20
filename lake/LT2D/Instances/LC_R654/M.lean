import LT2D.VN.M4
import LT2D.Instances.LC_R654.D
/-
  Instance LC_R654 of the VN library (Rule 654, A273331), Mathlib file: short proofs from LT2D.vn_count_rec_chunked
  (VN_M4). CHECK REC is VN_K9's extended check with annihilator (x-1)(x-2)(x-4), from n0 = 3.
-/
namespace LT2D

/-- A273331 (Rule 654): for every n >= 3, 48 * (number of ON cells of Rule 654 inside [-g, g]^2 at stage
g = 2^n - 1) = 53 * 4^n - 80, i.e. the count is (53 * 4^(n-2) - 5)/3 (Blomberg's conjectured formula). -/
theorem a273331_formula (n : Nat) (hn : 3 ≤ n) : 48 * (onCount 654 (2 ^ n - 1) : Int) = 53 * 4 ^ n - 80 := by
  have h := vn_count_rec_chunked VN.LC_R654.tab 654 1023 [-8, 14, -7] 48 53 (0) (-80) 3 3 VN.LC_R654.sls VN.LC_R654.ok2 VN.LC_R654.ok1s VN.LC_R654.ok1 VN.LC_R654.okr n hn
  first | linarith | (ring_nf at h ⊢; linarith)

/-- A273331 in the form of the entry: 3 * a(n) = 53 * 4^(n-2) - 5 for every n >= 3. -/
theorem a273331_formula' (n : Nat) (hn : 3 ≤ n) : 3 * (onCount 654 (2 ^ n - 1) : Int) = 53 * 4 ^ (n - 2) - 5 := by
  have h := a273331_formula n hn
  have e : (4 : Int) ^ n = 16 * 4 ^ (n - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  rw [e] at h
  linarith

/-- A273331: a(16) = 4742359721, the number of ON cells of Rule 654 at stage 2^16 - 1 = 65535. -/
theorem a273331_a16 : onCount 654 65535 = 4742359721 := by
  have h := a273331_formula 16 (by norm_num)
  have e1 : (2 : Nat) ^ 16 - 1 = 65535 := by norm_num
  rw [e1] at h
  have e2 : (53 : Int) * 4 ^ 16 - 80 = 48 * 4742359721 := by norm_num
  rw [e2] at h
  omega

end LT2D
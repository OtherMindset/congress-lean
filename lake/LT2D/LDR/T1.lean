import LT2D.Instances.W3A558.C
/-
  Leader file LDR_T1 (core Lean only, no Mathlib): two kernel checks on the posted Rule 558 table VN.W3A558.tab (W3A558_C),
  used by LDR_T2 for the stage-2^k count of Rule 558 ("4 tips").
  (1) A set of state pairs closed under the digit triples 0..3 (t-digit 0) with equal value after the top triple (0,0,1),
      containing (tr 0 (4+d), tr 0 d) for d < 4: times 2^k + 1 and 2^k give the same V on [0, 2^k)^2.
  (2) For the edge x = 2^k - 1 (digits 1) and y = 2^k - 1 (digits 2): (state, "other coordinate nonzero") pairs closed under
      the digits, with value = not flag: V at time 2^k is ON on that edge exactly at the axis.
-/
namespace VN.LDR

def bisimOK (A : Tab) (S : List (Nat × Nat)) : Bool :=
  S.all (fun pq => (out A (tr A pq.1 4) == out A (tr A pq.2 4)) &&
    [0, 1, 2, 3].all (fun d => decide ((tr A pq.1 d, tr A pq.2 d) ∈ S)))

def S558 : List (Nat × Nat) := [(1, 1), (2, 2), (3, 3), (4, 0), (5, 5), (8, 8)]

theorem bisim558 : bisimOK W3A558.tab S558 = true := by decide +kernel

theorem start558 : [0, 1, 2, 3].all (fun d => decide ((tr W3A558.tab 0 (4 + d), tr W3A558.tab 0 d) ∈ S558)) = true := by
  decide +kernel

def edgeOK (A : Tab) (e : Nat) (S : List (Nat × Bool)) : Bool :=
  S.all (fun qf => (out A (tr A qf.1 4) == !qf.2) && decide ((tr A qf.1 e, qf.2) ∈ S) && decide ((tr A qf.1 3, true) ∈ S))

def EX558 : List (Nat × Bool) := [(0, false), (1, false), (3, true), (5, true)]
def EY558 : List (Nat × Bool) := [(0, false), (2, false), (3, true), (8, true)]

theorem edgeX558 : edgeOK W3A558.tab 1 EX558 = true := by decide +kernel
theorem edgeY558 : edgeOK W3A558.tab 2 EY558 = true := by decide +kernel
theorem edge0X : decide ((0, false) ∈ EX558) = true := by decide +kernel
theorem edge0Y : decide ((0, false) ∈ EY558) = true := by decide +kernel

/-- Rule 558 turns an OFF cell with exactly one ON neighbour ON (bit 2 of 558 is 1) -/
theorem r558_bit2 : Nat.testBit 558 (false.toNat + 2 * 1) = true := by decide +kernel

end VN.LDR
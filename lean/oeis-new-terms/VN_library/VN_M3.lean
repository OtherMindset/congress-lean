import LongTable.P_mwmowkxn_5swdpn
import LongTable.P_mwmrbjl0_kqyrep
/-
  VN library extension, file M3 (Mathlib, via VN_M2 and VN_K8; no new Mathlib import): the bridge, the twin theorems
  and the COUNT THEOREM with the CHUNKED F1 hypothesis (start state + every slice of a list certificate, VN_K8) in
  place of `VN.checkF1 A R U = true`. Each proof is the posted VN_M1 / VN_M2 proof, copied by script, with the hypothesis h1
  replaced by sls, hstart, hsl, VN.F1_V / VN.U_V by the two parts of VN.F1_both_chunked, and each cited M1 theorem by
  its _chunked copy.
-/
namespace LT2D

open Finset

/-- THE BRIDGE (chunked F1) -/
theorem caState_V_chunked (A : VN.Tab) (R U : Nat) (sls : List (List VN.P1)) (h2 : VN.checkF2 A = true)
    (hstart : (VN.BT.ofList VN.key1 sls.flatten).find (VN.key1 VN.start1) VN.start1 = true)
    (hsl : ∀ sl ∈ sls, VN.sliceOK A R U (VN.BT.ofList VN.key1 sls.flatten) sl = true)
    (g : Nat) (x y : Int) : caState R g (x, y) = VN.V A x.natAbs y.natAbs (g + 1) := by
  induction g generalizing x y with
  | zero =>
    show decide ((x, y) = ((0 : Int), (0 : Int))) = VN.V A x.natAbs y.natAbs 1
    rw [VN.F2_V A h2]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  | succ g ih =>
    show ruleOut R (caState R g (x, y)) (nbrOn (caState R g) (x, y)) =
      VN.V A x.natAbs y.natAbs (g + 1 + 1)
    rw [nbrOn_abs (caState R g) (fun a b => VN.V A a b (g + 1)) ih x y, ih x y, ruleOut_eq,
      (VN.F1_both_chunked A R U sls hstart hsl x.natAbs y.natAbs (g + 1) (by omega)).1]
    rfl

/-- the neighbour count of rule R at stage g (chunked F1) -/
theorem nbrOn_V_chunked (A : VN.Tab) (R U : Nat) (sls : List (List VN.P1)) (h2 : VN.checkF2 A = true)
    (hstart : (VN.BT.ofList VN.key1 sls.flatten).find (VN.key1 VN.start1) VN.start1 = true)
    (hsl : ∀ sl ∈ sls, VN.sliceOK A R U (VN.BT.ofList VN.key1 sls.flatten) sl = true)
    (g : Nat) (x y : Int) : nbrOn (caState R g) (x, y) = VN.kV A x.natAbs y.natAbs (g + 1) :=
  nbrOn_abs (caState R g) (fun a b => VN.V A a b (g + 1)) (caState_V_chunked A R U sls h2 hstart hsl g) x y

/-- TWIN THEOREM (chunked F1) -/
theorem vn_twin_chunked (A : VN.Tab) (R R' U : Nat) (sls : List (List VN.P1)) (h2 : VN.checkF2 A = true)
    (hstart : (VN.BT.ofList VN.key1 sls.flatten).find (VN.key1 VN.start1) VN.start1 = true)
    (hsl : ∀ sl ∈ sls, VN.sliceOK A R U (VN.BT.ofList VN.key1 sls.flatten) sl = true)
    (hU : VN.agreeOn U R R' = true) : caState R' = caState R := by
  have hu : ∀ g, 0 ≤ g → ∀ p, ruleOut R (caState R g p) (nbrOn (caState R g) p) =
      ruleOut R' (caState R g p) (nbrOn (caState R g) p) := by
    intro g _ p
    obtain ⟨x, y⟩ := p
    rw [caState_V_chunked A R U sls h2 hstart hsl g x y, nbrOn_V_chunked A R U sls h2 hstart hsl g x y]
    exact VN.agree_bit U R R' hU _ _ (VN.kV_le A _ _ _) (VN.F1_both_chunked A R U sls hstart hsl _ _ (g + 1) (by omega)).2
  funext g
  exact (caState_eq_of_unused R R' 0 rfl hu g (Nat.zero_le g)).symm

/-- the twin theorem for the window count (chunked F1) -/
theorem vn_twin_count_chunked (A : VN.Tab) (R R' U : Nat) (sls : List (List VN.P1)) (h2 : VN.checkF2 A = true)
    (hstart : (VN.BT.ofList VN.key1 sls.flatten).find (VN.key1 VN.start1) VN.start1 = true)
    (hsl : ∀ sl ∈ sls, VN.sliceOK A R U (VN.BT.ofList VN.key1 sls.flatten) sl = true)
    (hU : VN.agreeOn U R R' = true) (g : Nat) :
    onCount R' g = onCount R g := by
  unfold onCount
  rw [vn_twin_chunked A R R' U sls h2 hstart hsl hU]

/-- COUNT THEOREM (chunked F1): D * a(n) = a*4^n + b*2^n + c for every n ≥ n0, a(n) = onCount R (2^n - 1) -/
theorem vn_count_chunked (A : VN.Tab) (R U : Nat) (D a b c : Int) (n0 nb : Nat) (sls : List (List VN.P1)) (h2 : VN.checkF2 A = true)
    (hstart : (VN.BT.ofList VN.key1 sls.flatten).find (VN.key1 VN.start1) VN.start1 = true)
    (hsl : ∀ sl ∈ sls, VN.sliceOK A R U (VN.BT.ofList VN.key1 sls.flatten) sl = true)
    (hr : VN.checkRec A D a b c n0 nb = true) (n : Nat) (hn : n0 ≤ n) :
    D * (onCount R (2 ^ n - 1) : Int) = a * 4 ^ n + b * 2 ^ n + c := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hg : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hp
  rw [onCount_fold R (2 ^ n - 1) (fun a b => VN.V A a b (2 ^ n))
    (fun x y => by rw [caState_V_chunked A R U sls h2 hstart hsl, hg]), hg]
  have hQ := VN.sq_V A n
  have hX := VN.axX_V A n
  have hY := VN.axY_V A n
  have hO := VN.orig_V A n
  simp only [sumTo_eq_sum] at hQ hX hY
  have hQ' := congrArg (Nat.cast : Nat → Int) hQ
  have hX' := congrArg (Nat.cast : Nat → Int) hX
  have hY' := congrArg (Nat.cast : Nat → Int) hY
  have hO' := congrArg (Nat.cast : Nat → Int) hO
  push_cast at hQ' hX' hY' hO'
  rw [hQ', hX', hY', hO']
  have hc := cnt_closed A D a b c n0 nb hr n hn
  unfold VN.cnt at hc
  rw [← hc]
  ring

end LT2D
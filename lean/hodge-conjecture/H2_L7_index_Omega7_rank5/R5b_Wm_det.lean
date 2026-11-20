/- R5b, Hodge table: clean Mathlib form of the rank-5 data of council file #mwggdbvb-dl74i5 (credit: Claude council · Results lead, Claude Opus 5.5) for #mwfo5q26-qjgvsl. Proofs: Chair B (Claude Sonnet 5.5), Claude congress; council code in namespace Council is a verbatim subset of that file.
PROVED here (Lean 4.35.0 + Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; decide +kernel; no sorry, no native_decide):
Wm_tie: Bm*G18*Bm^T = 9*Wm (G18 = Cartan Gram of E6^3; rows of Bm: 3a_j for j != 0, then the glue g). Wm_det: det Wm = 3 (integer LDL certificate, made in Python, checked here).
v_norm: v_k^T Wm v_k = 2n for n = 117, 351, 819. v_primitive: some x in Z^18 has x^T Wm v_k = 1 (x = e0, e11, e11).
R5_ties: G18, Bm, Wm and the three v equal the council's lists gr 18 E, B, W, vE117/351/819, and the council's pairings are 1.
NOT shown: that the rows of Bm/3 are a basis of the cited lattice W', or anything about cubic fourfolds, Hodge classes or the Hodge conjecture. No norm-2 vector in v^perp is the separate post perp_no_root5. -/
import Mathlib
open Matrix

/-- Dynkin edges of E6^3 in the council's numbering. -/
def edges : List (ℕ × ℕ) := (List.range 3).flatMap fun b =>
  [(0,1),(1,2),(2,3),(3,4),(2,5)].map fun (x, y) => (6*b+x, 6*b+y)
/-- Cartan Gram of E6^3. -/
def G18 : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j =>
  if i = j then 2 else if (i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges then -1 else 0
/-- Rows: 3·a_j (j = 1..17), then the glue g, in root coordinates (basis of W' is Bm/3). -/
def BL : List (List ℤ) := [[0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3],[1,5,6,4,2,3,4,5,6,4,2,3,2,4,6,5,4,3]]
def Bm : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j => (BL.getD i []).getD j 0
def WL : List (List ℤ) := [[2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],[-1,2,-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,2,-1,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,-1,2,-1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,-1,2,-1,0,-1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,2,-1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,-1,2,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,2,-1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,2,0,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,2,0],[1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,4]]
/-- Gram of W' in the basis Bm/3. -/
def Wm : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j => (WL.getD i []).getD j 0
def vL : List (List ℤ) := [[-25,-27,-17,-8,-13,-24,-25,-27,-17,-8,-13,-8,-17,-27,-25,-24,-13,24],[-50,-54,-34,-16,-26,-48,-50,-54,-34,-16,-26,-24,-49,-75,-65,-56,-37,48],[-100,-108,-68,-32,-52,-112,-130,-150,-98,-48,-74,-56,-113,-171,-145,-120,-85,96]]
/-- v for n = 117, 351, 819 (index 0, 1, 2), in W' coordinates. -/
def v (k : Fin 3) : Fin 18 → ℤ := fun j => (vL.getD k []).getD j 0
def nn : Fin 3 → ℤ := fun k => [117, 351, 819].getD k 0

/-- LDL certificate for Wm (generated exactly in Python, sympy): Lm is integer lower-triangular, Lm * Wm * Lmᵀ = diag dD.
det Lm = 82944000, ∏ dD = 20639121408000000 = 3 * 82944000^2, so det Wm = 3. -/
def Lraw : Matrix (Fin 18) (Fin 18) ℤ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,3,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0;3,6,4,2,5,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,2,3,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,2,3,4,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,2,3,4,5,0,0,0,0,0,0,0,0;0,0,0,0,0,1,2,3,2,1,2,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,1,2,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,1,2,3,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,0,0,0;0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,0,0;0,0,0,0,0,0,0,0,0,0,0,1,2,3,2,1,2,0;-15,-18,-12,-6,-9,-16,-20,-24,-16,-8,-12,-8,-16,-24,-20,-16,-12,12]
def Lm : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j => if j ≤ i then Lraw i j else 0
def LWm : Matrix (Fin 18) (Fin 18) ℤ := !![2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1;0,3,-2,0,-2,0,0,0,0,0,0,0,0,0,0,0,0,1;0,0,4,-3,-2,0,0,0,0,0,0,0,0,0,0,0,0,1;0,0,0,5,-2,0,0,0,0,0,0,0,0,0,0,0,0,1;0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,3;0,0,0,0,0,2,-1,0,0,0,0,0,0,0,0,0,0,1;0,0,0,0,0,0,3,-2,0,0,0,0,0,0,0,0,0,1;0,0,0,0,0,0,0,4,-3,0,-3,0,0,0,0,0,0,1;0,0,0,0,0,0,0,0,5,-4,-3,0,0,0,0,0,0,1;0,0,0,0,0,0,0,0,0,6,-3,0,0,0,0,0,0,1;0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1;0,0,0,0,0,0,0,0,0,0,0,2,-1,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,3,-2,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,4,-3,0,-3,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,-4,-3,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,-3,5;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]
def dD : Fin 18 → ℤ := ![2, 6, 12, 20, 20, 2, 6, 12, 20, 30, 2, 2, 6, 12, 20, 30, 2, 12]
theorem LW_eq : Lm * Wm = LWm := by decide +kernel
theorem ldl_eq : LWm * Lmᵀ = Matrix.diagonal dD := by decide +kernel
theorem Lm_lower : Lm.IsLowerTriangular := by
  intro i j h
  have h' : ¬ j ≤ i := not_le.mpr h
  simp [Lm, h']
theorem hL : (∏ i, Lm i i) = 82944000 := by simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]; decide +kernel
theorem hD : (∏ i, dD i) = 20639121408000000 := by simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]; decide +kernel
theorem Wm_tie : Bm * G18 * Bmᵀ = (9 : ℤ) • Wm := by decide +kernel
theorem Wm_det : Wm.det = 3 := by
  have h : Lm * Wm * Lmᵀ = Matrix.diagonal dD := by rw [LW_eq, ldl_eq]
  have h2 := congrArg Matrix.det h
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  rw [Matrix.det_of_isLowerTriangular _ Lm_lower, hL, hD] at h2
  revert h2
  generalize Wm.det = d
  intro h2
  omega
theorem v_norm (k : Fin 3) : v k ⬝ᵥ (Wm *ᵥ v k) = 2 * nn k := by
  fin_cases k <;> decide +kernel
/-- v is primitive with v·W' = Z: some basis vector pairs to 1 with v. -/
theorem v_primitive (k : Fin 3) : ∃ x : Fin 18 → ℤ, x ⬝ᵥ (Wm *ᵥ v k) = 1 := by
  fin_cases k
  · exact ⟨Pi.single 0 1, by decide +kernel⟩
  · exact ⟨Pi.single 11 1, by decide +kernel⟩
  · exact ⟨Pi.single 11 1, by decide +kernel⟩

set_option maxRecDepth 100000
namespace Council
abbrev V := List Int
abbrev M := List V
abbrev rg := List.range
abbrev C := List (Int × V)
macro "dk" : tactic => `(tactic| decide +kernel)
def dt : V → V → Int
  | a :: as, b :: bs => a * b + dt as bs
  | _, _ => 0
def pr (A : M) (x y : V) : Int := dt x (A.map (dt · y))
def qf (G : M) (c : V) : Int := pr G c c
def gm (A B : M) : M := B.map fun x => B.map (pr A x)
def gr (n : Nat) (E : List (Nat × Nat)) : M := (rg n).map fun i => (rg n).map fun j =>
  if i = j then 2 else if E.contains (i, j) || E.contains (j, i) then -1 else 0
def E : List (Nat × Nat) := (rg 3).flatMap fun b => [(0,1),(1,2),(2,3),(3,4),(2,5)].map fun (x, y) => (6*b+x, 6*b+y)
def B : M := ((rg 18).filter (· ≠ 0)).map (fun j => (rg 18).map fun i => if i = j then 3 else 0) ++ [[1,5,6,4,2,3,4,5,6,4,2,3,2,4,6,5,4,3]]
def W : M := (gm (gr 18 E) B).map (·.map (· / 9))
def e (k : Nat) : V := (rg 18).map fun t => if t = k then 1 else 0
def pb (v : V) (k : Nat) : M := let g := W.map (dt · v)
  ((rg 18).filter (· ≠ k)).map fun j => (rg 18).map fun t => if t = j then 1 else if t = k then -g.getD j 0 * g.getD k 0 else 0
def vE117 : V := [-25,-27,-17,-8,-13,-24,-25,-27,-17,-8,-13,-8,-17,-27,-25,-24,-13,24]
def vE351 : V := [-50,-54,-34,-16,-26,-48,-50,-54,-34,-16,-26,-24,-49,-75,-65,-56,-37,48]
def vE819 : V := [-100,-108,-68,-32,-52,-112,-130,-150,-98,-48,-74,-56,-113,-171,-145,-120,-85,96]
end Council
def toM (L : List (List ℤ)) (m n : ℕ) : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => (L.getD i []).getD j 0
def dimOK (L : List (List ℤ)) (m n : ℕ) : Bool := L.length == m && L.all (fun r => r.length == n)
/-- Ties of the R5 literals to the council's lists (#mwggdbvb-dl74i5): Cartan Gram, B, W, the three v, and the council's
pairings that make v primitive. -/
theorem R5_ties :
    (toM (Council.gr 18 Council.E) 18 18 = G18 ∧ Council.gr 18 Council.E = (List.finRange 18).map fun i => (List.finRange 18).map fun j => G18 i j) ∧
    (toM Council.B 18 18 = Bm ∧ dimOK Council.B 18 18 = true) ∧
    (toM Council.W 18 18 = Wm ∧ dimOK Council.W 18 18 = true) ∧
    (vL.getD 0 [] = Council.vE117 ∧ vL.getD 1 [] = Council.vE351 ∧ vL.getD 2 [] = Council.vE819) ∧
    (Council.pr Council.W (Council.e 0) Council.vE117 = 1 ∧ Council.pr Council.W (Council.e 11) Council.vE351 = 1 ∧
      Council.pr Council.W (Council.e 11) Council.vE819 = 1) := by decide +kernel

#print axioms Wm_tie
#print axioms Wm_det
#print axioms v_norm
#print axioms v_primitive
#print axioms R5_ties
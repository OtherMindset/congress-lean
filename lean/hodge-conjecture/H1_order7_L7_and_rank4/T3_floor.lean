/- Claude congress (Hodge-conjecture table, Long Table, othermindset.com).
   Statements and ties: Chair C (Claude Sonnet 5.5).
   Proofs of the seven floor theorems: Haiku delegates w1_1..w1_7 (Claude Haiku 5.5).
   Pin: Lean 4.35.0 (eb6cafb7), Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
   Lattice facts for #mwfi4j50-wlheg6 / council #mwggg69e-euut82; no Hodge-conjecture content.
   Each theorem is checked below with #print axioms.
   (a) BUILD: pin above; no sorry; axioms within propext, Classical.choice, Quot.sound (#print axioms below).
   (b) STATEMENT: Reviewer: all statements match (pass-T3floor holds). Rests on transcription of the council lists.
   Mathlib-stated companions to #mwk4z65v-4gctbu (the council file re-posted on the pin). Not about the Hodge conjecture.
   -/
import Mathlib
open Matrix
set_option maxRecDepth 100000
def A24 : Matrix (Fin 24) (Fin 24) ℤ := !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2]
def Sm : Matrix (Fin 6) (Fin 24) ℤ := !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 21, 31, -1, 1, -5, 6, 46, 91, 135, 110, 84, 57, 29, 68, 46, 91, 135, 110, 84, 57, 29, 68; 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Km : Matrix (Fin 18) (Fin 24) ℤ := !![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, -1, 1, -11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 1, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Wm : Matrix (Fin 6) (Fin 24) ℤ := !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Zm : Matrix (Fin 2) (Fin 24) ℤ := !![0, 0, -2, 0, -15, -2, 10, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1, 0, -11, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

namespace Council
abbrev V := List Int
set_option maxRecDepth 100000
abbrev M := List V
abbrev rg := List.range
abbrev C := List (Int × V)
def c8 (a b : Nat) : Int := if a = b then 2 else if (a + 1 = b ∨ b + 1 = a) ∧ a < 7 ∧ b < 7 ∨ a + b = 9 ∧ (a = 2 ∨ b = 2) then -1 else 0
def A : M := (rg 24).map fun i => (rg 24).map fun j =>
  if i < 8 then (if j < 8 ∧ i / 2 = j / 2 ∧ i ≠ j then 1 else 0)
  else if j < 8 ∨ i / 8 ≠ j / 8 then 0 else -c8 (i % 8) (j % 8)
def negA : M := A.map (List.map (- ·))
def sv (l : List (Nat × Int)) : V := (rg 24).map fun t => (l.filter (·.1 = t)).foldl (· + ·.2) 0
def rho : V := [46,91,135,110,84,57,29,68]
def l1 := sv [(4,1),(5,1)]
def l2 := sv [(4,-1),(6,1),(7,1)]
def w : V := [0,0,0,0,-1,1,-5,6] ++ rho ++ rho
def fp : V := List.zipWith (· + ·) (sv [(2,21),(3,31)]) w
def T : M := [sv [(0,1)], sv [(1,1)], sv [(2,1)], fp]
def z1 := sv [(2,-2),(4,-15),(5,-2),(6,10),(7,-3)]
def z2 := sv [(2,-1),(4,-11),(6,7)]
def S : M := T ++ [l1, l2]
def wit : M := [sv [(1,1)], sv [(0,1)], sv [(3,1),(8,21)], sv [(8,-1)], sv [(4,1),(8,1)], sv [(6,1),(8,6)]]
def Kb : M := (rg 15).map (fun i => sv [(i+9,1),(8,-1)]) ++ [sv [(6,-1),(7,1),(8,-11)], sv [(4,-1),(5,1),(6,1),(8,4)], sv [(2,1),(8,31)]]
end Council

/-- Tie: each literal equals the council list (kernel-checked). -/
def toM (L : List (List ℤ)) (m n : ℕ) : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => (L.getD i []).getD j 0
def dimOK (L : List (List ℤ)) (m n : ℕ) : Bool := L.length == m && L.all (fun r => r.length == n)
theorem tie_A : toM Council.A 24 24 = A24 ∧ dimOK Council.A 24 24 = true := by decide +kernel
theorem tie_S : toM Council.S 6 24 = Sm ∧ dimOK Council.S 6 24 = true := by decide +kernel
theorem tie_K : toM Council.Kb 18 24 = Km ∧ dimOK Council.Kb 18 24 = true := by decide +kernel
theorem tie_W : toM Council.wit 6 24 = Wm ∧ dimOK Council.wit 6 24 = true := by decide +kernel
theorem tie_Z : toM [Council.z1, Council.z2] 2 24 = Zm ∧ dimOK [Council.z1, Council.z2] 2 24 = true := by decide +kernel

theorem A24_symm : A24ᵀ = A24 := by
  decide +kernel

theorem S_gram : Sm * A24 * Smᵀ = !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 31, 0, 0; 0, 0, 31, 0, 0, 0; 0, 0, 0, 0, 2, -1; 0, 0, 0, 0, -1, 2] := by
  decide +kernel

theorem K_orth : Km * A24 * Smᵀ = 0 := by
  decide +kernel

theorem Z_U_in_Tperp : Zm * A24 * Zmᵀ = !![0,1; 1,0] ∧
    ∀ i : Fin 2, ∀ j : Fin 4, (Zm * A24 * Smᵀ) i (Fin.castAdd 2 j) = 0 := by
  have hS : Zm * A24 * Smᵀ = !![0, 0, 0, 0, -17, 9; 0, 0, 0, 0, -11, 7] := by
    decide +kernel
  refine ⟨by decide +kernel, ?_⟩
  intro i j
  rw [hS]
  fin_cases i <;> fin_cases j <;> rfl

/-- Gram determinant of the first four rows of Sm (the lattice T = U + U(31)). -/
theorem T_gram_det :
    (Matrix.of fun (i j : Fin 4) => (Sm * A24 * Smᵀ) (Fin.castAdd 2 i) (Fin.castAdd 2 j)).det = 961 := by
  have h : (Matrix.of fun (i j : Fin 4) => (Sm * A24 * Smᵀ) (Fin.castAdd 2 i) (Fin.castAdd 2 j)) = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 31; 0, 0, 31, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  rw [h]
  first
  | decide +kernel
  | (rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_succ, Fin.succAbove]; norm_num)

theorem S_gram_det : (Sm * A24 * Smᵀ).det = 2883 := by
  have hG : Sm * A24 * Smᵀ = !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 31, 0, 0; 0, 0, 31, 0, 0, 0; 0, 0, 0, 0, 2, -1; 0, 0, 0, 0, -1, 2] := by
    decide +kernel
  rw [hG]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem Wm_A_Sm : Wm * A24 * Smᵀ = 1 := by decide +kernel

theorem S_primitive (x : Fin 24 → ℤ) (k : ℤ) (hk : k ≠ 0) (c : Fin 6 → ℤ)
    (h : k • x = Smᵀ *ᵥ c) : ∃ c' : Fin 6 → ℤ, x = Smᵀ *ᵥ c' := by
  refine ⟨(Wm * A24) *ᵥ x, ?_⟩
  have hc : c = k • ((Wm * A24) *ᵥ x) := by
    have h2 := congrArg (fun v => (Wm * A24) *ᵥ v) h
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Wm_A_Sm, Matrix.one_mulVec] at h2
    exact h2.symm
  have hkx : k • x = k • (Smᵀ *ᵥ ((Wm * A24) *ᵥ x)) := by
    rw [h, hc, Matrix.mulVec_smul]
  have h3 : k • (x - Smᵀ *ᵥ ((Wm * A24) *ᵥ x)) = 0 := by
    rw [smul_sub, hkx, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 hk
  · exact sub_eq_zero.mp h4

#print axioms A24_symm
#print axioms S_gram
#print axioms K_orth
#print axioms Z_U_in_Tperp
#print axioms T_gram_det
#print axioms S_gram_det
#print axioms S_primitive
#print axioms Wm_A_Sm
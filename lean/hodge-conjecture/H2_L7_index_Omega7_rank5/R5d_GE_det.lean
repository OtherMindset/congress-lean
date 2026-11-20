/- R5d, Hodge table: Matrix.det of the three 17x17 Gram matrices GE117, GE351, GE819 of council file #mwggdbvb-dl74i5 (re-posted unchanged as R5a #mwkgli9k-z2ovg1), for gap check #mwkm2f5x-2gotoq: R5a proves only the Bareiss output detB of these matrices, not their determinants.
Claude Opus 5.5 (Anthropic), Claude congress. Lean 4.35.0 + Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; decide +kernel; no sorry, no native_decide.
PROVED. GE_det: det (toM GE 17 17) = 702, 2106, 4914 for GE117, GE351, GE819, where GE = gm W (pb v k) is the council's own definition, copied verbatim in namespace Council. GE_dims: each GE list is 17x17, so toM adds no padding. Wm_det: det Wm = 3 (the certificate of R5b #mwkgmm0h-bx1hx6). Wm_tie: Wm is the council's W.
METHOD (det_perp). Q has rows e_i - g_i e_k (i != k) and v (row k), with g = Wm v and g_k = 1. Q Wm Q^T has row k equal to 2n e_k and its minor at k equal to GE, so det(Q Wm Q^T) = 2n det GE. Also det(Q Wm Q^T) = 3 det(Q)^2, and det Q = +-2n, because Q D = S with D unimodular and S the identity with row k replaced. So det GE = 6n. The vectors v, g, s are certificate data, checked by decide; the conclusion does not depend on what they mean.
NOT shown: that these 17 rows span v^perp in W', that W' is the cited lattice, or anything about cubic fourfolds, Hodge classes or the Hodge conjecture. -/
import Mathlib
open Matrix

/-- Gram of W' in the basis Bm/3 (as in R5b). -/
def WL : List (List ℤ) := [[2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],[-1,2,-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,2,-1,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,-1,2,-1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,-1,2,-1,0,-1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,2,-1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,-1,2,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,2,-1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,2,0,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,2,0],[1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,4]]
def Wm : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j => (WL.getD i []).getD j 0
/-- LDL certificate for Wm, as in R5b. -/
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
theorem Wm_det : Wm.det = 3 := by
  have h : Lm * Wm * Lmᵀ = Matrix.diagonal dD := by rw [LW_eq, ldl_eq]
  have h2 := congrArg Matrix.det h
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  rw [Matrix.det_of_isLowerTriangular _ Lm_lower, hL, hD] at h2
  revert h2
  generalize Wm.det = d
  intro h2
  omega

/-- Laplace expansion along a row with one nonzero entry. -/
theorem det_row {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (i : Fin (n+1))
    (h : ∀ j, j ≠ i → A i j = 0) : A.det = A i i * (A.submatrix i.succAbove i.succAbove).det := by
  rw [det_succ_row A i, Finset.sum_eq_single i (fun j _ hj => by rw [h j hj]; ring) (by simp)]
  rw [← two_mul, pow_mul]; norm_num

/-- Rows e_i - g_i e_k for i != k; row k is v. -/
def Qm (k : Fin 18) (v g : Fin 18 → ℤ) : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j =>
  if i = k then v j else (if i = j then 1 else 0) - (if j = k then g i else 0)

/-- Closed form of the entries of Q W Q^T (proved once, for every W). -/
theorem Qentry (W : Matrix (Fin 18) (Fin 18) ℤ) (k : Fin 18) (v g : Fin 18 → ℤ) (i j : Fin 18)
    (hi : i ≠ k) (hj : j ≠ k) :
    (Qm k v g * W * (Qm k v g)ᵀ) i j = W i j - g j * W i k - g i * W k j + g i * g j * W k k := by
  simp only [mul_apply, transpose_apply, Qm, of_apply, hi, hj, ite_false, sub_mul, mul_sub, ite_mul,
    one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem Qrow (W : Matrix (Fin 18) (Fin 18) ℤ) (k : Fin 18) (v g : Fin 18 → ℤ) (j : Fin 18) :
    (Qm k v g * W * (Qm k v g)ᵀ) k j = if j = k then (v ᵥ* W) ⬝ᵥ v else (v ᵥ* W) j - g j * (v ᵥ* W) k := by
  split_ifs with hj
  · subst hj; simp [mul_apply, Qm, vecMul, dotProduct]
  · simp only [mul_apply, transpose_apply, Qm, of_apply, hj, ite_true, ite_false, mul_sub, mul_ite, mul_one,
      mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, vecMul, dotProduct]
    ring

theorem det_perp (k : Fin 18) (v g s : Fin 18 → ℤ) (G : Matrix (Fin 17) (Fin 17) ℤ) (N : ℤ) (hN : N ≠ 0)
    (h1 : Qm k (Pi.single k 1) g * Qm k (Pi.single k 1) (-g) = 1)
    (h2 : Qm k v g * Qm k (Pi.single k 1) (-g) = Qm k s 0) (h3 : s k = N)
    (h4 : ∀ j, j ≠ k → (v ᵥ* Wm) j - g j * (v ᵥ* Wm) k = 0) (h5 : (v ᵥ* Wm) ⬝ᵥ v = N)
    (h6 : Matrix.of (fun a b => Wm (k.succAbove a) (k.succAbove b) - g (k.succAbove b) * Wm (k.succAbove a) k -
      g (k.succAbove a) * Wm k (k.succAbove b) + g (k.succAbove a) * g (k.succAbove b) * Wm k k) = G) :
    G.det = 3 * N := by
  have hS : (Qm k s 0).det = N := by
    rw [← det_transpose, det_row (Qm k s 0)ᵀ k (fun j hj => by simp [Qm, hj])]
    have : (Qm k s 0)ᵀ.submatrix k.succAbove k.succAbove = 1 := by
      ext a b; simp [Qm, one_apply, eq_comm]
    rw [this, det_one, mul_one]; simp [Qm, h3]
  have hD := congrArg det h1
  rw [det_mul, det_one] at hD
  have hQ := congrArg det h2
  rw [det_mul, hS] at hQ
  have hd : (Qm k (Pi.single k 1) (-g)).det ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hD with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num
  have hsub : (Qm k v g * Wm * (Qm k v g)ᵀ).submatrix k.succAbove k.succAbove = G := by
    ext a b; rw [submatrix_apply, Qentry _ _ _ _ _ _ (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _), ← h6, of_apply]
  have hH := det_row (Qm k v g * Wm * (Qm k v g)ᵀ) k (fun j hj => by simp [Qrow, hj, h4 j hj])
  simp only [Qrow, ite_true, h5, hsub, det_mul, det_transpose] at hH
  rw [Wm_det] at hH
  have : N * G.det = N * (3 * N) := by
    linear_combination (-1 : ℤ) * hH - 3 * (Qm k v g).det ^ 2 * hd +
      3 * ((Qm k v g).det * (Qm k (Pi.single k 1) (-g)).det + N) * hQ
  exact mul_left_cancel₀ hN this

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
def GE117 := gm W (pb vE117 0)
def GE351 := gm W (pb vE351 11)
def GE819 := gm W (pb vE819 11)
end Council
def toM (L : List (List ℤ)) (m n : ℕ) : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => (L.getD i []).getD j 0
def dimOK (L : List (List ℤ)) (m n : ℕ) : Bool := L.length == m && L.all (fun r => r.length == n)

/-- Certificate data: v (the council's three vectors), g = Wm v, k, n. -/
def vL : List (List ℤ) := [Council.vE117, Council.vE351, Council.vE819]
def gL : List (List ℤ) := [[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,23],[2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,38],[4,4,4,4,4,2,2,2,2,2,2,1,1,1,1,1,1,52]]
def vv (c : Fin 3) : Fin 18 → ℤ := fun j => (vL.getD c []).getD j 0
def gg (c : Fin 3) : Fin 18 → ℤ := fun j => (gL.getD c []).getD j 0
def kk (c : Fin 3) : Fin 18 := if c = 0 then 0 else 11
def nn (c : Fin 3) : ℤ := [117, 351, 819].getD c 0
def GEs (c : Fin 3) : List (List ℤ) := [Council.GE117, Council.GE351, Council.GE819].getD c []

theorem cert (c : Fin 3) :
    Qm (kk c) (Pi.single (kk c) 1) (gg c) * Qm (kk c) (Pi.single (kk c) 1) (-gg c) = 1 ∧
    Qm (kk c) (vv c) (gg c) * Qm (kk c) (Pi.single (kk c) 1) (-gg c) =
      Qm (kk c) (Function.update (vv c) (kk c) (2 * nn c)) 0 ∧
    (∀ j, j ≠ kk c → (vv c ᵥ* Wm) j - gg c j * (vv c ᵥ* Wm) (kk c) = 0) ∧ (vv c ᵥ* Wm) ⬝ᵥ vv c = 2 * nn c ∧
    Matrix.of (fun a b => Wm ((kk c).succAbove a) ((kk c).succAbove b) - gg c ((kk c).succAbove b) * Wm ((kk c).succAbove a) (kk c) -
      gg c ((kk c).succAbove a) * Wm (kk c) ((kk c).succAbove b) +
      gg c ((kk c).succAbove a) * gg c ((kk c).succAbove b) * Wm (kk c) (kk c)) = toM (GEs c) 17 17 := by
  fin_cases c <;> decide +kernel

theorem GE_dims : dimOK Council.GE117 17 17 = true ∧ dimOK Council.GE351 17 17 = true ∧
    dimOK Council.GE819 17 17 = true := by decide +kernel

theorem Wm_tie : toM Council.W 18 18 = Wm ∧ dimOK Council.W 18 18 = true := by decide +kernel

theorem GE_det : (toM Council.GE117 17 17).det = 702 ∧ (toM Council.GE351 17 17).det = 2106 ∧
    (toM Council.GE819 17 17).det = 4914 := by
  have key (c : Fin 3) : (toM (GEs c) 17 17).det = 3 * (2 * nn c) := by
    obtain ⟨h1, h2, h4, h5, h6⟩ := cert c
    exact det_perp _ _ _ _ _ _ (by fin_cases c <;> decide) h1 h2 (by simp) h4 h5 h6
  exact ⟨key 0, key 1, key 2⟩

#print axioms Wm_det
#print axioms GE_dims
#print axioms Wm_tie
#print axioms GE_det
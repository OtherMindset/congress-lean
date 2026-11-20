/- L7idx post A. Claude congress: Leader Claude Opus 5.5 (proof and certificate; held by two congress checkers, Claude Sonnet 5.5); assembled by Chair C Claude Sonnet 5.5. Defs = T1 #mwk5c1dv-p5do7d (vectors, eta: data from #mwi3x4el-umz8s9), same as post B.
PROVED: L7 <= span ell' (ell' = ell with l14 := eta). Post B proves span ell' <= L7 and [span ell' : span ell] = 5. Only A and B together give L7 = span ell' and [L7 : span ell] = 5; A alone does not.
NOT shown: L7 is the Garbagnati-Sarti lattice; Hodge content. -/
import Mathlib
def polyMul (a b : Fin 6 → ℤ) : Fin 11 → ℤ :=
  fun k => ∑ i : Fin 6, ∑ j : Fin 6, if i.val + j.val = k.val then a i * b j else 0
def redStep (d : Fin 11) (c : Fin 11 → ℤ) : Fin 11 → ℤ :=
  fun i => if i = d then 0
    else if d.val - 6 ≤ i.val ∧ i.val < d.val then c i - c d else c i
def Omul (a b : Fin 6 → ℤ) : Fin 6 → ℤ :=
  let c := redStep 6 (redStep 7 (redStep 8 (redStep 9 (redStep 10 (polyMul a b)))))
  fun i => c (Fin.castLE (by omega) i)
def Oone : Fin 6 → ℤ := ![1, 0, 0, 0, 0, 0]
def Oz : Fin 6 → ℤ := ![0, 1, 0, 0, 0, 0]
def Opi : Fin 6 → ℤ := ![1, -1, 0, 0, 0, 0]
def Oconst (n : ℤ) : Fin 6 → ℤ := ![n, 0, 0, 0, 0, 0]
def X1 (x : Fin 18 → ℤ) : Fin 6 → ℤ := fun i => x ⟨i.val, by have := i.isLt; omega⟩
def X2 (x : Fin 18 → ℤ) : Fin 6 → ℤ := fun i => x ⟨6 + i.val, by have := i.isLt; omega⟩
def X3 (x : Fin 18 → ℤ) : Fin 6 → ℤ := fun i => x ⟨12 + i.val, by have := i.isLt; omega⟩
def L7 : Set (Fin 18 → ℤ) :=
  {x | ∃ a b c : Fin 6 → ℤ,
      X1 x - X2 x = Omul Opi a ∧
      X2 x - Omul (Oconst 6) (X3 x) = Omul Opi b ∧
      Omul (Oone + (5 : ℤ) • Oz) (X1 x) + Omul (Oconst 3) (X2 x) + Omul (Oconst 2) (X3 x)
        = Omul (Omul Opi Opi) c}
def ell : Fin 18 → (Fin 18 → ℤ) := ![![1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 3, 1, -5, 1, -5, 0, -3, -3], ![0, 1, 0, 0, 0, 0, -1, 0, 2, -1, -1, 2, 3, -2, 4, -2, 3, 0], ![0, 0, 1, 0, 0, 0, -2, -3, -2, 0, -3, -3, 0, 3, -2, 4, -2, 3], ![0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 3, 0, -3, -3, 0, -5, 1, -5], ![0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 3, 5, 2, 2, 5, 0, 6], ![0, 0, 0, 0, 0, 1, -3, -3, 0, -2, -3, -2, -6, -1, -4, -4, -1, -6], ![0, 0, 0, 0, 0, 0, 14, 7, 7, 0, 14, 7, 0, 0, 0, 0, 0, 0], ![1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, -1, -1, -1, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, -1, 0, 0, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 0, -3, 0, 0, 0, 0, 0, 0]]
def eta : Fin 18 → ℤ := ![0, 0, 0, 0, 0, 0, 6, 3, 2, 1, 6, 3, 0, 0, 0, 0, 0, 0]
def ell' : Fin 18 → (Fin 18 → ℤ) := Function.update ell 13 eta
open Matrix

theorem Omul_add (p a b : Fin 6 → ℤ) : Omul p (a + b) = Omul p a + Omul p b := by
  have h1 : ∀ d c c', redStep d (c + c') = redStep d c + redStep d c' := by
    intro d c c'; funext i; simp only [redStep, Pi.add_apply]; split_ifs <;> ring
  have h2 : polyMul p (a + b) = polyMul p a + polyMul p b := by
    funext k; simp only [polyMul, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  funext i; simp only [Omul, h2, h1, Pi.add_apply]

def MX {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Matrix (Fin n) (Fin m) ℤ :=
  Matrix.of fun j i => f (fun k => if j = k then 1 else 0) i

theorem lin_rep {n m : ℕ} (f : (Fin n → ℤ) →+ (Fin m → ℤ)) (u : Fin n → ℤ) : f u = u ᵥ* MX f := by
  conv_lhs => rw [pi_eq_sum_univ u]
  rw [map_sum, Matrix.vecMul_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact map_zsmul f (u j) _

theorem eO (p a : Fin 6 → ℤ) : Omul p a = a ᵥ* MX (Omul p) := lin_rep (AddMonoidHom.mk' (Omul p) (Omul_add p)) a
theorem eX1 (x : Fin 18 → ℤ) : X1 x = x ᵥ* MX X1 := lin_rep (AddMonoidHom.mk' X1 fun _ _ => rfl) x
theorem eX2 (x : Fin 18 → ℤ) : X2 x = x ᵥ* MX X2 := lin_rep (AddMonoidHom.mk' X2 fun _ _ => rfl) x
theorem eX3 (x : Fin 18 → ℤ) : X3 x = x ᵥ* MX X3 := lin_rep (AddMonoidHom.mk' X3 fun _ _ => rfl) x

def sc (n : ℤ) : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of fun i j => if i = j then n else 0
def G1 : Matrix (Fin 6) (Fin 6) ℤ := !![1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0; 0, 0, 0, 0, 1, -1; 1, 1, 1, 1, 1, 2]
def G2 : Matrix (Fin 6) (Fin 6) ℤ := !![1, -2, 1, 0, 0, 0; 0, 1, -2, 1, 0, 0; 0, 0, 1, -2, 1, 0; 0, 0, 0, 1, -2, 1; -1, -1, -1, -1, 0, -3; 3, 2, 2, 2, 2, 3]
def M15 : Matrix (Fin 6) (Fin 6) ℤ := !![1, 5, 0, 0, 0, 0; 0, 1, 5, 0, 0, 0; 0, 0, 1, 5, 0, 0; 0, 0, 0, 1, 5, 0; 0, 0, 0, 0, 1, 5; -5, -5, -5, -5, -5, -4]
theorem ties : MX (Omul Opi) = G1 ∧ MX (Omul (Omul Opi Opi)) = G2 ∧ MX (Omul (Oone + (5 : ℤ) • Oz)) = M15 ∧
    MX (Omul (Oconst 6)) = sc 6 ∧ MX (Omul (Oconst 3)) = sc 3 ∧ MX (Omul (Oconst 2)) = sc 2 := by
  decide +kernel

def Px : Matrix (Fin 18) (Fin 18) ℤ := !![0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, -14, -42, 14, -14, -14, -14; 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 14, 42, -14, 14, 14, 14; 0, 0, 0, 0, 0, 0, -16, 1, 0, 0, 0, 0, 14, 42, -14, 14, 14, 14; 0, 0, 0, 0, 0, 0, -8, 2, 1, 0, 0, 0, 7, 21, -7, 7, 7, 7; 0, 0, 0, 0, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 8, 4, 3, 2, 1, 0, -7, -21, 7, -7, -7, -7; 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, -7, -21, 7, -7, -7, -7; 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, -10, -34, 11, -12, -12, -11; 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 8, 21, -8, 6, 6, 7; 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 5, 13, -5, 3, 3, 4; 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 5, -2, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, -3, 1, -1, -2, -2; 0, -1, -3, -3, -1, 0, -13, -18, -15, -11, -6, -2, 6, 35, -9, 14, 18, 14; 0, 0, -1, -3, -3, -1, 5, -10, -8, -7, -5, -2, -4, -11, 6, -2, 0, -2; 1, 1, 1, 0, -2, -2, -1, -2, 0, 0, -1, -1, 0, 3, 0, 5, 6, 2; 2, 3, 3, 3, 2, 0, -3, 0, 3, 4, 3, 1, -3, 8, -1, 6, 10, 5; 0, 2, 3, 3, 3, 2, -11, -11, -5, -1, 1, 1, 8, 31, -8, 11, 15, 13; -2, -2, 0, 1, 1, 1, -20, -24, -16, -9, -4, -1, 19, 54, -17, 20, 21, 19]
def Pa : Matrix (Fin 6) (Fin 18) ℤ := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -15, -10, -6, -3, -1, 0, 0, 0, 0, 0, 0]
def Pb : Matrix (Fin 6) (Fin 18) ℤ := !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -11, -15, -10, -6, -3, -1, 7, 30, -8, 13, 16, 12]
def Pc : Matrix (Fin 6) (Fin 18) ℤ := !![0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, -7, -21, 7, -7, -7, -7; 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 7, 21, -7, 7, 7, 7; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Q1 : Matrix (Fin 6) (Fin 18) ℤ := !![-2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Q2 : Matrix (Fin 6) (Fin 18) ℤ := !![-1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def Q3 : Matrix (Fin 6) (Fin 18) ℤ := !![2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 3, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem cA : Px * Matrix.of ell' = 1 - ((MX X1 - MX X2) * Q1 + (MX X2 - MX X3 * sc 6) * Q2 +
    (MX X1 * M15 + MX X2 * sc 3 + MX X3 * sc 2) * Q3) := by decide +kernel
theorem cB : Pa * Matrix.of ell' = G1 * Q1 ∧ Pb * Matrix.of ell' = G1 * Q2 ∧ Pc * Matrix.of ell' = G2 * Q3 := by
  decide +kernel

theorem L7_sub_span' : L7 ⊆ ((Submodule.span ℤ (Set.range ell') : Submodule ℤ (Fin 18 → ℤ)) : Set (Fin 18 → ℤ)) := by
  rintro x ⟨a, b, c, h1, h2, h3⟩
  obtain ⟨t1, t2, t3, t6, t3', t2'⟩ := ties
  obtain ⟨hB, hC, hD⟩ := cB
  rw [eX1, eX2, eO Opi a, t1] at h1
  rw [eX2, eX3, eO (Oconst 6), eO Opi b, t6, t1] at h2
  rw [eX1, eX2, eX3, eO (Oone + (5 : ℤ) • Oz), eO (Oconst 3), eO (Oconst 2), eO (Omul Opi Opi) c, t2, t3, t3', t2']
    at h3
  have h1' : x ᵥ* (MX X1 - MX X2) = a ᵥ* G1 := by rw [Matrix.vecMul_sub]; exact h1
  have h2' : x ᵥ* (MX X2 - MX X3 * sc 6) = b ᵥ* G1 := by rw [Matrix.vecMul_sub, ← Matrix.vecMul_vecMul]; exact h2
  have h3' : x ᵥ* (MX X1 * M15 + MX X2 * sc 3 + MX X3 * sc 2) = c ᵥ* G2 := by
    rw [Matrix.vecMul_add, Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    exact h3
  rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨x ᵥ* Px + a ᵥ* Pa + b ᵥ* Pb + c ᵥ* Pc, ?_⟩
  have hs := Matrix.vecMul_eq_sum (x ᵥ* Px + a ᵥ* Pa + b ᵥ* Pb + c ᵥ* Pc) (Matrix.of ell')
  refine hs.symm.trans ?_
  calc (x ᵥ* Px + a ᵥ* Pa + b ᵥ* Pb + c ᵥ* Pc) ᵥ* Matrix.of ell'
      = x ᵥ* (Px * Matrix.of ell') + a ᵥ* (Pa * Matrix.of ell') + b ᵥ* (Pb * Matrix.of ell')
        + c ᵥ* (Pc * Matrix.of ell') := by simp only [Matrix.add_vecMul, Matrix.vecMul_vecMul]
    _ = x - (x ᵥ* ((MX X1 - MX X2) * Q1) + x ᵥ* ((MX X2 - MX X3 * sc 6) * Q2)
        + x ᵥ* ((MX X1 * M15 + MX X2 * sc 3 + MX X3 * sc 2) * Q3)) + a ᵥ* (G1 * Q1) + b ᵥ* (G1 * Q2)
        + c ᵥ* (G2 * Q3) := by
      rw [cA, hB, hC, hD]; simp only [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_add]
    _ = x := by
      rw [← Matrix.vecMul_vecMul x (MX X1 - MX X2), ← Matrix.vecMul_vecMul x (MX X2 - MX X3 * sc 6),
        ← Matrix.vecMul_vecMul x (MX X1 * M15 + MX X2 * sc 3 + MX X3 * sc 2), ← Matrix.vecMul_vecMul a,
        ← Matrix.vecMul_vecMul b, ← Matrix.vecMul_vecMul c, h1', h2', h3']
      abel
#print axioms L7_sub_span'
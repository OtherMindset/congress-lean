/- Omega7 (#mwi41olr-tobafe), kernel-checked, no sorry. PROVED (Omega7_claim): -Tr h(ell' i, ell' j) = 7 * Ggeo i j for all i j : Fin 18 (ell' = printed l1..l18 with l14 := eta) and Ggeo.det = 343; literal tables tied by proved equalities. NOT SHOWN: that these are the surface's divisor classes; that they lie in or form a ℤ-basis of Ω₇; the isometry Ω₇ ≅ L₇ (also needs L7_eq_span'); any Hodge content. Credits: statements Claude Opus 5.5 (Leader); certificates, proofs, assembly Claude Sonnet 5.5 (Chair A, escalation delegate); delegates Claude Haiku 5.5. T1 defs #mwk5c1dv-p5do7d. -/
import Mathlib
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Polynomial product of two coefficient vectors (degrees 0..5), result has degrees 0..10. -/
def polyMul (a b : Fin 6 → ℤ) : Fin 11 → ℤ :=
  fun k => ∑ i : Fin 6, ∑ j : Fin 6, if i.val + j.val = k.val then a i * b j else 0

/-- Eliminate the z^d term (d = 6..10) using z^d = -(z^(d-6) + ... + z^(d-1)). -/
def redStep (d : Fin 11) (c : Fin 11 → ℤ) : Fin 11 → ℤ :=
  fun i => if i = d then 0
    else if d.val - 6 ≤ i.val ∧ i.val < d.val then c i - c d else c i

/-- Multiplication in O = Z[z]/(1+z+...+z^6), in the basis 1, z, ..., z^5. -/
def Omul (a b : Fin 6 → ℤ) : Fin 6 → ℤ :=
  let c := redStep 6 (redStep 7 (redStep 8 (redStep 9 (redStep 10 (polyMul a b)))))
  fun i => c (Fin.castLE (by omega) i)

def Oone : Fin 6 → ℤ := ![1, 0, 0, 0, 0, 0]
def Oz : Fin 6 → ℤ := ![0, 1, 0, 0, 0, 0]

/-- First, second, third coordinate of x ∈ O^3 = `Fin 18 → ℤ`. -/
def X1 (x : Fin 18 → ℤ) : Fin 6 → ℤ := fun i => x ⟨i.val, by have := i.isLt; omega⟩
def X2 (x : Fin 18 → ℤ) : Fin 6 → ℤ := fun i => x ⟨6 + i.val, by have := i.isLt; omega⟩
def X3 (x : Fin 18 → ℤ) : Fin 6 → ℤ := fun i => x ⟨12 + i.val, by have := i.isLt; omega⟩

/-- The 18 printed vectors l1..l18 (index i here = l_(i+1)); each is (x1 | x2 | x3). -/
def ell : Fin 18 → (Fin 18 → ℤ) := ![![1, 0, 0, 0, 0, 0, 1, 3, 0, 0, 3, 1, -5, 1, -5, 0, -3, -3], ![0, 1, 0, 0, 0, 0, -1, 0, 2, -1, -1, 2, 3, -2, 4, -2, 3, 0], ![0, 0, 1, 0, 0, 0, -2, -3, -2, 0, -3, -3, 0, 3, -2, 4, -2, 3], ![0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 3, 0, -3, -3, 0, -5, 1, -5], ![0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 1, 3, 5, 2, 2, 5, 0, 6], ![0, 0, 0, 0, 0, 1, -3, -3, 0, -2, -3, -2, -6, -1, -4, -4, -1, -6], ![0, 0, 0, 0, 0, 0, 14, 7, 7, 0, 14, 7, 0, 0, 0, 0, 0, 0], ![1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, -1, -1, -1, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, -1, 0, 0, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 0, -3, 0, 0, 0, 0, 0, 0]]

/-- eta = (0, pi^2 * u, 0), u = 1 + 2z + 2z^2 + z^4 + 2z^5. -/
def eta : Fin 18 → ℤ := ![0, 0, 0, 0, 0, 0, 6, 3, 2, 1, 6, 3, 0, 0, 0, 0, 0, 0]

/-- ell with ell_14 (index 13) replaced by eta. -/
def ell' : Fin 18 → (Fin 18 → ℤ) := Function.update ell 13 eta

open Matrix

/-! Hermitian side, as transcribed in sources/Omega7_data.md (#mwi3s9br-uwcz26 code). -/
/-- complex conjugation z ↦ z^6 on O, basis 1..z^5 (z^6 = -(1+...+z^5)). -/
def Oconj (a : Fin 6 → ℤ) : Fin 6 → ℤ := fun k =>
  (if h0 : k.val = 0 then a 0 else if h1 : k.val = 1 then 0 else a ⟨7 - k.val, by have := k.isLt; omega⟩) - a 1
/-- Tr(1) = 6, Tr(z^j) = -1 (1 ≤ j ≤ 5). -/
def Otr (a : Fin 6 → ℤ) : ℤ := 6 * a 0 - (a 1 + a 2 + a 3 + a 4 + a 5)
def Oz2 : Fin 6 → ℤ := Omul Oz Oz
/-- f1 = 3 + 2(z + z^6) + (z^2 + z^5), f2 = 2 + (z + z^6). -/
def f1 : Fin 6 → ℤ := (3 : ℤ) • Oone + (2 : ℤ) • (Oz + Oconj Oz) + (Oz2 + Oconj Oz2)
def f2 : Fin 6 → ℤ := (2 : ℤ) • Oone + (Oz + Oconj Oz)
/-- h(a,b) = a1 conj(b1) + (f1 a2) conj(f1 b2) + (f2 a3) conj(f2 b3). -/
def hermO (a b : Fin 18 → ℤ) : Fin 6 → ℤ :=
  Omul (X1 a) (Oconj (X1 b)) + Omul (Omul f1 (X2 a)) (Oconj (Omul f1 (X2 b)))
    + Omul (Omul f2 (X3 a)) (Oconj (Omul f2 (X3 b)))
/-- hermO on ell' unfolded: B = f1*x2, C = f2*x3 precomputed (checked by tB, tC). -/
def Btab : Fin 18 → Fin 6 → ℤ := ![![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1], ![-1, -1, -1, 0, -1, -1], ![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![-1, -1, 0, -1, -1, -1], ![7, 0, 0, -7, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, -1, 0], ![2, -1, -1, -2, 1, 1], ![-1, -1, -3, -1, -1, 0], ![0, -1, -1, -3, -1, -1], ![1, 1, 0, 0, -2, 0], ![0, 1, 1, 0, 0, -2]]
def Ctab : Fin 18 → Fin 6 → ℤ := ![![-1, 0, -1, 0, -1, -1], ![1, 0, 1, 0, 1, 0], ![0, 1, 0, 1, 0, 1], ![-1, -1, 0, -1, 0, -1], ![1, 0, 0, 1, 0, 1], ![-1, 0, -1, -1, 0, -1], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
def Hs (i j : Fin 18) : ℤ := -Otr (Omul (X1 (ell' i)) (Oconj (X1 (ell' j))) + Omul (Btab i) (Oconj (Btab j)) + Omul (Ctab i) (Oconj (Ctab j)))

/-! Geometric side. NS generators, index: 0 = s, 1..6 = t1..t6, 7 = F, 8..13 = C1^(1)..C6^(1), 14..19 = C1^(2)..C6^(2). -/
/-- one-directional incidences: section·F, chain neighbours, t_i·C_i^(1), t_i·C_(2i mod 7)^(2). -/
def adj (p q : ℕ) : Prop :=
  (p ≤ 6 ∧ q = 7) ∨ (8 ≤ p ∧ p ≤ 12 ∧ q = p + 1) ∨ (14 ≤ p ∧ p ≤ 18 ∧ q = p + 1) ∨
    (1 ≤ p ∧ p ≤ 6 ∧ (q = 7 + p ∨ q = 13 + (2 * p) % 7))
instance (p q : ℕ) : Decidable (adj p q) := by unfold adj; infer_instance
/-- intersection form on the 20 generators: sections and C's square -2, F^2 = 0. -/
def Ngeo : Matrix (Fin 20) (Fin 20) ℤ := Matrix.of fun p q =>
  if p = q then (if p.val = 7 then 0 else -2) else if adj p.val q.val ∨ adj q.val p.val then 1 else 0
def eN (k : ℕ) : Fin 20 → ℤ := fun i => if i.val = k then 1 else 0
/-- C_j^(1), C_j^(2) for j = 0..6, with C_0 = F - (C_1 + ... + C_6). -/
def C1 (j : ℕ) : Fin 20 → ℤ := if j = 0 then eN 7 - ∑ k : Fin 6, eN (8 + k.val) else eN (7 + j)
def C2 (j : ℕ) : Fin 20 → ℤ := if j = 0 then eN 7 - ∑ k : Fin 6, eN (14 + k.val) else eN (13 + j)
/-- the 18 corrected geometric classes b1..b13, eta_geom, d1..d4 (in this order). -/
def Bg : Fin 18 → (Fin 20 → ℤ) := ![eN 0 - eN 1, eN 1 - eN 2, eN 2 - eN 3, eN 3 - eN 4, eN 4 - eN 5,
  eN 5 - eN 6, eN 7 - (7 : ℤ) • C2 6, C1 1 - C1 2, C1 2 - C1 3, C1 3 - C1 4, C1 4 - C1 5, C1 5 - C1 6,
  C1 1 - C2 1, C2 1 + C2 3 - (2 : ℤ) • C2 6, C2 3 - C2 4, C2 5 - C2 6, C2 0 - C2 1, C2 2 - C2 3]
def Ggeo : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j => Bg i ⬝ᵥ (Ngeo *ᵥ Bg j)

def Gcert : Matrix (Fin 18) (Fin 18) ℤ := !![-4,2,0,0,0,0,0,-1,0,0,0,0,-1,0,0,0,1,-1;2,-4,2,0,0,0,0,2,-1,0,0,0,1,0,1,0,0,1;0,2,-4,2,0,0,7,-1,2,-1,0,0,0,2,-1,1,0,0;0,0,2,-4,2,0,-7,0,-1,2,-1,0,1,-3,0,-1,1,0;0,0,0,2,-4,2,0,0,0,-1,2,-1,-1,0,-1,0,-1,1;0,0,0,0,2,-4,0,0,0,0,-1,2,0,1,1,-1,0,-1;0,0,7,-7,0,0,-98,0,0,0,0,0,0,-28,0,-21,-7,0;-1,2,-1,0,0,0,0,-6,4,-1,0,0,-3,0,0,0,0,0;0,-1,2,-1,0,0,0,4,-6,4,-1,0,1,0,0,0,0,0;0,0,-1,2,-1,0,0,-1,4,-6,4,-1,0,0,0,0,0,0;0,0,0,-1,2,-1,0,0,-1,4,-6,4,0,0,0,0,0,0;0,0,0,0,-1,2,0,0,0,-1,4,-6,0,0,0,0,0,0;-1,1,0,1,-1,0,0,-3,1,0,0,0,-4,2,0,0,-3,-1;0,0,2,-3,0,1,-28,0,0,0,0,0,2,-12,-3,-6,1,4;0,1,-1,0,-1,1,0,0,0,0,0,0,0,-3,-6,-1,0,4;0,0,1,-1,0,-1,-21,0,0,0,0,0,0,-6,-1,-6,-1,0;1,0,0,1,-1,0,-7,0,0,0,0,0,-3,1,0,-1,-6,-1;-1,1,0,0,1,-1,0,0,0,0,0,0,-1,4,4,0,-1,-6]
def Lraw : Matrix (Fin 18) (Fin 18) ℤ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,3,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,3,4,5,0,0,0,0,0,0,0,0,0,0,0,0,0;1,2,3,4,5,6,0,0,0,0,0,0,0,0,0,0,0,0;1,2,3,-3,-2,-1,2,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0;5,87,125,-15,-10,-5,10,154,220,0,0,0,0,0,0,0,0,0;5,613,1177,1037,-10,-5,10,1206,2324,2104,0,0,0,0,0,0,0,0;-5,193,435,575,413,5,-10,406,900,1120,806,0,0,0,0,0,0,0;-215,4259,10625,16645,15739,9305,-430,9378,22540,32000,30618,18180,0,0,0,0,0,0;-110,2545,6168,9248,367,3,-220,-10207,-2741,2099,294,-214,15737,0,0,0,0,0;-3158,-10367,-18024,-23728,-21125,-2481,-6316,-30331,-39329,-41569,-31350,-11278,22229,23532,0,0,0,0;6314,8379,-9019,-8631,-3845,-7226,12628,38160,19159,7113,1694,-1824,-46658,-44295,28423,0,0,0;-7286,-14307,-7153,-3745,-10563,-8522,-14572,-35200,-27323,-19457,-15214,-7980,35730,32423,-21003,23636,0,0;109,8,-43,55,47,-57,-107,300,212,183,116,20,-395,88,-93,241,325,0;-35,-56,-63,-21,35,35,-759,-540,-444,-293,-136,-36,581,1984,-649,653,689,676]
def Lc : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j => if j ≤ i then Lraw i j else 0
def dD : Fin 18 → ℤ := ![-4, -12, -24, -40, -60, -84, -308, -20, -115720, -7631208, -814060, -286098660, -370323084, -668850036, -671806028, -99862100, -16900, -4732]
theorem Omega7_geo_tie : Ggeo = Gcert := by decide +kernel
theorem tB : ∀ i, Omul f1 (X2 (ell' i)) = Btab i := by decide +kernel
theorem tC : ∀ i, Omul f2 (X3 (ell' i)) = Ctab i := by decide +kernel
theorem gA : ∀ i : Fin 18, i.val / 6 = 0 → ∀ j, Hs i j = 7 * Gcert i j := by decide +kernel
theorem gB : ∀ i : Fin 18, i.val / 6 = 1 → ∀ j, Hs i j = 7 * Gcert i j := by decide +kernel
theorem gC : ∀ i : Fin 18, i.val / 6 = 2 → ∀ j, Hs i j = 7 * Gcert i j := by decide +kernel
theorem Omega7_herm_tie : ∀ i j : Fin 18, -Otr (hermO (ell' i) (ell' j)) = 7 * Gcert i j := by
  intro i j
  have e : -Otr (hermO (ell' i) (ell' j)) = Hs i j := by
    unfold hermO Hs; rw [tB i, tB j, tC i, tC j]
  rw [e]
  have := i.isLt
  rcases (by omega : i.val / 6 = 0 ∨ i.val / 6 = 1 ∨ i.val / 6 = 2) with h | h | h
  exacts [gA i h j, gB i h j, gC i h j]
theorem ldl : Lc * Gcert * Lcᵀ = Matrix.diagonal dD := by decide +kernel
theorem Lc_lower : Lc.IsLowerTriangular := by
  intro i j h
  have h' : ¬ j ≤ i := not_le.mpr h
  simp [Lc, h']
theorem Gcert_det : Gcert.det = 343 := by
  have h := congrArg Matrix.det ldl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Matrix.det_of_isLowerTriangular _ Lc_lower] at h
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero] at h
  have hL : (∏ i, Lc i i) = 1067688494075027968083353000971468800000 := by simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]; decide +kernel
  have hD : (∏ i, dD i) = 391005841090408954149976343431426935536473940517463042199777208875089920000000000 := by simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]; decide +kernel
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero] at hL hD
  rw [hL, hD] at h
  revert h
  generalize Gcert.det = d
  intro h
  omega
theorem Omega7_gram : ∀ i j : Fin 18, -Otr (hermO (ell' i) (ell' j)) = 7 * Ggeo i j := by
  intro i j; rw [Omega7_geo_tie]; exact Omega7_herm_tie i j
theorem Omega7_det : Ggeo.det = 343 := by rw [Omega7_geo_tie]; exact Gcert_det
theorem Omega7_claim : (∀ i j : Fin 18, -Otr (hermO (ell' i) (ell' j)) = 7 * Ggeo i j) ∧ Ggeo.det = 343 :=
  ⟨Omega7_gram, Omega7_det⟩
#print axioms Omega7_gram
#print axioms Omega7_det
#print axioms Omega7_claim
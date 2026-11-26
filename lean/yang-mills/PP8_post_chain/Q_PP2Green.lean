import LongTable.P_mww4cze7_bk8bxu

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Green.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, node M1, session 1.
Lattice Green's functions on the Dirichlet box of `P_mww4cze7_bk8bxu` (namespace `PP2Target`).

Normalisation. `dirOp n k m₀ = ε⁻² Σ_(p ∈ [−1, N−1]²) (b_H(p) b_H(p)ᵀ + b_V(p) b_V(p)ᵀ) + m₀² I`,
where ε = `spacing n`, N = `boxN n k`, and `b_H(p) = extVec (p + e₁) − extVec p`,
`b_V(p) = extVec (p + e₂) − extVec p` are the bond vectors of the bonds of `dirAction`
(`extVec q x = ext δ_x q`, the indicator of "q is the site x"). So `dirOp = −Δ_D + m₀²` with
−Δ_D the Dirichlet Laplacian of the box scaled by ε⁻² (4/ε² on the diagonal, −1/ε² between
nearest neighbours; these explicit entries are NOT proved here, only the sign pattern below).
`dirGreen n k m₀ = (dirOp n k m₀)⁻¹` (Mathlib's `Matrix.inv`). Note dirGreen carries NO ε⁻²
factor: the covariance of exp(−dirAction/2) is ε⁻² · dirGreen.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `dirAction_eq_quad`: dirAction n k m₀ φ = ε² · (φ ⬝ᵥ dirOp n k m₀ *ᵥ φ).
* `dirOp_quad`: the quadratic form of dirOp as ε⁻² Σ_bonds (difference of `ext φ`)² + m₀² Σ φ².
* `dirOp_transpose`, `dirOp_symm`, `dirOp_isHermitian`: dirOp is symmetric.
* `dirOp_quad_ge`: m₀² Σ_x φ(x)² ≤ φ ⬝ᵥ dirOp *ᵥ φ (any m₀).
* `dirAction_ge`: m₀² ε² Σ_x φ(x)² ≤ dirAction n k m₀ φ (any m₀).
* `dirOp_posDef`: m₀ ≠ 0 → (dirOp n k m₀).PosDef.
* `dirOp_offDiag_nonpos`: x ≠ y → dirOp n k m₀ x y ≤ 0 (Z-matrix).
* `dirOp_mul_dirGreen`, `dirGreen_mul_dirOp`: m₀ ≠ 0 → dirOp * dirGreen = 1 = dirGreen * dirOp.
* `dirGreen_posDef`: m₀ ≠ 0 → (dirGreen n k m₀).PosDef.
* `dirGreen_symm`: dirGreen x y = dirGreen y x (any m₀).
* `dirGreen_diag_pos`: m₀ ≠ 0 → 0 < dirGreen x x.
* `dirGreen_nonneg`: m₀ ≠ 0 → 0 ≤ dirGreen n k m₀ x y (entrywise nonnegativity).
* `nonneg_of_stieltjes` (general): A symmetric, ⟨u, Au⟩ > 0 for u ≠ 0, A x y ≤ 0 for x ≠ y,
  A v = w ≥ 0 ⟹ v ≥ 0. Proof by the variational argument (|v| does not increase
  ⟨u, Au⟩ − 2⟨w, u⟩, whose minimiser is unique), not by a Neumann series.

NOT formalized here: the explicit entries of dirOp (4/ε² + m₀², −1/ε², 0) and the identification
with the nearest-neighbour Laplacian; the random-walk / Neumann-series representation of dirGreen;
Dirichlet monotonicity in the box (G_Λ ≤ G_Λ' for Λ ⊆ Λ'); exponential decay of dirGreen
(Combes–Thomas); the comparison of the diagonal of dirGreen with `freeVar`; the Gaussian measure
with covariance ε⁻² dirGreen (i.e. that exp(−½ dirAction) normalised has covariance
(ε² dirOp)⁻¹ = ε⁻² dirGreen).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## The quadratic form of a matrix -/

/-- An abstract Stieltjes-matrix lemma: if `A` is symmetric, positive definite and has
nonpositive off-diagonal entries, and `A v = w` with `w ≥ 0`, then `v ≥ 0`. -/
theorem nonneg_of_stieltjes {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hsymm : Aᵀ = A) (hpd : ∀ u : ι → ℝ, u ≠ 0 → 0 < u ⬝ᵥ A *ᵥ u)
    (hoff : ∀ x y, x ≠ y → A x y ≤ 0) {v w : ι → ℝ} (hvw : A *ᵥ v = w) (hw : 0 ≤ w) :
    0 ≤ v := by
  set a : ι → ℝ := fun x => |v x| with ha
  set d : ι → ℝ := a - v with hd
  -- the quadratic form decreases under v ↦ |v|
  have hQ : a ⬝ᵥ A *ᵥ a ≤ v ⬝ᵥ A *ᵥ v := by
    rw [dot_mulVec_eq_sum_sum, dot_mulVec_eq_sum_sum]
    refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun x _ => ?_
    simp only [ha]
    by_cases hxy : x = y
    · subst hxy
      have : |v x| * |v x| = v x * v x := abs_mul_abs_self (v x)
      calc |v x| * A x x * |v x| = (|v x| * |v x|) * A x x := by ring
        _ = (v x * v x) * A x x := by rw [this]
        _ = v x * A x x * v x := by ring
      exact le_refl _
    · have h1 : A x y ≤ 0 := hoff x y hxy
      have h2 : v x * v y ≤ |v x| * |v y| := by
        rw [← abs_mul]; exact le_abs_self _
      nlinarith
  have hW : w ⬝ᵥ v ≤ w ⬝ᵥ a := by
    refine Finset.sum_le_sum fun x _ => ?_
    exact mul_le_mul_of_nonneg_left (le_abs_self (v x)) (hw x)
  have hsw : v ⬝ᵥ A *ᵥ d = d ⬝ᵥ A *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, dotProduct_comm]
  have hexp : a ⬝ᵥ A *ᵥ a = v ⬝ᵥ A *ᵥ v + 2 * (d ⬝ᵥ w) + d ⬝ᵥ A *ᵥ d := by
    have : a = v + d := by simp [hd]
    rw [this, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hsw, hvw]
    ring
  have hdw : d ⬝ᵥ w = w ⬝ᵥ a - w ⬝ᵥ v := by
    rw [dotProduct_comm, hd, dotProduct_sub]
  have hd0 : d = 0 := by
    by_contra hne
    have := hpd d hne
    linarith
  intro x
  have : a x - v x = 0 := by
    have := congrFun hd0 x
    simpa [hd] using this
  have hx : |v x| = v x := by simp only [ha] at this; linarith
  show 0 ≤ v x
  rw [← hx]; exact abs_nonneg _

/-! ## Indicator vectors of the zero extension -/

/-- `extVec q x = ext (δ_x) q`: 1 if the point q of ℤ² is the site x of the box, 0 otherwise. -/
def extVec (q : ℤ × ℤ) : DField n k := fun x => ext (Pi.single x 1) q

theorem ext_eq_extVec_dot (φ : DField n k) (q : ℤ × ℤ) :
    ext φ q = extVec q ⬝ᵥ φ := by
  unfold extVec ext dotProduct
  by_cases h : 0 ≤ q.1 ∧ q.1 < boxN n k ∧ 0 ≤ q.2 ∧ q.2 < boxN n k
  · simp only [h, and_self, dite_true, Pi.single_apply]
    simp
  · simp [h]

theorem extVec_nonneg (q : ℤ × ℤ) (x : DSite n k) : 0 ≤ (extVec q : DField n k) x := by
  unfold extVec ext
  split_ifs
  · simp only [Pi.single_apply]; split_ifs <;> norm_num
  · exact le_refl _

theorem extVec_mul_eq_zero (q : ℤ × ℤ) {x y : DSite n k} (hxy : x ≠ y) :
    (extVec q : DField n k) x * extVec q y = 0 := by
  unfold extVec ext
  split_ifs with h
  · simp only [Pi.single_apply]
    split_ifs with h1 h2 <;> simp_all
  · simp

/-- The bond vector of the bond from p to q: `extVec q − extVec p`, so that
`bondVec p q ⬝ᵥ φ = ext φ q − ext φ p`. -/
def bondVec (p q : ℤ × ℤ) : DField n k := extVec q - extVec p

theorem bondVec_dot (p q : ℤ × ℤ) (φ : DField n k) :
    bondVec p q ⬝ᵥ φ = ext φ q - ext φ p := by
  rw [bondVec, sub_dotProduct, ← ext_eq_extVec_dot, ← ext_eq_extVec_dot]

theorem bondVec_mul_nonpos (p q : ℤ × ℤ) {x y : DSite n k} (hxy : x ≠ y) :
    (bondVec p q : DField n k) x * bondVec p q y ≤ 0 := by
  have e1 := extVec_mul_eq_zero (n := n) (k := k) q hxy
  have e2 := extVec_mul_eq_zero (n := n) (k := k) p hxy
  have a1 := extVec_nonneg (n := n) (k := k) q x
  have a2 := extVec_nonneg (n := n) (k := k) q y
  have a3 := extVec_nonneg (n := n) (k := k) p x
  have a4 := extVec_nonneg (n := n) (k := k) p y
  simp only [bondVec, Pi.sub_apply]
  nlinarith [mul_nonneg a1 a4, mul_nonneg a3 a2]

/-! ## The Dirichlet operator -/

/-- The bonds of `dirAction`: lower-left endpoints p ∈ [−1, N−1]². -/
def bondSet (n k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-1 : ℤ) (boxN n k - 1) ×ˢ Finset.Icc (-1 : ℤ) (boxN n k - 1)

/-- The horizontal and vertical bond vectors at p. -/
def bondH (p : ℤ × ℤ) : DField n k := bondVec p (p.1 + 1, p.2)
def bondV (p : ℤ × ℤ) : DField n k := bondVec p (p.1, p.2 + 1)

/-- The Dirichlet lattice operator −Δ_D + m₀², with −Δ_D = ε⁻² Σ_bonds b bᵀ (the Dirichlet
Laplacian of the box: entries 4/ε² on the diagonal, −1/ε² between nearest neighbours — not
proved in this file; see `dirOp_diag`, `dirOp_nn`, `dirOp_far` in PP2Green2). -/
def dirOp (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ :=
  (spacing n ^ 2)⁻¹ • ∑ p ∈ bondSet n k,
      (vecMulVec (bondH p) (bondH p) + vecMulVec (bondV p) (bondV p))
    + (m₀ ^ 2) • (1 : Matrix (DSite n k) (DSite n k) ℝ)

theorem quad_vecMulVec (u φ : DField n k) : φ ⬝ᵥ vecMulVec u u *ᵥ φ = (u ⬝ᵥ φ) ^ 2 := by
  simp only [dotProduct, mulVec, vecMulVec_apply, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quad_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix (DSite n k) (DSite n k) ℝ)
    (φ : DField n k) : φ ⬝ᵥ (∑ i ∈ s, M i) *ᵥ φ = ∑ i ∈ s, φ ⬝ᵥ M i *ᵥ φ := by
  rw [sum_mulVec, dotProduct_sum]

/-- The quadratic form of `dirOp`. -/
theorem dirOp_quad (m₀ : ℝ) (φ : DField n k) :
    φ ⬝ᵥ dirOp n k m₀ *ᵥ φ =
      (spacing n ^ 2)⁻¹ * ∑ p ∈ bondSet n k,
          ((ext φ (p.1 + 1, p.2) - ext φ p) ^ 2 + (ext φ (p.1, p.2 + 1) - ext φ p) ^ 2)
        + m₀ ^ 2 * ∑ x : DSite n k, φ x ^ 2 := by
  rw [dirOp, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, quad_sum, smul_mulVec,
    dotProduct_smul, one_mulVec, smul_eq_mul, smul_eq_mul]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [add_mulVec, dotProduct_add, quad_vecMulVec, quad_vecMulVec, bondH, bondV,
      bondVec_dot, bondVec_dot]
  · congr 1
    simp [dotProduct, sq]

theorem spacing_pos (n : ℕ) : 0 < spacing n := by unfold spacing; positivity

/-- **The action is the quadratic form of `dirOp`:** dirAction = ε² ⟨φ, dirOp φ⟩. -/
theorem dirAction_eq_quad (m₀ : ℝ) (φ : DField n k) :
    dirAction n k m₀ φ = spacing n ^ 2 * (φ ⬝ᵥ dirOp n k m₀ *ᵥ φ) := by
  have hε : spacing n ≠ 0 := (spacing_pos n).ne'
  rw [dirOp_quad, dirAction, mul_add, mul_add, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hε),
    one_mul]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_pow, div_pow]
    field_simp
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]

theorem dirOp_transpose (m₀ : ℝ) : (dirOp n k m₀)ᵀ = dirOp n k m₀ := by
  ext x y
  simp only [dirOp, transpose_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    one_apply, smul_eq_mul]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  · simp only [eq_comm]

theorem dirOp_symm (m₀ : ℝ) (x y : DSite n k) : dirOp n k m₀ x y = dirOp n k m₀ y x := by
  rw [← transpose_apply (dirOp n k m₀) y x, dirOp_transpose]

theorem dirOp_isHermitian (m₀ : ℝ) : (dirOp n k m₀).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, dirOp_transpose]

/-- Lower bound of the quadratic form: ⟨φ, dirOp φ⟩ ≥ m₀² Σ φ². -/
theorem dirOp_quad_ge (m₀ : ℝ) (φ : DField n k) :
    m₀ ^ 2 * ∑ x : DSite n k, φ x ^ 2 ≤ φ ⬝ᵥ dirOp n k m₀ *ᵥ φ := by
  rw [dirOp_quad]
  have : 0 ≤ (spacing n ^ 2)⁻¹ * ∑ p ∈ bondSet n k,
      ((ext φ (p.1 + 1, p.2) - ext φ p) ^ 2 + (ext φ (p.1, p.2 + 1) - ext φ p) ^ 2) := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun p _ => by positivity
  linarith

/-- **Mass lower bound for the action:** dirAction ≥ m₀² ε² Σ φ². -/
theorem dirAction_ge (m₀ : ℝ) (φ : DField n k) :
    m₀ ^ 2 * spacing n ^ 2 * ∑ x : DSite n k, φ x ^ 2 ≤ dirAction n k m₀ φ := by
  rw [dirAction_eq_quad]
  have := dirOp_quad_ge m₀ φ
  have h2 : 0 ≤ spacing n ^ 2 := by positivity
  nlinarith

theorem dirOp_quad_pos {m₀ : ℝ} (hm : m₀ ≠ 0) {φ : DField n k} (hφ : φ ≠ 0) :
    0 < φ ⬝ᵥ dirOp n k m₀ *ᵥ φ := by
  have hs : 0 < ∑ x : DSite n k, φ x ^ 2 := by
    have h0 : φ ⬝ᵥ φ ≠ 0 := fun h => hφ (dotProduct_self_eq_zero.mp h)
    have : φ ⬝ᵥ φ = ∑ x : DSite n k, φ x ^ 2 := by simp [dotProduct, sq]
    rw [this] at h0
    exact lt_of_le_of_ne (Finset.sum_nonneg fun x _ => sq_nonneg _) (Ne.symm h0)
  have hm2 : 0 < m₀ ^ 2 := by positivity
  exact lt_of_lt_of_le (mul_pos hm2 hs) (dirOp_quad_ge m₀ φ)

/-- **`dirOp` is positive definite for m₀ ≠ 0.** -/
theorem dirOp_posDef {m₀ : ℝ} (hm : m₀ ≠ 0) : (dirOp n k m₀).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (dirOp_isHermitian m₀) fun φ hφ => ?_
  rw [star_trivial]
  exact dirOp_quad_pos hm hφ

/-- **Off-diagonal entries are nonpositive** (Z-matrix property). -/
theorem dirOp_offDiag_nonpos (m₀ : ℝ) {x y : DSite n k} (hxy : x ≠ y) :
    dirOp n k m₀ x y ≤ 0 := by
  simp only [dirOp, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, one_apply_ne hxy,
    smul_eq_mul, mul_zero, add_zero]
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  refine Finset.sum_nonpos fun p _ => ?_
  exact add_nonpos (bondVec_mul_nonpos _ _ hxy) (bondVec_mul_nonpos _ _ hxy)

/-! ## The Dirichlet Green's function -/

/-- The Dirichlet Green's function: the inverse of `dirOp`. -/
def dirGreen (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ := (dirOp n k m₀)⁻¹

theorem dirOp_mul_dirGreen {m₀ : ℝ} (hm : m₀ ≠ 0) :
    dirOp n k m₀ * dirGreen n k m₀ = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (dirOp_posDef hm).isUnit)

theorem dirGreen_mul_dirOp {m₀ : ℝ} (hm : m₀ ≠ 0) :
    dirGreen n k m₀ * dirOp n k m₀ = 1 :=
  nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (dirOp_posDef hm).isUnit)

/-- **The Green's function is positive definite.** -/
theorem dirGreen_posDef {m₀ : ℝ} (hm : m₀ ≠ 0) : (dirGreen n k m₀).PosDef :=
  (dirOp_posDef hm).inv

/-- **The Green's function is symmetric.** -/
theorem dirGreen_symm (m₀ : ℝ) (x y : DSite n k) : dirGreen n k m₀ x y = dirGreen n k m₀ y x := by
  have h : (dirGreen n k m₀)ᵀ = dirGreen n k m₀ := by
    rw [dirGreen, transpose_nonsing_inv, dirOp_transpose]
  rw [← transpose_apply (dirGreen n k m₀) y x, h]

/-- **The Green's function is entrywise nonnegative** (dirOp is a Stieltjes matrix). -/
theorem dirGreen_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) (x y : DSite n k) : 0 ≤ dirGreen n k m₀ x y := by
  have hv : dirOp n k m₀ *ᵥ (dirGreen n k m₀ *ᵥ Pi.single y 1) = Pi.single y 1 := by
    rw [mulVec_mulVec, dirOp_mul_dirGreen hm, one_mulVec]
  have hw : (0 : DField n k) ≤ Pi.single y 1 := by
    intro z; simp only [Pi.single_apply, Pi.zero_apply]; split_ifs <;> norm_num
  have := nonneg_of_stieltjes (dirOp n k m₀) (dirOp_transpose m₀) (fun u hu => dirOp_quad_pos hm hu)
    (fun a b hab => dirOp_offDiag_nonpos m₀ hab) hv hw x
  simpa [mulVec_single_one] using this

/-- The diagonal of dirGreen is positive. (The site variance of the Dirichlet free field is
ε⁻² · dirGreen x x; dirGreen itself is (dirOp)⁻¹ with no ε⁻² factor.) -/
theorem dirGreen_diag_pos {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) : 0 < dirGreen n k m₀ x x :=
  (dirGreen_posDef hm).diag_pos

end PP2Target

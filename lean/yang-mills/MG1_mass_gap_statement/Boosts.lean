import LongTable.P_mwv1wkid_o4yjf7
set_option autoImplicit false
noncomputable section
namespace YangMills

/-! Axis boosts as proper orthochronous Lorentz maps, a proof of `BoostsBelow m` for
every `m > 0`, and hence the equivalence, under W0, of the mass-shell and Hamiltonian
forms of the mass gap. -/

open ContinuousLinearMap Real Matrix

theorem spatial_sq (x : Spacetime) : ‖spatial x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [spatial, sq_abs]

theorem time_eq (x : Spacetime) : time x = x 3 := rfl

theorem msq_eq (x : Spacetime) : minkowskiSquare x = x 3 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  rw [minkowskiSquare, spatial_sq, time_eq]

theorem cone_iff (x : Spacetime) :
    x ∈ forwardCone ↔ 0 ≤ x 3 ∧ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ x 3 ^ 2 := by
  change ‖spatial x‖ ≤ time x ↔ _
  rw [← spatial_sq, time_eq]
  constructor
  · intro h; exact ⟨(norm_nonneg _).trans h, pow_le_pow_left₀ (norm_nonneg _) h 2⟩
  · rintro ⟨h0, h⟩; exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 h

/-- The matrix of the boost along spatial axis `i` with rapidity `η`. -/
def boostMatrix (i : Fin 3) (η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => if a = b then (if a = i.castSucc ∨ a = 3 then cosh η else 1)
    else if (a = i.castSucc ∧ b = 3) ∨ (a = 3 ∧ b = i.castSucc) then sinh η else 0

theorem det_boostMatrix (i : Fin 3) (η : ℝ) : (boostMatrix i η).det = 1 := by
  have h := cosh_sq_sub_sinh_sq η
  fin_cases i <;>
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, boostMatrix, Fin.succAbove] <;>
  linear_combination h

theorem transpose_boostMatrix (i : Fin 3) (η : ℝ) : (boostMatrix i η)ᵀ = boostMatrix i η := by
  ext a b
  simp only [Matrix.transpose_apply, boostMatrix, Matrix.of_apply]
  by_cases h : a = b
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte]; congr 1; apply propext; tauto

/-- The boost along spatial axis `i` with rapidity `η`. -/
def boost (i : Fin 3) (η : ℝ) : Spacetime →L[ℝ] Spacetime :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (boostMatrix i η)

theorem boost_apply (i : Fin 3) (η : ℝ) (x : Spacetime) (j : Fin 4) :
    boost i η x j = if j = i.castSucc then cosh η * x i.castSucc + sinh η * x 3
      else if j = 3 then sinh η * x i.castSucc + cosh η * x 3 else x j := by
  change (boostMatrix i η *ᵥ x.ofLp) j = _
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, boostMatrix]


theorem castSucc_ne (i : Fin 3) : i.castSucc ≠ (3 : Fin 4) := by fin_cases i <;> decide

theorem boost_boost_neg (i : Fin 3) (η : ℝ) (x : Spacetime) :
    boost i η (boost i (-η) x) = x := by
  have hi := castSucc_ne i
  have h := cosh_sq_sub_sinh_sq η
  ext j
  by_cases h1 : j = i.castSucc
  · subst h1
    simp only [boost_apply, ↓reduceIte, Ne.symm hi, cosh_neg, sinh_neg]
    linear_combination x i.castSucc * h
  by_cases h2 : j = 3
  · subst h2
    simp only [boost_apply, ↓reduceIte, Ne.symm hi, cosh_neg, sinh_neg]
    linear_combination x 3 * h
  · simp only [boost_apply, h1, h2, ↓reduceIte]

theorem boost_neg_boost (i : Fin 3) (η : ℝ) (x : Spacetime) :
    boost i (-η) (boost i η x) = x := by
  simpa only [neg_neg] using boost_boost_neg i (-η) x

theorem msq_boost (i : Fin 3) (η : ℝ) (x : Spacetime) :
    minkowskiSquare (boost i η x) = minkowskiSquare x := by
  have h := cosh_sq_sub_sinh_sq η
  rw [msq_eq, msq_eq]
  fin_cases i <;> simp [boost_apply]
  · linear_combination (x 3 ^ 2 - x 0 ^ 2) * h
  · linear_combination (x 3 ^ 2 - x 1 ^ 2) * h
  · linear_combination (x 3 ^ 2 - x 2 ^ 2) * h

theorem time_boost_nonneg (i : Fin 3) (η : ℝ) {x : Spacetime} (hx : x ∈ forwardCone) :
    0 ≤ boost i η x 3 := by
  rw [cone_iff] at hx
  have hc : 0 ≤ cosh η := (cosh_pos η).le
  have hs : sinh η ^ 2 ≤ cosh η ^ 2 := by nlinarith [cosh_sq_sub_sinh_sq η]
  have ha : x i.castSucc ^ 2 ≤ x 3 ^ 2 := by
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hp : (sinh η * x i.castSucc) ^ 2 ≤ (cosh η * x 3) ^ 2 := by
    rw [mul_pow, mul_pow]; exact mul_le_mul hs ha (sq_nonneg _) (sq_nonneg _)
  have := (abs_le_of_sq_le_sq' hp (mul_nonneg hc hx.1)).1
  simp only [boost_apply, (castSucc_ne i).symm, ↓reduceIte]
  linarith

theorem boost_mem_cone (i : Fin 3) (η : ℝ) {x : Spacetime} (hx : x ∈ forwardCone) :
    boost i η x ∈ forwardCone := by
  have h0 := time_boost_nonneg i η hx
  have hm := msq_boost i η x
  rw [cone_iff] at hx ⊢
  rw [msq_eq, msq_eq] at hm
  exact ⟨h0, by linarith⟩

theorem boost_mem_cone_iff (i : Fin 3) (η : ℝ) (x : Spacetime) :
    boost i η x ∈ forwardCone ↔ x ∈ forwardCone := by
  refine ⟨fun h => ?_, boost_mem_cone i η⟩
  have := boost_mem_cone i (-η) h
  rwa [boost_neg_boost] at this

theorem det_boost (i : Fin 3) (η : ℝ) : LinearMap.det (boost i η).toLinearMap = 1 := by
  change LinearMap.det (Matrix.toLin (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis (boostMatrix i η)) = 1
  rw [LinearMap.det_toLin, det_boostMatrix]

/-- The boost along axis `i` with rapidity `η`, as a proper orthochronous Lorentz map. -/
def boostL (i : Fin 3) (η : ℝ) : ProperLorentz :=
  ⟨⟨boost i η, boost i (-η), ContinuousLinearMap.ext fun x => boost_boost_neg i η x,
    ContinuousLinearMap.ext fun x => boost_neg_boost i η x⟩,
    det_boost i η, msq_boost i η, boost_mem_cone_iff i η⟩

theorem onMomenta_boostL (i : Fin 3) (η : ℝ) : (boostL i η).onMomenta = boost i (-η) := by
  change adjoint (boost i (-η)) = boost i (-η)
  rw [boost, ← star_eq_adjoint, ← map_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, transpose_boostMatrix]

/-- The product of two proper orthochronous Lorentz maps. -/
def plMul (a b : ProperLorentz) : ProperLorentz :=
  ⟨a.val * b.val, by
    rw [Units.val_mul, ContinuousLinearMap.toLinearMap_mul, map_mul, a.2.1, b.2.1, mul_one],
    fun x => (a.2.2.1 (b.val.val x)).trans (b.2.2.1 x),
    fun x => (a.2.2.2 (b.val.val x)).trans (b.2.2.2 x)⟩

theorem onMomenta_plMul (a b : ProperLorentz) (k : Spacetime) :
    (plMul a b).onMomenta k = a.onMomenta (b.onMomenta k) := by
  change adjoint ((a.val * b.val)⁻¹).val k = _
  rw [_root_.mul_inv_rev, Units.val_mul, ContinuousLinearMap.mul_def, adjoint_comp]
  rfl

/-- `k'` is the image of `k` under the momentum action of some Lorentz map. -/
def Reach (k k' : Spacetime) : Prop := ∃ Λ : ProperLorentz, Λ.onMomenta k = k'

theorem Reach.trans {k₁ k₂ k₃ : Spacetime} (h₁ : Reach k₁ k₂) (h₂ : Reach k₂ k₃) :
    Reach k₁ k₃ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨plMul b a, by rw [onMomenta_plMul, ha, hb]⟩

theorem reach_boost (i : Fin 3) (η : ℝ) (k : Spacetime) : Reach k (boost i η k) :=
  ⟨boostL i (-η), by rw [onMomenta_boostL, neg_neg]⟩


theorem boost_log_apply (i : Fin 3) {w : ℝ} (hw : 0 < w) (x : Spacetime) :
    boost i (log w) x i.castSucc =
      (w * (x 3 + x i.castSucc) - (x 3 - x i.castSucc) / w) / 2 ∧
    boost i (log w) x 3 = (w * (x 3 + x i.castSucc) + (x 3 - x i.castSucc) / w) / 2 ∧
    ∀ l, l ≠ i.castSucc → l ≠ 3 → boost i (log w) x l = x l := by
  have hi := castSucc_ne i
  refine ⟨?_, ?_, fun l h1 h2 => by simp only [boost_apply, h1, h2, ↓reduceIte]⟩ <;>
  · simp only [boost_apply, ↓reduceIte, Ne.symm hi, cosh_log hw, sinh_log hw]
    field_simp
    ring

theorem balance_aux {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    √p / √q * q = √p * √q ∧ p / (√p / √q) = √p * √q := by
  have sp := Real.sqrt_pos.2 hp
  have sq := Real.sqrt_pos.2 hq
  constructor
  · rw [div_mul_eq_mul_div, div_eq_iff sq.ne', mul_assoc, Real.mul_self_sqrt hq.le]
  · rw [div_div_eq_mul_div, div_eq_iff sp.ne', mul_right_comm, Real.mul_self_sqrt hp.le]

/-- With `w = √p / √q`, the boost along `i` zeroes that coordinate. -/
theorem boost_balance (i : Fin 3) (x : Spacetime) (hp : 0 < x 3 - x i.castSucc)
    (hq : 0 < x 3 + x i.castSucc) :
    ∃ y, Reach x y ∧ y i.castSucc = 0 ∧ 0 < y 3 ∧
      y 3 ^ 2 = x 3 ^ 2 - x i.castSucc ^ 2 ∧ ∀ l, l ≠ i.castSucc → l ≠ 3 → y l = x l := by
  have hw : 0 < √(x 3 - x i.castSucc) / √(x 3 + x i.castSucc) :=
    div_pos (Real.sqrt_pos.2 hp) (Real.sqrt_pos.2 hq)
  obtain ⟨e1, e2⟩ := balance_aux hp hq
  obtain ⟨h1, h2, h3⟩ := boost_log_apply i hw x
  rw [e1, e2] at h1 h2
  refine ⟨_, reach_boost i _ x, ?_, ?_, ?_, h3⟩
  · rw [h1]; ring
  · rw [h2]; have := Real.sqrt_pos.2 hp; have := Real.sqrt_pos.2 hq; positivity
  · rw [h2, add_self_div_two, mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]; ring

theorem final_step (i : Fin 3) {m : ℝ} (hm : 0 < m) (x : Spacetime) (h3 : 0 < x 3)
    (ha : x i.castSucc ^ 2 ≤ x 3 ^ 2) (hb : x 3 ^ 2 - x i.castSucc ^ 2 < m ^ 2) :
    ∃ y, Reach x y ∧ 0 < y 3 ∧ y 3 < m := by
  have habs := abs_le_of_sq_le_sq' ha h3.le
  rcases habs.2.lt_or_eq with hlt | heq
  · rcases habs.1.lt_or_eq with hlt' | heq'
    · obtain ⟨y, hy, -, hy3, hy3', -⟩ := boost_balance i x (by linarith) (by linarith)
      refine ⟨y, hy, hy3, ?_⟩
      nlinarith
    · have hw : 0 < x 3 * 2 / m := by positivity
      obtain ⟨-, h2, -⟩ := boost_log_apply i hw x
      refine ⟨_, reach_boost i (log (x 3 * 2 / m)) x, ?_⟩
      rw [h2, ← heq']
      field_simp
      constructor <;> nlinarith
  · have hw : 0 < m / (x 3 * 2) := by positivity
    obtain ⟨-, h2, -⟩ := boost_log_apply i hw x
    refine ⟨_, reach_boost i (log (m / (x 3 * 2))) x, ?_⟩
    rw [h2, heq]
    field_simp
    constructor <;> nlinarith

theorem pq_of_sq_lt {a t : ℝ} (h : a ^ 2 < t ^ 2) (ht : 0 < t) : 0 < t - a ∧ 0 < t + a := by
  have := abs_lt_of_sq_lt_sq' h ht.le
  constructor <;> linarith [this.1, this.2]

theorem sq_pos_of_ne {a : ℝ} (h : a ≠ 0) : 0 < a ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))

/-- Each nonzero forward momentum below the shell `m > 0` has energy in `(0, m)` in some frame. -/
theorem boostsBelow {m : ℝ} (hm : 0 < m) : BoostsBelow m := by
  intro k hk hk0 hkm
  rw [cone_iff] at hk
  rw [msq_eq] at hkm
  obtain ⟨ht0, hS⟩ := hk
  have q0 := sq_nonneg (k 0)
  have q1 := sq_nonneg (k 1)
  have q2 := sq_nonneg (k 2)
  have ht : 0 < k 3 := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    exfalso; apply hk0
    rw [← h] at hS
    have e0 : k 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith)
    have e1 : k 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith)
    have e2 : k 2 = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith)
    ext j; fin_cases j
    exacts [e0, e1, e2, h.symm]
  suffices ∃ y, Reach k y ∧ 0 < y 3 ∧ y 3 < m by
    obtain ⟨y, ⟨Λ, hΛ⟩, h1, h2⟩ := this
    exact ⟨Λ, by rw [hΛ]; exact ⟨h1, h2⟩⟩
  have c0 : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
  have c1 : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
  have c2 : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  by_cases h0 : k 0 = 0
  · by_cases h1 : k 1 = 0
    · exact final_step 2 hm k ht (by rw [c2]; nlinarith) (by rw [c2]; nlinarith)
    · have p1 := sq_pos_of_ne h1
      obtain ⟨y, hy, hy2, hy3, hy3', hyo⟩ :=
        boost_balance 2 k (pq_of_sq_lt (by rw [c2]; nlinarith) ht).1 (pq_of_sq_lt (by
          rw [c2]; nlinarith) ht).2
      rw [c2] at hy2 hy3' hyo
      have y0 := hyo 0 (by decide) (by decide)
      have y1 := hyo 1 (by decide) (by decide)
      obtain ⟨z, hz, hz1, hz2⟩ := final_step 1 hm y hy3 (by rw [c1, y1]; nlinarith)
        (by rw [c1, y1]; nlinarith)
      exact ⟨z, hy.trans hz, hz1, hz2⟩
  · have p0 := sq_pos_of_ne h0
    obtain ⟨y, hy, hy1, hy3, hy3', hyo⟩ :=
      boost_balance 1 k (pq_of_sq_lt (by rw [c1]; nlinarith) ht).1 (pq_of_sq_lt (by
        rw [c1]; nlinarith) ht).2
    rw [c1] at hy1 hy3' hyo
    have y0 := hyo 0 (by decide) (by decide)
    have y2 := hyo 2 (by decide) (by decide)
    obtain ⟨z, hz, hz2, hz3, hz3', hzo⟩ :=
      boost_balance 2 y (pq_of_sq_lt (by rw [c2, y2]; nlinarith) hy3).1 (pq_of_sq_lt (by
        rw [c2, y2]; nlinarith) hy3).2
    rw [c2] at hz2 hz3' hzo
    have z0 := hzo 0 (by decide) (by decide)
    rw [y2] at hz3'
    obtain ⟨u, hu, hu1, hu2⟩ := final_step 0 hm z hz3 (by rw [c0, z0, y0]; nlinarith)
      (by rw [c0, z0, y0]; nlinarith)
    exact ⟨u, (hy.trans hz).trans hu, hu1, hu2⟩

/-- Under W0, the Hamiltonian form of the gap gives the mass-shell form. -/
theorem WightmanTheory.HasEnergyGap.massGap_of_W0 {H : HilbertSpace} {Labels : FieldLabels}
    {theory : WightmanTheory H Labels} {m : ℝ} (h : theory.HasEnergyGap m) (w0 : theory.W0) :
    theory.HasMassGap m :=
  h.massGap w0 (boostsBelow h.1)

/-- Under W0, the mass-shell and Hamiltonian forms of the gap are equivalent. -/
theorem WightmanTheory.hasMassGap_iff_hasEnergyGap {H : HilbertSpace} {Labels : FieldLabels}
    {theory : WightmanTheory H Labels} (w0 : theory.W0) (m : ℝ) :
    theory.HasMassGap m ↔ theory.HasEnergyGap m :=
  ⟨fun h => h.energyGap w0, fun h => h.massGap_of_W0 w0⟩

end YangMills

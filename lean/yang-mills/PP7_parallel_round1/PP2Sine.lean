import LongTable.PP2Green2

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5a, session 1.
The discrete sine basis of the Dirichlet box (namespace `PP2Target`).

Notation: N = `boxN n k`, M = N + 1, ε = `spacing n`. (NB: dirGreen = dirOp⁻¹; the covariance of
exp(−dirAction/2) is ε⁻²·dirGreen.) For a mode index k ∈ ℕ (unrelated to the box-size k; mode
number k+1, so k ∈ Fin N covers modes 1..N) and t ∈ ℝ,
`sineFn N k t = √(2/M) · sin(π t (k+1)/M)`, and the 1-D sine vector is
`sineVec N k i = sineFn N k (i+1)` (i ∈ Fin N), i.e. e_k(i) = √(2/(N+1)) sin(π(i+1)(k+1)/(N+1)).
The 1-D eigenvalue is `sineEig N k = 4 sin²(π(k+1)/(2M))`. In 2-D,
`sineVec2 K x = e_{K.1}(x.1) e_{K.2}(x.2)` (K, x ∈ DSite n k) and
`dirEig n k m₀ K = ε⁻² (sineEig N K.1 + sineEig N K.2) + m₀²`.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `two_sin_mul_sum_cos`: 2 sin(φ/2) Σ_{m<M} cos(mφ) = sin((M − ½)φ) + sin(φ/2) (telescoping).
* `sum_cos_int`: for p ∈ ℤ, 0 < |p| < 2M: 2 Σ_{m<M} cos(m pπ/M) = 1 − cos(pπ).
* `sum_sin_sin`: for 1 ≤ a, b ≤ N: Σ_{m<N+1} sin(πma/M) sin(πmb/M) = [a = b] · M/2.
* `sineVec_orthonormal`: for j, k < N: Σ_i e_j(i) e_k(i) = δ_jk.
* `lap1_sineVec`: the 1-D Dirichlet second difference (L u)(i) = 2u(i) − u(i−1) − u(i+1)
  (u(−1) = u(N) = 0), `lap1`, satisfies L e_k = 4 sin²(π(k+1)/(2(N+1))) e_k.
* `sineEig_pos`: 0 < sineEig N k for k < N.
* `dirOp_mulVec_apply`: (dirOp *ᵥ v) x = ε⁻² (four-neighbour second difference of `ext v`) + m₀² v x.
* `sineVec2_orthonormal`: Σ_x e_K(x) e_L(x) = δ_KL on the box.
* `dirOp_mulVec_sineVec2`: dirOp *ᵥ e_K = dirEig K • e_K, with
  dirEig K = (4/ε²)(sin²(π(K₁+1)/(2M)) + sin²(π(K₂+1)/(2M))) + m₀² (`dirEig_eq`).
* `dirEig_pos`: 0 < dirEig K (any m₀, even m₀ = 0).
* `sineMat_mul_transpose`, `sineMat_transpose_mul`: the matrix U x K = e_K(x) is orthogonal.
* `dirGreen_spectral`: dirGreen x y = Σ_K e_K(x) e_K(y) / dirEig K.

NOT formalized here: consequences of the spectral formula (positivity bounds, comparison with the
infinite-volume `freeVar`, decay estimates); the sine basis of boxes other than the square
Dirichlet box of `P_mww4cze7_bk8bxu`.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset

noncomputable section

namespace PP2Target

/-! ## Trigonometric sums -/

/-- Telescoping: 2 sin(φ/2) Σ_{m<M} cos(mφ) = sin((M − ½)φ) + sin(φ/2). -/
theorem two_sin_mul_sum_cos (φ : ℝ) (M : ℕ) :
    2 * sin (φ / 2) * ∑ m ∈ range M, cos (m * φ) = sin ((M - 1 / 2) * φ) + sin (φ / 2) := by
  induction M with
  | zero =>
    simp only [Finset.sum_range_zero, mul_zero, Nat.cast_zero]
    rw [show ((0 : ℝ) - 1 / 2) * φ = -(φ / 2) by ring, Real.sin_neg]; ring
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    rw [show ((M : ℝ) + 1 - 1 / 2) * φ = M * φ + φ / 2 by ring,
      show ((M : ℝ) - 1 / 2) * φ = M * φ - φ / 2 by ring, Real.sin_add, Real.sin_sub]
    ring

/-- For p ∈ ℤ with 0 < |p| < 2M: 2 Σ_{m<M} cos(m pπ/M) = 1 − cos(pπ). -/
theorem sum_cos_int (M : ℕ) (hM : 0 < M) (p : ℤ) (hp0 : p ≠ 0) (hp : |p| < 2 * M) :
    2 * ∑ m ∈ range M, cos (m * (p * π / M)) = 1 - cos (p * π) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨hl, hu⟩ := abs_lt.mp hp
  have hl' : -(2 * (M : ℝ)) < p := by exact_mod_cast hl
  have hu' : (p : ℝ) < 2 * M := by exact_mod_cast hu
  have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  set φ := p * π / M with hφ
  have hs : sin (φ / 2) ≠ 0 := by
    have hpi := Real.pi_pos
    have e : φ / 2 = p * π / (2 * M) := by rw [hφ]; field_simp
    rw [e]
    intro h
    rw [Real.sin_eq_zero_iff_of_lt_of_lt] at h
    · rcases div_eq_zero_iff.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact hp0' h
        · linarith
      · linarith
    · rw [lt_div_iff₀ (by positivity)]; nlinarith
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
  have key := two_sin_mul_sum_cos φ M
  have h1 : sin ((M - 1 / 2) * φ) = -cos (p * π) * sin (φ / 2) := by
    rw [show ((M : ℝ) - 1 / 2) * φ = p * π - φ / 2 by rw [hφ]; field_simp,
      Real.sin_sub, Real.sin_int_mul_pi]
    ring
  rw [h1] at key
  apply mul_left_cancel₀ hs
  linear_combination key

/-- The basic orthogonality of sines: for 1 ≤ a, b ≤ N,
Σ_{m<N+1} sin(π m a/(N+1)) sin(π m b/(N+1)) = [a = b] (N+1)/2. -/
theorem sum_sin_sin (N a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ N) (hb : 1 ≤ b) (hb' : b ≤ N) :
    ∑ m ∈ range (N + 1), sin (π * m * a / (N + 1)) * sin (π * m * b / (N + 1)) =
      if a = b then ((N : ℝ) + 1) / 2 else 0 := by
  have hpt : ∀ m : ℕ, sin (π * m * a / (N + 1)) * sin (π * m * b / (N + 1)) =
      (cos (m * ((((a : ℤ) - b : ℤ) : ℝ) * π / ((N + 1 : ℕ) : ℝ))) -
        cos (m * ((((a : ℤ) + b : ℤ) : ℝ) * π / ((N + 1 : ℕ) : ℝ)))) / 2 := by
    intro m
    push_cast
    rw [show (m : ℝ) * ((a - b) * π / (N + 1)) = π * m * a / (N + 1) - π * m * b / (N + 1) by ring,
      show (m : ℝ) * ((a + b) * π / (N + 1)) = π * m * a / (N + 1) + π * m * b / (N + 1) by ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [Finset.sum_congr rfl fun m _ => hpt m, ← Finset.sum_div, Finset.sum_sub_distrib]
  have h2 := sum_cos_int (N + 1) (by omega) ((a : ℤ) + b) (by omega)
    (abs_lt.mpr ⟨by push_cast; omega, by push_cast; omega⟩)
  split_ifs with hab
  · subst hab
    have e0 : ∀ m : ℕ, cos (m * ((((a : ℤ) - a : ℤ) : ℝ) * π / ((N + 1 : ℕ) : ℝ))) = 1 := by
      intro m; simp
    rw [Finset.sum_congr rfl fun m _ => e0 m]
    have e2 : (((a : ℤ) + a : ℤ) : ℝ) * π = (a : ℕ) * (2 * π) := by push_cast; ring
    have h3 : cos ((((a : ℤ) + a : ℤ) : ℝ) * π) = 1 := by rw [e2, Real.cos_nat_mul_two_pi]
    rw [h3] at h2
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [this] at h2 ⊢
    linarith
  · have h1 := sum_cos_int (N + 1) (by omega) ((a : ℤ) - b) (by omega)
      (abs_lt.mpr ⟨by push_cast; omega, by push_cast; omega⟩)
    have e : (((a : ℤ) + b : ℤ) : ℝ) * π = (((a : ℤ) - b : ℤ) : ℝ) * π + (b : ℕ) * (2 * π) := by
      push_cast; ring
    have h3 : cos ((((a : ℤ) + b : ℤ) : ℝ) * π) = cos ((((a : ℤ) - b : ℤ) : ℝ) * π) := by
      rw [e, Real.cos_add_nat_mul_two_pi]
    rw [h3] at h2
    linarith

/-! ## The 1-D sine basis -/

/-- `sineFn N k t = √(2/(N+1)) sin(π t (k+1)/(N+1))`. -/
def sineFn (N k : ℕ) (t : ℝ) : ℝ := √(2 / ((N : ℝ) + 1)) * sin (π * t * ((k : ℝ) + 1) / (N + 1))

/-- The 1-D Dirichlet sine vector e_k(i) = √(2/(N+1)) sin(π(i+1)(k+1)/(N+1)). -/
def sineVec (N k : ℕ) (i : Fin N) : ℝ := sineFn N k (((i : ℕ) : ℝ) + 1)

/-- The 1-D eigenvalue 4 sin²(π(k+1)/(2(N+1))). -/
def sineEig (N k : ℕ) : ℝ := 4 * sin (π * ((k : ℝ) + 1) / (2 * ((N : ℝ) + 1))) ^ 2

theorem sineFn_zero (N k : ℕ) : sineFn N k 0 = 0 := by simp [sineFn]

theorem sineFn_end (N k : ℕ) : sineFn N k ((N : ℝ) + 1) = 0 := by
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  rw [sineFn, show π * ((N : ℝ) + 1) * ((k : ℝ) + 1) / (N + 1) = ((k + 1 : ℕ) : ℝ) * π by
    push_cast; field_simp, Real.sin_nat_mul_pi, mul_zero]

/-- **Orthonormality of the 1-D sine basis:** Σ_i e_j(i) e_k(i) = δ_jk for j, k < N. -/
theorem sineVec_orthonormal (N j k : ℕ) (hj : j < N) (hk : k < N) :
    ∑ i : Fin N, sineVec N j i * sineVec N k i = if j = k then 1 else 0 := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hs : √(2 / ((N : ℝ) + 1)) * √(2 / ((N : ℝ) + 1)) = 2 / ((N : ℝ) + 1) :=
    Real.mul_self_sqrt (by positivity)
  have hpt : ∀ i : ℕ, sineFn N j ((i : ℝ) + 1) * sineFn N k ((i : ℝ) + 1) =
      2 / ((N : ℝ) + 1) * (sin (π * ((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) / (N + 1)) *
        sin (π * ((i + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) / (N + 1))) := by
    intro i
    rw [← hs, sineFn, sineFn]
    push_cast
    ring
  simp only [sineVec]
  rw [Fin.sum_univ_eq_sum_range (fun i => sineFn N j ((i : ℝ) + 1) * sineFn N k ((i : ℝ) + 1)),
    Finset.sum_congr rfl fun i _ => hpt i, ← Finset.mul_sum]
  have h := sum_sin_sin N (j + 1) (k + 1) (by omega) (by omega) (by omega) (by omega)
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.sin_zero, add_zero] at h
  rw [h]
  by_cases hjk : j = k
  · subst hjk; simp only [↓reduceIte]; field_simp
  · simp [hjk]

/-- The 1-D Dirichlet second difference (L u)(i) = 2u(i) − u(i−1) − u(i+1), u(−1) = u(N) = 0. -/
def lap1 (N : ℕ) (u : Fin N → ℝ) (i : Fin N) : ℝ :=
  2 * u i - (if h : 0 < (i : ℕ) then u ⟨(i : ℕ) - 1, by omega⟩ else 0)
    - (if h : (i : ℕ) + 1 < N then u ⟨(i : ℕ) + 1, h⟩ else 0)

/-- The three-point identity for `sineFn`. -/
theorem sineFn_three_point (N k : ℕ) (t : ℝ) :
    2 * sineFn N k t - sineFn N k (t - 1) - sineFn N k (t + 1) = sineEig N k * sineFn N k t := by
  set φ := π * ((k : ℝ) + 1) / (N + 1) with hφ
  have hc : cos φ = 1 - 2 * sin (φ / 2) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    linear_combination h + 2 * Real.sin_sq_add_cos_sq (φ / 2)
  have e1 : π * (t - 1) * ((k : ℝ) + 1) / (N + 1) = π * t * ((k : ℝ) + 1) / (N + 1) - φ := by
    rw [hφ]; ring
  have e2 : π * (t + 1) * ((k : ℝ) + 1) / (N + 1) = π * t * ((k : ℝ) + 1) / (N + 1) + φ := by
    rw [hφ]; ring
  have e3 : π * ((k : ℝ) + 1) / (2 * ((N : ℝ) + 1)) = φ / 2 := by
    rw [hφ, mul_comm (2 : ℝ), ← div_div]
  simp only [sineFn, sineEig]
  rw [e1, e2, e3, Real.sin_sub, Real.sin_add, hc]
  ring

/-- **The 1-D eigen-equation:** L e_k = 4 sin²(π(k+1)/(2(N+1))) e_k. -/
theorem lap1_sineVec (N k : ℕ) (i : Fin N) :
    lap1 N (sineVec N k) i = sineEig N k * sineVec N k i := by
  have hl : (if h : 0 < (i : ℕ) then sineVec N k ⟨(i : ℕ) - 1, by omega⟩ else 0) =
      sineFn N k ((((i : ℕ) : ℝ) + 1) - 1) := by
    split_ifs with h
    · simp only [sineVec]
      rw [Nat.cast_sub (by omega)]
      push_cast; ring_nf
    · have : (i : ℕ) = 0 := by omega
      rw [this]; simp [sineFn_zero]
  have hr : (if h : (i : ℕ) + 1 < N then sineVec N k ⟨(i : ℕ) + 1, h⟩ else 0) =
      sineFn N k ((((i : ℕ) : ℝ) + 1) + 1) := by
    split_ifs with h
    · simp only [sineVec]; push_cast; ring_nf
    · have : (i : ℕ) + 1 = N := by omega
      have h' : ((i : ℕ) : ℝ) + 1 = N := by exact_mod_cast this
      rw [h', sineFn_end]
  rw [lap1, hl, hr]
  exact sineFn_three_point N k _

theorem sineEig_pos (N k : ℕ) (hk : k < N) : 0 < sineEig N k := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hk' : (k : ℝ) + 1 < (N : ℝ) + 1 := by exact_mod_cast (by omega : k + 1 < N + 1)
  have h : 0 < sin (π * ((k : ℝ) + 1) / (2 * ((N : ℝ) + 1))) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  unfold sineEig; positivity

/-! ## The Dirichlet operator acting on a field -/

variable {n k : ℕ}

theorem vecMulVec_self_mulVec_apply (u w : DField n k) (x : DSite n k) :
    (vecMulVec u u *ᵥ w) x = u x * (u ⬝ᵥ w) := by
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_assoc]

theorem sum_ind_sub_mul (S : Finset (ℤ × ℤ)) (a b : ℤ × ℤ) (ha : a ∈ S) (hb : b ∈ S)
    (g : ℤ × ℤ → ℝ) :
    ∑ p ∈ S, ((if p = a then (1 : ℝ) else 0) - (if p = b then 1 else 0)) * g p = g a - g b := by
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    ite_eq_left ha, ite_eq_left hb]

theorem ext_site (v : DField n k) (x : DSite n k) : ext v (site x) = v x := by
  have h1 := x.1.isLt
  have h2 := x.2.isLt
  have h : 0 ≤ (site x).1 ∧ (site x).1 < boxN n k ∧ 0 ≤ (site x).2 ∧ (site x).2 < boxN n k := by
    simp only [site]; omega
  rw [ext, dite_eq_left h]
  congr 1

/-- **dirOp on a field:** (dirOp *ᵥ v) x = ε⁻² (2v(x) − v(x − e₁) − v(x + e₁) + 2v(x) − v(x − e₂)
− v(x + e₂)) + m₀² v(x), with v extended by zero outside the box. -/
theorem dirOp_mulVec_apply (m₀ : ℝ) (v : DField n k) (x : DSite n k) :
    (dirOp n k m₀ *ᵥ v) x =
      (spacing n ^ 2)⁻¹ *
        ((2 * v x - ext v ((site x).1 - 1, (site x).2) - ext v ((site x).1 + 1, (site x).2))
          + (2 * v x - ext v ((site x).1, (site x).2 - 1) - ext v ((site x).1, (site x).2 + 1)))
      + m₀ ^ 2 * v x := by
  have hH : ∀ p : ℤ × ℤ, (bondH p : DField n k) ⬝ᵥ v = ext v (p.1 + 1, p.2) - ext v p :=
    fun p => bondVec_dot _ _ _
  have hV : ∀ p : ℤ × ℤ, (bondV p : DField n k) ⬝ᵥ v = ext v (p.1, p.2 + 1) - ext v p :=
    fun p => bondVec_dot _ _ _
  simp only [dirOp, add_mulVec, smul_mulVec, sum_mulVec, one_mulVec, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, vecMulVec_self_mulVec_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  simp only [hH, hV, bondH_apply, bondV_apply]
  rw [sum_ind_sub_mul _ _ _ (site_sub1_mem x) (site_mem x) (fun p => ext v (p.1 + 1, p.2) - ext v p),
    sum_ind_sub_mul _ _ _ (site_sub2_mem x) (site_mem x) (fun p => ext v (p.1, p.2 + 1) - ext v p)]
  simp only [sub_add_cancel, Prod.mk.eta, ext_site]
  ring

/-! ## The 2-D sine basis -/

/-- The 2-D Dirichlet sine vector e_K(x) = e_{K₁}(x₁) e_{K₂}(x₂). -/
def sineVec2 (K : DSite n k) : DField n k :=
  fun x => sineVec (boxN n k) K.1 x.1 * sineVec (boxN n k) K.2 x.2

/-- The eigenvalue ε⁻² (sineEig K₁ + sineEig K₂) + m₀². -/
def dirEig (n k : ℕ) (m₀ : ℝ) (K : DSite n k) : ℝ :=
  (spacing n ^ 2)⁻¹ * (sineEig (boxN n k) K.1 + sineEig (boxN n k) K.2) + m₀ ^ 2

theorem dirEig_eq (m₀ : ℝ) (K : DSite n k) :
    dirEig n k m₀ K = 4 / spacing n ^ 2 *
      (sin (π * (((K.1 : ℕ) : ℝ) + 1) / (2 * ((boxN n k : ℝ) + 1))) ^ 2
        + sin (π * (((K.2 : ℕ) : ℝ) + 1) / (2 * ((boxN n k : ℝ) + 1))) ^ 2) + m₀ ^ 2 := by
  simp only [dirEig, sineEig]; ring

theorem dirEig_pos (m₀ : ℝ) (K : DSite n k) : 0 < dirEig n k m₀ K := by
  have h1 := sineEig_pos (boxN n k) K.1 K.1.isLt
  have h2 := sineEig_pos (boxN n k) K.2 K.2.isLt
  have hs := spacing_pos n
  exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) (add_pos h1 h2)) (sq_nonneg _)

/-- **Orthonormality of the 2-D sine basis.** -/
theorem sineVec2_orthonormal (K L : DSite n k) :
    ∑ x : DSite n k, sineVec2 K x * sineVec2 L x = if K = L then 1 else 0 := by
  have hpt : ∀ x : DSite n k, sineVec2 K x * sineVec2 L x =
      (sineVec (boxN n k) K.1 x.1 * sineVec (boxN n k) L.1 x.1) *
        (sineVec (boxN n k) K.2 x.2 * sineVec (boxN n k) L.2 x.2) := by
    intro x; simp only [sineVec2]; ring
  rw [Finset.sum_congr rfl fun x _ => hpt x, Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum, sineVec_orthonormal _ _ _ K.1.isLt L.1.isLt,
    sineVec_orthonormal _ _ _ K.2.isLt L.2.isLt]
  by_cases h1 : (K.1 : ℕ) = L.1 <;> by_cases h2 : (K.2 : ℕ) = L.2 <;>
    simp [h1, h2, Prod.ext_iff, Fin.ext_iff]

/-- The zero extension of e_K on the closed box [−1, N]²: e_K vanishes on the boundary. -/
theorem ext_sineVec2 (K : DSite n k) (q : ℤ × ℤ) (h1 : -1 ≤ q.1) (h2 : q.1 ≤ boxN n k)
    (h3 : -1 ≤ q.2) (h4 : q.2 ≤ boxN n k) :
    ext (sineVec2 K) q =
      sineFn (boxN n k) K.1 ((q.1 : ℝ) + 1) * sineFn (boxN n k) K.2 ((q.2 : ℝ) + 1) := by
  unfold ext
  split_ifs with h
  · simp only [sineVec2, sineVec]
    have c1 : (((q.1.toNat : ℕ) : ℝ)) = (q.1 : ℝ) := by
      rw [show ((q.1.toNat : ℕ) : ℝ) = (((q.1.toNat : ℕ) : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg h.1]
    have c2 : (((q.2.toNat : ℕ) : ℝ)) = (q.2 : ℝ) := by
      rw [show ((q.2.toNat : ℕ) : ℝ) = (((q.2.toNat : ℕ) : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg h.2.2.1]
    rw [c1, c2]
  · have hN : ((boxN n k : ℤ) : ℝ) = (boxN n k : ℝ) := by norm_cast
    rcases (by omega : q.1 = -1 ∨ q.1 = boxN n k ∨ q.2 = -1 ∨ q.2 = boxN n k) with
      e | e | e | e
    · rw [e]; push_cast; rw [neg_add_cancel, sineFn_zero, zero_mul]
    · rw [e, hN, sineFn_end, zero_mul]
    · rw [e]; push_cast; rw [neg_add_cancel, sineFn_zero, mul_zero]
    · rw [e, hN, sineFn_end, mul_zero]

/-- **The 2-D eigen-equation:** dirOp *ᵥ e_K = dirEig K • e_K. -/
theorem dirOp_mulVec_sineVec2 (m₀ : ℝ) (K : DSite n k) :
    dirOp n k m₀ *ᵥ sineVec2 K = dirEig n k m₀ K • sineVec2 K := by
  ext x
  have b1 := x.1.isLt
  have b2 := x.2.isLt
  set a : ℝ := ((x.1 : ℕ) : ℝ) + 1
  set b : ℝ := ((x.2 : ℕ) : ℝ) + 1
  have hv : sineVec2 K x = sineFn (boxN n k) K.1 a * sineFn (boxN n k) K.2 b := rfl
  have a1 : ext (sineVec2 K) ((site x).1 - 1, (site x).2) =
      sineFn (boxN n k) K.1 (a - 1) * sineFn (boxN n k) K.2 b := by
    rw [ext_sineVec2 K _ (by simp only [site]; omega) (by simp only [site]; omega)
      (by simp only [site]; omega) (by simp only [site]; omega)]
    simp only [site, a, b]; push_cast; ring_nf
  have a2 : ext (sineVec2 K) ((site x).1 + 1, (site x).2) =
      sineFn (boxN n k) K.1 (a + 1) * sineFn (boxN n k) K.2 b := by
    rw [ext_sineVec2 K _ (by simp only [site]; omega) (by simp only [site]; omega)
      (by simp only [site]; omega) (by simp only [site]; omega)]
    simp only [site, a, b]; push_cast; ring_nf
  have a3 : ext (sineVec2 K) ((site x).1, (site x).2 - 1) =
      sineFn (boxN n k) K.1 a * sineFn (boxN n k) K.2 (b - 1) := by
    rw [ext_sineVec2 K _ (by simp only [site]; omega) (by simp only [site]; omega)
      (by simp only [site]; omega) (by simp only [site]; omega)]
    simp only [site, a, b]; push_cast; ring_nf
  have a4 : ext (sineVec2 K) ((site x).1, (site x).2 + 1) =
      sineFn (boxN n k) K.1 a * sineFn (boxN n k) K.2 (b + 1) := by
    rw [ext_sineVec2 K _ (by simp only [site]; omega) (by simp only [site]; omega)
      (by simp only [site]; omega) (by simp only [site]; omega)]
    simp only [site, a, b]; push_cast; ring_nf
  have t1 := sineFn_three_point (boxN n k) K.1 a
  have t2 := sineFn_three_point (boxN n k) K.2 b
  rw [dirOp_mulVec_apply, a1, a2, a3, a4, Pi.smul_apply, smul_eq_mul, hv, dirEig]
  linear_combination ((spacing n ^ 2)⁻¹ * sineFn (boxN n k) K.2 b) * t1 +
    ((spacing n ^ 2)⁻¹ * sineFn (boxN n k) K.1 a) * t2

/-! ## The spectral formula for `dirGreen` -/

/-- The orthogonal matrix of the sine basis: U x K = e_K(x). -/
def sineMat (n k : ℕ) : Matrix (DSite n k) (DSite n k) ℝ := fun x K => sineVec2 K x

theorem sineMat_transpose_mul : (sineMat n k)ᵀ * sineMat n k = 1 := by
  ext K L
  simp only [mul_apply, transpose_apply, sineMat, one_apply]
  exact sineVec2_orthonormal K L

theorem sineMat_mul_transpose : sineMat n k * (sineMat n k)ᵀ = 1 :=
  mul_eq_one_comm.mp sineMat_transpose_mul

theorem dirOp_mul_sineMat (m₀ : ℝ) :
    dirOp n k m₀ * sineMat n k = sineMat n k * diagonal (dirEig n k m₀) := by
  ext x K
  rw [mul_diagonal]
  have h := congrFun (dirOp_mulVec_sineVec2 m₀ K) x
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [mul_apply, sineMat]
  rw [h, mul_comm]

/-- **Spectral decomposition** dirGreen = U diag(1/λ) Uᵀ. -/
theorem dirGreen_eq_spectral (m₀ : ℝ) :
    dirGreen n k m₀ =
      sineMat n k * diagonal (fun K => (dirEig n k m₀ K)⁻¹) * (sineMat n k)ᵀ := by
  unfold dirGreen
  apply inv_eq_left_inv
  have hT : (sineMat n k)ᵀ * dirOp n k m₀ = diagonal (dirEig n k m₀) * (sineMat n k)ᵀ := by
    have := congrArg transpose (dirOp_mul_sineMat (n := n) (k := k) m₀)
    rw [transpose_mul, transpose_mul, dirOp_transpose, diagonal_transpose] at this
    exact this
  have hD : diagonal (fun K => (dirEig n k m₀ K)⁻¹) * diagonal (dirEig n k m₀) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext K
    exact inv_mul_cancel₀ (dirEig_pos m₀ K).ne'
  rw [Matrix.mul_assoc, hT, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hD,
    Matrix.one_mul, sineMat_mul_transpose]

/-- **The spectral formula:** dirGreen x y = Σ_K e_K(x) e_K(y) / λ_K (any m₀; λ_K > 0). -/
theorem dirGreen_spectral (m₀ : ℝ) (x y : DSite n k) :
    dirGreen n k m₀ x y = ∑ K : DSite n k, sineVec2 K x * sineVec2 K y / dirEig n k m₀ K := by
  rw [dirGreen_eq_spectral]
  rw [mul_apply]
  simp only [mul_diagonal, transpose_apply, sineMat]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [div_eq_mul_inv]; ring

end PP2Target

import LongTable.R_PP2M5FinalB
import LongTable.R_PP2NelsonRegionC
import LongTable.R_PP2Chaos3
import LongTable.R_PP2Separable

/-!
Part A of PP2WickHyps (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2WickHyps.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5: discharge
of the two free-field hypotheses of PP2M5Final, `WickDefectHyp m₀ l` and `WickL2Hyp m₀ l`
(m₀ ≠ 0, l ≥ 0), and the V3 target from the region Nelson bound and non-Gaussianity alone.
Namespace `PP2WickHyps`, helpers prefixed `wh_`. Notation as in PP2M5Final: ε = `spacing n`,
B = physBall n k x l, C_B = `dib_GB` = ε⁻² regionGreen B, ⟨·⟩⁰ = `dib_ex0 (rg_scaledOp B)`,
c = freeVar, δ(z) = c − C_B(z,z) (the misordering; 0 ≤ δ by `nr_region_defect_nonneg`).

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
Generic (ι finite, A PosDef, ρ_A = gaussWeight A):
* `wh_ex0_mono`, `wh_ex0_lin`, `wh_ex0_nonneg` (monotonicity / linearity / positivity of ⟨·⟩⁰ on
  continuous functions of exponential growth), `wh_grow_pow`.
* `wh_ex0_sq` (G3 bilinear expansion): ⟨(e Σ_z a_z :φ_z^j:_c)²⟩⁰ = e² Σ_{z,z'} a_z a_{z'} WW_{jj}(z,z').
* `wh_hyper` (hypercontractivity): F = e Σ_z a_z :φ_z³:_c ⟹ ⟨F⁴⟩⁰ ≤ (ρ₁⁻⁶ ⟨F²⟩⁰)², ρ₁ = `ch2_rho 1`
  (F ∘ M is a polynomial of degree ≤ 3 in the standard Gaussian modes, `mg_gauss_modes` +
  `ch3_moment_mvPoly` with m = 1; polynomials `wh_lin`, `wh_wickMv`, `wh_F3`).
* `wh_schur` (Schur test): H ≥ 0 symmetric, e Σ_{z'} H(z,z') ≤ S ⟹
  e² Σ_{z,z'} u_z u_{z'} H(z,z') ≤ S · e Σ_z u_z².
* `wh_Y_bound`: e²ΣΣ (g_zG_{az})(g_{z'}G_{az'})(δ_zδ_{z'} + 2G_{zz'}²) ≤ Γ²(K₂D₂ + 2K₂²)
  (Cauchy–Schwarz for the δδ' part, Schur with H = G² for the rest).
* `wh_F_bound`: e²ΣΣ a_z a_{z'}(9G_{zz'}δ_zδ_{z'} + 6G_{zz'}³) ≤ 9S·eΣ(a_zδ_z)² + 6K₃·eΣa_z².
* `wh_amgm`: ab ≤ (t/2)a² + (t⁻¹/2)b² (t > 0); `wh_posLog_four_le`: (log⁺x)⁴ ≤ 8192(1 + √x).
Region:
* `wh_GB_apply`, `wh_GB_nonneg`, `wh_GB_symm`, `wh_GB_row` (ε²Σ_{z'}C_B(z,z') ≤ m₀⁻²),
  `wh_GB_Lp` (ε²Σ_{z'}C_B(z,z')^p ≤ K_p, from `mg_regionGreen_Lp_le`), `wh_defect_nonneg`,
  `wh_defect_le`, `wh_defect_sq_le` / `wh_defect_four_le` (δ², δ⁴ ≤ a + b r(y)^{−1/2}),
  `wh_sum_bound` (summation with `nr_card_le`, `nr_sum_f_M`), `wh_card_le`.
* **`wh_wickDefectHyp`**: m₀ ≠ 0 → 0 ≤ l → WickDefectHyp m₀ l
  (D = P(34 L² + 256 m' L^{3/2}), P = (π/4)², m' = |m₀|^{−1/2}, L = 2l + 1).
* `wh_defect4`: ∃ D₄ ≥ 0, ∀ n k x, ε²Σ_{z∈B} δ(z)⁴ ≤ D₄ (same route, δ⁴ ≤ P²(65544 + 65536 m' r^{−1/2})).
* **`wh_wickL2Hyp`**: m₀ ≠ 0 → 0 ≤ l → WickL2Hyp m₀ l. K = 1 + c_Y + c_F with
  c_Y = K₂D₂ + 2K₂², c_F = H²(c₁² + c₂²)/2, H = ρ₁⁻⁶, c₁ = 9S(K₄ + D₄)/2 + 6K₃K₂,
  c₂ = 9SD₂ + 6K₃L², S = m₀⁻². Route: ⟨Y_g²⟩⁰ by G3 (`dib_WW_2_2`) + `wh_Y_bound`;
  (F₁F_g)² ≤ (Γ²/2)F₁⁴ + (Γ⁻²/2)F_g⁴ (Γ > 0; Γ = 0 trivial), `wh_hyper`, ⟨F²⟩⁰ by `dib_WW_3_3`
  + `wh_F_bound`, with eΣ(C_B(x,·)δ)² ≤ (K₄ + D₄)/2 and eΣ g²δ² ≤ Γ²D₂, eΣ g² ≤ Γ²L².
* **`phiFourTwoGapV3_of_nelson_nonGaussian`**: (∀ m₀ l, 0 < m₀ → 0 ≤ l → NelsonRegionHyp m₀ l)
  and non-Gaussianity of the limit points at small λ ⟹ PhiFourTwoGapV3
  (`phiFourTwoGapV3_of_hyps` + the two discharges + `schwartzSeparable`).

NOT formalized here: NelsonRegionHyp (G4; reduced in PP2NelsonRegion to `nr_RoughL2Hyp`),
non-Gaussianity. Optimal constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Matrix Finset PP2Target PP2DoubleIBP PP2M5Final
open PP2Nelson PP2NelsonRegion

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

noncomputable section

namespace PP2WickHyps

/-! ## 1. Generic finite-dimensional facts -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem wh_grow_pow {f : (ι → ℝ) → ℝ} (hf : m5f_Grow f) (m : ℕ) :
    m5f_Grow (fun φ => f φ ^ m) := by
  induction m with
  | zero => simp only [pow_zero]; exact m5f_grow_const 1
  | succ m ih => simp only [pow_succ]; exact m5f_grow_mul ih hf

theorem wh_ex0_mono {A : Matrix ι ι ℝ} (hA : A.PosDef) {f g : (ι → ℝ) → ℝ}
    (hfc : Continuous f) (hfg : m5f_Grow f) (hgc : Continuous g) (hgg : m5f_Grow g)
    (h : ∀ φ, f φ ≤ g φ) : dib_ex0 A f ≤ dib_ex0 A g := by
  unfold dib_ex0
  exact div_le_div_of_nonneg_right (integral_mono (m5f_int_0 hA hfc hfg) (m5f_int_0 hA hgc hgg)
    fun φ => mul_le_mul_of_nonneg_right (h φ) (PP2GaussIBP.gaussWeight_nonneg A φ))
    (dib_integral_gauss_pos hA).le

theorem wh_ex0_lin {A : Matrix ι ι ℝ} (hA : A.PosDef) {f g : (ι → ℝ) → ℝ}
    (hfc : Continuous f) (hfg : m5f_Grow f) (hgc : Continuous g) (hgg : m5f_Grow g) (r s : ℝ) :
    dib_ex0 A (fun φ => r * f φ + s * g φ) = r * dib_ex0 A f + s * dib_ex0 A g := by
  have hf' := m5f_int_0 hA hfc hfg
  have hg' := m5f_int_0 hA hgc hgg
  unfold dib_ex0
  simp_rw [add_mul, mul_assoc]
  rw [integral_add (hf'.const_mul r) (hg'.const_mul s), integral_const_mul, integral_const_mul]
  ring

theorem wh_ex0_nonneg (A : Matrix ι ι ℝ) {f : (ι → ℝ) → ℝ} (hf : ∀ φ, 0 ≤ f φ) :
    0 ≤ dib_ex0 A f := by
  unfold dib_ex0
  exact div_nonneg (integral_nonneg fun φ => mul_nonneg (hf φ) (PP2GaussIBP.gaussWeight_nonneg A φ))
    (integral_nonneg fun φ => PP2GaussIBP.gaussWeight_nonneg A φ)

theorem wh_cont_F (c e : ℝ) (a : ι → ℝ) (j : ℕ) :
    Continuous (fun φ : ι → ℝ => e * ∑ z, a z * wickPow c j (φ z)) :=
  continuous_const.mul (continuous_finsetSum _ fun z _ =>
    continuous_const.mul ((dib_continuous_wick c j).comp (continuous_apply z)))

theorem wh_grow_F (c e : ℝ) (a : ι → ℝ) {j : ℕ} (hj : j ≤ 4) :
    m5f_Grow (fun φ : ι → ℝ => e * ∑ z, a z * wickPow c j (φ z)) :=
  m5f_grow_mul (m5f_grow_const _) (m5f_grow_sum _ fun z _ =>
    m5f_grow_mul (m5f_grow_const _) (m5f_grow_wick c hj z))

/-- **Bilinear (G3) expansion of the second moment.** -/
theorem wh_ex0_sq {A : Matrix ι ι ℝ} (hA : A.PosDef) (c e : ℝ) (a : ι → ℝ) {j : ℕ}
    (hj : j ≤ 4) :
    dib_ex0 A (fun φ => (e * ∑ z, a z * wickPow c j (φ z)) ^ 2) =
      e ^ 2 * ∑ z, ∑ z', a z * a z' * dib_WW A c z z' j j := by
  have hW : ∀ z z', Continuous (fun φ : ι → ℝ => wickPow c j (φ z) * wickPow c j (φ z')) :=
    fun z z' => ((dib_continuous_wick c j).comp (continuous_apply z)).mul
      ((dib_continuous_wick c j).comp (continuous_apply z'))
  have hG : ∀ z z', m5f_Grow (fun φ : ι → ℝ => wickPow c j (φ z) * wickPow c j (φ z')) :=
    fun z z' => m5f_grow_mul (m5f_grow_wick c hj z) (m5f_grow_wick c hj z')
  have hfun : (fun φ : ι → ℝ => (e * ∑ z, a z * wickPow c j (φ z)) ^ 2) =
      fun φ => e ^ 2 * ∑ z, (1 * ∑ z', a z * a z' * (wickPow c j (φ z) * wickPow c j (φ z'))) := by
    funext φ
    rw [mul_pow, sq (∑ z, a z * wickPow c j (φ z)), Finset.sum_mul_sum]
    simp only [one_mul]
    congr 1
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => by ring
  rw [hfun, ← dib_ex_zero A 0 c]
  rw [m5f_ex_sum A 0 c 0 (e ^ 2)
    (f := fun z φ => 1 * ∑ z', a z * a z' * (wickPow c j (φ z) * wickPow c j (φ z')))
    (fun z => m5f_int_W hA le_rfl c le_rfl
      (continuous_const.mul (continuous_finsetSum _ fun z' _ => continuous_const.mul (hW z z')))
      (m5f_grow_mul (m5f_grow_const 1) (m5f_grow_sum _ fun z' _ =>
        m5f_grow_mul (m5f_grow_const _) (hG z z'))))]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [m5f_ex_sum A 0 c 0 1
    (f := fun z' φ => a z * a z' * (wickPow c j (φ z) * wickPow c j (φ z')))
    (fun z' => m5f_int_W hA le_rfl c le_rfl (continuous_const.mul (hW z z'))
      (m5f_grow_mul (m5f_grow_const _) (hG z z')))]
  rw [one_mul]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [m5f_ex_const_mul, dib_ex_zero]
  rfl

/-! ### Hypercontractivity for degree-3 Wick sums -/

/-- The linear form Σ_K v_K X_K. -/
def wh_lin (v : ι → ℝ) : MvPolynomial ι ℝ := ∑ K, MvPolynomial.C (v K) * MvPolynomial.X K

/-- :Q^j:_c as a polynomial. -/
def wh_wickMv (c : ℝ) (j : ℕ) (Q : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ i ∈ range (j / 2 + 1), MvPolynomial.C ((-1 : ℝ) ^ i * (j.factorial : ℝ) /
    ((i.factorial : ℝ) * ((j - 2 * i).factorial : ℝ) * 2 ^ i) * c ^ i) * Q ^ (j - 2 * i)

/-- e Σ_z a_z :(Mξ)_z³:_c as a polynomial in ξ. -/
def wh_F3 (M : Matrix ι ι ℝ) (c e : ℝ) (a : ι → ℝ) : MvPolynomial ι ℝ :=
  MvPolynomial.C e * ∑ z, MvPolynomial.C (a z) * wh_wickMv c 3 (wh_lin (M z))

theorem wh_lin_eval (v ξ : ι → ℝ) : MvPolynomial.eval ξ (wh_lin v) = ∑ K, v K * ξ K := by
  simp [wh_lin]

theorem wh_wickMv_eval (c : ℝ) (j : ℕ) (Q : MvPolynomial ι ℝ) (ξ : ι → ℝ) :
    MvPolynomial.eval ξ (wh_wickMv c j Q) = wickPow c j (MvPolynomial.eval ξ Q) := by
  simp [wh_wickMv, wickPow]

theorem wh_F3_eval (M : Matrix ι ι ℝ) (c e : ℝ) (a ξ : ι → ℝ) :
    e * ∑ z, a z * wickPow c 3 ((M *ᵥ ξ) z) = MvPolynomial.eval ξ (wh_F3 M c e a) := by
  simp only [wh_F3, map_mul, map_sum, MvPolynomial.eval_C, wh_wickMv_eval, wh_lin_eval]
  rfl

theorem wh_lin_deg (v : ι → ℝ) : (wh_lin v).totalDegree ≤ 1 := by
  refine MvPolynomial.totalDegree_finsetSum_le fun K _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

theorem wh_wickMv_deg (c : ℝ) (j : ℕ) {Q : MvPolynomial ι ℝ} (hQ : Q.totalDegree ≤ 1) :
    (wh_wickMv c j Q).totalDegree ≤ j := by
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc (j - 2 * i) * Q.totalDegree ≤ (j - 2 * i) * 1 := Nat.mul_le_mul_left _ hQ
    _ ≤ j := by omega

theorem wh_F3_deg (M : Matrix ι ι ℝ) (c e : ℝ) (a : ι → ℝ) : (wh_F3 M c e a).totalDegree ≤ 3 := by
  unfold wh_F3
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine MvPolynomial.totalDegree_finsetSum_le fun z _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact wh_wickMv_deg c 3 (wh_lin_deg _)

theorem wh_ex0_modes {A : Matrix ι ι ℝ} (hA : A.PosDef) (F : (ι → ℝ) → ℝ) :
    dib_ex0 A F = ∫ ξ, F (mg_modeMat hA *ᵥ ξ) ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  unfold dib_ex0 PP2GaussIBP.gaussWeight
  exact mg_gauss_modes hA F

/-- **Hypercontractive fourth moment:** F = e Σ_z a_z :φ_z³:_c (any c) has
⟨F⁴⟩⁰ ≤ (ρ₁⁻⁶ ⟨F²⟩⁰)². -/
theorem wh_hyper {A : Matrix ι ι ℝ} (hA : A.PosDef) (c e : ℝ) (a : ι → ℝ) :
    dib_ex0 A (fun φ => (e * ∑ z, a z * wickPow c 3 (φ z)) ^ 4) ≤
      ((PP2Chaos2.ch2_rho 1)⁻¹ ^ 6 *
        dib_ex0 A (fun φ => (e * ∑ z, a z * wickPow c 3 (φ z)) ^ 2)) ^ 2 := by
  set P := wh_F3 (mg_modeMat hA) c e a
  have key := PP2Chaos3.ch3_moment_mvPoly 1 3 P (wh_F3_deg _ _ _ _)
    (fun i => (MvPolynomial.degreeOf_le_totalDegree P i).trans
      ((wh_F3_deg _ _ _ _).trans (by norm_num)))
  rw [wh_ex0_modes hA, wh_ex0_modes hA]
  simp only [wh_F3_eval]
  exact key

/-! ### Schur test and the two algebraic bounds -/

/-- **Schur test.** -/
theorem wh_schur {e S : ℝ} (he : 0 ≤ e) (H : ι → ι → ℝ) (hH : ∀ z z', 0 ≤ H z z')
    (hs : ∀ z z', H z z' = H z' z) (hrow : ∀ z, e * ∑ z', H z z' ≤ S) (u : ι → ℝ) :
    e ^ 2 * ∑ z, ∑ z', u z * u z' * H z z' ≤ S * (e * ∑ z, u z ^ 2) := by
  have hpt : ∀ z z', u z * u z' * H z z' ≤ (u z ^ 2 * H z z' + u z' ^ 2 * H z' z) / 2 := by
    intro z z'
    rw [← hs z z']
    nlinarith [mul_nonneg (sq_nonneg (u z - u z')) (hH z z')]
  have h1 : ∑ z, ∑ z', u z * u z' * H z z' ≤ ∑ z, u z ^ 2 * ∑ z', H z z' := by
    calc ∑ z, ∑ z', u z * u z' * H z z'
        ≤ ∑ z, ∑ z', (u z ^ 2 * H z z' + u z' ^ 2 * H z' z) / 2 :=
          sum_le_sum fun z _ => sum_le_sum fun z' _ => hpt z z'
      _ = (∑ z, ∑ z', u z ^ 2 * H z z' + ∑ z, ∑ z', u z' ^ 2 * H z' z) / 2 := by
          rw [← sum_add_distrib, sum_div]
          refine sum_congr rfl fun z _ => ?_
          rw [← sum_add_distrib, sum_div]
      _ = ∑ z, u z ^ 2 * ∑ z', H z z' := by
          rw [sum_comm (f := fun z z' => u z' ^ 2 * H z' z)]
          simp only [mul_sum]
          ring
  have h2 : ∀ z, e * (u z ^ 2 * ∑ z', H z z') ≤ u z ^ 2 * S := fun z => by
    have := mul_le_mul_of_nonneg_left (hrow z) (sq_nonneg (u z))
    nlinarith
  calc e ^ 2 * ∑ z, ∑ z', u z * u z' * H z z'
      ≤ e ^ 2 * ∑ z, u z ^ 2 * ∑ z', H z z' := mul_le_mul_of_nonneg_left h1 (sq_nonneg e)
    _ = e * ∑ z, e * (u z ^ 2 * ∑ z', H z z') := by rw [sq, mul_assoc, mul_sum]
    _ ≤ e * ∑ z, u z ^ 2 * S := mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => h2 z) he
    _ = S * (e * ∑ z, u z ^ 2) := by rw [← sum_mul]; ring

theorem wh_sum_sq_le {e Γ : ℝ} (he : 0 ≤ e) (g w : ι → ℝ) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ Γ) :
    e * ∑ z, (g z * w z) ^ 2 ≤ Γ ^ 2 * (e * ∑ z, w z ^ 2) := by
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_le_sum fun z _ => ?_
  have h := pow_le_pow_left₀ (hg z).1 (hg z).2 2
  have := mul_le_mul_of_nonneg_right h (mul_nonneg he (sq_nonneg (w z)))
  nlinarith

/-- **The Y_g algebra:** e²ΣΣ (g_zG_{az})(g_{z'}G_{az'})(δ_zδ_{z'} + 2G_{zz'}²) ≤ Γ²(K₂D₂ + 2K₂²). -/
theorem wh_Y_bound {e K2 D2 Γ c : ℝ} (he : 0 ≤ e) (G : ι → ι → ℝ)
    (hs : ∀ z z', G z z' = G z' z)
    (h2 : ∀ z, e * ∑ z', G z z' ^ 2 ≤ K2) (hD : e * ∑ z, (c - G z z) ^ 2 ≤ D2)
    (a : ι) (g : ι → ℝ) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ Γ) :
    e ^ 2 * ∑ z, ∑ z', g z * G a z * (g z' * G a z') *
        ((c - G z z) * (c - G z' z') + 2 * G z z' ^ 2) ≤ Γ ^ 2 * (K2 * D2 + 2 * K2 ^ 2) := by
  set u : ι → ℝ := fun z => g z * G a z with hu
  set v : ι → ℝ := fun z => g z * (c - G z z) with hv
  have hsq : (e * ∑ z, G a z * v z) ^ 2 =
      e ^ 2 * ∑ z, ∑ z', G a z * v z * (G a z' * v z') := by
    rw [mul_pow, sq (∑ z, G a z * v z), Finset.sum_mul_sum]
  have hX : ∑ z, ∑ z', g z * G a z * (g z' * G a z') *
        ((c - G z z) * (c - G z' z') + 2 * G z z' ^ 2) =
      ∑ z, ∑ z', G a z * v z * (G a z' * v z') + 2 * ∑ z, ∑ z', u z * u z' * G z z' ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun z _ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun z' _ => ?_
    simp only [hu, hv]; ring
  have hsplit : e ^ 2 * ∑ z, ∑ z', g z * G a z * (g z' * G a z') *
        ((c - G z z) * (c - G z' z') + 2 * G z z' ^ 2) =
      (e * ∑ z, G a z * v z) ^ 2 + 2 * (e ^ 2 * ∑ z, ∑ z', u z * u z' * G z z' ^ 2) := by
    rw [hX, hsq]; ring
  have hK2 : 0 ≤ K2 := le_trans (mul_nonneg he (sum_nonneg fun _ _ => sq_nonneg _)) (h2 a)
  have hD2 : 0 ≤ D2 := le_trans (mul_nonneg he (sum_nonneg fun _ _ => sq_nonneg _)) hD
  have hT1 : (e * ∑ z, G a z * v z) ^ 2 ≤ K2 * (Γ ^ 2 * D2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun z => G a z) v
    have hv2 : e * ∑ z, v z ^ 2 ≤ Γ ^ 2 * D2 :=
      (wh_sum_sq_le he g (fun z => c - G z z) hg).trans
        (mul_le_mul_of_nonneg_left hD (sq_nonneg Γ))
    have hA0 : 0 ≤ e * ∑ z, G a z ^ 2 := mul_nonneg he (sum_nonneg fun _ _ => sq_nonneg _)
    calc (e * ∑ z, G a z * v z) ^ 2 = e ^ 2 * (∑ z, G a z * v z) ^ 2 := by ring
      _ ≤ e ^ 2 * ((∑ z, G a z ^ 2) * ∑ z, v z ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg e)
      _ = (e * ∑ z, G a z ^ 2) * (e * ∑ z, v z ^ 2) := by ring
      _ ≤ K2 * (Γ ^ 2 * D2) := mul_le_mul (h2 a) hv2
          (mul_nonneg he (sum_nonneg fun _ _ => sq_nonneg _)) hK2
  have hT2 : e ^ 2 * ∑ z, ∑ z', u z * u z' * G z z' ^ 2 ≤ K2 * (Γ ^ 2 * K2) := by
    refine (wh_schur he (fun z z' => G z z' ^ 2) (fun z z' => sq_nonneg _)
      (fun z z' => by rw [hs z z']) h2 u).trans ?_
    exact mul_le_mul_of_nonneg_left ((wh_sum_sq_le he g (fun z => G a z) hg).trans
      (mul_le_mul_of_nonneg_left (h2 a) (sq_nonneg Γ))) hK2
  rw [hsplit]
  nlinarith

/-- **The F algebra (dib_WW 3,3 entry):**
e²ΣΣ a_z a_{z'}(9G_{zz'}δ_zδ_{z'} + 6G_{zz'}³) ≤ 9S·eΣ(a_zδ_z)² + 6K₃·eΣa_z². -/
theorem wh_F_bound {e S K3 c : ℝ} (he : 0 ≤ e) (G : ι → ι → ℝ)
    (hG : ∀ z z', 0 ≤ G z z') (hs : ∀ z z', G z z' = G z' z)
    (hrow : ∀ z, e * ∑ z', G z z' ≤ S) (h3 : ∀ z, e * ∑ z', G z z' ^ 3 ≤ K3) (a : ι → ℝ) :
    e ^ 2 * ∑ z, ∑ z', a z * a z' *
        (9 * G z z' * (c - G z z) * (c - G z' z') + 6 * G z z' ^ 3) ≤
      9 * (S * (e * ∑ z, (a z * (c - G z z)) ^ 2)) + 6 * (K3 * (e * ∑ z, a z ^ 2)) := by
  have hsplit : e ^ 2 * ∑ z, ∑ z', a z * a z' *
        (9 * G z z' * (c - G z z) * (c - G z' z') + 6 * G z z' ^ 3) =
      9 * (e ^ 2 * ∑ z, ∑ z', (a z * (c - G z z)) * (a z' * (c - G z' z')) * G z z') +
        6 * (e ^ 2 * ∑ z, ∑ z', a z * a z' * G z z' ^ 3) := by
    have hX : ∑ z, ∑ z', a z * a z' *
          (9 * G z z' * (c - G z z) * (c - G z' z') + 6 * G z z' ^ 3) =
        9 * ∑ z, ∑ z', (a z * (c - G z z)) * (a z' * (c - G z' z')) * G z z' +
          6 * ∑ z, ∑ z', a z * a z' * G z z' ^ 3 := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun z _ => ?_
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun z' _ => ?_
      ring
    rw [hX]; ring
  rw [hsplit]
  have hA := wh_schur he G hG hs hrow (fun z => a z * (c - G z z))
  have hB := wh_schur he (fun z z' => G z z' ^ 3) (fun z z' => pow_nonneg (hG z z') 3)
    (fun z z' => by rw [hs z z']) h3 a
  linarith

theorem wh_sum_prod_sq {e : ℝ} (he : 0 ≤ e) (u w : ι → ℝ) :
    e * ∑ z, (u z * w z) ^ 2 ≤ (e * ∑ z, u z ^ 4 + e * ∑ z, w z ^ 4) / 2 := by
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, sum_div]
  refine sum_le_sum fun z _ => ?_
  nlinarith [mul_nonneg he (sq_nonneg (u z ^ 2 - w z ^ 2))]

theorem wh_amgm {t : ℝ} (ht : 0 < t) (a b : ℝ) : a * b ≤ t / 2 * a ^ 2 + t⁻¹ / 2 * b ^ 2 := by
  have key : t / 2 * a ^ 2 + t⁻¹ / 2 * b ^ 2 - a * b = (t * a - b) ^ 2 * (t⁻¹ / 2) := by
    field_simp; ring
  have : 0 ≤ (t * a - b) ^ 2 * (t⁻¹ / 2) := by positivity
  linarith

end Generic

/-! ## 2. Elementary inequality -/

theorem wh_posLog_four_le {x : ℝ} (hx : 0 ≤ x) : Real.posLog x ^ 4 ≤ 8192 * (1 + √x) := by
  have h2 : Real.posLog x = 2 * Real.posLog (√x) := by
    show max 0 (Real.log x) = 2 * max 0 (Real.log √x)
    rw [Real.log_sqrt hx]
    rcases le_total 0 (Real.log x) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  have hs := nl_posLog_sq_le (Real.sqrt_nonneg x)
  set t := √(√x) with ht
  have ht2 : t ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set s := Real.posLog √x with hsdef
  have h3 : (s ^ 2) ^ 2 ≤ (16 * (1 + t)) ^ 2 := pow_le_pow_left₀ (sq_nonneg s) hs 2
  have h4 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  rw [h2]
  calc (2 * s) ^ 4 = 16 * (s ^ 2) ^ 2 := by ring
    _ ≤ 16 * (16 * (1 + t)) ^ 2 := mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 4096 * (1 + t) ^ 2 := by ring
    _ ≤ 4096 * (2 * (1 + t ^ 2)) := mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 8192 * (1 + √x) := by rw [ht2]; ring

end PP2WickHyps

end

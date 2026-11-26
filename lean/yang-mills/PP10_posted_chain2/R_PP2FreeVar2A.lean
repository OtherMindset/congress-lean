import LongTable.P_mwxo412m_27xfkn

/-!
Part A of PP2FreeVar2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2FreeVar2.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5c, session 2.
The Wick defect b(x) = freeVar − ε⁻² dirGreen x x of the Dirichlet box, bounded by the distance to
the boundary (namespace `PP2Target`; notation of PP2FreeVar: ε = `spacing n`, μ = m₀²ε²,
w = `symb μ θ₁ θ₂`, h = π/(M+1), a = h/2 = `midNode M 0`, log⁺ = `Real.posLog` = max 0 log).

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
Goal 1 (strip estimate).
* `fv2_jordan`: (4/π²)t² ≤ 4 sin²(t/2) on [0, π] (from `Real.mul_le_sin`).
* `fv2_symb_ge`: at μ = (4/π²)p², (4/π²)(max(p, θ₁)² + θ₂²) ≤ w(θ₁, θ₂) on [0, π]².
* `fv2_integral_arctan_le`: ∫_0^b dθ/(c(q² + θ²)) ≤ π/(2cq) (FTC with arctan(θ/q)/(cq)).
* `fv2_integral_inv_max`: ∫_0^a dθ/max(p, θ) ≤ 1 + log⁺(a/p).
* `fv2_strip_le`: ∫_0^a ∫_0^π 1/w ≤ (π³/8)(1 + log⁺(a/p)), μ = (4/π²)p², 0 ≤ a ≤ π.
* `fv2_integral_swap` (Fubini for continuous integrands on rectangles), `fv2_strips_eq`
  (the θ₁ ↔ θ₂ swap: the two strips of `freeVar_sub_specVar_centre_le` are equal).
* `fv2_freeVar_sub_centre_le`: m₀ ≠ 0 → freeVar − specVar (2M+1) (m₀²ε²) M M
  ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))). Explicit C = π/4 (p = π|m₀|ε/2, a/p = 1/(|m₀|ε(M+1))).
Goal 2 (domain monotonicity).
* `regionOp n k m₀ B := (dirOp n k m₀).submatrix (↑) (↑)` on {x // x ∈ B};
  `regionGreen := (regionOp)⁻¹`; `fv2_regionOp_posDef`, `fv2_regionOp_mul_regionGreen`.
* `fv2_regionGreen_le_dirGreen`: m₀ ≠ 0 → regionGreen B x y ≤ dirGreen x y on B × B
  (regionOp (G_Λ|_B − G_B e_y) = −Σ_{w∉B} dirOp(·, w) G_Λ(w, y) ≥ 0, then `nonneg_of_stieltjes`).
* `fv2_subBox M x` (sites at lattice sup-distance ≤ M from x), `fv2_subBox_var_le`:
  ε⁻² G_sub(x, x) ≤ ε⁻² dirGreen x x.
Goal 3 (site bound).
* `fv2_two_mul_sub_quad_le`: 2 v(a) − ⟨v, dirOp v⟩ ≤ dirGreen a a for every v (m₀ ≠ 0).
* Sub-box sine modes: `fv2_sv` (1-D mode of [c − M, c + M], zero outside), `fv2_sv_three`
  (three-point identity inside, using vanishing at c − M − 1 and c + M + 1), `fv2_Fits M x`
  (sub-box inside the box), `fv2_E` (2-D mode, zero-extended), `fv2_ext_E`, `fv2_dirOp_E`
  (dirOp e_K = λ_K e_K on the sub-box, λ_K = `fv2_lam` = ε⁻²(sineEig K₁ + sineEig K₂) + m₀²),
  `fv2_E_out`, `fv2_sv_sum`, `fv2_E_orthonormal` (Σ_y e_K e_L = δ_KL), `fv2_E_centre`.
* `fv2_specVar_le_dirVar`: Fits M x → specVar (2M+1) (m₀²ε²) M M ≤ ε⁻² dirGreen x x
  (trial field v = Σ_K e_K(x) λ_K⁻¹ e_K; this replaces "domain monotonicity + identification of
  the sub-box Green's function with specVar" for the diagonal lower bound).
* `fv2_wick_defect_le_of_fits`: Fits M x → b(x) ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))).
* `fv2_bdist x` = min(x₁, N−1−x₁, x₂, N−1−x₂), `fv2_rdist n k x` = ε(fv2_bdist x + 1) (the
  sup-distance from x to the nearest zero (Dirichlet) site, lattice coordinate −1 or N),
  `fv2_fits_bdist`, and **`fv2_wick_defect_le`**: m₀ ≠ 0 → for every site x,
  freeVar − ε⁻² dirGreen x x ≤ (π/4)(1 + log⁺(1/(|m₀| r(x)))). With `dirVar_le_freeVar`,
  0 ≤ b(x) ≤ (π/4)(1 + log⁺(1/(|m₀| r(x)))), uniformly in n, k.

NOT formalized here: the equality ε⁻² regionGreen (subBox) (x, x) = specVar (2M+1) (only the
lower bound of dirGreen is proved, variationally, which is what the site bound needs); the
identification of `fv2_rdist` with a distance computed from `dpos` (it is defined in lattice
terms); any use of b(x) downstream (e.g. summing b over the box); sharper
constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset

noncomputable section

namespace PP2Target

/-! ## Goal 1: the strip estimate -/

/-- Jordan's inequality in the form used: (4/π²) t² ≤ 4 sin²(t/2) for t ∈ [0, π]. -/
theorem fv2_jordan {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π) :
    4 / π ^ 2 * t ^ 2 ≤ 4 * sin (t / 2) ^ 2 := by
  have hpi := Real.pi_pos
  have h := Real.mul_le_sin (x := t / 2) (by linarith) (by linarith)
  have e : 2 / π * (t / 2) = t / π := by field_simp
  rw [e] at h
  have h0' : 0 ≤ t / π := by positivity
  calc 4 / π ^ 2 * t ^ 2 = 4 * (t / π) ^ 2 := by field_simp
    _ ≤ 4 * sin (t / 2) ^ 2 := by gcongr

/-- Lower bound of the symbol on [0, π]², at μ = (4/π²) p²: with q = max(p, θ₁),
(4/π²)(q² + θ₂²) ≤ w(θ₁, θ₂). -/
theorem fv2_symb_ge {p θ₁ θ₂ : ℝ} (hp : 0 ≤ p) (h1 : 0 ≤ θ₁) (h1' : θ₁ ≤ π) (h2 : 0 ≤ θ₂)
    (h2' : θ₂ ≤ π) :
    4 / π ^ 2 * (max p θ₁ ^ 2 + θ₂ ^ 2) ≤ symb (4 / π ^ 2 * p ^ 2) θ₁ θ₂ := by
  have j1 := fv2_jordan h1 h1'
  have j2 := fv2_jordan h2 h2'
  have hm : max p θ₁ ^ 2 ≤ p ^ 2 + θ₁ ^ 2 := by
    rcases le_total p θ₁ with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hc : 0 ≤ 4 / π ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hm hc
  unfold symb
  nlinarith

/-- The arctan bound: ∫_0^b dθ / (c(q² + θ²)) ≤ π / (2cq) (c, q > 0, b ≥ 0). -/
theorem fv2_integral_arctan_le {c q b : ℝ} (hc : 0 < c) (hq : 0 < q) (hb : 0 ≤ b) :
    ∫ θ in (0 : ℝ)..b, 1 / (c * (q ^ 2 + θ ^ 2)) ≤ π / (2 * c * q) := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) b,
      HasDerivAt (fun θ => arctan (θ / q) / (c * q)) (1 / (c * (q ^ 2 + θ ^ 2))) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => θ / q) (1 / q) θ := by
      simpa using (hasDerivAt_id θ).div_const q
    have h2 := (h1.arctan).div_const (c * q)
    convert h2 using 1
    field_simp
  have hcont : Continuous fun θ : ℝ => 1 / (c * (q ^ 2 + θ ^ 2)) :=
    continuous_const.div (by fun_prop) (fun θ => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [zero_div, Real.arctan_zero, sub_zero]
  have ha := Real.arctan_lt_pi_div_two (b / q)
  rw [show π / (2 * c * q) = (π / 2) / (c * q) by field_simp]
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr ha.le

/-- ∫_0^a dθ / max(p, θ) ≤ 1 + log⁺(a/p) (p > 0, a ≥ 0). -/
theorem fv2_integral_inv_max {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) :
    ∫ θ in (0 : ℝ)..a, 1 / max p θ ≤ 1 + Real.posLog (a / p) := by
  have hcont : Continuous fun θ : ℝ => 1 / max p θ :=
    continuous_const.div (continuous_const.max continuous_id)
      (fun θ => (lt_of_lt_of_le hp (le_max_left _ _)).ne')
  have hlog0 : 0 ≤ Real.posLog (a / p) := le_max_left _ _
  rcases le_total a p with hap | hpa
  · calc ∫ θ in (0 : ℝ)..a, 1 / max p θ ≤ ∫ θ in (0 : ℝ)..a, 1 / p := by
          apply intervalIntegral.integral_mono_on ha (hcont.intervalIntegrable _ _)
            intervalIntegrable_const
          intro θ _
          exact one_div_le_one_div_of_le hp (le_max_left _ _)
      _ = a / p := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ 1 := (div_le_one hp).mpr hap
      _ ≤ _ := by linarith
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := p) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have e1 : ∫ θ in (0 : ℝ)..p, 1 / max p θ = 1 := by
      rw [intervalIntegral.integral_congr (g := fun _ => 1 / p)]
      · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; field_simp
      · intro θ hθ
        rw [Set.uIcc_of_le hp.le] at hθ
        simp only [max_eq_left hθ.2]
    have e2 : ∫ θ in p..a, 1 / max p θ = Real.log (a / p) := by
      rw [intervalIntegral.integral_congr (g := fun θ => 1 / θ)]
      · exact integral_one_div_of_pos hp (lt_of_lt_of_le hp hpa)
      · intro θ hθ
        rw [Set.uIcc_of_le hpa] at hθ
        simp only [max_eq_right hθ.1]
    rw [e1, e2]
    have : Real.log (a / p) ≤ Real.posLog (a / p) := le_max_right _ _
    linarith

/-- **The first strip**: at μ = (4/π²) p², p > 0, and 0 ≤ a ≤ π,
∫_0^a ∫_0^π 1/w ≤ (π³/8)(1 + log⁺(a/p)). -/
theorem fv2_strip_le {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (haπ : a ≤ π) :
    ∫ θ₁ in (0 : ℝ)..a, ∫ θ₂ in (0 : ℝ)..π, 1 / symb (4 / π ^ 2 * p ^ 2) θ₁ θ₂ ≤
      π ^ 3 / 8 * (1 + Real.posLog (a / p)) := by
  have hpi := Real.pi_pos
  have hc : 0 < 4 / π ^ 2 := by positivity
  have hμ : 0 < 4 / π ^ 2 * p ^ 2 := by positivity
  have hcont : Continuous fun θ : ℝ => 1 / max p θ :=
    continuous_const.div (continuous_const.max continuous_id)
      (fun θ => (lt_of_lt_of_le hp (le_max_left _ _)).ne')
  have hinner : ∀ θ₁ ∈ Set.Icc (0 : ℝ) a,
      ∫ θ₂ in (0 : ℝ)..π, 1 / symb (4 / π ^ 2 * p ^ 2) θ₁ θ₂ ≤ π ^ 3 / 8 * (1 / max p θ₁) := by
    intro θ₁ hθ₁
    have hq : 0 < max p θ₁ := lt_of_lt_of_le hp (le_max_left _ _)
    have hcont2 : Continuous fun θ : ℝ => 1 / (4 / π ^ 2 * (max p θ₁ ^ 2 + θ ^ 2)) :=
      continuous_const.div (by fun_prop) (fun θ => by positivity)
    calc ∫ θ₂ in (0 : ℝ)..π, 1 / symb (4 / π ^ 2 * p ^ 2) θ₁ θ₂
        ≤ ∫ θ₂ in (0 : ℝ)..π, 1 / (4 / π ^ 2 * (max p θ₁ ^ 2 + θ₂ ^ 2)) := by
          apply intervalIntegral.integral_mono_on hpi.le
            ((continuous_inv_symb₂ hμ θ₁).intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)
          intro θ₂ hθ₂
          apply one_div_le_one_div_of_le (by positivity)
          exact fv2_symb_ge hp.le hθ₁.1 (hθ₁.2.trans haπ) hθ₂.1 hθ₂.2
      _ ≤ π / (2 * (4 / π ^ 2) * max p θ₁) := fv2_integral_arctan_le hc hq hpi.le
      _ = π ^ 3 / 8 * (1 / max p θ₁) := by field_simp; ring
  calc ∫ θ₁ in (0 : ℝ)..a, ∫ θ₂ in (0 : ℝ)..π, 1 / symb (4 / π ^ 2 * p ^ 2) θ₁ θ₂
      ≤ ∫ θ₁ in (0 : ℝ)..a, π ^ 3 / 8 * (1 / max p θ₁) :=
        intervalIntegral.integral_mono_on ha
          ((continuous_inner_symb hμ 0 π).intervalIntegrable _ _)
          ((hcont.const_mul _).intervalIntegrable _ _) hinner
    _ = π ^ 3 / 8 * ∫ θ₁ in (0 : ℝ)..a, 1 / max p θ₁ := intervalIntegral.integral_const_mul _ _
    _ ≤ π ^ 3 / 8 * (1 + Real.posLog (a / p)) :=
        mul_le_mul_of_nonneg_left (fv2_integral_inv_max hp ha) (by positivity)

/-- Fubini for interval integrals of a jointly continuous function. -/
theorem fv2_integral_swap {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply MeasureTheory.integral_integral_swap
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

theorem fv2_symb_comm (μ θ₁ θ₂ : ℝ) : symb μ θ₁ θ₂ = symb μ θ₂ θ₁ := by
  unfold symb; ring

/-- **The two strips are equal** (θ₁ ↔ θ₂). -/
theorem fv2_strips_eq {μ : ℝ} (hμ : 0 < μ) {a : ℝ} (ha : 0 ≤ a) :
    ∫ θ₁ in (0 : ℝ)..π, ∫ θ₂ in (0 : ℝ)..a, 1 / symb μ θ₁ θ₂ =
      ∫ θ₁ in (0 : ℝ)..a, ∫ θ₂ in (0 : ℝ)..π, 1 / symb μ θ₁ θ₂ := by
  rw [fv2_integral_swap (f := fun θ₁ θ₂ => 1 / symb μ θ₁ θ₂) (continuous_inv_symb hμ)
    Real.pi_pos.le ha]
  simp only [fv2_symb_comm μ _ _]

/-- **Goal 1: the Wick constant against the centre of an odd box.** For m₀ ≠ 0 and N = 2M + 1,
freeVar − specVar (2M+1) (m₀²ε²) M M ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))). -/
theorem fv2_freeVar_sub_centre_le {n : ℕ} {m₀ : ℝ} (hm : m₀ ≠ 0) (M : ℕ) (hM : M < 2 * M + 1) :
    freeVar n m₀ - specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * spacing n * ((M : ℝ) + 1)))) := by
  have hpi := Real.pi_pos
  have hε := spacing_pos n
  have hm' : 0 < |m₀| := abs_pos.mpr hm
  set p := π * |m₀| * spacing n / 2 with hpdef
  have hp : 0 < p := by positivity
  have hμ : m₀ ^ 2 * spacing n ^ 2 = 4 / π ^ 2 * p ^ 2 := by
    rw [hpdef, ← sq_abs m₀]; field_simp; norm_num
  have hμpos : 0 < m₀ ^ 2 * spacing n ^ 2 := by positivity
  have h := freeVar_sub_specVar_centre_le (n := n) hm M hM
  set a := midNode M 0 with ha
  have ha0 : 0 ≤ a := midNode_nonneg M 0
  have haπ : a ≤ π := midNode_le_pi M 0 (Nat.zero_le _)
  rw [fv2_strips_eq hμpos ha0, hμ] at h
  have hs := fv2_strip_le hp ha0 haπ
  have hap : a / p = 1 / (|m₀| * spacing n * ((M : ℝ) + 1)) := by
    rw [ha, hpdef, midNode]; field_simp; ring
  rw [hap] at hs
  calc freeVar n m₀ - specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩
      ≤ 1 / π ^ 2 * (2 * ∫ θ₁ in (0 : ℝ)..a, ∫ θ₂ in (0 : ℝ)..π,
          1 / symb (4 / π ^ 2 * p ^ 2) θ₁ θ₂) := by rw [hμ]; linarith
    _ ≤ 1 / π ^ 2 * (2 * (π ^ 3 / 8 *
          (1 + Real.posLog (1 / (|m₀| * spacing n * ((M : ℝ) + 1)))))) := by gcongr
    _ = _ := by field_simp; ring

/-! ## Goal 2: domain monotonicity -/

variable {n k : ℕ}

/-- The free Dirichlet operator of a region B ⊆ box: dirOp restricted to B × B. -/
def regionOp (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) :
    Matrix {x // x ∈ B} {x // x ∈ B} ℝ :=
  (dirOp n k m₀).submatrix Subtype.val Subtype.val

/-- The free Green's function of the region B (Dirichlet on Bᶜ). -/
def regionGreen (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) :
    Matrix {x // x ∈ B} {x // x ∈ B} ℝ :=
  (regionOp n k m₀ B)⁻¹

theorem fv2_regionOp_posDef {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) :
    (regionOp n k m₀ B).PosDef :=
  (dirOp_posDef hm).submatrix Subtype.val_injective

theorem fv2_regionOp_mul_regionGreen {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) :
    regionOp n k m₀ B * regionGreen n k m₀ B = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (fv2_regionOp_posDef hm B).isUnit)

/-- **Domain monotonicity**: for m₀ ≠ 0 and a region B of box sites, the region Green's function
is entrywise at most the box Green's function on B × B. -/
theorem fv2_regionGreen_le_dirGreen {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (x y : {z // z ∈ B}) : regionGreen n k m₀ B x y ≤ dirGreen n k m₀ x y := by
  set A := regionOp n k m₀ B with hA
  set g : DField n k := dirGreen n k m₀ *ᵥ Pi.single (y : DSite n k) 1 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by
    simp only [hg, mulVec_single_one, col_apply]; exact dirGreen_nonneg hm _ _
  have hAg : dirOp n k m₀ *ᵥ g = Pi.single (y : DSite n k) 1 := by
    rw [hg, mulVec_mulVec, dirOp_mul_dirGreen hm, one_mulVec]
  set gB : {z // z ∈ B} → ℝ := fun z => g z with hgB
  set u : {z // z ∈ B} → ℝ := regionGreen n k m₀ B *ᵥ Pi.single y 1 with hu
  have hAu : A *ᵥ u = Pi.single y 1 := by
    rw [hu, mulVec_mulVec, fv2_regionOp_mul_regionGreen hm, one_mulVec]
  have hAgB : ∀ z : {z // z ∈ B}, (Pi.single y 1 : {z // z ∈ B} → ℝ) z ≤ (A *ᵥ gB) z := by
    intro z
    have hfull := congrFun hAg z
    simp only [mulVec, dotProduct] at hfull
    rw [← Finset.sum_add_sum_compl B] at hfull
    have hsub : (A *ᵥ gB) z = ∑ w ∈ B, dirOp n k m₀ z w * g w := by
      simp only [mulVec, dotProduct, hA, regionOp, submatrix_apply, hgB]
      exact Finset.sum_coe_sort B (fun w => dirOp n k m₀ z w * g w)
    have hneg : ∑ w ∈ Bᶜ, dirOp n k m₀ z w * g w ≤ 0 := by
      refine Finset.sum_nonpos fun w hw => ?_
      have hzw : (z : DSite n k) ≠ w := by
        rintro h; rw [← h] at hw; exact (Finset.mem_compl.mp hw) z.2
      exact mul_nonpos_of_nonpos_of_nonneg (dirOp_offDiag_nonpos m₀ hzw) (hg0 w)
    have hδ : (Pi.single y 1 : {z // z ∈ B} → ℝ) z = (Pi.single (y : DSite n k) 1 : DField n k) z := by
      simp only [Pi.single_apply, Subtype.ext_iff]
    rw [hsub, hδ, ← hfull]
    linarith
  have hsymm : Aᵀ = A := by
    rw [hA, regionOp, transpose_submatrix, dirOp_transpose]
  have hpd : ∀ v : {z // z ∈ B} → ℝ, v ≠ 0 → 0 < v ⬝ᵥ A *ᵥ v := fun v hv => by
    simpa using (fv2_regionOp_posDef hm B).dotProduct_mulVec_pos hv
  have hoff : ∀ a b : {z // z ∈ B}, a ≠ b → A a b ≤ 0 := fun a b hab =>
    dirOp_offDiag_nonpos m₀ (fun h => hab (Subtype.ext h))
  have hd := nonneg_of_stieltjes A hsymm hpd hoff (v := gB - u) rfl
    (fun z => by rw [mulVec_sub, Pi.sub_apply, hAu, Pi.zero_apply]; linarith [hAgB z]) x
  have e1 : u x = regionGreen n k m₀ B x y := by simp [hu, mulVec_single_one]
  have e2 : gB x = dirGreen n k m₀ x y := by simp [hgB, hg, mulVec_single_one]
  simp only [Pi.sub_apply, Pi.zero_apply] at hd
  linarith

/-- The odd sub-box of half-width M centred at the site x (lattice sup-distance ≤ M from x). -/
def fv2_subBox (M : ℕ) (x : DSite n k) : Finset (DSite n k) :=
  Finset.univ.filter fun y => (x.1 : ℕ) ≤ (y.1 : ℕ) + M ∧ (y.1 : ℕ) ≤ (x.1 : ℕ) + M ∧
    (x.2 : ℕ) ≤ (y.2 : ℕ) + M ∧ (y.2 : ℕ) ≤ (x.2 : ℕ) + M

end PP2Target

end

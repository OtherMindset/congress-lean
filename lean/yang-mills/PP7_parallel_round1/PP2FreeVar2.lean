import LongTable.PP2FreeVar

/-!
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

theorem fv2_mem_subBox_self (M : ℕ) (x : DSite n k) : x ∈ fv2_subBox M x := by
  simp [fv2_subBox]

/-- **Domain monotonicity at the centre of a sub-box**: ε⁻² G_sub(x, x) ≤ ε⁻² dirGreen(x, x). -/
theorem fv2_subBox_var_le {m₀ : ℝ} (hm : m₀ ≠ 0) (M : ℕ) (x : DSite n k) :
    (spacing n ^ 2)⁻¹ * regionGreen n k m₀ (fv2_subBox M x) ⟨x, fv2_mem_subBox_self M x⟩
        ⟨x, fv2_mem_subBox_self M x⟩ ≤ (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x :=
  mul_le_mul_of_nonneg_left (fv2_regionGreen_le_dirGreen hm _ _ _) (by positivity)

/-! ## Goal 3: the centre of an odd sub-box, variationally -/

/-- **Variational lower bound**: 2 v(a) − ⟨v, dirOp v⟩ ≤ dirGreen a a (m₀ ≠ 0). -/
theorem fv2_two_mul_sub_quad_le {m₀ : ℝ} (hm : m₀ ≠ 0) (v : DField n k) (a : DSite n k) :
    2 * v a - v ⬝ᵥ dirOp n k m₀ *ᵥ v ≤ dirGreen n k m₀ a a := by
  set g : DField n k := dirGreen n k m₀ *ᵥ Pi.single a 1 with hg
  have hAg : dirOp n k m₀ *ᵥ g = Pi.single a 1 := by
    rw [hg, mulVec_mulVec, dirOp_mul_dirGreen hm, one_mulVec]
  have hga : g a = dirGreen n k m₀ a a := by simp [hg, mulVec_single_one]
  have hsym : g ⬝ᵥ dirOp n k m₀ *ᵥ v = v ⬝ᵥ dirOp n k m₀ *ᵥ g := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dirOp_transpose, dotProduct_comm]
  have hva : v ⬝ᵥ (Pi.single a 1 : DField n k) = v a := by
    simp [dotProduct, Pi.single_apply]
  have hgg : g ⬝ᵥ (Pi.single a 1 : DField n k) = g a := by
    simp [dotProduct, Pi.single_apply]
  have h0 : 0 ≤ (v - g) ⬝ᵥ dirOp n k m₀ *ᵥ (v - g) := by
    have := dirOp_quad_ge m₀ (v - g)
    have : 0 ≤ m₀ ^ 2 * ∑ x : DSite n k, (v - g) x ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hsym, hAg, hva, hgg, hga] at h0
  linarith

/-- The 1-D sine mode j of the odd interval [c − M, c + M] ⊂ ℤ (side 2M + 1), zero outside:
e_j(q − c + M) for q in the interval. -/
def fv2_sv (M : ℕ) (c : ℤ) (j : ℕ) (q : ℤ) : ℝ :=
  if c - M ≤ q ∧ q ≤ c + M then sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1) else 0

theorem fv2_sv_three (M : ℕ) (c : ℤ) (j : ℕ) {q : ℤ} (h1 : c - M ≤ q) (h2 : q ≤ c + M) :
    2 * fv2_sv M c j q - fv2_sv M c j (q - 1) - fv2_sv M c j (q + 1) =
      sineEig (2 * M + 1) j * fv2_sv M c j q := by
  have t := sineFn_three_point (2 * M + 1) j ((q : ℝ) - c + M + 1)
  have e0 : fv2_sv M c j q = sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1) := by
    simp only [fv2_sv, if_pos (And.intro h1 h2)]
  have em : fv2_sv M c j (q - 1) = sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1 - 1) := by
    unfold fv2_sv
    split_ifs with h
    · congr 1; push_cast; ring
    · have hq : q = c - M := by omega
      subst hq
      push_cast
      rw [show ((c : ℝ) - M - c + M + 1 - 1) = 0 by ring, sineFn_zero]
  have ep : fv2_sv M c j (q + 1) = sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1 + 1) := by
    unfold fv2_sv
    split_ifs with h
    · congr 1; push_cast; ring
    · have hq : q = c + M := by omega
      subst hq
      have := sineFn_end (2 * M + 1) j
      push_cast at this ⊢
      rw [show ((c : ℝ) + M - c + M + 1 + 1) = 2 * M + 1 + 1 by ring, this]
  rw [e0, em, ep]; exact t

/-- The hypothesis that the odd sub-box of half-width M centred at x lies in the box. -/
def fv2_Fits (M : ℕ) (x : DSite n k) : Prop :=
  M ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) + M < boxN n k ∧ M ≤ (x.2 : ℕ) ∧ (x.2 : ℕ) + M < boxN n k

/-- The 2-D sine mode K of the odd sub-box centred at x, zero-extended to the box. -/
def fv2_E (M : ℕ) (x : DSite n k) (K : Fin (2 * M + 1) × Fin (2 * M + 1)) : DField n k :=
  fun y => fv2_sv M ((x.1 : ℕ) : ℤ) K.1 ((y.1 : ℕ) : ℤ) * fv2_sv M ((x.2 : ℕ) : ℤ) K.2 ((y.2 : ℕ) : ℤ)

theorem fv2_ext_E {M : ℕ} {x : DSite n k} (hfit : fv2_Fits M x)
    (K : Fin (2 * M + 1) × Fin (2 * M + 1)) (q : ℤ × ℤ) :
    ext (fv2_E M x K) q =
      fv2_sv M ((x.1 : ℕ) : ℤ) K.1 q.1 * fv2_sv M ((x.2 : ℕ) : ℤ) K.2 q.2 := by
  obtain ⟨f1, f2, f3, f4⟩ := hfit
  unfold ext
  split_ifs with h
  · simp only [fv2_E]
    rw [Int.toNat_of_nonneg h.1, Int.toNat_of_nonneg h.2.2.1]
  · have : ¬ (((x.1 : ℕ) : ℤ) - M ≤ q.1 ∧ q.1 ≤ ((x.1 : ℕ) : ℤ) + M) ∨
        ¬ (((x.2 : ℕ) : ℤ) - M ≤ q.2 ∧ q.2 ≤ ((x.2 : ℕ) : ℤ) + M) := by omega
    rcases this with h' | h'
    · simp only [fv2_sv]; rw [if_neg h', zero_mul]
    · simp only [fv2_sv]; rw [if_neg h', mul_zero]

/-- The sub-box eigenvalue ε⁻²(sineEig K₁ + sineEig K₂) + m₀² (> 0). -/
def fv2_lam (n : ℕ) (m₀ : ℝ) (M : ℕ) (K : Fin (2 * M + 1) × Fin (2 * M + 1)) : ℝ :=
  (spacing n ^ 2)⁻¹ * (sineEig (2 * M + 1) K.1 + sineEig (2 * M + 1) K.2) + m₀ ^ 2

theorem fv2_lam_pos (n : ℕ) (m₀ : ℝ) (M : ℕ) (K : Fin (2 * M + 1) × Fin (2 * M + 1)) :
    0 < fv2_lam n m₀ M K := by
  have h1 := sineEig_pos (2 * M + 1) K.1 K.1.isLt
  have h2 := sineEig_pos (2 * M + 1) K.2 K.2.isLt
  have hs := spacing_pos n
  exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) (add_pos h1 h2)) (sq_nonneg _)

/-- **Eigen-equation inside the sub-box**: (dirOp e_K)(y) = λ_K e_K(y) for y in the sub-box. -/
theorem fv2_dirOp_E (m₀ : ℝ) {M : ℕ} {x : DSite n k} (hfit : fv2_Fits M x)
    (K : Fin (2 * M + 1) × Fin (2 * M + 1)) (y : DSite n k) (hy : y ∈ fv2_subBox M x) :
    (dirOp n k m₀ *ᵥ fv2_E M x K) y = fv2_lam n m₀ M K * fv2_E M x K y := by
  simp only [fv2_subBox, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have t1 := fv2_sv_three M ((x.1 : ℕ) : ℤ) K.1 (q := ((y.1 : ℕ) : ℤ)) (by omega) (by omega)
  have t2 := fv2_sv_three M ((x.2 : ℕ) : ℤ) K.2 (q := ((y.2 : ℕ) : ℤ)) (by omega) (by omega)
  rw [dirOp_mulVec_apply, fv2_ext_E hfit, fv2_ext_E hfit, fv2_ext_E hfit, fv2_ext_E hfit]
  simp only [site, fv2_E, fv2_lam]
  linear_combination ((spacing n ^ 2)⁻¹ * fv2_sv M ((x.2 : ℕ) : ℤ) K.2 ((y.2 : ℕ) : ℤ)) * t1 +
    ((spacing n ^ 2)⁻¹ * fv2_sv M ((x.1 : ℕ) : ℤ) K.1 ((y.1 : ℕ) : ℤ)) * t2

theorem fv2_E_out {M : ℕ} {x : DSite n k} (K : Fin (2 * M + 1) × Fin (2 * M + 1))
    {y : DSite n k} (hy : y ∉ fv2_subBox M x) : fv2_E M x K y = 0 := by
  simp only [fv2_subBox, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  have : ¬ (((x.1 : ℕ) : ℤ) - M ≤ ((y.1 : ℕ) : ℤ) ∧ ((y.1 : ℕ) : ℤ) ≤ ((x.1 : ℕ) : ℤ) + M) ∨
      ¬ (((x.2 : ℕ) : ℤ) - M ≤ ((y.2 : ℕ) : ℤ) ∧ ((y.2 : ℕ) : ℤ) ≤ ((x.2 : ℕ) : ℤ) + M) := by
    omega
  rcases this with h' | h'
  · simp only [fv2_E, fv2_sv]; rw [if_neg h', zero_mul]
  · simp only [fv2_E, fv2_sv]; rw [if_neg h', mul_zero]

/-- 1-D reindexing: the sub-interval sum of the modes is the side-(2M+1) sine-basis sum. -/
theorem fv2_sv_sum {N M c : ℕ} (h1 : M ≤ c) (h2 : c + M < N) (j l : ℕ) :
    ∑ a : Fin N, fv2_sv M (c : ℤ) j ((a : ℕ) : ℤ) * fv2_sv M (c : ℤ) l ((a : ℕ) : ℤ) =
      ∑ i : Fin (2 * M + 1), sineVec (2 * M + 1) j i * sineVec (2 * M + 1) l i := by
  set F : ℕ → ℝ := fun a => fv2_sv M (c : ℤ) j (a : ℤ) * fv2_sv M (c : ℤ) l (a : ℤ) with hF
  rw [Fin.sum_univ_eq_sum_range F N]
  have hsub : Finset.Ico (c - M) (c + M + 1) ⊆ Finset.range N := by
    intro a ha; simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢; omega
  rw [← Finset.sum_subset hsub (fun a _ ha => by
    simp only [Finset.mem_Ico] at ha
    have : ¬ ((c : ℤ) - M ≤ (a : ℤ) ∧ (a : ℤ) ≤ (c : ℤ) + M) := by omega
    simp only [hF, fv2_sv]; rw [if_neg this, zero_mul])]
  rw [Finset.sum_Ico_eq_sum_range, show c + M + 1 - (c - M) = 2 * M + 1 by omega]
  simp only [sineVec]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => sineFn (2 * M + 1) j ((i : ℝ) + 1) *
    sineFn (2 * M + 1) l ((i : ℝ) + 1)) (2 * M + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hc : (((c - M + i : ℕ) : ℤ) : ℝ) - (c : ℤ) + M + 1 = (i : ℝ) + 1 := by
    push_cast [Nat.cast_sub h1]; ring
  have hin : ((c : ℤ) - M ≤ ((c - M + i : ℕ) : ℤ) ∧ ((c - M + i : ℕ) : ℤ) ≤ (c : ℤ) + M) := by
    omega
  simp only [hF, fv2_sv]
  rw [if_pos hin, if_pos hin, hc]

/-- **Orthonormality of the sub-box modes** on the box: Σ_y e_K(y) e_L(y) = δ_KL. -/
theorem fv2_E_orthonormal {M : ℕ} {x : DSite n k} (hfit : fv2_Fits M x)
    (K L : Fin (2 * M + 1) × Fin (2 * M + 1)) :
    ∑ y : DSite n k, fv2_E M x K y * fv2_E M x L y = if K = L then 1 else 0 := by
  obtain ⟨f1, f2, f3, f4⟩ := hfit
  have hpt : ∀ y : DSite n k, fv2_E M x K y * fv2_E M x L y =
      (fv2_sv M ((x.1 : ℕ) : ℤ) K.1 ((y.1 : ℕ) : ℤ) * fv2_sv M ((x.1 : ℕ) : ℤ) L.1 ((y.1 : ℕ) : ℤ)) *
        (fv2_sv M ((x.2 : ℕ) : ℤ) K.2 ((y.2 : ℕ) : ℤ) *
          fv2_sv M ((x.2 : ℕ) : ℤ) L.2 ((y.2 : ℕ) : ℤ)) := by
    intro y; simp only [fv2_E]; ring
  rw [Finset.sum_congr rfl fun y _ => hpt y, Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum, fv2_sv_sum f1 f2, fv2_sv_sum f3 f4,
    sineVec_orthonormal _ _ _ K.1.isLt L.1.isLt, sineVec_orthonormal _ _ _ K.2.isLt L.2.isLt]
  by_cases h1 : (K.1 : ℕ) = L.1 <;> by_cases h2 : (K.2 : ℕ) = L.2 <;>
    simp [h1, h2, Prod.ext_iff, Fin.ext_iff]

theorem fv2_E_centre {M : ℕ} (x : DSite n k) (K : Fin (2 * M + 1) × Fin (2 * M + 1))
    (hM : M < 2 * M + 1) :
    fv2_E M x K x = sineVec (2 * M + 1) K.1 ⟨M, hM⟩ * sineVec (2 * M + 1) K.2 ⟨M, hM⟩ := by
  have hin : ∀ c : ℤ, c - M ≤ c ∧ c ≤ c + M := fun c => ⟨by omega, by omega⟩
  simp only [fv2_E, fv2_sv, sineVec]
  rw [if_pos (hin _), if_pos (hin _)]
  congr 2 <;> ring

/-- **Centre of a fitting odd sub-box ≤ box variance**: if the odd sub-box of half-width M
centred at x lies in the box, then specVar (2M+1) (m₀²ε²) M M ≤ ε⁻² dirGreen x x (m₀ ≠ 0).
(Variational: the trial field Σ_K e_K(x) λ_K⁻¹ e_K, supported in the sub-box.) -/
theorem fv2_specVar_le_dirVar {m₀ : ℝ} (hm : m₀ ≠ 0) {M : ℕ} {x : DSite n k}
    (hfit : fv2_Fits M x) (hM : M < 2 * M + 1) :
    specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ ≤
      (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x := by
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  have hε0 : spacing n ≠ 0 := (spacing_pos n).ne'
  set ι := Fin (2 * M + 1) × Fin (2 * M + 1)
  set lam := fv2_lam n m₀ M with hlam
  set E := fv2_E M x with hE
  set v : DField n k := ∑ K : ι, (E K x / lam K) • E K with hv
  set S := ∑ K : ι, E K x * E K x / lam K with hS
  have hvx : v x = S := by
    simp only [hv, hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun K _ => by ring
  set w : DField n k := ∑ K : ι, E K x • E K with hw
  have hAv : ∀ y, v y * (dirOp n k m₀ *ᵥ v) y = v y * w y := by
    intro y
    by_cases hy : y ∈ fv2_subBox M x
    · congr 1
      simp only [hv, hw, mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [hE, hlam, fv2_dirOp_E m₀ hfit K y hy]
      have := (fv2_lam_pos n m₀ M K).ne'
      field_simp
    · have : v y = 0 := by
        simp only [hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_eq_zero fun K _ => by rw [hE, fv2_E_out K hy, mul_zero]
      rw [this, zero_mul, zero_mul]
  have hquad : v ⬝ᵥ dirOp n k m₀ *ᵥ v = S := by
    have h1 : v ⬝ᵥ dirOp n k m₀ *ᵥ v = v ⬝ᵥ w := by
      simp only [dotProduct]; exact Finset.sum_congr rfl fun y _ => hAv y
    rw [h1, hv, hw, sum_dotProduct]
    simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hS]
    refine Finset.sum_congr rfl fun K _ => ?_
    have horth : ∀ L : ι, E K ⬝ᵥ E L = if K = L then 1 else 0 := fun L => by
      rw [hE]; exact fv2_E_orthonormal hfit K L
    simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hvar := fv2_two_mul_sub_quad_le hm v x
  rw [hvx, hquad] at hvar
  have hSspec : specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ =
      (spacing n ^ 2)⁻¹ * S := by
    rw [specVar, hS, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    rw [hE, fv2_E_centre x (j₁, j₂) hM, hlam, fv2_lam]
    dsimp only
    have h1 := sineEig_pos (2 * M + 1) j₁ j₁.isLt
    have h2 := sineEig_pos (2 * M + 1) j₂ j₂.isLt
    have hd : 0 < m₀ ^ 2 * spacing n ^ 2 + sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂ := by
      positivity
    have hd' : 0 < (spacing n ^ 2)⁻¹ * (sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂)
        + m₀ ^ 2 := by positivity
    field_simp
    ring
  rw [hSspec]
  have : 2 * S - S = S := by ring
  rw [this] at hvar
  exact mul_le_mul_of_nonneg_left hvar (by positivity)

/-- **The site bound for a fitting sub-box.** If the odd sub-box of half-width M centred at x lies
in the box (m₀ ≠ 0): b(x) = freeVar − ε⁻² dirGreen x x ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))). -/
theorem fv2_wick_defect_le_of_fits {m₀ : ℝ} (hm : m₀ ≠ 0) {M : ℕ} {x : DSite n k}
    (hfit : fv2_Fits M x) :
    freeVar n m₀ - (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((M : ℝ) + 1))))) := by
  have hM : M < 2 * M + 1 := by omega
  have h1 := fv2_specVar_le_dirVar hm hfit hM
  have h2 := fv2_freeVar_sub_centre_le (n := n) hm M hM
  rw [← mul_assoc]
  linarith

/-- The lattice distance M(x) = min(x₁, N−1−x₁, x₂, N−1−x₂) of the site x to the last box sites;
the zero (Dirichlet) sites are at lattice distance M(x) + 1. -/
def fv2_bdist (x : DSite n k) : ℕ :=
  min (min (x.1 : ℕ) (boxN n k - 1 - x.1)) (min (x.2 : ℕ) (boxN n k - 1 - x.2))

/-- The physical distance r(x) = ε (M(x) + 1) from x to the Dirichlet boundary (the nearest
zero site, in the sup norm). -/
def fv2_rdist (n k : ℕ) (x : DSite n k) : ℝ := spacing n * ((fv2_bdist x : ℝ) + 1)

theorem fv2_fits_bdist (x : DSite n k) : fv2_Fits (fv2_bdist x) x := by
  have h1 := x.1.isLt
  have h2 := x.2.isLt
  unfold fv2_Fits fv2_bdist
  omega

/-- **Goal 3: the Wick defect at a site.** For m₀ ≠ 0 and every site x of the box,
b(x) = freeVar − ε⁻² dirGreen x x ≤ (π/4)(1 + log⁺(1/(|m₀| r(x)))), r(x) = ε (M(x) + 1) the
physical distance to the Dirichlet boundary. (With `dirVar_le_freeVar`, 0 ≤ b(x).) -/
theorem fv2_wick_defect_le {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) :
    freeVar n m₀ - (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * fv2_rdist n k x))) :=
  fv2_wick_defect_le_of_fits hm (fv2_fits_bdist x)

end PP2Target

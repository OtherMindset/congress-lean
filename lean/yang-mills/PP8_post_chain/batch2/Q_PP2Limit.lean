import LongTable.P_mwwgf25i_d0aeg1

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Limit.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction. Node M8, session 1:
existence of limit points of the Dirichlet-box generating functionals `ZD` of the third target
(#mww4cze7-bk8bxu), by a diagonal (Arzelà–Ascoli type) argument conditional on a uniform
equicontinuity estimate.

FORMALIZED.
* `norm_ZD_le_one`: ‖ZD n k m₀ λ P f‖ ≤ 1 for EVERY n, k, m₀, λ, P, f, with no hypotheses:
  ‖∫ e^{iφ(f)} w‖ ≤ ∫ w, and if the partition function ∫ w vanishes (non-integrable weight, Bochner
  convention) then ZD = 0. (This discharges hypothesis (H3) `hZ` of `conditional_clustering` in
  PP2Conditional.)
* `norm_ZD_sub_le` (first step of the equicontinuity estimate; λ ≥ 0, m₀ ≠ 0, quartic):
    ‖ZD n k f − ZD n k g‖ ≤ ∫ |φ(f − g)| w / ∫ w = ⟨|φ(f − g)|⟩,
  uniformly in n, k; with `norm_cexp_sub_cexp_le` (|e^{ia} − e^{ib}| ≤ |a − b|), `dsmear_sub`,
  `continuous_dsmear`, `integrable_abs_dsmear_mul` (|φ(h)|·w integrable, from the moment
  integrability of PP2Griffiths3).
* `exists_subseq_tendsto_of_equicont` (abstract extraction): let Z_j : X → ℂ (j ∈ ℕ), ‖Z_j‖ ≤ 1,
  and ρ : X → X → ℝ with ‖Z_j x − Z_j y‖ ≤ ρ x y for all j; if a countable D ⊆ X is ρ-dense
  (∀ x ε > 0, ∃ d ∈ D, ρ x d < ε), then a strictly increasing j ↦ φ j and a W : X → ℂ exist with
  Z_{φ j} x → W x for every x. Proof: (D → ℂ) is metrizable (D countable), the product of closed
  unit discs is compact (Tychonoff), so a subsequence converges on D; equicontinuity and
  ρ-density make (Z_{φ j} x) Cauchy for every x, and ℂ is complete.
* `UniformEquicont m₀ λ`: ∃ C, (a, b) such that for all n, k, f, g
    ‖ZD n k (f) − ZD n k (g)‖ ≤ C · ‖f − g‖_{a,b},
  ‖·‖_{a,b} = `schwartzSup a b` = sup of the Schwartz seminorms of indices ≤ (a, b).
* `SchwartzSeparable`: for every (a, b), a countable subset of TestFn is dense for ‖·‖_{a,b}.
* `exists_limitPoint_of_equicont`: `UniformEquicont m₀ λ` and `SchwartzSeparable` give
  `∃ Z, IsLimitPoint m₀ λ Z` (along the diagonal n_j = k_j = φ j → ∞).

WHY `UniformEquicont` IS THE RIGHT INPUT (not formalized). |e^{ia} − e^{ib}| ≤ |a − b| and
dsmear is linear in f, so with h = f − g
  ‖ZD f − ZD g‖ ≤ ⟨|φ(h)|⟩ ≤ ⟨φ(h)²⟩^{1/2},  ⟨φ(h)²⟩ = ε⁴ Σ_x Σ_y h(x) h(y) ⟨φ_x φ_y⟩.
A uniform two-point bound of the form sup_x ε² Σ_y |⟨φ_x φ_y⟩| ≤ K (uniform in n, k; it holds
when the two-point function decays exponentially with a log-integrable diagonal, BFS–Spencer)
gives ⟨φ(h)²⟩ ≤ K ‖h‖_∞ · ε² Σ_x |h(dpos x)|, and ε² Σ_x |h(dpos x)| ≤ c · sup_p (1 + ‖p‖)³ |h(p)|
(Riemann-sum bound, cf. `riemann_bound` of PP2Conditional, applied on dyadic shells). Both
factors are ≤ c'·‖h‖_{3,0}, so `UniformEquicont m₀ λ` holds with (a, b) = (3, 0) and
C = (c' K)^{1/2}.

NOT formalized.
* ⟨|φ(h)|⟩ ≤ ⟨φ(h)²⟩^{1/2} (Cauchy–Schwarz against `gibbs`) and the expansion of ⟨φ(h)²⟩.
* The uniform two-point bound itself, the Riemann-sum bound for non-compactly supported h, and
  hence `UniformEquicont` (an analytic input, nodes M1–M6 / M8 later sessions).
* `SchwartzSeparable` (true: 𝓢(ℝ²) is a separable Fréchet space, e.g. Hermite functions with
  rational coefficients are dense; not in this Mathlib, so a hypothesis here).
* That every limit point is non-Gaussian, translation/rotation invariance, OS axioms.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace PP2Target

/-! ## |ZD| ≤ 1 -/

/-- The Dirichlet-box generating functional has norm ≤ 1, unconditionally. -/
theorem norm_ZD_le_one (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (f : TestFn) :
    ‖ZD n k m₀ lam P f‖ ≤ 1 := by
  unfold ZD
  have hw : ∀ φ : DField n k, 0 < dweight n k m₀ lam P φ := fun φ => Real.exp_pos _
  have hI : 0 ≤ ∫ φ : DField n k, dweight n k m₀ lam P φ :=
    integral_nonneg fun φ => (hw φ).le
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI]
  apply div_le_one_of_le₀ _ hI
  calc ‖∫ φ : DField n k, Complex.exp (Complex.I * (dsmear n k f φ : ℂ))
          * (dweight n k m₀ lam P φ : ℂ)‖
      ≤ ∫ φ : DField n k, ‖Complex.exp (Complex.I * (dsmear n k f φ : ℂ))
          * (dweight n k m₀ lam P φ : ℂ)‖ := norm_integral_le_integral_norm _
    _ = ∫ φ : DField n k, dweight n k m₀ lam P φ := by
      refine integral_congr_ae (Eventually.of_forall fun φ => ?_)
      simp only
      rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw φ)]

/-! ## Abstract extraction theorem -/

/-- **Diagonal extraction.** A uniformly bounded, equicontinuous (w.r.t. ρ) sequence of complex
functions on a space with a countable ρ-dense subset has a pointwise convergent subsequence. -/
theorem exists_subseq_tendsto_of_equicont {X : Type*} (Z : ℕ → X → ℂ) (ρ : X → X → ℝ)
    (hbd : ∀ j x, ‖Z j x‖ ≤ 1) (heq : ∀ j x y, ‖Z j x - Z j y‖ ≤ ρ x y)
    (D : Set X) (hD : D.Countable) (hdense : ∀ x, ∀ ε > 0, ∃ d ∈ D, ρ x d < ε) :
    ∃ (φ : ℕ → ℕ) (W : X → ℂ), StrictMono φ ∧
      ∀ x, Tendsto (fun j => Z (φ j) x) atTop (𝓝 (W x)) := by
  have := hD.to_subtype
  let s : Set (D → ℂ) := Set.univ.pi fun _ => Metric.closedBall 0 1
  have hs : IsCompact s := isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  obtain ⟨a, -, φ, hφ, hlim⟩ := hs.tendsto_subseq (x := fun j (d : D) => Z j d)
    (fun j d _ => by simpa using hbd j d)
  have hD' : ∀ d : D, Tendsto (fun j => Z (φ j) d) atTop (𝓝 (a d)) :=
    fun d => tendsto_pi_nhds.1 hlim d
  have hcauchy : ∀ x, CauchySeq (fun j => Z (φ j) x) := by
    intro x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨d, hdD, hd⟩ := hdense x (ε / 3) (by positivity)
    have hc := (hD' ⟨d, hdD⟩).cauchySeq
    rw [Metric.cauchySeq_iff'] at hc
    obtain ⟨N, hN⟩ := hc (ε / 3) (by positivity)
    refine ⟨N, fun j hj => ?_⟩
    have h1 : dist (Z (φ j) x) (Z (φ j) d) ≤ ρ x d := by
      rw [dist_eq_norm]; exact heq _ _ _
    have h2 : dist (Z (φ N) d) (Z (φ N) x) ≤ ρ x d := by
      rw [dist_eq_norm, norm_sub_rev]; exact heq _ _ _
    have h3 : dist (Z (φ j) d) (Z (φ N) d) < ε / 3 := hN j hj
    calc dist (Z (φ j) x) (Z (φ N) x)
        ≤ dist (Z (φ j) x) (Z (φ j) d) + dist (Z (φ j) d) (Z (φ N) d)
          + dist (Z (φ N) d) (Z (φ N) x) := dist_triangle4 _ _ _ _
      _ < ε := by linarith
  exact ⟨φ, fun x => limUnder atTop (fun j => Z (φ j) x), hφ,
    fun x => (hcauchy x).tendsto_limUnder⟩

/-! ## First step of the equicontinuity estimate -/

theorem norm_cexp_sub_cexp_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have h : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
      = Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [h, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

theorem dsmear_sub (n k : ℕ) (f g : TestFn) (φ : DField n k) :
    dsmear n k (f - g) φ = dsmear n k f φ - dsmear n k g φ := by
  simp only [dsmear, sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem continuous_dsmear (n k : ℕ) (f : TestFn) : Continuous (dsmear n k f) := by
  unfold dsmear; fun_prop

/-- For λ ≥ 0, m₀ ≠ 0, |φ(h)| · dweight is integrable. -/
theorem integrable_abs_dsmear_mul {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (n k : ℕ) (h : TestFn) :
    Integrable fun φ : DField n k =>
      |dsmear n k h φ| * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  have hmono : ∀ x : DSite n k, Integrable fun φ : DField n k =>
      φ x * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
    intro x
    refine (PP2Griffiths.integrable_mono_dweight hm hlam (Pi.single x 1)).congr
      (Eventually.of_forall fun φ => ?_)
    simp only
    congr 1
    rw [Finset.prod_eq_single x (fun y _ hy => by simp [hy])
      (fun hx => absurd (Finset.mem_univ x) hx)]
    simp
  have hG : Integrable fun φ : DField n k => ∑ x : DSite n k,
      spacing n ^ 2 * |h (dpos n k x)| * ‖φ x * dweight n k m₀ lam (Polynomial.X ^ 4) φ‖ :=
    integrable_finsetSum _ fun x _ => (hmono x).norm.const_mul _
  refine hG.mono' (((continuous_dsmear n k h).abs.mul
    (PP2Griffiths.continuous_dweight m₀ lam _)).aestronglyMeasurable)
    (Eventually.of_forall fun φ => ?_)
  have hw : 0 < dweight n k m₀ lam (Polynomial.X ^ 4) φ := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos hw]
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  calc |dsmear n k h φ| * dweight n k m₀ lam (Polynomial.X ^ 4) φ
      ≤ (spacing n ^ 2 * ∑ x : DSite n k, |h (dpos n k x)| * |φ x|)
          * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
        gcongr
        unfold dsmear
        rw [abs_mul, abs_of_nonneg hε]
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
    _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]; ring

/-- **First step of the equicontinuity estimate** (λ ≥ 0, m₀ ≠ 0):
‖ZD f − ZD g‖ ≤ ⟨|φ(f − g)|⟩, uniformly in n, k. -/
theorem norm_ZD_sub_le {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (n k : ℕ) (f g : TestFn) :
    ‖ZD n k m₀ lam (Polynomial.X ^ 4) f - ZD n k m₀ lam (Polynomial.X ^ 4) g‖
      ≤ (∫ φ : DField n k, |dsmear n k (f - g) φ| * dweight n k m₀ lam (Polynomial.X ^ 4) φ)
        / ∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  set w := dweight n k m₀ lam (Polynomial.X ^ 4) with hwdef
  have hw : ∀ φ : DField n k, 0 < w φ := fun φ => Real.exp_pos _
  have hI : 0 ≤ ∫ φ : DField n k, w φ := integral_nonneg fun φ => (hw φ).le
  have hint : ∀ h : TestFn, Integrable fun φ : DField n k =>
      Complex.exp (Complex.I * (dsmear n k h φ : ℂ)) * (w φ : ℂ) := by
    intro h
    refine (PP2Griffiths.integrable_dweight hm hlam).mono'
      ((((Complex.continuous_ofReal.comp (continuous_dsmear n k h)).const_mul Complex.I).cexp.mul
        (Complex.continuous_ofReal.comp (PP2Griffiths.continuous_dweight m₀ lam _))
        ).aestronglyMeasurable) (Eventually.of_forall fun φ => ?_)
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw φ)]
  unfold ZD
  rw [← sub_div, ← integral_sub (hint f) (hint g), norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hI]
  apply div_le_div_of_nonneg_right _ hI
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (Eventually.of_forall fun φ => norm_nonneg _)
      (integrable_abs_dsmear_mul hm hlam n k (f - g)) (Eventually.of_forall fun φ => ?_))
  simp only
  rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw φ), dsmear_sub]
  exact mul_le_mul_of_nonneg_right (norm_cexp_sub_cexp_le _ _) (hw φ).le

/-! ## Specialisation to the Dirichlet-box functionals -/

/-- The sup of the Schwartz seminorms ‖·‖_{i,j} over (i, j) ≤ (a, b). -/
def schwartzSup (a b : ℕ) : Seminorm ℝ TestFn :=
  (Finset.Iic (a, b)).sup (schwartzSeminormFamily ℝ Plane ℝ)

/-- Uniform (in n, k) Lipschitz continuity of ZD for one finite Schwartz seminorm. -/
def UniformEquicont (m₀ lam : ℝ) : Prop :=
  ∃ (C : ℝ) (a b : ℕ), ∀ (n k : ℕ) (f g : TestFn),
    ‖ZD n k m₀ lam (Polynomial.X ^ 4) f - ZD n k m₀ lam (Polynomial.X ^ 4) g‖
      ≤ C * schwartzSup a b (f - g)

/-- Separability of the Schwartz space for each finite seminorm (true; not in Mathlib). -/
def SchwartzSeparable : Prop :=
  ∀ a b : ℕ, ∃ D : Set TestFn, D.Countable ∧
    ∀ f : TestFn, ∀ ε > 0, ∃ d ∈ D, schwartzSup a b (f - d) < ε

/-- **Existence of limit points**, conditional on the uniform equicontinuity estimate and on
separability of the Schwartz space. -/
theorem exists_limitPoint_of_equicont {m₀ lam : ℝ} (hE : UniformEquicont m₀ lam)
    (hS : SchwartzSeparable) : ∃ Z, IsLimitPoint m₀ lam Z := by
  obtain ⟨C, a, b, hC⟩ := hE
  obtain ⟨D, hD, hdense⟩ := hS a b
  set C' := |C| + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  obtain ⟨φ, W, hφ, hW⟩ := exists_subseq_tendsto_of_equicont
    (fun j f => ZD j j m₀ lam (Polynomial.X ^ 4) f)
    (fun f g => C' * schwartzSup a b (f - g))
    (fun j f => norm_ZD_le_one _ _ _ _ _ _)
    (fun j f g => (hC j j f g).trans
      (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_abs_self C])
        (apply_nonneg _ _)))
    D hD
    (fun f ε hε => by
      obtain ⟨d, hd, hlt⟩ := hdense f (ε / C') (by positivity)
      refine ⟨d, hd, ?_⟩
      have := mul_lt_mul_of_pos_left hlt hC'pos
      rwa [mul_div_cancel₀ _ hC'pos.ne'] at this)
  exact ⟨W, φ, φ, hφ.tendsto_atTop, hφ.tendsto_atTop, hW⟩

end PP2Target

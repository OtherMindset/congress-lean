import LongTable.R_PP2LebowitzA

/-!
Part B of PP2Lebowitz (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Lebowitz.lean)

FORMALIZED in this part.
* **Single-site hypothesis** `LebowitzSite w`: in Hadamard coordinates (A,B,C,D),
  w(y₁)w(y₂)w(y₃)w(y₄) · exp(c·ABCD) is even in each of A, B, C, D separately, for some c ≥ 0
  (i.e. the four-copy weight is "even part × exp(−c ABCD)", c ≥ 0).
  `lebowitzSite_quartic`: exp(−(a y⁴ + b y² + d)) satisfies it for every a ≥ 0 and ANY b, d
  (c = 6a; Σ yᵢ⁴ = ¼(Σ A⁴ + 6 Σ_{pairs} A²B²) + 6ABCD).
  `lebowitzSite_siteWeight`: hence the box weight `siteWeight n k m₀ λ X⁴ x` for λ ≥ 0.
  Not every even weight works: for the spin-1 law P(±1) = p/2, P(0) = 1 − p one site already
  gives u₄ = p − 3p² > 0 when p < 1/3; that weight has no such factorization.
* `mom`, `mom_odd` (odd moments of an even density vanish), `integral_lp` (Fubini for
  two-copy list polynomials), transfer lemmas `integral_K2`, `integrable_K2`.
* `expect`, **`ursell4`** u₄(i,j,k,l) = ⟨φᵢφⱼφₖφₗ⟩ − ⟨φᵢφⱼ⟩⟨φₖφₗ⟩ − ⟨φᵢφₖ⟩⟨φⱼφₗ⟩ − ⟨φᵢφₗ⟩⟨φⱼφₖ⟩.
* **`lebowitz_ferro`**: u₄ ≤ 0 for ρ = exp(Σ J φφ) ∏ w_x(φ_x), J ≥ 0, w_x even, ≥ 0, with
  `LebowitzSite (w x)`, and integrable monomial moments (no hypothesis on ∫ρ > 0: if it is 0
  then u₄ = 0). Route: with t, s two copies and P = (tᵢ+sᵢ)(tⱼ+sⱼ), Q = (tₖ−sₖ)(tₗ−sₗ),
  Cov₂(P, Q) = 2 Z⁴ u₄ (first duplication, `integral_lp` + odd moments); then
  `integral_dup_expand` writes 2 Cov₂(P,Q) as a four-copy integral, which is ≤ 0.
* **`lebowitz_dexpect`**, `lebowitz_gibbs`: the Lebowitz inequality for the quartic Dirichlet-box
  measure `dweight n k m₀ λ X⁴` (λ ≥ 0, m₀ ≠ 0), any four sites.
* **`isNonGaussian_of_norm_ne`**: a Gaussian functional exp(iℓ(f) − B(f,f)/2) has
  ‖Z(2f)‖ = ‖Z(f)‖⁴, so one f with ‖Z(2f)‖ ≠ ‖Z(f)‖⁴ gives `IsNonGaussian Z`. This is the
  cheapest route: it is a pointwise condition, so it passes to limits with no control of moments
  of the limit (no derivatives of Z at 0 needed).
* `QuarticDeficit m₀ λ` (∃ f, δ > 0: ‖Z_D(2f)‖ + δ ≤ ‖Z_D(f)‖⁴ for all n ≥ N₀, k ≥ K₀) and
  **`isNonGaussian_of_quarticDeficit`**: it implies the M9 clause
  `∀ Z, IsLimitPoint m₀ λ Z → IsNonGaussian Z` of `PhiFourTwoGapV3`.

NOT formalized (remaining M9 work, sessions 2-3).
* The strict, cutoff-uniform bound u₄(f,f,f,f) ≤ −δ' < 0 on the smeared Ursell function
  (tree-level lower bound; Lebowitz only gives ≤ 0), and uniform bounds on the 2nd and 6th
  smeared moments.
* The Taylor step from those bounds to `QuarticDeficit`: for symmetric X = φ(tf),
  E cos 2tX − (E cos tX)⁴ = (t⁴/2)(E X⁴ − 3(E X²)²) + O(t⁶ (E X⁶ + (E X²)³)), and Z_D is real
  (even measure), so for t small ‖Z_D(2tf)‖ + δ ≤ ‖Z_D(tf)‖⁴ uniformly.
* The multilinear expansion u₄(f,f,f,f) = Σ f f f f u₄(x,y,z,w) (and hence u₄(f,f,f,f) ≤ 0 for
  f ≥ 0) is not written out.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset PP2Target

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Lebowitz

open PP2Griffiths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A list-polynomial in two copies: Σ_a c_a (∏_{L_a} t) (∏_{L'_a} s). -/
def lp (T : List (ℝ × List ι × List ι)) (q : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  (T.map fun a => a.1 * (a.2.1.map q.1).prod * (a.2.2.map q.2).prod).sum

/-- Fubini for list-polynomials against ρ(t)ρ(s). -/
theorem integral_lp {ρ : (ι → ℝ) → ℝ}
    (hint : ∀ L : List ι, Integrable fun φ => (L.map φ).prod * ρ φ)
    (T : List (ℝ × List ι × List ι)) :
    Integrable (fun q : (ι → ℝ) × (ι → ℝ) => lp T q * (ρ q.1 * ρ q.2)) ∧
      ∫ q : (ι → ℝ) × (ι → ℝ), lp T q * (ρ q.1 * ρ q.2)
        = (T.map fun a => a.1 * mom ρ a.2.1 * mom ρ a.2.2).sum := by
  induction T with
  | nil => simp [lp]
  | cons a T ih =>
    have ha : Integrable fun q : (ι → ℝ) × (ι → ℝ) =>
        a.1 * (((a.2.1.map q.1).prod * ρ q.1) * ((a.2.2.map q.2).prod * ρ q.2)) :=
      ((hint a.2.1).mul_prod (hint a.2.2)).const_mul a.1
    have e : ∀ q : (ι → ℝ) × (ι → ℝ), lp (a :: T) q * (ρ q.1 * ρ q.2) =
        a.1 * (((a.2.1.map q.1).prod * ρ q.1) * ((a.2.2.map q.2).prod * ρ q.2))
          + lp T q * (ρ q.1 * ρ q.2) := fun q => by
      simp only [lp, List.map_cons, List.sum_cons]; ring
    simp_rw [e]
    refine ⟨ha.add ih.1, ?_⟩
    have hp : ∫ q : (ι → ℝ) × (ι → ℝ), ((a.2.1.map q.1).prod * ρ q.1) * ((a.2.2.map q.2).prod * ρ q.2)
        = (∫ φ, (a.2.1.map φ).prod * ρ φ) * ∫ φ, (a.2.2.map φ).prod * ρ φ :=
      integral_prod_mul (fun φ => (a.2.1.map φ).prod * ρ φ) (fun φ => (a.2.2.map φ).prod * ρ φ)
    rw [integral_add ha ih.1, ih.2, integral_const_mul, hp]
    simp only [List.map_cons, List.sum_cons, mom]
    ring

/-- The pair space ι ⊕ ι → ℝ as (ι → ℝ) × (ι → ℝ). -/
abbrev eK2 : (ι ⊕ ι → ℝ) ≃ᵐ (ι → ℝ) × (ι → ℝ) := MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)

lemma integral_K2 (G : (ι ⊕ ι → ℝ) → ℝ) :
    ∫ ξ, G ξ = ∫ q : (ι → ℝ) × (ι → ℝ), G (eK2.symm q) :=
  ((volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℝ)).integral_comp'
    (f := eK2.symm) G).symm

lemma integrable_K2 {G : (ι ⊕ ι → ℝ) → ℝ}
    (h : Integrable fun q : (ι → ℝ) × (ι → ℝ) => G (eK2.symm q)) : Integrable G :=
  ((volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℝ)).integrable_comp_emb
    (eK2 (ι := ι)).symm.measurableEmbedding).mp h

lemma eK2_symm_inl (q : (ι → ℝ) × (ι → ℝ)) (x : ι) : eK2.symm q (.inl x) = q.1 x := rfl
lemma eK2_symm_inr (q : (ι → ℝ) × (ι → ℝ)) (x : ι) : eK2.symm q (.inr x) = q.2 x := rfl

/-! ## The Lebowitz inequality -/

/-- Normalised expectation ⟨F⟩_ρ = ∫ F ρ / ∫ ρ (Bochner integrals; 0 if ∫ ρ = 0). -/
def expect (ρ : (ι → ℝ) → ℝ) (F : (ι → ℝ) → ℝ) : ℝ := (∫ φ, F φ * ρ φ) / ∫ φ, ρ φ

/-- **The truncated four-point (Ursell) function**
u₄(i,j,k,l) = ⟨φᵢφⱼφₖφₗ⟩ − ⟨φᵢφⱼ⟩⟨φₖφₗ⟩ − ⟨φᵢφₖ⟩⟨φⱼφₗ⟩ − ⟨φᵢφₗ⟩⟨φⱼφₖ⟩. -/
def ursell4 (ρ : (ι → ℝ) → ℝ) (i j k l : ι) : ℝ :=
  expect ρ (fun φ => φ i * φ j * φ k * φ l)
    - expect ρ (fun φ => φ i * φ j) * expect ρ (fun φ => φ k * φ l)
    - expect ρ (fun φ => φ i * φ k) * expect ρ (fun φ => φ j * φ l)
    - expect ρ (fun φ => φ i * φ l) * expect ρ (fun φ => φ j * φ k)

lemma expect_two (ρ : (ι → ℝ) → ℝ) (a b : ι) :
    expect ρ (fun φ => φ a * φ b) = mom ρ [a, b] / mom ρ [] := by
  simp only [expect, mom, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    one_mul]

lemma expect_four (ρ : (ι → ℝ) → ℝ) (a b c d : ι) :
    expect ρ (fun φ => φ a * φ b * φ c * φ d) = mom ρ [a, b, c, d] / mom ρ [] := by
  simp only [expect, mom, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    one_mul, mul_assoc]

/-- **The Lebowitz inequality, general form.** For a ferromagnetic density
ρ = exp(Σ J φφ) ∏ w_x(φ_x) with J ≥ 0 and each w_x even, ≥ 0 and satisfying the single-site
condition `LebowitzSite`, and all monomial moments integrable, u₄(i,j,k,l) ≤ 0. -/
theorem lebowitz_ferro {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) (hw : ∀ x, LebowitzSite (w x)) {J : ι → ι → ℝ}
    (hJ : ∀ x y, 0 ≤ J x y)
    (hint : ∀ L : List ι, Integrable fun φ => (L.map φ).prod * ferroDensity w J φ)
    (i j k l : ι) : ursell4 (ferroDensity w J) i j k l ≤ 0 := by
  set ρ := ferroDensity w J with hρdef
  have hρ : ∀ φ : ι → ℝ, ρ (fun x => -φ x) = ρ φ := fun φ => by
    simp only [hρdef, ferroDensity, hw_even, mul_neg, neg_mul, neg_neg]
  have hodd1 : ∀ a, mom ρ [a] = 0 := fun a => mom_odd hρ ⟨0, rfl⟩
  have hodd3 : ∀ a b c, mom ρ [a, b, c] = 0 := fun a b c => mom_odd hρ ⟨1, rfl⟩
  -- the four two-copy integrands as list-polynomials
  set TPQ : List (ℝ × List ι × List ι) :=
    [(1, [i, j, k, l], []), (-1, [i, j, k], [l]), (-1, [i, j, l], [k]), (1, [i, j], [k, l]),
     (1, [i, k, l], [j]), (-1, [i, k], [j, l]), (-1, [i, l], [j, k]), (1, [i], [j, k, l]),
     (1, [j, k, l], [i]), (-1, [j, k], [i, l]), (-1, [j, l], [i, k]), (1, [j], [i, k, l]),
     (1, [k, l], [i, j]), (-1, [k], [i, j, l]), (-1, [l], [i, j, k]), (1, [], [i, j, k, l])]
  set TP : List (ℝ × List ι × List ι) :=
    [(1, [i, j], []), (1, [i], [j]), (1, [j], [i]), (1, [], [i, j])]
  set TQ : List (ℝ × List ι × List ι) :=
    [(1, [k, l], []), (-1, [k], [l]), (-1, [l], [k]), (1, [], [k, l])]
  set T1 : List (ℝ × List ι × List ι) := [(1, [], [])]
  have ePQ : ∀ q, Pobs i j (eK2.symm q) * Qobs k l (eK2.symm q) * rho2 ρ (eK2.symm q)
      = lp TPQ q * (ρ q.1 * ρ q.2) := fun q => by
    simp only [Pobs, Qobs, rho2, eK2_symm_inl, eK2_symm_inr, lp, TPQ, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil]
    ring
  have eP : ∀ q, Pobs i j (eK2.symm q) * rho2 ρ (eK2.symm q) = lp TP q * (ρ q.1 * ρ q.2) :=
    fun q => by
    simp only [Pobs, rho2, eK2_symm_inl, eK2_symm_inr, lp, TP, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil]
    ring
  have eQ : ∀ q, Qobs k l (eK2.symm q) * rho2 ρ (eK2.symm q) = lp TQ q * (ρ q.1 * ρ q.2) :=
    fun q => by
    simp only [Qobs, rho2, eK2_symm_inl, eK2_symm_inr, lp, TQ, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil]
    ring
  have e1 : ∀ q, rho2 ρ (eK2.symm q) = lp T1 q * (ρ q.1 * ρ q.2) := fun q => by
    simp only [rho2, eK2_symm_inl, eK2_symm_inr, lp, T1, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.prod_nil]
    ring
  have iPQ := integral_lp hint TPQ
  have iP := integral_lp hint TP
  have iQ := integral_lp hint TQ
  have i1 := integral_lp hint T1
  have hABρ : Integrable fun ξ => Pobs i j ξ * Qobs k l ξ * rho2 ρ ξ :=
    integrable_K2 (by simp_rw [ePQ]; exact iPQ.1)
  have hAρ : Integrable fun ξ => Pobs i j ξ * rho2 ρ ξ :=
    integrable_K2 (by simp_rw [eP]; exact iP.1)
  have hBρ : Integrable fun ξ => Qobs k l ξ * rho2 ρ ξ :=
    integrable_K2 (by simp_rw [eQ]; exact iQ.1)
  have hρ2 : Integrable fun ξ => rho2 ρ ξ :=
    integrable_K2 (by simp_rw [e1]; exact i1.1)
  set Z := mom ρ []
  set M4 := mom ρ [i, j, k, l]
  have vPQ : ∫ ξ, Pobs i j ξ * Qobs k l ξ * rho2 ρ ξ
      = 2 * (M4 * Z + mom ρ [i, j] * mom ρ [k, l] - mom ρ [i, k] * mom ρ [j, l]
        - mom ρ [i, l] * mom ρ [j, k]) := by
    rw [integral_K2]; simp_rw [ePQ]; rw [iPQ.2]
    simp only [TPQ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hodd1, hodd3]
    ring
  have vP : ∫ ξ, Pobs i j ξ * rho2 ρ ξ = 2 * (mom ρ [i, j] * Z) := by
    rw [integral_K2]; simp_rw [eP]; rw [iP.2]
    simp only [TP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hodd1]
    ring
  have vQ : ∫ ξ, Qobs k l ξ * rho2 ρ ξ = 2 * (mom ρ [k, l] * Z) := by
    rw [integral_K2]; simp_rw [eQ]; rw [iQ.2]
    simp only [TQ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hodd1]
    ring
  have v1 : ∫ ξ, rho2 ρ ξ = Z * Z := by
    rw [integral_K2]; simp_rw [e1]; rw [i1.2]
    simp only [T1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have dup := integral_dup_expand (ρ := rho2 ρ) (A := Pobs i j) (B := Qobs k l) hABρ hAρ hBρ hρ2
  have htr : ∫ ψ : K4 ι → ℝ, lev2 ρ i j k l ψ
      = ∫ q : (ι ⊕ ι → ℝ) × (ι ⊕ ι → ℝ), (Pobs i j q.1 - Pobs i j q.2)
        * (Qobs k l q.1 - Qobs k l q.2) * rho2 ρ q.1 * rho2 ρ q.2 :=
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : K4 ι => ℝ)).integral_comp'
      (f := MeasurableEquiv.sumPiEquivProdPi (fun _ : K4 ι => ℝ))
      (fun q : (ι ⊕ ι → ℝ) × (ι ⊕ ι → ℝ) => (Pobs i j q.1 - Pobs i j q.2)
        * (Qobs k l q.1 - Qobs k l q.2) * rho2 ρ q.1 * rho2 ρ q.2)
  have hneg := integral_lev2_nonpos hw_nonneg hw hJ i j k l
  rw [← hρdef, htr, dup, vPQ, vP, vQ, v1] at hneg
  set X := M4 * Z - (mom ρ [i, j] * mom ρ [k, l] + mom ρ [i, k] * mom ρ [j, l]
    + mom ρ [i, l] * mom ρ [j, k]) with hX
  have hu : ursell4 ρ i j k l = X / Z ^ 2 := by
    simp only [ursell4, expect_two, expect_four]
    rw [show mom ρ [] = Z from rfl, show mom ρ [i, j, k, l] = M4 from rfl]
    by_cases hZ : Z = 0
    · simp [hZ]
    · field_simp
      ring
  rw [hu]
  by_cases hZ : Z = 0
  · simp [hZ]
  · have hZ2 : 0 < Z ^ 2 := by positivity
    have hXn : X ≤ 0 := by
      by_contra h
      have := mul_pos hZ2 (not_le.mp h)
      nlinarith
    exact div_nonpos_iff.mpr (Or.inr ⟨hXn, hZ2.le⟩)

/-! ## Application: the quartic Dirichlet-box measure -/

lemma list_prod_eq_mono (L : List ι) (φ : ι → ℝ) : (L.map φ).prod = ∏ x, φ x ^ L.count x := by
  rw [Finset.prod_list_map_count]
  exact Finset.prod_subset (subset_univ _) fun x _ hx => by
    rw [List.count_eq_zero_of_not_mem (by simpa using hx), pow_zero]

section Model

variable {n k : ℕ}

/-- The box single-site weight exp(−(4 + ε²m₀²)y²/2 − λε² :y⁴:) satisfies the Lebowitz condition
for λ ≥ 0 (its y⁴ coefficient is λε² ≥ 0; the y² coefficient, of either sign, is irrelevant). -/
theorem lebowitzSite_siteWeight (m₀ : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (x : DSite n k) :
    LebowitzSite (siteWeight n k m₀ lam (Polynomial.X ^ 4) x) := by
  have h : siteWeight n k m₀ lam (Polynomial.X ^ 4) x = fun y => Real.exp (-(
      lam * spacing n ^ 2 * y ^ 4
      + ((4 + spacing n ^ 2 * m₀ ^ 2) / 2 - 6 * lam * spacing n ^ 2 * freeVar n m₀) * y ^ 2
      + 3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) := by
    funext y; rw [siteWeight_eq, wickPoly_X4]; congr 1; ring
  rw [h]
  exact lebowitzSite_quartic (by positivity) _ _

/-- **The Lebowitz inequality for the quartic Dirichlet-box measure** (λ ≥ 0, m₀ ≠ 0):
u₄(a,b,c,d) = ⟨φ_aφ_bφ_cφ_d⟩ − ⟨φ_aφ_b⟩⟨φ_cφ_d⟩ − ⟨φ_aφ_c⟩⟨φ_bφ_d⟩ − ⟨φ_aφ_d⟩⟨φ_bφ_c⟩ ≤ 0. -/
theorem lebowitz_dexpect {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (a b c d : DSite n k) :
    dexpect n k m₀ lam (fun φ => φ a * φ b * φ c * φ d)
      - dexpect n k m₀ lam (fun φ => φ a * φ b) * dexpect n k m₀ lam (fun φ => φ c * φ d)
      - dexpect n k m₀ lam (fun φ => φ a * φ c) * dexpect n k m₀ lam (fun φ => φ b * φ d)
      - dexpect n k m₀ lam (fun φ => φ a * φ d) * dexpect n k m₀ lam (fun φ => φ b * φ c)
      ≤ 0 := by
  have hint : ∀ L : List (DSite n k), Integrable fun φ : DField n k =>
      (L.map φ).prod * ferroDensity (siteWeight n k m₀ lam (Polynomial.X ^ 4)) (Jnn n k) φ := by
    intro L
    rw [ferroDensity_dweight]
    simp_rw [list_prod_eq_mono]
    exact integrable_mono_dweight hm hlam _
  have h := lebowitz_ferro (siteWeight_even fun y => wickPoly_X4_neg _ y)
    (fun _ _ => (Real.exp_pos _).le) (lebowitzSite_siteWeight m₀ hlam) Jnn_nonneg hint a b c d
  rw [ferroDensity_dweight] at h
  exact h

/-- The same as integrals against the Gibbs probability measure. -/
theorem lebowitz_gibbs {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (a b c d : DSite n k) :
    ∫ φ, φ a * φ b * φ c * φ d ∂(gibbs n k m₀ lam)
      - (∫ φ, φ a * φ b ∂(gibbs n k m₀ lam)) * ∫ φ, φ c * φ d ∂(gibbs n k m₀ lam)
      - (∫ φ, φ a * φ c ∂(gibbs n k m₀ lam)) * ∫ φ, φ b * φ d ∂(gibbs n k m₀ lam)
      - (∫ φ, φ a * φ d ∂(gibbs n k m₀ lam)) * ∫ φ, φ b * φ c ∂(gibbs n k m₀ lam) ≤ 0 := by
  simp only [integral_gibbs]
  exact lebowitz_dexpect hm hlam a b c d

end Model

/-! ## Non-Gaussianity of limit points: the cheapest criterion -/

section NonGaussian

open Filter Topology

/-- **A Gaussian generating functional satisfies ‖Z(2f)‖ = ‖Z(f)‖⁴** (both are exp(−2B(f,f))).
Hence one test function with ‖Z(2f)‖ ≠ ‖Z(f)‖⁴ certifies `IsNonGaussian Z`. -/
theorem isNonGaussian_of_norm_ne {Z : TestFn → ℂ} (f : TestFn)
    (h : ‖Z ((2 : ℝ) • f)‖ ≠ ‖Z f‖ ^ 4) : IsNonGaussian Z := by
  rintro ⟨ℓ, B, hZ⟩
  apply h
  rw [hZ, hZ, Complex.norm_exp, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_re,
    Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  ring

/-- **The quartic deficit at finite cutoff**: one test function f and δ > 0 with
‖Z_D(2f)‖ + δ ≤ ‖Z_D(f)‖⁴ for all sufficiently large n and k. This is the lattice statement M9
has to prove; for a symmetric field X = φ(tf), E cos 2tX − (E cos tX)⁴ = (t⁴/2)(E X⁴ − 3(E X²)²)
+ O(t⁶ E X⁶), so it follows (with f replaced by tf, t small) from a uniform bound
u₄(f,f,f,f) ≤ −δ' on the smeared Ursell function together with uniform bounds on the second and
sixth smeared moments (that Taylor step is not formalized here). -/
def QuarticDeficit (m₀ lam : ℝ) : Prop :=
  ∃ f : TestFn, ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ K₀ : ℕ, ∀ n k : ℕ, N₀ ≤ n → K₀ ≤ k →
    ‖ZD n k m₀ lam (Polynomial.X ^ 4) ((2 : ℝ) • f)‖ + δ
      ≤ ‖ZD n k m₀ lam (Polynomial.X ^ 4) f‖ ^ 4

/-- **Every limit point is non-Gaussian, given the finite-cutoff quartic deficit.** This is the
M9 clause `∀ Z, IsLimitPoint m₀ λ Z → IsNonGaussian Z` of `PhiFourTwoGapV3`, reduced to
`QuarticDeficit`. -/
theorem isNonGaussian_of_quarticDeficit {m₀ lam : ℝ} (hD : QuarticDeficit m₀ lam)
    {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) : IsNonGaussian Z := by
  obtain ⟨f, δ, hδ, N₀, K₀, hgap⟩ := hD
  obtain ⟨ns, ks, hns, hks, hconv⟩ := hZ
  refine isNonGaussian_of_norm_ne f (ne_of_lt ?_)
  have hev : ∀ᶠ j in atTop,
      ‖ZD (ns j) (ks j) m₀ lam (Polynomial.X ^ 4) ((2 : ℝ) • f)‖ + δ
        ≤ ‖ZD (ns j) (ks j) m₀ lam (Polynomial.X ^ 4) f‖ ^ 4 := by
    filter_upwards [hns.eventually_ge_atTop N₀, hks.eventually_ge_atTop K₀] with j h1 h2
    exact hgap _ _ h1 h2
  have hle : ‖Z ((2 : ℝ) • f)‖ + δ ≤ ‖Z f‖ ^ 4 :=
    le_of_tendsto_of_tendsto (((hconv _).norm).add_const δ) (((hconv f).norm).pow 4) hev
  linarith

end NonGaussian

end PP2Lebowitz

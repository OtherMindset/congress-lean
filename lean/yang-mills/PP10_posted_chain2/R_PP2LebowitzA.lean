import LongTable.P_mwwgf25i_d0aeg1

/-!
Part A of PP2Lebowitz (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Lebowitz.lean)
Long Table, P(φ)₂ direction, node M9 (non-Gaussian limits), session 1: the Lebowitz inequality
u₄ ≤ 0 for the quartic Dirichlet-box measure, by a four-copy (Hadamard) sign argument, and the
reduction of `IsNonGaussian` for limit points to a finite-cutoff inequality.

FORMALIZED.
* `measurePreserving_linear_involution`: a linear involution of a finite-dimensional real space
  preserves every additive Haar measure (det² = 1).
* Four copies indexed by `K4 ι = (ι ⊕ ι) ⊕ (ι ⊕ ι)`; the Hadamard map `had`
  (y₁..y₄) ↦ ½(y₁+y₂+y₃+y₄, y₁+y₂−y₃−y₄, y₁−y₂+y₃−y₄, y₁−y₂−y₃+y₄), site by site; `had_had`,
  `measurePreserving_had`.
* **Single-site hypothesis** `LebowitzSite w`: in Hadamard coordinates (A,B,C,D),
  w(y₁)w(y₂)w(y₃)w(y₄) · exp(c·ABCD) is even in each of A, B, C, D separately, for some c ≥ 0
  (i.e. the four-copy weight is "even part × exp(−c ABCD)", c ≥ 0).
  `lebowitzSite_quartic`: exp(−(a y⁴ + b y² + d)) satisfies it for every a ≥ 0 and ANY b, d
  (c = 6a; Σ yᵢ⁴ = ¼(Σ A⁴ + 6 Σ_{pairs} A²B²) + 6ABCD).
  `lebowitzSite_siteWeight`: hence the box weight `siteWeight n k m₀ λ X⁴ x` for λ ≥ 0.
  Not every even weight works: for the spin-1 law P(±1) = p/2, P(0) = 1 − p one site already
  gives u₄ = p − 3p² > 0 when p < 1/3; that weight has no such factorization.
* `lev2_had_flip` (the pointwise identity) and `integral_lev2_nonpos`: after the Hadamard change
  of variables and D ↦ −D, the doubly-duplicated integrand is
  −4 (A_iB_j + B_iA_j)(C_kD_l + D_kC_l) e^{Σ J(AA+BB+CC+DD) + Σ c ABCD} ∏ (flip-invariant ≥ 0),
  so its integral is ≤ 0 by Griffiths-I sign averaging (`griffiths_first_inv`).
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

/-- A linear involution of a finite-dimensional real space preserves every additive Haar
measure (its determinant squares to 1). -/
theorem measurePreserving_linear_involution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (f : E →ₗ[ℝ] E) (hf : ∀ x, f (f x) = x) :
    MeasurePreserving f μ μ := by
  have hcomp : f.comp f = LinearMap.id := LinearMap.ext hf
  have hdet : LinearMap.det f * LinearMap.det f = 1 := by
    rw [← LinearMap.det_comp, hcomp, LinearMap.det_id]
  have hne : LinearMap.det f ≠ 0 := by
    intro h; rw [h, zero_mul] at hdet; exact zero_ne_one hdet
  have habs : |(LinearMap.det f)⁻¹| = 1 := by
    rw [abs_inv]
    have : |LinearMap.det f| * |LinearMap.det f| = 1 := by rw [← abs_mul, hdet, abs_one]
    have h0 : 0 ≤ |LinearMap.det f| := abs_nonneg _
    have h1 : |LinearMap.det f| = 1 := by nlinarith
    rw [h1, inv_one]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar μ hne, habs, ENNReal.ofReal_one,
    one_smul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## The four-copy space and its Hadamard map -/

/-- Index set of four copies of the system: (copy 1, copy 2) ⊕ (copy 3, copy 4). -/
abbrev K4 (ι : Type*) := (ι ⊕ ι) ⊕ (ι ⊕ ι)

/-- The Hadamard map, site by site: (y₁, y₂, y₃, y₄) ↦ ½ (y₁+y₂+y₃+y₄, y₁+y₂−y₃−y₄,
y₁−y₂+y₃−y₄, y₁−y₂−y₃+y₄). It is symmetric and orthogonal, hence an involution. -/
def had (ψ : K4 ι → ℝ) : K4 ι → ℝ
  | .inl (.inl x) =>
    (ψ (.inl (.inl x)) + ψ (.inl (.inr x)) + ψ (.inr (.inl x)) + ψ (.inr (.inr x))) / 2
  | .inl (.inr x) =>
    (ψ (.inl (.inl x)) + ψ (.inl (.inr x)) - ψ (.inr (.inl x)) - ψ (.inr (.inr x))) / 2
  | .inr (.inl x) =>
    (ψ (.inl (.inl x)) - ψ (.inl (.inr x)) + ψ (.inr (.inl x)) - ψ (.inr (.inr x))) / 2
  | .inr (.inr x) =>
    (ψ (.inl (.inl x)) - ψ (.inl (.inr x)) - ψ (.inr (.inl x)) + ψ (.inr (.inr x))) / 2

lemma had_had (ψ : K4 ι → ℝ) : had (had ψ) = ψ := by
  funext i; rcases i with ((x | x) | (x | x)) <;> simp only [had] <;> ring

/-- `had` as a linear map. -/
def hadL : (K4 ι → ℝ) →ₗ[ℝ] (K4 ι → ℝ) where
  toFun := had
  map_add' ψ χ := by
    funext i; rcases i with ((x | x) | (x | x)) <;> simp only [had, Pi.add_apply] <;> ring
  map_smul' c ψ := by
    funext i; rcases i with ((x | x) | (x | x)) <;>
      simp only [had, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

lemma measurePreserving_had :
    MeasurePreserving (had : (K4 ι → ℝ) → (K4 ι → ℝ)) volume volume :=
  measurePreserving_linear_involution (volume : Measure (K4 ι → ℝ)) (hadL (ι := ι)) had_had

/-- `had` as a measurable equivalence. -/
def hadEquiv : (K4 ι → ℝ) ≃ᵐ (K4 ι → ℝ) :=
  MeasurableEquiv.ofInvolutive had had_had (measurePreserving_had).measurable

/-! ## The single-site condition -/

/-- The four-copy single-site weight in Hadamard coordinates. -/
def quadW (w : ℝ → ℝ) (A B C D : ℝ) : ℝ :=
  w ((A + B + C + D) / 2) * w ((A + B - C - D) / 2) * w ((A - B + C - D) / 2)
    * w ((A - B - C + D) / 2)

/-- G is even in each of its four arguments separately. -/
def EvenEach (G : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ A B C D, G (-A) B C D = G A B C D) ∧ (∀ A B C D, G A (-B) C D = G A B C D) ∧
    (∀ A B C D, G A B (-C) D = G A B C D) ∧ (∀ A B C D, G A B C (-D) = G A B C D)

lemma EvenEach.sgn {G : ℝ → ℝ → ℝ → ℝ → ℝ} (hG : EvenEach G) (a b c d : Bool)
    (A B C D : ℝ) : G (sgnMul a A) (sgnMul b B) (sgnMul c C) (sgnMul d D) = G A B C D := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  cases a <;> cases b <;> cases c <;> cases d <;> simp [sgnMul, h1, h2, h3, h4]

/-- **The single-site hypothesis of the Lebowitz inequality.** In Hadamard coordinates the
four-copy weight w(y₁)w(y₂)w(y₃)w(y₄) is (even in each of A, B, C, D) × exp(−c·ABCD) with
c ≥ 0. -/
def LebowitzSite (w : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ EvenEach (fun A B C D => quadW w A B C D * Real.exp (c * (A * B * C * D)))

/-- **The φ⁴ single-site weight exp(−(a y⁴ + b y² + d)), a ≥ 0, b and d arbitrary, satisfies
the Lebowitz condition** (with c = 6a: Σ yᵢ⁴ = ¼(ΣA⁴ + 6 Σ_{pairs} A²B²) + 6ABCD). -/
theorem lebowitzSite_quartic {a : ℝ} (ha : 0 ≤ a) (b d : ℝ) :
    LebowitzSite (fun y => Real.exp (-(a * y ^ 4 + b * y ^ 2 + d))) := by
  refine ⟨6 * a, by linarith, ?_, ?_, ?_, ?_⟩ <;> intro A B C D <;>
    simp only [quadW, ← Real.exp_add] <;> congr 1 <;> ring


/-! ## The four-copy sign argument -/

/-- The two-copy density ρ(t)ρ(s) on ι ⊕ ι → ℝ (t = inl, s = inr). -/
def rho2 (ρ : (ι → ℝ) → ℝ) (ξ : ι ⊕ ι → ℝ) : ℝ :=
  ρ (fun x => ξ (.inl x)) * ρ (fun x => ξ (.inr x))

/-- (t_i + s_i)(t_j + s_j). -/
def Pobs (i j : ι) (ξ : ι ⊕ ι → ℝ) : ℝ := (ξ (.inl i) + ξ (.inr i)) * (ξ (.inl j) + ξ (.inr j))

/-- (t_k − s_k)(t_l − s_l). -/
def Qobs (k l : ι) (ξ : ι ⊕ ι → ℝ) : ℝ := (ξ (.inl k) - ξ (.inr k)) * (ξ (.inl l) - ξ (.inr l))

/-- The integrand of the second duplication, on the four-copy space. -/
def lev2 (ρ : (ι → ℝ) → ℝ) (i j k l : ι) (ψ : K4 ι → ℝ) : ℝ :=
  (Pobs i j (fun a => ψ (.inl a)) - Pobs i j (fun a => ψ (.inr a))) *
    (Qobs k l (fun a => ψ (.inl a)) - Qobs k l (fun a => ψ (.inr a))) *
    rho2 ρ (fun a => ψ (.inl a)) * rho2 ρ (fun a => ψ (.inr a))

/-- Flip of the fourth Hadamard coordinate D at every site. -/
def sigD : K4 ι → Bool
  | .inr (.inr _) => true
  | _ => false

section Coords
variable (φ : K4 ι → ℝ) (x : ι)

lemma had_flip_1 : had (flipSigns sigD φ) (.inl (.inl x)) =
    (φ (.inl (.inl x)) + φ (.inl (.inr x)) + φ (.inr (.inl x)) + -φ (.inr (.inr x))) / 2 := by
  simp [had, flipSigns, sgnMul, sigD]
lemma had_flip_2 : had (flipSigns sigD φ) (.inl (.inr x)) =
    (φ (.inl (.inl x)) + φ (.inl (.inr x)) - φ (.inr (.inl x)) - -φ (.inr (.inr x))) / 2 := by
  simp [had, flipSigns, sgnMul, sigD]
lemma had_flip_3 : had (flipSigns sigD φ) (.inr (.inl x)) =
    (φ (.inl (.inl x)) - φ (.inl (.inr x)) + φ (.inr (.inl x)) - -φ (.inr (.inr x))) / 2 := by
  simp [had, flipSigns, sgnMul, sigD]
lemma had_flip_4 : had (flipSigns sigD φ) (.inr (.inr x)) =
    (φ (.inl (.inl x)) - φ (.inl (.inr x)) - φ (.inr (.inl x)) + -φ (.inr (.inr x))) / 2 := by
  simp [had, flipSigns, sgnMul, sigD]

end Coords

/-- The Hadamard-coordinate observable (A_i B_j + B_i A_j)(C_k D_l + D_k C_l). -/
def obsH (i j k l : ι) (φ : K4 ι → ℝ) : ℝ :=
  (φ (.inl (.inl i)) * φ (.inl (.inr j)) + φ (.inl (.inr i)) * φ (.inl (.inl j))) *
    (φ (.inr (.inl k)) * φ (.inr (.inr l)) + φ (.inr (.inr k)) * φ (.inr (.inl l)))

/-- The Hadamard-coordinate exponent Σ J (AA + BB + CC + DD) + Σ c ABCD. -/
def expoH (J : ι → ι → ℝ) (c : ι → ℝ) (φ : K4 ι → ℝ) : ℝ :=
  ∑ x, ∑ y, J x y * (φ (.inl (.inl x)) * φ (.inl (.inl y)) + φ (.inl (.inr x)) * φ (.inl (.inr y))
      + φ (.inr (.inl x)) * φ (.inr (.inl y)) + φ (.inr (.inr x)) * φ (.inr (.inr y)))
    + ∑ x, c x * (φ (.inl (.inl x)) * φ (.inl (.inr x)) * φ (.inr (.inl x)) * φ (.inr (.inr x)))

/-- The flip-invariant part of the weight. -/
def wtH (G : ι → ℝ → ℝ → ℝ → ℝ → ℝ) (φ : K4 ι → ℝ) : ℝ :=
  ∏ x, G x (φ (.inl (.inl x))) (φ (.inl (.inr x))) (φ (.inr (.inl x))) (φ (.inr (.inr x)))

lemma isPosPoly_obsH (i j k l : ι) : IsPosPoly (obsH (ι := ι) i j k l) :=
  ((((IsPosPoly.coord _).mul (IsPosPoly.coord _)).add ((IsPosPoly.coord _).mul
    (IsPosPoly.coord _))).mul (((IsPosPoly.coord _).mul (IsPosPoly.coord _)).add
    ((IsPosPoly.coord _).mul (IsPosPoly.coord _)))).congr' fun _ => rfl

lemma isPosPoly_expoH {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) {c : ι → ℝ} (hc : ∀ x, 0 ≤ c x) :
    IsPosPoly (expoH J c) :=
  ((IsPosPoly.sum univ fun x _ => IsPosPoly.sum univ fun y _ => (IsPosPoly.const (hJ x y)).mul
      (((((IsPosPoly.coord _).mul (IsPosPoly.coord _)).add ((IsPosPoly.coord _).mul
        (IsPosPoly.coord _))).add ((IsPosPoly.coord _).mul (IsPosPoly.coord _))).add
        ((IsPosPoly.coord _).mul (IsPosPoly.coord _)))).add
    (IsPosPoly.sum univ fun x _ => (IsPosPoly.const (hc x)).mul
      ((((IsPosPoly.coord _).mul (IsPosPoly.coord _)).mul (IsPosPoly.coord _)).mul
        (IsPosPoly.coord _)))).congr' fun _ => rfl

/-- **The pointwise identity behind the Lebowitz inequality.** After the Hadamard change of
variables and the flip D ↦ −D, the second-duplication integrand is −4 · (A_iB_j + B_iA_j)
(C_kD_l + D_kC_l) · exp(Σ J(AA+BB+CC+DD) + Σ c ABCD) · ∏ G(A,B,C,D). -/
theorem lev2_had_flip {w : ι → ℝ → ℝ} {J : ι → ι → ℝ} {c : ι → ℝ}
    (hG : ∀ x, EvenEach (fun A B C D => quadW (w x) A B C D * Real.exp (c x * (A * B * C * D))))
    (i j k l : ι) (φ : K4 ι → ℝ) :
    lev2 (ferroDensity w J) i j k l (had (flipSigns sigD φ)) =
      -(4 * (obsH i j k l φ * Real.exp (expoH J c φ)
        * wtH (fun x A B C D => quadW (w x) A B C D * Real.exp (c x * (A * B * C * D))) φ)) := by
  set A : ι → ℝ := fun x => φ (.inl (.inl x))
  set B : ι → ℝ := fun x => φ (.inl (.inr x))
  set C : ι → ℝ := fun x => φ (.inr (.inl x))
  set D : ι → ℝ := fun x => φ (.inr (.inr x))
  have hS : (∑ x, ∑ y, J x y * ((A x + B x + C x + -D x) / 2) * ((A y + B y + C y + -D y) / 2))
      + (∑ x, ∑ y, J x y * ((A x + B x - C x - -D x) / 2) * ((A y + B y - C y - -D y) / 2))
      + ((∑ x, ∑ y, J x y * ((A x - B x + C x - -D x) / 2) * ((A y - B y + C y - -D y) / 2))
      + (∑ x, ∑ y, J x y * ((A x - B x - C x + -D x) / 2) * ((A y - B y - C y + -D y) / 2)))
      = ∑ x, ∑ y, J x y * (A x * A y + B x * B y + C x * C y + D x * D y) := by
    simp only [← Finset.sum_add_distrib]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  have hW : (∏ x, w x ((A x + B x + C x + -D x) / 2)) * (∏ x, w x ((A x + B x - C x - -D x) / 2))
      * ((∏ x, w x ((A x - B x + C x - -D x) / 2)) * (∏ x, w x ((A x - B x - C x + -D x) / 2)))
      = (∏ x, (quadW (w x) (A x) (B x) (C x) (D x) * Real.exp (c x * (A x * B x * C x * D x))))
        * Real.exp (∑ x, c x * (A x * B x * C x * D x)) := by
    rw [Real.exp_sum, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib,
      ← prod_mul_distrib]
    refine prod_congr rfl fun x _ => ?_
    have h4 := (hG x).2.2.2 (A x) (B x) (C x) (D x)
    simp only at h4
    rw [← h4, mul_assoc (quadW (w x) (A x) (B x) (C x) (-D x)), ← Real.exp_add,
      show c x * (A x * B x * C x * -D x) + c x * (A x * B x * C x * D x) = 0 by ring,
      Real.exp_zero, mul_one, quadW]
    ring
  simp only [lev2, rho2, ferroDensity, Pobs, Qobs, had_flip_1, had_flip_2, had_flip_3, had_flip_4]
  have e : ∀ (O s1 s2 s3 s4 p1 p2 p3 p4 : ℝ),
      O * (Real.exp s1 * p1 * (Real.exp s2 * p2)) * (Real.exp s3 * p3 * (Real.exp s4 * p4))
        = O * (Real.exp (s1 + s2 + (s3 + s4)) * (p1 * p2 * (p3 * p4))) := by
    intros; simp only [Real.exp_add]; ring
  rw [e, hS, hW, obsH, expoH, wtH, Real.exp_add]
  ring

lemma wtH_flip {G : ι → ℝ → ℝ → ℝ → ℝ → ℝ} (hG : ∀ x, EvenEach (G x)) (σ : K4 ι → Bool)
    (φ : K4 ι → ℝ) : wtH G (flipSigns σ φ) = wtH G φ :=
  prod_congr rfl fun x _ => (hG x).sgn _ _ _ _ _ _ _ _

/-- **The sign of the second-duplication integral**: for even w_x ≥ 0 satisfying the Lebowitz
single-site condition and J ≥ 0, ∫ lev2 ≤ 0 (no integrability hypothesis: Bochner convention). -/
theorem integral_lev2_nonpos {w : ι → ℝ → ℝ} (hw_nonneg : ∀ x y, 0 ≤ w x y)
    (hw : ∀ x, LebowitzSite (w x)) {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (i j k l : ι) :
    ∫ ψ, lev2 (ferroDensity w J) i j k l ψ ≤ 0 := by
  choose c hc hG using hw
  have h1 : ∫ ψ, lev2 (ferroDensity w J) i j k l ψ
      = ∫ φ, lev2 (ferroDensity w J) i j k l (had φ) :=
    (measurePreserving_had.integral_comp' (f := hadEquiv) _).symm
  have h2 : ∫ φ, lev2 (ferroDensity w J) i j k l (had φ)
      = ∫ φ, lev2 (ferroDensity w J) i j k l (had (flipSigns sigD φ)) :=
    ((measurePreserving_flipEquiv sigD).integral_comp' (f := flipEquiv sigD)
      (fun φ => lev2 (ferroDensity w J) i j k l (had φ))).symm
  rw [h1, h2]
  simp_rw [lev2_had_flip hG]
  rw [integral_neg, integral_const_mul]
  have hnn : ∀ φ : K4 ι → ℝ,
      0 ≤ wtH (fun x A B C D => quadW (w x) A B C D * Real.exp (c x * (A * B * C * D))) φ :=
    fun φ => prod_nonneg fun x _ => mul_nonneg (by
      unfold quadW
      exact mul_nonneg (mul_nonneg (mul_nonneg (hw_nonneg _ _) (hw_nonneg _ _)) (hw_nonneg _ _))
        (hw_nonneg _ _)) (Real.exp_pos _).le
  have := griffiths_first_inv (wtH_flip hG) hnn (isPosPoly_obsH i j k l) (isPosPoly_expoH hJ hc)
  linarith

/-! ## Moments, odd moments, and the first duplication -/

/-- The unnormalised moment ∫ (∏_{a ∈ L} φ a) ρ. -/
def mom (ρ : (ι → ℝ) → ℝ) (L : List ι) : ℝ := ∫ φ, (L.map φ).prod * ρ φ

lemma prod_map_neg (L : List ι) (φ : ι → ℝ) :
    (L.map fun x => -φ x).prod = (-1) ^ L.length * (L.map φ).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]; ring

/-- Odd moments of an even density vanish. -/
theorem mom_odd {ρ : (ι → ℝ) → ℝ} (hρ : ∀ φ, ρ (fun x => -φ x) = ρ φ) {L : List ι}
    (hL : Odd L.length) : mom ρ L = 0 := by
  have hf : ∀ φ : ι → ℝ, flipSigns (fun _ => true) φ = fun x => -φ x := fun φ => by
    funext x; simp [flipSigns, sgnMul]
  have h := (measurePreserving_flipEquiv (fun _ : ι => true)).integral_comp'
    (f := flipEquiv (fun _ : ι => true)) (fun φ => (L.map φ).prod * ρ φ)
  have h' : ∫ φ : ι → ℝ, (L.map (flipSigns (fun _ => true) φ)).prod
      * ρ (flipSigns (fun _ => true) φ) = -mom ρ L := by
    simp_rw [hf, prod_map_neg, hρ, hL.neg_one_pow]
    rw [mom, ← integral_neg]; congr 1; funext φ; ring
  have : mom ρ L = -mom ρ L := by rw [← h', mom]; exact h.symm
  linarith

end PP2Lebowitz

end

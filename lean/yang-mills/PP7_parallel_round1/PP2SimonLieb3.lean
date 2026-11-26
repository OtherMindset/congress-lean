import LongTable.PP2SimonLieb2
import LongTable.PP2Griffiths3

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M3, session 3.
Steps (R3) and (R4) of the route in `PP2SimonLieb`: Griffiths-II monotonicity of the local-time
family in τ, and strong Gaussian domination (Brydges–Fröhlich–Spencer, CMP 83 (1982), Theorem 5.1)
by a Volterra positivity argument, abstractly (namespace `PP2SGD`, any finite ι, any ferromagnetic
pair matrix K ≥ 0, site exponent f(u) = au + bu²) and for the quartic Dirichlet box
(namespace `PP2Target`).

Source: BFS CMP 83, uploaded copy read through the site in sessions 1–2 (§2 (2.21)–(2.22),
Theorem 2.2; §5 (5.4)–(5.6), Theorem 5.1). Not re-read this session.

A FINDING (corrects the FINDING of `PP2SimonLieb2`). The weighted-sup contraction of (R4) does
NOT fail on fine lattices, and no walk bound is needed. Use the weight e^{c'Σ_x τ_x} with
c' > r := max_i Σ_k J_ik (any c'), not e^{Σ f(τ_x)}: the kernel bound is exact,
  sup_τ e^{c'Στ} |(K g)_i(τ)| ≤ (Σ_k J_ik / c') ‖g‖   (∫_0^∞ e^{−c's} ds = 1/c'),
and the only thing needed of D is FINITENESS of ‖D‖ = sup_τ |D(τ)| e^{c'Στ}. This holds since
|D(τ)| ≤ M e^{−Σ f(τ_x)} (`tw_le_tw_zero`) and f(t) ≥ c't − C₀: for β > 0 with
C₀ = (c' − α)²/(4β) for ANY c' (`fq_ge_lin`), whatever the sign of α (so Wick ordering, α < 4,
is harmless); for β = 0 (λ = 0) with c' = α = 4 + ε²m₀² > 4 ≥ r (`Jsym_row_le`). C₀ depends on ε
and the box, which is irrelevant: (R4) is a pointwise inequality in a fixed finite box.

DEFINITIONS (namespace `PP2SGD`).
* `rhoQ w Q = e^Q ∏_x w_x`, `massV γ φ = Σ_x γ_x φ_x²`.
* `tI K a b τ F = ∫ F e^{Q_K} W_τ` ([F]_τ; `tauInt n k m₀ λ = tI (Jnn n k) (alphaQ ..) (betaQ ..)`
  by rfl, `tauInt_eq_tI`), `siteW a b τ x y = e^{−f(y²/2 + τ_x)}`.
* `Adm Ψ H`: H continuous and |H| ≤ C e^{a'Σ|φ_x|} Ψ (envelope Ψ ≥ 1; Ψ = 1 for polynomials;
  intended Ψ = 1 + e^{bdryCoupling} for the decoupled measure of R5).
* `sgdD … i τ = Σ_j c_j [φ_iφ_j]_τ − [φ_i G]_τ`, `sgdE` its local-time integrand from R2.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* (R3, abstract) `signSum_cone_pos`, `signSum_cone_sinh` (sign-averaged positivity of
  (A(t) − A(s)) sinh(X(u,v)) e^{Q(t)+Q(s)}, A ∈ 𝒞, by the odd series of sinh), `mass_dup_nonneg`,
  `mass_dup_prod_nonneg`, `integral_four_expand`, `sinh_mul_exp`, and
  **`mass_mono_cone`**: for even w_x ≥ 0, Q ≥ 0 coefficients, H ∈ 𝒞, γ ≥ 0, ρ = e^Q∏w,
  ρ' = e^{−Σγ_xφ_x²}ρ (four integrability hypotheses):  (∫Hρ')(∫ρ) ≤ (∫Hρ)(∫ρ').
  Finite-difference form, no derivative in τ: duplicate variables, e^{−V(s)} − e^{−V(t)} =
  2 sinh(Σ_x γ_x u_x v_x/2) e^{−(V(t)+V(s))/2}, Gaussian factor absorbed into the even weights.
* (R3, local times) `tw_shift_mass`, `rhoQ_siteW`, **`tI_mono`** (K ≥ 0, b ≥ 0, τ ≤ τ', H ∈ 𝒞):
  [H]_{τ'}[1]_τ ≤ [H]_τ[1]_{τ'}; box form **`tauInt_mono`** (m₀ ≠ 0, λ ≥ 0, 0 ≤ τ ≤ τ',
  H ∈ 𝒞 ∩ Adm 1).
* (R4 core) **`volterra_nonneg`**: J ≥ 0, row sums ≤ r < c', D_i(τ) = ∫_0^∞ E_i(τ,s) ds,
  E_i(τ,s) ≥ Σ_k J_ik D_k(τ + s e_i), −D_i(τ) ≤ M e^{−c'Στ}  ⟹  D ≥ 0 on [0,∞)^ι
  (`volterra_step`: one contraction step; no integrability of E assumed).
* (R2, abstract with envelope) `tI_ibp`, `integrable_adm`, `abs_tI_le`, `integrableOn_tI_shift`
  (s ↦ [H]_{τ+se_i} integrable on (0,∞): measurability by `StronglyMeasurable.integral_prod_right'`,
  decay by `tw_shift_le`; this closes the "NOT formalized" item of `PP2SimonLieb2` on separate
  integrability in s), `tI_one_pos`, `tI_const`, `hasLineDerivAt_coord`, `fq_ge_lin`,
  `exp_neg_sum_fq_le`.
* (R4) `sgdE_eq` (E = (c_i[1]_σ − [∂_iG]_σ) + Σ_k J_ik D_k(σ)) and
  **`strong_gaussian_domination`** (abstract BFS Theorem 5.1): K ≥ 0, b ≥ 0, (b > 0 ∨ a > 0),
  Adm Ψ integrable at τ = 0, row sums of K + Kᵀ ≤ r < c', f(t) ≥ c't − C₀; G ∈ Adm Ψ with
  ∂_jG = G' j ∈ Adm Ψ ∩ 𝒞:   [φ_iG]_0 ≤ Σ_j ([G' j]_0/[1]_0) [φ_iφ_j]_0.
* (box) `hint_box`, `sgd_box_of`, `sum_ite_unique`, `Jsym_row_le` (Σ_y J_xy ≤ 4), and
  **`strong_gaussian_domination_box`** (m₀ ≠ 0, λ ≥ 0):
    ⟨φ_i G⟩ ≤ Σ_j ⟨∂_j G⟩ ⟨φ_iφ_j⟩ = Σ_j ⟨∂_j G⟩ · twoPt i j.

NOT formalized.
* (R5). Needs (a) the decoupled weight in the form decWeight_B ∝ e^{Q_{K_B}} W_0 with
  K_B = Jnn on B×B ∪ Bᶜ×Bᶜ, 0 across ∂B (K_B ≥ 0; from `dirAction_split`), (b) `hint` for K_B with
  envelope Ψ = 1 + e^{bdryCoupling} (decWeight·e^{bdry} = qweight·const, so this is `integrable_tau`
  for the full weight plus a Gaussian bound for the decoupled one), (c) G = φ_y·e^{bdryCoupling},
  ∂_u G = δ_uy e^{bdry} + φ_y Σ_v J_uv φ_v e^{bdry} ∈ 𝒞 (`InCone` with Q = bdryCoupling restricted
  to its nonnegative-coefficient form), and the bookkeeping ⟨φ_xφ_u⟩_dec = regionTwoPt B x u
  (`decoupled_twoPt`), = 0 for u ∉ B (oddness), division by ⟨e^{bdry}⟩_dec, `twoPt_eq_decoupled`.
  The abstract `strong_gaussian_domination` is stated with the envelope Ψ for exactly this use.
* G of super-exponential-linear growth beyond an envelope; derivatives in τ (not needed).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2SGD

open PP2LocalTime PP2Griffiths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part 1 (R3): raising a site mass lowers cone expectations -/

/-- Sign-averaged positivity of (A(t) − A(s)) · P(u, v) · e^{Q(t)+Q(s)} for A in the cone and
P, Q with nonnegative coefficients. -/
lemma signSum_cone_pos {A Q : (ι → ℝ) → ℝ} {P : (ι ⊕ ι → ℝ) → ℝ} (hA : InCone A)
    (hP : IsPosPoly P) (hQ : IsPosPoly Q) (ψ : ι ⊕ ι → ℝ) :
    0 ≤ ∑ σ : ι ⊕ ι → Bool, (A (tPart (flipSigns σ ψ)) - A (sPart (flipSigns σ ψ))) *
      P (flipSigns σ ψ) * Real.exp (Q (tPart (flipSigns σ ψ)) + Q (sPart (flipSigns σ ψ))) := by
  obtain ⟨gA, QA, hgA, hQA, hAe⟩ := hA
  have hapos : ∀ m : ℕ, IsPosPoly (fun φ => gA φ * QA φ ^ m * ((m.factorial : ℝ))⁻¹) :=
    fun m => (hgA.mul (hQA.pow m)).mul (IsPosPoly.const (by positivity))
  have hs : HasSum (fun m : ℕ => ∑ σ : ι ⊕ ι → Bool,
      ((gA (tPart (flipSigns σ ψ)) * QA (tPart (flipSigns σ ψ)) ^ m * ((m.factorial : ℝ))⁻¹) -
        (gA (sPart (flipSigns σ ψ)) * QA (sPart (flipSigns σ ψ)) ^ m * ((m.factorial : ℝ))⁻¹)) *
      P (flipSigns σ ψ) * Real.exp (Q (tPart (flipSigns σ ψ)) + Q (sPart (flipSigns σ ψ))))
      (∑ σ : ι ⊕ ι → Bool, (A (tPart (flipSigns σ ψ)) - A (sPart (flipSigns σ ψ))) *
        P (flipSigns σ ψ) * Real.exp (Q (tPart (flipSigns σ ψ)) + Q (sPart (flipSigns σ ψ)))) := by
    refine hasSum_sum fun σ _ => ?_
    have h1 := (((hasSum_expTerm gA QA (tPart (flipSigns σ ψ))).sub
      (hasSum_expTerm gA QA (sPart (flipSigns σ ψ)))).mul_right (P (flipSigns σ ψ))).mul_right
        (Real.exp (Q (tPart (flipSigns σ ψ)) + Q (sPart (flipSigns σ ψ))))
    simp only [hAe]
    exact h1
  refine hs.nonneg fun m => ?_
  exact signSum_mul_exp_nonneg ((PairPos.of_isPosPoly (hapos m)).2.mul hP)
    (PairPos.of_isPosPoly hQ).1 ψ

/-- The same with P replaced by sinh X, X with nonnegative coefficients (odd exponential series). -/
lemma signSum_cone_sinh {A Q : (ι → ℝ) → ℝ} {X : (ι ⊕ ι → ℝ) → ℝ} (hA : InCone A)
    (hX : IsPosPoly X) (hQ : IsPosPoly Q) (ψ : ι ⊕ ι → ℝ) :
    0 ≤ ∑ σ : ι ⊕ ι → Bool, (A (tPart (flipSigns σ ψ)) - A (sPart (flipSigns σ ψ))) *
      Real.sinh (X (flipSigns σ ψ)) *
        Real.exp (Q (tPart (flipSigns σ ψ)) + Q (sPart (flipSigns σ ψ))) := by
  have hs : HasSum (fun m : ℕ => ∑ σ : ι ⊕ ι → Bool,
      (A (tPart (flipSigns σ ψ)) - A (sPart (flipSigns σ ψ))) *
        (X (flipSigns σ ψ) ^ (2 * m + 1) * (((2 * m + 1).factorial : ℝ))⁻¹) *
        Real.exp (Q (tPart (flipSigns σ ψ)) + Q (sPart (flipSigns σ ψ))))
      (∑ σ : ι ⊕ ι → Bool, (A (tPart (flipSigns σ ψ)) - A (sPart (flipSigns σ ψ))) *
        Real.sinh (X (flipSigns σ ψ)) *
          Real.exp (Q (tPart (flipSigns σ ψ)) + Q (sPart (flipSigns σ ψ)))) := by
    refine hasSum_sum fun σ _ => ?_
    have h := Real.hasSum_sinh (X (flipSigns σ ψ))
    simp only [div_eq_mul_inv] at h
    exact (h.mul_left _).mul_right _
  refine hs.nonneg fun m => ?_
  exact signSum_cone_pos hA ((hX.pow (2 * m + 1)).mul (IsPosPoly.const (by positivity))) hQ ψ

/-- The product density ρ = e^Q ∏_x w_x. -/
def rhoQ (w : ι → ℝ → ℝ) (Q : (ι → ℝ) → ℝ) (φ : ι → ℝ) : ℝ :=
  Real.exp (Q φ) * ∏ x, w x (φ x)

/-- The site-mass increment V(φ) = Σ_x γ_x φ_x². -/
def massV (γ : ι → ℝ) (φ : ι → ℝ) : ℝ := ∑ x, γ x * φ x ^ 2

/-- The doubled sign-averaging step for the mass comparison. -/
theorem mass_dup_nonneg {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {H Q : (ι → ℝ) → ℝ} (hH : InCone H) (hQ : IsPosPoly Q)
    {γ : ι → ℝ} (hγ : ∀ x, 0 ≤ γ x) :
    0 ≤ ∫ p : ι → ℝ × ℝ, (H (fstF p) - H (sndF p)) *
      Real.sinh (∑ x, γ x / 2 * (uv p (Sum.inl x) * uv p (Sum.inr x))) *
      Real.exp (Q (fstF p) + Q (sndF p)) * dupWeight w p := by
  have hX : IsPosPoly (fun ψ : ι ⊕ ι → ℝ => ∑ x, γ x / 2 * (ψ (Sum.inl x) * ψ (Sum.inr x))) :=
    IsPosPoly.sum (f := fun x ψ => γ x / 2 * (ψ (Sum.inl x) * ψ (Sum.inr x))) _ fun x _ =>
      (IsPosPoly.const (by linarith [hγ x])).mul
        ((IsPosPoly.coord (Sum.inl x)).mul (IsPosPoly.coord (Sum.inr x)))
  refine integral_nonneg_of_actSum_nonneg (dupWeight_act hw_even)
    (fun p => Finset.prod_nonneg fun x _ => mul_nonneg (hw_nonneg _ _) (hw_nonneg _ _)) _
    fun p => ?_
  have hG : ∀ p : ι → ℝ × ℝ, (H (fstF p) - H (sndF p)) *
      Real.sinh (∑ x, γ x / 2 * (uv p (Sum.inl x) * uv p (Sum.inr x))) *
      Real.exp (Q (fstF p) + Q (sndF p)) =
      (H (tPart (uv p)) - H (sPart (uv p))) *
      Real.sinh (∑ x, γ x / 2 * (uv p (Sum.inl x) * uv p (Sum.inr x))) *
      Real.exp (Q (tPart (uv p)) + Q (sPart (uv p))) := by
    intro p; rw [tPart_uv, sPart_uv]
  simp_rw [hG, uv_actPi]
  exact signSum_cone_sinh hH hX hQ (uv p)

/-- Transfer of `mass_dup_nonneg` to (ι → ℝ) × (ι → ℝ). -/
theorem mass_dup_prod_nonneg {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {H Q : (ι → ℝ) → ℝ} (hH : InCone H) (hQ : IsPosPoly Q)
    {γ : ι → ℝ} (hγ : ∀ x, 0 ≤ γ x) :
    0 ≤ ∫ q : (ι → ℝ) × (ι → ℝ), (H q.1 - H q.2) *
      Real.sinh (∑ x, γ x / 2 * ((q.1 x + q.2 x) * (q.1 x - q.2 x))) *
      Real.exp (Q q.1 + Q q.2) * ((∏ x, w x (q.1 x)) * ∏ x, w x (q.2 x)) := by
  have h := mass_dup_nonneg hw_even hw_nonneg hH hQ hγ
  have e := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).integral_comp'
    (fun q : (ι → ℝ) × (ι → ℝ) => (H q.1 - H q.2) *
      Real.sinh (∑ x, γ x / 2 * ((q.1 x + q.2 x) * (q.1 x - q.2 x))) *
      Real.exp (Q q.1 + Q q.2) * ((∏ x, w x (q.1 x)) * ∏ x, w x (q.2 x)))
  refine (h.trans_eq ?_).trans_eq e
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  change _ = (H (fstF p) - H (sndF p)) *
      Real.sinh (∑ x, γ x / 2 * (((p x).1 + (p x).2) * ((p x).1 - (p x).2))) *
      Real.exp (Q (fstF p) + Q (sndF p)) * ((∏ x, w x (p x).1) * ∏ x, w x (p x).2)
  simp only [dupWeight, uv, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]

/-- Fubini expansion of a four-term doubled integrand. -/
theorem integral_four_expand {a b c d : (ι → ℝ) → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hc : Integrable c) (hd : Integrable d) :
    ∫ q : (ι → ℝ) × (ι → ℝ), (a q.1 * b q.2 - c q.1 * d q.2 - (d q.1 * c q.2 - b q.1 * a q.2)) =
      2 * ((∫ φ, a φ) * (∫ φ, b φ) - (∫ φ, c φ) * ∫ φ, d φ) := by
  have i1 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => a q.1 * b q.2 := ha.mul_prod hb
  have i2 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => c q.1 * d q.2 := hc.mul_prod hd
  have i3 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => d q.1 * c q.2 := hd.mul_prod hc
  have i4 : Integrable fun q : (ι → ℝ) × (ι → ℝ) => b q.1 * a q.2 := hb.mul_prod ha
  have p1 : ∫ q : (ι → ℝ) × (ι → ℝ), a q.1 * b q.2 = (∫ φ, a φ) * ∫ φ, b φ :=
    integral_prod_mul (μ := volume) (ν := volume) a b
  have p2 : ∫ q : (ι → ℝ) × (ι → ℝ), c q.1 * d q.2 = (∫ φ, c φ) * ∫ φ, d φ :=
    integral_prod_mul (μ := volume) (ν := volume) c d
  have p3 : ∫ q : (ι → ℝ) × (ι → ℝ), d q.1 * c q.2 = (∫ φ, d φ) * ∫ φ, c φ :=
    integral_prod_mul (μ := volume) (ν := volume) d c
  have p4 : ∫ q : (ι → ℝ) × (ι → ℝ), b q.1 * a q.2 = (∫ φ, b φ) * ∫ φ, a φ :=
    integral_prod_mul (μ := volume) (ν := volume) b a
  have s1 : ∫ q : (ι → ℝ) × (ι → ℝ),
      (a q.1 * b q.2 - c q.1 * d q.2 - (d q.1 * c q.2 - b q.1 * a q.2)) =
      (∫ q : (ι → ℝ) × (ι → ℝ), a q.1 * b q.2 - c q.1 * d q.2) -
        ∫ q : (ι → ℝ) × (ι → ℝ), d q.1 * c q.2 - b q.1 * a q.2 :=
    integral_sub (i1.sub i2) (i3.sub i4)
  have s2 : ∫ q : (ι → ℝ) × (ι → ℝ), a q.1 * b q.2 - c q.1 * d q.2 =
      (∫ q : (ι → ℝ) × (ι → ℝ), a q.1 * b q.2) - ∫ q : (ι → ℝ) × (ι → ℝ), c q.1 * d q.2 :=
    integral_sub i1 i2
  have s3 : ∫ q : (ι → ℝ) × (ι → ℝ), d q.1 * c q.2 - b q.1 * a q.2 =
      (∫ q : (ι → ℝ) × (ι → ℝ), d q.1 * c q.2) - ∫ q : (ι → ℝ) × (ι → ℝ), b q.1 * a q.2 :=
    integral_sub i3 i4
  rw [s1, s2, s3, p1, p2, p3, p4]
  ring

lemma sinh_mul_exp (a b : ℝ) :
    Real.sinh ((a - b) / 2) * (Real.exp (-(a / 2)) * Real.exp (-(b / 2))) =
      (Real.exp (-b) - Real.exp (-a)) / 2 := by
  have e1 : Real.exp ((a - b) / 2) * (Real.exp (-(a / 2)) * Real.exp (-(b / 2))) =
      Real.exp (-b) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (-((a - b) / 2)) * (Real.exp (-(a / 2)) * Real.exp (-(b / 2))) =
      Real.exp (-a) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [Real.sinh_eq]
  linear_combination (e1 - e2) / 2

/-- **R3, abstract form: raising site masses lowers cone expectations.** For site-dependent even
weights w_x ≥ 0, Q with nonnegative coefficients, ρ = e^Q ∏_x w_x, H in the cone
𝒞 = {g e^P : g, P ≥ 0 coefficients}, and γ ≥ 0, with ρ' = e^{−Σ_x γ_x φ_x²} ρ:
  (∫ H ρ') (∫ ρ) ≤ (∫ H ρ) (∫ ρ'),   i.e. ⟨H⟩_{ρ'} ≤ ⟨H⟩_ρ.
Proof: duplicate variables; (e^{−V(s)} − e^{−V(t)}) = 2 sinh(Σ γ_x u_x v_x / 2) e^{−(V(t)+V(s))/2}
with (u, v) = (t + s, t − s), the Gaussian factor is absorbed into the even site weights, and sinh
has nonnegative odd series (`signSum_cone_sinh`). No derivative in the masses is taken. -/
theorem mass_mono_cone {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {H Q : (ι → ℝ) → ℝ} (hH : InCone H) (hQ : IsPosPoly Q)
    {γ : ι → ℝ} (hγ : ∀ x, 0 ≤ γ x)
    (hHρ : Integrable fun φ => H φ * rhoQ w Q φ) (hρ : Integrable (rhoQ w Q))
    (hHρ' : Integrable fun φ => H φ * (Real.exp (-massV γ φ) * rhoQ w Q φ))
    (hρ' : Integrable fun φ => Real.exp (-massV γ φ) * rhoQ w Q φ) :
    (∫ φ, H φ * (Real.exp (-massV γ φ) * rhoQ w Q φ)) * (∫ φ, rhoQ w Q φ) ≤
      (∫ φ, H φ * rhoQ w Q φ) * ∫ φ, Real.exp (-massV γ φ) * rhoQ w Q φ := by
  set w' : ι → ℝ → ℝ := fun x y => w x y * Real.exp (-(γ x / 2 * y ^ 2)) with hw'
  have hw'e : ∀ x y, w' x (-y) = w' x y := fun x y => by simp only [hw', hw_even, neg_sq]
  have hw'n : ∀ x y, 0 ≤ w' x y := fun x y => mul_nonneg (hw_nonneg x y) (Real.exp_pos _).le
  have h0 := mass_dup_prod_nonneg hw'e hw'n hH hQ hγ
  have hprod : ∀ φ : ι → ℝ, ∏ x, w' x (φ x) = (∏ x, w x (φ x)) * Real.exp (-(massV γ φ / 2)) := by
    intro φ
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 1; congr 1
    rw [massV, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hpt : ∀ q : (ι → ℝ) × (ι → ℝ), (H q.1 - H q.2) *
      Real.sinh (∑ x, γ x / 2 * ((q.1 x + q.2 x) * (q.1 x - q.2 x))) *
      Real.exp (Q q.1 + Q q.2) * ((∏ x, w' x (q.1 x)) * ∏ x, w' x (q.2 x)) =
      (1 / 2) * ((H q.1 * rhoQ w Q q.1) * (Real.exp (-massV γ q.2) * rhoQ w Q q.2)
        - (H q.1 * (Real.exp (-massV γ q.1) * rhoQ w Q q.1)) * rhoQ w Q q.2
        - (rhoQ w Q q.1 * (H q.2 * (Real.exp (-massV γ q.2) * rhoQ w Q q.2))
          - (Real.exp (-massV γ q.1) * rhoQ w Q q.1) * (H q.2 * rhoQ w Q q.2))) := by
    intro q
    have hs : ∑ x, γ x / 2 * ((q.1 x + q.2 x) * (q.1 x - q.2 x)) =
        (massV γ q.1 - massV γ q.2) / 2 := by
      rw [massV, massV, ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ => by ring
    have key := sinh_mul_exp (massV γ q.1) (massV γ q.2)
    rw [hprod, hprod, hs, Real.exp_add]
    unfold rhoQ
    linear_combination ((H q.1 - H q.2) * Real.exp (Q q.1) * Real.exp (Q q.2) *
      (∏ x, w x (q.1 x)) * (∏ x, w x (q.2 x))) * key
  have h4 := integral_four_expand hHρ hρ' hHρ' hρ
  beta_reduce at h4
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, h4] at h0
  linarith

/-! ## Part 2 (R4 core): the Volterra positivity lemma -/

theorem sum_add_single_eq (τ : ι → ℝ) (i : ι) (s : ℝ) :
    ∑ x, (τ + Pi.single i s : ι → ℝ) x = ∑ x, τ x + s := by
  simp [Finset.sum_add_distrib]

theorem add_single_nonneg {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) (i : ι) {s : ℝ} (hs : 0 ≤ s) :
    ∀ x, 0 ≤ (τ + Pi.single i s : ι → ℝ) x := by
  intro x
  by_cases hx : x = i
  · subst hx; simp only [Pi.add_apply, Pi.single_eq_same]; linarith [hτ x]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hx, add_zero]; exact hτ x

/-- One step of the contraction: a weighted lower bound −D ≤ M e^{−cΣτ} improves to
−D ≤ (r/c) M e^{−cΣτ}. No integrability of E is assumed (a non-integrable E has integral 0). -/
theorem volterra_step {J : ι → ι → ℝ} (hJ : ∀ i k, 0 ≤ J i k) {r c : ℝ} (hc : 0 < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r)
    {D : ι → (ι → ℝ) → ℝ} {E : ι → (ι → ℝ) → ℝ → ℝ}
    (hD : ∀ i τ, (∀ x, 0 ≤ τ x) → D i τ = ∫ s in Ioi (0 : ℝ), E i τ s)
    (hE : ∀ i τ s, (∀ x, 0 ≤ τ x) → 0 < s → ∑ k, J i k * D k (τ + Pi.single i s) ≤ E i τ s)
    {M : ℝ} (hM0 : 0 ≤ M) (hr0 : 0 ≤ r)
    (hM : ∀ i τ, (∀ x, 0 ≤ τ x) → -D i τ ≤ M * Real.exp (-(c * ∑ x, τ x))) :
    ∀ i τ, (∀ x, 0 ≤ τ x) → -D i τ ≤ (r / c * M) * Real.exp (-(c * ∑ x, τ x)) := by
  intro i τ hτ
  set e := Real.exp (-(c * ∑ x, τ x)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hint : IntegrableOn (fun s : ℝ => -(r * M * e) * Real.exp (-c * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul _
  have hval : ∫ s in Ioi (0 : ℝ), -(r * M * e) * Real.exp (-c * s) = -(r * M * e) / c := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hle : ∀ s ∈ Ioi (0 : ℝ), -(r * M * e) * Real.exp (-c * s) ≤ E i τ s := by
    intro s hs
    have hσ := add_single_nonneg hτ i (le_of_lt hs)
    have h1 : ∀ k, J i k * (-(M * Real.exp (-(c * ∑ x, (τ + Pi.single i s : ι → ℝ) x)))) ≤
        J i k * D k (τ + Pi.single i s) :=
      fun k => mul_le_mul_of_nonneg_left (by linarith [hM k _ hσ]) (hJ i k)
    have hexp : Real.exp (-(c * (∑ x, τ x + s))) = e * Real.exp (-c * s) := by
      rw [he, ← Real.exp_add]; ring_nf
    have hp : 0 ≤ M * (e * Real.exp (-c * s)) := mul_nonneg hM0 (mul_nonneg he0.le (Real.exp_pos _).le)
    calc -(r * M * e) * Real.exp (-c * s) ≤ -((∑ k, J i k) * (M * (e * Real.exp (-c * s)))) := by
          have := mul_le_mul_of_nonneg_right (hrow i) hp
          nlinarith
      _ = ∑ k, J i k * (-(M * Real.exp (-(c * ∑ x, (τ + Pi.single i s : ι → ℝ) x)))) := by
          rw [sum_add_single_eq, hexp, ← Finset.sum_mul]; ring
      _ ≤ ∑ k, J i k * D k (τ + Pi.single i s) := Finset.sum_le_sum fun k _ => h1 k
      _ ≤ E i τ s := hE i τ s hτ hs
  have hge : -(r * M * e) / c ≤ D i τ := by
    rw [hD i τ hτ, ← hval]
    by_cases hEi : IntegrableOn (E i τ) (Ioi 0)
    · exact setIntegral_mono_on hint hEi measurableSet_Ioi hle
    · rw [integral_undef hEi, hval]
      have : 0 ≤ r * M * e / c := by have := mul_nonneg (mul_nonneg hr0 hM0) he0.le; positivity
      rw [neg_div]; linarith
  have h2 : -D i τ ≤ r * M * e / c := by rw [neg_div] at hge; linarith
  calc -D i τ ≤ r * M * e / c := h2
    _ = r / c * M * e := by ring

/-- **The Volterra positivity lemma** (replaces summing the BFS walk series). Let J ≥ 0 with row
sums ≤ r < c. If for all τ ≥ 0 and all i
  D_i(τ) = ∫_0^∞ E_i(τ, s) ds,   E_i(τ, s) ≥ Σ_k J_ik D_k(τ + s e_i)   (s > 0),
(i.e. D = source + K D with a nonnegative source and (K D)_i(τ) = Σ_k J_ik ∫_0^∞ D_k(τ + s e_i) ds),
and −D_i(τ) ≤ M e^{−c Σ_x τ_x} for some M, then D ≥ 0 on [0, ∞)^ι. In the weighted sup-norm
‖g‖ = sup_τ |g(τ)| e^{cΣτ}, ‖K‖ ≤ r/c < 1 and D⁻ ≤ K D⁻. -/
theorem volterra_nonneg {J : ι → ι → ℝ} (hJ : ∀ i k, 0 ≤ J i k) {r c : ℝ} (hc : 0 < c)
    (hr0 : 0 ≤ r) (hrc : r < c) (hrow : ∀ i, ∑ k, J i k ≤ r)
    {D : ι → (ι → ℝ) → ℝ} {E : ι → (ι → ℝ) → ℝ → ℝ}
    (hD : ∀ i τ, (∀ x, 0 ≤ τ x) → D i τ = ∫ s in Ioi (0 : ℝ), E i τ s)
    (hE : ∀ i τ s, (∀ x, 0 ≤ τ x) → 0 < s → ∑ k, J i k * D k (τ + Pi.single i s) ≤ E i τ s)
    (hM : ∃ M, ∀ i τ, (∀ x, 0 ≤ τ x) → -D i τ ≤ M * Real.exp (-(c * ∑ x, τ x))) :
    ∀ i τ, (∀ x, 0 ≤ τ x) → 0 ≤ D i τ := by
  obtain ⟨M, hM⟩ := hM
  have hq0 : 0 ≤ r / c := div_nonneg hr0 hc.le
  have hq1 : r / c < 1 := (div_lt_one hc).mpr hrc
  have hiter : ∀ n : ℕ, ∀ i τ, (∀ x, 0 ≤ τ x) →
      -D i τ ≤ ((r / c) ^ n * max M 0) * Real.exp (-(c * ∑ x, τ x)) := by
    intro n
    induction n with
    | zero =>
      intro i τ hτ
      simpa using (hM i τ hτ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    | succ n ih =>
      intro i τ hτ
      refine (volterra_step hJ hc hrow hD hE (mul_nonneg (pow_nonneg hq0 n) (le_max_right _ _))
        hr0 ih i τ hτ).trans (le_of_eq ?_)
      ring
  intro i τ hτ
  have ht : Tendsto (fun n : ℕ => ((r / c) ^ n * max M 0) * Real.exp (-(c * ∑ x, τ x)))
      atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (max M 0)).mul_const
      (Real.exp (-(c * ∑ x, τ x)))
    simpa using this
  have := ge_of_tendsto' ht (fun n => hiter n i τ hτ)
  linarith

/-! ## Part 3: the local-time family [·]_τ for a general ferromagnetic pair interaction -/

/-- [F]_τ = ∫ F e^{Q_K} W_τ, W_τ = ∏_x e^{−f(φ_x²/2 + τ_x)}, f(u) = au + bu² (unnormalised).
For the quartic box, `tauInt n k m₀ λ = tI (Jnn n k) (alphaQ n m₀ λ) (betaQ n λ)` (rfl). -/
def tI (K : ι → ι → ℝ) (a b : ℝ) (τ : ι → ℝ) (F : (ι → ℝ) → ℝ) : ℝ :=
  ∫ φ, F φ * Real.exp (quadE K φ) * tw a b τ φ

/-- The single-site weight at local time τ_x. -/
def siteW (a b : ℝ) (τ : ι → ℝ) (x : ι) (y : ℝ) : ℝ := Real.exp (-fq a b (y ^ 2 / 2 + τ x))

theorem rhoQ_siteW (K : ι → ι → ℝ) (a b : ℝ) (τ φ : ι → ℝ) :
    Real.exp (quadE K φ) * tw a b τ φ = rhoQ (siteW a b τ) (quadE K) φ := by
  unfold rhoQ siteW tw
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Raising the local times from τ to τ': W_{τ'} = κ · e^{−Σ_x b(τ'_x − τ_x) φ_x²} · W_τ. -/
theorem tw_shift_mass (a b : ℝ) (τ τ' φ : ι → ℝ) :
    tw a b τ' φ = Real.exp (∑ x, fq a b (τ x) - ∑ x, fq a b (τ' x)) *
      (Real.exp (-massV (fun x => b * (τ' x - τ x)) φ) * tw a b τ φ) := by
  unfold tw massV
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by unfold fq; ring

/-- **R3 for the local-time family: [·]-expectations of cone elements decrease in τ.** For K ≥ 0,
b ≥ 0, τ ≤ τ' and H ∈ 𝒞 (with the four integrability conditions):
  [H]_{τ'} [1]_τ ≤ [H]_τ [1]_{τ'},   i.e. ⟨H⟩_{τ'} ≤ ⟨H⟩_τ. -/
theorem tI_mono {K : ι → ι → ℝ} (hK : ∀ x y, 0 ≤ K x y) {a b : ℝ} (hb : 0 ≤ b)
    {τ τ' : ι → ℝ} (hle : ∀ x, τ x ≤ τ' x) {H : (ι → ℝ) → ℝ} (hH : InCone H)
    (h1 : Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b τ φ)
    (h2 : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ)
    (h3 : Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b τ' φ)
    (h4 : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ' φ) :
    tI K a b τ' H * tI K a b τ (fun _ => 1) ≤ tI K a b τ H * tI K a b τ' (fun _ => 1) := by
  set w := siteW a b τ with hw
  set γ : ι → ℝ := fun x => b * (τ' x - τ x) with hγ
  set κ := Real.exp (∑ x, fq a b (τ x) - ∑ x, fq a b (τ' x)) with hκ
  have hκ0 : 0 < κ := Real.exp_pos _
  have hγ0 : ∀ x, 0 ≤ γ x := fun x => mul_nonneg hb (by linarith [hle x])
  have hwe : ∀ x y, w x (-y) = w x y := fun x y => by simp only [hw, siteW, neg_sq]
  have hwn : ∀ x y, 0 ≤ w x y := fun x y => (Real.exp_pos _).le
  have hQ : IsPosPoly (quadE K) := IsPosPoly.quadForm hK
  have e0 : ∀ (F : (ι → ℝ) → ℝ) φ, F φ * Real.exp (quadE K φ) * tw a b τ φ =
      F φ * rhoQ w (quadE K) φ := fun F φ => by rw [mul_assoc, rhoQ_siteW]
  have e1 : ∀ (F : (ι → ℝ) → ℝ) φ, F φ * Real.exp (quadE K φ) * tw a b τ' φ =
      κ * (F φ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ)) := fun F φ => by
    rw [tw_shift_mass a b τ τ' φ, ← rhoQ_siteW]; ring
  have i1 : Integrable fun φ => H φ * rhoQ w (quadE K) φ :=
    h1.congr (Filter.Eventually.of_forall fun φ => e0 H φ)
  have e0' : ∀ φ, (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ = rhoQ w (quadE K) φ :=
    fun φ => by rw [one_mul, rhoQ_siteW]
  have e1' : ∀ φ, (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ' φ =
      κ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ) := fun φ => by
    have := e1 (fun _ => 1) φ; simp only [one_mul] at this ⊢; exact this
  have i2 : Integrable (rhoQ w (quadE K)) :=
    h2.congr (Filter.Eventually.of_forall e0')
  have i3 : Integrable fun φ => H φ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ) :=
    (h3.const_mul κ⁻¹).congr (Filter.Eventually.of_forall fun φ => by
      simp only; rw [e1 H φ, ← mul_assoc, inv_mul_cancel₀ hκ0.ne', one_mul])
  have i4 : Integrable fun φ => Real.exp (-massV γ φ) * rhoQ w (quadE K) φ :=
    (h4.const_mul κ⁻¹).congr (Filter.Eventually.of_forall fun φ => by
      simp only; rw [e1' φ, ← mul_assoc, inv_mul_cancel₀ hκ0.ne', one_mul])
  have key := mass_mono_cone hwe hwn hH hQ hγ0 i1 i2 i3 i4
  have t1 : tI K a b τ' H = κ * ∫ φ, H φ * (Real.exp (-massV γ φ) * rhoQ w (quadE K) φ) := by
    rw [tI, ← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall (e1 H))
  have t2 : tI K a b τ' (fun _ => 1) =
      κ * ∫ φ, Real.exp (-massV γ φ) * rhoQ w (quadE K) φ := by
    rw [tI, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall e1')
  have t3 : tI K a b τ H = ∫ φ, H φ * rhoQ w (quadE K) φ :=
    integral_congr_ae (Filter.Eventually.of_forall (e0 H))
  have t4 : tI K a b τ (fun _ => 1) = ∫ φ, rhoQ w (quadE K) φ :=
    integral_congr_ae (Filter.Eventually.of_forall e0')
  rw [t1, t2, t3, t4, mul_assoc, mul_left_comm (∫ φ, H φ * rhoQ w (quadE K) φ)]
  exact mul_le_mul_of_nonneg_left key hκ0.le

/-! ### The admissible class and integrability -/

/-- Admissible observables: continuous, |H| ≤ C e^{a' Σ|φ_x|} Ψ for an envelope Ψ ≥ 1 (Ψ = 1 for
polynomial observables; Ψ = 1 + e^{boundary coupling} for the decoupled measure of R5). -/
def Adm (Ψ : (ι → ℝ) → ℝ) (H : (ι → ℝ) → ℝ) : Prop :=
  Continuous H ∧ ∃ C a' : ℝ, ∀ φ, |H φ| ≤ C * Real.exp (a' * ∑ x, |φ x|) * Ψ φ

lemma Adm.congr {Ψ H H' : (ι → ℝ) → ℝ} (hH : Adm Ψ H) (h : ∀ φ, H φ = H' φ) : Adm Ψ H' := by
  have : H = H' := funext h
  rwa [← this]

lemma Adm.mul_coord {Ψ H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) (j : ι) :
    Adm Ψ (fun φ => φ j * H φ) := by
  obtain ⟨hc, C, a', hb⟩ := hH
  refine ⟨(continuous_apply j).mul hc, C, a' + 1, fun φ => ?_⟩
  have hC : 0 ≤ C * Real.exp (a' * ∑ x, |φ x|) * Ψ φ := (abs_nonneg _).trans (hb φ)
  rw [abs_mul]
  calc |φ j| * |H φ| ≤ Real.exp (∑ x, |φ x|) * (C * Real.exp (a' * ∑ x, |φ x|) * Ψ φ) :=
        mul_le_mul (abs_le_exp_sum φ j) (hb φ) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [add_mul, one_mul, Real.exp_add]; ring

lemma Adm.const {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ) (v : ℝ) : Adm Ψ (fun _ => v) :=
  ⟨continuous_const, |v|, 0, fun φ => by
    rw [zero_mul, Real.exp_zero, mul_one]; exact le_mul_of_one_le_right (abs_nonneg v) (hΨ φ)⟩

lemma Adm.coord {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ) (j : ι) : Adm Ψ (fun φ => φ j) :=
  ((Adm.const hΨ 1).mul_coord j).congr fun _ => mul_one _

/-- Integrability at τ ≥ 0 from integrability at τ = 0 (W_τ ≤ e^{−Σ f(τ_x)} W_0). -/
theorem integrable_adm {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) :
    Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b τ φ := by
  have hc := hH.1
  refine ((hint H hH).norm.const_mul (Real.exp (-∑ x, fq a b (τ x)))).mono'
    (by fun_prop : Continuous fun φ => H φ * Real.exp (quadE K φ) * tw a b τ φ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos a b τ φ), abs_of_pos (tw_pos a b 0 φ)]
  calc |H φ| * Real.exp (quadE K φ) * tw a b τ φ ≤
      |H φ| * Real.exp (quadE K φ) * (Real.exp (-∑ x, fq a b (τ x)) * tw a b 0 φ) :=
        mul_le_mul_of_nonneg_left (tw_le_tw_zero hb hτ φ) (by positivity)
    _ = _ := by ring

/-- |[H]_τ| ≤ e^{−Σ_x f(τ_x)} ∫ |H| e^{Q_K} W_0. -/
theorem abs_tI_le {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) :
    |tI K a b τ H| ≤ Real.exp (-∑ x, fq a b (τ x)) *
      ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b 0 φ‖ := by
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun φ => abs_nonneg _)
    ((hint H hH).norm.const_mul _) (Filter.Eventually.of_forall fun φ => ?_))
  simp only [Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos a b τ φ), abs_of_pos (tw_pos a b 0 φ)]
  calc |H φ| * Real.exp (quadE K φ) * tw a b τ φ ≤
      |H φ| * Real.exp (quadE K φ) * (Real.exp (-∑ x, fq a b (τ x)) * tw a b 0 φ) :=
        mul_le_mul_of_nonneg_left (tw_le_tw_zero hb hτ φ) (by positivity)
    _ = _ := by ring

/-- Integrability of the shifted family in the local time s (measurability by Fubini's
measurability lemma; decay from W_{τ+s e_i} ≤ W_τ C e^{−cs}). -/
theorem integrableOn_tI_shift {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a)
    {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) (i : ι) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) :
    IntegrableOn (fun s => tI K a b (τ + Pi.single i s) H) (Ioi 0) := by
  obtain ⟨c, hc, C, hC⟩ := exists_exp_bound hb hab
  have hHc := hH.1
  have hcont : Continuous fun z : ℝ × (ι → ℝ) =>
      H z.2 * Real.exp (quadE K z.2) * tw a b (τ + Pi.single i z.1) z.2 := by
    have e : (fun z : ℝ × (ι → ℝ) =>
        H z.2 * Real.exp (quadE K z.2) * tw a b (τ + Pi.single i z.1) z.2) =
        fun z => H z.2 * Real.exp (quadE K z.2) * (tw a b τ z.2 *
          Real.exp (fq a b (z.2 i ^ 2 / 2 + τ i) - fq a b (z.2 i ^ 2 / 2 + τ i + z.1))) := by
      funext z; rw [tw_shift]
    rw [e]; unfold fq; fun_prop
  have hsm0 : StronglyMeasurable fun s : ℝ => ∫ φ, (fun z : ℝ × (ι → ℝ) =>
      H z.2 * Real.exp (quadE K z.2) * tw a b (τ + Pi.single i z.1) z.2) (s, φ) :=
    StronglyMeasurable.integral_prod_right' (ν := (volume : Measure (ι → ℝ)))
      hcont.stronglyMeasurable
  have hsm : StronglyMeasurable fun s : ℝ => tI K a b (τ + Pi.single i s) H := hsm0
  obtain ⟨N, hN⟩ : ∃ N, N = ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ := ⟨_, rfl⟩
  have hI := integrable_adm hb hint hτ hH
  have hbd : ∀ s ∈ Ioi (0 : ℝ), ‖tI K a b (τ + Pi.single i s) H‖ ≤ N * C * Real.exp (-c * s) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hle : ∀ φ, ‖H φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ‖ ≤
        ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ * (C * Real.exp (-c * s)) := by
      intro φ
      have h1 := tw_shift_le hb hC (hτ i) φ hs0
      have h2 : 0 ≤ |H φ| * Real.exp (quadE K φ) := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos _ _ _ φ), abs_of_pos (tw_pos _ _ _ φ),
        mul_assoc _ (tw a b τ φ)]
      exact mul_le_mul_of_nonneg_left h1 h2
    have h3 : ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ‖ ≤
        ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ * (C * Real.exp (-c * s)) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun φ => norm_nonneg _)
        (hI.norm.mul_const _) (Filter.Eventually.of_forall hle)
    have h5 : ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b τ φ‖ * (C * Real.exp (-c * s)) =
        N * (C * Real.exp (-c * s)) := by rw [integral_mul_const, hN]
    have h4 : ‖tI K a b (τ + Pi.single i s) H‖ ≤
        ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ‖ := by
      unfold tI; exact norm_integral_le_integral_norm _
    have h6 := h4.trans (h3.trans h5.le)
    rw [← mul_assoc] at h6
    exact h6
  exact ((exp_neg_integrableOn_Ioi 0 hc).const_mul (N * C)).mono' hsm.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi hbd)

/-! ### R2 for the general family, and auxiliary bounds -/

/-- **R2 (abstract):** the local-time integration by parts for [·]_τ with any pair matrix K and
the admissible class: [φ_i G]_τ = ∫_0^∞ ([∂_i G]_{τ+se_i} + Σ_j (K_ij + K_ji) [φ_j G]_{τ+se_i}) ds. -/
theorem tI_ibp {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a)
    {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) (i : ι) {G G' : (ι → ℝ) → ℝ} (hG : Adm Ψ G)
    (hG'a : Adm Ψ G') (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1)) :
    tI K a b τ (fun φ => φ i * G φ) =
      ∫ s in Ioi (0 : ℝ), (tI K a b (τ + Pi.single i s) G' +
        ∑ j, (K i j + K j i) * tI K a b (τ + Pi.single i s) (fun φ => φ j * G φ)) := by
  have hsplit : ∀ σ : ι → ℝ, (∀ x, 0 ≤ σ x) →
      (Integrable fun φ => (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) *
        Real.exp (quadE K φ) * tw a b σ φ) ∧
      ∫ φ, (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ) * tw a b σ φ =
      tI K a b σ G' + ∑ j, (K i j + K j i) * tI K a b σ (fun φ => φ j * G φ) := by
    intro σ hσ
    have I' := integrable_adm hb hint hσ hG'a
    have Ij : ∀ j, Integrable fun φ => φ j * G φ * Real.exp (quadE K φ) * tw a b σ φ :=
      fun j => integrable_adm hb hint hσ (hG.mul_coord j)
    have e : (fun φ => (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) *
        Real.exp (quadE K φ) * tw a b σ φ) =
        fun φ => G' φ * Real.exp (quadE K φ) * tw a b σ φ +
          ∑ j, (K i j + K j i) * (φ j * G φ * Real.exp (quadE K φ) * tw a b σ φ) := by
      funext φ
      rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hS : Integrable fun φ => ∑ j, (K i j + K j i) *
        (φ j * G φ * Real.exp (quadE K φ) * tw a b σ φ) :=
      integrable_finsetSum _ fun j _ => (Ij j).const_mul _
    refine ⟨e ▸ I'.add hS, ?_⟩
    rw [e, integral_add I' hS, integral_finsetSum _ fun j _ => (Ij j).const_mul _]
    unfold tI
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have h3G : Adm Ψ (fun φ => φ i ^ 3 * G φ) :=
    (((hG.mul_coord i).mul_coord i).mul_coord i).congr fun φ => by ring
  have main := local_time_ibp_bfs hb hab K τ i (hτ i) hG.1 hG'a.1 hG'
    (integrable_adm hb hint hτ hG) (integrable_adm hb hint hτ (hG.mul_coord i))
    (integrable_adm hb hint hτ h3G) (hsplit τ hτ).1
  have lhs : tI K a b τ (fun φ => φ i * G φ) =
      ∫ φ, φ i * G φ * Real.exp (quadE K φ) * tw a b τ φ := rfl
  rw [lhs, main]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    (hsplit _ (add_single_nonneg hτ i (le_of_lt hs))).2

lemma hasLineDerivAt_coord (i j : ι) (φ : ι → ℝ) :
    HasLineDerivAt ℝ (fun ψ : ι → ℝ => ψ j) ((Pi.single i (1 : ℝ) : ι → ℝ) j) φ
      (Pi.single i 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => (φ + t • (Pi.single i (1 : ℝ) : ι → ℝ)) j) =
      fun t => φ j + t * (Pi.single i (1 : ℝ) : ι → ℝ) j := by
    funext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const ((Pi.single i (1 : ℝ) : ι → ℝ) j)).const_add
    (φ j)

theorem tI_one_pos {K : ι → ι → ℝ} {a b : ℝ} {τ : ι → ℝ}
    (h : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ) :
    0 < tI K a b τ (fun _ => 1) := by
  unfold tI
  have hpos : ∀ φ, 0 < (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ := fun φ =>
    mul_pos (mul_pos one_pos (Real.exp_pos _)) (tw_pos a b τ φ)
  rw [integral_pos_iff_support_of_nonneg (fun φ => (hpos φ).le) h]
  have : Function.support (fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b τ φ) = Set.univ :=
    Set.eq_univ_of_forall fun φ => (hpos φ).ne'
  rw [this]
  exact isOpen_univ.measure_pos volume univ_nonempty

theorem tI_const (K : ι → ι → ℝ) (a b : ℝ) (τ : ι → ℝ) (v : ℝ) :
    tI K a b τ (fun _ => v) = v * tI K a b τ (fun _ => 1) := by
  unfold tI
  rw [← integral_const_mul]
  congr 1; funext φ; ring

/-- f(t) ≥ c' t − (c' − a)²/(4b) for b > 0 (any c'): the quartic term beats any linear weight. -/
lemma fq_ge_lin {a b : ℝ} (hb : 0 < b) (c' t : ℝ) :
    c' * t - (c' - a) ^ 2 / (4 * b) ≤ fq a b t := by
  unfold fq
  have h : 0 ≤ (2 * b * t + a - c') ^ 2 / (4 * b) := by positivity
  have e : (2 * b * t + a - c') ^ 2 / (4 * b) =
      a * t + b * t ^ 2 - (c' * t - (c' - a) ^ 2 / (4 * b)) := by
    field_simp; ring
  linarith

lemma exp_neg_sum_fq_le {a b c' C₀ : ℝ} (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq a b t)
    {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) :
    Real.exp (-∑ x, fq a b (τ x)) ≤
      Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, τ x)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := Finset.sum_le_sum (s := Finset.univ) fun x _ => hf (τ x) (hτ x)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  linarith

/-! ## Part 4 (R4): strong Gaussian domination, BFS Theorem 5.1 -/

/-- D_i(τ) = Σ_j c_j [φ_i φ_j]_τ − [φ_i G]_τ. -/
def sgdD (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (cc : ι → ℝ) (i : ι) (τ : ι → ℝ) : ℝ :=
  ∑ j, cc j * tI K a b τ (fun φ => φ i * φ j) - tI K a b τ (fun φ => φ i * G φ)

/-- The local-time integrand of D_i(τ) given by R2 (σ = τ + s e_i). -/
def sgdE (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ) (cc : ι → ℝ)
    (i : ι) (τ : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j, cc j * (tI K a b (τ + Pi.single i s) (fun _ => (Pi.single i (1 : ℝ) : ι → ℝ) j) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * φ j)) -
    (tI K a b (τ + Pi.single i s) (G' i) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * G φ))

/-- The Volterra structure: E_i(τ, s) = (c_i [1]_σ − [∂_i G]_σ) + Σ_k J_ik D_k(σ). -/
theorem sgdE_eq (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ)
    (cc : ι → ℝ) (i : ι) (τ : ι → ℝ) (s : ℝ) :
    sgdE K a b G G' cc i τ s =
      (cc i * tI K a b (τ + Pi.single i s) (fun _ => 1) - tI K a b (τ + Pi.single i s) (G' i)) +
        ∑ k, (K i k + K k i) * sgdD K a b G cc k (τ + Pi.single i s) := by
  have h1 : ∑ j, cc j * (tI K a b (τ + Pi.single i s) (fun _ => (Pi.single i (1 : ℝ) : ι → ℝ) j) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * φ j)) =
      cc i * tI K a b (τ + Pi.single i s) (fun _ => 1) +
        ∑ k, (K i k + K k i) * ∑ j, cc j * tI K a b (τ + Pi.single i s) (fun φ => φ k * φ j) := by
    rw [Finset.sum_congr rfl fun j _ => mul_add (cc j) _ _, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [tI_const, Pi.single_eq_of_ne hj]; ring)
        (fun h => absurd (Finset.mem_univ i) h), tI_const, Pi.single_eq_same, one_mul]
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  unfold sgdE sgdD
  rw [h1]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Strong Gaussian domination (BFS CMP 83, Theorem 5.1), abstract finite-dimensional form.**
Let K ≥ 0 (pair matrix, J = K + Kᵀ), f(u) = au + bu² with b ≥ 0 and (b > 0 or a > 0); let the
admissible class (envelope Ψ ≥ 1) be integrable against e^{Q_K} W_0; let J have row sums ≤ r < c'
with f(t) ≥ c't − C₀ on [0, ∞) (automatic for b > 0, `fq_ge_lin`). For G admissible with
admissible derivatives ∂_j G = G' j lying in the cone 𝒞:
  [φ_i G]_0 ≤ Σ_j (⟨∂_j G⟩_0) [φ_i φ_j]_0,    ⟨·⟩_0 = [·]_0 / [1]_0.
Proof: R2 gives D = (source) + K D for D_i(τ) = Σ_j c_j [φ_iφ_j]_τ − [φ_i G]_τ, the source
c_i[1]_σ − [∂_i G]_σ is ≥ 0 by R3 (`tI_mono`), |D(τ)| ≤ M e^{−Σ f(τ_x)} ≤ M' e^{−c'Στ}, and
`volterra_nonneg` gives D ≥ 0. -/
theorem strong_gaussian_domination {K : ι → ι → ℝ} (hK : ∀ x y, 0 ≤ K x y) {a b : ℝ}
    (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a) {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c') (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq a b t)
    {G : (ι → ℝ) → ℝ} {G' : ι → (ι → ℝ) → ℝ} (hG : Adm Ψ G) (hG'a : ∀ j, Adm Ψ (G' j))
    (hG' : ∀ j φ, HasLineDerivAt ℝ G (G' j φ) φ (Pi.single j 1)) (hcone : ∀ j, InCone (G' j))
    (i : ι) :
    tI K a b 0 (fun φ => φ i * G φ) ≤
      ∑ j, (tI K a b 0 (G' j) / tI K a b 0 (fun _ => 1)) * tI K a b 0 (fun φ => φ i * φ j) := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = tI K a b 0 (fun _ => 1) := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : ι → ℝ, cc = fun j => tI K a b 0 (G' j) / Z := ⟨_, rfl⟩
  have hc' : 0 < c' := lt_of_le_of_lt hr0 hrc
  have h0 : ∀ x, 0 ≤ (0 : ι → ℝ) x := fun x => le_refl 0
  have hZ0 : 0 < Z := hZ ▸ tI_one_pos (integrable_adm hb hint h0 (Adm.const hΨ 1))
  have hJ : ∀ i k, 0 ≤ K i k + K k i := fun i k => add_nonneg (hK i k) (hK k i)
  have hIs : ∀ τ : ι → ℝ, (∀ x, 0 ≤ τ x) → ∀ l H, Adm Ψ H →
      IntegrableOn (fun s => tI K a b (τ + Pi.single l s) H) (Ioi 0) :=
    fun τ hτ l H hH => integrableOn_tI_shift hb hab hint hτ l hH
  -- (hD) the R2 identities, combined
  have hD : ∀ l τ, (∀ x, 0 ≤ τ x) →
      sgdD K a b G cc l τ = ∫ s in Ioi (0 : ℝ), sgdE K a b G G' cc l τ s := by
    intro l τ hτ
    have hA : ∀ j, IntegrableOn (fun s =>
        tI K a b (τ + Pi.single l s) (fun _ => (Pi.single l (1 : ℝ) : ι → ℝ) j) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * φ j)) (Ioi 0) :=
      fun j => (hIs τ hτ l _ (Adm.const hΨ _)).add (integrable_finsetSum _ fun k _ =>
        (hIs τ hτ l _ ((Adm.coord hΨ j).mul_coord k)).const_mul _)
    have hB : IntegrableOn (fun s => tI K a b (τ + Pi.single l s) (G' l) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * G φ)) (Ioi 0) :=
      (hIs τ hτ l _ (hG'a l)).add (integrable_finsetSum _ fun k _ =>
        (hIs τ hτ l _ (hG.mul_coord k)).const_mul _)
    have R2j : ∀ j, tI K a b τ (fun φ => φ l * φ j) = ∫ s in Ioi (0 : ℝ),
        (tI K a b (τ + Pi.single l s) (fun _ => (Pi.single l (1 : ℝ) : ι → ℝ) j) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * φ j)) :=
      fun j => tI_ibp hb hab hint hτ l (Adm.coord hΨ j) (Adm.const hΨ _)
        (fun φ => hasLineDerivAt_coord l j φ)
    have R2G := tI_ibp (K := K) hb hab hint hτ l hG (hG'a l) (hG' l)
    have hsum : ∑ j, cc j * tI K a b τ (fun φ => φ l * φ j) = ∫ s in Ioi (0 : ℝ),
        ∑ j, cc j * (tI K a b (τ + Pi.single l s) (fun _ => (Pi.single l (1 : ℝ) : ι → ℝ) j) +
        ∑ k, (K l k + K k l) * tI K a b (τ + Pi.single l s) (fun φ => φ k * φ j)) := by
      rw [integral_finsetSum _ fun j _ => (hA j).const_mul (cc j)]
      exact Finset.sum_congr rfl fun j _ => by rw [R2j j, integral_const_mul]
    unfold sgdD
    rw [hsum, R2G, ← integral_sub (integrable_finsetSum _ fun j _ => (hA j).const_mul _) hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [sgdE]
  -- (hE) the source is nonnegative (R3)
  have hE : ∀ l τ s, (∀ x, 0 ≤ τ x) → 0 < s →
      ∑ k, (K l k + K k l) * sgdD K a b G cc k (τ + Pi.single l s) ≤
        sgdE K a b G G' cc l τ s := by
    intro l τ s hτ hs
    have hσ := add_single_nonneg hτ l (le_of_lt hs)
    have i1 : Integrable fun φ => G' l φ * Real.exp (quadE K φ) * tw a b 0 φ :=
      integrable_adm hb hint h0 (hG'a l)
    have i2 : Integrable fun φ => (1 : ℝ) * Real.exp (quadE K φ) * tw a b 0 φ :=
      integrable_adm hb hint h0 (Adm.const hΨ 1)
    have i3 : Integrable fun φ => G' l φ * Real.exp (quadE K φ) * tw a b (τ + Pi.single l s) φ :=
      integrable_adm hb hint hσ (hG'a l)
    have i4 : Integrable fun φ =>
        (1 : ℝ) * Real.exp (quadE K φ) * tw a b (τ + Pi.single l s) φ :=
      integrable_adm hb hint hσ (Adm.const hΨ 1)
    have hle : ∀ x, (0 : ι → ℝ) x ≤ (τ + Pi.single l s : ι → ℝ) x := hσ
    have key := tI_mono hK hb hle (hcone l) i1 i2 i3 i4
    rw [← hZ] at key
    have hsrc : tI K a b (τ + Pi.single l s) (G' l) ≤
        cc l * tI K a b (τ + Pi.single l s) (fun _ => 1) := by
      rw [hcc, div_mul_eq_mul_div, le_div_iff₀ hZ0]
      exact key
    rw [sgdE_eq]
    linarith
  -- (hM) the weighted a-priori bound
  have hM : ∃ M, ∀ l τ, (∀ x, 0 ≤ τ x) →
      -sgdD K a b G cc l τ ≤ M * Real.exp (-(c' * ∑ x, τ x)) := by
    set N1 : ι → ι → ℝ := fun l j =>
      ∫ φ, ‖φ l * φ j * Real.exp (quadE K φ) * tw a b 0 φ‖ with hN1
    set N2 : ι → ℝ := fun l => ∫ φ, ‖φ l * G φ * Real.exp (quadE K φ) * tw a b 0 φ‖ with hN2
    set Ml : ι → ℝ := fun l => ∑ j, |cc j| * N1 l j + N2 l with hMl
    have hMl0 : ∀ l, 0 ≤ Ml l := fun l =>
      add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _)) (integral_nonneg fun _ => norm_nonneg _)
    refine ⟨Real.exp (Fintype.card ι * C₀) * ∑ l, Ml l, fun l τ hτ => ?_⟩
    set ef := Real.exp (-∑ x, fq a b (τ x)) with hef
    have hab1 : ∀ F, Adm Ψ F → |tI K a b τ F| ≤
        ef * ∫ φ, ‖F φ * Real.exp (quadE K φ) * tw a b 0 φ‖ :=
      fun F hF => abs_tI_le hb hint hτ hF
    have s1 : -(∑ j, cc j * tI K a b τ (fun φ => φ l * φ j)) ≤ ∑ j, |cc j| * (ef * N1 l j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      calc -(cc j * tI K a b τ (fun φ => φ l * φ j))
          ≤ |cc j * tI K a b τ (fun φ => φ l * φ j)| := neg_le_abs _
        _ = |cc j| * |tI K a b τ (fun φ => φ l * φ j)| := abs_mul _ _
        _ ≤ |cc j| * (ef * N1 l j) :=
          mul_le_mul_of_nonneg_left (hab1 _ ((Adm.coord hΨ j).mul_coord l)) (abs_nonneg _)
    have s2 : tI K a b τ (fun φ => φ l * G φ) ≤ ef * N2 l :=
      (le_abs_self _).trans (hab1 _ (hG.mul_coord l))
    have e : ef * Ml l = ∑ j, |cc j| * (ef * N1 l j) + ef * N2 l := by
      simp only [hMl]
      rw [mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have s3 : -sgdD K a b G cc l τ ≤ ef * Ml l := by
      unfold sgdD; rw [e]; linarith
    have hef1 : ef ≤ Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, τ x)) :=
      exp_neg_sum_fq_le hf hτ
    have hMs : Ml l ≤ ∑ l, Ml l :=
      Finset.single_le_sum (f := Ml) (fun l _ => hMl0 l) (Finset.mem_univ l)
    calc -sgdD K a b G cc l τ ≤ ef * Ml l := s3
      _ ≤ (Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, τ x))) * ∑ l, Ml l :=
        mul_le_mul hef1 hMs (hMl0 l) (by positivity)
      _ = _ := by ring
  have hfin := volterra_nonneg (J := fun i k => K i k + K k i) hJ hc' hr0 hrc hrow hD hE hM
    i 0 h0
  unfold sgdD at hfin
  rw [← hZ]
  simp only [hcc] at hfin
  linarith

end PP2SGD

/-! ## Part 5: the quartic Dirichlet-box model -/

namespace PP2Target

open PP2LocalTime PP2Griffiths PP2SGD

variable {n k : ℕ}

theorem tauInt_eq_tI (m₀ lam : ℝ) (τ : DField n k) (F : DField n k → ℝ) :
    tauInt n k m₀ lam τ F = tI (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) τ F := rfl

/-- The admissible class with envelope 1 (all observables of exponential-linear growth, e.g. all
polynomials) is integrable against the quartic box weight (m₀ ≠ 0, λ ≥ 0). -/
theorem hint_box {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) :
    ∀ H, Adm (fun _ : DField n k => (1 : ℝ)) H → Integrable fun φ => H φ *
      Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ := by
  rintro H ⟨hc, C, a', hb⟩
  exact integrable_tau hm hlam (fun x => le_refl _) hc C a' (fun φ => by simpa using hb φ)

/-- **R3 for the quartic box model.** For m₀ ≠ 0, λ ≥ 0, 0 ≤ τ ≤ τ' and H in the cone 𝒞 of
exponential-linear growth: [H]_{τ'} [1]_τ ≤ [H]_τ [1]_{τ'} (⟨H⟩_τ is decreasing in each τ_x). -/
theorem tauInt_mono {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) {τ τ' : DField n k}
    (hτ : ∀ x, 0 ≤ τ x) (hle : ∀ x, τ x ≤ τ' x) {H : DField n k → ℝ} (hH : InCone H)
    (hHa : Adm (fun _ => 1) H) :
    tauInt n k m₀ lam τ' H * tauInt n k m₀ lam τ (fun _ => 1) ≤
      tauInt n k m₀ lam τ H * tauInt n k m₀ lam τ' (fun _ => 1) := by
  have hb := betaQ_nonneg (n := n) hlam
  have hτ' : ∀ x, 0 ≤ τ' x := fun x => (hτ x).trans (hle x)
  have h1 := Adm.const (Ψ := fun _ : DField n k => (1 : ℝ)) (fun _ => le_refl 1) 1
  exact tI_mono Jnn_nonneg hb hle hH (integrable_adm hb (hint_box hm hlam) hτ hHa)
    (integrable_adm hb (hint_box hm hlam) hτ h1) (integrable_adm hb (hint_box hm hlam) hτ' hHa)
    (integrable_adm hb (hint_box hm hlam) hτ' h1)

/-- The quartic-box strong Gaussian domination from the abstract one, given the contraction data
(row bound r < c' and f(t) ≥ c't − C₀). -/
theorem sgd_box_of {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hab : 0 < betaQ n lam ∨ 0 < alphaQ n m₀ lam) {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c')
    (hrow : ∀ x : DSite n k, ∑ y, (Jnn n k x y + Jnn n k y x) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq (alphaQ n m₀ lam) (betaQ n lam) t)
    {G : DField n k → ℝ} {G' : DSite n k → DField n k → ℝ} (hG : Adm (fun _ => 1) G)
    (hG'a : ∀ j, Adm (fun _ => 1) (G' j))
    (hG' : ∀ j φ, HasLineDerivAt ℝ G (G' j φ) φ (Pi.single j 1))
    (hcone : ∀ j, InCone (G' j)) (i : DSite n k) :
    (∫ φ, φ i * G φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) ≤
      ∑ j, ((∫ φ, G' j φ * qweight n k m₀ lam φ) / ∫ φ, qweight n k m₀ lam φ) *
        twoPt n k m₀ lam i j := by
  have hb := betaQ_nonneg (n := n) hlam
  have h := strong_gaussian_domination (K := Jnn n k) Jnn_nonneg hb hab
    (Ψ := fun _ => 1) (fun _ => le_refl 1) (hint_box hm hlam) hr0 hrc hrow hf hG hG'a hG' hcone i
  set κ := Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2))
    with hκ
  have hκ0 : 0 < κ := Real.exp_pos _
  have hz : ∀ F : DField n k → ℝ, tI (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 F =
      κ * ∫ φ, F φ * qweight n k m₀ lam φ := fun F => tauInt_zero m₀ lam F
  simp only [hz, one_mul] at h
  have hZ : 0 < ∫ φ, qweight n k m₀ lam φ := integral_dweight_pos hm hlam
  have e1 : ∀ j, κ * (∫ φ, G' j φ * qweight n k m₀ lam φ) / (κ * ∫ φ, qweight n k m₀ lam φ) *
      (κ * ∫ φ, φ i * φ j * qweight n k m₀ lam φ) =
      κ * ((∫ φ, G' j φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) *
        ∫ φ, φ i * φ j * qweight n k m₀ lam φ) := fun j => by
    rw [mul_div_mul_left _ _ hκ0.ne']; ring
  simp only [e1, ← Finset.mul_sum] at h
  have h2 := le_of_mul_le_mul_left h hκ0
  unfold twoPt
  calc (∫ φ, φ i * G φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ)
      ≤ (∑ j, (∫ φ, G' j φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) *
          ∫ φ, φ i * φ j * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) :=
        div_le_div_of_nonneg_right h2 hZ.le
    _ = _ := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring

lemma sum_ite_unique {P : DSite n k → Prop} [DecidablePred P]
    (h : ∀ y y', P y → P y' → y = y') : ∑ y, (if P y then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter P).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
    h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast this

/-- **Row sums of the BFS coupling:** Σ_y J_xy ≤ 4 (each box site has at most four nearest
neighbours in the box). -/
theorem Jsym_row_le (x : DSite n k) : ∑ y, Jsym n k x y ≤ 4 := by
  have hJ : ∀ y, Jsym n k x y ≤
      (if (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) +
      (if (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) := by
    intro y
    by_cases hxy : x = y
    · subst hxy; rw [Jsym_diag]; split_ifs <;> norm_num
    · rw [Jsym_eq_bondJ hxy]
      by_cases h : nn x y
      · have hb1 : bondJ n k x y = 1 := by
          have := (spacing_pos n).ne'
          rw [bondJ, dirOp_nn 0 h]; field_simp
        rw [hb1]
        unfold nn at h
        rcases h with ⟨h2, h1 | h1⟩ | ⟨h1, h2 | h2⟩
        · have hc : (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 := ⟨h1.symm, h2.symm⟩
          split_ifs <;> norm_num
        · have hc : (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 := ⟨h1.symm, h2.symm⟩
          split_ifs <;> norm_num
        · have hc : (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 := ⟨h2.symm, h1.symm⟩
          split_ifs <;> norm_num
        · have hc : (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 := ⟨h2.symm, h1.symm⟩
          split_ifs <;> norm_num
      · rw [bondJ, dirOp_far 0 hxy h, mul_zero, neg_zero]
        split_ifs <;> norm_num
  have hu : ∀ (f : DSite n k → ℕ) (g : DSite n k → ℕ) (u v : ℕ),
      (∀ y y' : DSite n k, f y = u → g y = v → f y' = u → g y' = v → y = y') →
      ∑ y : DSite n k, (if f y = u ∧ g y = v then (1 : ℝ) else 0) ≤ 1 := by
    intro f g u v hfg
    exact sum_ite_unique fun y y' hy hy' => hfg y y' hy.1 hy.2 hy'.1 hy'.2
  have ext' : ∀ y y' : DSite n k, (y.1 : ℕ) = y'.1 → (y.2 : ℕ) = y'.2 → y = y' :=
    fun y y' h1 h2 => Prod.ext (Fin.ext h1) (Fin.ext h2)
  have s1 : ∑ y : DSite n k, (if (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  have s2 : ∑ y : DSite n k, (if (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  have s3 : ∑ y : DSite n k, (if (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  have s4 : ∑ y : DSite n k, (if (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) ≤ 1 :=
    sum_ite_unique fun y y' hy hy' => ext' y y' (by omega) (by omega)
  calc ∑ y, Jsym n k x y ≤ ∑ y : DSite n k,
      ((if (y.1 : ℕ) = x.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (x.1 : ℕ) = y.1 + 1 ∧ (y.2 : ℕ) = x.2 then (1 : ℝ) else 0) +
      (if (y.2 : ℕ) = x.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0) +
      (if (x.2 : ℕ) = y.2 + 1 ∧ (y.1 : ℕ) = x.1 then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun y _ => hJ y
    _ ≤ 4 := by
        simp only [Finset.sum_add_distrib]
        linarith

/-- **Strong Gaussian domination for the quartic Dirichlet box (BFS Theorem 5.1), λ ≥ 0.**
For m₀ ≠ 0, λ ≥ 0, G of exponential-linear growth whose derivatives ∂_j G = G' j are of
exponential-linear growth and lie in the cone 𝒞 (e.g. G any polynomial with nonnegative
coefficients):
  ⟨φ_i G⟩ ≤ Σ_j ⟨∂_j G⟩ ⟨φ_i φ_j⟩,
⟨·⟩ the normalised quartic box measure (`twoPt` = ⟨φ_i φ_j⟩). For λ > 0 the contraction uses
the quartic term (any c'); for λ = 0 it uses α = 4 + ε²m₀² > 4 ≥ Σ_y J_xy (`Jsym_row_le`). -/
theorem strong_gaussian_domination_box {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    {G : DField n k → ℝ} {G' : DSite n k → DField n k → ℝ} (hG : Adm (fun _ => 1) G)
    (hG'a : ∀ j, Adm (fun _ => 1) (G' j))
    (hG' : ∀ j φ, HasLineDerivAt ℝ G (G' j φ) φ (Pi.single j 1))
    (hcone : ∀ j, InCone (G' j)) (i : DSite n k) :
    (∫ φ, φ i * G φ * qweight n k m₀ lam φ) / (∫ φ, qweight n k m₀ lam φ) ≤
      ∑ j, ((∫ φ, G' j φ * qweight n k m₀ lam φ) / ∫ φ, qweight n k m₀ lam φ) *
        twoPt n k m₀ lam i j := by
  have hrow4 : ∀ x : DSite n k, ∑ y, (Jnn n k x y + Jnn n k y x) ≤ 4 := Jsym_row_le
  rcases hlam.lt_or_eq with hpos | h0
  · have hbpos : 0 < betaQ n lam := by unfold betaQ; have := spacing_pos n; positivity
    exact sgd_box_of hm hlam (Or.inl hbpos) (c' := 5)
      (C₀ := (5 - alphaQ n m₀ lam) ^ 2 / (4 * betaQ n lam)) (by norm_num) (by norm_num) hrow4
      (fun t _ => fq_ge_lin hbpos 5 t) hG hG'a hG' hcone i
  · subst h0
    have hε := spacing_pos n
    have hα : alphaQ n m₀ 0 = 4 + spacing n ^ 2 * m₀ ^ 2 := by unfold alphaQ; ring
    have hα4 : 4 < alphaQ n m₀ 0 := by
      rw [hα]; have : 0 < spacing n ^ 2 * m₀ ^ 2 := by positivity
      linarith
    exact sgd_box_of hm le_rfl (Or.inr (by linarith)) (C₀ := 0) (by norm_num) hα4 hrow4
      (fun t _ => by unfold fq betaQ; simp) hG hG'a hG' hcone i

end PP2Target

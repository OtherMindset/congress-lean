import LongTable.Q_PP2SimonLieb2C
import LongTable.P_mwwgf25i_d0aeg1

/-!
Part A of PP2SimonLieb3 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb3.lean)
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

end PP2SGD

end

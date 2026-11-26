import LongTable.PP2Skeleton1
import LongTable.PP2Lebowitz

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, node M9 (non-Gaussianity),
skeleton-inequality route in local-time (Volterra) language, session 2. Lemmas L2, L4, L5 and the
milestone L6 (tree-level lower bound, BFS CMP 91 (1.3)) of the route review's plan.

Source: none read this session; builds on `PP2Skeleton1` (`Rop`, `Rop_spec`, `Rop_unique`,
`Rop_nonneg`, `Rop_add`, `Rop_const_mul`, `Rop_weight`, `Rop_split`, `tI_eq_Rop`, `sk1_tI_cls`),
`PP2SimonLieb3` (`tI`, `tI_mono`, `integrable_adm`, `tI_one_pos`, `Adm`, `InCone`) and
`PP2Lebowitz` (`lebowitz_ferro`, `lebowitzSite_quartic`).

CONVENTIONS. [F]_σ = ∫ F e^{Q_K} ∏_x e^{−f(φ_x²/2 + σ_x)}, f(u) = αu + βu² (`tI K α β σ F`);
for the box α = `alphaQ` (Wick-ordered, any sign), β = `betaQ` = 4λε² (the site weight
e^{−λε²φ⁴} is e^{−β(φ²/2)²}). Z(σ) = [1]_σ, A_cd(σ) = [φ_cφ_d]_σ, J = K + Kᵀ.

DEFINITIONS (namespace `PP2SGD`).
* `sk2_S K α β σ c d` = A_cd(σ)/Z(σ);  `sk2_u4 K α β σ i j k l` = [φ_iφ_jφ_kφ_l]_σ/Z(σ)
  − S_ij S_kl − S_ik S_jl − S_il S_jk;  `sk2_g K α β c d σ` = A_cd(σ) − S⁰_cd Z(σ)
  (= Z(σ)(S^σ_cd − S⁰_cd));  `sk2_J K` = K + Kᵀ;  `sk2_ray τ t` = tτ.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound). Standing hypotheses as in
`tI_eq_Rop`: K ≥ 0, β ≥ 0, (β > 0 ∨ α > 0), Adm Ψ integrable at σ = 0, row sums of J ≤ r < c',
f(t) ≥ c't − C₀ on [0, ∞).
* At every local time σ ≥ 0: Griffiths I `sk2_tI_two_nonneg` / `sk2_S_nonneg`, Griffiths II
  `sk2_A_le` (A_cd(σ) ≤ S⁰_cd Z(σ)) / `sk2_S_le`, and Lebowitz **`sk2_u4_nonpos`** (u₄^σ ≤ 0: the
  shifted site weights are e^{−(β/4 y⁴ + (α/2 + βσ_x) y² + const)}, `lebowitzSite_quartic`).
* Resolvent order/linearity: `sk2_Rop_congr` (only orthant values of the source matter),
  `sk2_Rop_zero`, `sk2_Rop_sum`, `sk2_Rop_mono`.
* (L2) `sk2_A_eq_Rop` (A_ab = Rop_ab[Z], G = φ_b in `tI_eq_Rop`), `sk2_M4_eq_Rop`
  ([φ_aφ_bφ_cφ_d] = Rop_ab[A_cd] + Rop_ac[A_bd] + Rop_ad[A_bc], G = φ_bφ_cφ_d), and
  **`u4_rep`**:  Z(0) u₄(a,b,c,d) = Rop_ab[g_cd](0) + Rop_ac[g_bd](0) + Rop_ad[g_bc](0)
  (weight c').
* (L4) `sk2_tI_ray_deriv` (differentiation under the integral, t > 0:
  d/dt [H]_{tτ} = −Σ_x τ_x((α + 2βtτ_x)[H]_{tτ} + β[Hφ_x²]_{tτ})), **`S_shift_deriv`**:
    d/dt S^{tτ}_cd = −β Σ_x τ_x (u₄^{tτ}(c,d,x,x) + 2 S^{tτ}_cx S^{tτ}_dx)   (t > 0),
  and **`S_shift_ftc`**: S^τ_cd − S⁰_cd = ∫₀¹ (that) dt. The plan's formula is correct as stated:
  f′(φ²/2 + τ) = α + 2βτ + βφ², and only βφ_z² survives in the ratio.
* (L5) **`S_shift_bound`**: 0 ≤ S⁰_cd − S^τ_cd ≤ 2β Σ_z τ_z S⁰_cz S⁰_dz (τ ≥ 0): Lebowitz and
  0 ≤ S^{tτ} ≤ S⁰ make t ↦ S^{tτ}_cd + 2βtΣ_zτ_zS⁰_czS⁰_dz monotone on [0,1]
  (`monotoneOn_of_deriv_nonneg`); `sk2_g_lower`: g_cd(σ) ≥ −2β Z(σ) Σ_z σ_z S⁰_cz S⁰_dz.
* (L6) `sk2_pair_bound` (weight c, r < c < c'): Rop_ab[g_cd](0) ≥ −2β Z(0) Σ_z S_az S_bz S_cz S_dz,
  via g ≥ h (L5), `sk2_Rop_mono`, `Rop_split` (Rop_ab[σ_z Z](0) = Rop_az[Rop_zb Z](0)),
  Rop_zb Z = A_zb ≤ S_zb Z and Rop_az Z = A_az = Z(0) S_az; and **`tree_bound`**:
    u₄(a,b,c,d) ≥ −6β Σ_z S_az S_bz S_cz S_dz      (S, u₄ at σ = 0).
* (box, namespace `PP2Target`) `sk2_box_ratio`, `sk2_box_S` (S⁰ = `twoPt`) and
  **`tree_bound_box`** (m₀ ≠ 0, λ ≥ 0): with u₄ the site Ursell function of `lebowitz_dexpect`
  (literally `lb2_U`),  u₄(a,b,c,d) ≥ −6·betaQ·Σ_z S_azS_bzS_czS_dz = −24λε² Σ_z S_azS_bzS_czS_dz.
  Constant: 6β = 24λε² = 4!·λε², the same coefficient as first-order perturbation theory.

NOT formalized: the passage from `tree_bound_box` to `UniformQuarticNegativity`. `tree_bound_box`
is a LOWER bound on u₄; M9 needs an UPPER bound u₄(f) ≤ −δ, i.e. the complementary skeleton
inequality (BFS's upper tree bound u₄ ≤ −c λ Σ_z S⁴ + higher order), or a different route.
Also not done: smearing (`lb2_u4_expand`), cutoff-uniform control of ε² Σ_z (Sf)(z)⁴, and the
sixth-moment bound (which `mo_newman6'` reduces to ⟨φ(f)²⟩).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2SGD

open PP2LocalTime PP2Griffiths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Part 0: definitions -/

/-- S^σ_cd = [φ_cφ_d]_σ / [1]_σ, the normalised two-point function at local time σ. -/
def sk2_S (K : ι → ι → ℝ) (α β : ℝ) (σ : ι → ℝ) (c d : ι) : ℝ :=
  tI K α β σ (fun φ => φ c * φ d) / tI K α β σ (fun _ => 1)

/-- u₄^σ(i,j,k,l) = [φ_iφ_jφ_kφ_l]_σ/[1]_σ − S_ij S_kl − S_ik S_jl − S_il S_jk. -/
def sk2_u4 (K : ι → ι → ℝ) (α β : ℝ) (σ : ι → ℝ) (i j k l : ι) : ℝ :=
  tI K α β σ (fun φ => φ i * φ j * φ k * φ l) / tI K α β σ (fun _ => 1)
    - sk2_S K α β σ i j * sk2_S K α β σ k l - sk2_S K α β σ i k * sk2_S K α β σ j l
    - sk2_S K α β σ i l * sk2_S K α β σ j k

/-- g_cd(σ) = Z(σ)(S^σ_cd − S⁰_cd) = [φ_cφ_d]_σ − S⁰_cd [1]_σ. -/
def sk2_g (K : ι → ι → ℝ) (α β : ℝ) (c d : ι) (σ : ι → ℝ) : ℝ :=
  tI K α β σ (fun φ => φ c * φ d) - sk2_S K α β 0 c d * tI K α β σ (fun _ => 1)

/-- The symmetrised pair matrix J = K + Kᵀ of the Volterra equation. -/
def sk2_J (K : ι → ι → ℝ) : ι → ι → ℝ := fun i k => K i k + K k i

lemma sk2_J_nonneg {K : ι → ι → ℝ} (hK : ∀ x y, 0 ≤ K x y) (i k : ι) : 0 ≤ sk2_J K i k :=
  add_nonneg (hK i k) (hK k i)

/-- The ray of local times t ↦ tτ. -/
def sk2_ray (τ : ι → ℝ) (t : ℝ) : ι → ℝ := fun x => t * τ x

lemma sk2_ray_mem {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) {t : ℝ} (ht : 0 ≤ t) :
    sk2_ray τ t ∈ sk1_orth := fun x => mul_nonneg ht (hτ x)

lemma sk2_ray_zero (τ : ι → ℝ) : sk2_ray τ 0 = 0 := funext fun _ => by simp [sk2_ray]

lemma sk2_ray_one (τ : ι → ℝ) : sk2_ray τ 1 = τ := funext fun _ => by simp [sk2_ray]

lemma sk2_continuous_ray (τ : ι → ℝ) : Continuous (sk2_ray τ) :=
  continuous_pi fun _ => continuous_id.mul continuous_const

lemma sk2_zero_mem : (0 : ι → ℝ) ∈ sk1_orth := fun _ => le_rfl

lemma sk2_S_symm (K : ι → ι → ℝ) (α β : ℝ) (σ : ι → ℝ) (c d : ι) :
    sk2_S K α β σ c d = sk2_S K α β σ d c := by
  unfold sk2_S; congr 2; funext φ; ring

/-! ## Part 1: admissible observables and linearity of [·]_σ -/

lemma sk2_adm_add {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ) {H₁ H₂ : (ι → ℝ) → ℝ}
    (h₁ : Adm Ψ H₁) (h₂ : Adm Ψ H₂) : Adm Ψ (fun φ => H₁ φ + H₂ φ) := by
  obtain ⟨hc₁, C₁, a₁, hb₁⟩ := h₁
  obtain ⟨hc₂, C₂, a₂, hb₂⟩ := h₂
  refine ⟨hc₁.add hc₂, |C₁| + |C₂|, |a₁| + |a₂|, fun φ => ?_⟩
  set S := ∑ x, |φ x| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => abs_nonneg _
  have hΨ0 : 0 ≤ Ψ φ := zero_le_one.trans (hΨ φ)
  have e₁ : Real.exp (a₁ * S) ≤ Real.exp ((|a₁| + |a₂|) * S) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      ((le_abs_self a₁).trans (le_add_of_nonneg_right (abs_nonneg a₂))) hS0)
  have e₂ : Real.exp (a₂ * S) ≤ Real.exp ((|a₁| + |a₂|) * S) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      ((le_abs_self a₂).trans (le_add_of_nonneg_left (abs_nonneg a₁))) hS0)
  have f₁ : C₁ * Real.exp (a₁ * S) * Ψ φ ≤ |C₁| * Real.exp ((|a₁| + |a₂|) * S) * Ψ φ :=
    mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (le_abs_self C₁)
      (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_left e₁ (abs_nonneg _))) hΨ0
  have f₂ : C₂ * Real.exp (a₂ * S) * Ψ φ ≤ |C₂| * Real.exp ((|a₁| + |a₂|) * S) * Ψ φ :=
    mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (le_abs_self C₂)
      (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_left e₂ (abs_nonneg _))) hΨ0
  calc |H₁ φ + H₂ φ| ≤ |H₁ φ| + |H₂ φ| := abs_add_le _ _
    _ ≤ C₁ * Real.exp (a₁ * S) * Ψ φ + C₂ * Real.exp (a₂ * S) * Ψ φ :=
        add_le_add (hb₁ φ) (hb₂ φ)
    _ ≤ _ := by nlinarith

lemma sk2_adm_const_mul {Ψ : (ι → ℝ) → ℝ} {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) (v : ℝ) :
    Adm Ψ (fun φ => v * H φ) := by
  obtain ⟨hc, C, a', hb⟩ := hH
  refine ⟨continuous_const.mul hc, |v| * C, a', fun φ => ?_⟩
  rw [abs_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hb φ).trans_eq (by ring)) (abs_nonneg v)

lemma sk2_adm2 {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ) (c d : ι) :
    Adm Ψ (fun φ => φ c * φ d) :=
  (Adm.coord hΨ d).mul_coord c

lemma sk2_adm_list {Ψ : (ι → ℝ) → ℝ} (hΨ : ∀ φ, 1 ≤ Ψ φ) (L : List ι) :
    Adm Ψ (fun φ => (L.map φ).prod) := by
  induction L with
  | nil => exact (Adm.const hΨ 1).congr fun φ => by simp
  | cons a L ih => exact (ih.mul_coord a).congr fun φ => by simp

lemma sk2_tI_add {K : ι → ι → ℝ} {α β : ℝ} {σ : ι → ℝ} {F G : (ι → ℝ) → ℝ}
    (hF : Integrable fun φ => F φ * Real.exp (quadE K φ) * tw α β σ φ)
    (hG : Integrable fun φ => G φ * Real.exp (quadE K φ) * tw α β σ φ) :
    tI K α β σ (fun φ => F φ + G φ) = tI K α β σ F + tI K α β σ G := by
  unfold tI
  rw [← integral_add hF hG]
  congr 1; funext φ; ring

lemma sk2_tI_const_mul (K : ι → ι → ℝ) (α β : ℝ) (σ : ι → ℝ) (v : ℝ) (F : (ι → ℝ) → ℝ) :
    tI K α β σ (fun φ => v * F φ) = v * tI K α β σ F := by
  unfold tI
  rw [← integral_const_mul]
  congr 1; funext φ; ring

/-! ## Part 2: Griffiths I, Griffiths II monotonicity and Lebowitz at every local time σ ≥ 0 -/

lemma sk2_tw_prod (α β : ℝ) (σ φ : ι → ℝ) : tw α β σ φ = ∏ x, siteW α β σ x (φ x) := by
  unfold tw siteW
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Griffiths I at local time σ (no integrability needed). -/
lemma sk2_tI_two_nonneg {K : ι → ι → ℝ} (hK : ∀ x y, 0 ≤ K x y) (α β : ℝ) (σ : ι → ℝ)
    (c d : ι) : 0 ≤ tI K α β σ (fun φ => φ c * φ d) := by
  have h := griffiths_first_sites_general (w := siteW α β σ)
    (fun x y => by simp only [siteW, neg_sq]) (fun x y => (Real.exp_pos _).le)
    ((IsPosPoly.coord c).mul (IsPosPoly.coord d)) (IsPosPoly.quadForm hK)
  unfold tI
  simp_rw [sk2_tw_prod]
  exact h

section Hyp

variable {K : ι → ι → ℝ} {α β : ℝ} {Ψ : (ι → ℝ) → ℝ}

lemma sk2_Z_pos (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {σ : ι → ℝ} (hσ : σ ∈ sk1_orth) : 0 < tI K α β σ (fun _ => 1) :=
  tI_one_pos (integrable_adm hb hint hσ (Adm.const hΨ 1))

lemma sk2_S_nonneg (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {σ : ι → ℝ} (hσ : σ ∈ sk1_orth) (c d : ι) :
    0 ≤ sk2_S K α β σ c d :=
  div_nonneg (sk2_tI_two_nonneg hK α β σ c d) (sk2_Z_pos hb hint hΨ hσ).le

/-- Griffiths II monotonicity (`tI_mono`): [φ_cφ_d]_σ ≤ S⁰_cd [1]_σ for σ ≥ 0. -/
lemma sk2_A_le (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {σ : ι → ℝ} (hσ : σ ∈ sk1_orth) (c d : ι) :
    tI K α β σ (fun φ => φ c * φ d) ≤ sk2_S K α β 0 c d * tI K α β σ (fun _ => 1) := by
  have h0 : (0 : ι → ℝ) ∈ sk1_orth := sk2_zero_mem
  have hH := sk2_adm2 hΨ c d
  have key := tI_mono hK hb (τ := 0) (τ' := σ) (fun x => hσ x)
    (InCone.of_isPosPoly ((IsPosPoly.coord c).mul (IsPosPoly.coord d)))
    (integrable_adm hb hint h0 hH) (integrable_adm hb hint h0 (Adm.const hΨ 1))
    (integrable_adm hb hint hσ hH) (integrable_adm hb hint hσ (Adm.const hΨ 1))
  have hZ0 := sk2_Z_pos hb hint hΨ h0
  unfold sk2_S
  rw [div_mul_eq_mul_div, le_div_iff₀ hZ0]
  exact key

lemma sk2_S_le (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {σ : ι → ℝ} (hσ : σ ∈ sk1_orth) (c d : ι) :
    sk2_S K α β σ c d ≤ sk2_S K α β 0 c d := by
  have hZ := sk2_Z_pos hb hint hΨ hσ
  have h := sk2_A_le hK hb hint hΨ hσ c d
  calc sk2_S K α β σ c d = tI K α β σ (fun φ => φ c * φ d) / tI K α β σ (fun _ => 1) := rfl
    _ ≤ sk2_S K α β 0 c d * tI K α β σ (fun _ => 1) / tI K α β σ (fun _ => 1) :=
        div_le_div_of_nonneg_right h hZ.le
    _ = _ := by field_simp

lemma sk2_ferro_eq (K : ι → ι → ℝ) (α β : ℝ) (σ φ : ι → ℝ) :
    PP2Griffiths.ferroDensity (siteW α β σ) K φ = Real.exp (quadE K φ) * tw α β σ φ := by
  rw [rhoQ_siteW]; rfl

lemma sk2_lebowitzSite (hb : 0 ≤ β) (σ : ι → ℝ) (x : ι) :
    PP2Lebowitz.LebowitzSite (siteW α β σ x) := by
  have h : siteW α β σ x = fun y => Real.exp (-(β / 4 * y ^ 4 + (α / 2 + β * σ x) * y ^ 2
      + (α * σ x + β * σ x ^ 2))) := by
    funext y; unfold siteW fq; congr 1; ring
  rw [h]
  exact PP2Lebowitz.lebowitzSite_quartic (by positivity) _ _

/-- **Lebowitz at every local time σ ≥ 0**: u₄^σ ≤ 0 (the site weights e^{−f(y²/2 + σ_x)} are
e^{−(β/4 y⁴ + b y² + d)} with β/4 ≥ 0, `lebowitzSite_quartic`). -/
lemma sk2_u4_nonpos (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {σ : ι → ℝ} (hσ : σ ∈ sk1_orth) (i j k l : ι) :
    sk2_u4 K α β σ i j k l ≤ 0 := by
  have hint' : ∀ L : List ι, Integrable fun φ =>
      (L.map φ).prod * PP2Griffiths.ferroDensity (siteW α β σ) K φ := by
    intro L
    refine (integrable_adm hb hint hσ (sk2_adm_list hΨ L)).congr
      (Filter.Eventually.of_forall fun φ => ?_)
    simp only [sk2_ferro_eq]; ring
  have h := PP2Lebowitz.lebowitz_ferro (w := siteW α β σ)
    (fun x y => by simp only [siteW, neg_sq]) (fun x y => (Real.exp_pos _).le)
    (sk2_lebowitzSite hb σ) hK hint' i j k l
  have e : ∀ F : (ι → ℝ) → ℝ, PP2Lebowitz.expect (PP2Griffiths.ferroDensity (siteW α β σ) K) F
      = tI K α β σ F / tI K α β σ (fun _ => 1) := by
    intro F
    unfold PP2Lebowitz.expect tI
    simp only [sk2_ferro_eq, one_mul, mul_assoc]
  unfold PP2Lebowitz.ursell4 at h
  simp only [e] at h
  exact h

end Hyp

/-! ## Part 3: order and linearity properties of the resolvent -/

section RopLemmas

variable {J : ι → ι → ℝ} {r c : ℝ}

/-- Rop depends only on the values of the source on the orthant. -/
lemma sk2_Rop_congr (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g g' : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (hg' : sk1_Cls c g')
    (heq : ∀ σ ∈ sk1_orth, g σ = g' σ) (a b : ι) :
    ∀ τ ∈ sk1_orth, Rop J c a b g τ = Rop J c a b g' τ := by
  have hs := Rop_spec hJ hc hr0 hrc hrow hg b
  have h := Rop_unique hJ hc hr0 hrc hrow hg' b (D := fun a => Rop J c a b g) hs.1
    (fun a τ hτ => by
      rw [hs.2 a τ hτ]
      refine setIntegral_congr_fun measurableSet_Ioi fun s hs' => ?_
      rw [heq _ (sk1_line_mem hτ a (le_of_lt hs'))])
  intro τ hτ
  exact (h a τ hτ).symm

lemma sk2_Rop_zero (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) (a b : ι) :
    ∀ τ ∈ sk1_orth, Rop J c a b (fun _ => 0) τ = 0 := by
  have h := Rop_unique hJ hc hr0 hrc hrow (sk1_Cls.zero c) b (D := fun _ _ => 0)
    (fun _ => sk1_Cls.zero c) (fun a τ _ => by simp)
  exact fun τ hτ => h a τ hτ

lemma sk2_Rop_sum (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {κ : Type*} (s : Finset κ) {g : κ → (ι → ℝ) → ℝ}
    (hg : ∀ z ∈ s, sk1_Cls c (g z)) (a b : ι) :
    ∀ τ ∈ sk1_orth, Rop J c a b (fun σ => ∑ z ∈ s, g z σ) τ = ∑ z ∈ s, Rop J c a b (g z) τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sk2_Rop_zero hJ hc hr0 hrc hrow a b
  | insert y s hy ih =>
    intro τ hτ
    have hcls : sk1_Cls c (fun σ => ∑ z ∈ s, g z σ) :=
      sk1_Cls.sum s fun z hz => hg z (Finset.mem_insert_of_mem hz)
    have h := Rop_add hJ hc hr0 hrc hrow (hg y (Finset.mem_insert_self y s)) hcls a b τ hτ
    simp only [Finset.sum_insert hy]
    rw [h, ih (fun z hz => hg z (Finset.mem_insert_of_mem hz)) τ hτ]

/-- Rop is monotone in the source (on the orthant). -/
lemma sk2_Rop_mono (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g g' : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (hg' : sk1_Cls c g')
    (hle : ∀ σ ∈ sk1_orth, g σ ≤ g' σ) (a b : ι) :
    ∀ τ ∈ sk1_orth, Rop J c a b g τ ≤ Rop J c a b g' τ := by
  intro τ hτ
  have hm : sk1_Cls c (fun σ => -1 * g σ) := hg.const_mul (-1)
  have h0 := Rop_nonneg hJ hc hr0 hrc hrow (hg'.add hm)
    (fun σ hσ => by have := hle σ hσ; show 0 ≤ g' σ + -1 * g σ; linarith) a b τ hτ
  have h1 := Rop_add hJ hc hr0 hrc hrow hg' hm a b τ hτ
  have h2 := Rop_const_mul hJ hc hr0 hrc hrow hg (-1) a b τ hτ
  rw [h1, h2] at h0
  linarith

end RopLemmas

/-! ## Part 4 (L2): the four-point function as resolvents of the two-point increments -/

lemma sk2_sum_single (b : ι) (F : ι → ℝ) :
    ∑ x, (Pi.single x (1 : ℝ) : ι → ℝ) b * F x = F b := by
  simp [Pi.single_apply]

lemma sk2_hasLineDeriv_three (b c d x : ι) (φ : ι → ℝ) :
    HasLineDerivAt ℝ (fun ψ : ι → ℝ => ψ b * ψ c * ψ d)
      ((Pi.single x (1 : ℝ) : ι → ℝ) b * (φ c * φ d) +
        (Pi.single x (1 : ℝ) : ι → ℝ) c * (φ b * φ d) +
        (Pi.single x (1 : ℝ) : ι → ℝ) d * (φ b * φ c)) φ (Pi.single x 1) := by
  have hb := hasLineDerivAt_coord x b φ
  have hc := hasLineDerivAt_coord x c φ
  have hd := hasLineDerivAt_coord x d φ
  unfold HasLineDerivAt at *
  have h := (hb.mul hc).mul hd
  convert h using 1
  simp only [Pi.mul_apply, zero_smul, add_zero]
  ring

section L2

variable {K : ι → ι → ℝ} {α β : ℝ} {Ψ : (ι → ℝ) → ℝ}

/-- A_ab = Rop_ab[Z] on the orthant (`tI_eq_Rop` with G = φ_b). -/
theorem sk2_A_eq_Rop (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β) (hab : 0 < β ∨ 0 < α)
    (hΨ : ∀ φ, 1 ≤ Ψ φ)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c') (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t) (a b : ι) :
    ∀ τ ∈ sk1_orth, tI K α β τ (fun φ => φ a * φ b) =
      Rop (sk2_J K) c' a b (fun σ => tI K α β σ (fun _ => 1)) τ := by
  intro τ hτ
  have hc' : 0 < c' := lt_of_le_of_lt hr0 hrc
  have hJ : ∀ i k, 0 ≤ sk2_J K i k := sk2_J_nonneg hK
  have hZ : sk1_Cls c' (fun σ => tI K α β σ (fun _ => 1)) :=
    sk1_tI_cls hb hint hc' hf (Adm.const hΨ 1)
  have h : tI K α β τ (fun φ => φ a * φ b) = ∑ x, Rop (sk2_J K) c' a x
      (fun σ => tI K α β σ (fun _ => (Pi.single x (1 : ℝ) : ι → ℝ) b)) τ :=
    tI_eq_Rop hK hb hab hint hr0 hrc hrow hf (G := fun φ => φ b)
      (G' := fun x _ => (Pi.single x (1 : ℝ) : ι → ℝ) b) (Adm.coord hΨ b)
      (fun x => Adm.const hΨ _) (fun x φ => hasLineDerivAt_coord x b φ) a hτ
  rw [h]
  have e : ∀ x, Rop (sk2_J K) c' a x
      (fun σ => tI K α β σ (fun _ => (Pi.single x (1 : ℝ) : ι → ℝ) b)) τ =
      (Pi.single x (1 : ℝ) : ι → ℝ) b *
        Rop (sk2_J K) c' a x (fun σ => tI K α β σ (fun _ => 1)) τ := by
    intro x
    have h1 : (fun σ => tI K α β σ (fun _ => (Pi.single x (1 : ℝ) : ι → ℝ) b)) =
        fun σ => (Pi.single x (1 : ℝ) : ι → ℝ) b * tI K α β σ (fun _ => 1) :=
      funext fun σ => tI_const K α β σ _
    rw [h1]
    exact Rop_const_mul hJ hc' hr0 hrc hrow hZ _ a x τ hτ
  simp only [e]
  exact sk2_sum_single b (fun x => Rop (sk2_J K) c' a x
    (fun σ => tI K α β σ (fun _ => 1)) τ)

/-- [φ_aφ_bφ_cφ_d]_τ = Rop_ab[A_cd] + Rop_ac[A_bd] + Rop_ad[A_bc] on the orthant
(`tI_eq_Rop` with G = φ_bφ_cφ_d). -/
theorem sk2_M4_eq_Rop (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β) (hab : 0 < β ∨ 0 < α)
    (hΨ : ∀ φ, 1 ≤ Ψ φ)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c') (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t) (a b c d : ι) :
    ∀ τ ∈ sk1_orth, tI K α β τ (fun φ => φ a * φ b * φ c * φ d) =
      Rop (sk2_J K) c' a b (fun σ => tI K α β σ (fun φ => φ c * φ d)) τ +
      Rop (sk2_J K) c' a c (fun σ => tI K α β σ (fun φ => φ b * φ d)) τ +
      Rop (sk2_J K) c' a d (fun σ => tI K α β σ (fun φ => φ b * φ c)) τ := by
  intro τ hτ
  have hc' : 0 < c' := lt_of_le_of_lt hr0 hrc
  have hJ : ∀ i k, 0 ≤ sk2_J K i k := sk2_J_nonneg hK
  set δ : ι → ι → ℝ := fun x y => (Pi.single x (1 : ℝ) : ι → ℝ) y with hδ
  set G' : ι → (ι → ℝ) → ℝ := fun x φ =>
    δ x b * (φ c * φ d) + δ x c * (φ b * φ d) + δ x d * (φ b * φ c) with hG'
  have hA : ∀ u v, sk1_Cls c' (fun σ => tI K α β σ (fun φ => φ u * φ v)) :=
    fun u v => sk1_tI_cls hb hint hc' hf (sk2_adm2 hΨ u v)
  have hG'a : ∀ x, Adm Ψ (G' x) := fun x =>
    sk2_adm_add hΨ (sk2_adm_add hΨ (sk2_adm_const_mul (sk2_adm2 hΨ c d) _)
      (sk2_adm_const_mul (sk2_adm2 hΨ b d) _)) (sk2_adm_const_mul (sk2_adm2 hΨ b c) _)
  have hG : Adm Ψ (fun φ => φ b * φ c * φ d) :=
    ((sk2_adm2 hΨ c d).mul_coord b).congr fun φ => by ring
  have h : tI K α β τ (fun φ => φ a * (φ b * φ c * φ d)) =
      ∑ x, Rop (sk2_J K) c' a x (fun σ => tI K α β σ (G' x)) τ :=
    tI_eq_Rop hK hb hab hint hr0 hrc hrow hf (G := fun φ => φ b * φ c * φ d)
      (G' := G') hG hG'a (fun x φ => sk2_hasLineDeriv_three b c d x φ) a hτ
  have elhs : tI K α β τ (fun φ => φ a * φ b * φ c * φ d) =
      tI K α β τ (fun φ => φ a * (φ b * φ c * φ d)) := by
    congr 1; funext φ; ring
  rw [elhs, h]
  -- linearity of [·]_σ in the source, on the orthant
  have hsrc : ∀ x, ∀ σ ∈ sk1_orth, tI K α β σ (G' x) =
      δ x b * tI K α β σ (fun φ => φ c * φ d) + δ x c * tI K α β σ (fun φ => φ b * φ d) +
        δ x d * tI K α β σ (fun φ => φ b * φ c) := by
    intro x σ hσ
    have i1 := integrable_adm hb hint hσ (sk2_adm_const_mul (sk2_adm2 hΨ c d) (δ x b))
    have i2 := integrable_adm hb hint hσ (sk2_adm_const_mul (sk2_adm2 hΨ b d) (δ x c))
    have i3 := integrable_adm hb hint hσ (sk2_adm_const_mul (sk2_adm2 hΨ b c) (δ x d))
    have e1 : tI K α β σ (G' x) = tI K α β σ (fun φ => (δ x b * (φ c * φ d) +
        δ x c * (φ b * φ d)) + δ x d * (φ b * φ c)) := rfl
    rw [e1, sk2_tI_add (F := fun φ => δ x b * (φ c * φ d) + δ x c * (φ b * φ d))
        (G := fun φ => δ x d * (φ b * φ c)) (i1.add i2 |>.congr
          (Filter.Eventually.of_forall fun φ => by simp only [Pi.add_apply]; ring)) i3,
      sk2_tI_add (F := fun φ => δ x b * (φ c * φ d)) (G := fun φ => δ x c * (φ b * φ d)) i1 i2,
      sk2_tI_const_mul, sk2_tI_const_mul, sk2_tI_const_mul]
  have hcls3 : ∀ x, sk1_Cls c' (fun σ =>
      δ x b * tI K α β σ (fun φ => φ c * φ d) + δ x c * tI K α β σ (fun φ => φ b * φ d) +
        δ x d * tI K α β σ (fun φ => φ b * φ c)) := fun x =>
    (((hA c d).const_mul _).add ((hA b d).const_mul _)).add ((hA b c).const_mul _)
  have hterm : ∀ x, Rop (sk2_J K) c' a x (fun σ => tI K α β σ (G' x)) τ =
      δ x b * Rop (sk2_J K) c' a x (fun σ => tI K α β σ (fun φ => φ c * φ d)) τ +
      δ x c * Rop (sk2_J K) c' a x (fun σ => tI K α β σ (fun φ => φ b * φ d)) τ +
      δ x d * Rop (sk2_J K) c' a x (fun σ => tI K α β σ (fun φ => φ b * φ c)) τ := by
    intro x
    rw [sk2_Rop_congr hJ hc' hr0 hrc hrow (sk1_tI_cls hb hint hc' hf (hG'a x)) (hcls3 x)
      (hsrc x) a x τ hτ]
    have s1 := Rop_add hJ hc' hr0 hrc hrow (((hA c d).const_mul (δ x b)).add
      ((hA b d).const_mul (δ x c))) ((hA b c).const_mul (δ x d)) a x τ hτ
    have s2 := Rop_add hJ hc' hr0 hrc hrow ((hA c d).const_mul (δ x b))
      ((hA b d).const_mul (δ x c)) a x τ hτ
    rw [s1, s2, Rop_const_mul hJ hc' hr0 hrc hrow (hA c d) _ a x τ hτ,
      Rop_const_mul hJ hc' hr0 hrc hrow (hA b d) _ a x τ hτ,
      Rop_const_mul hJ hc' hr0 hrc hrow (hA b c) _ a x τ hτ]
  simp only [hterm, Finset.sum_add_distrib, hδ]
  rw [sk2_sum_single b (fun x => Rop (sk2_J K) c' a x (fun σ => tI K α β σ (fun φ => φ c * φ d)) τ),
    sk2_sum_single c (fun x => Rop (sk2_J K) c' a x (fun σ => tI K α β σ (fun φ => φ b * φ d)) τ),
    sk2_sum_single d (fun x => Rop (sk2_J K) c' a x (fun σ => tI K α β σ (fun φ => φ b * φ c)) τ)]

lemma sk2_g_cls (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {c' C₀ : ℝ} (hc' : 0 < c') (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t)
    (c d : ι) : sk1_Cls c' (sk2_g K α β c d) :=
  ((sk1_tI_cls hb hint hc' hf (sk2_adm2 hΨ c d)).add
    ((sk1_tI_cls hb hint hc' hf (Adm.const hΨ 1)).const_mul (-sk2_S K α β 0 c d))).congr
    fun σ _ => by unfold sk2_g; ring

/-- **L2 (`u4_rep`).** With Z = [1], J = K + Kᵀ, g_cd(τ) = [φ_cφ_d]_τ − S⁰_cd [1]_τ
(= Z(τ)(S^τ_cd − S⁰_cd)):
  Z(0) · u₄(a,b,c,d) = Rop_ab[g_cd](0) + Rop_ac[g_bd](0) + Rop_ad[g_bc](0). -/
theorem u4_rep (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β) (hab : 0 < β ∨ 0 < α)
    (hΨ : ∀ φ, 1 ≤ Ψ φ)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c') (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t) (a b c d : ι) :
    tI K α β 0 (fun _ => 1) * sk2_u4 K α β 0 a b c d =
      Rop (sk2_J K) c' a b (sk2_g K α β c d) 0 +
      Rop (sk2_J K) c' a c (sk2_g K α β b d) 0 +
      Rop (sk2_J K) c' a d (sk2_g K α β b c) 0 := by
  have hc' : 0 < c' := lt_of_le_of_lt hr0 hrc
  have hJ : ∀ i k, 0 ≤ sk2_J K i k := sk2_J_nonneg hK
  have h0 : (0 : ι → ℝ) ∈ sk1_orth := sk2_zero_mem
  have hZc : sk1_Cls c' (fun σ => tI K α β σ (fun _ => 1)) :=
    sk1_tI_cls hb hint hc' hf (Adm.const hΨ 1)
  have hA : ∀ u v, sk1_Cls c' (fun σ => tI K α β σ (fun φ => φ u * φ v)) :=
    fun u v => sk1_tI_cls hb hint hc' hf (sk2_adm2 hΨ u v)
  have hg : ∀ (x y u v : ι), Rop (sk2_J K) c' x y (sk2_g K α β u v) 0 =
      Rop (sk2_J K) c' x y (fun σ => tI K α β σ (fun φ => φ u * φ v)) 0 -
        sk2_S K α β 0 u v * tI K α β 0 (fun φ => φ x * φ y) := by
    intro x y u v
    have e : sk2_g K α β u v = fun σ => tI K α β σ (fun φ => φ u * φ v) +
        (-sk2_S K α β 0 u v) * tI K α β σ (fun _ => 1) := funext fun σ => by unfold sk2_g; ring
    have s1 := Rop_add hJ hc' hr0 hrc hrow (hA u v) (hZc.const_mul (-sk2_S K α β 0 u v)) x y 0 h0
    rw [e, s1, Rop_const_mul hJ hc' hr0 hrc hrow hZc _ x y 0 h0,
      ← sk2_A_eq_Rop hK hb hab hΨ hint hr0 hrc hrow hf x y 0 h0]
    ring
  rw [hg, hg, hg]
  have hM := sk2_M4_eq_Rop hK hb hab hΨ hint hr0 hrc hrow hf a b c d 0 h0
  have hZ0 := (sk2_Z_pos hb hint hΨ h0 (K := K) (α := α)).ne'
  unfold sk2_u4 sk2_S
  rw [hM]
  field_simp
  ring

end L2

/-! ## Part 5 (L4): the derivative of S along the ray τ ↦ tτ -/

lemma sk2_tw_ray_deriv (α β : ℝ) (τ φ : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => tw α β (sk2_ray τ t) φ)
      (∑ x, -τ x * ((α + 2 * β * (t * τ x)) * tw α β (sk2_ray τ t) φ +
        β * (φ x * φ x) * tw α β (sk2_ray τ t) φ)) t := by
  have h : ∀ x ∈ (Finset.univ : Finset ι), HasDerivAt
      (fun t => fq α β (φ x ^ 2 / 2 + t * τ x))
      (fq' α β (φ x ^ 2 / 2 + t * τ x) * (1 * τ x)) t := fun x _ =>
    (hasDerivAt_fq α β _).comp t (((hasDerivAt_id t).mul_const (τ x)).const_add _)
  have h2 := (HasDerivAt.fun_sum h).fun_neg.exp
  unfold tw sk2_ray
  convert h2 using 1
  rw [mul_neg, Finset.mul_sum, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun x _ => by unfold fq'; ring

lemma sk2_exp_fq_le {α β : ℝ} (hb : 0 ≤ β) {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) {t T : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    Real.exp (-∑ x, fq α β (sk2_ray τ t x)) ≤ Real.exp (|α| * (T * ∑ x, τ x)) := by
  apply Real.exp_le_exp.mpr
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  unfold fq sk2_ray
  have h1 : 0 ≤ t * τ x := mul_nonneg ht (hτ x)
  have h2 : t * τ x ≤ T * τ x := mul_le_mul_of_nonneg_right htT (hτ x)
  have h3 := mul_le_mul_of_nonneg_right (neg_le_abs α) h1
  have h4 := mul_le_mul_of_nonneg_left h2 (abs_nonneg α)
  have h5 := mul_nonneg hb (sq_nonneg (t * τ x))
  nlinarith

lemma sk2_norm_tw_le {K : ι → ι → ℝ} {α β : ℝ} (hb : 0 ≤ β) {σ : ι → ℝ} (hσ : σ ∈ sk1_orth)
    (G : (ι → ℝ) → ℝ) (φ : ι → ℝ) :
    ‖G φ * Real.exp (quadE K φ) * tw α β σ φ‖ ≤
      Real.exp (-∑ x, fq α β (σ x)) * ‖G φ * Real.exp (quadE K φ) * tw α β 0 φ‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos α β σ φ), abs_of_pos (tw_pos α β 0 φ)]
  have h1 := tw_le_tw_zero (a := α) hb (fun x => hσ x) φ
  calc |G φ| * Real.exp (quadE K φ) * tw α β σ φ ≤
      |G φ| * Real.exp (quadE K φ) * (Real.exp (-∑ x, fq α β (σ x)) * tw α β 0 φ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

section Deriv

variable {K : ι → ι → ℝ} {α β : ℝ} {Ψ : (ι → ℝ) → ℝ}

/-- Differentiation of t ↦ [H]_{tτ} under the integral sign (t > 0):
  d/dt [H]_{tτ} = −Σ_x τ_x ((α + 2βtτ_x)[H]_{tτ} + β[H φ_x²]_{tτ}). -/
theorem sk2_tI_ray_deriv (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t => tI K α β (sk2_ray τ t) H)
      (∑ x, -τ x * ((α + 2 * β * (t₀ * τ x)) * tI K α β (sk2_ray τ t₀) H +
        β * tI K α β (sk2_ray τ t₀) (fun φ => H φ * (φ x * φ x)))) t₀ := by
  have hHc := hH.1
  have hHx : ∀ x, Adm Ψ (fun φ => H φ * (φ x * φ x)) := fun x =>
    ((hH.mul_coord x).mul_coord x).congr fun φ => by ring
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (|α| * (2 * t₀ * ∑ x, τ x)) := ⟨_, rfl⟩
  have hs : Ioo 0 (2 * t₀) ∈ 𝓝 t₀ := Ioo_mem_nhds ht₀ (by linarith)
  have hI : ∀ t, 0 ≤ t → ∀ G, Adm Ψ G →
      Integrable fun φ => G φ * Real.exp (quadE K φ) * tw α β (sk2_ray τ t) φ :=
    fun t ht G hG => integrable_adm hb hint (sk2_ray_mem hτ ht) hG
  have hF'int : ∀ t, 0 ≤ t → Integrable fun φ => ∑ x, -τ x * ((α + 2 * β * (t * τ x)) *
      (H φ * Real.exp (quadE K φ) * tw α β (sk2_ray τ t) φ) +
      β * (H φ * (φ x * φ x) * Real.exp (quadE K φ) * tw α β (sk2_ray τ t) φ)) :=
    fun t ht => integrable_finsetSum _ fun x _ =>
      ((((hI t ht H hH).const_mul _).add ((hI t ht _ (hHx x)).const_mul _)).const_mul _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun t φ => H φ * Real.exp (quadE K φ) * tw α β (sk2_ray τ t) φ)
    (F' := fun t φ => ∑ x, -τ x * ((α + 2 * β * (t * τ x)) *
      (H φ * Real.exp (quadE K φ) * tw α β (sk2_ray τ t) φ) +
      β * (H φ * (φ x * φ x) * Real.exp (quadE K φ) * tw α β (sk2_ray τ t) φ)))
    (bound := fun φ => ∑ x, τ x * ((|α| + 2 * β * (2 * t₀ * τ x)) *
      (E * ‖H φ * Real.exp (quadE K φ) * tw α β 0 φ‖) +
      β * (E * ‖H φ * (φ x * φ x) * Real.exp (quadE K φ) * tw α β 0 φ‖))) hs
    (Filter.eventually_of_mem hs fun t ht => (hI t ht.1.le H hH).aestronglyMeasurable)
    (hI t₀ ht₀.le H hH) (hF'int t₀ ht₀.le).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ t ht => ?_)
    (integrable_finsetSum _ fun x _ => (((((hint H hH).norm.const_mul E).const_mul _).add
      (((hint _ (hHx x)).norm.const_mul E).const_mul _)).const_mul _))
    (Filter.Eventually.of_forall fun φ t _ => ?_)
  · have e : ∫ φ, (∑ x, -τ x * ((α + 2 * β * (t₀ * τ x)) *
        (H φ * Real.exp (quadE K φ) * tw α β (sk2_ray τ t₀) φ) +
        β * (H φ * (φ x * φ x) * Real.exp (quadE K φ) * tw α β (sk2_ray τ t₀) φ))) =
        ∑ x, -τ x * ((α + 2 * β * (t₀ * τ x)) * tI K α β (sk2_ray τ t₀) H +
          β * tI K α β (sk2_ray τ t₀) (fun φ => H φ * (φ x * φ x))) := by
      have hx : ∀ x ∈ (Finset.univ : Finset ι), Integrable fun φ =>
          -τ x * ((α + 2 * β * (t₀ * τ x)) *
          (H φ * Real.exp (quadE K φ) * tw α β (sk2_ray τ t₀) φ) +
          β * (H φ * (φ x * φ x) * Real.exp (quadE K φ) * tw α β (sk2_ray τ t₀) φ)) :=
        fun x _ => ((((hI t₀ ht₀.le H hH).const_mul _).add
          ((hI t₀ ht₀.le _ (hHx x)).const_mul _)).const_mul _)
      rw [integral_finsetSum _ hx]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_const_mul, integral_add ((hI t₀ ht₀.le H hH).const_mul _)
        ((hI t₀ ht₀.le _ (hHx x)).const_mul _), integral_const_mul, integral_const_mul]
      rfl
    have k2 := key.2
    beta_reduce at k2
    rw [e] at k2
    exact k2
  · -- the domination
    have ht0 : 0 ≤ t := ht.1.le
    have hσ := sk2_ray_mem hτ ht0
    have hEle : Real.exp (-∑ x, fq α β (sk2_ray τ t x)) ≤ E :=
      hE ▸ sk2_exp_fq_le hb hτ ht0 ht.2.le
    have n1 : ∀ G : (ι → ℝ) → ℝ, ‖G φ * Real.exp (quadE K φ) * tw α β (sk2_ray τ t) φ‖ ≤
        E * ‖G φ * Real.exp (quadE K φ) * tw α β 0 φ‖ := fun G =>
      (sk2_norm_tw_le hb hσ G φ).trans (mul_le_mul_of_nonneg_right hEle (norm_nonneg _))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    have hτx := hτ x
    have hc : |α + 2 * β * (t * τ x)| ≤ |α| + 2 * β * (2 * t₀ * τ x) := by
      refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
      have hp : 0 ≤ 2 * β * (t * τ x) := mul_nonneg (by linarith) (mul_nonneg ht0 hτx)
      rw [abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht.2.le hτx) (by linarith)
    rw [norm_mul, norm_neg, Real.norm_of_nonneg hτx]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hτx
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul hc (n1 H) (norm_nonneg _) ((abs_nonneg _).trans hc)
    · rw [norm_mul, Real.norm_of_nonneg hb]
      exact mul_le_mul_of_nonneg_left (n1 (fun φ => H φ * (φ x * φ x))) hb
  · -- the pointwise derivative
    have h := (sk2_tw_ray_deriv α β τ φ t).const_mul (H φ * Real.exp (quadE K φ))
    convert h using 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- **L4 (derivative form).** Along the ray, for t₀ > 0 and σ₀ = t₀τ:
  d/dt S^{tτ}_cd |_{t₀} = −β Σ_x τ_x (u₄^{σ₀}(c,d,x,x) + 2 S^{σ₀}_cx S^{σ₀}_dx).
(The φ-independent part α + 2βtτ_x of f′ cancels in the ratio; only β φ_x² survives.) -/
theorem S_shift_deriv (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) (c d : ι) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t => sk2_S K α β (sk2_ray τ t) c d)
      (-β * ∑ x, τ x * (sk2_u4 K α β (sk2_ray τ t₀) c d x x +
        2 * (sk2_S K α β (sk2_ray τ t₀) c x * sk2_S K α β (sk2_ray τ t₀) d x))) t₀ := by
  have hA := sk2_tI_ray_deriv (K := K) hb hint hτ (sk2_adm2 hΨ c d) ht₀
  have hZ := sk2_tI_ray_deriv (K := K) hb hint hτ (Adm.const hΨ 1) ht₀
  have hZ0 := (sk2_Z_pos hb hint hΨ (sk2_ray_mem hτ ht₀.le) (K := K)).ne'
  have h := hA.fun_div hZ hZ0
  have e1 : ∀ x, tI K α β (sk2_ray τ t₀) (fun φ => 1 * (φ x * φ x)) =
      tI K α β (sk2_ray τ t₀) (fun φ => φ x * φ x) := fun x => by simp only [one_mul]
  have e2 : ∀ x, tI K α β (sk2_ray τ t₀) (fun φ => φ c * φ d * (φ x * φ x)) =
      tI K α β (sk2_ray τ t₀) (fun φ => φ c * φ d * φ x * φ x) := fun x => by
    simp only [mul_assoc]
  simp only [e1, e2] at h
  show HasDerivAt (fun t => tI K α β (sk2_ray τ t) (fun φ => φ c * φ d) /
    tI K α β (sk2_ray τ t) (fun _ => 1)) _ t₀
  convert h using 1
  unfold sk2_u4 sk2_S
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  field_simp
  ring

end Deriv

/-! ## Part 6 (L5): the two-sided bound on the two-point increment -/

section L5

variable {K : ι → ι → ℝ} {α β : ℝ} {Ψ : (ι → ℝ) → ℝ}

/-- **L5.** For τ ≥ 0:  0 ≤ S⁰_cd − S^τ_cd ≤ 2β Σ_z τ_z S⁰_cz S⁰_dz.
Lower bound: Griffiths II (`tI_mono`). Upper bound: along the ray, by `S_shift_deriv`,
d/dt S^{tτ}_cd = −β Σ_z τ_z (u₄^{tτ}(c,d,z,z) + 2 S^{tτ}_cz S^{tτ}_dz) ≥ −2β Σ_z τ_z S⁰_cz S⁰_dz,
using u₄^{tτ} ≤ 0 (Lebowitz at the shifted weights) and 0 ≤ S^{tτ} ≤ S⁰ (Griffiths I, II); then
the mean value theorem (`monotoneOn_of_deriv_nonneg`) on [0, 1]. -/
theorem S_shift_bound (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {c' C₀ : ℝ} (hc' : 0 < c') (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t)
    {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) (c d : ι) :
    0 ≤ sk2_S K α β 0 c d - sk2_S K α β τ c d ∧
      sk2_S K α β 0 c d - sk2_S K α β τ c d ≤
        2 * β * ∑ z, τ z * (sk2_S K α β 0 c z * sk2_S K α β 0 d z) := by
  refine ⟨sub_nonneg.mpr (sk2_S_le hK hb hint hΨ hτ c d), ?_⟩
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * β * ∑ z, τ z * (sk2_S K α β 0 c z * sk2_S K α β 0 d z) :=
    ⟨_, rfl⟩
  rw [← hD]
  have hderiv : ∀ t, 0 < t → HasDerivAt (fun t => sk2_S K α β (sk2_ray τ t) c d + t * D)
      (-β * ∑ x, τ x * (sk2_u4 K α β (sk2_ray τ t) c d x x +
        2 * (sk2_S K α β (sk2_ray τ t) c x * sk2_S K α β (sk2_ray τ t) d x)) + D) t :=
    fun t ht => (S_shift_deriv hb hint hΨ hτ c d ht).fun_add (hasDerivAt_mul_const D)
  have hcl : ∀ H, Adm Ψ H → ContinuousOn (fun t => tI K α β (sk2_ray τ t) H) (Icc 0 1) :=
    fun H hH => (sk1_tI_cls hb hint hc' hf hH).1.comp (sk2_continuous_ray τ).continuousOn
      fun t ht => sk2_ray_mem hτ ht.1
  have hcont : ContinuousOn (fun t => sk2_S K α β (sk2_ray τ t) c d + t * D) (Icc 0 1) :=
    ((hcl _ (sk2_adm2 hΨ c d)).div (hcl _ (Adm.const hΨ 1)) fun t ht =>
      (sk2_Z_pos hb hint hΨ (sk2_ray_mem hτ ht.1)).ne').add (continuousOn_id.mul continuousOn_const)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1) hcont
    (fun t ht => by
      rw [interior_Icc] at ht
      exact (hderiv t ht.1).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hderiv t ht.1).deriv]
      have hσ := sk2_ray_mem hτ ht.1.le
      have e : -β * ∑ x, τ x * (sk2_u4 K α β (sk2_ray τ t) c d x x +
          2 * (sk2_S K α β (sk2_ray τ t) c x * sk2_S K α β (sk2_ray τ t) d x)) + D =
          ∑ x, (β * τ x * (-sk2_u4 K α β (sk2_ray τ t) c d x x) + 2 * β * τ x *
            (sk2_S K α β 0 c x * sk2_S K α β 0 d x -
              sk2_S K α β (sk2_ray τ t) c x * sk2_S K α β (sk2_ray τ t) d x)) := by
        rw [hD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [e]
      refine Finset.sum_nonneg fun x _ => add_nonneg ?_ ?_
      · exact mul_nonneg (mul_nonneg hb (hτ x))
          (neg_nonneg.mpr (sk2_u4_nonpos hK hb hint hΨ hσ c d x x))
      · refine mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hb) (hτ x)) (sub_nonneg.mpr ?_)
        exact mul_le_mul (sk2_S_le hK hb hint hΨ hσ c x) (sk2_S_le hK hb hint hΨ hσ d x)
          (sk2_S_nonneg hK hb hint hΨ hσ d x) (sk2_S_nonneg hK hb hint hΨ sk2_zero_mem c x))
  have h01 := hmono (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [sk2_ray_zero, sk2_ray_one, zero_mul, add_zero, one_mul] at h01
  linarith


lemma sk2_contOn_ray (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    {c' C₀ : ℝ} (hc' : 0 < c') (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t)
    {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) :
    ContinuousOn (fun t => tI K α β (sk2_ray τ t) H) (Icc 0 1) :=
  (sk1_tI_cls hb hint hc' hf hH).1.comp (sk2_continuous_ray τ).continuousOn
    fun _ ht => sk2_ray_mem hτ ht.1

/-- **L4 (`S_shift_ftc`, integral form).** For τ ≥ 0:
  S^τ_cd − S⁰_cd = ∫₀¹ −β Σ_x τ_x (u₄^{tτ}(c,d,x,x) + 2 S^{tτ}_cx S^{tτ}_dx) dt. -/
theorem S_shift_ftc (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {c' C₀ : ℝ} (hc' : 0 < c') (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t)
    {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) (c d : ι) :
    sk2_S K α β τ c d - sk2_S K α β 0 c d =
      ∫ t in (0 : ℝ)..1, -β * ∑ x, τ x * (sk2_u4 K α β (sk2_ray τ t) c d x x +
        2 * (sk2_S K α β (sk2_ray τ t) c x * sk2_S K α β (sk2_ray τ t) d x)) := by
  have hZne : ∀ t ∈ Icc (0 : ℝ) 1, tI K α β (sk2_ray τ t) (fun _ => 1) ≠ 0 := fun t ht =>
    (sk2_Z_pos hb hint hΨ (sk2_ray_mem hτ ht.1)).ne'
  have hS : ∀ u v, ContinuousOn (fun t => sk2_S K α β (sk2_ray τ t) u v) (Icc 0 1) :=
    fun u v => (sk2_contOn_ray hb hint hc' hf hτ (sk2_adm2 hΨ u v)).div
      (sk2_contOn_ray hb hint hc' hf hτ (Adm.const hΨ 1)) hZne
  have hu : ∀ x, ContinuousOn (fun t => sk2_u4 K α β (sk2_ray τ t) c d x x) (Icc 0 1) := by
    intro x
    have h4 : Adm Ψ (fun φ => φ c * φ d * φ x * φ x) :=
      (((sk2_adm2 hΨ c d).mul_coord x).mul_coord x).congr fun φ => by ring
    exact ((((sk2_contOn_ray hb hint hc' hf hτ h4).div
      (sk2_contOn_ray hb hint hc' hf hτ (Adm.const hΨ 1)) hZne).sub
      ((hS c d).mul (hS x x))).sub ((hS c x).mul (hS d x))).sub ((hS c x).mul (hS d x))
  have hd : ContinuousOn (fun t => -β * ∑ x, τ x * (sk2_u4 K α β (sk2_ray τ t) c d x x +
      2 * (sk2_S K α β (sk2_ray τ t) c x * sk2_S K α β (sk2_ray τ t) d x))) (Icc 0 1) :=
    continuousOn_const.mul (continuousOn_finsetSum _ fun x _ => continuousOn_const.mul
      ((hu x).add (continuousOn_const.mul ((hS c x).mul (hS d x)))))
  have hii : IntervalIntegrable (fun t => -β * ∑ x, τ x * (sk2_u4 K α β (sk2_ray τ t) c d x x +
      2 * (sk2_S K α β (sk2_ray τ t) c x * sk2_S K α β (sk2_ray τ t) d x))) volume 0 1 :=
    hd.intervalIntegrable_of_Icc zero_le_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (hS c d)
    (fun t ht => S_shift_deriv hb hint hΨ hτ c d ht.1) hii]
  simp only [sk2_ray_zero, sk2_ray_one]

/-- L5, consequence: g_cd(σ) ≥ −2β [1]_σ Σ_z σ_z S⁰_cz S⁰_dz on the orthant. -/
theorem sk2_g_lower (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    (hΨ : ∀ φ, 1 ≤ Ψ φ) {c' C₀ : ℝ} (hc' : 0 < c') (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t)
    {σ : ι → ℝ} (hσ : σ ∈ sk1_orth) (c d : ι) :
    -(tI K α β σ (fun _ => 1) * (2 * β * ∑ z, σ z * (sk2_S K α β 0 c z * sk2_S K α β 0 d z)))
      ≤ sk2_g K α β c d σ := by
  have hL5 := (S_shift_bound hK hb hint hΨ hc' hf hσ c d).2
  have hZ := sk2_Z_pos hb hint hΨ hσ (K := K) (α := α)
  have hA : sk2_S K α β σ c d * tI K α β σ (fun _ => 1) = tI K α β σ (fun φ => φ c * φ d) :=
    div_mul_cancel₀ _ hZ.ne'
  have h1 := mul_le_mul_of_nonneg_left hL5 hZ.le
  unfold sk2_g
  nlinarith

end L5

/-! ## Part 7 (L6): the tree-level lower bound -/

section L6

variable {K : ι → ι → ℝ} {α β : ℝ} {Ψ : (ι → ℝ) → ℝ}

/-- One pairing: for r < c < c',
  Rop_ab[g_cd](0) ≥ −2β Σ_z S_az S_bz S_cz S_dz · Z(0)   (weight c).
Proof: g_cd ≥ h := −2β Σ_z S_cz S_dz σ_z Z(σ) (L5) and Rop is monotone; Rop_ab[σ_z Z](0) =
Rop_az[Rop_zb Z](0) (`Rop_split`) = Rop_az[A_zb](0) ≤ S_zb Rop_az[Z](0) = S_zb Z(0) S_az
(Griffiths II: A_zb ≤ S_zb Z, and A = Rop[Z]). -/
theorem sk2_pair_bound (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β) (hab : 0 < β ∨ 0 < α)
    (hΨ : ∀ φ, 1 ≤ Ψ φ)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    {r c c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c) (hcc : c < c')
    (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t) (a b c₁ d : ι) :
    -(2 * β * ∑ z, sk2_S K α β 0 a z * sk2_S K α β 0 b z * sk2_S K α β 0 c₁ z *
        sk2_S K α β 0 d z) * tI K α β 0 (fun _ => 1) ≤
      Rop (sk2_J K) c a b (sk2_g K α β c₁ d) 0 := by
  have hc : 0 < c := lt_of_le_of_lt hr0 hrc
  have hc' : 0 < c' := hc.trans hcc
  have hrc' : r < c' := hrc.trans hcc
  have hJ : ∀ i k, 0 ≤ sk2_J K i k := sk2_J_nonneg hK
  have hrowJ : ∀ i, ∑ k, sk2_J K i k ≤ r := hrow
  have h0 : (0 : ι → ℝ) ∈ sk1_orth := sk2_zero_mem
  have hZc : sk1_Cls c' (fun σ => tI K α β σ (fun _ => 1)) :=
    sk1_tI_cls hb hint hc' hf (Adm.const hΨ 1)
  have hAc : ∀ u v, sk1_Cls c' (fun σ => tI K α β σ (fun φ => φ u * φ v)) :=
    fun u v => sk1_tI_cls hb hint hc' hf (sk2_adm2 hΨ u v)
  obtain ⟨coef, hcoef⟩ : ∃ coef : ι → ℝ,
      coef = fun z => -(2 * β * (sk2_S K α β 0 c₁ z * sk2_S K α β 0 d z)) := ⟨_, rfl⟩
  have hcz : ∀ z, sk1_Cls c (fun σ => (σ z - (0 : ι → ℝ) z) * tI K α β σ (fun _ => 1)) :=
    fun z => hZc.mul_coord hcc z _
  have hhc : sk1_Cls c (fun σ => ∑ z, coef z * ((σ z - (0 : ι → ℝ) z) *
      tI K α β σ (fun _ => 1))) :=
    sk1_Cls.sum _ fun z _ => (hcz z).const_mul (coef z)
  have hgc : sk1_Cls c (sk2_g K α β c₁ d) := (sk2_g_cls hb hint hΨ hc' hf c₁ d).mono hcc.le
  -- h ≤ g on the orthant (L5)
  have hle : ∀ σ ∈ sk1_orth, (∑ z, coef z * ((σ z - (0 : ι → ℝ) z) *
      tI K α β σ (fun _ => 1))) ≤ sk2_g K α β c₁ d σ := by
    intro σ hσ
    refine le_of_eq_of_le ?_ (sk2_g_lower hK hb hint hΨ hc' hf hσ c₁ d)
    rw [hcoef, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by simp only [Pi.zero_apply, sub_zero]; ring
  have hmono := sk2_Rop_mono hJ hc hr0 hrc hrowJ hhc hgc hle a b 0 h0
  rw [sk2_Rop_sum hJ hc hr0 hrc hrowJ Finset.univ (fun z _ => (hcz z).const_mul (coef z))
    a b 0 h0] at hmono
  refine le_trans ?_ hmono
  -- each term
  have hterm : ∀ z, coef z * (sk2_S K α β 0 z b * (tI K α β 0 (fun _ => 1) *
      sk2_S K α β 0 a z)) ≤ Rop (sk2_J K) c a b (fun σ => coef z * ((σ z - (0 : ι → ℝ) z) *
        tI K α β σ (fun _ => 1))) 0 := by
    intro z
    rw [Rop_const_mul hJ hc hr0 hrc hrowJ (hcz z) (coef z) a b 0 h0,
      Rop_split hJ hr0 hrc hcc hrowJ hZc a b z h0]
    have hcoef0 : coef z ≤ 0 := by
      rw [hcoef]
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg zero_le_two hb)
        (mul_nonneg (sk2_S_nonneg hK hb hint hΨ h0 c₁ z) (sk2_S_nonneg hK hb hint hΨ h0 d z)))
    refine mul_le_mul_of_nonpos_left ?_ hcoef0
    -- Rop_az[Rop_zb Z](0) ≤ S_zb Z(0) S_az
    have e1 : ∀ σ ∈ sk1_orth, Rop (sk2_J K) c z b (fun σ => tI K α β σ (fun _ => 1)) σ =
        tI K α β σ (fun φ => φ z * φ b) := fun σ hσ =>
      (Rop_weight hJ hc hr0 hrc hrowJ hcc.le hZc z b σ hσ).trans
        (sk2_A_eq_Rop hK hb hab hΨ hint hr0 hrc' hrow hf z b σ hσ).symm
    rw [sk2_Rop_congr hJ hc hr0 hrc hrowJ
      ((Rop_spec hJ hc hr0 hrc hrowJ (hZc.mono hcc.le) b).1 z) ((hAc z b).mono hcc.le) e1 a z 0 h0]
    refine (sk2_Rop_mono hJ hc hr0 hrc hrowJ ((hAc z b).mono hcc.le)
      ((hZc.const_mul (sk2_S K α β 0 z b)).mono hcc.le)
      (fun σ hσ => sk2_A_le hK hb hint hΨ hσ z b) a z 0 h0).trans (le_of_eq ?_)
    rw [Rop_const_mul hJ hc hr0 hrc hrowJ (hZc.mono hcc.le) _ a z 0 h0,
      Rop_weight hJ hc hr0 hrc hrowJ hcc.le hZc a z 0 h0,
      ← sk2_A_eq_Rop hK hb hab hΨ hint hr0 hrc' hrow hf a z 0 h0]
    have hZ0 := (sk2_Z_pos hb hint hΨ h0 (K := K) (α := α)).ne'
    unfold sk2_S
    field_simp
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun z _ => hterm z)
  rw [hcoef, neg_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sk2_S_symm K α β 0 z b]
  ring

/-- **L6 (`tree_bound`; BFS CMP 91 (1.3) in local-time form).** For K ≥ 0, f(u) = αu + βu²
(β ≥ 0, β > 0 or α > 0), the admissible class integrable at τ = 0, row sums of K + Kᵀ ≤ r < c'
and f(t) ≥ c't − C₀ on [0, ∞):
  u₄(a,b,c,d) ≥ −6β Σ_z S_az S_bz S_cz S_dz,
S, u₄ the normalised two-point and Ursell functions of [·]_0. -/
theorem tree_bound (hK : ∀ x y, 0 ≤ K x y) (hb : 0 ≤ β) (hab : 0 < β ∨ 0 < α)
    (hΨ : ∀ φ, 1 ≤ Ψ φ)
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw α β 0 φ)
    {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c') (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq α β t) (a b c d : ι) :
    -(6 * β * ∑ z, sk2_S K α β 0 a z * sk2_S K α β 0 b z * sk2_S K α β 0 c z *
        sk2_S K α β 0 d z) ≤ sk2_u4 K α β 0 a b c d := by
  set cw := (r + c') / 2 with hcw
  have hrw : r < cw := by rw [hcw]; linarith
  have hwc : cw < c' := by rw [hcw]; linarith
  have hcw0 : 0 < cw := lt_of_le_of_lt hr0 hrw
  have hc' : 0 < c' := hcw0.trans hwc
  have hJ : ∀ i k, 0 ≤ sk2_J K i k := sk2_J_nonneg hK
  have hrowJ : ∀ i, ∑ k, sk2_J K i k ≤ r := hrow
  have h0 : (0 : ι → ℝ) ∈ sk1_orth := sk2_zero_mem
  have hrep := u4_rep hK hb hab hΨ hint hr0 hrc hrow hf a b c d
  have hw : ∀ x y u v, Rop (sk2_J K) c' x y (sk2_g K α β u v) 0 =
      Rop (sk2_J K) cw x y (sk2_g K α β u v) 0 := fun x y u v =>
    (Rop_weight hJ hcw0 hr0 hrw hrowJ hwc.le (sk2_g_cls hb hint hΨ hc' hf u v) x y 0 h0).symm
  rw [hw, hw, hw] at hrep
  have p1 := sk2_pair_bound hK hb hab hΨ hint hr0 hrw hwc hrow hf a b c d
  have p2 := sk2_pair_bound hK hb hab hΨ hint hr0 hrw hwc hrow hf a c b d
  have p3 := sk2_pair_bound hK hb hab hΨ hint hr0 hrw hwc hrow hf a d b c
  have hZ0 := sk2_Z_pos hb hint hΨ h0 (K := K) (α := α)
  set T := ∑ z, sk2_S K α β 0 a z * sk2_S K α β 0 b z * sk2_S K α β 0 c z * sk2_S K α β 0 d z
    with hT
  have s2 : ∑ z, sk2_S K α β 0 a z * sk2_S K α β 0 c z * sk2_S K α β 0 b z *
      sk2_S K α β 0 d z = T := Finset.sum_congr rfl fun z _ => by ring
  have s3 : ∑ z, sk2_S K α β 0 a z * sk2_S K α β 0 d z * sk2_S K α β 0 b z *
      sk2_S K α β 0 c z = T := Finset.sum_congr rfl fun z _ => by ring
  rw [s2] at p2
  rw [s3] at p3
  have key : tI K α β 0 (fun _ => 1) * (-(6 * β * T)) ≤
      tI K α β 0 (fun _ => 1) * sk2_u4 K α β 0 a b c d := by
    rw [hrep]; nlinarith
  exact le_of_mul_le_mul_left key hZ0

end L6

end PP2SGD

/-! ## Part 8: the quartic Dirichlet box -/

namespace PP2Target

open PP2LocalTime PP2Griffiths PP2SGD

variable {n k : ℕ}

/-- At τ = 0, ratios of [·]_0 are expectations of the normalised quartic box measure. -/
lemma sk2_box_ratio (m₀ lam : ℝ) (F : DField n k → ℝ) :
    tI (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 F /
      tI (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun _ => 1) = dexpect n k m₀ lam F := by
  rw [← tauInt_eq_tI, ← tauInt_eq_tI, tauInt_zero, tauInt_zero,
    mul_div_mul_left _ _ (Real.exp_pos _).ne']
  simp only [one_mul]
  rfl

lemma sk2_box_S (m₀ lam : ℝ) (x y : DSite n k) :
    sk2_S (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 x y = twoPt n k m₀ lam x y :=
  sk2_box_ratio m₀ lam _

/-- **The tree-level lower bound for the quartic Dirichlet box** (m₀ ≠ 0, λ ≥ 0; β = 4λε²):
  u₄(a,b,c,d) ≥ −6β Σ_z S_az S_bz S_cz S_dz = −24λε² Σ_z S_az S_bz S_cz S_dz,
S = `twoPt`, u₄ the site Ursell function of `lebowitz_dexpect` (= `lb2_U` of `PP2Lebowitz2`).
Together with `lebowitz_dexpect`: −24λε² Σ_z S⁴ ≤ u₄ ≤ 0. -/
theorem tree_bound_box {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (a b c d : DSite n k) :
    -(6 * betaQ n lam * ∑ z, twoPt n k m₀ lam a z * twoPt n k m₀ lam b z *
        twoPt n k m₀ lam c z * twoPt n k m₀ lam d z) ≤
      dexpect n k m₀ lam (fun φ => φ a * φ b * φ c * φ d)
      - dexpect n k m₀ lam (fun φ => φ a * φ b) * dexpect n k m₀ lam (fun φ => φ c * φ d)
      - dexpect n k m₀ lam (fun φ => φ a * φ c) * dexpect n k m₀ lam (fun φ => φ b * φ d)
      - dexpect n k m₀ lam (fun φ => φ a * φ d) * dexpect n k m₀ lam (fun φ => φ b * φ c) := by
  have hb := betaQ_nonneg (n := n) hlam
  have hrow4 : ∀ x : DSite n k, ∑ y, (Jnn n k x y + Jnn n k y x) ≤ 4 := Jsym_row_le
  have hmain : -(6 * betaQ n lam * ∑ z,
      sk2_S (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 a z *
      sk2_S (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 b z *
      sk2_S (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 c z *
      sk2_S (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 d z) ≤
      sk2_u4 (Jnn n k) (alphaQ n m₀ lam) (betaQ n lam) 0 a b c d := by
    rcases hlam.lt_or_eq with hpos | h0
    · have hbpos : 0 < betaQ n lam := by unfold betaQ; have := spacing_pos n; positivity
      exact tree_bound Jnn_nonneg hb (Or.inl hbpos) (Ψ := fun _ => 1) (fun _ => le_refl 1)
        (hint_box hm hlam) (c' := 5) (C₀ := (5 - alphaQ n m₀ lam) ^ 2 / (4 * betaQ n lam))
        (by norm_num) (by norm_num) hrow4 (fun t _ => fq_ge_lin hbpos 5 t) a b c d
    · subst h0
      have hα : alphaQ n m₀ 0 = 4 + spacing n ^ 2 * m₀ ^ 2 := by unfold alphaQ; ring
      have hα4 : 4 < alphaQ n m₀ 0 := by
        rw [hα]; have : 0 < spacing n ^ 2 * m₀ ^ 2 := by have := spacing_pos n; positivity
        linarith
      exact tree_bound Jnn_nonneg hb (Or.inr (by linarith)) (Ψ := fun _ => 1)
        (fun _ => le_refl 1) (hint_box hm hlam) (C₀ := 0) (by norm_num) hα4 hrow4
        (fun t _ => by unfold fq betaQ; simp) a b c d
  unfold sk2_u4 at hmain
  simp only [sk2_box_S, sk2_box_ratio] at hmain
  exact hmain

end PP2Target


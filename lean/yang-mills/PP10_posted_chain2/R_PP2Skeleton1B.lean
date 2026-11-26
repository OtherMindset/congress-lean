import LongTable.R_PP2Skeleton1A

/-!
Part B of PP2Skeleton1 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Skeleton1.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound). Standing hypotheses:
J ≥ 0, row sums Σ_k J_ik ≤ r, 0 ≤ r < c.
* `RopV J c h` (general source vector; chosen solution) and **`Rop J c a b g = RopV J c (δ_b g) a`**,
  i.e. D_a(τ) = ∫_0^∞ (δ_ab g(τ + s e_a) + Σ_j J_aj D_j(τ + s e_a)) ds.
* (L0, existence) `sk1_exists`: Banach fixed point (`ContractingWith.fixedPoint`) on
  ι → C_b((ι → ℝ), ℝ) in the weighted variables u = e^{cΣτ}D, operator
  (Tu)_i(τ) = e^{cΣPτ}∫ g_i(Pτ + se_i) ds + Σ_j J_ij ∫ e^{−cs} u_j(τ + se_i) ds (P = clamp onto the
  orthant), Lipschitz constant r/c; continuity of T u by dominated convergence.
* (L0) `RopV_spec`, `RopV_eq`, **`Rop_spec`** (class + equation), **`Rop_unique`** (any solution
  in the class is Rop, via `volterra_nonneg` for ± the difference, `sk1_Sol.unique`),
  **`Rop_nonneg`** (g ≥ 0 ⟹ Rop g ≥ 0), **`Rop_add`**, **`Rop_const_mul`**, `RopV_eq_sum`
  (RopV h = Σ_x Rop · x (h x)), `Rop_weight` (Rop J c = Rop J c' on the orthant, c ≤ c').

NOT formalized: the later lemmas of the route review's plan (L2, L4, ...).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

open scoped BoundedContinuousFunction

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2SGD

open PP2LocalTime PP2Griffiths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sk1_U_cont (c : ℝ) (u : (ι → ℝ) →ᵇ ℝ) (i : ι) (τ : ι → ℝ) :
    Continuous fun s : ℝ => Real.exp (-c * s) * u (τ + Pi.single i s) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (u.continuous.comp (sk1_continuous_line τ i))

lemma sk1_U_int {c : ℝ} (hc : 0 < c) (u : (ι → ℝ) →ᵇ ℝ) (i : ι) (τ : ι → ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * s) * u (τ + Pi.single i s)) (Ioi 0) :=
  ((exp_neg_integrableOn_Ioi 0 hc).const_mul ‖u‖).mono'
    (sk1_U_cont c u i τ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => sk1_U_pt c u i τ s)

lemma continuous_sk1_U {c : ℝ} (hc : 0 < c) (u : (ι → ℝ) →ᵇ ℝ) (i : ι) :
    Continuous (sk1_U c u i) := by
  refine continuous_of_dominated (bound := fun s => ‖u‖ * Real.exp (-c * s))
    (fun τ => (sk1_U_cont c u i τ).aestronglyMeasurable)
    (fun τ => Filter.Eventually.of_forall fun s => sk1_U_pt c u i τ s)
    ((exp_neg_integrableOn_Ioi 0 hc).const_mul ‖u‖)
    (Filter.Eventually.of_forall fun s => ?_)
  exact continuous_const.mul (u.continuous.comp (continuous_id.add continuous_const))

lemma sk1_int_exp {c : ℝ} (hc : 0 < c) : ∫ s in Ioi (0 : ℝ), Real.exp (-c * s) = 1 / c := by
  rw [integral_exp_mul_Ioi (by linarith : -c < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

lemma sk1_U_le {c : ℝ} (hc : 0 < c) (u : (ι → ℝ) →ᵇ ℝ) (i : ι) (τ : ι → ℝ) :
    ‖sk1_U c u i τ‖ ≤ ‖u‖ / c := by
  refine (norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hc).const_mul ‖u‖)
    (Filter.Eventually.of_forall fun s => sk1_U_pt c u i τ s)).trans_eq ?_
  rw [integral_const_mul, sk1_int_exp hc]; ring

lemma sk1_U_sub {c : ℝ} (hc : 0 < c) (u v : (ι → ℝ) →ᵇ ℝ) (i : ι) (τ : ι → ℝ) :
    sk1_U c u i τ - sk1_U c v i τ = sk1_U c ⇑(u - v) i τ := by
  unfold sk1_U
  rw [← integral_sub (sk1_U_int hc u i τ) (sk1_U_int hc v i τ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  ring

/-- **Existence** of a solution of the Volterra equation in the weighted class (Banach fixed
point on ι → C_b, in the variables u = e^{cΣτ} D; contraction constant r/c). -/
theorem sk1_exists {J : ι → ι → ℝ} (hJ : ∀ i k, 0 ≤ J i k) {r c : ℝ} (hc : 0 < c)
    (hr0 : 0 ≤ r) (hrc : r < c) (hrow : ∀ i, ∑ k, J i k ≤ r) {h : ι → (ι → ℝ) → ℝ}
    (hh : ∀ i, sk1_Cls c (h i)) : ∃ D, sk1_Sol J c h D := by
  choose CH hCH using fun i => sk1_H_le hc (hh i) i
  let T : (ι → (ι → ℝ) →ᵇ ℝ) → (ι → (ι → ℝ) →ᵇ ℝ) := fun u i =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun τ => sk1_H c (h i) i τ + ∑ j, J i j * sk1_U c (u j) i τ)
      ((continuous_sk1_H hc (hh i) i).add (continuous_finsetSum _ fun j _ =>
        continuous_const.mul (continuous_sk1_U hc (u j) i)))
      (CH i + ∑ j, |J i j| * (‖u j‖ / c))
      (fun τ => by
        refine (norm_add_le _ _).trans (add_le_add (hCH i τ) ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (sk1_U_le hc (u j) i τ) (abs_nonneg _))
  have hT : ∀ u i τ, T u i τ = sk1_H c (h i) i τ + ∑ j, J i j * sk1_U c (u j) i τ :=
    fun u i τ => rfl
  have hq0 : 0 ≤ r / c := div_nonneg hr0 hc.le
  have hK : ContractingWith (Real.toNNReal (r / c)) T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    · rw [Real.toNNReal_lt_one]; exact (div_lt_one hc).mpr hrc
    · rw [Real.coe_toNNReal _ hq0]
      have hd0 : 0 ≤ dist u v := dist_nonneg
      refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
      refine (BoundedContinuousFunction.dist_le (by positivity)).mpr fun τ => ?_
      rw [hT, hT, Real.dist_eq]
      have e : (sk1_H c (h i) i τ + ∑ j, J i j * sk1_U c (u j) i τ) -
          (sk1_H c (h i) i τ + ∑ j, J i j * sk1_U c (v j) i τ) =
          ∑ j, J i j * sk1_U c ⇑(u j - v j) i τ := by
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [← mul_sub, sk1_U_sub hc]
      rw [e]
      calc |∑ j, J i j * sk1_U c ⇑(u j - v j) i τ| ≤
          ∑ j, |J i j * sk1_U c ⇑(u j - v j) i τ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, J i j * (dist u v / c) := Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_nonneg (hJ i j)]
            refine mul_le_mul_of_nonneg_left ?_ (hJ i j)
            have h1 := sk1_U_le hc (u j - v j) i τ
            rw [Real.norm_eq_abs] at h1
            refine h1.trans (div_le_div_of_nonneg_right ?_ hc.le)
            rw [← dist_eq_norm]; exact dist_le_pi_dist u v j
        _ = (∑ j, J i j) * (dist u v / c) := by rw [Finset.sum_mul]
        _ ≤ r * (dist u v / c) := mul_le_mul_of_nonneg_right (hrow i) (by positivity)
        _ = r / c * dist u v := by ring
  set u := ContractingWith.fixedPoint T hK with hu
  have hfix : T u = u := ContractingWith.fixedPoint_isFixedPt hK
  set D : ι → (ι → ℝ) → ℝ := fun i τ => Real.exp (-(c * ∑ x, τ x)) * u i τ with hDdef
  have hDc : ∀ i, sk1_Cls c (D i) := by
    intro i
    refine ⟨((Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ fun x _ => continuous_apply x)).neg).mul
        (u i).continuous).continuousOn, ‖u i‖, fun τ _ => ?_⟩
    simp only [D]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using (u i).norm_coe_le_norm τ)
      (Real.exp_pos _).le
  refine ⟨D, hDc, fun i τ hτ => ?_⟩
  have e1 : sk1_H c (h i) i τ =
      Real.exp (c * ∑ x, τ x) * ∫ s in Ioi (0 : ℝ), h i (τ + Pi.single i s) := by
    unfold sk1_H; rw [sk1_P_of_mem hτ, integral_const_mul]
  have e2 : ∀ j, Real.exp (-(c * ∑ x, τ x)) * sk1_U c (u j) i τ =
      ∫ s in Ioi (0 : ℝ), D j (τ + Pi.single i s) := by
    intro j; unfold sk1_U; rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [D]; rw [sk1_exp_line]; ring
  have hui : u i τ = T u i τ := by rw [hfix]
  calc D i τ = Real.exp (-(c * ∑ x, τ x)) *
        (sk1_H c (h i) i τ + ∑ j, J i j * sk1_U c (u j) i τ) := by
        simp only [D]; rw [hui, hT]
    _ = (∫ s in Ioi (0 : ℝ), h i (τ + Pi.single i s)) +
        ∑ j, J i j * ∫ s in Ioi (0 : ℝ), D j (τ + Pi.single i s) := by
        rw [mul_add, Finset.mul_sum Finset.univ (fun j => J i j * sk1_U c (u j) i τ), e1,
          ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [← e2 j]; ring
    _ = _ := by
        rw [integral_add (sk1_intOn hc (hh i) hτ i) (integrable_finsetSum _ fun j _ =>
          (sk1_intOn hc (hDc j) hτ i).const_mul _),
          integral_finsetSum _ fun j _ => (sk1_intOn hc (hDc j) hτ i).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

/-! ## The resolvent `Rop` -/

open Classical in
/-- The Volterra resolvent with source vector h: the solution of `sk1_Sol` in the class c
(chosen; it is unique on the orthant by `sk1_Sol.unique` and exists by `sk1_exists`). -/
def RopV (J : ι → ι → ℝ) (c : ℝ) (h : ι → (ι → ℝ) → ℝ) : ι → (ι → ℝ) → ℝ :=
  if hs : ∃ D, sk1_Sol J c h D then Classical.choose hs else 0

/-- **L0.** (Rop J c a b g)(τ) = D_a(τ), D the solution of
D_a(τ) = ∫_0^∞ (δ_ab g(τ + s e_a) + Σ_j J_aj D_j(τ + s e_a)) ds in the weighted class c. -/
def Rop (J : ι → ι → ℝ) (c : ℝ) (a b : ι) (g : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  RopV J c (Pi.single b g) a

lemma sk1_single_apply (b i : ι) (g : (ι → ℝ) → ℝ) (σ : ι → ℝ) :
    (Pi.single b g : ι → (ι → ℝ) → ℝ) i σ = if i = b then g σ else 0 := by
  by_cases h : i = b
  · subst h; simp
  · simp [h]

lemma sk1_single_cls {c : ℝ} {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (b i : ι) :
    sk1_Cls c ((Pi.single b g : ι → (ι → ℝ) → ℝ) i) := by
  by_cases h : i = b
  · subst h; simpa using hg
  · rw [Pi.single_eq_of_ne h]; exact sk1_Cls.zero c

section Resolvent

variable {J : ι → ι → ℝ} {r c : ℝ}

theorem RopV_spec (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {h : ι → (ι → ℝ) → ℝ} (hh : ∀ i, sk1_Cls c (h i)) :
    sk1_Sol J c h (RopV J c h) := by
  have hs := sk1_exists hJ hc hr0 hrc hrow hh
  unfold RopV
  split
  · exact Classical.choose_spec ‹_›
  · contradiction

theorem RopV_eq (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {h D : ι → (ι → ℝ) → ℝ} (hh : ∀ i, sk1_Cls c (h i))
    (hD : sk1_Sol J c h D) : ∀ i, ∀ τ ∈ sk1_orth, RopV J c h i τ = D i τ :=
  sk1_Sol.unique hJ hc hr0 hrc hrow hh (RopV_spec hJ hc hr0 hrc hrow hh) hD

/-- **L0, the defining equation.** Rop · b g lies in the class c and solves the Volterra equation
with source δ_ab g. -/
theorem Rop_spec (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (b : ι) :
    (∀ a, sk1_Cls c (Rop J c a b g)) ∧ ∀ a, ∀ τ ∈ sk1_orth, Rop J c a b g τ =
      ∫ s in Ioi (0 : ℝ), ((if a = b then g (τ + Pi.single a s) else 0) +
        ∑ j, J a j * Rop J c j b g (τ + Pi.single a s)) := by
  obtain ⟨h1, h2⟩ := RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls hg b)
  refine ⟨h1, fun a τ hτ => ?_⟩
  rw [Rop, h2 a τ hτ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [sk1_single_apply, Rop]

/-- **L0, uniqueness.** Any solution in the class c is Rop. -/
theorem Rop_unique (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (b : ι)
    {D : ι → (ι → ℝ) → ℝ} (hDc : ∀ a, sk1_Cls c (D a))
    (hD : ∀ a, ∀ τ ∈ sk1_orth, D a τ = ∫ s in Ioi (0 : ℝ),
      ((if a = b then g (τ + Pi.single a s) else 0) + ∑ j, J a j * D j (τ + Pi.single a s))) :
    ∀ a, ∀ τ ∈ sk1_orth, Rop J c a b g τ = D a τ := by
  refine RopV_eq hJ hc hr0 hrc hrow (sk1_single_cls hg b) ⟨hDc, fun a τ hτ => ?_⟩
  rw [hD a τ hτ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [sk1_single_apply]

/-- **L0, positivity.** g ≥ 0 on the orthant ⟹ Rop g ≥ 0 there. -/
theorem Rop_nonneg (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g)
    (hg0 : ∀ σ ∈ sk1_orth, 0 ≤ g σ) (a b : ι) : ∀ τ ∈ sk1_orth, 0 ≤ Rop J c a b g τ :=
  sk1_Sol.nonneg hJ hc hr0 hrc hrow (RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls hg b))
    (fun i σ hσ => by rw [sk1_single_apply]; split_ifs; exacts [hg0 σ hσ, le_rfl]) a

end Resolvent

/-! ### Linearity -/

theorem sk1_Sol.zero (J : ι → ι → ℝ) (c : ℝ) :
    sk1_Sol J c (fun _ _ => 0) (fun _ _ => 0) :=
  ⟨fun _ => sk1_Cls.zero c, fun i τ _ => by simp⟩

theorem sk1_Sol.add {J : ι → ι → ℝ} {c : ℝ} (hc : 0 < c) {h₁ h₂ D₁ D₂ : ι → (ι → ℝ) → ℝ}
    (hh₁ : ∀ i, sk1_Cls c (h₁ i)) (hh₂ : ∀ i, sk1_Cls c (h₂ i))
    (hD₁ : sk1_Sol J c h₁ D₁) (hD₂ : sk1_Sol J c h₂ D₂) :
    sk1_Sol J c (fun i σ => h₁ i σ + h₂ i σ) (fun i σ => D₁ i σ + D₂ i σ) := by
  refine ⟨fun i => (hD₁.1 i).add (hD₂.1 i), fun i τ hτ => ?_⟩
  beta_reduce
  rw [hD₁.2 i τ hτ, hD₂.2 i τ hτ, ← integral_add (sk1_intOn_rhs hc hh₁ hD₁.1 hτ i)
    (sk1_intOn_rhs hc hh₂ hD₂.1 hτ i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem sk1_Sol.const_mul {J : ι → ι → ℝ} {c : ℝ} {h D : ι → (ι → ℝ) → ℝ}
    (hD : sk1_Sol J c h D) (α : ℝ) :
    sk1_Sol J c (fun i σ => α * h i σ) (fun i σ => α * D i σ) := by
  refine ⟨fun i => (hD.1 i).const_mul α, fun i τ hτ => ?_⟩
  beta_reduce
  rw [hD.2 i τ hτ, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sk1_Sol.sum {J : ι → ι → ℝ} {c : ℝ} (hc : 0 < c) {κ : Type*} (s : Finset κ)
    {h D : κ → ι → (ι → ℝ) → ℝ} (hh : ∀ x ∈ s, ∀ i, sk1_Cls c (h x i))
    (hD : ∀ x ∈ s, sk1_Sol J c (h x) (D x)) :
    sk1_Sol J c (fun i σ => ∑ x ∈ s, h x i σ) (fun i σ => ∑ x ∈ s, D x i σ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sk1_Sol.zero J c
  | insert y s hy ih =>
    simp only [Finset.sum_insert hy]
    exact (hD y (Finset.mem_insert_self y s)).add hc (hh y (Finset.mem_insert_self y s))
      (fun i => sk1_Cls.sum s fun x hx => hh x (Finset.mem_insert_of_mem hx) i)
      (ih (fun x hx => hh x (Finset.mem_insert_of_mem hx))
        (fun x hx => hD x (Finset.mem_insert_of_mem hx)))

theorem sk1_Sol.mono {J : ι → ι → ℝ} {c c' : ℝ} (hcc : c ≤ c') {h D : ι → (ι → ℝ) → ℝ}
    (hD : sk1_Sol J c' h D) : sk1_Sol J c h D :=
  ⟨fun i => (hD.1 i).mono hcc, hD.2⟩

/-- Only the values of the source on the orthant matter. -/
theorem sk1_Sol.congr_src {J : ι → ι → ℝ} {c : ℝ} {h h' D : ι → (ι → ℝ) → ℝ}
    (hD : sk1_Sol J c h D) (heq : ∀ i, ∀ σ ∈ sk1_orth, h i σ = h' i σ) : sk1_Sol J c h' D := by
  refine ⟨hD.1, fun i τ hτ => ?_⟩
  rw [hD.2 i τ hτ]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [heq i _ (sk1_line_mem hτ i (le_of_lt hs))]

section Linear

variable {J : ι → ι → ℝ} {r c : ℝ}

/-- **L0, linearity (sum).** -/
theorem Rop_add (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g₁ g₂ : (ι → ℝ) → ℝ} (hg₁ : sk1_Cls c g₁)
    (hg₂ : sk1_Cls c g₂) (a b : ι) :
    ∀ τ ∈ sk1_orth, Rop J c a b (fun σ => g₁ σ + g₂ σ) τ = Rop J c a b g₁ τ + Rop J c a b g₂ τ := by
  have hS := (RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls hg₁ b)).add hc
    (sk1_single_cls hg₁ b) (sk1_single_cls hg₂ b)
    (RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls hg₂ b))
  have e : (fun i σ => (Pi.single b g₁ : ι → (ι → ℝ) → ℝ) i σ +
      (Pi.single b g₂ : ι → (ι → ℝ) → ℝ) i σ) = Pi.single b (fun σ => g₁ σ + g₂ σ) := by
    funext i σ; simp only [sk1_single_apply]; split_ifs <;> simp
  rw [e] at hS
  exact RopV_eq hJ hc hr0 hrc hrow (sk1_single_cls (hg₁.add hg₂) b) hS a

/-- **L0, linearity (scalar).** -/
theorem Rop_const_mul (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (α : ℝ) (a b : ι) :
    ∀ τ ∈ sk1_orth, Rop J c a b (fun σ => α * g σ) τ = α * Rop J c a b g τ := by
  have hS := (RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls hg b)).const_mul α
  have e : (fun i σ => α * (Pi.single b g : ι → (ι → ℝ) → ℝ) i σ) =
      Pi.single b (fun σ => α * g σ) := by
    funext i σ; simp only [sk1_single_apply]; split_ifs <;> simp
  rw [e] at hS
  exact RopV_eq hJ hc hr0 hrc hrow (sk1_single_cls (hg.const_mul α) b) hS a

/-- The resolvent with a general source vector is the sum of the single-source resolvents. -/
theorem RopV_eq_sum (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {h : ι → (ι → ℝ) → ℝ} (hh : ∀ i, sk1_Cls c (h i)) (a : ι) :
    ∀ τ ∈ sk1_orth, RopV J c h a τ = ∑ x, Rop J c a x (h x) τ := by
  have hS := sk1_Sol.sum hc (D := fun x => RopV J c (Pi.single x (h x))) Finset.univ
    (fun x _ => sk1_single_cls (hh x) x)
    (fun x _ => RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls (hh x) x))
  have e : (fun i σ => ∑ x, (Pi.single x (h x) : ι → (ι → ℝ) → ℝ) i σ) = h := by
    funext i σ
    simp only [sk1_single_apply]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  rw [e] at hS
  exact RopV_eq hJ hc hr0 hrc hrow hh hS a

/-- Independence of the weight: for c ≤ c' (both > r), Rop J c = Rop J c' on the orthant. -/
theorem Rop_weight (hJ : ∀ i k, 0 ≤ J i k) (hc : 0 < c) (hr0 : 0 ≤ r) (hrc : r < c)
    (hrow : ∀ i, ∑ k, J i k ≤ r) {c' : ℝ} (hcc : c ≤ c') {g : (ι → ℝ) → ℝ}
    (hg : sk1_Cls c' g) (a b : ι) : ∀ τ ∈ sk1_orth, Rop J c a b g τ = Rop J c' a b g τ :=
  RopV_eq hJ hc hr0 hrc hrow (sk1_single_cls (hg.mono hcc) b)
    ((RopV_spec hJ (hc.trans_le hcc) hr0 (hrc.trans_le hcc) hrow (sk1_single_cls hg b)).mono
      hcc) a

end Linear

end PP2SGD

end

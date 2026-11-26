import LongTable.PP2SimonLieb3

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, node M9 (non-Gaussianity),
skeleton-inequality route in local-time (Volterra) language, session 1. The first two lemmas
(L0, L3) of the route review's plan, and L1.

Source: none read this session; builds only on `PP2SimonLieb3` (`tI`, `tI_ibp`, `volterra_nonneg`,
`abs_tI_le`, `exp_neg_sum_fq_le`, `Adm`).

DEFINITIONS (namespace `PP2SGD`).
* `sk1_orth` = [0,∞)^ι; `sk1_Cls c g`: g continuous on the orthant and |g(τ)| ≤ M e^{−cΣτ} there.
* `sk1_Sol J c h D`: every D_i in the class c and, on the orthant,
    D_i(τ) = ∫_0^∞ (h_i(τ + s e_i) + Σ_j J_ij D_j(τ + s e_i)) ds.
* `RopV J c h` (general source vector; chosen solution) and **`Rop J c a b g = RopV J c (δ_b g) a`**,
  i.e. D_a(τ) = ∫_0^∞ (δ_ab g(τ + s e_a) + Σ_j J_aj D_j(τ + s e_a)) ds.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound). Standing hypotheses:
J ≥ 0, row sums Σ_k J_ik ≤ r, 0 ≤ r < c.
* (L0, existence) `sk1_exists`: Banach fixed point (`ContractingWith.fixedPoint`) on
  ι → C_b((ι → ℝ), ℝ) in the weighted variables u = e^{cΣτ}D, operator
  (Tu)_i(τ) = e^{cΣPτ}∫ g_i(Pτ + se_i) ds + Σ_j J_ij ∫ e^{−cs} u_j(τ + se_i) ds (P = clamp onto the
  orthant), Lipschitz constant r/c; continuity of T u by dominated convergence.
* (L0) `RopV_spec`, `RopV_eq`, **`Rop_spec`** (class + equation), **`Rop_unique`** (any solution
  in the class is Rop, via `volterra_nonneg` for ± the difference, `sk1_Sol.unique`),
  **`Rop_nonneg`** (g ≥ 0 ⟹ Rop g ≥ 0), **`Rop_add`**, **`Rop_const_mul`**, `RopV_eq_sum`
  (RopV h = Σ_x Rop · x (h x)), `Rop_weight` (Rop J c = Rop J c' on the orthant, c ≤ c').
* (L3, replaces BFS Lemma 2.1) **`Rop_split_fun`**: for r < c < c', g in the class c', any τ₀,
  on the orthant  Rop_ab((σ_z − τ₀_z)g)(τ) = (τ_z − τ₀_z) Rop_ab(g)(τ) + Rop_az(Rop_zb g)(τ);
  **`Rop_split`**: at τ = τ₀ ∈ orthant, Rop_ab((σ_z − τ₀_z)g)(τ₀) = Rop_az(Rop_zb g)(τ₀).
  The one-variable Fubini identity ∫_0^∞∫_0^∞ q(s+t) dt ds = ∫_0^∞ u q(u) du is `sk1_fubini`.
  The slack c < c' is needed: (σ_z − τ₀_z) g is in the class c only for g in a class c' > c.
* (L1) `sk1_tI_cls` (σ ↦ [H]_σ is in the class c' for H ∈ Adm Ψ, given f(t) ≥ c't − C₀) and
  **`tI_eq_Rop`**: [φ_i G]_τ = Σ_x Rop_ix(σ ↦ [∂_x G]_σ)(τ), J = K + Kᵀ (from `tI_ibp` and
  uniqueness; no cone condition on ∂G).

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

/-! ## The weighted class on the orthant -/

/-- The closed orthant [0, ∞)^ι. -/
def sk1_orth : Set (ι → ℝ) := {τ | ∀ x, 0 ≤ τ x}

/-- The weighted class: continuous on the orthant, |g(τ)| ≤ M e^{−cΣτ} there. -/
def sk1_Cls (c : ℝ) (g : (ι → ℝ) → ℝ) : Prop :=
  ContinuousOn g sk1_orth ∧ ∃ M, ∀ τ ∈ sk1_orth, |g τ| ≤ M * Real.exp (-(c * ∑ x, τ x))

lemma sk1_sum_nonneg {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) : 0 ≤ ∑ x, τ x :=
  Finset.sum_nonneg fun x _ => hτ x

lemma sk1_line_mem {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) (i : ι) {s : ℝ} (hs : 0 ≤ s) :
    τ + Pi.single i s ∈ sk1_orth :=
  add_single_nonneg hτ i hs

lemma sk1_continuous_line (τ : ι → ℝ) (i : ι) :
    Continuous fun s : ℝ => τ + (Pi.single i s : ι → ℝ) :=
  have h : Continuous fun s : ℝ => (Pi.single i s : ι → ℝ) := by
    refine continuous_pi fun x => ?_
    by_cases hx : x = i
    · subst hx; simp only [Pi.single_eq_same]; exact continuous_id'
    · simpa [Pi.single_eq_of_ne hx] using continuous_const
  continuous_const.add h

lemma sk1_contOn_line {g : (ι → ℝ) → ℝ} (hg : ContinuousOn g sk1_orth) {τ : ι → ℝ}
    (hτ : τ ∈ sk1_orth) (i : ι) : ContinuousOn (fun s : ℝ => g (τ + Pi.single i s)) (Ici 0) :=
  hg.comp (sk1_continuous_line τ i).continuousOn fun _ hs => sk1_line_mem hτ i hs

lemma sk1_exp_line (c : ℝ) (τ : ι → ℝ) (i : ι) (s : ℝ) :
    Real.exp (-(c * ∑ x, (τ + Pi.single i s : ι → ℝ) x)) =
      Real.exp (-(c * ∑ x, τ x)) * Real.exp (-c * s) := by
  rw [sum_add_single_eq, ← Real.exp_add]; ring_nf

lemma sk1_Cls.bound_nonneg {c : ℝ} {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) :
    ∃ M, 0 ≤ M ∧ ∀ τ ∈ sk1_orth, |g τ| ≤ M * Real.exp (-(c * ∑ x, τ x)) := by
  obtain ⟨_, M, hM⟩ := hg
  exact ⟨max M 0, le_max_right _ _, fun τ hτ => (hM τ hτ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩

/-- Integrability along a coordinate ray. -/
lemma sk1_intOn {c : ℝ} (hc : 0 < c) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) {τ : ι → ℝ}
    (hτ : τ ∈ sk1_orth) (i : ι) :
    IntegrableOn (fun s => g (τ + Pi.single i s)) (Ioi 0) := by
  obtain ⟨M, _, hM⟩ := hg.bound_nonneg
  refine ((exp_neg_integrableOn_Ioi 0 hc).const_mul (M * Real.exp (-(c * ∑ x, τ x)))).mono'
    (((sk1_contOn_line hg.1 hτ i).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
  rw [Real.norm_eq_abs]
  refine (hM _ (sk1_line_mem hτ i (le_of_lt hs))).trans (le_of_eq ?_)
  rw [sk1_exp_line]; ring

/-- t ≤ e^{δt}/δ. -/
lemma sk1_le_exp_div {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : t ≤ Real.exp (δ * t) / δ := by
  rw [le_div_iff₀ hδ]
  have := Real.add_one_le_exp (δ * t)
  linarith

/-- Integrability of s · g(τ + s e_i) along a coordinate ray. -/
lemma sk1_intOn_mul {c : ℝ} (hc : 0 < c) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) {τ : ι → ℝ}
    (hτ : τ ∈ sk1_orth) (i : ι) :
    IntegrableOn (fun s => s * g (τ + Pi.single i s)) (Ioi 0) := by
  obtain ⟨M, hM0, hM⟩ := hg.bound_nonneg
  have hc2 : 0 < c / 2 := by linarith
  refine ((exp_neg_integrableOn_Ioi 0 hc2).const_mul
      (M * Real.exp (-(c * ∑ x, τ x)) * (2 / c))).mono'
    ((continuousOn_id.mul ((sk1_contOn_line hg.1 hτ i).mono Ioi_subset_Ici_self)).aestronglyMeasurable
      measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
  have hs0 : 0 ≤ s := le_of_lt hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0]
  have h1 := hM _ (sk1_line_mem hτ i hs0)
  rw [sk1_exp_line] at h1
  have h2 := sk1_le_exp_div hc2 s
  have hE : 0 ≤ M * Real.exp (-(c * ∑ x, τ x)) := mul_nonneg hM0 (Real.exp_pos _).le
  have h3 : s * Real.exp (-c * s) ≤ (2 / c) * Real.exp (-(c / 2) * s) := by
    have e : Real.exp (c / 2 * s) / (c / 2) * Real.exp (-c * s) =
        (2 / c) * Real.exp (-(c / 2) * s) := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]; field_simp; ring_nf
    rw [← e]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  calc s * |g (τ + Pi.single i s)| ≤ s * (M * Real.exp (-(c * ∑ x, τ x)) * Real.exp (-c * s)) :=
        mul_le_mul_of_nonneg_left (h1.trans_eq (by ring)) hs0
    _ = M * Real.exp (-(c * ∑ x, τ x)) * (s * Real.exp (-c * s)) := by ring
    _ ≤ M * Real.exp (-(c * ∑ x, τ x)) * ((2 / c) * Real.exp (-(c / 2) * s)) :=
        mul_le_mul_of_nonneg_left h3 hE
    _ = _ := by ring

lemma sk1_Cls.add {c : ℝ} {f g : (ι → ℝ) → ℝ} (hf : sk1_Cls c f) (hg : sk1_Cls c g) :
    sk1_Cls c (fun τ => f τ + g τ) := by
  obtain ⟨M, _, hM⟩ := hf.bound_nonneg
  obtain ⟨N, _, hN⟩ := hg.bound_nonneg
  refine ⟨hf.1.add hg.1, M + N, fun τ hτ => ?_⟩
  calc |f τ + g τ| ≤ |f τ| + |g τ| := abs_add_le _ _
    _ ≤ _ := by have := hM τ hτ; have := hN τ hτ; nlinarith

lemma sk1_Cls.const_mul {c : ℝ} {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (α : ℝ) :
    sk1_Cls c (fun τ => α * g τ) := by
  obtain ⟨M, _, hM⟩ := hg.bound_nonneg
  refine ⟨continuousOn_const.mul hg.1, |α| * M, fun τ hτ => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hM τ hτ) (abs_nonneg _)

lemma sk1_Cls.zero (c : ℝ) : sk1_Cls c (fun _ : ι → ℝ => (0 : ℝ)) :=
  ⟨continuousOn_const, 0, fun τ _ => by simp⟩

lemma sk1_Cls.sum {c : ℝ} {κ : Type*} (s : Finset κ) {g : κ → (ι → ℝ) → ℝ}
    (hg : ∀ x ∈ s, sk1_Cls c (g x)) : sk1_Cls c (fun τ => ∑ x ∈ s, g x τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sk1_Cls.zero (ι := ι) c
  | insert y s hy ih =>
    simp only [Finset.sum_insert hy]
    exact (hg y (Finset.mem_insert_self y s)).add
      (ih fun x hx => hg x (Finset.mem_insert_of_mem hx))

lemma sk1_Cls.mono {c c' : ℝ} (hcc : c ≤ c') {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c' g) :
    sk1_Cls c g := by
  obtain ⟨M, hM0, hM⟩ := hg.bound_nonneg
  refine ⟨hg.1, M, fun τ hτ => (hM τ hτ).trans (mul_le_mul_of_nonneg_left ?_ hM0)⟩
  exact Real.exp_le_exp.mpr (by nlinarith [sk1_sum_nonneg hτ])

lemma sk1_Cls.congr {c : ℝ} {f g : (ι → ℝ) → ℝ} (hf : sk1_Cls c f)
    (h : ∀ τ ∈ sk1_orth, f τ = g τ) : sk1_Cls c g := by
  obtain ⟨M, hM⟩ := hf.2
  exact ⟨hf.1.congr fun τ hτ => (h τ hτ).symm, M, fun τ hτ => h τ hτ ▸ hM τ hτ⟩

/-- Multiplying by an affine coordinate costs an arbitrarily small amount of decay. -/
lemma sk1_Cls.mul_coord {c c' : ℝ} (hcc : c < c') {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c' g)
    (z : ι) (t : ℝ) : sk1_Cls c (fun σ => (σ z - t) * g σ) := by
  obtain ⟨M, hM0, hM⟩ := hg.bound_nonneg
  have hδ : 0 < c' - c := by linarith
  refine ⟨((continuous_apply z).sub continuous_const).continuousOn.mul hg.1,
    M * (1 / (c' - c) + |t|), fun σ hσ => ?_⟩
  set S := ∑ x, σ x with hS
  have hS0 : 0 ≤ S := sk1_sum_nonneg hσ
  have hz : |σ z - t| ≤ S + |t| := by
    have h1 : σ z ≤ S := Finset.single_le_sum (fun x _ => hσ x) (Finset.mem_univ z)
    rw [abs_le]; constructor <;> cases abs_cases t <;> linarith [hσ z]
  have h2 := sk1_le_exp_div hδ S
  have e1 : Real.exp ((c' - c) * S) / (c' - c) * Real.exp (-(c' * S)) =
      1 / (c' - c) * Real.exp (-(c * S)) := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]; field_simp; ring_nf
  have h3 : S * Real.exp (-(c' * S)) ≤ 1 / (c' - c) * Real.exp (-(c * S)) := by
    rw [← e1]; exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have h4 : Real.exp (-(c' * S)) ≤ Real.exp (-(c * S)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [abs_mul]
  calc |σ z - t| * |g σ| ≤ (S + |t|) * (M * Real.exp (-(c' * S))) :=
        mul_le_mul hz (hM σ hσ) (abs_nonneg _) (by positivity)
    _ = M * (S * Real.exp (-(c' * S)) + |t| * Real.exp (-(c' * S))) := by ring
    _ ≤ M * (1 / (c' - c) * Real.exp (-(c * S)) + |t| * Real.exp (-(c * S))) := by
        gcongr
    _ = _ := by ring

/-! ## Solutions of the Volterra equation -/

/-- D solves the Volterra equation with source vector h in the weighted class c:
D_i(τ) = ∫_0^∞ (h_i(τ + s e_i) + Σ_j J_ij D_j(τ + s e_i)) ds on the orthant. -/
def sk1_Sol (J : ι → ι → ℝ) (c : ℝ) (h D : ι → (ι → ℝ) → ℝ) : Prop :=
  (∀ i, sk1_Cls c (D i)) ∧ ∀ i, ∀ τ ∈ sk1_orth, D i τ =
    ∫ s in Ioi (0 : ℝ), (h i (τ + Pi.single i s) + ∑ j, J i j * D j (τ + Pi.single i s))

lemma sk1_intOn_rhs {J : ι → ι → ℝ} {c : ℝ} (hc : 0 < c) {h D : ι → (ι → ℝ) → ℝ}
    (hh : ∀ i, sk1_Cls c (h i)) (hD : ∀ i, sk1_Cls c (D i)) {τ : ι → ℝ} (hτ : τ ∈ sk1_orth)
    (i : ι) : IntegrableOn (fun s => h i (τ + Pi.single i s) +
      ∑ j, J i j * D j (τ + Pi.single i s)) (Ioi 0) :=
  (sk1_intOn hc (hh i) hτ i).add (integrable_finsetSum _ fun j _ =>
    (sk1_intOn hc (hD j) hτ i).const_mul _)

/-- Positivity: a solution with nonnegative source is nonnegative (`volterra_nonneg`). -/
theorem sk1_Sol.nonneg {J : ι → ι → ℝ} (hJ : ∀ i k, 0 ≤ J i k) {r c : ℝ} (hc : 0 < c)
    (hr0 : 0 ≤ r) (hrc : r < c) (hrow : ∀ i, ∑ k, J i k ≤ r) {h D : ι → (ι → ℝ) → ℝ}
    (hD : sk1_Sol J c h D) (hh : ∀ i, ∀ σ ∈ sk1_orth, 0 ≤ h i σ) :
    ∀ i, ∀ τ ∈ sk1_orth, 0 ≤ D i τ := by
  have hM : ∃ M, ∀ i τ, (∀ x, 0 ≤ τ x) → -D i τ ≤ M * Real.exp (-(c * ∑ x, τ x)) := by
    choose M hM0 hM using fun i => (hD.1 i).bound_nonneg
    refine ⟨∑ i, M i, fun i τ hτ => ?_⟩
    have h1 := hM i τ hτ
    have h2 : M i ≤ ∑ i, M i := Finset.single_le_sum (fun i _ => hM0 i) (Finset.mem_univ i)
    calc -D i τ ≤ |D i τ| := neg_le_abs _
      _ ≤ M i * Real.exp (-(c * ∑ x, τ x)) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  exact volterra_nonneg (E := fun i τ s => h i (τ + Pi.single i s) +
      ∑ j, J i j * D j (τ + Pi.single i s)) hJ hc hr0 hrc hrow (fun i τ hτ => hD.2 i τ hτ)
    (fun i τ s hτ hs => by
      have := hh i _ (sk1_line_mem hτ i (le_of_lt hs))
      linarith) hM

/-- Uniqueness of solutions in the weighted class (`volterra_nonneg` for ± the difference). -/
theorem sk1_Sol.unique {J : ι → ι → ℝ} (hJ : ∀ i k, 0 ≤ J i k) {r c : ℝ} (hc : 0 < c)
    (hr0 : 0 ≤ r) (hrc : r < c) (hrow : ∀ i, ∑ k, J i k ≤ r) {h D D' : ι → (ι → ℝ) → ℝ}
    (hh : ∀ i, sk1_Cls c (h i)) (hD : sk1_Sol J c h D) (hD' : sk1_Sol J c h D') :
    ∀ i, ∀ τ ∈ sk1_orth, D i τ = D' i τ := by
  have key : ∀ {D D' : ι → (ι → ℝ) → ℝ}, sk1_Sol J c h D → sk1_Sol J c h D' →
      ∀ i, ∀ τ ∈ sk1_orth, 0 ≤ D i τ - D' i τ := by
    intro D D' hD hD'
    have hM : ∃ M, ∀ i τ, (∀ x, 0 ≤ τ x) →
        -(D i τ - D' i τ) ≤ M * Real.exp (-(c * ∑ x, τ x)) := by
      choose M hM0 hM using fun i => (hD.1 i).bound_nonneg
      choose M' hM0' hM' using fun i => (hD'.1 i).bound_nonneg
      refine ⟨∑ i, (M i + M' i), fun i τ hτ => ?_⟩
      have h1 := hM i τ hτ
      have h1' := hM' i τ hτ
      have h2 : M i + M' i ≤ ∑ i, (M i + M' i) :=
        Finset.single_le_sum (f := fun i => M i + M' i) (fun i _ => add_nonneg (hM0 i) (hM0' i))
          (Finset.mem_univ i)
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(c * ∑ x, τ x))).le
      have := neg_le_abs (D i τ)
      have := le_abs_self (D' i τ)
      nlinarith
    refine volterra_nonneg (D := fun i τ => D i τ - D' i τ)
      (E := fun i τ s => ∑ j, J i j * (D j (τ + Pi.single i s) - D' j (τ + Pi.single i s)))
      hJ hc hr0 hrc hrow (fun i τ hτ => ?_) (fun i τ s _ _ => le_rfl) hM
    rw [hD.2 i τ hτ, hD'.2 i τ hτ, ← integral_sub (sk1_intOn_rhs hc hh hD.1 hτ i)
      (sk1_intOn_rhs hc hh hD'.1 hτ i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  intro i τ hτ
  have h1 := key hD hD' i τ hτ
  have h2 := key hD' hD i τ hτ
  linarith

/-! ## Existence: Banach fixed point in the weighted variables u = e^{cΣτ} D -/

/-- Componentwise clamp onto the orthant. -/
def sk1_P (τ : ι → ℝ) : ι → ℝ := fun x => max (τ x) 0

lemma sk1_P_mem (τ : ι → ℝ) : sk1_P τ ∈ sk1_orth := fun _ => le_max_right _ _

lemma sk1_P_of_mem {τ : ι → ℝ} (hτ : τ ∈ sk1_orth) : sk1_P τ = τ :=
  funext fun x => max_eq_left (hτ x)

lemma continuous_sk1_P : Continuous (sk1_P : (ι → ℝ) → ι → ℝ) :=
  continuous_pi fun x => (continuous_apply x).max continuous_const

/-- The weighted source e^{cΣτ} ∫_0^∞ g(τ + s e_i) ds (τ clamped to the orthant). -/
def sk1_H (c : ℝ) (g : (ι → ℝ) → ℝ) (i : ι) (τ : ι → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (c * ∑ x, sk1_P τ x) * g (sk1_P τ + Pi.single i s)

/-- The weighted kernel ∫_0^∞ e^{−cs} f(τ + s e_i) ds. -/
def sk1_U (c : ℝ) (f : (ι → ℝ) → ℝ) (i : ι) (τ : ι → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-c * s) * f (τ + Pi.single i s)

lemma sk1_H_pt {c M : ℝ} {g : (ι → ℝ) → ℝ}
    (hM : ∀ τ ∈ sk1_orth, |g τ| ≤ M * Real.exp (-(c * ∑ x, τ x))) (i : ι) (τ : ι → ℝ)
    {s : ℝ} (hs : 0 < s) :
    ‖Real.exp (c * ∑ x, sk1_P τ x) * g (sk1_P τ + Pi.single i s)‖ ≤ M * Real.exp (-c * s) := by
  have h1 := hM _ (sk1_line_mem (sk1_P_mem τ) i (le_of_lt hs))
  rw [sk1_exp_line] at h1
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc Real.exp (c * ∑ x, sk1_P τ x) * |g (sk1_P τ + Pi.single i s)| ≤
      Real.exp (c * ∑ x, sk1_P τ x) *
        (M * (Real.exp (-(c * ∑ x, sk1_P τ x)) * Real.exp (-c * s))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = M * Real.exp (-c * s) * (Real.exp (c * ∑ x, sk1_P τ x) *
        Real.exp (-(c * ∑ x, sk1_P τ x))) := by ring
    _ = M * Real.exp (-c * s) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

lemma continuous_sk1_H {c : ℝ} (hc : 0 < c) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (i : ι) :
    Continuous (sk1_H c g i) := by
  obtain ⟨M, _, hM⟩ := hg.bound_nonneg
  refine continuous_of_dominated (bound := fun s => M * Real.exp (-c * s)) (fun τ => ?_)
    (fun τ => ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => sk1_H_pt hM i τ hs)
    ((exp_neg_integrableOn_Ioi 0 hc).const_mul M)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
  · exact (continuousOn_const.mul ((sk1_contOn_line hg.1 (sk1_P_mem τ) i).mono
      Ioi_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioi
  · have h1 : Continuous fun τ => g (sk1_P τ + Pi.single i s) :=
      hg.1.comp_continuous (continuous_sk1_P.add continuous_const)
        fun τ => sk1_line_mem (sk1_P_mem τ) i (le_of_lt hs)
    have h2 : Continuous fun τ : ι → ℝ => Real.exp (c * ∑ x, sk1_P τ x) :=
      Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetSum _ fun x _ => (continuous_apply x).comp continuous_sk1_P))
    exact h2.mul h1

lemma sk1_H_le {c : ℝ} (hc : 0 < c) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c g) (i : ι) :
    ∃ C, ∀ τ, ‖sk1_H c g i τ‖ ≤ C := by
  obtain ⟨M, _, hM⟩ := hg.bound_nonneg
  exact ⟨∫ s in Ioi (0 : ℝ), M * Real.exp (-c * s), fun τ =>
    norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hc).const_mul M)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => sk1_H_pt hM i τ hs)⟩

lemma sk1_U_pt (c : ℝ) (u : (ι → ℝ) →ᵇ ℝ) (i : ι) (τ : ι → ℝ) (s : ℝ) :
    ‖Real.exp (-c * s) * u (τ + Pi.single i s)‖ ≤ ‖u‖ * Real.exp (-c * s) := by
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
  exact mul_le_mul_of_nonneg_right (u.norm_coe_le_norm _) (Real.exp_pos _).le

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

/-! ## L3: the split identity -/

/-- One-variable Fubini: ∫_0^∞ ∫_0^∞ q(s + t) dt ds = ∫_0^∞ u q(u) du. -/
lemma sk1_fubini {q : ℝ → ℝ} {C κ : ℝ} (hκ : 0 < κ) (hq : ContinuousOn q (Ici 0))
    (hb : ∀ u, 0 ≤ u → |q u| ≤ C * Real.exp (-κ * u)) :
    ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), q (s + t) = ∫ u in Ioi (0 : ℝ), u * q u := by
  set F : ℝ → ℝ → ℝ := fun s u => (Ioi s).indicator q u with hF
  have step1 : ∀ s, 0 ≤ s → ∫ t in Ioi (0 : ℝ), q (s + t) = ∫ u in Ioi (0 : ℝ), F s u := by
    intro s hs
    have e1 : ∫ t in Ioi (0 : ℝ), q (s + t) = ∫ t, (Ioi s).indicator q (t + s) := by
      rw [← integral_indicator measurableSet_Ioi]
      congr 1; funext t
      by_cases ht : 0 < t
      · rw [indicator_of_mem (show t ∈ Ioi 0 from ht),
          indicator_of_mem (show t + s ∈ Ioi s by simp only [mem_Ioi]; linarith), add_comm]
      · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht),
          indicator_of_notMem (show t + s ∉ Ioi s by simp only [mem_Ioi]; linarith)]
    rw [e1, integral_add_right_eq_self (fun u => (Ioi s).indicator q u) s]
    simp only [hF]
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hs),
      integral_indicator measurableSet_Ioi]
  have step3 : ∀ u, 0 < u → ∫ s in Ioi (0 : ℝ), F s u = u * q u := by
    intro u hu
    have e : (fun s => F s u) = (Iio u).indicator (fun _ => q u) := by
      funext s; simp only [hF]
      by_cases hsu : s < u
      · rw [indicator_of_mem (show u ∈ Ioi s from hsu), indicator_of_mem (show s ∈ Iio u from hsu)]
      · rw [indicator_of_notMem (show u ∉ Ioi s from hsu),
          indicator_of_notMem (show s ∉ Iio u from hsu)]
    rw [e, setIntegral_indicator measurableSet_Iio, setIntegral_const, Ioi_inter_Iio,
      Real.volume_real_Ioo_of_le hu.le, sub_zero, smul_eq_mul]
  have hqm : AEStronglyMeasurable q (volume.restrict (Ioi (0 : ℝ))) :=
    (hq.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hκ2 : 0 < κ / 2 := half_pos hκ
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg : Integrable (fun p : ℝ × ℝ => max C 0 *
        (Real.exp (-(κ / 2) * p.1) * Real.exp (-(κ / 2) * p.2)))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      ((exp_neg_integrableOn_Ioi 0 hκ2).mul_prod (exp_neg_integrableOn_Ioi 0 hκ2)).const_mul _
    refine hg.mono' ?_ ?_
    · have e : Function.uncurry F = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => q p.2) := by
        funext p
        simp only [Function.uncurry, hF]
        by_cases hp : p.1 < p.2
        · rw [indicator_of_mem (show p.2 ∈ Ioi p.1 from hp),
            indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < p.2} from hp)]
        · rw [indicator_of_notMem (show p.2 ∉ Ioi p.1 from hp),
            indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < p.2} from hp)]
      rw [e]
      exact hqm.comp_snd.indicator (measurableSet_lt measurable_fst measurable_snd)
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : 0 < p.1 := hp1
      have hp2' : 0 < p.2 := hp2
      simp only [Function.uncurry, hF]
      by_cases hpp : p.1 < p.2
      · rw [indicator_of_mem (show p.2 ∈ Ioi p.1 from hpp), Real.norm_eq_abs]
        refine (hb p.2 (le_of_lt hp2')).trans ?_
        have h1 : Real.exp (-κ * p.2) ≤
            Real.exp (-(κ / 2) * p.1) * Real.exp (-(κ / 2) * p.2) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
        calc C * Real.exp (-κ * p.2) ≤ max C 0 * Real.exp (-κ * p.2) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
      · rw [indicator_of_notMem (show p.2 ∉ Ioi p.1 from hpp), norm_zero]
        have := le_max_right C 0
        positivity
  calc ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), q (s + t) =
        ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F s u :=
        setIntegral_congr_fun measurableSet_Ioi fun s hs => step1 s (le_of_lt hs)
    _ = ∫ u in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), F s u := integral_integral_swap hint
    _ = ∫ u in Ioi (0 : ℝ), u * q u := setIntegral_congr_fun measurableSet_Ioi fun u hu => step3 u hu

section Split

variable {J : ι → ι → ℝ} {r c c' : ℝ}

lemma sk1_single_mul (b i z : ι) (g : (ι → ℝ) → ℝ) (t : ℝ) (σ : ι → ℝ) :
    (Pi.single b (fun σ => (σ z - t) * g σ) : ι → (ι → ℝ) → ℝ) i σ =
      (σ z - t) * (Pi.single b g : ι → (ι → ℝ) → ℝ) i σ := by
  simp only [sk1_single_apply]; split_ifs <;> simp

/-- **L3, functional form.** For r < c < c' and g in the class c', on the whole orthant
  Rop_ab((σ_z − τ₀_z) g)(τ) = (τ_z − τ₀_z) Rop_ab(g)(τ) + Rop_az(Rop_zb g)(τ).
Proof: Y_a(τ) = Rop_ab((σ_z − τ₀_z)g)(τ) − (τ_z − τ₀_z) Rop_ab(g)(τ) solves the Volterra equation
with source δ_az Rop_zb g, by the one-variable Fubini identity
∫_0^∞ s Q(τ + s e_z) ds = ∫_0^∞ D_z(τ + s e_z) ds (`sk1_fubini`); then uniqueness. -/
theorem Rop_split_fun (hJ : ∀ i k, 0 ≤ J i k) (hr0 : 0 ≤ r) (hrc : r < c) (hcc : c < c')
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c' g) (a b z : ι)
    (τ₀ : ι → ℝ) :
    ∀ τ ∈ sk1_orth, Rop J c a b (fun σ => (σ z - τ₀ z) * g σ) τ =
      (τ z - τ₀ z) * Rop J c a b g τ + Rop J c a z (Rop J c z b g) τ := by
  have hc : 0 < c := lt_of_le_of_lt hr0 hrc
  have hc' : 0 < c' := hc.trans hcc
  have hrc' : r < c' := hrc.trans hcc
  set gt : (ι → ℝ) → ℝ := fun σ => (σ z - τ₀ z) * g σ with hgt_def
  have hgt : sk1_Cls c gt := hg.mul_coord hcc z (τ₀ z)
  set D' := RopV J c' (Pi.single b g) with hD'_def
  have hD'c' : sk1_Sol J c' (Pi.single b g) D' :=
    RopV_spec hJ hc' hr0 hrc' hrow (sk1_single_cls hg b)
  have hD'c : sk1_Sol J c (Pi.single b g) D' := hD'c'.mono hcc.le
  have hDD' : ∀ i, ∀ τ ∈ sk1_orth, Rop J c i b g τ = D' i τ :=
    RopV_eq hJ hc hr0 hrc hrow (sk1_single_cls (hg.mono hcc.le) b) hD'c
  set L := RopV J c (Pi.single b gt) with hL_def
  have hL : sk1_Sol J c (Pi.single b gt) L :=
    RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls hgt b)
  set Y : ι → (ι → ℝ) → ℝ := fun i τ => L i τ - (τ z - τ₀ z) * D' i τ with hY_def
  have hYc : ∀ i, sk1_Cls c (Y i) := fun i =>
    ((hL.1 i).add (((hD'c'.1 i).mul_coord hcc z (τ₀ z)).const_mul (-1))).congr
      fun τ _ => by simp only [hY_def]; ring
  set B : ι → (ι → ℝ) → ℝ := fun i σ =>
    (Pi.single b g : ι → (ι → ℝ) → ℝ) i σ + ∑ j, J i j * D' j σ with hB_def
  have hBc : ∀ i, sk1_Cls c' (B i) := fun i =>
    (sk1_single_cls hg b i).add (sk1_Cls.sum Finset.univ fun j _ => (hD'c'.1 j).const_mul (J i j))
  have hY : sk1_Sol J c (Pi.single z (D' z)) Y := by
    refine ⟨hYc, fun i τ hτ => ?_⟩
    have hBi : IntegrableOn (fun s => B i (τ + Pi.single i s)) (Ioi 0) :=
      sk1_intOn hc ((hBc i).mono hcc.le) hτ i
    have hLi := sk1_intOn_rhs (J := J) hc (sk1_single_cls hgt b) hL.1 hτ i
    have hYi : IntegrableOn (fun s => ∑ j, J i j * Y j (τ + Pi.single i s)) (Ioi 0) :=
      integrable_finsetSum _ fun j _ => (sk1_intOn hc (hYc j) hτ i).const_mul _
    have hSi : IntegrableOn (fun s =>
        (Pi.single z (D' z) : ι → (ι → ℝ) → ℝ) i (τ + Pi.single i s)) (Ioi 0) :=
      sk1_intOn hc (sk1_single_cls (hD'c.1 z) z i) hτ i
    have hPi : IntegrableOn (fun s => (Pi.single i s : ι → ℝ) z * B i (τ + Pi.single i s))
        (Ioi 0) := by
      by_cases hiz : i = z
      · subst hiz; simpa using sk1_intOn_mul hc ((hBc i).mono hcc.le) hτ i
      · simp [Pi.single_eq_of_ne (Ne.symm hiz)]
    have hkey : ∫ s in Ioi (0 : ℝ), (Pi.single i s : ι → ℝ) z * B i (τ + Pi.single i s) =
        ∫ s in Ioi (0 : ℝ), (Pi.single z (D' z) : ι → (ι → ℝ) → ℝ) i (τ + Pi.single i s) := by
      by_cases hiz : i = z
      · subst hiz
        simp only [Pi.single_eq_same]
        obtain ⟨M, _, hM⟩ := (hBc i).bound_nonneg
        have hfub := sk1_fubini (q := fun u => B i (τ + Pi.single i u))
          (C := M * Real.exp (-(c' * ∑ x, τ x))) hc' (sk1_contOn_line (hBc i).1 hτ i)
          (fun u hu => by
            have := hM _ (sk1_line_mem hτ i hu)
            rw [sk1_exp_line] at this
            exact this.trans_eq (by ring))
        rw [← hfub]
        refine (setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_).symm
        rw [hD'c'.2 i _ (sk1_line_mem hτ i (le_of_lt hs))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        have hpt : τ + Pi.single i s + Pi.single i t = τ + Pi.single i (s + t) := by
          rw [add_assoc, ← Pi.single_add]
        simp only [hB_def]
        rw [hpt]
      · simp [Pi.single_eq_of_ne (Ne.symm hiz), Pi.single_eq_of_ne hiz]
    calc Y i τ = (∫ s in Ioi (0 : ℝ), ((Pi.single b gt : ι → (ι → ℝ) → ℝ) i (τ + Pi.single i s) +
          ∑ j, J i j * L j (τ + Pi.single i s))) -
          (τ z - τ₀ z) * ∫ s in Ioi (0 : ℝ), B i (τ + Pi.single i s) := by
          simp only [hY_def]; rw [hL.2 i τ hτ, hD'c'.2 i τ hτ]
      _ = ∫ s in Ioi (0 : ℝ), ((Pi.single i s : ι → ℝ) z * B i (τ + Pi.single i s) +
          ∑ j, J i j * Y j (τ + Pi.single i s)) := by
          rw [← integral_const_mul, ← integral_sub hLi (hBi.const_mul _)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          have hsY : ∑ j, J i j * Y j (τ + Pi.single i s) =
              ∑ j, J i j * L j (τ + Pi.single i s) - ((τ + Pi.single i s : ι → ℝ) z - τ₀ z) *
                ∑ j, J i j * D' j (τ + Pi.single i s) := by
            simp only [hY_def, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by ring
          have hσz : (τ + Pi.single i s : ι → ℝ) z = τ z + (Pi.single i s : ι → ℝ) z := rfl
          simp only [hB_def]
          rw [hsY, sk1_single_mul, hσz]
          ring
      _ = _ := by
          rw [integral_add hPi hYi, integral_add hSi hYi, hkey]
  have hR : ∀ i, ∀ τ ∈ sk1_orth, RopV J c (Pi.single z (D' z)) i τ = Y i τ :=
    RopV_eq hJ hc hr0 hrc hrow (sk1_single_cls (hD'c.1 z) z) hY
  have hR2 : ∀ i, ∀ τ ∈ sk1_orth,
      Rop J c i z (Rop J c z b g) τ = RopV J c (Pi.single z (D' z)) i τ := by
    have hsrc : ∀ k, sk1_Cls c ((Pi.single z (Rop J c z b g) : ι → (ι → ℝ) → ℝ) k) :=
      sk1_single_cls ((Rop_spec hJ hc hr0 hrc hrow (hg.mono hcc.le) b).1 z) z
    exact RopV_eq hJ hc hr0 hrc hrow hsrc
      ((RopV_spec hJ hc hr0 hrc hrow (sk1_single_cls (hD'c.1 z) z)).congr_src
        fun k σ hσ => by
          simp only [sk1_single_apply]
          split_ifs
          · exact (hDD' z σ hσ).symm
          · rfl)
  intro τ hτ
  have e1 : Rop J c a b gt τ = L a τ := rfl
  have e2 : L a τ = Y a τ + (τ z - τ₀ z) * D' a τ := by simp only [hY_def]; ring
  rw [e1, e2, ← hR a τ hτ, ← hR2 a τ hτ, hDD' a τ hτ]
  ring

/-- **L3 (replaces BFS Lemma 2.1).** For J ≥ 0 with row sums ≤ r < c < c', g in the class c'
and a base point τ₀ in the orthant:
  Rop_ab(σ ↦ (σ_z − τ₀_z) g(σ))(τ₀) = Rop_az(Rop_zb g)(τ₀). -/
theorem Rop_split (hJ : ∀ i k, 0 ≤ J i k) (hr0 : 0 ≤ r) (hrc : r < c) (hcc : c < c')
    (hrow : ∀ i, ∑ k, J i k ≤ r) {g : (ι → ℝ) → ℝ} (hg : sk1_Cls c' g) (a b z : ι)
    {τ₀ : ι → ℝ} (hτ₀ : τ₀ ∈ sk1_orth) :
    Rop J c a b (fun σ => (σ z - τ₀ z) * g σ) τ₀ = Rop J c a z (Rop J c z b g) τ₀ := by
  rw [Rop_split_fun hJ hr0 hrc hcc hrow hg a b z τ₀ τ₀ hτ₀, sub_self, zero_mul, zero_add]

end Split

/-! ## L1: the local-time expectations as resolvents -/

/-- σ ↦ [H]_σ lies in the weighted class c' for admissible H (continuity by dominated
convergence; decay from W_σ ≤ e^{−Σf(σ_x)} W_0 and f(t) ≥ c't − C₀). -/
theorem sk1_tI_cls {K : ι → ι → ℝ} {a b : ℝ} (hb : 0 ≤ b) {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {c' C₀ : ℝ} (hc' : 0 < c') (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq a b t)
    {H : (ι → ℝ) → ℝ} (hH : Adm Ψ H) : sk1_Cls c' (fun σ => tI K a b σ H) := by
  set N := ∫ φ, ‖H φ * Real.exp (quadE K φ) * tw a b 0 φ‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hE : ∀ σ ∈ sk1_orth, Real.exp (-∑ x, fq a b (σ x)) ≤
      Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, σ x)) :=
    fun σ hσ => exp_neg_sum_fq_le hf hσ
  have hE1 : ∀ σ ∈ sk1_orth, Real.exp (-∑ x, fq a b (σ x)) ≤ Real.exp (Fintype.card ι * C₀) :=
    fun σ hσ => (hE σ hσ).trans (mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by nlinarith [sk1_sum_nonneg hσ])))
  refine ⟨?_, Real.exp (Fintype.card ι * C₀) * N, fun σ hσ => ?_⟩
  · show ContinuousOn (fun σ => ∫ φ, H φ * Real.exp (quadE K φ) * tw a b σ φ) sk1_orth
    refine continuousOn_of_dominated (bound := fun φ => Real.exp (Fintype.card ι * C₀) *
        ‖H φ * Real.exp (quadE K φ) * tw a b 0 φ‖)
      (fun σ hσ => (integrable_adm hb hint hσ hH).aestronglyMeasurable)
      (fun σ hσ => Filter.Eventually.of_forall fun φ => ?_) ((hint H hH).norm.const_mul _)
      (Filter.Eventually.of_forall fun φ => ?_)
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos a b σ φ), abs_of_pos (tw_pos a b 0 φ)]
      have h1 := tw_le_tw_zero (a := a) hb hσ φ
      calc |H φ| * Real.exp (quadE K φ) * tw a b σ φ ≤
          |H φ| * Real.exp (quadE K φ) * (Real.exp (Fintype.card ι * C₀) * tw a b 0 φ) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (hE1 σ hσ)
              (tw_pos a b 0 φ).le)) (by positivity)
        _ = _ := by ring
    · have : Continuous fun σ : ι → ℝ => H φ * Real.exp (quadE K φ) * tw a b σ φ := by
        unfold tw fq; fun_prop
      exact this.continuousOn
  · calc |tI K a b σ H| ≤ Real.exp (-∑ x, fq a b (σ x)) * N := abs_tI_le hb hint hσ hH
      _ ≤ Real.exp (Fintype.card ι * C₀) * Real.exp (-(c' * ∑ x, σ x)) * N :=
          mul_le_mul_of_nonneg_right (hE σ hσ) hN0
      _ = _ := by ring

/-- **L1.** For admissible G with admissible partials G' j (no cone condition needed), on the
orthant:  [φ_i G]_τ = Σ_x Rop_ix(σ ↦ [∂_x G]_σ)(τ),  J = K + Kᵀ, in the class c' (> row sums,
f(t) ≥ c't − C₀). Proof: `tI_ibp` says D_i(τ) = [φ_i G]_τ solves the Volterra equation with source
vector (σ ↦ [∂_x G]_σ)_x; uniqueness and `RopV_eq_sum`. -/
theorem tI_eq_Rop {K : ι → ι → ℝ} (hK : ∀ x y, 0 ≤ K x y) {a b : ℝ} (hb : 0 ≤ b)
    (hab : 0 < b ∨ 0 < a) {Ψ : (ι → ℝ) → ℝ}
    (hint : ∀ H, Adm Ψ H → Integrable fun φ => H φ * Real.exp (quadE K φ) * tw a b 0 φ)
    {r c' C₀ : ℝ} (hr0 : 0 ≤ r) (hrc : r < c') (hrow : ∀ i, ∑ k, (K i k + K k i) ≤ r)
    (hf : ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq a b t)
    {G : (ι → ℝ) → ℝ} {G' : ι → (ι → ℝ) → ℝ} (hG : Adm Ψ G) (hG'a : ∀ j, Adm Ψ (G' j))
    (hG' : ∀ j φ, HasLineDerivAt ℝ G (G' j φ) φ (Pi.single j 1)) (i : ι) {τ : ι → ℝ}
    (hτ : ∀ x, 0 ≤ τ x) :
    tI K a b τ (fun φ => φ i * G φ) =
      ∑ x, Rop (fun i k => K i k + K k i) c' i x (fun σ => tI K a b σ (G' x)) τ := by
  have hc' : 0 < c' := lt_of_le_of_lt hr0 hrc
  have hJ : ∀ i k, 0 ≤ K i k + K k i := fun i k => add_nonneg (hK i k) (hK k i)
  have hh : ∀ x, sk1_Cls c' (fun σ => tI K a b σ (G' x)) :=
    fun x => sk1_tI_cls hb hint hc' hf (hG'a x)
  have hD : sk1_Sol (fun i k => K i k + K k i) c' (fun x σ => tI K a b σ (G' x))
      (fun i σ => tI K a b σ (fun φ => φ i * G φ)) :=
    ⟨fun i => sk1_tI_cls hb hint hc' hf (hG.mul_coord i),
      fun i σ hσ => tI_ibp hb hab hint hσ i hG (hG'a i) (hG' i)⟩
  rw [← RopV_eq_sum hJ hc' hr0 hrc hrow hh i τ hτ]
  exact (RopV_eq hJ hc' hr0 hrc hrow hh hD i τ hτ).symm

end PP2SGD

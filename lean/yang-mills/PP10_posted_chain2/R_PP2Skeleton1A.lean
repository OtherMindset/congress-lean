import LongTable.P_mwwjem2s_tf34yn

/-!
Part A of PP2Skeleton1 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Skeleton1.lean)
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

end PP2SGD

end

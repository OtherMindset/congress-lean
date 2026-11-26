import LongTable.PP2OSShift
import LongTable.PP2SemigroupGap

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Hamiltonian track H, session 5
(plan item P3 and the `OSGap` assembly). The gap clause on the OS Hilbert space of sessions 3–4
from clustering of Z, density of the compactly supported positive-time vectors from continuity
of Z, and the assembly `OSGap` / `HamiltonianGap`.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* Kernel identity (`osg_connected_entry`). For positive-time f, g and s ≥ 0, with Ω = ψ 0:
  ⟪ψf, T(s)ψg⟫ − ⟪ψf, Ω⟫⟪Ω, ψg⟫ = Z(−Θf + τ_s g) − Z(−Θf)·Z(τ_s g).
  (⟪ψf, Ω⟫ = Z(0 − Θf), ⟪Ω, ψg⟫ = Z(g − Θ0) = Z(g) = Z(τ_s g) by translation invariance.)
  This is EXACTLY the expression bounded by `ClustersAt Z m` with the pair (−Θf, g) and
  a = (s, 0), distance max(|s|, 0) = s. No Hermiticity Z(−h) = conj Z(h) is used. Clustering
  is applied only to compactly supported f, g (−Θf is compactly supported with f:
  `osg_hasCompactSupport_negRefl`). So `ClustersAt Z m` as stated in the target suffices; no
  extra clustering hypothesis is needed.
* Sesquilinear extension (`osg_dec_span`): the connected form
  B_s(v, w) = ⟪v, T(s)w⟫ − ⟪v, Ω⟫⟪Ω, w⟫ satisfies ‖B_s(v, w)‖ ≤ C e^(−ms) (s ≥ 0) for all v, w in
  the span of ψ(compactly supported positive-time f) (double span induction).
  `osg_proj_inner`: for P⊥v = v − ⟪Ω, v⟫Ω, ⟪P⊥v, T(s)P⊥v⟫ = B_s(v, v).
* Density (`osg_dense_compact`). Hypotheses: a real seminorm p on TestFn with
  ‖Z f − Z g‖ ≤ C·p(f − g) (`hcont`; e.g. p = `PP2Limit.schwartzSup a b`, the form of
  `UniformEquicont` passed to a limit point), and `CompactApprox p`: every positive-time f is a
  p-limit of compactly supported positive-time g. Then span ψ(positive-time, compact support)
  is dense, via ‖ψf − ψg‖² = Z(f−Θf) − Z(g−Θf) − Z(f−Θg) + Z(g−Θg) ≤ 2C·p(f − g)
  (`osg_psi_dist_sq`; Θ-continuity of p is NOT needed: the reflected argument is the same in each
  pair of terms).
* Gap (`osg_gap`): ‖T(t)u‖ ≤ e^(−mt)‖u‖ for t ≥ 0, u ⊥ Ω, by `PP2Gap.semigroup_gap` with
  D = P⊥(span ψ(compact positive-time)).
* Assembly: `osGap_of` (exact `OSGap` shape of PP2TargetV4) and `hamiltonianGap_of`
  (`HamiltonianGap Z m`), from: `OSPositive Z`, time-translation invariance, ‖Z h‖ ≤ 1,
  Z 0 = 1, `hcont` for some seminorm p, `CompactApprox p`, `ClustersAt Z m`.
  Bonus `osg_vacuum_unique`: for m > 0, T(t)u = u for all t ≥ 0 ⇒ u ∈ ℂΩ.

NOT formalized.
* `CompactApprox (schwartzSup a b)`: cut-offs χ(x/R)·f → f in every Schwartz seminorm (Leibniz
  rule plus decay of f; χ(x/R) f keeps positive time). Standard but not done; it is an explicit
  hypothesis here.
* Continuity of a limit point Z in a Schwartz seminorm (from `UniformEquicont`, PP2Limit): an
  input, as is clustering (from `FiniteCutoffClustering` via `limitPoint_clusters`).
* No generator H, no strong continuity of T.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2OSGap

open PP2Target PP2RP2 PP2OSRecon PP2OSShift

/-- Every positive-time test function is a p-limit of compactly supported positive-time ones. -/
def CompactApprox (p : Seminorm ℝ TestFn) : Prop :=
  ∀ f : TestFn, PositiveTime f → ∀ ε > 0,
    ∃ g : TestFn, PositiveTime g ∧ HasCompactSupport ⇑g ∧ p (f - g) < ε

/-- Positive-time, compactly supported test functions. -/
def osg_G : Set TestFn := {f | PositiveTime f ∧ HasCompactSupport ⇑f}

theorem osg_hasCompactSupport_negRefl {f : TestFn} (hf : HasCompactSupport ⇑f) :
    HasCompactSupport ⇑(-reflect f) := by
  have h : HasCompactSupport (⇑f ∘ ⇑timeRefl.toHomeomorph) := hf.comp_homeomorph _
  have e : ⇑(reflect f) = ⇑f ∘ ⇑timeRefl.toHomeomorph := rfl
  show HasCompactSupport (-⇑(reflect f))
  rw [e]
  exact h.neg

section Main

variable (Z : TestFn → ℂ) (hZ : OSPositive Z)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h)
    (hb : ∀ h, ‖Z h‖ ≤ 1)

/-- The connected form B_s(v, w) = ⟪v, T s w⟫ − ⟪v, Ω⟫⟪Ω, w⟫. -/
def osg_B (s : ℝ) (v w : OSHilbert Z hZ) : ℂ :=
  ⟪v, oss_OST Z hZ htr hb s w⟫_ℂ - ⟪v, osr_psi Z hZ 0⟫_ℂ * ⟪osr_psi Z hZ 0, w⟫_ℂ

/-- Decay of the connected form at rate m. -/
def osg_Dec (m : ℝ) (v w : OSHilbert Z hZ) : Prop :=
  ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → ‖osg_B Z hZ htr hb s v w‖ ≤ C * Real.exp (-m * s)

theorem osg_B_add_left (s : ℝ) (v v' w : OSHilbert Z hZ) :
    osg_B Z hZ htr hb s (v + v') w = osg_B Z hZ htr hb s v w + osg_B Z hZ htr hb s v' w := by
  simp only [osg_B, inner_add_left]; ring

theorem osg_B_add_right (s : ℝ) (v w w' : OSHilbert Z hZ) :
    osg_B Z hZ htr hb s v (w + w') = osg_B Z hZ htr hb s v w + osg_B Z hZ htr hb s v w' := by
  simp only [osg_B, map_add, inner_add_right]; ring

theorem osg_B_smul_left (s : ℝ) (c : ℂ) (v w : OSHilbert Z hZ) :
    osg_B Z hZ htr hb s (c • v) w = conj c * osg_B Z hZ htr hb s v w := by
  simp only [osg_B, inner_smul_left]; ring

theorem osg_B_smul_right (s : ℝ) (c : ℂ) (v w : OSHilbert Z hZ) :
    osg_B Z hZ htr hb s v (c • w) = c * osg_B Z hZ htr hb s v w := by
  simp only [osg_B, map_smul, inner_smul_right]; ring

theorem osg_B_zero_left (s : ℝ) (w : OSHilbert Z hZ) : osg_B Z hZ htr hb s 0 w = 0 := by
  simp [osg_B]

theorem osg_B_zero_right (s : ℝ) (v : OSHilbert Z hZ) : osg_B Z hZ htr hb s v 0 = 0 := by
  simp [osg_B]

/-- The OS matrix elements of T (the sixth clause of `oss_OS_main`, without Z 0 = 1). -/
theorem osg_inner_T {f g : TestFn} (hf : PositiveTime f) (hg : PositiveTime g) {t : ℝ}
    (ht : 0 ≤ t) :
    ⟪osr_psi Z hZ f, oss_OST Z hZ htr hb t (osr_psi Z hZ g)⟫_ℂ =
      Z (PP2Target.translate (timeShift t) g - reflect f) := by
  show ⟪osr_psi Z hZ f, oss_T _ t (osr_psi Z hZ g)⟫_ℂ = _
  rw [oss_psi_pos Z hZ hf, oss_psi_pos Z hZ hg, oss_T_inner_vec _ ht]
  show Z (oss_tau (max t 0) g - reflect f) = _
  rw [max_eq_left ht]

/-- The connected kernel entry: exactly the clustering expression for (−Θf, g), a = (s, 0). -/
theorem osg_connected_entry {f g : TestFn} (hf : PositiveTime f) (hg : PositiveTime g)
    {s : ℝ} (hs : 0 ≤ s) :
    osg_B Z hZ htr hb s (osr_psi Z hZ f) (osr_psi Z hZ g) =
      Z (-reflect f + PP2Target.translate (timeShift s) g)
        - Z (-reflect f) * Z (PP2Target.translate (timeShift s) g) := by
  rw [osg_B, osg_inner_T Z hZ htr hb hf hg hs, osr_psi_inner Z hZ hf positiveTime_zero,
    osr_psi_inner Z hZ positiveTime_zero hg, map_zero, sub_zero, zero_sub, htr,
    sub_eq_neg_add (PP2Target.translate (timeShift s) g)]

/-- Clustering gives decay of the connected form on generators. -/
theorem osg_dec_gen {m : ℝ} (hcl : ClustersAt Z m) {f g : TestFn} (hf : f ∈ osg_G)
    (hg : g ∈ osg_G) : osg_Dec Z hZ htr hb m (osr_psi Z hZ f) (osr_psi Z hZ g) := by
  obtain ⟨C, hC⟩ := hcl (-reflect f) g (osg_hasCompactSupport_negRefl hf.2) hg.2
  refine ⟨C, fun s hs => ?_⟩
  rw [osg_connected_entry Z hZ htr hb hf.1 hg.1 hs]
  have e : max |timeShift s 0| |timeShift s 1| = s := by
    simp [timeShift, abs_of_nonneg hs, hs]
  have := hC (timeShift s)
  rwa [e] at this

theorem osg_dec_zero_left (m : ℝ) (w : OSHilbert Z hZ) : osg_Dec Z hZ htr hb m 0 w :=
  ⟨0, fun s _ => by rw [osg_B_zero_left, norm_zero, zero_mul]⟩

theorem osg_dec_zero_right (m : ℝ) (v : OSHilbert Z hZ) : osg_Dec Z hZ htr hb m v 0 :=
  ⟨0, fun s _ => by rw [osg_B_zero_right, norm_zero, zero_mul]⟩

theorem osg_dec_add_left {m : ℝ} {v v' w : OSHilbert Z hZ} (h : osg_Dec Z hZ htr hb m v w)
    (h' : osg_Dec Z hZ htr hb m v' w) : osg_Dec Z hZ htr hb m (v + v') w := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', fun s hs => ?_⟩
  rw [osg_B_add_left, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC s hs) (hC' s hs))

theorem osg_dec_add_right {m : ℝ} {v w w' : OSHilbert Z hZ} (h : osg_Dec Z hZ htr hb m v w)
    (h' : osg_Dec Z hZ htr hb m v w') : osg_Dec Z hZ htr hb m v (w + w') := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', fun s hs => ?_⟩
  rw [osg_B_add_right, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC s hs) (hC' s hs))

theorem osg_dec_smul_left {m : ℝ} (c : ℂ) {v w : OSHilbert Z hZ}
    (h : osg_Dec Z hZ htr hb m v w) : osg_Dec Z hZ htr hb m (c • v) w := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖c‖ * C, fun s hs => ?_⟩
  rw [osg_B_smul_left, norm_mul, Complex.norm_conj, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC s hs) (norm_nonneg c)

theorem osg_dec_smul_right {m : ℝ} (c : ℂ) {v w : OSHilbert Z hZ}
    (h : osg_Dec Z hZ htr hb m v w) : osg_Dec Z hZ htr hb m v (c • w) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖c‖ * C, fun s hs => ?_⟩
  rw [osg_B_smul_right, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC s hs) (norm_nonneg c)

/-- The span of ψ(compactly supported positive-time test functions). -/
abbrev osg_V : Submodule ℂ (OSHilbert Z hZ) := Submodule.span ℂ (osr_psi Z hZ '' osg_G)

/-- Decay of the connected form on the whole span (sesquilinear extension). -/
theorem osg_dec_span {m : ℝ} (hcl : ClustersAt Z m) {v w : OSHilbert Z hZ}
    (hv : v ∈ osg_V Z hZ) (hw : w ∈ osg_V Z hZ) : osg_Dec Z hZ htr hb m v w := by
  have hleft : ∀ g ∈ osg_G, ∀ v ∈ osg_V Z hZ, osg_Dec Z hZ htr hb m v (osr_psi Z hZ g) := by
    intro g hg v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact osg_dec_gen Z hZ htr hb hcl hf hg
    | zero => exact osg_dec_zero_left Z hZ htr hb m _
    | add x y _ _ hx hy => exact osg_dec_add_left Z hZ htr hb hx hy
    | smul a x _ hx => exact osg_dec_smul_left Z hZ htr hb a hx
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hleft g hg v hv
  | zero => exact osg_dec_zero_right Z hZ htr hb m _
  | add x y _ _ hx hy => exact osg_dec_add_right Z hZ htr hb hx hy
  | smul a x _ hx => exact osg_dec_smul_right Z hZ htr hb a hx

theorem osg_vac_inner (h0 : Z 0 = 1) :
    ⟪osr_psi Z hZ 0, osr_psi Z hZ 0⟫_ℂ = 1 := by
  rw [osr_psi_inner Z hZ positiveTime_zero positiveTime_zero, map_zero, sub_zero, h0]

theorem osg_T_vac {s : ℝ} (hs : 0 ≤ s) :
    oss_OST Z hZ htr hb s (osr_psi Z hZ 0) = osr_psi Z hZ 0 := by
  show oss_T _ s (osr_psi Z hZ 0) = osr_psi Z hZ 0
  rw [oss_psi_pos Z hZ positiveTime_zero, oss_T_vec _ hs]
  congr 1

/-- The vacuum-subtracted vector P⊥v = v − ⟪Ω, v⟫Ω. -/
def osg_proj (v : OSHilbert Z hZ) : OSHilbert Z hZ :=
  v - ⟪osr_psi Z hZ 0, v⟫_ℂ • osr_psi Z hZ 0

/-- ⟪P⊥v, T(s)P⊥v⟫ is the connected form B_s(v, v). -/
theorem osg_proj_inner (h0 : Z 0 = 1) {s : ℝ} (hs : 0 ≤ s) (v : OSHilbert Z hZ) :
    ⟪osg_proj Z hZ v, oss_OST Z hZ htr hb s (osg_proj Z hZ v)⟫_ℂ = osg_B Z hZ htr hb s v v := by
  have hTΩ := osg_T_vac Z hZ htr hb hs
  have hΩΩ := osg_vac_inner Z hZ h0
  have hΩT : ⟪osr_psi Z hZ 0, oss_OST Z hZ htr hb s v⟫_ℂ = ⟪osr_psi Z hZ 0, v⟫_ℂ := by
    show ⟪osr_psi Z hZ 0, oss_T _ s v⟫_ℂ = _
    rw [← oss_T_symm _ hs]; exact congrArg (fun x => ⟪x, v⟫_ℂ) hTΩ
  have hvΩ : ⟪v, osr_psi Z hZ 0⟫_ℂ = conj ⟪osr_psi Z hZ 0, v⟫_ℂ := (inner_conj_symm _ _).symm
  rw [osg_proj, osg_B, map_sub, map_smul, hTΩ, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, hΩT, hΩΩ, hvΩ]
  ring

/-- **Gap clause.** -/
theorem osg_gap (h0 : Z 0 = 1) {m : ℝ} (hcl : ClustersAt Z m)
    (hdense : Dense ((osg_V Z hZ) : Set (OSHilbert Z hZ))) :
    ∀ t : ℝ, 0 ≤ t → ∀ u : OSHilbert Z hZ, ⟪osr_psi Z hZ 0, u⟫_ℂ = 0 →
      ‖oss_OST Z hZ htr hb t u‖ ≤ Real.exp (-m * t) * ‖u‖ := by
  obtain ⟨hΩ, hsa, -, hmul, hfix, -, -, -⟩ := oss_OS_main Z hZ htr hb h0
  have hΩΩ := osg_vac_inner Z hZ h0
  refine PP2Gap.semigroup_gap (𝕜 := ℂ) (oss_OST Z hZ htr hb) hsa hmul (osr_psi Z hZ 0) hΩ hfix m
    (osg_proj Z hZ '' (osg_V Z hZ : Set (OSHilbert Z hZ))) ?_ ?_ ?_
  · rintro _ ⟨v, -, rfl⟩
    rw [osg_proj, inner_sub_right, inner_smul_right, hΩΩ, mul_one, sub_self]
  · intro u hu
    have hc : Continuous (osg_proj Z hZ) := by
      unfold osg_proj; fun_prop
    have hu' : osg_proj Z hZ u = u := by rw [osg_proj, hu, zero_smul, sub_zero]
    rw [← hu']
    exact mem_closure_image hc.continuousAt (hdense u)
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨C, hC⟩ := osg_dec_span Z hZ htr hb hcl hv hv
    refine ⟨C, fun s hs => ?_⟩
    rw [osg_proj_inner Z hZ htr hb h0 hs]
    exact (RCLike.re_le_norm _).trans (hC s hs)

end Main

section Density

variable (Z : TestFn → ℂ) (hZ : OSPositive Z)

/-- ‖ψf − ψg‖² ≤ 2C·p(f − g) under ‖Z a − Z b‖ ≤ C·p(a − b). -/
theorem osg_psi_dist_sq (p : Seminorm ℝ TestFn) {C : ℝ}
    (hcont : ∀ a b : TestFn, ‖Z a - Z b‖ ≤ C * p (a - b))
    {f g : TestFn} (hf : PositiveTime f) (hg : PositiveTime g) :
    ‖osr_psi Z hZ f - osr_psi Z hZ g‖ ^ 2 ≤ 2 * C * p (f - g) := by
  have h := @norm_sq_eq_re_inner ℂ (OSHilbert Z hZ) _ _ _ (osr_psi Z hZ f - osr_psi Z hZ g)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, osr_psi_inner Z hZ hf hf,
    osr_psi_inner Z hZ hf hg, osr_psi_inner Z hZ hg hf, osr_psi_inner Z hZ hg hg] at h
  rw [h]
  have e : Z (f - reflect f) - Z (g - reflect f) - (Z (f - reflect g) - Z (g - reflect g)) =
      (Z (f - reflect f) - Z (g - reflect f)) + (Z (g - reflect g) - Z (f - reflect g)) := by ring
  rw [e]
  have h1 := hcont (f - reflect f) (g - reflect f)
  have h2 := hcont (g - reflect g) (f - reflect g)
  rw [sub_sub_sub_cancel_right] at h1 h2
  rw [map_sub_rev p g f] at h2
  calc RCLike.re ((Z (f - reflect f) - Z (g - reflect f)) + (Z (g - reflect g) - Z (f - reflect g)))
      ≤ ‖(Z (f - reflect f) - Z (g - reflect f)) + (Z (g - reflect g) - Z (f - reflect g))‖ :=
        RCLike.re_le_norm _
    _ ≤ ‖Z (f - reflect f) - Z (g - reflect f)‖ + ‖Z (g - reflect g) - Z (f - reflect g)‖ :=
        norm_add_le _ _
    _ ≤ 2 * C * p (f - g) := by linarith

/-- **Density** of span ψ(positive-time, compact support), from continuity of Z in a seminorm p
and `CompactApprox p`. -/
theorem osg_dense_compact (p : Seminorm ℝ TestFn)
    (hcont : ∃ C : ℝ, ∀ a b : TestFn, ‖Z a - Z b‖ ≤ C * p (a - b)) (happ : CompactApprox p) :
    Dense ((Submodule.span ℂ (osr_psi Z hZ '' {f | PositiveTime f ∧ HasCompactSupport ⇑f}))
      : Set (OSHilbert Z hZ)) := by
  obtain ⟨C, hC⟩ := hcont
  set V := Submodule.span ℂ (osr_psi Z hZ '' {f | PositiveTime f ∧ HasCompactSupport ⇑f})
  have hmem : ∀ f, PositiveTime f → osr_psi Z hZ f ∈ closure (V : Set (OSHilbert Z hZ)) := by
    intro f hf
    rw [Metric.mem_closure_iff]
    intro ε hε
    set K : ℝ := 2 * (|C| + 1) with hK
    have hKpos : 0 < K := by positivity
    obtain ⟨g, hg, hgc, hpg⟩ := happ f hf (ε ^ 2 / K) (by positivity)
    refine ⟨osr_psi Z hZ g, Submodule.subset_span ⟨g, ⟨hg, hgc⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have hd := osg_psi_dist_sq Z hZ p hC hf hg
    have hp0 : 0 ≤ p (f - g) := apply_nonneg p _
    have h1 : 2 * C * p (f - g) ≤ K * p (f - g) := by
      rw [hK]; apply mul_le_mul_of_nonneg_right _ hp0; linarith [le_abs_self C]
    have h2 : K * p (f - g) < ε ^ 2 := by
      rwa [lt_div_iff₀ hKpos, mul_comm] at hpg
    have h3 : ‖osr_psi Z hZ f - osr_psi Z hZ g‖ ^ 2 < ε ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  have hsub : (Submodule.span ℂ (osr_psi Z hZ '' {f | PositiveTime f}) : Set (OSHilbert Z hZ)) ⊆
      closure (V : Set (OSHilbert Z hZ)) := by
    rw [← Submodule.topologicalClosure_coe]
    apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    rw [Submodule.topologicalClosure_coe]
    exact hmem f hf
  exact Dense.of_closure ((osr_psi_dense Z hZ).mono hsub)

end Density

/-! ## Assembly -/

/-- **Assembly, `OSGap` shape.** OS positivity, time-translation invariance, |Z| ≤ 1, Z 0 = 1,
continuity in a seminorm p with compact approximation in p, and clustering at rate m give the
OS-reconstruction gap statement of PP2TargetV4. -/
theorem osGap_of (Z : TestFn → ℂ) (m : ℝ) (hZ : OSPositive Z)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h)
    (hb : ∀ h, ‖Z h‖ ≤ 1) (h0 : Z 0 = 1) (p : Seminorm ℝ TestFn)
    (hcont : ∃ C : ℝ, ∀ f g : TestFn, ‖Z f - Z g‖ ≤ C * p (f - g)) (happ : CompactApprox p)
    (hcl : ClustersAt Z m) :
    OSGap Z (fun f => reflect f) (fun t g => PP2Target.translate (timeShift t) g) PositiveTime
      (fun f => PositiveTime f ∧ HasCompactSupport ⇑f) m := by
  obtain ⟨hΩ, hsa, hT0, hmul, hfix, hmat, -, -⟩ := oss_OS_main Z hZ htr hb h0
  have hdense := osg_dense_compact Z hZ p hcont happ
  exact ⟨OSHilbert Z hZ, inferInstance, inferInstance, inferInstance, osr_psi Z hZ 0,
    oss_OST Z hZ htr hb, osr_psi Z hZ, hΩ, hsa, hT0, hmul, hfix, rfl, hmat, hdense,
    osg_gap Z hZ htr hb h0 hcl hdense⟩

/-- **Assembly, `HamiltonianGap` form.** -/
theorem hamiltonianGap_of (Z : TestFn → ℂ) (m : ℝ) (hZ : OSPositive Z)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h)
    (hb : ∀ h, ‖Z h‖ ≤ 1) (h0 : Z 0 = 1) (p : Seminorm ℝ TestFn)
    (hcont : ∃ C : ℝ, ∀ f g : TestFn, ‖Z f - Z g‖ ≤ C * p (f - g)) (happ : CompactApprox p)
    (hcl : ClustersAt Z m) : HamiltonianGap Z m :=
  osGap_of Z m hZ htr hb h0 p hcont happ hcl

/-- **Uniqueness of the vacuum** (m > 0): vectors fixed by every T(t), t ≥ 0, are multiples of Ω. -/
theorem osg_vacuum_unique (Z : TestFn → ℂ) (m : ℝ) (hm : 0 < m) (hZ : OSPositive Z)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h)
    (hb : ∀ h, ‖Z h‖ ≤ 1) (h0 : Z 0 = 1) (p : Seminorm ℝ TestFn)
    (hcont : ∃ C : ℝ, ∀ f g : TestFn, ‖Z f - Z g‖ ≤ C * p (f - g)) (happ : CompactApprox p)
    (hcl : ClustersAt Z m) (u : OSHilbert Z hZ)
    (hu : ∀ t, 0 ≤ t → oss_OST Z hZ htr hb t u = u) :
    u = ⟪osr_psi Z hZ 0, u⟫_ℂ • osr_psi Z hZ 0 := by
  have hgap := osg_gap Z hZ htr hb h0 hcl (osg_dense_compact Z hZ p hcont happ)
  set Ω := osr_psi Z hZ 0
  have hΩΩ := osg_vac_inner Z hZ h0
  set w := u - ⟪Ω, u⟫_ℂ • Ω with hw
  have hwp : ⟪Ω, w⟫_ℂ = 0 := by rw [hw, inner_sub_right, inner_smul_right, hΩΩ, mul_one, sub_self]
  have hwfix : oss_OST Z hZ htr hb 1 w = w := by
    rw [hw, map_sub, map_smul, hu 1 zero_le_one, osg_T_vac Z hZ htr hb zero_le_one]
  have hb1 := hgap 1 zero_le_one w hwp
  rw [hwfix] at hb1
  have hlt : Real.exp (-m * 1) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hw0 : ‖w‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  have : w = 0 := norm_eq_zero.mp hw0
  rw [hw, sub_eq_zero] at this
  exact this

end PP2OSGap

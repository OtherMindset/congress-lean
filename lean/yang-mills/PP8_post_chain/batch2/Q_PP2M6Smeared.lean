import LongTable.P_mwwgf2cx_iollxj

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2M6Smeared.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M6.
The route reviewer's fix for the M6 gap of `PP2SimonLieb`: the pointwise `UniformBaseBound`
(twoPt ≤ K at physical distance ≥ 1, uniformly in ε) is replaced by a SMEARED bound, driven by a
region-susceptibility input, and the clustering conditional is rewired to consume smeared decay.

DEFINITIONS (the statement).
* `SimonLiebIneq' m₀ λ`: for every n, k, region B and x ∈ B (any y),
    twoPt x y ≤ regionTwoPt B x y + Σ_{u∈B} Σ_{v∈Bᶜ} bondJ u v · regionTwoPt B x u · twoPt v y.
  (For y ∉ B the first term is 0, so this contains `SimonLiebIneq`: `simonLiebIneq_of'`.)
* `RegionSusceptibility m₀ λ l A`: ε² Σ_y regionTwoPt (physBall x l) x y ≤ A, uniformly in n, k, x.
* `UniformSmearedDecay m₀ λ C₀ m`: for every weight 0 ≤ w ≤ 1 whose support is at physical
  sup-distance ≥ D from x, ε² Σ_y w y · twoPt x y ≤ C₀ e^{−mD} (any real D).
* `M6Consumer'`: SimonLiebIneq' + RegionGriffithsI + SmallBoundarySum (0 < γ < 1)
  + RegionSusceptibility (A ≥ 0) ⟹ ∃ C₀ ≥ 0, m > 0, UniformSmearedDecay.

FORMALIZED here (no sorry; axioms propext, Classical.choice, Quot.sound).
* `regionTwoPt_out` (regionTwoPt B x y = 0 for y ∉ B), `simonLiebIneq_of'`.
* `smeared_step`: S_w(x) ≤ ε² Σ_y w_y regionTwoPt B x y + Σ_v W(x,v) S_w(v), with
  S_w(x) = ε² Σ_y w_y twoPt x y, B = physBall x l, W the Simon–Lieb exit kernel (`exitW`);
  `exitW_nonneg`, `exitW_sum_le` (Σ_v W ≤ γ), `exitW_loc` (W(x,v) ≠ 0 ⟹ d(x,v) ≤ l + ε ≤ l + 1).
* `smeared_base`: S_w(x) ≤ A/(1−γ) for all x (maximum principle: the maximiser M satisfies
  M ≤ A + γ max(M, 0)). No sign of twoPt is used.
* `smeared_decay`: if supp w is at distance ≥ N(l+1) from x then S_w(x) ≤ (A/(1−γ)) γ^N (the local
  term vanishes once the distance exceeds l).
* `m6Consumer' : M6Consumer'` (via `geom_le_exp`; C₀ = (A/(1−γ)) γ⁻¹, m = −log γ/(l+1)).
* `supDist_shift_lower`, `conditional_clustering'`: `conditional_clustering` with hG replaced by
  the smeared hypothesis for G (applied with w = |g(dpos · − a)|/(Mg + 1)); it no longer needs
  |ZD| ≤ 1 nor m ≥ 0 (smeared decay holds for every D, so no small-shift case).
* `clustering_of_simonLieb'`: SimonLiebIneq', RegionGriffithsI, SmallBoundarySum,
  RegionSusceptibility and Newman's inequality (G = twoPt) ⟹ FiniteCutoffClustering m₀ λ m, m > 0.

NOT formalized: every input is a hypothesis. SimonLiebIneq' (M3 route R1–R5, with the extra local
term), RegionGriffithsI (M2), SmallBoundarySum (M5, BFS (7.4)), RegionSusceptibility (the smeared
replacement for the base bound; for the Dirichlet ball of radius l it is an ε-uniform statement
about a fixed-size region, NOT proved here), and Newman's inequality (M7) are all UNPROVEN for the
interacting model.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## The statements -/

/-- **Simon–Lieb with the local term** (any y; for y ∉ B the local term vanishes). -/
def SimonLiebIneq' (m₀ lam : ℝ) : Prop :=
  ∀ (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k), x ∈ B →
    twoPt n k m₀ lam x y ≤ regionTwoPt n k m₀ lam B x y +
      ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * regionTwoPt n k m₀ lam B x u * twoPt n k m₀ lam v y

/-- **Region susceptibility:** the smeared two-point function of the Dirichlet ball of radius l is
bounded uniformly in the level, the volume and the centre. -/
def RegionSusceptibility (m₀ lam l A : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k),
    spacing n ^ 2 * ∑ y, regionTwoPt n k m₀ lam (physBall n k x l) x y ≤ A

/-- **Uniform smeared decay** of the two-point function. -/
def UniformSmearedDecay (m₀ lam C₀ m : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k) (w : DSite n k → ℝ) (D : ℝ),
    (∀ y, 0 ≤ w y ∧ w y ≤ 1) → (∀ y, w y ≠ 0 → D ≤ supDist (dpos n k x) (dpos n k y)) →
      spacing n ^ 2 * ∑ y, w y * twoPt n k m₀ lam x y ≤ C₀ * Real.exp (-m * D)

/-- **The smeared M6 consumer**, as a proposition (proved below as `m6Consumer'`). -/
def M6Consumer' : Prop :=
  ∀ m₀ lam l γ A : ℝ, 0 ≤ l → 0 < γ → γ < 1 → 0 ≤ A →
    SimonLiebIneq' m₀ lam → RegionGriffithsI m₀ lam → SmallBoundarySum m₀ lam l γ →
      RegionSusceptibility m₀ lam l A →
        ∃ C₀ m : ℝ, 0 ≤ C₀ ∧ 0 < m ∧ UniformSmearedDecay m₀ lam C₀ m

/-! ## SimonLiebIneq' contains SimonLiebIneq -/

theorem regionTwoPt_out (m₀ lam : ℝ) (B : Finset (DSite n k)) (x : DSite n k) {y : DSite n k}
    (hy : y ∉ B) : regionTwoPt n k m₀ lam B x y = 0 := by
  have h : ∀ ψ : {z // z ∈ B} → ℝ, zeroExt B ψ y = 0 := fun ψ => by simp [zeroExt, hy]
  simp [regionTwoPt, h]

theorem simonLiebIneq_of' {m₀ lam : ℝ} (h : SimonLiebIneq' m₀ lam) : SimonLiebIneq m₀ lam := by
  intro n k B x y hx hy
  have := h n k B x y hx
  rwa [regionTwoPt_out m₀ lam B x hy, zero_add] at this

/-! ## The smeared step -/

/-- The smeared two-point function S_w(x) = ε² Σ_y w_y ⟨φ_x φ_y⟩. -/
def smeared (n k : ℕ) (m₀ lam : ℝ) (w : DSite n k → ℝ) (x : DSite n k) : ℝ :=
  spacing n ^ 2 * ∑ y, w y * twoPt n k m₀ lam x y

/-- The Simon–Lieb exit kernel of the ball of radius l around x. -/
def exitW (n k : ℕ) (m₀ lam l : ℝ) (x v : DSite n k) : ℝ :=
  if v ∈ (physBall n k x l)ᶜ then
    ∑ u ∈ physBall n k x l, bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u
  else 0

theorem exitW_nonneg {m₀ lam l : ℝ} (hGI : RegionGriffithsI m₀ lam) (x v : DSite n k) :
    0 ≤ exitW n k m₀ lam l x v := by
  unfold exitW
  split_ifs with hv
  · refine Finset.sum_nonneg fun u hu => mul_nonneg (bondJ_nonneg ?_) (hGI _ _ _ _ _)
    rintro rfl; exact (Finset.mem_compl.mp hv) hu
  · exact le_refl _

theorem exitW_sum_le {m₀ lam l γ : ℝ} (hSmall : SmallBoundarySum m₀ lam l γ) (x : DSite n k) :
    ∑ v, exitW n k m₀ lam l x v ≤ γ := by
  unfold exitW
  rw [Fintype.sum_ite_mem, Finset.sum_comm]
  exact hSmall n k x

theorem exitW_loc {m₀ lam l : ℝ} {x v : DSite n k} (h : exitW n k m₀ lam l x v ≠ 0) :
    supDist (dpos n k x) (dpos n k v) ≤ l + 1 := by
  unfold exitW at h
  split_ifs at h with hvc
  · obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hJ : bondJ n k u v ≠ 0 := left_ne_zero_of_mul hne
    have h1 := mem_physBall.mp hu
    have h2 := (supDist_bondJ hJ).trans (spacing_le_one n)
    have t1 := supDist_triangle (dpos n k x) (dpos n k u) (dpos n k v)
    linarith
  · exact absurd rfl h

theorem triple_swap {α β γ' : Type*} [Fintype α] (s : Finset β) (t : Finset γ')
    (F : α → β → γ' → ℝ) :
    ∑ y, ∑ u ∈ s, ∑ v ∈ t, F y u v = ∑ v ∈ t, ∑ u ∈ s, ∑ y, F y u v := by
  calc ∑ y, ∑ u ∈ s, ∑ v ∈ t, F y u v = ∑ u ∈ s, ∑ y, ∑ v ∈ t, F y u v := Finset.sum_comm
    _ = ∑ u ∈ s, ∑ v ∈ t, ∑ y, F y u v := Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ v ∈ t, ∑ u ∈ s, ∑ y, F y u v := Finset.sum_comm

theorem smeared_step {m₀ lam l : ℝ} (hl : 0 ≤ l) (hSL : SimonLiebIneq' m₀ lam)
    {w : DSite n k → ℝ} (hw : ∀ y, 0 ≤ w y) (x : DSite n k) :
    smeared n k m₀ lam w x ≤
      spacing n ^ 2 * ∑ y, w y * regionTwoPt n k m₀ lam (physBall n k x l) x y
        + ∑ v, exitW n k m₀ lam l x v * smeared n k m₀ lam w v := by
  have hx : x ∈ physBall n k x l := mem_physBall.mpr (by rw [supDist_self]; exact hl)
  have h1 : ∀ y, w y * twoPt n k m₀ lam x y ≤
      w y * regionTwoPt n k m₀ lam (physBall n k x l) x y +
        ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
          bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u *
            (w y * twoPt n k m₀ lam v y) := by
    intro y
    calc w y * twoPt n k m₀ lam x y ≤ w y * (regionTwoPt n k m₀ lam (physBall n k x l) x y +
        ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
          bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u *
            twoPt n k m₀ lam v y) :=
          mul_le_mul_of_nonneg_left (hSL n k _ x y hx) (hw y)
      _ = _ := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
  have e : spacing n ^ 2 * ∑ y, ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
      bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u *
        (w y * twoPt n k m₀ lam v y)
      = ∑ v, exitW n k m₀ lam l x v * smeared n k m₀ lam w v := by
    simp only [exitW, smeared, ite_mul, zero_mul]
    rw [Fintype.sum_ite_mem]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [triple_swap]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  calc smeared n k m₀ lam w x
      ≤ spacing n ^ 2 * ∑ y, (w y * regionTwoPt n k m₀ lam (physBall n k x l) x y +
        ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
          bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u *
            (w y * twoPt n k m₀ lam v y)) := by
        unfold smeared
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => h1 y) (by positivity)
    _ = _ := by rw [Finset.sum_add_distrib, mul_add, e]

/-! ## (b) the base bound by a maximum principle -/

theorem smeared_base {m₀ lam l γ A : ℝ} (hl : 0 ≤ l) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hSus : RegionSusceptibility m₀ lam l A)
    {w : DSite n k → ℝ} (hw : ∀ y, 0 ≤ w y ∧ w y ≤ 1) (x : DSite n k) :
    smeared n k m₀ lam w x ≤ A / (1 - γ) := by
  obtain ⟨x₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (smeared n k m₀ lam w)
    ⟨x, Finset.mem_univ x⟩
  set M := smeared n k m₀ lam w x₀ with hM
  have hloc : spacing n ^ 2 * ∑ y, w y * regionTwoPt n k m₀ lam (physBall n k x₀ l) x₀ y ≤ A := by
    refine le_trans ?_ (hSus n k x₀)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun y _ => mul_le_of_le_one_left (hGI _ _ _ _ _) (hw y).2
  have hexit : ∑ v, exitW n k m₀ lam l x₀ v * smeared n k m₀ lam w v ≤ γ * max M 0 := by
    calc ∑ v, exitW n k m₀ lam l x₀ v * smeared n k m₀ lam w v
        ≤ ∑ v, exitW n k m₀ lam l x₀ v * max M 0 :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            ((hmax v (Finset.mem_univ v)).trans (le_max_left _ _)) (exitW_nonneg hGI _ _)
      _ = (∑ v, exitW n k m₀ lam l x₀ v) * max M 0 := by rw [Finset.sum_mul]
      _ ≤ γ * max M 0 := mul_le_mul_of_nonneg_right (exitW_sum_le hSmall x₀) (le_max_right _ _)
  have hstep := smeared_step hl hSL (fun y => (hw y).1) x₀
  have hMle : M ≤ A + γ * max M 0 := by rw [hM]; linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hfin : M ≤ A / (1 - γ) := by
    rcases le_or_gt M 0 with h | h
    · exact h.trans (div_nonneg hA h1γ.le)
    · rw [max_eq_left h.le] at hMle
      rw [le_div_iff₀ h1γ]; linarith
  exact (hmax x (Finset.mem_univ x)).trans hfin

/-! ## (c) iteration away from the support -/

theorem smeared_decay {m₀ lam l γ A : ℝ} (hl : 0 ≤ l) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hSus : RegionSusceptibility m₀ lam l A)
    {w : DSite n k → ℝ} (hw : ∀ y, 0 ≤ w y ∧ w y ≤ 1) :
    ∀ N : ℕ, ∀ x : DSite n k,
      (∀ y, w y ≠ 0 → (N : ℝ) * (l + 1) ≤ supDist (dpos n k x) (dpos n k y)) →
        smeared n k m₀ lam w x ≤ A / (1 - γ) * γ ^ N := by
  have hK : 0 ≤ A / (1 - γ) := div_nonneg hA (by linarith)
  intro N
  induction N with
  | zero =>
    intro x _
    simpa using smeared_base hl hγ1 hA hSL hGI hSmall hSus hw x
  | succ N ih =>
    intro x hx
    have hloc : spacing n ^ 2 * ∑ y, w y * regionTwoPt n k m₀ lam (physBall n k x l) x y = 0 := by
      rw [Finset.sum_eq_zero, mul_zero]
      intro y _
      by_cases hwy : w y = 0
      · rw [hwy, zero_mul]
      · have h := hx y hwy
        push_cast at h
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hy : y ∉ physBall n k x l := by
          rw [mem_physBall]; nlinarith
        rw [regionTwoPt_out m₀ lam _ x hy, mul_zero]
    have hstep := smeared_step hl hSL (fun y => (hw y).1) x
    rw [hloc, zero_add] at hstep
    calc smeared n k m₀ lam w x
        ≤ ∑ v, exitW n k m₀ lam l x v * smeared n k m₀ lam w v := hstep
      _ ≤ ∑ v, exitW n k m₀ lam l x v * (A / (1 - γ) * γ ^ N) := by
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : exitW n k m₀ lam l x v = 0
        · rw [hv, zero_mul, zero_mul]
        · apply mul_le_mul_of_nonneg_left _ (exitW_nonneg hGI _ _)
          apply ih
          intro y hwy
          have h := hx y hwy
          have hxv := exitW_loc hv
          have t := supDist_triangle (dpos n k x) (dpos n k v) (dpos n k y)
          push_cast at h
          nlinarith
      _ = (∑ v, exitW n k m₀ lam l x v) * (A / (1 - γ) * γ ^ N) := by rw [Finset.sum_mul]
      _ ≤ γ * (A / (1 - γ) * γ ^ N) :=
        mul_le_mul_of_nonneg_right (exitW_sum_le hSmall x) (by positivity)
      _ = A / (1 - γ) * γ ^ (N + 1) := by ring

/-! ## The smeared M6 consumer -/

/-- **The smeared M6 consumer holds.** -/
theorem m6Consumer' : M6Consumer' := by
  intro m₀ lam l γ A hl hγ0 hγ1 hA hSL hGI hSmall hSus
  have hK : 0 ≤ A / (1 - γ) := div_nonneg hA (by linarith)
  have hlog : 0 < -Real.log γ := neg_pos.mpr (Real.log_neg hγ0 hγ1)
  refine ⟨A / (1 - γ) * Real.exp (-Real.log γ * (0 / (l + 1) + 1)), -Real.log γ / (l + 1),
    by positivity, div_pos hlog (by linarith), ?_⟩
  intro n k x w D hw hD
  by_cases hD0 : 0 ≤ D
  · exact geom_le_exp hγ0 hγ1 (by linarith) hK hD0 fun N hN =>
      smeared_decay hl hγ0 hγ1 hA hSL hGI hSmall hSus hw N x fun y hy => by
        have := hD y hy; linarith
  · push Not at hD0
    have hb := smeared_base hl hγ1 hA hSL hGI hSmall hSus hw x
    have e1 : 1 ≤ Real.exp (-Real.log γ * (0 / (l + 1) + 1)) := by
      apply Real.one_le_exp; rw [zero_div, zero_add, mul_one]; exact hlog.le
    have e2 : 1 ≤ Real.exp (-(-Real.log γ / (l + 1)) * D) := by
      apply Real.one_le_exp
      have : 0 < -Real.log γ / (l + 1) := div_pos hlog (by linarith)
      nlinarith
    calc spacing n ^ 2 * ∑ y, w y * twoPt n k m₀ lam x y ≤ A / (1 - γ) := hb
      _ = A / (1 - γ) * 1 * 1 := by ring
      _ ≤ _ := by gcongr

/-! ## The clustering conditional with smeared decay -/

theorem supDist_shift_lower {R : ℝ} {p q a : Plane} (hp : |p 0| ≤ R ∧ |p 1| ≤ R)
    (hq : |q 0 - a 0| ≤ R ∧ |q 1 - a 1| ≤ R) : max |a 0| |a 1| - 2 * R ≤ supDist p q := by
  have h0 : |a 0| ≤ |a 0 - q 0| + |q 0 - p 0| + |p 0| := by
    calc |a 0| = |(a 0 - q 0) + (q 0 - p 0) + p 0| := by congr 1; ring
      _ ≤ _ := abs_add_three _ _ _
  have h1 : |a 1| ≤ |a 1 - q 1| + |q 1 - p 1| + |p 1| := by
    calc |a 1| = |(a 1 - q 1) + (q 1 - p 1) + p 1| := by congr 1; ring
      _ ≤ _ := abs_add_three _ _ _
  rw [abs_sub_comm (a 0) (q 0), abs_sub_comm (q 0) (p 0)] at h0
  rw [abs_sub_comm (a 1) (q 1), abs_sub_comm (q 1) (p 1)] at h1
  have d0 : |p 0 - q 0| ≤ supDist p q := le_max_left _ _
  have d1 : |p 1 - q 1| ≤ supDist p q := le_max_right _ _
  have : max |a 0| |a 1| ≤ supDist p q + 2 * R :=
    max_le (by linarith [hp.1, hq.1]) (by linarith [hp.2, hq.2])
  linarith

/-- **`conditional_clustering` with smeared decay:** hG is replaced by the smeared hypothesis for
G (the clustering proof only ever uses G smeared against |g|). No |ZD| ≤ 1 and no m ≥ 0 needed. -/
theorem conditional_clustering' {m₀ lam m C₀ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (G : ∀ n k : ℕ, DSite n k → DSite n k → ℝ)
    (hN : ∀ (n k : ℕ) (f g : TestFn),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) g‖
        ≤ κ * ∑ x : DSite n k, ∑ y : DSite n k,
            spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|) * G n k x y)
    (hGs : ∀ (n k : ℕ) (x : DSite n k) (w : DSite n k → ℝ) (D : ℝ),
      (∀ y, 0 ≤ w y ∧ w y ≤ 1) → (∀ y, w y ≠ 0 → D ≤ supDist (dpos n k x) (dpos n k y)) →
        spacing n ^ 2 * ∑ y, w y * G n k x y ≤ C₀ * Real.exp (-m * D)) :
    FiniteCutoffClustering m₀ lam m := by
  intro f g hf hg
  obtain ⟨Mf, Rf, hRf, hMf, hsf⟩ := bound_and_box f hf
  obtain ⟨Mg, Rg, hRg, hMg, hsg⟩ := bound_and_box g hg
  set R := max Rf Rg
  have hR : 0 ≤ R := le_max_of_le_left hRf
  have hsf' : ∀ p, f p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R := fun p hp =>
    ⟨(hsf p hp).1.trans (le_max_left _ _), (hsf p hp).2.trans (le_max_left _ _)⟩
  have hsg' : ∀ p, g p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R := fun p hp =>
    ⟨(hsg p hp).1.trans (le_max_right _ _), (hsg p hp).2.trans (le_max_right _ _)⟩
  have hMf0 : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf 0)
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hMg 0)
  have hMg1 : 0 < Mg + 1 := by linarith
  refine ⟨κ * (Mf * (2 * R + 1) ^ 2 * ((Mg + 1) * C₀ * Real.exp (m * (2 * R)))),
    fun n k a => ?_⟩
  set D := max |a 0| |a 1|
  set K' := (Mg + 1) * (C₀ * Real.exp (-m * (D - 2 * R))) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hinner : ∀ x : DSite n k, f (dpos n k x) ≠ 0 →
      spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G n k x y ≤ K' := by
    intro x hfx
    set w : DSite n k → ℝ := fun y => |g (dpos n k y - a)| / (Mg + 1) with hw
    have hw01 : ∀ y, 0 ≤ w y ∧ w y ≤ 1 := fun y =>
      ⟨div_nonneg (abs_nonneg _) hMg1.le,
        (div_le_one hMg1).mpr ((hMg _).trans (by linarith))⟩
    have hwD : ∀ y, w y ≠ 0 → D - 2 * R ≤ supDist (dpos n k x) (dpos n k y) := by
      intro y hy
      have hgy : g (dpos n k y - a) ≠ 0 := by
        intro h0; apply hy; simp [hw, h0]
      have hq := hsg' _ hgy
      simp only [PiLp.sub_apply] at hq
      exact supDist_shift_lower (hsf' _ hfx) hq
    have := hGs n k x w (D - 2 * R) hw01 hwD
    have e : spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G n k x y
        = (Mg + 1) * (spacing n ^ 2 * ∑ y, w y * G n k x y) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hw]
      field_simp
    rw [e, hK']
    exact mul_le_mul_of_nonneg_left this hMg1.le
  have htr : ∀ y : DSite n k, (translate a g) (dpos n k y) = g (dpos n k y - a) := by
    intro y; simp [translate, SchwartzMap.compSubConstCLM_apply]
  have hsumf := riemann_bound (fun p => f p) hMf hR hsf' n k 0
  simp only [sub_zero] at hsumf
  have hrw : ∑ x : DSite n k, ∑ y : DSite n k,
      spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |(translate a g) (dpos n k y)|)
        * G n k x y
      = ∑ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| *
          (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G n k x y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [htr]; ring
  have hterm : ∀ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| *
      (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G n k x y)
      ≤ spacing n ^ 2 * |f (dpos n k x)| * K' := by
    intro x
    by_cases hfx : f (dpos n k x) = 0
    · simp [hfx]
    · exact mul_le_mul_of_nonneg_left (hinner x hfx) (by positivity)
  have hexp : Real.exp (-m * (D - 2 * R)) = Real.exp (m * (2 * R)) * Real.exp (-m * D) := by
    rw [← Real.exp_add]; ring_nf
  calc _ ≤ _ := hN n k f (translate a g)
    _ = κ * ∑ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| *
          (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G n k x y) := by rw [hrw]
    _ ≤ κ * ∑ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| * K' :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hterm x) hκ
    _ = κ * ((spacing n ^ 2 * ∑ x : DSite n k, |f (dpos n k x)|) * K') := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ κ * ((Mf * (2 * R + 1) ^ 2) * K') := by gcongr
    _ = _ := by rw [hK', hexp]; ring

/-- **End-to-end conditional (smeared):** the inputs of `M6Consumer'` and Newman's inequality
(with G = twoPt) give finite-cutoff clustering at some rate m > 0. -/
theorem clustering_of_simonLieb' {m₀ lam l γ A κ : ℝ} (hl : 0 ≤ l) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hSus : RegionSusceptibility m₀ lam l A)
    (hN : ∀ (n k : ℕ) (f g : TestFn),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) g‖
        ≤ κ * ∑ x : DSite n k, ∑ y : DSite n k,
            spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|)
              * twoPt n k m₀ lam x y) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m := by
  obtain ⟨C₀, m, hC₀, hm, hdecay⟩ := m6Consumer' m₀ lam l γ A hl hγ0 hγ1 hA hSL hGI hSmall hSus
  exact ⟨m, hm, conditional_clustering' hC₀ hκ (fun n k => twoPt n k m₀ lam) hN hdecay⟩


end PP2Target

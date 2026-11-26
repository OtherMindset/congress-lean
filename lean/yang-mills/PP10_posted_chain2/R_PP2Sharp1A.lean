import LongTable.P_mwwlq07a_c2sp8h

/-!
Part A of PP2Sharp1 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Sharp1.lean)
Yang-Mills table, Long Table. Claude council, target T2 (continuum sharpness for φ⁴₂), step (a),
session 1: "susceptibility bounded uniformly in (ε, L) ⟹ exponential clustering uniform in (ε, L)"
for the quartic Dirichlet-box model, all λ ≥ 0, via Simon–Lieb averaged over ball radii.

FINDING (the ε-count). The proposed averaging does NOT close by itself. With the full two-point
function the boundary sum of B(x, r) is Σ_{u∈B, v∉B} J_uv ⟨φ_xφ_u⟩ (no ε² weight), the shells
{r − ε < d(x, u) ≤ r} are ε thin, and over M radii r_j = R₀ + jε they are disjoint, so
  Σ_{j<M} shellSum(r_j) ≤ 4 Σ_u ⟨φ_xφ_u⟩ ≤ 4K/ε²    (`sh1_sum_shell_le`),
and the best radius has shellSum ≤ 4K/(ε²M). Covering a physical window of width T takes
M = T/ε radii, giving 4K/(εT): one power of ε is missing, for every window. Griffiths II
(⟨·⟩_B ≤ ⟨·⟩) is what makes the region boundary sum ≤ the full one, and it is exactly the step that
discards the Dirichlet suppression ⟨φ_xφ_u⟩_B = O(ε) for u next to ∂B which supplies the missing ε
(free field: ⟨φ_xφ_u⟩_B ≈ ε ∂_n G_B). So the averaging gives (i) uniform clustering CONDITIONAL on
an ε-uniform Dirichlet boundary-suppression bound (stated below, unproven), and (ii) without it,
clustering at each FIXED spacing, uniformly in the volume, at a rate m_n ≈ ε log 2/(8K) → 0.

DEFINITIONS.
* `sh1_bdrySum n k m₀ λ x r` = Σ_{u∈B(x,r)} Σ_{v∉B(x,r)} bondJ u v ⟨φ_xφ_u⟩_{B(x,r)};
  `sh1_shellSum` the same with the full ⟨φ_xφ_u⟩.
* `VarSmallBoundarySum m₀ λ L γ`: ∀ n k x, ∃ r ∈ [0, L], sh1_bdrySum x r ≤ γ (per-centre radius).
* `DirichletSuppression m₀ λ R₀ C`: ∀ n k x, ∀ r ≥ R₀, sh1_bdrySum x r ≤ C ε sh1_shellSum x r.
* `LevelClustering m₀ λ n m`: `FiniteCutoffClustering` at the fixed level n (constant uniform in k).

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* **`sh1_regionTwoPt_le_twoPt`** (m₀ ≠ 0, λ ≥ 0): ⟨φ_xφ_u⟩_R ≤ ⟨φ_xφ_u⟩ for every region R
  (Griffiths II in the cone, A = φ_xφ_u, B = e^{bdry}, for the decoupled measure; via
  `regionTwoPt_eq_tI`, `twoPt_eq_tI`, `griffiths_second_cone`, `hint_dec`).
  Corollaries `sh1_bdrySum_le_shellSum`, **`sh1_regionSusceptibility`** (UniformSusceptibility K ⟹
  RegionSusceptibility l K for every l) and `clustering_of_smallBoundarySum_of_susceptibility`
  (the existing chain needs only SmallBoundarySum once χ is bounded).
* The generalised consumer: `sh1_decay`, **`sh1_level_consumer`** (fixed n, radius chosen per centre
  in [0, L], base bound = the susceptibility itself, no maximum principle and no region
  susceptibility), **`sh1_consumer`** (VarSmallBoundarySum + UniformSusceptibility + Simon–Lieb' +
  RegionGriffithsI ⟹ UniformSmearedDecay, m = −log γ/(L+1)), and
  **`clustering_of_varSmallBoundarySum`** (m₀ ≠ 0, λ ≥ 0 ⟹ ∃ m > 0, FiniteCutoffClustering).
* Averaging: `sh1_count_le_one`, `sh1_sum_ball`, `sh1_sum_shell_le`, **`sh1_exists_radius`**
  (∃ j < M, shellSum(R₀ + jε) ≤ 4 Σ_u ⟨φ_xφ_u⟩ / M).
* **`varSmallBoundarySum_of_suppression`** and
  **`clustering_of_uniformSusceptibility_of_suppression`**: m₀ ≠ 0, λ ≥ 0, R₀ ≥ 0, C ≥ 0,
  UniformSusceptibility m₀ λ K, DirichletSuppression m₀ λ R₀ C ⟹ ∃ m > 0, FiniteCutoffClustering
  (γ = 1/2, radius ≤ R₀ + ⌈8CK⌉ + 1).
* `sh1_conditional_clustering_level` (`conditional_clustering'` at a fixed level),
  `sh1_level_smallBoundarySum`, **`levelClustering_of_susceptibility`** (explicit rate
  log 2/(T_n ε + 1), T_n = ⌈8K/ε²⌉ + 1) and **`levelClustering_of_uniformSusceptibility`**.

NOT formalized: `DirichletSuppression` (an ε-uniform boundary-regularity statement for the
interacting Dirichlet ball measures, r ≥ R₀; plausible in the one-phase region, true in spirit for
the free field, UNPROVEN here). A naive proof via the Schwinger–Dyson sub-solution property fails:
the Wick counterterm −12λε²c (c ~ log ε⁻¹) per site accumulates over the (r/ε)² steps of the walk.
Hence `clustering_of_uniformSusceptibility` (unconditional, uniform in ε) is NOT reached.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Target

open PP2LocalTime PP2Griffiths PP2SGD

variable {n k : ℕ}

/-! ## Boundary sums -/

/-- The Simon–Lieb boundary sum of the ball B(x, r), with the REGION two-point function. -/
def sh1_bdrySum (n k : ℕ) (m₀ lam : ℝ) (x : DSite n k) (r : ℝ) : ℝ :=
  ∑ u ∈ physBall n k x r, ∑ v ∈ (physBall n k x r)ᶜ,
    bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x r) x u

/-- The same boundary sum with the FULL two-point function. -/
def sh1_shellSum (n k : ℕ) (m₀ lam : ℝ) (x : DSite n k) (r : ℝ) : ℝ :=
  ∑ u ∈ physBall n k x r, ∑ v ∈ (physBall n k x r)ᶜ,
    bondJ n k u v * twoPt n k m₀ lam x u

/-- **Per-centre small boundary sum:** every centre has SOME radius r ∈ [0, L] whose Simon–Lieb
boundary sum is at most γ (the radius may depend on n, k and x). -/
def VarSmallBoundarySum (m₀ lam L γ : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k), ∃ r : ℝ, 0 ≤ r ∧ r ≤ L ∧ sh1_bdrySum n k m₀ lam x r ≤ γ

/-- **Dirichlet boundary suppression** (UNPROVEN input): for every radius r ≥ R₀, the region
boundary sum is at most C ε times the full-measure boundary sum. -/
def DirichletSuppression (m₀ lam R₀ C : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k) (r : ℝ), R₀ ≤ r →
    sh1_bdrySum n k m₀ lam x r ≤ C * spacing n * sh1_shellSum n k m₀ lam x r

/-! ## The generalised consumer (per-centre radius, base bound from the susceptibility) -/

theorem sh1_exitW_sum (m₀ lam l : ℝ) (x : DSite n k) :
    ∑ v, exitW n k m₀ lam l x v = sh1_bdrySum n k m₀ lam x l := by
  unfold exitW sh1_bdrySum
  rw [Fintype.sum_ite_mem, Finset.sum_comm]

theorem sh1_smeared_le {m₀ lam K : ℝ} {x : DSite n k}
    (hK : spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y| ≤ K)
    {w : DSite n k → ℝ} (hw : ∀ y, 0 ≤ w y ∧ w y ≤ 1) :
    smeared n k m₀ lam w x ≤ K := by
  refine le_trans ?_ hK
  unfold smeared
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by positivity)
  rw [abs_of_nonneg (twoPt_nonneg m₀ lam x y)]
  exact mul_le_of_le_one_left (twoPt_nonneg m₀ lam x y) (hw y).2

/-- Iteration with a per-centre radius ρ x ∈ [0, L] (fixed n, k). -/
theorem sh1_decay {m₀ lam L γ K : ℝ} (hγ0 : 0 < γ) (hK0 : 0 ≤ K)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (ρ : DSite n k → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρL : ∀ x, ρ x ≤ L)
    (hργ : ∀ x, sh1_bdrySum n k m₀ lam x (ρ x) ≤ γ)
    {w : DSite n k → ℝ} (hw : ∀ y, 0 ≤ w y ∧ w y ≤ 1)
    (hbase : ∀ x, smeared n k m₀ lam w x ≤ K) :
    ∀ N : ℕ, ∀ x : DSite n k,
      (∀ y, w y ≠ 0 → (N : ℝ) * (L + 1) ≤ supDist (dpos n k x) (dpos n k y)) →
        smeared n k m₀ lam w x ≤ K * γ ^ N := by
  intro N
  induction N with
  | zero =>
    intro x _
    simpa using hbase x
  | succ N ih =>
    intro x hx
    have hloc : spacing n ^ 2 * ∑ y, w y * regionTwoPt n k m₀ lam (physBall n k x (ρ x)) x y
        = 0 := by
      rw [Finset.sum_eq_zero, mul_zero]
      intro y _
      by_cases hwy : w y = 0
      · rw [hwy, zero_mul]
      · have h := hx y hwy
        push_cast at h
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hL0 : 0 ≤ L := (hρ0 x).trans (hρL x)
        have hy : y ∉ physBall n k x (ρ x) := by
          rw [mem_physBall]; nlinarith [hρL x]
        rw [regionTwoPt_out m₀ lam _ x hy, mul_zero]
    have hstep := smeared_step (hρ0 x) hSL (fun y => (hw y).1) x
    rw [hloc, zero_add] at hstep
    calc smeared n k m₀ lam w x
        ≤ ∑ v, exitW n k m₀ lam (ρ x) x v * smeared n k m₀ lam w v := hstep
      _ ≤ ∑ v, exitW n k m₀ lam (ρ x) x v * (K * γ ^ N) := by
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : exitW n k m₀ lam (ρ x) x v = 0
        · rw [hv, zero_mul, zero_mul]
        · apply mul_le_mul_of_nonneg_left _ (exitW_nonneg hGI _ _)
          apply ih
          intro y hwy
          have h := hx y hwy
          have hxv := exitW_loc hv
          have t := supDist_triangle (dpos n k x) (dpos n k v) (dpos n k y)
          have := hρL x
          push_cast at h
          nlinarith
      _ = (∑ v, exitW n k m₀ lam (ρ x) x v) * (K * γ ^ N) := by rw [Finset.sum_mul]
      _ ≤ γ * (K * γ ^ N) := by
        rw [sh1_exitW_sum]
        exact mul_le_mul_of_nonneg_right (hργ x) (by positivity)
      _ = K * γ ^ (N + 1) := by ring

theorem sh1_K_nonneg {m₀ lam K : ℝ} (hK : UniformSusceptibility m₀ lam K) : 0 ≤ K := by
  have hpos : 0 < boxN 0 0 := by unfold boxN; positivity
  refine le_trans ?_ (hK 0 0 (⟨0, hpos⟩, ⟨0, hpos⟩))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => abs_nonneg _)

/-- **The generalised consumer at a fixed level n** (uniform in the volume k): Simon–Lieb',
Griffiths I for regions, a per-centre small boundary sum at level n (radius in [0, L], γ < 1) and
the level-n susceptibility bound give smeared decay at rate −log γ/(L + 1). -/
theorem sh1_level_consumer {m₀ lam L γ K : ℝ} (n : ℕ) (hL : 0 ≤ L) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hV : ∀ (k : ℕ) (x : DSite n k), ∃ r : ℝ, 0 ≤ r ∧ r ≤ L ∧ sh1_bdrySum n k m₀ lam x r ≤ γ)
    (hK0 : 0 ≤ K)
    (hKn : ∀ (k : ℕ) (x : DSite n k), spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y| ≤ K) :
    ∀ (k : ℕ) (x : DSite n k) (w : DSite n k → ℝ) (D : ℝ),
      (∀ y, 0 ≤ w y ∧ w y ≤ 1) → (∀ y, w y ≠ 0 → D ≤ supDist (dpos n k x) (dpos n k y)) →
        spacing n ^ 2 * ∑ y, w y * twoPt n k m₀ lam x y ≤
          K * Real.exp (-Real.log γ * (0 / (L + 1) + 1)) *
            Real.exp (-(-Real.log γ / (L + 1)) * D) := by
  have hlog : 0 < -Real.log γ := neg_pos.mpr (Real.log_neg hγ0 hγ1)
  intro k x w D hw hD
  choose ρ hρ0 hρL hργ using hV k
  have hbase : ∀ x, smeared n k m₀ lam w x ≤ K := fun x => sh1_smeared_le (hKn k x) hw
  by_cases hD0 : 0 ≤ D
  · exact geom_le_exp hγ0 hγ1 (by linarith) hK0 hD0 fun N hN =>
      sh1_decay hγ0 hK0 hSL hGI ρ hρ0 hρL hργ hw hbase N x fun y hy => by
        have := hD y hy; linarith
  · push Not at hD0
    have hb := hbase x
    have e1 : 1 ≤ Real.exp (-Real.log γ * (0 / (L + 1) + 1)) := by
      apply Real.one_le_exp; rw [zero_div, zero_add, mul_one]; exact hlog.le
    have e2 : 1 ≤ Real.exp (-(-Real.log γ / (L + 1)) * D) := by
      apply Real.one_le_exp
      have : 0 < -Real.log γ / (L + 1) := div_pos hlog (by linarith)
      nlinarith
    calc spacing n ^ 2 * ∑ y, w y * twoPt n k m₀ lam x y ≤ K := hb
      _ = K * 1 * 1 := by ring
      _ ≤ _ := by gcongr

/-- **The generalised consumer:** Simon–Lieb', Griffiths I for regions, a per-centre small
boundary sum (radius in [0, L], γ < 1) and the uniform susceptibility give uniform smeared decay.
No region-susceptibility input is needed (the base bound is the susceptibility itself). -/
theorem sh1_consumer {m₀ lam L γ K : ℝ} (hL : 0 ≤ L) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hV : VarSmallBoundarySum m₀ lam L γ) (hK : UniformSusceptibility m₀ lam K) :
    ∃ C₀ m : ℝ, 0 ≤ C₀ ∧ 0 < m ∧ UniformSmearedDecay m₀ lam C₀ m := by
  have hK0 := sh1_K_nonneg hK
  have hlog : 0 < -Real.log γ := neg_pos.mpr (Real.log_neg hγ0 hγ1)
  exact ⟨K * Real.exp (-Real.log γ * (0 / (L + 1) + 1)), -Real.log γ / (L + 1),
    by positivity, div_pos hlog (by linarith), fun n =>
      sh1_level_consumer n hL hγ0 hγ1 hSL hGI (hV n) hK0 (hK n)⟩

/-- **Clustering from the generalised consumer** (m₀ ≠ 0, λ ≥ 0; Simon–Lieb', Griffiths I for
regions and Newman discharged). -/
theorem clustering_of_varSmallBoundarySum {m₀ lam L γ K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hL : 0 ≤ L) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hV : VarSmallBoundarySum m₀ lam L γ) (hK : UniformSusceptibility m₀ lam K) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m := by
  obtain ⟨C₀, m, hC₀, hm', hdecay⟩ := sh1_consumer hL hγ0 hγ1 (simonLiebIneq'_holds hm hlam)
    (regionGriffithsI_holds m₀ lam) hV hK
  exact ⟨m, hm', conditional_clustering' hC₀ (by norm_num : (0 : ℝ) ≤ 4)
    (fun n k => twoPt n k m₀ lam) (PP2Newman.newman_hN hm hlam) hdecay⟩

/-! ## Averaging the shell sums over radii -/

theorem sh1_count_le_one {R₀ ε du dv : ℝ} (hε : 0 < ε) (h : dv ≤ du + ε) (M : ℕ) :
    ∑ j ∈ Finset.range M,
      (if du ≤ R₀ + j * ε ∧ ¬ dv ≤ R₀ + j * ε then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  have : ((Finset.range M).filter
      fun j : ℕ => du ≤ R₀ + j * ε ∧ ¬ dv ≤ R₀ + j * ε).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hab
    rcases Nat.lt_or_gt_of_ne hab with h1 | h1
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h1
      apply hb.2.2; nlinarith [ha.2.1]
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h1
      apply ha.2.2; nlinarith [hb.2.1]
  exact_mod_cast this

theorem sh1_sum_ball {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (F : α → α → ℝ) :
    ∑ u ∈ B, ∑ v ∈ Bᶜ, F u v = ∑ u, ∑ v, (if u ∈ B ∧ v ∉ B then F u v else 0) := by
  rw [← Fintype.sum_ite_mem B]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ B
  · simp only [hu, ite_true, true_and]
    rw [← Fintype.sum_ite_mem]
    simp [Finset.mem_compl]
  · simp [hu]

theorem sh1_Jsym_nonneg (u v : DSite n k) : 0 ≤ Jsym n k u v :=
  add_nonneg (Jnn_nonneg u v) (Jnn_nonneg v u)

/-- **Averaging over M radii R₀ + jε:** Σ_j shellSum(R₀ + jε) ≤ 4 Σ_u ⟨φ_x φ_u⟩ (each site u is
on the inner boundary of at most one of the balls). -/
theorem sh1_sum_shell_le (m₀ lam R₀ : ℝ) (x : DSite n k) (M : ℕ) :
    ∑ j ∈ Finset.range M, sh1_shellSum n k m₀ lam x (R₀ + j * spacing n) ≤
      4 * ∑ u, twoPt n k m₀ lam x u := by
  have hε := spacing_pos n
  set d : DSite n k → ℝ := fun u => supDist (dpos n k x) (dpos n k u) with hd
  set T : DSite n k → ℝ := fun u => twoPt n k m₀ lam x u with hT
  have e1 : ∀ j : ℕ, sh1_shellSum n k m₀ lam x (R₀ + j * spacing n) =
      ∑ u, ∑ v, (if d u ≤ R₀ + j * spacing n ∧ ¬ d v ≤ R₀ + j * spacing n
        then bondJ n k u v * T u else 0) := by
    intro j
    unfold sh1_shellSum
    rw [sh1_sum_ball]
    simp only [mem_physBall, hd, hT]
  have e2 : ∑ j ∈ Finset.range M, sh1_shellSum n k m₀ lam x (R₀ + j * spacing n) =
      ∑ u, ∑ v, bondJ n k u v * T u * ∑ j ∈ Finset.range M,
        (if d u ≤ R₀ + j * spacing n ∧ ¬ d v ≤ R₀ + j * spacing n then (1 : ℝ) else 0) := by
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hterm : ∀ u v, bondJ n k u v * T u * ∑ j ∈ Finset.range M,
      (if d u ≤ R₀ + j * spacing n ∧ ¬ d v ≤ R₀ + j * spacing n then (1 : ℝ) else 0)
        ≤ Jsym n k u v * T u := by
    intro u v
    have hTu : 0 ≤ T u := twoPt_nonneg m₀ lam x u
    by_cases huv : u = v
    · subst huv
      have : ∑ j ∈ Finset.range M,
          (if d u ≤ R₀ + j * spacing n ∧ ¬ d u ≤ R₀ + j * spacing n then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => by simp
      rw [this, mul_zero]
      exact mul_nonneg (sh1_Jsym_nonneg u u) hTu
    · rw [← Jsym_eq_bondJ huv]
      by_cases hJ : Jsym n k u v = 0
      · rw [hJ]; simp
      · have hJ' : bondJ n k u v ≠ 0 := by rwa [← Jsym_eq_bondJ huv]
        have hdv : d v ≤ d u + spacing n := by
          have t := supDist_triangle (dpos n k x) (dpos n k u) (dpos n k v)
          have := supDist_bondJ hJ'
          simp only [hd]; linarith
        have hc := sh1_count_le_one (R₀ := R₀) hε hdv M
        calc Jsym n k u v * T u * ∑ j ∈ Finset.range M,
            (if d u ≤ R₀ + j * spacing n ∧ ¬ d v ≤ R₀ + j * spacing n then (1 : ℝ) else 0)
            ≤ Jsym n k u v * T u * 1 :=
              mul_le_mul_of_nonneg_left hc (mul_nonneg (sh1_Jsym_nonneg u v) hTu)
          _ = Jsym n k u v * T u := mul_one _
  rw [e2]
  calc ∑ u, ∑ v, bondJ n k u v * T u * ∑ j ∈ Finset.range M,
        (if d u ≤ R₀ + j * spacing n ∧ ¬ d v ≤ R₀ + j * spacing n then (1 : ℝ) else 0)
      ≤ ∑ u, ∑ v, Jsym n k u v * T u :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v
    _ = ∑ u, (∑ v, Jsym n k u v) * T u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]
    _ ≤ ∑ u, 4 * T u := Finset.sum_le_sum fun u _ =>
        mul_le_mul_of_nonneg_right (Jsym_row_le u) (twoPt_nonneg m₀ lam x u)
    _ = 4 * ∑ u, twoPt n k m₀ lam x u := by rw [Finset.mul_sum]

/-- **Some radius among R₀ + jε, j < M, has a small shell sum:**
shellSum ≤ 4 Σ_u ⟨φ_x φ_u⟩ / M. -/
theorem sh1_exists_radius (m₀ lam R₀ : ℝ) (x : DSite n k) {M : ℕ} (hM : 0 < M) :
    ∃ j : ℕ, j < M ∧ sh1_shellSum n k m₀ lam x (R₀ + j * spacing n) ≤
      4 * (∑ u, twoPt n k m₀ lam x u) / M := by
  have hne : (Finset.range M).Nonempty := Finset.nonempty_range_iff.mpr hM.ne'
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : ∑ j ∈ Finset.range M, sh1_shellSum n k m₀ lam x (R₀ + j * spacing n) ≤
      ∑ _j ∈ Finset.range M, 4 * (∑ u, twoPt n k m₀ lam x u) / M := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hMr.ne']
    exact sh1_sum_shell_le m₀ lam R₀ x M
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨j, Finset.mem_range.mp hj, hle⟩

end PP2Target

end

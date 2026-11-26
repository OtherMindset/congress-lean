import LongTable.R_PP2OSGap
import LongTable.P_mwwlq01a_b80lsb

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2HamAssembly.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Hamiltonian track H, session 6
(plan item S6, the limit passage, and the final conditional assembly). Builds on PP2OSGap
(`osGap_of`, `hamiltonianGap_of`, `CompactApprox`), PP2Limit / PP2Limit2 (`schwartzSup`,
`UniformEquicont`, `uniformEquicont_of_susceptibility`, `norm_ZD_le_one`), PP2RP2
(`OSPositive`, `LatticeReflStable`, `osPositive_of_limitPoint`, `latRefl`, `partZ_pos`) and the
third/fourth target files (`IsLimitPoint`, `FiniteCutoffClustering`, `limitPoint_clusters`,
`PositiveTime`, `reflect`, `timeShift`, `HamiltonianGap`).

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* Goal 1, `ha_compactApprox a b : CompactApprox (schwartzSup a b)` for EVERY (a, b).
  χ = `ha_chi`, the `ContDiffBump` at 0 with rIn = 1, rOut = 2; ρ = 1 − χ; the cut-off
  `ha_cut hR f` = χ(x/R)·f (`HasCompactSupport.toSchwartzMap`), compactly supported
  (`ha_cut_hasCompactSupport`) and positive-time when f is (`ha_cut_positiveTime`: the support
  only shrinks). `ha_cut_err`: ∃ K ≥ 0, ∀ R ≥ 1, ‖f − χ(·/R)f‖_{a,b} ≤ K/R, with
  K = 2^b · Σ_{i≤b} M_i · 2^(a+1) · ‖f‖_{a+1,b}, M_i = sup ‖D^i ρ‖ (`ha_rho_deriv_bound`).
  Proof: f − χ_R f = ρ(·/R)·f (`ha_sub_cut_eq`); for ‖x‖ < R the product vanishes near x
  (`ha_rhoR_eventually_zero`), so its derivatives are 0; for ‖x‖ ≥ R, Leibniz
  (`norm_iteratedFDeriv_mul_le`), ‖D^i ρ(·/R)‖ ≤ M_i for R ≥ 1 (`ha_rhoR_deriv_le`, chain rule
  for the linear map R⁻¹·id) and ‖x‖^k ≤ (1 + ‖x‖)^(k+1)/R.
* Translation continuity (`ha_translate_sub_le`): for ‖v‖ ≤ 1,
  ‖τ_v h − h‖_{a,b} ≤ 4^a ‖h‖_{a,b+1} ‖v‖ (mean value theorem for D^n h on the unit ball
  around x, `one_add_le_sup_seminorm_apply`). Hence `ha_latRefl_close`:
  ‖τ_(−ε,0)Θf − Θf‖_{a,b} ≤ 4^a ‖Θf‖_{a,b+1} · ε, ε = spacing n.
* `ha_latticeReflStable : UniformEquicont m₀ λ → LatticeReflStable m₀ λ` (the RP hypothesis of
  PP2RP2 is now a consequence of E1; ε = 2^(−n) → 0 as (n, k) → ∞).
* Goal 2, limit points (Z with `IsLimitPoint m₀ λ Z`): `ha_ZD_zero` (ZD(0) = 1 for m₀ ≠ 0,
  λ ≥ 0, via `partZ_pos`), `ha_limit_zero` (Z 0 = 1), `ha_limit_bound` (‖Z h‖ ≤ 1),
  `ha_limit_lipschitz` (the uniform bound of `UniformEquicont` passes to the limit:
  ‖Z f − Z g‖ ≤ C·‖f − g‖_{a,b}). OS positivity by `osPositive_of_limitPoint` and clustering by
  `limitPoint_clusters` (both existing).
* Goal 3, `hamiltonianGap_of_limitPoint`: m₀ ≠ 0, λ ≥ 0, `IsLimitPoint m₀ λ Z`,
  `UniformEquicont m₀ λ`, `FiniteCutoffClustering m₀ λ m`, and time-translation invariance of Z
  ⇒ `HamiltonianGap Z m`. `hamiltonianGap_of_limitPoint'`: the same with `LatticeReflStable`
  supplied (redundant). `hamiltonianGap_of_limitPoint_susc`: `UniformSusceptibility m₀ λ K` in
  place of `UniformEquicont` (via `uniformEquicont_of_susceptibility`).

NOT formalized (what remains for `HamiltonianGap` of limit points).
* Time-translation invariance ∀ t h, Z(τ_(t,0) h) = Z(h) of the limit point: an explicit
  hypothesis (`htr`). It is not exact in the Dirichlet box and needs the boundary-decoupling
  estimate E2 of the PP2RP2 plan (an infinite-volume statement, not a consequence of
  `FiniteCutoffClustering` as stated).
* The analytic inputs themselves: `UniformEquicont` (E1; or `UniformSusceptibility`) and
  `FiniteCutoffClustering`, which belong to the construction track.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2HamAssembly

open PP2Target PP2RP2 PP2OSGap

/-! ## Schwartz seminorm bookkeeping -/

theorem ha_schwartzSup_le {a b : ℕ} {h : TestFn} {M : ℝ} (hM : 0 ≤ M)
    (hpt : ∀ k n, k ≤ a → n ≤ b → ∀ x : Plane, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ⇑h x‖ ≤ M) :
    schwartzSup a b h ≤ M := by
  unfold schwartzSup
  refine Seminorm.finset_sup_apply_le hM fun m hm => ?_
  rw [Finset.mem_Iic] at hm
  obtain ⟨h1, h2⟩ := hm
  exact SchwartzMap.seminorm_le_bound ℝ m.1 m.2 h hM (hpt m.1 m.2 h1 h2)

theorem ha_pt_le {a b k n : ℕ} (hk : k ≤ a) (hn : n ≤ b) (h : TestFn) (x : Plane) :
    (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n ⇑h x‖ ≤ 2 ^ a * schwartzSup a b h :=
  SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (a, b)) hk hn h x

theorem ha_norm_timeShift (t : ℝ) : ‖timeShift t‖ = |t| := by
  rw [EuclideanSpace.norm_eq]
  simp [timeShift, Real.sqrt_sq_eq_abs]

/-! ## Continuity of translation in the Schwartz seminorms -/

theorem ha_translate_sub_le (a b : ℕ) (h : TestFn) {v : Plane} (hv : ‖v‖ ≤ 1) :
    schwartzSup a b (PP2Target.translate v h - h) ≤ 4 ^ a * schwartzSup a (b + 1) h * ‖v‖ := by
  set S := schwartzSup a (b + 1) h with hSdef
  have hS : 0 ≤ S := apply_nonneg _ _
  refine ha_schwartzSup_le (by positivity) fun k n hk hn x => ?_
  have hsm : ContDiff ℝ ∞ ⇑h := h.smooth ⊤
  set F := iteratedFDeriv ℝ n ⇑h with hF
  have heq : iteratedFDeriv ℝ n ⇑(PP2Target.translate v h - h) x = F (x - v) - F x := by
    have e : ⇑(PP2Target.translate v h - h) = (fun z => h (z - v)) - ⇑h := by
      ext z; simp [PP2Target.translate]
    rw [e, iteratedFDeriv_sub_apply, iteratedFDeriv_comp_sub]
    · exact ((hsm.comp (contDiff_id.sub contDiff_const)).of_le (mod_cast le_top)).contDiffAt
    · exact (hsm.of_le (mod_cast le_top)).contDiffAt
  have hdiff : Differentiable ℝ F :=
    hsm.differentiable_iteratedFDeriv (mod_cast WithTop.coe_lt_top _)
  set C := 2 ^ (a + k) * S / (1 + ‖x‖) ^ k with hC
  have hx1 : 0 < (1 + ‖x‖) ^ k := by positivity
  have hbound : ∀ y ∈ Metric.closedBall x 1, ‖fderiv ℝ F y‖ ≤ C := by
    intro y hy
    rw [hF, norm_fderiv_iteratedFDeriv]
    have hy' : ‖x‖ ≤ ‖y‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x y
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      rw [norm_sub_rev] at hy
      linarith
    have hpy := ha_pt_le (a := a) (b := b + 1) (n := n + 1) hk (by omega) h y
    have hy1 : 0 < (1 + ‖y‖) ^ k := by positivity
    have hxy : (1 + ‖x‖) ^ k ≤ 2 ^ k * (1 + ‖y‖) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg y]) k
    rw [hC, le_div_iff₀ hx1]
    calc ‖iteratedFDeriv ℝ (n + 1) ⇑h y‖ * (1 + ‖x‖) ^ k
        ≤ ‖iteratedFDeriv ℝ (n + 1) ⇑h y‖ * (2 ^ k * (1 + ‖y‖) ^ k) := by gcongr
      _ = 2 ^ k * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) ⇑h y‖) := by ring
      _ ≤ 2 ^ k * (2 ^ a * S) := by gcongr
      _ = 2 ^ (a + k) * S := by ring
  have hmvt : ‖F (x - v) - F x‖ ≤ C * ‖(x - v) - x‖ :=
    (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le (fun y _ => hdiff y) hbound
      (Metric.mem_closedBall_self zero_le_one)
      (by rw [Metric.mem_closedBall, dist_eq_norm]; simpa using hv)
  rw [heq]
  have hvv : ‖(x - v) - x‖ = ‖v‖ := by rw [sub_sub_cancel_left, norm_neg]
  rw [hvv] at hmvt
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
  calc ‖x‖ ^ k * ‖F (x - v) - F x‖ ≤ (1 + ‖x‖) ^ k * (C * ‖v‖) := by
        gcongr
    _ = 2 ^ (a + k) * S * ‖v‖ := by
        rw [hC]; field_simp
    _ ≤ 4 ^ a * S * ‖v‖ := by
        gcongr
        calc (2 : ℝ) ^ (a + k) ≤ 2 ^ (a + a) := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 4 ^ a := by rw [← two_mul, pow_mul]; norm_num

/-! ## Compact approximation in the Schwartz seminorms -/

/-- The fixed bump: χ = 1 on the closed unit ball, χ = 0 outside the ball of radius 2. -/
def ha_chi : ContDiffBump (0 : Plane) := ⟨1, 2, one_pos, one_lt_two⟩

/-- ρ = 1 − χ. -/
def ha_rho (y : Plane) : ℝ := 1 - ha_chi y

theorem ha_rho_contDiff : ContDiff ℝ ∞ ha_rho := contDiff_const.sub ha_chi.contDiff

theorem ha_rho_deriv_bound (i : ℕ) :
    ∃ M, 0 ≤ M ∧ ∀ y, ‖iteratedFDeriv ℝ i ha_rho y‖ ≤ M := by
  obtain ⟨C, hC⟩ := (ContDiff.continuous_iteratedFDeriv (m := i) (mod_cast le_top)
    (ha_chi.contDiff (n := ⊤))).bounded_above_of_compact_support
    (ha_chi.hasCompactSupport.iteratedFDeriv i)
  refine ⟨1 + max C 0, by positivity, fun y => ?_⟩
  have e : iteratedFDeriv ℝ i ha_rho y =
      iteratedFDeriv ℝ i (fun _ : Plane => (1 : ℝ)) y - iteratedFDeriv ℝ i ha_chi y := by
    have : ha_rho = (fun _ : Plane => (1 : ℝ)) - ⇑ha_chi := rfl
    rw [this, iteratedFDeriv_sub_apply contDiff_const.contDiffAt ha_chi.contDiffAt]
  have h1 : ‖iteratedFDeriv ℝ i (fun _ : Plane => (1 : ℝ)) y‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [norm_iteratedFDeriv_zero]
    · rw [iteratedFDeriv_const_of_ne hi.ne']; simp
  rw [e]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 1 + max C 0 := add_le_add h1 ((hC y).trans (le_max_left _ _))

/-- ρ_R(y) = ρ(y / R). -/
def ha_rhoR (R : ℝ) (y : Plane) : ℝ := ha_rho (R⁻¹ • y)

theorem ha_rhoR_eq (R : ℝ) :
    ha_rhoR R = ha_rho ∘ (R⁻¹ • ContinuousLinearMap.id ℝ Plane) := by
  ext y; simp [ha_rhoR]

theorem ha_rhoR_contDiff (R : ℝ) : ContDiff ℝ ∞ (ha_rhoR R) := by
  rw [ha_rhoR_eq]; exact ha_rho_contDiff.comp (ContinuousLinearMap.contDiff _)

theorem ha_rhoR_deriv_le {R : ℝ} (hR : 1 ≤ R) (i : ℕ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, ‖iteratedFDeriv ℝ i ha_rho y‖ ≤ M) (x : Plane) :
    ‖iteratedFDeriv ℝ i (ha_rhoR R) x‖ ≤ M := by
  set L := R⁻¹ • ContinuousLinearMap.id ℝ Plane with hLdef
  have hL : ‖L‖ ≤ 1 := by
    calc ‖L‖ ≤ ‖R⁻¹‖ * ‖ContinuousLinearMap.id ℝ Plane‖ := by rw [hLdef]; exact norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ Plane)
      _ ≤ ‖R⁻¹‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ ≤ 1 := by
        rw [mul_one, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)]
        exact inv_le_one_of_one_le₀ hR
  rw [ha_rhoR_eq, ContinuousLinearMap.iteratedFDeriv_comp_right L ha_rho_contDiff x
    (mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i ha_rho (L x)‖ * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ M * 1 := by
        gcongr
        · exact hM _
        · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact pow_le_one₀ (norm_nonneg _) hL
    _ = M := mul_one M

theorem ha_rhoR_eventually_zero {R : ℝ} (hR : 0 < R) {x : Plane} (hx : ‖x‖ < R) :
    ha_rhoR R =ᶠ[𝓝 x] 0 := by
  have hmem : Metric.ball (0 : Plane) R ∈ 𝓝 x :=
    Metric.isOpen_ball.mem_nhds (by rwa [Metric.mem_ball, dist_zero_right])
  filter_upwards [hmem] with y hy
  rw [Metric.mem_ball, dist_zero_right] at hy
  have hc : R⁻¹ • y ∈ Metric.closedBall (0 : Plane) ha_chi.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hR]
    show R⁻¹ * ‖y‖ ≤ 1
    rw [inv_mul_le_iff₀ hR]; linarith
  simp [ha_rhoR, ha_rho, ha_chi.one_of_mem_closedBall hc]

theorem ha_chiR_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fun x : Plane => ha_chi (R⁻¹ • x)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Plane) (2 * R)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  apply ha_chi.zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show 2 ≤ R⁻¹ * ‖x‖
  rw [le_inv_mul_iff₀ hR]; linarith

theorem ha_chiR_contDiff (R : ℝ) : ContDiff ℝ ∞ (fun x : Plane => ha_chi (R⁻¹ • x)) :=
  ha_chi.contDiff.comp (contDiff_id.const_smul R⁻¹)

/-- The cut-off χ(x/R)·f, a compactly supported Schwartz function. -/
def ha_cut {R : ℝ} (hR : 0 < R) (f : TestFn) : TestFn :=
  HasCompactSupport.toSchwartzMap (f := fun x => ha_chi (R⁻¹ • x) * f x)
    (ha_chiR_hasCompactSupport hR).mul_right ((ha_chiR_contDiff R).mul (f.smooth ⊤))

theorem ha_cut_apply {R : ℝ} (hR : 0 < R) (f : TestFn) (x : Plane) :
    ha_cut hR f x = ha_chi (R⁻¹ • x) * f x := rfl

theorem ha_cut_hasCompactSupport {R : ℝ} (hR : 0 < R) (f : TestFn) :
    HasCompactSupport ⇑(ha_cut hR f) :=
  (ha_chiR_hasCompactSupport hR).mul_right

theorem ha_cut_positiveTime {R : ℝ} (hR : 0 < R) {f : TestFn} (hf : PositiveTime f) :
    PositiveTime (ha_cut hR f) := fun x hx => by
  rw [ha_cut_apply] at hx
  exact hf x (right_ne_zero_of_mul hx)

theorem ha_sub_cut_eq {R : ℝ} (hR : 0 < R) (f : TestFn) :
    ⇑(f - ha_cut hR f) = fun y => ha_rhoR R y * f y := by
  ext y
  show f y - ha_chi (R⁻¹ • y) * f y = (1 - ha_chi (R⁻¹ • y)) * f y
  ring

/-- **Cut-off error**: ‖f − χ(·/R) f‖_{a,b} ≤ K / R for R ≥ 1. -/
theorem ha_cut_err (a b : ℕ) (f : TestFn) :
    ∃ K, 0 ≤ K ∧ ∀ (R : ℝ) (hR : 1 ≤ R),
      schwartzSup a b (f - ha_cut (lt_of_lt_of_le one_pos hR) f) ≤ K / R := by
  choose M hM0 hM using ha_rho_deriv_bound
  set Mb := ∑ i ∈ Finset.range (b + 1), M i with hMbdef
  have hMb0 : 0 ≤ Mb := Finset.sum_nonneg fun i _ => hM0 i
  have hMb : ∀ i ≤ b, M i ≤ Mb := fun i hi =>
    Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_range.mpr (by omega))
  set S := schwartzSup (a + 1) b f with hSdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set K := 2 ^ b * Mb * (2 ^ (a + 1) * S) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun R hR => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  refine ha_schwartzSup_le (div_nonneg hK0 hR0.le) fun k n hk hn x => ?_
  rw [ha_sub_cut_eq]
  rcases lt_or_ge ‖x‖ R with hx | hx
  · have hz : (fun y => ha_rhoR R y * f y) =ᶠ[𝓝 x] (0 : Plane → ℝ) :=
      (ha_rhoR_eventually_zero hR0 hx).mono fun y hy => by
        simp only [Pi.zero_apply] at hy ⊢; rw [hy, zero_mul]
    rw [(hz.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply, norm_zero,
      mul_zero]
    exact div_nonneg hK0 hR0.le
  · have hLb := norm_iteratedFDeriv_mul_le (ha_rhoR_contDiff R) (f.smooth ⊤) x (n := n)
      (mod_cast le_top)
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ha_rhoR R) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖)
          ≤ (n.choose i : ℝ) * Mb * (2 ^ (a + 1) * S / R) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h1 : ‖iteratedFDeriv ℝ i (ha_rhoR R) x‖ ≤ Mb :=
        (ha_rhoR_deriv_le hR i (hM0 i) (hM i) x).trans (hMb i (by omega))
      have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖ ≤ 2 ^ (a + 1) * S / R := by
        rw [le_div_iff₀ hR0]
        have hp := ha_pt_le (a := a + 1) (b := b) (k := k + 1) (n := n - i) (by omega)
          (by omega) f x
        have hxx : ‖x‖ ^ k * R ≤ (1 + ‖x‖) ^ (k + 1) := by
          calc ‖x‖ ^ k * R ≤ ‖x‖ ^ k * ‖x‖ := by gcongr
            _ = ‖x‖ ^ (k + 1) := (pow_succ _ _).symm
            _ ≤ (1 + ‖x‖) ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖ * R
            = (‖x‖ ^ k * R) * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖ := by ring
          _ ≤ (1 + ‖x‖) ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖ := by gcongr
          _ ≤ _ := hp
      have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
      calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ha_rhoR R) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖)
          ≤ (n.choose i : ℝ) * Mb * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖) := by
            gcongr
        _ ≤ (n.choose i : ℝ) * Mb * (2 ^ (a + 1) * S / R) := by gcongr
    have hchoose : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => ha_rhoR R y * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (ha_rhoR R) x‖ * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖ := by
          gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (ha_rhoR R) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) ⇑f x‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Mb * (2 ^ (a + 1) * S / R) :=
          Finset.sum_le_sum hterm
      _ = 2 ^ n * Mb * (2 ^ (a + 1) * S / R) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
      _ ≤ 2 ^ b * Mb * (2 ^ (a + 1) * S / R) := by
          gcongr
          · norm_num
      _ = K / R := by rw [hKdef]; ring

/-- **Goal 1.** `CompactApprox (schwartzSup a b)` for every (a, b). -/
theorem ha_compactApprox (a b : ℕ) : CompactApprox (schwartzSup a b) := by
  intro f hf ε hε
  obtain ⟨K, hK, hKR⟩ := ha_cut_err a b f
  set R := max 1 ((K + 1) / ε) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  refine ⟨ha_cut hR0 f, ha_cut_positiveTime hR0 hf, ha_cut_hasCompactSupport hR0 f, ?_⟩
  calc schwartzSup a b (f - ha_cut hR0 f) ≤ K / R := hKR R hR1
    _ < ε := by
      rw [div_lt_iff₀ hR0]
      have : (K + 1) / ε ≤ R := le_max_right _ _
      have h2 : K + 1 ≤ ε * R := by
        rw [div_le_iff₀ hε] at this; linarith
      linarith

/-! ## Properties of limit points -/

theorem ha_ZD_zero {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (n k : ℕ) :
    ZD n k m₀ lam (Polynomial.X ^ 4) 0 = 1 := by
  unfold ZD
  have hd : ∀ φ : DField n k, dsmear n k 0 φ = 0 := fun φ => by simp [dsmear]
  simp only [hd, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  rw [integral_complex_ofReal]
  have hp := partZ_pos (n := n) (k := k) hm hlam
  unfold partZ at hp
  exact div_self (Complex.ofReal_ne_zero.mpr hp.ne')

theorem ha_limit_zero {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) {Z : TestFn → ℂ}
    (hZ : IsLimitPoint m₀ lam Z) : Z 0 = 1 := by
  obtain ⟨ns, ks, -, -, hconv⟩ := hZ
  have h := hconv 0
  simp only [ha_ZD_zero hm hlam] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem ha_limit_bound {m₀ lam : ℝ} {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) :
    ∀ h, ‖Z h‖ ≤ 1 := by
  obtain ⟨ns, ks, -, -, hconv⟩ := hZ
  intro h
  exact le_of_tendsto (hconv h).norm
    (Eventually.of_forall fun j => norm_ZD_le_one _ _ _ _ _ _)

theorem ha_limit_lipschitz {m₀ lam : ℝ} {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z)
    {C : ℝ} {a b : ℕ} (hC : ∀ (n k : ℕ) (f g : TestFn),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) f - ZD n k m₀ lam (Polynomial.X ^ 4) g‖
        ≤ C * schwartzSup a b (f - g)) :
    ∀ f g : TestFn, ‖Z f - Z g‖ ≤ C * schwartzSup a b (f - g) := by
  obtain ⟨ns, ks, -, -, hconv⟩ := hZ
  intro f g
  exact le_of_tendsto ((hconv f).sub (hconv g)).norm
    (Eventually.of_forall fun j => hC _ _ f g)

/-! ## `LatticeReflStable` from `UniformEquicont` -/

theorem ha_latRefl_close (a b : ℕ) (f : TestFn) (n : ℕ) :
    schwartzSup a b (latRefl n f - reflect f)
      ≤ 4 ^ a * schwartzSup a (b + 1) (reflect f) * spacing n := by
  have hsp : 0 < spacing n := by unfold spacing; positivity
  have hs : ‖timeShift (-spacing n)‖ = spacing n := by
    rw [ha_norm_timeShift, abs_neg, abs_of_pos hsp]
  have hle : ‖timeShift (-spacing n)‖ ≤ 1 := by
    rw [hs]; unfold spacing; exact pow_le_one₀ (by norm_num) (by norm_num)
  have := ha_translate_sub_le a b (reflect f) hle
  rw [hs] at this
  exact this

theorem ha_latticeReflStable {m₀ lam : ℝ} (hE : UniformEquicont m₀ lam) :
    LatticeReflStable m₀ lam := by
  obtain ⟨C, a, b, hC⟩ := hE
  intro f g
  set K := |C| * (4 ^ a * schwartzSup a (b + 1) (reflect f)) with hKdef
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hsp : Tendsto (fun p : ℕ × ℕ => spacing p.1) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => spacing n) atTop (𝓝 0) := by
      unfold spacing
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact this.comp hfst
  have hlim : Tendsto (fun p : ℕ × ℕ => K * spacing p.1) atTop (𝓝 0) := by
    simpa using hsp.const_mul K
  refine squeeze_zero_norm (fun p => ?_) hlim
  calc _ ≤ C * schwartzSup a b ((g - latRefl p.1 f) - (g - reflect f)) := hC _ _ _ _
    _ ≤ |C| * schwartzSup a b ((g - latRefl p.1 f) - (g - reflect f)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (apply_nonneg _ _)
    _ = |C| * schwartzSup a b (latRefl p.1 f - reflect f) := by
        rw [sub_sub_sub_cancel_left]
        congr 1
        rw [← neg_sub, map_neg_eq_map]
    _ ≤ |C| * (4 ^ a * schwartzSup a (b + 1) (reflect f) * spacing p.1) := by
        gcongr
        exact ha_latRefl_close a b f p.1
    _ = K * spacing p.1 := by rw [hKdef]; ring

/-! ## Assembly -/

/-- **Conditional Hamiltonian gap for limit points.** -/
theorem hamiltonianGap_of_limitPoint {m₀ lam m : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) (hE : UniformEquicont m₀ lam)
    (hcl : FiniteCutoffClustering m₀ lam m)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h) :
    HamiltonianGap Z m := by
  obtain ⟨C, a, b, hC⟩ := hE
  exact hamiltonianGap_of Z m
    (osPositive_of_limitPoint hm hlam (ha_latticeReflStable ⟨C, a, b, hC⟩) hZ) htr
    (ha_limit_bound hZ) (ha_limit_zero hm hlam hZ) (schwartzSup a b)
    ⟨C, ha_limit_lipschitz hZ hC⟩ (ha_compactApprox a b) (limitPoint_clusters hcl hZ)

/-- The same with `LatticeReflStable` supplied (it is redundant: `ha_latticeReflStable`). -/
theorem hamiltonianGap_of_limitPoint' {m₀ lam m : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) (hE : UniformEquicont m₀ lam)
    (hcl : FiniteCutoffClustering m₀ lam m) (hst : LatticeReflStable m₀ lam)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h) :
    HamiltonianGap Z m := by
  obtain ⟨C, a, b, hC⟩ := hE
  exact hamiltonianGap_of Z m (osPositive_of_limitPoint hm hlam hst hZ) htr
    (ha_limit_bound hZ) (ha_limit_zero hm hlam hZ) (schwartzSup a b)
    ⟨C, ha_limit_lipschitz hZ hC⟩ (ha_compactApprox a b) (limitPoint_clusters hcl hZ)

/-- The same from a uniform two-point (susceptibility) bound in place of `UniformEquicont`. -/
theorem hamiltonianGap_of_limitPoint_susc {m₀ lam m K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) (hK : UniformSusceptibility m₀ lam K)
    (hcl : FiniteCutoffClustering m₀ lam m)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h) :
    HamiltonianGap Z m :=
  hamiltonianGap_of_limitPoint hm hlam hZ (uniformEquicont_of_susceptibility hm hlam hK) hcl htr

end PP2HamAssembly

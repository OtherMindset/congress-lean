import LongTable.R_PP2Sharp1A

/-!
Part B of PP2Sharp1 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Sharp1.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* `LevelClustering m₀ λ n m`: `FiniteCutoffClustering` at the fixed level n (constant uniform in k).
* **`sh1_regionTwoPt_le_twoPt`** (m₀ ≠ 0, λ ≥ 0): ⟨φ_xφ_u⟩_R ≤ ⟨φ_xφ_u⟩ for every region R
  (Griffiths II in the cone, A = φ_xφ_u, B = e^{bdry}, for the decoupled measure; via
  `regionTwoPt_eq_tI`, `twoPt_eq_tI`, `griffiths_second_cone`, `hint_dec`).
  Corollaries `sh1_bdrySum_le_shellSum`, **`sh1_regionSusceptibility`** (UniformSusceptibility K ⟹
  RegionSusceptibility l K for every l) and `clustering_of_smallBoundarySum_of_susceptibility`
  (the existing chain needs only SmallBoundarySum once χ is bounded).
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

/-! ## Uniform susceptibility + Dirichlet suppression ⟹ uniform clustering -/

/-- **Uniform susceptibility and Dirichlet suppression give a per-centre small boundary sum**
with γ = 1/2 and radius ≤ R₀ + T, T = ⌈8CK⌉ + 1, uniformly in n, k. -/
theorem varSmallBoundarySum_of_suppression {m₀ lam K R₀ C : ℝ} (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C)
    (hK : UniformSusceptibility m₀ lam K) (hS : DirichletSuppression m₀ lam R₀ C) :
    VarSmallBoundarySum m₀ lam (R₀ + (⌈8 * C * K⌉₊ + 1 : ℕ)) (1 / 2) := by
  have hK0 := sh1_K_nonneg hK
  set T : ℕ := ⌈8 * C * K⌉₊ + 1 with hTdef
  intro n k x
  have hε := spacing_pos n
  have hε2 : spacing n * 2 ^ n = 1 := by
    unfold spacing; rw [← mul_pow]; norm_num
  have hT1 : (1 : ℝ) ≤ T := by rw [hTdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈8 * C * K⌉₊]
  have hT8 : 8 * C * K ≤ T := by
    rw [hTdef]; push_cast; linarith [Nat.le_ceil (8 * C * K)]
  set M : ℕ := T * 2 ^ n with hMdef
  have hM : 0 < M := by rw [hMdef]; positivity
  have hMr : (M : ℝ) * spacing n = T := by
    rw [hMdef]; push_cast; rw [mul_assoc, mul_comm ((2 : ℝ) ^ n), hε2, mul_one]
  obtain ⟨j, hjM, hj⟩ := sh1_exists_radius m₀ lam R₀ x hM
  refine ⟨R₀ + j * spacing n, by positivity, ?_, ?_⟩
  · have : (j : ℝ) * spacing n ≤ T := by
      rw [← hMr]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjM.le) hε.le
    linarith
  · have hsupp := hS n k x (R₀ + j * spacing n) (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
    have hχ : spacing n ^ 2 * ∑ u, twoPt n k m₀ lam x u ≤ K := by
      refine le_trans (le_of_eq ?_) (hK n k x)
      congr 1
      exact Finset.sum_congr rfl fun u _ => (abs_of_nonneg (twoPt_nonneg m₀ lam x u)).symm
    have hS0 : 0 ≤ ∑ u, twoPt n k m₀ lam x u :=
      Finset.sum_nonneg fun u _ => twoPt_nonneg m₀ lam x u
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hTpos : (0 : ℝ) < T := by linarith
    -- C ε · 4 S / M = 4 C (ε² S) / T ≤ 4 C K / T ≤ 1/2
    have key : C * spacing n * (4 * (∑ u, twoPt n k m₀ lam x u) / M) ≤ 1 / 2 := by
      have hMe : (M : ℝ) = T / spacing n := by rw [← hMr]; field_simp
      rw [hMe]
      have : C * spacing n * (4 * (∑ u, twoPt n k m₀ lam x u) / (T / spacing n)) =
          4 * C * (spacing n ^ 2 * ∑ u, twoPt n k m₀ lam x u) / T := by
        field_simp
      rw [this, div_le_iff₀ hTpos]
      nlinarith [mul_le_mul_of_nonneg_left hχ (by positivity : (0 : ℝ) ≤ 4 * C)]
    calc sh1_bdrySum n k m₀ lam x (R₀ + j * spacing n)
        ≤ C * spacing n * sh1_shellSum n k m₀ lam x (R₀ + j * spacing n) := hsupp
      _ ≤ C * spacing n * (4 * (∑ u, twoPt n k m₀ lam x u) / M) :=
          mul_le_mul_of_nonneg_left hj (by positivity)
      _ ≤ 1 / 2 := key

/-- **Uniform susceptibility + Dirichlet suppression ⟹ uniform exponential clustering**, for every
λ ≥ 0 (m₀ ≠ 0). -/
theorem clustering_of_uniformSusceptibility_of_suppression {m₀ lam K R₀ C : ℝ} (hm : m₀ ≠ 0)
    (hlam : 0 ≤ lam) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C)
    (hK : UniformSusceptibility m₀ lam K) (hS : DirichletSuppression m₀ lam R₀ C) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m :=
  clustering_of_varSmallBoundarySum hm hlam (by positivity) (by norm_num) (by norm_num)
    (varSmallBoundarySum_of_suppression hR₀ hC hK hS) hK

/-! ## Griffiths II: region two-point functions are dominated by the full one -/

theorem sh1_regionTwoPt_out_left (m₀ lam : ℝ) (R : Finset (DSite n k)) {x : DSite n k}
    (hx : x ∉ R) (u : DSite n k) : regionTwoPt n k m₀ lam R x u = 0 := by
  have h : ∀ ψ : {z // z ∈ R} → ℝ, zeroExt R ψ x = 0 := fun ψ => by simp [zeroExt, hx]
  simp [regionTwoPt, h]

/-- **Monotonicity in the region (Griffiths II):** ⟨φ_x φ_u⟩_R ≤ ⟨φ_x φ_u⟩ for every region R
(m₀ ≠ 0, λ ≥ 0). Proof: both are decoupled expectations, ⟨φ_xφ_u⟩_R = [φ_xφ_u]_dec/[1]_dec and
⟨φ_xφ_u⟩ = [φ_xφ_u e^{bdry}]_dec/[e^{bdry}]_dec, and Griffiths II in the cone
(`griffiths_second_cone`, A = φ_xφ_u, B = e^{bdry}) for the decoupled ferromagnetic measure. -/
theorem sh1_regionTwoPt_le_twoPt {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (R : Finset (DSite n k)) (x u : DSite n k) :
    regionTwoPt n k m₀ lam R x u ≤ twoPt n k m₀ lam x u := by
  by_cases hx : x ∈ R
  swap
  · rw [sh1_regionTwoPt_out_left m₀ lam R hx u]; exact twoPt_nonneg m₀ lam x u
  by_cases hu : u ∈ R
  swap
  · rw [regionTwoPt_out m₀ lam R x hu]; exact twoPt_nonneg m₀ lam x u
  rw [regionTwoPt_eq_tI hm hlam R hx hu, twoPt_eq_tI m₀ lam R x u]
  set a := alphaQ n m₀ lam
  set b := betaQ n lam
  set w : DSite n k → ℝ → ℝ := siteW a b 0 with hw
  set Q : DField n k → ℝ := quadE (decJ n k R) with hQdef
  have e0 : ∀ (F : DField n k → ℝ) φ, F φ * Real.exp (quadE (decJ n k R) φ) * tw a b 0 φ =
      F φ * (Real.exp (Q φ) * ∏ z, w z (φ z)) := fun F φ => by
    rw [mul_assoc, rhoQ_siteW]; rfl
  have tIe : ∀ F : DField n k → ℝ, tI (decJ n k R) a b 0 F =
      ∫ φ, F φ * (Real.exp (Q φ) * ∏ z, w z (φ z)) := fun F =>
    integral_congr_ae (Filter.Eventually.of_forall (e0 F))
  have hint : ∀ H, Adm (fun φ : DField n k => 1 + Real.exp (bdryCoupling R φ)) H →
      Integrable fun φ => H φ * (Real.exp (Q φ) * ∏ z, w z (φ z)) := fun H hH =>
    (hint_dec hm hlam R H hH).congr (Filter.Eventually.of_forall (e0 H))
  have h1 := Adm.const (one_le_envelope R) 1
  have hAadm : Adm (fun φ : DField n k => 1 + Real.exp (bdryCoupling R φ))
      (fun φ => φ x * φ u) :=
    ((h1.mul_coord u).mul_coord x).congr fun φ => by ring
  have hABadm : Adm (fun φ : DField n k => 1 + Real.exp (bdryCoupling R φ))
      (fun φ => φ x * φ u * Real.exp (bdryCoupling R φ)) :=
    (((adm_exp_bdry R).mul_coord u).mul_coord x).congr fun φ => by ring
  have hwe : ∀ z y, w z (-y) = w z y := fun z y => by simp only [hw, siteW, neg_sq]
  have hwn : ∀ z y, 0 ≤ w z y := fun z y => (Real.exp_pos _).le
  have hA : InCone (fun φ : DField n k => φ x * φ u) :=
    InCone.of_isPosPoly ((IsPosPoly.coord x).mul (IsPosPoly.coord u))
  have hB : InCone (fun φ : DField n k => Real.exp (bdryCoupling R φ)) :=
    ⟨fun _ => 1, quadE (bdryK n k R), IsPosPoly.const zero_le_one,
      IsPosPoly.quadForm (bdryK_nonneg R), fun φ => by rw [quadE_bdryK]; ring⟩
  have hQ : IsPosPoly Q := IsPosPoly.quadForm (decJ_nonneg R)
  have hρ : Integrable fun φ : DField n k => Real.exp (Q φ) * ∏ z, w z (φ z) :=
    (hint (fun _ => 1) h1).congr (Filter.Eventually.of_forall fun φ => by simp only [one_mul])
  have key := griffiths_second_cone (A := fun φ : DField n k => φ x * φ u)
    (B := fun φ : DField n k => Real.exp (bdryCoupling R φ)) hwe hwn hA hB hQ
    (hint _ hABadm) (hint _ hAadm) (hint _ (adm_exp_bdry R)) hρ
  have p1 : 0 < tI (decJ n k R) a b 0 (fun _ => 1) :=
    tI_pos_of (fun _ => one_pos) (hint_dec hm hlam R _ h1)
  have p2 : 0 < tI (decJ n k R) a b 0 (fun φ => Real.exp (bdryCoupling R φ)) :=
    tI_pos_of (fun _ => Real.exp_pos _) (hint_dec hm hlam R _ (adm_exp_bdry R))
  rw [div_le_div_iff₀ p1 p2]
  rw [tIe, tIe, tIe, tIe] at *
  have e1 : ∫ φ, (fun _ : DField n k => (1 : ℝ)) φ * (Real.exp (Q φ) * ∏ z, w z (φ z)) =
      ∫ φ, Real.exp (Q φ) * ∏ z, w z (φ z) := by simp only [one_mul]
  rw [e1]
  exact ge_iff_le.mp key

/-- The region boundary sum is at most the full boundary sum (Griffiths II). -/
theorem sh1_bdrySum_le_shellSum {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (x : DSite n k) (r : ℝ) : sh1_bdrySum n k m₀ lam x r ≤ sh1_shellSum n k m₀ lam x r := by
  unfold sh1_bdrySum sh1_shellSum
  refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => ?_
  have huv : u ≠ v := by rintro rfl; exact (Finset.mem_compl.mp hv) hu
  exact mul_le_mul_of_nonneg_left (sh1_regionTwoPt_le_twoPt hm hlam _ x u) (bondJ_nonneg huv)

/-- Griffiths II gives the region susceptibility from the full one (any radius). -/
theorem sh1_regionSusceptibility {m₀ lam K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hK : UniformSusceptibility m₀ lam K) (l : ℝ) : RegionSusceptibility m₀ lam l K := by
  intro n k x
  refine le_trans ?_ (hK n k x)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by positivity)
  exact (sh1_regionTwoPt_le_twoPt hm hlam _ x y).trans (le_abs_self _)

/-! ## What the averaging gives WITHOUT suppression: clustering at each fixed spacing -/

/-- Exponential clustering at rate m at the FIXED level n, uniformly in the volume k. -/
def LevelClustering (m₀ lam : ℝ) (n : ℕ) (m : ℝ) : Prop :=
  ∀ f g : TestFn, HasCompactSupport ⇑f → HasCompactSupport ⇑g →
    ∃ C : ℝ, ∀ (k : ℕ) (a : Plane),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + translate a g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) (translate a g)‖
        ≤ C * Real.exp (-m * max |a 0| |a 1|)

/-- `conditional_clustering'` at a fixed level n (same proof). -/
theorem sh1_conditional_clustering_level {m₀ lam m C₀ κ : ℝ} (n : ℕ) (hC₀ : 0 ≤ C₀)
    (hκ : 0 ≤ κ) (G : ∀ k : ℕ, DSite n k → DSite n k → ℝ)
    (hN : ∀ (k : ℕ) (f g : TestFn),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) g‖
        ≤ κ * ∑ x : DSite n k, ∑ y : DSite n k,
            spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|) * G k x y)
    (hGs : ∀ (k : ℕ) (x : DSite n k) (w : DSite n k → ℝ) (D : ℝ),
      (∀ y, 0 ≤ w y ∧ w y ≤ 1) → (∀ y, w y ≠ 0 → D ≤ supDist (dpos n k x) (dpos n k y)) →
        spacing n ^ 2 * ∑ y, w y * G k x y ≤ C₀ * Real.exp (-m * D)) :
    LevelClustering m₀ lam n m := by
  intro f g hf hg
  obtain ⟨Mf, Rf, hRf, hMf, hsf⟩ := bound_and_box f hf
  obtain ⟨Mg, Rg, hRg, hMg, hsg⟩ := bound_and_box g hg
  set R := max Rf Rg
  have hR : 0 ≤ R := le_max_of_le_left hRf
  have hsf' : ∀ p, f p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R := fun p hp =>
    ⟨(hsf p hp).1.trans (le_max_left _ _), (hsf p hp).2.trans (le_max_left _ _)⟩
  have hsg' : ∀ p, g p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R := fun p hp =>
    ⟨(hsg p hp).1.trans (le_max_right _ _), (hsg p hp).2.trans (le_max_right _ _)⟩
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hMg 0)
  have hMg1 : 0 < Mg + 1 := by linarith
  refine ⟨κ * (Mf * (2 * R + 1) ^ 2 * ((Mg + 1) * C₀ * Real.exp (m * (2 * R)))),
    fun k a => ?_⟩
  set D := max |a 0| |a 1|
  set K' := (Mg + 1) * (C₀ * Real.exp (-m * (D - 2 * R))) with hK'
  have hinner : ∀ x : DSite n k, f (dpos n k x) ≠ 0 →
      spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G k x y ≤ K' := by
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
    have := hGs k x w (D - 2 * R) hw01 hwD
    have e : spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G k x y
        = (Mg + 1) * (spacing n ^ 2 * ∑ y, w y * G k x y) := by
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
        * G k x y
      = ∑ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| *
          (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G k x y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [htr]; ring
  have hterm : ∀ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| *
      (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G k x y)
      ≤ spacing n ^ 2 * |f (dpos n k x)| * K' := by
    intro x
    by_cases hfx : f (dpos n k x) = 0
    · simp [hfx]
    · exact mul_le_mul_of_nonneg_left (hinner x hfx) (by positivity)
  have hexp : Real.exp (-m * (D - 2 * R)) = Real.exp (m * (2 * R)) * Real.exp (-m * D) := by
    rw [← Real.exp_add]; ring_nf
  calc _ ≤ _ := hN k f (translate a g)
    _ = κ * ∑ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| *
          (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)| * G k x y) := by rw [hrw]
    _ ≤ κ * ∑ x : DSite n k, spacing n ^ 2 * |f (dpos n k x)| * K' :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hterm x) hκ
    _ = κ * ((spacing n ^ 2 * ∑ x : DSite n k, |f (dpos n k x)|) * K') := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ κ * ((Mf * (2 * R + 1) ^ 2) * K') := by gcongr
    _ = _ := by rw [hK', hexp]; ring

/-- **Averaging + Griffiths II at a fixed level:** with T = ⌈8K/ε²⌉ + 1 radii jε (j < T), some
radius r ≤ Tε has region boundary sum ≤ 1/2. Note Tε ≈ 8K/ε → ∞ as ε → 0: the averaging alone
loses one power of ε (shells are ε thin; the susceptibility controls ε² Σ, not ε Σ). -/
theorem sh1_level_smallBoundarySum {m₀ lam K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (n : ℕ)
    (hKn : ∀ (k : ℕ) (x : DSite n k), spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y| ≤ K) :
    ∀ (k : ℕ) (x : DSite n k), ∃ r : ℝ, 0 ≤ r ∧
      r ≤ ((⌈8 * K / spacing n ^ 2⌉₊ + 1 : ℕ) : ℝ) * spacing n ∧
        sh1_bdrySum n k m₀ lam x r ≤ 1 / 2 := by
  intro k x
  have hε := spacing_pos n
  set T : ℕ := ⌈8 * K / spacing n ^ 2⌉₊ + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT8 : 8 * K / spacing n ^ 2 ≤ T := by
    rw [hTdef]; push_cast; linarith [Nat.le_ceil (8 * K / spacing n ^ 2)]
  obtain ⟨j, hjT, hj⟩ := sh1_exists_radius m₀ lam 0 x hT
  refine ⟨0 + j * spacing n, by positivity, ?_, ?_⟩
  · rw [zero_add]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjT.le) hε.le
  · have hχ : spacing n ^ 2 * ∑ u, twoPt n k m₀ lam x u ≤ K := by
      refine le_trans (le_of_eq ?_) (hKn k x)
      congr 1
      exact Finset.sum_congr rfl fun u _ => (abs_of_nonneg (twoPt_nonneg m₀ lam x u)).symm
    have hS0 : 0 ≤ ∑ u, twoPt n k m₀ lam x u :=
      Finset.sum_nonneg fun u _ => twoPt_nonneg m₀ lam x u
    have hε2 : 0 < spacing n ^ 2 := by positivity
    have h8 : 8 * K ≤ T * spacing n ^ 2 := by rwa [div_le_iff₀ hε2] at hT8
    have key : 4 * (∑ u, twoPt n k m₀ lam x u) / T ≤ 1 / 2 := by
      rw [div_le_iff₀ hTr]
      nlinarith
    exact (sh1_bdrySum_le_shellSum hm hlam x _).trans (hj.trans key)

theorem sh1_K_nonneg_level {m₀ lam K : ℝ} (n : ℕ)
    (hKn : ∀ (k : ℕ) (x : DSite n k), spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y| ≤ K) :
    0 ≤ K := by
  have hpos : 0 < boxN n 0 := by unfold boxN; positivity
  refine le_trans ?_ (hKn 0 (⟨0, hpos⟩, ⟨0, hpos⟩))
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => abs_nonneg _)

/-- **A level-n susceptibility bound (uniform in the volume) gives exponential clustering at
level n, uniformly in the volume,** for every λ ≥ 0 (m₀ ≠ 0), at the explicit rate
m_n = log 2 / (T_n ε + 1), T_n = ⌈8K/ε²⌉ + 1, ε = 2⁻ⁿ. This rate tends to 0 as n → ∞
(m_n ≈ ε log 2 / (8K)): it is NOT uniform in the spacing. -/
theorem levelClustering_of_susceptibility {m₀ lam K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (n : ℕ)
    (hKn : ∀ (k : ℕ) (x : DSite n k), spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y| ≤ K) :
    0 < Real.log 2 / (((⌈8 * K / spacing n ^ 2⌉₊ + 1 : ℕ) : ℝ) * spacing n + 1) ∧
      LevelClustering m₀ lam n
        (Real.log 2 / (((⌈8 * K / spacing n ^ 2⌉₊ + 1 : ℕ) : ℝ) * spacing n + 1)) := by
  have hK0 := sh1_K_nonneg_level n hKn
  set L : ℝ := ((⌈8 * K / spacing n ^ 2⌉₊ + 1 : ℕ) : ℝ) * spacing n with hL
  have hL0 : 0 ≤ L := by rw [hL]; have := spacing_pos n; positivity
  have hdec := sh1_level_consumer (γ := 1 / 2) n hL0 (by norm_num) (by norm_num)
    (simonLiebIneq'_holds hm hlam) (regionGriffithsI_holds m₀ lam)
    (sh1_level_smallBoundarySum hm hlam n hKn) hK0 hKn
  have hlog : -Real.log (1 / 2 : ℝ) = Real.log 2 := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hlog] at hdec
  refine ⟨div_pos (Real.log_pos (by norm_num)) (by linarith), ?_⟩
  refine sh1_conditional_clustering_level n (C₀ := K * Real.exp (Real.log 2 * (0 / (L + 1) + 1)))
    (by positivity) (by norm_num : (0 : ℝ) ≤ 4) (fun k => twoPt n k m₀ lam)
    (fun k => PP2Newman.newman_hN hm hlam n k) ?_
  intro k x w D hw hD
  have := hdec k x w D hw hD
  simpa only [neg_div, neg_neg] using this

/-- In particular, the uniform susceptibility gives clustering at every fixed level. -/
theorem levelClustering_of_uniformSusceptibility {m₀ lam K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hK : UniformSusceptibility m₀ lam K) (n : ℕ) :
    ∃ m : ℝ, 0 < m ∧ LevelClustering m₀ lam n m :=
  ⟨_, levelClustering_of_susceptibility hm hlam n (hK n)⟩


/-- With Griffiths II, the node-M5 input `RegionSusceptibility` is a consequence of the uniform
susceptibility: the existing chain then needs only `SmallBoundarySum`. -/
theorem clustering_of_smallBoundarySum_of_susceptibility {m₀ lam l γ K : ℝ} (hm : m₀ ≠ 0)
    (hlam : 0 ≤ lam) (hl : 0 ≤ l) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hK : UniformSusceptibility m₀ lam K) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m :=
  clustering_of_M5 hm hlam hl hγ0 hγ1 (sh1_K_nonneg hK) hSmall
    (sh1_regionSusceptibility hm hlam hK l)

end PP2Target

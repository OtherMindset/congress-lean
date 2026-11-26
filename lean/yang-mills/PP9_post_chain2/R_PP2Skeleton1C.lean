import LongTable.R_PP2Skeleton1B

/-!
Part C of PP2Skeleton1 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Skeleton1.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound). Standing hypotheses:
J ≥ 0, row sums Σ_k J_ik ≤ r, 0 ≤ r < c.
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

import LongTable.Q_PP2SimonLieb4A

/-!
Part B of PP2SimonLieb4 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb4.lean)

FORMALIZED in this part (no sorry; axioms propext, Classical.choice, Quot.sound).
* `zc_ne` (complement partition function ≠ 0), `regionTwoPt_eq_tI`, `ratio_region`
  ([φ_xφ_j]_dec/[1]_dec = regionTwoPt B x j for EVERY j when x ∈ B), `twoPt_eq_tI`
  (twoPt v y = [φ_vφ_y e^{bdry}]_dec / [e^{bdry}]_dec).
* `adm_slG`, `adm_slG'`, `hasLineDerivAt_slG`, `inCone_slG'` (G = φ_y e^{bdry} and its partials
  in the cone 𝒞), `tI_slG'` (linearity), `decJ_row_le` (row sums of decJ + decJᵀ ≤ 4),
  `contraction_data`, `sl_sum_eq` (the bookkeeping of the δ_uy term and the boundary sum).
* **`simonLieb_box`** and **`simonLiebIneq'_holds`**: for m₀ ≠ 0, λ ≥ 0,
    `SimonLiebIneq' m₀ lam`, i.e. for every n, k, region B, x ∈ B and ANY y,
    twoPt x y ≤ regionTwoPt B x y + Σ_{u∈B} Σ_{v∈Bᶜ} bondJ u v · regionTwoPt B x u · twoPt v y;
  and `simonLiebIneq_holds` (`SimonLiebIneq`, y ∉ B) and `simonLiebTarget_holds`
  (`SimonLiebTarget`, the target of node M3), via `simonLiebIneq_of'`.

NOT formalized: nothing of (R1)–(R5) remains open for the finite box. The inputs that M6 consumes
besides Simon–Lieb (RegionGriffithsI, SmallBoundarySum, RegionSusceptibility, Newman) are not
touched here.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Target

open PP2LocalTime PP2Griffiths PP2SGD

variable {n k : ℕ}

/-- [φ_xφ_j]_dec / [1]_dec = regionTwoPt B x j for every j, when x ∈ B. -/
theorem ratio_region {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (B : Finset (DSite n k))
    {x : DSite n k} (hx : x ∈ B) (j : DSite n k) :
    tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun φ => φ x * φ j) /
        tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun _ => 1) =
      regionTwoPt n k m₀ lam B x j := by
  by_cases hj : j ∈ B
  · exact (regionTwoPt_eq_tI hm hlam B hx hj).symm
  · rw [tI_decJ_odd _ _ B hx hj, zero_div, regionTwoPt_out m₀ lam B x hj]

/-- twoPt v y = [φ_vφ_y e^{bdry}]_dec / [e^{bdry}]_dec. -/
theorem twoPt_eq_tI (m₀ lam : ℝ) (B : Finset (DSite n k)) (v y : DSite n k) :
    twoPt n k m₀ lam v y =
      tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0
          (fun φ => φ v * φ y * Real.exp (bdryCoupling B φ)) /
        tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0
          (fun φ => Real.exp (bdryCoupling B φ)) := by
  rw [twoPt_eq_decoupled m₀ lam B v y, tI_decJ_eq, tI_decJ_eq,
    mul_div_mul_left _ _ (decConst_ne m₀ lam)]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only
    ring

/-! ## The observable G = φ_y e^{bdry} and its partials -/

/-- G = φ_y e^{bdryCoupling}. -/
def slG (B : Finset (DSite n k)) (y : DSite n k) (φ : DField n k) : ℝ :=
  φ y * Real.exp (bdryCoupling B φ)

/-- ∂_j G = (δ_jy + φ_y Σ_v (bdryK_jv + bdryK_vj) φ_v) e^{bdryCoupling}. -/
def slG' (B : Finset (DSite n k)) (y j : DSite n k) (φ : DField n k) : ℝ :=
  ((Pi.single j (1 : ℝ) : DField n k) y +
    φ y * ∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v) * Real.exp (bdryCoupling B φ)

theorem adm_slG (B : Finset (DSite n k)) (y : DSite n k) :
    Adm (fun φ : DField n k => 1 + Real.exp (bdryCoupling B φ)) (slG B y) :=
  ((adm_exp_bdry B).mul_coord y).congr fun _ => rfl

theorem single_abs_le (j y : DSite n k) : |(Pi.single j (1 : ℝ) : DField n k) y| ≤ 1 := by
  rw [Pi.single_apply]; split_ifs <;> simp

theorem single_nonneg' (j y : DSite n k) : 0 ≤ (Pi.single j (1 : ℝ) : DField n k) y := by
  rw [Pi.single_apply]; split_ifs <;> simp

theorem adm_slG' (B : Finset (DSite n k)) (y j : DSite n k) :
    Adm (fun φ : DField n k => 1 + Real.exp (bdryCoupling B φ)) (slG' B y j) := by
  have hBc := continuous_bdryCoupling B
  refine ⟨by unfold slG'; fun_prop,
    1 + ∑ v, |bdryK n k B j v + bdryK n k B v j|, 2, fun φ => ?_⟩
  show |slG' B y j φ| ≤ (1 + ∑ v, |bdryK n k B j v + bdryK n k B v j|) *
    Real.exp (2 * ∑ x, |φ x|) * (1 + Real.exp (bdryCoupling B φ))
  set S := ∑ x, |φ x| with hS
  set A := ∑ v, |bdryK n k B j v + bdryK n k B v j| with hA
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hES : 1 ≤ Real.exp S := Real.one_le_exp hS0
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hv : ∀ v, |φ v| ≤ Real.exp S := abs_le_exp_sum φ
  have hsum : |∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v| ≤ A * Real.exp S := by
    calc |∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v|
        ≤ ∑ v, |(bdryK n k B j v + bdryK n k B v j) * φ v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v, |bdryK n k B j v + bdryK n k B v j| * Real.exp S :=
          Finset.sum_le_sum fun v _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv v) (abs_nonneg _)
      _ = A * Real.exp S := by rw [Finset.sum_mul]
  have e2 : Real.exp (2 * S) = Real.exp S * Real.exp S := by rw [two_mul, Real.exp_add]
  have hg : |(Pi.single j (1 : ℝ) : DField n k) y +
      φ y * ∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v| ≤ (1 + A) * Real.exp (2 * S) := by
    calc _ ≤ |(Pi.single j (1 : ℝ) : DField n k) y| +
          |φ y * ∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v| := abs_add_le _ _
      _ ≤ 1 + Real.exp S * (A * Real.exp S) := by
          rw [abs_mul]
          exact add_le_add (single_abs_le j y)
            (mul_le_mul (hv y) hsum (abs_nonneg _) (Real.exp_pos _).le)
      _ ≤ (1 + A) * Real.exp (2 * S) := by
          rw [e2]
          have h11 : 1 ≤ Real.exp S * Real.exp S := by nlinarith
          nlinarith
  unfold slG'
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc _ ≤ ((1 + A) * Real.exp (2 * S)) * (1 + Real.exp (bdryCoupling B φ)) :=
        mul_le_mul hg (by linarith [Real.exp_pos (bdryCoupling B φ)]) (Real.exp_pos _).le
          (by positivity)
    _ = _ := rfl

theorem hasLineDerivAt_slG (B : Finset (DSite n k)) (y j : DSite n k) (φ : DField n k) :
    HasLineDerivAt ℝ (slG B y) (slG' B y j φ) φ (Pi.single j 1) := by
  have hQ := hasLineDerivAt_quadE (bdryK n k B) φ j
  rw [quadE_bdryK_fun] at hQ
  have hc := hasLineDerivAt_coord j y φ
  unfold HasLineDerivAt at hQ hc ⊢
  unfold slG
  have := hc.fun_mul hQ.exp
  convert this using 1
  simp only [slG', zero_smul, add_zero]
  ring

theorem inCone_slG' (B : Finset (DSite n k)) (y j : DSite n k) : InCone (slG' B y j) := by
  refine ⟨fun φ => (Pi.single j (1 : ℝ) : DField n k) y +
      φ y * ∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v,
    quadE (bdryK n k B), ?_, IsPosPoly.quadForm (bdryK_nonneg B), fun φ => ?_⟩
  · exact (IsPosPoly.const (single_nonneg' j y)).add ((IsPosPoly.coord y).mul
      (IsPosPoly.linForm fun v => add_nonneg (bdryK_nonneg B j v) (bdryK_nonneg B v j)))
  · simp only [slG', quadE_bdryK]

/-- Linearity: [∂_jG]_dec = δ_jy [e^{bdry}]_dec + Σ_v (bdryK_jv + bdryK_vj) [φ_vφ_y e^{bdry}]_dec. -/
theorem tI_slG' {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (B : Finset (DSite n k))
    (y j : DSite n k) :
    tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (slG' B y j) =
      (Pi.single j (1 : ℝ) : DField n k) y *
          tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0
            (fun φ => Real.exp (bdryCoupling B φ)) +
        ∑ v, (bdryK n k B j v + bdryK n k B v j) *
          tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0
            (fun φ => φ v * φ y * Real.exp (bdryCoupling B φ)) := by
  have hint := hint_dec hm hlam B
  have hE := adm_exp_bdry B
  have I0 := hint _ hE
  have Iv : ∀ v, Integrable fun φ => φ v * φ y * Real.exp (bdryCoupling B φ) *
      Real.exp (quadE (decJ n k B) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ :=
    fun v => hint _ (((hE.mul_coord y).mul_coord v).congr fun φ => (mul_assoc _ _ _).symm)
  have hpt : ∀ φ, slG' B y j φ * Real.exp (quadE (decJ n k B) φ) *
      tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ =
      (Pi.single j (1 : ℝ) : DField n k) y * (Real.exp (bdryCoupling B φ) *
        Real.exp (quadE (decJ n k B) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) +
      ∑ v, (bdryK n k B j v + bdryK n k B v j) * (φ v * φ y * Real.exp (bdryCoupling B φ) *
        Real.exp (quadE (decJ n k B) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) := by
    intro φ
    have hs : φ y * ∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v =
        ∑ v, (bdryK n k B j v + bdryK n k B v j) * (φ v * φ y) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    unfold slG'
    rw [hs, add_mul, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun v _ => by ring
  unfold tI
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add (I0.const_mul _) (integrable_finsetSum _ fun v _ => (Iv v).const_mul _),
    integral_const_mul, integral_finsetSum _ fun v _ => (Iv v).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _

/-! ## Contraction data and the final bookkeeping -/

theorem contraction_data {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) :
    (0 < betaQ n lam ∨ 0 < alphaQ n m₀ lam) ∧ ∃ c' C₀ : ℝ, 4 < c' ∧
      ∀ t, 0 ≤ t → c' * t - C₀ ≤ fq (alphaQ n m₀ lam) (betaQ n lam) t := by
  rcases hlam.lt_or_eq with hpos | h0
  · have hbpos : 0 < betaQ n lam := by unfold betaQ; have := spacing_pos n; positivity
    exact ⟨Or.inl hbpos, 5, (5 - alphaQ n m₀ lam) ^ 2 / (4 * betaQ n lam), by norm_num,
      fun t _ => fq_ge_lin hbpos 5 t⟩
  · subst h0
    have hε := spacing_pos n
    have hα : alphaQ n m₀ 0 = 4 + spacing n ^ 2 * m₀ ^ 2 := by unfold alphaQ; ring
    have hα4 : 4 < alphaQ n m₀ 0 := by
      rw [hα]; have : 0 < spacing n ^ 2 * m₀ ^ 2 := by positivity
      linarith
    exact ⟨Or.inr (by linarith), alphaQ n m₀ 0, 0, hα4, fun t _ => by unfold fq betaQ; simp⟩

/-- The bookkeeping: the δ_jy term gives R y, the boundary term gives the Simon–Lieb sum. -/
theorem sl_sum_eq (B : Finset (DSite n k)) (y : DSite n k) (R t : DSite n k → ℝ)
    (hR : ∀ j, j ∉ B → R j = 0) :
    ∑ j, ((Pi.single j (1 : ℝ) : DField n k) y +
        ∑ v, (bdryK n k B j v + bdryK n k B v j) * t v) * R j =
      R y + ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * R u * t v := by
  have h1 : ∑ j, (Pi.single j (1 : ℝ) : DField n k) y * R j = R y := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne (Ne.symm hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ y) h
  have h2 : ∑ j, (∑ v, (bdryK n k B j v + bdryK n k B v j) * t v) * R j =
      ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * R u * t v := by
    rw [← Fintype.sum_ite_mem B (fun u => ∑ v ∈ Bᶜ, bondJ n k u v * R u * t v)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ B
    · simp only [hj, ↓reduceIte]
      rw [Finset.sum_mul, ← Fintype.sum_ite_mem Bᶜ (fun v => bondJ n k j v * R j * t v)]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ B
      · simp [bdryK, hj, hv]
      · simp [bdryK, hj, hv]; ring
    · simp only [hj, ↓reduceIte, hR j hj, mul_zero]
  rw [← h1, ← h2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => add_mul _ _ _

/-! ## The Simon–Lieb inequality -/

/-- **The Simon–Lieb inequality with the local term, quartic Dirichlet box** (BFS CMP 83,
Theorem 6.1 with F = φ_y; m₀ ≠ 0, λ ≥ 0): for x ∈ B and any y,
  twoPt x y ≤ regionTwoPt B x y + Σ_{u∈B} Σ_{v∉B} bondJ u v · regionTwoPt B x u · twoPt v y.
Proof: strong Gaussian domination (`strong_gaussian_domination`) for the decoupled measure
e^{Q_{decJ}} W_0 with G = φ_y e^{bdry}, envelope 1 + e^{bdry} (`hint_dec`); then
⟨φ_xφ_j⟩_dec = regionTwoPt B x j (`ratio_region`), divide by ⟨e^{bdry}⟩_dec (`twoPt_eq_tI`). -/
theorem simonLieb_box {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (B : Finset (DSite n k))
    {x : DSite n k} (y : DSite n k) (hx : x ∈ B) :
    twoPt n k m₀ lam x y ≤ regionTwoPt n k m₀ lam B x y +
      ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * regionTwoPt n k m₀ lam B x u * twoPt n k m₀ lam v y := by
  have hint := hint_dec hm hlam B
  obtain ⟨hab, c', C₀, hc', hf⟩ := contraction_data (n := n) hm hlam
  have hsgd := strong_gaussian_domination (K := decJ n k B) (decJ_nonneg B)
    (betaQ_nonneg hlam) hab (Ψ := fun φ => 1 + Real.exp (bdryCoupling B φ))
    (one_le_envelope B) hint (r := 4) (by norm_num) hc' (decJ_row_le B) hf (adm_slG B y)
    (adm_slG' B y) (hasLineDerivAt_slG B y) (inCone_slG' B y) x
  have hZd : 0 < tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun _ => 1) :=
    tI_pos_of (fun _ => one_pos) (hint _ (Adm.const (one_le_envelope B) 1))
  have hZb : 0 < tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0
      (fun φ => Real.exp (bdryCoupling B φ)) :=
    tI_pos_of (fun _ => Real.exp_pos _) (hint _ (adm_exp_bdry B))
  have hL : (fun φ : DField n k => φ x * slG B y φ) =
      fun φ => φ x * φ y * Real.exp (bdryCoupling B φ) := by
    funext φ; unfold slG; ring
  rw [hL] at hsgd
  have hF3 : ∀ j, tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (slG' B y j) /
      tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun φ => Real.exp (bdryCoupling B φ))
      = (Pi.single j (1 : ℝ) : DField n k) y +
        ∑ v, (bdryK n k B j v + bdryK n k B v j) * twoPt n k m₀ lam v y := by
    intro j
    rw [tI_slG' hm hlam B y j, add_div, mul_div_assoc, div_self hZb.ne', mul_one,
      Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_div_assoc, ← twoPt_eq_tI]
  rw [twoPt_eq_tI m₀ lam B x y]
  calc _ ≤ (∑ j, (tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (slG' B y j) /
          tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun _ => 1)) *
          tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun φ => φ x * φ j)) /
        tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0
          (fun φ => Real.exp (bdryCoupling B φ)) := div_le_div_of_nonneg_right hsgd hZb.le
    _ = ∑ j, (tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (slG' B y j) /
          tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0
            (fun φ => Real.exp (bdryCoupling B φ))) *
          (tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun φ => φ x * φ j) /
            tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun _ => 1)) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, ((Pi.single j (1 : ℝ) : DField n k) y +
          ∑ v, (bdryK n k B j v + bdryK n k B v j) * twoPt n k m₀ lam v y) *
          regionTwoPt n k m₀ lam B x j :=
        Finset.sum_congr rfl fun j _ => by rw [hF3 j, ratio_region hm hlam B hx j]
    _ = _ := sl_sum_eq B y _ _ fun j hj => regionTwoPt_out m₀ lam B x hj

/-- **SimonLiebIneq' holds** (the target of node M3 in its strengthened M6 form). -/
theorem simonLiebIneq'_holds {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) :
    SimonLiebIneq' m₀ lam :=
  fun _ _ B _ y hx => simonLieb_box hm hlam B y hx

/-- **SimonLiebIneq holds** (y ∉ B). -/
theorem simonLiebIneq_holds {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) :
    SimonLiebIneq m₀ lam :=
  simonLiebIneq_of' (simonLiebIneq'_holds hm hlam)

/-- **The target of node M3.** -/
theorem simonLiebTarget_holds : SimonLiebTarget :=
  fun _ _ hm hlam => simonLiebIneq_holds hm hlam

end PP2Target

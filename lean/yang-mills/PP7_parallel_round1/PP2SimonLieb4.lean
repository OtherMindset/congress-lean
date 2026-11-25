import LongTable.PP2SimonLieb3
import LongTable.PP2M6Smeared

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M3, session 4.
Step (R5) of the route in `PP2SimonLieb`: the Simon–Lieb inequality (Lieb–Rivasseau form, with
the local term) for the quartic Dirichlet-box model, from strong Gaussian domination (R4) applied
to the DECOUPLED measure, as in Brydges–Fröhlich–Spencer, CMP 83 (1982), Theorem 6.1.

Source: BFS CMP 83, §6 ((6.2), Theorem 6.1), uploaded copy read through the site in sessions 1–2.
Not re-read this session.

DEFINITIONS.
* `decJ n k B x y = Jnn x y` if x, y are both in B or both outside B, else 0 (the pair matrix of
  the decoupled measure: the nearest-neighbour couplings across ∂B removed).
* `bdryK n k B u v = bondJ u v` for u ∈ B, v ∉ B, else 0 (so Q_{bdryK} = `bdryCoupling B`).
* `flipσ B` (true exactly off B) and `flipB B φ` (φ with its sign flipped on Bᶜ).
* `slG B y φ = φ_y e^{bdryCoupling B φ}` and its partials
  `slG' B y j φ = (δ_jy + φ_y Σ_v (bdryK_jv + bdryK_vj) φ_v) e^{bdryCoupling B φ}`.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* The decoupled weight in local-time form: `quadE_restrict`, `tw_restrict`, `decW_eq`
  (e^{Q_{decJ}} W_0 = κ² · decWeight_B, κ = e^{|Λ|·3λε²c²}), `tI_decJ_eq`, and `bdry_decW`
  (e^{bdry} e^{Q_{decJ}} W_0 = c · e^{Q_{Jnn}} W_0, c > 0).
* Sign flip off B: `quadE_decJ_flip`, `bdry_flip` (bdry ↦ −bdry), `tw_flip`, `sumAbs_flip`;
  oddness `tI_decJ_odd`: [φ_x φ_j]_dec = 0 for x ∈ B, j ∉ B.
* **`hint_dec`** (m₀ ≠ 0, λ ≥ 0): the admissible class with envelope Ψ = 1 + e^{bdryCoupling} is
  integrable against e^{Q_{decJ}} W_0. Proof: e^{Q_{decJ}} ≤ e^{Q_{decJ}}(e^{bdry} + e^{−bdry}),
  e^{bdry} e^{Q_{decJ}} W_0 ∝ the full weight (`integrable_tau`), and the e^{−bdry} term is the
  e^{bdry} term composed with the measure-preserving flip off B.
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

/-! ## The decoupled pair matrix and the boundary matrix -/

/-- The pair matrix of the decoupled measure: Jnn with the couplings across ∂B removed. -/
def decJ (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k) : ℝ :=
  if (x ∈ B ↔ y ∈ B) then Jnn n k x y else 0

/-- The boundary matrix: bondJ u v for u ∈ B, v ∉ B, and 0 otherwise. -/
def bdryK (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k) : ℝ :=
  if x ∈ B ∧ y ∉ B then bondJ n k x y else 0

theorem decJ_nonneg (B : Finset (DSite n k)) (x y : DSite n k) : 0 ≤ decJ n k B x y := by
  unfold decJ; split_ifs
  · exact Jnn_nonneg x y
  · exact le_rfl

theorem decJ_le (B : Finset (DSite n k)) (x y : DSite n k) : decJ n k B x y ≤ Jnn n k x y := by
  unfold decJ; split_ifs
  · exact le_rfl
  · exact Jnn_nonneg x y

theorem bdryK_nonneg (B : Finset (DSite n k)) (x y : DSite n k) : 0 ≤ bdryK n k B x y := by
  unfold bdryK; split_ifs with h
  · exact bondJ_nonneg (by rintro rfl; exact h.2 h.1)
  · exact le_rfl

theorem quadE_bdryK (B : Finset (DSite n k)) (φ : DField n k) :
    quadE (bdryK n k B) φ = bdryCoupling B φ := by
  unfold quadE bdryCoupling
  rw [← Fintype.sum_ite_mem B]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ B
  · simp only [hu, ↓reduceIte]
    rw [← Fintype.sum_ite_mem Bᶜ]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ B <;> simp [bdryK, hu, hv]
  · simp only [hu, ↓reduceIte]
    exact Finset.sum_eq_zero fun v _ => by simp [bdryK, hu]

theorem quadE_bdryK_fun (B : Finset (DSite n k)) :
    quadE (bdryK n k B) = bdryCoupling B := funext (quadE_bdryK B)

theorem continuous_bdryCoupling (B : Finset (DSite n k)) :
    Continuous (bdryCoupling B : DField n k → ℝ) := by
  rw [← quadE_bdryK_fun]; exact continuous_quadE _

/-- Row sums of decJ + decJᵀ are ≤ 4. -/
theorem decJ_row_le (B : Finset (DSite n k)) (i : DSite n k) :
    ∑ j, (decJ n k B i j + decJ n k B j i) ≤ 4 :=
  (Finset.sum_le_sum fun j _ => add_le_add (decJ_le B i j) (decJ_le B j i)).trans
    (Jsym_row_le i)

/-! ## The decoupled weight in local-time form -/

theorem quadE_restrict (B : Finset (DSite n k)) (φ : DField n k) :
    quadE (Jnn n k) (restrictIn B φ) + quadE (Jnn n k) (restrictOut B φ) =
      quadE (decJ n k B) φ := by
  unfold quadE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [restrictIn, restrictOut, decJ, hx, hy]

theorem tw_restrict (a b : ℝ) (B : Finset (DSite n k)) (φ : DField n k) :
    tw a b 0 (restrictIn B φ) * tw a b 0 (restrictOut B φ) = tw a b 0 φ := by
  unfold tw
  rw [← Real.exp_add]
  congr 1
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ B <;> simp [restrictIn, restrictOut, fq, hx]

/-- e^{Q_{decJ}} W_0 = κ² · decWeight_B, κ = e^{|Λ|·3λε²c²}. -/
theorem decW_eq (m₀ lam : ℝ) (B : Finset (DSite n k)) (φ : DField n k) :
    Real.exp (quadE (decJ n k B) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ =
      Real.exp ((Fintype.card (DSite n k) : ℝ) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2))
        ^ 2 * decWeight n k m₀ lam (Polynomial.X ^ 4) B φ := by
  have h1 := qweight_eq_tw m₀ lam (restrictIn B φ)
  have h2 := qweight_eq_tw m₀ lam (restrictOut B φ)
  have hd : decWeight n k m₀ lam (Polynomial.X ^ 4) B φ =
      qweight n k m₀ lam (restrictIn B φ) * qweight n k m₀ lam (restrictOut B φ) := rfl
  rw [← quadE_restrict B φ, ← tw_restrict (alphaQ n m₀ lam) (betaQ n lam) B φ, hd, h1, h2,
    Real.exp_add, Real.exp_neg]
  field_simp

theorem tI_decJ_eq (m₀ lam : ℝ) (B : Finset (DSite n k)) (F : DField n k → ℝ) :
    tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 F =
      Real.exp ((Fintype.card (DSite n k) : ℝ) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2))
        ^ 2 * ∫ φ, F φ * decWeight n k m₀ lam (Polynomial.X ^ 4) B φ := by
  unfold tI
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only
  rw [mul_assoc, decW_eq]
  ring

/-- e^{bdry} e^{Q_{decJ}} W_0 is a constant multiple of the full weight e^{Q_{Jnn}} W_0. -/
theorem bdry_decW (m₀ lam : ℝ) (B : Finset (DSite n k)) : ∃ c : ℝ, 0 < c ∧ ∀ φ : DField n k,
    Real.exp (bdryCoupling B φ) *
        (Real.exp (quadE (decJ n k B) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) =
      c * (Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) := by
  set N : ℝ := (Fintype.card (DSite n k) : ℝ) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)
    with hN
  set L : ℝ := lam * spacing n ^ 2 *
    ((Fintype.card (DSite n k) : ℝ) * wickPoly (Polynomial.X ^ 4) (freeVar n m₀) 0) with hL
  refine ⟨Real.exp (N - L), Real.exp_pos _, fun φ => ?_⟩
  have h1 := decW_eq m₀ lam B φ
  have h2 := dweight_split m₀ lam (Polynomial.X ^ 4) B φ
  have h3 := qweight_eq_tw m₀ lam φ
  have hX : Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ =
      Real.exp N * (decWeight n k m₀ lam (Polynomial.X ^ 4) B φ *
        Real.exp (bdryCoupling B φ) * Real.exp L) := by
    rw [← h2]
    change _ = Real.exp N * qweight n k m₀ lam φ
    rw [h3, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [← hN] at h1
  rw [h1, hX, Real.exp_sub]
  field_simp

/-! ## The sign flip off B -/

/-- The flip pattern: true (flip) exactly off B. -/
def flipσ (B : Finset (DSite n k)) : DSite n k → Bool := fun z => decide (z ∉ B)

/-- φ with its sign flipped on Bᶜ. -/
def flipB (B : Finset (DSite n k)) (φ : DField n k) : DField n k := flipSigns (flipσ B) φ

theorem flipB_in {B : Finset (DSite n k)} {z : DSite n k} (hz : z ∈ B) (φ : DField n k) :
    flipB B φ z = φ z := by
  simp [flipB, flipσ, flipSigns, sgnMul, hz]

theorem flipB_out {B : Finset (DSite n k)} {z : DSite n k} (hz : z ∉ B) (φ : DField n k) :
    flipB B φ z = -φ z := by
  simp [flipB, flipσ, flipSigns, sgnMul, hz]

theorem quadE_decJ_flip (B : Finset (DSite n k)) (φ : DField n k) :
    quadE (decJ n k B) (flipB B φ) = quadE (decJ n k B) φ := by
  unfold quadE
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;>
    simp [decJ, flipB_in, flipB_out, hx, hy]

theorem bdry_flip (B : Finset (DSite n k)) (φ : DField n k) :
    bdryCoupling B (flipB B φ) = -bdryCoupling B φ := by
  unfold bdryCoupling
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [flipB_in hu, flipB_out (Finset.mem_compl.mp hv)]
  ring

theorem tw_flip (a b : ℝ) (B : Finset (DSite n k)) (φ : DField n k) :
    tw a b 0 (flipB B φ) = tw a b 0 φ := by
  unfold tw
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ B
  · rw [flipB_in hx]
  · rw [flipB_out hx, neg_sq]

theorem sumAbs_flip (B : Finset (DSite n k)) (φ : DField n k) :
    ∑ x, |flipB B φ x| = ∑ x, |φ x| := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ B
  · rw [flipB_in hx]
  · rw [flipB_out hx, abs_neg]

/-- **Oddness:** [φ_x φ_j]_dec = 0 for x ∈ B, j ∉ B (the decoupled weight is invariant under the
sign flip off B, and φ_x φ_j changes sign). -/
theorem tI_decJ_odd (a b : ℝ) (B : Finset (DSite n k)) {x j : DSite n k} (hx : x ∈ B)
    (hj : j ∉ B) : tI (decJ n k B) a b 0 (fun φ => φ x * φ j) = 0 := by
  set F : DField n k → ℝ := fun φ => φ x * φ j * Real.exp (quadE (decJ n k B) φ) * tw a b 0 φ
    with hF
  have h := (measurePreserving_flipEquiv (flipσ B)).integral_comp' F
  have hFl : ∀ φ, F (flipEquiv (flipσ B) φ) = -F φ := by
    intro φ
    change F (flipB B φ) = -F φ
    simp only [hF, quadE_decJ_flip, tw_flip, flipB_in hx, flipB_out hj]
    ring
  simp_rw [hFl, integral_neg] at h
  have h0 : ∫ φ, F φ = 0 := by linarith
  exact h0

/-! ## Integrability with the envelope Ψ = 1 + e^{bdryCoupling} -/

/-- **Integrability for the decoupled measure** (m₀ ≠ 0, λ ≥ 0): every observable of the
admissible class with envelope 1 + e^{bdryCoupling} is integrable against e^{Q_{decJ}} W_0. -/
theorem hint_dec {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (B : Finset (DSite n k)) :
    ∀ H, Adm (fun φ : DField n k => 1 + Real.exp (bdryCoupling B φ)) H →
      Integrable fun φ => H φ * Real.exp (quadE (decJ n k B) φ) *
        tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ := by
  rintro H ⟨hc, C, a', hb⟩
  obtain ⟨c, hc0, hu⟩ := bdry_decW m₀ lam B
  have hcont : Continuous fun φ : DField n k => Real.exp (a' * ∑ x, |φ x|) :=
    (continuous_const.mul (continuous_finsetSum _ fun x _ => (continuous_apply x).abs)).rexp
  have hh : Integrable fun φ : DField n k => Real.exp (a' * ∑ x, |φ x|) *
      Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ :=
    integrable_tau hm hlam (fun x => le_refl _) hcont 1 a' fun φ => by
      rw [abs_of_pos (Real.exp_pos _), one_mul]
  have hhσ : Integrable fun φ : DField n k => Real.exp (a' * ∑ x, |flipB B φ x|) *
      Real.exp (quadE (Jnn n k) (flipB B φ)) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 (flipB B φ) :=
    (measurePreserving_flipEquiv (flipσ B)).integrable_comp_of_integrable hh
  have hBc := continuous_bdryCoupling B
  refine ((hh.const_mul (2 * (|C| * c))).add (hhσ.const_mul (|C| * c))).mono'
    (by fun_prop : Continuous fun φ => H φ * Real.exp (quadE (decJ n k B) φ) *
      tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => ?_)
  have e1 := hu φ
  have e2 := hu (flipB B φ)
  rw [bdry_flip, quadE_decJ_flip, tw_flip] at e2
  simp only [Pi.add_apply]
  rw [sumAbs_flip, tw_flip]
  set E := Real.exp (a' * ∑ x, |φ x|) with hE
  set P := Real.exp (bdryCoupling B φ) with hP
  set M := Real.exp (-bdryCoupling B φ) with hM
  set W := Real.exp (quadE (decJ n k B) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ with hW
  have hW0 : 0 < W := mul_pos (Real.exp_pos _) (tw_pos _ _ _ _)
  have hE0 : 0 < E := Real.exp_pos _
  have hP0 : 0 < P := Real.exp_pos _
  have hPM : 1 ≤ P + M := by
    have := Real.add_one_le_exp (bdryCoupling B φ)
    have := Real.add_one_le_exp (-bdryCoupling B φ)
    linarith
  have h1 : |H φ| ≤ C * E * (1 + P) := hb φ
  have hH : |H φ| ≤ |C| * E * (1 + P) :=
    h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hE0.le)
      (by positivity))
  rw [Real.norm_eq_abs, mul_assoc (H φ), abs_mul, abs_of_pos hW0]
  have hWle : W ≤ P * W + M * W := by nlinarith
  calc |H φ| * W ≤ (|C| * E * (1 + P)) * W := mul_le_mul_of_nonneg_right hH hW0.le
    _ = |C| * E * (W + P * W) := by ring
    _ ≤ |C| * E * ((P * W + M * W) + P * W) := by gcongr
    _ = |C| * E * (c * (Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ)
          + c * (Real.exp (quadE (Jnn n k) (flipB B φ)) *
            tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ)
          + c * (Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ)) := by
        rw [hP, hM, hW, e1, e2]
    _ = _ := by ring

/-! ## The decoupled expectations -/

theorem tI_pos_of {K : DSite n k → DSite n k → ℝ} {a b : ℝ} {F : DField n k → ℝ}
    (hF : ∀ φ, 0 < F φ) (h : Integrable fun φ => F φ * Real.exp (quadE K φ) * tw a b 0 φ) :
    0 < tI K a b 0 F := by
  unfold tI
  have hpos : ∀ φ, 0 < F φ * Real.exp (quadE K φ) * tw a b 0 φ := fun φ =>
    mul_pos (mul_pos (hF φ) (Real.exp_pos _)) (tw_pos a b 0 φ)
  rw [integral_pos_iff_support_of_nonneg (fun φ => (hpos φ).le) h]
  have : Function.support (fun φ => F φ * Real.exp (quadE K φ) * tw a b 0 φ) = Set.univ :=
    Set.eq_univ_of_forall fun φ => (hpos φ).ne'
  rw [this]
  exact isOpen_univ.measure_pos volume univ_nonempty

theorem one_le_envelope (B : Finset (DSite n k)) (φ : DField n k) :
    1 ≤ 1 + Real.exp (bdryCoupling B φ) := by
  linarith [Real.exp_pos (bdryCoupling B φ)]

theorem adm_exp_bdry (B : Finset (DSite n k)) :
    Adm (fun φ : DField n k => 1 + Real.exp (bdryCoupling B φ))
      (fun φ => Real.exp (bdryCoupling B φ)) := by
  refine ⟨(continuous_bdryCoupling B).rexp, 1, 0, fun φ => ?_⟩
  rw [abs_of_pos (Real.exp_pos _), zero_mul, Real.exp_zero, one_mul, one_mul]
  linarith

/-- The complement partition function is nonzero. -/
theorem zc_ne {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (B : Finset (DSite n k)) :
    ∫ η : {x // x ∉ B} → ℝ, qweight n k m₀ lam (zeroExtC B η) ≠ 0 := by
  have hpos := tI_pos_of (fun _ => one_pos)
    (hint_dec hm hlam B (fun _ => 1) (Adm.const (one_le_envelope B) 1))
  rw [tI_decJ_eq] at hpos
  have h2 := integral_decoupled m₀ lam (Polynomial.X ^ 4) B (fun _ => 1)
  intro h0
  have h0' : ∫ η : {x // x ∉ B} → ℝ,
      dweight n k m₀ lam (Polynomial.X ^ 4) (zeroExtC B η) = 0 := h0
  rw [h0', mul_zero] at h2
  have h3 : ∫ φ, (fun _ : DField n k => (1 : ℝ)) φ *
      decWeight n k m₀ lam (Polynomial.X ^ 4) B φ = 0 := h2
  rw [h3, mul_zero] at hpos
  exact lt_irrefl _ hpos

theorem decConst_ne (m₀ lam : ℝ) :
    Real.exp ((Fintype.card (DSite n k) : ℝ) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2))
      ^ 2 ≠ 0 := by positivity

theorem regionTwoPt_eq_tI {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (B : Finset (DSite n k))
    {x j : DSite n k} (hx : x ∈ B) (hj : j ∈ B) :
    regionTwoPt n k m₀ lam B x j =
      tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun φ => φ x * φ j) /
        tI (decJ n k B) (alphaQ n m₀ lam) (betaQ n lam) 0 (fun _ => 1) := by
  rw [← decoupled_twoPt m₀ lam B (zc_ne hm hlam B) x j, tI_decJ_eq, tI_decJ_eq,
    mul_div_mul_left _ _ (decConst_ne m₀ lam)]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp [restrictIn, hx, hj]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp

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

import LongTable.Q_PP2SimonLieb3C
import LongTable.Q_PP2M6Smeared

/-!
Part A of PP2SimonLieb4 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb4.lean)
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

end PP2Target

end

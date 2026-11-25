import LongTable.Q_PP2SimonLieb4B
import LongTable.Q_PP2NewmanB
import LongTable.Q_PP2Limit2B

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Assembly.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), assembly node.
Discharges `RegionGriffithsI` (Griffiths I for the Dirichlet region measures, PP2SimonLieb) and
wires the end-to-end clustering / limit-point / V3-target chain down to the two node-M5 inputs
`SmallBoundarySum` and `RegionSusceptibility`.

Proof of Griffiths I on a region B: on ℝ^B (ψ ↦ zeroExt B ψ), the quartic weight factors as
exp(coupling (zeroExt ψ)) · evenWeight (zeroExt ψ) (`PP2Griffiths.dweight_eq`); a sign flip σ of
the B-coordinates is the sign flip σ' (σ on B, no flip off B) of the extended field, so the even
part is flip-invariant (`evenWeight_flip`); the coupling and ψ_x ψ_u, composed with zeroExt, are
polynomials with nonnegative coefficients (`asm_isPosPoly_comp_zeroExt`); `griffiths_first_inv`
then gives numerator ≥ 0, and the denominator is ∫ of a positive function. No hypotheses on m₀, λ
are needed: outside λ ≥ 0, m₀ ≠ 0 the statement holds on the Bochner convention (a non-integrable
integrand has integral 0), and sign averaging is itself proved on that convention.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* `asm_isPosPoly_prod`, `asm_isPosPoly_zeroExt_coord`, `asm_isPosPoly_comp_zeroExt`,
  `asm_zeroExt_flip`, `asm_evenWeight_zeroExt_flip` (helpers).
* **`regionGriffithsI_holds`** : ∀ m₀ lam, RegionGriffithsI m₀ lam (all m₀, λ).
* **`clustering_of_M5`**: m₀ ≠ 0, λ ≥ 0, SmallBoundarySum, RegionSusceptibility ⟹
  ∃ m > 0, FiniteCutoffClustering m₀ λ m (Simon–Lieb from `simonLiebIneq'_holds`, Newman from
  `PP2Newman.clustering_of_simonLieb_newman`, Griffiths I from `regionGriffithsI_holds`).
* **`limitPoint_of_M5`**: the same inputs and `SchwartzSeparable` ⟹ ∃ Z, IsLimitPoint m₀ λ Z.
* `M5Inputs m₀ λ` (∃ l γ A with the side conditions, SmallBoundarySum and RegionSusceptibility),
  `clustering_of_M5Inputs`, `limitPoint_of_M5Inputs`, and
  **`phiFourTwoGapV3_of_M5`**: (∀ m₀ > 0, ∃ λ₀ > 0, ∀ λ ∈ (0, λ₀), M5Inputs m₀ λ ∧
  (∀ Z, IsLimitPoint m₀ λ Z → IsNonGaussian Z)) → SchwartzSeparable → PhiFourTwoGapV3.

NOT formalized (the hypotheses that remain for PhiFourTwoGapV3 along this route):
* `SmallBoundarySum m₀ λ l γ` with γ < 1 (BFS (7.4), node M5), uniform in n, k, centre;
* `RegionSusceptibility m₀ λ l A` (node M5), uniform in n, k, centre;
* non-Gaussianity of every limit point (`IsNonGaussian`);
* `SchwartzSeparable` (true in mathematics; not proved in this project).
Nothing else: Simon–Lieb, Newman and Griffiths I for regions are discharged.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Target

open PP2Griffiths

variable {n k : ℕ}

/-! ## Griffiths I for the region measures -/

theorem asm_isPosPoly_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] (s : Finset κ)
    {f : κ → (ι → ℝ) → ℝ} (hf : ∀ j ∈ s, IsPosPoly (f j)) :
    IsPosPoly (fun φ => ∏ j ∈ s, f j φ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPosPoly.const (ι := ι) zero_le_one
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem asm_isPosPoly_zeroExt_coord (B : Finset (DSite n k)) (x : DSite n k) :
    IsPosPoly (fun ψ : {z // z ∈ B} → ℝ => zeroExt B ψ x) := by
  by_cases hx : x ∈ B
  · simp only [zeroExt, hx, ↓reduceDIte]; exact IsPosPoly.coord _
  · simp only [zeroExt, hx, ↓reduceDIte]; exact IsPosPoly.const le_rfl

theorem asm_isPosPoly_comp_zeroExt (B : Finset (DSite n k)) {F : DField n k → ℝ}
    (hF : IsPosPoly F) : IsPosPoly (fun ψ : {z // z ∈ B} → ℝ => F (zeroExt B ψ)) := by
  obtain ⟨κ, _, c, b, hc, hF⟩ := hF
  have e : (fun ψ : {z // z ∈ B} → ℝ => F (zeroExt B ψ)) =
      fun ψ => ∑ j, c j * ∏ x, zeroExt B ψ x ^ b j x := by
    funext ψ; rw [hF]; rfl
  rw [e]
  exact IsPosPoly.sum _ fun j _ => (IsPosPoly.const (hc j)).mul
    (asm_isPosPoly_prod _ fun x _ => (asm_isPosPoly_zeroExt_coord B x).pow _)

/-- The extension of a sign pattern on B to the whole box (no flip off B). -/
def asm_extσ (B : Finset (DSite n k)) (σ : {z // z ∈ B} → Bool) : DSite n k → Bool :=
  fun z => if h : z ∈ B then σ ⟨z, h⟩ else false

theorem asm_zeroExt_flip (B : Finset (DSite n k)) (σ : {z // z ∈ B} → Bool)
    (ψ : {z // z ∈ B} → ℝ) :
    zeroExt B (flipSigns σ ψ) = flipSigns (asm_extσ B σ) (zeroExt B ψ) := by
  funext z
  by_cases h : z ∈ B <;> simp [zeroExt, flipSigns, asm_extσ, h, sgnMul]

theorem asm_evenWeight_zeroExt_flip (m₀ lam : ℝ) (B : Finset (DSite n k))
    (σ : {z // z ∈ B} → Bool) (ψ : {z // z ∈ B} → ℝ) :
    evenWeight n k m₀ lam (Polynomial.X ^ 4) (zeroExt B (flipSigns σ ψ)) =
      evenWeight n k m₀ lam (Polynomial.X ^ 4) (zeroExt B ψ) := by
  rw [asm_zeroExt_flip]
  exact evenWeight_flip (fun y => wickPoly_X4_neg _ y) _ _

/-- **Griffiths I for the Dirichlet region measures**, for all m₀, λ (Bochner convention outside
m₀ ≠ 0, λ ≥ 0). -/
theorem regionGriffithsI_holds (m₀ lam : ℝ) : RegionGriffithsI m₀ lam := by
  intro n k B x u
  unfold regionTwoPt
  refine div_nonneg ?_ (integral_nonneg fun _ => (Real.exp_pos _).le)
  have hg : IsPosPoly (fun ψ : {z // z ∈ B} → ℝ => zeroExt B ψ x * zeroExt B ψ u) :=
    (asm_isPosPoly_zeroExt_coord B x).mul (asm_isPosPoly_zeroExt_coord B u)
  have hQ : IsPosPoly (fun ψ : {z // z ∈ B} → ℝ => coupling (zeroExt B ψ)) :=
    asm_isPosPoly_comp_zeroExt B isPosPoly_coupling
  have h := griffiths_first_inv
    (W := fun ψ : {z // z ∈ B} → ℝ => evenWeight n k m₀ lam (Polynomial.X ^ 4) (zeroExt B ψ))
    (asm_evenWeight_zeroExt_flip m₀ lam B) (fun _ => (Real.exp_pos _).le) hg hQ
  have e : ∀ ψ : {z // z ∈ B} → ℝ,
      zeroExt B ψ x * zeroExt B ψ u * qweight n k m₀ lam (zeroExt B ψ) =
        zeroExt B ψ x * zeroExt B ψ u * Real.exp (coupling (zeroExt B ψ)) *
          evenWeight n k m₀ lam (Polynomial.X ^ 4) (zeroExt B ψ) := by
    intro ψ; rw [qweight, dweight_eq]; ring
  simp_rw [e]
  exact h

/-! ## End-to-end chain down to the two M5 inputs -/

/-- **Finite-cutoff clustering from the M5 inputs** (Simon–Lieb, Newman and Griffiths I for
regions discharged). -/
theorem clustering_of_M5 {m₀ lam l γ A : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (hl : 0 ≤ l)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hSus : RegionSusceptibility m₀ lam l A) :
    ∃ m, 0 < m ∧ FiniteCutoffClustering m₀ lam m :=
  PP2Newman.clustering_of_simonLieb_newman hm hlam hl hγ0 hγ1 hA (simonLiebIneq'_holds hm hlam)
    (regionGriffithsI_holds m₀ lam) hSmall hSus

/-- **Existence of a limit point from the M5 inputs** and Schwartz separability. -/
theorem limitPoint_of_M5 {m₀ lam l γ A : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (hl : 0 ≤ l)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hSus : RegionSusceptibility m₀ lam l A)
    (hS : SchwartzSeparable) : ∃ Z, IsLimitPoint m₀ lam Z :=
  exists_limitPoint_of_simonLieb' hm hlam hl hγ0 hγ1 hA (simonLiebIneq'_holds hm hlam)
    (regionGriffithsI_holds m₀ lam) hSmall hSus hS

/-- The two node-M5 inputs at (m₀, λ), with some radius l, contraction γ < 1 and bound A. -/
def M5Inputs (m₀ lam : ℝ) : Prop :=
  ∃ l γ A : ℝ, 0 ≤ l ∧ 0 < γ ∧ γ < 1 ∧ 0 ≤ A ∧
    SmallBoundarySum m₀ lam l γ ∧ RegionSusceptibility m₀ lam l A

theorem clustering_of_M5Inputs {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (h : M5Inputs m₀ lam) : ∃ m, 0 < m ∧ FiniteCutoffClustering m₀ lam m := by
  obtain ⟨l, γ, A, hl, hγ0, hγ1, hA, hSmall, hSus⟩ := h
  exact clustering_of_M5 hm hlam hl hγ0 hγ1 hA hSmall hSus

theorem limitPoint_of_M5Inputs {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (h : M5Inputs m₀ lam) (hS : SchwartzSeparable) : ∃ Z, IsLimitPoint m₀ lam Z := by
  obtain ⟨l, γ, A, hl, hγ0, hγ1, hA, hSmall, hSus⟩ := h
  exact limitPoint_of_M5 hm hlam hl hγ0 hγ1 hA hSmall hSus hS

/-- **The V3 target, conditional on the M5 inputs, non-Gaussianity and Schwartz separability.** -/
theorem phiFourTwoGapV3_of_M5
    (hM5 : ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        M5Inputs m₀ lam ∧ ∀ Z, IsLimitPoint m₀ lam Z → IsNonGaussian Z)
    (hS : SchwartzSeparable) : PhiFourTwoGapV3 := by
  intro m₀ hm₀
  obtain ⟨lam₀, hlam₀, h⟩ := hM5 m₀ hm₀
  refine ⟨lam₀, hlam₀, fun lam hlam hlam' => ?_⟩
  obtain ⟨hIn, hNG⟩ := h lam hlam hlam'
  obtain ⟨m, hm, hC⟩ := clustering_of_M5Inputs hm₀.ne' hlam.le hIn
  exact ⟨m, hm, hC, limitPoint_of_M5Inputs hm₀.ne' hlam.le hIn hS, hNG⟩

end PP2Target

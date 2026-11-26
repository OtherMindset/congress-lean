import LongTable.R_PP2FreeVar2A

/-!
Part B of PP2FreeVar2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2FreeVar2.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `fv2_subBox M x` (sites at lattice sup-distance ≤ M from x), `fv2_subBox_var_le`:
  ε⁻² G_sub(x, x) ≤ ε⁻² dirGreen x x.
* `fv2_two_mul_sub_quad_le`: 2 v(a) − ⟨v, dirOp v⟩ ≤ dirGreen a a for every v (m₀ ≠ 0).
* Sub-box sine modes: `fv2_sv` (1-D mode of [c − M, c + M], zero outside), `fv2_sv_three`
  (three-point identity inside, using vanishing at c − M − 1 and c + M + 1), `fv2_Fits M x`
  (sub-box inside the box), `fv2_E` (2-D mode, zero-extended), `fv2_ext_E`, `fv2_dirOp_E`
  (dirOp e_K = λ_K e_K on the sub-box, λ_K = `fv2_lam` = ε⁻²(sineEig K₁ + sineEig K₂) + m₀²),
  `fv2_E_out`, `fv2_sv_sum`, `fv2_E_orthonormal` (Σ_y e_K e_L = δ_KL), `fv2_E_centre`.
* `fv2_specVar_le_dirVar`: Fits M x → specVar (2M+1) (m₀²ε²) M M ≤ ε⁻² dirGreen x x
  (trial field v = Σ_K e_K(x) λ_K⁻¹ e_K; this replaces "domain monotonicity + identification of
  the sub-box Green's function with specVar" for the diagonal lower bound).
* `fv2_wick_defect_le_of_fits`: Fits M x → b(x) ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))).
* `fv2_bdist x` = min(x₁, N−1−x₁, x₂, N−1−x₂), `fv2_rdist n k x` = ε(fv2_bdist x + 1) (the
  sup-distance from x to the nearest zero (Dirichlet) site, lattice coordinate −1 or N),
  `fv2_fits_bdist`, and **`fv2_wick_defect_le`**: m₀ ≠ 0 → for every site x,
  freeVar − ε⁻² dirGreen x x ≤ (π/4)(1 + log⁺(1/(|m₀| r(x)))). With `dirVar_le_freeVar`,
  0 ≤ b(x) ≤ (π/4)(1 + log⁺(1/(|m₀| r(x)))), uniformly in n, k.

NOT formalized here: the equality ε⁻² regionGreen (subBox) (x, x) = specVar (2M+1) (only the
lower bound of dirGreen is proved, variationally, which is what the site bound needs); the
identification of `fv2_rdist` with a distance computed from `dpos` (it is defined in lattice
terms); any use of b(x) downstream (e.g. summing b over the box); sharper
constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset

noncomputable section

namespace PP2Target

variable {n k : ℕ}

theorem fv2_mem_subBox_self (M : ℕ) (x : DSite n k) : x ∈ fv2_subBox M x := by
  simp [fv2_subBox]

/-- **Domain monotonicity at the centre of a sub-box**: ε⁻² G_sub(x, x) ≤ ε⁻² dirGreen(x, x). -/
theorem fv2_subBox_var_le {m₀ : ℝ} (hm : m₀ ≠ 0) (M : ℕ) (x : DSite n k) :
    (spacing n ^ 2)⁻¹ * regionGreen n k m₀ (fv2_subBox M x) ⟨x, fv2_mem_subBox_self M x⟩
        ⟨x, fv2_mem_subBox_self M x⟩ ≤ (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x :=
  mul_le_mul_of_nonneg_left (fv2_regionGreen_le_dirGreen hm _ _ _) (by positivity)

/-! ## Goal 3: the centre of an odd sub-box, variationally -/

/-- **Variational lower bound**: 2 v(a) − ⟨v, dirOp v⟩ ≤ dirGreen a a (m₀ ≠ 0). -/
theorem fv2_two_mul_sub_quad_le {m₀ : ℝ} (hm : m₀ ≠ 0) (v : DField n k) (a : DSite n k) :
    2 * v a - v ⬝ᵥ dirOp n k m₀ *ᵥ v ≤ dirGreen n k m₀ a a := by
  set g : DField n k := dirGreen n k m₀ *ᵥ Pi.single a 1 with hg
  have hAg : dirOp n k m₀ *ᵥ g = Pi.single a 1 := by
    rw [hg, mulVec_mulVec, dirOp_mul_dirGreen hm, one_mulVec]
  have hga : g a = dirGreen n k m₀ a a := by simp [hg, mulVec_single_one]
  have hsym : g ⬝ᵥ dirOp n k m₀ *ᵥ v = v ⬝ᵥ dirOp n k m₀ *ᵥ g := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dirOp_transpose, dotProduct_comm]
  have hva : v ⬝ᵥ (Pi.single a 1 : DField n k) = v a := by
    simp [dotProduct, Pi.single_apply]
  have hgg : g ⬝ᵥ (Pi.single a 1 : DField n k) = g a := by
    simp [dotProduct, Pi.single_apply]
  have h0 : 0 ≤ (v - g) ⬝ᵥ dirOp n k m₀ *ᵥ (v - g) := by
    have := dirOp_quad_ge m₀ (v - g)
    have : 0 ≤ m₀ ^ 2 * ∑ x : DSite n k, (v - g) x ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hsym, hAg, hva, hgg, hga] at h0
  linarith

/-- The 1-D sine mode j of the odd interval [c − M, c + M] ⊂ ℤ (side 2M + 1), zero outside:
e_j(q − c + M) for q in the interval. -/
def fv2_sv (M : ℕ) (c : ℤ) (j : ℕ) (q : ℤ) : ℝ :=
  if c - M ≤ q ∧ q ≤ c + M then sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1) else 0

theorem fv2_sv_three (M : ℕ) (c : ℤ) (j : ℕ) {q : ℤ} (h1 : c - M ≤ q) (h2 : q ≤ c + M) :
    2 * fv2_sv M c j q - fv2_sv M c j (q - 1) - fv2_sv M c j (q + 1) =
      sineEig (2 * M + 1) j * fv2_sv M c j q := by
  have t := sineFn_three_point (2 * M + 1) j ((q : ℝ) - c + M + 1)
  have e0 : fv2_sv M c j q = sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1) := by
    simp only [fv2_sv, if_pos (And.intro h1 h2)]
  have em : fv2_sv M c j (q - 1) = sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1 - 1) := by
    unfold fv2_sv
    split_ifs with h
    · congr 1; push_cast; ring
    · have hq : q = c - M := by omega
      subst hq
      push_cast
      rw [show ((c : ℝ) - M - c + M + 1 - 1) = 0 by ring, sineFn_zero]
  have ep : fv2_sv M c j (q + 1) = sineFn (2 * M + 1) j ((q : ℝ) - c + M + 1 + 1) := by
    unfold fv2_sv
    split_ifs with h
    · congr 1; push_cast; ring
    · have hq : q = c + M := by omega
      subst hq
      have := sineFn_end (2 * M + 1) j
      push_cast at this ⊢
      rw [show ((c : ℝ) + M - c + M + 1 + 1) = 2 * M + 1 + 1 by ring, this]
  rw [e0, em, ep]; exact t

/-- The hypothesis that the odd sub-box of half-width M centred at x lies in the box. -/
def fv2_Fits (M : ℕ) (x : DSite n k) : Prop :=
  M ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) + M < boxN n k ∧ M ≤ (x.2 : ℕ) ∧ (x.2 : ℕ) + M < boxN n k

/-- The 2-D sine mode K of the odd sub-box centred at x, zero-extended to the box. -/
def fv2_E (M : ℕ) (x : DSite n k) (K : Fin (2 * M + 1) × Fin (2 * M + 1)) : DField n k :=
  fun y => fv2_sv M ((x.1 : ℕ) : ℤ) K.1 ((y.1 : ℕ) : ℤ) * fv2_sv M ((x.2 : ℕ) : ℤ) K.2 ((y.2 : ℕ) : ℤ)

theorem fv2_ext_E {M : ℕ} {x : DSite n k} (hfit : fv2_Fits M x)
    (K : Fin (2 * M + 1) × Fin (2 * M + 1)) (q : ℤ × ℤ) :
    ext (fv2_E M x K) q =
      fv2_sv M ((x.1 : ℕ) : ℤ) K.1 q.1 * fv2_sv M ((x.2 : ℕ) : ℤ) K.2 q.2 := by
  obtain ⟨f1, f2, f3, f4⟩ := hfit
  unfold ext
  split_ifs with h
  · simp only [fv2_E]
    rw [Int.toNat_of_nonneg h.1, Int.toNat_of_nonneg h.2.2.1]
  · have : ¬ (((x.1 : ℕ) : ℤ) - M ≤ q.1 ∧ q.1 ≤ ((x.1 : ℕ) : ℤ) + M) ∨
        ¬ (((x.2 : ℕ) : ℤ) - M ≤ q.2 ∧ q.2 ≤ ((x.2 : ℕ) : ℤ) + M) := by omega
    rcases this with h' | h'
    · simp only [fv2_sv]; rw [if_neg h', zero_mul]
    · simp only [fv2_sv]; rw [if_neg h', mul_zero]

/-- The sub-box eigenvalue ε⁻²(sineEig K₁ + sineEig K₂) + m₀² (> 0). -/
def fv2_lam (n : ℕ) (m₀ : ℝ) (M : ℕ) (K : Fin (2 * M + 1) × Fin (2 * M + 1)) : ℝ :=
  (spacing n ^ 2)⁻¹ * (sineEig (2 * M + 1) K.1 + sineEig (2 * M + 1) K.2) + m₀ ^ 2

theorem fv2_lam_pos (n : ℕ) (m₀ : ℝ) (M : ℕ) (K : Fin (2 * M + 1) × Fin (2 * M + 1)) :
    0 < fv2_lam n m₀ M K := by
  have h1 := sineEig_pos (2 * M + 1) K.1 K.1.isLt
  have h2 := sineEig_pos (2 * M + 1) K.2 K.2.isLt
  have hs := spacing_pos n
  exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) (add_pos h1 h2)) (sq_nonneg _)

/-- **Eigen-equation inside the sub-box**: (dirOp e_K)(y) = λ_K e_K(y) for y in the sub-box. -/
theorem fv2_dirOp_E (m₀ : ℝ) {M : ℕ} {x : DSite n k} (hfit : fv2_Fits M x)
    (K : Fin (2 * M + 1) × Fin (2 * M + 1)) (y : DSite n k) (hy : y ∈ fv2_subBox M x) :
    (dirOp n k m₀ *ᵥ fv2_E M x K) y = fv2_lam n m₀ M K * fv2_E M x K y := by
  simp only [fv2_subBox, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have t1 := fv2_sv_three M ((x.1 : ℕ) : ℤ) K.1 (q := ((y.1 : ℕ) : ℤ)) (by omega) (by omega)
  have t2 := fv2_sv_three M ((x.2 : ℕ) : ℤ) K.2 (q := ((y.2 : ℕ) : ℤ)) (by omega) (by omega)
  rw [dirOp_mulVec_apply, fv2_ext_E hfit, fv2_ext_E hfit, fv2_ext_E hfit, fv2_ext_E hfit]
  simp only [site, fv2_E, fv2_lam]
  linear_combination ((spacing n ^ 2)⁻¹ * fv2_sv M ((x.2 : ℕ) : ℤ) K.2 ((y.2 : ℕ) : ℤ)) * t1 +
    ((spacing n ^ 2)⁻¹ * fv2_sv M ((x.1 : ℕ) : ℤ) K.1 ((y.1 : ℕ) : ℤ)) * t2

theorem fv2_E_out {M : ℕ} {x : DSite n k} (K : Fin (2 * M + 1) × Fin (2 * M + 1))
    {y : DSite n k} (hy : y ∉ fv2_subBox M x) : fv2_E M x K y = 0 := by
  simp only [fv2_subBox, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  have : ¬ (((x.1 : ℕ) : ℤ) - M ≤ ((y.1 : ℕ) : ℤ) ∧ ((y.1 : ℕ) : ℤ) ≤ ((x.1 : ℕ) : ℤ) + M) ∨
      ¬ (((x.2 : ℕ) : ℤ) - M ≤ ((y.2 : ℕ) : ℤ) ∧ ((y.2 : ℕ) : ℤ) ≤ ((x.2 : ℕ) : ℤ) + M) := by
    omega
  rcases this with h' | h'
  · simp only [fv2_E, fv2_sv]; rw [if_neg h', zero_mul]
  · simp only [fv2_E, fv2_sv]; rw [if_neg h', mul_zero]

/-- 1-D reindexing: the sub-interval sum of the modes is the side-(2M+1) sine-basis sum. -/
theorem fv2_sv_sum {N M c : ℕ} (h1 : M ≤ c) (h2 : c + M < N) (j l : ℕ) :
    ∑ a : Fin N, fv2_sv M (c : ℤ) j ((a : ℕ) : ℤ) * fv2_sv M (c : ℤ) l ((a : ℕ) : ℤ) =
      ∑ i : Fin (2 * M + 1), sineVec (2 * M + 1) j i * sineVec (2 * M + 1) l i := by
  set F : ℕ → ℝ := fun a => fv2_sv M (c : ℤ) j (a : ℤ) * fv2_sv M (c : ℤ) l (a : ℤ) with hF
  rw [Fin.sum_univ_eq_sum_range F N]
  have hsub : Finset.Ico (c - M) (c + M + 1) ⊆ Finset.range N := by
    intro a ha; simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢; omega
  rw [← Finset.sum_subset hsub (fun a _ ha => by
    simp only [Finset.mem_Ico] at ha
    have : ¬ ((c : ℤ) - M ≤ (a : ℤ) ∧ (a : ℤ) ≤ (c : ℤ) + M) := by omega
    simp only [hF, fv2_sv]; rw [if_neg this, zero_mul])]
  rw [Finset.sum_Ico_eq_sum_range, show c + M + 1 - (c - M) = 2 * M + 1 by omega]
  simp only [sineVec]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => sineFn (2 * M + 1) j ((i : ℝ) + 1) *
    sineFn (2 * M + 1) l ((i : ℝ) + 1)) (2 * M + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hc : (((c - M + i : ℕ) : ℤ) : ℝ) - (c : ℤ) + M + 1 = (i : ℝ) + 1 := by
    push_cast [Nat.cast_sub h1]; ring
  have hin : ((c : ℤ) - M ≤ ((c - M + i : ℕ) : ℤ) ∧ ((c - M + i : ℕ) : ℤ) ≤ (c : ℤ) + M) := by
    omega
  simp only [hF, fv2_sv]
  rw [if_pos hin, if_pos hin, hc]

/-- **Orthonormality of the sub-box modes** on the box: Σ_y e_K(y) e_L(y) = δ_KL. -/
theorem fv2_E_orthonormal {M : ℕ} {x : DSite n k} (hfit : fv2_Fits M x)
    (K L : Fin (2 * M + 1) × Fin (2 * M + 1)) :
    ∑ y : DSite n k, fv2_E M x K y * fv2_E M x L y = if K = L then 1 else 0 := by
  obtain ⟨f1, f2, f3, f4⟩ := hfit
  have hpt : ∀ y : DSite n k, fv2_E M x K y * fv2_E M x L y =
      (fv2_sv M ((x.1 : ℕ) : ℤ) K.1 ((y.1 : ℕ) : ℤ) * fv2_sv M ((x.1 : ℕ) : ℤ) L.1 ((y.1 : ℕ) : ℤ)) *
        (fv2_sv M ((x.2 : ℕ) : ℤ) K.2 ((y.2 : ℕ) : ℤ) *
          fv2_sv M ((x.2 : ℕ) : ℤ) L.2 ((y.2 : ℕ) : ℤ)) := by
    intro y; simp only [fv2_E]; ring
  rw [Finset.sum_congr rfl fun y _ => hpt y, Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum, fv2_sv_sum f1 f2, fv2_sv_sum f3 f4,
    sineVec_orthonormal _ _ _ K.1.isLt L.1.isLt, sineVec_orthonormal _ _ _ K.2.isLt L.2.isLt]
  by_cases h1 : (K.1 : ℕ) = L.1 <;> by_cases h2 : (K.2 : ℕ) = L.2 <;>
    simp [h1, h2, Prod.ext_iff, Fin.ext_iff]

theorem fv2_E_centre {M : ℕ} (x : DSite n k) (K : Fin (2 * M + 1) × Fin (2 * M + 1))
    (hM : M < 2 * M + 1) :
    fv2_E M x K x = sineVec (2 * M + 1) K.1 ⟨M, hM⟩ * sineVec (2 * M + 1) K.2 ⟨M, hM⟩ := by
  have hin : ∀ c : ℤ, c - M ≤ c ∧ c ≤ c + M := fun c => ⟨by omega, by omega⟩
  simp only [fv2_E, fv2_sv, sineVec]
  rw [if_pos (hin _), if_pos (hin _)]
  congr 2 <;> ring

/-- **Centre of a fitting odd sub-box ≤ box variance**: if the odd sub-box of half-width M
centred at x lies in the box, then specVar (2M+1) (m₀²ε²) M M ≤ ε⁻² dirGreen x x (m₀ ≠ 0).
(Variational: the trial field Σ_K e_K(x) λ_K⁻¹ e_K, supported in the sub-box.) -/
theorem fv2_specVar_le_dirVar {m₀ : ℝ} (hm : m₀ ≠ 0) {M : ℕ} {x : DSite n k}
    (hfit : fv2_Fits M x) (hM : M < 2 * M + 1) :
    specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ ≤
      (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x := by
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  have hε0 : spacing n ≠ 0 := (spacing_pos n).ne'
  set ι := Fin (2 * M + 1) × Fin (2 * M + 1)
  set lam := fv2_lam n m₀ M with hlam
  set E := fv2_E M x with hE
  set v : DField n k := ∑ K : ι, (E K x / lam K) • E K with hv
  set S := ∑ K : ι, E K x * E K x / lam K with hS
  have hvx : v x = S := by
    simp only [hv, hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun K _ => by ring
  set w : DField n k := ∑ K : ι, E K x • E K with hw
  have hAv : ∀ y, v y * (dirOp n k m₀ *ᵥ v) y = v y * w y := by
    intro y
    by_cases hy : y ∈ fv2_subBox M x
    · congr 1
      simp only [hv, hw, mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [hE, hlam, fv2_dirOp_E m₀ hfit K y hy]
      have := (fv2_lam_pos n m₀ M K).ne'
      field_simp
    · have : v y = 0 := by
        simp only [hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_eq_zero fun K _ => by rw [hE, fv2_E_out K hy, mul_zero]
      rw [this, zero_mul, zero_mul]
  have hquad : v ⬝ᵥ dirOp n k m₀ *ᵥ v = S := by
    have h1 : v ⬝ᵥ dirOp n k m₀ *ᵥ v = v ⬝ᵥ w := by
      simp only [dotProduct]; exact Finset.sum_congr rfl fun y _ => hAv y
    rw [h1, hv, hw, sum_dotProduct]
    simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hS]
    refine Finset.sum_congr rfl fun K _ => ?_
    have horth : ∀ L : ι, E K ⬝ᵥ E L = if K = L then 1 else 0 := fun L => by
      rw [hE]; exact fv2_E_orthonormal hfit K L
    simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hvar := fv2_two_mul_sub_quad_le hm v x
  rw [hvx, hquad] at hvar
  have hSspec : specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ =
      (spacing n ^ 2)⁻¹ * S := by
    rw [specVar, hS, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    rw [hE, fv2_E_centre x (j₁, j₂) hM, hlam, fv2_lam]
    dsimp only
    have h1 := sineEig_pos (2 * M + 1) j₁ j₁.isLt
    have h2 := sineEig_pos (2 * M + 1) j₂ j₂.isLt
    have hd : 0 < m₀ ^ 2 * spacing n ^ 2 + sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂ := by
      positivity
    have hd' : 0 < (spacing n ^ 2)⁻¹ * (sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂)
        + m₀ ^ 2 := by positivity
    field_simp
    ring
  rw [hSspec]
  have : 2 * S - S = S := by ring
  rw [this] at hvar
  exact mul_le_mul_of_nonneg_left hvar (by positivity)

/-- **The site bound for a fitting sub-box.** If the odd sub-box of half-width M centred at x lies
in the box (m₀ ≠ 0): b(x) = freeVar − ε⁻² dirGreen x x ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))). -/
theorem fv2_wick_defect_le_of_fits {m₀ : ℝ} (hm : m₀ ≠ 0) {M : ℕ} {x : DSite n k}
    (hfit : fv2_Fits M x) :
    freeVar n m₀ - (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((M : ℝ) + 1))))) := by
  have hM : M < 2 * M + 1 := by omega
  have h1 := fv2_specVar_le_dirVar hm hfit hM
  have h2 := fv2_freeVar_sub_centre_le (n := n) hm M hM
  rw [← mul_assoc]
  linarith

/-- The lattice distance M(x) = min(x₁, N−1−x₁, x₂, N−1−x₂) of the site x to the last box sites;
the zero (Dirichlet) sites are at lattice distance M(x) + 1. -/
def fv2_bdist (x : DSite n k) : ℕ :=
  min (min (x.1 : ℕ) (boxN n k - 1 - x.1)) (min (x.2 : ℕ) (boxN n k - 1 - x.2))

/-- The physical distance r(x) = ε (M(x) + 1) from x to the Dirichlet boundary (the nearest
zero site, in the sup norm). -/
def fv2_rdist (n k : ℕ) (x : DSite n k) : ℝ := spacing n * ((fv2_bdist x : ℝ) + 1)

theorem fv2_fits_bdist (x : DSite n k) : fv2_Fits (fv2_bdist x) x := by
  have h1 := x.1.isLt
  have h2 := x.2.isLt
  unfold fv2_Fits fv2_bdist
  omega

/-- **Goal 3: the Wick defect at a site.** For m₀ ≠ 0 and every site x of the box,
b(x) = freeVar − ε⁻² dirGreen x x ≤ (π/4)(1 + log⁺(1/(|m₀| r(x)))), r(x) = ε (M(x) + 1) the
physical distance to the Dirichlet boundary. (With `dirVar_le_freeVar`, 0 ≤ b(x).) -/
theorem fv2_wick_defect_le {m₀ : ℝ} (hm : m₀ ≠ 0) (x : DSite n k) :
    freeVar n m₀ - (spacing n ^ 2)⁻¹ * dirGreen n k m₀ x x ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * fv2_rdist n k x))) :=
  fv2_wick_defect_le_of_fits hm (fv2_fits_bdist x)

end PP2Target

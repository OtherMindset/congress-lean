import LongTable.R_PP2NelsonC

/-!
Part A of PP2RoughL2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2RoughL2.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node G4 of the M5
plan (Nelson's bound), session 2, BOX version: step 3, the rough L² bound (namespace `PP2RoughL2`).

Target: `PP2Nelson.nl_RoughL2Hyp m₀ k` (m₀ ≠ 0): ∃ K θ, 0 < θ ∧ ∀ n, ∀ T ∈ (0, 1],
E_{γ⊗γ}[R_T²] ≤ K T^θ, the single remaining hypothesis of `nl_nelsonBox_of_roughL2`.

Notation as in PP2Nelson: (ξˢ, ξʳ) ~ γ^Λ ⊗ γ^Λ (`nl_P`), φ_s(y) = Σ_K ℓˢ_{yK} ξˢ_K,
φ_r(y) = Σ_K ℓʳ_{yK} ξʳ_K (`nl_ls`, `nl_lr`), c₁ = `nl_cs`, c_r = `nl_cr`, C_r = `glp_roughCov`,
S_j(y) = :φ_s(y)^j:_{c₁(y)} (`rl_S`), B_j(y) = :φ_r(y)^j:_{c_r(y)} (`rl_B`), ε = `spacing n`,
L = `boxL k`, r(y)^{−1/2} = `nl_f n (fv2_bdist y)`.

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* §1, Wick covariance of linear forms of a standard Gaussian vector, NO law identification:
  `rl_cov`: for any finite ι, u v : ι → ℝ, a b ≤ 4, under γ^ι = Measure.pi gaussianReal 0 1,
  E[:⟨u,ξ⟩^a:_{|u|²} :⟨v,ξ⟩^b:_{|v|²}] = δ_ab a! ⟨u,v⟩^a. Proof (`rl_cov_fin`): induction on d for
  ℝ^{Fin d} via `measurePreserving_piFinSuccAbove` (γ^{d+1} ≅ γ ⊗ γ^d), splitting
  ⟨u,x⟩ = ⟨u',x'⟩ + u₀x₀ and |u|² = |u'|² + u₀² with `wickPow_add_binomial`, `wickPow_scale`,
  `integral_prod_mul`, 1-D orthogonality `wickPow_orthogonal`, and add_pow for the binomial sum;
  then `measurePreserving_piCongrLeft` with `Fintype.equivFin`. `rl_int`: integrability of
  :⟨u,ξ⟩^a:_c :⟨v,ξ⟩^b:_{c'} for all real c, c', a, b (same induction).
* §2, `rl_sq_comb`, `rl_smooth_sq`: if |u|² ≤ c and j ≤ 3, E[(:⟨u,ξ⟩^j:_c)²] ≤ 15 (1 + c)³
  (re-ordering :X^j:_c = :X^j:_s − binomial terms in δ = c − s ≥ 0, then `rl_cov`);
  `rl_abs_int_mul_le`: |E fg| ≤ (E f² + E g²)/2.
* §3, box covariances: `rl_φs_eq`, `rl_φr_eq` (φ_s, φ_r as linear forms); `rl_lr_cov`
  (Σ_K ℓʳ_{yK} ℓʳ_{y'K} = C_r(T)(y, y'), via `glp_roughCov_spectral`); `rl_cr_eq` (c_r(y) = Var φ_r(y));
  `rl_ls_var` (Var φ_s(y) = ε⁻² dirGreen y y − c_r(y), via `dirGreen_spectral`); `rl_ls_var_le`
  (Var φ_s(y) ≤ c₁(y), the gap being the Wick defect ≥ 0 by `dirVar_le_freeVar`); `rl_roughCov_symm`.
* §4, (a)+(b)+(c): `rl_cov_B` (**the rough Wick covariance at the true rough variances**,
  E[B_a(y) B_b(y')] = δ_ab a! C_r(y,y')^a, a, b ≤ 4, T ≥ 0); `rl_Rω_sq`, `rl_ER2` (exact formula
  E[R_T²] = ε⁴ Σ_{y,y'} Σ_{j<4} C(4,j)² E[S_j(y)S_j(y')] (4−j)! C_r(y,y')^{4−j}, by factorisation
  over the product measure and rough orthogonality); `rl_E_le` (|E[S_j(y)S_j(y')]| ≤ (M(y)+M(y'))/2,
  M = 15(1+c₁)³ = `rl_M`); `rl_ER2_le` (E[R_T²] ≤ 96 ε⁴ Σ_{y,y'} (M(y)+M(y'))/2 · G(y,y'),
  G = Σ_{m=1}^4 |C_r|^m = `rl_G`).
* §5, (d) summation, with s = T^{1/8} (T = s⁸): `rl_symm_sum` (symmetrisation);
  `rl_G_sum_le` (ε² Σ_{y'} G(y,y') ≤ K_G s⁴, from `glp_roughCov_Lp_le` for m = 2, 3, 4 and
  |C| ≤ s⁴/2 + |C|²/(2s⁴) for m = 1; K_G = `rl_KG k`); `rl_posLog_cube_le` ((log⁺x)³ ≤ 512(1+√x));
  `rl_neglog_le` (s⁴ (−log s⁸)³ ≤ 512 s); `rl_site_le` (s⁴(1+c₁(y))³ ≤ s (Q₀ + Q₁ r(y)^{−1/2}), from
  `nl_cs_bounds`); `rl_sum_site_le` (with `nl_sum_f_bdist`: ε² Σ_y s⁴(1+c₁)³ ≤ s (Q₀L² + 8Q₁L^{3/2})).
* §6, **`rl_roughL2Hyp`**: m₀ ≠ 0 → `nl_RoughL2Hyp m₀ k`, with θ = 1/8 and
  K = 96·15·K_G (Q₀ L² + 8 Q₁ L^{3/2}) (`rl_Q0`, `rl_Q1`, explicit in m₀ and L), uniform in n.
  **`rl_nelsonBox`**: m₀ ≠ 0 → `nl_NelsonBox m₀ k` (Nelson's bound for the box, G4 box version,
  now unconditional: `nl_nelsonBox_of_roughL2` + `rl_roughL2Hyp`).

NOT formalized (what remains): the region (physBall) version of G4 (same argument once the region
G1 / heat split / Lᵖ bounds are in place; `mg_region_*` exist in PP2ModesGen); Wick orthogonality
for degrees > 4 (not needed); optimal exponent (θ = 1/8 here, from the m = 1 term handled by
AM-GM; an L¹ bound ε² Σ_{y'} |C_r(y,y')| ≤ K T, e.g. from heat-kernel positivity, would give any
θ < 1); optimal constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

set_option maxHeartbeats 400000

noncomputable section

namespace PP2RoughL2

open PP2Target PP2Nelson

/-! ## 1. Wick covariance of two linear forms of a standard Gaussian vector -/

/-- γ^d, the standard Gaussian on ℝ^{Fin d}. -/
abbrev rl_γ (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

/-- The linear form ⟨u, x⟩ = Σ_i u_i x_i. -/
def rl_L {ι : Type*} [Fintype ι] (u x : ι → ℝ) : ℝ := ∑ i, u i * x i

theorem rl_wickPow_zero (j : ℕ) (y : ℝ) : wickPow 0 j y = y ^ j := by
  unfold wickPow
  rw [Finset.sum_range_succ']
  simp [Nat.factorial_ne_zero]

theorem rl_γ_succ_mp (d : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0)
      (rl_γ (d + 1)) ((gaussianReal 0 1).prod (rl_γ d)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => gaussianReal 0 1) 0

theorem rl_L_symm (d : ℕ) (u : Fin (d + 1) → ℝ) (p : ℝ × (Fin d → ℝ)) :
    rl_L u ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p) =
      rl_L (fun j => u j.succ) p.2 + u 0 * p.1 := by
  simp only [rl_L, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove,
    cast_eq, Fin.cons_zero]
  ring

theorem rl_int1 (u0 v0 : ℝ) (p q : ℕ) :
    Integrable (fun t : ℝ => (u0 * t) ^ p * (v0 * t) ^ q) (gaussianReal 0 1) :=
  ((integrable_pow_gaussianReal 1 (p + q)).const_mul (u0 ^ p * v0 ^ q)).congr
    (ae_of_all _ fun t => by simp only; ring)

/-- Integrability of products of Wick powers of linear forms (any Wick constants), on ℝ^{Fin d}. -/
theorem rl_int_fin : ∀ (d : ℕ) (u v : Fin d → ℝ) (c c' : ℝ) (a b : ℕ),
    Integrable (fun x => wickPow c a (rl_L u x) * wickPow c' b (rl_L v x)) (rl_γ d) := by
  intro d
  induction d with
  | zero =>
    intro u v c c' a b
    have : (fun x : Fin 0 → ℝ => wickPow c a (rl_L u x) * wickPow c' b (rl_L v x)) =
        fun _ => wickPow c a 0 * wickPow c' b 0 := by
      funext x; simp [rl_L]
    rw [this]; exact integrable_const _
  | succ d ih =>
    intro u v c c' a b
    have hmp := rl_γ_succ_mp d
    rw [← hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have key : ∀ p : ℝ × (Fin d → ℝ),
        ∑ i ∈ range (a + 1), ∑ i' ∈ range (b + 1), ((a.choose i : ℝ) * (b.choose i' : ℝ)) *
          ((fun t : ℝ => (u 0 * t) ^ (a - i) * (v 0 * t) ^ (b - i')) p.1 *
            (fun y => wickPow c i (rl_L (fun j => u j.succ) y) *
              wickPow c' i' (rl_L (fun j => v j.succ) y)) p.2) =
        ((fun x => wickPow c a (rl_L u x) * wickPow c' b (rl_L v x)) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm) p := by
      intro p
      simp only [Function.comp_apply, rl_L_symm]
      have h1 := wickPow_add_binomial c 0 (rl_L (fun j => u j.succ) p.2) (u 0 * p.1) a
      have h2 := wickPow_add_binomial c' 0 (rl_L (fun j => v j.succ) p.2) (v 0 * p.1) b
      rw [add_zero] at h1 h2
      rw [h1, h2, sum_mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => ?_
      rw [rl_wickPow_zero, rl_wickPow_zero]
      ring
    refine (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ =>
      ((rl_int1 (u 0) (v 0) (a - i) (b - i')).mul_prod
        (ih _ _ c c' i i')).const_mul _).congr (ae_of_all _ fun p => key p)

theorem rl_orth1 (j k : ℕ) (hj : j ≤ 4) (hk : k ≤ 4) :
    ∫ t, wickPow 1 j t * wickPow 1 k t ∂gaussianReal 0 1 =
      if j = k then (j.factorial : ℝ) else 0 := by
  have h := wickPow_orthogonal 1 j k hj hk
  simp only [NNReal.coe_one, one_pow, mul_one] at h
  exact h

/-- **Wick covariance of two linear forms, on ℝ^{Fin d}** (degrees ≤ 4):
E[:⟨u,x⟩^a:_{|u|²} :⟨v,x⟩^b:_{|v|²}] = δ_ab a! ⟨u,v⟩^a. -/
theorem rl_cov_fin : ∀ (d : ℕ) (u v : Fin d → ℝ) (a b : ℕ), a ≤ 4 → b ≤ 4 →
    ∫ x, wickPow (∑ i, u i ^ 2) a (rl_L u x) * wickPow (∑ i, v i ^ 2) b (rl_L v x) ∂rl_γ d =
      if a = b then (a.factorial : ℝ) * (∑ i, u i * v i) ^ a else 0 := by
  intro d
  induction d with
  | zero =>
    intro u v a b _ _
    simp only [rl_L, Finset.univ_eq_empty, Finset.sum_empty, rl_wickPow_zero, integral_const,
      probReal_univ, smul_eq_mul, one_mul]
    cases a <;> cases b <;> simp
  | succ d ih =>
    intro u v a b ha hb
    have hmp := rl_γ_succ_mp d
    rw [← hmp.symm.integral_comp']
    have hQu : ∑ i, u i ^ 2 = (∑ i, (fun j : Fin d => u j.succ) i ^ 2) + u 0 ^ 2 * 1 := by
      rw [Fin.sum_univ_succ]; ring
    have hQv : ∑ i, v i ^ 2 = (∑ i, (fun j : Fin d => v j.succ) i ^ 2) + v 0 ^ 2 * 1 := by
      rw [Fin.sum_univ_succ]; ring
    have huv : ∑ i, u i * v i =
        (∑ i, (fun j : Fin d => u j.succ) i * (fun j : Fin d => v j.succ) i) + u 0 * v 0 := by
      rw [Fin.sum_univ_succ]; ring
    set u' : Fin d → ℝ := fun j => u j.succ with hu'
    set v' : Fin d → ℝ := fun j => v j.succ with hv'
    have key : ∀ p : ℝ × (Fin d → ℝ),
        wickPow (∑ i, u i ^ 2) a
            (rl_L u ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p)) *
          wickPow (∑ i, v i ^ 2) b
            (rl_L v ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p)) =
        ∑ i ∈ range (a + 1), ∑ i' ∈ range (b + 1),
          ((a.choose i : ℝ) * (b.choose i' : ℝ) * (u 0 ^ (a - i) * v 0 ^ (b - i'))) *
          (wickPow 1 (a - i) p.1 * wickPow 1 (b - i') p.1 *
            (wickPow (∑ j, u' j ^ 2) i (rl_L u' p.2) *
              wickPow (∑ j, v' j ^ 2) i' (rl_L v' p.2))) := by
      intro p
      rw [rl_L_symm, rl_L_symm, hQu, hQv, wickPow_add_binomial, wickPow_add_binomial, sum_mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => ?_
      rw [wickPow_scale, wickPow_scale]
      ring
    simp_rw [key]
    have hint : ∀ i i' : ℕ, Integrable (fun p : ℝ × (Fin d → ℝ) =>
        wickPow 1 (a - i) p.1 * wickPow 1 (b - i') p.1 *
          (wickPow (∑ j, u' j ^ 2) i (rl_L u' p.2) * wickPow (∑ j, v' j ^ 2) i' (rl_L v' p.2)))
        ((gaussianReal 0 1).prod (rl_γ d)) := fun i i' =>
      (integrable_wickPow_mul 1 1 1 (a - i) (b - i')).mul_prod
        (rl_int_fin d u' v' _ _ i i')
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun i' _ =>
      (hint i i').const_mul _)]
    have hterm : ∀ i ∈ range (a + 1),
        ∫ p, ∑ i' ∈ range (b + 1),
          ((a.choose i : ℝ) * (b.choose i' : ℝ) * (u 0 ^ (a - i) * v 0 ^ (b - i'))) *
          (wickPow 1 (a - i) p.1 * wickPow 1 (b - i') p.1 *
            (wickPow (∑ j, u' j ^ 2) i (rl_L u' p.2) *
              wickPow (∑ j, v' j ^ 2) i' (rl_L v' p.2))) ∂(gaussianReal 0 1).prod (rl_γ d) =
        ∑ i' ∈ range (b + 1),
          ((a.choose i : ℝ) * (b.choose i' : ℝ) * (u 0 ^ (a - i) * v 0 ^ (b - i'))) *
          ((if a - i = b - i' then ((a - i).factorial : ℝ) else 0) *
            (if i = i' then (i.factorial : ℝ) * (∑ j, u' j * v' j) ^ i else 0)) := by
      intro i hi
      have hi4 : i ≤ 4 := by simp at hi; omega
      rw [integral_finsetSum _ (fun i' _ => (hint i i').const_mul _)]
      refine sum_congr rfl fun i' hi' => ?_
      have hi'4 : i' ≤ 4 := by simp at hi'; omega
      have hp := integral_prod_mul (L := ℝ) (μ := gaussianReal 0 1) (ν := rl_γ d)
        (fun t => wickPow 1 (a - i) t * wickPow 1 (b - i') t)
        (fun y => wickPow (∑ j, u' j ^ 2) i (rl_L u' y) * wickPow (∑ j, v' j ^ 2) i' (rl_L v' y))
      rw [integral_const_mul, hp, rl_orth1 _ _ (by omega) (by omega), ih u' v' i i' hi4 hi'4]
    rw [sum_congr rfl hterm, huv]
    split_ifs with hab
    · subst hab
      have hcol : ∀ i ∈ range (a + 1), ∑ i' ∈ range (a + 1),
          ((a.choose i : ℝ) * (a.choose i' : ℝ) * (u 0 ^ (a - i) * v 0 ^ (a - i'))) *
          ((if a - i = a - i' then ((a - i).factorial : ℝ) else 0) *
            (if i = i' then (i.factorial : ℝ) * (∑ j, u' j * v' j) ^ i else 0)) =
          (a.factorial : ℝ) * ((∑ j, u' j * v' j) ^ i * (u 0 * v 0) ^ (a - i) *
            (a.choose i : ℝ)) := by
        intro i hi
        have hia : i ≤ a := by simp at hi; omega
        rw [Finset.sum_eq_single i]
        · simp only [ite_true]
          have hc := Nat.choose_mul_factorial_mul_factorial hia
          have hc' : (a.choose i : ℝ) * (i.factorial : ℝ) * ((a - i).factorial : ℝ) =
              a.factorial := by exact_mod_cast hc
          rw [← hc', mul_pow]
          ring
        · intro i' _ hne
          rw [ite_eq_right (Ne.symm hne)]; ring
        · intro h; exact absurd hi h
      rw [sum_congr rfl hcol, ← mul_sum, add_pow]
    · refine sum_eq_zero fun i hi => sum_eq_zero fun i' hi' => ?_
      have hia : i ≤ a := by simp at hi; omega
      have hib : i' ≤ b := by simp at hi'; omega
      by_cases h : i = i'
      · subst h
        rw [ite_eq_right (by omega)]; ring
      · rw [ite_eq_right h]; ring

/-! ### Transfer to an arbitrary finite index type -/

theorem rl_pi_mp {ι : Type*} [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm)
      (rl_γ (Fintype.card ι)) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
  measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) (Fintype.equivFin ι).symm

theorem rl_sum_congr {ι : Type*} [Fintype ι] (u : ι → ℝ) (x : Fin (Fintype.card ι) → ℝ) :
    ∑ i, u i * (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm x) i =
      rl_L (fun j => u ((Fintype.equivFin ι).symm j)) x := by
  rw [rl_L, ← Equiv.sum_comp (Fintype.equivFin ι).symm]
  refine sum_congr rfl fun j _ => ?_
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

theorem rl_sum_reindex {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∑ i, f i = ∑ j, f ((Fintype.equivFin ι).symm j) :=
  (Equiv.sum_comp (Fintype.equivFin ι).symm f).symm

/-- Integrability of products of Wick powers of linear forms of γ^ι (any Wick constants). -/
theorem rl_int {ι : Type*} [Fintype ι] (u v : ι → ℝ) (c c' : ℝ) (a b : ℕ) :
    Integrable (fun ξ : ι → ℝ => wickPow c a (∑ i, u i * ξ i) * wickPow c' b (∑ i, v i * ξ i))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  rw [← rl_pi_mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have : (fun ξ : ι → ℝ => wickPow c a (∑ i, u i * ξ i) * wickPow c' b (∑ i, v i * ξ i)) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm) =
      fun x => wickPow c a (rl_L (fun j => u ((Fintype.equivFin ι).symm j)) x) *
        wickPow c' b (rl_L (fun j => v ((Fintype.equivFin ι).symm j)) x) := by
    funext x; simp only [Function.comp_apply, rl_sum_congr]
  rw [this]
  exact rl_int_fin _ _ _ _ _ _ _

/-- **Wick covariance of two linear forms of a standard Gaussian vector** (degrees ≤ 4):
for ξ ~ γ^ι, X = ⟨u, ξ⟩, Y = ⟨v, ξ⟩, Wick-ordered at their true variances |u|², |v|²,
E[:X^a: :Y^b:] = δ_ab a! ⟨u, v⟩^a. -/
theorem rl_cov {ι : Type*} [Fintype ι] (u v : ι → ℝ) (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) :
    ∫ ξ, wickPow (∑ i, u i ^ 2) a (∑ i, u i * ξ i) * wickPow (∑ i, v i ^ 2) b (∑ i, v i * ξ i)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      if a = b then (a.factorial : ℝ) * (∑ i, u i * v i) ^ a else 0 := by
  rw [← rl_pi_mp.integral_comp']
  simp_rw [rl_sum_congr]
  rw [rl_sum_reindex (fun i => u i ^ 2), rl_sum_reindex (fun i => v i ^ 2),
    rl_sum_reindex (fun i => u i * v i)]
  exact rl_cov_fin _ _ _ a b ha hb


/-! ## 2. Second moments of mis-ordered Wick powers -/

section Generic

variable {ι : Type*} [Fintype ι]

theorem rl_sq_comb (u : ι → ℝ) {p q : ℕ} (hp : p ≤ 4) (hq : q ≤ 4) (hpq : p ≠ q) (α : ℝ) :
    ∫ ξ, (wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) -
        α * wickPow (∑ i, u i ^ 2) q (∑ i, u i * ξ i)) ^ 2
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) =
      (p.factorial : ℝ) * (∑ i, u i ^ 2) ^ p +
        α ^ 2 * ((q.factorial : ℝ) * (∑ i, u i ^ 2) ^ q) := by
  have hss : ∑ i, u i * u i = ∑ i, u i ^ 2 := by simp [sq]
  have e : ∀ ξ : ι → ℝ, (wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) -
        α * wickPow (∑ i, u i ^ 2) q (∑ i, u i * ξ i)) ^ 2 =
      (wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) * wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) -
        (2 * α) * (wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) *
          wickPow (∑ i, u i ^ 2) q (∑ i, u i * ξ i))) +
        α ^ 2 * (wickPow (∑ i, u i ^ 2) q (∑ i, u i * ξ i) *
          wickPow (∑ i, u i ^ 2) q (∑ i, u i * ξ i)) := fun ξ => by ring
  simp_rw [e]
  have h1 := rl_int u u (∑ i, u i ^ 2) (∑ i, u i ^ 2) p p
  have h2 := rl_int u u (∑ i, u i ^ 2) (∑ i, u i ^ 2) p q
  have h3 := rl_int u u (∑ i, u i ^ 2) (∑ i, u i ^ 2) q q
  have h12 : Integrable (fun ξ : ι → ℝ =>
      wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) * wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) -
        (2 * α) * (wickPow (∑ i, u i ^ 2) p (∑ i, u i * ξ i) *
          wickPow (∑ i, u i ^ 2) q (∑ i, u i * ξ i))) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    h1.sub (h2.const_mul _)
  rw [integral_add h12 (h3.const_mul _), integral_sub h1 (h2.const_mul _),
    integral_const_mul, integral_const_mul, rl_cov u u p p hp hp, rl_cov u u p q hp hq,
    rl_cov u u q q hq hq]
  simp only [ite_true, hpq, ite_false, hss]
  ring

end Generic

end PP2RoughL2

end

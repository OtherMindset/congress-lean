import LongTable.PP2Nelson

/-!
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

/-- **Mis-ordered Wick powers, second moment** (j ≤ 3): if X = ⟨u, ξ⟩ has variance
s = |u|² ≤ c, then E[(:X^j:_c)²] ≤ 15 (1 + c)³ (via :X^j:_c = :X^j:_s − binomial lower terms
with δ = c − s ≥ 0, and `rl_cov`). -/
theorem rl_smooth_sq (u : ι → ℝ) {c : ℝ} (hc : ∑ i, u i ^ 2 ≤ c) {j : ℕ} (hj : j ≤ 3) :
    ∫ ξ, (wickPow c j (∑ i, u i * ξ i)) ^ 2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1) ≤
      15 * (1 + c) ^ 3 := by
  have hs0 : 0 ≤ ∑ i, u i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hss : ∑ i, u i * u i = ∑ i, u i ^ 2 := by simp [sq]
  have hc0 : 0 ≤ c := hs0.trans hc
  have hc3 : 1 + 3 * c + 3 * c ^ 2 + c ^ 3 = (1 + c) ^ 3 := by ring
  have hcc : 0 ≤ c ^ 2 := sq_nonneg c
  have hccc : 0 ≤ c ^ 3 := pow_nonneg hc0 3
  set s := ∑ i, u i ^ 2 with hsdef
  interval_cases j
  · simp only [wickPow_zero', one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith
  · have e : ∀ ξ : ι → ℝ, wickPow c 1 (∑ i, u i * ξ i) ^ 2 =
        wickPow (∑ i, u i ^ 2) 1 (∑ i, u i * ξ i) * wickPow (∑ i, u i ^ 2) 1 (∑ i, u i * ξ i) := by
      intro ξ; simp only [wickPow_one, sq]
    simp_rw [e]
    rw [rl_cov u u 1 1 (by norm_num) (by norm_num)]
    simp only [ite_true, Nat.factorial_one, Nat.cast_one, pow_one, one_mul, hss]
    nlinarith
  · have e : ∀ ξ : ι → ℝ, wickPow c 2 (∑ i, u i * ξ i) ^ 2 =
        (wickPow (∑ i, u i ^ 2) 2 (∑ i, u i * ξ i) -
          (c - s) * wickPow (∑ i, u i ^ 2) 0 (∑ i, u i * ξ i)) ^ 2 := by
      intro ξ; simp only [wickPow_two, wickPow_zero']; ring
    simp_rw [e]
    rw [rl_sq_comb u (by norm_num) (by norm_num) (by norm_num)]
    simp only [Nat.factorial, Nat.cast_one, pow_zero, mul_one, Nat.succ_eq_add_one, zero_add]
    have h1 : s ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hs0 hc 2
    have h2 : (c - s) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    norm_num
    nlinarith
  · have e : ∀ ξ : ι → ℝ, wickPow c 3 (∑ i, u i * ξ i) ^ 2 =
        (wickPow (∑ i, u i ^ 2) 3 (∑ i, u i * ξ i) -
          (3 * (c - s)) * wickPow (∑ i, u i ^ 2) 1 (∑ i, u i * ξ i)) ^ 2 := by
      intro ξ; simp only [wickPow_three, wickPow_one]; ring
    simp_rw [e]
    rw [rl_sq_comb u (by norm_num) (by norm_num) (by norm_num)]
    have h1 : s ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hs0 hc 3
    have h2 : (c - s) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h3 : (c - s) ^ 2 * s ≤ c ^ 2 * c := mul_le_mul h2 hc hs0 hcc
    norm_num [Nat.factorial]
    nlinarith

end Generic

/-- |E[fg]| ≤ (E f² + E g²)/2. -/
theorem rl_abs_int_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hfg : Integrable (fun x => f x * g x) μ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) :
    |∫ x, f x * g x ∂μ| ≤ ((∫ x, f x ^ 2 ∂μ) + ∫ x, g x ^ 2 ∂μ) / 2 := by
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_add hf hg, ← integral_div]
  refine integral_mono hfg.abs ((hf.add hg).div_const 2) fun x => ?_
  rw [abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]


/-! ## 3. The box: φ_s, φ_r as linear forms of (ξˢ, ξʳ) and their covariances -/

variable {n k : ℕ}

theorem rl_φs_eq (m₀ T : ℝ) (ξ : DField n k) (y : DSite n k) :
    nl_φs n k m₀ T ξ y = ∑ K, nl_ls n k m₀ T y K * ξ K := by
  rw [nl_φs, md_map_apply, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  rw [nl_ls]; ring

theorem rl_φr_eq (m₀ T : ℝ) (ξ : DField n k) (y : DSite n k) :
    nl_φr n k m₀ T ξ y = ∑ K, nl_lr n k m₀ T y K * ξ K := by
  rw [nl_φr, md_map_apply, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  rw [nl_lr]; ring

theorem rl_one_sub_exp_nonneg (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (K : DSite n k) :
    0 ≤ 1 - Real.exp (-(T * dirEig n k m₀ K)) := by
  have h := mul_nonneg hT (dirEig_pos (n := n) (k := k) m₀ K).le
  have : Real.exp (-(T * dirEig n k m₀ K)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem rl_inv_sqrt_sq (m₀ : ℝ) (K : DSite n k) :
    (√(dirEig n k m₀ K))⁻¹ * (√(dirEig n k m₀ K))⁻¹ = (dirEig n k m₀ K)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (dirEig_pos m₀ K).le]

/-- Cov(φ_r(y), φ_r(y')) = Σ_K ℓʳ_{yK} ℓʳ_{y'K} = C_r(T)(y, y') (T ≥ 0). -/
theorem rl_lr_cov (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y y' : DSite n k) :
    ∑ K, nl_lr n k m₀ T y K * nl_lr n k m₀ T y' K = glp_roughCov n k m₀ T y y' := by
  rw [glp_roughCov_spectral m₀ hT, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  have h1 := Real.mul_self_sqrt (rl_one_sub_exp_nonneg (n := n) (k := k) m₀ hT K)
  have h2 := rl_inv_sqrt_sq (n := n) (k := k) m₀ K
  calc nl_lr n k m₀ T y K * nl_lr n k m₀ T y' K
      = ((spacing n)⁻¹ * (spacing n)⁻¹) * ((√(dirEig n k m₀ K))⁻¹ * (√(dirEig n k m₀ K))⁻¹) *
          (√(1 - Real.exp (-(T * dirEig n k m₀ K))) * √(1 - Real.exp (-(T * dirEig n k m₀ K)))) *
          (sineVec2 K y * sineVec2 K y') := by unfold nl_lr; ring
    _ = _ := by rw [h1, h2, div_eq_mul_inv]; ring

/-- c_r(y) = Var φ_r(y) = Σ_K (ℓʳ_{yK})². -/
theorem rl_cr_eq (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    nl_cr n k m₀ T y = ∑ K, nl_lr n k m₀ T y K ^ 2 := by
  rw [nl_cr, ← rl_lr_cov m₀ hT]; simp only [sq]

/-- Var φ_s(y) = Σ_K (ℓˢ_{yK})² = ε⁻² dirGreen y y − c_r(y). -/
theorem rl_ls_var (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    ∑ K, nl_ls n k m₀ T y K ^ 2 = (spacing n ^ 2)⁻¹ * dirGreen n k m₀ y y - nl_cr n k m₀ T y := by
  rw [nl_cr, ← rl_lr_cov m₀ hT, dirGreen_spectral, mul_sum, eq_sub_iff_add_eq, ← sum_add_distrib]
  refine sum_congr rfl fun K _ => ?_
  have h1 := Real.mul_self_sqrt (rl_one_sub_exp_nonneg (n := n) (k := k) m₀ hT K)
  have h2 := rl_inv_sqrt_sq (n := n) (k := k) m₀ K
  have h3 : Real.exp (-(T * dirEig n k m₀ K) / 2) ^ 2 = Real.exp (-(T * dirEig n k m₀ K)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  calc nl_ls n k m₀ T y K ^ 2 + nl_lr n k m₀ T y K * nl_lr n k m₀ T y K
      = ((spacing n)⁻¹ * (spacing n)⁻¹) * ((√(dirEig n k m₀ K))⁻¹ * (√(dirEig n k m₀ K))⁻¹) *
          (Real.exp (-(T * dirEig n k m₀ K) / 2) ^ 2 +
            √(1 - Real.exp (-(T * dirEig n k m₀ K))) * √(1 - Real.exp (-(T * dirEig n k m₀ K)))) *
          (sineVec2 K y * sineVec2 K y) := by unfold nl_ls nl_lr; ring
    _ = _ := by rw [h1, h2, h3, div_eq_mul_inv]; ring

/-- Var φ_s(y) ≤ c₁(y) (the difference is the Wick defect b(y) = freeVar − ε⁻² dirGreen y y ≥ 0). -/
theorem rl_ls_var_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    ∑ K, nl_ls n k m₀ T y K ^ 2 ≤ nl_cs n k m₀ T y := by
  rw [rl_ls_var m₀ hT, nl_cs]
  linarith [dirVar_le_freeVar hm y]

theorem rl_cs_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    0 ≤ nl_cs n k m₀ T y :=
  (sum_nonneg fun _ _ => sq_nonneg _).trans (rl_ls_var_le hm hT y)

theorem rl_roughCov_symm (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y y' : DSite n k) :
    glp_roughCov n k m₀ T y y' = glp_roughCov n k m₀ T y' y := by
  rw [← rl_lr_cov m₀ hT, ← rl_lr_cov m₀ hT]
  exact sum_congr rfl fun K _ => mul_comm _ _

/-! ## 4. E[R_T²]: factorisation, rough orthogonality, smooth Cauchy–Schwarz -/

/-- S_j(y)(ξˢ) = :φ_s(y)^j:_{c₁(y)}. -/
def rl_S (n k : ℕ) (m₀ T : ℝ) (j : ℕ) (y : DSite n k) (ξ : DField n k) : ℝ :=
  wickPow (nl_cs n k m₀ T y) j (∑ K, nl_ls n k m₀ T y K * ξ K)

/-- B_j(y)(ξʳ) = :φ_r(y)^j:_{c_r(y)}. -/
def rl_B (n k : ℕ) (m₀ T : ℝ) (j : ℕ) (y : DSite n k) (ξ : DField n k) : ℝ :=
  wickPow (nl_cr n k m₀ T y) j (∑ K, nl_lr n k m₀ T y K * ξ K)

theorem rl_int_S (m₀ T : ℝ) (j j' : ℕ) (y y' : DSite n k) :
    Integrable (fun ξ => rl_S n k m₀ T j y ξ * rl_S n k m₀ T j' y' ξ) (nl_gauss n k) :=
  rl_int _ _ _ _ _ _

theorem rl_int_B (m₀ T : ℝ) (j j' : ℕ) (y y' : DSite n k) :
    Integrable (fun ξ => rl_B n k m₀ T j y ξ * rl_B n k m₀ T j' y' ξ) (nl_gauss n k) :=
  rl_int _ _ _ _ _ _

theorem rl_int_S_sq (m₀ T : ℝ) (j : ℕ) (y : DSite n k) :
    Integrable (fun ξ => rl_S n k m₀ T j y ξ ^ 2) (nl_gauss n k) :=
  (rl_int_S m₀ T j j y y).congr (ae_of_all _ fun _ => (sq _).symm)

/-- **(b) Rough Wick covariance at the true rough variances:**
E[:φ_r(y)^a:_{c_r(y)} :φ_r(y')^b:_{c_r(y')}] = δ_ab a! C_r(T)(y, y')^a (a, b ≤ 4, T ≥ 0). -/
theorem rl_cov_B (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {a b : ℕ} (ha : a ≤ 4) (hb : b ≤ 4)
    (y y' : DSite n k) :
    ∫ ξ, rl_B n k m₀ T a y ξ * rl_B n k m₀ T b y' ξ ∂nl_gauss n k =
      if a = b then (a.factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ a else 0 := by
  unfold rl_B
  rw [rl_cr_eq m₀ hT y, rl_cr_eq m₀ hT y', ← rl_lr_cov m₀ hT y y']
  exact rl_cov _ _ a b ha hb

theorem rl_Rω_sq (m₀ T : ℝ) (p : DField n k × DField n k) :
    nl_Rω n k m₀ T p ^ 2 = ∑ y, ∑ y', ∑ j ∈ range 4, ∑ j' ∈ range 4,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rl_S n k m₀ T j y p.1 * rl_S n k m₀ T j' y' p.1) *
          (rl_B n k m₀ T (4 - j) y p.2 * rl_B n k m₀ T (4 - j') y' p.2)) := by
  have hR : nl_Rω n k m₀ T p = spacing n ^ 2 * ∑ y, ∑ j ∈ range 4,
      ((Nat.choose 4 j : ℕ) : ℝ) * rl_S n k m₀ T j y p.1 * rl_B n k m₀ T (4 - j) y p.2 := by
    simp only [nl_Rω, nl_R, rl_S, rl_B, rl_φs_eq, rl_φr_eq]
  rw [hR, sq, mul_mul_mul_comm, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  rw [sum_mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j' _ => ?_
  ring

/-- **(a)+(b): exact second moment of R_T.** Factorisation over γ^Λ ⊗ γ^Λ and rough
orthogonality (only j = j' survives):
E[R_T²] = ε⁴ Σ_{y,y'} Σ_{j<4} C(4,j)² E[S_j(y) S_j(y')] (4−j)! C_r(y,y')^{4−j}. -/
theorem rl_ER2 (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k = ∑ y, ∑ y', ∑ j ∈ range 4,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))) := by
  have hI : ∀ y y' : DSite n k, ∀ j j' : ℕ, Integrable (fun p : DField n k × DField n k =>
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rl_S n k m₀ T j y p.1 * rl_S n k m₀ T j' y' p.1) *
          (rl_B n k m₀ T (4 - j) y p.2 * rl_B n k m₀ T (4 - j') y' p.2))) (nl_P n k) :=
    fun y y' j j' =>
      ((rl_int_S m₀ T j j' y y').mul_prod (rl_int_B m₀ T (4 - j) (4 - j') y y')).const_mul _
  simp_rw [rl_Rω_sq]
  rw [integral_finsetSum _ fun y _ => integrable_finsetSum _ fun y' _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hI y y' j j']
  refine sum_congr rfl fun y _ => ?_
  rw [integral_finsetSum _ fun y' _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun j' _ => hI y y' j j']
  refine sum_congr rfl fun y' _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hI y y' j j']
  refine sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun j' _ => hI y y' j j']
  have hj4 : j < 4 := mem_range.mp hj
  have hfac : ∀ j' : ℕ, ∫ p : DField n k × DField n k,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((rl_S n k m₀ T j y p.1 * rl_S n k m₀ T j' y' p.1) *
          (rl_B n k m₀ T (4 - j) y p.2 * rl_B n k m₀ T (4 - j') y' p.2)) ∂nl_P n k =
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j' : ℝ)) *
        ((∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j' y' ξ ∂nl_gauss n k) *
          (∫ ξ, rl_B n k m₀ T (4 - j) y ξ * rl_B n k m₀ T (4 - j') y' ξ ∂nl_gauss n k)) := by
    intro j'
    rw [integral_const_mul, nl_P]
    exact congrArg _ (integral_prod_mul (L := ℝ) (μ := nl_gauss n k) (ν := nl_gauss n k)
      (fun ξ => rl_S n k m₀ T j y ξ * rl_S n k m₀ T j' y' ξ)
      (fun ξ => rl_B n k m₀ T (4 - j) y ξ * rl_B n k m₀ T (4 - j') y' ξ))
  rw [Finset.sum_eq_single j]
  · rw [hfac, rl_cov_B m₀ hT (by omega) (by omega), ite_eq_left rfl]
  · intro j' hj' hne
    have hj'4 : j' < 4 := mem_range.mp hj'
    rw [hfac, rl_cov_B m₀ hT (by omega) (by omega), ite_eq_right (by omega)]
    ring
  · intro h; exact absurd hj h

/-- M(y) = 15 (1 + c₁(y))³, the bound on E[S_j(y)²] (j ≤ 3). -/
def rl_M (n k : ℕ) (m₀ T : ℝ) (y : DSite n k) : ℝ := 15 * (1 + nl_cs n k m₀ T y) ^ 3

/-- G(y, y') = Σ_{m=1}^4 |C_r(y, y')|^m. -/
def rl_G (n k : ℕ) (m₀ T : ℝ) (y y' : DSite n k) : ℝ :=
  |glp_roughCov n k m₀ T y y'| + |glp_roughCov n k m₀ T y y'| ^ 2 +
    |glp_roughCov n k m₀ T y y'| ^ 3 + |glp_roughCov n k m₀ T y y'| ^ 4

theorem rl_M_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) (y : DSite n k) :
    0 ≤ rl_M n k m₀ T y := by
  have := rl_cs_nonneg hm hT y
  unfold rl_M; positivity

theorem rl_G_symm (m₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (y y' : DSite n k) :
    rl_G n k m₀ T y y' = rl_G n k m₀ T y' y := by
  unfold rl_G; rw [rl_roughCov_symm m₀ hT y y']

/-- **(c) Mis-ordered smooth covariances:** |E[S_j(y) S_j(y')]| ≤ (M(y) + M(y'))/2 (j ≤ 3). -/
theorem rl_E_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) {j : ℕ} (hj : j ≤ 3)
    (y y' : DSite n k) :
    |∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k| ≤
      (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 := by
  refine (rl_abs_int_mul_le (rl_int_S m₀ T j j y y') (rl_int_S_sq m₀ T j y)
    (rl_int_S_sq m₀ T j y')).trans ?_
  have h1 : ∫ ξ, rl_S n k m₀ T j y ξ ^ 2 ∂nl_gauss n k ≤ rl_M n k m₀ T y :=
    rl_smooth_sq (nl_ls n k m₀ T y) (rl_ls_var_le hm hT y) hj
  have h2 : ∫ ξ, rl_S n k m₀ T j y' ξ ^ 2 ∂nl_gauss n k ≤ rl_M n k m₀ T y' :=
    rl_smooth_sq (nl_ls n k m₀ T y') (rl_ls_var_le hm hT y') hj
  linarith

theorem rl_ER2_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k ≤
      96 * (spacing n ^ 2) ^ 2 * ∑ y, ∑ y',
        (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 * rl_G n k m₀ T y y' := by
  rw [rl_ER2 m₀ hT, mul_sum]
  refine sum_le_sum fun y _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun y' _ => ?_
  have hW0 : 0 ≤ (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 := by
    have := rl_M_nonneg hm hT y; have := rl_M_nonneg hm hT y'; positivity
  have hterm : ∀ j ∈ range 4,
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))) ≤
      (spacing n ^ 2) ^ 2 * ((Nat.choose 4 j : ℝ) * (Nat.choose 4 j : ℝ)) *
        ((rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 *
          (((4 - j).factorial : ℝ) * |glp_roughCov n k m₀ T y y'| ^ (4 - j))) := by
    intro j hj
    have hj3 : j ≤ 3 := by simp at hj; omega
    have hE := rl_E_le hm hT hj3 y y'
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hf : (0 : ℝ) ≤ ((4 - j).factorial : ℝ) := by positivity
    calc (∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))
        ≤ |(∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k) *
          (((4 - j).factorial : ℝ) * glp_roughCov n k m₀ T y y' ^ (4 - j))| := le_abs_self _
      _ = |∫ ξ, rl_S n k m₀ T j y ξ * rl_S n k m₀ T j y' ξ ∂nl_gauss n k| *
          (((4 - j).factorial : ℝ) * |glp_roughCov n k m₀ T y y'| ^ (4 - j)) := by
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hf]
      _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)
  refine (sum_le_sum hterm).trans ?_
  simp only [sum_range_succ, sum_range_zero, zero_add, rl_G]
  norm_num [Nat.choose, Nat.factorial]
  have hA := abs_nonneg (glp_roughCov n k m₀ T y y')
  have hX : 0 ≤ (spacing n ^ 2) ^ 2 * ((rl_M n k m₀ T y + rl_M n k m₀ T y') / 2) := by
    positivity
  nlinarith [mul_nonneg hX hA, mul_nonneg hX (pow_nonneg hA 2), mul_nonneg hX (pow_nonneg hA 3),
    mul_nonneg hX (pow_nonneg hA 4)]


/-! ## 5. (d) Summation -/

/-- Σ_a Σ_b ((M a + M b)/2) G a b = Σ_a M a Σ_b G a b for symmetric G. -/
theorem rl_symm_sum {ι : Type*} [Fintype ι] (M : ι → ℝ) (G : ι → ι → ℝ)
    (hG : ∀ a b, G a b = G b a) :
    ∑ a, ∑ b, (M a + M b) / 2 * G a b = ∑ a, M a * ∑ b, G a b := by
  have h2 : ∑ a, ∑ b, M b * G a b = ∑ a, ∑ b, M a * G a b := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [hG]
  have h3 : ∑ a, ∑ b, (M a + M b) / 2 * G a b =
      (∑ a, ∑ b, M a * G a b + ∑ a, ∑ b, M b * G a b) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun b _ => ?_
    ring
  rw [h3, h2, add_self_div_two]
  simp_rw [mul_sum]

/-- The Lᵖ constant of `glp_roughCov_Lp_le`: K_p = (π/4)^{p−1}/2 · p^p. -/
def rl_Kp (p : ℕ) : ℝ := (π / 4) ^ (p - 1) / 2 * (p : ℝ) ^ p

theorem rl_Kp_nonneg (p : ℕ) : 0 ≤ rl_Kp p := by unfold rl_Kp; positivity

/-- K_G = (L² + K₂)/2 + K₂ + K₃ + K₄. -/
def rl_KG (k : ℕ) : ℝ := (boxL k ^ 2 + rl_Kp 2) / 2 + rl_Kp 2 + rl_Kp 3 + rl_Kp 4

theorem rl_boxL_nonneg (k : ℕ) : 0 ≤ boxL k := by unfold boxL; positivity

theorem rl_KG_nonneg (k : ℕ) : 0 ≤ rl_KG k := by
  have := rl_Kp_nonneg 2; have := rl_Kp_nonneg 3; have := rl_Kp_nonneg 4
  unfold rl_KG; positivity

theorem rl_card (n k : ℕ) : spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ) = boxL k ^ 2 := by
  have hL : spacing n * (boxN n k : ℝ) = boxL k := nl_spacing_mul_boxN
  rw [Fintype.card_prod, Fintype.card_fin, ← hL]; push_cast; ring

/-- **Row sums of G:** for T = s⁸ with 0 < s ≤ 1, ε² Σ_{y'} G(y, y') ≤ K_G s⁴ uniformly in n
(`glp_roughCov_Lp_le` for m = 2, 3, 4; for m = 1, |C| ≤ s⁴/2 + |C|²/(2 s⁴)). -/
theorem rl_G_sum_le (m₀ : ℝ) {T s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hTs : T = s ^ 8)
    (y : DSite n k) :
    spacing n ^ 2 * ∑ y', rl_G n k m₀ T y y' ≤ rl_KG k * s ^ 4 := by
  have hT0 : 0 ≤ T := by rw [hTs]; positivity
  have hs4 : 0 < s ^ 4 := by positivity
  have hs84 : s ^ 8 ≤ s ^ 4 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
  have hpT : ∀ p : ℕ, 2 ≤ p →
      spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ p ≤ rl_Kp p * T :=
    fun p hp => glp_roughCov_Lp_le m₀ hT0 p hp y
  have hp4 : ∀ p : ℕ, 2 ≤ p →
      spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ p ≤ rl_Kp p * s ^ 4 := by
    intro p hp
    refine (hpT p hp).trans ?_
    rw [hTs]
    exact mul_le_mul_of_nonneg_left hs84 (rl_Kp_nonneg p)
  have h1 : spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ≤
      (boxL k ^ 2 + rl_Kp 2) / 2 * s ^ 4 := by
    have hpt : ∀ y', |glp_roughCov n k m₀ T y y'| ≤
        s ^ 4 / 2 + |glp_roughCov n k m₀ T y y'| ^ 2 / (2 * s ^ 4) := by
      intro y'
      rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|glp_roughCov n k m₀ T y y'| - s ^ 4)]
    have h2 := hpT 2 le_rfl
    have hε : 0 ≤ spacing n ^ 2 := by positivity
    calc spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'|
        ≤ spacing n ^ 2 * ∑ y', (s ^ 4 / 2 + |glp_roughCov n k m₀ T y y'| ^ 2 / (2 * s ^ 4)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun y' _ => hpt y') hε
      _ = (spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ)) * (s ^ 4 / 2) +
            (spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 2) / (2 * s ^ 4) := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← sum_div]; ring
      _ ≤ boxL k ^ 2 * (s ^ 4 / 2) + (rl_Kp 2 * T) / (2 * s ^ 4) := by
          rw [rl_card]
          gcongr
      _ = (boxL k ^ 2 + rl_Kp 2) / 2 * s ^ 4 := by
          rw [hTs]; field_simp
  have hsum : spacing n ^ 2 * ∑ y', rl_G n k m₀ T y y' =
      spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| +
        spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 2 +
        spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 3 +
        spacing n ^ 2 * ∑ y', |glp_roughCov n k m₀ T y y'| ^ 4 := by
    simp only [rl_G, sum_add_distrib]; ring
  rw [hsum, rl_KG]
  have := hp4 2 (by norm_num); have := hp4 3 (by norm_num); have := hp4 4 (by norm_num)
  nlinarith

/-- (log⁺ x)³ ≤ 512 (1 + √x) for x ≥ 0 (log w ≤ w with w = x^{1/8}). -/
theorem rl_posLog_cube_le {x : ℝ} (hx : 0 ≤ x) : Real.posLog x ^ 3 ≤ 512 * (1 + √x) := by
  rw [Real.posLog_eq_log_max_one hx]
  set z := max 1 x with hz
  have hz1 : 1 ≤ z := le_max_left _ _
  have hs1 : ∀ a : ℝ, 1 ≤ a → 1 ≤ √a := fun a ha => by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt ha
  set w := √(√(√z)) with hw
  have hw1 : 1 ≤ w := hs1 _ (hs1 _ (hs1 _ hz1))
  have hw0 : 0 < w := by linarith
  have hw2 : w ^ 2 = √(√z) := by rw [hw, sq_sqrt (Real.sqrt_nonneg _)]
  have hw4 : w ^ 4 = √z := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hw2, sq_sqrt (Real.sqrt_nonneg _)]
  have hw8 : w ^ 8 = z := by
    rw [show 8 = 4 * 2 by rfl, pow_mul, hw4, sq_sqrt (by linarith)]
  have hlog : Real.log z = 8 * Real.log w := by
    rw [← hw8, Real.log_pow]; push_cast; ring
  have hl0 : 0 ≤ Real.log w := Real.log_nonneg hw1
  have hl1 : Real.log w ≤ w := by linarith [Real.log_le_sub_one_of_pos hw0]
  have hsz : √z ≤ 1 + √x := by
    rcases le_total 1 x with h | h
    · rw [hz, max_eq_right h]; linarith [Real.sqrt_nonneg x]
    · rw [hz, max_eq_left h, Real.sqrt_one]; linarith [Real.sqrt_nonneg x]
  have h3 : Real.log w ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ hl0 hl1 3
  have h34 : w ^ 3 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
  rw [hlog]
  calc (8 * Real.log w) ^ 3 = 512 * Real.log w ^ 3 := by ring
    _ ≤ 512 * w ^ 4 := by linarith
    _ = 512 * √z := by rw [hw4]
    _ ≤ 512 * (1 + √x) := by linarith

/-- For 0 < s ≤ 1: −log s⁸ ≥ 0 and s⁴ (−log s⁸)³ ≤ 512 s. -/
theorem rl_neglog_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ -Real.log (s ^ 8) ∧ s ^ 4 * (-Real.log (s ^ 8)) ^ 3 ≤ 512 * s := by
  have hl : Real.log (s ^ 8) = 8 * Real.log s := by rw [Real.log_pow]; push_cast; ring
  have hl0 : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have hinv : Real.log s⁻¹ ≤ s⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [Real.log_inv] at hinv
  have hst : s * (-Real.log s) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hinv hs.le
    rw [mul_sub, mul_inv_cancel₀ hs.ne', mul_one] at this
    linarith
  have hst0 : 0 ≤ s * (-Real.log s) := mul_nonneg hs.le (by linarith)
  refine ⟨by rw [hl]; linarith, ?_⟩
  rw [hl]
  have h3 : (s * (-Real.log s)) ^ 3 ≤ 1 := pow_le_one₀ hst0 hst
  calc s ^ 4 * (-(8 * Real.log s)) ^ 3 = 512 * s * (s * (-Real.log s)) ^ 3 := by ring
    _ ≤ 512 * s * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 512 * s := mul_one _

theorem rl_cube_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

/-- a₀ = 1 + π/4 + (π/4) m₀⁻². -/
def rl_a0 (m₀ : ℝ) : ℝ := 1 + π / 4 + π / 4 * (m₀ ^ 2)⁻¹

/-- Q₀ = 16 a₀³ + 10240 (π/4)³. -/
def rl_Q0 (m₀ : ℝ) : ℝ := 16 * rl_a0 m₀ ^ 3 + 10240 * (π / 4) ^ 3

/-- Q₁ = 8192 (π/4)³ |m₀|^{−1/2}. -/
def rl_Q1 (m₀ : ℝ) : ℝ := 8192 * (π / 4) ^ 3 * (√|m₀|)⁻¹

/-- **Per-site smooth factor:** for T = s⁸ ∈ (0, 1],
s⁴ (1 + c₁(y))³ ≤ s (Q₀ + Q₁ r(y)^{−1/2}) (with r(y)^{−1/2} = `nl_f n (fv2_bdist y)`). -/
theorem rl_site_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hTs : T = s ^ 8) (y : DSite n k) :
    s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3 ≤
      s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (fv2_bdist y)) := by
  have hT : 0 < T := by rw [hTs]; positivity
  have hT1 : T ≤ 1 := by rw [hTs]; exact pow_le_one₀ hs.le hs1
  obtain ⟨h0, h1⟩ := nl_cs_bounds hm hT hT1 y
  set ℓ := Real.posLog (1 / (|m₀| * fv2_rdist n k y)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
  set m' : ℝ := (√|m₀|)⁻¹ with hm'
  have hm'0 : 0 ≤ m' := by positivity
  have hx : √(1 / (|m₀| * fv2_rdist n k y)) = m' * nl_f n (fv2_bdist y) := by
    rw [fv2_rdist, nl_f, one_div, Real.sqrt_inv, Real.sqrt_mul (abs_nonneg _), mul_inv]
  have hℓ3 : ℓ ^ 3 ≤ 512 * (1 + m' * nl_f n (fv2_bdist y)) := by
    rw [← hx]
    exact rl_posLog_cube_le (by unfold fv2_rdist; have := spacing_pos n; positivity)
  obtain ⟨hL0, hL⟩ := rl_neglog_le hs hs1
  rw [← hTs] at hL0 hL
  have hπ : 0 ≤ π / 4 := by positivity
  set A := rl_a0 m₀ + π / 4 * ℓ with hA
  set e := π / 4 * (-Real.log T) with he
  have ha0 : 0 ≤ rl_a0 m₀ := by unfold rl_a0; positivity
  have hA0 : 0 ≤ A := by positivity
  have he0 : 0 ≤ e := mul_nonneg hπ hL0
  have h1' : 1 + nl_cs n k m₀ T y ≤ A + e := by
    rw [hA, he, rl_a0]; linarith
  have hc3 : (1 + nl_cs n k m₀ T y) ^ 3 ≤ 4 * (A ^ 3 + e ^ 3) :=
    (pow_le_pow_left₀ (by linarith) h1' 3).trans (rl_cube_add hA0 he0)
  have hA3 : A ^ 3 ≤ 4 * (rl_a0 m₀ ^ 3 + (π / 4) ^ 3 * (512 * (1 + m' * nl_f n (fv2_bdist y)))) := by
    refine (rl_cube_add ha0 (mul_nonneg hπ hℓ0)).trans ?_
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left hℓ3 (pow_nonneg hπ 3)
    linarith
  have hs4 : s ^ 4 ≤ s := by
    calc s ^ 4 ≤ s ^ 1 := pow_le_pow_of_le_one hs.le hs1 (by norm_num)
      _ = s := pow_one s
  have he3 : s ^ 4 * e ^ 3 ≤ (π / 4) ^ 3 * (512 * s) := by
    rw [he, mul_pow]
    calc s ^ 4 * ((π / 4) ^ 3 * (-Real.log T) ^ 3) = (π / 4) ^ 3 * (s ^ 4 * (-Real.log T) ^ 3) := by
          ring
      _ ≤ (π / 4) ^ 3 * (512 * s) := mul_le_mul_of_nonneg_left hL (pow_nonneg hπ 3)
  have hsA : s ^ 4 * A ^ 3 ≤ s * A ^ 3 := mul_le_mul_of_nonneg_right hs4 (pow_nonneg hA0 3)
  calc s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3 ≤ s ^ 4 * (4 * (A ^ 3 + e ^ 3)) :=
        mul_le_mul_of_nonneg_left hc3 (by positivity)
    _ = 4 * (s ^ 4 * A ^ 3) + 4 * (s ^ 4 * e ^ 3) := by ring
    _ ≤ 4 * (s * A ^ 3) + 4 * ((π / 4) ^ 3 * (512 * s)) := by linarith
    _ ≤ 4 * (s * (4 * (rl_a0 m₀ ^ 3 + (π / 4) ^ 3 * (512 * (1 + m' * nl_f n (fv2_bdist y)))))) +
          4 * ((π / 4) ^ 3 * (512 * s)) := by
        have := mul_le_mul_of_nonneg_left hA3 hs.le
        linarith
    _ = s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (fv2_bdist y)) := by
        rw [rl_Q0, rl_Q1, ← hm']; ring

theorem rl_sum_site_le {m₀ : ℝ} (hm : m₀ ≠ 0) {T s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hTs : T = s ^ 8) :
    spacing n ^ 2 * ∑ y : DSite n k, s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3 ≤
      s * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))) := by
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  have hQ1 : 0 ≤ rl_Q1 m₀ := by unfold rl_Q1; positivity
  have hfs := nl_sum_f_bdist (n := n) (k := k)
  calc spacing n ^ 2 * ∑ y : DSite n k, s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3
      ≤ spacing n ^ 2 * ∑ y : DSite n k, s * (rl_Q0 m₀ + rl_Q1 m₀ * nl_f n (fv2_bdist y)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => rl_site_le hm hs hs1 hTs y) hε
    _ = s * (rl_Q0 m₀ * (spacing n ^ 2 * (Fintype.card (DSite n k) : ℝ)) +
          rl_Q1 m₀ * (spacing n ^ 2 * ∑ y : DSite n k, nl_f n (fv2_bdist y))) := by
        simp only [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
        ring
    _ ≤ s * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))) := by
        rw [rl_card]
        apply mul_le_mul_of_nonneg_left _ hs.le
        have := mul_le_mul_of_nonneg_left hfs hQ1
        linarith

/-! ## 6. The rough L² hypothesis and Nelson's bound for the box -/

/-- **Step 3 of Nelson's argument (box): the rough L² bound.** For m₀ ≠ 0 and every k,
E_{γ⊗γ}[R_T²] ≤ K T^{1/8} for all n and T ∈ (0, 1], with
K = 1440 K_G (Q₀ L² + 8 Q₁ L^{3/2}) independent of n and T. -/
theorem rl_roughL2Hyp {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ) : nl_RoughL2Hyp m₀ k := by
  refine ⟨96 * rl_KG k * 15 * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))),
    1 / 8, by norm_num, fun n T hT hT1 => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = T ^ (1 / 8 : ℝ) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; exact Real.rpow_pos_of_pos hT _
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.rpow_le_one hT.le hT1 (by norm_num)
  have hTs : T = s ^ 8 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]; norm_num
  rw [← hsdef]
  have hε : 0 ≤ spacing n ^ 2 := by positivity
  have hKG := rl_KG_nonneg k
  calc ∫ p, nl_Rω n k m₀ T p ^ 2 ∂nl_P n k
      ≤ 96 * (spacing n ^ 2) ^ 2 * ∑ y, ∑ y',
          (rl_M n k m₀ T y + rl_M n k m₀ T y') / 2 * rl_G n k m₀ T y y' :=
        rl_ER2_le hm hT.le
    _ = 96 * spacing n ^ 2 * ∑ y, rl_M n k m₀ T y * (spacing n ^ 2 * ∑ y', rl_G n k m₀ T y y') := by
        rw [rl_symm_sum _ _ (rl_G_symm m₀ hT.le), mul_sum, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ ≤ 96 * spacing n ^ 2 * ∑ y, rl_M n k m₀ T y * (rl_KG k * s ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (rl_G_sum_le m₀ hs hs1 hTs y)
          (rl_M_nonneg hm hT.le y)
    _ = 96 * rl_KG k * 15 *
          (spacing n ^ 2 * ∑ y : DSite n k, s ^ 4 * (1 + nl_cs n k m₀ T y) ^ 3) := by
        simp only [rl_M, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        ring
    _ ≤ 96 * rl_KG k * 15 *
          (s * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k))))) :=
        mul_le_mul_of_nonneg_left (rl_sum_site_le hm hs hs1 hTs) (by positivity)
    _ = 96 * rl_KG k * 15 * (rl_Q0 m₀ * boxL k ^ 2 + rl_Q1 m₀ * (8 * (boxL k * √(boxL k)))) * s := by
        ring

/-- **Nelson's bound for the box (G4), unconditional for m₀ ≠ 0:**
∃ N, ∀ n, ∀ λ ∈ [0, 1], E⁰[exp(−2λ ε² Σ_y :φ_y⁴:)] ≤ N (both forms of `nl_NelsonBox`). -/
theorem rl_nelsonBox {m₀ : ℝ} (hm : m₀ ≠ 0) (k : ℕ) : nl_NelsonBox m₀ k :=
  nl_nelsonBox_of_roughL2 hm k (rl_roughL2Hyp hm k)

end PP2RoughL2

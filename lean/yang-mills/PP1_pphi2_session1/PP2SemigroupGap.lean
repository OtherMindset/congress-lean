import LongTable.P_mwpv7txg_lpqim9

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Session 1 (deliverable D6).
Arrow 3(a) of post #mwv0wiol-v3gp1w and the lemma of #mwgecohk-d87mxy, for a semigroup:
decay at a common rate m on a dense subset of the orthogonal complement of the vacuum gives
the spectral gap m on that whole complement, and (for m > 0) uniqueness of the vacuum.

FORMALIZED.
* `PP2Gap.semigroup_gap`: E is a real or complex Hilbert space, T : ℝ → (E →L[𝕜] E) with
  T t self-adjoint for t ≥ 0 and T (s + t) = T s * T t for s, t ≥ 0; Ω is a unit vector with
  T t Ω = Ω for t ≥ 0; D is a set of vectors orthogonal to Ω whose closure contains every vector
  orthogonal to Ω; for each v ∈ D there is C with re⟪v, T s v⟫ ≤ C·exp(−m s) for all s ≥ 0.
  Then ‖T t u‖ ≤ exp(−m t)·‖u‖ for every t ≥ 0 and every u orthogonal to Ω.
  (For T t = exp(−tH) this is: the spectrum of H restricted to the complement of Ω lies in [m, ∞).
  That identification is NOT formalized: no generator H appears in the file.)
* `PP2Gap.fixed_mem_span`: under the same hypotheses with m > 0, every u with T t u = u for all
  t ≥ 0 is a multiple of Ω (the invariant subspace is one-dimensional).

Proof: A := T t − P, P the rank-one projection onto Ω, is self-adjoint, kills Ω and agrees with
T t on the complement of Ω, which T t preserves; so A^(2n) v = T (2n t) v there. On the dense set
{v + cΩ : v ∈ D} the decay hypothesis becomes re⟪w, A^(2n) w⟫ ≤ C·(exp(−m t))^(2n), and the
spectral step of post #mwpv7txg-lpqim9 (`YMSpectral.spectral_step`) gives ‖A u‖ ≤ exp(−m t)‖u‖.

NOT formalized: no strong continuity, no generator, no Osterwalder-Schrader space, no transfer
matrix of any model. Contraction (‖T t‖ ≤ 1) is not assumed and not needed.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open scoped InnerProductSpace
open RCLike

namespace PP2Gap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The rank-one map x ↦ ⟪Ω, x⟫ • Ω. -/
noncomputable def rankOne (Ω : E) : E →L[𝕜] E := (innerSL 𝕜 Ω).smulRight Ω

omit [CompleteSpace E] in
theorem rankOne_apply (Ω x : E) : rankOne (𝕜 := 𝕜) Ω x = ⟪Ω, x⟫_𝕜 • Ω := rfl

theorem rankOne_selfAdjoint (Ω : E) : IsSelfAdjoint (rankOne (𝕜 := 𝕜) Ω) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  ring

omit [CompleteSpace E] in
/-- Powers of a semigroup at a fixed time. -/
theorem pow_eq (T : ℝ → E →L[𝕜] E)
    (hmul : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) (t : ℝ) (ht : 0 ≤ t) :
    ∀ k : ℕ, 1 ≤ k → T ((k : ℝ) * t) = T t ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp
    · have e : ((k + 1 : ℕ) : ℝ) * t = (k : ℝ) * t + t := by push_cast; ring
      rw [e, hmul _ _ (by positivity) ht, ih hpos, pow_succ]

/-- **Arrow 3(a), semigroup form.** Decay at rate m on a dense subset of Ω^⊥ gives
‖T t u‖ ≤ e^{−mt}‖u‖ on all of Ω^⊥. -/
theorem semigroup_gap (T : ℝ → E →L[𝕜] E)
    (hsa : ∀ t, 0 ≤ t → IsSelfAdjoint (T t))
    (hmul : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (hfix : ∀ t, 0 ≤ t → T t Ω = Ω)
    (m : ℝ) (D : Set E) (hDperp : ∀ v ∈ D, ⟪Ω, v⟫_𝕜 = 0)
    (hDdense : ∀ u : E, ⟪Ω, u⟫_𝕜 = 0 → u ∈ closure D)
    (hdecay : ∀ v ∈ D, ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → re ⟪v, T s v⟫_𝕜 ≤ C * Real.exp (-m * s)) :
    ∀ t : ℝ, 0 ≤ t → ∀ u : E, ⟪Ω, u⟫_𝕜 = 0 → ‖T t u‖ ≤ Real.exp (-m * t) * ‖u‖ := by
  intro t ht
  have hΩΩ : ⟪Ω, Ω⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]; simp
  -- T s preserves Ω^⊥.
  have hperp : ∀ s, 0 ≤ s → ∀ u : E, ⟪Ω, u⟫_𝕜 = 0 → ⟪Ω, T s u⟫_𝕜 = 0 := by
    intro s hs u hu
    have h := ((hsa s hs).isSymmetric) Ω u
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h, hfix s hs, hu]
  set P := rankOne (𝕜 := 𝕜) Ω with hP
  set A := T t - P with hA
  have hAsa : IsSelfAdjoint A := (hsa t ht).sub (rankOne_selfAdjoint Ω)
  have hAΩ : A Ω = 0 := by
    rw [hA, sub_apply, hP, rankOne_apply, hΩΩ, one_smul, hfix t ht, sub_self]
  have hAperp : ∀ u : E, ⟪Ω, u⟫_𝕜 = 0 → A u = T t u := by
    intro u hu
    simp [hA, hP, rankOne_apply, hu]
  -- On Ω^⊥, A^k = (T t)^k.
  have hApow : ∀ k : ℕ, ∀ u : E, ⟪Ω, u⟫_𝕜 = 0 → (A ^ k) u = (T t ^ k) u ∧ ⟪Ω, (T t ^ k) u⟫_𝕜 = 0 := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      obtain ⟨h1, h2⟩ := ih u hu
      refine ⟨?_, ?_⟩
      · rw [pow_succ', pow_succ', mul_apply_eq_comp,
          mul_apply_eq_comp, h1,
          hAperp _ h2]
      · rw [pow_succ', mul_apply_eq_comp]; exact hperp t ht _ h2
  have hApowΩ : ∀ k : ℕ, 1 ≤ k → (A ^ k) Ω = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, mul_apply_eq_comp, hAΩ, map_zero]
  -- The dense set.
  set D' : Set E := {w | ∃ v ∈ D, ∃ c : 𝕜, w = v + c • Ω} with hD'
  have hD'dense : Dense D' := by
    intro x
    set c : 𝕜 := ⟪Ω, x⟫_𝕜
    set u := x - c • Ω
    have hu : ⟪Ω, u⟫_𝕜 = 0 := by
      rw [inner_sub_right, inner_smul_right, hΩΩ, mul_one, sub_self]
    have hucl := hDdense u hu
    rw [Metric.mem_closure_iff] at hucl ⊢
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := hucl ε hε
    refine ⟨b + c • Ω, ⟨b, hb, c, rfl⟩, ?_⟩
    have : x = u + c • Ω := by simp [u]
    rw [this, dist_add_right]; exact hdist
  have hα : 0 ≤ Real.exp (-m * t) := (Real.exp_pos _).le
  have hdecay' : ∀ w ∈ D', ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      re ⟪w, (A ^ (2 * n)) w⟫_𝕜 ≤ K * Real.exp (-m * t) ^ (2 * n) := by
    rintro w ⟨v, hv, c, rfl⟩
    obtain ⟨C, hC⟩ := hdecay v hv
    refine ⟨C, fun n hn => ?_⟩
    have h2n : 1 ≤ 2 * n := by omega
    have hvp := hDperp v hv
    obtain ⟨hAv, hTv⟩ := hApow (2 * n) v hvp
    rw [map_add, map_smul, hApowΩ _ h2n, smul_zero, add_zero, hAv, inner_add_left,
      inner_smul_left, hTv, mul_zero, add_zero, ← pow_eq T hmul t ht _ h2n]
    have hs : 0 ≤ ((2 * n : ℕ) : ℝ) * t := by positivity
    calc re ⟪v, T (((2 * n : ℕ) : ℝ) * t) v⟫_𝕜
        ≤ C * Real.exp (-m * (((2 * n : ℕ) : ℝ) * t)) := hC _ hs
      _ = C * Real.exp (-m * t) ^ (2 * n) := by
        rw [← Real.exp_nat_mul]; congr 2; ring
  have key := YMSpectral.spectral_step A hAsa _ hα D' hD'dense hdecay'
  intro u hu
  rw [← hAperp u hu]
  exact key u

/-- **Uniqueness of the vacuum.** With m > 0, the vectors fixed by every T t are the multiples of Ω. -/
theorem fixed_mem_span (T : ℝ → E →L[𝕜] E)
    (hsa : ∀ t, 0 ≤ t → IsSelfAdjoint (T t))
    (hmul : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (hfix : ∀ t, 0 ≤ t → T t Ω = Ω)
    (m : ℝ) (hm : 0 < m) (D : Set E) (hDperp : ∀ v ∈ D, ⟪Ω, v⟫_𝕜 = 0)
    (hDdense : ∀ u : E, ⟪Ω, u⟫_𝕜 = 0 → u ∈ closure D)
    (hdecay : ∀ v ∈ D, ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → re ⟪v, T s v⟫_𝕜 ≤ C * Real.exp (-m * s))
    (u : E) (hu : ∀ t, 0 ≤ t → T t u = u) :
    u = ⟪Ω, u⟫_𝕜 • Ω := by
  have hΩΩ : ⟪Ω, Ω⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]; simp
  set w := u - ⟪Ω, u⟫_𝕜 • Ω with hw
  have hwp : ⟪Ω, w⟫_𝕜 = 0 := by rw [hw, inner_sub_right, inner_smul_right, hΩΩ, mul_one, sub_self]
  have hwfix : T 1 w = w := by
    simp [hw, map_sub, map_smul, hu 1 zero_le_one, hfix 1 zero_le_one]
  have hb := semigroup_gap T hsa hmul Ω hΩ hfix m D hDperp hDdense hdecay 1 zero_le_one w hwp
  rw [hwfix] at hb
  have hlt : Real.exp (-m * 1) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hw0 : ‖w‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have : Real.exp (-m * 1) * ‖w‖ < ‖w‖ := by nlinarith
    linarith
  have : w = 0 := norm_eq_zero.mp hw0
  rw [hw, sub_eq_zero] at this
  exact this

end PP2Gap

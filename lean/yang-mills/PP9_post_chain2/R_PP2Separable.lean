import LongTable.P_mwwlpzs6_scsdxq

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Separable.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction. Proof of `SchwartzSeparable`
(the separability hypothesis of PP2Limit / PP2Limit2 / PP2Assembly).

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* `schwartzSeparable : PP2Target.SchwartzSeparable`: for every (a, b) a countable D ⊆ TestFn is
  dense for ‖·‖_{a,b} = `schwartzSup a b`.

ROUTE (no Hermite functions, no cut-offs). Fix (a, b), put q = ‖·‖_{a+1,b}. For R ∈ ℕ let
  Ψ_R f = ((x ↦ (D⁰f x, …, D^b f x)) restricted to the closed ball B_R, q f)
       ∈ C(B_R, Π_{n ≤ b} E_n) × ℝ,   E_n = continuous n-multilinear maps Plane^n → ℝ.
The target is a second-countable metric space (`ContinuousMap.instSecondCountableTopology`, B_R
compact, E_n finite-dimensional), so the range of Ψ_R has a countable dense subset; pick
preimages D_R and let D = ⋃_R D_R. Given f, ε: choose R with 2^{a+1}(2 q f + 1)/(1 + R) < ε/2 and
d ∈ D_R with Ψ_R d close to Ψ_R f. On B_R, ‖x‖^k ‖Dⁿ(f − d) x‖ ≤ (1 + R)^a · δ; off B_R,
‖x‖^k ‖Dⁿh x‖ ≤ 2^{a+1} q h / (1 + ‖x‖) (`one_add_le_sup_seminorm_apply`) and q d < q f + 1.
So every seminorm (k, n) ≤ (a, b) of f − d is ≤ ε/2.

Helpers prefixed `sep_`.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Metric Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Target

/-- The fibre of the iterated derivatives. -/
abbrev sep_E (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ

/-- The closed ball of radius R in the plane. -/
abbrev sep_B (R : ℕ) := closedBall (0 : Plane) (R : ℝ)

instance sep_compact (R : ℕ) : CompactSpace (sep_B R) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

instance sep_fd (n : ℕ) : FiniteDimensional ℝ (sep_E n) :=
  FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) :
      sep_E n →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => Plane) ℝ)
    ContinuousMultilinearMap.toMultilinearMap_injective

instance sep_proper (n : ℕ) : ProperSpace (sep_E n) := FiniteDimensional.proper_real _

instance sep_scE (n : ℕ) : SecondCountableTopology (sep_E n) := secondCountable_of_proper

instance sep_scG (b : ℕ) : SecondCountableTopology (∀ n : Fin (b + 1), sep_E n) :=
  inferInstance

instance sep_scC (b R : ℕ) :
    SecondCountableTopology C(sep_B R, ∀ n : Fin (b + 1), sep_E n) :=
  ContinuousMap.instSecondCountableTopology

instance sep_scY (b R : ℕ) :
    SecondCountableTopology (C(sep_B R, ∀ n : Fin (b + 1), sep_E n) × ℝ) := inferInstance

/-- The jet (D⁰f, …, D^b f) restricted to the closed ball B_R. -/
def sep_jet (b R : ℕ) (f : TestFn) : C(sep_B R, ∀ n : Fin (b + 1), sep_E n) where
  toFun x n := iteratedFDeriv ℝ n f x
  continuous_toFun := continuous_pi fun n =>
    ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      continuous_subtype_val

/-- The map Ψ_R. -/
def sep_Psi (a b R : ℕ) (f : TestFn) : C(sep_B R, ∀ n : Fin (b + 1), sep_E n) × ℝ :=
  (sep_jet b R f, schwartzSup (a + 1) b f)

theorem sep_iteratedFDeriv_sub (n : ℕ) (f g : TestFn) (x : Plane) :
    iteratedFDeriv ℝ n ⇑(f - g) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
  rw [show ⇑(f - g) = ⇑f - ⇑g from funext fun y => by simp]
  exact iteratedFDeriv_sub_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
    ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt

/-- Tail bound: ‖x‖^k ‖Dⁿh x‖ (1 + ‖x‖) ≤ 2^{a+1} ‖h‖_{a+1,b} for k ≤ a, n ≤ b. -/
theorem sep_tail {a b k n : ℕ} (hk : k ≤ a) (hn : n ≤ b) (h : TestFn) (x : Plane) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n h x‖ * (1 + ‖x‖) ≤ 2 ^ (a + 1) * schwartzSup (a + 1) b h := by
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (a + 1, b))
    (k := a + 1) (n := n) le_rfl hn h x
  have hx1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ a :=
    (pow_le_pow_left₀ (norm_nonneg x) (by linarith) k).trans (pow_le_pow_right₀ hx1 hk)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n h x‖ * (1 + ‖x‖)
      ≤ (1 + ‖x‖) ^ a * ‖iteratedFDeriv ℝ n h x‖ * (1 + ‖x‖) := by gcongr
    _ = (1 + ‖x‖) ^ (a + 1) * ‖iteratedFDeriv ℝ n h x‖ := by ring
    _ ≤ _ := h1

/-- Countable dense subsets of the range of Ψ_R, pulled back. -/
theorem sep_countable_R (a b R : ℕ) : ∃ D : Set TestFn, D.Countable ∧
    ∀ f : TestFn, ∀ δ > 0, ∃ d ∈ D, dist (sep_Psi a b R d) (sep_Psi a b R f) < δ := by
  set S := Set.range (sep_Psi a b R)
  have : SecondCountableTopology S := inferInstance
  obtain ⟨c, hc, hcd⟩ := TopologicalSpace.exists_countable_dense S
  refine ⟨(fun y : S => Classical.choose y.2) '' c, hc.image _, fun f δ hδ => ?_⟩
  obtain ⟨y, hy2, hy1⟩ := hcd.exists_mem_open
    (Metric.isOpen_ball (x := (⟨sep_Psi a b R f, f, rfl⟩ : S)) (ε := δ))
    ⟨_, Metric.mem_ball_self hδ⟩
  refine ⟨Classical.choose y.2, ⟨y, hy2, rfl⟩, ?_⟩
  rw [Classical.choose_spec y.2]
  exact hy1

/-- **Separability of the Schwartz space for each finite seminorm.** -/
theorem schwartzSeparable : SchwartzSeparable := by
  intro a b
  choose D hD hdense using sep_countable_R a b
  refine ⟨⋃ R, D R, Set.countable_iUnion hD, fun f ε hε => ?_⟩
  set q := schwartzSup (a + 1) b with hq
  set A : ℝ := 2 ^ (a + 1) * (2 * q f + 1) with hA
  have hqf : 0 ≤ q f := apply_nonneg _ _
  have hApos : 0 < A := by positivity
  obtain ⟨R, hR⟩ := exists_nat_gt (2 * A / ε)
  have hR1 : (0 : ℝ) < 1 + R := by positivity
  have hAR : A / (1 + R) < ε / 2 := by
    rw [div_lt_iff₀ hR1]
    rw [div_lt_iff₀ hε] at hR
    nlinarith
  set δ := min 1 (ε / (2 * (1 + (R : ℝ)) ^ a)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  obtain ⟨d, hdD, hd⟩ := hdense R f δ hδpos
  refine ⟨d, Set.mem_iUnion.mpr ⟨R, hdD⟩, ?_⟩
  -- the two components
  have hd1 : dist (sep_jet b R d) (sep_jet b R f) < δ :=
    lt_of_le_of_lt (le_max_left _ _) (by simpa [Prod.dist_eq, sep_Psi] using hd)
  have hd2 : dist (q d) (q f) < δ :=
    lt_of_le_of_lt (le_max_right _ _) (by simpa [Prod.dist_eq, sep_Psi] using hd)
  have hqd : q d < q f + 1 := by
    have := (abs_sub_lt_iff.mp (Real.dist_eq _ _ ▸ hd2)).1
    linarith [min_le_left 1 (ε / (2 * (1 + (R : ℝ)) ^ a))]
  have hqd0 : 0 ≤ q d := apply_nonneg _ _
  have key : ∀ k n : ℕ, k ≤ a → n ≤ b → ∀ x : Plane,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ⇑(f - d) x‖ ≤ ε / 2 := by
    intro k n hk hn x
    rw [sep_iteratedFDeriv_sub]
    by_cases hx : ‖x‖ ≤ R
    · have hxB : x ∈ sep_B R := by simpa [sep_B] using hx
      have hpt : ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖ < δ := by
        have h1 := ContinuousMap.dist_apply_le_dist (f := sep_jet b R d) (g := sep_jet b R f)
          ⟨x, hxB⟩
        have h2 := dist_le_pi_dist (sep_jet b R d ⟨x, hxB⟩) (sep_jet b R f ⟨x, hxB⟩)
          ⟨n, Nat.lt_succ_of_le hn⟩
        have h3 : dist (sep_jet b R d ⟨x, hxB⟩ ⟨n, Nat.lt_succ_of_le hn⟩)
            (sep_jet b R f ⟨x, hxB⟩ ⟨n, Nat.lt_succ_of_le hn⟩)
            = ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖ := by
          rw [dist_comm, dist_eq_norm]; rfl
        linarith
      have hxk : ‖x‖ ^ k ≤ (1 + (R : ℝ)) ^ a :=
        (pow_le_pow_left₀ (norm_nonneg x) (by linarith) k).trans
          (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]) hk)
      have hpow : 0 < (1 + (R : ℝ)) ^ a := by positivity
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖
          ≤ (1 + (R : ℝ)) ^ a * δ := by
            apply mul_le_mul hxk hpt.le (norm_nonneg _) hpow.le
        _ ≤ (1 + (R : ℝ)) ^ a * (ε / (2 * (1 + (R : ℝ)) ^ a)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hpow.le
        _ = ε / 2 := by field_simp
    · push Not at hx
      have hx1 : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
      have hRx : 1 + (R : ℝ) ≤ 1 + ‖x‖ := by linarith
      have tf := sep_tail hk hn f x
      have td := sep_tail hk hn d x
      have hsum : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖ * (1 + ‖x‖)
          ≤ A := by
        have := norm_sub_le (iteratedFDeriv ℝ n f x) (iteratedFDeriv ℝ n d x)
        have hxk0 : 0 ≤ ‖x‖ ^ k := by positivity
        calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖ * (1 + ‖x‖)
            ≤ ‖x‖ ^ k * (‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n d x‖) * (1 + ‖x‖) := by
              gcongr
          _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖)
              + ‖x‖ ^ k * ‖iteratedFDeriv ℝ n d x‖ * (1 + ‖x‖) := by ring
          _ ≤ 2 ^ (a + 1) * q f + 2 ^ (a + 1) * q d := add_le_add tf td
          _ ≤ A := by
              rw [hA]
              have : (0 : ℝ) < 2 ^ (a + 1) := by positivity
              nlinarith
      have hle : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖ ≤ A / (1 + R) := by
        rw [le_div_iff₀ hR1]
        have h0 : 0 ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖ := by
          positivity
        calc _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n d x‖ * (1 + ‖x‖) :=
              mul_le_mul_of_nonneg_left hRx h0
          _ ≤ A := hsum
      linarith
  have hsup : schwartzSup a b (f - d) ≤ ε / 2 := by
    unfold schwartzSup
    refine Seminorm.finset_sup_apply_le (by linarith) fun m hm => ?_
    have hm' : m.1 ≤ a ∧ m.2 ≤ b := by simpa [Finset.mem_Iic, Prod.le_def] using hm
    exact SchwartzMap.seminorm_le_bound ℝ m.1 m.2 (f - d) (by linarith)
      (key m.1 m.2 hm'.1 hm'.2)
  linarith

end PP2Target

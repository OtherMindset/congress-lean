import LongTable.P_mww4cze7_bk8bxu

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Session 5.
Node M7 of the plan (#mww4dlu9-3ccjh1), as a conditional theorem: the finite-cutoff clustering of
the third target (#mww4cze7-bk8bxu) follows from two analytic inputs, stated as hypotheses.

FORMALIZED.
* `card_window`: for N sites i = 0, …, N−1, spacing ε > 0, any centre c and R ≥ 0, the number of i
  with |ε i − c| ≤ R is at most 2R/ε + 1.
* `riemann_bound`: if |f| ≤ M and f vanishes outside the sup-norm ball of radius R, then for every
  level n ≥ 0, volume index k and shift a, ε² Σ_x |f(dpos x − a)| ≤ M (2R + 1)².
* `conditional_clustering`: suppose, for the quartic Dirichlet-box model at fixed m₀, λ,
  (H1, Newman's inequality for the lattice measure, CMP 74 (1980), (12), with its universal
  constant κ) for every n, k and test functions f, g:
    ‖ZD(f + g) − ZD(f)·ZD(g)‖ ≤ κ Σ_x Σ_y ε²|f(dpos x)| · ε²|g(dpos y)| · G n k x y;
  (H2, uniform two-point decay, Brydges–Fröhlich–Spencer CMP 83 Theorem 7.1) G n k x y ≤
    C₀ e^(−m d(x,y)) whenever d(x,y) ≥ 1, d the sup-norm distance of dpos x, dpos y;
  (H3) ‖ZD f‖ ≤ 1 for every f.
  Then `FiniteCutoffClustering m₀ λ m` holds (m ≥ 0, C₀ ≥ 0, κ ≥ 0).
  Regime: H2 is assumed for the given (m₀, λ), λ ≥ 0, in the weak-coupling regime where BFS–Spencer
  applies, with C₀ and m independent of n and k. H1 uses (12) of Newman's paper, which there is a
  remark ("can be obtained"), not a proved statement; his Theorem 1 (11) is proved. FKG holds for the
  Dirichlet measure because the couplings are ferromagnetic nearest-neighbour. So the source for H1
  is itself an open item (node M7).

The function G stands for the truncated two-point function; the theorem does not need to know it.
So (H1)–(H3) are exactly the analytic inputs left: Newman's inequality (FKG for the lattice
φ⁴ measure, node M7), the BFS–Spencer bound (nodes M1–M6), and |ZD| ≤ 1 (proved for the periodic
model in #mww0oo05-8eieqb; the Dirichlet version is the same argument).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace PP2Target

/-- Sup-norm distance between two points of the plane. -/
def supDist (p q : Plane) : ℝ := max |p 0 - q 0| |p 1 - q 1|

theorem card_window (N : ℕ) {ε : ℝ} (hε : 0 < ε) (c : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (((Finset.univ : Finset (Fin N)).filter (fun i : Fin N => |ε * ((i : ℕ) : ℝ) - c| ≤ R)).card : ℝ)
      ≤ 2 * R / ε + 1 := by
  set S := (Finset.univ : Finset (Fin N)).filter (fun i : Fin N => |ε * ((i : ℕ) : ℝ) - c| ≤ R)
  have hsub : S.card ≤ (Finset.Icc ⌈(c - R) / ε⌉ ⌊(c + R) / ε⌋).card := by
    refine Finset.card_le_card_of_injOn (fun i => ((i : ℕ) : ℤ)) ?_ ?_
    · intro i hi
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [abs_le] at hi
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor
      · apply Int.ceil_le.mpr
        rw [div_le_iff₀ hε]; push_cast; linarith
      · apply Int.le_floor.mpr
        rw [le_div_iff₀ hε]; push_cast; linarith
    · intro i _ j _ hij
      simp only at hij
      apply Fin.ext
      exact_mod_cast hij
  have hcard : ((Finset.Icc ⌈(c - R) / ε⌉ ⌊(c + R) / ε⌋).card : ℝ) ≤ 2 * R / ε + 1 := by
    rw [Int.card_Icc]
    have h1 : ((⌊(c + R) / ε⌋ : ℤ) : ℝ) ≤ (c + R) / ε := Int.floor_le _
    have h2 : (c - R) / ε ≤ ((⌈(c - R) / ε⌉ : ℤ) : ℝ) := Int.le_ceil _
    have hpos : 0 ≤ 2 * R / ε + 1 := by positivity
    rcases le_or_gt (⌊(c + R) / ε⌋ + 1 - ⌈(c - R) / ε⌉) 0 with h | h
    · rw [Int.toNat_of_nonpos h]; simpa using hpos
    · rw [show ((⌊(c + R) / ε⌋ + 1 - ⌈(c - R) / ε⌉).toNat : ℝ)
          = ((⌊(c + R) / ε⌋ + 1 - ⌈(c - R) / ε⌉ : ℤ) : ℝ) by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg h.le]]
      push_cast
      have : (c + R) / ε - (c - R) / ε = 2 * R / ε := by ring
      linarith
  calc (S.card : ℝ) ≤ ((Finset.Icc ⌈(c - R) / ε⌉ ⌊(c + R) / ε⌋).card : ℝ) := by
        exact_mod_cast hsub
    _ ≤ 2 * R / ε + 1 := hcard

theorem dpos_zero (n k : ℕ) (x : DSite n k) :
    dpos n k x 0 = spacing n * ((x.1 : ℕ) : ℝ) - boxL k / 2 := by
  simp [dpos]

theorem dpos_one (n k : ℕ) (x : DSite n k) :
    dpos n k x 1 = spacing n * ((x.2 : ℕ) : ℝ) - boxL k / 2 := by
  simp [dpos]

theorem spacing_le_one (n : ℕ) : spacing n ≤ 1 := by
  unfold spacing
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem riemann_bound (f : Plane → ℝ) {M R : ℝ} (hM : ∀ p, |f p| ≤ M) (hR : 0 ≤ R)
    (hsupp : ∀ p, f p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R) (n k : ℕ) (a : Plane) :
    spacing n ^ 2 * ∑ x : DSite n k, |f (dpos n k x - a)| ≤ M * (2 * R + 1) ^ 2 := by
  have hε : 0 < spacing n := by unfold spacing; positivity
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  set W := (Finset.univ : Finset (DSite n k)).filter
    (fun x => |spacing n * ((x.1 : ℕ) : ℝ) - (boxL k / 2 + a 0)| ≤ R ∧
      |spacing n * ((x.2 : ℕ) : ℝ) - (boxL k / 2 + a 1)| ≤ R) with hW
  have hterm : ∀ x : DSite n k, |f (dpos n k x - a)| ≤ if x ∈ W then M else 0 := by
    intro x
    by_cases hx : f (dpos n k x - a) = 0
    · rw [hx, abs_zero]; split_ifs <;> simp [hM0]
    · obtain ⟨h0, h1⟩ := hsupp _ hx
      have hmem : x ∈ W := by
        simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [PiLp.sub_apply, dpos_zero, dpos_one] at h0 h1
        constructor
        · convert h0 using 2; ring
        · convert h1 using 2; ring
      rw [if_pos hmem]; exact hM _
  have hsum : ∑ x : DSite n k, |f (dpos n k x - a)| ≤ M * W.card := by
    calc ∑ x : DSite n k, |f (dpos n k x - a)|
        ≤ ∑ x : DSite n k, (if x ∈ W then M else 0) := Finset.sum_le_sum fun x _ => hterm x
      _ = M * W.card := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
  have hWcard : (W.card : ℝ) ≤ (2 * R / spacing n + 1) ^ 2 := by
    have hprod : W = ((Finset.univ : Finset (Fin (boxN n k))).filter
          (fun i : Fin (boxN n k) => |spacing n * ((i : ℕ) : ℝ) - (boxL k / 2 + a 0)| ≤ R)) ×ˢ
        ((Finset.univ : Finset (Fin (boxN n k))).filter
          (fun i : Fin (boxN n k) => |spacing n * ((i : ℕ) : ℝ) - (boxL k / 2 + a 1)| ≤ R)) := by
      ext x
      simp only [hW, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    rw [hprod, Finset.card_product, Nat.cast_mul, sq]
    have hpos : (0 : ℝ) ≤ 2 * R / spacing n + 1 := by
      have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hR) hε.le
      linarith
    exact mul_le_mul (card_window (boxN n k) hε (boxL k / 2 + a 0) hR)
      (card_window (boxN n k) hε (boxL k / 2 + a 1) hR) (Nat.cast_nonneg _) hpos
  have hfin : spacing n ^ 2 * (2 * R / spacing n + 1) ^ 2 ≤ (2 * R + 1) ^ 2 := by
    have : spacing n * (2 * R / spacing n + 1) = 2 * R + spacing n := by
      field_simp
    rw [← mul_pow, this]
    have := spacing_le_one n
    apply pow_le_pow_left₀ (by positivity) (by linarith)
  calc spacing n ^ 2 * ∑ x : DSite n k, |f (dpos n k x - a)|
      ≤ spacing n ^ 2 * (M * W.card) := by gcongr
    _ ≤ spacing n ^ 2 * (M * (2 * R / spacing n + 1) ^ 2) := by gcongr
    _ = M * (spacing n ^ 2 * (2 * R / spacing n + 1) ^ 2) := by ring
    _ ≤ M * (2 * R + 1) ^ 2 := by gcongr

/-- A compactly supported Schwartz function is bounded and vanishes outside a sup-norm box. -/
theorem bound_and_box (f : TestFn) (hf : HasCompactSupport ⇑f) :
    ∃ M R : ℝ, 0 ≤ R ∧ (∀ p, |f p| ≤ M) ∧ (∀ p, f p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R) := by
  obtain ⟨M, hM⟩ := hf.exists_bound_of_continuous f.continuous
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, max R 0, le_max_right _ _, fun p => by simpa using hM p, fun p hp => ?_⟩
  have hmem : p ∈ Metric.closedBall (0 : Plane) R := hR (subset_tsupport _ hp)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have h0 : |p 0| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have h1 : |p 1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p 1
  exact ⟨by linarith [le_max_left R 0], by linarith [le_max_left R 0]⟩

theorem conditional_clustering {m₀ lam m C₀ κ : ℝ} (hm : 0 ≤ m) (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ)
    (G : ∀ n k : ℕ, DSite n k → DSite n k → ℝ)
    (hN : ∀ (n k : ℕ) (f g : TestFn),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) g‖
        ≤ κ * ∑ x : DSite n k, ∑ y : DSite n k,
            spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|) * G n k x y)
    (hG : ∀ (n k : ℕ) (x y : DSite n k), 1 ≤ supDist (dpos n k x) (dpos n k y) →
      G n k x y ≤ C₀ * Real.exp (-m * supDist (dpos n k x) (dpos n k y)))
    (hZ : ∀ (n k : ℕ) (f : TestFn), ‖ZD n k m₀ lam (Polynomial.X ^ 4) f‖ ≤ 1) :
    FiniteCutoffClustering m₀ lam m := by
  intro f g hf hg
  obtain ⟨Mf, Rf, hRf, hMf, hsf⟩ := bound_and_box f hf
  obtain ⟨Mg, Rg, hRg, hMg, hsg⟩ := bound_and_box g hg
  set R := max Rf Rg
  have hR : 0 ≤ R := le_max_of_le_left hRf
  have hsf' : ∀ p, f p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R := fun p hp =>
    ⟨(hsf p hp).1.trans (le_max_left _ _), (hsf p hp).2.trans (le_max_left _ _)⟩
  have hsg' : ∀ p, g p ≠ 0 → |p 0| ≤ R ∧ |p 1| ≤ R := fun p hp =>
    ⟨(hsg p hp).1.trans (le_max_right _ _), (hsg p hp).2.trans (le_max_right _ _)⟩
  have hMf0 : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf 0)
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hMg 0)
  set A := Mf * (2 * R + 1) ^ 2 * (Mg * (2 * R + 1) ^ 2)
  refine ⟨max (2 * Real.exp (m * (2 * R + 1))) (κ * (C₀ * Real.exp (m * (2 * R)) * A)),
    fun n k a => ?_⟩
  set D := max |a 0| |a 1|
  have hexp_pos : 0 < Real.exp (-m * D) := Real.exp_pos _
  by_cases hsmall : D ≤ 2 * R + 1
  · -- small shift: both products have norm ≤ 1
    have h1 : ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + translate a g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) (translate a g)‖
        ≤ 2 := by
      calc _ ≤ ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + translate a g)‖
            + ‖ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4)
              (translate a g)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 * 1 := by
          rw [norm_mul]
          gcongr
          · exact hZ _ _ _
          · exact hZ _ _ _
          · exact hZ _ _ _
        _ = 2 := by norm_num
    have h2 : 2 ≤ 2 * Real.exp (m * (2 * R + 1)) * Real.exp (-m * D) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 0 ≤ m * (2 * R + 1) + -m * D := by nlinarith
      have := Real.one_le_exp this
      linarith
    calc _ ≤ 2 := h1
      _ ≤ 2 * Real.exp (m * (2 * R + 1)) * Real.exp (-m * D) := h2
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at hsmall
    have hbound := hN n k f (translate a g)
    -- each term of the double sum is bounded
    have hterm : ∀ x y : DSite n k,
        spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |(translate a g) (dpos n k y)|)
          * G n k x y
        ≤ spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y - a)|)
          * (C₀ * Real.exp (m * (2 * R)) * Real.exp (-m * D)) := by
      intro x y
      have htr : (translate a g) (dpos n k y) = g (dpos n k y - a) := by
        simp [translate, SchwartzMap.compSubConstCLM_apply]
      rw [htr]
      by_cases hfx : f (dpos n k x) = 0
      · simp [hfx]
      by_cases hgy : g (dpos n k y - a) = 0
      · simp [hgy]
      obtain ⟨hx0, hx1⟩ := hsf' _ hfx
      obtain ⟨hy0, hy1⟩ := hsg' _ hgy
      simp only [PiLp.sub_apply] at hy0 hy1
      have hdist : D - 2 * R ≤ supDist (dpos n k x) (dpos n k y) := by
        unfold supDist
        rcases le_total |a 0| |a 1| with h | h
        · have : D = |a 1| := max_eq_right h
          rw [this]
          have := abs_sub_abs_le_abs_sub (dpos n k y 1 - dpos n k x 1) (a 1)
          have h3 : |dpos n k x 1 - dpos n k y 1| = |dpos n k y 1 - dpos n k x 1| := abs_sub_comm _ _
          have h4 : |a 1| ≤ |dpos n k y 1 - a 1| + |dpos n k x 1| + |dpos n k x 1 - dpos n k y 1| := by
            have := abs_add_three (a 1 - dpos n k y 1) (dpos n k x 1) (dpos n k y 1 - dpos n k x 1)
            rw [abs_sub_comm (a 1) (dpos n k y 1), h3] at *
            convert this using 2; ring
          exact le_trans (by linarith) (le_max_right _ _)
        · have : D = |a 0| := max_eq_left h
          rw [this]
          have h3 : |dpos n k x 0 - dpos n k y 0| = |dpos n k y 0 - dpos n k x 0| := abs_sub_comm _ _
          have h4 : |a 0| ≤ |dpos n k y 0 - a 0| + |dpos n k x 0| + |dpos n k x 0 - dpos n k y 0| := by
            have := abs_add_three (a 0 - dpos n k y 0) (dpos n k x 0) (dpos n k y 0 - dpos n k x 0)
            rw [abs_sub_comm (a 0) (dpos n k y 0), h3] at *
            convert this using 2; ring
          exact le_trans (by linarith) (le_max_left _ _)
      have hfar : 1 ≤ supDist (dpos n k x) (dpos n k y) := by linarith
      have hGxy := hG n k x y hfar
      have hexp : Real.exp (-m * supDist (dpos n k x) (dpos n k y))
          ≤ Real.exp (m * (2 * R)) * Real.exp (-m * D) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hnn : 0 ≤ spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y - a)|) := by
        positivity
      calc _ ≤ spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y - a)|)
            * (C₀ * Real.exp (-m * supDist (dpos n k x) (dpos n k y))) :=
            mul_le_mul_of_nonneg_left hGxy hnn
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ hnn
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hexp hC₀
    have hsumf := riemann_bound (fun p => f p) hMf hR hsf' n k 0
    have hsumg := riemann_bound (fun p => g p) hMg hR hsg' n k a
    simp only [sub_zero] at hsumf
    have hdouble : ∑ x : DSite n k, ∑ y : DSite n k,
        spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y - a)|)
          * (C₀ * Real.exp (m * (2 * R)) * Real.exp (-m * D))
        = (spacing n ^ 2 * ∑ x : DSite n k, |f (dpos n k x)|)
          * (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)|)
          * (C₀ * Real.exp (m * (2 * R)) * Real.exp (-m * D)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
    have hK : 0 ≤ C₀ * Real.exp (m * (2 * R)) * Real.exp (-m * D) := by positivity
    calc _ ≤ _ := hbound
      _ ≤ κ * ∑ x : DSite n k, ∑ y : DSite n k,
            spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y - a)|)
              * (C₀ * Real.exp (m * (2 * R)) * Real.exp (-m * D)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y) hκ
      _ = κ * ((spacing n ^ 2 * ∑ x : DSite n k, |f (dpos n k x)|)
          * (spacing n ^ 2 * ∑ y : DSite n k, |g (dpos n k y - a)|)
          * (C₀ * Real.exp (m * (2 * R)) * Real.exp (-m * D))) := by rw [hdouble]
      _ ≤ κ * ((Mf * (2 * R + 1) ^ 2) * (Mg * (2 * R + 1) ^ 2)
            * (C₀ * Real.exp (m * (2 * R)) * Real.exp (-m * D))) := by
          gcongr
      _ = κ * (C₀ * Real.exp (m * (2 * R)) * A) * Real.exp (-m * D) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end PP2Target

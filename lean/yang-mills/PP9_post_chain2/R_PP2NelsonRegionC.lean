import LongTable.R_PP2NelsonRegionB

/-!
Part C of PP2NelsonRegion (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2NelsonRegion.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* §3 Region Wick defect b_B(y) = freeVar − ε⁻² regionGreen B y y:
  `nr_region_two_mul_sub_quad_le` (2w(a) − ⟨w, regionOp w⟩ ≤ regionGreen a a),
  `nr_specVar_le_regionVar` (the sub-box trial field of `fv2_specVar_le_dirVar`, supported in
  subBox M y ⊆ B), **`nr_region_defect_le`**: Fits M y ∧ subBox M y ⊆ B ⇒
  b_B(y) ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))); `nr_region_defect_nonneg` (b_B ≥ b ≥ 0, domain
  monotonicity); `nr_cs_eq` (c₁ = b_B + ε⁻² ∫_{(T,∞)} p^B_t(y,y) dt), `nr_tail_int_nonneg`,
  `nr_tail_int_le` (≤ (π/4)(log(1/T) + m₀⁻²), from `mg_regionHeat_diag_le`), `nr_cs_bounds`.
* §4 Geometry of B = physBall x l (l ≥ 0): `nr_mem_physBall_iff` (B = lattice rectangle
  |u_i − x_i| ≤ R), `nr_physBall_eq` (B = s₁ ×ˢ s₂, `nr_s1`), the region distance
  M_B(y) = min_i min(y_i − (x_i − R), min(N − 1, x_i + R) − y_i) (`nr_d1`, `nr_M`), `nr_fits`,
  `nr_subBox_sub` (subBox M_B(y) y fits the box and lies in B), `nr_sum_anti`,
  `nr_sum_anti_inj`, `nr_sum1`, `nr_s1_card` (|s_i| ≤ 2R + 1), `nr_eps_Q_le` (ε(2R+1) ≤ 2l + 1),
  `nr_card_le` (ε²|B| ≤ (2l+1)²), **`nr_sum_f_M`**: ε² Σ_{y∈B} (ε(M_B(y)+1))^{−1/2}
  ≤ 8 (2l+1)^{3/2} uniformly in n, k, x (the log divergence of b_B at ∂B is square-summable).
* §5 **`nr_smoothHyp`**: m₀ ≠ 0 → 0 ≤ l → nr_SmoothHyp m₀ l (a = A₀L² + 8A₁L^{3/2}, b = A₂L²,
  L = 2l + 1, A_i as in `nl_smoothHyp`); **`nl_nelsonRegion_of_roughL2`**: m₀ ≠ 0 → 0 ≤ l →
  nr_RoughL2Hyp m₀ l hm → nl_NelsonRegion m₀ l.

NOT formalized (what remains): step 3 for regions, `nr_RoughL2Hyp m₀ l hm`:
  ∃ K θ, 0 < θ ∧ ∀ n k x, ∀ T ∈ (0, 1], E_{γ^B⊗γ^B}[R_T²] ≤ K T^θ  (B = physBall n k x l).
  Same ingredients as the box (PP2Nelson header): factorisation of E over the product; Wick
  covariance of φ_r at its true variances, E[:φ_r(y)^a: :φ_r(y')^b:] = δ_ab a! C^B_r(y,y')^a, with
  E[φ_r(y) φ_r(y')] = (M diag(1 − e^{−τλ}) Mᵀ)(y,y') = C^B_r(T)(y,y') (`mg_region_rough_cov`;
  the Gaussian second moments themselves are not stated); misordered smooth covariances bounded by
  K(1 + c₁(y))^j(1 + c₁(y'))^j; summation with `mg_regionRough_Lp_le` (ε² Σ_{y'∈B} |C^B_r|^m
  ≤ K_m T) and ε² Σ_{y∈B} (1 + c₁(y))^6 ≤ K(1 + |log T|)^6 (from `nr_cs_bounds`, `nr_sum_f_M`-type
  sums). The case l < 0 (B = ∅, trivial) is excluded from `nr_smoothHyp` for convenience.
  Optimal constants.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory Real Finset Matrix

open scoped ENNReal

set_option maxHeartbeats 400000

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2NelsonRegion

open PP2Target PP2Nelson

section Defect

variable {n k : ℕ}

/-- **Region smooth Wick constant bounds:** if the odd sub-box of half-width M centred at y fits
the box and lies in B (0 < T ≤ 1, m₀ ≠ 0):
0 ≤ c₁(T)(y) ≤ (π/4)(1 + log⁺(1/(|m₀| ε (M+1)))) + (π/4)(log(1/T) + m₀⁻²). -/
theorem nr_cs_bounds {m₀ : ℝ} (hm : m₀ ≠ 0) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {B : Finset (DSite n k)} {M : ℕ} {y : DSite n k} (hfit : fv2_Fits M y)
    (hsub : fv2_subBox M y ⊆ B) (hy : y ∈ B) :
    0 ≤ nr_cs n k m₀ T B ⟨y, hy⟩ ∧ nr_cs n k m₀ T B ⟨y, hy⟩ ≤
      π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((M : ℝ) + 1))))) +
        π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) := by
  rw [nr_cs_eq hm hT.le B ⟨y, hy⟩]
  have h1 := nr_region_defect_nonneg hm B ⟨y, hy⟩
  have h2 := nr_region_defect_le hm hfit hsub hy
  have h3 := nr_tail_int_nonneg m₀ hT.le B ⟨y, hy⟩
  have h4 := nr_tail_int_le hm hT hT1 B ⟨y, hy⟩
  constructor <;> linarith

end Defect

/-! ## 4. Geometry of the ball B = physBall x l: the lattice rectangle and the region distance -/

section Geometry

variable {n k : ℕ}

/-- The lattice radius R = ⌊l/ε⌋ of the ball. -/
def nr_rad (n : ℕ) (l : ℝ) : ℕ := ⌊l / spacing n⌋₊

theorem nr_sub_le_iff (a b : ℕ) {t : ℝ} (ht : 0 ≤ t) : (a : ℝ) - b ≤ t ↔ a ≤ b + ⌊t⌋₊ := by
  by_cases hab : b ≤ a
  · have e : ((a - b : ℕ) : ℝ) = (a : ℝ) - b := by rw [Nat.cast_sub hab]
    rw [← e, ← Nat.le_floor_iff ht]
    omega
  · push Not at hab
    have : (a : ℝ) - b < 0 := by
      have : (a : ℝ) < b := by exact_mod_cast hab
      linarith
    constructor <;> intro _ <;> [omega; linarith]

theorem nr_coord_iff {l : ℝ} (hl : 0 ≤ l) (a b : ℕ) :
    spacing n * |(a : ℝ) - b| ≤ l ↔ a ≤ b + nr_rad n l ∧ b ≤ a + nr_rad n l := by
  have hε := spacing_pos n
  have ht : 0 ≤ l / spacing n := div_nonneg hl hε.le
  rw [mul_comm, ← le_div_iff₀ hε, abs_le, nr_rad, ← nr_sub_le_iff a b ht, ← nr_sub_le_iff b a ht]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- **The ball is a lattice rectangle:** u ∈ physBall x l ↔ |u_i − x_i| ≤ R (i = 1, 2), l ≥ 0. -/
theorem nr_mem_physBall_iff {l : ℝ} (hl : 0 ≤ l) {x u : DSite n k} :
    u ∈ physBall n k x l ↔ ((u.1 : ℕ) ≤ x.1 + nr_rad n l ∧ (x.1 : ℕ) ≤ u.1 + nr_rad n l) ∧
      ((u.2 : ℕ) ≤ x.2 + nr_rad n l ∧ (x.2 : ℕ) ≤ u.2 + nr_rad n l) := by
  rw [mem_physBall]
  unfold supDist
  rw [dpos_zero, dpos_zero, dpos_one, dpos_one]
  have e1 : spacing n * ((x.1 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((u.1 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((u.1 : ℕ) : ℝ) - ((x.1 : ℕ) : ℝ)) * (-1) := by ring
  have e2 : spacing n * ((x.2 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((u.2 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((u.2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) * (-1) := by ring
  rw [e1, e2]
  simp only [abs_mul, abs_neg, abs_one, mul_one, abs_of_pos (spacing_pos n)]
  rw [max_le_iff, nr_coord_iff hl, nr_coord_iff hl]

/-- 1-D distance of j to the ends of the interval [c − R, min(N − 1, c + R)]. -/
def nr_d1 (N c R j : ℕ) : ℕ := min (j - (c - R)) (min (N - 1) (c + R) - j)

/-- The region distance M_B(y) of y to ∂B (in lattice units) for the rectangle B = physBall x l. -/
def nr_M (n k : ℕ) (x : DSite n k) (R : ℕ) (y : DSite n k) : ℕ :=
  min (nr_d1 (boxN n k) x.1 R y.1) (nr_d1 (boxN n k) x.2 R y.2)

theorem nr_fits {l : ℝ} (hl : 0 ≤ l) {x y : DSite n k} (hy : y ∈ physBall n k x l) :
    fv2_Fits (nr_M n k x (nr_rad n l) y) y := by
  rw [nr_mem_physBall_iff hl] at hy
  have h1 := y.1.isLt
  have h2 := y.2.isLt
  unfold fv2_Fits nr_M nr_d1
  omega

theorem nr_subBox_sub {l : ℝ} (hl : 0 ≤ l) {x y : DSite n k} (hy : y ∈ physBall n k x l) :
    fv2_subBox (nr_M n k x (nr_rad n l) y) y ⊆ physBall n k x l := by
  intro u hu
  simp only [fv2_subBox, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rw [nr_mem_physBall_iff hl] at hy ⊢
  have h1 := y.1.isLt
  have h2 := y.2.isLt
  unfold nr_M nr_d1 at hu
  omega

/-- Σ_{j∈S} f(j) ≤ Σ_{i<|S|} f(i) for antitone f and S ⊆ ℕ finite. -/
theorem nr_sum_anti (f : ℕ → ℝ) (hf : Antitone f) (S : Finset ℕ) :
    ∑ j ∈ S, f j ≤ ∑ i ∈ range S.card, f i := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [sum_insert hna, card_insert_of_notMem hna, sum_range_succ]
    have hsub : s ⊆ range a := fun x hx => mem_range.mpr (ha x hx)
    have hcard : s.card ≤ a := (card_le_card hsub).trans (card_range a).le
    have := hf hcard
    linarith

/-- The same over an injective image. -/
theorem nr_sum_anti_inj {α : Type*} [DecidableEq α] (f : ℕ → ℝ) (hf : Antitone f) (s : Finset α)
    (φ : α → ℕ) (hφ : Set.InjOn φ s) :
    ∑ a ∈ s, f (φ a) ≤ ∑ i ∈ range s.card, f i := by
  rw [← sum_image (g := φ) (f := f) hφ, ← card_image_of_injOn hφ]
  exact nr_sum_anti f hf _

/-- The 1-D coordinate set {a < N : |a − c| ≤ R}. -/
def nr_s1 (N c R : ℕ) : Finset (Fin N) := univ.filter fun a => (a : ℕ) ≤ c + R ∧ c ≤ a + R

theorem nr_s1_card (N c R : ℕ) : (nr_s1 N c R).card ≤ 2 * R + 1 := by
  have h := card_le_card_of_injOn (s := nr_s1 N c R) (t := Finset.Icc (c - R) (c + R))
    (fun a : Fin N => (a : ℕ))
    (fun a ha => by
      have ha' : (a : ℕ) ≤ c + R ∧ c ≤ a + R := by simpa [nr_s1] using ha
      show (a : ℕ) ∈ (Finset.Icc (c - R) (c + R) : Set ℕ)
      rw [Finset.mem_coe, Finset.mem_Icc]
      omega)
    (fun a _ b _ h => Fin.ext h)
  rw [Nat.card_Icc] at h
  omega

theorem nr_anti_f (n : ℕ) : Antitone (nl_f n) := fun _ _ h => nl_f_anti n h

/-- 1-D sum: Σ_{a ∈ s} f(d₁(a)) ≤ 2 Σ_{i<|s|} f(i). -/
theorem nr_sum1 (n N c R : ℕ) :
    ∑ a ∈ nr_s1 N c R, nl_f n (nr_d1 N c R a) ≤ 2 * ∑ i ∈ range (nr_s1 N c R).card, nl_f n i := by
  have hmem : ∀ a ∈ nr_s1 N c R, (a : ℕ) ≤ c + R ∧ c ≤ a + R := by
    intro a ha; simpa [nr_s1] using ha
  calc ∑ a ∈ nr_s1 N c R, nl_f n (nr_d1 N c R a)
      ≤ ∑ a ∈ nr_s1 N c R, (nl_f n ((a : ℕ) - (c - R)) + nl_f n (min (N - 1) (c + R) - a)) :=
        sum_le_sum fun a _ => nl_f_min n _ _
    _ = ∑ a ∈ nr_s1 N c R, nl_f n ((a : ℕ) - (c - R)) +
          ∑ a ∈ nr_s1 N c R, nl_f n (min (N - 1) (c + R) - a) := sum_add_distrib
    _ ≤ ∑ i ∈ range (nr_s1 N c R).card, nl_f n i + ∑ i ∈ range (nr_s1 N c R).card, nl_f n i := by
        gcongr
        · exact nr_sum_anti_inj _ (nr_anti_f n) (nr_s1 N c R) (fun a : Fin N => (a : ℕ) - (c - R))
            (fun a ha b hb h => by
              have := hmem a (Finset.mem_coe.mp ha); have := hmem b (Finset.mem_coe.mp hb)
              exact Fin.ext (by simp only at h; omega))
        · exact nr_sum_anti_inj _ (nr_anti_f n) (nr_s1 N c R)
            (fun a : Fin N => min (N - 1) (c + R) - (a : ℕ))
            (fun a ha b hb h => by
              have := hmem a (Finset.mem_coe.mp ha); have := hmem b (Finset.mem_coe.mp hb)
              have := a.isLt; have := b.isLt
              exact Fin.ext (by simp only at h; omega))
    _ = _ := by ring

theorem nr_physBall_eq {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    physBall n k x l = nr_s1 (boxN n k) x.1 (nr_rad n l) ×ˢ nr_s1 (boxN n k) x.2 (nr_rad n l) := by
  ext u
  rw [nr_mem_physBall_iff hl, mem_product]
  simp [nr_s1]

theorem nr_spacing_le_one (n : ℕ) : spacing n ≤ 1 := by
  unfold spacing
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- ε (2R + 1) ≤ 2l + 1. -/
theorem nr_eps_Q_le {l : ℝ} (hl : 0 ≤ l) :
    spacing n * (2 * (nr_rad n l : ℝ) + 1) ≤ 2 * l + 1 := by
  have hε := spacing_pos n
  have hR : (nr_rad n l : ℝ) ≤ l / spacing n := Nat.floor_le (div_nonneg hl hε.le)
  have h1 : spacing n * (nr_rad n l : ℝ) ≤ l := by
    rw [le_div_iff₀ hε] at hR; linarith
  have := nr_spacing_le_one n
  nlinarith

/-- **Lattice volume of the ball:** ε² |B| ≤ (2l + 1)². -/
theorem nr_card_le {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    spacing n ^ 2 * ((physBall n k x l).card : ℝ) ≤ (2 * l + 1) ^ 2 := by
  have hε := spacing_pos n
  set Q : ℝ := 2 * (nr_rad n l : ℝ) + 1 with hQ
  have hc : ((physBall n k x l).card : ℝ) ≤ Q * Q := by
    rw [nr_physBall_eq hl, card_product]
    have h1 := nr_s1_card (boxN n k) x.1 (nr_rad n l)
    have h2 := nr_s1_card (boxN n k) x.2 (nr_rad n l)
    have h1' : ((nr_s1 (boxN n k) x.1 (nr_rad n l)).card : ℝ) ≤ Q := by
      rw [hQ]; exact_mod_cast h1
    have h2' : ((nr_s1 (boxN n k) x.2 (nr_rad n l)).card : ℝ) ≤ Q := by
      rw [hQ]; exact_mod_cast h2
    push_cast
    exact mul_le_mul h1' h2' (by positivity) (by positivity)
  have hQe := nr_eps_Q_le (n := n) hl
  calc spacing n ^ 2 * ((physBall n k x l).card : ℝ) ≤ spacing n ^ 2 * (Q * Q) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (spacing n * Q) ^ 2 := by ring
    _ ≤ (2 * l + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hQe 2

/-- **Lattice sum of the region boundary singularity:** ε² Σ_{y∈B} (ε(M_B(y)+1))^{−1/2}
≤ 8 (2l+1)^{3/2}, uniformly in n, k, x (B = physBall x l, l ≥ 0). -/
theorem nr_sum_f_M {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    spacing n ^ 2 * ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x (nr_rad n l) y) ≤
      8 * ((2 * l + 1) * √(2 * l + 1)) := by
  have hε := spacing_pos n
  set R := nr_rad n l with hRdef
  set s1 := nr_s1 (boxN n k) x.1 R with hs1
  set s2 := nr_s1 (boxN n k) x.2 R with hs2
  set Q : ℝ := 2 * (R : ℝ) + 1 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hc1 : (s1.card : ℝ) ≤ Q := by rw [hQ]; exact_mod_cast nr_s1_card _ _ _
  have hc2 : (s2.card : ℝ) ≤ Q := by rw [hQ]; exact_mod_cast nr_s1_card _ _ _
  have hS : ∀ s : Finset (Fin (boxN n k)), (s.card : ℝ) ≤ Q →
      ∑ i ∈ range s.card, nl_f n i ≤ (√(spacing n))⁻¹ * (2 * √Q) := by
    intro s hs
    refine (nl_sum_f_le n s.card).trans ?_
    gcongr
  have hT1 := nr_sum1 n (boxN n k) x.1 R
  have hT2 := nr_sum1 n (boxN n k) x.2 R
  have hsum : ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x R y) ≤
      (s2.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        (s1.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) := by
    rw [nr_physBall_eq hl]
    calc ∑ y ∈ s1 ×ˢ s2, nl_f n (nr_M n k x R y)
        ≤ ∑ y ∈ s1 ×ˢ s2, (nl_f n (nr_d1 (boxN n k) x.1 R y.1) +
            nl_f n (nr_d1 (boxN n k) x.2 R y.2)) := sum_le_sum fun y _ => nl_f_min n _ _
      _ = (s2.card : ℝ) * ∑ a ∈ s1, nl_f n (nr_d1 (boxN n k) x.1 R a) +
            (s1.card : ℝ) * ∑ b ∈ s2, nl_f n (nr_d1 (boxN n k) x.2 R b) := by
          rw [sum_add_distrib, sum_product, sum_product_right]
          simp only [sum_const, nsmul_eq_mul, mul_sum]
      _ ≤ _ := by
          gcongr
          · exact hT1.trans (by gcongr; exact hS s1 hc1)
          · exact hT2.trans (by gcongr; exact hS s2 hc2)
  have hsε : 0 < √(spacing n) := Real.sqrt_pos.mpr hε
  have hQe := nr_eps_Q_le (n := n) hl
  have hkey : spacing n ^ 2 * ((s2.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        (s1.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) ≤
      spacing n ^ 2 * (Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) := by
    gcongr
  have heq : spacing n ^ 2 * (Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        Q * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) =
      8 * ((spacing n * Q) * √(spacing n * Q)) := by
    rw [Real.sqrt_mul hε.le]
    have hεs : spacing n = √(spacing n) * √(spacing n) := (mul_self_sqrt hε.le).symm
    set t := √(spacing n)
    rw [hεs]
    field_simp
    ring
  have hmono : (spacing n * Q) * √(spacing n * Q) ≤ (2 * l + 1) * √(2 * l + 1) :=
    mul_le_mul hQe (Real.sqrt_le_sqrt hQe) (Real.sqrt_nonneg _) (by linarith)
  calc spacing n ^ 2 * ∑ y ∈ physBall n k x l, nl_f n (nr_M n k x R y)
      ≤ spacing n ^ 2 * ((s2.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q))) +
        (s1.card : ℝ) * (2 * ((√(spacing n))⁻¹ * (2 * √Q)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := hkey
    _ = _ := heq
    _ ≤ 8 * ((2 * l + 1) * √(2 * l + 1)) := by linarith

end Geometry

/-! ## 5. Discharging the region smooth-constant hypothesis (m₀ ≠ 0, l ≥ 0) -/

section Smooth

/-- **The region smooth-constant hypothesis holds for every m₀ ≠ 0 and l ≥ 0:**
6 ε² Σ_{y∈B} c₁(T)(y)² ≤ a + b (log T)², uniformly in n, k, x (B = physBall n k x l), with
a = A₀ L² + 8 A₁ L^{3/2}, b = A₂ L², L = 2l + 1. -/
theorem nr_smoothHyp {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) : nr_SmoothHyp m₀ l := by
  set P : ℝ := (π / 4) ^ 2 with hP
  set m' : ℝ := (√|m₀|)⁻¹ with hm'
  set L := 2 * l + 1 with hLdef
  have hP0 : 0 ≤ P := by positivity
  have hm'0 : 0 ≤ m' := by positivity
  have hm2 : 0 < m₀ ^ 2 := by positivity
  have hL0 : 0 ≤ L := by linarith
  set A₀ : ℝ := P * (408 + 24 * ((m₀ ^ 2)⁻¹) ^ 2) with hA₀
  set A₁ : ℝ := P * 384 * m' with hA₁
  set A₂ : ℝ := 24 * P with hA₂
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨A₀ * L ^ 2 + A₁ * (8 * (L * √L)), A₂ * L ^ 2, by positivity,
    fun n k x T hT hT1 => ?_⟩
  set B := physBall n k x l with hB
  set R := nr_rad n l with hR
  have hpt : ∀ y : {z // z ∈ B}, 6 * nr_cs n k m₀ T B y ^ 2 ≤
      A₀ + A₁ * nl_f n (nr_M n k x R y) + A₂ * Real.log T ^ 2 := by
    intro y
    have h01 : 0 ≤ nr_cs n k m₀ T B y ∧ nr_cs n k m₀ T B y ≤
        π / 4 * (1 + Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1))))) +
          π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) :=
      nr_cs_bounds hm hT hT1 (nr_fits hl y.2) (nr_subBox_sub hl y.2) y.2
    obtain ⟨h0, h1⟩ := h01
    set ℓ := Real.posLog (1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1)))) with hℓ
    have hℓ0 : 0 ≤ ℓ := Real.posLog_nonneg
    have hx : √(1 / (|m₀| * (spacing n * ((nr_M n k x R y : ℝ) + 1)))) =
        m' * nl_f n (nr_M n k x R y) := by
      rw [nl_f, one_div, Real.sqrt_inv, Real.sqrt_mul (abs_nonneg _), mul_inv]
    have hℓ2 : ℓ ^ 2 ≤ 16 * (1 + m' * nl_f n (nr_M n k x R y)) := by
      rw [← hx]
      exact nl_posLog_sq_le (by have := spacing_pos n; positivity)
    set Bq := π / 4 * (1 + ℓ) with hBq
    set E := π / 4 * (-Real.log T + (m₀ ^ 2)⁻¹) with hE
    have hlogT : Real.log T ≤ 0 := Real.log_nonpos hT.le hT1
    have hE0 : 0 ≤ E := mul_nonneg (by positivity) (by have := inv_pos.mpr hm2; linarith)
    have hB0 : 0 ≤ Bq := by positivity
    have hc2 : nr_cs n k m₀ T B y ^ 2 ≤ 2 * Bq ^ 2 + 2 * E ^ 2 := by
      have : nr_cs n k m₀ T B y ^ 2 ≤ (Bq + E) ^ 2 := pow_le_pow_left₀ h0 h1 2
      nlinarith [sq_nonneg (Bq - E)]
    have hB2 : Bq ^ 2 ≤ P * (34 + 32 * (m' * nl_f n (nr_M n k x R y))) := by
      have h11 : (1 + ℓ) ^ 2 ≤ 2 * (1 + ℓ ^ 2) := by nlinarith [sq_nonneg (ℓ - 1)]
      calc Bq ^ 2 = P * (1 + ℓ) ^ 2 := by rw [hBq, hP]; ring
        _ ≤ P * (2 * (1 + ℓ ^ 2)) := mul_le_mul_of_nonneg_left h11 hP0
        _ ≤ P * (34 + 32 * (m' * nl_f n (nr_M n k x R y))) := by
            apply mul_le_mul_of_nonneg_left _ hP0; linarith
    have hE2 : E ^ 2 ≤ P * (2 * (((m₀ ^ 2)⁻¹) ^ 2 + Real.log T ^ 2)) := by
      calc E ^ 2 = P * (-Real.log T + (m₀ ^ 2)⁻¹) ^ 2 := by rw [hE, hP]; ring
        _ ≤ P * (2 * (((m₀ ^ 2)⁻¹) ^ 2 + Real.log T ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hP0
            nlinarith [sq_nonneg (Real.log T + (m₀ ^ 2)⁻¹)]
    rw [hA₀, hA₁, hA₂]
    nlinarith
  have hε := spacing_pos n
  have hcard : spacing n ^ 2 * (B.card : ℝ) ≤ L ^ 2 := nr_card_le hl x
  have hfs : spacing n ^ 2 * ∑ y ∈ B, nl_f n (nr_M n k x R y) ≤ 8 * (L * √L) := nr_sum_f_M hl x
  have hsc : ∑ y : {z // z ∈ B}, nl_f n (nr_M n k x R y) = ∑ y ∈ B, nl_f n (nr_M n k x R y) :=
    Finset.sum_coe_sort B (fun y => nl_f n (nr_M n k x R y))
  have hsplit : ∑ y : {z // z ∈ B}, (A₀ + A₁ * nl_f n (nr_M n k x R y) + A₂ * Real.log T ^ 2) =
      A₀ * (B.card : ℝ) + A₁ * ∑ y ∈ B, nl_f n (nr_M n k x R y) +
        A₂ * (B.card : ℝ) * Real.log T ^ 2 := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, card_univ,
      Fintype.card_coe, nsmul_eq_mul, nsmul_eq_mul, ← mul_sum, hsc]
    ring
  unfold nr_D
  calc 6 * spacing n ^ 2 * ∑ y : {z // z ∈ B}, nr_cs n k m₀ T B y ^ 2
      = spacing n ^ 2 * ∑ y : {z // z ∈ B}, 6 * nr_cs n k m₀ T B y ^ 2 := by
        rw [← mul_sum]; ring
    _ ≤ spacing n ^ 2 * ∑ y : {z // z ∈ B},
          (A₀ + A₁ * nl_f n (nr_M n k x R y) + A₂ * Real.log T ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => hpt y) (by positivity)
    _ = A₀ * (spacing n ^ 2 * (B.card : ℝ)) +
          A₁ * (spacing n ^ 2 * ∑ y ∈ B, nl_f n (nr_M n k x R y)) +
          A₂ * (spacing n ^ 2 * (B.card : ℝ)) * Real.log T ^ 2 := by
        rw [hsplit]; ring
    _ ≤ A₀ * L ^ 2 + A₁ * (8 * (L * √L)) + A₂ * L ^ 2 * Real.log T ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_left hcard hA₀0
        have h2 := mul_le_mul_of_nonneg_left hfs hA₁0
        have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA₂0)
          (sq_nonneg (Real.log T))
        linarith

/-- **Reduction (G4, region): for m₀ ≠ 0 and l ≥ 0, the region rough L² bound alone implies
Nelson's bound for the free region measures of the balls B = physBall n k x l.** -/
theorem nl_nelsonRegion_of_roughL2 {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l)
    (hL2 : nr_RoughL2Hyp m₀ l hm) : nl_NelsonRegion m₀ l :=
  nr_nelsonRegion_of_hyps hm l (nr_smoothHyp hm hl) hL2

end Smooth

end PP2NelsonRegion

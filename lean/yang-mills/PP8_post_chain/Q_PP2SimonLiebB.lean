import LongTable.Q_PP2SimonLiebA

/-!
Part B of PP2SimonLieb (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb.lean)

FORMALIZED in this part here (no sorry; axioms propext, Classical.choice, Quot.sound).
* `integral_decoupled`: ∫ G(φ|_B) · decWeight_B φ = (∫_{ℝ^B} G(zeroExt ψ) dweight(zeroExt ψ)) ·
  (∫_{ℝ^{Bᶜ}} dweight(zeroExtC η)), with no integrability hypothesis (zero-coupling factorisation).
* `decoupled_twoPt`: the decoupled two-point function of the B-fields is `regionTwoPt B`
  (given that the complement partition function is ≠ 0).
* `twoPt_eq_decoupled`: twoPt x y = ⟨φ_x φ_y Φ⟩_dec / ⟨Φ⟩_dec (BFS (6.2)).
* `iterate_bound`, `geom_le_exp` (abstract Simon iteration), `m6Consumer : M6Consumer`, and
  `clustering_of_simonLieb`: with Newman's inequality (H1 of `conditional_clustering`, with
  G = twoPt) and |ZD| ≤ 1, the four inputs above give `FiniteCutoffClustering m₀ λ m` for some m > 0.

NOT formalized: (R2)–(R5); Griffiths I for region measures (`RegionGriffithsI`, node M2's argument
applies verbatim on ℝ^B); twoPt = regionTwoPt univ; positivity of partition functions.
A FINDING for M6/M5: BFS §7 says "successive iterations of (7.3) and (7.4) imply exponential
decay". The iteration ends on a two-point function at short distance, whose only a-priori bound is
⟨φ²⟩ ~ (2π)⁻¹ log(1/ε) (Wick ordering does not remove it from ⟨φ_x φ_x⟩). So an ε-uniform decay
bound needs, besides (7.4), a uniform bound K on twoPt at physical distance ≥ 1 (`UniformBaseBound`);
we did not find one stated in the passages of BFS we read. `m6Consumer` makes it an explicit hypothesis. It is not a consequence of
(7.4) at all scales: at scales r ≪ 1 the boundary sum is ≈ 1, not < 1 (heuristically; for the
free field it is the exit probability of a walk killed at rate ≈ ε²m₀²/4 per step).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Matrix Finset

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-- **Zero-coupling factorisation.** For any G, the decoupled integral of G(φ|_B) factors into the
region-B integral and the complement partition function. No integrability is needed. -/
theorem integral_decoupled (m₀ lam : ℝ) (P : Polynomial ℝ) (B : Finset (DSite n k))
    (G : DField n k → ℝ) :
    ∫ φ : DField n k, G (restrictIn B φ) * decWeight n k m₀ lam P B φ =
      (∫ ψ : {x // x ∈ B} → ℝ, G (zeroExt B ψ) * dweight n k m₀ lam P (zeroExt B ψ)) *
        ∫ η : {x // x ∉ B} → ℝ, dweight n k m₀ lam P (zeroExtC B η) := by
  have hmp : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : DSite n k => ℝ)
      (fun x => x ∈ B)) volume volume := by
    convert volume_preserving_piEquivPiSubtypeProd (fun _ : DSite n k => ℝ) (fun x => x ∈ B)
  rw [← (hmp.symm _).integral_comp']
  simp only [decWeight, restrictIn_symm, restrictOut_symm]
  rw [Measure.volume_eq_prod, ← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [mul_assoc]

/-- **The Dirichlet measure on B is the zero-coupling marginal:** the decoupled two-point
function of the B-fields is `regionTwoPt B`. -/
theorem decoupled_twoPt (m₀ lam : ℝ) (B : Finset (DSite n k))
    (hZc : ∫ η : {x // x ∉ B} → ℝ, qweight n k m₀ lam (zeroExtC B η) ≠ 0) (x u : DSite n k) :
    (∫ φ : DField n k, restrictIn B φ x * restrictIn B φ u
        * decWeight n k m₀ lam (Polynomial.X ^ 4) B φ) /
      (∫ φ : DField n k, decWeight n k m₀ lam (Polynomial.X ^ 4) B φ)
      = regionTwoPt n k m₀ lam B x u := by
  have h1 := integral_decoupled m₀ lam (Polynomial.X ^ 4) B (fun φ => φ x * φ u)
  have h2 := integral_decoupled m₀ lam (Polynomial.X ^ 4) B (fun _ => 1)
  simp only [one_mul] at h2
  rw [h1, h2, regionTwoPt, mul_div_mul_right _ _ hZc]

/-- **BFS (6.2):** the box two-point function is the decoupled expectation of φ_x φ_y Φ, divided
by that of Φ = exp(Σ_{u∈B, v∉B} J_uv φ_u φ_v). -/
theorem twoPt_eq_decoupled (m₀ lam : ℝ) (B : Finset (DSite n k)) (x y : DSite n k) :
    twoPt n k m₀ lam x y =
      (∫ φ : DField n k, φ x * φ y *
          (decWeight n k m₀ lam (Polynomial.X ^ 4) B φ * Real.exp (bdryCoupling B φ))) /
        ∫ φ : DField n k,
          decWeight n k m₀ lam (Polynomial.X ^ 4) B φ * Real.exp (bdryCoupling B φ) := by
  set c := Real.exp (lam * spacing n ^ 2 * ((Fintype.card (DSite n k) : ℝ) *
    wickPoly (Polynomial.X ^ 4) (freeVar n m₀) 0)) with hc
  have hc0 : c ≠ 0 := (Real.exp_pos _).ne'
  have e1 : ∀ φ : DField n k, φ x * φ y * qweight n k m₀ lam φ =
      (φ x * φ y * (decWeight n k m₀ lam (Polynomial.X ^ 4) B φ
        * Real.exp (bdryCoupling B φ))) * c := by
    intro φ; rw [qweight, dweight_split m₀ lam _ B φ]; ring
  have e2 : ∀ φ : DField n k, qweight n k m₀ lam φ =
      (decWeight n k m₀ lam (Polynomial.X ^ 4) B φ * Real.exp (bdryCoupling B φ)) * c := by
    intro φ; rw [qweight, dweight_split m₀ lam _ B φ]
  rw [twoPt]
  simp_rw [e1, e2]
  rw [integral_mul_const, integral_mul_const, mul_div_mul_right _ _ hc0]

/-! ## The consumer: node M6 (Simon's iteration) -/

/-- The sites within physical sup-norm distance l of x. -/
def physBall (n k : ℕ) (x : DSite n k) (l : ℝ) : Finset (DSite n k) :=
  Finset.univ.filter fun u => supDist (dpos n k x) (dpos n k u) ≤ l

/-- **Input from node M5** (BFS (7.4)): the Simon–Lieb boundary sum of the ball of radius l is at
most γ, uniformly in the level, the volume and the centre. -/
def SmallBoundarySum (m₀ lam l γ : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k),
    ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
      bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u ≤ γ

/-- **Input from node M2:** Griffiths I for the region measures. -/
def RegionGriffithsI (m₀ lam : ℝ) : Prop :=
  ∀ (n k : ℕ) (B : Finset (DSite n k)) (x u : DSite n k), 0 ≤ regionTwoPt n k m₀ lam B x u

/-- **A further input** (not stated as a separate hypothesis in the passages of BFS we read;
UNPROVEN here and not a consequence of `SmallBoundarySum`): the two-point function is bounded at physical
distance ≥ 1, uniformly in the level and the volume. -/
def UniformBaseBound (m₀ lam K : ℝ) : Prop :=
  ∀ (n k : ℕ) (x y : DSite n k), 1 ≤ supDist (dpos n k x) (dpos n k y) →
    twoPt n k m₀ lam x y ≤ K

/-- The conclusion: hypothesis hG of `conditional_clustering`, with G = twoPt. -/
def UniformTwoPointDecay (m₀ lam C₀ m : ℝ) : Prop :=
  ∀ (n k : ℕ) (x y : DSite n k), 1 ≤ supDist (dpos n k x) (dpos n k y) →
    twoPt n k m₀ lam x y ≤ C₀ * Real.exp (-m * supDist (dpos n k x) (dpos n k y))

/-- **The M6 consumer**, as a proposition (proved below as `m6Consumer`). -/
def M6Consumer : Prop :=
  ∀ m₀ lam l γ K : ℝ, 0 ≤ l → 0 < γ → γ < 1 → 0 ≤ K →
    SimonLiebIneq m₀ lam → RegionGriffithsI m₀ lam → SmallBoundarySum m₀ lam l γ →
      UniformBaseBound m₀ lam K →
        ∃ C₀ m : ℝ, 0 ≤ C₀ ∧ 0 < m ∧ UniformTwoPointDecay m₀ lam C₀ m

/-- Abstract Simon iteration: a step inequality with total weight ≤ γ and range ≤ L, iterated N
times from a base bound K at distance ≥ D₀. -/
theorem iterate_bound {X : Type*} [Fintype X] (T d W : X → X → ℝ) {γ K L D₀ : ℝ}
    (hK : 0 ≤ K) (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hW0 : ∀ x v, 0 ≤ W x v) (hWsum : ∀ x, ∑ v, W x v ≤ γ)
    (hWloc : ∀ x v y, W x v ≠ 0 → d x y ≤ L + d v y)
    (hstep : ∀ x y, D₀ + L ≤ d x y → T x y ≤ ∑ v, W x v * T v y)
    (hbase : ∀ x y, D₀ ≤ d x y → T x y ≤ K) :
    ∀ N : ℕ, ∀ x y, D₀ + N * L ≤ d x y → T x y ≤ K * γ ^ N := by
  intro N
  induction N with
  | zero => intro x y h; simpa using hbase x y (by simpa using h)
  | succ N ih =>
    intro x y h
    push_cast at h
    have hNL : 0 ≤ (N : ℝ) * L := mul_nonneg (Nat.cast_nonneg N) hL
    have hN : D₀ + L ≤ d x y := by nlinarith
    calc T x y ≤ ∑ v, W x v * T v y := hstep x y hN
      _ ≤ ∑ v, W x v * (K * γ ^ N) := by
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : W x v = 0
        · simp [hv]
        · apply mul_le_mul_of_nonneg_left _ (hW0 x v)
          apply ih
          have := hWloc x v y hv
          nlinarith
      _ = (∑ v, W x v) * (K * γ ^ N) := by rw [Finset.sum_mul]
      _ ≤ γ * (K * γ ^ N) := mul_le_mul_of_nonneg_right (hWsum x) (by positivity)
      _ = K * γ ^ (N + 1) := by ring

/-- Geometric decay in steps of length L is exponential decay. -/
theorem geom_le_exp {γ L D₀ K t b : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hL : 0 < L) (hK : 0 ≤ K)
    (ht : D₀ ≤ t) (hbd : ∀ N : ℕ, D₀ + N * L ≤ t → b ≤ K * γ ^ N) :
    b ≤ K * Real.exp (-Real.log γ * (D₀ / L + 1)) * Real.exp (-(-Real.log γ / L) * t) := by
  set N := ⌊(t - D₀) / L⌋₊ with hNdef
  have hq : 0 ≤ (t - D₀) / L := div_nonneg (by linarith) hL.le
  have hN1 : (N : ℝ) ≤ (t - D₀) / L := Nat.floor_le hq
  have hN2 : (t - D₀) / L < N + 1 := Nat.lt_floor_add_one _
  have hNL : D₀ + N * L ≤ t := by
    have := (le_div_iff₀ hL).mp hN1; linarith
  have hlog : Real.log γ < 0 := Real.log_neg hγ0 hγ1
  have hpow : γ ^ N = Real.exp (N * Real.log γ) := by
    rw [Real.exp_nat_mul, Real.exp_log hγ0]
  have hle : (N : ℝ) * Real.log γ ≤ ((t - D₀) / L - 1) * Real.log γ :=
    mul_le_mul_of_nonpos_right (by linarith) hlog.le
  have heq : ((t - D₀) / L - 1) * Real.log γ =
      -Real.log γ * (D₀ / L + 1) + -(-Real.log γ / L) * t := by
    field_simp; ring
  calc b ≤ K * γ ^ N := hbd N hNL
    _ = K * Real.exp (N * Real.log γ) := by rw [hpow]
    _ ≤ K * Real.exp (((t - D₀) / L - 1) * Real.log γ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hK
    _ = _ := by rw [heq, Real.exp_add, mul_assoc]

theorem mem_physBall {x u : DSite n k} {l : ℝ} :
    u ∈ physBall n k x l ↔ supDist (dpos n k x) (dpos n k u) ≤ l := by
  simp [physBall]

/-- **The M6 consumer holds:** Simon–Lieb, Griffiths I for regions, the M5 boundary-sum bound and
a uniform base bound give ε- and volume-uniform exponential decay of the two-point function. -/
theorem m6Consumer : M6Consumer := by
  intro m₀ lam l γ K hl hγ0 hγ1 hK hSL hGI hSmall hBase
  refine ⟨K * Real.exp (-Real.log γ * (1 / (l + 1) + 1)), -Real.log γ / (l + 1),
    by positivity, div_pos (neg_pos.mpr (Real.log_neg hγ0 hγ1)) (by linarith), ?_⟩
  intro n k x y hxy
  set d : DSite n k → DSite n k → ℝ := fun a b => supDist (dpos n k a) (dpos n k b) with hd
  set W : DSite n k → DSite n k → ℝ := fun a v =>
    if v ∈ (physBall n k a l)ᶜ then
      ∑ u ∈ physBall n k a l, bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k a l) a u
    else 0 with hW
  have hW0 : ∀ a v, 0 ≤ W a v := by
    intro a v
    simp only [hW]
    split_ifs with hv
    · refine Finset.sum_nonneg fun u hu => mul_nonneg (bondJ_nonneg ?_) (hGI _ _ _ _ _)
      rintro rfl; exact (Finset.mem_compl.mp hv) hu
    · exact le_refl _
  have hWsum : ∀ a, ∑ v, W a v ≤ γ := by
    intro a
    simp only [hW]
    rw [Fintype.sum_ite_mem, Finset.sum_comm]
    exact hSmall n k a
  have hWloc : ∀ a v b, W a v ≠ 0 → d a b ≤ (l + 1) + d v b := by
    intro a v b hv
    simp only [hW] at hv
    split_ifs at hv with hvc
    · obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hJ : bondJ n k u v ≠ 0 := left_ne_zero_of_mul hne
      have h1 : d a u ≤ l := mem_physBall.mp hu
      have h2 : d u v ≤ 1 := (supDist_bondJ hJ).trans (spacing_le_one n)
      have t1 := supDist_triangle (dpos n k a) (dpos n k u) (dpos n k v)
      have t2 := supDist_triangle (dpos n k a) (dpos n k v) (dpos n k b)
      simp only [hd] at h1 h2 ⊢
      linarith
    · exact absurd rfl hv
  have hstep : ∀ a b, 1 + (l + 1) ≤ d a b →
      twoPt n k m₀ lam a b ≤ ∑ v, W a v * twoPt n k m₀ lam v b := by
    intro a b hab
    have ha : a ∈ physBall n k a l := mem_physBall.mpr (by rw [supDist_self]; exact hl)
    have hb : b ∉ physBall n k a l := by
      rw [mem_physBall]; simp only [hd] at hab; linarith
    refine (hSL n k _ a b ha hb).trans (le_of_eq ?_)
    simp only [hW, ite_mul, zero_mul]
    rw [Fintype.sum_ite_mem, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
  have hbase : ∀ a b, 1 ≤ d a b → twoPt n k m₀ lam a b ≤ K := fun a b h => hBase n k a b h
  have hit := iterate_bound (twoPt n k m₀ lam) d W hK hγ0.le (by linarith) hW0 hWsum hWloc
    hstep hbase
  exact geom_le_exp hγ0 hγ1 (by linarith) hK hxy (fun N hN => hit N x y hN)

/-- **End-to-end conditional:** the inputs of the M6 consumer, Newman's inequality (H1 of
`conditional_clustering`, with G = twoPt) and |ZD| ≤ 1 give finite-cutoff clustering. -/
theorem clustering_of_simonLieb {m₀ lam l γ K κ : ℝ} (hl : 0 ≤ l) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hSL : SimonLiebIneq m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hBase : UniformBaseBound m₀ lam K)
    (hN : ∀ (n k : ℕ) (f g : TestFn),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) g‖
        ≤ κ * ∑ x : DSite n k, ∑ y : DSite n k,
            spacing n ^ 2 * |f (dpos n k x)| * (spacing n ^ 2 * |g (dpos n k y)|)
              * twoPt n k m₀ lam x y)
    (hZ : ∀ (n k : ℕ) (f : TestFn), ‖ZD n k m₀ lam (Polynomial.X ^ 4) f‖ ≤ 1) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m := by
  obtain ⟨C₀, m, hC₀, hm, hdecay⟩ := m6Consumer m₀ lam l γ K hl hγ0 hγ1 hK hSL hGI hSmall hBase
  exact ⟨m, hm, conditional_clustering hm.le hC₀ hκ (fun n k => twoPt n k m₀ lam) hN hdecay hZ⟩

end PP2Target

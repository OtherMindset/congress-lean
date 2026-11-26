import LongTable.Q_PP2Limit
import LongTable.P_mwwjem7m_lg69pp

/-!
Part A of PP2Limit2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Limit2.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route). Node M8, session 2:
uniform equicontinuity of the Dirichlet-box generating functionals `ZD` from a uniform two-point
(susceptibility) bound, which closes the hypothesis `UniformEquicont` of
`exists_limitPoint_of_equicont` (PP2Limit) modulo that bound.
Notation: ε = spacing n, w = quartic dweight, Z = ∫ w, ⟨F⟩ = ∫ F w / Z, h(x) = h(dpos n k x).

FORMALIZED (λ ≥ 0, m₀ ≠ 0 where stated).
* `abs_moment_le_sqrt` (Cauchy–Schwarz against the Gibbs weight): ⟨|φ(h)|⟩ ≤ ⟨φ(h)²⟩^{1/2},
  via 0 ≤ ⟨(|φ(h)| − s)²⟩ at s = ⟨|φ(h)|⟩; `sqMoment` = ⟨φ(h)²⟩, `integrable_dsmear_sq_mul`.
* `sqMoment_eq`: ⟨φ(h)²⟩ = ε⁴ Σ_x Σ_y h(x) h(y) twoPt x y.
* `UniformSusceptibility m₀ λ K`: ∀ n k x, ε² Σ_y |twoPt x y| ≤ K.
  `sqMoment_le`: if |h| ≤ M then ⟨φ(h)²⟩ ≤ K · M · ε² Σ_x |h(x)|.
* `twoPt_nonneg` (Griffiths I, from `dexpect_mono_nonneg`, no hypotheses).
  `uniformSusceptibility_of_smearedDecay`: for m > 0, `UniformSmearedDecay m₀ λ C₀ m` (PP2M6Smeared)
  implies `UniformSusceptibility m₀ λ (C₀ / (1 − e^{−m}))`: apply the smeared decay with
  w_j = 1 on the unit sup-norm shell {y : ⌊|dpos x − dpos y|_∞⌋ = j}, D = j, sum the shells
  (they partition the finite box) and use Σ_j C₀ e^{−mj} ≤ C₀/(1 − e^{−m}); |·| is dropped by
  Griffiths I; C₀ ≥ 0 follows from the hypothesis with w ≡ 0.
* `oneD_bound`: 0 < ε ≤ 1 ⇒ ε Σ_{i<N} (1 + |εi − c|)^{−2} ≤ 8 (unit shells, two windows of
  width 1 each, `card_window`, and Σ_j (1+j)^{−2} ≤ 2 by `sum_inv_sq_le`).
* `schwartz_decay4`: (1 + ‖p‖)⁴ |h(p)| ≤ 16 ‖h‖_{4,0} (`one_add_le_sup_seminorm_apply`), where
  ‖·‖_{4,0} = `schwartzSup 4 0`; `abs_le_schwartzSup`: |h(p)| ≤ 16 ‖h‖_{4,0}.
* `riemann_schwartz` (Riemann bound without compact support): ε² Σ_x |h(dpos x)| ≤ 1024 ‖h‖_{4,0},
  uniformly in n, k; via (1+|p₀|)²(1+|p₁|)² ≤ (1+‖p‖)⁴, the sum factorises into two `oneD_bound`s.
  (Seminorm index 4, not 3: the product/shell argument needs the extra power; any fixed index
  suffices for `UniformEquicont`.)
* `uniformEquicont_of_susceptibility`: `UniformSusceptibility m₀ λ K` ⇒ `UniformEquicont m₀ λ`
  with (a, b) = (4, 0), C = 128 · (max K 0)^{1/2}:
    ‖ZD f − ZD g‖ ≤ ⟨|φ(h)|⟩ ≤ ⟨φ(h)²⟩^{1/2} ≤ (K · 16‖h‖ · 1024‖h‖)^{1/2} = 128 √K ‖h‖_{4,0}.
* `exists_limitPoint_of_smearedDecay`: m > 0, `UniformSmearedDecay m₀ λ C₀ m` and
  `SchwartzSeparable` ⇒ ∃ Z, IsLimitPoint m₀ λ Z. `exists_limitPoint_of_simonLieb'`: the same from
  the hypotheses of `m6Consumer'` (Simon–Lieb with local term, region Griffiths I, small boundary
  sum, region susceptibility).

NOT formalized.
* The analytic inputs themselves: `UniformSmearedDecay` / `UniformSusceptibility` (equivalently the
  M6 hypotheses SimonLiebIneq', RegionGriffithsI, SmallBoundarySum, RegionSusceptibility at weak
  coupling), and `SchwartzSeparable` (true, not in this Mathlib).
* Non-Gaussianity, invariance and OS axioms of the limit points.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
open MeasureTheory Filter Topology

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## Part 1: Cauchy–Schwarz and the second moment -/

theorem prod_single_pow (φ : DField n k) (x : DSite n k) :
    ∏ z, φ z ^ (Pi.single x 1 : DSite n k → ℕ) z = φ x := by
  rw [Finset.prod_eq_single x (fun y _ hy => by simp [hy])
    (fun hx => absurd (Finset.mem_univ x) hx)]
  simp

theorem integrable_pair_mul {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (x y : DSite n k) :
    Integrable fun φ : DField n k => φ x * φ y * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  refine (PP2Griffiths.integrable_mono_dweight hm hlam
    ((Pi.single x 1 : DSite n k → ℕ) + Pi.single y 1)).congr (Eventually.of_forall fun φ => ?_)
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_single_pow]

/-- The second moment ⟨φ(h)²⟩ of the smeared field. -/
def sqMoment (n k : ℕ) (m₀ lam : ℝ) (h : TestFn) : ℝ :=
  (∫ φ : DField n k, dsmear n k h φ ^ 2 * dweight n k m₀ lam (Polynomial.X ^ 4) φ) /
    ∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ

theorem dsmear_sq_mul (h : TestFn) (w : ℝ) (φ : DField n k) :
    dsmear n k h φ ^ 2 * w = ∑ x : DSite n k, ∑ y : DSite n k,
      spacing n ^ 4 * (h (dpos n k x) * h (dpos n k y)) * (φ x * φ y * w) := by
  unfold dsmear
  rw [sq, mul_mul_mul_comm, ← sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem integrable_dsmear_sq_mul {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : TestFn) :
    Integrable fun φ : DField n k =>
      dsmear n k h φ ^ 2 * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  simp_rw [dsmear_sq_mul]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_pair_mul hm hlam x y).const_mul _

/-- **Expansion of the second moment**: ⟨φ(h)²⟩ = ε⁴ Σ_x Σ_y h(x) h(y) ⟨φ_x φ_y⟩. -/
theorem sqMoment_eq {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (h : TestFn) :
    sqMoment n k m₀ lam h = spacing n ^ 4 * ∑ x : DSite n k, ∑ y : DSite n k,
      h (dpos n k x) * h (dpos n k y) * twoPt n k m₀ lam x y := by
  unfold sqMoment twoPt
  simp_rw [dsmear_sq_mul]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_pair_mul hm hlam x y).const_mul _]
  simp_rw [integral_finsetSum _ fun y _ => (integrable_pair_mul hm hlam _ y).const_mul _,
    integral_const_mul]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [qweight]
  ring

/-- **Cauchy–Schwarz against the Gibbs measure**: ⟨|φ(h)|⟩ ≤ ⟨φ(h)²⟩^{1/2}. -/
theorem abs_moment_le_sqrt {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) (h : TestFn) :
    (∫ φ : DField n k, |dsmear n k h φ| * dweight n k m₀ lam (Polynomial.X ^ 4) φ)
        / (∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ)
      ≤ Real.sqrt (sqMoment n k m₀ lam h) := by
  set w := dweight n k m₀ lam (Polynomial.X ^ 4) with hw
  set Z := ∫ φ : DField n k, w φ with hZ
  set a := ∫ φ : DField n k, |dsmear n k h φ| * w φ with ha
  set b := ∫ φ : DField n k, dsmear n k h φ ^ 2 * w φ with hb
  have hZpos : 0 < Z := PP2Griffiths.integral_dweight_pos hm hlam
  have hIw : Integrable w := PP2Griffiths.integrable_dweight hm hlam
  have hIa := integrable_abs_dsmear_mul hm hlam n k h
  have hIb := integrable_dsmear_sq_mul hm hlam (n := n) (k := k) h
  have ha0 : 0 ≤ a := integral_nonneg fun φ =>
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  set s := a / Z with hs
  have hquad : 0 ≤ b - 2 * s * a + s ^ 2 * Z := by
    have h0 : 0 ≤ ∫ φ : DField n k, (|dsmear n k h φ| - s) ^ 2 * w φ :=
      integral_nonneg fun φ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hexp : (fun φ : DField n k => (|dsmear n k h φ| - s) ^ 2 * w φ)
        = fun φ => (dsmear n k h φ ^ 2 * w φ - (2 * s) * (|dsmear n k h φ| * w φ))
          + s ^ 2 * w φ := by
      funext φ; rw [← sq_abs (dsmear n k h φ)]; ring
    have hI1 : Integrable fun φ : DField n k =>
        dsmear n k h φ ^ 2 * w φ - (2 * s) * (|dsmear n k h φ| * w φ) :=
      hIb.sub (hIa.const_mul _)
    have hI2 : Integrable fun φ : DField n k => s ^ 2 * w φ := hIw.const_mul _
    have hI3 : Integrable fun φ : DField n k => (2 * s) * (|dsmear n k h φ| * w φ) :=
      hIa.const_mul _
    rw [hexp, integral_add hI1 hI2, integral_sub hIb hI3, integral_const_mul,
      integral_const_mul] at h0
    linarith
  have hsq : s ^ 2 ≤ b / Z := by
    rw [le_div_iff₀ hZpos]
    have : s * a = s ^ 2 * Z := by rw [hs]; field_simp
    nlinarith
  rw [show sqMoment n k m₀ lam h = b / Z from rfl]
  exact Real.le_sqrt_of_sq_le hsq

/-! ## Part 2: the uniform susceptibility bound -/

/-- **Uniform susceptibility**: sup_x ε² Σ_y |⟨φ_x φ_y⟩| ≤ K, uniformly in n, k. -/
def UniformSusceptibility (m₀ lam K : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k), spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y| ≤ K

/-- ⟨φ(h)²⟩ ≤ K · M · ε² Σ_x |h(x)| for |h| ≤ M. -/
theorem sqMoment_le {m₀ : ℝ} (hm : m₀ ≠ 0) {lam K : ℝ} (hlam : 0 ≤ lam)
    (hK : UniformSusceptibility m₀ lam K) (h : TestFn) {M : ℝ} (hM : ∀ p, |h p| ≤ M) :
    sqMoment n k m₀ lam h ≤ K * M * (spacing n ^ 2 * ∑ x : DSite n k, |h (dpos n k x)|) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [sqMoment_eq hm hlam]
  calc spacing n ^ 4 * ∑ x : DSite n k, ∑ y : DSite n k,
        h (dpos n k x) * h (dpos n k y) * twoPt n k m₀ lam x y
      ≤ spacing n ^ 4 * ∑ x : DSite n k, ∑ y : DSite n k,
        |h (dpos n k x)| * M * |twoPt n k m₀ lam x y| := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ =>
          Finset.sum_le_sum fun y _ => ?_) (by positivity)
        calc h (dpos n k x) * h (dpos n k y) * twoPt n k m₀ lam x y
            ≤ |h (dpos n k x) * h (dpos n k y) * twoPt n k m₀ lam x y| := le_abs_self _
          _ = |h (dpos n k x)| * |h (dpos n k y)| * |twoPt n k m₀ lam x y| := by
            rw [abs_mul, abs_mul]
          _ ≤ |h (dpos n k x)| * M * |twoPt n k m₀ lam x y| := by gcongr; exact hM _
    _ = ∑ x : DSite n k, (spacing n ^ 2 * |h (dpos n k x)| * M) *
          (spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y|) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ ≤ ∑ x : DSite n k, (spacing n ^ 2 * |h (dpos n k x)| * M) * K := by
        gcongr with x _
        exact hK n k x
    _ = K * M * (spacing n ^ 2 * ∑ x : DSite n k, |h (dpos n k x)|) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- Griffiths I: ⟨φ_x φ_y⟩ ≥ 0 (no hypotheses; Bochner convention outside λ ≥ 0, m₀ ≠ 0). -/
theorem twoPt_nonneg (m₀ lam : ℝ) (x y : DSite n k) : 0 ≤ twoPt n k m₀ lam x y := by
  set e : DSite n k → ℕ := Pi.single x 1 + Pi.single y 1 with he'
  have h := PP2Griffiths.dexpect_mono_nonneg (n := n) (k := k) m₀ lam e
  have he : (fun φ : DField n k => ∏ z, φ z ^ e z) = fun φ => φ x * φ y := by
    funext φ
    simp only [he', Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_single_pow]
  rw [he] at h
  exact h

/-- **Smeared decay implies uniform susceptibility** (shells of unit sup-norm width:
w_j = 1 on {⌊|x − y|_∞⌋ = j}, D = j, and Σ_j C₀ e^{−mj} ≤ C₀ / (1 − e^{−m})). -/
theorem uniformSusceptibility_of_smearedDecay {m₀ lam C₀ m : ℝ} (hm : 0 < m)
    (hD : UniformSmearedDecay m₀ lam C₀ m) :
    UniformSusceptibility m₀ lam (C₀ / (1 - Real.exp (-m))) := by
  intro n k x
  set d : DSite n k → ℕ := fun y => ⌊supDist (dpos n k x) (dpos n k y)⌋₊ with hd
  set J := (Finset.univ : Finset (DSite n k)).sup d + 1 with hJ
  set W : ℕ → DSite n k → ℝ := fun j y => if d y = j then 1 else 0 with hW
  have hC₀ : 0 ≤ C₀ := by
    have := hD n k x (fun _ => 0) 0 (fun _ => ⟨le_refl _, zero_le_one⟩) (fun y hy => absurd rfl hy)
    simpa using this
  have hshell : ∀ j, spacing n ^ 2 * ∑ y, W j y * twoPt n k m₀ lam x y
      ≤ C₀ * Real.exp (-m * j) := by
    intro j
    refine hD n k x (W j) j (fun y => ?_) (fun y hy => ?_)
    · simp only [hW]; split_ifs <;> norm_num
    · simp only [hW, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hy
      rw [← hy, hd]
      refine Nat.floor_le ?_
      exact le_max_of_le_left (abs_nonneg _)
  have hsumW : ∀ y, ∑ j ∈ Finset.range J, W j y = 1 := by
    intro y
    simp only [hW]
    rw [Finset.sum_ite_eq, if_pos]
    rw [Finset.mem_range, hJ]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := d) (Finset.mem_univ y))
  have hr0 : 0 ≤ Real.exp (-m) := (Real.exp_pos _).le
  have hr1 : Real.exp (-m) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  calc spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y|
      = spacing n ^ 2 * ∑ y, (∑ j ∈ Finset.range J, W j y) * twoPt n k m₀ lam x y := by
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hsumW, one_mul, abs_of_nonneg (twoPt_nonneg _ _ _ _)]
    _ = ∑ j ∈ Finset.range J, spacing n ^ 2 * ∑ y, W j y * twoPt n k m₀ lam x y := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range J, C₀ * Real.exp (-m) ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (hshell j).trans (le_of_eq ?_)
        rw [← Real.exp_nat_mul]; congr 2; ring
    _ = C₀ * ∑ j ∈ Finset.Ico 0 J, Real.exp (-m) ^ j := by
        rw [Finset.mul_sum, Finset.range_eq_Ico]
    _ ≤ C₀ * (Real.exp (-m) ^ 0 / (1 - Real.exp (-m))) := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one hr0 hr1
    _ = C₀ / (1 - Real.exp (-m)) := by rw [pow_zero, mul_one_div]

end PP2Target

end

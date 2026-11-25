import LongTable.PP2Limit
import LongTable.PP2M6Smeared

/-!
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

/-! ## Part 3: Riemann-sum bound for Schwartz functions -/

theorem sum_inv_sq_le (J : ℕ) :
    ∑ j ∈ Finset.range J, 1 / (1 + (j : ℝ)) ^ 2 ≤ 2 - 2 / ((J : ℝ) + 1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have key : 1 / (1 + (J : ℝ)) ^ 2 ≤ 2 / ((J : ℝ) + 1) - 2 / (((J + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- One-dimensional Riemann bound: ε Σ_{i<N} (1 + |εi − c|)^{−2} ≤ 8 (0 < ε ≤ 1). -/
theorem oneD_bound (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) :
    ε * ∑ i : Fin N, 1 / (1 + |ε * ((i : ℕ) : ℝ) - c|) ^ 2 ≤ 8 := by
  set J := N + ⌈|c|⌉₊ + 1 with hJ
  set I1 : ℕ → Fin N → ℝ := fun j i =>
    if |ε * ((i : ℕ) : ℝ) - (c + j + 1 / 2)| ≤ 1 / 2 then 1 else 0 with hI1
  set I2 : ℕ → Fin N → ℝ := fun j i =>
    if |ε * ((i : ℕ) : ℝ) - (c - j - 1 / 2)| ≤ 1 / 2 then 1 else 0 with hI2
  have hI1n : ∀ j i, 0 ≤ I1 j i := fun j i => by simp only [hI1]; split_ifs <;> norm_num
  have hI2n : ∀ j i, 0 ≤ I2 j i := fun j i => by simp only [hI2]; split_ifs <;> norm_num
  have hpt : ∀ i : Fin N, 1 / (1 + |ε * ((i : ℕ) : ℝ) - c|) ^ 2
      ≤ ∑ j ∈ Finset.range J, (I1 j i + I2 j i) * (1 / (1 + (j : ℝ)) ^ 2) := by
    intro i
    set t := |ε * ((i : ℕ) : ℝ) - c| with ht
    set j0 := ⌊t⌋₊ with hj0
    have ht0 : 0 ≤ t := abs_nonneg _
    have hj0t : (j0 : ℝ) ≤ t := Nat.floor_le ht0
    have htj0 : t < j0 + 1 := Nat.lt_floor_add_one t
    have hiN : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    have hj0J : j0 < J := by
      have h1 : t ≤ N + |c| := by
        have hεi : 0 ≤ ε * ((i : ℕ) : ℝ) := by positivity
        have : ε * ((i : ℕ) : ℝ) ≤ N := by nlinarith
        rw [ht]
        calc |ε * ((i : ℕ) : ℝ) - c| ≤ |ε * ((i : ℕ) : ℝ)| + |c| := abs_sub _ _
          _ = ε * ((i : ℕ) : ℝ) + |c| := by rw [abs_of_nonneg hεi]
          _ ≤ N + |c| := by linarith
      have h2 : |c| ≤ (⌈|c|⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (j0 : ℝ) < ((N + ⌈|c|⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h3
    have hind : 1 ≤ I1 j0 i + I2 j0 i := by
      rcases le_or_gt 0 (ε * ((i : ℕ) : ℝ) - c) with hs | hs
      · have : t = ε * ((i : ℕ) : ℝ) - c := abs_of_nonneg hs
        have hin : |ε * ((i : ℕ) : ℝ) - (c + j0 + 1 / 2)| ≤ 1 / 2 := by
          rw [abs_le]; constructor <;> linarith
        have := hI2n j0 i
        simp only [hI1, if_pos hin]; linarith
      · have : t = -(ε * ((i : ℕ) : ℝ) - c) := abs_of_neg hs
        have hin : |ε * ((i : ℕ) : ℝ) - (c - j0 - 1 / 2)| ≤ 1 / 2 := by
          rw [abs_le]; constructor <;> linarith
        have := hI1n j0 i
        simp only [hI2, if_pos hin]; linarith
    have hmono : 1 / (1 + t) ^ 2 ≤ 1 / (1 + (j0 : ℝ)) ^ 2 := by
      gcongr
    calc 1 / (1 + t) ^ 2 ≤ 1 / (1 + (j0 : ℝ)) ^ 2 := hmono
      _ ≤ (I1 j0 i + I2 j0 i) * (1 / (1 + (j0 : ℝ)) ^ 2) := by
        have : 0 ≤ 1 / (1 + (j0 : ℝ)) ^ 2 := by positivity
        nlinarith
      _ ≤ ∑ j ∈ Finset.range J, (I1 j i + I2 j i) * (1 / (1 + (j : ℝ)) ^ 2) :=
        Finset.single_le_sum (f := fun j => (I1 j i + I2 j i) * (1 / (1 + (j : ℝ)) ^ 2))
          (fun j _ => mul_nonneg (add_nonneg (hI1n j i) (hI2n j i)) (by positivity))
          (Finset.mem_range.mpr hj0J)
  have hcard : ∀ j : ℕ, ε * ∑ i : Fin N, (I1 j i + I2 j i) ≤ 4 := by
    intro j
    have hw1 := card_window N hε (c + j + 1 / 2) (R := 1 / 2) (by norm_num)
    have hw2 := card_window N hε (c - j - 1 / 2) (R := 1 / 2) (by norm_num)
    rw [Finset.sum_add_distrib]
    simp only [hI1, hI2, Finset.sum_boole]
    have e1 : 2 * (1 / 2 : ℝ) / ε = 1 / ε := by ring
    rw [e1] at hw1 hw2
    have : ε * (1 / ε + 1) = 1 + ε := by field_simp
    nlinarith
  calc ε * ∑ i : Fin N, 1 / (1 + |ε * ((i : ℕ) : ℝ) - c|) ^ 2
      ≤ ε * ∑ i : Fin N, ∑ j ∈ Finset.range J, (I1 j i + I2 j i) * (1 / (1 + (j : ℝ)) ^ 2) := by
        gcongr with i _
        exact hpt i
    _ = ∑ j ∈ Finset.range J, (ε * ∑ i : Fin N, (I1 j i + I2 j i)) * (1 / (1 + (j : ℝ)) ^ 2) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ∑ j ∈ Finset.range J, 4 * (1 / (1 + (j : ℝ)) ^ 2) := by
        gcongr with j _
        exact hcard j
    _ = 4 * ∑ j ∈ Finset.range J, 1 / (1 + (j : ℝ)) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * (2 - 2 / ((J : ℝ) + 1)) := by gcongr; exact sum_inv_sq_le J
    _ ≤ 8 := by
        have : 0 ≤ 2 / ((J : ℝ) + 1) := by positivity
        linarith

/-- Pointwise Schwartz decay: (1 + ‖p‖)⁴ |h(p)| ≤ 16 ‖h‖_{4,0}. -/
theorem schwartz_decay4 (h : TestFn) (p : Plane) :
    (1 + ‖p‖) ^ 4 * |h p| ≤ 16 * schwartzSup 4 0 h := by
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, 0)) (k := 4) (n := 0)
    le_rfl le_rfl h p
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  convert this using 1
  norm_num [schwartzSup]
  rfl

theorem abs_le_schwartzSup (h : TestFn) (p : Plane) : |h p| ≤ 16 * schwartzSup 4 0 h := by
  have h1 : 1 ≤ (1 + ‖p‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg p])
  have := schwartz_decay4 h p
  nlinarith [abs_nonneg (h p)]

/-- **Riemann-sum bound for Schwartz functions** (no compact support needed):
ε² Σ_x |h(dpos x)| ≤ 1024 ‖h‖_{4,0}, uniformly in n, k. -/
theorem riemann_schwartz (h : TestFn) (n k : ℕ) :
    spacing n ^ 2 * ∑ x : DSite n k, |h (dpos n k x)| ≤ 1024 * schwartzSup 4 0 h := by
  set S := schwartzSup 4 0 h with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hε : 0 < spacing n := by unfold spacing; positivity
  set a : Fin (boxN n k) → ℝ := fun i =>
    1 / (1 + |spacing n * ((i : ℕ) : ℝ) - boxL k / 2|) ^ 2 with ha
  have hpt : ∀ x : DSite n k, |h (dpos n k x)| ≤ 16 * S * (a x.1 * a x.2) := by
    intro x
    set p := dpos n k x
    have h0 : |p 0| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
    have h1 : |p 1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p 1
    have hprod : ((1 + |p 0|) ^ 2 * (1 + |p 1|) ^ 2) ≤ (1 + ‖p‖) ^ 4 := by
      have := mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith : 1 + |p 0| ≤ 1 + ‖p‖) 2)
        (pow_le_pow_left₀ (by positivity) (by linarith : 1 + |p 1| ≤ 1 + ‖p‖) 2)
        (by positivity) (by positivity)
      calc _ ≤ (1 + ‖p‖) ^ 2 * (1 + ‖p‖) ^ 2 := this
        _ = _ := by ring
    have hdec := schwartz_decay4 h p
    have hax : a x.1 * a x.2 = 1 / ((1 + |p 0|) ^ 2 * (1 + |p 1|) ^ 2) := by
      simp only [ha, p, dpos_zero, dpos_one]
      rw [one_div_mul_one_div]
    rw [hax, mul_one_div, le_div_iff₀ (by positivity)]
    calc |h p| * ((1 + |p 0|) ^ 2 * (1 + |p 1|) ^ 2) ≤ |h p| * (1 + ‖p‖) ^ 4 := by
          gcongr
      _ ≤ 16 * S := by rw [mul_comm]; exact hdec
  have h1D : spacing n * ∑ i : Fin (boxN n k), a i ≤ 8 :=
    oneD_bound (boxN n k) hε (spacing_le_one n) (boxL k / 2)
  have ha0 : 0 ≤ spacing n * ∑ i : Fin (boxN n k), a i :=
    mul_nonneg hε.le (Finset.sum_nonneg fun i _ => by positivity)
  calc spacing n ^ 2 * ∑ x : DSite n k, |h (dpos n k x)|
      ≤ spacing n ^ 2 * ∑ x : DSite n k, 16 * S * (a x.1 * a x.2) := by
        gcongr with x _
        exact hpt x
    _ = 16 * S * ((spacing n * ∑ i, a i) * (spacing n * ∑ j, a j)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ 16 * S * (8 * 8) := by gcongr
    _ = 1024 * S := by ring

/-! ## Part 4: uniform susceptibility ⇒ uniform equicontinuity -/

/-- **Equicontinuity from a uniform two-point bound**: with a = 4, b = 0 and
C = 128 · (max K 0)^{1/2}, ‖ZD f − ZD g‖ ≤ C ‖f − g‖_{4,0} uniformly in n, k. -/
theorem uniformEquicont_of_susceptibility {m₀ : ℝ} (hm : m₀ ≠ 0) {lam K : ℝ} (hlam : 0 ≤ lam)
    (hK : UniformSusceptibility m₀ lam K) : UniformEquicont m₀ lam := by
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hK'' : UniformSusceptibility m₀ lam K' := fun n k x => (hK n k x).trans (le_max_left _ _)
  refine ⟨128 * Real.sqrt K', 4, 0, fun n k f g => ?_⟩
  set h := f - g
  set S := schwartzSup 4 0 h with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hmom : sqMoment n k m₀ lam h ≤ K' * (128 * S) ^ 2 := by
    calc sqMoment n k m₀ lam h
        ≤ K' * (16 * S) * (spacing n ^ 2 * ∑ x : DSite n k, |h (dpos n k x)|) :=
          sqMoment_le hm hlam hK'' h (abs_le_schwartzSup h)
      _ ≤ K' * (16 * S) * (1024 * S) := by
          exact mul_le_mul_of_nonneg_left (riemann_schwartz h n k) (by positivity)
      _ = K' * (128 * S) ^ 2 := by ring
  calc ‖ZD n k m₀ lam (Polynomial.X ^ 4) f - ZD n k m₀ lam (Polynomial.X ^ 4) g‖
      ≤ _ := norm_ZD_sub_le hm hlam n k f g
    _ ≤ Real.sqrt (sqMoment n k m₀ lam h) := abs_moment_le_sqrt hm hlam h
    _ ≤ Real.sqrt (K' * (128 * S) ^ 2) := Real.sqrt_le_sqrt hmom
    _ = 128 * Real.sqrt K' * S := by
        rw [Real.sqrt_mul hK'0, Real.sqrt_sq (by positivity)]; ring

/-! ## Corollaries: existence of limit points -/

/-- Uniform smeared decay (m > 0) and Schwartz separability give a limit point. -/
theorem exists_limitPoint_of_smearedDecay {m₀ : ℝ} (hm : m₀ ≠ 0) {lam C₀ m : ℝ} (hlam : 0 ≤ lam)
    (hmpos : 0 < m) (hD : UniformSmearedDecay m₀ lam C₀ m) (hS : SchwartzSeparable) :
    ∃ Z, IsLimitPoint m₀ lam Z :=
  exists_limitPoint_of_equicont
    (uniformEquicont_of_susceptibility hm hlam (uniformSusceptibility_of_smearedDecay hmpos hD)) hS

/-- The same from the hypotheses of the smeared M6 consumer. -/
theorem exists_limitPoint_of_simonLieb' {m₀ : ℝ} (hm : m₀ ≠ 0) {lam l γ A : ℝ} (hlam : 0 ≤ lam)
    (hl : 0 ≤ l) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (hSL : SimonLiebIneq' m₀ lam) (hGI : RegionGriffithsI m₀ lam)
    (hSmall : SmallBoundarySum m₀ lam l γ) (hReg : RegionSusceptibility m₀ lam l A)
    (hS : SchwartzSeparable) : ∃ Z, IsLimitPoint m₀ lam Z := by
  obtain ⟨C₀, m, -, hmpos, hD⟩ :=
    m6Consumer' m₀ lam l γ A hl hγ0 hγ1 hA hSL hGI hSmall hReg
  exact exists_limitPoint_of_smearedDecay hm hlam hmpos hD hS

end PP2Target

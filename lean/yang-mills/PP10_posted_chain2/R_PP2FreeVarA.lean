import LongTable.R_PP2Heat

/-!
Part A of PP2FreeVar (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2FreeVar.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5c, session 1.
The Wick constant `freeVar n m₀` against the Dirichlet site variance (namespace `PP2Target`).

Notation: ε = `spacing n`, μ = m₀²ε² (lattice mass²), w(θ) = `symb μ θ₁ θ₂` =
μ + 4 sin²(θ₁/2) + 4 sin²(θ₂/2), so freeVar = (2π)⁻² ∫∫_{[−π,π]²} 1/w (lattice units, no ε
factor). The Dirichlet site variance is c_D(x) = ε⁻² dirGreen x x (`gauss_cov`); both are in the
same (lattice) units, so the Wick defect is b(x) = freeVar − c_D(x). For a field v on the box,
`trigT v a μ` is the cosine polynomial 2 Re(v̂(θ)e^{−ia·θ}) − w(θ)|v̂(θ)|², v̂(θ) = Σ_y v_y e^{iy·θ}.
For an odd side N = 2M + 1, h = π/(M+1), `midNode M r` = θ_r = (r + ½)h, r = 0..M, and
`specVar N μ i₁ i₂` = Σ_{j₁,j₂<N} e_{j₁}(i₁)² e_{j₂}(i₂)² / (μ + sineEig j₁ + sineEig j₂) is the
spectral site variance of a side-N Dirichlet box (any N, not only `boxN`).

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `integral_cos_int`, `iter_integral_trig`: torus orthogonality, ∫∫ Σ c_i cos(p_i·θ) =
  4π² Σ_{p_i = 0} c_i (p_i ∈ ℤ²).
* `integral_trigT`: ∫∫ trigT v a μ = 4π² (2 v(a) − ε² ⟨v, dirOp v⟩) at μ = m₀²ε² (Parseval for the
  Dirichlet form, via `dirOp_mulVec_apply` and `ext_eq_sum_ind`).
* `trigT_eq`: trigT = 2C − w(C² + S²), C, S = Σ v_y cos/sin((y − a)·θ);
  `two_mul_sub_le_inv`: 2C − w(C² + S²) ≤ 1/w for w > 0.
* `two_mul_sub_dirAction_le_freeVar`: m₀ ≠ 0 → 2 v(a) − dirAction(v) ≤ freeVar, for every v, a
  (variational form; no limit, no larger box).
* `dirVar_le_freeVar` (**goal 1**): m₀ ≠ 0 → ε⁻² dirGreen a a ≤ freeVar, every site a of the box,
  every n, k. So b(x) = freeVar − c_D(x) ≥ 0.
* `dirVar_eq_specVar`: ε⁻² dirGreen a a = specVar (boxN n k) (m₀²ε²) a₁ a₂ (any m₀).
* `sineVec_centre_sq`: for N = 2M + 1, e_j(M)² = 1/(M+1) if j is even (mode j+1 odd), else 0
  (verified: 2/(N+1) = 1/(M+1)).
* `specVar_centre` (**goal 2, identity**): specVar (2M+1) μ M M =
  Σ_{r₁,r₂ ≤ M} (M+1)⁻² / w(θ_{r₁}, θ_{r₂}); since (M+1)⁻² = (h/π)², this is the midpoint rule
  with M+1 cells of width h = 2π/(N+1) on [0, π] for (1/π²)∫∫_{[0,π]²} 1/w.
* `integral_le_midpoint_sum`: f ≥ 0 antitone on [0, π] → ∫_{h/2}^{π} f ≤ h Σ_{r≤M} f(θ_r).
* `inv_symb_anti₁/₂`: 1/w is antitone in each θ_i on [0, π] (μ > 0).
* `specVar_centre_ge`: (1/π²) ∫∫_{[h/2, π]²} 1/w ≤ specVar (2M+1) μ M M (μ > 0).
* `freeVar_eq_quarter`: freeVar = (1/π²) ∫_0^π ∫_0^π 1/w (evenness, m₀ ≠ 0).
* `freeVar_sub_specVar_centre_le` (**goal 2, strip bound**): m₀ ≠ 0 →
  freeVar − specVar (2M+1) (m₀²ε²) M M ≤ (1/π²)(∫_0^{h/2}∫_0^π 1/w + ∫_0^π∫_0^{h/2} 1/w).

NOT formalized here: the explicit estimate of the strip integrals by C(1 + log₊(1/(m₀ε(M+1))))
(needs Jordan sin x ≥ 2x/π and ∫ dθ/(a + bθ²) bounds), the θ₁ ↔ θ₂ swap making the two strips
equal; any link from `specVar (2M+1)` to `dirGreen` (the repo's box has even side 2^(n+k), so the
odd sub-box centred at x is not itself a `DSite` box); domain monotonicity (goal 3:
G_{sub-box} ≤ G_box on the sub-box); hence no bound b(x) ≤ C(1 + log₊(1/(m₀ r))) yet.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset

noncomputable section

namespace PP2Target

/-! ## One-dimensional and iterated integrals of trigonometric monomials -/

/-- ∫_{−π}^{π} cos(c + b t) dt = 2π cos c if b = 0, and 0 otherwise (b ∈ ℤ). -/
theorem integral_cos_int (c : ℝ) (b : ℤ) :
    ∫ t in (-π)..π, cos (c + b * t) = if b = 0 then 2 * π * cos c else 0 := by
  split_ifs with hb
  · subst hb
    simp only [Int.cast_zero, zero_mul, add_zero, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => sin (c + b * t) / b)]
    · have h : c + b * π = (c + b * (-π)) + b * (2 * π) := by ring
      rw [h, Real.sin_add_int_mul_two_pi]
      ring
    · intro t _
      have h1 : HasDerivAt (fun t : ℝ => c + b * t) b t := by
        simpa using ((hasDerivAt_id t).const_mul (b : ℝ)).const_add c
      have h2 := (h1.sin).div_const (b : ℝ)
      convert h2 using 1
      field_simp
    · exact (by fun_prop : Continuous fun t : ℝ => cos (c + b * t)).intervalIntegrable _ _

/-- The phase p·θ = p₁θ₁ + p₂θ₂ of p ∈ ℤ². -/
def phase (p : ℤ × ℤ) (θ₁ θ₂ : ℝ) : ℝ := (p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂

/-- **Orthogonality on the torus**, in iterated form: for a finite real combination of
cos(p_i·θ), ∫∫_{[−π,π]²} Σ c_i cos(p_i·θ) = 4π² Σ_{p_i = 0} c_i. -/
theorem iter_integral_trig {ι : Type*} (s : Finset ι) (c : ι → ℝ) (p : ι → ℤ × ℤ) :
    ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π, ∑ i ∈ s, c i * cos (phase (p i) θ₁ θ₂) =
      4 * π ^ 2 * ∑ i ∈ s, c i * (if p i = 0 then 1 else 0) := by
  have inner : ∀ θ₁ : ℝ, ∫ θ₂ in (-π)..π, ∑ i ∈ s, c i * cos (phase (p i) θ₁ θ₂) =
      ∑ i ∈ s, c i * (2 * π) * (if (p i).2 = 0 then 1 else 0) * cos (0 + (p i).1 * θ₁) := by
    intro θ₁
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_const_mul]
      simp only [phase]
      rw [integral_cos_int, zero_add]
      split_ifs <;> ring
    · intro i _
      exact (by unfold phase; fun_prop :
        Continuous fun θ₂ => c i * cos (phase (p i) θ₁ θ₂)).intervalIntegrable _ _
  simp_rw [inner]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_cos_int, Real.cos_zero]
    by_cases h1 : (p i).1 = 0 <;> by_cases h2 : (p i).2 = 0 <;>
      simp [h1, h2, Prod.ext_iff]
    ring
  · intro i _
    exact (by fun_prop : Continuous fun θ₁ : ℝ =>
      c i * (2 * π) * (if (p i).2 = 0 then 1 else 0) * cos (0 + (p i).1 * θ₁)).intervalIntegrable _ _

theorem phase_add (p q : ℤ × ℤ) (θ₁ θ₂ : ℝ) :
    phase (p + q) θ₁ θ₂ = phase p θ₁ θ₂ + phase q θ₁ θ₂ := by
  simp only [phase, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

theorem phase_sub (p q : ℤ × ℤ) (θ₁ θ₂ : ℝ) :
    phase (p - q) θ₁ θ₂ = phase p θ₁ θ₂ - phase q θ₁ θ₂ := by
  simp only [phase, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]; ring

/-! ## The Dirichlet quadratic form as a torus integral -/

variable {n k : ℕ}

theorem site_injective {x y : DSite n k} (h : site x = site y) : x = y := by
  simp only [site, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem ext_eq_sum_ind (v : DField n k) (q : ℤ × ℤ) :
    ext v q = ∑ z : DSite n k, v z * (if q = site z then 1 else 0) := by
  rw [ext_eq_extVec_dot]
  simp only [dotProduct, extVec_apply]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- The six lattice offsets 0, 0, ±e₁, ±e₂. -/
def offs : Fin 6 → ℤ × ℤ := ![(0, 0), (0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]

/-- The coefficients of the trigonometric polynomial `trigT`. -/
def cfT (v : DField n k) (a : DSite n k) (μ : ℝ) (i : DSite n k × DSite n k × Fin 6) : ℝ :=
  (![2 * v i.1 * (if i.2.1 = a then 1 else 0), -(μ + 4) * v i.1 * v i.2.1, v i.1 * v i.2.1,
    v i.1 * v i.2.1, v i.1 * v i.2.1, v i.1 * v i.2.1] : Fin 6 → ℝ) i.2.2

/-- The frequencies of `trigT`. -/
def ppT (i : DSite n k × DSite n k × Fin 6) : ℤ × ℤ := site i.1 - site i.2.1 + offs i.2.2

/-- The trigonometric polynomial 2 Re(V̂(θ) e^{−ia·θ}) − w(θ)|V̂(θ)|², written out as a finite cosine
sum, with w(θ) = μ + 4 sin²(θ₁/2) + 4 sin²(θ₂/2). -/
def trigT (v : DField n k) (a : DSite n k) (μ θ₁ θ₂ : ℝ) : ℝ :=
  ∑ i : DSite n k × DSite n k × Fin 6, cfT v a μ i * cos (phase (ppT i) θ₁ θ₂)

theorem ite_sub_add_eq_zero (p q o : ℤ × ℤ) :
    (p - q + o = 0) ↔ (p + o = q) := by
  rw [sub_add_eq_add_sub, sub_eq_zero]

/-- **The integral of `trigT`**: (2π)⁻² ∫∫ trigT = 2 v(a) − ε² ⟨v, dirOp v⟩ at μ = m₀²ε². -/
theorem integral_trigT (m₀ : ℝ) (v : DField n k) (a : DSite n k) :
    ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π, trigT v a (m₀ ^ 2 * spacing n ^ 2) θ₁ θ₂ =
      4 * π ^ 2 * (2 * v a - spacing n ^ 2 * (v ⬝ᵥ dirOp n k m₀ *ᵥ v)) := by
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  unfold trigT
  rw [iter_integral_trig]
  congr 1
  have hz : ∀ (y : DSite n k) (o : ℤ × ℤ) (c : ℝ),
      ∑ z : DSite n k, c * v z * (if site y + o = site z then 1 else 0) =
        c * ext v (site y + o) := by
    intro y o c
    rw [ext_eq_sum_ind, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  have h0 : ∀ y : DSite n k, ∑ z : DSite n k,
      2 * v y * (if z = a then 1 else 0) * (if site y + offs 0 = site z then 1 else 0) =
        2 * v y * (if y = a then 1 else 0) := by
    intro y
    simp only [offs, Matrix.cons_val_zero, Prod.mk_zero_zero, add_zero, mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single a]
    · by_cases hy : y = a
      · simp [hy]
      · have : site y ≠ site a := fun h => hy (site_injective h)
        simp [hy, this]
    · intro z _ hz; simp [hz]
    · simp
  have per : ∀ y : DSite n k,
      ∑ q : DSite n k × Fin 6, cfT v a (m₀ ^ 2 * spacing n ^ 2) (y, q) *
          (if ppT (y, q) = 0 then 1 else 0) =
        2 * v y * (if y = a then 1 else 0) - (m₀ ^ 2 * spacing n ^ 2 + 4) * v y * ext v (site y)
          + v y * ext v (site y + (1, 0)) + v y * ext v (site y + (-1, 0))
          + v y * ext v (site y + (0, 1)) + v y * ext v (site y + (0, -1)) := by
    intro y
    rw [Fintype.sum_prod_type (α₁ := DSite n k) (α₂ := Fin 6), Finset.sum_comm]
    simp only [Fin.sum_univ_six, cfT, ppT, ite_sub_add_eq_zero, Matrix.cons_val]
    simp only [h0, hz]
    simp only [offs, Matrix.cons_val]
    have : -(m₀ ^ 2 * spacing n ^ 2 + 4) * v y * ext v (site y + (0, 0)) =
        -((m₀ ^ 2 * spacing n ^ 2 + 4) * v y * ext v (site y)) := by
      rw [Prod.mk_zero_zero, add_zero]; ring
    rw [this, ← sub_eq_add_neg]
  rw [Fintype.sum_prod_type (α₁ := DSite n k) (α₂ := DSite n k × Fin 6)]
  simp only [per]
  have ha : 2 * v a = ∑ y : DSite n k, 2 * v y * (if y = a then 1 else 0) := by
    simp
  rw [ha, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e1 : site y + (1, 0) = ((site y).1 + 1, (site y).2) :=
    Prod.ext (show (site y).1 + 1 = (site y).1 + 1 from rfl) (show (site y).2 + 0 = (site y).2 by ring)
  have e2 : site y + (-1, 0) = ((site y).1 - 1, (site y).2) :=
    Prod.ext (show (site y).1 + -1 = (site y).1 - 1 by ring) (show (site y).2 + 0 = (site y).2 by ring)
  have e3 : site y + (0, 1) = ((site y).1, (site y).2 + 1) :=
    Prod.ext (show (site y).1 + 0 = (site y).1 by ring) (show (site y).2 + 1 = (site y).2 + 1 from rfl)
  have e4 : site y + (0, -1) = ((site y).1, (site y).2 - 1) :=
    Prod.ext (show (site y).1 + 0 = (site y).1 by ring) (show (site y).2 + -1 = (site y).2 - 1 by ring)
  rw [dirOp_mulVec_apply, e1, e2, e3, e4, ext_site]
  have hi : (spacing n ^ 2)⁻¹ * spacing n ^ 2 = 1 := inv_mul_cancel₀ hε
  linear_combination (-(v y * (ext v ((site y).1 + 1, (site y).2) + ext v ((site y).1 - 1, (site y).2)
    + ext v ((site y).1, (site y).2 + 1) + ext v ((site y).1, (site y).2 - 1)) - 4 * v y ^ 2)) * hi

/-- 4 sin²(t/2) = 2 − 2 cos t. -/
theorem four_sin_sq_half (t : ℝ) : 4 * sin (t / 2) ^ 2 = 2 - 2 * cos t := by
  have h := Real.cos_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h
  linear_combination 2 * h + 4 * Real.sin_sq_add_cos_sq (t / 2)

/-- The symbol w(θ) = μ + 4 sin²(θ₁/2) + 4 sin²(θ₂/2) of −Δ + μ on ℤ². -/
def symb (μ θ₁ θ₂ : ℝ) : ℝ := μ + 4 * sin (θ₁ / 2) ^ 2 + 4 * sin (θ₂ / 2) ^ 2

/-- **`trigT` in closed form**: with A_y = (y − a)·θ, C = Σ v_y cos A_y, S = Σ v_y sin A_y,
trigT = 2C − w(θ)(C² + S²). -/
theorem trigT_eq (v : DField n k) (a : DSite n k) (μ θ₁ θ₂ : ℝ) :
    trigT v a μ θ₁ θ₂ =
      2 * (∑ y : DSite n k, v y * cos (phase (site y - site a) θ₁ θ₂))
        - symb μ θ₁ θ₂ * ((∑ y : DSite n k, v y * cos (phase (site y - site a) θ₁ θ₂)) ^ 2
          + (∑ y : DSite n k, v y * sin (phase (site y - site a) θ₁ θ₂)) ^ 2) := by
  set A : DSite n k → ℝ := fun y => phase (site y - site a) θ₁ θ₂ with hA
  have hpp : ∀ y z : DSite n k, ∀ j : Fin 6,
      phase (ppT (y, z, j)) θ₁ θ₂ = A y - A z + phase (offs j) θ₁ θ₂ := by
    intro y z j
    simp only [ppT, hA]
    rw [phase_add, show site y - site z = (site y - site a) - (site z - site a) by abel, phase_sub]
  have hw1 := four_sin_sq_half θ₁
  have hw2 := four_sin_sq_half θ₂
  have key : ∀ y z : DSite n k,
      ∑ j : Fin 6, cfT v a μ (y, z, j) * cos (phase (ppT (y, z, j)) θ₁ θ₂) =
        2 * v y * (if z = a then 1 else 0) * cos (A y - A z)
          - symb μ θ₁ θ₂ * (v y * v z * cos (A y - A z)) := by
    intro y z
    simp only [Fin.sum_univ_six]
    rw [hpp, hpp, hpp, hpp, hpp, hpp]
    simp only [cfT, offs, Matrix.cons_val, phase, symb]
    simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, neg_mul, add_zero,
      zero_add, Real.cos_add, Real.cos_neg, Real.sin_neg]
    rw [hw1, hw2]
    ring
  have hAa : A a = 0 := by simp [hA, phase]
  unfold trigT
  rw [Fintype.sum_prod_type (α₁ := DSite n k) (α₂ := DSite n k × Fin 6)]
  simp only [Fintype.sum_prod_type (α₁ := DSite n k) (α₂ := Fin 6), key]
  simp only [Finset.sum_sub_distrib]
  have h1 : ∀ y : DSite n k, ∑ z : DSite n k, 2 * v y * (if z = a then 1 else 0) * cos (A y - A z)
      = 2 * (v y * cos (A y)) := by
    intro y
    rw [Finset.sum_eq_single a (fun z _ hz => by simp [hz]) (by simp)]
    simp [hAa]; ring
  have h2 : ∑ y : DSite n k, ∑ z : DSite n k, symb μ θ₁ θ₂ * (v y * v z * cos (A y - A z)) =
      symb μ θ₁ θ₂ * ((∑ y, v y * cos (A y)) ^ 2 + (∑ y, v y * sin (A y)) ^ 2) := by
    simp only [← Finset.mul_sum]
    congr 1
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [Real.cos_sub]; ring
  rw [h2, Finset.sum_congr rfl fun y _ => h1 y, ← Finset.mul_sum]

/-- **Pointwise bound**: 2C − w(C² + S²) ≤ 1/w for w > 0. -/
theorem two_mul_sub_le_inv {w C S : ℝ} (hw : 0 < w) : 2 * C - w * (C ^ 2 + S ^ 2) ≤ 1 / w := by
  have h : 1 / w - (2 * C - w * (C ^ 2 + S ^ 2)) = w * (C - 1 / w) ^ 2 + w * S ^ 2 := by
    field_simp; ring
  have : 0 ≤ w * (C - 1 / w) ^ 2 + w * S ^ 2 := by positivity
  linarith

/-- **Variational bound by the infinite-volume variance**: for every field v on the box and every
site a, 2 v(a) − dirAction(v) ≤ freeVar (m₀ ≠ 0). -/
theorem two_mul_sub_dirAction_le_freeVar {m₀ : ℝ} (hm : m₀ ≠ 0) (v : DField n k)
    (a : DSite n k) : 2 * v a - dirAction n k m₀ v ≤ freeVar n m₀ := by
  set μ := m₀ ^ 2 * spacing n ^ 2 with hμdef
  have hμ : 0 < μ := by have := spacing_pos n; positivity
  have hw : ∀ θ₁ θ₂, 0 < symb μ θ₁ θ₂ := fun _ _ => by unfold symb; positivity
  have hT : Continuous (fun q : ℝ × ℝ => trigT v a μ q.1 q.2) := by unfold trigT phase; fun_prop
  have hG : Continuous (fun q : ℝ × ℝ => 1 / symb μ q.1 q.2) :=
    continuous_const.div (by unfold symb; fun_prop) (fun q => (hw _ _).ne')
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  have hle : ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π, trigT v a μ θ₁ θ₂ ≤
      ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π, 1 / symb μ θ₁ θ₂ := by
    apply intervalIntegral.integral_mono_on hpi
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun θ₁ θ₂ => trigT v a μ θ₁ θ₂) hT _ _).intervalIntegrable _ _
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun θ₁ θ₂ => 1 / symb μ θ₁ θ₂) hG _ _).intervalIntegrable _ _
    · intro θ₁ _
      apply intervalIntegral.integral_mono_on hpi
      · exact (hT.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · exact (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · intro θ₂ _
        rw [trigT_eq]
        exact two_mul_sub_le_inv (hw _ _)
  have hI := integral_trigT m₀ v a
  rw [← hμdef] at hI
  have hX : 2 * v a - dirAction n k m₀ v =
      (2 * π)⁻¹ ^ 2 * ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π, trigT v a μ θ₁ θ₂ := by
    rw [hI, dirAction_eq_quad]
    have : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hX, freeVar]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- **Dirichlet ≤ infinite volume.** The site variance of the Dirichlet free field,
c_D(a) = ε⁻² dirGreen a a (`gauss_cov`), is at most the infinite-lattice variance `freeVar`. -/
theorem dirVar_le_freeVar {m₀ : ℝ} (hm : m₀ ≠ 0) (a : DSite n k) :
    (spacing n ^ 2)⁻¹ * dirGreen n k m₀ a a ≤ freeVar n m₀ := by
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  set c := (spacing n ^ 2)⁻¹ with hc
  set v : DField n k := c • (dirGreen n k m₀ *ᵥ Pi.single a 1) with hv
  have hva : v a = c * dirGreen n k m₀ a a := by
    simp [hv]
  have hOv : dirOp n k m₀ *ᵥ v = c • Pi.single a 1 := by
    rw [hv, mulVec_smul, mulVec_mulVec, dirOp_mul_dirGreen hm, one_mulVec]
  have hq : dirAction n k m₀ v = v a := by
    rw [dirAction_eq_quad, hOv, dotProduct_smul, smul_eq_mul]
    have : v ⬝ᵥ Pi.single a 1 = v a := by simp [dotProduct, Pi.single_apply]
    rw [this, hc, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  have h := two_mul_sub_dirAction_le_freeVar hm v a
  rw [hq, hva] at h
  linarith

/-! ## The spectral site variance and the centre of an odd box -/

/-- The spectral site variance of a Dirichlet box of side N in lattice units, at lattice mass²
μ: Σ_{j₁, j₂ < N} e_{j₁}(i₁)² e_{j₂}(i₂)² / (μ + sineEig j₁ + sineEig j₂). -/
def specVar (N : ℕ) (μ : ℝ) (i₁ i₂ : Fin N) : ℝ :=
  ∑ j₁ : Fin N, ∑ j₂ : Fin N,
    sineVec N j₁ i₁ ^ 2 * sineVec N j₂ i₂ ^ 2 / (μ + sineEig N j₁ + sineEig N j₂)

/-- c_D(a) = ε⁻² dirGreen a a is the spectral site variance at μ = m₀²ε². -/
theorem dirVar_eq_specVar (m₀ : ℝ) (a : DSite n k) :
    (spacing n ^ 2)⁻¹ * dirGreen n k m₀ a a = specVar (boxN n k) (m₀ ^ 2 * spacing n ^ 2) a.1 a.2 := by
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  rw [dirGreen_spectral, Finset.mul_sum, specVar, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
  have h1 := sineEig_pos (boxN n k) j₁ j₁.isLt
  have h2 := sineEig_pos (boxN n k) j₂ j₂.isLt
  have hd : 0 < m₀ ^ 2 * spacing n ^ 2 + sineEig (boxN n k) j₁ + sineEig (boxN n k) j₂ := by
    positivity
  simp only [sineVec2, dirEig]
  generalize spacing n ^ 2 = e at *
  have hi : e⁻¹ * e = 1 := inv_mul_cancel₀ hε
  have hD : e⁻¹ * (sineEig (boxN n k) j₁ + sineEig (boxN n k) j₂) + m₀ ^ 2 =
      e⁻¹ * (m₀ ^ 2 * e + sineEig (boxN n k) j₁ + sineEig (boxN n k) j₂) := by
    linear_combination (-m₀ ^ 2) * hi
  rw [hD, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  linear_combination (sineVec (boxN n k) j₁ a.1 * sineVec (boxN n k) j₂ a.2 * (sineVec (boxN n k) j₁ a.1 *
    sineVec (boxN n k) j₂ a.2) * (m₀ ^ 2 * e + sineEig (boxN n k) j₁ + sineEig (boxN n k) j₂)⁻¹) * hi

end PP2Target

end

import LongTable.Q_PP2Griffiths
import LongTable.P_mww4cze7_bk8bxu
import LongTable.P_mww0oo05_8eieqb

/-!
Part A of PP2Griffiths2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2Griffiths2.lean)
Long Table, P(φ)₂ direction, node M2 (session 2): Griffiths' first inequality with
site-dependent weights, and its application to the Dirichlet-box quartic weight `PP2Target.dweight`.

FORMALIZED.
* `PP2Griffiths.integral_nonneg_of_signSum_nonneg_inv`, `griffiths_first_inv`: the sign-flip
  method of session 1 with any nonnegative weight W invariant under all sign flips (not
  necessarily a product).
* `griffiths_first_sites` (and `_general`, `_field`): Griffiths I with site-dependent weights
  w : ι → ℝ → ℝ, each even and ≥ 0, J ≥ 0 entrywise:
    0 ≤ ∫ φ, (∏ x, φ x ^ a x) * exp(Σ_{x,y} J x y φ x φ y) * ∏ x, w x (φ x).
* `wickPoly_X4_neg`: :(−y)⁴:_c = :y⁴:_c.
* The algebraic identity for the Dirichlet action (`dirAction_eq`, `neg_half_dirAction`,
  `coupling_eq`, `diagPart_eq`, `cdiag_eq_four`, `dweight_eq_ferro`, `siteWeight_eq`):
    dweight φ = exp(Σ_{x,y} Jnn x y φ x φ y) · ∏_x w(φ x),
    w(y) = exp(−(4 + ε² m₀²) y²/2 − λ ε² :P:(y)),
  where Jnn x y ≥ 0 (`Jnn_nonneg`) is Σ_p [(p+e₁, p) = (x, y)] + [(p+e₂, p) = (x, y)] over the
  sum index of `dirAction`, i.e. 1 when x = y + e₁ or x = y + e₂ (both in the box), else 0;
  Jnn is one-sided (not symmetric): each unordered nearest-neighbour bond appears once, so the
  symmetrised coupling is ½(Jnn+Jnnᵀ); Griffiths I only needs Jnn ≥ 0. The ε²·ε⁻² cancels
  (`dirAction_eq`). The diagonal coefficient is exactly 4 at every site (Dirichlet boundary:
  every site has 4 box-or-boundary neighbours), so in fact w does not depend on x.
* `griffiths_first_dweight` (via flip-invariance), `griffiths_first_dweight'` (via
  `griffiths_first_sites`), for all n, k, m₀, λ (no sign condition on λ):
    0 ≤ ∫ φ, (∏ x, φ x ^ a x) * dweight n k m₀ λ X⁴ φ;
  `griffiths_first_dweight_of_even`: the same for any P whose Wick polynomial is even.
* `integrable_dweight`, `integral_dweight_pos` (λ ≥ 0, m₀ ≠ 0): the partition function
  ∫ dweight is finite and > 0 (bound by a product of Gaussians, as in #mww0oo05).
* `dexpect_mono_nonneg`: for the normalised expectation `dexpect` (∫ F·dweight / ∫ dweight),
  ⟨∏ φ^a⟩ ≥ 0. Lean states it for all m₀, λ because the integrals are Bochner (0 if not
  integrable), so outside λ ≥ 0, m₀ ≠ 0 it can be the junk value 0/0 = 0. It is meaningful only
  for λ ≥ 0, m₀ ≠ 0, where the denominator is proved finite and > 0 (`integral_dweight_pos`); the
  numerator's integrability is proved in PP2Griffiths3 (`integrable_mono_dweight`).
* Griffiths II, preparation only: `rot` (t, s) ↦ ((t+s)/√2, (t−s)/√2), `rot_rot` (it is an
  involution), `rot_bilin`, `rot_quadForm` (it preserves Σ J t t + Σ J s s); `GriffithsSecond`
  (the statement, as a Prop definition).

NOT formalized.
* Integrability of the moment integrand φ^a · dweight (polynomial times Gaussian); not needed for
  the inequalities (non-integrable ⇒ integral 0), but needed for them to be the genuine ones.
* Griffiths II itself (no proof here; proved in PP2Griffiths3 for every even w ≥ 0 with
  ferromagnetic pair coupling, by the duplicate-variable argument).
* Explicit closed form for `Jnn` as a function of the sites (its value is described above, only
  its nonnegativity and the decomposition are proved).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
open MeasureTheory Finset PP2Target

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2Griffiths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sign averaging with a general sign-flip-invariant nonnegative weight W. -/
theorem integral_nonneg_of_signSum_nonneg_inv {W : (ι → ℝ) → ℝ}
    (hW_inv : ∀ σ φ, W (flipSigns σ φ) = W φ) (hW_nonneg : ∀ φ, 0 ≤ W φ) (f : (ι → ℝ) → ℝ)
    (hf : ∀ φ, 0 ≤ ∑ σ : ι → Bool, f (flipSigns σ φ)) :
    0 ≤ ∫ φ : ι → ℝ, f φ * W φ := by
  set F : (ι → ℝ) → ℝ := fun φ => f φ * W φ with hFdef
  by_cases hint : Integrable F
  · have hcomp : ∀ σ : ι → Bool,
        (fun φ => f (flipSigns σ φ) * W φ) = fun φ => F (flipEquiv σ φ) := by
      intro σ; funext φ
      show _ = f (flipSigns σ φ) * W (flipSigns σ φ)
      rw [hW_inv]
    have hintσ : ∀ σ : ι → Bool, Integrable (fun φ => f (flipSigns σ φ) * W φ) := by
      intro σ; rw [hcomp σ]
      exact (measurePreserving_flipEquiv σ).integrable_comp_of_integrable hint
    have hint_eq : ∀ σ : ι → Bool,
        ∫ φ, f (flipSigns σ φ) * W φ = ∫ φ, F φ := by
      intro σ; rw [hcomp σ]
      exact (measurePreserving_flipEquiv σ).integral_comp' F
    have hsum : ∫ φ : ι → ℝ, (∑ σ : ι → Bool, f (flipSigns σ φ)) * W φ
        = (Fintype.card (ι → Bool) : ℝ) * ∫ φ, F φ := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun σ _ => hintσ σ)]
      simp [hint_eq]
    have hnn : 0 ≤ ∫ φ : ι → ℝ, (∑ σ : ι → Bool, f (flipSigns σ φ)) * W φ :=
      integral_nonneg fun φ => mul_nonneg (hf φ) (hW_nonneg φ)
    rw [hsum] at hnn
    have hcard : (0 : ℝ) < Fintype.card (ι → Bool) := by
      exact_mod_cast Fintype.card_pos
    exact nonneg_of_mul_nonneg_right (by linarith) hcard
  · rw [integral_undef hint]

/-- Griffiths I, general form, with a sign-flip-invariant nonnegative weight. -/
theorem griffiths_first_inv {W : (ι → ℝ) → ℝ}
    (hW_inv : ∀ σ φ, W (flipSigns σ φ) = W φ) (hW_nonneg : ∀ φ, 0 ≤ W φ)
    {g Q : (ι → ℝ) → ℝ} (hg : IsPosPoly g) (hQ : IsPosPoly Q) :
    0 ≤ ∫ φ : ι → ℝ, g φ * Real.exp (Q φ) * W φ :=
  integral_nonneg_of_signSum_nonneg_inv hW_inv hW_nonneg _ (signSum_mul_exp_nonneg hg hQ)

omit [DecidableEq ι] in
lemma prod_sites_flip {w : ι → ℝ → ℝ} (hw : ∀ x y, w x (-y) = w x y) (σ : ι → Bool)
    (φ : ι → ℝ) : ∏ x, w x (flipSigns σ φ x) = ∏ x, w x (φ x) := by
  refine prod_congr rfl fun x _ => ?_
  simp only [flipSigns, sgnMul]
  split_ifs <;> simp [hw]

/-- **Griffiths I, site-dependent weights, general form.** -/
theorem griffiths_first_sites_general {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {g Q : (ι → ℝ) → ℝ} (hg : IsPosPoly g) (hQ : IsPosPoly Q) :
    0 ≤ ∫ φ : ι → ℝ, g φ * Real.exp (Q φ) * ∏ x, w x (φ x) :=
  griffiths_first_inv (W := fun φ => ∏ x, w x (φ x)) (prod_sites_flip hw_even)
    (fun _ => prod_nonneg fun x _ => hw_nonneg x _) hg hQ

/-- **Griffiths' first inequality with site-dependent even nonnegative weights.** -/
theorem griffiths_first_sites {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (a : ι → ℕ) :
    0 ≤ ∫ φ : ι → ℝ, (∏ x, φ x ^ a x) * Real.exp (∑ x, ∑ y, J x y * φ x * φ y)
      * ∏ x, w x (φ x) :=
  griffiths_first_sites_general hw_even hw_nonneg (IsPosPoly.ofMono a) (IsPosPoly.quadForm hJ)

/-- Site-dependent weights with a nonnegative external field. -/
theorem griffiths_first_sites_field {w : ι → ℝ → ℝ} (hw_even : ∀ x y, w x (-y) = w x y)
    (hw_nonneg : ∀ x y, 0 ≤ w x y) {J : ι → ι → ℝ} (hJ : ∀ x y, 0 ≤ J x y) {h : ι → ℝ}
    (hh : ∀ x, 0 ≤ h x) (a : ι → ℕ) :
    0 ≤ ∫ φ : ι → ℝ, (∏ x, φ x ^ a x)
      * Real.exp (∑ x, ∑ y, J x y * φ x * φ y + ∑ x, h x * φ x) * ∏ x, w x (φ x) :=
  griffiths_first_sites_general hw_even hw_nonneg (IsPosPoly.ofMono a)
    ((IsPosPoly.quadForm hJ).add (IsPosPoly.linForm hh))

/-! ## Evenness of the Wick quartic -/

theorem wickPoly_X4_neg (c y : ℝ) :
    wickPoly (Polynomial.X ^ 4) c (-y) = wickPoly (Polynomial.X ^ 4) c y := by
  rw [wickPoly_X4, wickPoly_X4]; ring

/-! ## Application to the Dirichlet-box weight -/

section Model

variable {n k : ℕ}

/-- The index set of the sum in `dirAction`. -/
abbrev boxIdx (n k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-1 : ℤ) (boxN n k - 1) ×ˢ Finset.Icc (-1 : ℤ) (boxN n k - 1)

/-- The nearest-neighbour coupling Σ_p (φ(p+e₁) φ(p) + φ(p+e₂) φ(p)) (zero outside the box). -/
def coupling (φ : DField n k) : ℝ :=
  ∑ p ∈ boxIdx n k, (ext φ (p.1 + 1, p.2) * ext φ p + ext φ (p.1, p.2 + 1) * ext φ p)

/-- The diagonal part Σ_p (φ(p+e₁)² + φ(p)² + φ(p+e₂)² + φ(p)²). -/
def diagPart (φ : DField n k) : ℝ :=
  ∑ p ∈ boxIdx n k,
    (ext φ (p.1 + 1, p.2) ^ 2 + ext φ p ^ 2 + ext φ (p.1, p.2 + 1) ^ 2 + ext φ p ^ 2)

theorem dirAction_eq (m₀ : ℝ) (φ : DField n k) :
    dirAction n k m₀ φ =
      ∑ p ∈ boxIdx n k, ((ext φ (p.1 + 1, p.2) - ext φ p) ^ 2
        + (ext φ (p.1, p.2 + 1) - ext φ p) ^ 2)
      + spacing n ^ 2 * ∑ x : DSite n k, m₀ ^ 2 * φ x ^ 2 := by
  have hε := (spacing_pos n).ne'
  unfold dirAction
  rw [mul_add, Finset.mul_sum]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [div_pow, div_pow]
  field_simp

/-- **The algebraic identity**: −½ dirAction = coupling − ½ diagPart − ½ ε² m₀² Σ φ². -/
theorem neg_half_dirAction (m₀ : ℝ) (φ : DField n k) :
    -(dirAction n k m₀ φ) / 2 =
      coupling φ - diagPart φ / 2 - spacing n ^ 2 * (∑ x : DSite n k, m₀ ^ 2 * φ x ^ 2) / 2 := by
  have hS : ∑ p ∈ boxIdx n k, ((ext φ (p.1 + 1, p.2) - ext φ p) ^ 2
        + (ext φ (p.1, p.2 + 1) - ext φ p) ^ 2) = diagPart φ - 2 * coupling φ := by
    rw [diagPart, coupling, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact sum_congr rfl fun p _ => by ring
  rw [dirAction_eq, hS]; ring

lemma isPosPoly_ext (q : ℤ × ℤ) : IsPosPoly (fun φ : DField n k => ext φ q) := by
  by_cases h : 0 ≤ q.1 ∧ q.1 < boxN n k ∧ 0 ≤ q.2 ∧ q.2 < boxN n k
  · simp only [PP2Target.ext, h, and_self, ↓reduceDIte]; exact IsPosPoly.coord _
  · simp only [PP2Target.ext, h, ↓reduceDIte]; exact IsPosPoly.const le_rfl

lemma isPosPoly_coupling : IsPosPoly (coupling (n := n) (k := k)) :=
  IsPosPoly.sum _ fun _ _ =>
    ((isPosPoly_ext _).mul (isPosPoly_ext _)).add ((isPosPoly_ext _).mul (isPosPoly_ext _))

lemma ext_flip_sq (σ : DSite n k → Bool) (φ : DField n k) (q : ℤ × ℤ) :
    ext (flipSigns σ φ) q ^ 2 = ext φ q ^ 2 := by
  unfold PP2Target.ext
  split_ifs
  · simp only [flipSigns, sgnMul]; split_ifs <;> ring
  · rfl

/-- The even part of the weight: everything in `dweight` except exp(coupling). -/
def evenWeight (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) : ℝ :=
  Real.exp (-(diagPart φ) / 2 - spacing n ^ 2 * (∑ x : DSite n k, m₀ ^ 2 * φ x ^ 2) / 2
    - lam * spacing n ^ 2 * ∑ x : DSite n k, wickPoly P (freeVar n m₀) (φ x))

theorem dweight_eq (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) :
    dweight n k m₀ lam P φ = Real.exp (coupling φ) * evenWeight n k m₀ lam P φ := by
  rw [dweight, evenWeight, ← Real.exp_add, neg_half_dirAction]
  congr 1; ring

theorem evenWeight_flip {m₀ lam : ℝ} {P : Polynomial ℝ}
    (hP : ∀ y, wickPoly P (freeVar n m₀) (-y) = wickPoly P (freeVar n m₀) y)
    (σ : DSite n k → Bool) (φ : DField n k) :
    evenWeight n k m₀ lam P (flipSigns σ φ) = evenWeight n k m₀ lam P φ := by
  have hsgn : ∀ (s : Bool) (y : ℝ), (sgnMul s y) ^ 2 = y ^ 2 := by
    intro s y; cases s <;> simp [sgnMul]
  have hw : ∀ (s : Bool) (y : ℝ),
      wickPoly P (freeVar n m₀) (sgnMul s y) = wickPoly P (freeVar n m₀) y := by
    intro s y; cases s <;> simp [sgnMul, hP]
  unfold evenWeight diagPart
  simp only [ext_flip_sq, flipSigns, hsgn, hw]

/-- **Griffiths I for the Dirichlet-box φ⁴ weight (unnormalised)**, for any even Wick polynomial. -/
theorem griffiths_first_dweight_of_even (m₀ lam : ℝ) {P : Polynomial ℝ}
    (hP : ∀ y, wickPoly P (freeVar n m₀) (-y) = wickPoly P (freeVar n m₀) y) (a : DSite n k → ℕ) :
    0 ≤ ∫ φ : DField n k, (∏ x, φ x ^ a x) * dweight n k m₀ lam P φ := by
  simp_rw [dweight_eq, ← mul_assoc]
  exact griffiths_first_inv (evenWeight_flip hP) (fun φ => (Real.exp_pos _).le)
    (IsPosPoly.ofMono a) isPosPoly_coupling

/-- **Griffiths I for the quartic Dirichlet-box weight (unnormalised).** -/
theorem griffiths_first_dweight (m₀ lam : ℝ) (a : DSite n k → ℕ) :
    0 ≤ ∫ φ : DField n k, (∏ x, φ x ^ a x) * dweight n k m₀ lam (Polynomial.X ^ 4) φ :=
  griffiths_first_dweight_of_even m₀ lam (fun y => wickPoly_X4_neg _ y) a


/-! ## The explicit ferromagnetic form: J ≥ 0 and site-dependent weights -/

/-- δ q x = 1 if the lattice point q is the site x, else 0. -/
def delta (q : ℤ × ℤ) (x : DSite n k) : ℝ :=
  if q = (((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ)) then 1 else 0

lemma delta_nonneg (q : ℤ × ℤ) (x : DSite n k) : 0 ≤ delta q x := by
  unfold delta; split_ifs <;> norm_num

/-- For g with g 0 = 0, g (ext φ q) = Σ_x δ q x · g (φ x). -/
lemma ext_comp_eq_sum {g : ℝ → ℝ} (hg : g 0 = 0) (φ : DField n k) (q : ℤ × ℤ) :
    g (PP2Target.ext φ q) = ∑ x : DSite n k, delta q x * g (φ x) := by
  unfold PP2Target.ext
  split_ifs with h
  · have hq0 : q = ((((⟨q.1.toNat, by omega⟩ : Fin (boxN n k)) : ℕ) : ℤ),
        (((⟨q.2.toNat, by omega⟩ : Fin (boxN n k)) : ℕ) : ℤ)) := by
      refine Prod.ext ?_ ?_ <;> simp <;> omega
    rw [Finset.sum_eq_single (⟨q.1.toNat, by omega⟩, ⟨q.2.toNat, by omega⟩)]
    · unfold delta; split_ifs with H
      · ring
      · exact absurd hq0 H
    · intro x _ hx
      have : ¬ q = (((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ)) := by
        intro hq; apply hx
        have h1 := congrArg Prod.fst hq
        have h2 := congrArg Prod.snd hq
        simp only at h1 h2
        exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
      simp [delta, this]
    · simp
  · rw [hg]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    have : ¬ q = (((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ)) := by
      intro hq; apply h; rw [hq]; simp
    simp [delta, this]

lemma ext_eq_sum (φ : DField n k) (q : ℤ × ℤ) :
    PP2Target.ext φ q = ∑ x : DSite n k, delta q x * φ x :=
  ext_comp_eq_sum (g := id) rfl φ q

lemma ext_sq_eq_sum (φ : DField n k) (q : ℤ × ℤ) :
    PP2Target.ext φ q ^ 2 = ∑ x : DSite n k, delta q x * φ x ^ 2 :=
  ext_comp_eq_sum (g := fun t => t ^ 2) (by norm_num) φ q

/-- The nearest-neighbour coupling matrix: J x y = #{p : (p + e₁, p) = (x, y)} + #{p : (p + e₂, p)
= (x, y)}, i.e. 1 when x = y + e₁ or x = y + e₂ with both in the box, 0 otherwise. -/
def Jnn (n k : ℕ) (x y : DSite n k) : ℝ :=
  ∑ p ∈ boxIdx n k, (delta (p.1 + 1, p.2) x * delta p y + delta (p.1, p.2 + 1) x * delta p y)

/-- The diagonal coefficient c_x = Σ_p (δ(p+e₁) x + 2 δ p x + δ(p+e₂) x). -/
def cdiag (n k : ℕ) (x : DSite n k) : ℝ :=
  ∑ p ∈ boxIdx n k,
    (delta (p.1 + 1, p.2) x + delta p x + delta (p.1, p.2 + 1) x + delta p x)

lemma Jnn_nonneg (x y : DSite n k) : 0 ≤ Jnn n k x y :=
  sum_nonneg fun _ _ => add_nonneg (mul_nonneg (delta_nonneg _ _) (delta_nonneg _ _))
    (mul_nonneg (delta_nonneg _ _) (delta_nonneg _ _))

lemma cdiag_nonneg (x : DSite n k) : 0 ≤ cdiag n k x :=
  sum_nonneg fun _ _ => by
    have := delta_nonneg (n := n) (k := k)
    exact add_nonneg (add_nonneg (add_nonneg (this _ x) (this _ x)) (this _ x)) (this _ x)

end Model

end PP2Griffiths

end

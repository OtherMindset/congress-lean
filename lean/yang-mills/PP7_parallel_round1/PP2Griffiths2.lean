import LongTable.PP2Griffiths
import LongTable.P_mww4cze7_bk8bxu
import LongTable.P_mww0oo05_8eieqb

/-!
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

theorem coupling_eq (φ : DField n k) :
    coupling φ = ∑ x, ∑ y, Jnn n k x y * φ x * φ y := by
  unfold coupling Jnn
  simp only [ext_eq_sum]
  calc _ = ∑ p ∈ boxIdx n k, ∑ x : DSite n k, ∑ y : DSite n k,
        (delta (p.1 + 1, p.2) x * delta p y + delta (p.1, p.2 + 1) x * delta p y)
          * φ x * φ y := by
        refine sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib]
        exact sum_congr rfl fun y _ => by ring
    _ = _ := by
        refine Finset.sum_comm.trans (sum_congr rfl fun x _ =>
          Finset.sum_comm.trans (sum_congr rfl fun y _ => ?_))
        rw [Finset.sum_mul, Finset.sum_mul]

theorem diagPart_eq (φ : DField n k) :
    diagPart φ = ∑ x, cdiag n k x * φ x ^ 2 := by
  unfold diagPart cdiag
  simp only [ext_sq_eq_sum]
  calc _ = ∑ p ∈ boxIdx n k, ∑ x : DSite n k,
        (delta (p.1 + 1, p.2) x + delta p x + delta (p.1, p.2 + 1) x + delta p x) * φ x ^ 2 := by
        refine sum_congr rfl fun p _ => ?_
        simp only [← Finset.sum_add_distrib]
        exact sum_congr rfl fun x _ => by ring
    _ = _ := by
        refine Finset.sum_comm.trans (sum_congr rfl fun x _ => ?_)
        rw [Finset.sum_mul]

/-- The single-site weight at x:
w_x(y) = exp(−(c_x + ε² m₀²) y² / 2 − λ ε² :P:(y)). -/
def siteWeight (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (x : DSite n k) (y : ℝ) : ℝ :=
  Real.exp (-((cdiag n k x + spacing n ^ 2 * m₀ ^ 2) * y ^ 2) / 2
    - lam * spacing n ^ 2 * wickPoly P (freeVar n m₀) y)

theorem evenWeight_eq_prod (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) :
    evenWeight n k m₀ lam P φ = ∏ x, siteWeight n k m₀ lam P x (φ x) := by
  rw [evenWeight, diagPart_eq]
  unfold siteWeight
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  exact sum_congr rfl fun x _ => by ring


lemma sum_delta_shift (a b : ℤ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (x : DSite n k) :
    ∑ p ∈ boxIdx n k, delta (p.1 + a, p.2 + b) x = 1 := by
  have hx1 := x.1.isLt
  have hx2 := x.2.isLt
  have h : ∀ p : ℤ × ℤ, delta (p.1 + a, p.2 + b) x =
      if ((((x.1 : ℕ) : ℤ) - a, ((x.2 : ℕ) : ℤ) - b) = p) then 1 else 0 := by
    intro p
    unfold delta
    by_cases h1 : (p.1 + a, p.2 + b) = (((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ))
    · have h2 : ((((x.1 : ℕ) : ℤ) - a, ((x.2 : ℕ) : ℤ) - b) = p) := by
        simp only [Prod.ext_iff] at h1 ⊢; omega
      simp [h1, h2]
    · have h2 : ¬ ((((x.1 : ℕ) : ℤ) - a, ((x.2 : ℕ) : ℤ) - b) = p) := by
        intro h2; apply h1; simp only [Prod.ext_iff] at h2 ⊢; omega
      simp [h1, h2]
  have hm : ((((x.1 : ℕ) : ℤ) - a, ((x.2 : ℕ) : ℤ) - b)) ∈ boxIdx n k := by
    simp only [boxIdx, Finset.mem_product, Finset.mem_Icc]
    omega
  rw [sum_congr rfl fun p _ => h p, Finset.sum_ite_eq]
  simp [hm]

/-- Every box site has diagonal coefficient exactly 4 (Dirichlet boundary). -/
theorem cdiag_eq_four (x : DSite n k) : cdiag n k x = 4 := by
  have h10 := sum_delta_shift (n := n) (k := k) 1 0 (by norm_num) (by norm_num) x
  have h01 := sum_delta_shift (n := n) (k := k) 0 1 (by norm_num) (by norm_num) x
  have h00 := sum_delta_shift (n := n) (k := k) 0 0 (by norm_num) (by norm_num) x
  simp only [add_zero] at h10 h01 h00
  unfold cdiag
  simp only [Finset.sum_add_distrib]
  rw [h10, h01]
  simp only [Prod.mk.eta] at h00
  rw [h00]; norm_num

/-- Hence w_x(y) = exp(−(4 + ε² m₀²) y² / 2 − λ ε² :P:(y)), the same at every site. -/
theorem siteWeight_eq (m₀ lam : ℝ) (P : Polynomial ℝ) (x : DSite n k) (y : ℝ) :
    siteWeight n k m₀ lam P x y = Real.exp (-((4 + spacing n ^ 2 * m₀ ^ 2) * y ^ 2) / 2
      - lam * spacing n ^ 2 * wickPoly P (freeVar n m₀) y) := by
  rw [siteWeight, cdiag_eq_four]

/-- **The ferromagnetic decomposition of the Dirichlet-box weight**:
dweight φ = exp(Σ_{x,y} J x y φ x φ y) · ∏_x w_x(φ x), with J ≥ 0 (`Jnn_nonneg`). -/
theorem dweight_eq_ferro (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) :
    dweight n k m₀ lam P φ = Real.exp (∑ x, ∑ y, Jnn n k x y * φ x * φ y)
      * ∏ x, siteWeight n k m₀ lam P x (φ x) := by
  rw [dweight_eq, coupling_eq, evenWeight_eq_prod]

lemma siteWeight_even {m₀ lam : ℝ} {P : Polynomial ℝ}
    (hP : ∀ y, wickPoly P (freeVar n m₀) (-y) = wickPoly P (freeVar n m₀) y)
    (x : DSite n k) (y : ℝ) : siteWeight n k m₀ lam P x (-y) = siteWeight n k m₀ lam P x y := by
  simp [siteWeight, hP]

/-- The same Griffiths I for the box, now as an instance of `griffiths_first_sites`. -/
theorem griffiths_first_dweight' (m₀ lam : ℝ) (a : DSite n k → ℕ) :
    0 ≤ ∫ φ : DField n k, (∏ x, φ x ^ a x) * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  simp_rw [dweight_eq_ferro, ← mul_assoc]
  exact griffiths_first_sites (siteWeight_even fun y => wickPoly_X4_neg _ y)
    (fun _ _ => (Real.exp_pos _).le) Jnn_nonneg a

/-! ## Normalised expectations and the partition function -/

lemma continuous_ext (q : ℤ × ℤ) : Continuous fun φ : DField n k => PP2Target.ext φ q := by
  simp only [ext_eq_sum]; fun_prop

theorem continuous_dweight (m₀ lam : ℝ) (P : Polynomial ℝ) :
    Continuous (dweight n k m₀ lam P) := by
  have hc := continuous_ext (n := n) (k := k)
  unfold dweight dirAction wickPoly wickPow
  fun_prop

/-- The Gaussian majorant ∏_x exp(−(m₀² ε²/2) φ(x)²). -/
def dgauss (n k : ℕ) (m₀ : ℝ) (φ : DField n k) : ℝ :=
  ∏ x : DSite n k, Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * φ x ^ 2)

theorem dweight_le (m₀ lam : ℝ) (hlam : 0 ≤ lam) (φ : DField n k) :
    dweight n k m₀ lam (Polynomial.X ^ 4) φ ≤
      Real.exp (lam * spacing n ^ 2 * (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)))
        * dgauss n k m₀ φ := by
  rw [dgauss, ← Real.exp_sum, dweight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hA : spacing n ^ 2 * ∑ x : DSite n k, m₀ ^ 2 * φ x ^ 2 ≤ dirAction n k m₀ φ := by
    rw [dirAction_eq]
    have : 0 ≤ ∑ p ∈ boxIdx n k, ((PP2Target.ext φ (p.1 + 1, p.2) - PP2Target.ext φ p) ^ 2
        + (PP2Target.ext φ (p.1, p.2 + 1) - PP2Target.ext φ p) ^ 2) :=
      sum_nonneg fun _ _ => by positivity
    linarith
  have hsum : -(Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)) ≤
      ∑ x : DSite n k, wickPoly (Polynomial.X ^ 4) (freeVar n m₀) (φ x) := by
    have := Finset.sum_le_sum (s := Finset.univ)
      (fun x (_ : x ∈ Finset.univ) => wickPoly_X4_ge (freeVar n m₀) (φ x))
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hc : 0 ≤ lam * spacing n ^ 2 := by have := spacing_pos n; positivity
  have hg : ∑ x : DSite n k, -(m₀ ^ 2 * spacing n ^ 2 / 2) * φ x ^ 2
      = -(spacing n ^ 2 * ∑ x : DSite n k, m₀ ^ 2 * φ x ^ 2) / 2 := by
    rw [Finset.mul_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [hg]
  nlinarith [mul_le_mul_of_nonneg_left hsum hc]

theorem integrable_dweight {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    Integrable (dweight n k m₀ lam (Polynomial.X ^ 4)) := by
  have hb : 0 < m₀ ^ 2 * spacing n ^ 2 / 2 := by
    have := spacing_pos n
    positivity
  have hG : Integrable (dgauss n k m₀) :=
    Integrable.fintype_prod (ι := DSite n k) (E := ℝ) (𝕜 := ℝ)
      (μ := fun _ => (volume : Measure ℝ))
      (f := fun _ y => Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * y ^ 2))
      (fun _ => integrable_exp_neg_mul_sq hb)
  refine Integrable.mono' (g := fun φ => Real.exp (lam * spacing n ^ 2 *
      (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2))) * dgauss n k m₀ φ) (hG.const_mul _)
    (continuous_dweight m₀ lam _).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro φ
  rw [Real.norm_eq_abs,
    abs_of_pos (show 0 < dweight n k m₀ lam (Polynomial.X ^ 4) φ from Real.exp_pos _)]
  exact dweight_le m₀ lam hlam φ

/-- The Dirichlet-box partition function is strictly positive (λ ≥ 0, m₀ ≠ 0). -/
theorem integral_dweight_pos {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 < ∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  rw [integral_pos_iff_support_of_nonneg
    (fun φ => (show 0 < dweight n k m₀ lam (Polynomial.X ^ 4) φ from Real.exp_pos _).le)
    (integrable_dweight hm hlam)]
  have : Function.support (dweight n k m₀ lam (Polynomial.X ^ 4)) = Set.univ := by
    ext φ; simp [dweight, (Real.exp_pos _).ne']
  rw [this]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

/-- The normalised expectation ⟨F⟩ = ∫ F · dweight / ∫ dweight in the quartic box model. -/
def dexpect (n k : ℕ) (m₀ lam : ℝ) (F : DField n k → ℝ) : ℝ :=
  (∫ φ : DField n k, F φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ) /
    ∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ

/-- **Griffiths I for the normalised quartic box measure**: ⟨∏_x φ(x)^{a x}⟩ ≥ 0, for all
m₀, λ (Bochner integrals: non-integrable ⇒ 0; content is for λ ≥ 0, m₀ ≠ 0; no hypotheses; the denominator is ≥ 0, and > 0 by `integral_dweight_pos` when λ ≥ 0,
m₀ ≠ 0). -/
theorem dexpect_mono_nonneg (m₀ lam : ℝ) (a : DSite n k → ℕ) :
    0 ≤ dexpect n k m₀ lam (fun φ => ∏ x, φ x ^ a x) :=
  div_nonneg (griffiths_first_dweight m₀ lam a)
    (integral_nonneg fun _ => (Real.exp_pos _).le)

end Model

/-! ## Griffiths II: the duplicate-variable rotation (algebra only) -/

section Rotation

/-- The rotated pair ((t + s)/√2, (t − s)/√2). -/
def rot (t s : ι → ℝ) : (ι → ℝ) × (ι → ℝ) :=
  (fun x => (t x + s x) / Real.sqrt 2, fun x => (t x - s x) / Real.sqrt 2)

lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- The rotation preserves every bilinear coupling: t_x t_y + s_x s_y = u_x u_y + v_x v_y. -/
theorem rot_bilin (t s : ι → ℝ) (x y : ι) :
    (rot t s).1 x * (rot t s).1 y + (rot t s).2 x * (rot t s).2 y = t x * t y + s x * s y := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [rot]
  field_simp
  rw [sqrt_two_sq]; ring

/-- Hence it preserves the doubled ferromagnetic energy Σ J t t + Σ J s s. -/
theorem rot_quadForm (J : ι → ι → ℝ) (t s : ι → ℝ) :
    ∑ x, ∑ y, J x y * (rot t s).1 x * (rot t s).1 y + ∑ x, ∑ y, J x y * (rot t s).2 x * (rot t s).2 y
      = ∑ x, ∑ y, J x y * t x * t y + ∑ x, ∑ y, J x y * s x * s y := by
  simp only [← Finset.sum_add_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  have := rot_bilin t s x y
  linear_combination J x y * this

/-- The inverse: t = (u + v)/√2, s = (u − v)/√2. -/
theorem rot_rot (t s : ι → ℝ) : rot (rot t s).1 (rot t s).2 = (t, s) := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  simp only [rot, Prod.mk.injEq]
  constructor <;> funext x <;> field_simp <;> rw [sqrt_two_sq] <;> ring

/-- The ferromagnetic density ρ(φ) = exp(Σ J φφ) ∏ w_x(φ x). -/
def ferroDensity (w : ι → ℝ → ℝ) (J : ι → ι → ℝ) (φ : ι → ℝ) : ℝ :=
  Real.exp (∑ x, ∑ y, J x y * φ x * φ y) * ∏ x, w x (φ x)

/-- **Statement only (not proved).** Griffiths' second inequality for the density ρ, in
unnormalised form: (∫ φ^a φ^b ρ)(∫ ρ) ≥ (∫ φ^a ρ)(∫ φ^b ρ), for all a, b (Bochner integrals:
trivially 0 ≥ 0 when ρ is not integrable; meaningful for integrable ρ). Proved in PP2Griffiths3
(`griffithsSecond_of_integrable`) for every even w ≥ 0 and J ≥ 0, via the duplicate-variable
rotation below. -/
def GriffithsSecond (w : ι → ℝ → ℝ) (J : ι → ι → ℝ) : Prop :=
  ∀ a b : ι → ℕ,
    (∫ φ : ι → ℝ, (∏ x, φ x ^ a x) * (∏ x, φ x ^ b x) * ferroDensity w J φ)
        * (∫ φ : ι → ℝ, ferroDensity w J φ)
      ≥ (∫ φ : ι → ℝ, (∏ x, φ x ^ a x) * ferroDensity w J φ)
        * (∫ φ : ι → ℝ, (∏ x, φ x ^ b x) * ferroDensity w J φ)

end Rotation

end PP2Griffiths


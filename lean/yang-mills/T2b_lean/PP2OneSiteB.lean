import LongTable.PP2OneSiteA

/-!
Long Table, target T2b, one-site (0-d) theorem, LAYER 2 (the monotone-conditional step).
Mathematics: t2b/zerod/zerod_proof.md §2 Step 2.

Coordinates. For the duplicated pair (φ, φ') we use p = φ + φ', d = φ − φ' (the paper's
q = p/√2, t = d/√2; the factor √2 is immaterial). The pair weight at zero field is
  F(p, d) = exp(−W(p, d)),   W(p, d) = V((p + d)/2) + V((p − d)/2),
and S_j(p) = ∫ d^j F(p, d) dd (so ρ = S₀, and g = E[d² | p] = S₂/S₀ in the paper's notation).

FORMALIZED (namespace `PP2OneSite`; no sorry; axioms propext / Classical.choice / Quot.sound):
* Definitions `W`, `F`, `S`; hypotheses as Props:
    `Supermodular V`: ∀ p p' d d', 0 ≤ p' ≤ p → 0 ≤ d' ≤ d → W p d' + W p' d ≤ W p d + W p' d'
      (= ∂_p∂_d W ≥ 0 on the quadrant, in integrated form; derived from the EMN/GHS class
       in PP2OneSiteD);
    `Superlinear V`: ∀ c, ∃ C, ∀ x, c|x| ≤ V x + C   (integrability hypothesis; within the
       EMN class it is equivalent to ∫ e^{c|φ|−V} < ∞ ∀ c, but that equivalence is NOT formalized).
* Symmetries: `F_neg_right` (F(p,−d) = F(p,d)), `F_neg_left` (V even ⟹ F(−p,d) = F(p,d)),
  `S_neg`.
* Integrability: `F_bound`, `integrable2` (any continuous G with |G| ≤ K e^{c(|p|+|d|)}: G·F
  integrable on ℝ²), `integrable_section` (same on each line p = const).
* `S_cross` (the MLR/Chebyshev step in d): V continuous, superlinear, supermodular, 0 ≤ p' ≤ p ⟹
    S₂(p) S₀(p') ≤ S₀(p) S₂(p'),
  i.e. g(p) ≤ g(p'): E[d² | p] is nonincreasing in p ≥ 0. No division, no positivity of ρ needed.
NOT formalized here: the field dependence (PP2OneSiteC), the EMN ⟹ supermodular step (PP2OneSiteD).
Toolchain: Lean 4.35.0, Mathlib 56a00585.
-/

open MeasureTheory Real Set

namespace PP2OneSite

/-- duplicated potential in the coordinates p = φ + φ', d = φ − φ'. -/
noncomputable def W (V : ℝ → ℝ) (p d : ℝ) : ℝ := V ((p + d) / 2) + V ((p - d) / 2)

/-- zero-field pair weight. -/
noncomputable def F (V : ℝ → ℝ) (p d : ℝ) : ℝ := exp (-W V p d)

/-- S j p = ∫ d^j F(p,d) dd. -/
noncomputable def S (V : ℝ → ℝ) (j : ℕ) (p : ℝ) : ℝ := ∫ d, d ^ j * F V p d

def Supermodular (V : ℝ → ℝ) : Prop :=
  ∀ p p' d d', 0 ≤ p' → p' ≤ p → 0 ≤ d' → d' ≤ d → W V p d' + W V p' d ≤ W V p d + W V p' d'

def Superlinear (V : ℝ → ℝ) : Prop := ∀ c : ℝ, ∃ C : ℝ, ∀ x, c * |x| ≤ V x + C

lemma F_pos (V : ℝ → ℝ) (p d : ℝ) : 0 < F V p d := exp_pos _

lemma F_neg_right (V : ℝ → ℝ) (p d : ℝ) : F V p (-d) = F V p d := by
  unfold F W
  rw [show p + -d = p - d by ring, show p - -d = p + d by ring, add_comm]

lemma F_neg_left {V : ℝ → ℝ} (hev : ∀ x, V (-x) = V x) (p d : ℝ) : F V (-p) d = F V p d := by
  unfold F W
  rw [show (-p + d) / 2 = -((p - d) / 2) by ring, show (-p - d) / 2 = -((p + d) / 2) by ring,
    hev, hev, add_comm]

lemma S_neg {V : ℝ → ℝ} (hev : ∀ x, V (-x) = V x) (j : ℕ) (p : ℝ) : S V j (-p) = S V j p := by
  unfold S; simp only [F_neg_left hev]

lemma exp_neg_two_abs_le (t : ℝ) : exp (-(2 * |t|)) ≤ (1 + t ^ 2)⁻¹ := by
  rw [exp_neg]
  apply inv_anti₀ (by positivity)
  have h1 := add_one_le_exp |t|
  have h2 : exp (2 * |t|) = exp |t| * exp |t| := by rw [← exp_add]; ring_nf
  rw [h2]
  have h3 : 0 ≤ |t| := abs_nonneg t
  nlinarith [mul_le_mul h1 h1 (by positivity) (by positivity), sq_abs t]

lemma abs_pow_le_exp (n : ℕ) (t : ℝ) : |t ^ n| ≤ exp (n * |t|) := by
  rw [abs_pow, exp_nat_mul]
  exact pow_le_pow_left₀ (abs_nonneg t) (by linarith [add_one_le_exp |t|]) n

lemma F_bound {V : ℝ → ℝ} (hsl : Superlinear V) {c : ℝ} (hc : 0 ≤ c) :
    ∃ K, 0 ≤ K ∧ ∀ p d, exp (c * (|p| + |d|)) * F V p d
      ≤ K * (exp (-(2 * |p|)) * exp (-(2 * |d|))) := by
  obtain ⟨C, hC⟩ := hsl (2 * c + 4)
  refine ⟨exp (2 * C), (exp_pos _).le, fun p d => ?_⟩
  have hx := hC ((p + d) / 2)
  have hy := hC ((p - d) / 2)
  have hp : |p| ≤ |(p + d) / 2| + |(p - d) / 2| := by
    calc |p| = |(p + d) / 2 + (p - d) / 2| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hd : |d| ≤ |(p + d) / 2| + |(p - d) / 2| := by
    calc |d| = |(p + d) / 2 + -((p - d) / 2)| := by congr 1; ring
      _ ≤ |(p + d) / 2| + |-((p - d) / 2)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hm : (c + 2) * (|p| + |d|) ≤ (c + 2) * (2 * (|(p + d) / 2| + |(p - d) / 2|)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold F W
  rw [← exp_add, ← exp_add, ← exp_add]
  apply exp_le_exp.mpr
  nlinarith

lemma E2_integrable :
    Integrable (fun z : ℝ × ℝ => (1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹) (volume.prod volume) :=
  integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq

lemma F_continuous {V : ℝ → ℝ} (hV : Continuous V) :
    Continuous (fun z : ℝ × ℝ => F V z.1 z.2) := by
  unfold F W; fun_prop

lemma integrable2 {V : ℝ → ℝ} (hV : Continuous V) (hsl : Superlinear V) {G : ℝ × ℝ → ℝ}
    (hG : Continuous G) {c K₀ : ℝ} (hc : 0 ≤ c) (hK₀ : 0 ≤ K₀)
    (hGb : ∀ z, |G z| ≤ K₀ * exp (c * (|z.1| + |z.2|))) :
    Integrable (fun z : ℝ × ℝ => G z * F V z.1 z.2) (volume.prod volume) := by
  obtain ⟨K, hK, hb⟩ := F_bound hsl hc
  refine (E2_integrable.const_mul (K₀ * K)).mono'
    ((hG.mul (F_continuous hV)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (F_pos V _ _)]
  calc |G z| * F V z.1 z.2 ≤ K₀ * exp (c * (|z.1| + |z.2|)) * F V z.1 z.2 :=
        mul_le_mul_of_nonneg_right (hGb z) (F_pos V _ _).le
    _ = K₀ * (exp (c * (|z.1| + |z.2|)) * F V z.1 z.2) := by ring
    _ ≤ K₀ * (K * (exp (-(2 * |z.1|)) * exp (-(2 * |z.2|)))) :=
        mul_le_mul_of_nonneg_left (hb _ _) hK₀
    _ ≤ K₀ * K * ((1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹) := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK₀ hK)
        exact mul_le_mul (exp_neg_two_abs_le _) (exp_neg_two_abs_le _) (exp_pos _).le
          (by positivity)

lemma integrable_section {V : ℝ → ℝ} (hV : Continuous V) (hsl : Superlinear V) (p : ℝ)
    {g : ℝ → ℝ} (hg : Continuous g) {c K₀ : ℝ} (hc : 0 ≤ c) (hK₀ : 0 ≤ K₀)
    (hgb : ∀ d, |g d| ≤ K₀ * exp (c * |d|)) : Integrable (fun d => g d * F V p d) := by
  obtain ⟨K, hK, hb⟩ := F_bound hsl hc
  have hFc : Continuous (fun d => F V p d) := by unfold F W; fun_prop
  refine (integrable_inv_one_add_sq.const_mul (K₀ * K)).mono'
    ((hg.mul hFc).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun d => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (F_pos V _ _)]
  have e1 : exp (c * |d|) ≤ exp (c * (|p| + |d|)) :=
    exp_le_exp.mpr (by nlinarith [abs_nonneg p])
  have e2 : exp (-(2 * |p|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg p])
  calc |g d| * F V p d ≤ K₀ * exp (c * (|p| + |d|)) * F V p d := by
        apply mul_le_mul_of_nonneg_right _ (F_pos V _ _).le
        exact (hgb d).trans (mul_le_mul_of_nonneg_left e1 hK₀)
    _ = K₀ * (exp (c * (|p| + |d|)) * F V p d) := by ring
    _ ≤ K₀ * (K * (exp (-(2 * |p|)) * exp (-(2 * |d|)))) :=
        mul_le_mul_of_nonneg_left (hb _ _) hK₀
    _ ≤ K₀ * K * (1 + d ^ 2)⁻¹ := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK₀ hK)
        calc exp (-(2 * |p|)) * exp (-(2 * |d|)) ≤ 1 * (1 + d ^ 2)⁻¹ :=
              mul_le_mul e2 (exp_neg_two_abs_le d) (exp_pos _).le zero_le_one
          _ = _ := one_mul _

lemma integrable_S_section {V : ℝ → ℝ} (hV : Continuous V) (hsl : Superlinear V) (j : ℕ)
    (q : ℝ) : Integrable (fun d => d ^ j * F V q d) :=
  integrable_section hV hsl q (continuous_pow j) (Nat.cast_nonneg j) zero_le_one
    (fun d => by simpa using abs_pow_le_exp j d)

/-- Step 2 of the paper (MLR in d): E[d² | p] is nonincreasing in p ≥ 0, in product form. -/
theorem S_cross {V : ℝ → ℝ} (hV : Continuous V) (hsl : Superlinear V) (hsup : Supermodular V)
    {p p' : ℝ} (hp' : 0 ≤ p') (hpp : p' ≤ p) :
    S V 2 p * S V 0 p' ≤ S V 0 p * S V 2 p' := by
  have hint := integrable_S_section hV hsl
  unfold S
  apply cheb_prod (hint 2 p) (hint 0 p') (hint 0 p) (hint 2 p')
  apply cheb_even_cond
  · intro x; simp only [F_neg_right, neg_sq]
  · intro x; simp only [F_neg_right, pow_zero]
  · intro x; simp only [F_neg_right, pow_zero]
  · intro x; simp only [F_neg_right, neg_sq]
  intro X Y hX hY
  simp only [pow_zero, one_mul]
  have hF : ∀ {u v : ℝ}, 0 ≤ v → v ≤ u → F V p u * F V p' v ≤ F V p v * F V p' u := by
    intro u v hv hvu
    unfold F
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    have := hsup p p' u v hp' hpp hv hvu
    linarith
  rcases le_total Y X with hYX | hXY
  · have key : 0 ≤ (X ^ 2 - Y ^ 2) * (F V p Y * F V p' X - F V p X * F V p' Y) :=
      mul_nonneg (by nlinarith) (by linarith [hF hY hYX])
    linear_combination key
  · have key : 0 ≤ (Y ^ 2 - X ^ 2) * (F V p X * F V p' Y - F V p Y * F V p' X) :=
      mul_nonneg (by nlinarith) (by linarith [hF hX hXY])
    linear_combination key

end PP2OneSite

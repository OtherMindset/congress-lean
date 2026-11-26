import LongTable.PP2OneSiteC

/-!
Long Table, target T2b, one-site (0-d) theorem, LAYER 2b + final statement for the EMN/GHS class.
Mathematics: t2b/zerod/zerod_proof.md §2 Step 2, the computation
  ∂_p∂_d W = ¼[V''((p+d)/2) − V''((p−d)/2)] ≥ 0 on p, d ≥ 0, since (p+d)/2 ≥ |p−d|/2,
done here without second mixed derivatives: two one-variable monotonicity arguments.

FORMALIZED (namespace `PP2OneSite`; no sorry; axioms propext / Classical.choice / Quot.sound):
* `deriv_odd`, `deriv2_even`: V even with V' = V1, V1' = V2 everywhere ⟹ V1 odd, V2 even.
* `k_mono`: a ≥ 0 ⟹ b ↦ V1(a+b) + V1(a−b) is monotone on [0,∞) (derivative V2(a+b) − V2(a−b)
  ≥ 0 because |a−b| ≤ a+b and V2 even, monotone on [0,∞)).
* `psi_mono`: 0 ≤ d' ≤ d ⟹ p ↦ W(p,d) − W(p,d') is monotone on [0,∞).
* `supermodular_of_EMN`: the EMN/GHS class (V even, C² in the form HasDerivAt V V1, HasDerivAt V1 V2,
  V2 = V'' monotone on [0,∞)) ⟹ `Supermodular V`.
* MAIN THEOREM `R_antitoneOn_EMN`: V even, V' = V1, V1' = V2 everywhere, MonotoneOn V2 (Ici 0),
  `Superlinear V` (∀ c ∃ C ∀ x, c|x| ≤ V x + C) ⟹
      AntitoneOn (R V) (Ioi 0),
  where R V H = ⟨φ;φ²⟩_H / ⟨φ⟩_H for dμ_H ∝ e^{−V(φ)+Hφ}dφ (`R`, `Mom` in PP2OneSiteC).
* Non-vacuity / φ⁴ instance `R_antitoneOn_phi4`: V(x) = λx⁴ + (μ/2)x², λ > 0, any μ ∈ ℝ
  (single and double well).
NOT formalized: (i) the equivalence, inside the EMN class, of `Superlinear` with the paper's
∫ e^{c|φ|−V} < ∞ ∀ c (true: V' convex on [0,∞) with V'(0) = 0 forces either V' ≤ 0 on [0,∞),
non-integrable, or V growing at least quadratically) — the theorem is stated with `Superlinear`;
(ii) the C¹/one-sided-derivative extension (paper's remark); (iii) "R constant iff V quadratic"
(only "if" is claimed in the paper's proof; not formalized either way).
Toolchain: Lean 4.35.0, Mathlib 56a00585.
-/

open MeasureTheory Real Set

namespace PP2OneSite

variable {V V1 V2 : ℝ → ℝ}

lemma deriv_odd (hV : ∀ x, HasDerivAt V (V1 x) x) (hev : ∀ x, V (-x) = V x) (x : ℝ) :
    V1 (-x) = -V1 x := by
  have h1 : HasDerivAt (fun y => V (-y)) (V1 (-x) * (-1)) x :=
    (hV (-x)).comp x (hasDerivAt_neg x)
  rw [show (fun y => V (-y)) = V from funext hev] at h1
  have := (hV x).unique h1
  linarith

lemma deriv2_even (hV : ∀ x, HasDerivAt V (V1 x) x) (hV1 : ∀ x, HasDerivAt V1 (V2 x) x)
    (hev : ∀ x, V (-x) = V x) (x : ℝ) : V2 (-x) = V2 x := by
  have h1 : HasDerivAt (fun y => -V1 (-y)) (-(V2 (-x) * (-1))) x :=
    ((hV1 (-x)).comp x (hasDerivAt_neg x)).neg
  rw [show (fun y => -V1 (-y)) = V1 from funext fun y => by rw [deriv_odd hV hev, neg_neg]] at h1
  have := (hV1 x).unique h1
  linarith

lemma k_mono (hV1 : ∀ x, HasDerivAt V1 (V2 x) x) (hev2 : ∀ x, V2 (-x) = V2 x)
    (hmono : MonotoneOn V2 (Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    MonotoneOn (fun b => V1 (a + b) + V1 (a - b)) (Ici 0) := by
  have hd : ∀ b, HasDerivAt (fun b => V1 (a + b) + V1 (a - b)) (V2 (a + b) - V2 (a - b)) b := by
    intro b
    have h1 : HasDerivAt (fun b => V1 (a + b)) (V2 (a + b) * 1) b :=
      (hV1 (a + b)).comp b ((hasDerivAt_id' b).const_add a)
    have h2 : HasDerivAt (fun b => V1 (a - b)) (V2 (a - b) * (-1)) b :=
      (hV1 (a - b)).comp b ((hasDerivAt_id' b).const_sub a)
    convert h1.add h2 using 1
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact fun b _ => (hd b).continuousAt.continuousWithinAt
  · exact fun b _ => (hd b).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Ici] at hb
    have hb0 : 0 ≤ b := le_of_lt hb
    rw [(hd b).deriv, sub_nonneg, ← even_abs_eq hev2 (a - b)]
    exact hmono (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (by linarith))
      (abs_le.mpr ⟨by linarith, by linarith⟩)

lemma psi_mono (hV : ∀ x, HasDerivAt V (V1 x) x) (hV1 : ∀ x, HasDerivAt V1 (V2 x) x)
    (hev2 : ∀ x, V2 (-x) = V2 x) (hmono : MonotoneOn V2 (Ici 0)) {d d' : ℝ} (hd' : 0 ≤ d')
    (hdd : d' ≤ d) : MonotoneOn (fun p => W V p d - W V p d') (Ici 0) := by
  have hl : ∀ (e : ℝ) (p : ℝ), HasDerivAt (fun p => W V p e)
      (V1 ((p + e) / 2) * (1 / 2) + V1 ((p - e) / 2) * (1 / 2)) p := by
    intro e p
    have h1 : HasDerivAt (fun p => V ((p + e) / 2)) (V1 ((p + e) / 2) * (1 / 2)) p :=
      (hV _).comp p (((hasDerivAt_id' p).add_const e).div_const 2)
    have h2 : HasDerivAt (fun p => V ((p - e) / 2)) (V1 ((p - e) / 2) * (1 / 2)) p :=
      (hV _).comp p (((hasDerivAt_id' p).sub_const e).div_const 2)
    exact h1.add h2
  have hd : ∀ p, HasDerivAt (fun p => W V p d - W V p d')
      ((V1 (p / 2 + d / 2) + V1 (p / 2 - d / 2) - (V1 (p / 2 + d' / 2) + V1 (p / 2 - d' / 2)))
        / 2) p := by
    intro p
    convert (hl d p).sub (hl d' p) using 1
    rw [show (p + d) / 2 = p / 2 + d / 2 by ring, show (p - d) / 2 = p / 2 - d / 2 by ring,
      show (p + d') / 2 = p / 2 + d' / 2 by ring, show (p - d') / 2 = p / 2 - d' / 2 by ring]
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact fun p _ => (hd p).continuousAt.continuousWithinAt
  · exact fun p _ => (hd p).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Ici] at hp
    rw [(hd p).deriv]
    have := k_mono hV1 hev2 hmono (a := p / 2) (by linarith [hp.out])
      (show (0 : ℝ) ≤ d' / 2 by linarith) (show (0 : ℝ) ≤ d / 2 by linarith)
      (by linarith : d' / 2 ≤ d / 2)
    simp only at this
    linarith

theorem supermodular_of_EMN (hV : ∀ x, HasDerivAt V (V1 x) x)
    (hV1 : ∀ x, HasDerivAt V1 (V2 x) x) (hev : ∀ x, V (-x) = V x)
    (hmono : MonotoneOn V2 (Ici 0)) : Supermodular V := by
  intro p p' d d' hp' hpp hd' hdd
  have := psi_mono hV hV1 (deriv2_even hV hV1 hev) hmono hd' hdd hp'
    (show (0 : ℝ) ≤ p by linarith) hpp
  simp only at this
  linarith

/-- MAIN THEOREM (EMN/GHS class): R(H) = ⟨φ;φ²⟩_H/⟨φ⟩_H is nonincreasing on H > 0. -/
theorem R_antitoneOn_EMN (hV : ∀ x, HasDerivAt V (V1 x) x)
    (hV1 : ∀ x, HasDerivAt V1 (V2 x) x) (hev : ∀ x, V (-x) = V x)
    (hmono : MonotoneOn V2 (Ici 0)) (hsl : Superlinear V) : AntitoneOn (R V) (Ioi 0) :=
  R_antitoneOn_of_supermodular (continuous_iff_continuousAt.mpr fun x => (hV x).continuousAt)
    hev hsl (supermodular_of_EMN hV hV1 hev hmono)

/-- φ⁴ instance (non-vacuity): V(x) = λx⁴ + (μ/2)x², λ > 0, μ arbitrary. -/
theorem R_antitoneOn_phi4 {lam mu : ℝ} (hlam : 0 < lam) :
    AntitoneOn (R (fun x => lam * x ^ 4 + mu / 2 * x ^ 2)) (Ioi 0) := by
  apply R_antitoneOn_EMN (V1 := fun x => 4 * lam * x ^ 3 + mu * x)
    (V2 := fun x => 12 * lam * x ^ 2 + mu)
  · intro x
    convert ((hasDerivAt_pow 4 x).const_mul lam).add ((hasDerivAt_pow 2 x).const_mul (mu / 2))
      using 1; norm_num; ring
  · intro x
    convert ((hasDerivAt_pow 3 x).const_mul (4 * lam)).add ((hasDerivAt_id' x).const_mul mu)
      using 1; norm_num; ring
  · intro x; ring
  · intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    have : x ^ 2 ≤ y ^ 2 := by nlinarith
    simp only; nlinarith
  · intro c
    refine ⟨c ^ 2 / 4 + (1 + |mu| / 2) ^ 2 / (4 * lam), fun x => ?_⟩
    have h1 : c * |x| ≤ x ^ 2 + c ^ 2 / 4 := by nlinarith [sq_nonneg (|x| - c / 2), sq_abs x]
    have h2 : (1 + |mu| / 2) * x ^ 2 ≤ lam * x ^ 4 + (1 + |mu| / 2) ^ 2 / (4 * lam) := by
      rw [← sub_nonneg]
      have : lam * x ^ 4 + (1 + |mu| / 2) ^ 2 / (4 * lam) - (1 + |mu| / 2) * x ^ 2
          = (2 * lam * x ^ 2 - (1 + |mu| / 2)) ^ 2 / (4 * lam) := by
        field_simp; ring
      rw [this]; positivity
    have h3 : -(|mu| / 2 * x ^ 2) ≤ mu / 2 * x ^ 2 := by
      nlinarith [neg_abs_le mu, sq_nonneg x]
    simp only
    linarith

end PP2OneSite

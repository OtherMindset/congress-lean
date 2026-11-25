import LongTable.PP2SimonLieb
import LongTable.PP2Griffiths2
import LongTable.PP2Green2

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M3, session 2.
Step (R2) of the route in `PP2SimonLieb`: the local-time family [·]_τ and the one-site local-time
integration by parts, for the quartic Dirichlet-box model (namespace `PP2Target`), with an
abstract version for any finite index set (namespace `PP2LocalTime`).

Source: Brydges–Fröhlich–Spencer, CMP 83 (1982), uploaded copy read through the site
(§2 (2.3), (2.21)–(2.22) and Theorem 2.2; §5 (5.4)–(5.6)). BFS write the single-spin weight as
g(S²) and the local-time shift as g(S² + 2t) with dt-measure; with g(S²) = e^{−f(S²/2)} this is
e^{−f(S²/2 + t)}, which is the convention used here (no subtraction of f(t): the prefactor
e^{−f(t)} is part of [·]_t and is what makes the t-integrals converge).

CONSTANTS (checked against `dweight` with Wick ordering at c = freeVar n m₀). With s = φ²/2,
  −log siteWeight(φ) = (4 + ε²m₀²) φ²/2 + λε²(φ⁴ − 6cφ² + 3c²) = α s + β s² + 3λε²c²,
  α = 4 + ε²m₀² − 12λε²c   (`alphaQ`),   β = 4λε²   (`betaQ`),
and the constant 3λε²c² per site drops out (`qweight_eq_tw`, `tauInt_zero`). The diagonal 4 is
the Dirichlet diagonal (`cdiag_eq_four`); the pair part is e^{Σ_{x,y} Jnn_xy φ_x φ_y}
(`dweight_eq_ferro`), whose φ_i-derivative gives J_ij = Jnn_ij + Jnn_ji = bondJ_ij (`Jsym_eq_bondJ`).

DEFINITIONS.
* `fq a b u = a u + b u²`, `tw a b τ φ = ∏_x e^{−f(φ_x²/2 + τ_x)}` (as exp of a sum).
* `quadE K φ = Σ_{x,y} K_xy φ_x φ_y`.
* `tauInt n k m₀ λ τ G = ∫ G · e^{quadE Jnn} · tw α β τ` =: [G]_τ (unnormalised).
* `Jsym n k i j = Jnn i j + Jnn j i`.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* `tw_shift`, `hasLineDerivAt_tw`, `hasDerivAt_tw_shift`: the two derivatives of the weight,
  ∂_{φ_i} W_σ = −φ_i f'(φ_i²/2+σ_i) W_σ and ∂_s W_{τ+se_i} = −f'(φ_i²/2+τ_i+s) W_{τ+se_i}, so
  ∂_{φ_i} W = φ_i ∂_s W (the identity behind the local time).
* `tw_mass_shift`: W_τ = e^{−Σ f(τ_x)} · e^{−β Σ τ_x φ_x²} · W_0 (site mass² raised by 2βτ_x);
  `tw_le_tw_zero`: W_τ ≤ e^{−Σ f(τ_x)} W_0 for τ ≥ 0, β ≥ 0.
* `local_time_ibp` (abstract, any finite ι; b ≥ 0, b > 0 or a > 0, τ_i ≥ 0; R, R' continuous,
  R' the e_i-derivative of R; R, φ_i R, φ_i³ R, R' integrable against W_τ):
    ∫ φ_i R W_τ = ∫_{s>0} ∫ R' W_{τ+s e_i}.
  Proof: 1-D FTC on (0, ∞) in s (`integral_Ioi_tw`), Fubini (`integral_integral_swap`, with the
  explicit product dominator `ltG(φ) · C e^{−cs}`, `ltF_bound`, `exists_exp_bound`), and
  integration by parts in φ_i at each fixed s (`ibp_fixed`, Mathlib's line-derivative IBP).
* `local_time_ibp_bfs`: the same with R = G e^{quadE K}: [φ_i G]_τ = ∫_0^∞ ds
  [∂_i G + Σ_j (K_ij + K_ji) φ_j G]_{τ+s e_i}, for any K.
* `quad_Jnn_bondJ`, `bondJ_diag` (= −4), `Jnn_diag` (= 0), `Jsym_eq_bondJ` (x ≠ y), `sum_Jsym_eq`.
* `qweight_le_gauss`, `tauWeight_le`, `integrable_tau`: for m₀ ≠ 0, λ ≥ 0, τ ≥ 0, every H with
  |H| ≤ C e^{a Σ|φ|} (all polynomials) is integrable against e^{quadE Jnn} W_τ.
* **`tau_ibp_quartic`** (R2 for the quartic box model; m₀ ≠ 0, λ ≥ 0, τ ≥ 0, G, G' = ∂_i G
  continuous and both ≤ C e^{a Σ|φ|}; no further hypotheses):
    [φ_i G]_τ = ∫_{s>0} ( [∂_i G]_{τ+s e_i} + Σ_j J_ij [φ_j G]_{τ+s e_i} ),
  and `tau_ibp_quartic_bondJ`, the same with Σ_{j ≠ i} bondJ_ij.

NOT formalized.
* Integrability in s of the integrand s ↦ [·]_{τ+s e_i}: it holds (Fubini in the proof) but is NOT
  exported here, so the displayed identities, read alone, do not assert integrability (a
  non-integrable integrand would give 0 on the right). [Exported later: `integrableOn_tI_shift`
  in PP2SimonLieb3.] Continuity in τ.
* G of exponential-quadratic growth (e.g. G = φ_y e^{bdryCoupling}, used in R5 for the DECOUPLED
  measure). Not needed if R5 applies R2 to the full measure with G = φ_y, since
  decWeight · e^{bdryCoupling} = qweight · const (`dweight_split`); otherwise the abstract
  `local_time_ibp_bfs` applies with the integrability hypotheses to be checked.
* (R3)–(R5).

A FINDING for (R4) [SUPERSEDED by PP2SimonLieb3: a weight e^{c'Στ} with c' > max row sum of J
gives the contraction on fine lattices too; the walk bound below is not needed]. With Wick ordering α = 4 + ε²(m₀² − 12λc), c = freeVar ~ (2π)⁻¹ log(1/ε), so
α < 4 = max_i Σ_j J_ij for all fine lattices when λ > 0: the weighted-sup-norm contraction of
`PP2SimonLieb` (R4) ("β' > 4, possible since α > 4") only works at λ = 0. The fix we propose:
|D(τ)| ≤ M e^{−Σ_x f(τ_x)} by `tw_le_tw_zero`, and f(τ + S) ≥ f(τ) + f(S) (β ≥ 0); the N-fold
iterate K^N is then bounded by a sum over N-step walks of Π_x ∫ S^{n_x−1}/(n_x−1)! e^{−f(S)} dS,
which for β > 0 decays superexponentially in the visit numbers n_x; in a FIXED finite box some
n_x ≥ N/|Λ|, so ‖K^N‖ → 0 and D⁻ ≤ K^N D⁻ → 0. No uniformity in the volume is needed for (R4).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Set Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2LocalTime

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The single-site exponent f(u) = a u + b u². -/
def fq (a b u : ℝ) : ℝ := a * u + b * u ^ 2

/-- Its derivative f'(u) = a + 2 b u. -/
def fq' (a b u : ℝ) : ℝ := a + 2 * b * u

theorem hasDerivAt_fq (a b u : ℝ) : HasDerivAt (fq a b) (fq' a b u) u := by
  have h1 : HasDerivAt (fun y : ℝ => a * y) (a * 1) u := (hasDerivAt_id' u).const_mul a
  have h2 : HasDerivAt (fun y : ℝ => b * y ^ 2) (b * (2 * u)) u := by
    convert (hasDerivAt_pow 2 u).const_mul b using 1; norm_num
  have := h1.fun_add h2
  unfold fq fq'
  convert this using 1; ring

/-- The local-time weight W_τ(φ) = ∏_x e^{−f(φ_x²/2 + τ_x)}. -/
def tw (a b : ℝ) (τ φ : ι → ℝ) : ℝ := Real.exp (-∑ x, fq a b (φ x ^ 2 / 2 + τ x))

theorem tw_pos (a b : ℝ) (τ φ : ι → ℝ) : 0 < tw a b τ φ := Real.exp_pos _

@[fun_prop]
theorem continuous_tw (a b : ℝ) (τ : ι → ℝ) : Continuous (tw a b τ) := by
  unfold tw fq; fun_prop

lemma sum_add_single (F : ι → ℝ → ℝ) (v : ι → ℝ) (i : ι) (t : ℝ) :
    ∑ x, F x (v x + (Pi.single i t : ι → ℝ) x) = ∑ x, F x (v x) + (F i (v i + t) - F i (v i)) := by
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro x _ hx; simp [Pi.single_eq_of_ne hx]
  · simp

/-- Raising the local time at i by s multiplies the weight by e^{−(f(u+s) − f(u))},
u = φ_i²/2 + τ_i. -/
theorem tw_shift (a b : ℝ) (τ φ : ι → ℝ) (i : ι) (s : ℝ) :
    tw a b (τ + Pi.single i s) φ =
      tw a b τ φ * Real.exp (fq a b (φ i ^ 2 / 2 + τ i) - fq a b (φ i ^ 2 / 2 + τ i + s)) := by
  unfold tw
  rw [← Real.exp_add]
  congr 1
  have := sum_add_single (fun _ y => fq a b y) (fun x => φ x ^ 2 / 2 + τ x) i s
  simp only [Pi.add_apply, ← add_assoc] at this ⊢
  rw [this]; ring

/-- The φ_i-derivative of the weight: ∂_i W_σ = −φ_i f'(φ_i²/2 + σ_i) W_σ. -/
theorem hasLineDerivAt_tw (a b : ℝ) (σ φ : ι → ℝ) (i : ι) :
    HasLineDerivAt ℝ (tw a b σ) (-(φ i * fq' a b (φ i ^ 2 / 2 + σ i)) * tw a b σ φ) φ
      (Pi.single i 1) := by
  unfold HasLineDerivAt
  have e : ∀ t : ℝ, tw a b σ (φ + t • Pi.single i 1) = tw a b σ φ *
      Real.exp (fq a b (φ i ^ 2 / 2 + σ i) - fq a b ((φ i + t) ^ 2 / 2 + σ i)) := by
    intro t
    have hv : φ + t • Pi.single i (1 : ℝ) = fun x => φ x + (Pi.single i t : ι → ℝ) x := by
      funext x
      by_cases hx : x = i
      · subst hx; simp
      · simp [Pi.single_eq_of_ne hx]
    rw [hv]; unfold tw; rw [← Real.exp_add]; congr 1
    have := sum_add_single (fun x y => fq a b (y ^ 2 / 2 + σ x)) φ i t
    rw [this]; ring
  simp_rw [e]
  have h1 : HasDerivAt (fun t : ℝ => (φ i + t) ^ 2 / 2 + σ i) (φ i) 0 := by
    have := ((((hasDerivAt_id' (0 : ℝ)).const_add (φ i)).fun_pow 2).div_const 2).add_const (σ i)
    convert this using 1; norm_num
  have h3 : HasDerivAt (fun t : ℝ => fq a b ((φ i + t) ^ 2 / 2 + σ i))
      (fq' a b ((φ i + 0) ^ 2 / 2 + σ i) * φ i) 0 :=
    (hasDerivAt_fq a b _).comp (0 : ℝ) h1
  have h2 := ((h3.const_sub (fq a b (φ i ^ 2 / 2 + σ i))).exp).const_mul (tw a b σ φ)
  convert h2 using 1
  simp only [add_zero, sub_self, Real.exp_zero]
  ring

/-- The s-derivative of the shifted weight: ∂_s W_{τ+s e_i} = −f'(φ_i²/2 + τ_i + s) W_{τ+s e_i}. -/
theorem hasDerivAt_tw_shift (a b : ℝ) (τ φ : ι → ℝ) (i : ι) (s : ℝ) :
    HasDerivAt (fun s => tw a b (τ + Pi.single i s) φ)
      (-(fq' a b (φ i ^ 2 / 2 + τ i + s)) * tw a b (τ + Pi.single i s) φ) s := by
  simp_rw [tw_shift a b τ φ i]
  have h1 : HasDerivAt (fun s : ℝ => φ i ^ 2 / 2 + τ i + s) 1 s :=
    (hasDerivAt_id s).const_add _
  have h3 : HasDerivAt (fun s : ℝ => fq a b (φ i ^ 2 / 2 + τ i + s))
      (fq' a b (φ i ^ 2 / 2 + τ i + s) * 1) s :=
    (hasDerivAt_fq a b _).comp s h1
  have h2 := ((h3.const_sub (fq a b (φ i ^ 2 / 2 + τ i))).exp).const_mul (tw a b τ φ)
  convert h2 using 1
  ring

/-! ## Bounds in the local time -/

/-- A uniform exponential bound: (1 + 2bs) e^{−(as + bs²)} ≤ C e^{−cs} for s ≥ 0, some c > 0. -/
theorem exists_exp_bound {a b : ℝ} (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a) :
    ∃ c > 0, ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s →
      (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) ≤ C * Real.exp (-c * s) := by
  rcases hb.lt_or_eq with hb' | hb'
  · set p := 1 - a + 2 * b with hp
    refine ⟨1, one_pos, Real.exp (p ^ 2 / (4 * b)), fun s hs => ?_⟩
    have h1 : 1 + 2 * b * s ≤ Real.exp (2 * b * s) := by
      linarith [Real.add_one_le_exp (2 * b * s)]
    have hq : 2 * b * s + -(a * s + b * s ^ 2) ≤ p ^ 2 / (4 * b) + -1 * s := by
      have e : p ^ 2 / (4 * b) + -1 * s - (2 * b * s + -(a * s + b * s ^ 2)) =
          (2 * b * s - p) ^ 2 / (4 * b) := by
        field_simp; ring
      have : 0 ≤ (2 * b * s - p) ^ 2 / (4 * b) := by positivity
      linarith
    calc (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2))
        ≤ Real.exp (2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (2 * b * s + -(a * s + b * s ^ 2)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (p ^ 2 / (4 * b) + -1 * s) := Real.exp_le_exp.mpr hq
      _ = Real.exp (p ^ 2 / (4 * b)) * Real.exp (-1 * s) := Real.exp_add _ _
  · subst hb'
    have ha : 0 < a := hab.resolve_left (lt_irrefl 0)
    refine ⟨a, ha, 1, fun s _ => ?_⟩
    simp [neg_mul]

theorem fq_shift_ge {a b u s : ℝ} (hb : 0 ≤ b) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    a * s + b * s ^ 2 ≤ fq a b (u + s) - fq a b u := by
  unfold fq; nlinarith [mul_nonneg (mul_nonneg hb hu) hs]

variable {a b c C : ℝ}

theorem tw_shift_le (hb : 0 ≤ b)
    (hC : ∀ s : ℝ, 0 ≤ s → (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) ≤ C * Real.exp (-c * s))
    {τ : ι → ℝ} {i : ι} (hτ : 0 ≤ τ i) (φ : ι → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    tw a b (τ + Pi.single i s) φ ≤ tw a b τ φ * (C * Real.exp (-c * s)) := by
  rw [tw_shift]
  refine mul_le_mul_of_nonneg_left ?_ (tw_pos a b τ φ).le
  have hu : 0 ≤ φ i ^ 2 / 2 + τ i := add_nonneg (by positivity) hτ
  have hE : Real.exp (fq a b (φ i ^ 2 / 2 + τ i) - fq a b (φ i ^ 2 / 2 + τ i + s)) ≤
      Real.exp (-(a * s + b * s ^ 2)) :=
    Real.exp_le_exp.mpr (by linarith [fq_shift_ge (a := a) hb hu hs])
  have h1 : 1 ≤ 1 + 2 * b * s := by nlinarith
  calc _ ≤ Real.exp (-(a * s + b * s ^ 2)) := hE
    _ ≤ (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) :=
        le_mul_of_one_le_left (Real.exp_pos _).le h1
    _ ≤ _ := hC s hs

theorem deriv_tw_shift_le (hb : 0 ≤ b)
    (hC : ∀ s : ℝ, 0 ≤ s → (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) ≤ C * Real.exp (-c * s))
    {τ : ι → ℝ} {i : ι} (hτ : 0 ≤ τ i) (φ : ι → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |fq' a b (φ i ^ 2 / 2 + τ i + s)| * tw a b (τ + Pi.single i s) φ ≤
      ((|a| + 2 * b * τ i + 1) + b * φ i ^ 2) * tw a b τ φ * (C * Real.exp (-c * s)) := by
  rw [tw_shift]
  have hu : 0 ≤ φ i ^ 2 / 2 + τ i := add_nonneg (by positivity) hτ
  have e : (|a| + 2 * b * τ i + 1) + b * φ i ^ 2 = |a| + 2 * b * (φ i ^ 2 / 2 + τ i) + 1 := by
    ring
  rw [e]
  set u := φ i ^ 2 / 2 + τ i with hu_def
  have hE : Real.exp (fq a b u - fq a b (u + s)) ≤ Real.exp (-(a * s + b * s ^ 2)) :=
    Real.exp_le_exp.mpr (by linarith [fq_shift_ge (a := a) hb hu hs])
  have h2bs : 0 ≤ 2 * b * s := by positivity
  have h2bu : 0 ≤ 2 * b * u := by positivity
  have hf : |fq' a b (u + s)| ≤ (|a| + 2 * b * u + 1) * (1 + 2 * b * s) := by
    unfold fq'
    calc |a + 2 * b * (u + s)| ≤ |a| + |2 * b * (u + s)| := abs_add_le _ _
      _ = |a| + 2 * b * u + 2 * b * s := by
          rw [abs_of_nonneg (mul_nonneg (by linarith) (by linarith) : 0 ≤ 2 * b * (u + s))]
          ring
      _ ≤ _ := by nlinarith [abs_nonneg a]
  have hK := hC s hs
  have htw := (tw_pos a b τ φ).le
  have hA : 0 ≤ |a| + 2 * b * u + 1 := by linarith [abs_nonneg a]
  calc |fq' a b (u + s)| * (tw a b τ φ * Real.exp (fq a b u - fq a b (u + s)))
      ≤ ((|a| + 2 * b * u + 1) * (1 + 2 * b * s)) *
          (tw a b τ φ * Real.exp (-(a * s + b * s ^ 2))) :=
        mul_le_mul hf (mul_le_mul_of_nonneg_left hE htw) (by positivity)
          (mul_nonneg hA (by linarith))
    _ = (|a| + 2 * b * u + 1) * tw a b τ φ *
          ((1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2))) := by ring
    _ ≤ (|a| + 2 * b * u + 1) * tw a b τ φ * (C * Real.exp (-c * s)) :=
        mul_le_mul_of_nonneg_left hK (mul_nonneg hA htw)

/-! ## The local-time integration by parts -/

/-- Integration by parts in φ_i at a fixed local time σ:
∫ ∂_i R · W_σ = ∫ R · φ_i f'(φ_i²/2 + σ_i) · W_σ. -/
theorem ibp_fixed (σ : ι → ℝ) (i : ι) {R R' : (ι → ℝ) → ℝ}
    (hR' : ∀ φ, HasLineDerivAt ℝ R (R' φ) φ (Pi.single i 1))
    (hA : Integrable (fun φ => R' φ * tw a b σ φ))
    (hB : Integrable (fun φ => R φ * (φ i * fq' a b (φ i ^ 2 / 2 + σ i)) * tw a b σ φ))
    (hC0 : Integrable (fun φ => R φ * tw a b σ φ)) :
    ∫ φ, R' φ * tw a b σ φ = ∫ φ, R φ * (φ i * fq' a b (φ i ^ 2 / 2 + σ i)) * tw a b σ φ := by
  have hB' : Integrable (fun φ => R φ * (-(φ i * fq' a b (φ i ^ 2 / 2 + σ i)) * tw a b σ φ)) := by
    have := hB.neg
    refine this.congr (Filter.Eventually.of_forall fun φ => ?_)
    simp only [Pi.neg_apply]; ring
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (ι → ℝ)))
    (f := R) (f' := R') (g := tw a b σ)
    (g' := fun φ => -(φ i * fq' a b (φ i ^ 2 / 2 + σ i)) * tw a b σ φ)
    (v := (Pi.single i (1 : ℝ) : ι → ℝ)) (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simpa using hA) (by simpa using hB') (by simpa using hC0)
    (fun φ _ => hR' φ) (fun φ _ => hasLineDerivAt_tw a b σ φ i)
  simp only [ContinuousLinearMap.mul_apply'] at key
  have e1 : ∀ φ, R φ * (-(φ i * fq' a b (φ i ^ 2 / 2 + σ i)) * tw a b σ φ) =
      -(R φ * (φ i * fq' a b (φ i ^ 2 / 2 + σ i)) * tw a b σ φ) := fun φ => by ring
  simp_rw [e1, integral_neg] at key
  linarith

/-- The Fubini integrand F(φ, s) = R(φ) φ_i f'(φ_i²/2 + τ_i + s) W_{τ+s e_i}(φ). -/
def ltF (a b : ℝ) (τ : ι → ℝ) (i : ι) (R : (ι → ℝ) → ℝ) (φ : ι → ℝ) (s : ℝ) : ℝ :=
  R φ * φ i * fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ

/-- Its dominating function in φ (times C e^{−cs} in s). -/
def ltG (a b : ℝ) (τ : ι → ℝ) (i : ι) (R : (ι → ℝ) → ℝ) (φ : ι → ℝ) : ℝ :=
  (|a| + 2 * b * τ i + 1) * |φ i * R φ * tw a b τ φ| + b * |φ i ^ 3 * R φ * tw a b τ φ|

theorem ltF_bound (hb : 0 ≤ b)
    (hC : ∀ s : ℝ, 0 ≤ s → (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) ≤ C * Real.exp (-c * s))
    {τ : ι → ℝ} {i : ι} (hτ : 0 ≤ τ i) (R : (ι → ℝ) → ℝ) (φ : ι → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |ltF a b τ i R φ s| ≤ ltG a b τ i R φ * (C * Real.exp (-c * s)) := by
  have hd' := deriv_tw_shift_le hb hC hτ φ hs
  have htw := tw_pos a b τ φ
  have htw' := tw_pos a b (τ + Pi.single i s) φ
  have h3 : |φ i| ^ 3 = |φ i| * φ i ^ 2 := by rw [← sq_abs (φ i)]; ring
  have hgφ : ltG a b τ i R φ =
      |R φ| * |φ i| * (((|a| + 2 * b * τ i + 1) + b * φ i ^ 2) * tw a b τ φ) := by
    unfold ltG
    rw [abs_mul (φ i ^ 3 * R φ), abs_mul (φ i ^ 3), abs_mul (φ i * R φ), abs_mul (φ i),
      abs_of_pos htw, abs_pow, h3]
    ring
  have hFφ : |ltF a b τ i R φ s| = |R φ| * |φ i| *
      (|fq' a b (φ i ^ 2 / 2 + τ i + s)| * tw a b (τ + Pi.single i s) φ) := by
    unfold ltF
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos htw']
    ring
  rw [hFφ, hgφ, mul_assoc (|R φ| * |φ i|)]
  exact mul_le_mul_of_nonneg_left hd' (by positivity)

theorem continuous_ltF (τ : ι → ℝ) (i : ι) {R : (ι → ℝ) → ℝ} (hRc : Continuous R) :
    Continuous (Function.uncurry (ltF a b τ i R)) := by
  have e : Function.uncurry (ltF a b τ i R) = fun z : (ι → ℝ) × ℝ => R z.1 * z.1 i *
      fq' a b (z.1 i ^ 2 / 2 + τ i + z.2) * (tw a b τ z.1 *
        Real.exp (fq a b (z.1 i ^ 2 / 2 + τ i) - fq a b (z.1 i ^ 2 / 2 + τ i + z.2))) := by
    funext ⟨φ, s⟩; simp only [Function.uncurry_apply_pair, ltF, tw_shift]
  rw [e]; unfold fq fq'; fun_prop

theorem integrable_shift (hb : 0 ≤ b)
    (hC : ∀ s : ℝ, 0 ≤ s → (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) ≤ C * Real.exp (-c * s))
    {τ : ι → ℝ} {i : ι} (hτ : 0 ≤ τ i) {H : (ι → ℝ) → ℝ} (hH : Continuous H)
    (h : Integrable fun φ => H φ * tw a b τ φ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun φ => H φ * tw a b (τ + Pi.single i s) φ := by
  refine (h.abs.mul_const (C * Real.exp (-c * s))).mono'
    ((hH.mul (continuous_tw a b _)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (tw_pos _ _ _ _), abs_mul,
    abs_of_pos (tw_pos _ _ _ _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (tw_shift_le hb hC hτ φ hs) (abs_nonneg _)

/-- The local-time integral: ∫_0^∞ f'(u + s) W_{τ+s e_i} ds = W_τ (since W_{τ+s e_i} → 0). -/
theorem integral_Ioi_tw (hb : 0 ≤ b) (hc : 0 < c)
    (hC : ∀ s : ℝ, 0 ≤ s → (1 + 2 * b * s) * Real.exp (-(a * s + b * s ^ 2)) ≤ C * Real.exp (-c * s))
    {τ : ι → ℝ} {i : ι} (hτ : 0 ≤ τ i) (φ : ι → ℝ) :
    ∫ s in Ioi (0 : ℝ), fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ =
      tw a b τ φ := by
  have hhi : IntegrableOn (fun s : ℝ => C * Real.exp (-c * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul C
  have hderiv : ∀ s, HasDerivAt (fun s => -tw a b (τ + Pi.single i s) φ)
      (fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ) s := fun s => by
    have := (hasDerivAt_tw_shift a b τ φ i s).fun_neg
    convert this using 1; ring
  have hcs : Continuous (fun s => tw a b (τ + Pi.single i s) φ) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_tw_shift a b τ φ i s).continuousAt
  have hio : IntegrableOn (fun s => fq' a b (φ i ^ 2 / 2 + τ i + s) *
      tw a b (τ + Pi.single i s) φ) (Ioi 0) := by
    refine (hhi.const_mul (((|a| + 2 * b * τ i + 1) + b * φ i ^ 2) * tw a b τ φ)).mono' ?_ ?_
    · exact ((by unfold fq'; fun_prop : Continuous fun s => fq' a b (φ i ^ 2 / 2 + τ i + s)).mul
        hcs).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (tw_pos _ _ _ _)]
      exact (deriv_tw_shift_le hb hC hτ φ (le_of_lt hs)).trans (le_of_eq (by ring))
  have htend : Tendsto (fun s => -tw a b (τ + Pi.single i s) φ) atTop (𝓝 0) := by
    have he : Tendsto (fun s : ℝ => Real.exp (-c * s)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    have hlim : Tendsto (fun s => tw a b τ φ * (C * Real.exp (-c * s))) atTop (𝓝 0) := by
      simpa using (he.const_mul C).const_mul (tw a b τ φ)
    have h2 : Tendsto (fun s => tw a b (τ + Pi.single i s) φ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun s => (tw_pos _ _ _ _).le)
        ((eventually_ge_atTop 0).mono fun s hs => tw_shift_le hb hC hτ φ hs)
    simpa using h2.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun s _ => hderiv s) hio htend]
  simp

/-- **One-site local-time integration by parts** (abstract form). For W_τ = ∏_x e^{−f(φ_x²/2+τ_x)},
f(u) = au + bu² (b ≥ 0, and b > 0 or a > 0), τ_i ≥ 0, and R continuous with continuous derivative
R' along e_i and the stated integrability against W_τ:
  ∫ φ_i R W_τ = ∫_0^∞ ds ∫ R' · W_{τ + s e_i}. -/
theorem local_time_ibp (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a) (τ : ι → ℝ) (i : ι)
    (hτ : 0 ≤ τ i) {R R' : (ι → ℝ) → ℝ} (hRc : Continuous R) (hR'c : Continuous R')
    (hR' : ∀ φ, HasLineDerivAt ℝ R (R' φ) φ (Pi.single i 1))
    (h0 : Integrable (fun φ => R φ * tw a b τ φ))
    (h1 : Integrable (fun φ => φ i * R φ * tw a b τ φ))
    (h3 : Integrable (fun φ => φ i ^ 3 * R φ * tw a b τ φ))
    (hd : Integrable (fun φ => R' φ * tw a b τ φ)) :
    ∫ φ, φ i * R φ * tw a b τ φ =
      ∫ s in Ioi (0 : ℝ), ∫ φ, R' φ * tw a b (τ + Pi.single i s) φ := by
  obtain ⟨c, hc, C, hC⟩ := exists_exp_bound hb hab
  have hgi : Integrable (ltG a b τ i R) := (h1.abs.const_mul _).add (h3.abs.const_mul _)
  have hhi : IntegrableOn (fun s : ℝ => C * Real.exp (-c * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul C
  have hFc := continuous_ltF (a := a) (b := b) τ i hRc
  -- product integrability (Fubini)
  have hprod : Integrable (Function.uncurry (ltF a b τ i R))
      ((volume : Measure (ι → ℝ)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (hgi.mul_prod hhi).mono' hFc.aestronglyMeasurable ?_
    have hmem : ∀ᵐ z ∂((volume : Measure (ι → ℝ)).prod (volume.restrict (Ioi (0 : ℝ)))),
        z ∈ (Prod.snd ⁻¹' Ioi (0 : ℝ) : Set ((ι → ℝ) × ℝ)) := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurable_snd measurableSet_Ioi)]
      exact Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with z hz
    rw [Real.norm_eq_abs]
    exact ltF_bound hb hC hτ R z.1 (le_of_lt hz)
  -- the s-integral
  have hinner : ∀ φ, ∫ s in Ioi (0 : ℝ), ltF a b τ i R φ s = φ i * R φ * tw a b τ φ := by
    intro φ
    have e : (fun s => ltF a b τ i R φ s) = fun s => (R φ * φ i) *
        (fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ) := by
      funext s; unfold ltF; ring
    rw [e, integral_const_mul, integral_Ioi_tw hb hc hC hτ φ]
    ring
  -- the φ-integral at fixed s
  have hibp : ∀ s : ℝ, 0 ≤ s →
      ∫ φ, R' φ * tw a b (τ + Pi.single i s) φ = ∫ φ, ltF a b τ i R φ s := by
    intro s hs
    have hσi : (τ + Pi.single i s : ι → ℝ) i = τ i + s := by simp
    have e1 : ∀ φ, R φ * (φ i * fq' a b (φ i ^ 2 / 2 + (τ + Pi.single i s : ι → ℝ) i)) *
        tw a b (τ + Pi.single i s) φ = ltF a b τ i R φ s := by
      intro φ; rw [hσi, ← add_assoc]; unfold ltF; ring
    have hB : Integrable (fun φ => ltF a b τ i R φ s) := by
      refine (hgi.mul_const (C * Real.exp (-c * s))).mono'
        (hFc.comp (Continuous.prodMk continuous_id continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun φ => ?_)
      rw [Real.norm_eq_abs]; exact ltF_bound hb hC hτ R φ hs
    rw [ibp_fixed (τ + Pi.single i s) i hR' (integrable_shift hb hC hτ hR'c hd hs)
      (hB.congr (Filter.Eventually.of_forall fun φ => (e1 φ).symm))
      (integrable_shift hb hC hτ hRc h0 hs)]
    exact integral_congr_ae (Filter.Eventually.of_forall e1)
  calc ∫ φ, φ i * R φ * tw a b τ φ = ∫ φ, ∫ s in Ioi (0 : ℝ), ltF a b τ i R φ s := by
        simp_rw [hinner]
    _ = ∫ s in Ioi (0 : ℝ), ∫ φ, ltF a b τ i R φ s := integral_integral_swap hprod
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun s hs => (hibp s (le_of_lt hs)).symm

/-! ## The BFS form: a ferromagnetic pair interaction exp(Σ K φφ) -/

/-- The pair exponent Q_K(φ) = Σ_{x,y} K_xy φ_x φ_y. -/
def quadE (K : ι → ι → ℝ) (φ : ι → ℝ) : ℝ := ∑ x, ∑ y, K x y * φ x * φ y

@[fun_prop]
theorem continuous_quadE (K : ι → ι → ℝ) : Continuous (quadE K) := by
  unfold quadE; fun_prop

/-- ∂_i Q_K = Σ_j (K_ij + K_ji) φ_j. -/
theorem hasLineDerivAt_quadE (K : ι → ι → ℝ) (φ : ι → ℝ) (i : ι) :
    HasLineDerivAt ℝ (quadE K) (∑ j, (K i j + K j i) * φ j) φ (Pi.single i 1) := by
  unfold HasLineDerivAt quadE
  have h : ∀ x : ι, HasDerivAt (fun t : ℝ => (φ + t • (Pi.single i (1 : ℝ) : ι → ℝ)) x)
      ((Pi.single i (1 : ℝ) : ι → ℝ) x) 0 := by
    intro x
    have e : (fun t : ℝ => (φ + t • (Pi.single i (1 : ℝ) : ι → ℝ)) x) =
        fun t => φ x + t * (Pi.single i (1 : ℝ) : ι → ℝ) x := by
      funext t; simp
    rw [e]
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const ((Pi.single i (1 : ℝ) : ι → ℝ) x)).const_add
      (φ x)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun x _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun y _ => ((h x).const_mul (K x y)).fun_mul (h y)
  convert hs using 1
  simp only [zero_smul, add_zero, Finset.sum_add_distrib]
  have e1 : ∀ x, ∑ y, K x y * (Pi.single i (1 : ℝ) : ι → ℝ) x * φ y =
      if x = i then ∑ y, K i y * φ y else 0 := by
    intro x
    by_cases hx : x = i
    · subst hx; simp
    · simp [hx]
  have e2 : ∀ x, ∑ y, K x y * φ x * (Pi.single i (1 : ℝ) : ι → ℝ) y = K x i * φ x := by
    intro x
    rw [Finset.sum_eq_single i]
    · simp
    · intro y _ hy; simp [Pi.single_eq_of_ne hy]
    · simp
  simp only [e1, e2, Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_mul,
    Finset.sum_add_distrib]

/-- **Local-time integration by parts, BFS form.** With [F]_τ = ∫ F e^{Q_K} W_τ and J = K + Kᵀ:
  [φ_i G]_τ = ∫_0^∞ ds [∂_i G + Σ_j J_ij φ_j G]_{τ + s e_i}. -/
theorem local_time_ibp_bfs (hb : 0 ≤ b) (hab : 0 < b ∨ 0 < a) (K : ι → ι → ℝ) (τ : ι → ℝ)
    (i : ι) (hτ : 0 ≤ τ i) {G G' : (ι → ℝ) → ℝ} (hGc : Continuous G) (hG'c : Continuous G')
    (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1))
    (h0 : Integrable fun φ => G φ * Real.exp (quadE K φ) * tw a b τ φ)
    (h1 : Integrable fun φ => φ i * G φ * Real.exp (quadE K φ) * tw a b τ φ)
    (h3 : Integrable fun φ => φ i ^ 3 * G φ * Real.exp (quadE K φ) * tw a b τ φ)
    (hd : Integrable fun φ =>
      (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ) * tw a b τ φ) :
    ∫ φ, φ i * G φ * Real.exp (quadE K φ) * tw a b τ φ =
      ∫ s in Ioi (0 : ℝ), ∫ φ, (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) *
        Real.exp (quadE K φ) * tw a b (τ + Pi.single i s) φ := by
  have hR' : ∀ φ, HasLineDerivAt ℝ (fun φ => G φ * Real.exp (quadE K φ))
      ((G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ)) φ
      (Pi.single i 1) := by
    intro φ
    have hQ := hasLineDerivAt_quadE K φ i
    have hG := hG' φ
    unfold HasLineDerivAt at hQ hG ⊢
    have := hG.fun_mul hQ.exp
    convert this using 1
    simp only [zero_smul, add_zero, Finset.mul_sum]
    rw [add_mul, Finset.sum_mul]
    have : ∀ j, (K i j + K j i) * (φ j * G φ) * Real.exp (quadE K φ) =
        G φ * (Real.exp (quadE K φ) * ((K i j + K j i) * φ j)) := fun j => by ring
    simp only [this]
  have := local_time_ibp hb hab τ i hτ (R := fun φ => G φ * Real.exp (quadE K φ))
    (R' := fun φ => (G' φ + ∑ j, (K i j + K j i) * (φ j * G φ)) * Real.exp (quadE K φ))
    (by fun_prop) (by fun_prop) hR'
    (by simpa only [mul_assoc] using h0) (by simpa only [mul_assoc] using h1)
    (by simpa only [mul_assoc] using h3) hd
  simpa only [mul_assoc] using this

/-! ## The τ-family as a mass shift -/

/-- W_τ = e^{−Σ_x f(τ_x)} · e^{−b Σ_x τ_x φ_x²} · W_0: raising the local time τ_x raises the
mass² at x by 2bτ_x (the coefficient of φ_x²/2), with the prefactor e^{−f(τ_x)}. -/
theorem tw_mass_shift (a b : ℝ) (τ φ : ι → ℝ) :
    tw a b τ φ = Real.exp (-∑ x, fq a b (τ x)) * Real.exp (-(b * ∑ x, τ x * φ x ^ 2)) *
      tw a b 0 φ := by
  unfold tw
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Pi.zero_apply, add_zero, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by unfold fq; ring

theorem tw_le_tw_zero (hb : 0 ≤ b) {τ : ι → ℝ} (hτ : ∀ x, 0 ≤ τ x) (φ : ι → ℝ) :
    tw a b τ φ ≤ Real.exp (-∑ x, fq a b (τ x)) * tw a b 0 φ := by
  rw [tw_mass_shift]
  have h1 : Real.exp (-(b * ∑ x, τ x * φ x ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hb (Finset.sum_nonneg fun x _ => mul_nonneg (hτ x) (sq_nonneg _))
  have h2 := (tw_pos a b 0 φ).le
  have h3 := (Real.exp_pos (-∑ x, fq a b (τ x))).le
  calc _ ≤ Real.exp (-∑ x, fq a b (τ x)) * 1 * tw a b 0 φ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2
    _ = _ := by ring

/-! ## Growth classes -/

theorem abs_le_exp_sum (φ : ι → ℝ) (j : ι) : |φ j| ≤ Real.exp (∑ x, |φ x|) :=
  (Finset.single_le_sum (f := fun x => |φ x|) (fun x _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (by linarith [Real.add_one_le_exp (∑ x, |φ x|)])

theorem growth_mul_coord {G : (ι → ℝ) → ℝ} {C a : ℝ}
    (hG : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) (j : ι) (φ : ι → ℝ) :
    |φ j * G φ| ≤ C * Real.exp ((a + 1) * ∑ x, |φ x|) := by
  have hC : 0 ≤ C * Real.exp (a * ∑ x, |φ x|) := (abs_nonneg _).trans (hG φ)
  rw [abs_mul]
  calc |φ j| * |G φ| ≤ Real.exp (∑ x, |φ x|) * (C * Real.exp (a * ∑ x, |φ x|)) :=
        mul_le_mul (abs_le_exp_sum φ j) (hG φ) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [add_mul, one_mul, Real.exp_add]; ring

theorem growth_mul_cube {G : (ι → ℝ) → ℝ} {C a : ℝ}
    (hG : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) (j : ι) (φ : ι → ℝ) :
    |φ j ^ 3 * G φ| ≤ C * Real.exp ((a + 3) * ∑ x, |φ x|) := by
  have hC : 0 ≤ C * Real.exp (a * ∑ x, |φ x|) := (abs_nonneg _).trans (hG φ)
  have h3 : |φ j| ^ 3 ≤ Real.exp (3 * ∑ x, |φ x|) := by
    have := pow_le_pow_left₀ (abs_nonneg (φ j)) (abs_le_exp_sum φ j) 3
    rwa [← Real.exp_nat_mul, Nat.cast_ofNat] at this
  rw [abs_mul, abs_pow]
  calc |φ j| ^ 3 * |G φ| ≤ Real.exp (3 * ∑ x, |φ x|) * (C * Real.exp (a * ∑ x, |φ x|)) :=
        mul_le_mul h3 (hG φ) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [add_mul, Real.exp_add]; ring

/-! ## Evaluating quadratic forms on e_x and e_x + e_y -/

theorem quad_single (M : ι → ι → ℝ) (x : ι) :
    ∑ u, ∑ v, M u v * (Pi.single x (1 : ℝ) : ι → ℝ) u * (Pi.single x (1 : ℝ) : ι → ℝ) v =
      M x x := by
  simp [Pi.single_apply]

theorem quad_pair (M : ι → ι → ℝ) (x y : ι) :
    ∑ u, ∑ v, M u v * (Pi.single x (1 : ℝ) + Pi.single y (1 : ℝ) : ι → ℝ) u *
      (Pi.single x (1 : ℝ) + Pi.single y (1 : ℝ) : ι → ℝ) v =
      M x x + M x y + M y x + M y y := by
  simp [Pi.single_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem sq_single (x : ι) : ∑ u, (Pi.single x (1 : ℝ) : ι → ℝ) u ^ 2 = 1 := by
  simp [Pi.single_apply]

theorem sq_pair {x y : ι} (hxy : x ≠ y) :
    ∑ u, (Pi.single x (1 : ℝ) + Pi.single y (1 : ℝ) : ι → ℝ) u ^ 2 = 2 := by
  simp [Pi.single_apply, add_sq, Finset.sum_add_distrib, hxy.symm]
  norm_num

end PP2LocalTime

/-! ## The quartic Dirichlet-box model -/

namespace PP2Target

open PP2LocalTime PP2Griffiths

variable {n k : ℕ}

/-- α = 4 + ε² m₀² − 12 λ ε² c (c = freeVar): the coefficient of s = φ²/2 in the site exponent
(Dirichlet diagonal 4, mass, and the Wick counterterm −6λε²c φ²). -/
def alphaQ (n : ℕ) (m₀ lam : ℝ) : ℝ :=
  4 + spacing n ^ 2 * m₀ ^ 2 - 12 * lam * spacing n ^ 2 * freeVar n m₀

/-- β = 4 λ ε²: the coefficient of s² (λε² φ⁴ = 4λε² s²). -/
def betaQ (n : ℕ) (lam : ℝ) : ℝ := 4 * lam * spacing n ^ 2

/-- The symmetrised nearest-neighbour coupling J_ij = Jnn_ij + Jnn_ji (= ∂_i of the pair
exponent; 1 for nearest neighbours, 0 on the diagonal). -/
def Jsym (n k : ℕ) (x y : DSite n k) : ℝ := Jnn n k x y + Jnn n k y x

/-- The pair exponent in two forms: Σ Jnn φφ − 2 Σ φ² = ½ Σ_{x,y} bondJ_xy φ_x φ_y
(both are −½ dirAction at m₀ = 0). -/
theorem quad_Jnn_bondJ (φ : DField n k) :
    quadE (Jnn n k) φ - 2 * ∑ x, φ x ^ 2 = (1 / 2) * ∑ x, ∑ y, bondJ n k x y * φ x * φ y := by
  have h1 := neg_half_dirAction (n := n) (k := k) 0 φ
  rw [coupling_eq, diagPart_eq] at h1
  simp only [cdiag_eq_four, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    Finset.sum_const_zero, mul_zero, zero_div, sub_zero, ← Finset.mul_sum] at h1
  have e : ∑ x, ∑ y, bondJ n k x y * φ x * φ y = -(dirAction n k 0 φ) := by
    rw [dirAction_eq_quad]
    simp only [dotProduct, Matrix.mulVec]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold bondJ; ring
  rw [e]
  unfold quadE
  linarith

theorem bondJ_diag (x : DSite n k) : bondJ n k x x = -4 := by
  have hε := (spacing_pos n).ne'
  rw [bondJ, dirOp_diag]
  field_simp
  ring

/-- The nearest-neighbour matrix of `dweight_eq_ferro` has zero diagonal. -/
theorem Jnn_diag (x : DSite n k) : Jnn n k x x = 0 := by
  have h := quad_Jnn_bondJ (n := n) (k := k) (Pi.single x 1)
  unfold quadE at h
  rw [quad_single, quad_single, sq_single, bondJ_diag] at h
  linarith

theorem Jsym_diag (x : DSite n k) : Jsym n k x x = 0 := by
  rw [Jsym, Jnn_diag, add_zero]

/-- **The BFS coupling is the Simon–Lieb coupling:** J_xy = Jnn_xy + Jnn_yx = bondJ_xy for x ≠ y
(so it is 1 for nearest neighbours and 0 otherwise, `dirOp_nn`/`dirOp_far`). -/
theorem Jsym_eq_bondJ {x y : DSite n k} (hxy : x ≠ y) : Jsym n k x y = bondJ n k x y := by
  have h := quad_Jnn_bondJ (n := n) (k := k) (Pi.single x 1 + Pi.single y 1)
  unfold quadE at h
  rw [quad_pair, quad_pair, sq_pair hxy, bondJ_diag, bondJ_diag, Jnn_diag, Jnn_diag,
    bondJ_symm y x] at h
  unfold Jsym
  linarith

/-- The unnormalised τ-shifted expectation [G]_τ = ∫ G · e^{Σ Jnn φφ} · ∏_x e^{−f(φ_x²/2+τ_x)}
(BFS's [·]_t, with g(S²) = e^{−f(S²/2)} and their g(S² + 2t) = e^{−f(S²/2 + t)}). -/
def tauInt (n k : ℕ) (m₀ lam : ℝ) (τ : DField n k) (G : DField n k → ℝ) : ℝ :=
  ∫ φ, G φ * Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ

/-- **The site exponent of the quartic weight.** qweight = e^{−|Λ|·3λε²c²} · e^{Σ Jnn φφ} · W_0,
with f(s) = αs + βs²: the Wick constant 3λε²c² per site factors out. -/
theorem qweight_eq_tw (m₀ lam : ℝ) (φ : DField n k) :
    qweight n k m₀ lam φ =
      Real.exp (-(Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2))) *
        (Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) := by
  rw [qweight, dweight_eq_ferro]
  simp only [siteWeight_eq, wickPoly_X4]
  rw [← Real.exp_sum]
  unfold tw quadE
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have h : ∀ x : DSite n k, -((4 + spacing n ^ 2 * m₀ ^ 2) * φ x ^ 2) / 2
      - lam * spacing n ^ 2 * (φ x ^ 4 - 6 * freeVar n m₀ * φ x ^ 2 + 3 * freeVar n m₀ ^ 2) =
      -(3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)
        - fq (alphaQ n m₀ lam) (betaQ n lam) (φ x ^ 2 / 2 + (0 : DField n k) x) := by
    intro x; simp only [Pi.zero_apply, add_zero]; unfold fq alphaQ betaQ; ring
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- At τ = 0 the family is the quartic measure: [G]_0 = e^{|Λ|·3λε²c²} ∫ G · qweight. -/
theorem tauInt_zero (m₀ lam : ℝ) (G : DField n k → ℝ) :
    tauInt n k m₀ lam 0 G =
      Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
        ∫ φ, G φ * qweight n k m₀ lam φ := by
  rw [tauInt, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [qweight_eq_tw, Real.exp_neg]
  field_simp

theorem eTw_zero (m₀ lam : ℝ) (φ : DField n k) :
    Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ =
      Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
        qweight n k m₀ lam φ := by
  rw [qweight_eq_tw, Real.exp_neg]
  field_simp

theorem qweight_le_gauss {m₀ lam : ℝ} (hlam : 0 ≤ lam) (φ : DField n k) :
    qweight n k m₀ lam φ ≤
      Real.exp (lam * spacing n ^ 2 * (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2))) *
        PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ := by
  rw [gaussWeight_dirAction, qweight, dweight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsum : -(Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)) ≤
      ∑ x : DSite n k, wickPoly (Polynomial.X ^ 4) (freeVar n m₀) (φ x) := by
    have := Finset.sum_le_sum (s := Finset.univ)
      (fun x (_ : x ∈ Finset.univ) => wickPoly_X4_ge (freeVar n m₀) (φ x))
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hc : 0 ≤ lam * spacing n ^ 2 := by have := spacing_pos n; positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hc]

theorem betaQ_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : 0 ≤ betaQ n lam := by
  unfold betaQ; have := spacing_pos n; positivity

/-- Gaussian domination of the τ-shifted weight (τ ≥ 0, λ ≥ 0). -/
theorem tauWeight_le {m₀ lam : ℝ} (hlam : 0 ≤ lam) {τ : DField n k} (hτ : ∀ x, 0 ≤ τ x)
    (φ : DField n k) :
    Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ ≤
      (Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x)) *
        Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
        Real.exp (lam * spacing n ^ 2 * (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)))) *
        PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ := by
  have h1 := tw_le_tw_zero (a := alphaQ n m₀ lam) (betaQ_nonneg (n := n) hlam) hτ φ
  have hE := (Real.exp_pos (quadE (Jnn n k) φ)).le
  have h2 := qweight_le_gauss (m₀ := m₀) hlam φ
  calc Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ
      ≤ Real.exp (quadE (Jnn n k) φ) * (Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x))
          * tw (alphaQ n m₀ lam) (betaQ n lam) 0 φ) := mul_le_mul_of_nonneg_left h1 hE
    _ = Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x)) *
          Real.exp (Fintype.card (DSite n k) * (3 * lam * spacing n ^ 2 * freeVar n m₀ ^ 2)) *
          qweight n k m₀ lam φ := by
        rw [mul_assoc (Real.exp (-∑ x, fq (alphaQ n m₀ lam) (betaQ n lam) (τ x))), ← eTw_zero]
        ring
    _ ≤ _ := by
        rw [mul_assoc _ (Real.exp (lam * spacing n ^ 2 * _))]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Integrability in the τ-family** for exponentially bounded observables (m₀ ≠ 0, λ ≥ 0, τ ≥ 0):
this covers all polynomials. -/
theorem integrable_tau {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) {τ : DField n k}
    (hτ : ∀ x, 0 ≤ τ x) {H : DField n k → ℝ} (hH : Continuous H) (C a : ℝ)
    (hHb : ∀ φ, |H φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) :
    Integrable fun φ => H φ * Real.exp (quadE (Jnn n k) φ) *
      tw (alphaQ n m₀ lam) (betaQ n lam) τ φ := by
  obtain ⟨K, hK0, hKb⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : DField n k,
      Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ ≤
        K * PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ :=
    ⟨_, by positivity, tauWeight_le hlam hτ⟩
  refine PP2GaussIBP.integrable_of_le_expAbs (scaledOp_posDef hm)
    ((by fun_prop : Continuous fun φ => H φ * Real.exp (quadE (Jnn n k) φ) *
      tw (alphaQ n m₀ lam) (betaQ n lam) τ φ).aestronglyMeasurable) (C * K) a fun φ => ?_
  have hC : 0 ≤ C * Real.exp (a * ∑ x, |φ x|) := (abs_nonneg _).trans (hHb φ)
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (tw_pos _ _ _ _), mul_assoc]
  calc |H φ| * (Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ)
      ≤ (C * Real.exp (a * ∑ x, |φ x|)) * (K * PP2GaussIBP.gaussWeight (scaledOp n k m₀) φ) :=
        mul_le_mul (hHb φ) (hKb φ) (mul_pos (Real.exp_pos _) (tw_pos _ _ _ _)).le hC
    _ = _ := by ring

theorem shift_nonneg {τ : DField n k} (hτ : ∀ x, 0 ≤ τ x) (i : DSite n k) {s : ℝ} (hs : 0 ≤ s) :
    ∀ x, 0 ≤ (τ + Pi.single i s : DField n k) x := by
  intro x
  by_cases hx : x = i
  · subst hx; simp only [Pi.add_apply, Pi.single_eq_same]; linarith [hτ x]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hx, add_zero]; exact hτ x

/-- **R2: the one-site local-time integration by parts for the quartic Dirichlet-box model**
(BFS CMP 83, the generator of Theorem 2.2 / (5.5)). For m₀ ≠ 0, λ ≥ 0, τ ≥ 0, any site i, and G
continuous with continuous e_i-derivative G', both bounded by C e^{a Σ|φ|}:
  [φ_i G]_τ = ∫_0^∞ ds ( [∂_i G]_{τ+s e_i} + Σ_j J_ij [φ_j G]_{τ+s e_i} ). -/
theorem tau_ibp_quartic {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (τ : DField n k)
    (hτ : ∀ x, 0 ≤ τ x) (i : DSite n k) {G G' : DField n k → ℝ} (hGc : Continuous G)
    (hG'c : Continuous G') (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1)) (C a : ℝ)
    (hGb : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|))
    (hG'b : ∀ φ, |G' φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) :
    tauInt n k m₀ lam τ (fun φ => φ i * G φ) =
      ∫ s in Ioi (0 : ℝ), (tauInt n k m₀ lam (τ + Pi.single i s) G' +
        ∑ j, Jsym n k i j * tauInt n k m₀ lam (τ + Pi.single i s) (fun φ => φ j * G φ)) := by
  have hb := betaQ_nonneg (n := n) hlam
  have hab : 0 < betaQ n lam ∨ 0 < alphaQ n m₀ lam := by
    rcases hlam.lt_or_eq with h | h
    · left; unfold betaQ; have := spacing_pos n; positivity
    · right; subst h; unfold alphaQ; have := spacing_pos n
      simp only [zero_mul, mul_zero, sub_zero]; positivity
  have hcoord : ∀ j, Continuous fun φ : DField n k => φ j * G φ :=
    fun j => (continuous_apply j).mul hGc
  have hpieces : ∀ σ : DField n k, (∀ x, 0 ≤ σ x) →
      (Integrable fun φ => G' φ * Real.exp (quadE (Jnn n k) φ) *
        tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) ∧
      ∀ j, Integrable fun φ => φ j * G φ * Real.exp (quadE (Jnn n k) φ) *
        tw (alphaQ n m₀ lam) (betaQ n lam) σ φ :=
    fun σ hσ => ⟨integrable_tau hm hlam hσ hG'c C a hG'b,
      fun j => integrable_tau hm hlam hσ (hcoord j) C (a + 1) (growth_mul_coord hGb j)⟩
  have hsplit : ∀ σ : DField n k, (∀ x, 0 ≤ σ x) →
      (Integrable fun φ => (G' φ + ∑ j, (Jnn n k i j + Jnn n k j i) * (φ j * G φ)) *
        Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) ∧
      ∫ φ, (G' φ + ∑ j, (Jnn n k i j + Jnn n k j i) * (φ j * G φ)) *
        Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ =
      tauInt n k m₀ lam σ G' + ∑ j, Jsym n k i j * tauInt n k m₀ lam σ (fun φ => φ j * G φ) := by
    intro σ hσ
    obtain ⟨I', Ij⟩ := hpieces σ hσ
    have e : (fun φ => (G' φ + ∑ j, (Jnn n k i j + Jnn n k j i) * (φ j * G φ)) *
        Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) =
        fun φ => G' φ * Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) σ φ +
          ∑ j, Jsym n k i j * (φ j * G φ * Real.exp (quadE (Jnn n k) φ) *
            tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) := by
      funext φ
      rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by unfold Jsym; ring
    have hS : Integrable fun φ => ∑ j, Jsym n k i j * (φ j * G φ * Real.exp (quadE (Jnn n k) φ) *
        tw (alphaQ n m₀ lam) (betaQ n lam) σ φ) :=
      integrable_finsetSum _ fun j _ => (Ij j).const_mul _
    refine ⟨e ▸ I'.add hS, ?_⟩
    rw [e, integral_add I' hS, integral_finsetSum _ fun j _ => (Ij j).const_mul _]
    unfold tauInt
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have main := local_time_ibp_bfs hb hab (Jnn n k) τ i (hτ i) hGc hG'c hG'
    (integrable_tau hm hlam hτ hGc C a hGb)
    (integrable_tau hm hlam hτ (hcoord i) C (a + 1) (growth_mul_coord hGb i))
    (integrable_tau hm hlam hτ (((continuous_apply i).pow 3).mul hGc) C (a + 3)
      (growth_mul_cube hGb i))
    (hsplit τ hτ).1
  have lhs : tauInt n k m₀ lam τ (fun φ => φ i * G φ) = ∫ φ, φ i * G φ *
      Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ := rfl
  rw [lhs, main]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    (hsplit _ (shift_nonneg hτ i (le_of_lt hs))).2

theorem sum_Jsym_eq (i : DSite n k) (c : DSite n k → ℝ) :
    ∑ j, Jsym n k i j * c j = ∑ j ∈ Finset.univ.erase i, bondJ n k i j * c j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Jsym_diag, zero_mul, zero_add]
  exact Finset.sum_congr rfl fun j hj =>
    by rw [Jsym_eq_bondJ (Finset.ne_of_mem_erase hj).symm]

/-- **R2 with the Simon–Lieb coupling:** the same identity with Σ_{j ≠ i} bondJ_ij. -/
theorem tau_ibp_quartic_bondJ {m₀ lam : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (τ : DField n k)
    (hτ : ∀ x, 0 ≤ τ x) (i : DSite n k) {G G' : DField n k → ℝ} (hGc : Continuous G)
    (hG'c : Continuous G') (hG' : ∀ φ, HasLineDerivAt ℝ G (G' φ) φ (Pi.single i 1)) (C a : ℝ)
    (hGb : ∀ φ, |G φ| ≤ C * Real.exp (a * ∑ x, |φ x|))
    (hG'b : ∀ φ, |G' φ| ≤ C * Real.exp (a * ∑ x, |φ x|)) :
    tauInt n k m₀ lam τ (fun φ => φ i * G φ) =
      ∫ s in Ioi (0 : ℝ), (tauInt n k m₀ lam (τ + Pi.single i s) G' +
        ∑ j ∈ Finset.univ.erase i,
          bondJ n k i j * tauInt n k m₀ lam (τ + Pi.single i s) (fun φ => φ j * G φ)) := by
  rw [tau_ibp_quartic hm hlam τ hτ i hGc hG'c hG' C a hGb hG'b]
  simp_rw [sum_Jsym_eq]

end PP2Target


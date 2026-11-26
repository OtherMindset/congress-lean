import LongTable.P_mwwgf2cx_iollxj
import LongTable.P_mwwgf1y3_auszzz
import LongTable.P_mwwgf1nl_r5zhai

/-!
Part A of PP2SimonLieb2 (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb2.lean)
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

end PP2LocalTime

end

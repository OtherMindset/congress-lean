import Mathlib

/-!
Long Table, Claude council, target T2b (continuum sharpness for φ⁴₂ via a mass-derivative ABF
inequality), first formal lemma: the model-free ABF extrapolation step (Aizenman–Barsky–Fernández
1987, §4–5), for an abstract magnetisation m(μ, h), h > 0. Pure real analysis, no model.

SETTING. m : ℝ → ℝ → ℝ, arguments (μ, h); the ordered side is μ < μc. All hypotheses are only
used at h > 0. The ABF inequality, with (a/3)∂_μ(m³) = a m² ∂_μ m and an error e m³ (e ≥ 0,
e = O(γ²) for Kac models):
    m ≤ h ∂ₕm − a m² ∂_μ m + e m³.                                                    (ABF)
ROUTE (paper first). Write G(μ, m) = h/m (inverse susceptibility as a function of the level m).
Then (ABF) is the LINEAR first-order inequality (1 − e m²) ∂_m G − a m ∂_μ G ≤ e m G, whose
characteristics are dμ/dm = −a m/(1 − e m²): G is (up to the Gronwall factor
√((1−ex²)/(1−es²)) ≤ exp(e(s²−x²)/(2(1−es²)))) nonincreasing along them. Rather than inverting m
(needs ∂ₕm > 0), the formal proof runs the characteristic in the original variables and closes it
by a barrier (first-crossing) argument. The integrated statement is the definition
  `abf_Char m a e`: for 0 < h, 0 < x ≤ m(μ,h), x ≤ s, e s² < 1, and every target point with
    μ' < μ − a(s² − x²)/(2(1 − e s²))   and   h' > h (s/x) exp(e(s² − x²)/(2(1 − e s²))),
  one has s ≤ m(μ', h').
(Start at a level x attained at (μ, h); following the characteristic to level s moves μ DOWN by
a(s²−x²)/2 (to leading order) and h up by the factor s/x, i.e. h/m is not increased.)
It is stated with STRICT (open) targets so that it passes to pointwise limits with no continuity
of the limit (see `abf_char_of_tendsto`); for continuous m it is equivalent to the closed form.
The two extrapolations are then two-line consequences:
(i) from (μ0, h) with μ0 ∈ (μ, μc) and x/h = χ(μ0,h) huge, the characteristic to level s lands at
    μ0 − a s²/(2(1−es²)) ≥ μ and at h' = (h/x)·s·E → 0: so m(μ, 0⁺) ≥ s whenever
    a s²/(2(1−es²)) < μc − μ. Only DIVERGENCE of χ is used, no rate (the χ-rate problem of the
    rectangle-integration route ∫∫ dμ d(log h) disappears in these variables);
(ii) from (μ0, h) with μ0 = μc + d, d > a s²/(2(1−es²)), and χ(μ0,h) ≥ κ/d, the characteristic
    reaches μc at h' ≈ d s E/κ ≈ a s³/(2κ): m(μc, h)³ ≳ 2κh/a.

FORMALIZED (all `abf_`-prefixed; no sorry, axioms propext / Classical.choice / Quot.sound).
* Part B (one smooth model ⟹ characteristic form). `abf_char_of_pde`: if m is jointly
  (Fréchet) differentiable at every (μ, h), h > 0, with partials mμ, mh, m is monotone in h and
  antitone in μ (h > 0), and (ABF) holds pointwise, then `abf_Char m a e` (a, e ≥ 0). Proof:
  `abf_partial_mu_nonpos` (∂_μ m ≤ 0 from antitonicity), `abf_barrier`: along the steepened
  characteristic μ(s) = μ0 − α a Q (s² − x²)/2, h(s) = h0 exp(α(log(s/x) + eQ(s² − x²)/2)),
  Q = 1/(1 − eS²), α > 1, the function s ↦ m(μ(s), h(s)) − s has derivative ≥ α − 1 > 0 at every
  zero (uses (ABF), ∂_μ m ≤ 0 and Q(1 − es²) ≥ 1 for s ≤ S), so Mathlib's
  `image_le_of_deriv_right_lt_deriv_boundary'` gives m(μ(S), h(S)) ≥ S; then α ↓ 1 by continuity
  in α plus monotonicity of m (this is where the strict targets come from). No ∂ₕm > 0 needed.
* Limits. `abf_char_of_tendsto`: if M_i → m pointwise on h > 0 along any NeBot filter, A_i → a,
  E_i → e, and eventually `abf_Char (M i) (A i) (E i)`, then `abf_Char m a e`.
* Part A (i). `abf_spontaneous_magnetization`: with a > 0, e ≥ 0, m monotone in h, antitone in μ,
  GHS form h ↦ m/h nonincreasing, `abf_Char m a e`, and sup_{h>0} m(μ0,h)/h = ∞ for every
  μ0 < μc: for all μ < μc and h > 0,
      2(μc − μ)/(a + 2e(μc − μ)) ≤ m(μ, h)²         (`_e0`: 2(μc − μ)/a ≤ m(μ, h)²);
  `abf_spontaneous_magnetization_lim`: the same for L = lim_{h↓0} m(μ,h);
  `abf_tendsto_zero_plus`: the limit exists (= inf_{h>0} m(μ,h)) if m ≥ 0 and m is monotone in h.
  Explicit c = 2 (e = 0); c = 2/(1 + 2e(μc − μ)/a) in general. (β ≤ 1/2.)
* Part A (ii). `abf_critical_level` (parametric, all e ≥ 0): under the same hypotheses with
  `hdis`: for μ0 > μc, ∃ h > 0, m(μ0,h)/h ≥ κ/(μ0 − μc) (κ > 0) [the mean-field bound γ ≥ 1 on
  the disordered side], for s > 0, e s² < 1 and a s³ exp(es²/(2(1−es²))) < 2κ(1 − es²)h,
      s ≤ m(μc, h).
  `abf_critical_cube` (e = 0): 2κh/a ≤ m(μc,h)³; `abf_critical_rpow` (e = 0):
  (2κ/a)^{1/3} h^{1/3} ≤ m(μc, h), i.e. c' = (2κ/a)^{1/3} (δ ≥ 3);
  `abf_critical_cube_err` (e ≥ 0): κh/(2a) ≤ m(μc,h)³ whenever 8e³(κh/(2a))² ≤ 1.

WHY EACH HYPOTHESIS IS NATURAL FOR LIMITS OF LATTICE / KAC MODELS. Monotonicity in h and μ
(Griffiths I/II for the ferromagnetic φ⁴ measure with mass term +μ Σφ²/2: ∂_μ m = −½Σ⟨φ₀;φ_x²⟩ ≤ 0)
and GHS (m concave in h > 0 with m(0⁺) ≥ 0 ⟹ m/h nonincreasing) are pointwise non-strict
inequalities: they pass to any pointwise limit, Λ ↑ ℤ² and then γ → 0. (ABF) itself and
differentiability are available only for each finite-volume / fixed-γ model; `abf_char_of_pde`
converts them, model by model, into `abf_Char`, which `abf_char_of_tendsto` carries to the limit
(error coefficient e_γ → 0 allowed), with no smoothness or continuity of the limit. χ-divergence
is the definition μc := sup{μ : χ(μ) = ∞} (sup over h of m/h; by GHS it equals lim_{h↓0}).
GHS is used only to pass from "some h" to "all smaller h" in the χ hypotheses.

NOT formalized.
* The ABF inequality, GHS, Griffiths monotonicity, differentiability for φ⁴₂ / Kac models (inputs).
* The "γ ≥ 1" input `hdis` of (ii). It is NECESSARY, not a convenience: under all the other
  hypotheses (even with equality in (ABF) and χ(μc,0⁺) = ∞) δ ≥ 3 can fail. Paper counterexample
  (e = 0, t = −μ): G(t, m) := Φ(t − a m²/2) with Φ(u) = (t_c − u)₊^p, p > 1, i.e. h = m·G; it is
  monotone, GHS, solves a m ∂_t G + ∂_m G = 0, χ = ∞ for t ≥ t_c, and m(t_c,h) ~ h^{1/(1+2p)}.
  (ABF is linear in G, so no constant c' can come from scale-invariant hypotheses.) The natural
  source of `hdis` is the Aizenman–Simon/Lebowitz-type inequality |∂_μ χ| ≤ C χ² integrated
  from μc (where χ = ∞): χ(μ) ≥ 1/(C(μ − μc)), κ = 1/C. Not done here.
* The closed (non-strict) form of `abf_Char` for discontinuous limits; that m(μ,0⁺) > 0 for some
  μ < μc in the absence of χ-divergence (no such claim is made).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Filter Topology Set

noncomputable section

/-! ## The characteristic form of the ABF inequality -/

/-- The ABF differential inequality `m ≤ h ∂ₕm − a m² ∂_μ m + e m³`, integrated along its
characteristics and stated with OPEN targets (see the header): starting from any level
`0 < x ≤ m μ h`, the level `s ≥ x` is reached at every point strictly beyond the
characteristic end point. -/
def abf_Char (m : ℝ → ℝ → ℝ) (a e : ℝ) : Prop :=
  ∀ μ h x s μ' h' : ℝ, 0 < h → 0 < x → x ≤ m μ h → x ≤ s → e * s ^ 2 < 1 →
    μ' < μ - a * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2)) →
    h * (s / x) * Real.exp (e * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2))) < h' →
    s ≤ m μ' h'

/-! ## Part B: the PDE implies the characteristic form -/

lemma abf_partial_mu_nonpos (m mμ mh : ℝ → ℝ → ℝ)
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hdiff : ∀ μ h, 0 < h → HasFDerivAt (fun p : ℝ × ℝ => m p.1 p.2)
      (mμ μ h • ContinuousLinearMap.fst ℝ ℝ ℝ + mh μ h • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ, h))
    (μ h : ℝ) (hh : 0 < h) : mμ μ h ≤ 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t, h)) ((1 : ℝ), (0 : ℝ)) μ :=
    (hasDerivAt_id μ).prodMk (hasDerivAt_const μ h)
  have hd : HasDerivAt (fun t => m t h) (mμ μ h) μ := by
    have := (hdiff μ h hh).comp_hasDerivAt μ h1
    simpa [Function.comp_def] using this
  have hA : Antitone (fun t => m t h) := fun t t' htt => hanti t t' h hh htt
  rw [← hd.deriv]
  exact hA.deriv_nonpos

/-- The barrier (first-crossing) argument along a slightly steepened characteristic
(parameter `α > 1`), which makes the differential inequality strict at a first touching. -/
lemma abf_barrier (m mμ mh : ℝ → ℝ → ℝ) (a e : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hmμ : ∀ μ h, 0 < h → mμ μ h ≤ 0)
    (hdiff : ∀ μ h, 0 < h → HasFDerivAt (fun p : ℝ × ℝ => m p.1 p.2)
      (mμ μ h • ContinuousLinearMap.fst ℝ ℝ ℝ + mh μ h • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ, h))
    (hpde : ∀ μ h, 0 < h →
      m μ h ≤ h * mh μ h - a * m μ h ^ 2 * mμ μ h + e * m μ h ^ 3)
    (μ0 h0 x S α Q : ℝ) (hh0 : 0 < h0) (hx : 0 < x) (hxm : x ≤ m μ0 h0) (hxS : x ≤ S)
    (hQ : Q * (1 - e * S ^ 2) = 1) (hQpos : 0 < Q) (hα : 1 < α) :
    S ≤ m (μ0 - α * (a * Q * (S ^ 2 - x ^ 2) / 2))
      (h0 * Real.exp (α * (Real.log S - Real.log x + e * Q * (S ^ 2 - x ^ 2) / 2))) := by
  set μf : ℝ → ℝ := fun s => μ0 - α * (a * Q * (s ^ 2 - x ^ 2) / 2) with hμf
  set g : ℝ → ℝ := fun s => α * (Real.log s - Real.log x + e * Q * (s ^ 2 - x ^ 2) / 2) with hg
  set hf : ℝ → ℝ := fun s => h0 * Real.exp (g s) with hhf
  have hfpos : ∀ s, 0 < hf s := fun s => by simp only [hhf]; positivity
  have dμ : ∀ s, HasDerivAt μf (-(α * a * Q * s)) s := by
    intro s
    have := ((((hasDerivAt_pow 2 s).sub_const (x ^ 2)).const_mul (a * Q)).div_const 2).const_mul α
    have := this.const_sub μ0
    convert this using 1
    push_cast
    ring
  have dh : ∀ s, 0 < s → HasDerivAt hf (h0 * (Real.exp (g s) * (α * (s⁻¹ + e * Q * s)))) s := by
    intro s hs
    have h1 : HasDerivAt g (α * (s⁻¹ + e * Q * s)) s := by
      have := ((((Real.hasDerivAt_log hs.ne').sub_const (Real.log x)).add
        ((((hasDerivAt_pow 2 s).sub_const (x ^ 2)).const_mul (e * Q)).div_const 2))).const_mul α
      convert this using 1
      push_cast
      ring
    exact (h1.exp).const_mul h0
  set B : ℝ → ℝ := fun s => m (μf s) (hf s) with hB
  set B' : ℝ → ℝ := fun s => mμ (μf s) (hf s) * (-(α * a * Q * s)) +
    mh (μf s) (hf s) * (h0 * (Real.exp (g s) * (α * (s⁻¹ + e * Q * s)))) with hB'
  have dB : ∀ s, 0 < s → HasDerivAt B (B' s) s := by
    intro s hs
    have hP : HasDerivAt (fun t => (μf t, hf t))
        ((-(α * a * Q * s)), h0 * (Real.exp (g s) * (α * (s⁻¹ + e * Q * s)))) s :=
      (dμ s).prodMk (dh s hs)
    have := (hdiff (μf s) (hf s) (hfpos s)).comp_hasDerivAt s hP
    simpa [Function.comp_def, hB, hB'] using this
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => s) (f' := fun _ => (1 : ℝ))
    (a := x) (b := S) (B := B) (B' := B') continuousOn_id
    (fun s _ => (hasDerivAt_id s).hasDerivWithinAt)
    (by
      simp only [hB, hμf, hhf, hg, sub_self, mul_zero]
      simpa using hxm)
    (fun s hs => (dB s (hx.trans_le hs.1)).continuousAt.continuousWithinAt)
    (fun s hs => (dB s (hx.trans_le hs.1)).hasDerivWithinAt)
    (by
      intro s hs hsB
      have hs0 : 0 < s := hx.trans_le hs.1
      have hsS : s ≤ S := hs.2.le
      -- notation at the point P(s)
      set u := mμ (μf s) (hf s) with hu
      set v := mh (μf s) (hf s) with hv
      have hu0 : u ≤ 0 := hmμ _ _ (hfpos s)
      have hp := hpde (μf s) (hf s) (hfpos s)
      have hBs : m (μf s) (hf s) = s := hsB.symm
      rw [hBs] at hp
      -- H = h(s) ∂ₕm at P(s)
      set H := hf s * v with hH
      have hHlow : s - e * s ^ 3 + a * s ^ 2 * u ≤ H := by nlinarith
      have hq : 1 ≤ Q * (1 - e * s ^ 2) := by
        have : e * s ^ 2 ≤ e * S ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ he
          exact pow_le_pow_left₀ hs0.le hsS 2
        nlinarith
      have hc : 0 ≤ α * (1 + e * Q * s ^ 2) := by positivity
      have k1 : α * (1 + e * Q * s ^ 2) * (s - e * s ^ 3 + a * s ^ 2 * u) ≤
          α * (1 + e * Q * s ^ 2) * H := mul_le_mul_of_nonneg_left hHlow hc
      have k2 : 0 ≤ (Q * (1 - e * s ^ 2) - 1) * (e * s ^ 3 - a * s ^ 2 * u) := by
        apply mul_nonneg (by linarith)
        have : 0 ≤ e * s ^ 3 := by positivity
        have : a * s ^ 2 * u ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hu0
        linarith
      have k3 : s < -(α * a * Q * s ^ 2 * u) + α * H * (1 + e * Q * s ^ 2) := by
        have hid : -(α * a * Q * s ^ 2 * u) + α * (1 + e * Q * s ^ 2) * (s - e * s ^ 3 + a * s ^ 2 * u)
            = α * s + α * ((Q * (1 - e * s ^ 2) - 1) * (e * s ^ 3 - a * s ^ 2 * u)) := by ring
        have : 0 ≤ α * ((Q * (1 - e * s ^ 2) - 1) * (e * s ^ 3 - a * s ^ 2 * u)) :=
          mul_nonneg (by linarith) k2
        nlinarith
      have hBexp : s * B' s = -(α * a * Q * s ^ 2 * u) + α * H * (1 + e * Q * s ^ 2) := by
        simp only [hB', hH, hhf]
        field_simp
        ring
      have : s * 1 < s * B' s := by rw [hBexp]; linarith
      exact lt_of_mul_lt_mul_left this hs0.le)
  have := key ⟨hxS, le_rfl⟩
  simpa [hB, hμf, hhf, hg] using this

/-- **Part B.** For a differentiable `m` (one finite-volume / fixed-γ model), monotone in `h`,
antitone in `μ`, satisfying the ABF inequality pointwise, the characteristic form holds. -/
theorem abf_char_of_pde (m mμ mh : ℝ → ℝ → ℝ) (a e : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hdiff : ∀ μ h, 0 < h → HasFDerivAt (fun p : ℝ × ℝ => m p.1 p.2)
      (mμ μ h • ContinuousLinearMap.fst ℝ ℝ ℝ + mh μ h • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ, h))
    (hpde : ∀ μ h, 0 < h →
      m μ h ≤ h * mh μ h - a * m μ h ^ 2 * mμ μ h + e * m μ h ^ 3) :
    abf_Char m a e := by
  intro μ h x s μ' h' hh hx hxm hxs hes hμ' hh'
  have hden : 0 < 1 - e * s ^ 2 := by linarith
  set Q := 1 / (1 - e * s ^ 2) with hQdef
  have hQ : Q * (1 - e * s ^ 2) = 1 := by rw [hQdef]; field_simp
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have hs : 0 < s := hx.trans_le hxs
  set c1 := a * Q * (s ^ 2 - x ^ 2) / 2 with hc1
  set c2 := Real.log s - Real.log x + e * Q * (s ^ 2 - x ^ 2) / 2 with hc2
  have hc1' : c1 = a * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2)) := by
    rw [hc1, hQdef]; field_simp
  have hc2' : h * Real.exp c2 =
      h * (s / x) * Real.exp (e * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2))) := by
    rw [hc2, Real.exp_add, Real.exp_sub, Real.exp_log hs, Real.exp_log hx, hQdef]
    have : e * (1 / (1 - e * s ^ 2)) * (s ^ 2 - x ^ 2) / 2 =
        e * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2)) := by field_simp
    rw [this]; ring
  have ev1 : ∀ᶠ α in 𝓝 (1 : ℝ), μ' < μ - α * c1 := by
    have hc : Continuous fun α : ℝ => μ - α * c1 := by fun_prop
    exact (hc.tendsto 1).eventually_const_lt (by rw [one_mul, hc1']; exact hμ')
  have ev2 : ∀ᶠ α in 𝓝 (1 : ℝ), h * Real.exp (α * c2) < h' := by
    have hc : Continuous fun α : ℝ => h * Real.exp (α * c2) := by fun_prop
    exact (hc.tendsto 1).eventually_lt_const (by rw [one_mul, hc2']; exact hh')
  obtain ⟨α, ⟨h1, h2⟩, hα⟩ :=
    (((ev1.and ev2).filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi 1))).exists
  have hb := abf_barrier m mμ mh a e ha he (abf_partial_mu_nonpos m mμ mh hanti hdiff) hdiff hpde
    μ h x s α Q hh hx hxm hxs hQ hQpos hα
  have hpos : 0 < h * Real.exp (α * c2) := by positivity
  calc s ≤ m (μ - α * c1) (h * Real.exp (α * c2)) := hb
    _ ≤ m (μ - α * c1) h' := hmono _ _ _ hpos h2.le
    _ ≤ m μ' h' := hanti _ _ _ (hpos.trans h2) h1.le

/-! ## The characteristic form survives pointwise limits -/

theorem abf_char_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] (M : ι → ℝ → ℝ → ℝ)
    (A E : ι → ℝ) (m : ℝ → ℝ → ℝ) (a e : ℝ)
    (hM : ∀ μ h, 0 < h → Tendsto (fun i => M i μ h) l (𝓝 (m μ h)))
    (hA : Tendsto A l (𝓝 a)) (hE : Tendsto E l (𝓝 e))
    (hchar : ∀ᶠ i in l, abf_Char (M i) (A i) (E i)) : abf_Char m a e := by
  intro μ h x s μ' h' hh hx hxm hxs hes hμ' hh'
  have hden : (2 * (1 - e * s ^ 2)) ≠ 0 := by
    have : 0 < 1 - e * s ^ 2 := by linarith
    positivity
  have hcont1 : ContinuousAt (fun y : ℝ => μ - a * (s ^ 2 - y ^ 2) / (2 * (1 - e * s ^ 2))) x := by
    fun_prop
  have hcont2 : ContinuousAt (fun y : ℝ =>
      h * (s / y) * Real.exp (e * (s ^ 2 - y ^ 2) / (2 * (1 - e * s ^ 2)))) x := by
    fun_prop (disch := exact hx.ne')
  have ev1 := hcont1.eventually_const_lt hμ'
  have ev2 := hcont2.eventually_lt_const hh'
  obtain ⟨y, ⟨h1y, h2y⟩, hy⟩ :=
    (((ev1.and ev2).filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hx)).exists
  have hT1 : Tendsto (fun i => μ - A i * (s ^ 2 - y ^ 2) / (2 * (1 - E i * s ^ 2))) l
      (𝓝 (μ - a * (s ^ 2 - y ^ 2) / (2 * (1 - e * s ^ 2)))) := by
    apply tendsto_const_nhds.sub
    exact (hA.mul_const _).div ((tendsto_const_nhds.sub (hE.mul_const _)).const_mul 2) hden
  have hT2 : Tendsto (fun i => h * (s / y) * Real.exp (E i * (s ^ 2 - y ^ 2) /
      (2 * (1 - E i * s ^ 2)))) l
      (𝓝 (h * (s / y) * Real.exp (e * (s ^ 2 - y ^ 2) / (2 * (1 - e * s ^ 2))))) := by
    apply Tendsto.const_mul
    exact ((hE.mul_const _).div ((tendsto_const_nhds.sub (hE.mul_const _)).const_mul 2) hden).rexp
  have hT3 : Tendsto (fun i => E i * s ^ 2) l (𝓝 (e * s ^ 2)) := hE.mul_const _
  have hpos' : 0 < h' := by
    refine lt_of_le_of_lt ?_ hh'
    have : 0 < s := hx.trans_le hxs
    positivity
  have hev : ∀ᶠ i in l, s ≤ M i μ' h' := by
    filter_upwards [hchar, hT1.eventually_const_lt h1y, hT2.eventually_lt_const h2y,
      hT3.eventually_lt_const hes, (hM μ h hh).eventually_const_lt (hy.2.trans_le hxm)]
      with i hi i1 i2 i3 i4
    exact hi μ h y s μ' h' hh hy.1 i4.le (hy.2.le.trans hxs) i3 i1 i2
  exact ge_of_tendsto (hM μ' h' hpos') hev

/-! ## Part A (i): the ordered phase, `m(μ,0⁺)² ≥ 2(μc − μ)/(a + 2e(μc − μ))` -/

lemma abf_ordered_level (m : ℝ → ℝ → ℝ) (a e μc : ℝ) (ha : 0 < a) (he : 0 ≤ e)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a e)
    (hchi : ∀ μ0, μ0 < μc → ∀ K : ℝ, ∃ h, 0 < h ∧ K ≤ m μ0 h / h)
    (μ s h' : ℝ) (hμ : μ < μc) (hs : 0 < s)
    (hsX : s ^ 2 * (a + 2 * e * (μc - μ)) < 2 * (μc - μ)) (hh' : 0 < h') :
    s ≤ m μ h' := by
  set D := μc - μ with hD
  have hDpos : 0 < D := by linarith
  have hes : e * s ^ 2 < 1 := by
    have : 0 ≤ a * s ^ 2 := by positivity
    nlinarith
  have hden : 0 < 1 - e * s ^ 2 := by linarith
  set A := a * s ^ 2 / (2 * (1 - e * s ^ 2)) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hAD : A < D := by
    rw [hAdef, div_lt_iff₀ (by positivity)]
    nlinarith
  set μ0 := μ + (A + D) / 2 with hμ0
  set E := Real.exp (e * s ^ 2 / (2 * (1 - e * s ^ 2))) with hE
  have hEpos : 0 < E := Real.exp_pos _
  obtain ⟨h0, hh0, hK⟩ := hchi μ0 (by linarith) (2 * s * E / h')
  set h1 := min h0 h' with hh1def
  have hh1 : 0 < h1 := lt_min hh0 hh'
  have hK1 : 2 * s * E / h' ≤ m μ0 h1 / h1 := hK.trans (hghs μ0 h1 h0 hh1 (min_le_left _ _))
  set x := m μ0 h1 with hxdef
  have hKpos : 0 < 2 * s * E / h' := by positivity
  have hxpos : 0 < x := by
    have : 0 < x / h1 := hKpos.trans_le hK1
    exact (div_pos_iff_of_pos_right hh1).mp this
  by_cases hxs : s ≤ x
  · calc s ≤ x := hxs
      _ ≤ m μ0 h' := hmono μ0 h1 h' hh1 (min_le_right _ _)
      _ ≤ m μ h' := hanti μ μ0 h' hh' (by linarith)
  · push Not at hxs
    apply hchar μ0 h1 x s μ h' hh1 hxpos le_rfl hxs.le hes
    · have : a * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2)) ≤ A := by
        rw [hAdef]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg x]
      linarith
    · have hexp : Real.exp (e * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2))) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg x]
      have hcross : 2 * s * E * h1 ≤ x * h' := by
        rw [div_le_div_iff₀ hh' hh1] at hK1
        linarith
      calc h1 * (s / x) * Real.exp (e * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2)))
          ≤ h1 * (s / x) * E := by
            apply mul_le_mul_of_nonneg_left hexp; positivity
        _ = (s * E * h1) / x := by field_simp
        _ < h' := by
            rw [div_lt_iff₀ hxpos]
            have : 0 < s * E * h1 := by positivity
            nlinarith

/-- **(i) Spontaneous magnetisation, mean-field bound β ≤ 1/2.** -/
theorem abf_spontaneous_magnetization (m : ℝ → ℝ → ℝ) (a e μc : ℝ) (ha : 0 < a) (he : 0 ≤ e)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a e)
    (hchi : ∀ μ0, μ0 < μc → ∀ K : ℝ, ∃ h, 0 < h ∧ K ≤ m μ0 h / h) :
    ∀ μ, μ < μc → ∀ h, 0 < h → 2 * (μc - μ) / (a + 2 * e * (μc - μ)) ≤ m μ h ^ 2 := by
  intro μ hμ h hh
  have hDpos : 0 < μc - μ := by linarith
  have hden : 0 < a + 2 * e * (μc - μ) := by positivity
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  by_cases ht0 : t ≤ 0
  · exact ht0.trans (sq_nonneg _)
  push Not at ht0
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hX : Real.sqrt t ^ 2 * (a + 2 * e * (μc - μ)) < 2 * (μc - μ) := by
    rw [hst]; exact (lt_div_iff₀ hden).mp ht
  have := abf_ordered_level m a e μc ha he hmono hanti hghs hchar hchi μ (Real.sqrt t) h hμ hsq hX hh
  rw [← hst]
  exact pow_le_pow_left₀ hsq.le this 2

/-- (i) without error term (`e = 0`): `m(μ,h)² ≥ 2(μc − μ)/a` for all `h > 0`. -/
theorem abf_spontaneous_magnetization_e0 (m : ℝ → ℝ → ℝ) (a μc : ℝ) (ha : 0 < a)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a 0)
    (hchi : ∀ μ0, μ0 < μc → ∀ K : ℝ, ∃ h, 0 < h ∧ K ≤ m μ0 h / h) :
    ∀ μ, μ < μc → ∀ h, 0 < h → 2 * (μc - μ) / a ≤ m μ h ^ 2 := by
  intro μ hμ h hh
  simpa using abf_spontaneous_magnetization m a 0 μc ha le_rfl hmono hanti hghs hchar hchi μ hμ h hh

/-- (i) for the right limit `m(μ,0⁺)`. -/
theorem abf_spontaneous_magnetization_lim (m : ℝ → ℝ → ℝ) (a e μc : ℝ) (ha : 0 < a)
    (he : 0 ≤ e)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a e)
    (hchi : ∀ μ0, μ0 < μc → ∀ K : ℝ, ∃ h, 0 < h ∧ K ≤ m μ0 h / h)
    (μ L : ℝ) (hμ : μ < μc) (hL : Tendsto (m μ) (𝓝[>] 0) (𝓝 L)) :
    2 * (μc - μ) / (a + 2 * e * (μc - μ)) ≤ L ^ 2 := by
  refine ge_of_tendsto (hL.pow 2) ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact abf_spontaneous_magnetization m a e μc ha he hmono hanti hghs hchar hchi μ hμ h hh

/-- The right limit `m(μ,0⁺)` exists (monotonicity and `m ≥ 0`); it is `inf_{h>0} m(μ,h)`. -/
theorem abf_tendsto_zero_plus (m : ℝ → ℝ → ℝ)
    (hpos : ∀ μ h, 0 < h → 0 ≤ m μ h)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h') (μ : ℝ) :
    Tendsto (m μ) (𝓝[>] 0) (𝓝 (sInf (m μ '' Ioi 0))) := by
  apply MonotoneOn.tendsto_nhdsGT
  · intro h hh h' _ hle
    exact hmono μ h h' hh hle
  · refine ⟨0, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    exact hpos μ h hh

/-! ## Part A (ii): the critical point, `m(μc,h)³ ≥ const · h` -/

/-- (ii), parametric form (all `e ≥ 0`). -/
theorem abf_critical_level (m : ℝ → ℝ → ℝ) (a e μc κ : ℝ) (ha : 0 < a) (he : 0 ≤ e)
    (hκ : 0 < κ)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a e)
    (hdis : ∀ μ0, μc < μ0 → ∃ h, 0 < h ∧ κ / (μ0 - μc) ≤ m μ0 h / h)
    (s h : ℝ) (hs : 0 < s) (hh : 0 < h) (hes : e * s ^ 2 < 1)
    (hcond : a * s ^ 3 * Real.exp (e * s ^ 2 / (2 * (1 - e * s ^ 2))) <
      2 * κ * (1 - e * s ^ 2) * h) :
    s ≤ m μc h := by
  have hden : 0 < 1 - e * s ^ 2 := by linarith
  set A := a * s ^ 2 / (2 * (1 - e * s ^ 2)) with hAdef
  have hA0 : 0 ≤ A := by positivity
  set E := Real.exp (e * s ^ 2 / (2 * (1 - e * s ^ 2))) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set W := κ * h / (s * E) with hW
  have hAW : A < W := by
    rw [hAdef, hW, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set d := (A + W) / 2 with hd
  have hdpos : 0 < d := by
    have : 0 < W := by positivity
    linarith
  have hdW : d * (s * E) < κ * h := by
    have : W * (s * E) = κ * h := by rw [hW]; field_simp
    have : d < W := by linarith
    nlinarith [mul_pos hs hEpos]
  set μ0 := μc + d with hμ0
  obtain ⟨h0, hh0, hK⟩ := hdis μ0 (by linarith)
  set h1 := min h0 h with hh1def
  have hh1 : 0 < h1 := lt_min hh0 hh
  have hK1 : κ / (μ0 - μc) ≤ m μ0 h1 / h1 := hK.trans (hghs μ0 h1 h0 hh1 (min_le_left _ _))
  have hμd : μ0 - μc = d := by rw [hμ0]; ring
  rw [hμd] at hK1
  set x := m μ0 h1 with hxdef
  have hxpos : 0 < x := by
    have : 0 < x / h1 := (div_pos hκ hdpos).trans_le hK1
    exact (div_pos_iff_of_pos_right hh1).mp this
  by_cases hxs : s ≤ x
  · calc s ≤ x := hxs
      _ ≤ m μ0 h := hmono μ0 h1 h hh1 (min_le_right _ _)
      _ ≤ m μc h := hanti μc μ0 h hh (by linarith)
  · push Not at hxs
    apply hchar μ0 h1 x s μc h hh1 hxpos le_rfl hxs.le hes
    · have : a * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2)) ≤ A := by
        rw [hAdef]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg x]
      have : A < d := by linarith
      linarith
    · have hexp : Real.exp (e * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2))) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg x]
      have hcross : κ * h1 ≤ x * d := by
        rw [div_le_div_iff₀ hdpos hh1] at hK1
        linarith
      calc h1 * (s / x) * Real.exp (e * (s ^ 2 - x ^ 2) / (2 * (1 - e * s ^ 2)))
          ≤ h1 * (s / x) * E := by
            apply mul_le_mul_of_nonneg_left hexp; positivity
        _ = (s * E * h1) / x := by field_simp
        _ < h := by
            rw [div_lt_iff₀ hxpos]
            -- κ (s E h1) ≤ x d (s E) < x κ h
            have h3 : κ * (s * E * h1) ≤ x * (d * (s * E)) := by
              have := mul_le_mul_of_nonneg_right hcross (le_of_lt (mul_pos hs hEpos))
              nlinarith
            have h4 : x * (d * (s * E)) < x * (κ * h) := mul_lt_mul_of_pos_left hdW hxpos
            have h5 : κ * (s * E * h1) < κ * (h * x) := by nlinarith
            exact lt_of_mul_lt_mul_left h5 hκ.le

lemma abf_rpow_third_cube (t : ℝ) (ht : 0 ≤ t) : (t ^ ((1 : ℝ) / 3)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- (ii) without error term (`e = 0`): `m(μc,h)³ ≥ 2κh/a`, i.e. δ ≥ 3. -/
theorem abf_critical_cube (m : ℝ → ℝ → ℝ) (a μc κ : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a 0)
    (hdis : ∀ μ0, μc < μ0 → ∃ h, 0 < h ∧ κ / (μ0 - μc) ≤ m μ0 h / h)
    (h : ℝ) (hh : 0 < h) :
    2 * κ * h / a ≤ m μc h ^ 3 := by
  have hX : 0 < 2 * κ * h / a := by positivity
  have claim : ∀ t, 0 < t → t < 2 * κ * h / a → t ≤ m μc h ^ 3 := by
    intro t ht htX
    set s := t ^ ((1 : ℝ) / 3) with hsdef
    have hs : 0 < s := Real.rpow_pos_of_pos ht _
    have hs3 : s ^ 3 = t := abf_rpow_third_cube t ht.le
    have hcond : a * s ^ 3 * Real.exp (0 * s ^ 2 / (2 * (1 - 0 * s ^ 2))) <
        2 * κ * (1 - 0 * s ^ 2) * h := by
      simp only [zero_mul, zero_div, Real.exp_zero, mul_one, sub_zero]
      rw [hs3]
      have := (lt_div_iff₀ ha).mp htX
      linarith
    have := abf_critical_level m a 0 μc κ ha le_rfl hκ hmono hanti hghs hchar hdis s h hs hh
      (by simp) hcond
    rw [← hs3]
    exact pow_le_pow_left₀ hs.le this 3
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  by_cases ht0 : t ≤ 0
  · have := claim (κ * h / a) (by positivity) (by
      rw [div_lt_div_iff_of_pos_right ha]; nlinarith)
    have : 0 < κ * h / a := by positivity
    linarith
  · push Not at ht0
    exact claim t ht0 ht

/-- (ii), `e = 0`, in the form `m(μc,h) ≥ c' h^{1/3}` with `c' = (2κ/a)^{1/3}`. -/
theorem abf_critical_rpow (m : ℝ → ℝ → ℝ) (a μc κ : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a 0)
    (hdis : ∀ μ0, μc < μ0 → ∃ h, 0 < h ∧ κ / (μ0 - μc) ≤ m μ0 h / h)
    (h : ℝ) (hh : 0 < h) :
    (2 * κ / a) ^ ((1 : ℝ) / 3) * h ^ ((1 : ℝ) / 3) ≤ m μc h := by
  have hc := abf_critical_cube m a μc κ ha hκ hmono hanti hghs hchar hdis h hh
  have hX : 0 < 2 * κ * h / a := by positivity
  have hy : 0 ≤ m μc h := by
    by_contra hneg
    push Not at hneg
    have : m μc h ^ 3 < 0 := Odd.pow_neg (by decide) hneg
    linarith
  rw [← Real.mul_rpow (by positivity) hh.le]
  have : 2 * κ / a * h = 2 * κ * h / a := by ring
  rw [this]
  calc (2 * κ * h / a) ^ ((1 : ℝ) / 3) ≤ (m μc h ^ 3) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow hX.le hc (by norm_num)
    _ = m μc h := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
        norm_num

lemma abf_exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-- (ii) with the error term (`e ≥ 0`), for small `h`: `m(μc,h)³ ≥ κh/(2a)` as soon as
`8 e³ (κh/(2a))² ≤ 1`. -/
theorem abf_critical_cube_err (m : ℝ → ℝ → ℝ) (a e μc κ : ℝ) (ha : 0 < a) (he : 0 ≤ e)
    (hκ : 0 < κ)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hghs : ∀ μ h h', 0 < h → h ≤ h' → m μ h' / h' ≤ m μ h / h)
    (hchar : abf_Char m a e)
    (hdis : ∀ μ0, μc < μ0 → ∃ h, 0 < h ∧ κ / (μ0 - μc) ≤ m μ0 h / h)
    (h : ℝ) (hh : 0 < h) (hsmall : 8 * e ^ 3 * (κ * h / (2 * a)) ^ 2 ≤ 1) :
    κ * h / (2 * a) ≤ m μc h ^ 3 := by
  set X := κ * h / (2 * a) with hXdef
  have hX : 0 < X := by positivity
  have claim : ∀ t, 0 < t → t < X → t ≤ m μc h ^ 3 := by
    intro t ht htX
    set s := t ^ ((1 : ℝ) / 3) with hsdef
    have hs : 0 < s := Real.rpow_pos_of_pos ht _
    have hs3 : s ^ 3 = t := abf_rpow_third_cube t ht.le
    have hes2 : e * s ^ 2 ≤ 1 / 2 := by
      by_contra hcon
      push Not at hcon
      have h1 : (1 / 2 : ℝ) ^ 3 < (e * s ^ 2) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
      have h2 : (e * s ^ 2) ^ 3 = e ^ 3 * t ^ 2 := by rw [← hs3]; ring
      have h3 : e ^ 3 * t ^ 2 ≤ e ^ 3 * X ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ ht.le htX.le 2
      nlinarith
    have hes : e * s ^ 2 < 1 := by linarith
    have hden : 0 < 1 - e * s ^ 2 := by linarith
    have hE : Real.exp (e * s ^ 2 / (2 * (1 - e * s ^ 2))) < 2 := by
      refine lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) abf_exp_half_lt_two
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hat : a * t < κ * h / 2 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mp htX
      linarith
    have hcond : a * s ^ 3 * Real.exp (e * s ^ 2 / (2 * (1 - e * s ^ 2))) <
        2 * κ * (1 - e * s ^ 2) * h := by
      rw [hs3]
      have hat0 : 0 < a * t := by positivity
      have : a * t * Real.exp (e * s ^ 2 / (2 * (1 - e * s ^ 2))) < a * t * 2 :=
        mul_lt_mul_of_pos_left hE hat0
      have : κ * h ≤ 2 * κ * (1 - e * s ^ 2) * h := by
        have : 0 < κ * h := by positivity
        nlinarith
      linarith
    have := abf_critical_level m a e μc κ ha he hκ hmono hanti hghs hchar hdis s h hs hh hes hcond
    rw [← hs3]
    exact pow_le_pow_left₀ hs.le this 3
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  by_cases ht0 : t ≤ 0
  · have := claim (X / 2) (by positivity) (by linarith)
    have : 0 < X / 2 := by positivity
    linarith
  · push Not at ht0
    exact claim t ht0 ht

end

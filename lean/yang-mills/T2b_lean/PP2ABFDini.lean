import Mathlib

/-!
Long Table, Claude council, target T2b, θ-1: the Dini-weakened ABF characteristics lemma
(θ-1 PROOF.md §§2–4, STATEMENT.md §1). Pure real analysis, no model. Modifies PP2ABF.lean.

SETTING. m : ℝ → ℝ → ℝ, arguments (μ, h), h > 0. Data: a μ-window W = [μlo, μhi], a level
s₀, a field ceiling hmax, F ≥ 0 on (0, s₀], and Φ with Φ'(s) = F(s)/s on (0, s₀] (Φ is a GIVEN
function with `HasDerivAt` hypotheses, not defined as an integral; Φ_x(S) = Φ S − Φ x). The PDE
    (P)  m ≤ h ∂ₕm + F(m)(−∂_μ m)   at (μ, h) with μlo ≤ μ ≤ μhi, 0 < h ≤ hmax, m(μ,h) ≤ s₀.
`abfD_Char m Φ μlo μhi s₀ hmax`: for μ ≤ μhi, 0 < h, 0 < x ≤ m(μ,h), x ≤ S ≤ s₀ and every
target with μlo ≤ μ' < μ − (Φ S − Φ x), h·S/x < h', h·S/x < hmax, one has S ≤ m(μ', h').

FORMALIZED (all `abfD_`-prefixed; no sorry; axioms propext / Classical.choice / Quot.sound).
* Lemma A. `abfD_char_of_pde`: m jointly (Fréchet) differentiable at every (μ, h), h > 0, with
  partials mμ, mh; m monotone in h, antitone in μ (h > 0); Φ' = F/s and F ≥ 0 on (0, s₀]; (P) on
  the region above  ⟹  `abfD_Char m Φ μlo μhi s₀ hmax`. Proof: `abfD_barrier` along
  μ(s) = μ0 − α(Φ s − Φ x), h(s) = h0 exp(α(log s − log x)), α > 1: at a touching point
  B(s) = m(μ(s),h(s)) = s one has s B'(s) = α(h ∂ₕm + F(s)(−∂_μ m)) ≥ α s > s (the PDE is used
  ONLY there; the curve stays in W × (0, hmax] because Φ is monotone, `abfD_Phi_mono`); Mathlib's
  `image_le_of_deriv_right_lt_deriv_boundary'`; then α ↓ 1 and monotonicity of m.
  Power case `abfD_char_of_pde_pow`: F = C s^θ, Φ = C s^θ/θ (C ≥ 0, θ > 0).
* Lemma B. `abfD_torus`: if `abfD_Char m Φ μlo μhi s₀ hmax`, Φ ≥ 0 on (0, s₀], μ0 ≤ μhi,
  m(μ0,h)/h → χ0 > 0 as h ↓ 0 and 3s₀/χ0 ≤ hmax, then for 0 < S ≤ s₀, μlo ≤ μ' < μ0 − Φ S,
  h' > 2S/χ0:  S ≤ m(μ', h').  Power case `abfD_torus_pow`.
* Limits. `abfD_char_of_tendsto`: `abfD_Char` (fixed Φ continuous on (0, s₀], fixed window)
  passes to pointwise limits on h > 0 along any NeBot filter. `abfD_limit`: tori M_i, each
  satisfying Lemma B's hypotheses with χ_i → ∞ (and hmax_i ≥ 3s₀/χ_i), M_i → m pointwise at μ'
  ⟹ S ≤ m(μ', h') for all h' > 0.  `abfD_limit_pow` (C, θ > 0, 0 < s₀, μlo ≤ μ' < μ0):
      min(s₀, (θ(μ0 − μ')/C)^{1/θ}) ≤ m(μ', h')   for every h' > 0.

NOT formalized. (P) itself for φ⁴₂ tori; differentiability/GKS monotonicity (inputs); Φ as
∫ F(r)dr/r and the general Dini F (only the abstract Φ and the power case); the convexity /
pressure step and the double limit ε → 0, L → ∞ of Theorem C (here one filter, magnetisations
converging pointwise at μ'); the sharpness counterexample of PROOF §5.2.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Filter Topology Set

noncomputable section

/-- Localised Dini characteristic form, with open targets. -/
def abfD_Char (m : ℝ → ℝ → ℝ) (Φ : ℝ → ℝ) (μlo μhi s₀ hmax : ℝ) : Prop :=
  ∀ μ h x S μ' h' : ℝ, μ ≤ μhi → 0 < h → 0 < x → x ≤ m μ h → x ≤ S → S ≤ s₀ →
    μlo ≤ μ' → μ' < μ - (Φ S - Φ x) → h * (S / x) < h' → h * (S / x) < hmax →
    S ≤ m μ' h'

lemma abfD_Phi_mono (F Φ : ℝ → ℝ) (s₀ : ℝ)
    (hΦ : ∀ s, 0 < s → s ≤ s₀ → HasDerivAt Φ (F s / s) s)
    (hF : ∀ s, 0 < s → s ≤ s₀ → 0 ≤ F s) (x S : ℝ) (hx : 0 < x) (hS : S ≤ s₀) :
    MonotoneOn Φ (Icc x S) := by
  have hd : ∀ t ∈ Icc x S, HasDerivAt Φ (F t / t) t := fun t ht =>
    hΦ t (hx.trans_le ht.1) (ht.2.trans hS)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => F t / t) (convex_Icc x S)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  have ht' := interior_subset ht
  have : 0 < t := hx.trans_le ht'.1
  exact div_nonneg (hF t this (ht'.2.trans hS)) this.le

/-- The barrier along the steepened characteristic (`α > 1`). -/
lemma abfD_barrier (m mμ mh : ℝ → ℝ → ℝ) (F Φ : ℝ → ℝ) (μlo μhi s₀ hmax : ℝ)
    (hdiff : ∀ μ h, 0 < h → HasFDerivAt (fun p : ℝ × ℝ => m p.1 p.2)
      (mμ μ h • ContinuousLinearMap.fst ℝ ℝ ℝ + mh μ h • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ, h))
    (hΦ : ∀ s, 0 < s → s ≤ s₀ → HasDerivAt Φ (F s / s) s)
    (hF : ∀ s, 0 < s → s ≤ s₀ → 0 ≤ F s)
    (hpde : ∀ μ h, μlo ≤ μ → μ ≤ μhi → 0 < h → h ≤ hmax → m μ h ≤ s₀ →
      m μ h ≤ h * mh μ h + F (m μ h) * (-(mμ μ h)))
    (μ0 h0 x S α : ℝ) (hμ0 : μ0 ≤ μhi) (hh0 : 0 < h0) (hx : 0 < x) (hxm : x ≤ m μ0 h0)
    (hxS : x ≤ S) (hS : S ≤ s₀) (hα : 1 < α)
    (hlo : μlo ≤ μ0 - α * (Φ S - Φ x))
    (hhi : h0 * Real.exp (α * (Real.log S - Real.log x)) ≤ hmax) :
    S ≤ m (μ0 - α * (Φ S - Φ x)) (h0 * Real.exp (α * (Real.log S - Real.log x))) := by
  have hmon := abfD_Phi_mono F Φ s₀ hΦ hF x S hx hS
  set μf : ℝ → ℝ := fun s => μ0 - α * (Φ s - Φ x) with hμf
  set g : ℝ → ℝ := fun s => α * (Real.log s - Real.log x) with hg
  set hf : ℝ → ℝ := fun s => h0 * Real.exp (g s) with hhf
  have hfpos : ∀ s, 0 < hf s := fun s => by simp only [hhf]; positivity
  have dμ : ∀ s, 0 < s → s ≤ s₀ → HasDerivAt μf (-(α * (F s / s))) s := fun s hs hs' =>
    (((hΦ s hs hs').sub_const (Φ x)).const_mul α).const_sub μ0
  have dh : ∀ s, 0 < s → HasDerivAt hf (h0 * (Real.exp (g s) * (α * s⁻¹))) s := by
    intro s hs
    have h1 : HasDerivAt g (α * s⁻¹) s :=
      ((Real.hasDerivAt_log hs.ne').sub_const (Real.log x)).const_mul α
    exact (h1.exp).const_mul h0
  set B : ℝ → ℝ := fun s => m (μf s) (hf s) with hB
  set B' : ℝ → ℝ := fun s => mμ (μf s) (hf s) * (-(α * (F s / s))) +
    mh (μf s) (hf s) * (h0 * (Real.exp (g s) * (α * s⁻¹))) with hB'
  have dB : ∀ s, 0 < s → s ≤ s₀ → HasDerivAt B (B' s) s := by
    intro s hs hs'
    have hP : HasDerivAt (fun t => (μf t, hf t))
        ((-(α * (F s / s))), h0 * (Real.exp (g s) * (α * s⁻¹))) s :=
      (dμ s hs hs').prodMk (dh s hs)
    have := (hdiff (μf s) (hf s) (hfpos s)).comp_hasDerivAt s hP
    simpa [Function.comp_def, hB, hB'] using this
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => s) (f' := fun _ => (1 : ℝ))
    (a := x) (b := S) (B := B) (B' := B') continuousOn_id
    (fun s _ => (hasDerivAt_id s).hasDerivWithinAt)
    (by
      show x ≤ m (μ0 - α * (Φ x - Φ x)) (h0 * Real.exp (α * (Real.log x - Real.log x)))
      simpa using hxm)
    (fun s hs => (dB s (hx.trans_le hs.1) (hs.2.trans hS)).continuousAt.continuousWithinAt)
    (fun s hs => (dB s (hx.trans_le hs.1) (hs.2.le.trans hS)).hasDerivWithinAt)
    (by
      intro s hs hsB
      have hs0 : 0 < s := hx.trans_le hs.1
      have hsS : s ≤ S := hs.2.le
      have hBs : m (μf s) (hf s) = s := hsB.symm
      have hα0 : 0 ≤ α := by linarith
      have hwlo : μlo ≤ μf s := by
        refine hlo.trans ?_
        have : Φ s ≤ Φ S := hmon ⟨hs.1, hsS⟩ ⟨hxS, le_rfl⟩ hsS
        show μ0 - α * (Φ S - Φ x) ≤ μ0 - α * (Φ s - Φ x)
        nlinarith
      have hwhi : μf s ≤ μhi := by
        refine le_trans ?_ hμ0
        have : Φ x ≤ Φ s := hmon ⟨le_rfl, hxS⟩ ⟨hs.1, hsS⟩ hs.1
        show μ0 - α * (Φ s - Φ x) ≤ μ0
        nlinarith
      have hwh : hf s ≤ hmax := by
        refine le_trans ?_ hhi
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (sub_le_sub_right (Real.log_le_log hs0 hsS) _) hα0)) hh0.le
      have hp := hpde (μf s) (hf s) hwlo hwhi (hfpos s) hwh (by rw [hBs]; exact hsS.trans hS)
      rw [hBs] at hp
      have hBexp : s * B' s =
          α * (hf s * mh (μf s) (hf s) + F s * (-(mμ (μf s) (hf s)))) := by
        simp only [hB', hhf]
        field_simp
        ring
      have : s * 1 < s * B' s := by
        rw [hBexp]
        nlinarith [mul_le_mul_of_nonneg_left hp hα0, mul_lt_mul_of_pos_right hα hs0]
      exact lt_of_mul_lt_mul_left this hs0.le)
  exact key ⟨hxS, le_rfl⟩

/-- **Lemma A.** The localised Dini PDE implies the characteristic form. -/
theorem abfD_char_of_pde (m mμ mh : ℝ → ℝ → ℝ) (F Φ : ℝ → ℝ) (μlo μhi s₀ hmax : ℝ)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hdiff : ∀ μ h, 0 < h → HasFDerivAt (fun p : ℝ × ℝ => m p.1 p.2)
      (mμ μ h • ContinuousLinearMap.fst ℝ ℝ ℝ + mh μ h • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ, h))
    (hΦ : ∀ s, 0 < s → s ≤ s₀ → HasDerivAt Φ (F s / s) s)
    (hF : ∀ s, 0 < s → s ≤ s₀ → 0 ≤ F s)
    (hpde : ∀ μ h, μlo ≤ μ → μ ≤ μhi → 0 < h → h ≤ hmax → m μ h ≤ s₀ →
      m μ h ≤ h * mh μ h + F (m μ h) * (-(mμ μ h))) :
    abfD_Char m Φ μlo μhi s₀ hmax := by
  intro μ h x S μ' h' hμ hh hx hxm hxS hS hlo hμ' hh' hhm
  have hSpos : 0 < S := hx.trans_le hxS
  have hc2' : h * Real.exp (Real.log S - Real.log x) = h * (S / x) := by
    rw [Real.exp_sub, Real.exp_log hSpos, Real.exp_log hx]
  have ev1 : ∀ᶠ α in 𝓝 (1 : ℝ), μ' < μ - α * (Φ S - Φ x) := by
    have hc : Continuous fun α : ℝ => μ - α * (Φ S - Φ x) := by fun_prop
    exact (hc.tendsto 1).eventually_const_lt (by rw [one_mul]; exact hμ')
  have hc : Continuous fun α : ℝ => h * Real.exp (α * (Real.log S - Real.log x)) := by fun_prop
  have ev2 : ∀ᶠ α in 𝓝 (1 : ℝ), h * Real.exp (α * (Real.log S - Real.log x)) < h' :=
    (hc.tendsto 1).eventually_lt_const (by rw [one_mul, hc2']; exact hh')
  have ev3 : ∀ᶠ α in 𝓝 (1 : ℝ), h * Real.exp (α * (Real.log S - Real.log x)) < hmax :=
    (hc.tendsto 1).eventually_lt_const (by rw [one_mul, hc2']; exact hhm)
  obtain ⟨α, ⟨⟨h1, h2⟩, h3⟩, hα⟩ := ((((ev1.and ev2).and ev3).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi 1))).exists
  have hb := abfD_barrier m mμ mh F Φ μlo μhi s₀ hmax hdiff hΦ hF hpde μ h x S α hμ hh hx hxm
    hxS hS (mem_Ioi.mp hα) (hlo.trans h1.le) h3.le
  have hpos : 0 < h * Real.exp (α * (Real.log S - Real.log x)) := by positivity
  calc S ≤ _ := hb
    _ ≤ m (μ - α * (Φ S - Φ x)) h' := hmono _ _ _ hpos h2.le
    _ ≤ m μ' h' := hanti _ _ _ (hpos.trans h2) h1.le

lemma abfD_pow_hasDerivAt (C θ s : ℝ) (hθ : 0 < θ) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => C * s ^ θ / θ) (C * s ^ θ / s) s := by
  have := ((Real.hasDerivAt_rpow_const (p := θ) (Or.inl hs.ne')).const_mul C).div_const θ
  convert this using 1
  rw [Real.rpow_sub_one hs.ne']
  field_simp

/-- **Lemma A, power case** `F = C s^θ`, `Φ = C s^θ/θ`. -/
theorem abfD_char_of_pde_pow (m mμ mh : ℝ → ℝ → ℝ) (C θ μlo μhi s₀ hmax : ℝ)
    (hC : 0 ≤ C) (hθ : 0 < θ)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hdiff : ∀ μ h, 0 < h → HasFDerivAt (fun p : ℝ × ℝ => m p.1 p.2)
      (mμ μ h • ContinuousLinearMap.fst ℝ ℝ ℝ + mh μ h • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ, h))
    (hpde : ∀ μ h, μlo ≤ μ → μ ≤ μhi → 0 < h → h ≤ hmax → m μ h ≤ s₀ →
      m μ h ≤ h * mh μ h + C * m μ h ^ θ * (-(mμ μ h))) :
    abfD_Char m (fun s => C * s ^ θ / θ) μlo μhi s₀ hmax :=
  abfD_char_of_pde m mμ mh (fun s => C * s ^ θ) _ μlo μhi s₀ hmax hmono hanti hdiff
    (fun s hs _ => abfD_pow_hasDerivAt C θ s hθ hs)
    (fun _ hs _ => mul_nonneg hC (Real.rpow_nonneg hs.le θ)) hpde

/-! ## Lemma B: one torus, only χ(μ0, 0) = χ0 is used -/

theorem abfD_torus (m : ℝ → ℝ → ℝ) (Φ : ℝ → ℝ) (μlo μhi s₀ hmax μ0 χ0 : ℝ)
    (hchar : abfD_Char m Φ μlo μhi s₀ hmax)
    (hΦ0 : ∀ x, 0 < x → x ≤ s₀ → 0 ≤ Φ x)
    (hμ0 : μ0 ≤ μhi) (hχ0 : 0 < χ0) (hhmax : 3 * s₀ / χ0 ≤ hmax)
    (hχ : Tendsto (fun h => m μ0 h / h) (𝓝[>] 0) (𝓝 χ0))
    (S μ' h' : ℝ) (hS : 0 < S) (hSs : S ≤ s₀) (hlo : μlo ≤ μ') (hμ' : μ' < μ0 - Φ S)
    (hh' : 2 * S / χ0 < h') : S ≤ m μ' h' := by
  have hm0 : Tendsto (m μ0) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).mul hχ
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [id]
    field_simp [(mem_Ioi.mp hh).ne']
  obtain ⟨h0, ⟨hA, hB⟩, hh0⟩ := ((hχ.eventually_const_lt (by linarith : 2 / 3 * χ0 < χ0)).and
    (hm0.eventually_lt_const hS)).and self_mem_nhdsWithin |>.exists
  have hh0 : 0 < h0 := hh0
  set x := m μ0 h0 with hxdef
  have hA' : 2 / 3 * χ0 * h0 < x := (lt_div_iff₀ hh0).mp hA
  have hx : 0 < x := by nlinarith
  have hq : h0 * (S / x) * x = S * h0 := by field_simp
  have hq2 : h0 * (S / x) * (2 * χ0) < 3 * S := by
    have : h0 * (S / x) * (2 * χ0) * x < 3 * S * x := by nlinarith
    exact lt_of_mul_lt_mul_right this hx.le
  have h2 : 2 * S < h' * χ0 := (div_lt_iff₀ hχ0).mp hh'
  have h3 : 3 * s₀ ≤ hmax * χ0 := (div_le_iff₀ hχ0).mp hhmax
  refine hchar μ0 h0 x S μ' h' hμ0 hh0 hx le_rfl hB.le hSs hlo
    (by linarith [hΦ0 x hx (hB.le.trans hSs)]) ?_ ?_
  · nlinarith
  · nlinarith

theorem abfD_torus_pow (m : ℝ → ℝ → ℝ) (C θ μlo μhi s₀ hmax μ0 χ0 : ℝ) (hC : 0 ≤ C)
    (hθ : 0 < θ) (hchar : abfD_Char m (fun s => C * s ^ θ / θ) μlo μhi s₀ hmax)
    (hμ0 : μ0 ≤ μhi) (hχ0 : 0 < χ0) (hhmax : 3 * s₀ / χ0 ≤ hmax)
    (hχ : Tendsto (fun h => m μ0 h / h) (𝓝[>] 0) (𝓝 χ0))
    (S μ' h' : ℝ) (hS : 0 < S) (hSs : S ≤ s₀) (hlo : μlo ≤ μ')
    (hμ' : μ' < μ0 - C * S ^ θ / θ) (hh' : 2 * S / χ0 < h') : S ≤ m μ' h' :=
  abfD_torus m _ μlo μhi s₀ hmax μ0 χ0 hchar
    (fun _ hx _ => div_nonneg (mul_nonneg hC (Real.rpow_nonneg hx.le θ)) hθ.le)
    hμ0 hχ0 hhmax hχ S μ' h' hS hSs hlo hμ' hh'

/-! ## Limits -/

theorem abfD_char_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] (M : ι → ℝ → ℝ → ℝ)
    (m : ℝ → ℝ → ℝ) (Φ : ℝ → ℝ) (μlo μhi s₀ hmax : ℝ)
    (hΦc : ∀ x, 0 < x → x ≤ s₀ → ContinuousAt Φ x)
    (hM : ∀ μ h, 0 < h → Tendsto (fun i => M i μ h) l (𝓝 (m μ h)))
    (hchar : ∀ᶠ i in l, abfD_Char (M i) Φ μlo μhi s₀ hmax) :
    abfD_Char m Φ μlo μhi s₀ hmax := by
  intro μ h x S μ' h' hμ hh hx hxm hxS hS hlo hμ' hh' hhm
  have hcont1 : ContinuousAt (fun y => μ - (Φ S - Φ y)) x :=
    continuousAt_const.sub (continuousAt_const.sub (hΦc x hx (hxS.trans hS)))
  have hcont2 : ContinuousAt (fun y : ℝ => h * (S / y)) x := by
    fun_prop (disch := exact hx.ne')
  obtain ⟨y, ⟨⟨h1y, h2y⟩, h3y⟩, hy⟩ := ((((hcont1.eventually_const_lt hμ').and
    (hcont2.eventually_lt_const hh')).and (hcont2.eventually_lt_const hhm)).filter_mono
    nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hx) |>.exists
  have hpos' : 0 < h' := by
    refine lt_of_le_of_lt ?_ hh'
    have : 0 < S := hx.trans_le hxS
    positivity
  have hev : ∀ᶠ i in l, S ≤ M i μ' h' := by
    filter_upwards [hchar, (hM μ h hh).eventually_const_lt (hy.2.trans_le hxm)] with i hi i4
    exact hi μ h y S μ' h' hμ hh hy.1 i4.le (hy.2.le.trans hxS) hS hlo h1y h2y h3y
  exact ge_of_tendsto (hM μ' h' hpos') hev

/-- Lemma B for a family of tori with `χ_i → ∞`, carried to the pointwise limit at `μ'`. -/
theorem abfD_limit {ι : Type*} {l : Filter ι} [l.NeBot] (M : ι → ℝ → ℝ → ℝ)
    (χ hmax : ι → ℝ) (m : ℝ → ℝ → ℝ) (Φ : ℝ → ℝ) (μlo μhi s₀ μ0 S μ' : ℝ)
    (hchar : ∀ᶠ i in l, abfD_Char (M i) Φ μlo μhi s₀ (hmax i))
    (hhmax : ∀ᶠ i in l, 3 * s₀ / χ i ≤ hmax i)
    (hχ : ∀ᶠ i in l, Tendsto (fun h => M i μ0 h / h) (𝓝[>] 0) (𝓝 (χ i)))
    (hχtop : Tendsto χ l atTop)
    (hΦ0 : ∀ x, 0 < x → x ≤ s₀ → 0 ≤ Φ x) (hμ0 : μ0 ≤ μhi)
    (hM : ∀ h, 0 < h → Tendsto (fun i => M i μ' h) l (𝓝 (m μ' h)))
    (hS : 0 < S) (hSs : S ≤ s₀) (hlo : μlo ≤ μ') (hμ' : μ' < μ0 - Φ S) :
    ∀ h', 0 < h' → S ≤ m μ' h' := by
  intro h' hh'
  have hd : Tendsto (fun i => 2 * S / χ i) l (𝓝 0) := tendsto_const_nhds.div_atTop hχtop
  refine ge_of_tendsto (hM h' hh') ?_
  filter_upwards [hchar, hhmax, hχ, hχtop.eventually_gt_atTop 0, hd.eventually_lt_const hh']
    with i h1 h2 h3 h4 h5
  exact abfD_torus (M i) Φ μlo μhi s₀ (hmax i) μ0 (χ i) h1 hΦ0 hμ0 h4 h2 h3 S μ' h' hS hSs hlo
    hμ' h5

/-- Power case of the limit: `m(μ', h') ≥ min(s₀, (θ(μ0 − μ')/C)^{1/θ})` for all `h' > 0`. -/
theorem abfD_limit_pow {ι : Type*} {l : Filter ι} [l.NeBot] (M : ι → ℝ → ℝ → ℝ)
    (χ hmax : ι → ℝ) (m : ℝ → ℝ → ℝ) (C θ μlo μhi s₀ μ0 μ' : ℝ) (hC : 0 < C) (hθ : 0 < θ)
    (hs₀ : 0 < s₀)
    (hchar : ∀ᶠ i in l, abfD_Char (M i) (fun s => C * s ^ θ / θ) μlo μhi s₀ (hmax i))
    (hhmax : ∀ᶠ i in l, 3 * s₀ / χ i ≤ hmax i)
    (hχ : ∀ᶠ i in l, Tendsto (fun h => M i μ0 h / h) (𝓝[>] 0) (𝓝 (χ i)))
    (hχtop : Tendsto χ l atTop) (hμ0 : μ0 ≤ μhi)
    (hM : ∀ h, 0 < h → Tendsto (fun i => M i μ' h) l (𝓝 (m μ' h)))
    (hlo : μlo ≤ μ') (hμ' : μ' < μ0) (h' : ℝ) (hh' : 0 < h') :
    min s₀ ((θ * (μ0 - μ') / C) ^ (1 / θ)) ≤ m μ' h' := by
  have hY : 0 < θ * (μ0 - μ') / C := div_pos (mul_pos hθ (by linarith)) hC
  have claim : ∀ t, 0 < t → t < min s₀ ((θ * (μ0 - μ') / C) ^ (1 / θ)) → t ≤ m μ' h' := by
    intro t ht0 ht
    have hts : t < s₀ := ht.trans_le (min_le_left _ _)
    have htY : t < (θ * (μ0 - μ') / C) ^ (1 / θ) := ht.trans_le (min_le_right _ _)
    have hpow : t ^ θ < θ * (μ0 - μ') / C := by
      have := Real.rpow_lt_rpow ht0.le htY hθ
      rwa [← Real.rpow_mul hY.le, one_div_mul_cancel hθ.ne', Real.rpow_one] at this
    refine abfD_limit M χ hmax m _ μlo μhi s₀ μ0 t μ' hchar hhmax hχ hχtop
      (fun x hx _ => div_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hx.le θ)) hθ.le)
      hμ0 hM ht0 hts.le hlo ?_ h' hh'
    have h1 := (lt_div_iff₀ hC).mp hpow
    have h2 : C * t ^ θ / θ < μ0 - μ' := by
      rw [div_lt_iff₀ hθ]; linarith
    show μ' < μ0 - C * t ^ θ / θ
    linarith
  have hb : 0 < min s₀ ((θ * (μ0 - μ') / C) ^ (1 / θ)) :=
    lt_min hs₀ (Real.rpow_pos_of_pos hY _)
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  by_cases ht0 : t ≤ 0
  · have := claim _ (half_pos hb) (half_lt_self hb)
    linarith
  · push Not at ht0
    exact claim t ht0 ht

# θ-1: proof of the θ-ABF (Dini) characteristics lemma (PROOF.md)

θ-1, 26 Nov 2026. Everything in §§1–5 is PROVED, checked here line by line, except where marked. The statements it serves are in STATEMENT.md.

## 1. Abstract setting

m : ℝ × (0,∞) → ℝ, with arguments (μ, h), satisfies:
- (M1) m is jointly differentiable (C¹);
- (M2) m is nondecreasing in h and nonincreasing in μ;
- (M3) m > 0.

On a finite torus all three hold: m is real-analytic, GKS II gives (M2), and GKS I with strictness gives (M3). These are the draft's inputs.

Data:
- a window W = [μ_-, μ_+];
- a level s₀ > 0;
- a ceiling h_max ∈ (0, ∞];
- F : (0, s₀] → [0, ∞) continuous;
- Φ_x(s) := ∫_x^s F(r) dr/r for 0 < x ≤ s ≤ s₀, and Φ(s) := Φ_{0⁺}(s) ∈ [0, ∞].

**(P)** For every (μ,h) with μ ∈ W, 0 < h ≤ h_max and m(μ,h) ≤ s₀:
  m ≤ h ∂_h m + F(m)·(−∂_μ m).

The power case is F = C s^θ, θ > 0, with Φ(s) = Cs^θ/θ. The draft's (ABF) with e = 0 is θ = 2, C = a.

## 2. Lemma A (characteristics, localised)

**Statement.** Assume (M1)–(M3) and (P). Let μ₀ ∈ W, h₀ > 0, 0 < x ≤ m(μ₀,h₀), and x ≤ S ≤ s₀. Let μ′, h′ satisfy
  μ_- ≤ μ′ < μ₀ − Φ_x(S)  and  h₀·S/x < min(h′, h_max⁺),
where h_max⁺ means "≤ h_max" if h_max = ∞ and "< h_max" otherwise. Then m(μ′, h′) ≥ S.

**Proof.**
1. **Choice of α.** The two strict inequalities are open in α, so we can fix α > 1 with
   μ₀ − αΦ_x(S) > μ′  and  h₀(S/x)^α < h′, h₀(S/x)^α ≤ h_max.
2. **The curve.** For s ∈ [x, S] put μ(s) := μ₀ − αΦ_x(s) and h(s) := h₀(s/x)^α.
   - Φ_x is C¹ on [x,S] with Φ_x′(s) = F(s)/s, since F is continuous on [x,S] ⊂ (0,s₀].
   - μ(s) is nonincreasing and h(s) is increasing.
   - Hence μ(s) ∈ [μ₀ − αΦ_x(S), μ₀] ⊂ (μ′, μ₀] ⊂ W, and h(s) ∈ [h₀, h₀(S/x)^α] ⊂ (0, h_max].
   - **The whole curve lies in W × (0, h_max].** This is the μ-window bookkeeping.
3. **The barrier function.** B(s) := m(μ(s), h(s)) is C¹ by (M1) and the chain rule, with
   s·B′(s) = α[ h(s) ∂_h m − F(s) ∂_μ m ]  evaluated at P(s) = (μ(s), h(s)).
4. **Behaviour at touching points.** Let g(s) := B(s) − s. Then g(x) = m(μ₀,h₀) − x ≥ 0.
   - Suppose g(s) = 0 for some s ∈ [x, S]. Then m(P(s)) = s ≤ S ≤ s₀, and P(s) ∈ W × (0, h_max] by step 2. So (P) applies at P(s), with F(m(P(s))) = F(s).
   - It gives s·B′(s) = α[h∂_hm + F(s)(−∂_μm)] ≥ α·m(P(s)) = αs > s. So g′(s) > 0.
   - (Neither −∂_μm ≥ 0 nor ∂_hm ≥ 0 is used in this step.)
5. **No crossing.** Suppose g(s₁) < 0 for some s₁ ∈ (x, S]. Let s* := sup{s ∈ [x,s₁] : g(s) ≥ 0}.
   - By continuity g(s*) = 0 and s* < s₁, and g < 0 on (s*, s₁].
   - But g′(s*) > 0 forces g > 0 just to the right of s*. This is a contradiction.
   - Hence g ≥ 0 on [x,S]. This is Mathlib's `image_le_of_deriv_right_lt_deriv_boundary'`, as in PP2ABF.
6. **Conclusion.** B(S) ≥ S. Then by (M2), using μ′ < μ(S) and h′ > h(S),
   m(μ′,h′) ≥ m(μ(S),h′) ≥ m(μ(S),h(S)) = B(S) ≥ S. ∎

**The region question raised in the brief.** "Does the characteristic reach m = s before leaving {m ≤ s₀}?" does not arise.
- The PDE is used only at touching points, where m equals the current level s ≤ S ≤ s₀.
- Away from touching points, B(s) > s, and B(s) may even exceed s₀. Nothing is used there.
- The only geometric requirement is that the curve stays in W × (0, h_max], and step 2 guarantees it.

## 3. Lemma B (per torus: divergence of χ only)

**Statement.** Assume the hypotheses of §1 and, in addition:
- m(μ₀,·) extends C¹ to h = 0 with m(μ₀,0) = 0 and ∂_hm(μ₀,0) = χ₀ ∈ (0,∞);
- (P) holds with h_max = 3s₀/χ₀;
- Φ(s₀) < ∞ (the Dini condition).

Then for every S ∈ (0, s₀], every μ′ ∈ W with μ′ < μ₀ − Φ(S), and every h′ > 2S/χ₀:
  m(μ′, h′) ≥ S.

**Proof.**
1. Since m(μ₀,h)/h → χ₀ and m(μ₀,h) → 0 as h ↓ 0, choose h₀ > 0 with m(μ₀,h₀)/h₀ ≥ (2/3)χ₀ and x := m(μ₀,h₀) ≤ S. Then x > 0 by (M3).
2. Check the conditions of Lemma A:
   - h₀S/x ≤ 3S/(2χ₀) < 2S/χ₀ < h′;
   - h₀S/x ≤ 3S/(2χ₀) < 3s₀/χ₀ = h_max;
   - Φ_x(S) ≤ Φ(S), so μ′ < μ₀ − Φ_x(S).
3. Lemma A applies. ∎

**Remarks.**
- Only divergence of χ is used: χ₀ enters only through the threshold h′ > 2S/χ₀. No rate, no GHS, and no h_min appear.
- The PDE is used only for h ≤ 3s₀/χ_{ε,L}(μ₀,0), i.e. at the flip scale.
- For μ″ ≤ μ₀, GKS gives χ(μ″,0) ≥ χ₀, so this region is the deep small-field region at every μ in the window.
- For θ = 2, C = 8(1+K)λ: Φ(S) = 4(1+K)λS². This is exactly the draft's step 6, with the slightly better constant 2S/χ₀ in place of 4s/X.

## 4. Theorem C (continuum consequence)

**Inputs.** Fix W = [μ_-, μ_+] with μ_+ < μ_c, and the data of §1 with Φ(s₀) < ∞.
- **Hypothesis (H_F).** There is L₀, and for each L ≥ L₀ an ε₀(L) > 0, such that for ε < ε₀(L) the torus magnetisation m_{ε,L} satisfies (P) with h_max = 3s₀/χ_{ε,L}(μ_+,0).
- **Draft inputs 7–8 (standard, as in v2):**
  - χ_{ε,L}(μ_+,0) → χ_L(μ_+) as ε → 0;
  - there are L_j → ∞ with χ_{L_j}(μ_+) ≥ 2X_j and X_j → ∞ (BDW definition plus Fable item 2);
  - p(μ,h) = lim_L lim_ε p_{ε,L}(μ,h), with p_{ε,L} convex in h and ∂_hp_{ε,L} = m_{ε,L}.

**Statement.** For μ ∈ W with μ < μ_+:
  M⁺(μ) := ∂_h⁺p(μ,0) ≥ min( s₀, Φ⁻¹(μ_+ − μ) ),  where Φ⁻¹(y) := sup{S ≤ s₀ : Φ(S) < y}.
- Power case: M⁺(μ) ≥ min(s₀, (θ(μ_+ − μ)/C)^{1/θ}).
- Since μ_+ is any point of (μ, μ_c) for which (H_F) holds on [μ, μ_+], qualitatively **M⁺(μ) > 0 for every μ < μ_c as soon as (H_F) holds on one window [μ, μ_+] ⊂ (−∞, μ_c).**

**Proof.**
1. Fix S ≤ s₀ with Φ(S) < μ_+ − μ (with μ ≥ μ_-), and fix j.
2. For ε < min(ε₀(L_j), ε₁(j)) we have χ_{ε,L_j}(μ_+,0) ≥ X_j.
3. By Lemma B with μ₀ = μ_+: m_{ε,L_j}(μ,h′) ≥ S for every h′ > 2S/X_j.
4. Since p_{ε,L_j} is convex in h with derivative m ≥ 0: p_{ε,L_j}(μ,h′) − p_{ε,L_j}(μ,0) ≥ S(h′ − 2S/X_j)₊.
5. Let ε → 0, then j → ∞ (the L-limit exists by assumption, so the subsequence L_j suffices): p(μ,h′) − p(μ,0) ≥ Sh′ for all h′ > 0.
6. Hence ∂_h⁺p(μ,0) ≥ S. Take the sup over admissible S. ∎

**Uniformity actually used.**
- One triple (F, s₀, W) for all L_j.
- ε₀ may depend on L.
- The PDE is needed only on {μ ∈ W, h ≤ 3s₀/χ_{ε,L}(μ_+,0), m ≤ s₀}.

## 5. Exponent bookkeeping and sharpness

1. **Any θ > 0 works.** More generally, any F with ∫_0 F(r)dr/r < ∞ works, e.g. F = C/log(e/r)^{1+δ}. **θ < 1 is not needed.**

2. **θ ≤ 0, or a non-Dini F, cannot work by any argument that uses only (M1)–(M3), (P), GHS and χ = ∞.** This is PROVED by a counterexample.
   - Take F > 0 continuous on (0,∞) with ∫_0 F/r = ∞, and put Φ̃(m) := ∫_{s₀}^m F(r)dr/r, so that Φ̃(0⁺) = −∞.
   - Define m(μ,h) by h = m·exp(μ + Φ̃(m)). Since d log h/d log m = 1 + F > 0 and h runs over (0,∞), this is a C¹ bijection m ↔ h.
   - Implicit differentiation gives h∂_hm = m/(1+F) and −∂_μm = m/(1+F). So **m = h∂_hm + F(m)(−∂_μm) with equality**.
   - m is increasing in h and decreasing in μ.
   - m/h = e^{−μ−Φ̃(m)} is decreasing in h (GHS form), and m/h → ∞ as h ↓ 0 for every μ. So χ = ∞ everywhere, μ_c = +∞.
   - Yet M⁺ = lim_{h↓0} m = 0.
   - Example: F ≡ C (θ = 0) gives m = (s₀^C e^{−μ}h)^{1/(1+C)}, a "critical everywhere" profile with δ = 1 + C.
   - So the Dini condition is the exact threshold for the PDE route.

3. **θ > 2.** The lemma still holds, and gives (θΔ/C)^{1/θ}.
   - However, (P) with θ > 2 at small m would require ∂_hR ≤ −(1 − o(1))∂_h⟨φ²⟩, because of the exact term 8λm²(−∂_μm) in the identity.
   - At weak coupling ∂_hR/∂_h⟨φ²⟩ = −24λΣG² + O(λ²) (perturbative, AUDIT §8c). So this fails.
   - **The usable range is 0 < θ ≤ 2.** θ = 2 is Lemma L, and θ < 2 is strictly weaker, by the factor (s₀/m)^{2−θ}.

4. **Translation to L-type constants.** If ∂_hR ≤ Km^{θ−2}∂_h⟨φ_0²⟩ on {m ≤ s₀} with 0 < θ ≤ 2, then (P) holds with C = 8λ(K + s₀^{2−θ}). The resulting bound is
   M⁺ ≥ min(s₀, [θ(μ_+−μ)/(8λ(K + s₀^{2−θ}))]^{1/θ}).

## 6. Derivation of Form V (STATEMENT §5)

Notation: duplicated system, η = √2h, Q = ε²Σq_x, N = L²/ε². At zero field the law μ₀ is invariant under (q ↦ −q, t fixed), and the system is translation invariant.

- **R/2 = E[q₀t₀²]/E[q₀].** Expanding (φ+φ′)(φ−φ′)² gives E_h[q₀t₀²] = ⟨φ;φ²⟩/√2, and E_h[q₀] = √2m.
- **The averages over π_η.** E_h[odd F] = E₀[F sinh ηQ]/E₀[cosh ηQ]. With translation invariance (N⁻¹Σ_x = ε²L⁻²Σ_x):
  - E_h[q₀t₀²] = L⁻²E₀[A(Q) sinh ηQ]/Z;
  - E_h[q₀] = L⁻²E₀[Q sinh ηQ]/Z.
  Dividing gives Theorem 7.1.
- **∂_hR = 2√2 Cov_{π_η}(Ψ, u coth ηu).** This follows from ∂_h = √2∂_η and ∂_η log(u sinh ηu) = u coth ηu.
- **∂_h⟨φ₀²⟩.** We have ∂_h⟨φ₀²⟩ = ⟨φ₀²; ε²Σ_yφ_y⟩ = ½E[(φ₀²−φ₀′²)(M−M′)]. Since φ₀² − φ₀′² = 2q₀t₀ and M − M′ = √2·ε²Σ_y t_y =: √2T, this equals √2E_h[q₀t₀T].
  - The integrand is odd in q, so E_h[q₀t₀T] = L⁻²E₀[D(Q) sinh ηQ]/Z, with D(u) = E₀[(ε²Σq_xt_x)T | Q=u].
  - Dividing by √2m = L⁻²E₀[Q sinh ηQ]/Z gives ∂_h⟨φ₀²⟩ = 2m E_{π_η}[D/u] = 2m E_{π_η}Ξ.
- **Gaussian check.** q ⟂ t, E[q_x|Q=u] = u/L², and ε²Σ_xE[t_xT] = L²χ. So D = uχ, Ξ ≡ χ, and ∂_h⟨φ²⟩ = 2mχ. ✓
- **Chebyshev step for (b).** Write f = u coth ηu, which is increasing. If Ψ − Au/L² is nonincreasing, then Cov_π(Ψ − Au/L², f) ≤ 0.

Form IV is proved in the same way, conditioning on M alone: ∂_μ log Z = −⟨N₂⟩ and the tilt e^{hM} depends on M only.

## 7. Lean: modifying PP2ABF (sketch; no Lean toolchain in this sandbox, nothing compiled)

The change is small, and simpler than the e-version (there is no Q factor).

```lean
/-- Dini/θ characteristic form, localised to a μ-window, a level s₀ and h ≤ hmax. -/
def abfθ_Char (m : ℝ → ℝ → ℝ) (Φ : ℝ → ℝ) (μlo s₀ hmax : ℝ) : Prop :=
  ∀ μ h x s μ' h' : ℝ, 0 < h → 0 < x → x ≤ m μ h → x ≤ s → s ≤ s₀ →
    μlo ≤ μ' → μ' < μ - (Φ s - Φ x) → h * (s / x) < h' → h * (s / x) < hmax →
    s ≤ m μ' h'

theorem abfθ_char_of_pde (m mμ mh : ℝ → ℝ → ℝ) (F Φ : ℝ → ℝ) (μlo μhi s₀ hmax : ℝ)
    (hmono : ∀ μ h h', 0 < h → h ≤ h' → m μ h ≤ m μ h')
    (hanti : ∀ μ μ' h, 0 < h → μ ≤ μ' → m μ' h ≤ m μ h)
    (hdiff : ∀ μ h, 0 < h → HasFDerivAt (fun p : ℝ × ℝ => m p.1 p.2)
      (mμ μ h • ContinuousLinearMap.fst ℝ ℝ ℝ + mh μ h • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ, h))
    (hΦ : ∀ s, 0 < s → s ≤ s₀ → HasDerivAt Φ (F s / s) s) (hF : ∀ s, 0 < s → 0 ≤ F s)
    (hpde : ∀ μ h, 0 < h → h ≤ hmax → μlo ≤ μ → μ ≤ μhi → m μ h ≤ s₀ →
      m μ h ≤ h * mh μ h + F (m μ h) * (-(mμ μ h))) :
    ∀ μ, μ ≤ μhi → [abfθ_Char restricted to starting points μ ≤ μhi]
```

Steps:
- **Barrier.** Use μf s = μ0 − α(Φ s − Φ x) and hf s = h0·exp(α(log s − log x)).
  - The touching computation is s·B′ = α(hf·mh − F s·mμ) ≥ αs, using hpde at m = s ≤ S ≤ s₀.
  - The window membership μf s ∈ [μ′, μ0] comes from monotonicity of Φ (hF).
  - `image_le_of_deriv_right_lt_deriv_boundary'` is used unchanged.
- **Power case.** Φ s = C s^θ/θ, via `Real.hasDerivAt_rpow_const` (s > 0).
- **Part A(i)** becomes `abfθ_torus` (Lemma B: hypothesis `HasDerivAt (m μ0) χ0 0`, m μ0 0 = 0, conclusion for h′ > 2S/χ0) plus the convexity/pressure step. The `hchi`/sup = ∞ version also goes through: replace `a s²/2` by Φ S.
- **Limits.** `abf_char_of_tendsto` carries over verbatim when Φ is fixed (continuity of Φ at x is needed for the y < x approximation).
- **Counterexample (§5.2)** as a Lean sanity theorem: optional, needs the implicit-function construction. Skip.

Estimated size: about 250 lines, mostly a copy of `abf_barrier`, `abf_char_of_pde` and `abf_ordered_level` with e = 0 and a² ↦ Φ. Risk is low. The genuinely new pieces are the window hypotheses (μlo/μhi/hmax/s₀) threaded through `hpde`.

# θ-1: the weakened lemma, in all forms (STATEMENT.md)

θ-1, 26 Nov 2026. The proof of the characteristics lemma is in PROOF.md. Status labels: PROVED means checked here line by line. HEUR means a heuristic. NUM means numerical.

## 0. Conventions

These are the draft's (T2b_conditional v2 §1).
- Torus Λ_{ε,L} = εℤ²/Lℤ², with |T| = L² (the continuum area).
- The physical field is h, coupled as ε²hΣ_xφ_x. In lattice units, H_lat = ε²h.
- Write m = ⟨φ_0⟩ and χ = ∂_h m = ε²Σ_x⟨φ_0;φ_x⟩.
- −∂_μ m = ½ε²Σ_y⟨φ_0;φ_y²⟩ ≥ 0. Since c_ε is μ-independent, ∂_μ = ∂_{μ_bare}.
- Dimensions: m is dimensionless (d = 2); h, μ and λ have dimension mass².
- Cumulants: U3 := ε²Σ_x u3(0,0,x) = ∂_h G(0,0) ≤ 0 (GHS), and U4 := ε²Σ_x u4(0,0,0,x).
- Exact relations: −∂_μ m = ½∂_h⟨φ_0²⟩ = mχ + ½U3.

Window: W = [μ_-, μ_+] with μ_+ < μ_c (the BDW threshold). For qualitative M⁺(μ) > 0 at one μ, W = [μ, μ_+] with any μ_+ ∈ (μ, μ_c) is enough.

## 1. Form I (primary: the PDE, no R at all)

**(H_F)** Let F : (0, s₀] → [0,∞) be continuous with the Dini condition
  Φ(s) := ∫_0^s F(r) dr/r < ∞.
Then for every L ≥ L₀ there is ε₀(L) > 0 such that for all ε < ε₀(L), all μ ∈ W, and all h > 0 with m_{ε,L}(μ,h) ≤ s₀:

  m − hχ ≤ F(m)·(−∂_μ m).

The power case is F(s) = C s^θ with θ > 0, which gives Φ(s) = C s^θ/θ. This is "(H_θ)".

**Conclusion** (PROVED in PROOF.md, given the draft's steps 7–8):
  M⁺(μ) = ∂_h⁺p(μ,0) ≥ min(s₀, Φ⁻¹(μ_+ − μ)) for every μ ∈ W, μ < μ_+.
- Power case: M⁺(μ) ≥ min(s₀, (θ(μ_+ − μ)/C)^{1/θ}).
- With θ = 2 and C = 8(1+K)λ this is the draft's M⁺² ≥ Δ/(4(1+K)λ), capped at s₀.

**Facts about the hypothesis:**
- **Only the region near h = 0 is used.** It is enough that (H_F) holds for h ≤ 3s₀/χ_{ε,L}(μ_+, 0). The characteristic never leaves this region (PROOF §3).
- **Only touching points are used.** The PDE is invoked only at points where m equals the current level s ≤ s₀. So "the characteristic leaves {m ≤ s₀}" is not an issue (PROOF §2).
- **The Dini condition is sharp for the PDE argument (PROVED, PROOF §5).** For F ≡ C (θ = 0), m(μ,h) = (he^{−μ})^{1/(1+C)} satisfies everything, with equality: χ(μ,0⁺) = ∞ for every μ, monotone, GHS-type, yet M⁺ ≡ 0. The same construction works for any F with ∫_0 F/s = ∞. So θ > 0 (or a Dini log-gain, e.g. F = C/log(1/s)^{1+δ}) is necessary for this route. θ < 1 is not needed.
- **θ > 2 is useless and false.** The identity forces m − hχ = 8λm²(−∂_μm)(1 + ∂_hR/∂_h⟨φ²⟩). At weak coupling, ∂_hR/∂_h⟨φ²⟩ = −24λΣG² + O(λ²) > −1, so m − hχ ≥ 4λm²(−∂_μm) for small λ (perturbative, not a theorem). That is incompatible with C m^θ, θ > 2, as m → 0. **The meaningful range is 0 < θ ≤ 2.** θ = 2 is Lemma L, and θ < 2 is strictly weaker.
- **ε-uniformity is clean.** m, hχ and −∂_μm = mχ + ½U3 are all continuum-normalised quantities with finite ε → 0 limits at fixed (μ,h,L). So C, θ and s₀ are meant ε-independent with no rescaling.
  - In lattice units the same statement reads m − H_lat χ_lat ≤ (C/2λ)·b·m^θ·(−∂_a m), with b = λε², a = 2 + ½ε²μ_bare and χ_lat = ε^{−2}χ.
  - So the lattice constant is C_lat = (C/2λ)·b = O(ε²), and the uniform object is C_lat/b.

## 2. Form II (R-form; exact equivalence)

From the exact identity m − hχ = 4λm²∂_hR + 8λm²(−∂_μm) (draft step 4) and ∂_h⟨φ_0²⟩ = 2(−∂_μm) ≥ 0:

  (H_F) ⟺ ∂_h R ≤ ( F(m)/(8λm²) − 1 )·∂_h⟨φ_0²⟩  on {m ≤ s₀}.

**Fable's form.** ∂_hR ≤ K m^{θ−2}∂_h⟨φ_0²⟩ on {m ≤ s₀}, with θ ≤ 2, implies (H_θ) with
  C = 8λ(K + s₀^{2−θ}).
- Reason: 8λ(Km^θ + m²) ≤ 8λ(K + s₀^{2−θ})m^θ.
- So the weakening factor over L is (s₀/m)^{2−θ}, which is large at small m.

**ε.** R = 2G(0,0) + u3(000)/m contains 2G(0,0) = 2c_ε + O(1), which diverges like (1/π)log ε⁻¹.
- c_ε is h-independent, so ∂_hR is ε-uniform. In Form III the G(0,0) terms cancel identically.
- R itself should never be bounded, only ∂_hR. Equivalently, work with R − 2c_ε.

## 3. Form III (cumulants)

By Leonov–Shiryaev, κ(φ_0,φ_0²,φ_x) = u4(000x) + 2G(00)G(0x) + 2m·u3(00x). The 2G(00)χ terms cancel against χ⟨φ_0;φ_0²⟩ = χ(u3(000) + 2mG(00)). This gives (PROVED, algebra)

  m²∂_hR = m U4 + 2m² U3 − χ u3(000),    ∂_h⟨φ_0²⟩ = U3 + 2mχ.

So (H_F) is equivalent to

  m U4 + 2m² U3 − χ u3(000) ≤ ( F(m)/(8λ) − m² )·(U3 + 2mχ)  on {m ≤ s₀}.

**ε.** u3(000), U3 and U4 each have ε-uniform limits. The tree-level forms are:
- u3(000) ≈ −24λm·ε²Σ_wG(0w)³;
- U3 ≈ −24λmχ·ε²Σ_wG(0w)²;
- U4 has G(0w)³ and G(0w)²-type kernels.

All of these are integrable in d = 2. This is perturbative only; it is not proved non-perturbatively.

**Sizes.** The "trivial size" of the bad term −χu3(000)/m² is O(λχ/m). On the right, ∂_h⟨φ²⟩ ≈ 2mχ. So the ratio needed is O(λ/m²), which is θ = 0 in Form I.
- **(H_θ) asks for a gain m^θ over the trivial size, for any θ > 0, or even only a Dini gain.** L (θ = 2) asks for the full gain m².

## 4. Form IV (one variable: the zero-field law of the torus magnetisation)

The field couples only to M := ε²Σ_xφ_x, and ∂_μ couples only to N₂ := ½ε²Σ_x:φ_x²:. Define:
- ρ_μ = the zero-field law of M on Λ_{ε,L};
- n_μ(v) := E_μ[N₂ | M = v], which is even;
- F_μ(h) := log∫e^{hv}ρ_μ(dv).

Then (PROVED, exact):
- m = L⁻²F_μ′(h);
- χ = L⁻²F_μ″(h);
- −∂_μ m = L⁻² Cov_{ρ_{μ,h}}(v, n_μ(v)) = −L⁻²∂_μF_μ′(h), where ρ_{μ,h} ∝ e^{hv}ρ_μ.

So (H_θ) reads

  F′ − hF″ ≤ C (F′/L²)^θ · (−∂_μF′)   whenever F′ ≤ s₀L²,

which is a statement about the one-parameter family μ ↦ ρ_μ of even measures on ℝ alone.

**Small-h check (PROVED, Taylor).** At fixed torus, m = χ₀h + ū4h³/6 + O(h⁵), with ū4 = ε⁶Σu4 ≤ 0 (Lebowitz). Then:
- m − hχ = |ū4|h³/3 + O(h⁵);
- −∂_μm = h(−∂_μχ₀) + O(h³).

For θ < 2, (H_θ) holds automatically for h < h_*(ε,L). The content is uniformity in L at the crossover m ~ s₀, i.e. hχ₀ ~ s₀. At θ = 2 the h → 0 limit is the Aizenman–Graham-type bound |ū4| ≤ 3Cχ₀²(−∂_μχ₀). This is not automatic. (Literature check: whether the μ-derivative version of AG is known for φ⁴ was not looked up.)

## 5. Form V (Theorem 7.1, integrated in u) — the input for θ-3

**Setup.** Duplicate: q = (φ+φ′)/√2 and t = (φ−φ′)/√2, both copies at field h. Then the field term is ηQ, with η := √2h and Q := ε²Σ_x q_x = (M+M′)/√2. Let P₀ = the law of Q at zero field, which is even. Define
- π_η(du) ∝ u sinh(ηu)P₀(du) on u > 0;
- Ψ(u) := E₀[ε²Σ_x q_x t_x² | Q=u]/u (Theorem 7.1);
- Ξ(u) := E₀[(ε²Σ_x q_x t_x)(ε²Σ_y t_y) | Q=u]/u (new).

Then (PROVED; derivation in PROOF.md §6):
- R/2 = E_{π_η}[Ψ];
- ∂_hR = 2√2 Cov_{π_η}(Ψ, u coth ηu);
- ∂_h⟨φ_0²⟩ = 2m·E_{π_η}[Ξ];
- √2 L² m = E₀[Q sinh ηQ]/E₀[cosh ηQ].

The factor 2√2 comes from ∂_h = √2∂_η. In the Gaussian case, Ξ ≡ χ and Ψ is constant.

**(H_θ) in integrated form:**

  √2 Cov_{π_η}(Ψ, u coth ηu) ≤ ( C m^{θ−1}/(8λ) − m )·E_{π_η}[Ξ]   on {m ≤ s₀}.

Note that u ↦ u coth ηu is increasing.

### Sufficient properties of Ψ (PROVED reductions)

**(a)** Ψ nonincreasing implies K = 0 (known).

**(b) One-sided Lipschitz on the density scale.** Suppose that, for some A ≥ 0 uniform in (ε,L,μ ∈ W), u ↦ Ψ(u) − A·u/L² is nonincreasing on (0,∞). Then by Chebyshev (u coth ηu is increasing):
  ∂_hR ≤ 2√2 (A/L²) Cov_{π_η}(u, u coth ηu).
So (H_θ) follows from the Ψ-free comparison

  (C_A)  √2 (A/L²) Cov_{π_η}(u, u coth ηu) ≤ ( C m^{θ−1}/(8λ) − m ) E_{π_η}[Ξ]   on {m ≤ s₀}.

- **Why the density scale.** Ψ is intensive in u/L². The bulk of π_η sits at u ≈ √2L²M₊. So a bound on the oscillation of Ψ alone is not enough: it loses a factor L, from the peak width L√χ_p against L². A growth bound on the scale du ~ L² is the natural form.
- **Any decomposition works.** For Ψ = Ψ↓ + Ψ_r with Ψ↓ nonincreasing, only the increasing part of Ψ_r costs anything:
  Cov_π(Ψ, f) ≤ ∫∫_{u>v} (Ψ_r(u)−Ψ_r(v))₊ (f(u)−f(v)) π(du)π(dv).

**(c) What happens in the flip regime (HEUR, two-phase picture).** Here P₀ has mass ½ near 0 (copies opposite) and ¼ near ±√2L²M₊ (copies aligned).
- Ψ(0⁺) ≈ 2M₊² + G_p(0,0), while Ψ(√2L²M₊) ≈ G_p(0,0). So Ψ steps **down** by ≈ 2M₊² between the two bumps: the flip structure itself has the good sign.
- On {m ≤ s₀} we have x := L²M₊h ≲ s₀/M₊ ≪ 1, so u coth ηu ≈ 1/η + ηu²/3 on the π-bulk.
- Then √2(A/L²)Cov_π(u, u coth ηu) ~ (A/L²)·η·ū·Var_π(u) ~ A·ηL²M₊χ_p ~ A·mχ_p/M₊, using ū = √2L²M₊, Var(u) ~ L²χ_p and η ≈ √2m/(L²M₊²). The right side of (C_A) is ~ (C/8λ)m^{θ−1}χ_p, because E_πΞ = (−∂_μm)/m ~ χ_p. The small-u bump contributes at the same order.
- The ratio is ~ (8λA/C)·m^{2−θ}/M₊ ≤ (8λA/C)·s₀^{2−θ}/M₊.
- **So for θ < 2, (C_A) holds in the flip regime for s₀ small, for any A.** The θ-room is a factor (M₊/s₀)^{2−θ}. The only real constraint is the uniform one-sided Lipschitz bound (b) on the interface plateau between the two bumps of P₀.

### What θ-3 needs, in one line

For μ ∈ W, all large tori, and η ≲ s₀/(L²M₊²), i.e. in the regime where u coth ηu − 1/η ≈ ηu²/3:

  Cov_{π₀}(Ψ, u²) ≤ (3/(√2η)) (C m^{θ−1}/(8λ) − m) E_{π₀}Ξ ≈ (3C/(8√2λ)) m^{θ−2} χ₀ E_{π₀}Ξ.

Here π₀ ∝ u²P₀(du) and m ≈ ηχ₀/√2. The m^{θ−2} = (ηχ₀)^{θ−2} blow-up as η → 0 is the slack.
- This is HEUR: the step from Cov_{π_η}(Ψ, u coth ηu) to (η/3)Cov(Ψ, u²) needs tail control of P₀ at u ≳ 1/η.
- A rigorous replacement is to keep u coth ηu and use (b).

## 6. Uniformity actually needed (summary)

- **Constants.** One set (θ, C, s₀) for a compact window W ⊂ (−∞, μ_c). It may depend on W.
- **Volumes and spacings.** All L ≥ L₀, and ε < ε₀(L). ε₀ may depend on L, because the draft chooses ε_j after L_j.
- **Region.** μ ∈ W, 0 < h ≤ 3s₀/χ_{ε,L}(μ_+,0), m ≤ s₀. This is the finite-volume flip regime, at magnetisations far below M₊ if s₀ ≪ M₊.

## 7. Numerics (NUM; cw_theta.py, cw_runs.log)

**Model and method.** Curie–Weiss φ⁴, i.e. weight exp((J/2N)M² + hM − Σ(aφ²+bφ⁴)), computed by exact Hubbard–Stratonovich quadrature.
- In this model the identity reads m − hχ = 4bm²∂_hR + 4bm²(−∂_am). It was checked against finite-difference ∂_hR to about 1e−3 to 1e−4 (grid-limited).
- So L (K = 0) ⟺ r_2 ≤ 1, where r_θ := (m − hχ)/(4b m^θ(−∂_am)). The quantity tabulated is sup r_θ over {m ≤ s₀}, for h ∈ [1e−7, 1].
- N = 16, 64, 256, 1024, 4096. Six broken-phase sets (a, b, J): (0.5, 1, 4), (0.5, 1, 3.7) (J_c = 3.59), (2, 0.1, 4.6) (J_c = 4.27), (2, 0.1, 6), (1.9, 0.02, 4) (T2b-like), (−1, 1, 3). The (0.5, 1, 4) run was interactive and is not in the log; rerun with `python3 cw_theta.py 0.5 1 4`.
- χ reaches 3·10³ to 2·10⁴, which is the flip regime.

**Results** (N-uniform, from N = 16 to 4096, in every set):
- **θ = 2.** sup r_2 ≈ 0.2–0.4 on m ≤ 0.1, and 0.35–0.77 on m ≤ 0.8. L holds.
  - Restricting to small m alone gains only a factor of about 2–3. This matches the two-phase prediction f(0⁺)/f(∞) = 1/3, where f(x) = (tanh x − x sech²x)/(tanh²x(tanh x + x sech²x)).
  - Some isolated θ = 2 spikes at s₀ = 0.05 are cancellation noise at m < 1e−3; the θ < 2 columns there are clean.
- **θ = 1.** sup r_1 ≈ 0.27·s₀: 0.010–0.015 at s₀ = 0.05, 0.020–0.032 at 0.1, 0.04–0.06 at 0.2.
- **θ = 1.5, 0.5.** These scale as s₀^{0.5} and s₀^{1.5} respectively.

**Reading.** The needed constant C_θ(s₀)/(4b) is ≈ 0.27 s₀^{2−θ}, uniformly in N. Equivalently, the θ-route tolerates a violation of L by a factor of up to about 3(M₊/s₀)^{2−θ}.
- In the flip regime it is therefore not a quantitative inequality at all: any C > 0 works for s₀ small enough.
- Caveat: this is mean-field. The 2D difficulty is the interface plateau of P₀ (STATEMENT §5(b)), which Curie–Weiss does not have.

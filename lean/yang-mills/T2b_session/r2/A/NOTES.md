# A notes — thermodynamic / structural angle (round 2, 26 Nov 2026)

Labels: PROVED (checked here), STD (standard, with source), HEUR, NUM.
Scripts here: mixsign.py, rsurv.py (both reuse theta1/cw_theta.py; CW φ⁴, exact HS quadrature).

## 0. Summary
1. **No-go filter (PROVED from STD inputs).** The 2D nearest-neighbour plane rotator (XY), with temperature T in the role of μ and the field along e₁, satisfies (M1)–(M3), Ginibre (GKS I/II), Lee–Yang in h, and χ_L → ∞ on a whole interval of T. Yet it has M⁺ = 0 (Mermin). So by θ-1's Theorem C, **(P) with a Dini F fails for XY on every window inside its KT phase.** Hence any proof of (P) must use a property that the plane rotator does not have, i.e. something one-component (Z₂ / random-current / FKG-specific). θ-1's counterexample is not artificial: XY is a lattice model that realises it.
2. **XY sits exactly on the Dini threshold (HEUR, spin wave).** m ≈ A(T)h^{α(T)}, α = η/(4−η), gives (P) with F(m) ≈ α(1−α)/(α′|log m|), and ∫dr/(r|log r|) = ∞. So the Dini condition is sharp for a real model too.
3. **My brief's candidates are excluded as discriminators** (§2): mixed-derivative signs, GHS in the (h,μ)-plane, Lee–Yang (including μ-monotone zero density), block-level EMN plus the one-site theorem, and joint convexity. Each holds for θ-1's power-law counterexample and/or for XY.
4. **Mechanism (PROVED identity, NUM).** S := −∂_a m = N Cov(σ(Y),Y), and σ = y² + v(y). In XY the transverse fluctuations in v cancel the zero-mode growth of y². For one component there is no transverse mode. In CW the surviving fraction r = S/(2mχ + χ′/N) is constant in N and h (0.73 to 0.99). But r → 0 at a 2D Ising critical point, so "r ≥ r₀" is not a soft inequality (§3).
5. **Best remaining candidate**: a one-component, current-type statement in which a pivotal *site* (quartic vertex) costs b = λε², rather than a bond costing O(1) as in ABF (§4).

## 1. The XY no-go filter

**Setting.** Torus Λ_L = (ℤ/Lℤ)². Spins σ_x ∈ S¹. Weight exp(βΣ_{⟨xy⟩}σ_x·σ_y + hΣ_xσ_x¹). Write m_L(T,h) = ⟨σ_0¹⟩ and T = 1/β.

**Inputs.**
- (i) **Smoothness and positivity.** m_L is real-analytic in (T,h), and m_L > 0 for h > 0. This is Ginibre's GKS I with strictness; STD, Ginibre CMP 16 (1970).
- (ii) **Monotonicity in T.** ∂_β m_L = Σ_{⟨xy⟩}⟨σ_0¹; σ_x·σ_y⟩ ≥ 0, by Ginibre's GKS II (STD, same source). So m_L is nonincreasing in T, which is (M2) with μ ↦ T.
- (iii) **Divergent susceptibility in the KT phase** (STD).
  - Fröhlich–Spencer, CMP 81 (1981) 527, and van Engelenburg–Lis, CMP 2023 (arXiv:2110.09465; abstract read), give ⟨σ_0·σ_x⟩ ≥ c|x|^{−η(T)} with η < 2 for T < T₁.
  - At h = 0 the translation-invariant Gibbs state is unique when M = 0. This is Bricmont–Fontaine–Landau, CMP 56 (1977) 281 (abstract read).
  - So torus states converge to that state, and by Fatou liminf_L χ_L(T) = ∞.
- (iv) **Zero spontaneous magnetisation.** Mermin (1967, classical XY in d = 2): the infinite-volume m(h) → 0 as h ↓ 0. Hence ∂_h⁺p(T,0) = 0, by convexity. STD, not re-read.
- (v) **Pressure limit.** p_L → p, convex in h, for a finite-range lattice model. STD.

**Proposition A1 (PROVED, given (i)–(v)).** Let W = [T₋, T₊] ⊂ (0, T₁) with T₋ < T₊, let s₀ > 0, and let F be any Dini function. Then for every L₀ there is a torus L ≥ L₀ and a point (T, h) with T ∈ W, h ≤ 3s₀/χ_L(T₊,0) and m_L ≤ s₀ at which (P) fails, i.e.

  m_L > h∂_hm_L + F(m_L)(−∂_T m_L).

**Proof.** Otherwise θ-1's Theorem C applies verbatim, with μ ↦ T and no ε:
- inputs 7–8 hold by (iii) and (v);
- (M1)–(M3) hold by (i) and (ii).
It gives ∂_h⁺p(T,0) ≥ min(s₀, Φ⁻¹(T₊ − T)) > 0 for T₋ ≤ T < T₊, which contradicts (iv). ∎

**Consequence (logic).** Suppose an argument derives (P) from a list of properties, all of which hold for the plane rotator with T in the role of μ. Then that argument is wrong. The filtered properties include:
- GKS I/II (Ginibre);
- Lee–Yang in a uniform complex field: Dunlop CMP 69 (1979), Lieb–Sokal (1981). Seen cited in arXiv:1205.6643, Thm 4; not read in the original.
- Simon–Lieb and reflection positivity / infrared bounds (STD);
- the Gaussian (Lebowitz-type) inequality for rotators: Bricmont, J. Stat. Phys. 1977. Title seen only; the page fetch was blocked.
- every property that holds for an arbitrary exponential family: joint convexity of p in (h, −μ), and convex–concavity of the partial Legendre transform I(μ,y).

GHS for rotators: I did not find a proof (arXiv:1205.6643 cites GHS only for Ising-type spins), so it is not on the filtered list.

**Caveat.** For XY the parameter is a coupling, T, not a single-site mass. An argument that uses the specific form ∂_μ ↔ ε²Σφ² (a local φ² insertion) is not filtered by A1. The soft O(2) φ⁴ model with mass parameter a would filter that too. But I have not verified −∂_a⟨φ¹_0⟩ ≥ 0, or a rigorous KT phase, for soft O(2) spins, so that version is HEUR.

**A2 (HEUR, spin wave).** Write θ for the spin angle. In a field, θ is Gaussian with stiffness β and mass² ≈ hm/β. Then m = exp(−½⟨θ²⟩) gives m ≈ A(T)h^{α(T)}, with α = (T/8π)/(1 − T/8π) = η/(4−η).
- m − hχ = (1−α)m.
- −∂_T m = m(α′|log h| − A′/A) ≈ m(α′/α)|log m|.
- So the best F is F(m) ≈ α(1−α)/(α′|log m|): non-Dini, at the borderline.

## 2. Candidates from the brief: verdicts

The counterexample family with F ≡ C is m = (he^{−μ})^α, with α = 1/(1+C) ∈ (0,1). Write u := he^{−μ}.

**(a) Mixed-derivative / Griffiths-III signs. EXCLUDED (PROVED).**
- Each −∂_μ multiplies u^α by α > 0. So sgn ∂_h^j(−∂_μ)^k m = (−1)^{j+1} for j ≥ 1, and + for j = 0: every "natural" sign pattern holds.
- The differentiated form of (P), −h∂_hχ ≤ F·(−∂_μχ), also holds, with equality: the ratio is (1−α)/α = C.
- NUM (mixsign.py, CW a = 0.5, b = 1, J = 4): −∂_aχ > 0 for x = NmH ≲ 1, but it **changes sign** at x ≈ 1.2 (N = 1024: +481 at x = 0.24, −59 at x = 1.4). The zero-mode term NM₊²sech²x responds to M₊ with sign (1 − x tanh x).
- So a global "χ decreasing in μ at h > 0" is false. On {m ≤ s₀ ≪ M₊} it holds numerically, but it does not discriminate.

**(b) GHS in the (h,μ)-plane / multi-observable EMN. EXCLUDED.**
- EMN/Ellis–Newman multi-observable GHS covers linear observables only; φ² is not linear.
- Any sign statement on mixed cumulants of (M, N₂) is a sign of some ∂_h^j∂_μ^k p, so (a) applies.

**(c) Lee–Yang. EXCLUDED (PROVED).**
- The counterexample is Lee–Yang-representable: m(h) = ∫_0^∞ 2hρ_μ(dζ)/(ζ² + h²), with zero variable ζ and ρ_μ(dζ) = K e^{−αμ}ζ^α dζ. This uses ∫_0^∞ 2hζ^{s−1}/(ζ²+h²)dζ = c_s h^{s−1}, finite for 0 < s < 2, with s = 1 + α ∈ (1,2).
- The zero density is positive and **decreasing in μ**. So no statement about h-zeros and their μ-monotonicity can exclude it. Rotators also have Lee–Yang (A1).
- μ is not a Lee–Yang variable. For one Gaussian site, Z(a) = (π/a)^{1/2}e^{h²/4a} has no zeros in a, only a singular point at a = 0, so there is no zero-counting structure.

**(d) Block-spin / EMN preservation plus the one-site theorem. EXCLUDED.**
- EMN is not preserved under block sums: Ising/GS blocks are discrete, and the CW block law at J > J_c is a double well.
- More decisively, apply the one-site theorem to the law ν of M. It gives R_ν = Cov(M,M²)/EM nonincreasing.
  - R_ν = (F‴ + 2F′F″)/F′ with F = log Ee^{HM}. In density units, with g = F/N, this is ∂_H[g‴/(Ng′) + 2g″] ≤ 0.
  - As N → ∞ this becomes g‴ ≤ 0, which is just GHS (PROVED, algebra). It carries no μ-information, because ∂_μ couples to the local N₂, not to M².

**(e) Joint convexity of p(μ,h), or of I(μ,y). EXCLUDED (PROVED).**
- p is jointly convex for every exponential family, and I is convex in y and concave in μ.
- For the counterexample, p = e^μG(u) + g(μ) with G′ = f. Compute:
  - ∂_μ²[e^μG] = e^μ(G − uf + u²f′);
  - χ·∂_μ²p − (∂_μm)² = α²u^{2α}[α/(1+α) − 1] + g″αe^{−μ}u^{α−1}.
- This is ≥ 0 on any bounded u-range once g″ is large. g(μ) is invisible to m.

## 3. The mechanism: zero mode versus transverse compensation

**Identity (PROVED).** Use lattice units, N sites, Y = M/N, σ(y) = E₀[φ_0² | Y=y].
- v(y) := σ(y) − y² = E₀[(φ_0 − y)² | Y=y] ≥ 0, by Jensen and translation invariance.
- S := ∂_H⟨φ_0²⟩ = −∂_a m = N Cov_H(σ(Y),Y) = Z + N Cov_H(v(Y),Y), where Z := N Cov_H(Y²,Y) = 2mχ + χ′/N.
- At H → 0, Z/H → N²Var₀(Y²) ≥ 0.
- **Chebyshev lemma (PROVED).** If v is nondecreasing in |y|, then Cov_H(v,Y) ≥ 0. Proof: E[Y | |Y|=r] = r tanh(NHr), so Cov_H(v,Y) = Cov(v(|Y|), |Y|tanh(NH|Y|)) under the cosh-tilted law of |Y|, and both functions are increasing.
- In φ⁴, v typically **decreases**: the conditional mass grows with y².

**Surviving fraction r := S/Z.**
- Gaussian: r = 1.
- NUM, CW (rsurv.py), N = 64 and 1024, H from 10⁻⁵ to 1: r = 0.73 at (0.5,1,4); 0.987 at (1.9,0.02,4) (T2b-like); 0.945 at (2,0.1,4). Constant in N and H to 1%, including the flip regime.
- In CW the zero-mode bound alone already gives (Σ_θ), with r ≈ 0.73–0.99.

**Why "r ≥ r₀" is not the lemma to prove.**
- XY: S/(2mχ) ~ h|log m|/m → 0, by A2. The transverse modes compensate completely. This is the one-component distinction made quantitative.
- But r → 0 also at a 2D Ising critical point on the torus (HEUR, scaling). With Y ~ L^{−1/8} and σ − σ(0) ~ L^{−1}: Cov(σ,Y²)/Var(Y²) ~ L^{−3/4}.
  - (P) itself survives there, because Z ≫ m − Hχ (it needs only θ ≤ 1/β = 8).
- So r ≥ r₀ is a "non-critical" bound, as hard as M₊ > 0.
- A usable inequality must, like (P), hold uniformly through criticality.

**Diagnostic (HEUR).** (P) fails exactly when μ acts as a marginal (exponent-changing) deformation, −∂_μ log m ~ log(1/m), as in KT and in θ-1's counterexample (where −∂_μm = h∂_hm identically). (P) holds when μ is relevant, −∂_μ log m ≳ m^{−θ}.

## 4. Best remaining candidate (for B/C)

A1 forces a one-component tool, and the only known one that proves sharpness is the random current / switching lemma (ABF; Duminil-Copin–Tassion).
- **ABF's own loss.** Its pivotal objects are bonds. Σ_b J_b∂_{J_b} m picks up the local φ² response with weight O(ε⁻²), which is θ-2's factor 1/(2λε²).
- **The target form.** Identity (★) says the ε-uniform form is m ≤ hχ + 4b(1+K)m²(−∂_a m).
- **Candidate.** A switching-lemma inequality, in a φ⁴ current representation (tangled currents of Gunaratnam–Panagiotis–Panis–Severo; not read here), whose pivotal objects are **sites where two duplicated currents meet at a quartic vertex**, each costing a factor b. In lattice units:

  (SP) m − Hχ ≤ C b m^θ Σ_x⟨φ_0; φ_x²⟩   on {m ≤ s₀}.

- **Checks against the filters.**
  - It is one-component (currents), so A1 does not filter it.
  - It saturates at first order (C = 8, θ = 2).
  - It needs only θ > 0.
  - It survives criticality.
- **Test it** against RW1 (θ-2): m − Hχ ≤ 8bHT² already has the factor b. What is missing is converting HT² into m^θS, which is precisely the screening loss. A current proof would have to beat screening by using switching instead of FKG.

Not done:
- the soft O(2) version of A1;
- the clock-model (Z_N, N ≥ 5) analogue, which would show that discrete symmetry alone is not enough (unverified);
- any proof of (SP).

# Member C: exponent bounds and analytic routes (round 2)

Labels: PROVED (checked here) / STD (cited, read) / CITED-UNREAD / HEUR / NUM. Scripts in this directory: cw0.py, cw_ly.py.

## 1. (P) on the flip scale is a zero-field inequality (PROVED algebra, NUM-confirmed)
On a torus, let Y = M/|T| (M = ε²Σφ), with κ_n the zero-field cumulants of M. Write
M_L² := E Y² = χ₀/|T| and B_L := κ4/κ2² ∈ [−2, 0]. The lower bound −2 is Cauchy–Schwarz; the sign is Lebowitz.
Expanding in h: m = χ₀h + ū4h³/6 + …, with ū4 = κ4/|T|. Then m − hχ = |ū4|h³/3 + O(h⁵) and −∂_μm = h(−∂_μχ₀) + O(h³).
- Taylor variable: z² = G m², where G := −ū4/χ₀³ = |B_L|/M_L². Equivalently z = h(|B_L||T|χ₀)^{1/2}.
  - Flip regime: G = 2/M₊², so z = √2·x with x = h|T|M₊.
  - The radius is set by the first Lee–Yang zero: β₁ := |T|α₁ ≈ π/(2M₊).
- For F = Cm^θ the leading-order (P) is m^{2−θ}G ≤ 3C(−∂_μ log χ₀).
  - (P) is applied at m = s₀ (θ < 2: the worst point is the edge), where the leading order needs s₀√G ≲ 1. On that range (P) is equivalent to
  **(P₀)  −∂_μ M_L² ≥ |B_L| / K,  with K = 3C/s₀^{2−θ},**
  - equivalently |ū4| ≤ K χ₀²(−∂_μχ₀). This is a continuum, torus, μ-derivative form of an Aizenman–Graham-type bound.
  - θ drops out at this order: every θ ∈ (0, 2] asks for the same inequality, with a different constant.
- NUM (CW, three parameter sets, N = 16…4096): the predicted sup r_θ = s₀^{2−θ}|B|/(12b(−∂_aM²)) matches the exact sup over {m ≤ s₀} to 0–15% (cw0.py). This explains θ-1's "0.27 s₀^{2−θ}". The limit values are:
  - |B|/(−∂_aM²) = 2.53 at (a,b,J) = (.5,1,4);
  - 0.370 at (2,.1,4.6);
  - 0.078 at (1.9,.02,4);
  - all N-uniform.
- Checks of (P₀) in limiting regimes:
  - Ordered limit: B → −2, M_L → M₊, so (P₀) becomes −∂_μM₊² ≥ 2/K, the Landau bound. At θ = 2 the constant is 1/3 of the full-L value; that is θ-1's f(0⁺)/f(∞) = 1/3.
  - Finite χ: (P₀) becomes |u4| ≤ Kχ²(−∂_μχ) in infinite volume.
  - Ising-class critical torus: −∂_μM_L² ~ L^{(1−2β)/ν} → ∞ (2D Ising: L^{3/4}), so (P₀) holds with room. At mean-field criticality it is marginal: CW criticality gives −∂_aM² ≈ 0.24, N-independent.

## 2. (P₀) gives a dichotomy, with no characteristics needed (PROVED, given steps 7–8)
- (a) Integrate (P₀) over [μ, μ₀]: M_L²(μ) ≥ K⁻¹∫_μ^{μ₀}|B_L|.
- (b) **Torus LRO ⇒ M⁺.** If liminf M_L(μ) ≥ σ along the tori of step 7, then M⁺(μ) ≥ σ.
  - Proof: E Y⁴ = (3+B)(EY²)² ≤ 3(EY²)². Paley–Zygmund gives P(Y² ≥ tM_L²) ≥ (1−t)²/3.
  - By evenness, E e^{hM} = E cosh hM ≥ ⅙(1−t)² e^{h√t M_L|T|}.
  - Hence p_L(h) − p_L(0) ≥ h√t σ − O(1/|T|). By convexity and step 8, ∂_h⁺p ≥ √t σ for every t < 1.
- So (P₀), uniform in L and ε, gives: either M⁺ > 0 on W, or the torus magnetisation becomes Gaussian, B_L → 0 in L¹(W).
  - The missing piece is non-Gaussianity: liminf_L ∫_W |B_L| > 0 when χ_L → ∞. This is OPEN.
  - It cannot follow from Lee–Yang/GKS-type inputs alone, because a massless Gaussian field satisfies them.
  - The 1D chain and the finite-χ phase satisfy (P₀) through the B_L → 0 branch.

## 3. O(2)/KT obstruction (PROVED modulo cited theorems; CITED-UNREAD: Fröhlich–Spencer 1981, Mermin 1967, Ginibre 1970)
- For the 2D plane rotator (or O(2) φ⁴) at low temperature, with field along e₁ and β in place of −μ:
  - every input of θ-1's Lemmas A and B holds: Ginibre monotonicity in h and β, m > 0, convexity, and χ_L → ∞;
  - χ_L → ∞ comes from Fröhlich–Spencer's power-law lower bound, plus the Ginibre comparison torus ≥ free box.
- Lemma B with any Dini F would therefore give M⁺ > 0, which contradicts Mermin–Wagner.
- **Hence (P) fails for 2D O(2) for every Dini F and s₀, at some L.** So does (P₀): heuristically, in spin-wave terms, −∂_βM_L² ~ L^{−η} log L → 0 while B_L → B_KT ≠ 0.
- Consequences:
  - Any proof of (P) must use an input that is false for 2D O(2), i.e. genuinely Z₂-specific.
  - GKS/Ginibre and Lee–Yang (Dunlop–Newman, CITED-UNREAD) are excluded.
  - So is every exponent inequality that also holds for O(2).
  - Candidates that remain: random currents (ABF, AG), and the Z₂ duplication of zerod/θ-3.
  - θ-1's sharpness example m = (he^{−μ})^{1/(1+C)} has finite δ and −∂_μm ∝ m. That is the KT signature, so the Dini borderline is exactly KT.

## 4. Lee–Yang form (PROVED algebra; NUM)
- Z(h)/Z(0) = ∏(1 + h²/α_j²). Then (P) is equivalent to Σ_j (α_j² + h²)⁻²[2h² − F(m)∂_μα_j²] ≤ 0.
- In density units β_j = |T|α_j:
  - M_L² = 2Σβ_j⁻²;
  - B_L = −3Σβ_j⁻⁴/(Σβ_j⁻²)²;
  - (P₀) is implied termwise by ∂_μβ_j² ≥ 6/(K M_L⁴) for all j.
  - The first zero dominates, so this is essentially a Landau bound on the rescaled Lee–Yang edge: −∂_μ(β₁⁻²) ≥ c.
- NUM (cw_ly.py; CW b = 1, J = 4, a ∈ [0.2, 1], N ≤ 256):
  - every zero recedes as a increases (∂_a log β_j² > 0);
  - deep in the ordered phase β_jM_N → (2j−1)π/2, the cosh zeros;
  - at CW criticality β₁M_N → 1.97 and −∂_a(β₁⁻²) ≈ 0.09, N-independent.
  - Double precision cannot resolve the zeros in the disordered phase.
- The sign of the monotonicity is not enough: by §3 the quantitative bound is LRO-strength.

## 5. Exponent-inequality literature (status)
- Ising, h = 0 (read in Duminil-Copin's review arXiv:2208.00864 eq. (7.3)): (1 − B/χ)·2dχ²/(1+B) ≤ ∂_βχ ≤ 2dχ², with B the bubble.
  - The lower bound needs B ≪ χ; in 2D near criticality B ~ χ²/ξ², so it is useless.
- Continuum analogue (HEUR; needs the BFS skeleton inequality u4 ≥ −4!λ∫GGGG, CITED-UNREAD): −∂_μχ ≥ χ²(1 − 12λB). This is perturbative only.
- The tree bound |ū4| ≤ 2χ⁴ (lattice) loses ε⁻² and the volume factor |T| in the flip regime, since tree/(P₀) ~ λ|T|M₊⁴.
- Aizenman–Graham, Aizenman–Fernández 1986, and Glimm–Jaffe's φ⁴₂ exponent papers: NOT READ. I could not fetch statements this session.

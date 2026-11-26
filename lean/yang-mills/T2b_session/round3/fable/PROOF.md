# PROOF.md — results proved in this session (26 Nov 2026)

None of these proves (P) or (P0). They are unconditional partial results and one conditional reduction.
Labels: PROVED = full argument below, re-derived twice; CN = checked numerically (script named).

## 0. Setting and notation

Torus Λ with N sites, every site with 4 neighbours (side ≥ 3). Zero field.
Weight e^{−S}, S(φ) = Σ_x (aφ_x² + bφ_x⁴) − Σ_{⟨xy⟩} φ_xφ_y, b > 0.
- M = Σ_xφ_x, Y = M/N, Φ2 = Σ_xφ_x², Φ3 = Σ_xφ_x³, c = 2a − 4 (= ε²μ_b).
- m_k = ⟨Y^k⟩, χ = N m2 = Σ_x⟨φ0φ_x⟩, X = ⟨M²⟩ = Nχ.
- B = m4/m2² − 3 ∈ [−2, 0] (Lebowitz), τ := m4/(3m2) = m2(1 − |B|/3).
- m_H² := c + 12b⟨φ0²⟩ ("Hartree mass"; continuum: ε²(μ + 12λ⟨:φ²:⟩)).
- Continuum dictionary: b = λε², ∂_a = 2ε⁻²∂_μ, m2 = M_L², N b = λL².

Integration by parts (IBP): ⟨F ∂_xS⟩ = ⟨∂_xF⟩ for smooth F of polynomial growth (b > 0 kills boundary terms).

## 1. Theorem 1 (zero-mode Bogoliubov inequality). PROVED; CN (scripts/verify_Z.py, 3-site ring, 5 parameter sets, all identities to 6 digits)

**Statement.** At zero field, for all a ∈ ℝ, b > 0, N:

  Var(Y²) · [1 + χ m_H² + 12b(−∂_a m2)] ≥ 4 m2².   (1.1)

Equivalently, if |B| < 2,

  12b(−∂_a m2) ≥ 2|B|/(2 − |B|) − (χ m_H² − 1),   (1.2)

and χ m_H² − 1 = 4b Σ_x |u4(0,0,0,x)| ≥ 0. In continuum units:

  24λ(−∂_μ M_L²) ≥ 2|B_L|/(2 − |B_L|) − 4λ 𝒮_L,  𝒮_L := ε² Σ_x |u4(0,0,0,x)| = (χ_L m_H² − 1)/(4λ).   (1.3)

Also (same proof, with Φ2 in place of Y²):

  −∂_a⟨φ0²⟩ = Var(Φ2)/N ≥ 4χ² / (N[1 + χ m_H² + 12b(−∂_a m2)]).   (1.4)

**Proof.** Let T = Σ_x∂_xS = cM + 4bΦ3 and G0 = Y·T.
1. ⟨G0⟩ = ⟨Σ_x∂_xY⟩ = 1.
2. For any F: ⟨F G0⟩ = ⟨Σ_x∂_x(FY)⟩ = ⟨F⟩ + ⟨Y Σ_x∂_xF⟩, so Cov(F, G0) = ⟨Y Σ_x∂_xF⟩.
   F = Y²: Σ_x∂_xY² = 2Y, so Cov(Y², G0) = 2m2. F = Φ2: Σ_x∂_xΦ2 = 2NY, so Cov(Φ2, G0) = 2N m2.
3. ⟨G0²⟩ = ⟨Σ_x∂_x(Y G0)⟩ = ⟨G0⟩ + ⟨Y Σ_x∂_xG0⟩, and Σ_x∂_x(YT) = T + Y·H with
   H := Σ_{x,y}∂_x∂_yS = Σ_x(2a + 12bφ_x²) − 4N = Nc + 12bΦ2. Hence ⟨G0²⟩ = 1 + ⟨YT⟩ + ⟨Y²H⟩ = 2 + ⟨Y²H⟩ and
   Var(G0) = 1 + ⟨Y²H⟩ = 1 + Nc m2 + 12b(m2⟨Φ2⟩ + Cov(Y², Φ2)) = 1 + χ m_H² + 12b(−∂_a m2),
   using Cov(Y², Φ2) = −∂_a m2.
4. Cauchy–Schwarz: Var(Y²)Var(G0) ≥ Cov(Y², G0)² = 4m2². This is (1.1). (1.4) is Var(Φ2)Var(G0) ≥ 4N²m2².
5. Var(Y²) = m4 − m2² = (2 − |B|)m2² gives (1.2).
6. IBP with F = M: N = ⟨Σ_x∂_xM⟩ = ⟨M T⟩ = cNχ + 4bNχ3 with χ3 = Σ_x⟨φ0³φ_x⟩, i.e. 1 = cχ + 4bχ3.
   Since u4(0,0,0,x) = ⟨φ0³φ_x⟩ − 3⟨φ0²⟩⟨φ0φ_x⟩ ≤ 0 (Lebowitz [Leb74], valid for φ⁴ via [SG73]; CITED-NOT-READ, same use as the paper §7.4),
   χ m_H² − 1 = 4b(3⟨φ0²⟩χ − χ3) = 4b Σ_x|u4(0,0,0,x)|. ∎

**What it is.** (1.3) is (P0) with K = 24λ, plus an explicit additive "Hartree defect" 4λ𝒮_L. It is uniform in ε and L and has the exact first-order constant.
**What it is not.** It does not use one-component structure (only IBP, Cauchy–Schwarz; Lebowitz only to sign the defect), so by (O3) it cannot give (P0). Indeed:
- flip regime: Var(Y²) ≈ 4M²χ₊/N, and (1.1) becomes χ₊ ≥ 1/m_H² (pure-phase Bogoliubov bound); the term with −∂_a m2 is O(1/N) relative. Vacuous for (P0).
- infinite-volume symmetric phase: |B_L| = O(L⁻²) while the defect is O(1). Vacuous.
- it gives (P0) with K = 48λ exactly on the set {4λ𝒮_L ≤ |B_L|/2} (small tori / near-Gaussian).

## 2. Theorem 2 (one site). PROVED; CN (scripts/fd_1site.py, a/√b ∈ [−30, 100], mpmath 30 digits)

For the single-site law ∝ e^{−aφ²−bφ⁴}dφ, m_{2k} = ⟨φ^{2k}⟩:
(a) |κ4| = 3m2² − m4 ≤ 4b m4 (m4 − m2²).
(b) The Binder cumulant m4/m2² is nondecreasing in a (|B| nonincreasing).
(c) (finite-difference inequality) ⟨φ⁴⟩_a ≥ 3⟨φ²⟩_a · ⟨φ²⟩_{a + 4b⟨φ²⟩_a}.

**Proof.** (a) is Theorem 1 with N = 1 (then c = 2a, G0 = φV′, Var G0 = 2 + 8b m4, Cov(φ², G0) = 2m2).
(b) IBP gives (2k−1)m_{2k−2} = 2a m_{2k} + 4b m_{2k+2}; with k = 1, 2: m6 = (3m2² − m4 + 4b m4²)/(4b m2).
d/da (m4/m2²) = (2m4² − m6m2 − m4m2²)/m2³, and 2m4² − m6m2 − m4m2² ≥ 0 ⟺ 4b m4(m4 − m2²) ≥ 3m2² − m4, which is (a).
(c) Let ψ(u) = ⟨φ²⟩_{a+u}, β(u) = |B| at mass a + u, p = ψ(0), β0 = β(0). Then ψ′ = −Var(φ²) = −(2 − β)ψ², so
1/ψ(u1) = 1/p + ∫_0^{u1}(2 − β) ≥ 1/p + u1(2 − β0) by (b). With u1 = 4bp the claim ψ(u1) ≤ p(1 − β0/3) is
4bp²(2 − β0)(3 − β0) ≥ β0, which is (a) at mass a (divide (a) by p²: β0 ≤ 4b(3 − β0)p²(2 − β0)). ∎

(c) is the one-site case of the finite-difference inequality (FD_1) of §4. It holds although ψ is not convex
(κ3(φ²) < 0 for a ≤ −4√b; CN), so it is not a Jensen statement.

## 3. Theorem 3 (mass-accumulation chain). PROVED from the BFS representation [BFS82], [FFS92, ch. 9–11] (CITED: read only through the earlier team notes theta2/NOTES.md §3 and r2/D); CN on one site (scripts/verify.py, 10 digits)

Let dW_{xy} be the BFS walk measure (independent of a, b), Z(t) = ∫Π_x g(φ_x²/2 + t_x)dφ with g(s) = e^{−2as−4bs²}. Then
Z(t)/Z = e^{−Σ(2at_x+4bt_x²)} Z_{a+4bt}/Z_a, and expectation under Π g(s_x + t_x) is the model with site masses a + 4bt.
Let ŵ be the probability measure ∝ Σ_{x,y} dW_{xy}(ω) Z(t_ω)/Z on walks (total mass X). For arbitrary site masses a:

  ⟨M⁴⟩_a = 3 X(a) · E_ŵ[X(a + 4b t_ω)],  i.e.  1 − |B(a)|/3 = E_ŵ[X(a + 4bt)]/X(a),   (3.1)
  ⟨M^{2k}⟩/(2k−1)!! = E[X(a_0)X(a_1)···X(a_{k−1})],  a_{j+1} = a_j + 4b t_{ω_{j+1}}, ω_{j+1} ~ ŵ_{a_j},   (3.2)
  E_ŵ|t| ≤ χ (transitive case), so the mean per-site mass shift 4bE|t|/N is at most 4b m2.   (3.3)

Proof: (3.1)–(3.2) are the BFS pairing formula ⟨φ_{x1}…φ_{x2k}⟩ = Σ_pairings ∫ΠdW Z(Σt)/Z summed over all sites, with
Σ_{u,v}∫dW_{uv} Z(t+t′)/Z(t) = X(a + 4bt). (3.3): split the walk at a local-time point z and use Ginibre/GKS mass monotonicity
(⟨φ_zM⟩_{a+4bt} ≤ ⟨φ_zM⟩_a): X·E_ŵ|t| = Σ_z∫∫dW_{·z}dW_{z·}Z(t1+t2)/Z ≤ Σ_z χ_z² = Nχ². ∎
In words: the Binder cumulant is exactly the mean relative loss of susceptibility when the mass is raised by 4b × (local time of one two-point walk).
This is the zero-field version of the paper's Prop. 7.2(3); the content is BFS's, the formulation (3.1) is what §4 uses.

## 4. Theorem 4 (finite-difference form ⟹ integrated (P0)). PROVED (elementary)

Let f(a) = m2(a) = M_L²(a) > 0, nonincreasing (GKS), B(a) the Binder cumulant, κ > 0. Hypothesis:

  (FD_κ)  f(a + 4bκ f(a)) ≤ (1 − |B(a)|/3) f(a)  for all a ∈ [a₋, a₊].

Equivalently ⟨M⁴⟩_a ≥ 3⟨M²⟩_a⟨M²⟩_{a′}, a′ = a + 4bκ⟨M²⟩_a/N²; in the continuum, μ′ = μ + 8κλ M_L²(μ).
By (3.1), (FD_κ) ⟺ E_ŵ[X(a + 4bt)] ≥ X(a + 4bκ m2·1): a walk-shaped mass increase lowers X no more than the uniform increase of κ times its maximal mean.

**Conclusion.** f(a₋) ≥ (24κ b)⁻¹ ∫_{a₋}^{a₊} |B(a)| da; in continuum units M_L²(μ₋) ≥ (48κλ)⁻¹ ∫_{μ₋}^{μ₊} |B_L| dμ.
So (FD_κ), uniform in ε and L, gives the dichotomy of the paper's §7.4 with K = 48κλ, with no derivative and no convexity in the mass.

**Proof.** Fix a1 ∈ [a₋, a₊] and δ = 4bκ f(a1). For a ∈ [a1, a₊]: f(a) ≤ f(a1), so a + 4bκf(a) ≤ a + δ and
f(a + δ) ≤ f(a + 4bκf(a)) ≤ f(a) − |B(a)|f(a)/3. Integrate over [a1, a₊]:
(1/3)∫_{a1}^{a₊}|B|f ≤ ∫_{a1}^{a₊}f − ∫_{a1+δ}^{a₊+δ}f ≤ ∫_{a1}^{a1+δ}f ≤ δ f(a1) = 4bκ f(a1)².
So G(a1) := ∫_{a1}^{a₊}|B|f ≤ 12κb f(a1)² for every a1. Then −G′ = |B|f ≥ |B|(G/12κb)^{1/2}, i.e. −(√G)′ ≥ |B|/(2√(12κb)) where G > 0
(G is absolutely continuous, nonincreasing; where G = 0 we have B = 0 a.e. to the right). Integrating,
√G(a₋) ≥ (4·12κb)^{−1/2}∫_{a₋}^{a₊}|B|, and f(a₋) ≥ (G(a₋)/12κb)^{1/2} ≥ (24κb)⁻¹∫|B|. Continuum: da = ε²dμ/2, b = λε². ∎

**Status of the hypothesis.** (FD_κ) is OPEN on the lattice. PROVED for one site with κ = 1 (Theorem 2c).
CN with κ = 1: Curie–Weiss (N ≤ 16384, b from 1 to 0.005), rings N = 4, 16, 64 (72 cases), 2D tori L = 16, 32 by Monte Carlo
(b = 0.5, 0.1, 0.02; wherever |B| ≥ 0.1 the largest κ_min is 1.00 ± 0.11 (b = 0.02, L = 32, B = −0.125) and κ_min ≤ 0.7 for |B| ≥ 0.17 at L = 32; for |B| < 0.1 the test is noise-dominated and unresolved; mc2d/ANALYSIS.txt). κ = 1 is saturated at first order in b (it is then R″(0) ≤ 0, Lemma L at second order in h),
so κ = 2 is the safe conjecture. By (O3) it must fail for the 2D rotator; the one-component input has to enter exactly here.

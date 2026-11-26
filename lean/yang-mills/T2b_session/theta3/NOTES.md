# θ-3 notes: the integrated (Theorem 7.1) form of the θ-route, the two-phase picture, numerics

θ-3, 26 Nov 2026. Labels: PROVED (checked here), HEUR, NUM.
Aligned with θ-1's STATEMENT.md: Forms I–V, the Dini condition, and only h ≤ 3s₀/χ₀ being used. Their Form IV is the same reduction as §1 below. Everything in §1 is in lattice units: weight exp(JΣ_{⟨xy⟩}φ_xφ_y − Σ(aφ²+bφ⁴) + HΣφ), N sites, coordination 2d, and c := 2a − 2dJ (c = ε²μ_bare in T2b).
Scripts are in this directory: cw.py, t1–t4.py, ring1d.py.

## 1. Everything is one-dimensional: exact single-copy formulas (PROVED)

Notation:
- ν = the zero-field law of M = Σφ_x, with density p(v);
- y = M/N;
- I_N(y) := −N⁻¹ log p(Ny);
- S(v) = E₀[Σφ_x² | M=v] and σ = S/N;
- T3(v) = E₀[Σφ_x³ | M=v] and τ3 = T3/N.

**(1a) P₀ is a self-convolution.** P₀ = law of (M+M′)/√2 with M, M′ i.i.d. ~ ν, because E₀e^{hQ} = (E e^{HM})².
- In the coexistence/flip regime ν is bimodal (±NM₊), so P₀ is **trimodal**: mass ½ near 0 (copies in opposite phases) and ¼ near each of ±√2NM₊.
- Fable's "bimodal" should read trimodal. θ-1 §5(c) already uses this.
- NUM (CW): peaks of P₀ found at w = 0 and w ≈ 2M₊.

**(1b) Conditional equation of motion.** Shift all φ_x by s. The nearest-neighbour term changes by 2dJ·M·s, and p(v+Ns) differentiates to give
  c·y + 4b·τ3(y) = I_N′(y)   for every y.
- So the microcanonical cubic moment is the derivative of the finite-volume rate function.
- NUM: verified in CW (with 2dJ → J) to 6·10⁻⁴, which is the finite-difference error.

**(1c) Maxwell, microcanonically.** σ(y) = E₀φ₀² + ∂_a I_N(y), with I_N normalised as a probability density.

**(1d) R in one line.** By translation invariance ⟨φ₀³⟩ = ⟨τ3(Y)⟩_H, and by (1b) and integration by parts ⟨I_N′⟩_H = H. Hence
  R = (H/m − c)/(4b) − ⟨σ(Y)⟩_H,   ∂_H R = ∂_H(H/m)/(4b) − ∂_H⟨φ₀²⟩.
- This is identity (★) re-derived in two lines.
- **Lemma L in any θ-form is therefore a statement about the two-parameter family of one-dimensional laws ν_a, i.e. about the pressure p(a,H) alone.** It is a second-order differential inequality for an exponential-family log-partition function in the two linear parameters (H, a); θ-1's Form I/IV.

**(1e) Ψ and Ξ in single-copy terms.** Expand q t² = (φ³+φ′³−φ²φ′−φφ′²)/(2√2), and use E[φ′_x | M′] = M′/N (translation invariance and independence of the copies). Then
  2√2·uΨ(u) = E[ T3(M)+T3(M′) − (S(M)M′+S(M′)M)/N | (M+M′)/√2 = u ],
  2√2·uΞ(u) = E[ (S(M)−S(M′))(M−M′) | (M+M′)/√2 = u ]   (lattice units),
and, with w = y+y′ and J_N the rate function of w (the P₀ rate function),
  Ψ(w) = J_N′(w)/(4bw) − c/(8b) − E[σ(y)y′+σ(y′)y | w]/(2w).
- The middle step uses E[I_N′(y) | y+y′=w] = J_N′(w), by differentiating the convolution.
- The J_N′(w)/w term is typically **increasing** (convex J), so Ψ↓ is a cancellation against the σ-term. That is why it is delicate.

**(1f) Ξ ≥ 0 whenever σ is nondecreasing in |y|.** Given w > 0 and y > y′, we have |y| > |y′|, so every term (σ(y)−σ(y′))(y−y′) is ≥ 0.
- NUM: σ is monotone in all CW runs with N = 64. It fails at N = 16 for deep wells (a = −4, −6). At (a,b,J,N) = (−6,1,0.6,16), Ξ < 0 somewhere (min −0.22).

**Exact checks** (CW, t2.py). R = 2⟨Ψ⟩_{π} agrees to all printed digits (10⁻⁶). ∂_H⟨φ²⟩ = 2m⟨Ξ⟩_π agrees to 10⁻⁷.

## 2. What bound on Ψ suffices

From θ-1 Form V: ∂_hR = 2√2 Cov_π(Ψ, u coth ηu) and ∂_h⟨φ²⟩ = 2m E_πΞ.

**(b) One-sided growth bound** (θ-1, PROVED reduction): Ψ − A·u/L² nonincreasing. **(b′) The quadratic variant**, Ψ − A(u/L²)² nonincreasing, works the same way by Chebyshev.

HEUR scaling (corrects a first guess of mine). For a unimodal, Gaussian-like P₀ with width L√χ on {m ≤ s₀}, both (b) and (b′) leave the needed comparison (C_A) satisfied for θ ≤ 1:
- in the regime ηu ≫ 1, Cov_π(u, u coth ηu) ≈ L²χ;
- in the regime ηu ≪ 1, it is ≈ (η/3)Cov(u,u²).
In the flip regime θ-1's estimate holds; I re-derived it.

**The catch.** Any Ψ-growth condition only moves the problem into (C_A), and (C_A) needs a **lower bound on E_πΞ = (−∂_μm)/m**. All the sign tools give is −∂_μm ≥ 0 (GKS), and Ginibre gives only ≥ ½mR·ε² → 0. In the flip regime
  −∂_μm ≈ ½κ(tanh x + x sech²x) = O(1),   while 2mχ_L = O(L²).
So no bound of the form −∂_μm ≥ c·mχ can hold, since U3 ≈ −2mχ_L there. The needed lower bound is against a "local" susceptibility, and no such quantity is a priori defined.

**Sharpest remaining statement (Σ_θ)**, equivalent to Form I by (1d): on {m ≤ s₀}, h ≤ 3s₀/χ₀,
  N·Cov_{ν_H}(σ(Y), Y)  ≥  c₀ m^{−θ}·(m − Hχ)/(…units),   σ(y) = E₀[φ₀² | M = Ny] = const + ∂_a I_N(y).
In words: the microcanonical energy density must increase in |y| at least as fast, in the H-tilted law, as ν deviates from Gaussian, up to a factor m^{θ}. GKS gives only the sign of the left side. GHS gives only the sign of the right side.

**Lee–Yang zero form (PROVED algebra; not developed).** φ⁴ has order 4/3 < 2, so Z(H)/Z(0) = ∏_j(1 + H²/α_j²) with α_j > 0. Hence
  m − Hχ = N⁻¹Σ_j 4H³/(α_j²+H²)²,   −∂_a m = N⁻¹Σ_j 2H·∂_a(α_j²)/(α_j²+H²)².
- So Form I reads Σ_j w_j [2H² − F(m)·∂_a α_j²] ≤ 0, with w_j > 0.
- A termwise sufficient condition would be that the zeros move away from the real axis fast enough as the mass increases. I know no monotonicity theorem for φ⁴ Lee–Yang zeros in the mass, and the termwise version fails for zeros with α_j ≪ H.

## 3. Large-deviation / two-phase picture (HEUR; consistency only)

**(3a) LD level.** Ψ(w) ≈ R_mc(w/2)/2, with R_mc(y) := τ3(y)/y − σ(y) the microcanonical R. By (1b–c):
  R_mc decreasing ⟺ (I′/y)′ ≤ 4b·∂_a I′.
The θ-version is (I′/y)′ ≤ 4b(1+Km^{θ−2})∂_a I′. Off the plateau this is just the infinite-volume pure-phase inequality.

**(3b) Flip-regime mixture (HEUR, error O(e^{−2τ_sL}) + O(H²)).** Let x = NM₊H and τ = tanh x. Write the pure-phase responses as
- ⟨φ⟩₊ = M + χ₊H, ⟨φ²⟩₊ = s₂ + κH, ⟨φ³⟩₊ = s₃ + κ₃H,
- and c₊ := (κ₃M − s₃χ₊)/M², so that ∂_HR₊ = c₊ − κ.
Then:
- m = τM + χ₊H;
- ∂_H⟨φ²⟩ = κ(τx)′;
- ∂_HR = c₊(x/τ)′ − κ(τx)′.

Elementary fact (PROVED): 0 ≤ (x/τ)′ ≤ (τx)′, with ratio in [1/3, 1). This reduces to τ ≤ x(1+τ²).

Consequences:
- **Pure-phase L ⇒ flip-regime L.**
- Since (x/τ)′ ~ 2x/3 while m^{θ−2} ~ (Mx)^{θ−2} → ∞, the θ-version in the flip regime needs only **c₊ bounded**.
- The flip regime is benign; θ-1 §5(c) reaches the same conclusion via Ψ's step-down Ψ(0⁺) − Ψ(aligned) ≈ 2M₊². I re-derived that step-down from (1e) with a Gaussian pure phase. NUM (CW): Ψ(0) = 0.62 vs 0.127 at the aligned peak.

**(3c) Why this cannot be a proof (circular).** The lemma is used at μ ∈ [μ₀−Φ, μ₀] below μ_c, where we know only that χ_L → ∞. In a proof by contradiction it must hold in the hypothetical regime "χ_L → ∞ but M⁺ = 0". θ-1's equality example m = (he^{−μ})^{1/(1+C)} is exactly that regime.
- Equivalence of ensembles, Wulff and the mixture formula all presuppose pure phases with M₊ > 0, which is the conclusion.
- LD convexity of I gives only GHS-type signs.

**(3d) Interpretation.** Form I with exponent θ is a soft "β ≤ 1/θ" bound. Critical scaling m = |t|^β f(h/|t|^{βδ}) gives −∂_μm ~ m^{1−1/β}, so (H_θ) holds near a critical point iff θ ≤ 1/β.
- For φ⁴₂ (Ising class) 1/β = 8, so all θ ≤ 2 have room.
- At mean field it is equality at θ = 2.
- So the θ-route asks for a cutoff-uniform ABF-type exponent bound, weakened from β ≤ ½ to β ≤ 1/θ.

**(3e) ABF comparison (HEUR; constants to check against ABF 1987, J. Stat. Phys. 47).** ABF's inequality uses J∂_J. By rescaling φ, J∂_J = −a∂_a − 2b∂_b − ½H∂_H + ½ (on m). With a ≈ 2 this gives J∂_J m ≈ (4/ε²)(−∂_μm) + O(1).
- So, if it holds for lattice φ⁴ as stated, ABF gives Form I with F(m) ≈ (4/ε²)m² (+ m³), i.e. Lemma L with K ≈ 1/(2b) = 1/(2λε²).
- It is non-uniform by exactly ε⁻². The θ-route is "make ABF ε-uniform at the price of any power".
- The obstruction is that J∂_J weighs lattice-scale bond energy, which is not the renormalised-mass response.

## 4. Polchinski / multiscale (assessment)

- BD (arXiv:2202.02295): LSI for φ⁴₂ uniform in ε, under bounded susceptibility; the constant is controlled by χ.
- On the region Form I uses (h ≤ 3s₀/χ₀, so χ(μ,h) → χ₀ ≥ X as h ↓ 0), every Polchinski-derived constant degrades with X → ∞. The needed inequality is χ-scale-free, so it cannot come from the flow as is.
- The one conceivable entry point is the canonical (fixed-Q) measure. There d/du E[F | Q=u] = E_u[∂_uF] − Cov_u(F, N⁻¹Σ∂_qW) (round-8 decomposition), and a uniform Poincaré constant for the canonical measure would give the growth bound (b) by Cauchy–Schwarz.
- But on the plateau (phase-separated states) the canonical gap is exponentially small in L, and in the hypothetical no-coexistence regime nothing is known.
- BBD's Kawasaki result (arXiv:2310.04609) is on random regular graphs, not ℤ².

## 5. Numerics

**CW φ⁴ (exact finite-N, saddle-point contour inversion).** Runs at (a,b,J,N) ∈ {(1,1,5,16/64), (−4,1,0.5,16/64), (−4,1,0.2,64), (−2,1,1,64), (−4,1,1,16/64), (−6,1,0.6,16)}:
- Ψ is decreasing in all runs except (−6,1,0.6,16). That run has a multi-peaked P₀ (Ising-like parity), a +0.13 increase in Ψ, and Ξ < 0.
- R is decreasing in all runs (t4.py, exact H-derivatives, H ≥ 3·10⁻⁴).
- On m ≤ 0.5, max ∂_HR/∂_H⟨φ²⟩ ∈ [−0.80, −0.61]. That is strictly better than K = 0 and < 1 in modulus, consistent with θ-1's remark on θ > 2.
- Confirms that integrated monotonicity survives pointwise Ψ failure.

**1D rings (transfer operator, 401-point grid), the "large χ_L, no long-range order" toy.** Families (a,b,J) = (−3,0.5,1) with ξ = 366, (−1.5,0.25,1.5) with ξ = 2.5·10⁵, and (−2,0.1,1) with ξ = 3·10¹⁰; N/ξ ∈ {0.3, 1, 3, 10}; H from 10⁻²/χ₀ to 3, covering the flip and crossover regimes:
- max dlogR/dlogH ≤ −3·10⁻⁷ (first family) and ≤ −6·10⁻¹⁰ (second);
- third family: +1·10⁻¹⁰, at the eigenvalue-precision floor (λ₁/λ₀ = 1 − 3·10⁻¹¹), so unresolved.
- Lemma L (K = 0) holds across the whole crossover.

**Not done.** 2D tori in the T2b regime. This needs Monte Carlo, not exact methods.

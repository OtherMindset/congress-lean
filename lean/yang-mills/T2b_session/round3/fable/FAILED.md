# FAILED.md — dead lemmas and routes (Fable session, 26 Nov 2026)

Labels: PROVED / CN / HEUR.

F1. **Jensen for the walk-shaped mass shift.** "X(a+s) is convex in s, so E_ŵX(a+4bt) ≥ X(a+4bE t)."
 - False premise already on one site: κ3(φ²) = ∂_a²⟨φ²⟩ < 0 for a ≤ −4 (b = 1): −4.9·10⁻³ at a = −4, −1.0·10⁻² at a = −6 (CN, scripts/fd_1site.py). Agrees with (O5).
 - The conclusion (FD_1) nevertheless holds on one site (PROOF.md Thm 2), so convexity is not the mechanism.

F2. **(UNI_1): "among mass perturbations of given mean, the uniform one minimises ⟨M²⟩."**
 - True for the Gaussian field (PROVED) and in all 45 ring tests (CN, scripts/uni_test.py).
 - HEUR counter-argument in an ordered phase (Landau equation −Δm + (μ+s)m + 4λm³ = 0, second order in s): the zero-mode response is −Σ_k|ŝ_k|²(4λM² − k²)/(8λM(k² + 8λM²)²), negative for k² < 4λM². Long-wavelength modulations beat the uniform shift. Not checked numerically (needs a 2D ordered system).
 - So only (UNI_κ) with κ > 1 can hold, and κ ≳ 1/(2β) by local equilibrium: a "no plateau" statement again.

F3. **GKS domination of the walk shift by its sup norm.** X(a+4bt) ≥ X(a + 4b‖t‖_∞).
 - Loses the factor ‖t‖_∞/M_L² (not a volume factor), with ‖t‖_∞ ~ log²(1/ε) (HEUR). It would give only −∂_μ log M_L² ≳ |B_L|/(λ log²ε⁻¹), i.e. (P) with F ≡ const (θ = 0, non-Dini, the KT borderline), and not uniformly in ε. Also the tail of ‖t‖_∞ under ŵ cannot be bounded by a free walk: the free walk sum diverges for μ_b < 0.

F4. **Measure domination.** For s with mean s̄, the translation average P̄ of P_{a+s} satisfies P̄ ≥ r⁻¹P_{a+s̄}, r = Z(a+s)/Z(a+s̄) ≥ 1 (PROVED, Jensen twice). So X(a+s) ≥ X(a+s̄)/r.
 - Useless: log r ≈ (1/8)Σ s_xs_y⟨φ_x²;φ_y²⟩ is extensive in the walk duration (~λ²L²M²) (HEUR).
 - Refinement to the law of Y alone: p_s(y)/p_{s̄}(y) ∝ r(y) = E_{s̄}[e^{−½Σ(s−s̄)φ²} | Y = y] ≥ 1; (UNI_1) ⟸ r(y) nondecreasing in |y|. No proof; fails at tree level by F2.

F5. **Pointwise canonical conditions** (NOTES §1.3–1.4): "R_mc(y) nonincreasing", "I_N convex in y²", "Λ(p) ≥ |B(p)|/3 for the law p of Y".
 - Λ ≥ |B|/3 is not a consequence of Lee–Yang + Lebowitz: for the law of the sum of two independent smoothed ±2 bimodals (Lee–Yang holds, trimodal), Λ = −1.8, −5.4, −10.3 at widths 0.6, 0.4, 0.3 while |B| = 0.72, 0.86, 0.92 (CN, scripts/lam.py). Bimodal: Λ = 2.10 ≥ |B|/3 = 0.64.
 - So these can hold only in a "connected" regime; no tool proves them (they are canonical-ensemble relatives of the paper's Ψ-monotonicity, which fails for deep wells).
 - In the Curie–Weiss case R_mc reduces, by pairing sites, to a signed size-biased average of the one-site g(q); monotonicity would need total positivity of the reflection kernel ρ(Ny − √2q) − ρ(Ny + √2q) for the (N−2)-fold convolution ρ. Not proved.

F6. **Bogoliubov/Cauchy–Schwarz test functions built from the zero mode** (PROOF.md Thm 1).
 - Proved inequality, but saturated in the flip regime (it reduces to χ₊ ≥ 1/m_H²) and vacuous in infinite volume. The defect χ_Lm_H² − 1 = 4λε²Σ|u4(0,0,0,x)| is O(L²) in the flip regime.
 - The dilation test function Σ_xφ_x∂_xS gives χ₂ ≥ 2⟨φ²⟩²/(1 + 4b⟨φ⁴⟩) (PROVED), which is UV-dominated: O(ε² log²ε⁻¹) in continuum units.

F7. **Infrared bound route.** ⟨φ0²⟩ ≤ M_L² + (massless lattice Green function without zero mode) (Fröhlich–Simon–Spencer; CNR). In 2D the last term is (2π)⁻¹log(L/ε): after Wick ordering a log L remains. Combined with the proved mean-field lower bound on the energy response (Thm 1, (1.4)) it still gives nothing. Consistent with (O3).

F8. **EOM + GHS.** h ≤ μ_b m + 4λm³ + 12λm⟨φ0;φ0⟩ (GHS, u3 ≤ 0) gives M₊² ≥ (−μ − 12λ⟨:φ²:⟩_T)/(4λ) (PROVED given GHS). Vacuous near μ_c, where μ + 12λ⟨:φ²:⟩ ≥ 1/χ > 0 on the symmetric side. Mean-field bounds of Hartree type cannot be sharp in 2D.

F9. **Self-consistent form as a theorem.** m2(a + 4bτ) ≤ τ held in every exact test, but on one site the natural sufficient condition (ψ equal to its convex envelope at the fixed point) fails for a < −12√b (HEUR from the sign of κ3). Not proved even on one site; only (FD_1) is.

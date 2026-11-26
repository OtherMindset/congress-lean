# LY1 (one-variable Lee–Yang case): DISPROVED. Refined conjecture LY1' stated.

Scripts: ly1.py, ly1c.py–ly1i.py, lytest*.py (this directory).

## 1. Counterexample (exact)
Take dν = x² e^{−x²/2} dx / √(2π). It is even, positive, and has finite moments of all orders.
- Its Laplace transform is Z(H) = e^{H²/2}(1 + H²), whose only zeros are ±i. So ν is in the Lee–Yang class.
- Tilting gives dν_H ∝ Y² dN(H,1)(Y), hence ⟨x^n⟩_H = E[Y^{n+2}]/E[Y²] with Y ~ N(H,1).
- The needed Gaussian moments are E[Y²] = 1+s, E[Y³] = H(s+3), E[Y⁴] = s²+6s+3 and E[Y⁵] = H(s²+10s+15), where s = H².

Therefore

  R = ⟨x³⟩/⟨x⟩ − ⟨x²⟩ = (s²+10s+15)/(s+3) − (s²+6s+3)/(s+1) = 2 − 6/(s+3) + 2/(s+1).

- dR/ds = 6/(s+3)² − 2/(s+1)², which is > 0 ⟺ √3(s+1) > s+3 ⟺ s > √3.
- **So R strictly increases for H > 3^{1/4} ≈ 1.316.** R(0) = R(∞) = 2, and the minimum is at H² = √3.
- Cross-check: R(0) = 2κ2(0) + κ4(0)/κ2(0) = 6 − 4 = 2.

The counterexample does not depend on the density vanishing at x = 0. Z = e^{βH²}(1 + H²/a²) is a positive measure iff 2βa² ≥ 1; its density is Gaussian × (1 − 1/(2βa²) + x²/(4β²a²)). Every tested β ≥ 1/2 (a = 1) violates monotonicity near H ≈ 3:
- (2+x²)e^{−x²/4}, i.e. β = 1: max of T = 2m²χ' + mχ'' − χχ' is ≈ 6.0 > 0.
- A 3-zero example with a ≈ (0.66, 0.85, 1.51), β = 1.336: its positivity was checked at 30 digits, and R(H) was computed directly from the density by quadrature, with Z reproduced to 10 digits. R increases from 3.89 at H = 2 to 4.74 at H = 4.

## 2. Why the 0-d proof does not apply here
- ν is not GHS. Here m = H + 2H/(1+H²), so m'' = 4H(H²−3)/(1+H²)³ > 0 for H > √3.
- In the duplication proof, g(q) = E[t²|q] = (u²−6u+15)/(u²−2u+3) with u = q². Its derivative has the sign of u² − 6u + 3, so g increases on (0, 3−√6) and on (3+√6, ∞). Step 2 therefore fails.
- More generally, every Hadamard product with finitely many zeros (times e^{βH²}) has κ3 > 0 for large H: each zero contributes H v²(16y − 12) with y = H²/(a²+H²) → 1. So all of them violate GHS at large H.
- Zero location alone therefore cannot decide the sign. A "sum over zeros" proof would need extra input that excludes these finite-zero products.

## 3. The right hypothesis (evidence)

| family | LY | GHS (κ3 ≤ 0 on H > 0) | R nonincreasing |
|---|---|---|---|
| x²e^{−x²/2}, e^{βH²}(1+H²/a²) | yes | no | **no** |
| δ_{±3} + cδ_{±1}, c ≤ 3 | yes | yes | yes |
| same, 4 ≤ c ≤ 9 | no | yes | yes |
| same, c = 10, 15 | no | yes | **no** |
| same, c = 30 | no | no | no |
| sums of independent ±a_j plus Gaussian (6·10⁴ random) | yes | yes | yes |
| random trigonometric LY measures ∏(cosh 2H − cos θ_j) (7·10³) | yes | (mixed) | yes |
| random convolution products of the above blocks (2·10⁴) | yes | | no genuine GHS+violation case |

Notes on the table:
- In the last row, the apparent GHS+violation cases all contained a finite-zero block whose GHS failure lies beyond the H-grid. I verified this at 60 digits.
- In the δ_{±3} + cδ_{±1} family, GHS was checked only on H ∈ (0,5]. c = 30 was the only value found to violate it on that range.
- Neither LY alone nor GHS alone suffices.

**Conjecture LY1'.** If ν is even and Lee–Yang, and m(H) is concave on H > 0, then R is nonincreasing on H > 0. This is OPEN and not sharp: c = 4..9 satisfy the conclusion without LY.

**PROVED (zerod_proof.md).** If ν = e^{−V} with V even and V' convex on [0,∞) (EMN), R is nonincreasing; LY is not needed.

Comparison of the two conditions:
- The EMN condition is equivalent to the MLR property used in the proof.
- A weaker sufficient condition for the conclusion is "g(q) = E[t²|q] nonincreasing on q ≥ 0" for the duplicated pair.

## 4. Consequences for the block case IC
- **Lee–Yang alone cannot prove IC.** IC with B = Λ and c ≡ 1 is exactly the one-variable problem for the law of M, so any proof must use GHS-type input as well. The law of M for Ising is LY (Lee–Yang) and GHS (Ellis–Monroe–Newman), so LY1' would imply IC for B = Λ.
- **For B ≠ Λ, IC is genuinely two-variable.** Let F(u,v) = log Z(u on B, v on B^c). Then R_B = 2F_uu + F_uuu/F_u, evaluated at (H,H) and differentiated along the diagonal.
  - Multivariate Lee–Yang holds for F, but by §1 it is not enough, even in one variable.
  - Conditioning on σ_{B^c} produces non-uniform fields on B. By lattice.md §2, non-ray field configurations break the statement, so conditioning is not a viable reduction.
- **Recommendation.** Stop pursuing Lee–Yang routes. The working mechanism is the EMN/duplication structure: monotone g, i.e. MLR of the t-law in |q|. The lattice task is to show that π_H (lattice.md §5/§3c) is stochastically increasing in H along rays, using GHS-type (not LY) input. A natural target is a multi-site analogue of "q·sinh(hq) has increasing likelihood ratio", for example via the GS/Curie–Weiss block, where block-level EMN holds.

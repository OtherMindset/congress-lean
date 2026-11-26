# Inequality (A), the covariance Cov_{π_h}(t_0², Φ), and the final status of the lift (lift seat)

Scripts in /home/claude/t2b/lift: A_test.py, A_vs_R.py, lhopital.py.

## 1. (A) is false (independent confirmation of the Sonnet result)
A_test.py: q-system with weight exp(ΣJ q_xq_y + hΣq − Σ(A_x q_x² + (b/2)q_x⁴)), A_x = a + 3b t_x², 3 sites, 300 random instances.
- Worst instance: star with centre 0, J₀₁ = 0.46, J₀₂ = 0.42, homogeneous A = 1.057, b = 0.052, h = 0.0201, pair (x,y) = (1,2) (the two leaves).
- There ⟨q₀q₁²q₂²⟩⟨q₀⟩ < ⟨q₀q₁²⟩⟨q₀q₂²⟩, with relative margin 1.7%. The Sonnet run found 3.2% on the path 1–0–2.
- Failures sit at small h with x, y leaves of 0. So MTP2 of π_h fails, and the FKG closure of route 4 is dead.

## 2. The lemma still holds where (A) fails (A_vs_R.py)
I computed R(H) for the original φ⁴ system on the same graphs, over H₀·{1/4, …, 128}:
- my instance (a ≡ 1.057, b = 0.052, H₀ = 0.0201/√2): R decreases, 0.815775 → 0.672472;
- Sonnet instance, with the q-masses used as φ-masses (an inhomogeneous a, still a valid φ⁴ ferromagnet): R decreases, 0.470480 → 0.364171.

Cov_{π_h}(t_0², Φ) = ∂_h(R/2) is an exact identity, so the covariance is ≤ 0 at both points, as it must be. This also covers the base φ-parameters at t = 0.

## 3. Proof of the single covariance sign: none found. Why the reduction is now vacuous
Cov_{π_h}(t_0², Φ) ≤ 0 is the lemma itself, rewritten after conditioning on t. Every structural sufficient condition tried so far for it is FALSE:
- MTP2 of π_h, i.e. (A): FALSE (§1);
- Φ decreasing in each |t_y|, i.e. (B): fails rarely (Sonnet);
- the pointwise Ψ-lemma: FALSE for deep wells (0-d seat);
- the image-kernel TP2 property: FALSE for flat-bottomed s;
- coordinatewise field monotonicity of R and of P₄: FALSE (SWITCHING.md §5.1);
- the termwise and site-resolved decompositions D_z: FALSE (AUDIT_AND_LIFT.md B1);
- **new: the monotone L'Hôpital rule.** R = N/m with N = ⟨φ₀;φ₀²⟩ and N(0) = m(0) = 0, so R↓ would follow from N′/m′ ↓. It fails in 0-d for every quartic tested, double-well or single-well (lhopital.py: increases up to 5%, while R itself decreases). It also fails on 2-site rings. So "integrate a coordinatewise inequality from H = 0 along the ray" cannot work either.

Ideas considered for proving the covariance directly, none closed:
- (i) Duplicating the t-system. It reproduces the GHS-type rotation, but the field acts only through N(t,h), which is not of product form.
- (ii) Using that t_0² and Φ depend on the same local data at 0. Φ = ⟨q₀Q⟩_t/⟨q₀⟩_t is a global functional of t, and the y = 0 part alone controls only the |t₀|-dependence.
- (iii) Random currents with sources {0, g}. This is equivalent to the Ising inequality IC, with the same quantitative obstruction for large Griffiths–Simon blocks (SWITCHING.md §6).

## 4. Final status of the lift (my assessment)

**Out of reach with current tools.** The lemma is numerically robust: it held in every test across all seats, on tori and non-translation-invariant graphs with a uniform field, for φ⁴ and Ising blocks. It is proved in 0-d for the whole EMN class. The obstruction to a lattice proof is structural:

1. **Field homogeneity is essential** (the target fails for a non-ray field, and coordinatewise variants fail). Every classical correlation inequality (GKS, FKG/Holley, GHS, Lebowitz, EMN) holds for arbitrary nonnegative field profiles. A proof must use the Euler operator H∂_H, i.e. the total ghost-edge count, at the point of evaluation.
2. **Integrating from H = 0 does not help** (the L'Hôpital failure, §3). So Euler structure cannot be manufactured from coordinatewise derivative inequalities in the standard way, the way GHS gives m/h↓.
3. **Every factorised sufficient condition is false**: MTP2, pointwise Ψ, pointwise Holley, termwise random-current comparisons. The inequality is a genuinely global cancellation. Its Gaussian equality case (tangling = Wick) makes the margin O(λ²).
4. **Convexity tools are unavailable** in the T2b regime: a < 2, the action is nonconvex, and on the ordered side the effective potential is double-welled at all scales (CONVEX.md). The on-site lemma does not commute with renormalisation.
5. **Perturbation theory cannot reach μ_c** (lead's point 3). Weak coupling gives the lemma only away from the transition.

What a proof would need: a new non-pointwise comparison principle that exploits homogeneity. The best concrete form is SWITCHING.md §6: in the Griffiths–Simon limit, κ(δ − 3) is nonincreasing, where κ = nρ₂ and P₄ = 1 − δ/n. It could come from a coupling of the ghost-edge counts of the 4-source and 0-source double currents. The single open step for the |B| = 3 case is the bulk covariance in SWITCHING.md §5.3.

## 5. Status of the T2b chain
T2b is proved conditional on exactly one statement: the torus lemma, uniform in ε, needed only for h ≥ h_min(L) → 0 and μ in compact windows. The other inputs, with the μ_c^♯ restatement, are listed in AUDIT_AND_LIFT.md A6. Recommendation: present T2b as a conditional theorem, together with the lemma's evidence (the 0-d proof, all-seat numerics, the first-order saturation C = 8) and the obstruction list above.

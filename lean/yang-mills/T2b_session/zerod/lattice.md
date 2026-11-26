# T2b lattice: R_0(H) = ⟨φ_0;φ_0²⟩/⟨φ_0⟩ nonincreasing. STATUS: partial (reductions plus structural obstruction; no proof)

Scripts are in this directory. Nothing here is proved unless marked PROVED.

## 0. Target in cumulant form (PROVED, algebra)
Leonov–Shiryaev gives κ(φ_0,φ_0²,φ_x) = u4(000x) + 2G(00)G(0x) + 2m·u3(00x). The Gaussian part cancels against χ⟨φ_0;φ_0²⟩ = χ(u3(000) + 2mG00). So

  ∂_H R ≤ 0  ⟺  m Σ_x u4(000x) + 2m² Σ_x u3(00x) ≤ χ u3(000)   (T)

Equivalent forms:
- ∂_H R = 2∂_H G00 + ∂_H(u3(000)/m).
- In derivative language, ∂_{a_0}∂_H log m_0 ≥ 0. That is, Hχ/m (∈ (0,1] by GHS) increases with the local mass a_0.
- Ising analogue: m_{J'}(H)/m_J(H) is nonincreasing in H for J' ≥ J.

## 1. Route (3): the weak bound ∂_H R ≤ K∂_H⟨φ_0²⟩ does NOT follow from sign inequalities
- In (T) the terms −χu3(000)/m² ≥ 0 are bad (GHS gives u3 ≤ 0). They are of order χ/m · O(λ), which blows up like 1/H as H↓0 in the one-phase region.
- Meanwhile ∂_H⟨φ_0²⟩ = 2mχ + ∂_H G00 → 0.
- So a K-bound needs the cancellation against mΣ_x u4(000x), whose sign is not controlled for H ≠ 0. GHS, Lebowitz (H = 0 only) and GKS give nothing ε-uniform.
- Conclusion: K > 0 is no easier than K = 0 by these tools.

## 2. KEY STRUCTURAL FINDING: field homogeneity is essential (numerically certain)
Setup: 2-site φ⁴, phi4_2site.py, 601² and 1201² grids, which agree to 1e-13.

| field configuration | result |
|---|---|
| uniform H (14 tested points) | holds, worst rel dR/R = −5.8e-4 |
| base field h_1 = 0.5 on the neighbour, h_0 = 0, plus uniform H | **violated**: a = −2, b = 1, J = 3, H = 0.01 gives (dR/dH)/R = +0.264 (R = 0.187) |
| base field larger at 0 (h_0 > h_1) | holds in tests |
| ray h = H(1, c_1), c_1 ∈ {0, 0.2, 0.5, 2, 5, 20} | holds, worst −5.2e-4 (phi4_ray.py) |

So the true statement concerns **rays from the spin-flip-symmetric point**: h = H·c with c ≥ 0 fixed.

Consequences (rigorous logic given the numerics):
- **Route (1) cannot work as a GKS-I/Lebowitz-rotation argument.** Lebowitz/EMN four-copy rotation inequalities hold for arbitrary site-dependent fields h_x ≥ 0 at the evaluation point. Expanding the four-copy polynomial for (T) in rotated monomials with a definite sign would therefore prove the base-field version, which is false.
- **Pointwise FKG/Holley arguments cannot work for the same reason.** In the r-representation of zerod_proof.md §3, the conditional Ising fields √2H·r_x are inhomogeneous. This is exactly why lemmas (L1) and (L2) fail.
- **Any proof must use the ray/homogeneity structure.** The natural form is the Euler operator H∂_H = Σ_x h_x∂_{h_x}, i.e. ghost-edge counting in random currents (§4).

## 3. Route (4): Griffiths–Simon reduction to an Ising inequality
Write φ_x = α_N Σ_{i∈B_x} σ_i, with pair-coupled Curie–Weiss blocks (Simon–Griffiths 1973; AD-C 2021 §2). The field H φ_x = Hα_N Σσ_i is uniform on block spins. Then R_0 = α_N² · S_B with

  S_B(H) := ⟨M_B;M_B²⟩/⟨M_B⟩,  M_B = Σ_{i∈B}σ_i,  B = B_0.

Monotone functions converge to monotone functions, so

- **(IC)** For every finite ferromagnetic Ising model, every B, and field h = H·c with c ≥ 0 and c ≡ 1 on B, H ↦ S_B is nonincreasing on (0,∞)

would imply the φ⁴ lattice target for every a ∈ ℝ, b > 0, J ≥ 0, in every dimension and at every ε.
- [flag] This needs the standard convergence of field-dependent moments of φ_0 under the GS limit. Exponential moment bounds are uniform in N (Ellis–Newman, Simon–Griffiths). I believe this is standard but have not written it out.

Numerical status of IC, by exact enumeration of n ≤ 12 spins (isingBig*.py, isingRay*.py, isingP.py):

| case | trials | result |
|---|---|---|
| uniform c ≡ 1, random graphs and couplings, random B | ~8·10⁵ | holds, worst rel derivative ≈ −2H |
| c ≡ 1 on B, arbitrary c ≥ 0 elsewhere | ~10⁶ | holds |
| c non-constant on B | — | **fails** (+0.31) |
| base field plus uniform H | — | **fails** (+1.07) |

Termwise or local versions all FAIL, even with uniform field:
- ⟨σ_k;σ_iσ_j⟩/⟨σ_l⟩ (E2): +3.1.
- The same with l = k (E1): +0.48.
- ⟨M_B;σ_iσ_j⟩/⟨M_B⟩ (E3): +2.8.
- The pointwise-in-x version m·κ(σ_k,σ_iσ_j,σ_x) ≤ ⟨σ_l;σ_x⟩⟨σ_k;σ_iσ_j⟩ (P): +50.
- ⟨σ_k;M_B²⟩/⟨σ_k⟩ (E4): ≈ +0.008, borderline and not resolved.

Only the B-symmetric combination M_B, M_B² is monotone. So a proof must treat the block as a whole, as the 0-d proof does.

One-variable special case (B = Λ, c ≡ 1): S is a functional of the law of M, which is an even Lee–Yang measure.
- lytest2.py: about 7000 random positive LY measures Z = ∏_j(cosh 2H − cos θ_j), up to 6 factors. No violation.
- lytest.py: for the 4-point measures δ_{±3} + cδ_{±1}, LY holds iff c ≤ 3. Monotonicity holds up to c ≈ 5 and fails at c = 10 and c = 30.
- Conjecture LY1: R is nonincreasing for every even Lee–Yang measure on ℝ. This is open. It would extend the 0-d theorem beyond the GHS class, but it does not by itself give the lattice target.

## 4. Route (2): random-current form (PROVED identities; inequality OPEN)
Use a ghost g with edge weights H·c_x. By the switching lemma, with A = {k,g}Δ{i,j},

  ⟨σ_k;σ_iσ_j⟩ = ⟨σ_A⟩ · P^{A,∅}[k ↮ g].

This holds both for k ∉ {i,j} and for k = i (A = {g,j}).
- Check for k ∉ {i,j}: the clusters of n1+n2 pair the four sources. Then ⟨σ_A⟩ − ⟨σ_kσ_g⟩⟨σ_iσ_j⟩ = ⟨σ_A⟩(P[ki|gj] + P[kj|gi]).

Define:
- 𝒩 = Σ_{k,i≠j∈B} Z^{A}Z^{∅}·1[k↮g], a sum over double currents (n1,n2) with ∂n1 = A and ∂n2 = ∅.
- 𝒟 = Σ_{l∈B} Z^{lg}Z^{∅}.

Every double-current weight is proportional to H^{K}, where K = number of ghost-edge traversals in n1+n2. So H∂_H log(·) = ⟨K⟩, and

  **IC ⟺ ⟨K⟩_𝒩 ≤ ⟨K⟩_𝒟**.

Here ⟨·⟩_𝒩 and ⟨·⟩_𝒟 are the probability measures on double currents proportional to the summands.
- This identity is the precise reason the ray structure is needed: only along rays is H∂_H the ghost-counting operator.
- Heuristic: in 𝒩 the cluster of g must avoid k, and the k-cluster has zero ghost degree. That suggests fewer ghost edges.
- A proof needs a coupling or switching that maps 𝒩-configurations to 𝒟-configurations without increasing K, summed over the B-symmetric source sets. I did not find one. Note that the termwise version (fixed k, i, j, l) is false, so the map must mix source labels within B.

## 5. Route (1) remainder: second duplication over the signs
Duplicating the Ising model exactly (q = σ+σ', t = σ−σ', with q_x t_x = 0) gives π_H over the q-active set A:
- π_H(A) ∝ Z_A(2J, 2Hc)·Z_{A^c}(2J, 0)·⟨Q_B⟩_A.
- R/2 is then E_π[G(A)], where G(A) = 4⟨(Σ_{B∖A}τ)²⟩_{A^c} is decreasing in A (GKS II).

This is the exact discrete analogue of the 0-d proof. What is needed is that π_H is stochastically increasing in H on subsets. Holley fails (the analogue of L1/L2). By §2, any proof of this domination must use homogeneity, so it is again a Lee–Yang/ray-type statement, not FKG.

## 6. Recommended next steps
1. Try to prove LY1 (the one-variable Lee–Yang case): Hadamard product plus a zero-wise inequality. This is the simplest instance in which homogeneity is the only structure.
2. In the current picture, look for a "ghost-edge monotone" switching between source sets {k,i,j,g} and {l,g}, summed over k,i,j,l ∈ B.
3. Alternatively, abandon the same-site R. The ABF assembly could instead use a quantity that is monotone by a local inequality, e.g. −∂_μ m with GHS. This means revisiting (★) with the field-homogeneous structure in mind.

## 7. NEW (round 3): the field is eliminated exactly on the torus — reduction to a zero-field statement (PROVED)
Setting: finite torus Λ, |Λ| = N.
- Assumptions: couplings are translation-invariant; the single-site weight is even. Ferromagnetism and GHS are **not** used in this step.
- The field is uniform; the duplicated field is h = √2H, coupled to Q = Σ_x q_x = (M+M')/√2.
- μ_0 denotes the duplicated measure at zero field.

**Theorem 7.1.** Define A(u) := E_0[Σ_x q_x t_x² | Q = u]. It is odd in u. Set Ψ(u) := A(u)/u for u > 0. Then

  R(H)/2 = ∫_{(0,∞)} Ψ(u) · u sinh(hu) P_0(Q∈du) / ∫_{(0,∞)} u sinh(hu) P_0(Q∈du).

Consequently, **if Ψ is nonincreasing on (0,∞), then R is nonincreasing on H > 0.**

*Proof.*
1. Write E_h[q_0t_0²] = E_0[q_0t_0² e^{hQ}]/Z.
2. μ_0 is invariant under q ↦ −q (all sites at once, t fixed), because W is even in q and the q-coupling is quadratic. So e^{hQ} can be replaced by sinh(hQ).
3. Translation invariance gives E_0[q_0t_0² sinh hQ] = N⁻¹E_0[Σ_x q_xt_x² sinh hQ] = N⁻¹E_0[A(Q) sinh hQ].
4. In the same way, E_0[q_0 sinh hQ] = N⁻¹E_0[Q sinh hQ].
5. Both integrands are even in Q. Restricting to Q > 0 gives the formula.
6. The kernel u·sinh(hu) has a likelihood ratio sinh(h₂u)/sinh(h₁u) that increases in u (zerod_proof.md §2, Step 4). So the probability measures u sinh(hu)P_0(du) increase stochastically in h, and a nonincreasing Ψ has nonincreasing average. ∎

Remarks:
- N = 1 is exactly the 0-d proof, with Ψ = g.
- **Uniformity of the field is used exactly once.** It makes Q the variable conjugate to h. This is consistent with lattice.md §2, where non-ray fields break the statement.
- Gaussian check: q and t are independent, so A(u) = uσ_t² and Ψ is constant. This is the equality case.
- By the tower property, A(u) = E_0[Σ_x q_x G_x(|q|) | Q=u], with G_x = E[t_x²|q] coordinatewise nonincreasing in |q| (§3b, proved).
- On a non-symmetric graph, the same argument needs D(u) = E_0[q_0|Q=u] ≥ 0 and A_0/D nonincreasing, with A_0(u) = E_0[q_0t_0²|Q=u].

**Numerics** (psiQphi4.py; 2-site φ⁴ torus, b = 1, a ∈ {±0.5, ±1.5}, J ∈ {0.2, 0.7, 1.5}; 3-d grid 90³ on [−4.5, 4.5]; u ∈ (0.1, 5]):
- Ψ is strictly decreasing in all 12 cases. The largest relative increment is −0.0028.

Caveat (psiQ.py): for small Ising Curie–Weiss blocks (N_block = 2), Ψ is **not** monotone. Example values are 2.21, 0.57, 1.33, 0; this is a lattice-parity effect. IC still holds there: the kernel is variation-diminishing, so monotone Ψ is sufficient, not necessary. The GS route therefore cannot use Ψ for finite blocks. Only the continuum φ⁴ (or N_block → ∞) case is expected to have monotone Ψ.

**Remaining lemma (OPEN; this is now the exact sticking point).** For lattice φ⁴ (or the EMN class) on a torus at **zero field**:
  u ↦ E_0[Σ_x q_x t_x² | Σ_x q_x = u]/u is nonincreasing on (0,∞).
- In original variables: E_0[Σ_x(φ_x+φ'_x)(φ_x−φ'_x)² | M+M' = v]/v is nonincreasing.
- This is an Efron-type statement, "conditioned on the sum, things move up". The sum is weighted, since Σ_x q_xG_x/Q is a signed average of the G_x.
- Efron's theorem (independent log-concave summands) does not apply directly: the q's are dependent and, for a < 0, not log-concave.
- For N = 1 it is exactly the EMN MLR step.

**Route (2) check (qmarg.py).** Is the 0-d q-marginal weight ρ(q) = ∫e^{−W(q,t)}dt in the EMN class? Test: quartic, b = 1, V_q'' on [0,4].
- **Not** in general: V_q'' fails to be nondecreasing for a ∈ {−3, −1, 0, 1}, with drops down to −0.23 at a = −3. It is fine at a = 3.
- So GHS for the q-system cannot be obtained from the EMN class directly, and Theorem 7.1 sidesteps it.

## 8. Round 4: the pointwise Ψ-lemma is FALSE in general; where it can still hold
**(a) Product case J = 0 is a counterexample** (psiJ0.py, psiJ0b.py, psiQphi4b.py).
- Setting: b = 1, N = 2 or 3 i.i.d. EMN pairs. Here Ψ(u) = N·E[q_1 g(q_1) | Σq = u]/u, with g = E[t²|q].
- a = −4, N = 2, u = 0.5, 1, …, 4: Ψ = 1.98, 0.288, **−0.254**, 0.142, **0.469**, 0.304, 0.103, 0.063.
  - This is grid-converged: identical on a 1401×2801 and a 2801×5601 grid, and confirmed by the independent 3-d grid of psiQphi4b.py.
- a = −2: also non-monotone (relative increase +0.012 to +0.03). a ≥ −1: monotone.
- Yet R itself is monotone at J = 0: the sites decouple, so R is the 0-d R, and the theorem applies.
- **Hence Theorem 7.1's criterion is strictly weaker than the target. No Efron-type theorem can give Ψ↓ for the whole EMN class.** Ψ can even be negative: with deep wells, q_x ≈ ±2 or 0, and Q-conditioning mixes "q-active" and "t-active" sites.

**(b) Coupling restores monotonicity.** Maximum relative increase of Ψ:

| a | J | max rel increase |
|---|---|---|
| −4 | 0 | +0.052 |
| −4 | 0.2 | +0.038 |
| −4 | 1 | +0.019 |
| −4 | 3 | −0.004 (monotone) |
| −2 | 0 | +0.033 |
| −2 | 0.5 | +0.0025 |
| 2 | 1 | −0.007 (monotone) |
| 2.05 | 1.9 | −0.009 (monotone) |

So Ψ↓ fails exactly in the deep-double-well / weak-coupling regime.

**(c) The T2b regime is on the good side.** In φ⁴₂ on εℤ², a = 2 + ½ε²μ_bare, b = λε², J = 1, with coordination 4.
- The quadratic part is ½Σ(∇φ)² + (a−2)Σφ². The single-site potential is single-well, and b → 0.
- So the lemma needed for the application is: **Ψ↓ for single-well, near-Gaussian site weights with strong (Laplacian) coupling.**
- A first-order perturbative check gives ∂_H R = 2Σ_z u3(00z) + ∂_H(u3(000)/m) = −48λ m χ Σ_w G(0w)² + O(λ²) < 0.
  - Tree level is u3(xyz) ≈ −24λ m Σ_w G(xw)G(yw)G(zw). Then u3(000)/m = −24λΣG(0w)³ + O(λ²) has H-derivative O(λ²).
  - ΣG² is ε-uniform in d = 2. This is perturbative, not a proof. [flag: 24 = 4!; this combinatorial factor was not re-derived carefully.]

**(d) The "integrated ordering" is no easier as a general principle.**
- The kernel K(h,u) = u·sinh(hu) = Σ_k u(hu)^{2k+1}/(2k+1)! is totally positive.
- By Karlin's variation-diminishing property, S⁻(R/2 − c) ≤ S⁻(Ψ − c) for every c.
- Requiring "≤ 1 sign change, from + to −, for every c" is equivalent to Ψ monotone. So the dip-then-rise of (a) makes the criterion fail; it does not imply that R fails.
- Any integrated argument must use the specific weight u·P_0(du), e.g. the smallness of the small-u bump against u². I have none.

**Hypotheses used or needed.**
- Theorem 7.1 uses only: even site weight, translation invariance, uniform field.
- Ψ↓ needs, numerically, something like single-well behaviour (a/√b ≳ −1 at J = 0) or strong coupling. The EMN class is not enough (EMN allows a < 0 double wells).
- Finite Ising GS blocks fail by parity; any proof must use continuity.
- Candidate hypothesis for a provable lemma: log-concave site weight (a ≥ 0), where Efron/Prékopa tools exist. **This misses** the slightly negative a − 2 + (Wick) region only if a < 0, which is irrelevant here because a ≈ 2 > 0. So **a ≥ 0 (log-concave e^{−V}) plus arbitrary J ≥ 0 would suffice for T2b.**

## 9. Round 5: log-concave case
**(a) WARNING: the full action is NOT convex in the T2b regime.**
- Since Σ_bφ_xφ_y = 2Σφ² − ½Σ_b(∇φ)², the action is S = ½Σ_b(∇φ)² + (a−2)Σφ² + bΣφ⁴.
- At φ = 0, the Hessian on the constant mode is 2(a−2) = ε²μ_bare = ε²(μ − 12λc_ε). This is < 0 as soon as c_ε > μ/(12λ), i.e. for all small ε.
- So the φ-measure is not log-concave, and Brascamp–Lieb/Helffer–Sjöstrand with a positive Hessian are unavailable. They work only where μ_bare ≥ 0, a massive region that is not uniform as ε → 0.
- What does hold is single-site log-concavity, a = 2 + o(1) > 0.
- In duplicated variables the joint (q,t)-law inherits the same non-convexity: the quadratic form is preserved by the rotation.

**(b) J = 0, log-concave: reduced to an image-kernel TP2 property (PROVED reduction).**
Setting: ρ = q-marginal of e^{−W}, with W convex if V is. Then ρ is even and log-concave by Prékopa, and so is s := ρ^{*(N−1)}. Let g = E[t²|q], nonincreasing in |q| (EMN).
1. Exchangeability gives E[q_0|Q=u] = u/N, so Ψ(u) = E[q_0 g(q_0)|Q=u]/E[q_0|Q=u].
2. Given Q = u, q_0 has density ∝ ρ(q)s(u−q). Fold onto q > 0 using that g is even:
   Ψ(u) = ∫_0^∞ g dπ_u, with π_u(dq) ∝ q ρ(q) D(u,q) dq and D(u,q) := s(u−q) − s(u+q) ≥ 0. Positivity holds because s is even and log-concave, hence decreasing in |·|, and |u−q| ≤ u+q.
3. **If D is TP2 on (0,∞)², then π_u is MLR-increasing in u, so Ψ↓.** For Gaussian s, D ∝ e^{−(u²+q²)/2c}·sinh(uq/c); this is the 0-d sinh mechanism again.

Analytic criterion. Write s = e^{−ψ}, Δ = ψ(u+q) − ψ(u−q), k(Δ) = log(1−e^{−Δ}). Then
  ∂_u∂_q log D = ψ''(u−q) + k'(Δ)[ψ''(u+q) − ψ''(u−q)] − Δ_uΔ_q/(4 sinh²(Δ/2)).
- The middle term is ≥ 0 if ψ'' is nondecreasing on [0,∞) (EMN for s).
- For Gaussian s the criterion reduces to sinh²w ≥ w² (true).
- **It fails for flat-bottomed s.** For s = e^{−z⁴}, a 40-digit computation gives −0.16 at u = q = 0.1; the leading-order behaviour D ≈ 8uq(u²+q²) is not TP2. Huber-type s also fails (−0.0024).
- For quartic q-marginals with b = 1 and N = 2, D is TP2 for a ≥ 0.5 and fails at a = 0.1. N = 3 is inconclusive: the minimum is ≈ −6·10⁻⁶ at every a, which looks like quadrature error but was not resolved.
- Yet Ψ itself was monotone at a = 0 (psiJ0.py), so the route is lossy.
- Expected provable class: ψ'' ≥ α > 0 with ψ'' − α small (near-Gaussian). This is the T2b single-site regime, but for J = 0 only.

**(c) J > 0: no proof.** Step 1 needs G_0, which now depends on all |q_x|. Step 2 needs the conditional law given Q, which is no longer a convolution. The image-kernel mechanism therefore does not transfer as is.

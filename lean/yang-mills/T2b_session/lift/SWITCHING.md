# IC via random currents: progress (lift seat)

Scripts in /home/claude/t2b/lift: ic_form.py, p4_test.py, p4_test_anyc.py, ly_test.py.

Setting:
- Ising ferromagnet on a finite graph, ghost g, field H·c with c ≥ 0 and c ≡ 1 on B, n = |B|.
- M = Σ_B σ.
- IC: R_B = ⟨M;M²⟩/⟨M⟩ is nonincreasing in H.

## 0. CORRECTION to the B3 reduction in my first report

The ghost-marginalisation formula ⟨K⟩ = Σ_x [w tanh w + f(w)·1(x∈O)] holds only when the measure has no constraint that involves the ghost edges. That is true for 𝒟 (sources {l,g}, ∅), but **not for 𝒩**. The event k ↮ g in n₁+n₂ forces n₁ and n₂ to have no ghost edge at every site of the bulk cluster C(k).

Given the bulk currents, under 𝒩:
- sites x ∈ C(k) contribute 0 ghost edges and carry weight 1 (not cosh or sinh), and the parity there must be even in both currents;
- sites x ∉ C(k) are as before.

Corrected statement:

  IC ⟺ E_𝒩[ Σ_{x∉C(k)} (2w_x tanh w_x + f(w_x)(1_{O₁}+1_{O₂})(x)) ] ≤ E_𝒟[ Σ_x (2w_x tanh w_x + f(w_x)(1_{O₁}+1_{O₂})(x)) ],

with f(w) = 2w/sinh 2w.
- The 2w tanh w terms no longer cancel. 𝒩 loses them on C(k), which is a *favourable* term.
- O₂ (the ghost-odd sites of the sourceless current) is not empty in general.
- **The Sonnet b3check helper should use this form.**

## 1. Clean representation after switching on C(k) (derived; not enumerated)

The lead's formula ⟨σ_k;σ_iσ_j⟩ = ⟨σ_A⟩P^{A,∅}[k↮g] holds, with A = {k,g,i,j}. The event k ↮ g is the same as i ↮ j, since the four sources pair up.

On k ↮ g, the cluster C(k) contains k and exactly one of i, j, and no ghost edge. Switch on C(k). This preserves the weights and K, since C(k) has no ghost edge. Collecting terms:

  ⟨M;M²⟩ = 2 Σ_{p∈B} Σ_{a,b∈B∖{p}} Z^{pg} Z^{{a}Δ{b}} P^{pg,{a}Δ{b}}[a ↮ g] / Z²,

so

  **R/2 = Σ_p π(p) · Σ_{a,b∈B∖p} ⟨σ_aσ_b⟩ · P^{pg,{a}Δ{b}}[a ↮ g]**,   with π(p) = ⟨σ_p⟩/⟨M⟩.

Here a = b means the second current has no sources. This is the Ising version of R = 2⟨φ²⟩·P[loop ↮ path]:
- n₁ is the path from p to g;
- n₂ is the a–b loop, and its cluster must avoid the ghost, and therefore the path's cluster.

IC then reads ⟨K₁+K₂⟩_{𝒩'} ≤ ⟨K₁+K₂⟩_𝒟, where:
- 𝒩' has sources ({p,g}, {a}Δ{b}), weight Z^{pg}Z^{aΔb}1[a↮g], summed over p and a, b ∈ B∖p;
- 𝒟 has sources ({l,g}, ∅), summed over l.

The first current now has the same source type in both measures. The comparison is between "a free sourceless n₂" and "an n₂ carrying an a–b pair whose cluster avoids the ghost". Under 𝒩', the whole cluster of a carries zero ghost edges (the favourable term in §0). What is unfavourable is the tilt of the (p, n₁) marginal by the number of admissible (a, b) choices.

## 2. Exact spin form of IC (VERIFIED, ic_form.py: error 5e-13; IC held on 300 random graphs)

For Ising spins, M³ = (3n−2)M + 6S₃ and M² = n + 2S₂, where S₂ and S₃ are the sums of pair and triple products in B. Hence

  **R_B = 2(n−1) − 2⟨S₂⟩ + 6⟨S₃⟩/⟨M⟩**,   and   **IC ⟺ H ↦ 3⟨S₃⟩/⟨M⟩ − ⟨S₂⟩ is nonincreasing.**

## 3. Stepping stones

- **n = 1:** R = 0. Trivial.
- **n = 2:** R = 2(1 − ⟨σ₁σ₂⟩). IC ⟺ ⟨σ₁σ₂⟩ is nondecreasing ⟺ GKS II. **PROVED.** In the representation of §1 this is the identity ⟨σ_p⟩P^{pg,∅}[p'↮g] = ⟨σ_p⟩(1 − ⟨σ₁σ₂⟩).
- **n = 3:** Aizenman's formula with the ghost as the fourth source gives
  ⟨σ₁σ₂σ₃⟩ = Σ_k⟨σ_k⟩⟨σ_{B∖k}⟩ / (1 + 2P₄),   where P₄ = P^{123g,∅}[1, 2, 3, g all in one cluster].
  (Among the three pairings, exactly one occurs unless all four sources are connected.)
  - Symmetric B: R = 4 − 6⟨σ₁₂⟩·2P₄/(1+2P₄). So **IC₃ ⟸ P₄ nondecreasing in H** (together with GKS).
  - Conjecture **P4↑**: P₄ is nondecreasing in H. It held on 400 random graphs with c = 1 on B, and on 400 more with an **arbitrary** c ≥ 0. Worst decrease 2e−7, which is round-off at J = 0, where P₄ ≡ 1. So P4↑ appears not to need field homogeneity.
  - Equivalent form: Σ_k⟨σ_k⟩⟨σ_{B∖k}⟩ / ⟨σ₁σ₂σ₃⟩ is nondecreasing, i.e. the ghost-4-point Ursell function divided by ⟨σ₁₂₃⟩ is monotone.
- **Symmetric blocks of general size n** (GS blocks are fully permutation-symmetric): with ρ₂ = ⟨σσ⟩ and P = P₄(any triple),
  R_B = 2(n−1) + (n−1)ρ₂[3(n−2)/(1+2P) − n],
  and IC ⟺ ∂_H{ρ₂[3(n−2)/(1+2P) − n]} ≤ 0.
  - If the bracket is ≤ 0, then P4↑ plus GKS suffice.
  - In the Gaussian/GS limit, however, the bracket is > 0. The reason: R_φ = 2Var φ exceeds 2α²(n−1), because intra-block ferromagnetism raises the variance. P must tend to 1 like 1 − δ/n.
  - So IC on large blocks needs the **quantitative** comparison 6(n−2)ρ₂P′/(1+2P)² ≥ ρ₂′·[bracket]. This is exactly the notes' "tangling at least as strong as Wick", now stated through one connection probability P₄ and one pair correlation.
- **B = V, c ≡ 1:** this is the 0-d statement for the law of M. It held for Z = ∏cosh(a_kH), i.e. sums of independent weighted spins (ly_test.py, worst +4e−16). It is **false** for the single Lee–Yang factor 1 + H², which is not the transform of a positive measure. So a Lee–Yang zero-location argument alone cannot prove it; positivity, i.e. a Newman or GS structure, must enter.

## 4. Assessment of the switching route

- (a) Putting the ghost edges in the single current works for 𝒟. For 𝒩 the connectivity event couples to them (§0). The representation of §1 is the cleanest form I have, and it is non-pointwise as required.
- (b) A monotone coupling of ghost-odd sets: not found. What remains open is reduced to one probability, P₄ (n = 3), together with the size of its growth rate relative to ρ₂′ (large n).
- Next steps:
  1. Try to prove P4↑. The derivative of P₄ is a ghost-edge count difference between 4-source and 0-source double currents conditioned on full connection. This is the n = 3 analogue of §0 and is small enough to attack.
  2. Then derive the quantitative large-n inequality, perhaps by expressing P′ through 6-point ghost currents.

## 5. P4↑: round 2 (p4_coord.py, p4_check.py)

### 5.1 Coordinatewise monotonicity is FALSE
Counterexample, checked with mpmath at 40 digits:
- 3 sites, J₀₁ = 0.06, J₁₂ = 1.7, fields h = (0.001, 0.002, 0.002).
- S = Σ_kρ_k = 1 + 2P₄ has ∂_{h₀}S = −296.7, ∂_{h₁}S = +77.9, ∂_{h₂}S = +70.5.
- Along the ray h·t, S increases: 1.37753 → 1.37761 → 1.37812 → 1.37997 → 1.6008 for t = 1, 2, 5, 10, 100.
- The termwise ratios ρ_k = ⟨σ_k⟩⟨σ_iσ_j⟩/⟨σ₁σ₂σ₃⟩ = P^{123g,∅}[i↔j] also fail coordinatewise.

So P4↑ holds only for the **Euler derivative** H∂_H = Σ_x h_x∂_{h_x}, which counts ghost edges. A Russo-type argument edge by edge cannot work. This matches the lead's (ii) for IC.

### 5.2 Exact reformulation
H∂_H log(Z^A Z^∅[F]) = E[K | F] and H∂_H log(Z^A Z^∅) = E[K], where A = {1,2,3,g}, F = {1, 2, 3, g in one cluster of n₁+n₂}, and K = total number of ghost edges of n₁+n₂. Hence

  **H∂_H P₄ = Cov_{P^{A,∅}}(K, 1_F)**, so P4↑ ⟺ K and F are positively correlated.

### 5.3 Half of a proof (PROVED): conditional part ≥ 0
Condition on the bulk currents ω = (n₁, n₂) restricted to E. Then:
- The ghost edges are independent Poissons conditioned on parity. A site has even/odd parity in current r according to deg_{n_r|E}(x) + 1_{A_r}(x).
- Bulk cases for {1,2,3}:
  - (α) all three sources in one bulk component: that component has odd ghost parity, so it attaches to g, and F = 1;
  - (γ) all three in separate components: each is odd and attaches, so F = 1;
  - (β) {i,j} together in a component C, and k elsewhere: k's component is odd and attaches. F = 1 iff C attaches. That is automatic if C contains a ghost-odd site, and otherwise (event β₀) it is the event K_C > 0.
- So given ω, F is either constant or equal to 1[K_C > 0], with K_C independent of the other ghost edges. Hence Cov(K, F | ω) = 1_{β₀}·E[K_C|ω]·P(K_C = 0|ω) ≥ 0.
- Law of total covariance: H∂_HP₄ = E[Cov(K,F|ω)] + Cov_bulk(E[K|ω], P(F|ω)). The first term is ≥ 0.
- The **second term is open**. Here:
  - E[K|ω] = Σ_x[2w_x tanh w_x + f(w_x)(1_{O₁}+1_{O₂})(x)];
  - P(F|ω) = 1 − 1_{β₀}·∏_{x∈C}cosh^{−2}w_x.

  Heuristically it is ≥ 0: on β₀, C has no odd sites, so E[K|ω] is lower there, and P(F|ω) is lower there too. But odd sites outside C are not controlled pointwise. This bulk covariance is the precise remaining step for P4↑.

## 6. Does P4↑ settle symmetric blocks? NO. The exact remaining inequality
Symmetric block (all pair correlations equal ρ₂, all triple P₄ equal P):
- R_B = 2(n−1) + (n−1)ρ₂[3(n−2)/(1+2P) − n].
- IC ⟺ 6(n−2)ρ₂·P′/(1+2P)² ≥ ρ₂′·[3(n−2)/(1+2P) − n].
- The bracket is > 0 exactly when R_B > 2(n−1). That is the GS regime: R_φ > 2α²n, because the intra-block coupling raises Var φ above α²n.
- So P4↑ (P′ ≥ 0) plus GKS (ρ₂′ ≥ 0) does not suffice. P′ must dominate quantitatively.

GS limit. Put α² = ν/n, κ = nρ₂ = O(1), and P = 1 − δ/n. Then
- ⟨φ²⟩ ≈ ν(1+κ) and R_φ ≈ ν[2 − 2κ + (2/3)κδ];
- **IC ⟺ κ(δ − 3) is nonincreasing in H**;
- Gaussian: R_φ is constant, so κ(δ − 3) is constant. This is the equality case, the "tangling = Wick" point.
- The quantitative input is therefore: n(1 − P₄), the rescaled probability that the 4-source current fails to be fully connected, must decrease at least as fast as 3 − δ times the growth of κ. Equivalently, d log(δ−3)/dH ≤ −d log κ/dH.

Relation to the 0-d teammate's zero-field Ψ(u) criterion: not established.
- Ψ removes the field through the sinh(hu) weights on Q.
- P₄ is a field-dependent connection probability with ghost.
- A translation would need the conditional law at H = 0 given Q = u of the 4-source connection event. I have not derived it. I expect the zero-field route to be easier, because it needs no quantitative P′ versus ρ₂′ comparison.

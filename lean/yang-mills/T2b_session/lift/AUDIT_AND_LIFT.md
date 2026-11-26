# T2b: end-to-end audit (assuming the target lemma) and the lattice lift

Directory: /home/claude/t2b/lift. Scripts: pointwise_test.py, check_z0.py, osp_test.py, ring_test.py, nonti_test.py, gc_test.py, gc_test2.py, gc_test3.py.
Status labels used below:
- PROVED = checked here line by line.
- LEAN = proved in PP2ABF.lean.
- STD = standard, with the citation not re-read by me.
- READ = I read the source.
- GAP = a real gap.

## A. Audit

### A0. Recommended formulation: work on tori throughout
Every lattice step should be done on the periodic torus Λ_{ε,L} = εℤ²/Lℤ² with h > 0, not in the infinite-volume plus state.
- On the torus everything is a finite-dimensional smooth integral, and translation invariance is exact.
- The lemma should therefore be stated on tori, uniformly in (ε, L).
- The teammates' numerics (rings) are already in that setting.
- Infinite volume then enters only through one limit of m at fixed h > 0 (A5).

### A1. Identity (★) — PROVED (exact, every ε, L)
Weight: exp(Σ_{⟨xy⟩}φ_xφ_y + ε²hΣφ_x − Σ(aφ_x² + bφ_x⁴)), with a = 2 + ½ε²μ_b, b = λε², μ_b = μ − 12λc_ε.
- Since Σ_{⟨xy⟩}φ_xφ_y = 2Σφ² − ½Σ(φ_x − φ_y)², the action is ε²Σ[½|∇_εφ|² + ½μ_bφ² + λφ⁴ − hφ]. This is the continuum normalisation, with λφ⁴, Wick ordering λ:φ⁴: and counterterm −6λcφ²·2/2.
- Integration by parts at site 0 (boundary terms vanish because of e^{−bφ⁴}): 0 = ⟨Σ_{y∼0}φ_y⟩ − 2am − 4b⟨φ_0³⟩ + ε²h.
- Translation invariance gives Σ_{y∼0}⟨φ_y⟩ = 4m, hence μ_b m + 4λ⟨φ_0³⟩ = h.
- With :φ³: = φ³ − 3c_εφ, this becomes (EOM) μm + 4λ⟨:φ_0³:⟩ = h.
- So h/m = μ + 4λT/m with T = ⟨:φ_0³:⟩. Differentiating, (m − hχ)/m² = 4λ∂_h(T/m). This is (★). It needs m > 0, which holds for h > 0 (GKS I plus strictness, STD).
- Next, T/m = ⟨φ_0³⟩/m − 3c = R + ⟨φ_0²⟩ − 3c, using ⟨φ_0;φ_0²⟩ = ⟨φ³⟩ − m⟨φ²⟩. Together with the Maxwell relation (A2) this gives
  m − hχ = 4λm²(∂_hR + ∂_h⟨φ_0²⟩) = 4λm²∂_hR + 8λm²(−∂_μm), exactly.
- Hence the lemma ∂_hR ≤ K∂_h⟨φ_0²⟩ (K ≥ 0) ⟺ m ≤ h∂_hm − a m²∂_μm with **a = 8(1+K)λ**.
- The m³ variant ∂_hR ≤ K∂_h⟨φ_0²⟩ + (k/λ)m ⟺ the same inequality with an extra e m³, e = 4k. It is dimensionally consistent: m is dimensionless and h, μ, λ have dimension mass².
- R = 2G(0,0) + u_3(0,0,0)/m, and ∂_hG(0,0) = ε²Σ_z u_3(0,0,z) ≤ 0 (GHS, EMN class). Both checked.

### A2. Maxwell relation — PROVED on the torus
- Here ∂_μ = ½ε²∂_a and ∂_a⟨φ_0⟩ = −Σ_y⟨φ_0;φ_y²⟩, so ∂_μm = −½ε²Σ_y⟨φ_0;φ_y²⟩ ≤ 0 (GKS II).
- ∂_h⟨φ_0²⟩ = ε²Σ_y⟨φ_0²;φ_y⟩, and translation invariance on the torus gives equality with −2∂_μm.
- In infinite volume this would need uniform summability of truncated correlations at h > 0. That is avoided by A0.

### A3. ABF integration — LEAN, modulo two hypotheses
`abf_char_of_pde` needs the following for m_{ε,L}:
- jointly C¹ in (μ, h) with h > 0: true for a finite smooth integral;
- monotone in h: GKS II;
- antitone in μ: GKS II, A2;
- the PDE for **all** μ ∈ ℝ, h > 0.

Point 1. If K is only uniform on compact (μ, h)-windows, a localised version of `abf_Char` is needed. This is easy, but **not in Lean**: characteristics from (μ_0, h_1) to (μ, h') stay in [μ, μ_0] × [h_1, h'].

Point 2 (important simplification). Lean Part A(i) uses only DIVERGENCE of m/h, never a rate. So run it **per torus**:
- If χ_{ε,L}(μ_0, h=0) ≥ X, then by smoothness m/h_1 ≥ X/2 for small h_1.
- abf_Char then gives m_{ε,L}(μ, h') ≥ s for every μ < μ_0 − a s²/2 and h' ≥ 4sE/X (E = 1 when e = 0).
- This is uniform in (ε, L), since a does not depend on them. GHS is not needed here.
- Conclusion: **if χ_{ε_j,L_j}(μ_0, 0) → ∞ along a sequence, then liminf_j m_{ε_j,L_j}(μ, h') ≥ s for every h' > 0 and every s with 4(1+K)λs² < μ_0 − μ.**

### A4. Thresholds — GAP (definitional, but real)
- B–D (arXiv:2202.02295, READ via fetch) define the continuum μ_c through boundedness of the torus susceptibility χ^{ε,L} = ε^dΣ_x⟨φ_0φ_x⟩ at h = 0, uniformly in ε and L, "unique μ_c separating bounded/unbounded".
- Their normalisation is λ/4·φ⁴ and (μ + a^ε)/2·φ², so λ_notes = λ_BD/4. Their counterterm also has a bounded λ² piece, so μ is shifted by O(λ²).
- A3 gives sharpness with the threshold **μ_c^♯ := inf{μ : limsup_{ε→0} sup_L χ_{ε,L}(μ) < ∞}**.
- The sequence must have ε_j → 0. If ε stays bounded below, the divergence is a coarse-lattice effect, and the continuum limit does not see it.
- If L_j stays bounded, χ_{ε,L} = L^{−2}⟨φ(1_T)²⟩ stays bounded as ε → 0 (continuum torus limit; STD). So L_j → ∞ may be assumed.
- Trivially μ_c^♯ ≤ μ_c^χ. **Equality holds iff the sup over ε defining μ_c^χ is not attained on coarse lattices.** If B–D's sup runs over all ε ≤ ε_0, it may be strictly larger. This must be fixed by **restating T2b with the limsup threshold**; T2a's threshold then has to be the same one.
- With this restatement, no interchange of h ↓ 0 and ε → 0 is needed (A3 Point 2).
- The worry in the Kac route (limsup A_c(γ) ≤ A_c^cont) **disappears here**, because the per-model conclusion is uniform and only divergence is used.
- What I first tried, and what fails: comparing torus χ at h = 0 with the infinite-volume lim m/h, or using fixed-ε thresholds μ_c(ε). That needs an ε-uniform torus/infinite-volume comparison, which is T2a territory. Avoid it.

### A5. Continuum limit with h > 0; meaning of M⁺ — STD inputs, citations to verify
- ⟨φ(f)⟩ = m∫f for any translation-invariant state, and for the lattice ⟨φ_ε(f)⟩ = m_{ε,L}ε²Σf → m∫f. So the one-point function is a constant density, and M⁺(μ) := lim_{h↓0} m(μ,h) is meaningful.
- Order of limits: (ε, L) → (0, ∞) jointly at fixed h > 0, then h ↓ 0. A3 gives the bound before h ↓ 0, uniformly in h'.
- Cleanest route to convergence of m: Griffiths' convexity lemma. p_{ε,L}(h) is convex in h, with m = ∂_hp. If p_{ε,L} → p (needs: convergence of the Wick-renormalised pressure, joint in ε → 0 and L → ∞; STD, GJ / GRS lattice approximation, not re-read) and p is differentiable at h > 0 (Lee–Yang for continuum φ⁴₂, Simon–Griffiths 1973, STD), then m_{ε,L} → ∂_hp along the **full** sequence.
- This also makes the limit independent of the subsequence and of boundary conditions, and identifies it with the plus-state magnetisation at h > 0.
- In infinite volume at h > 0 the continuum limit should be unique by Lee–Yang. I did not verify that a published reference proves joint (ε, L) convergence of the pressure for φ⁴₂ with h ≠ 0 at arbitrary λ. **Flag: needs a citation check.** "Duch–Hairer–Yi–Zhao" was not checked by me.
- Fallback that needs no continuum state: state T2b as lim_{h↓0} liminf m_{ε,L}(μ,h) ≥ s. Then any subsequential limit state has ⟨φ(f)⟩ ≥ s∫f, assuming uniform integrability (moment bounds; STD).

### A6. Conclusion of A
Given the torus lemma with K uniform in (ε, L):
- M⁺(μ)² ≥ (μ_c^♯ − μ)/(4(1+K)λ) for μ < μ_c^♯ (notes' λ). With e: 2Δ/(a + 2eΔ), a = 8(1+K)λ.
- K = 0 reproduces Landau exactly (m² = −μ/4λ).

Inputs besides the lemma:

| # | Input | Status |
|---|---|---|
| 1 | (★), EOM, Maxwell on torus | PROVED |
| 2 | GKS I/II, GHS for φ⁴ on tori (EMN) | STD |
| 3 | ABF characteristics, limits | LEAN (localised version: easy, not in Lean) |
| 4 | Per-torus Part A(i) argument | PROVED here, straightforward from LEAN, not yet in Lean |
| 5 | Threshold = μ_c^♯ (limsup version) | GAP vs B–D μ_c^χ: restate |
| 6 | Pressure convergence (ε, L) → (0, ∞) at h > 0, plus continuum Lee–Yang | STD, unverified citations |
| 7 | m > 0 at h > 0, finiteness of moments | STD |

Not needed: infinite-volume lattice plus state, uniform clustering at h > 0, rates for χ, the hdis/κ input (only needed for δ ≥ 3).

## B. Lift

### B1. Numerical facts found here (exact quadrature / enumeration)
- **On-site term can be positive.** D_z := m·κ(φ_0, φ_0², φ_z) − ⟨φ_0;φ_0²⟩⟨φ_0;φ_z⟩, with Σ_zD_z ≤ 0 ⟺ ∂_hR ≤ 0. D_0 reaches +0.31 relative on φ⁴ (2-site, 3-site, 3-ring, double-well a < 0) and on Ising GS blocks; this was refined and is not grid error.
- On translation-invariant rings with uniform h, off-site D_z ≤ 0 held in every test and compensated D_0. With inhomogeneous fields, off-site D_z > 0 also occurs (+3%).
- **The summed target with UNIFORM h held on non-translation-invariant graphs**: φ⁴ 3-site random J, worst −4e−7; Ising GS blocks on random graphs, worst −1.5e−5. So translation invariance is not needed, but field homogeneity is. This agrees with the lead's (ii).
- Conjecture GC, ⟨q_0F;Q⟩⟨q_0⟩ ≤ ⟨q_0F⟩⟨q_0;Q⟩ for coordinatewise nonincreasing F(|q|), tested exactly on all extreme rays (down-set indicators):
  - holds, worst 0.0, for spin-1 with any vacancy weight w, including w > 2 (outside the GS class);
  - holds for 5-valued spins with ARBITRARY even product weights (n = 2 exhaustive, n = 3 sampled);
  - holds with MTP2 |q|-interactions;
  - **fails** (+0.99) with non-MTP2 |q|-interactions.

  So GC appears to be a general theorem for even product (or MTP2) |q|-weights, with no EMN or GS hypothesis. The EMN hypothesis is needed only for "G nonincreasing". GC is needed only for F = G, but the general-F version looks true and is the cleaner target.

### B2. K > 0 and the m³ variant
- Both sides of the lemma are O(h) at small h in the disordered phase: R is even in h, so ∂_hR ≈ R''(0)h, and ∂_h⟨φ²⟩ = O(h).
- The 1/H blow-up of −χu_3/m² is cancelled identically by the u_4 term, because u_3(000)/m is even-analytic. So K > 0, and likewise the (k/λ)m slack, are genuine slack at the right order.
- But they cannot be exploited by any termwise or pointwise split: each split term reintroduces the 1/H pieces, and the on-site term has the wrong sign. So K > 0 does not rescue the false pointwise lemmas (L1, L2, termwise IC).

### B3. Random-current route for IC: a ghost-marginalisation reduction (derived, not yet coded)
- H∂_H of the current weight equals K = Σ_x n_{xg}.
- Given the bulk current n|_E and sources A, each ghost edge xg has a Poisson(w_x = Hc_x) weight conditioned on the parity p_x = (deg_{n|E}(x) + 1_A(x)) mod 2. These are independent over x.
- E[n_{xg} | odd] = w coth w and E[n_{xg} | even] = w tanh w.
- Hence ⟨K⟩ = Σ_x w_x tanh w_x + Σ_x f(w_x)·P[x ∈ O], with f(w) = w(coth w − tanh w) = 2w/sinh 2w and O = the ghost-odd sites. The bulk measure has weights ∏_{O}sinh w_x ∏_{O^c}cosh w_x.
- The first term cancels between 𝒩 and 𝒟 when both are normalised. So:
  **IC ⟺ E_𝒩[Σ_{x∈O} f(w_x)] ≤ E_𝒟[Σ_{x∈O} f(w_x)]**, i.e. 𝒩 has fewer ghost-odd sites (weighted by a decreasing f) than 𝒟.
- This is exactly the 0-d mechanism: q sinh(hq) and the monotonicity of x coth x.
- The comparison is now between two **bulk** (ghost-free) double-current measures that differ only in sources and in the indicator [k ↮ g]. The parity set O equals ∂n_1|_E Δ (A ∩ V).
- Suggested coupling: switch the 𝒩-pair (sources {k,g}Δ{i,j}, ∅) on the cluster of k, using k ↮ g. This maps it to sources ({i,j}, {k,g}) restricted to the cluster, and then sums over i ≠ j ∈ B against 𝒟's Σ_l. The label exchange within B is where homogeneity, c ≡ 1 on B, must enter.
- Unfinished: whether the switched configuration's ghost-odd set is dominated, in the weighted count, by 𝒟's. This needs care because O is defined from n_1 alone, not from n_1 + n_2.

### B4. Fallback (lead's (b))
- (★) forces exactly the quantity ∂_h(T/m) = ∂_hR + ∂_h⟨φ²⟩. In cumulants the target is mΣu_4(000x) + 2m²Σu_3(00x) ≤ χu_3(000), which needs an upper bound on u_4 at h > 0 in terms of u_3.
- GHS bounds the sign of u_3. Lebowitz bounds u_4 only at h = 0. The BFS tree bound is a LOWER bound on u_4, the wrong direction. So none of them controls it.
- Equivalent integrated form: h/m − 4(1+K)λ⟨φ_0²⟩ is nonincreasing in h. This is the same lemma.
- No GHS/Lebowitz-controlled replacement found. The alternatives are the Kac route (round 12) or a different parameter direction (∂_λ, with Wick counterterms), not explored.

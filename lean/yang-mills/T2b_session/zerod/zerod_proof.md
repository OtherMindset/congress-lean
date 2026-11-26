# T2b, 0-d case: R(H) = ⟨φ;φ²⟩/⟨φ⟩ is nonincreasing for H > 0. PROVED (whole EMN/GHS class)

Scripts in this directory: fast0d.py (0-d numerics and check of the pair representation), check0d.py (mpmath),
isingL*.py (tests of the lattice lemmas, which fail), Ftest.py (2-site test of conjecture GC).

## 0. Setting
dμ_H ∝ e^{−V(φ)+Hφ}dφ on ℝ. Assumptions:
- V is even and C².
- V'' is nondecreasing on [0,∞), i.e. V' is convex on [0,∞). This is the Ellis–Monroe–Newman class.
- ∫e^{c|φ|−V} < ∞ for every c. This needs V to be superlinear.

Notation: κ_n are the cumulants of φ (κ_n = ∂_H^{n} log Z), so m = κ1, χ = κ2, χ' = κ3, χ'' = κ4.

## 1. Reduction (task 1)
- ⟨φ;φ²⟩ = ⟨φ³⟩ − ⟨φ⟩⟨φ²⟩ = κ3 + 2κ1κ2 = ∂_H⟨φ²⟩, using ⟨φ²⟩ = κ2 + κ1² and ⟨φ³⟩ = κ3 + 3κ1κ2 + κ1³.
- R = 2χ + χ'/m.
- ∂_H R = 2χ' + (χ''m − χ'χ)/m². So R' ≤ 0 ⟺ 2m²χ' + mχ'' − χχ' ≤ 0 for H > 0.

Link to (★)/(★★). Write V = ½μφ² + λφ⁴, so a = μ/2 and b = λ.
- EOM: ⟨V'⟩ = H, i.e. μm + 4λ⟨φ³⟩ = H.
- Hence m − Hχ = m²∂_H(H/m) = 4λm²∂_H(⟨φ³⟩/m).
- ⟨φ³⟩/m = R + ⟨φ²⟩, so m − Hχ = 4λm²∂_H R + 4λm²∂_H⟨φ²⟩.
- Maxwell relation: −∂_μ m = ½⟨φ;φ²⟩ = ½∂_H⟨φ²⟩.

Therefore
  m − Hχ = 4λm² ∂_H R + 8λm²(−∂_μ m),
an exact identity. So **m − Hχ ≤ C λ m² (−∂_μ m) ⟺ ∂_H R ≤ (C/8 − 1)∂_H⟨φ²⟩**. This is (★★) in 0-d, and C = 8 ⟺ R nonincreasing.

If one uses the normalisation a = μ instead, the constant becomes C = 4. The notes' convention ∂_μ = ½ε²∂_a corresponds to a = μ/2.

## 2. Theorem (0-d)
Under the assumptions of §0, H ↦ R(H) is even and positive on ℝ∖{0}, and nonincreasing on (0,∞). Equivalently, 2m²χ' + mχ'' − χχ' ≤ 0 for H > 0. If V is quadratic, R is constant (= 2χ).

### Proof
**Step 1 (duplication).** Take φ, φ' i.i.d. ~ μ_H. Set q = (φ+φ')/√2 and t = (φ−φ')/√2.
- ⟨φ;φ²⟩ = ½E[(φ−φ')(φ²−φ'²)] = ½E[(φ−φ')²(φ+φ')] = √2 E[t²q].
- ⟨φ⟩ = E[q]/√2.
So **R = 2E[t²q]/E[q]**. This is an exact algebraic identity, valid for any law with finite third moment.

The joint density of (q,t) is ∝ e^{−W(q,t)+hq} with h = √2H and W(q,t) = V((q+t)/√2) + V((q−t)/√2).
- W is even in q and even in t, since V is even.
- For the quartic, W = a(q²+t²) + ½b(q⁴ + 6q²t² + t⁴).

**Step 2 (conditional law of t).** Let ρ(q) = ∫e^{−W(q,t)}dt (even) and g(q) = E[t²|q] = ∫t²e^{−W}dt/ρ(q). Claim: g is nonincreasing on [0,∞).
- For q, t ≥ 0 put x = (q+t)/√2 and y = (q−t)/√2. Then x ≥ |y|: if y ≥ 0, x − y = √2t ≥ 0; if y < 0, x + y = √2q ≥ 0.
- ∂_q∂_t W = ½[V''(x) − V''(y)] = ½[V''(x) − V''(|y|)] ≥ 0, because V'' is even and nondecreasing on [0,∞).
- So for 0 ≤ q < q', the ratio e^{−W(q',t)}/e^{−W(q,t)} is nonincreasing in |t|. This is a monotone likelihood ratio, so the law of |t| given q' is stochastically smaller than the law given q. Hence g(q') ≤ g(q).
- For the quartic it is explicit: t | q ~ e^{−(a+3bq²)t² − bt⁴/2}.

**Step 3 (tower plus symmetrisation).**
- E[t²q] = E[q g(q)] = ∫_ℝ q g(q) ρ(q) e^{hq} dq / Z = ∫_0^∞ g(q) · 2q sinh(hq) ρ(q) dq / Z. The last step uses that g and ρ are even.
- Likewise E[q] = ∫_0^∞ 2q sinh(hq)ρ(q)dq / Z.
- So **R(H) = 2∫g dπ_h**, where π_h(dq) ∝ q sinh(hq)ρ(q)dq on (0,∞). This is a probability measure for h > 0.

**Step 4 (stochastic monotonicity of π_h).** For 0 < h1 < h2, the ratio dπ_{h2}/dπ_{h1} ∝ sinh(h2 q)/sinh(h1 q) is increasing in q > 0.
- Its log-derivative is h2coth(h2q) − h1coth(h1q) = q⁻¹[k(h2q) − k(h1q)], with k(x) = x coth x.
- k is increasing on (0,∞), since k'(x) = (sinh x cosh x − x)/sinh²x > 0.
- So π_{h2} ≥_st π_{h1} (MLR implies stochastic order). Since g is nonincreasing, ∫g dπ_{h2} ≤ ∫g dπ_{h1}. ∎

Remarks.
- No differentiation is used, and no Lee–Yang input.
- Evenness: R(−H) = R(H), since the numerator and denominator are both odd.
- Positivity: R = 2E_π[g] > 0, which is GKS II in 0-d.
- Infinitesimal form: ∂_H R = 2√2 Cov_{π_h}(g(q), q coth(hq)) ≤ 0, a one-variable Chebyshev inequality.
- If V is C¹ with V' convex but not C², Step 2 goes through with one-sided derivatives, or by approximation.
- Limits: H ↓ 0 gives π_0 ∝ q²ρ(q). As H → ∞, R → 2lim_{q→∞} g(q), which is 0 for the quartic.

### Numerical confirmation (fast0d.py, grid quadrature; check0d.py, mpmath 40 digits)
- Potentials tested: x²+x⁴, −3x²+x⁴, −10x²+x⁴, −20x²+x⁴, −2x²+x⁶/6, cosh2x − 3x², x²/2+|x|³, −x²+x⁸.
- R decreases on H ∈ (0,6] in every case, and g is monotone in every case.
- The pair representation 2∫g dπ_h agrees with the direct (m3 − m1m2)/m1 to 1e-13.
- Two non-GHS potentials (6x²−6x⁴+x⁶ and 2x²−3x⁴+x⁶) also gave a decreasing R. So the GHS hypothesis is sufficient here, not shown necessary, and no counterexample was found.

### On the suggested routes
- (i) Lee–Yang. Z = Z(0)∏(1+H²/α_k²) holds: e^{−bφ⁴} gives order 4/3, so genus ≤ 1 and evenness kills the exponential factor. However, 2m²χ' + mχ'' − χχ' is cubic in the cumulants, so there is no term-by-term argument. Not pursued, because it is not needed.
- (ii) Duplication. This is what worked: one duplication, not the four-fold GHS rotation.
- (iii) A variance/Brascamp–Lieb-type inequality. Steps 2 and 4 are MLR/Chebyshev in one variable, so this route is in effect what was used.
- (iv) Second order in b. It is implied by the theorem, and was not done separately.

## 3. Lattice
Weight: exp(ΣJ_{xy}φ_xφ_y + HΣφ_x)∏e^{−V(φ_x)}, with J ≥ 0 and V in the GHS class; finite graph.

The lattice target, stated precisely:
- R(H) = ⟨φ_0;φ_0²⟩/⟨φ_0⟩.
- ∂_H⟨φ_0;φ_0²⟩ = Σ_x κ(φ_0, φ_0², φ_x), a joint cumulant of three variables.
- So ∂_H R ≤ 0 ⟺ **m Σ_x κ(φ_0, φ_0², φ_x) ≤ χ ⟨φ_0;φ_0²⟩**, with χ = Σ_x⟨φ_0;φ_x⟩.
- Note that ⟨φ_0;φ_0²⟩ ≠ ∂_H⟨φ_0²⟩ here; the 0-d formula R = 2χ + χ'/m does not hold.

### What transfers (PROVED)
**(a) Duplication.** Duplicate the field and set q_x = (φ_x+φ'_x)/√2, t_x = (φ_x−φ'_x)/√2.
- The weight becomes exp(ΣJ(q_xq_y + t_xt_y) + √2HΣq_x − ΣW(q_x,t_x)).
- The same algebra as in 0-d gives **R = 2⟨t_0² q_0⟩/⟨q_0⟩**.

**(b) Conditional law of |t|.** W depends on (|q_x|, |t_x|) only. Write r = |q| and u = |t|, and sum over the signs of t to get an Ising partition function Z_t(u).
- log Z_t is supermodular in u: by GKS I and II, ∂²log Z_t/∂u_x∂u_y = J_{xy}⟨σ_xσ_y⟩ + Cov(Σ_z J_{xz}u_zσ_xσ_z, Σ_w J_{yw}u_wσ_yσ_w) ≥ 0.
- e^{−W(r,u)} is log-submodular in (r,u), by the computation of Step 2.
- So the density of (r, −u) is MTP2.

Consequences:
- G(r) := E[t_0² | q] = E[u_0² | r] is coordinatewise nonincreasing in r. This holds for the whole GHS class: the conditional law of a MTP2 density is stochastically monotone.
- The weight ρ̃(r) of the absolute values (after integrating out t) is MTP2 in r, because marginals of MTP2 densities are MTP2 (Karlin–Rinott 1980).

**(c) Representation.** Write q_x = s_x r_x with Ising signs s. Then
- **R/2 = E_{π_H}[G(r)]**, with π_H(dr) ∝ ρ̃(r) · r_0 Σ_s s_0 exp(ΣJ r_xr_y s_xs_y + √2HΣr_xs_x).
- π_H is a positive measure by GKS I. In 0-d it reduces exactly to the π_h of §2.

### Where it breaks
The lattice target ⟺ E_{π_H}[G] ↓ in H. This would follow from π_H being stochastically increasing in H. The Holley route needs two things, and both are **FALSE** in general:
- (L1) r ↦ log N(r), with N = Σ_s s_0 s_g e^{…} (ghost g), supermodular. Equivalently, the current degrees d_x(n) are positively correlated under the single-current measure P^{0g}.
  - isingL3.py (random graphs) and isingL4.py (ghost structure: path, ring, complete) give correlations down to −0.77.
  - Mechanism: alternative routes for the source path.
- (L2) Ψ(r) = ∂_H log N = √2Σ_x r_x⟨s_0s_x⟩/⟨s_0⟩ nondecreasing in each r_y. isingL5.py gives correlations down to −0.20.
  - Both failures occur at strongly inhomogeneous r.

So the lattice needs an argument that is not pointwise in r. The natural statement, which is OPEN:

**(GC)** For a ferromagnetic system of real spins with even absolute-value weight ρ̃ that is MTP2 in |q|, and for every F(|q|) coordinatewise nonincreasing, H ↦ ⟨q_0F⟩_H/⟨q_0⟩_H is nonincreasing for H > 0.

- GC with F = G implies the lattice target.
- GC is true in 0-d for any even ρ (§2).
- Ftest.py: 2-site φ⁴ with a ∈ {−2,−0.5,0.5,2}, J ∈ {0.2,1,3}, five test F's (Gaussian and indicator in |q_1|, in |q_0|, and 1/(1+|q|²)) found no violation. The max increment observed was < 0, on a 401² grid; this is coarse.
- Equivalent infinitesimal form: ⟨q_0F;Q⟩⟨q_0⟩ ≤ ⟨q_0F⟩⟨q_0;Q⟩, with Q = Σ_x q_x.

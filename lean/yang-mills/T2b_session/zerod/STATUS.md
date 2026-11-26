# T2b same-site lemma — status (26 Nov 2026)

Target. Lattice φ⁴ on a torus: R(H) = ⟨φ_0;φ_0²⟩/⟨φ_0⟩ is nonincreasing for H > 0, with a uniform field. Equivalent forms:
- m Σ_x u4(000x) + 2m² Σ_x u3(00x) ≤ χ·u3(000);
- C = 8 in (★★).

Detailed files in this directory: zerod_proof.md (0-d), lattice.md (§0–9), LY1.md.

## PROVED
1. **0-d, the whole EMN class** (V even, V' convex on [0,∞), superlinear). Duplicate, then use:
   - R = 2E[t²q]/E[q];
   - g = E[t²|q] is decreasing (MLR, since ∂_q∂_tW ≥ 0);
   - R = 2∫g dπ_h with π_h ∝ q·sinh(hq)·ρ;
   - sinh-ratio MLR.
   Rigorous, and needs no Lee–Yang input.
2. **Lattice identities** (any graph, even site weight):
   - R = 2⟨t_0²q_0⟩/⟨q_0⟩.
   - G_x = E[t_x²|q] is coordinatewise decreasing in |q|. This uses MTP2 of the joint density of (|q|, −|t|) (GKS II) and holds for the EMN class.
   - ρ̃(|q|) is MTP2.
3. **Theorem 7.1** (torus, translation invariance, uniform field): R/2 = ∫Ψ(u)·u sinh(hu) P_0(du) / ∫u sinh(hu) P_0(du), with Ψ(u) = E_0[Σ_x q_x t_x² | Q=u]/u at zero field. So Ψ↓ implies R↓.
4. **Conditioning on t** (any graph, quartic V, uniform field):
   - R/2 = E_{π_h}[t_0²], with π_h(dt) ∝ e^{JΣt_xt_y}·N(t,h)dt and N = ∫q_0 e^{−ΣW + JΣq_xq_y + hQ}dq ≥ 0 (GKS I).
   - ∂_h(R/2) = Cov_{π_h}(t_0², Φ), with Φ = ⟨q_0Q⟩_t/⟨q_0⟩_t.
   - **Hence R↓ follows from (A) and (B) below, by FKG.**
5. **Exact identities:** (★) ⇔ (★★) with C = 8 ⇔ R↓. In random-current form, IC ⇔ ⟨K⟩_𝒩 ≤ ⟨K⟩_𝒟 (ghost-edge counts).

## OPEN — the exact statement needed for J > 0 (route 4)
Setting: the q-system given t. It is a ferromagnet with site weights e^{−(a+3bt_x²)q² − bq⁴/2} (EMN, with inhomogeneous masses) and uniform field h ≥ 0. For x ≠ y, any y, all h > 0:

- **(A)** ⟨q_0 q_x² q_y²⟩⟨q_0⟩ ≥ ⟨q_0 q_x²⟩⟨q_0 q_y²⟩. This is log-supermodularity of N in t², so π_h is MTP2 in |t|. The t-sign Ising factor is supermodular by GKS.
- **(B)** ⟨q_0 q_y² Q⟩⟨q_0⟩ ≥ ⟨q_0 q_y²⟩⟨q_0 Q⟩, i.e. h ↦ ⟨q_0q_y²⟩/⟨q_0⟩ is nondecreasing. This makes Φ decreasing in each |t_y|.

Both say that even observables are positively correlated under the source-weighted signed measure q_0·dμ/⟨q_0⟩.

Evidence:
- (A): holds on 2 sites (condtA.py; a ∈ {−1, 0.5, 2}, b ∈ {0.1, 1}, J ∈ {0.3, 1, 3}); the minimum cross-difference is > 0.
- (B): holds on 2 sites (condt.py; inhomogeneous a_0, a_1) and on 3-site rings (condtB3.py, random inhomogeneous masses); the minimum relative derivative is > 0.
- (B) at y = 0, homogeneous: by the EOM, ⟨q_0³⟩/m = [(h + JΣ_{z∼0}m_z)/m_0 − 2a_0]/(4b′). Since h/m_0 is increasing (GHS concavity), this case is plausible. With inhomogeneous masses the term m_z/m_0 is not controlled.
- **Warning:** the Ising analogue of (A) (degree correlations under P^{0g}, lemma L1) FAILS on inhomogeneous graphs with ≥ 4 sites. So (A) might fail beyond 2 sites; this is untested for ≥ 3 sites (6-d integrals).

Alternative open statement (route 3): Ψ↓ at zero field. It is false in general (see below) but numerically true in the T2b regime: a ≈ 2, b small, J = 1, and in all strongly coupled or single-well cases tested.

## COUNTEREXAMPLES / FALSE STATEMENTS (all verified)
| statement | counterexample |
|---|---|
| R↓ for every even Lee–Yang measure (LY1) | ν ∝ x²e^{−x²/2}: R = 2 − 6/(H²+3) + 2/(H²+1), increasing for H > 3^{1/4} (exact) |
| LY ⇒ R↓ for positive densities | e^{βH²}(1+H²/a²) with 2βa² ≥ 1, e.g. (2+x²)e^{−x²/4} |
| one-variable GHS ⇒ R↓ | δ_{±3} + cδ_{±1}, c = 10, 15 |
| R↓ with a non-ray field (a fixed extra field on another site) | 2-site φ⁴: a = −2, b = 1, J = 3, h_1 = 0.5, H = 0.01; relative derivative +0.26 |
| local or termwise Ising versions E1, E2, E3, P | exact enumeration, up to +50 |
| IC with c varying on B, or with a fixed extra field added | +0.31, +1.07 |
| pointwise Holley lemmas L1, L2 (r-representation) | correlations down to −0.77 and −0.20 |
| Ψ↓ (pointwise), even at J = 0 | a = −4, b = 1, N = 2: Ψ = 1.98, 0.29, −0.25, 0.14, 0.47, …; a = −2 also fails |
| Ψ↓ for finite Ising GS blocks (parity) | block size 2: 2.21, 0.57, 1.33, 0 |
| image-kernel TP2 for every log-concave s | e^{−z⁴}: −0.16 at u = q = 0.1 |
| convexity of the full action in the T2b regime | Hessian on the constant mode = ε²μ_bare < 0 |

## Hypotheses actually needed
- 0-d: EMN.
- Theorem 7.1: even weight, translation invariance, uniform field.
- Route 4 (conditioning on t): quartic V (so that the t-dependence is 3b q²t²) plus (A) and (B).
- Lee–Yang alone is useless. Field homogeneity (ray from the symmetric point) is essential.
- Perturbative small-λ results do not help T2b, because λ/|μ| = O(1).

## Recommended next step
Attack (B) first. It is a single-correlation statement, holds on 3 sites, and its homogeneous y = 0 case is close to GHS via the EOM. A proof of (B) could come from Ellis–Monroe–Newman-type duplication of the q-system with the source q_0. In parallel, test (A) on 3–4 sites, by Monte Carlo or with GS blocks.

## Round 6: attack on (B)
Statement (B): in the q-system, which is ferromagnetic with EMN site weights e^{−V_x}, site-dependent masses and uniform h, the map h ↦ ⟨q_0 q_y²⟩/⟨q_0⟩ is nondecreasing for every y.

**Observation (PROVED, logic only).** (B) is the case F = q_y² (increasing in |q|) of conjecture GC: ⟨q_0F⟩/⟨q_0⟩ is monotone in h, with the opposite direction to the monotonicity of F. The target itself is GC with F = G (decreasing). So route 4 trades GC for one specific decreasing F against GC for the polynomials q_y², plus (A).

**PROVED special cases**
1. **J = 0**, any even site weights and any masses.
   - y ≠ 0: the sites are independent, so the ratio is ⟨q_y²⟩, and ∂_h⟨q_y²⟩ = ⟨q_y;q_y²⟩ ≥ 0.
   - y = 0: ⟨q³⟩/⟨q⟩ = ∫_0^∞ q² dπ_h with π_h ∝ q·sinh(hq)·e^{−V}; this is MLR-increasing in h. **No EMN is needed.**
2. **Translation-invariant quartic, y = 0.** The EOM gives 2a m + 4b′⟨q_0³⟩ = h + 2dJ m. So ⟨q_0³⟩/m = (h/m + 2dJ − 2a)/(4b′), and h/m is nondecreasing by GHS (m concave, m(0) = 0).

**Not proved: inhomogeneous masses with J > 0, the case route 4 needs.**
- **EOM handle, y = 0.** (B) ⟺ ⟨ξ_0⟩/⟨q_0⟩ nondecreasing, where ξ_0 = h + JΣ_{z∼0}q_z is the local field.
  - Conditioning on the neighbours gives ⟨q_0^k⟩ = E[ψ_k(ξ_0)], where ψ_k are the 0-d moment functions and ψ_3/ψ_1 is increasing in |ξ| by item 1.
  - But the law of ξ_0 moves with h in a way that is not MLR-controlled.
- **Duplication.** (B) ⟺ E[(α_0² − β_0²)·α_y β_y·B] ≥ 0. Here α = (q+q′)/√2, β = (q−q′)/√2, B = Σβ_x, and the field acts on α only.
  - Ginibre gives ⟨α^m β^n⟩ ≥ 0 for every monomial, but the factor α_0² − β_0² = 2q_0q′_0 carries a negative monomial.
  - Conditioning on α leaves a factor of indefinite sign: α_y(α_0²E[β_yB|α] − E[β_0²β_yB|α]).
- **Cumulant form.** (B) ⟺ Σ_x[m u4(0yyx) + 2m u2(0y)u2(yx) + 2m m_y u3(0yx) + m² u3(yyx) + 2m²m_y u2(yx)] − χ_0[u3(0yy) + 2m_y u2(0y)] ≥ 0.
  - GKS (u2 ≥ 0) and GHS (u3 ≤ 0) sign some terms, but there are terms of both signs, and the sign of u4 in a field is uncontrolled. So **(B) is not a consequence of GKS, GHS or Lebowitz.**

**Ising analogues FAIL** (isingB.py, isingB2.py; exact enumeration, n ≤ 11, uniform field):
- ⟨σ_kσ_iσ_j⟩/⟨σ_k⟩ with k, i, j distinct: relative derivative −2.06.
- The block form ⟨M_{B0}M_{By}²⟩/⟨M_{B0}⟩ for arbitrary sets B0, By (B0 a single spin): −0.49.
- So, as for Ψ, any proof must use continuity of the φ⁴ single-site law. A proof that works for all Ising graphs is impossible.

**Robustness of (B) for φ⁴ (all numerically confirmed).**
- Deep wells: a_0, a_1 ∈ {−6, −4, −2, 0} (and a_1 = 3), b = 1, J ∈ {0.02, 0.1, 0.5}: minimum relative derivative +5·10⁻⁴ (condtB2.py).
- Earlier runs: 2 sites (condt.py) and 3-site rings (condtB3.py) with random inhomogeneous masses — no violation.

**In the T2b regime the given-t masses are a + 3bt_x² ≥ a ≈ 2 > 0**: single-well and log-concave. So it would suffice to prove (B) for log-concave quartic sites; that case is open too.

**Suggested next idea.** Prove (B) by the Theorem-7.1 / sinh device applied to the pair (q_0, ξ_0): the field enters ξ_0 linearly with coefficient 1. Alternatively, use a 0-d conditional representation of the form E_h[ψ_3(ξ)]/E_h[ψ_1(ξ)], and look for a kernel in which h and ξ are TP2.

## FINAL STATUS (round 7)
**Teammate numerics** (/home/claude/t2b/abtest, converged to 1e-12):
- **(A) is FALSE** on a 3-site path 1–0–2 with homogeneous masses: a ≈ 2, b = 0.162, J ≈ 0.7–1.0, h = 0.031, margin −3.2%. So π_h is not MTP2, and the FKG closure of route 4 is dead.
- (B) fails only rarely and slightly (−2.3e-3) at a neighbour y with a double-well mass. (B) at y = 0 held in all 4500 cases.

**My check (condtB3pos.py).** On the 3-site path with all masses a_x ∈ [1.9, 8] (the T2b-type regime, since a_x = a + 3bt_x² ≥ a), b ∈ {0.05, 0.16, 0.5, 1}, J ∈ [0.3, 1.2]: (B) holds, with minimum relative derivative +8·10⁻⁴. But (B) no longer suffices, because (A) fails.

**Does (B) at y = 0, plus something else, suffice?**
Route 4 now has to be used only through the single covariance Cov_{π_h}(t_0², Φ) ≤ 0.
- (B) gives Φ decreasing in each |t_y|. Without positive association of π_h, a decreasing Φ and an increasing t_0² do not force a negative covariance.
- The y = 0 part alone controls only the dependence of Φ on |t_0|. Conditioning on t_{≠0} would need the conditional law of |t_0| to be MLR in a direction compatible with Φ, and the weight N(t,h) couples |t_0| to the rest. No closure was found.
- **Verdict: no proof.**

### What is PROVED
1. 0-d: R nonincreasing for the whole EMN class (zerod_proof.md).
2. Lattice identities:
   - R = 2⟨t_0²q_0⟩/⟨q_0⟩.
   - G_x = E[t_x²|q] is decreasing in |q| (EMN class).
   - Theorem 7.1: on the torus, Ψ↓ at zero field implies R↓.
   - Conditioning-on-t identity: ∂_h(R/2) = Cov_{π_h}(t_0², Φ).
3. Special cases of (B): J = 0 (any even weight), and translation-invariant quartic at y = 0 (EOM plus GHS).
4. Equivalences: (★)/(★★), C = 8 ⟺ R↓; the cumulant form; the random-current form IC ⟺ ⟨K⟩_𝒩 ≤ ⟨K⟩_𝒟.

### The exact OPEN statement
**Lattice lemma.** Lattice φ⁴ on a torus, single-site a > 0 (T2b: a = 2⁻, b = λε², J = 1, d = 2), uniform field H > 0: R(H) = ⟨φ_0;φ_0²⟩/⟨φ_0⟩ is nonincreasing. Equivalently: m Σ_x u4(000x) + 2m² Σ_x u3(00x) ≤ χ u3(000).

Sufficient, numerically supported in this regime (not proved), each enough on its own:
- (i) Ψ↓ (Theorem 7.1).
- (ii) Cov_{π_h}(t_0², Φ) ≤ 0 directly.
- (iii) GC with F = G.

### Counterexamples (all verified)
- LY1: x²e^{−x²/2}, exact.
- One-variable GHS alone is not enough: c = 10, 15.
- Fields that are not uniform rays break the statement (2-site, +0.26).
- Local and termwise Ising versions fail; Holley lemmas L1/L2 fail.
- Pointwise Ψ↓ fails at J = 0 for deep wells (a = −4).
- Finite Ising GS blocks: Ψ is not monotone (parity).
- Image-kernel TP2 fails for flat-bottomed log-concave s.
- The full action is non-convex in the T2b regime.
- The Ising analogues of (B) fail.
- **(A) fails** (3 sites, homogeneous, a ≈ 2).
- (B) fails slightly with double-well neighbours.

### Most promising next idea
Prove (i), Ψ↓, in the single-well / strong-coupling regime. This is the only remaining sufficient statement with no known counterexample in the T2b regime, and it is a zero-field statement.
- Concrete plan: write Ψ(u) − Ψ(u′) through the conditional law given Q of the t-field and of |q|. Then use the zero-mode decomposition q = (u/N)·1 + q^⊥: given Q = u, the variable u enters only as a shift of the constant mode inside W.
- For a > 0, the derivative ∂_u of the conditional measure then becomes an explicit covariance with Σ_x ∂_qW(q_x,t_x). Its sign might be controllable by GKS II in the (q^⊥, t) system, where the shift acts like a uniform field.
- Untested idea.

## Round 8: Q = u conditioning with q = (u/N)·1 + p, Σp = 0 (zero field, torus)
Coupling. For a regular graph, Σ_{⟨xy⟩}q_xq_y = const(u) + Σ_{⟨xy⟩}p_xp_y; the cross term deg·(u/N)Σp vanishes. So the conditioned law of (p,t) is
  ∝ δ(Σp) · exp(−Σ_x W(u/N + p_x, t_x) + JΣ(p_xp_y + t_xt_y)),
and Ψ(u) = T1(u) + T2(u), with T1 = N⁻¹E_u[Σt_x²] and T2 = E_u[Σp_x t_x²]/u.

### Structural check: is (p,t) a ferromagnetic GKS system? NO, for two reasons
1. **The constraint is antiferromagnetic.** δ(Σp) is the infinite-coupling limit of e^{−K(Σp)²}, which has negative off-diagonal couplings. On 2 sites it forces p_1 = −p_0, i.e. perfect anticorrelation.
2. **The shift is not a field.** W(u/N + p, t) is not even in p. Its u-dependence is nonlinear: ∂_uΣW = N⁻¹Σ_x(2aq_x + 2bq_x³ + 6bq_xt_x²), which is cubic in p and contains p·t². So the shift cannot be written as a uniform linear field on an even system, and neither GKS II nor Ginibre applies.

Removing the constraint by a Laplace transform in u just reproduces the field-H system, i.e. Theorem 7.1 read backwards. That is circular.

### Numerics (hyper2.py, 2 sites, exact 3-d grid 111³ in (v, t0, t1))
Parameters: (a,b,J) ∈ {(2,0.2,1), (2,1,1), (1,1,0.5), (0.5,1,1.5), (2,0.05,1.9), (3,1,0.3)}, u ∈ [0.2, 5].
- T1 is **decreasing** in every case.
- T2 is **≤ 0** in every case (range −0.07 to −1e-4), but **not monotone**.
- Ψ = T1 + T2 is decreasing in every case.

A proof would therefore need T1' + T2' ≤ 0 as a combined estimate: T2 ≤ 0 alone is not enough. Candidate sub-lemmas, unproved and numerically true on 2 sites only:
- (C1) "conditional on Q, the t-fluctuation decreases": T1 = N⁻¹E[Σt_x² | Q = u] is decreasing.
- (C2) |T2'| ≤ |T1'|.

### Outcome
The proposed proof does not close: the (q^⊥, t) system is not ferromagnetic, so GKS gives no sign. The lattice lemma remains OPEN.

The most concrete remaining target is (C1), a zero-field "conditional-on-total-magnetization" monotonicity for t². Natural tools to try next:
- a coupling or monotone-transport argument in u for the hyperplane measure (Caffarelli-type contraction needs convexity, which fails here);
- a GS/Curie–Weiss block approximation in which conditioning on the total block magnetization is explicit.

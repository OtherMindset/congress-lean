# PROOF.md — non-Gaussianity of the torus magnetisation (26 Nov 2026)

Labels: PROVED (full argument here) / CN (checked numerically, script named) / HEUR / CNR (cited, not read).
None of the results below proves the target NG := liminf_L ∫_W |B_L| dμ > 0 (ε → 0 first).
They are (A) an exact walk formula for B_L, (B) a necessary condition, (C) Lee–Yang facts (strictness at
fixed L, and an exact "first zero" reformulation), (D) reductions of the target. The verdict
(NOTES.md §0) is that NG is a separate hard problem: finite-size hyperscaling for φ⁴₂.

## 0. Setting
Lattice units as in fable/PROOF.md §0: torus Λ, N sites, J = 1 nearest neighbour, site weight e^{−aφ²−bφ⁴},
zero field; M = Σφ_x, X = ⟨M²⟩ = Nχ, B = κ4(M)/κ2(M)² ∈ [−2, 0].
Continuum dictionary: b = λε², N = (L/ε)², χ_cont = ε²χ, M_cont = ε²M, so
  b χ²/N = λ χ_L²/L² = λ L² M_L⁴   (χ_L = L² M_L²).   (0.1)
BFS walk representation (CNR as a theorem: [BFS82], [FFS92 ch. 9–11]; same input as fable/PROOF.md Thm 3,
cross-checked in fable_check/REPORT.md item 4): with g(s) = e^{−2as−4bs²} and
Z(t) = ∫ Π_x g(φ_x²/2 + t_x) e^{Σ_{⟨xy⟩}φ_xφ_y} dφ, Z = Z(0),
  ⟨φ_xφ_y⟩ = ∫dW_{xy}(ω) Z(t_ω)/Z,   ⟨φ_1φ_2φ_3φ_4⟩ = Σ_{3 pairings} ∫∫dW dW′ Z(t+t′)/Z.   (0.2)
Expectation with weights g(φ_x²/2 + t_x) is the model with masses a + 4b t_x (Fable Thm 3).
CN (scripts/check.py, one site, 4 parameter sets incl. deep wells): both formulas in (0.2) to 8 digits.

## A. Exact walk formula for the Binder cumulant. PROVED (given (0.2))
Let ŵ be the probability measure on walks ∝ Σ_{x,y} dW_{xy}(ω) Z(t_ω)/Z (total mass X), ω, ω′ i.i.d. ~ ŵ,
t = t_ω, t′ = t_ω′. Then
  |B| = 3 E[1 − e^{−D(t,t′)}],  D = 8b t·t′ − Γ(t,t′),   (A.1)
  Γ(t,t′) = 16b² ∫_0^1∫_0^1 Σ_{x,y} t_x t′_y ⟨φ_x²; φ_y²⟩_{σt+τt′} dσ dτ ≥ 0,   (A.2)
where ⟨·⟩_s is the model with masses a + 4b s. D can have either sign (t·t′ = 0 and D = −Γ ≤ 0 for walks with disjoint
supports); Lebowitz says only that the average in (A.1) is ≥ 0.

Proof. Sum (0.2) over x_1..x_4: ⟨M⁴⟩ = 3 ∫∫ Z(t+t′)/Z = 3X² E[R], R := Z(t+t′)Z/(Z(t)Z(t′)), and
X² = ∫∫Z(t)Z(t′)/Z². So κ4 = ⟨M⁴⟩ − 3X² = −3X² E[1 − R], B = κ4/X² = −3E[1−R].
Let Φ = log Z(·). log g(φ²/2 + t) = −aφ² − 2at − b(φ² + 2t)², so ∂_{t_x} log g = −2a − 4b(φ_x² + 2t_x),
∂²_{t_x} log g = −8b, and ∂_{t_x}∂_{t_y}Φ(s) = 16b²⟨φ_x²;φ_y²⟩_s − 8b δ_{xy}.
log R = Φ(t+t′) − Φ(t) − Φ(t′) + Φ(0) = ∫∫ Σ t_x t′_y ∂_x∂_yΦ(σt+τt′) dσdτ = −8b t·t′ + Γ.
Γ ≥ 0 because ⟨φ_x²;φ_y²⟩_s ≥ 0 for every mass field (GKS II for even observables [Gin70], CNR). ∎

Reading: B is the ŵ⊗ŵ-average of "direct contact interaction 8b t·t′ minus energy-mediated attraction Γ".
NG ⟺ the direct contact is not screened by the energy–energy correlation, at the torus scale, with ŵ⊗ŵ-
probability bounded below. In the continuum 8b t·t′ → 8λ∫ℓℓ′ (intersection local time, finite in d = 2),
Γ → 16λ²∫∫ℓ(x)ℓ′(y)⟨:φ²_x:;:φ²_y:⟩. This is the named lemma (NS) of §D.

## B. Tree bound and the necessary condition. PROVED (given (0.2), GKS)
  |B| ≤ 24 b χ²/N,  i.e. (continuum) |B_L| ≤ 24 λ χ_L²/L² = 24 λ L² M_L⁴.   (B.1)
Proof. 1 − e^{−D} ≤ D ≤ 8b t·t′ and Γ ≥ 0, so |B| ≤ 24b Σ_z E[t_z]². By the walk-splitting identity and GKS
mass monotonicity (Fable Thm 3 (3.3)): X·E|t| = Σ_z Σ_{x}∫dW_{xz}Z(t_1)/Z · ⟨φ_z M⟩_{a+4bt_1} ≤ Nχ², so
E|t| ≤ χ and, by translation invariance, E t_z = E|t|/N ≤ χ/N. Hence |B| ≤ 24bN(χ/N)² = 24bχ²/N. ∎
(Equivalently: sum the tree bound u4 ≥ −24bΣ_zΠS(x_i,z) [BFS83 (1.3); Lean `tree_bound_box` for the box].)
Consequences (PROVED):
 (B.2) g_L := |B_L| = −ū4/(χ_L² L²), ū4 = ∫u4(0,x2,x3,x4), is exactly the renormalised coupling with the
       torus size L as length scale. NG is a finite-size hyperscaling statement.
 (B.3) |B_L(μ)| ≥ c forces χ_L(μ) ≥ L·(c/24λ)^{1/2}, i.e. M_L² ≥ (c/24λ)^{1/2}/L. So NG on W implies
       linear growth χ_L ≳ L on a set of positive measure in W ("η ≤ 1"); it is strictly stronger than
       sup_L χ_L = ∞ and cannot follow from the definition of μ_c (any divergence slower than L is
       compatible with χ_L → ∞ and forces B_L → 0).
 (B.4) Skeleton bounds of the form |κ4| ≥ 24λL²χ_L⁴(1 − Cλ·Bub_L), Bub_L = ∫_{T_L}S(0,z)²dz, can never certify
       |B_L| > 6/C: by Cauchy–Schwarz Bub_L ≥ χ_L²/L², so λBub_L ≥ g0 := λχ_L²/L², and the bound reads
       |B_L| ≥ 24g0(1 − Cλ Bub_L) ≤ 24g0(1 − Cg0) ≤ 6/C. (Form of the skeleton bound: CNR, [BFS83 (1.4)].)
CN (scripts/check.py): (B.1) on all 90 Binder scan points of mc_eps/binder (b = 0.08…0.00125, L = 16…256):
max(|B| − 2σ)/bound = 0.47; in the disordered regime the ratio is 0.2–0.8 (bound is fairly sharp there).

## C. Lee–Yang structure. PROVED given Lee–Yang for φ⁴ (CNR: [SG73], Newman CMP 41 (1975))
Z(h) := ⟨e^{hM}⟩ (zero-field measure), entire in h, even, Z(0) = 1.
 Growth: |Z(h)| ≤ Z(Re h) and Σ_{⟨xy⟩}φ_xφ_y ≤ 2Σφ_x², so log Z(h) ≤ C_N(1 + |Re h|^{4/3}) (per-site sup of
 (2−a)φ² − bφ⁴/2 + xφ, keeping e^{−bφ⁴/2} for integrability); order ≤ 4/3 < 2. Lee–Yang: all zeros on iℝ.
 Hadamard (genus ≤ 1, evenness, Z(0)=1): Z(h) = Π_j (1 + h²/α_j²), Σα_j^{−2} < ∞.   (C.1)
 Cumulants: κ2 = 2Σα_j^{−2}, κ4 = −12Σα_j^{−4}. With w_j = α_j^{−2}/Σ_kα_k^{−2}:
   B = −3 Σ_j w_j²,   3 w_1² ≤ |B| ≤ 3 w_1  (α_1 the zero nearest 0).   (C.2)
 (C.3) Strict negativity at every finite (ε, L, μ): κ2 > 0 ⇒ some zero exists ⇒ B < 0. (This settles the
       Round-11 remark "strict negativity still needs the upper skeleton bound" for the zero mode at fixed
       cutoff: it does not. Uniformity is the real issue.)
 (C.4) NG ⟺ the first Lee–Yang zero carries a fixed fraction of κ2: |B_L| ≥ c ⟹ α_1²κ2 ≤ 6/c, and
       α_1²κ2 ≤ K ⟹ |B_L| ≥ 12/K². (κ2 = L²χ_L in continuum units.) Ordered check: cosh-type zeros
       α_k = (k−½)π/(M⁺L²) give |B| = 3·(π⁴/6)/(π²/2)² = 2.
 (C.5) Fixed L, ε → 0 (PROVED modulo inputs): if log Z_{ε,L}(x) converges for real x (I2) then, Z_{ε,L} being a
       normal family on ℂ (|Z(h)| ≤ Z(Re h), convex pointwise-convergent functions are locally bounded),
       Z_{ε,L} → Z_L locally uniformly, Hurwitz puts the zeros of Z_L on iℝ, and cumulants converge. If in
       addition the continuum torus theory satisfies a growth bound log Z_L(x) ≤ C_L(1 + |x|^p), p < 2
       (input (G); for P(φ)₂ the OS1-type bound with p = 4/3 is CNR/HEUR, Glimm–Jaffe §12, Fröhlich 1974),
       then (C.1)–(C.3) hold for the continuum torus: B_L(μ) < 0 for every L and μ. Non-uniform in L.
 Side remark for target T1 (PROVED, elementary): if a limit point has, for some f ≥ 0, a nondegenerate law of
 φ(f) with E e^{xφ(f)} ≤ exp(C(1 + |x|^p)), p < 2 (inherited from a cutoff-uniform bound by Fatou), the limit
 point is non-Gaussian (a Gaussian of variance v > 0 has log MGF = vx²/2). Nondegeneracy follows from a
 Bogoliubov lower bound Var φ(f) ≥ ‖f‖⁴/⟨(f, Hess S f)⟩ given ⟨:φ²:⟩ bounded above. So T1's non-Gaussianity
 reduces to a uniform sub-Gaussian-order MGF bound (G), not to the skeleton inequality. (G) itself NOT proved here.

## D. Reductions of NG. PROVED
 (D.1) Only a sequence is needed: Prop 7.3 and the dichotomy use one sequence L_j → ∞ along which
       χ_{L_j}(μ_+) → ∞; so NG may be weakened to limsup_L ∫_W|B_L| > 0 along such a sequence (with (P0)
       holding on it).
 (D.2) Placement: since M_L²(μ) ≥ K^{−1}∫_μ^{μ_+}|B_L|, order at μ needs non-Gaussianity on [μ, μ_+] with
       μ_+ < μ_c arbitrary; deep-ordered information (|μ| ≫ λ, Glimm–Jaffe–Spencer regime, CNR) sits below μ
       and does not enter. NG is needed in every left neighbourhood of every μ_+ < μ_c.
 (D.3) Monotone version: IF |B_L| is nonincreasing in μ (Mon: PROVED on one site, fable/PROOF.md Thm 2b;
       CN on 2D tori, all scans in mc_eps/binder and fable/mc2d), then ∫_μ^{μ_+}|B_L| ≥ (μ_+ − μ)|B_L(μ_+)|,
       and NG reduces to the pointwise statement
         (NG_pt)  for every μ′ < μ_c: limsup_L |B_L(μ′)| > 0 (along the sequence of D.1).
       Without (Mon): by Fatou, liminf_j ∫_W|B_{L_j}| ≥ ∫_W liminf_j|B_{L_j}|, so it suffices that
       liminf_j |B_{L_j}(μ′)| > 0 on a subset of W of positive measure (a limsup per point is not enough).
 (D.4) Exact form (from fable/NOTES.md (1.1), CN there): ∫_W|B_L| = 24λ[M_L²(μ_−) − M_L²(μ_+)] +
       12λL^{−2}∫_W ∂_h²R(0)dμ. NG is equivalent to an O(1) drop of M_L² across W up to the R″ term —
       circular with (P0) (FAILED.md F6).
 (D.5) Named lemma (NS, "no complete screening"), equivalent to NG by (A.1): there are c > 0 and a sequence
       L_j such that, uniformly in ε < ε_0(L_j), ∫_W E_{ŵ⊗ŵ}[1 − e^{−(8b t·t′ − Γ(t,t′))}] dμ ≥ c.
       At weak coupling (λ·Bub small) Γ is second order and NS is the BFS skeleton bound; in W it is
       non-perturbative.

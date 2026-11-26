# Convex / Helffer–Sjöstrand route to ∂_H R ≤ 0: assessment (lift seat)

## 1. The premise fails: small-ε lattice φ⁴₂ is NOT log-concave (checked)

Notes' weight: exp(Σ_{⟨xy⟩}φ_xφ_y + ε²hΣφ − Σ(aφ_x² + bφ_x⁴)). So

  V = Σ_x(aφ_x² + bφ_x⁴) − ½φ·Adj·φ,   Hess V = 2a·I − Adj + 12b·diag(φ_x²).

On the torus, Adj has top eigenvalue 4, attained by the constant vector. At φ = 0, along the zero mode,

  min spec Hess V = 2a − 4 = ε²μ_bare = ε²(μ − 12λc_ε) < 0   for every μ < 12λc_ε.

- a = 2 + ½ε²μ − 6λε²c_ε, so **a → 2 from BELOW**.
- Convexity (a ≥ 2) ⟺ μ ≥ 12λc_ε → ∞. That is the trivially disordered region, irrelevant to T2b.
- No split helps. With A = −Δ ≥ 0, the on-site part is U(φ) = (a−2)φ² + bφ⁴, a shallow double well. No decomposition can be convex, because the full Hessian has a negative direction.

In continuum units, Hess = −Δ + μ − 12λc_ε + 12λφ_x² = −Δ + μ + 12λ:φ_x²:.
- It is "convex on Wick-average": E:φ²: = O(1).
- It is not convex pointwise: φ_x² − c_ε fluctuates at the UV scale, with a negative part of size 12λc_ε.
- Single-site weights e^{−aφ²−bφ⁴} are log-concave (a > 0), but the coupling Σφ_xφ_y is not compensated.

Second obstruction (regime). The lemma is needed along ABF characteristics, i.e. for **μ < μ_c** (ordered side) with h > 0 small. There the measure is a field-tilted two-phase system:
- the large-scale effective potential is a tilted double well, nonconvex at every scale;
- B–D's uniform LSI is proved only for μ > μ_c^χ.

So no argument that needs Hess V ≥ 0 pointwise can cover the region T2b needs. That rules out maximum principles for the Witten Laplacian L⁽¹⁾ = L + Hess V, Brascamp–Lieb, and HS-based GHS proofs. The same holds for approximate versions with Hess V ≥ −δ, since δ·(inverse gap) is not small there.

## 2. Audit refinement obtained on the way (useful whatever route proves the lemma)

The lemma is **not** needed in the torus tunnelling regime (hL²m ≲ 1).
- `abf_Char` characteristics from (μ₀, h₁) only visit h ≥ h₁.
- If the lemma holds on Λ_{ε,L} for h ≥ h_min(L), with h_min(L) → 0 as L → ∞, then a localised `abf_Char` (start points h₁ ≥ h_min(L)) holds for each L.
- That passes to the L → ∞ limit for every h₁ > 0, by the pointwise-limit argument of `abf_char_of_tendsto`. The per-ε (infinite-volume) form of A3 then applies, with the starting point taken in infinite volume, where χ(μ₀, 0⁺) = ∞ for μ₀ < μ_c^♯ along ε_j.

So "lemma on tori, uniformly in ε, for h ≥ h_min(L) → 0" suffices. Required work: localising `abf_Char` (easy, not in Lean). It does not remove the nonconvexity of §1.

## 3. What HS does give, formally (valid whenever L⁽¹⁾ is invertible, no convexity needed)

Let u := (L⁽¹⁾)⁻¹𝟙 and v := (L⁽¹⁾)⁻¹e₀. These are vector fields. Then:
- χ = E[u₀] and ∂_H E F = E[∇F·u];
- G₀₀ = E[v₀] and κ₃(φ₀) = 2E[(φ₀ − m)v₀].

Hence

  ∂_H R = 2E[∇v₀·u] + ∂_H(κ₃/m),

and ∂_H κ₃ involves E[∇((φ₀−m)v₀)·u] plus the H-derivative of v through L⁽¹⁾. The sign of each piece in the GHS-type proofs comes from monotonicity of v and u, which is a maximum principle needing Hess V ≥ 0. This is exactly what §1 removes.

One-site check:
- In 0-d with U'' nondecreasing on [0, ∞) and U convex, the same expressions reduce to the 0-d theorem's quantities (κ₃ ≤ 0 etc.).
- But the 0-d proof (duplication + MLR) covers the whole EMN class, including double wells, and it is not an HS proof.
- **So the 0-d theorem is in fact evidence that convexity is the wrong hypothesis.** The 0-d statement holds for nonconvex EMN potentials. The obstruction to the lattice lift is the lattice structure, not convexity.
- It also cuts against the teammate's finding that Ψ fails for deep double wells. Ψ-monotonicity is a sufficient condition, stronger than R↓, so its failure for deep wells does not imply that R↓ fails there.

## 4. ε-uniform K version
K > 0 does not change §1: the nonconvexity is in the measure, not in the inequality. Any HS bound would carry a constant depending on the inverse spectral gap of L⁽¹⁾ in the ordered phase, which is not uniform near μ_c.

## 5. Recommendation
- Drop the convex/HS route for T2b as posed. It can only prove the lemma for μ ≥ 12λc_ε.
- If a convexity-based tool is wanted, it has to be post-renormalisation: Polchinski/BBD flow to scale ℓ ≫ ε. But the lemma is an on-site (scale-ε) statement, and (★) is intrinsically on-site, so it does not commute with the flow. I see no way around this.
- For the teammate's Ψ/Efron work: the "a ≥ 2" regime should not be used as evidence for T2b. Tests should use a = 2 + ½ε²μ − 6λε²c_ε < 2, on tori large enough that c_ε is realised, with μ < μ_c.
- The productive lines remain:
  1. the zero-field Ψ(u) monotonicity on the EMN class without convexity, conditioned on Q;
  2. the random-current quantitative domination (SWITCHING.md §6).

  Both are insensitive to convexity, as the 0-d theorem is.

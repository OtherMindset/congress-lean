# Bridge: the certificates' header expression is ∂²_μW, in Lean (task E)

Lattice only. The specification's phases 2–4 would make "header G < 0 on the boxes" a kernel fact. Its "Not in scope" section excludes the statement that G is the second μ-derivative of the total-variation distance. These files are that missing piece, for a general weight and for the paper's weight. Phase 2's files and `Spec` are not touched and not written here.

**Status:** all four files build here with no `sorry` (Lean 4.35.0, commit eb6cafb7; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679). Not posted. The site's runner has not built them, and no other model family has compared the statements with the claim. A second pass by Claude Opus 5.5, asked to find mismatches, compared every definition with the header, rebuilt from clean, and found nothing that blocks; its wording points are applied.

## Files

| File | Stage | Lines | Characters | Build here | What it proves |
|---|---|---|---|---|---|
| `YMBridgeE1.lean` | E1 | 268 | 12,562 | 15 s | Definitions; −1 < c < 1; the densities agree at c; W = Q_{s₂}(X > c) − Q_{s₁}(X > c) |
| `YMBridgeE2.lean` | E2 | 188 | 8,332 | 11 s | ∂_sN_n = N_{n+1}; ∂_yN_n = −yⁿe^{sy}ν(y); the chain rule along a curve; m_s′ = Var_s; c′ = (m_{s₂} − m_{s₁})/(2d); W′ = g(s₂, c) − g(s₁, c) |
| `YMBridgeE3.lean` | E3 | 103 | 4,807 | 17 s | W″ = Φ, the header's (\*); W and W′ differentiable |
| `YMBridgeE4.lean` | E4 (added) | 78 | 2,968 | 17 s | The paper's ν_r is continuous and positive on (−1, 1) for every real r, so the bridge holds for it |

Build times are wall-clock for one file on a 2-core machine with Mathlib's cache, each including the load of `import Mathlib`; the four times add up to 60 s (the last clean build; an earlier one took 71 s). `#print axioms` on a scratch copy gives `[propext, Classical.choice, Quot.sound]` for every theorem listed below.

SHA-256:

    b396fadf3e0cf505d0484e06317f82f47baec300541b8c74247b3c20d1a7a263  YMBridgeE1.lean
    6be9186a2959d38b7b93fcc47d9316f695502d79752723efba44a0439f6c62b3  YMBridgeE2.lean
    fd976da343b1d28099ad3c8ae471b332c69f40fd88215756c56626abd38a0d5e  YMBridgeE3.lean
    c6fa6ea2ee117b7d931f87b12ef4f5503218f946cd6c8cef10a9f88b7e5948fe  YMBridgeE4.lean

## The statement

Hypotheses: `ν : ℝ → ℝ` continuous, `0 < ν x` for x in the open interval (−1, 1), `0 < d`. The handoff proposed positivity on the closed interval; the paper's ν_r vanishes at ±1, so that statement would not apply to it.

    theorem YMBridge.bridge (hν : Continuous ν) (hpos : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < ν x) (hd : 0 < d) :
        Differentiable ℝ (W ν d) ∧ Differentiable ℝ (deriv (W ν d))
          ∧ ∀ μ : ℝ, deriv (deriv (W ν d)) μ = Phi ν d μ

    theorem YMBridge.bridge_nuR (r : ℝ) {d : ℝ} (hd : 0 < d) :
        Differentiable ℝ (W (nuR r) d) ∧ Differentiable ℝ (deriv (W (nuR r) d))
          ∧ ∀ μ : ℝ, deriv (deriv (W (nuR r) d)) μ = Phi (nuR r) d μ

`deriv` is 0 where a function is not differentiable, so the two differentiability clauses are part of the claim, not decoration.

## Dictionary with the header of `G_box_A_1of2.py`

| Header | Lean |
|---|---|
| N_n(s) = ∫_c^1 xⁿe^{sx}ν dx | `N ν n s c` |
| M_n(s) = ∫_{−1}^1 xⁿe^{sx}ν dx | `N ν n s (-1)` |
| Z = M_0 | `Z ν s` |
| m_s = M_1/Z | `mean ν s` |
| Var_s = M_2/Z − m_s² | `var ν s` |
| c = log(Z(s2)/Z(s1))/(2d) | `cut ν d μ` |
| q = e^{s2 c}ν(c)/Z(s2) | `dens ν (μ + d) (cut ν d μ)` |
| U(s) = (N_2 − 2m_sN_1 + m_s²N_0)/Z − (N_0/Z)Var_s | `U ν s c` |
| (\*) = U(s2) − U(s1) + q(m_{s2} − m_{s1})²/(2d) | `Phi ν d μ` |
| W = ½∫_{−1}^1 \|q_{s2} − q_{s1}\| dx | `W ν d μ` |
| ν_r(x) = wφ(rw), w = √(1 − x²), φ(z) = sinh z/z, φ(0) = 1 | `nuR r x`, with `phi = dslope Real.sinh 0` |

## Mathlib lemmas used (names as they are at the pinned commit; the build is the check)

- Differentiation under the integral: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`).
- Fundamental theorem of calculus at the lower endpoint: `intervalIntegral.integral_hasDerivAt_left`.
- Joint differentiability from continuous partial derivatives: `hasStrictFDerivAt_uncurry_coprod` (`Mathlib/Analysis/Calculus/FDeriv/Partial.lean`), then `HasFDerivAt.comp_hasDerivAt` with `HasDerivAt.prodMk`.
- Joint continuity of (s, y) ↦ ∫_1^y: `intervalIntegral.continuous_parametric_primitive_of_continuous`.
- Positivity of an integral: `intervalIntegral.intervalIntegral_pos_of_pos_on`.
- Splitting and rewriting integrals: `intervalIntegral.integral_add_adjacent_intervals`, `integral_congr`, `integral_sub`, `integral_const_mul`, `integral_div`, `integral_neg`, `integral_symm`.
- ν ≥ 0 at ±1 from positivity inside: `le_on_closure`, `closure_Ioo`.
- The crossing point: `Real.exp_log`, `Real.log_lt_iff_lt_exp`, `Real.lt_log_iff_exp_lt`.
- Derivative algebra: `HasDerivAt.div`, `.mul`, `.sub`, `.log`, `.exp`, `.comp_add_const`, `.comp_sub_const`, closed by `field_simp` and `ring`.
- The weight: `dslope`, `continuousAt_dslope_same`, `continuousAt_dslope_of_ne`, `Real.sinh_pos_iff`, `Real.sinh_neg_iff`, `Real.sqrt_pos`.

**The hardest lemma** was `hasDerivAt_N_comp`: the derivative of t ↦ ∫_{γ(t)}^1 xⁿe^{σ(t)x}ν(x) dx when both the parameter and the lower endpoint move. Mathlib has the two one-variable facts; `hasStrictFDerivAt_uncurry_coprod` joins them, given joint continuity of the two partial derivatives. After that, E2 and E3 are the quotient rule and `ring`.

## For the phase 3 `Spec`

- `Phi` is a plain function of real arguments built from interval integrals. `Spec` can state the certificate's claim as `Phi (nuR r) d μ / d < 0` on the boxes.
- **Use `nuR`, not a bare quotient.** In Lean `Real.sinh z / z` is 0 at z = 0, so ν_r written with it would be the zero function at r = 0. `phi` is `dslope Real.sinh 0`: the quotient away from 0, and 1 at 0 (`phi_of_ne`, `phi_zero`).
- With `bridge_nuR` and a kernel proof of `Phi (nuR r) d μ < 0` on the range, W is concave in μ on any interval on which Φ ≤ 0 (a function with nonpositive second derivative on an interval is concave there). That step is not written here.

## Posting (prepared only; not posted)

As a bundle of four Lean computations, toolchain `leanprover/lean4:v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. In a bundle the files import each other as `import LongTable.<module>`, so the lines `import YMBridgeE1`, `import YMBridgeE2`, `import YMBridgeE3` become `import LongTable.YMBridgeE1`, and so on; nothing else changes. Claimed output for each: `(no output; exit 0)`. A `code_ref` needs the commit as it is on GitHub, which this session could not push.

Statement card:

| Theorem | Claim |
|---|---|
| `YMBridge.cut_mem_Ioo` | For continuous ν positive on (−1, 1) and d > 0: −1 < c < 1, where c = log(Z(μ+d)/Z(μ−d))/(2d) and Z(s) = ∫_{−1}^1 e^{sx}ν(x) dx. |
| `YMBridge.dens_cut_eq` | Same hypotheses: q_{μ+d}(c) = q_{μ−d}(c), with q_s(x) = e^{sx}ν(x)/Z(s). |
| `YMBridge.W_eq` | Same hypotheses: W := ½∫_{−1}^1 \|q_{μ+d} − q_{μ−d}\| dx equals ∫_c^1 e^{(μ+d)x}ν dx / Z(μ+d) − ∫_c^1 e^{(μ−d)x}ν dx / Z(μ−d). |
| `YMBridge.hasDerivAt_W` | Same hypotheses: W has derivative g(μ+d, c) − g(μ−d, c) at μ, where g(s, y) = N_1(s, y)/Z(s) − m_s·N_0(s, y)/Z(s) and N_n(s, y) = ∫_y^1 xⁿe^{sx}ν(x) dx. |
| `YMBridge.hasDerivAt_W'` | Same hypotheses: t ↦ g(t+d, c(t)) − g(t−d, c(t)) has derivative Φ at μ, where Φ = U(s₂) − U(s₁) + q(m_{s₂} − m_{s₁})²/(2d) is the header's (\*) with the header's U, q, c, m, Var. |
| `YMBridge.bridge` | Same hypotheses: W is differentiable in μ, its derivative is differentiable, and the second derivative at every real μ equals Φ. |
| `YMBridge.nuR_continuous`, `YMBridge.nuR_pos` | ν_r(x) = √(1−x²)·φ(r√(1−x²)), with φ(z) = sinh z/z and φ(0) = 1, is continuous on ℝ and positive on (−1, 1), for every real r. |
| `YMBridge.bridge_nuR` | For every real r and every d > 0: W for the weight ν_r is twice differentiable in μ and its second derivative at every real μ equals Φ for ν_r. |

## Not formalized

- That W for ν_r is the total-variation distance of the lattice conditional laws (steps 1–2 of #mwpwcrz7-uii66h).
- That Φ is negative on the range (the certificates), and that the certificate programs compute Φ/d.
- That ½∫|q_{s₂} − q_{s₁}| is the total-variation distance of Q_{s₂} and Q_{s₁} as measures. Here W is defined by that integral.
- The step from W″ < 0 to W(μ) ≤ W(0).

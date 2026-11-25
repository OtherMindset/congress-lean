# PP1: P(φ)₂ direction, Session 1 (Claude council, 25 Nov 2026)

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Both files built locally with `lake build` (no sorry; `#print axioms` gives propext, Classical.choice, Quot.sound for the two theorems).

| File | Imports | What |
| --- | --- | --- |
| `PP2SemigroupGap.lean` | `LongTable.P_mwpv7txg_lpqim9` (the posted `YMSpectralStep`, #mwpv7txg-lpqim9) | D6: one real lemma (arrow 3(a), semigroup form) |
| `PP2Target.lean` | `Mathlib` | D5: the target statement, definitions only, no proof |

## Statement card, `PP2SemigroupGap.lean`

- `PP2Gap.rankOne Ω` (def): x ↦ ⟪Ω, x⟫ • Ω.
- `PP2Gap.rankOne_apply`, `PP2Gap.rankOne_selfAdjoint`: its formula; it is self-adjoint.
- `PP2Gap.pow_eq`: if T(s+t) = T(s)T(t) for s, t ≥ 0, then T(k·t) = T(t)^k for k ≥ 1, t ≥ 0.
- `PP2Gap.semigroup_gap`: E a real or complex Hilbert space; T : ℝ → (E →L E) with T t self-adjoint and T(s+t) = T(s)T(t) for s, t ≥ 0; Ω a unit vector fixed by every T t (t ≥ 0); D ⊆ Ω^⊥ with Ω^⊥ ⊆ closure D; for each v ∈ D some C with Re⟪v, T(s)v⟫ ≤ C·e^{−ms} for s ≥ 0. Then ‖T(t)u‖ ≤ e^{−mt}‖u‖ for t ≥ 0 and u ⊥ Ω.
- `PP2Gap.fixed_mem_span`: same hypotheses and m > 0; a vector fixed by every T t (t ≥ 0) is ⟪Ω, u⟫Ω.

## Statement card, `PP2Target.lean`

The card is in the file's header comment (definitions `Site`, `pos`, `freeAction`, `freeWeight`, `wickConst`, `wickPow`, `wickPoly`, `weight`, `smear`, `Zlat`, `translate`, `IsNonGaussian`, `HasUniformClustering`, `GappedLimit`, `PhiFourTwoWeakCouplingGap`, `PPhiTwoWeakCouplingGap`). No theorem.

## Post drafts

`posts/` holds the text of each Long Table post of the session (D1–D4, summary), as drafted and second-passed.

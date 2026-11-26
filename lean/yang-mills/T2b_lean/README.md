# T2b Lean files (session 13)

Toolchain: Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
Each file builds as module `LongTable.<name>` with no `sorry`. Every theorem uses only propext, Classical.choice and Quot.sound, checked with `check.sh` by the authoring agent and again independently by the lead.

| File | Contents | Theorems |
|---|---|---|
| PP2ABFDini.lean | The Dini-weakened ABF characteristics lemma (Lemma A), the per-torus Lemma B, the power case F = C s^θ, and the passage to limits (`abfD_limit_pow`). Imports only Mathlib. | 24 |
| PP2TorusEOM.lean | The equation of motion on any finite graph (`eom`); the translation-invariant form (`eom_ti`); the H- and a-derivative formulas. Imports only Mathlib. | 55 |
| PP2TorusMaxwell.lean | The Maxwell relation, and the exact identity `star_identity`: m − Hχ = 4bm²(∂_H R + ∂_H⟨φ₀²⟩). | 29 |
| PP2TorusNN.lean | The nearest-neighbour torus (ZMod N)², N ≥ 3: `eom_nn`, `eom_continuum` (μ_b m + 4λ⟨φ₀³⟩ = h), `maxwell_nn`, `star_nn`. | 16 |

Not formalized:
- m > 0 for H > 0 (GKS I);
- GKS and GHS signs;
- joint C¹ regularity in (μ, h);
- the pressure-convexity step;
- the open input (P).

Not posted to the Long Table.

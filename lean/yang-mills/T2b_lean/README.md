# T2b Lean files (session 13)

Toolchain: Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
Each file builds as module `LongTable.<name>` with no `sorry`. Every theorem uses only propext, Classical.choice and Quot.sound, checked with `check.sh` by the authoring agent and again independently by the lead.

| File | Contents | `theorem`/`lemma` declarations |
|---|---|---|
| PP2ABFDini.lean | The Dini-weakened ABF characteristics lemma (Lemma A), the per-torus Lemma B, the power case F = C s^θ, and the passage to limits (`abfD_limit_pow`). Imports only Mathlib. | 10 |
| PP2TorusEOM.lean | The equation of motion on any finite graph (`eom`); the translation-invariant form (`eom_ti`); the H- and a-derivative formulas. Imports only Mathlib. | 36 |
| PP2TorusMaxwell.lean | The Maxwell relation, and the exact identity `star_identity`: m − Hχ = 4bm²(∂_H R + ∂_H⟨φ₀²⟩). | 20 |
| PP2TorusNN.lean | The nearest-neighbour torus (ZMod N)², N ≥ 3: `eom_nn`, `eom_continuum` (μ_b m + 4λ⟨φ₀³⟩ = h), `maxwell_nn`, `star_nn`. | 9 |
| PP2OneSiteA–D.lean | The one-site theorem. `R_antitoneOn_EMN`: for V that is C², even, with V″ nondecreasing on [0,∞) and superlinear, R(H) = ⟨φ;φ²⟩_H/⟨φ⟩_H is antitone on H > 0. `R_antitoneOn_phi4`: the instance V = λx⁴ + (μ/2)x² for λ > 0 and any μ. Layers: Chebyshev/MLR in product form, sinh-ratio monotonicity, the duplication change of variables, supermodularity from EMN. Imports only Mathlib. | 8+13+18+7 |

Not formalized:
- m > 0 for H > 0 (GKS I);
- GKS and GHS signs;
- joint C¹ regularity in (μ, h);
- the pressure-convexity step;
- the open input (P).

Posted to the Yang–Mills table of the Long Table on 26 November 2026 (by reference to commit dc5c9e9): PP2ABFDini #mwxrgqa8-yzwwh3, PP2TorusEOM #mwxrgqed-wp91bc, PP2TorusMaxwell #mwxrgqjt-yz1opc, PP2TorusNN #mwxrgqpc-6ye1sm, PP2OneSiteA #mwxrgqtf-l3pl1a, PP2OneSiteB #mwxrgqyf-36c38e, PP2OneSiteC #mwxrgr5q-ejxthl, PP2OneSiteD #mwxrgras-f25253. The site's runner built each; GPT-6 and Gemini 4 Argon each gave a hard statement-match holds; ledger status machine-checked. See the paper's Online Resource 1, Section S3.

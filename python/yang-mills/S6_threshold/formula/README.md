# Is the certificates' G really ∂²_μW / d? (formula bridge, tasks A–C)

Lattice only. The G certificates (`../../S4_general_d/G_box_A_*.py`, `../G_affine_cert.py`) enclose an expression (\*) written in the header of `G_box_A_1of2.py`. The files here address one question: is that expression the second μ-derivative of the total-variation distance W(μ, r, d)? Nothing in the reviewed files is changed.

| File | What it is |
|---|---|
| `POST_C_derivation.md` | The derivation of ∂²_μW = U(s₂) − U(s₁) + q(m_{s₂} − m_{s₁})²/(2d), every step written out. Posted at the yang-mills table as #mws992zj-dsd6ec |
| `POST_A_transcription.md` | The header's symbols mapped to step 5 of #mwpwcrz7-uii66h and step 3 of #mwoe82ar-5qx8aa. Posted as #mws99s69-2jprg3 |
| `d2W_vs_header.py`, `d2W_vs_header.out` | Numerical test: ∂²_μW from the definition of W (quadrature, numerical root for the crossing, five-point stencil with two Richardson steps) against the header expression, at 240 points, and against the affine enclosure of the 20 reference boxes at 60 points. Standard library plus mpmath; about 25 s. Posted as #mws9bfaj-0zbpmm (described in #mws9d9rx-h4wrqb); the site's runner reran it with matching output (26.5 s), read back from the site on 22 Nov 2026 |
| `CHECK_PROMPTS.md` | The three prompts for the GPT and Gemini checks, which this session could not run |

## Rerun

    python3 d2W_vs_header.py     # must print the 10 lines of d2W_vs_header.out

SHA-256 of the file: 6079ba1163c34b2fbfa91c680d662e1cdd4346115c24e7565338e411cf2ae4c6. The site stores it after normalisation (blank-line runs cut to one): 10,278 characters, SHA-256 65c7b5edd0a047e99c1d5e16396d01ea329cbb192591aa9c186107fbe8de9171; that text prints the same output.

Output was character-identical under Python 3.13.18 with mpmath 1.4.1 and Python 3.12.3 with mpmath 1.3.0 (this session's runs of this version of the file).

## What the test shows, and what it does not

- Threshold, written into the file before its first run: max |A − B|/|B| < 10⁻¹⁰. Measured: 3.6 × 10⁻¹⁸ (at μ = 0, r = 0, d = 0.005).
- Step 1/16 in place of 1/32 gives 9.2 × 10⁻¹⁶, a factor 256 = 2⁸, as an h⁸ truncation error should: the difference is the stencil's truncation error, not a disagreement between the two sides.
- Controls, run offline at 8 of the points: the test fails for wrong formulas. Without the q-term the relative difference is 0.54–0.61; with 1/d in place of 1/(2d), 2.7–7.5; with the q-term's sign flipped, 0.70–0.76.
- The 20 reference boxes of `../G_affine_reference.txt` (at commit 95d0843): at all 60 points, 2⁶⁴·G lies within e of the affine part, for G from either side; the largest |residual|/e is 0.0293. Phase 2's self-contained reference program was not available (not pushed), so the committed numbers of `G_affine_reference.txt` are embedded in the program.
- The program was edited once after its first run, on the second pass's advice: a label, the printed error estimate (now |r2 − r1|/63) and one more printed ratio. Sides A and B and the threshold were not changed, and the measured maximum is the same.

This is evidence, not proof. The derivation is `POST_C_derivation.md`; a kernel proof is in `lean/yang-mills/S6_threshold/bridge/`.

Second pass (Claude Opus 5.5, asked to find errors): no blocking error in the three items; it rederived the identity and confirmed it by its own quadrature at 5 points off the grid (relative differences about 10⁻⁴⁰ to 10⁻³⁹); its wording points are applied.

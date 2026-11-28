# One phase or many? — preprint source

LaTeX source of the Zenodo preprint "One phase or many? What OpenAI's formal Yang–Mills construction proves about its vacuum, and where it stops" (A. R. Cohen, v1, 27 November 2026, doi:10.5281/zenodo.24614275), and of its Online Resource 1.

- `zenodo.tex`: the preprint. Build with `pdflatex zenodo.tex` (run twice).
- `online_resource_1/supp.tex`: Online Resource 1. Build with `xelatex supp.tex` (run twice) from inside `online_resource_1/`. It reads `rec.txt` (build and axiom record), `repro.txt` (reproduction recipe) and the eight Lean files in `../../OP_onephase/`. It needs the Latin Modern and DejaVu Sans Mono fonts.
- The two PDFs are the files deposited on Zenodo.

The Lean files themselves are in `../OP_onephase/`.

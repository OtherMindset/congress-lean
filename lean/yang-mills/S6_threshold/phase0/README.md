# Phase 0: float prototype of the affine-form certificate

Phase 0 of `../SPEC_small_certificate_and_kernel_checker.md`. **A float prototype: it is not rigorous and proves nothing about G.** Its purpose is to measure how many boxes an affine-form certificate needs. The results, and the gate 0 verdict (passes: 128 boxes), are in `RESULTS.md`.

## Requirements

Python 3 with numpy. The certificate under `python/yang-mills/S4_general_d/` is imported read-only and is not changed.

## Files

| File | What it does | Run time |
|---|---|---|
| `affine.py` | Affine forms in floats, vectorised over boxes. Implements the rules of spec 2.2 plus the measured variants (`Ctx.prod`, `Ctx.fn`), the error term split by source, and optional modelled rounding (`Ctx.unit`) | — |
| `g_affine.py` | Port of `G_enclosure` from `G_box_A_1of2.py` (spec 2.3), with no clip of c | — |
| `check_port.py` | Step 4: zero-width boxes against the certificate's point values, and the reference box | seconds |
| `check_contain.py` | Point values of G, c and q at 400 points in each box lie in the affine range | seconds |
| `check_c.py` | Step 5: the incomplete moments for c < 0 against quadrature, the range of c over the grids, and the error against cell size | seconds |
| `measure.py` | Steps 6–7: smallest equal-cell count per region, for three rule sets. Writes `measure_out.json`; its printout is saved as `measure_out.txt` | about 3 min |
| `breakdown.py` | The error term of G split by operation and stage, for typical cells, and the effect of rounding at 2^(−P) | seconds |
| `grid.py` | The proposed grid (uniform 8 × 8 × 2). Writes `grid_8x8x2.csv` | seconds |

## Rerun

From this folder:

    python3 check_port.py
    python3 check_contain.py
    python3 check_c.py
    python3 breakdown.py
    python3 grid.py
    python3 measure.py > measure_out.txt

Rule sets, as named in the scripts:

- `spec`: the specification's rules as written.
- `sq+best`: the specification's products, the square rule, and α taken at whichever end of the range gives the smaller spread.
- `tight`: as `sq+best`, plus the diagonal terms of products.

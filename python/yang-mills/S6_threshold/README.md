# Phase 1: exact affine-form certificate for G < 0 (128 boxes)

This is Part A of `lean/yang-mills/S6_threshold/SPEC_small_certificate_and_kernel_checker.md` (phase 1). Lattice only.

**Status: built and run here, not yet checked by anyone else.** Gate 1 needs three things: runner reruns with matching output, a second pass by a different Claude model, and code reads by two model families. None of them has happened. Nothing has been posted, and there is no ledger entry. The paper's theorems keep resting on the present certificate, `python/yang-mills/S4_general_d/G_box_A_*.py` (ledger l-mwpwfqjt-6ak431), which is unchanged.

## Claim

G(μ, r, d) < 0 for all 0 < d ≤ 1/5 and 0 ≤ μ, r ≤ 4/5. This is the same G, defined by the same header expression, as in `G_box_A_1of2.py`, so the derivation checks already made on that header carry over.

## Files

| File | What it is |
|---|---|
| `G_affine_cert.py` | The certificate: Python integers and `fractions` only, affine forms at P = 64, a uniform 8 × 8 × 2 grid (128 boxes), one part. Its output is in `G_affine_cert.out` |
| `G_affine_tiling.py` | Exact-rational check that the boxes cover [0, 4/5]² × [0, 1/5], by two independent arguments. Its output is in `G_affine_tiling.out` |
| `G_affine_reference.py`, `G_affine_reference.txt` | The reference file: the five integers of the affine form of G for 20 fixed boxes. Phase 2's Lean `Eval` must reproduce them |
| `G_affine_checks.py`, `G_affine_checks.out` | Cross-checks, not part of the proof (listed below) |

## Rerun

From this folder:

    python3 G_affine_cert.py        # about 2 s; must print the five lines of G_affine_cert.out
    python3 G_affine_tiling.py      # under 1 s
    python3 G_affine_reference.py   # rewrites G_affine_reference.txt; must not change it
    python3 G_affine_checks.py      # about 40 s; needs ../S4_general_d/G_box_A_1of2.py

## Results (this session's runs)

- **Largest upper bound** of G over the 128 boxes: ≤ −0.016143. All guards hold. c lies in [−0.000308, 0.195490], and q ≤ 0.695.
- **P = 64 against P = 104:** the same largest upper bound to 9 decimals; box by box they differ by at most 2 × 10⁻¹⁶.
- **The present certificate's point values:** at 1,536 rational points (12 a box, both corners of every box included), the present certificate's point intervals all lie inside the affine enclosure of their box. The smallest gap between the upper bound and a point value is 0.0044.
- **Reference box** μ ∈ [0.400, 0.405], r ∈ [0.40, 0.41], d ∈ [0.126, 0.154]: affine [−0.061665, −0.061008], inside the present certificate's [−0.074852, −0.047796].
- **Rule tests:** 30,000 results of the operations, on random forms at random ε, all satisfy (ENC). The operations are +, −, ×, the square rule, ×7, ÷13, 1/x, √x, eˣ and asin.
- **Float prototype:** for every box, the exact upper bound agrees with the phase 0 prototype (rules `sq+best`) to the 6 decimals of `phase0/grid_8x8x2.csv`.

These checks are evidence that the program does what its header says. They are not a proof of it: the proof is the code read.

## Points to derive in the code reads (spec 2.5)

The header of `G_affine_cert.py` states each rule. A reader should derive, from the source:

1. **(ENC) and the inputs.** The meaning of a form (c, a₁, a₂, a₃, e) at scale 2^(−P). `var` must map ε onto a set containing the box: c − a < S·lo and c + a > S·hi. A box is accepted only if c + |a₁| + |a₂| + |a₃| + e < 0.
2. **Product rule** (`A.__mul__`): the centre and the linear part are floored. The error is ceil((|cx|ey + |cy|ex + (Lx + ex)(Ly + ey)) / S) + 4.
3. **Square rule** (`sq`, a phase 0 addition): (Ax + ux)² ∈ [0, R²]. The centre is floor((2cx² + R²)/(2S)), and e = ceil((R² + 4|cx|ex)/(2S)) + 4.
4. **Division by a positive integer** and the `+4`. Also `const`: the centre is the floor of S·mid, and e = ceil(S·half-width) + 1.
5. **The function rule** (`fn_rule`): with α a lower or upper bound of f′ on [lo, hi], g = f − α·id is monotone there. Its range is the hull of the enclosures at the two ends. Rounding ζ down costs +1 in δ. Keeping whichever α gives the smaller hull is sound.
6. **The derivative bounds**, one function at a time, including the direction of each rounding:
   - 1/x: −⌈S³/lo²⌉ and −⌊S³/hi²⌋.
   - √x: ⌊S²/(2⌈√(hi·S)⌉)⌋ and ⌈S²/(2⌊√(lo·S)⌋)⌉.
   - eˣ: S·e^lo rounded down, S·e^hi rounded up.
   - asin: S²/⌈√(S² − m²)⌉ rounded down and ⌈S²/⌊√(S² − M²)⌋⌉, with m = min|y| (0 if the range contains 0) and M = max|y|.

   artanh needs no rule: the artanh series for c is a polynomial in u₂ with a value tail.
7. **The enclosures of the elementary functions on rationals:** `exp_iv` (remainder bound for |q| ≤ 2), `asin_iv` (aₖ ≤ 1 and the tail q^(2NA+3)/(1 − q²), oddness), `cosh_hi`, and π by Machin.
8. **The table moments over [−1, 1]:** F[k][n] = π·Q[k][n] with Q rational, from the recurrence. Each is enclosed using π's interval.
9. **The range of c:** there is no clip. The closed forms for ∫ over [c, 1], and the recurrence (n + 2)T₀ₙ = (n − 1)T₀,ₙ₋₂ + c^(n−1)w³, hold for every c in (−1, 1). The guard is −1/64 ≤ lo(c) and hi(c) ≤ 1/4. That range also satisfies the asin guard (|·| ≤ 1/4) and keeps 1 − c² > 0.
10. **The tails go into e:**
    - The series tail of `G_box_A_1of2.py`, at the upper corner of the box, added to every E_n and O_n. It is monotone in μ, r, d ≥ 0, and the length of [c, 1] is ≤ 2.
    - The artanh tail ≤ 2·hi(u₂)^13 for 0 ≤ u₂ < 1/4.
    - The φ tail ≤ z^(2KR+2)·cosh z/(2KR+3)! for z ≥ 0.
11. **The evaluator follows `G_box_A_1of2.py`:** the same series degrees (JS, JD, KR = 18, 5, 7), the same pair algebra, and G = 2U_o + 2q·m_o².
12. **Tiling** (`G_affine_tiling.py`): the product-partition argument and the volume argument.

## Not done

- The runner rerun.
- The second pass by a different Claude model.
- The two-family code reads.
- The ledger entry.
- Phase 2 (the Lean `Eval` and its kernel timing).
- The range 1/5 ≤ d ≤ 2/5.

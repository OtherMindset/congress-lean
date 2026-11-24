# Phase 0 results: float affine-form prototype, cell sizes and gate 0

Claude (claude-opus-5-5), single Opus session, 22 Nov 2026 UTC, on congress-lean at `b62aecd`. A measurement, not a result. Lattice only.

**This is a float prototype. It is not rigorous and proves nothing about G.** The numbers below are evidence about how many boxes an exact affine-form certificate will need. They are not evidence that G < 0 beyond what the present certificate already proves.

## Gate 0: passes, by a wide margin

| Grid on [0, 4/5]² × [0, 1/5] | Rules | Boxes | Largest float upper bound of G |
|---|---|---|---|
| uniform 8 × 8 × 2 (cells 1/10 × 1/10 × 1/10) | specification 2.2 as written | **128** | **−0.0070** |
| uniform 8 × 8 × 2 | specification products + square rule + better endpoint (see 4) | 128 | −0.0161 |
| uniform 8 × 8 × 1 (cells 1/10 × 1/10 × 1/5) | the same | 64 | −0.0069 |
| region table, 16 regions of 1/5 × 1/5 × 1/5 | specification 2.2 as written | 49 | −0.0050 |
| region table, 16 regions | square rule + better endpoint | 27 | −0.0056 |

The budget was 2,000 boxes with every upper bound ≤ −0.005. With the rules exactly as the specification writes them, a plain uniform grid of 128 boxes passes. The smallest margin on it is 0.0020 below the −0.005 threshold, or 0.0070 below 0. It is at the corner cell μ, r ∈ [0.7, 0.8], d ∈ [0.1, 0.2].

For comparison, the present certificate uses 64,000 boxes and plain intervals. On the reference box μ ∈ [0.400, 0.405], r ∈ [0.40, 0.41], d ∈ [0.126, 0.154], its enclosure of G is [−0.07485, −0.04780], 0.027 wide. The affine prototype gives [−0.06179, −0.06089], 0.0009 wide, inside it.

## 1. Port check (step 4)

- The present evaluator was imported unchanged and reproduces the reference box: upper end −969423951419388557984473300202 / 2^104, about −0.0478.
- **Zero-width boxes.** At 42 points, the 40 random ones plus the corners (0.8, 0.8, 0.2) and (0.001, 0, 0.001), the affine centre agrees with the certificate's point interval to 3.5 × 10⁻¹⁶ (largest difference).
- **Reference box.** The affine range lies inside the certificate's interval, for all three rule sets (`check_port.py`).
- **Containment.** At 400 points in each box, corners included, for five grids and rule sets (160,000 points), the point values of G, c and q all lie in the box's affine range (`check_contain.py`). Over the sampled points, G runs from −0.0690 to −0.0442. This agrees with the handoff's range of about −0.069 to −0.043.

This containment test is a smoke test of the rules. It is not a proof that the rules are sound: soundness is phase 1's code reads and phase 3's proof.

## 2. Cell sizes by region (step 6)

These are the largest equal cells per region whose float upper bounds all stay ≤ −0.005. They come from an exhaustive search over n_μ, n_r ≤ 8, n_d ≤ 4 per region (`measure.py`; the full tables are in `measure_out.txt` and `measure_out.json`). The rules are the specification's, as written.

| μ \ r | [0, 0.2] | [0.2, 0.4] | [0.4, 0.6] | [0.6, 0.8] |
|---|---|---|---|---|
| [0, 0.2] | 0.2 × 0.2 × 0.2 | 0.2 × 0.2 × 0.2 | 0.2 × 0.2 × 0.2 | 0.2 × 0.2 × 0.2 |
| [0.2, 0.4] | 0.2 × 0.2 × 0.2 | 0.1 × 0.2 × 0.2 | 0.1 × 0.2 × 0.2 | 0.2 × 0.1 × 0.2 |
| [0.4, 0.6] | 0.1 × 0.2 × 0.2 | 0.1 × 0.2 × 0.2 | 0.1 × 0.1 × 0.2 | 0.1 × 0.1 × 0.2 |
| [0.6, 0.8] | 0.1 × 0.2 × 0.1 | 0.067 × 0.2 × 0.1 | 0.1 × 0.1 × 0.1 | 0.1 × 0.1 × 0.1 |

(cells h_μ × h_r × h_d; 49 boxes in all.) The search minimises the count, so some regions end close to −0.005. Small cells are needed where μ is large; the range in d is rarely split.

**Scaling with cell size.** This was measured on cells [0.8 − h, 0.8]² × [0.2 − h/2, 0.2], shrinking to the worst corner (`check_c.py`, part c):

| h | linear part | error term, specification rules | error / h² | error term, tight rules | error / h² |
|---|---|---|---|---|---|
| 0.2 | 0.0057 | 0.136 | 3.40 | 0.077 | 1.93 |
| 0.1 | 0.0026 | 0.031 | 3.08 | 0.020 | 2.03 |
| 0.05 | 0.0013 | 0.0074 | 2.96 | 0.0052 | 2.09 |
| 0.025 | 0.0006 | 0.0018 | 2.91 | 0.0013 | 2.12 |

The error term is quadratic: its constant is about 2.9 under the specification's rules and about 2.1 under the tight rules. The linear part, about 0.025·h, is the function's own variation; it is about 8 % of the radius at h = 0.1. This answers the specification's "not known" point 1 (the constant was unmeasured).

## 3. Where the error term comes from

The error term is split exactly, by source. Each product, function rule or tail records the error it creates, and the rules pass that error on linearly, so the shares add up to 100 % (`breakdown.py`). The rules are the specification's.

| Cell | Error term | By operation | Largest sources (operation @ stage) |
|---|---|---|---|
| worst cell of 8×8×2, μ, r ∈ [0.7, 0.8], d ∈ [0.1, 0.2] | 0.0371 | products 71 %, 1/x 29 % | 1/x in the pair algebra 27 %, squares d², r² 23 %, products in the pair algebra 23 %, powers μ^i, r^2k, d^2j 15 % |
| middle cell [0.4, 0.5]² × [0, 0.1] | 0.0168 | products 83 %, 1/x 17 % | d², r² 34 %, powers 21 %, pair algebra 20 %, 1/x 16 % |
| low cell [0, 0.2]² × [0, 0.2] | 0.0329 | products 95 %, 1/x 5 % | d², r² 46 %, powers 27 %, pair algebra 15 % |
| reference box | 0.00029 | products 92 %, 1/x 8 % | d², r² 78 % |

The other function rules, √x, e^x and asin, each contribute under 1 %. The truncation tails are each below 10⁻¹⁵ and are negligible. The products that build the moment series (stages `full` and `partial`) are under 5 %.

The two large sources are:

1. **The squares d² and r²**, at the very start. The specification's product rule applied to x·x charges (Σ|xᵢ|)² in full. Because x² − (linear part) ≥ 0 lies in [0, R²], the error can be halved.
2. **The single 1/x in the pair algebra**, 1/(Z₀² − d²Z₁²). Under the specification's rule, α is a lower bound of f′ = −1/x², which is the steeper end. The other end, an upper bound of f′, is just as sound and gives a smaller spread for 1/x.

## 4. Rule variants measured

All three variants are sound for the same reason as the specification's rules. In the float prototype, they all pass the containment test.

| Variant | What changes | 8×8×1 | 8×8×2 |
|---|---|---|---|
| specification as written | — | +0.0121 (fails) | −0.0070 |
| function rule "best" | α = lower **or upper** bound of f′ (derivative at either end), whichever gives the smaller spread: g = f − αx is monotone either way | +0.0061 | −0.0111 |
| square rule | x² = x₀² + 2x₀·(linear) + [0, R²], R = Σ\|xᵢ\| + e: centre + R²/2, error R²/2 + 2\|x₀\|e | −0.0024 | −0.0127 |
| square + "best" | both | −0.0069 | −0.0161 |
| + diagonal products | xᵢyᵢεᵢ² ∈ [0, xᵢyᵢ]: centre + Σxᵢyᵢ/2, error Lx·Ly − Σ\|xᵢyᵢ\|/2 | −0.0113 | −0.0205 |
| + secant slope ("cheb") | α = secant slope; needs the interior extreme of g, so a lower bound at a point near f′(x*) = α | −0.0178 | −0.0264 |

My recommendation for phase 1 is the square rule together with "best". Each adds a few lines to the soundness proof and nothing to the kernel cost. Together they more than double the margin of the 8 × 8 × 2 grid.

## 5. The crossing point c (step 5)

- **No clip.** The prototype uses the closed forms and recurrences of `inc_table` on the whole affine range of c. The guard is −δ ≤ lo(c) and hi(c) ≤ 1/4, with δ = 0.05.
- **The formulas for c < 0.** T₀₀ = π/4 − (c w + asin c)/2, T₀₁ = w³/3 and (n + 2)T₀ₙ = (n − 1)T₀,ₙ₋₂ + c^(n−1) w³ come from differentiating x^(n−1)w³, so they hold for every c in (−1, 1), with asin odd. Checked against Gauss–Legendre quadrature (x = sin t), for c ∈ {−0.2, −0.05, −0.01, −10⁻⁴, 0, 0.1, 0.25}, all k ≤ 7 and all n ≤ 31: the largest difference is 1.3 × 10⁻¹⁴. In the affine arithmetic they behave: the boxes at μ = 0, where c straddles 0, pass the containment test.
- **How far below 0 c goes.** The lowest lo(c) over all boxes is −0.0015 (4 × 4 × 1 grid), −0.00034 (8 × 8 × 2) and −0.00009 (16 × 16 × 2). It always occurs at the cells with μ_lo = 0. The highest hi(c) is 0.198, inside the 1/4 that the guard allows. The guard never failed. **δ = 1/64 is ample**, and I propose it.
- The artanh series in u₂ = (d t)² is evaluated as a polynomial with its tail, as the certificate does, so **artanh is never needed as a function rule**.

## 6. Precision P

The prototype models the exact program's rounding: it adds 4·2^(−P) to the error term at every product, square, function rule and non-integer scaling. With that, the largest upper bound on 8 × 8 × 2 is unchanged to 6 decimals for every P from 32 to 104, against −0.006984 without rounding. Rounding contributes about 10⁻⁶ at P = 32.

This is a crude model: float64 has 53 bits, so it shows the size of the rounding error, not the exact program's arithmetic. The relevant quantities are absolute errors, and the tails are below 10⁻¹⁵. Both point to **P = 64 being enough, which makes the integers in the kernel smaller**. This is a guess for phase 1 to confirm, by running the exact program at P = 64 and at P = 104 and comparing.

## 7. Proposed grid for phase 1

**Uniform 8 × 8 × 2**: cells [i/10, (i+1)/10] × [j/10, (j+1)/10] × [k/10, (k+1)/10], i, j = 0..7, k = 0, 1, so 128 boxes.

| | μ | r | d |
|---|---|---|---|
| ends | 0, 1/10, …, 8/10 | 0, 1/10, …, 8/10 | 0, 1/10, 2/10 |
| cells | 8 | 8 | 2 |

Float upper bounds: ≤ −0.0070 under the specification's rules, ≤ −0.0161 with the square rule and "best". `grid_8x8x2.csv` lists all 128 boxes with their exact ends and the float upper bounds under three rule sets, for phase 1 to compare against.

Why uniform rather than the 27- to 49-box region tables:

- It keeps `Cover` trivial.
- It has more margin.
- The count is already about 500 times smaller than the present 64,000, so the kernel cost no longer depends on squeezing it. As a guess from the specification's own figures: 128 × 1.2 s is about 3 minutes, and 128 × 12 s, the pilot's 4 s times three for affine forms, is about 26 minutes. Both are inside gate 2's 2 hours. These are guesses until phase 2 measures them.

If the exact program comes out with less margin than the prototype, 16 × 16 × 2 (512 boxes, ≤ −0.0305 under the specification's rules) is the next step.

## 8. Fallbacks

Not needed: the gate passes. No second-order forms, no rewriting of G, no `native_decide`.

## 9. What this does not show, and what I did not do or check

- Nothing about G < 0. The float prototype has no outward rounding. Its constants (π, the moment tables over [−1, 1]) are floats, not intervals. Its soundness rests on code that no one else has read.
- The rule variants of section 4 are mine, not the specification's. Each needs the same two-family code read as the rest before phase 1 relies on it.
- The specification's claims about the present enclosure (its width of about 2.2 per unit of μ, and the slopes) were not rerun. The prototype's linear part, about 0.025·h, is consistent with slopes of a few hundredths.
- The range 1/5 ≤ d ≤ 2/5 was not looked at.
- No exact arithmetic (phase 1), no Lean (phases 2 and 3), no post and no ledger change.

## Files

`affine.py` (affine forms), `g_affine.py` (the port), `check_port.py`, `check_contain.py`, `check_c.py`, `measure.py`, `breakdown.py`, `grid.py`; outputs `measure_out.txt`, `measure_out.json`, `grid_8x8x2.csv`. To rerun, see `README.md`.

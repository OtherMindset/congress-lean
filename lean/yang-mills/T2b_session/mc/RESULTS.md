# Monte Carlo test of Lemma L (K = 0) on 2D tori in the phase-flipping regime

26 Nov 2026. Directory /home/claude/t2b/mc. All numbers come from `results.json` (`analysis.log`, `table.txt` and `summary_table.md` are views of it).

## Model and conventions
- Model: an L×L periodic torus with weight exp(Σ_⟨xy⟩ φ_xφ_y + HΣφ_x − Σ(aφ_x² + bφ_x⁴)). Each of the 2N torus bonds is counted once, ε = 1, H = ε²h, b = λ.
- Observables: site averages A, B, C of φ, φ², φ³. m = ⟨A⟩, R = (⟨C⟩ − m⟨B⟩)/m.
- dR/dH is computed as a correlation, using d⟨O⟩/dH = N·Cov(O, A).
- D = d⟨φ²⟩/dH = −∂_a m = 2(−∂_μ m). This is the Maxwell relation, exact on the torus.
- Lattice EOM (exact): (4 − 2a)m − 4b⟨φ³⟩ + H = 0. Differentiating gives m − Hχ = 4bm²(∂_H R + D), with χ = ∂_H m = N·Var(A).
- ABF ratio: Q_μ := (m − Hχ)/(b m²(−∂_μ m)) = 8(1 + ∂_H R/D). L with K = 0 ⟺ Q_μ ≤ 8. Written with ∂_a instead of ∂_μ, the threshold is 4.
- Two estimators of Q are reported: Q, computed directly from m − Hχ, and Qid, computed from the identity. They agree to ≤ 0.11 on every grid point.
- Relative margin of L: margin := −∂_H R/D = 1 − Q_μ/8. A violation means margin < 0.
- Flip scale: s := H·⟨|M|⟩₀, with M = ΣA·N measured at H = 0. s ~ 1 ⟺ H ~ m*/χ, i.e. h ~ s′/χ, which is the window the ABF characteristic uses.

## Algorithm (phi4.c)
- Each sweep has three parts:
  - a Metropolis sweep, with step tuned to 50% acceptance during thermalisation;
  - an overrelaxation sweep: reflection φ → J/a − φ, which preserves the Gaussian part, accepted with the quartic factor;
  - a **fixed** number NCL of Brower–Tamayo/Wolff embedded clusters, with bond probability 1 − e^{−2φ_xφ_y} on like-sign bonds and flip acceptance min(1, e^{−2HΣ_cluster φ}).
- **Bug found and fixed during validation.** The first version ran clusters "until ≥ N sites were visited". That is a state-dependent stopping rule, and it biased results by up to 7% (2×2 χ 20σ off, Gaussian χ 4% off). NCL is now fixed after thermalisation.
- Measurements are taken every sweep. Autocorrelation times: τ_int ≈ 5–12 sweeps for |A| and B, and ≲ 4 for A, since sign flips happen every few sweeps.
- Thermalisation is 5000 sweeps from an ordered start.

## Validation
- **2×2 torus vs. exact transfer-matrix quadrature** (`validate.py`, `validation/validate.log`).
  - On L = 2 the torus is a 4-cycle with coupling 2.
  - Checked: m, B, C, χ, R and dR/dH at (a, b, H) = (1.5, 0.5, 0.3) by direct simulation, and at (1.8, 0.1) by H = 0 runs reweighted to H = 0.05 and 0.3.
  - All pulls |p| < 0.7, including dR/dH.
- **Gaussian b = 0, a = 2.5, 16×16:** ⟨φ²⟩ = 0.25401(16) vs. 0.25405 exact; χ = 1.0047 vs. 1.
- **Exact EOM on all 93 production runs:** pulls have mean 0.06 and rms 1.02. The largest is 3.7, on one run (b0.5_a0.8_L64, s = 1; residual 6·10⁻⁴ against terms of size about 1.6).
- **Reweighting vs. direct runs:** dR/dH at s = 1 and 10 from the multihistogram vs. the plain direct-run estimate (not independent: the direct runs are also multihistogram inputs; the H = 0-only reweighting, which is independent of them, agrees as well), 38 pulls, rms 0.87.
- **Binning:** the significance of every point is stable across 10/50/250 blocks (direct runs) and 20/100/400 blocks (H = 0 reweighting).

## Critical points (Binder crossing, L = 8/16/32; `binder/`)
| b | a_c (rough) |
|---|---|
| 0.5 | ≈ 0.905 |
| 0.1 | ≈ 1.71 |
| 0.02 | ≈ 1.927 |

- In terms of δ_c = 2 − a_c, δ_c/b ≈ 2.2, 2.9 and 3.6 respectively.
- The `binder/` files use the old 3-column format.

Simulated points:
- "deep": a = 0.70, 1.60, 1.88;
- "moderate": a = 0.80, 1.65, 1.91;
- "near-critical, ordered side": a = 0.88, 1.69, 1.92;
- L = 32 and 64 for every point, plus L = 128 at (b, a) = (0.1, 1.65).
- m* = ⟨|A|⟩ is between 0.55 and 1.38, i.e. 0.53–0.80 of the classical minimum √((2−a)/2b).
- ξ_2nd ≈ 1–10. This is rough: it is computed from χ_conn = N(⟨A²⟩ − ⟨|A|⟩²) and the k_min structure factor.
- χ per site runs from 340 to 13,800.

Runs and estimators:
- Each (b, a, L) has an H = 0 run of 2·10⁵ sweeps (6·10⁴ at L = 128).
- Direct runs of 5·10⁴ sweeps (2·10⁴ at L = 128) were done at s = 1, s = 10, H = 0.05, and at L = 32 also at H = 0.01 and 0.2.
- Flip-regime curves on s ∈ {0.03, …, 10} come from a Z₂-symmetrised multihistogram (WHAM in H) of the H = 0 run and the s = 1, 10 runs. Jackknife uses 20 aligned blocks.
- Symmetrising (adding each run mirrored as a run at −H_k) was essential. Without it, WHAM had O(1) noise in dR/dH as H → 0.

## Results (s = 1 is the centre of the flip window; full grid in table.txt)
See `summary_table.md`.
- dR/dH < 0 at **every** point: 19 (b, a, L) × 9 flip-grid values, plus 74 direct runs.
- Significance is −77σ to −185σ on the multihistogram flip grid, and −24σ to −52σ in direct runs at s ≥ 10.
- In the direct s = 1 runs alone (no reweighting), significance is −1σ to −21σ. This is only because those runs are short; their central values agree with the multihistogram.

## Margins
- **In the flip regime the margin is large.**
  - As s → 0 it is 0.70–0.94. Q_μ is 0.5–2.3, far below 8.
  - It decreases monotonically in s, towards the single-phase value.
  - The minimum over s ≤ 10 is 0.134 (b = 0.02, a = 1.88, L = 32, s = 10).
- **The smallest margin overall is at moderate/large H, not in the flip regime.**
  - It is 0.066 (Q_μ = 7.47) at b = 0.02, a = 1.88, L = 32, H = 0.2, still at −30σ.
  - It decreases with H and with b. This is consistent with C = 8 being saturated at first order in λ (Q → 8 in the weak-coupling, large-field limit).
- **Volume dependence is weak.** From L = 32 to 128 at fixed s the margin is equal or larger; at s = 10, b = 0.1, a = 1.65 it goes 0.314 → 0.339 → 0.350.
- Nearer criticality the flip-regime margin is larger, not smaller.

## Verdict
- No violation, and nothing close to one.
- The least significant point is still negative (the direct L = 128, s = 1 run, −1.1σ, short run). The same point from the multihistogram is −121σ.
- In the flip regime the smallest relative margin is 13% (Q_μ ≤ 6.93). Overall it is 6.6%, at H = 0.2, b = 0.02.

## Trade-off and caveats
- **Cost of smaller b.** At equal reduced distance, smaller b moves a_c towards 2 and gives larger field amplitudes. Cost per sweep and τ are essentially unchanged in this range. The real cost of approaching T2b (ε → 0: b = λε², ξ ≫ 1) is that ξ and L must grow together.
- Here ξ ≲ 10 and L ≤ 128, so this tests the lattice lemma at fixed spacing, not uniformity in ε.
- The margin shrinks as b decreases at fixed H, so the most delicate regime is small b at moderate H, not the flip regime.

## Files
- `phi4.c`: the simulation code.
- `ana.py`: estimators, jackknife, symmetrised reweighting and WHAM.
- `validate.py`, `binder.py`, `run_all.py`, `analyze.py`, `table.py`: the analysis scripts.
- `runs/`: raw data (4 doubles per sweep: A, B, C, |φ̃(k_min)|²/N) and `meta.json`.

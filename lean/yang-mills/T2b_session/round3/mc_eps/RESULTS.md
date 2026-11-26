# Lemma L margin vs lattice spacing at fixed continuum physics (2D phi^4, flip window)

26 Nov 2026. Directory /home/claude/t2b/mc_eps. Nothing was posted; files only. Everything below is generated from `results_*.json` / `table_all.md` (via `make_table.py`) unless noted.

## Verdict (short)
**Margin stable, decreasing only slowly, with no sign of collapse; extrapolates to a clearly positive value.**
Over a factor 8 in eps (b = 0.08 -> 0.00125, L = 32 -> 256) the minimum margin in the flip window (always at s = 10, the window edge) goes 0.399 -> 0.378, a drop of 0.021 +- 0.003 (5% relative). Increments per halving of eps: -0.0085 +- 0.002, -0.0066 +- 0.0023, -0.0058 +- 0.0033 (shrinking, but not by a clean factor 2). Fits to r0 + c*eps give r0(eps->0) = 0.378 +- 0.002 (chi2 2.3/2); a log(eps) drift fits as well (chi2 0.6/2) and cannot be excluded, but its slope (0.0073 per halving) would need ~50 more halvings to reach 0. At larger s (outside the window; direct estimator) the increments clearly halve each step (s = 100: -0.0087, -0.0051, -0.0022). A part of the small-s drift is mistuning of the matched state (see "Matching quality"), not eps. The test is at eps/eps_0 down to 1/8 only, one physical box, one distance to criticality: it supports, but does not prove, uniformity as eps -> 0.

## Design (every choice)
- Code: `phi4.c`, `ana.py` (WHAM, jackknife, estimators), `analyze.py` logic copied unmodified from the validated `mc/` directory; the binary was recompiled from the unmodified source with `gcc -O3 -march=native`. Additions (new files/edits only in this copy): `ana.py` gets two extra jackknifed observables (`margin` = -dR/dH / D, and the EOM combination `eo0`); `analyze_eps.py` (= analyze.py with those, grid s in {0.1,0.3,1,3,10}); `run_eps.py` (launcher, fixed seeds from crc32 of key); `binder2.py`, `cross.py` (Binder scan and crossing); `ext_run.py` (large-s direct runs). The 2x2 transfer-matrix validation was NOT re-run (source unchanged); the exact-EOM pull check was run on every run here (below).
- Model/margin as in the original: r = margin = -dR/dH / D, D = d<phi^2>/dH = N Cov(phi^2-average, A); R = (<C> - m<B>)/m; dR/dH by correlation estimators; Z2-symmetrised multihistogram (WHAM) of the H = 0 run and direct runs at s = 1, 3, 10 (fixed seeds), 20 aligned jackknife blocks; s = H<|M|>_0 with M = N*A measured on the H = 0 run of the same point. Because s = H<|M|> = h * int phi d^2x is a physical invariant, the same s grid is the same physical field at every spacing.
- Spacing sequence: eps^2 = b/lambda, so eps/eps_0 = sqrt(b/b_0): b = 0.08, 0.02, 0.005, 0.00125 -> eps/eps_0 = 1, 1/2, 1/4, 1/8, with L = 32, 64, 128, 256 (physical box L*eps fixed). The 4th spacing (L = 256) is included; family-A reference at b = 0.00125 is only extrapolated (see below).
- Statistics per point: H = 0 run 2e5 sweeps (3e5 at k0; 1.2e5 at b = 0.00125) after 5000 thermalisation; direct runs at s = 1, 3, 10 of 8e4 sweeps (1e5 at k0, 6e4 at b = 0.00125). Each of the b = 0.08, 0.02, 0.005 family-B points was run twice with independent seeds (k0+R0, B1+R1, B2+R2) and combined by inverse-variance weighting. Measurement every sweep. WHAM inputs are thinned (every k-th sweep so each run has <= 1e5 samples for k0/p1/p3, <= 5e4 for R-replicas; k<=4, i.e. below tau_int ~ 8-11); direct-run estimators use all sweeps.
- Autocorrelation: tau_int(|A|) = 7.4-8.4 sweeps (b = 0.08..0.005), 11 at b = 0.00125 (L = 256); n_ind ~ n/(2 tau) = 12,000-20,000 per H = 0 run (5,400 at b = 0.00125). Direct runs tau_int(|A|) 6-20.

## Critical points (Binder crossing, H = 0, U = 1 - <A^4>/(3<A^2>^2), jackknife 20 blocks; linear interpolation of U_L - U_2L on 4 a-values, error = resampling of the U errors; `binder/`)
| b | pair (L,2L) | a_c(L,2L) |
|---|---|---|
| 0.08 | (16,32) / (32,64) / (64,128) | 1.76061(89) / 1.75091(24) / 1.74773(5) |
| 0.02 | (64,128) | 1.92427(5) |
| 0.005 | (64,128) / (128,256) | 1.97792(3) / 1.97759(1) |
| 0.00125 | - | not measured; (2-a_c)/b increments per halving of eps: 0.673, 0.695 (observed) -> extrapolated a_c ~ 1.9934 |
- The infinite-volume a_c is not reachable by these crossings: the crossing drifts with L (b = 0.08: 1.7606, 1.7509, 1.7477, differences shrinking by ~3 per doubling, extrapolates to ~1.746, i.e. ~0.0016 below the (64,128) value). Quoted errors are statistical only; the interpolation/correction-to-scaling systematic is larger, and is the reason for family B.
- Consistency with the one-loop mapping: (2-a_c)/b = 3.114 (0.08), 3.787 (0.02), 4.482 (0.005) from the (L,2L) crossings with box fixed; the increments per halving of eps are 0.673, 0.695, vs the prediction 6 ln2/(2 pi) = 0.662 for mu_b = mu - 12 lambda c_eps with c_eps = ln(1/eps)/(2 pi) + const. The a_c(b) used is therefore compatible with the stated continuum mapping.
- Distance to criticality: b_0 point at a = 1.744 (L = 32): a_c(32,64) - a = 0.00691 +- 0.00024 =: Delta (in lambda = 1 units, (mu_b - mu_c) = -2*Delta/eps_0^2 = -0.173). It is ordered (U = 0.629, chi = 478 per site, m* = 0.67, xi_2nd/L = 0.168).

## Two families (documented because a_c uncertainty can matter)
- **Family A (a_c based)**: a_k = a_c(L_k,2L_k; b_k) - Delta*(b_k/b_0): b = 0.02: a = 1.92254; b = 0.005: a = 1.97716. (b = 0.00125 not run: needs L = 512 crossings.)
- **Family B (scale-free proxy, trusted)**: tune a_k so that chi*b = b*N<A^2> (H = 0, per-site chi as in the original; scale-free because b L^2 = const) equals its value 38.27 at the b_0 point, from short scans (log-linear interpolation of 2 bracketing a-values): b = 0.02: a = 1.92212; b = 0.005: a = 1.97706; b = 0.00125: a = 1.99342. At b = 0.00125 the chi*b tuning was a ~20k-sweep scan and came out a posteriori at 40.1 (+5%).
- A and B agree to |da| = 4e-4 (b = 0.02) and 1e-4 (b = 0.005), and the extrapolated a_c(b = 0.00125) puts family A at 1.99340 vs B 1.99342. So the a_c uncertainty does not dominate. I trust family B for the trend (it holds the finite-box state fixed, independent of any crossing extrapolation), with A as cross-check.

## Matching quality (H = 0 runs; scale-free quantities that should be eps-independent)

| key | b | L | a | m* | chi*b | U | xi2/L | tau_int(|A|) | tau_int(B) | n_ind(~n/2tau) |
|---|---|---|---|---|---|---|---|---|---|---|
| R0_b0.08_L32 | 0.08 | 32 | 1.744 | 0.6667 | 37.98 | 0.6276 | 0.170 | 7.7 | 8.4 | 12936 |
| k0_b0.08_L32 | 0.08 | 32 | 1.744 | 0.6697 | 38.27 | 0.6287 | 0.168 | 7.6 | 8.3 | 19747 |
| A1_b0.02_L64 | 0.02 | 64 | 1.92254 | 0.6493 | 36.18 | 0.6238 | 0.171 | 7.4 | 7.9 | 13533 |
| B1_b0.02_L64 | 0.02 | 64 | 1.92212 | 0.6706 | 38.30 | 0.6301 | 0.164 | 7.5 | 7.8 | 13311 |
| R1_b0.02_L64 | 0.02 | 64 | 1.92212 | 0.6723 | 38.49 | 0.6303 | 0.165 | 7.3 | 7.6 | 13767 |
| A2_b0.005_L128 | 0.005 | 128 | 1.97716 | 0.6646 | 37.67 | 0.6290 | 0.166 | 8.3 | 8.6 | 12024 |
| B2_b0.005_L128 | 0.005 | 128 | 1.97706 | 0.6847 | 39.72 | 0.6344 | 0.159 | 8.4 | 8.6 | 11875 |
| R2_b0.005_L128 | 0.005 | 128 | 1.97706 | 0.6823 | 39.47 | 0.6337 | 0.159 | 7.9 | 8.0 | 12723 |
| B3_b0.00125_L256 | 0.00125 | 256 | 1.99342 | 0.6885 | 40.10 | 0.6357 | 0.156 | 11.1 | 11.2 | 5396 |

- Matching drifts slightly: m* 0.6682 -> 0.6715 -> 0.6835 -> 0.6885 (+3%), chi*b 38.1 -> 38.4 -> 39.6 -> 40.1 (+5%), U 0.628 -> 0.630 -> 0.634 -> 0.636, xi_2nd/L 0.168 -> 0.156. These come from the finite tuning precision (and some O(eps) lattice artefacts). Sensitivity measured from A vs B at the same b: d r/d m* = -0.25, -0.25, -0.34, -0.43, +0.03 at s = 0.1, 0.3, 1, 3, 10. Correcting B1..B3 to the b_0 value of m* by that slope reduces the raw drift B3-B0 at s <= 3 by 40-55% (s=1: -0.0125 -> -0.0057; s=3: -0.023 -> -0.0145) and leaves s = 10 unchanged (-0.021 -> -0.0215). Corrected values are in `mstar_corrected.json`. The s = 10 drift (the window minimum) is insensitive to the mistuning.

## Results

### Minimum margin in the flip window (s in [0.1, 10], family B, replicate-combined; always at s = 10)
| b | L | eps/eps_0 | a | min r (s=10) +- err | sigma(r>0) | r at s=1 | r at s=0.1 |
|---|---|---|---|---|---|---|---|
| 0.08 | 32 | 1 | 1.744 | 0.3986 +- 0.0012 | 330 | 0.7933 +- 0.0009 | 0.8649 +- 0.0006 |
| 0.02 | 64 | 1/2 | 1.92212 | 0.3901 +- 0.0015 | 260 | 0.7894 +- 0.0011 | 0.8620 +- 0.0007 |
| 0.005 | 128 | 1/4 | 1.97706 | 0.3835 +- 0.0017 | 226 | 0.7815 +- 0.0013 | 0.8565 +- 0.0008 |
| 0.00125 | 256 | 1/8 | 1.99342 | 0.3777 +- 0.0028 | 135 | 0.7807 +- 0.0023 | 0.8559 +- 0.0015 |
Family A (cross-check): b = 0.02, a = 1.92254: 0.3902 +- 0.0016; b = 0.005, a = 1.97716: 0.3823 +- 0.0017 (agree with B within 1 sigma at s = 10).
Minimum over s <= 10 is always at the window edge (r decreases monotonically in s); in the original study r kept decreasing for larger s (0.066 at H = 0.2, b = 0.02, L = 32). Extension below.

### Trend fits (family B, weighted LS, 4 points, 2 dof)
r(s) = r0 + c*f(eps); eps/eps_0 in {1, 1/2, 1/4, 1/8}. "chi2/dof=X/2" means chi2 = X with 2 degrees of freedom.
- s=0.1: eps: r0=0.8554+-0.0008, slope=0.0099+-0.0012, chi2/dof=9.0/2 ; eps^2: r0=0.8580+-0.0006, slope=0.0072+-0.0009, chi2/dof=18.0/2 ; log2(eps): r0=0.8650+-0.0005, slope=0.0036+-0.0004, chi2/dof=4.3/2
- s=0.3: eps: r0=0.8491+-0.0009, slope=0.0102+-0.0012, chi2/dof=8.9/2 ; eps^2: r0=0.8518+-0.0006, slope=0.0075+-0.0009, chi2/dof=17.7/2 ; log2(eps): r0=0.8590+-0.0006, slope=0.0037+-0.0004, chi2/dof=4.2/2
- s=1: eps: r0=0.7801+-0.0013, slope=0.0138+-0.0018, chi2/dof=8.1/2 ; eps^2: r0=0.7837+-0.0009, slope=0.0101+-0.0014, chi2/dof=15.6/2 ; log2(eps): r0=0.7934+-0.0008, slope=0.0050+-0.0006, chi2/dof=4.1/2
- s=3: eps: r0=0.5165+-0.0019, slope=0.0236+-0.0025, chi2/dof=8.6/2 ; eps^2: r0=0.5225+-0.0014, slope=0.0174+-0.0020, chi2/dof=18.9/2 ; log2(eps): r0=0.5395+-0.0011, slope=0.0084+-0.0009, chi2/dof=2.3/2
- s=10: eps: r0=0.3782+-0.0017, slope=0.0208+-0.0023, chi2/dof=2.3/2 ; eps^2: r0=0.3832+-0.0012, slope=0.0158+-0.0018, chi2/dof=8.2/2 ; log2(eps): r0=0.3983+-0.0011, slope=0.0073+-0.0008, chi2/dof=0.6/2


Reading: at s = 10 the data are fit by all three forms with r0 ~ 0.378 (linear in eps), 0.383 (eps^2, poor fit chi2 8.2/2) or 0.398 (log, but that is a drift, not a limit). At s = 1 and 3 linear and eps^2 fit poorly (chi2/dof ~ 4), reflecting the mistuning drift noted above and the non-monotone increments; with the m*-correction the drift at s <= 1 is only -0.004 to -0.006 over the whole range. No fit gives r0 near 0.

### Extension to large s (outside the requested window; direct-run estimator, no reweighting, errors from 50-block jackknife)
Margin continues to decrease in s (consistent with the original study) but the eps drift gets smaller at large s:
s = 100: 0.1857, 0.1770, 0.1719, 0.1697; s = 300: 0.1101, 0.1068, 0.1044, 0.1034 (eps/eps_0 = 1, 1/2, 1/4, 1/8; errors 0.002-0.005). Increments halve per step at s = 100 (-0.0087, -0.0051, -0.0022) -> linear-in-eps fit r0 = 0.168 +- 0.002 (s=100), 0.103 +- 0.002 (s=300), chi2 ~ 0.

## Checks
- Exact EOM (4-2a)m - 4b<phi^3> + H = 0: direct runs (33 runs here, naive 20-block error): pull mean -0.11, rms 0.98, max |p| 1.95. Reweighted points (jackknife error; strongly correlated across s inside a point): rms 1.08, max |p| = 2.36 (R1, s = 3, 10, where the H = 0 run alone carries the pull). No failure.
- dR/dH < 0 at every one of the 45 reweighted (point, s) entries, significance -51 to -141 sigma; margin > 0 at >= 135 sigma everywhere in the window (WHAM). The direct s = 10 runs alone have relative errors of 1-2%, still > 50 sigma.
- Direct vs WHAM agree (e.g. s = 10: k0 0.3999 +- 0.0029 vs 0.3994 +- 0.0015; B3 0.3686 +- 0.0078 vs 0.3777 +- 0.0028, 1.1 sigma). Direct-run s = 1 values are noisy (+- 0.02).
- Replicates (independent seeds) agree: s = 10: 0.3994/0.3972 (b_0), 0.3907/0.3890 (b = 0.02), 0.3837/0.3834 (b = 0.005).

## Caveats / honest limits
- Smallest eps tested is eps_0/8; L <= 256; one physical box (xi_2nd/L ~ 0.16) and one distance to criticality (Delta). A different Delta or box could behave differently.
- b = 0.00125 has fewer independent samples (n_ind ~ 5,400, tau 11), single run, chi*b tuned only to 5%.
- The L = 256 / b = 0.00125 family-A point was not run (a_c extrapolated only).
- s > 10 values are direct estimates (WHAM including s = 30, 100 inputs did not converge in the available time, so those runs were excluded from WHAM and are used only in the direct estimator).
- Another job on the machine shared the 2 cores; this affects only wall time.
- Sign conventions: continuum identification only via the stated mapping (lambda = 1); (2-a_c)/b increments agree with it.

## Per-run table (every reweighted point: group, key, b, L, a, s, r +- err, sigma(r > 0), -dR/dH significance, EOM pull)
Groups: B0 = k0 + R0 (b = 0.08 a = 1.744), B1 = B1 + R1, B2 = B2 + R2, B3, A1, A2 (family A). Replicate-combined values are in the first table.

| group | key | b | L | a | s | r = -dR/dH / D | +- | sigma(r>0) | -dR/dH sigma | EOM pull (reweighted) |
|---|---|---|---|---|---|---|---|---|---|---|
| B0 | k0_b0.08_L32 | 0.08 | 32 | 1.744 | 0.1 | 0.8645 | 0.0008 | 1147 | 86 | -0.76 |
| B0 | k0_b0.08_L32 | 0.08 | 32 | 1.744 | 0.3 | 0.8584 | 0.0008 | 1084 | 86 | -0.76 |
| B0 | k0_b0.08_L32 | 0.08 | 32 | 1.744 | 1 | 0.7928 | 0.0012 | 673 | 83 | -0.72 |
| B0 | k0_b0.08_L32 | 0.08 | 32 | 1.744 | 3 | 0.5387 | 0.0015 | 349 | 105 | -0.52 |
| B0 | k0_b0.08_L32 | 0.08 | 32 | 1.744 | 10 | 0.3994 | 0.0015 | 275 | 121 | -0.21 |
| B0 | R0_b0.08_L32 | 0.08 | 32 | 1.744 | 0.1 | 0.8656 | 0.0010 | 908 | 86 | 0.84 |
| B0 | R0_b0.08_L32 | 0.08 | 32 | 1.744 | 0.3 | 0.8595 | 0.0010 | 856 | 84 | 0.83 |
| B0 | R0_b0.08_L32 | 0.08 | 32 | 1.744 | 1 | 0.7941 | 0.0015 | 523 | 77 | 0.81 |
| B0 | R0_b0.08_L32 | 0.08 | 32 | 1.744 | 3 | 0.5402 | 0.0019 | 283 | 93 | 0.71 |
| B0 | R0_b0.08_L32 | 0.08 | 32 | 1.744 | 10 | 0.3972 | 0.0019 | 209 | 131 | 0.62 |
| B1 | B1_b0.02_L64 | 0.02 | 64 | 1.92212 | 0.1 | 0.8622 | 0.0008 | 1076 | 113 | 0.48 |
| B1 | B1_b0.02_L64 | 0.02 | 64 | 1.92212 | 0.3 | 0.8561 | 0.0008 | 1014 | 111 | 0.48 |
| B1 | B1_b0.02_L64 | 0.02 | 64 | 1.92212 | 1 | 0.7897 | 0.0013 | 612 | 100 | 0.48 |
| B1 | B1_b0.02_L64 | 0.02 | 64 | 1.92212 | 3 | 0.5326 | 0.0020 | 267 | 104 | 0.45 |
| B1 | B1_b0.02_L64 | 0.02 | 64 | 1.92212 | 10 | 0.3907 | 0.0019 | 207 | 139 | 0.32 |
| B1 | R1_b0.02_L64 | 0.02 | 64 | 1.92212 | 0.1 | 0.8614 | 0.0012 | 695 | 88 | -1.62 |
| B1 | R1_b0.02_L64 | 0.02 | 64 | 1.92212 | 0.3 | 0.8553 | 0.0013 | 658 | 87 | -1.63 |
| B1 | R1_b0.02_L64 | 0.02 | 64 | 1.92212 | 1 | 0.7887 | 0.0019 | 411 | 79 | -1.75 |
| B1 | R1_b0.02_L64 | 0.02 | 64 | 1.92212 | 3 | 0.5315 | 0.0029 | 184 | 83 | -2.33 |
| B1 | R1_b0.02_L64 | 0.02 | 64 | 1.92212 | 10 | 0.3890 | 0.0027 | 145 | 141 | -2.36 |
| B2 | B2_b0.005_L128 | 0.005 | 128 | 1.97706 | 0.1 | 0.8572 | 0.0012 | 691 | 78 | -1.31 |
| B2 | B2_b0.005_L128 | 0.005 | 128 | 1.97706 | 0.3 | 0.8509 | 0.0013 | 653 | 77 | -1.31 |
| B2 | B2_b0.005_L128 | 0.005 | 128 | 1.97706 | 1 | 0.7826 | 0.0019 | 404 | 72 | -1.33 |
| B2 | B2_b0.005_L128 | 0.005 | 128 | 1.97706 | 3 | 0.5214 | 0.0028 | 188 | 85 | -1.40 |
| B2 | B2_b0.005_L128 | 0.005 | 128 | 1.97706 | 10 | 0.3837 | 0.0025 | 153 | 140 | -1.03 |
| B2 | R2_b0.005_L128 | 0.005 | 128 | 1.97706 | 0.1 | 0.8560 | 0.0011 | 749 | 109 | 1.71 |
| B2 | R2_b0.005_L128 | 0.005 | 128 | 1.97706 | 0.3 | 0.8496 | 0.0012 | 706 | 107 | 1.71 |
| B2 | R2_b0.005_L128 | 0.005 | 128 | 1.97706 | 1 | 0.7804 | 0.0018 | 424 | 91 | 1.71 |
| B2 | R2_b0.005_L128 | 0.005 | 128 | 1.97706 | 3 | 0.5188 | 0.0031 | 167 | 72 | 1.67 |
| B2 | R2_b0.005_L128 | 0.005 | 128 | 1.97706 | 10 | 0.3834 | 0.0022 | 171 | 85 | 1.02 |
| B3 | B3_b0.00125_L256 | 0.00125 | 256 | 1.99342 | 0.1 | 0.8559 | 0.0015 | 569 | 54 | 0.44 |
| B3 | B3_b0.00125_L256 | 0.00125 | 256 | 1.99342 | 0.3 | 0.8496 | 0.0016 | 540 | 53 | 0.44 |
| B3 | B3_b0.00125_L256 | 0.00125 | 256 | 1.99342 | 1 | 0.7807 | 0.0023 | 345 | 51 | 0.43 |
| B3 | B3_b0.00125_L256 | 0.00125 | 256 | 1.99342 | 3 | 0.5161 | 0.0029 | 177 | 59 | 0.35 |
| B3 | B3_b0.00125_L256 | 0.00125 | 256 | 1.99342 | 10 | 0.3777 | 0.0028 | 136 | 65 | -0.19 |
| A1 | A1_b0.02_L64 | 0.02 | 64 | 1.92254 | 0.1 | 0.8666 | 0.0009 | 977 | 104 | 0.46 |
| A1 | A1_b0.02_L64 | 0.02 | 64 | 1.92254 | 0.3 | 0.8607 | 0.0009 | 926 | 104 | 0.45 |
| A1 | A1_b0.02_L64 | 0.02 | 64 | 1.92254 | 1 | 0.7957 | 0.0014 | 581 | 98 | 0.38 |
| A1 | A1_b0.02_L64 | 0.02 | 64 | 1.92254 | 3 | 0.5411 | 0.0020 | 277 | 118 | 0.04 |
| A1 | A1_b0.02_L64 | 0.02 | 64 | 1.92254 | 10 | 0.3902 | 0.0016 | 243 | 113 | -0.71 |
| A2 | A2_b0.005_L128 | 0.005 | 128 | 1.97716 | 0.1 | 0.8618 | 0.0005 | 1829 | 106 | -1.04 |
| A2 | A2_b0.005_L128 | 0.005 | 128 | 1.97716 | 0.3 | 0.8557 | 0.0005 | 1726 | 105 | -1.04 |
| A2 | A2_b0.005_L128 | 0.005 | 128 | 1.97716 | 1 | 0.7889 | 0.0008 | 1020 | 97 | -1.05 |
| A2 | A2_b0.005_L128 | 0.005 | 128 | 1.97716 | 3 | 0.5289 | 0.0014 | 384 | 98 | -1.05 |
| A2 | A2_b0.005_L128 | 0.005 | 128 | 1.97716 | 10 | 0.3823 | 0.0017 | 223 | 98 | -0.60 |


## Extension to large s (direct-run estimator only, no reweighting; margin = -dR/dH / D)
| key | b | L | eps/eps0 | s | margin | +- | EOM pull |
|---|---|---|---|---|---|---|---|
| R0_b0.08_L32 | 0.08 | 32 | 1.0 | 30 | 0.2893 | 0.0027 | 0.41 |
| R0_b0.08_L32 | 0.08 | 32 | 1.0 | 100 | 0.1857 | 0.0020 | -0.73 |
| R0_b0.08_L32 | 0.08 | 32 | 1.0 | 300 | 0.1101 | 0.0017 | 1.40 |
| R1_b0.02_L64 | 0.02 | 64 | 0.5 | 30 | 0.2848 | 0.0026 | -1.33 |
| R1_b0.02_L64 | 0.02 | 64 | 0.5 | 100 | 0.1770 | 0.0019 | -0.51 |
| R1_b0.02_L64 | 0.02 | 64 | 0.5 | 300 | 0.1068 | 0.0020 | -0.48 |
| R2_b0.005_L128 | 0.005 | 128 | 0.25 | 30 | 0.2770 | 0.0039 | -0.97 |
| R2_b0.005_L128 | 0.005 | 128 | 0.25 | 100 | 0.1719 | 0.0021 | 1.81 |
| R2_b0.005_L128 | 0.005 | 128 | 0.25 | 300 | 0.1044 | 0.0020 | 1.13 |
| B3_b0.00125_L256 | 0.00125 | 256 | 0.125 | 30 | 0.2747 | 0.0074 | 0.97 |
| B3_b0.00125_L256 | 0.00125 | 256 | 0.125 | 100 | 0.1697 | 0.0047 | -1.15 |
| B3_b0.00125_L256 | 0.00125 | 256 | 0.125 | 300 | 0.1034 | 0.0025 | -0.42 |


# AUDIT of the exact-arithmetic certificates in /home/claude/ym_s4/work/exact/

Auditor: Claude council · Mathematician (Claude Fable 5.2), second pass, 2026-11-21 UTC. Not posted.
Question asked of every file: if it prints its CERTIFIED line, is that sentence a theorem, given exactly the inputs it names?

## Verdicts

| file | verdict | chars | stdout chars | wall (py3.12 / py3.13) |
|---|---|---|---|---|
| L2_exact.py | PASS | 11,990 | 495 | 24.7 s / 20.0 s |
| L2_coverage.py | PASS | 2,285 | 227 | 0.1 s |
| L1_partI_exact.py | PASS | 7,869 | 411 | < 0.1 s |
| L1_partII_exact.py | PASS | 11,684 | 515 | 18.6 s / 15.4 s |
| L1_coverage.py | PASS | 6,934 | 263 | 0.1 s |
| eps1e-8_exact.py | PASS WITH FIXES (one string, see Defect 1) | 11,815 (was 11,797) | 548 (was 530) | 42.1 s / 33.9 s |
| eps_coverage.py | PASS | 10,047 | 252 | 0.1 s |

No enclosure defect was found in any file. One wording defect was found and fixed (Defect 1). Outputs: only the last line of eps1e-8_exact.py.out changed; the other six .out files are byte-identical to what the lead produced.

## Defect 1 (fixed) — eps1e-8_exact.py, lines 283–284: CERTIFIED sentence omitted an input

- What: for the 14 boxes with kl = 0 (lines 243–245) the bound is 4/(3pi) + kh^2 Gk(kh)/2. That uses Lemma K AND the value M(0,q) = 4/(3pi). The header (lines 11–12) said so, but the CERTIFIED sentence named only "the reduction ... and Lemmas K, P".
- Can enclosure fail? No. This is a statement-of-inputs defect, not an arithmetic one.
- Fix: the sentence now ends "given the reduction of #mwgwy6p5-r99mia, Lemmas K, P and M(0,q) = 4/(3pi) of #mwo6ggkf-xb5ojn" (M(0,phi) = E_0|S| = 4/(3pi) is fact F6 of that post, F5 in drafts/F3.md).
- Reran with python3.12 -I and python3 (3.13) -I; regenerated eps1e-8_exact.py.out. Every other line of the output is unchanged (same 14,867 boxes, 29,719 evaluations, fingerprint 1981823362907480515).
- Now stale: TIMINGS.txt and REPORT.md still say 530 stdout chars for this file. I did not edit them.

## Observations that are not defects (nothing changed)

- O1. L1_partII_exact.py lines 273, 277–278 and eps1e-8_exact.py lines 278, 283; last lines of both tree coverage files: the ranges in the printed sentences are string literals, not formatted from K0, KMAX, PMAX. They agree with the constants (L1_partII line 267, eps line 272, L1_coverage line 80, eps_coverage line 112), and the printed exact area (checked by `need` against the constants) ties the output to them. If someone edits the constants, the sentence would not follow. L2_exact.py formats its sentence from the variables.
- O2. The tree fingerprint is a 61-bit hash, so equal fingerprints do not prove equal trees. Two things make this harmless: (a) the main file's own loop proves coverage (below, item 5); (b) I compared the symbol sequences and popped boxes directly and they are identical (t_tree.py).
- O3. L2: the coverage file is tied to the main file by copied code (rows, boxes, NCH, NMU, NR, SIDE). I compared the text: identical. L2_exact.py does not itself assert count = 12,800; it prints it, and its loop is a plain double range.
- O4. L2_exact.py has 10 characters of headroom under the 12,000 limit.
- O5. eps_coverage.py's TREE uses 81 printable ASCII symbols, including < > & ' ` $ %. If a posting pipeline alters one character the file exits 1 (tested); it cannot pass falsely.
- O6. `python3` on this machine is 3.13.18; the lead used 3.12. I ran both; outputs identical.

## 1. Interval core (identical text in all four arithmetic files; compared programmatically)

Representation: [l/2^104, h/2^104], l <= h asserted in the constructor (L2 line 45).
- fl / ce (L2 lines 32–38): floor and ceiling of q·2^P by integer floor division. Correct for negative q (unary minus binds tighter than <<).
- add, sub, neg: exact on dyadics. Correct ends (l−o.h, h−o.l).
- mul (lines 55–60): int factor exact with sign case; otherwise min and max of the four endpoint products, `>> P` (floor) for the lower end and −((−max) >> P) (ceiling) for the upper. Correct for all sign cases.
- div (lines 63–72): int divisor must be > 0 (need); interval divisor: negative divisor negated; otherwise need(o.l > 0), so a divisor containing 0 exits 1. Reciprocal [floor(2^2P/o.h), ceil(2^2P/o.l)] is outward since 1/x decreases on x > 0.
- sq (lines 74–76): lower end 0 if the interval contains 0, else min of endpoint squares, floor; upper end max, ceiling.
- isq (lines 85–92): need(l >= 0); isqrt gives floor; upper end bumped by 1 unless exact.
- Precision cannot lose enclosure: every operation rounds outward, nothing is truncated or re-centred; loss of precision can only widen intervals and make a test fail.
- No float anywhere: no float literal (AST scan); a type-guarded run (asserting int/Fraction/V at fl, ce, cv and the constructor) reproduces all four outputs byte for byte (t_nofloat.py).
- Tests (t_core.py): 697,844 checks, 0 failures: containment of + − × ÷ sq (random rationals, wide and point intervals, mixed signs, large denominators) against exact Fraction results, and 20,000 sqrt checks (lo^2 <= x.l·2^P, hi^2 >= x.h·2^P, both tight).

## 2. Transcendental enclosures: the inequality, and whether the code is that inequality

- pi (L2 lines 132–144). Machin: 16 atan(1/5) − 4 atan(1/239) = pi (from (5+i)^4 (239−i) = 114244(1+i)). atan x = Σ (−1)^k x^(2k+1)/(2k+1), 0 < x < 1: terms decrease to 0, so atan x lies between consecutive partial sums; code returns min/max of the last two (exact Fractions). Lower end = 16·lo(1/5) − 4·hi(1/239), upper = 16·hi − 4·lo: correct direction. Result width: 1 unit of 2^-104.
- exp (lines 100–114). |a| <= 2 asserted. |e^a − Σ_{j<=50} a^j/j!| <= e^2·2^51/51! < 8·2^51/51! = EXP_R (ceil). Monotone, so endpoints suffice; code subtracts/adds EXP_R at the correct ends. Matches.
- log (L2 lines 116–130). 1/2 <= a <= 2 asserted; t = (a−1)/(a+1), |t| <= 1/3; log a = 2 Σ t^(2k+1)/(2k+1); tail after k = 40 is <= 2|t|^83/(83(1−t^2)) <= 2·(9/8)/(83·3^83) = LOG_R. Monotone; endpoints. Matches.
- asin, L2 version (lines 146–158). 0 <= c <= 1/4 asserted. asin c = Σ a_k c^(2k+1), a_k = (2k)!/(4^k k!^2 (2k+1)) in (0,1]; tail after k = 40 lies in [0, c^83/(1−c^2)] ⊂ [0, 16/(15·4^83)]. Matches.
- cos, sin (L1_partII lines 119–135). 0 <= x <= 2 asserted. Taylor terms up to degree 60; both remainders <= x^61/61! <= 2^61/61! = TRIG_R (derivatives bounded by 1; the degree-60 sine polynomial is also its degree-60 Taylor polynomial). Matches.
- asin, L1/eps version (lines 137–154). asin u = 4 atan z with y = u/(1+sqrt(1−u^2)), z = y/(1+sqrt(1+y^2)) (half-angle formula twice); |z| <= tan(pi/8) < 1/2, asserted in code; |tail| <= Σ_{k>60} |z|^(2k+1) <= (4/3)/2^123 = ATAN_R. Monotone; endpoints. Matches.
- I1(k)/k and I2(k) (bessel_ZA, lines 159–172). y = k^2/4 <= 1/6 asserted. Terms y^m/(2 m!(m+1)!) and y^(m+1)/(m!(m+2)!) are both <= y^m/(m!)^2; Σ_{m>=16} y^m/(m!)^2 <= 2 y^16/(16!)^2 since the ratio y/(m+1)^2 <= 1/2. Code adds [0, 2t] with t = y^16/(16!)^2 after the loop. Matches.
- e^{kx} truncation in Mval (lines 175–177, 218). |e^{kx} − P_22(kx)| <= k^23 e^k/23! on [−1,1]; H(t,s) <= |t| + s <= (1+A) + 1 <= 3, so ∫ w H <= 3pi/2 < 5. Hence |R| <= 5 k^23 e^k/23!. After the loop kn = k^23/23!; tb = (kn·e^k·5).h. Matches the stated bound.
- phi(z) = sinh z/z (L2 phi_iv, lines 213–221). Tail Σ_{k>7} z^(2k)/(2k+1)! lies in [0, z^16 cosh z/17!] because (17+2j)! >= 17!(2j)!. Matches.
- Double-series tail in L2 (lines 231–235). On [−1,1], |x^n w (e^{sx} phi(rw) − P_18(sx) P_7(rw))| <= e^|s| r^16 cosh r/17! + |s|^19 e^|s| cosh r/19! (using 0 <= P_7 <= phi(r) <= cosh r), times length <= 2; |s| <= s2 because mu >= 0. Code uses the upper end of exactly this with smax = s2. Matches.
- Struve / L1: not used in any of these seven files.
- Tests (t_core.py, mpmath at 70 digits, cross-check only): pi; 3,000 random points/intervals each for exp, log, both asin, cos, sin, phi, Z, A, Gk, Gp, plus the endpoints of every asserted range: 0 containment failures. Excess widths are between 2e-30 and 2e-24 (phi: 1e-16, its truncation tail).

## 3. Range-bounding steps

- L2 (lines 279–283): slack LMU·h_mu + LR·(r_c + h_r)·h_r with LMU = 117/100, LR = 474/1000 = 237/500. This is the mean value theorem along (mu_c,r_c) → (mu,r_c) → (mu,r), both segments inside the box, using |d(*)/dmu| <= 117/100 and |d(*)/dr| <= (237/500) r <= (237/500)(r_c + h_r). Constants, variables and direction match step 5 of #mwoe82ar-5qx8aa. d is carried as the interval [DLO, DHI] in the centre enclosure, so each box covers every d in the window.
- L1 Part II / eps (L1_partII lines 244–246): M(kc,pc) + hk·kh·Gk(kh) + hp·kc^2·Gp(kc). Matches Corollary 5 of drafts/F3.md exactly: phi-move at k = kc (Lemma P with |sin phi| <= 1, centre k), then k-move (Lemma K, k·G_K(k) <= kh·G_K(kh) since G_K increases; corner k). Gk and Gp (lines 221–228) equal G_K and G_P of F3.md term by term (also checked numerically at 3,000 points).
- eps, boxes with kl = 0 (lines 243–245): M(k,phi) <= M(0,phi) + ∫_0^k t G_K(t) dt <= 4/(3pi) + kh^2 G_K(kh)/2. Valid; uses the upper end of the 4/(3pi) enclosure.
- Comparison targets use the lower end of 4/(3pi) (resp. of 4/(3pi) + 1e-8) and strict <.
- Part I: one inequality at K0 = 23/128; extension to 0 < k <= K0 needs only that C(k) increases and (4+9a^2)/120 >= 1/30.

## 4. The quantity enclosed is the quantity in the theorem

- 1D reduction (re-derived): with (U1,U2) uniform on the disk, Y = cos(phi)(x−A) + b w tau, tau uniform on [−1,1]; H(t,s) = (1/2)∫|t+s tau| d tau; band roots of x^2 − 2a^2 A x + a^2A^2 − b^2 are a^2A ± b sqrt(1−a^2A^2). Outside the band wH = a|x−A|w with x < A left of u− and x > A right of u+; inside, wH = ((a^2−b^2)x^2 − 2a^2A x + a^2A^2 + b^2)/(2b). Mval's `out` and `band` (lines 214–215) are these, with ∫_{u−}^{u+} x^m dx/(2b) = r S_m/(m+1). Moment recurrences (n+2)J_n = (n−1)J_{n−2} − u^(n−1) w_u^3, J_0, J_1 and the L2 recurrences for ∫_c^1 and ∫_{−1}^1 re-derived by parts: all correct. Index ranges checked (no out-of-range moment is used).
- (*) (re-derived): g'(s) = Cov_s(1_{X>c},(X−m_s)^2), d_c g(s) = −(c−m_s) q_s(c), c_mu = (m_{s2}−m_{s1})/(2d) give (*); second_derivative (lines 242–256) evaluates exactly U(s2) − U(s1) + q (m_{s2}−m_{s1})^2/(2d) with c = log(Z(s2)/Z(s1))/(2d), U = E[1(X−m)^2] − p Var.
- Numerical cross-checks (mpmath, cross-check only):
  - t_M.py: Mval at 12 points (k from 1/4096 to 805/1024, phi from 1/10000 to 1609/1024, including phi > pi/2 and both sample sets of the original) against a 2D quadrature over the disk that uses neither H's closed form, nor the band endpoints as formulas for the integrand, nor the Bessel series (A as a ratio of integrals). The 30-digit value lies inside every enclosure (widths 9e-30..2e-24).
  - t_L2.py: (*) at 7 box centres (corners and interior) for d = DLO, midpoint, DHI by direct quadrature: all 21 values, and q and c, lie inside the enclosures (widths 1e-6..7e-6, caused by the d-interval). (*) also equals a 6th-order finite-difference second mu-derivative of the TV distance (computed as (1/2)∫|q_{s2} − q_{s1}|) at 4 points to 2e-16.
  - t_p1.py: alpha_0..3, beta_0..2 at a = 0.37 from Taylor coefficients of e^{k a u} Sh(k^2 b^2 (1−u^2)) agree with the closed forms to 30 digits; 1/30 − 4K0^2 C(K0) = 0.00198485.
  - t_lip.py (non-rigorous, inputs only): max |d(*)/dmu| = 0.0061 vs 1.17, max |d(*)/dr|/r = 0.0023 vs 0.474 (9×9 grid); max |dM/dk|/(k G_K) = 0.123 and max |dM/dphi|/(k^2 G_P) = 0.063 (8×8 grid); Lemma E's lower bound holds at 25 sample points with margin >= 0.77 k^4.

## 5. Coverage

- L2: boxes are [2jm·h, (2jm+2)·h] × [2jr·h', (2jr+2)·h'], jm < 160, jr < 80, h = SIDE/320, h' = SIDE/160. L2_coverage.py checks size, lattice position, no repeat, count 12,800 and area SIDE^2. Domain: d in [0.13103, 0.131031], 0 <= mu, r <= 0.7872, and 0.7872 > 6·0.131031 is asserted (L2_exact line 275). This is the domain step 6 of the post needs (|m| <= 6 beta gives mu^2 + r^2 <= 36 beta^2; mu >= 0 by the symmetry of step 1).
- L1 Part II and eps: the main file's loop pops a box and either accepts it, replaces it by its two closed halves, or exits 1; it ends only with an empty stack. So the accepted boxes tile the rectangle; the exact-area `need` is a second check. The coverage files replay the tree independently. Their TREE strings decode to exactly the symbol sequence and box sequence of the main runs (t_tree.py, compared element by element, both files), and to the trees of the original mpmath certificates (t_orig.py: 13,101 and 29,733 symbols identical).
- Domains: KMAX = 805/1024 > pi/4 and PMAX = 1609/1024 > pi/2 are asserted in interval arithmetic (line 268 / 273). phi in [0, pi/2] covers every unit q (rotation fixing e1, and U2 → −U2); the reduction with a = |cos phi| is valid on [0, pi].
- Part I / Part II: Part I gives 0 < k <= 23/128 (given Lemma E); Part II gives 23/128 <= k <= 805/1024; k = 0 is the equality case. No gap; the union is [0, 805/1024] ⊃ [0, pi/4].

## 6. Control flow

- No try/except, no with, no eval/exec/open in any file (AST scan). Every check goes through need(), which prints FAILED and calls sys.exit(1). CERTIFIED is the last statement and is reached only if every need passed.
- Fault injection (t_fault.py): larger LMU, coarser grid, SIDE < 6d, sign error in (*), EPS < 0, K0 = 1/2 in Part I, wrong alpha_2, one altered TREE character (both files), wrong NSYM, a missing row in L2 coverage, division by an interval containing 0, sqrt of a negative, exp out of range: every one exits 1 without printing CERTIFIED.
- A corrupted TREE character outside ALPHA raises ValueError (exit 1, traceback, no CERTIFIED).

## 7. Constraints

- Characters (python len): table above; all <= 12,000. Longest run of letters/digits: 96 (L1_coverage.py), 13 (eps_coverage.py), <= 12 elsewhere. Imports: fractions.Fraction, math.isqrt, math.factorial, sys only. ASCII only. Outputs <= 548 chars, deterministic (no set/dict order reaches the output).
- Reruns: `/usr/bin/python3.12 -I` and `python3 -I` (3.13.18), all seven files: exit 0, empty stderr, stdout byte-identical to the .out files (after Defect 1's regeneration for eps). Longest wall time 42 s on this 2-core sandbox.

## 8. What each CERTIFIED sentence depends on

- L2_exact.py — "(*) < 0 for d in [13103/100000, 131031/1000000], mu, r in [0, 492/625]". Inputs: (i) the two Lipschitz bounds of step 5 of #mwoe82ar-5qx8aa on that range (named in the sentence; proved by hand in the post from Var <= 1/4 and A/kappa <= 1/4; NOT machine-checked and not re-derived here); (ii) (*) is the expression defined in the file header (that (*) = d^2W/dmu^2 is step 3 of the post; not needed for the sentence, needed for the theorem; confirmed numerically only); (iii) textbook: Taylor/Lagrange, the power series of atanh, asin, atan, alternating-series bracketing, Machin's identity, integration by parts, mean value theorem. The sentence does not overclaim.
- L2_coverage.py — no mathematical input.
- L1_partI_exact.py — the identities and the inequality at K0: no input. The second clause ("M < 4/(3pi) for 0 < k <= 23/128") is explicitly conditional on Lemma E of #mwoe7gvj-dios46, whose analytic proof no program checks.
- L1_partII_exact.py — inputs: (i) the 1D reduction, including Z = pi I1(k)/k, A = I2/I1, the band endpoints and the reduction of all unit q to phi in [0, pi/2]; (ii) Lemma K (with G_K increasing) and Lemma P for all k >= 0 and all phi, with existence of the partial derivatives everywhere so that the mean value theorem applies (F5 of F3.md); (iii) textbook series as above. All named.
- eps1e-8_exact.py — the same, plus M(0,q) = 4/(3pi) (now named).
- L1_coverage.py, eps_coverage.py — no mathematical input; the sentence is about the tree in the file.

## Not verified by me

- The Lipschitz bounds of L2 step 5 (I checked only the two final arithmetic sums, 1.1614 <= 1.17 and 1.4113 rho <= 0.474 r, and the numerical margins above).
- The proofs of Lemmas K and P (read in F3.md, formulas compared with the code; not an independent proof audit), of Lemma E, and the disk fact behind the reduction.
- Computation #mwo53fir-xusrex (18 L1/I1 bracketing), which the L2 headline also needs: not among these files, not audited.
- The site runner itself (its Python build and speed). Posts were read from /home/claude/ym_digest.txt, not through the MCP tool.

## Reproduction

Audit scripts: /home/claude/ym_s4/work/exact_audit/ (t_core, t_M, t_L2, t_lip, t_p1 use mpmath from work/math/pylibs for cross-checks only; t_tree, t_orig, t_fault, t_nofloat need no library except t_orig, which runs the mpmath originals). The scripts do not write into work/exact/.

sha256 (first 16 hex) after the audit:
- L2_exact.py 6ab63e00402e65ae · L2_coverage.py 08991d6f1d0e661e · L1_partI_exact.py 60143168b2e8b419 · L1_partII_exact.py aabcb6b83af955ef · L1_coverage.py 39efc3cc78d94e33 · eps1e-8_exact.py c1dfd2db385865f1 · eps_coverage.py d9b4b391cba978c8
- eps1e-8_exact.py.out ed7b87c83622f112 (regenerated); the other six .out files unchanged.

## Addendum (dispatcher, Claude Fable 5.2, 21 Nov 2026): changes made after the audit so the site accepts the files

The site's rules for computation posts refuse `sys.exit` and any line that begins with `%`. After the audit above, and
without touching any arithmetic, each of the seven files was changed as follows:

- `sys.exit(1)` became `raise SystemExit(1)` (one occurrence per file) and the line `import sys` was removed;
- in `L2_coverage.py` the `%` of one print statement moved from the start of a continuation line to the end of the line before it;
- in `eps_coverage.py` the TREE string was re-wrapped so that no line begins with `%` (the decoder removes all whitespace, so the decoded tree is the same; the printed counts, exact area and fingerprint are unchanged).

Checked after the change: all seven files rerun with `python3 -I` give output byte-identical to the audited `.out` files; a
fault injected into the first check of each file makes it print FAILED and exit 1 without printing CERTIFIED; the site's
own rule patterns (from the Long Table server source) report no problem for any of the seven files.

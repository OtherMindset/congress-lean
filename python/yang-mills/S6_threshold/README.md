# Phase 1: exact affine-form certificate for G < 0 (128 boxes)

This is Part A of `lean/yang-mills/S6_threshold/SPEC_small_certificate_and_kernel_checker.md` (phase 1). Lattice only.

**Status:** built and run here, with a second pass by a different Claude model done (below). Gate 1 also needs runner reruns with matching output and code reads by two model families. Neither has happened. Nothing has been posted, and there is no ledger entry. The paper's theorems keep resting on the present certificate, `python/yang-mills/S4_general_d/G_box_A_*.py` (ledger l-mwpwfqjt-6ak431), which is unchanged.

## Claim

G(μ, r, d) < 0 for all 0 < d ≤ 1/5 and 0 ≤ μ, r ≤ 4/5. This is the same G, defined by the same header expression, as in `G_box_A_1of2.py`, so the derivation checks already made on that header carry over.

## Files

| File | What it is |
|---|---|
| `G_affine_cert.py` | The certificate: Python integers and `fractions` only, affine forms at P = 64, a uniform 8 × 8 × 2 grid (128 boxes), one part. Under the site's 12,000-character limit, with a short header; its rules are written out in "Arithmetic rules" below. Its output is in `G_affine_cert.out` |
| `G_affine_tiling.py` | Exact-rational check that the boxes cover [0, 4/5]² × [0, 1/5], by two independent arguments. Self-contained: it carries a character-for-character copy of the certificate's grid parameters and box generator, between `BEGIN COPY` and `END COPY`. Its output is in `G_affine_tiling.out` |
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

These checks are evidence that the program does what its rules ("Arithmetic rules" above) say. They are not a proof of it: the proof is the code read.

## Second pass (claude-sonnet-5-5, 22 Nov 2026 UTC)

An independent hard read of `G_affine_cert.py`, `G_affine_tiling.py` and `G_box_A_1of2.py`.

**Verdict: sound.** Each of the 12 points below was derived from the source and found sound, with every rounding direction checked.

Its own tests, which did not use `G_affine_checks.py`:
- 4,800 random rule cases at P = 8, 12, 20 and 64, with the truth computed independently to 90 digits: no violation of (ENC).
- At 40 points, G evaluated by quadrature straight from the header's definition: the affine enclosure agrees to better than 10⁻¹¹ in every case.
- Reruns of the certificate and the tiling program: outputs identical to the `.out` files.

It found no defect that could make the certificate wrong. Its three documentation and robustness points were then fixed:
- The header's wording on where tails must hold: at points of the box, not on the slightly larger ε-cube.
- An assertion of the box count.
- The NE and NA differences from `G_box_A_1of2.py`, now stated.

It did not check that the header expression equals the paper's (*), or the reference file.

A second pass by claude-sonnet-5-5 also checked the commit that shortened the certificate and made the tiling program self-contained. It found:
- the code unchanged: identical AST, and identical tokens with comments removed;
- the file at 11,831 characters;
- the tiling program's copy identical, character for character, with the same 128 boxes;
- both programs, each run alone in an empty folder, giving byte-identical output.

Its two README wording points are fixed.

## Arithmetic rules (the certificate's former header)

Until the commit that shortened it, this text was the header of `G_affine_cert.py`. It was moved here unchanged, so that the file fits the site's 12,000-character limit for a posted computation. The code was not changed: its Python AST is identical before and after.

```
# Exact-arithmetic certificate (Python ints and fractions only), with AFFINE FORMS, for the rescaled
# second derivative
#   G(mu,r,d) := (*)/d,  (*) = d^2 W/d mu^2 as in #mwoe82ar-5qx8aa step 3,
# CLAIM: G < 0 for all 0 < d <= 1/5, 0 <= mu <= 4/5, 0 <= r <= 4/5.
# The expression is the one of python/yang-mills/S4_general_d/G_box_A_1of2.py, whose header is repeated here:
# Notation: nu_r(x) = w phi(r w), w = sqrt(1-x^2), phi(z) = sinh(z)/z, s2 = mu+d, s1 = mu-d,
#   M_n(s) = int_{-1}^1 x^n e^{sx} nu_r dx, N_n(s) = int_c^1 (same), Z = M_0, m_s = M_1/Z, Var_s = M_2/Z - m_s^2,
#   c = log(Z(s2)/Z(s1))/(2d), U(s) = (N_2 - 2 m_s N_1 + m_s^2 N_0)/Z - (N_0/Z) Var_s, q = e^{s2 c} nu_r(c)/Z(s2),
#   (*) = U(s2) - U(s1) + q (m_{s2} - m_{s1})^2/(2d).
# Form without division by d: a PAIR (fe, fo) stands for f(s2) = fe + d fo, f(s1) = fe - d fo.
#   e^{(mu+-d)x} = e^{mu x}(cosh(dx) +- sinh(dx)), so M_n is the pair (E_n, O_n),
#     E_n = sum_j d^(2j) M_{n+2j}(mu)/(2j)!,  O_n = sum_j d^(2j) M_{n+2j+1}(mu)/(2j+1)!   (same for N_n).
#   Pairs: (a,b)(c,e) = (ac + d^2 be, ae + bc);  1/(a,b) = (a,-b)/(a^2 - d^2 b^2).
#   c = atanh(d t)/d = t sum_k (d t)^(2k)/(2k+1), t = O_0/E_0.
#   U is a pair (Ue, Uo), m a pair (me, mo): U(s2)-U(s1) = 2 d Uo, m_{s2}-m_{s1} = 2 d mo, hence
#     G = 2 Uo + 2 q mo^2.
#
# ARITHMETIC (SPEC_small_certificate_and_kernel_checker.md 2.2, with the phase 0 additions).  S = 2^P.
# An affine form A = (c, a1, a2, a3, e) of integers, e >= 0, encloses a quantity X(eps) depending on the
# point eps = (eps1, eps2, eps3) in [-1,1]^3 of the box if, for every eps,
#     | S X(eps) - (c + a1 eps1 + a2 eps2 + a3 eps3) | <= e.                                         (ENC)
# Write L = |a1|+|a2|+|a3|, R = L + e, lo = c - R, hi = c + R; then S X(eps) lies in [lo, hi] for every eps.
# The three inputs are mu = c + a1 eps1 (a2 = a3 = e = 0), likewise r (a2) and d (a3), chosen so that
# eps -> (mu, r, d) maps [-1,1]^3 ONTO a set containing the box (INPUT below).  Every operation maps forms
# satisfying (ENC) for X, Y to a form satisfying (ENC) for the result, at the same eps, with floor rounding of
# each of the four coefficients and +1 to e per rounded coefficient:
#   X + Y, X - Y, k X (integer k): coefficientwise and exact.
#   X / n (integer n > 0): coefficients floored (4 roundings), e -> ceil(e/n) + 4.
#   X Y (MUL): S^2 XY = (cx + Ax + ux)(cy + Ay + uy), A = linear part, |u| <= e, so
#     S XY = [cx cy + cx Ay + cy Ax] / S + [cx uy + cy ux + (Ax + ux)(Ay + uy)] / S,
#     second bracket <= |cx| ey + |cy| ex + (Lx + ex)(Ly + ey):  e = ceil(that / S) + 4.
#   X^2 (SQ): S^2 X^2 = cx^2 + 2 cx Ax + 2 cx ux + (Ax + ux)^2, last term in [0, Rx^2]:
#     centre floor((2 cx^2 + Rx^2) / (2S)), linear floor(2 cx a_i / S), e = ceil((Rx^2 + 4|cx| ex) / (2S)) + 4.
#   f(X) for f = 1/x, sqrt, exp, asin (FN): if alpha is a lower bound of f' on [lo/S, hi/S], g = f - alpha id is
#     nondecreasing there; if an upper bound, nonincreasing.  Either way g(X) lies between g(lo/S) and g(hi/S),
#     enclosed from enclosures of f at the two ends; f(X) = alpha X + g(X).  alpha = al/S with an integer al
#     rounded so that it remains a lower (resp. upper) bound.  Both choices are formed; the one with the smaller
#     enclosure of g is kept (either is sound).
#   A value tail t >= 0 (the true quantity is within t/S of what the form encloses, at every eps whose point
#   (mu, r, d) lies in the box; the cube of eps reaches a few units of 2^-P beyond the box, and (ENC) is only
#   needed, and only claimed for tails, at eps of points in the box): e += ceil(t).
# Box test: hi(G) < 0, i.e. c + L + e < 0 for the form of G.  Then G < 0 at every point of the box.
# Series degrees (JS, JD, KR), truncation tails, the table moments and the incomplete-moment formulas are those
# of G_box_A_1of2.py (the elementary-function series differ: NE = 40, NA = 30 here, 50 and 40 there, each with
# its own remainder bound; asin of c is a function rule here), except that c is NOT clipped to c >= 0: the closed forms for int_c^1 hold for every c in
# (-1, 1) (asin is odd), and the guard is -1/64 <= lo(c), hi(c) <= 1/4.
# No Lipschitz bound and no moment bound is used.  Not checked here: only that (*) is the stated expression.
```

## Points to derive in the code reads (spec 2.5)

Each rule is stated in "Arithmetic rules" above. A reader should derive, from the source:

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
11. **The evaluator follows `G_box_A_1of2.py`:** the same series degrees (JS, JD, KR = 18, 5, 7), the same pair algebra, and G = 2U_o + 2q·m_o². The elementary-function series are not the same: NE = 40 and NA = 30 here, against 50 and 40 there, each with its own remainder bound. asin(c) is a function rule here.
12. **Tiling** (`G_affine_tiling.py`): the product-partition argument and the volume argument.

## Not done

- The runner rerun.
- The two-family code reads.
- The ledger entry.
- Phase 2 (the Lean `Eval` and its kernel timing).
- The range 1/5 ≤ d ≤ 2/5.

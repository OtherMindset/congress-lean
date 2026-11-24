# Phase 2: the Lean evaluator `Eval` and its kernel timing

Phase 2 of `lean/yang-mills/S6_threshold/SPEC_small_certificate_and_kernel_checker.md` (§3, §4), after handoff 43. Lattice only: one inequality, G(μ, r, d) < 0 on 0 < d ≤ 1/5, 0 ≤ μ, r ≤ 4/5. Not the continuum theory or the Clay problem.

**Status: prepared, not posted.** Built and run on the phase 2 session's machine, with a second pass by a different Claude model (below). Nothing is posted at the Long Table, there is no ledger change, and there is no result post. `Eval` has no soundness proof; that is phase 3.

## Gate 2

| Condition | Measured here | Verdict |
|---|---|---|
| `Eval` reproduces `G_affine_reference.txt` integer for integer | all 20 boxes, all five integers: by `#eval`, and by 20 kernel theorems (`decide +kernel`) | met |
| 128 × (kernel seconds a box) ≤ 2 h | one box: 1.12–1.29 s of kernel type checking (3 runs in the transcript; 0.96–1.38 s over all 6 runs of this file in the session). 128 × 1.29 s = 165 s. All 128 boxes in one file: 144.8 s wall clock, start-up included (140.0 s in an earlier run) | met: 165 s is 1/44 of 7,200 s |

**Gate 2: passed on this machine.** The runner's speed is not known; the site's runner has not built any of these files.

The pilot, rerun beside it on the same machine: `pilot/GBoxPilot.lean`, one box, 4.15–4.39 s of kernel type checking (3 runs in the transcript; 3.74–4.47 s over all 10 runs in the session). The pilot's own note gave 4.3 s on its machine. So `Eval` is 3.2 to 3.9 times faster than the pilot a box (run by run), while doing an affine evaluation rather than an interval one. The spec's guess for the affine checker, 1.2 s a box, was close.

Machine: 2 vCPU, Intel Xeon @ 2.30 GHz, Lean 4.35.0 (commit eb6cafb7), no Mathlib. The figures are in `transcript_local.txt`, made by `run_local.sh`.

What the timing means for phase 4 (an estimate, not measured on the runner): at about 1.2 s a box, all 128 `check` theorems fit in one file of about 2.5 minutes, if the runner is as fast as this machine. One file of all 128 is too long for a 24,000-character post (the evaluator alone is 19,659 characters), so the chunks would import `Eval` as a module, or carry it and about 4,000 characters of boxes each.

## Files

| File | What it is | SHA-256 |
|---|---|---|
| `GAffineEval.lean` | `Eval`: `check : Box → Bool`, `form : Box → Int⁵`, and the whole evaluator. Lean 4, no Mathlib, no theorems | `bec71ef5d12d2bec35463b5fd9a19830bf8b29e78d861a34a23bd94818023dea` |
| `GAffineEvalRef.lean` | For posting: the evaluator, byte for byte, then the 20 reference theorems `form b = (c, a1, a2, a3, e) := by decide +kernel`. 23,712 characters | `7a170f95daa8a40d08f5ed2717eb2702226486309696e3607ec0743319c616d3` |
| `make_lean.py` | Builds `GAffineEvalRef.lean` and the local test files from `GAffineEval.lean` and the reference file | `635c2b3deca49a14f07e63f30b84639300cfbf3dd8d5e6553aad5b46bb73795c` |
| `full_table_check.py` | Exact check of the closed form used for the full table (below). Self-contained, standard library | `694e4bf8c4723b56777834c9a0543a518efd0c56f66bb6c106f5d8b5f1b8ebf2` |
| `run_local.sh`, `transcript_local.txt` | The local reruns and their output | (see the commit) |
| `../../../../python/yang-mills/S6_threshold/G_affine_reference_sc.py` | Handoff 43 §3 item 1: the reference program, self-contained. It prints the 22 lines of `G_affine_reference.txt` and writes no file | `06c610500e5d10e7bb4269cdbc76eb928dd62fe3fd1e7bf0ac6ec72372e26ef9` |

`G_affine_reference_sc.py` is a new file, not a change to `G_affine_reference.py`. Its evaluator is lines 8–360 of `G_affine_cert.py`, copied character for character between `BEGIN COPY` and `END COPY`; a `diff` against those lines is empty. It is 10,664 characters, standard library only, with no line starting with `%` or `!` and no run of 160 letters or digits. Run alone in an empty folder with `python3 -I`, its output is byte-identical to `G_affine_reference.txt` (0.3 s).

No reviewed file is changed: `G_affine_cert.py`, `G_affine_tiling.py`, the README, `G_affine_reference.txt` and `S4_general_d/` are as at 95d0843.

## How `Eval` is written

Same algorithm and same rounding as `G_affine_cert.py`. Every function carries, in its comment, the formula it computes.

- **Numbers.** A signed integer is a sign and a magnitude, `Z = ⟨neg, mag⟩`. All arithmetic is `Nat.add`, `sub`, `mul`, `div`, `shiftLeft`, `shiftRight`, `pow`, `log2`, `ble`, `beq`, written as the kernel's own functions, through local notations `+ₙ -ₙ *ₙ /ₙ`. A negative zero is allowed and is harmless: comparisons treat it as zero.
- **Rounding** is by shifts with P = 64. ⌊x/2^k⌋ for negative x is −⌈|x|/2^k⌉, as Python's `>>`.
- **Rationals** are pairs n/d, not reduced. Only their values enter: floors, ceilings and comparisons. They are used where Python uses `Fraction`: the series for eˣ and asin, π, the constants, and the function rule.
- **Guards.** Every `need` of the Python program is a conjunct of `ok`, with the same strictness. `check b` is `hi(G) < 0 && ok`.
- **Tables** are lists walked head first by structural recursion: `zipAdd`, `ktab`, `dotF`, `pairDot`. They are never indexed or appended to.

Where the mathematics allowed a cleaner form with exactly the same values, it is used:

- **eˣ** by Horner: 1 + q(1 + q/2(1 + … (1 + q/40))). It is the same rational as the forward sum.
- **asin** by the ratio of its coefficients, C_{k+1}/C_k = (2k+1)²/((2k+2)(2k+3)), as a Horner form in q².
- **atan(1/m)** with one shared denominator: s_k = N/(m^(2k+1) · 1·3·…·(2k+1)), stepped by N ↦ N m²(2k+3) ± 1·3·…·(2k+1).
- **The full table.** Python's QFULL (a recurrence, then `ktab` differences) is the Beta integral
  T[k][n] = (1/π) ∫₋₁¹ xⁿ (1 − x²)^(k+1/2) dx, so T[k][2j] = (2j−1)!! (2k+1)!! / (2^(j+k+1) (j+k+1)!), and T[k][2j+1] = 0.
  It is walked by T[k][2j+2] = T[k][2j](2j+1)/(2(j+k+2)) and T[k+1][0] = T[k][0](2k+3)/(2(k+2)). `full_table_check.py` checks, in exact rationals, that this equals QFULL at all 320 entries and that every entry is ≥ 0, so Python's `sorted` in FULLC keeps the order. Only the exact part of the computation changes; the rounded constants are the same.
- **The incomplete table** stays as in Python, because its entries are affine forms whose rounding must be reproduced: (n+2) Iₙ = (n−1) Iₙ₋₂ + c^(n−1) w³, then `ktab`.

Python's `x * y` with `y is x` dispatches to the square rule. The Lean reproduces exactly those three places and no others: `w * w` in w³, the first `cp * c` in `inc_table`, and `mul(mm, mm)`.

### Departures from the letter of spec §3.1

1. **Item 3 (every intermediate forced to a literal before reuse): not done.** The evaluator uses ordinary `let`s. The kernel did not run into deep recursion on any of the 128 boxes, or on the 20 reference boxes, and the timing above is with that code. If a later chunk does hit "deep recursion", forcing is the fix to try.
2. **Item 4 (no lists in inner loops): not followed to the letter.** The tables are lists, walked head first, never indexed and never appended to. The pilot's cost came from `getD` and `++`, which are not used.

Neither affects the values. Both points are performance choices; the measured time is what gate 2 asks about.

## Checks made

- **#eval against the Python program, all 128 boxes:** the five integers of G, lo and hi of q, lo and hi of c, and `check = true`. 0 mismatches (`make_lean.py evalcheck`).
- **Kernel:** all 20 reference theorems pass by `decide +kernel` (23.9 s for the file). All 128 `check b = true` theorems pass (144.8 s).
- **Mutations.**
  - The kernel refuses the reference theorem for box 1 with e one less.
  - The kernel proves `check b = false` for the whole range taken as one box, where Python fails its c guard.
  - Four rounding mutants each fail to reproduce all 20 reference boxes: e of a product rounded down, `+3` for `+4`, a negative shift truncated, and e of a division floored. A fifth, the `+1` in the function rule's δ removed, is caught on 18 of the 20 boxes, and on all 128 boxes when q and c are compared as well. (A change of one unit in e can vanish in a later ceiling.)
- **Not done from spec §3.3 item 2:** "a box shifted outside the range is rejected". `check` does not know the range; boxes just outside it, such as d ∈ [1/5, 3/10], pass in both Python and Lean. That rejection belongs to `Cover` (phase 3). The test "an upper bound tightened to the exact value plus one unit" was not made.

## Second pass (claude-sonnet-5-5, Agent tool, 22 Nov 2026 UTC)

The pass was asked to find errors, not to confirm. It made a hard read of `GAffineEval.lean` at `bec71ef5…` against `G_affine_cert.py` and the README's "Arithmetic rules", and ran its own differential tests.

**Verdict: SOUND.** It found no defect. Its tests, with every outcome an exact match:
- All 128 grid boxes: `ok`, `form`, and q and c.
- About 1,800 random boxes off the grid: μ and r up to 5/2, d up to 3, reversed, degenerate, tiny boxes, and boxes on edge 0.
  - In about 200 of them Python's `need` failed. In each of those the Lean `ok` was false.
  - In none did Lean accept a box that Python refused.
- 8,400 rule-level cases. Every affine rule and every function rule was tested, with magnitudes up to 2^70 and 30% negative zeros. Each guard predicate was false exactly when Python's `need` failed.
- Guard boundaries at ±1 unit.
- π, e, cosh and asin as exact rationals.
- `isqrt`, `csqrt`, `zshr` and `zdiv` on edge values.
- `GAffineEvalRef.lean` built: all 20 theorems pass.

It listed the two departures from §3.1 above, and found that neither affects correctness. It did not run the 128-box kernel file, and it did not test the c, u₂ and √ guards at their exact boundary inside a full box. It checked those guards' strictness by reading and at unit level.

## For posting later (operator's go only)

- `GAffineEvalRef.lean`, as one Lean post. It has 23,712 characters, no `#eval`, no line starting with `%` or `!`, and no run of 160 letters or digits. About 24 s here, and the runner's time is unknown. It is the site-checkable version of acceptance step 1.
- `G_affine_reference_sc.py`, by `code_ref` (handoff 43 §3 item 1). The runner should print the 22 lines of `G_affine_reference.txt`.
- The site normalises stored text. Among other things it cuts runs of blank lines to one, and the Python file has such runs. The stored SHA-256 will then differ from the file's.
- A description cannot go next to `code_ref`. It goes in a separate summary post.

## Not done, or not known

- The runner's time for any of these files, and how the runner compares in speed with this machine.
- A soundness proof (`Spec`, `Sound`, `Cover`, `Main`: phase 3).
- That the header expression is the paper's (*). Out of scope, as before.
- The display issue at line 387 of `G_affine_cert.py` (the printed lower end of c rounded upward) is left as it is. `Eval` compares integers, not the printed decimals.
- The toolchain was installed from the GitHub release of Lean 4.35.0, because elan's download host was refused by this session's network.

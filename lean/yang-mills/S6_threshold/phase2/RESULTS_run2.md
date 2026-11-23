# Phase 2, run 2: a second, independent Lean `Eval` and its kernel timing

Claude (claude-opus-5-5), a scheduled phase 2 session, 23 Nov 2026 UTC. It started at 00:32 UTC. Lattice only: one inequality, G(μ, r, d) < 0 on 0 < d ≤ 1/5, 0 ≤ μ, r ≤ 4/5.

**Status: prepared, not posted.** There is no ledger change and no result post. `Eval` has no soundness proof; that is phase 3.

**Relation to run 1.** Branch `claude/s6-phase2-eval` at 465adc6 (22 Nov 2026, 20:10 UTC) already holds a phase 2: `GAffineEval.lean` and its README. This session found that branch only after its own evaluator was written and timed. Run 2 leaves run 1 untouched and lives on its own branch, `claude/s6-phase2-eval-b`, in `phase2/run2/` and this note. It is a second evaluator written separately from the first. The two agree on every box tried (below).

## Gate 2

| Condition | Measured here | Verdict |
|---|---|---|
| `Eval` reproduces `G_affine_reference.txt` integer for integer | All 20 boxes and all five integers: by `#eval` (`run2/local/RefEval.out`) and by 20 kernel theorems (`run2/GAffReference.lean`, by `decide +kernel`, 33 s for the file) | met |
| 128 × (kernel seconds a box) ≤ 2 h | One box: 1.49–1.68 s of kernel time (6 runs). 128 × 1.68 s = 215 s. All 128 grid boxes, `check b = true` by `decide +kernel`, one theorem each: 198.5 s and 206.3 s of kernel time in two runs (199 s and 207 s wall) | met: 215 s is 1/33 of 7,200 s |

**Gate 2 verdict: met on this machine.** This is not a site result. The runner has built none of these files, and its speed relative to this machine is unknown.

**The pilot, rerun beside it.** `pilot/GBoxPilot.lean`, one box (the same box as reference box 20), took 4.68–4.89 s of kernel time over 7 runs, or 4.35–4.80 s net of start-up. The scoping note gave 4.3 s on its own machine. Run 2's `Eval` is about 3 times faster a box than the pilot, while computing an affine form instead of an interval.

**Run 1's evaluator on this machine.** Its reference box took 1.30–1.68 s, and all 128 boxes 151.5 s. It is about 25% faster than run 2's. Probably the cause is its closed forms (Horner for eˣ and asin, a Beta-integral form for the full table), but that is a guess: it was not profiled.

Machine: 2 vCPU, Intel Xeon @ 2.10 GHz, 7 GB. Lean 4.35.0 (commit eb6cafb7), no Mathlib. It was installed from the GitHub release, because elan's host, release.lean-lang.org, was refused by this session's network. All figures are in `run2/local/timing_transcript.txt` and `run2/local/All128_timing.csv`.

## Files (all new; no existing file changed)

| File | What it is |
|---|---|
| `phase2/run2/GAffEval.lean` | `Eval`: `GAff.gform : Box → A` (the affine form of G), `GAff.check : Box → Bool`, and `GAff.out` (the five integers and `check`). Lean 4, core only, no theorems. 22,865 characters |
| `phase2/run2/GAffReference.lean` | The 20 reference theorems `out b = (c, a1, a2, a3, e, true) := by decide +kernel`. It imports `GAffEval`. 4,454 characters |
| `phase2/run2/local/` | Local files, not for posting. `RefEval.lean` / `.out` is the `#eval` transcript. `All128_timing.lean` / `.csv` is the 128-box kernel file and its times. `timing_transcript.txt` holds the timings. `CrossMine.lean`, `CrossOther.lean` and `crosscheck_428.out` are the comparison with run 1. `MutRef.lean`, `mutant_cdivP.diff`, `Tight.lean` and `Outside.lean` are the mutation tests |
| `python/yang-mills/S6_threshold/G_affine_reference_standalone.py` | Handoff 43 §3 item 1. It prints the 22 lines of `G_affine_reference.txt` and writes no file. Lines 8–360 of `G_affine_cert.py` are copied character for character between `BEGIN COPY` and `END COPY`. 10,627 characters, standard library only. Run alone with `python3 -I` in an empty folder, its output is byte-identical to `G_affine_reference.txt`, before and after the site's normalisation (as simulated here). Run 1 has the same kind of file, `G_affine_reference_sc.py`; only one of the two needs posting |

The SHA-256 of each file is in the commit message and in the operator report.

## How run 2's `Eval` is written

- **Numbers.** Natural numbers only. A signed integer is `Z = ⟨neg, mag⟩`, and −0 is allowed: every function depends only on the value. A rational is a signed numerator over a positive natural denominator, never reduced, used only through floors, ceilings and comparisons. All arithmetic is written as `Nat.add`, `Nat.mul`, `Nat.div`, `Nat.shiftRight`, `Nat.pow`, `Nat.log2`, `Nat.ble`, `Nat.beq` and so on, with no type-class arithmetic. Rounding at 2^−64 is a shift. Python's `>>` and `//` floor negative values, and `zshr` and `zfdiv` do the same.
- **Python's `o is s`.** It sends a product to the square rule in exactly three places: `w * w` in w³, the first `cp * c` in `inc_table`, and the two squares inside `mul(mm, mm)`. The Lean uses `asq` there and nowhere else.
- **Exact parts.** Each is written over one common denominator, with the same rational value as Python's `Fraction`:
  - eˣ as Σ mʲ d^(40−j) 40!/j!;
  - asin with M = 4³⁰·61!!, so that every M·Cₖ is an integer;
  - π by Machin, as PI_LO + PI_HI and PI_HI − PI_LO;
  - QFULL over 2²⁴·24!, by its own recurrence and `ktab` differences, as in Python.

  The box-independent constants are recomputed in every box. Measured: π, π/4 and the whole full table together take about 0.09 s of a box's kernel time.
- **Guards.**
  - Every `need` reached from `G_affine` is a conjunct of the `ok` field of the form it guards, and `ok` propagates through every operation. So `check b = (gform b).ok && hi(G) < 0`.
  - Additions, which only make `check` stricter:
    - lo ≤ hi with positive denominators in the box;
    - every integer square root checked (r² ≤ n < (r+1)²);
    - two cosh numerators ≥ 0 and the length of `pairs`, which cannot fail.
- **Departures from spec §3.1.** As in run 1, two items are not followed to the letter:
  - Item 3, forcing every intermediate value to a literal, is not done. In a toy test on this machine (20,000 steps of a two-field loop), plain `let`s took 1.05 s and match-forcing 3.4 s. The kernel's cache kept shared subterms shared, and no box hit "deep recursion".
  - Item 4: tables are lists, walked from the front by structural recursion. They are never indexed (no `getD`) and never appended to.

  Neither changes a value. Both affect only speed, and the speed is what gate 2 measured.

## Checks made

- **Python against Lean.** The second pass (below) checked the full grid, 128 of 128 boxes, with all five integers and `check` identical, and 1,450 random boxes.
- **Run 1 against run 2.** 428 boxes: the 128 grid boxes and 300 random boxes inside [0, 4/5]² × [0, 1/5] (seed 20261123). The output lines are byte-identical, five integers and `check`, and `check` is true in all 428.
- **Mutations.**
  - Ceiling to floor in the product rule's e (`mutant_cdivP.diff`): the kernel refuses reference theorem 1.
  - The reference box's exact upper end of G: the kernel proves "hi(G) ≤ that value" and refuses "hi(G) < that value" (`Tight.lean`). Shifting the bound by one unit flips the verdict.
  - A box outside the range, μ ∈ [2, 21/10], r and d in [0, 1/10]: the kernel proves `check b = false` (`Outside.lean`), and Python fails there with "exp argument".
  - Not shown: that every box just outside the range is refused. `check` does not know the range, and that belongs to `Cover` (phase 3).
- **Site rules, checked on the files.**
  - No `#eval`, `run_cmd`, `sorry` or `native_decide` in the two posted Lean files.
  - No line starts with `%` or `!`, there is no run of 160 or more letters or digits, and no line has trailing spaces.
  - The Lean files are under 24,000 characters each, and the Python file is under 12,000.
  - The files were rebuilt after a simulated site normalisation (NFC, blank-line runs cut to one, ends trimmed): `GAffEval` builds and all 20 reference theorems pass.

## Second pass (claude-sonnet-5-5, Agent tool, asked to find errors)

**Verdict: SOUND.** It found no defect that changes an output integer or makes `check` true where Python fails. It found two documentation-only points, both now fixed in the header of `GAffEval.lean`:
- the list of added guards was incomplete;
- the claim of equal integers holds for boxes with nonnegative rational endpoints, which is all that `Box` can express.

Its tests:
- the 128 grid boxes, matching;
- 1,450 random boxes, including degenerate, reversed, tiny and out-of-range ones. Wherever Python succeeded and lo ≤ hi, all five integers matched and `ok` was true. Wherever Python failed a `need`, `ok` was false. No box was accepted by Lean and refused by Python.
- 13,500 operation-level cases, with about 30% negative values or −0: 0 mismatches;
- exp_iv, asin_iv and cosh_hi as exact rationals at 130 points, and π/4 and all 320 FULLC entries: identical.

It did not run the 128-box kernel file. It did not check phase 3 soundness, which is out of scope.

## For posting later (operator's go only)

- Either `GAffEval.lean` and then `GAffReference.lean`, as two Lean posts, if the site lets one Lean post import another. Or run 1's `GAffineEvalRef.lean`, one self-contained post of 23,712 characters. Run 2's evaluator does not fit in one post with the 20 theorems: 22,865 + 4,454 characters.
- One of the two self-contained reference programs, by `code_ref`, with the summary in a separate post.
- The site's normalisation changes the stored SHA-256 of each file, as before.

## Not done, or not known

- The runner's time for any of these files.
- Whether the site resolves `import GAffEval` between posts. The module name would have to match.
- A soundness proof (phase 3), and that the header expression is the paper's (*).
- Line 387 of `G_affine_cert.py`, which displays c's lower end rounded upward, is left alone. `Eval` compares integers, not the printed decimals.

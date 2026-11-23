# Gate 2 bundle: run 1's evaluator, its reference theorems, and the 128-box timing file

Prepared by Claude (claude-opus-5-5) on 23 Nov 2026 UTC, on the operator's choice of run 1. Lattice only.

**Status: prepared, not posted.** Posting waits for the operator's go.

## Files

The Lean files import each other by local names (`import LongTable.GAffineEval`). The bundle action rewrites those imports to the modules of the posts.

| Module | Characters | SHA-256 | What it is |
|---|---|---|---|
| `GAffineEval` | 19,659 | `bec71ef5d12d2bec35463b5fd9a19830bf8b29e78d861a34a23bd94818023dea` | Run 1's `phase2/GAffineEval.lean`, byte for byte: the evaluator and no theorems. It is the module that `Sound` and the chunks will later import |
| `GAffineReference` | 4,082 | `eb402191acd2249e8cc54c227532cc0ff6bf62b97c7e1d8706c58cdbdb9c1e03` | `import LongTable.GAffineEval`, then run 1's 20 reference theorems `form b = (c, a1, a2, a3, e) := by decide +kernel`. Everything after the import is the part of run 1's `GAffineEvalRef.lean` that follows the evaluator, byte for byte |
| `GAffineAll128` | 12,286 | `d3a7808e98ad828ddb4b5d37f7d6a41e18c3f3a7af272c6e2efc4a1bf3ba02ce` | `import LongTable.GAffineEval`, then `check b = true` by `decide +kernel` for the 128 boxes of the grid, in the order of `boxes()`. A timing file, not a result |

- `make_bundle.py` writes `bundle_payload.json` from these files. That payload is the call with `"action": "bundle"`: `toolchain` is `leanprover/lean4:v4.35.0` and `mathlib` is `56a005855ea17e0b0958f73ec801ae140b0a1679`, because imports work only on the Mathlib images. Each `output` is `""`, since a build of these files prints nothing. The 20 reference theorems carry a statement card.
- `make_bundle.py` also writes `reference_program_payload.json`, which posts run 1's `G_affine_reference_sc.py` by `code_ref`. It points at commit 465adc6, which is public on `claude/s6-phase2-eval`, with SHA-256 `06c61050…6ef9`. Its output is the 22 lines of `G_affine_reference.txt`.

## Checked here (Lean 4.35.0, core, 2 vCPU Xeon @ 2.10 GHz)

- **Local build.** The three modules were built in a `LongTable/` tree, so the imports resolve as they will on the site. All three build, with no messages.
  - `GAffineReference`: 22.2 s wall.
  - `GAffineAll128`: 137.6 s wall, and 129.4 s in a second run.
  - Peak memory of the `GAffineAll128` build: 822 MB.
- **Boxes.** The 128 boxes of `GAffineAll128` are exactly `G_affine_cert.py`'s `boxes()`.
- **Reference theorems.** The 20 boxes and integers of `GAffineReference` are exactly those of `G_affine_reference.txt`.
- **Site rules.** No `#eval`, `run_cmd`, `run_elab`, `run_meta`, `initialize`, `unsafe`, `sorry` or `native_decide` in any file. No line starts with `%` or `!`, and there is no run of 160 letters or digits.
- **The reference program.** At 465adc6, run alone, its output is byte-identical to `G_affine_reference.txt`.
- **Not tested here:** the Mathlib image itself. These files import no Mathlib, and the local build is core-only.

## The bundle on the runner (expected, not measured)

- **Builds.** 3 Lean builds (the evaluator once, then the two files that import it), plus one Python rerun.
- **Time.** Locally the 128-box file takes 2.2–2.5 minutes of the 20-minute limit (2.5 on one core) and under 1 GB of the 6 GB. On a runner up to about 6 times slower than this machine, it would still fit.
- **What it tells us.** The runner's time for `GAffineAll128` decides the chunk plan for phase 4. One file of 128 boxes may be enough.

## Draft summary post (a separate post, since a description cannot go next to code_ref)

> S6 phase 2 (gate 2), lattice only: G(μ, r, d) < 0 on 0 < d ≤ 1/5, 0 ≤ μ, r ≤ 4/5.
>
> **The posts**
> - `GAffineEval`: a Lean 4 evaluator, core only, no soundness proof. It has the same algorithm and rounding as `G_affine_cert.py` at 95d0843, with natural numbers only, shifts at P = 64 and `Nat.ble` comparisons.
> - `GAffineReference`: 20 theorems. Each says the evaluator gives, integer for integer, the five integers of the affine form of G in `G_affine_reference.txt`.
> - `GAffineAll128`: `check b = true` for all 128 grid boxes, by `decide +kernel`. Its runner time is what gate 2 measures. It is not a proof of the inequality: `Sound` and `Cover` (phase 3) are missing.
> - The Python reference program reproduces the reference file.
>
> **Local figures (2 vCPU Xeon)**
> - About 1.2 s of kernel time a box; 151.5 s for all 128 boxes.
> - The interval pilot takes 4.7 s on its one box.
>
> **Second passes and cross-check**
> - claude-sonnet-5-5 read this evaluator, and also an independent second one (branch `claude/s6-phase2-eval-b`), asked to find errors. Both passes: sound.
> - The two evaluators agree byte for byte on 428 boxes.
>
> **Status**
> - No ledger change. The paper's theorems still rest on `G_box_A_*.py` (l-mwpwfqjt-6ak431).

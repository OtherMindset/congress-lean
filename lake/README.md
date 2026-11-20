# LT2D: one buildable Lean project

This folder is the Lean development behind the paper *Machine-Checked Proofs of Conjectured ON-Cell Counts for
Two-Dimensional Outer-Totalistic Cellular Automata*, consolidated into a single Lake project. The proofs were written
and posted by AI agents at the [oeis-new-terms table](https://othermindset.com/table/oeis-new-terms) of the Long Table
at othermindset.com and built there by its sandboxed runner. Here they build together, from a clean clone, against one
set of definitions.

- **Toolchain:** Lean 4.35.0 (`leanprover/lean4:v4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), the same
  as the site's runner.
- **Mathlib:** commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lakefile.lean` and `lake-manifest.json`.

## Build

```
git clone https://github.com/OtherMindset/congress-lean
cd congress-lean/lake
lake exe cache get      # Mathlib's prebuilt files (about 7 GB in .lake)
lake build              # builds All.lean and everything it imports
```

`lake build` builds the default target `All`, which imports every module that holds a top-level theorem of the
paper. To build every module, including ones no result imports, run `lake build LT2D`. Some certificates are large
`decide +kernel` checks: peak memory per module is in `build_report.csv` (the largest is under 6 GB).

## What to read

Only two things need reading to trust a result: the definitions and the top-level statements.

- `LT2D/Defs.lean`: the seven definitions (`Cell`, `ruleOut`, `nbrOn`, `step`, `caState`, `window`, `onCount`),
  copied verbatim from post #mwmovuz3-8p5t1y. No other file declares them.
- `manifest.json`, `top_level_theorems`: the 191 top-level theorems, each with its module, post, ledger entries and
  the statement the runner reported. `statements_before_after.txt` shows each one matching the statement as this build
  elaborates it.

Everything else is checked by the kernel. `axioms.txt` shows that every top-level theorem rests on `propext`,
`Classical.choice` and `Quot.sound` only.

## Layout

| Path | What |
| --- | --- |
| `LT2D/Defs.lean` | the seven definitions |
| `LT2D/Basic.lean` | one copy of each lemma that several posted files declared (finite-list device, `card_window`, `nbrOn_abs`, `sum_Icc_natAbs`, `onCount_fold`, ...); the source post is named above each declaration |
| `LT2D/VN/` | the VN certificate library: `K1`-`K9` (core Lean), `M1`-`M4` (Mathlib) |
| `LT2D/Instances/<name>/` | one instance of the library per rule: `C` (table and seed/step certificates), `D1`, `D2`, ... (data), `D` (chunked step certificate), `M` (the theorems) |
| `LT2D/Groups/<name>/` | groups of instances, a core file `C` and a Mathlib file `M` each |
| `LT2D/A272706/` | the Rule 515/523 chain that preceded the VN library |
| `LT2D/Early/` | the first results (18 Nov), proved with a finite-list device rather than the VN library |
| `LT2D/LDR/` | Rules 469 and 337 from the Rule 558 proof (parity relations) |
| `LT2D/Relations/` | hand-written relations between entries |
| `LT2D/R750/` | Rule 750 (A169707), a direct induction |
| `All.lean` | imports every module with a top-level theorem |
| `manifest.json` | post id -> module, SHA-256 of the posted text and of the file here, the edits made; the top-level theorems |
| `manifest_sources.json` | every posted file used: SHA-256, author (name and model), toolchain, ledger entries that use it |
| `scripts/` | the checks (below), the per-module build, and `fetch_sources.py` to re-fetch the posted texts |
| `report/` | the consolidation report: declaration map, duplicate diffs, every edit with before and after |

## How the files differ from the posts

Each module is a posted file with only these changes (all listed in `report/edits.json` and `report/edits.diff`):

1. imports by post id (`LongTable.P_<id>`) replaced by module names;
2. declarations that moved to `LT2D/Defs.lean` or `LT2D/Basic.lean` deleted, and `import LT2D.Basic` added;
3. `private` added to 35 rule-specific helpers that share a name with a different helper in another file and are not
   used outside their own file;
4. one helper renamed, `D1` to `D1_r641`, in the two files of the Rule 641 (A273310) lineage.

No proof was otherwise changed, and no `decide +kernel` was replaced.

## Checks

Each script exits non-zero on failure.

| Script | Checks | Output |
| --- | --- | --- |
| `scripts/check_unique_defs.py` | the seven definitions each occur exactly once, in `LT2D/Defs.lean`, and no other name is declared publicly twice | `report/check_unique_defs.txt` |
| `scripts/check_forbidden.py` | no `sorry`, `native_decide`, `axiom` or `implemented_by` outside comments and strings | `report/check_forbidden.txt` |
| `scripts/gen_axioms.py` | `#print axioms` for every top-level theorem (`axioms.lean`); only `propext`, `Classical.choice`, `Quot.sound` | `axioms.txt` |
| `scripts/statements_before_after.py` | each top-level statement, printed as the runner prints it (`scripts/Report.lean`, the runner's `ReportImports.lean` with prefix `LT2D`), equals the runner's | `statements_before_after.txt` |
| `scripts/build_all.py` | builds each module on its own, in import order, with time and peak memory | `build_report.csv` |

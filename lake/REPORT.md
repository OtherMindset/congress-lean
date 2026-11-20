# Consolidation report: LT2D Lean development (20 Nov 2026)

Carried out from the site builder's handoff "carry out the LT2D consolidation" (20 Nov 2026, 09:45 US Eastern). The
article editor's plan the handoff names as the specification was not available to this session. The operator chose to
use instead the consolidation plan in `docs/definitions_audit.md` of `cohen_jar_draft_source.zip` (steps 1-7, the
same steps as the plan's §4) together with the handoff. The acceptance criteria used are listed in §6. The plan's §3
(extra theorems) was not available; how the theorem list was formed is in §1.

## 1. Theorem list

- **Source:** the paper's `paper/appendix_index.tex` (generated from `paper/rows.json`), 182 theorems in 88 rows,
  plus 9 results that `paper/main.tex` names and the appendix does not: `LT2D.a169707_rule750`,
  `LT2D.rule750_on_in_window` (Theorem 8), `LT2D.a273331_a16`, `LT2D.r469_parity`, `LT2D.r337_parity`,
  `LT2D.count_compl558`, `LT2D.r337_count_odd` (Theorem on parity), `LT2D.r990_caState_eq_926`, `LT2D.r990_count`.
- **Count:** 191 top-level theorems. The handoff gives 189 for the paper. 182 + 7 would be 189, but without the plan's
  §3 this session couldn't tell which two of the nine main-text results the 189 leaves out, so all nine are covered.
- **Each theorem was found** in the passing runner result of exactly one posted file (40 posts). The list, with each
  theorem's module, post, ledger entries and runner statement, is `manifest.json` → `top_level_theorems`. Five
  main-text theorems are named in no ledger entry's theorem list; they carry the entries whose evidence uses their post
  (`ledger_ids_via`).

## 2. Collect (step 1)

- **Import closure:** 133 posted files, fetched once each from `/api/work/oeis-new-terms/<id>` (the oeis-new-terms
  ledger with `?part=ledger`), 0.2 s apart, recursively through `imports`. No file imports a data post
  (`LongTable.D_<id>`), so there are no data modules.
- **SHA-256:** all 133 texts match the post's `code_sha256`. They are listed in `manifest_sources.json` (post id,
  SHA-256, author name and model, toolchain and Mathlib of the passing run, the ledger entries that use the post).
  `scripts/fetch_sources.py` re-fetches them into `sources/` and checks each hash; `sources/` is not committed, since
  the repository holds each file once.
- **Four imported posts have no passing runner result of their own:** #mwmsmhru-fync82, #mwmsn5zn-jc4kar
  (Rule 619 data), #mwohw8h0-ylki35 and #mwohw8ku-sbtbs1 (Rule 654 data). The runner refused them with "the file
  declares no theorem"; they were built as imports of posts that passed. Their author is "Claude congress · Leader"
  (`claude-opus-5-5`).
- **Against `add-posted-dependencies`:** 47 of the 133 files are in that branch. 32 are byte-identical to the site. 15
  differ. The site's version was used for all of them:
  - 12 (`W3L1r_rules_505_507/W3B_R507_D1`, `_D2`, `_D3`, `_D`, `_M`, `W3B_R505_D1`, `_D2`, `_D3`, `_D`, `_M`,
    `W3A1_class_558/W3A558_D`, `_M`) import the previous file as `LongTable.<module>` where the site has
    `LongTable.P_<id>`, and the repository copy ends in a newline that the site's text doesn't have.
  - 3 (`W3B_R507_C`, `W3B_R505_C`, `W3A558_C`) differ only in that final newline.

  These are the code_ref files: the repository keeps the version before the site's `bundle` rewrote the imports.

## 3. Map (step 2)

Full tables: `report/declarations.md`. Diffs between differing duplicates: `report/duplicate_diffs.txt`.

- **Nine lineages, not three.** Nine posted files declare `def caState` (with `Cell`, `ruleOut`, `nbrOn`, `step`), and
  11 declare `window` and `onCount`. In every file each of the seven definitions is identical after whitespace
  normalisation. Lineages A (#mwmg73qw-sgejby, A272706 and Rule 750), B (#mwmovuz3-8p5t1y, the VN library: 126 of
  the 191 theorems) and C (#mwmbjanx-5lciqx, Rules 721/729) are the audit's. The other six are the first results of
  18 Nov, each a self-contained file or a core/Mathlib pair: A273385 (#mwmbp99x-ymn9an), R245/R323/A270084
  (#mwmc69rp-fpejr2), A271055 (#mwmeo46j-i1w8jl), A271061 (#mwmezycj-p4n3xa), A273310 (#mwmnzbwy-gx846h),
  A269911 (#mwmo3omz-3d6q7j).
- **46 names are declared in more than one file:**
  - the 7 definitions;
  - 21 generic lemmas that are identical or have the same statement. These include the finite-list device (`coFin`,
    `finOn`, `cands`, `offAfter`, `onAfter`, `sameSet` and their lemmas), `caState_zero`, `card_window`,
    `nbrOn_abs`, `sum_Icc_natAbs` and `onCount_fold`;
  - 18 rule-specific helpers with the same name in different files. These include `D1`, `stages`, `offSet`,
    `count_formula` and the two `sumTo_eq_sum`: the A-lineage one is about `A272706.sumTo`, the B-lineage one about
    `VN.sumTo`.

  Of the 18 helpers, 11 differ between files and 7 are identical but rule-specific, such as `O1`, `P5`, `D2` and
  `box9`.

## 4. Layout and edits (steps 3-5)

- `LT2D/Defs.lean`: the seven definitions with their docstrings, verbatim from #mwmovuz3-8p5t1y, with that file's
  seven Mathlib imports.
- `LT2D/Basic.lean`: one copy of each of the 21 generic lemmas, each verbatim from a named post. `open Finset` covers
  only the two lemmas whose source had it.
- 133 modules with readable names (`manifest.json` maps post id → module), and `All.lean`, which imports the 40
  modules with top-level theorems.

Edits, all in `report/edits.json`, with the full before/after for every file in `report/edits.diff`:

| Edit | Count | Why |
| --- | --- | --- |
| import `LongTable.P_<id>` → module name | 199 lines in 122 files | modules have names, not post ids |
| delete a declaration that moved to Defs/Basic | 166 | one copy only |
| `import LT2D.Basic` added | 16 files | the files that declared moved declarations |
| `private` added to a helper | 35 | the name clashes with a different helper in another file, and no other file uses this copy |
| `D1` → `D1_r641` | 14 occurrences in 2 files | `LT2D.D1` is public and used by another file in two lineages, with different values (Rule 641 vs Rule 3); renamed in the A273310 pair (`Early.A273310_Core`, `Early.A273310_M`) |

**Proof edits.** No proof body was changed, apart from the rename. Deleting a moved lemma removed its proof where that
copy's proof differed from the one kept in `Basic`, with the same statement. This applies to:

- `card_window` in `Early.A271055`, `Early.A273310_M`, `Early.A269911_M` and `Early.A270084_M`;
- `contains_offAfter` and `contains_onAfter` in `Early.R245_A`.

Their texts are in `report/edits.json` and the diffs in `report/duplicate_diffs.txt`. No `decide +kernel` was
replaced. No `sorry`, `native_decide`, `axiom` or `implemented_by` occurs.

Note for the operator: the `Early.*` core files, which before had no Mathlib, now import Mathlib through `LT2D.Defs`.
All of them built unchanged.

## 5. Build (step 6)

- **Hardware:** 2 vCPU (Intel Xeon @ 2.10 GHz), 7.8 GB RAM, Linux; Lean 4.35.0 release tarball (commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), no elan.
- **Clean clone of `consolidate` at commit `4293039`:**
  - `git clone`: 1 s.
  - `lake exe cache get`: 125 s. This includes Lake fetching Mathlib and its dependencies, building the cache tool,
    and decompressing 9,030 files. It downloaded nothing, because this machine's `~/.cache/mathlib` already held the
    archives from setup. A run with that cache empty is in §5.1.
  - All 136 modules, one at a time in import order (`scripts/build_all.py`): 3,161 s (52.7 min) wall clock, 3,156 s
    summed over modules. A following `lake build` had nothing to do (9 s).
- **Per module:** `build_report.csv` (seconds, peak RSS, exit code), measured from a Python wrapper with
  `getrusage(RUSAGE_CHILDREN)`. The slowest module is `Instances.LC_R654.D` (388 s). The largest peak is 5,005 MB
  (`Early.A271061_Part2`, which imports all of Mathlib), under the runner's 6 GB a file.

### 5.1 Cache download included

A second fresh clone was made with `~/.cache/mathlib` emptied. Its `lake exe cache get` took 102 s, covering:

- Lake fetching Mathlib and its dependencies;
- building the cache tool;
- downloading 9,031 files (453 MB) from `https://cache.mathlib.org`;
- decompressing them, which leaves 7.3 GB in `.lake`.

| From a clean clone | Time |
| --- | --- |
| clone + `lake exe cache get` (empty cache) + build of every module | 1 s + 102 s + 3,161 s = 3,264 s (54.4 min) |
| build of every module, cache already in place | 3,161 s (52.7 min) |

The build was run one module at a time, as the handoff asks for the measurement, so it used one of the two CPUs most
of the time. A plain `lake build`, which runs modules in parallel, should be somewhat faster on the same machine; it
was not timed separately.

## 6. Checks (step 7) and acceptance

| Criterion | Result |
| --- | --- |
| `All.lean` builds from a clean clone with `lake exe cache get` | pass |
| `check_unique_defs.py`: the 7 definitions each once, in `LT2D/Defs.lean`; no other name declared publicly twice | pass (`report/check_unique_defs.txt`) |
| `check_forbidden.py`: no `sorry`, `native_decide`, `axiom`, `implemented_by` | pass, 138 files (`report/check_forbidden.txt`) |
| `gen_axioms.py`: only `propext`, `Classical.choice`, `Quot.sound` | pass, 191 theorems (`axioms.txt`) |
| `statements_before_after.py`: each statement as the runner prints it equals the runner's | pass, 191 of 191 match, 0 differ (`statements_before_after.txt`) |

The statements are printed with `scripts/Report.lean`, the runner's `lean/ReportImports.lean`
(`OtherMindset/othermindset-lean-runner` at `19af8de9`) with the module prefix `LongTable` changed to `LT2D`. Every
statement mentions only `LT2D.*` and Mathlib constants, whose names are unchanged, so no name mapping was needed.

## 7. Not done (out of scope)

- No merge into `main`, no GitHub workflows, no change to posts, the ledger or the runner, no new mathematics.
- No Zenodo or Software Heritage deposit: that is the operator's step.
- The handoff says a CI check that `def caState` occurs once; that is `scripts/check_unique_defs.py`, to run by hand,
  because workflows are out of scope.

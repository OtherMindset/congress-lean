# paper/: checks and data behind the paper's tables

Files used for *Certified Digit Automata for Nonlinear Two-Dimensional Cellular Automata: Kernel-Checked Proofs of
OEIS Counting Conjectures in Lean 4* (A. R. Cohen). None of them is part of the Lean library: `lake build` does not
build them, and no result depends on them. Run the commands from `lake/`.

## Statement check (paper, Section 9.2)

```
python3 -I paper/check_statements.py paper/rows.json manifest.json paper/statement_check.txt
```

`rows.json` holds the rows of the paper's Tables 2-4, as generated from the ledger export by `gen_tables_jar.py`.
The script compares each row with the statement the runner elaborated (`manifest.json`, `top_level_theorems`):
closed forms as functions of n (exact evaluation at 41 consecutive n, truncated subtraction in exponents), equal
counts and relations by their rules, order and hypothesis. Result: 191 theorems, 184 matched, 0 mismatched, 7 to be
read (printed in the paper's Appendix A).

## Certificate sizes (paper, Table 5)

- `table_sizes.py` lists every guessed table in `LT2D/` with its rule, mask, chunks and recurrence check, and writes
  `Sizes.lean`, which recomputes the seed and step product sizes with the library's own `VN.explore` by `#eval`:

  ```
  python3 -I paper/table_sizes.py . /tmp/tables.json paper/Sizes.lean
  lake env lean paper/Sizes.lean        # prints Sizes_output.txt
  ```

- `table_sizes.json` joins those sizes with `build_report.csv`; `gen_sizes_tex.py` writes the paper's Table 5.

## Worked example and negative controls (paper, Section 6)

- `WE_rule1.lean`: the three certificates of the 7-state table for Rule 1 (A269907), alone.
- `NEG.lean`: kernel-checked negative controls for that table (wrong rule, wrong mask, changed constant, wrong
  starting index, one changed transition), each proved `= false`.
- `NEG926.lean`: the Rule 926 counting check with a changed constant or coefficient, and the twin test for Rule
  1022, each proved `= false`.

Check them with `lake env lean paper/<file>.lean` (no output means they hold).

## Data

- `data_in/results.csv`: the oeis-new-terms ledger export of 19 Nov 2026 used for the paper's tables.
- `data_in/sim_n9.json`, `data_in/sim_extra_n9.json`: counts c_R(n), n <= 9, from an independent simulation, which
  `gen_tables_jar.py` compares with every closed form and relation.
- `gen_artifact_tex.py`: writes the paper's definitions listing, build table and Appendix A from this directory's
  parent.
- `r750_kernel_check.py`: the 2-kernel growth diagnostic for Rule 750 (paper, Table 7).

Not here: the guessing program (`gen/kernel.py`), the generators `emit2.py` and `emit_instance.py` named in the
headers of the generated files, and the OEIS snapshot of 19 Nov 2026.

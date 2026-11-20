# Declaration map (step 2)

Parsed with `scripts/leandecls.py` (comments, strings and docstrings skipped) over the 133 posted files in the import closure of the 191 top-level theorems.

## Files declaring `def caState`

9 files declare `caState` (with `Cell`, `ruleOut`, `nbrOn`, `step`); 11 declare `window` and `onCount`. All copies of each of the seven definitions are identical after whitespace normalisation.

| Lineage | Root post (declares caState) | Module | Files in lineage | Top-level theorems |
|---|---|---|---|---|
| A | #mwmg73qw-sgejby | `LT2D.A272706.M1` | 4 | 4 |
| B | #mwmovuz3-8p5t1y | `LT2D.VN.M1` | 39 | 126 |
| C | #mwmbjanx-5lciqx | `LT2D.Early.A273446` | 1 | 2 |
| D | #mwmbp99x-ymn9an | `LT2D.Early.A273385` | 1 | 12 |
| E | #mwmc69rp-fpejr2 | `LT2D.Early.R245_A` | 6 | 5 |
| F | #mwmeo46j-i1w8jl | `LT2D.Early.A271055` | 1 | 1 |
| G | #mwmezycj-p4n3xa | `LT2D.Early.A271061_Part1` | 3 | 36 |
| H | #mwmnzbwy-gx846h | `LT2D.Early.A273310_Core` | 2 | 4 |
| I | #mwmo3omz-3d6q7j | `LT2D.Early.A269911_Core` | 2 | 1 |

Files importing two lineages: 0 (none could, before consolidation).

Files with `window`/`onCount` but no `caState` (they import a core file of their lineage): #mwmc7dqp-lya7v1 (`LT2D.Early.R245_B`), #mwmfdcb8-xvayfc (`LT2D.Early.R323_B`), #mwmo00d2-zk3ahq (`LT2D.Early.A273310_M`), #mwmo4lkh-4j151k (`LT2D.Early.A269911_M`), #mwmo64bd-kg91iu (`LT2D.Early.A270084_M`)

## Names declared in more than one file

| Name | Files | Kind | Resolution |
|---|---|---|---|
| `LT2D.Cell` | 9 | identical | moved to `LT2D/Defs.lean` |
| `LT2D.D1` | 4 | 3 variants | `private` in A273385, R245_A; renamed `D1_r641` in the A273310 pair; kept in A269911 (used by its Mathlib file) |
| `LT2D.D2` | 2 | identical | `private` in `LT2D.Early.A273385`; public copy kept where another file uses it |
| `LT2D.D3` | 2 | 2 variants | `private` in `LT2D.Early.R245_A`; public copy kept where another file uses it |
| `LT2D.O1` | 3 | identical | `private` in `LT2D.Early.A273446`, `LT2D.Early.A269911_Core`; public copy kept where another file uses it |
| `LT2D.P5` | 2 | identical | `private` in `LT2D.Early.A273446`; public copy kept where another file uses it |
| `LT2D.base_box` | 2 | 2 variants | `private` in `LT2D.Early.R245_B`, `LT2D.Early.R323_A` |
| `LT2D.box9` | 2 | identical | `private` in `LT2D.Early.R245_B`, `LT2D.Early.R323_A` |
| `LT2D.caState` | 9 | identical | moved to `LT2D/Defs.lean` |
| `LT2D.caState_zero` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.cands` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.card_offSet` | 3 | 2 variants | `private` in `LT2D.Early.R245_B`, `LT2D.Early.R323_B`, `LT2D.Early.A270084_M` |
| `LT2D.card_window` | 9 | 2 variants | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.coFin` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.coFin_congr` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.contains_cands_false` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.contains_offAfter` | 6 | 2 variants | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.contains_onAfter` | 3 | 2 variants | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.count_formula` | 2 | 2 variants | `private` in `LT2D.Early.R245_B`, `LT2D.Early.A270084_M` |
| `LT2D.count_large` | 2 | 2 variants | `private` in `LT2D.Early.R323_B`, `LT2D.Early.A270084_M` |
| `LT2D.count_three` | 2 | 2 variants | `private` in `LT2D.Early.R323_B`, `LT2D.Early.A270084_M` |
| `LT2D.finOn` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.finOn_congr` | 3 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.nbrOn` | 9 | identical | moved to `LT2D/Defs.lean` |
| `LT2D.nbrOn_abs` | 2 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.offAfter` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.offSet` | 3 | 2 variants | `private` in `LT2D.Early.R245_B`, `LT2D.Early.R323_B`, `LT2D.Early.A270084_M` |
| `LT2D.onAfter` | 3 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.onCount` | 11 | identical | moved to `LT2D/Defs.lean` |
| `LT2D.onCount_O3` | 2 | identical | `private` in `LT2D.Early.R323_B`, `LT2D.Early.A270084_M` |
| `LT2D.onCount_fold` | 2 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.onCount_odd` | 2 | 2 variants | `private` in `LT2D.Early.A271055`, `LT2D.Early.A273310_M` |
| `LT2D.ruleOut` | 9 | identical | moved to `LT2D/Defs.lean` |
| `LT2D.sameSet` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.sameSet_contains` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.same_counts` | 2 | 2 variants | `private` in `LT2D.Early.A273385`; public copy kept where another file uses it |
| `LT2D.stage1` | 2 | identical | `private` in `LT2D.Early.A273385`, `LT2D.Early.A273310_Core` |
| `LT2D.stages` | 4 | 4 variants | `private` in `LT2D.Early.A273446`, `LT2D.Early.R245_A`, `LT2D.Early.A273310_Core`, `LT2D.Early.A269911_Core` |
| `LT2D.step` | 9 | identical | moved to `LT2D/Defs.lean` |
| `LT2D.step_allOn` | 2 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.step_coFin` | 5 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.step_coFin0` | 2 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.step_finOn` | 6 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.sumTo_eq_sum` | 2 | 2 variants | `private` in `LT2D.A272706.M2`; public copy kept where another file uses it |
| `LT2D.sum_Icc_natAbs` | 2 | identical | one copy moved to `LT2D/Basic.lean`; other copies deleted |
| `LT2D.window` | 11 | identical | moved to `LT2D/Defs.lean` |

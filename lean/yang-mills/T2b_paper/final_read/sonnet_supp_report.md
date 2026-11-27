# Review of /home/claude/supp/supp.tex (Online Resource 1) against paper, repo @446f7f9 and the Long Table

Read-only. Nothing edited or posted.

## Verified correct
- Commits dc5c9e9, 7ba981b, 446f7f9: the T2b_lean file trees are identical (same blob ids). Full hashes dc5c9e9272f5...e19cb and 446f7f96bf68...1618 match `git rev-parse`.
- Table S3: all 212 program files. The list of paths equals the repo's .py/.c files under T2b_session exactly. Every SHA-256 matches `git show 446f7f9:<path> | sha256sum` (212 of 212, not a sample). Per-directory file counts all match, including zerod 52, numerics 25, lift 17 and b3check 16. Repo has 211 .py + 1 .c, matching "Python programs and one C program".
- S3: all 8 Lean-file hashes and the check.sh hash match. Theorem counts by `^(theorem|lemma) ` match: ABFDini 10, EOM 36, Maxwell 20, NN 9, OneSiteA 8, B 13, C 18, D 7. They agree with the paper's Section 11 totals (46 and 65). All named theorems exist in the files. Toolchain v4.35.0 and Mathlib 56a005855ea1... match the README, the file headers and the runner.
- Table S2 vs notes files: the descriptions for zerod, theta1-3, lift, numerics, mc, r2/A-E (structure, walks, exponent bounds, literature, convexity), round3/fable, fd, ng, vehl and mc_eps are consistent with the notes. The files zerod_proof.md, AUDIT_AND_LIFT.md and RESULTS.md exist.
- S4 referee summaries match round3/{fable,fd,ng,v1}_check/REPORT.md (verdicts, fixes, the "m not m/H" normalisation error, the Thm 6.1/Cor 6.2 hypotheses, the Thm 4.1 formalisation overstatement, the (O4)/(O5) wording, the referee-2 "missed two points" link). The reports were "recorded by the lead from the referee's final message", as S4 says.
- Site: Lean post ids and ledger ids match: mwxrgqa8, qed, qjt, qpc, qtf, qyf, r5q and ras, each with its own suffix. Ledger entries for all four OneSite files, ABFDini, TorusEOM, Maxwell and NN are machine-checked with 1 openai, 1 google and 1 runner. The conditional entries l-mwzlzv3n-k7uhb4, l-mwzlzvsz-bnlmd9, l-mwzlzwnn-funp3d, l-mwzlzxhj-dahntw and l-mwzlzy4r-zob2io all exist, with evidence posts mwzfyk6n, mwzircx2, mwzg06k8, mwzg0mj8 and mwziu7xt respectively.
- Site narratives: the gap #mwzhu97n (the |B|<=24x vs B>=-24x issue and the constants 13.73/0.2825 rounded down), the answer #mwzhzicp (Lebowitz; 13.74/0.2826; exact 13.7329 and 0.28250681), the hard holds #mwzi533b on the amended post, and #mwzl2e57 on the reposted one are all correct. Same for #mwzhu2w9 ("unsure"; two sites, small J, disjoint local times), the reply #mwzhziqc, the reposted #mwzircx2 with hard holds #mwzl2cd6 (builds on mwzircx2), and #mwzfzotr superseded by #mwzg06k8 (step 7 is indeed garbled). The gap #mwzc8k62 and its answer #mwzcpm4u (narrowed to ContinuousAt at s0) are described correctly.
- The Lean files were posted on 26 Nov 2026 (post time 16:22 UTC). The site stores its own code hash (7d6960c1... for ABFDini) that differs from the repo hash, which S3 explains correctly.
- S1 rows vs paper numbering (zenodo.aux): Thm 3.1, 4.1, 5.1, Prop 5.2, Thm 6.1, Cor 6.2, Thm 7.1, Prop 7.2, 7.3, Thm 8.1, Prop 8.2, Thm 8.3, Prop 8.4 are correct. Cross-references "Section 12.2/12.3/12.5" and "Section 11" are right (12.3 = who, 12.4 = Lean files, 12.5 = resultchecks). Paper items 1-4 map to Referee 1-4 as used in S1.

## Findings

1. ERROR. Table S1, row "Prop 5.2 (Dini sharp)", Produced-by column: "round 1 (T2b_session/theta2, theta3)". The sharpness counterexample is in T2b_session/theta1/PROOF.md section 5 item 2 ("Exponent bookkeeping and sharpness"; the Lean header of PP2ABFDini also cites "the sharpness counterexample of PROOF section 5.2"). theta2/NOTES.md is titled "non-sharp tools" and theta3 does not contain it. Fix: put `T2b_session/theta1` in that row.

2. INCONSISTENCY. "Round" labels in S2 vs S1/S4. Table S2 says "r2/A-r2/E: Round-2 team notes" and uses the paper's "round3/..." directories for the paper's round 2. S1 and S4 attribute r2/B (Prop 7.2), r2/E and b3check ((O4)-(O6)) to round 1, and the paper (12.3) says round 1 and round 2 were both on 26 Nov 2026. The directory names (r2, round3) are the sessions' own labels (their "round 2", "round 3") and do not match the paper's rounds 1 and 2. Fix: add one sentence to S2, e.g. "Directory names r2 and round3 are the working sessions' own labels; r2 belongs to round 1 and round3 to round 2 of the paper", and change "Round-2 team notes" in S2 accordingly.

3. INCONSISTENCY (nit-to-minor). S4 "Sessions": "on 26 and 27 November 2026". The paper (12.3) dates both rounds on 26 Nov; the notes and reports are all dated 26 Nov; 27 Nov is the date of posting, the cross-family checks and the ledger entries (23:24-23:25 UTC). Fix: "on 26 November; the posting and cross-family checks were on 27 November".

4. NIT. S1 legend: "A blank ledger column means ..." but the table writes "none". Say "none".

5. NIT. S1 legend defines "conditional" as resting on "cited sources that no checker read". The ledger entries for Thm 6.1/Cor 6.2 (hypothesis H_F, "A conditional theorem, not T2b") and Prop 8.2 (hypothesis FD_kappa) also depend on open hypotheses; Thm 6.1 also depends on (I3), which has no reference. Fix: "conditional means rests on cited sources that no checker read and, for Thm 6.1, Cor 6.2 and Prop 8.2, on the stated open hypotheses." (S4 mentions (I3) later, but not the hypotheses.) The paper's 12.7 has the same simplification.

6. NIT. S4, PP2ABFDini gap: the same gap was first raised in #mwy5ow9i-ysngix (26 Nov 23:00 UTC, a statement-only check without runner output), then re-run as #mwzc8k62-lkaumd (27 Nov). The re-check that "held" is #mwzf4vf9-8z4wu1 and is not cited. Fix: cite #mwzf4vf9-8z4wu1 (and optionally the earlier #mwy5ow9i-ysngix). The S3 "Theorems; notes" cell for PP2ABFDini could also cite it.

7. NIT. Table S1 gives no program directory for Thm 7.1, Prop 7.3 or Thm 6.1 (only "round 1"); the Lean-less results are otherwise traced. Optional: name theta3 (Thm 7.1 form) and theta2/r2/C as sources if that is accurate (not verified).

8. NIT (S2). The rows "abtest, b3check: Tests used for (O4)-(O6)" and "mcval: re-validation" could not be checked against any notes file (neither directory has one). The code is consistent: b3check has exact-enumeration/strip tests and mcval/validate.py is the exact 2x2 torus check. Note also that mcval/ana.py and validate.py are byte-identical to mc/ana.py and mc/validate.py (and mc_eps/run_all.py, binder.py, analyze.py equal mc/ copies), so the hashes repeat in S3; this is correct, but a reader may wonder.

9. OUT-OF-SCOPE NOTE (repository, not supp). lean/yang-mills/T2b_lean/README.md states different theorem counts (24, 55, 29, 16, 16+14+27+8 = 65 for OneSite) from the true counts (10, 36, 20, 9, 8+13+18+7 = 46). The supp and paper counts are right by grep (and the paper's 46 + 65 total is consistent). If the README is meant to be cited, it could mislead; a reviewer comparing may be confused. Also the README says "Not posted to the Long Table", which is stale.

## Not verified
- Gemini check ids (e.g. #mwzluawc-bjnxut, #mwzikxtr-igvwmy) beyond what the ledger entries show (1 google, hard, rederived).
- Prop 8.4's, Thm 8.1's and Prop 8.2's statements against their posts (only the ledger entries were read for the latter two).
- Table S1 attribution of models (Opus/Fable/Sonnet) beyond what the paper and notes say; the repo notes do not name the model.

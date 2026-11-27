# Consistency and copy check: Zenodo (20 pp) and JSP (24 pp) builds of the phi^4_2 preprint

Read only. No file edited, nothing posted. Line numbers refer to /home/claude/paper/body.tex unless stated.

## 1. Cross-references and logs: clean
- Every \ref/\eqref resolves; every \cite key exists in refs.bib. No "??" in either PDF (pdftotext). No undefined reference/citation, "multiply defined" or Overfull warnings in zenodo.log or jsp.log. bibtex ran without warnings.
- Section/theorem numbers printed in both PDFs are identical (same aux numbering): Thm 3.1, 4.1, 5.1, Prop 5.2, Thm 6.1, Cor 6.2, Thm 7.1, Prop 7.2, 7.3, Thm 8.1, Prop 8.2, Thm 8.3, Prop 8.4, Sections 9 (obstructions), 10, 11 (Lean), 12 (production), 12.3, 12.4, 13. All prose citations of these go through \ref, so they match. The only hard-coded numbers are "Theorems 9.1, 9.3, 9.2" at line 505, explicitly described as the old numbering (current: 8.1, 8.3, 8.2; order zeromode / FDbubble / FD is right), and external "Proposition 20, Lemma 22, Definition 3, equations (6),(11), Lemmas 21-23" of [vEHL26], which I could not check.
- Residual log items (harmless): JSP font-size substitution warnings, hyperref bookmark-level warnings, 24 "Underfull \vbox" (sn-jnl, with \raggedbottom), Underfull \hbox in the sloppypar paragraphs of 12.1 and 12.4 (see nits).

## 2. Internal consistency

### Findings
1. **ERROR / inconsistency: version date.** zenodo.tex:27 says "Preprint, version 1, 26 November 2026", but the text reports events on 27 November 2026 (lines 464, 505: five results posted and checked on 27 Nov; re-posts mwzircx2 and mwziu7xt decode to 27 Nov 21:54 and 21:56 UTC). Fix: date the preprint 27 November 2026 (or the actual deposit date). JSP wrapper has no date, which is fine.
2. **INCONSISTENCY: commit hash.** body.tex:456 (Section 11) gives repository commit `7ba981b` for the Lean files; declarations.tex:13 (Data and code availability, both versions) gives commit `446f7f9` for the same repo/branch `claude/pphi2-t2b-session13`, which also holds the paper source. Either one is stale or they intentionally differ (Lean snapshot vs final); if intentional, say so ("Lean files at commit 7ba981b; the complete repository at 446f7f9"), otherwise unify. The Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (line 441) is the only copy and is consistent.
3. **INCONSISTENCY: who checked the five results.** declarations.tex ("Use of large language models") says the Lean statements "and five results with their proofs" were checked by "OpenAI (GPT-6 Sol and GPT-6 Astra) and Google (Gemini 4 Argon)". Body 12.4 (lines 505-510) says the five results were checked by GPT-6 Astra and Gemini 4 Argon only; Sol checked only Lean statements (line 501). Fix: reword the declaration, e.g. "the Lean statements by GPT-6 Sol, GPT-6 Astra and Gemini 4 Argon, and five results with their proofs by GPT-6 Astra and Gemini 4 Argon".
4. **INCONSISTENCY: keywords differ.** zenodo.tex:34 has an extra keyword "differential inequalities"; jsp.tex:36 does not. Zenodo also separates by ";" and JSP by "," (layout only). Pick one list.

### Verified consistent
- Author name "Alexander Ross Cohen" (zenodo.tex:23, jsp.tex:30), ORCID 0009-0006-2755-8313 (zenodo.tex:25, jsp.tex:41), affiliation Other Mindset Lab LLC, email alexander.ross.cohen@gmail.com (JSP only, jsp.tex:30), DOI 10.5281/zenodo.24565416 (zenodo.tex:37 and declarations.tex:7 identical). Declarations use initials "A.R.C." (fine).
- Model names: Claude Opus 5.5, Claude Fable 5.2, Claude Sonnet 5.5, GPT-6 Sol, GPT-6 Astra, Gemini 4 Argon are spelled the same everywhere (body, declarations). Sonnet 5.5 appears at line 486 and in the declarations; Sol only at line 501 and the declarations.
- Post ids (15): mwxrgqa8-yzwwh3, mwxrgqed-wp91bc, mwxrgqjt-yz1opc, mwxrgqpc-6ye1sm, mwxrgqtf-l3pl1a, mwxrgqyf-36c38e, mwxrgr5q-ejxthl, mwxrgras-f25253 (line 464, the eight Lean files); mwzfyk6n-7vf6aa, mwzfz4vz-kcw1vq, mwzg06k8-2nmi18, mwzg0mj8-bskmht, mwzg170q-1swu3s (line 505); mwzircx2-dp977k (510); mwziu7xt-7jygdd (509). Each appears once, format correct, and the embedded timestamps agree with the stated dates (8 Lean posts 26 Nov 16:22 UTC; the rest 27 Nov). The re-post ids come after the originals, as the text says.
- "Eight Lean files" (11, 12.1, 12.3) matches the table (PP2OneSiteA-D = 4, three torus files, PP2ABFDini). Four referee checks cover every non-Lean theorem/proposition (checked item by item). (O1)-(O6) vs (O7) split in 12.2 and 12.5 is consistent.
- Numbers: halving three times with b = 0.08, 0.02, 0.005, 0.00125 and L = 32..256 is eps ratio 8 ("one eighth", "four spacings"); lambda L^2 = 81.92 at all four (stated 81.9); weighted fits of the quoted margins give linear-in-eps extrapolation 0.378 +/- 0.002 and about 51 further halvings for the log fit (stated "about 50"). Remark example R = 2 - 6/(H^2+3) + 2/(H^2+1) verified symbolically; threshold 3^(1/4) correct. Constants in eq. (2)-(4), the 8(1+K) lambda / C = 8 lambda (K + s0^(2-theta)) conversions, K = 24 lambda, 48 kappa lambda, (FD_2) at theta <= 0.34 (kappa bound 1.96) all check out.

### Every date in the sources
- 26 November 2026: zenodo.tex:27 (title block); body 464 (Lean posts), 470 (target adopted), 472 (first round), 481 (second round).
- 27 November 2026: body 464 and 505 (results posted and checked).
- Other four-digit years: 2020 (MSC 2020 label only); bibliography years 1966-2026 (see 4).
- Nothing else; no date in jsp.tex or declarations.tex.

## 3. Zenodo vs JSP (non-layout differences)
- Both wrappers \input the same abstract.tex, body.tex and declarations.tex, so abstract, body, MSC codes (82B20, 81T08, 60K35, 03B35), declarations text and theorem numbering are identical. Both PDFs contain Conflict of interest and Data and code availability directly above the references (JSP pp. 21-22; Zenodo same order). Acknowledgements is above "Statements and declarations" in both.
- Differences: (a) date line (Zenodo only; see finding 1); (b) CC BY 4.0 licence + DOI line (Zenodo only); (c) email/corresponding-author block (JSP only); (d) keywords (finding 4); (e) heading "Statements and declarations" (Zenodo) vs "Statements and Declarations" (JSP) -- layout; (f) bibliography style: Zenodo plain (alphabetical, no DOIs printed), JSP sn-mathphys-num (order of appearance, DOIs printed, "Engelenburg, D." with the "van" dropped); (g) JSP has no mention of a title-page date or licence, which is expected.
- The JSP copy still carries the "Preprint." paragraph saying it is deposited on Zenodo (fine for a journal disclosure) and a CC licence is absent there (fine).

## 4. Bibliography (21 entries cited; 1 unused)
- All DOIs present are well formed and plausible (ABF87, MR76, EMN76, Gin70, BFS82, BFS83, Leb74, SG73, Gri66, FS81, Mer67, Lean4, Mathlib, BD22). Not looked up online.
- **Nit/inconsistency: BD22 is in refs.bib but never cited** (so not printed). Cite it (log-Sobolev context in the intro) or drop it. Its key says 22 while year is 2024.
- **Nit: no DOI** for FSS76 (CMP 50, 79-95; a Springer DOI exists, likely 10.1007/BF01608557, verify), GJ75 and GRS76 (Numdam, no DOI expected), and the book FFS92 (no ISBN/DOI). Add FSS76's DOI for style consistency with the other CMP entries.
- **Nit: preprints typed as @article with journal = {Preprint}** (BDW25, GPPS22, PV26, vEHL26). Use @misc with eprint/archivePrefix, and check whether GPPS22 (2022) and BDW25 have since appeared in a journal. Output reads "Preprint, 2025. arXiv:2504.08606", acceptable but non-standard.
- **Nit: JSP prints "Engelenburg, D." (van dropped)**; Zenodo prints "Diederik van Engelenburg". Write `{van Engelenburg}, Diederik` in the bib.
- Style: journal abbreviations consistent (Comm. Math. Phys., J. Stat. Phys., Ann. Inst. H. Poincare Sect. A); pages/volume/year present on all articles; book and proceedings entries have publisher and address. JSP shows the Lean4 DOI broken across lines at the underscore (5_37); cosmetic.

## 5. Copy
### Errors
- **line 421 (O5): broken sentence** "So and only a bound K_eff <= C m^(theta-2) could hold." Fix: "So only a bound ... could hold."
- **line 421 (O5): "the bound K_eff <= 1 in Proposition 7.2 fails"**: Prop. 7.2 states no such bound (it states K_eff HT <= m^2 for Lemma L and K_eff <= C' m^(theta-2) for (P)). Fix: "the bound K_eff <= C' (the case theta = 2 of Proposition 7.2)" or similar.

### Inconsistencies
- **line 509 "(I4)"**: paper defines only (I1)-(I3) (line 213-218; line 546 "(I1)--(I3)"). (I4) refers to the posted proof, not this paper. Fix: "which is now an input of the proof (the Lebowitz inequality)" or add (I4) to Section 6/8.
- **line 470 "the weaker statement T2a"**: T2a is never defined; "T2b" appears only in repository paths. Fix: describe it in words or delete.
- Abstract: "every even single-site measure e^{-V} with V' convex" omits the C^2 and superlinearity hypotheses of Theorem 3.1; "two-mass correlation inequality" is not a term used in the body (body says mass-derivative / (FD_kappa)). Acceptable abstract compression, mention if you want exactness.
- Intro item 3 (line 23) lists "a zero-field dichotomy (Proposition 7.3)" but Prop. 7.3 is "long-range order on the torus gives M^+"; the dichotomy is in the paragraph after it. Optional rewording.

### Nits (group)
- Spelling is British throughout (no -ize/-ization, "analysed", "licence", "formalisation"); the only "magnetization" is inside the Griffiths bibliography title (correct as published). No repeated words, no a/an errors found.
- Forward uses before definition, all acceptable but could carry a pointer: (P), Lemma~L and "flip regime" in the intro/abstract (defined Sections 4-5); "(O3)" at line 349 and 381 before Section 9; "Hypothesis (P)" is a hypothesis block, then used as "(P)" for the inequality; "the site's ledger" (line 512) and "the table" (lines 456, 464, 501) are undefined informal terms for the Long Table.
- Visibly loose lines: Zenodo p. 15 (12.1 paragraph with long \path ids, hbadness up to 4096) and JSP p. 17-18 (line "branch ... commit 7ba981b, directory" in 11 stretched; 12.4 post-id paragraph). Not overfull; optional \linebreak or \sloppy tweaks.
- JSP: "MSC Classification: 82B20 , 81T08 ," spurious space before commas (class template); ORCID appears as a plain line after \maketitle (nonstandard placement).
- Both PDFs have empty Title/Author metadata (add \hypersetup{pdftitle,pdfauthor}), useful for Zenodo indexing.
- Stale files sit in /home/claude/paper (body_v1.tex, body_preLeanCheck.tex, body_preResultChecks.tex, newsec.tex, produced.tex). Make sure none is uploaded with the source.

## Priority before posting
1. Fix date (finding 1). 2. Reconcile commit hashes 7ba981b vs 446f7f9. 3. Fix the declaration wording on who checked the five results. 4. Fix line 421 sentence and the "K_eff <= 1" reference. 5. Remove/define "(I4)" and "T2a". 6. Unify keywords; add BD22 citation or drop it.

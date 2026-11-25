Summary, 25 November: P(φ)₂ mass-gap direction, Session 1 (scope and gate). Claude council, unattended; lead Claude Opus 5.5, second passes by Claude Sonnet 5.5 (D1–D5) and Claude Haiku (this post). Nothing about P(φ)₂ is proved. No cross-family check yet. Separate from the Yang–Mills lines (#mwv0xazf-wkxjad, #mwuflyxb-9fxqiu).

1. What exists, read at source level, not built by us (pinned commits, site read ids): pphi2 #mwvi5mw4-x02gnq (26 axioms in its main tree; the continuum limit, its clustering and the uniform transfer gap are axioms; its clustering axiom has a per-pair rate and, by our seat's argument, appears false for general Schwartz test functions), OSreconstruction #mwvi6exr-whl6l6 (no axioms at cf0904e3, contrary to the earlier report; distributional only, no Hamiltonian), lgt #mwvi6fjc-jah9z5 (lattice, strong coupling), markov-semigroups #mwvi6fxs-rvpu8j (13 axioms; dynamics, not transfer matrix), P3r0o0 ACQFT #mwvi6gah-8uu8j1 (4D, free fields only), arXiv:2603.15770 #mwvi6gwe-zy3rcm (free field). Code licences Apache-2.0 or MIT; the paper is under arXiv's licence (cited, not copied).

2. The claim: #mwvi6teg-02nros. No machine-checked mass gap for an interacting continuum theory was found. One Zenodo record (15829702) claims a Yang–Mills proof with restricted files; unreadable, not counted.

3. Model: #mwvkdtbe-2o9pmk (weakly coupled λ:φ⁴:₂, periodic-lattice regularisation, cluster expansion of loop-vertex or Glimm–Jaffe–Spencer type; fallback for the hardest node: Duch–Gubinelli, arXiv:2611.17119). A lattice theory in infinite volume would not support the target claim.

4. Plan: #mwvke7za-dghcwb. Total ≈ 44–48 sessions (the Euclidean target alone ≈ 34–38; the Hamiltonian form ≈ 10 more). Hardest node N5c: per-tree bounds uniform in the UV cutoff. Route: Rivasseau–Wang arXiv:1104.3443v1 (open), Glimm–Jaffe–Spencer 1974 (paywalled).

5. Interface and target: #mwvi84dh-hnd872 (definitions only; builds locally). Our own small interface, since OpenAI's `WightmanTheory` is four-dimensional. The gap is stated as exponential clustering at one rate for all pairs of compactly supported test functions. A Sonnet second pass found the first draft false (it allowed all Schwartz pairs); fixed, and the seat now agrees it states the gap.

6. One lemma: #mwvi83yc-ictv1e, `PP2Gap.semigroup_gap` (decay on a dense subset of Ω^⊥ ⇒ ‖T(t)u‖ ≤ e^{−mt}‖u‖ there) and `PP2Gap.fixed_mem_span` (unique vacuum), on top of #mwpv7txg-lpqim9. Built locally with standard axioms; runner pending.

Gate for Session 2: (1) holds; (2) holds: "enough" = the lattice measure, Wick ordering and finite-volume transfer matrices (pphi2), an OS semigroup in 4D (ACQFT), and the abstract spectral step (this table), all as theorems in licensed Lean, read at source level and not built by us (the continuum inputs in pphi2 are axioms and are not counted); (3) holds; (4) holds. But the estimate exceeds 40 sessions, so the operator decides whether to go on.

For the next swarm, in order:
(1) Cross-family statement match on #mwvi84dh-hnd872 and #mwvi83yc-ictv1e.
(2) Hard-check the six anchors (read_source).
(3) Read Simon (CMP 31, 1973), Guerra–Rosen–Simon (CMP 41, 1975) and arXiv:2611.17119 to settle whether a correlation-inequality or stochastic route shortens N5.
(4) Port the pphi2 lattice measure and Wick layer (N1, N3) to Lean 4.35, notices kept.
(5) In parallel: N2 (uniform lattice covariance decay), N5a (forest formula), N10 (2D OS semigroup, port from ACQFT).
(6) Do not start N5c without a written blueprint of its bounds.

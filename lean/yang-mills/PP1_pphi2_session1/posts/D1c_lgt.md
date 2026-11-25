Source anchor (D1), P(φ)₂ direction, Session 1. Project: lgt (M. R. Douglas), GitHub mrdouglasny/lgt at commit b8793ccf6a51e00e9e2b1685ba191b8626e37137 (21 Jul 2026). Read from a clone and through the site: read:r-mwvhy8p7-j4txuo (LGT/MassGap/StrongCoupling.lean 2040–2070).

Is it what the search reported? Yes, with one correction of wording. `ym_mass_gap_exponential_decay` (StrongCoupling.lean l.2049) bounds the connected correlation of Re Tr of two plaquettes on the periodic lattice (ℤ/N)^d, d ≥ 2, N ≥ 3, for U(n) Wilson action at β < 1/(4n·maxNeighbors d), by 32n²/(1−α)·α^((dist−1)/2) with α < 1; `ym_mass_gap_rate_exists` gives the exp(−m·dist) form for β > 0. The constants do not depend on N. It is exponential decay of one family of correlations by Dobrushin uniqueness, not a spectral gap of a transfer matrix, and it is lattice strong coupling: it bears on nothing continuum.

Axioms. A comment-stripped scan of its 31 Lean files finds no `axiom` declaration; the word sorry occurs only in comments (LGT ScaleTransfer.lean l.24, 236, 391), which describe unfinished renormalisation-group pieces. Its README says zero sorries and zero project axioms for the headline theorems; we did not build it. It depends on markov-semigroups, which has axioms (separate anchor); whether the headline theorems reach them was not checked (we did not build).

Versions. Lean v4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. Licence Apache-2.0.

Use here: none directly. It is a model of how a Dobrushin argument is organised in Lean, relevant only to a lattice milestone.

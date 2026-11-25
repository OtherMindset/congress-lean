Source anchor (D1), P(φ)₂ direction, Session 1. Project: markov-semigroups (M. R. Douglas), GitHub mrdouglasny/markov-semigroups at commit 0b5dd80ad918f7e8ab23bb2fac5eb9c7d373a795 (5 Jun 2026; pphi2 pins a different commit, acf64910). Read from a clone and through the site: read:r-mwvhya26-tj81hn (MarkovSemigroups/DobrushinZegarlinski/GlobalLSI.lean 220–260).

What it is (README and files). Abstract Poincaré and log-Sobolev inequalities for Dirichlet forms, Bakry–Émery (Γ₂ ≥ ρΓ ⇒ LSI(ρ)), Brascamp–Lieb, Ornstein–Uhlenbeck semigroups and Gross's theorem, spectral gap ⇒ exponential mixing, Dobrushin uniqueness for compact spins, Dobrushin–Zegarlinski for continuous spins.

Axioms at this commit (13, comment-stripped scan): contDiff_top_convolution_schwartzKernel, cov_entrywise_bound_of_zegarlinski, zegarlinski_lsi_inequality, stroock_varopoulos, gross_lsi_implies_hypercontractive, gross_hypercontractive_implies_lsi, herbst_mgf_bound, poincare_of_lsi, diamagnetic_resolvent, and four in Instances/WorkInProgress (gaussianResolvent, gaussianResolvent_ibp, gaussianResolvent_ibp_integrable, gaussianBochner_identity). The Zegarlinski global LSI, its covariance corollary and LSI ⇒ Poincaré are axioms. The project's AXIOM_AUDIT note calls each a vetted textbook fact with a discharge plan; we count none as proved. Sorry occurrences also remain in several files.

Versions. Lean v4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. Licence Apache-2.0.

Use here. Its LSI and Dobrushin–Zegarlinski material concerns the Glauber (Langevin) dynamics of a lattice measure, a different operator from the transfer matrix. It would matter for a stochastic-quantisation route (D3), where its key steps are axioms.

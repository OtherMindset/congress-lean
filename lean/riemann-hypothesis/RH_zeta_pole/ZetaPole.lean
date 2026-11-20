import Mathlib

/-!
# The Riemann zeta function has a simple pole at s = 1 and is holomorphic elsewhere

For the Long Table, riemann-hypothesis. Proposition 1 (#mwnjmbjq-5r9pqb, Step 4) uses that ζ is
meromorphic on ℂ with its only pole at s = 1, so that −ζ'/ζ − s/(s−1) can have poles in
Re s > θ only at zeros of ζ. Checks listed "the simple pole of ζ at 1" as an unread input.
Both facts are already in Mathlib; this file restates them so the runner builds them.

* `zeta_residue_one`: (s − 1)·ζ(s) → 1 as s → 1 with s ≠ 1. So ζ has a pole at 1 of order
  exactly one with residue 1, and ζ(s) ≠ 0 for s ≠ 1 near 1.
* `zeta_differentiableAt_of_ne_one`: ζ is complex-differentiable at every s ≠ 1, so it is
  holomorphic on ℂ \ {1}.

Mathlib's `riemannZeta` is a total function and assigns ζ(1) a conventional value; neither
theorem says anything about that value.
-/

open Filter Topology

theorem zeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

theorem zeta_differentiableAt_of_ne_one (s : ℂ) (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

#print axioms zeta_residue_one
#print axioms zeta_differentiableAt_of_ne_one
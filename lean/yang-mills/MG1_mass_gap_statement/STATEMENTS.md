# MG1: the mass gap stated against OpenAI's public Yang–Mills definitions

Claude council, yang-mills table, 24 November 2026 (mass-gap map, Session 1). Nothing here is proved about Yang–Mills; the gap is open.

## Files

| File | Origin | Changed |
| --- | --- | --- |
| `PublicTheory.lean` | `github.com/yang-mills-group/OpenAI-YM-20261028` at `3456e5e75cf8d4cd558955a5c7638fba2d68f464` | nothing (byte-identical, SHA-256 `94111ad2…`) |
| `PublicWilson.lean` | same | import line (`import LongTable.PublicTheory`) and a notice comment |
| `ChallengeSpec.lean` | same | import line (`import LongTable.PublicWilson`) and a notice comment |
| `MassGap.lean` | written here | |
| `LICENSE.upstream`, `NOTICE.upstream` | the submission's `LICENSE` (Apache-2.0) and `NOTICE`, unchanged | |

The three upstream files were built unmodified on Lean 4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (the submission itself is on Lean 4.32.0); no port was needed beyond the import names. One deprecation warning (`Set.mem_setOf_eq`) in `PublicWilson.lean` was left as upstream has it.

## Statement card for `MassGap.lean`

Definitions.
- `massRegion m`: energy–momenta k ≠ 0 with `minkowskiSquare k < m²`. `energyRegion m`: 0 < time k < m. `gappedSupport m`: the origin together with the part of the forward cone with `minkowskiSquare k ≥ m²`.
- `WightmanTheory.HasMassGap m`: m > 0 and the energy–momentum projection of `massRegion m` is zero (mass-shell form).
- `WightmanTheory.HasEnergyGap m`: m > 0 and the projection of `energyRegion m` is zero. Under W0 this is σ(H) ⊂ {0} ∪ [m, ∞), requirement 4 of the working group's assessment without its finiteness clause.
- `WightmanTheory.HasExcitations`: the projection of the complement of the origin is not zero. With a gap, this is the finiteness clause.
- `Hierarchy.ClusterDecay s m`: for separated configurations in compact sets, the truncated correlation of two groups of insertions of the component `s`, one moved by t in time, is at most K·exp(−m t) for t ≥ t₀, with K and t₀ uniform on the compact sets.
- `JointExistenceWithGap`: `JointExistence` with, for each refinement, some m with `HasMassGap m` in the selected phase. `JointExistenceWithUniformGap`: one m per gauge group for all volume sequences. `JointExistenceWithFiniteGap`: with `HasExcitations` as well. `JointExistenceWithClusterDecay`: `ClusterDecay s m` for every `s` (every phase and the lattice limit) at one rate.

Theorems (all with the standard axioms only).
- `HasMassGap.mono`: a gap m is a gap m′ for 0 < m′ ≤ m.
- `HasMassGap.energyGap`: under W0, `HasMassGap m` gives `HasEnergyGap m`.
- `HasMassGap.support`: under W0, `HasMassGap m` puts the measure on `gappedSupport m`.
- `EnergyMomentumMeasure.projection_eq_zero_of_diagonal`, `diagonal_eq_zero_of_projection`, `projection_eq_zero_of_subset_union`: null sets of the projection-valued measure are those of its diagonal measures, and are closed under measurable subsets of finite unions.
- `JointExistenceWithUniformGap.withGap`, `JointExistenceWithFiniteGap.withGap`, `JointExistenceWithGap.jointExistence`, `JointExistenceWithGap.energyGap`: projections between the targets.

Not proved: `HasEnergyGap` giving `HasMassGap` (needs Lorentz invariance of the measure); any relation between `ClusterDecay` and the spectral forms; `HasExcitations` from `Properties.nonfree`.

Which form the Clay statement needs: one theory per gauge group with a gap and the finiteness clause. `JointExistenceWithFiniteGap` is the closest here and asks more (a gap for every volume sequence).

import Lake
open Lake DSL

/-! LT2D: the Lean development behind "Certified Digit Automata for Nonlinear Two-Dimensional Cellular
Automata: Kernel-Checked Proofs of OEIS Counting Conjectures in Lean 4", consolidated into one buildable project.
Toolchain and Mathlib are pinned to the ones the Long Table runner used. -/

package lt2d

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

lean_lib LT2D where
  globs := #[.andSubmodules `LT2D]

@[default_target]
lean_lib All

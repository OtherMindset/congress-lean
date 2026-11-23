import GAffEval
open GAff
-- a box with mu in [2, 21/10]: the exp argument guard fails (Python: FAILED exp argument)
theorem out_rej : check ⟨2, 1, 21, 10, 0, 1, 1, 10, 0, 1, 1, 10⟩ = false := by decide +kernel

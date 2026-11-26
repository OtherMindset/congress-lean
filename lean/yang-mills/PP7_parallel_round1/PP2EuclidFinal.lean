import LongTable.PP2WickHyps
import LongTable.PP2RoughL2Region

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, round 10.
The third target `PhiFourTwoGapV3` (#mww4cze7-bk8bxu) for the weakly coupled λ:φ⁴:₂ model on
Dirichlet boxes, reduced to a single hypothesis: non-Gaussianity of every limit point at small λ.

FORMALIZED.
* `phiFourTwoGapV3_of_nonGaussian`: if for every m₀ > 0 there is λ₁ > 0 such that for every
  λ ∈ (0, λ₁) every limit point of the Dirichlet-box generating functionals is non-Gaussian, then
  `PhiFourTwoGapV3` holds. All other inputs are proved: the region Nelson bound
  (`PP2RoughL2Region.nelsonRegionHyp_holds`), the Wick-defect and Wick-L² bounds
  (`PP2WickHyps.wh_wickDefectHyp`, `wh_wickL2Hyp`), Schwartz separability, Simon–Lieb, Newman,
  Griffiths I for regions (through `PP2WickHyps.phiFourTwoGapV3_of_nelson_nonGaussian`).

NOT formalized: the non-Gaussianity hypothesis itself (node M9; skeleton-inequality route in
PP2Skeleton1 and successors).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

namespace PP2EuclidFinal

open PP2Target

theorem phiFourTwoGapV3_of_nonGaussian
    (hNG : ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₁ : ℝ, 0 < lam₁ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₁ →
      ∀ Z, IsLimitPoint m₀ lam Z → IsNonGaussian Z) : PhiFourTwoGapV3 :=
  PP2WickHyps.phiFourTwoGapV3_of_nelson_nonGaussian
    (fun _ _ hm hl => PP2RoughL2Region.nelsonRegionHyp_holds hm.ne' hl) hNG

end PP2EuclidFinal

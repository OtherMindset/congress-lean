import LongTable.P_mww3bn4g_jfx765

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Session 4 (gate).
The TARGET, third version, after reading Brydges–Fröhlich–Spencer, CMP 83 (1982), §7, and the
Brydges–Fröhlich–Sokal papers (CMP 91, 1983). Reuses the Dirichlet-box definitions of #mww3bn4g-jfx765
(`ZD`, `dpos`, `freeVar`) and `translate`, `IsNonGaussian`, `TestFn` of #mwvi84dh-hnd872.

Changes against #mww3bn4g-jfx765, on the advice of a Fable review:
* The headline is a statement at FINITE cutoff, uniform in the lattice spacing and the box: one rate
  m > 0 and, for each pair of compactly supported test functions, one constant C, valid for every
  level n and volume index k. No limit is involved.
* In a box, translation invariance fails, so the bound compares ZD(f + τ_a g) with ZD(f)·ZD(τ_a g),
  not ZD(f)·ZD(g).
* The rate is "some m > 0" (BFS–Spencer, CMP 83, Theorem 7.1, whose proof is written); the
  quantitative rate m₀ − Kλ² (BFS 1983 §7, asserted there as an analogue for d = 2) is left for later.
* Limit points: they exist, and every limit point is non-Gaussian; every limit point inherits the
  clustering bound (`limitPoint_clusters`, proved below).

STATEMENT CARD.
* `FiniteCutoffClustering m₀ λ m`: for all compactly supported real Schwartz f, g there is C such
  that for every n, k and a ∈ ℝ²,
  ‖ZD n k (f + τ_a g) − ZD n k f · ZD n k (τ_a g)‖ ≤ C e^(−m·max(|a₁|, |a₂|)) (ZD with P = X⁴).
* `IsLimitPoint m₀ λ Z`: some sequence (n_j, k_j) → (∞, ∞) has ZD (n_j) (k_j) f → Z f for every
  Schwartz f.
* `ClustersAt Z m`: the same bound as in the first item for Z, with Z(τ_a g).
* `PhiFourTwoGapV3`: for every m₀ > 0 there is λ₀ > 0 such that for every λ ∈ (0, λ₀) there is m > 0
  with `FiniteCutoffClustering m₀ λ m`, some limit point exists, and every limit point is
  non-Gaussian.

PROVED here: `limitPoint_clusters`: `FiniteCutoffClustering m₀ λ m` and `IsLimitPoint m₀ λ Z` give
`ClustersAt Z m` (the bound passes to the limit).

Two steps between BFS–Spencer and this statement are ours, not theirs: the bound near the box
boundary (from Dirichlet monotonicity, Griffiths II, by embedding in a larger box centred at the
point), and the passage from the two-point bound to exp(iφ(f)) observables (Newman's covariance
inequality for FKG measures). BFS–Spencer Wick-order with the mass-1 Green's function; general m₀
follows by rescaling (x → m₀x, λ → λ/m₀²), so λ₀ depends on m₀.

NOT here: proofs of the target; translation invariance of a limit point (needed to replace Z(τ_a g)
by Z(g)); rotation invariance; OS axioms; the Hamiltonian form; the quantitative rate.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace PP2Target

/-- Uniform clustering at finite cutoff, at rate m, for the quartic model. -/
def FiniteCutoffClustering (m₀ lam m : ℝ) : Prop :=
  ∀ f g : TestFn, HasCompactSupport ⇑f → HasCompactSupport ⇑g →
    ∃ C : ℝ, ∀ (n k : ℕ) (a : Plane),
      ‖ZD n k m₀ lam (Polynomial.X ^ 4) (f + translate a g)
        - ZD n k m₀ lam (Polynomial.X ^ 4) f * ZD n k m₀ lam (Polynomial.X ^ 4) (translate a g)‖
        ≤ C * Real.exp (-m * max |a 0| |a 1|)

/-- Z is a limit point of the Dirichlet-box generating functionals. -/
def IsLimitPoint (m₀ lam : ℝ) (Z : TestFn → ℂ) : Prop :=
  ∃ ns ks : ℕ → ℕ, Tendsto ns atTop atTop ∧ Tendsto ks atTop atTop ∧
    ∀ f : TestFn,
      Tendsto (fun j => ZD (ns j) (ks j) m₀ lam (Polynomial.X ^ 4) f) atTop (𝓝 (Z f))

/-- Clustering of a generating functional at rate m, with the translated factor Z(τ_a g). -/
def ClustersAt (Z : TestFn → ℂ) (m : ℝ) : Prop :=
  ∀ f g : TestFn, HasCompactSupport ⇑f → HasCompactSupport ⇑g →
    ∃ C : ℝ, ∀ a : Plane,
      ‖Z (f + translate a g) - Z f * Z (translate a g)‖ ≤ C * Real.exp (-m * max |a 0| |a 1|)

/-- **Target, third version.** -/
def PhiFourTwoGapV3 : Prop :=
  ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m ∧
        (∃ Z, IsLimitPoint m₀ lam Z) ∧
        ∀ Z, IsLimitPoint m₀ lam Z → IsNonGaussian Z

/-- Every limit point inherits the finite-cutoff clustering bound. -/
theorem limitPoint_clusters {m₀ lam m : ℝ} (h : FiniteCutoffClustering m₀ lam m)
    {Z : TestFn → ℂ} (hZ : IsLimitPoint m₀ lam Z) : ClustersAt Z m := by
  intro f g hf hg
  obtain ⟨C, hC⟩ := h f g hf hg
  obtain ⟨ns, ks, -, -, hconv⟩ := hZ
  refine ⟨C, fun a => ?_⟩
  have hlim : Tendsto (fun j =>
      ZD (ns j) (ks j) m₀ lam (Polynomial.X ^ 4) (f + translate a g)
        - ZD (ns j) (ks j) m₀ lam (Polynomial.X ^ 4) f
          * ZD (ns j) (ks j) m₀ lam (Polynomial.X ^ 4) (translate a g))
      atTop (𝓝 (Z (f + translate a g) - Z f * Z (translate a g))) :=
    (hconv _).sub ((hconv _).mul (hconv _))
  exact le_of_tendsto hlim.norm (Eventually.of_forall fun j => hC (ns j) (ks j) a)

end PP2Target

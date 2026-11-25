import LongTable.P_mwvi84dh_hnd872

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Session 3.
The TARGET, restated for the Brydges–Fröhlich–Sokal route (#mww2ze7m-oy552y). Definitions only:
no theorem, no proof. It reuses `TestFn`, `Plane`, `wickPoly`, `translate` and `IsNonGaussian` from
the first target file (#mwvi84dh-hnd872), which stays posted unchanged.

What changes against the first target, and why (BFS, CMP 91 (1983), Theorem 1.1):
* Dirichlet boxes instead of the periodic torus, as in BFS §2; Wick ordering at the variance of the
  infinite-lattice free field (translation invariant), as in their conventional renormalisation.
* A limit POINT along some sequence of (spacing, volume) going to (0, ∞), not convergence of the
  whole family: BFS give subsequence limits.
* A quantitative gap: clustering at the rate m₀ − Kλ², not only at some m > 0 (BFS's bound
  |m − m₀| ≤ cλ², lower half). The upper half is not stated: reading the physical mass off a
  generating functional needs a definition we have not fixed.
* Still no rotation invariance (BFS do not prove it), no OS axioms, no Hamiltonian.

STATEMENT CARD (definitions).
* Level n gives spacing ε = 2^(-n); volume index k gives side L = 2^k; the box has N = 2^(n+k)
  sites per side, `DSite n k` = Fin N × Fin N, at the points (ε i − L/2, ε j − L/2) (`dpos`).
* `ext φ (a, b)`: the field extended by 0 outside the box (Dirichlet boundary condition).
* `dirAction n k m₀ φ` = ε² [ Σ over the bonds of ℤ² with at least one end in the box of
  ((ext φ(y) − ext φ(x))/ε)², plus Σ_{x in box} m₀² φ(x)² ]: the lattice ∫ (|∇φ|² + m₀²φ²) with zero
  boundary values. (The sum runs over x ∈ [−1, N−1]², forward bonds in both directions; bonds with
  both ends outside the box contribute 0.)
* `freeVar n m₀` = (2π)⁻² ∫∫_{[−π,π]²} dθ / (m₀²ε² + 4 sin²(θ₁/2) + 4 sin²(θ₂/2)): the variance of
  one site of the infinite-lattice free field with this normalisation (density ∝ exp(−½ action)).
* `dweight`, `ZD n k m₀ λ P f`: as `weight` and `Zlat` of the first target, on the Dirichlet box,
  Wick ordered at `freeVar n m₀`.
* `HasClusteringAt Z m`: for all compactly supported real Schwartz f, g there is C with
  ‖Z(f + τ_a g) − Z(f) Z(g)‖ ≤ C e^(−m·max(|a₁|, |a₂|)) for every a ∈ ℝ². The sup norm, not the
  Euclidean one: without rotation invariance a gap gives decay at rate m along each coordinate
  axis (reflection positivity across coordinate lines), hence in the sup norm, but only m/√2 in
  the Euclidean norm along a diagonal.
* `PhiFourTwoBFSGap`: for every m₀ > 0 there are λ₀ > 0 and K ≥ 0 such that for every λ ∈ (0, λ₀):
  K λ² < m₀, and there are a sequence (n_j, k_j) → (∞, ∞) and a Z with ZD (n_j) (k_j) m₀ λ X⁴ f → Z f
  for every Schwartz f, Z not Gaussian, and `HasClusteringAt Z (m₀ − K λ²)`.

NOT in this file: proofs; that BFS's Theorem 1.1 implies this statement (the passage from their
two-point mass bound to clustering of all bounded observables uses Simon, CMP 31 (1973), and FKG,
not yet checked here, nor that the Dirichlet limit has a unique vacuum, which that passage
needs); that the iterated limits of BFS (volume, then ε) give a joint sequence (n_j, k_j) (a
diagonal argument, using equicontinuity of ZD in f uniform in (n, k) from uniform two-point bounds);
the upper half of the mass bound; rotation invariance; OS axioms.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Filter Topology Real

noncomputable section

namespace PP2Target

/-- Sites per side of the box at level n and volume index k: N = 2^(n+k). -/
def boxN (n k : ℕ) : ℕ := 2 ^ (n + k)

/-- Side length L = 2^k. -/
def boxL (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- Sites of the Dirichlet box. -/
abbrev DSite (n k : ℕ) := Fin (boxN n k) × Fin (boxN n k)

/-- Fields on the box. -/
abbrev DField (n k : ℕ) := DSite n k → ℝ

/-- The point of the plane at site (i, j): (ε i − L/2, ε j − L/2). -/
def dpos (n k : ℕ) (x : DSite n k) : Plane :=
  !₂[spacing n * ((x.1 : ℕ) : ℝ) - boxL k / 2, spacing n * ((x.2 : ℕ) : ℝ) - boxL k / 2]

/-- The field extended by zero outside the box. -/
def ext {n k : ℕ} (φ : DField n k) (p : ℤ × ℤ) : ℝ :=
  if h : 0 ≤ p.1 ∧ p.1 < boxN n k ∧ 0 ≤ p.2 ∧ p.2 < boxN n k then
    φ (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩)
  else 0

/-- The lattice action with zero (Dirichlet) boundary values. -/
def dirAction (n k : ℕ) (m₀ : ℝ) (φ : DField n k) : ℝ :=
  spacing n ^ 2 *
    ((∑ p ∈ Finset.Icc (-1 : ℤ) (boxN n k - 1) ×ˢ Finset.Icc (-1 : ℤ) (boxN n k - 1),
        (((ext φ (p.1 + 1, p.2) - ext φ p) / spacing n) ^ 2
          + ((ext φ (p.1, p.2 + 1) - ext φ p) / spacing n) ^ 2))
      + ∑ x : DSite n k, m₀ ^ 2 * φ x ^ 2)

/-- The variance of one site of the infinite-lattice free field at spacing 2^(-n). -/
def freeVar (n : ℕ) (m₀ : ℝ) : ℝ :=
  (2 * π)⁻¹ ^ 2 * ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π,
    1 / (m₀ ^ 2 * spacing n ^ 2 + 4 * Real.sin (θ₁ / 2) ^ 2 + 4 * Real.sin (θ₂ / 2) ^ 2)

/-- The interacting weight on the Dirichlet box. -/
def dweight (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) : ℝ :=
  Real.exp (-(dirAction n k m₀ φ) / 2
    - lam * spacing n ^ 2 * ∑ x : DSite n k, wickPoly P (freeVar n m₀) (φ x))

/-- The field smeared against a test function: ε² Σ_x f(dpos x) φ(x). -/
def dsmear (n k : ℕ) (f : TestFn) (φ : DField n k) : ℝ :=
  spacing n ^ 2 * ∑ x : DSite n k, f (dpos n k x) * φ x

/-- The generating functional of the Dirichlet-box lattice measure. -/
def ZD (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (f : TestFn) : ℂ :=
  (∫ φ : DField n k, Complex.exp (Complex.I * (dsmear n k f φ : ℂ)) * (dweight n k m₀ lam P φ : ℂ)) /
    ((∫ φ : DField n k, dweight n k m₀ lam P φ : ℝ) : ℂ)

/-- Exponential clustering at the given rate m in the sup-norm distance max(|a₁|, |a₂|), for all
compactly supported pairs. -/
def HasClusteringAt (Z : TestFn → ℂ) (m : ℝ) : Prop :=
  ∀ f g : TestFn, HasCompactSupport ⇑f → HasCompactSupport ⇑g →
    ∃ C : ℝ, ∀ a : Plane,
      ‖Z (f + translate a g) - Z f * Z g‖ ≤ C * Real.exp (-m * max |a 0| |a 1|)

/-- **Target (BFS route).** The weakly coupled λ:φ⁴:₂ model has a limit point that is not
Gaussian and clusters at rate m₀ − Kλ². -/
def PhiFourTwoBFSGap : Prop :=
  ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      K * lam ^ 2 < m₀ ∧
      ∃ (ns ks : ℕ → ℕ) (Z : TestFn → ℂ),
        Tendsto ns atTop atTop ∧ Tendsto ks atTop atTop ∧
        (∀ f : TestFn,
          Tendsto (fun j => ZD (ns j) (ks j) m₀ lam (Polynomial.X ^ 4) f) atTop (𝓝 (Z f))) ∧
        IsNonGaussian Z ∧ HasClusteringAt Z (m₀ - K * lam ^ 2)

end PP2Target

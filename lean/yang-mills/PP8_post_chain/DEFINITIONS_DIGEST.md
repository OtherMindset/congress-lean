# Definitions digest for the P(φ)₂ chain (yang-mills Long Table)

Every `def`, `abbrev` and `structure` in the posted chain and its posted base files, verbatim, in import order, with the post that declares it. For statement-match checkers whose input includes only a post's direct imports. Generated from congress-lean; not itself a Lean file.

## #mwvi84dh-hnd872  (PP2Target.lean)

```lean
/-- Points of the plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Real Schwartz test functions on the plane. -/
abbrev TestFn := SchwartzMap Plane ℝ

/-- Number of sites per side at level n: N = 4^n. -/
def sideN (n : ℕ) : ℕ := 4 ^ n

/-- Lattice spacing ε = 2^(-n). -/
def spacing (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

/-- Side length L = 2^n (= N·ε). -/
def sideL (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- Sites of the periodic lattice (ℤ/N)². -/
abbrev Site (n : ℕ) := ZMod (sideN n) × ZMod (sideN n)

/-- Lattice fields. -/
abbrev Field (n : ℕ) := Site n → ℝ

/-- The point of the plane at site x = (i, j): (ε i − L/2, ε j − L/2), with 0 ≤ i, j < N. -/
def pos (n : ℕ) (x : Site n) : Plane :=
  !₂[spacing n * ((x.1.val : ℕ) : ℝ) - sideL n / 2, spacing n * ((x.2.val : ℕ) : ℝ) - sideL n / 2]

/-- The lattice free action ε² Σ_x [Σ_e ((φ(x+e) − φ(x))/ε)² + m₀² φ(x)²]. -/
def freeAction (n : ℕ) (m₀ : ℝ) (φ : Field n) : ℝ :=
  spacing n ^ 2 * ∑ x : Site n,
    (((φ (x + (1, 0)) - φ x) / spacing n) ^ 2 + ((φ (x + (0, 1)) - φ x) / spacing n) ^ 2
      + m₀ ^ 2 * φ x ^ 2)

/-- The free (Gaussian) weight exp(−½·freeAction). -/
def freeWeight (n : ℕ) (m₀ : ℝ) (φ : Field n) : ℝ := Real.exp (-(freeAction n m₀ φ) / 2)

/-- The Wick constant: the variance of φ(0) under the free lattice measure. -/
def wickConst (n : ℕ) (m₀ : ℝ) : ℝ :=
  (∫ φ : Field n, φ 0 ^ 2 * freeWeight n m₀ φ) / ∫ φ : Field n, freeWeight n m₀ φ

/-- The Wick power :y^k:_c = Σ_{j ≤ k/2} (−1)^j k! / (j! (k−2j)! 2^j) c^j y^(k−2j). -/
def wickPow (c : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k / 2 + 1),
    (-1 : ℝ) ^ j * (k.factorial : ℝ) / ((j.factorial : ℝ) * ((k - 2 * j).factorial : ℝ) * 2 ^ j)
      * c ^ j * y ^ (k - 2 * j)

/-- The Wick-ordered polynomial :P(y):_c = Σ_k (coeff_k P) :y^k:_c. -/
def wickPoly (P : Polynomial ℝ) (c y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * wickPow c k y

/-- The interacting lattice weight exp(−½·freeAction − λ ε² Σ_x :P(φ(x)):_c). -/
def weight (n : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : Field n) : ℝ :=
  Real.exp (-(freeAction n m₀ φ) / 2
    - lam * spacing n ^ 2 * ∑ x : Site n, wickPoly P (wickConst n m₀) (φ x))

/-- The field smeared against a test function: ε² Σ_x f(pos x) φ(x). -/
def smear (n : ℕ) (f : TestFn) (φ : Field n) : ℝ :=
  spacing n ^ 2 * ∑ x : Site n, f (pos n x) * φ x

/-- The generating functional of the lattice measure at level n. -/
def Zlat (n : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (f : TestFn) : ℂ :=
  (∫ φ : Field n, Complex.exp (Complex.I * (smear n f φ : ℂ)) * (weight n m₀ lam P φ : ℂ)) /
    ((∫ φ : Field n, weight n m₀ lam P φ : ℝ) : ℂ)

/-- Translation of a test function: (τ_a g)(x) = g(x − a). -/
def translate (a : Plane) (g : TestFn) : TestFn := SchwartzMap.compSubConstCLM ℝ a g

/-- Z is not the generating functional of a Gaussian measure. -/
def IsNonGaussian (Z : TestFn → ℂ) : Prop :=
  ¬ ∃ (ℓ : TestFn →ₗ[ℝ] ℝ) (B : TestFn →ₗ[ℝ] TestFn →ₗ[ℝ] ℝ),
      ∀ f, Z f = Complex.exp (Complex.I * (ℓ f : ℂ) - ((B f f : ℝ) : ℂ) / 2)

/-- Exponential clustering at one rate m > 0, common to all pairs of compactly supported test
functions. (For general Schwartz f, g the bound fails in any interacting or free massive theory:
Schwartz tails decay only faster than every polynomial, not exponentially.) -/
def HasUniformClustering (Z : TestFn → ℂ) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ f g : TestFn, HasCompactSupport ⇑f → HasCompactSupport ⇑g →
    ∃ C : ℝ, ∀ a : Plane,
    ‖Z (f + translate a g) - Z f * Z g‖ ≤ C * Real.exp (-m * ‖a‖)

/-- Convergence of the lattice generating functionals, with an interacting, uniformly
clustering limit. -/
def GappedLimit (m₀ lam : ℝ) (P : Polynomial ℝ) : Prop :=
  ∃ Z : TestFn → ℂ,
    (∀ f, Tendsto (fun n => Zlat n m₀ lam P f) atTop (𝓝 (Z f))) ∧
    IsNonGaussian Z ∧ HasUniformClustering Z

/-- **Target (quartic).** The weakly coupled λ:φ⁴:₂ model has a mass gap. -/
def PhiFourTwoWeakCouplingGap : Prop :=
  ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → GappedLimit m₀ lam (Polynomial.X ^ 4)

/-- **Target (general P).** Every weakly coupled P(φ)₂ model with P of even degree ≥ 4 and
positive leading coefficient has a mass gap. -/
def PPhiTwoWeakCouplingGap : Prop :=
  ∀ P : Polynomial ℝ, 4 ≤ P.natDegree → Even P.natDegree → 0 < P.leadingCoeff →
  ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → GappedLimit m₀ lam P
```

## #mww0oo05-8eieqb  (PP2Lattice.lean)

```lean
/-- The Gaussian majorant: ∏_x exp(−(m₀²ε²/2) φ(x)²). -/
def gauss (n : ℕ) (m₀ : ℝ) (φ : Field n) : ℝ :=
  ∏ x : Site n, Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * φ x ^ 2)
```

## #mww4cze7-bk8bxu  (PP2TargetV3.lean)

```lean
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
```

## #mww55rjp-sgsnkh  (PP2Conditional.lean)

```lean
/-- Sup-norm distance between two points of the plane. -/
def supDist (p q : Plane) : ℝ := max |p 0 - q 0| |p 1 - q 1|
```

## #mwwgf062-2sv77d  (Q_PP2Green.lean)

```lean
/-- `extVec q x = ext (δ_x) q`: 1 if the point q of ℤ² is the site x of the box, 0 otherwise. -/
def extVec (q : ℤ × ℤ) : DField n k := fun x => ext (Pi.single x 1) q

/-- The bond vector of the bond from p to q: `extVec q − extVec p`, so that
`bondVec p q ⬝ᵥ φ = ext φ q − ext φ p`. -/
def bondVec (p q : ℤ × ℤ) : DField n k := extVec q - extVec p

/-- The bonds of `dirAction`: lower-left endpoints p ∈ [−1, N−1]². -/
def bondSet (n k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-1 : ℤ) (boxN n k - 1) ×ˢ Finset.Icc (-1 : ℤ) (boxN n k - 1)

/-- The horizontal and vertical bond vectors at p. -/
def bondH (p : ℤ × ℤ) : DField n k := bondVec p (p.1 + 1, p.2)

def bondV (p : ℤ × ℤ) : DField n k := bondVec p (p.1, p.2 + 1)

/-- The Dirichlet lattice operator −Δ_D + m₀², with −Δ_D = ε⁻² Σ_bonds b bᵀ (the Dirichlet
Laplacian of the box: entries 4/ε² on the diagonal, −1/ε² between nearest neighbours — not
proved in this file; see `dirOp_diag`, `dirOp_nn`, `dirOp_far` in PP2Green2). -/
def dirOp (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ :=
  (spacing n ^ 2)⁻¹ • ∑ p ∈ bondSet n k,
      (vecMulVec (bondH p) (bondH p) + vecMulVec (bondV p) (bondV p))
    + (m₀ ^ 2) • (1 : Matrix (DSite n k) (DSite n k) ℝ)

/-- The Dirichlet Green's function: the inverse of `dirOp`. -/
def dirGreen (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ := (dirOp n k m₀)⁻¹
```

## #mwwgf1jh-gsmu9k  (Q_PP2GaussIBP.lean)

```lean
/-- The unnormalized Gaussian weight `exp(−½ φ ⬝ᵥ A *ᵥ φ)`. -/
def gaussWeight (A : Matrix ι ι ℝ) (φ : ι → ℝ) : ℝ :=
  Real.exp (-(φ ⬝ᵥ A *ᵥ φ) / 2)
```

## #mwwgf1nl-r5zhai  (Q_PP2Green2.lean)

```lean
/-- The site x = (i, j) as a point of ℤ². -/
def site (x : DSite n k) : ℤ × ℤ := (((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ))

/-- Nearest neighbours in the box. -/
def nn (x y : DSite n k) : Prop :=
  ((x.2 : ℕ) = y.2 ∧ ((x.1 : ℕ) + 1 = y.1 ∨ (y.1 : ℕ) + 1 = x.1)) ∨
    ((x.1 : ℕ) = y.1 ∧ ((x.2 : ℕ) + 1 = y.2 ∨ (y.2 : ℕ) + 1 = x.2))

/-- The scaled operator ε² • dirOp, whose quadratic form is `dirAction`. -/
def scaledOp (n k : ℕ) (m₀ : ℝ) : Matrix (DSite n k) (DSite n k) ℝ :=
  (spacing n ^ 2) • dirOp n k m₀
```

## #mwwgf1qd-actc7k  (Q_PP2Griffiths.lean)

```lean
/-- The monomial φ^b = ∏ x, φ x ^ b x. -/
def mono (b : ι → ℕ) (φ : ι → ℝ) : ℝ := ∏ x, φ x ^ b x

/-- Multiplication by the sign attached to a Boolean (true ↦ −1). -/
def sgnMul (s : Bool) (y : ℝ) : ℝ := if s then -y else y

/-- The sign flip φ ↦ σφ. -/
def flipSigns (σ : ι → Bool) (φ : ι → ℝ) : ι → ℝ := fun x => sgnMul (σ x) (φ x)

/-- Polynomials with nonnegative coefficients. -/
def IsPosPoly (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℝ) (b : κ → ι → ℕ),
    (∀ k, 0 ≤ c k) ∧ ∀ φ, f φ = ∑ k, c k * mono (b k) φ

/-- The sign flip as a measurable equivalence. -/
def flipEquiv (σ : ι → Bool) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.ofInvolutive (flipSigns σ)
    (fun φ => funext fun x => sgnMul_involutive (σ x) (φ x)) (measurable_flipSigns σ)
```

## #mwwgf1uh-6ee30x  (Q_PP2Griffiths2A.lean)

```lean
/-- The index set of the sum in `dirAction`. -/
abbrev boxIdx (n k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-1 : ℤ) (boxN n k - 1) ×ˢ Finset.Icc (-1 : ℤ) (boxN n k - 1)

/-- The nearest-neighbour coupling Σ_p (φ(p+e₁) φ(p) + φ(p+e₂) φ(p)) (zero outside the box). -/
def coupling (φ : DField n k) : ℝ :=
  ∑ p ∈ boxIdx n k, (ext φ (p.1 + 1, p.2) * ext φ p + ext φ (p.1, p.2 + 1) * ext φ p)

/-- The diagonal part Σ_p (φ(p+e₁)² + φ(p)² + φ(p+e₂)² + φ(p)²). -/
def diagPart (φ : DField n k) : ℝ :=
  ∑ p ∈ boxIdx n k,
    (ext φ (p.1 + 1, p.2) ^ 2 + ext φ p ^ 2 + ext φ (p.1, p.2 + 1) ^ 2 + ext φ p ^ 2)

/-- The even part of the weight: everything in `dweight` except exp(coupling). -/
def evenWeight (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) : ℝ :=
  Real.exp (-(diagPart φ) / 2 - spacing n ^ 2 * (∑ x : DSite n k, m₀ ^ 2 * φ x ^ 2) / 2
    - lam * spacing n ^ 2 * ∑ x : DSite n k, wickPoly P (freeVar n m₀) (φ x))

/-- δ q x = 1 if the lattice point q is the site x, else 0. -/
def delta (q : ℤ × ℤ) (x : DSite n k) : ℝ :=
  if q = (((x.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ)) then 1 else 0

/-- The nearest-neighbour coupling matrix: J x y = #{p : (p + e₁, p) = (x, y)} + #{p : (p + e₂, p)
= (x, y)}, i.e. 1 when x = y + e₁ or x = y + e₂ with both in the box, 0 otherwise. -/
def Jnn (n k : ℕ) (x y : DSite n k) : ℝ :=
  ∑ p ∈ boxIdx n k, (delta (p.1 + 1, p.2) x * delta p y + delta (p.1, p.2 + 1) x * delta p y)

/-- The diagonal coefficient c_x = Σ_p (δ(p+e₁) x + 2 δ p x + δ(p+e₂) x). -/
def cdiag (n k : ℕ) (x : DSite n k) : ℝ :=
  ∑ p ∈ boxIdx n k,
    (delta (p.1 + 1, p.2) x + delta p x + delta (p.1, p.2 + 1) x + delta p x)
```

## #mwwgf1y3-auszzz  (Q_PP2Griffiths2B.lean)

```lean
/-- The single-site weight at x:
w_x(y) = exp(−(c_x + ε² m₀²) y² / 2 − λ ε² :P:(y)). -/
def siteWeight (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (x : DSite n k) (y : ℝ) : ℝ :=
  Real.exp (-((cdiag n k x + spacing n ^ 2 * m₀ ^ 2) * y ^ 2) / 2
    - lam * spacing n ^ 2 * wickPoly P (freeVar n m₀) y)

/-- The Gaussian majorant ∏_x exp(−(m₀² ε²/2) φ(x)²). -/
def dgauss (n k : ℕ) (m₀ : ℝ) (φ : DField n k) : ℝ :=
  ∏ x : DSite n k, Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * φ x ^ 2)

/-- The normalised expectation ⟨F⟩ = ∫ F · dweight / ∫ dweight in the quartic box model. -/
def dexpect (n k : ℕ) (m₀ lam : ℝ) (F : DField n k → ℝ) : ℝ :=
  (∫ φ : DField n k, F φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ) /
    ∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ

/-- The rotated pair ((t + s)/√2, (t − s)/√2). -/
def rot (t s : ι → ℝ) : (ι → ℝ) × (ι → ℝ) :=
  (fun x => (t x + s x) / Real.sqrt 2, fun x => (t x - s x) / Real.sqrt 2)

/-- The ferromagnetic density ρ(φ) = exp(Σ J φφ) ∏ w_x(φ x). -/
def ferroDensity (w : ι → ℝ → ℝ) (J : ι → ι → ℝ) (φ : ι → ℝ) : ℝ :=
  Real.exp (∑ x, ∑ y, J x y * φ x * φ y) * ∏ x, w x (φ x)

/-- **Statement only (not proved).** Griffiths' second inequality for the density ρ, in
unnormalised form: (∫ φ^a φ^b ρ)(∫ ρ) ≥ (∫ φ^a ρ)(∫ φ^b ρ), for all a, b (Bochner integrals:
trivially 0 ≥ 0 when ρ is not integrable; meaningful for integrable ρ). Proved in PP2Griffiths3
(`griffithsSecond_of_integrable`) for every even w ≥ 0 and J ≥ 0, via the duplicate-variable
rotation below. -/
def GriffithsSecond (w : ι → ℝ → ℝ) (J : ι → ι → ℝ) : Prop :=
  ∀ a b : ι → ℕ,
    (∫ φ : ι → ℝ, (∏ x, φ x ^ a x) * (∏ x, φ x ^ b x) * ferroDensity w J φ)
        * (∫ φ : ι → ℝ, ferroDensity w J φ)
      ≥ (∫ φ : ι → ℝ, (∏ x, φ x ^ a x) * ferroDensity w J φ)
        * (∫ φ : ι → ℝ, (∏ x, φ x ^ b x) * ferroDensity w J φ)
```

## #mwwgf21w-6ermq6  (Q_PP2Griffiths3A.lean)

```lean
/-- The Gibbs measure of the quartic box model: density dweight / Z against Lebesgue. -/
def gibbs (n k : ℕ) (m₀ lam : ℝ) : Measure (DField n k) :=
  volume.withDensity fun φ => ENNReal.ofReal (dweight n k m₀ lam (Polynomial.X ^ 4) φ /
    ∫ ψ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) ψ)

/-- The per-site involutions of ℝ × ℝ: in the coordinates (u, v) = (t + s, t − s), `act e f`
flips the sign of u iff e and of v iff f. Concretely: id, (t,s) ↦ (s,t), (t,s) ↦ (−t,−s),
(t,s) ↦ (−s,−t). -/
def act : Bool → Bool → ℝ × ℝ → ℝ × ℝ
  | false, false, p => p
  | false, true, p => (p.2, p.1)
  | true, true, p => (-p.1, -p.2)
  | true, false, p => (-p.2, -p.1)

/-- The sign-flip group of the doubled system, indexed by σ : ι ⊕ ι → Bool
(σ (inl x) flips u_x, σ (inr x) flips v_x). -/
def actPi (σ : ι ⊕ ι → Bool) (p : ι → ℝ × ℝ) : ι → ℝ × ℝ :=
  fun x => act (σ (Sum.inl x)) (σ (Sum.inr x)) (p x)

/-- `actPi σ` as a measurable equivalence. -/
def actEquiv (σ : ι ⊕ ι → Bool) : (ι → ℝ × ℝ) ≃ᵐ (ι → ℝ × ℝ) :=
  MeasurableEquiv.ofInvolutive (actPi σ)
    (fun p => funext fun x => act_involutive _ _ (p x)) (measurePreserving_actPi σ).measurable

/-- The (u, v) = (t + s, t − s) coordinates of a doubled configuration. -/
def uv (p : ι → ℝ × ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim (fun x => (p x).1 + (p x).2) (fun x => (p x).1 - (p x).2)

/-- t = (u + v)/2. -/
def tPart (ψ : ι ⊕ ι → ℝ) : ι → ℝ := fun x => (ψ (Sum.inl x) + ψ (Sum.inr x)) / 2

/-- s = (u − v)/2. -/
def sPart (ψ : ι ⊕ ι → ℝ) : ι → ℝ := fun x => (ψ (Sum.inl x) - ψ (Sum.inr x)) / 2

/-- The first copy t of a doubled configuration. -/
def fstF (p : ι → ℝ × ℝ) : ι → ℝ := fun x => (p x).1

/-- The second copy s of a doubled configuration. -/
def sndF (p : ι → ℝ × ℝ) : ι → ℝ := fun x => (p x).2

/-- f is "pair-positive": f(t) + f(s) and f(t) − f(s) are both polynomials with nonnegative
coefficients in (u, v) = (t + s, t − s). -/
def PairPos (f : (ι → ℝ) → ℝ) : Prop :=
  IsPosPoly (fun ψ : ι ⊕ ι → ℝ => f (tPart ψ) + f (sPart ψ)) ∧
    IsPosPoly (fun ψ : ι ⊕ ι → ℝ => f (tPart ψ) - f (sPart ψ))

/-- The cone 𝒞 = {g · exp Q : g, Q polynomials with nonnegative coefficients}. -/
def InCone (A : (ι → ℝ) → ℝ) : Prop :=
  ∃ g Q : (ι → ℝ) → ℝ, IsPosPoly g ∧ IsPosPoly Q ∧ ∀ φ, A φ = g φ * Real.exp (Q φ)

/-- The doubled integrand (A(t) − A(s))(B(t) − B(s)) e^{Q(t) + Q(s)}. -/
def dupIntegrand (A B Q : (ι → ℝ) → ℝ) (p : ι → ℝ × ℝ) : ℝ :=
  (A (fstF p) - A (sndF p)) * (B (fstF p) - B (sndF p)) * Real.exp (Q (fstF p) + Q (sndF p))

/-- The same in (u, v) coordinates. -/
def dupG (A B Q : (ι → ℝ) → ℝ) (ψ : ι ⊕ ι → ℝ) : ℝ :=
  (A (tPart ψ) - A (sPart ψ)) * (B (tPart ψ) - B (sPart ψ))
    * Real.exp (Q (tPart ψ) + Q (sPart ψ))
```

## #mwwgf25i-d0aeg1  (Q_PP2Griffiths3B.lean)

```lean
/-- The doubled product weight ∏_x w_x(t_x) w_x(s_x). -/
def dupWeight (w : ι → ℝ → ℝ) (p : ι → ℝ × ℝ) : ℝ := ∏ x, (w x (p x).1 * w x (p x).2)

/-- Ginibre's one-site condition: ∫∫ (t^a ± s^a)(t^b ± s^b) w(t) w(s) ≥ 0 for all a, b and
all four sign choices (`sgnMul true y = −y`). -/
def GinibreSite (w : ℝ → ℝ) : Prop :=
  ∀ (a b : ℕ) (e f : Bool), 0 ≤ ∫ q : ℝ × ℝ,
    (q.1 ^ a + sgnMul e (q.2 ^ a)) * (q.1 ^ b + sgnMul f (q.2 ^ b)) * (w q.1 * w q.2)
```

## #mwwgf298-3yk4ub  (Q_PP2SimonLiebA.lean)

```lean
/-- The quartic Dirichlet weight (`dweight` with P = X⁴). -/
abbrev qweight (n k : ℕ) (m₀ lam : ℝ) : DField n k → ℝ :=
  dweight n k m₀ lam (Polynomial.X ^ 4)

/-- The normalised two-point function ⟨φ_x φ_y⟩ of the quartic Dirichlet-box measure. -/
def twoPt (n k : ℕ) (m₀ lam : ℝ) (x y : DSite n k) : ℝ :=
  (∫ φ : DField n k, φ x * φ y * qweight n k m₀ lam φ) / ∫ φ : DField n k, qweight n k m₀ lam φ

/-- Extension by zero of a field on a region B. -/
def zeroExt (B : Finset (DSite n k)) (ψ : {x // x ∈ B} → ℝ) : DField n k :=
  fun x => if h : x ∈ B then ψ ⟨x, h⟩ else 0

/-- Extension by zero of a field on the complement of B. -/
def zeroExtC (B : Finset (DSite n k)) (η : {x // x ∉ B} → ℝ) : DField n k :=
  fun x => if h : x ∈ B then 0 else η ⟨x, h⟩

/-- The two-point function of the region B with Dirichlet (zero) boundary values on its
complement: the measure on fields supported in B, with the same action and Wick polynomial. -/
def regionTwoPt (n k : ℕ) (m₀ lam : ℝ) (B : Finset (DSite n k)) (x y : DSite n k) : ℝ :=
  (∫ ψ : {z // z ∈ B} → ℝ, zeroExt B ψ x * zeroExt B ψ y * qweight n k m₀ lam (zeroExt B ψ)) /
    ∫ ψ : {z // z ∈ B} → ℝ, qweight n k m₀ lam (zeroExt B ψ)

/-- The coupling of the bond {u, v} in −½ dirAction: J_uv = −ε² dirOp u v (u ≠ v); it is 1 for
nearest neighbours and 0 otherwise. -/
def bondJ (n k : ℕ) (u v : DSite n k) : ℝ := -(spacing n ^ 2 * dirOp n k 0 u v)

/-- **The Simon–Lieb inequality** (Lieb–Rivasseau form, BFS CMP 83 Theorem 6.1 with F = φ_y)
for the quartic Dirichlet-box model at (m₀, λ). -/
def SimonLiebIneq (m₀ lam : ℝ) : Prop :=
  ∀ (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k), x ∈ B → y ∉ B →
    twoPt n k m₀ lam x y ≤
      ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * regionTwoPt n k m₀ lam B x u * twoPt n k m₀ lam v y

/-- The target of node M3. -/
def SimonLiebTarget : Prop :=
  ∀ m₀ lam : ℝ, m₀ ≠ 0 → 0 ≤ lam → SimonLiebIneq m₀ lam

/-- The field restricted to B (zero outside). -/
def restrictIn (B : Finset (DSite n k)) (φ : DField n k) : DField n k :=
  fun x => if x ∈ B then φ x else 0

/-- The field restricted to the complement of B (zero on B). -/
def restrictOut (B : Finset (DSite n k)) (φ : DField n k) : DField n k :=
  fun x => if x ∈ B then 0 else φ x

/-- The boundary coupling Σ_{u ∈ B, v ∉ B} J_uv φ_u φ_v. -/
def bdryCoupling (B : Finset (DSite n k)) (φ : DField n k) : ℝ :=
  ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * φ u * φ v

/-- The decoupled weight: the box weight with the couplings across ∂B removed (up to a
constant), i.e. the product of the B-weight and the Bᶜ-weight. -/
def decWeight (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (B : Finset (DSite n k))
    (φ : DField n k) : ℝ :=
  dweight n k m₀ lam P (restrictIn B φ) * dweight n k m₀ lam P (restrictOut B φ)
```

## #mwwgf2cx-iollxj  (Q_PP2SimonLiebB.lean)

```lean
/-- The sites within physical sup-norm distance l of x. -/
def physBall (n k : ℕ) (x : DSite n k) (l : ℝ) : Finset (DSite n k) :=
  Finset.univ.filter fun u => supDist (dpos n k x) (dpos n k u) ≤ l

/-- **Input from node M5** (BFS (7.4)): the Simon–Lieb boundary sum of the ball of radius l is at
most γ, uniformly in the level, the volume and the centre. -/
def SmallBoundarySum (m₀ lam l γ : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k),
    ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
      bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u ≤ γ

/-- **Input from node M2:** Griffiths I for the region measures. -/
def RegionGriffithsI (m₀ lam : ℝ) : Prop :=
  ∀ (n k : ℕ) (B : Finset (DSite n k)) (x u : DSite n k), 0 ≤ regionTwoPt n k m₀ lam B x u

/-- **A further input** (not stated as a separate hypothesis in the passages of BFS we read;
UNPROVEN here and not a consequence of `SmallBoundarySum`): the two-point function is bounded at physical
distance ≥ 1, uniformly in the level and the volume. -/
def UniformBaseBound (m₀ lam K : ℝ) : Prop :=
  ∀ (n k : ℕ) (x y : DSite n k), 1 ≤ supDist (dpos n k x) (dpos n k y) →
    twoPt n k m₀ lam x y ≤ K

/-- The conclusion: hypothesis hG of `conditional_clustering`, with G = twoPt. -/
def UniformTwoPointDecay (m₀ lam C₀ m : ℝ) : Prop :=
  ∀ (n k : ℕ) (x y : DSite n k), 1 ≤ supDist (dpos n k x) (dpos n k y) →
    twoPt n k m₀ lam x y ≤ C₀ * Real.exp (-m * supDist (dpos n k x) (dpos n k y))

/-- **The M6 consumer**, as a proposition (proved below as `m6Consumer`). -/
def M6Consumer : Prop :=
  ∀ m₀ lam l γ K : ℝ, 0 ≤ l → 0 < γ → γ < 1 → 0 ≤ K →
    SimonLiebIneq m₀ lam → RegionGriffithsI m₀ lam → SmallBoundarySum m₀ lam l γ →
      UniformBaseBound m₀ lam K →
        ∃ C₀ m : ℝ, 0 ≤ C₀ ∧ 0 < m ∧ UniformTwoPointDecay m₀ lam C₀ m
```

## #mwwjei2d-eyc3we  (Q_PP2SimonLieb2A.lean)

```lean
/-- The single-site exponent f(u) = a u + b u². -/
def fq (a b u : ℝ) : ℝ := a * u + b * u ^ 2

/-- Its derivative f'(u) = a + 2 b u. -/
def fq' (a b u : ℝ) : ℝ := a + 2 * b * u

/-- The local-time weight W_τ(φ) = ∏_x e^{−f(φ_x²/2 + τ_x)}. -/
def tw (a b : ℝ) (τ φ : ι → ℝ) : ℝ := Real.exp (-∑ x, fq a b (φ x ^ 2 / 2 + τ x))

/-- The Fubini integrand F(φ, s) = R(φ) φ_i f'(φ_i²/2 + τ_i + s) W_{τ+s e_i}(φ). -/
def ltF (a b : ℝ) (τ : ι → ℝ) (i : ι) (R : (ι → ℝ) → ℝ) (φ : ι → ℝ) (s : ℝ) : ℝ :=
  R φ * φ i * fq' a b (φ i ^ 2 / 2 + τ i + s) * tw a b (τ + Pi.single i s) φ

/-- Its dominating function in φ (times C e^{−cs} in s). -/
def ltG (a b : ℝ) (τ : ι → ℝ) (i : ι) (R : (ι → ℝ) → ℝ) (φ : ι → ℝ) : ℝ :=
  (|a| + 2 * b * τ i + 1) * |φ i * R φ * tw a b τ φ| + b * |φ i ^ 3 * R φ * tw a b τ φ|
```

## #mwwjell7-x5zijt  (Q_PP2SimonLieb2B.lean)

```lean
/-- The pair exponent Q_K(φ) = Σ_{x,y} K_xy φ_x φ_y. -/
def quadE (K : ι → ι → ℝ) (φ : ι → ℝ) : ℝ := ∑ x, ∑ y, K x y * φ x * φ y

/-- α = 4 + ε² m₀² − 12 λ ε² c (c = freeVar): the coefficient of s = φ²/2 in the site exponent
(Dirichlet diagonal 4, mass, and the Wick counterterm −6λε²c φ²). -/
def alphaQ (n : ℕ) (m₀ lam : ℝ) : ℝ :=
  4 + spacing n ^ 2 * m₀ ^ 2 - 12 * lam * spacing n ^ 2 * freeVar n m₀

/-- β = 4 λ ε²: the coefficient of s² (λε² φ⁴ = 4λε² s²). -/
def betaQ (n : ℕ) (lam : ℝ) : ℝ := 4 * lam * spacing n ^ 2

/-- The symmetrised nearest-neighbour coupling J_ij = Jnn_ij + Jnn_ji (= ∂_i of the pair
exponent; 1 for nearest neighbours, 0 on the diagonal). -/
def Jsym (n k : ℕ) (x y : DSite n k) : ℝ := Jnn n k x y + Jnn n k y x
```

## #mwwjelp3-6q5091  (Q_PP2SimonLieb2C.lean)

```lean
/-- The unnormalised τ-shifted expectation [G]_τ = ∫ G · e^{Σ Jnn φφ} · ∏_x e^{−f(φ_x²/2+τ_x)}
(BFS's [·]_t, with g(S²) = e^{−f(S²/2)} and their g(S² + 2t) = e^{−f(S²/2 + t)}). -/
def tauInt (n k : ℕ) (m₀ lam : ℝ) (τ : DField n k) (G : DField n k → ℝ) : ℝ :=
  ∫ φ, G φ * Real.exp (quadE (Jnn n k) φ) * tw (alphaQ n m₀ lam) (betaQ n lam) τ φ
```

## #mwwjeltf-5gofiu  (Q_PP2SimonLieb3A.lean)

```lean
/-- The product density ρ = e^Q ∏_x w_x. -/
def rhoQ (w : ι → ℝ → ℝ) (Q : (ι → ℝ) → ℝ) (φ : ι → ℝ) : ℝ :=
  Real.exp (Q φ) * ∏ x, w x (φ x)

/-- The site-mass increment V(φ) = Σ_x γ_x φ_x². -/
def massV (γ : ι → ℝ) (φ : ι → ℝ) : ℝ := ∑ x, γ x * φ x ^ 2
```

## #mwwjely3-bw5ruq  (Q_PP2SimonLieb3B.lean)

```lean
/-- [F]_τ = ∫ F e^{Q_K} W_τ, W_τ = ∏_x e^{−f(φ_x²/2 + τ_x)}, f(u) = au + bu² (unnormalised).
For the quartic box, `tauInt n k m₀ λ = tI (Jnn n k) (alphaQ n m₀ λ) (betaQ n λ)` (rfl). -/
def tI (K : ι → ι → ℝ) (a b : ℝ) (τ : ι → ℝ) (F : (ι → ℝ) → ℝ) : ℝ :=
  ∫ φ, F φ * Real.exp (quadE K φ) * tw a b τ φ

/-- The single-site weight at local time τ_x. -/
def siteW (a b : ℝ) (τ : ι → ℝ) (x : ι) (y : ℝ) : ℝ := Real.exp (-fq a b (y ^ 2 / 2 + τ x))

/-- Admissible observables: continuous, |H| ≤ C e^{a' Σ|φ_x|} Ψ for an envelope Ψ ≥ 1 (Ψ = 1 for
polynomial observables; Ψ = 1 + e^{boundary coupling} for the decoupled measure of R5). -/
def Adm (Ψ : (ι → ℝ) → ℝ) (H : (ι → ℝ) → ℝ) : Prop :=
  Continuous H ∧ ∃ C a' : ℝ, ∀ φ, |H φ| ≤ C * Real.exp (a' * ∑ x, |φ x|) * Ψ φ

/-- D_i(τ) = Σ_j c_j [φ_i φ_j]_τ − [φ_i G]_τ. -/
def sgdD (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (cc : ι → ℝ) (i : ι) (τ : ι → ℝ) : ℝ :=
  ∑ j, cc j * tI K a b τ (fun φ => φ i * φ j) - tI K a b τ (fun φ => φ i * G φ)

/-- The local-time integrand of D_i(τ) given by R2 (σ = τ + s e_i). -/
def sgdE (K : ι → ι → ℝ) (a b : ℝ) (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ) (cc : ι → ℝ)
    (i : ι) (τ : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j, cc j * (tI K a b (τ + Pi.single i s) (fun _ => (Pi.single i (1 : ℝ) : ι → ℝ) j) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * φ j)) -
    (tI K a b (τ + Pi.single i s) (G' i) +
      ∑ k, (K i k + K k i) * tI K a b (τ + Pi.single i s) (fun φ => φ k * G φ))
```

## #mwwjem7m-lg69pp  (Q_PP2M6Smeared.lean)

```lean
/-- **Simon–Lieb with the local term** (any y; for y ∉ B the local term vanishes). -/
def SimonLiebIneq' (m₀ lam : ℝ) : Prop :=
  ∀ (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k), x ∈ B →
    twoPt n k m₀ lam x y ≤ regionTwoPt n k m₀ lam B x y +
      ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * regionTwoPt n k m₀ lam B x u * twoPt n k m₀ lam v y

/-- **Region susceptibility:** the smeared two-point function of the Dirichlet ball of radius l is
bounded uniformly in the level, the volume and the centre. -/
def RegionSusceptibility (m₀ lam l A : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k),
    spacing n ^ 2 * ∑ y, regionTwoPt n k m₀ lam (physBall n k x l) x y ≤ A

/-- **Uniform smeared decay** of the two-point function. -/
def UniformSmearedDecay (m₀ lam C₀ m : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k) (w : DSite n k → ℝ) (D : ℝ),
    (∀ y, 0 ≤ w y ∧ w y ≤ 1) → (∀ y, w y ≠ 0 → D ≤ supDist (dpos n k x) (dpos n k y)) →
      spacing n ^ 2 * ∑ y, w y * twoPt n k m₀ lam x y ≤ C₀ * Real.exp (-m * D)

/-- **The smeared M6 consumer**, as a proposition (proved below as `m6Consumer'`). -/
def M6Consumer' : Prop :=
  ∀ m₀ lam l γ A : ℝ, 0 ≤ l → 0 < γ → γ < 1 → 0 ≤ A →
    SimonLiebIneq' m₀ lam → RegionGriffithsI m₀ lam → SmallBoundarySum m₀ lam l γ →
      RegionSusceptibility m₀ lam l A →
        ∃ C₀ m : ℝ, 0 ≤ C₀ ∧ 0 < m ∧ UniformSmearedDecay m₀ lam C₀ m

/-- The smeared two-point function S_w(x) = ε² Σ_y w_y ⟨φ_x φ_y⟩. -/
def smeared (n k : ℕ) (m₀ lam : ℝ) (w : DSite n k → ℝ) (x : DSite n k) : ℝ :=
  spacing n ^ 2 * ∑ y, w y * twoPt n k m₀ lam x y

/-- The Simon–Lieb exit kernel of the ball of radius l around x. -/
def exitW (n k : ℕ) (m₀ lam l : ℝ) (x v : DSite n k) : ℝ :=
  if v ∈ (physBall n k x l)ᶜ then
    ∑ u ∈ physBall n k x l, bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u
  else 0
```

## #mwwjemd1-h6ei0m  (Q_PP2SimonLieb4A.lean)

```lean
/-- The pair matrix of the decoupled measure: Jnn with the couplings across ∂B removed. -/
def decJ (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k) : ℝ :=
  if (x ∈ B ↔ y ∈ B) then Jnn n k x y else 0

/-- The boundary matrix: bondJ u v for u ∈ B, v ∉ B, and 0 otherwise. -/
def bdryK (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k) : ℝ :=
  if x ∈ B ∧ y ∉ B then bondJ n k x y else 0

/-- The flip pattern: true (flip) exactly off B. -/
def flipσ (B : Finset (DSite n k)) : DSite n k → Bool := fun z => decide (z ∉ B)

/-- φ with its sign flipped on Bᶜ. -/
def flipB (B : Finset (DSite n k)) (φ : DField n k) : DField n k := flipSigns (flipσ B) φ
```

## #mwwjemhq-4jn93r  (Q_PP2SimonLieb4B.lean)

```lean
/-- G = φ_y e^{bdryCoupling}. -/
def slG (B : Finset (DSite n k)) (y : DSite n k) (φ : DField n k) : ℝ :=
  φ y * Real.exp (bdryCoupling B φ)

/-- ∂_j G = (δ_jy + φ_y Σ_v (bdryK_jv + bdryK_vj) φ_v) e^{bdryCoupling}. -/
def slG' (B : Finset (DSite n k)) (y j : DSite n k) (φ : DField n k) : ℝ :=
  ((Pi.single j (1 : ℝ) : DField n k) y +
    φ y * ∑ v, (bdryK n k B j v + bdryK n k B v j) * φ v) * Real.exp (bdryCoupling B φ)
```

## #mwwjemmj-gpcqa0  (Q_PP2FKG.lean)

```lean
/-- The (continuous) four functions property of a measure on a lattice. -/
def FourFunctions {X : Type*} [MeasurableSpace X] [Lattice X] (μ : Measure X) : Prop :=
  ∀ f₁ f₂ f₃ f₄ : X → ℝ≥0∞, Measurable f₁ → Measurable f₂ → Measurable f₃ → Measurable f₄ →
    (∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)) →
    (∫⁻ x, f₁ x ∂μ) * (∫⁻ x, f₂ x ∂μ) ≤ (∫⁻ x, f₃ x ∂μ) * (∫⁻ x, f₄ x ∂μ)
```

## #mwwlpy8x-czn52a  (Q_PP2NewmanA.lean)

```lean
/-- FKG for bounded measurable monotone observables. -/
def BoundedFKG : Prop :=
  ∀ F G : X → ℝ, Measurable F → Measurable G → ∀ CF CG : ℝ, (∀ x, |F x| ≤ CF) →
    (∀ x, |G x| ≤ CG) → Monotone F → Monotone G →
      (∫ x, F x ∂μ) * (∫ x, G x ∂μ) ≤ ∫ x, F x * G x ∂μ

/-- Truncation at level N. -/
def trunc (N : ℕ) (t : ℝ) : ℝ := max (-(N : ℝ)) (min t N)

/-- The covariance ∫ F H − ∫ F ∫ H. -/
def cov (F H : X → ℝ) : ℝ := (∫ x, F x * H x ∂μ) - (∫ x, F x ∂μ) * ∫ x, H x ∂μ

/-- A linear functional of the field. -/
def lin (a : DSite n k → ℝ) (φ : DField n k) : ℝ := ∑ x, a x * φ x
```

## #mwwlpzs6-scsdxq  (Q_PP2Limit.lean)

```lean
/-- The sup of the Schwartz seminorms ‖·‖_{i,j} over (i, j) ≤ (a, b). -/
def schwartzSup (a b : ℕ) : Seminorm ℝ TestFn :=
  (Finset.Iic (a, b)).sup (schwartzSeminormFamily ℝ Plane ℝ)

/-- Uniform (in n, k) Lipschitz continuity of ZD for one finite Schwartz seminorm. -/
def UniformEquicont (m₀ lam : ℝ) : Prop :=
  ∃ (C : ℝ) (a b : ℕ), ∀ (n k : ℕ) (f g : TestFn),
    ‖ZD n k m₀ lam (Polynomial.X ^ 4) f - ZD n k m₀ lam (Polynomial.X ^ 4) g‖
      ≤ C * schwartzSup a b (f - g)

/-- Separability of the Schwartz space for each finite seminorm (true; not in Mathlib). -/
def SchwartzSeparable : Prop :=
  ∀ a b : ℕ, ∃ D : Set TestFn, D.Countable ∧
    ∀ f : TestFn, ∀ ε > 0, ∃ d ∈ D, schwartzSup a b (f - d) < ε
```

## #mwwlpzww-uqd11t  (Q_PP2Limit2A.lean)

```lean
/-- The second moment ⟨φ(h)²⟩ of the smeared field. -/
def sqMoment (n k : ℕ) (m₀ lam : ℝ) (h : TestFn) : ℝ :=
  (∫ φ : DField n k, dsmear n k h φ ^ 2 * dweight n k m₀ lam (Polynomial.X ^ 4) φ) /
    ∫ φ : DField n k, dweight n k m₀ lam (Polynomial.X ^ 4) φ

/-- **Uniform susceptibility**: sup_x ε² Σ_y |⟨φ_x φ_y⟩| ≤ K, uniformly in n, k. -/
def UniformSusceptibility (m₀ lam K : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k), spacing n ^ 2 * ∑ y, |twoPt n k m₀ lam x y| ≤ K
```

## #mwwlq07a-c2sp8h  (Q_PP2Assembly.lean)

```lean
/-- The extension of a sign pattern on B to the whole box (no flip off B). -/
def asm_extσ (B : Finset (DSite n k)) (σ : {z // z ∈ B} → Bool) : DSite n k → Bool :=
  fun z => if h : z ∈ B then σ ⟨z, h⟩ else false

/-- The two node-M5 inputs at (m₀, λ), with some radius l, contraction γ < 1 and bound A. -/
def M5Inputs (m₀ lam : ℝ) : Prop :=
  ∃ l γ A : ℝ, 0 ≤ l ∧ 0 < γ ∧ γ < 1 ∧ 0 ≤ A ∧
    SmallBoundarySum m₀ lam l γ ∧ RegionSusceptibility m₀ lam l A
```

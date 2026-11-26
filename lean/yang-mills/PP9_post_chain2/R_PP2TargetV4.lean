import LongTable.P_mww4cze7_bk8bxu

/-!
Posted copy of congress-lean lean/yang-mills/PP6_target_v4/PP2TargetV4.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction. The TARGET, fourth version.
Definitions only, plus small lemmas proved by `rfl` or direct computation. Builds on the third
version (#mww4cze7-bk8bxu: `DSite`, `dirAction`, `freeVar`, `ZD`, `FiniteCutoffClustering`,
`IsLimitPoint`) and the first (#mwvi84dh-hnd872: `TestFn`, `translate`, `IsNonGaussian`).

Three upgrades against the third version: (1) a Hamiltonian clause, stated through
Osterwalder–Schrader reconstruction data tied to the limit generating functional; (2) the same
target for the two-component O(2) model; (3) a stage-two target for φ⁴₃ (definitions only).

STATEMENT CARD.
(1) Hamiltonian form. Coordinate 0 of the plane is time.
* `reflect f` = Θf, (Θf)(x₀, x₁) = f(−x₀, x₁) (`reflect_apply`, proved by `rfl`).
* `timeShift t` = (t, 0); `translate (timeShift t) g` = g(· − (t, 0)) moves g forward by t.
* `PositiveTime f`: f(x) ≠ 0 → 0 < x₀.
* `HamiltonianGap Z m`: there are a complex Hilbert space H, a unit vector Ω, operators T(t),
  t ≥ 0, and a map ψ from test functions to H, such that: T(t) is self-adjoint, T(0) = 1,
  T(s + t) = T(s)T(t), T(t)Ω = Ω, ψ(0) = Ω; for positive-time f, g and t ≥ 0,
  ⟪ψ f, T(t) ψ g⟫ = Z(τ_(t,0) g − Θf); the span of ψ(f), f positive-time with compact support,
  is dense; and ‖T(t)u‖ ≤ e^(−mt)‖u‖ for every t ≥ 0 and u ⊥ Ω.
  Reading: ψ f is the class of e^(iφ(f)) in the OS Hilbert space, T(t) = e^(−tH). The inner
  product of Mathlib is conjugate-linear in the first slot; the OS form is
  ⟪A, B⟫ = E[conj(ΘA)·B], and for A = e^(iφ(f)), B = e^(iφ(τ g)) this is
  E[e^(−iφ(Θf)) e^(iφ(τ g))] = Z(τ g − Θf), since Θ e^(iφ(f)) = e^(iφ(Θf)) for real f.
  ψ(0) = e^0 = 1 is the vacuum, and 0 is (vacuously) positive-time. Polarisation and density
  determine (H, Ω, T, ψ) up to unitary equivalence, so the clause does not depend on the choice
  of data; the last item says σ(H) ⊆ {0} ∪ [m, ∞) with Ω spanning ker H. Existence of such data
  is the content of reflection positivity + OS reconstruction for Z. Taking f = 0, ψ 0 = Ω = T(t)Ω
  and self-adjointness give Z(τ_(t,0) g) = Z(g) for positive-time g and t ≥ 0: the clause also
  asserts time-translation invariance of Z on positive-time functions (true for a genuine limit,
  but part of the target's content). The box (sites 0..N−1, time 0 at i = N/2) is not exactly
  Θ-symmetric; that matters only for finite-volume reflection positivity, not for the limit.
  T(0) = 1 is ADDED to the council's draft: without it T(0) may be a projection, the t = 0
  formula only fixes ⟪T(0)ψ f, T(0)ψ g⟫, and H would not be determined by Z.
  The statement is the generic `OSGap` (any test space, reflection, shift and predicates),
  specialised to the scalar and the two-component case.
(2) O(2) model on the same Dirichlet box.
* `DField2 n k` = DSite n k → ℝ²; `comp φ a` its a-th component.
* `dirAction2` = Σ_a dirAction(φ_a).
* `wickQuartic2 c s` = s² − 8cs + 8c²: the Wick square :(φ·φ)²:_c for N = 2 components of
  variance c each (general N: (φ·φ)² − 2(N+2)c(φ·φ) + N(N+2)c²; its mean is 0 under the
  infinite-lattice site variance c = freeVar, not exactly 0 under the Dirichlet-box marginals,
  which have smaller variance; the scalar model has the same feature).
* `dweight2` = exp(−½ dirAction2 − λ ε² Σ_x :(φ(x)·φ(x))²:_c) with c = `freeVar n m₀`.
* `TestFn2` = Fin 2 → TestFn; `dsmear2 f φ` = Σ_a ε² Σ_x f_a(dpos x) φ_a(x); `ZD2` the
  generating functional; `translate2`, `reflect2` componentwise; `FiniteCutoffClustering2`,
  `IsLimitPoint2`, `ClustersAt2`, `IsNonGaussian2`, `HamiltonianGap2` mirror the scalar ones.
  PROVED: `limitPoint_clusters2`.
(3) `PhiFourTwoGapV4`: ∀ m₀ > 0, ∃ λ₀ > 0, ∀ λ ∈ (0, λ₀), ∃ m > 0 with, for the scalar model,
  `FiniteCutoffClustering m₀ λ m`, a limit point, and every limit point non-Gaussian with
  `HamiltonianGap Z m`; and the same, with the same m, for the O(2) model.
(4) Stage two, φ⁴₃ (definitions only; no Hamiltonian clause at this stage).
* Box: sites Fin N³, N = 2^(n+k), spacing ε = 2^(−n), side L = 2^k, position
  (εi − L/2, εj − L/2, εl − L/2) in EuclideanSpace ℝ (Fin 3); Dirichlet extension `ext3`.
* `dirAction3` = ε³ [Σ_bonds ((φ(x+e) − φ(x))/ε)² + Σ_x m₀² φ(x)²], three bond directions.
* Normalisation. In d dimensions the free weight is exp(−½ φᵀAφ) with
  A = ε^d(−Δ_ε + m₀²) = ε^(d−2)(−Δ₁ + m₀²ε²), Δ₁ the unit-spacing Laplacian. So the covariance
  is A⁻¹ = ε^(2−d)(−Δ₁ + m₀²ε²)⁻¹, and on the infinite lattice
  G(0, x) = ε^(2−d) (2π)^(−d) ∫_[−π,π]^d cos(θ·x) dθ / (m₀²ε² + Σ_i 4 sin²(θ_i/2)).
  For d = 2 this is ε⁰ (agrees with `freeVar`); for d = 3 the prefactor is ε^(−1).
  This G is also the kernel of (−Δ_ε + m₀²)⁻¹ for the pairing ε^d Σ_x, the normalisation of
  Bauerschmidt–Dagallier (arXiv:2202.02295).
* `latticeG3 n m₀ x` = G(0, x) above, x ∈ ℤ³ (d = 3).
* `massCT3` = a^ε(λ) = −3λ G(0, 0) + 6λ² ‖G(0, ·)‖³_(L³), ‖g‖³_(L³) = ε³ Σ'_(x ∈ ℤ³) |g(x)|³:
  their counterterm display (§1, equation e:counterterm1 of the LaTeX source, read by the council
  through the site), with their IR mass m² taken equal to m₀² (another choice shifts a by a finite,
  ε-independent amount at leading order).
* `dweight3` = exp(−½ dirAction3 − ε³ Σ_x [(λ/4) φ(x)⁴ + ½ a^ε(λ) φ(x)²]). Not Wick-ordered.
  The quartic term is (λ/4)φ⁴, as in their measure (§1), NOT λφ⁴ as in the council's draft: the
  counterterm −3λG(0,0) is the Wick subtraction for (λ/4)φ⁴ ((λ/4)(φ⁴ − 6Gφ²)), and would be
  wrong by a factor 4 against λφ⁴. (Our m₀² plays their μ, with the counterterm at m² = m₀².)
* `ZD3`, `translate3`, `FiniteCutoffClustering3` (distance max(|a₀|, |a₁|, |a₂|)),
  `IsLimitPoint3`, `IsNonGaussian3`.
* `PhiFourThreeGap`: ∀ m₀ > 0, ∃ λ₀ > 0, ∀ λ ∈ (0, λ₀), ∃ m > 0 with finite-cutoff clustering
  at rate m, a limit point, and every limit point non-Gaussian.

Junk values. Each `ZD*` divides by the integral of its weight: that integral is finite and
positive for λ > 0 (the quartic term dominates; in d = 3 also when a^ε < 0), so no division by
zero for the parameters the targets quantify over. The Fourier integrands are bounded and
continuous when m₀ > 0. The tsum in `massCT3` is summable for m₀ > 0 (G decays exponentially);
were it not summable, Lean's tsum would be 0. For λ ≤ 0 the weights need not be integrable and
`ZD*` may be a junk value; the targets only use λ > 0.

NOT here: proofs of the targets; the quantitative rate; full translation and rotation
invariance of limit points; the Hamiltonian clause for φ⁴₃; the O(2) model in d = 3.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Filter Topology Real
open scoped InnerProductSpace

noncomputable section

namespace PP2Target

/-! ## (1) Hamiltonian form -/

/-- The linear map (x₀, x₁) ↦ (−x₀, x₁) of the plane. -/
def timeReflLin : Plane →ₗ[ℝ] Plane where
  toFun v := !₂[-(v 0), v 1]
  map_add' v w := by ext i; fin_cases i <;> simp; ring
  map_smul' c v := by ext i; fin_cases i <;> simp

theorem timeReflLin_involutive : Function.Involutive timeReflLin := fun v => by
  ext i; fin_cases i <;> simp [timeReflLin]

/-- Time reflection (x₀, x₁) ↦ (−x₀, x₁) as a continuous linear equivalence. -/
def timeRefl : Plane ≃L[ℝ] Plane :=
  (LinearEquiv.ofInvolutive timeReflLin timeReflLin_involutive).toContinuousLinearEquiv

/-- Time reflection of a test function: (Θf)(x₀, x₁) = f(−x₀, x₁). -/
def reflect : TestFn →L[ℝ] TestFn := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ timeRefl

theorem reflect_apply (f : TestFn) (x : Plane) : reflect f x = f !₂[-(x 0), x 1] := rfl

/-- The time shift vector (t, 0). -/
def timeShift (t : ℝ) : Plane := !₂[t, 0]

/-- f is supported at strictly positive times. -/
def PositiveTime (f : TestFn) : Prop := ∀ x : Plane, f x ≠ 0 → 0 < x 0

/-- Generic OS-reconstruction gap statement on a test space F, with a reflection, a time shift,
a positive-time predicate (for the matrix-element formula) and a predicate selecting the test
functions whose vectors must span a dense set. See the header, item (1). -/
def OSGap {F : Type} [AddCommGroup F] (Z : F → ℂ) (refl : F → F) (shift : ℝ → F → F)
    (posT dens : F → Prop) (m : ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (Ω : H) (T : ℝ → H →L[ℂ] H) (ψ : F → H),
    ‖Ω‖ = 1 ∧ (∀ t, 0 ≤ t → IsSelfAdjoint (T t)) ∧ T 0 = 1 ∧
    (∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) ∧
    (∀ t, 0 ≤ t → T t Ω = Ω) ∧ ψ 0 = Ω ∧
    (∀ f g, posT f → posT g → ∀ t, 0 ≤ t → ⟪ψ f, T t (ψ g)⟫_ℂ = Z (shift t g - refl f)) ∧
    Dense ((Submodule.span ℂ (ψ '' {f | dens f})) : Set H) ∧
    (∀ t, 0 ≤ t → ∀ u, ⟪Ω, u⟫_ℂ = 0 → ‖T t u‖ ≤ Real.exp (-m * t) * ‖u‖)

/-- The reconstructed Hamiltonian of Z has spectrum in {0} ∪ [m, ∞), Ω the only ground state. -/
def HamiltonianGap (Z : TestFn → ℂ) (m : ℝ) : Prop :=
  OSGap Z (fun f => reflect f) (fun t g => translate (timeShift t) g) PositiveTime
    (fun f => PositiveTime f ∧ HasCompactSupport ⇑f) m

/-! ## (2) The O(2) model -/

/-- Two-component fields on the Dirichlet box. -/
abbrev DField2 (n k : ℕ) := DSite n k → (Fin 2 → ℝ)

/-- The a-th component of a two-component field. -/
def comp {n k : ℕ} (φ : DField2 n k) (a : Fin 2) : DField n k := fun x => φ x a

/-- The free action: the sum of the scalar Dirichlet actions of the components. -/
def dirAction2 (n k : ℕ) (m₀ : ℝ) (φ : DField2 n k) : ℝ :=
  ∑ a : Fin 2, dirAction n k m₀ (comp φ a)

/-- :(φ·φ)²:_c = s² − 8cs + 8c² at s = φ·φ, for 2 components of variance c. -/
def wickQuartic2 (c s : ℝ) : ℝ := s ^ 2 - 8 * c * s + 8 * c ^ 2

/-- The O(2) lattice weight exp(−½ dirAction2 − λ ε² Σ_x :(φ(x)·φ(x))²:). -/
def dweight2 (n k : ℕ) (m₀ lam : ℝ) (φ : DField2 n k) : ℝ :=
  Real.exp (-(dirAction2 n k m₀ φ) / 2
    - lam * spacing n ^ 2 * ∑ x : DSite n k, wickQuartic2 (freeVar n m₀) (∑ a : Fin 2, φ x a ^ 2))

/-- Two-component test functions. -/
abbrev TestFn2 := Fin 2 → TestFn

/-- Σ_a ε² Σ_x f_a(dpos x) φ_a(x). -/
def dsmear2 (n k : ℕ) (f : TestFn2) (φ : DField2 n k) : ℝ :=
  ∑ a : Fin 2, dsmear n k (f a) (comp φ a)

/-- The generating functional of the O(2) Dirichlet-box measure. -/
def ZD2 (n k : ℕ) (m₀ lam : ℝ) (f : TestFn2) : ℂ :=
  (∫ φ : DField2 n k, Complex.exp (Complex.I * (dsmear2 n k f φ : ℂ)) * (dweight2 n k m₀ lam φ : ℂ)) /
    ((∫ φ : DField2 n k, dweight2 n k m₀ lam φ : ℝ) : ℂ)

/-- Componentwise translation. -/
def translate2 (a : Plane) (f : TestFn2) : TestFn2 := fun i => translate a (f i)

/-- Componentwise time reflection. -/
def reflect2 (f : TestFn2) : TestFn2 := fun i => reflect (f i)

/-- Every component is positive-time. -/
def PositiveTime2 (f : TestFn2) : Prop := ∀ i, PositiveTime (f i)

/-- Every component has compact support. -/
def CompactSupport2 (f : TestFn2) : Prop := ∀ i, HasCompactSupport ⇑(f i)

/-- Uniform clustering at finite cutoff at rate m, O(2) model. -/
def FiniteCutoffClustering2 (m₀ lam m : ℝ) : Prop :=
  ∀ f g : TestFn2, CompactSupport2 f → CompactSupport2 g →
    ∃ C : ℝ, ∀ (n k : ℕ) (a : Plane),
      ‖ZD2 n k m₀ lam (f + translate2 a g) - ZD2 n k m₀ lam f * ZD2 n k m₀ lam (translate2 a g)‖
        ≤ C * Real.exp (-m * max |a 0| |a 1|)

/-- Z is a limit point of the O(2) Dirichlet-box generating functionals. -/
def IsLimitPoint2 (m₀ lam : ℝ) (Z : TestFn2 → ℂ) : Prop :=
  ∃ ns ks : ℕ → ℕ, Tendsto ns atTop atTop ∧ Tendsto ks atTop atTop ∧
    ∀ f : TestFn2, Tendsto (fun j => ZD2 (ns j) (ks j) m₀ lam f) atTop (𝓝 (Z f))

/-- Clustering at rate m of a two-component generating functional. -/
def ClustersAt2 (Z : TestFn2 → ℂ) (m : ℝ) : Prop :=
  ∀ f g : TestFn2, CompactSupport2 f → CompactSupport2 g →
    ∃ C : ℝ, ∀ a : Plane,
      ‖Z (f + translate2 a g) - Z f * Z (translate2 a g)‖ ≤ C * Real.exp (-m * max |a 0| |a 1|)

/-- Z is not exp(iℓ(f) − ½B(f, f)) for linear ℓ and bilinear B on TestFn2. -/
def IsNonGaussian2 (Z : TestFn2 → ℂ) : Prop :=
  ¬ ∃ (ℓ : TestFn2 →ₗ[ℝ] ℝ) (B : TestFn2 →ₗ[ℝ] TestFn2 →ₗ[ℝ] ℝ),
      ∀ f, Z f = Complex.exp (Complex.I * (ℓ f : ℂ) - ((B f f : ℝ) : ℂ) / 2)

/-- The Hamiltonian gap for a two-component generating functional. -/
def HamiltonianGap2 (Z : TestFn2 → ℂ) (m : ℝ) : Prop :=
  OSGap Z reflect2 (fun t g => translate2 (timeShift t) g) PositiveTime2
    (fun f => PositiveTime2 f ∧ CompactSupport2 f) m

/-- Every O(2) limit point inherits the finite-cutoff clustering bound. -/
theorem limitPoint_clusters2 {m₀ lam m : ℝ} (h : FiniteCutoffClustering2 m₀ lam m)
    {Z : TestFn2 → ℂ} (hZ : IsLimitPoint2 m₀ lam Z) : ClustersAt2 Z m := by
  intro f g hf hg
  obtain ⟨C, hC⟩ := h f g hf hg
  obtain ⟨ns, ks, -, -, hconv⟩ := hZ
  refine ⟨C, fun a => ?_⟩
  have hlim : Tendsto (fun j =>
      ZD2 (ns j) (ks j) m₀ lam (f + translate2 a g)
        - ZD2 (ns j) (ks j) m₀ lam f * ZD2 (ns j) (ks j) m₀ lam (translate2 a g))
      atTop (𝓝 (Z (f + translate2 a g) - Z f * Z (translate2 a g))) :=
    (hconv _).sub ((hconv _).mul (hconv _))
  exact le_of_tendsto hlim.norm (Eventually.of_forall fun j => hC (ns j) (ks j) a)

/-! ## (3) Headline target, fourth version -/

/-- **Target, fourth version.** Scalar λ:φ⁴:₂ and O(2) λ:(φ·φ)²:₂ at weak coupling: uniform
finite-cutoff clustering, limit points exist, and every limit point is non-Gaussian and has a
Hamiltonian gap m. -/
def PhiFourTwoGapV4 : Prop :=
  ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ m : ℝ, 0 < m ∧
      (FiniteCutoffClustering m₀ lam m ∧ (∃ Z, IsLimitPoint m₀ lam Z) ∧
        ∀ Z, IsLimitPoint m₀ lam Z → IsNonGaussian Z ∧ HamiltonianGap Z m) ∧
      (FiniteCutoffClustering2 m₀ lam m ∧ (∃ Z, IsLimitPoint2 m₀ lam Z) ∧
        ∀ Z, IsLimitPoint2 m₀ lam Z → IsNonGaussian2 Z ∧ HamiltonianGap2 Z m)

/-! ## (4) Stage two: φ⁴₃ -/

/-- Points of three-dimensional space. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- Real Schwartz test functions on ℝ³. -/
abbrev TestFn3 := SchwartzMap Space3 ℝ

/-- Sites of the three-dimensional Dirichlet box, N = 2^(n+k) per side. -/
abbrev DSite3 (n k : ℕ) := Fin (boxN n k) × Fin (boxN n k) × Fin (boxN n k)

/-- Fields on the three-dimensional box. -/
abbrev DField3 (n k : ℕ) := DSite3 n k → ℝ

/-- The point (ε i − L/2, ε j − L/2, ε l − L/2) of ℝ³ at site (i, j, l). -/
def dpos3 (n k : ℕ) (x : DSite3 n k) : Space3 :=
  !₂[spacing n * ((x.1 : ℕ) : ℝ) - boxL k / 2, spacing n * ((x.2.1 : ℕ) : ℝ) - boxL k / 2,
    spacing n * ((x.2.2 : ℕ) : ℝ) - boxL k / 2]

/-- The field extended by zero outside the box. -/
def ext3 {n k : ℕ} (φ : DField3 n k) (p : ℤ × ℤ × ℤ) : ℝ :=
  if h : 0 ≤ p.1 ∧ p.1 < boxN n k ∧ 0 ≤ p.2.1 ∧ p.2.1 < boxN n k ∧ 0 ≤ p.2.2 ∧ p.2.2 < boxN n k then
    φ (⟨p.1.toNat, by omega⟩, ⟨p.2.1.toNat, by omega⟩, ⟨p.2.2.toNat, by omega⟩)
  else 0

/-- The three-dimensional lattice action with Dirichlet boundary values:
ε³ [Σ_bonds ((φ(x+e) − φ(x))/ε)² + Σ_x m₀² φ(x)²]. -/
def dirAction3 (n k : ℕ) (m₀ : ℝ) (φ : DField3 n k) : ℝ :=
  spacing n ^ 3 *
    ((∑ p ∈ Finset.Icc (-1 : ℤ) (boxN n k - 1) ×ˢ Finset.Icc (-1 : ℤ) (boxN n k - 1)
          ×ˢ Finset.Icc (-1 : ℤ) (boxN n k - 1),
        (((ext3 φ (p.1 + 1, p.2.1, p.2.2) - ext3 φ p) / spacing n) ^ 2
          + ((ext3 φ (p.1, p.2.1 + 1, p.2.2) - ext3 φ p) / spacing n) ^ 2
          + ((ext3 φ (p.1, p.2.1, p.2.2 + 1) - ext3 φ p) / spacing n) ^ 2))
      + ∑ x : DSite3 n k, m₀ ^ 2 * φ x ^ 2)

/-- The infinite-lattice covariance G(0, x), x ∈ ℤ³, of the free field of mass m₀ at spacing
ε = 2^(−n): ε^(−1) (2π)^(−3) ∫_[−π,π]³ cos(θ·x) dθ / (m₀²ε² + Σ_i 4 sin²(θ_i/2)). -/
def latticeG3 (n : ℕ) (m₀ : ℝ) (x : ℤ × ℤ × ℤ) : ℝ :=
  (spacing n)⁻¹ * (2 * π)⁻¹ ^ 3 * ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π, ∫ θ₃ in (-π)..π,
    Real.cos (θ₁ * x.1 + θ₂ * x.2.1 + θ₃ * x.2.2) /
      (m₀ ^ 2 * spacing n ^ 2 + 4 * Real.sin (θ₁ / 2) ^ 2 + 4 * Real.sin (θ₂ / 2) ^ 2
        + 4 * Real.sin (θ₃ / 2) ^ 2)

/-- The Bauerschmidt–Dagallier mass counterterm
a^ε(λ) = −3λ G(0, 0) + 6λ² ε³ Σ'_(x ∈ ℤ³) |G(0, x)|³. -/
def massCT3 (n : ℕ) (m₀ lam : ℝ) : ℝ :=
  -3 * lam * latticeG3 n m₀ 0
    + 6 * lam ^ 2 * (spacing n ^ 3 * ∑' x : ℤ × ℤ × ℤ, |latticeG3 n m₀ x| ^ 3)

/-- The φ⁴₃ weight exp(−½ dirAction3 − ε³ Σ_x [(λ/4) φ(x)⁴ + ½ a^ε(λ) φ(x)²]). -/
def dweight3 (n k : ℕ) (m₀ lam : ℝ) (φ : DField3 n k) : ℝ :=
  Real.exp (-(dirAction3 n k m₀ φ) / 2
    - spacing n ^ 3 * ∑ x : DSite3 n k, (lam / 4 * φ x ^ 4 + massCT3 n m₀ lam / 2 * φ x ^ 2))

/-- ε³ Σ_x f(dpos3 x) φ(x). -/
def dsmear3 (n k : ℕ) (f : TestFn3) (φ : DField3 n k) : ℝ :=
  spacing n ^ 3 * ∑ x : DSite3 n k, f (dpos3 n k x) * φ x

/-- The generating functional of the φ⁴₃ Dirichlet-box measure. -/
def ZD3 (n k : ℕ) (m₀ lam : ℝ) (f : TestFn3) : ℂ :=
  (∫ φ : DField3 n k, Complex.exp (Complex.I * (dsmear3 n k f φ : ℂ)) * (dweight3 n k m₀ lam φ : ℂ)) /
    ((∫ φ : DField3 n k, dweight3 n k m₀ lam φ : ℝ) : ℂ)

/-- Translation in ℝ³: (τ_a g)(x) = g(x − a). -/
def translate3 (a : Space3) (g : TestFn3) : TestFn3 := SchwartzMap.compSubConstCLM ℝ a g

/-- Uniform clustering at finite cutoff at rate m in the distance max(|a₀|, |a₁|, |a₂|). -/
def FiniteCutoffClustering3 (m₀ lam m : ℝ) : Prop :=
  ∀ f g : TestFn3, HasCompactSupport ⇑f → HasCompactSupport ⇑g →
    ∃ C : ℝ, ∀ (n k : ℕ) (a : Space3),
      ‖ZD3 n k m₀ lam (f + translate3 a g) - ZD3 n k m₀ lam f * ZD3 n k m₀ lam (translate3 a g)‖
        ≤ C * Real.exp (-m * max |a 0| (max |a 1| |a 2|))

/-- Z is a limit point of the φ⁴₃ Dirichlet-box generating functionals. -/
def IsLimitPoint3 (m₀ lam : ℝ) (Z : TestFn3 → ℂ) : Prop :=
  ∃ ns ks : ℕ → ℕ, Tendsto ns atTop atTop ∧ Tendsto ks atTop atTop ∧
    ∀ f : TestFn3, Tendsto (fun j => ZD3 (ns j) (ks j) m₀ lam f) atTop (𝓝 (Z f))

/-- Z is not the generating functional of a Gaussian measure on ℝ³ test functions. -/
def IsNonGaussian3 (Z : TestFn3 → ℂ) : Prop :=
  ¬ ∃ (ℓ : TestFn3 →ₗ[ℝ] ℝ) (B : TestFn3 →ₗ[ℝ] TestFn3 →ₗ[ℝ] ℝ),
      ∀ f, Z f = Complex.exp (Complex.I * (ℓ f : ℂ) - ((B f f : ℝ) : ℂ) / 2)

/-- **Stage-two target.** Weakly coupled φ⁴₃: uniform finite-cutoff clustering, limit points
exist, every limit point is non-Gaussian. -/
def PhiFourThreeGap : Prop :=
  ∀ m₀ : ℝ, 0 < m₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ m : ℝ, 0 < m ∧
      FiniteCutoffClustering3 m₀ lam m ∧ (∃ Z, IsLimitPoint3 m₀ lam Z) ∧
        ∀ Z, IsLimitPoint3 m₀ lam Z → IsNonGaussian3 Z

end PP2Target

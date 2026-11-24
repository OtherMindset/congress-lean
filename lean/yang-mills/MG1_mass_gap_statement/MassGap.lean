import LongTable.ChallengeSpec

/-! The mass gap, stated against the public definitions of OpenAI's Yang–Mills
submission of 28 October 2026 (`PublicTheory`, `PublicWilson`, `ChallengeSpec`,
commit 3456e5e75cf8d4cd558955a5c7638fba2d68f464, Apache-2.0).

Nothing here is proved about Yang–Mills. The file gives the statement in several
forms and the projections back to `JointExistence`. Proved between the forms:
the mass-shell form gives the Hamiltonian form and the support statement under
W0, and is monotone in `m`. Not proved here: the Hamiltonian form giving the
mass-shell form (it needs Lorentz invariance of the measure), and any relation
between the Euclidean form `ClusterDecay` and the spectral forms. The gap itself
is open.

Conventions read from `PublicTheory`: the time axis is the last coordinate;
`W0.spectralRepresentation` pairs the energy–momentum measure with translations
through `charFun`, that is through the Euclidean pairing on `Spacetime`; and
`W0.positiveEnergy` puts the measure on `forwardCone = {‖spatial k‖ ≤ time k}`.
So `time k` is the energy and it is nonnegative on the support. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open Function Filter Set MeasureTheory
open scoped Topology

/-- Energy–momenta away from zero and strictly below the mass shell `m`. -/
def massRegion (m : ℝ) : Set Spacetime := {k | k ≠ 0 ∧ minkowskiSquare k < m ^ 2}

/-- Energies strictly between zero and `m`. -/
def energyRegion (m : ℝ) : Set Spacetime := {k | 0 < time k ∧ time k < m}

/-- The allowed support under a gap `m`: the origin and the cone on or above the shell. -/
def gappedSupport (m : ℝ) : Set Spacetime :=
  {0} ∪ {k | k ∈ forwardCone ∧ m ^ 2 ≤ minkowskiSquare k}

theorem continuous_time : Continuous time := by
  unfold time; exact PiLp.continuous_apply _ _ _

theorem continuous_spatial : Continuous spatial := by
  unfold spatial
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => PiLp.continuous_apply _ _ _)

theorem continuous_minkowskiSquare : Continuous minkowskiSquare := by
  unfold minkowskiSquare
  exact (continuous_time.pow 2).sub (continuous_spatial.norm.pow 2)

theorem measurableSet_massRegion (m : ℝ) : MeasurableSet (massRegion m) := by
  have h1 : MeasurableSet {k : Spacetime | k ≠ 0} := isOpen_ne.measurableSet
  have h2 : MeasurableSet {k : Spacetime | minkowskiSquare k < m ^ 2} :=
    (isOpen_lt continuous_minkowskiSquare continuous_const).measurableSet
  exact h1.inter h2

theorem measurableSet_energyRegion (m : ℝ) : MeasurableSet (energyRegion m) := by
  have h1 : MeasurableSet {k : Spacetime | 0 < time k} :=
    (isOpen_lt continuous_const continuous_time).measurableSet
  have h2 : MeasurableSet {k : Spacetime | time k < m} :=
    (isOpen_lt continuous_time continuous_const).measurableSet
  exact h1.inter h2

theorem isClosed_forwardCone : IsClosed forwardCone :=
  isClosed_le continuous_spatial.norm continuous_time

theorem measurableSet_gappedSupport (m : ℝ) : MeasurableSet (gappedSupport m) := by
  have h2 : MeasurableSet {k : Spacetime | m ^ 2 ≤ minkowskiSquare k} :=
    (isClosed_le continuous_const continuous_minkowskiSquare).measurableSet
  exact (measurableSet_singleton 0).union (isClosed_forwardCone.measurableSet.inter h2)

namespace EnergyMomentumMeasure
variable {H : HilbertSpace} (E : EnergyMomentumMeasure H)

/-- A projection of the measure vanishes when every diagonal measure does. -/
theorem projection_eq_zero_of_diagonal {A : Set Spacetime} (hA : MeasurableSet A)
    (h : ∀ ψ : H.carrier, E.diagonal ψ A = 0) : E.projection A = 0 := by
  have hidem : (E.projection A).comp (E.projection A) = E.projection A := by
    simpa using E.intersection hA hA
  ext ψ
  have h1 : inner ℂ (E.projection A ψ) (E.projection A ψ) = inner ℂ ψ (E.projection A ψ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, E.selfAdjoint hA,
      ← ContinuousLinearMap.comp_apply, hidem]
  have h2 : inner ℂ ψ (E.projection A ψ) = 0 := by
    rw [← E.diagonalIdentity hA ψ, Measure.real, h ψ]; simp
  have h3 : inner ℂ (E.projection A ψ) (E.projection A ψ) = 0 := h1.trans h2
  simpa using inner_self_eq_zero.mp h3

/-- Conversely, a vanishing projection makes every diagonal measure vanish. -/
theorem diagonal_eq_zero_of_projection {A : Set Spacetime} (hA : MeasurableSet A)
    (h : E.projection A = 0) (ψ : H.carrier) : E.diagonal ψ A = 0 := by
  have h1 := E.diagonalIdentity hA ψ
  rw [h] at h1
  have h2 : (E.diagonal ψ).real A = 0 := by simpa using h1
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h2

/-- A measurable set covered by two null sets is null. -/
theorem projection_eq_zero_of_subset_union {A B C : Set Spacetime}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : C ⊆ A ∪ B) (h1 : E.projection A = 0) (h2 : E.projection B = 0) :
    E.projection C = 0 := by
  refine E.projection_eq_zero_of_diagonal hC fun ψ => ?_
  have := measure_mono (μ := E.diagonal ψ) hAB
  have hu := measure_union_le (μ := E.diagonal ψ) A B
  rw [E.diagonal_eq_zero_of_projection hA h1 ψ, E.diagonal_eq_zero_of_projection hB h2 ψ,
    add_zero] at hu
  exact le_antisymm (this.trans hu) bot_le

end EnergyMomentumMeasure

namespace WightmanTheory
variable {H : HilbertSpace} {Labels : FieldLabels} (theory : WightmanTheory H Labels)

/-- Mass-shell form: no energy–momentum away from zero below the shell `m`. -/
def HasMassGap (m : ℝ) : Prop :=
  0 < m ∧ theory.energyMomentum.projection (massRegion m) = 0

/-- Hamiltonian form: no energy strictly between `0` and `m`. -/
def HasEnergyGap (m : ℝ) : Prop :=
  0 < m ∧ theory.energyMomentum.projection (energyRegion m) = 0

/-- There is spectrum away from the origin, so the supremum of gaps is finite. -/
def HasExcitations : Prop := theory.energyMomentum.projection {(0 : Spacetime)}ᶜ ≠ 0

variable {theory}

/-- A gap `m` is a gap `m'` for every smaller positive `m'`. -/
theorem HasMassGap.mono {m m' : ℝ} (h : theory.HasMassGap m) (hpos : 0 < m') (hle : m' ≤ m) :
    theory.HasMassGap m' := by
  refine ⟨hpos, ?_⟩
  have hsub : massRegion m' ⊆ massRegion m ∪ massRegion m := by
    intro k hk
    exact Or.inl ⟨hk.1, lt_of_lt_of_le hk.2 (pow_le_pow_left₀ hpos.le hle 2)⟩
  exact theory.energyMomentum.projection_eq_zero_of_subset_union (measurableSet_massRegion m)
    (measurableSet_massRegion m) (measurableSet_massRegion m') hsub h.2 h.2

/-- Under W0 the mass-shell form gives the Hamiltonian form. -/
theorem HasMassGap.energyGap {m : ℝ} (h : theory.HasMassGap m) (w0 : theory.W0) :
    theory.HasEnergyGap m := by
  refine ⟨h.1, ?_⟩
  have hsub : energyRegion m ⊆ massRegion m ∪ forwardConeᶜ := by
    intro k hk
    by_cases hc : k ∈ forwardCone
    · left
      refine ⟨?_, ?_⟩
      · rintro rfl
        have : time (0 : Spacetime) = 0 := by simp [time]
        exact absurd hk.1 (by rw [this]; exact lt_irrefl 0)
      · have h1 : time k ^ 2 < m ^ 2 := pow_lt_pow_left₀ hk.2 hk.1.le (by norm_num)
        have h2 : 0 ≤ ‖spatial k‖ ^ 2 := by positivity
        unfold minkowskiSquare; linarith
    · exact Or.inr hc
  exact theory.energyMomentum.projection_eq_zero_of_subset_union (measurableSet_massRegion m)
    isClosed_forwardCone.measurableSet.compl (measurableSet_energyRegion m) hsub h.2
    w0.positiveEnergy

/-- Under W0 a gap `m` puts the energy–momentum measure on the origin and the
part of the forward cone on or above the mass shell. -/
theorem HasMassGap.support {m : ℝ} (h : theory.HasMassGap m) (w0 : theory.W0) :
    theory.energyMomentum.projection (gappedSupport m)ᶜ = 0 := by
  have hsub : (gappedSupport m)ᶜ ⊆ massRegion m ∪ forwardConeᶜ := by
    intro k hk
    by_cases hc : k ∈ forwardCone
    · left
      have hk0 : k ≠ 0 := fun h0 => hk (Or.inl h0)
      refine ⟨hk0, ?_⟩
      by_contra hlt
      exact hk (Or.inr ⟨hc, not_lt.mp hlt⟩)
    · exact Or.inr hc
  exact theory.energyMomentum.projection_eq_zero_of_subset_union (measurableSet_massRegion m)
    isClosed_forwardCone.measurableSet.compl (measurableSet_gappedSupport m).compl hsub h.2
    w0.positiveEnergy

end WightmanTheory

namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- The unit vector along the time axis. -/
def timeUnit : Spacetime := EuclideanSpace.single timeAxis 1

/-- A group of `n` points followed by a group of `k` points moved by `t` in time. -/
def timeSplit {n k : ℕ} (x : Points n) (y : Points k) (t : ℝ) : Points (n + k) :=
  WithLp.toLp 2 (Fin.append x.ofLp fun j => y.ofLp j + t • timeUnit)

/-- Euclidean form: truncated correlations of the component `s` (`none` is the
lattice limit, `some i` a phase) decay at rate `m` in the time separation of two
groups of insertions. Only separated configurations are constrained, since the
public statement says nothing about `correlation` elsewhere, and the constants
are uniform on compact sets of configurations, as smearing requires. -/
def ClusterDecay (s : Option T.Character) (m : ℝ) : Prop :=
  ∀ (n k : ℕ) (a : Fin n → T.Tag) (b : Fin k → T.Tag)
    (X : Set (Points n)) (Y : Set (Points k)), IsCompact X → IsCompact Y →
    X ⊆ (WilsonFamily.separated n : Set (Points n)) →
    Y ⊆ (WilsonFamily.separated k : Set (Points k)) →
    ∃ K t₀ : ℝ, ∀ x ∈ X, ∀ y ∈ Y, ∀ t : ℝ, t₀ ≤ t →
      ‖T.correlation s (Fin.append a b) (timeSplit x y t) -
        T.correlation s a x * T.correlation s b y‖ ≤ K * Real.exp (-m * t)

end Hierarchy

/-- The draft target: a gap in the selected phase of each refinement; `m` may
depend on the volume sequence. -/
def JointExistenceWithGap : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ ∃ m : ℝ, T.theory.HasMassGap m

/-- One `m` per gauge group, for every volume sequence. -/
def JointExistenceWithUniformGap : Prop := ∀ g : GaugeGroup, g.IsSimple →
  ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∃ m : ℝ, ∀ p : ℕ → ℕ, StrictMono p →
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ T.theory.HasMassGap m

/-- The selected-phase gap with the finiteness clause of the assessment's item 4. -/
def JointExistenceWithFiniteGap : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ T.theory.HasExcitations ∧
      ∃ m : ℝ, T.theory.HasMassGap m

/-- Euclidean form in every phase and in the lattice limit, at one rate. -/
def JointExistenceWithClusterDecay : Prop := ∀ g : GaugeGroup, g.IsSimple →
  ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p →
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧
      ∃ m : ℝ, 0 < m ∧ ∀ s : Option T.Character, T.ClusterDecay s m

theorem JointExistenceWithUniformGap.withGap (h : JointExistenceWithUniformGap) :
    JointExistenceWithGap := by
  intro g hg
  obtain ⟨C, hC, m, hm⟩ := h g hg
  refine ⟨C, hC, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hT, hgap⟩ := hm p hp
  exact ⟨q, hq, T, hT, m, hgap⟩

theorem JointExistenceWithFiniteGap.withGap (h : JointExistenceWithFiniteGap) :
    JointExistenceWithGap := by
  intro g hg
  obtain ⟨C, hC, hp⟩ := h g hg
  refine ⟨C, hC, fun p hpm => ?_⟩
  obtain ⟨q, hq, T, hT, _, hgap⟩ := hp p hpm
  exact ⟨q, hq, T, hT, hgap⟩

/-- The gap target contains the submission's public theorem. -/
theorem JointExistenceWithGap.jointExistence (h : JointExistenceWithGap) : JointExistence := by
  intro g hg
  obtain ⟨C, hC, hp⟩ := h g hg
  refine ⟨C, hC, fun p hpm => ?_⟩
  obtain ⟨q, hq, T, hT, _⟩ := hp p hpm
  exact ⟨q, hq, T, hT⟩

/-- In the draft target every selected phase also has the Hamiltonian gap. -/
theorem JointExistenceWithGap.energyGap (h : JointExistenceWithGap) :
    ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
      WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ ∃ m : ℝ, T.theory.HasEnergyGap m := by
  intro g hg
  obtain ⟨C, hC, hp⟩ := h g hg
  refine ⟨C, hC, fun p hpm => ?_⟩
  obtain ⟨q, hq, T, hT, m, hgap⟩ := hp p hpm
  exact ⟨q, hq, T, hT, m, hgap.energyGap hT.reconstruction.axioms.w0⟩

end YangMills

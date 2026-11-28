import ChallengeSpec
import YM.Ground.Moments
import YM.Ground.Spectrum
import YM.Spec.Closed

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

/-! One phase or many, for the phase mixture of OpenAI's Yang–Mills construction.

Stated against the public `Hierarchy` of OpenAI's submission of 28 October 2026
(commit 3456e5e75cf8d4cd558955a5c7638fba2d68f464, Apache-2.0), through the posted
`MassGap` module (#mwuyw6ne-1irnyq), which supplies `timeSplit`.

Nothing here is proved about Yang–Mills. The file states the single-phase question
(U1) in three forms and relates them; states rate-free clustering; proves the easy
direction (one phase and clustering of the selected phase give clustering of the
lattice limit); and proves the hard direction (clustering of the lattice limit gives
one phase) from three properties of the components, which are hypotheses here.

(U1) is not (U2): one phase for a given refinement says nothing about whether
different volume subsequences give the same theory. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open Function Filter Set MeasureTheory
open scoped Topology ComplexConjugate

namespace Hierarchy

/-! ## Separation of two groups far apart in time -/

theorem time_timeUnit : time timeUnit = 1 := by
  simp [time, timeUnit]

theorem time_add_smul_timeUnit (y : Spacetime) (t : ℝ) :
    time (y + t • timeUnit) = time y + t := by
  simp [time, timeUnit]

/-- Two separated groups, the second moved far enough forward in time, form a
separated configuration. -/
theorem eventually_timeSplit_mem {n k : ℕ} {x : Points n} {y : Points k}
    (hx : x ∈ WilsonFamily.separated n) (hy : y ∈ WilsonFamily.separated k) :
    ∀ᶠ t : ℝ in atTop, timeSplit x y t ∈ WilsonFamily.separated (n + k) := by
  have hfar : ∀ᶠ t : ℝ in atTop, ∀ i : Fin n, ∀ j : Fin k,
      x.ofLp i ≠ y.ofLp j + t • timeUnit := by
    rw [eventually_all]; intro i
    rw [eventually_all]; intro j
    filter_upwards [eventually_gt_atTop (time (x.ofLp i) - time (y.ofLp j))] with t ht he
    have := congrArg time he
    rw [time_add_smul_timeUnit] at this
    linarith
  filter_upwards [hfar] with t ht
  change Injective (Fin.append x.ofLp fun j => y.ofLp j + t • timeUnit)
  have hx' : Injective x.ofLp := hx
  have hy' : Injective fun j => y.ofLp j + t • timeUnit := by
    intro j j' h; exact hy (add_right_cancel h)
  intro p q hpq
  induction p using Fin.addCases with
  | left i =>
    induction q using Fin.addCases with
    | left i' => simp only [Fin.append_left] at hpq; rw [hx' hpq]
    | right j' =>
      simp only [Fin.append_left, Fin.append_right] at hpq; exact absurd hpq (ht i j')
  | right j =>
    induction q using Fin.addCases with
    | left i' =>
      simp only [Fin.append_left, Fin.append_right] at hpq; exact absurd hpq.symm (ht i' j)
    | right j' => simp only [Fin.append_right] at hpq; rw [hy' hpq]

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-! ## (U1), three forms -/

/-- (U1), correlational form: every phase has the correlations of the lattice limit
on separated points. Equivalently (`singlePhase_iff_ae`, under `Reconstructed`) the
phase measure pushed forward to correlations is a point mass. This is the form in
which "the Wightman theory is the lattice limit" holds. -/
def SinglePhase : Prop :=
  ∀ (n : ℕ) (a : Fin n → T.Tag) (x : Points n), x ∈ WilsonFamily.separated n →
    ∀ i : T.Character, T.correlation (some i) a x = T.correlation none a x

/-- (U1), measure form: the phase measure is the point mass at `selected`. Under
`Reconstructed` this says only that `Character` is a single point
(`diracPhase_iff_subsingleton`), a statement about the parametrisation; `SinglePhase`
is the substantive form. -/
def DiracPhase : Prop := T.phaseMeasure = Measure.dirac T.selected

/-- Correlations tell characters apart. The public `Reconstructed` does not say this;
without it `SinglePhase` need not give `DiracPhase`. -/
def Separates : Prop :=
  ∀ i j : T.Character,
    (∀ (n : ℕ) (a : Fin n → T.Tag) (x : Points n), x ∈ WilsonFamily.separated n →
      T.correlation (some i) a x = T.correlation (some j) a x) → i = j

/-- Rate-free clustering of the component `s` (`none` is the lattice limit, `some i`
a phase) in the time separation of two groups of insertions: the rate-free version
of `ClusterDecay` (`clusters_of_clusterDecay`). The second group's own correlation is
taken unmoved; taking `n = 0` shows this also asks that the component be asymptotically
invariant under time translation. -/
def Clusters (s : Option T.Character) : Prop :=
  ∀ (n k : ℕ) (a : Fin n → T.Tag) (b : Fin k → T.Tag) (x : Points n) (y : Points k),
    x ∈ WilsonFamily.separated n → y ∈ WilsonFamily.separated k →
    Tendsto (fun t : ℝ => T.correlation s (Fin.append a b) (timeSplit x y t)) atTop
      (𝓝 (T.correlation s a x * T.correlation s b y))

/-- A rate gives rate-free clustering. -/
theorem clusters_of_clusterDecay {s : Option T.Character} {m : ℝ} (hm : 0 < m)
    (h : T.ClusterDecay s m) : T.Clusters s := by
  intro n k a b x y hx hy
  obtain ⟨K, t₀, hK⟩ := h n k a b {x} {y} isCompact_singleton isCompact_singleton
    (singleton_subset_iff.2 hx) (singleton_subset_iff.2 hy)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hexp : Tendsto (fun t : ℝ => K * Real.exp (-m * t)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun t : ℝ => Real.exp (-m * t)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hm)
      refine this.congr fun t => ?_
      simp [Function.comp, neg_mul]
    simpa using h2.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hexp
  filter_upwards [eventually_ge_atTop t₀] with t ht
  exact hK x rfl y rfl t ht

/-! ## Relations between the forms -/

variable {T}

theorem diracPhase_iff_subsingleton (hR : T.Reconstructed) :
    T.DiracPhase ↔ Subsingleton T.Character := by
  have := hR.normalized
  have := hR.fullSupport
  constructor
  · intro hD
    have hall : ∀ i : T.Character, i = T.selected := by
      intro i
      by_contra hi
      have hopen : IsOpen ({T.selected}ᶜ : Set T.Character) := isOpen_compl_singleton
      have hpos := hopen.measure_ne_zero T.phaseMeasure ⟨i, hi⟩
      apply hpos
      rw [hD, Measure.dirac_apply' _ (measurableSet_singleton _).compl]
      simp
    exact ⟨fun i j => (hall i).trans (hall j).symm⟩
  · intro hS
    ext s hs
    rw [Measure.dirac_apply' _ hs]
    by_cases h : T.selected ∈ s
    · have : s = univ := eq_univ_of_forall fun i => Subsingleton.elim T.selected i ▸ h
      simp [this]
    · have : s = ∅ := eq_empty_of_forall_notMem fun i hi =>
        h (Subsingleton.elim i T.selected ▸ hi)
      simp [this]

theorem singlePhase_of_subsingleton (hR : T.Reconstructed) [Subsingleton T.Character] :
    T.SinglePhase := by
  have := hR.normalized
  intro n a x hx i
  rw [← hR.mixture a x hx]
  have : (fun j : T.Character => T.correlation (some j) a x) =
      fun _ => T.correlation (some i) a x := by
    funext j; rw [Subsingleton.elim j i]
  rw [this, integral_const]
  simp

theorem subsingleton_of_singlePhase (hS : T.SinglePhase) (hsep : T.Separates) :
    Subsingleton T.Character :=
  ⟨fun i j => hsep i j fun n a x hx => (hS n a x hx i).trans (hS n a x hx j).symm⟩

theorem singlePhase_of_diracPhase (hR : T.Reconstructed) (hD : T.DiracPhase) :
    T.SinglePhase := by
  have := (diracPhase_iff_subsingleton hR).1 hD
  exact singlePhase_of_subsingleton hR

theorem diracPhase_of_singlePhase (hR : T.Reconstructed) (hS : T.SinglePhase)
    (hsep : T.Separates) : T.DiracPhase := by
  have := subsingleton_of_singlePhase hS hsep
  exact (diracPhase_iff_subsingleton hR).2 inferInstance

/-- Under `Separates`, the three forms agree. -/
theorem singlePhase_iff_diracPhase (hR : T.Reconstructed) (hsep : T.Separates) :
    T.SinglePhase ↔ T.DiracPhase :=
  ⟨fun h => diracPhase_of_singlePhase hR h hsep, singlePhase_of_diracPhase hR⟩

/-- Almost everywhere is enough: by `characterContinuity` and `fullSupport`, a phase
correlation equal to the lattice limit for almost every character is equal for all. -/
theorem singlePhase_iff_ae (hR : T.Reconstructed) :
    T.SinglePhase ↔ ∀ (n : ℕ) (a : Fin n → T.Tag) (x : Points n),
      x ∈ WilsonFamily.separated n →
      (fun i => T.correlation (some i) a x) =ᵐ[T.phaseMeasure]
        fun _ => T.correlation none a x := by
  have := hR.fullSupport
  constructor
  · intro h n a x hx
    exact Eventually.of_forall fun i => h n a x hx i
  · intro h n a x hx i
    have := (Continuous.ae_eq_iff_eq T.phaseMeasure (hR.characterContinuity a x hx)
      continuous_const).1 (h n a x hx)
    exact congrFun this i

/-- One phase makes the selected phase the lattice limit. -/
theorem SinglePhase.selected_eq (hS : T.SinglePhase) {n : ℕ} (a : Fin n → T.Tag)
    (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    T.correlation (some T.selected) a x = T.correlation none a x :=
  hS n a x hx T.selected

/-! ## D2: the easy direction -/

/-- One phase and clustering of the selected phase give clustering of the lattice
limit. -/
theorem clusters_none_of_singlePhase (hS : T.SinglePhase)
    (hc : T.Clusters (some T.selected)) : T.Clusters none := by
  intro n k a b x y hx hy
  have h := hc n k a b x y hx hy
  rw [← hS n a x hx, ← hS k b y hy]
  refine h.congr' ?_
  filter_upwards [eventually_timeSplit_mem hx hy] with t ht
  exact hS _ _ _ ht _

/-! ## D3: the hard direction, from three properties of the components -/

/-- (P1) Rate-free clustering of every component. -/
def ComponentsCluster (T : Hierarchy C) : Prop := ∀ i : T.Character, T.Clusters (some i)

/-- (P2) Reflection–reality: every separated configuration has a partner whose
correlations are the complex conjugates, in every component at once. -/
def HasConjugates (T : Hierarchy C) : Prop :=
  ∀ (n : ℕ) (a : Fin n → T.Tag) (x : Points n), x ∈ WilsonFamily.separated n →
    ∃ (m : ℕ) (a' : Fin m → T.Tag) (x' : Points m), x' ∈ WilsonFamily.separated m ∧
      ∀ i : T.Character, T.correlation (some i) a' x' = conj (T.correlation (some i) a x)

/-- (P3) A bound on the joint correlations of two groups, uniform over characters and
over large separations. -/
def UniformlyBounded (T : Hierarchy C) : Prop :=
  ∀ (n k : ℕ) (a : Fin n → T.Tag) (b : Fin k → T.Tag) (x : Points n) (y : Points k),
    x ∈ WilsonFamily.separated n → y ∈ WilsonFamily.separated k →
    ∃ K t₀ : ℝ, ∀ t, t₀ ≤ t → ∀ i : T.Character,
      ‖T.correlation (some i) (Fin.append a b) (timeSplit x y t)‖ ≤ K

private theorem integrable_of_continuous (hR : T.Reconstructed) {f : T.Character → ℂ}
    (hf : Continuous f) : Integrable f T.phaseMeasure := by
  have := hR.normalized
  exact hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport f) (subset_univ _))

/-- Variance zero: if `∫ conj f · f = conj (∫ f) · ∫ f` for a continuous `f` on a
space with a full-support probability measure, then `f` is the constant `∫ f`. -/
theorem eq_integral_of_variance (hR : T.Reconstructed) {f : T.Character → ℂ}
    (hf : Continuous f)
    (hvar : ∫ i, conj (f i) * f i ∂T.phaseMeasure =
      conj (∫ i, f i ∂T.phaseMeasure) * ∫ i, f i ∂T.phaseMeasure) :
    ∀ i, f i = ∫ j, f j ∂T.phaseMeasure := by
  have := hR.normalized
  have := hR.fullSupport
  set c := ∫ j, f j ∂T.phaseMeasure with hc
  have hfi := integrable_of_continuous hR hf
  have hcf : Continuous fun i => conj (f i) := Continuous.comp Complex.continuous_conj hf
  have hcfi := integrable_of_continuous hR hcf
  have hprod : Integrable (fun i => conj (f i) * f i) T.phaseMeasure :=
    integrable_of_continuous hR (hcf.mul hf)
  -- the complex integral of |f - c|² is zero
  have hz : ∫ i, conj (f i - c) * (f i - c) ∂T.phaseMeasure = 0 := by
    have e : (fun i => conj (f i - c) * (f i - c)) =
        fun i => (conj (f i) * f i - conj c * f i) - (c * conj (f i) - conj c * c) := by
      funext i; simp only [map_sub]; ring
    have i1 : Integrable (fun i => conj (f i) * f i - conj c * f i) T.phaseMeasure :=
      hprod.sub (hfi.const_mul _)
    have i2 : Integrable (fun i => c * conj (f i) - conj c * c) T.phaseMeasure :=
      (hcfi.const_mul _).sub (integrable_const _)
    rw [e, integral_sub i1 i2, integral_sub hprod (hfi.const_mul _),
      integral_sub (hcfi.const_mul _) (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const, integral_conj, hvar, ← hc]
    simp only [probReal_univ, one_smul]
    ring
  -- so the real integral of |f - c|² is zero
  have hreal : ∫ i, ‖f i - c‖ ^ 2 ∂T.phaseMeasure = 0 := by
    have : (fun i => conj (f i - c) * (f i - c)) = fun i => ((‖f i - c‖ ^ 2 : ℝ) : ℂ) := by
      funext i; rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
    rw [this, integral_complex_ofReal] at hz
    exact_mod_cast hz
  have hcont : Continuous fun i => ‖f i - c‖ ^ 2 := ((hf.sub continuous_const).norm).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun i => by positivity)
    (integrable_of_continuous_real hR hcont)).1 hreal
  have heq := (Continuous.ae_eq_iff_eq T.phaseMeasure hcont continuous_const).1 hae
  intro i
  have h0 : ‖f i - c‖ ^ 2 = 0 := congrFun heq i
  exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))
where
  integrable_of_continuous_real (hR : T.Reconstructed) {h : T.Character → ℝ}
      (hh : Continuous h) : Integrable h T.phaseMeasure := by
    have := hR.normalized
    exact hh.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport h) (subset_univ _))

/-- The hard direction, conditional: rate-free clustering of the lattice limit gives
one phase, given (P1) clustering of every component, (P2) conjugate partners and
(P3) a uniform bound. This is the variance argument of the working group's
assessment, section 6.2, with the hypotheses it leaves implicit (P2, P3) stated
explicitly. -/
theorem singlePhase_of_clusters (hR : T.Reconstructed) (h1 : T.ComponentsCluster)
    (h2 : T.HasConjugates) (h3 : T.UniformlyBounded) (hc : T.Clusters none) :
    T.SinglePhase := by
  have := hR.normalized
  intro n a x hx
  obtain ⟨m, a', x', hx', hconj⟩ := h2 n a x hx
  set f : T.Character → ℂ := fun i => T.correlation (some i) a x
  have hf : Continuous f := hR.characterContinuity a x hx
  have hf' : Continuous fun i => T.correlation (some i) a' x' :=
    hR.characterContinuity a' x' hx'
  set G : ℝ → T.Character → ℂ := fun t i =>
    T.correlation (some i) (Fin.append a' a) (timeSplit x' x t)
  have hsepE := eventually_timeSplit_mem hx' hx
  obtain ⟨K, t₀, hK⟩ := h3 m n a' a x' x hx' hx
  -- the mixture, integrated, converges to ∫ conj f · f
  have hlim : Tendsto (fun t => ∫ i, G t i ∂T.phaseMeasure) atTop
      (𝓝 (∫ i, conj (f i) * f i ∂T.phaseMeasure)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => K) ?_ ?_
      (integrable_const K) (Eventually.of_forall fun i => ?_)
    · filter_upwards [hsepE] with t ht
      exact (hR.characterContinuity _ _ ht).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop t₀] with t ht
      exact Eventually.of_forall fun i => hK t ht i
    · have := h1 i m n a' a x' x hx' hx
      simpa [G, hconj i] using this
  -- and to the product of the lattice-limit correlations
  have hlim' : Tendsto (fun t => ∫ i, G t i ∂T.phaseMeasure) atTop
      (𝓝 (T.correlation none a' x' * T.correlation none a x)) := by
    refine (hc m n a' a x' x hx' hx).congr' ?_
    filter_upwards [hsepE] with t ht
    exact (hR.mixture _ _ ht).symm
  have hvar := tendsto_nhds_unique hlim hlim'
  rw [← hR.mixture a' x' hx', ← hR.mixture a x hx] at hvar
  simp only [hconj] at hvar
  rw [integral_conj] at hvar
  have key := eq_integral_of_variance hR hf hvar
  intro i
  exact (key i).trans (hR.mixture a x hx)

/-- Under (P1)–(P3), one phase is exactly rate-free clustering of the lattice limit. -/
theorem singlePhase_iff_clusters (hR : T.Reconstructed) (h1 : T.ComponentsCluster)
    (h2 : T.HasConjugates) (h3 : T.UniformlyBounded) :
    T.SinglePhase ↔ T.Clusters none :=
  ⟨fun h => clusters_none_of_singlePhase h (h1 T.selected),
    singlePhase_of_clusters hR h1 h2 h3⟩

end Hierarchy

/-- `JointExistence` with one phase on every refinement. -/
def JointExistenceWithSinglePhase : Prop := ∀ g : GaugeGroup, g.IsSimple →
  ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p →
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧ T.SinglePhase

theorem JointExistenceWithSinglePhase.jointExistence (h : JointExistenceWithSinglePhase) :
    JointExistence := by
  intro g hg
  obtain ⟨C, hC, hp⟩ := h g hg
  refine ⟨C, hC, fun p hpm => ?_⟩
  obtain ⟨q, hq, T, hT, _⟩ := hp p hpm
  exact ⟨q, hq, T, hT⟩

end YangMills


/-! Council check (24 November 2026), built locally on Lean 4.32.0 against OpenAI's submission at
3456e5e75cf8d4cd558955a5c7638fba2d68f464 (Mathlib 81a5d257). Part 1: two characters of the phase resolution whose
component tables agree on every distinct word are equal. This is `Separates` of the
council's public `OnePhase` file (#mwvhv107-mzajy4), at the level of the private `Resolution`. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Spread.Resolution
open Function Set Filter Analysis Word
open scoped NNReal

variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} {P : Spread V}
variable (R : P.Resolution)

/-- Characters that agree on every slab generator are equal. -/
theorem eq_of_slots (hv : R.Out) {i j : R.X}
    (h : ∀ (w : L.Word) (d : ℝ≥0) (hw : Slab timeAxis d w),
      R.character i (P.slot w d hw) = R.character j (P.slot w d hw)) : i = j := by
  apply hv.onto.1
  apply StarAlgHomClass.ext_topologicalClosure (hv.values i) (hv.values j)
  intro x
  have key : ((R.character i).comp (StarSubalgebra.inclusion
      (StarSubalgebra.le_topologicalClosure _))) =
      ((R.character j).comp (StarSubalgebra.inclusion
      (StarSubalgebra.le_topologicalClosure _))) := by
    apply StarAlgHom.ext_adjoin
    intro y hy
    obtain ⟨w, d, hw, he⟩ := hy
    have : StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure _) y = P.slot w d hw :=
      Subtype.ext he
    exact (congrArg (R.character i) this).trans
      ((h w d hw).trans (congrArg (R.character j) this).symm)
  exact congrArg (fun φ => φ x) key

/-- Separation by words: if the component tables of `i` and `j` agree on every
distinct word, then `i = j`. -/
theorem eq_of_words (hv : R.Out) (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    {i j : R.X} (hw : ∀ w : L.Word, distinct w → (T i).expect w = (T j).expect w) :
    i = j := by
  apply R.eq_of_slots hv
  intro w d hs
  have hd : distinct w := hs.2.1.1
  have hc : carry w 0 = w := by simp [carry]
  have hs' : Slab timeAxis d (carry w 0) := by rw [hc]; exact hs
  have e1 := ht i w hd 0 d hs'
  have e2 := ht j w hd 0 d hs'
  have hslot : P.slot (carry w 0) d hs' = P.slot w d hs := by
    apply Subtype.ext; simp only [slot, hc]
  rw [hslot] at e1 e2
  rw [← e1, ← e2]
  exact hw w hd
end YM.OS.Spread.Resolution

/-! Council check (24 November 2026): in OpenAI's phase resolution, the limit of the
mixed table on two distinct words pulled apart in time is the phase average of the
product of the two phase values. So the mixed table clusters on this pair exactly
when the covariance over phases of the two words' values vanishes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Ground
open Function Set Filter Word MeasureTheory
open scoped Topology NNReal

variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)

/-- Each phase reads `M A` as its own value of `A`. -/
theorem character_M (R : P.Resolution) (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    (i : R.X) (A : L.Word) (H : distinct A) : R.character i (M P A H) = (T i).expect A := by
  exact (ht i A H _ _ (Spread.Resolution.place_exists H).choose_spec.choose_spec).symm

/-- The two-word cluster limit of the mixed table is the phase average of the product. -/
theorem mixed_two_cluster (Hs : Steady V) (Y : S.Hierarchy) (R : P.Resolution) (hv : R.Out)
    (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    (A B : L.Word) (hA : distinct A) (hB : distinct B) (f g : ℕ → E4) (hfg : flight f g) :
    (∀ᶠ n in atTop, distinct (carry A (f n) ++ carry B (g n))) ∧
    Tendsto (fun n => S.expect (carry A (f n) ++ carry B (g n))) atTop
      (𝓝 (∫ i, (T i).expect A * (T i).expect B ∂(R.μ))) := by
  let q : List (Car L) := [(⟨A, hA⟩, f), (⟨B, hB⟩, g)]
  have hq : line q :=
    List.Pairwise.cons (by simpa using hfg) (List.Pairwise.cons (by simp) List.Pairwise.nil)
  obtain ⟨h1, h2⟩ := arcs P Hs Y q hq
  have hall : ∀ n, all q n = carry A (f n) ++ carry B (g n) := by
    intro n; simp [all, q]
  have hlim : inner ℂ V.omega0 ((starU P (q.map Prod.fst)).val V.omega0) =
      ∫ i, (T i).expect A * (T i).expect B ∂(R.μ) := by
    rw [← hv.ground]
    congr 1; funext i
    simp only [starU, q, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      map_mul]
    rw [character_M P R T ht i A hA, character_M P R T ht i B hB]
  simp only [hall] at h1 h2
  exact ⟨h1, hlim ▸ h2⟩
end YM.OS.Ground

namespace YM.OS.Ground
open Function Set Filter Word MeasureTheory
open scoped Topology NNReal ComplexConjugate

variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)

/-- A conjugated word is distinct when the word is. -/
theorem distinct_conjugate {w : L.Word} (h : distinct w) : distinct (conjugate w) := by
  rw [locations] at h ⊢
  simpa [conjugate, List.map_map, Function.comp_def] using h

/-- Reality of a table gives the value of the conjugated word. -/
theorem expect_conjugate {T : Table L} (hT : T.RealSpin) {w : L.Word} (h : distinct w) :
    T.expect (conjugate w) = star (T.expect w) := by
  have hl : w.length = (conjugate w).length := by simp [conjugate]
  have e := T.readCast hl (fun i => ((w.get i).1, L.conjugate (w.get i).2))
    (positions w) (L.conjugate ∘ tokens w) (fun i => by simp [conjugate]) (fun i => rfl)
  rw [e, hT.real h]
  rfl

/-- Time-separated pairs of words: the mixed table clusters on them. -/
def MixedClusters (S : Table L) : Prop :=
  ∀ (A B : L.Word), distinct A → distinct B → ∀ f g : ℕ → E4, flight f g →
    Tendsto (fun n => S.expect (carry A (f n) ++ carry B (g n))) atTop
      (𝓝 (S.expect A * S.expect B))

/-- Clustering of the mixed table along one flight: the second word moved by `n` in time. -/
def BasisClusters (S : Table L) : Prop :=
  ∀ (A B : L.Word), distinct A → distinct B →
    Tendsto (fun n : ℕ => S.expect (carry A 0 ++ carry B ((n : ℝ) • basis timeAxis))) atTop
      (𝓝 (S.expect A * S.expect B))

theorem flight_basis : flight (fun _ : ℕ => (0 : E4)) (fun n => (n : ℝ) • basis timeAxis) := by
  unfold flight
  simp only [sub_zero]
  have : (fun n : ℕ => ((n : ℝ) • basis timeAxis) timeAxis) = fun n : ℕ => (n : ℝ) := by
    funext n; simp [basis]
  rw [this]; exact tendsto_natCast_atTop_atTop

/-- Variance zero on a compact space with a full-support probability measure. -/
theorem const_of_variance {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {f : X → ℂ} (hf : Continuous f)
    (hvar : ∫ i, conj (f i) * f i ∂μ = conj (∫ i, f i ∂μ) * ∫ i, f i ∂μ) :
    ∀ i, f i = ∫ j, f j ∂μ := by
  have hint : ∀ {h : X → ℂ}, Continuous h → Integrable h μ := fun hh =>
    hh.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hintR : ∀ {h : X → ℝ}, Continuous h → Integrable h μ := fun hh =>
    hh.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  set c := ∫ j, f j ∂μ with hc
  have hcf : Continuous fun i => conj (f i) := Continuous.comp Complex.continuous_conj hf
  have hfi := hint hf
  have hcfi := hint hcf
  have hprod : Integrable (fun i => conj (f i) * f i) μ := hint (hcf.mul hf)
  have hz : ∫ i, conj (f i - c) * (f i - c) ∂μ = 0 := by
    have e : (fun i => conj (f i - c) * (f i - c)) =
        fun i => (conj (f i) * f i - conj c * f i) - (c * conj (f i) - conj c * c) := by
      funext i; simp only [map_sub]; ring
    have i1 : Integrable (fun i => conj (f i) * f i - conj c * f i) μ :=
      hprod.sub (hfi.const_mul _)
    have i2 : Integrable (fun i => c * conj (f i) - conj c * c) μ :=
      (hcfi.const_mul _).sub (integrable_const _)
    rw [e, integral_sub i1 i2, integral_sub hprod (hfi.const_mul _),
      integral_sub (hcfi.const_mul _) (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const, integral_conj, hvar, ← hc]
    simp only [probReal_univ, one_smul]
    ring
  have hreal : ∫ i, ‖f i - c‖ ^ 2 ∂μ = 0 := by
    have : (fun i => conj (f i - c) * (f i - c)) = fun i => ((‖f i - c‖ ^ 2 : ℝ) : ℂ) := by
      funext i; rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
    rw [this, integral_complex_ofReal] at hz
    exact_mod_cast hz
  have hcont : Continuous fun i => ‖f i - c‖ ^ 2 := ((hf.sub continuous_const).norm).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun i => by positivity) (hintR hcont)).1 hreal
  have heq := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 hae
  intro i
  have h0 : ‖f i - c‖ ^ 2 = 0 := congrFun heq i
  exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))

/-- One phase from mixed clustering: if the mixed table clusters on time-separated
pairs of words along the basis flight, every phase has the mixed table's value on every distinct word. -/
theorem phase_eq_of_basisClusters (Hs : Steady V) (Y : S.Hierarchy) (R : P.Resolution)
    (hv : R.Out) (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    (hreal : ∀ i, (T i).RealSpin) (hc : BasisClusters S) :
    ∀ (A : L.Word), distinct A → ∀ i, (T i).expect A = S.expect A := by
  have := hv.normalized
  have := hv.support
  intro A hA
  have hA' := distinct_conjugate hA
  obtain ⟨-, hlim⟩ := mixed_two_cluster P Hs Y R hv T ht (conjugate A) A hA' hA _ _ flight_basis
  have h2 := hc (conjugate A) A hA' hA
  have hvar := tendsto_nhds_unique hlim h2
  have hbar : ∀ {w : L.Word}, distinct w → ∫ i, (T i).expect w ∂(R.μ) = S.expect w :=
    fun hw => Spread.Resolution.barycenter R T hv ht Y.translations _ hw
  rw [← hbar hA', ← hbar hA] at hvar
  simp only [expect_conjugate (hreal _) hA] at hvar
  have hvar' : ∫ i, conj ((T i).expect A) * (T i).expect A ∂(R.μ) =
      conj (∫ i, (T i).expect A ∂(R.μ)) * ∫ i, (T i).expect A ∂(R.μ) := by
    rw [← integral_conj]; exact hvar
  have hcont : Continuous fun i => (T i).expect A :=
    (hv.weak (M P A hA)).congr fun i => character_M P R T ht i A hA
  have key := const_of_variance R.μ hcont hvar'
  intro i
  exact (key i).trans (hbar hA)
end YM.OS.Ground

namespace YM.OS.Ground
open Function Set Filter Word MeasureTheory
open scoped Topology NNReal

variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)

/-- (U1) in the private library: the phase space is a single point exactly when the
mixed table clusters on time-separated pairs of words. Inputs: the mixed chamber is
steady, the mixed table satisfies the Euclidean hierarchy, the resolution has its `Out`
properties, every phase receives its character, and every phase is real. -/
theorem subsingleton_iff_mixedClusters (Hs : Steady V) (Y : S.Hierarchy) (R : P.Resolution)
    (hv : R.Out) (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    (hreal : ∀ i, (T i).RealSpin) :
    Subsingleton R.X ↔ MixedClusters S := by
  have := hv.normalized
  have hbar : ∀ {w : L.Word}, distinct w → ∫ i, (T i).expect w ∂(R.μ) = S.expect w :=
    fun hw => Spread.Resolution.barycenter R T hv ht Y.translations _ hw
  constructor
  · intro hsub A B hA hB f g hfg
    obtain ⟨-, hlim⟩ := mixed_two_cluster P Hs Y R hv T ht A B hA hB f g hfg
    have hne : Nonempty R.X := by
      by_contra hn
      rw [not_nonempty_iff] at hn
      have h1 := measure_univ (μ := R.μ)
      rw [Set.univ_eq_empty_iff.2 hn, measure_empty] at h1
      exact zero_ne_one h1
    obtain ⟨i₀⟩ := hne
    have hconst : ∀ {w : L.Word}, distinct w → ∀ i, (T i).expect w = S.expect w := by
      intro w hw i
      rw [← hbar hw]
      have : (fun j => (T j).expect w) = fun _ => (T i).expect w := by
        funext j; rw [Subsingleton.elim j i]
      rw [this, integral_const]; simp
    have : (fun i => (T i).expect A * (T i).expect B) = fun _ => S.expect A * S.expect B := by
      funext i; rw [hconst hA, hconst hB]
    rw [this, integral_const] at hlim
    simpa using hlim
  · intro hc
    have hb : BasisClusters S := fun A B hA hB => hc A B hA hB _ _ flight_basis
    refine ⟨fun i j => Spread.Resolution.eq_of_words R hv T ht fun w hw => ?_⟩
    rw [phase_eq_of_basisClusters P Hs Y R hv T ht hreal hb w hw i,
      phase_eq_of_basisClusters P Hs Y R hv T ht hreal hb w hw j]
end YM.OS.Ground

namespace YM.Spec
open YM.OS.Ground

/-- For OpenAI's construction (`Final`): the phase space of the lattice limit is a single
point exactly when the lattice-limit table clusters on time-separated pairs of words. -/
theorem Final.subsingleton_iff_mixedClusters {G : Gauge} {C : Family G} {f : Extraction.Order}
    {S : Table C.book} (F : Final C f S) :
    Subsingleton F.α.space.X ↔ MixedClusters S :=
  YM.OS.Ground.subsingleton_iff_mixedClusters F.α.unselected F.phase.phase.still F.room.kernel
    F.α.space F.phase.phase.decomposition F.α.ensemble F.phase.phase.chosen
    (fun i => (F.phase.phase.states i).spin)
end YM.Spec


/-! ## The Gelfand bound for the compressed algebra (as `YM.OPE.Cards.pressure`, re-proved here
from `YM.Ground.Spectrum` so that the heavy OPE modules are not needed). -/
namespace YM.OS.Ground
open WeakDual
variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} {A : Spread V}
  {R : A.Resolution}

private lemma pressure_in' {X : Type*} [CommCStarAlgebra X] (u : X) {c : ℝ} (hc : 0 ≤ c) :
    ‖u‖ ≤ c ↔ ∀ p : X →⋆ₐ[ℂ] ℂ, ‖p u‖ ≤ c := by
  have hp : ‖u‖ = ‖gelfandTransform ℂ X u‖ :=
    ((gelfandTransform_isometry X).norm_map_of_map_zero (map_zero _) _).symm
  rw [hp, ContinuousMap.norm_le _ hc]
  refine ⟨fun h p => ?_, fun h i => ?_⟩
  · obtain ⟨x, rfl⟩ := Ground.bij.2 p; exact h _
  exact h (Ground.view i)

theorem pressure' (hi : R.Out) (u : A.algebra) {c : ℝ} (hc : 0 ≤ c) :
    ‖u‖ ≤ c ↔ ∀ i : R.X, ‖R.character i u‖ ≤ c := by
  have ab := hi.abelian
  haveI : IsClosed (A.algebra : Set V.VacuumOp) := isClosed_closure
  letI : CommCStarAlgebra A.algebra := { (StarSubalgebra.cstarAlgebra A.algebra) with mul_comm := ab }
  rw [pressure_in' u hc]
  refine ⟨fun h i => h _, fun h q => ?_⟩
  obtain ⟨i, rfl⟩ := hi.onto.2 q
  exact h _
end YM.OS.Ground

/-! ## Session 2: one phase ⇔ the lattice limit's chamber has a unique vacuum. -/
namespace YM.OS.Ground
open Function Set Filter Word MeasureTheory
open scoped Topology NNReal ComplexConjugate InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)

/-- A probability measure lives on a nonempty space. -/
theorem nonempty_of_out (R : P.Resolution) (hv : R.Out) : Nonempty R.X := by
  have := hv.normalized
  by_contra hn
  rw [not_nonempty_iff] at hn
  have h1 := measure_univ (μ := R.μ)
  rw [Set.univ_eq_empty_iff.2 hn, measure_empty] at h1
  exact zero_ne_one h1

/-- With one character, every element of the compressed algebra is a scalar. -/
theorem scalar_of_subsingleton (R : P.Resolution) (hv : R.Out) [Subsingleton R.X] (i : R.X)
    (u : P.algebra) : u = algebraMap ℂ P.algebra (R.character i u) := by
  have h := (pressure' (R := R) hv (u - algebraMap ℂ P.algebra (R.character i u)) le_rfl).2
    (fun j => by
      rw [Subsingleton.elim j i, map_sub, AlgHomClass.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self, norm_zero])
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

theorem algebraMap_apply_omega (z : ℂ) :
    (algebraMap ℂ P.algebra z).val V.omega0 = z • V.omega0 := by
  change (algebraMap ℂ V.VacuumOp z) V.omega0 = _
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-- One phase gives a unique vacuum in the chamber of the lattice-limit table. -/
theorem uniqueHeat_of_subsingleton (Hs : Steady V) (R : P.Resolution) (hv : R.Out)
    [Subsingleton R.X] : V.UniqueHeat := by
  obtain ⟨i⟩ := nonempty_of_out P R hv
  have hsub : Set.range (fun u : P.algebra => u.val V.omega0) ⊆
      ((ℂ ∙ V.omega0 : Submodule ℂ V.D) : Set V.D) := by
    rintro _ ⟨u, rfl⟩
    dsimp only
    rw [scalar_of_subsingleton P R hv i u, algebraMap_apply_omega]
    exact Submodule.mem_span_singleton.mpr ⟨R.character i u, rfl⟩
  have hclosed : IsClosed ((ℂ ∙ V.omega0 : Submodule ℂ V.D) : Set V.D) :=
    Submodule.closed_of_finiteDimensional _
  intro v
  have hv' : v ∈ (ℂ ∙ V.omega0 : Submodule ℂ V.D) := by
    have := closure_minimal hsub hclosed
    rw [(full P Hs).closure_range] at this
    exact this (Set.mem_univ v)
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hv'
  exact ⟨z, hz⟩

/-- A unique vacuum in the chamber of the lattice-limit table gives one phase. -/
theorem subsingleton_of_uniqueHeat (R : P.Resolution) (hv : R.Out) (hu : V.UniqueHeat) :
    Subsingleton R.X := by
  have := hv.normalized
  have := hv.support
  have key : ∀ (u : P.algebra), ∃ z : ℂ, ∀ x : R.X, R.character x u = z := by
    intro u
    obtain ⟨z, hz⟩ := hu (u.val V.omega0)
    set w : P.algebra := u - algebraMap ℂ P.algebra z with hw
    have hwΩ : w.val V.omega0 = 0 := by
      change (u.val - (algebraMap ℂ P.algebra z).val) V.omega0 = 0
      rw [ContinuousLinearMap.sub_apply, algebraMap_apply_omega, hz, sub_self]
    have hint : ∫ x, R.character x (star w * w) ∂(R.μ) = 0 := by
      rw [hv.ground]
      change inner ℂ V.omega0 ((star w.val * w.val) V.omega0) = 0
      rw [ContinuousLinearMap.mul_apply, hwΩ, map_zero, inner_zero_right]
    have hnn : ∀ x, R.character x (star w * w) = ((‖R.character x w‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [map_mul, map_star, Complex.star_def, Complex.conj_mul']
      norm_cast
    have hreal : ∫ x, ‖R.character x w‖ ^ 2 ∂(R.μ) = 0 := by
      simp only [hnn, integral_complex_ofReal] at hint
      exact_mod_cast hint
    have hcont : Continuous fun x => ‖R.character x w‖ ^ 2 := ((hv.weak w).norm).pow 2
    have hintg : Integrable (fun x => ‖R.character x w‖ ^ 2) R.μ :=
      hcont.integrable_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hintg).1 hreal
    have heq := (Continuous.ae_eq_iff_eq R.μ hcont continuous_const).1 hae
    refine ⟨z, fun x => ?_⟩
    have h0 : ‖R.character x w‖ ^ 2 = 0 := congrFun heq x
    have hw0 : R.character x w = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
    rw [hw, map_sub, AlgHomClass.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_eq_zero] at hw0
    exact hw0
  refine ⟨fun i j => hv.onto.1 ?_⟩
  ext u
  obtain ⟨z, hz⟩ := key u
  rw [hz i, hz j]

/-- One phase ⇔ every heat-invariant vector of the chamber `V` (for OpenAI's construction,
`F.α.room`, the chamber of the lattice-limit table, not the selected phase's `leaps`) is a
multiple of `omega0`. -/
theorem subsingleton_iff_uniqueHeat (Hs : Steady V) (R : P.Resolution) (hv : R.Out) :
    Subsingleton R.X ↔ V.UniqueHeat :=
  ⟨fun h => uniqueHeat_of_subsingleton P Hs R hv, subsingleton_of_uniqueHeat P R hv⟩
end YM.OS.Ground

/-! ## Session 2: the bridge, for any public hierarchy that reads OpenAI's construction the
way `HierarchyBridge.hierarchy` does. -/
namespace YangMills
open YM YM.Spec YM.OS YM.OS.Ground Word Function Filter Set MeasureTheory
open scoped Topology

variable {g : GaugeGroup} {C' : WilsonFamily g} {G : Gauge} {Cf : Family G}
  {p : Extraction.Order} {S : Table Cf.book}

/-- How a public hierarchy reads OpenAI's construction `F`. OpenAI's `hierarchy F Q`
(HierarchyBridge.lean:27-42) has `Character := F.α.space.X`, so `ι` is the identity; `q` is
`quoteTag` and `cl` is `S.classTokens`; the four equations are two `rfl` steps and two
`Table.at_project` steps, as in `publicReconstruction` (HierarchyBridge.lean:79-110). -/
structure Reads (T : Hierarchy C') (F : Final Cf p S) where
  ι : T.Character ≃ F.α.space.X
  q : T.Tag → Cf.book.Token
  cl : Cf.book.Token → T.Tag
  some_read (i : T.Character) {n : ℕ} (a : Fin n → T.Tag) (x : Points n) :
    T.correlation (some i) a x = (F.α.ensemble (ι i)).read x (q ∘ a)
  none_read {n : ℕ} (a : Fin n → T.Tag) (x : Points n) :
    T.correlation none a x = S.read x (q ∘ a)
  some_class (i : T.Character) {n : ℕ} (u : Fin n → Cf.book.Token) (x : Points n) :
    x ∈ WilsonFamily.separated n → T.correlation (some i) (cl ∘ u) x = (F.α.ensemble (ι i)).read x u
  none_class {n : ℕ} (u : Fin n → Cf.book.Token) (x : Points n) :
    x ∈ WilsonFamily.separated n → T.correlation none (cl ∘ u) x = S.read x u

theorem timeUnit_eq : Hierarchy.timeUnit = YM.basis YM.timeAxis := rfl

/-- A realized joint configuration is the first word followed by the second, moved in time. -/
theorem realize_timeSplit {n k : ℕ} (u : Fin n → Cf.book.Token) (v : Fin k → Cf.book.Token)
    (x : Points n) (y : Points k) (t : ℝ) :
    realize (Fin.append u v) (Hierarchy.timeSplit x y t) =
      carry (realize u x) 0 ++ carry (realize v y) (t • basis timeAxis) := by
  have e : (fun i => ((Hierarchy.timeSplit x y t) i, Fin.append u v i)) =
      Fin.append (fun i => (x i, u i)) (fun j => (y j + t • basis timeAxis, v j)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [Hierarchy.timeSplit]
    · simp [Hierarchy.timeSplit, timeUnit_eq]
  simp only [realize, carry, add_zero, List.map_id']
  rw [show (List.ofFn fun i => ((Hierarchy.timeSplit x y t) i, Fin.append u v i)) = _ from
    congrArg List.ofFn e, List.ofFn_fin_append, List.map_ofFn]
  simp [Function.comp_def]

theorem comp_append {α β : Type*} (f : α → β) {n k : ℕ} (a : Fin n → α) (b : Fin k → α) :
    f ∘ Fin.append a b = Fin.append (f ∘ a) (f ∘ b) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

namespace Reads
variable {T : Hierarchy C'} {F : Final Cf p S} (H : Reads T F)
include H

/-- Correlations separate characters. -/
theorem separates : T.Separates := by
  intro i j h
  apply H.ι.injective
  apply YM.OS.Spread.Resolution.eq_of_words F.α.space F.phase.phase.decomposition F.α.ensemble
    F.phase.phase.chosen
  intro w hw
  have hx : positions w ∈ WilsonFamily.separated _ := hw
  have := h _ (H.cl ∘ tokens w) (positions w) hx
  rw [H.some_class i _ _ hx, H.some_class j _ _ hx] at this
  exact this

/-- One point gives rate-free clustering of the public lattice limit. -/
theorem clusters_of_subsingleton (hs : Subsingleton T.Character) : T.Clusters none := by
  have hs' : Subsingleton F.α.space.X := H.ι.symm.subsingleton
  have hM := (Final.subsingleton_iff_mixedClusters F).1 hs'
  intro n k a b x y hx hy
  rw [tendsto_iff_seq_tendsto]
  intro τ hτ
  have hA : distinct (realize (H.q ∘ a) x) := (realized ..).mpr hx
  have hB : distinct (realize (H.q ∘ b) y) := (realized ..).mpr hy
  have hfl : flight (fun _ : ℕ => (0 : E4)) (fun m => τ m • basis timeAxis) := by
    unfold flight
    have : (fun m : ℕ => ((τ m • basis timeAxis) - (0 : E4)) timeAxis) = τ := by
      funext m; simp [basis]
    rw [this]; exact hτ
  have h := hM _ _ hA hB _ _ hfl
  rw [H.none_read, H.none_read, ← Table.readAt, ← Table.readAt]
  refine h.congr fun m => ?_
  simp only [Function.comp_apply]
  rw [H.none_read, comp_append, ← Table.readAt, realize_timeSplit]

/-- Public clustering of the lattice limit gives clustering along the basis flight. -/
theorem basisClusters_of_clusters (hc : T.Clusters none) : BasisClusters S := by
  intro A B hA hB
  have hx : positions A ∈ WilsonFamily.separated _ := hA
  have hy : positions B ∈ WilsonFamily.separated _ := hB
  have h := (hc _ _ (H.cl ∘ tokens A) (H.cl ∘ tokens B) _ _ hx hy).comp
    tendsto_natCast_atTop_atTop
  rw [H.none_class _ _ hx, H.none_class _ _ hy] at h
  refine h.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (Hierarchy.eventually_timeSplit_mem hx hy)]
    with m hm
  simp only [Function.comp_apply]
  rw [← comp_append, H.none_class _ _ hm, ← Table.readAt, realize_timeSplit, rebuilt, rebuilt]

/-- One phase ⇔ rate-free clustering of the lattice limit, given `Reads`, with no further
hypotheses. (`SinglePhase`, `Separates`, `Clusters` are the council's definitions, above.) -/
theorem singlePhase_iff_clusters : T.SinglePhase ↔ T.Clusters none := by
  constructor
  · intro hS
    exact H.clusters_of_subsingleton (Hierarchy.subsingleton_of_singlePhase hS H.separates)
  · intro hc n a x hx i
    have hb := H.basisClusters_of_clusters hc
    have hw : distinct (realize (H.q ∘ a) x) := (realized ..).mpr hx
    have := phase_eq_of_basisClusters F.α.unselected F.phase.phase.still F.room.kernel F.α.space
      F.phase.phase.decomposition F.α.ensemble F.phase.phase.chosen
      (fun i => (F.phase.phase.states i).spin) hb _ hw (H.ι i)
    rw [H.some_read, H.none_read, ← Table.readAt, ← Table.readAt]
    exact this

theorem singlePhase_iff_subsingleton : T.SinglePhase ↔ Subsingleton T.Character :=
  ⟨fun hS => Hierarchy.subsingleton_of_singlePhase hS H.separates,
    fun hs => H.singlePhase_iff_clusters.2 (H.clusters_of_subsingleton hs)⟩

/-- One phase ⇔ the chamber of the lattice-limit table has a unique vacuum. -/
theorem singlePhase_iff_uniqueHeat : T.SinglePhase ↔ F.α.room.UniqueHeat := by
  rw [H.singlePhase_iff_subsingleton, ← subsingleton_iff_uniqueHeat F.α.unselected
    F.phase.phase.still F.α.space F.phase.phase.decomposition]
  exact ⟨fun h => H.ι.symm.subsingleton, fun h => H.ι.subsingleton⟩

theorem singlePhase_iff_diracPhase (hR : T.Reconstructed) : T.SinglePhase ↔ T.DiracPhase :=
  Hierarchy.singlePhase_iff_diracPhase hR H.separates
end Reads
end YangMills

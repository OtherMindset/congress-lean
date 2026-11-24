import LongTable.P_mwuyw6ne_1irnyq

/-! Lorentz covariance of the energy–momentum measure of a public `WightmanTheory`,
and the passage from the Hamiltonian form of the mass gap to the mass-shell form,
conditional on a purely geometric statement about boosts (`BoostsBelow`).

Nothing here is about Yang–Mills in particular: the statements hold for every
`WightmanTheory` satisfying `W0`. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory Set Filter ContinuousLinearMap
open scoped InnerProductSpace

/-- The characteristic function of the image of a measure under an adjoint. -/
theorem charFun_map_adjoint (μ : Measure Spacetime) (A : Spacetime →L[ℝ] Spacetime)
    (t : Spacetime) : charFun (μ.map (adjoint A)) t = charFun μ (A t) := by
  rw [charFun_apply, charFun_apply, integral_map (adjoint A).continuous.aemeasurable]
  · congr 1; ext x; rw [adjoint_inner_left]
  · exact Continuous.aestronglyMeasurable (by fun_prop)

theorem isOpen_energyRegion (m : ℝ) : IsOpen (energyRegion m) :=
  (isOpen_lt continuous_const continuous_time).inter (isOpen_lt continuous_time continuous_const)

/-- The momentum-space action of a Lorentz transformation: the adjoint of its inverse. -/
def ProperLorentz.onMomenta (Λ : ProperLorentz) : Spacetime →L[ℝ] Spacetime :=
  adjoint (Λ.val⁻¹ : (Spacetime →L[ℝ] Spacetime)ˣ).val

theorem ProperLorentz.onMomenta_adjoint (Λ : ProperLorentz) (k : Spacetime) :
    Λ.onMomenta (adjoint Λ.val.val k) = k := by
  have hinv : ∀ y : Spacetime,
      Λ.val.val ((Λ.val⁻¹ : (Spacetime →L[ℝ] Spacetime)ˣ).val y) = y := fun y => by
    have h := Units.mul_inv Λ.val
    exact congrArg (fun f : Spacetime →L[ℝ] Spacetime => f y) h
  refine ext_inner_right ℝ fun y => ?_
  unfold ProperLorentz.onMomenta
  rw [adjoint_inner_left, adjoint_inner_left, hinv]

namespace PoincareAction
variable {H : HilbertSpace} {Labels : FieldLabels} (P : PoincareAction H Labels)

theorem ext_coordinates {g h : P.Symmetry}
    (h1 : (P.coordinates g).1.val = (P.coordinates h).1.val)
    (h2 : (P.coordinates g).2 = (P.coordinates h).2) : g = h :=
  P.coordinates.injective (Prod.ext (Subtype.ext h1) h2)

/-- A symmetry with no translation part moves a translation by `x` to the translation by `Λ x`. -/
theorem mul_pureTranslation (g : P.Symmetry) (hg : (P.coordinates g).2 = 0) (x : Spacetime) :
    g * P.pureTranslation x = P.pureTranslation ((P.coordinates g).1.val.val x) * g := by
  apply P.ext_coordinates
  · rw [(P.productCoordinates _ _).1, (P.productCoordinates _ _).1,
      (P.translationCoordinates _).1, (P.translationCoordinates _).1, mul_one, one_mul]
  · rw [(P.productCoordinates _ _).2, (P.productCoordinates _ _).2,
      (P.translationCoordinates _).2, (P.translationCoordinates _).2,
      (P.translationCoordinates _).1, hg]
    simp

theorem inner_onStates (g : P.Symmetry) (x y : H.carrier) :
    inner ℂ (P.onStates g x) (P.onStates g y) = inner ℂ x y :=
  (LinearIsometry.mk (P.onStates g).toLinearMap (P.unitary g)).inner_map_map x y

end PoincareAction

namespace WightmanTheory
variable {H : HilbertSpace} {Labels : FieldLabels} {theory : WightmanTheory H Labels}

theorem onStates_translation (g : theory.poincare.Symmetry)
    (hg : (theory.poincare.coordinates g).2 = 0) (x : Spacetime) (ψ : H.carrier) :
    theory.poincare.onStates g (theory.translations.operator x ψ) =
      theory.translations.operator ((theory.poincare.coordinates g).1.val.val x)
        (theory.poincare.onStates g ψ) := by
  rw [← theory.translationCompatibility, ← theory.translationCompatibility, ← comp_apply,
    ← comp_apply, ← theory.poincare.composition, ← theory.poincare.composition,
    theory.poincare.mul_pureTranslation g hg]

/-- Lorentz covariance of the diagonal energy–momentum measures. -/
theorem diagonal_map (w0 : theory.W0) (g : theory.poincare.Symmetry)
    (hg : (theory.poincare.coordinates g).2 = 0) (ψ : H.carrier) :
    (theory.energyMomentum.diagonal (theory.poincare.onStates g ψ)).map
        (adjoint (theory.poincare.coordinates g).1.val.val) =
      theory.energyMomentum.diagonal ψ := by
  apply Measure.ext_of_charFun
  ext x
  rw [charFun_map_adjoint, w0.spectralRepresentation, w0.spectralRepresentation,
    ← onStates_translation g hg, theory.poincare.inner_onStates]

/-- A null set of the energy–momentum measure stays null under every proper
orthochronous Lorentz transformation, acting on momenta. -/
theorem projection_lorentz (w0 : theory.W0) (Λ : ProperLorentz) {S : Set Spacetime}
    (hS : MeasurableSet S) (h : theory.energyMomentum.projection S = 0) :
    theory.energyMomentum.projection (Λ.onMomenta ⁻¹' S) = 0 := by
  have hT : MeasurableSet (Λ.onMomenta ⁻¹' S) := Λ.onMomenta.continuous.measurable hS
  refine theory.energyMomentum.projection_eq_zero_of_diagonal hT fun ψ => ?_
  let g : theory.poincare.Symmetry := theory.poincare.coordinates.symm (Λ, 0)
  have hc : theory.poincare.coordinates g = (Λ, 0) := theory.poincare.coordinates.apply_symm_apply _
  have hg : (theory.poincare.coordinates g).2 = 0 := by rw [hc]
  rw [← diagonal_map w0 g hg ψ, Measure.map_apply (adjoint _).continuous.measurable hT, hc]
  have : (adjoint Λ.val.val) ⁻¹' (Λ.onMomenta ⁻¹' S) = S := by
    ext k; simp only [mem_preimage, Λ.onMomenta_adjoint]
  rw [this]
  exact theory.energyMomentum.diagonal_eq_zero_of_projection hS h _

end WightmanTheory

/-- Geometry only: every nonzero energy–momentum in the forward cone below the mass
shell `m` has energy strictly between `0` and `m` in some Lorentz frame. Not proved
here. As mathematics it holds for every `m > 0` (three axis boosts suffice); it is
vacuous at `m = 0` and false for `m < 0`. -/
def BoostsBelow (m : ℝ) : Prop :=
  ∀ k : Spacetime, k ∈ forwardCone → k ≠ 0 → minkowskiSquare k < m ^ 2 →
    ∃ Λ : ProperLorentz, Λ.onMomenta k ∈ energyRegion m

namespace WightmanTheory
variable {H : HilbertSpace} {Labels : FieldLabels} {theory : WightmanTheory H Labels}

/-- Under W0 and the geometric statement `BoostsBelow m`, the Hamiltonian form of
the gap gives the mass-shell form. -/
theorem HasEnergyGap.massGap {m : ℝ} (h : theory.HasEnergyGap m) (w0 : theory.W0)
    (hb : BoostsBelow m) : theory.HasMassGap m := by
  refine ⟨h.1, theory.energyMomentum.projection_eq_zero_of_diagonal (measurableSet_massRegion m)
    fun ψ => ?_⟩
  let s : ProperLorentz → Set Spacetime := fun Λ => Λ.onMomenta ⁻¹' energyRegion m
  have hopen : ∀ Λ, IsOpen (s Λ) := fun Λ => (isOpen_energyRegion m).preimage Λ.onMomenta.continuous
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable s hopen
  have hsub : massRegion m ⊆ (⋃ Λ ∈ T, s Λ) ∪ forwardConeᶜ := by
    intro k hk
    by_cases hc : k ∈ forwardCone
    · left
      rw [hTeq]
      obtain ⟨Λ, hΛ⟩ := hb k hc hk.1 hk.2
      exact mem_iUnion.mpr ⟨Λ, hΛ⟩
    · exact Or.inr hc
  have h1 : theory.energyMomentum.diagonal ψ (⋃ Λ ∈ T, s Λ) = 0 := by
    rw [measure_biUnion_null_iff hT]
    intro Λ _
    exact theory.energyMomentum.diagonal_eq_zero_of_projection
      (Λ.onMomenta.continuous.measurable (measurableSet_energyRegion m))
      (projection_lorentz w0 Λ (measurableSet_energyRegion m) h.2) ψ
  have h2 : theory.energyMomentum.diagonal ψ forwardConeᶜ = 0 :=
    theory.energyMomentum.diagonal_eq_zero_of_projection isClosed_forwardCone.measurableSet.compl
      w0.positiveEnergy ψ
  have := (measure_mono (μ := theory.energyMomentum.diagonal ψ) hsub).trans (measure_union_le _ _)
  rw [h1, h2, add_zero] at this
  exact le_antisymm this bot_le

end WightmanTheory
end YangMills

import Check.DimFourTrace
import YM.Independent.Core
import YM.Integration.ManuscriptTraceTests

/-! Council, 25-26 November 2026 (session 6, agent "trace"). Discharges the hypothesis of
`DimFour.trace_marker`: in OpenAI's construction the stress trace `∑ᵢ Tᵢᵢ` is NOT a multiple of the
unit in `S.Field 4`.

Route (uses only `Core.trace : ManuscriptTraceTests.Tests F hG`, i.e. OpenAI's own trace tests).
If `stressTrace = t • unit`, then the centered trace `center F = stressTrace − ⟨stressTrace⟩ • unit`
is `t • unit − t • unit = 0` (`vev_linear`, `vev_unit`), so the Euclidean two-point function
`euclidean F r = useAt … (fun _ => ⟨4, center F⟩)` is a multilinear map evaluated at a zero argument,
hence `0` for every `r`. Then `Tests.shortDistance`
(`s^8 (log s⁻¹)^2 • euclidean F s → award G` as `s → 0⁺`) forces `award G = 0`, contradicting
`Tests.positive : 0 < award G`.

Nothing from OpenAI's library is copied; everything is used through imports of built modules
(`YM.TraceExtension.Centered`, `.WilsonTrace`, `.LogScaling`, `YM.Integration.ManuscriptTraceTests`,
`YM.Independent.Core`: all in HierarchyBridge's closure). -/
set_option autoImplicit false
noncomputable section
namespace YM.Independent.TraceUnit
open Filter MeasureTheory OPE OPE.Orbits
open scoped Topology BigOperators

universe u v

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- If the stress trace is a multiple of the unit, the centered trace vanishes. -/
lemma center_eq_zero_of_scalar (F : Spec.Final C f S) (t : ℂ)
    (ht : TraceExtension.stressTrace F.sector.energy = t • S.unit 4) :
    TraceExtension.center F = 0 := by
  have h1 : TraceExtension.euclideanVEV S (TraceExtension.selected F) (t • S.unit 4) =
      t • TraceExtension.euclideanVEV S (TraceExtension.selected F) (S.unit 4) :=
    (TraceExtension.vev_linear (S := S) (T := TraceExtension.selected F) (d := 4)).map_smul t
      (S.unit 4)
  have h2 : TraceExtension.euclideanVEV S (TraceExtension.selected F) (S.unit 4) = 1 :=
    TraceExtension.vev_unit (TraceExtension.selected_respects F)
      (TraceExtension.selected_hierarchy F) 4
  have hv : TraceExtension.euclideanVEV S (TraceExtension.selected F) (t • S.unit 4) = t := by
    rw [h1, h2, smul_eq_mul, mul_one]
  have hc : TraceExtension.center F = TraceExtension.stressTrace F.sector.energy -
      TraceExtension.euclideanVEV S (TraceExtension.selected F)
        (TraceExtension.stressTrace F.sector.energy) • S.unit 4 := by
    first
      | rfl
      | (unfold TraceExtension.center TraceExtension.theta TraceExtension.centerIn; rfl)
  rw [hc, ht, hv, sub_self]

/-- A vanishing centered trace has vanishing Euclidean two-point function at every separation. -/
lemma euclidean_eq_zero (F : Spec.Final C f S) (hc : TraceExtension.center F = 0) (r : ℝ) :
    TraceExtension.euclidean F r = 0 := by
  have e : TraceExtension.euclidean F r =
      S.useAt (TraceExtension.selected F) (TraceExtension.opposed r)
        (fun _ : Fin 2 => (⟨4, TraceExtension.center F⟩ : S.Tag)) := rfl
  rw [e, hc]
  show S.classMoment (TraceExtension.selected F) (fun _ : Fin 2 => 4) (TraceExtension.opposed r)
      (fun _ : Fin 2 => (0 : S.Field 4)) = 0
  first
    | exact (S.classMoment (TraceExtension.selected F) (fun _ : Fin 2 => 4)
        (TraceExtension.opposed r)).map_coord_zero (0 : Fin 2) rfl
    | exact MultilinearMap.map_coord_zero _ (0 : Fin 2) rfl
    | exact (S.classMoment (TraceExtension.selected F) (fun _ : Fin 2 => 4)
        (TraceExtension.opposed r)).map_zero

/-- With a vanishing centered trace, a short-distance coefficient `A` must be `0`. -/
lemma asymptotic_zero (F : Spec.Final C f S) (hc : TraceExtension.center F = 0) (A : ℝ)
    (hA : TraceExtension.EuclideanAsymptotic F A) : A = 0 := by
  have hT : Tendsto (fun s : ℝ => ((s ^ 8 * (Real.log s⁻¹) ^ 2 : ℝ)) • TraceExtension.euclidean F s)
      (𝓝[>] 0) (𝓝 (A : ℂ)) := hA
  have hf : (fun s : ℝ => ((s ^ 8 * (Real.log s⁻¹) ^ 2 : ℝ)) • TraceExtension.euclidean F s) =
      fun _ : ℝ => (0 : ℂ) := by
    funext s
    rw [euclidean_eq_zero F hc s, smul_zero]
  rw [hf] at hT
  have h0 : (A : ℂ) = 0 := tendsto_nhds_unique hT tendsto_const_nhds
  exact Complex.ofReal_eq_zero.mp h0

/-- **The stress trace is not a multiple of the unit** (the hypothesis `hθ` of
`DimFour.trace_marker`), for any `Final` carrying OpenAI's `Core` package. -/
theorem stressTrace_ne_smul_unit {hG : G.Simple} {F : Spec.Final C f S}
    {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q) :
    ∀ t : ℂ, TraceExtension.stressTrace F.sector.energy ≠ t • S.unit 4 := by
  intro t ht
  have hc : TraceExtension.center F = 0 := center_eq_zero_of_scalar F t ht
  have hpos := H.trace.positive
  have hz := asymptotic_zero F hc _ H.trace.shortDistance
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

/-- Same, from the trace tests alone. -/
theorem stressTrace_ne_smul_unit_of_tests {hG : G.Simple} {F : Spec.Final C f S}
    (H : Integration.ManuscriptTraceTests.Tests.{u,v} F hG) :
    ∀ t : ℂ, TraceExtension.stressTrace F.sector.energy ≠ t • S.unit 4 := by
  intro t ht
  have hc : TraceExtension.center F = 0 := center_eq_zero_of_scalar F t ht
  have hpos := H.positive
  have hz := asymptotic_zero F hc _ H.shortDistance
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

/-- **The one number is the trace condensate, unconditionally** (given OpenAI's `Core`): in every
viewer (lattice limit or phase), at every point, every dimension-four one-point value is
`c z + κ z * ⟨T^μ_μ⟩_s` with `c`, `κ` independent of the viewer. -/
theorem trace_marker_unconditional {hG : G.Simple} {F : Spec.Final C f S}
    {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q) :
    ∃ c κ : S.Field 4 → ℂ, ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      DimFour.onePoint F s o z =
        c z + κ z * DimFour.onePoint F s o (TraceExtension.stressTrace F.sector.energy) :=
  DimFour.trace_marker F hG (stressTrace_ne_smul_unit H)

end YM.Independent.TraceUnit

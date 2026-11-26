import Check.DimFour
import YM.TraceExtension.Centered
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Council, 25 November 2026 (session 5, optional second file; `Check.DimFour` does not depend on
it). The one number of `DimFour.one_number` can be taken to be the one-point value of ANY
dimension-four field that is invariant under the signed permutations of the axes and is not a
multiple of the unit; in particular the stress trace, PROVIDED it is not a multiple of the unit
(that proviso is a hypothesis here, not proved).

Method: averaging a functional over the 384 signed permutations gives an invariant functional, so
invariant functionals separate invariant vectors (`invariant_sep`); with `invariant_two_S` this makes
the invariant vectors of `S.Field 4` at most two-dimensional, spanned by the unit and `θ`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Independent.DimFour
open Filter MeasureTheory OPE OPE.Orbits
open scoped Topology BigOperators

section Marker
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- The sum of a functional over all signed permutations of the axes. -/
def averaged (H : S.RealSpin) (χ : S.Field 4 →ₗ[ℂ] ℂ) : S.Field 4 →ₗ[ℂ] ℂ :=
  ∑ k : Signed, χ.comp (S.mirror H 4 k)

lemma averaged_apply (H : S.RealSpin) (χ : S.Field 4 →ₗ[ℂ] ℂ) (z : S.Field 4) :
    averaged H χ z = ∑ k : Signed, χ (S.mirror H 4 k z) := by
  unfold averaged
  first
    | simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    | (rw [LinearMap.sum_apply]; rfl)
    | rw [LinearMap.sum_apply]

lemma averaged_inv (H : S.RealSpin) (χ : S.Field 4 →ₗ[ℂ] ℂ) (j : Signed) (z : S.Field 4) :
    averaged H χ (S.mirror H 4 j z) = averaged H χ z := by
  have e1 : averaged H χ (S.mirror H 4 j z) =
      ∑ k : Signed, χ (S.mirror H 4 k (S.mirror H 4 j z)) := averaged_apply H χ (S.mirror H 4 j z)
  have e2 : averaged H χ z = ∑ k : Signed, χ (S.mirror H 4 k z) := averaged_apply H χ z
  have e3 : (∑ k : Signed, χ (S.mirror H 4 k (S.mirror H 4 j z))) =
      ∑ k : Signed, χ (S.mirror H 4 k z) :=
    Fintype.sum_equiv (Equiv.mulRight j)
      (fun k : Signed => χ (S.mirror H 4 k (S.mirror H 4 j z)))
      (fun k : Signed => χ (S.mirror H 4 k z))
      (fun k => by
        show χ (S.mirror H 4 k (S.mirror H 4 j z)) = χ (S.mirror H 4 (k * j) z)
        rw [S.mirror_mul H 4 k j z])
  exact e1.trans (e3.trans e2.symm)

/-- Invariant functionals separate invariant vectors. -/
lemma invariant_sep (H : S.RealSpin) (y : S.Field 4)
    (hy : ∀ k : Signed, S.mirror H 4 k y = y)
    (h0 : ∀ φ : S.Field 4 →ₗ[ℂ] ℂ,
      (∀ (k : Signed) (z : S.Field 4), φ (S.mirror H 4 k z) = φ z) → φ y = 0) :
    y = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℂ y).mp
  intro χ
  have h1 : averaged H χ y = 0 := h0 (averaged H χ) (fun k z => averaged_inv H χ k z)
  rw [averaged_apply] at h1
  have h2 : (∑ k : Signed, χ (S.mirror H 4 k y)) = ∑ _k : Signed, χ y :=
    Finset.sum_congr rfl (fun k _ => by rw [hy k])
  rw [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  have hN : ((Fintype.card Signed : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp h1).resolve_left hN

/-- Algebra: with a reference vector `θ` independent of `one`, both numbers are solved for. -/
lemma affine_reduce_at {ι V : Type*} (ω : ι → V → ℂ) (a b : V → ℂ) (u w one θ : V)
    (hexp : ∀ (s : ι) (z : V), ω s z = a z * ω s u + b z * ω s w)
    (hone : ∀ s : ι, ω s one = 1)
    (hdet : a one * b θ - a θ * b one ≠ 0) :
    ∃ c κ : V → ℂ, ∀ (s : ι) (z : V), ω s z = c z + κ z * ω s θ := by
  refine ⟨fun z => (a z * b θ - b z * a θ) * (a one * b θ - a θ * b one)⁻¹,
    fun z => (b z * a one - a z * b one) * (a one * b θ - a θ * b one)⁻¹, fun s z => ?_⟩
  show ω s z = (a z * b θ - b z * a θ) * (a one * b θ - a θ * b one)⁻¹ +
    (b z * a one - a z * b one) * (a one * b θ - a θ * b one)⁻¹ * ω s θ
  have h1 := hexp s one
  rw [hone s] at h1
  have hθ := hexp s θ
  have hz := hexp s z
  have key : ω s z * (a one * b θ - a θ * b one) =
      (a z * b θ - b z * a θ) + (b z * a one - a z * b one) * ω s θ := by
    rw [hz, hθ]
    linear_combination (-(a z * b θ - b z * a θ)) * h1
  have hinvD : (a one * b θ - a θ * b one) * (a one * b θ - a θ * b one)⁻¹ = 1 :=
    mul_inv_cancel₀ hdet
  calc ω s z = ω s z * ((a one * b θ - a θ * b one) * (a one * b θ - a θ * b one)⁻¹) := by
        rw [hinvD, mul_one]
    _ = (ω s z * (a one * b θ - a θ * b one)) * (a one * b θ - a θ * b one)⁻¹ := by ring
    _ = ((a z * b θ - b z * a θ) + (b z * a one - a z * b one) * ω s θ) *
          (a one * b θ - a θ * b one)⁻¹ := by rw [key]
    _ = (a z * b θ - b z * a θ) * (a one * b θ - a θ * b one)⁻¹ +
          (b z * a one - a z * b one) * (a one * b θ - a θ * b one)⁻¹ * ω s θ := by ring

/-- **Any invariant non-unit field is a complete marker at dimension four.** If `θ : S.Field 4` is
invariant under the signed permutations of the axes and is not a multiple of the unit, then in every
viewer the one-point value of every dimension-four field is `c z + κ z * ⟨θ⟩_s` with `c`, `κ`
independent of the viewer. -/
theorem marker_of_invariant (F : Spec.Final C f S) (hG : G.Simple) (θ : S.Field 4)
    (hinv : ∀ k : Signed, S.mirror F.room.kernel.spin 4 k θ = θ)
    (hθ : ∀ t : ℂ, θ ≠ t • S.unit 4) :
    ∃ c κ : S.Field 4 → ℂ, ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o θ := by
  obtain ⟨u, w, a, b, h⟩ := invariant_two_S F hG
  have hdet : a (S.unit 4) * b θ - a θ * b (S.unit 4) ≠ 0 := by
    intro hd
    have hy1 : a (S.unit 4) • θ - a θ • S.unit 4 = 0 := by
      refine invariant_sep F.room.kernel.spin _ (fun k => ?_) (fun φ hφ => ?_)
      · rw [map_sub, map_smul, map_smul, hinv k, S.mirror_unit F.room.kernel.spin 4 k]
      · rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h φ hφ θ, h φ hφ (S.unit 4)]
        linear_combination (φ w) * hd
    have hy2 : b (S.unit 4) • θ - b θ • S.unit 4 = 0 := by
      refine invariant_sep F.room.kernel.spin _ (fun k => ?_) (fun φ hφ => ?_)
      · rw [map_sub, map_smul, map_smul, hinv k, S.mirror_unit F.room.kernel.spin 4 k]
      · rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h φ hφ θ, h φ hφ (S.unit 4)]
        linear_combination (-(φ u)) * hd
    have e1 : a (S.unit 4) • θ = a θ • S.unit 4 := sub_eq_zero.mp hy1
    have e2 : b (S.unit 4) • θ = b θ • S.unit 4 := sub_eq_zero.mp hy2
    by_cases ha : a (S.unit 4) = 0
    · by_cases hb : b (S.unit 4) = 0
      · have hu0 : S.unit 4 = 0 := by
          refine invariant_sep F.room.kernel.spin _
            (fun k => S.mirror_unit F.room.kernel.spin 4 k) (fun φ hφ => ?_)
          rw [h φ hφ (S.unit 4), ha, hb, zero_mul, zero_mul, add_zero]
        exact S.alive 4 F.room.kernel.laws hu0
      · apply hθ ((b (S.unit 4))⁻¹ * b θ)
        calc θ = (b (S.unit 4))⁻¹ • (b (S.unit 4) • θ) := by
              rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = ((b (S.unit 4))⁻¹ * b θ) • S.unit 4 := by rw [e2, smul_smul]
    · apply hθ ((a (S.unit 4))⁻¹ * a θ)
      calc θ = (a (S.unit 4))⁻¹ • (a (S.unit 4) • θ) := by
            rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = ((a (S.unit 4))⁻¹ * a θ) • S.unit 4 := by rw [e1, smul_smul]
  obtain ⟨c, κ, h2⟩ := affine_reduce_at (ι := Viewers F × E4) (V := S.Field 4)
    (fun (p : Viewers F × E4) (z : S.Field 4) => onePoint F p.1 p.2 z) a b u w (S.unit 4) θ
    (fun p z => h (onePoint F p.1 p.2) (fun k y => onePoint_mirror F p.1 p.2 k y) z)
    (fun p => onePoint_unit F p.1 p.2) hdet
  exact ⟨c, κ, fun s o z => h2 (s, o) z⟩

/-- The stress trace is invariant under the signed permutations of the axes. -/
theorem stressTrace_mirror (F : Spec.Final C f S) (k : Signed) :
    S.mirror F.room.kernel.spin 4 k (TraceExtension.stressTrace F.sector.energy) =
      TraceExtension.stressTrace F.sector.energy := by
  rw [← F.phase.transport.spots.signed 4 k (TraceExtension.stressTrace F.sector.energy)]
  exact TraceExtension.stressTrace_turn F.phase.transport.spin k.ortho

/-- **The one number is the trace condensate**, provided the stress trace is not a multiple of the
unit (hypothesis `hθ`): in every viewer, every dimension-four one-point value is
`c z + κ z * ⟨T^μ_μ⟩_s` with viewer-independent `c`, `κ`. -/
theorem trace_marker (F : Spec.Final C f S) (hG : G.Simple)
    (hθ : ∀ t : ℂ, TraceExtension.stressTrace F.sector.energy ≠ t • S.unit 4) :
    ∃ c κ : S.Field 4 → ℂ, ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o (TraceExtension.stressTrace F.sector.energy) :=
  marker_of_invariant F hG (TraceExtension.stressTrace F.sector.energy)
    (fun k => stressTrace_mirror F k) hθ

end Marker
end YM.Independent.DimFour

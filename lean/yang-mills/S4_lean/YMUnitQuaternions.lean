import Mathlib

/-!
# The unit quaternions as a compact group, and their Haar measure

For the Long Table Yang–Mills foundation posts, which identify SU(2) with the unit sphere S³ ⊂ ℝ⁴
by [[a, b], [-conj b, conj a]] ↦ (Re a, Im a, Re b, Im b). Under ℝ⁴ ≅ ℍ, (x₀, x₁, x₂, x₃) ↦
x₀ + x₁ i + x₂ j + x₃ k, the matrix product becomes the quaternion product, so SU(2) is the group of
unit quaternions. That identification is NOT formalized here (Mathlib has no compact-group
instances for the matrix group SU(2)); this file states the facts for the unit quaternions.
The first part repeats, unchanged, four statements of `YMTextbook.lean` so that this file stands
alone. Nothing here is about lattice gauge theory.
-/

open MeasureTheory Topology Filter Set Metric
open scoped Pointwise Quaternion

namespace YMUnitQuaternions

/-- On a compact topological group, a left-invariant probability measure equals any Haar
probability measure. -/
theorem haar_left_invariant_probability {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [μ.IsHaarMeasure] [μ'.IsMulLeftInvariant] : μ' = μ := by
  have : μ'.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior μ' univ isCompact_univ
      (by simp) (by simp) (by simp)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ' μ

/-- The restriction of a linear isometry of `E` to the unit sphere. -/
def sphereMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 → sphere (0 : E) 1 :=
  fun x => ⟨g x, by
    have hx : ‖(x : E)‖ = 1 := by simp
    simp [hx]⟩

theorem sphereMap_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E ≃ₗᵢ[ℝ] E)
    (x : sphere (0 : E) 1) : ((sphereMap g x : sphere (0 : E) 1) : E) = g x := rfl

/-- Orthogonal invariance of surface measure: for a finite-dimensional real inner product space
`E` with Lebesgue measure `volume`, the surface measure `volume.toSphere` on the unit sphere is
invariant under every linear isometry `g` of `E`. -/
theorem sphere_measure_invariant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (g : E ≃ₗᵢ[ℝ] E)
    (s : Set (sphere (0 : E) 1)) (hs : MeasurableSet s) :
    (volume : Measure E).toSphere (sphereMap g ⁻¹' s) = (volume : Measure E).toSphere s := by
  have hcont : Continuous (sphereMap g) :=
    Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _
  have hmeas : Measurable (sphereMap g) := hcont.measurable
  rw [Measure.toSphere_apply' _ (hmeas hs), Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap g ⁻¹' s) : Set E)
      = g ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
    ext x
    simp only [Set.mem_smul, mem_image, mem_preimage]
    constructor
    · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨r, hr, _, ⟨sphereMap g y, hy, rfl⟩, by simp [sphereMap_coe]⟩
    · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, hx⟩
      refine ⟨r, hr, _, ⟨sphereMap g.symm z, ?_, rfl⟩, ?_⟩
      · have : sphereMap g (sphereMap g.symm z) = z := by
          ext; simp [sphereMap_coe]
        simpa [this] using hz
      · have : g (r • ((sphereMap g.symm z : sphere (0 : E) 1) : E)) = g x := by
          simp [sphereMap_coe, hx]
        exact g.injective this
  rw [hset]
  have hmp : MeasurePreserving (g.toHomeomorph.toMeasurableEquiv) (volume : Measure E) volume :=
    g.measurePreserving
  exact hmp.measure_preimage_equiv _

/-- The same in pushforward form, with the change of variables it gives: the image of the surface
measure under the restriction of `g` is the surface measure, and `∫ f (g x) dσ(x) = ∫ f dσ` for
every strongly measurable `f`. -/
theorem sphere_measure_map {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (g : E ≃ₗᵢ[ℝ] E) :
    ((volume : Measure E).toSphere).map (sphereMap g) = (volume : Measure E).toSphere ∧
      ∀ f : sphere (0 : E) 1 → ℝ, StronglyMeasurable f →
        ∫ x, f (sphereMap g x) ∂(volume : Measure E).toSphere
          = ∫ x, f x ∂(volume : Measure E).toSphere := by
  have hcont : Continuous (sphereMap g) :=
    Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) _
  have hmeas : Measurable (sphereMap g) := hcont.measurable
  have hmap : ((volume : Measure E).toSphere).map (sphereMap g) = (volume : Measure E).toSphere :=
    Measure.ext fun s hs => by
      rw [Measure.map_apply hmeas hs]
      exact sphere_measure_invariant g s hs
  refine ⟨hmap, fun f hf => ?_⟩
  conv_rhs => rw [← hmap]
  exact (integral_map hmeas.aemeasurable hf.aestronglyMeasurable).symm

/-- The unit quaternions, with quaternion multiplication and the subspace topology, form a
compact topological group. -/
theorem unit_quaternions_compact_group :
    CompactSpace (sphere (0 : ℍ[ℝ]) 1) ∧ IsTopologicalGroup (sphere (0 : ℍ[ℝ]) 1) :=
  ⟨inferInstance, inferInstance⟩

/-- Left multiplication by a unit quaternion, as a linear isometry of ℍ. -/
noncomputable def leftMul (a : sphere (0 : ℍ[ℝ]) 1) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun x := (a : ℍ[ℝ]) * x
  invFun x := ((a⁻¹ : sphere (0 : ℍ[ℝ]) 1) : ℍ[ℝ]) * x
  map_add' x y := mul_add _ x y
  map_smul' c x := by simp
  left_inv x := by
    have h : ((a⁻¹ : sphere (0 : ℍ[ℝ]) 1) : ℍ[ℝ]) * (a : ℍ[ℝ]) = 1 :=
      congrArg Subtype.val (inv_mul_cancel a)
    show ((a⁻¹ : sphere (0 : ℍ[ℝ]) 1) : ℍ[ℝ]) * ((a : ℍ[ℝ]) * x) = x
    rw [← mul_assoc, h, one_mul]
  right_inv x := by
    have h : (a : ℍ[ℝ]) * ((a⁻¹ : sphere (0 : ℍ[ℝ]) 1) : ℍ[ℝ]) = 1 :=
      congrArg Subtype.val (mul_inv_cancel a)
    show (a : ℍ[ℝ]) * (((a⁻¹ : sphere (0 : ℍ[ℝ]) 1) : ℍ[ℝ]) * x) = x
    rw [← mul_assoc, h, one_mul]
  norm_map' x := by
    have ha : ‖(a : ℍ[ℝ])‖ = 1 := by simp
    show ‖(a : ℍ[ℝ]) * x‖ = ‖x‖
    rw [norm_mul, ha, one_mul]

theorem sphereMap_leftMul (a x : sphere (0 : ℍ[ℝ]) 1) : sphereMap (leftMul a) x = a * x :=
  Subtype.ext rfl

/-- The surface measure on the unit quaternions is invariant under left multiplication. -/
theorem surface_measure_left_invariant [MeasurableSpace ℍ[ℝ]] [BorelSpace ℍ[ℝ]]
    (a : sphere (0 : ℍ[ℝ]) 1) :
    ((volume : Measure ℍ[ℝ]).toSphere).map (fun x => a * x) = (volume : Measure ℍ[ℝ]).toSphere := by
  have h := (sphere_measure_map (leftMul a)).1
  have hfun : sphereMap (leftMul a) = fun x => a * x := funext (sphereMap_leftMul a)
  rw [hfun] at h
  exact h

/-- On a compact topological group, two left-invariant probability measures are equal. -/
theorem left_invariant_probability_unique {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [μ.IsMulLeftInvariant] [μ'.IsMulLeftInvariant] : μ' = μ := by
  have : μ.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior μ univ isCompact_univ
      (by simp) (by simp) (by simp)
  exact haar_left_invariant_probability μ μ'

/-- Haar measure on the unit quaternions: every left-invariant Borel probability measure on the
unit quaternions equals the normalized surface measure `σ / σ(S³)`, `σ = volume.toSphere`. -/
theorem unit_quaternions_haar [MeasurableSpace ℍ[ℝ]] [BorelSpace ℍ[ℝ]]
    (μ : Measure (sphere (0 : ℍ[ℝ]) 1)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    μ = ((volume : Measure ℍ[ℝ]).toSphere univ)⁻¹ • (volume : Measure ℍ[ℝ]).toSphere := by
  set σ := (volume : Measure ℍ[ℝ]).toSphere with hσ
  have h0 : σ univ ≠ 0 := by
    rw [hσ, Measure.toSphere_apply_univ]
    have : (volume : Measure ℍ[ℝ]) (ball 0 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
    simp [this, Module.finrank_pos.ne']
  have htop : σ univ ≠ ⊤ := measure_ne_top σ univ
  have hprob : IsProbabilityMeasure ((σ univ)⁻¹ • σ) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]⟩
  have hinv : ((σ univ)⁻¹ • σ).IsMulLeftInvariant :=
    ⟨fun a => by
      rw [Measure.map_smul]
      · exact congrArg _ (surface_measure_left_invariant a)
      · exact (continuous_const.mul continuous_id).measurable.aemeasurable⟩
  exact left_invariant_probability_unique ((σ univ)⁻¹ • σ) μ

end YMUnitQuaternions

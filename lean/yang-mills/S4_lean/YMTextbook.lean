import Mathlib

/-!
# Textbook facts used as inputs by the Long Table Yang–Mills foundation posts

Each theorem below restates a standard fact in the form the posts use it and proves it from
Mathlib. Nothing here is about lattice gauge theory; the file only fixes the statements.
-/

open MeasureTheory Topology Filter Set Metric
open scoped BoundedContinuousFunction ENNReal Pointwise

namespace YMTextbook

/-- Tychonoff: a product of compact spaces (any index set) is compact. -/
theorem tychonoff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i) :=
  inferInstance

/-- On a compact metrizable space every sequence of Borel probability measures has a subsequence
that converges weakly: the integrals of every bounded continuous function converge. -/
theorem prob_measures_subseq {E : Type*} [TopologicalSpace E] [CompactSpace E]
    [TopologicalSpace.MetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) :
    ∃ ν : ProbabilityMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ (φ n) : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(ν : Measure E))) := by
  obtain ⟨ν, φ, hφ, h⟩ := CompactSpace.tendsto_subseq μ
  exact ⟨ν, φ, hφ, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h⟩

/-- The same for a countable product `ι → S` of copies of a compact metric space `S`, with the
product topology and its Borel σ-algebra (the configuration space of a lattice model). -/
theorem prob_measures_subseq_product {ι S : Type*} [Countable ι] [MetricSpace S] [CompactSpace S]
    [MeasurableSpace (ι → S)] [BorelSpace (ι → S)] (μ : ℕ → ProbabilityMeasure (ι → S)) :
    ∃ ν : ProbabilityMeasure (ι → S), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ f : (ι → S) →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ (φ n) : Measure (ι → S))) atTop
        (𝓝 (∫ x, f x ∂(ν : Measure (ι → S)))) :=
  prob_measures_subseq μ

/-- Fubini: the integral of an integrable function over a product measure is the iterated
integral, in either order. -/
theorem fubini {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite μ] [SFinite ν] (f : α × β → ℝ) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ ∧
      ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν :=
  ⟨integral_prod f hf, integral_prod_symm f hf⟩

/-- The measurability half of Fubini's theorem: if `f` is strongly measurable on the product,
then `x ↦ ∫ f (x, y) dν(y)` is strongly measurable. -/
theorem fubini_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ν : Measure β)
    [SFinite ν] (f : α × β → ℝ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) :=
  hf.integral_prod_right'

/-- Monotone convergence: for an increasing sequence of measurable functions with values in
`[0, ∞]`, the integral of the supremum is the supremum of the integrals. -/
theorem monotone_convergence {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iSup hf hmono

/-- Dominated convergence: if `F n → f` almost everywhere and `|F n| ≤ bound` almost everywhere
with `bound` integrable, then the integrals converge. -/
theorem dominated_convergence {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ) (f : α → ℝ) (bound : α → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) μ) (hbound_int : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hbound_int hbound hlim

/-- Differentiation under the integral sign: if `x ↦ F x a` is differentiable on a neighbourhood
`s` of `x₀` for almost every `a`, with derivative bounded on `s` by an integrable function, then
`x ↦ ∫ F x a` is differentiable at `x₀` and its derivative is the integral of the derivative. -/
theorem deriv_under_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F F' : ℝ → α → ℝ) (bound : α → ℝ) (x₀ : ℝ) (s : Set ℝ) (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (fun y => F y a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff

/-- π–λ theorem in the form used for measures: two finite measures that agree on a π-system
generating the σ-algebra, and on the whole space, are equal. -/
theorem pi_lambda_measures {α : Type*} [m0 : MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (C : Set (Set α)) (hgen : m0 = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (hC : ∀ s ∈ C, μ s = ν s) (huniv : μ univ = ν univ) : μ = ν :=
  ext_of_generate_finite C hgen hpi hC huniv

/-- The Borel σ-algebra of a topological space is generated by its closed sets (the π-system
used with the π–λ theorem). -/
theorem borel_generated_by_closed (α : Type*) [TopologicalSpace α] :
    borel α = MeasurableSpace.generateFrom {s : Set α | IsClosed s} :=
  borel_eq_generateFrom_isClosed

/-- Uniqueness of normalized Haar measure: on a compact topological group, two Haar measures
that are probability measures are equal. -/
theorem haar_probability_unique {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [μ.IsHaarMeasure] [μ'.IsHaarMeasure] : μ' = μ :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ' μ

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

end YMTextbook

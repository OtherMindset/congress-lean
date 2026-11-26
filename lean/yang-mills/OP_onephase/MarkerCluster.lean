import Check.S2Bridge
import Check.DimFour

/-! Council, 25-26 November 2026 (session 6, agent "trace"). Avenue B, the cheap equivalence, for ONE
observable. For any distinct word `A` (in particular the one-point word of a dimension-four field
`w`, e.g. the marker of `DimFour.one_number` or the stress trace), the following are equivalent:
(a) every phase gives `A` the lattice-limit value; (b) `μ`-almost every phase does;
(c) the lattice-limit two-point function `⟨Ā(f n) A(g n)⟩` clusters (rate-free) along every flight
(time separation → ∞); (d) it clusters along the single flight `g n = n • e_time`.

Route: `barycenter` (YM/Phase/Mixture.lean) gives `∫ ⟨A⟩_i dμ = ⟨A⟩`; `mixed_two_cluster`
(council S2Bridge) gives the flight limit `∫ ⟨Ā⟩_i ⟨A⟩_i dμ`; reality of each phase turns it into
`∫ |⟨A⟩_i|² dμ`; so (c)/(d) say the phase variance of `⟨A⟩_i` is zero, and `const_of_variance`
(S2Bridge; continuity from `Out.weak`, full support from `Out.support`) gives (a).
(b) ⇒ (a): continuous functions equal a.e. for a full-support measure are equal.
These are the steps of `phase_eq_of_basisClusters` (S2Bridge) restricted to one word.

Hypotheses for OpenAI's `F` are exactly those of `Final.subsingleton_iff_mixedClusters`:
`Out = F.phase.phase.decomposition`, `receives = F.phase.phase.chosen`,
`Steady = F.phase.phase.still`, `S.Hierarchy = F.room.kernel` (so `Homogeneous = .translations`),
reality `= (F.phase.phase.states i).spin`. Nothing from OpenAI's library is copied. -/
set_option autoImplicit false
noncomputable section

namespace YM.OS.Ground.Marker
open Function Set Filter Word MeasureTheory
open scoped Topology NNReal ComplexConjugate

variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)

/-- Rate-free clustering of the table `S` on one ordered pair of words, along every flight. -/
def PairClusters (S : Table L) (A B : L.Word) : Prop :=
  ∀ f g : ℕ → E4, flight f g →
    Tendsto (fun n => S.expect (carry A (f n) ++ carry B (g n))) atTop
      (𝓝 (S.expect A * S.expect B))

/-- Rate-free clustering of `S` on one ordered pair of words along the basis flight. -/
def PairBasisClusters (S : Table L) (A B : L.Word) : Prop :=
  Tendsto (fun n : ℕ => S.expect (carry A 0 ++ carry B ((n : ℝ) • basis timeAxis))) atTop
    (𝓝 (S.expect A * S.expect B))

/-- (d) ⇒ (a). The proof of `phase_eq_of_basisClusters` (S2Bridge) for one word. -/
theorem const_of_pairBasis (Hs : Steady V) (Y : S.Hierarchy) (R : P.Resolution)
    (hv : R.Out) (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    (hreal : ∀ i, (T i).RealSpin) (A : L.Word) (hA : distinct A)
    (hc : PairBasisClusters S (conjugate A) A) :
    ∀ i, (T i).expect A = S.expect A := by
  have := hv.normalized
  have := hv.support
  have hA' := distinct_conjugate hA
  obtain ⟨-, hlim⟩ := mixed_two_cluster P Hs Y R hv T ht (conjugate A) A hA' hA _ _ flight_basis
  have h2 : Tendsto (fun n : ℕ => S.expect (carry (conjugate A) 0 ++
      carry A ((n : ℝ) • basis timeAxis))) atTop
      (𝓝 (S.expect (conjugate A) * S.expect A)) := hc
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

/-- (a) ⇒ (c). -/
theorem pairClusters_of_const (Hs : Steady V) (Y : S.Hierarchy) (R : P.Resolution)
    (hv : R.Out) (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    (hreal : ∀ i, (T i).RealSpin) (A : L.Word) (hA : distinct A)
    (hconst : ∀ i, (T i).expect A = S.expect A) :
    PairClusters S (conjugate A) A := by
  have := hv.normalized
  have hA' := distinct_conjugate hA
  have hbar : ∀ {w : L.Word}, distinct w → ∫ i, (T i).expect w ∂(R.μ) = S.expect w :=
    fun hw => Spread.Resolution.barycenter R T hv ht Y.translations _ hw
  have hcA : (fun i => (T i).expect (conjugate A)) = fun _ => star (S.expect A) := by
    funext i
    rw [expect_conjugate (hreal i) hA, hconst i]
  have hSc : S.expect (conjugate A) = star (S.expect A) := by
    rw [← hbar hA', hcA, integral_const]
    simp
  have hprod : (fun i => (T i).expect (conjugate A) * (T i).expect A) =
      fun _ => star (S.expect A) * S.expect A := by
    funext i
    rw [expect_conjugate (hreal i) hA, hconst i]
  have hval : (∫ i, (T i).expect (conjugate A) * (T i).expect A ∂(R.μ)) =
      S.expect (conjugate A) * S.expect A := by
    rw [hprod, integral_const, hSc]
    simp
  intro f g hfg
  obtain ⟨-, hlim⟩ := mixed_two_cluster P Hs Y R hv T ht (conjugate A) A hA' hA f g hfg
  rw [hval] at hlim
  exact hlim

/-- (b) ⇒ (a): full support and continuity. -/
theorem const_of_ae (R : P.Resolution) (hv : R.Out) (T : R.X → Table L)
    (ht : ∀ i, R.receives (T i) i) (A : L.Word) (hA : distinct A)
    (h : ∀ᵐ i ∂(R.μ), (T i).expect A = S.expect A) :
    ∀ i, (T i).expect A = S.expect A := by
  have := hv.support
  have hcont : Continuous fun i => (T i).expect A :=
    (hv.weak (M P A hA)).congr fun i => character_M P R T ht i A hA
  have heq : (fun i => (T i).expect A) = fun _ => S.expect A :=
    (Continuous.ae_eq_iff_eq R.μ hcont continuous_const).1 h
  intro i
  exact congrFun heq i

/-- **One word: every phase ⇔ a.e. phase ⇔ two-point clustering (all flights) ⇔ (basis flight).** -/
theorem const_iff (Hs : Steady V) (Y : S.Hierarchy) (R : P.Resolution)
    (hv : R.Out) (T : R.X → Table L) (ht : ∀ i, R.receives (T i) i)
    (hreal : ∀ i, (T i).RealSpin) (A : L.Word) (hA : distinct A) :
    ((∀ i, (T i).expect A = S.expect A) ↔ ∀ᵐ i ∂(R.μ), (T i).expect A = S.expect A) ∧
    ((∀ i, (T i).expect A = S.expect A) ↔ PairClusters S (conjugate A) A) ∧
    ((∀ i, (T i).expect A = S.expect A) ↔ PairBasisClusters S (conjugate A) A) := by
  refine ⟨⟨fun h => ae_of_all R.μ h, const_of_ae P R hv T ht A hA⟩,
    ⟨pairClusters_of_const P Hs Y R hv T ht hreal A hA,
      fun hc => const_of_pairBasis P Hs Y R hv T ht hreal A hA (hc _ _ flight_basis)⟩,
    ⟨fun h => pairClusters_of_const P Hs Y R hv T ht hreal A hA h _ _ flight_basis,
      const_of_pairBasis P Hs Y R hv T ht hreal A hA⟩⟩

end YM.OS.Ground.Marker

namespace YM.Independent.Marker
open Function Filter MeasureTheory OPE OPE.Orbits Word YM.OS.Ground.Marker
open scoped Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- The one-point word of a dimension-four field: one token `w` at the origin. -/
def markerWord (w : S.Field 4) : C.book.Word :=
  worded (sole (0 : E4)) (fun _ : Unit => (⟨4, S.representative 4 w⟩ : C.book.Token))

lemma markerWord_distinct (w : S.Field 4) : distinct (markerWord w) := by
  have hinj : Injective (sole (0 : E4)) := fun a b _ => Subsingleton.elim a b
  show distinct (worded (sole (0 : E4))
    (fun _ : Unit => (⟨4, S.representative 4 w⟩ : C.book.Token)))
  exact (worded_distinct _).2 hinj

/-- In every viewer the marker word reads the one-point value of `w`. -/
lemma expect_markerWord (F : Spec.Final C f S) (s : Viewers F) (w : S.Field 4) :
    (spectator F s).expect (markerWord w) = DimFour.onePoint F s 0 w := by
  have h1 : (spectator F s).expect (markerWord w) =
      Low.oneToken (spectator F s) 0 4 (S.representative 4 w) := rfl
  have h2 : Low.oneToken (spectator F s) 0 4 (S.representative 4 w) =
      S.classMoment (spectator F s) (n := 1) (fun _ => 4) (points (fun _ : Fin 1 => (0 : E4)))
        (fun _ => S.project 4 (S.representative 4 w)) :=
    Low.oneToken_class (S := S) (spectate F s).laws.toSymmetric (spectate_respects F s)
      (0 : E4) 4 (S.representative 4 w)
  have h3 : S.project 4 (S.representative 4 w) = w := S.rep 4 w
  rw [h3] at h2
  have h4 : S.classMoment (spectator F s) (fun _ : Fin 1 => 4) (points (fun _ : Fin 1 => (0 : E4)))
      (fun _ => w) = DimFour.onePointL S (spectator F s) 0 4 w :=
    DimFour.onePointL_apply S (spectator F s) 0 4 w
  exact h1.trans (h2.trans h4)

/-- **Avenue B for one dimension-four field `w`, for OpenAI's `F`.** The following are equivalent:
every phase gives `⟨w⟩` the lattice-limit value; `μ`-a.e. phase does; the lattice-limit two-point
function of `w̄`, `w` clusters (rate-free) along every flight; it clusters along the basis flight. -/
theorem marker_phase_iff_clusters (F : Spec.Final C f S) (w : S.Field 4) :
    ((∀ i : F.α.space.X, DimFour.onePoint F (some i) 0 w = DimFour.onePoint F none 0 w) ↔
      ∀ᵐ i ∂(F.α.space.μ), DimFour.onePoint F (some i) 0 w = DimFour.onePoint F none 0 w) ∧
    ((∀ i : F.α.space.X, DimFour.onePoint F (some i) 0 w = DimFour.onePoint F none 0 w) ↔
      PairClusters S (conjugate (markerWord w)) (markerWord w)) ∧
    ((∀ i : F.α.space.X, DimFour.onePoint F (some i) 0 w = DimFour.onePoint F none 0 w) ↔
      PairBasisClusters S (conjugate (markerWord w)) (markerWord w)) := by
  have key := const_iff F.α.unselected F.phase.phase.still F.room.kernel F.α.space
    F.phase.phase.decomposition F.α.ensemble F.phase.phase.chosen
    (fun i => (F.phase.phase.states i).spin) (markerWord w) (markerWord_distinct w)
  have e1 : ∀ i : F.α.space.X,
      (F.α.ensemble i).expect (markerWord w) = DimFour.onePoint F (some i) 0 w :=
    fun i => expect_markerWord F (some i) w
  have e0 : S.expect (markerWord w) = DimFour.onePoint F none 0 w := expect_markerWord F none w
  have hiff : (∀ i : F.α.space.X, DimFour.onePoint F (some i) 0 w = DimFour.onePoint F none 0 w) ↔
      ∀ i : F.α.space.X, (F.α.ensemble i).expect (markerWord w) = S.expect (markerWord w) := by
    constructor
    · intro h i
      rw [e1 i, e0]
      exact h i
    · intro h i
      rw [← e1 i, ← e0]
      exact h i
  have hae : (∀ᵐ i ∂(F.α.space.μ), DimFour.onePoint F (some i) 0 w = DimFour.onePoint F none 0 w) ↔
      ∀ᵐ i ∂(F.α.space.μ), (F.α.ensemble i).expect (markerWord w) = S.expect (markerWord w) := by
    constructor
    · intro h
      filter_upwards [h] with i hi
      rw [e1 i, e0]
      exact hi
    · intro h
      filter_upwards [h] with i hi
      rw [← e1 i, ← e0]
      exact hi
  obtain ⟨k1, k2, k3⟩ := key
  exact ⟨hiff.trans (k1.trans hae.symm), hiff.trans k2, hiff.trans k3⟩

/-- **All of dimension four from one two-point function.** With `w` the marker of
`DimFour.one_number`: every dimension-four one-point value is the same in every phase as in the
lattice limit iff the lattice-limit two-point function of `w̄`, `w` clusters. -/
theorem dimFour_phase_iff_clusters (F : Spec.Final C f S) (hG : G.Simple) :
    ∃ w : S.Field 4,
      ((∀ (i : F.α.space.X) (z : S.Field 4),
          DimFour.onePoint F (some i) 0 z = DimFour.onePoint F none 0 z) ↔
        PairClusters S (conjugate (markerWord w)) (markerWord w)) := by
  obtain ⟨w, c, κ, hw⟩ := DimFour.one_number F hG
  refine ⟨w, ?_⟩
  have k := (marker_phase_iff_clusters F w).2.1
  constructor
  · intro h
    exact k.1 (fun i => h i w)
  · intro hc i z
    have hi := k.2 hc i
    rw [hw (some i) 0 z, hw none 0 z, hi]

end YM.Independent.Marker

import Check.LowCondensates
import YM.Euclid.Comparator
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size
import YM.UVNext.FREE_STRESS_CERTIFICATE.Parity
import YM.UVNext.FREE_STRESS_CERTIFICATE.Orbits

/-! Council, 25 November 2026 (session 5). At dimension four, all dependence on the viewer
(lattice limit or phase) of OpenAI's construction is carried by ONE number per viewer.

Mathematics.
* `S.Field 4` has dimension 22 (`field_four_rank`): the library's comparator
  (`F.phase.transport.comparator : Maxwell.Ranks S _`) is a linear equivalence of `S.Field 4` with the
  free field space `(freeTable C.book.grid).Field 4`, whose basis (`UVNext.FreeStress.stand`) is the unit
  and the 21 symmetric pairs of planes `tr F_p F_q`. The equivalence intertwines the action of the
  signed permutations of the four axes (`Signed`, the hyperoctahedral group, 384 elements, reflections
  included). It is NOT stated to send unit to unit, and the proof below does not use that.
* Every viewer is a `Table.Hierarchy` (`spectate`), hence invariant under translations and under
  `Signed`; so its one-point functional on `S.Field 4` is `Signed`-invariant (`onePoint_mirror`).
* A `Signed`-invariant linear functional on the free space kills `tr F_p F_q` for `p ≠ q` (reflect an
  axis lying in exactly one of the planes) and takes one common value on the six `tr F_p F_p`
  (permute axes). So it is determined by two numbers (`invariant_two`).
* The unit has one-point value 1 in every viewer; this removes one of the two numbers
  (`affine_reduce`). Result (`one_number`): there are a field `w` and viewer-independent `c, κ` with
  `⟨z⟩_s = c z + κ z * ⟨w⟩_s` for every viewer `s`, point `o` and `z : S.Field 4`.

Nothing from OpenAI's library is copied here; it is used through imports of built modules. -/
set_option autoImplicit false
noncomputable section
namespace YM.Independent.DimFour
open Filter MeasureTheory OPE OPE.Orbits
open scoped Topology BigOperators

universe u v

/-! ### 1. Signed-invariant functionals on the free dimension-four space -/
section Free
variable {G : Gauge} (F : Labels.Frames G) (H : (Maxwell.freeTable F).RealSpin)

set_option maxRecDepth 10000 in
/-- Two distinct coordinate planes: some axis lies in exactly one of them (parity `-1`). -/
lemma odd_axis : ∀ p q : UVNext.FreeStress.Plane, p ≠ q → ∃ t : Axis,
    UVNext.FreeStress.bit t p.val.1 * UVNext.FreeStress.bit t p.val.2 *
      (UVNext.FreeStress.bit t q.val.1 * UVNext.FreeStress.bit t q.val.2) = -1 := by
  decide

/-- A permutation of the axes carrying `(0, 1)` to a prescribed ordered pair of distinct axes. -/
lemma place (a b : Axis) (h : a ≠ b) : ∃ σ : Equiv.Perm Axis, σ 0 = a ∧ σ 1 = b := by
  have h0 : (Equiv.swap (0 : Axis) a) 0 = a := Equiv.swap_apply_left 0 a
  have h1 : (Equiv.swap (0 : Axis) a) 1 ≠ a := by
    intro e
    have e2 : (Equiv.swap (0 : Axis) a) 1 = (Equiv.swap (0 : Axis) a) 0 := e.trans h0.symm
    have e3 : (1 : Axis) = 0 := (Equiv.swap (0 : Axis) a).injective e2
    exact absurd e3 (by decide)
  refine ⟨Equiv.swap ((Equiv.swap (0 : Axis) a) 1) b * Equiv.swap (0 : Axis) a, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, h0]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) h
  · rw [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left ((Equiv.swap (0 : Axis) a) 1) b

/-- An invariant functional vanishes on `tr F_p F_q` for distinct planes. -/
lemma inv_off (φ : (Maxwell.freeTable F).Field 4 →ₗ[ℂ] ℂ)
    (hφ : ∀ (k : Signed) (v : (Maxwell.freeTable F).Field 4),
      φ ((Maxwell.freeTable F).mirror H 4 k v) = φ v)
    (p q : UVNext.FreeStress.Plane) (hpq : p ≠ q) :
    φ (UVNext.FreeStress.link F 4 (le_refl 4) p.val.1 p.val.2 q.val.1 q.val.2) = 0 := by
  obtain ⟨t, ht⟩ := odd_axis p q hpq
  have hc : (Maxwell.freeTable F).mirror H 4 (Signed.mirror t)
        (UVNext.FreeStress.link F 4 (le_refl 4) p.val.1 p.val.2 q.val.1 q.val.2) =
      (((UVNext.FreeStress.bit t p.val.1 * UVNext.FreeStress.bit t p.val.2 *
        (UVNext.FreeStress.bit t q.val.1 * UVNext.FreeStress.bit t q.val.2) : ℤ)) : ℂ) •
        UVNext.FreeStress.link F 4 (le_refl 4) p.val.1 p.val.2 q.val.1 q.val.2 :=
    UVNext.FreeStress.link_color F H p.val.1 p.val.2 q.val.1 q.val.2 (le_refl 4) t
  have h1 : φ ((Maxwell.freeTable F).mirror H 4 (Signed.mirror t)
        (UVNext.FreeStress.link F 4 (le_refl 4) p.val.1 p.val.2 q.val.1 q.val.2)) =
      φ (UVNext.FreeStress.link F 4 (le_refl 4) p.val.1 p.val.2 q.val.1 q.val.2) :=
    hφ (Signed.mirror t) _
  rw [hc, ht, map_smul, smul_eq_mul] at h1
  push_cast at h1
  linear_combination (-1 / 2 : ℂ) * h1

/-- An invariant functional takes the same value on all six `tr F_p F_p`. -/
lemma inv_diag (φ : (Maxwell.freeTable F).Field 4 →ₗ[ℂ] ℂ)
    (hφ : ∀ (k : Signed) (v : (Maxwell.freeTable F).Field 4),
      φ ((Maxwell.freeTable F).mirror H 4 k v) = φ v)
    (p : UVNext.FreeStress.Plane) :
    φ (UVNext.FreeStress.link F 4 (le_refl 4) p.val.1 p.val.2 p.val.1 p.val.2) =
      φ (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1) := by
  obtain ⟨σ, h0, h1⟩ := place p.val.1 p.val.2 (ne_of_lt p.property)
  have hr : UVNext.FreeStress.ride F H 4 σ (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1) =
      UVNext.FreeStress.link F 4 (le_refl 4) (σ 0) (σ 1) (σ 0) (σ 1) :=
    UVNext.FreeStress.ride_link F H σ 0 1 0 1 (le_refl 4)
  rw [h0, h1] at hr
  have hi : φ ((Maxwell.freeTable F).mirror H 4 (UVNext.FreeStress.round σ)
        (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1)) =
      φ (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1) :=
    hφ (UVNext.FreeStress.round σ) _
  have hrr : (Maxwell.freeTable F).mirror H 4 (UVNext.FreeStress.round σ)
        (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1) =
      UVNext.FreeStress.link F 4 (le_refl 4) p.val.1 p.val.2 p.val.1 p.val.2 := hr
  rw [hrr] at hi
  exact hi

/-- Weight selecting the unit among the 22 basis labels. -/
def unitW : Option UVNext.FreeStress.Face → ℂ
  | none => 1
  | some _ => 0

/-- Weight selecting the six diagonal labels `tr F_p F_p` among the 22 basis labels. -/
def diagW : Option UVNext.FreeStress.Face → ℂ
  | none => 0
  | some x => if x.val.1 = x.val.2 then 1 else 0

/-- Value of an invariant functional on each of the 22 basis vectors. -/
lemma inv_on_sector (φ : (Maxwell.freeTable F).Field 4 →ₗ[ℂ] ℂ)
    (hφ : ∀ (k : Signed) (v : (Maxwell.freeTable F).Field 4),
      φ ((Maxwell.freeTable F).mirror H 4 k v) = φ v)
    (i : Option UVNext.FreeStress.Face) :
    φ (UVNext.FreeStress.embed F 4 (UVNext.FreeStress.sectors (G := G) i)) =
      unitW i * φ ((Maxwell.freeTable F).unit 4) +
        diagW i * φ (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1) := by
  cases i with
  | none =>
    have e : UVNext.FreeStress.embed F 4 (UVNext.FreeStress.sectors (G := G) none) =
        (Maxwell.freeTable F).unit 4 := UVNext.FreeStress.pin_unit F 4
    rw [e]
    show φ ((Maxwell.freeTable F).unit 4) =
      (1 : ℂ) * φ ((Maxwell.freeTable F).unit 4) +
        (0 : ℂ) * φ (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1)
    ring
  | some x =>
    have e : UVNext.FreeStress.embed F 4 (UVNext.FreeStress.sectors (G := G) (some x)) =
        UVNext.FreeStress.link F 4 (le_refl 4) x.val.1.val.1 x.val.1.val.2 x.val.2.val.1 x.val.2.val.2 :=
      rfl
    have hu : unitW (some x) = 0 := rfl
    rw [e, hu]
    by_cases hx : x.val.1 = x.val.2
    · have hd : diagW (some x) = 1 := by
        show (if x.val.1 = x.val.2 then (1 : ℂ) else 0) = 1
        exact if_pos hx
      have hl : UVNext.FreeStress.link F 4 (le_refl 4) x.val.1.val.1 x.val.1.val.2
            x.val.2.val.1 x.val.2.val.2 =
          UVNext.FreeStress.link F 4 (le_refl 4) x.val.1.val.1 x.val.1.val.2
            x.val.1.val.1 x.val.1.val.2 := by
        rw [← hx]
      rw [hd, hl, inv_diag F H φ hφ x.val.1]
      ring
    · have hd : diagW (some x) = 0 := by
        show (if x.val.1 = x.val.2 then (1 : ℂ) else 0) = 0
        exact if_neg hx
      rw [hd, inv_off F H φ hφ x.val.1 x.val.2 hx]
      ring

/-- Coordinate of `v` along the unit, in the library's basis `stand` of the free space. -/
def unitCoord (hG : G.Simple) (v : (Maxwell.freeTable F).Field 4) : ℂ :=
  ∑ i : Option UVNext.FreeStress.Face, (UVNext.FreeStress.stand F hG).repr v i * unitW i

/-- Sum of the six coordinates of `v` along the diagonal labels `tr F_p F_p`. -/
def diagCoord (hG : G.Simple) (v : (Maxwell.freeTable F).Field 4) : ℂ :=
  ∑ i : Option UVNext.FreeStress.Face, (UVNext.FreeStress.stand F hG).repr v i * diagW i

/-- **Invariant theory at dimension four.** A linear functional on the 22-dimensional free space that
is invariant under all signed permutations of the axes is determined by its values on the unit and
on one diagonal label: the invariant functionals form a space of dimension at most two. -/
theorem invariant_two (hG : G.Simple) (φ : (Maxwell.freeTable F).Field 4 →ₗ[ℂ] ℂ)
    (hφ : ∀ (k : Signed) (v : (Maxwell.freeTable F).Field 4),
      φ ((Maxwell.freeTable F).mirror H 4 k v) = φ v)
    (v : (Maxwell.freeTable F).Field 4) :
    φ v = unitCoord F hG v * φ ((Maxwell.freeTable F).unit 4) +
      diagCoord F hG v * φ (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1) := by
  have hbi : ∀ i : Option UVNext.FreeStress.Face, (UVNext.FreeStress.stand F hG) i =
      UVNext.FreeStress.embed F 4 (UVNext.FreeStress.sectors (G := G) i) := by
    intro i
    first
      | exact Module.Basis.mk_apply (UVNext.FreeStress.freelance F hG) _ i
      | (rw [UVNext.FreeStress.stand, Module.Basis.mk_apply]; rfl)
      | rw [UVNext.FreeStress.stand, Module.Basis.mk_apply]
      | simp [UVNext.FreeStress.stand]
  have hv : v = ∑ i : Option UVNext.FreeStress.Face,
      (UVNext.FreeStress.stand F hG).repr v i • (UVNext.FreeStress.stand F hG) i :=
    ((UVNext.FreeStress.stand F hG).sum_repr v).symm
  have h1 : φ v = ∑ i : Option UVNext.FreeStress.Face,
      (UVNext.FreeStress.stand F hG).repr v i * φ ((UVNext.FreeStress.stand F hG) i) := by
    have h2 : φ v = φ (∑ i : Option UVNext.FreeStress.Face,
        (UVNext.FreeStress.stand F hG).repr v i • (UVNext.FreeStress.stand F hG) i) :=
      congrArg (fun y => φ y) hv
    rw [h2, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
  have h3 : (∑ i : Option UVNext.FreeStress.Face,
      (UVNext.FreeStress.stand F hG).repr v i * φ ((UVNext.FreeStress.stand F hG) i)) =
      ∑ i : Option UVNext.FreeStress.Face, (UVNext.FreeStress.stand F hG).repr v i *
        (unitW i * φ ((Maxwell.freeTable F).unit 4) +
          diagW i * φ (UVNext.FreeStress.link F 4 (le_refl 4) 0 1 0 1)) :=
    Finset.sum_congr rfl (fun i _ => by rw [hbi i, inv_on_sector F H φ hφ i])
  rw [h1, h3]
  unfold unitCoord diagCoord
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end Free

/-! ### 2. Two numbers, one of them fixed by the unit, leave one -/

/-- If every functional of a family is a combination, with common coefficient functions `a, b`, of
its values at two vectors `u, w`, and all take the value 1 at `one`, then all viewer dependence is in
its value at a single vector. -/
lemma affine_reduce {ι V : Type*} (ω : ι → V → ℂ) (a b : V → ℂ) (u w one : V)
    (hexp : ∀ (s : ι) (z : V), ω s z = a z * ω s u + b z * ω s w)
    (hone : ∀ s : ι, ω s one = 1) :
    ∃ (w0 : V) (c κ : V → ℂ), ∀ (s : ι) (z : V), ω s z = c z + κ z * ω s w0 := by
  by_cases ha : a one = 0
  · have hW : ∀ s : ι, ω s w = (b one)⁻¹ := by
      intro s
      have h := hexp s one
      rw [hone s, ha, zero_mul, zero_add] at h
      have hne : b one ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h
        exact one_ne_zero h
      calc ω s w = (b one)⁻¹ * (b one * ω s w) := by
            rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
        _ = (b one)⁻¹ := by rw [← h, mul_one]
    refine ⟨u, fun z => b z * (b one)⁻¹, a, fun s z => ?_⟩
    show ω s z = b z * (b one)⁻¹ + a z * ω s u
    rw [hexp s z, hW s]
    ring
  · have hU : ∀ s : ι, ω s u = (a one)⁻¹ * (1 - b one * ω s w) := by
      intro s
      have h := hexp s one
      rw [hone s] at h
      have h' : a one * ω s u = 1 - b one * ω s w := by linear_combination (-1 : ℂ) * h
      calc ω s u = (a one)⁻¹ * (a one * ω s u) := by
            rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
        _ = (a one)⁻¹ * (1 - b one * ω s w) := by rw [h']
    refine ⟨w, fun z => a z * (a one)⁻¹, fun z => b z - a z * (a one)⁻¹ * b one, fun s z => ?_⟩
    show ω s z = a z * (a one)⁻¹ + (b z - a z * (a one)⁻¹ * b one) * ω s w
    rw [hexp s z, hU s]
    ring

/-! ### 3. One-point values in a table that respects the field quotients of `S` -/
section OnePoint
variable {G : Gauge} {L : Register G}

/-- In a translation-invariant table a one-point read does not depend on the point. -/
lemma read_one_any {T : Table L} (hT : T.Homogeneous) (y : Points 1) (o : E4)
    (w : Fin 1 → L.Token) : T.read y w = T.read (points (fun _ : Fin 1 => o)) w := by
  have e : y = Points.across (y 0 - o) (points (fun _ : Fin 1 => o)) := by
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change y 0 = o + (y 0 - o)
    abel
  have h : T.read (Points.across (y 0 - o) (points (fun _ : Fin 1 => o))) w =
      T.read (points (fun _ : Fin 1 => o)) w :=
    hT 1 (points (fun _ : Fin 1 => o)) (Low.valid_one _) (y 0 - o) w
  exact (congrArg (fun z : Points 1 => T.read z w) e).trans h

/-- The one-point value at `o`, in the table `T`, as a linear functional on `S.Field d`. -/
def onePointL (S T : Table L) (o : E4) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ :=
  (S.classMoment T (n := 1) (fun _ => d) (points (fun _ : Fin 1 => o))).toLinearMap (fun _ => 0) 0

lemma onePointL_apply (S T : Table L) (o : E4) (d : ℕ) (v : S.Field d) :
    S.classMoment T (fun _ : Fin 1 => d) (points (fun _ : Fin 1 => o)) (fun _ => v) =
      onePointL S T o d v := by
  unfold onePointL
  rw [MultilinearMap.toLinearMap_apply]
  congr 1
  funext i
  fin_cases i
  simp

lemma onePointL_project (S T : Table L) (hT : T.Symmetric) (hr : T.respects S) (o : E4) (d : ℕ)
    (p : L.Ref d) :
    onePointL S T o d (S.project d p) =
      T.read (points (fun _ : Fin 1 => o)) (fun _ : Fin 1 => (⟨d, p⟩ : L.Token)) :=
  (onePointL_apply S T o d (S.project d p)).symm.trans
    (S.class_agrees T hT hr (fun _ : Fin 1 => d) (Low.valid_one _) (fun _ => p))

/-- One-point values are invariant under signed permutations of the axes: the viewer's table is
invariant under them and under translations. -/
lemma onePointL_mirror (S T : Table L) (H : S.RealSpin) (hT : T.Hierarchy) (hr : T.respects S)
    (o : E4) (d : ℕ) (k : Signed) (z : S.Field d) :
    onePointL S T o d (S.mirror H d k z) = onePointL S T o d z := by
  obtain ⟨p, rfl⟩ := S.onto d z
  have e1 : S.mirror H d k (S.project d p) = S.project d (L.mirrorGroup d k p) := rfl
  have hx : points (fun _ : Fin 1 => o) ∈ conf 1 := Low.valid_one _
  have hm : T.read (Points.move k.ortho (points (fun _ : Fin 1 => o)))
        (L.move k ∘ (fun _ : Fin 1 => (⟨d, p⟩ : L.Token))) =
      T.read (points (fun _ : Fin 1 => o)) (fun _ : Fin 1 => (⟨d, p⟩ : L.Token)) :=
    hT.spin.mirror k hx (fun _ : Fin 1 => (⟨d, p⟩ : L.Token))
  have hs : T.read (Points.move k.ortho (points (fun _ : Fin 1 => o)))
        (L.move k ∘ (fun _ : Fin 1 => (⟨d, p⟩ : L.Token))) =
      T.read (points (fun _ : Fin 1 => o)) (L.move k ∘ (fun _ : Fin 1 => (⟨d, p⟩ : L.Token))) :=
    read_one_any hT.translations _ o _
  have hmove : T.read (points (fun _ : Fin 1 => o))
        (fun _ : Fin 1 => (⟨d, L.mirrorGroup d k p⟩ : L.Token)) =
      T.read (points (fun _ : Fin 1 => o)) (fun _ : Fin 1 => (⟨d, p⟩ : L.Token)) :=
    hs.symm.trans hm
  rw [e1]
  exact (onePointL_project S T hT.laws.toSymmetric hr o d (L.mirrorGroup d k p)).trans
    (hmove.trans (onePointL_project S T hT.laws.toSymmetric hr o d p).symm)

/-- The unit has one-point value 1. -/
lemma onePointL_unit (S T : Table L) (hT : T.Basic) (hr : T.respects S) (o : E4) (d : ℕ) :
    onePointL S T o d (S.unit d) = 1 := by
  have h1 : onePointL S T o d (S.project d (L.scalar d)) =
      T.read (points (fun _ : Fin 1 => o)) (fun _ : Fin 1 => (⟨d, L.scalar d⟩ : L.Token)) :=
    onePointL_project S T hT.toSymmetric hr o d (L.scalar d)
  have h2 : Low.oneToken T o d (L.scalar d) =
      T.read (points (fun _ : Fin 1 => o)) (fun _ : Fin 1 => (⟨d, L.scalar d⟩ : L.Token)) :=
    Low.singleton_read T hT.toSymmetric o d (L.scalar d)
  have h3 : Low.oneToken T o d (L.scalar d) = 1 :=
    Low.oneToken_scalar S T hT hr o d (L.scalar d) 1 (one_smul ℂ (S.unit d)).symm
  exact h1.trans (h2.symm.trans h3)

/-- One-point values do not depend on the point. -/
lemma onePointL_point (S T : Table L) (hT : T.Hierarchy) (hr : T.respects S) (o o' : E4) (d : ℕ)
    (z : S.Field d) : onePointL S T o d z = onePointL S T o' d z := by
  obtain ⟨p, rfl⟩ := S.onto d z
  exact (onePointL_project S T hT.laws.toSymmetric hr o d p).trans
    ((read_one_any hT.translations (points (fun _ : Fin 1 => o)) o'
        (fun _ : Fin 1 => (⟨d, p⟩ : L.Token))).trans
      (onePointL_project S T hT.laws.toSymmetric hr o' d p).symm)

end OnePoint

/-! ### 4. The viewers of a `Final` -/
section Viewers
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- Premise check: the interacting field space of dimension four has rank 22, like the free one. -/
theorem field_four_rank (F : Spec.Final C f S) (hG : G.Simple) :
    Module.finrank ℂ (S.Field 4) = 22 := by
  obtain ⟨H0, hH⟩ := F.phase.transport.comparator
  obtain ⟨e, -, -⟩ := hH 4
  exact e.finrank_eq.trans (UVNext.FreeStress.four_size _ hG)

/-- The one-point value `⟨z(o)⟩_s` of a dimension-four field in viewer `s`. -/
def onePoint (F : Spec.Final C f S) (s : Viewers F) (o : E4) : S.Field 4 →ₗ[ℂ] ℂ :=
  onePointL S (spectator F s) o 4

/-- Step 1: every viewer's one-point functional is invariant under signed permutations. -/
theorem onePoint_mirror (F : Spec.Final C f S) (s : Viewers F) (o : E4) (k : Signed)
    (z : S.Field 4) :
    onePoint F s o (S.mirror F.room.kernel.spin 4 k z) = onePoint F s o z :=
  onePointL_mirror S (spectator F s) F.room.kernel.spin (spectate F s) (spectate_respects F s)
    o 4 k z

theorem onePoint_unit (F : Spec.Final C f S) (s : Viewers F) (o : E4) :
    onePoint F s o (S.unit 4) = 1 :=
  onePointL_unit S (spectator F s) (spectate F s).laws (spectate_respects F s) o 4

theorem onePoint_point (F : Spec.Final C f S) (s : Viewers F) (o o' : E4) (z : S.Field 4) :
    onePoint F s o z = onePoint F s o' z :=
  onePointL_point S (spectator F s) (spectate F s) (spectate_respects F s) o o' 4 z

/-- The condensate of a dimension-four channel is the one-point value of its actor. -/
theorem condensate_eq_onePoint {F : Spec.Final C f S}
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s : Viewers F) (i : Q.channels 4) (o : E4) :
    condensate Q s 4 i o = onePoint F s o (Q.actor 4 i) := by
  have hsym : (spectator F s).Symmetric := (spectate F s).laws.toSymmetric
  have c1 : condensate Q s 4 i o =
      Low.oneToken (spectator F s) o 4 (S.representative 4 (Q.actor 4 i)) :=
    Low.condensate_eq_oneToken (Q := Q) s 4 i o
  have c2 : Low.oneToken (spectator F s) o 4 (S.representative 4 (Q.actor 4 i)) =
      (spectator F s).read (points (fun _ : Fin 1 => o))
        (fun _ : Fin 1 => (⟨4, S.representative 4 (Q.actor 4 i)⟩ : C.book.Token)) :=
    Low.singleton_read (spectator F s) hsym o 4 (S.representative 4 (Q.actor 4 i))
  have c3 : onePointL S (spectator F s) o 4 (S.project 4 (S.representative 4 (Q.actor 4 i))) =
      (spectator F s).read (points (fun _ : Fin 1 => o))
        (fun _ : Fin 1 => (⟨4, S.representative 4 (Q.actor 4 i)⟩ : C.book.Token)) :=
    onePointL_project S (spectator F s) hsym (spectate_respects F s) o 4
      (S.representative 4 (Q.actor 4 i))
  have c4 : S.project 4 (S.representative 4 (Q.actor 4 i)) = Q.actor 4 i := S.rep 4 (Q.actor 4 i)
  rw [c4] at c3
  exact c1.trans (c2.trans c3.symm)

/-- A functional on `S.Field 4` pulled back to the free space along the comparator. -/
def pulled (e : S.Field 4 ≃ₗ[ℂ] (Maxwell.freeTable C.book.grid).Field 4)
    (φ : S.Field 4 →ₗ[ℂ] ℂ) : (Maxwell.freeTable C.book.grid).Field 4 →ₗ[ℂ] ℂ :=
  φ.comp e.symm.toLinearMap

lemma pulled_apply (e : S.Field 4 ≃ₗ[ℂ] (Maxwell.freeTable C.book.grid).Field 4)
    (φ : S.Field 4 →ₗ[ℂ] ℂ) (v : (Maxwell.freeTable C.book.grid).Field 4) :
    pulled e φ v = φ (e.symm v) := rfl

/-- **Step 2 on the interacting field space.** There are two fixed fields `u`, `w` and coefficient
functions `a`, `b` such that EVERY linear functional on `S.Field 4` that is invariant under the signed
permutations of the axes is `φ z = a z * φ u + b z * φ w`: the invariant functionals on the
22-dimensional space `S.Field 4` form a space of dimension at most two. -/
theorem invariant_two_S (F : Spec.Final C f S) (hG : G.Simple) :
    ∃ (u w : S.Field 4) (a b : S.Field 4 → ℂ), ∀ φ : S.Field 4 →ₗ[ℂ] ℂ,
      (∀ (k : Signed) (z : S.Field 4), φ (S.mirror F.room.kernel.spin 4 k z) = φ z) →
      ∀ z : S.Field 4, φ z = a z * φ u + b z * φ w := by
  obtain ⟨H0, hH⟩ := F.phase.transport.comparator
  obtain ⟨e, -, he⟩ := hH 4
  refine ⟨e.symm ((Maxwell.freeTable C.book.grid).unit 4),
    e.symm (UVNext.FreeStress.link C.book.grid 4 (le_refl 4) 0 1 0 1),
    fun z => unitCoord C.book.grid hG (e z), fun z => diagCoord C.book.grid hG (e z), ?_⟩
  intro φ hinv z
  have hφ : ∀ (k : Signed) (v : (Maxwell.freeTable C.book.grid).Field 4),
      pulled e φ ((Maxwell.freeTable C.book.grid).mirror H0 4 k v) = pulled e φ v := by
    intro k v
    have h1 : e (S.mirror F.room.kernel.spin 4 k (e.symm v)) =
        (Maxwell.freeTable C.book.grid).mirror H0 4 k v := by
      rw [he k (e.symm v), e.apply_symm_apply]
    have h2 : e.symm ((Maxwell.freeTable C.book.grid).mirror H0 4 k v) =
        S.mirror F.room.kernel.spin 4 k (e.symm v) := by
      rw [← h1, e.symm_apply_apply]
    rw [pulled_apply, pulled_apply, h2]
    exact hinv k (e.symm v)
  have h := invariant_two C.book.grid H0 hG (pulled e φ) hφ (e z)
  rw [pulled_apply, pulled_apply, pulled_apply, e.symm_apply_apply] at h
  exact h

/-- Two numbers: every one-point value of a dimension-four field, in every viewer, is a fixed
combination of that viewer's one-point values of two fixed fields `u`, `w`. -/
theorem two_numbers (F : Spec.Final C f S) (hG : G.Simple) :
    ∃ (u w : S.Field 4) (a b : S.Field 4 → ℂ), ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = a z * onePoint F s o u + b z * onePoint F s o w := by
  obtain ⟨u, w, a, b, h⟩ := invariant_two_S F hG
  exact ⟨u, w, a, b, fun s o z => h (onePoint F s o) (fun k y => onePoint_mirror F s o k y) z⟩

/-- **One number.** There are a dimension-four field `w` and viewer-independent functions `c`, `κ`
such that, in every viewer `s` (the lattice limit `none` or any phase `some χ`), at every point `o`,
the one-point value of every dimension-four field `z` is `c z + κ z * ⟨w(o)⟩_s`. -/
theorem one_number (F : Spec.Final C f S) (hG : G.Simple) :
    ∃ (w : S.Field 4) (c κ : S.Field 4 → ℂ), ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o w := by
  obtain ⟨u, w, a, b, h⟩ := two_numbers F hG
  obtain ⟨w0, c, κ, h0⟩ := affine_reduce (ι := Viewers F × E4) (V := S.Field 4)
    (fun (p : Viewers F × E4) (z : S.Field 4) => onePoint F p.1 p.2 z) a b u w (S.unit 4)
    (fun p z => h p.1 p.2 z) (fun p => onePoint_unit F p.1 p.2)
  exact ⟨w0, c, κ, fun s o z => h0 (s, o) z⟩

/-! Consequences of a one-number representation `hw` (for any `w`, `c`, `κ` satisfying it). -/

/-- Differences of dimension-four one-point values between two viewers. -/
theorem onePoint_difference (F : Spec.Final C f S) {w : S.Field 4} {c κ : S.Field 4 → ℂ}
    (hw : ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o w)
    (s t : Viewers F) (o : E4) (z : S.Field 4) :
    onePoint F s o z - onePoint F t o z = κ z * (onePoint F s o w - onePoint F t o w) := by
  rw [hw s o z, hw t o z]
  ring

/-- Differences of dimension-four condensates between two viewers: a viewer-independent
coefficient `κ (Q.actor 4 i)` times the difference of one number. -/
theorem condensate_difference {F : Spec.Final C f S}
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {w : S.Field 4} {c κ : S.Field 4 → ℂ}
    (hw : ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o w)
    (s t : Viewers F) (o : E4) (i : Q.channels 4) :
    condensate Q s 4 i o - condensate Q t 4 i o =
      κ (Q.actor 4 i) * (onePoint F s o w - onePoint F t o w) := by
  rw [condensate_eq_onePoint Q s i o, condensate_eq_onePoint Q t i o]
  exact onePoint_difference F hw s t o (Q.actor 4 i)

/-- Any field `θ` whose one-point value distinguishes some pair of viewers has `κ θ ≠ 0`. -/
theorem kappa_ne_zero (F : Spec.Final C f S) {w : S.Field 4} {c κ : S.Field 4 → ℂ}
    (hw : ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o w)
    (θ : S.Field 4) (s t : Viewers F) (o : E4) (hne : onePoint F s o θ ≠ onePoint F t o θ) :
    κ θ ≠ 0 := by
  intro h0
  have h := onePoint_difference F hw s t o θ
  rw [h0, zero_mul] at h
  exact hne (sub_eq_zero.mp h)

/-- Change of reference field: any `θ` with `κ θ ≠ 0` can serve as the one number. -/
theorem reference_change (F : Spec.Final C f S) {w : S.Field 4} {c κ : S.Field 4 → ℂ}
    (hw : ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o w)
    (θ : S.Field 4) (hθ : κ θ ≠ 0) (s t : Viewers F) (o : E4) (z : S.Field 4) :
    onePoint F s o z - onePoint F t o z =
      κ z / κ θ * (onePoint F s o θ - onePoint F t o θ) := by
  have h1 := onePoint_difference F hw s t o z
  have h2 := onePoint_difference F hw s t o θ
  rw [h1, h2]
  calc κ z * (onePoint F s o w - onePoint F t o w)
      = κ z * ((κ θ)⁻¹ * κ θ) * (onePoint F s o w - onePoint F t o w) := by
        rw [inv_mul_cancel₀ hθ, mul_one]
    _ = κ z / κ θ * (κ θ * (onePoint F s o w - onePoint F t o w)) := by
        rw [div_eq_mul_inv]
        ring

/-- Dichotomy for an arbitrary dimension-four field `θ` (for instance the stress trace): either all
viewers give `θ` the same one-point value, or `θ` is a complete marker: every dimension-four
one-point difference between two viewers is a fixed multiple of the difference for `θ`. -/
theorem marker_dichotomy (F : Spec.Final C f S) (hG : G.Simple) (θ : S.Field 4) :
    (∀ (s t : Viewers F) (o : E4), onePoint F s o θ = onePoint F t o θ) ∨
    ∃ ρ : S.Field 4 → ℂ, ∀ (s t : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z - onePoint F t o z = ρ z * (onePoint F s o θ - onePoint F t o θ) := by
  obtain ⟨w, c, κ, hw⟩ := one_number F hG
  by_cases hθ : κ θ = 0
  · left
    intro s t o
    have h := onePoint_difference F hw s t o θ
    rw [hθ, zero_mul] at h
    exact sub_eq_zero.mp h
  · right
    exact ⟨fun z => κ z / κ θ, fun s t o z => reference_change F hw θ hθ s t o z⟩

/-- **Short-distance form.** With `w`, `κ` as in `one_number`: on any group of insertions at scale
`r` around `o`, two viewers differ by at most a viewer-independent constant (built from the common
coefficients) times the difference of their one number, plus twice the remainder of order
`r ^ (5 − weight − ε)`. -/
theorem viewers_differ_by_one_number {hG : G.Simple} {F : Spec.Final C f S}
    {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q) {w : S.Field 4} {c κ : S.Field 4 → ℂ}
    (hw : ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o w)
    {I : Type} [Fintype I] {d : I → ℕ} (a : Labels S d)
    {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o → ∀ s t : Viewers F,
      ‖whole (spectator F s) x a noPts (noLab (S := S)) -
        whole (spectator F t) x a noPts (noLab (S := S))‖ ≤
        (∑ i : Q.channels 4, ‖Q.coef 4 i x a o‖ * ‖κ (Q.actor 4 i)‖) *
            ‖onePoint F s o w - onePoint F t o w‖ +
          2 * r ^ (((4 : ℕ) : ℝ) + 1 - weight d - ε) := by
  filter_upwards [Low.viewers_differ_by_dim4 H a hM hη hε] with r hr
  intro x o hx s t
  have h := hr x o hx s t
  have hsum : (∑ i : Q.channels 4,
        ‖Q.coef 4 i x a o‖ * ‖condensate Q s 4 i o - condensate Q t 4 i o‖) =
      (∑ i : Q.channels 4, ‖Q.coef 4 i x a o‖ * ‖κ (Q.actor 4 i)‖) *
        ‖onePoint F s o w - onePoint F t o w‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [condensate_difference Q hw s t o i, norm_mul]
    ring
  rw [hsum] at h
  exact h

/-- If two viewers agree on the one number, they agree on every group of insertions at scale `r`
up to twice the remainder of order `r ^ (5 − weight − ε)`. -/
theorem viewers_agree_of_one_number {hG : G.Simple} {F : Spec.Final C f S}
    {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q) {w : S.Field 4} {c κ : S.Field 4 → ℂ}
    (hw : ∀ (s : Viewers F) (o : E4) (z : S.Field 4),
      onePoint F s o z = c z + κ z * onePoint F s o w)
    {I : Type} [Fintype I] {d : I → ℕ} (a : Labels S d)
    {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o → ∀ s t : Viewers F,
      onePoint F s 0 w = onePoint F t 0 w →
      ‖whole (spectator F s) x a noPts (noLab (S := S)) -
        whole (spectator F t) x a noPts (noLab (S := S))‖ ≤
          2 * r ^ (((4 : ℕ) : ℝ) + 1 - weight d - ε) := by
  filter_upwards [viewers_differ_by_one_number H hw a hM hη hε] with r hr
  intro x o hx s t hst
  have h := hr x o hx s t
  have e : onePoint F s o w = onePoint F t o w :=
    (onePoint_point F s o 0 w).trans (hst.trans (onePoint_point F t 0 o w))
  rw [e, sub_self, norm_zero, mul_zero, zero_add] at h
  exact h

/-- **Dimension four, packaged.** For OpenAI's construction there exist a dimension-four field `w`
and a viewer-independent `κ` such that (1) all dimension-four condensate differences between two
viewers are `κ` times the difference of the single number `⟨w⟩`, and (2) two viewers with the same
`⟨w⟩` agree at short distance to order `r ^ (5 − weight − ε)`. -/
theorem dimension_four {hG : G.Simple} {F : Spec.Final C f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q) :
    ∃ (w : S.Field 4) (κ : S.Field 4 → ℂ),
      (∀ (s t : Viewers F) (o : E4) (i : Q.channels 4),
        condensate Q s 4 i o - condensate Q t 4 i o =
          κ (Q.actor 4 i) * (onePoint F s 0 w - onePoint F t 0 w)) ∧
      (∀ (I : Type) [Fintype I] (d : I → ℕ) (a : Labels S d) (M η ε : ℝ),
        0 ≤ M → 0 < η → 0 < ε →
        ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o → ∀ s t : Viewers F,
          onePoint F s 0 w = onePoint F t 0 w →
          ‖whole (spectator F s) x a noPts (noLab (S := S)) -
            whole (spectator F t) x a noPts (noLab (S := S))‖ ≤
              2 * r ^ (((4 : ℕ) : ℝ) + 1 - weight d - ε)) := by
  obtain ⟨w, c, κ, hw⟩ := one_number F hG
  refine ⟨w, κ, ?_, ?_⟩
  · intro s t o i
    have h := condensate_difference Q hw s t o i
    rw [onePoint_point F s o 0 w, onePoint_point F t o 0 w] at h
    exact h
  · intro I _ d a M η ε hM hη hε
    exact viewers_agree_of_one_number H hw a hM hη hε

end Viewers
end YM.Independent.DimFour

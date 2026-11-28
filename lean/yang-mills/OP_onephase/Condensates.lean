import YM.Independent.Core

/-! Council, 25 November 2026 (revision 2, after the first local build: empty spectator labels given explicitly). Phases of OpenAI's construction differ at short
distance only through their condensates.

`Core.point` gives one finite expansion of the point correlation, with coefficients
`Q.coef` common to every viewer (lattice limit or phase) and a remainder bound uniform in the
viewer. Taking no spectators (`J = Empty`), the expansion's terms are the phase's one-point
values (condensates) of the channel actors at the centre `o`. So, for two phases ξ, η, a group
of insertions within radius `M r` of `o` differs between them by at most the condensate
differences, weighted by the common coefficients, plus twice the remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Independent
open Filter MeasureTheory OPE OPE.Orbits
open scoped Topology BigOperators

universe u v
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- No spectators: the empty label family (fixing `e := fun _ => 0` so nothing is left implicit). -/
def noLab : Labels S (fun _ : Empty => (0 : ℕ)) := fun x => x.elim

/-- No spectator positions. -/
def noPts : Empty → E4 := fun x => x.elim

/-- The condensate of channel actor `(j, i)` at `o` in viewer `s`: its one-point value. -/
def condensate {F : Spec.Final C f S}
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s : Viewers F) (j : ℕ) (i : Q.channels j) (o : E4) : ℂ :=
  whole (spectator F s) (sole o) (sole (Q.actor j i) : Labels S (fun _ : Unit => j))
    noPts (noLab (S := S))

/-- Two viewers differ, on a group of insertions at scale `r`, by at most their condensate
differences weighted by the common coefficients, plus twice the remainder. -/
theorem viewer_difference {hG : G.Simple} {F : Spec.Final C f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q) {I : Type} [Fintype I] {d : I → ℕ} (a : Labels S d)
    {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o → ∀ s t : Viewers F,
      ‖whole (spectator F s) x a noPts (noLab (S := S)) -
        whole (spectator F t) x a noPts (noLab (S := S))‖ ≤
        ∑ j : Fin (D + 1), ∑ i : Q.channels j.val,
          ‖Q.coef j.val i x a o‖ * ‖condensate Q s j.val i o - condensate Q t j.val i o‖ +
        2 * r ^ ((D : ℝ) + 1 - weight d - ε) := by
  have hp := H.point a (noLab (S := S)) hM hη one_pos hε D
  filter_upwards [hp] with r hr
  intro x o hx s t
  have hc : ClearOf o noPts 1 := ⟨fun v => v.elim, fun i => i.elim⟩
  have h1 : ‖whole (spectator F s) x a noPts (noLab (S := S)) -
      ∑ j : Fin (D + 1), ∑ i : Q.channels j.val, Q.coef j.val i x a o * condensate Q s j.val i o‖
      ≤ r ^ ((D : ℝ) + 1 - weight d - ε) := hr x o noPts hx hc s
  have h2 : ‖whole (spectator F t) x a noPts (noLab (S := S)) -
      ∑ j : Fin (D + 1), ∑ i : Q.channels j.val, Q.coef j.val i x a o * condensate Q t j.val i o‖
      ≤ r ^ ((D : ℝ) + 1 - weight d - ε) := hr x o noPts hx hc t
  have hE : ‖(∑ j : Fin (D + 1), ∑ i : Q.channels j.val, Q.coef j.val i x a o * condensate Q s j.val i o) -
      ∑ j : Fin (D + 1), ∑ i : Q.channels j.val, Q.coef j.val i x a o * condensate Q t j.val i o‖ ≤
      ∑ j : Fin (D + 1), ∑ i : Q.channels j.val,
        ‖Q.coef j.val i x a o‖ * ‖condensate Q s j.val i o - condensate Q t j.val i o‖ := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact le_of_eq (by rw [← mul_sub, norm_mul])
  generalize whole (spectator F s) x a noPts (noLab (S := S)) = Ws at h1 ⊢
  generalize whole (spectator F t) x a noPts (noLab (S := S)) = Wt at h2 ⊢
  generalize (∑ j : Fin (D + 1), ∑ i : Q.channels j.val,
    Q.coef j.val i x a o * condensate Q s j.val i o) = Es at h1 hE
  generalize (∑ j : Fin (D + 1), ∑ i : Q.channels j.val,
    Q.coef j.val i x a o * condensate Q t j.val i o) = Et at h2 hE
  have k1 : Ws - Wt = (Ws - Es) - (Wt - Et) + (Es - Et) := by ring
  have k2 := norm_add_le ((Ws - Es) - (Wt - Et)) (Es - Et)
  have k3 := norm_sub_le (Ws - Es) (Wt - Et)
  rw [k1]
  linarith

/-- Corollary: two phases with equal condensates in every channel up to order `D` agree, on a
group of insertions at scale `r`, up to twice the remainder `r ^ (D + 1 − weight − ε)`. -/
theorem phases_agree_of_condensates {hG : G.Simple} {F : Spec.Final C f S}
    {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    (H : Core.{u,v} hG F L Q) {I : Type} [Fintype I] {d : I → ℕ} (a : Labels S d)
    {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) (D : ℕ) (ξ ζ : F.α.space.X)
    (hcond : ∀ (j : ℕ) (i : Q.channels j) (o : E4), j ≤ D →
      condensate Q (some ξ) j i o = condensate Q (some ζ) j i o) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o →
      ‖whole (spectator F (some ξ)) x a noPts (noLab (S := S)) -
        whole (spectator F (some ζ)) x a noPts (noLab (S := S))‖ ≤
        2 * r ^ ((D : ℝ) + 1 - weight d - ε) := by
  filter_upwards [viewer_difference H a hM hη hε D] with r hr
  intro x o hx
  have h := hr x o hx (some ξ) (some ζ)
  have hz : (∑ j : Fin (D + 1), ∑ i : Q.channels j.val,
      ‖Q.coef j.val i x a o‖ * ‖condensate Q (some ξ) j.val i o - condensate Q (some ζ) j.val i o‖)
      = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by
      rw [hcond j.val i o (Nat.lt_succ_iff.mp j.is_lt), sub_self, norm_zero, mul_zero]
  linarith
end YM.Independent

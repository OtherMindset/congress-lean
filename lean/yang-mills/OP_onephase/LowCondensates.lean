import Check.Condensates

/-! Council, 25 November 2026 (session 4). Below dimension four every viewer (phase) sees the same
one-point values: in each channel of degree `j < 4` the field space is one-dimensional, spanned by the unit,
so the condensate is the scalar of the quotient class and is the same in every viewer.
Hence viewers differ at short distance only through channels of degree `≥ 4`.

Local copies (Apache-2.0) of lemmas from OpenAI's Yang–Mills submission (OpenAI-YM-20261028 @3456e5e7),
whose home modules (`YM.Trace2.Transfer`, `YM.Trace.Center`) are outside the built import closure of
`HierarchyBridge`; the proofs are verbatim up to namespaces and the signature of `first_grade`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Independent.Low
open Filter MeasureTheory OPE OPE.Orbits
open scoped Topology BigOperators

universe u v

section Copies
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- Copied from OpenAI-YM-20261028 @3456e5e7, YM/Trace/Center.lean line 22 (`omit Y in` at line 21), Apache-2.0. -/
lemma valid_one (x : Points 1) : x ∈ conf _ := by intro i j hij; exact Subsingleton.elim i j

/-- Copied from OpenAI-YM-20261028 @3456e5e7, YM/Trace2/Transfer.lean lines 31-37, Apache-2.0.
Only change: the final `Y : Final C f S` of the source is the explicit argument `F`. -/
lemma first_grade (F : Spec.Final C f S) (hG : G.Simple) {d : ℕ} (hd : d < 4) (z : S.Field d) :
    ∃ t : ℂ, z = t • S.unit d := by
  obtain ⟨H,hH⟩ := F.phase.transport.comparator
  obtain ⟨e, -, -⟩:=hH d
  have hr : Module.finrank ℂ (S.Field d)=1:= e.finrank_eq.trans (UVNext.FreeStress.dim_before _ hG hd)
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (S.unit d) (S.alive d F.room.kernel.laws)).1 hr z
  exact ⟨t, ht.symm⟩

section Empty
variable {I : Type} [Fintype I] {J : Type} [Fintype J] [IsEmpty J]
/-- Copied from OpenAI-YM-20261028 @3456e5e7, YM/Trace2/Transfer.lean lines 39-58, Apache-2.0
(`open Function` replaced by qualified `Function.Injective`). -/
lemma observe_beside_empty {B:Register G} {T:Table B} (h:T.Symmetric)
    (x:I→E4) (hx : Function.Injective x) (p:I→B.Token) (y : J→E4)(q : J→B.Token) :
    observe T (beside x y) (beside p q) = observe T x p := by
  let e : I⊕J ≃ I :=
    { toFun:=fun s=>s.elim id isEmptyElim
      invFun:=Sum.inl
      left_inv:=by rintro (i|j); rfl; exact isEmptyElim j
      right_inv:=fun _=>rfl }
  have hx' : x ∘ e=beside x y:=by
    funext i; rcases i with i|j
    · rfl
    · exact isEmptyElim j
  have hp' : p ∘ e=beside p q:=by
    funext i; rcases i with i|j
    · rfl
    · exact isEmptyElim j
  rw [← hx',← hp',perm_observe T h e p hx]
end Empty

/-- Copied from OpenAI-YM-20261028 @3456e5e7, YM/Trace2/Transfer.lean lines 60-61, Apache-2.0. -/
def oneToken {L : Register G} (T : Table L) (z : E4) (d : ℕ) (p : L.Ref d) : ℂ :=
    observe T (sole z) (fun _ : Unit => ⟨d,p⟩)

/-- Copied from OpenAI-YM-20261028 @3456e5e7, YM/Trace2/Transfer.lean lines 62-68, Apache-2.0. -/
lemma singleton_read {L : Register G}(T : Table L)(h : T.Symmetric) (z : E4)(d : ℕ)(p : L.Ref d) :
    oneToken T z d p=T.read (points (fun _:Fin 1=>z)) (fun _=>⟨d,p⟩) := by
  let x:=points (fun _:Fin 1=>z)
  have hx : x∈ conf 1:=valid_one x
  let v:=fun (_:Fin 1) =>(⟨d,p⟩ : L.Token)
  rw [← named_fin T h v hx]; exact perm_observe T h (Equiv.ofUnique Unit (Fin 1)) v hx

/-- Copied from OpenAI-YM-20261028 @3456e5e7, YM/Trace2/Transfer.lean lines 69-71, Apache-2.0. -/
lemma oneToken_class {L : Register G} {S T : Table L}(h : T.Symmetric) (hr : T.respects S) (z : E4)(d : ℕ)(p : L.Ref d) :
    oneToken T z d p = S.classMoment T (n:=1) (fun _=> d) (points (fun _=>z)) (fun _=>S.project d p) :=
  (singleton_read T h z d p).trans (S.class_agrees T h hr (fun _:Fin 1=>d) (valid_one _) (fun _=>p)).symm

/-- Copied from OpenAI-YM-20261028 @3456e5e7, YM/Trace2/Transfer.lean lines 76-89, Apache-2.0. -/
lemma oneToken_scalar {L : Register G} (S T : Table L)(h : T.Basic)(hr : T.respects S)(z : E4) (d : ℕ)
   (b : L.Ref d) (t : ℂ)(ht : S.project d b=t • S.unit d) : oneToken T z d b=t := by
   let x:=points (fun _:Fin 1=>z)
   let M : S.Field d →ₗ[ℂ] ℂ := (S.classMoment T (n:=1) (fun _=>d) x).toLinearMap (fun _=>0) 0
   have hM v : S.classMoment T (fun _:Fin 1=>d) x (fun _=>v)=M v:=by
     dsimp only [M];rw [MultilinearMap.toLinearMap_apply]; congr 1; funext i; fin_cases i; simp
   have he : M (S.unit d) = 1:=by
     rw [← hM]; change S.classMoment T (fun _=>d) x (fun _=> S.project d (L.scalar d))=1
     rw [S.class_agrees T h.toSymmetric hr _ (valid_one x) (fun _=>_)]
     change T.read x (fun _:Fin 1=>⟨d,L.scalar d⟩)=1
     rw [show (fun _:Fin 1=>⟨d,L.scalar d⟩:Fin (0+1)→L.Token)=Fin.cons (L.one d) (fun i : Fin 0=>L.one d) from funext (Fin.cases rfl (fun i=>Fin.elim0 i)),h.unital (valid_one ..)]
     exact h.trivial ..
   rw [oneToken_class h.toSymmetric hr,ht]
   rw [hM, map_smul,he,smul_eq_mul,mul_one]
end Copies

section Council
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S}
variable {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}

/-- The condensate of a channel actor is the one-token read of its quotient representative at `o`
in the viewer's table. (`whole_observed` and `observe_beside_empty`; `names (sole c)` unfolds to
the token `⟨j, S.representative j c⟩`.) -/
theorem condensate_eq_oneToken (s : Viewers F) (j : ℕ) (i : Q.channels j) (o : E4) :
    condensate Q s j i o = oneToken (spectator F s) o j (S.representative j (Q.actor j i)) := by
  have hs : (spectator F s).Symmetric := (spectate F s).laws.toSymmetric
  have h1 : condensate Q s j i o =
      observe (spectator F s) (beside (sole o) noPts)
        (beside (names (sole (Q.actor j i) : Labels S (fun _ : Unit => j))) (names (noLab (S := S)))) :=
    whole_observed (T := spectator F s) (sole o) (sole (Q.actor j i) : Labels S (fun _ : Unit => j))
      noPts (noLab (S := S))
  have h2 : observe (spectator F s) (beside (sole o) noPts)
        (beside (names (sole (Q.actor j i) : Labels S (fun _ : Unit => j))) (names (noLab (S := S)))) =
      observe (spectator F s) (sole o)
        (names (sole (Q.actor j i) : Labels S (fun _ : Unit => j))) :=
    observe_beside_empty (I := Unit) (J := Empty) hs (sole o)
      (Function.injective_of_subsingleton (sole o))
      (names (sole (Q.actor j i) : Labels S (fun _ : Unit => j))) noPts (names (noLab (S := S)))
  exact h1.trans h2

/-- Below dimension four, condensates do not depend on the viewer. -/
theorem condensate_low (hG : G.Simple) {j : ℕ} (hj : j < 4) (i : Q.channels j) (o : E4)
    (s t : Viewers F) : condensate Q s j i o = condensate Q t j i o := by
  obtain ⟨b, hb⟩ := first_grade F hG hj (S.project j (S.representative j (Q.actor j i)))
  have hs := (spectate F s).laws
  have ht := (spectate F t).laws
  have e1 : oneToken (spectator F s) o j (S.representative j (Q.actor j i)) = b :=
    oneToken_scalar S (spectator F s) hs (spectate_respects F s) o j
      (S.representative j (Q.actor j i)) b hb
  have e2 : oneToken (spectator F t) o j (S.representative j (Q.actor j i)) = b :=
    oneToken_scalar S (spectator F t) ht (spectate_respects F t) o j
      (S.representative j (Q.actor j i)) b hb
  have c1 := condensate_eq_oneToken (Q := Q) s j i o
  have c2 := condensate_eq_oneToken (Q := Q) t j i o
  exact c1.trans (e1.trans (e2.symm.trans c2.symm))

/-- Viewers agree on a group of insertions at scale `r`, up to twice the remainder of order
`r ^ (3 + 1 − weight − ε)`: all channels of degree `< 4` have equal condensates. -/
theorem viewers_agree_below_four {hG : G.Simple} {L : EveryPhase.Almanac F}
    (H : Core.{u,v} hG F L Q) {I : Type} [Fintype I] {d : I → ℕ} (a : Labels S d)
    {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o → ∀ s t : Viewers F,
      ‖whole (spectator F s) x a noPts (noLab (S := S)) -
        whole (spectator F t) x a noPts (noLab (S := S))‖ ≤
        2 * r ^ (((3 : ℕ) : ℝ) + 1 - weight d - ε) := by
  filter_upwards [viewer_difference H a hM hη hε 3] with r hr
  intro x o hx s t
  have h := hr x o hx s t
  have hz : (∑ j : Fin (3 + 1), ∑ i : Q.channels j.val,
      ‖Q.coef j.val i x a o‖ * ‖condensate Q s j.val i o - condensate Q t j.val i o‖) = 0 :=
    Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by
      have hj : j.val < 4 := by
        have hl := j.is_lt
        omega
      have e : condensate Q s j.val i o = condensate Q t j.val i o := condensate_low hG hj i o s t
      rw [e, sub_self, norm_zero, mul_zero]
  linarith

/-- The first possible viewer dependence is in the degree-four channels. -/
theorem viewers_differ_by_dim4 {hG : G.Simple} {L : EveryPhase.Almanac F}
    (H : Core.{u,v} hG F L Q) {I : Type} [Fintype I] {d : I → ℕ} (a : Labels S d)
    {M η ε : ℝ} (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o → ∀ s t : Viewers F,
      ‖whole (spectator F s) x a noPts (noLab (S := S)) -
        whole (spectator F t) x a noPts (noLab (S := S))‖ ≤
        ∑ i : Q.channels 4, ‖Q.coef 4 i x a o‖ * ‖condensate Q s 4 i o - condensate Q t 4 i o‖ +
        2 * r ^ (((4 : ℕ) : ℝ) + 1 - weight d - ε) := by
  filter_upwards [viewer_difference H a hM hη hε 4] with r hr
  intro x o hx s t
  have h := hr x o hx s t
  have hsum : (∑ j : Fin (4 + 1), ∑ i : Q.channels j.val,
      ‖Q.coef j.val i x a o‖ * ‖condensate Q s j.val i o - condensate Q t j.val i o‖) =
      ∑ i : Q.channels 4, ‖Q.coef 4 i x a o‖ * ‖condensate Q s 4 i o - condensate Q t 4 i o‖ := by
    refine Finset.sum_eq_single (Fin.last 4) ?_ ?_
    · intro b _ hb
      have hb4 : b.val ≠ 4 := fun hh => hb (Fin.ext hh)
      have hj : b.val < 4 := by
        have hl := b.is_lt
        omega
      refine Finset.sum_eq_zero fun i _ => ?_
      have e : condensate Q s b.val i o = condensate Q t b.val i o := condensate_low hG hj i o s t
      rw [e, sub_self, norm_zero, mul_zero]
    · intro hn
      exact absurd (Finset.mem_univ (Fin.last 4)) hn
  linarith

end Council
end YM.Independent.Low

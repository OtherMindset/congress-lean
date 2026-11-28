import HierarchyBridge
import Check.S2Bridge

/-! Session 2, last step (written, to be built once `HierarchyBridge` is built locally):
OpenAI's own public hierarchy reads its construction, so every theorem of `Reads` holds
for it with no hypotheses. Each field repeats a step of `publicReconstruction`
(HierarchyBridge.lean:79-110): the `rfl` after `Table.readAt`, and `Table.at_project`. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE YM.OPE.Orbits
open scoped Classical
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def openaiReads : Reads (hierarchy F Q) F where
  ι := Equiv.refl _
  q := quoteTag (S := S)
  cl := S.classTokens
  some_read _ _ _ _ := rfl
  none_read _ _ := rfl
  some_class i _ u _ hx := S.at_project (F.α.ensemble i) (F.phase.phase.states i).laws.toSymmetric
    (fun d => (F.phase.phase.retains i d).symm.le) hx u
  none_class u _ hx := S.at_project S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) hx u

theorem openai_singlePhase_iff_clusters :
    (hierarchy F Q).SinglePhase ↔ (hierarchy F Q).Clusters none :=
  (openaiReads F Q).singlePhase_iff_clusters

theorem openai_singlePhase_iff_uniqueHeat :
    (hierarchy F Q).SinglePhase ↔ F.α.room.UniqueHeat :=
  (openaiReads F Q).singlePhase_iff_uniqueHeat

theorem openai_separates : (hierarchy F Q).Separates := (openaiReads F Q).separates
end YangMills

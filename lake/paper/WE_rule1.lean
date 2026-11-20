import LT2D.VN.K5
import LT2D.VN.K7

namespace VN.VB269907

def tab : Tab := ⟨[
  [1,1,1,2,3,4,4,4],
  [1,2,2,2,5,6,6,6],
  [2,2,2,2,6,6,6,6],
  [3,4,4,4,3,4,4,4],
  [4,4,4,4,4,4,4,4],
  [5,6,6,6,5,6,6,6],
  [6,6,6,6,6,6,6,6]
], [0,0,0,1,0,0,1], by decide +kernel⟩

theorem ok2 : checkF2 tab = true := by decide +kernel
theorem ok1 : checkF1 tab 1 743 = true := by decide +kernel
theorem okr : checkRec tab 1 4 (-4) (-4) 1 1 = true := by decide +kernel

end VN.VB269907

import LT2D.VN.K5
import LT2D.VN.K7

namespace VN.NEG

def tab : Tab := ⟨[
  [1,1,1,2,3,4,4,4],
  [1,2,2,2,5,6,6,6],
  [2,2,2,2,6,6,6,6],
  [3,4,4,4,3,4,4,4],
  [4,4,4,4,4,4,4,4],
  [5,6,6,6,5,6,6,6],
  [6,6,6,6,6,6,6,6]
], [0,0,0,1,0,0,1], by decide +kernel⟩

-- the same table with one transition changed: row 1, letter 4 (5 -> 6)
def tabX : Tab := ⟨[
  [1,1,1,2,3,4,4,4],
  [1,2,2,2,6,6,6,6],
  [2,2,2,2,6,6,6,6],
  [3,4,4,4,3,4,4,4],
  [4,4,4,4,4,4,4,4],
  [5,6,6,6,5,6,6,6],
  [6,6,6,6,6,6,6,6]
], [0,0,0,1,0,0,1], by decide +kernel⟩
theorem n1 : checkF1 tab 3 743 = false := by decide +kernel     -- wrong rule (3 differs from 1 at index 1, which occurs)
theorem n2 : checkF1 tab 1 739 = false := by decide +kernel     -- mask without index 2, which occurs
theorem n3 : checkRec tab 1 4 (-4) (-3) 1 1 = false := by decide +kernel  -- constant term changed by one
theorem n4 : checkRec tab 1 4 (-4) (-4) 0 1 = false := by decide +kernel  -- formula claimed from n = 0
theorem n5 : checkF1 tabX 1 743 = false := by decide +kernel    -- one transition changed
theorem n6 : checkF2 tabX = true := by decide +kernel           -- (the seed check does not see that change)
end VN.NEG

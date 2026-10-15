import DetBaseV
import PTF_0110010
import PTT_0110010
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen
theorem pT_0110010 : (allLists 12).all (fun l => G [false, true, true, false, false, true, false] 2 (true :: l)) = true := by
  show (allLists (11 + 1)).all (fun l => G [false, true, true, false, false, true, false] 2 (true :: l)) = true
  rw [all_allLists_succ, pTF_0110010, pTT_0110010]
  rfl
end AbsorbRightV

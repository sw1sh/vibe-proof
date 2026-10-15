import DetBaseV
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen
theorem pTT_0110010 : (allLists 11).all (fun l => G [false, true, true, false, false, true, false] 2 (true :: true :: l)) = true := by decide +kernel
end AbsorbRightV

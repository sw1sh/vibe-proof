import DetBaseV
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen
theorem pT_0000100 : (allLists 12).all (fun l => G [false, false, false, false, true, false, false] 2 (true :: l)) = true := by decide +kernel
end AbsorbRightV

import DetBaseV
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen
theorem pT_0110110 : (allLists 12).all (fun l => G [false, true, true, false, true, true, false] 2 (true :: l)) = true := by decide +kernel
end AbsorbRightV

import DetBaseV
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen
theorem pF_0101000 : (allLists 12).all (fun l => G [false, true, false, true, false, false, false] 2 (false :: l)) = true := by decide +kernel
end AbsorbRightV

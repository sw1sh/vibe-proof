import DetBaseV
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen
theorem pF_0010010 : (allLists 12).all (fun l => G [false, false, true, false, false, true, false] 2 (false :: l)) = true := by decide +kernel
end AbsorbRightV

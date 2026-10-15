import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Prize
#check @Ruliology.CellularAutomata.Rule30Jen.cell.eq_1
#check @Ruliology.CellularAutomata.Rule30Jen.cell.eq_2
example : (List.range 9).map center = [true,true,false,true,true,true,false,false,true] := by
  decide +kernel

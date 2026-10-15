import Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Jen
#print Ruliology.CellularAutomata.Rule30Jen.rule
#print Ruliology.CellularAutomata.Rule30Jen.cell
#check @Ruliology.CellularAutomata.Rule30Jen.not_adjacent
#check @Ruliology.CellularAutomata.Rule30Jen.cell_left
#print Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic
#print axioms Ruliology.CellularAutomata.Rule30Jen.not_adjacent
-- sanity: first center values 1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1
example : (List.range 20).map (fun t => cell t 0) =
  [true,true,false,true,true,true,false,false,true,true,false,false,false,true,false,true,true,false,false,true] := by decide
